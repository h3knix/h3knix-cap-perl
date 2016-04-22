#!/usr/bin/env perl
# cap
# Michael Vandenberghe ( h3k ) 2005
# Licensed under gpl

use strict;
use warnings;
use File::Basename;
use LWP::Simple;
use Sort::Versions;
use File::Glob;
use File::Copy;
use Getopt::Long;
Getopt::Long::Configure("no_ignore_case");

my $globalVersion="2005.11.12";
my $logDir = "var/log/captracks";
my $capdir = "/usr/src/capsules";
my $pacodir="/var/log/paco";

#makecap variables
my $postInstall = "postInstall.sh";
my $preRemove = "preRemove.sh";
my $postRemove = "postRemove.sh";

# repository variables
my $server = "http://caps.h3knix.org/";
my $backend = "capbackend.php?type=";
my $repo = "get&data=";
my $searchstr = "search&data=";
my $aliasPrefix = "&alias=";
my $alias="new";
my $depAlias;


my @errors;
my $tarextract = "tar xvjf"; # used to extract a capsule's files

# used to count specific actions, to display a summary at the end
my $depcaps = 0;
my $updates = 0;
my $installs = 0;
my $removes = 0;
my $lists = 0;

my $inpath = "";

my $confFile = "/etc/cap.conf";
my %config;

###################################
# makes sure the prerequisite tools/files are found
if ( ! -d $capdir ) {
	if ( system("mkdir -p \"$capdir\"") != 0 ) {
		print "\n\nError:\n could not create $capdir";
		exit 1;
	}
}
###################################
# initialize conf file

if ( -e $confFile ) {
	open(my $conf, $confFile);
	while(<$conf>) {
		my $line = $_ ; chomp($line);
		if ( $line =~ m/(^[^\#]+)=(.+)$/ ) {
			$config{$1}=$2;
		}
	}
	close($conf);
}

###################################
# misc functions

# creates a temporary file, based off a seed and a randomized number
# returns the filename that it created
sub createTemp {
	my $seed = $_[0];
	my $f = `mktemp -q /tmp/$seed.XXXXXX`;
	chomp($f);
	if ( $f ) {
		#print "made ".$f."\n";
	} else {
		print "failed to create temporary file '".$f."'\n";
		exit 1;
	}
	return $f;
}

sub trim {
	my $string = shift;
	$string =~ s/\s//g;
	return $string;
}

# prints the current time, in format YYYY-MM-DD H-M-S
# note: does not print line break
sub printTime {
	my ($sec,$min,$hour,$mday,$mon,$year)=localtime(time);
	printf "%4d-%02d-%02d %02d:%02d:%02d", $year+1900,$mon+1,$mday,$hour,$min,$sec;
}

# sorts a list of directories, by how many sub directories the dir has
# sorts so that the deepest dirs come up first
# used with removal scripts, to remove emtpy directories in the appropriate order
sub mysort {
	my $aa=$a; my $bb=$b;
	(($bb=~ tr/\//\//) || lc($a) cmp lc($b)) <=> ($aa =~ tr/\//\//);
}

# uses the filename of a capsule, to parse out keyword and version works on properly named capsules only
sub sepCap {
	my $capFileName = basename($_[0]);
	$capFileName =~ s{\.cap$}{};
	if ( $capFileName =~ m/^(.*)-(.+)$/ ) {
		return ($1,$2, $capFileName);
	} else {
		print "\nFatal Error:\n\tMalformed capname: \"$capFileName\"\n\n";
		exit 1;
	}
}

# query the user for a simple answer
# returns the user's answer
sub askUser {
	my $question = $_[0];
	print "$question";
	my $answer = <STDIN>;
	chomp($answer);
	return $answer;
}

# takes an input capname, and checks if a track file exists for it
# when the capname and track file do not match, it asks the user for the path to the track file
sub findCapTrack {
	my $capName = $_[0];
	my $lookAgain = $_[1];
	if ( -f "$inpath/$logDir/$capName/filelist" ) {
		return "$inpath/$logDir/$capName/filelist";
	} else {
		if ( $lookAgain != 0 ) {
			print "\n\nCould not find $inpath/$logDir/$capName/filelist\n";
			print " Specify the correct pathname for $capName: ";
			my $pathName = <STDIN>; chomp($pathName);
			if ( ! -e $pathName ) {
				print "\n Error:\n   Could not find \"$pathName\"\n\n";
				exit 1;
			} else {
				return $pathName;
			}
		} else {
			print "\n Error:\n   Could not find \"$inpath/$logDir/$capName/filelist\"\n\n";
			exit 1;
		}
	}
}

# check that a file exists
# exists with an error when it does not exist
sub checkFile {
	my $fileName = $_[0];
	if ( -d $fileName ) {
		print "\n Error:\n '$fileName' is a directory, not a file!\n\n";
		exit 1;
	}
	if ( ! -f $fileName ) {
		print "\n Error:\n Regular file '$fileName' doesnt exist!\n\n";
		exit 1;
	}
}

# check if a directory exists ( preparing for installation of a capsule )
# if it does, ask the user if he would like to delete it, so captool can use it
sub checkdir {
	my $dirname = $_[0];
	if ( -d $dirname ) {
		my $danswer = askUser("  $dirname already exists\n  Delete $dirname?> ");
		if ($danswer =~ /y/i) {
			if ( system("rm -rf $dirname") == 0 ) {
				print "  $dirname deleted!\n";
				return 0;
			} else {
				push(@errors,"# Could not delete $dirname!");
				return 1;
			}
		} else {
			push(@errors,"# $dirname exists, cannot continue");
			return 1;
		}
	}
	return 0;
}



###################################
# depcap functions

sub separateDep {
	my $input = trim($_[0]);
	if ( $input =~ m/(.*)\((..)(.*)\)/ ) {
			return ($1,$2,$3);
	} else {
		return ($input, "none", "none");
	}
}

sub getVersion {
	my $pkg = $_[0];
	foreach my $file (glob("$inpath/$logDir/$pkg-*")) {
		my $pkg2 = basename($file);
		if ( $pkg2 =~ m/^.*-(.*)$/ ) {
			return $1;
		}
	}
	return 'none';
}

sub getVersions {
	my $pkg = $_[0];
	my @arr;
	foreach my $file (glob("$inpath/$logDir/$pkg-*")) {
		my $pkg2 = basename($file);
		if ( $pkg2 =~ m/^.*-(.*)$/ ) {
			push(@arr,$1);
		}
	}
	return @arr;
}

# pass in (<version>, <version>, <operator>) , it will return how the operator evaluates on the two versions
sub compareVersions {
	my $ver1 = $_[0];
	my $ver2 = $_[1];
	my $op = $_[2];
	my $eval = versioncmp($ver1,$ver2);
	
	if ( $op eq "=="  ) {
		if ( $eval == 0 ) { return 1; } else { return 0; }
	} elsif ( $op eq ">=" ) {
		if ( $eval >= 0 ) { return 1; } else { return 0; }
	} elsif ( $op eq "<=" ) {
		if ( $eval <= 0 ) { return 1; } else { return 0; }
	} elsif ( $op eq "<<" ) {
		if ( $eval < 0 ) { return 1; } else { return 0; }
	} elsif ( $op eq ">>" ) {
		if ( $eval > 0 ) { return 1; } else { return 0; }
	}
}

sub evaluateDepCheck {
	my $input = $_[0];
	my ($pkg,$operator,$version) = separateDep($input);
	if ( $operator eq "none" ) {
		foreach my $file (glob("$inpath/$logDir/$pkg-*")) {
			return 1;
		}
		return "none";
	} else {
		my $count = 0;
		foreach my $file (glob("$inpath/$logDir/$pkg-*")) {
			my $pkg2 = basename($file);
			if ( $pkg2 =~ m/^.*-(.*)$/ ) {
				if ( compareVersions($1,$version,$operator) ) {
					return 1;
				}
				$count++;
			}
		}
		if ( $count > 0 ) { return 0; } 
		else { return 'none'; }
	}
}

###################################
# Capsule database access methods and capsule repository access methods

# optional second argument for database alias
sub getinfo {
	my $skey = $_[0];
	my $entry = 'none';
	if ( defined($_[1]) ) {
		print "  Retrieving entry for $skey from database: ".$_[1];
		$entry = get($server.$backend.$repo.$skey.$aliasPrefix.$_[1]);
	} elsif ( defined($alias) ) {
		print "  Retrieving entry for $skey from database: ".$alias;
		$entry = get($server.$backend.$repo.$skey.$aliasPrefix.$alias);
	} else {
		print "  Retrieving entry for $skey";
		$entry = get($server.$backend.$repo.$skey);
	}
	if ($entry) {
		my ($key,$capname,$deps,$md5,$url,$desc,$arch,$version) = split("%", $entry);
		if ($key eq "none") {
			print "\n -". $skey ." was not found in database\n";
			push(@errors,"# \"$skey\" was not found in database, DB");
			return ("none");
		} else {
			print " +++ \n";
			return ($key,$capname,$deps,$md5,$url,$desc,$arch,$version);
		}
	}
	print "\n - Could not retreive entry!\n";
	push(@errors,"# could not get an entry for \"$skey\", DB");
	return ("none");
}

# retrieve an entry and print it to stdout in a nice way...
sub outEntry {
	my $key = $_[0];
	my $capname = $_[1];
	my $deps = $_[2];
	my $md5 = $_[3];
	my $url = $_[4];
	my $desc = $_[5];
	my $arch = $_[6];
	my $version = $_[7];
	
	print "  Keyword: $key\n";
	print "  Capname: $capname\n";
	if ( length($deps) >= 75 ) {
		print "  Deps:\n";
		my @depArr = split(/,/, $deps);
		foreach my $dep (@depArr) {
			print "\t$dep\n";
		}
	} else {
		print "  Deps: $deps\n";
	}
	print "  md5: $md5\n";
	print "  arch: $arch\n";
	print "  version: $version\n";
	print "  desc: $desc\n";
	print "  urls:\n";
	my @urls = split(/,/, $url);
	foreach my $surl (@urls) {
		print "\t$surl\n";
	}
	print "\n";
	$lists++;
}

# retreives the capsule info, and sends it to outEntry
sub printEntry { 
	my $key = $_[0];
	if ( defined($key) ) {
		my ($key,$capname,$deps,$md5,$url,$desc,$arch,$version) = getinfo($key);
		print "\n";
		if ($key ne "none") {
			outEntry($key,$capname,$deps,$md5,$url,$desc,$arch,$version);
		} else { push(@errors,"# keyword \"$key\" does not exist in database"); }
	}
}

sub capsearch {
	my $term = $_[0];
	if ( defined($term) ) {
		print "\n Searching for \"$term\" ...\n\n";
		my $entry='none';
		if ( defined($alias) ) {
			$entry = get($server.$backend.$searchstr.$term.$aliasPrefix.$alias);
		} else {
			$entry = get($server.$backend.$searchstr.$term);
		}
		my @entries = split("\n",$entry);
		foreach my $eEntry (@entries) {
			if ( $eEntry ) {
				my ($key,$capname,$deps,$md5,$url,$desc,$arch,$version) = split("%", $eEntry);
				$key = trim($key);
				if ( $key ne "none" ) {
					outEntry($key,$capname,$deps,$md5,$url,$desc,$arch,$version);
				} else {
					print "\n\tNo results!\n";
				}
			}
		}
		print "\n";
	} else {
		print "\n\n Error:\n Must specify term!\n\n";
	}
}

sub download {
	my $capname = $_[0];
	my $md5 = $_[1];
	my $url = $_[2];
	my @urls = split(",", $url);
	if ($urls[0] ne "none") {
		my $count = 0;
		my $max = scalar(@urls);
		my $ret = 0;
		foreach $url (@urls) {
			if ( $ret != 2 ) {
				## check if the capsule has already been downloaded before, and matches the md5sum
				if ( -e "$capname.cap" ) {
					print "$capname found...\n";
					if ( integrity($md5,"$capname.cap") == 0 ) {
						print "+ $capname usable\n";
						return 0;
					} else {
						print "- $capname not usable\n";
						if (system("rm $capname.cap") != 0) {
							push(@errors,"# Error # : could not download \"$capname\", PRMS");
							return 1;
						}
					}
				}
				
				print "   Downloading $capname ...\n";
				print "|--------------------------------------------------------------------------|\n";
				$ret = system("wget $url");
				if ( $ret == 0) {
					print "|--------------------------------------------------------------------------|\n";
					print ">>> Sucessful\n\n";
					last;
				} else {
					print "\n|--------------------------------------------------------------------------|\n";
					print "### Download failed\n\n";
				}
				$count +=1;
				if ($max == $count) {
					print "### Failed ###\n\n";
					push(@errors,"# All download attemps failed , DWNLD");
					return 1;
				} else {
					print "  Trying another mirror\n";
				}
			} else {
				push(@errors,"# User cancelled download");
				return 1;
			}
		}
		if ( integrity($md5,"$capname.cap") != 0 ) {
			push(@errors,"# getcap failed, file $capname integrity check failed!");
			return 1;
		} else {
			return 0;
		}
	}
	print "### Download failed\n\n";
	push(@errors,"# could not get a url for \"$capname\", WEB");
	return 1;
}

# optional 3rd argument for database alias
sub getcap {
	my $lkey = $_[0];
	my $ask = $_[1];
	chdir "$capdir";
	my ($key,$capname,$deps,$md5,$url,$desc,$arch,$version);
	if ( defined($_[2]) ) {
		($key,$capname,$deps,$md5,$url,$desc,$arch,$version) = getinfo($lkey,$_[2]);
	} else {
		($key,$capname,$deps,$md5,$url,$desc,$arch,$version) = getinfo($lkey);
	}
	if ($key ne "none") {
		if ( defined($depAlias) ) {
			deps($deps,$ask,$depAlias);
		} else {
			deps($deps,$ask);
		}
		print "\n";
		if ( download($capname,$md5,$url) == 1 ) { return 1; }
		if ( captool("$capname.cap",$ask) == 1 ) {
			print "# Installation aborted\n\n";
			exit 1;
		}
		return 0;
	}
	push(@errors,"# getcap failed keyword error");
	return 1;
}

# optional third argument for database aliasing
# --
# optional fourth argument is a capsule filename, 
# if capsule filename specified, it will be used instead of whatever is on the repository
sub upgradeClean {
	my $oldCapName = $_[0];chomp($oldCapName);
	my $ask = $_[1];chomp($ask);
	my $capname = '';
	my $oldFileName = '';
	my $isSync = 0;
	
	print "\n Updating $oldCapName...\n";
	print " Starting Update...   [ ";printTime();print " ]\n";
	
	print "##################################################################\n";
	
	if ( defined($_[3]) ) {
		chomp($_[3]);
		checkFile( $_[3]); # check that the new capsule exists
		
		# split the capname arguments, into useable data
		my $gotoDir = dirname($oldCapName);
		my ($capOldKeyword,$capOldVersion, $capOldFileName) = sepCap($oldCapName);
		my ($capNewKeyword,$capNewVersion, $capNewName) = sepCap($_[3]);
		$capname = $capNewName;
		
		# we need to see if the old package is installed, before trying to install the new one
		$oldFileName = findCapTrack($capOldFileName);
		if ( $capOldFileName eq  $capname ) {
			$isSync = 1;
			my $newPkgOldFile = createTemp($capOldFileName);
			if ( system("mv $oldFileName $newPkgOldFile") == 0 ) {
				$oldFileName=$newPkgOldFile;
			} else {
				print "\n\n Error:\n clean sync failed to relocate '$oldFileName' to '$newPkgOldFile'!\n\n";
				exit 1;
			}
		}
		
		if ( captool($gotoDir."/".$capname.".cap",$ask) != 0 ) {
			print "\n\n Error:\n captool failed!\n\n";
			exit 1;
		}
	} else {
		chdir "$capdir";
		
		# split the capname arguments, into useable data
		my ($capOldKeyword,$capOldVersion, $capOldFileName) = sepCap($oldCapName);	
		my ($key,$capNewName,$deps,$md5,$url,$desc,$arch,$version) = getinfo($capOldKeyword);
		$capname = $capNewName;
		if ($key eq "none") {
			push(@errors,"# keyword \"$key\" does not exist in database"); 
			return 1;
		}
		
		my $indep = evaluateDepCheck($key);
		if ( $indep eq "none" ) {
			push(@errors,"# \"$key\" is not installed, cannot upgrade!");
			return 1;
		}
		my $hasdep = evaluateDepCheck("$key(<<$version)");
		if ( $hasdep == 0 ) {
			print "\n\n Error:\n $key is already the latest version!\n\n";
			push(@errors,"# $key is already the latest version!");
			return 1;
		}
		
		# we need to see if the old package is installed, before trying to install the new one
		$oldFileName = findCapTrack($capOldFileName);
		if ( $capOldFileName eq  $capname ) {
			$isSync = 1;
			my $newPkgOldFile = createTemp($capOldFileName);
			if ( system("mv $oldFileName $newPkgOldFile") == 0 ) {
				$oldFileName=$newPkgOldFile;
			} else {
				print "\n\n Error:\n clean sync failed to relocate '$oldFileName' to '$newPkgOldFile'!\n\n";
				exit 1;
			}
		}
		
		if ( defined($_[2]) ) {
			if ( getcap($key,$ask, $_[2]) != 0 ) {
				push(@errors,"# Upgrade failed on getcap");
				return 1;
			}
		} else {
			if ( getcap($key,$ask) != 0 ) {
				push(@errors,"# Upgrade failed on getcap");
				return 1;
			}
		}
		checkFile($capname.".cap"); # check that the new capsule exists
	}
	
	print "##################################################################\n";
	
	print "\n Removing left over files...\n";
	
		my $newFileName = findCapTrack($capname);
		open(my $oldFile,  $oldFileName) or die ("Cannot open new!\n"); # old capsule file list
		
		my $upgradeVerbose = '';
		if ( defined $config{"upgradeVerbose"} and $config{"upgradeVerbose"} ) {
			$upgradeVerbose = ' -v';
		}
		my %dirs;
		while(<$oldFile>) {
			my $oldLine = $_; chomp($oldLine);
			if ( `grep -e "^$oldLine\$" $newFileName` eq "" ) {
				my $folder = dirname($oldLine);
				
				if ( ! exists($dirs{$folder}) ) {
					$dirs{$folder}='';
				}
				system("rm$upgradeVerbose \"$inpath$oldLine\"");
			}
		}
		close($oldFile);
	
	print "\t[ Done ]\n";
	
	print "\n Removing left over directories...";
	
		foreach my $dir ( keys(%dirs) ) {
			my $cur=$dir;
			while ( $cur ne "/" and $cur ne '.' ) {
				$dirs{dirname($cur)} = '';
				$cur=dirname($cur);
			}
		}
		foreach my $dir ( sort mysort keys(%dirs) ) {
			if ( $dir ne "/" ) {
				system("rmdir \"$inpath$dir\" 2> /dev/null");
			}
		}
	
	print " [ Done ]\n";
	
	if ( ! $isSync ) {
		if ( -d "$inpath/$logDir/$oldCapName" ) {
			print " Removing old track file $inpath/$logDir/$oldCapName...";
				system("rm -rf \"$inpath/$logDir/$oldCapName\"");
			print " [ Done ]\n\n";
		}
	} else {
		print "\n Clean sync detected, skipping removal of $inpath/$logDir/$oldCapName\n\n";
	}
	
	print " > Finished Update... [ ";printTime();print " ]\n\n";
	
	$updates++;
}

#%%%%%%%%%%%%%%%%%%%%#
# Capsule dependency functions

sub deps {
	my @deps = split(/,/,$_[0]);
	my $ask = $_[1];
	my @rdeps;
	my @udeps;
	if ( scalar(@deps) > 0 ) {
		print "\n|-- Resolving deps -----------------------|\n";
		foreach my $dep (@deps) {
			$dep=trim($dep);
			my $hasdep = evaluateDepCheck($dep);
			if ( $hasdep ne "none" ) {
				if ( $hasdep == 1 ) {
					print "\tFound $dep\n";
				} elsif ( $hasdep == 0 ) {
					print "\tUpgrading $dep\n";
					push(@udeps, $dep);
				}
			} else {
				print "\t$dep not found\n";
				push(@rdeps, $dep);
			}
		}
		print "|-----------------------------------------|\n";
		foreach my $ndep (@udeps) {
			my $cleandep = (split(/\(/,$ndep))[0];
			my $depver = getVersion($cleandep);
			if ( defined($depAlias) ) {
				if ( upgradeClean($cleandep."-".$depver,$ask,$depAlias) == 0 ) {
					$updates +=1;
				} else {
					print " Upgrade $ndep Failed\n";
					dumpErrors();
					exit 1;
				}
			} else {
				if ( upgradeClean($cleandep."-".$depver,$ask) == 0 ) {
					$updates +=1;
				} else {
					print " Upgrade $ndep Failed\n";
					dumpErrors();
					exit 1;
				}
			}
		}
		foreach my $ndep (@rdeps) {
			my $cleandep = (split(/\(/,$ndep))[0];
			if ( defined($depAlias) ) {
				if ( getcap($cleandep,$ask, $depAlias) == 0 ) {
					$depcaps +=1;
				} else {
					print " $cleandep Failed\n";
					dumpErrors();
					exit 1;
				}
			} else {
				if ( getcap($cleandep,$ask) == 0 ) {
					$depcaps +=1;
				} else {
					print " $cleandep Failed\n";
					dumpErrors();
					exit 1;
				}
			}
		}
		return 0;
	} else {
		print "\n<-- No deps to resolve ------------------->";
		return 0;
	}
}

#%%%%%%%%%%%%%%%%%%%%#
# Capsule handling functions

sub integrity {
	my $md5 = $_[0];
	my $cap = $_[1];
	print "  Checking integrity...";
	if ( system("echo \"". $md5 . "  ". $cap ."\" | md5sum -c &> /dev/null") != 0 ) {
		print " [ FAILED ]\n";
		return 1;
	}
	print " [ passed ]\n";
	return 0;
}

sub captool {
	my $capFileName = $_[0];
	my $ask = $_[1];
	checkFile($capFileName);
	chdir(dirname($capFileName)); # change directory right next to the capsule
	$capFileName= basename($capFileName);
	
	my ($capKeyword,$capVersion, $capName) = sepCap($capFileName);
	
	if ( $ask ) {
		my $answer = askUser("\n  Install $capName?  ");
		if ($answer =~ /y/i) { print "\n  -continuing\n"; } 
		else { print "\n  Installation cancelled\n"; return 1; }
	}
	print "\n  Installing $capName\n";
	print "|-----------------------------------------|\n";
	
	if ( defined $config{"extractVerbose"} and $config{"extractVerbose"} ) {
		print "|## Extracting files #####################|\n\n";
		if ( system("$tarextract $capName.cap -C $inpath/") != 0 ) {
			push(@errors,"# Error # : Captool failed to extract files.");
			return 1;
		}
		print "\n|#########################################|\n\n";
	} else {
		print "\n Extracting files... ";
		if ( system("$tarextract $capName.cap -C $inpath/ > /dev/null 2> /dev/null") != 0 ) {
			push(@errors,"# Error # : Captool failed to extract files.");
			return 1;
		}
		print "[DONE]\n\n";
	}
	if ( -f "$inpath/$logDir/$capName/$postInstall" ) {
		print "|## Executing postInstall script #########|\n\n";
			if ( system("inpath=$inpath capName=$capName logDir=$logDir sh $inpath/$logDir/$capName/$postInstall") != 0 ) {
				push(@errors,"# Error # : postInstall script failed for $capName.");
				return 1;
			}
		print "\n|#########################################|\n\n";
	}
	
	print "|-----------------------------------------|\n";
	
	return 0;	
}

sub removecap {
	my $capFileName = $_[0];
	my $ask = $_[1];
	
	my $newFileName = findCapTrack($capFileName);
	
	if ( $ask ) {
		my $answer = askUser("\n  Remove $capFileName?  ");
		if ($answer !~ /y/i) { print "\n  Removal cancelled\n"; return 1; }
	}
	
	my $verboseRemovecap='';
	if ( defined $config{'verboseRemovecap'} and $config{'verboseRemovecap'} ) {
		$verboseRemovecap=' -v'
	}
	
	if ( -f "$inpath/$logDir/$capFileName/$preRemove" ) {
		print "|## Executing preRemove script ##########|\n\n";
			if ( system("inpath=$inpath capName=$capFileName logDir=$logDir sh $inpath/$logDir/$capFileName/$preRemove") != 0 ) {
				print("\n# Error #:\n\tpreRemove script failed for $capFileName.\n");
				exit 1;
			}
		print "\n|#########################################|\n\n";
	}
	
	print "\n Removing left over files {\n";
	
		open(my $oldFile,  $newFileName) or die ("Cannot open $capFileName!\n");
		
		my %dirs;
		while(<$oldFile>) {
			my $oldLine = $_; chomp($oldLine);
			my $folder = dirname($oldLine);
			
			if ( ! exists($dirs{$folder}) ) {
				$dirs{$folder}='';
			}
			system("rm$verboseRemovecap \"$inpath$oldLine\"");
		}
		close($oldFile);
		if ( -f "$inpath/$pacodir/$capFileName" ) { system("rm -v $inpath/$pacodir/$capFileName"); }
	print "} [ Done ]\n";
	
	print "\n Removing left over directories...";
	
		foreach my $dir ( keys(%dirs) ) {
			my $cur=$dir;
			while ( $cur ne "/" and $cur ne '.' ) {
				$dirs{dirname($cur)} = '';
				$cur=dirname($cur);
			}
		}
		foreach my $dir ( sort mysort keys(%dirs) ) {
			if ( $dir ne "/" ) {
				system("rmdir \"$inpath$dir\" 2> /dev/null");
			}
		}
	
	print " [ Done ]\n";
	
	if ( -f "$inpath/$logDir/$capFileName/$postRemove" ) {
		print "|## Executing postRemove script ##########|\n\n";
			if ( system("inpath=$inpath capName=$capFileName logDir=$logDir sh $inpath/$logDir/$capFileName/$postRemove") != 0 ) {
				push(@errors,"# Error # : postRemove script failed for $capFileName.");
				return 1;
			}
		print "\n|#########################################|\n\n";
	}

	print "Removing captrack directory...";
		if ( system("rm -rf \"$inpath/$logDir/$capFileName\" 2> /dev/null") != 0 ) {
			push(@errors,"# Error # : captrack directory removal failed for $capFileName.");
		}
	print " [ Done ]\n";
}

sub h3kpkg {
	my $pkg = $_[0];
	my %dirs;
	
	print "  Initializing system...";
		# initialize makecap and directory for package
		if ( -d $pkg ) { print "\n\nFATAL ERROR :\n\t$pkg directory already exists\n"; exit 1; }
		open(my $fpkg, "$inpath/$logDir/$pkg/filelist") or die "\nError:\n\tCould not open package $inpath/$logDir/$pkg/filelist";
		
		mkdir($pkg) or die "\nError:\n\tCould not create directory $pkg";
		chdir $pkg or die "\nError:\n\tCound not chdir $pkg";
		if ( system("mkdir -p \"$logDir/$pkg\"") != 0 ) { die "\nError:\n\tCould not create directory $logDir/$pkg";}
		copy("$inpath/$logDir/$pkg/filelist", "$logDir/$pkg/filelist") or die "\nError:\n\tCould not copy file list";
	print " [DONE]\n";
	
	print "  Initializing capsule script files...";
		if ( -f "$inpath/$logDir/$pkg/$postInstall" ) {
			copy("$inpath/$logDir/$pkg/$postInstall", "$logDir/$pkg/$postInstall") or die "\nError:\n\tCould not copy $postInstall";
			system("chmod +x \"$logDir/$pkg/$postInstall\"");
		}
		
		if ( -f "$inpath/$logDir/$pkg/$preRemove" ) {
			copy("$inpath/$logDir/$pkg/$preRemove", "$logDir/$pkg/$preRemove") or die "\nError:\n\tCould not copy $preRemove";
			system("chmod +x \"$logDir/$pkg/$preRemove\"");
		}
		
		if ( -f "$inpath/$logDir/$pkg/$postRemove" ) {
			copy("$inpath/$logDir/$pkg/$postRemove", "$logDir/$pkg/$postRemove") or die "\nError:\n\tCould not copy $postRemove";
			system("chmod +x \"$logDir/$pkg/$postRemove\"");
		}
	print " [DONE]\n";
	
	print "  Generating capsule folder {\n";
	#write capsule scripts
	my $numfiles = 0;
	my $counter = 0;
	
	while(<$fpkg>) {
		my $line = $_; chomp($line);
		my $folder = dirname($line);
		
		if ( ! -d ".".$folder ) {
			system("mkdir -p \".$folder\"");
		}
		
		if ( -d $line ) {
			if ( system("mkdir -p \"./$line\"") != 0 ) {
				push(@errors,"Failed to create dir $line");
			} else {
				$counter++;
			}
			$numfiles++;
		} else {
			if ( system("cp -lp \"$line\" \"./$line\"") != 0 ) {
				push(@errors,"Failed to copy $line");
			} else {
				$counter++;
			}
			$numfiles++;
		}
	}
	close($fpkg);
	
	print "  } DONE\n";
	
	if ( -f "$inpath/$logDir/$pkg/changelog" ) {
			copy("$inpath/$logDir/$pkg/changelog", "$logDir/$pkg/changelog") or die "\nError:\n\tCould not copy changelog";
	} else {
		print "  Generating standard changelog...\n";
		open(my $fclog, ">$logDir/$pkg/changelog") or die "Could not open changelog";
		my @date = split(" ",`date`);
		print $fclog " @ $date[1] $date[2] $date[5]\n\t> Created\n";
		close($fclog);
	}
	
	# return number of files versus the number of files successfully copied
	return($numfiles,$counter);	
}

sub compress {
	my $pkg = $_[0];
	if ( -e "$pkg.cap" )  { push(@errors,"$pkg.cap already exists, won't overwrite, operation cancelled"); } 
	else {
		if ( -d "$pkg" ) {
			if ( defined $config{'stripOnCompress'} and $config{'stripOnCompress'} ) {
				print "  Stripping binary debugging data...";
				if ( system("cd $pkg && find . -type f -exec strip --strip-debug '{}' ';' &> /dev/null && cd ..") != 0 ){
					push(@errors,"could not strip binaries");
					return;
				}
				print " [DONE]\n";
			}
			my $verboseCompress='';
			if ( defined $config{'verboseMakeCapCompress'} and $config{'verboseMakeCapCompress'} ) {
				$verboseCompress = 'v';
			}
			print "  Compressing capsule...\n";
			my $dir = (split("/",$pkg))[0];
			#generate machine info for repo monitor
			system("uname -a > $pkg/$logDir/$pkg/machine");
			if ( system("cd $pkg && tar c".$verboseCompress."pjf ../$dir.cap * && cd ..") == 0 ) {
				print "\t[DONE]\n";
				print "\n".'@ Summary @-@-@-@-@-@-@-@-@-@-@-@-@-@-@-@-@-@-@-@-@-@-@-@-@-@'."\n\n";
				print "  Generating md5sum\n";
				print "  MD5SUM = ";
				if ( system("md5sum $dir.cap") == 0 ) {
					print "\n  Capsule successfully created at $dir.cap\n";
					print "\n".'@-@-@-@-@-@-@-@-@-@-@-@-@-@-@-@-@-@-@-@-@-@-@-@-@-@-@-@-@-@-@'."\n\n";
					return 0;
				} else { push(@errors,"md5sum for $pkg.cap could not be created"); } 
			} else { push(@errors,"$pkg could not be compressed"); }
		} else { push(@errors,"$pkg does not exist or is not a directory"); }
	}
	print "Capsule compression failed\n";
	print "\t-------------------------------------------------\n\n";
	return 1;
}

sub dumpErrors {
	if (scalar(@errors)==0) {
		print " + No errors\n";
	} else {
		print "\n";
		print " - Errors ...\n";
		print "---------------------------------------------------->\n";
		foreach my $error (@errors) {
			print "  $error\n";
		}
		print "---------------------------------------------------->\n";
		print " - ".scalar(@errors)." errors\n";
	}
}

#%%%%%%%%%%%%%%%%%%%%#
# parse the command line arguments, and store the values into the hash table opts
my %opts=();
GetOptions(
		"t:s" => \$opts{"captrack"},
		"cmd:s" => \$opts{"capcom"},
		"cl:s" => \$opts{"listCaptrack"},
		"cL:s" => \$opts{"listAllCaptrack"},
		"e:s" => \$opts{"depCheck"},
		"pv:s" => \$opts{"printVersion"},
		"p:s" => \$opts{"printVersionBot"},
		"db:s" => \$opts{"alias"},
		"b:s" => \$opts{"buildCap"},
		"c:s" => \$opts{"compressCap"},
		"depdb:s" => \$opts{"depAlias"},
		"i|install|captool:s"=> \$opts{"install"},
		"I|Install|Captool:s"=> \$opts{"installNoConfirm"},
		"g|repo:s"=> \$opts{"getcap"},
		"G|Repo:s"=> \$opts{"getcapNoConfirm"},
		"r|remove|uninstall|removecap:s"=> \$opts{"remove"},
		"R|Remove|Uninstall|Removecap:s"=> \$opts{"removeNoConfirm"},
		"l|list:s"=> \$opts{"list"},
		"s|search:s"=> \$opts{"search"},
		"inpath|path:s"=> \$opts{"inpath"},
		"u:s"=> \$opts{"updateOld"},
		"u_new:s"=>\$opts{"updateLocalNew"},
		"help|h"=>\$opts{"help"},
		"version|v"=>\$opts{"version"}
	);
########################

# help and version info
########################
if ( $opts{"help"} ) {
	print "
 >> cap $globalVersion help page<<
	
 Licensed under the gpl,
 see http://www.gnu.org/copyleft/gpl.html for the full gpl license
	
	
   >> General Capsule functions
	
	-g <keyword> or -repo <keyword>
		Install a capsule from the repo, with dependency resolution
		Capitalize the first letter of the flag to
		install without confirmation
	
	-i <capsule> or -install <capsule>
		Install a capsule from the local machine/path
		Capitalize the first letter of the flag to
		install without confirmation
	
	-r <captrackname> or -remove <captrackname>
		Perform a removal of <captrackname> from the local machine/path
		Capitalize the first letter of the argument
		to install without confirmation
		^ Warning: use with caution!
	
	
	-l <keyword> or -list <keyword>
		Print an entry from the capsule database
	
	-db <alias>
		Change capsule database used for capsule requests
	
	-depdb <alias>
		Change capsule database for dependencies * Advanced usage *
	
	-s <term> or -search <keyword>
		Print an entry from the capsule database
	
  >> Updating a capsule
	
	-u <capname>
		Update a capsule installed on the system, specified by <capname>
	
	-u_new <capsule path>
		Update capsule specified by -u, to a specific capsule\n\t\ton the local machine/path.
	
	When -u is used, and -u_new is not specified, the capsule
	 updater will attempt to update the specified capsule
	  ( <capname> ) to the latest version from the capsule database.
	
  >> Capsule tracking/filelist functions
	
	-cl <captrackname>
		List the files from a captrack filelist
	
	-cL
		List all the captrack names installed locally
	
	-cmd \"<command>\"
		Set the command to track
	
	-t <captrackname>
		Track <command> and store captrack as <captrackname>,
		if <command> is not set
		'make install' is the default command
	
	
   >> Capsule constructions functions
	
	-b <captrackname>
		Build a capsule using tracked install
	
	-c <captrackfolder>
		Compress a capsule folder into a cap file
	
	
   >> Misc capsule functions
	
	-pv <keyword>
		Print the versions installed of the capsule specifed
	
	-e <depStatement>
		Evaluate a depStatement, ex: xchat(>=2.4)
	
	-inpath <path> or -path <path>
		Specify chroot for capsule installation
	
   >> More Detailed information
   
";
	exit 0;
}
if ( defined($opts{"version"}) ) {
	print "\n >> cap $globalVersion <<\n";
	print "\n Licensed under the gpl, \n";
	print " see http://www.gnu.org/copyleft/gpl.html for the full gpl license\n\n";
}

if (defined($opts{"inpath"}) ) {
	print "\nSetting path: ".$opts{"inpath"}."\n";
	$inpath = $opts{"inpath"};
}

########################
# capkg functions


if ( defined($opts{"listCaptrack"}) and $opts{"listCaptrack"} ne '') {
	if ( -f "$inpath/$logDir/".$opts{"listCaptrack"}."/filelist" ) {
		print "\n|#########################################|\n\n";
		system("cat $inpath/$logDir/".$opts{"listCaptrack"}."/filelist");
		print "\n|#########################################|\n";
	} else {
		push(@errors,"Could not find package ".$opts{l});
	}
}
if ( defined($opts{"listAllCaptrack"}) ) {
	print "\n|- Capsule Tracks ------------------------|\n";
	system("ls $inpath/$logDir");
	print "\n|-----------------------------------------|\n";
}

my $command = '';

if ( defined($opts{"capcom"}) and $opts{"capcom"} ne '' ) {
	$command = $opts{"capcom"};
}

if ( defined($opts{"captrack"}) and $opts{"captrack"} ne '' ){
	my $pkgname = $opts{"captrack"};
	if ( ! $command) {
		print "No command specified for $pkgname, use \"make install\"? [n] : ";
		my $ranswer = <STDIN>;
		if ($ranswer =~ m{^[y*,Y*]}) {
			$command = "make install";
		} else {
			print("\nError:\n\tNo command to track for \"$pkgname\"\n");
			exit 1
		}
	}
	if ( system("paco --version") == 127 ) {
		print("\nError:\n\tpaco is required to track packages\n");
		exit 1;
	}
	if ( ! -d "$pacodir" ) {
		if ( system("mkdir -p $pacodir") != 0 ) {
			print("\nError:\n\tCannot create paco directory '$pacodir'\n");
			exit 1;
		}
	}
	print "\n  capkg $globalVersion\n\n";
	if ( -d "$inpath/$logDir/$pkgname" ) {
		print("\nError:\n\t\"$pkgname\" has already been tracked once before\n");
		exit 1;
	}
	if ( defined $config{"trackNoWarn"} and ( $config{"trackNoWarn"} ne "no" and $config{"trackNoWarn"} ne '1' ) ) {
		print " Tracking : \"$pkgname\"\n";
		print "   Command : \"$command\"\n";
		print "Five seconds to abort before track begins... 0";
		$| = 1;
		for (my $i = 0; $i <= 5 ; $i+=1) {
			print "\b";
			print "$i";
			sleep 1;
		}
	}
	if ( ! -d "$inpath/$logDir/$pkgname" ) {
		if ( system("mkdir -p \"$inpath/$logDir/$pkgname\"") != 0 ) {
			print("\nError:\n\tCould not create directory '$inpath/$logDir/$pkgname'\n");
			exit 1;
		}
	}
	print "\n\n";
	print "  Tracking $command to package $pkgname\n";
	print "|-----------------------------------------|\n\n";
	system("paco -lp $pkgname \"$command\"");
	system("paco -f $pkgname > $inpath/$logDir/$pkgname/filelist");
	if ( system("sed -i 1d $inpath/$logDir/$pkgname/filelist") != 0 ) {
		print("\nError:\n\t\"$pkgname\" Failed file list cleansing\n");
	}
	print "\n|-----------------------------------------|\n";
	if ( `cat $inpath/$logDir/$pkgname/filelist | wc -l` == 0 ) {
		print("\nError:\n\tPackage \"$pkgname\" failed tracking\n");
		unlink "$inpath/$logDir/$pkgname/filelist";
		exit 1;
	}
	print "  Finished\n\n";
	exit 0;
}

########################


if (defined $opts{"depCheck"} ) {
	print evaluateDepCheck($opts{"depCheck"});
	exit 0;
}

if ( defined $opts{"printVersionBot"} ) {
	if ( $opts{"printVersionBot"} ne "" ) {
		print getVersion($opts{"printVersionBot"})."\n";
		exit 0;
	}
}

if (defined $opts{"buildCap"}) {
	my ($numfiles,$counter) = h3kpkg($opts{"buildCap"});
	if ( $numfiles < $counter ) {
		my $numoff = $counter - $numfiles;
		push(@errors,"# file count mismatch error, possible capsule corruption \n\t$numoff files not found or misplaced!");
	}
}

if (defined $opts{"compressCap"}) {
	compress($opts{"compressCap"});
}

if ( defined $opts{"printVersion"} ) {
	if ( $opts{"printVersion"} ne "" ) {
		my @vers = getVersions($opts{"printVersion"});
		print "\n \"".$opts{"printVersion"}."\" versions installed:\n";
		foreach my $ver (@vers) {
			print "\t- $ver\n";
		}
		print "\n";
	}
}

if ( defined $opts{"alias"} ) { 
	$alias = $opts{"alias"};
}

if ( defined $opts{"depAlias"} ) { 
	$depAlias = $opts{"depAlias"};
}

if ( defined $opts{"list"} ) { 
	my @list = split(/ /,$opts{"list"});
	print "\n";
	foreach my $lkey (@list) {
		printEntry($lkey);
	}
	print "\n";
}

if ( defined $opts{"search"} ) { capsearch($opts{"search"}); }

if (defined $opts{"install"}) { 
	my @list = split(/ /,$opts{"install"});
	foreach my $i (@list) { captool($i,1); }
}
if (defined $opts{"installNoConfirm"}) { 
	my @list = split(/ /,$opts{"installNoConfirm"});
	foreach my $i (@list) { captool($i,0); }
}
if (defined $opts{"remove"}) { 
	my @list = split(/ /,$opts{"remove"});
	foreach my $i (@list) { removecap($i,1); }
}
if (defined $opts{"removeNoConfirm"}) { 
	my @list = split(/ /,$opts{"removeNoConfirm"});
	foreach my $i (@list) { removecap($i,0); }
}

if (defined $opts{"getcap"}) {
	my @list = split(/ /,$opts{"getcap"});
	foreach my $i (@list) { if ( getcap($i,1) != 0 ) { dumpErrors(); exit 1; } }
}
if (defined $opts{"getcapNoConfirm"}) {
	my @list = split(/ /,$opts{"getcapNoConfirm"});
	foreach my $i (@list) { if ( getcap($i,0) != 0 ) { dumpErrors(); exit 1; } }
}

if ( defined($opts{"updateOld"})) {
	if ( $opts{"updateOld"} eq "" ) {
		print "\n Error:\n\tRequires input for -u\n\n"; exit 1;
	} else {
		if (defined($opts{"updateLocalNew"}) and $opts{"updateLocalNew"} ne "") {
			my @list;
			@list = split(/ /,$opts{"updateOld"});
			if ( scalar(@list) > 1 ) { print "\n Error:\n Cannot update multiple capsules using -u_new\n\n"; exit 1; }
			@list = split(/ /,$opts{"updateLocalNew"});
			if ( scalar(@list) > 1 ) { print "\n Error:\n Cannot update multiple capsules using -u_new\n\n"; exit 1; }
			
			upgradeClean($opts{"updateOld"}, 0, 0, $opts{"updateLocalNew"});
		} else {
			my @list = split(/ /,$opts{"updateOld"});
			foreach my $i (@list) { 
				upgradeClean($i,0);
			}
		}
	}
}

# if there are non-fatal errors, print them out along with a summary of performed actions
print "\n @ Summary\n";
if ( $installs > 0 ) { print " + $installs install(s) performed\n"; }
if ( $removes > 0 ) { print " + $removes removal(s) performed\n"; }
if ( $depcaps > 0 ) { print " + $depcaps dependency(s) resolved\n"; }
if ( $updates > 0 ) { print " + $updates update(s) performed\n"; }
if ( $lists > 0 ) { print " + $lists capsule(s) listed\n"; }
dumpErrors();
print "\n";
exit 0;
