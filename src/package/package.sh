#!/usr/bin/env bash
set -e
set -x

unset CDPATH
my_pwd="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
export STEEL_HOME=$(realpath $my_pwd/../..)

if [[ -z "$OS" ]] ; then
    OS=$(uname)
fi

is_windows=false
if [[ "$OS" = "Windows_NT" ]] ; then
   is_windows=true
fi

if [[ -z $CI_THREADS ]] ; then
    CI_THREADS=4
fi

! [[ -e fstar ]]
! [[ -e steel ]]

# Create a F* binary package
if [[ -z $FSTAR_HOME ]] ; then
    fstar_exe=$(which fstar.exe)
    FSTAR_HOME=$(realpath $(dirname $fstar_exe)/..)
fi
rm -rf $FSTAR_HOME/src/ocaml-output/fstar*
OTHERFLAGS='--admit_smt_queries true' make -C $FSTAR_HOME -j $CI_THREADS package
fstar_pkg_root=$FSTAR_HOME/src/ocaml-output/fstar
if $is_windows ; then
    unzip $fstar_pkg_root.zip
else
    tar xf $fstar_pkg_root.tar.gz
fi
mv fstar steel

# Compile and install Steel into that package
# Important: we are using F* from the package itself to compile Steel
export FSTAR_HOME=$PWD/steel
OTHERFLAGS='--admit_smt_queries true' make -C $STEEL_HOME -j $CI_THREADS
PREFIX=$PWD/steel make -C $STEEL_HOME -j $CI_THREADS install
if $is_windows ; then
    steel_pkg=steel.zip
    ! [[ -e $steel_pkg ]]
    zip -r -9 $steel_pkg steel
else
    steel_pkg=steel.tar.gz
    ! [[ -e $steel_pkg ]]
    tar czf $steel_pkg steel
fi
