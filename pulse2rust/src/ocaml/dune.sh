#!/usr/bin/env bash
set -e
set -x
cd $(cd `dirname $0` && pwd)
if [[ "$OS" = Windows_NT ]] ; then
    cc_linker="-cc $(rustup toolchain list -v | grep '^[^- ]*-x86_64-pc-windows-gnu' | sed 's!^[^ ]* \+\((default)\t\+\)\?!!')/lib/rustlib/x86_64-pc-windows-gnu/bin/gcc-ld/ld.lld.exe"
fi
cat >dune <<EOF
(include_subdirs unqualified)

(rule
 (targets librustast_bindings.a)
 (deps (source_tree .))
 (action
  (no-infer
   (progn
    (run cargo build)
    (run cp target/debug/librustast_bindings.a ./librustast_bindings.a)
   ))))

(executable
 (name main)
 (libraries batteries fstar.lib menhirLib)
 (foreign_archives rustast_bindings)
 (flags (:standard $cc_linker -w -27-33-8-26))
)
EOF
exec dune build
