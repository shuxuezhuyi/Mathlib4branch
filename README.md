# Mathlib4branch

Copy from https://github.com/leanprover-community/mathlib4/branches or somewhere similar.

Intended to be a folder within Mathlib​4.

## require

leanprover/lean4:v4.2.0-rc1

and

mathlib4/commit/644ffcede0f3d1da4b7cfc97215cd7ab5e071696

but not necessary.

## how to use

```shell
find Mathlib -name "*.lean" | env LC_ALL=C sort | sed 's/\.lean//;s,/,.,g;s/^/import /' > Mathlib.lean

lake build
```

## Source

https://github.com/girving/ray