/-
Copyright (c) 2023 Geoffrey Irving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Irving
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Complex

/-!
## `Complex.pow` and `pow` interact nicely
-/

-- Remove once https://github.com/leanprover/lean4/issues/2220 is fixed
local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y)

theorem pow_mul_nat {z w : ℂ} {n : ℕ} : (z ^ w) ^ n = z ^ (w * n) := by
  by_cases z0 : z = 0
  · rw [z0]
    by_cases w0 : w = 0; · rw [w0]; simp
    by_cases n0 : n = 0; · rw [n0]; simp
    have wn0 : w * n ≠ 0 := mul_ne_zero w0 (Nat.cast_ne_zero.mpr n0)
    rw [Complex.zero_cpow w0]
    rw [Complex.zero_cpow wn0]
    exact zero_pow' n n0
  simp only [Complex.cpow_def_of_ne_zero z0, ← Complex.exp_nat_mul]
  ring_nf
