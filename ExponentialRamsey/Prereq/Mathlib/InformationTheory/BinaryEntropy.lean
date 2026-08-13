/-
Copyright (c) 2023 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Binary entropy function
Defines the function `h(p)` which gives the entropy of a Bernoulli random variable with probability
`p`. We define the function directly, since it is a useful function as is.

Mathlib's `Real.binEntropy` is the special case `b = exp 1`; `binEnt_eq_binEntropy_div` relates the
two, which lets the analytic facts be inherited from there.
-/


open Real

/-- The binary entropy function -/
noncomputable def binEnt (b p : ℝ) : ℝ :=
  -p * logb b p - (1 - p) * logb b (1 - p)

@[simp]
theorem binEnt_zero {b : ℝ} : binEnt b 0 = 0 := by simp [binEnt]

theorem binEnt_symm {b p : ℝ} : binEnt b (1 - p) = binEnt b p := by
  rw [binEnt, sub_sub_cancel, binEnt]; ring

@[simp]
theorem binEnt_one {b : ℝ} : binEnt b 1 = 0 := by simp [binEnt]

/-- An alternate expression for the binary entropy in terms of `Real.binEntropy`, which is where the
analytic facts about it are proved. -/
theorem binEnt_eq_binEntropy_div {b p : ℝ} : binEnt b p = binEntropy p / log b := by
  rw [binEnt, binEntropy, logb, logb, log_inv, log_inv]; ring

theorem binEnt_nonneg {b p : ℝ} (hb : 1 < b) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) : 0 ≤ binEnt b p :=
  (div_nonneg (binEntropy_nonneg hp₀ hp₁) (log_nonneg hb.le)).trans_eq
    binEnt_eq_binEntropy_div.symm

/-- An alternate expression for the binary entropy in terms of natural logs, which is sometimes
easier to prove analytic facts about. -/
theorem binEnt_eq {b p : ℝ} : binEnt b p = (-(p * log p) + -((1 - p) * log (1 - p))) / log b := by
  rw [binEnt, logb, logb, neg_mul, sub_eq_add_neg, add_div, mul_div_assoc', mul_div_assoc', neg_div,
    neg_div]

theorem binEnt_e {p : ℝ} : binEnt (exp 1) p = -p * log p - (1 - p) * log (1 - p) := by
  rw [binEnt, logb, logb, log_exp, div_one, div_one]

