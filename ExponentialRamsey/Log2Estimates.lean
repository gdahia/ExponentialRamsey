/-
Copyright (c) 2022 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Algebra.Order.GroupWithZero.Unbundled.Basic

/-!
# Estimates on log base 2 of rationals by iterative squaring
-/

noncomputable section

open Real

theorem logb_zpow {b x : ℝ} (m : ℤ) : logb b (x ^ m) = m * logb b x := by
  rw [logb, log_zpow, mul_div_assoc, logb]

theorem logb_base {b : ℝ} (hb : 0 < b) (hb' : b ≠ 1) : logb b b = 1 :=
  div_self (log_ne_zero_of_pos_of_ne_one hb hb')

/-- Variant of `Real.logb_div_base` for dividing the argument by its base. -/
theorem logb_div_base' {b x : ℝ} (hb : 0 < b) (hb' : b ≠ 1) (hx : x ≠ 0) :
    logb b (x / b) = logb b x - 1 := by rw [logb_div hx hb.ne', logb_base hb hb']

/-- the form of goal which is used to prove log2 estimates -/
def LogBase2Goal (x₁ x₂ a₁ a₂ : ℝ) : Prop :=
  0 < x₁ → x₁ ≤ x₂ → a₁ < logb 2 x₁ ∧ logb 2 x₂ < a₂

theorem log_base2_square {x₁ x₂ a₁ a₂ : ℝ} (h : LogBase2Goal (x₁ ^ 2) (x₂ ^ 2) (2 * a₁) (2 * a₂)) :
    LogBase2Goal x₁ x₂ a₁ a₂ := fun hx₁ hx₂ => by
  simpa [logb_pow] using h (pow_pos hx₁ _) (pow_le_pow_left₀ hx₁.le hx₂ _)

theorem log_base2_weaken {x₁ x₂ a₁ a₂ : ℝ} (x₃ x₄ : ℝ) (h : LogBase2Goal x₃ x₄ a₁ a₂) (h₁ : x₃ ≤ x₁)
    (h₂ : x₂ ≤ x₄) (h₃ : 0 < x₃) : LogBase2Goal x₁ x₂ a₁ a₂ :=
  by
  intro hx₁ hx₂
  have t := h h₃ (h₁.trans (hx₂.trans h₂))
  exact
    ⟨t.1.trans_le (logb_le_logb_of_le one_lt_two h₃ h₁),
      t.2.trans_le' (logb_le_logb_of_le one_lt_two (hx₁.trans_le hx₂) h₂)⟩

theorem log_base2_half {x₁ x₂ a₁ a₂ : ℝ} (h : LogBase2Goal (x₁ / 2) (x₂ / 2) (a₁ - 1) (a₂ - 1)) :
    LogBase2Goal x₁ x₂ a₁ a₂ := fun hx₁ hx₂ => by
  have h_two_ne_one : (2 : ℝ) ≠ 1 := by norm_num
  simpa [logb_div_base', hx₁.ne', h_two_ne_one, (hx₁.trans_le hx₂).ne'] using
    h (half_pos hx₁) (div_le_div_of_nonneg_right hx₂ zero_le_two)

theorem log_base2_scale {x₁ x₂ a₁ a₂ : ℝ} (m : ℤ)
    (h : LogBase2Goal (x₁ * 2 ^ m) (x₂ * 2 ^ m) (a₁ + m) (a₂ + m)) : LogBase2Goal x₁ x₂ a₁ a₂ := by
  intro hx₁ hx₂
  have i : 0 < (2 : ℝ) ^ m := zpow_pos zero_lt_two _
  have := h (mul_pos hx₁ i) (mul_le_mul_of_nonneg_right hx₂ i.le)
  simpa [logb_mul hx₁.ne' i.ne', logb_mul (hx₁.trans_le hx₂).ne' i.ne', logb_zpow, logb_base,
    (by norm_num : (2 : ℝ) ≠ 1)] using this

theorem log_base2_start {x₁ x₂ a₁ a₂ : ℝ} (hx₁ : 0 < x₁) (hx₂ : x₁ ≤ x₂)
    (h : LogBase2Goal x₁ x₂ a₁ a₂) : a₁ < logb 2 x₁ ∧ logb 2 x₂ < a₂ :=
  h hx₁ hx₂

theorem log_base2_end {x₁ x₂ a₁ a₂ : ℝ} (hx₁ : 1 < x₁) (hx₂ : x₂ < 2) (ha₁ : a₁ ≤ 0)
    (ha₂ : 1 ≤ a₂) : LogBase2Goal x₁ x₂ a₁ a₂ := by
  rintro - h
  refine' ⟨ha₁.trans_lt (div_pos (log_pos hx₁) (log_pos one_lt_two)), lt_of_lt_of_le _ ha₂⟩
  rw [logb, div_lt_one (log_pos one_lt_two)]
  exact log_lt_log ((zero_le_one.trans_lt hx₁).trans_le h) hx₂

-- TODO: either temporarily restore `weaken` macro, or create a log library under b-mehta somewhere
-- namespace Tactic
--
-- namespace Interactive
--
-- /- ./././Mathport/Syntax/Translate/Tactic/Mathlib/Core.lean:38:34: unsupported: setup_tactic_parser -/
-- /- ./././Mathport/Syntax/Translate/Expr.lean:337:4: warning: unsupported (TODO): `[tacs] -/
-- /-- a quick macro to simplify log2 estimate proofs -/
-- unsafe def weaken (t u : parse parser.pexpr) : tactic Unit :=
--   implementation omitted
--
-- end Interactive
--
-- end Tactic
