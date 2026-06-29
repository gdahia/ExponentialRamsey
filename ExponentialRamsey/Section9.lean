/-
Copyright (c) 2023 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import ExponentialRamsey.Section8
import ExponentialRamsey.Prereq.Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Section 9
-/


namespace SimpleGraph

open scoped BigOperators ExponentialRamsey Nat Real

open Filter Finset Nat Real Asymptotics

theorem is_o_one_iff {α : Type*} {l : Filter α} {f : α → ℝ} :
    (f =o[l] fun _ => (1 : ℝ)) ↔ Tendsto f l (nhds 0) :=
  Asymptotics.isLittleO_one_iff ℝ

-- fails at n = 0 because rhs is 0 and lhs is 1
theorem little_o_stirling :
    ∃ f : ℕ → ℝ,
      (f =o[atTop] fun i => (1 : ℝ)) ∧
        ∀ n : ℕ, n ≠ 0 → (n.factorial : ℝ) = (1 + f n) * sqrt (2 * π * n) * (n / exp 1) ^ n := by
  refine' ⟨fun n => Stirling.stirlingSeq n / sqrt π - 1, _, _⟩
  · rw [is_o_one_iff]
    have hπ : √π ≠ 0 := sqrt_ne_zero'.2 pi_pos
    have h : Tendsto (fun n => Stirling.stirlingSeq n / √π) atTop (nhds 1) := by
      have := Stirling.tendsto_stirlingSeq_sqrt_pi.div_const (√π)
      rwa [div_self hπ] at this
    convert h.sub_const 1 using 2
    norm_num
  intro n hn
  simp only [Stirling.stirlingSeq]
  have h1 : (1 : ℝ) + (n.factorial / (√(2 * ↑n) * (↑n / exp 1) ^ n) / √π - 1) =
      n.factorial / (√(2 * ↑n) * (↑n / exp 1) ^ n) / √π := by ring
  rw [h1, show 2 * π * ↑n = 2 * ↑n * π from by ring,
    sqrt_mul (by positivity : (0 : ℝ) ≤ 2 * ↑n) π]
  have hπ : √π ≠ 0 := sqrt_ne_zero'.2 pi_pos
  have hn2 : √(2 * ↑n) ≠ 0 := sqrt_ne_zero'.mpr (by positivity)
  have hne : (↑n / exp 1) ^ n ≠ 0 := by positivity
  field_simp


-- giving explicit bounds here requires an explicit version of stirling
theorem weak_little_o_stirling :
    ∃ f : ℕ → ℝ,
      (f =o[atTop] fun i => (i : ℝ)) ∧ ∀ᶠ n : ℕ in atTop, (n.factorial : ℝ) = 2 ^ f n * (n / exp 1) ^ n := by
  sorry


-- g is log 2 - log k
theorem nine_four_log_aux :
    ∃ g : ℕ → ℝ,
      (g =o[atTop] fun i => (i : ℝ)) ∧
        ∀ᶠ l : ℕ in atTop, ∀ k, l ≤ k → g k ≤ log (k + l) - log k - log l := by
  refine' ⟨fun k => log 2 - log k, _, _⟩
  · suffices (fun k : ℝ => log 2 - log k) =o[atTop] id by
      exact this.comp_tendsto tendsto_natCast_atTop_atTop
    exact IsLittleO.sub (isLittleO_const_id_atTop _) isLittleO_log_id_atTop
  filter_upwards [eventually_gt_atTop 0] with l hl₀ k hlk
  rw [sub_sub, add_comm (log _), ← sub_sub, sub_le_sub_iff_right, ← log_div]
  · refine' log_le_log zero_lt_two _
    rwa [le_div_iff₀, two_mul, add_le_add_iff_right, Nat.cast_le]
    rwa [Nat.cast_pos]
  · positivity
  · positivity


theorem nine_four_aux_aux {f : ℕ → ℝ} (hf : f =o[atTop] fun i => (1 : ℝ)) :
    ∀ᶠ l : ℕ in atTop, ∀ k, l ≤ k → 2 ^ (-3 : ℝ) ≤ (1 + f (k + l)) / ((1 + f k) * (1 + f l)) := by
  rw [isLittleO_one_iff ℝ] at hf
  have h₁ : (-1 / 2 : ℝ) < 0 := by norm_num
  filter_upwards [eventually_gt_atTop 0, top_adjuster (hf.eventually (eventually_ge_nhds h₁)),
    top_adjuster (hf.eventually (eventually_le_nhds zero_lt_one))] with l hn1 hneg h1 k hlk
  have h₂ : ∀ k, l ≤ k → 1 / 2 ≤ 1 + f k := by
    intro k hlk
    linarith only [hneg k hlk]
  have h₃ : ∀ k, l ≤ k → 1 + f k ≤ 2 := by
    intro k hlk
    linarith only [h1 k hlk]
  have h₄ : ∀ k, l ≤ k → 0 < 1 + f k := by
    intro k hlk
    linarith only [h₂ k hlk]
  have h23 : (2 : ℝ) ^ (-3 : ℝ) = 1 / 8 := by norm_num
  rw [h23, le_div_iff₀ (mul_pos (h₄ _ hlk) (h₄ _ le_rfl))]
  have h4le : (1 + f k : ℝ) * (1 + f l) ≤ 2 * 2 :=
    mul_le_mul (h₃ _ hlk) (h₃ _ le_rfl) (h₄ _ le_rfl).le (le_of_lt zero_lt_two)
  have h4 : (1 : ℝ) / 8 * ((1 + f k) * (1 + f l)) ≤ 1 / 2 :=
    calc (1 : ℝ) / 8 * ((1 + f k) * (1 + f l)) ≤ 1 / 8 * (2 * 2) :=
        mul_le_mul_of_nonneg_left h4le (by norm_num)
    _ = 1 / 2 := by norm_num
  linarith [h₂ _ (Nat.le_add_left l k)]


-- f is -3 + (log 2 - log k - log (2 π)) / (2 log 2)
--    = -3 - (log k + log π) / (2 log 2)
theorem nine_four_aux :
    ∃ f : ℕ → ℝ,
      (f =o[atTop] fun i => (i : ℝ)) ∧
        ∀ᶠ l : ℕ in atTop,
          ∀ k,
            l ≤ k →
              (2 : ℝ) ^ f k * ((k + l) ^ (k + l) / (k ^ k * l ^ l)) ≤ ((k + l).choose l : ℝ) := by
  sorry


-- f is -3 + (log 2 - log k - log (2 π)) / (2 log 2)
theorem nine_four :
    ∃ f : ℕ → ℝ,
      (f =o[atTop] fun i => (i : ℝ)) ∧
        ∀ᶠ l : ℕ in atTop,
          ∀ k,
            l ≤ k →
              ∀ γ : ℝ,
                γ = l / (k + l) →
                  (2 : ℝ) ^ f k * γ ^ (-l : ℝ) * (1 - γ) ^ (-k : ℝ) ≤ ((k + l).choose l : ℝ) := by
  sorry


theorem end_ramseyNumber (μ₀ μ₁ p₀ : ℝ) (hμ₀ : 0 < μ₀) (hμ₁ : μ₁ < 1) (hp₀ : 0 < p₀) :
    ∀ᶠ l : ℕ in atTop,
      ∀ k,
        l ≤ k →
          ∀ μ,
            μ₀ ≤ μ →
              μ ≤ μ₁ →
                ∀ n : ℕ,
                  ∀ χ : TopEdgeLabelling (Fin n) (Fin 2),
                    (¬∃ (m : Finset (Fin n)) (c : Fin 2),
                          χ.MonochromaticOf m c ∧ ![k, l] c ≤ m.card) →
                      ∀ ini : BookConfig χ,
                        p₀ ≤ ini.p →
                          (endState μ k l ini).X.card ≤
                            ramseyNumber ![k, ⌈(l : ℝ) ^ (3 / 4 : ℝ)⌉₊] := by
  filter_upwards [one_div_k_lt_p μ₀ μ₁ p₀ hμ₀ hμ₁ hp₀, top_adjuster (eventually_gt_atTop 0)] with l
    hl hl₀ k hlk μ hμl hμu n χ hχ ini hini
  refine' (condition_fails_at_end (hl₀ k hlk).ne' (hl₀ l le_rfl).ne').resolve_right _
  rw [not_le]
  exact hl k hlk μ hμl hμu n χ hχ ini hini _ le_rfl


theorem end_ramseyNumber_pow_isLittleO :
    ∃ f : ℕ → ℝ,
      (f =o[atTop] fun i => (i : ℝ)) ∧
        ∀ μ₀ μ₁ p₀ : ℝ,
          0 < μ₀ →
            μ₁ < 1 →
              0 < p₀ →
                ∀ᶠ l : ℕ in atTop,
                  ∀ k,
                    l ≤ k →
                      ∀ μ,
                        μ₀ ≤ μ →
                          μ ≤ μ₁ →
                            ∀ n : ℕ,
                              ∀ χ : TopEdgeLabelling (Fin n) (Fin 2),
                                (¬∃ (m : Finset (Fin n)) (c : Fin 2),
                                      χ.MonochromaticOf m c ∧ ![k, l] c ≤ m.card) →
                                  ∀ ini : BookConfig χ,
                                    p₀ ≤ ini.p → ((endState μ k l ini).X.card : ℝ) ≤ 2 ^ f k := by
  refine' ⟨fun k => (log 2)⁻¹ * (2 * (log k * k ^ (3 / 4 : ℝ))), _, _⟩
  · refine' IsLittleO.const_mul_left _ _
    refine' IsLittleO.const_mul_left _ _
    suffices (fun k => log k * k ^ (3 / 4 : ℝ)) =o[atTop] id by
      exact this.comp_tendsto tendsto_natCast_atTop_atTop
    refine'
      (IsLittleO.mul_isBigO (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4))
            (isBigO_refl _ _)).congr'
        EventuallyEq.rfl _
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with k hk
    rw [← rpow_add hk]
    norm_num1
    rw [rpow_one]
    rfl
  intro μ₀ μ₁ p₀ hμ₀ hμ₁ hp₀
  filter_upwards [end_ramseyNumber μ₀ μ₁ p₀ hμ₀ hμ₁ hp₀, eventually_ge_atTop 1] with l hl hl₁ k
    hlk μ hμl hμu n χ hχ ini hini
  specialize hl k hlk μ hμl hμu n χ hχ ini hini
  rw [rpow_def_of_pos two_pos, mul_inv_cancel_left₀ (log_pos one_lt_two).ne', mul_left_comm, ←
    rpow_def_of_pos (Nat.cast_pos.2 _)]
  swap
  · exact hl₁.trans hlk
  rw [ramseyNumber_pair_swap] at hl
  refine' (Nat.cast_le.2 (hl.trans ramseyNumber_le_right_pow_left')).trans _
  rw [Nat.cast_pow, ← Real.rpow_natCast]
  refine' rpow_le_rpow_of_exponent_le (Nat.one_le_cast.2 (hl₁.trans hlk)) _
  refine'
    (ceil_le_two_mul _).trans
      (mul_le_mul_of_nonneg_left
        (rpow_le_rpow (Nat.cast_nonneg _) (Nat.cast_le.2 hlk) (by norm_num1)) two_pos.le)
  exact (one_le_rpow (Nat.one_le_cast.2 hl₁) (by norm_num1)).trans' (by norm_num1)


theorem descFactorial_eq_prod {n k : ℕ} : n.descFactorial k = ∏ i ∈ Finset.range k, (n - i) := by
  exact Nat.descFactorial_eq_prod_range n k


theorem cast_descFactorial_eq_prod {n k : ℕ} :
    (n.descFactorial k : ℝ) = ∏ i ∈ Finset.range k, ((n - i : ℕ) : ℝ) := by
  rw [descFactorial_eq_prod]
  norm_cast


theorem pow_div_le_choose {n k : ℕ} (h : k ≤ n) : (n / k : ℝ) ^ k ≤ n.choose k := by
  have h1 : k.factorial ∣ n.descFactorial k := Nat.factorial_dvd_descFactorial _ _
  have h2 : (↑k.factorial : ℝ) ≠ 0 := by positivity
  rw [Nat.choose_eq_descFactorial_div_factorial, Nat.cast_div h1 h2,
    ← Finset.prod_range_add_one_eq_factorial, Nat.cast_prod, ← Finset.prod_range_reflect,
    cast_descFactorial_eq_prod, ← Finset.prod_div_distrib]
  suffices h : ∀ x ∈ Finset.range k, (n / k : ℝ) ≤ (↑(n - x) : ℝ) / (k - 1 - x + 1 : ℕ) by
    have key := Finset.prod_le_prod (fun x (_ : x ∈ Finset.range k) => by positivity) h
    simp only [Finset.prod_const, Finset.card_range] at key ⊢
    exact key
  intro x hx
  rw [Finset.mem_range] at hx
  have hlt : 0 < k - x := Nat.sub_pos_of_lt hx
  rw [Nat.sub_sub, add_comm 1, ← Nat.sub_sub, Nat.sub_add_cancel hlt]
  rw [div_le_div_iff₀ (Nat.cast_pos.2 (Nat.pos_of_ne_zero (by omega : k ≠ 0)))
    (Nat.cast_pos.2 hlt)]
  rw [Nat.cast_sub hx.le, Nat.cast_sub (hx.le.trans h), mul_sub, sub_mul,
    sub_le_sub_iff_left, mul_comm, ← Nat.cast_mul, ← Nat.cast_mul, Nat.cast_le]
  exact Nat.mul_le_mul_right _ h


theorem exp_le_one_sub_inv {x : ℝ} (hx : x < 1) : exp x ≤ (1 - x)⁻¹ := by
  rw [← one_mul ((1 - x)⁻¹), le_mul_inv_iff₀ (sub_pos_of_lt hx)]
  convert mul_le_mul_of_nonneg_left (add_one_le_exp (-x)) (exp_pos x).le using 1
  · ring
  rw [← Real.exp_add]
  ring_nf
  rw [Real.exp_zero]


theorem le_of_gamma_le_half {l k : ℕ} {γ : ℝ} (h : γ = l / (k + l)) (hl : 0 < l) (hγ : γ ≤ 1 / 2) :
    l ≤ k := by
  rwa [h, div_le_div_iff₀, one_mul, mul_comm, two_mul, add_le_add_iff_right, Nat.cast_le] at hγ
  · exact lt_add_of_le_of_pos (Nat.cast_nonneg k) (Nat.cast_pos.2 hl)
  · exact two_pos


theorem nine_three_lower_n (γ₀ : ℝ) (hγ₀ : 0 < γ₀) :
    ∀ᶠ l : ℕ in atTop,
      ∀ k : ℕ,
        ∀ γ : ℝ,
          γ = l / (k + l) →
            γ₀ ≤ γ →
              γ < 1 →
                l ≤ k →
                  ∀ δ : ℝ, δ ≤ γ / 20 → ∀ n : ℕ, exp (-δ * k) * (k + l).choose l ≤ n → 2 ≤ n := by
  sorry


theorem ge_floor {n : ℝ} (h : 1 ≤ n) : (n / 2 : ℝ) ≤ ⌊(n : ℝ)⌋₊ := by
  by_cases h₂ : n < 2
  · have : (1 : ℝ) ≤ ⌊n⌋₊ := by rwa [Nat.one_le_cast, Nat.one_le_floor_iff]
    refine' this.trans' _
    linarith
  · refine' (Nat.sub_one_lt_floor n).le.trans' _
    linarith


theorem nine_three_part_one :
    ∃ f : ℕ → ℝ,
      (f =o[atTop] fun i => (i : ℝ)) ∧
        ∀ γ₀ : ℝ,
          0 < γ₀ →
            ∀ᶠ l : ℕ in atTop,
              ∀ k : ℕ,
                ∀ γ : ℝ,
                  γ = l / (k + l) →
                    γ₀ ≤ γ →
                      γ ≤ 1 / 5 →
                        l ≤ k →
                          ∀ δ : ℝ,
                            δ = min (1 / 200) (γ / 20) →
                              ∀ n : ℕ,
                                ∀ χ : TopEdgeLabelling (Fin n) (Fin 2),
                                  (¬∃ (m : Finset (Fin n)) (c : Fin 2),
                                        χ.MonochromaticOf m c ∧ ![k, l] c ≤ m.card) →
                                    ∀ ini : BookConfig χ,
                                      1 / 4 ≤ ini.p →
                                        ⌊(n / 2 : ℝ)⌋₊ ≤ ini.X.card →
                                          exp (-δ * k) * (k + l).choose l ≤ n →
                                            exp (-δ * k) *
                                                  (1 - γ) ^ (-k + (redSteps γ k l ini).card : ℝ) *
                                                (beta γ k l ini / γ) ^
                                                  (densitySteps γ k l ini).card ≤
                                              2 ^ f k := by
  sorry


theorem nine_three_part_two :
    ∃ f : ℕ → ℝ,
      (f =o[atTop] fun i => (i : ℝ)) ∧
        ∀ γ₀ : ℝ,
          0 < γ₀ →
            ∀ᶠ l : ℕ in atTop,
              ∀ k : ℕ,
                ∀ γ : ℝ,
                  γ = l / (k + l) →
                    γ₀ ≤ γ →
                      γ ≤ 1 / 5 →
                        l ≤ k →
                          ∀ δ : ℝ,
                            δ = min (1 / 200) (γ / 20) →
                              ∀ n : ℕ,
                                ∀ χ : TopEdgeLabelling (Fin n) (Fin 2),
                                  (¬∃ (m : Finset (Fin n)) (c : Fin 2),
                                        χ.MonochromaticOf m c ∧ ![k, l] c ≤ m.card) →
                                    ∀ ini : BookConfig χ,
                                      1 / 4 ≤ ini.p →
                                        ⌊(n / 2 : ℝ)⌋₊ ≤ ini.X.card →
                                          exp (-δ * k) * (k + l).choose l ≤ n →
                                            γ * (k - (redSteps γ k l ini).card) ≤
                                              beta γ k l ini * (redSteps γ k l ini).card / (1 - γ) *
                                                    log (γ / beta γ k l ini) +
                                                  δ * k +
                                                f k := by
  sorry


theorem hMul_log_ineq {x : ℝ} (hx : 0 < x) : -x * log x ≤ exp (-1) := by
  have := add_one_le_exp (-log x - 1)
  rwa [sub_add_cancel, sub_eq_add_neg, Real.exp_add, Real.exp_neg, exp_log hx, inv_mul_eq_div,
    le_div_iff₀ hx, mul_comm, mul_neg, ← neg_mul] at this


theorem hMul_log_ineq_special {c x : ℝ} (hc : 0 < c) (hx : 0 < x) : x * log (c / x) ≤ c / exp 1 := by
  have := hMul_log_ineq (div_pos hx hc)
  rwa [neg_mul, ← mul_neg, ← log_inv, inv_div, div_mul_eq_mul_div, div_le_iff₀ hc, Real.exp_neg,
    inv_mul_eq_div] at this


theorem nine_three_part_three (γ₀ : ℝ) (hγ₀ : 0 < γ₀) :
    ∃ f : ℕ → ℝ,
      (f =o[atTop] fun i => (i : ℝ)) ∧
        ∀ᶠ l : ℕ in atTop,
          ∀ k : ℕ,
            ∀ γ : ℝ,
              γ = l / (k + l) →
                γ₀ ≤ γ →
                  γ ≤ 1 / 5 →
                    l ≤ k →
                      ∀ δ : ℝ,
                        δ = min (1 / 200) (γ / 20) →
                          ∀ n : ℕ,
                            ∀ χ : TopEdgeLabelling (Fin n) (Fin 2),
                              (¬∃ (m : Finset (Fin n)) (c : Fin 2),
                                    χ.MonochromaticOf m c ∧ ![k, l] c ≤ m.card) →
                                ∀ ini : BookConfig χ,
                                  1 / 4 ≤ ini.p →
                                    ⌊(n / 2 : ℝ)⌋₊ ≤ ini.X.card →
                                      exp (-δ * k) * (k + l).choose l ≤ n →
                                        (k : ℝ) * (1 - δ / γ) * (1 + 1 / (exp 1 * (1 - γ)))⁻¹ +
                                            f k ≤
                                          (redSteps γ k l ini).card := by
  sorry


theorem it_keeps_showing_up {γ : ℝ} (hγ : γ ≤ 1) : 0 < 1 + 1 / (exp 1 * (1 - γ)) :=
  add_pos_of_pos_of_nonneg zero_lt_one
    (one_div_nonneg.2 (mul_nonneg (exp_pos _).le (sub_nonneg_of_le hγ)))

theorem rearranging_more {c γ : ℝ} (hγl : 0.1 ≤ γ) (hγu : γ ≤ 0.2) (hc : 0 < c) (hc' : c < 0.95) :
    c < (1 - 1 / (200 * γ)) * (1 + 1 / (exp 1 * (1 - γ)))⁻¹ ↔
      1 / ((1 - 1 / (200 * γ)) / c - 1) / (1 - γ) < exp 1 := by
  sorry


theorem numerics_one_middle_aux {γ : ℝ} (hγu : γ = 1 / 10) :
    0.67435 < (1 - 1 / 20) * (1 + 1 / (exp 1 * (1 - γ)))⁻¹ := by
  sorry


theorem numerics_one_left {γ δ : ℝ} (hγl : 0 < γ) (hγu : γ ≤ 1 / 10) (hδ : δ = γ / 20) :
    0.67435 < (1 - δ / γ) * (1 + 1 / (exp 1 * (1 - γ)))⁻¹ := by
  sorry


theorem ConcaveOn.hMul {f g : ℝ → ℝ} {s : Set ℝ} (hf : ConcaveOn ℝ s f) (hg : ConcaveOn ℝ s g)
    (hf' : MonotoneOn f s) (hg' : AntitoneOn g s) (hf'' : ∀ x ∈ s, 0 ≤ f x)
    (hg'' : ∀ x ∈ s, 0 ≤ g x) : ConcaveOn ℝ s fun x => f x * g x := by
  sorry


-- lemma convex_on_sub_const {s : set ℝ} {c : ℝ} (hs : convex ℝ s) : concave_on ℝ s (λ x, x - c) :=
-- (convex_on_id hs).sub (concave_on_const _ hs)
theorem ConvexOn.const_hMul {c : ℝ} {s : Set ℝ} {f : ℝ → ℝ} (hf : ConvexOn ℝ s f) (hc : 0 ≤ c) :
    ConvexOn ℝ s fun x => c * f x :=
  ⟨hf.1, fun x hx y hy a b ha hb hab =>
    (mul_le_mul_of_nonneg_left (hf.2 hx hy ha hb hab) hc).trans_eq
      (by simp only [smul_eq_mul]; ring_nf)⟩

theorem ConcaveOn.const_hMul {c : ℝ} {s : Set ℝ} {f : ℝ → ℝ} (hf : ConcaveOn ℝ s f) (hc : 0 ≤ c) :
    ConcaveOn ℝ s fun x => c * f x :=
  ⟨hf.1, fun x hx y hy a b ha hb hab =>
    (mul_le_mul_of_nonneg_left (hf.2 hx hy ha hb hab) hc).trans_eq'
      (by simp only [smul_eq_mul]; ring_nf)⟩

theorem StrictConvexOn.const_hMul_neg {c : ℝ} {s : Set ℝ} {f : ℝ → ℝ} (hf : StrictConvexOn ℝ s f)
    (hc : c < 0) : StrictConcaveOn ℝ s fun x => c * f x :=
  ⟨hf.1, fun x hx y hy hxy a b ha hb hab =>
    (mul_lt_mul_of_neg_left (hf.2 hx hy hxy ha hb hab) hc).trans_eq'
      (by simp only [smul_eq_mul]; ring_nf)⟩

theorem StrictConvexOn.const_hMul {c : ℝ} {s : Set ℝ} {f : ℝ → ℝ} (hf : StrictConvexOn ℝ s f)
    (hc : 0 < c) : StrictConvexOn ℝ s fun x => c * f x :=
  ⟨hf.1, fun x hx y hy hxy a b ha hb hab =>
    (mul_lt_mul_of_pos_left (hf.2 hx hy hxy ha hb hab) hc).trans_eq
      (by simp only [smul_eq_mul]; ring_nf)⟩

theorem convexOn_inv : ConvexOn ℝ (Set.Ioi (0 : ℝ)) fun x => x⁻¹ := by
  sorry

theorem convexOn_one_div : ConvexOn ℝ (Set.Ioi (0 : ℝ)) fun x => 1 / x := by
  sorry

theorem quadratic_is_concave {a b c : ℝ} (ha : 0 < a) :
    StrictConvexOn ℝ Set.univ fun x => a * x ^ 2 + b * x + c := by
  sorry


theorem rearranging {c γ : ℝ} (hγ₀ : 0 < γ) (hγu : γ ≤ 0.2) :
    c < (1 - 1 / (200 * γ)) * (1 + 1 / (exp 1 * (1 - γ)))⁻¹ ↔
      (1 - c) * γ ^ 2 + (c * (1 + 1 / exp 1) - (1 + 1 / 200)) * γ + 1 / 200 < 0 := by
  sorry


-- lhs is 39/40 * (1 + 5 / (4 e))
theorem numerics_one {γ δ : ℝ} (hγl : 0 < γ) (hγu : γ ≤ 1 / 5) (hδ : δ = min (1 / 200) (γ / 20)) :
    0.6678 < (1 - δ / γ) * (1 + 1 / (exp 1 * (1 - γ)))⁻¹ := by
  sorry


theorem nine_three (γ₀ : ℝ) (hγ₀ : 0 < γ₀) :
    ∀ᶠ l : ℕ in atTop,
      ∀ k : ℕ,
        l ≤ k →
          ∀ γ : ℝ,
            γ = l / (k + l) →
              γ₀ ≤ γ →
                γ ≤ 1 / 5 →
                  ∀ δ : ℝ,
                    δ = min (1 / 200) (γ / 20) →
                      ∀ n : ℕ,
                        ∀ χ : TopEdgeLabelling (Fin n) (Fin 2),
                          (¬∃ (m : Finset (Fin n)) (c : Fin 2),
                                χ.MonochromaticOf m c ∧ ![k, l] c ≤ m.card) →
                            ∀ ini : BookConfig χ,
                              1 / 4 ≤ ini.p →
                                ⌊(n / 2 : ℝ)⌋₊ ≤ ini.X.card →
                                  exp (-δ * k) * (k + l).choose l ≤ n →
                                    (2 / 3 : ℝ) * k ≤ (redSteps γ k l ini).card := by
  sorry


theorem yael_two {n k a : ℕ} : n.ascFactorial (k + a) = (n + a).ascFactorial k * n.ascFactorial a := by
  rw [Nat.add_comm k a, ← Nat.ascFactorial_mul_ascFactorial, mul_comm]


theorem asc_hMul_asc {a b c : ℕ} :
    a.ascFactorial b * (a + b).ascFactorial c = a.ascFactorial c * (a + c).ascFactorial b := by
  rw [Nat.ascFactorial_mul_ascFactorial, Nat.ascFactorial_mul_ascFactorial, Nat.add_comm b c]


theorem asc_div_asc_const_right' {a b c : ℕ} :
    (a.ascFactorial b : ℝ) / (a + c).ascFactorial b = a.ascFactorial c / (a + b).ascFactorial c := by
  sorry


theorem asc_div_asc_const_right {a b c : ℕ} :
    ((a + c).ascFactorial b : ℝ) / a.ascFactorial b = (a + b).ascFactorial c / a.ascFactorial c := by
  sorry


-- d = a + c
-- a = d - c
theorem asc_div_asc_const_right_sub' {b c d : ℕ} (h : c ≤ d) :
    ((d - c).ascFactorial b : ℝ) / d.ascFactorial b =
      (d - c).ascFactorial c / (d - c + b).ascFactorial c := by
  sorry


theorem choose_ratio {l k t : ℕ} (h : t ≤ k) :
    ((k + l - t).choose l : ℝ) / (k + l).choose l = ∏ i ∈ Finset.range t, (k - i) / (k + l - i) := by
  sorry


theorem fact_d_two_part_one {l k t : ℕ} (h : t ≤ k) :
    ((k + l - t).choose l : ℝ) / (k + l).choose l =
      (k / (k + l)) ^ t * ∏ i ∈ Finset.range t, (1 - i * l / (k * (k + l - i))) := by
  sorry


theorem fact_d_two_part_two {l k t : ℕ} (h : t ≤ k) :
    ∏ i ∈ Finset.range t, (1 - i * l / (k * (k + l - i)) : ℝ) ≤
      exp (-l / (k * (k + l)) * ∑ i ∈ Finset.range t, i) := by
  sorry


theorem d_two {l k t : ℕ} {γ : ℝ} (ht : 0 < k) (h : t ≤ k) (hγ : γ = l / (k + l)) :
    ((k + l - t).choose l : ℝ) ≤
      exp (-γ * (t * (t - 1)) / (2 * k)) * (1 - γ) ^ t * (k + l).choose l := by
  sorry


theorem nine_six :
    ∀ (l k t : ℕ) (γ : ℝ),
      0 < k →
        t ≤ k →
          γ = l / (k + l) →
            exp (-1) * (1 - γ) ^ (-t : ℝ) * exp (γ * t ^ 2 / (2 * k)) * (k + l - t).choose l ≤
              (k + l).choose l := by
  sorry


theorem nine_five_density :
    ∃ f : ℕ → ℝ,
      (f =o[atTop] fun i => (i : ℝ)) ∧
        ∀ γ₀ : ℝ,
          0 < γ₀ →
            ∀ᶠ l : ℕ in atTop,
              ∀ k : ℕ,
                ∀ γ η : ℝ,
                  γ₀ ≤ γ →
                    0 ≤ η →
                      1 / 2 ≤ 1 - γ - η →
                        ∀ n : ℕ,
                          ∀ χ : TopEdgeLabelling (Fin n) (Fin 2),
                            (¬∃ (m : Finset (Fin n)) (c : Fin 2),
                                  χ.MonochromaticOf m c ∧ ![k, l] c ≤ m.card) →
                              ∀ ini : BookConfig χ,
                                1 - γ - η ≤ ini.p →
                                  γ ≤ 1 / 2 →
                                    γ < 1 →
                                      l ≤ k →
                                        1 / 2 ≤ ini.p →
                                          exp (f k) *
                                                (1 - γ - η) ^
                                                  (γ * (redSteps γ k l ini).card / (1 - γ)) *
                                              (1 - γ - η) ^ (redSteps γ k l ini).card ≤
                                            ini.p ^
                                              ((redSteps γ k l ini).card +
                                                (densitySteps γ k l ini).card) := by
  sorry


theorem nine_five :
    ∃ f : ℕ → ℝ,
      (f =o[atTop] fun i => (i : ℝ)) ∧
        ∀ γ₀ : ℝ,
          0 < γ₀ →
            ∀ᶠ l : ℕ in atTop,
              ∀ k : ℕ,
                l ≤ k →
                  ∀ γ δ η : ℝ,
                    γ = l / (k + l) →
                      γ₀ ≤ γ →
                        0 ≤ δ →
                          δ ≤ γ / 20 →
                            0 ≤ η →
                              1 / 2 ≤ 1 - γ - η →
                                ∀ n : ℕ,
                                  ∀ χ : TopEdgeLabelling (Fin n) (Fin 2),
                                    (¬∃ (m : Finset (Fin n)) (c : Fin 2),
                                          χ.MonochromaticOf m c ∧ ![k, l] c ≤ m.card) →
                                      ∀ ini : BookConfig χ,
                                        1 - γ - η ≤ ini.p →
                                          ⌊(n / 2 : ℝ)⌋₊ ≤ ini.Y.card →
                                            exp (-δ * k) * (k + l).choose l ≤ n →
                                              Real.exp (-δ * k + f k) *
                                                        (1 - γ - η) ^
                                                          (γ * (redSteps γ k l ini).card /
                                                            (1 - γ)) *
                                                      ((1 - γ - η) / (1 - γ)) ^
                                                        (redSteps γ k l ini).card *
                                                    exp
                                                      (γ * (redSteps γ k l ini).card ^ 2 /
                                                        (2 * k)) *
                                                  (k - (redSteps γ k l ini).card + l).choose l ≤
                                                (endState γ k l ini).Y.card := by
  sorry


section

variable {V : Type*}

open Fintype

section

/-- The density of a simple graph. -/
def density [Fintype V] (G : SimpleGraph V) [Fintype G.edgeSet] : ℚ :=
  G.edgeFinset.card / (card V).choose 2

theorem density_congr [Fintype V] (G₁ G₂ : SimpleGraph V) [Fintype G₁.edgeSet]
    [Fintype G₂.edgeSet] (h : G₁ = G₂) : G₁.density = G₂.density := by
  sorry

theorem density_eq_average [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [Fintype G.edgeSet] [DecidableRel G.Adj] :
    G.density =
      (((card V * (card V - 1) : ℕ) : ℚ))⁻¹ *
        ∑ x : V, ∑ y ∈ Finset.univ.erase x, if G.Adj x y then 1 else 0 := by
  sorry


/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (x y) -/
theorem density_eq_average' [Fintype V] (G : SimpleGraph V) [Fintype G.edgeSet]
    [DecidableRel G.Adj] :
    G.density =
      (((card V * (card V - 1) : ℕ) : ℚ))⁻¹ * ∑ (x : V) (y : V), if G.Adj x y then 1 else 0 := by
  sorry


theorem density_eq_average_neighbors [Fintype V] (G : SimpleGraph V) [Fintype G.edgeSet]
    [DecidableRel G.Adj] :
    G.density = (((card V * (card V - 1) : ℕ) : ℚ))⁻¹ * ∑ x : V, (G.neighborFinset x).card := by
  sorry


theorem density_compl [Fintype V] (G : SimpleGraph V) [Fintype G.edgeSet]
    [Fintype Gᶜ.edgeSet] (h : 2 ≤ card V) : Gᶜ.density = 1 - G.density := by
  sorry


theorem erase_eq_filter {α : Type*} [DecidableEq α] {s : Finset α} (a : α) :
    s.erase a = s.filter (· ≠ a) := by
  ext x
  simp [and_comm]

variable [Fintype V]

theorem density_eq_average_partition [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    [Fintype G.edgeSet] (n : ℕ) (hn₀ : 0 < n) (hn : n < card V) :
    G.density = ((((card V).choose n : ℕ) : ℚ))⁻¹ *
      ∑ U ∈ (Finset.univ : Finset V).powersetCard n, G.edgeDensity U (Uᶜ) := by
  sorry


theorem exists_density_edgeDensity [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    [Fintype G.edgeSet] (n : ℕ) (hn₀ : 0 < n) (hn : n < card V) :
    ∃ U : Finset V, U.card = n ∧ G.density ≤ G.edgeDensity U (Uᶜ) := by
  sorry


theorem exists_equibipartition_edgeDensity (G : SimpleGraph V) [DecidableRel G.Adj]
    [Fintype G.edgeSet] (hn : 2 ≤ card V) :
    ∃ X Y : Finset V,
      Disjoint X Y ∧
        ⌊(card V / 2 : ℝ)⌋₊ ≤ X.card ∧
          ⌊(card V / 2 : ℝ)⌋₊ ≤ Y.card ∧ G.density ≤ G.edgeDensity X Y := by
  sorry


end

/-- The density of a label in the edge labelling. -/
def TopEdgeLabelling.density [Fintype V] {K : Type*} (χ : TopEdgeLabelling V K) (k : K)
    [Fintype (χ.labelGraph k).edgeSet] : ℝ :=
  SimpleGraph.density (χ.labelGraph k)

theorem exists_equibipartition_col_density {n : ℕ} (χ : TopEdgeLabelling (Fin n) (Fin 2))
    (hn : 2 ≤ n) :
    ∃ ini : BookConfig χ,
      χ.density 0 ≤ ini.p ∧ ⌊(n / 2 : ℝ)⌋₊ ≤ ini.X.card ∧ ⌊(n / 2 : ℝ)⌋₊ ≤ ini.Y.card := by
  sorry


theorem density_zero_one [Fintype V] (χ : TopEdgeLabelling V (Fin 2))
    [Fintype (χ.labelGraph 0).edgeSet] [Fintype (χ.labelGraph 1).edgeSet]
    (h : 2 ≤ card V) : χ.density 0 = 1 - χ.density 1 := by
  sorry


end

theorem nine_two_monotone {γ η : ℝ} (γ' δ' : ℝ) (hγu : γ ≤ γ') (hηγ : δ' ≤ 1 - γ' - η) (hδ : 0 < δ')
    (hγ1 : γ' < 1) (hδ' : δ' ≤ 1) : δ' ^ (1 / (1 - γ')) ≤ (1 - γ - η) ^ (1 / (1 - γ)) := by
  have : δ' ≤ 1 - γ - η := hηγ.trans (by linarith only [hγu])
  refine' (Real.rpow_le_rpow hδ.le this _).trans' _
  · exact div_nonneg (by norm_num1) (by linarith only [hγu, hγ1])
  refine' Real.rpow_le_rpow_of_exponent_ge hδ hδ' _
  exact div_le_div_of_nonneg_left zero_le_one (sub_pos_of_lt hγ1) (by linarith only [hγu])


theorem nine_two_numeric_aux {γ η : ℝ} (hγu : γ ≤ 1 / 10) (hηγ : η ≤ γ / 15) :
    (134 / 150) ^ (10 / 9 : ℝ) ≤ (1 - γ - η) ^ (1 / (1 - γ)) := by
  refine' (nine_two_monotone (1 / 10) (67 / 75) hγu _ _ _ _).trans_eq' _
  · linarith only [hηγ, hγu]
  · norm_num1
  · norm_num1
  · norm_num1
  · norm_num


theorem nine_two_numeric {γ η : ℝ} (hγu : γ ≤ 1 / 10) (hηγ : η ≤ γ / 15) :
    exp (-1 / 3 + 1 / 5) ≤ (1 - γ - η) ^ (1 / (1 - γ)) := by
  refine' (nine_two_numeric_aux hγu hηγ).trans' _
  have : (0 : ℝ) < 134 / 150 := by norm_num1
  rw [← Real.le_log_iff_exp_le (Real.rpow_pos_of_pos this _), Real.log_rpow this, ← div_le_iff₀']
  swap; · positivity
  norm_num1
  rw [neg_le, ← Real.log_inv, inv_div, le_div_iff₀, mul_comm, ← Real.log_rpow, Real.log_le_iff_le_exp, ←
    exp_one_rpow]
  · refine' (Real.rpow_le_rpow (by norm_num1) exp_one_gt_d9.le (by norm_num1)).trans' _
    norm_num
  · exact Real.rpow_pos_of_pos (by norm_num1) _
  · norm_num1
  · norm_num1


theorem nine_two_part_two {k t : ℕ} {γ η : ℝ} (hγl : 0 ≤ γ) (hγu : γ ≤ 1 / 10) (hηγ : η ≤ γ / 15)
    (ht : (2 / 3 : ℝ) * k ≤ t) (hk : 0 < k)
    (h : exp (-1 / 3 + 1 / 5) ≤ (1 - γ - η) ^ (1 / (1 - γ))) :
    exp (6 * γ * t ^ 2 / (20 * k)) ≤ exp (γ * t ^ 2 / (2 * k)) * (1 - γ - η) ^ (γ * t / (1 - γ)) := by
  have : 0 < 1 - γ - η := by linarith only [hγu, hηγ]
  rw [div_eq_mul_one_div _ (1 - γ), mul_comm _ (1 / (1 - γ)), Real.rpow_mul this.le]
  refine'
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (exp_pos _).le h (by positivity))
          (exp_pos _).le).trans'
      _
  rw [← exp_one_rpow (_ + _), ← Real.rpow_mul (exp_pos _).le, exp_one_rpow, ← Real.exp_add, exp_le_exp,
    sq, mul_mul_mul_comm, ← div_mul_eq_mul_div, ← mul_assoc γ, mul_div_assoc (γ * t),
    mul_comm (γ * t), ← add_mul, div_add']
  swap; · positivity
  refine' mul_le_mul_of_nonneg_right _ (by positivity)
  rw [div_le_iff₀, div_mul_eq_mul_div, mul_div_assoc, mul_div_mul_right]
  · linarith
  · positivity
  · positivity


-- lemma nine_two_part_two {k t : ℕ} {γ η : ℝ} (hγl : 0 ≤ γ) (hγu : γ ≤ 1 / 10) (hηγ : η ≤ γ / 15)
--   (ht : (2 / 3 : ℝ) * k ≤ t) (hk : 0 < k)
--   (h : exp (- 1 / 3 + 1 / 5) ≤ (1 - γ - η) ^ (1 / (1 - γ))) :
--   exp ((k : ℝ) * (γ * (2 / 15))) ≤ exp (γ * t ^ 2 / (2 * k)) * (1 - γ - η) ^ (γ * t / (1 - γ)) :=
-- begin
--   have : 0 < 1 - γ - η := by linarith only [hγu, hηγ],
--   rw [div_eq_mul_one_div _ (1 - γ), mul_comm _ (1 / (1 - γ)), rpow_mul this.le],
--   refine (mul_le_mul_of_nonneg_left (rpow_le_rpow (exp_pos _).le h (by positivity))
--     (exp_pos _).le).trans' _,
--   rw [←exp_one_rpow (_ + _), ←rpow_mul (exp_pos _).le, exp_one_rpow, ←real.exp_add, exp_le_exp,
--     sq, ←mul_assoc γ, mul_div_assoc, ←mul_comm (γ * t), ←mul_add],
--   have : (k : ℝ) * (γ * (2 / 15)) ≤ γ * t * (1 / 5),
--   { rw [mul_left_comm, mul_assoc],
--     refine mul_le_mul_of_nonneg_left _ hγl,
--     linarith only [ht] },
--   refine this.trans (mul_le_mul_of_nonneg_left _ (by positivity)),
--   rw [div_add', le_div_iff₀],
--   { linarith only [ht] },
--   { positivity },
--   { positivity },
-- end
theorem nine_two_part_three {η γ : ℝ} (hγl : 0 ≤ η) (hγu : γ ≤ 1 / 10) (hηγ : η ≤ γ / 15) :
    exp (-3 * η / 2) ≤ (1 - γ - η) / (1 - γ) := by
  rw [← one_sub_div, ← div_mul_eq_mul_div]
  swap; · linarith
  have h₂ : -1 / 3 ≤ -3 / 2 * η := by linarith
  refine' (general_convex_thing' (by linarith) h₂ (by norm_num)).trans _
  have : 1 + -10 / 9 * η ≤ 1 - η / (1 - γ) := by
    rw [neg_div, neg_mul, ← sub_eq_add_neg, sub_le_sub_iff_left, div_eq_mul_one_div, mul_comm]
    refine' mul_le_mul_of_nonneg_right _ hγl
    rw [div_le_iff₀] <;> linarith
  refine' this.trans' _
  rw [← mul_assoc, ← div_mul_eq_mul_div, add_le_add_iff_left]
  refine' mul_le_mul_of_nonneg_right _ hγl
  suffices exp (-1 / 3) ≤ 61 / 81 by
    rw [mul_div_assoc, ← le_div_iff₀, sub_le_iff_le_add]
    · exact this.trans_eq (by norm_num1)
    · norm_num1
  refine' le_of_pow_le_pow_left₀ (by norm_num : 3 ≠ 0) (by norm_num1) _
  rw [← exp_nat_mul, Nat.cast_ofNat, mul_div_cancel₀, ← inv_div, inv_pow, Real.exp_neg]
  · refine' inv_anti₀ (by norm_num1) (exp_one_gt_d9.le.trans' (by norm_num1))
  · norm_num1


theorem nine_two_part_four {k t : ℕ} {η γ : ℝ} (hγl : 0 ≤ η) (hγu : γ ≤ 1 / 10) (hηγ : η ≤ γ / 15)
    (ht : (2 / 3 : ℝ) * k ≤ t) (hk : 0 < k) :
    exp (-3 * γ * t ^ 2 / (20 * k)) ≤ ((1 - γ - η) / (1 - γ)) ^ t := by
  refine' (pow_le_pow_left₀ (exp_pos _).le (nine_two_part_three hγl hγu hηγ) _).trans' _
  rw [← exp_nat_mul, exp_le_exp, neg_mul, neg_mul, neg_div, neg_mul, neg_div, mul_neg,
    neg_le_neg_iff, mul_div_assoc, mul_left_comm, ← mul_assoc, sq, mul_mul_mul_comm, mul_div_assoc]
  refine' mul_le_mul_of_nonneg_left _ (by positivity)
  refine' (div_le_div_of_nonneg_right hηγ (by positivity)).trans _
  rw [div_div, div_eq_mul_one_div, mul_div_assoc]
  refine' mul_le_mul_of_nonneg_left _ (by linarith)
  rw [le_div_iff₀, ← mul_assoc]
  · exact ht.trans' (mul_le_mul_of_nonneg_right (by norm_num1) (Nat.cast_nonneg _))
  · positivity


theorem nine_two_part_five {k t : ℕ} {η γ γ₀ δ fk : ℝ} (hη₀ : 0 ≤ η) (hγu : γ ≤ 1 / 10)
    (hηγ : η ≤ γ / 15) (hγ₀' : 0 < γ) (h₂ : 0 ≤ 1 - γ - η) (ht : (2 / 3 : ℝ) * k ≤ t) (hk : 0 < k)
    (hδ : δ = γ / 20) (hγ₀ : γ₀ ≤ γ) (hγ₁ : γ < 1) (hfk : -fk ≤ γ₀ / 60 * k) :
    1 ≤
      exp (-δ * k + fk) * (1 - γ - η) ^ (γ * t / (1 - γ)) * ((1 - γ - η) / (1 - γ)) ^ t *
        exp (γ * t ^ 2 / (2 * ↑k)) := by
  sorry


-- TODO: move
section

variable {V K : Type*} {n : K → ℕ}

theorem ramseyNumber_le_finset_aux {s : Finset V} (C : TopEdgeLabelling V K)
    (h :
      ∃ (m : Finset s) (c : K),
        (C.pullback (Function.Embedding.subtype (· ∈ s))).MonochromaticOf m c ∧ n c ≤ m.card) :
    ∃ (m : Finset V) (c : K), m ⊆ s ∧ C.MonochromaticOf m c ∧ n c ≤ m.card := by
  obtain ⟨m, c, hm, hn⟩ := h
  refine' ⟨_, c, _, hm.map, _⟩
  · intro x hx
    rw [Finset.mem_map] at hx
    obtain ⟨y, _, hy⟩ := hx
    rw [← hy]
    exact y.property
  · simpa [Finset.card_map] using hn


-- there should be a version of this for IsRamseyValid and it should be useful *for* the proof
-- that ramsey numbers exist
theorem ramseyNumber_le_finset [DecidableEq K] [Fintype K] {s : Finset V}
    (h : ramseyNumber n ≤ s.card) (C : TopEdgeLabelling V K) :
  ∃ (m : Finset V) (c : K), m ⊆ s ∧ C.MonochromaticOf m c ∧ n c ≤ m.card := by
  have : ramseyNumber n ≤ Fintype.card s := by rwa [Fintype.card_coe]
  rw [ramseyNumber_le_iff, isRamseyValid_iff_eq] at this
  refine' ramseyNumber_le_finset_aux C _
  obtain ⟨m, c, hm, hcard⟩ := this (C.pullback (Function.Embedding.subtype (· ∈ s)))
  exact ⟨m, c, hm, hcard.le⟩


theorem ramseyNumber_le_choose' {i j : ℕ} : ramseyNumber ![i, j] ≤ (i + j).choose i :=
  ((ramseyNumber.mono_two (Nat.le_succ _) (Nat.le_succ _)).trans
        (ramseyNumber_le_choose (i + 1) (j + 1))).trans
    (by simp only [Nat.succ_sub_succ_eq_sub, Nat.sub_zero, Nat.add_succ, Nat.succ_add_sub_one]; exact le_rfl)

end

theorem nine_two (γ₀ : ℝ) (hγ₀ : 0 < γ₀) :
    ∀ᶠ l : ℕ in atTop,
      ∀ k : ℕ,
        ∀ γ δ η : ℝ,
          γ = l / (k + l) →
            γ₀ ≤ γ →
              γ ≤ 1 / 10 →
                δ = γ / 20 →
                  0 ≤ η →
                    η ≤ γ / 15 →
                      ∀ n : ℕ,
                        ∀ χ : TopEdgeLabelling (Fin n) (Fin 2),
                          1 - γ - η ≤ χ.density 0 →
                            exp (-δ * k) * (k + l).choose l ≤ n →
                              ∃ (m : Finset (Fin n)) (c : Fin 2),
                                χ.MonochromaticOf m c ∧ ![k, l] c ≤ m.card := by
  sorry


theorem nine_two_variant (γ₀ : ℝ) (hγ₀ : 0 < γ₀) :
    ∀ᶠ l : ℕ in atTop,
      ∀ k : ℕ,
        ∀ γ δ η : ℝ,
          γ = l / (k + l) →
            γ₀ ≤ γ →
              γ ≤ 1 / 10 →
                δ = γ / 20 →
                  0 ≤ η →
                    η ≤ γ / 15 →
                      ∀ V : Type*,
                        [DecidableEq V] →
                          [Fintype V] →
                            ∀ χ : TopEdgeLabelling V (Fin 2),
                              1 - γ - η ≤ χ.density 0 →
                                exp (-δ * k) * (k + l).choose l ≤ Fintype.card V →
                                  ∃ (m : Finset V) (c : Fin 2),
                                    χ.MonochromaticOf m c ∧ ![k, l] c ≤ m.card := by
  sorry


theorem nine_one_part_one {m : ℝ} (hm : 1 < m) : (⌈(m / exp 1 : ℝ)⌉₊ : ℝ) < m := by
  have : 1 / 2 < m / 2 := div_lt_div_of_pos_right hm two_pos
  refine' ((ceil_lt_two_mul this).trans_le' _).trans_eq _
  · refine' Nat.cast_le.2 (Nat.ceil_mono _)
    exact div_le_div_of_nonneg_left (by linarith) two_pos (exp_one_gt_d9.le.trans' (by norm_num1))
  exact mul_div_cancel₀ _ two_ne_zero


theorem gamma'_le_gamma_iff {k l m : ℕ} (h : m ≤ l) (h' : 0 < k) :
    (l - m : ℝ) / (k + l - m) < (l / (k + l)) ^ 2 ↔ (l * (k + l) : ℝ) / (k + 2 * l) < m := by
  have :
      (l : ℝ) * l * (k + l - m) - (l - m) * ((k + l) * (k + l)) =
        k * (m * (k + 2 * l) - l * (k + l)) := by
    ring_nf
  rw [div_pow, div_lt_iff₀, div_lt_iff₀, div_mul_eq_mul_div, lt_div_iff₀, ← sub_pos, sq, sq, this,
    mul_pos_iff, or_iff_left, and_iff_right, sub_pos]
  · rwa [Nat.cast_pos]
  · simp only [not_and', not_lt, Nat.cast_nonneg, imp_true_iff]
  · positivity
  · positivity
  rw [add_sub_assoc, ← Nat.cast_sub h]
  positivity


theorem gamma_hMul_k_le_m_of {k l m : ℕ} (h : m ≤ l) (h' : 0 < k)
    (hg : (l - m : ℝ) / (k + l - m) < (l / (k + l)) ^ 2) : (l / (k + l) : ℝ) * k ≤ m := by
  rw [gamma'_le_gamma_iff h h'] at hg
  refine' hg.le.trans' _
  rw [div_mul_eq_mul_div, div_le_div_iff₀, ← sub_nonneg]
  · ring_nf
    positivity
  · positivity
  · positivity


/-- Part of the right hand side of (50) -/
noncomputable def uLowerBoundRatio (ξ : ℝ) (k l m : ℕ) : ℝ :=
  (1 + ξ) ^ m * ∏ i ∈ Finset.range m, ((l - i : ℕ) : ℝ) / ((k + l - i : ℕ) : ℝ)

theorem uLowerBoundRatio_eq {ξ : ℝ} (k l m : ℕ) :
    uLowerBoundRatio ξ k l m =
      ∏ i ∈ Finset.range m, (1 + ξ) * (((l - i : ℕ) : ℝ) / ((k + l - i : ℕ) : ℝ)) := by
  rw [uLowerBoundRatio, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]


theorem uLowerBoundRatio_of_l_lt_m {ξ : ℝ} {k l m : ℕ} (h : l < m) : uLowerBoundRatio ξ k l m = 0 := by
  rw [uLowerBoundRatio, Finset.prod_eq_zero (Finset.mem_range.2 h), MulZeroClass.mul_zero]
  rw [Nat.sub_self, Nat.cast_zero, zero_div]


theorem uLowerBoundRatio_nonneg {ξ : ℝ} {k l m : ℕ} (hξ : 0 ≤ ξ) : 0 ≤ uLowerBoundRatio ξ k l m := by
  rcases lt_or_ge l m with h | h
  · rw [uLowerBoundRatio_of_l_lt_m h]
  rw [uLowerBoundRatio_eq]
  refine' Finset.prod_nonneg fun i hi => _
  exact mul_nonneg (by linarith only [hξ])
    (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))


theorem uLowerBoundRatio_pos {ξ : ℝ} {k l m : ℕ} (hξ : 0 ≤ ξ) (h : m ≤ l) :
    0 < uLowerBoundRatio ξ k l m := by
  rw [uLowerBoundRatio_eq]
  refine' Finset.prod_pos fun i hi => _
  rw [Finset.mem_range] at hi
  have hnum : (0 : ℝ) < (l - i : ℕ) := by
    exact_mod_cast Nat.sub_pos_of_lt (hi.trans_le h)
  have hden : (0 : ℝ) < (k + l - i : ℕ) := by
    exact_mod_cast Nat.sub_pos_of_lt ((hi.trans_le h).trans_le (Nat.le_add_left l k))
  positivity


theorem U_lower_bound_decreasing {ξ : ℝ} (k l : ℕ) (hξ : 0 ≤ ξ) (hξ' : ξ ≤ 1) (hlk : l ≤ k)
    (hk : 0 < k) : Antitone (uLowerBoundRatio ξ k l) := by
  sorry


theorem xi_numeric : exp (1 / 20) < 1 + 1 / 16 := by
  refine' lt_of_pow_lt_pow_left₀ 20 (by positivity : (0 : ℝ) ≤ 1 + 1 / 16) _
  rw [← exp_nat_mul]
  refine' (exp_one_lt_d9.trans_eq' (by norm_num)).trans_le _
  norm_num


theorem uLowerBoundRatio_lower_bound_aux_aux {k l m n : ℕ} {γ δ : ℝ} (hml : m ≤ l) (hk₀ : 0 < k)
    (hγ : γ = l / (k + l)) (hδ : δ = γ / 20) (hg : (l - m : ℝ) / (k + l - m) < (l / (k + l)) ^ 2)
    (hn : exp (-δ * k) * (k + l).choose l ≤ n) :
    ((k + l - m).choose k : ℝ) ≤ n * uLowerBoundRatio (1 / 16) k l m := by
  sorry


theorem uLowerBoundRatio_lower_bound_aux {k l m n : ℕ} {γ δ : ℝ} (hml : m < l) (hk₀ : 0 < k)
    (hγ : γ = l / (k + l)) (hδ : δ = γ / 20) (hg : (l - m : ℝ) / (k + l - m) < (l / (k + l)) ^ 2)
    (hn : exp (-δ * k) * (k + l).choose l ≤ n) : (k : ℝ) ≤ n * uLowerBoundRatio (1 / 16) k l m := by
  sorry


theorem uLowerBoundRatio_lower_bound' {k l m n : ℕ} {γ δ : ℝ} (hml : m < l) (hk₀ : 0 < k)
    (hlk : l ≤ k) (hγ : γ = l / (k + l)) (hδ : δ = γ / 20)
    (hn : exp (-δ * k) * (k + l).choose l ≤ n) (h : (k : ℝ) < (l - 2) * l) :
    (k : ℝ) ≤ n * uLowerBoundRatio (1 / 16) k l m := by
  sorry


theorem small_k {k l : ℕ} {γ γ₀ : ℝ} (hγ₀ : 0 < γ₀) (hγl : γ₀ ≤ γ) (hγ : γ = l / (k + l))
    (hk₀ : 0 < k) : (k : ℝ) ≤ l * (γ₀⁻¹ - 1) := by
  subst γ
  rwa [le_div_iff₀, ← le_div_iff₀' hγ₀, ← le_sub_iff_add_le, div_eq_mul_inv, ← mul_sub_one] at hγl
  positivity


/-- Cliques which are useful for section 9 and 10 -/
def IsGoodClique {n : ℕ} (ξ : ℝ) (k l : ℕ) (χ : TopEdgeLabelling (Fin n) (Fin 2))
    (x : Finset (Fin n)) : Prop :=
  χ.MonochromaticOf x 1 ∧ (n : ℝ) * uLowerBoundRatio ξ k l x.card ≤ (commonBlues χ x).card

theorem empty_is_good {n k l : ℕ} {ξ : ℝ} {χ : TopEdgeLabelling (Fin n) (Fin 2)} :
    IsGoodClique ξ k l χ ∅ := by
  constructor
  · simp
  rw [uLowerBoundRatio_eq]
  simp
  rw [commonBlues]
  simp


theorem good_clique_bound {n k l ξ} {χ : TopEdgeLabelling (Fin n) (Fin 2)} {x : Finset (Fin n)}
    (hχ : ¬∃ (m : Finset (Fin n)) (c : Fin 2), χ.MonochromaticOf (↑m) c ∧ ![k, l] c ≤ m.card)
    (hx : IsGoodClique ξ k l χ x) : x.card < l := by
  by_contra h
  rw [not_lt] at h
  exact hχ ⟨x, 1, hx.1, by simpa using h⟩


theorem commonBlues_insert {V : Type*} [Fintype V] [DecidableEq V] {x : Finset V} {i : V}
    {χ : TopEdgeLabelling V (Fin 2)} :
    commonBlues χ (insert i x) = (blue_neighbors χ) i ∩ commonBlues χ x := by
  ext v
  simp [commonBlues]


theorem maximally_good_clique_aux {V : Type*} [DecidableEq V] [Fintype V]
    {χ : TopEdgeLabelling V (Fin 2)} {U : Finset V} :
    (χ.pullback (Function.Embedding.subtype (· ∈ U))).density 1 =
      (((U.card * (U.card - 1) : ℕ) : ℝ))⁻¹ * ∑ v ∈ U, ((blue_neighbors χ) v ∩ U).card := by
  sorry


theorem big_U {U : ℕ} (hU : 256 ≤ U) : (U : ℝ) / (U - 1) * (1 + 1 / 16) ≤ 1 + 1 / 15 := by
  have : (256 : ℝ) ≤ U := (Nat.cast_le.2 hU).trans_eq' (by norm_num1)
  rw [div_mul_eq_mul_div, div_le_iff₀] <;> linarith


-- here
theorem maximally_good_clique {n k l : ℕ} {ξ ξ' : ℝ} {χ : TopEdgeLabelling (Fin n) (Fin 2)}
    (hξ : 0 ≤ ξ)
    (hχ : ¬∃ (m : Finset (Fin n)) (c : Fin 2), χ.MonochromaticOf (↑m) c ∧ ![k, l] c ≤ m.card)
    {x : Finset (Fin n)}
    (hU : ((commonBlues χ x).card : ℝ) / ((commonBlues χ x).card - 1) * (1 + ξ) ≤ 1 + ξ')
    (hU' : 2 ≤ (commonBlues χ x).card) (hx : IsGoodClique ξ k l χ x)
    (h : ∀ i : Fin n, i ∉ x → IsGoodClique ξ k l χ (insert i x) → False) :
    1 - (1 + ξ') * ((l - x.card : ℝ) / (k + l - x.card)) ≤
      (χ.pullback (Function.Embedding.subtype (· ∈ commonBlues χ x))).density 0 := by
  sorry


theorem nine_one_end {k l n : ℕ} {ξ : ℝ} {χ : TopEdgeLabelling (Fin n) (Fin 2)} {x : Finset (Fin n)}
    (hχ : ¬∃ (m : Finset (Fin n)) (c : Fin 2), χ.MonochromaticOf (↑m) c ∧ ![k, l] c ≤ m.card)
    (hx : IsGoodClique ξ k l χ x)
    (h :
      ∃ (m : Finset (Fin n)) (c : Fin 2),
        m ⊆ commonBlues χ x ∧ χ.MonochromaticOf (↑m) c ∧ ![k, l - x.card] c ≤ m.card) :
    False := by
  sorry


theorem nine_one_part_two {k l n : ℕ} {γ δ : ℝ} {χ : TopEdgeLabelling (Fin n) (Fin 2)}
    {x : Finset (Fin n)}
    (hχ : ¬∃ (m : Finset (Fin n)) (c : Fin 2), χ.MonochromaticOf (↑m) c ∧ ![k, l] c ≤ m.card)
    (hml : x.card < l) (hl₀ : 0 < l) (hlk : l ≤ k) (hγ : γ = l / (k + l)) (hδ : δ = γ / 20)
    (hm : exp (-δ * k) * (k + l).choose l ≤ n) (hx : IsGoodClique (1 / 16) k l χ x)
    (hγ' : (l - x.card : ℝ) / (k + l - x.card) < (l / (k + l)) ^ 2) : False := by
  sorry


theorem nine_one_part_three {k l m : ℕ} {γ γ' δ : ℝ} (hml : m < l) (hk₀ : 0 < k)
    (hγ : γ = l / (k + l)) (hδ : δ = γ / 20) (hγ' : γ' = (l - m) / (k + l - m))
    (h :
      exp (-δ * k) * (k + l).choose l * uLowerBoundRatio (1 / 16) k l m <
        exp (-(γ' / 20) * k) * ↑((k + (l - m)).choose (l - m))) :
    False := by
  sorry


theorem gamma'_le_gamma {k l m : ℕ} (hk : 0 < k) (h : m ≤ l) :
    (l - m : ℝ) / (k + l - m) ≤ l / (k + l) := by
  rw [div_le_div_iff₀, ← sub_nonneg]
  · ring_nf
    positivity
  · rw [add_sub_assoc, ← Nat.cast_sub h]
    positivity
  · positivity


theorem l_minus_m_big (γ₀ : ℝ) {k l m : ℕ} (hml : m ≤ l) (hl₀ : 0 < l)
    (hkl : (k : ℝ) ≤ l * (γ₀⁻¹ - 1)) (h₁ : 0 < γ₀⁻¹ - 1 + 2) (h₂ : 0 < (γ₀⁻¹ - 1 + 2)⁻¹)
    (hγ' : (m : ℝ) ≤ l * (k + ↑l) / (k + 2 * l)) : ⌈(l : ℝ) * (γ₀⁻¹ - 1 + 2)⁻¹⌉₊ ≤ l - m := by
  sorry


/- ./././Mathport/Syntax/Translate/Basic.lean:641:2: warning: expanding binder collection (i «expr ∉ » x) -/
theorem nine_one_precise (γ₀ : ℝ) (hγ₀ : 0 < γ₀) :
    ∀ᶠ l : ℕ in atTop,
      ∀ k : ℕ,
        ∀ γ δ : ℝ,
          γ = l / (k + l) →
            γ₀ ≤ γ →
              γ ≤ 1 / 10 →
                δ = γ / 20 → (ramseyNumber ![k, l] : ℝ) ≤ exp (-δ * k + 1) * (k + l).choose l := by
  sorry


theorem nine_one_o_filter (γ₀ : ℝ) (hγ₀ : 0 < γ₀) :
    ∃ f : ℕ → ℝ,
      (f =o[atTop] fun i => (i : ℝ)) ∧
        ∀ᶠ l : ℕ in atTop,
          ∀ k : ℕ,
            ∀ γ δ : ℝ,
              γ = l / (k + l) →
                γ₀ ≤ γ →
                  γ ≤ 1 / 10 →
                    δ = γ / 20 →
                      (ramseyNumber ![k, l] : ℝ) ≤ exp (-δ * k + f k) * (k + l).choose l := by
  refine' ⟨fun i => 1, _, nine_one_precise _ hγ₀⟩
  exact (isLittleO_const_id_atTop (1 : ℝ)).comp_tendsto tendsto_natCast_atTop_atTop


theorem nine_one_nine :
    ∀ᶠ l in atTop, ∀ k, k = 9 * l → (ramseyNumber ![k, l] : ℝ) ≤ exp (-l / 25) * (k + l).choose l := by
  filter_upwards [nine_one_precise (1 / 10) (by norm_num1), eventually_ge_atTop 200] with l hl hl'
    k hk
  subst hk
  refine' (hl (9 * l) (1 / 10) (1 / 10 / 20) _ le_rfl le_rfl rfl).trans _
  · rw [Nat.cast_mul, ← add_one_mul, mul_comm, ← div_div, div_self]
    · norm_num1
    · positivity
  refine' mul_le_mul_of_nonneg_right (exp_le_exp.2 _) (Nat.cast_nonneg _)
  have : (200 : ℝ) ≤ l := by exact_mod_cast hl'
  rw [Nat.cast_mul]
  norm_num1
  linarith


end SimpleGraph
