/-
Copyright (c) 2023 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import ExponentialRamsey.Basic
import ExponentialRamsey.Prereq.Constructive
import Mathlib.Algebra.Order.Floor.Semifield

/-!
# Section 4
-/

theorem ConvexOn.hMul {f g : ℝ → ℝ} {s : Set ℝ} (hf : ConvexOn ℝ s f) (hg : ConvexOn ℝ s g)
    (hf' : MonotoneOn f s) (hg' : MonotoneOn g s) (hf'' : ∀ x ∈ s, 0 ≤ f x)
    (hg'' : ∀ x ∈ s, 0 ≤ g x) : ConvexOn ℝ s fun x => f x * g x :=
  hf.mul hg hf'' hg'' (hf'.monovaryOn hg')

theorem MonotoneOn.hMul {s : Set ℝ} {f g : ℝ → ℝ} (hf : MonotoneOn f s) (hg : MonotoneOn g s)
    (hf' : ∀ x ∈ s, 0 ≤ f x) (hg' : ∀ x ∈ s, 0 ≤ g x) : MonotoneOn (fun x => f x * g x) s :=
hf.mul hg hf' hg'

theorem convexOn_sub_const {s : Set ℝ} {c : ℝ} (hs : Convex ℝ s) : ConvexOn ℝ s fun x => x - c :=
  (convexOn_id hs).sub (concaveOn_const _ hs)

theorem Convex.union {s t : Set ℝ} (hs : Convex ℝ s) (ht : Convex ℝ t) (hst : ¬Disjoint s t) :
    Convex ℝ (s ∪ t) := by
  rw [Set.not_disjoint_iff] at hst
  obtain ⟨a, has, hat⟩ := hst
  rw [convex_iff_ordConnected, Set.ordConnected_iff_uIcc_subset]
  rintro x (hx | hx) y (hy | hy)
  · exact (hs.ordConnected.uIcc_subset hx hy).trans Set.subset_union_left
  · exact
      Set.uIcc_subset_uIcc_union_uIcc.trans
        (Set.union_subset_union (hs.ordConnected.uIcc_subset hx has)
          (ht.ordConnected.uIcc_subset hat hy))
  · rw [Set.union_comm]
    exact
      Set.uIcc_subset_uIcc_union_uIcc.trans
        (Set.union_subset_union (ht.ordConnected.uIcc_subset hx hat)
          (hs.ordConnected.uIcc_subset has hy))
  · exact (ht.ordConnected.uIcc_subset hx hy).trans Set.subset_union_right

theorem convexOn_univ_max {k : ℝ} : ConvexOn ℝ Set.univ (max k) := by
  refine' LinearOrder.convexOn_of_lt convex_univ _
  rintro x - y - hxy a b ha hb hab
  simp only [smul_eq_mul]
  refine' max_le _ _
  · refine'
      (add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) ha.le)
            (mul_le_mul_of_nonneg_left (le_max_left _ _) hb.le)).trans_eq'
        _
    rw [← add_mul, hab, one_mul]
  · exact
      add_le_add (mul_le_mul_of_nonneg_left (le_max_right _ _) ha.le)
        (mul_le_mul_of_nonneg_left (le_max_right _ _) hb.le)

theorem ConvexOn.congr' {s : Set ℝ} {f g : ℝ → ℝ} (hf : ConvexOn ℝ s f) (h : s.EqOn f g) :
    ConvexOn ℝ s g := by
  refine' ⟨hf.1, _⟩
  intro x hx y hy a b ha hb hab
  rw [← h (hf.1 hx hy ha hb hab), ← h hx, ← h hy]
  exact hf.2 hx hy ha hb hab

/-- the descending factorial but with a more general setting -/
def descFactorial {α : Type*} [One α] [Mul α] [Sub α] [NatCast α] (x : α) : ℕ → α
  | 0 => 1
  | k + 1 => (x - (k : α)) * descFactorial x k

theorem descFactorial_nonneg {x : ℝ} : ∀ {k : ℕ}, (k : ℝ) - 1 ≤ x → 0 ≤ descFactorial x k
  | 0, h => zero_le_one
  | k + 1, h => mul_nonneg (by grind) (descFactorial_nonneg (h.trans' (by simp)))

theorem descFactorial_nat (n : ℕ) : ∀ k : ℕ, descFactorial n k = n.descFactorial k
  | 0 => rfl
  | k + 1 => by simp [descFactorial, Nat.descFactorial_succ, descFactorial_nat n k]

theorem descFactorial_cast_nat (n : ℕ) : ∀ k : ℕ, descFactorial (n : ℝ) k = n.descFactorial k
  | 0 => by simp [descFactorial]
  | k + 1 => by
    rw [descFactorial, Nat.descFactorial_succ, descFactorial_cast_nat, Nat.cast_mul]
    cases lt_or_ge n k with
    | inl h =>
      rw [Nat.descFactorial_of_lt h, Nat.cast_zero, mul_zero, mul_zero]
    | inr h => rw [Nat.cast_sub h]

theorem descFactorial_monotoneOn :
    ∀ k, MonotoneOn (fun x : ℝ => descFactorial x k) (Set.Ici (k - 1))
  | 0 => by
    simp only [descFactorial]
    exact monotoneOn_const
  | k + 1 => by
    rw [Nat.cast_add_one, add_sub_cancel_right]
    refine' MonotoneOn.hMul _ ((descFactorial_monotoneOn k).mono _) _ _
    · intro x hx y hy hxy
      simpa using hxy
    · rw [Set.Ici_subset_Ici]
      simp
    · intro x hx
      exact sub_nonneg_of_le hx
    intro x hx
    refine' descFactorial_nonneg (hx.trans' _)
    simp

theorem descFactorial_convex :
    ∀ k : ℕ, ConvexOn ℝ (Set.Ici ((k : ℝ) - 1)) fun x => descFactorial x k
  | 0 => convexOn_const 1 (convex_Ici _)
  | k + 1 => by
    rw [Nat.cast_add_one, add_sub_cancel_right]
    change ConvexOn _ _ fun x : ℝ => (x - k) * descFactorial x k
    refine' ConvexOn.hMul _ _ _ _ _ _
    · exact convexOn_sub_const (convex_Ici _)
    · refine' (descFactorial_convex k).subset _ (convex_Ici _)
      rw [Set.Ici_subset_Ici]
      simp
    · intro x hx y hy hxy
      simpa using hxy
    · refine' (descFactorial_monotoneOn _).mono _
      rw [Set.Ici_subset_Ici]
      simp
    · intro x hx
      exact sub_nonneg_of_le hx
    intro x hx
    refine' descFactorial_nonneg (hx.trans' _)
    simp

theorem my_convex {k : ℝ} {f : ℝ → ℝ} (hf : ConvexOn ℝ (Set.Ici k) f)
    (hf' : MonotoneOn f (Set.Ici k)) (hk : ∀ x < k, f x = f k) : ConvexOn ℝ Set.univ f := by
  have : f = f ∘ max k := by grind
  rw [this]
  have : Set.range (max k) = Set.Ici k := by
    ext x
    rw [Set.mem_range, Set.mem_Ici]
    constructor
    · rintro ⟨x, rfl⟩
      exact le_max_left _ _
    intro h
    refine' ⟨x, _⟩
    rw [max_eq_right h]
  refine' ConvexOn.comp _ _ _
  · rwa [Set.image_univ, this]
  · exact convexOn_univ_max
  rwa [Set.image_univ, this]

-- is equal to desc_factorial for all naturals x, and for all x ≥ k - 1
/-- a variant of the descending factorial which truncates at k-1 -/
noncomputable def myDescFactorial (x : ℝ) (k : ℕ) : ℝ :=
  if x < k - 1 then 0 else descFactorial x k

theorem myDescFactorial_eqOn {k : ℕ} :
    (Set.Ici ((k : ℝ) - 1)).EqOn (fun x => myDescFactorial x k) fun x => descFactorial x k := by
  intro x hx
  dsimp
  rw [myDescFactorial, if_neg]
  rwa [not_lt]

theorem myDescFactorial_eq_nat_descFactorial {n k : ℕ} :
    myDescFactorial n k = n.descFactorial k := by
  rw [myDescFactorial, descFactorial_cast_nat, ite_eq_right_iff, eq_comm, Nat.cast_eq_zero,
    Nat.descFactorial_eq_zero_iff_lt]
  intro h
  rw [← @Nat.cast_lt ℝ]
  linarith

theorem myDescFactorial_convexOn_Ici (k : ℕ) :
    ConvexOn ℝ (Set.Ici ((k : ℝ) - 1)) fun x => myDescFactorial x k :=
  (descFactorial_convex _).congr' myDescFactorial_eqOn.symm

theorem myDescFactorial_convex {k : ℕ} (hk : k ≠ 0) :
    ConvexOn ℝ Set.univ fun x => myDescFactorial x k := by
  refine'
    my_convex ((descFactorial_convex _).congr' myDescFactorial_eqOn.symm)
      ((descFactorial_monotoneOn _).congr myDescFactorial_eqOn.symm) _
  intro x hx
  rw [myDescFactorial, if_pos hx, myDescFactorial, if_neg (lt_irrefl _)]
  have h : (k : ℝ) - 1 = (k - 1 : ℕ) := by
    rw [Nat.cast_sub, Nat.cast_one]
    rwa [Nat.succ_le_iff, pos_iff_ne_zero]
  rw [h, descFactorial_cast_nat, eq_comm, Nat.cast_eq_zero, Nat.descFactorial_eq_zero_iff_lt]
  exact Nat.pred_lt hk

/-- a definition of the generalized binomial coefficient -/
noncomputable def myGeneralizedBinomial (x : ℝ) (k : ℕ) : ℝ :=
  (k.factorial : ℝ)⁻¹ • myDescFactorial x k

theorem myGeneralizedBinomial_nat (n k : ℕ) : myGeneralizedBinomial n k = n.choose k := by
  rw [myGeneralizedBinomial, myDescFactorial_eq_nat_descFactorial, smul_eq_mul,
    Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul, inv_mul_cancel_left₀]
  positivity

theorem myGeneralizedBinomial_convex {k : ℕ} (hk : k ≠ 0) :
    ConvexOn ℝ Set.univ fun x => myGeneralizedBinomial x k :=
  (myDescFactorial_convex hk).smul (by positivity)

open scoped BigOperators ExponentialRamsey

theorem my_thing {α : Type*} {s : Finset α} (f : α → ℕ) (b : ℕ) (hb : b ≠ 0) :
    myGeneralizedBinomial ((∑ i ∈ s, f i) / s.card) b * s.card ≤ ∑ i ∈ s, (f i).choose b := by
  cases' eq_or_ne s.card 0 with hs hs
  · simp only [hs, Nat.cast_zero, MulZeroClass.mul_zero]
    exact Nat.cast_nonneg _
  have h₁ : ∑ i ∈ s, (s.card : ℝ)⁻¹ = 1 := by
    rw [Finset.sum_const, nsmul_eq_mul, mul_inv_cancel₀]
    exact_mod_cast hs
  have h₂ : ∀ i ∈ s, (f i : ℝ) ∈ (Set.univ : Set ℝ) := by intro i hi; simp
  have h₃ : ∀ i ∈ s, (0 : ℝ) ≤ (s.card : ℝ)⁻¹ := by
    intro i hi
    positivity
  rw [← le_div_iff₀ (by positivity : (0 : ℝ) < s.card)]
  simpa [div_eq_mul_inv, smul_eq_mul, Finset.sum_mul, Finset.mul_sum, Nat.cast_sum,
    myGeneralizedBinomial_nat, mul_comm, mul_left_comm, mul_assoc] using
    (myGeneralizedBinomial_convex hb).map_sum_le h₃ h₁ h₂

open Real

theorem b_le_sigma_hMul_m {m b : ℕ} {σ : ℝ} (hb : (b : ℝ) ≤ σ * m / 2) (hσ : 0 ≤ σ) :
    (b : ℝ) ≤ σ * m :=
  hb.trans (half_le_self (by positivity))

theorem cast_b_le_cast_m {m b : ℕ} {σ : ℝ} (hb : (b : ℝ) ≤ σ * m / 2) (hσ₀ : 0 ≤ σ) (hσ₁ : σ ≤ 1) :
    (b : ℝ) ≤ m :=
  (b_le_sigma_hMul_m hb hσ₀).trans (mul_le_of_le_one_left (Nat.cast_nonneg _) hσ₁)

theorem b_le_m {m b : ℕ} {σ : ℝ} (hb : (b : ℝ) ≤ σ * m / 2) (hσ₀ : 0 ≤ σ) (hσ₁ : σ ≤ 1) : b ≤ m :=
  Nat.cast_le.1 (cast_b_le_cast_m hb hσ₀ hσ₁)

theorem four_two_aux_aux {m b : ℕ} {σ : ℝ} (hb : (b : ℝ) ≤ σ * m / 2) (hσ : 0 < σ) :
    myGeneralizedBinomial (σ * m) b * (m.choose b : ℝ)⁻¹ =
      descFactorial (σ * m) b / descFactorial (m : ℝ) b := by
  rw [myGeneralizedBinomial, smul_eq_mul, Nat.choose_eq_descFactorial_div_factorial, Nat.cast_div,
    inv_div, ← div_eq_inv_mul, div_mul_div_cancel₀ (by positivity), ← descFactorial_cast_nat]
  · congr 1
    refine' myDescFactorial_eqOn _
    rw [Set.mem_Ici]
    have : (b : ℝ) - 1 ≤ b := by linarith
    exact this.trans (hb.trans (half_le_self (by positivity)))
  · exact Nat.factorial_dvd_descFactorial _ _
  · positivity

theorem four_two_aux {m b : ℕ} {σ : ℝ} :
    descFactorial (σ * m) b / descFactorial (m : ℝ) b =
      ∏ i ∈ Finset.range b, (σ * m - i) / (m - i) := by
  induction' b with b ih
  · simp [descFactorial]
  rw [descFactorial, descFactorial, Finset.prod_range_succ, ← ih, div_mul_div_comm, mul_comm,
    mul_comm (_ - _)]

theorem four_two_aux' {m b : ℕ} {σ : ℝ} (hb : (b : ℝ) ≤ σ * m / 2) (hσ₀ : 0 < σ) (hσ₁ : σ ≤ 1) :
    ∏ i ∈ Finset.range b, (σ * m - i) / (m - i) =
      σ ^ b * ∏ i ∈ Finset.range b, (1 - (1 - σ) * i / (σ * (m - i))) := by
  rw [Finset.pow_eq_prod_const, ← Finset.prod_mul_distrib]
  refine' Finset.prod_congr rfl _
  intro i hi
  rw [mul_one_sub, mul_div_assoc', mul_div_mul_left _ _ hσ₀.ne', sub_div']
  · ring_nf
  rw [Finset.mem_range] at hi
  have hb' : 0 < b := pos_of_gt hi
  have : (i : ℝ) < b := by rwa [Nat.cast_lt]
  suffices (i : ℝ) < m by linarith only [this]
  refine' (this.trans_le hb).trans_le ((half_le_self (by positivity)).trans _)
  exact mul_le_of_le_one_left (Nat.cast_nonneg _) hσ₁

theorem four_two_aux'' {m b i : ℕ} {σ : ℝ} (hb : (b : ℝ) ≤ σ * m / 2) (hσ₀ : 0 ≤ σ) (hσ₁ : σ ≤ 1)
    (hi : i ∈ Finset.range b) : (1 : ℝ) - i / (σ * m) ≤ 1 - (1 - σ) * i / (σ * (m - i)) := by
  rw [Finset.mem_range] at hi
  have : (i : ℝ) < m := by
    rw [Nat.cast_lt]
    refine' hi.trans_le (b_le_m hb hσ₀ hσ₁)
  rw [sub_le_sub_iff_left, mul_comm σ, ← div_mul_div_comm, ← div_div,
    div_eq_mul_one_div (i / σ : ℝ), mul_comm]
  refine' mul_le_mul_of_nonneg_left _ (by positivity)
  have hmpos : (0 : ℝ) < m := this.trans_le' (Nat.cast_nonneg _)
  have hden : 0 < (m : ℝ) - i := by rwa [sub_pos]
  have hiσ : (i : ℝ) ≤ σ * m := by
    have hib : (i : ℝ) ≤ b := by exact_mod_cast hi.le
    nlinarith [hib, hb]
  rw [div_le_iff₀ hden, one_div, inv_mul_eq_div, le_div_iff₀ hmpos]
  linarith

theorem exp_thing {x : ℝ} (hx₀ : 0 ≤ x) (hx₁ : x ≤ 1 / 2) : Real.exp (-2 * x) ≤ 1 - x := by
  let a := 2 * x
  have ha : 0 ≤ a := mul_nonneg (by norm_num1) hx₀
  have ha' : 0 ≤ 1 - a := by
    simp only [a]
    linarith only [hx₁]
  have := convexOn_exp.2 (Set.mem_univ (-1)) (Set.mem_univ 0) ha ha' (by simp)
  simp only [smul_eq_mul, mul_neg, ← neg_mul, mul_one, MulZeroClass.mul_zero, add_zero,
    Real.exp_zero, a] at this
  refine' this.trans _
  rw [add_comm, sub_add, sub_le_sub_iff_left, ← mul_one_sub, mul_right_comm]
  refine' le_mul_of_one_le_left hx₀ _
  have hexp : Real.exp (-1) ≤ 1 / 2 := by
    rw [Real.exp_neg]
    simpa [one_div] using
      one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2)
        (exp_one_gt_d9.le.trans' (by norm_num))
  linarith

theorem four_two_aux''' {m b i : ℕ} {σ : ℝ} (hb : (b : ℝ) ≤ σ * m / 2) (hσ₀ : 0 ≤ σ)
    (hi : i ∈ Finset.range b) : Real.exp (-2 / (σ * m) * i) ≤ (1 : ℝ) - i / (σ * m) := by
  rw [div_mul_comm, mul_comm]
  refine' exp_thing (by positivity) _
  rw [Finset.mem_range] at hi
  have hbpos : (0 : ℝ) < b := by exact_mod_cast pos_of_gt hi
  have hden : 0 < σ * (m : ℝ) := by nlinarith [hbpos, hb]
  have hib : (i : ℝ) ≤ b := by exact_mod_cast hi.le
  rw [div_le_iff₀ hden]
  nlinarith

theorem four_two_aux'''' {m b : ℕ} {σ : ℝ} (hb : (b : ℝ) ≤ σ * m / 2) (hσ₀ : 0 ≤ σ) (hσ₁ : σ ≤ 1) :
    Real.exp (-2 / (σ * m) * ∑ i ∈ Finset.range b, i) ≤
      ∏ i ∈ Finset.range b, (1 - (1 - σ) * i / (σ * (m - i))) := by
  rw [Nat.cast_sum, Finset.mul_sum, Real.exp_sum]
  refine' Finset.prod_le_prod _ _
  · intro i hi
    positivity
  intro i hi
  exact (four_two_aux''' hb hσ₀ hi).trans (four_two_aux'' hb hσ₀ hσ₁ hi)

-- Fact 4.2
theorem four_two_left {m b : ℕ} {σ : ℝ} (hb : (b : ℝ) ≤ σ * m / 2) (hσ₀ : 0 < σ) (hσ₁ : σ ≤ 1) :
    σ ^ b * m.choose b * exp (-b ^ 2 / (σ * m)) ≤ myGeneralizedBinomial (σ * m) b := by
  have : 0 < (m.choose b : ℝ) := by
    rw [Nat.cast_pos]
    exact Nat.choose_pos (b_le_m hb hσ₀.le hσ₁)
  rw [mul_right_comm, ← le_div_iff₀ this, div_eq_mul_inv (myGeneralizedBinomial _ _),
    four_two_aux_aux hb hσ₀, four_two_aux, four_two_aux' hb hσ₀ hσ₁]
  refine' mul_le_mul_of_nonneg_left ((four_two_aux'''' hb hσ₀.le hσ₁).trans' _) (by positivity)
  rw [exp_le_exp, Finset.sum_range_id, ← Nat.choose_two_right, Nat.cast_choose_two,
    div_mul_eq_mul_div]
  refine' div_le_div_of_nonneg_right _ (by positivity)
  nlinarith [(0 : ℝ) ≤ b]

open Filter Finset Real

namespace SimpleGraph

variable {V : Type*} [DecidableEq V] {χ : TopEdgeLabelling V (Fin 2)}

theorem four_one_part_one [Fintype V] (μ : ℝ) (l k : ℕ) (C : BookConfig χ)
    (hC : ramseyNumber ![k, ⌈(l : ℝ) ^ (2 / 3 : ℝ)⌉₊] ≤ C.numBigBlues μ)
    (hR : ¬∃ m : Finset V, χ.MonochromaticOf m 0 ∧ k ≤ m.card) :
    ∃ U : Finset V,
      χ.MonochromaticOf U 1 ∧
        U.card = ⌈(l : ℝ) ^ (2 / 3 : ℝ)⌉₊ ∧
          U ⊆ C.X ∧ ∀ x ∈ U, μ * C.X.card ≤ ((blue_neighbors χ) x ∩ C.X).card := by
  let W := C.X.filter fun x => μ * C.X.card ≤ ((blue_neighbors χ) x ∩ C.X).card
  have : ramseyNumber ![k, ⌈(l : ℝ) ^ (2 / 3 : ℝ)⌉₊] ≤ W.card := hC
  rw [← Fintype.card_coe W, ramseyNumber_le_iff, isRamseyValid_iff_eq] at this
  obtain ⟨U, hU⟩ := this (χ.pullback (Function.Embedding.subtype _))
  rw [Fin.exists_fin_two] at hU
  rcases hU with (⟨hU', hU''⟩ | hU)
  · exfalso
    apply hR
    refine ⟨U.map (Function.Embedding.subtype _), hU'.map, ?_⟩
    rw [card_map, ← hU'']
    simp
  refine' ⟨U.map (Function.Embedding.subtype _), hU.1.map, _, _⟩
  · rw [card_map, ← hU.2]
    simp
  constructor
  · intro x hx
    rw [Finset.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact (Finset.mem_filter.mp y.property).1
  · intro x hx
    rw [Finset.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact (Finset.mem_filter.mp y.property).2

theorem colDensity_hMul [Fintype V] {k : Fin 2} {A B : Finset V} :
    colDensity χ k A B * A.card = (∑ x ∈ B, (colNeighbors χ k x ∩ A).card) / B.card := by
  rcases A.eq_empty_or_nonempty with (rfl | hA)
  · rw [colDensity_empty_left]
    simp only [inter_empty, card_empty, Nat.cast_zero, sum_const_zero, zero_div,
      MulZeroClass.mul_zero]
  rw [colDensity_comm, colDensity_eq_sum, div_mul_eq_mul_div, mul_div_mul_right]
  rwa [Nat.cast_ne_zero, ← pos_iff_ne_zero, card_pos]

theorem colDensity_hMul_hMul [Fintype V] {k : Fin 2} {A B : Finset V} :
    colDensity χ k A B * (A.card * B.card) = ∑ x ∈ B, (colNeighbors χ k x ∩ A).card := by
  rcases B.eq_empty_or_nonempty with (rfl | hA)
  · simp [colDensity_empty_right]
  rw [← mul_assoc, colDensity_hMul, div_mul_cancel₀]
  rwa [Nat.cast_ne_zero, ← pos_iff_ne_zero, card_pos]

-- (10)
theorem four_one_part_two [Fintype V] (μ : ℝ) {l : ℕ} {C : BookConfig χ} {U : Finset V} (hl : l ≠ 0)
    (hU : U.card = ⌈(l : ℝ) ^ (2 / 3 : ℝ)⌉₊) (hU' : U ⊆ C.X)
    (hU'' : ∀ x ∈ U, μ * C.X.card ≤ ((blue_neighbors χ) x ∩ C.X).card) :
    (μ * C.X.card - U.card) / (C.X.card - U.card) ≤ (blue_density χ) U (C.X \ U) := by
  rw [colDensity_eq_sum, Finset.card_sdiff_of_subset hU',
    ← Nat.cast_sub (Finset.card_le_card hU'), ← div_div]
  refine' div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  rw [le_div_iff₀]
  have :
      U.card • (μ * C.X.card - U.card) ≤
        ∑ x ∈ U, (((blue_neighbors χ) x ∩ (C.X \ U)).card : ℝ) := by
    rw [← Finset.sum_const]
    refine' sum_le_sum _
    intro x hx
    rw [← Finset.inter_sdiff_assoc, sub_le_iff_le_add, ← Nat.cast_add]
    refine' (hU'' _ hx).trans _
    rw [Nat.cast_le]
    exact card_le_card_sdiff_add_card
  convert this using 1
  · rw [nsmul_eq_mul, mul_comm]
  · rw [Nat.cast_sum]
  rw [hU]
  positivity

-- (10)
omit [DecidableEq V] in
theorem four_one_part_three (μ : ℝ) {k l : ℕ} {C : BookConfig χ} {U : Finset V} (hμ : 0 ≤ μ)
    (hk₆ : 6 ≤ k) (hl : 3 ≤ l) (hU : U.card = ⌈(l : ℝ) ^ (2 / 3 : ℝ)⌉₊)
    (hX : ramseyNumber ![k, ⌈(l : ℝ) ^ (2 / 3 : ℝ)⌉₊] ≤ C.X.card) :
    μ - 2 / k ≤ (μ * C.X.card - U.card) / (C.X.card - U.card) := by
  set m : ℕ := ⌈(l : ℝ) ^ (2 / 3 : ℝ)⌉₊
  have hm₃ : 3 ≤ m := by
    rw [Nat.add_one_le_ceil_iff, Nat.cast_two, div_eq_mul_inv, rpow_mul (Nat.cast_nonneg _), ←
      rpow_lt_rpow_iff, ← rpow_mul, inv_mul_cancel₀ (by norm_num : (3 : ℝ) ≠ 0), rpow_one]
    · norm_cast
      rw [← Nat.succ_le_iff]
      exact (pow_le_pow_left₀ (by norm_num1) hl 2).trans_eq' (by norm_num1)
    · exact Real.rpow_nonneg (Nat.cast_nonneg _) _
    · norm_num1
    · exact Real.rpow_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) _
    · norm_num1
  have hm₂ : 2 ≤ m := hm₃.trans' (by norm_num1)
  have hk₀ : 0 < (k : ℝ) := by
    rw [Nat.cast_pos]
    exact hk₆.trans_lt' (by norm_num1)
  have hk₃ : 3 ≤ k := hk₆.trans' (by norm_num1)
  have := (right_lt_ramseyNumber hk₃ hm₂).trans_le hX
  have : (0 : ℝ) < C.X.card - U.card := by rwa [hU, sub_pos, Nat.cast_lt]
  rw [sub_div' hk₀.ne', div_le_div_iff₀ hk₀ this, sub_mul, sub_mul, mul_sub, mul_sub, hU,
    sub_sub, mul_right_comm, sub_le_sub_iff_left]
  suffices (m : ℝ) * (k / 2 * (1 - μ) + 1) ≤ C.X.card by linarith
  have : (m : ℝ) * (k / 2 * (1 - μ) + 1) ≤ (m : ℝ) * (k / 2 + 1) := by
    refine' mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    have hmul : k / 2 * (1 - μ) ≤ k / 2 := by
      refine' mul_le_of_le_one_right (half_pos hk₀).le _
      rwa [sub_le_self_iff]
    simpa [add_comm] using add_le_add_right hmul 1
  refine' this.trans _
  rw [ramseyNumber_pair_swap] at hX
  replace hX := (mul_sub_two_le_ramseyNumber hm₃).trans hX
  rw [← @Nat.cast_le ℝ] at hX
  refine' hX.trans' _
  rw [Nat.cast_mul, Nat.cast_sub, Nat.cast_two]
  swap
  · exact hk₃.trans' (by norm_num1)
  refine' mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  have hk₆' : (6 : ℝ) ≤ k := by exact_mod_cast hk₆
  linarith only [hk₆']

variable [Fintype V] {k l : ℕ} {C : BookConfig χ} {U : Finset V} {μ₀ : ℝ}

theorem ceil_lt_two_hMul {x : ℝ} (hx : 1 / 2 < x) : (⌈x⌉₊ : ℝ) < 2 * x := by
  cases lt_or_ge x 1
  · have : ⌈x⌉₊ = 1 := by
      rw [Nat.ceil_eq_iff]
      · rw [Nat.sub_self, Nat.cast_zero, Nat.cast_one]
        constructor <;> linarith
      norm_num
    rw [this, Nat.cast_one]
    linarith
  refine' (Nat.ceil_lt_add_one _).trans_le _
  · linarith
  · linarith

theorem ceil_le_two_hMul {x : ℝ} (hx : 1 / 2 ≤ x) : (⌈x⌉₊ : ℝ) ≤ 2 * x := by
  rcases eq_or_lt_of_le hx with (rfl | hx')
  · norm_num
  exact (Nat.ceil_lt_two_mul (by simpa [one_div] using hx')).le

-- l ≥ 4 / μ₀
theorem mu_div_two_le_sigma (hμ₀ : 0 < μ₀) :
    ∀ᶠ l : ℕ in atTop, ∀ k, l ≤ k → ∀ μ : ℝ, μ₀ ≤ μ → ∀ σ : ℝ, μ - 2 / k ≤ σ → μ / 2 ≤ σ := by
  have t : Filter.Tendsto (Nat.cast : ℕ → ℝ) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [t.eventually_ge_atTop (4 / μ₀)] with l hl k hlk μ hμ σ hσ
  have hk : 4 / μ ≤ k := by
    refine' (div_le_div_of_nonneg_left (by norm_num1) hμ₀ hμ).trans (hl.trans _)
    rwa [Nat.cast_le]
  refine' hσ.trans' _
  rw [le_sub_comm, sub_half]
  refine' (div_le_div_of_nonneg_left (by norm_num1) _ hk).trans _
  · exact div_pos (by norm_num1) (hμ₀.trans_le hμ)
  field_simp [(hμ₀.trans_le hμ).ne']
  nlinarith

-- l ≥ 4 / μ₀
-- l ≥ 1 / 16
-- l ≥ (8 / μ₀) ^ 2.4
theorem four_one_part_four (hμ₀ : 0 < μ₀) :
    ∀ᶠ l : ℕ in atTop,
      ∀ k : ℕ,
        l ≤ k →
          ∀ μ : ℝ,
            μ₀ ≤ μ →
              ∀ σ : ℝ,
                μ - 2 / k ≤ σ →
                  (⌈(l : ℝ) ^ (1 / 4 : ℝ)⌉₊ : ℝ) ≤ σ * ⌈(l : ℝ) ^ (2 / 3 : ℝ)⌉₊ / 2 := by
  have t : Filter.Tendsto (Nat.cast : ℕ → ℝ) atTop atTop := tendsto_natCast_atTop_atTop
  have h3 : (0 : ℝ) < 2 / 3 - 1 / 4 := by norm_num1
  have h4 : (0 : ℝ) < 1 / 4 := by norm_num1
  filter_upwards [((tendsto_rpow_atTop h4).comp t).eventually_ge_atTop (1 / 2),
    ((tendsto_rpow_atTop h3).comp t).eventually_ge_atTop (4 * 2 / μ₀), mu_div_two_le_sigma hμ₀,
    Filter.eventually_gt_atTop 0] with l hl hl'' hl' hl₀ k hlk μ hμ σ hσ
  specialize hl' k hlk μ hμ σ hσ
  dsimp at hl hl''
  rw [mul_div_assoc]
  refine' (mul_le_mul_of_nonneg_right hl' (by positivity)).trans' _
  rw [div_mul_div_comm, two_mul]
  refine' (ceil_le_two_hMul hl).trans _
  rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2 + 2), mul_comm μ,
    ← div_le_iff₀ (hμ₀.trans_le hμ)]
  refine' (Nat.le_ceil _).trans' _
  have hmul :
      2 * (l : ℝ) ^ (1 / 4 : ℝ) * (2 + 2) / μ =
        (4 * 2 / μ) * (l : ℝ) ^ (1 / 4 : ℝ) := by ring
  rw [hmul, ← le_div_iff₀ (Real.rpow_pos_of_pos (by exact_mod_cast hl₀) _), ← rpow_sub]
  · exact hl''.trans' (div_le_div_of_nonneg_left (by norm_num1) hμ₀ hμ)
  · rwa [Nat.cast_pos]

/-- the set of vertices which are connected to S by only blue edges -/
def commonBlues (χ : TopEdgeLabelling V (Fin 2)) (S : Finset V) : Finset V :=
  univ.filter fun i => ∀ j ∈ S, i ∈ (blue_neighbors χ) j

theorem monochromaticBetween_commonBlues {S : Finset V} :
    χ.MonochromaticBetween S (commonBlues χ S) 1 := by
  intro x hx y hy h
  simp [commonBlues] at hy
  have := hy x hx
  rw [mem_colNeighbors] at this
  obtain ⟨h, z⟩ := this
  exact z

theorem four_one_part_five (χ : TopEdgeLabelling V (Fin 2)) {b : ℕ} {X U : Finset V} :
    ∑ S ∈ powersetCard b U, ((commonBlues χ S ∩ (X \ U)).card : ℝ) =
      ∑ v ∈ X \ U, ((blue_neighbors χ) v ∩ U).card.choose b := by
  have :
    ∀ S,
      ((commonBlues χ S ∩ (X \ U)).card : ℝ) =
        ∑ v ∈ X \ U, if v ∈ commonBlues χ S then 1 else 0 := by
    intro S
    rw [Finset.sum_boole (R := ℝ) (fun v => v ∈ commonBlues χ S) (X \ U),
      filter_mem_eq_inter, inter_comm]
  simp_rw [this]
  rw [Finset.sum_comm (s := powersetCard b U) (t := X \ U)
      (f := fun S v => if v ∈ commonBlues χ S then (1 : ℝ) else 0),
    Nat.cast_sum]
  change (∑ v ∈ X \ U, (∑ S ∈ powersetCard b U,
      (if v ∈ commonBlues χ S then (1 : ℝ) else 0))) =
    ∑ v ∈ X \ U, (((blue_neighbors χ) v ∩ U).card.choose b : ℝ)
  refine' Finset.sum_congr rfl (fun v hv => ?_)
  rw [Finset.sum_boole (R := ℝ) (fun S => v ∈ commonBlues χ S) (powersetCard b U),
    ← Finset.card_powersetCard]
  congr 2
  ext S
  simp [commonBlues, subset_iff, mem_colNeighbors_comm, and_assoc, and_comm]
  intro _hcard
  constructor
  · rintro ⟨hU, hblue⟩ x hx
    exact ⟨hU hx, hblue x hx⟩
  · intro h
    exact ⟨fun x hx => (h hx).1, fun x hx => (h hx).2⟩

theorem four_one_part_six (χ : TopEdgeLabelling V (Fin 2)) {m b : ℕ} {X U : Finset V} (σ : ℝ)
    (hU : U.card = m) (hb : b ≠ 0) (hσ' : σ = (blue_density χ) U (X \ U)) :
    myGeneralizedBinomial (σ * ↑m) b * (X \ U).card ≤
      ∑ v ∈ X \ U, ((blue_neighbors χ) v ∩ U).card.choose b := by
  refine' (my_thing _ _ hb).trans' _
  rw [← colDensity_hMul, ← hσ', hU]

theorem four_one_part_seven {V : Type*} [DecidableEq V] {m b : ℕ} {X U : Finset V} {μ σ : ℝ}
    (hσ : (b : ℝ) ≤ σ * m / 2) (hσ₀ : 0 < σ) (hσ₁ : σ ≤ 1) (hμ₀ : 0 < μ) (hσ' : μ - 2 / k ≤ σ)
    (hk : 6 ≤ k) (hm : 3 ≤ m) (hkμ : 4 / μ ≤ k) (hUX : U ⊆ X) (hU : U.card = m)
    (hX : ramseyNumber ![k, m] ≤ X.card) :
    μ ^ b * X.card * m.choose b * (3 / 4) * exp (-4 * b / (μ * k) - b ^ 2 / (σ * m)) ≤
      myGeneralizedBinomial (σ * ↑m) b * (X \ U).card := by
  refine' (mul_le_mul_of_nonneg_right (four_two_left hσ hσ₀ hσ₁) (Nat.cast_nonneg _)).trans' _
  have : 4 * m ≤ X.card := by
    refine' hX.trans' _
    refine' (ramseyNumber.mono_two hk le_rfl).trans' _
    rw [ramseyNumber_pair_swap]
    refine' (mul_sub_two_le_ramseyNumber hm).trans_eq' _
    rw [mul_comm]
  have h₁ : 3 / 4 * (X.card : ℝ) ≤ (X \ U).card := by
    have this' : (4 : ℝ) * m ≤ X.card := by exact_mod_cast this
    rw [Finset.card_sdiff_of_subset hUX, Nat.cast_sub (Finset.card_le_card hUX), hU]
    linarith only [this']
  have : μ * (1 - 2 / (μ * k)) ≤ σ := by
    rwa [mul_one_sub, mul_div_assoc', mul_div_mul_left _ _ hμ₀.ne']
  have h₂ : μ * exp (-4 / (μ * k)) ≤ σ := by
    refine' this.trans' (mul_le_mul_of_nonneg_left _ hμ₀.le)
    refine' (exp_thing (by positivity) _).trans_eq' _
    · rw [← div_div, div_le_div_iff₀, one_mul, div_mul_eq_mul_div, two_mul]
      · simpa [show (2 + 2 : ℝ) = 4 by norm_num] using hkμ
      · rw [Nat.cast_pos]
        exact hk.trans_lt' (by norm_num1)
      · norm_num
    · ring_nf
  rw [sub_eq_add_neg, neg_div, Real.exp_add, mul_right_comm _ (Real.exp _), ← mul_assoc]
  refine' mul_le_mul_of_nonneg_right _ (exp_pos _).le
  rw [mul_right_comm _ (m.choose b : ℝ), mul_right_comm, mul_right_comm _ (m.choose b : ℝ)]
  refine' mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
  rw [mul_comm (μ ^ b), mul_right_comm _ (μ ^ b), mul_assoc, mul_comm (σ ^ b),
    mul_comm (X.card : ℝ)]
  refine' mul_le_mul h₁ _ (by positivity) (Nat.cast_nonneg _)
  refine' (pow_le_pow_left₀ (by positivity) h₂ _).trans' _
  rw [mul_pow, ← Real.rpow_natCast (exp _), ← exp_mul, div_mul_eq_mul_div]

theorem four_one_part_eight {μ : ℝ} {m b : ℕ} {U X : Finset V} (hU : U.card = m) (hbm : b ≤ m)
    (h :
      μ ^ b * X.card / 2 * m.choose b ≤
        ∑ S ∈ powersetCard b U, ((commonBlues χ S ∩ (X \ U)).card : ℝ)) :
    ∃ S, S ⊆ U ∧ S.card = b ∧ μ ^ b * X.card / 2 ≤ (commonBlues χ S ∩ (X \ U)).card := by
  have : (Finset.powersetCard b U).Nonempty :=
    Finset.powersetCard_nonempty.2 (by rwa [hU])
  have h' :
    ∑ i ∈ Finset.powersetCard b U, μ ^ b * X.card / 2 ≤ μ ^ b * X.card / 2 * m.choose b := by
    rw [sum_const, Finset.card_powersetCard, hU, nsmul_eq_mul, mul_comm]
  obtain ⟨S, hS, hS'⟩ := exists_le_of_sum_le this (h.trans' h')
  rw [Finset.mem_powersetCard] at hS
  exact ⟨S, hS.1, hS.2, hS'⟩

theorem four_one_part_nine_aux :
    Tendsto (fun l : ℝ => l ^ (-(2 / 3 - 1 / 4 * 2 : ℝ)) + l ^ (-(1 - 1 / 4 : ℝ))) atTop
      (nhds (0 + 0)) := by
  refine' Filter.Tendsto.add _ _
  · refine' tendsto_rpow_neg_atTop _
    norm_num
  · refine' tendsto_rpow_neg_atTop _
    norm_num

-- l ≥ 4 / μ₀
-- l > 0
-- l ^ (- 1 / 6) + l ^ (- 3 / 4) ≤ μ₀ * log (3 / 2) / 8
theorem four_one_part_nine (hμ₀ : 0 < μ₀) :
    ∀ᶠ l : ℕ in atTop,
      ∀ k,
        l ≤ k →
          ∀ (μ σ : ℝ) (b m : ℕ),
            μ₀ ≤ μ →
              μ - 2 / k ≤ σ →
                (b : ℝ) ≤ σ * m / 2 →
                  b = ⌈(l : ℝ) ^ (1 / 4 : ℝ)⌉₊ →
                    m = ⌈(l : ℝ) ^ (2 / 3 : ℝ)⌉₊ →
                      (1 / 2 : ℝ) ≤ 3 / 4 * exp (-4 * b / (μ * k) - b ^ 2 / (σ * m)) := by
  have t : Filter.Tendsto (Nat.cast : ℕ → ℝ) atTop atTop := tendsto_natCast_atTop_atTop
  have ineq : 0 + 0 < log (3 / 2) * μ₀ / (4 * 2) := by
    rw [add_zero]
    refine' div_pos (mul_pos _ hμ₀) (by norm_num1)
    refine' log_pos _
    norm_num
  have := four_one_part_nine_aux.eventually_le_const ineq
  have h4 : (0 : ℝ) < 1 / 4 := by norm_num1
  filter_upwards [((tendsto_rpow_atTop h4).comp t).eventually_ge_atTop (1 / 2),
    mu_div_two_le_sigma hμ₀, t.eventually_gt_atTop 0, Filter.eventually_gt_atTop 0,
    t.eventually this] with l hl hl' hl'' hl''' hl'''' k hlk μ σ b m hμ hσ hσ' hb hm
  --
  suffices (2 / 3 : ℝ) ≤ exp (-4 * b / (μ * k) - b ^ 2 / (σ * m)) by linarith only [this]
  have hσbound : μ / 2 ≤ σ := hl' k hlk μ hμ σ hσ
  rw [← log_le_iff_le_exp]
  swap
  · norm_num1
  have hmpos : 0 < m := by
    rw [hm, Nat.ceil_pos]
    positivity
  rw [neg_mul, neg_div, neg_sub_left, le_neg, ← log_inv, inv_div]
  have hμ' : 0 < μ := hμ₀.trans_le hμ
  have hfirst : (b : ℝ) ^ 2 / (σ * m) ≤ b ^ 2 / m * (2 / μ) := by
    rw [mul_comm, ← div_div, div_eq_mul_inv _ σ]
    refine' mul_le_mul_of_nonneg_left _ (by positivity)
    have hσpos : 0 < σ := (div_pos hμ' (by norm_num : (0 : ℝ) < 2)).trans_le hσbound
    have hinv : σ⁻¹ ≤ (μ / 2)⁻¹ :=
      (inv_le_inv₀ hσpos (div_pos hμ' (by norm_num : (0 : ℝ) < 2))).2 hσbound
    simpa [inv_div] using hinv
  refine' (add_le_add_left hfirst _).trans _
  have h' := ceil_le_two_hMul hl
  dsimp at h'
  have : (b ^ 2 : ℝ) / m ≤ 4 * l ^ (-(2 / 3 - (1 / 4 : ℝ) * 2)) := by
    rw [neg_sub, rpow_sub hl'', rpow_mul (Nat.cast_nonneg _), rpow_two, mul_div_assoc']
    gcongr
    · rw [hb]
      refine' (pow_le_pow_left₀ (by positivity) h' 2).trans_eq _
      rw [mul_pow]
      congr 1
      norm_num1
    rw [hm]
    exact Nat.le_ceil _
  refine' (add_le_add_left (mul_le_mul_of_nonneg_right this (by positivity)) _).trans _
  have : (4 : ℝ) * b / (μ * k) ≤ l ^ (-(1 - (1 / 4 : ℝ))) * (4 * 2 / μ) := by
    rw [neg_sub, rpow_sub hl'', rpow_one, div_mul_div_comm, mul_comm _ (_ * _ : ℝ), mul_assoc,
      mul_comm μ, hb]
    gcongr
  refine' (add_le_add_right this _).trans _
  rw [mul_comm (4 : ℝ), mul_assoc, mul_div_assoc', ← add_mul]
  have hfactor : 4 * 2 / μ ≤ 4 * 2 / μ₀ :=
    div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 4 * 2) hμ₀ hμ
  have hlog_nonneg : 0 ≤ log (3 / 2) := (log_pos (by norm_num)).le
  calc
    (↑l ^ (-(2 / 3 - 1 / 4 * 2)) + ↑l ^ (-(1 - 1 / 4))) * (4 * 2 / μ)
        ≤ (log (3 / 2) * μ₀ / (4 * 2)) * (4 * 2 / μ) :=
      mul_le_mul_of_nonneg_right hl'''' (by positivity)
    _ ≤ (log (3 / 2) * μ₀ / (4 * 2)) * (4 * 2 / μ₀) :=
      mul_le_mul_of_nonneg_left hfactor (by positivity)
    _ = log (3 / 2) := by field_simp [hμ₀.ne']

-- lemma 4.1
-- (9)
theorem four_one (hμ₀ : 0 < μ₀) :
    ∀ᶠ l : ℕ in atTop,
      ∀ k,
        l ≤ k →
          ∀ μ : ℝ,
            μ₀ ≤ μ →
              ∀ n : ℕ,
                ∀ χ : TopEdgeLabelling (Fin n) (Fin 2),
                  ∀ C : BookConfig χ,
                    ramseyNumber ![k, ⌈(l : ℝ) ^ (2 / 3 : ℝ)⌉₊] ≤ C.numBigBlues μ →
                      (¬∃ m : Finset (Fin n), χ.MonochromaticOf m 0 ∧ k ≤ m.card) →
                        ∃ s t : Finset (Fin n),
                          s ⊆ C.X ∧
                            t ⊆ C.X ∧
                              Disjoint s t ∧
                                χ.MonochromaticOf s 1 ∧
                                  χ.MonochromaticBetween s t 1 ∧
                                    (l : ℝ) ^ (1 / 4 : ℝ) ≤ s.card ∧
                                      μ ^ s.card * C.X.card / 2 ≤ t.card := by
  have t : Filter.Tendsto (Nat.cast : ℕ → ℝ) atTop atTop := tendsto_natCast_atTop_atTop
  have h23 : (0 : ℝ) < 2 / 3 := by norm_num
  filter_upwards [Filter.eventually_ge_atTop 6, four_one_part_four hμ₀, four_one_part_nine hμ₀,
    mu_div_two_le_sigma hμ₀, t.eventually_ge_atTop (4 / μ₀),
    ((tendsto_rpow_atTop h23).comp t).eventually_gt_atTop 2] with l hl hl' hl₃ hl₄ hl₅ hl₆ k hlk μ
    hμ n χ C hC hR
  --
  obtain ⟨U, Ublue, Usize, UX, Uneigh⟩ := four_one_part_one μ l k C hC hR
  set m := ⌈(l : ℝ) ^ (2 / 3 : ℝ)⌉₊
  have hm : 3 ≤ m := by rwa [Nat.add_one_le_ceil_iff, Nat.cast_two]
  have hC' : ramseyNumber ![k, m] ≤ C.X.card := hC.trans (Finset.card_le_card (filter_subset _ _))
  let σ := (blue_density χ) U (C.X \ U)
  have hμ' : 0 < μ := hμ₀.trans_le hμ
  have h11 : μ - 2 / k ≤ σ :=
    (four_one_part_three μ hμ'.le (hl.trans hlk) (hl.trans' (by norm_num1)) Usize hC').trans
      (four_one_part_two μ (hl.trans_lt' (by norm_num1)).ne' Usize UX Uneigh)
  -- simp only [←nat.ceil_le],
  specialize hl' k hlk μ hμ σ h11
  set b := ⌈(l : ℝ) ^ (1 / 4 : ℝ)⌉₊
  have hb : b ≠ 0 := by
    rw [ne_eq, Nat.ceil_eq_zero, not_le]
    refine' rpow_pos_of_pos _ _
    rw [Nat.cast_pos]
    linarith only [hl]
  specialize hl₃ k hlk μ σ b m hμ h11 hl' rfl rfl
  have : μ / 2 ≤ σ := hl₄ k hlk μ hμ σ h11
  have hk : 4 / μ ≤ k := by
    refine' ((div_le_div_of_nonneg_left (by norm_num1) hμ₀ hμ).trans hl₅).trans _
    rwa [Nat.cast_le]
  have hσ₀ : 0 < σ := this.trans_lt' (by positivity)
  have hσ₁ : σ ≤ 1 := by
    dsimp [σ]
    exact colDensity_le_one
  have h₁ :
    μ ^ b * C.X.card / 2 * m.choose b ≤
      ∑ S ∈ Finset.powersetCard b U, ((commonBlues χ S ∩ (C.X \ U)).card : ℝ) := by
    rw [four_one_part_five χ]
    refine' (four_one_part_six χ σ Usize hb rfl).trans' _
    refine' (four_one_part_seven hl' hσ₀ hσ₁ hμ' h11 (hl.trans hlk) hm hk UX Usize hC').trans' _
    rw [div_mul_eq_mul_div, div_eq_mul_one_div]
    refine' (mul_le_mul_of_nonneg_left hl₃ (by positivity)).trans_eq _
    simp only [mul_assoc]
  have hbm : b ≤ m := b_le_m hl' hσ₀.le hσ₁
  obtain ⟨S, hSU, hScard, hT⟩ := four_one_part_eight Usize hbm h₁
  refine' ⟨S, commonBlues χ S ∩ (C.X \ U), _, _, _, _, _, _, _⟩
  · exact hSU.trans UX
  · exact Finset.inter_subset_right.trans Finset.sdiff_subset
  · refine' Disjoint.inf_right' _ _
    refine' Disjoint.mono_left hSU _
    exact disjoint_sdiff
  · refine' Ublue.subset _
    exact hSU
  · refine' monochromaticBetween_commonBlues.subset_right _
    exact Finset.inter_subset_left
  · rw [hScard]
    exact Nat.le_ceil _
  rwa [hScard]

theorem four_one' (hμ₀ : 0 < μ₀) :
    ∀ᶠ l : ℕ in atTop,
      ∀ k,
        l ≤ k →
          ∀ μ,
            μ₀ ≤ μ →
              ∀ n : ℕ,
                ∀ χ : TopEdgeLabelling (Fin n) (Fin 2),
                  ∀ C : BookConfig χ,
                    ramseyNumber ![k, ⌈(l : ℝ) ^ (2 / 3 : ℝ)⌉₊] ≤ C.numBigBlues μ →
                      (¬∃ m : Finset (Fin n), χ.MonochromaticOf m 0 ∧ k ≤ m.card) →
                        ∃ s t : Finset (Fin n),
                          (l : ℝ) ^ (1 / 4 : ℝ) ≤ s.card ∧
                            (s, t) ∈ BookConfig.usefulBlueBooks χ μ C.X := by
  filter_upwards [four_one hμ₀] with l hl k hlk μ hμ n χ C h₁ h₂
  obtain ⟨s, t, hs, ht, hst, hs', hst', hscard, htcard⟩ := hl k hlk μ hμ n χ C h₁ h₂
  refine' ⟨s, t, hscard, _⟩
  rw [BookConfig.mem_usefulBlueBooks']
  exact ⟨hs, ht, hst, hs', hst', htcard⟩

theorem four_three_aux (hμ₀ : 0 < μ₀) :
    ∀ᶠ l : ℕ in atTop,
      ∀ k,
        l ≤ k →
          ∀ μ,
            μ₀ ≤ μ →
              ∀ n : ℕ,
                ∀ χ : TopEdgeLabelling (Fin n) (Fin 2),
                  (¬∃ m : Finset (Fin n), χ.MonochromaticOf m 0 ∧ k ≤ m.card) →
                    ∀ C : BookConfig χ,
                      ramseyNumber ![k, ⌈(l : ℝ) ^ (2 / 3 : ℝ)⌉₊] ≤ C.numBigBlues μ →
                         (l : ℝ) ^ (1 / 4 : ℝ) ≤ (BookConfig.getBook χ μ C.X).1.card := by
  filter_upwards [four_one' hμ₀] with l hl k hlk μ hμ n χ hχ C hC
  obtain ⟨s, t, hs, hst⟩ := hl k hlk μ hμ n χ C hC hχ
  refine' hs.trans _
  rw [Nat.cast_le]
  exact BookConfig.getBook_max s t hst

theorem four_three_aux' (hμ₀ : 0 < μ₀) :
    ∀ᶠ l : ℕ in atTop,
      ∀ k,
        l ≤ k →
          ∀ μ,
            μ₀ ≤ μ →
              ∀ n : ℕ,
                ∀ χ : TopEdgeLabelling (Fin n) (Fin 2),
                  (¬∃ m : Finset (Fin n), χ.MonochromaticOf m 0 ∧ k ≤ m.card) →
                    ∀ init : BookConfig χ,
                      ∀ i : ℕ,
                        i ≤ finalStep μ k l init →
                          (l : ℝ) ^ (1 / 4 : ℝ) * (bigBlueSteps μ k l init ∩ range i).card ≤
                             (algorithm μ k l init i).B.card := by
  filter_upwards [Filter.eventually_gt_atTop 0, four_three_aux hμ₀] with l hl₀ hl k hlk μ hμ
    n χ hχ init i hi
  induction' i with i ih
  · rw [range_zero, inter_empty, card_empty, Nat.cast_zero, MulZeroClass.mul_zero]
    exact Nat.cast_nonneg _
  rw [range_add_one]
  rw [Nat.succ_le_iff] at hi
  specialize ih hi.le
  by_cases hstep : i ∈ bigBlueSteps μ k l init
  swap
  · rw [Finset.inter_insert_of_notMem hstep]
    refine' ih.trans _
    rw [Nat.cast_le]
    exact Finset.card_le_card (b_subset hi)
  rw [Finset.inter_insert_of_mem hstep, card_insert_of_notMem]
  swap
  · simp
  rw [big_blue_applied hstep, BookConfig.bigBlueStep_b, Nat.cast_add_one, mul_add_one,
    card_union_of_disjoint, Nat.cast_add]
  · refine' add_le_add ih _
    rw [bigBlueSteps, mem_filter] at hstep
    exact hl k hlk μ hμ n χ hχ _ hstep.2.2
  refine' Disjoint.mono_right BookConfig.getBook_fst_subset _
  exact (algorithm μ k l init i).hXB.symm

theorem four_three (hμ₀ : 0 < μ₀) :
    ∀ᶠ l : ℕ in atTop,
      ∀ k,
        l ≤ k →
          ∀ μ,
            μ₀ ≤ μ →
              ∀ n : ℕ,
                ∀ χ : TopEdgeLabelling (Fin n) (Fin 2),
                  (¬∃ (m : Finset (Fin n)) (c : Fin 2),
                        χ.MonochromaticOf m c ∧ ![k, l] c ≤ m.card) →
                    ∀ init : BookConfig χ,
                           ((bigBlueSteps μ k l init).card : ℝ) ≤ (l : ℝ) ^ (3 / 4 : ℝ) := by
  filter_upwards [four_three_aux' hμ₀, Filter.eventually_gt_atTop 0] with l hl hl₀ k hlk μ hμ
    n χ hχ init
  simp only [Fin.exists_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    exists_or, not_or] at hχ
  obtain ⟨hχr, hχb⟩ := hχ
  specialize hl k hlk μ hμ n χ hχr init (finalStep μ k l init) le_rfl
  have : bigBlueSteps μ k l init ∩ range (finalStep μ k l init) = bigBlueSteps μ k l init := by
    rw [Finset.inter_eq_left, bigBlueSteps]
    exact filter_subset _ _
  rw [this] at hl
  push_neg at hχb
  by_contra hcontra
  rw [not_le] at hcontra
  refine' (not_lt_of_ge ((mul_le_mul_of_nonneg_left hcontra.le (by positivity)).trans hl)) _
  rw [← rpow_add (by exact_mod_cast hl₀),
    show (1 / 4 + 3 / 4 : ℝ) = 1 by norm_num, rpow_one, Nat.cast_lt]
  exact hχb (endState μ k l init).B (endState μ k l init).blue_b

theorem four_four_red_aux {μ : ℝ} {k l : ℕ} (ini : BookConfig χ) (i : ℕ)
    (hi : i ≤ finalStep μ k l ini) :
    (redSteps μ k l ini ∩ range i).card ≤ (algorithm μ k l ini i).A.card := by
  induction' i with i ih
  · rw [range_zero, inter_empty, card_empty]
    simp
  rw [range_add_one]
  rw [Nat.succ_le_iff] at hi
  specialize ih hi.le
  by_cases hstep : i ∈ redSteps μ k l ini
  swap
  · rw [Finset.inter_insert_of_notMem hstep]
    refine' ih.trans _
    exact Finset.card_le_card (a_subset hi)
  rw [Finset.inter_insert_of_mem hstep, card_insert_of_notMem]
  swap
  · simp
  rwa [red_applied hstep, BookConfig.redStepBasic_a, card_insert_of_notMem, add_le_add_iff_right]
  refine' Finset.disjoint_left.1 (algorithm μ k l ini i).hXA _
  exact BookConfig.getCentralVertex_mem_x _ _ _

theorem four_four_blue_density_aux {μ : ℝ} {k l : ℕ} (hk : k ≠ 0) (hl : l ≠ 0) (ini : BookConfig χ)
    (i : ℕ) (hi : i ≤ finalStep μ k l ini) :
    ((bigBlueSteps μ k l ini ∪ densitySteps μ k l ini) ∩ range i).card ≤
      (algorithm μ k l ini i).B.card := by
  induction' i with i ih
  · rw [range_zero, inter_empty, card_empty]
    simp
  rw [range_add_one]
  rw [Nat.succ_le_iff] at hi
  specialize ih hi.le
  by_cases hstep : i ∈ bigBlueSteps μ k l ini ∪ densitySteps μ k l ini
  swap
  · rw [Finset.inter_insert_of_notMem hstep]
    exact ih.trans (Finset.card_le_card (b_subset hi))
  rw [Finset.inter_insert_of_mem hstep, card_insert_of_notMem]
  swap
  · simp
  refine' (show #((bigBlueSteps μ k l ini ∪ densitySteps μ k l ini) ∩ range i) + 1 ≤
      #(algorithm μ k l ini i).B + 1 by simpa [add_comm] using add_le_add_right ih 1).trans _
  rw [mem_union] at hstep
  cases hstep with
  | inl hbig =>
    rw [big_blue_applied hbig, BookConfig.bigBlueStep_b, card_union_of_disjoint,
      add_le_add_iff_left]
    swap
    · refine' Disjoint.mono_right BookConfig.getBook_fst_subset _
      exact (algorithm μ k l ini i).hXB.symm
    rw [bigBlueSteps, mem_filter] at hbig
    exact BookConfig.one_le_card_getBook_fst (BookConfig.get_book_condition hk hl hbig.2.2)
  | inr hdens =>
    rw [density_applied hdens, BookConfig.densityBoostStepBasic_b, card_insert_of_notMem]
    refine' Finset.disjoint_left.1 (algorithm μ k l ini i).hXB _
    exact BookConfig.getCentralVertex_mem_x _ _ _

theorem t_le_a_card (μ : ℝ) (k l : ℕ) (ini : BookConfig χ) :
    (redSteps μ k l ini).card ≤ (endState μ k l ini).A.card := by
  have hl := four_four_red_aux ini (finalStep μ k l ini) le_rfl
  have : redSteps μ k l ini ∩ range (finalStep μ k l ini) = redSteps μ k l ini := by
    rw [Finset.inter_eq_left]
    exact redSteps_subset_redOrDensitySteps.trans (filter_subset _ _)
  rwa [this] at hl

-- observation 4.4
theorem four_four_red (μ : ℝ) {k l : ℕ}
    (h : ¬∃ (m : Finset V) (c : Fin 2), χ.MonochromaticOf m c ∧ ![k, l] c ≤ m.card)
     (ini : BookConfig χ) : (redSteps μ k l ini).card ≤ k := by
  have hl := t_le_a_card μ k l ini
  simp only [Fin.exists_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    exists_or, not_or, not_exists, not_and, not_le] at h
  exact hl.trans (h.1 _ (endState μ k l ini).red_a).le

-- observation 4.4
theorem four_four_blue_density (μ : ℝ) {k l : ℕ} (hk : k ≠ 0) (hl : l ≠ 0)
    (h : ¬∃ (m : Finset V) (c : Fin 2), χ.MonochromaticOf m c ∧ ![k, l] c ≤ m.card)
     (ini : BookConfig χ) : (bigBlueSteps μ k l ini).card + (densitySteps μ k l ini).card ≤ l := by
  have hl := four_four_blue_density_aux hk hl ini (finalStep μ k l ini) le_rfl
  have :
    (bigBlueSteps μ k l ini ∪ densitySteps μ k l ini) ∩ range (finalStep μ k l ini) =
      bigBlueSteps μ k l ini ∪ densitySteps μ k l ini := by
    rw [Finset.inter_eq_left, union_subset_iff]
    exact ⟨filter_subset _ _, densitySteps_subset_redOrDensitySteps.trans (filter_subset _ _)⟩
  rw [← card_union_of_disjoint, ← this]
  · simp only [Fin.exists_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      exists_or, not_or, not_exists, not_and, not_le] at h
    exact hl.trans (h.2 _ (endState μ k l ini).blue_b).le
  refine' bigBlueSteps_disjoint_redOrDensitySteps.mono_right _
  exact densitySteps_subset_redOrDensitySteps

-- observation 4.4
theorem four_four_degree (μ : ℝ) {k l : ℕ} (hk : k ≠ 0) (hl : l ≠ 0)
    (h : ¬∃ (m : Finset V) (c : Fin 2), χ.MonochromaticOf m c ∧ ![k, l] c ≤ m.card)
     (ini : BookConfig χ) : (degreeSteps μ k l ini).card ≤ k + l + 1 := by
  refine' num_degreeSteps_le_add.trans _
  rw [add_le_add_iff_right, add_assoc]
  exact add_le_add (four_four_red μ h _) (four_four_blue_density μ hk hl h _)

end SimpleGraph
