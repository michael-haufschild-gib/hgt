import GaloisForLFunctions.ArithmeticOrientationTheory.TheOffLineZerosObstructTheMoebiusReceiver
import GaloisForLFunctions.ArithmeticOrientationTheory.TheObstructionCountIsTheCodimensionOfTheRepairingIdeal

/-!
# The Möbius receiver counts its off-line zeros

Each zero `ρ` of `ζ` with `½ + ε < Re ρ < 1` and `ζ(ρ − ε) ≠ 0` is an obstruction point `ρ − ε` of
the damped Möbius weight `μ(d)d^{−ε}` (`mem_obstructionHull_moebius_of_zero`).  Distinct zeros give
distinct points (`eq_of_halfPlanePoint_two_three`: the values at `2` and `3` determine `s`, since
`3^a ≠ 2^b`), and finitely many separated characters map `𝒲_{1/2}` onto `ℂ^m`
(`surjective_pi_algHom_of_separated`).  Hence the repairing ideal has codimension at least the number
of such zeros (`card_le_rank_quotient_paidIdeal_moebius`): the index of the receiver is a lower bound
for the off-line zero count, one dimension per zero.
-/

open Finset ArithmeticFunction LSeries Complex

namespace GaloisForLFunctions.ArithmeticOrientationTheory

open TransHorizonIncidenceMechanics WienerAlgebraAt BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-! ### Separated characters are jointly surjective -/

/-- Finitely many pairwise separated characters of a commutative `ℂ`-algebra map it onto `ℂ^ι`:
`e_i = ∏_{j ≠ i} (χ_i a_{ij} − χ_j a_{ij})⁻¹ (a_{ij} − χ_j a_{ij})` has `χ_k e_i = δ_{ik}`. -/
theorem surjective_pi_algHom_of_separated {A : Type} [CommRing A] [Algebra ℂ A] {ι : Type}
    [Fintype ι] [DecidableEq ι] (χ : ι → A →ₐ[ℂ] ℂ) (hsep : ∀ i j, i ≠ j → ∃ a, χ i a ≠ χ j a) :
    Function.Surjective (AlgHom.pi χ) := by
  choose a ha using hsep
  let fac : ι → ι → A := fun i j => if h : j = i then 1 else
    (χ i (a i j (Ne.symm h)) - χ j (a i j (Ne.symm h)))⁻¹ •
      (a i j (Ne.symm h) - algebraMap ℂ A (χ j (a i j (Ne.symm h))))
  let e : ι → A := fun i => ∏ j, fac i j
  have hfac : ∀ i j k, χ k (fac i j) = if h : j = i then 1 else
      (χ i (a i j (Ne.symm h)) - χ j (a i j (Ne.symm h)))⁻¹ *
        (χ k (a i j (Ne.symm h)) - χ j (a i j (Ne.symm h))) := fun i j k => by
    simp only [fac]
    split_ifs with h
    · exact _root_.map_one _
    · rw [map_smul, map_sub, AlgHom.commutes, smul_eq_mul]; rfl
  have he : ∀ i k, χ k (e i) = if k = i then 1 else 0 := fun i k => by
    simp only [e, map_prod, hfac]
    split_ifs with hki
    · subst hki
      refine Finset.prod_eq_one fun j _ => ?_
      split_ifs with h
      · rfl
      · exact inv_mul_cancel₀ (sub_ne_zero.2 (ha k j (Ne.symm h)))
    · refine Finset.prod_eq_zero (mem_univ k) ?_
      rw [dif_neg hki, sub_self, mul_zero]
  intro v
  refine ⟨∑ i, v i • e i, funext fun k => ?_⟩
  rw [AlgHom.pi_apply, map_sum]
  simp only [map_smul, he, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq, if_pos (mem_univ k)]

/-- An ideal killed by `m` separated characters has codimension at least `m`. -/
theorem card_le_rank_quotient_of_separated {A : Type} [CommRing A] [Algebra ℂ A] {ι : Type}
    [Fintype ι] [DecidableEq ι] (χ : ι → A →ₐ[ℂ] ℂ) (hsep : ∀ i j, i ≠ j → ∃ a, χ i a ≠ χ j a)
    (I : Ideal A) (hI : ∀ x ∈ I, ∀ i, χ i x = 0) :
    (Fintype.card ι : Cardinal) ≤ Module.rank ℂ (A ⧸ I) := by
  let L := Ideal.Quotient.liftₐ I (AlgHom.pi χ)
    fun x hx => funext fun i => hI x hx i
  have hsurj : Function.Surjective L := by
    intro v
    obtain ⟨x, rfl⟩ := surjective_pi_algHom_of_separated χ hsep v
    exact ⟨Ideal.Quotient.mk I x, rfl⟩
  have h := rank_range_le L.toLinearMap
  rwa [LinearMap.range_eq_top.2 hsurj, rank_top, rank_fun'] at h

/-! ### Distinct half-plane points -/

/-- The values at `2` and `3` determine a half-plane point. -/
theorem eq_of_halfPlanePoint_two_three {s s' : ℂ} (hs : (1 / 2 : ℝ) ≤ s.re)
    (hs' : (1 / 2 : ℝ) ≤ s'.re)
    (h2 : (halfPlanePoint (1 / 2) s hs).ω 2 = (halfPlanePoint (1 / 2) s' hs').ω 2)
    (h3 : (halfPlanePoint (1 / 2) s hs).ω 3 = (halfPlanePoint (1 / 2) s' hs').ω 3) : s = s' := by
  have hexp : ∀ (n : ℕ) (hn : n ≠ 0) (z : ℂ) (hz : (1 / 2 : ℝ) ≤ z.re),
      (halfPlanePoint (1 / 2) z hz).ω n = exp ((Real.log n : ℂ) * (((1 / 2 : ℝ) : ℂ) - z)) := by
    intro n hn z hz
    have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    simp only [halfPlanePoint, hn, if_false]
    rw [cpow_def_of_ne_zero hn', ← ofReal_natCast,
      ← ofReal_log (by exact_mod_cast (Nat.zero_le n) : (0 : ℝ) ≤ n)]
  rw [hexp 2 two_ne_zero, hexp 2 two_ne_zero] at h2
  rw [hexp 3 three_ne_zero, hexp 3 three_ne_zero] at h3
  obtain ⟨a, ha⟩ := exp_eq_exp_iff_exists_int.1 h2
  obtain ⟨b, hb⟩ := exp_eq_exp_iff_exists_int.1 h3
  push_cast at ha hb
  have hπ : (2 * Real.pi : ℂ) * I ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero (ofReal_ne_zero.2 Real.pi_ne_zero)) I_ne_zero
  have hreal : ((a * Real.log 3 - b * Real.log 2 : ℝ) : ℂ) * (2 * Real.pi * I) = 0 := by
    push_cast
    linear_combination (Real.log 2 : ℂ) * hb - (Real.log 3 : ℂ) * ha
  have hreal' : (a : ℝ) * Real.log 3 = b * Real.log 2 := by
    have := (mul_eq_zero.1 hreal).resolve_right hπ
    rw [ofReal_eq_zero] at this
    linarith
  have hz : (3 : ℝ) ^ a = (2 : ℝ) ^ b := by
    rw [← Real.rpow_intCast, ← Real.rpow_intCast, Real.rpow_def_of_pos (by norm_num),
      Real.rpow_def_of_pos (by norm_num)]
    congr 1
    linarith
  have ha0 := int_eq_zero_of_three_zpow_eq_two_zpow hz
  rw [ha0, Int.cast_zero, zero_mul, add_zero] at ha
  have hl2 : (Real.log 2 : ℂ) ≠ 0 := ofReal_ne_zero.2 (Real.log_pos one_lt_two).ne'
  have := mul_left_cancel₀ hl2 ha
  linear_combination -this

/-! ### The count -/

/-- **The Möbius receiver counts its off-line zeros.**  For `0 < ε < ½` and any finite set `Z` of
zeros of `ζ` with `½ + ε < Re ρ < 1` and `ζ(ρ − ε) ≠ 0`, the repairing ideal of `μ(d)d^{−ε}` has
codimension at least `|Z|`. -/
theorem card_le_rank_quotient_paidIdeal_moebius {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2)
    (Z : Finset ℂ) (hZ : ∀ ρ ∈ Z, 1 / 2 + ε < ρ.re ∧ ρ.re < 1 ∧ riemannZeta ρ = 0 ∧
      riemannZeta (ρ - ε) ≠ 0) :
    (Z.card : Cardinal) ≤ Module.rank ℂ (WienerAlgebraAt (1 / 2) ⧸
      paidIdeal (pmPowerDampedRealWeight ε) (summable_abs_moebius_div hε)) := by
  classical
  have hre : ∀ ρ : Z, (1 / 2 : ℝ) ≤ ((ρ : ℂ) - ε).re := fun ρ => by
    have := (hZ ρ ρ.2).1; simp; linarith
  let χ : Z → WienerAlgebraAt (1 / 2) →ₐ[ℂ] ℂ := fun ρ =>
    WienerAlgebraAt.bohrCharacter (1 / 2) (halfPlanePoint (1 / 2) ((ρ : ℂ) - ε) (hre ρ))
  have hsep : ∀ ρ ρ', ρ ≠ ρ' → ∃ a, χ ρ a ≠ χ ρ' a := by
    intro ρ ρ' hne
    have hval : ∀ (n : ℕ), n ≠ 0 → ∀ ρ'' : Z, χ ρ'' (pointMass n) =
        (halfPlanePoint (1 / 2) ((ρ'' : ℂ) - ε) (hre ρ'')).ω n / (n : ℂ) ^ ((1 / 2 : ℝ) : ℂ) :=
      fun n hn ρ'' => by
        rw [WienerAlgebraAt.bohrCharacter_apply, toFn_pointMass, bohrEval_pointMass hn]
    have hn0 : ∀ n : ℕ, n ≠ 0 → (n : ℂ) ^ ((1 / 2 : ℝ) : ℂ) ≠ 0 := fun n hn => by
      rw [Ne, cpow_eq_zero_iff]; exact fun h => hn (by exact_mod_cast h.1)
    by_contra hall
    push Not at hall
    have h2 := hall (pointMass 2)
    have h3 := hall (pointMass 3)
    rw [hval 2 two_ne_zero, hval 2 two_ne_zero, div_left_inj' (hn0 2 two_ne_zero)] at h2
    rw [hval 3 three_ne_zero, hval 3 three_ne_zero, div_left_inj' (hn0 3 three_ne_zero)] at h3
    exact hne (Subtype.ext (sub_left_inj.1 (eq_of_halfPlanePoint_two_three _ _ h2 h3)))
  have h := card_le_rank_quotient_of_separated χ hsep _ fun k hk ρ => by
    obtain ⟨h1, h2, h3, h4⟩ := hZ ρ ρ.2
    exact mem_obstructionHull_moebius_of_zero hε hε2 h1 h2 h3 h4 k hk
  rwa [Fintype.card_coe] at h

end

end GaloisForLFunctions.ArithmeticOrientationTheory
