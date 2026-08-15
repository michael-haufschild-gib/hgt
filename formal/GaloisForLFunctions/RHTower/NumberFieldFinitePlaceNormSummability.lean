import Mathlib.NumberTheory.NumberField.DedekindZeta

/-!
# Summability of number-field finite-prime norm powers

This module derives the finite-place norm budget needed for Artin Euler products from Mathlib's
ideal-count asymptotic.  It is a number-field theorem, independent of representations and of any
analytic continuation claim.
-/

open scoped BigOperators Topology Real nonZeroDivisors
open Filter Asymptotics
open NumberField IsDedekindDomain

noncomputable section

universe u

namespace GaloisForLFunctions

variable {K : Type u} [Field K] [NumberField K]

/-- Finite-prime norm powers of a number field are summable for every exponent strictly greater
than one. -/
theorem numberField_summable_finitePlace_absNorm_rpow
    {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun v : HeightOneSpectrum (𝓞 K) =>
      (v.asIdeal.absNorm : ℝ) ^ (-σ)) := by
  classical
  let a : ℕ → ℝ := fun n =>
    Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n}
  have ha_nonneg : ∀ n, 0 ≤ a n := fun n => Nat.cast_nonneg _
  have hcard (n : ℕ) :
      Nat.card {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ n} =
        ∑ k ∈ Finset.Icc 1 n, Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = k} := by
    rw [← add_left_inj 1, ← Ideal.card_norm_le_eq_card_norm_le_add_one,
      show Finset.Icc 1 n = Finset.Ioc 0 n from Finset.Icc_succ_left_eq_Ioc _ _,
      show 1 = Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = 0} by
        simp [Ideal.absNorm_eq_zero_iff],
      Finset.sum_Ioc_add_eq_sum_Icc n.zero_le,
      ← Finset.card_preimage_eq_sum_card_image_eq
        (fun k _ ↦ Ideal.finite_setOf_absNorm_eq k)]
    simp [Set.coe_eq_subtype]
  have hlim :
      Tendsto (fun n : ℕ => (∑ k ∈ Finset.Icc 1 n, a k) / (n : ℝ)) atTop
        (𝓝 (NumberField.dedekindZeta_residue K)) := by
    refine ((NumberField.Ideal.tendsto_norm_le_div_atTop₀ K).comp
      tendsto_natCast_atTop_atTop).congr fun n ↦ ?_
    simp only [Function.comp_apply, Nat.cast_le]
    rw [hcard n, Nat.cast_sum]
  have hO :
      (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, a k) =O[atTop]
        fun n ↦ (n : ℝ) ^ (1 : ℝ) := by
    apply Asymptotics.isBigO_atTop_natCast_rpow_of_tendsto_div_rpow
    convert hlim using 1
    simp
  have hL : LSeriesSummable (fun n ↦ (a n : ℂ)) (σ : ℂ) :=
    LSeriesSummable_of_sum_norm_bigO_and_nonneg hO ha_nonneg (by norm_num) (by simpa using hσ)
  let q : ℕ → ℝ := fun n => if n = 0 then 0 else a n * (n : ℝ) ^ (-σ)
  have hq : Summable q := by
    rw [LSeriesSummable] at hL
    refine hL.norm.congr fun n ↦ ?_
    by_cases hn : n = 0
    · simp [q, hn, LSeries.term_def]
    · rw [LSeries.term_def, if_neg hn, norm_div, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (ha_nonneg n),
        Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn)]
      simp only [q, if_neg hn, Complex.ofReal_re]
      rw [Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]
  let F : (Σ n : ℕ, {I : Ideal (𝓞 K) // Ideal.absNorm I = n}) → ℝ := fun x =>
    if x.1 = 0 then 0 else (x.1 : ℝ) ^ (-σ)
  have hF_nonneg : ∀ x, 0 ≤ F x := by
    intro x
    by_cases hx : x.1 = 0
    · simp [F, hx]
    · simp only [F, if_neg hx]
      exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hF : Summable F := by
    refine (summable_sigma_of_nonneg hF_nonneg).mpr ⟨?_, ?_⟩
    · intro n
      letI : Fintype {I : Ideal (𝓞 K) // Ideal.absNorm I = n} :=
        (Ideal.finite_setOf_absNorm_eq n).fintype
      exact Summable.of_finite
    · refine hq.congr fun n ↦ ?_
      letI : Fintype {I : Ideal (𝓞 K) // Ideal.absNorm I = n} :=
        (Ideal.finite_setOf_absNorm_eq n).fintype
      by_cases hn : n = 0
      · simp [F, q, hn]
      · simp only [F, q, if_neg hn, tsum_fintype, Finset.sum_const, Finset.card_univ,
          nsmul_eq_mul]
        change (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℝ) *
            (n : ℝ) ^ (-σ) =
          (Fintype.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℝ) *
            (n : ℝ) ^ (-σ)
        rw [Nat.card_eq_fintype_card]
  let e : (Σ n : ℕ, {I : Ideal (𝓞 K) // Ideal.absNorm I = n}) ≃ Ideal (𝓞 K) :=
    Equiv.sigmaFiberEquiv fun I : Ideal (𝓞 K) => Ideal.absNorm I
  have hIdeals : Summable (fun I : Ideal (𝓞 K) =>
      if I = ⊥ then 0 else (Ideal.absNorm I : ℝ) ^ (-σ)) := by
    refine e.summable_iff.mp (hF.congr fun x ↦ ?_)
    rcases x with ⟨n, I⟩
    change (if n = 0 then 0 else (n : ℝ) ^ (-σ)) =
      if e ⟨n, I⟩ = ⊥ then 0 else (Ideal.absNorm (e ⟨n, I⟩) : ℝ) ^ (-σ)
    change (if n = 0 then 0 else (n : ℝ) ^ (-σ)) =
      if (I : Ideal (𝓞 K)) = ⊥ then 0 else (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ^ (-σ)
    by_cases hn : n = 0
    · have hI : (I : Ideal (𝓞 K)) = ⊥ :=
        Ideal.absNorm_eq_zero_iff.mp (I.property.trans hn)
      simp [hn, hI]
    · have hI : (I : Ideal (𝓞 K)) ≠ ⊥ := by
        intro hI
        apply hn
        rw [← I.property, hI]
        simp
      simp [hn, hI, I.property]
  have hPrimes : Summable (fun v : HeightOneSpectrum (𝓞 K) =>
      if v.asIdeal = ⊥ then 0 else (v.asIdeal.absNorm : ℝ) ^ (-σ)) := by
    simpa [Function.comp_def] using
      hIdeals.comp_injective HeightOneSpectrum.asIdeal_injective
  refine hPrimes.congr fun v ↦ ?_
  simp [v.ne_bot]

/-- The complex norm of finite-prime Euler arguments is summable in the half-plane
`1 < re s`. -/
theorem numberField_summable_finitePlace_norm_cpow
    {s : ℂ} (hs : 1 < s.re) :
    Summable (fun v : HeightOneSpectrum (𝓞 K) =>
      ‖((v.asIdeal.absNorm : ℂ) ^ (-s))‖) := by
  refine (numberField_summable_finitePlace_absNorm_rpow (K := K) hs).congr fun v ↦ ?_
  have hvnorm_ne : v.asIdeal.absNorm ≠ 0 := by
    intro hvnorm
    exact v.ne_bot (Ideal.absNorm_eq_zero_iff.mp hvnorm)
  rw [Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hvnorm_ne), Complex.neg_re]

end GaloisForLFunctions
