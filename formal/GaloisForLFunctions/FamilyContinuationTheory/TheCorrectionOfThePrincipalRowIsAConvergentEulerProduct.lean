import GaloisForLFunctions.FamilyContinuationTheory.TheFamilyStepReadsTheZerosOfTheLFunctions

/-!
# The correction of the principal row is a convergent Euler product

In the high expansion of the cubic-theta probe the principal row is
`ζ^S(6z) ζ^S(w)/L^S(x, η) · ∏_{P∉S} H_P(x, w, z)`. At the double residue `w = 1`, `z = 1/6` the
local factor, with `Q = N(P)`, `q = Q⁻¹`, `D = η(P) Q^{−s}` and `R = A_P Q^{3−6s}` for a phase
`‖A_P‖ ≤ 1`, is

`h(s) = (1 − q²) (1 − q (R − D)/(1 − D)) / (1 − R)`   (`principalLocalFactor`).

The correction of the target `η` is `H_η = ∏_{P∉S} h_P`. This module proves that it has the
properties the continuation step asks for, uniformly in the phases.

* `norm_principalLocalFactor_sub_one_le`: for `N(P) ≥ 4` and `Re s ≥ σ`,
  `‖h − 1‖ ≤ 14 N(P)^{−e}` whenever `1 ≤ e ≤ min(6σ − 3, 1 + σ, 2)`; so the product converges
  absolutely on `Re s > 2/3`.
* `hasProd_and_bounds_of_defect`: a product of holomorphic factors with summable defects
  `≤ 1/2` is holomorphic, equals `exp` of the sum of the logarithms, and is bounded by
  `exp(3/2 Σ b)`.
* `exists_principalCorrection_cutoff`: for `σ > 2/3` there is `N₀` such that for every finite set
  `S` of primes containing those of norm `≤ N₀` and all phases, `H` is holomorphic on
  `Re s > σ` and `‖H − 1‖ ≤ 1/2` there; in particular `H ≠ 0`.
* `exists_cutoff_zetaZeroAbscissa_le_of_two_estimates`: the native endpoint for
  `K = ℚ(ζ₃)` with this correction (the deleted Euler factors of `S` included), whose only
  premise is the pair of estimates.
-/

noncomputable section

open Complex NumberField IsDedekindDomain
open scoped Classical

namespace GaloisForLFunctions.FamilyContinuationTheory

open HeckeLFunctions _root_.RHTower

/-- The local factor of the principal row at the double residue `w = 1`, `z = 1/6`, for a prime of
norm `Q`, a phase `A` and a character value `η`. -/
def principalLocalFactor (Q : ℝ) (A η s : ℂ) : ℂ :=
  (1 - ((Q : ℂ)⁻¹) ^ 2) *
      (1 - (Q : ℂ)⁻¹ * (A * (Q : ℂ) ^ (3 - 6 * s) - η * (Q : ℂ) ^ (-s)) /
        (1 - η * (Q : ℂ) ^ (-s))) /
    (1 - A * (Q : ℂ) ^ (3 - 6 * s))

/-- The defect of the local factor as one fraction. -/
theorem principal_local_identity (q D R : ℂ) (hR : 1 - R ≠ 0) :
    (1 - q ^ 2) * (1 - q * (R - D) / (1 - D)) / (1 - R) - 1 =
      (R - q ^ 2 - q * (R - D) / (1 - D) * (1 - q ^ 2)) / (1 - R) := by
  rw [div_sub_one hR]
  ring

theorem norm_ofReal_cpow_le {Q a : ℝ} (hQ : 1 ≤ Q) {w : ℂ} (hw : w.re ≤ a) :
    ‖(Q : ℂ) ^ w‖ ≤ Q ^ a := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith)]
  exact Real.rpow_le_rpow_of_exponent_le hQ hw

theorem rpow_le_half_of_four_le {Q a : ℝ} (hQ : 4 ≤ Q) (ha : a ≤ -(1 / 2)) : Q ^ a ≤ 1 / 2 := by
  have hQ0 : 0 < Q := by linarith
  have hs := Real.sqrt_pos.mpr hQ0
  have hs2 := Real.sq_sqrt hQ0.le
  calc Q ^ a ≤ Q ^ (-(1 / 2) : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) ha
    _ = (Real.sqrt Q)⁻¹ := by rw [Real.rpow_neg hQ0.le, ← Real.sqrt_eq_rpow]
    _ ≤ 1 / 2 := by
        rw [← one_div, div_le_iff₀ hs]
        nlinarith [Real.sqrt_nonneg Q]

/-- **The local defect.** For `Q ≥ 4`, `‖A‖, ‖η‖ ≤ 1` and `Re s ≥ σ`,
`‖h − 1‖ ≤ 14 Q^{−e}` for every `e` with `1 ≤ e ≤ min(6σ − 3, 1 + σ, 2)`. -/
theorem norm_principalLocalFactor_sub_one_le {Q σ e : ℝ} {A η s : ℂ} (hQ : 4 ≤ Q)
    (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1) (hs : σ ≤ s.re) (he : 1 ≤ e) (he6 : e ≤ 6 * σ - 3)
    (heσ : e ≤ 1 + σ) (he2 : e ≤ 2) :
    ‖principalLocalFactor Q A η s - 1‖ ≤ 14 * Q ^ (-e) := by
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  set D := η * (Q : ℂ) ^ (-s) with hDdef
  set R := A * (Q : ℂ) ^ (3 - 6 * s) with hRdef
  set q : ℂ := (Q : ℂ)⁻¹ with hqdef
  set T := Q ^ (-e) with hTdef
  have hT0 : 0 ≤ T := Real.rpow_nonneg hQ0.le _
  have hq : ‖q‖ = Q ^ (-1 : ℝ) := by
    rw [hqdef, norm_inv, Complex.norm_real, Real.norm_of_nonneg hQ0.le, Real.rpow_neg_one]
  have hD : ‖D‖ ≤ Q ^ (-σ) := by
    rw [hDdef, norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) hη).trans
      (norm_ofReal_cpow_le hQ1 (by rw [neg_re]; linarith))
  have hR : ‖R‖ ≤ T := by
    rw [hRdef, norm_mul]
    refine (mul_le_of_le_one_left (norm_nonneg _) hA).trans
      ((norm_ofReal_cpow_le hQ1 (a := 3 - 6 * σ) ?_).trans
        (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith)))
    simp only [sub_re, mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero]
    linarith
  have hTq : T ≤ Q ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith)
  have hQinv : Q ^ (-1 : ℝ) ≤ 1 / 4 := by
    rw [Real.rpow_neg_one, inv_eq_one_div, div_le_div_iff₀ hQ0 (by norm_num)]
    linarith
  have hDh : ‖D‖ ≤ 1 / 2 := hD.trans (rpow_le_half_of_four_le hQ (by linarith))
  have hRh : ‖R‖ ≤ 1 / 4 := hR.trans (hTq.trans hQinv)
  have hqD : ‖q‖ * ‖D‖ ≤ T := by
    rw [hq]
    calc Q ^ (-1 : ℝ) * ‖D‖ ≤ Q ^ (-1 : ℝ) * Q ^ (-σ) :=
          mul_le_mul_of_nonneg_left hD (Real.rpow_nonneg hQ0.le _)
      _ = Q ^ (-1 + -σ) := (Real.rpow_add hQ0 _ _).symm
      _ ≤ T := Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith)
  have hq2 : ‖q‖ ^ 2 ≤ T := by
    rw [hq, ← Real.rpow_natCast, ← Real.rpow_mul hQ0.le]
    exact Real.rpow_le_rpow_of_exponent_le hQ1 (by norm_num; linarith)
  have hqR : ‖q‖ * ‖R‖ ≤ T :=
    (mul_le_of_le_one_left (norm_nonneg _) (by rw [hq]; linarith)).trans hR
  have h1D : 1 / 2 ≤ ‖1 - D‖ := by
    have := norm_sub_norm_le (1 : ℂ) D
    rw [norm_one] at this
    linarith
  have h1R : 3 / 4 ≤ ‖1 - R‖ := by
    have := norm_sub_norm_le (1 : ℂ) R
    rw [norm_one] at this
    linarith
  have hR0 : 1 - R ≠ 0 := norm_pos_iff.mp (by linarith)
  have hP : principalLocalFactor Q A η s - 1 =
      (R - q ^ 2 - q * (R - D) / (1 - D) * (1 - q ^ 2)) / (1 - R) :=
    principal_local_identity q D R hR0
  have ha : ‖q * (R - D) / (1 - D)‖ ≤ 4 * T := by
    rw [norm_div, norm_mul, div_le_iff₀ (by linarith)]
    calc ‖q‖ * ‖R - D‖ ≤ ‖q‖ * (‖R‖ + ‖D‖) :=
          mul_le_mul_of_nonneg_left (norm_sub_le _ _) (norm_nonneg _)
      _ = ‖q‖ * ‖R‖ + ‖q‖ * ‖D‖ := by ring
      _ ≤ T + T := add_le_add hqR hqD
      _ ≤ 4 * T * ‖1 - D‖ := by nlinarith
  have hq2' : ‖1 - q ^ 2‖ ≤ 2 := by
    have h := norm_sub_le (1 : ℂ) (q ^ 2)
    rw [norm_one, norm_pow] at h
    linarith
  have hnum : ‖R - q ^ 2 - q * (R - D) / (1 - D) * (1 - q ^ 2)‖ ≤ 10 * T := by
    have e1 : ‖R - q ^ 2‖ ≤ ‖R‖ + ‖q‖ ^ 2 := by
      have h := norm_sub_le R (q ^ 2)
      rwa [norm_pow] at h
    have e2 : ‖q * (R - D) / (1 - D) * (1 - q ^ 2)‖ ≤ 4 * T * 2 := by
      rw [norm_mul]
      exact mul_le_mul ha hq2' (norm_nonneg _) (by positivity)
    calc _ ≤ ‖R - q ^ 2‖ + ‖q * (R - D) / (1 - D) * (1 - q ^ 2)‖ := norm_sub_le _ _
      _ ≤ (‖R‖ + ‖q‖ ^ 2) + 4 * T * 2 := add_le_add e1 e2
      _ ≤ 10 * T := by linarith
  rw [hP, norm_div, div_le_iff₀ (by linarith : (0 : ℝ) < ‖1 - R‖)]
  nlinarith [mul_le_mul_of_nonneg_left h1R hT0]

/-- The local factor is holomorphic in `s` where its two denominators do not vanish. -/
theorem differentiableAt_principalLocalFactor {Q : ℝ} (hQ : 0 < Q) (A η : ℂ) {s : ℂ}
    (hD : 1 - η * (Q : ℂ) ^ (-s) ≠ 0) (hR : 1 - A * (Q : ℂ) ^ (3 - 6 * s) ≠ 0) :
    DifferentiableAt ℂ (principalLocalFactor Q A η) s := by
  have hQ' : (Q : ℂ) ≠ 0 := ofReal_ne_zero.mpr hQ.ne'
  have h1 : DifferentiableAt ℂ (fun s : ℂ => (Q : ℂ) ^ (-s)) s :=
    differentiableAt_id.neg.const_cpow (Or.inl hQ')
  have h2 : DifferentiableAt ℂ (fun s : ℂ => (Q : ℂ) ^ (3 - 6 * s)) s :=
    ((differentiableAt_const 3).sub ((differentiableAt_const 6).mul differentiableAt_id)).const_cpow
      (Or.inl hQ')
  exact ((differentiableAt_const _).mul ((differentiableAt_const 1).sub
    (((differentiableAt_const _).mul ((h2.const_mul A).sub (h1.const_mul η))).div
      ((differentiableAt_const 1).sub (h1.const_mul η)) hD))).div
    ((differentiableAt_const 1).sub (h2.const_mul A)) hR

/-- The denominators of the local factor do not vanish for `Q ≥ 4`, `Re s ≥ 2/3`. -/
theorem principalLocalFactor_denominators {Q : ℝ} (hQ : 4 ≤ Q) {A η s : ℂ} (hA : ‖A‖ ≤ 1)
    (hη : ‖η‖ ≤ 1) (hs : 2 / 3 ≤ s.re) :
    1 - η * (Q : ℂ) ^ (-s) ≠ 0 ∧ 1 - A * (Q : ℂ) ^ (3 - 6 * s) ≠ 0 := by
  have hQ1 : 1 ≤ Q := by linarith
  have hD : ‖η * (Q : ℂ) ^ (-s)‖ ≤ 1 / 2 := by
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) hη).trans
      ((norm_ofReal_cpow_le hQ1 (a := -(1 / 2)) (by rw [neg_re]; linarith)).trans
        (rpow_le_half_of_four_le hQ le_rfl))
  have hR : ‖A * (Q : ℂ) ^ (3 - 6 * s)‖ ≤ 1 / 2 := by
    rw [norm_mul]
    refine (mul_le_of_le_one_left (norm_nonneg _) hA).trans
      ((norm_ofReal_cpow_le hQ1 (a := -1) ?_).trans
        (rpow_le_half_of_four_le hQ (by norm_num)))
    simp only [sub_re, mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero]
    linarith
  constructor
  · intro h
    have := norm_sub_norm_le (1 : ℂ) (η * (Q : ℂ) ^ (-s))
    rw [h, norm_zero, norm_one] at this
    linarith
  · intro h
    have := norm_sub_norm_le (1 : ℂ) (A * (Q : ℂ) ^ (3 - 6 * s))
    rw [h, norm_zero, norm_one] at this
    linarith

/-! ### Products of factors near `1` -/

/-- **A normally convergent product.** Factors holomorphic on an open `U`, with summable defects
`‖f_i − 1‖ ≤ b_i ≤ 1/2`, have a holomorphic product, equal to the exponential of the sum of the
logarithms, whose logarithm is bounded by `3/2 Σ b_i`. -/
theorem hasProd_and_bounds_of_defect {ι : Type*} {f : ι → ℂ → ℂ} {b : ι → ℝ} {U : Set ℂ}
    (hU : IsOpen U) (hb : Summable b) (hf : ∀ i, DifferentiableOn ℂ (f i) U)
    (hfb : ∀ i, ∀ s ∈ U, ‖f i s - 1‖ ≤ b i) (hb2 : ∀ i, b i ≤ 1 / 2) :
    DifferentiableOn ℂ (fun s => ∏' i, f i s) U ∧
      ∀ s ∈ U, ∏' i, f i s = cexp (∑' i, Complex.log (f i s)) ∧
        ‖∑' i, Complex.log (f i s)‖ ≤ 3 / 2 * ∑' i, b i := by
  have hlog : ∀ i, ∀ s ∈ U, ‖Complex.log (f i s)‖ ≤ 3 / 2 * b i := by
    intro i s hs
    have h := norm_log_one_add_half_le_self ((hfb i s hs).trans (hb2 i))
    rw [add_sub_cancel] at h
    exact h.trans (mul_le_mul_of_nonneg_left (hfb i s hs) (by norm_num))
  have hne : ∀ i, ∀ s ∈ U, f i s ≠ 0 := by
    intro i s hs h0
    have := (hfb i s hs).trans (hb2 i)
    rw [h0, zero_sub, norm_neg, norm_one] at this
    linarith
  have hslit : ∀ i, ∀ s ∈ U, f i s ∈ slitPlane := by
    intro i s hs
    refine mem_slitPlane_iff.mpr (Or.inl ?_)
    have h1 := (hfb i s hs).trans (hb2 i)
    have h2 := Complex.abs_re_le_norm (f i s - 1)
    rw [sub_re, one_re] at h2
    linarith [abs_le.mp h2]
  have hb' : Summable fun i => 3 / 2 * b i := hb.mul_left _
  have hsum : ∀ s ∈ U, Summable fun i => Complex.log (f i s) := fun s hs =>
    hb'.of_norm_bounded fun i => hlog i s hs
  have heq : ∀ s ∈ U, ∏' i, f i s = cexp (∑' i, Complex.log (f i s)) := fun s hs =>
    (cexp_tsum_eq_tprod (fun i => hne i s hs) (hsum s hs)).symm
  refine ⟨?_, fun s hs => ⟨heq s hs, ?_⟩⟩
  · have hd : DifferentiableOn ℂ (fun s => ∑' i, Complex.log (f i s)) U :=
      differentiableOn_tsum_of_summable_norm hb'
        (fun i s hs => (hf i s hs).clog (hslit i s hs)) hU hlog
    exact hd.cexp.congr fun s hs => heq s hs
  · have hsn : Summable fun i => ‖Complex.log (f i s)‖ :=
      hb'.of_nonneg_of_le (fun _ => norm_nonneg _) fun i => hlog i s hs
    calc ‖∑' i, Complex.log (f i s)‖ ≤ ∑' i, ‖Complex.log (f i s)‖ := norm_tsum_le_tsum_norm hsn
      _ ≤ ∑' i, 3 / 2 * b i := Summable.tsum_le_tsum (fun i => hlog i s hs) hsn hb'
      _ = 3 / 2 * ∑' i, b i := tsum_mul_left

/-! ### The correction over a number field -/

section NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- The norm of a finite prime, as a real number. -/
abbrev primeNorm (v : HeightOneSpectrum (𝓞 K)) : ℝ := (v.asIdeal.absNorm : ℝ)

/-- The correction of the principal row: the product of the local factors over the primes outside
`S`, with phases `A` and character values `η`. -/
def principalCorrection (A η : HeightOneSpectrum (𝓞 K) → ℂ)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (s : ℂ) : ℂ :=
  ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S}, principalLocalFactor (primeNorm v.1) (A v) (η v) s

/-- The defect exponent `min(6σ − 3, 1 + σ, 2)`; it exceeds `1` for `σ > 2/3`. -/
def defectExponent (σ : ℝ) : ℝ := min (6 * σ - 3) (min (1 + σ) 2)

theorem one_lt_defectExponent {σ : ℝ} (hσ : 2 / 3 < σ) : 1 < defectExponent σ :=
  lt_min (by linarith) (lt_min (by linarith) (by norm_num))

/-- The summable majorant `14 N(v)^{−e}` of the local defects. -/
def defectWeight (e : ℝ) (v : HeightOneSpectrum (𝓞 K)) : ℝ := 14 * primeNorm v ^ (-e)

theorem defectWeight_nonneg (e : ℝ) (v : HeightOneSpectrum (𝓞 K)) : 0 ≤ defectWeight e v :=
  mul_nonneg (by norm_num) (Real.rpow_nonneg (by positivity) _)

/-- **The correction is close to `1`.** For `σ > 2/3` there is a norm `N₀` such that, whenever
`S` contains every prime of norm `≤ N₀`, the correction with any phases of modulus `≤ 1` is
holomorphic on `Re s > σ` and satisfies `‖H(s) − 1‖ ≤ 1/2` there. -/
theorem exists_principalCorrection_cutoff {σ : ℝ} (hσ : 2 / 3 < σ) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ (S : Finset (HeightOneSpectrum (𝓞 K))),
      (∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal.absNorm ≤ N₀ → v ∈ S) →
      ∀ A η : HeightOneSpectrum (𝓞 K) → ℂ, (∀ v, ‖A v‖ ≤ 1) → (∀ v, ‖η v‖ ≤ 1) →
        DifferentiableOn ℂ (principalCorrection A η S) {s : ℂ | σ < s.re} ∧
          ∀ s : ℂ, σ < s.re → ‖principalCorrection A η S s - 1‖ ≤ 1 / 2 := by
  have he1 : 1 < defectExponent σ := one_lt_defectExponent hσ
  have he6 : defectExponent σ ≤ 6 * σ - 3 := min_le_left _ _
  have heσ : defectExponent σ ≤ 1 + σ := (min_le_right _ _).trans (min_le_left _ _)
  have he2 : defectExponent σ ≤ 2 := (min_le_right _ _).trans (min_le_right _ _)
  have hB : Summable (defectWeight (K := K) (defectExponent σ)) :=
    (numberField_summable_finitePlace_absNorm_rpow (K := K) he1).mul_left 14
  -- primes outside a finite set `F` carry total defect `< 1/6`
  obtain ⟨F, hF⟩ := ((tendsto_order.1 (tendsto_tsum_compl_atTop_zero
    (defectWeight (K := K) (defectExponent σ)))).2 (1 / 6) (by norm_num)).exists
  refine ⟨max 4 (F.sup fun v => v.asIdeal.absNorm), le_max_left _ _, ?_⟩
  intro S hS A η hA hη
  have hbig : ∀ v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S}, 4 ≤ primeNorm v.1 ∧ v.1 ∉ F := by
    intro v
    have hv : max 4 (F.sup fun v => v.asIdeal.absNorm) < v.1.asIdeal.absNorm :=
      lt_of_not_ge fun h => v.2 (hS v.1 h)
    refine ⟨?_, fun hF' => ?_⟩
    · have : 4 < v.1.asIdeal.absNorm := (le_max_left _ _).trans_lt hv
      unfold primeNorm
      exact_mod_cast this.le
    · exact absurd ((Finset.le_sup (f := fun v => v.asIdeal.absNorm) hF').trans
        (le_max_right _ _)) (not_le.mpr hv)
  have hBT : Summable fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} =>
      defectWeight (defectExponent σ) v.1 := hB.comp_injective Subtype.val_injective
  have hsmall : ∑' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S},
      defectWeight (defectExponent σ) v.1 ≤ 1 / 6 := by
    have hi : Function.Injective fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} =>
        (⟨v.1, (hbig v).2⟩ : {v // v ∉ F}) := fun v w h =>
      Subtype.ext (congrArg (fun x : {v // v ∉ F} => x.1) h)
    have hBF : Summable fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ F} =>
        defectWeight (defectExponent σ) v.1 := hB.comp_injective Subtype.val_injective
    have h1 : ∑' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S}, defectWeight (defectExponent σ) v.1 ≤
        ∑' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ F}, defectWeight (defectExponent σ) v.1 :=
      Summable.tsum_le_tsum_of_inj (f := fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} =>
          defectWeight (defectExponent σ) v.1)
        (g := fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ F} => defectWeight (defectExponent σ) v.1)
        _ hi (fun _ _ => defectWeight_nonneg _ _) (fun _ => le_rfl) hBT hBF
    exact h1.trans hF.le
  have hhalf : ∀ v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S},
      defectWeight (defectExponent σ) v.1 ≤ 1 / 2 := fun v => by
    have := Summable.le_tsum hBT v fun w _ => defectWeight_nonneg _ w.1
    linarith
  have hU : IsOpen {s : ℂ | σ < s.re} := isOpen_lt continuous_const continuous_re
  obtain ⟨hdiff, hrep⟩ := hasProd_and_bounds_of_defect
    (f := fun (v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S}) s =>
      principalLocalFactor (primeNorm v.1) (A v.1) (η v.1) s)
    (b := fun v => defectWeight (defectExponent σ) v.1) hU hBT
    (fun v s hs => by
      have hs' : σ < s.re := hs
      obtain ⟨hD, hR⟩ := principalLocalFactor_denominators (s := s) (hbig v).1 (hA v.1) (hη v.1)
        (by linarith)
      exact (differentiableAt_principalLocalFactor (by linarith [(hbig v).1]) _ _ hD hR)
        |>.differentiableWithinAt)
    (fun v s hs => norm_principalLocalFactor_sub_one_le (hbig v).1 (hA v.1) (hη v.1)
      (le_of_lt hs) he1.le he6 heσ he2)
    hhalf
  refine ⟨hdiff, fun s hs => ?_⟩
  obtain ⟨hexp, hlog⟩ := hrep s hs
  have hexp' : principalCorrection A η S s = cexp (∑' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S},
      Complex.log (principalLocalFactor (primeNorm v.1) (A v.1) (η v.1) s)) := hexp
  have hz : ‖∑' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S},
      Complex.log (principalLocalFactor (primeNorm v.1) (A v.1) (η v.1) s)‖ ≤ 1 / 4 :=
    hlog.trans (by linarith)
  rw [hexp']
  calc _ ≤ 2 * ‖∑' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S},
        Complex.log (principalLocalFactor (primeNorm v.1) (A v.1) (η v.1) s)‖ :=
        Complex.norm_exp_sub_one_le (hz.trans (by norm_num))
    _ ≤ 1 / 2 := by linarith

/-- The deleted Euler factors `∏_{v ∈ S} (1 − ψ(v) N(v)^{−s})⁻¹`, which turn `1/L^S` into `1/L`. -/
def deletedEulerFactors (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (s : ℂ) : ℂ :=
  ∏ v ∈ S, (1 - heckeValue 𝔪 ψ v.asIdeal * (primeNorm v : ℂ) ^ (-s))⁻¹

theorem two_le_primeNorm (v : HeightOneSpectrum (𝓞 K)) : (2 : ℝ) ≤ primeNorm v := by
  unfold primeNorm
  exact_mod_cast ArtinMertens.two_le_absNorm_of_isPrime v.isPrime v.ne_bot

/-- The deleted term `ψ(v) N(v)^{−s}` has modulus `≤ N(v)^{−Re s}`. -/
theorem norm_deletedTerm_le (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪)
    (v : HeightOneSpectrum (𝓞 K)) (s : ℂ) :
    ‖heckeValue 𝔪 ψ v.asIdeal * (primeNorm v : ℂ) ^ (-s)‖ ≤ primeNorm v ^ (-s.re) := by
  have hv := two_le_primeNorm v
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith), neg_re]
  exact mul_le_of_le_one_left (Real.rpow_nonneg (by linarith) _) (norm_heckeValue_le_one 𝔪 ψ _)

/-- On `Re s > 0` no deleted factor has a pole. -/
theorem deletedTerm_denominator_ne_zero (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪)
    (v : HeightOneSpectrum (𝓞 K)) {s : ℂ} (hs : 0 < s.re) :
    1 - heckeValue 𝔪 ψ v.asIdeal * (primeNorm v : ℂ) ^ (-s) ≠ 0 := by
  have hv := two_le_primeNorm v
  have hlt : ‖heckeValue 𝔪 ψ v.asIdeal * (primeNorm v : ℂ) ^ (-s)‖ < 1 :=
    (norm_deletedTerm_le 𝔪 ψ v s).trans_lt
      (Real.rpow_lt_one_of_one_lt_of_neg (by linarith) (by linarith))
  intro h
  have := norm_sub_norm_le (1 : ℂ) (heckeValue 𝔪 ψ v.asIdeal * (primeNorm v : ℂ) ^ (-s))
  rw [h, norm_zero, norm_one] at this
  linarith

/-- On `Re s ≥ 2` each deleted factor is at most `4/3`. -/
theorem norm_deletedEulerFactor_le (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪)
    (v : HeightOneSpectrum (𝓞 K)) {s : ℂ} (hs : 2 ≤ s.re) :
    ‖(1 - heckeValue 𝔪 ψ v.asIdeal * (primeNorm v : ℂ) ^ (-s))⁻¹‖ ≤ 4 / 3 := by
  have hv := two_le_primeNorm v
  have hsmall : ‖heckeValue 𝔪 ψ v.asIdeal * (primeNorm v : ℂ) ^ (-s)‖ ≤ 1 / 4 := by
    refine (norm_deletedTerm_le 𝔪 ψ v s).trans ?_
    calc primeNorm v ^ (-s.re) ≤ primeNorm v ^ (-(2 : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      _ = (primeNorm v ^ 2)⁻¹ := by rw [Real.rpow_neg (by linarith)]; norm_cast
      _ ≤ 1 / 4 := by
          rw [inv_eq_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
  have hlow : 3 / 4 ≤ ‖1 - heckeValue 𝔪 ψ v.asIdeal * (primeNorm v : ℂ) ^ (-s)‖ := by
    have := norm_sub_norm_le (1 : ℂ) (heckeValue 𝔪 ψ v.asIdeal * (primeNorm v : ℂ) ^ (-s))
    rw [norm_one] at this
    linarith
  rw [norm_inv]
  calc _ ≤ (3 / 4 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hlow
    _ = 4 / 3 := by norm_num

/-- The deleted Euler factors are holomorphic on `Re s > 0`. -/
theorem differentiableOn_deletedEulerFactors (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    DifferentiableOn ℂ (deletedEulerFactors 𝔪 ψ S) {s : ℂ | 0 < s.re} := by
  unfold deletedEulerFactors
  refine DifferentiableOn.fun_finsetProd fun v _ s hs => ?_
  have hv := two_le_primeNorm v
  have hQ' : (primeNorm v : ℂ) ≠ 0 := ofReal_ne_zero.mpr (by linarith)
  exact (((differentiableAt_const 1).sub ((differentiableAt_id.neg.const_cpow
    (Or.inl hQ')).const_mul _)).inv (deletedTerm_denominator_ne_zero 𝔪 ψ v hs)).differentiableWithinAt

/-- The full correction of the character `ψ`: the principal correction with character values
`ψ(v)`, times the deleted Euler factors of `S`. -/
def fullPrincipalCorrection (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪)
    (A : HeightOneSpectrum (𝓞 K) → ℂ) (S : Finset (HeightOneSpectrum (𝓞 K))) (s : ℂ) : ℂ :=
  principalCorrection A (fun v => heckeValue 𝔪 ψ v.asIdeal) S s * deletedEulerFactors 𝔪 ψ S s

/-- **The corrections have the properties of the continuation step.** For `σ > 2/3` there is
`N₀` such that, for every `S` containing the primes of norm `≤ N₀`, every character `ψ` and all
phases of modulus `≤ 1`, the full correction is holomorphic and nonvanishing on `Re s > σ` and
bounded by `3/2 (4/3)^{|S|}` on `Re s ≥ 2`. -/
theorem exists_fullPrincipalCorrection_cutoff {σ : ℝ} (hσ : 2 / 3 < σ) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ (S : Finset (HeightOneSpectrum (𝓞 K))),
      (∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal.absNorm ≤ N₀ → v ∈ S) →
      ∀ (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪) (A : HeightOneSpectrum (𝓞 K) → ℂ),
        (∀ v, ‖A v‖ ≤ 1) →
        DifferentiableOn ℂ (fullPrincipalCorrection 𝔪 ψ A S) {s : ℂ | σ < s.re} ∧
          (∀ s : ℂ, σ < s.re → fullPrincipalCorrection 𝔪 ψ A S s ≠ 0) ∧
          ∀ s : ℂ, 2 ≤ s.re → ‖fullPrincipalCorrection 𝔪 ψ A S s‖ ≤ 3 / 2 * (4 / 3) ^ S.card := by
  have hσ' : 2 / 3 < min σ 1 := lt_min hσ (by norm_num)
  obtain ⟨N₀, hN₀, hcut⟩ := exists_principalCorrection_cutoff (K := K) hσ'
  refine ⟨N₀, hN₀, fun S hS 𝔪 ψ A hA => ?_⟩
  obtain ⟨hdiff, hclose⟩ := hcut S hS A (fun v => heckeValue 𝔪 ψ v.asIdeal) hA
    (fun v => norm_heckeValue_le_one 𝔪 ψ _)
  have hlow : ∀ s : ℂ, σ < s.re → min σ 1 < s.re := fun s hs =>
    lt_of_le_of_lt (min_le_left _ _) hs
  have hsub : {s : ℂ | σ < s.re} ⊆ {s : ℂ | 0 < s.re} := fun s hs => by
    have := hlow s hs
    simp only [Set.mem_setOf_eq]
    linarith
  refine ⟨(hdiff.mono fun s hs => hlow s hs).mul
      ((differentiableOn_deletedEulerFactors 𝔪 ψ S).mono hsub), fun s hs => ?_, fun s hs => ?_⟩
  · have hH : principalCorrection A (fun v => heckeValue 𝔪 ψ v.asIdeal) S s ≠ 0 := by
      intro h0
      have := hclose s (hlow s hs)
      rw [h0, zero_sub, norm_neg, norm_one] at this
      linarith
    refine mul_ne_zero hH (Finset.prod_ne_zero_iff.mpr fun v _ => inv_ne_zero ?_)
    exact deletedTerm_denominator_ne_zero 𝔪 ψ v (hsub hs)
  · have hs' : min σ 1 < s.re := lt_of_le_of_lt (min_le_right _ _) (by linarith)
    have hH : ‖principalCorrection A (fun v => heckeValue 𝔪 ψ v.asIdeal) S s‖ ≤ 3 / 2 := by
      have h1 := hclose s hs'
      have h2 := norm_sub_norm_le (principalCorrection A (fun v => heckeValue 𝔪 ψ v.asIdeal) S s) 1
      rw [norm_one] at h2
      linarith
    have hdel : ‖deletedEulerFactors 𝔪 ψ S s‖ ≤ (4 / 3) ^ S.card := by
      unfold deletedEulerFactors
      refine (Finset.norm_prod_le _ _).trans ?_
      calc ∏ v ∈ S, ‖(1 - heckeValue 𝔪 ψ v.asIdeal * (primeNorm v : ℂ) ^ (-s))⁻¹‖
          ≤ ∏ _v ∈ S, (4 / 3 : ℝ) :=
            Finset.prod_le_prod (fun _ _ => norm_nonneg _)
              fun v _ => norm_deletedEulerFactor_le 𝔪 ψ v hs
        _ = (4 / 3) ^ S.card := Finset.prod_const _
    unfold fullPrincipalCorrection
    rw [norm_mul]
    exact mul_le_mul hH hdel (norm_nonneg _) (by norm_num)

end NumberField

/-! ### The endpoint with the corrections -/

/-- **The native endpoint with the principal corrections.** Over `K = ℚ(ζ₃)`, for
`σ₀ ∈ (2/3, 1)` there is `N₀` with the following property. Let `S` contain the primes of norm
`≤ N₀` and let `A_η` be phases of modulus `≤ 1`. If, whenever every `L(s, η)` is zero-free in
`Re s > β` off `1`, each ray class character has a sum with a direct bound `Z^{a₁}` and a
comparison `Z^{a₂}` with the signal of `exp((s − c)²) H_η(s)/L(s, η)`, `H_η` the full principal
correction and `a₁, a₂ < β` common to all characters, then `zetaZeroAbscissa ≤ σ₀`. -/
theorem exists_cutoff_zetaZeroAbscissa_le_of_two_estimates {K : Type*} [Field K]
    [NumberField K] [IsCyclotomicExtension {3} ℚ K] {σ₀ : ℝ} (hσ₀ : σ₀ < 1)
    (hσ₀' : 2 / 3 < σ₀) :
    ∃ N₀ : ℕ, ∀ (S : Finset (HeightOneSpectrum (𝓞 K))),
      (∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal.absNorm ≤ N₀ → v ∈ S) →
      ∀ (c : ℝ) (A : (Σ 𝔫 : Modulus K, HeckeCharacter 𝔫) → HeightOneSpectrum (𝓞 K) → ℂ),
        (∀ η v, ‖A η v‖ ≤ 1) →
        (∀ β : ℝ, σ₀ < β → β ≤ 1 →
          (∀ (η : Σ 𝔫 : Modulus K, HeckeCharacter 𝔫) (ρ : ℂ), β < ρ.re → ρ ≠ 1 →
            heckeLFunction η.1 η.2 ρ ≠ 0) →
          ∃ a₁ a₂ : ℝ, a₁ < β ∧ a₂ < β ∧
            ∀ η : Σ 𝔫 : Modulus K, HeckeCharacter 𝔫,
              ∃ (J : ℝ → ℂ) (C Z₀ : ℝ), 1 ≤ Z₀ ∧
                (∀ Z : ℝ, Z₀ ≤ Z → ‖J Z‖ ≤ C * Z ^ a₁) ∧
                (∀ Z : ℝ, Z₀ ≤ Z →
                  ‖J Z - signal (fun s : ℂ => cexp ((s - c) ^ 2) *
                    fullPrincipalCorrection η.1 η.2 (A η) S s / heckeLFunction η.1 η.2 s) 2 Z‖ ≤
                      C * Z ^ a₂)) →
        zetaZeroAbscissa ≤ σ₀ := by
  obtain ⟨N₀, -, hN₀⟩ := exists_fullPrincipalCorrection_cutoff (K := K) hσ₀'
  refine ⟨N₀, fun S hS c A hA hstep => ?_⟩
  exact zetaZeroAbscissa_le_of_two_reciprocal_estimates hσ₀ c
    (fun η => fullPrincipalCorrection η.1 η.2 (A η) S)
    (fun η => (hN₀ S hS η.1 η.2 (A η) (hA η)).1)
    (fun η => (hN₀ S hS η.1 η.2 (A η) (hA η)).2.1)
    (fun η => ⟨_, (hN₀ S hS η.1 η.2 (A η) (hA η)).2.2⟩) hstep

end GaloisForLFunctions.FamilyContinuationTheory
