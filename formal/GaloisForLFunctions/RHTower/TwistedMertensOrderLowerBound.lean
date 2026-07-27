import GaloisForLFunctions.RHTower.TwistedMobiusOrderLowerBound
import GaloisForLFunctions.RHTower.HermitianMertensIntegrationLaw
import GaloisForLFunctions.RHTower.MobiusMertensEvenConvolutionOrderLaw

/-!
# The Mertens companion order law from below

Passing from a coefficient sequence to its partial sums divides the radial generating function by
`1 - z`.  On the ray `z = e^{-x}` this costs exactly one power of `x`, so a subpower bound of
exponent `α` on the Hermitian mixed convolution of the partial sums `M_χ` forces decay of the raw
twisted source at the *shifted* exponent `(α+1)/(2k) - 1`.

An `L`-zero at `ρ` therefore forbids every exponent below `2k(1 + Re ρ) - 1`, which is the lower
half of the companion law `(R15)`.  Its upper half is a different matter: it needs the classical
estimate `M_χ(N) = O(N^{Θ_χ + ε})`.
-/

open Complex Filter Finset
open scoped ArithmeticFunction.Moebius LSeries.notation

namespace RHTower

variable {N : ℕ} [NeZero N]

/-- Partial sums of a unit-bounded sequence grow at most linearly. -/
theorem norm_partialSumSeq_le {a : ℕ → ℂ} (ha : ∀ n, ‖a n‖ ≤ 1) (M : ℕ) :
    ‖partialSumSeq a M‖ ≤ (M : ℝ) + 1 := by
  rw [partialSumSeq]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ n ∈ Finset.range (M + 1), ‖a n‖ ≤ ∑ _n ∈ Finset.range (M + 1), (1 : ℝ) :=
        Finset.sum_le_sum fun n _ => ha n
    _ = (M : ℝ) + 1 := by simp

/-- The partial-sum source converges on the open ray. -/
theorem summable_norm_partialSumSeq_mul_pow {a : ℕ → ℂ} (ha : ∀ n, ‖a n‖ ≤ 1)
    {x : ℝ} (hx : 0 < x) :
    Summable fun M : ℕ => ‖partialSumSeq a M * ((Real.exp (-x) : ℝ) : ℂ) ^ M‖ := by
  have hr0 : (0 : ℝ) ≤ Real.exp (-x) := (Real.exp_pos _).le
  have hr1 : Real.exp (-x) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hgeo : Summable fun M : ℕ => (Real.exp (-x)) ^ M :=
    summable_geometric_of_lt_one hr0 hr1
  have hlin : Summable fun M : ℕ => (M : ℝ) ^ 1 * (Real.exp (-x)) ^ M :=
    summable_pow_mul_geometric_of_norm_lt_one 1 (by rwa [Real.norm_eq_abs, abs_of_nonneg hr0])
  have hsum : Summable fun M : ℕ => ((M : ℝ) + 1) * (Real.exp (-x)) ^ M := by
    have := hlin.add hgeo
    refine this.congr fun M => ?_
    ring
  refine Summable.of_nonneg_of_le (fun M => norm_nonneg _) (fun M => ?_) hsum
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
  exact mul_le_mul_of_nonneg_right (norm_partialSumSeq_le ha M) (by positivity)

/-- **The partial-sum generating function.**  Multiplying by `1 - q` undoes partial summation. -/
theorem tsum_partialSumSeq_mul_pow {a : ℕ → ℂ} {q : ℂ} (hq : ‖q‖ < 1)
    (ha : Summable fun M : ℕ => ‖a M * q ^ M‖) :
    (1 - q) * ∑' M : ℕ, partialSumSeq a M * q ^ M = ∑' M : ℕ, a M * q ^ M := by
  have hgeo : Summable fun M : ℕ => ‖q ^ M‖ := by
    simpa [norm_pow] using summable_geometric_of_lt_one (norm_nonneg q) hq
  have hcauchy := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm ha hgeo
  have hinner : ∀ M : ℕ,
      (∑ ij ∈ Finset.antidiagonal M, (a ij.1 * q ^ ij.1) * q ^ ij.2)
        = partialSumSeq a M * q ^ M := by
    intro M
    rw [partialSumSeq, Finset.sum_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_range] at hk
    have hk' : k + (M - k) = M := by omega
    rw [mul_assoc, ← pow_add, hk']
  rw [funext hinner] at hcauchy
  rw [tsum_geometric_of_norm_lt_one hq] at hcauchy
  have hne : (1 : ℂ) - q ≠ 0 := by
    intro h
    have : q = 1 := by linear_combination -h
    rw [this] at hq
    simp at hq
  rw [← hcauchy, mul_comm, mul_assoc, inv_mul_cancel₀ hne, mul_one]

omit [NeZero N] in
/-- **Decay transfer.**  A subpower bound on the Hermitian mixed convolution of the partial sums
gives decay of the raw twisted source at the exponent shifted down by one. -/
theorem twistedMobiusLaplaceDecay_of_mertensSubpower (χ : DirichletCharacter ℂ N)
    {k : ℕ} (hk : 0 < k) {α C : ℝ} (hα : 0 ≤ α) (hC : 0 ≤ C)
    (hupper : ∀ M : ℕ,
      (mixedAdditiveConvolutionPower (partialSumSeq (↗χ * ↗μ)) k M).re
        ≤ C * ((M : ℝ) + 1) ^ α) :
    TwistedMobiusLaplaceDecay χ (max ((α + 1) / (2 * (k : ℝ)) - 1) 0) := by
  have hcoeff : ∀ n : ℕ, ‖(↗χ * ↗μ) n‖ ≤ 1 := norm_twistedMobiusCoeff_le_one χ
  have hAbel : 0 ≤ mixedSubpowerAbelConstant α := mixedSubpowerAbelConstant_nonneg hα
  refine ⟨(C * mixedSubpowerAbelConstant α) ^ ((2 * (k : ℝ))⁻¹), 1,
    Real.rpow_nonneg (mul_nonneg hC hAbel) _, one_pos, ?_⟩
  intro x hx hx1
  set q : ℂ := ((Real.exp (-x) : ℝ) : ℂ) with hq
  have hr0 : (0 : ℝ) ≤ Real.exp (-x) := (Real.exp_pos _).le
  have hr1 : Real.exp (-x) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hqnorm : ‖q‖ < 1 := by
    rw [hq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
    exact hr1
  have hraw : Summable fun M : ℕ => ‖(↗χ * ↗μ) M * q ^ M‖ :=
    summable_norm_twistedCoeff_mul_pow χ hx
  -- Abel bound for the partial-sum source
  have hbound := norm_tsum_le_of_mixedAdditiveConvolutionPower_subpower
    hk hα hC hx hx1.le (summable_norm_partialSumSeq_mul_pow hcoeff hx) hupper
  -- undo partial summation
  have hid := tsum_partialSumSeq_mul_pow (a := ↗χ * ↗μ) hqnorm hraw
  have hfac : ‖∑' M : ℕ, (↗χ * ↗μ) M * q ^ M‖
      = ‖(1 : ℂ) - q‖ * ‖∑' M : ℕ, partialSumSeq (↗χ * ↗μ) M * q ^ M‖ := by
    rw [← hid, norm_mul]
  have honeq : ‖(1 : ℂ) - q‖ ≤ x := by
    have hreal : (1 : ℂ) - q = ((1 - Real.exp (-x) : ℝ) : ℂ) := by
      rw [hq]; push_cast; ring
    rw [hreal, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    have := Real.add_one_le_exp (-x)
    have hexp : Real.exp (-x) * Real.exp x = 1 := by
      rw [← Real.exp_add]; simp
    nlinarith [Real.add_one_le_exp x, hr0, Real.exp_pos x]
  -- assemble
  rw [twistedMobiusLaplaceTransform_eq_tsum_pow, ← hq, hfac]
  set K : ℝ := (C * mixedSubpowerAbelConstant α) ^ ((2 * (k : ℝ))⁻¹) with hK
  have hK0 : 0 ≤ K := Real.rpow_nonneg (mul_nonneg hC hAbel) _
  have hstep : ‖(1 : ℂ) - q‖ * ‖∑' M : ℕ, partialSumSeq (↗χ * ↗μ) M * q ^ M‖
      ≤ x * (K * (1 / x) ^ ((α + 1) / (2 * (k : ℝ)))) := by
    refine mul_le_mul honeq hbound (norm_nonneg _) hx.le
  refine hstep.trans ?_
  -- `x · x^{-b} = x^{-(b-1)} ≤ x^{-max (b-1) 0}` for `0 < x ≤ 1`
  set b : ℝ := (α + 1) / (2 * (k : ℝ)) with hb
  have hxinv : (1 / x) ^ b = x ^ (-b) := by
    rw [one_div, ← Real.rpow_neg_one x, ← Real.rpow_mul hx.le]
    congr 1
    ring
  have hxone : x = x ^ (1 : ℝ) := (Real.rpow_one x).symm
  have hcollect : x * (K * x ^ (-b)) = K * x ^ (-(b - 1)) := by
    rw [show (-(b - 1)) = 1 + -b by ring, Real.rpow_add hx, Real.rpow_one]
    ring
  rw [hxinv, hcollect]
  refine mul_le_mul_of_nonneg_left ?_ hK0
  refine Real.rpow_le_rpow_of_exponent_ge hx hx1.le ?_
  have : b - 1 ≤ max (b - 1) 0 := le_max_left _ _
  linarith

/-- **No Mertens subpower below the shifted zero abscissa.** -/
theorem not_mertensSubpower_of_LFunction_eq_zero {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1)
    {k : ℕ} (hk : 0 < k) {α C : ℝ} (hα : 0 ≤ α) (hC : 0 ≤ C)
    {ρ : ℂ} (hzero : DirichletCharacter.LFunction χ ρ = 0) (hpos : 0 < ρ.re)
    (hlt : (α + 1) / (2 * (k : ℝ)) - 1 < ρ.re) :
    ¬ (∀ M : ℕ,
      (mixedAdditiveConvolutionPower (partialSumSeq (↗χ * ↗μ)) k M).re
        ≤ C * ((M : ℝ) + 1) ^ α) := by
  intro hupper
  have hmax : max ((α + 1) / (2 * (k : ℝ)) - 1) 0 < ρ.re := max_lt hlt hpos
  exact not_twistedMobiusLaplaceDecay_of_LFunction_eq_zero hχ (le_max_right _ _) hmax hzero
    (twistedMobiusLaplaceDecay_of_mertensSubpower χ hk hα hC hupper)

/-- Polynomial domination of the Hermitian mixed convolution of the partial sums. -/
theorem norm_mixedAdditiveConvolutionPower_partialSumSeq_le_pow {a : ℕ → ℂ}
    (ha : ∀ n, ‖a n‖ ≤ 1) (j M : ℕ) :
    ‖mixedAdditiveConvolutionPower (partialSumSeq a) (j + 1) M‖
      ≤ ((M : ℝ) + 1) ^ (4 * j + 3) := by
  have hlin : ∀ n : ℕ, ‖partialSumSeq a n‖ ≤ 1 * ((n : ℝ) + 1) ^ (1 : ℝ) := by
    intro n
    rw [one_mul, Real.rpow_one]
    exact norm_partialSumSeq_le ha n
  have hconv : ∀ n : ℕ, ‖additiveConvolutionPower (partialSumSeq a) (j + 1) n‖
      ≤ ((n : ℝ) + 1) ^ ((2 * j + 1 : ℕ) : ℝ) := by
    intro n
    have h := norm_additiveConvolutionPower_succ_le (partialSumSeq a) (A := 1) (α := 1)
      zero_le_one zero_le_one hlin j n
    refine h.trans (le_of_eq ?_)
    rw [one_pow, one_mul]
    congr 1
    push_cast
    ring
  show ‖∑ ab ∈ Finset.antidiagonal M, additiveConvolutionPower (partialSumSeq a) (j + 1) ab.1 *
    (starRingEnd ℂ) (additiveConvolutionPower (partialSumSeq a) (j + 1) ab.2)‖ ≤ _
  refine (norm_sum_le _ _).trans ?_
  have hstep : ∀ ab ∈ Finset.antidiagonal M,
      ‖additiveConvolutionPower (partialSumSeq a) (j + 1) ab.1 *
          (starRingEnd ℂ) (additiveConvolutionPower (partialSumSeq a) (j + 1) ab.2)‖
        ≤ ((M : ℝ) + 1) ^ ((4 * j + 2 : ℕ) : ℝ) := by
    intro ab hab
    rw [Finset.mem_antidiagonal] at hab
    rw [norm_mul, RCLike.norm_conj]
    have hb1 : ((ab.1 : ℝ) + 1) ^ ((2 * j + 1 : ℕ) : ℝ) ≤ ((M : ℝ) + 1) ^ ((2 * j + 1 : ℕ) : ℝ) := by
      refine Real.rpow_le_rpow (by positivity) ?_ (by positivity)
      have h : (ab.1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast (by omega : ab.1 ≤ M)
      linarith
    have hb2 : ((ab.2 : ℝ) + 1) ^ ((2 * j + 1 : ℕ) : ℝ) ≤ ((M : ℝ) + 1) ^ ((2 * j + 1 : ℕ) : ℝ) := by
      refine Real.rpow_le_rpow (by positivity) ?_ (by positivity)
      have h : (ab.2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast (by omega : ab.2 ≤ M)
      linarith
    calc ‖additiveConvolutionPower (partialSumSeq a) (j + 1) ab.1‖ *
          ‖additiveConvolutionPower (partialSumSeq a) (j + 1) ab.2‖
        ≤ ((M : ℝ) + 1) ^ ((2 * j + 1 : ℕ) : ℝ) * ((M : ℝ) + 1) ^ ((2 * j + 1 : ℕ) : ℝ) :=
          mul_le_mul ((hconv ab.1).trans hb1) ((hconv ab.2).trans hb2) (norm_nonneg _)
            (by positivity)
      _ = ((M : ℝ) + 1) ^ ((4 * j + 2 : ℕ) : ℝ) := by
          rw [← Real.rpow_add (by positivity)]
          congr 1
          push_cast
          ring
  refine (Finset.sum_le_sum hstep).trans ?_
  rw [Finset.sum_const, Finset.Nat.card_antidiagonal, nsmul_eq_mul]
  have hcast : ((M + 1 : ℕ) : ℝ) = (M : ℝ) + 1 := by push_cast; ring
  rw [hcast, show ((M : ℝ) + 1) ^ (4 * j + 3) = ((M : ℝ) + 1) * ((M : ℝ) + 1) ^ (4 * j + 2) by ring]
  refine mul_le_mul_of_nonneg_left (le_of_eq ?_) (by positivity)
  rw [← Real.rpow_natCast ((M : ℝ) + 1) (4 * j + 2)]

/-- **The companion order law `(R15)` from below.**  An `L`-zero at `ρ` forces the logarithmic
order exponent of the Hermitian mixed convolution of the partial sums to be at least
`2k(1 + Re ρ) - 1`. -/
theorem two_mul_one_add_re_sub_one_le_limsup_mertens
    {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) {j : ℕ} {ρ : ℂ}
    (hzero : DirichletCharacter.LFunction χ ρ = 0) (hpos : 0 < ρ.re) :
    2 * ((j : ℝ) + 1) * (1 + ρ.re) - 1 ≤ Filter.limsup
      (fun M => Real.log
          (1 + max (mixedAdditiveConvolutionPower (partialSumSeq (↗χ * ↗μ)) (j + 1) M).re 0)
        / Real.log ((M : ℝ) + 1)) atTop := by
  have hcoeff : ∀ n : ℕ, ‖(↗χ * ↗μ) n‖ ≤ 1 := norm_twistedMobiusCoeff_le_one χ
  refine le_limsup_of_no_subpower_below (D := 4 * j + 3) (fun M => ?_) fun α C hα hC hlt => ?_
  · exact (Complex.re_le_norm _).trans
      (norm_mixedAdditiveConvolutionPower_partialSumSeq_le_pow hcoeff j M)
  · have hkR : (0 : ℝ) < 2 * (((j + 1 : ℕ) : ℝ)) := by
      have : (0 : ℝ) < ((j + 1 : ℕ) : ℝ) := by positivity
      linarith
    have hshift : (α + 1) / (2 * (((j + 1 : ℕ) : ℝ))) - 1 < ρ.re := by
      rw [sub_lt_iff_lt_add, div_lt_iff₀ hkR]
      push_cast at hlt ⊢
      nlinarith [hlt]
    exact not_mertensSubpower_of_LFunction_eq_zero hχ (Nat.succ_pos j) hα hC hzero hpos hshift

/-- **`(R15)` from below at the critical line.**  For a nontrivial primitive character the
companion exponent is at least `2k(1 + 1/2) - 1 = 3k - 1`. -/
theorem three_mul_sub_one_le_limsup_mertens
    {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) {j : ℕ} :
    3 * ((j : ℝ) + 1) - 1 ≤ Filter.limsup
      (fun M => Real.log
          (1 + max (mixedAdditiveConvolutionPower (partialSumSeq (↗χ * ↗μ)) (j + 1) M).re 0)
        / Real.log ((M : ℝ) + 1)) atTop := by
  obtain ⟨ρ, hρre, hzero⟩ := exists_LFunction_eq_zero_half_le_re hχ hprim
  have hpos : 0 < ρ.re := by linarith
  refine le_trans ?_ (two_mul_one_add_re_sub_one_le_limsup_mertens hχ (j := j) hzero hpos)
  have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  nlinarith [hρre, hj]

end RHTower
