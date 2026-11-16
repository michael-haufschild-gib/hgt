import GaloisForLFunctions.SpectralTheoryOfTheCubicCover.TheUntwistedSquarefreeSeriesIsHolomorphicInitially
import GaloisForLFunctions.SpectralTheoryOfTheCubicCover.TheUntwistedSquarefreeThetaSeriesHasASimplePole
import Mathlib.NumberTheory.LSeries.SumCoeff

/-!
# A remainder for the squarefree theta squares reads the zeros of `ζ_K`

The untwisted squarefree theta-square series `S₁(w) = Σ σ(A) N(A)^{−w}` (squarefree `A` prime to `3`, `σ` the
theta-square weight; the row root numbers up to their conductor phase) is the quotient of the completed
unramified theta square `Λ₀` by the cube zeta factor (SpectralTheoryOfTheCubicCover):

`(s − 4/3) Λ₀(s) = 2 B^{−s} \overline{C}² (2/3) Z̃(s) M(s) S₁(s/2)`,  `Z̃(s) = (1 − 3^{−z}) (z − 1) ζ(z) L(z, χ₋₃)`,
`z = 3s/2 − 1`.

So a zero `ρ` of `ζ_K = ζ · L(·, χ₋₃)` is a zero of `Z̃` at `s = 2(1 + ρ)/3`, i.e. `w = (1 + ρ)/3`. Suppose the
partial sums have a power remainder,

`Σ_{N(A) ≤ t} σ(A) = c t^{2/3} + O(t^β)`.

Abel summation (`twistedSquarefreeSeries_one_eq_remainder`) writes `S₁(w) = w (c/(w − 2/3) + J(w))` with `J` the
Mellin transform of the remainder, holomorphic on `Re w > β`. The identity above then continues to
`max(1, 2β) < Re s < 13/3`, `Im s > 0`, and its right side vanishes at `2(1 + ρ)/3`:

* `remainder_forces_thetaSquare_zero`: **every zero `ρ` of `ζ_K` with `Re ρ > max(½, 3β − 1)`, `Im ρ > 0` is a
  zero of `Λ₀` at `2(1 + ρ)/3`**;
* `sqrtRemainder_forces_thetaSquare_zero`: a square-root remainder `O(t^{1/2+ε})` for every `ε` forces every
  zero of `ζ_K` right of the critical line (upper half-plane) onto the zero set of `s ↦ Λ₀(2(1 + s)/3)`;
* `remainderExponent_ge`: a zero `ρ` with `Λ₀(2(1 + ρ)/3) ≠ 0` bounds every remainder exponent below by
  `(1 + Re ρ)/3`.

The remainder of the squarefree first moment is the zero-free region of `ζ_K` read at `3w − 1`: below
`(1 + Θ)/3` it can only be reached through coincident zeros of the theta square.
-/

noncomputable section

open MeasureTheory Filter Topology Asymptotics Set
open scoped BigOperators Classical

namespace GaloisForLFunctions.OrderSixMetaplecticTheory

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicEisenstein
  SpectralTheoryOfTheCubicCover FamilyContinuationTheory FamilyContinuationTheory.EisensteinNorm

/-! ### The coefficients by norm -/

/-- The coefficient of `n^{−w}`: `Σ_{N(A) = n} σ(A)` over squarefree ideals prime to `3`. -/
def thetaNormCoeff (n : ℕ) : ℂ :=
  ∑' A : {A : Ideal O // Ideal.absNorm A = n}, untwistedSquarefreeCoefficient A

/-- The partial sums `Σ_{N(A) ≤ t} σ(A)`. -/
def squarefreeThetaSum (t : ℝ) : ℂ := ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, thetaNormCoeff k

/-- Ideals sorted by their norm. -/
abbrev normFibre : (Σ n : ℕ, {A : Ideal O // Ideal.absNorm A = n}) ≃ Ideal O :=
  Equiv.sigmaFiberEquiv (fun A : Ideal O => Ideal.absNorm A)

theorem unramifiedNormWeight_mul_coeff (w : ℂ) (A : Ideal O) :
    unramifiedNormWeight w A * untwistedSquarefreeCoefficient A =
      untwistedSquarefreeCoefficient A * ((Ideal.absNorm A : ℕ) : ℂ) ^ (-w) := by
  by_cases hA : primaryIdealGenerator A = 0
  · rw [unramifiedNormWeight_of_bad w A hA, untwistedSquarefreeCoefficient_of_bad A hA, zero_mul,
      zero_mul]
  · rw [unramifiedNormWeight_of_good w A hA, mul_comm]

/-- The summand `σ(A) N(A)^{−w}`. -/
abbrev thetaTerm (w : ℂ) (A : Ideal O) : ℂ :=
  untwistedSquarefreeCoefficient A * ((Ideal.absNorm A : ℕ) : ℂ) ^ (-w)

theorem thetaTerm_summable_norm (w : ℂ) (hw : 1 < w.re) : Summable (fun A => ‖thetaTerm w A‖) := by
  simpa only [thetaTerm, unramifiedNormWeight_mul_coeff] using untwistedSquarefreeSeries_summable_norm w hw

theorem thetaTerm_fibre (w : ℂ) (n : ℕ) (A : {A : Ideal O // Ideal.absNorm A = n}) :
    thetaTerm w (normFibre ⟨n, A⟩) = untwistedSquarefreeCoefficient A * (n : ℂ) ^ (-w) := by
  simp only [thetaTerm, normFibre, Equiv.sigmaFiberEquiv_apply, A.2]

theorem fibre_tsum (w : ℂ) (n : ℕ) :
    ∑' A : {A : Ideal O // Ideal.absNorm A = n}, thetaTerm w (normFibre ⟨n, A⟩) =
      thetaNormCoeff n * (n : ℂ) ^ (-w) := by
  rw [tsum_congr (thetaTerm_fibre w n), tsum_mul_right, thetaNormCoeff]

theorem term_eq (w : ℂ) (hw : 1 < w.re) (n : ℕ) :
    LSeries.term thetaNormCoeff w n = thetaNormCoeff n * (n : ℂ) ^ (-w) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · have hw0 : -w ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      simp only [Complex.neg_re, Complex.zero_re] at this
      linarith
    subst hn
    rw [LSeries.term_zero, Nat.cast_zero, Complex.zero_cpow hw0, mul_zero]
  · rw [LSeries.term_of_ne_zero hn.ne', Complex.cpow_neg, div_eq_mul_inv]

/-- **`S₁` as an `L`-series by norms.** For `Re w > 1`, `S₁(w) = Σ_n (Σ_{N(A) = n} σ(A)) n^{−w}`. -/
theorem twistedSquarefreeSeries_one_eq_LSeries (w : ℂ) (hw : 1 < w.re) :
    twistedSquarefreeSeries 1 w = LSeries thetaNormCoeff w := by
  have hg : Summable (thetaTerm w) := (thetaTerm_summable_norm w hw).of_norm
  have hs : Summable (thetaTerm w ∘ normFibre) := normFibre.summable_iff.mpr hg
  have h1 : twistedSquarefreeSeries 1 w = ∑' A, thetaTerm w A := by
    rw [twistedSquarefreeSeries_one_eq]
    exact tsum_congr fun A => unramifiedNormWeight_mul_coeff w A
  have h2 : ∑' c, thetaTerm w (normFibre c) =
      ∑' n, ∑' A : {A : Ideal O // Ideal.absNorm A = n}, thetaTerm w (normFibre ⟨n, A⟩) :=
    hs.tsum_sigma
  rw [h1, ← normFibre.tsum_eq (thetaTerm w), h2]
  refine tsum_congr fun n => ?_
  rw [term_eq w hw n, ← fibre_tsum]

theorem thetaNormCoeff_LSeriesSummable (w : ℂ) (hw : 1 < w.re) : LSeriesSummable thetaNormCoeff w := by
  have hs : Summable ((fun A => ‖thetaTerm w A‖) ∘ normFibre) :=
    normFibre.summable_iff.mpr (thetaTerm_summable_norm w hw)
  have hsig := (summable_sigma_of_nonneg (fun p => norm_nonneg _)).mp hs
  refine Summable.of_norm_bounded hsig.2 (fun n => ?_)
  rw [term_eq w hw n, ← fibre_tsum]
  exact norm_tsum_le_tsum_norm (hsig.1 n)

/-! ### Abel summation -/

/-- The remainder `E(t) = Σ_{N(A) ≤ t} σ(A) − c t^{2/3}` on `t > 1`, zero on `t ≤ 1`. -/
def thetaRemainder (c : ℂ) (t : ℝ) : ℂ :=
  (Ioi (1 : ℝ)).indicator (fun t => squarefreeThetaSum t - c * ((t ^ (2 / 3 : ℝ) : ℝ) : ℂ)) t

/-- The Mellin transform `J(w) = ∫_1^∞ E(t) t^{−w−1} dt` of the remainder. -/
def remainderMellin (c : ℂ) (w : ℂ) : ℂ := mellin (thetaRemainder c) (-w)

theorem squarefreeThetaSum_measurable : Measurable squarefreeThetaSum := by
  have h : squarefreeThetaSum = (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, thetaNormCoeff k) ∘ Nat.floor := rfl
  rw [h]
  exact measurable_from_nat.comp Nat.measurable_floor

theorem thetaRemainder_measurable (c : ℂ) : Measurable (thetaRemainder c) := by
  refine Measurable.indicator ?_ measurableSet_Ioi
  exact squarefreeThetaSum_measurable.sub (measurable_const.mul
    (Complex.measurable_ofReal.comp (Real.continuous_rpow_const (by norm_num)).measurable))

section Remainder

variable {c : ℂ} {β K : ℝ} (hβ : 0 ≤ β)
  (hE : ∀ t : ℝ, 1 ≤ t → ‖squarefreeThetaSum t - c * ((t ^ (2 / 3 : ℝ) : ℝ) : ℂ)‖ ≤ K * t ^ β)
include hE

theorem K_nonneg : 0 ≤ K := by
  have h := hE 1 le_rfl
  simp only [Real.one_rpow, mul_one] at h
  exact (norm_nonneg _).trans h

include hβ in
theorem norm_thetaRemainder_le (t : ℝ) : ‖thetaRemainder c t‖ ≤ K * (1 + |t|) ^ β := by
  have hK := K_nonneg hE
  unfold thetaRemainder
  by_cases ht : t ∈ Ioi (1 : ℝ)
  · rw [indicator_of_mem ht]
    have ht1 : (1 : ℝ) < t := ht
    refine (hE t ht1.le).trans (mul_le_mul_of_nonneg_left ?_ hK)
    exact Real.rpow_le_rpow (by linarith) (by rw [abs_of_pos (by linarith)]; linarith) hβ
  · rw [indicator_of_notMem ht, norm_zero]
    positivity

include hβ in
theorem thetaRemainder_locallyIntegrableOn : LocallyIntegrableOn (thetaRemainder c) (Ioi 0) := by
  have hφ : Continuous (fun t : ℝ => K * (1 + |t|) ^ β) :=
    continuous_const.mul ((continuous_const.add continuous_abs).rpow_const fun _ => Or.inr hβ)
  refine (hφ.continuousOn.locallyIntegrableOn measurableSet_Ioi).mono
    (thetaRemainder_measurable c).aestronglyMeasurable (Eventually.of_forall fun t => ?_)
  rw [Real.norm_of_nonneg (by have := K_nonneg hE; positivity)]
  exact norm_thetaRemainder_le hβ hE t

include hβ in
/-- **The remainder transform is holomorphic on `Re w > β`.** -/
theorem remainderMellin_differentiableAt (w : ℂ) (hw : β < w.re) :
    DifferentiableAt ℂ (remainderMellin c) w := by
  have hm : DifferentiableAt ℂ (mellin (thetaRemainder c)) (-w) := by
    refine mellin_differentiableAt_of_isBigO_rpow (a := -β) (b := -w.re - 1)
      (thetaRemainder_locallyIntegrableOn hβ hE) ?_ (by simp; linarith) ?_ (by simp)
    · refine IsBigO.of_bound K ?_
      filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
      rw [neg_neg, Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _)]
      unfold thetaRemainder
      rw [indicator_of_mem (show t ∈ Ioi (1 : ℝ) from ht)]
      exact hE t ht.le
    · refine IsBigO.of_bound 0 ?_
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
      unfold thetaRemainder
      rw [indicator_of_notMem (show t ∉ Ioi (1 : ℝ) from fun h => absurd ht.2 (not_lt.mpr (le_of_lt h))),
        norm_zero, zero_mul]
  exact hm.comp w differentiableAt_id.neg

theorem partialSums_isBigO (hβ1 : β ≤ 2 / 3) :
    (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, thetaNormCoeff k) =O[atTop] fun n : ℕ => (n : ℝ) ^ (2 / 3 : ℝ) := by
  refine IsBigO.of_bound (‖c‖ + K) ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hS : squarefreeThetaSum n = ∑ k ∈ Finset.Icc 1 n, thetaNormCoeff k := by
    rw [squarefreeThetaSum, Nat.floor_natCast]
  have h := hE n hn1
  rw [hS] at h
  have hp : (0 : ℝ) ≤ (n : ℝ) ^ (2 / 3 : ℝ) := Real.rpow_nonneg (by linarith) _
  have hβp : (n : ℝ) ^ β ≤ (n : ℝ) ^ (2 / 3 : ℝ) := Real.rpow_le_rpow_of_exponent_le hn1 hβ1
  rw [Real.norm_of_nonneg hp]
  calc ‖∑ k ∈ Finset.Icc 1 n, thetaNormCoeff k‖
      ≤ ‖c * (((n : ℝ) ^ (2 / 3 : ℝ) : ℝ) : ℂ)‖ +
          ‖∑ k ∈ Finset.Icc 1 n, thetaNormCoeff k - c * (((n : ℝ) ^ (2 / 3 : ℝ) : ℝ) : ℂ)‖ :=
        norm_le_insert' _ _
    _ ≤ ‖c‖ * (n : ℝ) ^ (2 / 3 : ℝ) + K * (n : ℝ) ^ (2 / 3 : ℝ) := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hp]
        gcongr
        exact h.trans (mul_le_mul_of_nonneg_left hβp (K_nonneg hE))
    _ = (‖c‖ + K) * (n : ℝ) ^ (2 / 3 : ℝ) := by ring

omit hE in
theorem integral_mainTerm (w : ℂ) (hw : 2 / 3 < w.re) :
    ∫ t in Ioi (1 : ℝ), c * (((t ^ (2 / 3 : ℝ) : ℝ) : ℂ)) * (t : ℂ) ^ (-(w + 1)) = c / (w - 2 / 3) := by
  have hpt : ∀ t ∈ Ioi (1 : ℝ), c * (((t ^ (2 / 3 : ℝ) : ℝ) : ℂ)) * (t : ℂ) ^ (-(w + 1)) =
      c * (t : ℂ) ^ ((2 / 3 : ℂ) - (w + 1)) := by
    intro t (ht : 1 < t)
    have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
    rw [Complex.ofReal_cpow (by linarith), mul_assoc, ← Complex.cpow_add _ _ ht0]
    congr 2
    push_cast
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul,
    integral_Ioi_cpow_of_lt (by simp; linarith) one_pos]
  have hne : w - 2 / 3 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hne' : (2 / 3 : ℂ) - (w + 1) + 1 ≠ 0 := by
    intro h
    apply hne
    linear_combination -h
  rw [Complex.ofReal_one, Complex.one_cpow, show (2 / 3 : ℂ) - (w + 1) + 1 = -(w - 2 / 3) by ring,
    neg_div_neg_eq, mul_one_div]

omit hE in
theorem integrableOn_mainTerm (w : ℂ) (hw : 2 / 3 < w.re) :
    IntegrableOn (fun t : ℝ => c * (((t ^ (2 / 3 : ℝ) : ℝ) : ℂ)) * (t : ℂ) ^ (-(w + 1))) (Ioi 1) := by
  have hpt : EqOn (fun t : ℝ => c * (t : ℂ) ^ ((2 / 3 : ℂ) - (w + 1)))
      (fun t : ℝ => c * (((t ^ (2 / 3 : ℝ) : ℝ) : ℂ)) * (t : ℂ) ^ (-(w + 1))) (Ioi 1) := by
    intro t (ht : 1 < t)
    have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
    simp only
    rw [Complex.ofReal_cpow (by linarith), mul_assoc, ← Complex.cpow_add _ _ ht0]
    congr 2
    push_cast
    ring
  refine IntegrableOn.congr_fun ?_ hpt measurableSet_Ioi
  exact (integrableOn_Ioi_cpow_of_lt (by simp; linarith) one_pos).const_mul c

theorem integrableOn_remainderTerm (w : ℂ) (hw : β < w.re) :
    IntegrableOn (fun t : ℝ => (squarefreeThetaSum t - c * (((t ^ (2 / 3 : ℝ) : ℝ) : ℂ))) *
      (t : ℂ) ^ (-(w + 1))) (Ioi 1) := by
  have hg : IntegrableOn (fun t : ℝ => K * t ^ (β - w.re - 1)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) one_pos).const_mul K
  refine hg.mono' ?_ ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_))
  · refine (Measurable.mul (squarefreeThetaSum_measurable.sub (measurable_const.mul
      (Complex.measurable_ofReal.comp (Real.continuous_rpow_const (by norm_num)).measurable))) ?_).aestronglyMeasurable
    exact (Complex.continuous_ofReal.measurable.pow_const _)
  · have ht1 : (1 : ℝ) < t := ht
    have ht0 : (0 : ℝ) < t := by linarith
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0]
    have hre : (-(w + 1)).re = -w.re - 1 := by
      simp only [Complex.neg_re, Complex.add_re, Complex.one_re]
      ring
    rw [hre]
    calc ‖squarefreeThetaSum t - c * (((t ^ (2 / 3 : ℝ) : ℝ) : ℂ))‖ * t ^ (-w.re - 1)
        ≤ K * t ^ β * t ^ (-w.re - 1) := by gcongr; exact hE t ht1.le
      _ = K * t ^ (β - w.re - 1) := by
        rw [mul_assoc, ← Real.rpow_add ht0]
        congr 2
        ring

omit hE in
theorem remainderMellin_eq (w : ℂ) :
    remainderMellin c w = ∫ t in Ioi (1 : ℝ),
      (squarefreeThetaSum t - c * (((t ^ (2 / 3 : ℝ) : ℝ) : ℂ))) * (t : ℂ) ^ (-(w + 1)) := by
  rw [remainderMellin, mellin]
  have hpt : ∀ t : ℝ, (t : ℂ) ^ (-w - 1) • thetaRemainder c t = (Ioi (1 : ℝ)).indicator
      (fun t => (squarefreeThetaSum t - c * (((t ^ (2 / 3 : ℝ) : ℝ) : ℂ))) * (t : ℂ) ^ (-(w + 1))) t := by
    intro t
    unfold thetaRemainder
    by_cases ht : t ∈ Ioi (1 : ℝ)
    · rw [indicator_of_mem ht, indicator_of_mem ht, smul_eq_mul, mul_comm, show -w - 1 = -(w + 1) by ring]
    · rw [indicator_of_notMem ht, indicator_of_notMem ht, smul_zero]
  simp_rw [hpt]
  rw [setIntegral_indicator measurableSet_Ioi, Ioi_inter_Ioi, show (0 : ℝ) ⊔ 1 = 1 by norm_num]

/-- **Abel summation.** For `Re w > 1` and `β ≤ 2/3`: `S₁(w) = w (c/(w − 2/3) + J(w))`. -/
theorem twistedSquarefreeSeries_one_eq_remainder (hβ1 : β ≤ 2 / 3) (w : ℂ) (hw : 1 < w.re) :
    twistedSquarefreeSeries 1 w = w * (c / (w - 2 / 3) + remainderMellin c w) := by
  rw [twistedSquarefreeSeries_one_eq_LSeries w hw,
    LSeries_eq_mul_integral _ (by norm_num : (0 : ℝ) ≤ 2 / 3) (by linarith)
      (thetaNormCoeff_LSeriesSummable w hw) (partialSums_isBigO hE hβ1)]
  congr 1
  have hsplit : ∀ t : ℝ, (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, thetaNormCoeff k) * (t : ℂ) ^ (-(w + 1)) =
      c * (((t ^ (2 / 3 : ℝ) : ℝ) : ℂ)) * (t : ℂ) ^ (-(w + 1)) +
        (squarefreeThetaSum t - c * (((t ^ (2 / 3 : ℝ) : ℝ) : ℂ))) * (t : ℂ) ^ (-(w + 1)) := by
    intro t
    rw [squarefreeThetaSum]
    ring
  simp_rw [hsplit]
  rw [integral_add (integrableOn_mainTerm w (by linarith))
    (integrableOn_remainderTerm hE w (by linarith)), integral_mainTerm w (by linarith),
    remainderMellin_eq]

end Remainder

/-! ### The zeros of the cube zeta factor -/

/-- The region `max(1, 2β) < Re s < 13/3`, `Im s > 0`. -/
def thetaRegion (β : ℝ) : Set ℂ :=
  {s : ℂ | max 1 (2 * β) < s.re} ∩ ({s : ℂ | s.re < 13 / 3} ∩ {s : ℂ | 0 < s.im})

theorem thetaRegion_isOpen (β : ℝ) : IsOpen (thetaRegion β) :=
  (isOpen_lt continuous_const Complex.continuous_re).inter
    ((isOpen_lt Complex.continuous_re continuous_const).inter (isOpen_lt continuous_const Complex.continuous_im))

theorem thetaRegion_convex (β : ℝ) : Convex ℝ (thetaRegion β) :=
  (convex_halfSpace_re_gt _).inter ((convex_halfSpace_re_lt _).inter (convex_halfSpace_im_gt _))

/-- `Z̃` vanishes at `2(1 + ρ)/3` for every zero `ρ ≠ 1` of `ζ · L(·, χ₋₃)`. -/
theorem clearedCubeZeta_eq_zero {ρ : ℂ} (hρ : riemannZeta ρ = 0 ∨ DirichletCharacter.LFunction chi3D ρ = 0)
    (hρ1 : ρ ≠ 1) : clearedCubeZeta (2 * (1 + ρ) / 3) = 0 := by
  have hz : 3 * (2 * (1 + ρ) / 3 / 2) - 1 = ρ := by ring
  unfold clearedCubeZeta
  rw [hz]
  rcases hρ with h | h
  · rw [_root_.RHTower.zetaPoleFilled_of_ne hρ1, h]
    ring
  · rw [h]
    ring

/-- Zeros of `ζ · L(·, χ₋₃)` lie left of `Re = 1`. -/
theorem re_lt_one_of_zero {ρ : ℂ} (hρ : riemannZeta ρ = 0 ∨ DirichletCharacter.LFunction chi3D ρ = 0) :
    ρ.re < 1 := by
  by_contra h
  push Not at h
  rcases hρ with hz | hz
  · exact riemannZeta_ne_zero_of_one_le_re h hz
  · exact DirichletCharacter.LFunction_ne_zero_of_one_le_re chi3D (Or.inl chi3D_ne_one) h hz

/-- **The core.** If `S₁` agrees on `Re w > 2` with a function `F` holomorphic on `Re w > β`, `w ≠ 2/3`, then
every zero `ρ` of `ζ · L(·, χ₋₃)` with `Re ρ > 1/2`, `Re ρ > 3β − 1`, `Im ρ > 0` is a zero of the completed
unramified theta square at `2(1 + ρ)/3`: the identity `(s − 4/3)Λ₀(s) = 2B^{−s}C̄²(2/3)Z̃(s)M(s)F(s/2)` continues
to `max(1, 2β) < Re s < 13/3`, `Im s > 0`, and its right side vanishes there. -/
theorem thetaSquare_zero_of_extension (F : ℂ → ℂ) {β : ℝ}
    (hFd : ∀ w : ℂ, β < w.re → w ≠ 2 / 3 → DifferentiableAt ℂ F w)
    (hFS : ∀ w : ℂ, 2 < w.re → twistedSquarefreeSeries 1 w = F w)
    {ρ : ℂ} (hρ : riemannZeta ρ = 0 ∨ DirichletCharacter.LFunction chi3D ρ = 0)
    (hρ1 : 1 / 2 < ρ.re) (hρβ : 3 * β - 1 < ρ.re) (hρi : 0 < ρ.im) :
    completedUnramified (2 * (1 + ρ) / 3) = 0 := by
  have hρlt := re_lt_one_of_zero hρ
  have hβ23 : β < 2 / 3 := by linarith
  set den : ℂ → ℂ := fun s => 2 * unitFrequencyWeight s * star rationalSourceThetaScalar ^ 2 * (2 / 3) *
    clearedCubeZeta s with hden
  set g : ℂ → ℂ := fun s => (s - 4 / 3) * completedUnramified s - den s * (besselSqMellin s * F (s / 2))
    with hg
  have hgd : DifferentiableOn ℂ g (thetaRegion β) := by
    intro s hs
    obtain ⟨h1, h2, h3⟩ := hs
    simp only [mem_setOf_eq] at h1 h2 h3
    have hs1 : 1 < s.re := lt_of_le_of_lt (le_max_left _ _) h1
    have hsβ : 2 * β < s.re := lt_of_le_of_lt (le_max_right _ _) h1
    have hhalf : β < (s / 2).re := by simp; linarith
    have hne : s / 2 ≠ 2 / 3 := by
      intro h
      have := congrArg Complex.im h
      simp at this
      linarith
    have hF2 : DifferentiableAt ℂ (fun s : ℂ => F (s / 2)) s := by
      have hd : DifferentiableAt ℂ (fun s : ℂ => s / 2) s := differentiableAt_id.div_const (2 : ℂ)
      exact (hFd (s / 2) hhalf hne).comp s hd
    refine DifferentiableAt.differentiableWithinAt ?_
    exact ((differentiableAt_id.sub_const _).mul (completedUnramified_differentiableAt s hs1 h2 h3)).sub
      ((((((differentiableAt_const _).mul (unitFrequencyWeight_differentiable s)).mul_const _).mul_const _).mul
        (clearedCubeZeta_differentiable s)).mul ((besselSqMellin_differentiableAt s (by linarith)).mul
          hF2))
  -- `g` vanishes where the series converges
  have hg0 : ∀ s ∈ thetaRegion β, 4 < s.re → g s = 0 := by
    intro s hs hs4
    obtain ⟨-, h2, h3⟩ := hs
    simp only [mem_setOf_eq] at h2 h3
    have hdn : den s ≠ 0 :=
      mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (unitFrequencyWeight_ne_zero s))
        (pow_ne_zero 2 scalar_star_ne_zero)) (by norm_num)) (clearedCubeZeta_ne_zero (by linarith))
    have hU := completedUntwistedS_eq s hs4 h2 h3
    rw [completedUntwistedS, div_eq_iff hdn] at hU
    have hS := hFS (s / 2) (by simp; linarith)
    simp only [hg, hden]
    rw [hU, hS]
    ring
  -- analytic continuation through the region
  have hzero : EqOn g 0 (thetaRegion β) := by
    have hre41 : (41 / 10 + Complex.I : ℂ).re = 41 / 10 := by simp
    have him41 : (41 / 10 + Complex.I : ℂ).im = 1 := by simp
    have hz₀ : (41 / 10 + Complex.I : ℂ) ∈ thetaRegion β := by
      refine ⟨?_, ?_, ?_⟩
      · show max 1 (2 * β) < (41 / 10 + Complex.I : ℂ).re
        rw [hre41]
        exact max_lt (by norm_num) (by linarith)
      · show (41 / 10 + Complex.I : ℂ).re < 13 / 3
        rw [hre41]
        norm_num
      · show 0 < (41 / 10 + Complex.I : ℂ).im
        rw [him41]
        norm_num
    refine (hgd.analyticOnNhd (thetaRegion_isOpen β)).eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (thetaRegion_convex β).isPreconnected hz₀ ?_
    have hopen : IsOpen (thetaRegion β ∩ {s : ℂ | 4 < s.re}) :=
      (thetaRegion_isOpen β).inter (isOpen_lt continuous_const Complex.continuous_re)
    have hmem : (41 / 10 + Complex.I : ℂ) ∈ thetaRegion β ∩ {s : ℂ | 4 < s.re} := by
      refine ⟨hz₀, ?_⟩
      show 4 < (41 / 10 + Complex.I : ℂ).re
      rw [hre41]
      norm_num
    filter_upwards [hopen.mem_nhds hmem] with s hs
    exact hg0 s hs.1 hs.2
  -- evaluate at `2(1 + ρ)/3`
  set s₀ : ℂ := 2 * (1 + ρ) / 3 with hs₀
  have hs₀re : s₀.re = 2 * (1 + ρ.re) / 3 := by simp [hs₀]
  have hs₀im : s₀.im = 2 * ρ.im / 3 := by simp [hs₀]
  have hmem : s₀ ∈ thetaRegion β := by
    refine ⟨?_, ?_, ?_⟩
    · show max 1 (2 * β) < s₀.re
      rw [hs₀re]
      exact max_lt (by linarith) (by linarith)
    · show s₀.re < 13 / 3
      rw [hs₀re]
      linarith
    · show 0 < s₀.im
      rw [hs₀im]
      linarith
  have hρ1' : ρ ≠ 1 := by
    intro h
    rw [h] at hρlt
    simp at hρlt
  have hgs := hzero hmem
  have hZ := clearedCubeZeta_eq_zero hρ hρ1'
  simp only [hg, hden, Pi.zero_apply] at hgs
  rw [← hs₀] at hZ
  rw [hZ, mul_zero, zero_mul, sub_zero] at hgs
  have hne : s₀ - 4 / 3 ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp only [Complex.sub_im, Complex.zero_im] at this
    rw [hs₀im] at this
    norm_num at this
    linarith
  exact (mul_eq_zero.mp hgs).resolve_left hne

/-- **A power remainder forces the zeros of `ζ_K` into the theta square.** If
`Σ_{N(A) ≤ t} σ(A) = c t^{2/3} + O(t^β)` (`t ≥ 1`), then every zero `ρ` of `ζ · L(·, χ₋₃)` with `Re ρ > 1/2`,
`Re ρ > 3β − 1`, `Im ρ > 0` is a zero of the completed unramified theta square at `2(1 + ρ)/3`. -/
theorem remainder_forces_thetaSquare_zero {c : ℂ} {β K : ℝ}
    (hE : ∀ t : ℝ, 1 ≤ t → ‖squarefreeThetaSum t - c * ((t ^ (2 / 3 : ℝ) : ℝ) : ℂ)‖ ≤ K * t ^ β)
    {ρ : ℂ} (hρ : riemannZeta ρ = 0 ∨ DirichletCharacter.LFunction chi3D ρ = 0)
    (hρ1 : 1 / 2 < ρ.re) (hρβ : 3 * β - 1 < ρ.re) (hρi : 0 < ρ.im) :
    completedUnramified (2 * (1 + ρ) / 3) = 0 := by
  have hρlt := re_lt_one_of_zero hρ
  -- reduce to `0 ≤ β' ≤ 2/3`
  set β' := max β 0 with hβ'
  have hβ0 : 0 ≤ β' := le_max_right _ _
  have hβ'1 : 3 * β' - 1 < ρ.re := by
    rcases le_total β 0 with h | h
    · rw [hβ', max_eq_right h]; linarith
    · rw [hβ', max_eq_left h]; exact hρβ
  have hβ23 : β' ≤ 2 / 3 := by linarith
  have hE' : ∀ t : ℝ, 1 ≤ t → ‖squarefreeThetaSum t - c * ((t ^ (2 / 3 : ℝ) : ℝ) : ℂ)‖ ≤ K * t ^ β' :=
    fun t ht => (hE t ht).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le ht (le_max_left _ _)) (K_nonneg hE))
  refine thetaSquare_zero_of_extension (fun w => w * (c / (w - 2 / 3) + remainderMellin c w))
    (β := β') ?_ (fun w hw => twistedSquarefreeSeries_one_eq_remainder hE' hβ23 w (by linarith)) hρ hρ1 hβ'1 hρi
  intro w hw hw23
  have h1 : DifferentiableAt ℂ (fun w : ℂ => c / (w - 2 / 3)) w :=
    (differentiableAt_const c).div (differentiableAt_id.sub_const (2 / 3 : ℂ)) (sub_ne_zero.mpr hw23)
  exact differentiableAt_id.mul (h1.add (remainderMellin_differentiableAt hβ0 hE' w hw))

/-- **Square-root remainder.** If for every `ε > 0` the partial sums are `c t^{2/3} + O_ε(t^{1/2+ε})`, every zero
`ρ` of `ζ · L(·, χ₋₃)` with `Re ρ > 1/2`, `Im ρ > 0` is a zero of `Λ₀` at `2(1 + ρ)/3`. -/
theorem sqrtRemainder_forces_thetaSquare_zero {c : ℂ}
    (hE : ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, ∀ t : ℝ, 1 ≤ t →
      ‖squarefreeThetaSum t - c * ((t ^ (2 / 3 : ℝ) : ℝ) : ℂ)‖ ≤ K * t ^ (1 / 2 + ε))
    {ρ : ℂ} (hρ : riemannZeta ρ = 0 ∨ DirichletCharacter.LFunction chi3D ρ = 0)
    (hρ1 : 1 / 2 < ρ.re) (hρi : 0 < ρ.im) :
    completedUnramified (2 * (1 + ρ) / 3) = 0 := by
  obtain ⟨K, hK⟩ := hE ((ρ.re - 1 / 2) / 6) (by linarith)
  exact remainder_forces_thetaSquare_zero hK hρ hρ1 (by linarith) hρi

/-- **The remainder exponent is at least `(1 + Re ρ)/3`** for every zero `ρ` of `ζ · L(·, χ₋₃)` with `Re ρ > 1/2`,
`Im ρ > 0`, at which the theta square does not vanish. -/
theorem remainderExponent_ge {c : ℂ} {β K : ℝ}
    (hE : ∀ t : ℝ, 1 ≤ t → ‖squarefreeThetaSum t - c * ((t ^ (2 / 3 : ℝ) : ℝ) : ℂ)‖ ≤ K * t ^ β)
    {ρ : ℂ} (hρ : riemannZeta ρ = 0 ∨ DirichletCharacter.LFunction chi3D ρ = 0)
    (hρ1 : 1 / 2 < ρ.re) (hρi : 0 < ρ.im) (hΛ : completedUnramified (2 * (1 + ρ) / 3) ≠ 0) :
    (1 + ρ.re) / 3 ≤ β := by
  by_contra h
  push Not at h
  exact hΛ (remainder_forces_thetaSquare_zero hE hρ hρ1 (by linarith) hρi)

end GaloisForLFunctions.OrderSixMetaplecticTheory
