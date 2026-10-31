import GaloisForLFunctions.ArithmeticCouplingTheory.TheCouplingCalculus
import GaloisForLFunctions.ArithmeticCouplingTheory.TheCouplingIsAsLargeAsTheKernel
import GaloisForLFunctions.AdelicKreinGeometry.TowerCoupling.InterTowerCouplingRigidity
import GaloisForLFunctions.RenormalizedIntersectionTheory.TheKunnethSquareOfWeilsKernelIsRH

/-!
# Bounded coupling is the Riemann hypothesis

Weil's correlation `ratCorr(u) = W(B, T_{log u} B)` on `ℚ_{>0}` (cubic spline `B`) is
`Φ(log u)` for the continuous Hermitian profile `Φ(x) = F(−x)`, `F(t) = Σ_ρ e^{t(ρ−1/2)} w_ρ`
(`ratCorr_eq_weilProfile`, `weilProfile_neg`). Its inter-tower coupling on two two-prime lattices
`⟨p, q⟩ × ⟨r, s⟩` is the profile coupling sampled on a dense product of log-scales
(`coprimeCrossDiff_ratCorr_eq`).

* **Bounded coupling is RH** (`riemannHypothesis_iff_exists_bound_coprimeCrossDiff`): the coupling of
  `ratCorr` is bounded on `⟨p, q⟩ × ⟨r, s⟩` iff RH holds, for any two pairs of distinct primes. Under
  RH it is at most `4 K_ζ(1)`; conversely a bound `M` gives `|Re K_ζ − K_ζ(1)| ≤ M/2` on all of `ℝ`
  by the lossless antidiagonal transfer, so the spline orbit is bounded and the zero width is `0`.
* **The coupling rate is the zero width** (`zetaZeroWidth_le_iff_coupling_rate`): for `σ ≥ 0`,
  `|Re C(u, v)| ≤ C e^{σ h(u, v)}` with `h` the largest log-height read by the coupling iff every zero
  satisfies `Re ρ − 1/2 ≤ σ`. Growth of the coupling is growth of the kernel, with no loss in the
  exponent and no Diophantine input.

So the inter-tower coupling is not a softer invariant than Weil's kernel: on two dense lattices the
two are equivalent with absolute constants.
-/

open Complex Filter Topology Set
open scoped ComplexConjugate
open GaloisForLFunctions.HeckeKreinToeplitz GaloisForLFunctions.ArithmeticPositiveDuality
open GaloisForLFunctions.AdelicKreinGeometry.TowerCoupling
open GaloisForLFunctions.RenormalizedIntersectionTheory (splineSeries continuous_splineSeries
  zetaKernel_eq_splineSeries orbitCorr_splineCycle_eq riemannHypothesis_iff_castelnuovoSeveri)
open GaloisForLFunctions.ArithmeticOrientationGeometry (zetaScalingDatum splineCycle
  zeta_splineOrbit_rate_iff_zetaZeroWidth_le)

noncomputable section

namespace GaloisForLFunctions.ArithmeticCouplingTheory

/-- Weil's profile `Φ(x) = F(−x)`: `ratCorr u = Φ(log u)`. -/
def weilProfile (x : ℝ) : ℂ := splineSeries (-x)

theorem continuous_weilProfile : Continuous weilProfile :=
  continuous_splineSeries.comp continuous_neg

theorem ratCorr_eq_weilProfile (u : posUnits) : ratCorr u = weilProfile (logPos u) := by
  rw [ratCorr_eq_zetaKernel, zetaKernel_eq_splineSeries]; rfl

theorem logPos_inv (u : posUnits) : logPos u⁻¹ = -logPos u := by
  have h := logPos_inv_mul u 1
  rwa [mul_one, logPos_one, zero_sub] at h

/-- **Weil's profile is Hermitian**: `Φ(−x) = conj Φ(x)`; it holds on the dense log-scales of
`⟨2, 3⟩` by Hermitian symmetry of `ratCorr` and extends by continuity. -/
theorem weilProfile_neg (x : ℝ) : weilProfile (-x) = conj (weilProfile x) := by
  have hD := dense_range_logPos_twoPrimeUnits (p := prime2) (q := prime3) (by decide)
  have heq : (fun x => weilProfile (-x)) = fun x => conj (weilProfile x) := by
    refine Continuous.ext_on hD (continuous_weilProfile.comp continuous_neg)
      (Complex.continuous_conj.comp continuous_weilProfile) ?_
    rintro _ ⟨u, rfl⟩
    simp only
    rw [← logPos_inv, ← ratCorr_eq_weilProfile, ← ratCorr_eq_weilProfile, isHermKernel_ratCorr]
  exact congrFun heq x

/-- The Weil orbit correlation of the spline cycle is the real part of the profile. -/
theorem orbitCorr_splineCycle_eq_weilProfile (t : ℝ) :
    zetaScalingDatum.orbitCorr splineCycle t = (weilProfile (-t)).re := by
  rw [orbitCorr_splineCycle_eq, weilProfile, neg_neg]

/-- The real part of Weil's profile is even. -/
theorem re_weilProfile_neg (x : ℝ) : (weilProfile (-x)).re = (weilProfile x).re := by
  rw [weilProfile_neg, Complex.conj_re]

/-- The inter-tower coupling of `ratCorr` is the profile coupling at the log-scales. -/
theorem coprimeCrossDiff_ratCorr_eq (u v : posUnits) :
    coprimeCrossDiff ratCorr u v = profileCoupling weilProfile (logPos u) (logPos v) := by
  simp only [coprimeCrossDiff, profileCoupling, ratCorr_eq_weilProfile, logPos_mul, logPos_one]

/-- The AKG cross-difference is the coupling of the calculus. -/
theorem coprimeCrossDiff_eq_coupling (K : posUnits → ℂ) (u v : posUnits) :
    coprimeCrossDiff K u v = coupling K u v := rfl

/-- The real part of the coupling over the log-scales of two lattices, as a bound on dense sets. -/
private theorem re_bound_of_lattice {p q r s : Nat.Primes} {g : ℝ → ℝ → ℝ}
    (h : ∀ u ∈ twoPrimeUnits p q, ∀ v ∈ twoPrimeUnits r s,
      |(coprimeCrossDiff ratCorr u v).re| ≤ g (logPos u) (logPos v)) :
    ∀ a ∈ Set.range (fun u : twoPrimeUnits p q => logPos u),
      ∀ b ∈ Set.range (fun v : twoPrimeUnits r s => logPos v),
        |(profileCoupling weilProfile a b).re| ≤ g a b := by
  rintro _ ⟨u, rfl⟩ _ ⟨v, rfl⟩
  rw [← coprimeCrossDiff_ratCorr_eq]
  exact h u u.2 v v.2

/-- `|Re K_ζ|` along the spline orbit, from a bound on the profile's real part. -/
private theorem abs_orbitCorr_le_of_profile {K : ℝ} (hK : ∀ x, |(weilProfile x).re -
    (weilProfile 0).re| ≤ K) (t : ℝ) :
    |zetaScalingDatum.orbitCorr splineCycle t| ≤ K + |(weilProfile 0).re| := by
  rw [orbitCorr_splineCycle_eq_weilProfile]
  have := hK (-t)
  have h2 := abs_sub_abs_le_abs_sub (weilProfile (-t)).re (weilProfile 0).re
  linarith

/-- **Bounded coupling is the Riemann hypothesis.** For any two pairs of distinct primes, the
inter-tower coupling of Weil's correlation is bounded on `⟨p, q⟩ × ⟨r, s⟩` iff RH holds. -/
theorem riemannHypothesis_iff_exists_bound_coprimeCrossDiff {p q r s : Nat.Primes}
    (hpq : p ≠ q) (hrs : r ≠ s) :
    RiemannHypothesis ↔ ∃ M : ℝ, ∀ u ∈ twoPrimeUnits p q, ∀ v ∈ twoPrimeUnits r s,
      ‖coprimeCrossDiff ratCorr u v‖ ≤ M := by
  constructor
  · intro hRH
    have hcs := riemannHypothesis_iff_castelnuovoSeveri.mp hRH
    refine ⟨4 * (zetaKernel 1).re, fun u _ v _ => ?_⟩
    have hb : ∀ w : posUnits, ‖weilProfile (logPos w)‖ ≤ (zetaKernel 1).re := fun w => by
      rw [← ratCorr_eq_weilProfile, ratCorr_eq_zetaKernel]; exact hcs _
    rw [coprimeCrossDiff_ratCorr_eq]
    have h1 := norm_profileCoupling_le weilProfile (logPos u) (logPos v)
    rw [← logPos_mul, ← logPos_one] at h1
    linarith [hb (u * v), hb u, hb v, hb 1]
  · rintro ⟨M, hM⟩
    have hre := abs_re_sub_le_of_dense continuous_weilProfile weilProfile_neg
      (dense_range_logPos_twoPrimeUnits hpq) (dense_range_logPos_twoPrimeUnits hrs)
      (g := fun _ _ => M) continuous_const
      (re_bound_of_lattice fun u hu v hv => (Complex.abs_re_le_norm _).trans (hM u hu v hv))
    have hrate : SquareRootThreshold.zetaZeroWidth ≤ 0 := by
      refine (zeta_splineOrbit_rate_iff_zetaZeroWidth_le le_rfl).mp
        ⟨M / 2 + |(weilProfile 0).re|, fun t _ => ?_⟩
      rw [zero_mul, Real.exp_zero, mul_one]
      exact abs_orbitCorr_le_of_profile hre t
    exact SquareRootThreshold.riemannHypothesis_iff_zetaZeroWidth_eq_zero.mpr
      (le_antisymm hrate SquareRootThreshold.zetaZeroWidth_nonneg)

/-- **Bounded coupling on `⟨2, 3⟩ × ⟨5, 7⟩` is RH.** -/
theorem riemannHypothesis_iff_exists_bound_coprimeCrossDiff_2357 :
    RiemannHypothesis ↔ ∃ M : ℝ, ∀ u ∈ twoPrimeUnits prime2 prime3,
      ∀ v ∈ twoPrimeUnits prime5 prime7, ‖coprimeCrossDiff ratCorr u v‖ ≤ M :=
  riemannHypothesis_iff_exists_bound_coprimeCrossDiff (by decide) (by decide)

/-- The largest log-height read by the coupling sample `(x, y)`: `max(|x|, |y|, |x + y|)`. -/
def couplingHeight (x y : ℝ) : ℝ := max |x| (max |y| |x + y|)

theorem continuous_couplingHeight : Continuous fun p : ℝ × ℝ => couplingHeight p.1 p.2 := by
  unfold couplingHeight; fun_prop

theorem couplingHeight_neg (x : ℝ) : couplingHeight x (-x) = |x| := by
  simp [couplingHeight]

theorem couplingHeight_nonneg (x y : ℝ) : 0 ≤ couplingHeight x y :=
  (abs_nonneg x).trans (le_max_left _ _)

/-- **The coupling rate is the zero width.** For `σ ≥ 0`, the real part of the inter-tower coupling
of Weil's correlation grows at most like `e^{σ h}` in the log-height `h` of the sample iff every zero
of `ζ` satisfies `Re ρ − 1/2 ≤ σ`. -/
theorem zetaZeroWidth_le_iff_coupling_rate {p q r s : Nat.Primes} (hpq : p ≠ q) (hrs : r ≠ s)
    {σ : ℝ} (hσ : 0 ≤ σ) :
    SquareRootThreshold.zetaZeroWidth ≤ σ ↔ ∃ C : ℝ, ∀ u ∈ twoPrimeUnits p q,
      ∀ v ∈ twoPrimeUnits r s, |(coprimeCrossDiff ratCorr u v).re| ≤
        C * Real.exp (σ * couplingHeight (logPos u) (logPos v)) := by
  constructor
  · intro hw
    obtain ⟨K, hK⟩ := (zeta_splineOrbit_rate_iff_zetaZeroWidth_le hσ).mpr hw
    have hK' : ∀ x : ℝ, |(weilProfile x).re| ≤ K * Real.exp (σ * |x|) := fun x => by
      rcases le_total 0 x with hx | hx
      · have := hK x hx
        rwa [orbitCorr_splineCycle_eq_weilProfile, re_weilProfile_neg, ← abs_of_nonneg hx] at this
      · have := hK (-x) (neg_nonneg.mpr hx)
        rwa [orbitCorr_splineCycle_eq_weilProfile, neg_neg, ← abs_of_nonpos hx] at this
    have hK0 : 0 ≤ K := by
      have := (abs_nonneg _).trans (hK' 0)
      simpa using this
    refine ⟨4 * K, fun u _ v _ => ?_⟩
    set a := logPos u
    set b := logPos v
    have hh := couplingHeight_nonneg a b
    have mono : ∀ y, |y| ≤ couplingHeight a b →
        K * Real.exp (σ * |y|) ≤ K * Real.exp (σ * couplingHeight a b) := fun y hy =>
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hy hσ)) hK0
    have ha : |a| ≤ couplingHeight a b := le_max_left _ _
    have hb : |b| ≤ couplingHeight a b := (le_max_left _ _).trans (le_max_right _ _)
    have hab : |a + b| ≤ couplingHeight a b := (le_max_right _ _).trans (le_max_right _ _)
    have h0 : |(0 : ℝ)| ≤ couplingHeight a b := by simpa using hh
    rw [coprimeCrossDiff_ratCorr_eq, profileCoupling]
    simp only [Complex.add_re, Complex.sub_re]
    have t1 := (hK' (a + b)).trans (mono _ hab)
    have t2 := (hK' a).trans (mono _ ha)
    have t3 := (hK' b).trans (mono _ hb)
    have t4 := (hK' 0).trans (mono _ h0)
    calc |(weilProfile (a + b)).re - (weilProfile a).re - (weilProfile b).re + (weilProfile 0).re|
        ≤ |(weilProfile (a + b)).re| + |(weilProfile a).re| + |(weilProfile b).re| +
            |(weilProfile 0).re| := by
          have := abs_add_le ((weilProfile (a + b)).re - (weilProfile a).re -
            (weilProfile b).re) (weilProfile 0).re
          have := abs_sub ((weilProfile (a + b)).re - (weilProfile a).re) (weilProfile b).re
          have := abs_sub (weilProfile (a + b)).re (weilProfile a).re
          linarith
      _ ≤ 4 * K * Real.exp (σ * couplingHeight a b) := by linarith
  · rintro ⟨C, hC⟩
    have hC0 : 0 ≤ C := by
      have h := hC 1 (Subgroup.one_mem _) 1 (Subgroup.one_mem _)
      simp only [coprimeCrossDiff, mul_one, sub_self, zero_sub, neg_add_cancel, Complex.zero_re,
        abs_zero, logPos_one, couplingHeight, abs_zero, add_zero, max_self, mul_zero,
        Real.exp_zero] at h
      linarith
    have hre := abs_re_sub_le_of_dense continuous_weilProfile weilProfile_neg
      (dense_range_logPos_twoPrimeUnits hpq) (dense_range_logPos_twoPrimeUnits hrs)
      (g := fun x y => C * Real.exp (σ * couplingHeight x y))
      (continuous_const.mul (Real.continuous_exp.comp
        (continuous_const.mul continuous_couplingHeight)))
      (re_bound_of_lattice hC)
    refine (zeta_splineOrbit_rate_iff_zetaZeroWidth_le hσ).mp
      ⟨C / 2 + |(weilProfile 0).re|, fun t ht => ?_⟩
    rw [orbitCorr_splineCycle_eq_weilProfile]
    have h1 := hre (-t)
    rw [couplingHeight_neg, abs_neg, abs_of_nonneg ht] at h1
    have h2 := abs_sub_abs_le_abs_sub (weilProfile (-t)).re (weilProfile 0).re
    have h3 : 1 ≤ Real.exp (σ * t) := Real.one_le_exp (mul_nonneg hσ ht)
    have h4 : |(weilProfile 0).re| ≤ |(weilProfile 0).re| * Real.exp (σ * t) :=
      le_mul_of_one_le_right (abs_nonneg _) h3
    nlinarith

end GaloisForLFunctions.ArithmeticCouplingTheory
