import GaloisForLFunctions.ArithmeticCouplingTheory.TheCouplingCalculus
import GaloisForLFunctions.ArithmeticCouplingTheory.TheCouplingIsAsLargeAsTheKernel
import GaloisForLFunctions.RenormalizedIntersectionTheory.TheKunnethSquareOfWeilsKernelIsRH
import GaloisForLFunctions.HeckeKreinToeplitz.OneGridHidesTwoGridsDecide
import GaloisForLFunctions.HeckeKreinToeplitz.TheFiniteIndexStratumOfZetaIsLindelofDeep

/-!
# Bounded coupling is the Riemann hypothesis

Weil's kernel `K_ζ(u) = W(B, T_{log u} B)` on `ℚ_{>0}` (cubic spline `B`) is `Φ(log u)` for the
continuous Hermitian profile `Φ(x) = F(−x)`, `F(t) = Σ_ρ e^{t(ρ−1/2)} w_ρ`
(`zetaKernel_eq_weilProfile`, `weilProfile_neg`). Its inter-tower coupling on two two-prime lattices
`⟨p, q⟩ × ⟨r, s⟩` is the profile coupling sampled on a dense product of log-scales
(`coupling_zetaKernel_eq`); it is the cross-difference `coprimeCrossDiff` of
`AdelicKreinGeometry/TowerCoupling` read on `ℚ_{>0}`.

* **Bounded coupling is RH** (`riemannHypothesis_iff_exists_bound_coupling`): the coupling of `K_ζ`
  is bounded on `⟨p, q⟩ × ⟨r, s⟩` iff RH holds, for any two pairs of distinct primes. Under RH it is
  at most `4 K_ζ(1)`; conversely a bound `M` gives `|Re K_ζ − K_ζ(1)| ≤ M/2` on all of `ℝ` by the
  lossless antidiagonal transfer, so the spline orbit is bounded and the zero width is `0`.
* **The coupling rate is the zero width** (`zetaZeroWidth_le_iff_coupling_rate`): for `σ ≥ 0`,
  `|Re C(u, v)| ≤ C e^{σ h(u, v)}`, with `h` the largest log-height read by the coupling, iff every
  zero satisfies `Re ρ − 1/2 ≤ σ`. Growth of the coupling is growth of the kernel, with no loss in
  the exponent and no Diophantine input.

So the inter-tower coupling is not a softer invariant than Weil's kernel: on two dense lattices the
two are equivalent with absolute constants.
-/

open Complex Filter Topology Set
open scoped ComplexConjugate
open GaloisForLFunctions.HeckeKreinToeplitz
open GaloisForLFunctions.RenormalizedIntersectionTheory (splineSeries continuous_splineSeries
  zetaKernel_eq_splineSeries orbitCorr_splineCycle_eq riemannHypothesis_iff_castelnuovoSeveri)
open GaloisForLFunctions.ArithmeticOrientationGeometry (zetaScalingDatum splineCycle
  zeta_splineOrbit_rate_iff_zetaZeroWidth_le)

noncomputable section

namespace GaloisForLFunctions.ArithmeticCouplingTheory

/-- The log-scale `log u` of a positive rational. -/
abbrev logScale (u : HeckeLattice) : ℝ := scale heckeLogScale u

theorem logScale_mul (u v : HeckeLattice) : logScale (u * v) = logScale u + logScale v :=
  scale_mul _ u v

theorem logScale_one : logScale 1 = 0 := by simp [logScale, scale]

theorem logScale_inv (u : HeckeLattice) : logScale u⁻¹ = -logScale u := scale_inv _ u

/-- The log-scales of a two-prime lattice are dense in `ℝ`. -/
theorem dense_range_logScale_twoPrimeLattice {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) : Dense (Set.range fun h : twoPrimeLattice hp hq => logScale h) := by
  have hdense : Dense (AddSubgroup.closure {Real.log p, Real.log q} : Set ℝ) :=
    dense_addSubgroupClosure_pair_iff.mpr (RHTower.irrational_log_ratio hq hp hpq.symm)
  refine hdense.mono fun x hx => ?_
  obtain ⟨m, n, hmn⟩ := AddSubgroup.mem_closure_pair.mp hx
  refine ⟨⟨primeElt hp ^ m * primeElt hq ^ n, Subgroup.mem_closure_pair.mpr ⟨m, n, rfl⟩⟩, ?_⟩
  change scale heckeLogScale (primeElt hp ^ m * primeElt hq ^ n) = x
  rw [scale_mul, scale_zpow, scale_zpow, scale_primeElt, scale_primeElt, ← hmn, zsmul_eq_mul,
    zsmul_eq_mul]

/-- Weil's profile `Φ(x) = F(−x)`: `K_ζ(u) = Φ(log u)`. -/
def weilProfile (x : ℝ) : ℂ := splineSeries (-x)

theorem continuous_weilProfile : Continuous weilProfile :=
  continuous_splineSeries.comp continuous_neg

theorem zetaKernel_eq_weilProfile (u : HeckeLattice) : zetaKernel u = weilProfile (logScale u) := by
  rw [zetaKernel_eq_splineSeries]; rfl

/-- **Weil's profile is Hermitian**: `Φ(−x) = conj Φ(x)`; it holds on the dense log-scales of
`⟨2, 3⟩` by Hermitian symmetry of `K_ζ` and extends by continuity. -/
theorem weilProfile_neg (x : ℝ) : weilProfile (-x) = conj (weilProfile x) := by
  have hD := dense_range_logScale_twoPrimeLattice Nat.prime_two Nat.prime_three (by norm_num)
  have heq : (fun x => weilProfile (-x)) = fun x => conj (weilProfile x) := by
    refine Continuous.ext_on hD (continuous_weilProfile.comp continuous_neg)
      (Complex.continuous_conj.comp continuous_weilProfile) ?_
    rintro _ ⟨u, rfl⟩
    simp only
    rw [← logScale_inv, ← zetaKernel_eq_weilProfile, ← zetaKernel_eq_weilProfile,
      isHermKernel_zetaKernel]
  exact congrFun heq x

/-- The Weil orbit correlation of the spline cycle is the real part of the profile. -/
theorem orbitCorr_splineCycle_eq_weilProfile (t : ℝ) :
    zetaScalingDatum.orbitCorr splineCycle t = (weilProfile (-t)).re := by
  rw [orbitCorr_splineCycle_eq, weilProfile, neg_neg]

/-- The real part of Weil's profile is even. -/
theorem re_weilProfile_neg (x : ℝ) : (weilProfile (-x)).re = (weilProfile x).re := by
  rw [weilProfile_neg, Complex.conj_re]

/-- The coupling of `K_ζ` is the profile coupling at the log-scales. -/
theorem coupling_zetaKernel_eq (u v : HeckeLattice) :
    coupling zetaKernel u v = profileCoupling weilProfile (logScale u) (logScale v) := by
  simp only [coupling, profileCoupling, zetaKernel_eq_weilProfile, logScale_mul, logScale_one]

/-- The real part of the coupling over two lattices, as a bound on dense sets. -/
private theorem re_bound_of_lattice {H₁ H₂ : Subgroup HeckeLattice} {g : ℝ → ℝ → ℝ}
    (h : ∀ u ∈ H₁, ∀ v ∈ H₂, |(coupling zetaKernel u v).re| ≤ g (logScale u) (logScale v)) :
    ∀ a ∈ Set.range (fun u : H₁ => logScale u),
      ∀ b ∈ Set.range (fun v : H₂ => logScale v),
        |(profileCoupling weilProfile a b).re| ≤ g a b := by
  rintro _ ⟨u, rfl⟩ _ ⟨v, rfl⟩
  rw [← coupling_zetaKernel_eq]
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
inter-tower coupling of Weil's kernel is bounded on `⟨p, q⟩ × ⟨r, s⟩` iff RH holds. -/
theorem riemannHypothesis_iff_exists_bound_coupling {p q r s : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hr : r.Prime) (hs : s.Prime) (hpq : p ≠ q) (hrs : r ≠ s) :
    RiemannHypothesis ↔ ∃ M : ℝ, ∀ u ∈ twoPrimeLattice hp hq, ∀ v ∈ twoPrimeLattice hr hs,
      ‖coupling zetaKernel u v‖ ≤ M := by
  constructor
  · intro hRH
    have hcs := riemannHypothesis_iff_castelnuovoSeveri.mp hRH
    refine ⟨4 * (zetaKernel 1).re, fun u _ v _ => ?_⟩
    have hb : ∀ w : HeckeLattice, ‖weilProfile (logScale w)‖ ≤ (zetaKernel 1).re := fun w => by
      rw [← zetaKernel_eq_weilProfile]; exact hcs _
    rw [coupling_zetaKernel_eq]
    have h1 := norm_profileCoupling_le weilProfile (logScale u) (logScale v)
    rw [← logScale_mul, ← logScale_one] at h1
    linarith [hb (u * v), hb u, hb v, hb 1]
  · rintro ⟨M, hM⟩
    have hre := abs_re_sub_le_of_dense continuous_weilProfile weilProfile_neg
      (dense_range_logScale_twoPrimeLattice hp hq hpq)
      (dense_range_logScale_twoPrimeLattice hr hs hrs)
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
theorem riemannHypothesis_iff_exists_bound_coupling_2357 :
    RiemannHypothesis ↔ ∃ M : ℝ, ∀ u ∈ twoPrimeLattice Nat.prime_two Nat.prime_three,
      ∀ v ∈ twoPrimeLattice (by norm_num : Nat.Prime 5) (by norm_num : Nat.Prime 7),
        ‖coupling zetaKernel u v‖ ≤ M :=
  riemannHypothesis_iff_exists_bound_coupling _ _ _ _ (by norm_num) (by norm_num)

/-- The largest log-height read by the coupling sample `(x, y)`: `max(|x|, |y|, |x + y|)`. -/
def couplingHeight (x y : ℝ) : ℝ := max |x| (max |y| |x + y|)

theorem continuous_couplingHeight : Continuous fun p : ℝ × ℝ => couplingHeight p.1 p.2 := by
  unfold couplingHeight; fun_prop

theorem couplingHeight_neg (x : ℝ) : couplingHeight x (-x) = |x| := by
  simp [couplingHeight]

theorem couplingHeight_nonneg (x y : ℝ) : 0 ≤ couplingHeight x y :=
  (abs_nonneg x).trans (le_max_left _ _)

/-- **The coupling rate is the zero width.** For `σ ≥ 0`, the real part of the inter-tower coupling
of Weil's kernel grows at most like `e^{σ h}` in the log-height `h` of the sample iff every zero of
`ζ` satisfies `Re ρ − 1/2 ≤ σ`. -/
theorem zetaZeroWidth_le_iff_coupling_rate {p q r s : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hr : r.Prime) (hs : s.Prime) (hpq : p ≠ q) (hrs : r ≠ s) {σ : ℝ} (hσ : 0 ≤ σ) :
    SquareRootThreshold.zetaZeroWidth ≤ σ ↔ ∃ C : ℝ, ∀ u ∈ twoPrimeLattice hp hq,
      ∀ v ∈ twoPrimeLattice hr hs, |(coupling zetaKernel u v).re| ≤
        C * Real.exp (σ * couplingHeight (logScale u) (logScale v)) := by
  constructor
  · intro hw
    obtain ⟨K, hK⟩ := (zeta_splineOrbit_rate_iff_zetaZeroWidth_le hσ).mpr hw
    have hK' : ∀ x : ℝ, |(weilProfile x).re| ≤ K * Real.exp (σ * |x|) := fun x => by
      rcases le_total 0 x with hx | hx
      · have := hK x hx
        rw [orbitCorr_splineCycle_eq_weilProfile, re_weilProfile_neg] at this
        rwa [abs_of_nonneg hx]
      · have := hK (-x) (neg_nonneg.mpr hx)
        rw [orbitCorr_splineCycle_eq_weilProfile, neg_neg] at this
        rwa [abs_of_nonpos hx]
    have hK0 : 0 ≤ K := by
      have := (abs_nonneg _).trans (hK' 0)
      simpa using this
    refine ⟨4 * K, fun u _ v _ => ?_⟩
    set a := logScale u
    set b := logScale v
    have hh := couplingHeight_nonneg a b
    have mono : ∀ y, |y| ≤ couplingHeight a b →
        K * Real.exp (σ * |y|) ≤ K * Real.exp (σ * couplingHeight a b) := fun y hy =>
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hy hσ)) hK0
    have ha : |a| ≤ couplingHeight a b := le_max_left _ _
    have hb : |b| ≤ couplingHeight a b := (le_max_left _ _).trans (le_max_right _ _)
    have hab : |a + b| ≤ couplingHeight a b := (le_max_right _ _).trans (le_max_right _ _)
    have h0 : |(0 : ℝ)| ≤ couplingHeight a b := by simpa using hh
    rw [coupling_zetaKernel_eq, profileCoupling]
    simp only [Complex.add_re, Complex.sub_re]
    have t1 := (hK' (a + b)).trans (mono _ hab)
    have t2 := (hK' a).trans (mono _ ha)
    have t3 := (hK' b).trans (mono _ hb)
    have t4 := (hK' 0).trans (mono _ h0)
    have e1 := abs_add_le ((weilProfile (a + b)).re - (weilProfile a).re - (weilProfile b).re)
      (weilProfile 0).re
    have e2 := abs_sub ((weilProfile (a + b)).re - (weilProfile a).re) (weilProfile b).re
    have e3 := abs_sub (weilProfile (a + b)).re (weilProfile a).re
    linarith
  · rintro ⟨C, hC⟩
    have hC0 : 0 ≤ C := by
      have h := hC 1 (Subgroup.one_mem _) 1 (Subgroup.one_mem _)
      have h0 : couplingHeight 0 0 = 0 := by simp [couplingHeight]
      rw [coupling_one_left, Complex.zero_re, abs_zero, logScale_one, h0, mul_zero,
        Real.exp_zero, mul_one] at h
      exact h
    have hre := abs_re_sub_le_of_dense continuous_weilProfile weilProfile_neg
      (dense_range_logScale_twoPrimeLattice hp hq hpq)
      (dense_range_logScale_twoPrimeLattice hr hs hrs)
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
