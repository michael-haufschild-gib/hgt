import GaloisForLFunctions.RHTower.RouteRCofinalSieveHarmonicResidue
import GaloisForLFunctions.HTGeometry.CofinalUnitProfileResidue

/-!
# The sub-quantum gap criterion at the Route R first trace wall

The oriented harmonic residue of the moving first-wall Gamma Bockstein takes
only the three values `-1`, `0`, `1`.  Because that residue is read by *every*
bounded, unit-mass, cofinally escaping profile on the primes — not only by the
restarted Euler sieve — the vanishing demanded of a source producer can be
replaced by a strict inequality: a single profile whose averages stay eventually
below one in modulus already forces neutral grade, hence critical placement.

The quantization therefore converts an exact annihilation requirement into an
open condition, and it does so for an arbitrary reading device.
-/

open Filter Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-! ## The first-wall residue in reference form -/

theorem routeRPrimeHarmonicAsymptotic_iff_hasReferenceResidue
    (a : Nat.Primes → ℂ) (c : ℂ) :
    RouteRPrimeHarmonicAsymptotic a c ↔
      HasReferenceResidue primeHarmonicWeight a c := by
  constructor
  · intro hs
    refine Summable.congr hs fun p => ?_
    simp [routeRPrimeHarmonicField, primeHarmonicWeight]
  · intro hs
    refine Summable.congr hs fun p => ?_
    simp [routeRPrimeHarmonicField, primeHarmonicWeight]

theorem hasReferenceResidue_criticalWall_neg_one_of_pos {t : ℝ} (ht : 0 < t) :
    HasReferenceResidue primeHarmonicWeight
      (routeRPrimeGammaCriticalWallField t) (-1) :=
  (routeRPrimeHarmonicAsymptotic_iff_hasReferenceResidue _ _).mp
    (routeRPrimeGammaCriticalWallAsymptotic_neg_one_of_pos ht)

theorem hasReferenceResidue_criticalWall_one_of_neg {t : ℝ} (ht : t < 0) :
    HasReferenceResidue primeHarmonicWeight
      (routeRPrimeGammaCriticalWallField t) 1 :=
  (routeRPrimeHarmonicAsymptotic_iff_hasReferenceResidue _ _).mp
    (routeRPrimeGammaCriticalWallAsymptotic_one_of_neg ht)

theorem hasReferenceResidue_criticalWall_zero :
    HasReferenceResidue primeHarmonicWeight
      (routeRPrimeGammaCriticalWallField 0) 0 :=
  (routeRPrimeHarmonicAsymptotic_iff_hasReferenceResidue _ _).mp
    routeRPrimeGammaCriticalWallAsymptotic_zero

/-! ## Every profile reads the same oriented quantum -/

section Profile

variable {mu : ℕ → Nat.Primes → ℝ}

theorem tendsto_profileAverage_criticalWall_neg_one_of_pos
    (hmu : IsCofinalUnitProfile primeHarmonicWeight mu) {t : ℝ} (ht : 0 < t) :
    Tendsto (fun N => profileAverage mu N (routeRPrimeGammaCriticalWallField t))
      atTop (𝓝 (-1)) :=
  tendsto_profileAverage hmu (hasReferenceResidue_criticalWall_neg_one_of_pos ht)

theorem tendsto_profileAverage_criticalWall_one_of_neg
    (hmu : IsCofinalUnitProfile primeHarmonicWeight mu) {t : ℝ} (ht : t < 0) :
    Tendsto (fun N => profileAverage mu N (routeRPrimeGammaCriticalWallField t))
      atTop (𝓝 1) :=
  tendsto_profileAverage hmu (hasReferenceResidue_criticalWall_one_of_neg ht)

theorem tendsto_profileAverage_criticalWall_zero
    (hmu : IsCofinalUnitProfile primeHarmonicWeight mu) :
    Tendsto (fun N => profileAverage mu N (routeRPrimeGammaCriticalWallField 0))
      atTop (𝓝 0) :=
  tendsto_profileAverage hmu hasReferenceResidue_criticalWall_zero

/-- **Sub-quantum gap forces neutral grade.**  The oriented residue is `-1`,
`0` or `1`, so an eventual modulus bound strictly below one excludes both
orientations. -/
theorem eq_zero_of_eventually_norm_profileAverage_le
    (hmu : IsCofinalUnitProfile primeHarmonicWeight mu) {t r : ℝ} (hr : r < 1)
    (hbound : ∀ᶠ N in atTop,
      ‖profileAverage mu N (routeRPrimeGammaCriticalWallField t)‖ ≤ r) :
    t = 0 := by
  by_contra ht
  rcases lt_or_gt_of_ne ht with htneg | htpos
  · have hlim := (tendsto_profileAverage_criticalWall_one_of_neg hmu htneg).norm
    have hle := le_of_tendsto hlim hbound
    rw [norm_one] at hle
    linarith
  · have hlim := (tendsto_profileAverage_criticalWall_neg_one_of_pos hmu htpos).norm
    have hle := le_of_tendsto hlim hbound
    rw [norm_neg, norm_one] at hle
    linarith

/-- Vanishing of the profile average is exactly neutral grade, for every
profile.  The restarted Euler sieve is one instance; the law is device-free. -/
theorem tendsto_profileAverage_criticalWall_zero_iff
    (hmu : IsCofinalUnitProfile primeHarmonicWeight mu) (t : ℝ) :
    Tendsto (fun N => profileAverage mu N (routeRPrimeGammaCriticalWallField t))
      atTop (𝓝 0) ↔ t = 0 := by
  constructor
  · intro hzero
    refine eq_zero_of_eventually_norm_profileAverage_le hmu
      (r := 1 / 2) (by norm_num) ?_
    have hnorm := hzero.norm
    rw [norm_zero] at hnorm
    exact hnorm.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 2)
  · rintro rfl
    exact tendsto_profileAverage_criticalWall_zero hmu

/-! ## Sharpened gap: one subsequence of real parts -/

/-- A family converging along any nontrivial filter to a value of unit real
modulus is not frequently below a threshold under one. -/
theorem not_frequently_abs_re_le_of_unit_limit {α : Type*} {l : Filter α}
    [l.NeBot] {F : α → ℂ} {r : ℝ} (hr : r < 1)
    {c : ℂ} (hc : |c.re| = 1) (hlim : Tendsto F l (𝓝 c))
    (hfreq : ∃ᶠ x in l, |(F x).re| ≤ r) : False := by
  have hre : Tendsto (fun x => |(F x).re|) l (𝓝 |c.re|) :=
    ((Complex.continuous_re.tendsto c).comp hlim).abs
  rw [hc] at hre
  obtain ⟨x, hle, hlt⟩ :=
    (hfreq.and_eventually (hre.eventually_const_lt hr)).exists
  linarith

/-- **Sharpest form of the gap criterion.**  The limiting residue is real and
quantized, so it is enough that the *real parts* stay below the quantum along a
*single subsequence*. -/
theorem eq_zero_of_frequently_abs_re_profileAverage_le
    (hmu : IsCofinalUnitProfile primeHarmonicWeight mu) {t r : ℝ} (hr : r < 1)
    (hfreq : ∃ᶠ N in atTop,
      |(profileAverage mu N (routeRPrimeGammaCriticalWallField t)).re| ≤ r) :
    t = 0 := by
  by_contra ht
  rcases lt_or_gt_of_ne ht with htneg | htpos
  · exact not_frequently_abs_re_le_of_unit_limit hr (by simp)
      (tendsto_profileAverage_criticalWall_one_of_neg hmu htneg) hfreq
  · exact not_frequently_abs_re_le_of_unit_limit hr (by simp)
      (tendsto_profileAverage_criticalWall_neg_one_of_pos hmu htpos) hfreq

/-! ## Robustness under negligible perturbation of the source field -/

/-- A producer field agreeing with the first wall up to a summable or pointwise
negligible error carries the same oriented residue. -/
theorem hasReferenceResidueMod_of_negligible_sub_criticalWall
    {a : Nat.Primes → ℂ} {t : ℝ} {c : ℂ}
    (hres : HasReferenceResidue primeHarmonicWeight
      (routeRPrimeGammaCriticalWallField t) c)
    (hneg : IsCofinitelyNegligible primeHarmonicWeight
      (fun p => a p - routeRPrimeGammaCriticalWallField t p)) :
    HasReferenceResidueMod primeHarmonicWeight a c :=
  ⟨fun p => routeRPrimeGammaCriticalWallField t p -
      c * (primeHarmonicWeight p : ℂ),
    fun p => a p - routeRPrimeGammaCriticalWallField t p, hres, hneg,
    fun p => by ring⟩

/-- **Robust gap criterion.**  The threshold test may be applied to any producer
field that agrees with the first wall up to a summable or `o(1/p)` error: the
oriented quantum is unchanged, so a frequent sub-quantum bound on the producer
still forces neutral grade. -/
theorem eq_zero_of_frequently_abs_re_profileAverage_le_of_negligible_sub
    (hmu : IsCofinalUnitProfile primeHarmonicWeight mu)
    {a : Nat.Primes → ℂ} {t r : ℝ} (hr : r < 1)
    (hneg : IsCofinitelyNegligible primeHarmonicWeight
      (fun p => a p - routeRPrimeGammaCriticalWallField t p))
    (hfreq : ∃ᶠ N in atTop, |(profileAverage mu N a).re| ≤ r) :
    t = 0 := by
  by_contra ht
  rcases lt_or_gt_of_ne ht with htneg | htpos
  · exact not_frequently_abs_re_le_of_unit_limit hr (by simp)
      (tendsto_profileAverage_mod primeHarmonicWeight_nonneg hmu
        (hasReferenceResidueMod_of_negligible_sub_criticalWall
          (hasReferenceResidue_criticalWall_one_of_neg htneg) hneg)) hfreq
  · exact not_frequently_abs_re_le_of_unit_limit hr (by simp)
      (tendsto_profileAverage_mod primeHarmonicWeight_nonneg hmu
        (hasReferenceResidueMod_of_negligible_sub_criticalWall
          (hasReferenceResidue_criticalWall_neg_one_of_pos htpos) hneg)) hfreq

/-! ## The Xi endpoint -/

/-- Sub-quantum gap at one divisor point puts that point on the critical
line. -/
theorem xiDivisorSupport_re_eq_half_of_eventually_norm_profileAverage_le
    (hmu : IsCofinalUnitProfile primeHarmonicWeight mu)
    (rho : XiDivisorSupport) {r : ℝ} (hr : r < 1)
    (hbound : ∀ᶠ N in atTop,
      ‖profileAverage mu N (routeRPrimeGammaXiCriticalWallField rho)‖ ≤ r) :
    (rho : ℂ).re = 1 / 2 := by
  rw [← primeDepthBVWoldXiCenteredRate_eq_zero_iff]
  exact eq_zero_of_eventually_norm_profileAverage_le hmu hr hbound

/-- Sharpened Xi endpoint: real parts, along a subsequence only. -/
theorem xiDivisorSupport_re_eq_half_of_frequently_abs_re_profileAverage_le
    (hmu : IsCofinalUnitProfile primeHarmonicWeight mu)
    (rho : XiDivisorSupport) {r : ℝ} (hr : r < 1)
    (hfreq : ∃ᶠ N in atTop,
      |(profileAverage mu N (routeRPrimeGammaXiCriticalWallField rho)).re| ≤ r) :
    (rho : ℂ).re = 1 / 2 := by
  rw [← primeDepthBVWoldXiCenteredRate_eq_zero_iff]
  exact eq_zero_of_frequently_abs_re_profileAverage_le hmu hr hfreq

end Profile

/-- Every Xi divisor point on the critical line is the Riemann hypothesis. -/
theorem riemannHypothesis_of_forall_xiDivisorSupport_re_eq_half
    (h : ∀ rho : XiDivisorSupport, (rho : ℂ).re = 1 / 2) : RiemannHypothesis := by
  rw [rh_iff_xi_ne_zero_right]
  intro z hz hzero
  exact (ne_of_gt (mem_rightHalf.mp hz))
    (h ⟨z, mem_xi_divisor_support_of_eq_zero hzero⟩)

/-- **RH from one sub-quantum gap.**  A single bounded cofinal prime-harmonic
profile whose first-wall averages stay eventually strictly inside the unit disc
at every Xi divisor point implies the Riemann hypothesis.  The threshold is the
harmonic quantum, so no exact annihilation is required of the source. -/
theorem riemannHypothesis_of_eventually_norm_profileAverage_lt_one
    {mu : ℕ → Nat.Primes → ℝ}
    (hmu : IsCofinalUnitProfile primeHarmonicWeight mu)
    (hbound : ∀ rho : XiDivisorSupport, ∃ r < 1, ∀ᶠ N in atTop,
      ‖profileAverage mu N (routeRPrimeGammaXiCriticalWallField rho)‖ ≤ r) :
    RiemannHypothesis := by
  refine riemannHypothesis_of_forall_xiDivisorSupport_re_eq_half fun rho => ?_
  obtain ⟨r, hr, hb⟩ := hbound rho
  exact xiDivisorSupport_re_eq_half_of_eventually_norm_profileAverage_le
    hmu rho hr hb

/-- **RH from one sub-quantum gap on real parts along a subsequence.**  The
weakest form of the criterion this file provides. -/
theorem riemannHypothesis_of_frequently_abs_re_profileAverage_lt_one
    {mu : ℕ → Nat.Primes → ℝ}
    (hmu : IsCofinalUnitProfile primeHarmonicWeight mu)
    (hfreq : ∀ rho : XiDivisorSupport, ∃ r < 1, ∃ᶠ N in atTop,
      |(profileAverage mu N (routeRPrimeGammaXiCriticalWallField rho)).re| ≤ r) :
    RiemannHypothesis := by
  refine riemannHypothesis_of_forall_xiDivisorSupport_re_eq_half fun rho => ?_
  obtain ⟨r, hr, hf⟩ := hfreq rho
  exact xiDivisorSupport_re_eq_half_of_frequently_abs_re_profileAverage_le
    hmu rho hr hf

/-- Uniqueness of the prime-harmonic residue on the enlarged domain, where the
error is allowed to be summable or pointwise `o(1/p)`. -/
theorem primeHarmonicResidueMod_unique {a : Nat.Primes → ℂ} {c d : ℂ}
    (hc : HasReferenceResidueMod primeHarmonicWeight a c)
    (hd : HasReferenceResidueMod primeHarmonicWeight a d) : c = d := by
  obtain ⟨mu, hmu⟩ := exists_isCofinalUnitProfile_primeHarmonic nthPrimeEquiv
  exact HasReferenceResidueMod.unique_of_profile primeHarmonicWeight_nonneg hmu
    hc hd

/-- **RH from a robust sub-quantum gap.**  At each Xi divisor point the producer
may deliver any field agreeing with the first wall up to a summable or `o(1/p)`
error; a frequent sub-quantum bound on the producer's own averages suffices. -/
theorem riemannHypothesis_of_frequently_negligible_producer
    {mu : ℕ → Nat.Primes → ℝ}
    (hmu : IsCofinalUnitProfile primeHarmonicWeight mu)
    (hprod : ∀ rho : XiDivisorSupport, ∃ (a : Nat.Primes → ℂ) (r : ℝ), r < 1 ∧
      IsCofinitelyNegligible primeHarmonicWeight
        (fun p => a p - routeRPrimeGammaXiCriticalWallField rho p) ∧
      (∃ᶠ N in atTop, |(profileAverage mu N a).re| ≤ r)) :
    RiemannHypothesis := by
  refine riemannHypothesis_of_forall_xiDivisorSupport_re_eq_half fun rho => ?_
  obtain ⟨a, r, hr, hneg, hfreq⟩ := hprod rho
  rw [← primeDepthBVWoldXiCenteredRate_eq_zero_iff]
  exact eq_zero_of_frequently_abs_re_profileAverage_le_of_negligible_sub hmu hr
    hneg hfreq

/-- The criterion is not vacuous: bounded cofinal prime-harmonic profiles
exist. -/
theorem exists_isCofinalUnitProfile_primeHarmonic_nthPrime :
    ∃ mu : ℕ → Nat.Primes → ℝ, IsCofinalUnitProfile primeHarmonicWeight mu :=
  exists_isCofinalUnitProfile_primeHarmonic nthPrimeEquiv

end

end RHTower
