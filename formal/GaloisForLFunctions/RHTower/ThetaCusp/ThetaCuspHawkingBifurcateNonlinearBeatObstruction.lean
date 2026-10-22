import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingSelfDualEinsteinDilationCarrier
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingTeukolskySingleSectorFrequencyNoGo
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingFullEinsteinGaugeFixedRadiationGram
import GaloisForLFunctions.RHTower.XiSpectralSupportCriterion

/-!
# Redshift-normalized nonlinear reflected/conjugate beat obstruction

The Birmingham--Mokhtari frequencies of the theta-reflected and Schwarz-conjugate
copies of an Xi divisor differ by `I * (re rho - 1 / 2)`.  After quotienting their
common causal redshift, the exact self-dual quadratic Einstein carrier is nonzero
at every divisor copy and its two relative time orientations have projective energy

`|C(rho)|^(2 : ℕ) * (exp (2 * delta * t) + exp (-2 * delta * t))`,

where `delta = re rho - 1 / 2`.  This normalized energy is uniformly bounded on
the full relative-time axis exactly when `delta = 0`.
-/

open Complex Real Set Filter Topology

namespace RHTower

noncomputable section

/-- Real growth rate of the reflected/conjugate Birmingham--Mokhtari beat. -/
def d4ThetaHawkingBMBeatRate (q : XiZeroCopy) : ℝ :=
  (q.1 : ℂ).re - 1 / 2

/-- Frequency difference between theta reflection and Schwarz conjugation. -/
def d4ThetaHawkingBMBeatDefect (q : XiZeroCopy) : ℂ :=
  thetaCuspHawkingTopologicalBlackHoleQNMPlus 0
      (xiSpectralPoint (xiZeroCopyReflectEquiv q)) -
    thetaCuspHawkingTopologicalBlackHoleQNMPlus 0
      (xiSpectralPoint (xiZeroCopyConjEquiv q))

/-- The exact Birmingham--Mokhtari beat defect is the imaginary critical-line tilt. -/
theorem d4ThetaHawkingBMBeatDefect_eq (q : XiZeroCopy) :
    d4ThetaHawkingBMBeatDefect q =
      Complex.I * (d4ThetaHawkingBMBeatRate q : ℂ) := by
  exact d4BMXiReflected_sub_conjugateQNMPlus_eq_tilt 0 q

/-- Exact self-dual quadratic Einstein coefficient carried by one Xi divisor copy. -/
def d4ThetaHawkingNonlinearBeatCarrier (amplitude : ℂ) (q : XiZeroCopy) : ℂ :=
  d4ThetaHawkingSelfDualQuadraticCarrierCoefficient amplitude (xiSpectralPoint q)

/-- One orientation of the common-redshift-normalized reflected/conjugate beat. -/
def d4ThetaHawkingOrientedNonlinearBeat
    (amplitude : ℂ) (q : XiZeroCopy) (t : ℝ) : ℂ :=
  d4ThetaHawkingNonlinearBeatCarrier amplitude q *
    Complex.exp (-Complex.I * d4ThetaHawkingBMBeatDefect q * (t : ℂ))

/-- Off-line frequency tilt becomes real exponential drift after common-redshift removal. -/
theorem d4ThetaHawkingOrientedNonlinearBeat_eq
    (amplitude : ℂ) (q : XiZeroCopy) (t : ℝ) :
    d4ThetaHawkingOrientedNonlinearBeat amplitude q t =
      d4ThetaHawkingNonlinearBeatCarrier amplitude q *
        (Real.exp (d4ThetaHawkingBMBeatRate q * t) : ℂ) := by
  rw [d4ThetaHawkingOrientedNonlinearBeat, d4ThetaHawkingBMBeatDefect_eq]
  have hexponent :
      -Complex.I * (Complex.I * (d4ThetaHawkingBMBeatRate q : ℂ)) * (t : ℂ) =
        ((d4ThetaHawkingBMBeatRate q * t : ℝ) : ℂ) := by
    calc
      -Complex.I * (Complex.I * (d4ThetaHawkingBMBeatRate q : ℂ)) * (t : ℂ) =
          -(Complex.I * Complex.I) *
            (d4ThetaHawkingBMBeatRate q : ℂ) * (t : ℂ) := by ring
      _ = ((d4ThetaHawkingBMBeatRate q * t : ℝ) : ℂ) := by
        rw [Complex.I_mul_I]
        push_cast
        ring
  rw [hexponent, ← Complex.ofReal_exp]

/-- Projective energy of both orientations of the redshift-normalized beat. -/
def d4ThetaHawkingBifurcateNonlinearBeatEnergy
    (amplitude : ℂ) (q : XiZeroCopy) (t : ℝ) : ℝ :=
  Complex.normSq (d4ThetaHawkingOrientedNonlinearBeat amplitude q t) +
    Complex.normSq (d4ThetaHawkingOrientedNonlinearBeat amplitude q (-t))

/-- Uniform two-sided regularity of one redshift-normalized nonlinear divisor beat. -/
def D4ThetaHawkingBifurcateNonlinearBeatRegular
    (amplitude : ℂ) (q : XiZeroCopy) : Prop :=
  ∃ M : ℝ, ∀ t : ℝ,
    d4ThetaHawkingBifurcateNonlinearBeatEnergy amplitude q t ≤ M

private lemma normSq_real_exp (x : ℝ) :
    Complex.normSq (Real.exp x : ℂ) = Real.exp (2 * x) := by
  rw [Complex.normSq_ofReal, ← Real.exp_add]
  ring_nf

/-- Closed optical-energy decomposition of the two horizon orientations. -/
theorem d4ThetaHawkingBifurcateNonlinearBeatEnergy_eq
    (amplitude : ℂ) (q : XiZeroCopy) (t : ℝ) :
    d4ThetaHawkingBifurcateNonlinearBeatEnergy amplitude q t =
      Complex.normSq (d4ThetaHawkingNonlinearBeatCarrier amplitude q) *
        (Real.exp (2 * d4ThetaHawkingBMBeatRate q * t) +
          Real.exp (-2 * d4ThetaHawkingBMBeatRate q * t)) := by
  rw [d4ThetaHawkingBifurcateNonlinearBeatEnergy,
    d4ThetaHawkingOrientedNonlinearBeat_eq,
    d4ThetaHawkingOrientedNonlinearBeat_eq, Complex.normSq_mul,
    Complex.normSq_mul, normSq_real_exp, normSq_real_exp]
  ring_nf

/-- A nonzero exact Einstein carrier is bifurcate-regular exactly on the critical line. -/
theorem d4ThetaHawkingBifurcateNonlinearBeatRegular_iff
    {amplitude : ℂ} (ha : amplitude ≠ 0) (q : XiZeroCopy) :
    D4ThetaHawkingBifurcateNonlinearBeatRegular amplitude q ↔
      (q.1 : ℂ).re = 1 / 2 := by
  let c : ℝ := Complex.normSq (d4ThetaHawkingNonlinearBeatCarrier amplitude q)
  have hcarrier : d4ThetaHawkingNonlinearBeatCarrier amplitude q ≠ 0 :=
    d4ThetaHawkingSelfDualQuadraticCarrierCoefficient_xi_ne_zero ha q
  have hc : 0 < c := (Complex.normSq_pos).2 hcarrier
  constructor
  · rintro ⟨M, hM⟩
    by_contra hline
    have hdelta : d4ThetaHawkingBMBeatRate q ≠ 0 := by
      intro hzero
      apply hline
      unfold d4ThetaHawkingBMBeatRate at hzero
      linarith
    let a : ℝ := 2 * d4ThetaHawkingBMBeatRate q ^ (2 : ℕ)
    have haPos : 0 < a := by
      dsimp [a]
      positivity
    have hlin : Tendsto (fun n : ℕ => a * (n : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.const_mul_atTop haPos
    have hexp : Tendsto (fun n : ℕ => Real.exp (a * (n : ℝ))) atTop atTop :=
      Real.tendsto_exp_atTop.comp hlin
    have hscaled : Tendsto
        (fun n : ℕ => c * Real.exp (a * (n : ℝ))) atTop atTop :=
      hexp.const_mul_atTop hc
    obtain ⟨n, hn⟩ := (Filter.tendsto_atTop.1 hscaled (M + 1)).exists
    have hbound := hM ((n : ℝ) * d4ThetaHawkingBMBeatRate q)
    rw [d4ThetaHawkingBifurcateNonlinearBeatEnergy_eq] at hbound
    have hfirst :
        c * Real.exp (a * (n : ℝ)) ≤
          c *
            (Real.exp
                (2 * d4ThetaHawkingBMBeatRate q *
                  ((n : ℝ) * d4ThetaHawkingBMBeatRate q)) +
              Real.exp
                (-2 * d4ThetaHawkingBMBeatRate q *
                  ((n : ℝ) * d4ThetaHawkingBMBeatRate q))) := by
      have hnonneg :
          0 ≤ c *
            Real.exp
              (-2 * d4ThetaHawkingBMBeatRate q *
                ((n : ℝ) * d4ThetaHawkingBMBeatRate q)) := by
        positivity
      dsimp [a]
      rw [show 2 * d4ThetaHawkingBMBeatRate q ^ (2 : ℕ) * (n : ℝ) =
          2 * d4ThetaHawkingBMBeatRate q *
            ((n : ℝ) * d4ThetaHawkingBMBeatRate q) by ring]
      linarith
    linarith
  · intro hline
    refine ⟨2 * Complex.normSq
      (d4ThetaHawkingNonlinearBeatCarrier amplitude q), ?_⟩
    intro t
    rw [d4ThetaHawkingBifurcateNonlinearBeatEnergy_eq]
    have hrate : d4ThetaHawkingBMBeatRate q = 0 := by
      unfold d4ThetaHawkingBMBeatRate
      linarith
    rw [hrate]
    norm_num
    rw [mul_comm]

/-- Gauge-fixed radiation map applied to the normalized direct beat and an arbitrary
orthogonal-helicity history. -/
def d4ThetaHawkingFullNonlinearBeatRadiation
    (amplitude : ℂ) (q : XiZeroCopy) (mixing : ℝ → ℂ) (t : ℝ) :
    EuclideanSpace ℂ (Fin 4) :=
  d4BMGaugeFixedSecondHarmonicRadiationMap q
    (d4ThetaHawkingOrientedNonlinearBeat amplitude q t, mixing t)

/-- Two-sided projective energy after applying the gauge-fixed radiation map. -/
def d4ThetaHawkingFullBifurcateNonlinearBeatEnergy
    (amplitude : ℂ) (q : XiZeroCopy) (mixing : ℝ → ℂ) (t : ℝ) : ℝ :=
  ‖d4ThetaHawkingFullNonlinearBeatRadiation amplitude q mixing t‖ ^ (2 : ℕ) +
    ‖d4ThetaHawkingFullNonlinearBeatRadiation amplitude q mixing (-t)‖ ^ (2 : ℕ)

/-- Uniform normalized regularity after arbitrary orthogonal-helicity mixing. -/
def D4ThetaHawkingFullBifurcateNonlinearBeatRegular
    (amplitude : ℂ) (q : XiZeroCopy) (mixing : ℝ → ℂ) : Prop :=
  ∃ M : ℝ, ∀ t : ℝ,
    d4ThetaHawkingFullBifurcateNonlinearBeatEnergy amplitude q mixing t ≤ M

private lemma d4ThetaHawkingDirectBeatRadiation_eq
    (amplitude : ℂ) (q : XiZeroCopy) (t : ℝ) :
    d4BMGaugeFixedSecondHarmonicRadiationMap q
        (d4ThetaHawkingOrientedNonlinearBeat amplitude q t, 0) =
      (Real.exp (d4ThetaHawkingBMBeatRate q * t) : ℂ) •
        d4BMGaugeFixedSecondHarmonicRadiationMap q
          (d4ThetaHawkingNonlinearBeatCarrier amplitude q, 0) := by
  rw [d4ThetaHawkingOrientedNonlinearBeat_eq]
  simpa [smul_eq_mul, mul_comm] using
    (map_smul (d4BMGaugeFixedSecondHarmonicRadiationMap q)
      (Real.exp (d4ThetaHawkingBMBeatRate q * t) : ℂ)
      (d4ThetaHawkingNonlinearBeatCarrier amplitude q, 0))

private lemma d4ThetaHawkingDirectBeatRadiation_norm_sq_eq
    (amplitude : ℂ) (q : XiZeroCopy) (t : ℝ) :
    ‖d4BMGaugeFixedSecondHarmonicRadiationMap q
        (d4ThetaHawkingOrientedNonlinearBeat amplitude q t, 0)‖ ^ (2 : ℕ) =
      Real.exp (2 * d4ThetaHawkingBMBeatRate q * t) *
        ‖d4BMGaugeFixedSecondHarmonicRadiationMap q
          (d4ThetaHawkingNonlinearBeatCarrier amplitude q, 0)‖ ^ (2 : ℕ) := by
  rw [d4ThetaHawkingDirectBeatRadiation_eq, norm_smul, Complex.norm_real,
    Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos (d4ThetaHawkingBMBeatRate q * t)), mul_pow]
  congr 1
  · rw [show Real.exp (d4ThetaHawkingBMBeatRate q * t) ^ (2 : ℕ) =
      Real.exp (d4ThetaHawkingBMBeatRate q * t) *
        Real.exp (d4ThetaHawkingBMBeatRate q * t) by ring,
      ← Real.exp_add]
    congr 1
    ring

/-- Full optical energy is forced direct energy plus nonnegative orthogonal-helicity energy. -/
theorem d4ThetaHawkingFullBifurcateNonlinearBeatEnergy_decomposition
    (amplitude : ℂ) (q : XiZeroCopy) (mixing : ℝ → ℂ) (t : ℝ) :
    d4ThetaHawkingFullBifurcateNonlinearBeatEnergy amplitude q mixing t =
      ‖d4BMGaugeFixedSecondHarmonicRadiationMap q
        (d4ThetaHawkingOrientedNonlinearBeat amplitude q t, 0)‖ ^ (2 : ℕ) +
      ‖d4BMGaugeFixedSecondHarmonicRadiationMap q (0, mixing t)‖ ^ (2 : ℕ) +
      (‖d4BMGaugeFixedSecondHarmonicRadiationMap q
        (d4ThetaHawkingOrientedNonlinearBeat amplitude q (-t), 0)‖ ^ (2 : ℕ) +
      ‖d4BMGaugeFixedSecondHarmonicRadiationMap q (0, mixing (-t))‖ ^ (2 : ℕ)) := by
  rw [d4ThetaHawkingFullBifurcateNonlinearBeatEnergy,
    d4ThetaHawkingFullNonlinearBeatRadiation,
    d4ThetaHawkingFullNonlinearBeatRadiation,
    d4BMGaugeFixedSecondHarmonicRadiation_norm_sq_decomposition q
      (d4ThetaHawkingOrientedNonlinearBeat amplitude q t) (mixing t),
    d4BMGaugeFixedSecondHarmonicRadiation_norm_sq_decomposition q
      (d4ThetaHawkingOrientedNonlinearBeat amplitude q (-t)) (mixing (-t))]

/-- Arbitrary orthogonal-helicity dynamics cannot cancel the nonzero direct Einstein beat. -/
theorem d4ThetaHawkingFullBifurcateNonlinearBeatRegular_forces_critical
    {amplitude : ℂ} (ha : amplitude ≠ 0) (q : XiZeroCopy) (mixing : ℝ → ℂ) :
    D4ThetaHawkingFullBifurcateNonlinearBeatRegular amplitude q mixing →
      (q.1 : ℂ).re = 1 / 2 := by
  rintro ⟨M, hM⟩
  let c : ℝ :=
    ‖d4BMGaugeFixedSecondHarmonicRadiationMap q
      (d4ThetaHawkingNonlinearBeatCarrier amplitude q, 0)‖ ^ (2 : ℕ)
  have hbase :
      d4BMGaugeFixedSecondHarmonicRadiationMap q
        (d4ThetaHawkingNonlinearBeatCarrier amplitude q, 0) ≠ 0 :=
    d4BMGaugeFixedSecondHarmonicRadiation_ne_zero_of_direct_ne_zero q
      (d4ThetaHawkingSelfDualQuadraticCarrierCoefficient_xi_ne_zero ha q) 0
  have hc : 0 < c := by
    dsimp [c]
    positivity
  by_contra hline
  have hdelta : d4ThetaHawkingBMBeatRate q ≠ 0 := by
    intro hzero
    apply hline
    unfold d4ThetaHawkingBMBeatRate at hzero
    linarith
  let a : ℝ := 2 * d4ThetaHawkingBMBeatRate q ^ (2 : ℕ)
  have haPos : 0 < a := by
    dsimp [a]
    positivity
  have hlin : Tendsto (fun n : ℕ => a * (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop haPos
  have hexp : Tendsto (fun n : ℕ => Real.exp (a * (n : ℝ))) atTop atTop :=
    Real.tendsto_exp_atTop.comp hlin
  have hscaled : Tendsto
      (fun n : ℕ => c * Real.exp (a * (n : ℝ))) atTop atTop :=
    hexp.const_mul_atTop hc
  obtain ⟨n, hn⟩ := (Filter.tendsto_atTop.1 hscaled (M + 1)).exists
  have hbound := hM ((n : ℝ) * d4ThetaHawkingBMBeatRate q)
  rw [d4ThetaHawkingFullBifurcateNonlinearBeatEnergy_decomposition] at hbound
  have hfirst :
      c * Real.exp (a * (n : ℝ)) ≤
        ‖d4BMGaugeFixedSecondHarmonicRadiationMap q
          (d4ThetaHawkingOrientedNonlinearBeat amplitude q
            ((n : ℝ) * d4ThetaHawkingBMBeatRate q), 0)‖ ^ (2 : ℕ) := by
    rw [d4ThetaHawkingDirectBeatRadiation_norm_sq_eq]
    dsimp [a, c]
    rw [show 2 * d4ThetaHawkingBMBeatRate q ^ (2 : ℕ) * (n : ℝ) =
      2 * d4ThetaHawkingBMBeatRate q *
        ((n : ℝ) * d4ThetaHawkingBMBeatRate q) by ring]
    rw [mul_comm]
  have hrest :
      0 ≤
        ‖d4BMGaugeFixedSecondHarmonicRadiationMap q
          (0, mixing ((n : ℝ) * d4ThetaHawkingBMBeatRate q))‖ ^ (2 : ℕ) +
        (‖d4BMGaugeFixedSecondHarmonicRadiationMap q
          (d4ThetaHawkingOrientedNonlinearBeat amplitude q
            (-((n : ℝ) * d4ThetaHawkingBMBeatRate q)), 0)‖ ^ (2 : ℕ) +
        ‖d4BMGaugeFixedSecondHarmonicRadiationMap q
          (0, mixing (-((n : ℝ) * d4ThetaHawkingBMBeatRate q)))‖ ^ (2 : ℕ)) := by
    positivity
  linarith

/-- Every Xi-labelled normalized nonlinear beat is uniformly regular. -/
def D4ThetaHawkingAllBifurcateNonlinearBeatsRegular : Prop :=
  ∀ q : XiZeroCopy, D4ThetaHawkingBifurcateNonlinearBeatRegular 1 q

/-- Global normalized nonlinear-beat regularity is equivalent to the Riemann hypothesis. -/
theorem d4ThetaHawkingAllBifurcateNonlinearBeatsRegular_iff_riemannHypothesis :
    D4ThetaHawkingAllBifurcateNonlinearBeatsRegular ↔ RiemannHypothesis := by
  constructor
  · intro hregular
    apply riemannHypothesis_of_xiSpectralPointSupport_im_eq_zero
    intro rho
    have hm : 0 < ((MeromorphicOn.divisor xi Set.univ) (rho : ℂ)).toNat :=
      xiSupportMultiplicity_pos rho
    let q : XiZeroCopy := ⟨rho, ⟨0, hm⟩⟩
    have hline : (rho : ℂ).re = 1 / 2 := by
      exact (d4ThetaHawkingBifurcateNonlinearBeatRegular_iff (by norm_num) q).1
        (hregular q)
    exact (xiSpectralPointSupport_im_eq_zero_iff rho).2 hline
  · intro hRH q
    exact (d4ThetaHawkingBifurcateNonlinearBeatRegular_iff (by norm_num) q).2
      (xi_divisor_support_re_eq_half_of_rh hRH q.1)

/-- Any normalized gauge-fixed radiation history that is regular in every divisor sector forces
RH, independently of its orthogonal-helicity component. -/
theorem riemannHypothesis_of_d4ThetaHawkingFullBifurcateNonlinearBeatRegular
    (mixing : XiZeroCopy → ℝ → ℂ)
    (hregular : ∀ q : XiZeroCopy,
      D4ThetaHawkingFullBifurcateNonlinearBeatRegular 1 q (mixing q)) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_xiSpectralPointSupport_im_eq_zero
  intro rho
  have hm : 0 < ((MeromorphicOn.divisor xi Set.univ) (rho : ℂ)).toNat :=
    xiSupportMultiplicity_pos rho
  let q : XiZeroCopy := ⟨rho, ⟨0, hm⟩⟩
  have hline : (rho : ℂ).re = 1 / 2 :=
    d4ThetaHawkingFullBifurcateNonlinearBeatRegular_forces_critical
      (by norm_num) q (mixing q) (hregular q)
  exact (xiSpectralPointSupport_im_eq_zero_iff rho).2 hline

end

end RHTower
