import GaloisForLFunctions.RHTower.ReflectedBiHeatPhaseHolomorphy
import GaloisForLFunctions.HTGeometry.LineJetTransfer

/-!
# Exact fixed-regulator reflected phase identity

On the central vertical line both complementary orders lie above the separate `L²` threshold, so
the existing polarized Fourier identity identifies the reflected phase integral with its double
series.  Holomorphy in the reflection parameter and the strip identity theorem propagate that
equality to the entire sharp reflected strip.
-/

open Complex Filter Set Topology
open HurwitzZeta MeasureTheory

namespace RHTower

noncomputable section

/-- Conjugating a finite positive-mode Dirichlet polynomial reverses its phase and conjugates its
order. -/
theorem dirichletTrunc_neg_eq_conj
    (b : ℂ) (N : ℕ) (theta : ℝ) :
    dirichletTrunc b N (-theta) =
      (starRingEnd ℂ) (dirichletTrunc ((starRingEnd ℂ) b) N theta) := by
  rw [dirichletTrunc, dirichletTrunc, sum_modeSet, sum_modeSet, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_mul, conj_ofReal_cpow (by positivity), map_neg, ← Complex.exp_conj]
  simp only [starRingEnd_apply]
  congr 1
  · simp
  · rw [Complex.star_def, map_mul, map_mul]
    simp

/-- Schwarz reflection of the boundary germ, proved from its convergent positive-mode truncations. -/
theorem phaseGerm_neg_eq_conj
    {b : ℂ} (hb : 0 < b.re) {theta : ℝ}
    (htheta : theta ∈ Ioo (-Real.pi) Real.pi) (htheta0 : theta ≠ 0) :
    phaseGerm b (-theta) =
      (starRingEnd ℂ) (phaseGerm ((starRingEnd ℂ) b) theta) := by
  have hleft := tendsto_dirichletTrunc (s := b) hb
    (θ := -theta) (by linarith [htheta.2]) (by linarith [htheta.1])
    (neg_ne_zero.mpr htheta0)
  have hbconj : 0 < ((starRingEnd ℂ) b).re := by simpa using hb
  have hright := tendsto_dirichletTrunc (s := (starRingEnd ℂ) b) hbconj
    (θ := theta) htheta.1 htheta.2.le htheta0
  have hrightStar : Tendsto
      (fun N : ℕ => (starRingEnd ℂ) (dirichletTrunc ((starRingEnd ℂ) b) N theta))
      atTop (nhds ((starRingEnd ℂ) (phaseGerm ((starRingEnd ℂ) b) theta))) :=
    (Complex.continuous_conj.tendsto _).comp hright
  have hfamilies : (fun N : ℕ => dirichletTrunc b N (-theta)) =
      fun N : ℕ => (starRingEnd ℂ) (dirichletTrunc ((starRingEnd ℂ) b) N theta) := by
    funext N
    exact dirichletTrunc_neg_eq_conj b N theta
  rw [← hfamilies] at hrightStar
  exact tendsto_nhds_unique hleft hrightStar

/-- On its integrable range, the directly reflected phase energy is the polarized energy with
conjugated right order. -/
theorem reflectedBiHeatFixedRegulatorPhaseEnergy_eq_polarized
    (Q : ReflectedBiHeatPositiveSlice) (z : ℂ)
    (hright : 0 < (Q.rightOrder z).re) :
    reflectedBiHeatFixedRegulatorPhaseEnergy Q z =
      polarizedHeatEnergy (Q.leftOrder z) ((starRingEnd ℂ) (Q.rightOrder z)) Q.x := by
  rw [reflectedBiHeatFixedRegulatorPhaseEnergy, polarizedHeatEnergy]
  congr 1
  apply integral_congr_ae
  have hneZero : ∀ᵐ theta ∂(volume : Measure ℝ), theta ≠ 0 :=
    MeasureTheory.compl_mem_ae_iff.mpr (measure_singleton (0 : ℝ))
  have hnePi : ∀ᵐ theta ∂(volume : Measure ℝ), theta ≠ Real.pi :=
    MeasureTheory.compl_mem_ae_iff.mpr (measure_singleton Real.pi)
  filter_upwards [self_mem_ae_restrict measurableSet_Ioc,
    MeasureTheory.ae_restrict_of_ae hneZero,
    MeasureTheory.ae_restrict_of_ae hnePi] with theta htheta htheta0 hthetaPi
  have hthetaOpen : theta ∈ Ioo (-Real.pi) Real.pi :=
    ⟨htheta.1, lt_of_le_of_ne htheta.2 hthetaPi⟩
  rw [reflectedBiHeatFixedRegulatorPhaseIntegrand,
    phaseGerm_neg_eq_conj hright hthetaOpen htheta0]

/-- Conjugating the polarized order converts every pair term to the asymmetric reflected term. -/
theorem polarizedHeatPairTerm_conj_eq_asymmetric
    (a b : ℂ) (x : ℝ) (p : ℕ × ℕ) :
    polarizedHeatPairTerm a ((starRingEnd ℂ) b) x p =
      asymmetricHeatPairTerm a b x p := by
  rw [polarizedHeatPairTerm, asymmetricHeatPairTerm,
    conj_ofReal_cpow (by positivity), map_neg]
  simp

/-- The square-indexed polarized series and the triangularly reindexed reflected series are
definitionally the same absolutely convergent family. -/
theorem polarizedHeatDoubleSum_conj_eq_reflectedBiHeatFixedRegulatorSum
    (Q : ReflectedBiHeatPositiveSlice) (z : ℂ) :
    polarizedHeatDoubleSum (Q.leftOrder z) ((starRingEnd ℂ) (Q.rightOrder z)) Q.x =
      reflectedBiHeatFixedRegulatorSum Q z := by
  rw [polarizedHeatDoubleSum, reflectedBiHeatFixedRegulatorSum]
  calc
    (∑' p : ℕ × ℕ, polarizedHeatPairTerm (Q.leftOrder z)
      ((starRingEnd ℂ) (Q.rightOrder z)) Q.x p) =
        ∑' p : ℕ × ℕ, asymmetricHeatPairTerm (Q.leftOrder z) (Q.rightOrder z) Q.x p := by
          apply tsum_congr
          intro p
          exact polarizedHeatPairTerm_conj_eq_asymmetric _ _ _ p
    _ = ∑' q : (ℕ × ℕ) ⊕ (ℕ × ℕ),
        asymmetricHeatPairTerm (Q.leftOrder z) (Q.rightOrder z) Q.x
          (upperLowerNatPairEquiv q) := by
          exact (Equiv.tsum_eq upperLowerNatPairEquiv
            (asymmetricHeatPairTerm (Q.leftOrder z) (Q.rightOrder z) Q.x)).symm
    _ = _ := by rfl

/-- The sharp reflected domain is the vertical strip centered at `1/2`. -/
theorem ReflectedBiHeatPositiveSlice.domain_eq_verticalStrip
    (Q : ReflectedBiHeatPositiveSlice) :
    Q.domain = GaloisForLFunctions.verticalStrip (1 / 2) ((1 - Q.delta) / 2) := by
  ext z
  rw [ReflectedBiHeatPositiveSlice.domain, GaloisForLFunctions.verticalStrip]
  simp only [Set.mem_setOf_eq, abs_lt]
  constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

/-- On the central line both shifted orders are strictly inside the classical separate-`L²`
strip. -/
theorem reflectedBiHeatFixedRegulatorPhaseEnergy_eq_sum_centralLine
    (Q : ReflectedBiHeatPositiveSlice) (t : ℝ) :
    reflectedBiHeatFixedRegulatorPhaseEnergy Q
        (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) =
      reflectedBiHeatFixedRegulatorSum Q (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) := by
  let z : ℂ := (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)
  have hzre : z.re = 1 / 2 := by simp [z]
  have hleftLower : 1 / 2 < (Q.leftOrder z).re := by
    rw [ReflectedBiHeatPositiveSlice.leftOrder]
    norm_num [Complex.add_re, Complex.div_re, hzre]
    linarith [Q.delta_pos]
  have hleftUpper : (Q.leftOrder z).re < 1 := by
    rw [ReflectedBiHeatPositiveSlice.leftOrder]
    norm_num [Complex.add_re, Complex.div_re, hzre]
    linarith [Q.delta_lt_one]
  have hrightLower : 1 / 2 < (Q.rightOrder z).re := by
    rw [ReflectedBiHeatPositiveSlice.rightOrder]
    norm_num [Complex.add_re, Complex.sub_re, Complex.div_re, hzre]
    linarith [Q.delta_pos]
  have hrightUpper : (Q.rightOrder z).re < 1 := by
    rw [ReflectedBiHeatPositiveSlice.rightOrder]
    norm_num [Complex.add_re, Complex.sub_re, Complex.div_re, hzre]
    linarith [Q.delta_lt_one]
  change reflectedBiHeatFixedRegulatorPhaseEnergy Q z =
    reflectedBiHeatFixedRegulatorSum Q z
  calc
    reflectedBiHeatFixedRegulatorPhaseEnergy Q z =
        polarizedHeatEnergy (Q.leftOrder z) ((starRingEnd ℂ) (Q.rightOrder z)) Q.x :=
      reflectedBiHeatFixedRegulatorPhaseEnergy_eq_polarized Q z
        (by linarith [hrightLower])
    _ = polarizedHeatDoubleSum (Q.leftOrder z)
        ((starRingEnd ℂ) (Q.rightOrder z)) Q.x := by
      apply polarizedHeatEnergy_eq_doubleSum hleftLower hleftUpper
      · simpa using hrightLower
      · simpa using hrightUpper
      · exact Q.x_pos
    _ = reflectedBiHeatFixedRegulatorSum Q z :=
      polarizedHeatDoubleSum_conj_eq_reflectedBiHeatFixedRegulatorSum Q z

/-- Exact fixed-positive-regulator phase/double-series identity on the full sharp reflected strip. -/
theorem reflectedBiHeatFixedRegulatorPhaseEnergy_eq_sum
    (Q : ReflectedBiHeatPositiveSlice) {z : ℂ} (hz : z ∈ Q.domain) :
    reflectedBiHeatFixedRegulatorPhaseEnergy Q z =
      reflectedBiHeatFixedRegulatorSum Q z := by
  let R : ℝ := (1 - Q.delta) / 2
  have hR : 0 < R := by dsimp [R]; linarith [Q.delta_lt_one]
  have hphase : DifferentiableOn ℂ (reflectedBiHeatFixedRegulatorPhaseEnergy Q)
      (GaloisForLFunctions.verticalStrip (1 / 2) R) := by
    rw [← Q.domain_eq_verticalStrip]
    exact differentiableOn_reflectedBiHeatFixedRegulatorPhaseEnergy Q
  have hsum : DifferentiableOn ℂ (reflectedBiHeatFixedRegulatorSum Q)
      (GaloisForLFunctions.verticalStrip (1 / 2) R) := by
    rw [← Q.domain_eq_verticalStrip]
    exact differentiableOn_reflectedBiHeatFixedRegulatorSum Q
  have heq := GaloisForLFunctions.eqOn_of_eqOn_line hR hphase hsum
    (reflectedBiHeatFixedRegulatorPhaseEnergy_eq_sum_centralLine Q)
  apply heq
  rwa [← Q.domain_eq_verticalStrip]

/-- Closed data for one point of the fixed-positive-regulator reflected domain. -/
structure ReflectedBiHeatFixedRegulatorPoint where
  slice : ReflectedBiHeatPositiveSlice
  z : ℂ
  z_mem : z ∈ slice.domain

/-- Premise-free exact regulated phase/double-series capstone. -/
theorem reflectedBiHeatFixedRegulatorPhaseEnergy_eq_sum_capstone :
    ∀ P : ReflectedBiHeatFixedRegulatorPoint,
      reflectedBiHeatFixedRegulatorPhaseEnergy P.slice P.z =
        reflectedBiHeatFixedRegulatorSum P.slice P.z := by
  intro P
  exact reflectedBiHeatFixedRegulatorPhaseEnergy_eq_sum P.slice P.z_mem

end

end RHTower
