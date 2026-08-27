import GaloisForLFunctions.HTGeometry.ProjectiveOperatorNormReturnTarget
import GaloisForLFunctions.HTGeometry.CompletedOccupationHardGapLaw
import GaloisForLFunctions.HTGeometry.OneSidedCaptureDensity
import GaloisForLFunctions.HTGeometry.ContinuousPlateauGrid
import GaloisForLFunctions.HTGeometry.ThermodynamicProjectiveRecurrenceExtinctionLaw
import GaloisForLFunctions.HTGeometry.ThermodynamicSameFieldUHFRecurrenceComplexityLaw

open Filter MeasureTheory Set Topology
open scoped Matrix.Norms.L2Operator

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open PrimeQuasiLocalCharge

variable {d : Type} [Fintype d] [DecidableEq d] [Nonempty d]

/-- Any scalar approximation controls its reference spectral coordinate. -/
theorem norm_anchorPhase_sub_le_unitaryEvolution_sub_scalar
    {H : Matrix d d ℂ} (hH : H.IsHermitian) (a : d) (t : ℝ) (c : ℂ) :
    ‖anchorPhase hH.eigenvalues a t - c‖ ≤
      ‖unitaryEvolution H t - c • (1 : Matrix d d ℂ)‖ := by
  set V : Matrix d d ℂ := (hH.eigenvectorUnitary : Matrix d d ℂ) with hVdef
  have hV : V ∈ unitary (Matrix d d ℂ) := hH.eigenvectorUnitary.2
  have hVstar : V * star V = 1 := (Unitary.mem_iff.mp hV).2
  have hone : c • (1 : Matrix d d ℂ) =
      V * Matrix.diagonal (fun _ : d => c) * star V := by
    rw [← smul_one_eq_diagonal_const c, Matrix.mul_smul, Matrix.mul_one,
      Matrix.smul_mul, hVstar]
  have hdiff : unitaryEvolution H t - c • (1 : Matrix d d ℂ) =
      V * Matrix.diagonal
        (fun i : d => Complex.exp (-(Complex.I * (t * hH.eigenvalues i))) - c) * star V := by
    rw [unitaryEvolution_spectral hH t, hone, ← Matrix.sub_mul, ← Matrix.mul_sub,
      ← Matrix.diagonal_sub]
  rw [hdiff, l2_opNorm_unitary_conj_eq hV, Matrix.l2_opNorm_diagonal]
  change ‖Complex.exp (-(Complex.I * (t * hH.eigenvalues a))) - c‖ ≤
    ‖fun i : d => Complex.exp (-(Complex.I * (t * hH.eigenvalues i))) - c‖
  exact norm_le_pi_norm
    (fun i : d => Complex.exp (-(Complex.I * (t * hH.eigenvalues i))) - c) a

/-- Approximation by any scalar unitary implies approximation by the reference eigenphase at
twice the radius. -/
theorem norm_unitaryEvolution_sub_anchorPhase_le_two_mul_of_scalar
    {H : Matrix d d ℂ} (hH : H.IsHermitian) (a : d) (t : ℝ) (c : ℂ) :
    ‖unitaryEvolution H t - anchorPhase hH.eigenvalues a t •
        (1 : Matrix d d ℂ)‖ ≤
      2 * ‖unitaryEvolution H t - c • (1 : Matrix d d ℂ)‖ := by
  let anchor := anchorPhase hH.eigenvalues a t
  calc
    ‖unitaryEvolution H t - anchor • (1 : Matrix d d ℂ)‖ ≤
        ‖unitaryEvolution H t - c • (1 : Matrix d d ℂ)‖ +
          ‖c • (1 : Matrix d d ℂ) - anchor • (1 : Matrix d d ℂ)‖ := by
      have hsum : unitaryEvolution H t - anchor • (1 : Matrix d d ℂ) =
          (unitaryEvolution H t - c • (1 : Matrix d d ℂ)) +
            (c • (1 : Matrix d d ℂ) - anchor • (1 : Matrix d d ℂ)) := by module
      rw [hsum]
      exact norm_add_le _ _
    _ = ‖unitaryEvolution H t - c • (1 : Matrix d d ℂ)‖ + ‖c - anchor‖ := by
      congr 1
      rw [← sub_smul, norm_smul, norm_one, mul_one]
    _ ≤ 2 * ‖unitaryEvolution H t - c • (1 : Matrix d d ℂ)‖ := by
      have ha : ‖c - anchor‖ ≤
          ‖unitaryEvolution H t - c • (1 : Matrix d d ℂ)‖ := by
        simpa [anchor, norm_sub_rev] using
          norm_anchorPhase_sub_le_unitaryEvolution_sub_scalar hH a t c
      linarith

/-- Times at which the evolution is close in operator norm to some scalar unitary. -/
def scalarUnitaryReturnTimes (H : Matrix d d ℂ) (eps : ℝ) : Set ℝ :=
  {t | ∃ c : ℂ, ‖c‖ = 1 ∧
    ‖unitaryEvolution H t - c • (1 : Matrix d d ℂ)‖ ≤ eps}

theorem scalarUnitaryReturnTimes_subset_projectiveReturnTimes
    {H : Matrix d d ℂ} (hH : H.IsHermitian) (a : d) (eps : ℝ) :
    scalarUnitaryReturnTimes H eps ⊆ projectiveReturnTimes H hH a (2 * eps) := by
  rintro t ⟨c, _hc, hclose⟩
  exact (norm_unitaryEvolution_sub_anchorPhase_le_two_mul_of_scalar hH a t c).trans
    (mul_le_mul_of_nonneg_left hclose (by norm_num))

/-- One-sided time probability of anchored operator returns equals phase-torus probability. -/
theorem windowProbability_projectiveReturnTimes
    {H : Matrix d d ℂ} (hH : H.IsHermitian) (a : d)
    {eps : ℝ} (heps : 0 ≤ eps) (T : ℝ) :
    (windowProbabilityMeasure T : Measure ℝ) (projectiveReturnTimes H hH a eps) =
      (clockPhaseWindowLaw (projectiveFrequency hH.eigenvalues a) T :
        Measure (UnitAddTorus {i : d // i ≠ a}))
          (anchoredProjectiveReturnTarget eps) := by
  rw [projectiveReturnTimes_eq_preimage hH a heps, clockPhaseWindowLaw,
    ProbabilityMeasure.toMeasure_map,
    Measure.map_apply (finiteClockPhasePoint_continuous _).measurable
      (isClosed_anchoredProjectiveReturnTarget eps).measurableSet]

/-- Exact Haar mass bounds completed one-sided anchored operator returns. -/
theorem limsup_windowProbability_projectiveReturnTimes_le
    {H : Matrix d d ℂ} (hH : H.IsHermitian)
    (hmax : MaximallyProjectiveEnergy hH.eigenvalues) (a : d)
    {eps : ℝ} (heps0 : 0 ≤ eps) (heps2 : eps < 2) :
    atTop.limsup (fun T => (windowProbabilityMeasure T : Measure ℝ)
      (projectiveReturnTimes H hH a eps)) ≤
      ENNReal.ofReal (projectiveReturnDensityBase eps ^ Fintype.card {i : d // i ≠ a}) := by
  have hind : RationallyIndependentFrequency
      (projectiveFrequency hH.eigenvalues a) :=
    maximallyProjectiveEnergy_projectiveFrequency_independent hH.eigenvalues hmax a
  have hmain := oneSided_closedTarget_limsup_le_volume
    (projectiveFrequency hH.eigenvalues a) hind
    (isClosed_anchoredProjectiveReturnTarget eps)
  have hvol : (volume : Measure (UnitAddTorus {i : d // i ≠ a}))
      (anchoredProjectiveReturnTarget eps) =
      ENNReal.ofReal (2 * Real.arcsin (eps / 2) / Real.pi) ^
        Fintype.card {i : d // i ≠ a} := by
    rw [← finiteTorusHaarProbabilityMeasure_toMeasure_eq_volume]
    exact finiteTorusHaarProbabilityMeasure_anchoredProjectiveReturnTarget heps0 heps2
  rw [hvol] at hmain
  have hbase : 0 ≤ 2 * Real.arcsin (eps / 2) / Real.pi := by
    exact div_nonneg (mul_nonneg (by norm_num) (Real.arcsin_nonneg.mpr (by linarith)))
      Real.pi_pos.le
  rw [← ENNReal.ofReal_pow hbase] at hmain
  simpa only [windowProbability_projectiveReturnTimes hH a heps0,
    projectiveReturnDensityBase] using hmain

/-- Sparse exact projective-return occupation forces arbitrarily late intervals without any
scalar-unitary operator-norm return. -/
theorem maximallyProjective_scalarUnitaryReturnTimes_late_deserts
    {H : Matrix d d ℂ} (hH : H.IsHermitian)
    (hmax : MaximallyProjectiveEnergy hH.eigenvalues) (a : d)
    {speed epsn epsw W : ℝ} (hspeed0 : 0 < speed) (hHspeed : ‖H‖ ≤ speed)
    (hepsn0 : 0 ≤ epsn) (hgap : epsn < epsw) (hW : 0 ≤ W)
    (htwoepsw : 2 * epsw < 2)
    (hpack : projectiveReturnDensityBase (2 * epsw) ^
        Fintype.card {i : d // i ≠ a} <
      ((epsw - epsn) / speed) / (W + (epsw - epsn) / speed)) :
    ∀ A0 : ℝ, 0 ≤ A0 → ∃ u : ℝ, A0 ≤ u ∧
      Icc u (u + W) ∩ scalarUnitaryReturnTimes H epsn = ∅ := by
  let b : ℝ := projectiveReturnDensityBase (2 * epsw) ^
    Fintype.card {i : d // i ≠ a}
  let delta : ℝ := (epsw - epsn) / speed
  have hepsw0 : 0 ≤ epsw := (hepsn0.trans hgap.le)
  have htwoepsw0 : 0 ≤ 2 * epsw := mul_nonneg (by norm_num) hepsw0
  have hb : 0 ≤ b := pow_nonneg (projectiveReturnDensityBase_pos
    (mul_pos (by norm_num) (lt_of_le_of_lt hepsn0 hgap))).le _
  have hdelta : 0 < delta := div_pos (sub_pos.mpr hgap) hspeed0
  have hlim := limsup_windowProbability_projectiveReturnTimes_le hH hmax a
    htwoepsw0 htwoepsw
  apply exists_late_interval_disjoint_of_limsup_windowProbability_le
    (scalarUnitaryReturnTimes H epsn) (projectiveReturnTimes H hH a (2 * epsw))
    hdelta hW hb
  · rintro t ⟨c, hc, htc⟩ v hv
    apply scalarUnitaryReturnTimes_subset_projectiveReturnTimes hH a epsw
    refine ⟨c, hc, ?_⟩
    calc
      ‖unitaryEvolution H v - c • (1 : Matrix d d ℂ)‖ ≤
          ‖unitaryEvolution H v - unitaryEvolution H t‖ +
            ‖unitaryEvolution H t - c • (1 : Matrix d d ℂ)‖ := by
        have hsum : unitaryEvolution H v - c • (1 : Matrix d d ℂ) =
            (unitaryEvolution H v - unitaryEvolution H t) +
              (unitaryEvolution H t - c • (1 : Matrix d d ℂ)) := by module
        rw [hsum]
        exact norm_add_le _ _
      _ ≤ speed * |v - t| + epsn := by
        gcongr
        exact (norm_unitaryEvolution_time_sub_le hH v t).trans
          (mul_le_mul_of_nonneg_right hHspeed (abs_nonneg _))
      _ ≤ speed * delta + epsn := by
        gcongr
        rw [abs_of_pos (sub_pos.mpr hv.1)]
        linarith [hv.2]
      _ = epsw := by
        dsimp [delta]
        field_simp
        ring
  · simpa only [b] using hlim
  · simpa only [b, delta] using hpack

theorem norm_embeddedInfinitePathPrefixHamiltonian
    (p : InfinitePathLabel → ℝ) (k : ℕ) :
    ‖embeddedInfinitePathPrefixHamiltonian p k‖ =
      ‖pathHamiltonian (infinitePathPrefixShell k p)‖ := by
  rw [embeddedInfinitePathPrefixHamiltonian, norm_matrixAFStageToUHF,
    norm_qubitStageMatrix]

theorem eventually_norm_pathHamiltonian_infinitePathPrefixShell_le
    {p : InfinitePathLabel → ℝ} (hp : Summable (fun i => |p i|)) :
    ∀ᶠ k : ℕ in atTop,
      ‖pathHamiltonian (infinitePathPrefixShell k p)‖ ≤
        ‖infinitePathUHFHamiltonian p‖ + 1 := by
  obtain ⟨K, hK⟩ := Metric.tendsto_atTop.mp
    (tendsto_embeddedInfinitePathPrefixHamiltonian hp) 1 (by norm_num)
  refine eventually_atTop.2 ⟨K, fun k hk => ?_⟩
  have hdist := hK k hk
  rw [dist_eq_norm] at hdist
  rw [← norm_embeddedInfinitePathPrefixHamiltonian p k]
  calc
    ‖embeddedInfinitePathPrefixHamiltonian p k‖ =
        ‖(embeddedInfinitePathPrefixHamiltonian p k - infinitePathUHFHamiltonian p) +
          infinitePathUHFHamiltonian p‖ := by congr 1; module
    _ ≤ ‖embeddedInfinitePathPrefixHamiltonian p k - infinitePathUHFHamiltonian p‖ +
          ‖infinitePathUHFHamiltonian p‖ := norm_add_le _ _
    _ ≤ ‖infinitePathUHFHamiltonian p‖ + 1 := by linarith

/-- One fixed operator-norm resolution used by the thermodynamic desert law. -/
def thermodynamicProjectiveDesertRadius : ℝ := 1 / 20

private def thermodynamicProjectiveWideRadius : ℝ := 1 / 10

private def infinitePathPrefixReference (k : ℕ) : Fin (k + 3) → Bool :=
  fun _ => false

theorem card_infinitePathPrefix_ne_reference (k : ℕ) :
    Fintype.card {i : (Fin (k + 3) → Bool) // i ≠ infinitePathPrefixReference k} =
      2 ^ (k + 3) - 1 := by
  simp

/-- Exact completed occupation bound used by the prefix desert law. -/
def thermodynamicProjectiveDesertDensity (k : ℕ) : ℝ :=
  quditPathProjectiveReturnDensity 2 (2 * thermodynamicProjectiveWideRadius) (k + 3)

theorem thermodynamicProjectiveDesertDensity_pos (k : ℕ) :
    0 < thermodynamicProjectiveDesertDensity k := by
  exact pow_pos (projectiveReturnDensityBase_pos
    (by norm_num [thermodynamicProjectiveWideRadius])) _

theorem thermodynamicProjectiveDesertDensity_tendsto_zero :
    Tendsto thermodynamicProjectiveDesertDensity atTop (nhds 0) := by
  exact (quditPathProjectiveReturnDensity_tendsto_zero
    (q := 2) (by norm_num) (ε := 2 * thermodynamicProjectiveWideRadius)
    (by norm_num [thermodynamicProjectiveWideRadius])
    (by norm_num [thermodynamicProjectiveWideRadius])).comp
      (tendsto_add_atTop_nat 3)

theorem thermodynamicProjectiveDesertDensity_eq_card (k : ℕ) :
    thermodynamicProjectiveDesertDensity k =
      projectiveReturnDensityBase (2 * thermodynamicProjectiveWideRadius) ^
        Fintype.card {i : (Fin (k + 3) → Bool) // i ≠ infinitePathPrefixReference k} := by
  rw [thermodynamicProjectiveDesertDensity, quditPathProjectiveReturnDensity,
    card_infinitePathPrefix_ne_reference]

/-- Uniform time thickness inherited from the bounded infinite-volume Hamiltonian. -/
def thermodynamicProjectiveDesertMesh (p : InfinitePathLabel → ℝ) : ℝ :=
  (thermodynamicProjectiveWideRadius - thermodynamicProjectiveDesertRadius) /
    (‖infinitePathUHFHamiltonian p‖ + 2)

theorem thermodynamicProjectiveDesertMesh_pos (p : InfinitePathLabel → ℝ) :
    0 < thermodynamicProjectiveDesertMesh p := by
  unfold thermodynamicProjectiveDesertMesh thermodynamicProjectiveWideRadius
    thermodynamicProjectiveDesertRadius
  positivity

/-- Explicit inverse-occupation length certified to be projective-return-free. -/
def thermodynamicProjectiveDesertWidth (p : InfinitePathLabel → ℝ) (k : ℕ) : ℝ :=
  thermodynamicProjectiveDesertMesh p /
      (2 * thermodynamicProjectiveDesertDensity k) -
    thermodynamicProjectiveDesertMesh p

theorem thermodynamicProjectiveDesertWidth_tendsto_atTop
    (p : InfinitePathLabel → ℝ) :
    Tendsto (thermodynamicProjectiveDesertWidth p) atTop atTop := by
  have hpositive : Tendsto thermodynamicProjectiveDesertDensity atTop (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨thermodynamicProjectiveDesertDensity_tendsto_zero,
      Filter.Eventually.of_forall thermodynamicProjectiveDesertDensity_pos⟩
  have hinv : Tendsto (fun k => (thermodynamicProjectiveDesertDensity k)⁻¹)
      atTop atTop := tendsto_inv_nhdsGT_zero.comp hpositive
  have hscale : Tendsto
      (fun k => (thermodynamicProjectiveDesertMesh p / 2) *
        (thermodynamicProjectiveDesertDensity k)⁻¹) atTop atTop :=
    hinv.const_mul_atTop (half_pos (thermodynamicProjectiveDesertMesh_pos p))
  have hshift := Filter.tendsto_atTop_add_const_right atTop
    (-thermodynamicProjectiveDesertMesh p) hscale
  convert hshift using 1
  funext k
  rw [thermodynamicProjectiveDesertWidth, div_eq_mul_inv]
  ring

/-- Quantitative same-field prefix desert law.  Certified return-free interval lengths grow
without bound and are the explicit inverse of the exact completed return occupation, up to the
uniform speed mesh. -/
theorem infinitePathPrefix_quantitativeProjectiveRecurrenceDeserts
    {p : InfinitePathLabel → ℝ}
    (hpmax : ∀ k, MaximallyProjectiveEnergy
      (pathEigenValues k (infinitePathPrefixShell k p)))
    (hsum : Summable (fun i => |p i|)) :
    Tendsto (thermodynamicProjectiveDesertWidth p) atTop atTop ∧
      ∀ᶠ k : ℕ in atTop,
        0 ≤ thermodynamicProjectiveDesertWidth p k ∧
        ∀ A0 : ℝ, 0 ≤ A0 → ∃ u : ℝ, A0 ≤ u ∧
          Icc u (u + thermodynamicProjectiveDesertWidth p k) ∩
            scalarUnitaryReturnTimes
              (pathHamiltonian (infinitePathPrefixShell k p))
                thermodynamicProjectiveDesertRadius = ∅ := by
  have hwidth := thermodynamicProjectiveDesertWidth_tendsto_atTop p
  refine ⟨hwidth, ?_⟩
  have hwidth0 : ∀ᶠ k : ℕ in atTop,
      0 ≤ thermodynamicProjectiveDesertWidth p k :=
    hwidth.eventually_ge_atTop 0
  have hnorm := eventually_norm_pathHamiltonian_infinitePathPrefixShell_le hsum
  filter_upwards [hwidth0, hnorm] with k hW hnormk
  refine ⟨hW, ?_⟩
  let H : Matrix (Fin (k + 3) → Bool) (Fin (k + 3) → Bool) ℂ :=
    pathHamiltonian (infinitePathPrefixShell k p)
  let hH : H.IsHermitian := isSelfAdjoint_pathHamiltonian _
  let speed : ℝ := ‖infinitePathUHFHamiltonian p‖ + 2
  have hspeed0 : 0 < speed := by dsimp [speed]; positivity
  have hHspeed : ‖H‖ ≤ speed := by
    dsimp [H, speed]
    linarith
  have hmax : MaximallyProjectiveEnergy hH.eigenvalues :=
    maximallyProjectiveEnergy_eigenvalues_of_orthoEigenBasis hH
      (isOrthoEigenBasis_pathEigenBasis k (infinitePathPrefixShell k p)) (hpmax k)
  have hbpos := thermodynamicProjectiveDesertDensity_pos k
  have hmeshpos := thermodynamicProjectiveDesertMesh_pos p
  have hpack : projectiveReturnDensityBase (2 * thermodynamicProjectiveWideRadius) ^
        Fintype.card {i : (Fin (k + 3) → Bool) //
          i ≠ infinitePathPrefixReference k} <
      ((thermodynamicProjectiveWideRadius - thermodynamicProjectiveDesertRadius) / speed) /
        (thermodynamicProjectiveDesertWidth p k +
          (thermodynamicProjectiveWideRadius - thermodynamicProjectiveDesertRadius) / speed) := by
    rw [← thermodynamicProjectiveDesertDensity_eq_card]
    have hmesh :
        (thermodynamicProjectiveWideRadius - thermodynamicProjectiveDesertRadius) / speed =
          thermodynamicProjectiveDesertMesh p := by rfl
    rw [hmesh, thermodynamicProjectiveDesertWidth]
    have hden : 2 * thermodynamicProjectiveDesertDensity k ≠ 0 := by positivity
    have hratio : thermodynamicProjectiveDesertMesh p /
          (thermodynamicProjectiveDesertMesh p /
            (2 * thermodynamicProjectiveDesertDensity k)) =
        2 * thermodynamicProjectiveDesertDensity k := by
      field_simp
    rw [sub_add_cancel, hratio]
    linarith
  simpa only [H] using
    maximallyProjective_scalarUnitaryReturnTimes_late_deserts hH hmax
      (infinitePathPrefixReference k) hspeed0 hHspeed
      (by norm_num [thermodynamicProjectiveDesertRadius])
      (by norm_num [thermodynamicProjectiveDesertRadius,
        thermodynamicProjectiveWideRadius]) hW
      (by norm_num [thermodynamicProjectiveWideRadius]) hpack

/-- Complete same-field lifecycle upgraded by a quantitative thermodynamic projective-return
desert scale. -/
structure ThermodynamicRecurrenceDesertLifecycle
    (p : InfinitePathLabel → ℝ) : Prop
    extends ThermodynamicSameFieldLifecycle p where
  projectiveDesertWidth_tendsto :
    Tendsto (thermodynamicProjectiveDesertWidth p) atTop atTop
  eventually_quantitativeProjectiveDeserts :
    ∀ᶠ k : ℕ in atTop,
      0 ≤ thermodynamicProjectiveDesertWidth p k ∧
      ∀ A0 : ℝ, 0 ≤ A0 → ∃ u : ℝ, A0 ≤ u ∧
        Icc u (u + thermodynamicProjectiveDesertWidth p k) ∩
          scalarUnitaryReturnTimes
            (pathHamiltonian (infinitePathPrefixShell k p))
              thermodynamicProjectiveDesertRadius = ∅

/-- Diverging certified deserts rule out every volume-independent projective-recurrence clock.
For each prescribed duration, all sufficiently large prefixes contain an arbitrarily late
interval of that duration with no operator-norm return up to global phase. -/
theorem ThermodynamicRecurrenceDesertLifecycle.eventually_arbitraryWidthProjectiveDeserts
    {p : InfinitePathLabel → ℝ} (hp : ThermodynamicRecurrenceDesertLifecycle p)
    (W : ℝ) (hW : 0 ≤ W) :
    ∀ᶠ k : ℕ in atTop,
      ∀ A0 : ℝ, 0 ≤ A0 → ∃ u : ℝ, A0 ≤ u ∧
        Icc u (u + W) ∩ scalarUnitaryReturnTimes
          (pathHamiltonian (infinitePathPrefixShell k p))
            thermodynamicProjectiveDesertRadius = ∅ := by
  have hwidth : ∀ᶠ k : ℕ in atTop,
      W ≤ thermodynamicProjectiveDesertWidth p k :=
    hp.projectiveDesertWidth_tendsto.eventually_ge_atTop W
  filter_upwards [hwidth, hp.eventually_quantitativeProjectiveDeserts] with k hk hdesert
  intro A0 hA0
  obtain ⟨u, hu, hlarge⟩ := hdesert.2 A0 hA0
  refine ⟨u, hu, Set.eq_empty_iff_forall_not_mem.2 fun t ht => ?_⟩
  have htlarge : t ∈ Icc u (u + thermodynamicProjectiveDesertWidth p k) :=
    ⟨ht.1.1, by linarith [ht.1.2]⟩
  have : t ∈ Icc u (u + thermodynamicProjectiveDesertWidth p k) ∩
      scalarUnitaryReturnTimes
        (pathHamiltonian (infinitePathPrefixShell k p))
          thermodynamicProjectiveDesertRadius := ⟨htlarge, ht.2⟩
  rw [hlarge] at this
  exact this

/-- **Unconditional quantitative thermodynamic recurrence-desert capstone.**  One countable
static nearest-neighbour Pauli field simultaneously has the full recurrence--complexity--UHF
lifecycle and projective-return-free intervals whose certified length diverges as the inverse of
its exact completed return occupation. -/
theorem exists_thermodynamicRecurrenceDesertLifecycle :
    ∃ p : InfinitePathLabel → ℝ, ThermodynamicRecurrenceDesertLifecycle p := by
  obtain ⟨p, hp⟩ := exists_thermodynamicSameFieldLifecycle
  have hdesert := infinitePathPrefix_quantitativeProjectiveRecurrenceDeserts
    hp.prefix_maximallyProjective hp.coefficient_summable
  exact ⟨p, {
    toThermodynamicSameFieldLifecycle := hp
    projectiveDesertWidth_tendsto := hdesert.1
    eventually_quantitativeProjectiveDeserts := hdesert.2 }⟩

/-- **Thermodynamic projective-recurrence desert law.**  One compatible static nearest-neighbour
qubit field has a fixed positive operator-norm resolution at which every prescribed duration is,
for every sufficiently large finite prefix, realized by arbitrarily late intervals containing no
return up to any global phase.  Each finite prefix nevertheless has syndetic projective recurrence
at every positive resolution. -/
theorem exists_thermodynamicProjectiveRecurrenceDesertLaw :
    ∃ p : InfinitePathLabel → ℝ,
      Summable (fun i => |p i|) ∧
      (∀ (k : ℕ) (eps : ℝ), 0 < eps →
        ∃ B : ℝ, 0 ≤ B ∧ ∀ a : ℝ,
          ∃ t ∈ Icc a (a + B), ∃ c : ℂ, ‖c‖ = 1 ∧
            ‖unitaryEvolution (pathHamiltonian (infinitePathPrefixShell k p)) t -
              c • (1 : Matrix (Fin (k + 3) → Bool)
                (Fin (k + 3) → Bool) ℂ)‖ < eps) ∧
      ∀ W : ℝ, 0 ≤ W → ∀ᶠ k : ℕ in atTop,
        ∀ A0 : ℝ, 0 ≤ A0 → ∃ u : ℝ, A0 ≤ u ∧
          Icc u (u + W) ∩ scalarUnitaryReturnTimes
            (pathHamiltonian (infinitePathPrefixShell k p))
              thermodynamicProjectiveDesertRadius = ∅ := by
  obtain ⟨p, _hpclose, hpgood, hsum⟩ :=
    exists_nestedCentered_allPrefixes_projective_summable
  refine ⟨p, hsum, fun k eps heps =>
    infinitePathPrefix_projectiveReturn_syndetic hpgood k heps, ?_⟩
  intro W hW
  let speed : ℝ := ‖infinitePathUHFHamiltonian p‖ + 2
  let delta : ℝ :=
    (thermodynamicProjectiveWideRadius - thermodynamicProjectiveDesertRadius) / speed
  let b : ℕ → ℝ := fun k =>
    projectiveReturnDensityBase (2 * thermodynamicProjectiveWideRadius) ^
      Fintype.card {i : (Fin (k + 3) → Bool) // i ≠ infinitePathPrefixReference k}
  have hspeed0 : 0 < speed := by
    dsimp [speed]
    positivity
  have hdelta0 : 0 < delta := by
    dsimp [delta, thermodynamicProjectiveWideRadius,
      thermodynamicProjectiveDesertRadius]
    positivity
  have hthreshold : 0 < delta / (W + delta) := by positivity
  have hbzero : Tendsto b atTop (nhds 0) := by
    have hmain := (quditPathProjectiveReturnDensity_tendsto_zero
      (q := 2) (by norm_num) (ε := 2 * thermodynamicProjectiveWideRadius)
      (by norm_num [thermodynamicProjectiveWideRadius])
      (by norm_num [thermodynamicProjectiveWideRadius])).comp
        (tendsto_add_atTop_nat 3)
    simpa [b, quditPathProjectiveReturnDensity, Function.comp_def] using hmain
  have hbsmall : ∀ᶠ k : ℕ in atTop, b k < delta / (W + delta) :=
    hbzero.eventually_lt_const hthreshold
  have hnorm := eventually_norm_pathHamiltonian_infinitePathPrefixShell_le hsum
  filter_upwards [hbsmall, hnorm] with k hbk hnormk
  let H : Matrix (Fin (k + 3) → Bool) (Fin (k + 3) → Bool) ℂ :=
    pathHamiltonian (infinitePathPrefixShell k p)
  let hH : H.IsHermitian := isSelfAdjoint_pathHamiltonian _
  have hmax : MaximallyProjectiveEnergy hH.eigenvalues :=
    infinitePathPrefixHamiltonian_eigenvalues_maximallyProjective hpgood k
  have hHspeed : ‖H‖ ≤ speed := by
    dsimp [H, speed]
    linarith
  have hpack : projectiveReturnDensityBase (2 * thermodynamicProjectiveWideRadius) ^
        Fintype.card {i : (Fin (k + 3) → Bool) //
          i ≠ infinitePathPrefixReference k} <
      ((thermodynamicProjectiveWideRadius - thermodynamicProjectiveDesertRadius) / speed) /
        (W + (thermodynamicProjectiveWideRadius -
          thermodynamicProjectiveDesertRadius) / speed) := by
    simpa only [b, delta] using hbk
  simpa only [H] using
    maximallyProjective_scalarUnitaryReturnTimes_late_deserts hH hmax
      (infinitePathPrefixReference k) hspeed0 hHspeed
      (by norm_num [thermodynamicProjectiveDesertRadius])
      (by norm_num [thermodynamicProjectiveDesertRadius,
        thermodynamicProjectiveWideRadius]) hW
      (by norm_num [thermodynamicProjectiveWideRadius]) hpack

end

end GaloisForLFunctions.HTGeometry
