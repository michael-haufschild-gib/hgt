import GaloisForLFunctions.HTGeometry.UniformProjectiveContinuousCircuitFirstReturnLaw
import GaloisForLFunctions.HTGeometry.AnchoredProjectiveReturnDensityLaw
import GaloisForLFunctions.HTGeometry.FiniteSpectralRecurrenceFrequencyLaw

/-!
# Completed-time occupation of continuous two-qubit circuit images

A maximally projective spectral flow spends only an explicitly bounded completed-time fraction
within fixed operator distance of the complete global-phase-saturated image of arbitrary continuous
`SU(4)` two-qubit circuits.  The proof covers the uncountable circuit family by a finite operator
net, controls every one-centre projective tube by an exact anchored Haar chord volume, and combines
the resulting bound with near-Hilbert circuit entropy.  At gate budget
`2^n / (64 * (n + 1))`, the occupation envelope tends to zero with qubit number.
-/

open Matrix Set Topology MeasureTheory Filter Complex UnitAddTorus
open scoped Matrix.Norms.L2Operator


namespace GaloisForLFunctions.HTGeometry

noncomputable section

theorem fourier_one_sub_eq_div (x y : UnitAddCircle) :
    (fourier 1 (x - y) : ℂ) = fourier 1 x / fourier 1 y := by
  rw [sub_eq_add_neg, fourier_one_add]
  have hy : (fourier 1 y : ℂ) ≠ 0 :=
    norm_ne_zero_iff.mp (by rw [norm_fourier_one y]; norm_num)
  apply (eq_div_iff hy).2
  rw [mul_assoc, ← fourier_one_add, neg_add_cancel]
  simp

theorem norm_fourier_one_sub_sub_one
    (x y : UnitAddCircle) :
    ‖fourier 1 (x - y) - 1‖ = ‖fourier 1 x - fourier 1 y‖ := by
  have hy : ‖(fourier 1 y : ℂ)‖ = 1 := norm_fourier_one y
  have hy0 : (fourier 1 y : ℂ) ≠ 0 := norm_ne_zero_iff.mp (by rw [hy]; norm_num)
  calc
    ‖fourier 1 (x - y) - 1‖ =
        ‖(fourier 1 (x - y) - 1) * fourier 1 y‖ := by
          rw [norm_mul, hy, mul_one]
    _ = ‖fourier 1 x - fourier 1 y‖ := by
      rw [fourier_one_sub_eq_div]
      congr 1
      field_simp

def phaseSaturatedMatrixOrbit {n : ℕ}
    (W : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) :
    Set (Matrix (Fin n → Bool) (Fin n → Bool) ℂ) :=
  (fun c : ℂ => c • W) '' Metric.sphere 0 1

theorem isCompact_phaseSaturatedMatrixOrbit {n : ℕ}
    (W : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) :
    IsCompact (phaseSaturatedMatrixOrbit W) := by
  exact (isCompact_sphere (0 : ℂ) 1).image
    (continuous_id.smul continuous_const)

theorem phaseSaturatedMatrixOrbit_nonempty {n : ℕ}
    (W : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) :
    (phaseSaturatedMatrixOrbit W).Nonempty := by
  refine ⟨W, 1, ?_, by simp⟩
  simp

theorem mem_phaseSaturatedMatrixOrbit_iff {n : ℕ}
    {W M : Matrix (Fin n → Bool) (Fin n → Bool) ℂ} :
    M ∈ phaseSaturatedMatrixOrbit W ↔
      ∃ c : ℂ, ‖c‖ = 1 ∧ M = c • W := by
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨c, by simpa [Metric.mem_sphere] using hc, rfl⟩
  · rintro ⟨c, hc, rfl⟩
    exact ⟨c, by simpa [Metric.mem_sphere] using hc, rfl⟩

def projectiveSpectralPointTube {n d : ℕ}
    (e : (Fin n → Bool) ≃ Fin (d + 1))
    (V : Matrix.unitaryGroup (Fin n → Bool) ℂ)
    (W : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) (r : ℝ) :
    Set (Fin d → UnitAddCircle) :=
  {x | Metric.infDist (projectiveSpectralMatrix e V x)
      (phaseSaturatedMatrixOrbit W) ≤ r}

theorem isClosed_projectiveSpectralPointTube {n d : ℕ}
    (e : (Fin n → Bool) ≃ Fin (d + 1))
    (V : Matrix.unitaryGroup (Fin n → Bool) ℂ)
    (W : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) (r : ℝ) :
    IsClosed (projectiveSpectralPointTube e V W r) := by
  exact isClosed_le
    ((Metric.continuous_infDist_pt (phaseSaturatedMatrixOrbit W)).comp
      (continuous_projectiveSpectralMatrix e V)) continuous_const

theorem mem_projectiveSpectralPointTube_iff {n d : ℕ}
    (e : (Fin n → Bool) ≃ Fin (d + 1))
    (V : Matrix.unitaryGroup (Fin n → Bool) ℂ)
    (W : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) (r : ℝ)
    (x : Fin d → UnitAddCircle) :
    x ∈ projectiveSpectralPointTube e V W r ↔
      ∃ c : ℂ, ‖c‖ = 1 ∧
        ‖projectiveSpectralMatrix e V x - c • W‖ ≤ r := by
  constructor
  · intro hx
    obtain ⟨M, hM, hMdist⟩ := exists_compactTarget_minDist
      (isCompact_phaseSaturatedMatrixOrbit W)
      (phaseSaturatedMatrixOrbit_nonempty W)
      (projectiveSpectralMatrix e V x)
    obtain ⟨c, hc, rfl⟩ := mem_phaseSaturatedMatrixOrbit_iff.mp hM
    refine ⟨c, hc, ?_⟩
    rw [← dist_eq_norm, hMdist]
    exact hx
  · rintro ⟨c, hc, hdist⟩
    have hmem : c • W ∈ phaseSaturatedMatrixOrbit W :=
      mem_phaseSaturatedMatrixOrbit_iff.mpr ⟨c, hc, rfl⟩
    exact (Metric.infDist_le_dist_of_mem hmem).trans (by
      simpa [dist_eq_norm] using hdist)

theorem projectiveSpectralPointTube_pair_chord {n d : ℕ}
    (e : (Fin n → Bool) ≃ Fin (d + 1))
    (V : Matrix.unitaryGroup (Fin n → Bool) ℂ)
    (W : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) (r : ℝ)
    {x y : Fin d → UnitAddCircle}
    (hx : x ∈ projectiveSpectralPointTube e V W r)
    (hy : y ∈ projectiveSpectralPointTube e V W r) :
    ∀ i, ‖fourier 1 (x i) - fourier 1 (y i)‖ ≤ 4 * r := by
  obtain ⟨cx, hcx, hxdist⟩ :=
    (mem_projectiveSpectralPointTube_iff e V W r x).mp hx
  obtain ⟨cy, hcy, hydist⟩ :=
    (mem_projectiveSpectralPointTube_iff e V W r y).mp hy
  have hcy0 : cy ≠ 0 := norm_ne_zero_iff.mp (by rw [hcy]; norm_num)
  let z : ℂ := cx / cy
  have hz : ‖z‖ = 1 := by simp [z, hcx, hcy]
  have hscalar : z * cy = cx := by
    dsimp [z]
    exact div_mul_cancel₀ cx hcy0
  have hupper :
      ‖projectiveSpectralMatrix e V x -
          z • projectiveSpectralMatrix e V y‖ ≤ 2 * r := by
    calc
      ‖projectiveSpectralMatrix e V x -
          z • projectiveSpectralMatrix e V y‖ ≤
          ‖projectiveSpectralMatrix e V x - cx • W‖ +
            ‖cx • W - z • projectiveSpectralMatrix e V y‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ = ‖projectiveSpectralMatrix e V x - cx • W‖ +
            ‖z • (cy • W - projectiveSpectralMatrix e V y)‖ := by
        congr 1
        rw [smul_sub, smul_smul, hscalar]
      _ = ‖projectiveSpectralMatrix e V x - cx • W‖ +
            ‖cy • W - projectiveSpectralMatrix e V y‖ := by
        rw [norm_smul, hz, one_mul]
      _ = ‖projectiveSpectralMatrix e V x - cx • W‖ +
            ‖projectiveSpectralMatrix e V y - cy • W‖ := by
        rw [norm_sub_rev (cy • W) (projectiveSpectralMatrix e V y)]
      _ ≤ r + r := add_le_add hxdist hydist
      _ = 2 * r := by ring
  let f : (Fin n → Bool) → ℂ := fun q =>
    fourier 1 (RHTower.zeroAnchoredPhase d x (e q)) -
      z * fourier 1 (RHTower.zeroAnchoredPhase d y (e q))
  have hmatrix :
      projectiveSpectralMatrix e V x -
          z • projectiveSpectralMatrix e V y =
        (V : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) *
          Matrix.diagonal f *
            (V⁻¹ : Matrix.unitaryGroup (Fin n → Bool) ℂ).1 := by
    have hdiag :
        Matrix.diagonal (fun q =>
            fourier 1 (RHTower.zeroAnchoredPhase d x (e q))) -
          z • Matrix.diagonal (fun q =>
            fourier 1 (RHTower.zeroAnchoredPhase d y (e q))) =
          Matrix.diagonal f := by
      ext i j
      by_cases hij : i = j
      · subst j
        simp [f]
      · simp [Matrix.diagonal_apply_ne _ hij]
    simp only [projectiveSpectralMatrix]
    calc
      ((V : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) *
            Matrix.diagonal (fun q =>
              fourier 1 (RHTower.zeroAnchoredPhase d x (e q)))) *
              (V⁻¹ : Matrix.unitaryGroup (Fin n → Bool) ℂ).1 -
          z • (((V : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) *
            Matrix.diagonal (fun q =>
              fourier 1 (RHTower.zeroAnchoredPhase d y (e q)))) *
              (V⁻¹ : Matrix.unitaryGroup (Fin n → Bool) ℂ).1) =
        (V : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) *
          (Matrix.diagonal (fun q =>
              fourier 1 (RHTower.zeroAnchoredPhase d x (e q))) -
            z • Matrix.diagonal (fun q =>
              fourier 1 (RHTower.zeroAnchoredPhase d y (e q)))) *
            (V⁻¹ : Matrix.unitaryGroup (Fin n → Bool) ℂ).1 := by
        rw [← Matrix.smul_mul, ← Matrix.mul_smul,
          ← Matrix.sub_mul, ← Matrix.mul_sub]
      _ = _ := by rw [hdiag]
  have hVinv : (V⁻¹ : Matrix.unitaryGroup (Fin n → Bool) ℂ).1 =
      star (V : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) := by simp
  rw [hmatrix, hVinv, l2_opNorm_unitary_conj_eq V.2,
    Matrix.l2_opNorm_diagonal] at hupper
  have hanchor : ‖(1 : ℂ) - z‖ ≤ 2 * r := by
    have h := (norm_le_pi_norm f (e.symm 0)).trans hupper
    simpa [f, RHTower.zeroAnchoredPhase] using h
  intro i
  have htail :
      ‖fourier 1 (x i) - z * fourier 1 (y i)‖ ≤ 2 * r := by
    have h := (norm_le_pi_norm f (e.symm i.succ)).trans hupper
    simpa [f, RHTower.zeroAnchoredPhase] using h
  calc
    ‖fourier 1 (x i) - fourier 1 (y i)‖ ≤
        ‖fourier 1 (x i) - z * fourier 1 (y i)‖ +
          ‖z * fourier 1 (y i) - fourier 1 (y i)‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ = ‖fourier 1 (x i) - z * fourier 1 (y i)‖ + ‖z - 1‖ := by
      congr 1
      rw [show z * fourier 1 (y i) - fourier 1 (y i) =
          (z - 1) * fourier 1 (y i) by ring,
        norm_mul, norm_fourier_one, mul_one]
    _ ≤ 2 * r + 2 * r := add_le_add htail (by simpa [norm_sub_rev] using hanchor)
    _ = 4 * r := by ring

theorem projectiveSpectralPointTube_sub_mem_anchored {n d : ℕ}
    (e : (Fin n → Bool) ≃ Fin (d + 1))
    (V : Matrix.unitaryGroup (Fin n → Bool) ℂ)
    (W : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) (r : ℝ)
    {x y : Fin d → UnitAddCircle}
    (hx : x ∈ projectiveSpectralPointTube e V W r)
    (hy : y ∈ projectiveSpectralPointTube e V W r) :
    x - y ∈ anchoredProjectiveReturnTarget (4 * r) := by
  intro i
  change ‖fourier 1 (x i - y i) - 1‖ ≤ 4 * r
  rw [norm_fourier_one_sub_sub_one]
  exact projectiveSpectralPointTube_pair_chord e V W r hx hy i

theorem volume_projectiveSpectralPointTube_le {n d : ℕ}
    (e : (Fin n → Bool) ≃ Fin (d + 1))
    (V : Matrix.unitaryGroup (Fin n → Bool) ℂ)
    (W : Matrix (Fin n → Bool) (Fin n → Bool) ℂ)
    {r : ℝ} (hr0 : 0 ≤ r) (hr2 : 4 * r < 2) :
    (volume : Measure (Fin d → UnitAddCircle))
        (projectiveSpectralPointTube e V W r) ≤
      ENNReal.ofReal (2 * Real.arcsin ((4 * r) / 2) / Real.pi) ^ d := by
  by_cases hne : (projectiveSpectralPointTube e V W r).Nonempty
  · obtain ⟨y, hy⟩ := hne
    have hsub : projectiveSpectralPointTube e V W r ⊆
        (fun x : Fin d → UnitAddCircle => x + (-y)) ⁻¹'
          anchoredProjectiveReturnTarget (4 * r) := by
      intro x hx
      change x + (-y) ∈ anchoredProjectiveReturnTarget (4 * r)
      simpa [sub_eq_add_neg] using
        projectiveSpectralPointTube_sub_mem_anchored e V W r hx hy
    calc
      (volume : Measure (Fin d → UnitAddCircle))
          (projectiveSpectralPointTube e V W r) ≤
          volume ((fun x : Fin d → UnitAddCircle => x + (-y)) ⁻¹'
            anchoredProjectiveReturnTarget (4 * r)) := measure_mono hsub
      _ = volume (anchoredProjectiveReturnTarget (4 * r)) := by
        rw [measure_preimage_add_right]
      _ = ENNReal.ofReal
          (2 * Real.arcsin ((4 * r) / 2) / Real.pi) ^ d := by
        rw [← finiteTorusHaarProbabilityMeasure_toMeasure_eq_volume]
        simpa using finiteTorusHaarProbabilityMeasure_anchoredProjectiveReturnTarget
          (d := Fin d) (mul_nonneg (by norm_num) hr0) hr2
  · have hempty : projectiveSpectralPointTube e V W r = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp hne
    rw [hempty, measure_empty]
    positivity

def projectiveContinuousCircuitCaptureTarget {n d : ℕ}
    (e : (Fin n → Bool) ≃ Fin (d + 1))
    (V : Matrix.unitaryGroup (Fin n → Bool) ℂ)
    (s : ℕ) (eps : ℝ) : Set (Fin d → UnitAddCircle) :=
  {x | Metric.infDist (projectiveSpectralMatrix e V x)
      (phaseCircuitMatrixImageAtMost n s) ≤ eps}

theorem isClosed_projectiveContinuousCircuitCaptureTarget {n d : ℕ}
    (e : (Fin n → Bool) ≃ Fin (d + 1))
    (V : Matrix.unitaryGroup (Fin n → Bool) ℂ)
    (s : ℕ) (eps : ℝ) :
    IsClosed (projectiveContinuousCircuitCaptureTarget e V s eps) := by
  exact isClosed_le
    ((Metric.continuous_infDist_pt (phaseCircuitMatrixImageAtMost n s)).comp
      (continuous_projectiveSpectralMatrix e V)) continuous_const

theorem mem_projectiveContinuousCircuitCaptureTarget_iff {n d : ℕ}
    (e : (Fin n → Bool) ≃ Fin (d + 1))
    (V : Matrix.unitaryGroup (Fin n → Bool) ℂ)
    (s : ℕ) (eps : ℝ) (x : Fin d → UnitAddCircle) :
    x ∈ projectiveContinuousCircuitCaptureTarget e V s eps ↔
      ∃ c : ℂ, ‖c‖ = 1 ∧ ∃ C : TwoQubitCircuit n,
        C.gateCount ≤ s ∧
        ‖projectiveSpectralMatrix e V x -
          c • (C.eval : Matrix (Fin n → Bool) (Fin n → Bool) ℂ)‖ ≤ eps := by
  constructor
  · intro hx
    obtain ⟨M, hM, hMdist⟩ := exists_compactTarget_minDist
      (isCompact_phaseCircuitMatrixImageAtMost n s)
      (phaseCircuitMatrixImageAtMost_nonempty n s)
      (projectiveSpectralMatrix e V x)
    obtain ⟨c, hc, C, hCs, rfl⟩ := mem_phaseCircuitMatrixImageAtMost_iff.mp hM
    refine ⟨c, hc, C, hCs, ?_⟩
    rw [← dist_eq_norm, hMdist]
    exact hx
  · rintro ⟨c, hc, C, hCs, hdist⟩
    have hmem : c • (C.eval : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) ∈
        phaseCircuitMatrixImageAtMost n s :=
      mem_phaseCircuitMatrixImageAtMost_iff.mpr ⟨c, hc, C, hCs, rfl⟩
    exact (Metric.infDist_le_dist_of_mem hmem).trans (by
      simpa [dist_eq_norm] using hdist)

theorem projectiveContinuousCircuitCaptureTarget_subset_quarterNetTubes
    {n d s : ℕ}
    (e : (Fin n → Bool) ≃ Fin (d + 1))
    (V : Matrix.unitaryGroup (Fin n → Bool) ℂ) :
    projectiveContinuousCircuitCaptureTarget e V s (1 / 20 : ℝ) ⊆
      ⋃ W ∈ atMostQuarterCircuitNet n s,
        projectiveSpectralPointTube e V
          (W : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) (3 / 10 : ℝ) := by
  intro x hx
  obtain ⟨c, hc, C, hCs, hdist⟩ :=
    (mem_projectiveContinuousCircuitCaptureTarget_iff
      e V s (1 / 20 : ℝ) x).mp hx
  obtain ⟨W, hW, hCW⟩ := atMostQuarterCircuitNet_cover C hCs
  rw [Set.mem_iUnion]
  refine ⟨W, ?_⟩
  rw [Set.mem_iUnion]
  refine ⟨hW, (mem_projectiveSpectralPointTube_iff e V
    (W : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) (3 / 10 : ℝ) x).mpr
      ⟨c, hc, ?_⟩⟩
  calc
    ‖projectiveSpectralMatrix e V x - c •
        (W : Matrix (Fin n → Bool) (Fin n → Bool) ℂ)‖ ≤
      ‖projectiveSpectralMatrix e V x - c •
          (C.eval : Matrix (Fin n → Bool) (Fin n → Bool) ℂ)‖ +
        ‖c • (C.eval : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) -
          c • (W : Matrix (Fin n → Bool) (Fin n → Bool) ℂ)‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ (1 / 20 : ℝ) + 1 / 4 := add_le_add hdist (by
      rw [← smul_sub, norm_smul, hc, one_mul]
      simpa [dist_eq_norm] using hCW)
    _ = 3 / 10 := by norm_num

def continuousCircuitOccupationBase : ℝ :=
  2 * Real.arcsin (3 / 5 : ℝ) / Real.pi

theorem continuousCircuitOccupationBase_nonneg :
    0 ≤ continuousCircuitOccupationBase := by
  have harg : (0 : ℝ) ≤ 3 / 5 := by norm_num
  have hasin : 0 ≤ Real.arcsin (3 / 5 : ℝ) := Real.arcsin_nonneg.mpr harg
  unfold continuousCircuitOccupationBase
  positivity

theorem two_mul_continuousCircuitOccupationBase_lt_one :
    2 * continuousCircuitOccupationBase < 1 := by
  have harg : (3 / 5 : ℝ) ∈ Set.Icc (-1) 1 := by norm_num
  have hangle : Real.pi / 4 ∈
      Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> nlinarith [Real.pi_pos]
  have hsqrt0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hsqrtSq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsin : (3 / 5 : ℝ) < Real.sin (Real.pi / 4) := by
    rw [Real.sin_pi_div_four]
    nlinarith
  have hasin : Real.arcsin (3 / 5 : ℝ) < Real.pi / 4 :=
    (Real.arcsin_lt_iff_lt_sin harg hangle).2 hsin
  have hfour : 4 * Real.arcsin (3 / 5 : ℝ) < Real.pi := by
    nlinarith
  unfold continuousCircuitOccupationBase
  rw [show 2 * (2 * Real.arcsin (3 / 5 : ℝ) / Real.pi) =
      (4 * Real.arcsin (3 / 5 : ℝ)) / Real.pi by ring]
  exact (div_lt_one Real.pi_pos).2 hfour

theorem tendsto_two_pow_sub_one_atTop :
    Tendsto (fun n : ℕ => 2 ^ n - 1) atTop atTop := by
  have hp : Tendsto (fun n : ℕ => 2 ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  rw [tendsto_atTop]
  intro b
  filter_upwards [hp.eventually_ge_atTop (b + 1)] with n hn
  omega

theorem volume_projectiveContinuousCircuitCaptureTarget_le
    {n d s : ℕ}
    (e : (Fin n → Bool) ≃ Fin (d + 1))
    (V : Matrix.unitaryGroup (Fin n → Bool) ℂ) :
    (volume : Measure (Fin d → UnitAddCircle))
        (projectiveContinuousCircuitCaptureTarget e V s (1 / 20 : ℝ)) ≤
      ENNReal.ofReal (atMostQuarterCircuitEntropyBound n s) *
        ENNReal.ofReal continuousCircuitOccupationBase ^ d := by
  classical
  let net := atMostQuarterCircuitNet n s
  let qE : ENNReal := ENNReal.ofReal continuousCircuitOccupationBase ^ d
  have hsubset :=
    projectiveContinuousCircuitCaptureTarget_subset_quarterNetTubes
      (s := s) e V
  have hmeasureUnion :
      (volume : Measure (Fin d → UnitAddCircle))
          (⋃ W ∈ net, projectiveSpectralPointTube e V
            (W : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) (3 / 10 : ℝ)) ≤
        ∑ W ∈ net, volume (projectiveSpectralPointTube e V
          (W : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) (3 / 10 : ℝ)) := by
    exact measure_biUnion_finset_le net fun W =>
      projectiveSpectralPointTube e V
        (W : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) (3 / 10 : ℝ)
  have htube (W : Matrix.unitaryGroup (Fin n → Bool) ℂ) :
      (volume : Measure (Fin d → UnitAddCircle))
          (projectiveSpectralPointTube e V
            (W : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) (3 / 10 : ℝ)) ≤ qE := by
    have h := volume_projectiveSpectralPointTube_le e V
      (W : Matrix (Fin n → Bool) (Fin n → Bool) ℂ)
      (r := (3 / 10 : ℝ)) (by norm_num) (by norm_num)
    rw [show (4 : ℝ) * (3 / 10) / 2 = 3 / 5 by norm_num] at h
    simpa [qE, continuousCircuitOccupationBase] using h
  have hcardReal : ((net.card : ℕ) : ℝ) ≤
      atMostQuarterCircuitEntropyBound n s := by
    simpa [net] using atMostQuarterCircuitNet_card_real_le n s
  have hcardENN : ((net.card : ℕ) : ENNReal) ≤
      ENNReal.ofReal (atMostQuarterCircuitEntropyBound n s) := by
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal hcardReal
  calc
    (volume : Measure (Fin d → UnitAddCircle))
        (projectiveContinuousCircuitCaptureTarget e V s (1 / 20 : ℝ)) ≤
        volume (⋃ W ∈ net, projectiveSpectralPointTube e V
          (W : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) (3 / 10 : ℝ)) :=
      measure_mono (by simpa [net] using hsubset)
    _ ≤ ∑ W ∈ net, volume (projectiveSpectralPointTube e V
        (W : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) (3 / 10 : ℝ)) :=
      hmeasureUnion
    _ ≤ ∑ _W ∈ net, qE := Finset.sum_le_sum fun W _ => htube W
    _ = ((net.card : ℕ) : ENNReal) * qE := by simp
    _ ≤ ENNReal.ofReal (atMostQuarterCircuitEntropyBound n s) * qE :=
      mul_le_mul_of_nonneg_right hcardENN (by exact bot_le)
    _ = ENNReal.ofReal (atMostQuarterCircuitEntropyBound n s) *
        ENNReal.ofReal continuousCircuitOccupationBase ^ d := by rfl

theorem maximallyProjective_continuousCircuitCapture_completedTime_le
    {n d s : ℕ}
    (energy : Fin (d + 1) → ℝ)
    (hmax : MaximallyProjectiveEnergy energy)
    (e : (Fin n → Bool) ≃ Fin (d + 1))
    (V : Matrix.unitaryGroup (Fin n → Bool) ℂ) :
    atTop.limsup (fun T =>
        (finiteTorusPhaseProbabilityMeasure
          (RHTower.zeroProjectiveFrequency energy) T :
            Measure (Fin d → UnitAddCircle))
          (projectiveContinuousCircuitCaptureTarget e V s (1 / 20 : ℝ))) ≤
      ENNReal.ofReal (atMostQuarterCircuitEntropyBound n s) *
        ENNReal.ofReal continuousCircuitOccupationBase ^ d := by
  exact (rationallyIndependent_closedTarget_limsup_le_volume
    (RHTower.zeroProjectiveFrequency energy)
    (RHTower.maximallyProjectiveEnergy_zeroProjectiveFrequency_independent energy hmax)
    (isClosed_projectiveContinuousCircuitCaptureTarget e V s (1 / 20 : ℝ))).trans
      (volume_projectiveContinuousCircuitCaptureTarget_le e V)

def nearHilbertContinuousCircuitOccupationCost (n : ℕ) : ℝ :=
  atMostQuarterCircuitEntropyBound n (nearHilbertContinuousCircuitBudget n) *
    continuousCircuitOccupationBase ^ (2 ^ n - 1)

theorem nearHilbertContinuousCircuitOccupationCost_nonneg (n : ℕ) :
    0 ≤ nearHilbertContinuousCircuitOccupationCost n := by
  unfold nearHilbertContinuousCircuitOccupationCost
  have hEntropy : 0 ≤ atMostQuarterCircuitEntropyBound n
      (nearHilbertContinuousCircuitBudget n) := by
    unfold atMostQuarterCircuitEntropyBound
    exact Finset.sum_nonneg fun R _hR => by positivity
  exact mul_nonneg hEntropy
    (pow_nonneg continuousCircuitOccupationBase_nonneg _)

theorem tendsto_nearHilbertContinuousCircuitOccupationCost_atTop :
    Tendsto nearHilbertContinuousCircuitOccupationCost atTop (nhds 0) := by
  have hbase0 : 0 ≤ 2 * continuousCircuitOccupationBase :=
    mul_nonneg (by norm_num) continuousCircuitOccupationBase_nonneg
  have hpow : Tendsto
      (fun m : ℕ => (2 * continuousCircuitOccupationBase) ^ m)
      atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hbase0
      two_mul_continuousCircuitOccupationBase_lt_one
  have hmajorLimit : Tendsto
      (fun n : ℕ =>
        (2 * continuousCircuitOccupationBase) ^ (2 ^ n - 1))
      atTop (nhds 0) :=
    hpow.comp tendsto_two_pow_sub_one_atTop
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall
      nearHilbertContinuousCircuitOccupationCost_nonneg
  · filter_upwards
      [eventually_nearHilbertContinuousCircuitEntropy_lt_projectiveBooleanCarrier]
      with n hn
    let d := 2 ^ n - 1
    have hqpow : 0 ≤ continuousCircuitOccupationBase ^ d :=
      pow_nonneg continuousCircuitOccupationBase_nonneg _
    calc
      nearHilbertContinuousCircuitOccupationCost n =
          atMostQuarterCircuitEntropyBound n
              (nearHilbertContinuousCircuitBudget n) *
            continuousCircuitOccupationBase ^ d := by
        rfl
      _ ≤ ((2 ^ d : ℕ) : ℝ) *
            continuousCircuitOccupationBase ^ d :=
        mul_le_mul_of_nonneg_right hn.le hqpow
      _ = (2 : ℝ) ^ d * continuousCircuitOccupationBase ^ d := by
        norm_cast
      _ = (2 * continuousCircuitOccupationBase) ^ d := by
        rw [mul_pow]
      _ = (2 * continuousCircuitOccupationBase) ^ (2 ^ n - 1) := by
        rfl
  · exact hmajorLimit

end

end GaloisForLFunctions.HTGeometry

