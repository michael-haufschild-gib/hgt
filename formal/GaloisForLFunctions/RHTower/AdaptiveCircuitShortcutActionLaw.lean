import GaloisForLFunctions.HTGeometry.PhaseTwistedReplicaShortcutActionLaw
import GaloisForLFunctions.RHTower.StaticChoiTraceDistanceLaw

/-!
# Adaptive circuit-shortcut action law

This capstone converts the phase-twisted replica law into an operational
pure-state trace-distance theorem.  For any finite spectrum, any normalized
initial spectral distribution, any finite dictionary of normalized targets,
and a target selector allowed to inspect time before choosing its target, the
total shortcut-time mass is bounded by target entropy times exact spectral
collision and finite-action-resolution terms.

Padded gate words instantiate the dictionary with exactly `|gate|^(s+1)`
targets.  Under full spectral support and maximal projective rank, exact
collision mass becomes the unavoidable replica permutation floor.
-/

open scoped BigOperators ComplexConjugate Interval ENNReal NNReal
open MeasureTheory ProbabilityTheory

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry

def finiteSpectralOrbitState
    {I : Type*} [Fintype I]
    (weight energy : I → ℝ) (t : ℝ) : EuclideanSpace ℂ I :=
  WithLp.toLp 2 fun i ↦
    ((Real.sqrt (weight i) : ℝ) : ℂ) *
      Complex.exp (((-energy i * t : ℝ) : ℂ) * Complex.I)

@[simp] theorem finiteSpectralOrbitState_apply
    {I : Type*} [Fintype I]
    (weight energy : I → ℝ) (t : ℝ) (i : I) :
    finiteSpectralOrbitState weight energy t i =
      ((Real.sqrt (weight i) : ℝ) : ℂ) *
        Complex.exp (((-energy i * t : ℝ) : ℂ) * Complex.I) := rfl

theorem finiteSpectralOrbitState_norm
    {I : Type*} [Fintype I]
    {weight energy : I → ℝ}
    (hweight : ∀ i, 0 ≤ weight i)
    (hweightSum : ∑ i, weight i = 1) (t : ℝ) :
    ‖finiteSpectralOrbitState weight energy t‖ = 1 := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)]
  rw [EuclideanSpace.norm_sq_eq]
  simp only [finiteSpectralOrbitState_apply, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
  simpa [Complex.mul_re, abs_of_nonneg (Real.sqrt_nonneg _),
    Real.sq_sqrt (hweight _)] using hweightSum

def finiteSpectralAnchorTwist
    {I : Type*} [Fintype I]
    (energy : I → ℝ) (anchor : ℝ) (i : I) : ℂ :=
  Complex.exp (((-energy i * anchor : ℝ) : ℂ) * Complex.I)

theorem norm_finiteSpectralAnchorTwist
    {I : Type*} [Fintype I]
    (energy : I → ℝ) (anchor : ℝ) (i : I) :
    ‖finiteSpectralAnchorTwist energy anchor i‖ = 1 := by
  unfold finiteSpectralAnchorTwist
  rw [Complex.norm_exp]
  norm_num [Complex.mul_re]

theorem inner_finiteSpectralOrbitState_eq_twistedAmplitude
    {I : Type*} [Fintype I]
    {weight energy : I → ℝ}
    (hweight : ∀ i, 0 ≤ weight i) (t anchor : ℝ) :
    inner ℂ (finiteSpectralOrbitState weight energy t)
        (finiteSpectralOrbitState weight energy anchor) =
      twistedFiniteSpectralAmplitude weight energy
        (finiteSpectralAnchorTwist energy anchor) t := by
  rw [EuclideanSpace.inner_toLp_toLp]
  unfold dotProduct twistedFiniteSpectralAmplitude
  apply Finset.sum_congr rfl
  intro i hi
  simp only [finiteSpectralOrbitState_apply, Pi.star_apply, star_mul,
    Complex.star_def, Complex.conj_ofReal]
  rw [show
      (starRingEnd ℂ)
          (Complex.exp (((-energy i * t : ℝ) : ℂ) * Complex.I)) =
        Complex.exp (((energy i * t : ℝ) : ℂ) * Complex.I) by
    rw [← Complex.exp_conj]
    congr 1
    push_cast
    simp]
  have hsqrt :
      ((Real.sqrt (weight i) : ℝ) : ℂ) *
          ((Real.sqrt (weight i) : ℝ) : ℂ) =
        (weight i : ℂ) := by
    norm_cast
    exact Real.mul_self_sqrt (hweight i)
  unfold finiteSpectralAnchorTwist
  rw [← hsqrt]
  ring

theorem pureStateTraceDistance_triangle
    {I : Type*} [Fintype I]
    (x y z : EuclideanSpace ℂ I)
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hz : ‖z‖ = 1) :
    pureStateTraceDistance x z ≤
      pureStateTraceDistance x y + pureStateTraceDistance y z := by
  rw [pureStateTraceDistance_eq_invSqrtTwo_mul_densityDist x z hx hz,
    pureStateTraceDistance_eq_invSqrtTwo_mul_densityDist x y hx hy,
    pureStateTraceDistance_eq_invSqrtTwo_mul_densityDist y z hy hz]
  rw [← mul_add]
  exact mul_le_mul_of_nonneg_left
    (dist_triangle (pureStateDensity x) (pureStateDensity y)
      (pureStateDensity z)) (inv_nonneg.mpr (Real.sqrt_nonneg _))

theorem norm_inner_ge_sqrt_one_sub_four_mul_sq_of_traceDistance_le
    {I : Type*} [Fintype I]
    (x z : EuclideanSpace ℂ I)
    (hx : ‖x‖ = 1) (hz : ‖z‖ = 1)
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    (hepsilonHalf : epsilon ≤ 1 / 2)
    (hdist : pureStateTraceDistance x z ≤ 2 * epsilon) :
    Real.sqrt (1 - 4 * epsilon ^ 2) ≤ ‖inner ℂ x z‖ := by
  have hinner : ‖inner ℂ x z‖ ≤ 1 := by
    calc
      ‖inner ℂ x z‖ ≤ ‖x‖ * ‖z‖ := norm_inner_le_norm _ _
      _ = 1 := by rw [hx, hz, one_mul]
  have hdeficit : 0 ≤ 1 - ‖inner ℂ x z‖ ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hinner)
      (by positivity : 0 ≤ 1 + ‖inner ℂ x z‖)]
  have hrootSq :
      (pureStateTraceDistance x z) ^ 2 =
        1 - ‖inner ℂ x z‖ ^ 2 := by
    unfold pureStateTraceDistance
    rw [Real.sq_sqrt hdeficit]
  have hdistNonneg := pureStateTraceDistance_nonneg x z
  have hdistSq :
      (pureStateTraceDistance x z) ^ 2 ≤ (2 * epsilon) ^ 2 := by
    nlinarith
  have hrad : 0 ≤ 1 - 4 * epsilon ^ 2 := by
    nlinarith [sq_nonneg (epsilon - 1 / 2)]
  have hsq : 1 - 4 * epsilon ^ 2 ≤ ‖inner ℂ x z‖ ^ 2 := by
    rw [hrootSq] at hdistSq
    nlinarith
  have hsqrtSq := Real.sq_sqrt hrad
  nlinarith [Real.sqrt_nonneg (1 - 4 * epsilon ^ 2), norm_nonneg (inner ℂ x z)]

def finiteSpectralTargetCaptureSet
    {I : Type*} [Fintype I]
    (weight energy : I → ℝ) (target : EuclideanSpace ℂ I)
    (epsilon : ℝ) : Set ℝ :=
  {t | pureStateTraceDistance
    (finiteSpectralOrbitState weight energy t) target ≤ epsilon}

noncomputable def finiteSpectralTargetAnchor
    {I : Type*} [Fintype I]
    (weight energy : I → ℝ) (target : EuclideanSpace ℂ I)
    (epsilon : ℝ) : ℝ := by
  classical
  exact
    if h : (finiteSpectralTargetCaptureSet
        weight energy target epsilon).Nonempty then
      Classical.choose h
    else 0

def finiteSpectralTargetTwist
    {I : Type*} [Fintype I]
    (weight energy : I → ℝ) (target : EuclideanSpace ℂ I)
    (epsilon : ℝ) (i : I) : ℂ :=
  finiteSpectralAnchorTwist energy
    (finiteSpectralTargetAnchor weight energy target epsilon) i

theorem norm_finiteSpectralTargetTwist
    {I : Type*} [Fintype I]
    (weight energy : I → ℝ) (target : EuclideanSpace ℂ I)
    (epsilon : ℝ) (i : I) :
    ‖finiteSpectralTargetTwist weight energy target epsilon i‖ = 1 :=
  norm_finiteSpectralAnchorTwist energy _ i

theorem pureStateTraceDistance_comm
    {I : Type*} [Fintype I] (x z : EuclideanSpace ℂ I) :
    pureStateTraceDistance x z = pureStateTraceDistance z x := by
  unfold pureStateTraceDistance
  rw [norm_inner_symm]

theorem targetCapture_implies_anchorCoherence
    {I : Type*} [Fintype I]
    {weight energy : I → ℝ}
    (hweight : ∀ i, 0 ≤ weight i)
    (hweightSum : ∑ i, weight i = 1)
    {target : EuclideanSpace ℂ I} (htarget : ‖target‖ = 1)
    {epsilon t : ℝ} (hepsilon : 0 ≤ epsilon)
    (hepsilonHalf : epsilon ≤ 1 / 2)
    (ht : t ∈ finiteSpectralTargetCaptureSet
      weight energy target epsilon) :
    Real.sqrt (1 - 4 * epsilon ^ 2) ≤
      ‖twistedFiniteSpectralAmplitude weight energy
        (finiteSpectralTargetTwist weight energy target epsilon) t‖ := by
  have hactive :
      (finiteSpectralTargetCaptureSet
        weight energy target epsilon).Nonempty := ⟨t, ht⟩
  have hanchor :
      finiteSpectralTargetAnchor weight energy target epsilon ∈
        finiteSpectralTargetCaptureSet
          weight energy target epsilon := by
    unfold finiteSpectralTargetAnchor
    rw [dif_pos hactive]
    exact Classical.choose_spec hactive
  have ht' : pureStateTraceDistance
      (finiteSpectralOrbitState weight energy t) target ≤ epsilon := ht
  have hanchor' : pureStateTraceDistance
      (finiteSpectralOrbitState weight energy
        (finiteSpectralTargetAnchor weight energy target epsilon)) target ≤
        epsilon := hanchor
  have htargetAnchor : pureStateTraceDistance target
      (finiteSpectralOrbitState weight energy
        (finiteSpectralTargetAnchor weight energy target epsilon)) ≤ epsilon := by
    rw [pureStateTraceDistance_comm]
    exact hanchor'
  have hbetween : pureStateTraceDistance
      (finiteSpectralOrbitState weight energy t)
      (finiteSpectralOrbitState weight energy
        (finiteSpectralTargetAnchor weight energy target epsilon)) ≤
      2 * epsilon := by
    calc
      _ ≤ pureStateTraceDistance
            (finiteSpectralOrbitState weight energy t) target +
          pureStateTraceDistance target
            (finiteSpectralOrbitState weight energy
              (finiteSpectralTargetAnchor weight energy target epsilon)) :=
        pureStateTraceDistance_triangle _ _ _
          (finiteSpectralOrbitState_norm hweight hweightSum t) htarget
          (finiteSpectralOrbitState_norm hweight hweightSum _)
      _ ≤ epsilon + epsilon := add_le_add ht' htargetAnchor
      _ = 2 * epsilon := by ring
  have hcoherence :=
    norm_inner_ge_sqrt_one_sub_four_mul_sq_of_traceDistance_le
      (finiteSpectralOrbitState weight energy t)
      (finiteSpectralOrbitState weight energy
        (finiteSpectralTargetAnchor weight energy target epsilon))
      (finiteSpectralOrbitState_norm hweight hweightSum t)
      (finiteSpectralOrbitState_norm hweight hweightSum _)
      hepsilon hepsilonHalf hbetween
  rw [inner_finiteSpectralOrbitState_eq_twistedAmplitude
    hweight t (finiteSpectralTargetAnchor weight energy target epsilon)] at hcoherence
  change Real.sqrt (1 - 4 * epsilon ^ 2) ≤
    ‖twistedFiniteSpectralAmplitude weight energy
      (finiteSpectralAnchorTwist energy
        (finiteSpectralTargetAnchor weight energy target epsilon)) t‖
  exact hcoherence

def gaussianSpectralTargetCaptureSet
    {I : Type*} [Fintype I]
    (weight energy : I → ℝ) (target : EuclideanSpace ℂ I)
    (T epsilon : ℝ) : Set ℝ :=
  {x | T * x ∈ finiteSpectralTargetCaptureSet
    weight energy target epsilon}

def uniformSpectralTargetCaptureSet
    {I : Type*} [Fintype I]
    (weight energy : I → ℝ) (target : EuclideanSpace ℂ I)
    (T epsilon : ℝ) : Set ℝ :=
  finiteSpectralTargetCaptureSet weight energy target epsilon ∩
    Set.Ioc (-T) T

theorem gaussianTargetCapture_subset_twistedCoherence
    {I : Type*} [Fintype I]
    {weight energy : I → ℝ}
    (hweight : ∀ i, 0 ≤ weight i)
    (hweightSum : ∑ i, weight i = 1)
    {target : EuclideanSpace ℂ I} (htarget : ‖target‖ = 1)
    {epsilon T : ℝ} (hepsilon : 0 ≤ epsilon)
    (hepsilonHalf : epsilon ≤ 1 / 2) :
    gaussianSpectralTargetCaptureSet
        weight energy target T epsilon ⊆
      gaussianTwistedCoherenceCaptureSet weight energy
        (finiteSpectralTargetTwist weight energy target epsilon) T
        (Real.sqrt (1 - 4 * epsilon ^ 2)) := by
  intro x hx
  unfold gaussianSpectralTargetCaptureSet at hx
  unfold gaussianTwistedCoherenceCaptureSet
  exact targetCapture_implies_anchorCoherence hweight hweightSum htarget
    hepsilon hepsilonHalf hx

theorem uniformTargetCapture_subset_twistedCoherence
    {I : Type*} [Fintype I]
    {weight energy : I → ℝ}
    (hweight : ∀ i, 0 ≤ weight i)
    (hweightSum : ∑ i, weight i = 1)
    {target : EuclideanSpace ℂ I} (htarget : ‖target‖ = 1)
    {epsilon T : ℝ} (hepsilon : 0 ≤ epsilon)
    (hepsilonHalf : epsilon ≤ 1 / 2) :
    uniformSpectralTargetCaptureSet
        weight energy target T epsilon ⊆
      uniformTwistedCoherenceCaptureSet weight energy
        (finiteSpectralTargetTwist weight energy target epsilon) T
        (Real.sqrt (1 - 4 * epsilon ^ 2)) := by
  intro t ht
  rcases ht with ⟨hcapture, hwindow⟩
  exact ⟨hwindow,
    targetCapture_implies_anchorCoherence hweight hweightSum htarget
      hepsilon hepsilonHalf hcapture⟩

/-- **Adaptive Gaussian target-dictionary shortcut law.**  Targets may be
chosen after observing sampled time.  Every normalized finite target
dictionary pays only its cardinality; all spectral obstructions are exposed
as exact replica collisions and intrinsic action resolution. -/
theorem gaussian_adaptiveTargetShortcut_actionLaw
    {I W : Type*} [Fintype I] [DecidableEq I] [Fintype W]
    {weight energy : I → ℝ}
    (hweight : ∀ i, 0 ≤ weight i)
    (hweightSum : ∑ i, weight i = 1)
    (target : W → EuclideanSpace ℂ I)
    (htarget : ∀ w, ‖target w‖ = 1)
    (n : ℕ) (hn : 0 < n) {T epsilon : ℝ}
    (hT : 0 < T) (hepsilon : 0 ≤ epsilon)
    (hepsilonHalf : epsilon ≤ 1 / 2) :
    Real.sqrt (1 - 4 * epsilon ^ 2) ^ (2 * n) *
        (gaussianReal 0 1).real
          (⋃ w : W, gaussianSpectralTargetCaptureSet
            weight energy (target w) T epsilon) ≤
      (Fintype.card W : ℝ) *
        (fidelityReplicaCollisionMass weight energy n +
          Real.exp
            (-((T * intrinsicReplicaActionResolution energy n) ^ 2) / 2)) := by
  let twist : W → I → ℂ := fun w ↦
    finiteSpectralTargetTwist weight energy (target w) epsilon
  have hsubset :
      (⋃ w : W, gaussianSpectralTargetCaptureSet
          weight energy (target w) T epsilon) ⊆
        ⋃ w : W, gaussianTwistedCoherenceCaptureSet
          weight energy (twist w) T
          (Real.sqrt (1 - 4 * epsilon ^ 2)) := by
    intro x hx
    simp only [Set.mem_iUnion] at hx ⊢
    obtain ⟨w, hw⟩ := hx
    exact ⟨w, gaussianTargetCapture_subset_twistedCoherence
      hweight hweightSum (htarget w) hepsilon hepsilonHalf hw⟩
  have hpow : 0 ≤ Real.sqrt (1 - 4 * epsilon ^ 2) ^ (2 * n) :=
    pow_nonneg (Real.sqrt_nonneg _) _
  calc
    Real.sqrt (1 - 4 * epsilon ^ 2) ^ (2 * n) *
        (gaussianReal 0 1).real
          (⋃ w : W, gaussianSpectralTargetCaptureSet
            weight energy (target w) T epsilon)
        ≤ Real.sqrt (1 - 4 * epsilon ^ 2) ^ (2 * n) *
          (gaussianReal 0 1).real
            (⋃ w : W, gaussianTwistedCoherenceCaptureSet
              weight energy (twist w) T
              (Real.sqrt (1 - 4 * epsilon ^ 2))) :=
      mul_le_mul_of_nonneg_left (measureReal_mono hsubset) hpow
    _ ≤ _ :=
      threshold_pow_mul_gaussianAdaptiveCoherenceShortcut_measureReal_le_intrinsic
        hweight hweightSum
        (fun w i ↦ norm_finiteSpectralTargetTwist
          weight energy (target w) epsilon i)
        n hn hT (Real.sqrt_nonneg _)

/-- Uniform-window version of the adaptive target-dictionary shortcut law. -/
theorem uniform_adaptiveTargetShortcut_actionLaw
    {I W : Type*} [Fintype I] [DecidableEq I] [Fintype W]
    {weight energy : I → ℝ}
    (hweight : ∀ i, 0 ≤ weight i)
    (hweightSum : ∑ i, weight i = 1)
    (target : W → EuclideanSpace ℂ I)
    (htarget : ∀ w, ‖target w‖ = 1)
    (n : ℕ) (hn : 0 < n) {T epsilon : ℝ}
    (hT : 0 < T) (hepsilon : 0 ≤ epsilon)
    (hepsilonHalf : epsilon ≤ 1 / 2) :
    Real.sqrt (1 - 4 * epsilon ^ 2) ^ (2 * n) *
        volume.real
          (⋃ w : W, uniformSpectralTargetCaptureSet
            weight energy (target w) T epsilon) ≤
      2 * T * (Fintype.card W : ℝ) *
        (fidelityReplicaCollisionMass weight energy n +
          min 1
            (T * intrinsicReplicaActionResolution energy n)⁻¹) := by
  let twist : W → I → ℂ := fun w ↦
    finiteSpectralTargetTwist weight energy (target w) epsilon
  have hsubset :
      (⋃ w : W, uniformSpectralTargetCaptureSet
          weight energy (target w) T epsilon) ⊆
        ⋃ w : W, uniformTwistedCoherenceCaptureSet
          weight energy (twist w) T
          (Real.sqrt (1 - 4 * epsilon ^ 2)) := by
    intro t ht
    simp only [Set.mem_iUnion] at ht ⊢
    obtain ⟨w, hw⟩ := ht
    exact ⟨w, uniformTargetCapture_subset_twistedCoherence
      hweight hweightSum (htarget w) hepsilon hepsilonHalf hw⟩
  have hpow : 0 ≤ Real.sqrt (1 - 4 * epsilon ^ 2) ^ (2 * n) :=
    pow_nonneg (Real.sqrt_nonneg _) _
  have hwindow :
      (⋃ w : W, uniformTwistedCoherenceCaptureSet
          weight energy (twist w) T
          (Real.sqrt (1 - 4 * epsilon ^ 2))) ⊆ Set.Ioc (-T) T := by
    intro t ht
    simp only [Set.mem_iUnion] at ht
    obtain ⟨w, hw⟩ := ht
    exact hw.1
  have hfinite :
      volume
          (⋃ w : W, uniformTwistedCoherenceCaptureSet
            weight energy (twist w) T
            (Real.sqrt (1 - 4 * epsilon ^ 2))) ≠ ∞ := by
    exact ne_of_lt ((measure_mono hwindow).trans_lt measure_Ioc_lt_top)
  calc
    Real.sqrt (1 - 4 * epsilon ^ 2) ^ (2 * n) *
        volume.real
          (⋃ w : W, uniformSpectralTargetCaptureSet
            weight energy (target w) T epsilon)
        ≤ Real.sqrt (1 - 4 * epsilon ^ 2) ^ (2 * n) *
          volume.real
            (⋃ w : W, uniformTwistedCoherenceCaptureSet
              weight energy (twist w) T
              (Real.sqrt (1 - 4 * epsilon ^ 2))) :=
      mul_le_mul_of_nonneg_left (measureReal_mono hsubset hfinite) hpow
    _ ≤ _ :=
      threshold_pow_mul_uniformAdaptiveCoherenceShortcut_measureReal_le_intrinsic
        hweight hweightSum
        (fun w i ↦ norm_finiteSpectralTargetTwist
          weight energy (target w) epsilon i)
        n hn hT (Real.sqrt_nonneg _)

/-- Probability-normalized Gaussian form, exposing the inverse replica
coherence factor used in shortcut estimates. -/
theorem gaussian_adaptiveTargetShortcut_probability_le
    {I W : Type*} [Fintype I] [DecidableEq I] [Fintype W]
    {weight energy : I → ℝ}
    (hweight : ∀ i, 0 ≤ weight i)
    (hweightSum : ∑ i, weight i = 1)
    (target : W → EuclideanSpace ℂ I)
    (htarget : ∀ w, ‖target w‖ = 1)
    (n : ℕ) (hn : 0 < n) {T epsilon : ℝ}
    (hT : 0 < T) (hepsilon : 0 ≤ epsilon)
    (hepsilonHalf : epsilon < 1 / 2) :
    (gaussianReal 0 1).real
          (⋃ w : W, gaussianSpectralTargetCaptureSet
            weight energy (target w) T epsilon) ≤
      (Fintype.card W : ℝ) *
        (Real.sqrt (1 - 4 * epsilon ^ 2) ^ (2 * n))⁻¹ *
        (fidelityReplicaCollisionMass weight energy n +
          Real.exp
            (-((T * intrinsicReplicaActionResolution energy n) ^ 2) / 2)) := by
  have hrad : 0 < 1 - 4 * epsilon ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr hepsilonHalf)
      (by nlinarith : 0 < 1 + 2 * epsilon)]
  have hpow : 0 < Real.sqrt (1 - 4 * epsilon ^ 2) ^ (2 * n) :=
    pow_pos (Real.sqrt_pos.2 hrad) _
  have hmain := gaussian_adaptiveTargetShortcut_actionLaw
    (energy := energy) hweight hweightSum target htarget n hn hT hepsilon
      hepsilonHalf.le
  calc
    _ ≤ ((Fintype.card W : ℝ) *
          (fidelityReplicaCollisionMass weight energy n +
            Real.exp
              (-((T * intrinsicReplicaActionResolution energy n) ^ 2) / 2))) /
        (Real.sqrt (1 - 4 * epsilon ^ 2) ^ (2 * n)) :=
      (le_div_iff₀ hpow).2 (by simpa [mul_comm] using hmain)
    _ = _ := by rw [div_eq_mul_inv]; ring

/-- Uniform probability is Lebesgue mass divided by window length `2T`. -/
theorem uniform_adaptiveTargetShortcut_probability_le
    {I W : Type*} [Fintype I] [DecidableEq I] [Fintype W]
    {weight energy : I → ℝ}
    (hweight : ∀ i, 0 ≤ weight i)
    (hweightSum : ∑ i, weight i = 1)
    (target : W → EuclideanSpace ℂ I)
    (htarget : ∀ w, ‖target w‖ = 1)
    (n : ℕ) (hn : 0 < n) {T epsilon : ℝ}
    (hT : 0 < T) (hepsilon : 0 ≤ epsilon)
    (hepsilonHalf : epsilon < 1 / 2) :
    volume.real
          (⋃ w : W, uniformSpectralTargetCaptureSet
            weight energy (target w) T epsilon) / (2 * T) ≤
      (Fintype.card W : ℝ) *
        (Real.sqrt (1 - 4 * epsilon ^ 2) ^ (2 * n))⁻¹ *
        (fidelityReplicaCollisionMass weight energy n +
          min 1
            (T * intrinsicReplicaActionResolution energy n)⁻¹) := by
  have hrad : 0 < 1 - 4 * epsilon ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr hepsilonHalf)
      (by nlinarith : 0 < 1 + 2 * epsilon)]
  have hpow : 0 < Real.sqrt (1 - 4 * epsilon ^ 2) ^ (2 * n) :=
    pow_pos (Real.sqrt_pos.2 hrad) _
  have hmain := uniform_adaptiveTargetShortcut_actionLaw
    (energy := energy) hweight hweightSum target htarget n hn hT hepsilon
      hepsilonHalf.le
  apply (div_le_iff₀ (by positivity : 0 < 2 * T)).2
  calc
    _ ≤ (2 * T * (Fintype.card W : ℝ) *
          (fidelityReplicaCollisionMass weight energy n +
            min 1
              (T * intrinsicReplicaActionResolution energy n)⁻¹)) /
        (Real.sqrt (1 - 4 * epsilon ^ 2) ^ (2 * n)) :=
      (le_div_iff₀ hpow).2 (by simpa [mul_comm] using hmain)
    _ = _ := by rw [div_eq_mul_inv]; ring


/-- Gaussian padded-circuit probability form with exact dictionary entropy. -/
theorem gaussian_adaptivePaddedCircuitShortcut_probability_le
    {I gate : Type*} [Fintype I] [DecidableEq I] [Fintype gate]
    {weight energy : I → ℝ}
    (hweight : ∀ i, 0 ≤ weight i)
    (hweightSum : ∑ i, weight i = 1)
    (s : ℕ)
    (target : PaddedCircuitWord gate s → EuclideanSpace ℂ I)
    (htarget : ∀ w, ‖target w‖ = 1)
    (n : ℕ) (hn : 0 < n) {T epsilon : ℝ}
    (hT : 0 < T) (hepsilon : 0 ≤ epsilon)
    (hepsilonHalf : epsilon < 1 / 2) :
    (gaussianReal 0 1).real
          (⋃ w : PaddedCircuitWord gate s,
            gaussianSpectralTargetCaptureSet
              weight energy (target w) T epsilon) ≤
      (Fintype.card gate : ℝ) ^ (s + 1) *
        (Real.sqrt (1 - 4 * epsilon ^ 2) ^ (2 * n))⁻¹ *
        (fidelityReplicaCollisionMass weight energy n +
          Real.exp
            (-((T * intrinsicReplicaActionResolution energy n) ^ 2) / 2)) := by
  simpa only [card_paddedCircuitWord, Nat.cast_pow] using
    gaussian_adaptiveTargetShortcut_probability_le
      (energy := energy) hweight hweightSum target htarget n hn hT hepsilon
        hepsilonHalf

/-- Uniform padded-circuit probability form with exact dictionary entropy. -/
theorem uniform_adaptivePaddedCircuitShortcut_probability_le
    {I gate : Type*} [Fintype I] [DecidableEq I] [Fintype gate]
    {weight energy : I → ℝ}
    (hweight : ∀ i, 0 ≤ weight i)
    (hweightSum : ∑ i, weight i = 1)
    (s : ℕ)
    (target : PaddedCircuitWord gate s → EuclideanSpace ℂ I)
    (htarget : ∀ w, ‖target w‖ = 1)
    (n : ℕ) (hn : 0 < n) {T epsilon : ℝ}
    (hT : 0 < T) (hepsilon : 0 ≤ epsilon)
    (hepsilonHalf : epsilon < 1 / 2) :
    volume.real
          (⋃ w : PaddedCircuitWord gate s,
            uniformSpectralTargetCaptureSet
              weight energy (target w) T epsilon) / (2 * T) ≤
      (Fintype.card gate : ℝ) ^ (s + 1) *
        (Real.sqrt (1 - 4 * epsilon ^ 2) ^ (2 * n))⁻¹ *
        (fidelityReplicaCollisionMass weight energy n +
          min 1
            (T * intrinsicReplicaActionResolution energy n)⁻¹) := by
  simpa only [card_paddedCircuitWord, Nat.cast_pow] using
    uniform_adaptiveTargetShortcut_probability_le
      (energy := energy) hweight hweightSum target htarget n hn hT hepsilon
        hepsilonHalf

/-- A gate alphabet with padded words of length `s + 1` pays exactly
`|gate|^(s+1)` in the Gaussian adaptive shortcut law. -/
theorem gaussian_adaptivePaddedCircuitShortcut_actionLaw
    {I gate : Type*} [Fintype I] [DecidableEq I] [Fintype gate]
    {weight energy : I → ℝ}
    (hweight : ∀ i, 0 ≤ weight i)
    (hweightSum : ∑ i, weight i = 1)
    (s : ℕ)
    (target : PaddedCircuitWord gate s → EuclideanSpace ℂ I)
    (htarget : ∀ w, ‖target w‖ = 1)
    (n : ℕ) (hn : 0 < n) {T epsilon : ℝ}
    (hT : 0 < T) (hepsilon : 0 ≤ epsilon)
    (hepsilonHalf : epsilon ≤ 1 / 2) :
    Real.sqrt (1 - 4 * epsilon ^ 2) ^ (2 * n) *
        (gaussianReal 0 1).real
          (⋃ w : PaddedCircuitWord gate s,
            gaussianSpectralTargetCaptureSet
              weight energy (target w) T epsilon) ≤
      (Fintype.card gate : ℝ) ^ (s + 1) *
        (fidelityReplicaCollisionMass weight energy n +
          Real.exp
            (-((T * intrinsicReplicaActionResolution energy n) ^ 2) / 2)) := by
  simpa only [card_paddedCircuitWord, Nat.cast_pow] using
    gaussian_adaptiveTargetShortcut_actionLaw
      hweight hweightSum target htarget n hn hT hepsilon hepsilonHalf

/-- Uniform-window padded-circuit counterpart. -/
theorem uniform_adaptivePaddedCircuitShortcut_actionLaw
    {I gate : Type*} [Fintype I] [DecidableEq I] [Fintype gate]
    {weight energy : I → ℝ}
    (hweight : ∀ i, 0 ≤ weight i)
    (hweightSum : ∑ i, weight i = 1)
    (s : ℕ)
    (target : PaddedCircuitWord gate s → EuclideanSpace ℂ I)
    (htarget : ∀ w, ‖target w‖ = 1)
    (n : ℕ) (hn : 0 < n) {T epsilon : ℝ}
    (hT : 0 < T) (hepsilon : 0 ≤ epsilon)
    (hepsilonHalf : epsilon ≤ 1 / 2) :
    Real.sqrt (1 - 4 * epsilon ^ 2) ^ (2 * n) *
        volume.real
          (⋃ w : PaddedCircuitWord gate s,
            uniformSpectralTargetCaptureSet
              weight energy (target w) T epsilon) ≤
      2 * T * (Fintype.card gate : ℝ) ^ (s + 1) *
        (fidelityReplicaCollisionMass weight energy n +
          min 1
            (T * intrinsicReplicaActionResolution energy n)⁻¹) := by
  simpa only [card_paddedCircuitWord, Nat.cast_pow] using
    uniform_adaptiveTargetShortcut_actionLaw
      hweight hweightSum target htarget n hn hT hepsilon hepsilonHalf

/-- Under maximal projective rank and full spectral support, the Gaussian
circuit-shortcut collision term is exactly the permutation floor. -/
theorem gaussian_adaptivePaddedCircuitShortcut_actionLaw_floor
    {I gate : Type*} [Fintype I] [DecidableEq I] [Fintype gate]
    {weight energy : I → ℝ}
    (hweight : ∀ i, 0 < weight i)
    (hweightSum : ∑ i, weight i = 1)
    (hmax : MaximallyProjectiveEnergy energy)
    (s : ℕ)
    (target : PaddedCircuitWord gate s → EuclideanSpace ℂ I)
    (htarget : ∀ w, ‖target w‖ = 1)
    (n : ℕ) (hn : 0 < n) {T epsilon : ℝ}
    (hT : 0 < T) (hepsilon : 0 ≤ epsilon)
    (hepsilonHalf : epsilon ≤ 1 / 2) :
    Real.sqrt (1 - 4 * epsilon ^ 2) ^ (2 * n) *
        (gaussianReal 0 1).real
          (⋃ w : PaddedCircuitWord gate s,
            gaussianSpectralTargetCaptureSet
              weight energy (target w) T epsilon) ≤
      (Fintype.card gate : ℝ) ^ (s + 1) *
        (fidelityReplicaPermutationFloor weight n +
          Real.exp
            (-((T * intrinsicReplicaActionResolution energy n) ^ 2) / 2)) := by
  rw [← (all_fidelityReplicaCollisionMass_eq_floor_iff
    hweight energy).2 hmax n]
  exact gaussian_adaptivePaddedCircuitShortcut_actionLaw
    (fun i => (hweight i).le) hweightSum s target htarget n hn hT
    hepsilon hepsilonHalf

/-- Maximal-projective uniform-window padded-circuit counterpart. -/
theorem uniform_adaptivePaddedCircuitShortcut_actionLaw_floor
    {I gate : Type*} [Fintype I] [DecidableEq I] [Fintype gate]
    {weight energy : I → ℝ}
    (hweight : ∀ i, 0 < weight i)
    (hweightSum : ∑ i, weight i = 1)
    (hmax : MaximallyProjectiveEnergy energy)
    (s : ℕ)
    (target : PaddedCircuitWord gate s → EuclideanSpace ℂ I)
    (htarget : ∀ w, ‖target w‖ = 1)
    (n : ℕ) (hn : 0 < n) {T epsilon : ℝ}
    (hT : 0 < T) (hepsilon : 0 ≤ epsilon)
    (hepsilonHalf : epsilon ≤ 1 / 2) :
    Real.sqrt (1 - 4 * epsilon ^ 2) ^ (2 * n) *
        volume.real
          (⋃ w : PaddedCircuitWord gate s,
            uniformSpectralTargetCaptureSet
              weight energy (target w) T epsilon) ≤
      2 * T * (Fintype.card gate : ℝ) ^ (s + 1) *
        (fidelityReplicaPermutationFloor weight n +
          min 1
            (T * intrinsicReplicaActionResolution energy n)⁻¹) := by
  rw [← (all_fidelityReplicaCollisionMass_eq_floor_iff
    hweight energy).2 hmax n]
  exact uniform_adaptivePaddedCircuitShortcut_actionLaw
    (fun i => (hweight i).le) hweightSum s target htarget n hn hT
    hepsilon hepsilonHalf

end RHTower
