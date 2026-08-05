import GaloisForLFunctions.RHTower.AdaptiveCircuitShortcutActionLaw
import GaloisForLFunctions.RHTower.StaticChoiQuantitativeRecurrenceUpperLaw
import GaloisForLFunctions.HTGeometry.FiniteEntropyPlateauFutureLaw

/-!
# Adaptive static-Choi circuit-shortcut action law

This module closes the operational gap between spectral phase-orbit laws and
channel circuit targets. For every nonempty finite static spectrum, every
finite dictionary of normalized states in the full Choi Hilbert space, and a
target selector allowed to inspect time, it bounds shortcut probability by
exact dictionary entropy, replica collision mass, and intrinsic action
resolution. Padded circuit words have exact entropy `|gate|^(s+1)`; maximal
projective spectra replace collision mass by the replica permutation floor.

No target is assumed to lie in the diagonal spectral subspace. The proof
chooses one captured orbit anchor for each arbitrary full-space target and
reduces every later capture to a phase-twisted orbit overlap.
-/

open scoped BigOperators ComplexConjugate Interval ENNReal NNReal
open MeasureTheory ProbabilityTheory

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry

theorem inner_staticSpectralChoiVector_eq_twistedAmplitude
    {d : ℕ} (hd : 0 < d) (t anchor : ℝ) (energy : Fin d → ℝ) :
    inner ℂ
        (staticSpectralChoiVector d anchor energy)
        (staticSpectralChoiVector d t energy) =
      twistedFiniteSpectralAmplitude (microcanonicalWeight (Fin d)) energy
        (finiteSpectralAnchorTwist energy anchor) t := by
  rw [EuclideanSpace.inner_toLp_toLp]
  change
    (∑ ij : Fin d × Fin d,
      (if ij.1 = ij.2 then
            ((Real.sqrt (d : ℝ))⁻¹ : ℂ) *
              fourier 1
                (finiteHamiltonianAddCirclePhase t energy ij.1)
        else 0) *
      starRingEnd ℂ
        (if ij.1 = ij.2 then
            ((Real.sqrt (d : ℝ))⁻¹ : ℂ) *
              fourier 1
                (finiteHamiltonianAddCirclePhase anchor energy ij.1)
          else 0)) = _
  rw [Fintype.sum_prod_type]
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hsqrt : Real.sqrt (d : ℝ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hdR)
  have hreal :
      (Real.sqrt (d : ℝ))⁻¹ * (Real.sqrt (d : ℝ))⁻¹ =
        (d : ℝ)⁻¹ := by
    field_simp [hsqrt]
    simp [pow_two, Real.mul_self_sqrt hdR.le]
  have hcoef :
      (((Real.sqrt (d : ℝ))⁻¹ : ℂ) *
          starRingEnd ℂ (((Real.sqrt (d : ℝ))⁻¹ : ℂ))) =
        (d : ℂ)⁻¹ := by
    rw [starRingEnd_apply, Complex.star_def, map_inv₀,
      Complex.conj_ofReal]
    calc
      (↑(Real.sqrt (d : ℝ)) : ℂ)⁻¹ *
            (↑(Real.sqrt (d : ℝ)) : ℂ)⁻¹ =
          (((Real.sqrt (d : ℝ))⁻¹ *
            (Real.sqrt (d : ℝ))⁻¹ : ℝ) : ℂ) := by
              rw [Complex.ofReal_mul, Complex.ofReal_inv]
      _ = (((d : ℝ)⁻¹ : ℝ) : ℂ) :=
        congrArg (fun x : ℝ ↦ (x : ℂ)) hreal
      _ = (d : ℂ)⁻¹ := by
        rw [Complex.ofReal_inv, Complex.ofReal_natCast]
  simp_rw [fourier_finiteHamiltonianAddCirclePhase]
  simp_rw [apply_ite (starRingEnd ℂ)]
  simp only [map_zero, ite_mul, zero_mul]
  have hdiag (i j : Fin d) :
      (if i = j then
          ((Real.sqrt (d : ℝ))⁻¹ : ℂ) *
              finiteObserverHamiltonianVertexPhase t energy i *
            if i = j then
              starRingEnd ℂ
                (((Real.sqrt (d : ℝ))⁻¹ : ℂ) *
                  finiteObserverHamiltonianVertexPhase anchor energy i)
            else 0
        else 0) =
        if i = j then
          (((Real.sqrt (d : ℝ))⁻¹ : ℂ) *
              finiteObserverHamiltonianVertexPhase t energy i) *
            starRingEnd ℂ
              (((Real.sqrt (d : ℝ))⁻¹ : ℂ) *
                finiteObserverHamiltonianVertexPhase anchor energy i)
        else 0 := by
    by_cases hij : i = j <;> simp [hij]
  simp_rw [hdiag]
  simp only [Fintype.sum_ite_eq]
  unfold twistedFiniteSpectralAmplitude microcanonicalWeight
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_mul]
  rw [show
      starRingEnd ℂ (finiteObserverHamiltonianVertexPhase anchor energy i) =
        Complex.exp (((-energy i * anchor : ℝ) : ℂ) * Complex.I) by
    unfold finiteObserverHamiltonianVertexPhase
    rw [starRingEnd_apply, Complex.star_def, ← Complex.exp_conj]
    congr 1
    push_cast
    simp
    ring_nf]
  calc
    (((Real.sqrt (d : ℝ))⁻¹ : ℂ) *
          finiteObserverHamiltonianVertexPhase t energy i) *
        (((starRingEnd ℂ) (((Real.sqrt (d : ℝ))⁻¹ : ℂ)) *
          Complex.exp (((-energy i * anchor : ℝ) : ℂ) * Complex.I))) =
      ((((Real.sqrt (d : ℝ))⁻¹ : ℂ) *
          starRingEnd ℂ (((Real.sqrt (d : ℝ))⁻¹ : ℂ))) *
        finiteObserverHamiltonianVertexPhase t energy i *
          Complex.exp (((-energy i * anchor : ℝ) : ℂ) * Complex.I)) := by ring
    _ = _ := by
      rw [hcoef]
      simp only [Fintype.card_fin, Complex.ofReal_inv,
        Complex.ofReal_natCast]
      unfold finiteObserverHamiltonianVertexPhase finiteSpectralAnchorTwist
      ring_nf

def staticChoiTargetCaptureSet
    {d : ℕ} (energy : Fin d → ℝ)
    (target : EuclideanSpace ℂ (Fin d × Fin d))
    (epsilon : ℝ) : Set ℝ :=
  {t | pureStateTraceDistance
    (staticSpectralChoiVector d t energy) target ≤ epsilon}

noncomputable def staticChoiTargetAnchor
    {d : ℕ} (energy : Fin d → ℝ)
    (target : EuclideanSpace ℂ (Fin d × Fin d))
    (epsilon : ℝ) : ℝ := by
  classical
  exact
    if h : (staticChoiTargetCaptureSet energy target epsilon).Nonempty then
      Classical.choose h
    else 0

def staticChoiTargetTwist
    {d : ℕ} (energy : Fin d → ℝ)
    (target : EuclideanSpace ℂ (Fin d × Fin d))
    (epsilon : ℝ) (i : Fin d) : ℂ :=
  finiteSpectralAnchorTwist energy
    (staticChoiTargetAnchor energy target epsilon) i

theorem norm_staticChoiTargetTwist
    {d : ℕ} (energy : Fin d → ℝ)
    (target : EuclideanSpace ℂ (Fin d × Fin d))
    (epsilon : ℝ) (i : Fin d) :
    ‖staticChoiTargetTwist energy target epsilon i‖ = 1 :=
  norm_finiteSpectralAnchorTwist energy _ i

theorem staticChoiTargetCapture_implies_anchorCoherence
    {d : ℕ} (hd : 0 < d) {energy : Fin d → ℝ}
    {target : EuclideanSpace ℂ (Fin d × Fin d)}
    (htarget : ‖target‖ = 1)
    {epsilon t : ℝ} (hepsilon : 0 ≤ epsilon)
    (hepsilonHalf : epsilon ≤ 1 / 2)
    (ht : t ∈ staticChoiTargetCaptureSet energy target epsilon) :
    Real.sqrt (1 - 4 * epsilon ^ 2) ≤
      ‖twistedFiniteSpectralAmplitude (microcanonicalWeight (Fin d)) energy
        (staticChoiTargetTwist energy target epsilon) t‖ := by
  have hactive :
      (staticChoiTargetCaptureSet energy target epsilon).Nonempty := ⟨t, ht⟩
  have hanchor :
      staticChoiTargetAnchor energy target epsilon ∈
        staticChoiTargetCaptureSet energy target epsilon := by
    unfold staticChoiTargetAnchor
    rw [dif_pos hactive]
    exact Classical.choose_spec hactive
  have ht' : pureStateTraceDistance
      (staticSpectralChoiVector d t energy) target ≤ epsilon := ht
  have hanchor' : pureStateTraceDistance
      (staticSpectralChoiVector d
        (staticChoiTargetAnchor energy target epsilon) energy) target ≤
        epsilon := hanchor
  have htargetAnchor : pureStateTraceDistance target
      (staticSpectralChoiVector d
        (staticChoiTargetAnchor energy target epsilon) energy) ≤ epsilon := by
    rw [pureStateTraceDistance_comm]
    exact hanchor'
  have hbetween : pureStateTraceDistance
      (staticSpectralChoiVector d t energy)
      (staticSpectralChoiVector d
        (staticChoiTargetAnchor energy target epsilon) energy) ≤
      2 * epsilon := by
    calc
      _ ≤ pureStateTraceDistance
            (staticSpectralChoiVector d t energy) target +
          pureStateTraceDistance target
            (staticSpectralChoiVector d
              (staticChoiTargetAnchor energy target epsilon) energy) :=
        pureStateTraceDistance_triangle _ _ _
          (staticSpectralChoiVector_norm hd t energy) htarget
          (staticSpectralChoiVector_norm hd _ energy)
      _ ≤ epsilon + epsilon := add_le_add ht' htargetAnchor
      _ = 2 * epsilon := by ring
  have hcoherence :=
    norm_inner_ge_sqrt_one_sub_four_mul_sq_of_traceDistance_le
      (staticSpectralChoiVector d t energy)
      (staticSpectralChoiVector d
        (staticChoiTargetAnchor energy target epsilon) energy)
      (staticSpectralChoiVector_norm hd t energy)
      (staticSpectralChoiVector_norm hd _ energy)
      hepsilon hepsilonHalf hbetween
  rw [norm_inner_symm] at hcoherence
  rw [inner_staticSpectralChoiVector_eq_twistedAmplitude
    hd t (staticChoiTargetAnchor energy target epsilon) energy] at hcoherence
  change Real.sqrt (1 - 4 * epsilon ^ 2) ≤
    ‖twistedFiniteSpectralAmplitude (microcanonicalWeight (Fin d)) energy
      (finiteSpectralAnchorTwist energy
        (staticChoiTargetAnchor energy target epsilon)) t‖
  exact hcoherence

def gaussianStaticChoiTargetCaptureSet
    {d : ℕ} (energy : Fin d → ℝ)
    (target : EuclideanSpace ℂ (Fin d × Fin d))
    (T epsilon : ℝ) : Set ℝ :=
  {x | T * x ∈ staticChoiTargetCaptureSet energy target epsilon}

def uniformStaticChoiTargetCaptureSet
    {d : ℕ} (energy : Fin d → ℝ)
    (target : EuclideanSpace ℂ (Fin d × Fin d))
    (T epsilon : ℝ) : Set ℝ :=
  staticChoiTargetCaptureSet energy target epsilon ∩ Set.Ioc (-T) T

theorem gaussianStaticChoiTargetCapture_subset_twistedCoherence
    {d : ℕ} (hd : 0 < d) {energy : Fin d → ℝ}
    {target : EuclideanSpace ℂ (Fin d × Fin d)}
    (htarget : ‖target‖ = 1)
    {epsilon T : ℝ} (hepsilon : 0 ≤ epsilon)
    (hepsilonHalf : epsilon ≤ 1 / 2) :
    gaussianStaticChoiTargetCaptureSet energy target T epsilon ⊆
      gaussianTwistedCoherenceCaptureSet
        (microcanonicalWeight (Fin d)) energy
        (staticChoiTargetTwist energy target epsilon) T
        (Real.sqrt (1 - 4 * epsilon ^ 2)) := by
  intro x hx
  unfold gaussianStaticChoiTargetCaptureSet at hx
  unfold gaussianTwistedCoherenceCaptureSet
  exact staticChoiTargetCapture_implies_anchorCoherence hd htarget
    hepsilon hepsilonHalf hx

theorem uniformStaticChoiTargetCapture_subset_twistedCoherence
    {d : ℕ} (hd : 0 < d) {energy : Fin d → ℝ}
    {target : EuclideanSpace ℂ (Fin d × Fin d)}
    (htarget : ‖target‖ = 1)
    {epsilon T : ℝ} (hepsilon : 0 ≤ epsilon)
    (hepsilonHalf : epsilon ≤ 1 / 2) :
    uniformStaticChoiTargetCaptureSet energy target T epsilon ⊆
      uniformTwistedCoherenceCaptureSet
        (microcanonicalWeight (Fin d)) energy
        (staticChoiTargetTwist energy target epsilon) T
        (Real.sqrt (1 - 4 * epsilon ^ 2)) := by
  intro t ht
  rcases ht with ⟨hcapture, hwindow⟩
  exact ⟨hwindow,
    staticChoiTargetCapture_implies_anchorCoherence hd htarget
      hepsilon hepsilonHalf hcapture⟩

/-- Adaptive Gaussian shortcut law for arbitrary normalized targets in the
full Choi Hilbert space. -/
theorem gaussian_adaptiveStaticChoiTargetShortcut_actionLaw
    {d : ℕ} (hd : 0 < d)
    {W : Type*} [Fintype W] {energy : Fin d → ℝ}
    (target : W → EuclideanSpace ℂ (Fin d × Fin d))
    (htarget : ∀ w, ‖target w‖ = 1)
    (n : ℕ) (hn : 0 < n) {T epsilon : ℝ}
    (hT : 0 < T) (hepsilon : 0 ≤ epsilon)
    (hepsilonHalf : epsilon ≤ 1 / 2) :
    Real.sqrt (1 - 4 * epsilon ^ 2) ^ (2 * n) *
        (gaussianReal 0 1).real
          (⋃ w : W, gaussianStaticChoiTargetCaptureSet
            energy (target w) T epsilon) ≤
      (Fintype.card W : ℝ) *
        (fidelityReplicaCollisionMass
            (microcanonicalWeight (Fin d)) energy n +
          Real.exp
            (-((T * intrinsicReplicaActionResolution energy n) ^ 2) / 2)) := by
  letI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  let twist : W → Fin d → ℂ := fun w ↦
    staticChoiTargetTwist energy (target w) epsilon
  have hsubset :
      (⋃ w : W, gaussianStaticChoiTargetCaptureSet
          energy (target w) T epsilon) ⊆
        ⋃ w : W, gaussianTwistedCoherenceCaptureSet
          (microcanonicalWeight (Fin d)) energy (twist w) T
          (Real.sqrt (1 - 4 * epsilon ^ 2)) := by
    intro x hx
    simp only [Set.mem_iUnion] at hx ⊢
    obtain ⟨w, hw⟩ := hx
    exact ⟨w, gaussianStaticChoiTargetCapture_subset_twistedCoherence
      hd (htarget w) hepsilon hepsilonHalf hw⟩
  have hpow : 0 ≤ Real.sqrt (1 - 4 * epsilon ^ 2) ^ (2 * n) :=
    pow_nonneg (Real.sqrt_nonneg _) _
  calc
    Real.sqrt (1 - 4 * epsilon ^ 2) ^ (2 * n) *
        (gaussianReal 0 1).real
          (⋃ w : W, gaussianStaticChoiTargetCaptureSet
            energy (target w) T epsilon)
        ≤ Real.sqrt (1 - 4 * epsilon ^ 2) ^ (2 * n) *
          (gaussianReal 0 1).real
            (⋃ w : W, gaussianTwistedCoherenceCaptureSet
              (microcanonicalWeight (Fin d)) energy (twist w) T
              (Real.sqrt (1 - 4 * epsilon ^ 2))) :=
      mul_le_mul_of_nonneg_left (measureReal_mono hsubset) hpow
    _ ≤ _ :=
      threshold_pow_mul_gaussianAdaptiveCoherenceShortcut_measureReal_le_intrinsic
        (fun i => (microcanonicalWeight_pos (Fin d) i).le)
        (sum_microcanonicalWeight_eq_one (Fin d))
        (fun w i => norm_staticChoiTargetTwist energy (target w) epsilon i)
        n hn hT (Real.sqrt_nonneg _)

/-- Uniform-window counterpart of the full-Choi adaptive shortcut law. -/
theorem uniform_adaptiveStaticChoiTargetShortcut_actionLaw
    {d : ℕ} (hd : 0 < d)
    {W : Type*} [Fintype W] {energy : Fin d → ℝ}
    (target : W → EuclideanSpace ℂ (Fin d × Fin d))
    (htarget : ∀ w, ‖target w‖ = 1)
    (n : ℕ) (hn : 0 < n) {T epsilon : ℝ}
    (hT : 0 < T) (hepsilon : 0 ≤ epsilon)
    (hepsilonHalf : epsilon ≤ 1 / 2) :
    Real.sqrt (1 - 4 * epsilon ^ 2) ^ (2 * n) *
        volume.real
          (⋃ w : W, uniformStaticChoiTargetCaptureSet
            energy (target w) T epsilon) ≤
      2 * T * (Fintype.card W : ℝ) *
        (fidelityReplicaCollisionMass
            (microcanonicalWeight (Fin d)) energy n +
          min 1 (T * intrinsicReplicaActionResolution energy n)⁻¹) := by
  letI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  let twist : W → Fin d → ℂ := fun w ↦
    staticChoiTargetTwist energy (target w) epsilon
  have hsubset :
      (⋃ w : W, uniformStaticChoiTargetCaptureSet
          energy (target w) T epsilon) ⊆
        ⋃ w : W, uniformTwistedCoherenceCaptureSet
          (microcanonicalWeight (Fin d)) energy (twist w) T
          (Real.sqrt (1 - 4 * epsilon ^ 2)) := by
    intro t ht
    simp only [Set.mem_iUnion] at ht ⊢
    obtain ⟨w, hw⟩ := ht
    exact ⟨w, uniformStaticChoiTargetCapture_subset_twistedCoherence
      hd (htarget w) hepsilon hepsilonHalf hw⟩
  have hpow : 0 ≤ Real.sqrt (1 - 4 * epsilon ^ 2) ^ (2 * n) :=
    pow_nonneg (Real.sqrt_nonneg _) _
  have hwindow :
      (⋃ w : W, uniformTwistedCoherenceCaptureSet
          (microcanonicalWeight (Fin d)) energy (twist w) T
          (Real.sqrt (1 - 4 * epsilon ^ 2))) ⊆ Set.Ioc (-T) T := by
    intro t ht
    simp only [Set.mem_iUnion] at ht
    obtain ⟨w, hw⟩ := ht
    exact hw.1
  have hfinite :
      volume
          (⋃ w : W, uniformTwistedCoherenceCaptureSet
            (microcanonicalWeight (Fin d)) energy (twist w) T
            (Real.sqrt (1 - 4 * epsilon ^ 2))) ≠ ∞ := by
    exact ne_of_lt ((measure_mono hwindow).trans_lt measure_Ioc_lt_top)
  calc
    Real.sqrt (1 - 4 * epsilon ^ 2) ^ (2 * n) *
        volume.real
          (⋃ w : W, uniformStaticChoiTargetCaptureSet
            energy (target w) T epsilon)
        ≤ Real.sqrt (1 - 4 * epsilon ^ 2) ^ (2 * n) *
          volume.real
            (⋃ w : W, uniformTwistedCoherenceCaptureSet
              (microcanonicalWeight (Fin d)) energy (twist w) T
              (Real.sqrt (1 - 4 * epsilon ^ 2))) :=
      mul_le_mul_of_nonneg_left (measureReal_mono hsubset hfinite) hpow
    _ ≤ _ :=
      threshold_pow_mul_uniformAdaptiveCoherenceShortcut_measureReal_le_intrinsic
        (fun i => (microcanonicalWeight_pos (Fin d) i).le)
        (sum_microcanonicalWeight_eq_one (Fin d))
        (fun w i => norm_staticChoiTargetTwist energy (target w) epsilon i)
        n hn hT (Real.sqrt_nonneg _)

/-- Probability-normalized Gaussian full-Choi adaptive shortcut law. -/
theorem gaussian_adaptiveStaticChoiTargetShortcut_probability_le
    {d : ℕ} (hd : 0 < d)
    {W : Type*} [Fintype W] {energy : Fin d → ℝ}
    (target : W → EuclideanSpace ℂ (Fin d × Fin d))
    (htarget : ∀ w, ‖target w‖ = 1)
    (n : ℕ) (hn : 0 < n) {T epsilon : ℝ}
    (hT : 0 < T) (hepsilon : 0 ≤ epsilon)
    (hepsilonHalf : epsilon < 1 / 2) :
    (gaussianReal 0 1).real
          (⋃ w : W, gaussianStaticChoiTargetCaptureSet
            energy (target w) T epsilon) ≤
      (Fintype.card W : ℝ) *
        (Real.sqrt (1 - 4 * epsilon ^ 2) ^ (2 * n))⁻¹ *
        (fidelityReplicaCollisionMass
            (microcanonicalWeight (Fin d)) energy n +
          Real.exp
            (-((T * intrinsicReplicaActionResolution energy n) ^ 2) / 2)) := by
  have hrad : 0 < 1 - 4 * epsilon ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr hepsilonHalf)
      (by nlinarith : 0 < 1 + 2 * epsilon)]
  have hpow : 0 < Real.sqrt (1 - 4 * epsilon ^ 2) ^ (2 * n) :=
    pow_pos (Real.sqrt_pos.2 hrad) _
  have hmain := gaussian_adaptiveStaticChoiTargetShortcut_actionLaw
    (energy := energy) hd target htarget n hn hT hepsilon hepsilonHalf.le
  calc
    _ ≤ ((Fintype.card W : ℝ) *
          (fidelityReplicaCollisionMass
              (microcanonicalWeight (Fin d)) energy n +
            Real.exp
              (-((T * intrinsicReplicaActionResolution energy n) ^ 2) / 2))) /
        (Real.sqrt (1 - 4 * epsilon ^ 2) ^ (2 * n)) :=
      (le_div_iff₀ hpow).2 (by simpa [mul_comm] using hmain)
    _ = _ := by rw [div_eq_mul_inv]; ring

/-- Probability-normalized uniform full-Choi adaptive shortcut law. -/
theorem uniform_adaptiveStaticChoiTargetShortcut_probability_le
    {d : ℕ} (hd : 0 < d)
    {W : Type*} [Fintype W] {energy : Fin d → ℝ}
    (target : W → EuclideanSpace ℂ (Fin d × Fin d))
    (htarget : ∀ w, ‖target w‖ = 1)
    (n : ℕ) (hn : 0 < n) {T epsilon : ℝ}
    (hT : 0 < T) (hepsilon : 0 ≤ epsilon)
    (hepsilonHalf : epsilon < 1 / 2) :
    volume.real
          (⋃ w : W, uniformStaticChoiTargetCaptureSet
            energy (target w) T epsilon) / (2 * T) ≤
      (Fintype.card W : ℝ) *
        (Real.sqrt (1 - 4 * epsilon ^ 2) ^ (2 * n))⁻¹ *
        (fidelityReplicaCollisionMass
            (microcanonicalWeight (Fin d)) energy n +
          min 1 (T * intrinsicReplicaActionResolution energy n)⁻¹) := by
  have hrad : 0 < 1 - 4 * epsilon ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr hepsilonHalf)
      (by nlinarith : 0 < 1 + 2 * epsilon)]
  have hpow : 0 < Real.sqrt (1 - 4 * epsilon ^ 2) ^ (2 * n) :=
    pow_pos (Real.sqrt_pos.2 hrad) _
  have hmain := uniform_adaptiveStaticChoiTargetShortcut_actionLaw
    (energy := energy) hd target htarget n hn hT hepsilon hepsilonHalf.le
  apply (div_le_iff₀ (by positivity : 0 < 2 * T)).2
  calc
    _ ≤ (2 * T * (Fintype.card W : ℝ) *
          (fidelityReplicaCollisionMass
              (microcanonicalWeight (Fin d)) energy n +
            min 1 (T * intrinsicReplicaActionResolution energy n)⁻¹)) /
        (Real.sqrt (1 - 4 * epsilon ^ 2) ^ (2 * n)) :=
      (le_div_iff₀ hpow).2 (by simpa [mul_comm] using hmain)
    _ = _ := by rw [div_eq_mul_inv]; ring

/-- Exact padded-word entropy in the Gaussian full-Choi shortcut law. -/
theorem gaussian_adaptiveStaticChoiPaddedCircuitShortcut_probability_le
    {d : ℕ} (hd : 0 < d)
    {gate : Type*} [Fintype gate] {energy : Fin d → ℝ}
    (s : ℕ)
    (target : PaddedCircuitWord gate s →
      EuclideanSpace ℂ (Fin d × Fin d))
    (htarget : ∀ w, ‖target w‖ = 1)
    (n : ℕ) (hn : 0 < n) {T epsilon : ℝ}
    (hT : 0 < T) (hepsilon : 0 ≤ epsilon)
    (hepsilonHalf : epsilon < 1 / 2) :
    (gaussianReal 0 1).real
          (⋃ w : PaddedCircuitWord gate s,
            gaussianStaticChoiTargetCaptureSet
              energy (target w) T epsilon) ≤
      (Fintype.card gate : ℝ) ^ (s + 1) *
        (Real.sqrt (1 - 4 * epsilon ^ 2) ^ (2 * n))⁻¹ *
        (fidelityReplicaCollisionMass
            (microcanonicalWeight (Fin d)) energy n +
          Real.exp
            (-((T * intrinsicReplicaActionResolution energy n) ^ 2) / 2)) := by
  simpa only [card_paddedCircuitWord, Nat.cast_pow] using
    gaussian_adaptiveStaticChoiTargetShortcut_probability_le
      hd target htarget n hn hT hepsilon hepsilonHalf

/-- Exact padded-word entropy in the uniform full-Choi shortcut law. -/
theorem uniform_adaptiveStaticChoiPaddedCircuitShortcut_probability_le
    {d : ℕ} (hd : 0 < d)
    {gate : Type*} [Fintype gate] {energy : Fin d → ℝ}
    (s : ℕ)
    (target : PaddedCircuitWord gate s →
      EuclideanSpace ℂ (Fin d × Fin d))
    (htarget : ∀ w, ‖target w‖ = 1)
    (n : ℕ) (hn : 0 < n) {T epsilon : ℝ}
    (hT : 0 < T) (hepsilon : 0 ≤ epsilon)
    (hepsilonHalf : epsilon < 1 / 2) :
    volume.real
          (⋃ w : PaddedCircuitWord gate s,
            uniformStaticChoiTargetCaptureSet
              energy (target w) T epsilon) / (2 * T) ≤
      (Fintype.card gate : ℝ) ^ (s + 1) *
        (Real.sqrt (1 - 4 * epsilon ^ 2) ^ (2 * n))⁻¹ *
        (fidelityReplicaCollisionMass
            (microcanonicalWeight (Fin d)) energy n +
          min 1 (T * intrinsicReplicaActionResolution energy n)⁻¹) := by
  simpa only [card_paddedCircuitWord, Nat.cast_pow] using
    uniform_adaptiveStaticChoiTargetShortcut_probability_le
      hd target htarget n hn hT hepsilon hepsilonHalf

/-- Under maximal projective rank, Gaussian collision mass is exactly the
replica permutation floor. -/
theorem gaussian_adaptiveStaticChoiPaddedCircuitShortcut_probability_le_floor
    {d : ℕ} (hd : 0 < d)
    {gate : Type*} [Fintype gate] {energy : Fin d → ℝ}
    (hmax : MaximallyProjectiveEnergy energy)
    (s : ℕ)
    (target : PaddedCircuitWord gate s →
      EuclideanSpace ℂ (Fin d × Fin d))
    (htarget : ∀ w, ‖target w‖ = 1)
    (n : ℕ) (hn : 0 < n) {T epsilon : ℝ}
    (hT : 0 < T) (hepsilon : 0 ≤ epsilon)
    (hepsilonHalf : epsilon < 1 / 2) :
    (gaussianReal 0 1).real
          (⋃ w : PaddedCircuitWord gate s,
            gaussianStaticChoiTargetCaptureSet
              energy (target w) T epsilon) ≤
      (Fintype.card gate : ℝ) ^ (s + 1) *
        (Real.sqrt (1 - 4 * epsilon ^ 2) ^ (2 * n))⁻¹ *
        (fidelityReplicaPermutationFloor
            (microcanonicalWeight (Fin d)) n +
          Real.exp
            (-((T * intrinsicReplicaActionResolution energy n) ^ 2) / 2)) := by
  letI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  rw [← (all_fidelityReplicaCollisionMass_eq_floor_iff
    (microcanonicalWeight_pos (Fin d)) energy).2 hmax n]
  exact gaussian_adaptiveStaticChoiPaddedCircuitShortcut_probability_le
    hd s target htarget n hn hT hepsilon hepsilonHalf

/-- Maximal-projective uniform-window full-Choi shortcut counterpart. -/
theorem uniform_adaptiveStaticChoiPaddedCircuitShortcut_probability_le_floor
    {d : ℕ} (hd : 0 < d)
    {gate : Type*} [Fintype gate] {energy : Fin d → ℝ}
    (hmax : MaximallyProjectiveEnergy energy)
    (s : ℕ)
    (target : PaddedCircuitWord gate s →
      EuclideanSpace ℂ (Fin d × Fin d))
    (htarget : ∀ w, ‖target w‖ = 1)
    (n : ℕ) (hn : 0 < n) {T epsilon : ℝ}
    (hT : 0 < T) (hepsilon : 0 ≤ epsilon)
    (hepsilonHalf : epsilon < 1 / 2) :
    volume.real
          (⋃ w : PaddedCircuitWord gate s,
            uniformStaticChoiTargetCaptureSet
              energy (target w) T epsilon) / (2 * T) ≤
      (Fintype.card gate : ℝ) ^ (s + 1) *
        (Real.sqrt (1 - 4 * epsilon ^ 2) ^ (2 * n))⁻¹ *
        (fidelityReplicaPermutationFloor
            (microcanonicalWeight (Fin d)) n +
          min 1 (T * intrinsicReplicaActionResolution energy n)⁻¹) := by
  letI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  rw [← (all_fidelityReplicaCollisionMass_eq_floor_iff
    (microcanonicalWeight_pos (Fin d)) energy).2 hmax n]
  exact uniform_adaptiveStaticChoiPaddedCircuitShortcut_probability_le
    hd s target htarget n hn hT hepsilon hepsilonHalf

end RHTower
