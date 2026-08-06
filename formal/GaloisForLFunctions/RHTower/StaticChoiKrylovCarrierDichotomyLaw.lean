import GaloisForLFunctions.RHTower.DirectAdaptiveStaticChoiShortcutActionLaw
import GaloisForLFunctions.HTGeometry.KrylovCarrierProjectionLaw

open scoped BigOperators ComplexConjugate

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry

def directStaticChoiTargetDiagonal
    {d : ℕ} (target : EuclideanSpace ℂ (Fin d × Fin d)) :
    EuclideanSpace ℂ (Fin d) :=
  WithLp.toLp 2 fun i => target (i, i)

theorem norm_directStaticChoiTargetDiagonal_le
    {d : ℕ} (target : EuclideanSpace ℂ (Fin d × Fin d)) :
    ‖directStaticChoiTargetDiagonal target‖ ≤ ‖target‖ := by
  have hdiag : (∑ i : Fin d, ‖target (i, i)‖ ^ 2) ≤
      ∑ ij : Fin d × Fin d, ‖target ij‖ ^ 2 := by
    let diag : Fin d → Fin d × Fin d := fun i => (i, i)
    have hinj : Function.Injective diag := by
      intro i j h
      exact congrArg Prod.fst h
    calc
      ∑ i : Fin d, ‖target (i, i)‖ ^ 2 =
          ∑ i : Fin d, ‖target (diag i)‖ ^ 2 := rfl
      _ = ∑ ij ∈ Finset.univ.image diag, ‖target ij‖ ^ 2 := by
        rw [Finset.sum_image]
        exact hinj.injOn
      _ ≤ ∑ ij : Fin d × Fin d, ‖target ij‖ ^ 2 :=
        Finset.sum_le_univ_sum_of_nonneg fun _ => sq_nonneg _
  have hsq : ‖directStaticChoiTargetDiagonal target‖ ^ 2 ≤ ‖target‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    simpa [directStaticChoiTargetDiagonal] using hdiag
  nlinarith [norm_nonneg (directStaticChoiTargetDiagonal target), norm_nonneg target]

theorem normalizedSpectralAmplitude_directStaticChoiTargetDiagonal
    {d : ℕ} (t : ℝ) (energy : Fin d → ℝ)
    (target : EuclideanSpace ℂ (Fin d × Fin d)) :
    normalizedSpectralAmplitude (directStaticChoiTargetDiagonal target)
        (fun i => -energy i) t =
      inner ℂ (staticSpectralChoiVector d t energy) target := by
  rw [inner_staticSpectralChoiVector_target_eq_directTwistedAmplitude]
  unfold normalizedSpectralAmplitude finiteRealTimeComplexAmplitude
  unfold twistedFiniteSpectralAmplitude
  apply Finset.sum_congr rfl
  intro i hi
  rw [directStaticChoiTargetWeight_mul_twist]
  unfold normalizedSpectralCoefficient directStaticChoiTargetDiagonal
  congr 1
  push_cast
  ring_nf

def directStaticChoiKrylovCarrierLoad
    {d : ℕ} {W : Type*} [Fintype W]
    (target : W → EuclideanSpace ℂ (Fin d × Fin d))
    (energy : Fin d → ℝ) (K : ℕ) : ℝ :=
  finiteKrylovCarrierLoad
    (fun w => directStaticChoiTargetDiagonal (target w))
    (fun i => -energy i) K

theorem staticChoiTargetCapture_implies_krylovCarrier
    {d : ℕ} (hd : 0 < d) {energy : Fin d → ℝ}
    {target : EuclideanSpace ℂ (Fin d × Fin d)}
    (htarget : ‖target‖ = 1) {K : ℕ} {T B epsilon t : ℝ}
    (htBound : |t| ≤ T) (hB : 0 ≤ B) (henergy : ∀ i, ‖energy i‖ ≤ B)
    (hepsilon : 0 ≤ epsilon) (hepsilonOne : epsilon ≤ 1)
    (ht : t ∈ staticChoiTargetCaptureSet energy target epsilon) :
    Real.sqrt (1 - epsilon ^ 2) -
        B ^ (K + 1) * |t| ^ (K + 1) / (K + 1).factorial ≤
      ‖spectralKrylovCarrier (fun i => -energy i) K
        (directStaticChoiTargetDiagonal target)‖ := by
  have hdiag : ‖directStaticChoiTargetDiagonal target‖ ≤ 1 := by
    calc
      ‖directStaticChoiTargetDiagonal target‖ ≤ ‖target‖ :=
        norm_directStaticChoiTargetDiagonal_le target
      _ = 1 := htarget
  have hfreq : ∀ i, ‖-energy i‖ ≤ B := by
    intro i
    simpa using henergy i
  have hlarge := staticChoiTargetCapture_implies_directCoherence
    hd htarget hepsilon hepsilonOne ht
  rw [← inner_staticSpectralChoiVector_target_eq_directTwistedAmplitude,
    ← normalizedSpectralAmplitude_directStaticChoiTargetDiagonal] at hlarge
  exact krylovCarrier_norm_ge_of_large_normalizedSpectralAmplitude
    (K := K) hd hdiag htBound hB hfreq hlarge

theorem no_staticChoiTargetCapture_of_krylovCarrierLoad
    {d : ℕ} (hd : 0 < d) {W : Type*} [Fintype W]
    {target : W → EuclideanSpace ℂ (Fin d × Fin d)}
    (htarget : ∀ w, ‖target w‖ = 1)
    {energy : Fin d → ℝ} {K : ℕ} {T B epsilon : ℝ}
    (hB : 0 ≤ B) (henergy : ∀ i, ‖energy i‖ ≤ B)
    (hepsilon : 0 ≤ epsilon) (hepsilonOne : epsilon ≤ 1)
    (hbudget : Real.sqrt (directStaticChoiKrylovCarrierLoad target energy K) +
        B ^ (K + 1) * T ^ (K + 1) / (K + 1).factorial <
          Real.sqrt (1 - epsilon ^ 2)) :
    ∀ t, |t| ≤ T → ∀ w,
      t ∉ staticChoiTargetCaptureSet energy (target w) epsilon := by
  intro t ht w hcapture
  have hdiag : ∀ v,
      ‖directStaticChoiTargetDiagonal (target v)‖ ≤ 1 := by
    intro v
    exact (norm_directStaticChoiTargetDiagonal_le (target v)).trans_eq (htarget v)
  have hnone := no_large_adaptive_amplitude_of_finiteKrylovLoad
    (K := K) hd hdiag hB (fun i => by simpa using henergy i)
    (show Real.sqrt (finiteKrylovCarrierLoad
        (fun v => directStaticChoiTargetDiagonal (target v))
        (fun i => -energy i) K) +
          B ^ (K + 1) * T ^ (K + 1) / (K + 1).factorial <
            Real.sqrt (1 - epsilon ^ 2) by simpa [directStaticChoiKrylovCarrierLoad] using hbudget)
      t ht w
  rw [normalizedSpectralAmplitude_directStaticChoiTargetDiagonal] at hnone
  have hlarge := staticChoiTargetCapture_implies_directCoherence
    hd (htarget w) hepsilon hepsilonOne hcapture
  rw [← inner_staticSpectralChoiVector_target_eq_directTwistedAmplitude] at hlarge
  exact (not_lt_of_ge hlarge) hnone

def directStaticChoiKrylovCarrierReplicaLoad
    {d : ℕ} {W : Type*} [Fintype W]
    (target : W → EuclideanSpace ℂ (Fin d × Fin d))
    (energy : Fin d → ℝ) (K r : ℕ) : ℝ :=
  finiteKrylovCarrierReplicaLoad
    (fun w => directStaticChoiTargetDiagonal (target w))
    (fun i => -energy i) K r

theorem no_staticChoiTargetCapture_of_krylovCarrierReplicaLoad
    {d : ℕ} (hd : 0 < d) {W : Type*} [Fintype W]
    {target : W → EuclideanSpace ℂ (Fin d × Fin d)}
    (htarget : ∀ w, ‖target w‖ = 1)
    {energy : Fin d → ℝ} {K r : ℕ} {T B epsilon : ℝ}
    (hB : 0 ≤ B) (henergy : ∀ i, ‖energy i‖ ≤ B)
    (hepsilon : 0 ≤ epsilon) (hepsilonOne : epsilon ≤ 1)
    (hthreshold : 0 ≤ Real.sqrt (1 - epsilon ^ 2) -
      B ^ (K + 1) * T ^ (K + 1) / (K + 1).factorial)
    (hbudget : directStaticChoiKrylovCarrierReplicaLoad target energy K r <
      (Real.sqrt (1 - epsilon ^ 2) -
        B ^ (K + 1) * T ^ (K + 1) / (K + 1).factorial) ^ (2 * r)) :
    ∀ t, |t| ≤ T → ∀ w,
      t ∉ staticChoiTargetCaptureSet energy (target w) epsilon := by
  have hdiag : ∀ v,
      ‖directStaticChoiTargetDiagonal (target v)‖ ≤ 1 := by
    intro v
    exact (norm_directStaticChoiTargetDiagonal_le (target v)).trans_eq (htarget v)
  have hnone := no_large_adaptive_amplitude_of_finiteKrylovReplicaLoad
    (K := K) (r := r) hd hdiag hB (fun i => by simpa using henergy i)
    hthreshold
    (show finiteKrylovCarrierReplicaLoad
        (fun v => directStaticChoiTargetDiagonal (target v))
        (fun i => -energy i) K r <
          (Real.sqrt (1 - epsilon ^ 2) -
            B ^ (K + 1) * T ^ (K + 1) / (K + 1).factorial) ^ (2 * r) by
      simpa [directStaticChoiKrylovCarrierReplicaLoad] using hbudget)
  intro t ht w hcapture
  have hsmall := hnone t ht w
  rw [normalizedSpectralAmplitude_directStaticChoiTargetDiagonal] at hsmall
  have hlarge := staticChoiTargetCapture_implies_directCoherence
    hd (htarget w) hepsilon hepsilonOne hcapture
  rw [← inner_staticSpectralChoiVector_target_eq_directTwistedAmplitude] at hlarge
  exact (not_lt_of_ge hlarge) hsmall

end RHTower
