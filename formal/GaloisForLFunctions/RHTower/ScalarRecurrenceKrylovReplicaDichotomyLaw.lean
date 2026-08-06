import GaloisForLFunctions.RHTower.ScalarRecurrenceTracelessCircuitSplit
import GaloisForLFunctions.RHTower.StaticChoiKrylovCarrierDichotomyLaw

open scoped BigOperators ComplexConjugate

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry

theorem norm_staticChoiTracelessResidual_le_one
    {d : ℕ} (hd : 0 < d) (energy : Fin d → ℝ)
    {target : EuclideanSpace ℂ (Fin d × Fin d)}
    (htarget : ‖target‖ = 1) :
    ‖staticChoiTracelessResidual energy target‖ ≤ 1 := by
  let v := staticSpectralChoiVector d 0 energy
  let a := staticChoiScalarComponent energy target
  let residual := staticChoiTracelessResidual energy target
  have horth : inner ℂ (a • v) residual = 0 := by
    rw [inner_smul_left]
    dsimp [v, residual]
    rw [inner_staticChoiTracelessResidual_zero hd]
    simp
  have hsplit : a • v + residual = target := by
    exact staticChoiTarget_eq_scalar_add_traceless energy target
  have hpy := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    (a • v) residual horth
  rw [hsplit, htarget] at hpy
  nlinarith [norm_nonneg residual, sq_nonneg ‖a • v‖]

def staticChoiTracelessDiagonal
    {d : ℕ} (energy : Fin d → ℝ)
    (target : EuclideanSpace ℂ (Fin d × Fin d)) :
    EuclideanSpace ℂ (Fin d) :=
  directStaticChoiTargetDiagonal (staticChoiTracelessResidual energy target)

theorem norm_staticChoiTracelessDiagonal_le_one
    {d : ℕ} (hd : 0 < d) (energy : Fin d → ℝ)
    {target : EuclideanSpace ℂ (Fin d × Fin d)}
    (htarget : ‖target‖ = 1) :
    ‖staticChoiTracelessDiagonal energy target‖ ≤ 1 :=
  (norm_directStaticChoiTargetDiagonal_le
    (staticChoiTracelessResidual energy target)).trans
      (norm_staticChoiTracelessResidual_le_one hd energy htarget)

def scalarRemovedStaticChoiKrylovReplicaLoad
    {d : ℕ} {W : Type*} [Fintype W]
    (target : W → EuclideanSpace ℂ (Fin d × Fin d))
    (energy : Fin d → ℝ) (K r : ℕ) : ℝ :=
  finiteKrylovCarrierReplicaLoad
    (fun w => staticChoiTracelessDiagonal energy (target w))
    (fun i => -energy i) K r

theorem scalarRemovedKrylovReplicaLoad_ge_of_capture
    {d : ℕ} (hd : 0 < d) {W : Type*} [Fintype W]
    {target : W → EuclideanSpace ℂ (Fin d × Fin d)}
    (htarget : ∀ w, ‖target w‖ = 1)
    {energy : Fin d → ℝ} {K r : ℕ} {T B epsilon rho t : ℝ}
    (htBound : |t| ≤ T) (hB : 0 ≤ B) (henergy : ∀ i, ‖energy i‖ ≤ B)
    (hepsilon : 0 ≤ epsilon) (hepsilonOne : epsilon ≤ 1)
    (hreturn : ‖inner ℂ (staticSpectralChoiVector d t energy)
      (staticSpectralChoiVector d 0 energy)‖ < rho)
    {w : W} (hcapture : t ∈ staticChoiTargetCaptureSet energy (target w) epsilon)
    (hthreshold : 0 ≤ Real.sqrt (1 - epsilon ^ 2) - rho -
      B ^ (K + 1) * |t| ^ (K + 1) / (K + 1).factorial) :
    (Real.sqrt (1 - epsilon ^ 2) - rho -
      B ^ (K + 1) * |t| ^ (K + 1) / (K + 1).factorial) ^ (2 * r) ≤
        scalarRemovedStaticChoiKrylovReplicaLoad target energy K r := by
  have htotal := staticChoiTargetCapture_implies_directCoherence
    hd (htarget w) hepsilon hepsilonOne hcapture
  rw [← inner_staticSpectralChoiVector_target_eq_directTwistedAmplitude] at htotal
  have hsplit := staticChoiTarget_capture_scalar_or_traceless_budget
    hd t energy (htarget w) (theta := Real.sqrt (1 - epsilon ^ 2))
      (eta := rho) htotal
  have hresidual : Real.sqrt (1 - epsilon ^ 2) - rho ≤
      ‖inner ℂ (staticSpectralChoiVector d t energy)
        (staticChoiTracelessResidual energy (target w))‖ := by
    rcases hsplit with hbad | hgood
    · exact False.elim ((not_le_of_gt hreturn) hbad)
    · exact hgood
  rw [← normalizedSpectralAmplitude_directStaticChoiTargetDiagonal] at hresidual
  exact finiteKrylovCarrierReplicaLoad_ge_of_large_amplitude
    (K := K) (r := r) hd
    (fun v => norm_staticChoiTracelessDiagonal_le_one hd energy (htarget v))
    htBound hB (fun i => by simpa using henergy i) hresidual hthreshold

theorem no_staticChoiTargetCapture_off_scalarReturn_of_krylovReplicaLoad
    {d : ℕ} (hd : 0 < d) {W : Type*} [Fintype W]
    {target : W → EuclideanSpace ℂ (Fin d × Fin d)}
    (htarget : ∀ w, ‖target w‖ = 1)
    {energy : Fin d → ℝ} {K r : ℕ} {T B epsilon rho t : ℝ}
    (htBound : |t| ≤ T) (hB : 0 ≤ B) (henergy : ∀ i, ‖energy i‖ ≤ B)
    (hepsilon : 0 ≤ epsilon) (hepsilonOne : epsilon ≤ 1)
    (hreturn : ‖inner ℂ (staticSpectralChoiVector d t energy)
      (staticSpectralChoiVector d 0 energy)‖ < rho)
    (hthreshold : 0 ≤ Real.sqrt (1 - epsilon ^ 2) - rho -
      B ^ (K + 1) * T ^ (K + 1) / (K + 1).factorial)
    (hbudget : scalarRemovedStaticChoiKrylovReplicaLoad target energy K r <
      (Real.sqrt (1 - epsilon ^ 2) - rho -
        B ^ (K + 1) * T ^ (K + 1) / (K + 1).factorial) ^ (2 * r)) :
    ∀ w, t ∉ staticChoiTargetCaptureSet energy (target w) epsilon := by
  intro w hcapture
  have hpow : |t| ^ (K + 1) ≤ T ^ (K + 1) :=
    pow_le_pow_left₀ (abs_nonneg t) htBound _
  have hcoef : 0 ≤ B ^ (K + 1) / (K + 1).factorial := by positivity
  have hrem :
      B ^ (K + 1) * |t| ^ (K + 1) / (K + 1).factorial ≤
        B ^ (K + 1) * T ^ (K + 1) / (K + 1).factorial := by
    calc
      B ^ (K + 1) * |t| ^ (K + 1) / (K + 1).factorial =
          (B ^ (K + 1) / (K + 1).factorial) * |t| ^ (K + 1) := by ring
      _ ≤ (B ^ (K + 1) / (K + 1).factorial) * T ^ (K + 1) :=
        mul_le_mul_of_nonneg_left hpow hcoef
      _ = _ := by ring
  have hpointThreshold : 0 ≤ Real.sqrt (1 - epsilon ^ 2) - rho -
      B ^ (K + 1) * |t| ^ (K + 1) / (K + 1).factorial := by
    linarith
  have hlower := scalarRemovedKrylovReplicaLoad_ge_of_capture
    (K := K) (r := r) hd htarget htBound hB henergy hepsilon hepsilonOne
      hreturn hcapture hpointThreshold
  have hbase : Real.sqrt (1 - epsilon ^ 2) - rho -
      B ^ (K + 1) * T ^ (K + 1) / (K + 1).factorial ≤
        Real.sqrt (1 - epsilon ^ 2) - rho -
          B ^ (K + 1) * |t| ^ (K + 1) / (K + 1).factorial := by
    linarith
  have hpower := pow_le_pow_left₀ hthreshold hbase (2 * r)
  exact (not_lt_of_ge (hpower.trans hlower)) hbudget

end RHTower
