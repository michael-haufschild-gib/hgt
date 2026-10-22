import GaloisForLFunctions.RHTower.ScalarRecurrenceTracelessCircuitSplit
import GaloisForLFunctions.RHTower.StaticChoiKrylovCarrierDichotomyLaw

/-!
# Krylov replica dichotomy after removing the scalar Choi return

For a finite static Hamiltonian with spectrum `energy : Fin d → ℝ`, let `χ(t)` be the normalized
Choi state of its evolution at time `t`, written in the spectral basis. A unit Choi target splits
orthogonally into its component along the identity Choi state `χ(0)` and a traceless residual. The
module bounds the residual and its diagonal by one, defines the scalar-removed Krylov replica load
`∑_w ‖Krylov_K(diag(residual_w))‖^(2r)` of a finite family of targets, and proves a dichotomy: if
some target is captured at time `t` (trace distance at most `ε` from `χ(t)`) while the scalar
return `|⟨χ(t), χ(0)⟩|` is below `ρ`, the replica load is at least
`(√(1 - ε²) - ρ - B^(K+1) |t|^(K+1) / (K+1)!)^(2r)`; so a load below that threshold excludes capture
off the scalar return.

## Main results

- `norm_staticChoiTracelessResidual_le_one`, `norm_staticChoiTracelessDiagonal_le_one`: the
  traceless residual of a unit target and its diagonal have norm at most one.
- `scalarRemovedKrylovReplicaLoad_ge_of_capture`: capture at time `t` off the scalar return forces
  the lower bound on the scalar-removed replica load.
- `no_staticChoiTargetCapture_off_scalarReturn_of_krylovReplicaLoad`: if the replica load is below
  the threshold computed with `T ≥ |t|`, no target is captured at time `t`.

## Hypotheses

All results are unconditional finite-dimensional statements. They assume `0 < d`, unit-norm
targets, `|t| ≤ T`, a spectral bound `|energy i| ≤ B` with `B ≥ 0`, `0 ≤ ε ≤ 1`, a scalar-return
bound `|⟨χ(t), χ(0)⟩| < ρ`, nonnegativity of the threshold, and, for the exclusion statement, the
load budget inequality.
-/

open scoped BigOperators ComplexConjugate

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry

/-- For `d > 0` and a unit Choi target, the traceless residual (the target minus its component along
the identity Choi state) has norm at most one, by Pythagoras. -/
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

/-- Diagonal `(r(i, i))_i` of the traceless residual of a Choi target. -/
def staticChoiTracelessDiagonal
    {d : ℕ} (energy : Fin d → ℝ)
    (target : EuclideanSpace ℂ (Fin d × Fin d)) :
    EuclideanSpace ℂ (Fin d) :=
  directStaticChoiTargetDiagonal (staticChoiTracelessResidual energy target)

/-- For `d > 0` and a unit Choi target, the diagonal of the traceless residual has norm at most one. -/
theorem norm_staticChoiTracelessDiagonal_le_one
    {d : ℕ} (hd : 0 < d) (energy : Fin d → ℝ)
    {target : EuclideanSpace ℂ (Fin d × Fin d)}
    (htarget : ‖target‖ = 1) :
    ‖staticChoiTracelessDiagonal energy target‖ ≤ 1 :=
  (norm_directStaticChoiTargetDiagonal_le
    (staticChoiTracelessResidual energy target)).trans
      (norm_staticChoiTracelessResidual_le_one hd energy htarget)

/-- Scalar-removed Krylov replica load: `∑_w ‖Krylov_K(diag residual_w)‖^(2r)` with frequencies
`-energy`, summed over a finite family of Choi targets. -/
def scalarRemovedStaticChoiKrylovReplicaLoad
    {d : ℕ} {W : Type*} [Fintype W]
    (target : W → EuclideanSpace ℂ (Fin d × Fin d))
    (energy : Fin d → ℝ) (K r : ℕ) : ℝ :=
  finiteKrylovCarrierReplicaLoad
    (fun w => staticChoiTracelessDiagonal energy (target w))
    (fun i => -energy i) K r

/-- Assuming unit targets, `|t| ≤ T`, `|energy i| ≤ B`, `0 ≤ ε ≤ 1`, scalar return
`|⟨χ(t), χ(0)⟩| < ρ`, and capture of target `w` at time `t` within trace distance `ε`, the
scalar-removed replica load is at least `(√(1 - ε²) - ρ - B^(K+1) |t|^(K+1) / (K+1)!)^(2r)`. -/
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
    (hthreshold : 0 ≤ Real.sqrt (1 - epsilon ^ (2 : ℕ)) - rho -
      B ^ (K + 1) * |t| ^ (K + 1) / (K + 1).factorial) :
    (Real.sqrt (1 - epsilon ^ (2 : ℕ)) - rho -
      B ^ (K + 1) * |t| ^ (K + 1) / (K + 1).factorial) ^ (2 * r) ≤
        scalarRemovedStaticChoiKrylovReplicaLoad target energy K r := by
  have htotal := staticChoiTargetCapture_implies_directCoherence
    hd (htarget w) hepsilon hepsilonOne hcapture
  rw [← inner_staticSpectralChoiVector_target_eq_directTwistedAmplitude] at htotal
  have hsplit := staticChoiTarget_capture_scalar_or_traceless_budget
    hd t energy (htarget w) (theta := Real.sqrt (1 - epsilon ^ (2 : ℕ)))
      (eta := rho) htotal
  have hresidual : Real.sqrt (1 - epsilon ^ (2 : ℕ)) - rho ≤
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

/-- Assuming the same bounds and that the replica load is below
`(√(1 - ε²) - ρ - B^(K+1) T^(K+1) / (K+1)!)^(2r)`, no target is captured within `ε` at any time `t`
with `|t| ≤ T` whose scalar return is below `ρ`. -/
theorem no_staticChoiTargetCapture_off_scalarReturn_of_krylovReplicaLoad
    {d : ℕ} (hd : 0 < d) {W : Type*} [Fintype W]
    {target : W → EuclideanSpace ℂ (Fin d × Fin d)}
    (htarget : ∀ w, ‖target w‖ = 1)
    {energy : Fin d → ℝ} {K r : ℕ} {T B epsilon rho t : ℝ}
    (htBound : |t| ≤ T) (hB : 0 ≤ B) (henergy : ∀ i, ‖energy i‖ ≤ B)
    (hepsilon : 0 ≤ epsilon) (hepsilonOne : epsilon ≤ 1)
    (hreturn : ‖inner ℂ (staticSpectralChoiVector d t energy)
      (staticSpectralChoiVector d 0 energy)‖ < rho)
    (hthreshold : 0 ≤ Real.sqrt (1 - epsilon ^ (2 : ℕ)) - rho -
      B ^ (K + 1) * T ^ (K + 1) / (K + 1).factorial)
    (hbudget : scalarRemovedStaticChoiKrylovReplicaLoad target energy K r <
      (Real.sqrt (1 - epsilon ^ (2 : ℕ)) - rho -
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
  have hpointThreshold : 0 ≤ Real.sqrt (1 - epsilon ^ (2 : ℕ)) - rho -
      B ^ (K + 1) * |t| ^ (K + 1) / (K + 1).factorial := by
    linarith
  have hlower := scalarRemovedKrylovReplicaLoad_ge_of_capture
    (K := K) (r := r) hd htarget htBound hB henergy hepsilon hepsilonOne
      hreturn hcapture hpointThreshold
  have hbase : Real.sqrt (1 - epsilon ^ (2 : ℕ)) - rho -
      B ^ (K + 1) * T ^ (K + 1) / (K + 1).factorial ≤
        Real.sqrt (1 - epsilon ^ (2 : ℕ)) - rho -
          B ^ (K + 1) * |t| ^ (K + 1) / (K + 1).factorial := by
    linarith
  have hpower := pow_le_pow_left₀ hthreshold hbase (2 * r)
  exact (not_lt_of_ge (hpower.trans hlower)) hbudget

end RHTower
