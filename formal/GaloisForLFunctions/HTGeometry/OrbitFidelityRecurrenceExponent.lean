/-
# The fidelity recurrence exponent of a physical orbit

The return amplitude of a state under a Hermitian evolution is the weighted sum of the spectral
phases with weights the squared eigenbasis overlaps, which sum to one by Parseval and are strictly
positive exactly when the state is cyclic.  So the first fidelity return of the orbit is the first
fidelity return of that weighted spectral packet, and the abstract exponent law applies.

Main results:
* `finiteComplexInner_unitaryEvolution_eq_sum` — the return amplitude is the weighted phase sum.
* `orbitFidelityReturnTime`, `orbitFidelityReturnTime_eq` — the physical first return.
* `tendsto_log_orbitFidelityReturnTime` — **the fidelity recurrence exponent of a cyclic orbit**.
-/
import GaloisForLFunctions.HTGeometry.FidelityReturnExponent
import GaloisForLFunctions.HTGeometry.CircuitDictionaryCounting
import GaloisForLFunctions.HTGeometry.EvolvedStateBundlePairing
import GaloisForLFunctions.HTGeometry.SpectralOrbitWindowBridge

open Matrix
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

noncomputable section

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- **The return amplitude is the weighted spectral phase sum.** -/
theorem finiteComplexInner_unitaryEvolution_eq_sum {H : Matrix α α ℂ} {e : α → α → ℂ}
    {lam : α → ℝ} (heb : IsOrthoEigenBasis H e lam) (Ω : α → ℂ) (t : ℝ) :
    finiteComplexInner Ω (unitaryEvolution H t *ᵥ Ω)
      = ∑ j, ((spectralWeights e Ω j : ℝ) : ℂ)
          * Complex.exp (((-(t * lam j) : ℝ) : ℂ) * Complex.I) := by
  rw [unitaryEvolution_mulVec_eq_sum heb Ω t]
  have hlin : finiteComplexInner Ω
      (∑ j, (finiteComplexInner (e j) Ω * Complex.exp (-(Complex.I * (t * lam j)))) • e j)
      = ∑ j, (finiteComplexInner (e j) Ω * Complex.exp (-(Complex.I * (t * lam j))))
          * finiteComplexInner Ω (e j) := by
    rw [finiteComplexInner]
    have hval : ∀ x : α,
        (∑ j, (finiteComplexInner (e j) Ω * Complex.exp (-(Complex.I * (t * lam j)))) • e j) x
          = ∑ j, (finiteComplexInner (e j) Ω * Complex.exp (-(Complex.I * (t * lam j)))) * e j x := by
      intro x
      simp [Finset.sum_apply]
    calc ∑ x, (starRingEnd ℂ) (Ω x)
          * (∑ j, (finiteComplexInner (e j) Ω * Complex.exp (-(Complex.I * (t * lam j)))) • e j) x
        = ∑ x, ∑ j, (finiteComplexInner (e j) Ω
            * Complex.exp (-(Complex.I * (t * lam j)))) * ((starRingEnd ℂ) (Ω x) * e j x) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [hval x, Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
      _ = ∑ j, (finiteComplexInner (e j) Ω * Complex.exp (-(Complex.I * (t * lam j))))
            * finiteComplexInner Ω (e j) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [show finiteComplexInner Ω (e j) = ∑ x, (starRingEnd ℂ) (Ω x) * e j x from rfl,
            Finset.mul_sum]
  rw [hlin]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hconj : finiteComplexInner Ω (e j) = (starRingEnd ℂ) (finiteComplexInner (e j) Ω) := by
    rw [finiteComplexInner, finiteComplexInner, map_sum]
    exact Finset.sum_congr rfl fun x _ => by rw [map_mul, Complex.conj_conj, mul_comm]
  have hw : ((spectralWeights e Ω j : ℝ) : ℂ)
      = finiteComplexInner (e j) Ω * (starRingEnd ℂ) (finiteComplexInner (e j) Ω) := by
    rw [spectralWeights, Complex.sq_norm, Complex.normSq_eq_conj_mul_self]
    ring
  have hphase : Complex.exp (-(Complex.I * ((t : ℂ) * ((lam j : ℝ) : ℂ))))
      = Complex.exp (((-(t * lam j) : ℝ) : ℂ) * Complex.I) := by
    congr 1
    push_cast
    ring
  rw [hconj, hw, ← hphase]
  ring

/-- **The fidelity deficit of the orbit is the spectral return deficit of the weights.** -/
theorem spectralReturnDeficit_eq_orbit_deficit {D : ℕ} (ρ : α ≃ Fin D)
    {H : Matrix α α ℂ} {e : α → α → ℂ} {lam : α → ℝ} (heb : IsOrthoEigenBasis H e lam)
    (Ω : α → ℂ) (t : ℝ) :
    spectralReturnDeficit (fun i => lam (ρ.symm i)) (fun i => spectralWeights e Ω (ρ.symm i)) t
      = 1 - ‖finiteComplexInner Ω (unitaryEvolution H t *ᵥ Ω)‖ ^ (2 : ℕ) := by
  rw [spectralReturnDeficit, spectralReturnAmplitude,
    finiteComplexInner_unitaryEvolution_eq_sum heb Ω t]
  congr 3
  exact Equiv.sum_comp ρ.symm fun j => ((spectralWeights e Ω j : ℝ) : ℂ)
    * Complex.exp (((-(t * lam j) : ℝ) : ℂ) * Complex.I)

/-! ## The physical first fidelity return -/

/-- The first fidelity return of an orbit after a positive cutoff. -/
def orbitFidelityReturnTime (H : Matrix α α ℂ) (Ω : α → ℂ) (t₀ δ : ℝ) : ℝ :=
  sInf {t : ℝ | t₀ ≤ t ∧ 1 - ‖finiteComplexInner Ω (unitaryEvolution H t *ᵥ Ω)‖ ^ (2 : ℕ) < δ}

theorem orbitFidelityReturnTime_eq {D : ℕ} (ρ : α ≃ Fin D)
    {H : Matrix α α ℂ} {e : α → α → ℂ} {lam : α → ℝ} (heb : IsOrthoEigenBasis H e lam)
    (Ω : α → ℂ) (t₀ δ : ℝ) :
    orbitFidelityReturnTime H Ω t₀ δ
      = fidelityReturnTime (fun i => lam (ρ.symm i))
          (fun i => spectralWeights e Ω (ρ.symm i)) t₀ δ := by
  rw [orbitFidelityReturnTime, fidelityReturnTime, fidelityReturnSet]
  congr 1
  ext t
  rw [Set.mem_setOf_eq, Set.mem_setOf_eq, spectralReturnDeficit_eq_orbit_deficit ρ heb Ω t]

/-- **The fidelity recurrence exponent of a cyclic orbit.**  A simple spectrum whose projective gap
ratios are not very well approximable, together with a cyclic seed, gives the first fidelity return
after a positive cutoff logarithmic exponent exactly half the number of independent gap ratios. -/
theorem tendsto_log_orbitFidelityReturnTime {e' : ℕ} (ρ : α ≃ Fin (e' + 3))
    {H : Matrix α α ℂ} {e : α → α → ℂ} {lam : α → ℝ} (heb : IsOrthoEigenBasis H e lam)
    {Ω : α → ℂ} (hΩ : finiteComplexInner Ω Ω = 1)
    (hcyc : ∀ j, finiteComplexInner (e j) Ω ≠ 0)
    (hgap : lam (ρ.symm 0) < lam (ρ.symm 1))
    (hnv : ¬ KleinbockMargulis.VWA
      (anchoredGapRatioMap (fun i => lam (ρ.symm i)) 0 1 (fun m => m.succ.succ)))
    {t₀ : ℝ} (ht₀ : 0 < t₀) :
    Filter.Tendsto
      (fun δ : ℝ => Real.log (orbitFidelityReturnTime H Ω t₀ δ) / Real.log (1 / δ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (((e' + 1 : ℕ) : ℝ) / 2)) := by
  classical
  set E : Fin (e' + 3) → ℝ := fun i => lam (ρ.symm i) with hEdef
  set p : Fin (e' + 3) → ℝ := fun i => spectralWeights e Ω (ρ.symm i) with hpdef
  have hp1 : ∑ i, p i = 1 := by
    rw [hpdef]
    rw [Equiv.sum_comp ρ.symm (spectralWeights e Ω)]
    exact sum_spectralWeights heb hΩ
  have hppos : ∀ i, 0 < p i := by
    intro i
    have hne := hcyc (ρ.symm i)
    show 0 < spectralWeights e Ω (ρ.symm i)
    rw [spectralWeights]
    have : 0 < ‖finiteComplexInner (e (ρ.symm i)) Ω‖ := norm_pos_iff.mpr hne
    positivity
  set c : ℝ := Finset.univ.inf' Finset.univ_nonempty p with hcdef
  have hcpos : 0 < c := by
    rw [hcdef, Finset.lt_inf'_iff]
    exact fun i _ => hppos i
  have hcp : ∀ i, c ≤ p i := fun i => Finset.inf'_le p (Finset.mem_univ i)
  have hg0 : 0 < E 1 - E 0 := by
    rw [hEdef]
    simp only
    linarith [hgap]
  have hmain := tendsto_log_fidelityReturnTime E p hp1 hppos hcpos hcp hg0 hnv ht₀
  refine hmain.congr' ?_
  filter_upwards with δ
  rw [orbitFidelityReturnTime_eq ρ heb Ω t₀ δ]

end

end GaloisForLFunctions.HTGeometry
