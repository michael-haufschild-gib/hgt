import GaloisForLFunctions.HTGeometry.AllJetLevelSet
import GaloisForLFunctions.HTGeometry.TorusDerivationLeibniz

/-!
# The constants of the torus derivation

A phase observable killed by the torus derivation is constant.  All its higher
jets vanish, so the attached quasiperiodic function has the same Taylor series
at the origin as a constant; being holomorphic on the connected time strip it
*is* that constant there, hence along the whole real orbit, hence — the orbit
being dense in the torus and the torus a uniqueness set for the polyannulus —
on the whole polyannulus.

The field of constants of the torus derivation on a polyannulus is therefore
exactly `ℂ`, which is what rational independence of the frequencies buys.
-/

open Complex Set Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {d : Type} [Fintype d] [DecidableEq d]

theorem iteratedDeriv_const_succ (c : ℂ) (k : ℕ) :
    iteratedDeriv (k + 1) (fun _ : ℂ => c) = 0 := by
  induction k with
  | zero =>
      rw [iteratedDeriv_one]
      exact deriv_const' c
  | succ k ih =>
      rw [iteratedDeriv_succ, ih]
      exact deriv_const' 0

/-- All higher jets of a derivation-killed observable vanish. -/
theorem phaseJet_eq_zero_of_torusDerivation_eq_zero {ρ omega : d → ℝ}
    {F : (d → ℂ) → ℂ}
    (h : ∀ z ∈ polyannulus ρ, torusDerivation omega F z = 0) (k : ℕ) :
    ∀ z ∈ polyannulus ρ, phaseJet omega F (k + 1) z = 0 := by
  induction k with
  | zero => exact h
  | succ k ih =>
      intro z hz
      show (torusDerivation omega)^[k + 1 + 1] F z = 0
      rw [Function.iterate_succ_apply']
      have hcong := torusDerivation_congr (isOpen_polyannulus ρ) omega
        (F := (torusDerivation omega)^[k + 1] F) (G := fun _ => (0 : ℂ)) ih z hz
      rw [hcong, torusDerivation_const]

/-- **The constants of the torus derivation.**  For rationally independent
frequencies, a phase observable killed by the torus derivation is constant on
the polyannulus. -/
theorem eq_const_of_torusDerivation_eq_zero {ρ omega : d → ℝ}
    (hρ : ∀ j, 0 < ρ j) (hindep : RationallyIndependentFrequency omega)
    {F : (d → ℂ) → ℂ} (hF : AnalyticOnNhd ℂ F (polyannulus ρ))
    (h : ∀ z ∈ polyannulus ρ, torusDerivation omega F z = 0) :
    ∀ z ∈ polyannulus ρ, F z = F (fun _ => 1) := by
  have hone : (fun _ : d => (1 : ℂ)) ∈ polyannulus ρ := one_mem_polyannulus hρ
  have hjets : ∀ k, iteratedDeriv k (phaseFunction omega F) 0
      = iteratedDeriv k (fun _ : ℂ => F (fun _ : d => (1 : ℂ))) 0 := by
    intro k
    rw [iteratedDeriv_phaseFunction hF k 0 (zero_mem_phaseStrip hρ),
      phaseFunction, phasePoint_zero]
    cases k with
    | zero => rfl
    | succ k =>
        rw [iteratedDeriv_const_succ]
        exact phaseJet_eq_zero_of_torusDerivation_eq_zero h k _ hone
  have hstrip := eqOn_of_iteratedDeriv_eq (isPreconnected_phaseStrip ρ omega)
    (analyticOnNhd_phaseFunction (omega := omega) hF)
    (analyticOnNhd_const (E := ℂ) (F := ℂ)) (zero_mem_phaseStrip hρ) hjets
  have horbit : ∀ t : ℝ,
      F (torusOrbitPoint omega t) - F (fun _ : d => (1 : ℂ)) = 0 := by
    intro t
    have hval := hstrip (ofReal_mem_phaseStrip hρ t)
    rw [phaseFunction, phasePoint_ofReal] at hval
    rw [hval, sub_self]
  have hall := eqOn_zero_polyannulus_of_eqOn_zero_orbit hρ hindep
    (hF.sub (analyticOnNhd_const : AnalyticOnNhd ℂ
      (fun _ : d → ℂ => F (fun _ : d => (1 : ℂ))) (polyannulus ρ))) horbit
  intro z hz
  have hzz : F z - F (fun _ : d => (1 : ℂ)) = 0 := hall z hz
  linear_combination hzz

end

end GaloisForLFunctions.HTGeometry
