import GaloisForLFunctions.HTGeometry.WaveGreenIdentityIntegrable
import GaloisForLFunctions.HTGeometry.WaveEnergyFlux

/-!
# The flux identity without compact support

The cancellation behind the energy estimate is an integration by parts, and integration by parts
needs integrability, not compact support. This file states the flux identity in that generality: the
four families of integrability hypotheses below are exactly what the Green identity and the
splitting of the integral consume, and a decaying solution — the kind a Fourier synthesis produces —
satisfies them without vanishing outside any compact set.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

open scoped ContDiff

section FluxIntegrable

variable {d : ℕ} {u V : ℝ × (Fin d → ℝ) → ℝ}

/-- **The energy flux identity for integrable data.** -/
theorem integral_dirDeriv_energyDensity_of_integrable (hu : ContDiff ℝ ∞ u)
    (hsolve : SolvesWaveEq u V) (t : ℝ)
    (h1 : ∀ i : Fin d, Integrable
      (fun x : Fin d → ℝ => coordPartial i (coordPartial i (slice u t)) x
        * slice (waveDirDeriv (timeDir d) u) t x) (volume : Measure (Fin d → ℝ)))
    (h2 : ∀ i : Fin d, Integrable
      (fun x : Fin d → ℝ => coordPartial i (slice u t) x
        * coordPartial i (slice (waveDirDeriv (timeDir d) u) t) x)
      (volume : Measure (Fin d → ℝ)))
    (h3 : ∀ i : Fin d, Integrable
      (fun x : Fin d → ℝ => coordPartial i (slice u t) x
        * slice (waveDirDeriv (timeDir d) u) t x) (volume : Measure (Fin d → ℝ)))
    (h4 : Integrable
      (fun x : Fin d → ℝ => 2 * ((V (t, x) + 1) * (u (t, x) * waveDirDeriv (timeDir d) u (t, x))))
      (volume : Measure (Fin d → ℝ))) :
    (∫ x : Fin d → ℝ, waveDirDeriv (timeDir d) (energyDensity u) (t, x))
      = 2 * ∫ x : Fin d → ℝ,
          (V (t, x) + 1) * (u (t, x) * waveDirDeriv (timeDir d) u (t, x)) := by
  classical
  set f : (Fin d → ℝ) → ℝ := slice u t with hf
  set g : (Fin d → ℝ) → ℝ := slice (waveDirDeriv (timeDir d) u) t with hg
  have hfcd : ContDiff ℝ ∞ f := contDiff_slice hu t
  have hgcd : ContDiff ℝ ∞ g := contDiff_slice (contDiff_dirDeriv hu _) t
  -- the pointwise expansion, exactly as in the compactly supported case
  have hpt : ∀ x : Fin d → ℝ, waveDirDeriv (timeDir d) (energyDensity u) (t, x)
      = 2 * (g x * ∑ i : Fin d, coordPartial i (coordPartial i f) x)
        + (∑ i : Fin d, 2 * (coordPartial i f x * coordPartial i g x))
        + 2 * ((V (t, x) + 1) * (f x * g x)) := by
    intro x
    have hexp := waveDirDeriv_energyDensity hu (t, x)
    have heq := hsolve (t, x)
    have hgeta : (fun y : Fin d → ℝ => waveDirDeriv (timeDir d) u (t, y)) = g := rfl
    have hfeta : (fun y : Fin d → ℝ => u (t, y)) = f := rfl
    have hspeta : ∀ i : Fin d, (fun y : Fin d → ℝ => waveDirDeriv (spaceDir d i) u (t, y))
        = coordPartial i f := by
      intro i
      funext y
      exact waveDirDeriv_spaceDir_eq hu i t y
    have hlap : ∀ i : Fin d, waveDirDeriv (spaceDir d i) (waveDirDeriv (spaceDir d i) u) (t, x)
        = coordPartial i (coordPartial i f) x := by
      intro i
      rw [waveDirDeriv_spaceDir_eq (contDiff_dirDeriv hu _) i t x, hspeta i]
    have hmix : ∀ i : Fin d, waveDirDeriv (timeDir d) (waveDirDeriv (spaceDir d i) u) (t, x)
        = coordPartial i g x := by
      intro i
      rw [waveDirDeriv_comm hu, waveDirDeriv_spaceDir_eq (contDiff_dirDeriv hu _) i t x, hgeta]
    have hsp : ∀ i : Fin d, waveDirDeriv (spaceDir d i) u (t, x) = coordPartial i f x := by
      intro i
      rw [waveDirDeriv_spaceDir_eq hu i t x, hfeta]
    have hsum : (∑ i : Fin d, 2 * (waveDirDeriv (spaceDir d i) u (t, x)
          * waveDirDeriv (timeDir d) (waveDirDeriv (spaceDir d i) u) (t, x)))
        = ∑ i : Fin d, 2 * (coordPartial i f x * coordPartial i g x) :=
      Finset.sum_congr rfl fun i _ => by rw [hsp i, hmix i]
    have hlapsum : (∑ i : Fin d, waveDirDeriv (spaceDir d i)
          (waveDirDeriv (spaceDir d i) u) (t, x))
        = ∑ i : Fin d, coordPartial i (coordPartial i f) x :=
      Finset.sum_congr rfl fun i _ => hlap i
    have hg' : waveDirDeriv (timeDir d) u (t, x) = g x := rfl
    have hf' : u (t, x) = f x := rfl
    rw [hexp, heq, hlapsum, hsum, hg', hf']
    ring
  -- the three pieces are integrable
  have hint1 : Integrable (fun x : Fin d → ℝ =>
      2 * (g x * ∑ i : Fin d, coordPartial i (coordPartial i f) x))
      (volume : Measure (Fin d → ℝ)) := by
    have hsumint : Integrable (fun x : Fin d → ℝ =>
        ∑ i : Fin d, coordPartial i (coordPartial i f) x * g x)
        (volume : Measure (Fin d → ℝ)) := integrable_finsetSum _ fun i _ => h1 i
    refine (hsumint.const_mul 2).congr (Filter.Eventually.of_forall fun x => ?_)
    show 2 * ∑ i : Fin d, coordPartial i (coordPartial i f) x * g x
      = 2 * (g x * ∑ i : Fin d, coordPartial i (coordPartial i f) x)
    rw [← Finset.sum_mul, mul_comm (∑ i : Fin d, coordPartial i (coordPartial i f) x) (g x)]
  have hint2' : Integrable
      (fun x : Fin d → ℝ => ∑ i : Fin d, 2 * (coordPartial i f x * coordPartial i g x))
      (volume : Measure (Fin d → ℝ)) :=
    integrable_finsetSum _ fun i _ => (h2 i).const_mul 2
  have hint12 : Integrable (fun x : Fin d → ℝ =>
      2 * (g x * ∑ i : Fin d, coordPartial i (coordPartial i f) x)
        + ∑ i : Fin d, 2 * (coordPartial i f x * coordPartial i g x))
      (volume : Measure (Fin d → ℝ)) := hint1.add hint2'
  have h4' : Integrable (fun x : Fin d → ℝ => 2 * ((V (t, x) + 1) * (f x * g x)))
      (volume : Measure (Fin d → ℝ)) := h4
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_add hint12 h4',
    integral_add hint1 hint2']
  -- the two derivative terms cancel by the Green identity
  have hgreen : (∫ x : Fin d → ℝ,
      2 * (g x * ∑ i : Fin d, coordPartial i (coordPartial i f) x))
      = -∑ i : Fin d, 2 * ∫ x : Fin d → ℝ, coordPartial i f x * coordPartial i g x := by
    have hcomm : (fun x : Fin d → ℝ =>
        2 * (g x * ∑ i : Fin d, coordPartial i (coordPartial i f) x))
        = fun x : Fin d → ℝ =>
          2 * ((∑ i : Fin d, coordPartial i (coordPartial i f) x) * g x) := by
      funext x
      ring
    rw [hcomm, integral_const_mul,
      integral_laplacian_mul_of_integrable hfcd hgcd h1 h2 h3, mul_neg, Finset.mul_sum]
  have hsum2 : (∫ x : Fin d → ℝ, ∑ i : Fin d, 2 * (coordPartial i f x * coordPartial i g x))
      = ∑ i : Fin d, 2 * ∫ x : Fin d → ℝ, coordPartial i f x * coordPartial i g x := by
    rw [integral_finsetSum _ fun i _ => (h2 i).const_mul 2]
    exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _
  rw [hgreen, hsum2, neg_add_cancel, zero_add, integral_const_mul]
  rfl

end FluxIntegrable

end GaloisForLFunctions.HTGeometry
