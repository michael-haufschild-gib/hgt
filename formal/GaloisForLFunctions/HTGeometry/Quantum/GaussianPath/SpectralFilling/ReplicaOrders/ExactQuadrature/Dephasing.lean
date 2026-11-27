import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralFilling.ReplicaOrders.ExactQuadrature.GapClock
import GaloisForLFunctions.HTGeometry.SpectralObservedOrbitDimension

/-! # Exact energy dephasing at finitely many physical dates -/
open Matrix Finset
open scoped Matrix.Norms.L2Operator ComplexConjugate
namespace GaloisForLFunctions.HTGeometry.SpectralFilling.ExactQuadrature
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I]
private abbrev Mat (I : Type*) := Matrix I I ℂ

theorem wave_diff (x y t : ℝ) : wave x t*conj (wave y t)=wave (x-y) t := by
  rw [wave,wave,←Complex.exp_conj,←Complex.exp_add,wave]
  congr 1
  push_cast
  simp [Complex.conj_ofReal]
  ring

/-- Every input matrix is pinched onto the equal-energy blocks by a
positive finite clock supported on actual dates after any chosen origin. -/
theorem physical_dephasing (H : selfAdjoint (Mat I)) (A : Mat I) (a : ℝ) (i j : I) :
    let E := H.2.isHermitian.eigenvalues
    let V := H.2.isHermitian.eigenvectorUnitary
    let Y := star V.val*A*V.val
    let U := unitaryEvolution H.val
    average (gaps univ (fun l => -E l)).toList
      (fun t => (star V.val*(U t*A*star (U t))*V.val) i j) a=if E i=E j then Y i j else 0 := by
  intro E V Y U
  let g (l : I) := -E l
  let φ (l : I) (t : ℝ) := Complex.exp (-(Complex.I*((t:ℂ)*(E l:ℂ))))
  have hφ (l : I) (t : ℝ) : φ l t=wave (g l) t := by
    dsimp only [φ,wave,g]
    congr 1
    push_cast
    ring
  have hfield (t : ℝ) : (star V.val*(U t*A*star (U t))*V.val) i j=Y i j*wave (g i-g j) t := by
    have he := evolved_reporter_conj V.property E (isHermitian_eq_conj_diagonal H.2.isHermitian) A t
    change U t*A*star (U t)=V.val*(diagonal (fun l => φ l t)*Y*star (diagonal (fun l => φ l t)))*star V.val at he
    rw [he,star_conj_cancel V.property,diagonal_conj_entry,hφ,hφ,←wave_diff]
    ring
  rw [show (fun t => (star V.val*(U t*A*star (U t))*V.val) i j)=_ from funext hfield,average_scale,
    gap_phase univ g (mem_univ i) (mem_univ j)]
  by_cases h : E i=E j <;> simp [g,h]

#print axioms physical_dephasing
end
end GaloisForLFunctions.HTGeometry.SpectralFilling.ExactQuadrature
