/-
# The clock phase point carries the Schrödinger evolution

The one-sided clock sampler `t ↦ (t ω_i / 2π)` puts the anchored relative-phase orbit of the
eigencoefficients exactly on the evolved state at physical time `t`, up to the global phase of the
anchored level -- which no fidelity sees.  Together with Parseval in the eigenbasis this turns a
physical circuit-capture event at time `t` into membership of the clock phase point in the
relative-phase capture target.

Main results:
* `eigenCoords` — the eigencoordinates of a state, and their Parseval identities.
* `projectiveSpectralOrbit_finiteClockPhasePoint` — **the clock phase point is the evolved state**.
* `finitePureStateFidelity_unitaryEvolution_eq_orbit` — **the physical fidelity is the orbit
  fidelity**.
-/
import GaloisForLFunctions.HTGeometry.CircuitDictionaryCounting
import GaloisForLFunctions.HTGeometry.OneSidedCaptureDensity

open Matrix Complex UnitAddTorus ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The eigencoordinates of a state in an orthonormal eigenbasis. -/
def eigenCoords (e : α → α → ℂ) (psi : α → ℂ) : α → ℂ :=
  fun j => finiteComplexInner (e j) psi

/-- Parseval: the eigencoordinates carry the norm. -/
theorem sum_normSq_eigenCoords {H : Matrix α α ℂ} {e : α → α → ℂ} {lam : α → ℝ}
    (heb : IsOrthoEigenBasis H e lam) (psi : α → ℂ)
    (hpsi : finiteComplexInner psi psi = 1) :
    ∑ j, ‖eigenCoords e psi j‖ ^ 2 = 1 := by
  have hpar := parseval_finiteComplexInner heb psi psi
  rw [hpsi] at hpar
  have hterm : ∀ j, conj (finiteComplexInner (e j) psi) * finiteComplexInner (e j) psi
      = ((‖eigenCoords e psi j‖ ^ 2 : ℝ) : ℂ) := by
    intro j
    show conj (eigenCoords e psi j) * eigenCoords e psi j = ((‖eigenCoords e psi j‖ ^ 2 : ℝ) : ℂ)
    rw [Complex.sq_norm]
    exact (Complex.normSq_eq_conj_mul_self).symm
  rw [Finset.sum_congr rfl (fun j _ => hterm j), ← Complex.ofReal_sum] at hpar
  exact_mod_cast hpar.symm

theorem finiteComplexInner_eigenCoords {H : Matrix α α ℂ} {e : α → α → ℂ} {lam : α → ℝ}
    (heb : IsOrthoEigenBasis H e lam) (u v : α → ℂ) :
    finiteComplexInner (eigenCoords e u) (eigenCoords e v) = finiteComplexInner u v := by
  rw [parseval_finiteComplexInner heb u v]
  rfl

/-- The eigencoordinate of a combination of eigenvectors is its coefficient. -/
theorem eigenCoords_sum_smul {H : Matrix α α ℂ} {e : α → α → ℂ} {lam : α → ℝ}
    (heb : IsOrthoEigenBasis H e lam) (a : α → ℂ) (j : α) :
    finiteComplexInner (e j) (∑ k, a k • e k) = a j := by
  classical
  rw [finiteComplexInner_sum_right]
  rw [Finset.sum_congr rfl (fun k (_ : k ∈ Finset.univ) => by
    rw [finiteComplexInner_smul_right, heb.orth j k])]
  simp

/-- **The eigencoordinates of the evolved state.** -/
theorem eigenCoords_unitaryEvolution {H : Matrix α α ℂ} {e : α → α → ℂ} {lam : α → ℝ}
    (heb : IsOrthoEigenBasis H e lam) (psi : α → ℂ) (t : ℝ) (j : α) :
    eigenCoords e (unitaryEvolution H t *ᵥ psi) j
      = eigenCoords e psi j * Complex.exp (-(Complex.I * ((t : ℂ) * (lam j : ℂ)))) := by
  show finiteComplexInner (e j) (unitaryEvolution H t *ᵥ psi)
      = finiteComplexInner (e j) psi * Complex.exp (-(Complex.I * ((t : ℂ) * (lam j : ℂ))))
  rw [unitaryEvolution_mulVec_eq_sum heb psi t, eigenCoords_sum_smul heb]

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- **The one-sided clock phase point carries the Schrödinger orbit.** -/
theorem projectiveSpectralOrbit_finiteClockPhasePoint (ref : I) (c : I → ℂ) (lam : I → ℝ)
    (t : ℝ) (j : I) :
    projectiveSpectralOrbit ref c
        (finiteClockPhasePoint (projectiveFrequency (fun i => -lam i) ref) t) j =
      c j * Complex.exp (-(Complex.I * ((t : ℂ) * ((lam j : ℂ) - (lam ref : ℂ))))) := by
  rw [projectiveSpectralOrbit, torusAmpOrbit, UnitAddTorus.mFourier_single]
  by_cases hj : j ≠ ref
  · have hsec : torusSection ref
        (finiteClockPhasePoint (projectiveFrequency (fun i => -lam i) ref) t) j =
        ((t * (projectiveFrequency (fun i => -lam i) ref ⟨j, hj⟩) /
          (2 * Real.pi) : ℝ) : UnitAddCircle) := by
      rw [torusSection, dif_pos hj, finiteClockPhasePoint]
    rw [hsec, fourier_coe_apply]
    congr 1
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    rw [projectiveFrequency]
    push_cast
    field_simp
    ring_nf
  · have hjref : j = ref := not_ne_iff.mp hj
    have hsec : torusSection ref
        (finiteClockPhasePoint (projectiveFrequency (fun i => -lam i) ref) t) j = 0 := by
      rw [torusSection, dif_neg hj]
    rw [hsec]
    simp [hjref]

/-- **The physical fidelity is the orbit fidelity.**  At physical time `t` the fidelity of the
evolved state with a target equals the fidelity of the anchored relative-phase orbit of the
eigencoordinates with the target's eigencoordinates. -/
theorem finitePureStateFidelity_unitaryEvolution_eq_orbit {H : Matrix I I ℂ} {e : I → I → ℂ}
    {lam : I → ℝ} (heb : IsOrthoEigenBasis H e lam) (ref : I) (psi v : I → ℂ) (t : ℝ) :
    finitePureStateFidelity (unitaryEvolution H t *ᵥ psi) v
      = finitePureStateFidelity
          (projectiveSpectralOrbit ref (eigenCoords e psi)
            (finiteClockPhasePoint (projectiveFrequency (fun i => -lam i) ref) t))
          (eigenCoords e v) := by
  classical
  have hphase : ‖Complex.exp (Complex.I * ((t : ℂ) * (lam ref : ℂ)))‖ = 1 := by
    have hrw : Complex.I * ((t : ℂ) * (lam ref : ℂ)) = (((t * lam ref : ℝ)) : ℂ) * Complex.I := by
      push_cast; ring
    rw [hrw, Complex.norm_exp_ofReal_mul_I]
  have hleft : finiteComplexInner (unitaryEvolution H t *ᵥ psi) v
      = ∑ j, conj (eigenCoords e psi j) *
          Complex.exp (Complex.I * ((t : ℂ) * (lam j : ℂ))) * eigenCoords e v j := by
    rw [parseval_finiteComplexInner heb (unitaryEvolution H t *ᵥ psi) v]
    refine Finset.sum_congr rfl fun j _ => ?_
    have h1 : finiteComplexInner (e j) (unitaryEvolution H t *ᵥ psi)
        = eigenCoords e psi j * Complex.exp (-(Complex.I * ((t : ℂ) * (lam j : ℂ)))) :=
      eigenCoords_unitaryEvolution heb psi t j
    show conj (finiteComplexInner (e j) (unitaryEvolution H t *ᵥ psi)) *
        finiteComplexInner (e j) v
        = conj (eigenCoords e psi j) *
          Complex.exp (Complex.I * ((t : ℂ) * (lam j : ℂ))) * eigenCoords e v j
    rw [h1, map_mul, ← Complex.exp_conj]
    have hc : conj (-(Complex.I * ((t : ℂ) * (lam j : ℂ))))
        = Complex.I * ((t : ℂ) * (lam j : ℂ)) := by simp [Complex.conj_I]
    rw [hc]
    rfl
  have hright : finiteComplexInner
      (projectiveSpectralOrbit ref (eigenCoords e psi)
        (finiteClockPhasePoint (projectiveFrequency (fun i => -lam i) ref) t))
      (eigenCoords e v)
      = conj (Complex.exp (Complex.I * ((t : ℂ) * (lam ref : ℂ)))) *
        ∑ j, conj (eigenCoords e psi j) *
          Complex.exp (Complex.I * ((t : ℂ) * (lam j : ℂ))) * eigenCoords e v j := by
    rw [finiteComplexInner, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [projectiveSpectralOrbit_finiteClockPhasePoint ref (eigenCoords e psi) lam t j, map_mul,
      ← Complex.exp_conj]
    have hc : conj (-(Complex.I * ((t : ℂ) * ((lam j : ℂ) - (lam ref : ℂ)))))
        = Complex.I * ((t : ℂ) * ((lam j : ℂ) - (lam ref : ℂ))) := by simp [Complex.conj_I]
    have hc2 : conj (Complex.exp (Complex.I * ((t : ℂ) * (lam ref : ℂ))))
        = Complex.exp (-(Complex.I * ((t : ℂ) * (lam ref : ℂ)))) := by
      rw [← Complex.exp_conj]
      congr 1
      simp [Complex.conj_I]
    rw [hc, hc2]
    have hsplit : Complex.exp (Complex.I * ((t : ℂ) * (lam j : ℂ)))
        = Complex.exp (Complex.I * ((t : ℂ) * (lam ref : ℂ))) *
          Complex.exp (Complex.I * ((t : ℂ) * ((lam j : ℂ) - (lam ref : ℂ)))) := by
      rw [← Complex.exp_add]
      ring_nf
    have hcancel : Complex.exp (-(Complex.I * ((t : ℂ) * (lam ref : ℂ)))) *
        Complex.exp (Complex.I * ((t : ℂ) * (lam ref : ℂ))) = 1 := by
      rw [← Complex.exp_add]
      simp
    rw [hsplit]
    calc conj (eigenCoords e psi j) *
          Complex.exp (Complex.I * ((t : ℂ) * ((lam j : ℂ) - (lam ref : ℂ)))) * eigenCoords e v j
        = 1 * (conj (eigenCoords e psi j) *
            Complex.exp (Complex.I * ((t : ℂ) * ((lam j : ℂ) - (lam ref : ℂ)))) *
            eigenCoords e v j) := by ring
      _ = _ := by rw [← hcancel]; ring
  rw [finitePureStateFidelity, finitePureStateFidelity, hleft, hright, norm_mul,
    Complex.norm_conj, hphase, one_mul]

end GaloisForLFunctions.HTGeometry

end
