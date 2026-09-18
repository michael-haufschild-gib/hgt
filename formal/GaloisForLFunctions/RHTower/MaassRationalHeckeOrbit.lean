import GaloisForLFunctions.RHTower.SelbergMaassHeckeOperatorConvolution

/-!
# Source-attached rational Hecke orbit

For one principal-congruence Maass eigenspace vector, this module defines the
span of all positive rational Hecke-coset images.  The exact rational Mackey
product formula makes that span stable under every positive rational trace.

This is an exact correspondence module only.  It neither identifies a local
Hecke algebra nor supplies commutativity, finite-dimensionality, local Satake
parameters, or a symmetric-power lift.
-/

namespace GaloisForLFunctions.RHTower

open Complex Matrix SpecialLinearGroup GeneralLinearGroup
open scoped MatrixGroups BigOperators

noncomputable section

/-- Span of the exact positive rational Hecke-coset orbit of one Maass eigenvector. -/
def principalHeckeOrbitSpan (N : ℕ) (lam : ℝ)
    (u : glMaassCuspEigenspace (principalCongruenceGL N) lam) :
    Submodule ℂ (glMaassCuspEigenspace (principalCongruenceGL N) lam) :=
  Submodule.span ℂ (Set.range (fun D : HeckeCoset positiveRationalGLRealImage
    (principalCongruenceGL N) (principalCongruenceGL N) =>
      rationalPrincipalHeckeCosetLinear N lam D u))

/-- A positive rational trace maps each generator of the source Hecke orbit
back into that orbit, by its finite Mackey decomposition. -/
theorem rationalPrincipalTraceLinear_orbit_generator_mem (N : ℕ) (h : GL (Fin 2) ℚ)
    (hh : 0 < (h.map (algebraMap ℚ ℝ)).val.det) (lam : ℝ)
    (u : glMaassCuspEigenspace (principalCongruenceGL N) lam)
    (D : HeckeCoset positiveRationalGLRealImage
      (principalCongruenceGL N) (principalCongruenceGL N)) :
    rationalPrincipalTraceLinear N h hh lam
      (rationalPrincipalHeckeCosetLinear N lam D u) ∈
        principalHeckeOrbitSpan N lam u := by
  classical
  refine Quotient.inductionOn D ?_
  intro d
  change rationalPrincipalTraceLinear N h hh lam
      (rationalPrincipalHeckeLinear N lam d u) ∈
        principalHeckeOrbitSpan N lam u
  let g := positiveRationalHeckeLift d
  have hg : 0 < (g.map (algebraMap ℚ ℝ)).val.det :=
    positiveRationalHeckeLift_det_pos d
  change rationalPrincipalTraceLinear N h hh lam
      (rationalPrincipalTraceLinear N g hg lam u) ∈
        principalHeckeOrbitSpan N lam u
  letI : Fintype (rationalMackeyOrbit N g h) := rationalMackeyOrbitFintype N g h
  have hcomp := rationalPrincipalTraceLinear_comp_eq_fiberwise_HeckeCosetLinear
    N g h hg hh lam
  have happ := LinearMap.congr_fun hcomp u
  rw [LinearMap.comp_apply] at happ
  rw [happ]
  rw [LinearMap.sum_apply]
  simp only [LinearMap.coe_smul, Pi.smul_apply]
  apply Submodule.sum_mem
  intro E hE
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨E, rfl⟩

/-- Every positive rational trace preserves the source-attached rational Hecke orbit. -/
theorem rationalPrincipalTraceLinear_maps_principalHeckeOrbitSpan (N : ℕ)
    (h : GL (Fin 2) ℚ) (hh : 0 < (h.map (algebraMap ℚ ℝ)).val.det) (lam : ℝ)
    (u v : glMaassCuspEigenspace (principalCongruenceGL N) lam)
    (hv : v ∈ principalHeckeOrbitSpan N lam u) :
    rationalPrincipalTraceLinear N h hh lam v ∈ principalHeckeOrbitSpan N lam u := by
  let S := principalHeckeOrbitSpan N lam u
  let T := rationalPrincipalTraceLinear N h hh lam
  have hgen : ∀ D : HeckeCoset positiveRationalGLRealImage
      (principalCongruenceGL N) (principalCongruenceGL N), T
        (rationalPrincipalHeckeCosetLinear N lam D u) ∈ S := by
    intro D
    simpa only [S, T] using
      rationalPrincipalTraceLinear_orbit_generator_mem N h hh lam u D
  have hmap : S.map T ≤ S := by
    rw [Submodule.map_le_iff_le_comap]
    apply Submodule.span_le.2
    rintro x ⟨D, rfl⟩
    exact hgen D
  apply hmap
  exact ⟨v, hv, rfl⟩

end

end GaloisForLFunctions.RHTower
