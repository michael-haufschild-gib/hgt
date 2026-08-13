import GaloisForLFunctions.HTGeometry.BoundedPerturbedFriedrichsOperator
import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative

/-!
# Compact resolvent under bounded self-adjoint perturbation

Let `T` be self-adjoint and suppose `(T - i)⁻¹` exists as a compact bounded operator `R`.
For a bounded self-adjoint perturbation `B`, the exact factorization

`T + B - i = (1 + B R) (T - i)`

reduces the resolvent problem to the bounded operator `1 + B R`.  The operator `-B R` is
compact.  It cannot have eigenvalue one: such an eigenvector would produce an `i`-eigenvector of
the self-adjoint operator `T + B`.  The compact Fredholm alternative therefore makes `1 + B R`
invertible.  Its product with `R` is the desired compact resolvent.

This is the perturbation theorem needed by the Connes--Consani compressed circle Dirac operator.
Unlike a bare invocation of Kato--Rellich, it also proves the compact-resolvent clause required by
a spectral triple.
-/

open Module Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Bounded self-adjoint perturbations preserve compact resolvent at `i`.** -/
theorem boundedShift_hasCompactResolventAt_I
    (T : H →ₗ.[ℂ] H) (B : H →L[ℂ] H)
    (hT : IsSelfAdjoint T) (hB : IsSelfAdjoint B)
    (hres : LinearPMap.HasCompactResolventAt T Complex.I) :
    LinearPMap.HasCompactResolventAt (boundedShift T B) Complex.I := by
  rcases hres with ⟨R, hRcompact, ⟨hRdom, hRright⟩, hRleft⟩
  let C : H →L[ℂ] H := -(B.comp R)
  let K : H →L[ℂ] H := 1 - C
  have K_apply (v : H) : K v = v + B (R v) := by
    simp [K, C]
  have hCcompact : IsCompactOperator C := (hRcompact.clm_comp B).neg
  have hC_no_one : ¬ Module.End.HasEigenvalue (C : Module.End ℂ H) 1 := by
    intro heig
    obtain ⟨x, hxmem, hxne⟩ := heig.exists_hasEigenvector
    have hCx : (C : Module.End ℂ H) x = x := by
      simpa only [one_smul] using Module.End.mem_eigenspace_iff.mp hxmem
    let y : (boundedShift T B).domain := ⟨R x, by simpa using hRdom x⟩
    have hSy : boundedShift T B y = Complex.I • (y : H) := by
      have hright := hRright x
      change T ⟨R x, hRdom x⟩ - Complex.I • R x = x at hright
      have hBx : B (R x) = -x := by
        have hCx' : -(B (R x)) = x := by simpa [C] using hCx
        exact neg_eq_iff_eq_neg.mp hCx'
      rw [boundedShift_apply]
      change T ⟨R x, hRdom x⟩ + B (R x) = Complex.I • R x
      have hTvalue : T ⟨R x, hRdom x⟩ = x + Complex.I • R x :=
        sub_eq_iff_eq_add.mp hright
      rw [hTvalue, hBx]
      module
    let S : H →ₗ.[ℂ] H := boundedShift T B
    have hSself : IsSelfAdjoint S := boundedShift_isSelfAdjoint T B hT hB
    have hSformal : S.IsFormalAdjoint S := by
      have hformal := LinearPMap.adjoint_isFormalAdjoint hSself.dense_domain
      change S.adjoint = S at hSself
      rw [hSself] at hformal
      exact hformal
    have hsym := hSformal y y
    rw [hSy, inner_smul_left, inner_smul_right] at hsym
    have hynorm : ‖(y : H)‖ ^ 2 = 0 := by
      have him := congrArg Complex.im hsym
      rw [inner_self_eq_norm_sq_to_K] at him
      norm_num [Complex.mul_im] at him
      have him' : -(‖(y : H)‖ ^ 2) = ‖(y : H)‖ ^ 2 := by
        exact_mod_cast him
      nlinarith
    have hyzero : (y : H) = 0 := by
      rw [sq_eq_zero_iff] at hynorm
      exact norm_eq_zero.mp hynorm
    apply hxne
    have hright := hRright x
    change T ⟨R x, hRdom x⟩ - Complex.I • R x = x at hright
    have hRzero : R x = 0 := hyzero
    have hsubzero : (⟨R x, hRdom x⟩ : T.domain) = 0 := Subtype.ext hRzero
    rw [hsubzero, LinearPMap.map_zero, hRzero, smul_zero, sub_zero] at hright
    exact hright.symm
  have hCres : (1 : ℂ) ∈ resolventSet ℂ C :=
    (hCcompact.hasEigenvalue_or_mem_resolventSet one_ne_zero).resolve_left hC_no_one
  have hKunit : IsUnit K := by
    simpa [K] using (spectrum.mem_resolventSet_iff.mp hCres)
  let Kinv : H →L[ℂ] H := Ring.inverse K
  have hKKinv : K * Kinv = 1 := Ring.mul_inverse_cancel K hKunit
  have hKinvK : Kinv * K = 1 := Ring.inverse_mul_cancel K hKunit
  let R' : H →L[ℂ] H := R.comp Kinv
  have hR'compact : IsCompactOperator R' := hRcompact.comp_clm Kinv
  refine ⟨R', hR'compact, ?_, ?_⟩
  · refine ⟨fun x => by simpa [R'] using hRdom (Kinv x), ?_⟩
    intro x
    have hright := hRright (Kinv x)
    have hKapply : K (Kinv x) = x := by
      calc
        K (Kinv x) = (K * Kinv) x := rfl
        _ = (1 : H →L[ℂ] H) x := by rw [hKKinv]
        _ = x := rfl
    change boundedShift T B
        ⟨R' x, by simpa [R'] using hRdom (Kinv x)⟩ - Complex.I • R' x = x
    rw [boundedShift_apply]
    calc
      T ⟨R (Kinv x), hRdom (Kinv x)⟩ + B (R (Kinv x)) -
          Complex.I • R (Kinv x) =
        (T ⟨R (Kinv x), hRdom (Kinv x)⟩ - Complex.I • R (Kinv x)) +
          B (R (Kinv x)) := by abel
      _ = Kinv x + B (R (Kinv x)) := by rw [hright]
      _ = K (Kinv x) := (K_apply (Kinv x)).symm
      _ = x := hKapply
  · intro x
    let xT : T.domain := ⟨(x : H), by
      simpa only [boundedShift_domain] using x.property⟩
    have hfactor :
        K (T xT - Complex.I • (x : H)) =
          boundedShift T B x - Complex.I • (x : H) := by
      have hleft := hRleft xT
      rw [boundedShift_apply]
      change K (T xT - Complex.I • (x : H)) =
        T xT + B (x : H) - Complex.I • (x : H)
      rw [K_apply, hleft]
      module
    change R (Kinv (boundedShift T B x - Complex.I • (x : H))) = (x : H)
    rw [← hfactor]
    have hcancel : Kinv (K (T xT - Complex.I • (x : H))) =
        T xT - Complex.I • (x : H) := by
      calc
        Kinv (K (T xT - Complex.I • (x : H))) =
            (Kinv * K) (T xT - Complex.I • (x : H)) := rfl
        _ = (1 : H →L[ℂ] H) (T xT - Complex.I • (x : H)) := by rw [hKinvK]
        _ = T xT - Complex.I • (x : H) := rfl
    rw [hcancel]
    exact hRleft xT

end

end GaloisForLFunctions.HTGeometry
