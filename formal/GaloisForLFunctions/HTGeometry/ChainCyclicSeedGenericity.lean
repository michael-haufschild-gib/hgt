/-
# The cubic seed is cyclic for almost every chain direction

The near-uniform diagonal carrier of the path shell has pairwise distinct classical energies, so at
that coefficient the chain Hamiltonian is diagonal with a simple spectrum; the cubic seed has
constant nonzero modulus in the computational basis, so its Krylov matrix there factors as a
diagonal matrix times a Vandermonde matrix and is invertible.  That witness makes the Krylov
determinant a nonzero real-analytic function of the coefficients, and a nonzero determinant makes
every eigenbasis overlap of the seed nonzero.

Main results:
* `det_ensembleKrylov_ne_zero_of_diagonal` — a diagonal member with distinct energies is a witness.
* `exists_chainKrylov_witness` — **the chain family has such a witness**.
* `cubicSeed_ne_zero` — the cubic seed has no vanishing amplitude.
* `finiteComplexInner_patchEigenBasis_ne_zero` — **a nonzero Krylov determinant makes the seed
  cyclic**.
-/
import GaloisForLFunctions.HTGeometry.EnsembleKrylovGenericity
import GaloisForLFunctions.HTGeometry.NearUniformSeparatingCarrier
import GaloisForLFunctions.HTGeometry.PathChainLabelIdentification
import GaloisForLFunctions.HTGeometry.PatchChainPullback
import GaloisForLFunctions.HTGeometry.CapacityIncubationInstantiation
import GaloisForLFunctions.HTGeometry.AlgebraicOrbitCoordinates

open Matrix MeasureTheory
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

set_option linter.unusedSectionVars false

/-- **A diagonal member with distinct energies makes every everywhere-nonzero seed cyclic.** -/
theorem det_ensembleKrylov_ne_zero_of_diagonal {N D : ℕ}
    {P : Fin N → Matrix (Fin D) (Fin D) ℂ} {θ : Fin N → ℝ} {d : Fin D → ℝ}
    (hH : spectralEnsembleMatrix P θ = Matrix.diagonal (fun i => ((d i : ℝ) : ℂ)))
    (hd : Function.Injective d) {χ : Fin D → ℂ} (hχ : ∀ x, χ x ≠ 0) :
    (ensembleKrylov P χ θ).det ≠ 0 := by
  classical
  have hK : ensembleKrylov P χ θ
      = Matrix.diagonal χ * Matrix.vandermonde (fun i => ((d i : ℝ) : ℂ)) := by
    ext x j
    rw [Matrix.diagonal_mul, Matrix.vandermonde]
    show ((spectralEnsembleMatrix P θ) ^ (j : ℕ) *ᵥ χ) x = χ x * ((d x : ℝ) : ℂ) ^ (j : ℕ)
    rw [hH, Matrix.diagonal_pow]
    show (Matrix.diagonal ((fun i => ((d i : ℝ) : ℂ)) ^ (j : ℕ)) *ᵥ χ) x = _
    rw [Matrix.mulVec, dotProduct]
    rw [Finset.sum_eq_single x]
    · rw [Matrix.diagonal_apply_eq, Pi.pow_apply]
      ring
    · intro y _ hy
      rw [Matrix.diagonal_apply_ne _ (Ne.symm hy), zero_mul]
    · intro hx
      exact absurd (Finset.mem_univ x) hx
  rw [hK, Matrix.det_mul, Matrix.det_diagonal]
  refine mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun x _ => hχ x) ?_
  refine Matrix.det_vandermonde_ne_zero_iff.mpr fun a b hab => ?_
  exact hd (Complex.ofReal_injective hab)

/-- **The chain family makes every everywhere-nonzero seed cyclic at some coefficient.**  The
near-uniform diagonal carrier separates the classical energies. -/
theorem exists_chainKrylov_witness (k : ℕ) {χ : Fin (2 ^ (k + 3)) → ℂ} (hχ : ∀ x, χ x ≠ 0) :
    ∃ θ₀ : Fin (Fintype.card (ChainLabel (k + 3))) → ℝ,
      (ensembleKrylov (chainPauliFin (k + 3)) χ θ₀).det ≠ 0 := by
  classical
  set eps : ℝ := (2 / 3) / 3 ^ (k + 3) with hepsdef
  have heps : 0 < eps := by
    rw [hepsdef]
    positivity
  have hsmall : eps * 3 ^ (k + 1 + 2) ≤ 2 / 3 := by
    rw [hepsdef, show k + 1 + 2 = k + 3 from by omega]
    have h3 : (0 : ℝ) < 3 ^ (k + 3) := by positivity
    field_simp
    exact le_refl 1
  set u : PathShell (k + 1) := nearUniformCarrier (k + 1) eps with hudef
  refine ⟨fun a => u (pathCoeffEquiv (k + 1) a), ?_⟩
  have hdiag : pathHamiltonian u = Matrix.diagonal (fun x => ((pathDiagEnergy u x : ℝ) : ℂ)) :=
    pathHamiltonian_eq_diagonal u (fun l hl => nearUniformCarrier_offDiag eps l hl)
  have hH : spectralEnsembleMatrix (chainPauliFin (k + 3)) (fun a => u (pathCoeffEquiv (k + 1) a))
      = Matrix.diagonal
        (fun i => ((pathDiagEnergy u ((qubitConfigFin (k + 3)).symm i) : ℝ) : ℂ)) := by
    rw [← reindex_pathHamiltonian u, hdiag]
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [Matrix.reindex, Matrix.submatrix, Matrix.diagonal_apply_eq]
    · rw [Matrix.diagonal_apply_ne _ hij]
      show Matrix.diagonal (fun x => ((pathDiagEnergy u x : ℝ) : ℂ))
        ((qubitConfigFin (k + 3)).symm i) ((qubitConfigFin (k + 3)).symm j) = 0
      exact Matrix.diagonal_apply_ne _ (fun h => hij ((qubitConfigFin (k + 3)).symm.injective h))
  refine det_ensembleKrylov_ne_zero_of_diagonal hH ?_ hχ
  intro a b hab
  simp only at hab
  by_contra hne
  have hconf : (qubitConfigFin (k + 3)).symm a ≠ (qubitConfigFin (k + 3)).symm b := by
    intro h
    exact hne ((qubitConfigFin (k + 3)).symm.injective h)
  have hsep := separation_nearUniformCarrier (n := k + 1) heps hsmall hconf
  rw [← hudef] at hsep
  rw [hab, sub_self, abs_zero] at hsep
  linarith [heps]

/-! ## The cubic seed never vanishes -/

theorem uniformPhaseSeed_ne_zero {α : Type*} [Fintype α] [DecidableEq α]
    (hα : 0 < Fintype.card α) (x : α → ℝ) (a : α) : uniformPhaseSeed x a ≠ 0 := by
  rw [uniformPhaseSeed, torusReplicaPhaseOrbit]
  refine mul_ne_zero ?_ ?_
  · have hpos : (0 : ℝ) < uniformPhaseWeights α a := by
      rw [uniformPhaseWeights]
      exact inv_pos.mpr (by exact_mod_cast hα)
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact (Real.sqrt_pos.mpr hpos).ne'
  · intro h
    have hnorm := norm_charLift (Pi.single a 1) x
    rw [h, norm_zero] at hnorm
    exact absurd hnorm (by norm_num)

theorem cubicSeed_ne_zero (n : ℕ) (c : MonLe (Fin n) 3 → ZMod 8) (x : Fin (2 ^ n)) :
    cubicSeed n c x ≠ 0 :=
  uniformPhaseSeed_ne_zero Fintype.card_pos _ _

/-! ## From a nonzero Krylov determinant to nonvanishing overlaps -/

theorem reindex_pow {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (A : Matrix α α ℂ) (m : ℕ) :
    (Matrix.reindex e e A) ^ m = Matrix.reindex e e (A ^ m) := by
  induction m with
  | zero =>
      ext x y
      by_cases h : x = y
      · subst h
        simp [Matrix.reindex, Matrix.submatrix, Matrix.one_apply]
      · simp [Matrix.reindex, Matrix.submatrix, Matrix.one_apply, h,
          e.symm.injective.eq_iff]
  | succ m ih =>
      rw [pow_succ, ih, pow_succ]
      show (A ^ m).submatrix e.symm e.symm * A.submatrix e.symm e.symm = _
      rw [Matrix.submatrix_mul_equiv]
      rfl

theorem mulVec_reindex_comp {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (A : Matrix α α ℂ) (Ω : α → ℂ) :
    (Matrix.reindex e e A) *ᵥ (fun y => Ω (e.symm y)) = fun x => (A *ᵥ Ω) (e.symm x) := by
  funext x
  show ∑ y, A (e.symm x) (e.symm y) * Ω (e.symm y) = ∑ y, A (e.symm x) y * Ω y
  exact Equiv.sum_comp e.symm fun y => A (e.symm x) y * Ω y

/-- **A nonzero Krylov determinant makes every eigenbasis overlap of the seed nonzero.** -/
theorem finiteComplexInner_patchEigenBasis_ne_zero (k : ℕ)
    (c : MonLe (Fin (k + 3)) 3 → ZMod 8) {ω : PatchSphere k}
    (hω : (ensembleKrylov (chainPauliFin (k + 3)) (cubicSeed (k + 3) c)
      (sphereCoeff (patchToCoeff k ω))).det ≠ 0)
    (j : FiniteQubitConfiguration (Fin (k + 3))) :
    finiteComplexInner (patchEigenBasis k ω j) (registerCubicSeed k c) ≠ 0 := by
  classical
  set e := qubitConfigFin (k + 3) with hedef
  set H := pathHamiltonian (pathPatchIsometry (k + 1)
    (ω : PatchSpace (2 * (k + 1) + 3) (10 * (k + 1) + 12))) with hHdef
  set Ω := registerCubicSeed k c with hΩdef
  have hχ : (fun y => cubicSeed (k + 3) c (e y)) = Ω := cubicSeed_comp (k + 3) c
  have hcols := Matrix.linearIndependent_cols_of_det_ne_zero hω
  have hcol : ∀ m : Fin (2 ^ (k + 3)),
      (ensembleKrylov (chainPauliFin (k + 3)) (cubicSeed (k + 3) c)
        (sphereCoeff (patchToCoeff k ω))).col m
        = fun x => (H ^ (m : ℕ) *ᵥ Ω) (e.symm x) := by
    intro m
    funext x
    show ((spectralEnsembleMatrix (chainPauliFin (k + 3)) (sphereCoeff (patchToCoeff k ω)))
        ^ (m : ℕ) *ᵥ cubicSeed (k + 3) c) x = _
    rw [← patchHam_reindex ω, reindex_pow]
    have hseed : cubicSeed (k + 3) c = fun y => Ω (e.symm y) := by
      funext y
      rw [← hχ]
      simp
    rw [hseed, mulVec_reindex_comp]
  have hcard : Fintype.card (FiniteQubitConfiguration (Fin (k + 3))) = 2 ^ (k + 3) :=
    (Fintype.card_congr e).trans (Fintype.card_fin _)
  set E : (Fin (2 ^ (k + 3)) → ℂ) →ₗ[ℂ] (FiniteQubitConfiguration (Fin (k + 3)) → ℂ) :=
    { toFun := fun v => fun y => v (e y)
      map_add' := fun v w => rfl
      map_smul' := fun a v => rfl } with hEdef
  have hEapply : ∀ (v : Fin (2 ^ (k + 3)) → ℂ) (y : FiniteQubitConfiguration (Fin (k + 3))),
      E v y = v (e y) := fun _ _ => rfl
  have hEker : LinearMap.ker E = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro v hv
    funext x
    have h1 := congrFun hv (e.symm x)
    rw [hEapply, Equiv.apply_symm_apply] at h1
    exact h1
  have hind0 : LinearIndependent ℂ
      (fun m : Fin (2 ^ (k + 3)) => fun y => (H ^ (m : ℕ) *ᵥ Ω) (e.symm y)) := by
    have hc := hcols
    rw [funext hcol] at hc
    exact hc
  have hstep2 : LinearIndependent ℂ
      (fun m : Fin (Fintype.card (FiniteQubitConfiguration (Fin (k + 3)))) =>
        H ^ (m : ℕ) *ᵥ Ω) := by
    have heq : (fun m : Fin (Fintype.card (FiniteQubitConfiguration (Fin (k + 3)))) =>
          H ^ (m : ℕ) *ᵥ Ω)
        = ⇑E ∘ ((fun m : Fin (2 ^ (k + 3)) => fun y => (H ^ (m : ℕ) *ᵥ Ω) (e.symm y))
            ∘ ⇑(finCongr hcard)) := by
      funext m
      funext y
      show _ = E (fun y' => (H ^ ((finCongr hcard m : Fin (2 ^ (k + 3))) : ℕ) *ᵥ Ω) (e.symm y')) y
      rw [hEapply, Equiv.symm_apply_apply]
      congr 3
    rw [heq]
    exact ((hind0.comp (finCongr hcard) (finCongr hcard).injective).map' E hEker)
  exact AlgebraicOrbit.finiteComplexInner_ne_zero_of_linearIndependent
    (isOrthoEigenBasis_patchEigenBasis ω) hstep2 j

end

end GaloisForLFunctions.HTGeometry
