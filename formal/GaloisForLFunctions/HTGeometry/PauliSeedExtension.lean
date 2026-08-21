/-
# The inductive step of the Pauli-path endpoint-complete induction

One leaf extension of an endpoint-complete Pauli seed is again an endpoint-complete Pauli seed: the
chart supplies a maximally projective extended spectrum and a new endpoint probe with no zero
off-diagonal spectral entry, recentring the energies makes the extension traceless, and the span
lemmas keep the Hamiltonian at weight two and the probe at weight one.

Main results:
* `trace_layerMatrixCoupling` — the trace of a layer coupling factorizes.
* `exists_pauliSeed_succ` — **the inductive step**.
-/
import GaloisForLFunctions.HTGeometry.PhysicalLeafPauliChainSpan
import GaloisForLFunctions.HTGeometry.PhysicalLeafSpectralDiagonal
import GaloisForLFunctions.HTGeometry.TwoQubitPauliSeed
import GaloisForLFunctions.HTGeometry.UnitaryChartProbeFamilyReduction
import GaloisForLFunctions.HTGeometry.EndpointCompleteMaximalLeafExtension
import GaloisForLFunctions.HTGeometry.SeparableInteractionTemporalDimensionLaw

open Matrix

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

theorem trace_layerMatrixCoupling {α ρ : Type*} [Fintype α] [Fintype ρ]
    (A : Matrix α α ℂ) (B : Matrix ρ ρ ℂ) :
    (layerMatrixCoupling A B).trace = A.trace * B.trace := by
  classical
  rw [Matrix.trace, Matrix.trace, Matrix.trace, Fintype.sum_prod_type]
  simp only [Matrix.diag_apply, layerMatrixCoupling]
  rw [Finset.sum_mul_sum]

theorem trace_reindex_snocConfig {n : ℕ}
    (X : Matrix (FiniteQubitConfiguration (Fin n) × Bool)
      (FiniteQubitConfiguration (Fin n) × Bool) ℂ) :
    (Matrix.reindex (snocConfig n) (snocConfig n) X).trace = X.trace := by
  rw [Matrix.trace, Matrix.trace]
  exact Equiv.sum_comp (snocConfig n).symm
    (fun i : FiniteQubitConfiguration (Fin n) × Bool => X i i)


theorem physicalLeafHamiltonian_sub_smul_one {P rho : Type*} [Fintype P] [Fintype rho]
    [DecidableEq P] [DecidableEq rho]
    (H V : Matrix P P ℂ) (shift : rho → ℂ) (edge : Matrix rho rho ℂ) (c : ℂ) :
    physicalLeafHamiltonian H V shift edge - c • (1 : Matrix (P × rho) (P × rho) ℂ)
      = physicalLeafHamiltonian H V (fun b => shift b - c) edge := by
  ext x y
  simp only [physicalLeafHamiltonian, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
    layerMatrixCoupling, Matrix.one_apply, Matrix.diagonal_apply, smul_eq_mul, Prod.ext_iff]
  by_cases h1 : x.1 = y.1 <;> by_cases h2 : x.2 = y.2 <;> simp [h1, h2]
  ring

/-- **The inductive step of the Pauli-path induction.**  A leaf extension of an endpoint-complete
Pauli seed is again an endpoint-complete Pauli seed. -/
theorem exists_pauliSeed_succ {m : ℕ} {S : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    (hcard : 3 ≤ Fintype.card S)
    {E : S → ℝ} (hEmax : MaximallyProjectiveEnergy E)
    {U : Matrix (FiniteQubitConfiguration (Fin (m + 1))) S ℂ}
    (hUleft : Uᴴ * U = 1) (hUright : U * Uᴴ = 1)
    {V : Matrix (FiniteQubitConfiguration (Fin (m + 1))) (FiniteQubitConfiguration (Fin (m + 1))) ℂ}
    (hVherm : V.IsHermitian) (hVspan : V ∈ pauliSiteSpan (m + 1) (Fin.last m))
    (hHspan : U * Matrix.diagonal (fun i => (E i : ℂ)) * Uᴴ ∈ pauliChainSpan (m + 1))
    (hVtrans : ∀ a b : S, a ≠ b → (Uᴴ * V * U) a b ≠ 0) :
    ∃ (E' : S × Bool → ℝ)
      (U' : Matrix (FiniteQubitConfiguration (Fin ((m + 1) + 1))) (S × Bool) ℂ)
      (V' : Matrix (FiniteQubitConfiguration (Fin ((m + 1) + 1)))
        (FiniteQubitConfiguration (Fin ((m + 1) + 1))) ℂ),
      MaximallyProjectiveEnergy E' ∧ (∑ i, E' i) = 0 ∧
      U'ᴴ * U' = 1 ∧ U' * U'ᴴ = 1 ∧
      V'.IsHermitian ∧ V' ∈ pauliSiteSpan ((m + 1) + 1) (Fin.last (m + 1)) ∧
      (U' * Matrix.diagonal (fun i => (E' i : ℂ)) * U'ᴴ) ∈ pauliChainSpan ((m + 1) + 1) ∧
      (∀ a b : S × Bool, a ≠ b → (U'ᴴ * V' * U') a b ≠ 0) := by
  classical
  obtain ⟨H, hHdef⟩ : ∃ H, H = U * Matrix.diagonal (fun i => (E i : ℂ)) * Uᴴ := ⟨_, rfl⟩
  obtain ⟨M, hMdef⟩ : ∃ M, M = Uᴴ * V * U := ⟨_, rfl⟩
  have hMherm : M.IsHermitian := by
    rw [hMdef]; exact Matrix.isHermitian_conjTranspose_mul_mul U hVherm
  have hM : ∀ a b : S, a ≠ b → M a b ≠ 0 := by rw [hMdef]; exact hVtrans
  obtain ⟨z, C, q, hH, e, X, hpU, hmaxCanonical, he, hXherm, hXfull⟩ :=
    exists_maximallyProjective_unitaryEndpointComplete_realLeafParameter hcard E hEmax M hMherm hM
  have hedge : (realLocalExtensionParameter (localExtensionSliceParameter q)).2.IsHermitian :=
    realSymmetricEdge_isHermitian _
  have hdiag := C.localExtensionMatrix_eq_unitary_diagonal (fun a => (E a : ℂ))
    (boolShift (z : ℂ)) M (realLocalExtensionParameter (localExtensionSliceParameter q)) hH e he
  have hphys := physicalLeafHamiltonian_eq_spectralBasis_diagonal U hUleft hUright
    (fun a => (E a : ℂ)) V
    (realLocalExtensionParameter (localExtensionSliceParameter q)).1
    (realLocalExtensionParameter (localExtensionSliceParameter q)).2
    (C.unitaryEigenvectorMatrix hH e)
    (fun i => ((C.realBranchEnergy (fun a => (E a : ℂ)) (boolShift (z : ℂ)) M
      (realLocalExtensionParameter (localExtensionSliceParameter q)) i : ℝ) : ℂ))
    (by rw [← hMdef]; simpa [Matrix.star_eq_conjTranspose] using hdiag)
  obtain ⟨B, hBdef⟩ : ∃ B, B = physicalLeafSpectralBasis U (C.unitaryEigenvectorMatrix hH e) :=
    ⟨_, rfl⟩
  have hWleft : (C.unitaryEigenvectorMatrix hH e)ᴴ * C.unitaryEigenvectorMatrix hH e = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using C.star_unitaryEigenvectorMatrix_mul_self hH e
  have hWright : C.unitaryEigenvectorMatrix hH e * (C.unitaryEigenvectorMatrix hH e)ᴴ = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using C.unitaryEigenvectorMatrix_mul_star_self hH e
  have hBleft : Bᴴ * B = 1 := by
    rw [hBdef]; exact physicalLeafSpectralBasis_star_mul_self U _ hUleft hWleft
  have hBright : B * Bᴴ = 1 := by
    rw [hBdef]; exact physicalLeafSpectralBasis_mul_star_self U _ hUright hWright
  obtain ⟨E0, hE0def⟩ : ∃ E0 : S × Bool → ℝ, E0 = C.realBranchEnergy (fun a => (E a : ℂ))
      (boolShift (z : ℂ)) M (realLocalExtensionParameter (localExtensionSliceParameter q)) :=
    ⟨_, rfl⟩
  obtain ⟨cs, hcsdef⟩ : ∃ cs : ℝ, cs = (∑ i, E0 i) / (Fintype.card (S × Bool) : ℝ) := ⟨_, rfl⟩
  obtain ⟨r, hrdef⟩ : ∃ r : Bool → ℝ, r = (localExtensionSliceParameter q).1 := ⟨_, rfl⟩
  have hp1 : (realLocalExtensionParameter (localExtensionSliceParameter q)).1
      = fun b => ((r b : ℝ) : ℂ) := by rw [hrdef]; rfl
  obtain ⟨Xt, hXtdef⟩ : ∃ Xt, Xt = X - ((X.trace.re / 2 : ℝ) : ℂ) • (1 : Matrix Bool Bool ℂ) :=
    ⟨_, rfl⟩
  have hXtherm : Xt.IsHermitian := by
    rw [hXtdef]
    refine Matrix.IsHermitian.sub hXherm ?_
    rw [Matrix.IsHermitian, Matrix.conjTranspose_smul]
    simp
  have hXtrre : X.trace = ((X.trace.re : ℝ) : ℂ) := by
    have h : (starRingEnd ℂ) X.trace = X.trace := by
      have hc := congrArg Matrix.trace hXherm
      rw [Matrix.trace_conjTranspose] at hc
      exact hc
    exact (Complex.conj_eq_iff_re.mp h).symm
  have hXttr : Xt.trace = 0 := by
    rw [hXtdef, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one, smul_eq_mul]
    rw [hXtrre]
    simp [Fintype.card_bool]
  refine ⟨recentredEnergy E0,
    B.submatrix (snocConfig (m + 1)).symm ⇑(Equiv.refl (S × Bool)),
    Matrix.reindex (snocConfig (m + 1)) (snocConfig (m + 1))
      (layerMatrixCoupling (1 : Matrix (FiniteQubitConfiguration (Fin (m + 1)))
        (FiniteQubitConfiguration (Fin (m + 1))) ℂ) Xt), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine maximallyProjectiveEnergy_recentredEnergy ?_
    have : E0 = fun i => hH.eigenvalues (e i) := by
      funext i; rw [hE0def]; exact he i
    rw [this]
    exact maximallyProjectiveEnergy_equiv e hmaxCanonical
  · exact sum_recentredEnergy E0
  · rw [Matrix.conjTranspose_submatrix,
      Matrix.submatrix_mul_equiv Bᴴ B ⇑(Equiv.refl (S × Bool)) (snocConfig (m + 1)).symm
        ⇑(Equiv.refl (S × Bool)), hBleft]
    rfl
  · rw [Matrix.conjTranspose_submatrix,
      Matrix.submatrix_mul_equiv B Bᴴ ⇑(snocConfig (m + 1)).symm (Equiv.refl (S × Bool))
        ⇑(snocConfig (m + 1)).symm, hBright]
    ext x y
    simp only [Matrix.submatrix_apply, Matrix.one_apply]
    by_cases hxy : x = y
    · subst hxy; simp
    · rw [if_neg hxy, if_neg fun hcon => hxy ((snocConfig (m + 1)).symm.injective hcon)]
  · exact (layerMatrixCoupling_isHermitian Matrix.isHermitian_one hXtherm).submatrix _
  · exact newProbe_mem_pauliSiteSpan hXtherm hXttr
  · rw [← hBdef, ← hE0def] at hphys
    have hHtr : (U * Matrix.diagonal (fun i => (E i : ℂ)) * Uᴴ).trace = 0 :=
      trace_eq_zero_of_mem_pauliChainSpan hHspan
    have hVtr : V.trace = 0 := trace_eq_zero_of_mem_pauliSiteSpan hVspan
    have hNP : (Fintype.card S : ℂ)
        = (Fintype.card (FiniteQubitConfiguration (Fin (m + 1))) : ℂ) := by
      have h1 : (Uᴴ * U).trace = (U * Uᴴ).trace := Matrix.trace_mul_comm Uᴴ U
      rw [hUleft, hUright, Matrix.trace_one, Matrix.trace_one] at h1
      exact h1
    have htrace : ((Fintype.card (FiniteQubitConfiguration (Fin (m + 1))) : ℕ) : ℂ) *
        (((r false : ℝ) : ℂ) + ((r true : ℝ) : ℂ)) = ∑ i, ((E0 i : ℝ) : ℂ) := by
      have hc := congrArg Matrix.trace hphys
      simp only [physicalLeafHamiltonian, Matrix.trace_add, trace_layerMatrixCoupling,
        Matrix.trace_one, Matrix.trace_diagonal, hHtr, hVtr, zero_mul, zero_add, add_zero,
        trace_unitary_conj_diagonal hBleft, hp1, Fintype.sum_bool] at hc
      linear_combination hc
    have htraceR : ((Fintype.card (FiniteQubitConfiguration (Fin (m + 1))) : ℕ) : ℝ) *
        (r false + r true) = ∑ i, E0 i := by exact_mod_cast htrace
    have hNPne : ((Fintype.card (FiniteQubitConfiguration (Fin (m + 1))) : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero (α := FiniteQubitConfiguration (Fin (m + 1)))
    have hcardSB : ((Fintype.card (S × Bool) : ℕ) : ℝ)
        = 2 * ((Fintype.card (FiniteQubitConfiguration (Fin (m + 1))) : ℕ) : ℝ) := by
      have hSR : ((Fintype.card S : ℕ) : ℝ)
          = ((Fintype.card (FiniteQubitConfiguration (Fin (m + 1))) : ℕ) : ℝ) := by
        exact_mod_cast hNP
      rw [Fintype.card_prod, Fintype.card_bool]
      push_cast
      rw [hSR]
      ring
    have hcs : ∑ i, E0 i
        = 2 * ((Fintype.card (FiniteQubitConfiguration (Fin (m + 1))) : ℕ) : ℝ) * cs := by
      rw [hcsdef, ← hcardSB]
      field_simp
    have hrsum : r false + r true = 2 * cs := by
      refine mul_left_cancel₀ hNPne ?_
      rw [htraceR, hcs]; ring
    have hshift : (fun b => (realLocalExtensionParameter
        (localExtensionSliceParameter q)).1 b - ((cs : ℝ) : ℂ))
        = boolShift (((2 * (r false - cs) : ℝ) : ℂ)) := by
      funext b
      rw [hp1]
      have hr2 : (r true : ℝ) = 2 * cs - r false := by linarith
      cases b
      · simp only [boolShift, Bool.false_eq_true, if_false]
        push_cast
        ring
      · simp only [boolShift, if_true]
        rw [hr2]
        push_cast
        ring
    have hD : Matrix.diagonal (fun i => ((recentredEnergy E0 i : ℝ) : ℂ))
        = Matrix.diagonal (fun i => ((E0 i : ℝ) : ℂ))
          - ((cs : ℝ) : ℂ) • (1 : Matrix (S × Bool) (S × Bool) ℂ) := by
      ext x y
      by_cases h : x = y
      · subst h
        simp only [Matrix.diagonal_apply_eq, Matrix.sub_apply, Matrix.smul_apply,
          Matrix.one_apply_eq, smul_eq_mul, mul_one, recentredEnergy, hcsdef]
        push_cast
        ring
      · simp [Matrix.sub_apply, Matrix.one_apply_ne h, h]
    have hcore : B * Matrix.diagonal (fun i => ((recentredEnergy E0 i : ℝ) : ℂ)) * Bᴴ
        = physicalLeafHamiltonian (U * Matrix.diagonal (fun i => (E i : ℂ)) * Uᴴ) V
            (boolShift (((2 * (r false - cs) : ℝ) : ℂ)))
            (realLocalExtensionParameter (localExtensionSliceParameter q)).2 := by
      rw [hD, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one,
        Matrix.smul_mul, hBright, ← hphys, ← hshift,
        physicalLeafHamiltonian_sub_smul_one]
    have hgoal : (B.submatrix (snocConfig (m + 1)).symm ⇑(Equiv.refl (S × Bool))) *
          Matrix.diagonal (fun i => ((recentredEnergy E0 i : ℝ) : ℂ)) *
          (B.submatrix (snocConfig (m + 1)).symm ⇑(Equiv.refl (S × Bool)))ᴴ
        = Matrix.reindex (snocConfig (m + 1)) (snocConfig (m + 1))
            (B * Matrix.diagonal (fun i => ((recentredEnergy E0 i : ℝ) : ℂ)) * Bᴴ) := rfl
    rw [hgoal, hcore]
    exact physicalLeaf_mem_pauliChainSpan hHspan hVspan _ hedge
  · intro a b hab
    have hone : Uᴴ * (1 : Matrix (FiniteQubitConfiguration (Fin (m + 1)))
        (FiniteQubitConfiguration (Fin (m + 1))) ℂ) * U = (1 : Matrix S S ℂ) := by
      rw [Matrix.mul_one]; exact hUleft
    have hstep : (B.submatrix (snocConfig (m + 1)).symm ⇑(Equiv.refl (S × Bool)))ᴴ *
          Matrix.reindex (snocConfig (m + 1)) (snocConfig (m + 1))
            (layerMatrixCoupling (1 : Matrix (FiniteQubitConfiguration (Fin (m + 1)))
              (FiniteQubitConfiguration (Fin (m + 1))) ℂ) Xt) *
          (B.submatrix (snocConfig (m + 1)).symm ⇑(Equiv.refl (S × Bool)))
        = Bᴴ * layerMatrixCoupling (1 : Matrix (FiniteQubitConfiguration (Fin (m + 1)))
            (FiniteQubitConfiguration (Fin (m + 1))) ℂ) Xt * B := by
      rw [Matrix.conjTranspose_submatrix, Matrix.reindex_apply,
        Matrix.submatrix_mul_equiv Bᴴ (layerMatrixCoupling (1 : Matrix
          (FiniteQubitConfiguration (Fin (m + 1))) (FiniteQubitConfiguration (Fin (m + 1))) ℂ) Xt)
          ⇑(Equiv.refl (S × Bool)) (snocConfig (m + 1)).symm (snocConfig (m + 1)).symm,
        Matrix.submatrix_mul_equiv (Bᴴ * layerMatrixCoupling (1 : Matrix
          (FiniteQubitConfiguration (Fin (m + 1))) (FiniteQubitConfiguration (Fin (m + 1))) ℂ) Xt) B
          ⇑(Equiv.refl (S × Bool)) (snocConfig (m + 1)).symm ⇑(Equiv.refl (S × Bool))]
      simp
    rw [hstep, hBdef, physicalLeafSpectralBasis, Matrix.conjTranspose_mul]
    rw [show (C.unitaryEigenvectorMatrix hH e)ᴴ *
        (tensorIdentityBasis (ρ := Bool) U)ᴴ *
        layerMatrixCoupling (1 : Matrix (FiniteQubitConfiguration (Fin (m + 1)))
          (FiniteQubitConfiguration (Fin (m + 1))) ℂ) Xt *
        (tensorIdentityBasis (ρ := Bool) U * C.unitaryEigenvectorMatrix hH e)
        = (C.unitaryEigenvectorMatrix hH e)ᴴ *
          ((tensorIdentityBasis (ρ := Bool) U)ᴴ *
            layerMatrixCoupling (1 : Matrix (FiniteQubitConfiguration (Fin (m + 1)))
              (FiniteQubitConfiguration (Fin (m + 1))) ℂ) Xt *
            tensorIdentityBasis (ρ := Bool) U) * C.unitaryEigenvectorMatrix hH e by
      simp only [Matrix.mul_assoc]]
    rw [tensorIdentityBasis_coordinate_layer U _ (1 : Matrix S S ℂ) Xt hone]
    have hsplit : layerMatrixCoupling (1 : Matrix S S ℂ) Xt
        = layerMatrixCoupling (1 : Matrix S S ℂ) X
          - ((X.trace.re / 2 : ℝ) : ℂ) • (1 : Matrix (S × Bool) (S × Bool) ℂ) := by
      rw [hXtdef]
      ext x y
      simp only [layerMatrixCoupling, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
        smul_eq_mul, Prod.ext_iff]
      by_cases h1 : x.1 = y.1 <;> by_cases h2 : x.2 = y.2 <;> simp [h1, h2]
    rw [hsplit, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one,
      Matrix.smul_mul]
    rw [show (C.unitaryEigenvectorMatrix hH e)ᴴ * C.unitaryEigenvectorMatrix hH e
        = (1 : Matrix (S × Bool) (S × Bool) ℂ) from hWleft]
    rw [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_ne hab, smul_zero, sub_zero]
    have := hXfull a b hab
    rw [LocalExtensionEigenbranchChart.unitaryProbeMatrix, Matrix.star_eq_conjTranspose] at this
    exact this


end GaloisForLFunctions.HTGeometry

end
