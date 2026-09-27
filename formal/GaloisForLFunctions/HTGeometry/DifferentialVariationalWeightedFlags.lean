import GaloisForLFunctions.HTGeometry.CompletedPseudoDiffOpSlopeDecomposition
import GaloisForLFunctions.HTGeometry.DifferentialVariationalOppositeBoundaryPair

/-!
# The canonical attracting and repelling weighted flags of a variational automorphism

Let `T` be the canonical variational action of a differential field automorphism `σ` on the
completed coordinate space.

* `variationalAttractingSubspace_eq_forwardBoundedSubspace` — the canonical attracting subspace (the
  vectors of non-positive growth rate) is exactly the space of vectors with **bounded** forward orbit.
  Non-positive rate follows from boundedness; conversely the backward-contracting component of a
  slow vector vanishes, because `T⁻¹` contracts a lattice `P` of that component at a linear rate
  `T^{-j} P ⊆ ϖ^{⌊j/m⌋ - b} P`, while slowness keeps `Tⁿ` of the component inside
  `ϖ^{-⌊n/2m⌋ - e} P`; together the component lies in every dilation of `P`.
* The same for the repelling subspace and `T⁻¹`, so the intersection of the two canonical subspaces
  is the slope-zero part, which carries a `T`-fixed lattice.
* `variationalSlopeSubspace σ b s` — the slope parts of `σ`; they are independent, finitely many are
  nonzero, and they span.  The attracting subspace is the sum of the parts of slope `≤ 0`, the
  repelling subspace the sum of the parts of slope `≥ 0`, and at every rational level `s` the
  attracting filtration step `⨁_{t ≤ s}` and the opposite step `⨁_{t > s}` are complementary: the
  attracting and repelling weighted flags of `σ` are opposite.
-/

open Filter

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {C K : Type*} [Field C] [Field K] [Algebra C K] [Differential K]
  [IsConstantBase C K]

attribute [local instance] DiffOp.completedPseudoDiffOpIntegerSMul

theorem two_mul_div_two_mul_le_div (n m : ℕ) (hm : 0 < m) : 2 * (n / (2 * m)) ≤ n / m := by
  rw [Nat.le_div_iff_mul_le hm]
  have := Nat.div_mul_le_self n (2 * m)
  nlinarith

theorem le_div_of_add_mul (N₀ m J : ℕ) (hm : 0 < m) : J ≤ (N₀ + 2 * m * (J + 1)) / (2 * m) := by
  rw [Nat.le_div_iff_mul_le (by omega)]
  nlinarith

/-- **Slow vectors are forward bounded.** -/
theorem mem_forwardBoundedSubspace_of_mem_variationalAttractingCore (σ : DifferentialFieldAut C K)
    {r : ℕ} (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (L : DiffOp.CompletedPseudoDiffOpLattice K (Fin r)) {v : Fin r → DiffOp.CompletedPseudoDiffOp K}
    (hv : v ∈ variationalAttractingCore σ b L) :
    v ∈ DiffOp.forwardBoundedSubspace (σ.vecBuildingActionEquiv b)
      (σ.isUniformizerSemilinear_vecBuildingActionEquiv b) := by
  classical
  have hT := σ.isUniformizerSemilinear_vecBuildingActionEquiv b
  have htop := DiffOp.forwardBoundedSubspace_sup_backwardContractingSubspace_eq_top hT
  have hvsup : v ∈ DiffOp.forwardBoundedSubspace (σ.vecBuildingActionEquiv b) hT ⊔
      DiffOp.backwardContractingSubspace (σ.vecBuildingActionEquiv b) hT := by
    rw [htop]
    trivial
  obtain ⟨β, hβ, γ, hγ, rfl⟩ := Submodule.mem_sup.1 hvsup
  have hγF : γ ∈ variationalAttractingCore σ b L := by
    have hvF : β + γ ∈ variationalAttractingSubspace σ b L := hv
    have hβF : β ∈ variationalAttractingSubspace σ b L :=
      mem_variationalAttractingCore_of_mem_forwardBoundedSubspace σ b L hβ
    have := Submodule.sub_mem _ hvF hβF
    rwa [add_sub_cancel_left] at this
  suffices hγ0 : γ = 0 by
    rw [hγ0, add_zero]
    exact hβ
  -- the contracting lattice of the backward-contracting part
  obtain ⟨P, hPfg, hPspan, m, hm, hcontr⟩ :=
    DiffOp.exists_contracting_lattice_backwardContractingSubspace hT
  obtain ⟨bb, hbb⟩ := DiffOp.exists_inv_pow_le_uniformizerDilate hT hPfg (by
    rw [hPspan]
    exact fun x hx => DiffOp.inv_apply_mem_backwardContractingSubspace hT hx) hm hcontr
  obtain ⟨e, he⟩ := DiffOp.exists_nat_le_uniformizerDilate_of_fg (M := P)
    (L.fg.of_le (inf_le_left : L.carrier ⊓
      (DiffOp.backwardContractingSubspace (σ.vecBuildingActionEquiv b) hT).restrictScalars
        (DiffOp.CompletedPseudoDiffOpInteger (K := K)) ≤ L.carrier)) (by
      rw [hPspan]
      exact fun x hx => hx.2)
  have hslow := Set.mem_iInter.1 hγF (2 * m - 1)
  rw [show 2 * m - 1 + 1 = 2 * m by omega] at hslow
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hslow
  refine DiffOp.eq_zero_of_forall_mem_uniformizerDilate hPfg fun j => ?_
  set n := N₀ + 2 * m * (j + bb + e + 1) with hndef
  have hn := hN₀ n (by omega)
  rw [DiffOp.mem_leftScale_uniformizer_iff, ← DifferentialFieldAut.vecBuildingActionEquiv_pow_apply]
    at hn
  have hTnγ : ((σ.vecBuildingActionEquiv b) ^ n) γ ∈
      DiffOp.backwardContractingSubspace (σ.vecBuildingActionEquiv b) hT :=
    DiffOp.pow_apply_mem_of_forall (fun x hx => DiffOp.apply_mem_backwardContractingSubspace hT hx)
      n γ hγ
  have h1 : ((σ.vecBuildingActionEquiv b) ^ n) γ ∈ DiffOp.uniformizerDilate (-((n / (2 * m) : ℕ) : ℤ))
      (L.carrier ⊓ (DiffOp.backwardContractingSubspace (σ.vecBuildingActionEquiv b) hT).restrictScalars
        (DiffOp.CompletedPseudoDiffOpInteger (K := K))) := by
    rw [DiffOp.uniformizerDilate_inf_restrictScalars]
    refine Submodule.mem_inf.2 ⟨?_, hTnγ⟩
    rw [DiffOp.mem_uniformizerDilate, neg_neg]
    exact hn
  have h2 := DiffOp.uniformizerDilate_mono he h1
  rw [DiffOp.uniformizerDilate_uniformizerDilate] at h2
  have h3 := DiffOp.apply_mem_semilinearImage (hT := hT.inv.pow n) h2
  rw [DiffOp.semilinearImage_uniformizerDilate] at h3
  have h4 := DiffOp.uniformizerDilate_mono (hbb n) h3
  rw [DiffOp.uniformizerDilate_uniformizerDilate] at h4
  have hback : ((σ.vecBuildingActionEquiv b)⁻¹ ^ n) (((σ.vecBuildingActionEquiv b) ^ n) γ) = γ := by
    rw [← LinearEquiv.mul_apply, inv_pow, inv_mul_cancel, LinearEquiv.coe_one, id]
  rw [hback] at h4
  refine DiffOp.uniformizerDilate_antitone P ?_ h4
  have hfl : 2 * (n / (2 * m)) ≤ n / m := two_mul_div_two_mul_le_div n m (by omega)
  have hbig : j + bb + e ≤ n / (2 * m) := le_div_of_add_mul N₀ m (j + bb + e) (by omega)
  have key : (j : ℤ) + bb + e + ((n / (2 * m) : ℕ) : ℤ) ≤ ((n / m : ℕ) : ℤ) := by
    exact_mod_cast (show j + bb + e + n / (2 * m) ≤ n / m by omega)
  linarith

/-- **The attracting subspace is the forward-bounded subspace.** -/
theorem variationalAttractingSubspace_eq_forwardBoundedSubspace (σ : DifferentialFieldAut C K)
    {r : ℕ} (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (L : DiffOp.CompletedPseudoDiffOpLattice K (Fin r)) :
    variationalAttractingSubspace σ b L = DiffOp.forwardBoundedSubspace (σ.vecBuildingActionEquiv b)
      (σ.isUniformizerSemilinear_vecBuildingActionEquiv b) := by
  apply le_antisymm
  · exact fun v hv => mem_forwardBoundedSubspace_of_mem_variationalAttractingCore σ b L hv
  · exact fun v hv => mem_variationalAttractingCore_of_mem_forwardBoundedSubspace σ b L hv

/-- **The repelling subspace is the backward-bounded subspace.** -/
theorem variationalRepellingSubspace_eq_forwardBoundedSubspace_inv (σ : DifferentialFieldAut C K)
    {r : ℕ} (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (L : DiffOp.CompletedPseudoDiffOpLattice K (Fin r)) :
    variationalRepellingSubspace σ b L = DiffOp.forwardBoundedSubspace
      (σ.vecBuildingActionEquiv b)⁻¹ (σ.isUniformizerSemilinear_vecBuildingActionEquiv b).inv := by
  rw [variationalRepellingSubspace, variationalAttractingSubspace_eq_forwardBoundedSubspace]
  exact DiffOp.forwardBoundedSubspace_congr (σ.vecBuildingActionEquiv_inv b).symm _ _

/-- The slope parts of a differential field automorphism: the slope-`s` parts of its canonical
variational action. -/
def variationalSlopeSubspace (σ : DifferentialFieldAut C K) {r : ℕ}
    (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K)) (s : ℚ) :
    Submodule (DiffOp.CompletedPseudoDiffOp K) (Fin r → DiffOp.CompletedPseudoDiffOp K) :=
  DiffOp.slopeSubspace (σ.vecBuildingActionEquiv b) (σ.isUniformizerSemilinear_vecBuildingActionEquiv b) s

section Slopes

variable (σ : DifferentialFieldAut C K) {r : ℕ}
  (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))

/-- The slope parts span. -/
theorem iSup_variationalSlopeSubspace_eq_top : ⨆ s, variationalSlopeSubspace σ b s = ⊤ :=
  DiffOp.iSup_slopeSubspace_eq_top (σ.isUniformizerSemilinear_vecBuildingActionEquiv b)

/-- The slope parts are independent. -/
theorem iSupIndep_variationalSlopeSubspace : iSupIndep (variationalSlopeSubspace σ b) :=
  DiffOp.iSupIndep_slopeSubspace (σ.isUniformizerSemilinear_vecBuildingActionEquiv b)

/-- Only finitely many slopes occur. -/
theorem finite_setOf_variationalSlopeSubspace_ne_bot :
    {s : ℚ | variationalSlopeSubspace σ b s ≠ ⊥}.Finite :=
  DiffOp.finite_setOf_slopeSubspace_ne_bot (σ.isUniformizerSemilinear_vecBuildingActionEquiv b)

theorem slopeAut_zero_one_eq (T : (Fin r → DiffOp.CompletedPseudoDiffOp K) ≃ₗ[ℤ]
    (Fin r → DiffOp.CompletedPseudoDiffOp K)) :
    DiffOp.slopeAut (K := K) T (0 : ℚ).num (0 : ℚ).den = T := by
  ext x
  simp [DiffOp.slopeAut, DiffOp.uniformizerSMulAut_apply]

/-- **The attracting subspace is the sum of the slope parts of slope at most zero.** -/
theorem variationalAttractingSubspace_eq_iSup_slope
    (L : DiffOp.CompletedPseudoDiffOpLattice K (Fin r)) :
    variationalAttractingSubspace σ b L = ⨆ t, ⨆ (_ : t ≤ (0 : ℚ)), variationalSlopeSubspace σ b t := by
  have hT := σ.isUniformizerSemilinear_vecBuildingActionEquiv b
  rw [variationalAttractingSubspace_eq_forwardBoundedSubspace,
    DiffOp.forwardBoundedSubspace_congr (slopeAut_zero_one_eq (σ.vecBuildingActionEquiv b)).symm hT
      (DiffOp.isUniformizerSemilinear_slopeAut hT _ _),
    DiffOp.forwardBoundedSubspace_slopeAut_eq hT 0]
  rfl

/-- **The repelling subspace is the sum of the slope parts of slope at least zero.** -/
theorem variationalRepellingSubspace_eq_iSup_slope
    (L : DiffOp.CompletedPseudoDiffOpLattice K (Fin r)) :
    variationalRepellingSubspace σ b L = ⨆ t, ⨆ (_ : (0 : ℚ) ≤ t), variationalSlopeSubspace σ b t := by
  have hT := σ.isUniformizerSemilinear_vecBuildingActionEquiv b
  rw [variationalRepellingSubspace_eq_forwardBoundedSubspace_inv,
    DiffOp.forwardBoundedSubspace_congr
      (show (σ.vecBuildingActionEquiv b)⁻¹ =
        (DiffOp.slopeAut (K := K) (σ.vecBuildingActionEquiv b) (0 : ℚ).num (0 : ℚ).den)⁻¹ by
          rw [slopeAut_zero_one_eq])
      hT.inv (DiffOp.isUniformizerSemilinear_slopeAut hT _ _).inv,
    DiffOp.forwardBoundedSubspace_inv_slopeAut_eq hT 0]
  rfl

/-- **The two canonical subspaces meet in the slope-zero part.** -/
theorem variationalAttractingSubspace_inf_variationalRepellingSubspace
    (L : DiffOp.CompletedPseudoDiffOpLattice K (Fin r)) :
    variationalAttractingSubspace σ b L ⊓ variationalRepellingSubspace σ b L =
      variationalSlopeSubspace σ b 0 := by
  have hT := σ.isUniformizerSemilinear_vecBuildingActionEquiv b
  rw [variationalAttractingSubspace_eq_forwardBoundedSubspace,
    variationalRepellingSubspace_eq_forwardBoundedSubspace_inv, variationalSlopeSubspace,
    DiffOp.slopeSubspace,
    DiffOp.forwardBoundedSubspace_congr (slopeAut_zero_one_eq (σ.vecBuildingActionEquiv b))
      (DiffOp.isUniformizerSemilinear_slopeAut hT _ _) hT,
    DiffOp.forwardBoundedSubspace_congr
      (show (DiffOp.slopeAut (K := K) (σ.vecBuildingActionEquiv b) (0 : ℚ).num (0 : ℚ).den)⁻¹ =
        (σ.vecBuildingActionEquiv b)⁻¹ by rw [slopeAut_zero_one_eq])
      (DiffOp.isUniformizerSemilinear_slopeAut hT _ _).inv hT.inv]

/-- **The attracting and repelling weighted flags are opposite.**  At every rational level `s` the
attracting filtration step (slopes `≤ s`) and the parts of slope `> s` are complementary. -/
theorem isCompl_variationalSlopeFlag (s : ℚ) :
    IsCompl (⨆ t, ⨆ (_ : t ≤ s), variationalSlopeSubspace σ b t)
      (⨆ t, ⨆ (_ : s < t), variationalSlopeSubspace σ b t) := by
  have hT := σ.isUniformizerSemilinear_vecBuildingActionEquiv b
  have h := DiffOp.isCompl_forwardBoundedSubspace_backwardContractingSubspace
    (DiffOp.isUniformizerSemilinear_slopeAut hT s.num s.den)
  rw [DiffOp.forwardBoundedSubspace_slopeAut_eq hT s,
    DiffOp.backwardContractingSubspace_slopeAut_eq hT s] at h
  exact h

end Slopes

end

end GaloisForLFunctions.HTGeometry
