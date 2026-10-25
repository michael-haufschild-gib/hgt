import GaloisForLFunctions.HTGeometry.MatrixPrincipalSymbolAbelianSpectrum
import GaloisForLFunctions.HTGeometry.DerivInvariantSuperspace
import GaloisForLFunctions.HTGeometry.FinrankIndependentSup

/-!
# Joint characters and multiplicities of finite commutative algebra actions

Common generalized eigenspaces give finitely many algebra characters.
They exhaust the module independently, and their dimensions sum to its
dimension. Every character vanishing on the action kernel occurs.
-/

section

noncomputable section
set_option autoImplicit false

namespace GaloisForLFunctions.HTGeometry

variable {A V : Type*} [CommRing A] [Algebra ℂ A]
  [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- The common maximal generalized eigenspace of an algebra action. -/
def algebraJointSpace (f : A →ₐ[ℂ] Module.End ℂ V) (χ : A → ℂ) : Submodule ℂ V :=
  ⨅ a : A, (f a).maxGenEigenspace (χ a)

omit [FiniteDimensional ℂ V] in
theorem algebraAction_commute (f : A →ₐ[ℂ] Module.End ℂ V) (a b : A) :
    Commute (f a) (f b) := by
  change f a * f b = f b * f a
  rw [← map_mul, ← map_mul, mul_comm]

omit [FiniteDimensional ℂ V] in
theorem algebraJointSpace_mapsTo (f : A →ₐ[ℂ] Module.End ℂ V)
    (χ : A → ℂ) (a : A) :
    Set.MapsTo (f a) (algebraJointSpace f χ) (algebraJointSpace f χ) := by
  intro x hx
  change x ∈ algebraJointSpace f χ at hx
  change f a x ∈ algebraJointSpace f χ
  simp only [algebraJointSpace, Submodule.mem_iInf] at hx ⊢
  intro b
  exact Module.End.mapsTo_maxGenEigenspace_of_comm (algebraAction_commute f b a) (χ b)
    (hx b)

omit [FiniteDimensional ℂ V] in
/-- An eigenvector in a maximal generalized eigenspace has its prescribed eigenvalue. -/
theorem eigenvalue_eq_of_mem_maxGenEigenspace (T : Module.End ℂ V)
    {α β : ℂ} {x : V} (hx : x ≠ 0)
    (hgen : x ∈ T.maxGenEigenspace β) (heig : T x = α • x) : α = β := by
  by_contra hab
  have hzero : x ∈ (⊥ : Submodule ℂ V) := by
    rw [← (T.disjoint_genEigenspace hab ⊤ ⊤).eq_bot]
    exact ⟨Module.End.eigenspace_le_maxGenEigenspace
      (Module.End.mem_eigenspace_iff.mpr heig), hgen⟩
  exact hx ((Submodule.mem_bot (R := ℂ)).mp hzero)

/-- Multiplication of the action forces multiplication of every nonzero joint character. -/
theorem algebraJointSpace_character_mul (f : A →ₐ[ℂ] Module.End ℂ V)
    (χ : A → ℂ) (hne : algebraJointSpace f χ ≠ ⊥) (a b : A) :
    χ (a * b) = χ a * χ b := by
  let J := algebraJointSpace f χ
  letI : Nontrivial J := Submodule.nontrivial_iff_ne_bot.mpr hne
  let S : Module.End ℂ J := (f a).restrict (algebraJointSpace_mapsTo f χ a)
  let T : Module.End ℂ J := (f b).restrict (algebraJointSpace_mapsTo f χ b)
  have hcomm (x : J) : S (T x) = T (S x) := by
    apply Subtype.ext
    change f a (f b (x : V)) = f b (f a (x : V))
    exact LinearMap.congr_fun (algebraAction_commute f a b).eq x
  obtain ⟨x, α, β, hx, ha, hb⟩ := exists_common_eigenvector S T hcomm
  have hxV : (x : V) ≠ 0 := fun h => hx (Subtype.ext h)
  have haV : f a (x : V) = α • (x : V) := congrArg Subtype.val ha
  have hbV : f b (x : V) = β • (x : V) := congrArg Subtype.val hb
  have hxJ (c : A) : (x : V) ∈ (f c).maxGenEigenspace (χ c) :=
    ((Submodule.mem_iInf _).mp x.property) c
  have hα : α = χ a := eigenvalue_eq_of_mem_maxGenEigenspace (f a) hxV (hxJ a) haV
  have hβ : β = χ b := eigenvalue_eq_of_mem_maxGenEigenspace (f b) hxV (hxJ b) hbV
  have hab : f (a * b) (x : V) = (χ a * χ b) • (x : V) := by
    rw [map_mul]
    change f a (f b (x : V)) = _
    rw [hbV, map_smul, haV, smul_smul, hα, hβ, mul_comm]
  exact (eigenvalue_eq_of_mem_maxGenEigenspace (f (a * b)) hxV (hxJ (a * b)) hab).symm

omit [FiniteDimensional ℂ V] in
theorem algebraJointSpace_character_one (f : A →ₐ[ℂ] Module.End ℂ V)
    (χ : A → ℂ) (hne : algebraJointSpace f χ ≠ ⊥) : χ 1 = 1 := by
  obtain ⟨x, hxJ, hx⟩ := (Submodule.ne_bot_iff _).mp hne
  have hx1 := ((Submodule.mem_iInf _).mp hxJ) (1 : A)
  exact (eigenvalue_eq_of_mem_maxGenEigenspace (f 1) hx hx1 (by simp)).symm

/-- Every nonzero joint spectral sector determines a unital complex algebra character. -/
def algebraJointCharacter (f : A →ₐ[ℂ] Module.End ℂ V)
    (χ : A → ℂ) (hne : algebraJointSpace f χ ≠ ⊥) : A →ₐ[ℂ] ℂ :=
  { jointGeneralizedEigencharacterLinearMap f.toLinearMap χ hne (algebraAction_commute f) with
    map_zero' := (jointGeneralizedEigencharacterLinearMap f.toLinearMap χ hne
      (algebraAction_commute f)).map_zero
    map_one' := algebraJointSpace_character_one f χ hne
    map_mul' := algebraJointSpace_character_mul f χ hne
    commutes' := fun z => by
      have h := (jointGeneralizedEigencharacterLinearMap f.toLinearMap χ hne
        (algebraAction_commute f)).map_smul z (1 : A)
      change χ ((algebraMap ℂ A) z) = (algebraMap ℂ ℂ) z
      simpa only [jointGeneralizedEigencharacterLinearMap_apply,
        Algebra.smul_def, mul_one, algebraJointSpace_character_one f χ hne,
        smul_eq_mul] using h }

theorem algebraJointCharacter_apply (f : A →ₐ[ℂ] Module.End ℂ V)
    (χ : A → ℂ) (hne : algebraJointSpace f χ ≠ ⊥) (a : A) :
    algebraJointCharacter f χ hne a = χ a := rfl

omit [FiniteDimensional ℂ V] in
/-- Joint generalized sectors of a commutative action are independent. -/
theorem algebraJointSpace_iSupIndep (f : A →ₐ[ℂ] Module.End ℂ V) :
    iSupIndep (algebraJointSpace f) := by
  apply Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo
  intro a b μ
  exact Module.End.mapsTo_maxGenEigenspace_of_comm (algebraAction_commute f b a) μ

/-- The joint sectors exhaust every finite complex module of a commutative algebra. -/
theorem algebraJointSpace_iSup_eq_top (f : A →ₐ[ℂ] Module.End ℂ V) :
    ⨆ χ : A → ℂ, algebraJointSpace f χ = ⊤ := by
  apply Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute
  · intro a b _
    exact algebraAction_commute f a b
  · intro a
    exact Module.End.iSup_maxGenEigenspace_eq_top (f a)

/-- Only finitely many joint sectors are nonzero. -/
@[reducible]
def algebraJointCharacterFintype (f : A →ₐ[ℂ] Module.End ℂ V) :
    Fintype {χ : A → ℂ // algebraJointSpace f χ ≠ ⊥} :=
  (algebraJointSpace_iSupIndep f).fintypeNeBotOfFiniteDimensional

/-- The nonzero joint sectors still exhaust the module. -/
theorem algebraJointSpace_nonzero_iSup_eq_top (f : A →ₐ[ℂ] Module.End ℂ V) :
    ⨆ χ : {χ : A → ℂ // algebraJointSpace f χ ≠ ⊥}, algebraJointSpace f χ.val = ⊤ := by
  apply le_antisymm le_top
  rw [← algebraJointSpace_iSup_eq_top f]
  apply iSup_le
  intro χ
  by_cases hχ : algebraJointSpace f χ = ⊥
  · rw [hχ]
    exact bot_le
  · exact le_iSup (fun ψ : {χ : A → ℂ // algebraJointSpace f χ ≠ ⊥} =>
      algebraJointSpace f ψ.val) ⟨χ, hχ⟩

/-- Finite dimension is the sum of the positive joint spectral multiplicities. -/
theorem finrank_eq_sum_algebraJointSpace (f : A →ₐ[ℂ] Module.End ℂ V) :
    letI := algebraJointCharacterFintype f
    Module.finrank ℂ V =
      ∑ χ : {χ : A → ℂ // algebraJointSpace f χ ≠ ⊥},
        Module.finrank ℂ (algebraJointSpace f χ.val) := by
  classical
  letI := algebraJointCharacterFintype f
  have hind : iSupIndep (fun χ : {χ : A → ℂ // algebraJointSpace f χ ≠ ⊥} =>
      algebraJointSpace f χ.val) :=
    (algebraJointSpace_iSupIndep f).comp Subtype.val_injective
  have h := finrank_finset_sup_of_iSupIndep
    (fun χ : {χ : A → ℂ // algebraJointSpace f χ ≠ ⊥} => algebraJointSpace f χ.val)
    hind Finset.univ
  have hsup : Finset.univ.sup (fun χ : {χ : A → ℂ // algebraJointSpace f χ ≠ ⊥} =>
      algebraJointSpace f χ.val) = (⊤ : Submodule ℂ V) := by
    rw [Finset.sup_eq_iSup]
    simpa only [Finset.mem_univ, iSup_pos] using algebraJointSpace_nonzero_iSup_eq_top f
  rw [hsup] at h
  simpa using h

theorem algebraJointSpace_finrank_pos (f : A →ₐ[ℂ] Module.End ℂ V)
    (χ : {χ : A → ℂ // algebraJointSpace f χ ≠ ⊥}) :
    0 < Module.finrank ℂ (algebraJointSpace f χ.val) := by
  letI : Nontrivial (algebraJointSpace f χ.val) :=
    Submodule.nontrivial_iff_ne_bot.mpr χ.property
  exact Module.finrank_pos

/-- A joint character vanishes on the full action kernel. -/
theorem algebraJointCharacter_eq_zero_of_map_eq_zero (f : A →ₐ[ℂ] Module.End ℂ V)
    (χ : A → ℂ) (hne : algebraJointSpace f χ ≠ ⊥) {a : A} (ha : f a = 0) :
    algebraJointCharacter f χ hne a = 0 := by
  obtain ⟨x, hxJ, hx⟩ := (Submodule.ne_bot_iff _).mp hne
  have hgen := ((Submodule.mem_iInf _).mp hxJ) a
  exact (eigenvalue_eq_of_mem_maxGenEigenspace (f a) hx hgen (by simp [ha])).symm

/-- Every character annihilating a finite action kernel is one of its joint spectral characters. -/
theorem character_eq_some_algebraJointCharacter (f : A →ₐ[ℂ] Module.End ℂ V)
    (φ : A →ₐ[ℂ] ℂ) (hφ : ∀ a, f a = 0 → φ a = 0) :
    ∃ χ : {χ : A → ℂ // algebraJointSpace f χ ≠ ⊥}, ∀ a, φ a = χ.val a := by
  classical
  letI := algebraJointCharacterFintype f
  by_contra hnone
  have hsep (χ : {χ : A → ℂ // algebraJointSpace f χ ≠ ⊥}) :
      ∃ a : A, φ a ≠ χ.val a := by
    by_contra h
    push Not at h
    exact hnone ⟨χ, h⟩
  choose a ha using hsep
  let c (χ : {χ : A → ℂ // algebraJointSpace f χ ≠ ⊥}) : A :=
    (a χ - algebraMap ℂ A (χ.val (a χ))) ^ Module.finrank ℂ V
  let b : A := ∏ χ : {χ : A → ℂ // algebraJointSpace f χ ≠ ⊥}, c χ
  have hkill (χ : {χ : A → ℂ // algebraJointSpace f χ ≠ ⊥})
      (x : V) (hx : x ∈ algebraJointSpace f χ.val) : f (c χ) x = 0 := by
    have hx' := ((Submodule.mem_iInf _).mp hx) (a χ)
    rw [Module.End.maxGenEigenspace_eq_genEigenspace_finrank,
      Module.End.genEigenspace_nat, LinearMap.mem_ker] at hx'
    change ((f (a χ) - χ.val (a χ) • (1 : Module.End ℂ V)) ^
      Module.finrank ℂ V) x = 0 at hx'
    change (f ((a χ - algebraMap ℂ A (χ.val (a χ))) ^ Module.finrank ℂ V)) x = 0
    rw [map_pow, map_sub, f.commutes, Algebra.algebraMap_eq_smul_one]
    exact hx'
  have hker : (⊤ : Submodule ℂ V) ≤ LinearMap.ker (f b) := by
    rw [← algebraJointSpace_nonzero_iSup_eq_top f]
    apply iSup_le
    intro χ x hx
    obtain ⟨d, hd⟩ : c χ ∣ b := Finset.dvd_prod_of_mem c (Finset.mem_univ χ)
    change f b x = 0
    rw [hd, mul_comm (c χ) d, map_mul]
    change f d (f (c χ) x) = 0
    rw [hkill χ x hx, map_zero]
  have hfb : f b = 0 := by
    ext x
    exact hker (show x ∈ (⊤ : Submodule ℂ V) from trivial)
  have hφb : φ b ≠ 0 := by
    dsimp only [b]
    rw [map_prod]
    apply Finset.prod_ne_zero_iff.mpr
    intro χ _
    dsimp only [c]
    rw [map_pow, map_sub, φ.commutes]
    exact pow_ne_zero _ (sub_ne_zero.mpr (ha χ))
  exact hφb (hφ b hfb)

end GaloisForLFunctions.HTGeometry

#print axioms GaloisForLFunctions.HTGeometry.algebraJointCharacter
#print axioms GaloisForLFunctions.HTGeometry.algebraJointSpace_iSup_eq_top
#print axioms GaloisForLFunctions.HTGeometry.finrank_eq_sum_algebraJointSpace
#print axioms GaloisForLFunctions.HTGeometry.character_eq_some_algebraJointCharacter
end
end
