import GaloisForLFunctions.WindowedLandauTheory.SharpRestriction.LevelLetterCocycles.DataN

/-! A matrix representation with the same traces as an irreducible one
has full matrix image. The trace pairing detects the kernel of the group algebra action. -/

noncomputable section
open Matrix WindowedLandauTheory.CyclotomicNorms
open scoped MonoidAlgebra Classical

namespace GlobalTheory.BrauerNesbittIrr

variable {K G V : Type} [Field K] [Group G]
variable [AddCommGroup V] [Module K V] [FiniteDimensional K V]

private theorem asAlgebraHom_surjective [IsAlgClosed K] (τ : Representation K G V)
    (hτ : τ.IsIrreducible) : Function.Surjective τ.asAlgebraHom := by
  letI := hτ
  have hscal (φ : Module.End K[G] τ.asModule) : ∃ c : K, ∀ m, φ m = c • m := by
    obtain ⟨c, hc⟩ := (IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed
      (A := K[G]) (V := τ.asModule) K).2 φ
    exact ⟨c, fun m => by rw [← hc]; rfl⟩
  intro f
  let F : Module.End (Module.End K[G] τ.asModule) τ.asModule :=
    { toFun := fun m => τ.asModuleEquiv.symm (f (τ.asModuleEquiv m))
      map_add' := fun x y => by simp
      map_smul' := fun φ m => by
        obtain ⟨c, hc⟩ := hscal φ
        simp only [Module.End.smul_def, RingHom.id_apply, hc, map_smul] }
  let b := Module.finBasis K V
  obtain ⟨r, hr⟩ := jacobson_density F (Finset.univ.image fun i => τ.asModuleEquiv.symm (b i))
  refine ⟨r, b.ext fun i => ?_⟩
  exact (congrArg τ.asModuleEquiv (hr _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))).symm

variable {n : ℕ}

private def matrixRepresentation (ρ : G →* GL (Fin n) K) : Representation K G (Fin n → K) :=
  Matrix.toLinAlgEquiv'.toAlgHom.toMonoidHom.comp ((Units.coeHom _).comp ρ)

private def matrixLift (ρ : G →* GL (Fin n) K) : K[G] →ₐ[K] Matrix (Fin n) (Fin n) K :=
  LinearMap.toMatrixAlgEquiv'.toAlgHom.comp (matrixRepresentation ρ).asAlgebraHom

private theorem matrixLift_single (ρ : G →* GL (Fin n) K) (g : G) (c : K) :
    matrixLift ρ (MonoidAlgebra.single g c) = c • (ρ g : Matrix (Fin n) (Fin n) K) := by
  rw [matrixLift, AlgHom.comp_apply, Representation.asAlgebraHom_single, map_smul]
  exact congrArg (c • ·) (LinearMap.toMatrixAlgEquiv'_toLinAlgEquiv' (ρ g).val)

private theorem matrixLift_mulVec_mem (ρ : G →* GL (Fin n) K) (W : Submodule K (Fin n → K))
    (hW : ∀ g, ∀ x ∈ W, (ρ g : Matrix (Fin n) (Fin n) K) *ᵥ x ∈ W)
    (a : K[G]) (x : Fin n → K) (hx : x ∈ W) : matrixLift ρ a *ᵥ x ∈ W := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simpa only [map_zero, zero_mulVec] using W.zero_mem
  | add b c hb hc =>
    rw [map_add, add_mulVec]
    exact W.add_mem hb hc
  | single g c =>
    rw [matrixLift_single, Matrix.smul_mulVec]
    exact W.smul_mem c (hW g x hx)

private theorem matrixLift_surjective [IsAlgClosed K] [Nonempty (Fin n)]
    (ρ : G →* GL (Fin n) K)
    (hρ : ∀ W : Submodule K (Fin n → K), (∀ g, ∀ x ∈ W, (ρ g : Matrix (Fin n) (Fin n) K) *ᵥ x ∈ W) →
      W = ⊥ ∨ W = ⊤) :
    Function.Surjective (matrixLift ρ) := by
  let τ := matrixRepresentation ρ
  letI : Nontrivial (Subrepresentation τ) :=
    ⟨⟨⊥, ⊤, fun h => bot_ne_top (congrArg Subrepresentation.toSubmodule h)⟩⟩
  have hτ : τ.IsIrreducible := by
    refine ⟨fun W => ?_⟩
    rcases hρ W.toSubmodule (fun g x hx => W.apply_mem_toSubmodule g hx) with h | h
    · exact Or.inl (Subrepresentation.toSubmodule_injective h)
    · exact Or.inr (Subrepresentation.toSubmodule_injective h)
  exact LinearMap.toMatrixAlgEquiv'.surjective.comp (asAlgebraHom_surjective τ hτ)

/-- Equality of traces transfers irreducibility in fixed dimension over an algebraically closed field. -/
theorem irred_of_trace_eq [IsAlgClosed K] (ρ ρ' : G →* GL (Fin n) K)
    (ht : ∀ g, (ρ g : Matrix (Fin n) (Fin n) K).trace = (ρ' g : Matrix (Fin n) (Fin n) K).trace)
    (hρ' : ∀ W : Submodule K (Fin n → K), (∀ g, ∀ x ∈ W, (ρ' g : Matrix (Fin n) (Fin n) K) *ᵥ x ∈ W) →
      W = ⊥ ∨ W = ⊤)
    (W : Submodule K (Fin n → K)) (hW : ∀ g, ∀ x ∈ W, (ρ g : Matrix (Fin n) (Fin n) K) *ᵥ x ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  by_cases hbot : W = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra! h
    exact hx0 (funext h)
  letI : Nonempty (Fin n) := ⟨i⟩
  have hs := matrixLift_surjective ρ' hρ'
  have htrace (a : K[G]) : (matrixLift ρ a).trace = (matrixLift ρ' a).trace := by
    induction a using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [map_add, trace_add, ha, hb]
    | single g c => simp only [matrixLift_single, trace_smul, ht]
  let F := (matrixLift ρ).toLinearMap
  let Q := (matrixLift ρ').toLinearMap
  have hker : LinearMap.ker F ≤ LinearMap.ker Q := by
    intro a ha
    have hFa : matrixLift ρ a = 0 := LinearMap.mem_ker.mp ha
    apply LinearMap.mem_ker.mpr
    change matrixLift ρ' a = 0
    apply Matrix.ext_iff_trace_mul_right.mpr
    intro A
    obtain ⟨b, rfl⟩ := hs A
    rw [← map_mul, ← htrace (a * b), map_mul, hFa, zero_mul, zero_mul]
  let q := (LinearMap.ker F).liftQ Q hker
  letI : FiniteDimensional K (K[G] ⧸ LinearMap.ker F) :=
    LinearEquiv.finiteDimensional F.quotKerEquivRange.symm
  have hrange : LinearMap.range Q = ⊤ := LinearMap.range_eq_top.mpr hs
  have hdim := LinearMap.finrank_range_le q
  rw [Submodule.range_liftQ, hrange, finrank_top, F.quotKerEquivRange.finrank_eq] at hdim
  have hF : Function.Surjective F := LinearMap.range_eq_top.mp
    (Submodule.eq_top_of_finrank_eq ((Submodule.finrank_le _).antisymm hdim))
  apply top_unique
  intro y _
  let A := Matrix.vecMulVec y (Pi.single i (x i)⁻¹)
  have hA : A *ᵥ x = y := by
    change Matrix.vecMulVec y (Pi.single i (x i)⁻¹) *ᵥ x = y
    rw [Matrix.vecMulVec_mulVec, single_dotProduct, inv_mul_cancel₀ hi, MulOpposite.op_one, one_smul]
  obtain ⟨a, ha⟩ := hF A
  have hy := matrixLift_mulVec_mem ρ W hW a x hx
  change matrixLift ρ a = A at ha
  rwa [ha, hA] at hy

/-- The Brauer–Nesbitt irreducibility criterion follows by comparing the trace coefficients. -/
theorem irredOn_top_of_charpoly_eq {l : ℕ} [Fact l.Prime]
    (ρ ρ' : G →* GL (Fin n) (Fbar l))
    (hc : ∀ g, (ρ g : Matrix (Fin n) (Fin n) (Fbar l)).charpoly =
      (ρ' g : Matrix (Fin n) (Fin n) (Fbar l)).charpoly)
    (hρ' : IrredOn ρ' ⊤) : IrredOn ρ ⊤ := by
  intro W hW
  refine irred_of_trace_eq ρ ρ' (fun g => ?_)
    (fun U hU => hρ' U fun g _ x hx => hU g x hx) W (fun g x hx => hW g (Subgroup.mem_top g) x hx)
  rw [Matrix.trace_eq_neg_charpoly_nextCoeff, Matrix.trace_eq_neg_charpoly_nextCoeff, hc]

end GlobalTheory.BrauerNesbittIrr
