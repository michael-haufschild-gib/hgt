import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.IntegerPolynomialGrading
import Mathlib.Algebra.MvPolynomial.Eval

/-! Commuting degree-one maps give an action of a multivariate polynomial ring on a graded sum. -/

noncomputable section

open DirectSum MvPolynomial
open scoped IsMulCommutative

namespace GlobalTheory

/-- A polynomial-linear map preserves the indicated degree pieces. -/
def IsGradedMap {ι R M N : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] [Module (MvPolynomial ι R) M] [Module (MvPolynomial ι R) N]
    (D : ℤ → Submodule R M) (E : ℤ → Submodule R N) (f : M →ₗ[MvPolynomial ι R] N) : Prop :=
  ∀ ⦃n : ℤ⦄ ⦃m : M⦄, m ∈ D n → f m ∈ E n

/-- Project onto a homogeneous component and include it back into the module. -/
def gradedProj {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (D : ℤ → Submodule R M) [Decomposition D] (n : ℤ) : M →ₗ[R] M :=
  (D n).subtype ∘ₗ DirectSum.component R ℤ (fun j => D j) n ∘ₗ
    (DirectSum.decomposeLinearEquiv D).toLinearMap

theorem gradedProj_of_mem {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (D : ℤ → Submodule R M) [Decomposition D] {n : ℤ} {m : M} (hm : m ∈ D n) :
    gradedProj D n m = m :=
  DirectSum.decompose_of_mem_same D hm

theorem gradedProj_of_mem_ne {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (D : ℤ → Submodule R M) [Decomposition D] {n j : ℤ} {m : M} (hm : m ∈ D n) (h : n ≠ j) :
    gradedProj D j m = 0 :=
  DirectSum.decompose_of_mem_ne D hm h

private theorem gradedIsInternal {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (D : ℤ → Submodule R M)
    (h₁ : ∀ (T : Finset ℤ) (v : ℤ → M), (∀ j ∈ T, v j ∈ D j) → ∑ j ∈ T, v j = 0 →
      ∀ j ∈ T, v j = 0) (h₂ : ∀ m, m ∈ ⨆ j, D j) : IsInternal D :=
  (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top D).2
    ⟨(iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero D).2 h₁, eq_top_iff.2 fun m _ => h₂ m⟩

section Family

variable {ι : Type*} {R : Type*} [CommRing R]
  {A : ℤ → Type*} [∀ n, AddCommGroup (A n)] [∀ n, Module R (A n)]
  {B : ℤ → Type*} [∀ n, AddCommGroup (B n)] [∀ n, Module R (B n)]

def OperatorsCommute (x : ι → ∀ n, A n →ₗ[R] A (n + 1)) : Prop :=
  ∀ (i j : ι) (n : ℤ) (a : A n), x i (n + 1) (x j n a) = x j (n + 1) (x i n a)

/-- The direct sum carrying the polynomial action determined by the degree-one maps. -/
def GrSum {x : ι → ∀ n, A n →ₗ[R] A (n + 1)} (_hx : OperatorsCommute x) : Type _ :=
  ⨁ n, A n

namespace GrSum

variable {x : ι → ∀ n, A n →ₗ[R] A (n + 1)} (hx : OperatorsCommute x)
  {y : ι → ∀ n, B n →ₗ[R] B (n + 1)} (hy : OperatorsCommute y)

instance : AddCommGroup (GrSum hx) := inferInstanceAs (AddCommGroup (⨁ n, A n))

instance : Module R (GrSum hx) := inferInstanceAs (Module R (⨁ n, A n))

def equivDirectSum : GrSum hx ≃ₗ[R] ⨁ n, A n := LinearEquiv.refl R _

def of (n : ℤ) : A n →ₗ[R] GrSum hx := DirectSum.lof R ℤ A n

def component (n : ℤ) : GrSum hx →ₗ[R] A n := DirectSum.component R ℤ A n

@[simp]
theorem component_of (n : ℤ) (a : A n) : component hx n (of hx n a) = a :=
  DirectSum.component.lof_self R n a

theorem component_of_ne {n k : ℤ} (h : k ≠ n) (a : A k) : component hx n (of hx k a) = 0 :=
  (DirectSum.component.of R n k a).trans (dif_neg h)

theorem of_injective (n : ℤ) : Function.Injective (of hx n) :=
  Function.LeftInverse.injective (component_of hx n)

theorem lhom_ext {N : Type*} [AddCommGroup N] [Module R N] {f g : GrSum hx →ₗ[R] N}
    (h : ∀ n a, f (of hx n a) = g (of hx n a)) : f = g :=
  DirectSum.linearMap_ext R fun n => LinearMap.ext (h n)

def desc {N : Type*} [AddCommGroup N] [Module R N] (φ : ∀ n, A n →ₗ[R] N) : GrSum hx →ₗ[R] N :=
  DirectSum.toModule R ℤ N φ

@[simp]
theorem desc_of {N : Type*} [AddCommGroup N] [Module R N] (φ : ∀ n, A n →ₗ[R] N) (n : ℤ)
    (a : A n) : desc hx φ (of hx n a) = φ n a :=
  DirectSum.toModule_lof R n a

def op (i : ι) : Module.End R (GrSum hx) := desc hx fun n => of hx (n + 1) ∘ₗ x i n

@[simp]
theorem op_of (i : ι) (n : ℤ) (a : A n) : op hx i (of hx n a) = of hx (n + 1) (x i n a) :=
  desc_of hx _ n a

theorem commute_op (i j : ι) : Commute (op hx i) (op hx j) :=
  lhom_ext hx fun n a => by simp [hx i j n a]

private def evalOperators : MvPolynomial ι R →ₐ[R] Module.End R (GrSum hx) := by
  let C := Algebra.adjoin R (Set.range (op hx))
  haveI : IsMulCommutative C := Algebra.isMulCommutative_adjoin R (by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact commute_op hx i j)
  exact C.val.comp (MvPolynomial.aeval fun i => ⟨op hx i, Algebra.subset_adjoin ⟨i, rfl⟩⟩)

private theorem evalOperators_X (i : ι) :
    evalOperators hx (X i) = op hx i := by
  simp [evalOperators]

instance : Module (MvPolynomial ι R) (GrSum hx) :=
  Module.compHom (GrSum hx) (evalOperators hx).toRingHom

theorem smul_def (p : MvPolynomial ι R) (m : GrSum hx) :
    p • m = evalOperators hx p m := rfl

instance : IsScalarTower R (MvPolynomial ι R) (GrSum hx) where
  smul_assoc r p m := by rw [smul_def, smul_def, map_smul]; rfl

theorem X_smul (i : ι) (m : GrSum hx) : (X i : MvPolynomial ι R) • m = op hx i m := by
  rw [smul_def, evalOperators_X]

@[simp]
theorem X_smul_of (i : ι) (n : ℤ) (a : A n) :
    (X i : MvPolynomial ι R) • of hx n a = of hx (n + 1) (x i n a) := by
  rw [X_smul, op_of]

def grading : ℤ → Submodule R (GrSum hx) := fun n => LinearMap.range (of hx n)

theorem mem_grading {n : ℤ} {m : GrSum hx} : m ∈ grading hx n ↔ ∃ a, of hx n a = m := Iff.rfl

theorem of_mem_grading (n : ℤ) (a : A n) : of hx n a ∈ grading hx n := ⟨a, rfl⟩

def pieceEquiv (n : ℤ) : A n ≃ₗ[R] grading hx n := LinearEquiv.ofInjective _ (of_injective hx n)

@[simp]
theorem coe_pieceEquiv (n : ℤ) (a : A n) : (pieceEquiv hx n a : GrSum hx) = of hx n a := rfl

instance : PolyGradedSMul ι (grading hx) :=
  polyGradedSMul_of_X_smul_mem _ (by
    rintro i n _ ⟨a, rfl⟩
    exact ⟨_, (X_smul_of hx i n a).symm⟩)

instance : Decomposition (grading hx) :=
  IsInternal.chooseDecomposition _ <| gradedIsInternal _
    (fun T v hv h j hj => by
      choose! a ha using fun i hi => (mem_grading hx).1 (hv i hi)
      have := congrArg (component hx j) h
      rw [← Finset.sum_congr rfl ha, map_sum, Finset.sum_eq_single j
        (fun i _ e => component_of_ne hx e _) (fun e => absurd hj e), component_of,
        map_zero] at this
      rw [← ha j hj, this, map_zero])
    fun m => by
      induction m using DirectSum.induction_on with
      | zero => exact zero_mem _
      | of n a => exact Submodule.mem_iSup_of_mem n ⟨a, rfl⟩
      | add a b ha hb => exact add_mem ha hb

theorem proj_grading (n : ℤ) (m : GrSum hx) :
    gradedProj (grading hx) n m = of hx n (component hx n m) := by
  have : gradedProj (grading hx) n = of hx n ∘ₗ component hx n := lhom_ext hx fun k a => by
    by_cases h : k = n
    · subst h
      simp [gradedProj_of_mem _ (of_mem_grading hx k a)]
    · simp [gradedProj_of_mem_ne _ (of_mem_grading hx k a) h, component_of_ne hx h]
  exact congr($this m)

variable {N : Type*} [AddCommGroup N] [Module R N] [Module (MvPolynomial ι R) N]
  [IsScalarTower R (MvPolynomial ι R) N]

def lift (φ : ∀ n, A n →ₗ[R] N)
    (hφ : ∀ i n a, φ (n + 1) (x i n a) = (X i : MvPolynomial ι R) • φ n a) :
    GrSum hx →ₗ[MvPolynomial ι R] N where
  toFun := desc hx φ
  map_add' := map_add _
  map_smul' p m := by
    have hX (i : ι) (m : GrSum hx) :
        desc hx φ ((X i : MvPolynomial ι R) • m) = (X i : MvPolynomial ι R) • desc hx φ m := by
      let x₁ := (LinearMap.lsmul (MvPolynomial ι R) (GrSum hx) (X i)).restrictScalars R
      let x₂ := (LinearMap.lsmul (MvPolynomial ι R) N (X i)).restrictScalars R
      have e : desc hx φ ∘ₗ x₁ = x₂ ∘ₗ desc hx φ :=
        lhom_ext hx fun n a => by
          change desc hx φ ((X i : MvPolynomial ι R) • of hx n a) =
            (X i : MvPolynomial ι R) • desc hx φ (of hx n a)
          rw [X_smul_of, desc_of, desc_of, hφ]
      exact LinearMap.congr_fun e m
    rw [RingHom.id_apply]
    induction p using MvPolynomial.induction_on generalizing m with
    | C a => rw [← MvPolynomial.algebraMap_eq, algebraMap_smul, algebraMap_smul, map_smul]
    | add p q hp hq => rw [add_smul, add_smul, map_add, hp, hq]
    | mul_X p i hp =>
      rw [mul_smul, mul_smul, hp]
      exact congrArg (p • ·) (hX i m)

@[simp]
theorem lift_of (φ : ∀ n, A n →ₗ[R] N) (hφ) (n : ℤ) (a : A n) :
    lift hx φ hφ (of hx n a) = φ n a := desc_of hx φ n a

theorem isGradedMap_lift (φ : ∀ n, A n →ₗ[R] N) (hφ) (𝒩 : ℤ → Submodule R N)
    (h : ∀ n a, φ n a ∈ 𝒩 n) : IsGradedMap (grading hx) 𝒩 (lift hx φ hφ) := by
  rintro n _ ⟨a, rfl⟩
  rw [lift_of]
  exact h n a

def map (φ : ∀ n, A n →ₗ[R] B n) (hφ : ∀ i n a, φ (n + 1) (x i n a) = y i n (φ n a)) :
    GrSum hx →ₗ[MvPolynomial ι R] GrSum hy :=
  lift hx (fun n => of hy n ∘ₗ φ n) fun i n a => by simp [hφ]

@[simp]
theorem map_of (φ : ∀ n, A n →ₗ[R] B n) (hφ) (n : ℤ) (a : A n) :
    map hx hy φ hφ (of hx n a) = of hy n (φ n a) := lift_of hx _ _ n a

theorem isGradedMap_map (φ : ∀ n, A n →ₗ[R] B n) (hφ) :
    IsGradedMap (grading hx) (grading hy) (map hx hy φ hφ) :=
  isGradedMap_lift hx _ _ _ fun n _ => of_mem_grading hy n _

end GrSum

end Family

end GlobalTheory
