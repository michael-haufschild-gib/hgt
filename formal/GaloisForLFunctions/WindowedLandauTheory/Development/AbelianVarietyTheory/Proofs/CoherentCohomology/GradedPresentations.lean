import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.GradedPolynomialAction
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Submodule
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! Homogeneous kernels, quotients, and finite free presentations. -/

noncomputable section

open DirectSum MvPolynomial

namespace GlobalTheory

section Projections

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N]
  [Module R M] [Module R N] (D : ℤ → Submodule R M) (E : ℤ → Submodule R N)
  [Decomposition D] [Decomposition E]

theorem gradedProj_mem (n : ℤ) (m : M) : gradedProj D n m ∈ D n :=
  (decompose D m n).2

theorem sum_support_gradedProj (m : M) [∀ n (x : D n), Decidable (x ≠ 0)] :
    ∑ n ∈ (decompose D m).support, gradedProj D n m = m :=
  sum_support_decompose D m

theorem gradedProj_sum (T : Finset ℤ) (v : ℤ → M) (hv : ∀ j ∈ T, v j ∈ D j)
    {n : ℤ} (hn : n ∈ T) : gradedProj D n (∑ j ∈ T, v j) = v n := by
  rw [map_sum, Finset.sum_eq_single n (fun j hj h => gradedProj_of_mem_ne D (hv j hj) h)
    (fun h => absurd hn h), gradedProj_of_mem D (hv n hn)]

/-- A linear map of degree `d` commutes with projection after shifting the degree. -/
theorem gradedProj_map_add (f : M →ₗ[R] N) (d : ℤ)
    (hf : ∀ ⦃n : ℤ⦄ ⦃m : M⦄, m ∈ D n → f m ∈ E (n + d)) (n : ℤ) (m : M) :
    gradedProj E (n + d) (f m) = f (gradedProj D n m) := by
  induction m using Decomposition.inductionOn D with
  | zero => simp only [map_zero]
  | add a b ha hb => simp only [map_add, ha, hb]
  | @homogeneous j a =>
    by_cases h : j = n
    · subst j
      rw [gradedProj_of_mem E (hf a.2), gradedProj_of_mem D a.2]
    · rw [gradedProj_of_mem_ne E (hf a.2) (by omega), gradedProj_of_mem_ne D a.2 h, map_zero]

end Projections

section Modules

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N]
  [Module R M] [Module R N] [Module (MvPolynomial ι R) M] [Module (MvPolynomial ι R) N]
  [IsScalarTower R (MvPolynomial ι R) M] [IsScalarTower R (MvPolynomial ι R) N]
  {D : ℤ → Submodule R M} {E : ℤ → Submodule R N}

theorem IsGradedMap.proj_apply [Decomposition D] [Decomposition E]
    {f : M →ₗ[MvPolynomial ι R] N} (hf : IsGradedMap D E f) (n : ℤ) (m : M) :
    gradedProj E n (f m) = f (gradedProj D n m) := by
  simpa only [add_zero, LinearMap.restrictScalars_apply] using
    gradedProj_map_add D E (f.restrictScalars R) 0 (by
      intro j x hx
      change f x ∈ E (j + 0)
      simpa only [add_zero] using hf hx) n m

theorem IsGradedMap.isHomogeneous_ker [Decomposition D] [Decomposition E]
    {f : M →ₗ[MvPolynomial ι R] N} (hf : IsGradedMap D E f) :
    (LinearMap.ker f).IsHomogeneous D := fun n m hm => by
  change f (gradedProj D n m) = 0
  rw [← hf.proj_apply, LinearMap.mem_ker.1 hm, map_zero]

theorem IsGradedMap.isHomogeneous_range [Decomposition D] [Decomposition E]
    {f : M →ₗ[MvPolynomial ι R] N} (hf : IsGradedMap D E f) :
    (LinearMap.range f).IsHomogeneous E := by
  rintro n _ ⟨m, rfl⟩
  exact ⟨gradedProj D n m, (hf.proj_apply n m).symm⟩

theorem proj_smul_of_mem [Decomposition D] [PolyGradedSMul ι D]
    {p : MvPolynomial ι R} {d : ℤ} (hp : p ∈ polyGrading ι R d) (n : ℤ) (m : M) :
    gradedProj D (n + d) (p • m) = p • gradedProj D n m :=
  gradedProj_map_add D D ((LinearMap.lsmul (MvPolynomial ι R) M p).restrictScalars R)
    d (by
      intro j x hx
      exact grSMul_mem D hp hx) n m

theorem proj_smul_of_mem_right [Decomposition D] [PolyGradedSMul ι D]
    (p : MvPolynomial ι R) {d : ℤ} {m : M} (hm : m ∈ D d) (n : ℤ) :
    gradedProj D n (p • m) = gradedProj (polyGrading ι R) (n - d) p • m := by
  simpa only [sub_add_cancel, LinearMap.restrictScalars_apply, LinearMap.toSpanSingleton_apply] using
    gradedProj_map_add (polyGrading ι R) D
      ((LinearMap.toSpanSingleton (MvPolynomial ι R) M m).restrictScalars R)
      d (by
        intro j q hq
        change q • m ∈ D (j + d)
        simpa only [add_comm d j] using grSMul_mem D hq hm) (n - d) p

theorem isHomogeneous_span_gr [Decomposition D] [PolyGradedSMul ι D]
    {G : Set M} (hG : ∀ g ∈ G, ∃ d, g ∈ D d) :
    (Submodule.span (MvPolynomial ι R) G).IsHomogeneous D := by
  intro n m hm
  change gradedProj D n m ∈ _
  obtain ⟨c, _, rfl⟩ := (Finsupp.mem_span_iff_linearCombination _ _ _).1 hm
  rw [Finsupp.linearCombination_apply, Finsupp.sum, map_sum]
  refine Submodule.sum_mem _ fun g _ => ?_
  obtain ⟨d, hd⟩ := hG g g.2
  rw [proj_smul_of_mem_right _ hd]
  exact Submodule.smul_mem _ _ (Submodule.subset_span g.2)

/-- The degree pieces on a submodule are preimages of the ambient degree pieces. -/
def grSub (D : ℤ → Submodule R M) (K : Submodule (MvPolynomial ι R) M) :
    ℤ → Submodule R K := fun n => (D n).comap (K.subtype.restrictScalars R)

/-- The degree pieces on a quotient are images of the ambient degree pieces. -/
def grQuot (D : ℤ → Submodule R M) (K : Submodule (MvPolynomial ι R) M) :
    ℤ → Submodule R (M ⧸ K) := fun n => (D n).map (K.mkQ.restrictScalars R)

@[simp]
theorem mem_grSub {K : Submodule (MvPolynomial ι R) M} {n : ℤ} {m : K} :
    m ∈ grSub D K n ↔ (m : M) ∈ D n := Iff.rfl

theorem mem_grQuot {K : Submodule (MvPolynomial ι R) M} {n : ℤ} {y : M ⧸ K} :
    y ∈ grQuot D K n ↔ ∃ m ∈ D n, K.mkQ m = y := Iff.rfl

instance grSub.polyGradedSMul [PolyGradedSMul ι D] (K : Submodule (MvPolynomial ι R) M) :
    PolyGradedSMul ι (grSub D K) where
  smul_mem _ _ _ _ hp hm := SetLike.GradedSMul.smul_mem (B := D) hp hm

instance grQuot.polyGradedSMul [PolyGradedSMul ι D] (K : Submodule (MvPolynomial ι R) M) :
    PolyGradedSMul ι (grQuot D K) where
  smul_mem := by
    rintro d n p _ hp ⟨m, hm, rfl⟩
    exact ⟨p • m, SetLike.GradedSMul.smul_mem (B := D) hp hm, map_smul K.mkQ p m⟩

omit [IsScalarTower R (MvPolynomial ι R) N] in
theorem IsGradedMap.liftQ {f : M →ₗ[MvPolynomial ι R] N} (hf : IsGradedMap D E f)
    (K : Submodule (MvPolynomial ι R) M) (h : K ≤ LinearMap.ker f) :
    IsGradedMap (grQuot D K) E (K.liftQ f h) := by
  rintro n _ ⟨m, hm, rfl⟩
  exact hf hm

/-- A homogeneous submodule is the direct sum of its intersections with the degree pieces. -/
@[implicit_reducible]
def grSubDecomposition [Decomposition D] {K : Submodule (MvPolynomial ι R) M}
    (hK : K.IsHomogeneous D) : Decomposition (grSub D K) := by
  classical
  refine (gradedIsInternal _ ?_ ?_).chooseDecomposition _
  · intro T v hv h j hj
    apply Subtype.ext
    have he : (∑ k ∈ T, (v k : M)) = 0 := by
      rw [← Submodule.coe_sum, h, Submodule.coe_zero]
    rw [← gradedProj_sum D T (fun k => (v k : M)) hv hj, he, map_zero]
    rfl
  · intro m
    have he : m = ∑ j ∈ (decompose D (m : M)).support, (⟨gradedProj D j m, hK j m.2⟩ : K) := by
      apply Subtype.ext
      rw [Submodule.coe_sum, sum_support_gradedProj]
    rw [he]
    exact Submodule.sum_mem _ fun j _ => Submodule.mem_iSup_of_mem j (gradedProj_mem D j m)

/-- Taking the quotient by a homogeneous submodule preserves the direct-sum decomposition. -/
@[implicit_reducible]
def grQuotDecomposition [Decomposition D] {K : Submodule (MvPolynomial ι R) M}
    (hK : K.IsHomogeneous D) : Decomposition (grQuot D K) := by
  refine (gradedIsInternal _ ?_ ?_).chooseDecomposition _
  · intro T v hv h j hj
    choose! w hw he using fun k hk => mem_grQuot.1 (hv k hk)
    have hW : ∑ k ∈ T, w k ∈ K := by
      rw [← Submodule.Quotient.mk_eq_zero, ← h]
      change K.mkQ (∑ k ∈ T, w k) = _
      rw [map_sum]
      exact Finset.sum_congr rfl he
    have hjK : gradedProj D j (∑ k ∈ T, w k) ∈ K := hK j hW
    rw [gradedProj_sum D T w hw hj] at hjK
    exact (he j hj).symm.trans ((Submodule.Quotient.mk_eq_zero K).2 hjK)
  · intro y
    obtain ⟨m, rfl⟩ := K.mkQ_surjective y
    induction m using Decomposition.inductionOn D with
    | zero => rw [map_zero]; exact zero_mem _
    | @homogeneous n m => exact Submodule.mem_iSup_of_mem n ⟨m, m.2, rfl⟩
    | add a b ha hb => rw [map_add]; exact add_mem ha hb

end Modules

section Free

variable (ι R : Type*) [CommRing R] {κ : Type*}

/-- The `k`th basis vector of the free polynomial module has degree `d k`. -/
def grFree (d : κ → ℤ) : ℤ → Submodule R (κ → MvPolynomial ι R) :=
  fun n => Submodule.pi Set.univ fun k => polyGrading ι R (n - d k)

variable {ι R}

theorem mem_grFree {d : κ → ℤ} {n : ℤ} {p : κ → MvPolynomial ι R} :
    p ∈ grFree ι R d n ↔ ∀ k, p k ∈ polyGrading ι R (n - d k) := by
  simp only [grFree, Submodule.mem_pi, Set.mem_univ, forall_const]

instance grFree.polyGradedSMul (d : κ → ℤ) : PolyGradedSMul ι (grFree ι R d) where
  smul_mem a n p q hp hq := mem_grFree.2 fun k => by
    have h := SetLike.GradedMul.mul_mem hp (mem_grFree.1 hq k)
    simpa only [vadd_eq_add, Pi.smul_apply, smul_eq_mul, add_sub_assoc] using h

instance grFree.decomposition [Finite κ] (d : κ → ℤ) : Decomposition (grFree ι R d) :=
  IsInternal.chooseDecomposition _ <| gradedIsInternal _
    (fun T v hv h j hj => funext fun k => by
      have he : gradedProj (polyGrading ι R) (j - d k) (∑ i ∈ T, v i k) = v j k := by
        rw [map_sum, Finset.sum_eq_single j
          (fun i hi e => gradedProj_of_mem_ne _ (mem_grFree.1 (hv i hi) k) (by omega))
          (fun e => absurd hj e), gradedProj_of_mem _ (mem_grFree.1 (hv j hj) k)]
      rw [← he, ← Finset.sum_apply, h, Pi.zero_apply, map_zero])
    fun p => by
      classical
      letI := Fintype.ofFinite κ
      rw [← Finset.univ_sum_single p]
      refine Submodule.sum_mem _ fun k _ => ?_
      induction p k using Decomposition.inductionOn (polyGrading ι R) with
      | zero => rw [Pi.single_zero]; exact zero_mem _
      | @homogeneous n x =>
        refine Submodule.mem_iSup_of_mem (n + d k) (mem_grFree.2 fun j => ?_)
        by_cases h : j = k
        · subst j; simpa only [Pi.single_eq_same, add_sub_cancel_right] using x.2
        · rw [Pi.single_eq_of_ne h]; exact zero_mem _
      | add a b ha hb => rw [Pi.single_add]; exact add_mem ha hb

theorem isGradedMap_linearCombination [Fintype κ] {M : Type*} [AddCommGroup M] [Module R M]
    [Module (MvPolynomial ι R) M] [IsScalarTower R (MvPolynomial ι R) M]
    (D : ℤ → Submodule R M) [PolyGradedSMul ι D] {g : κ → M} {d : κ → ℤ}
    (hg : ∀ k, g k ∈ D (d k)) :
    IsGradedMap (grFree ι R d) D (Fintype.linearCombination (MvPolynomial ι R) g) := by
  intro n m hm
  rw [Fintype.linearCombination_apply]
  refine Submodule.sum_mem _ fun k _ => ?_
  simpa only [add_comm (d k) (n - d k), sub_add_cancel] using
    grSMul_mem D (mem_grFree.1 hm k) (hg k)

end Free

end GlobalTheory
