import Mathlib.RingTheory.Smooth.Fiber
import Mathlib.RingTheory.Discriminant

open scoped TensorProduct

namespace Algebra

universe u v

theorem traceForm_nondegenerate_of_algEquiv
    {K A B : Type*} [Field K] [CommRing A] [CommRing B]
    [Algebra K A] [Algebra K B]
    [Module.Free K A] [Module.Free K B]
    [Module.Finite K A] [Module.Finite K B]
    (e : A ≃ₐ[K] B) (hB : (traceForm K B).Nondegenerate) :
    (traceForm K A).Nondegenerate := by
  constructor
  · intro x hx
    apply e.injective
    rw [map_zero]
    apply hB.1 (e x)
    intro y
    obtain ⟨y, rfl⟩ := e.surjective y
    rw [traceForm_apply, ← map_mul, trace_eq_of_algEquiv]
    exact hx y
  · intro y hy
    apply e.injective
    rw [map_zero]
    apply hB.2 (e y)
    intro x
    obtain ⟨x, rfl⟩ := e.surjective x
    rw [traceForm_apply, ← map_mul, trace_eq_of_algEquiv]
    exact hy x

theorem traceForm_nondegenerate_prod
    {K A B : Type*} [Field K] [CommRing A] [CommRing B]
    [Algebra K A] [Algebra K B]
    [Module.Free K A] [Module.Free K B]
    [Module.Finite K A] [Module.Finite K B]
    (hA : (traceForm K A).Nondegenerate)
    (hB : (traceForm K B).Nondegenerate) :
    (traceForm K (A × B)).Nondegenerate := by
  constructor
  · intro x hx
    apply Prod.ext
    · apply hA.1 x.1
      intro y
      have h := hx (y, 0)
      simpa [traceForm_apply, trace_prod_apply] using h
    · apply hB.1 x.2
      intro y
      have h := hx (0, y)
      simpa [traceForm_apply, trace_prod_apply] using h
  · intro y hy
    apply Prod.ext
    · apply hA.2 y.1
      intro x
      have h := hy (x, 0)
      simpa [traceForm_apply, trace_prod_apply] using h
    · apply hB.2 y.2
      intro x
      have h := hy (0, x)
      simpa [traceForm_apply, trace_prod_apply] using h

noncomputable def piOptionAlgEquivProd
    {K I : Type*} [CommRing K]
    (A : Option I → Type*) [∀ i, Semiring (A i)] [∀ i, Algebra K (A i)] :
    (∀ i, A i) ≃ₐ[K] A none × (∀ i : I, A (some i)) :=
  AlgEquiv.ofRingEquiv (f := RingEquiv.piOptionEquivProd) (by
    intro x
    ext i <;> rfl)

theorem traceForm_nondegenerate_pi_fields
    (K : Type u) [Field K] :
    ∀ (I : Type v) [Finite I] (A : I → Type v)
      [∀ i, Field (A i)] [∀ i, Algebra K (A i)]
      [∀ i, Module.Finite K (A i)] [∀ i, Algebra.IsSeparable K (A i)],
      (traceForm K (∀ i, A i)).Nondegenerate := by
  intro I hI A _ _ _ _
  let P : Type v → Prop := fun J =>
    ∀ (_ : Finite J) (A : J → Type v)
      [∀ i, Field (A i)] [∀ i, Algebra K (A i)]
      [∀ i, Module.Finite K (A i)] [∀ i, Algebra.IsSeparable K (A i)],
      (traceForm K (∀ i, A i)).Nondegenerate
  apply (Finite.induction_empty_option (P := P) (α := I) ?_ ?_ ?_) hI A
  · intro α β e hα hβ A _ _ _ _
    letI : Finite β := hβ
    let hαfin : Finite α := Finite.of_equiv β e.symm
    letI : Finite α := hαfin
    let eA : (∀ i : β, A i) ≃ₐ[K] (∀ j : α, A (e j)) :=
      (AlgEquiv.piCongrLeft K A e).symm
    exact traceForm_nondegenerate_of_algEquiv eA
      (hα hαfin (fun j => A (e j)))
  · intro _ A _ _ _ _
    constructor <;> intro x hx <;> exact Subsingleton.elim _ _
  · intro α _ hα hopt A _ _ _ _
    letI : Finite (Option α) := hopt
    apply traceForm_nondegenerate_of_algEquiv (piOptionAlgEquivProd A)
    exact traceForm_nondegenerate_prod
      (traceForm_nondegenerate K (A none))
      (hα inferInstance (fun i => A (some i)))

theorem traceForm_nondegenerate_of_formallyUnramified_field
    (K A : Type*) [Field K] [CommRing A] [Algebra K A]
    [Module.Free K A] [Module.Finite K A]
    [Algebra.FormallyUnramified K A] :
    (traceForm K A).Nondegenerate := by
  letI : Algebra.FinitePresentation K A := by
    rw [← Algebra.FinitePresentation.of_finiteType]
    infer_instance
  letI : Algebra.Etale K A := Algebra.Etale.of_formallyUnramified_of_flat
  obtain ⟨I, hI, Ai, hAiField, hAiAlg, e, hAi⟩ :=
    Algebra.Etale.iff_exists_algEquiv_prod K A |>.mp inferInstance
  letI : Finite I := hI
  letI (i : I) : Field (Ai i) := hAiField i
  letI (i : I) : Algebra K (Ai i) := hAiAlg i
  letI (i : I) : Module.Finite K (Ai i) := (hAi i).1
  letI (i : I) : Algebra.IsSeparable K (Ai i) := (hAi i).2
  exact traceForm_nondegenerate_of_algEquiv e
    (traceForm_nondegenerate_pi_fields K I Ai)

theorem trace_baseChange_apply
    {R B A : Type*} [CommRing R] [CommRing B] [CommRing A]
    [Algebra R B] [Algebra R A] [Module.Free R B] [Module.Finite R B]
    (x : B) :
    trace A (A ⊗[R] B) (1 ⊗ₜ[R] x) = algebraMap R A (trace R B x) := by
  change LinearMap.trace A (A ⊗[R] B)
      (Algebra.lmul A (A ⊗[R] B) (1 ⊗ₜ[R] x)) =
    algebraMap R A (LinearMap.trace R B (Algebra.lmul R B x))
  rw [← Algebra.baseChange_lmul, LinearMap.trace_baseChange]

theorem traceMatrix_baseChange
    {R B A : Type*} [CommRing R] [CommRing B] [CommRing A]
    [Algebra R B] [Algebra R A] [Module.Free R B] [Module.Finite R B]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι R B) :
    traceMatrix A (b.baseChange A) =
      (algebraMap R A).mapMatrix (traceMatrix R b) := by
  ext i j
  simp [traceMatrix_apply, traceForm_apply, trace_baseChange_apply,
    Module.Basis.baseChange_apply, TensorProduct.tmul_mul_tmul]

theorem isUnit_discr_of_formallyUnramified
    {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]
    [Module.Free R B] [Module.Finite R B]
    [Algebra.FormallyUnramified R B]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι R B) : IsUnit (discr R b) := by
  by_contra hunit
  have hspan : Ideal.span ({discr R b} : Set R) ≠ ⊤ :=
    Ideal.span_singleton_ne_top hunit
  obtain ⟨m, hm, hle⟩ := Ideal.ne_top_iff_exists_maximal.mp hspan
  let k := R ⧸ m
  letI : Field k := Ideal.Quotient.field m
  have hdmem : discr R b ∈ m := hle (Ideal.subset_span (Set.mem_singleton _))
  have hdzero : algebraMap R k (discr R b) = 0 := by
    change Ideal.Quotient.mk m (discr R b) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hdmem
  have hnd : (traceForm k (k ⊗[R] B)).Nondegenerate :=
    traceForm_nondegenerate_of_formallyUnramified_field k (k ⊗[R] B)
  have hdet : (traceMatrix k (b.baseChange k)).det ≠ 0 := by
    rw [traceMatrix_of_basis]
    exact (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero (b.baseChange k)).mp hnd
  apply hdet
  rw [traceMatrix_baseChange, ← RingHom.map_det, ← discr_def, hdzero]

noncomputable def traceDualVector
    {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι R B) (i : ι) : B :=
  ∑ j, (traceMatrix R b)⁻¹ i j • b j

theorem trace_traceDualVector_mul_basis
    {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]
    [Module.Free R B] [Module.Finite R B]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι R B) (h : IsUnit (discr R b)) (i j : ι) :
    trace R B (traceDualVector b i * b j) = if i = j then 1 else 0 := by
  rw [traceDualVector, Finset.sum_mul, map_sum]
  simp only [smul_mul_assoc, map_smul, smul_eq_mul]
  change (∑ x, (traceMatrix R b)⁻¹ i x * traceMatrix R b x j) = _
  rw [← Matrix.mul_apply, Matrix.nonsing_inv_mul _ (by simpa [discr_def] using h),
    Matrix.one_apply]

theorem basis_repr_eq_trace_traceDualVector_mul
    {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]
    [Module.Free R B] [Module.Finite R B]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι R B) (h : IsUnit (discr R b)) (x : B) (i : ι) :
    b.repr x i = trace R B (traceDualVector b i * x) := by
  nth_rw 2 [← b.sum_repr x]
  rw [Finset.mul_sum, map_sum]
  simp only [mul_smul_comm, map_smul, smul_eq_mul,
    trace_traceDualVector_mul_basis b h]
  simp

noncomputable def traceSeparabilityElem
    {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι R B) : B ⊗[R] B :=
  ∑ i, traceDualVector b i ⊗ₜ[R] b i

theorem traceSeparabilityElem_comm
    {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]
    [Module.Free R B] [Module.Finite R B]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι R B) (h : IsUnit (discr R b)) (s : B) :
    (1 ⊗ₜ[R] s) * traceSeparabilityElem b =
      (s ⊗ₜ[R] 1) * traceSeparabilityElem b := by
  apply (b.tensorProduct b).repr.injective
  ext ij
  rcases ij with ⟨i, j⟩
  simp only [traceSeparabilityElem, Finset.mul_sum, map_sum,
    TensorProduct.tmul_mul_tmul, one_mul]
  change Finsupp.lapply (R := R) (i, j)
      (∑ x, (b.tensorProduct b).repr
        (traceDualVector b x ⊗ₜ[R] (s * b x))) =
    Finsupp.lapply (R := R) (i, j)
      (∑ x, (b.tensorProduct b).repr
        ((s * traceDualVector b x) ⊗ₜ[R] b x))
  rw [map_sum, map_sum]
  change (∑ x, (b.tensorProduct b).repr
      (traceDualVector b x ⊗ₜ[R] (s * b x)) (i, j)) =
    ∑ x, (b.tensorProduct b).repr
      ((s * traceDualVector b x) ⊗ₜ[R] b x) (i, j)
  simp_rw [Module.Basis.tensorProduct_repr_tmul_apply]
  simp only [smul_eq_mul]
  simp_rw [basis_repr_eq_trace_traceDualVector_mul b h]
  have hc (x : ι) :
      trace R B (traceDualVector b i * traceDualVector b x) =
        b.repr (traceDualVector b i) x := by
    rw [mul_comm]
    exact (basis_repr_eq_trace_traceDualVector_mul b h _ _).symm
  simp_rw [hc]
  simp_rw [trace_traceDualVector_mul_basis b h]
  simp only [ite_mul, one_mul, zero_mul]
  have hleft :
      (∑ x, trace R B (traceDualVector b j * (s * b x)) *
        b.repr (traceDualVector b i) x) =
      trace R B (traceDualVector b j * (s * traceDualVector b i)) := by
    nth_rw 2 [← b.sum_repr (traceDualVector b i)]
    rw [Finset.mul_sum, Finset.mul_sum, map_sum]
    simp only [mul_smul_comm, map_smul, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro x hx
    ring
  rw [hleft]
  simp
  congr 1
  ring

theorem traceSeparabilityElem_lmul_eq_one
    {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]
    [Module.Free R B] [Module.Finite R B]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι R B) (h : IsUnit (discr R b)) :
    Algebra.TensorProduct.lmul' R (traceSeparabilityElem b) = 1 := by
  let z := Algebra.TensorProduct.lmul' R (traceSeparabilityElem b)
  have hz (x : B) : trace R B (z * x) = trace R B x := by
    calc
      trace R B (z * x) =
          ∑ i, trace R B (traceDualVector b i * b i * x) := by
        simp [z, traceSeparabilityElem, Finset.sum_mul, map_sum,
          Algebra.TensorProduct.lmul'_apply_tmul]
      _ = ∑ i, b.repr (x * b i) i := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [basis_repr_eq_trace_traceDualVector_mul b h]
        congr 1
        ring
      _ = trace R B x := by
        rw [Algebra.trace_eq_matrix_trace b]
        simp [Matrix.trace, Algebra.leftMulMatrix_apply,
          LinearMap.toMatrix_apply]
  change z = 1
  apply b.repr.injective
  ext i
  rw [basis_repr_eq_trace_traceDualVector_mul b h,
    basis_repr_eq_trace_traceDualVector_mul b h]
  simpa only [mul_one, mul_comm] using hz (traceDualVector b i)

theorem formallyUnramified_of_isUnit_discr
    {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]
    [Module.Free R B] [Module.Finite R B]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι R B) (h : IsUnit (discr R b)) :
    Algebra.FormallyUnramified R B := by
  rw [Algebra.FormallyUnramified.iff_exists_tensorProduct]
  refine ⟨traceSeparabilityElem b, ?_, traceSeparabilityElem_lmul_eq_one b h⟩
  intro s
  rw [sub_mul, sub_eq_zero]
  exact traceSeparabilityElem_comm b h s

end Algebra
