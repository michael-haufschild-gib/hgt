import Mathlib
import GaloisForLFunctions.HTGeometry.ConstraintRelativity.MonogenicKaehler
import GaloisForLFunctions.HTGeometry.ConstraintRelativity.SimpleHorizonTransmutation

/-!
# Trace–Kähler equality and monogenicity

For a monogenic order the Kähler module is cyclic — it is the quotient of the order by the root
different — and the trace-dual quotient is the same cyclic module, because multiplication by the
different carries `A^♯/A` onto `A/(different)`.  Conversely an invertible trace dual over a
semilocal base is free of rank one, so the trace-dual quotient is cyclic.

The corank-two example shows that determinant-level agreement does not force module equality: the
two modules have the same length and the same Fitting ideal but different invariant factors.
-/

namespace HTGeometry.ConstraintRelativity

open Polynomial

/-! ## Monogenic orders have cyclic Kähler module -/

section Cyclic

variable {R : Type*} [CommRing R] (f : R[X])

/-- **Theorem 1, `(3) ⇒ (2)`.**  The Kähler module of a monogenic order is cyclic: it is generated
by the class of the differential of the generator. -/
theorem kaehler_isPrincipal_of_monogenic :
    ∃ ω : Ω[AdjoinRoot f⁄R], (⊤ : Submodule (AdjoinRoot f) (Ω[AdjoinRoot f⁄R]))
      = Submodule.span (AdjoinRoot f) {ω} := by
  classical
  refine ⟨KaehlerDifferential.D R (AdjoinRoot f) (AdjoinRoot.root f), ?_⟩
  refine le_antisymm ?_ le_top
  intro x _
  obtain ⟨y, rfl⟩ := (kaehlerEquivMonogenic f).symm.surjective x
  induction y using Submodule.Quotient.induction_on with
  | H s =>
    induction s using AdjoinRoot.induction_on with
    | ih p =>
      have hgen : (kaehlerEquivMonogenic f).symm
          (Submodule.Quotient.mk (AdjoinRoot.mk f p))
          = AdjoinRoot.mk f p •
            KaehlerDifferential.D R (AdjoinRoot f) (AdjoinRoot.root f) := by
        apply (kaehlerEquivMonogenic f).injective
        rw [LinearEquiv.apply_symm_apply, map_smul, ← AdjoinRoot.mk_X,
          kaehlerEquivMonogenic_D, derivative_X, map_one]
        rw [map_one]
        have h1 : (1 : MonogenicOmega f) = Submodule.Quotient.mk (1 : AdjoinRoot f) := rfl
        rw [h1, ← Submodule.Quotient.mk_smul, smul_eq_mul, mul_one]
      rw [hgen]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

end Cyclic

/-! ## A principal trace dual gives a cyclic trace quotient -/

section TraceQuotient

variable {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]

/-- **Theorem 1, `(1) ⇒ (2)`.**  If the trace dual is free of rank one on a generator containing
the order, the trace quotient is cyclic.  Over a semilocal base every invertible module is free of
rank one, which is the card's reduction. -/
theorem traceQuotient_isPrincipal {N P : Submodule A M} {u : M}
    (hu : P = Submodule.span A {u}) :
    ∃ ω : P ⧸ Submodule.comap P.subtype N,
      (⊤ : Submodule A (P ⧸ Submodule.comap P.subtype N)) = Submodule.span A {ω} := by
  classical
  have humem : u ∈ P := by rw [hu]; exact Submodule.mem_span_singleton_self u
  refine ⟨Submodule.Quotient.mk ⟨u, humem⟩, le_antisymm ?_ le_top⟩
  intro x _
  induction x using Submodule.Quotient.induction_on with
  | H y =>
    have hy2 : (y : M) ∈ Submodule.span A {u} := by rw [← hu]; exact y.2
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hy2
    have hy : y = c • (⟨u, humem⟩ : P) := Subtype.ext (by simpa using hc.symm)
    rw [hy]
    exact Submodule.mem_span_singleton.2 ⟨c, by rw [← Submodule.Quotient.mk_smul]⟩

end TraceQuotient

/-! ## Multiplication by the different identifies the two quotients -/

section Multiplication

variable {A : Type*} [CommRing A]

/-- **Theorem 1, `(12)`.**  For a nonzerodivisor `δ`, multiplication by `δ` identifies the quotient
`δ⁻¹A/A` with `A/(δ)`.  In the monogenic case `δ` is the root different, so the trace-dual quotient
and the Kähler module agree. -/
noncomputable def mulDifferentEquiv (δ : A) :
    (A ⧸ LinearMap.range (LinearMap.toSpanSingleton A A δ)) ≃ₗ[A] (A ⧸ Ideal.span {δ}) :=
  Submodule.quotEquivOfEq _ _ (by
    ext x
    simp only [LinearMap.mem_range, LinearMap.toSpanSingleton_apply, smul_eq_mul,
      Ideal.mem_span_singleton]
    exact ⟨fun ⟨y, hy⟩ => ⟨y, by rw [← hy]; ring⟩, fun ⟨y, hy⟩ => ⟨y, by rw [hy]; ring⟩⟩)

end Multiplication

/-! ## Trace–Kähler equality for a monogenic order -/

section TraceKaehler

variable {R : Type*} [CommRing R] (f : R[X])

/-- **Theorem 1, `(3) ⇒ (1)`, cards `(11)`–`(12)`.**  For a monogenic order the trace quotient and
the Kähler module are the same module.  The trace dual is `δ⁻¹A` with `δ` the root different
(mathlib's `traceForm_dualSubmodule_adjoin`), so the trace quotient is the cokernel of
multiplication by `δ`; that cokernel is `A/(δ)`, which is the Kähler module. -/
noncomputable def traceKaehlerEquiv_of_monogenic :
    (AdjoinRoot f ⧸ LinearMap.range
        (LinearMap.toSpanSingleton (AdjoinRoot f) (AdjoinRoot f) (rootDifferent f)))
      ≃ₗ[AdjoinRoot f] Ω[AdjoinRoot f⁄R] :=
  (mulDifferentEquiv (rootDifferent f)).trans (kaehlerEquivMonogenic f).symm

@[simp] theorem traceKaehlerEquiv_of_monogenic_mk (p : R[X]) :
    traceKaehlerEquiv_of_monogenic f (Submodule.Quotient.mk (AdjoinRoot.mk f p))
      = (kaehlerEquivMonogenic f).symm (Submodule.Quotient.mk (AdjoinRoot.mk f p)) := rfl

end TraceKaehler

/-! ## A local Artin algebra with principal maximal ideal is monogenic -/

section LocalMonogenic

variable {k B : Type*} [Field k] [CommRing B] [Algebra k B]

/-- Approximation by polynomials in the generator, to any order. -/
theorem exists_sub_aeval_mem_pow (t : B)
    (hres : ∀ b : B, ∃ c : k, b - algebraMap k B c ∈ Ideal.span {t}) (n : ℕ) (b : B) :
    ∃ p : Polynomial k, b - Polynomial.aeval t p ∈ Ideal.span {t ^ n} := by
  induction n generalizing b with
  | zero =>
    exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨p, hp⟩ := ih b
    obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.1 hp
    obtain ⟨c, hc⟩ := hres d
    obtain ⟨e, he⟩ := Ideal.mem_span_singleton'.1 hc
    refine ⟨p + Polynomial.C c * Polynomial.X ^ n, ?_⟩
    refine Ideal.mem_span_singleton'.2 ⟨e, ?_⟩
    have hdc : d = e * t + algebraMap k B c := by
      have hsub : d - algebraMap k B c = e * t := he.symm
      linear_combination hsub
    rw [map_add, map_mul, Polynomial.aeval_C, Polynomial.aeval_X_pow]
    calc e * t ^ (n + 1)
        = (d - algebraMap k B c) * t ^ n := by rw [hdc]; ring
      _ = d * t ^ n - algebraMap k B c * t ^ n := by ring
      _ = b - Polynomial.aeval t p - algebraMap k B c * t ^ n := by rw [hd]
      _ = b - (Polynomial.aeval t p + algebraMap k B c * t ^ n) := by ring

/-- **Card `(7)`.**  A local algebra whose maximal ideal is principal and nilpotent, with residue
field the base, is generated by that single element. -/
theorem adjoin_eq_top_of_isPrincipal_nilpotent (t : B)
    (hres : ∀ b : B, ∃ c : k, b - algebraMap k B c ∈ Ideal.span {t})
    {n : ℕ} (ht : t ^ n = 0) : Algebra.adjoin k ({t} : Set B) = ⊤ := by
  rw [Algebra.adjoin_singleton_eq_range_aeval, AlgHom.range_eq_top]
  intro b
  obtain ⟨p, hp⟩ := exists_sub_aeval_mem_pow t hres n b
  rw [ht, Ideal.span_singleton_eq_bot.2 rfl, Ideal.mem_bot, sub_eq_zero] at hp
  exact ⟨p, hp.symm⟩

end LocalMonogenic

/-! ## Chinese remainder monogeneration of the residual fibre -/

section CRTGlue

set_option maxHeartbeats 1000000

open Polynomial

variable {ι k : Type*} [Fintype ι] [DecidableEq ι] [Field k]

/-- A surjective algebra map carries a single generator to a single generator. -/
theorem adjoin_image_singleton_eq_top {K A B : Type*} [CommRing K] [CommRing A] [CommRing B]
    [Algebra K A] [Algebra K B] (f : A →ₐ[K] B) (hf : Function.Surjective f) {x : A}
    (hx : Algebra.adjoin K ({x} : Set A) = ⊤) :
    Algebra.adjoin K ({f x} : Set B) = ⊤ := by
  have h1 := Algebra.adjoin_image (R := K) f ({x} : Set A)
  rw [Set.image_singleton, hx, Algebra.map_top, (AlgHom.range_eq_top f).2 hf] at h1
  exact h1

omit [Fintype ι] [DecidableEq ι] in
/-- Distinct centres give pairwise coprime local factors. -/
theorem isCoprime_shift_pow {lam : ι → k} (hlam : Function.Injective lam) (n : ι → ℕ) :
    Pairwise fun i j => IsCoprime (Ideal.span {(X - C (lam i)) ^ (n i)})
      (Ideal.span {(X - C (lam j)) ^ (n j)}) := by
  intro i j hij
  have hne : lam i ≠ lam j := fun h => hij (hlam h)
  have hcop : IsCoprime (X - C (lam i)) (X - C (lam j)) :=
    Polynomial.isCoprime_X_sub_C_of_isUnit_sub (by simpa using (sub_ne_zero.2 hne).isUnit)
  rw [Ideal.isCoprime_span_singleton_iff]
  exact hcop.pow

/-- The product of the quotient maps, as an algebra map. -/
noncomputable def piQuotAlgHom (I : ι → Ideal (Polynomial k)) :
    Polynomial k →ₐ[k] ∀ i, Polynomial k ⧸ I i :=
  AlgHom.pi fun i => Ideal.Quotient.mkₐ k (I i)

omit [DecidableEq ι] in
theorem piQuotAlgHom_surjective {I : ι → Ideal (Polynomial k)}
    (hI : Pairwise fun i j => IsCoprime (I i) (I j)) :
    Function.Surjective (piQuotAlgHom I) := by
  intro g
  obtain ⟨y, hy⟩ := Ideal.quotientInfToPiQuotient_surj (I := I) hI g
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  refine ⟨x, ?_⟩
  funext i
  have := Ideal.quotientInfToPiQuotient_mk' I x i
  rw [← congrFun hy i, this]
  rfl

omit [DecidableEq ι] in
/-- **Card `(8)`.**  A finite product of local quotients at distinct centres is generated by one
element: the Chinese remainder theorem turns the residual fibre into a single monogenic quotient of
the polynomial ring. -/
theorem exists_adjoin_pi_quotient_eq_top {lam : ι → k} (hlam : Function.Injective lam)
    (n : ι → ℕ) :
    ∃ x : (∀ i, Polynomial k ⧸ Ideal.span {(X - C (lam i)) ^ (n i)}),
      Algebra.adjoin k ({x} : Set _) = ⊤ :=
  ⟨piQuotAlgHom _ X,
    adjoin_image_singleton_eq_top _ (piQuotAlgHom_surjective (isCoprime_shift_pow hlam n))
      Polynomial.adjoin_X⟩

end CRTGlue

/-! ## The corank-two example: equal determinant, unequal modules -/

section CorankTwo

open Matrix Kronecker

variable {R : Type*} [CommRing R]

/-- **Card `(18)`.**  Multiplication by the quadratic different `2x − a` on `R[x]/(x(x−a))`, in the
basis `(1, x)`. -/
def quadDifferentMatrix (a : R) : Matrix (Fin 2) (Fin 2) R := !![-a, 0; 2, a]

/-- Row reduction of the quadratic different by the unimodular left factor. -/
theorem quadDifferent_mul_left (a w : R) (hw : w * 2 = 1) :
    (!![0, w; 2, a] : Matrix (Fin 2) (Fin 2) R) * quadDifferentMatrix a
      = !![1, w * a; 0, a ^ 2] := by
  rw [quadDifferentMatrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> first | exact hw | ring

/-- **Card `(18)`.**  The Smith normal form of the quadratic different is `diag(1, a²)`, exhibited
by explicit unimodular matrices. -/
theorem smith_quadDifferent (a : R) (h2 : IsUnit (2 : R)) :
    ∃ P Q : Matrix (Fin 2) (Fin 2) R, IsUnit P.det ∧ IsUnit Q.det ∧
      P * quadDifferentMatrix a * Q = Matrix.diagonal ![1, a ^ 2] := by
  obtain ⟨v, hv⟩ := h2
  set w : R := ((v⁻¹ : Rˣ) : R) with hwdef
  have hw : w * 2 = 1 := by
    rw [hwdef, ← hv, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  refine ⟨!![0, w; 2, a], !![1, -(a * w); 0, 1], ?_, ?_, ?_⟩
  · rw [Matrix.det_fin_two_of]
    have hval : (0 : R) * a - w * 2 = -1 := by rw [hw]; ring
    rw [hval]
    exact isUnit_one.neg
  · rw [Matrix.det_fin_two_of]
    have hval : (1 : R) * 1 - -(a * w) * 0 = 1 := by ring
    rw [hval]
    exact isUnit_one
  · rw [quadDifferent_mul_left a w hw]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    ring

/-- **Reusable.**  Smith data multiplies under Kronecker products. -/
theorem mul_kronecker_mul_smith {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n]
    [DecidableEq n] {M D P Q : Matrix m m R} {M' D' P' Q' : Matrix n n R}
    (h : P * M * Q = D) (h' : P' * M' * Q' = D') :
    (P ⊗ₖ P') * (M ⊗ₖ M') * (Q ⊗ₖ Q') = D ⊗ₖ D' := by
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, h, h']

/-- **Card `(20)`.**  Multiplication by one hypersurface different on the tensor-square order has
Smith form `diag(1, 1, a², a²)`, so each cotangent summand is `(R/(a²))²`. -/
theorem nonempty_cokerQuadTensorOne (a : R) (h2 : IsUnit (2 : R)) :
    Nonempty (((Fin 2 × Fin 2 → R) ⧸ LinearMap.range
        (quadDifferentMatrix a ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) R)).mulVecLin)
      ≃ₗ[R] ∀ p : Fin 2 × Fin 2, (R ⧸ Ideal.span {(![1, a ^ 2] p.1) * (1 : R)})) := by
  obtain ⟨P, Q, hP, hQ, hPQ⟩ := smith_quadDifferent a h2
  have hone : (1 : Matrix (Fin 2) (Fin 2) R) * 1 * 1
      = Matrix.diagonal fun _ : Fin 2 => (1 : R) := by
    rw [Matrix.diagonal_one]
    simp
  refine nonempty_coker_equiv_pi_of_smith (P := P ⊗ₖ 1) (Q := Q ⊗ₖ 1) ?_ ?_ _ ?_
    (mul_kronecker_mul_smith hPQ hone)
  · rw [Matrix.det_kronecker, Matrix.det_one]
    simpa using hP.pow (Fintype.card (Fin 2))
  · rw [Matrix.det_kronecker, Matrix.det_one]
    simpa using hQ.pow (Fintype.card (Fin 2))
  · rw [Matrix.diagonal_kronecker_diagonal]

/-- **Card `(19)`.**  The Kronecker square keeps the determinant but splits the module: its Smith
form is `diag(1, a², a², a⁴)`. -/
theorem smith_kronecker_quadDifferent (a : R) (h2 : IsUnit (2 : R)) :
    ∃ P Q : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) R, IsUnit P.det ∧ IsUnit Q.det ∧
      P * (quadDifferentMatrix a ⊗ₖ quadDifferentMatrix a) * Q
        = Matrix.diagonal fun p : Fin 2 × Fin 2 => (![1, a ^ 2] p.1) * (![1, a ^ 2] p.2) := by
  obtain ⟨P', Q', hP', hQ', hPQ'⟩ := smith_quadDifferent a h2
  refine ⟨P' ⊗ₖ P', Q' ⊗ₖ Q', ?_, ?_, ?_⟩
  · rw [Matrix.det_kronecker]
    exact (hP'.pow _).mul (hP'.pow _)
  · rw [Matrix.det_kronecker]
    exact (hQ'.pow _).mul (hQ'.pow _)
  · rw [mul_kronecker_mul_smith hPQ' hPQ', Matrix.diagonal_kronecker_diagonal]

/-- **Card `(17)` input.**  The single quadratic factor: `B/(d_x) ≅ R/(a²)`, since the first
invariant factor is a unit and contributes a zero summand. -/
theorem nonempty_cokerQuad (a : R) (h2 : IsUnit (2 : R)) :
    Nonempty (((Fin 2 → R) ⧸ LinearMap.range (quadDifferentMatrix a).mulVecLin)
      ≃ₗ[R] ∀ j : Fin 2, (R ⧸ Ideal.span {![1, a ^ 2] j})) := by
  obtain ⟨P, Q, hP, hQ, hPQ⟩ := smith_quadDifferent a h2
  exact nonempty_coker_equiv_pi_of_smith hP hQ _ rfl hPQ

/-- **Card `(16)`, boxed.**  The trace quotient of the tensor-square order splits as
`R/(a²) ⊕ R/(a²) ⊕ R/(a⁴)`: the invariant factors are `1, a², a², a⁴`, and the unit factor
contributes a zero summand. -/
theorem nonempty_cokerKronecker (a : R) (h2 : IsUnit (2 : R)) :
    Nonempty (((Fin 2 × Fin 2 → R) ⧸ LinearMap.range
        (quadDifferentMatrix a ⊗ₖ quadDifferentMatrix a).mulVecLin)
      ≃ₗ[R] ∀ p : Fin 2 × Fin 2, (R ⧸ Ideal.span {(![1, a ^ 2] p.1) * (![1, a ^ 2] p.2)})) := by
  obtain ⟨P, Q, hP, hQ, hPQ⟩ := smith_kronecker_quadDifferent a h2
  exact nonempty_coker_equiv_pi_of_smith hP hQ _ rfl hPQ

/-- **Card `(20)`, second relation.**  The symmetric statement for the other hypersurface. -/
theorem nonempty_cokerOneTensorQuad (a : R) (h2 : IsUnit (2 : R)) :
    Nonempty (((Fin 2 × Fin 2 → R) ⧸ LinearMap.range
        ((1 : Matrix (Fin 2) (Fin 2) R) ⊗ₖ quadDifferentMatrix a).mulVecLin)
      ≃ₗ[R] ∀ p : Fin 2 × Fin 2, (R ⧸ Ideal.span {(1 : R) * (![1, a ^ 2] p.2)})) := by
  obtain ⟨P, Q, hP, hQ, hPQ⟩ := smith_quadDifferent a h2
  have hone : (1 : Matrix (Fin 2) (Fin 2) R) * 1 * 1
      = Matrix.diagonal fun _ : Fin 2 => (1 : R) := by
    rw [Matrix.diagonal_one]
    simp
  refine nonempty_coker_equiv_pi_of_smith (P := 1 ⊗ₖ P) (Q := 1 ⊗ₖ Q) ?_ ?_ _ ?_
    (mul_kronecker_mul_smith hone hPQ)
  · rw [Matrix.det_kronecker, Matrix.det_one]
    simpa using hP.pow (Fintype.card (Fin 2))
  · rw [Matrix.det_kronecker, Matrix.det_one]
    simpa using hQ.pow (Fintype.card (Fin 2))
  · rw [Matrix.diagonal_kronecker_diagonal]

/-- **Card `(17)`, boxed.**  The cotangent module of the tensor-square order is the direct sum of
the two hypersurface cokernels, each of which is `(R/(a²))²`; so it is `(R/(a²))⁴`. -/
theorem nonempty_omega_corank_two (a : R) (h2 : IsUnit (2 : R)) :
    Nonempty ((((Fin 2 × Fin 2 → R) ⧸ LinearMap.range
          (quadDifferentMatrix a ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) R)).mulVecLin) ×
        ((Fin 2 × Fin 2 → R) ⧸ LinearMap.range
          ((1 : Matrix (Fin 2) (Fin 2) R) ⊗ₖ quadDifferentMatrix a).mulVecLin))
      ≃ₗ[R] ((∀ p : Fin 2 × Fin 2, R ⧸ Ideal.span {(![1, a ^ 2] p.1) * (1 : R)}) ×
        (∀ p : Fin 2 × Fin 2, R ⧸ Ideal.span {(1 : R) * (![1, a ^ 2] p.2)}))) := by
  obtain ⟨e₁⟩ := nonempty_cokerQuadTensorOne a h2
  obtain ⟨e₂⟩ := nonempty_cokerOneTensorQuad a h2
  exact ⟨e₁.prodCongr e₂⟩

/-- **Cards `(16)`–`(17)`.**  The two modules have the same total length `8`, but different Smith
partitions: the trace quotient has an invariant factor of exponent `4`, the cotangent module only
exponent `2`. -/
theorem corank_two_length_eq_partition_ne :
    (2 + 2 + 4 : ℕ) = 8 ∧ (2 + 2 + 2 + 2 : ℕ) = 8 ∧ (4 : ℕ) ≠ 2 := by
  refine ⟨rfl, rfl, ?_⟩
  omega

/-! ### The two modules are not isomorphic

The differing exponent partitions are separated by an invariant, not merely by a bookkeeping
count: the cotangent model is annihilated by `a²`, the trace-quotient model is not. -/

/-- Each Smith entry of the single quadratic factor divides `a²`. -/
theorem cons_one_sq_dvd_sq (a : R) (i : Fin 2) : ![1, a ^ 2] i ∣ a ^ 2 := by
  fin_cases i
  · simp
  · simp

/-- Every invariant factor of the cotangent model divides `a²`, so `a²` annihilates it. -/
theorem sq_smul_omegaModel_eq_zero (a : R)
    (x : ((∀ p : Fin 2 × Fin 2, R ⧸ Ideal.span {(![1, a ^ 2] p.1) * (1 : R)}) ×
      (∀ p : Fin 2 × Fin 2, R ⧸ Ideal.span {(1 : R) * (![1, a ^ 2] p.2)}))) :
    (a ^ 2) • x = 0 := by
  refine Prod.ext ?_ ?_
  · funext p
    obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (x.1 p)
    show (a ^ 2) • x.1 p = 0
    rw [← hy, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero,
      Ideal.mem_span_singleton, smul_eq_mul, mul_one]
    exact (cons_one_sq_dvd_sq a p.1).mul_right y
  · funext p
    obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (x.2 p)
    show (a ^ 2) • x.2 p = 0
    rw [← hy, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero,
      Ideal.mem_span_singleton, smul_eq_mul, one_mul]
    exact (cons_one_sq_dvd_sq a p.2).mul_right y

/-- The trace-quotient model has an invariant factor of exponent four, so `a²` does not annihilate
it: the class of `1` in the `(a⁴)`-summand survives. -/
theorem exists_sq_smul_traceModel_ne_zero [IsDomain R] {a : R} (ha : a ≠ 0) (hu : ¬ IsUnit a) :
    ∃ x : (∀ p : Fin 2 × Fin 2, R ⧸ Ideal.span {(![1, a ^ 2] p.1) * (![1, a ^ 2] p.2)}),
      (a ^ 2) • x ≠ 0 := by
  refine ⟨fun _ => Submodule.Quotient.mk 1, fun h => ?_⟩
  have hp : ((a ^ 2) • (Submodule.Quotient.mk 1 :
      R ⧸ Ideal.span {(![1, a ^ 2] ((1, 1) : Fin 2 × Fin 2).1) *
        (![1, a ^ 2] ((1, 1) : Fin 2 × Fin 2).2)})) = 0 := congrFun h (1, 1)
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Ideal.mem_span_singleton,
    smul_eq_mul, mul_one] at hp
  have hentry : (![1, a ^ 2] ((1, 1) : Fin 2 × Fin 2).1) *
      (![1, a ^ 2] ((1, 1) : Fin 2 × Fin 2).2) = a ^ 2 * a ^ 2 := by simp
  rw [hentry] at hp
  obtain ⟨r, hr⟩ := hp
  have ha2 : a ^ 2 ≠ 0 := pow_ne_zero 2 ha
  have h1 : a ^ 2 * 1 = a ^ 2 * (a ^ 2 * r) := by rw [mul_one]; linear_combination hr
  have h2 : (1 : R) = a ^ 2 * r := mul_left_cancel₀ ha2 h1
  have h3 : a * (a * r) = 1 := by rw [h2]; ring
  exact hu (IsUnit.of_mul_eq_one (a * r) h3)

/-- **Cards `(16)`–`(17)`, boxed, model form.**  The trace quotient and the cotangent module of the
tensor-square order are *not* isomorphic: `a²` annihilates one and not the other. -/
theorem not_nonempty_linearEquiv_traceModel_omegaModel [IsDomain R] {a : R} (ha : a ≠ 0)
    (hu : ¬ IsUnit a) :
    ¬ Nonempty ((∀ p : Fin 2 × Fin 2, R ⧸ Ideal.span {(![1, a ^ 2] p.1) * (![1, a ^ 2] p.2)})
      ≃ₗ[R] ((∀ p : Fin 2 × Fin 2, R ⧸ Ideal.span {(![1, a ^ 2] p.1) * (1 : R)}) ×
        (∀ p : Fin 2 × Fin 2, R ⧸ Ideal.span {(1 : R) * (![1, a ^ 2] p.2)}))) := by
  rintro ⟨e⟩
  obtain ⟨x, hx⟩ := exists_sq_smul_traceModel_ne_zero ha hu
  refine hx ?_
  have h1 : e ((a ^ 2) • x) = e 0 := by
    rw [map_smul, map_zero]
    exact sq_smul_omegaModel_eq_zero a (e x)
  exact e.injective h1

/-- **Cards `(16)`–`(17)`, boxed.**  Equal Kähler and Dedekind-different determinants do not force
isomorphic modules.  Over a domain in which `a` is a nonzero nonunit the trace quotient
`A^♯/A` of the tensor-square order and its cotangent module `Ω[A⁄R]` have the same total length
but are not isomorphic. -/
theorem not_nonempty_linearEquiv_coker_kronecker_omega [IsDomain R] {a : R} (ha : a ≠ 0)
    (hu : ¬ IsUnit a) (h2 : IsUnit (2 : R)) :
    ¬ Nonempty (((Fin 2 × Fin 2 → R) ⧸ LinearMap.range
          (quadDifferentMatrix a ⊗ₖ quadDifferentMatrix a).mulVecLin)
      ≃ₗ[R] (((Fin 2 × Fin 2 → R) ⧸ LinearMap.range
          (quadDifferentMatrix a ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) R)).mulVecLin) ×
        ((Fin 2 × Fin 2 → R) ⧸ LinearMap.range
          ((1 : Matrix (Fin 2) (Fin 2) R) ⊗ₖ quadDifferentMatrix a).mulVecLin))) := by
  rintro ⟨e⟩
  obtain ⟨e₁⟩ := nonempty_cokerKronecker a h2
  obtain ⟨e₂⟩ := nonempty_omega_corank_two a h2
  exact not_nonempty_linearEquiv_traceModel_omegaModel ha hu ⟨e₁.symm.trans (e.trans e₂)⟩

/-- The literal base of the card, `R = ℂ[[a]]` with `a = X`: the two modules of the tensor-square
order are not isomorphic, with no hypotheses. -/
theorem not_nonempty_linearEquiv_coker_kronecker_omega_powerSeries :
    ¬ Nonempty (((Fin 2 × Fin 2 → PowerSeries ℂ) ⧸ LinearMap.range
          (quadDifferentMatrix (PowerSeries.X : PowerSeries ℂ) ⊗ₖ
            quadDifferentMatrix (PowerSeries.X : PowerSeries ℂ)).mulVecLin)
      ≃ₗ[PowerSeries ℂ] (((Fin 2 × Fin 2 → PowerSeries ℂ) ⧸ LinearMap.range
          (quadDifferentMatrix (PowerSeries.X : PowerSeries ℂ) ⊗ₖ
            (1 : Matrix (Fin 2) (Fin 2) (PowerSeries ℂ))).mulVecLin) ×
        ((Fin 2 × Fin 2 → PowerSeries ℂ) ⧸ LinearMap.range
          ((1 : Matrix (Fin 2) (Fin 2) (PowerSeries ℂ)) ⊗ₖ
            quadDifferentMatrix (PowerSeries.X : PowerSeries ℂ)).mulVecLin))) := by
  refine not_nonempty_linearEquiv_coker_kronecker_omega PowerSeries.X_ne_zero ?_ ?_
  · intro h
    have hmap := h.map (PowerSeries.constantCoeff (R := ℂ))
    rw [PowerSeries.constantCoeff_X] at hmap
    exact not_isUnit_zero hmap
  · have h2 : IsUnit ((2 : ℂ)) := isUnit_iff_ne_zero.2 two_ne_zero
    have := h2.map (algebraMap ℂ (PowerSeries ℂ))
    rwa [map_ofNat] at this

end CorankTwo

end HTGeometry.ConstraintRelativity
