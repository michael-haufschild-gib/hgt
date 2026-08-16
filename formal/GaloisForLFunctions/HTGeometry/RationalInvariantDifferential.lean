import GaloisForLFunctions.HTGeometry.JetSubstitutionDescent
import GaloisForLFunctions.HTGeometry.RatFuncCompositionDegree

/-!
# Invariant differentials read on rational functions

An invariant `k`-differential of the substitution endomorphism is by construction an element of the
free jet field of order zero.  Order-zero elements are exactly the rational functions of the free
generator, so the whole invariance relation transports to an identity in `RatFunc C`:

`Q ∘ R · (R')^k = λ · Q`.

The derivative `R'` itself is produced by the same transport: the derivative factor of the
substitution has order zero, so it is the evaluation of a rational function, and that rational
function is the classical derivative.

This turns every statement about invariant differentials on the jet field into a statement about
rational maps of the projective line, which is the form the classification of exceptional maps
consumes.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

variable {C : Type*} [Field C] [CharZero C]

/-! ## Order-zero elements are rational functions of the generator -/

theorem mem_adjoin_freeGen_of_order_zero {v : JetField C Unit}
    (hv : ∀ j : ℕ, 0 < j → JetField.pd ((), j) v = 0) :
    v ∈ IntermediateField.adjoin C ({JetField.jet ((), 0)} : Set (JetField C Unit)) := by
  have hmem : v ∈ jetPrefixField C 1 := by
    rw [mem_jetPrefixField_iff]
    exact fun j hj => hv j (by omega)
  have hset : ((fun p : Unit × ℕ => (JetField.jet p : JetField C Unit)) '' {p | p.2 < 1})
      = ({JetField.jet ((), 0)} : Set (JetField C Unit)) := by
    ext z
    constructor
    · rintro ⟨⟨u, j⟩, hj, rfl⟩
      have hj0 : j = 0 := by simpa using hj
      rw [hj0]
      rfl
    · rintro rfl
      exact ⟨((), 0), by simp, rfl⟩
  rw [jetPrefixField, hset] at hmem
  exact hmem

/-- **Order zero is rationality in the free generator.** -/
theorem exists_ratFunc_of_order_zero {v : JetField C Unit}
    (hv : ∀ j : ℕ, 0 < j → JetField.pd ((), j) v = 0) :
    ∃ Q : RatFunc C,
      ratFuncEval (JetField.jet ((), 0) : JetField C Unit) transcendental_freeGen Q = v := by
  refine ⟨(RatFunc.algEquivOfTranscendental (JetField.jet ((), 0) : JetField C Unit)
    transcendental_freeGen).symm ⟨v, mem_adjoin_freeGen_of_order_zero hv⟩, ?_⟩
  simp only [ratFuncEval, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.apply_symm_apply]
  rfl

/-! ## The derivative of a rational function -/

omit [CharZero C] in
theorem substitutionDeriv_order_zero (R : RatFunc C) :
    ∀ j : ℕ, 0 < j → JetField.pd ((), j) (substitutionDeriv R) = 0 :=
  fun j hj => pd_substitutionDeriv_eq_zero R (by omega)

/-- The derivative of a rational function, produced by the derivative factor of its substitution
on the free jet field. -/
def ratFuncDeriv (R : RatFunc C) : RatFunc C :=
  (RatFunc.algEquivOfTranscendental (JetField.jet ((), 0) : JetField C Unit)
      transcendental_freeGen).symm
    ⟨substitutionDeriv R, mem_adjoin_freeGen_of_order_zero (substitutionDeriv_order_zero R)⟩

@[simp]
theorem ratFuncEval_ratFuncDeriv (R : RatFunc C) :
    ratFuncEval (JetField.jet ((), 0) : JetField C Unit) transcendental_freeGen
        (ratFuncDeriv R) = substitutionDeriv R := by
  simp only [ratFuncDeriv, ratFuncEval, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    AlgEquiv.apply_symm_apply]
  rfl

theorem ratFuncDeriv_ne_zero {R : RatFunc C} (hR : substitutionDeriv R ≠ 0) :
    ratFuncDeriv R ≠ 0 := by
  intro h
  apply hR
  rw [← ratFuncEval_ratFuncDeriv R, h, map_zero]

/-- Evaluation at equal points agrees. -/
theorem ratFuncEval_congr {K E : Type*} [Field K] [Field E] [Algebra K E] {y y' : E}
    (hy : Transcendental K y) (hy' : Transcendental K y') (h : y = y') (Q : RatFunc K) :
    ratFuncEval y hy Q = ratFuncEval y' hy' Q := by
  subst h
  rfl

/-! ## Substitution on rational functions -/

omit [CharZero C] in
theorem not_isConst_of_substitutionDeriv_ne_zero {R : RatFunc C}
    (hR : substitutionDeriv R ≠ 0) : ¬ ∃ c : C, R = RatFunc.C c := by
  rintro ⟨c, rfl⟩
  apply hR
  have hval : substitutionValue (RatFunc.C c : RatFunc C)
      = algebraMap C (JetField C Unit) c := by
    rw [substitutionValue]
    exact ratFuncEval_C _ transcendental_freeGen c
  rw [substitutionDeriv, hval, Derivation.map_algebraMap]

/-- **Evaluation intertwines substitution.**  Evaluating a composed rational function at the free
generator is the substitution endomorphism applied to the evaluation. -/
theorem ratFuncEval_ratFuncSubstitution (R : RatFunc C) (hR : substitutionDeriv R ≠ 0)
    (Q : RatFunc C) :
    ratFuncEval (JetField.jet ((), 0) : JetField C Unit) transcendental_freeGen
        (ratFuncSubstitutionAlgHom R (not_isConst_of_substitutionDeriv_ne_zero hR) Q)
      = jetSubstitution R hR
          (ratFuncEval (JetField.jet ((), 0) : JetField C Unit) transcendental_freeGen Q) := by
  have hRtr : Transcendental C R :=
    R.transcendental_of_ne_C (not_isConst_of_substitutionDeriv_ne_zero hR)
  have hsubst : ratFuncSubstitutionAlgHom R (not_isConst_of_substitutionDeriv_ne_zero hR)
      = ratFuncEval R hRtr := rfl
  rw [hsubst]
  have h1 := ratFuncEval_algHom
    (ratFuncEval (JetField.jet ((), 0) : JetField C Unit) transcendental_freeGen)
    (y := R) hRtr Q
  have h2 := ratFuncEval_algHom (jetSubstitution R hR)
    (y := (JetField.jet ((), 0) : JetField C Unit)) transcendental_freeGen Q
  have hpt : ratFuncEval (JetField.jet ((), 0) : JetField C Unit) transcendental_freeGen R
      = jetSubstitution R hR (JetField.jet ((), 0) : JetField C Unit) :=
    (jetSubstitution_freeGen R hR).symm
  rw [← h1, ← h2]
  exact ratFuncEval_congr _ _ hpt Q

/-! ## The transported invariance relation -/

/-- **An invariant differential is a rational relation.**  Every invariant `k`-differential of the
substitution comes from a nonzero rational function satisfying `Q ∘ R · (R')^k = λ Q`. -/
theorem exists_ratFunc_relation_of_isInvariantDifferential (R : RatFunc C)
    (hR : substitutionDeriv R ≠ 0) {k : ℤ} {q : JetField C Unit} {lam : C}
    (hq : IsInvariantDifferential R hR k q lam) :
    ∃ Q : RatFunc C, Q ≠ 0 ∧
      ratFuncSubstitutionAlgHom R (not_isConst_of_substitutionDeriv_ne_zero hR) Q
          * ratFuncDeriv R ^ k = RatFunc.C lam * Q := by
  obtain ⟨hq0, hqord, hqeig⟩ := hq
  obtain ⟨Q, hQ⟩ := exists_ratFunc_of_order_zero hqord
  have hinj : Function.Injective
      (ratFuncEval (JetField.jet ((), 0) : JetField C Unit) transcendental_freeGen) :=
    ratFuncEval_injective _ transcendental_freeGen
  refine ⟨Q, ?_, ?_⟩
  · intro h
    exact hq0 (by rw [← hQ, h, map_zero])
  · refine hinj ?_
    rw [map_mul, map_zpow₀, map_mul, ratFuncEval_ratFuncSubstitution R hR,
      ratFuncEval_ratFuncDeriv, hQ]
    have hC : ratFuncEval (JetField.jet ((), 0) : JetField C Unit) transcendental_freeGen
        (RatFunc.C lam) = algebraMap C (JetField C Unit) lam :=
      ratFuncEval_C _ transcendental_freeGen lam
    rw [hC]
    exact hqeig

/-- **A rational relation is an invariant differential.**  The converse transport. -/
theorem isInvariantDifferential_of_ratFunc_relation (R : RatFunc C)
    (hR : substitutionDeriv R ≠ 0) {k : ℤ} {lam : C} {Q : RatFunc C} (hQ : Q ≠ 0)
    (hrel : ratFuncSubstitutionAlgHom R (not_isConst_of_substitutionDeriv_ne_zero hR) Q
        * ratFuncDeriv R ^ k = RatFunc.C lam * Q) :
    IsInvariantDifferential R hR k
      (ratFuncEval (JetField.jet ((), 0) : JetField C Unit) transcendental_freeGen Q) lam := by
  have hinj : Function.Injective
      (ratFuncEval (JetField.jet ((), 0) : JetField C Unit) transcendental_freeGen) :=
    ratFuncEval_injective _ transcendental_freeGen
  refine ⟨?_, ?_, ?_⟩
  · intro h
    exact hQ (hinj (by rw [h, map_zero]))
  · intro j hj
    refine derivation_eq_zero_of_mem_adjoin _ _ ?_
      (ratFuncEval_mem_adjoin transcendental_freeGen Q)
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    exact JetField.pd_jet_of_ne (by simp only [ne_eq, Prod.mk.injEq, true_and]; omega)
  · have h := congrArg
      (ratFuncEval (JetField.jet ((), 0) : JetField C Unit) transcendental_freeGen) hrel
    rw [map_mul, map_zpow₀, map_mul, ratFuncEval_ratFuncSubstitution R hR,
      ratFuncEval_ratFuncDeriv] at h
    have hC : ratFuncEval (JetField.jet ((), 0) : JetField C Unit) transcendental_freeGen
        (RatFunc.C lam) = algebraMap C (JetField C Unit) lam :=
      ratFuncEval_C _ transcendental_freeGen lam
    rw [hC] at h
    exact h

/-! ## The derivative is the classical one -/

@[simp]
theorem ratFuncDeriv_X : ratFuncDeriv (RatFunc.X : RatFunc C) = 1 := by
  have hinj : Function.Injective
      (ratFuncEval (JetField.jet ((), 0) : JetField C Unit) transcendental_freeGen) :=
    ratFuncEval_injective _ transcendental_freeGen
  refine hinj ?_
  rw [ratFuncEval_ratFuncDeriv, map_one, substitutionDeriv]
  have hval : substitutionValue (RatFunc.X : RatFunc C)
      = (JetField.jet ((), 0) : JetField C Unit) := by
    rw [substitutionValue]
    exact ratFuncEval_X _ transcendental_freeGen
  rw [hval, JetField.pd_jet_self]

/-! ## The hard direction in classical language -/

/-- **A nonconstant eigenvector of order at most one produces an invariant rational
`k`-differential with `k ≠ 0`.** -/
theorem exists_ratFunc_relation_of_order_one (R : RatFunc C) (hR : substitutionDeriv R ≠ 0)
    {u : JetField C Unit} (hu : ∀ j : ℕ, 1 < j → JetField.pd ((), j) u = 0)
    (hnc : ∀ e : C, u ≠ algebraMap C (JetField C Unit) e) {lam : C} (hlam : lam ≠ 0)
    (heig : jetSubstitution R hR u = algebraMap C (JetField C Unit) lam * u) :
    ∃ (k : ℤ) (Q : RatFunc C) (μ : C), k ≠ 0 ∧ μ ≠ 0 ∧ Q ≠ 0 ∧
      ratFuncSubstitutionAlgHom R (not_isConst_of_substitutionDeriv_ne_zero hR) Q
          * ratFuncDeriv R ^ k = RatFunc.C μ * Q := by
  obtain ⟨k, q, μ, hk, hμ, hq⟩ :=
    exists_nonzero_isInvariantDifferential_of_order_one R hR hu hnc hlam heig
  obtain ⟨Q, hQ0, hQ⟩ := exists_ratFunc_relation_of_isInvariantDifferential R hR hq
  exact ⟨k, Q, μ, hk, hμ, hQ0, hQ⟩

/-- **The tensor-or-affine-structure dichotomy in classical language.**  A nonconstant eigenvector
of the substitution of any finite jet order forces either a nonzero rational function with
`Q ∘ R · (R')^k = μ Q`, `k ≠ 0`, `μ ≠ 0`, or an invariant affine structure at some jet level at
least two. -/
theorem exists_ratFunc_relation_or_hasNormalizingShift (R : RatFunc C)
    (hR : substitutionDeriv R ≠ 0) {u : JetField C Unit} {M : ℕ}
    (hu : ∀ j : ℕ, M < j → JetField.pd ((), j) u = 0)
    (hnc : ∀ e : C, u ≠ algebraMap C (JetField C Unit) e) {lam : C} (hlam : lam ≠ 0)
    (heig : jetSubstitution R hR u = algebraMap C (JetField C Unit) lam * u) :
    (∃ (k : ℤ) (Q : RatFunc C) (μ : C), k ≠ 0 ∧ μ ≠ 0 ∧ Q ≠ 0 ∧
        ratFuncSubstitutionAlgHom R (not_isConst_of_substitutionDeriv_ne_zero hR) Q
          * ratFuncDeriv R ^ k = RatFunc.C μ * Q)
      ∨ ∃ (N : ℕ) (hN : 2 ≤ N), HasNormalizingShift R hR (le_trans one_le_two hN) := by
  rcases exists_nonzero_isInvariantDifferential_or_hasNormalizingShift R hR hlam M u hu hnc heig
    with ⟨k, q, μ, hk, hμ, hq⟩ | hshift
  · obtain ⟨Q, hQ0, hQ⟩ := exists_ratFunc_relation_of_isInvariantDifferential R hR hq
    exact Or.inl ⟨k, Q, μ, hk, hμ, hQ0, hQ⟩
  · exact Or.inr hshift

/-! ## The derivative is a derivation of the rational function field -/

omit [CharZero C] in
private theorem ratFuncEval_freeGen_injective :
    Function.Injective
      (ratFuncEval (JetField.jet ((), 0) : JetField C Unit) transcendental_freeGen) :=
  ratFuncEval_injective _ transcendental_freeGen

omit [CharZero C] in
theorem substitutionValue_add (R S : RatFunc C) :
    substitutionValue (R + S) = substitutionValue R + substitutionValue S :=
  map_add _ R S

omit [CharZero C] in
theorem substitutionValue_mul (R S : RatFunc C) :
    substitutionValue (R * S) = substitutionValue R * substitutionValue S :=
  map_mul _ R S

theorem ratFuncDeriv_add (R S : RatFunc C) :
    ratFuncDeriv (R + S) = ratFuncDeriv R + ratFuncDeriv S := by
  refine ratFuncEval_freeGen_injective ?_
  rw [map_add, ratFuncEval_ratFuncDeriv, ratFuncEval_ratFuncDeriv, ratFuncEval_ratFuncDeriv,
    substitutionDeriv, substitutionDeriv, substitutionDeriv, substitutionValue_add, map_add]

theorem ratFuncDeriv_mul (R S : RatFunc C) :
    ratFuncDeriv (R * S) = R * ratFuncDeriv S + S * ratFuncDeriv R := by
  refine ratFuncEval_freeGen_injective ?_
  rw [ratFuncEval_ratFuncDeriv, map_add, map_mul, map_mul, ratFuncEval_ratFuncDeriv,
    ratFuncEval_ratFuncDeriv, substitutionDeriv, substitutionDeriv, substitutionDeriv,
    substitutionValue_mul]
  have h := (JetField.pd ((), 0) : Derivation C (JetField C Unit) (JetField C Unit)).leibniz
    (substitutionValue R) (substitutionValue S)
  simp only [smul_eq_mul] at h
  rw [h]
  rfl

theorem ratFuncDeriv_C (a : C) : ratFuncDeriv (RatFunc.C a : RatFunc C) = 0 := by
  refine ratFuncEval_freeGen_injective ?_
  rw [ratFuncEval_ratFuncDeriv, map_zero, substitutionDeriv]
  have hval : substitutionValue (RatFunc.C a : RatFunc C)
      = algebraMap C (JetField C Unit) a := ratFuncEval_C _ transcendental_freeGen a
  rw [hval, Derivation.map_algebraMap]

/-- **The derivative of rational functions is a derivation.**  Mathlib has no derivation on
`RatFunc`; this one is transported from the coordinate partial of the free jet field, and
`ratFuncDeriv_X` identifies it as the classical one. -/
def ratFuncDerivation : Derivation C (RatFunc C) (RatFunc C) where
  toFun := ratFuncDeriv
  map_add' := ratFuncDeriv_add
  map_smul' a R := by
    show ratFuncDeriv (a • R) = a • ratFuncDeriv R
    have hsm : a • R = RatFunc.C a * R := RatFunc.smul_eq_C_mul a R
    rw [hsm, ratFuncDeriv_mul, ratFuncDeriv_C, mul_zero, add_zero,
      RatFunc.smul_eq_C_mul a (ratFuncDeriv R)]
  map_one_eq_zero' := by
    show ratFuncDeriv (1 : RatFunc C) = 0
    have h1 : (1 : RatFunc C) = RatFunc.C 1 := by rw [map_one]
    rw [h1, ratFuncDeriv_C]
  leibniz' := fun R S => by
    show ratFuncDeriv (R * S) = R • ratFuncDeriv S + S • ratFuncDeriv R
    rw [ratFuncDeriv_mul]
    simp only [smul_eq_mul]

@[simp]
theorem ratFuncDerivation_apply (R : RatFunc C) : ratFuncDerivation R = ratFuncDeriv R := rfl

/-- **The derivative of a polynomial is the classical one.** -/
theorem ratFuncDeriv_algebraMap (P : Polynomial C) :
    ratFuncDeriv (algebraMap (Polynomial C) (RatFunc C) P)
      = algebraMap (Polynomial C) (RatFunc C) (Polynomial.derivative P) := by
  induction P using Polynomial.induction_on with
  | C a =>
      rw [RatFunc.algebraMap_C, ratFuncDeriv_C, Polynomial.derivative_C, map_zero]
  | add p q hp hq =>
      rw [map_add, ratFuncDeriv_add, hp, hq, Polynomial.derivative_add, map_add]
  | monomial n a ih =>
      have hstep : (Polynomial.C a * Polynomial.X ^ (n + 1))
          = (Polynomial.C a * Polynomial.X ^ n) * Polynomial.X := by ring
      have hRHS : Polynomial.derivative ((Polynomial.C a * Polynomial.X ^ n) * Polynomial.X)
          = Polynomial.derivative (Polynomial.C a * Polynomial.X ^ n) * Polynomial.X
            + (Polynomial.C a * Polynomial.X ^ n) := by
        rw [Polynomial.derivative_mul, Polynomial.derivative_X, mul_one]
      rw [hstep, map_mul, ratFuncDeriv_mul, ih, RatFunc.algebraMap_X, ratFuncDeriv_X, hRHS]
      simp only [map_add, map_mul, RatFunc.algebraMap_X]
      ring

end

end GaloisForLFunctions.HTGeometry
