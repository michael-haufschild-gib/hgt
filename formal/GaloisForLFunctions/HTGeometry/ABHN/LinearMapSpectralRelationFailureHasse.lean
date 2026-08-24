import GaloisForLFunctions.HTGeometry.HassePredicate
import GaloisForLFunctions.HTGeometry.ABHN.HasseLinearMapEigenvectors
import GaloisForLFunctions.HTGeometry.ABHN.HasseLinearMapPeriodicity
import GaloisForLFunctions.HTGeometry.ABHN.HasseLinearMapEigenDimensions
import GaloisForLFunctions.HTGeometry.ABHN.HasseLinearMapRelations
import GaloisForLFunctions.HTGeometry.ABHN.HasseLinearMapInvariants

/-!
# Linear-map spectral and relation defects at every completion

Faithful completion reflects eigenvalue occurrence, generalized eigenspace dimensions, finite
order, involutivity, commutation, idempotence, semiconjugacy, and standard finite-dimensional
invariants.  Failure of these conditions persists at every global-field place.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped TensorProduct

universe u w

/-- Absence of a chosen eigenvalue over a number field persists at every completion. -/
theorem numberField_linearMap_eigenKernel_eq_bot_iff_forall_place
    (K : Type u) [Field K] [NumberField K]
    {M : Type w} [AddCommGroup M] [Module K M] (f : M →ₗ[K] M) (a : K) :
    LinearMap.ker (f - a • LinearMap.id) = ⊥ ↔ ∀ p : NumberFieldPlace K,
      LinearMap.ker (f.baseChange (completion K p) -
        (algebraMap K (completion K p) a) • LinearMap.id) = ⊥ := by
  simpa only [not_ne_iff] using not_iff_forall_not_of_iff_exists
    (numberField_linearMap_eigenKernel_ne_bot_iff_exists_place K f a)

/-- Absence of a chosen eigenvalue over a function field persists at every completion. -/
theorem rationalFunction_linearMap_eigenKernel_eq_bot_iff_forall_place
    (F : Type u) [Field F] [Finite F]
    {M : Type w} [AddCommGroup M] [Module (RatFunc F) M]
    (f : M →ₗ[RatFunc F] M) (a : RatFunc F) :
    LinearMap.ker (f - a • LinearMap.id) = ⊥ ↔ ∀ p : RationalFunctionPlace F,
      LinearMap.ker (f.baseChange (rationalFunctionCompletion F p) -
        (algebraMap (RatFunc F) (rationalFunctionCompletion F p) a) • LinearMap.id) = ⊥ := by
  simpa only [not_ne_iff] using not_iff_forall_not_of_iff_exists
    (rationalFunction_linearMap_eigenKernel_ne_bot_iff_exists_place F f a)

/-- Failure of a prescribed finite order over a number field persists at every completion. -/
theorem numberField_linearMap_pow_ne_id_iff_forall_place
    (K : Type u) [Field K] [NumberField K]
    {M : Type w} [AddCommGroup M] [Module K M] (f : M →ₗ[K] M) (n : ℕ) :
    f ^ n ≠ 1 ↔ ∀ p : NumberFieldPlace K,
      (f.baseChange (completion K p)) ^ n ≠ 1 :=
  not_iff_forall_not_of_iff_exists
    (numberField_linearMap_pow_eq_id_iff_exists_place K f n)

/-- Failure of a prescribed finite order over a function field persists at every completion. -/
theorem rationalFunction_linearMap_pow_ne_id_iff_forall_place
    (F : Type u) [Field F] [Finite F]
    {M : Type w} [AddCommGroup M] [Module (RatFunc F) M]
    (f : M →ₗ[RatFunc F] M) (n : ℕ) :
    f ^ n ≠ 1 ↔ ∀ p : RationalFunctionPlace F,
      (f.baseChange (rationalFunctionCompletion F p)) ^ n ≠ 1 :=
  not_iff_forall_not_of_iff_exists
    (rationalFunction_linearMap_pow_eq_id_iff_exists_place F f n)

/-- Failure of involutivity over a number field persists at every completion. -/
theorem numberField_linearMap_not_involutive_iff_forall_place
    (K : Type u) [Field K] [NumberField K]
    {M : Type w} [AddCommGroup M] [Module K M] (f : M →ₗ[K] M) :
    ¬ Function.Involutive f ↔ ∀ p : NumberFieldPlace K,
      ¬ Function.Involutive (f.baseChange (completion K p)) :=
  not_iff_forall_not_of_iff_exists
    (numberField_linearMap_involutive_iff_exists_place K f)

/-- Failure of involutivity over a function field persists at every completion. -/
theorem rationalFunction_linearMap_not_involutive_iff_forall_place
    (F : Type u) [Field F] [Finite F]
    {M : Type w} [AddCommGroup M] [Module (RatFunc F) M]
    (f : M →ₗ[RatFunc F] M) :
    ¬ Function.Involutive f ↔ ∀ p : RationalFunctionPlace F,
      ¬ Function.Involutive (f.baseChange (rationalFunctionCompletion F p)) :=
  not_iff_forall_not_of_iff_exists
    (rationalFunction_linearMap_involutive_iff_exists_place F f)

/-- A wrong generalized-eigenspace dimension over a number field persists everywhere. -/
theorem numberField_linearMap_generalizedEigenKernel_finrank_ne_iff_forall_place
    (K : Type u) [Field K] [NumberField K]
    {M : Type w} [AddCommGroup M] [Module K M]
    (f : M →ₗ[K] M) (a : K) (n d : ℕ) :
    Module.finrank K (LinearMap.ker ((f - a • LinearMap.id) ^ n)) ≠ d ↔
      ∀ p : NumberFieldPlace K,
        Module.finrank (completion K p) (LinearMap.ker
          ((f.baseChange (completion K p) -
            (algebraMap K (completion K p) a) • LinearMap.id) ^ n)) ≠ d :=
  not_iff_forall_not_of_iff_exists
    (numberField_linearMap_generalizedEigenKernel_finrank_eq_iff_exists_place K f a n d)

/-- A wrong generalized-eigenspace dimension over a function field persists everywhere. -/
theorem rationalFunction_linearMap_generalizedEigenKernel_finrank_ne_iff_forall_place
    (F : Type u) [Field F] [Finite F]
    {M : Type w} [AddCommGroup M] [Module (RatFunc F) M]
    (f : M →ₗ[RatFunc F] M) (a : RatFunc F) (n d : ℕ) :
    Module.finrank (RatFunc F) (LinearMap.ker ((f - a • LinearMap.id) ^ n)) ≠ d ↔
      ∀ p : RationalFunctionPlace F,
        Module.finrank (rationalFunctionCompletion F p) (LinearMap.ker
          ((f.baseChange (rationalFunctionCompletion F p) -
            (algebraMap (RatFunc F) (rationalFunctionCompletion F p) a) •
              LinearMap.id) ^ n)) ≠ d :=
  not_iff_forall_not_of_iff_exists
    (rationalFunction_linearMap_generalizedEigenKernel_finrank_eq_iff_exists_place F f a n d)

/-- Noncommutation of number-field endomorphisms persists at every completion. -/
theorem numberField_linearMap_not_commute_iff_forall_place
    (K : Type u) [Field K] [NumberField K]
    {M : Type w} [AddCommGroup M] [Module K M] (f g : M →ₗ[K] M) :
    ¬ Commute f g ↔ ∀ p : NumberFieldPlace K,
      ¬ Commute (f.baseChange (completion K p)) (g.baseChange (completion K p)) :=
  not_iff_forall_not_of_iff_exists
    (numberField_linearMap_commute_iff_exists_place K f g)

/-- Noncommutation of function-field endomorphisms persists at every completion. -/
theorem rationalFunction_linearMap_not_commute_iff_forall_place
    (F : Type u) [Field F] [Finite F]
    {M : Type w} [AddCommGroup M] [Module (RatFunc F) M]
    (f g : M →ₗ[RatFunc F] M) :
    ¬ Commute f g ↔ ∀ p : RationalFunctionPlace F,
      ¬ Commute (f.baseChange (rationalFunctionCompletion F p))
        (g.baseChange (rationalFunctionCompletion F p)) :=
  not_iff_forall_not_of_iff_exists
    (rationalFunction_linearMap_commute_iff_exists_place F f g)

/-- Nonidempotence of a number-field endomorphism persists at every completion. -/
theorem numberField_linearMap_not_isIdempotentElem_iff_forall_place
    (K : Type u) [Field K] [NumberField K]
    {M : Type w} [AddCommGroup M] [Module K M] (f : M →ₗ[K] M) :
    ¬ IsIdempotentElem f ↔ ∀ p : NumberFieldPlace K,
      ¬ IsIdempotentElem (f.baseChange (completion K p)) :=
  not_iff_forall_not_of_iff_exists
    (numberField_linearMap_isIdempotentElem_iff_exists_place K f)

/-- Nonidempotence of a function-field endomorphism persists at every completion. -/
theorem rationalFunction_linearMap_not_isIdempotentElem_iff_forall_place
    (F : Type u) [Field F] [Finite F]
    {M : Type w} [AddCommGroup M] [Module (RatFunc F) M]
    (f : M →ₗ[RatFunc F] M) :
    ¬ IsIdempotentElem f ↔ ∀ p : RationalFunctionPlace F,
      ¬ IsIdempotentElem (f.baseChange (rationalFunctionCompletion F p)) :=
  not_iff_forall_not_of_iff_exists
    (rationalFunction_linearMap_isIdempotentElem_iff_exists_place F f)

/-- Failure of a fixed semiconjugacy over a number field persists at every completion. -/
theorem numberField_linearMap_not_semiconjBy_iff_forall_place
    (K : Type u) [Field K] [NumberField K]
    {M : Type w} [AddCommGroup M] [Module K M] (f g h : M →ₗ[K] M) :
    ¬ SemiconjBy f g h ↔ ∀ p : NumberFieldPlace K,
      ¬ SemiconjBy (f.baseChange (completion K p)) (g.baseChange (completion K p))
        (h.baseChange (completion K p)) :=
  not_iff_forall_not_of_iff_exists
    (numberField_linearMap_semiconjBy_iff_exists_place K f g h)

/-- Failure of a fixed semiconjugacy over a function field persists at every completion. -/
theorem rationalFunction_linearMap_not_semiconjBy_iff_forall_place
    (F : Type u) [Field F] [Finite F]
    {M : Type w} [AddCommGroup M] [Module (RatFunc F) M]
    (f g h : M →ₗ[RatFunc F] M) :
    ¬ SemiconjBy f g h ↔ ∀ p : RationalFunctionPlace F,
      ¬ SemiconjBy (f.baseChange (rationalFunctionCompletion F p))
        (g.baseChange (rationalFunctionCompletion F p))
        (h.baseChange (rationalFunctionCompletion F p)) :=
  not_iff_forall_not_of_iff_exists
    (rationalFunction_linearMap_semiconjBy_iff_exists_place F f g h)

/-- A wrong characteristic polynomial of a number-field endomorphism persists everywhere. -/
theorem numberField_linearMap_charpoly_ne_iff_forall_place
    (K : Type u) [Field K] [NumberField K]
    {M : Type w} [AddCommGroup M] [Module K M] [Module.Finite K M]
    (f : M →ₗ[K] M) (q : Polynomial K) :
    f.charpoly ≠ q ↔ ∀ p : NumberFieldPlace K,
      (f.baseChange (completion K p)).charpoly ≠ q.map (algebraMap K (completion K p)) :=
  not_iff_forall_not_of_iff_exists
    (numberField_linearMap_charpoly_eq_iff_exists_place K f q)

/-- A wrong characteristic polynomial of a function-field endomorphism persists everywhere. -/
theorem rationalFunction_linearMap_charpoly_ne_iff_forall_place
    (F : Type u) [Field F] [Finite F]
    {M : Type w} [AddCommGroup M] [Module (RatFunc F) M] [Module.Finite (RatFunc F) M]
    (f : M →ₗ[RatFunc F] M) (q : Polynomial (RatFunc F)) :
    f.charpoly ≠ q ↔ ∀ p : RationalFunctionPlace F,
      (f.baseChange (rationalFunctionCompletion F p)).charpoly ≠
        q.map (algebraMap (RatFunc F) (rationalFunctionCompletion F p)) :=
  not_iff_forall_not_of_iff_exists
    (rationalFunction_linearMap_charpoly_eq_iff_exists_place F f q)

/-- A wrong trace of a number-field endomorphism persists at every completion. -/
theorem numberField_linearMap_trace_ne_iff_forall_place
    (K : Type u) [Field K] [NumberField K]
    {M : Type w} [AddCommGroup M] [Module K M] [Module.Finite K M]
    (f : M →ₗ[K] M) (a : K) :
    LinearMap.trace K M f ≠ a ↔ ∀ p : NumberFieldPlace K,
      LinearMap.trace (completion K p) (completion K p ⊗[K] M)
        (f.baseChange (completion K p)) ≠ algebraMap K (completion K p) a :=
  not_iff_forall_not_of_iff_exists
    (numberField_linearMap_trace_eq_iff_exists_place K f a)

/-- A wrong trace of a function-field endomorphism persists at every completion. -/
theorem rationalFunction_linearMap_trace_ne_iff_forall_place
    (F : Type u) [Field F] [Finite F]
    {M : Type w} [AddCommGroup M] [Module (RatFunc F) M] [Module.Finite (RatFunc F) M]
    (f : M →ₗ[RatFunc F] M) (a : RatFunc F) :
    LinearMap.trace (RatFunc F) M f ≠ a ↔ ∀ p : RationalFunctionPlace F,
      LinearMap.trace (rationalFunctionCompletion F p)
        (rationalFunctionCompletion F p ⊗[RatFunc F] M)
        (f.baseChange (rationalFunctionCompletion F p)) ≠
          algebraMap (RatFunc F) (rationalFunctionCompletion F p) a :=
  not_iff_forall_not_of_iff_exists
    (rationalFunction_linearMap_trace_eq_iff_exists_place F f a)

/-- A wrong determinant of a number-field endomorphism persists at every completion. -/
theorem numberField_linearMap_det_ne_iff_forall_place
    (K : Type u) [Field K] [NumberField K]
    {M : Type w} [AddCommGroup M] [Module K M] [Module.Finite K M]
    (f : M →ₗ[K] M) (a : K) :
    LinearMap.det f ≠ a ↔ ∀ p : NumberFieldPlace K,
      LinearMap.det (f.baseChange (completion K p)) ≠ algebraMap K (completion K p) a :=
  not_iff_forall_not_of_iff_exists
    (numberField_linearMap_det_eq_iff_exists_place K f a)

/-- A wrong determinant of a function-field endomorphism persists at every completion. -/
theorem rationalFunction_linearMap_det_ne_iff_forall_place
    (F : Type u) [Field F] [Finite F]
    {M : Type w} [AddCommGroup M] [Module (RatFunc F) M] [Module.Finite (RatFunc F) M]
    (f : M →ₗ[RatFunc F] M) (a : RatFunc F) :
    LinearMap.det f ≠ a ↔ ∀ p : RationalFunctionPlace F,
      LinearMap.det (f.baseChange (rationalFunctionCompletion F p)) ≠
        algebraMap (RatFunc F) (rationalFunctionCompletion F p) a :=
  not_iff_forall_not_of_iff_exists
    (rationalFunction_linearMap_det_eq_iff_exists_place F f a)

end GaloisForLFunctions.HTGeometry.ABHN
