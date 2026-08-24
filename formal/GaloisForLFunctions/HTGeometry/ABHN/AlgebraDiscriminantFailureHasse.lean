import GaloisForLFunctions.HTGeometry.HassePredicate
import GaloisForLFunctions.HTGeometry.ABHN.HasseAlgebraDiscriminant

/-!
# Algebra trace and discriminant defects at every completion

Basis discriminants and finite-algebra traces commute with faithful completion.  A wrong value,
and in particular discriminant vanishing, therefore persists at every global-field place.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped TensorProduct

universe u w x

/-- A wrong number-field algebra discriminant persists at every completion. -/
theorem numberField_algebra_discr_ne_iff_forall_place
    (K : Type u) [Field K] [NumberField K]
    {B : Type w} [CommRing B] [Algebra K B] [Module.Free K B] [Module.Finite K B]
    {ι : Type x} [Fintype ι] [DecidableEq ι] (e : Module.Basis ι K B) (c : K) :
    Algebra.discr K e ≠ c ↔ ∀ p : NumberFieldPlace K,
      Algebra.discr (completion K p)
        (e.baseChange (completion K p) :
          Module.Basis ι (completion K p) (completion K p ⊗[K] B)) ≠
            algebraMap K (completion K p) c :=
  not_iff_forall_not_of_iff_exists
    (numberField_algebra_discr_eq_iff_exists_place K e c)

/-- A wrong function-field algebra discriminant persists at every completion. -/
theorem rationalFunction_algebra_discr_ne_iff_forall_place
    (F : Type u) [Field F] [Finite F]
    {B : Type w} [CommRing B] [Algebra (RatFunc F) B]
    [Module.Free (RatFunc F) B] [Module.Finite (RatFunc F) B]
    {ι : Type x} [Fintype ι] [DecidableEq ι]
    (e : Module.Basis ι (RatFunc F) B) (c : RatFunc F) :
    Algebra.discr (RatFunc F) e ≠ c ↔ ∀ p : RationalFunctionPlace F,
      Algebra.discr (rationalFunctionCompletion F p)
        (e.baseChange (rationalFunctionCompletion F p) :
          Module.Basis ι (rationalFunctionCompletion F p)
            (rationalFunctionCompletion F p ⊗[RatFunc F] B)) ≠
              algebraMap (RatFunc F) (rationalFunctionCompletion F p) c :=
  not_iff_forall_not_of_iff_exists
    (rationalFunction_algebra_discr_eq_iff_exists_place F e c)

/-- Vanishing of a number-field algebra discriminant persists at every completion. -/
theorem numberField_algebra_discr_eq_zero_iff_forall_place
    (K : Type u) [Field K] [NumberField K]
    {B : Type w} [CommRing B] [Algebra K B] [Module.Free K B] [Module.Finite K B]
    {ι : Type x} [Fintype ι] [DecidableEq ι] (e : Module.Basis ι K B) :
    Algebra.discr K e = 0 ↔ ∀ p : NumberFieldPlace K,
      Algebra.discr (completion K p)
        (e.baseChange (completion K p) :
          Module.Basis ι (completion K p) (completion K p ⊗[K] B)) = 0 := by
  simpa only [not_ne_iff] using not_iff_forall_not_of_iff_exists
    (numberField_algebra_discr_ne_zero_iff_exists_place K e)

/-- Vanishing of a function-field algebra discriminant persists at every completion. -/
theorem rationalFunction_algebra_discr_eq_zero_iff_forall_place
    (F : Type u) [Field F] [Finite F]
    {B : Type w} [CommRing B] [Algebra (RatFunc F) B]
    [Module.Free (RatFunc F) B] [Module.Finite (RatFunc F) B]
    {ι : Type x} [Fintype ι] [DecidableEq ι] (e : Module.Basis ι (RatFunc F) B) :
    Algebra.discr (RatFunc F) e = 0 ↔ ∀ p : RationalFunctionPlace F,
      Algebra.discr (rationalFunctionCompletion F p)
        (e.baseChange (rationalFunctionCompletion F p) :
          Module.Basis ι (rationalFunctionCompletion F p)
            (rationalFunctionCompletion F p ⊗[RatFunc F] B)) = 0 := by
  simpa only [not_ne_iff] using not_iff_forall_not_of_iff_exists
    (rationalFunction_algebra_discr_ne_zero_iff_exists_place F e)

/-- A wrong finite-algebra trace over a number field persists at every completion. -/
theorem numberField_algebra_trace_ne_iff_forall_place
    (K : Type u) [Field K] [NumberField K]
    {B : Type w} [CommRing B] [Algebra K B] [Module.Free K B] [Module.Finite K B]
    (x : B) (c : K) :
    Algebra.trace K B x ≠ c ↔ ∀ p : NumberFieldPlace K,
      Algebra.trace (completion K p) (completion K p ⊗[K] B) (1 ⊗ₜ[K] x) ≠
        algebraMap K (completion K p) c :=
  not_iff_forall_not_of_iff_exists
    (numberField_algebra_trace_eq_iff_exists_place K x c)

/-- A wrong finite-algebra trace over a function field persists at every completion. -/
theorem rationalFunction_algebra_trace_ne_iff_forall_place
    (F : Type u) [Field F] [Finite F]
    {B : Type w} [CommRing B] [Algebra (RatFunc F) B]
    [Module.Free (RatFunc F) B] [Module.Finite (RatFunc F) B]
    (x : B) (c : RatFunc F) :
    Algebra.trace (RatFunc F) B x ≠ c ↔ ∀ p : RationalFunctionPlace F,
      Algebra.trace (rationalFunctionCompletion F p)
        (rationalFunctionCompletion F p ⊗[RatFunc F] B) (1 ⊗ₜ[RatFunc F] x) ≠
          algebraMap (RatFunc F) (rationalFunctionCompletion F p) c :=
  not_iff_forall_not_of_iff_exists
    (rationalFunction_algebra_trace_eq_iff_exists_place F x c)

end GaloisForLFunctions.HTGeometry.ABHN
