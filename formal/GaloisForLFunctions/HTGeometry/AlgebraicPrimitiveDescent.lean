import GaloisForLFunctions.HTGeometry.SemilinearCircuitDescent
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Polynomial.Degree.SmallDegree

/-!
# Algebraic additive primitives descend to the base plus constants

Let several automorphisms preserve a field extension and send an algebraic
element `g` to `g + b_i`, with `b_i` in the base field.  Mapping the minimal
polynomial by the base automorphism and translating its variable by `b_i`
give the same monic polynomial.  Comparison of the second-highest
coefficient shows that

`g + nextCoeff(minpoly g) / natDegree(minpoly g)`

is fixed by every automorphism.  Thus, when the joint fixed field is the
declared constant field, `g` belongs to the base field plus a constant.

This is the algebraic-primitive half of the elementary several-automorphism
Ostrowski argument.  It requires neither a PPV torsor nor a fixed-field
Galois correspondence.
-/

open Polynomial

namespace GaloisForLFunctions

noncomputable section

/-- Translating the variable of a positive-degree monic polynomial changes
its second-highest coefficient by `degree * translation`. -/
theorem nextCoeff_taylor_of_monic
    {K : Type*} [Field K] [CharZero K]
    (P : K[X]) (hP : P.Monic) (hpos : 0 < P.natDegree) (r : K) :
    (P.taylor r).nextCoeff = P.nextCoeff + (P.natDegree : K) * r := by
  rw [nextCoeff, natDegree_taylor, if_neg hpos.ne']
  rw [taylor_coeff]
  have hHD : P.hasseDeriv (P.natDegree - 1) =
      C P.nextCoeff + C (P.natDegree : K) * X := by
    ext n
    rw [hasseDeriv_coeff]
    by_cases hn0 : n = 0
    · subst n
      simp [nextCoeff, hpos.ne']
    · by_cases hn1 : n = 1
      · subst n
        have hsum : 1 + (P.natDegree - 1) = P.natDegree := by omega
        have hd : P.natDegree = (P.natDegree - 1) + 1 := by omega
        rw [hsum, hP.coeff_natDegree, hd]
        simp only [Nat.add_sub_cancel, Nat.choose_succ_self_right, Nat.cast_add,
          Nat.cast_one, mul_one]
        simp
      · have hn2 : 2 ≤ n := by omega
        have hlt : P.natDegree < n + (P.natDegree - 1) := by omega
        rw [coeff_eq_zero_of_natDegree_lt hlt]
        simp only [coeff_add, coeff_C, hn0, if_false, zero_add, coeff_C_mul_X]
        simp [hn1]
  rw [hHD]
  simp

/-- Naturality of the minimal polynomial under compatible ring equivalences,
assuming only that the chosen element is integral rather than that the whole
extension is integral. -/
theorem minpoly_map_eq_of_ringEquiv_of_isIntegral
    {R A S T : Type*} [Field R] [Field A] [Field S] [Field T]
    [Algebra R S] [Algebra A T]
    {f : R ≃+* A} {g : S ≃+* T}
    (hcomp : (algebraMap A T).comp f =
      (g : S →+* T).comp (algebraMap R S))
    {x : S} (hx : IsIntegral R x) :
    (minpoly R x).map f = minpoly A (g x) := by
  refine minpoly.eq_of_irreducible_of_monic ?_ ?_ ?_
  · rw [← Polynomial.mapEquiv_apply, MulEquiv.irreducible_iff]
    exact minpoly.irreducible hx
  · simpa using
      (Polynomial.map_aeval_eq_aeval_map hcomp (minpoly R x) x).symm
  · exact (minpoly.monic hx).map _

/-- The trace coordinate of an algebraic additive primitive is jointly fixed
by all compatible automorphisms. -/
theorem algebraic_additive_primitive_traceCoordinate_jointFixed
    {I C K L : Type*} [Field C] [Field K] [Field L]
    [Algebra C K] [Algebra C L] [Algebra K L]
    [Differential K] [Differential L] [CharZero K]
    (SK : CommutingDifferenceDifferentialField I C K)
    (SL : CommutingDifferenceDifferentialField I C L)
    (hσ : ∀ i x, SL.aut i (algebraMap K L x) =
      algebraMap K L (SK.aut i x))
    {g : L} (hg : IsIntegral K g) (b : I → K)
    (hshift : ∀ i, SL.aut i g = g + algebraMap K L (b i)) :
    JointFixed SL
      (g + algebraMap K L
        ((minpoly K g).nextCoeff / ((minpoly K g).natDegree : K))) := by
  let P := minpoly K g
  have hPmonic : P.Monic := minpoly.monic hg
  have hPpos : 0 < P.natDegree := (minpoly.irreducible hg).natDegree_pos
  have hnK : (P.natDegree : K) ≠ 0 := Nat.cast_ne_zero.mpr hPpos.ne'
  intro i
  have hcomp : (algebraMap K L).comp (SK.aut i).toRingHom =
      (SL.aut i).toRingHom.comp (algebraMap K L) := by
    ext x
    exact (hσ i x).symm
  have hmap : P.map (SK.aut i).toRingHom = minpoly K (SL.aut i g) := by
    exact minpoly_map_eq_of_ringEquiv_of_isIntegral hcomp hg
  have hpoly : P.map (SK.aut i).toRingHom =
      P.comp (X - Polynomial.C (b i)) := by
    rw [hmap, hshift, minpoly.add_algebraMap]
  have hnext := congrArg Polynomial.nextCoeff hpoly
  rw [Polynomial.nextCoeff_map (SK.aut i).injective] at hnext
  have htaylor : P.comp (X - Polynomial.C (b i)) = P.taylor (-(b i)) := by
    simp [Polynomial.taylor_apply, sub_eq_add_neg]
  rw [htaylor, nextCoeff_taylor_of_monic P hPmonic hPpos] at hnext
  simp only [mul_neg] at hnext
  have hnext' : SK.aut i P.nextCoeff =
      P.nextCoeff + -(P.natDegree : K) * b i := by
    simpa using hnext
  have hfrac : b i + SK.aut i (P.nextCoeff / (P.natDegree : K)) =
      P.nextCoeff / (P.natDegree : K) := by
    rw [map_div₀ (SK.aut i), map_natCast, hnext']
    field_simp
    ring
  rw [map_add, hshift, hσ]
  simpa [P, add_assoc] using
    congrArg (fun z : K => g + algebraMap K L z) hfrac

/-- If the joint fixed field is the image of `C`, every algebraic additive
primitive belongs to the base field plus a constant. -/
theorem algebraic_additive_primitive_eq_base_add_constant
    {I C K L : Type*} [Field C] [Field K] [Field L]
    [Algebra C K] [Algebra C L] [Algebra K L]
    [Differential K] [Differential L] [CharZero K]
    (SK : CommutingDifferenceDifferentialField I C K)
    (SL : CommutingDifferenceDifferentialField I C L)
    (hσ : ∀ i x, SL.aut i (algebraMap K L x) =
      algebraMap K L (SK.aut i x))
    (hfixed : ∀ x : L, JointFixed SL x →
      ∃ c : C, algebraMap C L c = x)
    {g : L} (hg : IsIntegral K g) (b : I → K)
    (hshift : ∀ i, SL.aut i g = g + algebraMap K L (b i)) :
    ∃ k : K, ∃ c : C, g = algebraMap K L k + algebraMap C L c := by
  let t : K :=
    (minpoly K g).nextCoeff / ((minpoly K g).natDegree : K)
  have hfix : JointFixed SL (g + algebraMap K L t) :=
    algebraic_additive_primitive_traceCoordinate_jointFixed
      SK SL hσ hg b hshift
  obtain ⟨c, hc⟩ := hfixed (g + algebraMap K L t) hfix
  refine ⟨-t, c, ?_⟩
  rw [hc]
  simp [t]

end

end GaloisForLFunctions
