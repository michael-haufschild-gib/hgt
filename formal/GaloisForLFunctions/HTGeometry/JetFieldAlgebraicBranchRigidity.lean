import GaloisForLFunctions.HTGeometry.JetFieldIteratedConstantRigidity
import GaloisForLFunctions.HTGeometry.DifferentialAlgebraicDeriv

/-!
# Algebraic branch rigidity over a free differential field

Let `A` be the free differential rational field over a characteristic-zero field `C`.  In any
differential field extension of `A`, an element algebraic over `A` cannot have derivative equal to
a nonzero element of `C`.  If `C` is algebraically closed, the constants in the relative algebraic
closure of `A` are exactly `C`.  Consequently, no algebraic branch can differ from another branch
by a nonconstant polynomial drift: a positive iterated derivative can be a base constant only in
the zero case, and the original algebraic element must itself be a base constant.

The proof differentiates the minimal polynomial.  Divisibility by the minimal polynomial and the
strict degree drop force a coefficient identity.  The free-field constant-kernel theorem then
eliminates the putative constant drift.  No closure, branch-separation, or differential-Galois
hypothesis is assumed.
-/

open scoped Differential
open Polynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {C ι R : Type*} [Field C] [CharZero C] [Fintype ι]
  [Field R] [Algebra (JetField C ι) R] [Differential R]
  [DifferentialAlgebra (JetField C ι) R]

/-- An element algebraic over a free differential field cannot have nonzero base-constant
derivative. -/
theorem eq_zero_of_isAlgebraic_deriv_eq_base
    {x : R} (hx : IsAlgebraic (JetField C ι) x) {c : C}
    (hx' : x′ = algebraMap (JetField C ι) R (algebraMap C (JetField C ι) c)) :
    c = 0 := by
  let A := JetField C ι
  let p : A[X] := minpoly A x
  let cc : A := algebraMap C A c
  let q : A[X] := Differential.mapCoeffs p + Polynomial.C cc * derivative p
  have hp0 : p ≠ 0 := minpoly.ne_zero hx.isIntegral
  have hpd : 0 < p.natDegree := (minpoly.irreducible hx.isIntegral).natDegree_pos
  have hqeval : aeval x q = 0 := by
    have hchain := Differential.deriv_aeval_eq (A := A) x p
    have hprel : aeval x p = 0 := minpoly.aeval A x
    rw [hprel, map_zero, hx'] at hchain
    simpa only [q, cc, map_add, map_mul, aeval_C, mul_comm] using hchain.symm
  have hdvd : p ∣ q := minpoly.dvd A x hqeval
  have hpmonic : p.Monic := minpoly.monic hx.isIntegral
  have hmaple : (Differential.mapCoeffs p).natDegree ≤ p.natDegree - 1 := by
    rw [natDegree_le_iff_coeff_eq_zero]
    intro m hm
    rw [Differential.coeff_mapCoeffs]
    by_cases hmd : m = p.natDegree
    · rw [hmd, hpmonic.coeff_natDegree]
      exact Differential.deriv.map_one_eq_zero
    · have hlt : p.natDegree < m := by omega
      rw [coeff_eq_zero_of_natDegree_lt hlt, map_zero]
  have hderle : (Polynomial.C cc * derivative p).natDegree ≤ p.natDegree - 1 := by
    exact (natDegree_C_mul_le cc (derivative p)).trans
      (Nat.le_pred_of_lt (natDegree_derivative_lt (Nat.ne_zero_of_lt hpd)))
  have hqle : q.natDegree ≤ p.natDegree - 1 := by
    exact (natDegree_add_le _ _).trans (max_le hmaple hderle)
  have hqlt : q.natDegree < p.natDegree := by omega
  have hq0 : q = 0 := Polynomial.eq_zero_of_dvd_of_natDegree_lt hdvd hqlt
  have hcoeff := congrArg (fun r : A[X] ↦ r.coeff (p.natDegree - 1)) hq0
  have hpcoeff : p.coeff p.natDegree = 1 := hpmonic.coeff_natDegree
  have hdercoeff : (derivative p).coeff (p.natDegree - 1) = (p.natDegree : A) := by
    rw [coeff_derivative, show p.natDegree - 1 + 1 = p.natDegree by omega, hpcoeff, one_mul]
    have hcast : ((p.natDegree - 1 + 1 : ℕ) : A) = (p.natDegree : A) := by
      rw [Nat.sub_add_cancel (by omega)]
    simpa only [Nat.cast_add, Nat.cast_one] using hcast
  simp only [q, coeff_add, Differential.coeff_mapCoeffs, coeff_C_mul, coeff_zero,
    hdercoeff] at hcoeff
  have hdermem : (p.coeff (p.natDegree - 1))′ ∈
      (⊥ : IntermediateField C A) := by
    have hderEq : (p.coeff (p.natDegree - 1))′ =
        -(cc * (p.natDegree : A)) := by
      linear_combination hcoeff
    rw [hderEq]
    exact IntermediateField.neg_mem _ (IntermediateField.mul_mem _
      ((⊥ : IntermediateField C A).algebraMap_mem c)
      (IntermediateField.natCast_mem _ p.natDegree))
  have hcoeffmem : p.coeff (p.natDegree - 1) ∈
      (⊥ : IntermediateField C A) := mem_bot_of_deriv_mem_bot hdermem
  have hderzero : (p.coeff (p.natDegree - 1))′ = 0 := by
    simpa only [differentialJet_succ, differentialJet_zero] using
      (differentialJet_eq_zero_of_mem_bot (u := p.coeff (p.natDegree - 1))
        (n := 1) (by omega) hcoeffmem)
  rw [hderzero, zero_add] at hcoeff
  have hnat : (p.natDegree : A) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_zero_of_lt hpd)
  have hcc : cc = 0 := (mul_eq_zero.mp hcoeff).resolve_right hnat
  exact (algebraMap C A).injective (by simpa [cc] using hcc)

/-- Over an algebraically closed base, every algebraic constant in an extension of a free
differential field already comes from the base field. -/
theorem eq_algebraMap_of_isAlgebraic_deriv_eq_zero
    [IsAlgClosed C] [Algebra C R] [IsScalarTower C (JetField C ι) R]
    {x : R} (hx : IsAlgebraic (JetField C ι) x) (hx' : x′ = 0) :
    ∃ c : C, x = algebraMap C R c := by
  let A := JetField C ι
  let p : A[X] := minpoly A x
  let q : A[X] := Differential.mapCoeffs p
  have hp0 : p ≠ 0 := minpoly.ne_zero hx.isIntegral
  have hpd : 0 < p.natDegree := (minpoly.irreducible hx.isIntegral).natDegree_pos
  have hqeval : aeval x q = 0 := by
    have hchain := Differential.deriv_aeval_eq (A := A) x p
    have hprel : aeval x p = 0 := minpoly.aeval A x
    rw [hprel, map_zero, hx', mul_zero, add_zero] at hchain
    simpa only [q] using hchain.symm
  have hdvd : p ∣ q := minpoly.dvd A x hqeval
  have hpmonic : p.Monic := minpoly.monic hx.isIntegral
  have hqle : q.natDegree ≤ p.natDegree - 1 := by
    rw [natDegree_le_iff_coeff_eq_zero]
    intro m hm
    simp only [q, Differential.coeff_mapCoeffs]
    by_cases hmd : m = p.natDegree
    · rw [hmd, hpmonic.coeff_natDegree]
      exact Differential.deriv.map_one_eq_zero
    · have hlt : p.natDegree < m := by omega
      rw [coeff_eq_zero_of_natDegree_lt hlt, map_zero]
  have hqlt : q.natDegree < p.natDegree := by omega
  have hq0 : q = 0 := Polynomial.eq_zero_of_dvd_of_natDegree_lt hdvd hqlt
  have hcoeffrange : ∀ m, p.coeff m ∈ Set.range (algebraMap C A) := by
    intro m
    rw [← IntermediateField.mem_bot]
    apply mem_bot_of_deriv_mem_bot
    have hm := congrArg (fun r : A[X] ↦ r.coeff m) hq0
    have hmzero : (p.coeff m)′ = 0 := by
      simpa only [q, Differential.coeff_mapCoeffs, coeff_zero] using hm
    rw [hmzero]
    exact IntermediateField.zero_mem _
  obtain ⟨r : C[X], hr⟩ := (Polynomial.mem_map_range (algebraMap C A)).2 hcoeffrange
  have hrmap : r.map (algebraMap C A) = p := by
    simpa only [Polynomial.coe_mapRingHom] using hr
  have hr0 : r ≠ 0 := by
    intro hrzero
    apply hp0
    simpa only [hrzero, Polynomial.map_zero] using hrmap.symm
  have hreval : aeval x r = 0 := by
    rw [← Polynomial.aeval_map_algebraMap A x r, hrmap]
    exact minpoly.aeval A x
  have hxC : IsAlgebraic C x := ⟨r, hr0, hreval⟩
  let L := IntermediateField.adjoin C ({x} : Set R)
  letI : Algebra.IsAlgebraic C L :=
    IntermediateField.isAlgebraic_adjoin_simple hxC.isIntegral
  obtain ⟨c, hc⟩ := (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := C) (K := L)).2
    (IntermediateField.AdjoinSimple.gen C x)
  refine ⟨c, ?_⟩
  have hmap := congrArg (algebraMap L R) hc
  simpa only [L, IsScalarTower.algebraMap_apply C L R,
    IntermediateField.AdjoinSimple.algebraMap_gen] using hmap.symm

/-- Complete iterated branch-rigidity law: for an element algebraic over a free differential
field, a positive jet can be a base constant only if that constant is zero, and the original
element is itself a base constant. -/
theorem differentialJet_eq_base_of_isAlgebraic
    [IsAlgClosed C] [Algebra C R] [IsScalarTower C (JetField C ι) R]
    {x : R} (hx : IsAlgebraic (JetField C ι) x) {n : ℕ} (hn : 0 < n) {c : C}
    (hjet : differentialJet n x = algebraMap C R c) :
    c = 0 ∧ ∃ c₀ : C, x = algebraMap C R c₀ := by
  induction n generalizing x c with
  | zero => omega
  | succ n ih =>
      cases n with
      | zero =>
          have hx' : x′ = algebraMap C R c := by
            simpa only [differentialJet_succ, differentialJet_zero] using hjet
          have hc : c = 0 := eq_zero_of_isAlgebraic_deriv_eq_base hx (by
            simpa only [IsScalarTower.algebraMap_apply C (JetField C ι) R] using hx')
          subst c
          refine ⟨rfl, eq_algebraMap_of_isAlgebraic_deriv_eq_zero hx ?_⟩
          simpa only [map_zero] using hx'
      | succ n =>
          have hxalg : IsAlgebraic (JetField C ι) x′ :=
            GaloisForLFunctions.isAlgebraic_deriv hx
          have hshift : differentialJet (n + 1) x′ = algebraMap C R c := by
            rw [← hjet]
            simpa only [differentialJet_succ, differentialJet_zero] using
              (differentialJet_add (n + 1) 1 x).symm
          obtain ⟨hc, c₁, hx'c⟩ := ih (x := x′) hxalg (by omega) hshift
          have hc₁ : c₁ = 0 := eq_zero_of_isAlgebraic_deriv_eq_base hx (by
            simpa only [IsScalarTower.algebraMap_apply C (JetField C ι) R] using hx'c)
          refine ⟨hc, eq_algebraMap_of_isAlgebraic_deriv_eq_zero hx ?_⟩
          simpa only [hc₁, map_zero] using hx'c

end

end GaloisForLFunctions.HTGeometry
