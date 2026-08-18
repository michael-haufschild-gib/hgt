import GaloisForLFunctions.HTGeometry.PolynomialEtaleLocallyNilpotentDomain
import GaloisForLFunctions.HTGeometry.PolynomialFibreQuotientBasis
import GaloisForLFunctions.HTGeometry.LocallyNilpotentDerivationSlice

/-!
# The étale rank-one property, and its inductive step in one variable

```text
HasEtaleRankOne R :  every domain finite free over R with unit discriminant has rank one
```

Two theorems:

* `hasEtaleRankOne_isAlgClosed` — an algebraically closed field has the property: a finite algebra
  of rank `n` with nonzero discriminant carries `n` jointly surjective maps to the field, so it is
  `Kⁿ`, which is a domain only for `n = 1`.
* `hasEtaleRankOne_polynomial` — the property passes from `R` to `R[X]`, for any characteristic-zero
  domain `R` containing `ℚ`.

The inductive step is the `𝔸¹`-invariance of finite étale covers.  Let `B` be a domain, finite free
over `R[X]` with unit discriminant.  Its unique derivation lifting `d/dX` is locally nilpotent
(`PolynomialEtaleLocallyNilpotentDomain`) and sends the parameter to `1`, so the slice theorem makes
`B` the polynomial ring over its ring of constants `C = ker ∂`.  Reduction mod the parameter is then
an isomorphism from `C` onto the fibre `B ⧸ (w)`: surjective because `aeval w p ≡ p.coeff 0`, and
injective because `C c = X * q` forces `c = 0`.  So the fibre is a domain; it is finite free of the
same rank over `R` with unit discriminant (`PolynomialFibreQuotientBasis`), and the induction
hypothesis applies.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial Lift

set_option maxHeartbeats 3200000
set_option linter.unusedSectionVars false

universe u

/-- A ring has the **étale rank-one property** if every domain that is finite free over it with
unit discriminant has rank one. -/
def HasEtaleRankOne (R : Type u) [CommRing R] : Prop :=
  ∀ {B : Type u} [CommRing B] [IsDomain B] [Algebra R B] [Module.Free R B] [Module.Finite R B]
    {n : ℕ}, 1 ≤ n → ∀ (e : Module.Basis (Fin n) R B), IsUnit (Algebra.discr R e) → n = 1

theorem hasEtaleRankOne_polynomial (R : Type u) [CommRing R] [IsDomain R] [CharZero R]
    [Algebra ℚ R] (h : HasEtaleRankOne R) : HasEtaleRankOne R[X] := by
  intro B _ _ _ _ _ n hn e hd
  letI algRB : Algebra R B := ((algebraMap R[X] B).comp (algebraMap R R[X])).toAlgebra
  haveI towerRB : IsScalarTower R R[X] B := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI algQB : Algebra ℚ B := ((algebraMap R B).comp (algebraMap ℚ R)).toAlgebra
  haveI towerQRB : IsScalarTower ℚ R B := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  set dB : Derivation R B B := liftDerivation e hd (polyDeriv R) with hdBdef
  set dQ : Derivation ℚ B B := dB.restrictScalars ℚ with hdQdef
  have hs : dQ (param R B) = 1 := by
    show dB (algebraMap R[X] B X) = 1
    rw [hdBdef, liftDerivation_algebraMap e hd (polyDeriv R) X]
    show algebraMap R[X] B (Polynomial.derivative X) = 1
    rw [Polynomial.derivative_X, map_one]
  have hnil : ∀ b : B, ∃ N, (⇑dQ)^[N] b = 0 := by
    intro b
    obtain ⟨N, hN⟩ := locallyNilpotent_liftDerivation_domain e hd b
    exact ⟨N, hN⟩
  have hbij := bijective_aeval_of_locallyNilpotent dQ hs hnil
  set C := derivationKernel dQ with hCdef
  set w : B := param R B with hwdef
  have hmkw : Ideal.Quotient.mk (Ideal.span {w}) w = 0 := param_mk_eq_zero
  have hsurjC : ∀ b : B, ∃ c : C,
      Ideal.Quotient.mk (Ideal.span {w}) (c : B) = Ideal.Quotient.mk (Ideal.span {w}) b := by
    intro b
    obtain ⟨p, hp⟩ := hbij.2 b
    refine ⟨p.coeff 0, ?_⟩
    obtain ⟨q, hq⟩ : (Polynomial.X : Polynomial C) ∣ (p - Polynomial.C (p.coeff 0)) := by
      rw [Polynomial.X_dvd_iff]
      simp
    have hpsplit : p = Polynomial.C (p.coeff 0) + Polynomial.X * q := by linear_combination hq
    have hb : b = ((p.coeff 0 : C) : B) + w * Polynomial.aeval w q := by
      rw [← hp]
      conv_lhs => rw [hpsplit]
      rw [map_add, map_mul, Polynomial.aeval_C, Polynomial.aeval_X]
      rfl
    rw [hb, map_add, map_mul, hmkw, zero_mul, add_zero]
  have hinjC : ∀ c : C, Ideal.Quotient.mk (Ideal.span {w}) (c : B) = 0 → (c : B) = 0 := by
    intro c hc
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at hc
    obtain ⟨y, hy⟩ := hc
    obtain ⟨q, hq⟩ := hbij.2 y
    have h1 : Polynomial.aeval w (Polynomial.C c) = Polynomial.aeval w (Polynomial.X * q) := by
      rw [Polynomial.aeval_C, map_mul, Polynomial.aeval_X, hq]
      exact hy
    have h2 : (Polynomial.C c : Polynomial C) = Polynomial.X * q := hbij.1 h1
    have h3 := congrArg (fun r : Polynomial C => r.coeff 0) h2
    simp only [Polynomial.coeff_C_zero, Polynomial.coeff_X_mul_zero] at h3
    rw [h3]
    rfl
  haveI hntQ : Nontrivial (fibreQuot R B) := by
    refine ⟨⟨1, 0, ?_⟩⟩
    intro h1
    have h2 : Ideal.Quotient.mk (Ideal.span {w}) ((1 : C) : B) = 0 := by
      rw [show ((1 : C) : B) = (1 : B) from rfl, map_one]
      exact h1
    have hone : (1 : B) = 0 := hinjC 1 h2
    exact one_ne_zero hone
  haveI hnzd : NoZeroDivisors (fibreQuot R B) := by
    constructor
    intro a b hab
    obtain ⟨a', rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨b', rfl⟩ := Ideal.Quotient.mk_surjective b
    obtain ⟨ca, hca⟩ := hsurjC a'
    obtain ⟨cb, hcb⟩ := hsurjC b'
    have hprod : Ideal.Quotient.mk (Ideal.span {w}) ((ca * cb : C) : B) = 0 := by
      rw [show ((ca * cb : C) : B) = (ca : B) * (cb : B) from rfl, map_mul, hca, hcb, ← map_mul]
      exact hab
    have hz : ((ca * cb : C) : B) = 0 := hinjC _ hprod
    have hz2 : (ca : B) * (cb : B) = 0 := hz
    rcases mul_eq_zero.mp hz2 with h | h
    · left
      rw [← hca, h, map_zero]
    · right
      rw [← hcb, h, map_zero]
  haveI : IsDomain (fibreQuot R B) := NoZeroDivisors.to_isDomain _
  haveI : Module.Free R (fibreQuot R B) := Module.Free.of_basis (fibreBasis e)
  haveI : Module.Finite R (fibreQuot R B) := Module.Finite.of_basis (fibreBasis e)
  have hdQuot : IsUnit (Algebra.discr R (fibreBasis e)) := by
    rw [discr_fibreBasis e]
    obtain ⟨c, hc, hce⟩ := Polynomial.isUnit_iff.mp hd
    rw [← hce]
    simpa using hc
  exact h hn (fibreBasis e) hdQuot


/-- **The base case: an algebraically closed field has the étale rank-one property.** -/
theorem hasEtaleRankOne_isAlgClosed (K : Type u) [Field K] [IsAlgClosed K] :
    HasEtaleRankOne K := by
  intro B _ _ _ _ _ n hn e hd
  classical
  obtain ⟨χ, hsurj, -⟩ := exists_algHom_family_of_discr_ne_zero e hd.ne_zero
  haveI : Module.Finite K B := Module.Finite.of_basis e
  have hfr : Module.finrank K B = Module.finrank K (Fin n → K) := by
    rw [Module.finrank_eq_card_basis e, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  have hinj : Function.Injective (AlgHom.pi χ) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfr
      (f := (AlgHom.pi χ).toLinearMap)).mpr hsurj
  by_contra hne
  have hn2 : 2 ≤ n := by omega
  set i0 : Fin n := ⟨0, by omega⟩ with hi0
  set i1 : Fin n := ⟨1, by omega⟩ with hi1
  have hne01 : i0 ≠ i1 := by
    rw [hi0, hi1]
    exact fun hcon => absurd (congrArg Fin.val hcon) (by norm_num)
  obtain ⟨x, hx⟩ := hsurj (fun i => if i = i0 then 1 else 0)
  obtain ⟨y, hy⟩ := hsurj (fun i => if i = i1 then 1 else 0)
  have hxv : ∀ i, χ i x = if i = i0 then 1 else 0 := fun i => congrFun hx i
  have hyv : ∀ i, χ i y = if i = i1 then 1 else 0 := fun i => congrFun hy i
  have hxy : x * y = 0 := by
    apply hinj
    rw [map_mul, map_zero]
    funext i
    show χ i x * χ i y = 0
    rw [hxv i, hyv i]
    by_cases hi : i = i0
    · rw [if_pos hi, if_neg (by rw [hi]; exact hne01), mul_zero]
    · rw [if_neg hi, zero_mul]
  have hx0 : x ≠ 0 := by
    intro h
    have := hxv i0
    rw [h, map_zero, if_pos rfl] at this
    exact one_ne_zero this.symm
  have hy0 : y ≠ 0 := by
    intro h
    have := hyv i1
    rw [h, map_zero, if_pos rfl] at this
    exact one_ne_zero this.symm
  rcases mul_eq_zero.mp hxy with h | h
  · exact hx0 h
  · exact hy0 h

end GaloisForLFunctions.HTGeometry
