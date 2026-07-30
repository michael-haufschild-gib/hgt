import GaloisForLFunctions.HTGeometry.DirichletFormal
import Mathlib

/-!
# Coefficient-first Dirichlet series and their leading terms

A Dirichlet series with polynomial coefficients can be written either as an arithmetic function
valued in `C[X]` or, when the degrees are bounded, as a polynomial in the coordinate valued in
arithmetic functions.  The second form is the one an analytic realisation produces, because there
the coordinate is adjoined to a ring of Dirichlet germs.

The comparison map

`Psi : Polynomial (ArithmeticFunction C) -> ArithmeticFunction (C[X])`,
`Psi P m = sum_j (P.coeff j m) X^j`,

is a ring homomorphism: on monomials it is exactly the statement that Dirichlet convolution of the
coefficient streams matches the convolution of the associated `C[X]`-valued streams.  Transporting
along `Psi` carries the whole leading-term theory of `DirFormal` to the coefficient-first form.
-/

open Polynomial ArithmeticFunction

namespace HTGeometry

/-- Dirichlet series with polynomial coefficients, written coefficient-first. -/
abbrev DirPoly := Polynomial (ArithmeticFunction ℂ)

namespace DirPoly

/-- The `m`-th Dirichlet coefficient of a coefficient-first series, as a polynomial. -/
noncomputable def coeffPoly (P : DirPoly) (m : ℕ) : ℂ[X] :=
  P.sum fun j a => Polynomial.C (a m) * X ^ j

@[simp] theorem coeffPoly_zero (m : ℕ) : coeffPoly 0 m = 0 := by
  simp [coeffPoly]

@[simp] theorem coeffPoly_monomial (j : ℕ) (a : ArithmeticFunction ℂ) (m : ℕ) :
    coeffPoly (Polynomial.monomial j a) m = Polynomial.C (a m) * X ^ j := by
  classical
  rw [coeffPoly, Polynomial.sum_monomial_index]
  simp

theorem coeffPoly_add (P Q : DirPoly) (m : ℕ) :
    coeffPoly (P + Q) m = coeffPoly P m + coeffPoly Q m := by
  classical
  simp only [coeffPoly]
  rw [Polynomial.sum_add_index] <;> intros <;> simp [add_mul]

theorem coeffPoly_one (m : ℕ) :
    coeffPoly (1 : DirPoly) m = if m = 1 then 1 else 0 := by
  classical
  have h1 : (1 : DirPoly) = Polynomial.monomial 0 (1 : ArithmeticFunction ℂ) := by
    simp [Polynomial.monomial_zero_left]
  rw [h1, coeffPoly_monomial]
  by_cases h : m = 1 <;> simp [h, ArithmeticFunction.one_apply]

/-- **The comparison map is multiplicative.** -/
theorem coeffPoly_mul (P Q : DirPoly) (m : ℕ) :
    coeffPoly (P * Q) m
      = ∑ x ∈ m.divisorsAntidiagonal, coeffPoly P x.1 * coeffPoly Q x.2 := by
  classical
  induction P using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [add_mul, coeffPoly_add, hp, hq, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun x _ => by rw [coeffPoly_add, add_mul]
  | monomial j1 f =>
      induction Q using Polynomial.induction_on' with
      | add p q hp hq =>
          rw [mul_add, coeffPoly_add, hp, hq, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun x _ => by rw [coeffPoly_add, mul_add]
      | monomial j2 g =>
          rw [Polynomial.monomial_mul_monomial]
          simp only [coeffPoly_monomial, ArithmeticFunction.mul_apply]
          rw [map_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [map_mul, pow_add]
          ring

theorem coeffPoly_coeff (P : DirPoly) (m j : ℕ) :
    (coeffPoly P m).coeff j = (P.coeff j) m := by
  classical
  induction P using Polynomial.induction_on' with
  | add p q hp hq => rw [coeffPoly_add, Polynomial.coeff_add, hp, hq]; simp
  | monomial j' a =>
      rw [coeffPoly_monomial, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
        Polynomial.coeff_monomial]
      by_cases h : j = j'
      · simp [h]
      · simp [h, Ne.symm h]

@[simp] theorem coeffPoly_zero_index (P : DirPoly) : coeffPoly P 0 = 0 := by
  ext j
  rw [coeffPoly_coeff]
  simp

/-- The comparison ring homomorphism into the coefficient-in-`C[X]` form. -/
noncomputable def toDirFormal : DirPoly →+* DirFormal where
  toFun P := ⟨fun m => coeffPoly P m, by simp⟩
  map_one' := by
    refine ArithmeticFunction.ext fun m => ?_
    show coeffPoly (1 : DirPoly) m = _
    rw [coeffPoly_one, ArithmeticFunction.one_apply]
  map_mul' P Q := by
    refine ArithmeticFunction.ext fun m => ?_
    show coeffPoly (P * Q) m = _
    rw [ArithmeticFunction.mul_apply]
    exact coeffPoly_mul P Q m
  map_zero' := by refine ArithmeticFunction.ext fun m => ?_; simp
  map_add' P Q := by
    refine ArithmeticFunction.ext fun m => ?_
    show coeffPoly (P + Q) m = _
    rw [coeffPoly_add]
    rfl

@[simp] theorem toDirFormal_apply (P : DirPoly) (m : ℕ) :
    toDirFormal P m = coeffPoly P m := rfl

theorem toDirFormal_injective : Function.Injective toDirFormal := by
  intro P Q h
  ext j m
  have hm := congrArg (fun F : DirFormal => F m) h
  simp only [toDirFormal_apply] at hm
  have := congrArg (fun p : ℂ[X] => p.coeff j) hm
  simpa [coeffPoly_coeff] using this

/-- Dividing the `m`-th Dirichlet coefficient by `m`: the coefficient-side form of translating the
argument by one. -/
noncomputable def dshiftFun (f : ArithmeticFunction ℂ) : ArithmeticFunction ℂ :=
  ⟨fun m => f m / (m : ℂ), by simp⟩

@[simp] theorem dshiftFun_apply (f : ArithmeticFunction ℂ) (m : ℕ) :
    dshiftFun f m = f m / (m : ℂ) := rfl

noncomputable def dshift : ArithmeticFunction ℂ ≃+* ArithmeticFunction ℂ where
  toFun := dshiftFun
  invFun f := ⟨fun m => f m * (m : ℂ), by simp⟩
  left_inv f := by
    refine ArithmeticFunction.ext fun m => ?_
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · have : ((m : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      show f m / (m : ℂ) * (m : ℂ) = f m
      field_simp
  right_inv f := by
    refine ArithmeticFunction.ext fun m => ?_
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · have : ((m : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      show f m * (m : ℂ) / (m : ℂ) = f m
      field_simp
  map_add' f g := by refine ArithmeticFunction.ext fun m => ?_; simp [add_div]
  map_mul' f g := by
    classical
    refine ArithmeticFunction.ext fun m => ?_
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    show (f * g) m / (m : ℂ) = ((dshiftFun f) * (dshiftFun g)) m
    rw [ArithmeticFunction.mul_apply, ArithmeticFunction.mul_apply, Finset.sum_div]
    refine Finset.sum_congr rfl fun x hx => ?_
    obtain ⟨hxn, hn0⟩ := Nat.mem_divisorsAntidiagonal.mp hx
    have hx1 : ((x.1 : ℂ)) ≠ 0 := by
      refine Nat.cast_ne_zero.mpr fun h0 => hn0 ?_
      rw [← hxn, h0, zero_mul]
    have hx2 : ((x.2 : ℂ)) ≠ 0 := by
      refine Nat.cast_ne_zero.mpr fun h0 => hn0 ?_
      rw [← hxn, h0, mul_zero]
    show f x.1 * g x.2 / (m : ℂ) = (f x.1 / (x.1 : ℂ)) * (g x.2 / (x.2 : ℂ))
    rw [← hxn]
    push_cast
    field_simp

/-- The shift on coefficient-first series: divide by the index and translate the coordinate. -/
noncomputable def sigmaDirPoly : DirPoly ≃+* DirPoly where
  toFun P := (P.map (dshift : ArithmeticFunction ℂ →+* ArithmeticFunction ℂ)).comp (X + 1)
  invFun P := (P.map (dshift.symm : ArithmeticFunction ℂ →+* ArithmeticFunction ℂ)).comp (X - 1)
  left_inv P := by
    simp only [Polynomial.map_comp, Polynomial.map_map, Polynomial.map_add, Polynomial.map_sub,
      Polynomial.map_X, Polynomial.map_one]
    rw [show ((dshift.symm : ArithmeticFunction ℂ →+* ArithmeticFunction ℂ).comp
      (dshift : ArithmeticFunction ℂ →+* ArithmeticFunction ℂ))
      = RingHom.id _ from by ext x; simp]
    rw [Polynomial.map_id, Polynomial.comp_assoc]
    rw [show ((X + 1 : DirPoly).comp (X - 1)) = X by
      simp only [Polynomial.add_comp, Polynomial.X_comp, Polynomial.one_comp]
      ring, Polynomial.comp_X]
  right_inv P := by
    simp only [Polynomial.map_comp, Polynomial.map_map, Polynomial.map_add, Polynomial.map_sub,
      Polynomial.map_X, Polynomial.map_one]
    rw [show ((dshift : ArithmeticFunction ℂ →+* ArithmeticFunction ℂ).comp
      (dshift.symm : ArithmeticFunction ℂ →+* ArithmeticFunction ℂ))
      = RingHom.id _ from by ext x; simp]
    rw [Polynomial.map_id, Polynomial.comp_assoc]
    rw [show ((X - 1 : DirPoly).comp (X + 1)) = X by
      simp only [Polynomial.sub_comp, Polynomial.X_comp, Polynomial.one_comp]
      ring, Polynomial.comp_X]
  map_add' P Q := by simp [Polynomial.map_add, Polynomial.add_comp]
  map_mul' P Q := by simp [Polynomial.map_mul, Polynomial.mul_comp]

theorem coeffPoly_map_dshift (P : DirPoly) (m : ℕ) :
    coeffPoly (P.map (dshift : ArithmeticFunction ℂ →+* ArithmeticFunction ℂ)) m
      = Polynomial.C ((m : ℂ))⁻¹ * coeffPoly P m := by
  classical
  induction P using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [Polynomial.map_add, coeffPoly_add, hp, hq, coeffPoly_add, mul_add]
  | monomial j a =>
      rw [Polynomial.map_monomial, coeffPoly_monomial, coeffPoly_monomial]
      show Polynomial.C (a m / (m : ℂ)) * X ^ j = _
      rw [div_eq_inv_mul, Polynomial.C_mul]
      ring

theorem coeffPoly_mul_X_add_one (Q : DirPoly) (m : ℕ) :
    coeffPoly (Q * (X + 1)) m = coeffPoly Q m * (X + 1) := by
  classical
  rw [coeffPoly_mul]
  have hone : ∀ b : ℕ, coeffPoly ((X : DirPoly) + 1) b
      = (if b = 1 then (1 : ℂ[X]) else 0) * (X + 1) := by
    intro b
    rw [coeffPoly_add, coeffPoly_one]
    have hX : (X : DirPoly) = Polynomial.monomial 1 1 := by
      simp [Polynomial.monomial_one_one_eq_X]
    rw [hX, coeffPoly_monomial, ArithmeticFunction.one_apply]
    by_cases h : b = 1 <;> simp [h]
  rw [Finset.sum_congr rfl (fun x _ => by rw [hone x.2])]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  rw [Finset.sum_eq_single (m, 1)]
  · simp
  · rintro x hx hne
    obtain ⟨hxn, -⟩ := Nat.mem_divisorsAntidiagonal.mp hx
    have hx2 : x.2 ≠ 1 := by
      intro h2
      exact hne (Prod.ext (by rw [h2, mul_one] at hxn; exact hxn) h2)
    simp [hx2]
  · intro hmem
    exact absurd (Nat.mem_divisorsAntidiagonal.mpr ⟨by simp, by omega⟩) hmem

theorem coeffPoly_comp_X_add_one (P : DirPoly) (m : ℕ) :
    coeffPoly (P.comp (X + 1)) m = (coeffPoly P m).comp (X + 1) := by
  classical
  induction P using Polynomial.induction_on' with
  | add p q hp hq => rw [Polynomial.add_comp, coeffPoly_add, hp, hq, coeffPoly_add,
      Polynomial.add_comp]
  | monomial j a =>
      rw [coeffPoly_monomial, Polynomial.mul_comp, Polynomial.C_comp, Polynomial.X_pow_comp]
      induction j with
      | zero =>
          rw [Polynomial.monomial_zero_left, Polynomial.C_comp, pow_zero, mul_one]
          have h0 : (Polynomial.C a : DirPoly) = Polynomial.monomial 0 a :=
            by rw [Polynomial.monomial_zero_left]
          conv_lhs => rw [h0]
          rw [coeffPoly_monomial]
          simp
      | succ j ih =>
          have hstep : (Polynomial.monomial (j + 1) a : DirPoly).comp (X + 1)
              = ((Polynomial.monomial j a : DirPoly).comp (X + 1)) * (X + 1) := by
            rw [← Polynomial.C_mul_X_pow_eq_monomial, ← Polynomial.C_mul_X_pow_eq_monomial]
            simp only [pow_succ, Polynomial.mul_comp, Polynomial.C_comp,
              Polynomial.X_pow_comp, Polynomial.X_comp, Polynomial.one_comp]
            ring
          rw [hstep, coeffPoly_mul_X_add_one, ih, pow_succ]
          ring

/-- **The comparison map intertwines the two shifts.** -/
theorem toDirFormal_sigma (P : DirPoly) :
    toDirFormal (sigmaDirPoly P) = DirFormal.sigmaEquiv (toDirFormal P) := by
  refine ArithmeticFunction.ext fun m => ?_
  show coeffPoly (sigmaDirPoly P) m = _
  rw [DirFormal.sigmaEquiv_apply, toDirFormal_apply]
  show coeffPoly ((P.map (dshift : ArithmeticFunction ℂ →+* ArithmeticFunction ℂ)).comp (X + 1)) m
    = _
  rw [coeffPoly_comp_X_add_one, coeffPoly_map_dshift, Polynomial.mul_comp, Polynomial.C_comp]

/-- The index-one embedding of the polynomial ring into coefficient-first series. -/
noncomputable def embDirPoly : ℂ[X] →+* DirPoly :=
  Polynomial.mapRingHom (algebraMap ℂ (ArithmeticFunction ℂ))

theorem toDirFormal_emb (p : ℂ[X]) :
    toDirFormal (embDirPoly p) = DirFormal.embHom p := by
  classical
  refine ArithmeticFunction.ext fun m => ?_
  show coeffPoly (p.map (algebraMap ℂ (ArithmeticFunction ℂ))) m = _
  rw [DirFormal.embHom_apply]
  have hval : ∀ c : ℂ, (algebraMap ℂ (ArithmeticFunction ℂ) c) m
      = c * (if m = 1 then 1 else 0) := by
    intro c
    rw [Algebra.algebraMap_eq_smul_one]
    show c • (1 : ArithmeticFunction ℂ) m = _
    rw [ArithmeticFunction.one_apply]
    simp [smul_eq_mul]
  induction p using Polynomial.induction_on' with
  | add u v hu hv =>
      rw [Polynomial.map_add, coeffPoly_add, hu, hv]
      by_cases h : m = 1 <;> simp [h]
  | monomial j c =>
      rw [Polynomial.map_monomial, coeffPoly_monomial, hval]
      by_cases h : m = 1
      · simp [h, ← Polynomial.C_mul_X_pow_eq_monomial]
      · simp [h]

/-- **The leading-term interface on coefficient-first Dirichlet series.** -/
noncomputable def dirichletLeadPoly : DirichletLead DirPoly :=
  DirichletLead.comap DirFormal.dirichletLead toDirFormal toDirFormal_injective
    sigmaDirPoly toDirFormal_sigma embDirPoly toDirFormal_emb

end DirPoly

end HTGeometry
