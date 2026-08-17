import GaloisForLFunctions.HTGeometry.JetWeightPartial
import GaloisForLFunctions.HTGeometry.JetWeightZeroCoordinates
import GaloisForLFunctions.HTGeometry.JetOrderRelationSlicing

/-!
# The weighted action on a slice

The weighted torus preserves every prefix field, so it acts on the coefficients of a slice.  On a
slice in a *weight-zero* coordinate — a ratio `y_k/y₁^k`, which the torus fixes — the action is
exactly the coefficientwise one, and a torus-invariant element therefore has torus-invariant
numerator and denominator up to a common scalar; normalizing the denominator makes every coefficient
invariant.

The consequence used downstream is the bottom of the weight-zero tower: a torus-invariant element of
jet order at most one is a rational function of the free generator alone.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

variable {C : Type*} [Field C] [CharZero C]

/-- Invariance under the weighted action of the scalar two.  In characteristic zero this single
scalar already forces the whole slicing structure, so it is the working form of torus invariance. -/
def IsWeightZero (v : JetField C Unit) : Prop :=
  weightScale (show (2 : C) ≠ 0 from two_ne_zero) v = v

theorem isWeightZero_jetRatio (j : ℕ) : IsWeightZero (jetRatio j : JetField C Unit) :=
  weightScale_jetRatio _ j

theorem isWeightZero_substitutionDeriv (R : RatFunc C) : IsWeightZero (substitutionDeriv R) :=
  weightScale_substitutionDeriv _ R

theorem IsWeightZero.mul {a b : JetField C Unit} (ha : IsWeightZero a) (hb : IsWeightZero b) :
    IsWeightZero (a * b) := by
  show weightScale _ (a * b) = a * b
  rw [map_mul, ha, hb]

theorem IsWeightZero.inv {a : JetField C Unit} (ha : IsWeightZero a) : IsWeightZero a⁻¹ := by
  show weightScale _ a⁻¹ = a⁻¹
  rw [map_inv₀, ha]

theorem IsWeightZero.add {a b : JetField C Unit} (ha : IsWeightZero a) (hb : IsWeightZero b) :
    IsWeightZero (a + b) := by
  show weightScale _ (a + b) = a + b
  rw [map_add, ha, hb]

theorem IsWeightZero.neg {a : JetField C Unit} (ha : IsWeightZero a) : IsWeightZero (-a) := by
  show weightScale _ (-a) = -a
  rw [map_neg, ha]

theorem isWeightZero_algebraMap (e : C) :
    IsWeightZero (algebraMap C (JetField C Unit) e) := by
  show weightScale _ (algebraMap C (JetField C Unit) e) = algebraMap C (JetField C Unit) e
  rw [AlgEquiv.commutes]

/-- The weighted action restricted to a prefix field. -/
def weightScalePrefixHom {lam : C} (h : lam ≠ 0) (k : ℕ) :
    ↥(jetPrefixField C k) →ₐ[C] ↥(jetPrefixField C k) where
  toFun z := ⟨weightScale h (z : JetField C Unit), weightScale_mem_jetPrefixField h k z.2⟩
  map_one' := by
    refine Subtype.ext ?_
    show weightScale h (1 : JetField C Unit) = 1
    rw [map_one]
  map_mul' x y := by
    refine Subtype.ext ?_
    show weightScale h ((x : JetField C Unit) * y) = weightScale h x * weightScale h y
    rw [map_mul]
  map_zero' := by
    refine Subtype.ext ?_
    show weightScale h (0 : JetField C Unit) = 0
    rw [map_zero]
  map_add' x y := by
    refine Subtype.ext ?_
    show weightScale h ((x : JetField C Unit) + y) = weightScale h x + weightScale h y
    rw [map_add]
  commutes' c := by
    refine Subtype.ext ?_
    show weightScale h (algebraMap C (JetField C Unit) c) = algebraMap C (JetField C Unit) c
    rw [AlgEquiv.commutes]

theorem weightScalePrefixHom_algebraMap {lam : C} (h : lam ≠ 0) (k : ℕ)
    (z : ↥(jetPrefixField C k)) :
    algebraMap ↥(jetPrefixField C k) (JetField C Unit) (weightScalePrefixHom h k z)
      = weightScale h (algebraMap ↥(jetPrefixField C k) (JetField C Unit) z) := rfl

/-- **The weighted action on a polynomial expression.** -/
theorem weightScale_aeval {lam : C} (h : lam ≠ 0) (k : ℕ) (x : JetField C Unit)
    (P : Polynomial ↥(jetPrefixField C k)) :
    weightScale h (Polynomial.aeval x P)
      = Polynomial.aeval (weightScale h x)
        (P.map (weightScalePrefixHom h k).toRingHom) := by
  induction P using Polynomial.induction_on with
  | C a =>
      rw [Polynomial.aeval_C, Polynomial.map_C, Polynomial.aeval_C]
      exact (weightScalePrefixHom_algebraMap h k a).symm
  | add p q hp hq =>
      rw [map_add, map_add, Polynomial.map_add, map_add, hp, hq]
  | monomial n a _ =>
      rw [map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X, map_mul, map_pow,
        Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X, map_mul,
        map_pow, Polynomial.aeval_C, Polynomial.aeval_X]
      congr 1

/-! ## The bottom of the weight-zero tower -/

/-- The weighted action is trivial on the order-zero prefix field. -/
theorem weightScale_eq_of_mem_prefix_one {lam : C} (h : lam ≠ 0)
    (z : ↥(jetPrefixField C 1)) :
    weightScale h (z : JetField C Unit) = (z : JetField C Unit) := by
  have hord : ∀ j : ℕ, 0 < j → JetField.pd ((), j) (z : JetField C Unit) = 0 := by
    intro j hj
    exact (mem_jetPrefixField_iff 1 _).mp z.2 j (by omega)
  obtain ⟨Q, hQ⟩ := exists_ratFunc_of_order_zero hord
  rw [← hQ]
  exact weightScale_ratFuncEval h Q

/-- **A torus-invariant element of jet order at most one has jet order zero.** -/
theorem pd_one_eq_zero_of_isWeightZero {v : JetField C Unit} (hv : IsWeightZero v)
    (hord : ∀ j : ℕ, 1 < j → JetField.pd ((), j) v = 0) :
    JetField.pd ((), 1) v = 0 := by
  classical
  have htwo : (2 : C) ≠ 0 := two_ne_zero
  set x : JetField C Unit := JetField.jet ((), 1) with hxdef
  have hx0 : x ≠ 0 := jet_ne_zero _
  have hxtr : Transcendental (jetPrefixField C 1) x := transcendental_jet_over_jetPrefixField 1
  have hinj : Function.Injective (Polynomial.aeval (R := ↥(jetPrefixField C 1)) x) :=
    transcendental_iff_injective.mp hxtr
  have hmemadj : v ∈ IntermediateField.adjoin (jetPrefixField C 1)
    ({x} : Set (JetField C Unit)) := mem_adjoin_jet_of_order hord
  set f : RatFunc ↥(jetPrefixField C 1) :=
    (RatFunc.algEquivOfTranscendental x hxtr).symm ⟨v, hmemadj⟩ with hfdef
  have hxeval : ratFuncEval x hxtr f = v := by
    simp only [ratFuncEval, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, hfdef,
      AlgEquiv.apply_symm_apply]
    rfl
  set P : Polynomial ↥(jetPrefixField C 1) := f.num with hPdef
  set Q : Polynomial ↥(jetPrefixField C 1) := f.denom with hQdef
  have hQ0 : Q ≠ 0 := RatFunc.denom_ne_zero f
  have hQm : Q.Monic := RatFunc.monic_denom f
  have hcop : IsCoprime P Q := RatFunc.isCoprime_num_denom f
  have hQy : Polynomial.aeval x Q ≠ 0 := fun hh => hQ0 (hinj (by simpa using hh))
  have hvdiv : v = Polynomial.aeval x P / Polynomial.aeval x Q := by
    rw [← hxeval, ratFuncEval_eq_div]
  set ρ2 : ↥(jetPrefixField C 1) := algebraMap C ↥(jetPrefixField C 1) 2 with hρ2def
  have hρ2 : ρ2 ≠ 0 := by
    rw [hρ2def]
    intro hh
    exact htwo ((algebraMap C ↥(jetPrefixField C 1)).injective (by rw [hh, map_zero]))
  set sc : Polynomial ↥(jetPrefixField C 1) := Polynomial.C ρ2 * Polynomial.X with hscdef
  have hscdeg : sc.natDegree = 1 := natDegree_scaleSubst hρ2
  have hmapid : ∀ Pp : Polynomial ↥(jetPrefixField C 1),
      Pp.map (weightScalePrefixHom htwo 1).toRingHom = Pp := by
    intro Pp
    refine Polynomial.ext (fun n => ?_)
    rw [Polynomial.coeff_map]
    refine Subtype.ext ?_
    exact weightScale_eq_of_mem_prefix_one htwo (Pp.coeff n)
  have hsceval : Polynomial.aeval x sc = weightScale htwo x := by
    rw [hscdef, map_mul, Polynomial.aeval_C, Polynomial.aeval_X, hxdef, weightScale_jet, pow_one,
      hρ2def, ← IsScalarTower.algebraMap_apply]
  have hscale : ∀ Pp : Polynomial ↥(jetPrefixField C 1),
      weightScale htwo (Polynomial.aeval x Pp) = Polynomial.aeval x (Pp.comp sc) := by
    intro Pp
    rw [Polynomial.aeval_comp, hsceval, weightScale_aeval htwo 1 x Pp, hmapid Pp]
  have hveq : weightScale htwo v = v := hv
  rw [hvdiv, map_div₀, hscale, hscale] at hveq
  have hcoeffsc : ∀ (Pp : Polynomial ↥(jetPrefixField C 1)) (n : ℕ),
      (Pp.comp sc).coeff n = ρ2 ^ n * Pp.coeff n := by
    intro Pp n
    rw [hscdef]
    exact coeff_comp_C_mul_X Pp ρ2 n
  have hQlead : Q.coeff Q.natDegree = 1 := hQm.leadingCoeff
  have hQsc0 : Q.comp sc ≠ 0 := by
    intro hh
    have hcf := congrArg (fun p : Polynomial ↥(jetPrefixField C 1) => p.coeff Q.natDegree) hh
    rw [hcoeffsc, hQlead, mul_one] at hcf
    exact pow_ne_zero Q.natDegree hρ2 hcf
  have hQscy : Polynomial.aeval x (Q.comp sc) ≠ 0 := fun hh => hQsc0 (hinj (by simpa using hh))
  have hcross : P.comp sc * Q = Q.comp sc * P := by
    refine hinj ?_
    rw [map_mul, map_mul]
    field_simp at hveq
    linear_combination hveq
  have hdvd : Q ∣ Q.comp sc :=
    hcop.symm.dvd_of_dvd_mul_left ⟨P.comp sc, by linear_combination -hcross⟩
  have hQscdeg : (Q.comp sc).natDegree = Q.natDegree := by
    rw [Polynomial.natDegree_comp, hscdeg, mul_one]
  obtain ⟨c, hc0, hc⟩ := eq_C_mul_of_dvd_of_natDegree_eq hQsc0 hdvd hQscdeg
  have hcval : c = ρ2 ^ Q.natDegree := by
    have hcf := congrArg (fun p : Polynomial ↥(jetPrefixField C 1) => p.coeff Q.natDegree) hc
    rw [hcoeffsc, hQlead, mul_one, Polynomial.coeff_C_mul, hQlead, mul_one] at hcf
    exact hcf.symm
  have hpowne : ∀ j : ℕ, j ≠ Q.natDegree → ρ2 ^ j ≠ ρ2 ^ Q.natDegree := by
    intro j hj
    rw [hρ2def, ← map_pow, ← map_pow]
    intro hh
    have h2 : (2 : C) ^ j = 2 ^ Q.natDegree :=
      (algebraMap C ↥(jetPrefixField C 1)).injective hh
    have hnat : ((2 ^ j : ℕ) : C) = ((2 ^ Q.natDegree : ℕ) : C) := by push_cast; exact h2
    exact hj (Nat.pow_right_injective (le_refl 2) (Nat.cast_injective (R := C) hnat))
  have hQcoeff : ∀ j : ℕ, j ≠ Q.natDegree → Q.coeff j = 0 := by
    intro j hj
    have hcf := congrArg (fun p : Polynomial ↥(jetPrefixField C 1) => p.coeff j) hc
    rw [hcoeffsc, Polynomial.coeff_C_mul, hcval] at hcf
    by_contra hQj
    exact hpowne j hj (mul_right_cancel₀ hQj (by linear_combination hcf))
  have hQpow : Q = Polynomial.X ^ Q.natDegree := by
    refine Polynomial.ext (fun n => ?_)
    rcases eq_or_ne n Q.natDegree with rfl | hn
    · rw [Polynomial.coeff_X_pow, if_pos rfl, hQlead]
    · rw [hQcoeff n hn, Polynomial.coeff_X_pow, if_neg hn]
  have hPsc : P.comp sc = Polynomial.C c * P := by
    refine mul_right_cancel₀ hQ0 ?_
    rw [hcross, hc]
    ring
  have hPcoeff : ∀ j : ℕ, j ≠ Q.natDegree → P.coeff j = 0 := by
    intro j hj
    have hcf := congrArg (fun p : Polynomial ↥(jetPrefixField C 1) => p.coeff j) hPsc
    rw [hcoeffsc, Polynomial.coeff_C_mul, hcval] at hcf
    by_contra hPj
    exact hpowne j hj (mul_right_cancel₀ hPj (by linear_combination hcf))
  have hPpow : P = Polynomial.C (P.coeff Q.natDegree) * Polynomial.X ^ Q.natDegree := by
    refine Polynomial.ext (fun n => ?_)
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    rcases eq_or_ne n Q.natDegree with rfl | hn
    · rw [if_pos rfl, mul_one]
    · rw [if_neg hn, mul_zero, hPcoeff n hn]
  have hvval : v = algebraMap ↥(jetPrefixField C 1) (JetField C Unit) (P.coeff Q.natDegree) := by
    have hPe : Polynomial.aeval x P
        = algebraMap ↥(jetPrefixField C 1) (JetField C Unit) (P.coeff Q.natDegree)
          * x ^ Q.natDegree := by
      conv_lhs => rw [hPpow]
      rw [map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X]
    have hQe : Polynomial.aeval x Q = x ^ Q.natDegree := by
      conv_lhs => rw [hQpow]
      rw [map_pow, Polynomial.aeval_X]
    rw [hvdiv, hPe, hQe, mul_div_assoc, div_self (pow_ne_zero _ hx0), mul_one]
  rw [hvval]
  exact (mem_jetPrefixField_iff 1 _).mp (P.coeff Q.natDegree).2 1 (by omega)


end

end GaloisForLFunctions.HTGeometry
