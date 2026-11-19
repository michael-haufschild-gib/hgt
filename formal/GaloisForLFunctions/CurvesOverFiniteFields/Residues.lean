import GaloisForLFunctions.CurvesOverFiniteFields.Basic
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.FieldTheory.RatFunc.Degree

/-!
# Residue rings of the two charts are finite over the constants

* The constants lie in the valuation ring at infinity (`algebraMap_mem_infRing`), and every element
  of that ring is congruent to a constant modulo its maximal ideal (`exists_const_sub_mem_maximalIdeal`):
  for `f = p/q` with `q` monic and `deg p ≤ deg q`, subtract the leading coefficient of `p` when
  the degrees agree.
* Residue rings of finite places are finite over `F`: they are finite over `F[x]/(g)` for the
  monic generator `g` of the contracted prime (`finiteDimensional_finChart_quotient`).
* Residue rings of infinite places are finite over `F`, through the residue field at infinity
  (`finiteDimensional_infChart_quotient`).
* There are finitely many infinite places (`finite_infPlace`): each lies over the maximal ideal of
  the valuation ring at infinity.
-/

noncomputable section

open Polynomial IsDedekindDomain

namespace GaloisForLFunctions.CurvesOverFiniteFields

variable (F : Type*) [Field F] [DecidableEq (RatFunc F)]

theorem inftyValuation_algebraMap (a : F) :
    RatFunc.inftyValuation F (algebraMap F (RatFunc F) a) ≤ 1 := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  · rw [show algebraMap F (RatFunc F) a = RatFunc.C a from rfl, RatFunc.inftyValuation.C F ha]

theorem algebraMap_mem_infRing (a : F) : algebraMap F (RatFunc F) a ∈ infRing F :=
  inftyValuation_algebraMap F a

/-- The constants as a subring of the valuation ring at infinity. -/
instance : Algebra F (infRing F) :=
  RingHom.toAlgebra
    { toFun := fun a => ⟨algebraMap F (RatFunc F) a, algebraMap_mem_infRing F a⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp
      map_zero' := by ext; simp
      map_add' := fun a b => by ext; simp }

instance : IsScalarTower F (infRing F) (RatFunc F) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

omit [DecidableEq (RatFunc F)] in
/-- `intDegree (p/q) = deg p − deg q` for nonzero polynomials. -/
theorem intDegree_div_polynomial {p q : F[X]} (hp : p ≠ 0) (hq : q ≠ 0) :
    (algebraMap F[X] (RatFunc F) p / algebraMap F[X] (RatFunc F) q).intDegree =
      (p.natDegree : ℤ) - q.natDegree := by
  have hp' : algebraMap F[X] (RatFunc F) p ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective F[X] (RatFunc F))).mpr hp
  have hq' : (algebraMap F[X] (RatFunc F) q)⁻¹ ≠ 0 :=
    inv_ne_zero ((map_ne_zero_iff _ (IsFractionRing.injective F[X] (RatFunc F))).mpr hq)
  rw [div_eq_mul_inv, RatFunc.intDegree_mul hp' hq', RatFunc.intDegree_inv,
    RatFunc.intDegree_polynomial, RatFunc.intDegree_polynomial]
  ring

/-- Elements of the valuation ring at infinity are congruent to constants. -/
theorem exists_const_sub_lt_one {f : RatFunc F} (hf : RatFunc.inftyValuation F f ≤ 1) :
    ∃ c : F, RatFunc.inftyValuation F (f - algebraMap F (RatFunc F) c) < 1 := by
  rcases eq_or_ne f 0 with rfl | hf0
  · exact ⟨0, by simp⟩
  have hdeg : f.intDegree ≤ 0 := by
    rw [RatFunc.inftyValuation_apply, RatFunc.inftyValuation_of_nonzero F hf0,
      ← WithZero.exp_zero, WithZero.exp_le_exp] at hf
    exact hf
  set p := f.num
  set q := f.denom
  have hq0 : q ≠ 0 := f.denom_ne_zero
  have hp0 : p ≠ 0 := RatFunc.num_ne_zero hf0
  have hfpq : f = algebraMap F[X] (RatFunc F) p / algebraMap F[X] (RatFunc F) q :=
    (RatFunc.num_div_denom f).symm
  have hdeg' : p.natDegree ≤ q.natDegree := by
    have := hdeg
    rw [hfpq, intDegree_div_polynomial F hp0 hq0] at this
    omega
  set c : F := if p.natDegree = q.natDegree then p.leadingCoeff else 0
  refine ⟨c, ?_⟩
  have hsub : f - algebraMap F (RatFunc F) c =
      algebraMap F[X] (RatFunc F) (p - C c * q) / algebraMap F[X] (RatFunc F) q := by
    have hq'' : algebraMap F[X] (RatFunc F) q ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective F[X] (RatFunc F))).mpr hq0
    rw [hfpq, map_sub, map_mul, sub_div, mul_div_cancel_right₀ _ hq'']
    rfl
  have hq' : algebraMap F[X] (RatFunc F) q ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective F[X] (RatFunc F))).mpr hq0
  by_cases h0 : p - C c * q = 0
  · rw [hsub, h0, map_zero, zero_div, map_zero]
    exact zero_lt_one
  have hlt : (p - C c * q).natDegree < q.natDegree := by
    by_cases hpq : p.natDegree = q.natDegree
    · have hc : c = p.leadingCoeff := if_pos hpq
      have hqmon : q.Monic := f.monic_denom
      have hcne : c ≠ 0 := by rw [hc]; exact leadingCoeff_ne_zero.mpr hp0
      have hCq0 : C c * q ≠ 0 := mul_ne_zero (C_ne_zero.mpr hcne) hq0
      have hdeg2 : (C c * q).natDegree = p.natDegree := by
        rw [hpq, natDegree_C_mul hcne]
      have hlead : (C c * q).leadingCoeff = p.leadingCoeff := by
        rw [leadingCoeff_C_mul_of_isUnit hcne.isUnit, hqmon.leadingCoeff, mul_one, hc]
      have hdegeq : p.degree = (C c * q).degree := by
        rw [degree_eq_natDegree hp0, degree_eq_natDegree hCq0, hdeg2]
      have := degree_sub_lt hdegeq hp0 hlead.symm
      have := natDegree_lt_natDegree h0 this
      omega
    · have hc : c = 0 := if_neg hpq
      have : p - C c * q = p := by rw [hc, C_0, zero_mul, sub_zero]
      rw [this]
      omega
  have hne' : f - algebraMap F (RatFunc F) c ≠ 0 := by
    rw [hsub]
    exact div_ne_zero ((map_ne_zero_iff _ (IsFractionRing.injective F[X] (RatFunc F))).mpr h0) hq'
  rw [RatFunc.inftyValuation_apply, RatFunc.inftyValuation_of_nonzero F hne', ← WithZero.exp_zero,
    WithZero.exp_lt_exp, hsub, intDegree_div_polynomial F h0 hq0]
  omega

/-- The residue field at infinity is spanned by the constants. -/
theorem algebraMap_infRing_quotient_surjective :
    Function.Surjective (algebraMap F (infRing F ⧸ IsLocalRing.maximalIdeal (infRing F))) := by
  intro y
  obtain ⟨⟨f, hf⟩, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨c, hc⟩ := exists_const_sub_lt_one F hf
  refine ⟨c, ?_⟩
  rw [IsScalarTower.algebraMap_apply F (infRing F), Ideal.Quotient.algebraMap_eq,
    Ideal.Quotient.eq]
  rw [← neg_mem_iff, neg_sub, Valuation.mem_maximalIdeal_iff]
  exact hc

instance finiteDimensional_infRing_quotient :
    FiniteDimensional F (infRing F ⧸ IsLocalRing.maximalIdeal (infRing F)) :=
  Module.Finite.of_surjective (Algebra.linearMap F _)
    (algebraMap_infRing_quotient_surjective F)


variable (K : Type*) [Field K] [Algebra F[X] K] [Algebra (RatFunc F) K]
  [IsScalarTower F[X] (RatFunc F) K] [FunctionField F K] [Algebra.IsSeparable (RatFunc F) K]
  [Algebra F K] [IsScalarTower F F[X] K] [IsScalarTower F (RatFunc F) K]

instance : IsScalarTower F (infRing F) K :=
  IsScalarTower.of_algebraMap_eq fun a => by
    rw [IsScalarTower.algebraMap_apply F (RatFunc F) K]
    rfl

instance : Module.Finite (infRing F) (infChart F K) :=
  IsIntegralClosure.finite (infRing F) (RatFunc F) K (infChart F K)

omit [DecidableEq (RatFunc F)] [Algebra F K] [IsScalarTower F F[X] K]
  [IsScalarTower F (RatFunc F) K] in
/-- The contraction of a finite place to `F[x]` is nonzero. -/
theorem comap_finPlace_ne_bot (P : FinPlace F K) :
    P.asIdeal.comap (algebraMap F[X] (finChart F K)) ≠ ⊥ := by
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot P.ne_bot
  exact Ideal.comap_ne_bot_of_integral_mem hx0 hx (Algebra.IsIntegral.isIntegral x)

/-- Residue rings of finite places are finite-dimensional over the constants. -/
instance finiteDimensional_finChart_quotient (P : FinPlace F K) :
    FiniteDimensional F (finChart F K ⧸ P.asIdeal) := by
  set p := P.asIdeal.comap (algebraMap F[X] (finChart F K))
  have hp := comap_finPlace_ne_bot F K P
  set g := Submodule.IsPrincipal.generator p
  have hg : Ideal.span {g} = p := Ideal.span_singleton_generator p
  have hg0 : g ≠ 0 := by
    intro h
    have : p = ⊥ := by rw [← hg, h, Ideal.span_singleton_eq_bot.mpr rfl]
    exact hp this
  haveI h1 : Module.Finite F (AdjoinRoot g) := (AdjoinRoot.powerBasis hg0).finite
  haveI : Module.Finite F (F[X] ⧸ Ideal.span {g}) := h1
  haveI : Module.Finite F (F[X] ⧸ p) :=
    Module.Finite.equiv (Ideal.quotientEquivAlgOfEq F hg).toLinearEquiv
  exact Module.Finite.trans (F[X] ⧸ p) _

omit [Algebra F[X] K] [IsScalarTower F[X] (RatFunc F) K] [FunctionField F K]
  [Algebra.IsSeparable (RatFunc F) K] [Algebra F K] [IsScalarTower F F[X] K]
  [IsScalarTower F (RatFunc F) K] in
/-- The contraction of an infinite place is the maximal ideal at infinity. -/
theorem comap_infPlace_eq (Q : InfPlace F K) :
    Q.asIdeal.comap (algebraMap (infRing F) (infChart F K)) =
      IsLocalRing.maximalIdeal (infRing F) := by
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot Q.ne_bot
  have hne : Q.asIdeal.comap (algebraMap (infRing F) (infChart F K)) ≠ ⊥ :=
    Ideal.comap_ne_bot_of_integral_mem hx0 hx (Algebra.IsIntegral.isIntegral x)
  haveI : (Q.asIdeal.comap (algebraMap (infRing F) (infChart F K))).IsPrime :=
    Ideal.IsPrime.comap _
  exact IsLocalRing.eq_maximalIdeal (Ideal.IsPrime.isMaximal inferInstance hne)

/-- Residue rings of infinite places are finite-dimensional over the constants. -/
instance finiteDimensional_infChart_quotient (Q : InfPlace F K) :
    FiniteDimensional F (infChart F K ⧸ Q.asIdeal) := by
  set p := Q.asIdeal.comap (algebraMap (infRing F) (infChart F K))
  haveI : Module.Finite F (infRing F ⧸ p) :=
    Module.Finite.equiv
      (Ideal.quotientEquivAlgOfEq F (comap_infPlace_eq F K Q).symm).toLinearEquiv
  exact Module.Finite.trans (infRing F ⧸ p) _

/-- There are finitely many infinite places. -/
instance finite_infPlace : Finite (InfPlace F K) := by
  have hfin := IsDedekindDomain.primesOver_finite (IsLocalRing.maximalIdeal (infRing F))
    (infChart F K)
  refine Finite.of_injective (β := hfin.toFinset) (fun Q => ⟨Q.asIdeal, ?_⟩) ?_
  · rw [Set.Finite.mem_toFinset]
    exact ⟨Q.isPrime, ⟨(comap_infPlace_eq F K Q).symm⟩⟩
  · intro Q Q' h
    exact HeightOneSpectrum.ext (congrArg Subtype.val h)

end GaloisForLFunctions.CurvesOverFiniteFields
