import GaloisForLFunctions.HTGeometry.BesselOrderParameterizedComparisonJet
import GaloisForLFunctions.HTGeometry.RatFuncShiftPowerFixedField
import GaloisForLFunctions.HTGeometry.SigmaDeltaComponentQuotient
import GaloisForLFunctions.HTGeometry.SigmaDeltaNoNewConstantsFieldExtension

/-!
# No new constants in the reduced Bessel PPV quotient

Finite differential-prime decomposition reduces the non-domain parameterized PV ring to one
domain component.  The least positive shift stabilizing that component is simple there, so the
domain Hardouin--Singer theorem applies.  Transitivity of the component action then descends the
same constant to every component, whose intersection is zero.
-/

namespace GaloisForLFunctions.HTGeometry.BesselDifferentialClosure

open GaloisForLFunctions GaloisForLFunctions.HTGeometry
open scoped Differential

noncomputable section

local instance besselOrderReducedNoNewBaseDifferential :
    Differential (RatFunc Constants) := coordinateTotalDifferential

local instance besselOrderReducedNoNewConstantsRatDifferentialAlgebra :
    DifferentialAlgebra Constants (RatFunc Constants) :=
  coordinateTotalDifferentialAlgebra

local instance besselOrderReducedNoNewPPVDifferential {s : ℝ}
    (data : BesselOrderParameterizedPVData s) : Differential data.PPVRing :=
  quotientDifferential data.M data.isSigmaDeltaIdeal.2

local instance besselOrderReducedNoNewPPVDifferentialAlgebra {s : ℝ}
    (data : BesselOrderParameterizedPVData s) :
    DifferentialAlgebra (RatFunc Constants) data.PPVRing :=
  ppvQuotientDifferentialAlgebra data.M data.isSigmaDeltaIdeal.2

local instance besselOrderReducedNoNewConstantsPPVDifferentialAlgebra {s : ℝ}
    (data : BesselOrderParameterizedPVData s) :
    DifferentialAlgebra Constants data.PPVRing :=
  differentialAlgebra_trans (C := Constants) (K := RatFunc Constants) (E := data.PPVRing)

local instance besselOrderReducedNoNewPPVReduced {s : ℝ}
    (data : BesselOrderParameterizedPVData s) : IsReduced data.PPVRing := data.isReduced

local instance besselOrderReducedNoNewRatCharZero : CharZero (RatFunc Constants) :=
  charZero_of_injective_ringHom (algebraMap ℚ (RatFunc Constants)).injective

private theorem ringEquiv_pow_fixed_of_fixed {R : Type*} [CommRing R]
    (σ : R ≃+* R) {x : R} (hx : σ x = x) (n : ℕ) : (σ ^ n) x = x := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [pow_succ']
      change σ ((σ ^ n) x) = x
      rw [ih, hx]

private theorem BesselOrderParameterizedPVData.baseCompatible_pow
    {s : ℝ} (data : BesselOrderParameterizedPVData s) (n : ℕ)
    (a : RatFunc Constants) :
    (data.sigmaEquiv ^ n) (algebraMap (RatFunc Constants) data.PPVRing a) =
      algebraMap (RatFunc Constants) data.PPVRing ((FieldShift.ratShiftEquiv ^ n) a) := by
  have hsemiconj : Function.Semiconj
      (algebraMap (RatFunc Constants) data.PPVRing)
      FieldShift.ratShiftEquiv data.sigmaEquiv := by
    intro a
    exact (data.baseCompatible a).symm
  rw [ringEquiv_pow_apply, ringEquiv_pow_apply]
  exact (hsemiconj.iterate_right n a).symm

/-- Differential finite generation descends to every differential-prime component quotient. -/
private theorem BesselOrderParameterizedPVData.component_diffGenerators_surjective
    {s : ℝ} (data : BesselOrderParameterizedPVData s)
    (P : Ideal data.PPVRing)
    (hPderiv : ∀ x ∈ P, Differential.deriv x ∈ P) :
    letI : Differential (data.PPVRing ⧸ P) := quotientDifferential P hPderiv
    Function.Surjective
      (differentialPolynomialEvalOver (K := RatFunc Constants)
        (fun i => Ideal.Quotient.mk P (data.diffGenerators i))) := by
  letI : Differential (data.PPVRing ⧸ P) := quotientDifferential P hPderiv
  intro z
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨Q, hQ⟩ := data.diffGenerators_surjective x
  refine ⟨Q, ?_⟩
  have hmap := map_differentialPolynomialEvalOver
    (F := RatFunc Constants) (L := data.PPVRing) (M := data.PPVRing ⧸ P)
    (Ideal.Quotient.mk P)
    (fun x => (quotientDifferential_deriv_mk P hPderiv x).symm)
    (fun a => show Ideal.Quotient.mk P
        (algebraMap (RatFunc Constants) data.PPVRing a) =
      algebraMap (RatFunc Constants) (data.PPVRing ⧸ P) a from rfl)
    data.diffGenerators Q
  rw [hQ] at hmap
  exact hmap.symm

/-- **Reduced Hardouin--Singer no-new-constants theorem for the concrete Bessel PPV datum.** -/
theorem BesselOrderParameterizedPVData.noNewConstants
    {s : ℝ} (data : BesselOrderParameterizedPVData s)
    {x : data.PPVRing} (hx : data.sigmaEquiv x = x) :
    ∃ c : Constants, x = algebraMap Constants data.PPVRing c := by
  classical
  letI : Nontrivial data.PPVRing := by
    rw [← not_subsingleton_iff_nontrivial, Ideal.Quotient.subsingleton_iff]
    exact data.ne_top
  obtain ⟨S, hSne, hSmin, hSbot⟩ :=
    exists_finite_minimalPrimeDifferential_inf_eq_bot_of_diffFG
      data.diffGenerators data.diffGenerators_surjective
  obtain ⟨P, period, hperiodPos, hPS, hPσ, hPσsymm, hPsimple⟩ :=
    exists_componentQuotient_isSigmaDeltaSimple data.sigmaEquiv data.commutesDeriv
      data.isSigmaDeltaSimple S hSne hSmin hSbot
  letI : P.IsPrime := (hSmin P hPS).1
  letI : Differential (data.PPVRing ⧸ P) :=
    quotientDifferential P (hSmin P hPS).2.1
  letI : IsDomain (data.PPVRing ⧸ P) := Ideal.Quotient.isDomain P
  letI : DifferentialAlgebra (RatFunc Constants) (data.PPVRing ⧸ P) := by
    constructor
    intro a
    change Differential.deriv
        (Ideal.Quotient.mk P (algebraMap (RatFunc Constants) data.PPVRing a)) =
      Ideal.Quotient.mk P
        (algebraMap (RatFunc Constants) data.PPVRing (Differential.deriv a))
    rw [quotientDifferential_deriv_mk]
    exact congrArg (Ideal.Quotient.mk P)
      (DifferentialAlgebra.deriv_algebraMap a)
  letI : DifferentialAlgebra Constants (data.PPVRing ⧸ P) :=
    differentialAlgebra_trans
      (C := Constants) (K := RatFunc Constants) (E := data.PPVRing ⧸ P)
  let τQ : (data.PPVRing ⧸ P) ≃+* (data.PPVRing ⧸ P) :=
    sigmaQuotientEquiv (data.sigmaEquiv ^ period) P hPσ hPσsymm
  have hτcomm : CommutesDeriv τQ :=
    quotientDifferential_commutesDeriv
      (commutesDeriv_pow data.sigmaEquiv data.commutesDeriv period) P
      ⟨hPσ, (hSmin P hPS).2.1⟩ hPσsymm
  have hcompat : ∀ a : RatFunc Constants,
      τQ (algebraMap (RatFunc Constants) (data.PPVRing ⧸ P) a) =
        algebraMap (RatFunc Constants) (data.PPVRing ⧸ P)
          ((FieldShift.ratShiftEquiv ^ period) a) := by
    intro a
    rw [show algebraMap (RatFunc Constants) (data.PPVRing ⧸ P) a =
        Ideal.Quotient.mk P (algebraMap (RatFunc Constants) data.PPVRing a) from rfl,
      sigmaQuotientEquiv_mk, data.baseCompatible_pow]
    rfl
  have hbaseConst : ∀ c : Constants,
      (FieldShift.ratShiftEquiv ^ period)
          (algebraMap Constants (RatFunc Constants) c) =
        algebraMap Constants (RatFunc Constants) c := by
    intro c
    apply ringEquiv_pow_fixed_of_fixed
    rw [FieldShift.ratShiftEquiv_apply, FieldShift.ratShift_const]
  have hbaseFix : ∀ a : RatFunc Constants,
      (FieldShift.ratShiftEquiv ^ period) a = a →
        ∃ c : Constants, algebraMap Constants (RatFunc Constants) c = a := by
    intro a ha
    obtain ⟨c, hc⟩ :=
      FieldShift.ratShiftEquiv_pow_fixed_eq_const hperiodPos ha
    exact ⟨c, hc.symm⟩
  have hyP := data.component_diffGenerators_surjective P (hSmin P hPS).2.1
  have hxpow : (data.sigmaEquiv ^ period) x = x :=
    ringEquiv_pow_fixed_of_fixed data.sigmaEquiv hx period
  have hxP : τQ (Ideal.Quotient.mk P x) = Ideal.Quotient.mk P x := by
    rw [sigmaQuotientEquiv_mk, hxpow]
  obtain ⟨c, hcP⟩ :=
    exists_eq_algebraMap_of_isSigmaDeltaSimple_of_diffFG_fieldExtension
      (C := Constants) (K := RatFunc Constants) (R := data.PPVRing ⧸ P)
      (FieldShift.ratShiftEquiv ^ period) τQ hτcomm hcompat
      hbaseConst hbaseFix hPsimple
      (fun i => Ideal.Quotient.mk P (data.diffGenerators i)) hyP hxP
  have hxcP : x - algebraMap Constants data.PPVRing c ∈ P := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_sub, hcP]
    change algebraMap Constants (data.PPVRing ⧸ P) c -
      algebraMap Constants (data.PPVRing ⧸ P) c = 0
    exact sub_self _
  have hxcFixed : data.sigmaEquiv
      (x - algebraMap Constants data.PPVRing c) =
      x - algebraMap Constants data.PPVRing c := by
    have hconst : data.sigmaEquiv (algebraMap Constants data.PPVRing c) =
        algebraMap Constants data.PPVRing c := by
      have hbc := data.baseCompatible_pow 1
        (algebraMap Constants (RatFunc Constants) c)
      rw [pow_one, pow_one, FieldShift.ratShiftEquiv_apply,
        FieldShift.ratShift_const] at hbc
      simpa [IsScalarTower.algebraMap_apply
        Constants (RatFunc Constants) data.PPVRing] using hbc
    rw [map_sub, hx, hconst]
  have hxcAll : x - algebraMap Constants data.PPVRing c ∈
      sInf (S : Set (Ideal data.PPVRing)) := by
    have hspan : Ideal.span {x - algebraMap Constants data.PPVRing c} ≤
        sInf (S : Set (Ideal data.PPVRing)) := by
      apply le_sInf
      intro Q hQS
      obtain ⟨n, hn⟩ := exists_iterate_map_eq_of_isSigmaDeltaSimple
        data.sigmaEquiv data.commutesDeriv data.isSigmaDeltaSimple
        S hSmin hSbot hPS hQS
      rw [Ideal.span_le]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst y
      have hmapped := Ideal.mem_map_of_mem
        (((data.sigmaEquiv ^ n) : data.PPVRing ≃+* data.PPVRing) :
          data.PPVRing →+* data.PPVRing) hxcP
      rw [ideal_map_pow_eq_iterate, hn] at hmapped
      have hfixedPow := ringEquiv_pow_fixed_of_fixed data.sigmaEquiv hxcFixed n
      change (data.sigmaEquiv ^ n)
        (x - algebraMap Constants data.PPVRing c) ∈ Q at hmapped
      rw [hfixedPow] at hmapped
      exact hmapped
    exact hspan (Ideal.mem_span_singleton_self _)
  have hxcZero : x - algebraMap Constants data.PPVRing c = 0 := by
    exact Ideal.mem_bot.mp (hSbot ▸ hxcAll)
  exact ⟨c, sub_eq_zero.mp hxcZero⟩

end

end GaloisForLFunctions.HTGeometry.BesselDifferentialClosure
