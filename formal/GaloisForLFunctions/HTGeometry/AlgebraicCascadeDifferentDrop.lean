import GaloisForLFunctions.HTGeometry.AlgebraicCascadePlace
import GaloisForLFunctions.HTGeometry.TopDegreeSharpDrop
import GaloisForLFunctions.HTGeometry.IntegralGeneratorDerivationClearing
import GaloisForLFunctions.HTGeometry.PlaceDerivationValuationDrop
import GaloisForLFunctions.HTGeometry.DedekindOrderMonogenic
import GaloisForLFunctions.HTGeometry.KummerDedekindDifferentOrder

/-!
# The extended derivation drops every place of the cascade model boundedly

The derivation `∂/∂u` at the uniformiser of the degree at infinity preserves the valuation ring of
the coordinate field.  On the algebraic model its extension need not preserve the integral closure,
but the closure is monogenic over the valuation ring, and the derivative of the generator's minimal
polynomial clears the extended derivation.  Feeding that clearing element into the adic-valuation
drop gives: at every place `Q` of the integral closure there is a positive integer `e` with

`v_Q(δ f) ≤ v_Q(f) · exp e`  for every `f` in the model,

and when `Q` lies over the maximal ideal with Kummer–Dedekind multiplicity `e`, that multiplicity
itself works — the tame bound `ord_Q(𝔡) ≤ e − 1` of the different.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Polynomial IsDedekindDomain IsLocalRing

variable (m : ℕ) (p : Polynomial CascadeField) [Fact (Irreducible p)]

/-! ## Constants of the valuation ring -/

theorem natCast_topOrd_eq_zero {n : ℕ} (hn : n ≠ 0) :
    topOrd m ((n : ℕ) : CascadeField) = (0 : ℤ) := by
  have hcast : ((n : ℕ) : CascadeField)
      = algebraMap (MvPolynomial ℕ ℂ) CascadeField ((n : ℕ) : MvPolynomial ℕ ℂ) := by
    rw [map_natCast]
  have hne : ((n : ℕ) : MvPolynomial ℕ ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  rw [hcast, topOrd_algebraMap m hne]
  have hdeg : MvPolynomial.degreeOf m ((n : ℕ) : MvPolynomial ℕ ℂ) = 0 := by
    have hC : ((n : ℕ) : MvPolynomial ℕ ℂ) = MvPolynomial.C ((n : ℕ) : ℂ) := by
      rw [map_natCast]
    rw [hC, MvPolynomial.degreeOf_C]
  rw [hdeg]
  norm_num

theorem isUnit_natCast_topInt {n : ℕ} (hn : n ≠ 0) : IsUnit ((n : ℕ) : topInt m) := by
  have hne : ((n : ℕ) : CascadeField) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hinv_ne : ((n : ℕ) : CascadeField)⁻¹ ≠ 0 := inv_ne_zero hne
  have hordn : topOrd m ((n : ℕ) : CascadeField) = (0 : ℤ) := natCast_topOrd_eq_zero m hn
  have hordinv : topOrd m ((n : ℕ) : CascadeField)⁻¹ = (0 : ℤ) := by
    have hmul := topOrd_mul m ((n : ℕ) : CascadeField) ((n : ℕ) : CascadeField)⁻¹
    rw [mul_inv_cancel₀ hne, topOrd_one, hordn] at hmul
    have := hmul.symm
    rwa [show ((0 : ℤ) : WithTop ℤ) + topOrd m ((n : ℕ) : CascadeField)⁻¹
        = topOrd m ((n : ℕ) : CascadeField)⁻¹ from zero_add _] at this
  have hmemn : ((n : ℕ) : CascadeField) ∈ topInt m := by
    rw [mem_topInt, hordn]
    exact le_rfl
  have hmeminv : ((n : ℕ) : CascadeField)⁻¹ ∈ topInt m := by
    rw [mem_topInt, hordinv]
    exact le_rfl
  refine isUnit_iff_exists_inv.mpr ⟨⟨_, hmeminv⟩, ?_⟩
  have hval : (((n : ℕ) : topInt m) : CascadeField) = ((n : ℕ) : CascadeField) := by
    push_cast
    rfl
  ext
  push_cast [hval]
  exact mul_inv_cancel₀ hne

instance charZero_residueField_topInt : CharZero (ResidueField (topInt m)) := by
  refine ⟨fun a b hab => ?_⟩
  by_contra hne
  rcases Nat.lt_or_ge a b with hlt | hge
  · have hdiff : ((b - a : ℕ) : ResidueField (topInt m)) = 0 := by
      push_cast [Nat.cast_sub hlt.le]
      rw [← hab]
      ring
    have hd0 : b - a ≠ 0 := by omega
    have hunit := (isUnit_natCast_topInt m hd0).map (residue (topInt m))
    rw [show (residue (topInt m)) (((b - a : ℕ) : topInt m))
        = ((b - a : ℕ) : ResidueField (topInt m)) from map_natCast _ _] at hunit
    rw [hdiff] at hunit
    exact hunit.ne_zero rfl
  · rcases Nat.lt_or_ge b a with hlt' | hge'
    · have hdiff : ((a - b : ℕ) : ResidueField (topInt m)) = 0 := by
        push_cast [Nat.cast_sub hlt'.le]
        rw [hab]
        ring
      have hd0 : a - b ≠ 0 := by omega
      have hunit := (isUnit_natCast_topInt m hd0).map (residue (topInt m))
      rw [show (residue (topInt m)) (((a - b : ℕ) : topInt m))
          = ((a - b : ℕ) : ResidueField (topInt m)) from map_natCast _ _] at hunit
      rw [hdiff] at hunit
      exact hunit.ne_zero rfl
    · exact hne (by omega)

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Polynomial IsDedekindDomain IsLocalRing WithZero
open UniqueFactorizationMonoid

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000

variable (m : ℕ) (p : Polynomial CascadeField) [Fact (Irreducible p)]

/-! ## The closure is a finite torsion-free module -/

theorem algebraMap_algCascadeInt_injective :
    Function.Injective (algebraMap (topInt m) (algCascadeInt m p)) := by
  intro x y hxy
  have h : algebraMap (topInt m) (AlgCascadeField p) x
      = algebraMap (topInt m) (AlgCascadeField p) y := by
    rw [IsScalarTower.algebraMap_apply (topInt m) (algCascadeInt m p) (AlgCascadeField p),
      IsScalarTower.algebraMap_apply (topInt m) (algCascadeInt m p) (AlgCascadeField p), hxy]
  have h2 : algebraMap CascadeField (AlgCascadeField p) (algebraMap (topInt m) CascadeField x)
      = algebraMap CascadeField (AlgCascadeField p) (algebraMap (topInt m) CascadeField y) := by
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
    exact h
  exact Subtype.ext ((algebraMap CascadeField (AlgCascadeField p)).injective h2)

instance module_finite_algCascadeInt : Module.Finite (topInt m) (algCascadeInt m p) :=
  IsIntegralClosure.finite (topInt m) CascadeField (AlgCascadeField p) (algCascadeInt m p)

instance isTorsionFree_algCascadeInt : Module.IsTorsionFree (topInt m) (algCascadeInt m p) :=
  (Module.isTorsionFree_iff_algebraMap_injective).mpr (algebraMap_algCascadeInt_injective m p)

theorem maxExt_algCascadeInt_ne_bot : maxExt (topInt m) (algCascadeInt m p) ≠ ⊥ := by
  obtain ⟨x, hxmem, hxne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (topInt_maximalIdeal_ne_bot m)
  refine Submodule.ne_bot_iff _ |>.mpr
    ⟨algebraMap (topInt m) (algCascadeInt m p) x, Ideal.mem_map_of_mem _ hxmem, ?_⟩
  intro h0
  exact hxne (algebraMap_algCascadeInt_injective m p (by rw [h0, map_zero]))

instance finiteDimensional_residue_quotient :
    FiniteDimensional (ResidueField (topInt m))
      (algCascadeInt m p ⧸ maxExt (topInt m) (algCascadeInt m p)) := by
  have hfin : Module.Finite (topInt m)
      (algCascadeInt m p ⧸ maxExt (topInt m) (algCascadeInt m p)) :=
    Module.Finite.of_surjective
      (Submodule.mkQ (Submodule.restrictScalars (topInt m)
        (maxExt (topInt m) (algCascadeInt m p))))
      (Submodule.mkQ_surjective _)
  exact Module.Finite.of_restrictScalars_finite (topInt m) (ResidueField (topInt m)) _

/-! ## The monogenic clearing package -/

/-- **A generator of the closure whose minimal-polynomial derivative clears the extended
derivation at every place.** -/
theorem exists_monogenic_clearing :
    ∃ α : algCascadeInt m p,
      Algebra.adjoin (topInt m) ({α} : Set (algCascadeInt m p)) = ⊤ ∧
      IsIntegral (topInt m) α ∧
      Polynomial.aeval α (derivative (minpoly (topInt m) α)) ≠ 0 ∧
      ∀ Q : HeightOneSpectrum (algCascadeInt m p), ∀ x : algCascadeInt m p,
        Q.valuation (AlgCascadeField p)
          (algebraMap (algCascadeInt m p) (AlgCascadeField p)
              (Polynomial.aeval α (derivative (minpoly (topInt m) α)))
            * algLaw p (uDeriv m)
              (algebraMap (algCascadeInt m p) (AlgCascadeField p) x)) ≤ 1 := by
  obtain ⟨α, hgen⟩ := exists_adjoin_eq_top_of_dedekind_finite
    (S := topInt m) (B := algCascadeInt m p) (maxExt_algCascadeInt_ne_bot m p)
  have hint : IsIntegral (topInt m) α :=
    IsIntegralClosure.isIntegral (topInt m) (AlgCascadeField p) α
  set ι : algCascadeInt m p →ₐ[topInt m] AlgCascadeField p :=
    IsScalarTower.toAlgHom (topInt m) (algCascadeInt m p) (AlgCascadeField p) with hι
  set q : Polynomial CascadeField
    := (minpoly (topInt m) α).map (algebraMap (topInt m) CascadeField) with hq
  have hqcoeff : ∀ i, q.coeff i ∈ topInt m := by
    intro i
    rw [hq, Polynomial.coeff_map]
    exact SetLike.coe_mem _
  have hcomm : ∀ r : Polynomial (topInt m),
      ι (Polynomial.aeval α r) = Polynomial.aeval (ι α) r := fun r =>
    (Polynomial.aeval_algHom_apply ι α r).symm
  have hqα : Polynomial.aeval (ι α) q = 0 := by
    rw [hq, Polynomial.aeval_map_algebraMap, ← hcomm, minpoly.aeval, map_zero]
  have hcmap : ι (Polynomial.aeval α (derivative (minpoly (topInt m) α)))
      = Polynomial.aeval (ι α) (derivative q) := by
    rw [hq, Polynomial.derivative_map, Polynomial.aeval_map_algebraMap, hcomm]
  have hqmin : q = minpoly CascadeField (ι α) := by
    rw [hq]
    exact (minpoly.isIntegrallyClosed_eq_field_fractions CascadeField
      (AlgCascadeField p) hint).symm
  have hcharK : CharZero CascadeField :=
    charZero_of_injective_algebraMap
      (IsFractionRing.injective (MvPolynomial ℕ ℂ) CascadeField)
  have hιint : IsIntegral CascadeField (ι α) := Algebra.IsIntegral.isIntegral _
  have hsep : (minpoly CascadeField (ι α)).Separable :=
    (minpoly.irreducible hιint).separable
  have hcne : Polynomial.aeval α (derivative (minpoly (topInt m) α)) ≠ 0 := by
    intro h0
    have h1 : Polynomial.aeval (ι α) (derivative q) = 0 := by
      rw [← hcmap, h0, map_zero]
    rw [hqmin] at h1
    exact hsep.aeval_derivative_ne_zero (minpoly.aeval _ _) h1
  refine ⟨α, hgen, hint, hcne, ?_⟩
  intro Q x
  have htransport : ∀ y : algCascadeInt m p,
      y ∈ Algebra.adjoin (topInt m) ({α} : Set (algCascadeInt m p)) →
      ι y ∈ Algebra.adjoin (topInt m) ({ι α} : Set (AlgCascadeField p)) := by
    intro y hy
    induction hy using Algebra.adjoin_induction with
    | mem z hz =>
        rw [Set.mem_singleton_iff] at hz
        subst hz
        exact Algebra.self_mem_adjoin_singleton _ _
    | algebraMap c =>
        rw [AlgHom.commutes]
        exact Subalgebra.algebraMap_mem _ _
    | add s t hs ht ihs iht =>
        rw [map_add]
        exact Subalgebra.add_mem _ ihs iht
    | mul s t hs ht ihs iht =>
        rw [map_mul]
        exact Subalgebra.mul_mem _ ihs iht
  have hmemx : ι x ∈ Algebra.adjoin (topInt m) ({ι α} : Set (AlgCascadeField p)) :=
    htransport x (hgen ▸ Algebra.mem_top)
  have hDS : ∀ a ∈ topInt m, uDeriv m a ∈ topInt m := fun a ha => uDeriv_mem_topInt ha
  have hD' : ∀ a : CascadeField,
      algLaw p (uDeriv m) (algebraMap CascadeField (AlgCascadeField p) a)
        = algebraMap CascadeField (AlgCascadeField p) (uDeriv m a) := fun a =>
    algLaw_algebraMap p (uDeriv m) a
  have hclear := aeval_derivative_mul_deriv_mem_adjoin (uDeriv m)
    (algLaw p (uDeriv m)) (topInt m) hDS hD' hqcoeff hqα hmemx
  have hle : Algebra.adjoin (topInt m) ({ι α} : Set (AlgCascadeField p))
      ≤ integralClosure (topInt m) (AlgCascadeField p) := by
    refine Algebra.adjoin_le ?_
    rintro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    exact α.2
  set b : algCascadeInt m p := ⟨_, hle hclear⟩ with hbdef
  have heq : algebraMap (algCascadeInt m p) (AlgCascadeField p)
      (Polynomial.aeval α (derivative (minpoly (topInt m) α)))
      * algLaw p (uDeriv m) (algebraMap (algCascadeInt m p) (AlgCascadeField p) x)
      = algebraMap (algCascadeInt m p) (AlgCascadeField p) b := by
    have hcast : algebraMap (algCascadeInt m p) (AlgCascadeField p)
        (Polynomial.aeval α (derivative (minpoly (topInt m) α)))
        = Polynomial.aeval (ι α) (derivative q) := hcmap
    rw [hcast]
    rfl
  rw [heq]
  exact Q.valuation_le_one b

/-! ## The drop at every place -/

set_option maxHeartbeats 8000000 in
/-- **The extended derivation drops every place boundedly.** -/
theorem exists_pos_valuation_algLaw_uDeriv_le
    (Q : HeightOneSpectrum (algCascadeInt m p)) :
    ∃ e : ℕ, 0 < e ∧ ∀ f : AlgCascadeField p,
      Q.valuation (AlgCascadeField p) (algLaw p (uDeriv m) f)
        ≤ Q.valuation (AlgCascadeField p) f * exp (e : ℤ) := by
  obtain ⟨α, hgen, hint, hcne, hclear⟩ := exists_monogenic_clearing m p
  set c : algCascadeInt m p := Polynomial.aeval α (derivative (minpoly (topInt m) α)) with hc
  set n : ℕ := multiplicity Q.asIdeal (Ideal.span {c}) with hn
  refine ⟨n + 1, Nat.succ_pos n, fun f => ?_⟩
  refine valuation_deriv_le_of_not_mem_pow Q (algLaw p (uDeriv m)) (hclear Q) ?_ f
  intro hmem
  have hle := (intValuation_le_pow_iff_mem Q c (n + 1)).mpr hmem
  rw [Q.intValuation_eq_exp_neg_multiplicity hcne, ← hn] at hle
  have := exp_le_exp.mp hle
  omega

set_option maxHeartbeats 8000000 in
/-- **At a place over the maximal ideal, the Kummer–Dedekind multiplicity itself bounds the
drop** — the tame different estimate `ord_Q(𝔡) ≤ e − 1`. -/
theorem valuation_algLaw_uDeriv_le_of_normalizedFactor
    (Q : HeightOneSpectrum (algCascadeInt m p))
    (hQ : Q.asIdeal ∈ normalizedFactors
      ((maximalIdeal (topInt m)).map (algebraMap (topInt m) (algCascadeInt m p))))
    {e : ℕ} (he : emultiplicity Q.asIdeal
      ((maximalIdeal (topInt m)).map (algebraMap (topInt m) (algCascadeInt m p)))
      = (e : ℕ∞)) (f : AlgCascadeField p) :
    Q.valuation (AlgCascadeField p) (algLaw p (uDeriv m) f)
      ≤ Q.valuation (AlgCascadeField p) f * exp (e : ℤ) := by
  obtain ⟨α, hgen, hint, hcne, hclear⟩ := exists_monogenic_clearing m p
  refine valuation_deriv_le_of_not_mem_pow Q (algLaw p (uDeriv m)) (hclear Q) ?_ f
  exact not_mem_pow_aeval_derivative (maximalIdeal.isMaximal _)
    (topInt_maximalIdeal_ne_bot m) hgen hint hQ he

end GaloisForLFunctions.HTGeometry
