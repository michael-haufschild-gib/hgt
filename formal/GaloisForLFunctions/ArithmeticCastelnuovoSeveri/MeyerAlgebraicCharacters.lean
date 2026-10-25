import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.MeyerFiniteProjectorAlgebra
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.PositiveMeyerDegreesCanForgetClasses
import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerOriginalConvolutionInverse

/-!
# Algebraic Meyer characters are actual Xi evaluations

An original-source Fredholm inverse forces every nonzero multiplicative degree
to detect a finite causal packet. Truncated local multiplication then selects
one value idempotent, which determines the degree on the whole source quotient.
No continuity or infinite expansion of the degree is assumed.
-/

noncomputable section
open Complex RHTower
open scoped ComplexConjugate
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

theorem meyerPointDegree_hasse (rho sigma : XiDivisorSupport)
    (j : DeningerArithmeticJetIndex sigma) :
    meyerPointDegree rho (meyerHasseJetClass sigma j) =
      if rho = sigma ∧ j.val = 0 then 1 else 0 := by
  change deningerMeyerXiSupportJetEvaluationLM rho ⟨0, xiSupportMultiplicity_pos rho⟩
    (meyerHasseJetClass sigma j) = _
  rw [meyerHasseJetClass_raw_jet]
  by_cases hj : j.val = 0
  · simp only [hj, Nat.factorial_zero, Nat.cast_one, and_true]
  · simp only [hj, Ne.symm hj, and_false, if_false]

theorem meyerPointDegree_ne_zero (rho : XiDivisorSupport) : meyerPointDegree rho ≠ 0 := by
  intro h
  have he := congrArg (fun d : DeningerMeyerStrongLogCohomology →ₗ[ℂ] ℂ =>
    d (meyerHasseJetClass rho ⟨0, xiSupportMultiplicity_pos rho⟩)) h
  rw [meyerPointDegree_hasse, if_pos ⟨rfl, rfl⟩] at he
  exact one_ne_zero he

theorem meyerPointDegree_injective : Function.Injective meyerPointDegree := by
  intro rho sigma h
  by_contra hne
  have he := congrArg (fun d : DeningerMeyerStrongLogCohomology →ₗ[ℂ] ℂ =>
    d (meyerHasseJetClass rho ⟨0, xiSupportMultiplicity_pos rho⟩)) h
  rw [meyerPointDegree_hasse, meyerPointDegree_hasse,
    if_pos ⟨rfl, rfl⟩, if_neg (fun h => hne h.1.symm)] at he
  exact one_ne_zero he

/-- Multiplicativity alone kills every positive-order local jet. -/
theorem meyerMultiplicativeDegree_higher_jet_zero
    (χ : DeningerMeyerStrongLogCohomology →ₗ[ℂ] ℂ)
    (hm : ∀ u v, χ (deningerMeyerCohomologyConvolution u v) = χ u * χ v)
    (rho : XiDivisorSupport) (j : DeningerArithmeticJetIndex rho) (hj : 0 < j.val) :
    χ (meyerHasseJetClass rho j) = 0 := by
  have hrec : ∀ n : ℕ, ∀ k : DeningerArithmeticJetIndex rho,
      xiSupportMultiplicity rho - k.val = n → 0 < k.val →
        χ (meyerHasseJetClass rho k) = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro k hkn hk
      have hs : χ (meyerHasseJetClass rho k) * χ (meyerHasseJetClass rho k) = 0 := by
        rw [← hm]
        by_cases hlt : k.val + k.val < xiSupportMultiplicity rho
        · rw [meyerHasseJetClass_product_same rho k k hlt]
          exact ih (xiSupportMultiplicity rho - (k.val + k.val))
            (by have hki := k.isLt; omega) ⟨k.val + k.val, hlt⟩ rfl (by
              change 0 < k.val + k.val
              omega)
        · rw [meyerHasseJetClass_product_truncated rho k k (Nat.le_of_not_gt hlt), map_zero]
      exact (mul_eq_zero.mp hs).elim id id
  exact hrec (xiSupportMultiplicity rho - j.val) j rfl hj

/-- Source-class inversion excludes a nonzero character supported only at infinity. -/
theorem meyerMultiplicativeDegree_detects_finite_jet
    (χ : DeningerMeyerStrongLogCohomology →ₗ[ℂ] ℂ) (hne : χ ≠ 0)
    (hm : ∀ u v, χ (deningerMeyerCohomologyConvolution u v) = χ u * χ v) :
    ∃ (rho : XiDivisorSupport) (j : DeningerArithmeticJetIndex rho),
      χ (meyerHasseJetClass rho j) ≠ 0 := by
  classical
  have hex : ∃ u, χ u ≠ 0 := by
    by_contra! h
    exact hne (LinearMap.ext h)
  obtain ⟨u, hu⟩ := hex
  induction u using Submodule.Quotient.induction_on with
  | H a =>
    let g : DeningerMeyerStrongLogTarget :=
      (-(χ (Submodule.Quotient.mk a))⁻¹) • a
    have hg : χ (Submodule.Quotient.mk g) = -1 := by
      change χ ((LinearMap.range deningerMeyerStrongLogSumLM).mkQ
        ((-(χ (Submodule.Quotient.mk a))⁻¹) • a)) = -1
      rw [map_smul, map_smul, smul_eq_mul, neg_mul]
      change -((χ (Submodule.Quotient.mk a))⁻¹ * χ (Submodule.Quotient.mk a)) = -1
      rw [inv_mul_cancel₀ hu]
    let S := deningerMeyerConvolutionResonantPacket g
    let v := deningerMeyerOriginalConvolutionInverse g (Submodule.Quotient.mk a)
    have hR := congrArg χ
      (deningerMeyerOriginalConvolutionInverse_right g (Submodule.Quotient.mk a))
    change χ (v + deningerMeyerCohomologyConvolution (Submodule.Quotient.mk g)
      (v - deningerMeyerFiniteXiCausalProjector S v)) = χ (Submodule.Quotient.mk a) at hR
    rw [map_add, hm, map_sub, hg] at hR
    have hp : χ (deningerMeyerFiniteXiCausalProjector S v) ≠ 0 := by
      have he : χ (deningerMeyerFiniteXiCausalProjector S v) = χ (Submodule.Quotient.mk a) := by
        calc
          _ = χ v + (-1) * (χ v - χ (deningerMeyerFiniteXiCausalProjector S v)) := by ring
          _ = _ := hR
      intro hz
      exact hu (he.symm.trans hz)
    by_contra! hall
    apply hp
    change χ (deningerMeyerFiniteXiCausalSection S (deningerMeyerFiniteXiJetPacketLM S v)) = 0
    rw [meyerFiniteXiCausalSection_eq_hasse_sum]
    simp only [map_sum, map_smul, hall, smul_zero, Finset.sum_const_zero]

/-- A nonzero character selects a local value idempotent with value one. -/
theorem meyerMultiplicativeDegree_detects_value
    (χ : DeningerMeyerStrongLogCohomology →ₗ[ℂ] ℂ) (hne : χ ≠ 0)
    (hm : ∀ u v, χ (deningerMeyerCohomologyConvolution u v) = χ u * χ v) :
    ∃ rho : XiDivisorSupport,
      χ (meyerHasseJetClass rho ⟨0, xiSupportMultiplicity_pos rho⟩) = 1 := by
  obtain ⟨rho, j, hj⟩ := meyerMultiplicativeDegree_detects_finite_jet χ hne hm
  have hj0 : j.val = 0 := by
    by_contra h
    exact hj (meyerMultiplicativeDegree_higher_jet_zero χ hm rho j (Nat.pos_of_ne_zero h))
  have hji : j = ⟨0, xiSupportMultiplicity_pos rho⟩ := Fin.ext hj0
  subst j
  refine ⟨rho, ?_⟩
  have hid := hm (meyerHasseJetClass rho ⟨0, xiSupportMultiplicity_pos rho⟩)
    (meyerHasseJetClass rho ⟨0, xiSupportMultiplicity_pos rho⟩)
  rw [meyerHasseJetClass_product_unit] at hid
  exact (mul_left_cancel₀ hj (by simpa only [mul_one] using hid)).symm

/-- A selected value idempotent determines the character on every local Hasse monomial. -/
private theorem multiplicativeDegree_hasse_eq_point_of_value_one
    (χ : DeningerMeyerStrongLogCohomology →ₗ[ℂ] ℂ)
    (hm : ∀ u v, χ (deningerMeyerCohomologyConvolution u v) = χ u * χ v)
    (rho : XiDivisorSupport)
    (he : χ (meyerHasseJetClass rho ⟨0, xiSupportMultiplicity_pos rho⟩) = 1)
    (sigma : XiDivisorSupport) (j : DeningerArithmeticJetIndex sigma) :
    χ (meyerHasseJetClass sigma j) = meyerPointDegree rho (meyerHasseJetClass sigma j) := by
  classical
  rw [meyerPointDegree_hasse]
  by_cases hj : j.val = 0
  · by_cases hs : rho = sigma
    · subst sigma
      have hji : j = ⟨0, xiSupportMultiplicity_pos rho⟩ := Fin.ext hj
      rw [hji, if_pos ⟨rfl, rfl⟩]
      exact he
    · rw [if_neg (fun h => hs h.1)]
      have hz := hm (meyerHasseJetClass sigma j)
        (meyerHasseJetClass rho ⟨0, xiSupportMultiplicity_pos rho⟩)
      rw [meyerHasseJetClass_product_distinct sigma rho (Ne.symm hs), map_zero, he, mul_one] at hz
      exact hz.symm
  · rw [if_neg (fun h => hj h.2)]
    exact meyerMultiplicativeDegree_higher_jet_zero χ hm sigma j (Nat.pos_of_ne_zero hj)

/-- Agreement on Hasse monomials extends through the exact finite causal expansion. -/
private theorem multiplicativeDegree_causal_eq_point_of_value_one
    (χ : DeningerMeyerStrongLogCohomology →ₗ[ℂ] ℂ)
    (hm : ∀ u v, χ (deningerMeyerCohomologyConvolution u v) = χ u * χ v)
    (rho : XiDivisorSupport)
    (he : χ (meyerHasseJetClass rho ⟨0, xiSupportMultiplicity_pos rho⟩) = 1)
    (S : Finset XiDivisorSupport) (c : DeningerMeyerFiniteXiJetPacket S) :
    χ (deningerMeyerFiniteXiCausalSection S c) =
      meyerPointDegree rho (deningerMeyerFiniteXiCausalSection S c) := by
  classical
  rw [meyerFiniteXiCausalSection_eq_hasse_sum]
  simp only [map_sum, map_smul, multiplicativeDegree_hasse_eq_point_of_value_one χ hm rho he]

/-- Every nonzero algebraic character is exactly one Xi value evaluation. -/
theorem meyerMultiplicativeDegree_eq_unique_point
    (χ : DeningerMeyerStrongLogCohomology →ₗ[ℂ] ℂ) (hne : χ ≠ 0)
    (hm : ∀ u v, χ (deningerMeyerCohomologyConvolution u v) = χ u * χ v) :
    ∃! rho : XiDivisorSupport, χ = meyerPointDegree rho := by
  classical
  obtain ⟨rho, he⟩ := meyerMultiplicativeDegree_detects_value χ hne hm
  have hχ : χ = meyerPointDegree rho := by
    apply LinearMap.ext
    intro u
    calc
      χ u = χ (deningerMeyerCohomologyConvolution u
          (meyerHasseJetClass rho ⟨0, xiSupportMultiplicity_pos rho⟩)) := by
        rw [hm, he, mul_one]
      _ = χ (deningerMeyerFiniteXiCausalProjector {rho} u) := by
        rw [meyerHasseValueClass_mul_eq_projector]
      _ = meyerPointDegree rho (deningerMeyerFiniteXiCausalProjector {rho} u) :=
        multiplicativeDegree_causal_eq_point_of_value_one χ hm rho he {rho}
          (deningerMeyerFiniteXiJetPacketLM {rho} u)
      _ = meyerPointDegree rho u := by
        change deningerMeyerXiSupportJetEvaluationLM rho ⟨0, xiSupportMultiplicity_pos rho⟩
          (deningerMeyerFiniteXiCausalProjector {rho} u) = _
        rw [meyerFiniteXiCausalProjector_jet, if_pos (Finset.mem_singleton_self rho)]
        rfl
  exact ⟨rho, hχ, fun sigma hσ => meyerPointDegree_injective (hσ.symm.trans hχ)⟩

/-- Algebraic characters have no continuity or source-admission premise. -/
theorem meyerMultiplicativeDegree_iff_point
    (χ : DeningerMeyerStrongLogCohomology →ₗ[ℂ] ℂ) :
    (χ ≠ 0 ∧ ∀ u v, χ (deningerMeyerCohomologyConvolution u v) = χ u * χ v) ↔
      ∃! rho : XiDivisorSupport, χ = meyerPointDegree rho := by
  constructor
  · rintro ⟨hne, hm⟩
    exact meyerMultiplicativeDegree_eq_unique_point χ hne hm
  · rintro ⟨rho, rfl, _⟩
    exact ⟨meyerPointDegree_ne_zero rho, meyerPointDegree_product rho⟩

/-- Arithmetic sharp reflects the point of a multiplicative degree. -/
theorem meyerPointDegree_sharp (rho : XiDivisorSupport)
    (u : DeningerMeyerStrongLogCohomology) :
    meyerPointDegree rho (meyerCohomologySharp u) =
      conj (meyerPointDegree (meyerLineReflect rho) u) := by
  induction u using Submodule.Quotient.induction_on with
  | H g =>
    rw [meyerCohomologySharp_mk, meyerPointDegree_mk, meyerPointDegree_mk,
      deningerMeyerSourceSharp_mellin, meyerLineReflect_val]
    rfl

private theorem reflection_fixed_iff (rho : XiDivisorSupport) :
    meyerLineReflect rho = rho ↔ (rho : ℂ).re = 1 / 2 := by
  constructor
  · intro h
    have hr := congrArg (fun p : XiDivisorSupport => (p : ℂ).re) h
    change 1 - (rho : ℂ).re = (rho : ℂ).re at hr
    linarith only [hr]
  · intro h
    apply Subtype.ext
    apply Complex.ext
    · change 1 - (rho : ℂ).re = (rho : ℂ).re
      linarith only [h]
    · change 0 - -(rho : ℂ).im = (rho : ℂ).im
      ring

/-- Hermitian algebraic point degrees are exactly critical point evaluations. -/
theorem meyerPointDegree_hermitian_iff (rho : XiDivisorSupport) :
    (∀ u, meyerPointDegree rho (meyerCohomologySharp u) = conj (meyerPointDegree rho u)) ↔
      (rho : ℂ).re = 1 / 2 := by
  constructor
  · intro h
    apply (reflection_fixed_iff rho).mp
    apply meyerPointDegree_injective
    apply LinearMap.ext
    intro u
    have he := h u
    rw [meyerPointDegree_sharp] at he
    have he' := congrArg conj he
    simpa only [Complex.conj_conj] using he'
  · intro h u
    rw [meyerPointDegree_sharp, (reflection_fixed_iff rho).mpr h]

/-- Positivity of an algebraic character selects exactly a critical Xi point. -/
theorem meyerPointDegree_positive_iff (rho : XiDivisorSupport) :
    (∀ u : DeningerMeyerStrongLogCohomology,
      0 ≤ (meyerDegreePair (meyerPointDegree rho) u u).re) ↔
        (rho : ℂ).re = 1 / 2 := by
  constructor
  · intro h
    by_contra hoff
    have hne : meyerLineReflect rho ≠ rho := fun he => hoff ((reflection_fixed_iff rho).mp he)
    let u := meyerHasseJetClass rho ⟨0, xiSupportMultiplicity_pos rho⟩ -
      meyerHasseJetClass (meyerLineReflect rho) ⟨0, xiSupportMultiplicity_pos _⟩
    have hfirst : meyerPointDegree rho u = 1 := by
      simp only [u, map_sub, meyerPointDegree_hasse, and_true, ↓reduceIte,
        if_neg (Ne.symm hne), sub_zero]
    have hsecond : meyerPointDegree (meyerLineReflect rho) u = -1 := by
      simp only [u, map_sub, meyerPointDegree_hasse, and_true, ↓reduceIte,
        if_neg hne, zero_sub]
    have hp := h u
    rw [meyerDegreePair, meyerPointDegree_product, meyerPointDegree_sharp,
      hfirst, hsecond, one_mul, map_neg, map_one, Complex.neg_re, Complex.one_re] at hp
    linarith only [hp]
  · intro hr u
    induction u using Submodule.Quotient.induction_on with
    | H g =>
      rw [meyerDegreePair, meyerCohomologySharp_mk,
        deningerMeyerCohomologyConvolution_mk, meyerPointDegree_sharp_square rho hr,
        Complex.ofReal_re]
      exact Complex.normSq_nonneg _

/-- Every positive nonzero multiplicative degree is a unique critical evaluation. -/
theorem meyerPositiveMultiplicativeDegree_iff_critical_point
    (χ : DeningerMeyerStrongLogCohomology →ₗ[ℂ] ℂ) :
    (χ ≠ 0 ∧
      (∀ u v, χ (deningerMeyerCohomologyConvolution u v) = χ u * χ v) ∧
      ∀ u, 0 ≤ (meyerDegreePair χ u u).re) ↔
        ∃! rho : XiDivisorSupport, χ = meyerPointDegree rho ∧ (rho : ℂ).re = 1 / 2 := by
  constructor
  · rintro ⟨hne, hm, hp⟩
    obtain ⟨rho, he, hu⟩ := meyerMultiplicativeDegree_eq_unique_point χ hne hm
    refine ⟨rho, ⟨he, ?_⟩, fun sigma hs => hu sigma hs.1⟩
    rw [he] at hp
    exact (meyerPointDegree_positive_iff rho).mp hp
  · rintro ⟨rho, ⟨rfl, hr⟩, _⟩
    exact ⟨meyerPointDegree_ne_zero rho, meyerPointDegree_product rho,
      (meyerPointDegree_positive_iff rho).mpr hr⟩

/-- All algebraic characters together read exactly the zeroth Xi values. -/
theorem meyerCharacterKernel_iff_values_zero (u : DeningerMeyerStrongLogCohomology) :
    (∀ χ : DeningerMeyerStrongLogCohomology →ₗ[ℂ] ℂ, χ ≠ 0 →
      (∀ v w, χ (deningerMeyerCohomologyConvolution v w) = χ v * χ w) → χ u = 0) ↔
        ∀ rho : XiDivisorSupport, meyerPointDegree rho u = 0 := by
  constructor
  · intro h rho
    exact h (meyerPointDegree rho) (meyerPointDegree_ne_zero rho) (meyerPointDegree_product rho)
  · intro h χ hne hm
    obtain ⟨rho, rfl, _⟩ := meyerMultiplicativeDegree_eq_unique_point χ hne hm
    exact h rho

/-- The common algebraic character kernel is the ordinary source trace radical. -/
theorem meyerCharacterKernel_source_iff_trace_radical (g : DeningerMeyerStrongLogTarget) :
    (∀ χ : DeningerMeyerStrongLogCohomology →ₗ[ℂ] ℂ, χ ≠ 0 →
      (∀ v w, χ (deningerMeyerCohomologyConvolution v w) = χ v * χ w) →
        χ (Submodule.Quotient.mk g) = 0) ↔
      ∀ h : DeningerMeyerStrongLogTarget, meyerSourceTrace g h = 0 :=
  (meyerCharacterKernel_iff_values_zero (Submodule.Quotient.mk g)).trans
    (meyerSourceTrace_radical_iff_values_zero g).symm

/-- Algebraic characters separate genuine source classes exactly when all Xi zeros are simple. -/
theorem meyerCharacters_separate_iff_simple :
    (∀ g : DeningerMeyerStrongLogTarget,
      (∀ χ : DeningerMeyerStrongLogCohomology →ₗ[ℂ] ℂ, χ ≠ 0 →
        (∀ v w, χ (deningerMeyerCohomologyConvolution v w) = χ v * χ w) →
          χ (Submodule.Quotient.mk g) = 0) ↔
        g ∈ LinearMap.range deningerMeyerStrongLogSumLM) ↔
      ∀ rho : XiDivisorSupport, xiSupportMultiplicity rho = 1 := by
  simpa only [meyerCharacterKernel_source_iff_trace_radical] using
    meyerSourceTrace_radical_eq_boundary_iff_simple

/-- Positive algebraic characters together read exactly the critical zeroth values. -/
theorem meyerPositiveCharacterKernel_iff_critical_values_zero
    (u : DeningerMeyerStrongLogCohomology) :
    (∀ χ : DeningerMeyerStrongLogCohomology →ₗ[ℂ] ℂ, χ ≠ 0 →
      (∀ v w, χ (deningerMeyerCohomologyConvolution v w) = χ v * χ w) →
      (∀ v, 0 ≤ (meyerDegreePair χ v v).re) → χ u = 0) ↔
        ∀ rho : XiDivisorSupport, (rho : ℂ).re = 1 / 2 → meyerPointDegree rho u = 0 := by
  constructor
  · intro h rho hr
    exact h (meyerPointDegree rho) (meyerPointDegree_ne_zero rho)
      (meyerPointDegree_product rho) ((meyerPointDegree_positive_iff rho).mpr hr)
  · intro h χ hne hm hp
    obtain ⟨rho, ⟨rfl, hr⟩, _⟩ :=
      (meyerPositiveMultiplicativeDegree_iff_critical_point χ).mp ⟨hne, hm, hp⟩
    exact h rho hr

/-- Positive character separation detects both off-line values and higher-jet obstructions. -/
theorem meyerPositiveCharacters_separate_iff :
    (∀ g : DeningerMeyerStrongLogTarget,
      (∀ χ : DeningerMeyerStrongLogCohomology →ₗ[ℂ] ℂ, χ ≠ 0 →
        (∀ v w, χ (deningerMeyerCohomologyConvolution v w) = χ v * χ w) →
        (∀ v, 0 ≤ (meyerDegreePair χ v v).re) → χ (Submodule.Quotient.mk g) = 0) ↔
        g ∈ LinearMap.range deningerMeyerStrongLogSumLM) ↔
      RiemannHypothesis ∧ ∀ rho : XiDivisorSupport, xiSupportMultiplicity rho = 1 := by
  constructor
  · intro h
    apply meyerSource_sharp_square_root_boundary_iff.mp
    intro g hg
    apply (h g).mp
    apply (meyerPositiveCharacterKernel_iff_critical_values_zero (Submodule.Quotient.mk g)).mpr
    intro rho hr
    have hq : (Submodule.Quotient.mk
        (deningerMeyerSourceConvolution g (deningerMeyerSourceSharp g)) :
          DeningerMeyerStrongLogCohomology) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr hg
    have hz := congrArg (meyerPointDegree rho) hq
    rw [meyerPointDegree_sharp_square rho hr, map_zero] at hz
    have hn := congrArg Complex.re hz
    rw [Complex.ofReal_re, Complex.zero_re] at hn
    exact Complex.normSq_eq_zero.mp hn
  · rintro ⟨hRH, hs⟩ g
    constructor
    · intro h
      have hv := (meyerPositiveCharacterKernel_iff_critical_values_zero
        (Submodule.Quotient.mk g)).mp h
      apply (meyerSourceTrace_radical_eq_boundary_iff_simple.mpr hs g).mp
      apply (meyerSourceTrace_radical_iff_values_zero g).mpr
      intro rho
      exact hv rho (xi_divisor_support_re_eq_half_of_rh hRH rho)
    · intro hg χ _ _ _
      have hq : (Submodule.Quotient.mk g : DeningerMeyerStrongLogCohomology) = 0 :=
        (Submodule.Quotient.mk_eq_zero _).mpr hg
      rw [hq, map_zero]

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri

