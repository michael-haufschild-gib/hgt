/-
Reflection deletion adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Moments.RadialEligibleEnergy

/-!
# Reflection deletion

Norms and residuals of the reflection deletion; norm values, frequency radii and losses of
sector localization; negligibility of small and upper reflected parts.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Classical Topology InnerProductSpace ComplexConjugate MatrixGroups ENNReal
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicJacobi CubicKubota CubicRamified
open scoped NNReal Pointwise
open RationalSource
open scoped Manifold ContDiff
open scoped Matrix
open UniqueFactorizationMonoid
open Asymptotics
open scoped ContDiff FourierTransform SchwartzMap
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology
open Filter
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical SchwartzMap
open scoped Classical SchwartzMap FourierTransform ContDiff
open scoped Classical
open scoped Classical
open scoped Classical
open scoped Classical SchwartzMap
open MeasureTheory
open scoped BigOperators Classical ContDiff SchwartzMap FourierTransform
open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace CenteredMomentReflectionDeletion
open HeckeFamily CenteredMomentComparisonReflection UniqueFactorizationMonoid
open  SchwartzPlanePoisson 
local notation "O" => Eisenstein.O
local notation "NI" => CubicEisenstein.NonzeroIdeal

def norm (I : NI) : ℝ := I.val.absNorm
lemma norm_pos (I : NI) : 0 < norm I := HeckeDyadic.norm_pos I

def outside (S : Finset (Ideal O)) (I : Ideal O) : Prop := ∀ P ∈ S, ¬ P ∣ I
abbrev SmoothIdeal (S : Finset (Ideal O)) := {I : NI // primeSupport I.val ⊆ S}
abbrev OutsideIdeal (S : Finset (Ideal O)) := {I : NI // outside S I.val}

def extract (S : Finset (Ideal O)) (I : Ideal O) : Ideal O :=
  ((normalizedFactors I).filter (· ∈ S)).prod
def residual (S : Finset (Ideal O)) (I : Ideal O) : Ideal O :=
  ((normalizedFactors I).filter (· ∉ S)).prod
lemma extract_factors (S : Finset (Ideal O)) (I : Ideal O) :
    normalizedFactors (extract S I) = (normalizedFactors I).filter (· ∈ S) :=
  normalizedFactors_prod_eq_self_of_subset
    (fun _ h => (Multiset.mem_filter.mp h).1)
lemma residual_factors (S : Finset (Ideal O)) (I : Ideal O) :
    normalizedFactors (residual S I) = (normalizedFactors I).filter (· ∉ S) :=
  normalizedFactors_prod_eq_self_of_subset
    (fun _ h => (Multiset.mem_filter.mp h).1)
lemma extract_ne_zero (S : Finset (Ideal O)) (I : Ideal O) : extract S I ≠ 0 :=
  prod_ne_zero_of_subset_normalizedFactors
    (fun _ h => (Multiset.mem_filter.mp h).1)
lemma residual_ne_zero (S : Finset (Ideal O)) (I : Ideal O) : residual S I ≠ 0 :=
  prod_ne_zero_of_subset_normalizedFactors
    (fun _ h => (Multiset.mem_filter.mp h).1)
lemma reconstruct (S : Finset (Ideal O)) (I : NI) :
    extract S I.val * residual S I.val = I.val := by
  rw [extract, residual, ← Multiset.prod_add, Multiset.filter_add_not]
  exact Ideal.prod_normalizedFactors_eq_self I.property
lemma extract_smooth (S : Finset (Ideal O)) (I : Ideal O) :
    primeSupport (extract S I) ⊆ S := by
  intro P hP
  have hh : P ∈ normalizedFactors I ∧ P ∈ S := by
    simpa only [primeSupport, extract_factors, Multiset.mem_toFinset, Multiset.mem_filter] using hP
  exact hh.2
lemma outside_iff_factors (S : Finset (Ideal O)) (hS : ∀ P ∈ S, Prime P) (I : NI) :
    outside S I.val ↔ ∀ P ∈ normalizedFactors I.val, P ∉ S := by
  constructor
  · intro h P hP hPS
    exact h P hPS (dvd_of_mem_normalizedFactors hP)
  · intro h P hPS hd
    exact h P ((mem_normalizedFactors_iff I.property).mpr ⟨hS P hPS, hd⟩) hPS
lemma residual_outside (S : Finset (Ideal O)) (hS : ∀ P ∈ S, Prime P) (I : Ideal O) :
    outside S (residual S I) := by
  rw [outside_iff_factors S hS ⟨_, residual_ne_zero S I⟩, residual_factors]
  intro P hP
  exact (Multiset.mem_filter.mp hP).2
lemma split_product (S : Finset (Ideal O)) (hS : ∀ P ∈ S, Prime P)
    (D : SmoothIdeal S) (J : OutsideIdeal S) :
    extract S (D.val.val * J.val.val) = D.val.val ∧
      residual S (D.val.val * J.val.val) = J.val.val := by
  have hd : (normalizedFactors D.val.val).filter (· ∈ S) = normalizedFactors D.val.val :=
    Multiset.filter_eq_self.mpr (fun P hP => D.property (Multiset.mem_toFinset.mpr hP))
  have hj : (normalizedFactors J.val.val).filter (· ∈ S) = 0 := by
    apply Multiset.filter_eq_nil.mpr
    intro P hP
    exact (outside_iff_factors S hS J.val).mp J.property P hP
  have hd' : (normalizedFactors D.val.val).filter (· ∉ S) = 0 := by
    apply Multiset.filter_eq_nil.mpr
    intro P hP
    exact not_not.mpr (D.property (Multiset.mem_toFinset.mpr hP))
  have hj' : (normalizedFactors J.val.val).filter (· ∉ S) = normalizedFactors J.val.val :=
    Multiset.filter_eq_self.mpr ((outside_iff_factors S hS J.val).mp J.property)
  simp only [extract, residual, normalizedFactors_mul D.val.property J.val.property,
    Multiset.filter_add, hd, hj, hd', hj', add_zero, zero_add,
    Ideal.prod_normalizedFactors_eq_self D.val.property,
    Ideal.prod_normalizedFactors_eq_self J.val.property, and_self]

def splitEquiv (S : Finset (Ideal O)) (hS : ∀ P ∈ S, Prime P) :
    NI ≃ SmoothIdeal S × OutsideIdeal S where
  toFun I := (⟨⟨extract S I.val, extract_ne_zero S I.val⟩, extract_smooth S I.val⟩,
    ⟨⟨residual S I.val, residual_ne_zero S I.val⟩, residual_outside S hS I.val⟩)
  invFun p := ⟨p.1.val.val * p.2.val.val, mul_ne_zero p.1.val.property p.2.val.property⟩
  left_inv I := Subtype.ext (reconstruct S I)
  right_inv p := by
    obtain ⟨hd, hj⟩ := split_product S hS p.1 p.2
    exact Prod.ext (Subtype.ext (Subtype.ext hd)) (Subtype.ext (Subtype.ext hj))

lemma outside_iff_coprime (S : Finset (Ideal O)) (hS : ∀ P ∈ S, Prime P) (I : NI) :
    outside S I.val ↔ ∀ P ∈ S, IsCoprime I.val P := by
  have he (P : Ideal O) (hP : Prime P) : primeSupport P = {P} := by
    simp only [primeSupport]
    have hf : normalizedFactors P = {P} := by
      simpa using normalizedFactors_prod_of_prime (m := ({P} : Multiset (Ideal O)))
        (by intro Q hQ; simpa only [Multiset.mem_singleton.mp hQ] using hP)
    simp [hf]
  simp only [outside]
  apply forall_congr'
  intro P
  apply forall_congr'
  intro hP
  rw [← CenteredMomentSupport.primeSupport_disjoint_iff I.property (hS P hP).ne_zero,
    he P (hS P hP), Finset.disjoint_singleton_right]
  simp only [primeSupport, Multiset.mem_toFinset,
    mem_normalizedFactors_iff I.property, hS P hP, true_and]

lemma deleted_coefficient (η : Character) (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (I : NI) :
    idealCoeff (η.excludePrimes S hS) I.val =
      if outside S I.val then idealCoeff η I.val else 0 := by
  rw [idealCoeff_excludePrimes, outside_iff_coprime S hS I]
  split_ifs <;> rfl

def DecayTwo (F : ℝ → ℂ) : Prop := ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 < x → x^2 * ‖F x‖ ≤ C

lemma schwartz_decayTwo (W : 𝓢(ℝ,ℂ)) : DecayTwo W := by
  refine ⟨SchwartzMap.seminorm ℝ 2 0 W, apply_nonneg _ _, ?_⟩
  intro x hx
  simpa only [Real.norm_eq_abs, abs_of_pos hx] using
    SchwartzMap.norm_pow_mul_le_seminorm ℝ W 2 x

lemma reflected_decayTwo (W : 𝓢(ℝ,ℂ)) : DecayTwo (paperRadialFourier W) := by
  obtain ⟨s,C,hC,hb⟩ := paperRadialFourier_source_weighted_bound 2
  refine ⟨C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W, by positivity, ?_⟩
  intro x hx
  exact (mul_le_mul_of_nonneg_right (by nlinarith : x^2 ≤ (1+x)^2)
    (norm_nonneg _)).trans (hb W x hx.le)

lemma inverse_norm_sq_summable : Summable (fun I : NI => (norm I ^ 2)⁻¹) := by
  have h := (fullIdealWeight_summable_norm (2 : ℂ) (by norm_num)).subtype
    (fun I : Ideal O => I ≠ 0)
  apply h.congr
  intro I
  change ‖fullIdealWeight (2 : ℂ) I.val‖ = (norm I ^ 2)⁻¹
  rw [fullIdealWeight, if_neg I.property]
  have hn := Complex.norm_cpow_eq_rpow_re_of_pos (norm_pos I) (-(2 : ℂ))
  norm_num [norm, Complex.ofReal_natCast, Complex.neg_re] at hn
  change ‖(Ideal.absNorm I.val : ℂ) ^ (-(2 : ℂ))‖ = ((Ideal.absNorm I.val : ℝ)^2)⁻¹
  exact hn

lemma radial_summable_norm (F : ℝ → ℂ) (hF : DecayTwo F) (X : ℝ) (hX : 0 < X) :
    Summable (fun I : NI => ‖F (norm I / X)‖) := by
  obtain ⟨C,hC,hb⟩ := hF
  apply (inverse_norm_sq_summable.mul_left (C*X^2)).of_nonneg_of_le (fun _ => norm_nonneg _)
  intro I
  have hx := div_pos (norm_pos I) hX
  have h : ‖F (norm I / X)‖ ≤ C / (norm I / X)^2 :=
    (le_div_iff₀ (sq_pos_of_pos hx)).mpr (by nlinarith [hb _ hx])
  exact h.trans_eq (by field_simp)

lemma plain_summable (η : Character) (F : ℝ → ℂ) (hF : DecayTwo F) (X : ℝ) (hX : 0< X) :
    Summable (fun I : NI => idealCoeff η I.val * F (norm I / X)) := by
  apply Summable.of_norm
  apply (radial_summable_norm F hF X hX).of_nonneg_of_le (fun _ => norm_nonneg _)
  intro I
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (idealCoeff_norm_le_one η I.val)

lemma pair_radial_summable_norm (F : ℝ → ℂ) (hF : DecayTwo F) (X : ℝ) (hX : 0 < X) :
    Summable (fun p : NI × NI => ‖F (norm p.1 * norm p.2 / X)‖) := by
  obtain ⟨C,hC,hb⟩ := hF
  have hs := inverse_norm_sq_summable.mul_of_nonneg inverse_norm_sq_summable
    (fun I => by positivity) (fun I => by positivity)
  apply (hs.mul_left (C*X^2)).of_nonneg_of_le (fun _ => norm_nonneg _)
  intro p
  have hx := div_pos (mul_pos (norm_pos p.1) (norm_pos p.2)) hX
  have h : ‖F (norm p.1 * norm p.2 / X)‖ ≤ C / (norm p.1 * norm p.2 / X)^2 :=
    (le_div_iff₀ (sq_pos_of_pos hx)).mpr (by nlinarith [hb _ hx])
  exact h.trans_eq (by field_simp)

lemma restricted_pair_summable (η : Character) (S : Finset (Ideal O))
    (F : ℝ → ℂ) (hF : DecayTwo F) (X : ℝ) (hX : 0 < X) :
    Summable (fun p : SmoothIdeal S × OutsideIdeal S =>
      idealCoeff η (p.1.val.val * p.2.val.val) * F (norm p.1.val * norm p.2.val / X)) := by
  have hi : Function.Injective (fun p : SmoothIdeal S × OutsideIdeal S => (p.1.val,p.2.val)) := by
    intro p q h
    exact Prod.ext (Subtype.ext (congrArg Prod.fst h)) (Subtype.ext (congrArg Prod.snd h))
  apply ((pair_radial_summable_norm F hF X hX).comp_injective hi).of_norm_bounded
  intro p
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (idealCoeff_norm_le_one η _)

lemma outside_plain_tsum (η : Character) (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (F : ℝ → ℂ) (X : ℝ) :
    (∑' I : OutsideIdeal S, idealCoeff η I.val.val * F (norm I.val / X)) =
      ∑' I : NI, idealCoeff (η.excludePrimes S hS) I.val * F (norm I / X) := by
  have he := tsum_subtype {I : NI | outside S I.val}
    (fun I : NI => idealCoeff η I.val * F (norm I / X))
  change (∑' I : OutsideIdeal S, idealCoeff η I.val.val * F (norm I.val / X)) = _ at he
  rw [he]
  apply tsum_congr
  intro I
  rw [deleted_coefficient]
  by_cases hI : outside S I.val <;> simp [Set.indicator, hI]

lemma restoration_inner (η : Character) (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (F : ℝ → ℂ) (X : ℝ) (D : SmoothIdeal S) :
    (∑' J : OutsideIdeal S, idealCoeff η (D.val.val * J.val.val) *
      F (norm D.val * norm J.val / X)) =
    idealCoeff η D.val.val *
      ∑' I : NI, idealCoeff (η.excludePrimes S hS) I.val * F (norm I / (X / norm D.val)) := by
  rw [← outside_plain_tsum η S hS F, ← tsum_mul_left]
  apply tsum_congr
  intro J
  rw [map_mul, mul_assoc]
  congr 2
  field_simp

lemma restoration_plain_summable (η : Character) (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (F : ℝ → ℂ) (hF : DecayTwo F) (X : ℝ) (hX : 0 < X) :
    Summable (fun D : SmoothIdeal S => idealCoeff η D.val.val *
      ∑' I : NI, idealCoeff (η.excludePrimes S hS) I.val * F (norm I / (X / norm D.val))) := by
  exact (restricted_pair_summable η S F hF X hX).prod.congr
    (fun D => restoration_inner η S hS F X D)

theorem restoration_plain (η : Character) (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (F : ℝ → ℂ) (hF : DecayTwo F) (X : ℝ) (hX : 0 < X) :
    (∑' I : NI, idealCoeff η I.val * F (norm I / X)) =
      ∑' D : SmoothIdeal S, idealCoeff η D.val.val *
        ∑' I : NI, idealCoeff (η.excludePrimes S hS) I.val * F (norm I / (X / norm D.val)) := by
  have he := (splitEquiv S hS).symm.tsum_eq
    (fun I : NI => idealCoeff η I.val * F (norm I / X))
  have hp := (restricted_pair_summable η S F hF X hX).tsum_prod
  have hpoint (p : SmoothIdeal S × OutsideIdeal S) :
      norm ((splitEquiv S hS).symm p) = norm p.1.val * norm p.2.val := by
    change (Ideal.absNorm (p.1.val.val * p.2.val.val) : ℝ) = _
    rw [map_mul, Nat.cast_mul]
    rfl
  simp only [hpoint] at he
  rw [← he]
  change (∑' p : SmoothIdeal S × OutsideIdeal S,
    idealCoeff η (p.1.val.val * p.2.val.val) * F (norm p.1.val * norm p.2.val / X)) = _
  rw [hp]
  exact tsum_congr (fun D => restoration_inner η S hS F X D)

lemma normalization_factor (X N : ℝ) (hX : 0< X) (hN : 0< N) :
    (Real.sqrt N : ℂ)⁻¹ * (Real.sqrt (X/N) : ℂ)⁻¹ = (Real.sqrt X : ℂ)⁻¹ := by
  rw [Real.sqrt_div hX.le, Complex.ofReal_div]
  have hn : (Real.sqrt N : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hN).ne'
  field_simp

lemma normalized_restoration_term (η : Character) (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (F : ℝ → ℂ) (X : ℝ) (hX : 0< X) (D : SmoothIdeal S) :
    idealCoeff η D.val.val / (Real.sqrt (norm D.val) : ℂ) *
      HeckeDyadic.polynomial (η.excludePrimes S hS) false F (X / norm D.val) 0 0 =
    (Real.sqrt X : ℂ)⁻¹ * (idealCoeff η D.val.val *
      ∑' I : NI, idealCoeff (η.excludePrimes S hS) I.val * F (norm I / (X / norm D.val))) := by
  rw [polynomial_plain _ _ _ (div_pos hX (norm_pos D.val))]
  change idealCoeff η D.val.val / (Real.sqrt (norm D.val) : ℂ) *
    ((Real.sqrt (X / norm D.val) : ℂ)⁻¹ *
    ∑' I : NI, idealCoeff (η.excludePrimes S hS) I.val * F (norm I / (X / norm D.val))) = _
  have h := normalization_factor X (norm D.val) hX (norm_pos D.val)
  rw [div_eq_mul_inv]
  linear_combination (idealCoeff η D.val.val *
    ∑' I : NI, idealCoeff (η.excludePrimes S hS) I.val * F (norm I / (X / norm D.val))) * h

theorem normalized_restoration (η : Character) (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (F : ℝ → ℂ) (hF : DecayTwo F) (X : ℝ) (hX : 0< X) :
    Summable (fun D : SmoothIdeal S => idealCoeff η D.val.val / (Real.sqrt (norm D.val) : ℂ) *
      HeckeDyadic.polynomial (η.excludePrimes S hS) false F (X / norm D.val) 0 0) ∧
    HeckeDyadic.polynomial η false F X 0 0 =
      ∑' D : SmoothIdeal S, idealCoeff η D.val.val / (Real.sqrt (norm D.val) : ℂ) *
        HeckeDyadic.polynomial (η.excludePrimes S hS) false F (X / norm D.val) 0 0 := by
  constructor
  · apply ((restoration_plain_summable η S hS F hF X hX).mul_left (Real.sqrt X : ℂ)⁻¹).congr
    intro D
    exact (normalized_restoration_term η S hS F X hX D).symm
  · rw [polynomial_plain _ _ _ hX]
    change (Real.sqrt X : ℂ)⁻¹ * (∑' I : NI, idealCoeff η I.val * F (norm I / X)) = _
    rw [restoration_plain η S hS F hF X hX, ← tsum_mul_left]
    apply tsum_congr
    intro D
    exact (normalized_restoration_term η S hS F X hX D).symm

theorem reflected_normalized_restoration (η : Character) (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (W : 𝓢(ℝ,ℂ)) (X : ℝ) (hX : 0< X) :
    Summable (fun D : SmoothIdeal S => idealCoeff η D.val.val / (Real.sqrt (norm D.val) : ℂ) *
      HeckeDyadic.polynomial (η.excludePrimes S hS) false (paperRadialFourier W) (X / norm D.val) 0 0) ∧
    HeckeDyadic.polynomial η false (paperRadialFourier W) X 0 0 =
      ∑' D : SmoothIdeal S, idealCoeff η D.val.val / (Real.sqrt (norm D.val) : ℂ) *
        HeckeDyadic.polynomial (η.excludePrimes S hS) false (paperRadialFourier W) (X / norm D.val) 0 0 :=
  normalized_restoration η S hS _ (reflected_decayTwo W) X hX

def outsideSum (η : Character) (S : Finset (Ideal O)) (F : ℝ → ℂ) (X : ℝ) : ℂ :=
  ∑' I : NI, (if outside S I.val then idealCoeff η I.val else 0) * F (norm I / X)

lemma outsideSum_summable (η : Character) (S : Finset (Ideal O))
    (F : ℝ → ℂ) (hF : DecayTwo F) (X : ℝ) (hX : 0< X) :
    Summable (fun I : NI => (if outside S I.val then idealCoeff η I.val else 0) * F (norm I / X)) := by
  apply (radial_summable_norm F hF X hX).of_norm_bounded
  intro I
  split_ifs
  · rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (idealCoeff_norm_le_one η I.val)
  · simp

lemma outside_mul_prime (S : Finset (Ideal O)) (hS : ∀ Q ∈ S, Prime Q)
    (P : Ideal O) (hP : Prime P) (hPS : P ∉ S) (I : Ideal O) :
    outside S (P*I) ↔ outside S I := by
  have hn (Q : Ideal O) (hQ : Q ∈ S) : ¬ Q ∣ P := by
    intro hd
    have he : Q = P := associated_iff_eq.mp (((hS Q hQ).dvd_prime_iff_associated hP).mp hd)
    exact hPS (he ▸ hQ)
  simp only [outside]
  apply forall_congr'
  intro Q
  apply forall_congr'
  intro hQ
  rw [(hS Q hQ).dvd_mul, not_or, and_iff_right (hn Q hQ)]

lemma prime_shift_tsum (η : Character) (S : Finset (Ideal O))
    (hS : ∀ Q ∈ S, Prime Q) (P : Ideal O) (hP : Prime P) (hPS : P ∉ S)
    (F : ℝ → ℂ) (X : ℝ) :
    (∑' I : NI, if P ∣ I.val then
      (if outside S I.val then idealCoeff η I.val else 0) * F (norm I / X) else 0) =
    idealCoeff η P * outsideSum η S F (X / (P.absNorm : ℝ)) := by
  let f : NI → ℂ := fun I => if P ∣ I.val then
    (if outside S I.val then idealCoeff η I.val else 0) * F (norm I / X) else 0
  let g : NI → ℂ := fun I => idealCoeff η P *
    ((if outside S I.val then idealCoeff η I.val else 0) * F (norm I / (X / (P.absNorm : ℝ))))
  let e : NI → NI := fun I => ⟨P*I.val, mul_ne_zero hP.ne_zero I.property⟩
  have he (I : NI) : f (e I) = g I := by
    have hn : norm (e I) = (P.absNorm : ℝ) * norm I := by
      simp only [norm, e, map_mul, Nat.cast_mul]
    simp only [f, e, dvd_mul_right, ite_true, outside_mul_prime S hS P hP hPS,
      map_mul, g]
    change (if outside S I.val then idealCoeff η P * idealCoeff η I.val else 0) *
      F (norm (e I) / X) = _
    rw [hn]
    by_cases ho : outside S I.val
    · simp only [ho, ite_true, mul_assoc]
      congr 2
      rw [div_div_eq_mul_div, mul_comm]
    · simp [ho]
  have hi : Function.Injective e := by
    intro I J hij
    exact Subtype.ext (mul_left_cancel₀ hP.ne_zero (congrArg Subtype.val hij))
  have hsum : (∑' I, f I) = ∑' I, g I := by
    apply tsum_eq_tsum_of_ne_zero_bij (fun I : Function.support g => e I.val)
    · exact hi.comp Subtype.val_injective
    · intro I hI
      have hd : P ∣ I.val := by
        by_contra hn
        exact hI (by simp [f, hn])
      obtain ⟨J,hJ⟩ := hd
      have hj : J ≠ 0 := by intro hz; exact I.property (by rw [hJ,hz,mul_zero])
      have hei : e ⟨J,hj⟩ = I := Subtype.ext hJ.symm
      have hg : g ⟨J,hj⟩ ≠ 0 := by rw [← he, hei]; exact hI
      exact ⟨⟨⟨J,hj⟩,hg⟩,hei⟩
    · intro I; exact he I.val
  change (∑' I, f I) = _
  rw [hsum, tsum_mul_left]
  rfl

lemma outsideSum_insert (η : Character) (S : Finset (Ideal O))
    (hS : ∀ Q ∈ S, Prime Q) (P : Ideal O) (hP : Prime P) (hPS : P ∉ S)
    (F : ℝ → ℂ) (hF : DecayTwo F) (X : ℝ) (hX : 0< X) :
    outsideSum η (insert P S) F X = outsideSum η S F X -
      idealCoeff η P * outsideSum η S F (X / (P.absNorm : ℝ)) := by
  have hs := outsideSum_summable η S F hF X hX
  have hd : Summable (fun I : NI => if P ∣ I.val then
      (if outside S I.val then idealCoeff η I.val else 0) * F (norm I / X) else 0) := by
    exact hs.indicator {I : NI | P ∣ I.val}
  rw [← prime_shift_tsum η S hS P hP hPS F X]
  simp only [outsideSum]
  rw [← hs.tsum_sub hd]
  apply tsum_congr
  intro I
  have hi : outside (insert P S) I.val = (¬ P ∣ I.val ∧ outside S I.val) := by
    simp [outside, Finset.mem_insert]
  rw [hi]
  by_cases hp : P ∣ I.val <;> by_cases ho : outside S I.val <;>
    simp [hp, ho]

lemma subset_product_nonzero (S : Finset (Ideal O)) (hS : ∀ P ∈ S, Prime P) :
    (∏ P ∈ S, P) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun P hP => (hS P hP).ne_zero)
lemma subset_product_norm_pos (S : Finset (Ideal O)) (hS : ∀ P ∈ S, Prime P) :
    0 < (Ideal.absNorm (∏ P ∈ S, P) : ℝ) := by
  exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (subset_product_nonzero S hS))

theorem finite_deletion_plain (η : Character) (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (F : ℝ → ℂ) (hF : DecayTwo F) (X : ℝ) (hX : 0< X) :
    outsideSum η S F X = ∑ D ∈ S.powerset, (-1 : ℂ)^D.card * idealCoeff η (∏ P ∈ D, P) *
      (∑' I : NI, idealCoeff η I.val * F (norm I / (X / (Ideal.absNorm (∏ P ∈ D, P) : ℝ)))) := by
  induction S using Finset.induction_on generalizing X with
  | empty => simp [outsideSum, outside]
  | @insert P S hPS ih =>
    have hP := hS P (Finset.mem_insert_self _ _)
    have hSS : ∀ Q ∈ S, Prime Q := fun Q hQ => hS Q (Finset.mem_insert_of_mem hQ)
    have hn : 0 < (P.absNorm : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hP.ne_zero)
    rw [outsideSum_insert η S hSS P hP hPS F hF X hX,
      ih hSS X hX, ih hSS (X / (P.absNorm : ℝ)) (div_pos hX hn),
      Finset.sum_powerset_insert hPS, Finset.mul_sum]
    rw [sub_eq_add_neg]
    congr 1
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro D hD
    have hPD : P ∉ D := fun h => hPS ((Finset.mem_powerset.mp hD) h)
    rw [Finset.card_insert_of_notMem hPD, Finset.prod_insert hPD, map_mul,
      map_mul, Nat.cast_mul, pow_succ]
    have hh : X / ((P.absNorm : ℝ) * (Ideal.absNorm (∏ Q ∈ D,Q) : ℝ)) =
        (X / (P.absNorm : ℝ)) / (Ideal.absNorm (∏ Q ∈ D,Q) : ℝ) := by rw [div_div]
    rw [hh]
    ring

lemma normalized_dilation_term (η : Character) (F : ℝ → ℂ) (X : ℝ)
    (hX : 0< X) (D : NI) :
    idealCoeff η D.val / (Real.sqrt (norm D) : ℂ) *
      HeckeDyadic.polynomial η false F (X / norm D) 0 0 =
    (Real.sqrt X : ℂ)⁻¹ * (idealCoeff η D.val *
      ∑' I : NI, idealCoeff η I.val * F (norm I / (X / norm D))) := by
  rw [polynomial_plain _ _ _ (div_pos hX (norm_pos D))]
  change idealCoeff η D.val / (Real.sqrt (norm D) : ℂ) *
    ((Real.sqrt (X / norm D) : ℂ)⁻¹ *
      ∑' I : NI, idealCoeff η I.val * F (norm I / (X / norm D))) = _
  have h := normalization_factor X (norm D) hX (norm_pos D)
  rw [div_eq_mul_inv]
  linear_combination (idealCoeff η D.val *
    ∑' I : NI, idealCoeff η I.val * F (norm I / (X / norm D))) * h

theorem normalized_finite_deletion (η : Character) (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (F : ℝ → ℂ) (hF : DecayTwo F) (X : ℝ) (hX : 0< X) :
    HeckeDyadic.polynomial (η.excludePrimes S hS) false F X 0 0 =
      ∑ D ∈ S.powerset, (-1 : ℂ)^D.card *
        (idealCoeff η (∏ P ∈ D,P) / (Real.sqrt (Ideal.absNorm (∏ P ∈ D,P) : ℝ) : ℂ)) *
        HeckeDyadic.polynomial η false F (X / (Ideal.absNorm (∏ P ∈ D,P) : ℝ)) 0 0 := by
  rw [polynomial_plain _ _ _ hX]
  have he : (∑' I : NI, idealCoeff (η.excludePrimes S hS) I.val * F ((I.val.absNorm : ℝ) / X)) =
      outsideSum η S F X := by
    apply tsum_congr
    intro I
    rw [deleted_coefficient]
    rfl
  rw [he, finite_deletion_plain η S hS F hF X hX, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro D hD
  have hDS : ∀ P ∈ D, Prime P := fun P hP => hS P ((Finset.mem_powerset.mp hD) hP)
  have ht := normalized_dilation_term η F X hX ⟨∏P∈D,P, subset_product_nonzero D hDS⟩
  dsimp only [norm] at ht
  dsimp only [norm]
  linear_combination -(-1 : ℂ)^D.card * ht

lemma subset_product_moebius (D : Finset (Ideal O)) (hD : ∀ P ∈ D, Prime P) :
    (moebius (∏ P ∈ D,P) : ℂ) = (-1 : ℂ)^D.card := by
  have hf : normalizedFactors (∏ P ∈ D,P) = D.val := by
    simpa using normalizedFactors_prod_of_prime (m := D.val) hD
  have hs : Squarefree (∏ P ∈ D,P) := by
    rw [squarefree_iff_nodup_normalizedFactors (subset_product_nonzero D hD), hf]
    exact D.nodup
  rw [hs.moebius_eq, factors_eq_normalizedFactors, hf]
  simp

theorem normalized_finite_deletion_moebius (η : Character) (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (F : ℝ → ℂ) (hF : DecayTwo F) (X : ℝ) (hX : 0< X) :
    HeckeDyadic.polynomial (η.excludePrimes S hS) false F X 0 0 =
      ∑ D ∈ S.powerset, (moebius (∏ P ∈ D,P) : ℂ) *
        (idealCoeff η (∏ P ∈ D,P) / (Real.sqrt (Ideal.absNorm (∏ P ∈ D,P) : ℝ) : ℂ)) *
        HeckeDyadic.polynomial η false F (X / (Ideal.absNorm (∏ P ∈ D,P) : ℝ)) 0 0 := by
  rw [normalized_finite_deletion η S hS F hF X hX]
  apply Finset.sum_congr rfl
  intro D hD
  rw [subset_product_moebius D (fun P hP => hS P ((Finset.mem_powerset.mp hD) hP))]

def reflectedTerm (η ηi : Character) (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (F : ℝ → ℂ) (X Q : ℝ)
    (D : Finset (Ideal O)) (H : SmoothIdeal S) : ℂ :=
  (moebius (∏ P ∈ D,P) : ℂ) * idealCoeff η (∏ P ∈ D,P) * idealCoeff ηi H.val.val /
    (Real.sqrt ((Ideal.absNorm (∏ P ∈ D,P) : ℝ) * norm H.val) : ℂ) *
    HeckeDyadic.polynomial (ηi.excludePrimes S hS) false F
      (Q * (Ideal.absNorm (∏ P ∈ D,P) : ℝ) / (X * norm H.val)) 0 0

lemma reflectedTerm_eq (η ηi : Character) (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (F : ℝ → ℂ) (X Q : ℝ)
    (D : Finset (Ideal O)) (H : SmoothIdeal S) :
    reflectedTerm η ηi S hS F X Q D H =
      ((moebius (∏ P ∈ D,P) : ℂ) *
        (idealCoeff η (∏ P ∈ D,P) / (Real.sqrt (Ideal.absNorm (∏ P ∈ D,P) : ℝ) : ℂ))) *
      (idealCoeff ηi H.val.val / (Real.sqrt (norm H.val) : ℂ) *
        HeckeDyadic.polynomial (ηi.excludePrimes S hS) false F
          ((Q / (X / (Ideal.absNorm (∏ P ∈ D,P) : ℝ))) / norm H.val) 0 0) := by
  have hs : Q * (Ideal.absNorm (∏ P ∈ D,P) : ℝ) / (X * norm H.val) =
      (Q / (X / (Ideal.absNorm (∏ P ∈ D,P) : ℝ))) / norm H.val := by
    simp only [div_div_eq_mul_div, div_div]
  unfold reflectedTerm
  rw [hs, Real.sqrt_mul (Nat.cast_nonneg _), Complex.ofReal_mul]
  ring

theorem deletion_reflection (η ηi : Character) (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (W F : ℝ → ℂ) (hW : DecayTwo W) (hF : DecayTwo F)
    (G : ℂ) (Q : ℝ) (hQ : 0< Q)
    (hreflect : ∀ Y : ℝ, 0< Y → HeckeDyadic.polynomial η false W Y 0 0 =
      G * HeckeDyadic.polynomial ηi false F (Q/Y) 0 0)
    (X : ℝ) (hX : 0< X) :
    (∀ D ∈ S.powerset, Summable (reflectedTerm η ηi S hS F X Q D)) ∧
    HeckeDyadic.polynomial (η.excludePrimes S hS) false W X 0 0 =
      G * ∑ D ∈ S.powerset, ∑' H : SmoothIdeal S, reflectedTerm η ηi S hS F X Q D H := by
  have hnorm (D : Finset (Ideal O)) (hD : D ∈ S.powerset) :
      0 < (Ideal.absNorm (∏ P ∈ D,P) : ℝ) :=
    subset_product_norm_pos D (fun P hP => hS P ((Finset.mem_powerset.mp hD) hP))
  constructor
  · intro D hD
    have hs := (normalized_restoration ηi S hS F hF (Q/(X/(Ideal.absNorm (∏ P ∈ D,P) : ℝ)))
      (div_pos hQ (div_pos hX (hnorm D hD)))).1
    exact (hs.mul_left ((moebius (∏ P ∈ D,P) : ℂ) *
      (idealCoeff η (∏ P ∈ D,P) / (Real.sqrt (Ideal.absNorm (∏ P ∈ D,P) : ℝ) : ℂ)))).congr
      (fun H => (reflectedTerm_eq η ηi S hS F X Q D H).symm)
  · rw [normalized_finite_deletion_moebius η S hS W hW X hX, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro D hD
    rw [hreflect _ (div_pos hX (hnorm D hD)),
      (normalized_restoration ηi S hS F hF (Q/(X/(Ideal.absNorm (∏ P ∈ D,P) : ℝ)))
        (div_pos hQ (div_pos hX (hnorm D hD)))).2]
    rw [mul_left_comm]
    congr 1
    rw [← tsum_mul_left]
    apply tsum_congr
    intro H
    rw [reflectedTerm_eq]

theorem primitive_deleted_reflection (c : O) [NeZero c]
    (χ : MulChar (O⧸Ideal.span {c}) ℂ)
    (hu : ∀ u : Oˣ, χ (Ideal.Quotient.mk (Ideal.span {c}) u.val) = 1)
    (hp : FiniteFourier.IsPrimitiveOnIdeals χ) (hχ : χ ≠ 1)
    (S : Finset (Ideal O)) (hS : ∀ P ∈ S, Prime P)
    (W : 𝓢(ℝ,ℂ)) (X : ℝ) (hX : 0< X) :
    let η := HeckePrimitive.character c χ hu
    let ηi := HeckePrimitive.character c χ⁻¹ (HeckePrimitive.inverse_unit_trivial c χ hu)
    let Q := ‖ringComplex c‖^2
    (∀ D ∈ S.powerset, Summable (reflectedTerm η ηi S hS (paperRadialFourier W) X Q D)) ∧
    HeckeDyadic.polynomial (η.excludePrimes S hS) false W X 0 0 =
      TraceCharacter.normalizedGauss c χ *
        ∑ D ∈ S.powerset, ∑' H : SmoothIdeal S,
          reflectedTerm η ηi S hS (paperRadialFourier W) X Q D H := by
  dsimp only
  apply deletion_reflection _ _ S hS W (paperRadialFourier W)
    (schwartz_decayTwo W) (reflected_decayTwo W) _ _ _
    (fun Y hY => primitive_normalized_reflection c χ hu hp hχ W Y hY) X hX
  exact sq_pos_of_pos (norm_pos_iff.mpr (ringComplex_ne_zero (NeZero.ne c)))

theorem primitive_deleted_reflection_absolute (c : O) [NeZero c]
    (χ : MulChar (O⧸Ideal.span {c}) ℂ)
    (hu : ∀ u : Oˣ, χ (Ideal.Quotient.mk (Ideal.span {c}) u.val) = 1)
    (hp : FiniteFourier.IsPrimitiveOnIdeals χ) (hχ : χ ≠ 1)
    (S : Finset (Ideal O)) (hS : ∀ P ∈ S, Prime P)
    (W : 𝓢(ℝ,ℂ)) (X : ℝ) (hX : 0< X) :
    let η := HeckePrimitive.character c χ hu
    let ηi := HeckePrimitive.character c χ⁻¹ (HeckePrimitive.inverse_unit_trivial c χ hu)
    let Q := ‖ringComplex c‖^2
    Summable (fun H : SmoothIdeal S => ∑ D ∈ S.powerset,
      ‖reflectedTerm η ηi S hS (paperRadialFourier W) X Q D H‖) := by
  dsimp only
  exact summable_sum (fun D hD =>
    ((primitive_deleted_reflection c χ hu hp hχ S hS W X hX).1 D hD).norm)

end CenteredMomentReflectionDeletion

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace CenteredMomentNaturalReflection
open HeckeFamily CenteredMomentReflectionDeletion CenteredMomentNaturalPrimitive
open SchwartzPlanePoisson
local notation "O" => Eisenstein.O
local instance : IsPrincipalIdealRing O := IsCyclotomicExtension.Rat.three_pid K

lemma polynomial_coeff_congr (χ ψ : Character)
    (h : ∀I,idealCoeff χ I=idealCoeff ψ I) (W : ℝ→ℂ) (X : ℝ) :
    HeckeDyadic.polynomial χ false W X 0 0=HeckeDyadic.polynomial ψ false W X 0 0 := by
  unfold HeckeDyadic.polynomial
  congr 1
  apply tsum_congr
  intro I
  unfold HeckeDyadic.summand HeckeDyadic.coefficient
  rw [h]

lemma inverse_deletion_coeff (χ ψ : Character) (S : Finset (Ideal O))
    (hS : ∀P∈S,Prime P) (h : ∀I,idealCoeff χ I=idealCoeff (ψ.excludePrimes S hS) I)
    (I : Ideal O) : idealCoeff χ.inverse I=idealCoeff (ψ.inverse.excludePrimes S hS) I := by
  rw [idealCoeff_inverse_conj,h,idealCoeff_excludePrimes,idealCoeff_excludePrimes,
    idealCoeff_inverse_conj]
  split_ifs <;> simp

theorem primitive_character_deleted (ψ : Character)
    (hp : FiniteFourier.IsPrimitiveOnIdeals ψ.residue) (hn : ψ.residue≠1) :
    ∃G : ℂ,‖G‖=1 ∧ ∀(S : Finset (Ideal O))(hS : ∀P∈S,Prime P)
      (W : 𝓢(ℝ,ℂ))(X : ℝ),0< X →
      (∀D∈S.powerset,Summable (reflectedTerm ψ ψ.inverse S hS (paperRadialFourier W)
        X (ψ.modulus.absNorm:ℝ) D)) ∧
      HeckeDyadic.polynomial (ψ.excludePrimes S hS) false W X 0 0=
        G*∑D∈S.powerset,∑'H : SmoothIdeal S,
          reflectedTerm ψ ψ.inverse S hS (paperRadialFourier W) X (ψ.modulus.absNorm:ℝ) D H := by
  rcases ψ with ⟨M,hM,χ,hu,p,hp0,hpm⟩
  obtain ⟨c,hc⟩ := Submodule.IsPrincipal.principal M
  change M=Ideal.span {c} at hc
  subst M
  have hc0 : c≠0 := by simpa only [ne_eq,Ideal.span_singleton_eq_bot] using hM
  let : NeZero c := ⟨hc0⟩
  refine ⟨TraceCharacter.normalizedGauss c χ,TraceCharacter.normalizedGauss_norm c χ hp,?_⟩
  intro S hS W X hX
  have hh := primitive_deleted_reflection c χ hu hp hn S hS W X hX
  rw [ringComplex_norm_sq_eq_absNorm_span] at hh
  exact hh

theorem original_natural_reflection (χ : Character) (hn : χ.residue≠1) :
    ∃(ψ : Character)(G : ℂ),FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧ ψ.residue≠1 ∧ ‖G‖=1 ∧
      let S := redundantSet χ.modulus ψ.modulus
      let hS := redundantSet_prime χ.modulus ψ.modulus
      ψ.modulus.absNorm*(redundantIdeal χ.modulus ψ.modulus).absNorm≤χ.modulus.absNorm ∧
      IsCoprime (redundantIdeal χ.modulus ψ.modulus) ψ.modulus ∧
      (∀I,idealCoeff χ I=idealCoeff (ψ.excludePrimes S hS) I) ∧
      ∀(W : 𝓢(ℝ,ℂ))(X : ℝ),0< X →
        (∀D∈S.powerset,Summable (reflectedTerm ψ ψ.inverse S hS (paperRadialFourier W)
          X (ψ.modulus.absNorm:ℝ) D)) ∧
        HeckeDyadic.polynomial χ false W X 0 0=
          G*∑D∈S.powerset,∑'H : SmoothIdeal S,
            reflectedTerm ψ ψ.inverse S hS (paperRadialFourier W) X (ψ.modulus.absNorm:ℝ) D H := by
  obtain ⟨ψ,hmod,hprim,hne,hsq,hcop,hdvd,hnorm,hcoeff⟩ := exists_natural_primitive χ
  obtain ⟨G,hG,hreflection⟩ := primitive_character_deleted ψ hprim (hne hn)
  refine ⟨ψ,G,hprim,hne hn,hG,hnorm,hcop,hcoeff,?_⟩
  intro W X hX
  have hh := hreflection _ (redundantSet_prime χ.modulus ψ.modulus) W X hX
  exact ⟨hh.1,(polynomial_coeff_congr χ _ hcoeff W X).trans hh.2⟩

theorem original_inverse_reflection (χ : Character) (hn : χ.residue≠1) :
    ∃(ψ : Character)(G : ℂ),FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧ ψ.residue≠1 ∧ ‖G‖=1 ∧
      let S := redundantSet χ.modulus ψ.modulus
      ψ.modulus.absNorm*(redundantIdeal χ.modulus ψ.modulus).absNorm≤χ.modulus.absNorm ∧
      ∀(W : 𝓢(ℝ,ℂ))(X : ℝ),0< X →
        HeckeDyadic.polynomial χ false W X 0 0=
          G*∑D∈S.powerset,∑'H : SmoothIdeal S,
            (UniqueFactorizationMonoid.moebius (∏P∈D,P):ℂ)*idealCoeff ψ (∏P∈D,P)*
              idealCoeff ψ.inverse H.val.val /
              (Real.sqrt ((Ideal.absNorm (∏P∈D,P):ℝ)*norm H.val):ℂ)*
              HeckeDyadic.polynomial χ.inverse false (paperRadialFourier W)
                ((ψ.modulus.absNorm:ℝ)*(Ideal.absNorm (∏P∈D,P):ℝ)/(X*norm H.val)) 0 0 := by
  obtain ⟨ψ,G,hprim,hne,hG,hnorm,hcop,hcoeff,hreflect⟩ := original_natural_reflection χ hn
  refine ⟨ψ,G,hprim,hne,hG,hnorm,?_⟩
  intro W X hX
  rw [(hreflect W X hX).2]
  congr 1
  apply Finset.sum_congr rfl
  intro D hD
  apply tsum_congr
  intro H
  unfold reflectedTerm
  rw [←polynomial_coeff_congr χ.inverse _
    (inverse_deletion_coeff χ ψ _ (redundantSet_prime χ.modulus ψ.modulus) hcoeff)]

end CenteredMomentNaturalReflection

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace CenteredMomentTwistedReflection
open HeckeFamily CenteredMomentNaturalPrimitive CenteredMomentNaturalReflection
open CenteredMomentReflectionDeletion SchwartzPlanePoisson
local notation "O" => Eisenstein.O

lemma polynomial_twisted_source (χ : Character) (W : ℝ→ℂ) (X t : ℝ) (hX : 0< X) :
    HeckeDyadic.polynomial χ false W X 0 (2*Real.pi*t)=
      HeckeDyadic.polynomial χ false (CompletedHeight.normTwistedSource W t) X 0 0 := by
  unfold HeckeDyadic.polynomial
  congr 1
  apply tsum_congr
  intro I
  have hm := HeckeDetectorDyadicBridge.norm_phase (I.val.absNorm:ℝ) X (HeckeDyadic.norm_pos I) hX 0 t
  simp only [neg_zero,Complex.cpow_zero,one_mul,Complex.zero_re,Complex.zero_im,sub_zero] at hm
  unfold HeckeDyadic.summand HeckeDyadic.coefficient
  simp only [Bool.false_eq_true,ite_false,HeckeDyadic.shift,Complex.ofReal_zero,zero_mul,sub_zero,
    neg_zero,Complex.cpow_zero,mul_one,CompletedHeight.normTwistedSource]
  simp only [HeckeDyadic.norm,HeckeDyadic.shift] at hm ⊢
  rw [hm]
  simp only [Complex.ofReal_zero]
  ring

theorem actual_original_twisted_reflection (χ : Character) (hn : χ.residue≠1) :
    ∃(ψ : Character)(G : ℂ),FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧ ψ.residue≠1 ∧ ‖G‖=1 ∧
      let S := redundantSet χ.modulus ψ.modulus
      ψ.modulus.absNorm*(redundantIdeal χ.modulus ψ.modulus).absNorm≤χ.modulus.absNorm ∧
      ∀(W : ℝ→ℂ)(a b : ℝ)(_ha : 0< a)(_hs : Function.support W⊆Set.Icc a b)
        (_hW : ContDiff ℝ ∞ W)(omega X : ℝ),0< X →
        HeckeDyadic.polynomial χ false W X 0 omega=
          G*∑D∈S.powerset,∑'H : SmoothIdeal S,
            (UniqueFactorizationMonoid.moebius (∏P∈D,P):ℂ)*idealCoeff ψ (∏P∈D,P)*
              idealCoeff ψ.inverse H.val.val /
              (Real.sqrt ((Ideal.absNorm (∏P∈D,P):ℝ)*norm H.val):ℂ)*
              HeckeDyadic.polynomial χ.inverse false
                (paperRadialFourier (CompletedHeight.normTwistedSource W (omega/(2*Real.pi))))
                ((ψ.modulus.absNorm:ℝ)*(Ideal.absNorm (∏P∈D,P):ℝ)/(X*norm H.val)) 0 0 := by
  obtain ⟨ψ,G,hp,hnp,hG,hcap,hreflect⟩ := original_inverse_reflection χ hn
  refine ⟨ψ,G,hp,hnp,hG,hcap,?_⟩
  intro W a b ha hs hW omega X hX
  have he : (CompletedHeight.uniformTwistedSchwartz W a b ha hs hW (omega/(2*Real.pi)) : ℝ→ℂ)=
      CompletedHeight.normTwistedSource W (omega/(2*Real.pi)) := by
    funext x
    exact CompletedHeight.uniformTwistedSchwartz_apply W a b ha hs hW _ x
  have hh := hreflect (CompletedHeight.uniformTwistedSchwartz W a b ha hs hW (omega/(2*Real.pi))) X hX
  rw [he] at hh
  have ht : 2*Real.pi*(omega/(2*Real.pi))=omega := by field_simp
  rw [←ht,polynomial_twisted_source χ W X (omega/(2*Real.pi)) hX]
  simpa only [ht] using hh

end CenteredMomentTwistedReflection

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
namespace CenteredMomentDescentLedger
theorem declared_width_drop (M J g g₂ t₂ σ m' q' δ : ℝ)
    (hwidth : m'+q'=M+J-g-g₂+t₂) (hg : J+σ ≤ g) (hcommon : t₂ ≤ g₂)
    (hnonempty : 0 ≤ m'+δ) :
    max 0 (m'+δ)+q' ≤ M-σ+δ := by
  rw [max_eq_right hnonempty]
  linarith


end CenteredMomentDescentLedger

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace CenteredMomentSectorLocalization
open CubicEisenstein  SchwartzPlanePoisson CenteredMomentCommonSupport CenteredMomentCorrelation CenteredMomentFourier
local notation "O" => Eisenstein.O

def normValue (h : O) : ℝ := Ideal.absNorm (Ideal.span {h})

theorem normValue_eq_embedding (h : O) : normValue h=‖ringComplex h‖^2 :=
  (ringComplex_norm_sq_eq_absNorm_span h).symm

theorem normValue_mul (v h : O) : normValue (v*h)=normValue v*normValue h := by
  simp only [normValue,← Ideal.span_singleton_mul_span_singleton,map_mul,Nat.cast_mul]

theorem normValue_pos (h : O) (hh : h ≠ 0) : 0 < normValue h := by
  unfold normValue
  exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
    (Ideal.span_singleton_eq_bot.not.mpr hh))

theorem normValue_ge_one (h : O) (hh : h ≠ 0) : 1 ≤ normValue h := by
  unfold normValue
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
    (Ideal.span_singleton_eq_bot.not.mpr hh))

theorem retained_pullback (R : ℝ) (v h : O) :
    retainedWeight R (normValue (v*h))=retainedWeight R (normValue v*normValue h) := by
  rw [normValue_mul]

theorem retained_norm_enclosure (R : ℝ) (v h : O) (hv : v ≠ 0)
    (hne : retainedWeight R (normValue (v*h)) ≠ 0) : normValue h ≤ 4*R/normValue v := by
  have hb := (retainedWeight_enclosure R _ hne).2
  rw [normValue_mul] at hb
  apply (le_div_iff₀ (normValue_pos v hv)).mpr
  nlinarith

def frequencyRadius (Tsec Z ξ : ℝ) : ℝ := Tsec*Z^(ξ/2)

def frequencyLoss (Z Csec ξ : ℝ) : ℝ := ξ/2+Real.logb Z (4*Csec)

theorem frequencyLoss_nonneg (Z Csec ξ : ℝ) (hZ : 1 < Z) (hC : 1 ≤ Csec) (hξ : 0 ≤ ξ) :
    0 ≤ frequencyLoss Z Csec ξ := by
  have hlog := Real.logb_nonneg hZ (show 1 ≤ 4*Csec by linarith)
  unfold frequencyLoss
  linarith

theorem source_enclosure_power (Z Csec L ξ Nv : ℝ) (hZ : 1 < Z) (hC : 0 < Csec) (hNv : 0 < Nv) :
    4*(Csec*Z^L)*Z^(ξ/2)/Nv=Z^(L-Real.logb Z Nv+frequencyLoss Z Csec ξ) := by
  have hz : 0 < Z := zero_lt_one.trans hZ
  rw [frequencyLoss,show L-Real.logb Z Nv+(ξ/2+Real.logb Z (4*Csec))=
    (L+ξ/2)+Real.logb Z (4*Csec)-Real.logb Z Nv by ring,
    Real.rpow_sub hz,Real.rpow_add hz,Real.rpow_add hz,
    Real.rpow_logb hz (ne_of_gt hZ),Real.rpow_logb hz (ne_of_gt hZ)]
  · ring
  · exact hNv
  · positivity

theorem actual_retained_row_enclosure (Tsec Z Csec L ξ : ℝ)
    (hZ : 1 < Z) (hC : 0 < Csec) (hT : Tsec ≤ Csec*Z^L)
    (v h : O) (hv : v ≠ 0)
    (hne : retainedWeight (frequencyRadius Tsec Z ξ) (normValue (v*h)) ≠ 0) :
    normValue h ≤ Z^(L-Real.logb Z (normValue v)+frequencyLoss Z Csec ξ) := by
  have hb := retained_norm_enclosure (frequencyRadius Tsec Z ξ) v h hv hne
  apply hb.trans
  rw [← source_enclosure_power Z Csec L ξ (normValue v) hZ hC (normValue_pos v hv)]
  apply div_le_div_of_nonneg_right _ (normValue_pos v hv).le
  dsimp only [frequencyRadius]
  nlinarith [mul_le_mul_of_nonneg_right hT (Real.rpow_nonneg (zero_lt_one.trans hZ).le (ξ/2))]

theorem actual_nonempty_width (Tsec Z Csec L ξ : ℝ)
    (hZ : 1 < Z) (hC : 0 < Csec) (hT : Tsec ≤ Csec*Z^L)
    (v h : O) (hv : v ≠ 0) (hh : h ≠ 0)
    (hne : retainedWeight (frequencyRadius Tsec Z ξ) (normValue (v*h)) ≠ 0) :
    0 ≤ L-Real.logb Z (normValue v)+frequencyLoss Z Csec ξ := by
  have he := (normValue_ge_one h hh).trans (actual_retained_row_enclosure Tsec Z Csec L ξ hZ hC hT v h hv hne)
  by_contra hn
  have hh := Real.rpow_lt_one_of_one_lt_of_neg hZ (lt_of_not_ge hn)
  linarith

theorem actual_declared_width_drop (Tsec Z Csec L ξ M J g g₂ t₂ σ q' : ℝ)
    (hZ : 1 < Z) (hC : 0 < Csec) (hT : Tsec ≤ Csec*Z^L)
    (v h : O) (hv : v ≠ 0) (hh : h ≠ 0)
    (hne : retainedWeight (frequencyRadius Tsec Z ξ) (normValue (v*h)) ≠ 0)
    (hwidth : (L-Real.logb Z (normValue v))+q'=M+J-g-g₂+t₂)
    (hg : J+σ ≤ g) (hcommon : t₂ ≤ g₂) :
    max 0 (L-Real.logb Z (normValue v)+frequencyLoss Z Csec ξ)+q' ≤
      M-σ+frequencyLoss Z Csec ξ :=
  CenteredMomentDescentLedger.declared_width_drop M J g g₂ t₂ σ _ q' _ hwidth hg hcommon
    (actual_nonempty_width Tsec Z Csec L ξ hZ hC hT v h hv hh hne)

theorem retained_first_dyad_enclosure (Tsec Z Csec L ξ : ℝ)
    (hZ : 1 < Z) (hC : 0 < Csec) (hT : Tsec ≤ Csec*Z^L)
    (n : ℤ) (hn : Retained (frequencyRadius Tsec Z ξ) n) :
    Real.logb Z (dyadicScale n) ≤ L+frequencyLoss Z Csec ξ := by
  have hb := retained_scale_le _ n hn
  have hp := source_enclosure_power Z Csec L ξ 1 hZ hC (by norm_num)
  simp only [Real.logb_one,sub_zero,div_one] at hp
  have he : dyadicScale n ≤ Z^(L+frequencyLoss Z Csec ξ) := by
    rw [← hp]
    dsimp only [frequencyRadius] at hb
    nlinarith [mul_le_mul_of_nonneg_right hT (Real.rpow_nonneg (zero_lt_one.trans hZ).le (ξ/2))]
  have hl := Real.logb_le_logb_of_le hZ (dyadicScale_pos n) he
  rwa [Real.logb_rpow (zero_lt_one.trans hZ) (ne_of_gt hZ)] at hl

def kernelReference (Tsec H : ℝ) : ℝ := Real.exp (-2*H)/Tsec

theorem kernelReference_pos (Tsec H : ℝ) (hT : 0 < Tsec) : 0 < kernelReference Tsec H :=
  div_pos (Real.exp_pos _) hT

theorem frequencyLoss_lt (Z Csec H ξ : ℝ) (hZ : 1 < Z) (hH : 0 ≤ H) (hξ : 0 < ξ)
    (hthreshold : 2*H/Real.log Z+Real.log (4*Csec)/Real.log Z < ξ/4) :
    frequencyLoss Z Csec ξ < ξ := by
  have h := div_nonneg (show 0 ≤ 2*H by linarith) (Real.log_pos hZ).le
  unfold frequencyLoss Real.logb
  linarith

theorem discarded_kernel_argument (Tsec Z Csec H ξ q : ℝ)
    (hT : 0 < Tsec) (hZ : 1 < Z) (hC : 1 ≤ Csec)
    (hthreshold : 2*H/Real.log Z+Real.log (4*Csec)/Real.log Z < ξ/4)
    (hne : discardedWeight (frequencyRadius Tsec Z ξ) q ≠ 0) :
    Z^(ξ/4) ≤ kernelReference Tsec H*q := by
  have hlog := Real.log_nonneg (show 1 ≤ 4*Csec by linarith)
  have hlogdiv := div_nonneg hlog (Real.log_pos hZ).le
  have he : 2*H < ξ/4*Real.log Z :=
    (div_lt_iff₀ (Real.log_pos hZ)).mp (by linarith : 2*H/Real.log Z < ξ/4)
  have hs : Z^(ξ/4) ≤ Real.exp (-2*H)*Z^(ξ/2) := by
    rw [Real.rpow_def_of_pos (zero_lt_one.trans hZ),Real.rpow_def_of_pos (zero_lt_one.trans hZ),← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith
  have hq := (discardedWeight_support _ q hne).le
  have hm := mul_le_mul_of_nonneg_left hq (kernelReference_pos Tsec H hT).le
  have hid : kernelReference Tsec H*frequencyRadius Tsec Z ξ=Real.exp (-2*H)*Z^(ξ/2) := by
    unfold kernelReference frequencyRadius
    field_simp
  rw [hid] at hm
  exact hs.trans hm

theorem retained_pullback_zero_extension (Tsec Z Csec L ξ : ℝ)
    (hZ : 1 < Z) (hC : 0 < Csec) (hT : Tsec ≤ Csec*Z^L)
    (v h : O) (hv : v ≠ 0) :
    retainedWeight (frequencyRadius Tsec Z ξ) (normValue (v*h)) =
      if normValue h ≤ Z^(L-Real.logb Z (normValue v)+frequencyLoss Z Csec ξ)
      then retainedWeight (frequencyRadius Tsec Z ξ) (normValue (v*h)) else 0 := by
  split_ifs with hb
  · rfl
  · by_contra hn
    exact hb (actual_retained_row_enclosure Tsec Z Csec L ξ hZ hC hT v h hv hn)

theorem actual_discarded_lattice_tail (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(ℝ,ℂ)) (Tsec Z Csec H ξ K B : ℝ),
      0 < Tsec → 1 < Z → 1 ≤ Csec →
      (2*H/Real.log Z+Real.log (4*Csec)/Real.log Z < ξ/4) →
      kernelReference Tsec H ≤ K → 0 ≤ B →
      ∀ c : O → ℂ, (∀ h, ‖c h‖ ≤ B) →
      ‖∑' h : O,(discardedWeight (frequencyRadius Tsec Z ξ) (normValue h):ℂ)*c h*
        paperRadialFourier W (K*normValue h)‖ ≤
      B*(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
        ((min 1 (kernelReference Tsec H))^2*(1+Z^(ξ/4))^A) := by
  obtain ⟨s,C,hC,ht⟩ := CenteredMomentTail.uniform_sector_lattice_tail A
  refine ⟨s,C,hC,?_⟩
  intro W Tsec Z Csec H ξ K B hT hZ hCsec hthreshold hK hB c hc
  let D : Set O := {h | discardedWeight (frequencyRadius Tsec Z ξ) (normValue h) ≠ 0}
  have hb := ht W D (kernelReference Tsec H) (Z^(ξ/4)) B
    (kernelReference_pos Tsec H hT) (Real.rpow_nonneg (zero_lt_one.trans hZ).le _) hB
    (fun h hh => by
      rw [← normValue_eq_embedding]
      exact discarded_kernel_argument Tsec Z Csec H ξ (normValue h) hT hZ hCsec hthreshold hh)
    K hK c (fun h => (discardedWeight (frequencyRadius Tsec Z ξ) (normValue h):ℂ))
    (fun h _ => hc h) (fun h _ => by
      rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (discardedWeight_nonneg _ _)]
      exact (discardedWeight_bounds _ _).2)
  simp_rw [← normValue_eq_embedding] at hb
  have he := tsum_subtype_eq_of_support_subset (f := fun h : O =>
    (discardedWeight (frequencyRadius Tsec Z ξ) (normValue h):ℂ)*c h*paperRadialFourier W (K*normValue h))
    (s := D) (by
      intro h hh
      change discardedWeight (frequencyRadius Tsec Z ξ) (normValue h) ≠ 0
      intro hz
      exact hh (by simp [hz]))
  rwa [he] at hb

theorem actual_discarded_second_tail (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(ℝ,ℂ)) (Tsec Z Csec H ξ K : ℝ),
      0 < Tsec → 1 < Z → 1 ≤ Csec →
      (2*H/Real.log Z+Real.log (4*Csec)/Real.log Z < ξ/4) →
      kernelReference Tsec H ≤ K →
      ∀ (u v : O) (hu : CanonicalQuadraticSieve.Supported (Ideal.span {u}))
        (hv : CanonicalQuadraticSieve.Supported (Ideal.span {v})),
      ‖∑' h : O,(discardedWeight (frequencyRadius Tsec Z ξ) (normValue h):ℂ)*
        CenteredMomentSupportedCorrelation.actualCorrelation u v hu hv (-h)*
        paperRadialFourier W (K*normValue h)‖ ≤
      (normValue u*normValue v)*(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
        ((min 1 (kernelReference Tsec H))^2*(1+Z^(ξ/4))^A) := by
  obtain ⟨s,C,hC,ht⟩ := actual_discarded_lattice_tail A
  refine ⟨s,C,hC,?_⟩
  intro W Tsec Z Csec H ξ K hT hZ hCsec hthreshold hK u v hu hv
  exact ht W Tsec Z Csec H ξ K (normValue u*normValue v) hT hZ hCsec hthreshold hK
    (by unfold normValue; positivity) _ (fun h => CenteredMomentTail.actualCorrelation_norm_le u v hu hv (-h))

theorem retained_product_ne_zero (R : ℝ) (v h : O)
    (hne : retainedWeight R (normValue (v*h)) ≠ 0) : v ≠ 0 ∧ h ≠ 0 := by
  have hp := (retainedWeight_enclosure R _ hne).1
  constructor <;> intro hz <;> simp [hz,normValue] at hp

theorem actual_nonempty_width_of_weight (Tsec Z Csec L ξ : ℝ)
    (hZ : 1 < Z) (hC : 0 < Csec) (hT : Tsec ≤ Csec*Z^L) (v h : O)
    (hne : retainedWeight (frequencyRadius Tsec Z ξ) (normValue (v*h)) ≠ 0) :
    0 ≤ L-Real.logb Z (normValue v)+frequencyLoss Z Csec ξ := by
  obtain ⟨hv,hh⟩ := retained_product_ne_zero _ v h hne
  exact actual_nonempty_width Tsec Z Csec L ξ hZ hC hT v h hv hh hne

theorem actual_second_pullback (R : ℝ) (Gc V h : O) :
    retainedWeight R (normValue ((Gc*V)*h))=
      retainedWeight R ((normValue Gc*normValue V)*normValue h) := by
  simp only [normValue_mul]

theorem retained_integral_empty (R : ℝ) (hR : 4*R < 1) (h : O) :
    retainedWeight R (normValue h)=0 := by
  by_contra hn
  have hh : h ≠ 0 := by
    intro hz
    subst h
    exact hn (by simpa [normValue] using retainedWeight_zero_nonpos R 0 le_rfl)
  have hb := (retainedWeight_enclosure R _ hn).2
  linarith [normValue_ge_one h hh]

theorem finite_retained_above (R a : ℝ) (ha : 0 < a) :
    {n : ℤ | Retained R n ∧ ∃ q : ℝ, a ≤ q ∧ dyadicWeight n q ≠ 0}.Finite := by
  obtain ⟨k,hk,_⟩ := exists_mem_Ico_zpow ha (by norm_num : (1:ℝ) < 2)
  obtain ⟨l,hl⟩ := pow_unbounded_of_one_lt (4*R) (by norm_num : (1:ℝ) < 2)
  apply (Set.finite_Icc k (l:ℤ)).subset
  intro n hn
  obtain ⟨hr,q,hq,hne⟩ := hn
  have hu := retained_scale_le R n hr
  have hs := (dyadicWeight_support n hne).2
  constructor
  · have h : (2:ℝ)^k < (2:ℝ)^n := hk.trans_lt (hq.trans_lt hs)
    exact ((zpow_lt_zpow_iff_right₀ (by norm_num : (1:ℝ) < 2)).mp h).le
  · have h : (2:ℝ)^n < (2:ℝ)^(l:ℤ) := by
      simpa only [zpow_natCast,dyadicScale] using hu.trans_lt hl
    exact ((zpow_lt_zpow_iff_right₀ (by norm_num : (1:ℝ) < 2)).mp h).le

theorem retainedWeight_finite_formula (R a : ℝ) (ha : 0 < a) :
    ∃ S : Finset ℤ, ∀ q : ℝ, a ≤ q →
      retainedWeight R q=∑ n ∈ S, if Retained R n then dyadicWeight n q else 0 := by
  let hs := finite_retained_above R a ha
  refine ⟨hs.toFinset,fun q hq => ?_⟩
  apply tsum_eq_sum
  intro n hn
  split_ifs with hr
  · by_contra hne
    exact hn (hs.mem_toFinset.mpr ⟨hr,q,hq,hne⟩)
  · rfl

theorem retainedWeight_smooth_positive (R q : ℝ) (hq : 0 < q) :
    ContDiffAt ℝ ∞ (retainedWeight R) q := by
  obtain ⟨S,hS⟩ := retainedWeight_finite_formula R (q/2) (by linarith)
  have hc : ContDiff ℝ ∞ (fun x : ℝ => ∑ n ∈ S, if Retained R n then dyadicWeight n x else 0) := by
    apply ContDiff.sum
    intro n hn
    by_cases hr : Retained R n
    · simpa [hr] using dyadicWeight_smooth n
    · simpa [hr] using (contDiff_const : ContDiff ℝ ∞ (fun _x : ℝ => (0:ℝ)))
  apply hc.contDiffAt.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds (show q/2 < q by linarith)] with x hx
  exact hS x hx.le

theorem discardedWeight_smooth_positive (R q : ℝ) (hq : 0 < q) :
    ContDiffAt ℝ ∞ (discardedWeight R) q := by
  have hc : ContDiffAt ℝ ∞ (fun x => (1:ℝ)-retainedWeight R x) q :=
    contDiffAt_const.sub (retainedWeight_smooth_positive R q hq)
  apply hc.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hq] with x hx
  have he := retained_add_discarded R x hx
  linarith

end CenteredMomentSectorLocalization

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace CenteredMomentReflectedAnnuli
open Set SchwartzPlanePoisson CenteredMomentSectorLocalization
open CenteredMomentComparisonReflection LocalLogFourier

def logWindow (v : ℝ) : ℂ := (annulus (Real.exp v) : ℂ)

theorem logWindow_smooth : ContDiff ℝ ∞ logWindow :=
  Complex.ofRealCLM.contDiff.comp (annulus_smooth.comp Real.contDiff_exp)

theorem logWindow_support : Function.support logWindow ⊆ Icc (-Real.log 4) 0 := by
  intro v hv
  have hn : annulus (Real.exp v) ≠ 0 := by simpa [logWindow] using hv
  have hlow : 1/4 < Real.exp v := lt_of_not_ge (fun h => hn (annulus_zero_low _ h))
  have hhigh : Real.exp v < 1 := lt_of_not_ge (fun h => hn (annulus_zero_high _ h))
  have hl : Real.exp (-Real.log 4) = (1/4 : ℝ) := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0:ℝ)<4)]
    norm_num
  constructor
  · exact (Real.exp_lt_exp.mp (hl ▸ hlow)).le
  · exact (Real.exp_lt_one_iff.mp hhigh).le

theorem logWindow_tsupport : tsupport logWindow ⊆ Icc (-Real.log 4) 0 :=
  closure_minimal logWindow_support isClosed_Icc

theorem logWindow_compact : HasCompactSupport logWindow :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc logWindow_support

def logWindowSchwartz : 𝓢(ℝ,ℂ) := logWindow_compact.toSchwartzMap logWindow_smooth

theorem logWindow_derivative_window (i : ℕ) (v : ℝ)
    (hi : ‖iteratedFDeriv ℝ i logWindow v‖ ≠ 0) :
    1/4 ≤ Real.exp v ∧ |v| ≤ Real.log 4 := by
  have hv := logWindow_tsupport (support_iteratedFDeriv_subset i (norm_ne_zero_iff.mp hi))
  have hl : Real.exp (-Real.log 4) = (1/4 : ℝ) := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0:ℝ)<4)]
    norm_num
  refine ⟨hl ▸ Real.exp_le_exp.mpr hv.1, abs_le.mpr ⟨hv.1,?_⟩⟩
  exact hv.2.trans (Real.log_nonneg (by norm_num))

theorem logWindow_derivative_bound (K : ℕ) :
    ∃ C : ℝ, 0< C ∧ ∀ i≤ K, ∀v : ℝ, ‖iteratedFDeriv ℝ i logWindow v‖≤ C := by
  let C := 1+∑ i∈Finset.range (K+1), SchwartzMap.seminorm ℝ 0 i logWindowSchwartz
  have hsum := Finset.sum_nonneg (s:=Finset.range (K+1))
    (fun i _ => apply_nonneg (SchwartzMap.seminorm ℝ 0 i) logWindowSchwartz)
  refine ⟨C,by dsimp [C];linarith,?_⟩
  intro i hi v
  have hb := SchwartzMap.le_seminorm' ℝ 0 i logWindowSchwartz v
  have hc := Finset.single_le_sum (s:=Finset.range (K+1))
    (f:=fun j=> SchwartzMap.seminorm ℝ 0 j logWindowSchwartz)
    (fun j _ => apply_nonneg (SchwartzMap.seminorm ℝ 0 j) logWindowSchwartz)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  change ‖iteratedDeriv i logWindowSchwartz v‖≤ C
  simpa only [pow_zero, one_mul] using hb.trans (by dsimp [C];linarith)

def reflected (W : ℝ→ℂ) (t : ℝ) : ℝ→ℂ :=
  paperRadialFourier (CompletedHeight.normTwistedSource W t)

theorem reflected_smooth (W : ℝ→ℂ) (a b : ℝ) (ha : 0< a)
    (hs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W) (t : ℝ) :
    ContDiffOn ℝ ∞ (reflected W t) (Ioi 0) := by
  have he : (CompletedHeight.uniformTwistedSchwartz W a b ha hs hW t : ℝ→ℂ)=
      CompletedHeight.normTwistedSource W t := by
    funext x
    exact CompletedHeight.uniformTwistedSchwartz_apply W a b ha hs hW t x
  unfold reflected
  rw [←he]
  exact paperRadialFourier_contDiffOn _

def annularProfile (F : ℝ→ℂ) (s x : ℝ) : ℂ := (annulus x:ℂ)*F (s*x)

def logProfile (W : ℝ→ℂ) (a b : ℝ) (ha : 0< a)
    (hs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W)
    (s : ℝ) (hs0 : 0< s) (t : ℝ) : 𝓢(ℝ,ℂ) :=
  positiveLogProfile logWindow (reflected W t) s logWindow_compact logWindow_smooth
    (reflected_smooth W a b ha hs hW t) hs0

@[simp] theorem logProfile_apply (W : ℝ→ℂ) (a b : ℝ) (ha : 0< a)
    (hs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W)
    (s : ℝ) (hs0 : 0< s) (t v : ℝ) :
    logProfile W a b ha hs hW s hs0 t v =
      annularProfile (reflected W t) s (Real.exp v) := rfl

theorem logProfile_tsupport (W : ℝ→ℂ) (a b : ℝ) (ha : 0< a)
    (hs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W)
    (s : ℝ) (hs0 : 0< s) (t : ℝ) :
    tsupport (logProfile W a b ha hs hW s hs0 t) ⊆ Icc (-Real.log 4) 0 := by
  apply closure_minimal _ isClosed_Icc
  intro v hv
  apply logWindow_support
  intro hz
  exact hv (by change logWindow v*reflected W t (s*Real.exp v)=0;rw [hz,zero_mul])

theorem logProfile_finite_seminorm (a b : ℝ) (ha : 0< a)
    (H : Finset (ℕ×ℕ)) (B : ℕ) :
    ∃ J : ℕ, ∀ W : ℝ→ℂ, ∀ hs : Function.support W⊆Icc a b,
      ∀hW : ContDiff ℝ ∞ W, ∃C : ℝ, 0< C ∧ ∀s : ℝ, ∀hs0 : 0< s, ∀t : ℝ,
      H.sup (schwartzSeminormFamily ℝ ℝ ℂ) (logProfile W a b ha hs hW s hs0 t) ≤
        C*(1+‖t‖)^J/(1+s)^B := by
  let K := H.sup Prod.snd
  obtain ⟨CW,hCW,hwin⟩ := logWindow_derivative_bound K
  obtain ⟨J,hJ⟩ := reflected_profile_height_control a b ha B K
  let D := 1+∑z∈H,(Real.log 4)^z.1*
    (∑i∈Finset.range (z.2+1),(z.2.choose i:ℝ)*CW)
  have hlog : 0≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hD : 0< D := by
    have hn : 0≤∑z∈H,(Real.log 4)^z.1*
        (∑i∈Finset.range (z.2+1),(z.2.choose i:ℝ)*CW) := by positivity
    dsimp [D];linarith
  refine ⟨J,?_⟩
  intro W hs hW
  obtain ⟨CF,hCF,hEuler⟩ := hJ W hs hW
  refine ⟨D*CF/(1/4:ℝ)^B,by positivity,?_⟩
  intro s hs0 t
  apply Seminorm.finset_sup_apply_le (by positivity)
  intro z hz
  have hzK : z.2≤ K := Finset.le_sup hz
  have hb := positive_log_uniform_seminorm logWindow (reflected W t)
    s (1/4) (Real.log 4) CW (CF*(1+‖t‖)^J) B z.2 z.1
    logWindow_compact logWindow_smooth (reflected_smooth W a b ha hs hW t)
    hs0 (by norm_num) (by norm_num) hlog hCW.le (by positivity)
    (fun i hi v => hwin i (hi.trans hzK) v)
    (fun v hv => by obtain ⟨i,hi,hn⟩:=hv;exact logWindow_derivative_window i v hn)
    (fun i hi x hx => hEuler t i (hi.trans hzK) x hx.le)
  have hd : (Real.log 4)^z.1*(∑i∈Finset.range (z.2+1),(z.2.choose i:ℝ)*CW)≤ D := by
    have h := Finset.single_le_sum (s:=H)
      (f:=fun z=>(Real.log 4)^z.1*(∑i∈Finset.range (z.2+1),(z.2.choose i:ℝ)*CW))
      (fun z _ => by positivity) hz
    dsimp [D];linarith
  have hb' : (1/4:ℝ)^B*(1+s)^B*
      SchwartzMap.seminorm ℝ z.1 z.2 (logProfile W a b ha hs hW s hs0 t) ≤
      D*(CF*(1+‖t‖)^J) := by
    apply hb.trans
    rw [←Finset.sum_mul, ←mul_assoc]
    exact mul_le_mul_of_nonneg_right hd (by positivity)
  have hb'' : SchwartzMap.seminorm ℝ z.1 z.2
      (logProfile W a b ha hs hW s hs0 t) ≤
      D*(CF*(1+‖t‖)^J)/((1/4:ℝ)^B*(1+s)^B) :=
    (le_div_iff₀ (by positivity)).mpr
      (by simpa only [mul_comm, mul_left_comm, mul_assoc] using hb')
  exact hb''.trans_eq (by ring)

theorem annularProfile_support (F : ℝ→ℂ) (s : ℝ) :
    Function.support (annularProfile F s) ⊆ Icc (1/4) 1 := by
  intro x hx
  constructor
  · by_contra hn
    exact hx (by simp [annularProfile,annulus_zero_low x (le_of_not_ge hn)])
  · by_contra hn
    exact hx (by simp [annularProfile,annulus_zero_high x (le_of_not_ge hn)])

theorem annularProfile_zero (F : ℝ→ℂ) (s x : ℝ)
    (hx : x≤1/4 ∨ 1≤ x) : annularProfile F s x=0 := by
  rcases hx with hx|hx
  · simp [annularProfile,annulus_zero_low x hx]
  · simp [annularProfile,annulus_zero_high x hx]

theorem annular_partition (F : ℝ→ℂ) (x : ℝ) (hx : 0< x) :
    (∑' n : ℤ,annularProfile F (dyadicScale n) (x/dyadicScale n))=F x := by
  have he (n : ℤ) : annularProfile F (dyadicScale n) (x/dyadicScale n)=
      (dyadicWeight n x:ℂ)*F x := by
    simp [annularProfile,dyadicWeight,mul_div_cancel₀,ne_of_gt (dyadicScale_pos n)]
  simp_rw [he]
  rw [tsum_mul_right,←Complex.ofReal_tsum,dyadicWeight_partition x hx]
  simp

theorem normalized_annular_term (η : HeckeFamily.Character) (F : ℝ→ℂ)
    (s Y : ℝ) (hs : 0< s) (hY : 0< Y) :
    HeckeDyadic.polynomial η false (fun x=>(annulus (x/s):ℂ)*F x) Y 0 0=
      (Real.sqrt s:ℂ)*HeckeDyadic.polynomial η false (annularProfile F s) (s*Y) 0 0 := by
  rw [polynomial_plain _ _ _ hY,polynomial_plain _ _ _ (mul_pos hs hY)]
  have he (x : ℝ) : (annulus ((x/Y)/s):ℂ)*F (x/Y)=
      annularProfile F s (x/(s*Y)) := by
    unfold annularProfile
    congr 2 <;> field_simp
  simp_rw [he]
  rw [Real.sqrt_mul hs.le,Complex.ofReal_mul]
  have hs' : (Real.sqrt s:ℂ)≠0 := by exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 hs))
  field_simp

def annularMass (B : ℕ) (n : ℤ) : ℝ :=
  Real.sqrt (dyadicScale n)/(1+dyadicScale n)^B

theorem annularMass_nonneg (B : ℕ) (n : ℤ) : 0≤ annularMass B n := by
  have hp := dyadicScale_pos n
  unfold annularMass
  positivity

lemma sqrt_nat_pow (x : ℝ) (hx : 0≤ x) (j : ℕ) :
    Real.sqrt (x^j)=(Real.sqrt x)^j := by
  induction j with
  | zero => simp
  | succ j ih => rw [pow_succ,Real.sqrt_mul (pow_nonneg hx j),ih,pow_succ]

theorem annularMass_lower_bound (B j : ℕ) :
    annularMass B (-(j:ℤ))≤(Real.sqrt (1/2:ℝ))^j := by
  have hx := dyadicScale_pos (-(j:ℤ))
  have hd : 1≤(1+dyadicScale (-(j:ℤ)))^B := one_le_pow₀ (by linarith)
  have he : dyadicScale (-(j:ℤ))=(1/2:ℝ)^j := by
    simp [dyadicScale,zpow_neg,inv_pow]
  calc
    annularMass B (-(j:ℤ))≤ Real.sqrt (dyadicScale (-(j:ℤ))) :=
      div_le_self (Real.sqrt_nonneg _) hd
    _=(Real.sqrt (1/2:ℝ))^j := by rw [he,sqrt_nat_pow _ (by norm_num)]

theorem annularMass_upper_bound (B A j : ℕ) (hAB : A+1≤ B) :
    annularMass B (j:ℤ)≤((2:ℝ)^A)⁻¹^j := by
  have hx : 1≤ dyadicScale (j:ℤ) := by
    simp only [dyadicScale,zpow_natCast]
    exact one_le_pow₀ (by norm_num)
  have hp : 0< dyadicScale (j:ℤ) := dyadicScale_pos _
  have hd : dyadicScale (j:ℤ)^(A+1)≤(1+dyadicScale (j:ℤ))^B :=
    (pow_le_pow_left₀ hp.le (by linarith) _).trans
      (pow_le_pow_right₀ (by linarith) hAB)
  have hb : annularMass B (j:ℤ)≤ dyadicScale (j:ℤ)/dyadicScale (j:ℤ)^(A+1) := by
    unfold annularMass
    exact div_le_div₀ hp.le (Real.sqrt_le_self_iff.mpr (Or.inr hx))
      (by positivity) hd
  calc
    annularMass B (j:ℤ)≤ dyadicScale (j:ℤ)/dyadicScale (j:ℤ)^(A+1) := hb
    _=((2:ℝ)^A)⁻¹^j := by
      rw [pow_succ,mul_comm (dyadicScale (j:ℤ)^A),div_mul_cancel_left₀ (ne_of_gt hp)]
      simp only [dyadicScale,zpow_natCast,←pow_mul,inv_pow]
      rw [Nat.mul_comm]

lemma nonnegative_geometric_tail (f : ℕ→ℝ) (q : ℝ) (hq0 : 0≤ q) (hq1 : q<1)
    (hf : ∀j,0≤ f j) (hb : ∀j,f j≤ q^j) (L : ℕ) :
    Summable (fun j=> f (j+L)) ∧ (∑'j:ℕ,f (j+L))≤ q^L/(1-q) := by
  have hg : Summable (fun j:ℕ=> q^(j+L)) := by
    simpa only [pow_add] using (summable_geometric_of_lt_one hq0 hq1).mul_right (q^L)
  have hs := Summable.of_nonneg_of_le (fun j=> hf (j+L)) (fun j=> hb (j+L)) hg
  refine ⟨hs,(hs.tsum_le_tsum (fun j=> hb (j+L)) hg).trans_eq ?_⟩
  simp_rw [pow_add]
  rw [tsum_mul_right,tsum_geometric_of_lt_one hq0 hq1]
  ring

theorem annularMass_lower_tail (B L : ℕ) :
    Summable (fun j:ℕ=> annularMass B (-((j+L:ℕ):ℤ))) ∧
      (∑'j:ℕ,annularMass B (-((j+L:ℕ):ℤ)))≤
        (Real.sqrt (1/2:ℝ))^L/(1-Real.sqrt (1/2:ℝ)) := by
  apply nonnegative_geometric_tail (fun j=> annularMass B (-(j:ℤ)))
    (Real.sqrt (1/2:ℝ)) (Real.sqrt_nonneg _)
    (by simpa using (Real.sqrt_lt_sqrt (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)<1)))
    (fun j=> annularMass_nonneg _ _) (annularMass_lower_bound B) L

theorem annularMass_upper_tail (B A L : ℕ) (hA : 1≤ A) (hAB : A+1≤ B) :
    Summable (fun j:ℕ=> annularMass B ((j+L:ℕ):ℤ)) ∧
      (∑'j:ℕ,annularMass B ((j+L:ℕ):ℤ))≤
        (((2:ℝ)^A)⁻¹)^L/(1-((2:ℝ)^A)⁻¹) := by
  have hp : 1<(2:ℝ)^A := by
    calc
      1<(2:ℝ)^1 := by norm_num
      _≤(2:ℝ)^A := pow_le_pow_right₀ (by norm_num) hA
  apply nonnegative_geometric_tail (fun j=> annularMass B (j:ℤ))
    ((2:ℝ)^A)⁻¹ (by positivity) (inv_lt_one_of_one_lt₀ hp)
    (fun j=> annularMass_nonneg _ _) (fun j=> annularMass_upper_bound B A j hAB) L

theorem annularMass_summable (B : ℕ) (hB : 2≤ B) : Summable (annularMass B) := by
  apply Summable.of_nat_of_neg
  · simpa only [Nat.add_zero] using (annularMass_upper_tail B 1 0 (by omega) hB).1
  · simpa only [Nat.add_zero] using (annularMass_lower_tail B 0).1

theorem logProfile_dyadic_seminorm_sum (a b : ℝ) (ha : 0< a)
    (H : Finset (ℕ×ℕ)) (B : ℕ) (hB : 2≤ B) :
    ∃ J : ℕ, ∀ W : ℝ→ℂ, ∀ hs : Function.support W⊆Icc a b,
      ∀hW : ContDiff ℝ ∞ W, ∃C : ℝ, 0< C ∧ ∀t : ℝ,
      Summable (fun n:ℤ=> Real.sqrt (dyadicScale n)*
        H.sup (schwartzSeminormFamily ℝ ℝ ℂ)
          (logProfile W a b ha hs hW (dyadicScale n) (dyadicScale_pos n) t)) ∧
      (∑'n:ℤ,Real.sqrt (dyadicScale n)*
        H.sup (schwartzSeminormFamily ℝ ℝ ℂ)
          (logProfile W a b ha hs hW (dyadicScale n) (dyadicScale_pos n) t))≤
        C*(1+‖t‖)^J := by
  obtain ⟨J,hJ⟩ := logProfile_finite_seminorm a b ha H B
  refine ⟨J,?_⟩
  intro W hs hW
  obtain ⟨CF,hCF,hbound⟩ := hJ W hs hW
  have hmass := annularMass_summable B hB
  have hmass0 : 0≤∑'n:ℤ,annularMass B n := tsum_nonneg (annularMass_nonneg B)
  refine ⟨CF*(1+∑'n:ℤ,annularMass B n),by positivity,?_⟩
  intro t
  let f := fun n:ℤ=> Real.sqrt (dyadicScale n)*
    H.sup (schwartzSeminormFamily ℝ ℝ ℂ)
      (logProfile W a b ha hs hW (dyadicScale n) (dyadicScale_pos n) t)
  have hf0 : ∀n,0≤ f n := fun n=>
    mul_nonneg (Real.sqrt_nonneg _) (apply_nonneg _ _)
  have hb : ∀n,f n≤(CF*(1+‖t‖)^J)*annularMass B n := by
    intro n
    have h := mul_le_mul_of_nonneg_left (hbound _ (dyadicScale_pos n) t)
      (Real.sqrt_nonneg (dyadicScale n))
    exact h.trans_eq (by unfold annularMass;ring)
  have hg := hmass.mul_left (CF*(1+‖t‖)^J)
  have hf := Summable.of_nonneg_of_le hf0 hb hg
  refine ⟨hf,(hf.tsum_le_tsum hb hg).trans ?_⟩
  rw [tsum_mul_left]
  nlinarith [show 0≤ CF*(1+‖t‖)^J by positivity]

end CenteredMomentReflectedAnnuli

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace CenteredMomentReflectedSeries
open HeckeFamily CenteredMomentSectorLocalization CenteredMomentReflectedAnnuli
open CenteredMomentComparisonReflection CenteredMomentReflectionDeletion
open SchwartzPlanePoisson
local notation "NI" => CubicEisenstein.NonzeroIdeal

def dyadicIdealTerm (η : Character) (F : ℝ→ℂ) (Y : ℝ) (I : NI) (n : ℤ) : ℂ :=
  idealCoeff η I.val*(dyadicWeight n ((I.val.absNorm:ℝ)/Y):ℂ)*F ((I.val.absNorm:ℝ)/Y)

lemma dyadicIdealTerm_norm (η : Character) (F : ℝ→ℂ) (Y : ℝ) (I : NI) (n : ℤ) :
    ‖dyadicIdealTerm η F Y I n‖=
      dyadicWeight n ((I.val.absNorm:ℝ)/Y)*‖idealCoeff η I.val*F ((I.val.absNorm:ℝ)/Y)‖ := by
  unfold dyadicIdealTerm
  rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_of_nonneg (dyadicWeight_bounds _ _).1,norm_mul]
  ring

lemma dyadic_ideal_absolute (η : Character) (F : ℝ→ℂ) (hF : DecayTwo F)
    (Y : ℝ) (hY : 0< Y) :
    Summable (fun p : NI×ℤ=>‖dyadicIdealTerm η F Y p.1 p.2‖) := by
  apply (summable_prod_of_nonneg (fun _=> norm_nonneg _)).mpr
  simp_rw [dyadicIdealTerm_norm]
  constructor
  · intro I
    exact (dyadicWeight_summable _).mul_right _
  · simp_rw [tsum_mul_right]
    have he (I : NI) : (∑'n : ℤ,dyadicWeight n ((I.val.absNorm:ℝ)/Y))=1 :=
      dyadicWeight_partition _ (div_pos (HeckeDyadic.norm_pos I) hY)
    simp_rw [he,one_mul]
    exact (plain_summable η F hF Y hY).norm

lemma dyadic_ideal_partition (η : Character) (F : ℝ→ℂ) (Y : ℝ) (hY : 0< Y) (I : NI) :
    (∑'n : ℤ,dyadicIdealTerm η F Y I n)=idealCoeff η I.val*F ((I.val.absNorm:ℝ)/Y) := by
  have he (n : ℤ) : dyadicIdealTerm η F Y I n=
      (dyadicWeight n ((I.val.absNorm:ℝ)/Y):ℂ)*(idealCoeff η I.val*F ((I.val.absNorm:ℝ)/Y)) := by
    unfold dyadicIdealTerm
    ring
  simp_rw [he]
  have hp : 0<(I.val.absNorm:ℝ)/Y := div_pos (HeckeDyadic.norm_pos I) hY
  rw [tsum_mul_right,←Complex.ofReal_tsum,dyadicWeight_partition _ hp]
  simp

theorem normalized_annular_series (η : Character) (F : ℝ→ℂ) (hF : DecayTwo F)
    (Y : ℝ) (hY : 0< Y) :
    Summable (fun n : ℤ=>(Real.sqrt (dyadicScale n):ℂ)*
      HeckeDyadic.polynomial η false (annularProfile F (dyadicScale n)) (dyadicScale n*Y) 0 0) ∧
    HeckeDyadic.polynomial η false F Y 0 0=
      ∑'n : ℤ,(Real.sqrt (dyadicScale n):ℂ)*
        HeckeDyadic.polynomial η false (annularProfile F (dyadicScale n)) (dyadicScale n*Y) 0 0 := by
  have habs := dyadic_ideal_absolute η F hF Y hY
  have hs := habs.of_norm
  have he (n : ℤ) : (Real.sqrt (dyadicScale n):ℂ)*
      HeckeDyadic.polynomial η false (annularProfile F (dyadicScale n)) (dyadicScale n*Y) 0 0=
      (Real.sqrt Y:ℂ)⁻¹*∑'I : NI,dyadicIdealTerm η F Y I n := by
    rw [←normalized_annular_term η F (dyadicScale n) Y (dyadicScale_pos n) hY,
      polynomial_plain _ _ _ hY]
    congr 1
    apply tsum_congr
    intro I
    simp only [dyadicIdealTerm,dyadicWeight]
    ring
  simp_rw [he]
  refine ⟨hs.prod_symm.prod.mul_left _,?_⟩
  rw [tsum_mul_left,polynomial_plain η F Y hY]
  congr 1
  rw [hs.tsum_comm]
  exact tsum_congr (fun I=>(dyadic_ideal_partition η F Y hY I).symm)

theorem actual_reflected_annular_series (η : Character) (W : 𝓢(ℝ,ℂ))
    (Y : ℝ) (hY : 0< Y) :
    Summable (fun n : ℤ=>(Real.sqrt (dyadicScale n):ℂ)*
      HeckeDyadic.polynomial η false (annularProfile (paperRadialFourier W) (dyadicScale n))
        (dyadicScale n*Y) 0 0) ∧
    HeckeDyadic.polynomial η false (paperRadialFourier W) Y 0 0=
      ∑'n : ℤ,(Real.sqrt (dyadicScale n):ℂ)*
        HeckeDyadic.polynomial η false (annularProfile (paperRadialFourier W) (dyadicScale n))
          (dyadicScale n*Y) 0 0 := by
  exact normalized_annular_series η _ (reflected_decayTwo W) Y hY

end CenteredMomentReflectedSeries

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace CenteredMomentReflectedTruncation
open HeckeFamily CenteredMomentSectorLocalization CenteredMomentReflectedAnnuli
open CenteredMomentComparisonReflection CenteredMomentReflectionDeletion
open CenteredMomentReflectedSeries SchwartzPlanePoisson
local notation "NI" => CubicEisenstein.NonzeroIdeal

theorem normalized_subseries (η : Character) (F : ℝ→ℂ) (hF : DecayTwo F)
    (Y : ℝ) (hY : 0< Y) (A : Set ℤ) :
    Summable (fun n : ℤ=> if n∈A then (Real.sqrt (dyadicScale n):ℂ)*
      HeckeDyadic.polynomial η false (annularProfile F (dyadicScale n)) (dyadicScale n*Y) 0 0 else 0) ∧
    HeckeDyadic.polynomial η false
      (fun x=>(∑'n : ℤ,if n∈A then dyadicWeight n x else 0:ℝ)*F x) Y 0 0=
      ∑'n : ℤ,if n∈A then (Real.sqrt (dyadicScale n):ℂ)*
        HeckeDyadic.polynomial η false (annularProfile F (dyadicScale n)) (dyadicScale n*Y) 0 0 else 0 := by
  have hs := (dyadic_ideal_absolute η F hF Y hY).of_norm
  have hi : Summable (fun p : NI×ℤ=> if p.2∈A then dyadicIdealTerm η F Y p.1 p.2 else 0) :=
    hs.indicator {p : NI×ℤ | p.2∈A}
  have he (n : ℤ) : (if n∈A then (Real.sqrt (dyadicScale n):ℂ)*
      HeckeDyadic.polynomial η false (annularProfile F (dyadicScale n)) (dyadicScale n*Y) 0 0 else 0)=
      (Real.sqrt Y:ℂ)⁻¹*∑'I : NI,if n∈A then dyadicIdealTerm η F Y I n else 0 := by
    split_ifs with hn
    · rw [←normalized_annular_term η F (dyadicScale n) Y (dyadicScale_pos n) hY,
        polynomial_plain _ _ _ hY]
      congr 1
      apply tsum_congr
      intro I
      simp only [dyadicIdealTerm,dyadicWeight]
      ring
    · simp
  simp_rw [he]
  refine ⟨hi.prod_symm.prod.mul_left _,?_⟩
  rw [tsum_mul_left,polynomial_plain η _ Y hY]
  congr 1
  rw [hi.tsum_comm]
  apply tsum_congr
  intro I
  have ht (n : ℤ) : (if n∈A then dyadicIdealTerm η F Y I n else 0)=
      ((if n∈A then dyadicWeight n ((I.val.absNorm:ℝ)/Y) else 0:ℝ):ℂ)*
        (idealCoeff η I.val*F ((I.val.absNorm:ℝ)/Y)) := by
    split_ifs <;> simp only [dyadicIdealTerm,Complex.ofReal_zero,zero_mul] ; ring
  simp_rw [ht]
  rw [tsum_mul_right,←Complex.ofReal_tsum]
  ring

def retainedAnnuli (R Y : ℝ) (hY : 0< Y) : Finset ℤ :=
  (finite_retained_above R (Y⁻¹) (inv_pos.mpr hY)).toFinset

lemma retainedAnnuli_mem (R Y : ℝ) (hY : 0< Y) (n : ℤ) :
    n∈retainedAnnuli R Y hY ↔ Retained R n ∧ ∃q : ℝ,Y⁻¹≤ q ∧ dyadicWeight n q≠0 := by
  exact (finite_retained_above R (Y⁻¹) (inv_pos.mpr hY)).mem_toFinset

lemma original_norm_lower (I : NI) (Y : ℝ) (hY : 0< Y) :
    Y⁻¹≤(I.val.absNorm:ℝ)/Y := by
  have hn : (1:ℝ)≤ I.val.absNorm := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr I.property))
  simpa only [one_div] using div_le_div_of_nonneg_right hn hY.le

theorem retained_finite_series (η : Character) (F : ℝ→ℂ) (hF : DecayTwo F)
    (R Y : ℝ) (hY : 0< Y) :
    HeckeDyadic.polynomial η false (fun x=>(retainedWeight R x:ℂ)*F x) Y 0 0=
      ∑n∈retainedAnnuli R Y hY,(Real.sqrt (dyadicScale n):ℂ)*
        HeckeDyadic.polynomial η false (annularProfile F (dyadicScale n)) (dyadicScale n*Y) 0 0 := by
  have hh := (normalized_subseries η F hF Y hY {n | Retained R n}).2
  change HeckeDyadic.polynomial η false (fun x=>(retainedWeight R x:ℂ)*F x) Y 0 0=_ at hh
  rw [hh,tsum_eq_sum (s:=retainedAnnuli R Y hY)]
  · apply Finset.sum_congr rfl
    intro n hn
    simp only [Set.mem_setOf_eq,if_pos ((retainedAnnuli_mem R Y hY n).mp hn).1]
  · intro n hn
    split_ifs with hr
    · rw [←normalized_annular_term η F (dyadicScale n) Y (dyadicScale_pos n) hY,
        polynomial_plain _ _ _ hY]
      have hz (I : NI) : dyadicWeight n ((I.val.absNorm:ℝ)/Y)=0 := by
        by_contra hne
        exact hn ((retainedAnnuli_mem R Y hY n).mpr ⟨hr,_,original_norm_lower I Y hY,hne⟩)
      have he (I : NI) : idealCoeff η I.val*
          ((annulus (((I.val.absNorm:ℝ)/Y)/dyadicScale n):ℂ)*F ((I.val.absNorm:ℝ)/Y))=0 := by
        change idealCoeff η I.val*((dyadicWeight n ((I.val.absNorm:ℝ)/Y):ℂ)*F _)=0
        rw [hz,Complex.ofReal_zero,zero_mul,mul_zero]
      simp_rw [he,tsum_zero,mul_zero]
    · rfl

end CenteredMomentReflectedTruncation

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace CenteredMomentComparisonReflection
open HeckeFamily SchwartzPlanePoisson
local notation "O" => Eisenstein.O
local notation "NI" => CubicEisenstein.NonzeroIdeal

lemma ideal_norm_rpow_summable (B : ℕ) (hB : 2≤ B) :
    Summable (fun I : NI=>(I.val.absNorm:ℝ)^(-(B:ℝ))) := by
  have hb : (1:ℝ)< B := by exact_mod_cast (by omega : 1< B)
  have hs := (fullIdealWeight_summable_norm (B:ℂ)
    (by simpa using hb)).comp_injective
      (Subtype.val_injective : Function.Injective (fun I : NI=> I.val))
  apply hs.congr
  intro I
  rw [Function.comp_apply,fullIdealWeight,if_neg I.property]
  change ‖((I.val.absNorm:ℝ):ℂ)^(-(B:ℂ))‖=_
  have hi : 0<(I.val.absNorm:ℝ) := HeckeDyadic.norm_pos I
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hi]
  simp

lemma plain_term_rapid_bound (η : Character) (F : ℝ→ℂ) (B : ℕ) (D Y : ℝ)
    (hY : 0< Y) (hF : ∀x : ℝ,0< x → x^B*‖F x‖≤ D) (I : NI) :
    ‖idealCoeff η I.val*F ((I.val.absNorm:ℝ)/Y)‖≤
      (D*Y^B)*(I.val.absNorm:ℝ)^(-(B:ℝ)) := by
  have hi : 0<(I.val.absNorm:ℝ) := HeckeDyadic.norm_pos I
  have hx : 0<(I.val.absNorm:ℝ)/Y := div_pos hi hY
  have hb : ‖F ((I.val.absNorm:ℝ)/Y)‖≤ D/((I.val.absNorm:ℝ)/Y)^B :=
    (le_div_iff₀ (pow_pos hx B)).mpr (by simpa only [mul_comm] using hF _ hx)
  calc
    _≤‖F ((I.val.absNorm:ℝ)/Y)‖:=by
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (idealCoeff_norm_le_one η _)
    _≤ D/((I.val.absNorm:ℝ)/Y)^B:=hb
    _=_:=by
      rw [Real.rpow_neg hi.le,Real.rpow_natCast,div_pow]
      field_simp

theorem plain_rapid_summable (η : Character) (F : ℝ→ℂ) (B : ℕ) (hB : 2≤ B)
    (D Y : ℝ) (hY : 0< Y) (hF : ∀x : ℝ,0< x → x^B*‖F x‖≤ D) :
    Summable (fun I : NI=> idealCoeff η I.val*F ((I.val.absNorm:ℝ)/Y)) := by
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _=> norm_nonneg _)
    (plain_term_rapid_bound η F B D Y hY hF)
    ((ideal_norm_rpow_summable B hB).mul_left (D*Y^B))

theorem plain_rapid_bound (B : ℕ) (hB : 2≤ B) :
    ∃C : ℝ,0< C ∧ ∀(η : Character)(F : ℝ→ℂ)(D Y : ℝ),0≤ D → 0< Y →
      (∀x : ℝ,0< x → x^B*‖F x‖≤ D) →
      ‖HeckeDyadic.polynomial η false F Y 0 0‖≤ C*D*(Y^B/Real.sqrt Y) := by
  let C := 1+∑' I : NI,(I.val.absNorm:ℝ)^(-(B:ℝ))
  have hs := ideal_norm_rpow_summable B hB
  have hnon : 0≤∑' I : NI,(I.val.absNorm:ℝ)^(-(B:ℝ)) :=
    tsum_nonneg (fun I=> Real.rpow_nonneg (HeckeDyadic.norm_pos I).le _)
  refine ⟨C,by dsimp [C];linarith,?_⟩
  intro η F D Y hD hY hF
  have ht := plain_rapid_summable η F B hB D Y hY hF
  have hh := ht.norm.tsum_le_tsum (plain_term_rapid_bound η F B D Y hY hF)
    (hs.mul_left (D*Y^B))
  rw [tsum_mul_left] at hh
  have hb : ‖∑' I : NI,idealCoeff η I.val*F ((I.val.absNorm:ℝ)/Y)‖≤ D*Y^B*C := by
    exact (norm_tsum_le_tsum_norm ht.norm).trans (hh.trans
      (mul_le_mul_of_nonneg_left (by dsimp [C];linarith) (by positivity)))
  rw [polynomial_plain η F Y hY,norm_mul,norm_inv,Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg Y)]
  calc
    _≤(Real.sqrt Y)⁻¹*(D*Y^B*C):=mul_le_mul_of_nonneg_left hb (by positivity)
    _=C*D*(Y^B/Real.sqrt Y):=by ring

theorem actual_reflected_absolute_bound (a b : ℝ) (ha : 0< a) (B : ℕ) (hB : 2≤ B) :
    ∃n : ℕ,∀(W : ℝ→ℂ),∀_hs : Function.support W⊆Set.Icc a b,
      ∀_hW : ContDiff ℝ ∞ W,∃C : ℝ,0< C ∧ ∀(η : Character)(t Y : ℝ),0< Y →
      ‖HeckeDyadic.polynomial η false
        (paperRadialFourier (CompletedHeight.normTwistedSource W t)) Y 0 0‖≤
        C*(1+‖t‖)^n*(Y^B/Real.sqrt Y) := by
  obtain ⟨n,hn⟩ := reflected_profile_height_control a b ha B 0
  obtain ⟨K,hK,hKb⟩ := plain_rapid_bound B hB
  refine ⟨n,?_⟩
  intro W hs hW
  obtain ⟨D,hD,hDb⟩ := hn W hs hW
  refine ⟨K*D,mul_pos hK hD,?_⟩
  intro η t Y hY
  have hf : ∀x : ℝ,0< x → x^B*‖paperRadialFourier (CompletedHeight.normTwistedSource W t) x‖≤ D*(1+‖t‖)^n := by
    intro x hx
    have hh := hDb t 0 (by omega) x hx.le
    simp only [LocalLogFourier.eulerDeriv,iteratedDeriv_zero,Real.exp_zero,mul_one] at hh
    exact (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hx.le (by linarith : x≤1+x) B)
      (norm_nonneg _)).trans hh
  exact (hKb η _ (D*(1+‖t‖)^n) Y (by positivity) hY hf).trans_eq (by ring)

lemma discarded_rapid_control (F : ℝ→ℂ) (A B : ℕ) (D R : ℝ)
    (hD : 0≤ D) (hR : 0< R) (hF : ∀x : ℝ,0< x → x^(B+A)*‖F x‖≤ D) :
    ∀x : ℝ,0< x → x^B*‖(CenteredMomentSectorLocalization.discardedWeight R x:ℂ)*F x‖≤ D/R^A := by
  intro x hx
  by_cases hz : CenteredMomentSectorLocalization.discardedWeight R x=0
  · simp only [hz,Complex.ofReal_zero,zero_mul,norm_zero,mul_zero]
    positivity
  have hRx := (CenteredMomentSectorLocalization.discardedWeight_support R x hz).le
  have hw := CenteredMomentSectorLocalization.discardedWeight_bounds R x
  have hnorm : ‖(CenteredMomentSectorLocalization.discardedWeight R x:ℂ)*F x‖≤‖F x‖ := by
    rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg hw.1]
    exact mul_le_of_le_one_left (norm_nonneg _) hw.2
  apply (mul_le_mul_of_nonneg_left hnorm (pow_nonneg hx.le B)).trans
  apply (le_div_iff₀ (pow_pos hR A)).mpr
  calc
    _≤(x^B*‖F x‖)*x^A :=mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hR.le hRx A) (by positivity)
    _=x^(B+A)*‖F x‖ :=by rw [pow_add];ring
    _≤ D :=hF x hx

theorem actual_reflected_discarded_bound (a b : ℝ) (ha : 0< a) (A B : ℕ) (hB : 2≤ B) :
    ∃n : ℕ,∀(W : ℝ→ℂ),∀_hs : Function.support W⊆Set.Icc a b,
      ∀_hW : ContDiff ℝ ∞ W,∃C : ℝ,0< C ∧ ∀(η : Character)(t Y R : ℝ),0< Y → 0< R →
      ‖HeckeDyadic.polynomial η false
        (fun x=>(CenteredMomentSectorLocalization.discardedWeight R x:ℂ)*
          paperRadialFourier (CompletedHeight.normTwistedSource W t) x) Y 0 0‖≤
        C*(1+‖t‖)^n*(Y^B/Real.sqrt Y)/R^A := by
  obtain ⟨n,hn⟩ := reflected_profile_height_control a b ha (B+A) 0
  obtain ⟨K,hK,hKb⟩ := plain_rapid_bound B hB
  refine ⟨n,?_⟩
  intro W hs hW
  obtain ⟨D,hD,hDb⟩ := hn W hs hW
  refine ⟨K*D,mul_pos hK hD,?_⟩
  intro η t Y R hY hR
  have hf : ∀x : ℝ,0< x → x^(B+A)*‖paperRadialFourier (CompletedHeight.normTwistedSource W t) x‖≤ D*(1+‖t‖)^n := by
    intro x hx
    have hh := hDb t 0 (by omega) x hx.le
    simp only [LocalLogFourier.eulerDeriv,iteratedDeriv_zero,Real.exp_zero,mul_one] at hh
    exact (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hx.le (by linarith : x≤1+x) (B+A))
      (norm_nonneg _)).trans hh
  have hm := discarded_rapid_control _ A B (D*(1+‖t‖)^n) R (by positivity) hR hf
  exact (hKb η _ ((D*(1+‖t‖)^n)/R^A) Y (by positivity) hY hm).trans_eq (by ring)

end CenteredMomentComparisonReflection

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped ContDiff
namespace CenteredMomentComparisonReflection
open HeckeFamily SchwartzPlanePoisson

lemma normalized_power_eq (Y : ℝ) (hY : 0< Y) (B : ℕ) :
    Y^B/Real.sqrt Y=Y^((B:ℝ)-1/2) := by
  rw [Real.rpow_sub hY,Real.rpow_natCast,Real.sqrt_eq_rpow]

theorem actual_reflected_small_negligible (a b xi saving : ℝ) (ha : 0< a) (hxi : 0< xi) :
    ∃n : ℕ,∀(W : ℝ→ℂ),∀_hs : Function.support W⊆Set.Icc a b,
      ∀_hW : ContDiff ℝ ∞ W,∃C : ℝ,0< C ∧ ∀(η : Character)(t Y Z : ℝ),
      1≤ Z → 0< Y → Y≤ Z^(-xi) →
      ‖HeckeDyadic.polynomial η false
        (paperRadialFourier (CompletedHeight.normTwistedSource W t)) Y 0 0‖≤
        C*(1+‖t‖)^n*Z^(-saving) := by
  obtain ⟨B,hB⟩ := exists_nat_gt (max (2:ℝ) (saving/xi+1/2))
  have hB2 : 2≤ B := by exact_mod_cast (le_of_lt ((le_max_left _ _).trans_lt hB))
  have hBp : 0≤(B:ℝ)-1/2 := by have := (le_max_left _ _).trans_lt hB;linarith
  have hsav : saving≤ xi*((B:ℝ)-1/2) := by
    have hh := (le_max_right _ _).trans_lt hB
    have hh' : saving/xi≤(B:ℝ)-1/2 := by linarith
    exact (div_le_iff₀ hxi).mp hh' |>.trans_eq (mul_comm _ _)
  obtain ⟨n,hn⟩ := actual_reflected_absolute_bound a b ha B hB2
  refine ⟨n,?_⟩
  intro W hs hW
  obtain ⟨C,hC,hbound⟩ := hn W hs hW
  refine ⟨C,hC,?_⟩
  intro η t Y Z hZ hY hYZ
  have hz : 0< Z := zero_lt_one.trans_le hZ
  apply (hbound η t Y hY).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [normalized_power_eq Y hY B]
  calc
    _≤(Z^(-xi))^((B:ℝ)-1/2) := Real.rpow_le_rpow hY.le hYZ hBp
    _=Z^((-xi)*((B:ℝ)-1/2)) := (Real.rpow_mul hz.le _ _).symm
    _≤ Z^(-saving) := Real.rpow_le_rpow_of_exponent_le hZ (by nlinarith)

theorem actual_reflected_upper_negligible (a b xi saving L Cscale : ℝ)
    (ha : 0< a) (hxi : 0< xi) (hCscale : 0< Cscale) :
    ∃n : ℕ,∀(W : ℝ→ℂ),∀_hs : Function.support W⊆Set.Icc a b,
      ∀_hW : ContDiff ℝ ∞ W,∃C : ℝ,0< C ∧ ∀(η : Character)(t Y Z : ℝ),
      1≤ Z → 0< Y → Y≤ Cscale*Z^L →
      ‖HeckeDyadic.polynomial η false
        (fun x=>(CenteredMomentSectorLocalization.discardedWeight (Z^(xi/2)) x:ℂ)*
          paperRadialFourier (CompletedHeight.normTwistedSource W t) x) Y 0 0‖≤
        C*(1+‖t‖)^n*Z^(-saving) := by
  obtain ⟨A,hA⟩ := exists_nat_gt ((saving+L*(3/2))/(xi/2))
  have hsav : saving+L*(3/2)≤ xi/2*(A:ℝ) := by
    have hh := (div_le_iff₀ (by linarith : 0< xi/2)).mp hA.le
    nlinarith
  obtain ⟨n,hn⟩ := actual_reflected_discarded_bound a b ha A 2 (by omega)
  refine ⟨n,?_⟩
  intro W hs hW
  obtain ⟨C,hC,hbound⟩ := hn W hs hW
  refine ⟨C*Cscale^(3/2:ℝ),by positivity,?_⟩
  intro η t Y Z hZ hY hYZ
  have hz : 0< Z := zero_lt_one.trans_le hZ
  have hR : 0< Z^(xi/2) := Real.rpow_pos_of_pos hz _
  have hp : Y^2/Real.sqrt Y≤ Cscale^(3/2:ℝ)*Z^(L*(3/2)) := by
    rw [normalized_power_eq Y hY 2]
    norm_num only [Nat.cast_ofNat,show (2:ℝ)-1/2=3/2 by norm_num]
    calc
      _≤(Cscale*Z^L)^(3/2:ℝ) := Real.rpow_le_rpow hY.le hYZ (by norm_num)
      _=_ := by rw [Real.mul_rpow hCscale.le (by positivity),←Real.rpow_mul hz.le]
  have hd : (Z^(xi/2))^A=Z^((xi/2)*(A:ℝ)) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hz.le]
  calc
    _≤ C*(1+‖t‖)^n*(Y^2/Real.sqrt Y)/(Z^(xi/2))^A := hbound η t Y _ hY hR
    _≤ C*(1+‖t‖)^n*(Cscale^(3/2:ℝ)*Z^(L*(3/2)))/(Z^(xi/2))^A :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hp (by positivity)) (by positivity)
    _=(C*Cscale^(3/2:ℝ))*(1+‖t‖)^n*Z^(L*(3/2)-(xi/2)*(A:ℝ)) := by
      rw [hd,Real.rpow_sub hz]
      ring
    _≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ (by linarith)) (by positivity)

end CenteredMomentComparisonReflection

end

end

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
