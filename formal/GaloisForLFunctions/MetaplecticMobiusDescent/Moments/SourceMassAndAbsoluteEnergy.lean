/-
Source mass and absolute energy adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Moments.RetainedEnergiesAndZeroModes

/-!
# Source mass and absolute energy

Finite columns, coefficients and radii of the source mass; added-zero tuples; summability and
absolute bounds of finite Hecke energies.
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
open scoped BigOperators Classical SchwartzMap
local notation "O" => Eisenstein.O
namespace CenteredMomentTail
open Eisenstein  CubicEisenstein SchwartzPlanePoisson
open CenteredMomentCommonSupport CenteredMomentCorrelation CenteredMomentFourier
open CenteredMomentSupportedCorrelation

theorem residueGauss_norm_le (d : O) (hd : d ≠ 0)
    (χ : MulChar (Residue d) ℂ) (h : Residue d) :
    ‖residueGauss d hd χ h‖ ≤ (Ideal.absNorm (Ideal.span {d}) : ℝ) := by
  let := finiteEisensteinQuotientOfNonzero hd
  let : Fintype (Residue d) := Fintype.ofFinite _
  unfold CenteredMomentFourier.residueGauss
  rw [tsum_fintype]
  calc
    _ ≤ ∑ x : Residue d, ‖χ x * residueTraceQuotientChar 1 d hd (h * x)‖ := norm_sum_le _ _
    _ ≤ ∑ _x : Residue d, (1 : ℝ) := Finset.sum_le_sum fun x _ => by
      rw [norm_mul, (residueTraceQuotientChar 1 d hd).norm_apply, mul_one]
      exact FiniteRayExpansion.norm_char_le_one χ x
    _ = _ := by simp [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]

theorem normalizedResidueGauss_norm_le (d : O) (hd : d ≠ 0)
    (χ : MulChar (Residue d) ℂ) (h : Residue d) :
    ‖normalizedResidueGauss d hd χ h‖ ≤ Real.sqrt (Ideal.absNorm (Ideal.span {d}) : ℝ) := by
  have hn : (0 : ℝ) < Ideal.absNorm (Ideal.span {d}) := by
    exact_mod_cast (Nat.pos_of_ne_zero
      (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hd)))
  rw [normalizedResidueGauss, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  apply (div_le_iff₀ (Real.sqrt_pos.mpr hn)).mpr
  rw [Real.mul_self_sqrt hn.le]
  exact residueGauss_norm_le d hd χ h

theorem normalizedResidueGauss_div_root_norm_le_one (d : O) (hd : d ≠ 0)
    (χ : MulChar (Residue d) ℂ) (h : Residue d) :
    ‖normalizedResidueGauss d hd χ h /
      (Real.sqrt (Ideal.absNorm (Ideal.span {d}) : ℝ) : ℂ)‖ ≤ 1 := by
  have hn : (0 : ℝ) < Ideal.absNorm (Ideal.span {d}) := by
    exact_mod_cast (Nat.pos_of_ne_zero
      (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hd)))
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact (div_le_one (Real.sqrt_pos.mpr hn)).mpr (normalizedResidueGauss_norm_le d hd χ h)

theorem fullModulusCorrelation_norm_le (u v : O) (_hu : u ≠ 0) (_hv : v ≠ 0)
    [Fintype (Residue u)] [Fintype (Residue v)]
    (χu : MulChar (Residue u) ℂ) (χv : MulChar (Residue v) ℂ) (j : O) :
    ‖fullModulusCorrelation u v χu χv j‖ ≤
      (Ideal.absNorm (Ideal.span {u}) : ℝ) * (Ideal.absNorm (Ideal.span {v}) : ℝ) := by
  unfold fullModulusCorrelation fullCorrelation
  calc
    _ ≤ ∑ x : Residue u, ‖∑ y : Residue v,
      if scaledResidue u v (u * v) rfl x - scaledResidue v u (u * v) (mul_comm u v) y =
        Ideal.Quotient.mk _ j then χu x * star (χv y) else 0‖ := norm_sum_le _ _
    _ ≤ ∑ _x : Residue u, ∑ _y : Residue v, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro x hx
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro y hy
      split_ifs
      · rw [norm_mul, norm_star]
        exact (mul_le_of_le_one_left (norm_nonneg _)
          (FiniteRayExpansion.norm_char_le_one χu x)).trans
          (FiniteRayExpansion.norm_char_le_one χv y)
      · simp
    _ = _ := by
      simp [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]

theorem actualCorrelation_norm_le (u v : O)
    (hu : CanonicalQuadraticSieve.Supported (Ideal.span {u}))
    (hv : CanonicalQuadraticSieve.Supported (Ideal.span {v})) (j : O) :
    ‖actualCorrelation u v hu hv j‖ ≤
      (Ideal.absNorm (Ideal.span {u}) : ℝ) * (Ideal.absNorm (Ideal.span {v}) : ℝ) := by
  let := finiteEisensteinQuotientOfNonzero (supported_element_ne_zero u hu)
  let := finiteEisensteinQuotientOfNonzero (supported_element_ne_zero v hv)
  let : Fintype (Residue u) := Fintype.ofFinite _
  let : Fintype (Residue v) := Fintype.ofFinite _
  unfold actualCorrelation
  exact fullModulusCorrelation_norm_le u v (supported_element_ne_zero u hu)
    (supported_element_ne_zero v hv) _ _ j

theorem weighted_lattice_tail (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(ℝ, ℂ)) (K T B : ℝ), 0 < K → 0 ≤ T → 0 ≤ B →
      ∀ c : O → ℂ, (∀ h, ‖c h‖ ≤ B) →
      ‖∑' h : {h : O // T ≤ K * ‖ringComplex h‖ ^ 2},
        c h.val * paperRadialFourier W (K * ‖ringComplex h.val‖ ^ 2)‖ ≤
        B * (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) /
          ((min 1 K) ^ 2 * (1 + T) ^ A) := by
  obtain ⟨s, C, hC, ht⟩ := paperRadialFourier_lattice_tail A
  refine ⟨s, C, hC, ?_⟩
  intro W K T B hK hT hB c hc
  let S := {h : O // T ≤ K * ‖ringComplex h‖ ^ 2}
  have hs : Summable (fun h : S => ‖paperRadialFourier W (K * ‖ringComplex h.val‖ ^ 2)‖) :=
    (paperRadialFourier_lattice_summable_norm W K hK).subtype _
  have hpoint (h : S) : ‖c h.val * paperRadialFourier W (K * ‖ringComplex h.val‖ ^ 2)‖ ≤
      B * ‖paperRadialFourier W (K * ‖ringComplex h.val‖ ^ 2)‖ := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hc _) (norm_nonneg _)
  have hsum : Summable (fun h : S =>
      ‖c h.val * paperRadialFourier W (K * ‖ringComplex h.val‖ ^ 2)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hpoint (hs.mul_left B)
  calc
    _ ≤ ∑' h : S, ‖c h.val * paperRadialFourier W (K * ‖ringComplex h.val‖ ^ 2)‖ :=
      norm_tsum_le_tsum_norm hsum
    _ ≤ ∑' h : S, B * ‖paperRadialFourier W (K * ‖ringComplex h.val‖ ^ 2)‖ :=
      hsum.tsum_le_tsum hpoint (hs.mul_left B)
    _ = B * ∑' h : S, ‖paperRadialFourier W (K * ‖ringComplex h.val‖ ^ 2)‖ := tsum_mul_left
    _ ≤ _ := by
      simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left (ht W K T hK hT) hB

theorem weighted_set_lattice_tail (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(ℝ, ℂ)) (D : Set O) (K T B : ℝ), 0 < K → 0 ≤ T → 0 ≤ B →
      (∀ h ∈ D, T ≤ K * ‖ringComplex h‖ ^ 2) →
      ∀ c δ : O → ℂ, (∀ h ∈ D, ‖c h‖ ≤ B) → (∀ h ∈ D, ‖δ h‖ ≤ 1) →
      ‖∑' h : D, δ h.val * c h.val * paperRadialFourier W (K * ‖ringComplex h.val‖ ^ 2)‖ ≤
        B * (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) /
          ((min 1 K) ^ 2 * (1 + T) ^ A) := by
  obtain ⟨s, C, hC, ht⟩ := paperRadialFourier_lattice_tail A
  refine ⟨s, C, hC, ?_⟩
  intro W D K T B hK hT hB hD c δ hc hδ
  let L := {h : O | T ≤ K * ‖ringComplex h‖ ^ 2}
  let f : D → L := fun h => ⟨h.val, hD h.val h.property⟩
  have hfi : Function.Injective f := by
    intro x y h
    exact Subtype.ext (congrArg (fun z : L => z.val) h)
  have hs := paperRadialFourier_lattice_summable_norm W K hK
  have hp (h : D) : ‖δ h.val * c h.val * paperRadialFourier W (K * ‖ringComplex h.val‖ ^ 2)‖ ≤
      B * ‖paperRadialFourier W (K * ‖ringComplex h.val‖ ^ 2)‖ := by
    rw [norm_mul, norm_mul]
    exact mul_le_mul_of_nonneg_right
      ((mul_le_of_le_one_left (norm_nonneg _) (hδ h.val h.property)).trans (hc h.val h.property))
      (norm_nonneg _)
  have hsum : Summable (fun h : D =>
      ‖δ h.val * c h.val * paperRadialFourier W (K * ‖ringComplex h.val‖ ^ 2)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hp ((hs.subtype D).mul_left B)
  calc
    _ ≤ ∑' h : D, ‖δ h.val * c h.val * paperRadialFourier W (K * ‖ringComplex h.val‖ ^ 2)‖ :=
      norm_tsum_le_tsum_norm hsum
    _ ≤ ∑' h : D, B * ‖paperRadialFourier W (K * ‖ringComplex h.val‖ ^ 2)‖ :=
      hsum.tsum_le_tsum hp ((hs.subtype D).mul_left B)
    _ = B * ∑' h : D, ‖paperRadialFourier W (K * ‖ringComplex h.val‖ ^ 2)‖ := tsum_mul_left
    _ ≤ B * ∑' h : L, ‖paperRadialFourier W (K * ‖ringComplex h.val‖ ^ 2)‖ :=
      mul_le_mul_of_nonneg_left ((hs.subtype D).tsum_le_tsum_of_inj f hfi
        (fun _ _ => norm_nonneg _) (fun _ => le_rfl) (hs.subtype L)) hB
    _ ≤ _ := by
      convert mul_le_mul_of_nonneg_left (ht W K T hK hT) hB using 1 <;> first | rfl | ring

theorem uniform_sector_lattice_tail (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(ℝ, ℂ)) (D : Set O) (K₀ T B : ℝ), 0 < K₀ → 0 ≤ T → 0 ≤ B →
      (∀ h ∈ D, T ≤ K₀ * ‖ringComplex h‖ ^ 2) →
      ∀ K : ℝ, K₀ ≤ K →
      ∀ c δ : O → ℂ, (∀ h ∈ D, ‖c h‖ ≤ B) → (∀ h ∈ D, ‖δ h‖ ≤ 1) →
      ‖∑' h : D, δ h.val * c h.val * paperRadialFourier W (K * ‖ringComplex h.val‖ ^ 2)‖ ≤
        B * (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) /
          ((min 1 K₀) ^ 2 * (1 + T) ^ A) := by
  obtain ⟨s, C, hC, ht⟩ := weighted_set_lattice_tail A
  refine ⟨s, C, hC, ?_⟩
  intro W D K₀ T B hK₀ hT hB hD K hK c δ hc hδ
  have hD' (h : O) (hh : h ∈ D) : T ≤ K * ‖ringComplex h‖ ^ 2 :=
    (hD h hh).trans (mul_le_mul_of_nonneg_right hK (sq_nonneg _))
  apply (ht W D K T B (hK₀.trans_le hK) hT hB hD' c δ hc hδ).trans
  apply div_le_div_of_nonneg_left (by positivity)
    (by have : 0 < min 1 K₀ := lt_min zero_lt_one hK₀; positivity)
  gcongr

theorem actual_correlation_tail (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(ℝ, ℂ)) (K T : ℝ), 0 < K → 0 ≤ T →
      ∀ (u v : O) (hu : CanonicalQuadraticSieve.Supported (Ideal.span {u}))
        (hv : CanonicalQuadraticSieve.Supported (Ideal.span {v})),
      ‖∑' h : {h : O // T ≤ K * ‖ringComplex h‖ ^ 2},
        actualCorrelation u v hu hv (-h.val) *
          paperRadialFourier W (K * ‖ringComplex h.val‖ ^ 2)‖ ≤
        ((Ideal.absNorm (Ideal.span {u}) : ℝ) * (Ideal.absNorm (Ideal.span {v}) : ℝ)) *
          (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) /
            ((min 1 K) ^ 2 * (1 + T) ^ A) := by
  obtain ⟨s, C, hC, ht⟩ := weighted_lattice_tail A
  refine ⟨s, C, hC, ?_⟩
  intro W K T hK hT u v hu hv
  exact ht W K T _ hK hT (by positivity) _
    (fun h => actualCorrelation_norm_le u v hu hv (-h))


end CenteredMomentTail
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace CenteredMomentAddedZero
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentRowNorm CenteredMomentFourier CenteredMomentCommonSupport
open CenteredMomentSupportedCorrelation CenteredMomentGaussEnergy CenteredMomentZeroMode
open CenteredExceptionalCount CenteredMomentRectangle CenteredMomentExtraction
open UniqueFactorizationMonoid 
local notation "O" => Eisenstein.O

lemma supported_one_ideal : Supported (1 : Ideal O) := by
  refine ⟨one_ne_zero, ?_⟩
  intro P hP
  simp only [normalizedFactors_one, Multiset.notMem_zero] at hP

lemma supported_one_element : Supported (Ideal.span {(1 : O)}) := by
  simpa only [Ideal.span_singleton_one, Ideal.one_eq_top] using supported_one_ideal

theorem pairFourier_one (u : O) (hu : Supported (Ideal.span {u})) (h : O) :
    pairFourier u 1 hu supported_one_element h =
      ProbePhysical.sexticGauss u (supported_element_ne_zero u hu) h := by
  have hone (x : Residue (1 : O)) : supportedModulusCharacter 1 supported_one_element x = 1 := by
    obtain ⟨n, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [supportedModulusCharacter_mk]
    simpa only [Ideal.span_singleton_one, Ideal.one_eq_top] using (idealRowHom n).map_one
  have aux (v : O) (hd : u ∣ v) (hv : v ≠ 0) (he : v = u) :
      (∑' x : Residue v, supportedModulusCharacter u hu (frequencyReduction u v hd x) *
        CubicEisenstein.residueTraceQuotientChar 1 v hv (Ideal.Quotient.mk _ h * x)) =
      residueGauss u (supported_element_ne_zero u hu) (supportedModulusCharacter u hu)
        (Ideal.Quotient.mk _ h) := by
    subst v
    apply tsum_congr
    intro x
    obtain ⟨n, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [frequencyReduction_mk]
  rw [← residueGauss_supported_mk u hu h]
  simpa only [pairFourier, pairResidue, hone, star_one, mul_one] using
    aux (u * 1) (dvd_mul_right u 1)
      (mul_ne_zero (supported_element_ne_zero u hu) (supported_element_ne_zero 1 supported_one_element))
      (mul_one u)

theorem gaussRow_zero_sixthRemainder (u : O) (hu : Supported (Ideal.span {u}))
    (hzero : gaussRow u hu 0 ≠ 0) : sixthRemainder (Ideal.span {u}) = 1 := by
  have hg : ProbePhysical.sexticGauss u (supported_element_ne_zero u hu) 0 ≠ 0 := by
    intro hz
    apply hzero
    simp only [gaussRow, hz, zero_div]
  have hm : pairFourier u 1 hu supported_one_element 0 ≠ 0 := by
    rwa [pairFourier_one]
  apply sixthRemainder_eq_of_prime_profile one_ne_zero
  intro P hP
  by_cases hmem : P ∈ normalizedFactors (Ideal.span {u})
  · obtain ⟨hmax, hlam, hodd⟩ := CanonicalQuadraticSieve.supported_factors_good _ hu P hmem
    let := hmax
    have hv := valuation_profile_of_mean_ne_zero u 1 hu supported_one_element hm P hlam hodd
    simpa only [Ideal.span_singleton_one, ← Ideal.one_eq_top, valuation,
      normalizedFactors_one, Multiset.count_zero, Nat.zero_mod] using hv
  · simp only [valuation, Multiset.count_eq_zero.mpr hmem, normalizedFactors_one,
      Multiset.count_zero, Nat.zero_mod]

theorem gaussRow_zero_ideal_sixth_power (u : O) (hu : Supported (Ideal.span {u}))
    (hzero : gaussRow u hu 0 ≠ 0) :
    sixthQuotient (Ideal.span {u}) ^ 6 = Ideal.span {u} := by
  simpa only [gaussRow_zero_sixthRemainder u hu hzero, one_mul] using
    sixth_normal_form (Ideal.span {u}) hu.1

theorem gaussRow_norm_le (u : O) (hu : Supported (Ideal.span {u})) (h : O) :
    ‖gaussRow u hu h‖ ≤ Real.sqrt (Ideal.absNorm (Ideal.span {u}) : ℝ) := by
  have hb := CenteredMomentTail.normalizedResidueGauss_norm_le u
    (supported_element_ne_zero u hu) (supportedModulusCharacter u hu) (Ideal.Quotient.mk _ h)
  simpa only [normalizedResidueGauss, residueGauss_supported_mk,
    gaussRow] using hb

theorem squarefree_divisor_sixth_of_gauss_zero (u : O)
    (hu : Supported (Ideal.span {u})) (hzero : gaussRow u hu 0 ≠ 0)
    (s : Ideal O) (hs : Squarefree s) (hd : s ∣ Ideal.span {u}) :
    s ^ 6 ∣ Ideal.span {u} := by
  have he := gaussRow_zero_ideal_sixth_power u hu hzero
  rw [← he] at hd ⊢
  exact pow_dvd_pow_of_dvd ((hs.dvd_pow_iff_dvd (by decide : 6 ≠ 0)).mp hd) 6

def idealGaussRow (I : Ideal O) (hI : Supported I) (h : O) : ℂ :=
  gaussRow (primaryIdealGenerator I) ((supported_span_primaryIdealGenerator_iff I).mpr hI) h

lemma idealGaussRow_norm_le (I : Ideal O) (hI : Supported I) (h : O) :
    ‖idealGaussRow I hI h‖ ≤ Real.sqrt (Ideal.absNorm I : ℝ) := by
  have hb := gaussRow_norm_le (primaryIdealGenerator I) ((supported_span_primaryIdealGenerator_iff I).mpr hI) h
  simpa only [idealGaussRow, (primaryIdealGenerator_spec I (supported_primaryIdealGenerator_ne_zero I hI)).1] using hb

lemma idealGaussRow_zero_sixthRemainder (I : Ideal O) (hI : Supported I)
    (hz : idealGaussRow I hI 0 ≠ 0) : sixthRemainder I = 1 := by
  have hb := gaussRow_zero_sixthRemainder (primaryIdealGenerator I)
    ((supported_span_primaryIdealGenerator_iff I).mpr hI) hz
  simpa only [idealGaussRow, (primaryIdealGenerator_spec I (supported_primaryIdealGenerator_ne_zero I hI)).1] using hb

def tupleProduct {r : ℕ} (v : Fin r → Ideal O) : Ideal O := ∏ i, v i

lemma tupleEntry_dvd {r : ℕ} (v : Fin r → Ideal O) (i : Fin r) : v i ∣ tupleProduct v :=
  Finset.dvd_prod_of_mem v (Finset.mem_univ i)

theorem tuple_product_fiber_card {r : ℕ} (S : Finset (Fin r → Ideal O))
    (I : Ideal O) (hI : I ≠ 0) :
    (S.filter (fun v => tupleProduct v = I)).card ≤ (idealDivisors I).card ^ r := by
  let T := S.filter (fun v => tupleProduct v = I)
  let f (v : T) : Fin r → idealDivisors I := fun i => ⟨v.val i, by
    apply (mem_idealDivisors hI).mpr
    rw [← (Finset.mem_filter.mp v.property).2]
    exact tupleEntry_dvd v.val i⟩
  have hf : Function.Injective f := by
    intro v w he
    apply Subtype.ext
    funext i
    exact congrArg Subtype.val (congrFun he i)
  simpa only [Fintype.card_coe, Fintype.card_fun, Fintype.card_fin, T] using
    Fintype.card_le_of_injective f hf

def idealAddedZero (S : Finset (Ideal O)) (hS : ∀ I ∈ S, Supported I)
    (c : Ideal O → ℂ) : ℂ :=
  ∑ I : S, c I.val * idealGaussRow I.val (hS I.val I.property) 0

theorem idealAddedZero_norm_le (S : Finset (Ideal O)) (hS : ∀ I ∈ S, Supported I)
    (c : Ideal O → ℂ) (B Y : ℝ) (hB : 0 ≤ B) (hY : 0 ≤ Y)
    (hc : ∀ I ∈ S, ‖c I‖ ≤ B) (hN : ∀ I ∈ S, (Ideal.absNorm I : ℝ) ≤ Y) :
    ‖idealAddedZero S hS c‖ ≤ (128 * Y ^ (1 / 6 : ℝ)) * (B * Real.sqrt Y) := by
  let F := S.filter (fun I => sixthRemainder I = 1)
  have hcount : (F.card : ℝ) ≤ 128 * Y ^ (1 / 6 : ℝ) := by
    simpa only [map_one, Nat.cast_one, div_one] using
      ideal_count_fixed_remainder F 1 one_ne_zero Y hY
        (fun I hI => (hS I (Finset.mem_filter.mp hI).1).1)
        (fun I hI => (Finset.mem_filter.mp hI).2)
        (fun I hI => hN I (Finset.mem_filter.mp hI).1)
  have hb (I : S) : ‖c I.val * idealGaussRow I.val (hS I.val I.property) 0‖ ≤
      if sixthRemainder I.val = 1 then B * Real.sqrt Y else 0 := by
    by_cases hr : sixthRemainder I.val = 1
    · simp only [hr, ite_true, norm_mul]
      exact mul_le_mul (hc I.val I.property)
        ((idealGaussRow_norm_le _ _ _).trans (Real.sqrt_le_sqrt (hN I.val I.property)))
        (norm_nonneg _) hB
    · have hz : idealGaussRow I.val (hS I.val I.property) 0 = 0 := by
        by_contra hn
        exact hr (idealGaussRow_zero_sixthRemainder _ _ hn)
      simp only [hr, ite_false, hz, mul_zero, norm_zero, le_refl]
  calc
    ‖idealAddedZero S hS c‖ ≤ ∑ I : S,
        ‖c I.val * idealGaussRow I.val (hS I.val I.property) 0‖ := norm_sum_le _ _
    _ ≤ ∑ I : S, if sixthRemainder I.val = 1 then B * Real.sqrt Y else 0 :=
      Finset.sum_le_sum (fun I _ => hb I)
    _ = (F.card : ℝ) * (B * Real.sqrt Y) := by
      rw [Finset.sum_coe_sort S (fun I => if sixthRemainder I = 1 then B * Real.sqrt Y else 0)]
      rw [← Finset.sum_filter]
      simp only [F, Finset.sum_const, nsmul_eq_mul]
    _ ≤ (128 * Y ^ (1 / 6 : ℝ)) * (B * Real.sqrt Y) :=
      mul_le_mul_of_nonneg_right hcount (mul_nonneg hB (Real.sqrt_nonneg _))

def normalizedIdealAddedZero (S : Finset (Ideal O)) (hS : ∀ I ∈ S, Supported I)
    (c : Ideal O → ℂ) (T : ℝ) : ℂ := (Real.sqrt T : ℂ)⁻¹ * idealAddedZero S hS c

theorem idealAddedZero_energy (S : Finset (Ideal O)) (hS : ∀ I ∈ S, Supported I)
    (c : Ideal O → ℂ) (B Y T : ℝ) (hB : 0 ≤ B) (hY : 0 ≤ Y) (hT : 0 < T)
    (hc : ∀ I ∈ S, ‖c I‖ ≤ B) (hN : ∀ I ∈ S, (Ideal.absNorm I : ℝ) ≤ Y) :
    ‖normalizedIdealAddedZero S hS c T‖ ^ 2 ≤ 16384 * B ^ 2 * T⁻¹ * Y ^ (4 / 3 : ℝ) := by
  have hb := idealAddedZero_norm_le S hS c B Y hB hY hc hN
  have hp : (Y ^ (1 / 6 : ℝ)) ^ 2 * Y = Y ^ (4 / 3 : ℝ) := by
    rw [← Real.rpow_mul_natCast hY]
    norm_num only [Nat.cast_ofNat]
    conv_lhs => rhs; rw [← Real.rpow_one Y]
    rw [← Real.rpow_add' hY (by norm_num : (1 / 3 : ℝ) + 1 ≠ 0)]
    norm_num
  have hs := sq_le_sq₀ (norm_nonneg (idealAddedZero S hS c)) (by positivity : 0 ≤ (128 * Y ^ (1 / 6 : ℝ)) * (B * Real.sqrt Y))
  have hb2 := hs.mpr hb
  have hn : ‖normalizedIdealAddedZero S hS c T‖ ^ 2 = T⁻¹ * ‖idealAddedZero S hS c‖ ^ 2 := by
    simp only [normalizedIdealAddedZero, norm_mul, norm_inv, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg T), mul_pow, inv_pow,
      Real.sq_sqrt hT.le]
  rw [hn]
  calc
    T⁻¹ * ‖idealAddedZero S hS c‖ ^ 2 ≤ T⁻¹ * ((128 * Y ^ (1 / 6 : ℝ)) * (B * Real.sqrt Y)) ^ 2 :=
      mul_le_mul_of_nonneg_left hb2 (inv_nonneg.mpr hT.le)
    _ = 16384 * B ^ 2 * T⁻¹ * Y ^ (4 / 3 : ℝ) := by
      rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hY]
      rw [← hp]
      ring

def tupleCoefficient {r : ℕ} (S : Finset (Fin r → Ideal O))
    (β : (Fin r → Ideal O) → ℂ) (I : Ideal O) : ℂ :=
  ∑ v ∈ S.filter (fun v => tupleProduct v = I), β v

def tupleColumns {r : ℕ} (S : Finset (Fin r → Ideal O)) : Finset (Ideal O) :=
  S.image tupleProduct

lemma tupleColumns_supported {r : ℕ} (S : Finset (Fin r → Ideal O))
    (hS : ∀ v ∈ S, Supported (tupleProduct v)) :
    ∀ I ∈ tupleColumns S, Supported I := by
  intro I hI
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hI
  exact hS v hv

theorem tupleCoefficient_norm_le {r : ℕ} (S : Finset (Fin r → Ideal O))
    (β : (Fin r → Ideal O) → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hβ : ∀ v ∈ S, ‖β v‖ ≤ B) (I : Ideal O) (hI : I ≠ 0) :
    ‖tupleCoefficient S β I‖ ≤ B * ((idealDivisors I).card : ℝ) ^ r := by
  calc
    ‖tupleCoefficient S β I‖ ≤ ∑ v ∈ S.filter (fun v => tupleProduct v = I), ‖β v‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _v ∈ S.filter (fun v => tupleProduct v = I), B :=
      Finset.sum_le_sum (fun v hv => hβ v (Finset.mem_filter.mp hv).1)
    _ = B * ((S.filter (fun v => tupleProduct v = I)).card : ℝ) := by
      simp only [Finset.sum_const, nsmul_eq_mul]; ring
    _ ≤ B * ((idealDivisors I).card : ℝ) ^ r := by
      apply mul_le_mul_of_nonneg_left _ hB
      exact_mod_cast tuple_product_fiber_card S I hI

theorem tuple_added_zero_energy (r : ℕ) (hr : 0 < r) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset (Fin r → Ideal O))
      (hS : ∀ v ∈ S, Supported (tupleProduct v))
      (β : (Fin r → Ideal O) → ℂ) (B Y T : ℝ),
      0 ≤ B → 1 ≤ Y → 0 < T →
      (∀ v ∈ S, ‖β v‖ ≤ B) →
      (∀ v ∈ S, (Ideal.absNorm (tupleProduct v) : ℝ) ≤ Y) →
      ‖normalizedIdealAddedZero (tupleColumns S) (tupleColumns_supported S hS)
          (tupleCoefficient S β) T‖ ^ 2 ≤ C * B ^ 2 * T⁻¹ * Y ^ (4 / 3 + ε : ℝ) := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  let δ := ε / (2 * r)
  have hδ : 0 < δ := div_pos hε (mul_pos (by norm_num) hr')
  obtain ⟨D, hD, hdiv⟩ := IdealDivisorBound.ideal_divisor_small_power δ hδ
  refine ⟨16384 * (D ^ r) ^ 2, by positivity, ?_⟩
  intro S hS β B Y T hB hY hT hβ hN
  have hY0 : 0 < Y := lt_of_lt_of_le zero_lt_one hY
  have hδr : δ * (r : ℝ) = ε / 2 := by dsimp [δ]; field_simp
  have hc (I : Ideal O) (hI : I ∈ tupleColumns S) :
      ‖tupleCoefficient S β I‖ ≤ B * (D ^ r * Y ^ (ε / 2)) := by
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hI
    have hI0 := (hS v hv).1
    have hn0 : (0 : ℝ) ≤ Ideal.absNorm (tupleProduct v) := Nat.cast_nonneg _
    calc
      ‖tupleCoefficient S β (tupleProduct v)‖ ≤
          B * ((idealDivisors (tupleProduct v)).card : ℝ) ^ r :=
        tupleCoefficient_norm_le S β B hB hβ _ hI0
      _ ≤ B * (D * (Ideal.absNorm (tupleProduct v) : ℝ) ^ δ) ^ r :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) (hdiv _ hI0) _) hB
      _ = B * (D ^ r * (Ideal.absNorm (tupleProduct v) : ℝ) ^ (ε / 2)) := by
        rw [mul_pow, ← Real.rpow_mul_natCast hn0, hδr]
      _ ≤ B * (D ^ r * Y ^ (ε / 2)) := by
        gcongr
        exact hN v hv
  have hn (I : Ideal O) (hI : I ∈ tupleColumns S) : (Ideal.absNorm I : ℝ) ≤ Y := by
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hI
    exact hN v hv
  have he := idealAddedZero_energy (tupleColumns S) (tupleColumns_supported S hS)
    (tupleCoefficient S β) (B * (D ^ r * Y ^ (ε / 2))) Y T (by positivity) hY0.le hT hc hn
  have hy : (Y ^ (ε / 2)) ^ 2 * Y ^ (4 / 3 : ℝ) = Y ^ (4 / 3 + ε : ℝ) := by
    rw [← Real.rpow_mul_natCast hY0.le, ← Real.rpow_add hY0]
    congr 1
    norm_num
    ring
  calc
    _ ≤ 16384 * (B * (D ^ r * Y ^ (ε / 2))) ^ 2 * T⁻¹ * Y ^ (4 / 3 : ℝ) := he
    _ = (16384 * (D ^ r) ^ 2) * B ^ 2 * T⁻¹ * Y ^ (4 / 3 + ε : ℝ) := by
      rw [← hy]
      ring

def originalCoefficient (N : ℕ) (c : O) (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (R : Ideal O) (t : ℝ) (ν : Fin N → Ideal O → ℂ)
    (Wslot : Fin N → ℝ → ℂ) (P : Fin N → ℝ) (W₁ W₂ : ℝ → ℂ)
    (X₁ X₂ Y₁ Y₂ : ℝ) (b₁ b₂ s : Ideal O) (v : Fin (N + 2) → Ideal O) : ℂ :=
  (∏ j : Fin N, ν j (v (j.castAdd 2)) *
      Wslot j ((Ideal.absNorm (v (j.castAdd 2)) : ℝ) / P j)) *
    idealWeight c χ R t (tupleProduct v) *
    idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂
      (b₁ * v ⟨N, by omega⟩) (b₂ * v ⟨N + 1, by omega⟩) *
    (if s ∣ tupleProduct v then 1 else 0)

lemma idealRectangle_norm_le (W₁ W₂ : ℝ → ℂ) (B₁ B₂ : ℝ)
    (hB₁ : 0 ≤ B₁) (_hB₂ : 0 ≤ B₂)
    (hW₁ : ∀ x, ‖W₁ x‖ ≤ B₁) (hW₂ : ∀ x, ‖W₂ x‖ ≤ B₂)
    (X₁ X₂ Y₁ Y₂ : ℝ) (I J : Ideal O) :
    ‖idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ I J‖ ≤ 2 * B₁ * B₂ := by
  have hprod (x y : ℝ) : ‖W₁ x * W₂ y‖ ≤ B₁ * B₂ := by
    rw [norm_mul]
    exact mul_le_mul (hW₁ x) (hW₂ y) (norm_nonneg _) hB₁
  unfold idealRectangle
  exact (norm_sub_le _ _).trans ((add_le_add
    (hprod ((Ideal.absNorm I : ℝ) / X₁) ((Ideal.absNorm J : ℝ) / X₂))
    (hprod ((Ideal.absNorm I : ℝ) / Y₁) ((Ideal.absNorm J : ℝ) / Y₂))).trans_eq (by ring))

theorem originalCoefficient_norm_le (N : ℕ) (c : O) (hc : c ≠ 0)
    (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (R : Ideal O) (t : ℝ)
    (ν : Fin N → Ideal O → ℂ) (Wslot : Fin N → ℝ → ℂ) (P : Fin N → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (b₁ b₂ s : Ideal O)
    (Bslot : Fin N → ℝ) (B₁ B₂ : ℝ)
    (hBslot : ∀ j, 0 ≤ Bslot j) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hν : ∀ j I, ‖ν j I‖ ≤ 1) (hWslot : ∀ j x, ‖Wslot j x‖ ≤ Bslot j)
    (hW₁ : ∀ x, ‖W₁ x‖ ≤ B₁) (hW₂ : ∀ x, ‖W₂ x‖ ≤ B₂)
    (v : Fin (N + 2) → Ideal O) (hv : tupleProduct v ≠ 0) :
    ‖originalCoefficient N c χ R t ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ b₁ b₂ s v‖ ≤
      (∏ j, Bslot j) * (2 * B₁ * B₂) := by
  have hslots : ‖∏ j : Fin N, ν j (v (j.castAdd 2)) *
      Wslot j ((Ideal.absNorm (v (j.castAdd 2)) : ℝ) / P j)‖ ≤ ∏ j, Bslot j := by
    rw [norm_prod]
    apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
    intro j hj
    rw [norm_mul]
    simpa only [one_mul] using mul_le_mul (hν j _) (hWslot j _) (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  have hweight := idealWeight_norm_le_one c hc χ R t (tupleProduct v) hv
  have hrect := idealRectangle_norm_le W₁ W₂ B₁ B₂ hB₁ hB₂ hW₁ hW₂ X₁ X₂ Y₁ Y₂
    (b₁ * v ⟨N, by omega⟩) (b₂ * v ⟨N + 1, by omega⟩)
  by_cases hs : s ∣ tupleProduct v
  · simp only [originalCoefficient, hs, ite_true, mul_one, norm_mul]
    have hsw := mul_le_mul hslots hweight (norm_nonneg _) (Finset.prod_nonneg (fun j _ => hBslot j))
    simp only [mul_one] at hsw
    exact mul_le_mul hsw hrect (norm_nonneg _) (Finset.prod_nonneg (fun j _ => hBslot j))
  · simp only [originalCoefficient, hs, ite_false, mul_zero, norm_zero]
    exact mul_nonneg (Finset.prod_nonneg (fun j _ => hBslot j)) (by positivity)

lemma originalCoefficient_eq_zero_of_not_dvd (N : ℕ) (c : O)
    (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (R : Ideal O) (t : ℝ)
    (ν : Fin N → Ideal O → ℂ) (Wslot : Fin N → ℝ → ℂ) (P : Fin N → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (b₁ b₂ s : Ideal O)
    (v : Fin (N + 2) → Ideal O) (hs : ¬s ∣ tupleProduct v) :
    originalCoefficient N c χ R t ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ b₁ b₂ s v = 0 := by
  simp only [originalCoefficient, hs, ite_false, mul_zero]

theorem original_added_zero_energy (N : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (c : O), c ≠ 0 →
      ∀ (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (R : Ideal O) (t : ℝ)
      (ν : Fin N → Ideal O → ℂ) (Wslot : Fin N → ℝ → ℂ) (P : Fin N → ℝ)
      (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (b₁ b₂ s : Ideal O)
      (Bslot : Fin N → ℝ) (B₁ B₂ : ℝ),
      (∀ j, 0 ≤ Bslot j) → 0 ≤ B₁ → 0 ≤ B₂ →
      (∀ j I, ‖ν j I‖ ≤ 1) → (∀ j x, ‖Wslot j x‖ ≤ Bslot j) →
      (∀ x, ‖W₁ x‖ ≤ B₁) → (∀ x, ‖W₂ x‖ ≤ B₂) →
      ∀ (S : Finset (Fin (N + 2) → Ideal O))
      (hS : ∀ v ∈ S, Supported (tupleProduct v)) (Y T : ℝ), 1 ≤ Y → 0 < T →
      (∀ v ∈ S, (Ideal.absNorm (tupleProduct v) : ℝ) ≤ Y) →
      ‖normalizedIdealAddedZero (tupleColumns S) (tupleColumns_supported S hS)
        (tupleCoefficient S (originalCoefficient N c χ R t ν Wslot P W₁ W₂
          X₁ X₂ Y₁ Y₂ b₁ b₂ s)) T‖ ^ 2 ≤
        C * ((∏ j, Bslot j) * (2 * B₁ * B₂)) ^ 2 * T⁻¹ * Y ^ (4 / 3 + ε : ℝ) := by
  obtain ⟨C, hC, he⟩ := tuple_added_zero_energy (N + 2) (by omega) ε hε
  refine ⟨C, hC, ?_⟩
  intro c hc χ R t ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ b₁ b₂ s Bslot B₁ B₂
    hBslot hB₁ hB₂ hν hWslot hW₁ hW₂ S hS Y T hY hT hN
  apply he S hS _ _ Y T (mul_nonneg (Finset.prod_nonneg (fun j _ => hBslot j)) (by positivity)) hY hT _ hN
  intro v hv
  exact originalCoefficient_norm_le N c hc χ R t ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ b₁ b₂ s
    Bslot B₁ B₂ hBslot hB₁ hB₂ hν hWslot hW₁ hW₂ v (hS v hv).1

theorem idealAddedZero_eq_gaussPolynomial (S : Finset (Ideal O))
    (hS : ∀ I ∈ S, Supported I) (c : Ideal O → ℂ) :
    idealAddedZero S hS c =
      gaussPolynomial (Finset.univ : Finset S)
        (fun I => primaryIdealGenerator I.val)
        (fun I => (supported_span_primaryIdealGenerator_iff I.val).mpr (hS I.val I.property))
        (fun I => c I.val) 0 := rfl

lemma idealGaussRow_zero_divisor_sixth (I : Ideal O) (hI : Supported I)
    (hz : idealGaussRow I hI 0 ≠ 0) (s : Ideal O) (hs : Squarefree s) (hd : s ∣ I) :
    s ^ 6 ∣ I := by
  have hrem := idealGaussRow_zero_sixthRemainder I hI hz
  have he : sixthQuotient I ^ 6 = I := by
    simpa only [hrem, one_mul] using sixth_normal_form I hI.1
  rw [← he] at hd ⊢
  exact pow_dvd_pow_of_dvd ((hs.dvd_pow_iff_dvd (by decide : 6 ≠ 0)).mp hd) 6

theorem idealAddedZero_nonzero_mask_norm (S : Finset (Ideal O))
    (hS : ∀ I ∈ S, Supported I) (c : Ideal O → ℂ) (s : Ideal O) (hs : Squarefree s)
    (hmask : ∀ I ∈ S, ¬s ∣ I → c I = 0) (Y : ℝ)
    (hN : ∀ I ∈ S, (Ideal.absNorm I : ℝ) ≤ Y)
    (hz : idealAddedZero S hS c ≠ 0) : (Ideal.absNorm s : ℝ) ^ 6 ≤ Y := by
  obtain ⟨I, _, hI⟩ := Finset.exists_ne_zero_of_sum_ne_zero hz
  have hg : idealGaussRow I.val (hS I.val I.property) 0 ≠ 0 := by
    intro he
    exact hI (by rw [he, mul_zero])
  have hd : s ∣ I.val := by
    by_contra hn
    exact hI (by rw [hmask I.val I.property hn, zero_mul])
  have hpow := idealGaussRow_zero_divisor_sixth I.val (hS I.val I.property) hg s hs hd
  have hn := (norm_le_of_dvd (hS I.val I.property).1 hpow).trans (hN I.val I.property)
  simpa only [map_pow, Nat.cast_pow] using hn

theorem original_tupleCoefficient_mask (N : ℕ) (c : O)
    (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (R : Ideal O) (t : ℝ)
    (ν : Fin N → Ideal O → ℂ) (Wslot : Fin N → ℝ → ℂ) (P : Fin N → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (b₁ b₂ s : Ideal O)
    (S : Finset (Fin (N + 2) → Ideal O)) (I : Ideal O) (hs : ¬s ∣ I) :
    tupleCoefficient S (originalCoefficient N c χ R t ν Wslot P W₁ W₂
      X₁ X₂ Y₁ Y₂ b₁ b₂ s) I = 0 := by
  apply Finset.sum_eq_zero
  intro v hv
  apply originalCoefficient_eq_zero_of_not_dvd
  rwa [(Finset.mem_filter.mp hv).2]

theorem added_zero_exponent (a s θ : ℝ) (ha : -θ ≤ a) (hs : s ≤ (a + θ) / 6) :
    a / 3 + 4 * θ / 3 ≤ a - s + 2 * θ := by linarith

theorem added_zero_scale_identity (Z a θ : ℝ) (hZ : 0 < Z) :
    (Z ^ a)⁻¹ * (Z ^ (a + θ)) ^ (4 / 3 : ℝ) = Z ^ (a / 3 + 4 * θ / 3) := by
  rw [← Real.rpow_neg hZ.le, ← Real.rpow_mul hZ.le, ← Real.rpow_add hZ]
  congr 1
  ring

theorem idealAddedZero_source_energy (S : Finset (Ideal O))
    (hS : ∀ I ∈ S, Supported I) (c : Ideal O → ℂ) (B Z a s θ : ℝ)
    (hB : 0 ≤ B) (hZ : 1 ≤ Z) (ha : -θ ≤ a) (hs : s ≤ (a + θ) / 6)
    (hc : ∀ I ∈ S, ‖c I‖ ≤ B)
    (hN : ∀ I ∈ S, (Ideal.absNorm I : ℝ) ≤ Z ^ (a + θ)) :
    ‖normalizedIdealAddedZero S hS c (Z ^ a)‖ ^ 2 ≤
      16384 * B ^ 2 * Z ^ (a - s + 2 * θ) := by
  have hZ0 : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  have he := idealAddedZero_energy S hS c B (Z ^ (a + θ)) (Z ^ a)
    hB (Real.rpow_nonneg hZ0.le _) (Real.rpow_pos_of_pos hZ0 _) hc hN
  calc
    _ ≤ 16384 * B ^ 2 * (Z ^ a)⁻¹ * (Z ^ (a + θ)) ^ (4 / 3 : ℝ) := he
    _ = 16384 * B ^ 2 * Z ^ (a / 3 + 4 * θ / 3) := by
      rw [mul_assoc, added_zero_scale_identity Z a θ hZ0]
    _ ≤ 16384 * B ^ 2 * Z ^ (a - s + 2 * θ) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ (added_zero_exponent a s θ ha hs))
        (by positivity)

theorem idealAddedZero_nonzero_mask_dyad (S : Finset (Ideal O))
    (hS : ∀ I ∈ S, Supported I) (c : Ideal O → ℂ) (s : Ideal O) (hs : Squarefree s)
    (hmask : ∀ I ∈ S, ¬s ∣ I → c I = 0) (Z a s₀ θ : ℝ) (hZ : 1 < Z)
    (hNs : Z ^ s₀ ≤ (Ideal.absNorm s : ℝ))
    (hN : ∀ I ∈ S, (Ideal.absNorm I : ℝ) ≤ Z ^ (a + θ))
    (hz : idealAddedZero S hS c ≠ 0) : -θ ≤ a ∧ s₀ ≤ (a + θ) / 6 := by
  have hZ0 : 0 < Z := lt_trans zero_lt_one hZ
  obtain ⟨I, _, _⟩ := Finset.exists_ne_zero_of_sum_ne_zero hz
  have hY : 1 ≤ Z ^ (a + θ) :=
    (norm_one_le (hS I.val I.property).1).trans (hN I.val I.property)
  have ha : 0 ≤ a + θ := (Real.rpow_le_rpow_left_iff hZ).mp (by simpa only [Real.rpow_zero] using hY)
  have hm := idealAddedZero_nonzero_mask_norm S hS c s hs hmask (Z ^ (a + θ)) hN hz
  have hp : Z ^ (s₀ * (6 : ℕ)) ≤ Z ^ (a + θ) := by
    rw [Real.rpow_mul_natCast hZ0.le]
    exact (pow_le_pow_left₀ (Real.rpow_nonneg hZ0.le _) hNs 6).trans hm
  have hsp := (Real.rpow_le_rpow_left_iff hZ).mp hp
  constructor <;> norm_num at hsp ⊢ <;> linarith

theorem idealAddedZero_source_energy_of_mask (S : Finset (Ideal O))
    (hS : ∀ I ∈ S, Supported I) (c : Ideal O → ℂ) (s : Ideal O) (hs : Squarefree s)
    (hmask : ∀ I ∈ S, ¬s ∣ I → c I = 0) (B Z a s₀ θ : ℝ)
    (hB : 0 ≤ B) (hZ : 1 < Z) (hNs : Z ^ s₀ ≤ (Ideal.absNorm s : ℝ))
    (hc : ∀ I ∈ S, ‖c I‖ ≤ B)
    (hN : ∀ I ∈ S, (Ideal.absNorm I : ℝ) ≤ Z ^ (a + θ)) :
    ‖normalizedIdealAddedZero S hS c (Z ^ a)‖ ^ 2 ≤
      16384 * B ^ 2 * Z ^ (a - s₀ + 2 * θ) := by
  by_cases hz : idealAddedZero S hS c = 0
  · simp only [normalizedIdealAddedZero, hz, mul_zero, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow]
    exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (Real.rpow_nonneg (by linarith) _)
  · obtain ⟨ha, hss⟩ := idealAddedZero_nonzero_mask_dyad S hS c s hs hmask Z a s₀ θ hZ hNs hN hz
    exact idealAddedZero_source_energy S hS c B Z a s₀ θ hB hZ.le ha hss hc hN

theorem actual_tuple_gauss_eq_columns {r : ℕ} (S : Finset (Fin r → Ideal O))
    (hS : ∀ v ∈ S, Supported (tupleProduct v)) (β : (Fin r → Ideal O) → ℂ) :
    gaussPolynomial (Finset.univ : Finset S)
      (fun v => primaryIdealGenerator (tupleProduct v.val))
      (fun v => (supported_span_primaryIdealGenerator_iff (tupleProduct v.val)).mpr (hS v.val v.property))
      (fun v => β v.val) 0 =
    idealAddedZero (tupleColumns S) (tupleColumns_supported S hS) (tupleCoefficient S β) := by
  let g (I : Ideal O) : ℂ := if hI : Supported I then idealGaussRow I hI 0 else 0
  have hl : gaussPolynomial (Finset.univ : Finset S)
      (fun v => primaryIdealGenerator (tupleProduct v.val))
      (fun v => (supported_span_primaryIdealGenerator_iff (tupleProduct v.val)).mpr (hS v.val v.property))
      (fun v => β v.val) 0 = ∑ v ∈ S, β v * g (tupleProduct v) := by
    rw [← Finset.sum_coe_sort S (fun v => β v * g (tupleProduct v))]
    apply Finset.sum_congr rfl
    intro v hv
    simp only [g, dif_pos (hS v.val v.property), idealGaussRow]
  have hr : idealAddedZero (tupleColumns S) (tupleColumns_supported S hS) (tupleCoefficient S β) =
      ∑ I ∈ tupleColumns S, tupleCoefficient S β I * g I := by
    rw [← Finset.sum_coe_sort (tupleColumns S) (fun I => tupleCoefficient S β I * g I)]
    apply Finset.sum_congr rfl
    intro I hI
    simp only [g, dif_pos (tupleColumns_supported S hS I.val I.property)]
  rw [hl, hr]
  symm
  simp only [tupleCoefficient, Finset.sum_mul]
  calc
    (∑ I ∈ tupleColumns S, ∑ v ∈ S.filter (fun v => tupleProduct v = I), β v * g I) =
        ∑ I ∈ tupleColumns S, ∑ v ∈ S.filter (fun v => tupleProduct v = I), β v * g (tupleProduct v) := by
      apply Finset.sum_congr rfl
      intro I hI
      apply Finset.sum_congr rfl
      intro v hv
      rw [(Finset.mem_filter.mp hv).2]
    _ = ∑ v ∈ S, β v * g (tupleProduct v) :=
      Finset.sum_fiberwise_of_maps_to (fun v hv => Finset.mem_image.mpr ⟨v, hv, rfl⟩) _

end CenteredMomentAddedZero

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace CenteredMomentAddedZeroUniform
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentGaussEnergy CenteredMomentAddedZero CenteredMomentRectangle
local notation "O" => Eisenstein.O

theorem uniform_tuple_energy (N : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, n ≤ N →
      ∀ (S : Finset (Fin (n + 2) → Ideal O))
      (hS : ∀ v ∈ S, Supported (tupleProduct v))
      (β : (Fin (n + 2) → Ideal O) → ℂ) (B Y T : ℝ),
      0 ≤ B → 1 ≤ Y → 0 < T →
      (∀ v ∈ S, ‖β v‖ ≤ B) →
      (∀ v ∈ S, (Ideal.absNorm (tupleProduct v) : ℝ) ≤ Y) →
      ‖normalizedIdealAddedZero (tupleColumns S) (tupleColumns_supported S hS)
          (tupleCoefficient S β) T‖ ^ 2 ≤ C * B ^ 2 * T⁻¹ * Y ^ (4 / 3 + ε : ℝ) := by
  let D (n : ℕ) := (tuple_added_zero_energy (n + 2) (by omega) ε hε).choose
  have hD (n : ℕ) : 0 < D n := (tuple_added_zero_energy (n + 2) (by omega) ε hε).choose_spec.1
  have hne : (Finset.range (N + 1)).Nonempty := ⟨0, by simp⟩
  let C := 1 + (Finset.range (N + 1)).sup' hne D
  have hzero : D 0 ≤ (Finset.range (N + 1)).sup' hne D :=
    Finset.le_sup' D (by simp : 0 ∈ Finset.range (N + 1))
  refine ⟨C, by dsimp [C]; linarith [hD 0], ?_⟩
  intro n hn S hS β B Y T hB hY hT hβ hN
  have hDn : D n ≤ C := by
    have h := Finset.le_sup' D (Finset.mem_range.mpr (Nat.lt_succ_of_le hn))
    dsimp only [C]
    linarith
  have he := (tuple_added_zero_energy (n + 2) (by omega) ε hε).choose_spec.2
    S hS β B Y T hB hY hT hβ hN
  apply he.trans
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by linarith) _)
  apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr hT.le)
  exact mul_le_mul_of_nonneg_right hDn (sq_nonneg _)

abbrev Tuple (ι : Type*) := (ι ⊕ Fin 2) → Ideal O

def coordinateEquiv {ι : Type*} {n : ℕ} (e : ι ≃ Fin n) :
    ι ⊕ Fin 2 ≃ Fin (n + 2) := (e.sumCongr (Equiv.refl (Fin 2))).trans finSumFinEquiv

def tupleEquiv {ι : Type*} {n : ℕ} (e : ι ≃ Fin n) :
    Tuple ι ≃ (Fin (n + 2) → Ideal O) :=
  (coordinateEquiv e).arrowCongr (Equiv.refl (Ideal O))

def finiteTupleProduct {ι : Type*} [Fintype ι] (v : Tuple ι) : Ideal O := ∏ i, v i

lemma tupleEquiv_slot {ι : Type*} {n : ℕ} (e : ι ≃ Fin n) (v : Tuple ι) (i : ι) :
    tupleEquiv e v ((e i).castAdd 2) = v (Sum.inl i) := by
  change v ((coordinateEquiv e).symm _) = _
  have h : coordinateEquiv e (Sum.inl i) = (e i).castAdd 2 := by
    simp only [coordinateEquiv, Equiv.trans_apply, Equiv.sumCongr_apply,
      Sum.map_inl, finSumFinEquiv_apply_left]
  rw [← h, Equiv.symm_apply_apply]

lemma tupleEquiv_plain {ι : Type*} {n : ℕ} (e : ι ≃ Fin n) (v : Tuple ι) (j : Fin 2) :
    tupleEquiv e v (j.natAdd n) = v (Sum.inr j) := by
  change v ((coordinateEquiv e).symm _) = _
  have h : coordinateEquiv e (Sum.inr j) = j.natAdd n := by
    simp only [coordinateEquiv, Equiv.trans_apply, Equiv.sumCongr_apply,
      Sum.map_inr, finSumFinEquiv_apply_right, Equiv.refl_apply]
  rw [← h, Equiv.symm_apply_apply]

theorem tupleProduct_reindex {ι : Type*} [Fintype ι] {n : ℕ}
    (e : ι ≃ Fin n) (v : Tuple ι) :
    tupleProduct (tupleEquiv e v) = finiteTupleProduct v := by
  exact (coordinateEquiv e).symm.prod_comp v

def originalFiniteCoefficient {ι : Type*} [Fintype ι]
    (c : O) (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (R : Ideal O) (t : ℝ)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (b₁ b₂ s : Ideal O) (v : Tuple ι) : ℂ :=
  (∏ j, ν j (v (Sum.inl j)) * Wslot j ((Ideal.absNorm (v (Sum.inl j)) : ℝ) / P j)) *
    idealWeight c χ R t (finiteTupleProduct v) *
    idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ (b₁ * v (Sum.inr 0)) (b₂ * v (Sum.inr 1)) *
    (if s ∣ finiteTupleProduct v then 1 else 0)

theorem originalCoefficient_reindex {ι : Type*} [Fintype ι] {n : ℕ}
    (e : ι ≃ Fin n) (c : O) (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (R : Ideal O) (t : ℝ) (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (b₁ b₂ s : Ideal O) (v : Tuple ι) :
    originalCoefficient n c χ R t (fun j => ν (e.symm j)) (fun j => Wslot (e.symm j))
      (fun j => P (e.symm j)) W₁ W₂ X₁ X₂ Y₁ Y₂ b₁ b₂ s (tupleEquiv e v) =
    originalFiniteCoefficient c χ R t ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ b₁ b₂ s v := by
  have hslot (j : Fin n) : tupleEquiv e v (j.castAdd 2) = v (Sum.inl (e.symm j)) := by
    simpa only [Equiv.apply_symm_apply] using tupleEquiv_slot e v (e.symm j)
  have hp₀ : (⟨n, by omega⟩ : Fin (n + 2)) = (0 : Fin 2).natAdd n := by ext; simp
  have hp₁ : (⟨n + 1, by omega⟩ : Fin (n + 2)) = (1 : Fin 2).natAdd n := by ext; simp
  simp only [originalCoefficient, originalFiniteCoefficient, tupleProduct_reindex,
    hslot, hp₀, hp₁, tupleEquiv_plain]
  rw [e.symm.prod_comp (fun j => ν j (v (Sum.inl j)) * Wslot j ((Ideal.absNorm (v (Sum.inl j)) : ℝ) / P j))]

lemma reindex_supported {ι : Type*} [Fintype ι] {n : ℕ} (e : ι ≃ Fin n)
    (S : Finset (Tuple ι)) (hS : ∀ v ∈ S, Supported (finiteTupleProduct v)) :
    ∀ w ∈ S.image (tupleEquiv e), Supported (tupleProduct w) := by
  intro w hw
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
  rw [tupleProduct_reindex]
  exact hS v hv

def finiteGaussZero {ι : Type*} [Fintype ι] (S : Finset (Tuple ι))
    (hS : ∀ v ∈ S, Supported (finiteTupleProduct v)) (β : Tuple ι → ℂ) : ℂ :=
  gaussPolynomial (Finset.univ : Finset S)
    (fun v => primaryIdealGenerator (finiteTupleProduct v.val))
    (fun v => (supported_span_primaryIdealGenerator_iff (finiteTupleProduct v.val)).mpr (hS v.val v.property))
    (fun v => β v.val) 0

theorem finiteGaussZero_reindex {ι : Type*} [Fintype ι] {n : ℕ}
    (e : ι ≃ Fin n) (S : Finset (Tuple ι))
    (hS : ∀ v ∈ S, Supported (finiteTupleProduct v)) (β : Tuple ι → ℂ) :
    finiteGaussZero S hS β =
      idealAddedZero (tupleColumns (S.image (tupleEquiv e)))
        (tupleColumns_supported _ (reindex_supported e S hS))
        (tupleCoefficient (S.image (tupleEquiv e)) (fun w => β ((tupleEquiv e).symm w))) := by
  rw [← actual_tuple_gauss_eq_columns (S.image (tupleEquiv e)) (reindex_supported e S hS)
    (fun w => β ((tupleEquiv e).symm w))]
  unfold finiteGaussZero gaussPolynomial
  apply Finset.sum_bij (fun v _ => (⟨tupleEquiv e v.val,
    Finset.mem_image.mpr ⟨v.val, v.property, rfl⟩⟩ : S.image (tupleEquiv e)))
  · intros; exact Finset.mem_univ _
  · intro v hv w hw he
    apply Subtype.ext
    exact (tupleEquiv e).injective (congrArg Subtype.val he)
  · intro w hw
    obtain ⟨v, hv, he⟩ := Finset.mem_image.mp w.property
    exact ⟨⟨v, hv⟩, Finset.mem_univ _, Subtype.ext he⟩
  · intro v hv
    simp only [Equiv.symm_apply_apply, tupleProduct_reindex]

theorem uniform_finite_energy (N : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type*} [Fintype ι], Fintype.card ι ≤ N →
      ∀ (S : Finset (Tuple ι)) (hS : ∀ v ∈ S, Supported (finiteTupleProduct v))
      (β : Tuple ι → ℂ) (B Y T : ℝ), 0 ≤ B → 1 ≤ Y → 0 < T →
      (∀ v ∈ S, ‖β v‖ ≤ B) →
      (∀ v ∈ S, (Ideal.absNorm (finiteTupleProduct v) : ℝ) ≤ Y) →
      ‖(Real.sqrt T : ℂ)⁻¹ * finiteGaussZero S hS β‖ ^ 2 ≤
        C * B ^ 2 * T⁻¹ * Y ^ (4 / 3 + ε : ℝ) := by
  obtain ⟨C, hC, he⟩ := uniform_tuple_energy N ε hε
  refine ⟨C, hC, ?_⟩
  intro ι inst hn S hS β B Y T hB hY hT hβ hN
  let e := Fintype.equivFin ι
  rw [finiteGaussZero_reindex e S hS β]
  apply he (Fintype.card ι) hn _ (reindex_supported e S hS) _ B Y T hB hY hT
  · intro w hw
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
    simpa only [Equiv.symm_apply_apply] using hβ v hv
  · intro w hw
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
    simpa only [tupleProduct_reindex] using hN v hv

theorem originalFiniteCoefficient_norm_le {ι : Type*} [Fintype ι]
    (c : O) (hc : c ≠ 0) (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (R : Ideal O) (t : ℝ)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (b₁ b₂ s : Ideal O)
    (Bslot : ι → ℝ) (B₁ B₂ : ℝ) (hBslot : ∀ j, 0 ≤ Bslot j)
    (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hν : ∀ j I, ‖ν j I‖ ≤ 1) (hWslot : ∀ j x, ‖Wslot j x‖ ≤ Bslot j)
    (hW₁ : ∀ x, ‖W₁ x‖ ≤ B₁) (hW₂ : ∀ x, ‖W₂ x‖ ≤ B₂)
    (v : Tuple ι) (hv : finiteTupleProduct v ≠ 0) :
    ‖originalFiniteCoefficient c χ R t ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ b₁ b₂ s v‖ ≤
      (∏ j, Bslot j) * (2 * B₁ * B₂) := by
  let e := Fintype.equivFin ι
  rw [← originalCoefficient_reindex e]
  have he := originalCoefficient_norm_le (Fintype.card ι) c hc χ R t
    (fun j => ν (e.symm j)) (fun j => Wslot (e.symm j)) (fun j => P (e.symm j))
    W₁ W₂ X₁ X₂ Y₁ Y₂ b₁ b₂ s (fun j => Bslot (e.symm j)) B₁ B₂
    (fun j => hBslot _) hB₁ hB₂ (fun j I => hν _ I) (fun j x => hWslot _ x) hW₁ hW₂
    (tupleEquiv e v) (by rwa [tupleProduct_reindex])
  simpa only [e.symm.prod_comp Bslot] using he

theorem original_subset_energy {α : Type*} (A : Finset α) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (J : Finset α), J ⊆ A →
      ∀ (c : O), c ≠ 0 → ∀ (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
      (R : Ideal O) (t : ℝ) (ν : α → Ideal O → ℂ) (Wslot : α → ℝ → ℂ) (P : α → ℝ)
      (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (b₁ b₂ s : Ideal O)
      (Bslot : α → ℝ) (B₁ B₂ : ℝ),
      (∀ j ∈ J, 0 ≤ Bslot j) → 0 ≤ B₁ → 0 ≤ B₂ →
      (∀ j ∈ J, ∀ I, ‖ν j I‖ ≤ 1) → (∀ j ∈ J, ∀ x, ‖Wslot j x‖ ≤ Bslot j) →
      (∀ x, ‖W₁ x‖ ≤ B₁) → (∀ x, ‖W₂ x‖ ≤ B₂) →
      ∀ (S : Finset (Tuple J)) (hS : ∀ v ∈ S, Supported (finiteTupleProduct v))
      (Y T : ℝ), 1 ≤ Y → 0 < T →
      (∀ v ∈ S, (Ideal.absNorm (finiteTupleProduct v) : ℝ) ≤ Y) →
      ‖(Real.sqrt T : ℂ)⁻¹ * finiteGaussZero S hS
        (originalFiniteCoefficient c χ R t (fun j : J => ν j.val)
          (fun j : J => Wslot j.val) (fun j : J => P j.val)
          W₁ W₂ X₁ X₂ Y₁ Y₂ b₁ b₂ s)‖ ^ 2 ≤
        C * ((∏ j ∈ J, Bslot j) * (2 * B₁ * B₂)) ^ 2 * T⁻¹ * Y ^ (4 / 3 + ε : ℝ) := by
  obtain ⟨C, hC, he⟩ := uniform_finite_energy A.card ε hε
  refine ⟨C, hC, ?_⟩
  intro J hJA c hc χ R t ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ b₁ b₂ s Bslot B₁ B₂
    hBslot hB₁ hB₂ hν hWslot hW₁ hW₂ S hS Y T hY hT hN
  have hcard : Fintype.card J ≤ A.card := by
    simpa only [Fintype.card_coe] using Finset.card_le_card hJA
  apply he hcard S hS _ _ Y T
    (mul_nonneg (Finset.prod_nonneg hBslot) (by positivity)) hY hT _ hN
  intro v hv
  have hb := originalFiniteCoefficient_norm_le c hc χ R t
    (fun j : J => ν j.val) (fun j : J => Wslot j.val) (fun j : J => P j.val)
    W₁ W₂ X₁ X₂ Y₁ Y₂ b₁ b₂ s (fun j : J => Bslot j.val) B₁ B₂
    (fun j => hBslot j.val j.property) hB₁ hB₂
    (fun j I => hν j.val j.property I) (fun j x => hWslot j.val j.property x)
    hW₁ hW₂ v (hS v hv).1
  simpa only [Finset.prod_coe_sort J Bslot] using hb

theorem empty_finiteTupleProduct {α : Type*} (v : Tuple (∅ : Finset α)) :
    finiteTupleProduct v = v (Sum.inr 0) * v (Sum.inr 1) := by
  simp only [finiteTupleProduct, Fintype.prod_sum_type, Fin.prod_univ_two]
  have he : (∏ j : (∅ : Finset α), v (Sum.inl j)) = 1 := by
    apply Finset.prod_eq_one
    intro j hj
    exact False.elim (Finset.notMem_empty j.val j.property)
  rw [he, one_mul]

lemma reindexCoefficient_mask {ι : Type*} [Fintype ι] {n : ℕ}
    (e : ι ≃ Fin n) (S : Finset (Tuple ι)) (β : Tuple ι → ℂ) (s : Ideal O)
    (hmask : ∀ v ∈ S, ¬s ∣ finiteTupleProduct v → β v = 0)
    (I : Ideal O) (hs : ¬s ∣ I) :
    tupleCoefficient (S.image (tupleEquiv e)) (fun w => β ((tupleEquiv e).symm w)) I = 0 := by
  apply Finset.sum_eq_zero
  intro w hw
  obtain ⟨hwS, hwI⟩ := Finset.mem_filter.mp hw
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hwS
  simp only [Equiv.symm_apply_apply]
  apply hmask v hv
  rwa [← tupleProduct_reindex e v, hwI]

lemma reindexColumns_norm {ι : Type*} [Fintype ι] {n : ℕ}
    (e : ι ≃ Fin n) (S : Finset (Tuple ι)) (Y : ℝ)
    (hN : ∀ v ∈ S, (Ideal.absNorm (finiteTupleProduct v) : ℝ) ≤ Y) :
    ∀ I ∈ tupleColumns (S.image (tupleEquiv e)), (Ideal.absNorm I : ℝ) ≤ Y := by
  intro I hI
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hI
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
  simpa only [tupleProduct_reindex] using hN v hv

theorem finiteGaussZero_nonzero_mask_norm {ι : Type*} [Fintype ι]
    (S : Finset (Tuple ι)) (hS : ∀ v ∈ S, Supported (finiteTupleProduct v))
    (β : Tuple ι → ℂ) (s : Ideal O) (hs : Squarefree s)
    (hmask : ∀ v ∈ S, ¬s ∣ finiteTupleProduct v → β v = 0)
    (Y : ℝ) (hN : ∀ v ∈ S, (Ideal.absNorm (finiteTupleProduct v) : ℝ) ≤ Y)
    (hz : finiteGaussZero S hS β ≠ 0) : (Ideal.absNorm s : ℝ) ^ 6 ≤ Y := by
  let e := Fintype.equivFin ι
  rw [finiteGaussZero_reindex e S hS β] at hz
  exact idealAddedZero_nonzero_mask_norm _ _ _ s hs
    (fun I _ => reindexCoefficient_mask e S β s hmask I) Y (reindexColumns_norm e S Y hN) hz

theorem finiteGaussZero_nonzero_mask_dyad {ι : Type*} [Fintype ι]
    (S : Finset (Tuple ι)) (hS : ∀ v ∈ S, Supported (finiteTupleProduct v))
    (β : Tuple ι → ℂ) (s : Ideal O) (hs : Squarefree s)
    (hmask : ∀ v ∈ S, ¬s ∣ finiteTupleProduct v → β v = 0)
    (Z a s₀ θ : ℝ) (hZ : 1 < Z) (hNs : Z ^ s₀ ≤ (Ideal.absNorm s : ℝ))
    (hN : ∀ v ∈ S, (Ideal.absNorm (finiteTupleProduct v) : ℝ) ≤ Z ^ (a + θ))
    (hz : finiteGaussZero S hS β ≠ 0) : -θ ≤ a ∧ s₀ ≤ (a + θ) / 6 := by
  let e := Fintype.equivFin ι
  rw [finiteGaussZero_reindex e S hS β] at hz
  exact idealAddedZero_nonzero_mask_dyad _ _ _ s hs
    (fun I _ => reindexCoefficient_mask e S β s hmask I) Z a s₀ θ hZ hNs
    (reindexColumns_norm e S (Z ^ (a + θ)) hN) hz

lemma originalFiniteCoefficient_mask {ι : Type*} [Fintype ι]
    (c : O) (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (R : Ideal O) (t : ℝ)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (b₁ b₂ s : Ideal O)
    (v : Tuple ι) (hs : ¬s ∣ finiteTupleProduct v) :
    originalFiniteCoefficient c χ R t ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ b₁ b₂ s v = 0 := by
  simp only [originalFiniteCoefficient, hs, ite_false, mul_zero]

theorem uniform_finite_source_energy (N : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type*} [Fintype ι], Fintype.card ι ≤ N →
      ∀ (S : Finset (Tuple ι)) (hS : ∀ v ∈ S, Supported (finiteTupleProduct v))
      (β : Tuple ι → ℂ) (s : Ideal O), Squarefree s →
      (∀ v ∈ S, ¬s ∣ finiteTupleProduct v → β v = 0) →
      ∀ (B Z a s₀ θ : ℝ), 0 ≤ B → 1 < Z → Z ^ s₀ ≤ (Ideal.absNorm s : ℝ) →
      (∀ v ∈ S, ‖β v‖ ≤ B) →
      (∀ v ∈ S, (Ideal.absNorm (finiteTupleProduct v) : ℝ) ≤ Z ^ (a + θ)) →
      ‖(Real.sqrt (Z ^ a) : ℂ)⁻¹ * finiteGaussZero S hS β‖ ^ 2 ≤
        C * B ^ 2 * Z ^ (a - s₀ + 2 * θ + ε * (a + θ)) := by
  obtain ⟨C, hC, he⟩ := uniform_finite_energy N ε hε
  refine ⟨C, hC, ?_⟩
  intro ι inst hn S hS β s hs hmask B Z a s₀ θ hB hZ hNs hβ hN
  have hZ0 : 0 < Z := zero_lt_one.trans hZ
  by_cases hz : finiteGaussZero S hS β = 0
  · rw [hz, mul_zero, norm_zero, zero_pow (by decide : 2 ≠ 0)]
    exact mul_nonneg (mul_nonneg hC.le (sq_nonneg _)) (Real.rpow_nonneg hZ0.le _)
  · obtain ⟨ha, hss⟩ := finiteGaussZero_nonzero_mask_dyad S hS β s hs hmask Z a s₀ θ hZ hNs hN hz
    have hY : 1 ≤ Z ^ (a + θ) := Real.one_le_rpow hZ.le (by linarith)
    have hb := he hn S hS β B (Z ^ (a + θ)) (Z ^ a) hB hY
      (Real.rpow_pos_of_pos hZ0 _) hβ hN
    have hp : (Z ^ a)⁻¹ * (Z ^ (a + θ)) ^ (4 / 3 + ε : ℝ) =
        Z ^ (a / 3 + 4 * θ / 3 + ε * (a + θ)) := by
      rw [← Real.rpow_neg hZ0.le, ← Real.rpow_mul hZ0.le, ← Real.rpow_add hZ0]
      congr 1
      ring
    calc
      _ ≤ C * B ^ 2 * (Z ^ a)⁻¹ * (Z ^ (a + θ)) ^ (4 / 3 + ε : ℝ) := hb
      _ = C * B ^ 2 * Z ^ (a / 3 + 4 * θ / 3 + ε * (a + θ)) := by rw [mul_assoc, hp]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hZ.le
          (by linarith [added_zero_exponent a s₀ θ ha hss]))
        (mul_nonneg hC.le (sq_nonneg _))

theorem original_subset_source_energy {α : Type*} (A : Finset α) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (J : Finset α), J ⊆ A →
      ∀ (c : O), c ≠ 0 → ∀ (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
      (R : Ideal O) (t : ℝ) (ν : α → Ideal O → ℂ) (Wslot : α → ℝ → ℂ) (P : α → ℝ)
      (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (b₁ b₂ s : Ideal O), Squarefree s →
      ∀ (Bslot : α → ℝ) (B₁ B₂ : ℝ),
      (∀ j ∈ J, 0 ≤ Bslot j) → 0 ≤ B₁ → 0 ≤ B₂ →
      (∀ j ∈ J, ∀ I, ‖ν j I‖ ≤ 1) → (∀ j ∈ J, ∀ x, ‖Wslot j x‖ ≤ Bslot j) →
      (∀ x, ‖W₁ x‖ ≤ B₁) → (∀ x, ‖W₂ x‖ ≤ B₂) →
      ∀ (S : Finset (Tuple J)) (hS : ∀ v ∈ S, Supported (finiteTupleProduct v))
      (Z a s₀ θ : ℝ), 1 < Z → Z ^ s₀ ≤ (Ideal.absNorm s : ℝ) →
      (∀ v ∈ S, (Ideal.absNorm (finiteTupleProduct v) : ℝ) ≤ Z ^ (a + θ)) →
      ‖(Real.sqrt (Z ^ a) : ℂ)⁻¹ * finiteGaussZero S hS
        (originalFiniteCoefficient c χ R t (fun j : J => ν j.val)
          (fun j : J => Wslot j.val) (fun j : J => P j.val)
          W₁ W₂ X₁ X₂ Y₁ Y₂ b₁ b₂ s)‖ ^ 2 ≤
        C * ((∏ j ∈ J, Bslot j) * (2 * B₁ * B₂)) ^ 2 *
          Z ^ (a - s₀ + 2 * θ + ε * (a + θ)) := by
  obtain ⟨C, hC, he⟩ := uniform_finite_source_energy A.card ε hε
  refine ⟨C, hC, ?_⟩
  intro J hJA c hc χ R t ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ b₁ b₂ s hs Bslot B₁ B₂
    hBslot hB₁ hB₂ hν hWslot hW₁ hW₂ S hS Z a s₀ θ hZ hNs hN
  have hcard : Fintype.card J ≤ A.card := by
    simpa only [Fintype.card_coe] using Finset.card_le_card hJA
  apply he hcard S hS _ s hs
    (fun v _ => originalFiniteCoefficient_mask c χ R t
      (fun j : J => ν j.val) (fun j : J => Wslot j.val) (fun j : J => P j.val)
      W₁ W₂ X₁ X₂ Y₁ Y₂ b₁ b₂ s v)
    _ Z a s₀ θ (mul_nonneg (Finset.prod_nonneg hBslot) (by positivity)) hZ hNs _ hN
  intro v hv
  have hb := originalFiniteCoefficient_norm_le c hc χ R t
    (fun j : J => ν j.val) (fun j : J => Wslot j.val) (fun j : J => P j.val)
    W₁ W₂ X₁ X₂ Y₁ Y₂ b₁ b₂ s (fun j : J => Bslot j.val) B₁ B₂
    (fun j => hBslot j.val j.property) hB₁ hB₂
    (fun j I => hν j.val j.property I) (fun j x => hWslot j.val j.property x)
    hW₁ hW₂ v (hS v hv).1
  simpa only [Finset.prod_coe_sort J Bslot] using hb

end CenteredMomentAddedZeroUniform

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical ContDiff

namespace CenteredMomentSourceMass
open CenteredMomentAddedZero CenteredMomentRectangle CenteredMomentExtraction
local notation "O" => Eisenstein.O

def idealBall (H : ℝ) : Finset (Ideal O) :=
  (Ideal.finite_setOf_absNorm_le (S := O) (Nat.ceil H)).toFinset.filter
    (fun I => I ≠ 0 ∧ (Ideal.absNorm I : ℝ) ≤ H)

@[simp] theorem mem_idealBall (H : ℝ) (I : Ideal O) :
    I ∈ idealBall H ↔ I ≠ 0 ∧ (Ideal.absNorm I : ℝ) ≤ H := by
  constructor
  · exact fun h => (Finset.mem_filter.mp h).2
  · intro h
    refine Finset.mem_filter.mpr ⟨?_,h⟩
    apply (Ideal.finite_setOf_absNorm_le (S := O) (Nat.ceil H)).mem_toFinset.mpr
    exact_mod_cast h.2.trans (Nat.le_ceil H)

lemma idealBall_card (H : ℝ) (hH : 0 ≤ H) :
    ((idealBall H).card : ℝ) ≤ 128*H := by
  by_cases hs : (idealBall H).Nonempty
  · obtain ⟨I,hI⟩ := hs
    have hI := (mem_idealBall H I).mp hI
    have hn : (1:ℝ) ≤ Ideal.absNorm I := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI.1)
    exact EisensteinLatticeCount.finite_ideal_count_real _ H (hn.trans hI.2)
      (fun J hJ => ((mem_idealBall H J).mp hJ).1)
      (fun J hJ => ((mem_idealBall H J).mp hJ).2)
  · rw [Finset.not_nonempty_iff_eq_empty.mp hs]
    simp only [Finset.card_empty,Nat.cast_zero]
    positivity

def tupleBox {r : ℕ} (H : Fin r → ℝ) : Finset (Fin r → Ideal O) :=
  Fintype.piFinset (fun i => idealBall (H i))

@[simp] lemma mem_tupleBox {r : ℕ} (H : Fin r → ℝ) (v : Fin r → Ideal O) :
    v ∈ tupleBox H ↔ ∀ i, v i ≠ 0 ∧ (Ideal.absNorm (v i):ℝ) ≤ H i := by
  simp [tupleBox]

lemma tupleBox_card {r : ℕ} (H : Fin r → ℝ) (hH : ∀ i, 0 ≤ H i) :
    ((tupleBox H).card:ℝ) ≤ 128^r * ∏ i, H i := by
  simp only [tupleBox,Fintype.card_piFinset,Nat.cast_prod]
  calc
    (∏ i, ((idealBall (H i)).card:ℝ)) ≤ ∏ i, 128*H i :=
      Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _) (fun i _ => idealBall_card _ (hH i))
    _ = _ := by rw [Finset.prod_mul_distrib]; simp

def profileProduct {r : ℕ} (W : Fin r → ℝ → ℂ) (q : Fin r → ℝ)
    (v : Fin r → Ideal O) : ℂ := ∏ i, W i ((Ideal.absNorm (v i):ℝ)/q i)

lemma profileProduct_mem_box {r : ℕ} (W : Fin r → ℝ → ℂ) (b q : Fin r → ℝ)
    (hq : ∀ i, 0< q i) (hzero : ∀ i, W i 0=0)
    (hs : ∀ i x, W i x ≠ 0 → x ≤ b i)
    (v : Fin r → Ideal O) (hv : profileProduct W q v ≠ 0) :
    v ∈ tupleBox (fun i => b i*q i) := by
  apply (mem_tupleBox _ _).mpr
  intro i
  have hw : W i ((Ideal.absNorm (v i):ℝ)/q i) ≠ 0 :=
    (Finset.prod_ne_zero_iff.mp hv) i (Finset.mem_univ i)
  refine ⟨?_,(div_le_iff₀ (hq i)).mp (hs i _ hw)⟩
  intro hz
  apply hw
  simp only [hz,map_zero,Nat.cast_zero,zero_div,hzero]

lemma profileProduct_norm_le {r : ℕ} (W : Fin r → ℝ → ℂ) (q B : Fin r → ℝ)
    (hW : ∀ i x, ‖W i x‖ ≤ B i) (v : Fin r → Ideal O) :
    ‖profileProduct W q v‖ ≤ ∏ i, B i := by
  rw [profileProduct,norm_prod]
  exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun i _ => hW i _)

theorem profileProduct_mass {r : ℕ} (W : Fin r → ℝ → ℂ) (b q B : Fin r → ℝ)
    (hb : ∀ i, 0≤ b i) (hq : ∀ i, 0< q i) (hB : ∀ i, 0≤ B i)
    (hzero : ∀ i, W i 0=0) (hs : ∀ i x, W i x ≠ 0 → x≤ b i)
    (hW : ∀ i x, ‖W i x‖≤ B i) (S : Finset (Fin r → Ideal O)) :
    (∑ v ∈ S, ‖profileProduct W q v‖) ≤
      (∏ i, B i) * (128^r * ∏ i, b i*q i) := by
  let F := S.filter (fun v => profileProduct W q v ≠ 0)
  have hsum : (∑ v ∈ S, ‖profileProduct W q v‖) = ∑ v ∈ F, ‖profileProduct W q v‖ := by
    symm
    apply Finset.sum_filter_of_ne
    intro v _ hv
    exact norm_ne_zero_iff.mp hv
  have hsub : F ⊆ tupleBox (fun i => b i*q i) := by
    intro v hv
    exact profileProduct_mem_box W b q hq hzero hs v (Finset.mem_filter.mp hv).2
  have hcard : (F.card:ℝ) ≤ 128^r * ∏ i, b i*q i :=
    (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
      (tupleBox_card _ (fun i => mul_nonneg (hb i) (hq i).le))
  rw [hsum]
  calc
    _ ≤ ∑ _v ∈ F, ∏ i, B i := Finset.sum_le_sum (fun v _ => profileProduct_norm_le W q B hW v)
    _ = (F.card:ℝ)*(∏ i, B i) := by simp
    _ ≤ (128^r * ∏ i, b i*q i)*(∏ i, B i) :=
      mul_le_mul_of_nonneg_right hcard (Finset.prod_nonneg (fun i _ => hB i))
    _ = _ := by ring

def sourceProfiles {N : ℕ} (Wslot : Fin N → ℝ → ℂ) (W₁ W₂ : ℝ → ℂ) :
    Fin (N+2) → ℝ → ℂ := Fin.append Wslot ![W₁,W₂]

def sourceScales {N : ℕ} (P : Fin N → ℝ) (X₁ X₂ : ℝ) (B₁ B₂ : Ideal O) :
    Fin (N+2) → ℝ :=
  Fin.append P ![X₁/(Ideal.absNorm B₁:ℝ),X₂/(Ideal.absNorm B₂:ℝ)]

def sourceBounds {N : ℕ} (b : Fin N → ℝ) (b₁ b₂ : ℝ) : Fin (N+2) → ℝ :=
  Fin.append b ![b₁,b₂]

lemma sourceProfiles_product {N : ℕ} (Wslot : Fin N → ℝ → ℂ) (W₁ W₂ : ℝ → ℂ)
    (P : Fin N → ℝ) (X₁ X₂ : ℝ) (B₁ B₂ : Ideal O) (v : Fin (N+2) → Ideal O) :
    profileProduct (sourceProfiles Wslot W₁ W₂) (sourceScales P X₁ X₂ B₁ B₂) v =
      (∏ j : Fin N, Wslot j ((Ideal.absNorm (v (j.castAdd 2)):ℝ)/P j)) *
      (W₁ ((Ideal.absNorm (B₁*v ⟨N,by omega⟩):ℝ)/X₁) *
       W₂ ((Ideal.absNorm (B₂*v ⟨N+1,by omega⟩):ℝ)/X₂)) := by
  simp only [profileProduct,Fin.prod_univ_add,sourceProfiles,sourceScales,
    Fin.append_left,Fin.append_right,Fin.prod_univ_two,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_fin_one,map_mul,Nat.cast_mul,div_div_eq_mul_div]
  have h₀ : Fin.natAdd N (0:Fin 2)=⟨N,by omega⟩ := by ext; simp
  have h₁ : Fin.natAdd N (1:Fin 2)=⟨N+1,by omega⟩ := by ext; simp
  rw [h₀,h₁]
  congr 2 <;> congr 1 <;> ring

lemma sourceBounds_product {N : ℕ} (b : Fin N → ℝ) (b₁ b₂ : ℝ) :
    (∏ i, sourceBounds b b₁ b₂ i) = (∏ j,b j)*b₁*b₂ := by
  simp only [sourceBounds,Fin.prod_univ_add,Fin.append_left,Fin.append_right,
    Fin.prod_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
  ring

lemma sourceScales_product {N : ℕ} (P : Fin N → ℝ) (X₁ X₂ : ℝ) (B₁ B₂ : Ideal O) :
    (∏ i, sourceScales P X₁ X₂ B₁ B₂ i) =
      (∏ j,P j)*(X₁*X₂)/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂) := by
  simp only [sourceScales,Fin.prod_univ_add,Fin.append_left,Fin.append_right,
    Fin.prod_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
  ring

lemma sourceBounds_nonneg {N : ℕ} (b : Fin N → ℝ) (b₁ b₂ : ℝ)
    (hb : ∀ j, 0≤ b j) (hb₁ : 0≤ b₁) (hb₂ : 0≤ b₂) :
    ∀ i, 0≤ sourceBounds b b₁ b₂ i := by
  simp only [Fin.forall_fin_add,sourceBounds,Fin.append_left,Fin.append_right,Fin.forall_fin_two]
  exact ⟨hb,hb₁,hb₂⟩

lemma sourceScales_pos {N : ℕ} (P : Fin N → ℝ) (X₁ X₂ : ℝ) (B₁ B₂ : Ideal O)
    (hP : ∀ j, 0< P j) (hX₁ : 0< X₁) (hX₂ : 0< X₂) (hB₁ : B₁≠0) (hB₂ : B₂≠0) :
    ∀ i, 0< sourceScales P X₁ X₂ B₁ B₂ i := by
  have hn₁ : (0:ℝ)< Ideal.absNorm B₁ := by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hB₁)
  have hn₂ : (0:ℝ)< Ideal.absNorm B₂ := by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hB₂)
  simp only [Fin.forall_fin_add,sourceScales,Fin.append_left,Fin.append_right,Fin.forall_fin_two]
  exact ⟨hP,div_pos hX₁ hn₁,div_pos hX₂ hn₂⟩

theorem originalCoefficient_factor (N : ℕ) (c : O) (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (R : Ideal O) (t : ℝ) (ν : Fin N → Ideal O → ℂ)
    (Wslot : Fin N → ℝ → ℂ) (P : Fin N → ℝ) (W₁ W₂ : ℝ → ℂ)
    (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ s : Ideal O) (v : Fin (N+2) → Ideal O) :
    originalCoefficient N c χ R t ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v =
      (∏ j,ν j (v (j.castAdd 2))) * idealWeight c χ R t (tupleProduct v) *
      (profileProduct (sourceProfiles Wslot W₁ W₂) (sourceScales P X₁ X₂ B₁ B₂) v -
       profileProduct (sourceProfiles Wslot W₁ W₂) (sourceScales P Y₁ Y₂ B₁ B₂) v) *
      (if s∣tupleProduct v then 1 else 0) := by
  rw [originalCoefficient,Finset.prod_mul_distrib,sourceProfiles_product,sourceProfiles_product]
  unfold idealRectangle
  ring

def sourcePool {N : ℕ} (ν : Fin N → Ideal O → ℂ) (b P : Fin N → ℝ)
    (b₁ b₂ X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O) : Finset (Fin (N+2) → Ideal O) :=
  ((tupleBox (fun i => sourceBounds b b₁ b₂ i*sourceScales P X₁ X₂ B₁ B₂ i)) ∪
    tupleBox (fun i => sourceBounds b b₁ b₂ i*sourceScales P Y₁ Y₂ B₁ B₂ i)).filter
      (fun v => ∀ j,ν j (v (j.castAdd 2)) ≠ 0)

lemma sourcePool_slot {N : ℕ} (ν : Fin N → Ideal O → ℂ) (b P : Fin N → ℝ)
    (b₁ b₂ X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O) (v : Fin (N+2) → Ideal O)
    (hv : v ∈ sourcePool ν b P b₁ b₂ X₁ X₂ Y₁ Y₂ B₁ B₂) (j : Fin N) :
    ν j (v (j.castAdd 2)) ≠ 0 := (Finset.mem_filter.mp hv).2 j

lemma sourcePool_nonzero {N : ℕ} (ν : Fin N → Ideal O → ℂ) (b P : Fin N → ℝ)
    (b₁ b₂ X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O) (v : Fin (N+2) → Ideal O)
    (hv : v ∈ sourcePool ν b P b₁ b₂ X₁ X₂ Y₁ Y₂ B₁ B₂) : tupleProduct v ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  rcases Finset.mem_union.mp (Finset.mem_filter.mp hv).1 with h|h <;>
    exact ((mem_tupleBox _ _).mp h i).1

theorem originalCoefficient_mem_sourcePool (N : ℕ) (c : O)
    (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (R : Ideal O) (t : ℝ)
    (ν : Fin N → Ideal O → ℂ) (Wslot : Fin N → ℝ → ℂ) (P b : Fin N → ℝ)
    (W₁ W₂ : ℝ → ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ s : Ideal O)
    (hP : ∀ j, 0< P j) (hX₁ : 0< X₁) (hX₂ : 0< X₂) (hY₁ : 0< Y₁) (hY₂ : 0< Y₂)
    (hB₁ : B₁≠0) (hB₂ : B₂≠0)
    (hzero : ∀ i, sourceProfiles Wslot W₁ W₂ i 0=0)
    (hs : ∀ i x, sourceProfiles Wslot W₁ W₂ i x≠0 → x≤ sourceBounds b b₁ b₂ i)
    (v : Fin (N+2) → Ideal O)
    (hv : originalCoefficient N c χ R t ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v ≠ 0) :
    v ∈ sourcePool ν b P b₁ b₂ X₁ X₂ Y₁ Y₂ B₁ B₂ := by
  rw [originalCoefficient_factor] at hv
  have hslots := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hv).1).1).1
  have hd := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hv).1).2
  apply Finset.mem_filter.mpr
  refine ⟨?_,fun j => (Finset.prod_ne_zero_iff.mp hslots) j (Finset.mem_univ j)⟩
  apply Finset.mem_union.mpr
  by_cases hx : profileProduct (sourceProfiles Wslot W₁ W₂) (sourceScales P X₁ X₂ B₁ B₂) v = 0
  · apply Or.inr
    have hy : profileProduct (sourceProfiles Wslot W₁ W₂) (sourceScales P Y₁ Y₂ B₁ B₂) v ≠ 0 := by
      intro hy; exact hd (by rw [hx,hy,sub_self])
    exact profileProduct_mem_box _ _ _ (sourceScales_pos _ _ _ _ _ hP hY₁ hY₂ hB₁ hB₂) hzero hs v hy
  · exact Or.inl (profileProduct_mem_box _ _ _ (sourceScales_pos _ _ _ _ _ hP hX₁ hX₂ hB₁ hB₂) hzero hs v hx)

def sourceRadius {N : ℕ} (b P : Fin N → ℝ) (b₁ b₂ T : ℝ) (B₁ B₂ : Ideal O) : ℝ :=
  (∏ j,b j)*b₁*b₂*(T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j,P j)

lemma source_coordinate_product {N : ℕ} (b P : Fin N → ℝ)
    (b₁ b₂ X₁ X₂ T : ℝ) (B₁ B₂ : Ideal O) (hT : X₁*X₂=T) :
    (∏ i,sourceBounds b b₁ b₂ i*sourceScales P X₁ X₂ B₁ B₂ i) =
      sourceRadius b P b₁ b₂ T B₁ B₂ := by
  rw [Finset.prod_mul_distrib,sourceBounds_product,sourceScales_product,hT]
  unfold sourceRadius
  ring

lemma tupleBox_product_bound {r : ℕ} (H : Fin r → ℝ) (v : Fin r → Ideal O)
    (hv : v ∈ tupleBox H) : (Ideal.absNorm (tupleProduct v):ℝ) ≤ ∏ i,H i := by
  simp only [tupleProduct,map_prod,Nat.cast_prod]
  exact Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _)
    (fun i _ => ((mem_tupleBox H v).mp hv i).2)

theorem sourcePool_product_bound {N : ℕ} (ν : Fin N → Ideal O → ℂ) (b P : Fin N → ℝ)
    (b₁ b₂ X₁ X₂ Y₁ Y₂ T : ℝ) (B₁ B₂ : Ideal O)
    (hX : X₁*X₂=T) (hY : Y₁*Y₂=T) (v : Fin (N+2) → Ideal O)
    (hv : v ∈ sourcePool ν b P b₁ b₂ X₁ X₂ Y₁ Y₂ B₁ B₂) :
    (Ideal.absNorm (tupleProduct v):ℝ) ≤ sourceRadius b P b₁ b₂ T B₁ B₂ := by
  rcases Finset.mem_union.mp (Finset.mem_filter.mp hv).1 with hx|hy
  · exact (tupleBox_product_bound _ v hx).trans_eq (source_coordinate_product b P b₁ b₂ X₁ X₂ T B₁ B₂ hX)
  · exact (tupleBox_product_bound _ v hy).trans_eq (source_coordinate_product b P b₁ b₂ Y₁ Y₂ T B₁ B₂ hY)

theorem originalCoefficient_profile_norm_le (N : ℕ) (c : O) (hc : c≠0)
    (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (R : Ideal O) (t : ℝ)
    (ν : Fin N → Ideal O → ℂ) (hν : ∀ j I, ‖ν j I‖≤1)
    (Wslot : Fin N → ℝ → ℂ) (P : Fin N → ℝ) (W₁ W₂ : ℝ → ℂ)
    (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ s : Ideal O) (v : Fin (N+2) → Ideal O)
    (hv : tupleProduct v≠0) :
    ‖originalCoefficient N c χ R t ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v‖ ≤
      ‖profileProduct (sourceProfiles Wslot W₁ W₂) (sourceScales P X₁ X₂ B₁ B₂) v‖+
      ‖profileProduct (sourceProfiles Wslot W₁ W₂) (sourceScales P Y₁ Y₂ B₁ B₂) v‖ := by
  have hn : ‖∏ j,ν j (v (j.castAdd 2))‖≤1 := by
    rw [norm_prod]
    exact Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun j _ => hν j _)
  have hw := idealWeight_norm_le_one c hc χ R t (tupleProduct v) hv
  rw [originalCoefficient_factor,norm_mul,norm_mul,norm_mul]
  have hm : ‖(if s∣tupleProduct v then 1 else 0 : ℂ)‖≤1 := by split_ifs <;> norm_num
  have hnw : ‖∏ j,ν j (v (j.castAdd 2))‖*‖idealWeight c χ R t (tupleProduct v)‖≤1 := by
    simpa only [one_mul] using mul_le_mul hn hw (norm_nonneg _) zero_le_one
  calc
    _ ≤ (1*‖profileProduct (sourceProfiles Wslot W₁ W₂) (sourceScales P X₁ X₂ B₁ B₂) v-
        profileProduct (sourceProfiles Wslot W₁ W₂) (sourceScales P Y₁ Y₂ B₁ B₂) v‖)*1 :=
      mul_le_mul (mul_le_mul_of_nonneg_right hnw (norm_nonneg _)) hm (norm_nonneg _) (by positivity)
    _ ≤ _ := by
      simpa only [one_mul,mul_one] using norm_sub_le
        (profileProduct (sourceProfiles Wslot W₁ W₂) (sourceScales P X₁ X₂ B₁ B₂) v)
        (profileProduct (sourceProfiles Wslot W₁ W₂) (sourceScales P Y₁ Y₂ B₁ B₂) v)

def sourceMassConstant {N : ℕ} (b D : Fin N → ℝ) (b₁ b₂ D₁ D₂ : ℝ) : ℝ :=
  2*128^(N+2)*(∏ j,D j)*D₁*D₂*(∏ j,b j)*b₁*b₂

theorem originalCoefficient_mass (N : ℕ) (c : O) (hc : c≠0)
    (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (R : Ideal O) (t : ℝ)
    (ν : Fin N → Ideal O → ℂ) (hν : ∀ j I, ‖ν j I‖≤1)
    (Wslot : Fin N → ℝ → ℂ) (P b D : Fin N → ℝ) (W₁ W₂ : ℝ → ℂ)
    (b₁ b₂ D₁ D₂ X₁ X₂ Y₁ Y₂ T : ℝ) (B₁ B₂ s : Ideal O)
    (hb : ∀ j, 0≤ b j) (hb₁ : 0≤ b₁) (hb₂ : 0≤ b₂)
    (hD : ∀ j, 0≤ D j) (hD₁ : 0≤ D₁) (hD₂ : 0≤ D₂)
    (hP : ∀ j, 0< P j) (hX₁ : 0< X₁) (hX₂ : 0< X₂) (hY₁ : 0< Y₁) (hY₂ : 0< Y₂)
    (hB₁ : B₁≠0) (hB₂ : B₂≠0) (hX : X₁*X₂=T) (hY : Y₁*Y₂=T)
    (hzero : ∀ i, sourceProfiles Wslot W₁ W₂ i 0=0)
    (hs : ∀ i x, sourceProfiles Wslot W₁ W₂ i x≠0 → x≤ sourceBounds b b₁ b₂ i)
    (hW : ∀ i x, ‖sourceProfiles Wslot W₁ W₂ i x‖≤ sourceBounds D D₁ D₂ i)
    (S : Finset (Fin (N+2) → Ideal O)) :
    (∑ v ∈ S, ‖originalCoefficient N c χ R t ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v‖) ≤
      sourceMassConstant b D b₁ b₂ D₁ D₂ *
        (T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j,P j) := by
  have hpoint (v : Fin (N+2) → Ideal O) :
      ‖originalCoefficient N c χ R t ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v‖ ≤
        ‖profileProduct (sourceProfiles Wslot W₁ W₂) (sourceScales P X₁ X₂ B₁ B₂) v‖+
        ‖profileProduct (sourceProfiles Wslot W₁ W₂) (sourceScales P Y₁ Y₂ B₁ B₂) v‖ := by
    by_cases hv : originalCoefficient N c χ R t ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v=0
    · rw [hv,norm_zero]; positivity
    · have hm := originalCoefficient_mem_sourcePool N c χ R t ν Wslot P b W₁ W₂ b₁ b₂
        X₁ X₂ Y₁ Y₂ B₁ B₂ s hP hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hzero hs v hv
      exact originalCoefficient_profile_norm_le N c hc χ R t ν hν Wslot P W₁ W₂
        X₁ X₂ Y₁ Y₂ B₁ B₂ s v (sourcePool_nonzero _ _ _ _ _ _ _ _ _ _ _ v hm)
  have hx := profileProduct_mass (sourceProfiles Wslot W₁ W₂) (sourceBounds b b₁ b₂)
    (sourceScales P X₁ X₂ B₁ B₂) (sourceBounds D D₁ D₂)
    (sourceBounds_nonneg b b₁ b₂ hb hb₁ hb₂) (sourceScales_pos _ _ _ _ _ hP hX₁ hX₂ hB₁ hB₂)
    (sourceBounds_nonneg D D₁ D₂ hD hD₁ hD₂) hzero hs hW S
  have hy := profileProduct_mass (sourceProfiles Wslot W₁ W₂) (sourceBounds b b₁ b₂)
    (sourceScales P Y₁ Y₂ B₁ B₂) (sourceBounds D D₁ D₂)
    (sourceBounds_nonneg b b₁ b₂ hb hb₁ hb₂) (sourceScales_pos _ _ _ _ _ hP hY₁ hY₂ hB₁ hB₂)
    (sourceBounds_nonneg D D₁ D₂ hD hD₁ hD₂) hzero hs hW S
  rw [source_coordinate_product b P b₁ b₂ X₁ X₂ T B₁ B₂ hX,sourceBounds_product] at hx
  rw [source_coordinate_product b P b₁ b₂ Y₁ Y₂ T B₁ B₂ hY,sourceBounds_product] at hy
  calc
    _ ≤ ∑ v ∈ S, (‖profileProduct (sourceProfiles Wslot W₁ W₂) (sourceScales P X₁ X₂ B₁ B₂) v‖+
        ‖profileProduct (sourceProfiles Wslot W₁ W₂) (sourceScales P Y₁ Y₂ B₁ B₂) v‖) :=
      Finset.sum_le_sum (fun v _ => hpoint v)
    _ ≤ _ := by
      rw [Finset.sum_add_distrib]
      exact (add_le_add hx hy).trans_eq (by unfold sourceRadius sourceMassConstant; ring)

theorem sourcePool_original_slots {N : ℕ} (ν : Fin N → Ideal O → ℂ)
    (pool : Fin N → Finset (Ideal O)) (hpool : ∀ j I, I∉pool j → ν j I=0)
    (b P : Fin N → ℝ) (b₁ b₂ X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O)
    (v : Fin (N+2) → Ideal O) (hv : v∈sourcePool ν b P b₁ b₂ X₁ X₂ Y₁ Y₂ B₁ B₂) :
    ∀ j, v (j.castAdd 2)∈pool j := by
  intro j
  by_contra h
  exact sourcePool_slot _ _ _ _ _ _ _ _ _ _ _ v hv j (hpool j _ h)

theorem tuple_weighted_regroup {r : ℕ} (S : Finset (Fin r → Ideal O))
    (β : (Fin r → Ideal O) → ℂ) (F : Ideal O → ℂ) :
    (∑ v ∈ S, β v*F (tupleProduct v)) =
      ∑ I ∈ tupleColumns S, tupleCoefficient S β I*F I := by
  symm
  simp only [tupleCoefficient,Finset.sum_mul]
  calc
    _ = ∑ I ∈ tupleColumns S, ∑ v ∈ S.filter (fun v => tupleProduct v=I), β v*F (tupleProduct v) := by
      apply Finset.sum_congr rfl
      intro I hI
      apply Finset.sum_congr rfl
      intro v hv
      rw [(Finset.mem_filter.mp hv).2]
    _ = _ := Finset.sum_fiberwise_of_maps_to (fun v hv => Finset.mem_image.mpr ⟨v,hv,rfl⟩) _

theorem tupleCoefficient_mass {r : ℕ} (S : Finset (Fin r → Ideal O))
    (β : (Fin r → Ideal O) → ℂ) :
    (∑ I ∈ tupleColumns S, ‖tupleCoefficient S β I‖) ≤ ∑ v ∈ S, ‖β v‖ := by
  calc
    _ ≤ ∑ I ∈ tupleColumns S, ∑ v ∈ S.filter (fun v => tupleProduct v=I), ‖β v‖ :=
      Finset.sum_le_sum (fun I _ => norm_sum_le _ _)
    _ = _ := Finset.sum_fiberwise_of_maps_to (fun v hv => Finset.mem_image.mpr ⟨v,hv,rfl⟩) _

lemma tupleCoefficient_eq_zero_outside {r : ℕ} (S : Finset (Fin r → Ideal O))
    (β : (Fin r → Ideal O) → ℂ) (I : Ideal O) (hI : I∉tupleColumns S) :
    tupleCoefficient S β I=0 := by
  apply Finset.sum_eq_zero
  intro v hv
  exact False.elim (hI (Finset.mem_image.mpr ⟨v,(Finset.mem_filter.mp hv).1,(Finset.mem_filter.mp hv).2⟩))

theorem source_column_support {N : ℕ} (ν : Fin N → Ideal O → ℂ) (b P : Fin N → ℝ)
    (b₁ b₂ X₁ X₂ Y₁ Y₂ T : ℝ) (B₁ B₂ : Ideal O)
    (hX : X₁*X₂=T) (hY : Y₁*Y₂=T)
    (β : (Fin (N+2) → Ideal O) → ℂ) (I : Ideal O)
    (hI : tupleCoefficient (sourcePool ν b P b₁ b₂ X₁ X₂ Y₁ Y₂ B₁ B₂) β I ≠ 0) :
    I≠0 ∧ (Ideal.absNorm I:ℝ)≤ sourceRadius b P b₁ b₂ T B₁ B₂ := by
  have hm : I∈tupleColumns (sourcePool ν b P b₁ b₂ X₁ X₂ Y₁ Y₂ B₁ B₂) := by
    by_contra h; exact hI (tupleCoefficient_eq_zero_outside _ _ _ h)
  obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hm
  exact ⟨sourcePool_nonzero _ _ _ _ _ _ _ _ _ _ _ v hv,
    sourcePool_product_bound _ _ _ _ _ _ _ _ _ _ _ _ hX hY v hv⟩

theorem original_source_eq_columns (N : ℕ) (c : O)
    (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (R : Ideal O) (t : ℝ)
    (ν : Fin N → Ideal O → ℂ) (Wslot : Fin N → ℝ → ℂ) (P b : Fin N → ℝ)
    (W₁ W₂ : ℝ → ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ s : Ideal O)
    (hP : ∀ j, 0< P j) (hX₁ : 0< X₁) (hX₂ : 0< X₂) (hY₁ : 0< Y₁) (hY₂ : 0< Y₂)
    (hB₁ : B₁≠0) (hB₂ : B₂≠0)
    (hzero : ∀ i, sourceProfiles Wslot W₁ W₂ i 0=0)
    (hs : ∀ i x, sourceProfiles Wslot W₁ W₂ i x≠0 → x≤ sourceBounds b b₁ b₂ i)
    (F : Ideal O → ℂ) :
    (∑' v : Fin (N+2) → Ideal O,
      originalCoefficient N c χ R t ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v * F (tupleProduct v)) =
    ∑ I ∈ tupleColumns (sourcePool ν b P b₁ b₂ X₁ X₂ Y₁ Y₂ B₁ B₂),
      tupleCoefficient (sourcePool ν b P b₁ b₂ X₁ X₂ Y₁ Y₂ B₁ B₂)
        (originalCoefficient N c χ R t ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s) I * F I := by
  rw [← tuple_weighted_regroup]
  apply tsum_eq_sum
  intro v hv
  have hz : originalCoefficient N c χ R t ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v = 0 := by
    by_contra hn
    exact hv (originalCoefficient_mem_sourcePool N c χ R t ν Wslot P b W₁ W₂ b₁ b₂
      X₁ X₂ Y₁ Y₂ B₁ B₂ s hP hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hzero hs v hn)
  rw [hz,zero_mul]

lemma smooth_annular_bound (W : ℝ → ℂ) (a b : ℝ) (ha : 0< a)
    (hs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W) :
    ∃ D : ℝ, 0≤ D ∧ (∀ x, ‖W x‖≤ D) ∧ W 0=0 ∧ (∀ x, W x≠0 → x≤ b) := by
  let D := SchwartzMap.seminorm ℝ 0 0 (CenteredMomentLattice.normPowerProfile W a b ha hs hW 0)
  refine ⟨D,apply_nonneg _ _,?_,?_,?_⟩
  · intro x
    rw [← CenteredMomentTwist.normPowerProfile_norm W a b ha hs hW 0 x]
    exact SchwartzMap.norm_le_seminorm ℝ _ _
  · by_contra hz
    have h := (hs hz).1
    linarith
  · intro x hx
    exact (hs hx).2

theorem smooth_source_mass_uniform (N : ℕ)
    (Wslot : Fin N → ℝ → ℂ) (W₁ W₂ : ℝ → ℂ)
    (a b : Fin N → ℝ) (a₁ b₁ a₂ b₂ : ℝ)
    (ha : ∀ j, 0< a j) (hb : ∀ j, 0≤ b j)
    (ha₁ : 0< a₁) (hb₁ : 0≤ b₁) (ha₂ : 0< a₂) (hb₂ : 0≤ b₂)
    (hsSlot : ∀ j, Function.support (Wslot j)⊆Set.Icc (a j) (b j))
    (hs₁ : Function.support W₁⊆Set.Icc a₁ b₁) (hs₂ : Function.support W₂⊆Set.Icc a₂ b₂)
    (hWslot : ∀ j, ContDiff ℝ ∞ (Wslot j)) (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂) :
    ∃ C : ℝ, 0< C ∧ ∀ (c : O), c≠0 → ∀ (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
      (R : Ideal O) (t : ℝ) (ν : Fin N → Ideal O → ℂ), (∀ j I, ‖ν j I‖≤1) →
      ∀ (P : Fin N → ℝ) (X₁ X₂ Y₁ Y₂ T : ℝ) (B₁ B₂ s : Ideal O),
      (∀ j, 0< P j) → 0< X₁ → 0< X₂ → 0< Y₁ → 0< Y₂ → B₁≠0 → B₂≠0 →
      X₁*X₂=T → Y₁*Y₂=T → ∀ S : Finset (Fin (N+2) → Ideal O),
      (∑ v ∈ S, ‖originalCoefficient N c χ R t ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v‖) ≤
        C*(T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j,P j) ∧
      (∑ I ∈ tupleColumns S, ‖tupleCoefficient S
        (originalCoefficient N c χ R t ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s) I‖) ≤
        C*(T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j,P j) := by
  choose D hD hDbound hDzero hDsupport using
    fun j => smooth_annular_bound (Wslot j) (a j) (b j) (ha j) (hsSlot j) (hWslot j)
  obtain ⟨D₁,hD₁,hDbound₁,hzero₁,hsupport₁⟩ := smooth_annular_bound W₁ a₁ b₁ ha₁ hs₁ hW₁
  obtain ⟨D₂,hD₂,hDbound₂,hzero₂,hsupport₂⟩ := smooth_annular_bound W₂ a₂ b₂ ha₂ hs₂ hW₂
  have hzero : ∀ i, sourceProfiles Wslot W₁ W₂ i 0=0 := by
    simpa only [Fin.forall_fin_add,sourceProfiles,Fin.append_left,Fin.append_right,Fin.forall_fin_two,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
      using And.intro hDzero (And.intro hzero₁ hzero₂)
  have hs : ∀ i x, sourceProfiles Wslot W₁ W₂ i x≠0 → x≤ sourceBounds b b₁ b₂ i := by
    simpa only [Fin.forall_fin_add,sourceProfiles,sourceBounds,Fin.append_left,Fin.append_right,Fin.forall_fin_two,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
      using And.intro hDsupport (And.intro hsupport₁ hsupport₂)
  have hbound : ∀ i x, ‖sourceProfiles Wslot W₁ W₂ i x‖≤ sourceBounds D D₁ D₂ i := by
    simpa only [Fin.forall_fin_add,sourceProfiles,sourceBounds,Fin.append_left,Fin.append_right,Fin.forall_fin_two,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
      using And.intro hDbound (And.intro hDbound₁ hDbound₂)
  let C₀ := sourceMassConstant b D b₁ b₂ D₁ D₂
  have hprodD : 0≤∏ j,D j := Finset.prod_nonneg (fun j _ => hD j)
  have hprodb : 0≤∏ j,b j := Finset.prod_nonneg (fun j _ => hb j)
  have hC₀ : 0≤ C₀ := by
    dsimp only [C₀,sourceMassConstant]
    positivity
  refine ⟨1+C₀,by positivity,?_⟩
  intro c hc χ R t ν hν P X₁ X₂ Y₁ Y₂ T B₁ B₂ s hP hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hX hY S
  have hm := originalCoefficient_mass N c hc χ R t ν hν Wslot P b D W₁ W₂
    b₁ b₂ D₁ D₂ X₁ X₂ Y₁ Y₂ T B₁ B₂ s hb hb₁ hb₂ hD hD₁ hD₂
    hP hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hX hY hzero hs hbound S
  have hT : 0< T := hX ▸ mul_pos hX₁ hX₂
  have hprodP : 0≤∏ j,P j := Finset.prod_nonneg (fun j _ => (hP j).le)
  have hraw : 0≤(T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j,P j) := by positivity
  have hbigger : C₀*(T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j,P j) ≤
      (1+C₀)*(T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j,P j) := by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (by linarith : C₀≤1+C₀) hraw
  have hmass := hm.trans hbigger
  exact ⟨hmass,(tupleCoefficient_mass S _).trans hmass⟩

theorem originalCoefficient_original_masks (N : ℕ) (c : O)
    (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (R : Ideal O) (t : ℝ)
    (ν : Fin N → Ideal O → ℂ) (Wslot : Fin N → ℝ → ℂ) (P : Fin N → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ s : Ideal O) (v : Fin (N+2) → Ideal O)
    (hv : originalCoefficient N c χ R t ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v≠0) :
    IsCoprime (tupleProduct v) R ∧ s∣tupleProduct v ∧ ∀ j, ν j (v (j.castAdd 2))≠0 := by
  refine ⟨?_,?_,?_⟩
  · by_contra h
    apply hv
    simp only [originalCoefficient,idealWeight,h,ite_false,zero_mul,mul_zero]
  · by_contra h
    apply hv
    simp only [originalCoefficient,h,ite_false,mul_zero]
  · rw [originalCoefficient_factor] at hv
    have hslots := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hv).1).1).1
    exact fun j => (Finset.prod_ne_zero_iff.mp hslots) j (Finset.mem_univ j)

theorem originalCoefficient_product_bound (N : ℕ) (c : O)
    (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (R : Ideal O) (t : ℝ)
    (ν : Fin N → Ideal O → ℂ) (Wslot : Fin N → ℝ → ℂ) (P b : Fin N → ℝ)
    (W₁ W₂ : ℝ → ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ T : ℝ) (B₁ B₂ s : Ideal O)
    (hP : ∀ j, 0< P j) (hX₁ : 0< X₁) (hX₂ : 0< X₂) (hY₁ : 0< Y₁) (hY₂ : 0< Y₂)
    (hB₁ : B₁≠0) (hB₂ : B₂≠0) (hX : X₁*X₂=T) (hY : Y₁*Y₂=T)
    (hzero : ∀ i, sourceProfiles Wslot W₁ W₂ i 0=0)
    (hs : ∀ i x, sourceProfiles Wslot W₁ W₂ i x≠0 → x≤ sourceBounds b b₁ b₂ i)
    (v : Fin (N+2) → Ideal O)
    (hv : originalCoefficient N c χ R t ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v≠0) :
    tupleProduct v≠0 ∧ (Ideal.absNorm (tupleProduct v):ℝ)≤ sourceRadius b P b₁ b₂ T B₁ B₂ := by
  have hm := originalCoefficient_mem_sourcePool N c χ R t ν Wslot P b W₁ W₂ b₁ b₂
    X₁ X₂ Y₁ Y₂ B₁ B₂ s hP hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hzero hs v hv
  exact ⟨sourcePool_nonzero _ _ _ _ _ _ _ _ _ _ _ v hm,
    sourcePool_product_bound _ _ _ _ _ _ _ _ _ _ _ _ hX hY v hm⟩

theorem sourceProfiles_annular_support (N : ℕ) (Wslot : Fin N → ℝ → ℂ) (W₁ W₂ : ℝ → ℂ)
    (a b : Fin N → ℝ) (a₁ b₁ a₂ b₂ : ℝ)
    (ha : ∀ j, 0< a j) (ha₁ : 0< a₁) (ha₂ : 0< a₂)
    (hsSlot : ∀ j, Function.support (Wslot j)⊆Set.Icc (a j) (b j))
    (hs₁ : Function.support W₁⊆Set.Icc a₁ b₁) (hs₂ : Function.support W₂⊆Set.Icc a₂ b₂) :
    (∀ i, sourceProfiles Wslot W₁ W₂ i 0=0) ∧
    (∀ i x, sourceProfiles Wslot W₁ W₂ i x≠0 → x≤ sourceBounds b b₁ b₂ i) := by
  have hz (W : ℝ → ℂ) (a b : ℝ) (ha : 0< a) (hs : Function.support W⊆Set.Icc a b) : W 0=0 := by
    by_contra h
    have h' := (hs h).1
    linarith
  constructor
  · simpa only [Fin.forall_fin_add,sourceProfiles,Fin.append_left,Fin.append_right,Fin.forall_fin_two,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
      using And.intro (fun j => hz (Wslot j) (a j) (b j) (ha j) (hsSlot j))
        (And.intro (hz W₁ a₁ b₁ ha₁ hs₁) (hz W₂ a₂ b₂ ha₂ hs₂))
  · simpa only [Fin.forall_fin_add,sourceProfiles,sourceBounds,Fin.append_left,Fin.append_right,
      Fin.forall_fin_two,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
      using And.intro (fun j x (hx : Wslot j x≠0) => (hsSlot j hx).2)
        (And.intro (fun x (hx : W₁ x≠0) => (hs₁ hx).2) (fun x (hx : W₂ x≠0) => (hs₂ hx).2))

theorem sourcePool_prime_slots {N : ℕ} (ν : Fin N → Ideal O → ℂ)
    (pool : Fin N → Finset (Ideal O)) (hpool : ∀ j I, I∉pool j → ν j I=0)
    (hprime : ∀ j I, I∈pool j → Prime I)
    (hdisjoint : Pairwise (Function.onFun Disjoint pool))
    (b P : Fin N → ℝ) (b₁ b₂ X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O)
    (v : Fin (N+2) → Ideal O) (hv : v∈sourcePool ν b P b₁ b₂ X₁ X₂ Y₁ Y₂ B₁ B₂) :
    (∀ j : Fin N, Prime (v (j.castAdd 2))) ∧ Function.Injective (fun j : Fin N => v (j.castAdd 2)) := by
  have hm := sourcePool_original_slots ν pool hpool b P b₁ b₂ X₁ X₂ Y₁ Y₂ B₁ B₂ v hv
  refine ⟨fun j => hprime j _ (hm j),?_⟩
  intro i j he
  by_contra hij
  have hmj : v (i.castAdd 2)∈pool j := by
    rw [show v (i.castAdd 2)=v (j.castAdd 2) from he]
    exact hm j
  exact Finset.disjoint_left.mp (hdisjoint hij) (hm i) hmj

open CenteredMomentAddedZeroUniform

def finiteColumns {ι : Type*} [Fintype ι] (S : Finset (Tuple ι)) : Finset (Ideal O) :=
  S.image finiteTupleProduct

def finiteColumnCoefficient {ι : Type*} [Fintype ι] (S : Finset (Tuple ι))
    (β : Tuple ι → ℂ) (I : Ideal O) : ℂ :=
  ∑ v ∈ S.filter (fun v => finiteTupleProduct v=I), β v

lemma finiteColumnCoefficient_mass {ι : Type*} [Fintype ι] (S : Finset (Tuple ι))
    (β : Tuple ι → ℂ) :
    (∑ I ∈ finiteColumns S, ‖finiteColumnCoefficient S β I‖) ≤ ∑ v ∈ S, ‖β v‖ := by
  calc
    _ ≤ ∑ I ∈ finiteColumns S, ∑ v ∈ S.filter (fun v => finiteTupleProduct v=I), ‖β v‖ :=
      Finset.sum_le_sum (fun I _ => norm_sum_le _ _)
    _ = _ := Finset.sum_fiberwise_of_maps_to (fun v hv => Finset.mem_image.mpr ⟨v,hv,rfl⟩) _

lemma finite_original_mass_reindex {ι : Type*} [Fintype ι] {n : ℕ} (e : ι≃Fin n)
    (c : O) (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (R : Ideal O) (t : ℝ)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ s : Ideal O) (S : Finset (Tuple ι)) :
    (∑ v ∈ S.image (tupleEquiv e), ‖originalCoefficient n c χ R t
      (fun j => ν (e.symm j)) (fun j => Wslot (e.symm j)) (fun j => P (e.symm j))
      W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v‖) =
    ∑ v ∈ S, ‖originalFiniteCoefficient c χ R t ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v‖ := by
  rw [Finset.sum_image (fun v _ w _ he => (tupleEquiv e).injective he)]
  apply Finset.sum_congr rfl
  intro v hv
  rw [originalCoefficient_reindex]

theorem smooth_finite_source_mass_uniform {ι : Type*} [Fintype ι]
    (Wslot : ι → ℝ → ℂ) (W₁ W₂ : ℝ → ℂ)
    (a b : ι → ℝ) (a₁ b₁ a₂ b₂ : ℝ)
    (ha : ∀ j, 0< a j) (hb : ∀ j, 0≤ b j)
    (ha₁ : 0< a₁) (hb₁ : 0≤ b₁) (ha₂ : 0< a₂) (hb₂ : 0≤ b₂)
    (hsSlot : ∀ j, Function.support (Wslot j)⊆Set.Icc (a j) (b j))
    (hs₁ : Function.support W₁⊆Set.Icc a₁ b₁) (hs₂ : Function.support W₂⊆Set.Icc a₂ b₂)
    (hWslot : ∀ j, ContDiff ℝ ∞ (Wslot j)) (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂) :
    ∃ C : ℝ, 0< C ∧ ∀ (c : O), c≠0 → ∀ (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
      (R : Ideal O) (t : ℝ) (ν : ι → Ideal O → ℂ), (∀ j I, ‖ν j I‖≤1) →
      ∀ (P : ι → ℝ) (X₁ X₂ Y₁ Y₂ T : ℝ) (B₁ B₂ s : Ideal O),
      (∀ j, 0< P j) → 0< X₁ → 0< X₂ → 0< Y₁ → 0< Y₂ → B₁≠0 → B₂≠0 →
      X₁*X₂=T → Y₁*Y₂=T → ∀ S : Finset (Tuple ι),
      (∑ v ∈ S, ‖originalFiniteCoefficient c χ R t ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v‖) ≤
        C*(T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j,P j) := by
  let e := Fintype.equivFin ι
  obtain ⟨C,hC,hbound⟩ := smooth_source_mass_uniform (Fintype.card ι)
    (fun j => Wslot (e.symm j)) W₁ W₂ (fun j => a (e.symm j)) (fun j => b (e.symm j))
    a₁ b₁ a₂ b₂ (fun j => ha _) (fun j => hb _) ha₁ hb₁ ha₂ hb₂
    (fun j => hsSlot _) hs₁ hs₂ (fun j => hWslot _) hW₁ hW₂
  refine ⟨C,hC,?_⟩
  intro c hc χ R t ν hν P X₁ X₂ Y₁ Y₂ T B₁ B₂ s hP hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hX hY S
  have hm := (hbound c hc χ R t (fun j => ν (e.symm j)) (fun j I => hν _ I)
    (fun j => P (e.symm j)) X₁ X₂ Y₁ Y₂ T B₁ B₂ s (fun j => hP _)
    hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hX hY (S.image (tupleEquiv e))).1
  rw [finite_original_mass_reindex] at hm
  simpa only [e.symm.prod_comp P] using hm

theorem smooth_subset_source_mass_uniform {α : Type*} (A : Finset α)
    (Wslot : α → ℝ → ℂ) (W₁ W₂ : ℝ → ℂ)
    (a b : α → ℝ) (a₁ b₁ a₂ b₂ : ℝ)
    (ha : ∀ j∈A, 0< a j) (hb : ∀ j∈A, 0≤ b j)
    (ha₁ : 0< a₁) (hb₁ : 0≤ b₁) (ha₂ : 0< a₂) (hb₂ : 0≤ b₂)
    (hsSlot : ∀ j∈A, Function.support (Wslot j)⊆Set.Icc (a j) (b j))
    (hs₁ : Function.support W₁⊆Set.Icc a₁ b₁) (hs₂ : Function.support W₂⊆Set.Icc a₂ b₂)
    (hWslot : ∀ j∈A, ContDiff ℝ ∞ (Wslot j)) (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂) :
    ∃ C : ℝ, 0< C ∧ ∀ J : Finset α, J⊆A →
      ∀ (c : O), c≠0 → ∀ (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
      (R : Ideal O) (t : ℝ) (ν : α → Ideal O → ℂ), (∀ j∈J, ∀ I, ‖ν j I‖≤1) →
      ∀ (P : α → ℝ) (X₁ X₂ Y₁ Y₂ T : ℝ) (B₁ B₂ s : Ideal O),
      (∀ j∈J, 0< P j) → 0< X₁ → 0< X₂ → 0< Y₁ → 0< Y₂ → B₁≠0 → B₂≠0 →
      X₁*X₂=T → Y₁*Y₂=T → ∀ S : Finset (Tuple J),
      (∑ v ∈ S, ‖originalFiniteCoefficient c χ R t (fun j : J => ν j.val)
        (fun j : J => Wslot j.val) (fun j : J => P j.val)
        W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v‖) ≤
        C*(T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j∈J,P j) ∧
      (∑ I ∈ finiteColumns S, ‖finiteColumnCoefficient S
        (originalFiniteCoefficient c χ R t (fun j : J => ν j.val)
          (fun j : J => Wslot j.val) (fun j : J => P j.val)
          W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s) I‖) ≤
        C*(T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j∈J,P j) := by
  have hfamily (J : Finset α) (hJ : J⊆A) := smooth_finite_source_mass_uniform
    (fun j : J => Wslot j.val) W₁ W₂ (fun j : J => a j.val) (fun j : J => b j.val)
    a₁ b₁ a₂ b₂ (fun j => ha j.val (hJ j.property)) (fun j => hb j.val (hJ j.property))
    ha₁ hb₁ ha₂ hb₂ (fun j => hsSlot j.val (hJ j.property)) hs₁ hs₂
    (fun j => hWslot j.val (hJ j.property)) hW₁ hW₂
  let D (J : Finset α) : ℝ := if hJ : J⊆A then (hfamily J hJ).choose else 1
  have hD (J : Finset α) : 0< D J := by
    dsimp only [D]
    split_ifs with hJ
    · exact (hfamily J hJ).choose_spec.1
    · norm_num
  let C := 1+∑ J∈A.powerset,D J
  have hsum : 0≤∑ J∈A.powerset,D J := Finset.sum_nonneg (fun J _ => (hD J).le)
  refine ⟨C,by dsimp [C]; linarith,?_⟩
  intro J hJ c hc χ R t ν hν P X₁ X₂ Y₁ Y₂ T B₁ B₂ s hP hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hX hY S
  have hDC : D J≤ C := by
    have hle := Finset.single_le_sum (fun K _ => (hD K).le) (Finset.mem_powerset.mpr hJ)
    dsimp only [C]
    linarith
  have hm := (hfamily J hJ).choose_spec.2 c hc χ R t (fun j : J => ν j.val)
    (fun j I => hν j.val j.property I) (fun j : J => P j.val)
    X₁ X₂ Y₁ Y₂ T B₁ B₂ s (fun j => hP j.val j.property)
    hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hX hY S
  have he : D J=(hfamily J hJ).choose := by simp only [D,dif_pos hJ]
  rw [← he,Finset.prod_coe_sort] at hm
  have hT : 0< T := hX ▸ mul_pos hX₁ hX₂
  have hprodP : 0≤∏ j∈J,P j := Finset.prod_nonneg (fun j hj => (hP j hj).le)
  have hraw : 0≤(T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j∈J,P j) := by positivity
  have hm' := hm.trans (show D J*(T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j∈J,P j) ≤
      C*(T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j∈J,P j) from
      by simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hDC hraw)
  exact ⟨hm',(finiteColumnCoefficient_mass S _).trans hm'⟩

theorem finiteColumns_reindex {ι : Type*} [Fintype ι] {n : ℕ} (e : ι≃Fin n)
    (S : Finset (Tuple ι)) :
    tupleColumns (S.image (tupleEquiv e))=finiteColumns S := by
  simp only [tupleColumns,finiteColumns,Finset.image_image]
  congr 1
  funext v
  exact tupleProduct_reindex e v

theorem finiteColumnCoefficient_reindex {ι : Type*} [Fintype ι] {n : ℕ} (e : ι≃Fin n)
    (S : Finset (Tuple ι)) (β : Tuple ι → ℂ) (I : Ideal O) :
    tupleCoefficient (S.image (tupleEquiv e)) (fun w => β ((tupleEquiv e).symm w)) I =
      finiteColumnCoefficient S β I := by
  unfold tupleCoefficient finiteColumnCoefficient
  have hset : (S.image (tupleEquiv e)).filter (fun w => tupleProduct w=I) =
      (S.filter (fun v => finiteTupleProduct v=I)).image (tupleEquiv e) := by
    ext w
    simp only [Finset.mem_filter,Finset.mem_image]
    constructor
    · rintro ⟨⟨v,hv,rfl⟩,hprod⟩
      exact ⟨v,⟨hv,by simpa only [tupleProduct_reindex] using hprod⟩,rfl⟩
    · rintro ⟨v,⟨hv,hprod⟩,rfl⟩
      exact ⟨⟨v,hv,rfl⟩,by simpa only [tupleProduct_reindex] using hprod⟩
  rw [hset,Finset.sum_image (fun v _ w _ he => (tupleEquiv e).injective he)]
  simp only [Equiv.symm_apply_apply]

end CenteredMomentSourceMass

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical ContDiff

namespace CenteredMomentSourceProfileMass
open Eisenstein CenteredMomentPrimary CenteredMomentRectangle
open CenteredMomentAddedZeroUniform CenteredMomentSourceMass
local notation "O" => Eisenstein.O

 theorem primary_mod_one (χ : MulChar (O ⧸ Ideal.span {(1:O)}) ℂ) (I : Ideal O) :
    primaryIdealCharacter 1 χ I=1 := by
  rw [primaryIdealCharacter_apply]
  have he : Ideal.Quotient.mk (Ideal.span {(1:O)}) (primaryIdealGenerator I)=1 := by
    rw [← map_one (Ideal.Quotient.mk (Ideal.span {(1:O)}))]
    apply Ideal.Quotient.eq.mpr
    rw [Ideal.span_singleton_one]
    trivial
  rw [he,map_one]

 theorem idealWeight_mod_one (χ : MulChar (O ⧸ Ideal.span {(1:O)}) ℂ) (R I : Ideal O) :
    CenteredMomentRectangle.idealWeight 1 χ R 0 I=(if IsCoprime I R then 1 else 0) := by
  simp only [idealWeight,primary_mod_one,Complex.ofReal_zero,mul_zero,Complex.cpow_zero,mul_one]

def profileCoefficient {ι : Type*} [Fintype ι]
    (R : Ideal O) (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ s : Ideal O) (v : Tuple ι) : ℂ :=
  (∏ j,ν j (v (Sum.inl j))*Wslot j ((Ideal.absNorm (v (Sum.inl j)):ℝ)/P j))*
    (if IsCoprime (finiteTupleProduct v) R then 1 else 0)*
    idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ (B₁*v (Sum.inr 0)) (B₂*v (Sum.inr 1))*
    (if s∣finiteTupleProduct v then 1 else 0)

 theorem profileCoefficient_eq_original {ι : Type*} [Fintype ι]
    (R : Ideal O) (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ s : Ideal O) (v : Tuple ι) :
    profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v=
      originalFiniteCoefficient 1 (1 : MulChar (O ⧸ Ideal.span {(1:O)}) ℂ) R 0
        ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v := by
  rw [originalFiniteCoefficient,idealWeight_mod_one]
  rfl

theorem profile_mass_uniform {ι : Type*} [Fintype ι]
    (Wslot : ι → ℝ → ℂ) (W₁ W₂ : ℝ → ℂ)
    (a b : ι → ℝ) (a₁ b₁ a₂ b₂ : ℝ)
    (ha : ∀ j,0< a j) (hb : ∀ j,0≤ b j)
    (ha₁ : 0< a₁) (hb₁ : 0≤ b₁) (ha₂ : 0< a₂) (hb₂ : 0≤ b₂)
    (hsSlot : ∀ j,Function.support (Wslot j)⊆Set.Icc (a j) (b j))
    (hs₁ : Function.support W₁⊆Set.Icc a₁ b₁) (hs₂ : Function.support W₂⊆Set.Icc a₂ b₂)
    (hWslot : ∀ j,ContDiff ℝ ∞ (Wslot j)) (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂) :
    ∃ C : ℝ,0< C ∧ ∀ (R : Ideal O) (ν : ι → Ideal O → ℂ),
      (∀ j I,‖ν j I‖≤1) → ∀ (P : ι → ℝ) (X₁ X₂ Y₁ Y₂ T : ℝ) (B₁ B₂ s : Ideal O),
      (∀ j,0< P j) → 0< X₁ → 0< X₂ → 0< Y₁ → 0< Y₂ → B₁≠0 → B₂≠0 →
      X₁*X₂=T → Y₁*Y₂=T → ∀ S : Finset (Tuple ι),
      (∑ v∈S,‖profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v‖)≤
        C*(T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j,P j) := by
  obtain ⟨C,hC,ht⟩ := smooth_finite_source_mass_uniform Wslot W₁ W₂ a b a₁ b₁ a₂ b₂
    ha hb ha₁ hb₁ ha₂ hb₂ hsSlot hs₁ hs₂ hWslot hW₁ hW₂
  refine ⟨C,hC,?_⟩
  intro R ν hν P X₁ X₂ Y₁ Y₂ T B₁ B₂ s hP hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hX hY S
  simp_rw [profileCoefficient_eq_original]
  exact ht 1 one_ne_zero 1 R 0 ν hν P X₁ X₂ Y₁ Y₂ T B₁ B₂ s
    hP hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hX hY S

end CenteredMomentSourceProfileMass

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace CenteredMomentFirstTailAggregate
open Eisenstein HeckeFamily CanonicalRowCompletion CanonicalQuadraticSieve

open CenteredMomentSourceRow CenteredMomentHeckeExpansion CenteredMomentTwist
local notation "O" => Eisenstein.O

theorem rowWeight_norm_le_one (η : Character) (m A z : O) (t : ℝ)
    (I : Ideal O) (hI : I≠0) : ‖rowWeight η m A z t I‖≤1 := by
  have hp := norm_real_imaginary_power (Ideal.absNorm I:ℝ) t (by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI))
  norm_cast at hp
  change ‖(idealCoeff η I*idealRowHom (m^6*(A*z)) I)*(Ideal.absNorm I:ℂ)^(Complex.I*t)‖≤1
  rw [norm_mul,norm_mul,hp,mul_one]
  exact (mul_le_of_le_one_left (norm_nonneg _)
    (idealCoeff_norm_le_one η I)).trans (idealRowHom_norm _ _)


end CenteredMomentFirstTailAggregate
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace CenteredMomentAbsoluteEnergy
open Eisenstein HeckeFamily CanonicalRowCompletion
open CenteredMomentHeckeExpansion CenteredMomentSourceRow CenteredMomentSourceMass
open CenteredMomentSourceProfileMass CenteredMomentAddedZeroUniform
open  SchwartzPlanePoisson InversePrincipalEnergy
local notation "O" => Eisenstein.O

theorem rowWeight_norm_le_one_all (η : Character) (m A z : O) (t : ℝ)
    (I : Ideal O) : ‖rowWeight η m A z t I‖ ≤ 1 := by
  by_cases hI : I=0
  · subst I
    rw [map_zero,norm_zero]
    norm_num
  · exact CenteredMomentFirstTailAggregate.rowWeight_norm_le_one η m A z t I hI

theorem radial_norm_summable (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0< K) :
    Summable (fun z : O => ‖Φ (‖ringComplex z‖^2/K)‖) := by
  simpa only [scaledRadialTest_apply] using
    actual_eisenstein_summable_norm (scaledRadialTest Φ K hK)

theorem radial_weight_lattice_bound_all (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0< K) :
    (∑' z : O, ‖Φ (‖ringComplex z‖^2/K)‖) ≤ diagonalControl Φ*max 1 K := by
  by_cases hlarge : 1≤ K
  · simpa only [max_eq_right hlarge] using radial_weight_lattice_bound Φ K hlarge
  have hsmall : K≤1 := (not_le.mp hlarge).le
  let B := 4*(Finset.Iic (2,0)).sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ
  have hB : 0≤ B := by dsimp [B]; positivity
  have hp (z : O) : ‖Φ (‖ringComplex z‖^2/K)‖ ≤
      B*((1+1*‖ringComplex z‖^2)^2)⁻¹ := by
    have hq : 0≤‖ringComplex z‖^2/K := div_nonneg (sq_nonneg _) hK.le
    have hh := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ)
      (m := (2,0)) (k := 2) (n := 0) le_rfl le_rfl Φ (‖ringComplex z‖^2/K)
    simp only [norm_iteratedFDeriv_zero,Real.norm_of_nonneg hq] at hh
    norm_num only [show (2:ℝ)^2=4 by norm_num] at hh
    change (1+‖ringComplex z‖^2/K)^2*‖Φ (‖ringComplex z‖^2/K)‖≤ B at hh
    have hq' : ‖ringComplex z‖^2≤‖ringComplex z‖^2/K := by
      apply (le_div_iff₀ hK).mpr
      exact mul_le_of_le_one_right (sq_nonneg _) hsmall
    have hden : (1+1*‖ringComplex z‖^2)^2≤(1+‖ringComplex z‖^2/K)^2 := by
      simp only [one_mul]
      gcongr
    rw [← div_eq_mul_inv]
    apply (le_div_iff₀ (by positivity)).mpr
    simpa only [mul_comm] using (mul_le_mul_of_nonneg_right hden (norm_nonneg _)).trans hh
  have hb := (radial_norm_summable Φ K hK).tsum_le_tsum hp
    ((scaled_eisenstein_cauchy_summable 1 (by norm_num)).mul_left B)
  rw [tsum_mul_left] at hb
  have hc := scaled_eisenstein_cauchy_small 1 (by norm_num) (by norm_num)
  simp only [one_mul] at hc hb
  have ht := hb.trans (mul_le_mul_of_nonneg_left hc hB)
  rw [max_eq_left hsmall,mul_one]
  dsimp only [B] at ht
  unfold diagonalControl
  nlinarith

theorem finite_hecke_polynomial_norm (η : Character) (m A z : O) (t : ℝ)
    (S : Finset (Ideal O)) (c : Ideal O → ℂ) :
    ‖∑ I∈S,c I*rowWeight η m A z t I‖ ≤ ∑ I∈S,‖c I‖ := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro I hI
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (rowWeight_norm_le_one_all η m A z t I)

theorem finite_hecke_energy_summable (η : Character) (m A : O) (t : ℝ)
    (S : Finset (Ideal O)) (c : Ideal O → ℂ) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0< K) :
    Summable (fun z : O => ((‖∑ I∈S,c I*rowWeight η m A z t I‖^2:ℝ):ℂ)*
      Φ (‖ringComplex z‖^2/K)) := by
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (f := fun z : O => (∑ I∈S,‖c I‖)^2*‖Φ (‖ringComplex z‖^2/K)‖)
  · intro z
    rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (sq_nonneg _)]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (norm_nonneg _) (finite_hecke_polynomial_norm η m A z t S c) 2)
      (norm_nonneg _)
  · exact (radial_norm_summable Φ K hK).mul_left _

theorem finite_hecke_energy_absolute (η : Character) (m A : O) (t : ℝ)
    (S : Finset (Ideal O)) (c : Ideal O → ℂ) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0< K) :
    ‖finiteHeckeEnergy η m A t S c Φ K‖ ≤
      diagonalControl Φ*max 1 K*(∑ I∈S,‖c I‖)^2 := by
  have hs := (finite_hecke_energy_summable η m A t S c Φ K hK).norm
  calc
    _ ≤ ∑' z : O, ‖((‖∑ I∈S,c I*rowWeight η m A z t I‖^2:ℝ):ℂ)*
        Φ (‖ringComplex z‖^2/K)‖ := norm_tsum_le_tsum_norm hs
    _ ≤ ∑' z : O,(∑ I∈S,‖c I‖)^2*‖Φ (‖ringComplex z‖^2/K)‖ := by
      apply hs.tsum_le_tsum _ ((radial_norm_summable Φ K hK).mul_left _)
      intro z
      rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (sq_nonneg _)]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (norm_nonneg _) (finite_hecke_polynomial_norm η m A z t S c) 2)
        (norm_nonneg _)
    _ = (∑ I∈S,‖c I‖)^2*(∑' z : O,‖Φ (‖ringComplex z‖^2/K)‖) := tsum_mul_left
    _ ≤ (∑ I∈S,‖c I‖)^2*(diagonalControl Φ*max 1 K) :=
      mul_le_mul_of_nonneg_left (radial_weight_lattice_bound_all Φ K hK) (sq_nonneg _)
    _ = _ := by ring

theorem smooth_subset_source_absolute_energy {α : Type*} (F : Finset α)
    (Wslot : α → ℝ → ℂ) (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ))
    (a b : α → ℝ) (a₁ b₁ a₂ b₂ : ℝ)
    (ha : ∀ j∈F,0< a j) (hb : ∀ j∈F,0≤ b j)
    (ha₁ : 0< a₁) (hb₁ : 0≤ b₁) (ha₂ : 0< a₂) (hb₂ : 0≤ b₂)
    (hsSlot : ∀ j∈F,Function.support (Wslot j)⊆Set.Icc (a j) (b j))
    (hs₁ : Function.support W₁⊆Set.Icc a₁ b₁) (hs₂ : Function.support W₂⊆Set.Icc a₂ b₂)
    (hWslot : ∀ j∈F,ContDiff ℝ ∞ (Wslot j)) (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂) :
    ∃ C : ℝ,0< C ∧ ∀ J : Finset α,J⊆F →
      ∀ (η : Character) (m A : O) (t : ℝ) (R : Ideal O) (ν : α → Ideal O → ℂ),
      (∀ j∈J,∀ I,‖ν j I‖≤1) →
      ∀ (P : α → ℝ) (X₁ X₂ Y₁ Y₂ T : ℝ) (B₁ B₂ s : Ideal O),
      (∀ j∈J,0< P j) → 0< X₁ → 0< X₂ → 0< Y₁ → 0< Y₂ → B₁≠0 → B₂≠0 →
      X₁*X₂=T → Y₁*Y₂=T → ∀ (S : Finset (Tuple J)) (K : ℝ),0< K →
      let H := (T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j∈J,P j)
      let E := finiteHeckeEnergy η m A t (finiteColumns S)
        (finiteColumnCoefficient S (profileCoefficient R (fun j : J => ν j.val)
          (fun j : J => Wslot j.val) (fun j : J => P j.val)
          W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s)) Φ K
      ‖E‖≤ C*max 1 K*H^2 ∧ ‖E‖/H≤ C*max 1 K*H := by
  obtain ⟨D,hD,hm⟩ := smooth_subset_source_mass_uniform F Wslot W₁ W₂ a b a₁ b₁ a₂ b₂
    ha hb ha₁ hb₁ ha₂ hb₂ hsSlot hs₁ hs₂ hWslot hW₁ hW₂
  let C := (diagonalControl Φ+1)*D^2
  have hd := diagonalControl_nonneg Φ
  have hC : 0< C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro J hJ η m A t R ν hν P X₁ X₂ Y₁ Y₂ T B₁ B₂ s hP hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hX hY S K hK H E
  have hmass := (hm J hJ 1 one_ne_zero 1 R 0 ν hν P X₁ X₂ Y₁ Y₂ T B₁ B₂ s
    hP hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hX hY S).2
  have hmass' : (∑ I∈finiteColumns S,‖finiteColumnCoefficient S
      (profileCoefficient R (fun j : J => ν j.val) (fun j : J => Wslot j.val)
        (fun j : J => P j.val) W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s) I‖)≤ D*H := by
    simpa only [finiteColumnCoefficient,profileCoefficient_eq_original,H,mul_assoc] using hmass
  have hT : 0< T := hX ▸ mul_pos hX₁ hX₂
  have hNB₁ : 0<(Ideal.absNorm B₁:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hB₁)
  have hNB₂ : 0<(Ideal.absNorm B₂:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hB₂)
  have hprod : 0<∏ j∈J,P j := Finset.prod_pos hP
  have hH : 0< H := by dsimp only [H]; positivity
  have hmax : 0≤ max 1 K := le_trans zero_le_one (le_max_left _ _)
  have he : ‖E‖≤ C*max 1 K*H^2 := by
    apply (finite_hecke_energy_absolute η m A t (finiteColumns S) _ Φ K hK).trans
    calc
      _ ≤ diagonalControl Φ*max 1 K*(D*H)^2 :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) hmass' 2)
          (mul_nonneg hd hmax)
      _ ≤ (diagonalControl Φ+1)*max 1 K*(D*H)^2 := by gcongr; linarith
      _ = C*max 1 K*H^2 := by dsimp only [C]; ring
  refine ⟨he,?_⟩
  apply (div_le_iff₀ hH).mpr
  convert he using 1 <;> first | rfl | ring

end CenteredMomentAbsoluteEnergy

end

end

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
