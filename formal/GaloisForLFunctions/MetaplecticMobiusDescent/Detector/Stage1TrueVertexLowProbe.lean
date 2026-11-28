import GaloisForLFunctions.MetaplecticMobiusDescent.Reflection.EdgeReflectedEnergy
import GaloisForLFunctions.MetaplecticMobiusDescent.Detector.PrincipalSignalComparison
import GaloisForLFunctions.MetaplecticMobiusDescent.Detector.SubSevenEighthsLowProbe

/-!
# Low Physical Detector Bounds at the Stage-1 Vertex `(2111/6000, 19249/40000, 20033/120000)`

Physical normalization, unselected-slot `L^{-1/2}` cancellation, central and remote Gaussian dyads,
and principal-residue normalization for the compensated physical probe at the Gram-admissible
Stage-1 edge scales `X = Z^{2111/6000}`, `Y = Z^{19249/40000}`, `∑ i, ell i = 20033/120000`
(`M = 99967/120000`, Gram gap `2 lx - ly - ℓ = 111/2000 > 0`):

* `stage1Vertex_low_physical_inverse_normalized`: dividing the reflected row energy
  `O(Z^{99967/120000 - 7d/4 + 507ε})` (`stage1Vertex_low_original_completed_energy`) by the physical
  scale `Q = q Z^{99967/120000} / L^2` (`L ≤ B Z^d`) yields `O((1 + ‖t‖)^degree Z^{d/8 + 507ε/2})`.
* `stage1Vertex_lowGramFactor_source_bound`: at `(Z^{2111/6000}/L, Z^{19249/40000}/L)` we have
  `Y/X = Z^{15527/120000}` and `X^2/Y = Z^{26693/120000} = Z^{111/2000} Z^{20033/120000}`, bounding
  `lowGramFactor` by `√(3q/L) Z^{268847/1440000 + (19249/80000)δ}`.
* `stage1Vertex_normalized_compensatedPhysicalProbe_low`: after normalizing by
  `sourceResidueConstant W0 W1 (∏ P ∈ S, P) * Probe.principalScalar Finset.univ Z (20033/120000) ...`,
  the low physical probe is `O(Z^{268847/1440000 + loss})`
  (`268847/1440000 = 139989/160000 - 495527/720000`).
-/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Classical Topology InnerProductSpace ComplexConjugate MatrixGroups ENNReal
open scoped ContDiff FourierTransform SchwartzMap

namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson

namespace ProbePhysical
open CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion RayFourExpansion
open ProbePrincipalResidueActual ProbeRaySlots PrincipalSignalComparison PrincipalMellinResidues
local notation "O" => Eisenstein.O
local notation "Id" => Ideal O
local notation "SupportedIdeal" => {I : Ideal O // Supported I}
local instance instFintypeUnitsOStage1Vertex : Fintype Oˣ := @Fintype.ofFinite _ cubic_units_finite

/-! ### Stage-1 vertex slot length, physical scale, and Gram scale helpers -/

lemma stage1Vertex_lowLength_bounds {K : ℕ} (ell : Fin K → ℝ) (hell : ∀ i, 0 ≤ ell i)
    (hsum : ∑ i, ell i ≤ 20033 / 120000) (J : Finset (Fin K)) :
    0 ≤ lowUnselectedLength ell J ∧ lowUnselectedLength ell J ≤ 20033 / 120000 ∧
    0 ≤ lowSelectedLength ell J ∧ lowSelectedLength ell J ≤ 20033 / 120000 - lowUnselectedLength ell J := by
  have hu : 0 ≤ lowUnselectedLength ell J := Finset.sum_nonneg (fun i _ => hell i)
  have hs : 0 ≤ lowSelectedLength ell J := Finset.sum_nonneg (fun i _ => hell i.val)
  have he := lowLength_sum ell J
  exact ⟨hu, by linarith, hs, by linarith⟩

lemma stage1Vertex_lowUnselectedProduct_norm_bound {K : ℕ} (ell : Fin K → ℝ)
    (hell : ∀ i, 0 ≤ ell i) (hsum : ∑ i, ell i ≤ 20033 / 120000)
    (b Z : ℝ) (hb : 1 ≤ b) (hZ : 1 ≤ Z) (slots : Fin K → Finset O)
    (hslots : ∀ i x, x ∈ slots i → elementNorm x ≤ b * Z ^ (ell i))
    (J : Finset (Fin K)) (a : LowUnselectedTuple slots J) :
    elementNorm (∏ i : J, (a i).val) ≤ b ^ K * Z ^ (20033 / 120000 : ℝ) := by
  have hz : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  have hsub : ∑ i ∈ J, ell i ≤ 20033 / 120000 :=
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => hell i)).trans hsum
  have hc : J.card ≤ K := by simpa using Finset.card_le_card (Finset.subset_univ J)
  rw [elementNorm_finset_prod]
  calc
    _ ≤ ∏ i : J, b * Z ^ (ell i.val) := Finset.prod_le_prod (fun _ _ => by unfold elementNorm; positivity)
      (fun i _ => hslots i.val _ (a i).property)
    _ = b ^ J.card * Z ^ (∑ i ∈ J, ell i) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_coe,
        ← Real.rpow_sum_of_pos hz, Finset.sum_coe_sort]
    _ ≤ b ^ K * Z ^ (20033 / 120000 : ℝ) := mul_le_mul (pow_le_pow_right₀ hb hc)
      (Real.rpow_le_rpow_of_exponent_le hZ hsub) (by positivity) (by positivity)

lemma stage1Vertex_source_scale_ratio (Z : ℝ) (hZ : 0 < Z) :
    Z ^ (19249 / 40000 : ℝ) / Z ^ (2111 / 6000 : ℝ) = Z ^ (15527 / 120000 : ℝ) := by
  rw [← Real.rpow_sub hZ]
  norm_num

lemma stage1Vertex_source_scale_square (Z : ℝ) (hZ : 0 < Z) :
    Z ^ (26693 / 120000 : ℝ) * Z ^ (19249 / 40000 : ℝ) = (Z ^ (2111 / 6000 : ℝ)) ^ 2 := by
  rw [← Real.rpow_add hZ, ← Real.rpow_natCast, ← Real.rpow_mul hZ.le]
  norm_num

lemma stage1Vertex_source_gram_power (Z δ : ℝ) (hZ : 0 < Z) :
    Z ^ (2111 / 6000 : ℝ) * (Z ^ (15527 / 120000 : ℝ)) ^ (1 / 6 : ℝ) *
      (Z ^ (19249 / 40000 : ℝ)) ^ δ =
      Z ^ (268847 / 720000 + (19249 / 40000) * δ : ℝ) := by
  rw [← Real.rpow_mul hZ.le, ← Real.rpow_mul hZ.le, ← Real.rpow_add hZ, ← Real.rpow_add hZ]
  congr 1
  ring

lemma stage1Vertex_source_gram_sqrt_power (Z δ : ℝ) (hZ : 0 < Z) :
    Real.sqrt (Z ^ (268847 / 720000 + (19249 / 40000) * δ : ℝ)) =
      Z ^ (268847 / 1440000 + (19249 / 80000) * δ : ℝ) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hZ.le]
  congr 1
  ring

lemma stage1Vertex_source_compensated_scale_admissible (q Z L : ℝ) (hq : 1 ≤ q) (hZ : 1 ≤ Z)
    (hL : 1 ≤ L) (hql : q ≤ Z ^ (15527 / 120000 : ℝ)) (hLl : L ≤ Z ^ (26693 / 120000 : ℝ)) :
    1 ≤ Z ^ (19249 / 40000 : ℝ) / L ∧
    q * Z ^ (2111 / 6000 : ℝ) ≤ Z ^ (19249 / 40000 : ℝ) ∧
    L * Z ^ (19249 / 40000 : ℝ) ≤ q ^ 2 * (Z ^ (2111 / 6000 : ℝ)) ^ 2 := by
  have hz : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  have hl : 0 < L := lt_of_lt_of_le zero_lt_one hL
  refine ⟨(le_div_iff₀ hl).mpr (by
    simpa using hLl.trans
      (Real.rpow_le_rpow_of_exponent_le hZ (show (26693 / 120000 : ℝ) ≤ 19249 / 40000 by norm_num))),
    ?_, ?_⟩
  · apply (le_div_iff₀ (Real.rpow_pos_of_pos hz (2111 / 6000))).mp
    rwa [stage1Vertex_source_scale_ratio Z hz]
  · calc
      _ ≤ Z ^ (26693 / 120000 : ℝ) * Z ^ (19249 / 40000 : ℝ) :=
        mul_le_mul_of_nonneg_right hLl (by positivity)
      _ = (Z ^ (2111 / 6000 : ℝ)) ^ 2 := stage1Vertex_source_scale_square Z hz
      _ ≤ _ := le_mul_of_one_le_left (by positivity) (one_le_pow₀ hq)

lemma stage1Vertex_lowGramFactor_source_bound (C : CalibrationData) (Z L δ : ℝ) (hZ : 1 ≤ Z)
    (hL : 1 ≤ L) (hql : elementNorm C.generator ≤ Z ^ (15527 / 120000 : ℝ))
    (hLl : L ≤ Z ^ (26693 / 120000 : ℝ)) (hδ : 0 ≤ δ) :
    lowGramFactor C (Z ^ (2111 / 6000 : ℝ) / L) (Z ^ (19249 / 40000 : ℝ) / L) δ ≤
      Real.sqrt (3 * elementNorm C.generator / L) *
        Z ^ (268847 / 1440000 + (19249 / 80000) * δ : ℝ) := by
  let q := elementNorm C.generator
  have hq : 1 ≤ q := calibration_elementNorm_ge_one C
  have hz : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  obtain ⟨_, hqp, ht⟩ := stage1Vertex_source_compensated_scale_admissible q Z L hq hZ hL hql hLl
  have hb := compensated_gram_scale_bound q (Z ^ (2111 / 6000 : ℝ)) (Z ^ (19249 / 40000 : ℝ))
    L δ hq0 (by positivity) (by positivity) hL hδ hqp ht
  have hratio : Z ^ (19249 / 40000 : ℝ) / (q * Z ^ (2111 / 6000 : ℝ)) ≤ Z ^ (15527 / 120000 : ℝ) := by
    rw [← stage1Vertex_source_scale_ratio Z hz]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity)
      (le_mul_of_one_le_left (by positivity) hq)
  have hscale : (lowPhysicalScale C (Z ^ (2111 / 6000 : ℝ) / L) (Z ^ (19249 / 40000 : ℝ) / L) /
      (Z ^ (19249 / 40000 : ℝ) / L)) *
      (1 + ((Z ^ (19249 / 40000 : ℝ) / L) ^ 2 /
        lowPhysicalScale C (Z ^ (2111 / 6000 : ℝ) / L) (Z ^ (19249 / 40000 : ℝ) / L)) ^ (1 / 6 : ℝ) +
      ((Z ^ (19249 / 40000 : ℝ) / L) ^ 2 /
        lowPhysicalScale C (Z ^ (2111 / 6000 : ℝ) / L) (Z ^ (19249 / 40000 : ℝ) / L)) ^ 2 /
        (Z ^ (19249 / 40000 : ℝ) / L)) * (Z ^ (19249 / 40000 : ℝ) / L) ^ δ ≤
      (3 * q / L) * Z ^ (268847 / 720000 + (19249 / 40000) * δ : ℝ) := by
    unfold lowPhysicalScale
    apply hb.trans
    have hp := Real.rpow_le_rpow
      (by positivity : 0 ≤ Z ^ (19249 / 40000 : ℝ) / (q * Z ^ (2111 / 6000 : ℝ)))
      hratio (show 0 ≤ (1 / 6 : ℝ) by norm_num)
    calc
      _ ≤ 3 * (q * Z ^ (2111 / 6000 : ℝ) / L) * (Z ^ (15527 / 120000 : ℝ)) ^ (1 / 6 : ℝ) *
          (Z ^ (19249 / 40000 : ℝ)) ^ δ := by gcongr
      _ = (3 * q / L) * (Z ^ (2111 / 6000 : ℝ) * (Z ^ (15527 / 120000 : ℝ)) ^ (1 / 6 : ℝ) *
          (Z ^ (19249 / 40000 : ℝ)) ^ δ) := by ring
      _ = _ := by rw [stage1Vertex_source_gram_power Z δ hz]
  unfold lowGramFactor
  apply (Real.sqrt_le_sqrt hscale).trans_eq
  rw [Real.sqrt_mul (by positivity), stage1Vertex_source_gram_sqrt_power Z δ hz]

theorem eventually_stage1Vertex_slot_scales {K : ℕ} (C : CalibrationData) (ell : Fin K → ℝ)
    (hell : ∀ i, 0 ≤ ell i) (hsum : ∑ i, ell i ≤ 20033 / 120000) (b : ℝ) (hb : 1 ≤ b) :
    ∀ᶠ Z : ℝ in Filter.atTop, 1 ≤ Z ∧
      ∀ (slots : Fin K → Finset O) (_hslots : ∀ i x, x ∈ slots i → x ≠ 0),
      (∀ i x, x ∈ slots i → elementNorm x ≤ b * Z ^ (ell i)) →
      ∀ (J : Finset (Fin K)) (a : LowUnselectedTuple slots J),
      let L := elementNorm (∏ i : J, (a i).val)
      1 ≤ Z ^ (19249 / 40000 : ℝ) / L ∧
      1 ≤ (Z ^ (19249 / 40000 : ℝ) / L) ^ 2 /
        lowPhysicalScale C (Z ^ (2111 / 6000 : ℝ) / L) (Z ^ (19249 / 40000 : ℝ) / L) ∧
      ∀ δ : ℝ, 0 ≤ δ →
        lowGramFactor C (Z ^ (2111 / 6000 : ℝ) / L) (Z ^ (19249 / 40000 : ℝ) / L) δ ≤
          Real.sqrt (3 * elementNorm C.generator / L) *
            Z ^ (268847 / 1440000 + (19249 / 80000) * δ : ℝ) := by
  have hq := (tendsto_rpow_atTop (show 0 < (15527 / 120000 : ℝ) by norm_num)).eventually
    (Filter.eventually_ge_atTop (elementNorm C.generator))
  have hbZ := (tendsto_rpow_atTop (show 0 < (111 / 2000 : ℝ) by norm_num)).eventually
    (Filter.eventually_ge_atTop (b ^ K))
  filter_upwards [Filter.eventually_ge_atTop (1 : ℝ), hq, hbZ] with Z hZ hq hbZ
  refine ⟨hZ, ?_⟩
  intro slots hslots hnorm J a
  let L := elementNorm (∏ i : J, (a i).val)
  have hz : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  have hL : 1 ≤ L := lowUnselectedProduct_norm_ge_one slots hslots J a
  have hl : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hLB : L ≤ b ^ K * Z ^ (20033 / 120000 : ℝ) :=
    stage1Vertex_lowUnselectedProduct_norm_bound ell hell hsum b Z hb hZ slots hnorm J a
  have hLl : L ≤ Z ^ (26693 / 120000 : ℝ) := calc
    L ≤ b ^ K * Z ^ (20033 / 120000 : ℝ) := hLB
    _ ≤ Z ^ (111 / 2000 : ℝ) * Z ^ (20033 / 120000 : ℝ) := mul_le_mul_of_nonneg_right hbZ (by positivity)
    _ = Z ^ (26693 / 120000 : ℝ) := by rw [← Real.rpow_add hz]; norm_num
  obtain ⟨hy, hp, _⟩ := stage1Vertex_source_compensated_scale_admissible _ Z L
    (calibration_elementNorm_ge_one C) hZ hL hq hLl
  refine ⟨hy, ?_, fun δ hδ => stage1Vertex_lowGramFactor_source_bound C Z L δ hZ hL hq hLl hδ⟩
  rw [lowPhysicalScale, compensated_gram_ratio _ _ _ _ (calibration_elementNorm_pos C)
    (by positivity) (by positivity) hl]
  exact (le_div_iff₀ (mul_pos (calibration_elementNorm_pos C) (by positivity))).mpr (by simpa using hp)

lemma stage1Vertex_lowPhysicalScale_source (C : CalibrationData) (Z L : ℝ) (hZ : 0 < Z) :
    lowPhysicalScale C (Z ^ (2111 / 6000 : ℝ) / L) (Z ^ (19249 / 40000 : ℝ) / L) =
      elementNorm C.generator * Z ^ (99967 / 120000 : ℝ) / L ^ 2 := by
  unfold lowPhysicalScale
  have he : Z ^ (2111 / 6000 : ℝ) * Z ^ (19249 / 40000 : ℝ) = Z ^ (99967 / 120000 : ℝ) := by
    rw [← Real.rpow_add hZ]; norm_num
  rw [← he]
  ring

lemma stage1Vertex_lowPhysicalScale_nominal_bound (C : CalibrationData) (Z L c d : ℝ)
    (hZ : 0 < Z) (hc : 0 < c) (hL : c * Z ^ d ≤ L) :
    lowPhysicalScale C (Z ^ (2111 / 6000 : ℝ) / L) (Z ^ (19249 / 40000 : ℝ) / L) ≤
      (elementNorm C.generator / c ^ 2) * Z ^ (99967 / 120000 - 2 * d : ℝ) := by
  rw [stage1Vertex_lowPhysicalScale_source C Z L hZ]
  calc
    _ ≤ elementNorm C.generator * Z ^ (99967 / 120000 : ℝ) / (c * Z ^ d) ^ 2 :=
      div_le_div_of_nonneg_left (by unfold elementNorm; positivity) (by positivity)
        (pow_le_pow_left₀ (by positivity) hL 2)
    _ = _ := by
      have hp : (Z ^ d) ^ 2 = Z ^ (2 * d) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hZ.le]
        congr 1; push_cast; ring
      rw [mul_pow, hp, Real.rpow_sub hZ]
      ring

lemma stage1Vertex_low_inverse_power_cancel (Z d α : ℝ) (hZ : 0 < Z) :
    Z ^ (99967 / 120000 - 7 * d / 4 + α) * (Z ^ d) ^ 2 / Z ^ (99967 / 120000 : ℝ) =
      Z ^ (d / 4 + α) := by
  have hp : (Z ^ d) ^ 2 = Z ^ (2 * d) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hZ.le]
    congr 1; push_cast; ring
  rw [hp, ← Real.rpow_add hZ, ← Real.rpow_sub hZ]
  congr 1
  ring

lemma stage1Vertex_low_inverse_sqrt_normalized (q C B Z L d α H E : ℝ) (n : ℕ)
    (hq : 0 < q) (hC : 0 ≤ C) (_hB : 0 ≤ B) (hZ : 0 < Z) (hL : 0 < L) (hH : 1 ≤ H)
    (hE : 0 ≤ E) (hEL : E ≤ C * H ^ n * Z ^ (99967 / 120000 - 7 * d / 4 + α)) (hLB : L ≤ B * Z ^ d) :
    Real.sqrt E / Real.sqrt (q * Z ^ (99967 / 120000 : ℝ) / L ^ 2) ≤
      Real.sqrt (C * B ^ 2 / q) * H ^ n * Z ^ (d / 8 + α / 2) := by
  have hratio : E / (q * Z ^ (99967 / 120000 : ℝ) / L ^ 2) ≤ (C * B ^ 2 / q) * H ^ n * Z ^ (d / 4 + α) := by
    calc
      _ ≤ (C * H ^ n * Z ^ (99967 / 120000 - 7 * d / 4 + α)) / (q * Z ^ (99967 / 120000 : ℝ) / L ^ 2) :=
        div_le_div_of_nonneg_right hEL (by positivity)
      _ = (C * H ^ n * Z ^ (99967 / 120000 - 7 * d / 4 + α)) * L ^ 2 / (q * Z ^ (99967 / 120000 : ℝ)) := by
        field_simp
      _ ≤ (C * H ^ n * Z ^ (99967 / 120000 - 7 * d / 4 + α)) * (B * Z ^ d) ^ 2 /
          (q * Z ^ (99967 / 120000 : ℝ)) := by gcongr
      _ = (C * B ^ 2 / q) * H ^ n *
          (Z ^ (99967 / 120000 - 7 * d / 4 + α) * (Z ^ d) ^ 2 / Z ^ (99967 / 120000 : ℝ)) := by ring
      _ = _ := by rw [stage1Vertex_low_inverse_power_cancel Z d α hZ]
  rw [← Real.sqrt_div hE]
  apply (Real.sqrt_le_sqrt hratio).trans
  rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity)]
  have hp : Real.sqrt (Z ^ (d / 4 + α)) = Z ^ (d / 8 + α / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hZ.le]
    congr 1; ring
  rw [hp]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_self_iff.mpr (Or.inr (one_le_pow₀ hH))) (by positivity))
    (by positivity)

/-! ### Unselected-slot `Z^{-d/2}` mass saving -/

lemma stage1Vertex_canonical_slot_inverse_three_halves : ∃ C : ℝ, 0 < C ∧
    ∀ (T : Finset HeckeIdealSeries.PrimeIdeal) (_hT : ∀ P ∈ T, Supported P.val),
      (∑ a : canonicalSlotSupport T, elementNorm a.val ^ (-(3 / 2 : ℝ))) ≤ C := by
  obtain ⟨C, hC, hb⟩ := ProbeGramCommon.supportedIdeal_rpow_finite_bound (-3 / 2) (by norm_num)
  refine ⟨C, hC, ?_⟩
  intro T hT
  let f : T → SupportedIdeal := fun P => ⟨P.val.val, hT P.val P.property⟩
  have hf : Function.Injective f := by
    intro P Q h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun I : SupportedIdeal => I.val) h
  have he : (∑ a : canonicalSlotSupport T, elementNorm a.val ^ (-(3 / 2 : ℝ))) =
      ∑ I ∈ Finset.univ.image f, ProbeGramCommon.gramIdealNorm I ^ (-3 / 2 : ℝ) := by
    rw [Finset.sum_image (fun P _ Q _ h => hf h)]
    have hh := (canonicalSlotEquiv T hT).sum_comp (fun a => elementNorm a.val ^ (-(3 / 2 : ℝ)))
    rw [← hh]
    apply Finset.sum_congr rfl
    intro P _
    rw [canonicalSlotEquiv_norm]
    dsimp [ProbeGramCommon.gramIdealNorm, f]
    norm_num
  rw [he]
  exact hb _

theorem stage1Vertex_lowUnselectedMass_bound (K : ℕ) (a M : ℝ) (ha : 0 < a) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (ell : Fin K → ℝ) (Z : ℝ), 0 < Z →
    ∀ (T : Fin K → Finset HeckeIdealSeries.PrimeIdeal) (_hT : ∀ i P, P ∈ T i → Supported P.val),
      (∀ i P, P ∈ T i → a * Z ^ (ell i) ≤ (Ideal.absNorm P.val : ℝ)) →
    ∀ (J : Finset (Fin K)) (W : Fin K → ℝ → ℂ) (P : Fin K → ℝ),
      (∀ i x, ‖W i x‖ ≤ M) →
      (∑ x : LowUnselectedTuple (fun i => canonicalSlotSupport (T i)) J,
        ‖lowUnselectedWeight (fun i => canonicalSlotSupport (T i)) J W P x‖ *
          elementNorm (∏ i : J, (x i).val) ^ (-(1 / 2 : ℝ))) ≤
        C * Z ^ (-lowUnselectedLength ell J / 2) := by
  obtain ⟨C, hC, hb⟩ := stage1Vertex_canonical_slot_inverse_three_halves
  let B := max 1 (C * M * a ^ (-(1 / 2 : ℝ)))
  have hB1 : 1 ≤ B := le_max_left _ _
  refine ⟨B ^ K, by positivity, ?_⟩
  intro ell Z hZ T hT hnorm J W P hW
  simp_rw [lowUnselectedWeight_norm_identity _ (fun i => canonicalSlotSupport_nonzero _ (hT i))]
  rw [← Fintype.prod_sum (fun (i : J) (x : canonicalSlotSupport (T i.val)) =>
    elementNorm x.val ^ (-2 : ℝ) * ‖W i.val (elementNorm x.val / P i.val)‖)]
  have hslot (i : J) :
      (∑ x : canonicalSlotSupport (T i.val),
        elementNorm x.val ^ (-2 : ℝ) * ‖W i.val (elementNorm x.val / P i.val)‖) ≤
      B * Z ^ (-ell i.val / 2) := by
    have hlo_pos : 0 < a * Z ^ (ell i.val) := mul_pos ha (Real.rpow_pos_of_pos hZ _)
    have hterm (x : canonicalSlotSupport (T i.val)) :
        elementNorm x.val ^ (-2 : ℝ) * ‖W i.val (elementNorm x.val / P i.val)‖ ≤
          (M * a ^ (-(1 / 2 : ℝ)) * Z ^ (-ell i.val / 2)) * elementNorm x.val ^ (-(3 / 2 : ℝ)) := by
      obtain ⟨Q, hQ, hQx⟩ := Finset.mem_image.mp x.property
      have hxlo : a * Z ^ (ell i.val) ≤ elementNorm x.val := by
        rw [← hQx, primaryTuple_norm Q (hT i.val Q hQ)]
        exact hnorm i.val Q hQ
      have hxpos : 0 < elementNorm x.val := lt_of_lt_of_le hlo_pos hxlo
      have hsplit : elementNorm x.val ^ (-2 : ℝ) =
          elementNorm x.val ^ (-(1 / 2 : ℝ)) * elementNorm x.val ^ (-(3 / 2 : ℝ)) := by
        rw [← Real.rpow_add hxpos]; norm_num
      have hhalf : elementNorm x.val ^ (-(1 / 2 : ℝ)) ≤ a ^ (-(1 / 2 : ℝ)) * Z ^ (-ell i.val / 2) := by
        have hinv : elementNorm x.val ^ (-(1 / 2 : ℝ)) ≤ (a * Z ^ (ell i.val)) ^ (-(1 / 2 : ℝ)) := by
          rw [Real.rpow_neg hxpos.le, Real.rpow_neg hlo_pos.le]
          exact inv_anti₀ (Real.rpow_pos_of_pos hlo_pos _)
            (Real.rpow_le_rpow hlo_pos.le hxlo (by norm_num))
        apply hinv.trans_eq
        rw [Real.mul_rpow ha.le (Real.rpow_nonneg hZ.le _), ← Real.rpow_mul hZ.le]
        congr 2; ring
      rw [hsplit]
      calc
        _ ≤ (a ^ (-(1 / 2 : ℝ)) * Z ^ (-ell i.val / 2)) * elementNorm x.val ^ (-(3 / 2 : ℝ)) * M :=
          mul_le_mul (mul_le_mul_of_nonneg_right hhalf (Real.rpow_nonneg hxpos.le _)) (hW i.val _)
            (norm_nonneg _) (by positivity)
        _ = _ := by ring
    calc
      _ ≤ ∑ x : canonicalSlotSupport (T i.val),
          (M * a ^ (-(1 / 2 : ℝ)) * Z ^ (-ell i.val / 2)) * elementNorm x.val ^ (-(3 / 2 : ℝ)) :=
        Finset.sum_le_sum (fun x _ => hterm x)
      _ = (M * a ^ (-(1 / 2 : ℝ)) * Z ^ (-ell i.val / 2)) *
          (∑ x : canonicalSlotSupport (T i.val), elementNorm x.val ^ (-(3 / 2 : ℝ))) :=
        (Finset.mul_sum ..).symm
      _ ≤ (M * a ^ (-(1 / 2 : ℝ)) * Z ^ (-ell i.val / 2)) * C :=
        mul_le_mul_of_nonneg_left (hb _ (hT i.val)) (by positivity)
      _ = (C * M * a ^ (-(1 / 2 : ℝ))) * Z ^ (-ell i.val / 2) := by ring
      _ ≤ B * Z ^ (-ell i.val / 2) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hZ.le _)
  have hc : J.card ≤ K := by simpa using Finset.card_le_card (Finset.subset_univ J)
  calc
    _ ≤ ∏ i : J, B * Z ^ (-ell i.val / 2) :=
      Finset.prod_le_prod (fun _ _ => Finset.sum_nonneg (fun _ _ =>
        mul_nonneg (Real.rpow_nonneg (by unfold elementNorm; positivity) _) (norm_nonneg _)))
        (fun i _ => hslot i)
    _ = B ^ J.card * Z ^ (-lowUnselectedLength ell J / 2) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_coe,
        ← Real.rpow_sum_of_pos hZ, Finset.sum_coe_sort J (fun i => -ell i / 2), lowUnselectedLength]
      simp_rw [neg_div, Finset.sum_neg_distrib, ← Finset.sum_div]
    _ ≤ B ^ K * Z ^ (-lowUnselectedLength ell J / 2) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hB1 hc) (Real.rpow_nonneg hZ.le _)

/-! ### Physical inverse energy and central/remote Gaussian dyads -/

theorem stage1Vertex_low_selected_physical_energy (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀ P ∈ S, P.IsMaximal) (hbad : fixedBadPrimes ⊆ S)
    (K : ℕ) (Ck ε : ℝ) (hCk : 0 < Ck) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ degree : ℕ, ∃ C Z₀ : ℝ, 0 < C ∧ 1 < Z₀ ∧
    ∀ (Z d ell0 shift : ℝ), Z₀ ≤ Z → 0 ≤ d → d ≤ 20033 / 120000 → 0 ≤ ell0 →
      ell0 ≤ 20033 / 120000 - d + ε → |shift| ≤ ε →
    ∀ (R : Finset O), (∀ z ∈ R, z ≠ 0 ∧ elementNorm z ≤ Ck * Z ^ (99967 / 120000 - 2 * d)) →
    ∀ (T : Fin K → Finset HeckeIdealSeries.PrimeIdeal), (∀ i P, P ∈ T i → Supported P.val) →
      (∀ i P, P ∈ T i → P.val ∉ S) → Pairwise (fun i j => Disjoint (T i) (T j)) →
    ∀ (J : Finset (Fin K)) (H : SelectedSlot J → ℝ),
      (∀ i, 1 ≤ H i) → (∀ i P, P ∈ T i.val → (Ideal.absNorm P.val : ℝ) ≤ H i) → (∏ i, H i) ≤ Z ^ ell0 →
    ∀ (W : Fin K → ℝ → ℂ), (∀ i x, ‖W i x‖ ≤ 1) → ∀ (Y : Fin K → ℝ) (t : ℝ) (σ : RayRing),
      (∑ z ∈ R, ‖lowSelectedInverseRow Finset.univ
        (lowSelectedWeight η (fun i => canonicalSlotSupport (T i)) J W Y t)
        η S hS (lowSelectedIdeal (fun i => canonicalSlotSupport (T i)) J) (Z ^ (1 + ell0 + shift)) t σ z‖ ^ 2) ≤
        C * (1 + ‖t‖) ^ degree * Z ^ ((99967 / 120000 - 7 * d / 4) + 507 * ε) := by
  obtain ⟨degree, C, Z₀, hC, hZ₀, he⟩ := InverseReflectedPhase.stage1Vertex_low_original_completed_energy
    (lowReflectionPeriod η S hS) (lowReflectionPeriod_ne_zero η S hS)
    (1 : Id) squarefree_one (lowReflectionMask η S hS) (lowReflectionMask_ne_zero η S hS)
    (lowReflectionMask_bad η S hS hbad).1 (lowReflectionMask_bad η S hS hbad).2
    (lowReflectionMask_period η S hS) (lowReflectionMask_bad_ideals η S hS hbad)
    (1 / 2) 2 (by norm_num) gaussianFixedWindow gaussianFixedWindow_support gaussianFixedWindow_contDiff
    Ck ε hCk hε hε1 K
  let C0 := (lowCorrectionEnergy + 1) * ((Fintype.card RayCharacter : ℝ) + 1) * 6 * C
  have hC0 : 0 < C0 := by have hh := lowCorrectionEnergy_nonneg; dsimp [C0]; positivity
  refine ⟨degree, C0, Z₀, hC0, hZ₀, ?_⟩
  intro Z d ell0 shift hZ hd hd1 hell hellcap hshift R hR T hT hout hdis J H hH1 hH hprod W hW Y t σ
  let L := fun i : SelectedSlot J => lowPrimeIdealList (lowPeriodPrimeList η S hS (T i.val))
  have hLP (i : SelectedSlot J) : lowPeriodPrimeList η S hS (T i.val) ⊆ T i.val := Finset.filter_subset _ _
  have hLS (i : SelectedSlot J) : ∀ P ∈ lowPeriodPrimeList η S hS (T i.val), Supported P.val :=
    fun P hP => hT i.val P (hLP i hP)
  have hlists : Pairwise (fun i j => Disjoint (L i) (L j)) :=
    lowPrimeIdealList_disjoint _ (lowPeriodPrimeList_disjoint η S hS _
      (fun i j hij => hdis (fun h => hij (Subtype.ext h))))
  have hparents : ∀ I ∈ lowIdealRows R, I ≠ 0 ∧ (Ideal.absNorm I : ℝ) ≤ Ck * Z ^ (99967 / 120000 - 2 * d) :=
    fun I hI => ⟨lowIdealRows_nonzero R (fun z hz => (hR z hz).1) I hI,
      lowIdealRows_norm_bound R _ (fun z hz => (hR z hz).2) I hI⟩
  have hcard : Fintype.card (SelectedSlot J) ≤ K := by
    simpa only [Fintype.card_coe, Finset.card_univ, Fintype.card_fin] using
      Finset.card_le_card (Finset.subset_univ (Finset.univ \ J))
  have hrow (χ : RayCharacter) (u : Oˣ) :
      (∑ I ∈ lowIdealRows R, ‖lowActualIdealPolynomial L
        (fun i I => lowSingleSlotWeight η (W i.val) (Y i.val) t (primaryIdealGenerator I))
        (rowTwist (physicalRayPeriodicBase η S hS σ χ) (lowReflectionMask η S hS)
          (cubicIdealGenerator (1 : Id)) (u.val * cubicIdealGenerator I))
        (CompletedHeight.normTwistedSource gaussianFixedWindow t) (Z ^ (1 + ell0 + shift))‖ ^ 2) ≤
          C * (1 + ‖t‖) ^ degree * Z ^ ((99967 / 120000 - 7 * d / 4) + 507 * ε) := by
    convert he Z d ell0 shift hZ hd hd1 hell hellcap hshift (lowIdealRows R) hparents hcard L H
      hlists (fun i => lowPrimeIdealList_maximal _)
      (fun i P hP => (lowPrimeIdealList_good_odd _ (hLS i) P hP).1)
      (fun i => lowPrimeIdealList_prime _)
      (fun i P hP => (lowPrimeIdealList_good_odd _ (hLS i) P hP).2)
      hH1 (fun i => lowPrimeIdealList_norm _ _ (fun P hP => hH i P (hLP i hP))) hprod
      (physicalRayPeriodicBase η S hS σ χ) (lowReflectionPeriod_actual η S hS σ χ).2
      (lowReflectionPeriod_actual η S hS σ χ).1 u t
      (fun i P => lowSingleSlotWeight η (W i.val) (Y i.val) t (primaryIdealGenerator P.val))
      (fun i P => low_actual_ideal_weight_bound η (W i.val) (hW i.val) (Y i.val) t P.val) using 1
    apply Finset.sum_congr rfl
    intro I _
    congr 2
    unfold lowActualIdealPolynomial
    congr 1
    ext p
    simp
  apply (lowSelectedInverseRow_actual_reflected_energy η S hS hbad T hT hout hdis J W Y
    (Z ^ (1 + ell0 + shift)) t σ R (fun z hz => (hR z hz).1)).trans
  have hh := Finset.sum_le_sum (fun χ (_ : χ ∈ (Finset.univ : Finset RayCharacter)) =>
    Finset.sum_le_sum (fun u (_ : u ∈ (Finset.univ : Finset Oˣ)) => hrow χ u))
  have hm := mul_le_mul_of_nonneg_left hh lowCorrectionEnergy_nonneg
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, low_unit_card] at hm
  simp only [Nat.cast_ofNat, Real.norm_eq_abs] at hm ⊢
  apply hm.trans
  dsimp [C0]
  have hc0 := lowCorrectionEnergy_nonneg
  have hcount : 0 ≤ (Fintype.card RayCharacter : ℝ) := Nat.cast_nonneg _
  have hzpos : 0 ≤ Z ^ ((99967 / 120000 - 7 * d / 4) + 507 * ε) :=
    Real.rpow_nonneg (le_trans zero_le_one (hZ₀.le.trans hZ)) _
  have htpos : 0 ≤ (1 + |t|) ^ degree := by positivity
  calc
    _ = (lowCorrectionEnergy * (Fintype.card RayCharacter : ℝ) * 6 * C) * (1 + |t|) ^ degree *
        Z ^ ((99967 / 120000 - 7 * d / 4) + 507 * ε) := by ring
    _ ≤ _ := by gcongr <;> linarith

theorem stage1Vertex_low_selected_nominal_energy (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀ P ∈ S, P.IsMaximal) (hbad : fixedBadPrimes ⊆ S)
    {K : ℕ} (ell : Fin K → ℝ) (hell : ∀ i, 0 ≤ ell i) (hsum : ∑ i, ell i ≤ 20033 / 120000)
    (Ck b ε : ℝ) (hCk : 0 < Ck) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ degree : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in Filter.atTop, 1 < Z ∧
    ∀ (T : Fin K → Finset HeckeIdealSeries.PrimeIdeal), (∀ i P, P ∈ T i → Supported P.val) →
      (∀ i P, P ∈ T i → P.val ∉ S) → Pairwise (fun i j => Disjoint (T i) (T j)) →
      (∀ i P, P ∈ T i → (Ideal.absNorm P.val : ℝ) ≤ b * Z ^ (ell i)) →
    ∀ (J : Finset (Fin K)) (R : Finset O),
      (∀ z ∈ R, z ≠ 0 ∧ elementNorm z ≤ Ck * Z ^ (99967 / 120000 - 2 * lowUnselectedLength ell J)) →
    ∀ X : ℝ, 0 < X → Z ^ (1 + lowSelectedLength ell J - ε / 2) ≤ X → X ≤ Z ^ (1 + lowSelectedLength ell J + ε / 2) →
    ∀ (W : Fin K → ℝ → ℂ), (∀ i x, ‖W i x‖ ≤ 1) → ∀ (Y : Fin K → ℝ) (t : ℝ) (σ : RayRing),
      (∑ z ∈ R, ‖lowSelectedInverseRow Finset.univ
        (lowSelectedWeight η (fun i => canonicalSlotSupport (T i)) J W Y t)
        η S hS (lowSelectedIdeal (fun i => canonicalSlotSupport (T i)) J) X t σ z‖ ^ 2) ≤
        C * (1 + ‖t‖) ^ degree * Z ^ ((99967 / 120000 - 7 * lowUnselectedLength ell J / 4) + 507 * ε) := by
  obtain ⟨degree, C, Z₀, hC, _, he⟩ := stage1Vertex_low_selected_physical_energy η S hS hbad K Ck ε hCk hε hε1
  refine ⟨degree, C, hC, ?_⟩
  filter_upwards [eventually_low_selected_caps ell hell b ε hε, Filter.eventually_ge_atTop Z₀] with Z hc hZ
  refine ⟨hc.1, ?_⟩
  intro T hT hout hdis hnorm J R hR X hX hXlo hXhi W hW Y t σ
  obtain ⟨hd, hd1, hs, hscap⟩ := stage1Vertex_lowLength_bounds ell hell hsum J
  have hscale := lowCentralShift_scale Z X (lowSelectedLength ell J + ε / 2) hc.1 hX
  rw [← hscale]
  exact he Z (lowUnselectedLength ell J) (lowSelectedLength ell J + ε / 2)
    (lowCentralShift Z X (lowSelectedLength ell J + ε / 2)) hZ hd hd1 (by linarith) (by linarith)
    (lowCentralShift_bound Z X (lowSelectedLength ell J) ε hc.1 hX hε.le hXlo hXhi)
    R hR T hT hout hdis J (fun i => max 1 (b * Z ^ (ell i.val)))
    (fun i => le_max_left _ _)
    (fun i P hP => (hnorm i.val P hP).trans (le_max_right _ _)) (hc.2 J) W hW Y t σ

theorem stage1Vertex_low_physical_inverse_normalized (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀ P ∈ S, P.IsMaximal) (hbad : fixedBadPrimes ⊆ S)
    {K : ℕ} (ell : Fin K → ℝ) (hell : ∀ i, 0 ≤ ell i) (hsum : ∑ i, ell i ≤ 20033 / 120000)
    (a b aCut bCut ε : ℝ) (ha : 0 < a) (haCut : 0 < aCut) (hbCut : 0 < bCut)
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ degree : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in Filter.atTop, 1 < Z ∧
    ∀ (T : Fin K → Finset HeckeIdealSeries.PrimeIdeal), (∀ i P, P ∈ T i → Supported P.val) →
      (∀ i P, P ∈ T i → P.val ∉ S) → Pairwise (fun i j => Disjoint (T i) (T j)) →
      (∀ i P, P ∈ T i → a * Z ^ (ell i) ≤ (Ideal.absNorm P.val : ℝ) ∧ (Ideal.absNorm P.val : ℝ) ≤ b * Z ^ (ell i)) →
    ∀ (J : Finset (Fin K)) (p : LowUnselectedTuple (fun i => canonicalSlotSupport (T i)) J),
    ∀ X : ℝ, 0 < X → Z ^ (1 + lowSelectedLength ell J - ε / 2) ≤ X → X ≤ Z ^ (1 + lowSelectedLength ell J + ε / 2) →
    ∀ (W : Fin K → ℝ → ℂ), (∀ i x, ‖W i x‖ ≤ 1) → ∀ t : ℝ,
      let L := elementNorm (∏ i : J, (p i).val)
      let Q := lowPhysicalScale (calibrationForSet S hS)
        (Z ^ (2111 / 6000 : ℝ) / L) (Z ^ (19249 / 40000 : ℝ) / L)
      ∀ (hX0 : 0 < Z ^ (2111 / 6000 : ℝ) / L) (hY0 : 0 < Z ^ (19249 / 40000 : ℝ) / L),
      (Real.sqrt Q)⁻¹ / (2 * Real.pi) *
        lowInverseMass (calibrationForSet S hS) aCut bCut haCut hbCut
          (Z ^ (2111 / 6000 : ℝ) / L) (Z ^ (19249 / 40000 : ℝ) / L) hX0 hY0
          (lowSelectedInverseRow Finset.univ
            (lowSelectedWeight η (fun i => canonicalSlotSupport (T i)) J W (fun i => Z ^ (ell i)) t)
            η S hS (lowSelectedIdeal (fun i => canonicalSlotSupport (T i)) J) X t) ≤
        C * (1 + ‖t‖) ^ degree * Z ^ (lowUnselectedLength ell J / 8 + 507 * ε / 2) := by
  let q := elementNorm (calibrationForSet S hS).generator
  let c := (min 1 a) ^ K
  let B := (max 1 b) ^ K
  have hq : 0 < q := calibration_elementNorm_pos _
  have hc : 0 < c := by dsimp [c]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  let Ck := 2 * bCut * (q / c ^ 2)
  have hCk : 0 < Ck := by dsimp [Ck]; positivity
  obtain ⟨degree, C, ZC, hbound⟩ := stage1Vertex_low_selected_nominal_energy η S hS hbad
    ell hell hsum Ck b ε hCk hε hε1
  let C0 := ((Fintype.card RayRing : ℝ) + 1) * Real.sqrt (C * B ^ 2 / q) / (2 * Real.pi)
  have hC0 : 0 < C0 := by dsimp [C0]; positivity
  refine ⟨degree, C0, hC0, ?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1, ?_⟩
  intro T hT hout hdis hnorm J p X hX hXlo hXhi W hW t
  dsimp only
  let L := elementNorm (∏ i : J, (p i).val)
  let Q := lowPhysicalScale (calibrationForSet S hS)
    (Z ^ (2111 / 6000 : ℝ) / L) (Z ^ (19249 / 40000 : ℝ) / L)
  intro hX0 hY0
  have hz : 0 < Z := lt_trans zero_lt_one hZ.1
  have hL : 0 < L := lowUnselectedProduct_norm_pos _
    (fun i n hn => canonicalSlotSupport_nonzero _ (hT i) n hn) J p
  have hnormE (i : Fin K) (n : O) (hn : n ∈ canonicalSlotSupport (T i)) :
      a * Z ^ (ell i) ≤ elementNorm n ∧ elementNorm n ≤ b * Z ^ (ell i) := by
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hn
    rw [primaryTuple_norm P (hT i P hP)]
    exact hnorm i P hP
  have hLlo : c * Z ^ (lowUnselectedLength ell J) ≤ L :=
    lowUnselectedProduct_norm_lower ell a Z ha hz _ (fun i n hn => (hnormE i n hn).1) J p
  have hLhi : L ≤ B * Z ^ (lowUnselectedLength ell J) :=
    lowUnselectedProduct_norm_upper_nominal ell b Z hz _ (fun i n hn => (hnormE i n hn).2) J p
  have hQ : 0 < Q := lowPhysicalScale_pos _ _ _ hX0 hY0
  let R := lowNumeratorRows aCut bCut haCut hbCut Q hQ
  let row := lowSelectedInverseRow Finset.univ
    (lowSelectedWeight η (fun i => canonicalSlotSupport (T i)) J W (fun i => Z ^ (ell i)) t)
    η S hS (lowSelectedIdeal (fun i => canonicalSlotSupport (T i)) J) X t
  have hrows : ∀ z ∈ R, z ≠ 0 ∧ elementNorm z ≤ Ck * Z ^ (99967 / 120000 - 2 * lowUnselectedLength ell J) := by
    intro z hzR
    refine ⟨lowNumeratorRows_nonzero aCut bCut haCut hbCut Q hQ z hzR, ?_⟩
    apply (lowNumeratorRows_norm_bound aCut bCut haCut hbCut Q hQ z hzR).trans
    have hh := mul_le_mul_of_nonneg_left
      (stage1Vertex_lowPhysicalScale_nominal_bound (calibrationForSet S hS)
        Z L c (lowUnselectedLength ell J) hz hc hLlo)
      (show 0 ≤ 2 * bCut by positivity)
    simpa only [Ck, mul_assoc] using hh
  have he (σ : RayRing) : (∑ z ∈ R, ‖row σ z‖ ^ 2) ≤
      C * (1 + ‖t‖) ^ degree * Z ^ (99967 / 120000 - 7 * lowUnselectedLength ell J / 4 + 507 * ε) :=
    hZ.2 T hT hout hdis (fun i P hP => (hnorm i P hP).2) J R hrows X hX hXlo hXhi W hW
      (fun i => Z ^ (ell i)) t σ
  have hn (σ : RayRing) : Real.sqrt (∑ z ∈ R, ‖row σ z‖ ^ 2) / Real.sqrt Q ≤
      Real.sqrt (C * B ^ 2 / q) * (1 + ‖t‖) ^ degree * Z ^ (lowUnselectedLength ell J / 8 + 507 * ε / 2) := by
    dsimp only [Q]
    rw [stage1Vertex_lowPhysicalScale_source _ Z L hz]
    exact stage1Vertex_low_inverse_sqrt_normalized q C B Z L (lowUnselectedLength ell J) (507 * ε)
      (1 + ‖t‖) (∑ z ∈ R, ‖row σ z‖ ^ 2) degree hq ZC.le hB.le hz hL
      (le_add_of_nonneg_right (norm_nonneg t))
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (he σ) hLhi
  change (Real.sqrt Q)⁻¹ / (2 * Real.pi) * (∑ σ : RayRing, Real.sqrt (∑ z ∈ R, ‖row σ z‖ ^ 2)) ≤ _
  calc
    _ = (∑ σ : RayRing, Real.sqrt (∑ z ∈ R, ‖row σ z‖ ^ 2) / Real.sqrt Q) / (2 * Real.pi) := by
      rw [← Finset.sum_div]; ring
    _ ≤ (∑ σ : RayRing, Real.sqrt (C * B ^ 2 / q) * (1 + ‖t‖) ^ degree *
        Z ^ (lowUnselectedLength ell J / 8 + 507 * ε / 2)) / (2 * Real.pi) :=
      div_le_div_of_nonneg_right (Finset.sum_le_sum (fun σ _ => hn σ)) (by positivity)
    _ ≤ _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      dsimp [C0]
      calc
        _ = ((Fintype.card RayRing : ℝ) * Real.sqrt (C * B ^ 2 / q) / (2 * Real.pi)) *
            (1 + |t|) ^ degree * Z ^ (lowUnselectedLength ell J / 8 + 507 * ε / 2) := by ring
        _ ≤ _ := by gcongr; linarith

theorem stage1Vertex_low_central_compensated_tuple (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀ P ∈ S, P.IsMaximal) (hbad : fixedBadPrimes ⊆ S)
    {K : ℕ} (ell : Fin K → ℝ) (hell : ∀ i, 0 ≤ ell i) (hsum : ∑ i, ell i ≤ 20033 / 120000)
    (a b ε : ℝ) (ha : 0 < a) (hε : 0 < ε) (hε1 : ε < 1)
    (W0 W1 : ℝ → ℂ) (a0 b0 a1 b1 M : ℝ) (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hab1 : a1 < b1) (hM : 0 ≤ M)
    (hW0 : Function.support W0 ⊆ Set.Icc a0 b0) (hW1 : Function.support W1 ⊆ Set.Icc a1 b1)
    (hW0s : ContDiff ℝ ∞ W0) (hW1s : ContDiff ℝ ∞ W1) (hWM : ∀ x, ‖W1 x‖ ≤ M) :
    ∃ degree : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in Filter.atTop, 1 < Z ∧
    ∀ (T : Fin K → Finset HeckeIdealSeries.PrimeIdeal), (∀ i P, P ∈ T i → Supported P.val) →
      (∀ i P, P ∈ T i → P.val ∉ S) → Pairwise (fun i j => Disjoint (T i) (T j)) →
      (∀ i P, P ∈ T i → a * Z ^ (ell i) ≤ (Ideal.absNorm P.val : ℝ) ∧ (Ideal.absNorm P.val : ℝ) ≤ b * Z ^ (ell i)) →
    ∀ (J : Finset (Fin K)) (X : ℝ), 0 < X →
      Z ^ (1 + lowSelectedLength ell J - ε / 2) ≤ X → X ≤ Z ^ (1 + lowSelectedLength ell J + ε / 2) →
    ∀ (W : Fin K → ℝ → ℂ), (∀ i x, ‖W i x‖ ≤ 1) → ∀ t : ℝ,
      ‖∑ p : ∀ i, canonicalSlotSupport (T i),
        compensationSubsetWeight η W (fun i => Z ^ (ell i)) (fun i => (p i).val) J *
          compensationRowTest η (calibrationForSet S hS) W0 W1 (fun i => (p i).val) J
            (Z ^ (2111 / 6000 : ℝ)) (Z ^ (19249 / 40000 : ℝ)) X t *
          selectedSlotFactor W (fun i => Z ^ (ell i)) (fun i => (p i).val) J t‖ ≤
        C * (1 + ‖t‖) ^ degree * Z ^ (268847 / 1440000 + 254 * ε) := by
  obtain ⟨Cg, hCg, hgram⟩ := compensation_tuple_actual_gram ε hε hε1 W0 W1
    a0 b0 a1 b1 M ha0 ha1 hab1 hM hW0 hW1 hW0s hW1s hWM S hS hbad
  obtain ⟨degree, Ci, hCi, hinverse⟩ := stage1Vertex_low_physical_inverse_normalized η S hS hbad
    ell hell hsum a b (a0 * a1) (max 1 (b0 * b1)) ε ha (mul_pos ha0 ha1)
    (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) hε hε1.le
  obtain ⟨Cu, hCu, hmass⟩ := stage1Vertex_lowUnselectedMass_bound K a 1 ha (by norm_num)
  let q := elementNorm (calibrationForSet S hS).generator
  have hq : 0 < q := calibration_elementNorm_pos _
  let C0 := Cg * Ci * Real.sqrt (3 * q) * Cu
  have hC0 : 0 < C0 := by dsimp [C0]; positivity
  refine ⟨degree, C0, hC0, ?_⟩
  filter_upwards [hinverse, eventually_stage1Vertex_slot_scales (calibrationForSet S hS)
    ell hell hsum (max 1 b) (le_max_left _ _)] with Z hInv hScale
  refine ⟨hInv.1, ?_⟩
  intro T hT hout hdis hnorm J X hX hXlo hXhi W hW t
  let slots := fun i => canonicalSlotSupport (T i)
  let Yp := fun i => Z ^ (ell i)
  let d := lowUnselectedLength ell J
  have hz : 0 < Z := lt_trans zero_lt_one hInv.1
  have hd : 0 ≤ d := (stage1Vertex_lowLength_bounds ell hell hsum J).1
  have hslots : ∀ i n, n ∈ slots i → n ≠ 0 := fun i => canonicalSlotSupport_nonzero _ (hT i)
  have hnormE : ∀ i n, n ∈ slots i → elementNorm n ≤ max 1 b * Z ^ (ell i) := by
    intro i n hn
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hn
    rw [primaryTuple_norm P (hT i P hP)]
    exact (hnorm i P hP).2.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
  have hs := hScale.2 slots hslots hnormE J
  have hg := hgram K η slots hslots J W Yp (Z ^ (2111 / 6000 : ℝ)) (Z ^ (19249 / 40000 : ℝ)) X t
    (by positivity) (by positivity) hX (fun p => (hs p).1) (fun p => (hs p).2.1)
  apply hg.trans
  let G := Z ^ (268847 / 1440000 + (19249 / 80000) * ε : ℝ)
  let V := Ci * (1 + ‖t‖) ^ degree * Z ^ (d / 8 + 507 * ε / 2)
  have hGV : G * V ≤ Ci * (1 + ‖t‖) ^ degree * Z ^ (268847 / 1440000 + d / 8 + 254 * ε) := by
    dsimp only [G, V]
    calc
      _ = Ci * (1 + ‖t‖) ^ degree *
          (Z ^ (268847 / 1440000 + (19249 / 80000) * ε : ℝ) * Z ^ (d / 8 + 507 * ε / 2)) := by ring
      _ ≤ _ := by
        rw [← Real.rpow_add hz]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact Real.rpow_le_rpow_of_exponent_le hInv.1.le (by linarith)
  have hterm (p : LowUnselectedTuple slots J) :
      let L := elementNorm (∏ i : J, (p i).val)
      let Q := lowPhysicalScale (calibrationForSet S hS)
        (Z ^ (2111 / 6000 : ℝ) / L) (Z ^ (19249 / 40000 : ℝ) / L)
      ‖lowUnselectedWeight slots J W Yp p‖ * ((Real.sqrt Q)⁻¹ / (2 * Real.pi)) *
        lowGramFactor (calibrationForSet S hS)
          (Z ^ (2111 / 6000 : ℝ) / L) (Z ^ (19249 / 40000 : ℝ) / L) ε *
        lowInverseMass (calibrationForSet S hS) (a0 * a1) (max 1 (b0 * b1)) (mul_pos ha0 ha1)
          (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
          (Z ^ (2111 / 6000 : ℝ) / L) (Z ^ (19249 / 40000 : ℝ) / L)
          (div_pos (by positivity) (lowUnselectedProduct_norm_pos slots hslots J p))
          (div_pos (by positivity) (lowUnselectedProduct_norm_pos slots hslots J p))
          (lowSelectedInverseRow Finset.univ (lowSelectedWeight η slots J W Yp t)
            η S hS (lowSelectedIdeal slots J) X t) ≤
      (Ci * Real.sqrt (3 * q) * (1 + ‖t‖) ^ degree * Z ^ (268847 / 1440000 + d / 8 + 254 * ε)) *
        (‖lowUnselectedWeight slots J W Yp p‖ * L ^ (-(1 / 2 : ℝ))) := by
    dsimp only
    let L := elementNorm (∏ i : J, (p i).val)
    let Q := lowPhysicalScale (calibrationForSet S hS)
      (Z ^ (2111 / 6000 : ℝ) / L) (Z ^ (19249 / 40000 : ℝ) / L)
    have hL := lowUnselectedProduct_norm_pos slots hslots J p
    have hgb := (hs p).2.2 ε hε.le
    have hib := hInv.2 T hT hout hdis hnorm J p X hX hXlo hXhi W hW t
      (div_pos (by positivity) hL) (div_pos (by positivity) hL)
    have hgn : 0 ≤ lowGramFactor (calibrationForSet S hS)
        (Z ^ (2111 / 6000 : ℝ) / L) (Z ^ (19249 / 40000 : ℝ) / L) ε :=
      Real.sqrt_nonneg _
    calc
      _ = (‖lowUnselectedWeight slots J W Yp p‖ *
          lowGramFactor (calibrationForSet S hS)
            (Z ^ (2111 / 6000 : ℝ) / L) (Z ^ (19249 / 40000 : ℝ) / L) ε) *
          (((Real.sqrt Q)⁻¹ / (2 * Real.pi)) *
          lowInverseMass (calibrationForSet S hS) (a0 * a1) (max 1 (b0 * b1)) (mul_pos ha0 ha1)
            (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
            (Z ^ (2111 / 6000 : ℝ) / L) (Z ^ (19249 / 40000 : ℝ) / L)
            (div_pos (by positivity) hL) (div_pos (by positivity) hL)
            (lowSelectedInverseRow Finset.univ (lowSelectedWeight η slots J W Yp t)
              η S hS (lowSelectedIdeal slots J) X t)) := by ring
      _ ≤ (‖lowUnselectedWeight slots J W Yp p‖ *
          lowGramFactor (calibrationForSet S hS)
            (Z ^ (2111 / 6000 : ℝ) / L) (Z ^ (19249 / 40000 : ℝ) / L) ε) * V :=
        mul_le_mul_of_nonneg_left hib (mul_nonneg (norm_nonneg _) hgn)
      _ ≤ (‖lowUnselectedWeight slots J W Yp p‖ * (Real.sqrt (3 * q / L) * G)) * V :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hgb (norm_nonneg _))
          (by dsimp [V]; positivity)
      _ = (‖lowUnselectedWeight slots J W Yp p‖ * Real.sqrt (3 * q / L)) * (G * V) := by ring
      _ ≤ (‖lowUnselectedWeight slots J W Yp p‖ * Real.sqrt (3 * q / L)) *
          (Ci * (1 + ‖t‖) ^ degree * Z ^ (268847 / 1440000 + d / 8 + 254 * ε)) :=
        mul_le_mul_of_nonneg_left hGV (by positivity)
      _ = _ := by rw [low_compensated_sqrt_factor q L hq.le hL]; ring
  have hh := mul_le_mul_of_nonneg_left (Finset.sum_le_sum (s := Finset.univ) (fun p _ => hterm p)) hCg.le
  apply hh.trans
  rw [← Finset.mul_sum]
  have hm := hmass ell Z hz T hT (fun i P hP => (hnorm i P hP).1) J W Yp hW
  have hcancel : Z ^ (268847 / 1440000 + d / 8 + 254 * ε) * Z ^ (-d / 2) ≤
      Z ^ (268847 / 1440000 + 254 * ε) := by
    rw [← Real.rpow_add hz]
    exact Real.rpow_le_rpow_of_exponent_le hInv.1.le (by linarith)
  calc
    _ ≤ Cg * ((Ci * Real.sqrt (3 * q) * (1 + ‖t‖) ^ degree *
        Z ^ (268847 / 1440000 + d / 8 + 254 * ε)) * (Cu * Z ^ (-d / 2))) := by gcongr
    _ = C0 * (1 + ‖t‖) ^ degree * (Z ^ (268847 / 1440000 + d / 8 + 254 * ε) * Z ^ (-d / 2)) := by
      dsimp [C0]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hcancel (by positivity)

theorem stage1Vertex_low_central_gaussian_dyad (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀ P ∈ S, P.IsMaximal) (hbad : fixedBadPrimes ⊆ S)
    {K : ℕ} (ell : Fin K → ℝ) (hell : ∀ i, 0 ≤ ell i) (hsum : ∑ i, ell i ≤ 20033 / 120000)
    (a b ε : ℝ) (ha : 0 < a) (hε : 0 < ε) (hε1 : ε < 1)
    (W0 W1 : ℝ → ℂ) (a0 b0 a1 b1 M : ℝ) (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hab1 : a1 < b1) (hM : 0 ≤ M)
    (hW0 : Function.support W0 ⊆ Set.Icc a0 b0) (hW1 : Function.support W1 ⊆ Set.Icc a1 b1)
    (hW0s : ContDiff ℝ ∞ W0) (hW1s : ContDiff ℝ ∞ W1) (hWM : ∀ x, ‖W1 x‖ ≤ M) :
    ∃ degree : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in Filter.atTop, 1 < Z ∧
    ∀ (T : Fin K → Finset HeckeIdealSeries.PrimeIdeal), (∀ i P, P ∈ T i → Supported P.val) →
      (∀ i P, P ∈ T i → P.val ∉ S) → Pairwise (fun i j => Disjoint (T i) (T j)) →
      (∀ i P, P ∈ T i → a * Z ^ (ell i) ≤ (Ideal.absNorm P.val : ℝ) ∧ (Ideal.absNorm P.val : ℝ) ≤ b * Z ^ (ell i)) →
    ∀ (J : Finset (Fin K)) (U : ℝ), 0 < U →
      Z ^ (1 + lowSelectedLength ell J - ε / 2) ≤ U → U ≤ Z ^ (1 + lowSelectedLength ell J + ε / 2) →
    ∀ (W : Fin K → ℝ → ℂ), (∀ i x, ‖W i x‖ ≤ 1) →
    ∀ (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V : ℝ → ℂ)),
      ‖lowCommonDyad η (calibrationForSet S hS) W0 W1 (fun i => canonicalSlotSupport (T i))
        W (fun i => Z ^ (ell i)) J (Z ^ (2111 / 6000 : ℝ)) (Z ^ (19249 / 40000 : ℝ)) U
          (Z ^ (1 + lowSelectedLength ell J)) V hV‖ ≤
        C * Z ^ (268847 / 1440000 + 254 * ε) *
          gaussianJointMoment V hV degree (U / Z ^ (1 + lowSelectedLength ell J)) := by
  obtain ⟨degree, C, hC, he⟩ := stage1Vertex_low_central_compensated_tuple η S hS hbad ell hell hsum
    a b ε ha hε hε1 W0 W1 a0 b0 a1 b1 M ha0 ha1 hab1 hM hW0 hW1 hW0s hW1s hWM
  refine ⟨degree, C, hC, ?_⟩
  filter_upwards [he] with Z hZ
  refine ⟨hZ.1, ?_⟩
  intro T hT hout hdis hnorm J U hU hlo hhi W hW V hV
  apply lowCommonDyad_norm_of_bound
  intro t
  simpa only [mul_assoc, mul_left_comm, mul_comm] using hZ.2 T hT hout hdis hnorm J U hU hlo hhi W hW t

lemma eventually_stage1Vertex_low_physical_scales {K : ℕ} (ell : Fin K → ℝ) (hell : ∀ i, 0 ≤ ell i)
    (hsum : ∑ i, ell i ≤ 20033 / 120000) (b : ℝ) :
    ∀ᶠ Z : ℝ in Filter.atTop, 1 < Z ∧
      ∀ (slots : Fin K → Finset O), (∀ i x, x ∈ slots i → x ≠ 0) →
      (∀ i x, x ∈ slots i → elementNorm x ≤ b * Z ^ (ell i)) →
      ∀ (J : Finset (Fin K)) (p : ∀ i, slots i),
      1 ≤ Z ^ (2111 / 6000 : ℝ) / elementNorm (slotProduct (fun i => (p i).val) J) ∧
      1 ≤ Z ^ (19249 / 40000 : ℝ) / elementNorm (slotProduct (fun i => (p i).val) J) := by
  filter_upwards [Filter.eventually_gt_atTop (1 : ℝ),
    (tendsto_rpow_atTop (show 0 < (22187 / 120000 : ℝ) by norm_num)).eventually
      (Filter.eventually_ge_atTop ((max 1 b) ^ K))] with Z hZ hc
  refine ⟨hZ, ?_⟩
  intro slots hn hnorm J p
  have hl : 0 < elementNorm (slotProduct (fun i => (p i).val) J) :=
    slotProduct_norm_pos _ (fun i => hn i _ (p i).property) J
  have hb := stage1Vertex_lowUnselectedProduct_norm_bound ell hell hsum (max 1 b) Z
    (le_max_left _ _) hZ.le slots
    (fun i n hm => (hnorm i n hm).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)))
    J (fun i => p i.val)
  rw [← slotProduct_subtype (fun i => (p i).val) J] at hb
  have hLX : elementNorm (slotProduct (fun i => (p i).val) J) ≤ Z ^ (2111 / 6000 : ℝ) := by
    apply hb.trans
    calc
      _ ≤ Z ^ (22187 / 120000 : ℝ) * Z ^ (20033 / 120000 : ℝ) :=
        mul_le_mul_of_nonneg_right hc (by positivity)
      _ = _ := by rw [← Real.rpow_add (lt_trans zero_lt_one hZ)]; norm_num
  exact ⟨(one_le_div hl).mpr hLX,
    (one_le_div hl).mpr (hLX.trans (Real.rpow_le_rpow_of_exponent_le hZ.le (by norm_num)))⟩

lemma stage1Vertex_canonicalTuple_count {K : ℕ} (ell : Fin K → ℝ) (hell : ∀ i, 0 ≤ ell i)
    (hsum : ∑ i, ell i ≤ 20033 / 120000) (b Z : ℝ) (hZ : 1 ≤ Z)
    (T : Fin K → Finset HeckeIdealSeries.PrimeIdeal) (hT : ∀ i P, P ∈ T i → Supported P.val)
    (hnorm : ∀ i P, P ∈ T i → (Ideal.absNorm P.val : ℝ) ≤ b * Z ^ (ell i)) :
    (Fintype.card (∀ i, canonicalSlotSupport (T i)) : ℝ) ≤
      (128 * max 1 b) ^ K * Z ^ (20033 / 120000 : ℝ) := by
  rw [Fintype.card_pi, Nat.cast_prod]
  calc
    _ ≤ ∏ i, 128 * (max 1 b * Z ^ (ell i)) := by
      apply Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _)
      intro i _
      simp only [Fintype.card_coe]
      apply canonicalSlot_count _ (hT i) _
        (one_le_mul_of_one_le_of_one_le (le_max_left _ _) (Real.one_le_rpow hZ (hell i)))
      intro P hP
      exact (hnorm i P hP).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
    _ = (128 * max 1 b) ^ K * Z ^ (∑ i, ell i) := by
      simp_rw [← mul_assoc]
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
        ← Real.rpow_sum_of_pos (lt_of_lt_of_le zero_lt_one hZ)]
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ hsum) (by positivity)

lemma stage1Vertex_compensation_scale_mass_bound {K : ℕ} (η : HeckeFamily.Character) (C : CalibrationData)
    (ell : Fin K → ℝ) (hell : ∀ i, 0 ≤ ell i) (hsum : ∑ i, ell i ≤ 20033 / 120000)
    (b Z : ℝ) (hZ : 1 ≤ Z) (T : Fin K → Finset HeckeIdealSeries.PrimeIdeal)
    (hT : ∀ i P, P ∈ T i → Supported P.val)
    (hnorm : ∀ i P, P ∈ T i → (Ideal.absNorm P.val : ℝ) ≤ b * Z ^ (ell i))
    (J : Finset (Fin K)) (W : Fin K → ℝ → ℂ) (hW : ∀ i x, ‖W i x‖ ≤ 1) :
    gaussianPhysicalScaleMass C (Finset.univ : Finset (∀ i, canonicalSlotSupport (T i)))
      (fun p => compensationSubsetWeight η W (fun i => Z ^ (ell i)) (fun i => (p i).val) J)
      (fun p => Z ^ (2111 / 6000 : ℝ) / elementNorm (slotProduct (fun i => (p i).val) J))
      (fun p => Z ^ (19249 / 40000 : ℝ) / elementNorm (slotProduct (fun i => (p i).val) J))
      (fun i : SelectedSlot J => W i.val)
      (fun p i => elementNorm (p i.val).val / Z ^ (ell i.val)) ≤
        (elementNorm C.generator * (128 * max 1 b) ^ K) * Z := by
  have hz : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  have hp (p : ∀ i, canonicalSlotSupport (T i)) (i : Fin K) : (p i).val ≠ 0 :=
    canonicalSlotSupport_nonzero _ (hT i) _ (p i).property
  have hterm (p : ∀ i, canonicalSlotSupport (T i)) :
      ‖compensationSubsetWeight η W (fun i => Z ^ (ell i)) (fun i => (p i).val) J‖ *
        (∏ i : SelectedSlot J, ‖W i.val (elementNorm (p i.val).val / Z ^ (ell i.val))‖) *
        lowPhysicalScale C (Z ^ (2111 / 6000 : ℝ) / elementNorm (slotProduct (fun i => (p i).val) J))
          (Z ^ (19249 / 40000 : ℝ) / elementNorm (slotProduct (fun i => (p i).val) J)) ≤
      elementNorm C.generator * Z ^ (99967 / 120000 : ℝ) := by
    have hcoeff : ‖compensationSubsetWeight η W (fun i => Z ^ (ell i)) (fun i => (p i).val) J‖ *
        (∏ i : SelectedSlot J, ‖W i.val (elementNorm (p i.val).val / Z ^ (ell i.val))‖) ≤ 1 :=
      (mul_le_of_le_one_left (Finset.prod_nonneg (fun _ _ => norm_nonneg _))
        (compensationSubsetWeight_norm_le_one η W hW _ _ (hp p) J)).trans
        (Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun (i : SelectedSlot J) _ => hW i.val _))
    have hL := slotProduct_norm_ge_one _ (hp p) J
    rw [stage1Vertex_lowPhysicalScale_source C Z _ hz]
    apply (mul_le_of_le_one_left (by unfold elementNorm; positivity) hcoeff).trans
    exact div_le_self (by unfold elementNorm; positivity) (one_le_pow₀ hL)
  unfold gaussianPhysicalScaleMass
  apply (Finset.sum_le_sum (fun p _ => hterm p)).trans
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hc := mul_le_mul_of_nonneg_right
    (stage1Vertex_canonicalTuple_count ell hell hsum b Z hZ T hT hnorm)
    (show 0 ≤ elementNorm C.generator * Z ^ (99967 / 120000 : ℝ) by unfold elementNorm; positivity)
  apply hc.trans_eq
  calc
    _ = (elementNorm C.generator * (128 * max 1 b) ^ K) *
        (Z ^ (20033 / 120000 : ℝ) * Z ^ (99967 / 120000 : ℝ)) := by ring
    _ = _ := by rw [← Real.rpow_add hz]; norm_num

lemma stage1Vertex_low_remote_power (Z ell ε : ℝ) (N : ℕ) (hZ : 1 ≤ Z) (hell : ell ≤ 20033 / 120000)
    (hN : 9 / 2 ≤ (ε / 2) * (N : ℝ)) :
    Z * (Z ^ (1 + ell)) ^ 2 / (Z ^ (ε / 2)) ^ N ≤ Z ^ (-1 : ℝ) := by
  have hz : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  have hsq : (Z ^ (1 + ell)) ^ 2 = Z ^ (2 * (1 + ell)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hz.le]
    congr 1; push_cast; ring
  have hn : (Z ^ (ε / 2)) ^ N = Z ^ ((ε / 2) * (N : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hz.le]
  rw [hsq, hn, show Z * Z ^ (2 * (1 + ell)) = Z ^ (1 + 2 * (1 + ell)) by
    rw [Real.rpow_add hz, Real.rpow_one], ← Real.rpow_sub hz]
  exact Real.rpow_le_rpow_of_exponent_le hZ (by linarith)

theorem stage1Vertex_low_remote_gaussian_dyads (S : Finset Id) (hS : ∀ P ∈ S, P.IsMaximal)
    {K : ℕ} (ell : Fin K → ℝ) (hell : ∀ i, 0 ≤ ell i) (hsum : ∑ i, ell i ≤ 20033 / 120000)
    (b ε : ℝ) (hε : 0 < ε) (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V : ℝ → ℂ))
    (W0 W1 : ℝ → ℂ) (a0 b0 a1 b1 B0 B1 : ℝ) (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hB0 : 0 ≤ B0) (hB1 : 0 ≤ B1)
    (hW0 : Function.support W0 ⊆ Set.Icc a0 b0) (hW1 : Function.support W1 ⊆ Set.Icc a1 b1)
    (hWB0 : ∀ x, ‖W0 x‖ ≤ B0) (hWB1 : ∀ x, ‖W1 x‖ ≤ B1) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in Filter.atTop, 1 < Z ∧
    ∀ (η : HeckeFamily.Character) (T : Fin K → Finset HeckeIdealSeries.PrimeIdeal),
      (∀ i P, P ∈ T i → Supported P.val) →
      (∀ i P, P ∈ T i → (Ideal.absNorm P.val : ℝ) ≤ b * Z ^ (ell i)) →
    ∀ (J : Finset (Fin K)) (W : Fin K → ℝ → ℂ), (∀ i x, ‖W i x‖ ≤ 1) →
      let f := fun j : ℕ => if lowRemote Z (lowSelectedLength ell J) ε ((2 : ℝ) ^ j) then
        ‖lowCommonDyad η (calibrationForSet S hS) W0 W1 (fun i => canonicalSlotSupport (T i))
          W (fun i => Z ^ (ell i)) J (Z ^ (2111 / 6000 : ℝ)) (Z ^ (19249 / 40000 : ℝ)) ((2 : ℝ) ^ j)
            (Z ^ (1 + lowSelectedLength ell J)) V hV‖ else 0
      Summable f ∧ (∑' j : ℕ, f j) ≤ C * Z ^ (-1 : ℝ) := by
  have hep : 0 < ε / 2 := by linarith
  obtain ⟨N, hN⟩ := exists_nat_gt ((9 / 2 : ℝ) / (ε / 2))
  have hN' : (9 / 2 : ℝ) ≤ (ε / 2) * (N : ℝ) := by
    have hh := (div_lt_iff₀ hep).mp hN
    nlinarith
  obtain ⟨Cg, _, he⟩ := gaussianPhysicalFamily_remote_polynomial V hV N
    a0 b0 a1 b1 B0 B1 ha0 ha1 hB0 hB1
  let q := elementNorm (calibrationForSet S hS).generator
  let C0 := Cg * (q * (128 * max 1 b) ^ K)
  have hq : 0 < q := calibration_elementNorm_pos _
  refine ⟨C0, by dsimp [C0]; positivity, ?_⟩
  filter_upwards [eventually_stage1Vertex_low_physical_scales ell hell hsum b] with Z hZ
  refine ⟨hZ.1, ?_⟩
  intro η T hT hnorm J W hW
  dsimp only [lowRemote]
  have hz : 0 < Z := lt_trans zero_lt_one hZ.1
  have hslots : ∀ i n, n ∈ canonicalSlotSupport (T i) → n ≠ 0 := fun i => canonicalSlotSupport_nonzero _ (hT i)
  have hnormE : ∀ i n, n ∈ canonicalSlotSupport (T i) → elementNorm n ≤ b * Z ^ (ell i) := by
    intro i n hn
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hn
    rw [primaryTuple_norm P (hT i P hP)]
    exact hnorm i P hP
  have hs := hZ.2 _ hslots hnormE J
  have hh := he η S hS W0 W1
    (HasCompactSupport.of_support_subset_isCompact isCompact_Icc hW0)
    (HasCompactSupport.of_support_subset_isCompact isCompact_Icc hW1)
    hW0 hW1 hWB0 hWB1 (Finset.univ : Finset (∀ i, canonicalSlotSupport (T i)))
    (fun p => compensationSubsetWeight η W (fun i => Z ^ (ell i)) (fun i => (p i).val) J)
    (fun p => Ideal.span {slotProduct (fun i => (p i).val) (Finset.univ \ J)})
    (fun p => Z ^ (2111 / 6000 : ℝ) / elementNorm (slotProduct (fun i => (p i).val) J))
    (fun p => Z ^ (19249 / 40000 : ℝ) / elementNorm (slotProduct (fun i => (p i).val) J))
    (fun p _ => (hs p).1) (fun p _ => (hs p).2)
    (fun i : SelectedSlot J => W i.val) (fun p i => elementNorm (p i.val).val / Z ^ (ell i.val))
    (Z ^ (1 + lowSelectedLength ell J)) (Z ^ (ε / 2)) (by positivity) (Real.one_le_rpow hZ.1.le hep.le)
  simp only [← lowCommonDyad_eq_family] at hh
  refine ⟨?_, ?_⟩
  · convert hh.1 using 1
    funext j
    split_ifs with h <;> simp_all only
  · have hhFinal := hh.2.trans (show _ ≤ C0 * Z ^ (-1 : ℝ) from by
      have hm := stage1Vertex_compensation_scale_mass_bound η (calibrationForSet S hS)
        ell hell hsum b Z hZ.1.le T hT hnorm J W hW
      calc
        _ ≤ Cg * ((q * (128 * max 1 b) ^ K) * Z) *
            (Z ^ (1 + lowSelectedLength ell J)) ^ 2 / (Z ^ (ε / 2)) ^ N := by gcongr
        _ = C0 * (Z * (Z ^ (1 + lowSelectedLength ell J)) ^ 2 / (Z ^ (ε / 2)) ^ N) := by
          dsimp [C0]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (stage1Vertex_low_remote_power Z (lowSelectedLength ell J) ε N hZ.1.le
            (by have hb := stage1Vertex_lowLength_bounds ell hell hsum J; linarith) hN')
          (by dsimp [C0]; positivity))
    convert hhFinal using 1 <;> first
    | rfl
    | apply tsum_congr; intro j; split_ifs with h <;> simp_all only

theorem stage1Vertex_low_central_gaussian_dyads (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀ P ∈ S, P.IsMaximal) (hbad : fixedBadPrimes ⊆ S)
    {K : ℕ} (ell : Fin K → ℝ) (hell : ∀ i, 0 ≤ ell i) (hsum : ∑ i, ell i ≤ 20033 / 120000)
    (a b ε : ℝ) (ha : 0 < a) (hε : 0 < ε) (hε1 : ε < 1)
    (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V : ℝ → ℂ))
    (W0 W1 : ℝ → ℂ) (a0 b0 a1 b1 M : ℝ) (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hab1 : a1 < b1) (hM : 0 ≤ M)
    (hW0 : Function.support W0 ⊆ Set.Icc a0 b0) (hW1 : Function.support W1 ⊆ Set.Icc a1 b1)
    (hW0s : ContDiff ℝ ∞ W0) (hW1s : ContDiff ℝ ∞ W1) (hWM : ∀ x, ‖W1 x‖ ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in Filter.atTop, 1 < Z ∧
    ∀ (T : Fin K → Finset HeckeIdealSeries.PrimeIdeal), (∀ i P, P ∈ T i → Supported P.val) →
      (∀ i P, P ∈ T i → P.val ∉ S) → Pairwise (fun i j => Disjoint (T i) (T j)) →
      (∀ i P, P ∈ T i → a * Z ^ (ell i) ≤ (Ideal.absNorm P.val : ℝ) ∧ (Ideal.absNorm P.val : ℝ) ≤ b * Z ^ (ell i)) →
    ∀ (J : Finset (Fin K)) (W : Fin K → ℝ → ℂ), (∀ i x, ‖W i x‖ ≤ 1) →
      let f := fun j : ℕ => if lowRemote Z (lowSelectedLength ell J) ε ((2 : ℝ) ^ j) then 0 else
        ‖lowCommonDyad η (calibrationForSet S hS) W0 W1 (fun i => canonicalSlotSupport (T i))
          W (fun i => Z ^ (ell i)) J (Z ^ (2111 / 6000 : ℝ)) (Z ^ (19249 / 40000 : ℝ)) ((2 : ℝ) ^ j)
            (Z ^ (1 + lowSelectedLength ell J)) V hV‖
      Summable f ∧ (∑' j : ℕ, f j) ≤ C * Z ^ (268847 / 1440000 + 256 * ε) := by
  obtain ⟨degree, C, hC, he⟩ := stage1Vertex_low_central_gaussian_dyad η S hS hbad ell hell hsum
    a b ε ha hε hε1 W0 W1 a0 b0 a1 b1 M ha0 ha1 hab1 hM hW0 hW1 hW0s hW1s hWM
  obtain ⟨Cm, hCm, hm⟩ := gaussianJointMoment_summed V hV degree ε hε
  refine ⟨C * Cm, mul_pos hC hCm, ?_⟩
  filter_upwards [he] with Z hZ
  refine ⟨hZ.1, ?_⟩
  intro T hT hout hdis hnorm J W hW
  let R := Z ^ (1 + lowSelectedLength ell J)
  let f := fun j : ℕ => if lowRemote Z (lowSelectedLength ell J) ε ((2 : ℝ) ^ j) then 0 else
    ‖lowCommonDyad η (calibrationForSet S hS) W0 W1 (fun i => canonicalSlotSupport (T i))
      W (fun i => Z ^ (ell i)) J (Z ^ (2111 / 6000 : ℝ)) (Z ^ (19249 / 40000 : ℝ)) ((2 : ℝ) ^ j) R V hV‖
  have hz : 0 < Z := lt_trans zero_lt_one hZ.1
  obtain ⟨hsm, hmb⟩ := hm R (by dsimp [R]; positivity)
  have hb (j : ℕ) : f j ≤ (C * Z ^ (268847 / 1440000 + 254 * ε)) *
      (((2 : ℝ) ^ j) ^ ε * gaussianJointMoment V hV degree ((2 : ℝ) ^ j / R)) := by
    dsimp only [f]
    split_ifs with hj
    · exact mul_nonneg (by positivity) (mul_nonneg (by positivity) (gaussianJointMoment_nonneg V hV degree _))
    · obtain ⟨hlo, hhi⟩ := not_lowRemote_bounds Z (lowSelectedLength ell J) ε ((2 : ℝ) ^ j) hz hj
      apply (hZ.2 T hT hout hdis hnorm J ((2 : ℝ) ^ j) (by positivity) hlo hhi W hW V hV).trans
      have hp : 1 ≤ ((2 : ℝ) ^ j) ^ ε := Real.one_le_rpow (one_le_pow₀ (by norm_num)) hε.le
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact le_mul_of_one_le_left (gaussianJointMoment_nonneg V hV degree _) hp
  have hn (j : ℕ) : 0 ≤ f j := by dsimp [f]; split_ifs <;> positivity
  have hsumf := Summable.of_nonneg_of_le hn hb (hsm.mul_left (C * Z ^ (268847 / 1440000 + 254 * ε)))
  refine ⟨hsumf, ?_⟩
  calc
    _ ≤ ∑' j : ℕ, (C * Z ^ (268847 / 1440000 + 254 * ε)) *
        (((2 : ℝ) ^ j) ^ ε * gaussianJointMoment V hV degree ((2 : ℝ) ^ j / R)) :=
      hsumf.tsum_le_tsum hb (hsm.mul_left _)
    _ = (C * Z ^ (268847 / 1440000 + 254 * ε)) *
        (∑' j : ℕ, ((2 : ℝ) ^ j) ^ ε * gaussianJointMoment V hV degree ((2 : ℝ) ^ j / R)) := tsum_mul_left
    _ ≤ (C * Z ^ (268847 / 1440000 + 254 * ε)) * (Cm * R ^ ε) :=
      mul_le_mul_of_nonneg_left hmb (by positivity)
    _ ≤ _ := by
      dsimp only [R]
      rw [← Real.rpow_mul hz.le]
      calc
        _ = (C * Cm) * (Z ^ (268847 / 1440000 + 254 * ε) * Z ^ ((1 + lowSelectedLength ell J) * ε)) := by ring
        _ ≤ _ := by
          rw [← Real.rpow_add hz]
          apply mul_le_mul_of_nonneg_left _ (mul_pos hC hCm).le
          have hh := stage1Vertex_lowLength_bounds ell hell hsum J
          exact Real.rpow_le_rpow_of_exponent_le hZ.1.le (by nlinarith)

theorem stage1Vertex_low_all_gaussian_dyads (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀ P ∈ S, P.IsMaximal) (hbad : fixedBadPrimes ⊆ S)
    {K : ℕ} (ell : Fin K → ℝ) (hell : ∀ i, 0 ≤ ell i) (hsum : ∑ i, ell i ≤ 20033 / 120000)
    (a b ε : ℝ) (ha : 0 < a) (hε : 0 < ε) (hε1 : ε < 1)
    (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V : ℝ → ℂ))
    (W0 W1 : ℝ → ℂ) (a0 b0 a1 b1 B0 B1 : ℝ) (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hab1 : a1 < b1) (hB0 : 0 ≤ B0) (hB1 : 0 ≤ B1)
    (hW0 : Function.support W0 ⊆ Set.Icc a0 b0) (hW1 : Function.support W1 ⊆ Set.Icc a1 b1)
    (hW0s : ContDiff ℝ ∞ W0) (hW1s : ContDiff ℝ ∞ W1)
    (hWB0 : ∀ x, ‖W0 x‖ ≤ B0) (hWB1 : ∀ x, ‖W1 x‖ ≤ B1) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in Filter.atTop, 1 < Z ∧
    ∀ (T : Fin K → Finset HeckeIdealSeries.PrimeIdeal), (∀ i P, P ∈ T i → Supported P.val) →
      (∀ i P, P ∈ T i → P.val ∉ S) → Pairwise (fun i j => Disjoint (T i) (T j)) →
      (∀ i P, P ∈ T i → a * Z ^ (ell i) ≤ (Ideal.absNorm P.val : ℝ) ∧ (Ideal.absNorm P.val : ℝ) ≤ b * Z ^ (ell i)) →
    ∀ (J : Finset (Fin K)) (W : Fin K → ℝ → ℂ), (∀ i x, ‖W i x‖ ≤ 1) →
      let f := fun j : ℕ => lowCommonDyad η (calibrationForSet S hS) W0 W1
        (fun i => canonicalSlotSupport (T i))
        W (fun i => Z ^ (ell i)) J (Z ^ (2111 / 6000 : ℝ)) (Z ^ (19249 / 40000 : ℝ)) ((2 : ℝ) ^ j)
          (Z ^ (1 + lowSelectedLength ell J)) V hV
      Summable f ∧ ‖∑' j : ℕ, f j‖ ≤ C * Z ^ (268847 / 1440000 + 256 * ε) := by
  obtain ⟨Cc, hCc, hcentral⟩ := stage1Vertex_low_central_gaussian_dyads η S hS hbad ell hell hsum
    a b ε ha hε hε1 V hV W0 W1 a0 b0 a1 b1 B1 ha0 ha1 hab1 hB1 hW0 hW1 hW0s hW1s hWB1
  obtain ⟨Cr, hCr, hremote⟩ := stage1Vertex_low_remote_gaussian_dyads S hS ell hell hsum b ε hε V hV
    W0 W1 a0 b0 a1 b1 B0 B1 ha0 ha1 hB0 hB1 hW0 hW1 hWB0 hWB1
  refine ⟨Cc + Cr, add_pos hCc hCr, ?_⟩
  filter_upwards [hcentral, hremote] with Z hc hr
  refine ⟨hc.1, ?_⟩
  intro T hT hout hdis hnorm J W hW
  have hc' := hc.2 T hT hout hdis hnorm J W hW
  have hr' := hr.2 η T hT (fun i P hP => (hnorm i P hP).2) J W hW
  dsimp only at hc' hr' ⊢
  have hh := low_dyad_norm_split _ (fun j => lowRemote Z (lowSelectedLength ell J) ε ((2 : ℝ) ^ j)) hc'.1 hr'.1
  refine ⟨hh.1, hh.2.trans ?_⟩
  have hp : Z ^ (-1 : ℝ) ≤ Z ^ (268847 / 1440000 + 256 * ε) :=
    Real.rpow_le_rpow_of_exponent_le hc.1.le (by linarith)
  calc
    _ ≤ Cc * Z ^ (268847 / 1440000 + 256 * ε) + Cr * Z ^ (-1 : ℝ) := add_le_add hc'.2 hr'.2
    _ ≤ Cc * Z ^ (268847 / 1440000 + 256 * ε) + Cr * Z ^ (268847 / 1440000 + 256 * ε) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hp hCr.le)
    _ = _ := by ring

/-! ### Physical probe and normalized low-frequency detector bound -/

theorem stage1Vertex_compensatedPhysicalProbe_low (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀ P ∈ S, P.IsMaximal) (hbad : fixedBadPrimes ⊆ S)
    {K : ℕ} (ell : Fin K → ℝ) (hell : ∀ i, 0 ≤ ell i) (hsum : ∑ i, ell i ≤ 20033 / 120000)
    (a b ε : ℝ) (ha : 0 < a) (hε : 0 < ε) (hε1 : ε < 1)
    (W : Fin K → ℝ → ℂ) (hW : ∀ i, Function.support (W i) ⊆ Set.Icc a b) (hWnorm : ∀ i x, ‖W i x‖ ≤ 1)
    (W0 W1 : ℝ → ℂ) (a0 b0 a1 b1 B0 B1 : ℝ) (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hab1 : a1 < b1) (hB0 : 0 ≤ B0) (hB1 : 0 ≤ B1)
    (hW0 : Function.support W0 ⊆ Set.Icc a0 b0) (hW1 : Function.support W1 ⊆ Set.Icc a1 b1)
    (hW0s : ContDiff ℝ ∞ W0) (hW1s : ContDiff ℝ ∞ W1)
    (hWB0 : ∀ x, ‖W0 x‖ ≤ B0) (hWB1 : ∀ x, ‖W1 x‖ ≤ B1) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in Filter.atTop, 1 < Z ∧
    ∀ (T : Fin K → Finset HeckeIdealSeries.PrimeIdeal), (∀ i P, P ∈ T i → Supported P.val) →
      (∀ i P, P ∈ T i → P.val ∉ S) → Pairwise (fun i j => Disjoint (T i) (T j)) →
      (∀ i P, P ∈ T i → a * Z ^ (ell i) ≤ (Ideal.absNorm P.val : ℝ) ∧ (Ideal.absNorm P.val : ℝ) ≤ b * Z ^ (ell i)) →
      ‖compensatedPhysicalProbe η (calibrationForSet S hS) W0 W1
        (fun i => canonicalSlotSupport (T i)) W (fun i => Z ^ (ell i))
        (Z ^ (2111 / 6000 : ℝ)) (Z ^ (19249 / 40000 : ℝ)) Z‖ ≤
        C * Z ^ (268847 / 1440000 + 256 * ε) := by
  obtain ⟨V, hV, _, hidentity⟩ := compensatedPhysicalProbe_common_gaussian W
    (fun _ => |Real.log a| + |Real.log b|) (fun _ => by positivity)
    (fun i => low_window_log_support (W i) a b ha (hW i))
  choose C hC he using fun A : Finset (Fin K) => stage1Vertex_low_all_gaussian_dyads η S hS hbad ell hell hsum
    a b ε ha hε hε1 (V A) (hV A) W0 W1 a0 b0 a1 b1 B0 B1 ha0 ha1 hab1 hB0 hB1
    hW0 hW1 hW0s hW1s hWB0 hWB1
  let C0 := (∑ A ∈ (Finset.univ : Finset (Fin K)).powerset, C A) + 1
  have hC0 : 0 < C0 := by
    have hn := Finset.sum_nonneg (fun A (_ : A ∈ (Finset.univ : Finset (Fin K)).powerset) => (hC A).le)
    dsimp only [C0]
    linarith
  refine ⟨C0, hC0, ?_⟩
  filter_upwards [Filter.eventually_all.mpr he] with Z hZ
  have hz1 : 1 < Z := (hZ ∅).1
  have hz : 0 < Z := lt_trans zero_lt_one hz1
  refine ⟨hz1, ?_⟩
  intro T hT hout hdis hnorm
  have hslots : ∀ i n, n ∈ canonicalSlotSupport (T i) → n ≠ 0 := fun i => canonicalSlotSupport_nonzero _ (hT i)
  rw [hidentity η (calibrationForSet S hS) W0 W1
    (HasCompactSupport.of_support_subset_isCompact isCompact_Icc hW0)
    (HasCompactSupport.of_support_subset_isCompact isCompact_Icc hW1)
    _ hslots (fun i => Z ^ (ell i)) (fun i => by positivity)
    (Z ^ (2111 / 6000 : ℝ)) (Z ^ (19249 / 40000 : ℝ)) Z (by positivity) (by positivity) hz]
  apply (norm_sum_le _ _).trans
  have hterm (A : Finset (Fin K)) :
      ‖∑' j : ℕ, lowCommonDyad η (calibrationForSet S hS) W0 W1
        (fun i => canonicalSlotSupport (T i)) W (fun i => Z ^ (ell i)) A
        (Z ^ (2111 / 6000 : ℝ)) (Z ^ (19249 / 40000 : ℝ)) ((2 : ℝ) ^ j)
        (Z * ∏ i ∈ Finset.univ \ A, Z ^ (ell i)) (V A) (hV A)‖ ≤
        C A * Z ^ (268847 / 1440000 + 256 * ε) := by
    have hc : Z * (∏ i ∈ Finset.univ \ A, Z ^ (ell i)) = Z ^ (1 + lowSelectedLength ell A) := by
      rw [lowSelectedScale_product ell A Z hz, Real.rpow_add hz, Real.rpow_one]
    rw [hc]
    exact ((hZ A).2 T hT hout hdis hnorm A W hWnorm).2
  have hh := Finset.sum_le_sum (fun A (_ : A ∈ (Finset.univ : Finset (Fin K)).powerset) => hterm A)
  apply hh.trans
  rw [← Finset.sum_mul]
  exact mul_le_mul_of_nonneg_right (by dsimp [C0]; linarith) (Real.rpow_nonneg hz.le _)

theorem stage1Vertex_ray_compensatedPhysicalProbe_low_loss
    (S : Finset Id) (hS : SourceExclusions S) (hmax : ∀ P ∈ S, P.IsMaximal)
    {K : ℕ} (ell : Fin K → ℝ) (hell : ∀ i, 0 ≤ ell i) (hinj : Function.Injective ell)
    (hsum : ∑ i, ell i ≤ 20033 / 120000) (R : Set Id)
    (a b B loss : ℝ) (ha : 0 < a) (hab : a ≤ b) (hloss : 0 < loss)
    (W : Fin K → ℝ → ℂ) (hW : ∀ i, Function.support (W i) ⊆ Set.Icc a b) (hWnorm : ∀ i x, ‖W i x‖ ≤ B)
    (W0 W1 : ℝ → ℂ) (a0 b0 a1 b1 B0 B1 : ℝ) (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hab1 : a1 < b1) (hB0 : 0 ≤ B0) (hB1 : 0 ≤ B1)
    (hW0 : Function.support W0 ⊆ Set.Icc a0 b0) (hW1 : Function.support W1 ⊆ Set.Icc a1 b1)
    (hW0s : ContDiff ℝ ∞ W0) (hW1s : ContDiff ℝ ∞ W1)
    (hWB0 : ∀ x, ‖W0 x‖ ≤ B0) (hWB1 : ∀ x, ‖W1 x‖ ≤ B1) :
    ∀ η : HeckeFamily.Character, ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in Filter.atTop,
      ‖compensatedPhysicalProbe η (calibrationForSet S hmax) W0 W1
        (fun i => canonicalSlotSupport (ProbeRaySlots.pool R S a b (Z ^ (ell i)))) W (fun i => Z ^ (ell i))
        (Z ^ (2111 / 6000 : ℝ)) (Z ^ (19249 / 40000 : ℝ)) Z‖ ≤
        C * Z ^ (268847 / 1440000 + loss) := by
  let D := max 1 B
  have hD : 0 < D := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  let Wn := fun i x => W i x / (D : ℂ)
  have hWn : ∀ i, Function.support (Wn i) ⊆ Set.Icc a b := by
    intro i x hx
    apply hW i
    intro hz
    exact hx (by dsimp [Wn]; rw [hz, zero_div])
  have hn : ∀ i x, ‖Wn i x‖ ≤ 1 := by
    intro i x
    dsimp only [Wn]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hD]
    exact (div_le_one hD).mpr ((hWnorm i x).trans (le_max_right _ _))
  have hscale : (fun i x => (D : ℂ) * Wn i x) = W := by
    funext i x; dsimp [Wn]; exact mul_div_cancel₀ _ (Complex.ofReal_ne_zero.mpr hD.ne')
  let ε := min (loss / 512) (1 / 2)
  have he : 0 < ε := by dsimp [ε]; positivity
  have he1 : ε < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have heloss : 256 * ε ≤ loss := by
    have hh := min_le_left (loss / 512) (1 / 2 : ℝ); dsimp only [ε]; linarith
  intro η
  obtain ⟨C, hC, hbound⟩ := stage1Vertex_compensatedPhysicalProbe_low η S hmax hS.bad ell hell hsum
    a b ε ha he he1 Wn hWn hn W0 W1 a0 b0 a1 b1 B0 B1 ha0 ha1 hab1 hB0 hB1
    hW0 hW1 hW0s hW1s hWB0 hWB1
  refine ⟨D ^ K * C, by positivity, ?_⟩
  filter_upwards [hbound, ProbeRaySlots.power_pools_eventually_disjoint R S (fun _ => a) (fun _ => b) ell
    (fun _ => ha) (fun _ => hab) hinj] with Z hZ hd
  have hz : 0 < Z := lt_trans zero_lt_one hZ.1
  have hraw : ‖compensatedPhysicalProbe η (calibrationForSet S hmax) W0 W1
      (fun i => canonicalSlotSupport (ProbeRaySlots.pool R S a b (Z ^ (ell i)))) Wn (fun i => Z ^ (ell i))
      (Z ^ (2111 / 6000 : ℝ)) (Z ^ (19249 / 40000 : ℝ)) Z‖ ≤
      C * Z ^ (268847 / 1440000 + 256 * ε) := by
    apply hZ.2 _ (fun i => ProbeRaySlots.pool_supported R S hS a b (Z ^ (ell i)))
      (fun i P hP => ((ProbeRaySlots.mem_pool R S a b (Z ^ (ell i)) P).mp hP).2.2.2)
      (fun i j hij => hd i j hij)
    intro i P hP
    have hh := ProbeRaySlots.pool_norm_bounds R S ha.le hab (Real.rpow_pos_of_pos hz _) P hP
    simpa only [mul_comm] using And.intro hh.1.le hh.2
  have heq := compensatedPhysicalProbe_window_scale η (calibrationForSet S hmax) W0 W1
    (fun i => canonicalSlotSupport (ProbeRaySlots.pool R S a b (Z ^ (ell i)))) Wn (fun i => Z ^ (ell i))
    (Z ^ (2111 / 6000 : ℝ)) (Z ^ (19249 / 40000 : ℝ)) Z (D : ℂ)
  rw [hscale] at heq
  rw [heq, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hD]
  have hz1 : 1 ≤ Z := hZ.1.le
  calc
    _ ≤ D ^ K * (C * Z ^ (268847 / 1440000 + 256 * ε)) := mul_le_mul_of_nonneg_left hraw (by positivity)
    _ ≤ D ^ K * (C * Z ^ (268847 / 1440000 + loss)) := by gcongr
    _ = _ := by ring

theorem stage1Vertex_ray_normalizer_inverse {K : ℕ}
    (M : Ideal O) [NeZero M] [Finite (O ⧸ M)]
    (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)
    (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (c b : ℝ) (hc : 0 < c) (hcb : c ≤ b)
    (ell : Fin K → ℝ) (hell : ∀ j, 0 < ell j) (hellsum : ∑ j, ell j = 20033 / 120000)
    (W : Fin K → ℝ → ℝ) (hW : ∀ j, ContDiff ℝ ∞ (W j)) (hcompact : ∀ j, HasCompactSupport (W j))
    (hsupp : ∀ j, Function.support (W j) ⊆ Set.Ioo c b) (hp : ∀ j y, 0 ≤ W j y) (hne : ∀ j, W j ≠ 0)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hW0 : Function.support W0 ⊆ Set.Icc a0 b0) (hW1 : Function.support W1 ⊆ Set.Icc a1 b1)
    (hr0 : ∀ y, (W0 y).im = 0) (hr1 : ∀ y, (W1 y).im = 0)
    (hp0 : ∀ y, 0 ≤ (W0 y).re) (hp1 : ∀ y, 0 ≤ (W1 y).re) (hn0 : W0 ≠ 0) (hn1 : W1 ≠ 0)
    (nu : ℝ) (hnu : 0 < nu) :
    letI : NeZero (∏ P ∈ S, P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop,
      let T := fun j => pool (RayQuotient.identityClass M H) S c b (Z ^ (ell j))
      let normer := sourceResidueConstant W0 W1 (∏ P ∈ S, P) *
        (Probe.principalScalar Finset.univ Z (20033 / 120000)
          (slotMass T (residueWeights W (fun j => Z ^ (ell j)))) : ℂ)
      normer ≠ 0 ∧ ‖normer⁻¹‖ ≤ C * Z ^ nu := by
  let : NeZero (∏ P ∈ S, P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  let cs := sourceResidueConstant W0 W1 (∏ P ∈ S, P)
  refine ⟨‖cs⁻¹‖ + 1, by positivity, ?_⟩
  have hpos (j : Fin K) : tsupport (W j) ⊆ Set.Ioi 0 := by
    apply Set.Subset.trans (closure_minimal (Set.Subset.trans (hsupp j) Set.Ioo_subset_Icc_self) isClosed_Icc)
    intro y hy
    exact lt_of_lt_of_le hc hy.1
  filter_upwards [power_ray_mass_and_normalizer M H hH S W c b hc hcb hsupp hW hcompact hpos hp hne ell hell nu hnu,
    eventually_gt_atTop (0 : ℝ)] with Z hmass hZ
  dsimp only
  refine ⟨ProbePrincipalNormalizer.signed_source_normalizer_ne_zero (∏ P ∈ S, P)
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1 Finset.univ
    (fun j => pool (RayQuotient.identityClass M H) S c b (Z ^ (ell j)))
    (residueWeights W (fun j => Z ^ (ell j))) Z (20033 / 120000) hZ (fun j _ => hmass.1 j), ?_⟩
  have hb : ‖(sourceResidueConstant W0 W1 (∏ P ∈ S, P) *
      (Probe.principalScalar Finset.univ Z (20033 / 120000)
        (slotMass (fun j => pool (RayQuotient.identityClass M H) S c b (Z ^ (ell j)))
          (residueWeights W (fun j => Z ^ (ell j)))) : ℂ))⁻¹‖ ≤ ‖cs⁻¹‖ * Z ^ nu := by
    rw [mul_inv_rev, norm_mul, ← Complex.ofReal_inv, Complex.norm_real]
    simpa only [hellsum, Real.norm_eq_abs, mul_comm] using
      mul_le_mul_of_nonneg_left hmass.2 (norm_nonneg cs⁻¹)
  exact hb.trans (mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hZ.le _))

/-- At `(X, Y, Z) = (Z^{2111/6000}, Z^{19249/40000}, Z)` and `∑ j, ell j = 20033/120000`, the
normalized low-frequency detector is `O(Z^{268847/1440000 + loss})`. -/
theorem stage1Vertex_normalized_compensatedPhysicalProbe_low {K : ℕ}
    (M : Ideal O) [NeZero M] [Finite (O ⧸ M)]
    (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀ P ∈ S, P.IsMaximal)
    (a b B loss : ℝ) (ha : 0 < a) (hab : a ≤ b) (hloss : 0 < loss)
    (ell : Fin K → ℝ) (hell : ∀ j, 0 < ell j) (hinj : Function.Injective ell)
    (hsum : ∑ j, ell j = 20033 / 120000)
    (W : Fin K → ℝ → ℝ) (hW : ∀ j, ContDiff ℝ ∞ (W j)) (hcompact : ∀ j, HasCompactSupport (W j))
    (hsupp : ∀ j, Function.support (W j) ⊆ Set.Ioo a b)
    (hWB : ∀ j y, 0 ≤ W j y ∧ W j y ≤ B) (hne : ∀ j, W j ≠ 0)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hW0 : Function.support W0 ⊆ Set.Icc a0 b0) (hW1 : Function.support W1 ⊆ Set.Icc a1 b1)
    (hr0 : ∀ y, (W0 y).im = 0) (hr1 : ∀ y, (W1 y).im = 0)
    (hp0 : ∀ y, 0 ≤ (W0 y).re) (hp1 : ∀ y, 0 ≤ (W1 y).re) (hn0 : W0 ≠ 0) (hn1 : W1 ≠ 0) :
    letI : NeZero (∏ P ∈ S, P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∀ η : HeckeFamily.Character, ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop,
      let Yp := fun j => Z ^ (ell j)
      let T := fun j => pool (RayQuotient.identityClass M H) S a b (Yp j)
      let WC : Fin K → ℝ → ℂ := fun j y => (W j y : ℂ)
      let normer := sourceResidueConstant W0 W1 (∏ P ∈ S, P) *
        (Probe.principalScalar Finset.univ Z (20033 / 120000) (slotMass T (residueWeights W Yp)) : ℂ)
      normer ≠ 0 ∧
      ‖compensatedPhysicalProbe η (calibrationForSet S hmax) W0 W1
        (fun j => canonicalSlotSupport (T j)) WC Yp
        (Z ^ (2111 / 6000 : ℝ)) (Z ^ (19249 / 40000 : ℝ)) Z / normer‖ ≤
        C * Z ^ (268847 / 1440000 + loss) := by
  let : NeZero (∏ P ∈ S, P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  let WC : Fin K → ℝ → ℂ := fun j y => (W j y : ℂ)
  have hWC (j : Fin K) : Function.support (WC j) ⊆ Set.Icc a b := by
    intro y hy
    apply Set.Ioo_subset_Icc_self (hsupp j _)
    intro hz
    exact hy (by dsimp [WC]; rw [hz]; simp)
  have hWCB (j : Fin K) (y : ℝ) : ‖WC j y‖ ≤ B := by
    simpa only [WC, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hWB j y).1] using (hWB j y).2
  have hW1' : Function.support W1 ⊆ Set.Icc a1 (max b1 (a1 + 1)) := by
    intro y hy
    exact ⟨(hW1 hy).1, (hW1 hy).2.trans (le_max_left _ _)⟩
  have hab1 : a1 < max b1 (a1 + 1) := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  obtain ⟨Cn, hCn, hnorm⟩ := stage1Vertex_ray_normalizer_inverse M H hH S hS a b ha hab
    ell hell hsum W hW hcompact hsupp (fun j y => (hWB j y).1) hne W0 W1 a0 b0 a1 b1 ha0 ha1
    hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1 (loss / 2) (by positivity)
  intro η
  obtain ⟨Cp, hCp, hprobe⟩ := stage1Vertex_ray_compensatedPhysicalProbe_low_loss S hS hmax ell
    (fun j => (hell j).le) hinj hsum.le (RayQuotient.identityClass M H) a b B (loss / 2)
    ha hab (by positivity) WC hWC hWCB W0 W1 a0 b0 a1 (max b1 (a1 + 1))
    (SchwartzMap.seminorm ℝ 0 0 W0) (SchwartzMap.seminorm ℝ 0 0 W1)
    ha0 ha1 hab1 (by positivity) (by positivity) hW0 hW1' (W0.smooth (⊤ : ℕ∞)) (W1.smooth (⊤ : ℕ∞))
    (SchwartzMap.norm_le_seminorm ℝ W0) (SchwartzMap.norm_le_seminorm ℝ W1) η
  refine ⟨Cp * Cn, by positivity, ?_⟩
  filter_upwards [hprobe, hnorm, eventually_gt_atTop (0 : ℝ)] with Z hp hn hZ
  dsimp only at hn ⊢
  refine ⟨hn.1, ?_⟩
  rw [div_eq_mul_inv, norm_mul]
  calc
    _ ≤ (Cp * Z ^ (268847 / 1440000 + loss / 2)) * (Cn * Z ^ (loss / 2)) :=
      mul_le_mul hp hn.2 (norm_nonneg _) (by positivity)
    _ = (Cp * Cn) * Z ^ (268847 / 1440000 + loss) := by
      rw [mul_mul_mul_comm, ← Real.rpow_add hZ]
      congr 2
      ring

end ProbePhysical

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein

end
