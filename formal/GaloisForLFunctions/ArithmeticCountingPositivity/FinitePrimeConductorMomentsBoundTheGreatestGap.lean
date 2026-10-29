import Mathlib.Analysis.Normed.Algebra.TrivSqZeroExt
import GaloisForLFunctions.ArithmeticCountingPositivity.TheFinitePrimeSecularSignsDetermineTheGap
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheAdjunctionEnergySeparatesValuations

/-!
# The first conductor moment bounds finite-prime gaps

Dual numbers retain conductor mass and energy in the same finite Euler
product. Local geometric first moments give the exact mean energy. Weighted
Cauchy-Schwarz then turns that count into an upper bound for the attained
greatest gap through the full arithmetic secular criterion.
-/

noncomputable section

open Finset Filter Topology

namespace GaloisForLFunctions.ArithmeticCountingPositivity

open GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
  GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity
  GaloisForLFunctions.ArithmeticIntersectionTheory

open private spectralWeight_one spectralWeight_mul spectralWeight_prime_pow
  spectralWeight_nonneg spectralWeight_ladder_hasSum from
  GaloisForLFunctions.ArithmeticCountingPositivity.FinitePrimeFlipsHaveUnitConductorMass
open private conductor_energy_gap conductor_coefficient_one from
  GaloisForLFunctions.ArithmeticCountingPositivity.FinitePrimeCountsDetermineTheFullResolvent

local notation "γ" => Real.eulerMascheroniConstant

/-- The explicit first energy moment contributed by a finite prime set. -/
def finiteFlipConductorEnergyMoment (F : Finset ℕ) : ℝ :=
  ∑ p ∈ F, 4 * (p : ℝ) * Real.log p / ((p : ℝ) ^ 2 - 1)

private def conductorEnergy (m : ℕ) : ℝ := Real.log m + tameDifferent m

private theorem conductorEnergy_one : conductorEnergy 1 = 0 := by
  simp only [conductorEnergy, Nat.cast_one, Real.log_one, tameDifferent_one, add_zero]

private theorem conductorEnergy_nonneg {m : ℕ} (hm : 0 < m) : 0 ≤ conductorEnergy m :=
  add_nonneg (Real.log_nonneg (by exact_mod_cast (show 1 ≤ m from hm)))
    (RenormalizedArithmeticPotentialTheory.tameDifferent_nonneg m)

private theorem conductorEnergy_mul {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    (hmn : m.Coprime n) : conductorEnergy (m * n) = conductorEnergy m + conductorEnergy n := by
  rw [conductorEnergy, Nat.cast_mul, Real.log_mul (by exact_mod_cast hm) (by exact_mod_cast hn),
    tameDifferent_mul hmn]
  unfold conductorEnergy
  ring

private theorem conductorEnergy_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    conductorEnergy (p ^ (k + 1)) =
      ((k : ℝ) + 1) * Real.log p + Real.log p / ((p : ℝ) - 1) := by
  simp only [conductorEnergy, Nat.cast_pow, Real.log_pow,
    tameDifferent_prime_pow hp (by omega : k + 1 ≠ 0), Nat.cast_add, Nat.cast_one]

private def primeMassFactor (p : ℕ) : ℝ := 1 + 4 * (p : ℝ) / ((p : ℝ) - 1) ^ 2

private def primeMomentFactor (p : ℕ) : ℝ :=
  4 * (p : ℝ) * ((p : ℝ) + 1) * Real.log p / ((p : ℝ) - 1) ^ 3

private theorem prime_moment_hasSum (F : Finset ℕ) {p : ℕ} (hp : p.Prime) :
    HasSum (fun k : ℕ => finiteFlipSpectralWeight F (p ^ k) * conductorEnergy (p ^ k))
      (if p ∈ F then primeMomentFactor p else 0) := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (p : ℝ) ≠ 0 := (zero_lt_one.trans hpR).ne'
  have hp1 : (p : ℝ) - 1 ≠ 0 := (sub_pos.mpr hpR).ne'
  have hr0 : 0 ≤ (p : ℝ)⁻¹ := by positivity
  have hr1 : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hpR
  have htail : HasSum (fun k : ℕ =>
      finiteFlipSpectralWeight F (p ^ (k + 1)) * conductorEnergy (p ^ (k + 1)))
      (if p ∈ F then primeMomentFactor p else 0) := by
    by_cases hpF : p ∈ F
    · have hg := hasSum_geometric_of_lt_one hr0 hr1
      have hk := hasSum_coe_mul_geometric_of_norm_lt_one (r := (p : ℝ)⁻¹)
        (by simpa only [Real.norm_eq_abs, abs_of_nonneg hr0] using hr1)
      let A : ℝ := 4 * Real.log p / ((p : ℝ) - 1)
      let B : ℝ := A * (1 + 1 / ((p : ℝ) - 1))
      have h := (hk.mul_left A).add (hg.mul_left B)
      have he (k : ℕ) :
          finiteFlipSpectralWeight F (p ^ (k + 1)) * conductorEnergy (p ^ (k + 1)) =
            A * ((k : ℝ) * ((p : ℝ)⁻¹) ^ k) + B * ((p : ℝ)⁻¹) ^ k := by
        rw [spectralWeight_prime_pow F hp, if_pos hpF, conductorEnergy_prime_pow hp]
        dsimp only [A, B]
        rw [inv_pow]
        field_simp [hp0, hp1]
        ring
      have hv : A * ((p : ℝ)⁻¹ / (1 - (p : ℝ)⁻¹) ^ 2) +
          B * (1 - (p : ℝ)⁻¹)⁻¹ = primeMomentFactor p := by
        dsimp only [A, B, primeMomentFactor]
        field_simp [hp0, hp1]
        ring
      rw [hv] at h
      rw [if_pos hpF]
      exact h.congr_fun he
    · simp only [spectralWeight_prime_pow F hp, if_neg hpF, zero_mul]
      exact hasSum_zero
  have hs : Summable (fun k : ℕ =>
      finiteFlipSpectralWeight F (p ^ k) * conductorEnergy (p ^ k)) :=
    (summable_nat_add_iff 1).mp htail.summable
  have hv := hs.tsum_eq_zero_add
  rw [pow_zero, conductorEnergy_one, mul_zero, zero_add, htail.tsum_eq] at hv
  simpa only [hv] using hs.hasSum

/-- The dual number with mass a and first-moment coefficient b. -/
private def momentDual (a b : ℝ) : TrivSqZeroExt ℝ ℝ := ⟨a, b⟩

private theorem momentDual_eq (a b : ℝ) :
    momentDual a b = (TrivSqZeroExt.inl a : TrivSqZeroExt ℝ ℝ) + TrivSqZeroExt.inr b := by
  apply TrivSqZeroExt.ext <;>
    simp only [momentDual, TrivSqZeroExt.fst_mk, TrivSqZeroExt.snd_mk,
      TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add, TrivSqZeroExt.fst_inl,
      TrivSqZeroExt.snd_inl, TrivSqZeroExt.fst_inr, TrivSqZeroExt.snd_inr,
      add_zero, zero_add]

private def dualConductorWeight (F : Finset ℕ) (m : ℕ) : TrivSqZeroExt ℝ ℝ :=
  momentDual (finiteFlipSpectralWeight F m) (finiteFlipSpectralWeight F m * conductorEnergy m)

private theorem dualConductorWeight_zero (F : Finset ℕ) : dualConductorWeight F 0 = 0 := by
  ext <;> simp [dualConductorWeight, momentDual, finiteFlipSpectralWeight]

private theorem dualConductorWeight_one (F : Finset ℕ) : dualConductorWeight F 1 = 1 := by
  ext <;> simp [dualConductorWeight, momentDual, spectralWeight_one, conductorEnergy_one]

private theorem dualConductorWeight_mul (F : Finset ℕ) {m n : ℕ} (hmn : m.Coprime n) :
    dualConductorWeight F (m * n) = dualConductorWeight F m * dualConductorWeight F n := by
  rcases eq_or_ne m 0 with rfl | hm
  · rw [zero_mul, dualConductorWeight_zero, zero_mul]
  rcases eq_or_ne n 0 with rfl | hn
  · rw [mul_zero, dualConductorWeight_zero, mul_zero]
  apply TrivSqZeroExt.ext
  · exact spectralWeight_mul F hmn
  · simp only [dualConductorWeight, momentDual, TrivSqZeroExt.snd_mul,
      TrivSqZeroExt.fst_mk, TrivSqZeroExt.snd_mk, op_smul_eq_mul, smul_eq_mul]
    rw [spectralWeight_mul F hmn, conductorEnergy_mul hm hn hmn]
    ring

private theorem dual_ladder_hasSum (F : Finset ℕ) {p : ℕ} (hp : p.Prime) :
    HasSum (fun k : ℕ => dualConductorWeight F (p ^ k))
      (momentDual (1 + if p ∈ F then 4 * (p : ℝ) / ((p : ℝ) - 1) ^ 2 else 0)
        (if p ∈ F then primeMomentFactor p else 0)) := by
  have h := (TrivSqZeroExt.hasSum_inl ℝ (spectralWeight_ladder_hasSum F hp)).add
    (TrivSqZeroExt.hasSum_inr ℝ (prime_moment_hasSum F hp))
  simpa only [dualConductorWeight, momentDual_eq] using h

private theorem dual_ladder_norm_summable (F : Finset ℕ) {p : ℕ} (hp : p.Prime) :
    Summable (fun k : ℕ => ‖dualConductorWeight F (p ^ k)‖) := by
  have hw := (spectralWeight_ladder_hasSum F hp).summable
  have hm := (prime_moment_hasSum F hp).summable
  apply (hw.add hm).congr
  intro k
  rw [TrivSqZeroExt.norm_def]
  have hd := conductorEnergy_nonneg (pow_pos hp.pos k)
  simp only [dualConductorWeight, momentDual, TrivSqZeroExt.fst_mk, TrivSqZeroExt.snd_mk,
    Real.norm_eq_abs, abs_of_nonneg (spectralWeight_nonneg F _),
    abs_of_nonneg (mul_nonneg (spectralWeight_nonneg F _) hd)]

private theorem dual_product_first_moment {ι : Type*} [DecidableEq ι]
    (F : Finset ι) (u e : ι → ℝ) :
    (∏ p ∈ F, momentDual (u p) (u p * e p)) =
      momentDual (∏ p ∈ F, u p) ((∏ p ∈ F, u p) * ∑ p ∈ F, e p) := by
  induction F using Finset.induction_on with
  | empty =>
      apply TrivSqZeroExt.ext <;>
        simp only [prod_empty, sum_empty, mul_zero, momentDual,
          TrivSqZeroExt.fst_one, TrivSqZeroExt.snd_one,
          TrivSqZeroExt.fst_mk, TrivSqZeroExt.snd_mk]
  | @insert p F hp ih =>
      simp only [prod_insert hp, sum_insert hp, ih]
      apply TrivSqZeroExt.ext
      · rfl
      · simp only [TrivSqZeroExt.snd_mul, momentDual, TrivSqZeroExt.fst_mk, TrivSqZeroExt.snd_mk,
          op_smul_eq_mul, smul_eq_mul]
        ring

private theorem primeMomentFactor_eq {p : ℕ} (hp : p.Prime) :
    primeMomentFactor p = primeMassFactor p *
      (4 * (p : ℝ) * Real.log p / ((p : ℝ) ^ 2 - 1)) := by
  have hp1 : (p : ℝ) - 1 ≠ 0 := (sub_pos.mpr (by exact_mod_cast hp.one_lt)).ne'
  have hpp : (p : ℝ) + 1 ≠ 0 := by positivity
  have hfactor : (p : ℝ) ^ 2 - 1 = ((p : ℝ) - 1) * ((p : ℝ) + 1) := by ring
  unfold primeMomentFactor primeMassFactor
  rw [hfactor]
  field_simp [hp1, hpp]
  ring

private theorem density_mass_product (F : Finset ℕ) (hF : ∀ p ∈ F, p.Prime) :
    finiteFlipHarmonicDensity F ^ 2 * (∏ p ∈ F, primeMassFactor p) = 1 := by
  rw [finiteFlipHarmonicDensity, ← prod_pow, ← prod_mul_distrib]
  apply prod_eq_one
  intro p hp
  have hpR : (1 : ℝ) < p := by exact_mod_cast (hF p hp).one_lt
  have hp1 : (p : ℝ) - 1 ≠ 0 := (sub_pos.mpr hpR).ne'
  have hpp : (p : ℝ) + 1 ≠ 0 := by positivity
  unfold primeMassFactor
  field_simp [hp1, hpp]
  ring

/-- The complete conductor probability weights have an exact first energy
moment, obtained by a dual-number Euler product of local geometric moments. -/
theorem hasSum_finiteFlipConductorEnergy (F : Finset ℕ) (hF : ∀ p ∈ F, p.Prime) :
    HasSum (fun m : ℕ => finiteFlipConductorCoefficient F m ^ 2 *
      (ramanujanAdjunctionEnergy m - γ)) (finiteFlipConductorEnergyMoment F) := by
  classical
  have hd := (EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum
    (dualConductorWeight_one F) (fun hmn => dualConductorWeight_mul F hmn)
    (fun hp => dual_ladder_norm_summable F hp) F).2
  rw [filter_true_of_mem hF] at hd
  have hprod : (∏ p ∈ F, ∑' k : ℕ, dualConductorWeight F (p ^ k)) =
      momentDual (∏ p ∈ F, primeMassFactor p)
        ((∏ p ∈ F, primeMassFactor p) * finiteFlipConductorEnergyMoment F) := by
    calc
      _ = ∏ p ∈ F, momentDual (primeMassFactor p) (primeMassFactor p *
          (4 * (p : ℝ) * Real.log p / ((p : ℝ) ^ 2 - 1))) := by
        refine prod_congr rfl fun p hp => ?_
        have hlocal := (dual_ladder_hasSum F (hF p hp)).tsum_eq
        simp only [if_pos hp, primeMomentFactor_eq (hF p hp)] at hlocal
        exact hlocal
      _ = _ := dual_product_first_moment F primeMassFactor _
  rw [hprod] at hd
  have hmoment := (TrivSqZeroExt.hasSum_snd ℝ hd).mul_left (finiteFlipHarmonicDensity F ^ 2)
  have hv : finiteFlipHarmonicDensity F ^ 2 *
      ((∏ p ∈ F, primeMassFactor p) * finiteFlipConductorEnergyMoment F) =
      finiteFlipConductorEnergyMoment F := by
    rw [← mul_assoc, density_mass_product F hF, one_mul]
  change HasSum (fun m : Nat.factoredNumbers F => finiteFlipHarmonicDensity F ^ 2 *
      (finiteFlipSpectralWeight F m * conductorEnergy m))
      (finiteFlipHarmonicDensity F ^ 2 *
        ((∏ p ∈ F, primeMassFactor p) * finiteFlipConductorEnergyMoment F)) at hmoment
  rw [hv] at hmoment
  have hnorm : HasSum (fun m : Nat.factoredNumbers F =>
      finiteFlipConductorCoefficient F m ^ 2 * conductorEnergy m)
      (finiteFlipConductorEnergyMoment F) :=
    hmoment.congr_fun fun m => by rw [finiteFlipConductorCoefficient_sq, mul_assoc]
  have hinj : Function.Injective (fun m : Nat.factoredNumbers F => (m : ℕ)) :=
    Subtype.val_injective
  have hz : ∀ m : ℕ, m ∉ Set.range (fun n : Nat.factoredNumbers F => (n : ℕ)) →
      finiteFlipConductorCoefficient F m ^ 2 * conductorEnergy m = 0 := by
    intro m hm
    have hnot : m ∉ Nat.factoredNumbers F := fun h => hm ⟨⟨m, h⟩, rfl⟩
    rw [finiteFlipConductorCoefficient_sq, finiteFlipSpectralWeight_eq, if_neg hnot,
      mul_zero, zero_mul]
  have hfull := (hinj.hasSum_iff hz).mp hnorm
  exact hfull.congr_fun fun m => by
    rw [ramanujanAdjunctionEnergy]
    dsimp only [conductorEnergy]
    ring

private theorem hasSum_tail_one {f : ℕ → ℝ} {L : ℝ} (h : HasSum f L) :
    HasSum (fun k : ℕ => f (k + 1)) (L - f 0) := by
  have hs := (summable_nat_add_iff 1).mpr h.summable
  have hv := h.tsum_eq
  rw [h.summable.tsum_eq_zero_add] at hv
  have ht : (∑' k : ℕ, f (k + 1)) = L - f 0 := by linarith only [hv]
  simpa only [ht] using hs.hasSum

private theorem hasSum_tail_two {f : ℕ → ℝ} {L : ℝ} (h : HasSum f L) :
    HasSum (fun k : ℕ => f (k + 2)) (L - f 0 - f 1) :=
  hasSum_tail_one (hasSum_tail_one h)

/-- A nonempty finite prime set has harmonic density strictly below one. -/
theorem finiteFlipHarmonicDensity_lt_one (F : Finset ℕ) (hF : ∀ p ∈ F, p.Prime)
    (hne : F.Nonempty) : finiteFlipHarmonicDensity F < 1 := by
  classical
  obtain ⟨p, hpF⟩ := hne
  have hp := hF p hpF
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hpp : 0 < (p : ℝ) + 1 := by positivity
  have hc : 0 < ((p : ℝ) - 1) / ((p : ℝ) + 1) := div_pos (sub_pos.mpr hpR) hpp
  have hc1 : ((p : ℝ) - 1) / ((p : ℝ) + 1) < 1 := by
    apply (div_lt_one hpp).mpr
    linarith
  have hE : ∀ q ∈ F.erase p, q.Prime := fun q hq => hF q (mem_of_mem_erase hq)
  have he : finiteFlipHarmonicDensity F =
      (((p : ℝ) - 1) / ((p : ℝ) + 1)) * finiteFlipHarmonicDensity (F.erase p) := by
    calc
      _ = finiteFlipHarmonicDensity (insert p (F.erase p)) :=
        congrArg finiteFlipHarmonicDensity (insert_erase hpF).symm
      _ = _ := prod_insert (fun h => (mem_erase.mp h).1 rfl)
  have hbound : finiteFlipHarmonicDensity F ≤ ((p : ℝ) - 1) / ((p : ℝ) + 1) := by
    rw [he]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (finiteFlipHarmonicDensity_le_one hE) hc.le
  exact hbound.trans_lt hc1

private theorem gap_value_le_energyMoment (F : Finset ℕ) (hF : ∀ p ∈ F, p.Prime)
    (hne : F.Nonempty) {s : ℝ} (hs : 0 < s) (hsδ : s < finiteFlipGreatestGap F) :
    s ≤ finiteFlipHarmonicDensity F ^ 2 / (1 - finiteFlipHarmonicDensity F ^ 2) *
      finiteFlipConductorEnergyMoment F := by
  let c := finiteFlipHarmonicDensity F
  let A := 1 - c ^ 2
  let M := finiteFlipConductorEnergyMoment F
  have hcpos : 0 < c := finiteFlipHarmonicDensity_pos hF
  have hc1 : c < 1 := finiteFlipHarmonicDensity_lt_one F hF hne
  have hcprod := mul_lt_mul_of_pos_left hc1 hcpos
  have hA : 0 < A := by dsimp only [A]; nlinarith only [hcprod, hc1]
  have hs2 := hsδ.trans_le (finiteFlipGreatestGap_bounds F hF).2
  have hden (k : ℕ) : 0 < ramanujanAdjunctionEnergy (k + 2) - γ - s :=
    sub_pos.mpr (hs2.trans_le (conductor_energy_gap k))
  have hzero : finiteFlipConductorCoefficient F 0 = 0 := by
    simp [finiteFlipConductorCoefficient]
  have hmass : HasSum (fun k : ℕ => finiteFlipConductorCoefficient F (k + 2) ^ 2) A := by
    have h := hasSum_tail_two (hasSum_finiteFlipConductorCoefficient_sq F hF)
    simpa only [hzero, zero_pow (by decide : (2 : ℕ) ≠ 0), sub_zero,
      conductor_coefficient_one] using h
  have hmoment : HasSum (fun k : ℕ => finiteFlipConductorCoefficient F (k + 2) ^ 2 *
      (ramanujanAdjunctionEnergy (k + 2) - γ)) M := by
    have h := hasSum_tail_two (hasSum_finiteFlipConductorEnergy F hF)
    simpa only [hzero, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul,
      ramanujanAdjunctionEnergy_one, sub_self, mul_zero, sub_zero] using h
  have hshift : HasSum (fun k : ℕ => finiteFlipConductorCoefficient F (k + 2) ^ 2 *
      (ramanujanAdjunctionEnergy (k + 2) - γ - s)) (M - s * A) :=
    (hmoment.sub (hmass.mul_left s)).congr_fun fun k => by ring
  have hreciprocal : HasSum (fun k : ℕ => finiteFlipConductorCoefficient F (k + 2) ^ 2 /
      (ramanujanAdjunctionEnergy (k + 2) - γ - s))
      (c ^ 2 * finiteFlipSecular F s + c ^ 2 / s) := by
    have h := hasSum_tail_one (hasSum_finiteFlipSecularSeries F hF hs hs2)
    change HasSum (fun k : ℕ => finiteFlipConductorCoefficient F (k + 2) ^ 2 /
      (ramanujanAdjunctionEnergy (k + 2) - γ - s))
      (c ^ 2 * finiteFlipSecular F s -
        finiteFlipConductorCoefficient F 1 ^ 2 / (ramanujanAdjunctionEnergy 1 - γ - s)) at h
    simpa only [conductor_coefficient_one, ramanujanAdjunctionEnergy_one, sub_self,
      zero_sub, div_neg, sub_neg_eq_add] using h
  have hCS (N : ℕ) :
      (∑ k ∈ range N, finiteFlipConductorCoefficient F (k + 2) ^ 2) ^ 2 ≤
        (∑ k ∈ range N, finiteFlipConductorCoefficient F (k + 2) ^ 2 /
          (ramanujanAdjunctionEnergy (k + 2) - γ - s)) *
        (∑ k ∈ range N, finiteFlipConductorCoefficient F (k + 2) ^ 2 *
          (ramanujanAdjunctionEnergy (k + 2) - γ - s)) := by
    apply sum_sq_le_sum_mul_sum_of_sq_le_mul (range N)
      (fun k _ => div_nonneg (sq_nonneg _) (hden k).le)
      (fun k _ => mul_nonneg (sq_nonneg _) (hden k).le)
    intro k _
    apply le_of_eq
    field_simp [(hden k).ne']
  have hlimit := le_of_tendsto_of_tendsto (hmass.tendsto_sum_nat.pow 2)
    (hreciprocal.tendsto_sum_nat.mul hshift.tendsto_sum_nat) (Eventually.of_forall hCS)
  have hshift0 : 0 ≤ M - s * A := by
    rw [← hshift.tsum_eq]
    exact tsum_nonneg fun k => mul_nonneg (sq_nonneg _) (hden k).le
  have hsign := ((finiteFlip_hasHyperplaneGap_iff_secular F hF _).mp
    (isGreatest_finiteFlip_hyperplaneGap F hF).1).2 s hs hsδ
  have hrecipBound : c ^ 2 * finiteFlipSecular F s + c ^ 2 / s ≤ c ^ 2 / s := by
    have h := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg c) hsign
    linarith only [h]
  have hpaid := hlimit.trans (mul_le_mul_of_nonneg_right hrecipBound hshift0)
  have hmul := mul_le_mul_of_nonneg_left hpaid hs.le
  have hcancel : s * (c ^ 2 / s * (M - s * A)) = c ^ 2 * (M - s * A) := by
    field_simp [hs.ne']
  rw [hcancel] at hmul
  have hfinal : s * A ≤ c ^ 2 * M := by
    calc
      _ = s * A ^ 2 + s * c ^ 2 * A := by dsimp only [A]; ring
      _ ≤ _ := by nlinarith only [hmul]
  calc
    s ≤ c ^ 2 * M / A := (le_div_iff₀ hA).mpr hfinal
    _ = _ := by ring

/-- The exact counted first moment bounds the attained greatest hyperplane
gap for every nonempty finite prime set. -/
theorem finiteFlipGreatestGap_le_energyMoment (F : Finset ℕ)
    (hF : ∀ p ∈ F, p.Prime) (hne : F.Nonempty) :
    finiteFlipGreatestGap F ≤
      finiteFlipHarmonicDensity F ^ 2 / (1 - finiteFlipHarmonicDensity F ^ 2) *
        finiteFlipConductorEnergyMoment F := by
  have hpos := finiteFlipGreatestGap_pos F hF
  have hp : ∀ᶠ s : ℝ in 𝓝[<] (finiteFlipGreatestGap F), 0 < s :=
    (lt_mem_nhds hpos).filter_mono nhdsWithin_le_nhds
  have hb : ∀ᶠ s : ℝ in 𝓝[<] (finiteFlipGreatestGap F), s < finiteFlipGreatestGap F :=
    self_mem_nhdsWithin
  have he : ∀ᶠ s : ℝ in 𝓝[<] (finiteFlipGreatestGap F),
      s ≤ finiteFlipHarmonicDensity F ^ 2 / (1 - finiteFlipHarmonicDensity F ^ 2) *
        finiteFlipConductorEnergyMoment F := by
    filter_upwards [hp, hb] with s hs hsδ
    exact gap_value_le_energyMoment F hF hne hs hsδ
  exact le_of_tendsto (tendsto_id.mono_left nhdsWithin_le_nhds) he

end GaloisForLFunctions.ArithmeticCountingPositivity
