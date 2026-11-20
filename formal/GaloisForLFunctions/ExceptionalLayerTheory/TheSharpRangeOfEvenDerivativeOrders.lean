import GaloisForLFunctions.ExceptionalLayerTheory.TheSquaredNormOfAnAbelianRadical
import Mathlib.Data.Nat.Log
import GaloisForLFunctions.ExceptionalLayerTheory.PrimeRadicalWeightsOfTheDerivativeAreas
import GaloisForLFunctions.ExceptionalLayerTheory.OneHighDerivativeAreaDeterminesTheWholeMultiplicityHistogram

/-!
# The sharp range of even derivative orders

For even j, the first W area weights m^(2/(j+1)) are rationally
independent exactly for W<2^(j+1). The first relation is 4 times the
weight at one equals the weight at 2^(j+1). Odd-degree radical descent
from the cyclotomic field applies regardless of the primality of j+1.
-/
noncomputable section
open Complex Filter Topology RHTower
namespace GaloisForLFunctions.ExceptionalLayerTheory

/-- Real odd-degree radicals in pairwise distinct rational power
classes are independent even for composite degrees. -/
theorem independent_odd_radical_classes {ι : Type*} {n : ℕ} (hn : Odd n)
    (m : ι → ℕ) (hm : ∀ i, 0 < m i)
    (hd : ∀ i j, i≠j → ∀ q : ℚ, q^n≠(m i:ℚ)/m j) :
    LinearIndependent ℚ (fun i => (m i:ℝ)^((n:ℝ)⁻¹)) := by
  have hn0 : 0<n := by obtain ⟨k,h⟩ := hn; omega
  apply independent_cyclotomic_radical_weights hn0 m hm
  letI : NeZero n := ⟨hn0.ne'⟩
  letI : NeZero (n : ℚ) := ⟨Nat.cast_ne_zero.mpr hn0.ne'⟩
  letI : IsCyclotomicExtension {n} ℚ (CyclotomicField n ℚ) :=
    CyclotomicField.isCyclotomicExtension n ℚ
  letI : IsAbelianGalois ℚ (CyclotomicField n ℚ) :=
    IsCyclotomicExtension.isAbelianGalois {n} ℚ (CyclotomicField n ℚ)
  let e : CyclotomicField n ℚ →ₐ[ℚ] ℂ := IsAlgClosed.lift
  intro i j hne v hv
  obtain ⟨q,hq⟩ := (odd_radical_descends_from_abelian_field e hn ((m i:ℚ)/m j)).mp
    ⟨v,by simpa only [Rat.cast_div,Rat.cast_natCast] using hv⟩
  exact hd i j hne q hq

private theorem even_weight_radical (j k : ℕ) :
    orderAreaWeight j k = (((k+1)^2:ℕ):ℝ)^(((j+1:ℕ):ℝ)⁻¹) := by
  rw [orderAreaWeight,div_eq_mul_inv,Real.rpow_mul (Nat.cast_nonneg _),Real.rpow_two,Nat.cast_pow]

theorem even_area_weights_independent {j W : ℕ} (hj : Even j) (hW : W<2^(j+1)) :
    LinearIndependent ℚ (fun k : Fin W => orderAreaWeight j k.val) := by
  have hn : Odd (j+1) := by obtain ⟨k,h⟩ := hj; exact ⟨k,by omega⟩
  simp only [even_weight_radical]
  apply independent_odd_radical_classes hn (fun k : Fin W => (k.val+1)^2)
    (fun k => pow_pos (Nat.succ_pos k.val) _)
  intro i k hne q hq
  have hratio : q^(j+1)=(((i.val+1:ℕ):ℚ)/((k.val+1:ℕ):ℚ))^2 := by
    simpa only [div_pow,Nat.cast_pow] using hq
  obtain ⟨v,hv⟩ := root_of_odd_power_square hn hratio
  have he := small_rational_power_ratio (Nat.succ_pos j) (Nat.succ_pos i.val) (Nat.succ_pos k.val)
    ((Nat.succ_le_of_lt i.isLt).trans_lt hW) ((Nat.succ_le_of_lt k.isLt).trans_lt hW) v hv
  exact hne (Fin.ext (Nat.succ.inj he))

/-- At the first excluded radicand a rational dependence is forced. -/
theorem even_area_weights_independent_iff {j W : ℕ} (hj : Even j) :
    LinearIndependent ℚ (fun k : Fin W => orderAreaWeight j k.val) ↔ W<2^(j+1) := by
  refine ⟨?_,even_area_weights_independent hj⟩
  intro h
  by_contra! hW
  have hbig : 1<(2:ℕ)^(j+1) := by
    simpa only [pow_zero] using (pow_lt_pow_right₀ (by decide : 1<(2:ℕ)) (Nat.succ_pos j))
  let i : Fin W := ⟨0,by omega⟩
  let k : Fin W := ⟨2^(j+1)-1,by omega⟩
  have hne : k≠i := by intro H; have := congrArg Fin.val H; dsimp only [k,i] at this; omega
  let w (t : Fin W) := orderAreaWeight j t.val
  have hi : w i=1 := by simp [w,i,orderAreaWeight]
  have hk : w k=4 := by
    have he : k.val+1=2^(j+1) := by dsimp [k]; omega
    change orderAreaWeight j k.val = 4
    rw [orderAreaWeight,he,Nat.cast_pow,Nat.cast_ofNat,div_eq_mul_inv,mul_comm (2:ℝ) _,
      Real.rpow_mul (by positivity : (0:ℝ)≤(2:ℝ)^(j+1)),
      Real.pow_rpow_inv_natCast (by norm_num : (0:ℝ)≤2) (Nat.succ_ne_zero j),Real.rpow_two]
    norm_num
  have H : Finsupp.linearCombination ℚ w (Finsupp.single k 1) =
      Finsupp.linearCombination ℚ w (Finsupp.single i 4) := by
    simp only [Finsupp.linearCombination_single,one_smul,hk,hi,Rat.smul_def]
    norm_num
  have hh := congrArg (fun v : Fin W →₀ ℚ => v k) (h H)
  exact (one_ne_zero : (1:ℚ)≠0) (by simpa only [Finsupp.single_eq_same,Finsupp.single_eq_of_ne hne] using hh)

/-- The least even integer at least the binary logarithm rounded down. -/
def evenCalibrationOrder (W : ℕ) := 2*((Nat.log 2 W+1)/2)

theorem even_calibration_bounds (W : ℕ) :
    Even (evenCalibrationOrder W) ∧ Nat.log 2 W ≤ evenCalibrationOrder W ∧
    evenCalibrationOrder W ≤ Nat.log 2 W+1 ∧ W<2^(evenCalibrationOrder W+1) := by
  have h₁ : Nat.log 2 W ≤ evenCalibrationOrder W := by unfold evenCalibrationOrder; omega
  have h₂ : evenCalibrationOrder W ≤ Nat.log 2 W+1 := by unfold evenCalibrationOrder; omega
  exact ⟨even_two_mul _,h₁,h₂,Nat.lt_pow_of_log_lt (by decide) (by omega)⟩

/-- A concrete derivative of order at most 1+floor(log₂ W) separates
all bounded integer histograms allowed by winding W. -/
theorem even_calibrated_histograms_injective (W : ℕ) :
    Function.Injective (boundedOrderMoment (W:=W) (evenCalibrationOrder W)) := by
  obtain ⟨hj,_,_,hW⟩ := even_calibration_bounds W
  let j := evenCalibrationOrder W
  have hlin := even_area_weights_independent hj hW
  intro a b he
  let c (i : Fin W) := ((a i).val:ℚ)-(b i).val
  change (∑ i, orderAreaWeight j i.val*((a i).val:ℝ)) =
    ∑ i, orderAreaWeight j i.val*((b i).val:ℝ) at he
  rw [←sub_eq_zero,←Finset.sum_sub_distrib] at he
  have hr : ∑ i, c i • orderAreaWeight j i.val=0 := by
    simpa only [c,Rat.smul_def,Rat.cast_sub,Rat.cast_natCast,sub_mul,mul_comm] using he
  funext i
  have hc := linearIndependent_iff'.mp hlin Finset.univ c hr i (Finset.mem_univ _)
  exact Fin.ext (by exact_mod_cast sub_eq_zero.mp hc)

theorem even_calibrated_area_decodes_xi (c : ℂ) {R : ℝ} (hR : 0<R)
    (hb : ∀ z, ‖z-c‖=R → xi z≠0) :
    let W := (windingNumber (fun θ => xi (c+↑R*exp (I*↑θ))) 0 (2*Real.pi)).toNat
    let j := evenCalibrationOrder W
    ∃ t : Finset ℂ, (∀ z, z∈t ↔ ‖z-c‖<R ∧ xi z=0) ∧
      ∀ᶠ u : ℝ in atTop, ∀ b : BoundedOrderCounts W,
        (∀ e : BoundedOrderCounts W, |xiDerivativeDiskArea j c R u-boundedOrderMoment j b| ≤
          |xiDerivativeDiskArea j c R u-boundedOrderMoment j e|) ↔
          ∀ k, (b k).val=divisorOrderCounts t W k := by
  dsimp only
  let W := (windingNumber (fun θ => xi (c+↑R*exp (I*↑θ))) 0 (2*Real.pi)).toNat
  let j := evenCalibrationOrder W
  obtain ⟨t,ht,hcap,ha⟩ := xi_disk_bounded_order_counts c hR hb
  let a : BoundedOrderCounts W := fun k => ⟨divisorOrderCounts t W k,Nat.lt_succ_of_le (hcap k)⟩
  refine ⟨t,ht,?_⟩
  have hl : Tendsto (xiDerivativeDiskArea j c R) atTop (𝓝 (boundedOrderMoment j a)) := ha j
  filter_upwards [nearest_finite_observation (even_calibrated_histograms_injective W) hl] with u hu
  intro b
  rw [hu]
  exact ⟨fun he k => congrArg Fin.val (congrFun he k),fun he => funext fun k => Fin.ext (he k)⟩

#print axioms even_calibration_bounds
#print axioms even_calibrated_histograms_injective
#print axioms even_calibrated_area_decodes_xi
#print axioms independent_odd_radical_classes
#print axioms even_area_weights_independent_iff
end GaloisForLFunctions.ExceptionalLayerTheory
