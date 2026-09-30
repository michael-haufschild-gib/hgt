/-
Positive even-series transfer for complete Borel kernels.

For everywhere summable real even series with nonnegative numerator coefficients
and strictly positive denominator coefficients, the coefficient-ratio limit
transfers to the full series as real time tends to infinity. The quantitative
prefix/tail estimate makes no truncation of either full series. All-order
coefficient domination yields the optimal coefficient and kernel ceiling.
A ratio limit greater than one forces the numerator-minus-denominator to escape;
a strict degree-one deficit under all-order domination forces the ceiling deficit
to escape. These are generic full-series theorems, with no arithmetic sign or RH
conclusion.
-/
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Normed
open Filter Topology
open scoped BigOperators
namespace RHTower
noncomputable section

def liClockPositiveEvenSeries (a : ℕ → ℝ) (t : ℝ) : ℝ :=
  ∑' j : ℕ, a j*t^(2*j)

private theorem evenPower_nonneg (t : ℝ) (j : ℕ) : 0 ≤ t^(2*j) := by
  rw [pow_mul]
  exact pow_nonneg (sq_nonneg t) j

theorem liClockPositiveEvenSeries_pos {a : ℕ → ℝ}
    (ha : ∀ j, 0 ≤ a j) (ha0 : 0 < a 0) (t : ℝ)
    (hs : Summable (fun j : ℕ => a j*t^(2*j))) :
    0 < liClockPositiveEvenSeries a t := by
  have h := hs.le_tsum 0 (fun j _ => mul_nonneg (ha j) (evenPower_nonneg t j))
  simp only [Nat.mul_zero,pow_zero,mul_one] at h
  exact ha0.trans_le h

private theorem weightedError_summable {a b : ℕ → ℝ} {k t : ℝ}
    (ha : Summable (fun j : ℕ => a j*t^(2*j)))
    (hb : Summable (fun j : ℕ => b j*t^(2*j))) :
    Summable (fun j : ℕ => |a j-k*b j| * t^(2*j)) := by
  have hs := (ha.sub (hb.mul_left k)).abs
  apply hs.congr
  intro j
  rw [show a j*t^(2*j)-k*(b j*t^(2*j))=(a j-k*b j)*t^(2*j) by ring,
    abs_mul,abs_of_nonneg (evenPower_nonneg t j)]

private theorem weightedError_prefix_le (a b : ℕ → ℝ) (k t : ℝ) (J : ℕ)
    (ht : 1 ≤ t) :
    (∑ j ∈ Finset.range J, |a j-k*b j| * t^(2*j)) ≤
      (∑ j ∈ Finset.range J, |a j-k*b j|) * t^(2*(J-1)) := by
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j hj
  have hpow : t^(2*j) ≤ t^(2*(J-1)) :=
    pow_le_pow_right₀ ht (by have := Finset.mem_range.mp hj; omega)
  exact mul_le_mul_of_nonneg_left hpow (abs_nonneg _)

private theorem weightedError_tail_le {a b : ℕ → ℝ} {k t δ : ℝ} (J : ℕ)
    (hb : ∀ j, 0 ≤ b j) (hδ : 0 ≤ δ)
    (haS : Summable (fun j : ℕ => a j*t^(2*j)))
    (hbS : Summable (fun j : ℕ => b j*t^(2*j)))
    (hbound : ∀ j, J ≤ j → |a j-k*b j| ≤ δ*b j) :
    (∑' j : ℕ, |a (j+J)-k*b (j+J)| * t^(2*(j+J))) ≤
      δ*liClockPositiveEvenSeries b t := by
  have he := (summable_nat_add_iff J).2 (weightedError_summable (k:=k) haS hbS)
  have hbs := (summable_nat_add_iff J).2 hbS
  have htail := he.tsum_le_tsum (fun j => by
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_right (hbound (j+J) (by omega))
        (evenPower_nonneg t (j+J))) (hbs.mul_left δ)
  have hp : 0 ≤ ∑ j ∈ Finset.range J, b j*t^(2*j) :=
    Finset.sum_nonneg (fun j _ => mul_nonneg (hb j) (evenPower_nonneg t j))
  have htotal := hbS.sum_add_tsum_nat_add J
  have hsle : (∑' j : ℕ, b (j+J)*t^(2*(j+J))) ≤ liClockPositiveEvenSeries b t := by
    unfold liClockPositiveEvenSeries
    linarith
  calc
    _ ≤ ∑' j : ℕ, δ*(b (j+J)*t^(2*(j+J))) := by simpa only [mul_assoc] using htail
    _ = δ*(∑' j : ℕ, b (j+J)*t^(2*(j+J))) := tsum_mul_left
    _ ≤ _ := mul_le_mul_of_nonneg_left hsle hδ

private theorem weightedError_abs_le {a b : ℕ → ℝ} {k t : ℝ}
    (haS : Summable (fun j : ℕ => a j*t^(2*j)))
    (hbS : Summable (fun j : ℕ => b j*t^(2*j))) :
    |liClockPositiveEvenSeries a t-k*liClockPositiveEvenSeries b t| ≤
      ∑' j : ℕ, |a j-k*b j| * t^(2*j) := by
  have he := weightedError_summable (k:=k) haS hbS
  have hn : Summable (fun j : ℕ => ‖(a j-k*b j)*t^(2*j)‖) := by
    simpa only [Real.norm_eq_abs,abs_mul,abs_of_nonneg (evenPower_nonneg t _)] using he
  have h := norm_tsum_le_tsum_norm hn
  have hsum : (∑' j : ℕ, (a j-k*b j)*t^(2*j)) =
      liClockPositiveEvenSeries a t-k*liClockPositiveEvenSeries b t := by
    simp_rw [sub_mul,mul_assoc]
    rw [haS.tsum_sub (hbS.mul_left k),tsum_mul_left]
    rfl
  rw [hsum] at h
  simpa only [Real.norm_eq_abs,abs_mul,abs_of_nonneg (evenPower_nonneg t _)] using h

private theorem weightedError_complete_le {a b : ℕ → ℝ} {k t δ : ℝ} (J : ℕ)
    (hb : ∀ j, 0 ≤ b j) (hδ : 0 ≤ δ) (ht : 1 ≤ t)
    (haS : Summable (fun j : ℕ => a j*t^(2*j)))
    (hbS : Summable (fun j : ℕ => b j*t^(2*j)))
    (hbound : ∀ j, J ≤ j → |a j-k*b j| ≤ δ*b j) :
    |liClockPositiveEvenSeries a t-k*liClockPositiveEvenSeries b t| ≤
      (∑ j ∈ Finset.range J, |a j-k*b j|) * t^(2*(J-1)) +
        δ*liClockPositiveEvenSeries b t := by
  have he := weightedError_summable (k:=k) haS hbS
  have hsplit := he.sum_add_tsum_nat_add J
  have habs := weightedError_abs_le (k:=k) haS hbS
  rw [← hsplit] at habs
  exact habs.trans (add_le_add (weightedError_prefix_le a b k t J ht)
    (weightedError_tail_le J hb hδ haS hbS hbound))

private theorem evenSeries_relative_error_le {a b : ℕ → ℝ} {k t δ : ℝ}
    (J : ℕ) (hJ : 0 < J) (hb : ∀ j, 0 < b j) (hδ : 0 ≤ δ) (ht : 1 ≤ t)
    (haS : Summable (fun j : ℕ => a j*t^(2*j)))
    (hbS : Summable (fun j : ℕ => b j*t^(2*j)))
    (hbound : ∀ j, J ≤ j → |a j-k*b j| ≤ δ*b j) :
    |liClockPositiveEvenSeries a t/liClockPositiveEvenSeries b t-k| ≤
      (∑ j ∈ Finset.range J, |a j-k*b j|)/(b J*t^2) + δ := by
  have hB := liClockPositiveEvenSeries_pos (fun j => (hb j).le) (hb 0) t hbS
  have htpos : 0 < t := lt_of_lt_of_le (by norm_num : (0:ℝ)<1) ht
  have hden := hbS.le_tsum J (fun j _ => mul_nonneg (hb j).le (evenPower_nonneg t j))
  have hbase : 0 < b J*t^(2*J) := mul_pos (hb J) (pow_pos htpos _)
  have hD : 0 ≤ ∑ j ∈ Finset.range J, |a j-k*b j| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have heq : liClockPositiveEvenSeries a t/liClockPositiveEvenSeries b t-k =
      (liClockPositiveEvenSeries a t-k*liClockPositiveEvenSeries b t)/liClockPositiveEvenSeries b t := by
    field_simp [hB.ne']
  rw [heq,abs_div,abs_of_pos hB]
  have hfull := weightedError_complete_le J (fun j => (hb j).le) hδ ht haS hbS hbound
  calc
    _ ≤ ((∑ j ∈ Finset.range J, |a j-k*b j|)*t^(2*(J-1))+
        δ*liClockPositiveEvenSeries b t)/liClockPositiveEvenSeries b t :=
      div_le_div_of_nonneg_right hfull hB.le
    _ = (∑ j ∈ Finset.range J, |a j-k*b j|)*t^(2*(J-1))/liClockPositiveEvenSeries b t+δ := by
      field_simp [hB.ne']
    _ ≤ (∑ j ∈ Finset.range J, |a j-k*b j|)*t^(2*(J-1))/(b J*t^(2*J))+δ := by
      gcongr
      exact hden
    _ = _ := by
      have hp : t^(2*J)=t^(2*(J-1))*t^2 := by rw [← pow_add]; congr 1; omega
      rw [hp]
      field_simp [pow_ne_zero _ htpos.ne', (hb J).ne']

private theorem coefficientError_le {x y k δ : ℝ} (hy : 0 < y)
    (h : |x/y-k| ≤ δ) : |x-k*y| ≤ δ*y := by
  have heq : x/y-k=(x-k*y)/y := by field_simp [hy.ne']
  rw [heq,abs_div,abs_of_pos hy] at h
  exact (div_le_iff₀ hy).mp h

theorem liClockPositiveEvenSeries_ratio_tendsto {a b : ℕ → ℝ} {k : ℝ}
    (_ha : ∀ j, 0 ≤ a j) (hb : ∀ j, 0 < b j)
    (haS : ∀ t : ℝ, Summable (fun j : ℕ => a j*t^(2*j)))
    (hbS : ∀ t : ℝ, Summable (fun j : ℕ => b j*t^(2*j)))
    (hq : Tendsto (fun j : ℕ => a j/b j) atTop (𝓝 k)) :
    Tendsto (fun t : ℝ => liClockPositiveEvenSeries a t/liClockPositiveEvenSeries b t)
      atTop (𝓝 k) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hδ : 0 < ε/2 := by linarith
  obtain ⟨J0,hJ0⟩ := eventually_atTop.mp ((Metric.tendsto_nhds.mp hq) (ε/2) hδ)
  let J := J0+1
  have hJ : 0 < J := by dsimp [J]; omega
  have htail (j : ℕ) (hj : J ≤ j) : |a j-k*b j| ≤ (ε/2)*b j := by
    have h := hJ0 j (by dsimp [J] at hj; omega)
    have hd : |a j/b j-k| ≤ ε/2 := by simpa only [Real.dist_eq] using h.le
    exact coefficientError_le (hb j) hd
  let D := ∑ j ∈ Finset.range J, |a j-k*b j|
  have hpow : Tendsto (fun t : ℝ => t^2) atTop atTop := tendsto_pow_atTop (by decide)
  have hdecay : Tendsto (fun t : ℝ => D/(b J*t^2)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (hpow.const_mul_atTop (hb J))
  have hsmall := hdecay.eventually_lt_const hδ
  filter_upwards [hsmall,eventually_ge_atTop (1:ℝ)] with t htSmall ht
  rw [Real.dist_eq]
  have herror := evenSeries_relative_error_le J hJ hb hδ.le ht (haS t) (hbS t) htail
  change |liClockPositiveEvenSeries a t/liClockPositiveEvenSeries b t-k| < ε
  dsimp [D] at htSmall
  linarith

theorem liClockPositiveEvenSeries_le_ceiling {a b : ℕ → ℝ} {k : ℝ}
    (hk : ∀ j, a j ≤ k*b j) (t : ℝ)
    (haS : Summable (fun j : ℕ => a j*t^(2*j)))
    (hbS : Summable (fun j : ℕ => b j*t^(2*j))) :
    liClockPositiveEvenSeries a t ≤ k*liClockPositiveEvenSeries b t := by
  have h := haS.tsum_le_tsum (fun j => by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (hk j) (evenPower_nonneg t j))
    (hbS.mul_left k)
  simpa only [liClockPositiveEvenSeries,tsum_mul_left] using h

theorem liClockPositiveEvenSeries_lt_ceiling {a b : ℕ → ℝ} {k : ℝ}
    (hk : ∀ j, a j ≤ k*b j) (h0 : a 0 < k*b 0) (t : ℝ)
    (haS : Summable (fun j : ℕ => a j*t^(2*j)))
    (hbS : Summable (fun j : ℕ => b j*t^(2*j))) :
    liClockPositiveEvenSeries a t < k*liClockPositiveEvenSeries b t := by
  have hs := (hbS.mul_left k).sub haS
  have h := hs.le_tsum 0 (fun j _ => by
    have he : k*(b j*t^(2*j))-a j*t^(2*j)=(k*b j-a j)*t^(2*j) := by ring
    rw [he]
    exact mul_nonneg (sub_nonneg.mpr (hk j)) (evenPower_nonneg t j))
  rw [Summable.tsum_sub (hbS.mul_left k) haS,tsum_mul_left] at h
  simp only [Nat.mul_zero,pow_zero,mul_one] at h
  change k*b 0-a 0 ≤ k*liClockPositiveEvenSeries b t-liClockPositiveEvenSeries a t at h
  linarith

theorem liClockPositiveEvenSeries_tendsto_atTop {b : ℕ → ℝ}
    (hb : ∀ j, 0 ≤ b j) (hb1 : 0 < b 1)
    (hbS : ∀ t : ℝ, Summable (fun j : ℕ => b j*t^(2*j))) :
    Tendsto (liClockPositiveEvenSeries b) atTop atTop := by
  have hl (t : ℝ) : b 1*t^2 ≤ liClockPositiveEvenSeries b t := by
    simpa only [Nat.mul_one,liClockPositiveEvenSeries] using
      (hbS t).le_tsum 1 (fun j _ => mul_nonneg (hb j) (evenPower_nonneg t j))
  exact tendsto_atTop_mono hl ((tendsto_pow_atTop (by decide : (2:ℕ)≠0)).const_mul_atTop hb1)

theorem liClockPositiveEvenSeries_relative_error_le {a b : ℕ → ℝ} {k t δ : ℝ}
    (J : ℕ) (hJ : 0 < J) (_ha : ∀ j, 0 ≤ a j) (hb : ∀ j, 0 < b j)
    (hδ : 0 ≤ δ) (ht : 1 ≤ t)
    (haS : Summable (fun j : ℕ => a j*t^(2*j)))
    (hbS : Summable (fun j : ℕ => b j*t^(2*j)))
    (hbound : ∀ j, J ≤ j → |a j-k*b j| ≤ δ*b j) :
    |liClockPositiveEvenSeries a t/liClockPositiveEvenSeries b t-k| ≤
      (∑ j ∈ Finset.range J, |a j-k*b j|)/(b J*t^2) + δ :=
  evenSeries_relative_error_le J hJ hb hδ ht haS hbS hbound

theorem liClockPositiveEvenSeries_coefficient_ceiling_iff {a b : ℕ → ℝ} {k K : ℝ}
    (_ha : ∀ j, 0 ≤ a j) (hb : ∀ j, 0 < b j)
    (hq : Tendsto (fun j : ℕ => a j/b j) atTop (𝓝 k))
    (hk : ∀ j, a j ≤ k*b j) :
    (∀ j, a j ≤ K*b j) ↔ k ≤ K := by
  constructor
  · intro hK
    exact le_of_tendsto hq (Eventually.of_forall fun j => (div_le_iff₀ (hb j)).mpr (hK j))
  · intro hK j
    exact (hk j).trans (mul_le_mul_of_nonneg_right hK (hb j).le)

theorem liClockPositiveEvenSeries_ceiling_iff {a b : ℕ → ℝ} {k K : ℝ}
    (ha : ∀ j, 0 ≤ a j) (hb : ∀ j, 0 < b j)
    (haS : ∀ t : ℝ, Summable (fun j : ℕ => a j*t^(2*j)))
    (hbS : ∀ t : ℝ, Summable (fun j : ℕ => b j*t^(2*j)))
    (hq : Tendsto (fun j : ℕ => a j/b j) atTop (𝓝 k))
    (hk : ∀ j, a j ≤ k*b j) :
    (∀ t : ℝ, 0 ≤ t → liClockPositiveEvenSeries a t ≤ K*liClockPositiveEvenSeries b t) ↔ k ≤ K := by
  constructor
  · intro hK
    apply le_of_tendsto (liClockPositiveEvenSeries_ratio_tendsto ha hb haS hbS hq)
    filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
    exact (div_le_iff₀ (liClockPositiveEvenSeries_pos (fun j => (hb j).le) (hb 0) t (hbS t))).mpr (hK t ht)
  · intro hK t _
    exact (liClockPositiveEvenSeries_le_ceiling hk t (haS t) (hbS t)).trans
      (mul_le_mul_of_nonneg_right hK (liClockPositiveEvenSeries_pos (fun j => (hb j).le) (hb 0) t (hbS t)).le)

theorem liClockPositiveEvenSeries_sub_tendsto_atTop {a b : ℕ → ℝ} {k : ℝ}
    (ha : ∀ j, 0 ≤ a j) (hb : ∀ j, 0 < b j)
    (haS : ∀ t : ℝ, Summable (fun j : ℕ => a j*t^(2*j)))
    (hbS : ∀ t : ℝ, Summable (fun j : ℕ => b j*t^(2*j)))
    (hq : Tendsto (fun j : ℕ => a j/b j) atTop (𝓝 k)) (hk : 1 < k) :
    Tendsto (fun t : ℝ => liClockPositiveEvenSeries a t-liClockPositiveEvenSeries b t) atTop atTop := by
  have hratio := (liClockPositiveEvenSeries_ratio_tendsto ha hb haS hbS hq).sub_const 1
  have hgrow := hratio.pos_mul_atTop (by linarith : 0 < k-1)
    (liClockPositiveEvenSeries_tendsto_atTop (fun j => (hb j).le) (hb 1) hbS)
  apply Filter.Tendsto.congr' _ hgrow
  exact Eventually.of_forall fun t => by
    have hB := liClockPositiveEvenSeries_pos (fun j => (hb j).le) (hb 0) t (hbS t)
    field_simp [hB.ne']

theorem liClockPositiveEvenSeries_ceiling_sub_tendsto_atTop {a b : ℕ → ℝ} {k : ℝ}
    (_ha : ∀ j, 0 ≤ a j) (_hb : ∀ j, 0 < b j)
    (haS : ∀ t : ℝ, Summable (fun j : ℕ => a j*t^(2*j)))
    (hbS : ∀ t : ℝ, Summable (fun j : ℕ => b j*t^(2*j)))
    (hk : ∀ j, a j ≤ k*b j) (h1 : a 1 < k*b 1) :
    Tendsto (fun t : ℝ => k*liClockPositiveEvenSeries b t-liClockPositiveEvenSeries a t) atTop atTop := by
  have hs (t : ℝ) : Summable (fun j : ℕ => (k*b j-a j)*t^(2*j)) := by
    apply ((hbS t).mul_left k |>.sub (haS t)).congr
    intro j
    ring
  have hgrow := liClockPositiveEvenSeries_tendsto_atTop (fun j => sub_nonneg.mpr (hk j))
    (sub_pos.mpr h1) hs
  apply Filter.Tendsto.congr' _ hgrow
  exact Eventually.of_forall fun t => by
    unfold liClockPositiveEvenSeries
    simp_rw [sub_mul,mul_assoc]
    rw [Summable.tsum_sub ((hbS t).mul_left k) (haS t),tsum_mul_left]

end
end RHTower
