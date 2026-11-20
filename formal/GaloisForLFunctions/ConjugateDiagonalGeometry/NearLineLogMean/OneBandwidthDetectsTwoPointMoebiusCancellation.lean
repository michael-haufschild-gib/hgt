import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.TheIncreasingWeightsOfTheFirstLogarithmicOverlap
import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.TheFirstOverlapBandAndTwoPointMoebiusCancellation

/-!
# One bandwidth detects ordinary two-point Möbius cancellation

At each cutoff one may prescribe a single bandwidth. If its product
with the cutoff stays in a closed subinterval of (1,2], convergence
of the resulting energy per unit bandwidth to its diagonal is
equivalent to the ordinary two-point Chowla statement.
-/

namespace GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.MoebiusGram
open Finset Filter Topology
open _root_.RHTower
open GaloisForLFunctions.ConjugateDiagonalGeometry.LogWindowRetrieval
noncomputable section

/-- The product of two consecutive Möbius coefficients. -/
def consecutiveMoebiusProduct (j : ℕ) := mobiusRealCoefficient (j+2)*mobiusRealCoefficient (j+1)

/-- The full off-diagonal energy in the first band is the measured adjacent correlation. -/
theorem normalized_excess_eq_consecutive_products {d : ℝ} (N : ℕ) (hd : 0 < d) (hband : d*((N:ℝ)+2) ≤ 2) :
    normalizedExcess (fun n => (coeff n : ℂ)) (N+2) d =
      2*(∑ j ∈ range (N+1), consecutiveMoebiusProduct j*adjacentWeight d (j+1)) := by
  have hcast : ((N+1+1:ℕ):ℝ) = (N:ℝ)+2 := by push_cast; ring
  have hb : d*((N+1+1:ℕ):ℝ) ≤ 2 := by rwa [hcast]
  rw [normalizedExcess,excess_energy_adjacent_spectrum _ (N+1) hd.le hb,mul_div_assoc,sum_div]
  congr 1
  apply sum_congr rfl
  intro j _
  have hs : Real.sqrt ((j+1:ℕ):ℝ) ≠ 0 := (Real.sqrt_pos.mpr (Nat.cast_pos.mpr (Nat.succ_pos _))).ne'
  have ht : Real.sqrt ((j+2:ℕ):ℝ) ≠ 0 := (Real.sqrt_pos.mpr (Nat.cast_pos.mpr (Nat.succ_pos _))).ne'
  simp only [gram,Complex.conj_ofReal,←Complex.ofReal_mul,Complex.ofReal_re,coeff,consecutiveMoebiusProduct,adjacentWeight]
  rw [←Nat.cast_succ (n:=j+1)]
  field_simp [hs,ht,hd.ne']

private theorem cesaro_shift (f : ℕ → ℝ)
    (h : Tendsto (fun N : ℕ => deningerPartialSum f N/((N:ℝ)+1)) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => (∑ j ∈ range N, f j)/((N:ℝ)+1)) atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds] at h ⊢
  intro ε hε
  obtain ⟨K,hK⟩ := eventually_atTop.mp (h ε hε)
  filter_upwards [eventually_ge_atTop (K+1)] with N hN
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N ≠ 0)
  have hh := hK n (by omega)
  change dist (deningerPartialSum f n/((n:ℝ)+1)) 0 < ε at hh
  change dist (deningerPartialSum f n/((n.succ:ℝ)+1)) 0 < ε
  have hp : 0 < (n:ℝ)+1 := by positivity
  have hs : 0 < (n.succ:ℝ)+1 := by positivity
  rw [Real.dist_eq,sub_zero,abs_div,abs_of_pos hp,div_lt_iff₀ hp] at hh
  rw [Real.dist_eq,sub_zero,abs_div,abs_of_pos hs,div_lt_iff₀ hs,Nat.cast_succ]
  linarith only [hh,hε]

/-- One energy observation per cutoff detects two-point Chowla for every
prescribed bandwidth with a fixed positive margin above inverse length. -/
theorem two_point_moebius_iff_one_bandwidth (d : ℕ → ℝ) {η : ℝ} (hη : 0<η)
    (hband : ∀ᶠ N : ℕ in atTop, 1+η ≤ d N*((N:ℝ)+2) ∧ d N*((N:ℝ)+2) ≤ 2) :
    Tendsto (fun N : ℕ => (∑ j ∈ range N, mobiusRealCoefficient (j+2)*mobiusRealCoefficient (j+1))/
      ((N:ℝ)+1)) atTop (𝓝 0) ↔
    Tendsto (fun N : ℕ => normalizedExcess (fun n => (coeff n : ℂ)) (N+2) (d N)) atTop (𝓝 0) := by
  constructor
  · intro h
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨K,hK⟩ := eventually_atTop.mp (two_point_moebius_implies_near_diagonal h (ε/2) (half_pos hε))
    filter_upwards [eventually_ge_atTop K,hband] with N hN hb
    have ht : ((N+1+1:ℕ):ℝ) = (N:ℝ)+2 := by push_cast; ring
    have hh := hK (N+1) (by omega) (d N) (by rw [ht]; linarith only [hb.1,hη]) (by simpa only [ht] using hb.2)
    change dist (normalizedExcess _ (N+2) (d N)) 0 < ε
    rw [Real.dist_eq,sub_zero]
    linarith only [hh,hε]
  · intro h
    obtain ⟨m,hm,hr⟩ := increasing_adjacent_rows_of_scale_margin d hη hband
    apply cesaro_shift consecutiveMoebiusProduct
    apply cesaro_zero_of_increasing_window_readings _ _ hm hr
    have hh := h.div_const 2
    rw [zero_div] at hh
    apply hh.congr'
    filter_upwards [hband] with N hb
    have hM : 0 < (N:ℝ)+2 := by positivity
    have hd := pos_of_mul_pos_left (lt_of_lt_of_le (by linarith only [hη] : 0<1+η) hb.1) hM.le
    change normalizedExcess _ (N+2) (d N)/2 = _
    rw [normalized_excess_eq_consecutive_products N hd hb.2,weightedPrefix]
    ring

/-- The fixed choice 3/(2M) at every cutoff M suffices. -/
theorem two_point_moebius_iff_three_halves_bandwidth :
    Tendsto (fun N : ℕ => (∑ j ∈ range N, mobiusRealCoefficient (j+2)*mobiusRealCoefficient (j+1))/
      ((N:ℝ)+1)) atTop (𝓝 0) ↔
    Tendsto (fun N : ℕ => normalizedExcess (fun n => (coeff n : ℂ)) (N+2) ((3/2)/((N:ℝ)+2)))
      atTop (𝓝 0) := by
  apply two_point_moebius_iff_one_bandwidth _ (η:=1/2) (by norm_num)
  filter_upwards with N
  rw [div_mul_cancel₀ _ (by positivity : (N:ℝ)+2 ≠ 0)]
  norm_num

private theorem ordinary_mean_zero_iff (S : ℕ → ℝ) :
    Tendsto (fun N : ℕ => S N/(N:ℝ)) atTop (𝓝 0) ↔
    Tendsto (fun N : ℕ => S N/((N:ℝ)+1)) atTop (𝓝 0) := by
  have hi : Tendsto (fun N : ℕ => (N:ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hf := (tendsto_const_nhds (x:=(1:ℝ))).add hi
  rw [add_zero] at hf
  constructor
  · intro h
    have hh := h.div hf one_ne_zero
    rw [zero_div] at hh
    apply hh.congr'
    filter_upwards [eventually_ge_atTop (1:ℕ)] with N hN
    have hn : 0<(N:ℝ) := Nat.cast_pos.mpr hN
    change S N/(N:ℝ)/(1+(N:ℝ)⁻¹)=_
    rw [div_div,mul_add,mul_one,mul_inv_cancel₀ hn.ne']
  · intro h
    have hh := h.mul hf
    rw [zero_mul] at hh
    apply hh.congr'
    filter_upwards [eventually_ge_atTop (1:ℕ)] with N hN
    have hn : 0<(N:ℝ) := Nat.cast_pos.mpr hN
    change S N/((N:ℝ)+1)*(1+(N:ℝ)⁻¹)=_
    field_simp [hn.ne',show (N:ℝ)+1≠0 by positivity]

/-- Ordinary unweighted two-point Chowla, with its original cutoff and
normalization, is equivalent to one prescribed energy reading per cutoff. -/
theorem chowla_iff_one_window_per_cutoff (d : ℕ → ℝ) {η : ℝ} (hη : 0<η)
    (hband : ∀ᶠ M : ℕ in atTop, 1+η ≤ d M*(M:ℝ) ∧ d M*(M:ℝ) ≤ 2) :
    Tendsto (fun M : ℕ => (∑ n ∈ Icc 1 M, mobiusRealCoefficient n*mobiusRealCoefficient (n+1))/(M:ℝ))
      atTop (𝓝 0) ↔
    Tendsto (fun M : ℕ => normalizedExcess (fun n => (coeff n:ℂ)) M (d M)) atTop (𝓝 0) := by
  have hsum (M : ℕ) : (∑ n ∈ Icc 1 M, mobiusRealCoefficient n*mobiusRealCoefficient (n+1)) =
      ∑ n ∈ range M, mobiusRealCoefficient (n+2)*mobiusRealCoefficient (n+1) := by
    rw [sum_Icc_eq_sum_range_shift]
    exact sum_congr rfl fun n _ => mul_comm _ _
  simp_rw [hsum]
  rw [ordinary_mean_zero_iff]
  have hs := (tendsto_add_atTop_nat 2).eventually hband
  have h := two_point_moebius_iff_one_bandwidth (fun N => d (N+2)) hη (by
    filter_upwards [hs] with N hN
    simpa only [Nat.cast_add,Nat.cast_ofNat] using hN)
  exact h.trans (tendsto_add_atTop_iff_nat (f:=fun M : ℕ =>
    normalizedExcess (fun n => (coeff n:ℂ)) M (d M)) (l:=𝓝 (0:ℝ)) 2)

#print axioms chowla_iff_one_window_per_cutoff

#print axioms two_point_moebius_iff_one_bandwidth
#print axioms two_point_moebius_iff_three_halves_bandwidth
end
end GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.MoebiusGram
