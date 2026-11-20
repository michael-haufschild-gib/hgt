import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.OneBandwidthDetectsTwoPointMoebiusCancellation
import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.TheSharpCesaroNormOfAnIncreasingWindow
import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.TheMassProfileOfTheFirstLogarithmicOverlap
import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.TheShortRatioEnergyOfLongMoebiusPolynomials
import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.TheConstantTermOfTheSquarefreeHarmonicDiagonal
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

/-!
# Reading the adjacent Möbius correlation in a critical-line finite part

The Plancherel endpoint used by Wu and Yang (arXiv:2611.05863) gives a
sinc-squared average of a single sharp Dirichlet polynomial. At bandwidth
λ/M, for 1 < λ ≤ 2, its logarithmic main term comes from the squarefree
diagonal. Each unit of ordinary two-point correlation shifts the finite
part by exactly 2(log λ − 1 + 1/λ), in both directions of convergence.
-/

namespace GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.MoebiusGram
open Finset Filter Topology MeasureTheory Complex
open _root_.RHTower hiding linePoint
open _root_.RHTower.Sieve
open GaloisForLFunctions.ConjugateDiagonalGeometry.LogWindowRetrieval
open GaloisForLFunctions.MultiscaleMollifiedZetaField
noncomputable section

/-- The normalized Fejér mean of the sharp critical-line Möbius polynomial. -/
def criticalFejerMean (M : ℕ) (d : ℝ) :=
  ∫ w : ℝ, d*(Real.sinc (Real.pi*d*w))^2*‖moebiusPoly M (linePoint (-(2*Real.pi)*w))‖^2

private theorem fejer_eq_sinc_sq {d : ℝ} (hd : 0 < d) (t : ℝ) :
    (fejerWeightAt d t).re = d*(Real.sinc (d*t/2))^2 := by
  rcases eq_or_ne t 0 with rfl|ht
  · simp [fejerWeightAt_zero hd]
  have hv : d*t/2 ≠ 0 := div_ne_zero (mul_ne_zero hd.ne' ht) (by norm_num)
  rw [fejerWeightAt,integral_fejer_symm_real t ht hd,Complex.ofReal_re,Real.sinc_of_ne_zero hv]
  have hc := Real.cos_two_mul (d*t/2)
  rw [show 2*(d*t/2)=d*t by ring] at hc
  have he : 2-2*Real.cos (d*t) = 4*(Real.sin (d*t/2))^2 := by
    nlinarith only [hc,Real.sin_sq_add_cos_sq (d*t/2)]
  rw [he]
  field_simp [hd.ne',ht]
  ring

/-- Dividing the moving-window energy by its bandwidth produces the
normalized Fejér mean in the critical-line Fourier normalization. -/
theorem critical_window_eq_fejer_mean (M : ℕ) {d : ℝ} (hd : 0 < d) :
    energy (fun n => (coeff n : ℂ)) M d = d*criticalFejerMean M d := by
  rw [energy,gallagher_identity _ _ hd,criticalFejerMean,←integral_const_mul]
  apply integral_congr_ae
  filter_upwards with w
  rw [fourier_triC hd,Complex.re_ofReal_mul,fejer_eq_sinc_sq hd,critical_moebius_logPoly,
    show d*-(2*Real.pi*w)/2 = -(Real.pi*d*w) by ring,Real.sinc_neg]
  ring

private theorem raw_diagonal (M : ℕ) :
    (∑ j ∈ range M, ‖(coeff (j+1) : ℂ)‖^2) = harmonicMoebiusDiagonal M := by
  rw [harmonicMoebiusDiagonal,Nat.floor_natCast,sum_Icc_eq_sum_range_shift]
  apply sum_congr rfl
  intro j _
  simp only [Complex.norm_real,Real.norm_eq_abs,sq_abs,coeff,div_pow,Real.sq_sqrt (Nat.cast_nonneg _),
    mobiusRealCoefficient]

private theorem excess_eq_centered_fejer (M : ℕ) {d : ℝ} (hd : 0<d) :
    normalizedExcess (fun n => (coeff n : ℂ)) M d = criticalFejerMean M d-harmonicMoebiusDiagonal M := by
  rw [normalizedExcess,excessEnergy,critical_window_eq_fejer_mean M hd,raw_diagonal,←mul_sub]
  field_simp [hd.ne']

private theorem squarefree_diagonal_limit :
    Tendsto (fun N : ℕ => harmonicMoebiusDiagonal (N+2:ℕ)-squarefreeDensity*Real.log (N+2:ℕ))
      atTop (𝓝 squarefreeHarmonicConstant) := by
  have hN : Tendsto (fun N : ℕ => ((N+2:ℕ):ℝ)) atTop atTop := by
    apply tendsto_atTop.mpr
    intro z
    filter_upwards [(tendsto_natCast_atTop_atTop (R:=ℝ)).eventually_ge_atTop z] with N h
    exact h.trans (Nat.cast_le.mpr (Nat.le_add_right N 2))
  have hz := ((tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/2)).comp hN).const_mul 12
  rw [mul_zero] at hz
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (.of_forall fun _ => norm_nonneg _) _ hz
  exact .of_forall fun N => by
    rw [Real.norm_eq_abs]
    exact squarefree_harmonic_finite_part (X:=(N+2:ℕ)) (by exact_mod_cast (show 1≤N+2 by omega))

/-- At every fixed first-band scale the ordinary adjacent correlation
has limit a exactly when the Fejér moment has the indicated two-term
asymptotic, with its explicit correlation-dependent finite part. -/
theorem consecutive_moebius_limit_iff_fejer_finite_part {scale : ℝ} (hlo : 1 < scale) (hhi : scale ≤ 2) (a : ℝ) :
    Tendsto (fun N : ℕ => deningerPartialSum consecutiveMoebiusProduct N/((N:ℝ)+1)) atTop (𝓝 a) ↔
    Tendsto (fun N : ℕ => criticalFejerMean (N+2) (scale/((N:ℝ)+2))-squarefreeDensity*Real.log (N+2:ℕ))
      atTop (𝓝 (squarefreeHarmonicConstant+2*a*adjacentMassProfile scale)) := by
  let d (N : ℕ) := scale/((N:ℝ)+2)
  let w (N j : ℕ) := adjacentWeight (d N) (j+1)
  have hd (N : ℕ) : 0<d N := div_pos (zero_lt_one.trans hlo) (by positivity)
  have hscale (N : ℕ) : d N*((N:ℝ)+2) = scale := div_mul_cancel₀ _ (by positivity)
  have hband : ∀ᶠ N : ℕ in atTop, 1+(scale-1) ≤ d N*((N:ℝ)+2) ∧ d N*((N:ℝ)+2) ≤ 2 :=
    .of_forall fun N => by rw [hscale]; exact ⟨by linarith,hhi⟩
  obtain ⟨m,hm,hr⟩ := increasing_adjacent_rows_of_scale_margin d (sub_pos.mpr hlo) hband
  have hend : ∀ᶠ N : ℕ in atTop, ((N:ℝ)+1)*w N N ≤ 1 := .of_forall fun N => by
    have h := adjacent_weight_le_reciprocal (Nat.succ_pos N) (hd N)
    rw [Nat.cast_succ,le_div_iff₀ (by positivity)] at h
    change ((N:ℝ)+1)*adjacentWeight (d N) (N+1) ≤ 1
    linarith only [h]
  have hP : Tendsto (fun N => ∑ j ∈ range (N+1), w N j) atTop (𝓝 (adjacentMassProfile scale)) := by
    have hp := (adjacent_mass_at_scaled_bandwidth hlo.le).comp (tendsto_add_atTop_nat 2)
    apply hp.congr
    intro N
    change adjacentMass (N+2) (scale/((N+2:ℕ):ℝ)) = _
    rw [adjacentMass,sum_Ico_eq_sum_range,show N+2-1=N+1 by omega]
    apply sum_congr rfl
    intro j _
    simp only [w,d,Nat.cast_add,Nat.cast_ofNat,add_comm 1 j]
  have hi := increasing_observation_iff_cesaro_limit consecutiveMoebiusProduct w a hm zero_lt_one hr hend hP
  rw [hi]
  let D (N : ℕ) := harmonicMoebiusDiagonal (N+2:ℕ)-squarefreeDensity*Real.log (N+2:ℕ)
  let Y := weightedPrefix consecutiveMoebiusProduct w
  let F (N : ℕ) := criticalFejerMean (N+2) (d N)-squarefreeDensity*Real.log (N+2:ℕ)
  have hf (N : ℕ) : F N = D N+2*Y N := by
    have ht := normalized_excess_eq_consecutive_products N (hd N) ((hscale N).le.trans hhi)
    rw [excess_eq_centered_fejer _ (hd N)] at ht
    dsimp only [F,D,Y,weightedPrefix,w]
    linarith only [ht]
  have hD : Tendsto D atTop (𝓝 squarefreeHarmonicConstant) := squarefree_diagonal_limit
  change Tendsto Y atTop (𝓝 (a*adjacentMassProfile scale)) ↔ Tendsto F atTop (𝓝 _)
  constructor
  · intro hy
    have h := hD.add (hy.const_mul 2)
    rw [←mul_assoc] at h
    exact h.congr fun N => (hf N).symm
  · intro h
    have hz := (h.sub hD).div_const 2
    rw [show (squarefreeHarmonicConstant+2*a*adjacentMassProfile scale-squarefreeHarmonicConstant)/2 =
      a*adjacentMassProfile scale by ring] at hz
    exact hz.congr fun N => by rw [hf N]; ring

/-- A measured finite part determines the ordinary two-point Möbius limit,
with both measurements taken at the original cutoff M. -/
theorem fejer_finite_part_iff_ordinary_moebius_limit {scale : ℝ}
    (hlo : 1 < scale) (hhi : scale ≤ 2) (C : ℝ) :
    Tendsto (fun M : ℕ => criticalFejerMean M (scale/(M:ℝ))-squarefreeDensity*Real.log M)
      atTop (𝓝 C) ↔
    Tendsto (fun M : ℕ => (∑ n ∈ Icc 1 M, mobiusRealCoefficient n*mobiusRealCoefficient (n+1))/(M:ℝ))
      atTop (𝓝 ((C-squarefreeHarmonicConstant)/(2*adjacentMassProfile scale))) := by
  let a := (C-squarefreeHarmonicConstant)/(2*adjacentMassProfile scale)
  have hp := adjacent_mass_profile_pos hlo
  have he : squarefreeHarmonicConstant+2*a*adjacentMassProfile scale=C := by
    dsimp only [a]
    field_simp [hp.ne']
    ring
  have h := (consecutive_moebius_limit_iff_fejer_finite_part hlo hhi a).symm
  rw [he] at h
  rw [←tendsto_add_atTop_iff_nat (f:=fun M : ℕ =>
    criticalFejerMean M (scale/(M:ℝ))-squarefreeDensity*Real.log M) 2,
    ←tendsto_add_atTop_iff_nat (f:=fun M : ℕ =>
    (∑ n ∈ Icc 1 M, mobiusRealCoefficient n*mobiusRealCoefficient (n+1))/(M:ℝ)) 1]
  have hs (N : ℕ) : (∑ n ∈ Icc 1 (N+1), mobiusRealCoefficient n*mobiusRealCoefficient (n+1)) =
      deningerPartialSum consecutiveMoebiusProduct N := by
    rw [sum_Icc_eq_sum_range_shift,deningerPartialSum]
    exact sum_congr rfl fun j _ => mul_comm _ _
  simp only [hs,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat] at h ⊢
  exact h

#print axioms fejer_finite_part_iff_ordinary_moebius_limit
#print axioms critical_window_eq_fejer_mean
#print axioms consecutive_moebius_limit_iff_fejer_finite_part
end
end GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.MoebiusGram
