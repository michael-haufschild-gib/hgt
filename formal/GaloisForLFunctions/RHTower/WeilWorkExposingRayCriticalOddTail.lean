import GaloisForLFunctions.RHTower.WeilWorkExposingRayCriticalOddSource
import GaloisForLFunctions.RHTower.WeilWorkExposingRayDifferentialWidth

/-!
# Literal opposite exposing-tail proportion at critical translation width

The actual odd four-translate Riemann source has atom trace asymptotic to minus
the literal exposingWeight. Its complete error decays at every rate below
2*pi*exp(-3/2), strictly faster than the exposing ray's rate 2*pi*exp(-2).

The proof retains the exact shorter residual and every term of the infinite
exposing mixture. A single uniform packet estimate controls all smaller polar
shifts. Consequently the relative error decays exponentially and the actual
integer atom trace is eventually strictly negative, without RH.

This concerns the full, noncompact source. Its exact compact polar versions and
signed energy identity are proved in the source leaf. Finite-head matching,
vanishing repair cost and the universal WP02 lower inequality remain open.

Paper: docs/reports/weil-work/results/02-exposing-ray/CRITICAL-WIDTH-ODD-PROOF.md.
-/

open MeasureTheory Real Set Filter Topology Zeta23
open scoped ComplexConjugate
noncomputable section
namespace RHTower.ExposingRayCriticalOdd
open ExposingRayWidth ExposingRayTail

private def residualCoefficients : Fin 4 → ℂ :=
  ![-(2*cosh (1/4)*polarWeight 1 : ℝ),1,(2*cosh (1/4)*polarWeight 1 : ℝ),-(2*polarWeight 1 : ℝ)]
private def residualPositions : Fin 4 → ℝ := ![-(1/2),0,1/2,1]

private theorem residual_packet : residual = packet (fun _ : Fin 4 => 0)
    residualCoefficients residualPositions := by
  funext t
  simp [residual,residualFilter,packet,residualCoefficients,residualPositions,
    Fin.sum_univ_succ,riemannKernelDeriv_zero,riemannPhiKernel_eq_ofReal]
  ring

private def polarCoefficients (c : ℝ) : Fin 3 → ℂ := ![1,-(polarWeight c : ℂ),-(polarWeight c : ℂ)]
private def polarPositions (c : ℝ) : Fin 3 → ℝ := ![0,c,-c]

private theorem polar_packet (c : ℝ) : (fun t => (polarShift c riemannKernelReal t : ℂ)) =
    packet (fun _ : Fin 3 => 0) (polarCoefficients c) (polarPositions c) := by
  funext t
  simp [polarShift,packet,polarCoefficients,polarPositions,Fin.sum_univ_succ,
    riemannKernelDeriv_zero,riemannPhiKernel_eq_ofReal]
  ring

private theorem polar_atom (c : ℝ) (n : ℕ) :
    atomCoeff (packet (fun _ : Fin 3 => 0) (polarCoefficients c) (polarPositions c)) n =
      polarExposingKernel c (log n)+polarExposingKernel c (-log n) := by
  rw [← polar_packet]
  unfold atomCoeff EF.weilTest convolution EF.tilde
  simp only [ContinuousLinearMap.mul_apply']
  have he (y : ℝ) : (∫ t : ℝ,(polarShift c riemannKernelReal t : ℂ)*
      conj (polarShift c riemannKernelReal (-(y-t)) : ℂ)) = (polarExposingKernel c y : ℂ) := by
    rw [ExposingRaySmallShift.polarExposingKernel_eq_corr,crossCorr]
    simp only [Complex.conj_ofReal,← Complex.ofReal_mul,show ∀ t : ℝ, -(y-t)=t-y from fun t => by ring]
    exact integral_ofReal
  rw [he,he]
  simp only [Complex.add_re,Complex.ofReal_re]

private theorem polar_mass (c : ℝ) : ∑ j, ‖polarCoefficients c j‖ ≤ 2 := by
  have hp := polarWeight_pos c
  have hq := polarWeight_le_half c
  simp only [polarCoefficients,Fin.sum_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,
    Fin.sum_univ_zero,norm_one,norm_neg,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hp]
  linarith

/-- Width of the exact residual gives every strict rate below the new endpoint. -/
theorem residual_exponential_bound {r : ℝ} (hr : 0 < r) (hrr : r < 2*π*exp (-(3/2))) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → |atomCoeff residual n| ≤ C*exp (-(r*n)) := by
  let a := r/(2*exp (-(2*(3/4:ℝ))))
  have hd : 0 < 2*exp (-(2*(3/4:ℝ))) := by positivity
  have ha : 0 < a := div_pos hr hd
  have haπ : a < π := by
    apply (div_lt_iff₀ hd).mpr
    rw [show -(2*(3/4:ℝ)) = -(3/2:ℝ) by ring]
    nlinarith [hrr]
  have heq : 2*a*exp (-(2*(3/4:ℝ))) = r := by dsimp [a]; field_simp
  obtain ⟨C,hC,hu⟩ := packet_atom_bound (fun _ : Fin 4 => 0) (R:=3/4) ha haπ
  let M := ∑ j, ‖residualCoefficients j‖
  refine ⟨C*(M^2+1),by positivity,fun n hn => ?_⟩
  rw [residual_packet,packet_atom_recenter _ _ _ (1/4)]
  have hx (j : Fin 4) : |residualPositions j-1/4| ≤ (3/4:ℝ) := by
    fin_cases j <;> norm_num [residualPositions]
  have h := hu residualCoefficients (fun j => residualPositions j-1/4) hx n hn
  rw [heq] at h
  exact h.trans (by dsimp [M]; gcongr; linarith)

/-- One bound controls every remaining polar row in the infinite exposing mixture. -/
theorem small_polar_exponential_bound {r : ℝ} (hr : 0 < r) (hrr : r < 2*π*exp (-(3/2))) :
    ∃ C : ℝ, 0 < C ∧ ∀ c : ℝ, 0 ≤ c → c ≤ 1/2 → ∀ n : ℕ, 1 ≤ n →
      |polarExposingKernel c (log n)+polarExposingKernel c (-log n)| ≤ C*exp (-(r*n)) := by
  let a := r/(2*exp (-(2*(3/4:ℝ))))
  have hd : 0 < 2*exp (-(2*(3/4:ℝ))) := by positivity
  have ha : 0 < a := div_pos hr hd
  have haπ : a < π := by
    apply (div_lt_iff₀ hd).mpr
    rw [show -(2*(3/4:ℝ)) = -(3/2:ℝ) by ring]
    nlinarith [hrr]
  have heq : 2*a*exp (-(2*(3/4:ℝ))) = r := by dsimp [a]; field_simp
  obtain ⟨C,hC,hu⟩ := packet_atom_bound (fun _ : Fin 3 => 0) (R:=3/4) ha haπ
  refine ⟨4*C,by positivity,fun c hc0 hc n hn => ?_⟩
  have hx (j : Fin 3) : |polarPositions c j| ≤ (3/4:ℝ) := by
    fin_cases j <;> simp [polarPositions,abs_of_nonneg hc0,abs_neg] <;> linarith
  have h := hu (polarCoefficients c) (polarPositions c) hx n hn
  rw [heq,polar_atom] at h
  have hm := polar_mass c
  have hm0 : 0 ≤ ∑ j, ‖polarCoefficients c j‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hm2 : (∑ j, ‖polarCoefficients c j‖)^2 ≤ 4 := by nlinarith
  exact h.trans (by nlinarith [mul_nonneg (mul_nonneg hC.le (sub_nonneg.mpr hm2)) (exp_pos (-(r*n))).le])

/-- The complete infinite remainder is faster than the leading exposing row. -/
theorem exposing_remainder_bound {r : ℝ} (hr : 0 < r) (hrr : r < 2*π*exp (-(3/2))) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      |exposingWeight n-(polarExposingKernel 1 (log n)+polarExposingKernel 1 (-log n))| ≤
        C*exp (-(r*n)) := by
  obtain ⟨C,hC,h⟩ := small_polar_exponential_bound hr hrr
  refine ⟨2*C,by positivity,fun n hn => ?_⟩
  let f (k : ℕ) := (1/2:ℝ)^k*(polarExposingKernel (1/((k:ℝ)+1)) (log n)+
    polarExposingKernel (1/((k:ℝ)+1)) (-log n))
  have hs : Summable f := summable_exposingWeight_term n
  have ht : ∀ k : ℕ, ‖f (k+1)‖ ≤ (1/2:ℝ)^k*(C*exp (-(r*n))) := by
    intro k
    have hk : 1/((k+1:ℕ)+1:ℝ) ≤ 1/2 := by
      apply (div_le_div_iff₀ (by positivity) (by norm_num)).mpr
      norm_cast
      omega
    have hc := h (1/((k+1:ℕ)+1:ℝ)) (by positivity) hk n hn
    dsimp [f]
    rw [abs_mul,abs_of_nonneg (by positivity : 0 ≤ (1/2:ℝ)^(k+1)),pow_succ]
    calc _ ≤ ((1/2:ℝ)^k*(1/2))*(C*exp (-(r*n))) := by gcongr
      _ ≤ (1/2:ℝ)^k*(C*exp (-(r*n))) := by gcongr; norm_num
  have hb := tsum_of_norm_bounded (hasSum_geometric_two.mul_right (C*exp (-(r*n)))) ht
  have he := hs.tsum_eq_zero_add
  change exposingWeight n = f 0+∑' k : ℕ,f (k+1) at he
  have hf0 : f 0 = polarExposingKernel 1 (log n)+polarExposingKernel 1 (-log n) := by simp [f]
  rw [hf0] at he
  rw [he,add_sub_cancel_left]
  simpa only [Real.norm_eq_abs,mul_assoc] using hb

/-- Actual opposite exposing-tail proportion with a strictly faster absolute remainder. -/
theorem source_exposing_error {r : ℝ} (hr : 0 < r) (hrr : r < 2*π*exp (-(3/2))) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      |atomCoeff source n+exposingWeight n| ≤ C*exp (-(r*n)) := by
  obtain ⟨C,hC,hc⟩ := residual_exponential_bound hr hrr
  obtain ⟨D,hD,hd⟩ := exposing_remainder_bound hr hrr
  refine ⟨C+D,by positivity,fun n hn => ?_⟩
  have he : atomCoeff source n+exposingWeight n = atomCoeff residual n+
      (exposingWeight n-(polarExposingKernel 1 (log n)+polarExposingKernel 1 (-log n))) := by
    linarith [source_atom n]
  rw [he]
  exact (abs_add_le _ _).trans (by linarith [hc n hn,hd n hn])

/-- Exponential relative error against the literal exposing ray, with exact leading coefficient -1. -/
theorem source_relative_error :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ ∀ᶠ n : ℕ in atTop,
      |atomCoeff source n/exposingWeight n+1| ≤ C*exp (-(δ*n)) := by
  let s := 2*π*exp (-(3/2:ℝ))
  have hs : exposingWeightDecayRate < s := by
    unfold exposingWeightDecayRate
    dsimp [s]
    apply mul_lt_mul_of_pos_left _ (by positivity)
    apply exp_lt_exp.mpr
    norm_num
  let r := (exposingWeightDecayRate+s)/2
  let b := (exposingWeightDecayRate+r)/2
  have hr : exposingWeightDecayRate < r := by dsimp [r]; linarith
  have hrs : r < s := by dsimp [r]; linarith
  have hb : exposingWeightDecayRate < b := by dsimp [b]; linarith
  have hbr : b < r := by dsimp [b]; linarith
  obtain ⟨C,hC,hu⟩ := source_exposing_error (exposingWeightDecayRate_pos.trans hr) hrs
  obtain ⟨D,hD,hl⟩ := exposingWeight_exponential_lower hb
  refine ⟨C/D,r-b,by positivity,by linarith,?_⟩
  filter_upwards [hl,eventually_ge_atTop (1:ℕ)] with n hn hn1
  have hw : 0 < exposingWeight n := (mul_pos hD (exp_pos _)).trans_le hn
  have he : C*exp (-(r*n)) = ((C/D)*exp (-((r-b)*n)))*(D*exp (-(b*n))) := by
    rw [show ((C/D)*exp (-((r-b)*n)))*(D*exp (-(b*n))) =
      ((C/D)*D)*(exp (-((r-b)*n))*exp (-(b*n))) by ring,
      div_mul_cancel₀ _ hD.ne',← exp_add]
    congr 2
    ring
  have he' : atomCoeff source n/exposingWeight n+1 =
      (atomCoeff source n+exposingWeight n)/exposingWeight n := by field_simp
  rw [he',abs_div,abs_of_pos hw]
  apply (div_le_iff₀ hw).mpr
  have h := hu n hn1
  rw [he] at h
  exact h.trans (mul_le_mul_of_nonneg_left hn (by positivity))

private theorem exponential_tendsto {δ : ℝ} (hδ : 0 < δ) (C : ℝ) :
    Tendsto (fun n : ℕ => C*exp (-(δ*n))) atTop (𝓝 0) := by
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (exp_pos (-δ)).le
    (exp_lt_one_iff.mpr (by linarith))).const_mul C
  simpa only [← exp_nat_mul,show ∀ n : ℕ, (n:ℝ)*(-δ)=-(δ*n) from fun n => by ring,mul_zero] using h

/-- The actual normalized atom trace converges to minus one. -/
theorem source_exposing_ratio :
    Tendsto (fun n : ℕ => atomCoeff source n/exposingWeight n) atTop (𝓝 (-1)) := by
  obtain ⟨C,δ,hC,hδ,h⟩ := source_relative_error
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have he := (exponential_tendsto hδ C).eventually_lt_const (by simpa using hε)
  obtain ⟨N,hN⟩ := eventually_atTop.mp (h.and he)
  refine ⟨N,fun n hn => ?_⟩
  rw [Real.dist_eq,sub_neg_eq_add]
  exact (hN n hn).1.trans_lt (hN n hn).2

/-- In particular the literal odd source has a strictly negative integer tail. -/
theorem source_eventually_negative : ∀ᶠ n : ℕ in atTop, atomCoeff source n < 0 := by
  have h := source_exposing_ratio.eventually_lt_const (show (-1:ℝ)<0 by norm_num)
  filter_upwards [h,exposingWeight_eventually_pos] with n hn hw
  simpa only [zero_mul] using (div_lt_iff₀ hw).mp hn

end RHTower.ExposingRayCriticalOdd
