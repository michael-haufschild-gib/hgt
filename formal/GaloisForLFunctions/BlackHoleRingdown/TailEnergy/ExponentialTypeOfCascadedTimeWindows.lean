import GaloisForLFunctions.BlackHoleRingdown.TailEnergy.SpectraOfCascadedRectangularWindows
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Horizontal decay of cascaded time windows

The rectangular-window identity gives |sinc z| ≤ exp |Im z| with
prefactor one. This constant survives the infinite product. Each
positive width also pays for one real-frequency weight, without
increasing the sum of widths in the exponential.
-/

noncomputable section
open Complex Filter Set Topology
open RHTower
namespace GaloisForLFunctions.BlackHoleRingdown

/-- The centered rectangular window, including the resonant frequency. -/
theorem box_integral_eq_twice_sinc (z : ℂ) :
    (∫ x in (-1:ℝ)..1, Complex.exp ((z*I)*(x:ℂ))) = 2*entireSinc z := by
  by_cases hz : z=0
  · subst z
    norm_num [entireSinc_zero]
  · rw [integral_exp_mul_complex (mul_ne_zero hz I_ne_zero),entireSinc_of_ne_zero hz]
    simp only [Complex.ofReal_one,Complex.ofReal_neg,mul_neg,mul_one]
    rw [show -(z*I)=(-z)*I by ring,Complex.exp_mul_I,Complex.exp_mul_I,Complex.cos_neg,Complex.sin_neg]
    field_simp [hz,I_ne_zero] <;> ring

/-- Sharp unit prefactor in the exponential estimate of an entire sinc. -/
theorem norm_entireSinc_le_exp_abs_im (z : ℂ) : ‖entireSinc z‖≤Real.exp |z.im| := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a:=(-1:ℝ)) (b:=1)
    (f:=fun x : ℝ => Complex.exp ((z*I)*(x:ℂ))) (C:=Real.exp |z.im|) (by
      intro x hx
      rw [uIoc_of_le (by norm_num : (-1:ℝ)≤1)] at hx
      rw [Complex.norm_exp]
      apply Real.exp_le_exp.mpr
      have hpt : ((z*I)*(x:ℂ)).re= -(z.im*x) := by simp [Complex.mul_re]
      rw [hpt]
      calc -(z.im*x) ≤ |z.im*x| := neg_le_abs _
           _ = |z.im| * |x| := abs_mul ..
           _ ≤ |z.im| := mul_le_of_le_one_right (abs_nonneg _) (abs_le.mpr ⟨hx.1.le,hx.2⟩))
  rw [box_integral_eq_twice_sinc,norm_mul,Complex.norm_two] at h
  norm_num only [sub_neg_eq_add,one_add_one_eq_two,abs_of_pos (by norm_num : (0:ℝ)<2)] at h
  linarith only [h]

private def normalized (r : ℝ) (z : ℂ) : ℝ :=
  ‖rectangularWindow r z‖/Real.exp (r*|z.im|)

private theorem norm_bounds {r : ℝ} (hr : 0 < r) (z : ℂ) :
    normalized r z≤1 ∧ normalized r z*(1+|z.re|)≤1+1/r := by
  let w := (r:ℂ)*z
  have him : |w.im|=r*|z.im| := by
    dsimp only [w]; simp [Complex.mul_im,abs_mul,abs_of_pos hr]
  have hnorm : ‖w‖=r*‖z‖ := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr]
  let E := Real.exp (r*|z.im|)
  have he : 0<E := Real.exp_pos _
  have hs : ‖entireSinc w‖≤E := by
    simpa only [him,E] using norm_entireSinc_le_exp_abs_im w
  have h₁ : normalized r z≤1 := (div_le_one he).mpr hs
  have h₂ : normalized r z*|z.re|≤1/r := by
    have hsin : ‖entireSinc w‖*‖w‖≤E := by
      by_cases hw : w=0
      · rw [hw,norm_zero,mul_zero]; exact he.le
      · apply (le_div_iff₀ (norm_pos_iff.mpr hw)).mp
        simpa only [him,E] using norm_entireSinc_le_of_ne hw
    have hx := mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm z) (mul_nonneg (norm_nonneg (entireSinc w)) hr.le)
    rw [hnorm,←mul_assoc] at hsin
    change ‖entireSinc w‖/E*|z.re|≤1/r
    rw [div_mul_eq_mul_div,div_le_div_iff₀ he hr,one_mul]
    exact (by simpa only [mul_assoc,mul_comm r |z.re|] using hx.trans hsin)
  exact ⟨h₁,by rw [mul_add,mul_one]; exact add_le_add h₁ h₂⟩

/-- Each polynomial weight may be bought with one initial box. The
exponential type stays the sum of all widths for every polynomial order. -/
theorem windowSpectrum_strip_bound {r : ℕ → ℝ} (hr : ∀ n, 0 < r n ∧ r n≤1)
    (hs : Summable r) (k : ℕ) (z : ℂ) :
    ‖windowSpectrum r z‖*(1+|z.re|)^k ≤
      (∏ j ∈ Finset.range k, (1+1/r j))*Real.exp ((∑' j, r j)*|z.im|) := by
  let P (N : ℕ) := ∏ j ∈ Finset.range N, normalized (r j) z
  let W := 1+|z.re|
  have hpos (n : ℕ) : 0≤normalized (r n) z := div_nonneg (norm_nonneg _) (Real.exp_pos _).le
  have hP (n : ℕ) : 0≤P n := Finset.prod_nonneg fun j _ => hpos j
  have hmono : Antitone P := antitone_nat_of_succ_le fun n => by
    change (∏ j ∈ Finset.range (n+1), normalized (r j) z)≤P n
    rw [Finset.prod_range_succ]
    exact mul_le_of_le_one_right (hP n) (norm_bounds (hr n).1 z).1
  have hfinite (n : ℕ) : P n*W^n ≤ ∏ j ∈ Finset.range n, (1+1/r j) := by
    induction n with
    | zero => simp [P]
    | succ n ih =>
      change (∏ j ∈ Finset.range (n+1), normalized (r j) z)*W^(n+1) ≤ _
      rw [Finset.prod_range_succ,Finset.prod_range_succ,pow_succ]
      calc _ = (P n*W^n)*(normalized (r n) z*W) := by dsimp only [P]; ring
           _ ≤ _ := mul_le_mul ih (norm_bounds (hr n).1 z).2
             (mul_nonneg (hpos n) (by dsimp [W]; positivity)) (Finset.prod_nonneg fun j _ => by
               have := (hr j).1; positivity)
  have hp := (windowSpectrum_hasProd (fun j => ⟨(hr j).1.le,(hr j).2⟩) hs z).tendsto_prod_nat.norm
  have he := ((hs.hasSum.tendsto_sum_nat).mul_const |z.im|).rexp
  have hlim : Tendsto P atTop (𝓝 (‖windowSpectrum r z‖/Real.exp ((∑' j,r j)*|z.im|))) := by
    apply (hp.div he (Real.exp_ne_zero _)).congr
    intro n
    change _ = ∏ j ∈ Finset.range n, ‖rectangularWindow (r j) z‖/Real.exp (r j*|z.im|)
    rw [Finset.prod_div_distrib,←norm_prod,←Real.exp_sum,←Finset.sum_mul]
  have hw : 0≤W^k := pow_nonneg (by dsimp only [W]; positivity) _
  have h := le_of_tendsto (hlim.mul_const (W^k)) (by
    filter_upwards [eventually_ge_atTop k] with n hn
    exact (mul_le_mul_of_nonneg_right (hmono hn) hw).trans (hfinite k))
  rw [div_mul_eq_mul_div] at h
  exact (div_le_iff₀ (Real.exp_pos _)).mp h

#print axioms box_integral_eq_twice_sinc
#print axioms windowSpectrum_strip_bound
end GaloisForLFunctions.BlackHoleRingdown
