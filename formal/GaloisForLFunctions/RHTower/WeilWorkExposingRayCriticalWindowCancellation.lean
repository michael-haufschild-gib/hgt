import GaloisForLFunctions.RHTower.EvenSectorAbelAveraging

/-!
# A vanishing pole moment cancels the critical arithmetic window

Compactness makes the window's Laplace factor vanish to first order when its
half-pole moment is zero. Quadratic Dirichlet cancellation then makes every
right-tail Abel average vanish. Signed coefficients are retained throughout.
-/

open MeasureTheory Filter Topology Set
noncomputable section
namespace RHTower.ExposingRayTransfer
open EvenSector OddSector

private theorem compact_laplace_zero_bound {q : ℝ → ℝ}
    (hq : Continuous q) (hqc : HasCompactSupport q)
    (hz : ∫ u, q u * Real.exp (u/2) = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
      |∫ u, q u * Real.exp ((1/2+s)*u)| ≤ s*C := by
  obtain ⟨D,hD⟩ := hqc.isCompact.isBounded.subset_closedBall 0
  let R := |D|
  have hsupport (u : ℝ) (hu : q u ≠ 0) : |u| ≤ R := by
    have hh := hD (subset_tsupport q hu)
    rw [Metric.mem_closedBall,Real.dist_eq,sub_zero] at hh
    exact hh.trans (le_abs_self D)
  let C := R*Real.exp R*(∫ u, |q u| * Real.exp (u/2))
  have hint : Integrable fun u => |q u| * Real.exp (u/2) :=
    (hq.abs.mul (by fun_prop)).integrable_of_hasCompactSupport hqc.abs.mul_right
  refine ⟨C,by dsimp [C,R]; positivity,fun s hs hs1 => ?_⟩
  have hi (t : ℝ) : Integrable fun u => q u*Real.exp ((1/2+t)*u) :=
    (hq.mul (by fun_prop)).integrable_of_hasCompactSupport hqc.mul_right
  have he : (∫ u,q u*Real.exp ((1/2+s)*u)) =
      ∫ u,q u*Real.exp (u/2)*(Real.exp (s*u)-1) := by
    have h0 : (∫ u,q u*Real.exp ((1/2+(0:ℝ))*u)) = 0 := by
      simpa only [add_zero,one_div,mul_comm (2:ℝ)⁻¹,← div_eq_mul_inv] using hz
    rw [← sub_zero (∫ u,q u*Real.exp ((1/2+s)*u)),← h0,
      ← integral_sub (hi s) (hi 0)]
    apply integral_congr_ae
    filter_upwards [] with u
    have hex : Real.exp ((1/2+s)*u) = Real.exp (u/2)*Real.exp (s*u) := by
      rw [← Real.exp_add]; congr 1; ring
    simp only [add_zero,hex]
    rw [show (1/2:ℝ)*u=u/2 by ring]
    ring
  rw [he]
  calc
    _ ≤ ∫ u, s*R*Real.exp R*(|q u| * Real.exp (u/2)) := by
      rw [← Real.norm_eq_abs]
      apply norm_integral_le_of_norm_le (hint.const_mul _)
      filter_upwards [] with u
      rw [Real.norm_eq_abs,abs_mul,abs_mul,abs_of_pos (Real.exp_pos _)]
      by_cases hu : q u=0
      · simp [hu]
      have hur := hsupport u hu
      have hsu : s*|u| ≤ R :=
        (mul_le_of_le_one_left (abs_nonneg u) hs1).trans hur
      have hb := abs_exp_sub_one_le_mul_exp (s*u)
      have hb' : |Real.exp (s*u)-1| ≤ s*R*Real.exp R := by
        apply hb.trans
        rw [abs_mul,abs_of_nonneg hs]
        exact mul_le_mul (mul_le_mul_of_nonneg_left hur hs)
          (Real.exp_le_exp.mpr hsu) (Real.exp_pos _).le (by positivity)
      nlinarith only [mul_le_mul_of_nonneg_left hb'
        (show 0 ≤ |q u| * Real.exp (u/2) by positivity)]
    _ = s*C := by rw [integral_const_mul]; dsimp [C]; ring

/-- Exact critical cancellation for every compact window with zero half-pole moment. -/
theorem tendsto_abel_window_zero {lam : ℕ → ℝ}
    (hsl : ∀ σ : ℝ, 1<σ → Summable fun n : ℕ => |lam n|/(n:ℝ)^σ)
    (hb : Tendsto (fun s : ℝ => s^2*oddDirichlet lam s) (𝓝[>] 0) (𝓝 0))
    {q : ℝ → ℝ} (hq : Continuous q) (hqc : HasCompactSupport q)
    (hz : ∫ u,q u*Real.exp (u/2)=0) (A : ℝ) :
    Tendsto (fun s : ℝ => s*∫ a in Ici A,
      windowKernelSum lam q a*Real.exp (-(1/2+s)*a)) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨C,hC,hbound⟩ := compact_laplace_zero_bound hq hqc hz
  have hall : Tendsto (fun s : ℝ => s*∫ a,
      windowKernelSum lam q a*Real.exp (-(1/2+s)*a)) (𝓝[>] 0) (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _
      (by simpa using hb.abs.const_mul C)
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0:ℝ)<1)] with s hs
    rw [(integral_kernelSum_mul_exp hsl hq hqc hs.1).2,
      Real.norm_eq_abs,abs_mul,abs_mul,abs_of_pos hs.1]
    have hh := mul_le_mul_of_nonneg_right (hbound s hs.1.le hs.2.le)
      (mul_nonneg hs.1.le (abs_nonneg (oddDirichlet lam s)))
    nlinarith only [hh]
  obtain ⟨D,hD⟩ := hqc.isCompact.isBounded.subset_closedBall 0
  have hzero (u : ℝ) (hu : |D| < |u|) : q u=0 := by
    by_contra hn
    have hh := hD (subset_tsupport q hn)
    rw [Metric.mem_closedBall,Real.dist_eq,sub_zero] at hh
    linarith [le_abs_self D]
  have hi := (integral_kernelSum_mul_exp hsl hq hqc (s := 1/2) (by norm_num)).1
  have hi' : Integrable fun a => windowKernelSum lam q a*Real.exp (-1*a) := by
    convert hi using 1
    norm_num
  let M := Real.exp (2 * |D| + 2 * |A|) *
    ∫ a, |windowKernelSum lam q a*Real.exp (-1*a)|
  have hhead (s : ℝ) (hs : 0<s) (hs1 : s<1) :=
    abs_setIntegral_Iio_mul_exp_le (by norm_num : (0:ℝ)≤1) (by norm_num : (1:ℝ)≤2)
      hi' (abs_nonneg D)
      (fun a ha => kernelSum_eq_zero_of_le lam (abs_nonneg D) hzero ha.le) A
      (μ := 1/2+s) (by linarith) (by linarith)
  have hx : Tendsto (fun s : ℝ => s) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have hheadlim : Tendsto (fun s : ℝ => s*∫ a in Iio A,
      windowKernelSum lam q a*Real.exp (-(1/2+s)*a)) (𝓝[>] 0) (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _
      (by simpa using hx.mul_const M)
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0:ℝ)<1)] with s hs
    rw [Real.norm_eq_abs,abs_mul,abs_of_pos hs.1]
    exact mul_le_mul_of_nonneg_left (hhead s hs.1 hs.2).2 hs.1.le
  have ht := hall.sub hheadlim
  simp only [sub_zero] at ht
  refine ht.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have he := integral_add_compl (s := Iio A) measurableSet_Iio
    (integral_kernelSum_mul_exp hsl hq hqc (show 0<s from hs)).1
  rw [compl_Iio] at he
  rw [← he]
  ring

/-- A cancelled compact window cannot sustain a positive half-exponential tail. -/
theorem nonpos_of_critical_window_tail {lam : ℕ → ℝ}
    (hsl : ∀ σ : ℝ,1<σ → Summable fun n : ℕ => |lam n|/(n:ℝ)^σ)
    (hb : Tendsto (fun s : ℝ => s^2*oddDirichlet lam s) (𝓝[>] 0) (𝓝 0))
    {q : ℝ → ℝ} (hq : Continuous q) (hqc : HasCompactSupport q)
    (hz : ∫ u,q u*Real.exp (u/2)=0) {A c M : ℝ}
    (htail : ∀ a : ℝ,A≤a → c*Real.exp (a/2)-M ≤ windowKernelSum lam q a) : c ≤ 0 := by
  have hlim := tendsto_abel_window_zero hsl hb hq hqc hz A
  have hx : Tendsto (fun s : ℝ => s) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have hleft : Tendsto (fun s : ℝ => c*Real.exp (-s*A)-
      M*s*(Real.exp (-(1/2+s)*A)/(1/2+s))) (𝓝[>] 0) (𝓝 c) := by
    have hc : ContinuousAt (fun s : ℝ => c*Real.exp (-s*A)-
        M*s*(Real.exp (-(1/2+s)*A)/(1/2+s))) 0 := by fun_prop (disch := norm_num)
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  apply le_of_tendsto_of_tendsto hleft hlim
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs0 : 0<s := hs
  have hμ : 0<(1/2:ℝ)+s := by linarith
  have hi := (integral_kernelSum_mul_exp hsl hq hqc hs0).1.integrableOn (s := Ici A)
  have hlo : IntegrableOn (fun a : ℝ => c*Real.exp (-s*a)-M*Real.exp (-(1/2+s)*a))
      (Ici A) := ((integrableOn_exp_neg_Ici hs0 A).const_mul c).sub
        ((integrableOn_exp_neg_Ici hμ A).const_mul M)
  have hh := setIntegral_mono_on hlo hi measurableSet_Ici (fun a ha => ?_)
  · have hiid : (∫ a in Ici A,c*Real.exp (-s*a)-M*Real.exp (-(1/2+s)*a)) =
        c*(Real.exp (-s*A)/s)-M*(Real.exp (-(1/2+s)*A)/(1/2+s)) := by
      rw [integral_sub ((integrableOn_exp_neg_Ici hs0 A).const_mul c)
        ((integrableOn_exp_neg_Ici hμ A).const_mul M),integral_const_mul,
        integral_const_mul,integral_exp_neg_Ici hs0,integral_exp_neg_Ici hμ]
    rw [hiid] at hh
    have hm := mul_le_mul_of_nonneg_left hh hs0.le
    convert hm using 1
    field_simp
  · have he : Real.exp (a/2)*Real.exp (-(1/2+s)*a)=Real.exp (-s*a) := by
      rw [← Real.exp_add]; congr 1; ring
    have hm := mul_le_mul_of_nonneg_right (htail a ha) (Real.exp_pos (-(1/2+s)*a)).le
    rwa [sub_mul,mul_assoc,he] at hm

end RHTower.ExposingRayTransfer
