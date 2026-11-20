import GaloisForLFunctions.RHTower.XiGaussianHeatHankelSincLevelWitness
import GaloisForLFunctions.Bottcher.Montel
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-!
# Spectra of cascaded rectangular time windows

The rectangular time window in Yang–Zhang–Ying (arXiv:2611.14200, S29)
has a sinc response. Cascading summable widths gives an entire response. Its zeros are
exactly those of the individual factors, including when different
widths give overlapping sets of blind frequencies.
-/

noncomputable section
open Complex Filter Metric Set Topology
open RHTower
namespace GaloisForLFunctions.BlackHoleRingdown

/-- Frequency response of a rectangular window of half-width r. -/
def rectangularWindow (r : ℝ) (z : ℂ) := entireSinc ((r:ℂ)*z)

/-- Frequency response of the infinite sequence of rectangular windows. -/
def windowSpectrum (r : ℕ → ℝ) (z : ℂ) := ∏' n : ℕ, rectangularWindow (r n) z

theorem windowSpectrum_even (r : ℕ → ℝ) : Function.Even (windowSpectrum r) := by
  intro z
  exact tprod_congr fun j => by simp only [rectangularWindow,mul_neg,entireSinc_neg]

private theorem scale_norm {r : ℝ} (hr : 0 ≤ r) (z : ℂ) : ‖(r:ℂ)*z‖=r*‖z‖ := by
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hr]

section
variable {r : ℕ → ℝ} (hr : ∀ n, 0 ≤ r n ∧ r n≤1) (hsum : Summable r)

include hr in
private theorem local_deviation {S : ℝ} (hS : 0<S) :
    ∃ C : ℝ, ∀ n z, z∈ball (0:ℂ) S → ‖rectangularWindow (r n) z-1‖≤C*r n := by
  let B := 2*Real.exp (2*S)
  have hB : 0≤B := by positivity
  have bound (z : ℂ) (hz : z∈ball (0:ℂ) (2*S)) : ‖entireSinc z‖≤B :=
    (norm_entireSinc_le z).trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mem_ball_zero_iff.mp hz).le) (by norm_num))
  let K := 2*B/(2*S)
  have hK : 0≤K := div_nonneg (by positivity) (by positivity)
  refine ⟨K*S,fun n z hz => ?_⟩
  have hR : 2*S/2=S := by ring
  have hstep : (r n:ℂ)*z∈ball (0:ℂ) (2*S/2) := by
    rw [hR,mem_ball_zero_iff,scale_norm (hr n).1]
    exact (mul_le_of_le_one_left (norm_nonneg z) ((hr n).2)).trans_lt
      (mem_ball_zero_iff.mp hz)
  have hzero : (0:ℂ)∈ball (0:ℂ) (2*S/2) := by rw [hR]; exact mem_ball_self hS
  have h := Bottcher.norm_sub_le_of_bounded_on_ball (by positivity : 0<2*S)
    differentiable_entireSinc.differentiableOn bound hstep hzero
  rw [entireSinc_zero,sub_zero,scale_norm (hr n).1] at h
  exact h.trans (calc K*(r n*‖z‖) ≤ K*(r n*S) :=
                         mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
                           (mem_ball_zero_iff.mp hz).le ((hr n).1)) hK
                      _ = _ := by ring)

private theorem factor_diff (r : ℝ) : Differentiable ℂ (rectangularWindow r) :=
  differentiable_entireSinc.comp (differentiable_const.mul differentiable_id)

private theorem centered (w : ℂ) : 1+(w-1)=w := by abel

include hr hsum in
private theorem product_locally {S : ℝ} (hS : 0<S) :
    HasProdLocallyUniformlyOn (fun n => rectangularWindow (r n)) (windowSpectrum r) (ball 0 S) := by
  obtain ⟨C,hC⟩ := local_deviation hr hS
  have h := Summable.hasProdLocallyUniformlyOn_nat_one_add
    (f:=fun n z => rectangularWindow (r n) z-1) isOpen_ball (hsum.mul_left C)
    (Eventually.of_forall hC) (fun n => ((factor_diff (r n)).continuous.sub continuous_const).continuousOn)
  simpa only [centered,windowSpectrum] using h

include hr hsum in
theorem windowSpectrum_hasProd (z : ℂ) :
    HasProd (fun n => rectangularWindow (r n) z) (windowSpectrum r z) :=
  (product_locally hr hsum (by positivity : 0<‖z‖+1)).hasProd
    (mem_ball_zero_iff.mpr (lt_add_one _))

include hr hsum in
/-- The local uniform product is holomorphic even at common zeros of its factors. -/
theorem differentiable_windowSpectrum : Differentiable ℂ (windowSpectrum r) := by
  intro z
  let U := ball (0:ℂ) (‖z‖+1)
  have hz : z∈U := mem_ball_zero_iff.mpr (lt_add_one _)
  have h := (product_locally hr hsum (by positivity : 0<‖z‖+1)).tendstoLocallyUniformlyOn_finsetRange
  have hp (n : ℕ) : DifferentiableOn ℂ (fun w => ∏ j ∈ Finset.range n, rectangularWindow (r j) w) U :=
    (Differentiable.fun_finsetProd fun j _ => factor_diff (r j)).differentiableOn
  exact ((h.differentiableOn (Eventually.of_forall hp) isOpen_ball) z hz).differentiableAt
    (isOpen_ball.mem_nhds hz)

include hr hsum in
theorem windowSpectrum_zero_iff_factor (z : ℂ) :
    windowSpectrum r z=0 ↔ ∃ n, rectangularWindow (r n) z=0 := by
  refine ⟨fun hz => ?_,tprod_of_exists_eq_zero⟩
  by_contra! hall
  obtain ⟨C,hC⟩ := local_deviation hr (by positivity : 0<‖z‖+1)
  have hs : Summable (fun n => ‖rectangularWindow (r n) z-1‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun n => hC n z (mem_ball_zero_iff.mpr (lt_add_one _))) (hsum.mul_left C)
  have hn := tprod_one_add_ne_zero_of_summable (f:=fun n => rectangularWindow (r n) z-1)
    (fun n => by simpa only [centered] using hall n) hs
  exact hn (by simpa only [centered,windowSpectrum] using hz)

end

/-- Positive widths put all zeros of the infinite product on the real axis. -/
theorem windowSpectrum_ne_zero_off_axis {r : ℕ → ℝ} (hr : ∀ n, 0 < r n ∧ r n≤1)
    (hs : Summable r) {z : ℂ} (hz : z.im≠0) : windowSpectrum r z≠0 := by
  intro h
  obtain ⟨n,hn⟩ := (windowSpectrum_zero_iff_factor (fun j => ⟨(hr j).1.le,(hr j).2⟩) hs z).mp h
  exact entireSinc_ne_zero_of_im_ne_zero (by
    simpa [Complex.mul_im] using mul_ne_zero (hr n).1.ne' hz) hn

#print axioms differentiable_windowSpectrum
#print axioms windowSpectrum_zero_iff_factor
#print axioms windowSpectrum_ne_zero_off_axis
end GaloisForLFunctions.BlackHoleRingdown
