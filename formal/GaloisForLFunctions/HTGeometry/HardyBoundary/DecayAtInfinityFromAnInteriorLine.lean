import GaloisForLFunctions.HTGeometry.VitaliConvergence
import Mathlib.Analysis.Complex.PhragmenLindelof
import Mathlib.Analysis.Complex.Convex

/-!
# Decay at infinity from vertical boundary values

A bounded holomorphic function on a right half-plane whose boundary trace
vanishes at infinity tends uniformly to zero at infinity in the half-plane.
The multiplier z/(r+z) suppresses a fixed bounded portion of the boundary.
-/

noncomputable section
open Set Filter Complex Metric
open scoped Topology Asymptotics
namespace GaloisForLFunctions.HTGeometry

private theorem cutoff_bounds {r : ℝ} (hr : 0 < r) (z : ℂ) (hz : 0 ≤ z.re) :
    r ≤ ‖(r:ℂ)+z‖ ∧ ‖z‖ ≤ ‖(r:ℂ)+z‖ := by
  constructor
  · calc r ≤ ((r:ℂ)+z).re := by simp [hz]
         _ ≤ _ := (le_abs_self _).trans (Complex.abs_re_le_norm _)
  · have hh : ‖z‖^2 ≤ ‖(r:ℂ)+z‖^2 := by
      rw [← Complex.normSq_eq_norm_sq,← Complex.normSq_eq_norm_sq,Complex.normSq_apply,Complex.normSq_apply]
      simp only [add_re,ofReal_re,add_im,ofReal_im,zero_add]
      nlinarith only [mul_nonneg hr.le hz,sq_nonneg r]
    nlinarith only [hh,norm_nonneg z,norm_nonneg ((r:ℂ)+z)]

private theorem bounded_right_max {g : ℂ → ℂ} {B η : ℝ}
    (hd : ∀ z : ℂ, 0 ≤ z.re → DifferentiableAt ℂ g z)
    (hb : ∀ z : ℂ, 0 ≤ z.re → ‖g z‖ ≤ B)
    (haxis : ∀ y : ℝ, ‖g ((y:ℂ)*I)‖ ≤ η) {z : ℂ} (hz : 0 ≤ z.re) : ‖g z‖ ≤ η := by
  have hcl : closure {w : ℂ | 0 < w.re} ⊆ {w : ℂ | 0 ≤ w.re} :=
    closure_minimal (fun w hw => show 0 ≤ w.re from le_of_lt hw) (isClosed_le continuous_const continuous_re)
  have hdc : DiffContOnCl ℂ g {w : ℂ | 0 < w.re} :=
    ⟨fun w hw => (hd w (le_of_lt hw)).differentiableWithinAt,
     fun w hw => (hd w (hcl hw)).continuousAt.continuousWithinAt⟩
  apply PhragmenLindelof.right_half_plane_of_bounded_on_real hdc _ _ haxis hz
  · refine ⟨1,by norm_num,0,Asymptotics.IsBigO.of_bound B ?_⟩
    filter_upwards [mem_inf_of_right (mem_principal_self {w : ℂ | 0 < w.re})] with w hw
    simpa only [zero_mul,Real.exp_zero,norm_one,mul_one] using hb w (le_of_lt hw)
  · refine ⟨B,?_⟩
    change ∀ᶠ x : ℝ in atTop, ‖g (x:ℂ)‖ ≤ B
    filter_upwards [eventually_ge_atTop (0:ℝ)] with x hx
    exact hb _ hx

/-- Boundary decay propagates uniformly in all directions of the closed right
half-plane, including the positive real axis. -/
theorem right_half_plane_decay_of_boundary {H : ℂ → ℂ} {K : ℝ}
    (hd : ∀ z : ℂ, 0 ≤ z.re → DifferentiableAt ℂ H z)
    (hb : ∀ z : ℂ, 0 ≤ z.re → ‖H z‖ ≤ K)
    (ha : ∀ ε : ℝ, 0 < ε → ∃ Y : ℝ, ∀ y : ℝ, Y ≤ |y| → ‖H ((y:ℂ)*I)‖ ≤ ε)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℝ, 0 < T ∧ ∀ z : ℂ, 0 ≤ z.re → T ≤ ‖z‖ → ‖H z‖ ≤ ε := by
  let η := ε/2
  have hη : 0 < η := div_pos hε two_pos
  obtain ⟨Y,hY⟩ := ha η hη
  have hK : 0 ≤ K := (norm_nonneg _).trans (hb 0 le_rfl)
  let r := |Y| *K/η+1
  have hr : 0 < r := by dsimp [r]; positivity
  have hrη : |Y| *K ≤ η*r := by
    dsimp [r]
    rw [mul_add,mul_one,show η*(|Y| *K/η) = |Y| *K by field_simp]
    linarith only [hη]
  let g := fun z : ℂ => z*H z/((r:ℂ)+z)
  have hden (z : ℂ) (hz : 0 ≤ z.re) : 0 < ‖(r:ℂ)+z‖ := hr.trans_le (cutoff_bounds hr z hz).1
  have hbd (z : ℂ) (hz : 0 ≤ z.re) : ‖g z‖ ≤ ‖H z‖ := by
    rw [show ‖g z‖ = ‖z‖*‖H z‖/‖(r:ℂ)+z‖ by simp only [g,norm_div,norm_mul], div_le_iff₀ (hden z hz)]
    rw [mul_comm ‖H z‖]
    exact mul_le_mul_of_nonneg_right (cutoff_bounds hr z hz).2 (norm_nonneg _)
  have hgd (z : ℂ) (hz : 0 ≤ z.re) : DifferentiableAt ℂ g z :=
    (differentiableAt_id.mul (hd z hz)).div (differentiableAt_id.const_add _)
      (norm_pos_iff.mp (hden z hz))
  have hsmall (y : ℝ) : ‖g ((y:ℂ)*I)‖ ≤ η := by
    have hy : 0 ≤ ((y:ℂ)*I).re := by simp
    by_cases h : Y ≤ |y|
    · exact (hbd _ hy).trans (hY y h)
    · rw [show ‖g ((y:ℂ)*I)‖ = |y| *‖H ((y:ℂ)*I)‖/‖(r:ℂ)+(y:ℂ)*I‖ by simp [g],div_le_iff₀ (hden _ hy)]
      have h' : |y| ≤ |Y| := (le_of_not_ge h).trans (le_abs_self Y)
      exact (mul_le_mul h' (hb _ hy) (norm_nonneg _) (abs_nonneg _)).trans
        (hrη.trans (mul_le_mul_of_nonneg_left (cutoff_bounds hr _ hy).1 hη.le))
  refine ⟨r,hr,?_⟩
  intro z hz hlarge
  have h := bounded_right_max hgd (fun w hw => (hbd w hw).trans (hb w hw)) hsmall hz
  rw [show ‖g z‖ = ‖z‖*‖H z‖/‖(r:ℂ)+z‖ by simp only [g,norm_div,norm_mul],div_le_iff₀ (hden z hz)] at h
  have hsum : ‖(r:ℂ)+z‖ ≤ 2*‖z‖ := calc
    _ ≤ r+‖z‖ := by simpa [Real.norm_of_nonneg hr.le] using norm_add_le (r:ℂ) z
    _ ≤ _ := by linarith only [hlarge]
  apply le_of_mul_le_mul_left (a := ‖z‖) _ (hr.trans_le hlarge)
  calc ‖z‖*‖H z‖ ≤ η*(2*‖z‖) := h.trans (mul_le_mul_of_nonneg_left hsum hη.le)
       _ = _ := by dsimp [η]; ring

/-- Vanishing on an interior vertical line propagates uniformly to each closed
half-plane strictly inside the domain of bounded holomorphy. -/
theorem interior_half_plane_decay_of_axis {H : ℂ → ℂ} {l K : ℝ} (hl : l < 0)
    (hd : ∀ z : ℂ, l < z.re → DifferentiableAt ℂ H z)
    (hb : ∀ z : ℂ, l < z.re → ‖H z‖ ≤ K)
    (ha : ∀ ε : ℝ, 0 < ε → ∃ Y : ℝ, ∀ y : ℝ, Y ≤ |y| → ‖H ((y:ℂ)*I)‖ ≤ ε)
    {s ε : ℝ} (hs : l < s) (hε : 0 < ε) :
    ∃ T : ℝ, 0 < T ∧ ∀ z : ℂ, s ≤ z.re → T ≤ ‖z‖ → ‖H z‖ ≤ ε := by
  have hright := fun {e : ℝ} (he : 0 < e) => right_half_plane_decay_of_boundary
    (fun z hz => hd z (hl.trans_le hz)) (fun z hz => hb z (hl.trans_le hz)) ha he
  let U := {z : ℂ | l < z.re}
  let Y := {z : ℂ | 0 < z.re}
  have hU : IsOpen U := isOpen_lt continuous_const continuous_re
  have hY : IsOpen Y := isOpen_lt continuous_const continuous_re
  -- A sequence of large vertical translates is locally bounded and tends to
  -- zero on the right half-plane. Vitali identifies its limit on the full domain.
  have hline (e : ℝ) (he : 0 < e) : ∃ B : ℝ, ∀ t : ℝ, B ≤ |t| →
      ‖H ((s:ℂ)+(t:ℂ)*I)‖ ≤ e := by
    by_contra! hbad
    choose t ht hp using fun n : ℕ => hbad (n:ℝ)
    let F := fun n : ℕ => fun z : ℂ => H (z+(t n:ℂ)*I)
    have hre (n : ℕ) (z : ℂ) : (z+(t n:ℂ)*I).re = z.re := by simp
    have hF (n : ℕ) : DifferentiableOn ℂ (F n) U := by
      intro z hz
      exact ((hd _ (by rw [hre]; exact hz)).comp z (differentiableAt_id.add_const _)).differentiableWithinAt
    have hloc (z : ℂ) (hz : z ∈ U) : ∃ r : ℝ, 0 < r ∧ ball z r ⊆ U ∧
        ∃ M : ℝ, ∀ n, ∀ w ∈ ball z r, ‖F n w‖ ≤ M := by
      obtain ⟨r,hr,hrU⟩ := Metric.isOpen_iff.mp hU z hz
      exact ⟨r,hr,hrU,K,fun n w hw => hb _ (by rw [hre]; exact hrU hw)⟩
    have hconv (z : ℂ) (hz : z ∈ Y) : Tendsto (fun n => F n z) atTop (𝓝 0) := by
      apply Metric.tendsto_nhds.mpr
      intro d hd'
      obtain ⟨T,_,hT⟩ := hright (half_pos hd')
      obtain ⟨N,hN⟩ := exists_nat_gt (T+|z.im|)
      filter_upwards [eventually_ge_atTop N] with n hn
      have hg : |t n| ≤ |z.im + t n|+|z.im| := by
        simpa only [add_sub_cancel_left] using abs_sub (z.im+t n) z.im
      have hz' : T ≤ ‖z+(t n:ℂ)*I‖ := by
        have h := Complex.abs_im_le_norm (z+(t n:ℂ)*I)
        simp only [add_im,mul_I_im,ofReal_re] at h
        have hcast : (N:ℝ) ≤ n := by exact_mod_cast hn
        linarith only [ht n,hg,hN,hcast,h]
      rw [dist_zero_right]
      exact (hT _ (by rw [hre]; exact le_of_lt hz) hz').trans_lt (half_lt_self hd')
    have h1 : (1:ℂ) ∈ Y := by change 0 < (1:ℂ).re; norm_num
    have hsub : Y ⊆ U := fun z hz => hl.trans hz
    have hfreq : ∃ᶠ z in 𝓝[≠] (1:ℂ), z ∈ Y :=
      (show ∀ᶠ z in 𝓝[≠] (1:ℂ), z ∈ Y from mem_nhdsWithin_of_mem_nhds (hY.mem_nhds h1)).frequently
    have hv := tendstoLocallyUniformlyOn_of_pointwise_on_uniquenessSet (T := fun _ => (0:ℂ))
      hU (convex_halfSpace_re_gt l).isPreconnected hF hloc (differentiableOn_const 0) hsub (hsub h1) hfreq hconv
    have hlim := (hv.tendsto_at (show (s:ℂ) ∈ U from hs)).norm
    have hsmall : ∀ᶠ n in atTop, ‖F n s‖ < e := by
      simpa only [norm_zero] using hlim.eventually (gt_mem_nhds (by simpa using he : ‖(0:ℂ)‖ < e))
    obtain ⟨n,hn⟩ := hsmall.exists
    exact (hp n).not_ge hn.le
  -- Apply the half-plane maximum principle with the new boundary at s.
  have hre (w : ℂ) (hw : 0 ≤ w.re) : l < ((s:ℂ)+w).re := by
    rw [add_re,ofReal_re]
    linarith only [hs,hw]
  obtain ⟨T,hT,hb'⟩ := right_half_plane_decay_of_boundary (H := fun w => H ((s:ℂ)+w))
    (fun w hw => (hd _ (hre w hw)).comp w (differentiableAt_id.const_add _))
    (fun w hw => hb _ (hre w hw)) hline hε
  refine ⟨T+|s|,add_pos_of_pos_of_nonneg hT (abs_nonneg _),?_⟩
  intro z hz hnorm
  have hgain : T ≤ ‖z-(s:ℂ)‖ := by
    have h := norm_add_le (z-(s:ℂ)) (s:ℂ)
    rw [sub_add_cancel,Complex.norm_real,Real.norm_eq_abs] at h
    linarith only [h,hnorm]
  simpa only [add_sub_cancel] using hb' (z-s) (by simpa using sub_nonneg.mpr hz) hgain

#print axioms interior_half_plane_decay_of_axis
end GaloisForLFunctions.HTGeometry
