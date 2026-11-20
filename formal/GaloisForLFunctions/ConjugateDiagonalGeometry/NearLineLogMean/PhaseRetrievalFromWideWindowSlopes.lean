import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.PhaseRetrievalFromSuccessiveLogWindows
import GaloisForLFunctions.HTGeometry.ComplexExpUnfolding

/-!
# Phase retrieval from the large-bandwidth slope alone

The triangular Fourier multiplier of a log window is affine beyond the
diameter of a finite prefix. Its slope is the unsmoothed intensity.
The independent-frequency argument of Gabet, Ferreira Da Costa and Lee
(arXiv:2611.18900, §4) recovers every finite-bandwidth reading from these
slopes, even when many integer pairs have identical ratios.
-/
noncomputable section
open Finset Complex Filter
open scoped Topology ComplexConjugate
namespace GaloisForLFunctions.ConjugateDiagonalGeometry.LogWindowRetrieval

private def prefixSet (N : ℕ) := Icc 1 N
private def pairs (N : ℕ) := (prefixSet N) ×ˢ (prefixSet N)
private def frequency (p : ℕ × ℕ) : ℂ := ((Real.log p.1-Real.log p.2:ℝ):ℂ)*I
private def amplitude (a : ℕ → ℂ) (p : ℕ × ℕ) := a p.1*conj (a p.2)
private def response (a : ℕ → ℂ) (N : ℕ) (z : ℂ) :=
  ∑ p ∈ pairs N, amplitude a p*cexp (frequency p*z)

private theorem rotated_pair (a : ℕ → ℂ) (t : ℝ) (p : ℕ × ℕ) :
    amplitude a p*cexp (frequency p*t) = translated a t p.1*conj (translated a t p.2) := by
  simp only [amplitude,frequency,translated,map_mul,←Complex.exp_conj,Complex.conj_ofReal,
    Complex.conj_I,mul_neg]
  rw [show ∀ A B C D : ℂ, A*B*(C*D)=A*C*(B*D) by intros; ring,←Complex.exp_add]
  congr 2
  push_cast
  ring

private theorem response_on_real (a : ℕ → ℂ) (N : ℕ) (t : ℝ) :
    response a N t = (‖∑ n ∈ prefixSet N, translated a t n‖^2 : ℝ) := by
  simp only [response,pairs,Finset.sum_product,rotated_pair,←Finset.mul_sum,
    ←Finset.sum_mul,←map_sum,Complex.mul_conj,Complex.normSq_eq_norm_sq]

private theorem energy_finite (a : ℕ → ℂ) (N : ℕ) (d : ℝ) :
    energy a N d = ∑ p ∈ pairs N, (amplitude a p).re*max (d-|(frequency p).im|) 0 := by
  rw [energy,RHTower.Sieve.integral_normSq_logWindowSum]
  simp [pairs,prefixSet,Finset.sum_product,amplitude,frequency,Complex.mul_im]

private theorem gap_bound {N : ℕ} {p : ℕ × ℕ} (hp : p∈pairs N) :
    |(frequency p).im| ≤ Real.log N := by
  obtain ⟨hi,hj⟩ := mem_product.mp hp
  obtain ⟨hi₁,hi₂⟩ := mem_Icc.mp hi
  obtain ⟨hj₁,hj₂⟩ := mem_Icc.mp hj
  have hi' := Real.log_le_log (Nat.cast_pos.mpr hi₁) (Nat.cast_le.mpr hi₂ : (p.1:ℝ) ≤ N)
  have hj' := Real.log_le_log (Nat.cast_pos.mpr hj₁) (Nat.cast_le.mpr hj₂ : (p.2:ℝ) ≤ N)
  simp only [frequency,Complex.mul_I_im,Complex.ofReal_re]
  exact abs_le.mpr ⟨by linarith only [hj',Real.log_natCast_nonneg p.1],
    by linarith only [hi',Real.log_natCast_nonneg p.2]⟩

/-- Beyond the logarithmic diameter the energy is exactly affine in the
bandwidth. Its slope is the squared modulus of the total prefix. -/
theorem wide_window_affine (a : ℕ → ℂ) (N : ℕ) {d : ℝ} (hd : Real.log N ≤ d) :
    energy a N d = d*‖∑ n ∈ Icc 1 N, a n‖^2 -
      ∑ i ∈ Icc 1 N, ∑ j ∈ Icc 1 N, gram (a i) (a j)*|Real.log i-Real.log j| := by
  have hsum : (∑ p ∈ pairs N, (amplitude a p).re) = ‖∑ n ∈ prefixSet N, a n‖^2 := by
    have h := congrArg Complex.re (response_on_real a N 0)
    simpa [response,translated,Complex.re_sum] using h
  rw [energy_finite]
  calc
    _ = ∑ p ∈ pairs N, (d*(amplitude a p).re-(amplitude a p).re*|(frequency p).im|) := by
      refine sum_congr rfl fun p hp => ?_
      rw [max_eq_left (sub_nonneg.mpr ((gap_bound hp).trans hd))]
      ring
    _ = _ := by
      rw [sum_sub_distrib,←mul_sum,hsum]
      simp [pairs,prefixSet,Finset.sum_product,amplitude,frequency,gram,Complex.mul_im]

/-- Any two bandwidths beyond the diameter read the same squared amplitude
by a single divided difference. -/
theorem wide_window_step (a : ℕ → ℂ) (N : ℕ) {d h : ℝ} (hd : Real.log N ≤ d) (hh : 0 ≤ h) :
    energy a N (d+h)-energy a N d = h*‖∑ n ∈ Icc 1 N, a n‖^2 := by
  rw [wide_window_affine a N (hd.trans (le_add_of_nonneg_right hh)),wide_window_affine a N hd]
  ring

theorem wide_window_slope (a : ℕ → ℂ) (N : ℕ) :
    Tendsto (fun d : ℝ => energy a N d/d) atTop (𝓝 (‖∑ n ∈ Icc 1 N,a n‖^2)) := by
  let E := ∑ i ∈ Icc 1 N, ∑ j ∈ Icc 1 N, gram (a i) (a j)*|Real.log i-Real.log j|
  have hz : Tendsto (fun d : ℝ => E/d) atTop (𝓝 0) := Tendsto.div_atTop tendsto_const_nhds tendsto_id
  have h := (tendsto_const_nhds (x:=‖∑ n ∈ Icc 1 N,a n‖^2)).sub hz
  rw [sub_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (Real.log N),eventually_gt_atTop (0:ℝ)] with d hd hp
  rw [wide_window_affine a N hd,sub_div,mul_div_cancel_left₀ _ hp.ne']

private theorem response_entire (a : ℕ → ℂ) (N : ℕ) : AnalyticOnNhd ℂ (response a N) Set.univ := by
  intro z _
  unfold response
  exact Finset.analyticAt_fun_sum _ fun p _ => analyticAt_const.mul
    (Complex.analyticAt_exp.comp ((analyticAt_const (v:=frequency p)).mul analyticAt_id))

private theorem equal_response_of_late_readings {a b : ℕ → ℂ} {N : ℕ} {t₀ : ℝ}
    (hread : ∃ᶠ t : ℝ in 𝓝[≠] t₀,
      Tendsto (fun d : ℝ => (energy (translated a t) N d-energy (translated b t) N d)/d)
        atTop (𝓝 0)) : response a N = response b N := by
  have hr : ∃ᶠ t : ℝ in 𝓝[≠] t₀, response a N t=response b N t := by
    apply hread.mono
    intro t ht
    have h := (wide_window_slope (translated a t) N).sub (wide_window_slope (translated b t) N)
    have hh := tendsto_nhds_unique (by simpa only [sub_div] using ht) h
    rw [response_on_real,response_on_real]
    exact congrArg Complex.ofReal (sub_eq_zero.mp hh.symm)
  have hmap : Tendsto (Complex.ofReal : ℝ → ℂ) (𝓝[≠] t₀) (𝓝[≠] (t₀:ℂ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨(Complex.continuous_ofReal.tendsto _).mono_left nhdsWithin_le_nhds,?_⟩
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact fun he => ht (Complex.ofReal_injective he)
  apply (response_entire a N).eq_of_frequently_eq (response_entire b N)
  exact fun hdeny => hr (hmap.eventually hdeny)

private theorem rotate_energy (a : ℕ → ℂ) (N : ℕ) (t d : ℝ) :
    energy (translated a t) N d =
      (∑ p ∈ pairs N, amplitude a p*(cexp (frequency p*t)*(max (d-|(frequency p).im|) 0:ℝ))).re := by
  rw [energy_finite,Complex.re_sum]
  refine sum_congr rfl fun p _ => ?_
  rw [←mul_assoc,rotated_pair,Complex.mul_re]
  simp only [amplitude,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]

/-- A vanishing finite exponential sum kills every frequency multiplier.
Repeated frequencies are grouped before uniqueness is applied. -/
private theorem zero_after_multiplier {ι : Type*} (S : Finset ι) (c f : ι → ℂ)
    (h : ∀ t : ℝ, ∑ i ∈ S, c i*cexp (f i*t) = 0) (g : ℂ → ℂ) :
    ∑ i ∈ S, c i*g (f i) = 0 := by
  classical
  let T := S.image f
  let A (z : ℂ) := ∑ i ∈ S.filter (fun i => f i=z), c i
  have hmap : ∀ i ∈ S, f i∈T := fun _ hi => mem_image_of_mem _ hi
  have hgroup (F : ℂ → ℂ) : (∑ i ∈ S, c i*F (f i)) = ∑ z ∈ T, A z*F z := by
    rw [←sum_fiberwise_of_maps_to hmap (fun i => c i*F (f i))]
    refine sum_congr rfl fun z _ => ?_
    rw [A,sum_mul]
    exact sum_congr rfl fun i hi => by rw [(mem_filter.mp hi).2]
  have hall := HTGeometry.exp_coeff_eq_zero (S:=T) (C:=A) (fun t => by rw [←hgroup]; exact h t)
  rw [hgroup]
  exact sum_eq_zero fun z hz => by rw [hall z hz,zero_mul]

/-- Slopes from any accumulating set of shifts for each prefix recover the
entire sequence up to one unit phase. Even the accumulation point may vary
from prefix to prefix. Measurement error can grow sublinearly in bandwidth. -/
theorem phase_from_wide_window_slopes (a b : ℕ → ℂ) :
    (∀ N : ℕ, ∃ t₀ : ℝ, ∃ᶠ t : ℝ in 𝓝[≠] t₀,
      Tendsto (fun d : ℝ => (energy (translated a t) N d-energy (translated b t) N d)/d)
        atTop (𝓝 0)) ↔
      ∃ u : ℂ, ‖u‖=1 ∧ ∀ n : ℕ, 0 < n → b n=a n*u := by
  constructor
  · intro h
    have he (N : ℕ) (t d : ℝ) : energy (translated a t) N d=energy (translated b t) N d := by
      obtain ⟨t₀,hr⟩ := h N
      have heq := equal_response_of_late_readings hr
      let c := fun p => amplitude a p-amplitude b p
      have hz (v : ℝ) : (∑ p ∈ pairs N, c p*cexp (frequency p*v))=0 := by
        simp only [c,sub_mul,sum_sub_distrib]
        exact sub_eq_zero.mpr (congrFun heq (v:ℂ))
      have hmul := zero_after_multiplier (pairs N) c frequency hz
        (fun z => cexp (z*t)*(max (d-|z.im|) 0:ℝ))
      simp only [c,sub_mul,sum_sub_distrib,sub_eq_zero] at hmul
      rw [rotate_energy,rotate_energy,hmul]
    apply (two_translates_recover_phase a b).mp
    exact ⟨fun N d => by simpa [translated] using he N 0 d,fun N d => he N Real.pi d⟩
  · rintro ⟨u,hu,h⟩ N
    refine ⟨0,Filter.Eventually.frequently (.of_forall fun t => ?_)⟩
    have hphase : ∀ n : ℕ, 0 < n → translated b t n=translated a t n*u := fun n hn => by
      simp only [translated,h n hn]; ring
    have heq := ((two_translates_recover_phase (translated a t) (translated b t)).mpr ⟨u,hu,hphase⟩).1
    simp only [heq N,sub_self,zero_div]
    exact tendsto_const_nhds

#print axioms wide_window_affine
#print axioms wide_window_slope
#print axioms phase_from_wide_window_slopes
end GaloisForLFunctions.ConjugateDiagonalGeometry.LogWindowRetrieval
