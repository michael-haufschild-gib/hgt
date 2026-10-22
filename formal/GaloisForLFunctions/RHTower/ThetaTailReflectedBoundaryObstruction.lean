import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspChargedBoundaryGrowth
import GaloisForLFunctions.RHTower.ThetaTailAnalyticLocality
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Charged-cusp obstruction to a reflected Cauchy comparison

The exact complex diagonal of the tail realization is the weighted integral
`4 ∫ (re z+s) |Phi(z+s)|^2 ds`. At the charged points, this is bounded by
`24*486^2*N^10`, while the reflected Cauchy diagonal grows at least as `N^12`.
Every positive reflected comparison therefore has a negative complex diagonal.

This file alone does not transfer that defect to finite real packets. It does
not prove a negative direction for the unsubtracted theta tail kernel.
-/

noncomputable section
namespace RHTower.DominatedL2Sections
open MeasureTheory Set Filter Topology
open scoped InnerProductSpace

theorem StripSource.channel_difference_re (P : StripSource) (z : ℂ) (s : ℝ) :
    (star (P.channel 1 z s)*P.channel 1 z s-
      star (P.channel (-1) z s)*P.channel (-1) z s).re =
    (Ioi (0:ℝ)).indicator (fun s => 4*(z.re+s)*‖P.phi (z+(s:ℂ))‖^2) s := by
  by_cases hs : s ∈ Ioi (0:ℝ)
  · simp only [StripSource.channel, Set.indicator_of_mem hs, Complex.sq_norm,
      Complex.normSq_apply, Complex.star_def, Complex.sub_re, Complex.mul_re,
      Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im]
    ring
  · simp [StripSource.channel, Set.indicator_of_notMem hs]

theorem StripSource.integrable_weighted_source_norm (P : StripSource) {z : ℂ}
    (hz : z ∈ thetaCuspStrip) :
    IntegrableOn (fun s : ℝ => 4*(z.re+s)*‖P.phi (z+(s:ℂ))‖^2) (Ioi 0) := by
  have h := ((((P.family 1).memLp hz).star.integrable_mul ((P.family 1).memLp hz)).sub
    (((P.family (-1)).memLp hz).star.integrable_mul ((P.family (-1)).memLp hz))).re
  have he : (fun s => (star (P.channel 1 z s)*P.channel 1 z s-
      star (P.channel (-1) z s)*P.channel (-1) z s).re) =
      (Ioi (0:ℝ)).indicator (fun s => 4*(z.re+s)*‖P.phi (z+(s:ℂ))‖^2) :=
    funext (P.channel_difference_re z)
  change Integrable (fun s => (star (P.channel 1 z s)*P.channel 1 z s-
      star (P.channel (-1) z s)*P.channel (-1) z s).re) at h
  rw [he] at h
  exact (integrable_indicator_iff measurableSet_Ioi).mp h

theorem StripSource.realization_diagonal_integral (P : StripSource) {z : ℂ}
    (hz : z ∈ thetaCuspStrip) :
    (P.realization.kernel z z).re =
      ∫ s : ℝ in Ioi 0, 4*(z.re+s)*‖P.phi (z+(s:ℂ))‖^2 := by
  have hi := (((P.family 1).memLp hz).star.integrable_mul ((P.family 1).memLp hz)).sub
    (((P.family (-1)).memLp hz).star.integrable_mul ((P.family (-1)).memLp hz))
  rw [P.realization_kernel hz hz, P.inner_difference hz hz]
  calc
    _ = ∫ s : ℝ, (star (P.channel 1 z s)*P.channel 1 z s-
        star (P.channel (-1) z s)*P.channel (-1) z s).re :=
      (Complex.reCLM.integral_comp_comm hi).symm
    _ = _ := by
      simp_rw [P.channel_difference_re]
      rw [integral_indicator measurableSet_Ioi]

theorem StripSource.realization_diagonal_le (P : StripSource) {z : ℂ}
    (hz : z ∈ thetaCuspStrip) (hz1 : z.re ≤ 1)
    {C : ℝ}
    (hPhi : ∀ s : ℝ, 0 ≤ s → ‖P.phi (z+(s:ℂ))‖ ≤ C*Real.exp (-s/2)) :
    (P.realization.kernel z z).re ≤ 24*C^2 := by
  have hi := integrableOn_exp_mul_Ioi (a := -(1/2:ℝ)) (by norm_num) (0:ℝ)
  have hmaj : IntegrableOn (fun s : ℝ => 12*C^2*Real.exp (-(1/2)*s)) (Ioi 0) :=
    hi.const_mul _
  rw [P.realization_diagonal_integral hz]
  calc
    _ ≤ ∫ s : ℝ in Ioi 0, 12*C^2*Real.exp (-(1/2)*s) := by
      apply setIntegral_mono_on (P.integrable_weighted_source_norm hz) hmaj measurableSet_Ioi
      intro s hs
      have hs0 : 0 ≤ s := hs.le
      have hsq : ‖P.phi (z+(s:ℂ))‖^2 ≤ C^2*Real.exp (-s) := by
        have h := pow_le_pow_left₀ (norm_nonneg _) (hPhi s hs0) 2
        rw [mul_pow, ← Real.exp_nat_mul] at h
        norm_num only [Nat.cast_ofNat] at h
        simpa only [show 2*(-s/2) = -s by ring] using h
      have hlin : 1+s ≤ 3*Real.exp (s/2) := by
        have h1 := Real.add_one_le_exp (s/2)
        have h0 := Real.one_le_exp (show 0 ≤ s/2 by positivity)
        linarith only [h1, h0]
      calc
        _ ≤ 4*(1+s)*(C^2*Real.exp (-s)) :=
          mul_le_mul (by linarith only [hz1]) hsq (sq_nonneg _) (by positivity)
        _ ≤ 4*(3*Real.exp (s/2))*(C^2*Real.exp (-s)) := by gcongr
        _ = _ := by
          rw [show 4*(3*Real.exp (s/2))*(C^2*Real.exp (-s)) =
            12*C^2*(Real.exp (s/2)*Real.exp (-s)) by ring, ← Real.exp_add]
          congr 2
          ring
    _ = _ := by rw [integral_const_mul, integral_exp_mul_Ioi (by norm_num : -(1/2:ℝ)<0)]; norm_num; ring

end RHTower.DominatedL2Sections

namespace RHTower.ThetaCuspBoundaryAudit
open DominatedL2Sections MeasureTheory Set Filter Topology

theorem chargedPoint_kernel_diagonal_upper (N : ℕ) (hN : 0 < N) :
    (completeThetaSource.realization.kernel (chargedPoint (1/(N:ℝ)^2))
      (chargedPoint (1/(N:ℝ)^2))).re ≤ 24*486^2*(N:ℝ)^10 := by
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hN
  have heps : 0 < 1/(N:ℝ)^2 := by positivity
  have heps1 : 1/(N:ℝ)^2 ≤ 1 := by rw [div_le_one (by positivity)]; nlinarith only [hN1]
  have hr := chargedPoint_re_bounds heps heps1
  have h := completeThetaSource.realization_diagonal_le (chargedPoint_mem_strip heps)
    hr.2 (C := 486*(N:ℝ)^5)
    (fun s hs => chargedPoint_source_horizontal_upper N hN s)
  convert h using 1; ring


def reflectedRate (z : ℂ) : ℂ := Complex.exp (2*z)+Complex.exp (-2*z)

theorem reflectedRate_re_pos {z : ℂ} (hz : z ∈ thetaCuspStrip) :
    0 < (reflectedRate z).re := by
  have hc : 0 < Real.cos (2*z.im) := by
    change |z.im| < Real.pi/4 at hz
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> linarith [le_abs_self z.im, neg_le_abs z.im]
  have hre : (reflectedRate z).re =
      (Real.exp (2*z.re)+Real.exp (-2*z.re))*Real.cos (2*z.im) := by
    simp only [reflectedRate, Complex.add_re, Complex.exp_re, Complex.mul_re, Complex.mul_im,
      Complex.re_ofNat, Complex.im_ofNat, Complex.neg_re, Complex.neg_im, zero_mul,
      sub_zero, add_zero, neg_mul, Real.cos_neg]
    ring
  rw [hre]
  positivity

theorem reflectedRate_chargedPoint_re {eps : ℝ} (heps : 0 < eps) :
    (reflectedRate (chargedPoint eps)).re = eps+eps/(eps^2+4) := by
  have he : Complex.exp (-2*chargedPoint eps) = ((eps:ℂ)+2*Complex.I)⁻¹ := by
    rw [show (-2:ℂ)*chargedPoint eps = -(2*chargedPoint eps) by ring,
      Complex.exp_neg, chargedPoint_exp heps]
  rw [reflectedRate, he, chargedPoint_exp heps]
  simp only [Complex.add_re, Complex.inv_re, Complex.mul_re, Complex.mul_im,
    Complex.re_ofNat, Complex.im_ofNat, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.normSq_apply, Complex.add_im]
  ring

theorem reflectedRate_chargedPoint_re_le {eps : ℝ} (heps : 0 < eps) :
    (reflectedRate (chargedPoint eps)).re ≤ 2*eps := by
  rw [reflectedRate_chargedPoint_re heps]
  have h : eps/(eps^2+4) ≤ eps := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith only [heps, mul_nonneg heps.le (sq_nonneg eps)]
  linarith only [h]


theorem chargedPoint_comparison_lower (N : ℕ) (hN : 0 < N) :
    (12*Real.pi^2*Real.exp (-4*Real.pi))^2/2*(N:ℝ)^12 ≤
      ‖thetaCuspStripSource (chargedPoint (1/(N:ℝ)^2))‖^2 /
        (reflectedRate (chargedPoint (1/(N:ℝ)^2))).re := by
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  have heps : 0 < 1/(N:ℝ)^2 := by positivity
  have hq0 := reflectedRate_re_pos (chargedPoint_mem_strip heps)
  have hq := reflectedRate_chargedPoint_re_le heps
  have hPhi := chargedPoint_source_lower N hN
  let A := 12*Real.pi^2*Real.exp (-4*Real.pi)
  have hA : 0 < A := by dsimp [A]; positivity
  have hsq : A^2*(N:ℝ)^10 ≤ ‖thetaCuspStripSource (chargedPoint (1/(N:ℝ)^2))‖^2 := by
    have h := pow_le_pow_left₀ (by positivity : 0 ≤ A*(N:ℝ)^5) hPhi 2
    simpa only [mul_pow, ← pow_mul] using h
  rw [le_div_iff₀ hq0]
  calc
    _ ≤ (A^2/2*(N:ℝ)^12)*(2*(1/(N:ℝ)^2)) :=
      mul_le_mul_of_nonneg_left hq (by positivity)
    _ = A^2*(N:ℝ)^10 := by field_simp
    _ ≤ _ := hsq

theorem exists_negative_reflected_comparison_diagonal {c : ℝ} (hc : 0 < c) :
    ∃ z ∈ thetaCuspStrip,
      (completeThetaSource.realization.kernel z z).re -
        c*‖thetaCuspStripSource z‖^2/(reflectedRate z).re < 0 := by
  let A := (12*Real.pi^2*Real.exp (-4*Real.pi))^2/2
  let D : ℝ := 24*486^2
  have hA : 0 < A := by dsimp [A]; positivity
  have hD : 0 < D := by norm_num [D]
  obtain ⟨N : ℕ, hN⟩ := exists_nat_gt (max 1 (D/(c*A)))
  have hNr : (1:ℝ) < N := (le_max_left _ _).trans_lt hN
  have hN0 : 0 < N := by exact_mod_cast (show (0:ℝ) < N by linarith only [hNr])
  have hN2 : D/(c*A) < (N:ℝ)^2 := by
    have h := (le_max_right 1 (D/(c*A))).trans_lt hN
    nlinarith only [h, hNr]
  have hgap : D < c*A*(N:ℝ)^2 := by
    have h := (div_lt_iff₀ (mul_pos hc hA)).mp hN2
    nlinarith only [h]
  let z := chargedPoint (1/(N:ℝ)^2)
  have hz : z ∈ thetaCuspStrip := chargedPoint_mem_strip (by positivity)
  have hk := chargedPoint_kernel_diagonal_upper N hN0
  have hh := chargedPoint_comparison_lower N hN0
  have hN10 : 0 < (N:ℝ)^10 := by positivity
  have hm := mul_lt_mul_of_pos_right hgap hN10
  have he : c*A*(N:ℝ)^2*(N:ℝ)^10 = c*(A*(N:ℝ)^12) := by ring
  rw [he] at hm
  have hle := mul_le_mul_of_nonneg_left hh hc.le
  refine ⟨z, hz, ?_⟩
  change (completeThetaSource.realization.kernel z z).re ≤ D*(N:ℝ)^10 at hk
  change c*(A*(N:ℝ)^12) ≤ c*(‖thetaCuspStripSource z‖^2/(reflectedRate z).re) at hle
  rw [mul_div_assoc]
  linarith only [hk, hm, hle]

end RHTower.ThetaCuspBoundaryAudit
