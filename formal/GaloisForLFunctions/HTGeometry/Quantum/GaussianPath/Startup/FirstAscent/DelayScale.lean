import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Real.Sqrt

/-! # Converting inverse-width changes into physical delays -/
open Real
namespace GaloisForLFunctions.HTGeometry.FirstAscent

/-- For a sufficiently sparse budget, a fixed prefactor inside the Gaussian
logarithm is absorbed by doubling its square root. -/
theorem sqrt_log_ratio {B N s : ℝ} (hB : 0<B) (hs : 0<s) (hN : 0<N)
    (hsize : s ≤ N) (hscale : B ≤ N/s) :
    sqrt (log (B*N/(42*s))) ≤ 2*sqrt (log (N/s)) := by
  have hq : 1 ≤ N/s := (one_le_div hs).mpr hsize
  have hl := log_nonneg hq
  have he : B*N/(42*s) ≤ (N/s)^2 := calc
    _ = (B*(N/s))/42 := by field_simp
    _ ≤ B*(N/s) := div_le_self (by positivity) (by norm_num)
    _ ≤ _ := (mul_le_mul_of_nonneg_right hscale (div_nonneg hN.le hs.le)).trans_eq (sq _).symm
  have hh := log_le_log (by positivity) he
  rw [log_pow] at hh
  apply sqrt_le_iff.mpr
  refine ⟨by positivity,?_⟩
  rw [mul_pow,sq_sqrt hl]
  linarith only [hh,hl]

/-- A square budget cutoff controls the relative Gaussian correction to
the clock, uniformly in the prefix size. -/
theorem budget_mass_bound {L N s : ℝ} (hL : 0 ≤ L) (hs : 0<s) (hN : 0<N)
    (hsN : s ≤ N) (hcut : L^2*s ≤ N) :
    L*(s/N)*sqrt (log (N/s)) ≤ 1 := by
  have hlog := log_nonneg ((one_le_div hs).mpr hsN)
  have hle : log (N/s) ≤ N/s := (log_le_sub_one_of_pos (div_pos hN hs)).trans (by linarith)
  apply (sq_le_sq₀ (by positivity) zero_le_one).mp
  rw [one_pow,mul_pow,sq_sqrt hlog]
  calc
    _ ≤ (L*(s/N))^2*(N/s) := mul_le_mul_of_nonneg_left hle (sq_nonneg _)
    _ = (L^2*s)/N := by field_simp
    _ ≤ _ := (div_le_one hN).mpr hcut

/-- On the initial semicircle an inverse-width loss of d delays a visit
by at most πd/(aN)², where W ≥ aN. -/
theorem delay_upper {u t d W a N : ℝ} (ha : 0<a) (hN : 0<N) (hW : a*N ≤ W)
    (hd : 0 ≤ d) (ht : t ≤ π/W) (hstop : t*(W-d) ≤ u) :
    t ≤ u/W+π*d/(a*N)^2 := by
  have hp := (mul_pos ha hN).trans_le hW
  have hl : t-u/W ≤ t*d/W := (le_div_iff₀ hp).mpr (by
    rw [sub_mul,div_mul_cancel₀ u hp.ne']
    linarith only [hstop])
  have hs : t*d/W ≤ π*d/(a*N)^2 := calc
    _ ≤ (π/W)*d/W := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right ht hd) hp.le
    _ = π*d/W^2 := by field_simp
    _ ≤ _ := div_le_div_of_nonneg_left (mul_nonneg pi_pos.le hd) (sq_pos_of_pos (mul_pos ha hN))
      ((sq_le_sq₀ (mul_pos ha hN).le hp.le).mpr hW)
  linarith only [hl,hs]

/-- Correcting width d makes every time through u/W+ud/(bN)² admissible
in the inverse clock, when W ≤ bN. -/
theorem delay_lower {u t d W b N : ℝ} (hu : 0 ≤ u) (ht : 0 ≤ t) (hd : 0 ≤ d)
    (hp : 0<W) (hW : W ≤ b*N) (hbefore : t ≤ u/W+u*d/(b*N)^2) :
    t*(W-d) ≤ u := by
  have hbN := hp.trans_le hW
  by_cases h : t ≤ u/W
  · linarith only [(le_div_iff₀ hp).mp h,mul_nonneg ht hd]
  have htim : u/(b*N) ≤ t := (div_le_div_of_nonneg_left hu hp hW).trans (le_of_not_ge h)
  have hdelta : t-u/W ≤ u*d/(b*N)^2 := by linarith only [hbefore]
  have hh : (t-u/W)*W ≤ t*d := calc
    _ ≤ (u*d/(b*N)^2)*W := mul_le_mul_of_nonneg_right hdelta hp.le
    _ ≤ (u*d/(b*N)^2)*(b*N) := mul_le_mul_of_nonneg_left hW (by positivity)
    _ = u/(b*N)*d := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_right htim hd
  rw [sub_mul,div_mul_cancel₀ u hp.ne'] at hh
  linarith only [hh]

end GaloisForLFunctions.HTGeometry.FirstAscent
