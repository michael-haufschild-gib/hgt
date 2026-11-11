import GaloisForLFunctions.RHTower.ZetaThinStripWeylBound
import Mathlib.Analysis.Complex.Liouville

/-!
# A Weyl bound for the linear Levinson detector

Cauchy's estimate on a fixed disk inside a thinner strip transfers the
zeta Weyl bound to its derivative. Both terms of the linear detector then
have exponent `3/16`, uniformly for bounded reciprocal-log coefficients.
-/

open Complex Metric Set
open RHTower

noncomputable section

namespace GaloisForLFunctions.MultiscaleMollifiedZetaField

/-- Zeta and its first derivative obey one global thin-strip Weyl estimate. -/
theorem exists_norm_zeta_and_deriv_thin_strip_le :
    ∃ r > 0, r < 1 / 2 ∧ ∃ C > 0, ∀ s : ℂ, |s.re - 1 / 2| ≤ r →
      ‖riemannZeta s‖ ≤ C * (1 + |s.im|) ^ (3 / 16 : ℝ) ∧
      ‖deriv riemannZeta s‖ ≤ C * (1 + |s.im|) ^ (3 / 16 : ℝ) := by
  obtain ⟨r, hr, hrhalf, C, hC, hzeta⟩ :=
    exists_global_norm_zeta_thin_strip_le_weyl (by norm_num : (0 : ℝ) < 1 / 48)
  have hp : (1 / 6 : ℝ) + 1 / 48 = 3 / 16 := by norm_num
  rw [hp] at hzeta
  let ρ : ℝ := r / 4
  let D : ℝ := C * (2 : ℝ) ^ (3 / 16 : ℝ) / ρ
  have hρ : 0 < ρ := by dsimp only [ρ]; positivity
  have hD : 0 < D := by dsimp only [D]; positivity
  refine ⟨r / 2, by positivity, by linarith only [hrhalf], C + D, by positivity, ?_⟩
  intro s hs
  have hstrip {z : ℂ} (hz : ‖z - s‖ ≤ r / 2) : |z.re - 1 / 2| ≤ r := by
    have hre : |z.re - s.re| ≤ r / 2 :=
      (by simpa only [Complex.sub_re] using Complex.abs_re_le_norm (z - s)).trans hz
    have he : z.re - 1 / 2 = (z.re - s.re) + (s.re - 1 / 2) := by ring
    rw [he]
    have hh := (abs_add_le (z.re - s.re) (s.re - 1 / 2)).trans (add_le_add hre hs)
    linarith only [hh]
  have hf : DifferentiableOn ℂ riemannZeta (ball s (r / 2)) := by
    intro z hz
    have hz' : ‖z - s‖ ≤ r / 2 := by simpa only [mem_ball, dist_eq_norm] using hz.le
    apply (differentiableAt_riemannZeta ?_).differentiableWithinAt
    intro he
    have hh := hstrip hz'
    rw [he] at hh
    norm_num at hh
    linarith only [hh, hrhalf]
  have hsub : closedBall s ρ ⊆ ball s (r / 2) := by
    intro z hz
    have hh : dist z s ≤ ρ := hz
    exact hh.trans_lt (by dsimp only [ρ]; linarith only [hr])
  have hbound : ∀ z ∈ sphere s ρ,
      ‖riemannZeta z‖ ≤ C * (2 : ℝ) ^ (3 / 16 : ℝ) * (1 + |s.im|) ^ (3 / 16 : ℝ) := by
    intro z hz
    have hn : ‖z - s‖ = ρ := by simpa only [mem_sphere, dist_eq_norm] using hz
    have hzstrip := hstrip (by rw [hn]; dsimp only [ρ]; linarith only [hr])
    have him : |z.im - s.im| ≤ ρ := by
      simpa only [Complex.sub_im, hn] using Complex.abs_im_le_norm (z - s)
    have hzheight : 1 + |z.im| ≤ 2 * (1 + |s.im|) := by
      have hh := abs_add_le (z.im - s.im) s.im
      rw [sub_add_cancel] at hh
      have hρ1 : ρ ≤ 1 := by dsimp only [ρ]; linarith only [hrhalf]
      linarith only [hh, him, hρ1, abs_nonneg s.im]
    calc
      _ ≤ C * (1 + |z.im|) ^ (3 / 16 : ℝ) := hzeta z hzstrip
      _ ≤ C * (2 * (1 + |s.im|)) ^ (3 / 16 : ℝ) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hzheight (by norm_num)) hC.le
      _ = _ := by rw [Real.mul_rpow (by norm_num) (by positivity)]; ring
  have hderiv := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le 1 hρ
    (hf.diffContOnCl_ball hsub) hbound
  have hderiv' : ‖deriv riemannZeta s‖ ≤ D * (1 + |s.im|) ^ (3 / 16 : ℝ) := by
    simpa only [iteratedDeriv_one, Nat.factorial_one, Nat.cast_one, one_mul, pow_one,
      D, div_mul_eq_mul_div] using hderiv
  have hheight : 0 ≤ (1 + |s.im|) ^ (3 / 16 : ℝ) := Real.rpow_nonneg (by positivity) _
  constructor
  · exact (hzeta s (hs.trans (by linarith only [hr]))).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hD.le) hheight)
  · exact hderiv'.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hC.le) hheight)

/-- The actual linear detector has the same thin-strip Weyl exponent. -/
theorem exists_norm_linearDetector_thin_strip_le :
    ∃ r > 0, r < 1 / 2 ∧ ∃ C > 0, ∀ s : ℂ, |s.re - 1 / 2| ≤ r →
      ∀ lam : ℝ, |lam| ≤ 1 →
        ‖riemannZeta s + (lam : ℂ) * deriv riemannZeta s‖ ≤ C * (1 + |s.im|) ^ (3 / 16 : ℝ) := by
  obtain ⟨r, hr, hrhalf, C, hC, hbound⟩ := exists_norm_zeta_and_deriv_thin_strip_le
  refine ⟨r, hr, hrhalf, 2 * C, by positivity, ?_⟩
  intro s hs lam hlam
  obtain ⟨hz, hd⟩ := hbound s hs
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hh : |lam| * ‖deriv riemannZeta s‖ ≤ C * (1 + |s.im|) ^ (3 / 16 : ℝ) :=
    (mul_le_mul_of_nonneg_right hlam (norm_nonneg _)).trans (by simpa only [one_mul] using hd)
  linarith only [hz, hh]

end GaloisForLFunctions.MultiscaleMollifiedZetaField
