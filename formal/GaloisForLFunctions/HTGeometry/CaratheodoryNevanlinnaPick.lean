/-
# The Carathéodory--Nevanlinna--Pick extension theorem on a half plane

Values prescribed at points of the open right half plane whose Carathéodory kernel
`(F x + conj (F y)) / (q x + conj (q y))` is positive semidefinite are interpolated by a single
holomorphic function of nonnegative real part on the whole half plane.

The Cayley transform carries the statement to the Schur class: the two kernels differ by the
congruence factor `(q x + 1) / (F x + 1)`, and the Nevanlinna--Pick theorem for the disc supplies
the interpolant.  The inverse Cayley transform is defined because a Schur function attaining the
value one at an interior point is constant.
-/
import GaloisForLFunctions.HTGeometry.SchurNevanlinnaPick

noncomputable section

open Filter Metric Topology
open scoped InnerProductSpace ComplexConjugate

namespace GaloisForLFunctions.HTGeometry

variable {X : Type*} {K : X → X → ℂ}

theorem IsPSDKernel.congr {K₁ K₂ : X → X → ℂ} (hK : IsPSDKernel K₁)
    (h : ∀ x y, K₁ x y = K₂ x y) : IsPSDKernel K₂ := by
  have : K₁ = K₂ := funext fun x => funext fun y => h x y
  exact this ▸ hK

/-- **Diagonal congruence.**  Multiplying a positive semidefinite kernel by `e x · conj (e y)`
preserves positivity. -/
theorem IsPSDKernel.mul_diag (hK : IsPSDKernel K) (e : X → ℂ) :
    IsPSDKernel (fun x y => e x * conj (e y) * K x y) := by
  classical
  refine ⟨?_, ?_⟩
  · intro x y
    simp only [map_mul, Complex.conj_conj, hK.conj_symm]
    ring
  · intro c
    have hsub : ∀ a : X, c a * e a ≠ 0 → a ∈ c.support := by
      intro a ha
      refine Finsupp.mem_support_iff.mpr (fun h0 => ha ?_)
      rw [h0, zero_mul]
    set c' : X →₀ ℂ := Finsupp.onFinset c.support (fun x => c x * e x) hsub with hc'
    have hc'apply : ∀ x, c' x = c x * e x := fun x => Finsupp.onFinset_apply
    have hval := hK.nonneg c'
    have hinner : ∀ (y : X) (a : ℂ),
        (c'.sum fun x b => conj a * b * K x y)
          = ∑ x ∈ c.support, conj a * (c x * e x) * K x y := by
      intro y a
      rw [Finsupp.sum_of_support_subset c' Finsupp.support_onFinset_subset _ (fun i _ => by simp)]
      exact Finset.sum_congr rfl (fun x _ => by rw [hc'apply])
    have hexpand : (c'.sum fun y a => c'.sum fun x b => conj a * b * K x y)
        = ∑ y ∈ c.support, ∑ x ∈ c.support,
            conj (c y * e y) * (c x * e x) * K x y := by
      rw [Finsupp.sum_of_support_subset c' Finsupp.support_onFinset_subset _ (fun i _ => by simp)]
      refine Finset.sum_congr rfl (fun y _ => ?_)
      rw [hinner y (c' y), hc'apply]
    rw [hexpand] at hval
    have htarget : (c.sum fun y a => c.sum fun x b => conj a * b * (e x * conj (e y) * K x y))
        = ∑ y ∈ c.support, ∑ x ∈ c.support,
            conj (c y * e y) * (c x * e x) * K x y := by
      rw [Finsupp.sum]
      refine Finset.sum_congr rfl (fun y _ => ?_)
      rw [Finsupp.sum]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      simp only [map_mul]
      ring
    rw [htarget]
    exact hval

/-- Scaling a positive semidefinite kernel by a nonnegative real preserves positivity. -/
theorem IsPSDKernel.const_mul (hK : IsPSDKernel K) {c : ℝ} (hc : 0 ≤ c) :
    IsPSDKernel (fun x y => (c : ℂ) * K x y) := by
  refine (hK.mul_diag (fun _ => ((Real.sqrt c : ℝ) : ℂ))).congr (fun x y => ?_)
  rw [Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt hc]

/-! ## The Cayley transform -/

/-- The Cayley transform of the right half plane onto the disc. -/
def cayleyRight (z : ℂ) : ℂ := (z - 1) / (z + 1)

theorem add_one_ne_zero_of_re_nonneg {z : ℂ} (hz : 0 ≤ z.re) : z + 1 ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at this
  linarith

theorem norm_cayleyRight_lt_one {z : ℂ} (hz : 0 < z.re) : ‖cayleyRight z‖ < 1 := by
  have hne : z + 1 ≠ 0 := add_one_ne_zero_of_re_nonneg hz.le
  rw [cayleyRight, norm_div, div_lt_one (by positivity)]
  have h1 : ‖z - 1‖ ^ 2 = Complex.normSq z - 2 * z.re + 1 := by
    rw [← Complex.normSq_eq_norm_sq]
    simp [Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
    ring
  have h2 : ‖z + 1‖ ^ 2 = Complex.normSq z + 2 * z.re + 1 := by
    rw [← Complex.normSq_eq_norm_sq]
    simp [Complex.normSq_apply, Complex.add_re, Complex.add_im]
    ring
  nlinarith [norm_nonneg (z - 1), norm_nonneg (z + 1), h1, h2]

theorem norm_cayleyRight_le_one {z : ℂ} (hz : 0 ≤ z.re) : ‖cayleyRight z‖ ≤ 1 := by
  have hne : z + 1 ≠ 0 := add_one_ne_zero_of_re_nonneg hz
  rw [cayleyRight, norm_div, div_le_one (by positivity)]
  have h1 : ‖z - 1‖ ^ 2 = Complex.normSq z - 2 * z.re + 1 := by
    rw [← Complex.normSq_eq_norm_sq]
    simp [Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
    ring
  have h2 : ‖z + 1‖ ^ 2 = Complex.normSq z + 2 * z.re + 1 := by
    rw [← Complex.normSq_eq_norm_sq]
    simp [Complex.normSq_apply, Complex.add_re, Complex.add_im]
    ring
  nlinarith [norm_nonneg (z - 1), norm_nonneg (z + 1), h1, h2]

theorem cayleyRight_ne_one {z : ℂ} (hz : 0 ≤ z.re) : cayleyRight z ≠ 1 := by
  intro h
  have hne : z + 1 ≠ 0 := add_one_ne_zero_of_re_nonneg hz
  rw [cayleyRight, div_eq_one_iff_eq hne] at h
  have : (2 : ℂ) = 0 := by linear_combination -h
  norm_num at this

theorem cayleyRight_inv {z : ℂ} (hz : 0 ≤ z.re) :
    (1 + cayleyRight z) / (1 - cayleyRight z) = z := by
  have hne : z + 1 ≠ 0 := add_one_ne_zero_of_re_nonneg hz
  have hd : (1 : ℂ) - cayleyRight z ≠ 0 := by
    intro h
    exact cayleyRight_ne_one hz (by linear_combination -h)
  rw [cayleyRight] at hd ⊢
  field_simp at hd ⊢
  ring

/-- The inverse Cayley transform has nonnegative real part on the closed disc. -/
theorem re_cayleyInv_nonneg {u : ℂ} (hu : ‖u‖ ≤ 1) (hne : u ≠ 1) :
    0 ≤ ((1 + u) / (1 - u)).re := by
  have hd : (1 : ℂ) - u ≠ 0 := fun h => hne (by linear_combination -h)
  have hden : (0 : ℝ) < Complex.normSq (1 - u) := Complex.normSq_pos.mpr hd
  have hsq : Complex.normSq u ≤ 1 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg u]
  rw [Complex.div_re]
  have hnum : (1 + u).re * (1 - u).re / Complex.normSq (1 - u)
      + (1 + u).im * (1 - u).im / Complex.normSq (1 - u)
      = (1 - Complex.normSq u) / Complex.normSq (1 - u) := by
    rw [← add_div]
    congr 1
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.sub_re,
      Complex.sub_im, Complex.one_re, Complex.one_im]
    ring
  rw [hnum]
  exact div_nonneg (by linarith) hden.le

/-! ## The half-plane extension theorem -/

/-- **Carathéodory--Nevanlinna--Pick on the right half plane.**  Interpolation data whose
Carathéodory kernel is positive semidefinite extends to a holomorphic function of nonnegative real
part on the whole open right half plane. -/
theorem exists_caratheodory_interpolant {X : Type*} [Nonempty X] (q F : X → ℂ)
    (hq : ∀ x, 0 < (q x).re)
    (hK : IsPSDKernel (fun x y => (F x + conj (F y)) / (q x + conj (q y)))) :
    ∃ Gf : ℂ → ℂ, DifferentiableOn ℂ Gf {z : ℂ | 0 < z.re} ∧
      (∀ z : ℂ, 0 < z.re → 0 ≤ (Gf z).re) ∧ (∀ x, Gf (q x) = F x) := by
  classical
  -- the diagonal forces nonnegative real parts
  have hFre : ∀ x, 0 ≤ (F x).re := by
    intro x
    have hval := hK.nonneg (Finsupp.single x 1)
    have hexp : ((Finsupp.single x (1 : ℂ)).sum fun y a =>
        (Finsupp.single x (1 : ℂ)).sum fun x' b =>
          conj a * b * ((F x' + conj (F y)) / (q x' + conj (q y))))
        = (F x + conj (F x)) / (q x + conj (q x)) := by
      simp [Finsupp.sum_single_index]
    rw [hexp] at hval
    rw [Complex.add_conj, Complex.add_conj, ← Complex.ofReal_div] at hval
    rw [Complex.ofReal_re] at hval
    have hqx := hq x
    have h2 : (0 : ℝ) < 2 * (q x).re := by linarith
    have h3 : 0 ≤ 2 * (F x).re := by
      by_contra hcon
      push Not at hcon
      have := div_neg_of_neg_of_pos hcon h2
      linarith
    linarith
  -- Cayley data
  set u : X → ℂ := fun x => cayleyRight (q x) with hudef
  set g : X → ℂ := fun x => cayleyRight (F x) with hgdef
  have hu : ∀ x, ‖u x‖ < 1 := fun x => norm_cayleyRight_lt_one (hq x)
  have hqne : ∀ x, q x + 1 ≠ 0 := fun x => add_one_ne_zero_of_re_nonneg (hq x).le
  have hFne : ∀ x, F x + 1 ≠ 0 := fun x => add_one_ne_zero_of_re_nonneg (hFre x)
  have hsum : ∀ x y, q x + conj (q y) ≠ 0 := by
    intro x y hzero
    have := congrArg Complex.re hzero
    simp only [Complex.add_re, Complex.conj_re, Complex.zero_re] at this
    have := hq x
    have := hq y
    linarith
  have hSchur : IsPSDKernel (fun x y => (1 - g x * conj (g y)) / (1 - u x * conj (u y))) := by
    refine (hK.mul_diag (fun x => (q x + 1) / (F x + 1))).congr (fun x y => ?_)
    have h1 : conj (q y) + 1 ≠ 0 := by
      simpa using (map_ne_zero (starRingEnd ℂ)).mpr (hqne y)
    have h2 : conj (F y) + 1 ≠ 0 := by
      simpa using (map_ne_zero (starRingEnd ℂ)).mpr (hFne y)
    simp only [hudef, hgdef, cayleyRight, map_div₀, map_sub, map_add, map_one]
    have hdq : (1 : ℂ) - (q x - 1) / (q x + 1) * ((conj (q y) - 1) / (conj (q y) + 1))
        = 2 * (q x + conj (q y)) / ((q x + 1) * (conj (q y) + 1)) := by
      have hqx := hqne x
      field_simp
      ring
    have hdF : (1 : ℂ) - (F x - 1) / (F x + 1) * ((conj (F y) - 1) / (conj (F y) + 1))
        = 2 * (F x + conj (F y)) / ((F x + 1) * (conj (F y) + 1)) := by
      have hFx := hFne x
      field_simp
      ring
    have hDne : 2 * (q x + conj (q y)) / ((q x + 1) * (conj (q y) + 1)) ≠ 0 :=
      div_ne_zero (mul_ne_zero two_ne_zero (hsum x y)) (mul_ne_zero (hqne x) h1)
    rw [hdq, hdF, eq_div_iff hDne]
    have hqx := hqne x
    have hFx := hFne x
    have hs := hsum x y
    field_simp
  obtain ⟨G, hGdiff, hGnorm, hGval⟩ := exists_schur_interpolant_of_pickKernel hu hSchur
  -- a Schur function attaining the value one is constant
  have hG1 : ∀ z : ℂ, ‖z‖ < 1 → G z ≠ 1 := by
    intro z hz hGz
    have hmem : z ∈ Metric.ball (0 : ℂ) 1 := by
      simpa [Metric.mem_ball, dist_zero_right] using hz
    have hmax : IsMaxOn (norm ∘ G) (Metric.ball (0 : ℂ) 1) z := by
      intro y hy
      have hy' : ‖y‖ < 1 := by
        simpa [Metric.mem_ball, dist_zero_right] using hy
      simp only [Function.comp_apply, hGz, norm_one]
      exact hGnorm y hy'
    have heq := Complex.eqOn_of_isPreconnected_of_isMaxOn_norm
      (isPreconnected_ball) isOpen_ball hGdiff hmem hmax
    obtain ⟨x⟩ := ‹Nonempty X›
    have hmemx : u x ∈ Metric.ball (0 : ℂ) 1 := by
      simpa [Metric.mem_ball, dist_zero_right] using hu x
    have : G (u x) = G z := heq hmemx
    rw [hGval x, hGz] at this
    exact cayleyRight_ne_one (hFre x) this
  refine ⟨fun z => (1 + G (cayleyRight z)) / (1 - G (cayleyRight z)), ?_, ?_, ?_⟩
  · intro z hz
    have hz' : (0 : ℝ) < z.re := hz
    have hne : z + 1 ≠ 0 := add_one_ne_zero_of_re_nonneg hz'.le
    have hcay : DifferentiableAt ℂ cayleyRight z := by
      show DifferentiableAt ℂ (fun w : ℂ => (w - 1) / (w + 1)) z
      exact (differentiableAt_id.sub_const 1).div (differentiableAt_id.add_const 1) hne
    have hball : cayleyRight z ∈ Metric.ball (0 : ℂ) 1 := by
      simpa [Metric.mem_ball, dist_zero_right] using norm_cayleyRight_lt_one hz'
    have hGat : DifferentiableAt ℂ G (cayleyRight z) :=
      hGdiff.differentiableAt (isOpen_ball.mem_nhds hball)
    have hcomp : DifferentiableAt ℂ (fun w => G (cayleyRight w)) z := hGat.comp z hcay
    have hd : (1 : ℂ) - G (cayleyRight z) ≠ 0 := by
      intro h
      exact hG1 (cayleyRight z) (norm_cayleyRight_lt_one hz') (by linear_combination -h)
    exact (((differentiableAt_const 1).add hcomp).div
      ((differentiableAt_const 1).sub hcomp) hd).differentiableWithinAt
  · intro z hz
    refine re_cayleyInv_nonneg (hGnorm _ (norm_cayleyRight_lt_one hz))
      (hG1 _ (norm_cayleyRight_lt_one hz))
  · intro x
    show (1 + G (cayleyRight (q x))) / (1 - G (cayleyRight (q x))) = F x
    have : cayleyRight (q x) = u x := rfl
    rw [this, hGval x]
    exact cayleyRight_inv (hFre x)

end GaloisForLFunctions.HTGeometry
