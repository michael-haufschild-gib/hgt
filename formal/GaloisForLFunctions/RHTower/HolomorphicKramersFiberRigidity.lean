import Mathlib.Analysis.Complex.OpenMapping

/-!
# Fixed-fiber Kramers symmetry is rigid in a holomorphic parameter

A standard two-dimensional antiunitary Kramers symmetry forces a matrix into quaternionic form

`[[a, b], [-conj b, conj a]]`.

If all four entries depend holomorphically on the same complex parameter, the conjugate partners
are holomorphic too. The open mapping theorem then makes `a` and `b` constant. Consequently the
whole family and its determinant are constant.

Thus a nonconstant holomorphic determinant cannot obtain off-real local multiplicity doubling from
a fixed antiunitary symmetry acting within every parameter fiber. The nonconstant alternative is
parameter-reversing covariance, relating `s` to `conj s`; that pairs distinct off-real fibers and
does not impose even analytic order at either point.
-/

open Complex Set

namespace RHTower

/-- If a holomorphic function and its pointwise complex conjugate are both holomorphic on a
connected open set, the function is constant there. -/
theorem holomorphic_conjugate_pair_constant
    {U : Set ℂ} {f g : ℂ → ℂ}
    (hUopen : IsOpen U) (hUconn : IsConnected U)
    (hf : AnalyticOnNhd ℂ f U) (hg : AnalyticOnNhd ℂ g U)
    (hpair : ∀ z ∈ U, g z = starRingEnd ℂ (f z)) :
    ∃ c : ℂ, ∀ z ∈ U, f z = c := by
  have hsum : AnalyticOnNhd ℂ (fun z => f z + g z) U := hf.add hg
  have him : ∀ z ∈ U, ((f z + g z).im : ℝ) = 0 := by
    intro z hz
    rw [hpair z hz]
    simp
  obtain ⟨C, hC⟩ := hsum.eq_const_of_im_eq_const him hUopen hUconn
  obtain ⟨z₀, hz₀⟩ := hUconn.nonempty
  have hre : ∀ z ∈ U, (f z).re = (f z₀).re := by
    intro z hz
    have hzC := congrArg Complex.re (hC z hz)
    have hz₀C := congrArg Complex.re (hC z₀ hz₀)
    rw [hpair z hz] at hzC
    rw [hpair z₀ hz₀] at hz₀C
    simp only [Complex.add_re, Complex.conj_re] at hzC hz₀C
    linarith
  exact hf.eq_const_of_re_eq_const hre hUopen hUconn

/-- A same-fiber holomorphic standard Kramers two-by-two family is constant. -/
theorem holomorphic_standardKramers_twoByTwo_constant
    {U : Set ℂ} {a b c d : ℂ → ℂ}
    (hUopen : IsOpen U) (hUconn : IsConnected U)
    (ha : AnalyticOnNhd ℂ a U) (hb : AnalyticOnNhd ℂ b U)
    (hc : AnalyticOnNhd ℂ c U) (hd : AnalyticOnNhd ℂ d U)
    (hdiag : ∀ z ∈ U, d z = starRingEnd ℂ (a z))
    (hoff : ∀ z ∈ U, c z = -starRingEnd ℂ (b z)) :
    ∃ a₀ b₀ : ℂ, ∀ z ∈ U,
      a z = a₀ ∧ b z = b₀ ∧ c z = -starRingEnd ℂ b₀ ∧ d z = starRingEnd ℂ a₀ := by
  obtain ⟨a₀, ha₀⟩ := holomorphic_conjugate_pair_constant hUopen hUconn ha hd hdiag
  have hnegc : AnalyticOnNhd ℂ (fun z => -c z) U := hc.neg
  have hpairb : ∀ z ∈ U, -c z = starRingEnd ℂ (b z) := by
    intro z hz
    rw [hoff z hz]
    simp
  obtain ⟨b₀, hb₀⟩ :=
    holomorphic_conjugate_pair_constant hUopen hUconn hb hnegc hpairb
  refine ⟨a₀, b₀, fun z hz => ⟨ha₀ z hz, hb₀ z hz, ?_, ?_⟩⟩
  · rw [hoff z hz, hb₀ z hz]
  · rw [hdiag z hz, ha₀ z hz]

/-- The determinant of a same-fiber holomorphic standard Kramers family is constant. -/
theorem holomorphic_standardKramers_twoByTwo_det_constant
    {U : Set ℂ} {a b c d : ℂ → ℂ}
    (hUopen : IsOpen U) (hUconn : IsConnected U)
    (ha : AnalyticOnNhd ℂ a U) (hb : AnalyticOnNhd ℂ b U)
    (hc : AnalyticOnNhd ℂ c U) (hd : AnalyticOnNhd ℂ d U)
    (hdiag : ∀ z ∈ U, d z = starRingEnd ℂ (a z))
    (hoff : ∀ z ∈ U, c z = -starRingEnd ℂ (b z)) :
    ∃ D : ℂ, ∀ z ∈ U, a z * d z - b z * c z = D := by
  obtain ⟨a₀, b₀, hconst⟩ := holomorphic_standardKramers_twoByTwo_constant
    hUopen hUconn ha hb hc hd hdiag hoff
  refine ⟨a₀ * starRingEnd ℂ a₀ + b₀ * starRingEnd ℂ b₀, fun z hz => ?_⟩
  obtain ⟨haeq, hbeq, hceq, hdeq⟩ := hconst z hz
  rw [haeq, hbeq, hceq, hdeq]
  ring

end RHTower
