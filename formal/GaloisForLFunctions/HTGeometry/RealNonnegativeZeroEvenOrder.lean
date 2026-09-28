import GaloisForLFunctions.HTGeometry.EntireZeroFactorization
import GaloisForLFunctions.HTGeometry.WeierstrassFactorizationEntire

/-!
# Even order at a nonnegative real zero

An entire function that is real on the real axis, not identically zero, and nonnegative on the
real axis near a real zero `x₀` vanishes there to even order `2k ≥ 2`; its cofactor is real and
positive at `x₀`.
-/

open Complex Filter Topology Set

namespace GaloisForLFunctions.HTGeometry

/-- **Even order at a real one-sided-free zero.** An entire function, real on the real axis,
not identically zero, and nonnegative on the real axis near a real zero `x₀`, vanishes there to
even order `2k ≥ 2`, with a cofactor that is real and positive at `x₀`. -/
theorem exists_even_order_factor_of_real_nonneg {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hreal : ∀ x : ℝ, (f x).im = 0) {x₀ : ℝ} (h0 : f x₀ = 0)
    (hnn : ∀ᶠ x : ℝ in 𝓝 x₀, 0 ≤ (f x).re) {z₁ : ℂ} (hz₁ : f z₁ ≠ 0) :
    ∃ k : ℕ, 1 ≤ k ∧ analyticOrderAt f x₀ = ((2 * k : ℕ) : ℕ∞) ∧
      ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ (g x₀).im = 0 ∧ 0 < (g x₀).re ∧
        ∀ z, f z = (z - x₀) ^ (2 * k) * g z := by
  have htop := GaloisForLFunctions.analyticOrderAt_ne_top_of_entire hf hz₁ (x₀ : ℂ)
  set d := (analyticOrderAt f x₀).toNat with hd
  have hord : analyticOrderAt f x₀ = (d : ℕ∞) := (ENat.coe_toNat htop).symm
  obtain ⟨g, hg, hg0, hfg⟩ := exists_entire_factor_of_analyticOrder hf hord
  have hd1 : d ≠ 0 := by
    intro h
    rw [h, Nat.cast_zero] at hord
    exact ((hf.analyticAt _).analyticOrderAt_eq_zero.mp hord) h0
  -- `g` is real on the real axis
  have hgreal : ∀ x : ℝ, (g x).im = 0 := by
    have hoff : ∀ x : ℝ, x ≠ x₀ → (g x).im = 0 := by
      intro x hx
      have hne : ((x : ℂ) - x₀) ^ d ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr (by exact_mod_cast hx))
      have hgx : g x = f x / ((x : ℂ) - x₀) ^ d := by rw [hfg x]; field_simp
      rw [hgx, show ((x : ℂ) - x₀) ^ d = (((x - x₀) ^ d : ℝ) : ℂ) by push_cast; ring,
        Complex.div_ofReal_im, hreal x, zero_div]
    intro x
    by_cases hx : x = x₀
    · subst hx
      have hc : Continuous fun t : ℝ => (g t).im :=
        Complex.continuous_im.comp (hg.continuous.comp Complex.continuous_ofReal)
      have hlim : Tendsto (fun t : ℝ => (g t).im) (𝓝[≠] x) (𝓝 (g x).im) :=
        (hc.tendsto x).mono_left nhdsWithin_le_nhds
      have hzero : Tendsto (fun t : ℝ => (g t).im) (𝓝[≠] x) (𝓝 0) :=
        tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun t ht => (hoff t ht).symm)
      exact tendsto_nhds_unique hlim hzero
    · exact hoff x hx
  set G : ℝ → ℝ := fun t => (g (x₀ + t : ℝ)).re
  have hGc : Continuous G :=
    Complex.continuous_re.comp (hg.continuous.comp (Complex.continuous_ofReal.comp
      (continuous_const.add continuous_id)))
  have hG0 : G 0 ≠ 0 := by
    simp only [G, add_zero]
    intro h
    exact hg0 (Complex.ext h (hgreal x₀))
  have hfG : ∀ t : ℝ, (f (x₀ + t : ℝ)).re = t ^ d * G t := by
    intro t
    have hgt : g (x₀ + t : ℝ) = ((G t : ℝ) : ℂ) := Complex.ext (by simp [G]) (by simpa using hgreal (x₀ + t))
    rw [hfg, hgt, show ((x₀ + t : ℝ) : ℂ) - x₀ = (t : ℂ) by push_cast; ring,
      ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]
  -- the sign of `G` is locally constant near `0`
  have hsign : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < G t * G 0 := by
    have : 0 < G 0 * G 0 := mul_self_pos.mpr hG0
    exact (hGc.mul continuous_const).continuousAt.eventually (lt_mem_nhds this)
  have hnn' : ∀ᶠ t in 𝓝 (0 : ℝ), 0 ≤ t ^ d * G t := by
    have h := (continuous_const.add continuous_id).continuousAt.tendsto.eventually
      (by simpa using hnn : ∀ᶠ x : ℝ in 𝓝 (x₀ + 0), 0 ≤ (f x).re)
    filter_upwards [h] with t ht
    rw [← hfG]; simpa using ht
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp (hsign.and hnn')
  -- a positive sample fixes the sign of `G 0`
  have hpos : 0 < G 0 := by
    obtain ⟨h1, h2⟩ := hball (y := ε / 2) (by rw [Real.dist_eq, sub_zero, abs_of_pos (by linarith)]; linarith)
    have hp : 0 < (ε / 2) ^ d := by positivity
    have hGt : 0 ≤ G (ε / 2) := by
      by_contra h; push Not at h; nlinarith [mul_neg_of_pos_of_neg hp h]
    rcases lt_or_gt_of_ne hG0 with h | h
    · nlinarith
    · exact h
  -- a negative sample forces an even order
  have heven : Even d := by
    by_contra hodd
    rw [Nat.not_even_iff_odd] at hodd
    obtain ⟨h1, h2⟩ := hball (y := -(ε / 2)) (by
      rw [Real.dist_eq, sub_zero, abs_neg, abs_of_pos (by linarith)]; linarith)
    have hGt : 0 < G (-(ε / 2)) := by
      by_contra h; push Not at h; nlinarith
    have hp : (-(ε / 2)) ^ d < 0 := hodd.pow_neg (by linarith)
    nlinarith
  obtain ⟨k, hk⟩ := heven
  refine ⟨k, by omega, by rw [hord, hk, two_mul], g, hg, hgreal x₀, ?_, ?_⟩
  · simpa [G] using hpos
  · intro z; rw [hfg z, hk, two_mul]

end GaloisForLFunctions.HTGeometry
