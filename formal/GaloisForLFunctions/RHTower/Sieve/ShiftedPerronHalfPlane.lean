import GaloisForLFunctions.RHTower.CCMGeneralizedVonKoch

/-!
# The shifted Perron formula right of a Xi frontier

For a complex point `s₀`, the twisted Chebyshev sum `Σ_{n ≤ N} Λ(n) n^{−s₀}` is the Perron integral
of `(−ζ'/ζ)(s₀ + w) x^w / w` over a vertical line `Re w = c > 1 − Re s₀` (`x = N + ½`).  Shifting
the contour to `Re w = σ₁ − Re s₀`, with `σ₁` right of every Xi zero, crosses two simple poles:

* `w = 0`, with residue `(−ζ'/ζ)(s₀)`;
* `w = 1 − s₀`, with residue `x^{1−s₀}/(1 − s₀)`.

This file proves the exact contour identity and the master inequality
(`norm_shiftedChebyshev_sub_le`):

`|Σ_{n≤N} Λ(n) n^{−s₀} − x^{1−s₀}/(1−s₀) + ζ'/ζ(s₀)| ≤ (truncation) + (|V_left| + |H_top| + |H_bottom|)/(2π)`.

The two poles are separated with a removable-singularity decomposition: the integrand equals
`dslope h 0 w + h(0)/w` with `h(w) = (−ζ'/ζ)(s₀ + w) x^w`, and `dslope h 0` has the single pole
`1 − s₀`.  No bound on `Im s₀` enters the identity, so after the line estimates the result is
uniform in the height of `s₀`.
-/

open Complex Filter Asymptotics Topology ArithmeticFunction

namespace RHTower.Sieve

noncomputable section

/-- The shifted Perron integrand `(−ζ'/ζ)(s₀ + w) · x^w / w`. -/
def shiftedPerronIntegrand (s₀ : ℂ) (x : ℝ) (w : ℂ) : ℂ :=
  (-deriv riemannZeta (s₀ + w) / riemannZeta (s₀ + w)) * ((x : ℂ) ^ w / w)

/-- The numerator `(−ζ'/ζ)(s₀ + w) · x^w`. -/
def shiftedPerronNumerator (s₀ : ℂ) (x : ℝ) (w : ℂ) : ℂ :=
  (-deriv riemannZeta (s₀ + w) / riemannZeta (s₀ + w)) * (x : ℂ) ^ w

/-- The Perron coefficients `Λ(n) n^{−s₀}`. -/
def shiftedVonMangoldt (s₀ : ℂ) (n : ℕ) : ℂ := ((Λ n : ℝ) : ℂ) * (n : ℂ) ^ (-s₀)

theorem shiftedVonMangoldt_zero (s₀ : ℂ) : shiftedVonMangoldt s₀ 0 = 0 := by
  simp [shiftedVonMangoldt]

theorem norm_shiftedVonMangoldt (s₀ : ℂ) (n : ℕ) :
    ‖shiftedVonMangoldt s₀ n‖ = (Λ n : ℝ) * (n : ℝ) ^ (-s₀.re) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [shiftedVonMangoldt]
  · rw [shiftedVonMangoldt, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg vonMangoldt_nonneg, Complex.norm_natCast_cpow_of_pos hn, Complex.neg_re]

/-- The shifted series is the logarithmic derivative at `s₀ + w`. -/
theorem tsum_shiftedVonMangoldt_cpow_neg {s₀ w : ℂ} (h : 1 < (s₀ + w).re) :
    ∑' n : ℕ, shiftedVonMangoldt s₀ n * (n : ℂ) ^ (-w) =
      -deriv riemannZeta (s₀ + w) / riemannZeta (s₀ + w) := by
  rw [← tsum_vonMangoldt_cpow_neg h]
  refine tsum_congr fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [shiftedVonMangoldt]
  · have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    rw [shiftedVonMangoldt, mul_assoc, ← Complex.cpow_add _ _ hn0, neg_add]

/-- Summability of the Perron weights for the shifted coefficients. -/
theorem summable_shiftedVonMangoldt_perron {s₀ : ℂ} {x σ : ℝ} (hx : 0 < x)
    (hσ : 1 < s₀.re + σ) :
    Summable (fun n : ℕ => ‖shiftedVonMangoldt s₀ n‖ * (x / n) ^ σ) := by
  have h := summable_vonMangoldt_perron (σ := s₀.re + σ) hx hσ
  have hxs : 0 < x ^ (-s₀.re) := Real.rpow_pos_of_pos hx _
  refine (h.mul_left (x ^ (-s₀.re))).congr fun n => ?_
  rw [norm_shiftedVonMangoldt, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg vonMangoldt_nonneg]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    rw [Real.div_rpow hx.le hn0.le, Real.div_rpow hx.le hn0.le, Real.rpow_add hx,
      Real.rpow_add hn0, Real.rpow_neg hn0.le, Real.rpow_neg hx.le]
    field_simp

/-- The truncated Perron integral is the normalised vertical integral of the shifted integrand. -/
theorem shiftedPerron_integral_eq_vIntegral' {s₀ : ℂ} {x σ T : ℝ} (hσ : 1 < s₀.re + σ) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t in (-T)..T,
        (∑' n : ℕ, shiftedVonMangoldt s₀ n * ((n : ℂ) ^ (-((σ : ℂ) + (t : ℝ) * I))))
          * ((x : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I) / ((σ : ℂ) + (t : ℝ) * I))
      = VIntegral' (shiftedPerronIntegrand s₀ x) σ (-T) T := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hpt : ∀ t : ℝ,
      (∑' n : ℕ, shiftedVonMangoldt s₀ n * ((n : ℂ) ^ (-((σ : ℂ) + (t : ℝ) * I))))
          * ((x : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I) / ((σ : ℂ) + (t : ℝ) * I))
        = shiftedPerronIntegrand s₀ x ((σ : ℂ) + (t : ℝ) * I) := by
    intro t
    rw [shiftedPerronIntegrand, tsum_shiftedVonMangoldt_cpow_neg]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero]
    linarith
  rw [intervalIntegral.integral_congr (g := fun t : ℝ =>
      shiftedPerronIntegrand s₀ x ((σ : ℂ) + (t : ℝ) * I)) (fun t _ => hpt t)]
  rw [VIntegral', VIntegral, smul_smul]
  have hcoef : (1 / (2 * (Real.pi : ℂ) * I)) * I = ((1 / (2 * Real.pi) : ℝ) : ℂ) := by
    have hIne : (I : ℂ) ≠ 0 := Complex.I_ne_zero
    have hpine : ((Real.pi : ℂ)) ≠ 0 := by simp [hpi.ne']
    push_cast
    field_simp
  rw [hcoef, smul_eq_mul]

/-! ## The two residues -/

section Residues

variable {alpha : ℝ} (halpha : 0 ≤ alpha) (hXi : XiZeroHalfPlaneBound alpha)
  {s₀ : ℂ} {x : ℝ} (hx : 0 < x) {σ₁ c T : ℝ}

include halpha hXi in
/-- The numerator is holomorphic wherever `Re (s₀ + w) > ½ + α` and `s₀ + w ≠ 1`. -/
theorem differentiableAt_shiftedPerronNumerator (hx : 0 < x) {w : ℂ}
    (hre : 1 / 2 + alpha < (s₀ + w).re) (hne : s₀ + w ≠ 1) :
    DifferentiableAt ℂ (shiftedPerronNumerator s₀ x) w := by
  have hzne : riemannZeta (s₀ + w) ≠ 0 := riemannZeta_ne_zero_of_xiZeroHalfPlaneBound halpha hXi hre
  have hxne : ((x : ℝ) : ℂ) ≠ 0 := by simpa using hx.ne'
  have hadd : DifferentiableAt ℂ (fun w : ℂ => s₀ + w) w := by fun_prop
  have hd1 : DifferentiableAt ℂ (fun w : ℂ => deriv riemannZeta (s₀ + w)) w :=
    (differentiableAt_deriv_riemannZeta hne).comp w hadd
  have hd2 : DifferentiableAt ℂ (fun w : ℂ => riemannZeta (s₀ + w)) w :=
    (differentiableAt_riemannZeta hne).comp w hadd
  exact ((hd1.neg.div hd2 hzne).mul (differentiableAt_id.const_cpow (Or.inl hxne)))

/-- A point strictly inside a rectangle is not on its border. -/
theorem not_mem_rectangleBorder_of_interior {z w p : ℂ} (hre1 : z.re < p.re) (hre2 : p.re < w.re)
    (him1 : z.im < p.im) (him2 : p.im < w.im) : p ∉ RectangleBorder z w := by
  intro hp
  simp only [RectangleBorder, Set.mem_union, Complex.mem_reProdIm, Set.mem_singleton_iff] at hp
  rcases hp with ((⟨-, h⟩ | ⟨h, -⟩) | ⟨-, h⟩) | ⟨h, -⟩ <;> linarith

/-- The Perron kernel `x^s/s` has a bounded difference quotient at any nonzero point. -/
theorem kernel_slope_isBigO {x : ℝ} (hx : 0 < x) {p : ℂ} (hp : p ≠ 0) :
    (fun s : ℂ => ((x : ℂ) ^ s / s - (x : ℂ) ^ p / p) / (s - p)) =O[𝓝[≠] p] (1 : ℂ → ℂ) := by
  have hxne : ((x : ℝ) : ℂ) ≠ 0 := by simpa using hx.ne'
  have hd : DifferentiableAt ℂ (fun s : ℂ => (x : ℂ) ^ s / s) p :=
    (differentiableAt_id.const_cpow (Or.inl hxne)).div differentiableAt_id hp
  have htend := hasDerivAt_iff_tendsto_slope.1 hd.hasDerivAt
  have heq : (fun s : ℂ => slope (fun s : ℂ => (x : ℂ) ^ s / s) p s)
      = fun s : ℂ => ((x : ℂ) ^ s / s - (x : ℂ) ^ p / p) / (s - p) := by
    funext s
    rw [slope_def_field]
  rw [← heq]
  exact htend.isBigO_one ℂ

/-- A function continuous at a point is bounded on its punctured neighbourhood. -/
theorem isBigO_one_of_continuousAt {f : ℂ → ℂ} {p : ℂ} (hf : ContinuousAt f p) :
    f =O[𝓝[≠] p] (1 : ℂ → ℂ) :=
  (hf.tendsto.mono_left nhdsWithin_le_nhds).isBigO_one ℂ

include halpha hXi in
/-- **The two residues.**  On the rectangle `[σ₁ − Re s₀, c] × [−T, T]` the normalised contour
integral of the shifted Perron integrand is `x^{1−s₀}/(1−s₀) + (−ζ'/ζ)(s₀)`. -/
theorem rectangleIntegral'_shiftedPerronIntegrand (hx : 0 < x)
    (hσ₁ : 1 / 2 + alpha < σ₁) (hσ₁1 : σ₁ < 1) (hs₀ : σ₁ < s₀.re) (hc0 : 0 < c)
    (hc1 : 1 < s₀.re + c) (hT : |s₀.im| < T) (hs₀1 : s₀ ≠ 1) :
    RectangleIntegral' (shiftedPerronIntegrand s₀ x)
        (((σ₁ - s₀.re : ℝ) : ℂ) - I * (T : ℂ)) ((c : ℂ) + I * (T : ℂ))
      = (x : ℂ) ^ (1 - s₀) / (1 - s₀) + shiftedPerronNumerator s₀ x 0 := by
  set z : ℂ := ((σ₁ - s₀.re : ℝ) : ℂ) - I * (T : ℂ) with hzdef
  set w : ℂ := (c : ℂ) + I * (T : ℂ) with hwdef
  have hzre : z.re = σ₁ - s₀.re := by rw [hzdef]; simp
  have hzim : z.im = -T := by rw [hzdef]; simp
  have hwre : w.re = c := by rw [hwdef]; simp
  have hwim : w.im = T := by rw [hwdef]; simp
  have hT0 : 0 < T := lt_of_le_of_lt (abs_nonneg _) hT
  have him1 : -T < -s₀.im := by have := neg_abs_le s₀.im; linarith [le_abs_self s₀.im]
  have him2 : -s₀.im < T := by have := neg_abs_le s₀.im; linarith
  set w₁ : ℂ := 1 - s₀ with hw₁def
  have hw₁re : w₁.re = 1 - s₀.re := by rw [hw₁def]; simp
  have hw₁im : w₁.im = -s₀.im := by rw [hw₁def]; simp
  have hw₁ne : w₁ ≠ 0 := by
    intro h; apply hs₀1; rw [hw₁def] at h; linear_combination -h
  have hzw_re : z.re ≤ w.re := by rw [hzre, hwre]; linarith
  have hzw_im : z.im ≤ w.im := by rw [hzim, hwim]; linarith
  -- interior points
  have hint : ∀ p : ℂ, z.re < p.re → p.re < w.re → z.im < p.im → p.im < w.im →
      Rectangle z w ∈ 𝓝 p := by
    intro p h1 h2 h3 h4
    rw [rectangle_mem_nhds_iff, Set.uIoo_of_le hzw_re, Set.uIoo_of_le hzw_im]
    exact ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
  have h0re1 : z.re < (0 : ℂ).re := by rw [hzre]; simp; linarith
  have h0re2 : (0 : ℂ).re < w.re := by rw [hwre]; simpa using hc0
  have h0im1 : z.im < (0 : ℂ).im := by rw [hzim]; simpa using hT0
  have h0im2 : (0 : ℂ).im < w.im := by rw [hwim]; simpa using hT0
  have hw₁re1 : z.re < w₁.re := by rw [hzre, hw₁re]; linarith
  have hw₁re2 : w₁.re < w.re := by rw [hw₁re, hwre]; linarith
  have hw₁im1 : z.im < w₁.im := by rw [hzim, hw₁im]; exact him1
  have hw₁im2 : w₁.im < w.im := by rw [hw₁im, hwim]; exact him2
  have h0nb : (0 : ℂ) ∉ RectangleBorder z w :=
    not_mem_rectangleBorder_of_interior h0re1 h0re2 h0im1 h0im2
  have hw₁nb : w₁ ∉ RectangleBorder z w :=
    not_mem_rectangleBorder_of_interior hw₁re1 hw₁re2 hw₁im1 hw₁im2
  -- the decomposition
  set h := shiftedPerronNumerator s₀ x with hhdef
  set G : ℂ → ℂ := dslope h 0 with hGdef
  set k : ℂ → ℂ := fun u => h 0 / u with hkdef
  have hFk : ∀ u : ℂ, u ≠ 0 → shiftedPerronIntegrand s₀ x u = G u + k u := by
    intro u hu
    rw [hGdef, dslope_of_ne _ hu, slope_def_field, hkdef]
    simp only [shiftedPerronIntegrand, hhdef, shiftedPerronNumerator, sub_zero]
    field_simp
    ring
  -- the numerator is holomorphic on the rectangle minus `w₁`
  have hhol : DifferentiableOn ℂ h (Rectangle z w \ {w₁}) := by
    intro u hu
    have hure : z.re ≤ u.re := by
      have := hu.1.1
      rw [Set.uIcc_of_le hzw_re] at this
      exact this.1
    have hre : 1 / 2 + alpha < (s₀ + u).re := by
      rw [Complex.add_re]; rw [hzre] at hure; linarith
    have hne : s₀ + u ≠ 1 := by
      intro h1; apply hu.2; rw [Set.mem_singleton_iff, hw₁def]; linear_combination h1
    exact (differentiableAt_shiftedPerronNumerator halpha hXi hx hre hne).differentiableWithinAt
  have hnhds0 : Rectangle z w \ {w₁} ∈ 𝓝 (0 : ℂ) := by
    rw [Set.sdiff_eq]
    exact Filter.inter_mem (hint 0 h0re1 h0re2 h0im1 h0im2)
      (isOpen_compl_singleton.mem_nhds (by simpa [eq_comm] using hw₁ne))
  have hGhol : DifferentiableOn ℂ G (Rectangle z w \ {w₁}) :=
    (Complex.differentiableOn_dslope hnhds0).mpr hhol
  have hkhol : DifferentiableOn ℂ k (Rectangle z w \ {0}) := by
    intro u hu
    have hu0 : u ≠ 0 := hu.2
    exact ((differentiableAt_const _).div differentiableAt_id hu0).differentiableWithinAt
  -- border integrability
  have hborder_sub : ∀ u ∈ RectangleBorder z w, u ∈ Rectangle z w \ {w₁} := by
    intro u hu
    refine ⟨rectangleBorder_subset_rectangle z w hu, ?_⟩
    rintro rfl; exact hw₁nb hu
  have hGcont : ContinuousOn G (RectangleBorder z w) :=
    hGhol.continuousOn.mono hborder_sub
  have hkcont : ContinuousOn k (RectangleBorder z w) := by
    intro u hu
    have hu0 : u ≠ 0 := by rintro rfl; exact h0nb hu
    exact (continuousAt_const.div continuousAt_id hu0).continuousWithinAt
  -- residue at `0`
  have hres0 : RectangleIntegral' k z w = h 0 := by
    refine ResidueTheoremOnRectangleWithSimplePole' hzw_re hzw_im
      (hint 0 h0re1 h0re2 h0im1 h0im2) hkhol ?_
    have hzero : (k - fun s => h 0 / (s - 0)) = 0 := by
      funext s; simp [hkdef]
    rw [hzero]
    exact Asymptotics.isBigO_zero _ _
  -- residue at `w₁`
  have hres1 : RectangleIntegral' G z w = (x : ℂ) ^ w₁ / w₁ := by
    refine ResidueTheoremOnRectangleWithSimplePole' hzw_re hzw_im
      (hint w₁ hw₁re1 hw₁re2 hw₁im1 hw₁im2) hGhol ?_
    -- the logarithmic derivative near its pole
    have hL : (fun s : ℂ => (-deriv riemannZeta (s₀ + s) / riemannZeta (s₀ + s)) -
        (s₀ + s - 1)⁻¹) =O[𝓝[≠] w₁] (1 : ℂ → ℂ) := by
      have hzeta := riemannZetaLogDerivResidueBigO
      have htend : Tendsto (fun s : ℂ => s₀ + s) (𝓝[≠] w₁) (𝓝[≠] (1 : ℂ)) := by
        refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
        · have : Tendsto (fun s : ℂ => s₀ + s) (𝓝 w₁) (𝓝 (s₀ + w₁)) :=
            (continuous_const.add continuous_id).tendsto w₁
          rw [show s₀ + w₁ = 1 by rw [hw₁def]; ring] at this
          exact this.mono_left nhdsWithin_le_nhds
        · filter_upwards [self_mem_nhdsWithin] with s hs
          intro h1; apply hs; rw [Set.mem_singleton_iff, hw₁def]
          rw [Set.mem_singleton_iff] at h1
          linear_combination h1
      have h2 := hzeta.comp_tendsto htend
      refine h2.congr' ?_ (Filter.EventuallyEq.refl _ _)
      filter_upwards with s
      simp [Pi.sub_apply, Pi.div_apply, Pi.neg_apply, Function.comp]
    have hK : (fun s : ℂ => (x : ℂ) ^ s / s) =O[𝓝[≠] w₁] (1 : ℂ → ℂ) := by
      have hxne : ((x : ℝ) : ℂ) ≠ 0 := by simpa using hx.ne'
      exact isBigO_one_of_continuousAt
        ((differentiableAt_id.const_cpow (Or.inl hxne)).div differentiableAt_id hw₁ne).continuousAt
    have hslope := kernel_slope_isBigO hx hw₁ne
    have hc0' : (fun s : ℂ => h 0 / s) =O[𝓝[≠] w₁] (1 : ℂ → ℂ) :=
      isBigO_one_of_continuousAt (continuousAt_const.div continuousAt_id hw₁ne)
    have hprod : (fun s : ℂ => ((-deriv riemannZeta (s₀ + s) / riemannZeta (s₀ + s)) -
        (s₀ + s - 1)⁻¹) * ((x : ℂ) ^ s / s)) =O[𝓝[≠] w₁] (1 : ℂ → ℂ) := by
      refine (hL.mul hK).trans ?_
      exact Asymptotics.isBigO_of_le _ fun s => by simp
    have hsum := (hprod.add hslope).sub hc0'
    refine hsum.congr' ?_ (Filter.EventuallyEq.refl _ _)
    have hev0 : ∀ᶠ s in 𝓝[≠] w₁, s ≠ 0 :=
      nhdsWithin_le_nhds (isOpen_compl_singleton.mem_nhds (by simpa using hw₁ne))
    filter_upwards [self_mem_nhdsWithin, hev0] with s hs hs0
    have hsw : s - w₁ ≠ 0 := sub_ne_zero.mpr hs
    have hsw' : s₀ + s - 1 = s - w₁ := by rw [hw₁def]; ring
    simp only [Pi.sub_apply]
    rw [hGdef, dslope_of_ne _ hs0, slope_def_field, hhdef]
    simp only [shiftedPerronNumerator, sub_zero, hsw']
    field_simp
    ring
  -- assemble
  rw [RectangleIntegral'_congr (g := G + k) (fun u hu => by
      have hu0 : u ≠ 0 := by rintro rfl; exact h0nb hu
      simp only [Pi.add_apply]; exact hFk u hu0)]
  rw [RectangleIntegral', RectangleBorderIntegrable.add hGcont.rectangleBorder_integrable
    hkcont.rectangleBorder_integrable, smul_add, ← RectangleIntegral', ← RectangleIntegral',
    hres1, hres0]

include halpha hXi in
/-- **Shifted Chebyshev master inequality.**  With `x = N + ½`, the twisted Chebyshev sum differs
from `x^{1−s₀}/(1−s₀) − ζ'/ζ(s₀)` by at most the Perron truncation error plus the three shifted
contour integrals. -/
theorem norm_shiftedChebyshev_sub_le {N : ℕ}
    (hσ₁ : 1 / 2 + alpha < σ₁) (hσ₁1 : σ₁ < 1) (hs₀ : σ₁ < s₀.re) (hc0 : 0 < c)
    (hc1 : 1 < s₀.re + c) (hT : |s₀.im| < T) (hs₀1 : s₀ ≠ 1) :
    ‖(∑ n ∈ Finset.Icc 1 N, shiftedVonMangoldt s₀ n)
        - ((((N : ℝ) + 1 / 2 : ℝ) : ℂ) ^ (1 - s₀) / (1 - s₀)
          + -deriv riemannZeta s₀ / riemannZeta s₀)‖
      ≤ (∑' n : ℕ, ‖shiftedVonMangoldt s₀ n‖ *
            ((((N : ℝ) + 1 / 2) / n) ^ c /
              (Real.pi * T * |Real.log (((N : ℝ) + 1 / 2) / n)|)))
        + (1 / (2 * Real.pi)) *
          (‖VIntegral (shiftedPerronIntegrand s₀ ((N : ℝ) + 1 / 2)) (σ₁ - s₀.re) (-T) T‖
            + ‖HIntegral (shiftedPerronIntegrand s₀ ((N : ℝ) + 1 / 2)) (σ₁ - s₀.re) c T‖
            + ‖HIntegral (shiftedPerronIntegrand s₀ ((N : ℝ) + 1 / 2)) (σ₁ - s₀.re) c (-T)‖) := by
  classical
  set x : ℝ := (N : ℝ) + 1 / 2 with hxdef
  have hx : (0 : ℝ) < x := by positivity
  have hT0 : 0 < T := lt_of_le_of_lt (abs_nonneg _) hT
  have hne : ∀ n : ℕ, (n : ℝ) ≠ x := by
    intro n hcon
    have h2 : (2 * n : ℤ) = 2 * (N : ℤ) + 1 := by
      have : (2 * (n : ℝ)) = 2 * (N : ℝ) + 1 := by rw [hcon, hxdef]; ring
      exact_mod_cast this
    omega
  have hconv := summable_shiftedVonMangoldt_perron (s₀ := s₀) (σ := c) hx hc1
  have hdef := summable_perron_error (c := shiftedVonMangoldt s₀) hx hc0 hT0 hconv
  have hperron := norm_tsum_lt_sub_perron_integral_le (c := shiftedVonMangoldt s₀)
    (shiftedVonMangoldt_zero s₀) hx hne hc0 hT0 hconv hdef
  have hind : ∑' n : ℕ, (if (n : ℝ) < x then shiftedVonMangoldt s₀ n else 0)
      = ∑ n ∈ Finset.Icc 1 N, shiftedVonMangoldt s₀ n := by
    have hsupp : ∀ n : ℕ, n ∉ Finset.Icc 1 N →
        (if (n : ℝ) < x then shiftedVonMangoldt s₀ n else 0) = 0 := by
      intro n hn
      rw [Finset.mem_Icc, not_and_or] at hn
      rcases hn with hn | hn
      · have : n = 0 := by omega
        subst this
        simp [shiftedVonMangoldt_zero]
      · refine if_neg ?_
        have : (N : ℝ) + 1 ≤ (n : ℝ) := by
          have : N + 1 ≤ n := by omega
          exact_mod_cast this
        rw [hxdef]; linarith
    rw [tsum_eq_sum hsupp]
    refine Finset.sum_congr rfl fun n hn => if_pos ?_
    have : n ≤ N := (Finset.mem_Icc.mp hn).2
    have : (n : ℝ) ≤ N := by exact_mod_cast this
    rw [hxdef]; linarith
  rw [hind, shiftedPerron_integral_eq_vIntegral' (x := x) (T := T) hc1] at hperron
  have hres := rectangleIntegral'_shiftedPerronIntegrand halpha hXi (s₀ := s₀) hx hσ₁ hσ₁1 hs₀
    hc0 hc1 hT hs₀1
  have hh0 : shiftedPerronNumerator s₀ x 0 = -deriv riemannZeta s₀ / riemannZeta s₀ := by
    simp [shiftedPerronNumerator]
  rw [hh0] at hres
  set f := shiftedPerronIntegrand s₀ x with hf
  have hshift := vIntegral_shift f (σ₁ - s₀.re) c T
  have hexp : VIntegral' f c (-T) T -
      ((x : ℂ) ^ (1 - s₀) / (1 - s₀) + -deriv riemannZeta s₀ / riemannZeta s₀) =
      (1 / (2 * (Real.pi : ℂ) * Complex.I)) •
        (VIntegral f (σ₁ - s₀.re) (-T) T + HIntegral f (σ₁ - s₀.re) c T -
          HIntegral f (σ₁ - s₀.re) c (-T)) := by
    rw [VIntegral', hshift, ← hres, RectangleIntegral', ← smul_sub]
    congr 1
    ring
  have hline : ‖VIntegral' f c (-T) T -
      ((x : ℂ) ^ (1 - s₀) / (1 - s₀) + -deriv riemannZeta s₀ / riemannZeta s₀)‖
      ≤ (1 / (2 * Real.pi)) * (‖VIntegral f (σ₁ - s₀.re) (-T) T‖ +
          ‖HIntegral f (σ₁ - s₀.re) c T‖ + ‖HIntegral f (σ₁ - s₀.re) c (-T)‖) := by
    rw [hexp, norm_smul, norm_two_pi_I_inv]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact le_trans (norm_sub_le _ _) (add_le_add (norm_add_le _ _) le_rfl)
  have htri := norm_sub_le_norm_sub_add_norm_sub
    (∑ n ∈ Finset.Icc 1 N, shiftedVonMangoldt s₀ n) (VIntegral' f c (-T) T)
    ((x : ℂ) ^ (1 - s₀) / (1 - s₀) + -deriv riemannZeta s₀ / riemannZeta s₀)
  linarith [htri, hperron, hline]

end Residues

end

end RHTower.Sieve
