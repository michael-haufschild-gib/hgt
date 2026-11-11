import Mathlib

/-!
# Linear statistics are not monotone under projection to the line

A linear statistic of a zero configuration is `Σ_ρ F(ξ_ρ)`, `ξ_ρ = (ρ − ½)/i`, with `F` entire:
these are the functionals an explicit formula evaluates on the prime side. A reflection pair
`{ρ, 1 − ρ̄}` of depth `δ` and ordinate `ξ` has the spectral points `ξ ∓ iδ`; its projection to the
line is the double point `ξ`. The **split increment** is the change of the statistic when the
double point splits into the pair.

* `re_deriv2_nonpos_of_splitIncrement_nonneg`: if splitting does not decrease the statistic at
  an ordinate for all small depths, then `Re F''(ξ) ≤ 0` (second derivative test for the pair
  sum on the vertical line through `ξ`).
* `eventually_splitIncrement_pos_of_re_deriv2_neg`: conversely `Re F''(ξ) < 0` makes splitting
  increase the statistic at every small depth; the sign of the curvature decides.
* `concaveOn_re_of_splitIncrement_nonneg`: monotonicity at every ordinate makes `ξ ↦ Re F(ξ)`
  concave on the line.
* `eq_const_of_concaveOn_of_bddBelow`: a concave function on `ℝ` that is bounded below is constant.
* `re_eq_zero_of_splitIncrement_nonneg`, `re_eq_zero_of_splitIncrement_nonpos`: a symbol whose
  real part tends to zero along the line and which is monotone under splitting, in either
  direction, has zero real part on the line. Convergent linear statistics are therefore never
  monotone under projection: at some ordinate projection increases them, at another it
  decreases them, at arbitrarily small depth.
* `heatSymbol_splitIncrement_sign`: the heat statistic `Σ_ρ e^{−tξ_ρ²}` is lowered by projection
  exactly at the ordinates below the height `(2t)^{−1/2}`: a floor in the height, none in the
  depth.
* `splitIncrement_fourierSymbol`: for the symbol `∫ g(u) e^{iξu} du` the split increment is
  `∫ g(u) · 2 cos(ξu) (cosh(δu) − 1) du`: projection adds this smooth density to the prime side.
-/

open Complex Filter Topology Set MeasureTheory

noncomputable section

namespace GaloisForLFunctions.FloorFreeArithmetic

/-- The change of the linear statistic with symbol `F` when the double point `ξ` of the line
splits into the reflection pair `ξ ± iδ`. -/
def splitIncrement (F : ℂ → ℂ) (ξ δ : ℝ) : ℝ :=
  (F (ξ + δ * I)).re + (F (ξ + δ * -I)).re - 2 * (F ξ).re

theorem splitIncrement_neg_symbol (F : ℂ → ℂ) (ξ δ : ℝ) :
    splitIncrement (fun w => -F w) ξ δ = -splitIncrement F ξ δ := by
  simp only [splitIncrement, Complex.neg_re]
  ring

/-! ### Derivatives along lines -/

/-- The derivative of an entire function along the complex line `w ↦ a + w c`. -/
theorem hasDerivAt_line {F : ℂ → ℂ} (hF : Differentiable ℂ F) (a c w : ℂ) :
    HasDerivAt (fun w : ℂ => F (a + w * c)) (deriv F (a + w * c) * c) w := by
  have hinner : HasDerivAt (fun w : ℂ => a + w * c) c w := by
    simpa using ((hasDerivAt_id w).mul_const c).const_add a
  exact (hF (a + w * c)).hasDerivAt.comp w hinner

/-- The derivative of an entire function is entire. -/
theorem differentiable_deriv_of_entire {F : ℂ → ℂ} (hF : Differentiable ℂ F) :
    Differentiable ℂ (deriv F) :=
  differentiableOn_univ.mp ((differentiableOn_univ.mpr hF).deriv isOpen_univ)

/-- First derivative of `t ↦ Re F(a + t c)` on the real line. -/
theorem hasDerivAt_re_line {F : ℂ → ℂ} (hF : Differentiable ℂ F) (a c : ℂ) (t : ℝ) :
    HasDerivAt (fun t : ℝ => (F (a + t * c)).re) (deriv F (a + t * c) * c).re t :=
  (hasDerivAt_line hF a c t).real_of_complex

/-- Second derivative of `t ↦ Re F(a + t c)` on the real line. -/
theorem hasDerivAt_re_line_deriv {F : ℂ → ℂ} (hF : Differentiable ℂ F) (a c : ℂ) (t : ℝ) :
    HasDerivAt (fun t : ℝ => (deriv F (a + t * c) * c).re)
      (deriv (deriv F) (a + t * c) * c * c).re t := by
  have h := (hasDerivAt_line (differentiable_deriv_of_entire hF) a c t).mul_const c
  exact h.real_of_complex

/-- The derivative of the quadratic tilt `δ ↦ (c/2) δ²`. -/
theorem hasDerivAt_half_mul_sq (c δ : ℝ) :
    HasDerivAt (fun δ : ℝ => c / 2 * δ ^ 2) (c * δ) δ := by
  have h := ((hasDerivAt_id' δ).mul (hasDerivAt_id' δ)).const_mul (c / 2)
  have hfun : (fun δ : ℝ => c / 2 * δ ^ 2) = fun y : ℝ => c / 2 * (y * y) := by
    funext y
    ring
  rw [hfun]
  exact h.congr_deriv (by ring)

/-! ### The second-order law -/

/-- The pair sum on the vertical line through `ξ`, tilted by `(a/2) δ²`, and its derivative. -/
theorem hasDerivAt_tiltedPairSum {F : ℂ → ℂ} (hF : Differentiable ℂ F) (ξ a δ : ℝ) :
    HasDerivAt (fun δ : ℝ => (F (ξ + δ * I)).re + (F (ξ + δ * -I)).re + a / 2 * δ ^ 2)
      ((deriv F (ξ + δ * I) * I).re + (deriv F (ξ + δ * -I) * -I).re + a * δ) δ :=
  ((hasDerivAt_re_line hF ξ I δ).add (hasDerivAt_re_line hF ξ (-I) δ)).add
    (hasDerivAt_half_mul_sq a δ)

/-- The second derivative of the tilted pair sum at depth zero is `a − 2 Re F''(ξ)`. -/
theorem hasDerivAt_tiltedPairSum_deriv {F : ℂ → ℂ} (hF : Differentiable ℂ F) (ξ a : ℝ) :
    HasDerivAt (fun δ : ℝ => (deriv F (ξ + δ * I) * I).re + (deriv F (ξ + δ * -I) * -I).re +
      a * δ) (a - 2 * (deriv (deriv F) ξ).re) 0 := by
  have h := ((hasDerivAt_re_line_deriv hF ξ I 0).add
    (hasDerivAt_re_line_deriv hF ξ (-I) 0)).add ((hasDerivAt_id' (0 : ℝ)).const_mul a)
  refine h.congr_deriv ?_
  have e1 : (ξ : ℂ) + ((0 : ℝ) : ℂ) * I = ξ := by simp
  have e2 : (ξ : ℂ) + ((0 : ℝ) : ℂ) * -I = ξ := by simp
  have e3 : deriv (deriv F) ξ * I * I = -deriv (deriv F) ξ := by
    rw [mul_assoc, Complex.I_mul_I, mul_neg_one]
  have e4 : deriv (deriv F) ξ * -I * -I = -deriv (deriv F) ξ := by
    rw [mul_assoc, neg_mul_neg, Complex.I_mul_I, mul_neg_one]
  rw [e1, e2, e3, e4, Complex.neg_re]
  ring

/-- The tilted pair sum has a critical point at depth zero. -/
theorem tiltedPairSum_deriv_zero (F : ℂ → ℂ) (ξ a : ℝ) :
    (deriv F (ξ + ((0 : ℝ) : ℂ) * I) * I).re + (deriv F (ξ + ((0 : ℝ) : ℂ) * -I) * -I).re +
      a * 0 = 0 := by
  simp

/-- **Second-order law.** If splitting the double point `ξ` does not decrease the statistic
for all small depths, then `Re F''(ξ) ≤ 0`. -/
theorem re_deriv2_nonpos_of_splitIncrement_nonneg {F : ℂ → ℂ} (hF : Differentiable ℂ F) {ξ : ℝ}
    (h : ∀ᶠ δ : ℝ in 𝓝[>] 0, 0 ≤ splitIncrement F ξ δ) : (deriv (deriv F) ξ).re ≤ 0 := by
  by_contra hcon
  have hc : 0 < (deriv (deriv F) ξ).re := lt_of_not_ge hcon
  set c : ℝ := (deriv (deriv F) ξ).re with hcdef
  -- the pair sum, tilted by half of the forbidden curvature, has a local maximum at zero
  set k : ℝ → ℝ := fun δ => (F (ξ + δ * I)).re + (F (ξ + δ * -I)).re + c / 2 * δ ^ 2 with hk
  have hderiv : deriv k = fun δ : ℝ => (deriv F (ξ + δ * I) * I).re +
      (deriv F (ξ + δ * -I) * -I).re + c * δ :=
    funext fun δ => (hasDerivAt_tiltedPairSum hF ξ c δ).deriv
  have hloc : IsLocalMax k 0 :=
    isLocalMax_of_deriv_deriv_neg
      (by rw [hderiv, (hasDerivAt_tiltedPairSum_deriv hF ξ c).deriv]; linarith only [hc])
      (by rw [hderiv]; exact tiltedPairSum_deriv_zero F ξ c)
      (hasDerivAt_tiltedPairSum hF ξ c 0).continuousAt
  have hev : ∀ᶠ δ : ℝ in 𝓝[>] 0, k δ ≤ k 0 ∧ 0 ≤ splitIncrement F ξ δ ∧ 0 < δ :=
    (hloc.filter_mono nhdsWithin_le_nhds).and (h.and self_mem_nhdsWithin)
  obtain ⟨δ, hle, hinc, hδ⟩ := hev.exists
  have hk0 : k 0 = 2 * (F ξ).re := by
    simp only [hk, Complex.ofReal_zero, zero_mul, add_zero]
    ring
  have hkδ : k δ = splitIncrement F ξ δ + 2 * (F ξ).re + c / 2 * δ ^ 2 := by
    simp only [hk, splitIncrement]
    ring
  have hpos : 0 < c / 2 * δ ^ 2 := by positivity
  linarith only [hle, hinc, hk0, hkδ, hpos]

/-- **Converse second-order law.** If `Re F''(ξ) < 0`, splitting the double point `ξ` increases
the statistic at every small nonzero depth: projection to the line decreases it there. -/
theorem eventually_splitIncrement_pos_of_re_deriv2_neg {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    {ξ : ℝ} (h : (deriv (deriv F) ξ).re < 0) :
    ∀ᶠ δ : ℝ in 𝓝[≠] 0, 0 < splitIncrement F ξ δ := by
  set c : ℝ := (deriv (deriv F) ξ).re with hcdef
  -- the pair sum, tilted by half of the curvature, has a local minimum at zero
  set k : ℝ → ℝ := fun δ => (F (ξ + δ * I)).re + (F (ξ + δ * -I)).re + c / 2 * δ ^ 2 with hk
  have hderiv : deriv k = fun δ : ℝ => (deriv F (ξ + δ * I) * I).re +
      (deriv F (ξ + δ * -I) * -I).re + c * δ :=
    funext fun δ => (hasDerivAt_tiltedPairSum hF ξ c δ).deriv
  have hloc : IsLocalMin k 0 :=
    isLocalMin_of_deriv_deriv_pos
      (by rw [hderiv, (hasDerivAt_tiltedPairSum_deriv hF ξ c).deriv]; linarith only [h])
      (by rw [hderiv]; exact tiltedPairSum_deriv_zero F ξ c)
      (hasDerivAt_tiltedPairSum hF ξ c 0).continuousAt
  have hk0 : k 0 = 2 * (F ξ).re := by
    simp only [hk, Complex.ofReal_zero, zero_mul, add_zero]
    ring
  filter_upwards [hloc.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with δ hle hδ
  have hkδ : k δ = splitIncrement F ξ δ + 2 * (F ξ).re + c / 2 * δ ^ 2 := by
    simp only [hk, splitIncrement]
    ring
  have hδ2 : 0 < δ ^ 2 := sq_pos_iff.mpr (Set.mem_compl_singleton_iff.mp hδ)
  have hneg : c / 2 * δ ^ 2 < 0 := by nlinarith only [h, hδ2]
  linarith only [hle, hk0, hkδ, hneg]

/-- If `Re F''(ξ) > 0`, splitting the double point `ξ` decreases the statistic at every small
nonzero depth. -/
theorem eventually_splitIncrement_neg_of_re_deriv2_pos {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    {ξ : ℝ} (h : 0 < (deriv (deriv F) ξ).re) :
    ∀ᶠ δ : ℝ in 𝓝[≠] 0, splitIncrement F ξ δ < 0 := by
  have hneg : (deriv (deriv fun w => -F w) ξ).re < 0 := by
    have h1 : deriv (fun w => -F w) = fun w => -deriv F w := funext fun w => deriv.neg
    have h2 : deriv (fun w => -deriv F w) ξ = -deriv (deriv F) ξ := deriv.neg
    rw [h1, h2, Complex.neg_re]
    linarith only [h]
  filter_upwards [eventually_splitIncrement_pos_of_re_deriv2_neg (F := fun w => -F w) hF.neg
    hneg] with δ hδ
  rw [splitIncrement_neg_symbol] at hδ
  linarith only [hδ]

/-- **Monotone statistics have concave symbols.** If at every ordinate splitting does not
decrease the statistic for all small depths, then `ξ ↦ Re F(ξ)` is concave on the line. -/
theorem concaveOn_re_of_splitIncrement_nonneg {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    (h : ∀ ξ : ℝ, ∀ᶠ δ : ℝ in 𝓝[>] 0, 0 ≤ splitIncrement F ξ δ) :
    ConcaveOn ℝ univ (fun ξ : ℝ => (F ξ).re) := by
  have h1 : ∀ x : ℝ, HasDerivAt (fun ξ : ℝ => (F ξ).re) (deriv F x).re x := fun x =>
    (hF x).hasDerivAt.real_of_complex
  have h2 : ∀ x : ℝ, HasDerivAt (fun ξ : ℝ => (deriv F ξ).re) (deriv (deriv F) x).re x :=
    fun x => ((differentiable_deriv_of_entire hF) x).hasDerivAt.real_of_complex
  have hd1 : deriv (fun ξ : ℝ => (F ξ).re) = fun ξ : ℝ => (deriv F ξ).re :=
    funext fun x => (h1 x).deriv
  refine concaveOn_univ_of_deriv2_nonpos (fun x => (h1 x).differentiableAt) ?_ ?_
  · rw [hd1]
    exact fun x => (h2 x).differentiableAt
  · intro x
    rw [Function.iterate_succ, Function.iterate_one, Function.comp_apply, hd1, (h2 x).deriv]
    exact re_deriv2_nonpos_of_splitIncrement_nonneg hF (h x)

/-! ### Concave functions on the line -/

/-- A concave function on `ℝ` that is bounded below is constant. -/
theorem eq_const_of_concaveOn_of_bddBelow {f : ℝ → ℝ} (hf : ConcaveOn ℝ univ f) {m : ℝ}
    (hm : ∀ x, m ≤ f x) (x y : ℝ) : f x = f y := by
  -- it suffices to exclude an increase and a decrease between two ordered points
  have key : ∀ a b : ℝ, a < b → f a = f b := by
    intro a b hab
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · -- positive slope: the function falls below `m` far to the left
      set s : ℝ := (f b - f a) / (b - a) with hs
      have hs0 : 0 < s := div_pos (sub_pos.mpr hlt) (sub_pos.mpr hab)
      set t : ℝ := a - (f a - m + 1) / s with ht
      have hpos : 0 < (f a - m + 1) / s := div_pos (by linarith only [hm a]) hs0
      have hta : t < a := by linarith only [hpos, ht]
      have hslope := hf.slope_anti_adjacent (mem_univ t) (mem_univ b) hta hab
      rw [← hs] at hslope
      have h1 := (le_div_iff₀ (sub_pos.mpr hta)).mp hslope
      have h2 : s * (a - t) = f a - m + 1 := by
        rw [ht, sub_sub_cancel, mul_div_cancel₀ _ hs0.ne']
      linarith only [h1, h2, hm t]
    · -- negative slope: the function falls below `m` far to the right
      set s : ℝ := (f a - f b) / (b - a) with hs
      have hs0 : 0 < s := div_pos (sub_pos.mpr hgt) (sub_pos.mpr hab)
      set t : ℝ := b + (f b - m + 1) / s with ht
      have hpos : 0 < (f b - m + 1) / s := div_pos (by linarith only [hm b]) hs0
      have hbt : b < t := by linarith only [hpos, ht]
      have hslope := hf.slope_anti_adjacent (mem_univ a) (mem_univ t) hab hbt
      have hneg : (f b - f a) / (b - a) = -s := by rw [hs, ← neg_div, neg_sub]
      rw [hneg] at hslope
      have h1 := (div_le_iff₀ (sub_pos.mpr hbt)).mp hslope
      have h2 : s * (t - b) = f b - m + 1 := by
        rw [ht, add_sub_cancel_left, mul_div_cancel₀ _ hs0.ne']
      linarith only [h1, h2, hm t]
  rcases lt_trichotomy x y with h | h | h
  · exact key x y h
  · rw [h]
  · exact (key y x h).symm

/-- A concave function on `ℝ` that tends to zero at `+∞` and is bounded below vanishes. -/
theorem eq_zero_of_concaveOn_of_tendsto {f : ℝ → ℝ} (hf : ConcaveOn ℝ univ f) {m : ℝ}
    (hm : ∀ x, m ≤ f x) (hlim : Tendsto f atTop (𝓝 0)) (x : ℝ) : f x = 0 := by
  have hconst : f = fun _ => f x := funext fun y => eq_const_of_concaveOn_of_bddBelow hf hm y x
  rw [hconst] at hlim
  exact tendsto_nhds_unique tendsto_const_nhds hlim

/-! ### No convergent linear statistic is monotone -/

/-- **No statistic that increases under splitting.** An entire symbol whose real part is
bounded below on the line and tends to zero at `+∞`, and which never decreases when a double
point of the line splits at small depth, has zero real part on the line. -/
theorem re_eq_zero_of_splitIncrement_nonneg {F : ℂ → ℂ} (hF : Differentiable ℂ F) {m : ℝ}
    (hm : ∀ x : ℝ, m ≤ (F x).re) (hlim : Tendsto (fun x : ℝ => (F x).re) atTop (𝓝 0))
    (h : ∀ ξ : ℝ, ∀ᶠ δ : ℝ in 𝓝[>] 0, 0 ≤ splitIncrement F ξ δ) (x : ℝ) : (F x).re = 0 :=
  eq_zero_of_concaveOn_of_tendsto (concaveOn_re_of_splitIncrement_nonneg hF h) hm hlim x

/-- **No statistic that decreases under splitting.** The same with the opposite sign: an
entire symbol whose real part is bounded above on the line, tends to zero at `+∞`, and never
increases under splitting at small depth, has zero real part on the line. -/
theorem re_eq_zero_of_splitIncrement_nonpos {F : ℂ → ℂ} (hF : Differentiable ℂ F) {m : ℝ}
    (hm : ∀ x : ℝ, (F x).re ≤ m) (hlim : Tendsto (fun x : ℝ => (F x).re) atTop (𝓝 0))
    (h : ∀ ξ : ℝ, ∀ᶠ δ : ℝ in 𝓝[>] 0, splitIncrement F ξ δ ≤ 0) (x : ℝ) : (F x).re = 0 := by
  have hneg := re_eq_zero_of_splitIncrement_nonneg (F := fun w => -F w) hF.neg (m := -m)
    (fun x => by simpa using hm x) (by simpa using hlim.neg)
    (fun ξ => (h ξ).mono fun δ hδ => by
      rw [splitIncrement_neg_symbol]
      linarith only [hδ]) x
  simpa using hneg

/-- **Both signs occur.** A symbol with bounded real part on the line, tending to zero at `+∞`
and not identically zero there, has an ordinate at which splitting decreases the statistic at
arbitrarily small depth, and an ordinate at which it increases it. -/
theorem exists_splitIncrement_neg_and_pos {F : ℂ → ℂ} (hF : Differentiable ℂ F) {m : ℝ}
    (hm : ∀ x : ℝ, |(F x).re| ≤ m) (hlim : Tendsto (fun x : ℝ => (F x).re) atTop (𝓝 0))
    {x₀ : ℝ} (hx₀ : (F x₀).re ≠ 0) :
    (∃ ξ : ℝ, ∃ᶠ δ : ℝ in 𝓝[>] 0, splitIncrement F ξ δ < 0) ∧
      ∃ ξ : ℝ, ∃ᶠ δ : ℝ in 𝓝[>] 0, 0 < splitIncrement F ξ δ := by
  constructor
  · by_contra hcon
    push Not at hcon
    exact hx₀ (re_eq_zero_of_splitIncrement_nonneg hF (m := -m)
      (fun x => (abs_le.mp (hm x)).1) hlim hcon x₀)
  · by_contra hcon
    push Not at hcon
    exact hx₀ (re_eq_zero_of_splitIncrement_nonpos hF (m := m)
      (fun x => (abs_le.mp (hm x)).2) hlim hcon x₀)

/-! ### The prime side of the projected pair -/

/-- The symbol of the linear statistic with real test `g`: `F(w) = ∫ g(u) e^{iwu} du`. -/
def fourierSymbol (g : ℝ → ℝ) (w : ℂ) : ℂ := ∫ u : ℝ, (g u : ℂ) * cexp (I * w * u)

/-- **The prime side of the projected pair.** For a continuous compactly supported real test
the split increment is `∫ g(u) · 2 cos(ξu) (cosh(δu) − 1) du`: projecting a reflection pair to
the line changes the statistic by the pairing of the test with a smooth even density. -/
theorem splitIncrement_fourierSymbol {g : ℝ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
    (ξ δ : ℝ) :
    splitIncrement (fourierSymbol g) ξ δ =
      ∫ u : ℝ, g u * (2 * Real.cos (ξ * u) * (Real.cosh (δ * u) - 1)) := by
  have hint : ∀ w : ℂ, Integrable fun u : ℝ => (g u : ℂ) * cexp (I * w * u) := by
    intro w
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact (Complex.continuous_ofReal.comp hg).mul
        (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal))
    · exact (hgc.comp_left (g := fun x : ℝ => (x : ℂ)) Complex.ofReal_zero).mul_right
  have hre : ∀ w : ℂ, (fourierSymbol g w).re = ∫ u : ℝ, ((g u : ℂ) * cexp (I * w * u)).re :=
    fun w => (integral_re (hint w)).symm
  have hpt : ∀ (a b u : ℝ), ((g u : ℂ) * cexp (I * ((a : ℂ) + b * I) * u)).re =
      g u * (Real.exp (-(b * u)) * Real.cos (a * u)) := by
    intro a b u
    have harg : I * ((a : ℂ) + b * I) * u = ((-(b * u) : ℝ) : ℂ) + ((a * u : ℝ) : ℂ) * I := by
      push_cast
      linear_combination ((b : ℂ) * u) * Complex.I_sq
    rw [harg, Complex.exp_add, ← Complex.ofReal_exp, Complex.re_ofReal_mul,
      Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  have h1 : (fourierSymbol g (ξ + δ * I)).re =
      ∫ u : ℝ, g u * (Real.exp (-(δ * u)) * Real.cos (ξ * u)) := by
    rw [hre]
    exact integral_congr_ae (Eventually.of_forall fun u => hpt ξ δ u)
  have h2 : (fourierSymbol g (ξ + δ * -I)).re =
      ∫ u : ℝ, g u * (Real.exp (δ * u) * Real.cos (ξ * u)) := by
    rw [hre]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    have := hpt ξ (-δ) u
    simp only [Complex.ofReal_neg, neg_mul, neg_neg] at this
    simpa only [mul_neg] using this
  have h3 : (fourierSymbol g ξ).re = ∫ u : ℝ, g u * Real.cos (ξ * u) := by
    rw [hre]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    have := hpt ξ 0 u
    simpa using this
  have hi : ∀ φ : ℝ → ℝ, Continuous φ → Integrable fun u : ℝ => g u * φ u := fun φ hφ =>
    Continuous.integrable_of_hasCompactSupport (hg.mul hφ) hgc.mul_right
  have hI1 : Integrable fun u : ℝ => g u * (Real.exp (-(δ * u)) * Real.cos (ξ * u)) :=
    hi _ (by fun_prop)
  have hI2 : Integrable fun u : ℝ => g u * (Real.exp (δ * u) * Real.cos (ξ * u)) :=
    hi _ (by fun_prop)
  have hI3 : Integrable fun u : ℝ => g u * Real.cos (ξ * u) := hi _ (by fun_prop)
  have hI12 : Integrable fun u : ℝ => g u * (Real.exp (-(δ * u)) * Real.cos (ξ * u)) +
      g u * (Real.exp (δ * u) * Real.cos (ξ * u)) := hI1.add hI2
  have hI3' : Integrable fun u : ℝ => 2 * (g u * Real.cos (ξ * u)) := hI3.const_mul 2
  have e12 : (∫ u : ℝ, g u * (Real.exp (-(δ * u)) * Real.cos (ξ * u))) +
      ∫ u : ℝ, g u * (Real.exp (δ * u) * Real.cos (ξ * u)) =
      ∫ u : ℝ, (g u * (Real.exp (-(δ * u)) * Real.cos (ξ * u)) +
        g u * (Real.exp (δ * u) * Real.cos (ξ * u))) := (integral_add hI1 hI2).symm
  have e3 : 2 * ∫ u : ℝ, g u * Real.cos (ξ * u) = ∫ u : ℝ, 2 * (g u * Real.cos (ξ * u)) :=
    (integral_const_mul 2 _).symm
  have e : (∫ u : ℝ, (g u * (Real.exp (-(δ * u)) * Real.cos (ξ * u)) +
        g u * (Real.exp (δ * u) * Real.cos (ξ * u)))) -
      ∫ u : ℝ, 2 * (g u * Real.cos (ξ * u)) =
      ∫ u : ℝ, ((g u * (Real.exp (-(δ * u)) * Real.cos (ξ * u)) +
        g u * (Real.exp (δ * u) * Real.cos (ξ * u))) - 2 * (g u * Real.cos (ξ * u))) :=
    (integral_sub hI12 hI3').symm
  rw [splitIncrement, h1, h2, h3, e12, e3, e]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only [Real.cosh_eq]
  ring

/-! ### The heat statistic has a floor in the height -/

/-- The symbol of the heat statistic at time `t`: `F(w) = e^{−t w²}`. -/
def heatSymbol (t : ℝ) (w : ℂ) : ℂ := cexp (-(t : ℂ) * (w * w))

theorem hasDerivAt_heatSymbol (t : ℝ) (w : ℂ) :
    HasDerivAt (heatSymbol t) (heatSymbol t w * (-(t : ℂ) * (2 * w))) w := by
  have h := (((hasDerivAt_id' w).mul (hasDerivAt_id' w)).const_mul (-(t : ℂ))).cexp
  refine h.congr_deriv ?_
  simp only [Pi.mul_apply]
  unfold heatSymbol
  ring

theorem differentiable_heatSymbol (t : ℝ) : Differentiable ℂ (heatSymbol t) :=
  fun w => (hasDerivAt_heatSymbol t w).differentiableAt

/-- The curvature of the heat symbol on the line: `Re F''(ξ) = (4t²ξ² − 2t) e^{−tξ²}`. -/
theorem re_deriv2_heatSymbol (t ξ : ℝ) :
    (deriv (deriv (heatSymbol t)) ξ).re =
      (4 * t ^ 2 * ξ ^ 2 - 2 * t) * Real.exp (-(t * ξ ^ 2)) := by
  have hd1 : deriv (heatSymbol t) = fun w : ℂ => heatSymbol t w * (-(t : ℂ) * (2 * w)) :=
    funext fun w => (hasDerivAt_heatSymbol t w).deriv
  have hd2 : deriv (fun w : ℂ => heatSymbol t w * (-(t : ℂ) * (2 * w))) (ξ : ℂ) =
      heatSymbol t ξ * (-(t : ℂ) * (2 * ξ)) * (-(t : ℂ) * (2 * ξ)) +
        heatSymbol t ξ * (-(t : ℂ) * (2 * 1)) :=
    ((hasDerivAt_heatSymbol t (ξ : ℂ)).mul
      (((hasDerivAt_id' (ξ : ℂ)).const_mul 2).const_mul (-(t : ℂ)))).deriv
  have hval : heatSymbol t ξ = ((Real.exp (-(t * ξ ^ 2)) : ℝ) : ℂ) := by
    unfold heatSymbol
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  have hreal : heatSymbol t ξ * (-(t : ℂ) * (2 * ξ)) * (-(t : ℂ) * (2 * ξ)) +
      heatSymbol t ξ * (-(t : ℂ) * (2 * 1)) =
      (((4 * t ^ 2 * ξ ^ 2 - 2 * t) * Real.exp (-(t * ξ ^ 2)) : ℝ) : ℂ) := by
    rw [hval]
    push_cast
    ring
  rw [hd1, hd2, hreal, Complex.ofReal_re]

/-- **The heat statistic is monotone below a height.** At heat time `t > 0` the statistic
`Σ_ρ e^{−t ξ_ρ²}` increases when a double point of the line splits at an ordinate with
`2tξ² < 1`, and decreases when it splits at an ordinate with `2tξ² > 1`, at every small depth.
Projection to the line lowers it exactly below the height `(2t)^{−1/2}`. -/
theorem heatSymbol_splitIncrement_sign {t : ℝ} (ht : 0 < t) (ξ : ℝ) :
    (2 * t * ξ ^ 2 < 1 → ∀ᶠ δ : ℝ in 𝓝[≠] 0, 0 < splitIncrement (heatSymbol t) ξ δ) ∧
      (1 < 2 * t * ξ ^ 2 → ∀ᶠ δ : ℝ in 𝓝[≠] 0, splitIncrement (heatSymbol t) ξ δ < 0) := by
  have hE : 0 < Real.exp (-(t * ξ ^ 2)) := Real.exp_pos _
  have hfac : (4 * t ^ 2 * ξ ^ 2 - 2 * t) * Real.exp (-(t * ξ ^ 2)) =
      2 * t * (2 * t * ξ ^ 2 - 1) * Real.exp (-(t * ξ ^ 2)) := by ring
  constructor
  · intro h
    apply eventually_splitIncrement_pos_of_re_deriv2_neg (differentiable_heatSymbol t)
    rw [re_deriv2_heatSymbol, hfac]
    exact mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by linarith only [ht])
      (by linarith only [h])) hE
  · intro h
    apply eventually_splitIncrement_neg_of_re_deriv2_pos (differentiable_heatSymbol t)
    rw [re_deriv2_heatSymbol, hfac]
    exact mul_pos (mul_pos (by linarith only [ht]) (by linarith only [h])) hE

end GaloisForLFunctions.FloorFreeArithmetic
