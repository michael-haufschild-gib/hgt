import GaloisForLFunctions.RHTower.RouteRCrossPrimeStokesCalkinPolarHandoff

/-!
# Four-channel structure of reflection-odd cross-prime Stokes curvature

The analytic pair scalar cannot be copied into the canonical Sonin prime seam:
on `(3,5,7)` it has nonzero triangle charge near the neutral grade, whereas
every one-prime-potential difference has zero triangle charge. The scalar does,
however, factor exactly through four one-prime channels. This identifies a
symmetric pair kernel as the algebraic object to test against source transport;
it does not assert an all-prime source lift or RH.
-/

open Filter
open scoped Topology
namespace RHTower
noncomputable section

private def f (x y : ℝ) : ℝ := (x + y) * (y / x + x / y)

private theorem f_lower {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    2 * (x + y) ≤ f x y := by
  have hxy : 0 < x * y := mul_pos hx hy
  have hsq := sq_nonneg (y - x)
  have hrat : 2 ≤ y / x + x / y := by
    have heq : y / x + x / y = (y * y + x * x) / (x * y) := by
      field_simp
    rw [heq]
    apply (le_div_iff₀ hxy).2
    nlinarith
  unfold f
  simpa only [mul_comm] using
    (mul_le_mul_of_nonneg_left hrat (le_of_lt (add_pos hx hy)))

private theorem f_upper {x z : ℝ} (hx : 0 < x) (hxz : x < z) (hz2 : z < 2 * x) :
    f x z < (15 / 2 : ℝ) * x := by
  have hz : 0 < z := lt_trans hx hxz
  have hxzpos : 0 < x * z := mul_pos hx hz
  have hprod : (2 * z - x) * (z - 2 * x) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
  have hnum : 2 * (z * z + x * x) ≤ 5 * (x * z) := by nlinarith [hprod]
  have hrat : z / x + x / z ≤ (5 / 2 : ℝ) := by
    have heq : z / x + x / z = (z * z + x * x) / (x * z) := by
      field_simp
    rw [heq]
    apply (div_le_iff₀ hxzpos).2
    nlinarith
  have hsum : x + z < 3 * x := by linarith
  have hmul : f x z ≤ (x + z) * (5 / 2 : ℝ) := by
    unfold f
    exact mul_le_mul_of_nonneg_left hrat (le_of_lt (add_pos hx hz))
  linarith

private theorem triangle_f_bound {x y z : ℝ}
    (hx : 0 < x) (hxy : x < y) (hyz : y < z) (hz2 : z < 2 * x) :
    x / 2 < f x y + f y z - f x z := by
  have hy : 0 < y := lt_trans hx hxy
  have hz : 0 < z := lt_trans hy hyz
  have h1 := f_lower hx hy
  have h2 := f_lower hy hz
  have h3 := f_upper hx (hxy.trans hyz) hz2
  linarith

private theorem log_three_five_seven :
    0 < Real.log (3 : ℝ) ∧
    Real.log (3 : ℝ) < Real.log (5 : ℝ) ∧
    Real.log (5 : ℝ) < Real.log (7 : ℝ) ∧
    Real.log (7 : ℝ) < 2 * Real.log (3 : ℝ) := by
  constructor
  · exact Real.log_pos (by norm_num)
  constructor
  · exact Real.log_lt_log (by norm_num) (by norm_num)
  constructor
  · exact Real.log_lt_log (by norm_num) (by norm_num)
  · have h := Real.log_lt_log (by norm_num : (0 : ℝ) < 7)
        (by norm_num : (7 : ℝ) < 9)
    rw [show (9 : ℝ) = 3 ^ (2 : ℕ) by norm_num, Real.log_pow] at h
    norm_num at h ⊢
    exact h

private theorem sinh_slope (a : ℝ) :
    Tendsto (fun g : ℝ => Real.sinh (g * a) / g) (𝓝[≠] 0) (𝓝 a) := by
  have hd : HasDerivAt (fun g : ℝ => Real.sinh (g * a)) a 0 := by
    simpa only [Function.comp_def, id_eq, zero_mul, Real.cosh_zero, one_mul] using
      (Real.hasDerivAt_sinh ((0 : ℝ) * a)).comp 0
        ((hasDerivAt_id (0 : ℝ)).mul_const a)
  simpa [Real.sinh_zero, smul_eq_mul, div_eq_mul_inv, mul_comm] using
    hd.tendsto_slope_zero

private theorem stokes_ratio_eq_sinh_ratio {p q : ℕ} (hp : 1 < p) (hq : 1 < q)
    {g : ℝ} (hg : g ≠ 0) :
    routeRCrossPrimeStokesRatio p q g =
      Real.sinh (g * Real.log q / 2) / Real.sinh (g * Real.log p / 2) := by
  have hx : Real.log (p : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hp)).ne'
  have hy : Real.log (q : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hq)).ne'
  have hA : g * Real.log p / 2 ≠ 0 := by exact div_ne_zero (mul_ne_zero hg hx) (by norm_num)
  have hB : g * Real.log q / 2 ≠ 0 := by exact div_ne_zero (mul_ne_zero hg hy) (by norm_num)
  have hSA : Real.sinh (g * Real.log p / 2) ≠ 0 := Real.sinh_ne_zero.mpr hA
  have hSB : Real.sinh (g * Real.log q / 2) ≠ 0 := Real.sinh_ne_zero.mpr hB
  unfold routeRCrossPrimeStokesRatio routeRDeningerHyperbolicSinc
  rw [if_neg hA, if_neg hB]
  field_simp [hg, hx, hy, hA, hB, hSA, hSB]

private theorem stokes_ratio_slope {p q : ℕ} (hp : 1 < p) (hq : 1 < q) :
    Tendsto (routeRCrossPrimeStokesRatio p q) (𝓝[≠] (0 : ℝ))
      (𝓝 (Real.log q / Real.log p)) := by
  have hx : Real.log (p : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hp)).ne'
  have hA := sinh_slope (Real.log (p : ℝ) / 2)
  have hB := sinh_slope (Real.log (q : ℝ) / 2)
  have hlim : Tendsto
      (fun g : ℝ =>
        (Real.sinh (g * (Real.log q / 2)) / g) /
          (Real.sinh (g * (Real.log p / 2)) / g))
      (𝓝[≠] 0) (𝓝 ((Real.log q / 2) / (Real.log p / 2))) :=
    hB.div hA (div_ne_zero hx (by norm_num))
  have hgnz : ∀ᶠ g : ℝ in 𝓝[≠] 0, g ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with g hg
    simpa using hg
  have heq : (routeRCrossPrimeStokesRatio p q) =ᶠ[𝓝[≠] (0 : ℝ)]
      (fun g : ℝ =>
        (Real.sinh (g * (Real.log q / 2)) / g) /
          (Real.sinh (g * (Real.log p / 2)) / g)) := by
    filter_upwards [hgnz] with g hg
    rw [stokes_ratio_eq_sinh_ratio hp hq hg]
    have hSA : Real.sinh (g * Real.log p / 2) ≠ 0 := by
      apply Real.sinh_ne_zero.mpr
      exact div_ne_zero (mul_ne_zero hg hx) (by norm_num)
    field_simp [hg, hSA]
  have htarget : (Real.log (q : ℝ) / 2) / (Real.log p / 2) =
      Real.log q / Real.log p := by field_simp [hx]
  rw [← htarget]
  exact Tendsto.congr' heq.symm hlim

private theorem stokes_odd_slope {p q : ℕ} (hp : 1 < p) (hq : 1 < q) :
    Tendsto (fun g : ℝ => routeRCrossPrimeStokesOddCurvature p q g / g)
      (𝓝[≠] (0 : ℝ))
      (𝓝 (-f (Real.log p) (Real.log q))) := by
  set x : ℝ := Real.log p
  set y : ℝ := Real.log q
  have hx : x ≠ 0 := (Real.log_pos (by exact_mod_cast hp)).ne'
  have hy : y ≠ 0 := (Real.log_pos (by exact_mod_cast hq)).ne'
  have hphase := sinh_slope ((x + y) / 2)
  have hratio := stokes_ratio_slope hp hq
  have hratio0 : y / x ≠ 0 := div_ne_zero hy hx
  have hsum := hratio.add (hratio.inv₀ hratio0)
  have hmain : Tendsto
      (fun g : ℝ => -2 * (Real.sinh (g * ((x + y) / 2)) / g) *
        (routeRCrossPrimeStokesRatio p q g +
          (routeRCrossPrimeStokesRatio p q g)⁻¹))
      (𝓝[≠] 0)
      (𝓝 (-2 * ((x + y) / 2) * (y / x + (y / x)⁻¹))) := by
    exact (tendsto_const_nhds.mul hphase).mul hsum
  have htarget : -2 * ((x + y) / 2) * (y / x + (y / x)⁻¹) = -f x y := by
    unfold f
    field_simp [hx, hy]
  rw [← htarget]
  apply Tendsto.congr' ?_ hmain
  filter_upwards with g
  rw [routeRCrossPrimeStokesOddCurvature_eq]
  unfold routeRCrossPrimeStokesPhase routeRCrossPrimeStokesGauge
  dsimp [x, y]
  ring

private theorem stokes_triangle_slope :
    Tendsto
      (fun g : ℝ =>
        (routeRCrossPrimeStokesOddCurvature 3 5 g +
          routeRCrossPrimeStokesOddCurvature 5 7 g -
          routeRCrossPrimeStokesOddCurvature 3 7 g) / g)
      (𝓝[≠] (0 : ℝ))
      (𝓝 (-(f (Real.log 3) (Real.log 5) +
        f (Real.log 5) (Real.log 7) - f (Real.log 3) (Real.log 7)))) := by
  have h35 := stokes_odd_slope (p := 3) (q := 5) (by norm_num) (by norm_num)
  have h57 := stokes_odd_slope (p := 5) (q := 7) (by norm_num) (by norm_num)
  have h37 := stokes_odd_slope (p := 3) (q := 7) (by norm_num) (by norm_num)
  have h := (h35.add h57).sub h37
  convert h using 1
  · funext g
    ring
  · ring

private theorem stokes_triangle_slope_strict :
    Tendsto
      (fun g : ℝ =>
        (routeRCrossPrimeStokesOddCurvature 3 5 g +
          routeRCrossPrimeStokesOddCurvature 5 7 g -
          routeRCrossPrimeStokesOddCurvature 3 7 g) / g)
      (𝓝[≠] (0 : ℝ))
      (𝓝 (-(f (Real.log 3) (Real.log 5) +
        f (Real.log 5) (Real.log 7) - f (Real.log 3) (Real.log 7)))) ∧
    -(f (Real.log 3) (Real.log 5) +
        f (Real.log 5) (Real.log 7) - f (Real.log 3) (Real.log 7)) <
      -(Real.log 3) / 2 := by
  refine ⟨stokes_triangle_slope, ?_⟩
  obtain ⟨hx, hxy, hyz, hz2⟩ := log_three_five_seven
  have h := triangle_f_bound hx hxy hyz hz2
  linarith

/-- The `(3,5,7)` triangle charge is nonzero in a punctured neighborhood of
the neutral grade. -/
theorem stokes_triangle_ne_zero_near_zero :
    ∀ᶠ g : ℝ in 𝓝[≠] 0,
      routeRCrossPrimeStokesOddCurvature 3 5 g +
        routeRCrossPrimeStokesOddCurvature 5 7 g -
        routeRCrossPrimeStokesOddCurvature 3 7 g ≠ 0 := by
  obtain ⟨hlim, hbound⟩ := stokes_triangle_slope_strict
  have hlog : 0 < Real.log (3 : ℝ) := log_three_five_seven.1
  have hnegative :
      -(f (Real.log 3) (Real.log 5) +
          f (Real.log 5) (Real.log 7) - f (Real.log 3) (Real.log 7)) < 0 := by
    linarith
  have hev := hlim.eventually (eventually_lt_nhds hnegative)
  filter_upwards [hev] with g hg
  intro hzero
  rw [hzero, zero_div] at hg
  exact (lt_irrefl (0 : ℝ)) hg

/-- No choice of one-prime potentials realizes the analytic pair scalar on all
three edges of `(3,5,7)` for every grade. -/
theorem no_direct_stokes_three_prime_potential :
    ¬∃ a : ℕ → ℝ → ℝ, ∀ g : ℝ,
      routeRCrossPrimeStokesOddCurvature 3 5 g = a 3 g - a 5 g ∧
      routeRCrossPrimeStokesOddCurvature 5 7 g = a 5 g - a 7 g ∧
      routeRCrossPrimeStokesOddCurvature 3 7 g = a 3 g - a 7 g := by
  rintro ⟨a, ha⟩
  obtain ⟨g, hg⟩ := stokes_triangle_ne_zero_near_zero.exists
  rcases ha g with ⟨h35, h57, h37⟩
  apply hg
  rw [h35, h57, h37]
  ring

/-- **Neutral-grade slope of the `(3,5,7)` triangle charge.** The quotient `Ω(g)/g` has a limit
at the neutral grade, and that limit is below `-(log 3)/2`. -/
theorem exists_tendsto_stokes_triangle_357_slope :
    ∃ L : ℝ, L < -(Real.log 3) / 2 ∧
      Tendsto
        (fun g : ℝ =>
          (routeRCrossPrimeStokesOddCurvature 3 5 g +
            routeRCrossPrimeStokesOddCurvature 5 7 g -
            routeRCrossPrimeStokesOddCurvature 3 7 g) / g)
        (𝓝[≠] (0 : ℝ)) (𝓝 L) :=
  ⟨_, stokes_triangle_slope_strict.2, stokes_triangle_slope_strict.1⟩

/-- Near the neutral grade the `(3,5,7)` triangle charge has sign opposite to `g`. -/
theorem stokes_triangle_357_sign_opposite :
    ∀ᶠ g : ℝ in 𝓝[≠] 0,
      g * (routeRCrossPrimeStokesOddCurvature 3 5 g +
        routeRCrossPrimeStokesOddCurvature 5 7 g -
        routeRCrossPrimeStokesOddCurvature 3 7 g) < 0 := by
  obtain ⟨L, hL, hlim⟩ := exists_tendsto_stokes_triangle_357_slope
  have hL0 : L < 0 := by
    have : 0 < Real.log (3 : ℝ) := log_three_five_seven.1
    linarith
  filter_upwards [hlim.eventually (eventually_lt_nhds hL0), self_mem_nhdsWithin] with g hg hg0
  have hg0' : g ≠ 0 := hg0
  have hsq : 0 < g * g := mul_self_pos.mpr hg0'
  have hrw : g * (routeRCrossPrimeStokesOddCurvature 3 5 g +
        routeRCrossPrimeStokesOddCurvature 5 7 g -
        routeRCrossPrimeStokesOddCurvature 3 7 g) =
      (g * g) * ((routeRCrossPrimeStokesOddCurvature 3 5 g +
        routeRCrossPrimeStokesOddCurvature 5 7 g -
        routeRCrossPrimeStokesOddCurvature 3 7 g) / g) := by
    field_simp
  rw [hrw]
  exact mul_neg_of_pos_of_neg hsq hg

/-- **Gauge invariance of the triangle charge.** Adding any one-particle potential difference
`b_p - b_q` to every pair coefficient leaves the triangle charge unchanged. -/
theorem triangle_charge_gauge_invariant (C : ℕ → ℕ → ℝ) (b : ℕ → ℝ) (p q r : ℕ) :
    (C p q + (b p - b q)) + (C q r + (b q - b r)) - (C p r + (b p - b r)) =
      C p q + C q r - C p r := by
  ring

/-- **Three-prime compensation law.** Any pair correction `B` that turns the analytic scalar into
a potential difference on the three edges of `(3,5,7)` has triangle sum `-Ω(g)`. -/
theorem stokes_triangle_357_compensation (B : ℕ → ℕ → ℝ) (a : ℕ → ℝ) (g : ℝ)
    (h35 : routeRCrossPrimeStokesOddCurvature 3 5 g + B 3 5 = a 3 - a 5)
    (h57 : routeRCrossPrimeStokesOddCurvature 5 7 g + B 5 7 = a 5 - a 7)
    (h37 : routeRCrossPrimeStokesOddCurvature 3 7 g + B 3 7 = a 3 - a 7) :
    B 3 5 + B 5 7 - B 3 7 =
      -(routeRCrossPrimeStokesOddCurvature 3 5 g +
        routeRCrossPrimeStokesOddCurvature 5 7 g -
        routeRCrossPrimeStokesOddCurvature 3 7 g) := by
  linarith

/-- Near the neutral grade, the compensating pair correction is never itself a potential
difference on `(3,5,7)`. -/
theorem stokes_triangle_357_correction_not_potential :
    ∀ᶠ g : ℝ in 𝓝[≠] 0, ∀ (B : ℕ → ℕ → ℝ) (a b : ℕ → ℝ),
      routeRCrossPrimeStokesOddCurvature 3 5 g + B 3 5 = a 3 - a 5 →
      routeRCrossPrimeStokesOddCurvature 5 7 g + B 5 7 = a 5 - a 7 →
      routeRCrossPrimeStokesOddCurvature 3 7 g + B 3 7 = a 3 - a 7 →
      ¬ (B 3 5 = b 3 - b 5 ∧ B 5 7 = b 5 - b 7 ∧ B 3 7 = b 3 - b 7) := by
  filter_upwards [stokes_triangle_ne_zero_near_zero] with g hg B a b h35 h57 h37 hB
  have hcomp := stokes_triangle_357_compensation B a g h35 h57 h37
  obtain ⟨hb35, hb57, hb37⟩ := hB
  rw [hb35, hb57, hb37] at hcomp
  exact hg (by linarith)

/-- First one-prime Stokes channel, `sinh(t) cosh(t)`. -/
def stokesChannelU (p : ℕ) (g : ℝ) : ℝ :=
  Real.sinh (g * Real.log p / 2) * Real.cosh (g * Real.log p / 2)

/-- Second one-prime Stokes channel, `sinh(t)^2`. -/
def stokesChannelV (p : ℕ) (g : ℝ) : ℝ :=
  Real.sinh (g * Real.log p / 2) ^ 2

/-- Third one-prime Stokes channel, `coth(t)` away from neutral grade. -/
def stokesChannelW (p : ℕ) (g : ℝ) : ℝ :=
  Real.cosh (g * Real.log p / 2) / Real.sinh (g * Real.log p / 2)

/-- Exact four-term separable factorization of the reflection-odd pair scalar.
For any finite prime packet, its full pair matrix has rank at most four. -/
theorem stokes_odd_four_channel {p q : ℕ} (hp : 1 < p) (hq : 1 < q)
    {g : ℝ} (hg : g ≠ 0) :
    routeRCrossPrimeStokesOddCurvature p q g =
      -2 * (stokesChannelU p g + stokesChannelU q g +
        stokesChannelV p g * stokesChannelW q g +
        stokesChannelW p g * stokesChannelV q g) := by
  have hx : Real.log (p : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hp)).ne'
  have hy : Real.log (q : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hq)).ne'
  have hA : Real.sinh (g * Real.log p / 2) ≠ 0 := by
    apply Real.sinh_ne_zero.mpr
    exact div_ne_zero (mul_ne_zero hg hx) (by norm_num)
  have hB : Real.sinh (g * Real.log q / 2) ≠ 0 := by
    apply Real.sinh_ne_zero.mpr
    exact div_ne_zero (mul_ne_zero hg hy) (by norm_num)
  rw [routeRCrossPrimeStokesOddCurvature_eq]
  unfold routeRCrossPrimeStokesGauge
  rw [stokes_ratio_eq_sinh_ratio hp hq hg]
  unfold routeRCrossPrimeStokesPhase stokesChannelU stokesChannelV stokesChannelW
  have hsum : g * (Real.log p + Real.log q) / 2 =
      g * Real.log p / 2 + g * Real.log q / 2 := by ring
  rw [hsum, Real.sinh_add]
  field_simp [hA, hB]
  ring

end
end RHTower
