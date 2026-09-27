import GaloisForLFunctions.RHTower.RouteRCrossPrimeStokesFourChannelObstruction
import Mathlib.NumberTheory.SumPrimeReciprocals

/-!
# Cofinal three-prime Stokes holonomy at every nonzero grade

For the reflection-odd analytic pair scalar `c_pq(g)` and a fixed pair `p < q`, the triangle
charge `Ω_pqr(g) = c_pq(g) + c_qr(g) - c_pr(g)` grows like `r^|g|` along a cofinal third index:

`Ω_pqr(g) / r^|g| → sign(g) (1/(1-p^{-|g|}) - 1/(1-q^{-|g|}))`,

with strictly positive bracket.  The proof uses the exact rational normal form of `c_pr(g)` in
`P = p^g`, `R = r^g`.  Consequences: no one-prime potential reproduces `c_pq(g)` on all prime
pairs at any nonzero grade; at small positive grade the triangle charge changes sign between
`(3,5,7)` and `(3,5,r)` for large `r`; any pair correction making the curvature a coboundary has
rows of size at least `C r^|g|`, and the two corrected rows are never both square-summable
against the reciprocal-prime weight `1/r`.
-/

open Filter Topology

namespace RHTower

noncomputable section

/-- Triangle charge (holonomy) of the analytic reflection-odd pair scalar. -/
def stokesTriangleCharge (p q r : ℕ) (g : ℝ) : ℝ :=
  routeRCrossPrimeStokesOddCurvature p q g + routeRCrossPrimeStokesOddCurvature q r g -
    routeRCrossPrimeStokesOddCurvature p r g

/-- The reflection-odd pair scalar is odd in the grade. -/
theorem routeRCrossPrimeStokesOddCurvature_neg_grade (p q : ℕ) (g : ℝ) :
    routeRCrossPrimeStokesOddCurvature p q (-g) =
      -routeRCrossPrimeStokesOddCurvature p q g := by
  unfold routeRCrossPrimeStokesOddCurvature
  rw [neg_neg]
  ring

theorem stokesTriangleCharge_neg_grade (p q r : ℕ) (g : ℝ) :
    stokesTriangleCharge p q r (-g) = -stokesTriangleCharge p q r g := by
  unfold stokesTriangleCharge
  simp only [routeRCrossPrimeStokesOddCurvature_neg_grade]
  ring

/-- Off the neutral grade the regularized Stokes ratio is a quotient of hyperbolic sines. -/
theorem routeRCrossPrimeStokesRatio_eq_sinh_div {p q : ℕ} (hp : 1 < p) (hq : 1 < q)
    {g : ℝ} (hg : g ≠ 0) :
    routeRCrossPrimeStokesRatio p q g =
      Real.sinh (g * Real.log q / 2) / Real.sinh (g * Real.log p / 2) := by
  have hx : Real.log (p : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hp)).ne'
  have hy : Real.log (q : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hq)).ne'
  have hA : g * Real.log p / 2 ≠ 0 := div_ne_zero (mul_ne_zero hg hx) (by norm_num)
  have hB : g * Real.log q / 2 ≠ 0 := div_ne_zero (mul_ne_zero hg hy) (by norm_num)
  have hSA : Real.sinh (g * Real.log p / 2) ≠ 0 := Real.sinh_ne_zero.mpr hA
  have hSB : Real.sinh (g * Real.log q / 2) ≠ 0 := Real.sinh_ne_zero.mpr hB
  unfold routeRCrossPrimeStokesRatio routeRDeningerHyperbolicSinc
  rw [if_neg hA, if_neg hB]
  field_simp [hg, hx, hy, hA, hB, hSA, hSB]

private theorem exp_half_rpow {p : ℕ} (hp : 1 < p) (g : ℝ) :
    Real.exp (g * Real.log p / 2) ^ 2 = (p : ℝ) ^ g := by
  rw [← Real.exp_nat_mul, Real.rpow_def_of_pos (by positivity)]
  congr 1
  push_cast
  ring

private theorem sinh_half_eq (x : ℝ) :
    Real.sinh x = (Real.exp x ^ 2 - 1) / (2 * Real.exp x) := by
  rw [Real.sinh_eq, Real.exp_neg]
  have := Real.exp_pos x
  field_simp

/-- **Rational normal form.** With `P = p^g` and `R = r^g`,
`c_pr(g) = -(PR-1)(R-1)/((P-1)R) - (PR-1)(P-1)/((R-1)P)`. -/
theorem routeRCrossPrimeStokesOddCurvature_rational {p r : ℕ} (hp : 1 < p) (hr : 1 < r)
    {g : ℝ} (hg : g ≠ 0) :
    routeRCrossPrimeStokesOddCurvature p r g =
      -(((p : ℝ) ^ g * (r : ℝ) ^ g - 1) * ((r : ℝ) ^ g - 1) /
          (((p : ℝ) ^ g - 1) * (r : ℝ) ^ g)) -
        ((p : ℝ) ^ g * (r : ℝ) ^ g - 1) * ((p : ℝ) ^ g - 1) /
          (((r : ℝ) ^ g - 1) * (p : ℝ) ^ g) := by
  rw [routeRCrossPrimeStokesOddCurvature_eq, routeRCrossPrimeStokesGauge,
    routeRCrossPrimeStokesRatio_eq_sinh_div hp hr hg, routeRCrossPrimeStokesPhase,
    ← exp_half_rpow hp, ← exp_half_rpow hr]
  set u := Real.exp (g * Real.log p / 2) with hu
  set w := Real.exp (g * Real.log r / 2) with hw
  have hsum : g * (Real.log p + Real.log r) / 2 = g * Real.log p / 2 + g * Real.log r / 2 := by
    ring
  have hx : Real.log (p : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hp)).ne'
  have hy : Real.log (r : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hr)).ne'
  have hu0 : 0 < u := Real.exp_pos _
  have hw0 : 0 < w := Real.exp_pos _
  have hu1 : u ^ 2 - 1 ≠ 0 := by
    intro h
    have h1 : u ^ 2 = 1 := by linarith
    have : u = 1 := by nlinarith
    rw [hu, Real.exp_eq_one_iff] at this
    exact div_ne_zero (mul_ne_zero hg hx) (by norm_num) this
  have hw1 : w ^ 2 - 1 ≠ 0 := by
    intro h
    have h1 : w ^ 2 = 1 := by linarith
    have : w = 1 := by nlinarith
    rw [hw, Real.exp_eq_one_iff] at this
    exact div_ne_zero (mul_ne_zero hg hy) (by norm_num) this
  rw [hsum, sinh_half_eq, sinh_half_eq (g * Real.log p / 2), sinh_half_eq (g * Real.log r / 2),
    Real.exp_add, ← hu, ← hw]
  field_simp
  ring

/-- Limit profile of `c_pr(g)/r^g` as a function of `t = r^{-g}`. -/
private def stokesTailProfile (P t : ℝ) : ℝ :=
  -((P - t) * (1 - t) / (P - 1)) - (P - t) * (P - 1) * t / (P * (1 - t))

private theorem stokes_div_rpow_eq {p r : ℕ} (hp : 1 < p) (hr : 1 < r) {g : ℝ} (hg : 0 < g) :
    routeRCrossPrimeStokesOddCurvature p r g / (r : ℝ) ^ g =
      stokesTailProfile ((p : ℝ) ^ g) ((r : ℝ) ^ g)⁻¹ := by
  rw [routeRCrossPrimeStokesOddCurvature_rational hp hr hg.ne']
  have hP : 1 < (p : ℝ) ^ g := Real.one_lt_rpow (by exact_mod_cast hp) hg
  have hR : 1 < (r : ℝ) ^ g := Real.one_lt_rpow (by exact_mod_cast hr) hg
  set P := (p : ℝ) ^ g
  set R := (r : ℝ) ^ g
  have hP1 : P - 1 ≠ 0 := by linarith
  have hR1 : R - 1 ≠ 0 := by linarith
  have hR0 : R ≠ 0 := by linarith
  have hP0 : P ≠ 0 := by linarith
  have hRt : 1 - R⁻¹ ≠ 0 := by
    have : R⁻¹ < 1 := inv_lt_one_of_one_lt₀ hR
    linarith
  unfold stokesTailProfile
  field_simp

private theorem tendsto_rpow_nat_atTop {g : ℝ} (hg : 0 < g) :
    Tendsto (fun r : ℕ => (r : ℝ) ^ g) atTop atTop :=
  (tendsto_rpow_atTop hg).comp tendsto_natCast_atTop_atTop

/-- **Cofinal one-leg limit.** For `g > 0`, `c_pr(g)/r^g → -1/(1-p^{-g})` as `r → ∞`. -/
theorem tendsto_stokesOddCurvature_div_rpow {p : ℕ} (hp : 1 < p) {g : ℝ} (hg : 0 < g) :
    Tendsto (fun r : ℕ => routeRCrossPrimeStokesOddCurvature p r g / (r : ℝ) ^ g) atTop
      (𝓝 (-(1 / (1 - (p : ℝ) ^ (-g))))) := by
  have hP : 1 < (p : ℝ) ^ g := Real.one_lt_rpow (by exact_mod_cast hp) hg
  set P := (p : ℝ) ^ g with hPdef
  have hinv : Tendsto (fun r : ℕ => ((r : ℝ) ^ g)⁻¹) atTop (𝓝 0) :=
    (tendsto_rpow_nat_atTop hg).inv_tendsto_atTop
  have hcont : ContinuousAt (stokesTailProfile P) 0 := by
    unfold stokesTailProfile
    have hP1 : P - 1 ≠ 0 := by linarith
    have hP0 : P * (1 - 0) ≠ 0 := by simp; linarith
    fun_prop (disch := assumption)
  have hlim := hcont.tendsto.comp hinv
  have hval : stokesTailProfile P 0 = -(1 / (1 - (p : ℝ) ^ (-g))) := by
    unfold stokesTailProfile
    rw [Real.rpow_neg (by positivity), ← hPdef]
    have hP1 : P - 1 ≠ 0 := by linarith
    have hP0 : P ≠ 0 := by linarith
    have hP2 : 1 - P⁻¹ ≠ 0 := by
      have : P⁻¹ < 1 := inv_lt_one_of_one_lt₀ hP
      linarith
    field_simp
    ring
  rw [hval] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 1] with r hr
  exact (stokes_div_rpow_eq hp hr hg).symm

/-- The positive cofinal holonomy coefficient `1/(1-p^{-a}) - 1/(1-q^{-a})`. -/
def stokesHolonomyCoefficient (p q : ℕ) (a : ℝ) : ℝ :=
  1 / (1 - (p : ℝ) ^ (-a)) - 1 / (1 - (q : ℝ) ^ (-a))

theorem stokesHolonomyCoefficient_pos {p q : ℕ} (hp : 1 < p) (hpq : p < q) {a : ℝ}
    (ha : 0 < a) : 0 < stokesHolonomyCoefficient p q a := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (lt_trans zero_lt_one hp)
  have hq1 : (1 : ℝ) < q := by exact_mod_cast (lt_trans hp hpq)
  have hpa : 1 < (p : ℝ) ^ a := Real.one_lt_rpow (by exact_mod_cast hp) ha
  have hlt : (p : ℝ) ^ a < (q : ℝ) ^ a :=
    Real.rpow_lt_rpow hp0.le (by exact_mod_cast hpq) ha
  unfold stokesHolonomyCoefficient
  rw [Real.rpow_neg hp0.le, Real.rpow_neg (by linarith)]
  have hqa : 1 < (q : ℝ) ^ a := hpa.trans hlt
  have h1 : 0 < 1 - ((p : ℝ) ^ a)⁻¹ := by
    have : ((p : ℝ) ^ a)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hpa
    linarith
  have h2 : 1 - ((p : ℝ) ^ a)⁻¹ < 1 - ((q : ℝ) ^ a)⁻¹ := by
    have : ((q : ℝ) ^ a)⁻¹ < ((p : ℝ) ^ a)⁻¹ := inv_strictAnti₀ (by linarith) hlt
    linarith
  have := one_div_lt_one_div_of_lt h1 h2
  linarith

private theorem tendsto_triangle_pos {p q : ℕ} (hp : 1 < p) (hq : 1 < q) {g : ℝ}
    (hg : 0 < g) :
    Tendsto (fun r : ℕ => stokesTriangleCharge p q r g / (r : ℝ) ^ g) atTop
      (𝓝 (stokesHolonomyCoefficient p q g)) := by
  have hfixed : Tendsto (fun r : ℕ => routeRCrossPrimeStokesOddCurvature p q g / (r : ℝ) ^ g)
      atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using
      (tendsto_const_nhds (x := routeRCrossPrimeStokesOddCurvature p q g)).mul
        (tendsto_rpow_nat_atTop hg).inv_tendsto_atTop
  have h := (hfixed.add (tendsto_stokesOddCurvature_div_rpow hq hg)).sub
    (tendsto_stokesOddCurvature_div_rpow hp hg)
  have hval : 0 + -(1 / (1 - (q : ℝ) ^ (-g))) - -(1 / (1 - (p : ℝ) ^ (-g))) =
      stokesHolonomyCoefficient p q g := by
    unfold stokesHolonomyCoefficient
    ring
  rw [hval] at h
  refine h.congr' (Eventually.of_forall fun r => ?_)
  unfold stokesTriangleCharge
  ring

/-- **Cofinal triangle holonomy at every nonzero grade.** With `a = |g|`,
`Ω_pqr(g)/r^a → sign(g) (1/(1-p^{-a}) - 1/(1-q^{-a}))` as the third index `r → ∞`. -/
theorem tendsto_stokesTriangleCharge_div_rpow {p q : ℕ} (hp : 1 < p) (hq : 1 < q) {g : ℝ}
    (hg : g ≠ 0) :
    Tendsto (fun r : ℕ => stokesTriangleCharge p q r g / (r : ℝ) ^ |g|) atTop
      (𝓝 (Real.sign g * stokesHolonomyCoefficient p q |g|)) := by
  rcases lt_or_gt_of_ne hg with hneg | hpos
  · have h := (tendsto_triangle_pos hp hq (neg_pos.mpr hneg)).neg
    rw [abs_of_neg hneg, Real.sign_of_neg hneg, neg_one_mul]
    refine h.congr' (Eventually.of_forall fun r => ?_)
    show -(stokesTriangleCharge p q r (-g) / (r : ℝ) ^ (-g)) =
      stokesTriangleCharge p q r g / (r : ℝ) ^ (-g)
    rw [stokesTriangleCharge_neg_grade, neg_div, neg_neg]
  · rw [abs_of_pos hpos, Real.sign_of_pos hpos, one_mul]
    exact tendsto_triangle_pos hp hq hpos

/-- **Sign and growth.** For `p < q` and `g ≠ 0` there is `C > 0` such that eventually
`C r^|g| ≤ |Ω_pqr(g)|` and `Ω_pqr(g)` has the sign of `g`. -/
theorem eventually_stokesTriangleCharge_growth {p q : ℕ} (hp : 1 < p) (hpq : p < q) {g : ℝ}
    (hg : g ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ r : ℕ in atTop,
      C * (r : ℝ) ^ |g| ≤ |stokesTriangleCharge p q r g| ∧
        0 < g * stokesTriangleCharge p q r g := by
  have ha : 0 < |g| := abs_pos.mpr hg
  set L := stokesHolonomyCoefficient p q |g| with hL
  have hL0 : 0 < L := stokesHolonomyCoefficient_pos hp hpq ha
  have hlim := tendsto_stokesTriangleCharge_div_rpow hp (lt_trans hp hpq) hg
  have hsg : Real.sign g * Real.sign g = 1 := by
    rcases lt_or_gt_of_ne hg with h | h
    · rw [Real.sign_of_neg h]; norm_num
    · rw [Real.sign_of_pos h]; norm_num
  have hlim' : Tendsto (fun r : ℕ => Real.sign g * (stokesTriangleCharge p q r g /
      (r : ℝ) ^ |g|)) atTop (𝓝 L) := by
    have := hlim.const_mul (Real.sign g)
    rwa [← mul_assoc, hsg, one_mul] at this
  refine ⟨L / 2, half_pos hL0, ?_⟩
  filter_upwards [hlim'.eventually (lt_mem_nhds (half_lt_self hL0)),
    eventually_gt_atTop 0] with r hr hr0
  have hR : 0 < (r : ℝ) ^ |g| := Real.rpow_pos_of_pos (by exact_mod_cast hr0) _
  have habs : |Real.sign g| = 1 := by
    rcases lt_or_gt_of_ne hg with h | h
    · rw [Real.sign_of_neg h]; norm_num
    · rw [Real.sign_of_pos h]; norm_num
  have hkey : L / 2 * (r : ℝ) ^ |g| < Real.sign g * stokesTriangleCharge p q r g := by
    have := mul_lt_mul_of_pos_right hr hR
    rwa [mul_assoc, div_mul_cancel₀ _ hR.ne'] at this
  constructor
  · have h1 : Real.sign g * stokesTriangleCharge p q r g ≤
        |Real.sign g * stokesTriangleCharge p q r g| := le_abs_self _
    rw [abs_mul, habs, one_mul] at h1
    linarith
  · rcases lt_or_gt_of_ne hg with h | h
    · rw [Real.sign_of_neg h] at hkey
      have : stokesTriangleCharge p q r g < 0 := by nlinarith
      nlinarith
    · rw [Real.sign_of_pos h] at hkey
      have : 0 < stokesTriangleCharge p q r g := by nlinarith
      exact mul_pos h this

/-- **No one-prime potential at any nonzero grade.** -/
theorem no_stokes_prime_potential {g : ℝ} (hg : g ≠ 0) :
    ¬∃ a : ℕ → ℝ, ∀ p q : ℕ, p.Prime → q.Prime → p < q →
      routeRCrossPrimeStokesOddCurvature p q g = a p - a q := by
  rintro ⟨a, ha⟩
  obtain ⟨C, hC, hev⟩ := eventually_stokesTriangleCharge_growth (p := 2) (q := 3)
    (by norm_num) (by norm_num) hg
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  obtain ⟨r, hrN, hr⟩ := Nat.exists_infinite_primes (max N 4)
  have h23 := ha 2 3 Nat.prime_two Nat.prime_three (by norm_num)
  have h3r := ha 3 r Nat.prime_three hr (by omega)
  have h2r := ha 2 r Nat.prime_two hr (by omega)
  have hzero : stokesTriangleCharge 2 3 r g = 0 := by
    unfold stokesTriangleCharge
    rw [h23, h3r, h2r]
    ring
  have := (hN r (le_of_max_le_left hrN)).2
  rw [hzero, mul_zero] at this
  exact lt_irrefl 0 this

/-- **Scale-dependent sign change.** At every sufficiently small positive grade the fixed
triangle `(3,5,7)` has negative charge, while `(3,5,r)` has positive charge for all large `r`. -/
theorem stokes_triangle_sign_change :
    ∀ᶠ g : ℝ in 𝓝[>] 0,
      stokesTriangleCharge 3 5 7 g < 0 ∧ ∀ᶠ r : ℕ in atTop, 0 < stokesTriangleCharge 3 5 r g := by
  have hsub : Set.Ioi (0 : ℝ) ⊆ ({0} : Set ℝ)ᶜ := fun x hx => ne_of_gt hx
  have hopp := stokes_triangle_357_sign_opposite
  have hopp' : ∀ᶠ g : ℝ in 𝓝[>] 0,
      g * (routeRCrossPrimeStokesOddCurvature 3 5 g +
        routeRCrossPrimeStokesOddCurvature 5 7 g -
        routeRCrossPrimeStokesOddCurvature 3 7 g) < 0 :=
    nhdsWithin_mono 0 hsub hopp
  filter_upwards [hopp', self_mem_nhdsWithin] with g hg hgpos
  have hgpos' : 0 < g := hgpos
  refine ⟨?_, ?_⟩
  · unfold stokesTriangleCharge
    by_contra hcon
    have := mul_nonneg hgpos'.le (not_lt.mp hcon)
    linarith
  · obtain ⟨C, -, hev⟩ := eventually_stokesTriangleCharge_growth (p := 3) (q := 5)
      (by norm_num) (by norm_num) hgpos'.ne'
    filter_upwards [hev] with r hr
    exact pos_of_mul_pos_right hr.2 hgpos'.le

/-- **Compensation law.** A pair correction `B` turning the curvature into a potential
difference on a triangle has triangle sum `-Ω`. -/
theorem stokes_correction_triangle (B : ℕ → ℕ → ℝ) (a : ℕ → ℝ) (p q r : ℕ) (g : ℝ)
    (hpq : routeRCrossPrimeStokesOddCurvature p q g + B p q = a p - a q)
    (hqr : routeRCrossPrimeStokesOddCurvature q r g + B q r = a q - a r)
    (hpr : routeRCrossPrimeStokesOddCurvature p r g + B p r = a p - a r) :
    B p q + B q r - B p r = -stokesTriangleCharge p q r g := by
  unfold stokesTriangleCharge
  linarith

/-- **Necessary correction size.** If `c + B` is a one-prime coboundary on all prime pairs
`p<q<r`, then for fixed `p<q` and `g ≠ 0` there are `C > 0` and `R` with
`C r^|g| ≤ |B_pr| + |B_qr|` for every prime `r > R`. -/
theorem stokes_correction_row_growth {p q : ℕ} (hp : 1 < p) (hpq : p < q) {g : ℝ} (hg : g ≠ 0)
    (B : ℕ → ℕ → ℝ) (a : ℕ → ℝ)
    (hcob : ∀ r : ℕ, r.Prime → q < r →
      routeRCrossPrimeStokesOddCurvature p q g + B p q = a p - a q ∧
      routeRCrossPrimeStokesOddCurvature q r g + B q r = a q - a r ∧
      routeRCrossPrimeStokesOddCurvature p r g + B p r = a p - a r) :
    ∃ C : ℝ, 0 < C ∧ ∃ R : ℕ, ∀ r : ℕ, r.Prime → R < r →
      C * (r : ℝ) ^ |g| ≤ |B p r| + |B q r| := by
  obtain ⟨C, hC, hev⟩ := eventually_stokesTriangleCharge_growth hp hpq hg
  have ha : 0 < |g| := abs_pos.mpr hg
  have hbig : ∀ᶠ r : ℕ in atTop, 2 * |B p q| ≤ C * (r : ℝ) ^ |g| := by
    have := (tendsto_rpow_nat_atTop ha).const_mul_atTop hC
    exact this.eventually_ge_atTop _
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hev.and hbig)
  refine ⟨C / 2, half_pos hC, max N q, fun r hr hrR => ?_⟩
  obtain ⟨hgrow, -⟩ := (hN r (le_of_lt (lt_of_le_of_lt (le_max_left _ _) hrR))).1
  have hsmall := (hN r (le_of_lt (lt_of_le_of_lt (le_max_left _ _) hrR))).2
  obtain ⟨h1, h2, h3⟩ := hcob r hr (lt_of_le_of_lt (le_max_right _ _) hrR)
  have htri := stokes_correction_triangle B a p q r g h1 h2 h3
  have hdiff : |stokesTriangleCharge p q r g| ≤ |B p q| + (|B p r| + |B q r|) := by
    have : stokesTriangleCharge p q r g = -(B p q) + (B p r - B q r) := by linarith
    rw [this]
    calc |-(B p q) + (B p r - B q r)| ≤ |-(B p q)| + |B p r - B q r| := abs_add_le _ _
      _ ≤ |B p q| + (|B p r| + |B q r|) := by
        rw [abs_neg]
        gcongr
        exact abs_sub _ _
  nlinarith

/-- **The corrected prime rows are not reciprocal-Euler square summable.** Under the
coboundary hypothesis, the two rows `r ↦ B_pr` and `r ↦ B_qr` are not both square-summable
against the weight `1/r` over the primes. -/
theorem stokes_correction_rows_not_hilbert {p q : ℕ} (hp : 1 < p) (hpq : p < q) {g : ℝ}
    (hg : g ≠ 0) (B : ℕ → ℕ → ℝ) (a : ℕ → ℝ)
    (hcob : ∀ r : ℕ, r.Prime → q < r →
      routeRCrossPrimeStokesOddCurvature p q g + B p q = a p - a q ∧
      routeRCrossPrimeStokesOddCurvature q r g + B q r = a q - a r ∧
      routeRCrossPrimeStokesOddCurvature p r g + B p r = a p - a r) :
    ¬ (Summable (fun r : Nat.Primes => B p r ^ 2 / (r : ℝ)) ∧
        Summable (fun r : Nat.Primes => B q r ^ 2 / (r : ℝ))) := by
  rintro ⟨hsp, hsq⟩
  obtain ⟨C, hC, R, hR⟩ := stokes_correction_row_growth hp hpq hg B a hcob
  apply Nat.Primes.not_summable_one_div
  have hsum : Summable (fun r : Nat.Primes => (2 / C ^ 2) * (B p r ^ 2 / (r : ℝ) +
      B q r ^ 2 / (r : ℝ))) := (hsp.add hsq).mul_left _
  refine Summable.of_norm_bounded_eventually hsum ?_
  have hfin : {r : Nat.Primes | (r : ℕ) ≤ R}.Finite := by
    refine (Set.finite_le_nat R).preimage ?_
    exact Subtype.val_injective.injOn
  filter_upwards [hfin.compl_mem_cofinite] with r hr
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at hr
  have hr0 : (0 : ℝ) < (r : ℕ) := by exact_mod_cast r.property.pos
  have hr1 : (1 : ℝ) ≤ (r : ℕ) := by exact_mod_cast r.property.one_lt.le
  have hgrow := hR r r.property hr
  have hpow : 1 ≤ ((r : ℕ) : ℝ) ^ |g| := Real.one_le_rpow hr1 (abs_nonneg g)
  have hC1 : C ≤ |B p r| + |B q r| := by nlinarith
  have hsq : C ^ 2 ≤ 2 * (B p r ^ 2 + B q r ^ 2) := by
    have h0 : 0 ≤ |B p r| + |B q r| := by positivity
    have := pow_le_pow_left₀ hC.le hC1 2
    nlinarith [sq_abs (B p r), sq_abs (B q r), sq_nonneg (|B p r| - |B q r|)]
  have key : 1 ≤ (2 / C ^ 2) * (B p r ^ 2 + B q r ^ 2) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    linarith
  calc ‖(1 : ℝ) / ((r : ℕ) : ℝ)‖ = 1 / ((r : ℕ) : ℝ) := by
        rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
    _ ≤ ((2 / C ^ 2) * (B p r ^ 2 + B q r ^ 2)) / ((r : ℕ) : ℝ) :=
        div_le_div_of_nonneg_right key hr0.le
    _ = _ := by ring

end

end RHTower
