import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheGevreyWindow

/-!
# An explicit Gevrey profile

The Gevrey window (`TheGevreyWindow`) needs a profile with explicit Gevrey bounds. The glue
function `E(x) = e^{−1/x}` (`x > 0`), `E = 0` (`x ≤ 0`), is of Gevrey class `2`:

* **Its derivatives** (`iteratedDeriv_expNegInvGlue`) are `E^{(n)}(x) = P_n(1/x) E(x)` with
  `P_0 = 1`, `P_{n+1} = X²(P_n − P_n′)`.
* **The weighted coefficient norm** `W(P) = Σ_j |c_j| j!` bounds `sup_{t ≥ 0} |P(t)| e^{−t}`, since
  `t^j e^{−t} ≤ j!` (`abs_eval_mul_exp_le`), and grows by at most `2D²` under `P ↦ X²(P − P′)` for
  `deg P < D` (`wnorm_step_le`). Hence `|E^{(n)}| ≤ 8^n (n!)²`
  (`abs_iteratedDeriv_expNegInvGlue_le`).
* **The profile** `φ_G(x) = c E(1 + x) E(1 − x)` (`gevreyProfile`) is smooth, vanishes off
  `[−1, 1]`,
  has `∫ φ_G = 1` and `‖φ_G^{(q)}‖₁ ≤ 2c 16^q (q!)²`.
* **The log-log overlap law for `φ_G`** (`riemannHypothesis_iff_gevreyProfile_nonneg_loglog`): for
  every `α > 2`, RH holds iff Weil's form is eventually nonnegative on the atomic families of
  `φ_G` of width `(log log N)^α/N`.
-/

noncomputable section

open MeasureTheory Set Filter Topology RHTower Polynomial
open scoped Real ContDiff

namespace GaloisForLFunctions.SpacingScaleHarmonicAnalysis

open ArithmeticElectrostatics

/-! ### The derivatives of the glue function -/

/-- `P_0 = 1`, `P_{n+1} = X²(P_n − P_n′)`: `E^{(n)}(x) = P_n(1/x) E(x)`. -/
def gluePoly : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => X ^ 2 * (gluePoly n - derivative (gluePoly n))

theorem iteratedDeriv_expNegInvGlue (n : ℕ) :
    iteratedDeriv n expNegInvGlue = fun x => (gluePoly n).eval x⁻¹ * expNegInvGlue x := by
  induction n with
  | zero => funext x; simp [gluePoly]
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    exact (expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul (gluePoly n) x).deriv

theorem natDegree_gluePoly_lt (n : ℕ) : (gluePoly n).natDegree < 2 * n + 1 := by
  induction n with
  | zero => simp [gluePoly]
  | succ n ih =>
    simp only [gluePoly]
    have h1 := natDegree_mul_le (p := (X : ℝ[X]) ^ 2) (q := gluePoly n - derivative (gluePoly n))
    have h2 : ((X : ℝ[X]) ^ 2).natDegree ≤ 2 := natDegree_X_pow_le 2
    have h3 := natDegree_sub_le (gluePoly n) (derivative (gluePoly n))
    have h4 := natDegree_derivative_le (gluePoly n)
    omega

/-! ### The weighted coefficient norm -/

/-- `W_D(P) = Σ_{j<D} |c_j| j!`. -/
def wnorm (D : ℕ) (p : ℝ[X]) : ℝ := ∑ j ∈ Finset.range D, |p.coeff j| * (j.factorial : ℝ)

theorem wnorm_nonneg (D : ℕ) (p : ℝ[X]) : 0 ≤ wnorm D p :=
  Finset.sum_nonneg fun j _ => by positivity

/-- `|P(t)| e^{−t} ≤ W_D(P)` for `t ≥ 0` and `deg P < D`: `t^j e^{−t} ≤ j!`. -/
theorem abs_eval_mul_exp_le {p : ℝ[X]} {D : ℕ} (hD : p.natDegree < D) {t : ℝ} (ht : 0 ≤ t) :
    |p.eval t| * Real.exp (-t) ≤ wnorm D p := by
  rw [eval_eq_sum_range' hD, wnorm]
  refine (mul_le_mul_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (Real.exp_pos _).le).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [abs_mul, abs_pow, abs_of_nonneg ht, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  have h := Real.pow_div_factorial_le_exp t ht j
  have hf : (0 : ℝ) < (j.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos j
  rw [div_le_iff₀ hf] at h
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos t)]
  linarith [mul_comm (Real.exp t) (j.factorial : ℝ)]

/-- **One step of the recursion**: `W_{D+2}(X²(P − P′)) ≤ 2D² W_D(P)` for `deg P < D`. -/
theorem wnorm_step_le {p : ℝ[X]} {D : ℕ} (hD : p.natDegree < D) :
    wnorm (D + 2) (X ^ 2 * (p - derivative p)) ≤ 2 * (D : ℝ) ^ 2 * wnorm D p := by
  set c : ℕ → ℝ := fun j => p.coeff j
  have hcD : c D = 0 := coeff_eq_zero_of_natDegree_lt hD
  -- the coefficients of `X²(P − P′)`
  have hq : ∀ j, (X ^ 2 * (p - derivative p)).coeff j =
      if 2 ≤ j then c (j - 2) - c (j - 2 + 1) * ((j - 2 : ℕ) + 1) else 0 := by
    intro j
    rw [coeff_X_pow_mul', coeff_sub, coeff_derivative]
  have hsum : wnorm (D + 2) (X ^ 2 * (p - derivative p)) =
      ∑ i ∈ Finset.range D, |c i - c (i + 1) * ((i : ℝ) + 1)| * ((i + 2).factorial : ℝ) := by
    unfold wnorm
    rw [Finset.sum_range_succ', Finset.sum_range_succ']
    simp only [hq]
    simp
  rw [hsum]
  -- split the two contributions
  have hsplit : ∀ i ∈ Finset.range D, |c i - c (i + 1) * ((i : ℝ) + 1)| * ((i + 2).factorial : ℝ) ≤
      |c i| * ((i + 2).factorial : ℝ) + |c (i + 1)| * ((i : ℝ) + 1) * ((i + 2).factorial : ℝ) := by
    intro i _
    have h := abs_sub (c i) (c (i + 1) * ((i : ℝ) + 1))
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (i : ℝ) + 1)] at h
    have hf : (0 : ℝ) ≤ ((i + 2).factorial : ℝ) := by positivity
    nlinarith
  refine (Finset.sum_le_sum hsplit).trans ?_
  rw [Finset.sum_add_distrib]
  -- reindex the shifted sum
  set g : ℕ → ℝ := fun j => |c j| * (j : ℝ) * ((j + 1).factorial : ℝ)
  have hshift : ∑ i ∈ Finset.range D, |c (i + 1)| * ((i : ℝ) + 1) * ((i + 2).factorial : ℝ) =
      ∑ j ∈ Finset.range D, g j := by
    have h1 : ∑ i ∈ Finset.range D, |c (i + 1)| * ((i : ℝ) + 1) * ((i + 2).factorial : ℝ) =
        ∑ i ∈ Finset.range D, g (i + 1) := Finset.sum_congr rfl fun i _ => by
          simp only [g]; push_cast; ring_nf
    have h2 := Finset.sum_range_succ' g D
    have h3 := Finset.sum_range_succ g D
    have hg0 : g 0 = 0 := by simp [g]
    have hgD : g D = 0 := by simp [g, hcD]
    rw [h1]
    linarith
  rw [hshift, wnorm, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i hi => ?_
  have hiD : (i : ℝ) + 1 ≤ D := by exact_mod_cast Finset.mem_range.mp hi
  have hf1 : ((i + 2).factorial : ℝ) = ((i : ℝ) + 2) * ((i : ℝ) + 1) * (i.factorial : ℝ) := by
    rw [Nat.factorial_succ, Nat.factorial_succ]; push_cast; ring
  have hf2 : ((i + 1).factorial : ℝ) = ((i : ℝ) + 1) * (i.factorial : ℝ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  simp only [g]
  rw [hf1, hf2]
  have hci : 0 ≤ |c i| * (i.factorial : ℝ) := by positivity
  have hkey : ((i : ℝ) + 2) * ((i : ℝ) + 1) + (i : ℝ) * ((i : ℝ) + 1) ≤ 2 * (D : ℝ) ^ 2 := by
    nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hkey hci]

/-- `W_{2n+1}(P_n) ≤ 8^n (n!)²`. -/
theorem wnorm_gluePoly_le (n : ℕ) :
    wnorm (2 * n + 1) (gluePoly n) ≤ 8 ^ n * ((n.factorial : ℝ)) ^ 2 := by
  induction n with
  | zero => simp [wnorm, gluePoly]
  | succ n ih =>
    have h := wnorm_step_le (natDegree_gluePoly_lt n)
    rw [show 2 * n + 1 + 2 = 2 * (n + 1) + 1 by ring] at h
    have hf : ((n + 1).factorial : ℝ) = ((n : ℝ) + 1) * (n.factorial : ℝ) := by
      rw [Nat.factorial_succ]; push_cast; ring
    have hD : (2 : ℝ) * ((2 * n + 1 : ℕ) : ℝ) ^ 2 ≤ 8 * ((n : ℝ) + 1) ^ 2 := by
      push_cast; nlinarith
    simp only [gluePoly]
    refine h.trans ?_
    have h0 := wnorm_nonneg (2 * n + 1) (gluePoly n)
    calc 2 * ((2 * n + 1 : ℕ) : ℝ) ^ 2 * wnorm (2 * n + 1) (gluePoly n)
        ≤ 8 * ((n : ℝ) + 1) ^ 2 * (8 ^ n * (n.factorial : ℝ) ^ 2) :=
          mul_le_mul hD ih h0 (by positivity)
      _ = 8 ^ (n + 1) * ((n + 1).factorial : ℝ) ^ 2 := by rw [hf, pow_succ]; ring

/-- **The glue function is Gevrey of class `2`**: `|E^{(n)}(x)| ≤ 8^n (n!)²`. -/
theorem abs_iteratedDeriv_expNegInvGlue_le (n : ℕ) (x : ℝ) :
    |iteratedDeriv n expNegInvGlue x| ≤ 8 ^ n * ((n.factorial : ℝ)) ^ 2 := by
  rw [iteratedDeriv_expNegInvGlue]
  rcases le_or_gt x 0 with hx | hx
  · simp [expNegInvGlue.zero_of_nonpos hx]
  · have hE : expNegInvGlue x = Real.exp (-x⁻¹) := by simp [expNegInvGlue, not_le.mpr hx]
    show |(gluePoly n).eval x⁻¹ * expNegInvGlue x| ≤ _
    rw [hE, abs_mul, abs_of_pos (Real.exp_pos _)]
    exact (abs_eval_mul_exp_le (natDegree_gluePoly_lt n) (inv_nonneg.mpr hx.le)).trans
      (wnorm_gluePoly_le n)

/-! ### The profile -/

/-- The bump `E(1 + x) E(1 − x)`, positive exactly on `(−1, 1)`. -/
def gevreyBump (x : ℝ) : ℝ := expNegInvGlue (1 + x) * expNegInvGlue (1 - x)

/-- The normalized profile `φ_G = E(1 + x) E(1 − x) / ∫ E(1 + y) E(1 − y) dy`. -/
def gevreyProfile (x : ℝ) : ℝ := (∫ y, gevreyBump y)⁻¹ * gevreyBump x

theorem contDiff_gevreyBump : ContDiff ℝ ∞ gevreyBump :=
  (expNegInvGlue.contDiff.comp (contDiff_const.add contDiff_id)).mul
    (expNegInvGlue.contDiff.comp (contDiff_const.sub contDiff_id))

theorem gevreyBump_vanishesOff : VanishesOff gevreyBump := by
  intro x hx
  unfold gevreyBump
  rcases lt_or_gt_of_ne (show x ≠ 0 by rintro rfl; norm_num at hx) with h | h
  · rw [abs_of_neg h] at hx
    rw [expNegInvGlue.zero_of_nonpos (by linarith), zero_mul]
  · rw [abs_of_pos h] at hx
    rw [expNegInvGlue.zero_of_nonpos (show 1 - x ≤ 0 by linarith), mul_zero]

theorem gevreyBump_nonneg (x : ℝ) : 0 ≤ gevreyBump x :=
  mul_nonneg (expNegInvGlue.nonneg _) (expNegInvGlue.nonneg _)

theorem integral_gevreyBump_pos : 0 < ∫ y, gevreyBump y := by
  have hc : HasCompactSupport gevreyBump := hasCompactSupport_of_vanishes gevreyBump_vanishesOff
  have hint : Integrable gevreyBump :=
    contDiff_gevreyBump.continuous.integrable_of_hasCompactSupport hc
  rw [integral_pos_iff_support_of_nonneg gevreyBump_nonneg hint]
  have hsub : Ioo (-1 : ℝ) 1 ⊆ Function.support gevreyBump := fun x hx => by
    simp only [Function.mem_support]
    exact (mul_pos (expNegInvGlue.pos_of_pos (by linarith [hx.1]))
      (expNegInvGlue.pos_of_pos (by linarith [hx.2]))).ne'
  refine lt_of_lt_of_le ?_ (measure_mono hsub)
  rw [Real.volume_Ioo]
  norm_num

theorem contDiff_gevreyProfile : ContDiff ℝ ∞ gevreyProfile :=
  contDiff_const.mul contDiff_gevreyBump

theorem gevreyProfile_vanishesOff : VanishesOff gevreyProfile := fun x hx => by
  simp [gevreyProfile, gevreyBump_vanishesOff x hx]

theorem integral_gevreyProfile : ∫ x, gevreyProfile x = 1 := by
  unfold gevreyProfile
  rw [integral_const_mul, inv_mul_cancel₀ integral_gevreyBump_pos.ne']

/-- `|φ_G^{(q)}|`: the bump is Gevrey of class `2` with `|(E(1+·)E(1−·))^{(q)}| ≤ 16^q (q!)²`. -/
theorem abs_iteratedDeriv_gevreyBump_le (q : ℕ) (x : ℝ) :
    |iteratedDeriv q gevreyBump x| ≤ 16 ^ q * ((q.factorial : ℝ)) ^ 2 := by
  have hE := (expNegInvGlue.contDiff (n := ⊤) : ContDiff ℝ ∞ expNegInvGlue)
  have h1 : ContDiff ℝ ∞ fun x => expNegInvGlue (1 + x) := hE.comp (contDiff_const.add contDiff_id)
  have h2 : ContDiff ℝ ∞ fun x => expNegInvGlue (1 - x) := hE.comp (contDiff_const.sub contDiff_id)
  have e : gevreyBump = (fun x => expNegInvGlue (1 + x)) * fun x => expNegInvGlue (1 - x) := rfl
  rw [e, iteratedDeriv_mul (contDiffAt_of_smooth h1 q x) (contDiffAt_of_smooth h2 q x)]
  simp only [iteratedDeriv_comp_const_add, iteratedDeriv_comp_const_sub]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hsum : ∑ l ∈ Finset.range (q + 1), (q.choose l : ℝ) = 2 ^ q := by
    exact_mod_cast Nat.sum_range_choose q
  calc ∑ l ∈ Finset.range (q + 1), |(q.choose l : ℝ) * iteratedDeriv l expNegInvGlue (1 + x) *
        ((-1 : ℝ) ^ (q - l) • iteratedDeriv (q - l) expNegInvGlue (1 - x))|
      ≤ ∑ l ∈ Finset.range (q + 1), (q.choose l : ℝ) * (8 ^ q * ((q.factorial : ℝ)) ^ 2) := by
        refine Finset.sum_le_sum fun l hl => ?_
        have hlq : l ≤ q := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
        rw [smul_eq_mul, abs_mul, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
          Nat.abs_cast]
        have a1 := abs_iteratedDeriv_expNegInvGlue_le l (1 + x)
        have a2 := abs_iteratedDeriv_expNegInvGlue_le (q - l) (1 - x)
        have hfac : (l.factorial : ℝ) * ((q - l).factorial : ℝ) ≤ q.factorial := by
          exact_mod_cast Nat.le_of_dvd (Nat.factorial_pos q)
            (Nat.factorial_mul_factorial_dvd_factorial hlq)
        have h8 : (8 : ℝ) ^ l * 8 ^ (q - l) = 8 ^ q := by
          rw [← pow_add, Nat.add_sub_cancel' hlq]
        have hprod : |iteratedDeriv l expNegInvGlue (1 + x)| *
            |iteratedDeriv (q - l) expNegInvGlue (1 - x)| ≤ 8 ^ q * ((q.factorial : ℝ)) ^ 2 := by
          calc _ ≤ (8 ^ l * ((l.factorial : ℝ)) ^ 2) *
                (8 ^ (q - l) * (((q - l).factorial : ℝ)) ^ 2) :=
                mul_le_mul a1 a2 (abs_nonneg _) (by positivity)
            _ = 8 ^ q * ((l.factorial : ℝ) * ((q - l).factorial : ℝ)) ^ 2 := by rw [← h8]; ring
            _ ≤ 8 ^ q * ((q.factorial : ℝ)) ^ 2 :=
                mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hfac 2) (by positivity)
        calc (q.choose l : ℝ) * |iteratedDeriv l expNegInvGlue (1 + x)| *
              |iteratedDeriv (q - l) expNegInvGlue (1 - x)|
            = (q.choose l : ℝ) * (|iteratedDeriv l expNegInvGlue (1 + x)| *
              |iteratedDeriv (q - l) expNegInvGlue (1 - x)|) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left hprod (by positivity)
    _ = 16 ^ q * ((q.factorial : ℝ)) ^ 2 := by
        rw [← Finset.sum_mul, hsum, show (16 : ℝ) ^ q = 2 ^ q * 8 ^ q by
          rw [← mul_pow]; norm_num]
        ring

/-- **The profile is Gevrey of class `2`**: `‖φ_G^{(q)}‖₁ ≤ 2c · 16^q (q!)²`, `c = (∫ bump)⁻¹`. -/
theorem integral_abs_iteratedDeriv_gevreyProfile_le (q : ℕ) :
    ∫ t, |iteratedDeriv q gevreyProfile t| ≤
      2 * (∫ y, gevreyBump y)⁻¹ * 16 ^ q * (q.factorial : ℝ) ^ (2 : ℝ) := by
  set c := (∫ y, gevreyBump y)⁻¹
  have hc : 0 ≤ c := inv_nonneg.mpr integral_gevreyBump_pos.le
  have he : iteratedDeriv q gevreyProfile = fun t => c * iteratedDeriv q gevreyBump t := by
    funext t
    exact iteratedDeriv_const_mul c (contDiffAt_of_smooth contDiff_gevreyBump q t)
  have hvan : ∀ t, t ∉ Icc (-1 : ℝ) 1 → gevreyBump t = 0 := fun t ht =>
    gevreyBump_vanishesOff t (by
      simp only [mem_Icc, not_and_or, not_le] at ht
      rcases ht with h | h
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith)
  have hd : Continuous fun t => c * iteratedDeriv q gevreyBump t :=
    continuous_const.mul (contDiff_gevreyBump.continuous_iteratedDeriv q (natCast_le_infty q))
  have hdR : SupportedIn 1 fun t => c * iteratedDeriv q gevreyBump t := fun t ht => by
    show c * iteratedDeriv q gevreyBump t = 0
    rw [iteratedDeriv_eq_zero_of_vanish hvan q (fun h => by
      have := abs_le.mpr ⟨h.1, h.2⟩; linarith), mul_zero]
  have hb : ∀ t, |c * iteratedDeriv q gevreyBump t| ≤ c * (16 ^ q * ((q.factorial : ℝ)) ^ 2) :=
    fun t => by
      rw [abs_mul, abs_of_nonneg hc]
      exact mul_le_mul_of_nonneg_left (abs_iteratedDeriv_gevreyBump_le q t) hc
  rw [he, Real.rpow_two]
  have := integral_abs_le_of_bound hd (hasCompactSupport_of_vanishes hdR) hb hdR zero_le_one
  linarith

/-! ### The log-log overlap law for the explicit profile -/

/-- **The overlap law for the explicit Gevrey profile**: for every dilation sequence whose overlap
ratio beats `(log log κ_N)²`, RH holds iff for all large `N` Weil's form is nonnegative on every
atomic test of profile `φ_G` and width `1/κ_N`. -/
theorem riemannHypothesis_iff_gevreyProfile_nonneg_of_growth {κ : ℕ → ℝ}
    (hκ : OverlapGrowthGevrey 2 κ) :
    RiemannHypothesis ↔ ∀ᶠ N : ℕ in atTop, ∀ x : ℕ → ℝ,
      0 ≤ weilQuad (atomicTest N x (dilate (κ N) gevreyProfile)) :=
  riemannHypothesis_iff_atomicFamilies_nonneg_of_gevrey contDiff_gevreyProfile
    gevreyProfile_vanishesOff integral_gevreyProfile (by norm_num) (by norm_num)
    integral_abs_iteratedDeriv_gevreyProfile_le hκ

/-- **The log-log overlap law**: for every `α > 2`, RH holds iff for all large `N` Weil's form is
nonnegative on the atomic families of the explicit profile `φ_G` of width `(log log N)^α/N` —
overlap ratio `(log log N)^α`. -/
theorem riemannHypothesis_iff_gevreyProfile_nonneg_loglog {α : ℝ} (hα : 2 < α) :
    RiemannHypothesis ↔ ∀ᶠ N : ℕ in atTop, ∀ x : ℕ → ℝ,
      0 ≤ weilQuad (atomicTest N x (dilate ((N : ℝ) / Real.log (Real.log N) ^ α)
        gevreyProfile)) :=
  riemannHypothesis_iff_gevreyProfile_nonneg_of_growth (overlapGrowthGevrey_loglog (by norm_num) hα)

/-- **The gauge for the explicit profile**: a bounded twist is seen at overlap ratio beyond
`(log log N)²` iff it is not Weil positive. -/
theorem gevreyProfile_atomicFamilies_negative_iff {lam : ℕ → ℝ}
    (hlam : ∀ n, |lam n| ≤ ArithmeticFunction.vonMangoldt n) {κ : ℕ → ℝ}
    (hκ : OverlapGrowthGevrey 2 κ) :
    (∃ᶠ N : ℕ in atTop, ∃ x : ℕ → ℝ,
      weilQuadTw lam (atomicTest N x (dilate (κ N) gevreyProfile)) < 0) ↔
        ¬ WeilPositiveFull lam :=
  atomicFamilies_negative_iff_of_gevrey hlam contDiff_gevreyProfile gevreyProfile_vanishesOff
    integral_gevreyProfile (by norm_num) (by norm_num) integral_abs_iteratedDeriv_gevreyProfile_le
    hκ

end GaloisForLFunctions.SpacingScaleHarmonicAnalysis
