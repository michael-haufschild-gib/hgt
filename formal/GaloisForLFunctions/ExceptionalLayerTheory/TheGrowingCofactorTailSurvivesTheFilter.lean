import GaloisForLFunctions.ExceptionalLayerTheory.TheGrowingGaussianErrorIsHolomorphic
import GaloisForLFunctions.ExceptionalLayerTheory.GaussianFilteredCofactorLocalization
import GaloisForLFunctions.ExceptionalLayerTheory.GaussianGrowingCofactorLocalization

/-!
# Growing filters of the actual complementary cofactor current

Polynomial Gaussian tail moments control the logarithmic half-strip after
an exponential twist. Translating filter roots compensates that twist,
while equal-radius Cauchy estimates preserve every spacing factor.
-/

open Complex Filter Topology

noncomputable section

namespace GaloisForLFunctions.ExceptionalLayerTheory

/-- The Mellin twist of the actual higher-moment complementary cofactor sum. -/
def twistedGaussianHigherVaughanCofactorTail (r : ℕ) (β t : ℝ) (U V W : ℕ)
    (ε z : ℂ) : ℂ :=
  Complex.exp ((((1 / 2 : ℂ) + t * I) - β) * z) *
    gaussianHigherVaughanCofactorTail r (1 / 2) t U V W (ε * Complex.exp (-2 * z))

private theorem higher_cofactor_tail_halfStrip_bounds (r k : ℕ) {α ξ t X : ℝ}
    (hα : 0 < α) (ht : 4 ≤ t) (hlo : 2 * α ≤ ξ) (hhi : ξ ≤ α * t)
    (hX : 2 * Real.exp 1 ≤ X) (hscale : α * X ^ 2 = 2)
    {U W : ℕ} (hU : 1 ≤ U) (hW : 1 ≤ W) (V : ℕ) :
    let p := 3 + 2 * k
    let f := twistedGaussianHigherVaughanCofactorTail r (1 / 2 + (p : ℝ) + 1)
      t U V W ((α : ℂ) - ξ * I)
    DifferentiableOn ℂ f (dampingHalfStrip (1 / (16 * t))) ∧
    ∀ z ∈ dampingHalfStrip (1 / (16 * t)), ‖f z‖ ≤
      (784 * 32 ^ r * ((r + 1).factorial : ℝ) * (k.factorial : ℝ) *
        (2 : ℝ) ^ p * Real.exp 2) * X ^ p / ((U * W : ℕ) : ℝ) ^ (2 * k) := by
  let p := 3 + 2 * k
  let K := 784 * 32 ^ r * ((r + 1).factorial : ℝ) * (k.factorial : ℝ)
  let ε := (α : ℂ) - ξ * I
  have ht0 : 0 < t := by linarith only [ht]
  have hX0 : 0 < X := (by positivity : 0 < 2 * Real.exp 1).trans_le hX
  have hradius : 1 / (16 * t) ≤ 1 :=
    (div_le_iff₀ (by positivity)).mpr (by linarith only [ht])
  have him (z : ℂ) (hz : z ∈ dampingHalfStrip (1 / (16 * t))) : t * |z.im| ≤ 1 / 16 := by
    have hh := mul_le_mul_of_nonneg_left hz.2.le ht0.le
    have he : t * (1 / (16 * t)) = 1 / 16 := by field_simp
    exact hh.trans_eq he
  have hgeom (z : ℂ) (hz : z ∈ dampingHalfStrip (1 / (16 * t))) :=
    exists_damping_rotated_scale hα ht hlo hhi (him z hz) hX0 hscale
  refine ⟨?_, ?_⟩
  · intro z hz
    have hd := differentiableAt_gaussianHigherVaughanCofactorTail r
      (by norm_num : (0 : ℝ) ≤ 1 / 2) t U V W (hgeom z hz).1
    have he : DifferentiableAt ℂ (fun w : ℂ => ε * Complex.exp (-2 * w)) z := by fun_prop
    have hw : DifferentiableAt ℂ (fun w : ℂ =>
        Complex.exp ((((1 / 2 : ℂ) + t * I) - ((1 / 2 + (p : ℝ) + 1 : ℝ) : ℂ)) * w)) z := by fun_prop
    exact (hw.mul (hd.comp z he)).differentiableWithinAt
  · intro z hz
    obtain ⟨hε, hεlo, hεhi, Y, hY, hscaleY, hYlo⟩ := hgeom z hz
    have hs : -1 ≤ z.re := by linarith only [hz.1, hradius]
    have hYhi := cofactor_rotated_scale_upper hα ht hlo hhi (him z hz) hX0 hscale hY hscaleY
    have hY1 : 1 ≤ Y := by
      have hex : 1 ≤ Real.exp 1 * Real.exp z.re := by
        rw [← Real.exp_add]
        exact Real.one_le_exp (by linarith only [hs])
      have hh := mul_le_mul_of_nonneg_right hX (Real.exp_pos z.re).le
      nlinarith only [hex, hh, hYlo]
    have hsector : ‖ε * Complex.exp (-2 * z)‖ ≤
        4 * (ε * Complex.exp (-2 * z)).re * t := by
      have hh := Complex.norm_le_abs_re_add_abs_im (ε * Complex.exp (-2 * z))
      rw [abs_of_pos hε, abs_of_nonpos
        (by linarith only [hεlo, hε] : (ε * Complex.exp (-2 * z)).im ≤ 0)] at hh
      have hm := mul_le_mul_of_nonneg_left ht hε.le
      nlinarith only [hh, hεhi, hm, hε]
    have hE := norm_gaussianHigherVaughanCofactorTail_le_moment r k
      (by norm_num : (0 : ℝ) ≤ 1 / 2) ht0 hε hsector hY1 hscaleY hU hW V
    have hphase : ((((1 / 2 : ℂ) + t * I) -
        ((1 / 2 + (p : ℝ) + 1 : ℝ) : ℂ)) * z).re =
        -((p : ℝ) + 1) * z.re - t * z.im := by
      norm_num [Complex.mul_re, Complex.mul_im] <;> ring_nf <;> simp
    have hb : -z.re - t * z.im ≤ 2 := by
      have hh := mul_le_mul_of_nonneg_left (neg_le_abs z.im) ht0.le
      have hi := him z hz
      linarith only [hs, hh, hi]
    change ‖twistedGaussianHigherVaughanCofactorTail r
      (1 / 2 + (p : ℝ) + 1) t U V W ε z‖ ≤ _
    unfold twistedGaussianHigherVaughanCofactorTail
    rw [norm_mul, Complex.norm_exp, hphase]
    calc
      _ ≤ Real.exp (-((p : ℝ) + 1) * z.re - t * z.im) *
          (K * (2 * X * Real.exp z.re) ^ p / ((U * W : ℕ) : ℝ) ^ (2 * k)) := by
        apply mul_le_mul_of_nonneg_left (hE.trans ?_) (Real.exp_pos _).le
        dsimp only [K, p]
        gcongr
      _ = (K * 2 ^ p * X ^ p / ((U * W : ℕ) : ℝ) ^ (2 * k)) *
          Real.exp (-z.re - t * z.im) := by
        rw [mul_pow, mul_pow, ← Real.exp_nat_mul]
        have he : -z.re - t * z.im =
            (-((p : ℝ) + 1) * z.re - t * z.im) + (p : ℝ) * z.re := by ring
        rw [he, Real.exp_add]
        ring
      _ ≤ (K * 2 ^ p * X ^ p / ((U * W : ℕ) : ℝ) ^ (2 * k)) * Real.exp 2 :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hb) (by dsimp only [K]; positivity)
      _ = _ := by dsimp only [K, p]; ring

/-- The actual complementary cofactor sum also retains every filter spacing
factor. Translating the roots pays only one additional height exponential. -/
theorem norm_filtered_gaussianHigherVaughanCofactorTail_le_growing (r k : ℕ)
    {β α ξ t X h B κ : ℝ} (hα : 0 < α)
    (ht : max 4 (34 + 2 * Real.exp 1) ≤ t) (hlo : 2 * α ≤ ξ) (hhi : ξ ≤ α * t)
    (hX : 2 * Real.exp 1 ≤ X) (hscale : α * X ^ 2 = 2)
    {U W : ℕ} (hU : 1 ≤ U) (hW : 1 ≤ W) (V : ℕ)
    (hh : 0 ≤ h) (hB : 0 ≤ B)
    (hBt : B + |gaussianCofactorTwist (1 / 2) β k| ≤ t ^ 2)
    (hhB : h * (B + |gaussianCofactorTwist (1 / 2) β k|) ≤ 1)
    (ws : List ℂ) (hws : ∀ ω ∈ ws, ‖ω‖ ≤ B)
    (hdt : (ws.length : ℝ) ≤ t) (hdegree : (ws.length : ℝ) * Real.log t ≤ κ * t) :
    ‖∑ j ∈ Finset.range ((dampingFilterPolynomial h ws).natDegree + 1),
      (dampingFilterPolynomial h ws).coeff j *
        twistedGaussianHigherVaughanCofactorTail r β t U V W ((α : ℂ) - ξ * I)
          ((j : ℂ) * h)‖ ≤
      ((784 * 32 ^ r * ((r + 1).factorial : ℝ) * (k.factorial : ℝ) *
        (2 : ℝ) ^ (3 + 2 * k) * Real.exp 2) *
        X ^ (3 + 2 * k) / ((U * W : ℕ) : ℝ) ^ (2 * k)) *
        h ^ ws.length * Real.exp ((1 + 3 * κ) * t) := by
  let c := gaussianCofactorTwist (1 / 2) β k
  let roots := ws.map (fun ω => ω - (c : ℂ))
  let f := twistedGaussianHigherVaughanCofactorTail r
    (1 / 2 + (3 + 2 * k : ℕ) + 1) t U V W ((α : ℂ) - ξ * I)
  let M := (784 * 32 ^ r * ((r + 1).factorial : ℝ) * (k.factorial : ℝ) *
    (2 : ℝ) ^ (3 + 2 * k) * Real.exp 2) * X ^ (3 + 2 * k) / ((U * W : ℕ) : ℝ) ^ (2 * k)
  have hX0 : 0 < X := (by positivity : 0 < 2 * Real.exp 1).trans_le hX
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  have hroots : ∀ ω ∈ roots, ‖ω‖ ≤ B + |c| := by
    intro ω hω
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hω
    calc
      _ ≤ ‖v‖ + ‖(c : ℂ)‖ := norm_sub_le _ _
      _ ≤ B + |c| := by
        rw [Complex.norm_real, Real.norm_eq_abs]
        exact add_le_add (hws v hv) (le_refl |c|)
  obtain ⟨hf, hb⟩ := higher_cofactor_tail_halfStrip_bounds r k hα
    ((le_max_left _ _).trans ht) hlo hhi hX hscale hU hW V
  have H := norm_dampingFilterPolynomial_sum_le_growing_order hM hh
    (show 0 ≤ B + |c| by positivity) ((le_max_right _ _).trans ht) hBt hhB
    roots hroots (by simpa only [roots, List.length_map] using hdt)
    (by simpa only [roots, List.length_map] using hdegree) hf hb
  have he (z : ℂ) : twistedGaussianHigherVaughanCofactorTail r β t U V W
      ((α : ℂ) - ξ * I) z = Complex.exp ((c : ℂ) * z) * f z := by
    dsimp only [twistedGaussianHigherVaughanCofactorTail, f]
    rw [← mul_assoc, ← Complex.exp_add]
    congr 2
    dsimp only [c, gaussianCofactorTwist]
    push_cast
    ring
  have hsum := cofactor_filter_twist h c ws f
  simp_rw [← he] at hsum
  have hscalar : ‖Complex.exp ((h : ℂ) * c) ^ ws.length‖ ≤ Real.exp t := by
    rw [norm_pow, Complex.norm_exp]
    have hre : ((h : ℂ) * c).re = h * c := by simp
    rw [hre, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have hc : h * c ≤ 1 := by
      have h₁ := mul_le_mul_of_nonneg_left (le_abs_self c) hh
      have h₂ := mul_nonneg hh hB
      change h * (B + |c|) ≤ 1 at hhB
      nlinarith only [h₁, h₂, hhB]
    have hm := mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg ws.length : (0 : ℝ) ≤ ws.length)
    nlinarith only [hm, hdt]
  rw [hsum, norm_mul]
  calc
    _ ≤ Real.exp t * (M * h ^ roots.length * Real.exp (3 * κ * t)) :=
      mul_le_mul hscalar H (norm_nonneg _) (Real.exp_pos _).le
    _ = _ := by
      have hd : roots.length = ws.length := by simp only [roots, List.length_map]
      rw [hd, show (1 + 3 * κ) * t = t + 3 * κ * t by ring, Real.exp_add]
      dsimp only [M]
      ring

/-- A moment of order comparable with height pays every factorial cost
and leaves an arbitrarily strong height power in the cofactor tail. -/
theorem higher_cofactor_tail_strip_constant_le (r k : ℕ) {t X Y : ℝ}
    (ht : 32 ≤ t) (hkt : (k : ℝ) ≤ t) (hrk : 3 * r ≤ k)
    (hX : 0 < X) (hY : X * t ^ 2 ≤ Y) :
    ((784 * 32 ^ r * ((r + 1).factorial : ℝ) * (k.factorial : ℝ) *
      (2 : ℝ) ^ (3 + 2 * k) * Real.exp 2) * X ^ (3 + 2 * k) / Y ^ (2 * k)) ≤
      6272 * Real.exp 2 * X ^ 3 * t ^ 2 / t ^ k := by
  have ht0 : 0 < t := by linarith only [ht]
  have ht1 : 1 ≤ t := by linarith only [ht]
  have hrk' : (r : ℝ) ≤ k := by exact_mod_cast (show r ≤ k by omega)
  have hrt : (r : ℝ) ≤ t := hrk'.trans hkt
  have hf := higher_tail_factorial_le r ht hrt
  have hk : (k.factorial : ℝ) ≤ t ^ k := by
    have hh : (k.factorial : ℝ) ≤ (k : ℝ) ^ k := by
      exact_mod_cast Nat.factorial_le_pow k
    exact hh.trans (pow_le_pow_left₀ (Nat.cast_nonneg _) hkt k)
  have htwo : (2 : ℝ) ^ (3 + 2 * k) ≤ 8 * t ^ k := by
    rw [pow_add, pow_mul]
    norm_num only [show (2 : ℝ) ^ 3 = 8 by norm_num, show (2 : ℝ) ^ 2 = 4 by norm_num]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 4) (by linarith only [ht]) k)
      (by norm_num)
  have horder : t ^ (3 * r + 2 + k + k) ≤ t ^ (3 * k + 2) :=
    pow_le_pow_right₀ ht1 (by omega)
  have hnum : 784 * 32 ^ r * ((r + 1).factorial : ℝ) * (k.factorial : ℝ) *
      (2 : ℝ) ^ (3 + 2 * k) * Real.exp 2 ≤
      6272 * Real.exp 2 * t ^ (3 * k + 2) := by
    calc
      _ = 784 * (32 ^ r * ((r + 1).factorial : ℝ)) * (k.factorial : ℝ) *
          (2 : ℝ) ^ (3 + 2 * k) * Real.exp 2 := by ring
      _ ≤ 784 * t ^ (3 * r + 2) * t ^ k * (8 * t ^ k) * Real.exp 2 := by
        gcongr
      _ = 6272 * Real.exp 2 * t ^ (3 * r + 2 + k + k) := by
        simp only [pow_add]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left horder (by positivity)
  calc
    _ ≤ (6272 * Real.exp 2 * t ^ (3 * k + 2)) * X ^ (3 + 2 * k) /
        (X * t ^ 2) ^ (2 * k) := by gcongr
    _ = _ := by
      rw [show 3 * k + 2 = k + k + k + 2 by omega,
        show 3 + 2 * k = 3 + (k + k) by omega, show 2 * k = k + k by omega]
      simp only [pow_add, mul_pow, pow_mul]
      field_simp
      <;> ring

/-- The half-strip tail bound absorbs the growing filter's exponential cost. -/
theorem higher_cofactor_tail_filter_cost_le (r k : ℕ) {a t Y : ℝ}
    (ha : 0 ≤ a) (ht : 32 ≤ t) (hkt : (k : ℝ) ≤ t) (htk : t / 2 ≤ (k : ℝ))
    (hrk : 3 * r ≤ k) (hlog : 8 * (a + 1) ≤ Real.log t)
    (hY : Real.exp (a * t) * t ^ 2 ≤ Y) :
    (((784 * 32 ^ r * ((r + 1).factorial : ℝ) * (k.factorial : ℝ) *
      (2 : ℝ) ^ (3 + 2 * k) * Real.exp 2) *
      Real.exp (a * t) ^ (3 + 2 * k) / Y ^ (2 * k)) *
      Real.exp ((1 + 3 * (a / 24)) * t)) ≤
      6272 * Real.exp 2 * t ^ 2 * Real.exp (-(a / 8 + 1) * t) := by
  have ht0 : 0 < t := by linarith only [ht]
  have hlog0 : 0 ≤ Real.log t := by linarith only [hlog, ha]
  have hkl : 4 * (a + 1) * t ≤ (k : ℝ) * Real.log t := by
    have hh := mul_le_mul htk hlog (by positivity : (0 : ℝ) ≤ 8 * (a + 1))
      (Nat.cast_nonneg k)
    nlinarith only [hh]
  have he : 3 * (a * t) + (1 + 3 * (a / 24)) * t -
      (k : ℝ) * Real.log t ≤ -(a / 8 + 1) * t := by
    nlinarith only [hkl, mul_nonneg ha ht0.le, ht0]
  have hp : t ^ k = Real.exp ((k : ℝ) * Real.log t) := by
    rw [Real.exp_nat_mul, Real.exp_log ht0]
  calc
    _ ≤ (6272 * Real.exp 2 * Real.exp (a * t) ^ 3 * t ^ 2 / t ^ k) *
        Real.exp ((1 + 3 * (a / 24)) * t) :=
      mul_le_mul_of_nonneg_right
        (higher_cofactor_tail_strip_constant_le r k ht hkt hrk (Real.exp_pos _) hY)
        (Real.exp_pos _).le
    _ = (6272 * Real.exp 2 * t ^ 2) *
        Real.exp (3 * (a * t) + (1 + 3 * (a / 24)) * t - (k : ℝ) * Real.log t) := by
      have he3 : Real.exp (3 * (a * t)) = Real.exp (a * t) ^ 3 := by
        rw [show 3 * (a * t) = a * t + a * t + a * t by ring,
          Real.exp_add, Real.exp_add]
        ring
      rw [hp, Real.exp_sub, Real.exp_add, he3]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (by positivity)

/-- With a polynomial cofactor cutoff and moment order `floor t`, the actual
discarded cofactor current remains exponentially small under growing filters. -/
theorem eventually_filtered_gaussianHigherVaughanCofactorTail_decay {a β : ℝ}
    (ha : 0 < a) :
    ∀ᶠ t : ℝ in atTop, ∀ α ξ h B : ℝ, 0 < α → 2 * α ≤ ξ → ξ ≤ α * t →
      α * Real.exp (a * t) ^ 2 = 2 → 0 ≤ h → 0 ≤ B →
      B + |gaussianCofactorTwist (1 / 2) β ⌊t⌋₊| ≤ t ^ 2 →
      h * (B + |gaussianCofactorTwist (1 / 2) β ⌊t⌋₊|) ≤ 1 →
      ∀ ws : List ℂ, (∀ ω ∈ ws, ‖ω‖ ≤ B) →
        (ws.length : ℝ) * Real.log t ≤ (a / 24) * t →
        ‖∑ j ∈ Finset.range ((dampingFilterPolynomial h ws).natDegree + 1),
          (dampingFilterPolynomial h ws).coeff j *
            twistedGaussianHigherVaughanCofactorTail (gaussianGrowingMomentOrder (a / 64) t)
              β t (gaussianGrowingLongCutoff a 68 t) ⌊t⌋₊ (gaussianGrowingCofactorCutoff 68 t)
                ((α : ℂ) - ξ * I) ((j : ℂ) * h)‖ ≤
          h ^ ws.length * Real.exp (-(a / 8) * t) := by
  have hp : Tendsto (fun t : ℝ => t ^ 2 * Real.exp (-t)) atTop (𝓝 0) := by
    simpa using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (2 : ℝ) 1 zero_lt_one
  have hp' := hp.const_mul (6272 * Real.exp 2)
  simp only [mul_zero] at hp'
  filter_upwards [eventually_gaussianGrowingMomentOrder_bounds (by positivity : 0 < a / 64),
    eventually_gaussianGrowingLongCutoff_bounds ha 68,
    eventually_gaussianGrowingCofactorCutoff_bounds ha 68,
    eventually_ge_atTop (max 32 (34 + 2 * Real.exp 1)),
    eventually_ge_atTop ((2 * Real.exp 1) / a),
    Real.tendsto_log_atTop.eventually
      (eventually_ge_atTop (8 * (a + 1) + 6 * (a / 64) + a / 24 + 1)),
    hp'.eventually_lt_const zero_lt_one]
    with t hr hcut hco ht htX hlog hsmall α ξ h B hα hlo hhi hscale hh hB hBt hhB ws hws hdegree
  have ht32 : 32 ≤ t := (le_max_left _ _).trans ht
  have ht0 : 0 < t := by linarith only [ht32]
  have hlog1 : 1 ≤ Real.log t := by linarith only [hlog, ha]
  have hlog0 : 0 < Real.log t := zero_lt_one.trans_le hlog1
  have hkt : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le ht0.le
  have htk : t / 2 ≤ (⌊t⌋₊ : ℝ) := by
    have hf := Nat.lt_floor_add_one t
    linarith only [hf, ht32]
  have hr6 : 6 * (gaussianGrowingMomentOrder (a / 64) t : ℝ) ≤ t := by
    have hm := mul_le_mul_of_nonneg_left
      (show 6 * (a / 64) ≤ Real.log t by linarith only [hlog, ha])
      (Nat.cast_nonneg (gaussianGrowingMomentOrder (a / 64) t) : (0 : ℝ) ≤ _)
    by_contra hfail
    have hpos := mul_pos (show 0 < a / 64 by positivity)
      (sub_pos.mpr (lt_of_not_ge hfail))
    nlinarith only [hm, hr.2.2.2, hpos]
  have hrk : 3 * gaussianGrowingMomentOrder (a / 64) t ≤ ⌊t⌋₊ := by
    have hh : 3 * (gaussianGrowingMomentOrder (a / 64) t : ℝ) ≤ (⌊t⌋₊ : ℝ) := by
      linarith only [hr6, htk]
    exact_mod_cast hh
  have hW : 1 ≤ gaussianGrowingCofactorCutoff 68 t := by
    apply Nat.one_le_iff_ne_zero.mpr
    intro hw
    have hc := hco.1
    rw [hw, mul_zero, Nat.cast_zero] at hc
    exact (not_le_of_gt (mul_pos (Real.exp_pos _) (sq_pos_of_pos ht0))) hc
  have hX : 2 * Real.exp 1 ≤ Real.exp (a * t) := by
    have hh := (div_le_iff₀ ha).mp htX
    have he := Real.add_one_le_exp (a * t)
    nlinarith only [hh, he]
  have hdt : (ws.length : ℝ) ≤ t := by
    have hm := mul_le_mul_of_nonneg_left
      (show a / 24 ≤ Real.log t by linarith only [hlog, ha]) ht0.le
    nlinarith only [hdegree, hm, hlog0]
  have H := norm_filtered_gaussianHigherVaughanCofactorTail_le_growing
    (gaussianGrowingMomentOrder (a / 64) t) ⌊t⌋₊ hα
    (max_le (by linarith only [ht32]) ((le_max_right _ _).trans ht))
    hlo hhi hX hscale hcut.1 hW ⌊t⌋₊ hh hB hBt hhB ws hws hdt hdegree
  have HC := higher_cofactor_tail_filter_cost_le
    (gaussianGrowingMomentOrder (a / 64) t) ⌊t⌋₊ ha.le ht32 hkt htk hrk
    (by linarith only [hlog, ha]) hco.1
  apply H.trans
  calc
    _ = _ * Real.exp ((1 + 3 * (a / 24)) * t) * h ^ ws.length := by ring
    _ ≤ (6272 * Real.exp 2 * t ^ 2 * Real.exp (-(a / 8 + 1) * t)) * h ^ ws.length :=
      mul_le_mul_of_nonneg_right HC (pow_nonneg hh _)
    _ = ((6272 * Real.exp 2) * (t ^ 2 * Real.exp (-t))) *
        (h ^ ws.length * Real.exp (-(a / 8) * t)) := by
      rw [show -(a / 8 + 1) * t = -t + -(a / 8) * t by ring, Real.exp_add]
      ring
    _ ≤ 1 * (h ^ ws.length * Real.exp (-(a / 8) * t)) :=
      mul_le_mul_of_nonneg_right hsmall.le (by positivity)
    _ = _ := one_mul _

end GaloisForLFunctions.ExceptionalLayerTheory
