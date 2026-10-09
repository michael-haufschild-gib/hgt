import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Topology.Order.IntermediateValue

/-!
# The first- and second-derivative tests for oscillatory integrals

For a `C¹` amplitude `g` and a real phase `Θ` with **nondecreasing** derivative, `Θ'' ≥ 0`,
whose derivative stays away from zero, `|Θ'| ≥ λ > 0` on `[a, b]`,

`‖∫_a^b g e^{iΘ}‖ ≤ (‖g(a)‖ + ‖g(b)‖ + ∫_a^b ‖g'‖ + sup ‖g‖) / λ`

(`norm_integral_mul_exp_le_of_monotone_phase`).  The proof is one integration by parts against
`e^{iΘ} = (e^{iΘ})'/(iΘ')`.  Monotonicity of `Θ'` is what makes the bound independent of the length
of `[a, b]` and of the size of `Θ''`: the transferred term `∫ ‖g‖ Θ''/Θ'²` is at most
`sup ‖g‖ · (1/Θ'(a) − 1/Θ'(b))`, and the two reciprocals have the same sign.

If instead `|Θ'(x)| ≥ μ|x − c|` around a possible stationary point `c`, removing the window
`|x − c| < δ` and applying the first test on each side gives

`‖∫_a^b g e^{iΘ}‖ ≤ 2δ sup ‖g‖ + (6 sup ‖g‖ + 2∫_a^b ‖g'‖)/(μδ)`

(`norm_integral_mul_exp_le_of_stationary`).  With `δ = μ^{-1/2}` this is the second-derivative
test `O(μ^{-1/2})`.
-/

open Set MeasureTheory intervalIntegral

namespace GaloisForLFunctions.HTGeometry

noncomputable section

private theorem norm_exp_ofReal_mul_I (θ : ℝ) : ‖Complex.exp ((θ : ℂ) * Complex.I)‖ = 1 := by
  rw [Complex.norm_exp_ofReal_mul_I]

/-- A continuous function on `[a, b]` that never vanishes has the same sign at both ends. -/
private theorem same_sign_of_ne_zero {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b)) (hne : ∀ x ∈ Icc a b, f x ≠ 0) :
    (0 < f a ∧ 0 < f b) ∨ (f a < 0 ∧ f b < 0) := by
  have ha := hne a ⟨le_rfl, hab⟩
  have hb := hne b ⟨hab, le_rfl⟩
  rcases lt_or_gt_of_ne ha with ha' | ha' <;> rcases lt_or_gt_of_ne hb with hb' | hb'
  · exact Or.inr ⟨ha', hb'⟩
  · obtain ⟨c, hc, hc0⟩ := intermediate_value_Icc hab hf ⟨ha'.le, hb'.le⟩
    exact absurd hc0 (hne c hc)
  · obtain ⟨c, hc, hc0⟩ := intermediate_value_Icc' hab hf ⟨hb'.le, ha'.le⟩
    exact absurd hc0 (hne c hc)
  · exact Or.inl ⟨ha', hb'⟩

/-- `|1/p − 1/q| ≤ 1/λ` for two reals of the same sign, both of modulus at least `λ`. -/
private theorem abs_inv_sub_inv_le {p q lam : ℝ} (hlam : 0 < lam) (hp : lam ≤ |p|) (hq : lam ≤ |q|)
    (hs : (0 < p ∧ 0 < q) ∨ (p < 0 ∧ q < 0)) : |1 / p - 1 / q| ≤ 1 / lam := by
  rcases hs with ⟨hp0, hq0⟩ | ⟨hp0, hq0⟩
  · rw [abs_of_pos hp0] at hp
    rw [abs_of_pos hq0] at hq
    have h1 : 1 / p ≤ 1 / lam := one_div_le_one_div_of_le hlam hp
    have h2 : 1 / q ≤ 1 / lam := one_div_le_one_div_of_le hlam hq
    have h3 : 0 < 1 / p := by positivity
    have h4 : 0 < 1 / q := by positivity
    rw [abs_le]; constructor <;> linarith
  · rw [abs_of_neg hp0] at hp
    rw [abs_of_neg hq0] at hq
    have h1 : 1 / -p ≤ 1 / lam := one_div_le_one_div_of_le hlam hp
    have h2 : 1 / -q ≤ 1 / lam := one_div_le_one_div_of_le hlam hq
    have h3 : 0 < 1 / -p := by have : 0 < -p := by linarith
                               positivity
    have h4 : 0 < 1 / -q := by have : 0 < -q := by linarith
                               positivity
    rw [one_div_neg_eq_neg_one_div] at h1 h2 h3 h4
    rw [abs_le]; constructor <;> linarith

/-- **The first-derivative test for a monotone phase derivative.**  For a `C¹` amplitude `g` and a
`C²` real phase `Θ` with `Θ'' ≥ 0` and `|Θ'| ≥ λ > 0` on `[a, b]`,
`‖∫_a^b g e^{iΘ}‖ ≤ (‖g(a)‖ + ‖g(b)‖ + V + G)/λ` whenever `‖g‖ ≤ G` on `[a, b]` and
`∫_a^b ‖g'‖ ≤ V`. -/
theorem norm_integral_mul_exp_le_of_monotone_phase {g g' : ℝ → ℂ} {Θ Θ' Θ'' : ℝ → ℝ}
    {a b lam G V : ℝ} (hab : a ≤ b) (hlam : 0 < lam)
    (hg : ∀ x ∈ Icc a b, HasDerivAt g (g' x) x) (hg' : ContinuousOn g' (Icc a b))
    (hΘ : ∀ x ∈ Icc a b, HasDerivAt Θ (Θ' x) x)
    (hΘ' : ∀ x ∈ Icc a b, HasDerivAt Θ' (Θ'' x) x) (hΘ'' : ContinuousOn Θ'' (Icc a b))
    (hpos : ∀ x ∈ Icc a b, 0 ≤ Θ'' x) (hlow : ∀ x ∈ Icc a b, lam ≤ |Θ' x|)
    (hG : ∀ x ∈ Icc a b, ‖g x‖ ≤ G) (hV : ∫ x in a..b, ‖g' x‖ ≤ V) :
    ‖∫ x in a..b, g x * Complex.exp ((Θ x : ℂ) * Complex.I)‖ ≤
      (‖g a‖ + ‖g b‖ + V + G) / lam := by
  have huI : uIcc a b = Icc a b := uIcc_of_le hab
  have hamem : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hbmem : b ∈ Icc a b := ⟨hab, le_rfl⟩
  have hG0 : 0 ≤ G := le_trans (norm_nonneg _) (hG a hamem)
  have hΘ'pos : ∀ x ∈ Icc a b, 0 < |Θ' x| := fun x hx => lt_of_lt_of_le hlam (hlow x hx)
  have hΘ'ne : ∀ x ∈ Icc a b, Θ' x ≠ 0 := fun x hx => abs_pos.1 (hΘ'pos x hx)
  have hDne : ∀ x ∈ Icc a b, ((Θ' x : ℂ) * Complex.I) ≠ 0 := fun x hx =>
    mul_ne_zero (Complex.ofReal_ne_zero.2 (hΘ'ne x hx)) Complex.I_ne_zero
  have hΘ'c : ContinuousOn Θ' (Icc a b) := fun x hx => (hΘ' x hx).continuousAt.continuousWithinAt
  have hΘc : ContinuousOn Θ (Icc a b) := fun x hx => (hΘ x hx).continuousAt.continuousWithinAt
  have hgc : ContinuousOn g (Icc a b) := fun x hx => (hg x hx).continuousAt.continuousWithinAt
  have hD : ∀ x ∈ Icc a b, HasDerivAt (fun y => (Θ' y : ℂ) * Complex.I)
      ((Θ'' x : ℂ) * Complex.I) x := fun x hx => (hΘ' x hx).ofReal_comp.mul_const _
  -- `u = g/(iΘ')`, `v = e^{iΘ}`
  have hu : ∀ x ∈ uIcc a b, HasDerivAt (fun y => g y / ((Θ' y : ℂ) * Complex.I))
      ((g' x * ((Θ' x : ℂ) * Complex.I) - g x * ((Θ'' x : ℂ) * Complex.I)) /
        ((Θ' x : ℂ) * Complex.I) ^ 2) x := by
    rw [huI]; intro x hx
    exact (hg x hx).div (hD x hx) (hDne x hx)
  have hv : ∀ x ∈ uIcc a b, HasDerivAt (fun y => Complex.exp ((Θ y : ℂ) * Complex.I))
      (Complex.exp ((Θ x : ℂ) * Complex.I) * ((Θ' x : ℂ) * Complex.I)) x := by
    rw [huI]; intro x hx
    exact ((hΘ x hx).ofReal_comp.mul_const Complex.I).cexp
  have hDc : ContinuousOn (fun y => (Θ' y : ℂ) * Complex.I) (Icc a b) :=
    (Complex.continuous_ofReal.comp_continuousOn hΘ'c).mul continuousOn_const
  have hu'c : ContinuousOn (fun x => (g' x * ((Θ' x : ℂ) * Complex.I) -
      g x * ((Θ'' x : ℂ) * Complex.I)) / ((Θ' x : ℂ) * Complex.I) ^ 2) (Icc a b) :=
    ((hg'.mul hDc).sub (hgc.mul ((Complex.continuous_ofReal.comp_continuousOn hΘ'').mul
      continuousOn_const))).div (hDc.pow 2) fun x hx => pow_ne_zero 2 (hDne x hx)
  have hEc : ContinuousOn (fun y => Complex.exp ((Θ y : ℂ) * Complex.I)) (Icc a b) :=
    Complex.continuous_exp.comp_continuousOn
      ((Complex.continuous_ofReal.comp_continuousOn hΘc).mul continuousOn_const)
  have hu'int : IntervalIntegrable (fun x => (g' x * ((Θ' x : ℂ) * Complex.I) -
      g x * ((Θ'' x : ℂ) * Complex.I)) / ((Θ' x : ℂ) * Complex.I) ^ 2) volume a b :=
    (huI ▸ hu'c).intervalIntegrable
  have hv'int : IntervalIntegrable
      (fun x => Complex.exp ((Θ x : ℂ) * Complex.I) * ((Θ' x : ℂ) * Complex.I)) volume a b :=
    (huI ▸ hEc.mul hDc).intervalIntegrable
  have hibp := integral_mul_deriv_eq_deriv_mul hu hv hu'int hv'int
  have hcongr : (∫ x in a..b, g x * Complex.exp ((Θ x : ℂ) * Complex.I)) =
      ∫ x in a..b, (g x / ((Θ' x : ℂ) * Complex.I)) *
        (Complex.exp ((Θ x : ℂ) * Complex.I) * ((Θ' x : ℂ) * Complex.I)) := by
    refine integral_congr fun x hx => ?_
    rw [huI] at hx
    rw [div_mul_eq_mul_div, eq_div_iff (hDne x hx)]
    ring
  -- the transferred term
  have hnormD : ∀ x, ‖(Θ' x : ℂ) * Complex.I‖ = |Θ' x| := fun x => by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have hpt : ∀ x ∈ Icc a b, ‖(g' x * ((Θ' x : ℂ) * Complex.I) - g x * ((Θ'' x : ℂ) *
      Complex.I)) / ((Θ' x : ℂ) * Complex.I) ^ 2 * Complex.exp ((Θ x : ℂ) * Complex.I)‖ ≤
      ‖g' x‖ / lam + G * (Θ'' x / Θ' x ^ 2) := by
    intro x hx
    have hp := hΘ'pos x hx
    rw [norm_mul, norm_exp_ofReal_mul_I, mul_one, norm_div, norm_pow, hnormD]
    have hnum : ‖g' x * ((Θ' x : ℂ) * Complex.I) - g x * ((Θ'' x : ℂ) * Complex.I)‖ ≤
        ‖g' x‖ * |Θ' x| + G * Θ'' x := by
      refine le_trans (norm_sub_le _ _) (add_le_add (le_of_eq ?_) ?_)
      · rw [norm_mul, hnormD]
      · rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (hpos x hx)]
        exact mul_le_mul_of_nonneg_right (hG x hx) (hpos x hx)
    have hsq : Θ' x ^ 2 = |Θ' x| ^ 2 := (sq_abs _).symm
    calc ‖g' x * ((Θ' x : ℂ) * Complex.I) - g x * ((Θ'' x : ℂ) * Complex.I)‖ / |Θ' x| ^ 2
        ≤ (‖g' x‖ * |Θ' x| + G * Θ'' x) / |Θ' x| ^ 2 :=
          div_le_div_of_nonneg_right hnum (by positivity)
      _ = ‖g' x‖ / |Θ' x| + G * (Θ'' x / Θ' x ^ 2) := by
          rw [hsq]; field_simp
      _ ≤ ‖g' x‖ / lam + G * (Θ'' x / Θ' x ^ 2) := by
          gcongr
          exact hlow x hx
  -- `∫ Θ''/Θ'² = 1/Θ'(a) − 1/Θ'(b)`
  have hrecip : ∀ x ∈ uIcc a b, HasDerivAt (fun y => -(1 / Θ' y)) (Θ'' x / Θ' x ^ 2) x := by
    rw [huI]; intro x hx
    have h := ((hΘ' x hx).inv (hΘ'ne x hx)).neg
    have e1 : (fun y => -(1 / Θ' y)) = fun y => -(Θ' y)⁻¹ := by funext y; rw [one_div]
    have e2 : -(-Θ'' x / Θ' x ^ 2) = Θ'' x / Θ' x ^ 2 := by ring
    rw [e1, ← e2]; exact h
  have hrc : ContinuousOn (fun x => Θ'' x / Θ' x ^ 2) (Icc a b) :=
    hΘ''.div (hΘ'c.pow 2) fun x hx => pow_ne_zero 2 (hΘ'ne x hx)
  have hrint : IntervalIntegrable (fun x => Θ'' x / Θ' x ^ 2) volume a b :=
    (huI ▸ hrc).intervalIntegrable
  have hFTC := integral_eq_sub_of_hasDerivAt hrecip hrint
  have hsign := same_sign_of_ne_zero hab hΘ'c hΘ'ne
  have hdiff : |1 / Θ' a - 1 / Θ' b| ≤ 1 / lam :=
    abs_inv_sub_inv_le hlam (hlow a hamem) (hlow b hbmem) hsign
  have hR : (∫ x in a..b, Θ'' x / Θ' x ^ 2) ≤ 1 / lam := by
    rw [hFTC]
    have : -(1 / Θ' b) - -(1 / Θ' a) = 1 / Θ' a - 1 / Θ' b := by ring
    rw [this]
    exact le_trans (le_abs_self _) hdiff
  have hg'int : IntervalIntegrable (fun x => ‖g' x‖) volume a b :=
    (huI ▸ hg'.norm).intervalIntegrable
  have htail : ‖∫ x in a..b, (g' x * ((Θ' x : ℂ) * Complex.I) - g x * ((Θ'' x : ℂ) *
      Complex.I)) / ((Θ' x : ℂ) * Complex.I) ^ 2 * Complex.exp ((Θ x : ℂ) * Complex.I)‖ ≤
      V / lam + G / lam := by
    refine le_trans (norm_integral_le_of_norm_le hab (Filter.Eventually.of_forall fun x hx =>
      hpt x (Ioc_subset_Icc_self hx)) ((hg'int.div_const lam).add (hrint.const_mul G))) ?_
    rw [integral_add (hg'int.div_const lam) (hrint.const_mul G), intervalIntegral.integral_div,
      intervalIntegral.integral_const_mul]
    have h1 : (∫ x in a..b, ‖g' x‖) / lam ≤ V / lam := div_le_div_of_nonneg_right hV hlam.le
    have h2 : G * (∫ x in a..b, Θ'' x / Θ' x ^ 2) ≤ G * (1 / lam) :=
      mul_le_mul_of_nonneg_left hR hG0
    rw [mul_one_div] at h2
    linarith
  have hbd : ∀ x ∈ Icc a b, ‖g x / ((Θ' x : ℂ) * Complex.I) *
      Complex.exp ((Θ x : ℂ) * Complex.I)‖ ≤ ‖g x‖ / lam := by
    intro x hx
    rw [norm_mul, norm_exp_ofReal_mul_I, mul_one, norm_div, hnormD]
    exact div_le_div_of_nonneg_left (norm_nonneg _) hlam (hlow x hx)
  rw [hcongr, hibp]
  calc ‖g b / ((Θ' b : ℂ) * Complex.I) * Complex.exp ((Θ b : ℂ) * Complex.I) -
        g a / ((Θ' a : ℂ) * Complex.I) * Complex.exp ((Θ a : ℂ) * Complex.I) -
        ∫ x in a..b, (g' x * ((Θ' x : ℂ) * Complex.I) - g x * ((Θ'' x : ℂ) * Complex.I)) /
          ((Θ' x : ℂ) * Complex.I) ^ 2 * Complex.exp ((Θ x : ℂ) * Complex.I)‖
      ≤ ‖g b‖ / lam + ‖g a‖ / lam + (V / lam + G / lam) := by
        refine le_trans (norm_sub_le _ _) (add_le_add (le_trans (norm_sub_le _ _)
          (add_le_add (hbd b hbmem) (hbd a hamem))) htail)
    _ = (‖g a‖ + ‖g b‖ + V + G) / lam := by ring

/-- **The stationary-point (second-derivative) test.**  If `Θ'' ≥ 0` and `|Θ'(x)| ≥ μ|x − c|` on
`[a, b]`, then for every `δ > 0`,
`‖∫_a^b g e^{iΘ}‖ ≤ 2δG + (6G + 2V)/(μδ)`, where `‖g‖ ≤ G` and `∫_a^b ‖g'‖ ≤ V`. -/
theorem norm_integral_mul_exp_le_of_stationary {g g' : ℝ → ℂ} {Θ Θ' Θ'' : ℝ → ℝ}
    {a b c μ δ G V : ℝ} (hab : a ≤ b) (hμ : 0 < μ) (hδ : 0 < δ)
    (hg : ∀ x ∈ Icc a b, HasDerivAt g (g' x) x) (hg' : ContinuousOn g' (Icc a b))
    (hΘ : ∀ x ∈ Icc a b, HasDerivAt Θ (Θ' x) x)
    (hΘ' : ∀ x ∈ Icc a b, HasDerivAt Θ' (Θ'' x) x) (hΘ'' : ContinuousOn Θ'' (Icc a b))
    (hpos : ∀ x ∈ Icc a b, 0 ≤ Θ'' x) (hlow : ∀ x ∈ Icc a b, μ * |x - c| ≤ |Θ' x|)
    (hG : ∀ x ∈ Icc a b, ‖g x‖ ≤ G) (hV : ∫ x in a..b, ‖g' x‖ ≤ V) :
    ‖∫ x in a..b, g x * Complex.exp ((Θ x : ℂ) * Complex.I)‖ ≤
      2 * δ * G + (6 * G + 2 * V) / (μ * δ) := by
  set p := max a (min (c - δ) b) with hp
  set q := max p (min (c + δ) b) with hq
  have hap : a ≤ p := le_max_left _ _
  have hpb : p ≤ b := max_le hab (min_le_right _ _)
  have hpq : p ≤ q := le_max_left _ _
  have hqb : q ≤ b := max_le hpb (min_le_right _ _)
  have hG0 : 0 ≤ G := le_trans (norm_nonneg _) (hG a ⟨le_rfl, hab⟩)
  have hμδ : 0 < μ * δ := mul_pos hμ hδ
  have hV0 : 0 ≤ V := le_trans (integral_nonneg hab fun x _ => norm_nonneg (g' x)) hV
  set F : ℝ → ℂ := fun x => g x * Complex.exp ((Θ x : ℂ) * Complex.I) with hF
  have hgc : ContinuousOn g (Icc a b) := fun x hx => (hg x hx).continuousAt.continuousWithinAt
  have hFc : ContinuousOn F (Icc a b) :=
    hgc.mul
      (Complex.continuous_exp.comp_continuousOn ((Complex.continuous_ofReal.comp_continuousOn
        fun x hx => (hΘ x hx).continuousAt.continuousWithinAt).mul continuousOn_const))
  have hFint : ∀ u v, a ≤ u → u ≤ v → v ≤ b → IntervalIntegrable F volume u v :=
    fun u v hu huv hv => ((hFc.mono (Icc_subset_Icc hu hv))).intervalIntegrable_of_Icc huv
  have hg'int : ∀ u v, a ≤ u → u ≤ v → v ≤ b → IntervalIntegrable (fun x => ‖g' x‖) volume u v :=
    fun u v hu huv hv => ((hg'.norm.mono (Icc_subset_Icc hu hv))).intervalIntegrable_of_Icc huv
  have hVsub : ∀ u v, a ≤ u → u ≤ v → v ≤ b → ∫ x in u..v, ‖g' x‖ ≤ V := by
    intro u v hu huv hv
    refine le_trans (integral_mono_interval hu huv hv (Filter.Eventually.of_forall fun x =>
      norm_nonneg _) (hg'int a b le_rfl hab le_rfl)) hV
  -- one side of the window
  have hside : ∀ u v, a ≤ u → u ≤ v → v ≤ b → (u < v → ∀ x ∈ Icc u v, δ ≤ |x - c|) →
      ‖∫ x in u..v, F x‖ ≤ (3 * G + V) / (μ * δ) := by
    intro u v hu huv hv hfar
    rcases eq_or_lt_of_le huv with heq | hlt
    · rw [heq, integral_same, norm_zero]
      exact div_nonneg (by linarith) hμδ.le
    · have hsub : Icc u v ⊆ Icc a b := Icc_subset_Icc hu hv
      have h := norm_integral_mul_exp_le_of_monotone_phase (lam := μ * δ) (G := G) (V := V)
        huv hμδ (fun x hx => hg x (hsub hx)) (hg'.mono hsub) (fun x hx => hΘ x (hsub hx))
        (fun x hx => hΘ' x (hsub hx)) (hΘ''.mono hsub) (fun x hx => hpos x (hsub hx))
        (fun x hx => le_trans (mul_le_mul_of_nonneg_left (hfar hlt x hx) hμ.le)
          (hlow x (hsub hx))) (fun x hx => hG x (hsub hx)) (hVsub u v hu huv hv)
      refine le_trans h (div_le_div_of_nonneg_right ?_ hμδ.le)
      have h1 := hG u ⟨hu, huv.trans hv⟩
      have h2 := hG v ⟨hu.trans huv, hv⟩
      linarith
  have hleft : ‖∫ x in a..p, F x‖ ≤ (3 * G + V) / (μ * δ) := by
    refine hside a p le_rfl hap hpb fun hlt x hx => ?_
    have hpe : p = min (c - δ) b := by
      rcases le_total a (min (c - δ) b) with h | h
      · rw [hp, max_eq_right h]
      · exfalso
        rw [hp, max_eq_left h] at hlt
        exact lt_irrefl a hlt
    have hxc : x ≤ c - δ := le_trans hx.2 (hpe ▸ min_le_left _ _)
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]; linarith
  have hright : ‖∫ x in q..b, F x‖ ≤ (3 * G + V) / (μ * δ) := by
    refine hside q b (hap.trans hpq) hqb le_rfl fun hlt x hx => ?_
    have hmin : min (c + δ) b ≤ q := le_max_right _ _
    have hcq : c + δ ≤ q := by
      rcases le_total (c + δ) b with h | h
      · rwa [min_eq_left h] at hmin
      · rw [min_eq_right h] at hmin; linarith
    rw [abs_of_nonneg (by linarith [hx.1])]; linarith [hx.1]
  have hmid : ‖∫ x in p..q, F x‖ ≤ 2 * δ * G := by
    have hlen : q - p ≤ 2 * δ := by
      rcases le_total (c - δ) b with h | h
      · have hp1 : c - δ ≤ p := le_trans (le_of_eq (min_eq_left h).symm) (le_max_right _ _)
        have hq1 : q ≤ max p (c + δ) := max_le_max le_rfl (min_le_left _ _)
        rcases le_total p (c + δ) with h' | h'
        · rw [max_eq_right h'] at hq1; linarith
        · rw [max_eq_left h'] at hq1; linarith
      · have hp1 : b ≤ p := le_trans (le_of_eq (min_eq_right h).symm) (le_max_right _ _)
        linarith [hδ]
    have hbound : ∀ x ∈ Set.uIoc p q, ‖F x‖ ≤ G := by
      intro x hx
      rw [uIoc_of_le hpq] at hx
      have hxab : x ∈ Icc a b := ⟨by linarith [hx.1], by linarith [hx.2]⟩
      rw [hF]; dsimp only
      rw [norm_mul, norm_exp_ofReal_mul_I, mul_one]
      exact hG x hxab
    refine le_trans (norm_integral_le_of_norm_le_const hbound) ?_
    rw [abs_of_nonneg (by linarith)]
    nlinarith
  have hsplit : (∫ x in a..b, F x) = (∫ x in a..p, F x) + (∫ x in p..q, F x) +
      ∫ x in q..b, F x := by
    rw [integral_add_adjacent_intervals (hFint a p le_rfl hap hpb)
      (hFint p q hap hpq hqb), integral_add_adjacent_intervals
      (hFint a q le_rfl (hap.trans hpq) hqb) (hFint q b (hap.trans hpq) hqb le_rfl)]
  change ‖∫ x in a..b, F x‖ ≤ _
  rw [hsplit]
  calc ‖(∫ x in a..p, F x) + (∫ x in p..q, F x) + ∫ x in q..b, F x‖
      ≤ ‖∫ x in a..p, F x‖ + ‖∫ x in p..q, F x‖ + ‖∫ x in q..b, F x‖ :=
        (norm_add_le _ _).trans (by gcongr; exact norm_add_le _ _)
    _ ≤ (3 * G + V) / (μ * δ) + 2 * δ * G + (3 * G + V) / (μ * δ) := by gcongr
    _ = 2 * δ * G + (6 * G + 2 * V) / (μ * δ) := by ring

end

end GaloisForLFunctions.HTGeometry
