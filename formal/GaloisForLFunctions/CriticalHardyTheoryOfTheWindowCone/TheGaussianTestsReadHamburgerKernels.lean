import GaloisForLFunctions.CriticalHardyTheoryOfTheWindowCone.TheShiftedGammaTestsAreTaylorCoefficients
import GaloisForLFunctions.HTGeometry.LaplaceBesselHalfIntegral
import GaloisForLFunctions.RHTower.WeilMarginSuperexponentialLaw
import GaloisForLFunctions.RHTower.WeilFullConeExtremePoint
import GaloisForLFunctions.RHTower.WeilConeXiDivisibleBlindFamily

/-!
# The Gaussian tests read Hamburger's kernels

Riemann's kernel is a sum over `k ≥ 1` of dilates of one profile,
`Φ(u) = Σ_k e^{u/2} P(k²e^{2u}) e^{−πk²e^{2u}}`, `P(y) = 4π²y² − 6πy`. Pair it with the Gaussian test

  `Y_t(v) = 2 e^{−3v/2} exp(−π t² e^{−2v})`,   `t > 0`.

At the atom `log n` the two orientations of the correlation give, with `x = kn`,

  `ratKer x t = 8x⁴/(π S³) − 6x²/(π S²)`,   `S = x² + t²`,
  `expKer x t = x (4π²x t − 4π) e^{−2πx t}`,

so (`hasSum_atomReading`)

  `n^{−1/2} ((Φ ⋆ Y_t)(log n) + (Φ ⋆ Y_t)(−log n)) = Σ_{k≥1} (ratKer (kn) t + expKer (kn) t)`.

This is the Laplace transform behind Hamburger's theorem, adapted to `Φ`. The rational part has poles at
`t = ±ix`; the exponential part is, for integer `x`, `i`-periodic up to a linear factor in `t`, and the
second difference in `t` with step `i` annihilates it.

Everything reduces to elementary fundamental-theorem integrals on the line, together with the half-integral
Laplace–Bessel formula.
-/

open MeasureTheory Filter Topology Set
open scoped Real

noncomputable section

namespace GaloisForLFunctions.CriticalHardyTheoryOfTheWindowCone

open _root_.RHTower _root_.RHTower.WeilSpectral

local notation "𝔽" => xiShiftedGammaTest

/-! ### Elementary bounds -/

theorem exp_neg_le_factorial_div {y : ℝ} (hy : 0 < y) (k : ℕ) :
    Real.exp (-y) ≤ (k.factorial : ℝ) / y ^ k := by
  have h := Real.pow_div_factorial_le_exp y hy.le k
  have hf : (0 : ℝ) < k.factorial := by exact_mod_cast k.factorial_pos
  rw [div_le_iff₀ hf] at h
  rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos y) (pow_pos hy k)]
  linarith

/-- The two-sided double exponential `exp(−a e^{2v} − b e^{−2v})`. -/
def twoSided (a b v : ℝ) : ℝ := Real.exp (-(a * Real.exp (2 * v)) - b * Real.exp (-(2 * v)))

theorem twoSided_pos (a b v : ℝ) : 0 < twoSided a b v := Real.exp_pos _

theorem continuous_twoSided (a b : ℝ) : Continuous (twoSided a b) := by
  unfold twoSided
  fun_prop

theorem exp_neg_mul_exp_two_le {a : ℝ} (ha : 0 < a) (k : ℕ) (v : ℝ) :
    Real.exp (-(a * Real.exp (2 * v))) ≤
      (k.factorial : ℝ) / a ^ k * Real.exp (-(2 * (k : ℝ) * v)) := by
  have h := exp_neg_le_factorial_div (mul_pos ha (Real.exp_pos (2 * v))) k
  refine h.trans (le_of_eq ?_)
  rw [mul_pow, ← Real.exp_nat_mul]
  have e : Real.exp (-(2 * (k : ℝ) * v)) = (Real.exp ((k : ℝ) * (2 * v)))⁻¹ := by
    rw [← Real.exp_neg]; ring_nf
  rw [e]
  field_simp

/-- `e^{pv} exp(−a e^{2v} − b e^{−2v}) ≤ C e^{−|v|}`. -/
theorem exists_exp_mul_twoSided_le (p : ℝ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v, Real.exp (p * v) * twoSided a b v ≤ C * Real.exp (-|v|) := by
  obtain ⟨k, hk⟩ := exists_nat_ge ((|p| + 1) / 2)
  have hk' : |p| + 1 ≤ 2 * (k : ℝ) := by linarith
  have hp1 := le_abs_self p
  have hp2 := neg_abs_le p
  have hA : 0 ≤ (k.factorial : ℝ) / a ^ k := by positivity
  have hB : 0 ≤ (k.factorial : ℝ) / b ^ k := by positivity
  refine ⟨(k.factorial : ℝ) / a ^ k + (k.factorial : ℝ) / b ^ k, by positivity, fun v => ?_⟩
  have hEp := (Real.exp_pos (p * v)).le
  rcases le_total 0 v with hv | hv
  · rw [abs_of_nonneg hv]
    have h1 : twoSided a b v ≤ Real.exp (-(a * Real.exp (2 * v))) := by
      unfold twoSided
      refine Real.exp_le_exp.mpr ?_
      have := mul_pos hb (Real.exp_pos (-(2 * v)))
      linarith
    have h2 := exp_neg_mul_exp_two_le ha k v
    calc Real.exp (p * v) * twoSided a b v
        ≤ Real.exp (p * v) * ((k.factorial : ℝ) / a ^ k * Real.exp (-(2 * (k : ℝ) * v))) :=
          mul_le_mul_of_nonneg_left (h1.trans h2) hEp
      _ = (k.factorial : ℝ) / a ^ k * Real.exp (p * v + -(2 * (k : ℝ) * v)) := by
          rw [Real.exp_add]; ring
      _ ≤ (k.factorial : ℝ) / a ^ k * Real.exp (-v) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) hA
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
  · rw [abs_of_nonpos hv, neg_neg]
    have h1 : twoSided a b v ≤ Real.exp (-(b * Real.exp (2 * (-v)))) := by
      unfold twoSided
      refine Real.exp_le_exp.mpr ?_
      have := mul_pos ha (Real.exp_pos (2 * v))
      have e : 2 * -v = -(2 * v) := by ring
      rw [e]
      linarith
    have h2 := exp_neg_mul_exp_two_le hb k (-v)
    calc Real.exp (p * v) * twoSided a b v
        ≤ Real.exp (p * v) * ((k.factorial : ℝ) / b ^ k * Real.exp (-(2 * (k : ℝ) * (-v)))) :=
          mul_le_mul_of_nonneg_left (h1.trans h2) hEp
      _ = (k.factorial : ℝ) / b ^ k * Real.exp (p * v + -(2 * (k : ℝ) * (-v))) := by
          rw [Real.exp_add]; ring
      _ ≤ (k.factorial : ℝ) / b ^ k * Real.exp v :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) hB
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le

theorem integrable_exp_neg_abs : Integrable fun v : ℝ => Real.exp (-|v|) := by
  simpa using integrable_exp_neg_mul_abs_fam (κ := 1) one_pos

theorem integrable_exp_mul_twoSided (p : ℝ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Integrable fun v => Real.exp (p * v) * twoSided a b v := by
  obtain ⟨C, -, hC⟩ := exists_exp_mul_twoSided_le p ha hb
  refine (integrable_exp_neg_abs.const_mul C).mono'
    ((by have := continuous_twoSided a b; fun_prop : Continuous fun v =>
      Real.exp (p * v) * twoSided a b v).aestronglyMeasurable) (Eventually.of_forall fun v => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (mul_pos (Real.exp_pos _) (twoSided_pos _ _ _))]
  exact hC v

theorem tendsto_exp_neg_abs_atTop : Tendsto (fun v : ℝ => Real.exp (-|v|)) atTop (𝓝 0) :=
  Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_abs_atTop_atTop

theorem tendsto_exp_neg_abs_atBot : Tendsto (fun v : ℝ => Real.exp (-|v|)) atBot (𝓝 0) :=
  Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_abs_atBot_atTop

/-! ### The two-sided integrals -/

/-- `J_p(a, b) = ∫ e^{pv} exp(−a e^{2v} − b e^{−2v}) dv`. -/
def twoSidedInt (p a b : ℝ) : ℝ := ∫ v, Real.exp (p * v) * twoSided a b v

/-- Integrating the total derivative of `e^v exp(−a e^{2v} − b e^{−2v})`. -/
theorem twoSidedInt_relation {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    twoSidedInt 1 a b - 2 * a * twoSidedInt 3 a b + 2 * b * twoSidedInt (-1) a b = 0 := by
  have h1 := integrable_exp_mul_twoSided 1 ha hb
  have h3 := integrable_exp_mul_twoSided 3 ha hb
  have hm := integrable_exp_mul_twoSided (-1) ha hb
  obtain ⟨C, hC0, hC⟩ := exists_exp_mul_twoSided_le 1 ha hb
  have hder : ∀ v, HasDerivAt (fun v => Real.exp (1 * v) * twoSided a b v)
      (Real.exp (1 * v) * twoSided a b v - 2 * a * (Real.exp (3 * v) * twoSided a b v) +
        2 * b * (Real.exp (-1 * v) * twoSided a b v)) v := by
    intro v
    have e1 : HasDerivAt (fun v : ℝ => Real.exp (1 * v)) (Real.exp (1 * v) * 1) v := by
      simpa using ((hasDerivAt_id v).const_mul (1 : ℝ)).exp
    have e2 : HasDerivAt (fun v : ℝ => Real.exp (2 * v)) (Real.exp (2 * v) * 2) v := by
      simpa using ((hasDerivAt_id v).const_mul (2 : ℝ)).exp
    have e3 : HasDerivAt (fun v : ℝ => Real.exp (-(2 * v))) (Real.exp (-(2 * v)) * (-2)) v := by
      simpa using ((hasDerivAt_id v).const_mul (2 : ℝ)).neg.exp
    have eT : HasDerivAt (twoSided a b) (twoSided a b v *
        (-(a * (Real.exp (2 * v) * 2)) - b * (Real.exp (-(2 * v)) * (-2)))) v :=
      ((e2.const_mul a).neg.sub (e3.const_mul b)).exp
    refine (e1.mul eT).congr_deriv ?_
    have x3 : Real.exp (3 * v) = Real.exp (1 * v) * Real.exp (2 * v) := by
      rw [← Real.exp_add]; ring_nf
    have xm : Real.exp (-1 * v) = Real.exp (1 * v) * Real.exp (-(2 * v)) := by
      rw [← Real.exp_add]; ring_nf
    rw [x3, xm]
    ring
  have hi1 : Integrable fun x => Real.exp (1 * x) * twoSided a b x -
      2 * a * (Real.exp (3 * x) * twoSided a b x) := h1.sub (h3.const_mul (2 * a))
  have hint := hi1.add (hm.const_mul (2 * b))
  have hlim : ∀ {l : Filter ℝ}, Tendsto (fun v : ℝ => Real.exp (-|v|)) l (𝓝 0) →
      Tendsto (fun v => Real.exp (1 * v) * twoSided a b v) l (𝓝 0) := by
    intro l hl
    have hl' := hl.const_mul C
    rw [mul_zero] at hl'
    refine squeeze_zero (fun v => ?_) (fun v => hC v) hl'
    exact (mul_pos (Real.exp_pos _) (twoSided_pos _ _ _)).le
  have h := integral_of_hasDerivAt_of_tendsto hder hint (hlim tendsto_exp_neg_abs_atBot)
    (hlim tendsto_exp_neg_abs_atTop)
  rw [integral_add hi1 (hm.const_mul (2 * b)), integral_sub h1 (h3.const_mul (2 * a)),
    integral_const_mul, integral_const_mul] at h
  unfold twoSidedInt
  linarith

/-- The substitution `w = e^{2v}`. -/
theorem integral_Ioi_eq_integral_exp (g : ℝ → ℝ) :
    ∫ w in Ioi (0 : ℝ), g w = ∫ v, (2 * Real.exp (2 * v)) * g (Real.exp (2 * v)) := by
  have him : (fun v : ℝ => Real.exp (2 * v)) '' univ = Ioi 0 := by
    ext w
    constructor
    · rintro ⟨v, -, rfl⟩
      exact Real.exp_pos _
    · intro hw
      refine ⟨Real.log w / 2, mem_univ _, ?_⟩
      simp only
      rw [mul_div_cancel₀ _ (two_ne_zero), Real.exp_log hw]
  have hinj : InjOn (fun v : ℝ => Real.exp (2 * v)) univ := fun x _ y _ h => by
    have := Real.exp_injective h
    linarith
  have hd : ∀ x ∈ (univ : Set ℝ), HasDerivWithinAt (fun v : ℝ => Real.exp (2 * v))
      (2 * Real.exp (2 * x)) univ x := fun x _ => by
    have : HasDerivAt (fun v : ℝ => Real.exp (2 * v)) (Real.exp (2 * x) * 2) x := by
      simpa using ((hasDerivAt_id x).const_mul (2 : ℝ)).exp
    exact (this.congr_deriv (mul_comm _ _)).hasDerivWithinAt
  have h := integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ hd hinj g
  rw [him] at h
  rw [h, Measure.restrict_univ]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only [smul_eq_mul]
  rw [abs_of_pos (by positivity)]

/-- `∫ e^{v} exp(−πx² e^{2v} − πt² e^{−2v}) dv = e^{−2πxt}/(2x)`. -/
theorem twoSidedInt_one {x t : ℝ} (hx : 0 < x) (ht : 0 < t) :
    twoSidedInt 1 (π * x ^ 2) (π * t ^ 2) = 1 / (2 * x) * Real.exp (-(2 * π * x * t)) := by
  have h := HTGeometry.integral_rpow_neg_half_mul_exp_theta_dual ht hx
  rw [integral_Ioi_eq_integral_exp] at h
  have e : ∀ v : ℝ, (2 * Real.exp (2 * v)) * (Real.exp (2 * v) ^ (-(1 / 2 : ℝ)) *
      Real.exp (-(π * t ^ 2 / Real.exp (2 * v)) - π * x ^ 2 * Real.exp (2 * v))) =
      2 * (Real.exp (1 * v) * twoSided (π * x ^ 2) (π * t ^ 2) v) := by
    intro v
    have e1 : Real.exp (2 * v) ^ (-(1 / 2 : ℝ)) = Real.exp (-v) := by
      rw [← Real.exp_mul]; ring_nf
    have e2 : π * t ^ 2 / Real.exp (2 * v) = π * t ^ 2 * Real.exp (-(2 * v)) := by
      rw [Real.exp_neg]; rfl
    have e3 : Real.exp (2 * v) * Real.exp (-v) = Real.exp (1 * v) := by
      rw [← Real.exp_add]; ring_nf
    unfold twoSided
    rw [e1, e2]
    have e4 : -(π * t ^ 2 * Real.exp (-(2 * v))) - π * x ^ 2 * Real.exp (2 * v) =
        -(π * x ^ 2 * Real.exp (2 * v)) - π * t ^ 2 * Real.exp (-(2 * v)) := by ring
    rw [e4, ← e3]
    ring
  simp_rw [e] at h
  rw [integral_const_mul] at h
  unfold twoSidedInt
  have e5 : 2 * π * t * x = 2 * π * x * t := by ring
  rw [e5] at h
  field_simp at h ⊢
  linarith

/-- Reflection `v ↦ −v` exchanges the two sides. -/
theorem twoSidedInt_neg (p a b : ℝ) : twoSidedInt (-p) a b = twoSidedInt p b a := by
  unfold twoSidedInt
  rw [← integral_neg_eq_self]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only
  unfold twoSided
  have e : -(a * Real.exp (2 * -v)) - b * Real.exp (-(2 * -v)) =
      -(b * Real.exp (2 * v)) - a * Real.exp (-(2 * v)) := by
    rw [show 2 * -v = -(2 * v) by ring, neg_neg]
    ring
  rw [e, show -p * -v = p * v by ring]

theorem twoSidedInt_neg_one {x t : ℝ} (hx : 0 < x) (ht : 0 < t) :
    twoSidedInt (-1) (π * x ^ 2) (π * t ^ 2) = 1 / (2 * t) * Real.exp (-(2 * π * x * t)) := by
  rw [twoSidedInt_neg, twoSidedInt_one ht hx]
  congr 2
  ring

theorem twoSidedInt_three {x t : ℝ} (hx : 0 < x) (ht : 0 < t) :
    twoSidedInt 3 (π * x ^ 2) (π * t ^ 2) =
      (1 / (2 * x) + π * t) / (2 * π * x ^ 2) * Real.exp (-(2 * π * x * t)) := by
  have h := twoSidedInt_relation (a := π * x ^ 2) (b := π * t ^ 2) (by positivity) (by positivity)
  rw [twoSidedInt_one hx ht, twoSidedInt_neg_one hx ht] at h
  have hE := Real.exp_pos (-(2 * π * x * t))
  field_simp at h ⊢
  linarith

/-! ### The one-sided integrals -/

/-- `M_p(q) = ∫ e^{pv} exp(−q e^{2v}) dv`, which is `∫₀^∞ w^{p/2−1} e^{−qw} dw / 2`. -/
def oneSidedInt (p q : ℝ) : ℝ := ∫ v, Real.exp (p * v) * Real.exp (-(q * Real.exp (2 * v)))

theorem exists_exp_mul_oneSided_le {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    ∃ C κ : ℝ, 0 ≤ C ∧ 0 < κ ∧ ∀ v, Real.exp (p * v) * Real.exp (-(q * Real.exp (2 * v))) ≤
      C * Real.exp (-(κ * |v|)) := by
  obtain ⟨k, hk⟩ := exists_nat_ge ((p + 1) / 2)
  have hk' : p + 1 ≤ 2 * (k : ℝ) := by linarith
  have hA : 0 ≤ (k.factorial : ℝ) / q ^ k := by positivity
  refine ⟨(k.factorial : ℝ) / q ^ k + 1, min p 1, by positivity, lt_min hp one_pos, fun v => ?_⟩
  have hm1 := min_le_left p 1
  have hm2 := min_le_right p 1
  have hm0 : 0 < min p 1 := lt_min hp one_pos
  rcases le_total 0 v with hv | hv
  · rw [abs_of_nonneg hv]
    have h2 := exp_neg_mul_exp_two_le hq k v
    calc Real.exp (p * v) * Real.exp (-(q * Real.exp (2 * v)))
        ≤ Real.exp (p * v) * ((k.factorial : ℝ) / q ^ k * Real.exp (-(2 * (k : ℝ) * v))) :=
          mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
      _ = (k.factorial : ℝ) / q ^ k * Real.exp (p * v + -(2 * (k : ℝ) * v)) := by
          rw [Real.exp_add]; ring
      _ ≤ (k.factorial : ℝ) / q ^ k * Real.exp (-(min p 1 * v)) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) hA
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
  · rw [abs_of_nonpos hv]
    have h1 : Real.exp (-(q * Real.exp (2 * v))) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by have := mul_pos hq (Real.exp_pos (2 * v)); linarith)
    calc Real.exp (p * v) * Real.exp (-(q * Real.exp (2 * v)))
        ≤ Real.exp (p * v) * 1 := mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
      _ = 1 * Real.exp (p * v) := by ring
      _ ≤ 1 * Real.exp (-(min p 1 * -v)) := by
          refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num)
          nlinarith
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le

theorem integrable_exp_mul_oneSided {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    Integrable fun v => Real.exp (p * v) * Real.exp (-(q * Real.exp (2 * v))) := by
  obtain ⟨C, κ, -, hκ, hC⟩ := exists_exp_mul_oneSided_le hp hq
  refine ((integrable_exp_neg_mul_abs_fam hκ).const_mul C).mono'
    ((by fun_prop : Continuous fun v =>
      Real.exp (p * v) * Real.exp (-(q * Real.exp (2 * v)))).aestronglyMeasurable)
    (Eventually.of_forall fun v => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (mul_pos (Real.exp_pos _) (Real.exp_pos _))]
  exact hC v

theorem hasDerivAt_oneSidedFactor (q v : ℝ) :
    HasDerivAt (fun v => Real.exp (-(q * Real.exp (2 * v))))
      (-(2 * q) * (Real.exp (2 * v) * Real.exp (-(q * Real.exp (2 * v))))) v := by
  have e2 : HasDerivAt (fun v : ℝ => Real.exp (2 * v)) (Real.exp (2 * v) * 2) v := by
    simpa using ((hasDerivAt_id v).const_mul (2 : ℝ)).exp
  refine ((e2.const_mul q).neg.exp).congr_deriv ?_
  ring

/-- `M_2(q) = 1/(2q)`. -/
theorem oneSidedInt_two {q : ℝ} (hq : 0 < q) : oneSidedInt 2 q = 1 / (2 * q) := by
  have hbot : Tendsto (fun v : ℝ => Real.exp (-(q * Real.exp (2 * v)))) atBot (𝓝 1) := by
    have h1 : Tendsto (fun v : ℝ => 2 * v) atBot atBot :=
      tendsto_id.const_mul_atBot (by norm_num : (0 : ℝ) < 2)
    have h2 := Real.tendsto_exp_atBot.comp h1
    have h3 := (h2.const_mul q).neg
    have := Real.continuous_exp.continuousAt.tendsto.comp (x := (0 : ℝ))
      (by simpa using h3)
    simpa using this
  have htop : Tendsto (fun v : ℝ => Real.exp (-(q * Real.exp (2 * v)))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun v : ℝ => 2 * v) atTop atTop :=
      tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2)
    have h2 := Real.tendsto_exp_atTop.comp h1
    exact Real.tendsto_exp_neg_atTop_nhds_zero.comp (h2.const_mul_atTop hq)
  have hi := integrable_exp_mul_oneSided (p := 2) (by norm_num) hq
  have h := integral_of_hasDerivAt_of_tendsto (fun v => hasDerivAt_oneSidedFactor q v)
    (hi.const_mul _) hbot htop
  rw [integral_const_mul] at h
  unfold oneSidedInt
  field_simp at h ⊢
  linarith

/-- `p M_p(q) = 2q M_{p+2}(q)`, integrating the total derivative of `e^{pv} exp(−q e^{2v})`. -/
theorem oneSidedInt_add_two {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    2 * q * oneSidedInt (p + 2) q = p * oneSidedInt p q := by
  have h0 := integrable_exp_mul_oneSided hp hq
  have h2 := integrable_exp_mul_oneSided (p := p + 2) (by linarith) hq
  obtain ⟨C, κ, -, hκ, hC⟩ := exists_exp_mul_oneSided_le hp hq
  have hder : ∀ v, HasDerivAt (fun v => Real.exp (p * v) * Real.exp (-(q * Real.exp (2 * v))))
      (p * (Real.exp (p * v) * Real.exp (-(q * Real.exp (2 * v)))) -
        2 * q * (Real.exp ((p + 2) * v) * Real.exp (-(q * Real.exp (2 * v))))) v := by
    intro v
    have e1 : HasDerivAt (fun v : ℝ => Real.exp (p * v)) (Real.exp (p * v) * p) v := by
      simpa using ((hasDerivAt_id v).const_mul p).exp
    refine (e1.mul (hasDerivAt_oneSidedFactor q v)).congr_deriv ?_
    have x : Real.exp ((p + 2) * v) = Real.exp (p * v) * Real.exp (2 * v) := by
      rw [← Real.exp_add]; ring_nf
    rw [x]
    ring
  have hlim : ∀ {l : Filter ℝ}, Tendsto (fun v : ℝ => |v|) l atTop →
      Tendsto (fun v => Real.exp (p * v) * Real.exp (-(q * Real.exp (2 * v)))) l (𝓝 0) := by
    intro l hl
    have h1 : Tendsto (fun v : ℝ => Real.exp (-(κ * |v|))) l (𝓝 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp (hl.const_mul_atTop hκ)
    have hl' := h1.const_mul C
    rw [mul_zero] at hl'
    refine squeeze_zero (fun v => ?_) (fun v => hC v) hl'
    exact (mul_pos (Real.exp_pos _) (Real.exp_pos _)).le
  have h := integral_of_hasDerivAt_of_tendsto hder ((h0.const_mul p).sub (h2.const_mul (2 * q)))
    (hlim tendsto_abs_atBot_atTop) (hlim tendsto_abs_atTop_atTop)
  rw [integral_sub (h0.const_mul p) (h2.const_mul (2 * q)), integral_const_mul,
    integral_const_mul] at h
  unfold oneSidedInt
  linarith

/-- `M_4(q) = 1/(2q²)`. -/
theorem oneSidedInt_four {q : ℝ} (hq : 0 < q) : oneSidedInt 4 q = 1 / (2 * q ^ 2) := by
  have h := oneSidedInt_add_two (p := 2) (by norm_num) hq
  rw [oneSidedInt_two hq, show (2 : ℝ) + 2 = 4 by norm_num] at h
  field_simp at h ⊢
  linarith

/-- `M_6(q) = 1/q³`. -/
theorem oneSidedInt_six {q : ℝ} (hq : 0 < q) : oneSidedInt 6 q = 1 / q ^ 3 := by
  have h := oneSidedInt_add_two (p := 4) (by norm_num) hq
  rw [oneSidedInt_four hq, show (4 : ℝ) + 2 = 6 by norm_num] at h
  field_simp at h ⊢
  linarith

end GaloisForLFunctions.CriticalHardyTheoryOfTheWindowCone
