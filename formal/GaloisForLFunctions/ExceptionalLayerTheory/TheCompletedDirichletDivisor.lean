import GaloisForLFunctions.RHTower.CompletionLogDerivZeroPairs
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import GaloisForLFunctions.RHTower.DirichletLZerosInfinite
import GaloisForLFunctions.RHTower.RiemannXiRealAxisNonvanishing
import GaloisForLFunctions.HTGeometry.OrderOneEnvelopeRootDivision

/-!
# The complete divisor of the Dirichlet repulsion auxiliary function

The entire function `Eχ(s) = ξ(s) q^(s/2) Λχ(s)` retains the complete
nontrivial divisor of `ζLχ`, including multiplicity and central zeros.
Every higher logarithmic derivative is its absolutely convergent zero
moment. For a real primitive character, reflection bounds the reciprocal
square mass by twice the real logarithmic derivative in `Re s > 1`.

Local inverse-square majorants justify differentiation of the infinite
Hadamard sum. No finite truncation or central-value assumption is used.
-/

open Complex Filter Topology Metric Set
open GaloisForLFunctions.EntireZeroDivisor

noncomputable section
namespace GaloisForLFunctions.ExceptionalLayerTheory

/-- Comparing a translated resolvent with the original inverse zero. -/
private theorem norm_resolvent_le {a w : ℂ} {δ R : ℝ}
    (ha : a ≠ 0) (hδ : 0 < δ) (hd : δ ≤ ‖w - a‖) (hR : 0 ≤ R) (hw : ‖w‖ ≤ R) :
    ‖(w - a)⁻¹‖ ≤ (1 + R / δ) / ‖a‖ := by
  have hapos : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hdpos : 0 < ‖w - a‖ := hδ.trans_le hd
  have ht : ‖a‖ ≤ R + ‖w - a‖ := by
    have hh := norm_sub_le_norm_sub_add_norm_sub a w 0
    rw [sub_zero, sub_zero, norm_sub_rev a w] at hh
    linarith only [hh, hw]
  have hm : R ≤ (R / δ) * ‖w - a‖ := by
    have hh := mul_le_mul_of_nonneg_left hd (div_nonneg hR hδ.le)
    simpa only [div_mul_cancel₀ R hδ.ne'] using hh
  rw [norm_inv, inv_eq_one_div, div_le_div_iff₀ hdpos hapos]
  nlinarith only [ht, hm]

private theorem norm_resolvent_power_le {a w : ℂ} {δ R : ℝ}
    (ha : a ≠ 0) (hδ : 0 < δ) (hd : δ ≤ ‖w - a‖) (hR : 0 ≤ R) (hw : ‖w‖ ≤ R)
    (n : ℕ) :
    ‖((w - a)⁻¹) ^ (n + 2)‖ ≤ δ⁻¹ ^ n * (1 + R / δ) ^ 2 * (1 / ‖a‖ ^ 2) := by
  have hi := norm_resolvent_le ha hδ hd hR hw
  have hiδ : ‖(w - a)⁻¹‖ ≤ δ⁻¹ := by
    rw [norm_inv]
    exact inv_anti₀ hδ hd
  have hs := pow_le_pow_left₀ (norm_nonneg _) hi 2
  have hn := pow_le_pow_left₀ (norm_nonneg _) hiδ n
  rw [norm_pow, pow_add]
  have hh := mul_le_mul hn hs (sq_nonneg _) (pow_nonneg (inv_nonneg.mpr hδ.le) n)
  calc
    _ ≤ δ⁻¹ ^ n * ((1 + R / δ) / ‖a‖) ^ 2 := hh
    _ = _ := by ring

private theorem resolvent_ball_bounds {a z w : ℂ} (ha : a.re ≤ -1) (_hz : -1 < z.re)
    (hw : w ∈ ball z ((z.re + 1) / 2)) :
    (z.re + 1) / 2 ≤ ‖w - a‖ ∧ ‖w‖ ≤ ‖z‖ + (z.re + 1) / 2 := by
  have hdist : ‖w - z‖ < (z.re + 1) / 2 := by simpa only [mem_ball, dist_eq_norm] using hw
  have hre := re_le_norm (z - w)
  rw [sub_re, norm_sub_rev z w] at hre
  have hwa := re_le_norm (w - a)
  rw [sub_re] at hwa
  have htri := norm_sub_le_norm_sub_add_norm_sub w z 0
  simp only [sub_zero] at htri
  constructor <;> linarith only [hdist, hre, hwa, ha, htri]

private theorem ne_zero_of_re_le_neg_one {a : ℂ} (ha : a.re ≤ -1) : a ≠ 0 := by
  intro h
  rw [h, zero_re] at ha
  norm_num at ha

private theorem sub_ne_zero_on_ball {a z w : ℂ} (ha : a.re ≤ -1) (hz : -1 < z.re)
    (hw : w ∈ ball z ((z.re + 1) / 2)) : w - a ≠ 0 := by
  have hb := (resolvent_ball_bounds ha hz hw).1
  have hp : 0 < ‖w - a‖ := by linarith only [hb, hz]
  exact norm_pos_iff.mp hp

private theorem hasDerivAt_resolvent {a w : ℂ} (hw : w - a ≠ 0) :
    HasDerivAt (fun u : ℂ => (u - a)⁻¹) (-((w - a)⁻¹) ^ 2) w := by
  have hd : HasDerivAt (fun u : ℂ => u - a) (1 : ℂ) w := (hasDerivAt_id w).sub_const a
  simpa only [neg_div, one_div, inv_pow] using! hd.inv hw

private theorem hasDerivAt_resolvent_power (n : ℕ) {a w : ℂ} (hw : w - a ≠ 0) :
    HasDerivAt (fun u : ℂ => ((u - a)⁻¹) ^ (n + 2))
      (-((n + 2 : ℕ) : ℂ) * ((w - a)⁻¹) ^ (n + 3)) w := by
  have h := (hasDerivAt_resolvent hw).pow (n + 2)
  have heq : ((n + 2 : ℕ) : ℂ) * ((w - a)⁻¹) ^ (n + 2 - 1) * (-((w - a)⁻¹) ^ 2) =
      -((n + 2 : ℕ) : ℂ) * ((w - a)⁻¹) ^ (n + 3) := by
    rw [show n + 2 - 1 = n + 1 by omega, show n + 3 = (n + 1) + 2 by omega, pow_add]
    ring
  rw [heq] at h
  exact h

/-- Higher reciprocal moments can be differentiated without truncating the
divisor. A local disc gives a summable inverse-square majorant. -/
private theorem deriv_tsum_resolvent_power {ι : Type*} {a : ι → ℂ}
    (ha : ∀ i, (a i).re ≤ -1) (hsum : Summable (fun i => 1 / ‖a i‖ ^ 2))
    (n : ℕ) {z : ℂ} (hz : -1 < z.re) :
    deriv (fun w : ℂ => ∑' i, ((w - a i)⁻¹) ^ (n + 2)) z =
      -((n + 2 : ℕ) : ℂ) * ∑' i, ((z - a i)⁻¹) ^ (n + 3) := by
  let δ : ℝ := (z.re + 1) / 2
  let R : ℝ := ‖z‖ + δ
  have hδ : 0 < δ := by dsimp [δ]; linarith only [hz]
  have hR : 0 ≤ R := add_nonneg (norm_nonneg z) hδ.le
  have hu : Summable (fun i => δ⁻¹ ^ n * (1 + R / δ) ^ 2 * (1 / ‖a i‖ ^ 2)) :=
    hsum.mul_left _
  have hdiff (i : ι) : DifferentiableOn ℂ (fun w : ℂ => ((w - a i)⁻¹) ^ (n + 2)) (ball z δ) := by
    intro w hw
    exact (hasDerivAt_resolvent_power n (sub_ne_zero_on_ball (ha i) hz hw)).differentiableAt.differentiableWithinAt
  have hbound (i : ι) (w : ℂ) (hw : w ∈ ball z δ) :
      ‖((w - a i)⁻¹) ^ (n + 2)‖ ≤ δ⁻¹ ^ n * (1 + R / δ) ^ 2 * (1 / ‖a i‖ ^ 2) :=
    norm_resolvent_power_le (ne_zero_of_re_le_neg_one (ha i)) hδ
      (resolvent_ball_bounds (ha i) hz hw).1 hR (resolvent_ball_bounds (ha i) hz hw).2 n
  have h := hasSum_deriv_of_summable_norm hu hdiff isOpen_ball hbound (mem_ball_self hδ)
  have hzmem : z ∈ ball z δ := mem_ball_self hδ
  have hterms (i : ι) :
      deriv (fun w : ℂ => ((w - a i)⁻¹) ^ (n + 2)) z =
        -((n + 2 : ℕ) : ℂ) * ((z - a i)⁻¹) ^ (n + 3) :=
    (hasDerivAt_resolvent_power n (sub_ne_zero_on_ball (ha i) hz hzmem)).deriv
  rw [← h.tsum_eq]
  simp_rw [hterms]
  exact tsum_mul_left

private theorem norm_regularized_resolvent_le {a w : ℂ} {δ R : ℝ}
    (ha : a ≠ 0) (hδ : 0 < δ) (hd : δ ≤ ‖w - a‖) (hR : 0 ≤ R) (hw : ‖w‖ ≤ R) :
    ‖(w - a)⁻¹ + a⁻¹‖ ≤ R * (1 + R / δ) * (1 / ‖a‖ ^ 2) := by
  have hwa : w - a ≠ 0 := norm_pos_iff.mp (hδ.trans_le hd)
  have heq : (w - a)⁻¹ + a⁻¹ = w / (a * (w - a)) := by field_simp; ring
  have hi := norm_resolvent_le ha hδ hd hR hw
  calc
    _ = (‖w‖ / ‖a‖) * ‖(w - a)⁻¹‖ := by rw [heq, norm_div, norm_mul, norm_inv]; ring
    _ ≤ (R / ‖a‖) * ((1 + R / δ) / ‖a‖) :=
      mul_le_mul (div_le_div_of_nonneg_right hw (norm_nonneg _)) hi
        (norm_nonneg _) (div_nonneg hR (norm_nonneg _))
    _ = _ := by ring

private theorem deriv_tsum_regularized_resolvent {ι : Type*} {a : ι → ℂ}
    (ha : ∀ i, (a i).re ≤ -1) (hsum : Summable (fun i => 1 / ‖a i‖ ^ 2))
    {z : ℂ} (hz : -1 < z.re) :
    deriv (fun w : ℂ => ∑' i, ((w - a i)⁻¹ + (a i)⁻¹)) z =
      -(∑' i, ((z - a i)⁻¹) ^ 2) := by
  let δ : ℝ := (z.re + 1) / 2
  let R : ℝ := ‖z‖ + δ
  have hδ : 0 < δ := by dsimp [δ]; linarith only [hz]
  have hR : 0 ≤ R := add_nonneg (norm_nonneg z) hδ.le
  have hu : Summable (fun i => R * (1 + R / δ) * (1 / ‖a i‖ ^ 2)) := hsum.mul_left _
  have hdiff (i : ι) : DifferentiableOn ℂ
      (fun w : ℂ => (w - a i)⁻¹ + (a i)⁻¹) (ball z δ) := by
    intro w hw
    exact ((hasDerivAt_resolvent (sub_ne_zero_on_ball (ha i) hz hw)).add_const _).differentiableAt.differentiableWithinAt
  have hbound (i : ι) (w : ℂ) (hw : w ∈ ball z δ) :
      ‖(w - a i)⁻¹ + (a i)⁻¹‖ ≤ R * (1 + R / δ) * (1 / ‖a i‖ ^ 2) :=
    norm_regularized_resolvent_le (ne_zero_of_re_le_neg_one (ha i)) hδ
      (resolvent_ball_bounds (ha i) hz hw).1 hR (resolvent_ball_bounds (ha i) hz hw).2
  have h := hasSum_deriv_of_summable_norm hu hdiff isOpen_ball hbound (mem_ball_self hδ)
  have hterms (i : ι) :
      deriv (fun w : ℂ => (w - a i)⁻¹ + (a i)⁻¹) z = -((z - a i)⁻¹) ^ 2 :=
    ((hasDerivAt_resolvent (sub_ne_zero_on_ball (ha i) hz (mem_ball_self hδ))).add_const _).deriv
  rw [← h.tsum_eq]
  simp_rw [hterms]
  exact tsum_neg

private theorem iteratedDeriv_tsum_regularized_resolvent {ι : Type*} {a : ι → ℂ}
    (ha : ∀ i, (a i).re ≤ -1) (hsum : Summable (fun i => 1 / ‖a i‖ ^ 2))
    (n : ℕ) {z : ℂ} (hz : -1 < z.re) :
    iteratedDeriv (n + 1) (fun w : ℂ => ∑' i, ((w - a i)⁻¹ + (a i)⁻¹)) z =
      (-1 : ℂ) ^ (n + 1) * ((n + 1).factorial : ℂ) * ∑' i, ((z - a i)⁻¹) ^ (n + 2) := by
  induction n generalizing z with
  | zero =>
    simpa only [zero_add, iteratedDeriv_one, pow_one, Nat.factorial_one, Nat.cast_one,
      mul_one, neg_one_mul] using deriv_tsum_regularized_resolvent ha hsum hz
  | succ n ih =>
    rw [iteratedDeriv_succ]
    have heq : iteratedDeriv (n + 1) (fun w : ℂ => ∑' i, ((w - a i)⁻¹ + (a i)⁻¹)) =ᶠ[𝓝 z]
        fun w => (-1 : ℂ) ^ (n + 1) * ((n + 1).factorial : ℂ) *
          ∑' i, ((w - a i)⁻¹) ^ (n + 2) := by
      filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz] with w hw
      exact ih hw
    rw [heq.deriv_eq, deriv_const_mul_field, deriv_tsum_resolvent_power ha hsum n hz]
    rw [Nat.factorial_succ (n + 1), pow_succ (-1 : ℂ) (n + 1)]
    push_cast
    ring

open RHTower.OrderOneHadamard RHTower.CompletionZeroPairs

/-- Every higher logarithmic derivative is the corresponding absolutely
convergent reciprocal moment of the complete multiplicity divisor. The
affine Hadamard factor disappears after the first derivative. -/
private theorem orderOne_entire_logarithmic_moments {f : ℂ → ℂ} {C : ℝ}
    (hC : 0 ≤ C) (hf : AnalyticOnNhd ℂ f univ) (hf0 : f 0 ≠ 0)
    (hbound : ∀ w : ℂ, ‖f w‖ ≤ Real.exp (C * (1 + ‖w‖) * Real.log (2 + ‖w‖)))
    (hleft : ∀ w : ℂ, f w = 0 → w.re ≤ -1) (n : ℕ) {z : ℂ} (hz : -1 < z.re) :
    Summable (fun i : ZeroCopy f => ‖((z - zeroCopyPoint f i)⁻¹) ^ (n + 2)‖) ∧
    iteratedDeriv (n + 1) (logDeriv f) z =
      (-1 : ℂ) ^ (n + 1) * ((n + 1).factorial : ℂ) *
        ∑' i : ZeroCopy f, ((z - zeroCopyPoint f i)⁻¹) ^ (n + 2) := by
  have hford : ∀ w, analyticOrderAt f w ≠ ⊤ := fun w =>
    hf.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ (mem_univ 0) (mem_univ w)
      (by rw [(hf 0 (mem_univ 0)).analyticOrderAt_eq_zero.mpr hf0]; exact ENat.zero_ne_top)
  have ha : ∀ i : ZeroCopy f, (zeroCopyPoint f i).re ≤ -1 :=
    fun i => hleft _ (apply_zeroCopyPoint hf i)
  have hane := zeroCopyPoint_ne_zero hf hf0
  have hsum := summable_inv_sq_zeroCopyPoint hC hf hf0 hbound
  have hδ : 0 < (z.re + 1) / 2 := by linarith only [hz]
  have hR : 0 ≤ ‖z‖ + (z.re + 1) / 2 := add_nonneg (norm_nonneg z) hδ.le
  have hzmem : z ∈ ball z ((z.re + 1) / 2) := mem_ball_self hδ
  have hmoment : Summable (fun i : ZeroCopy f => ((z - zeroCopyPoint f i)⁻¹) ^ (n + 2)) := by
    refine (hsum.mul_left (((z.re + 1) / 2)⁻¹ ^ n *
      (1 + (‖z‖ + (z.re + 1) / 2) / ((z.re + 1) / 2)) ^ 2)).of_norm_bounded fun i => ?_
    exact norm_resolvent_power_le (hane i) hδ (resolvent_ball_bounds (ha i) hz hzmem).1 hR
      (resolvent_ball_bounds (ha i) hz hzmem).2 n
  refine ⟨hmoment.norm, ?_⟩
  obtain ⟨c, d, hfac⟩ := exists_expAffine_mul_hadamardProduct hC hf hf0 hford hbound
  let P := hadamardProduct f
  have hPd : Differentiable ℂ P := fun w =>
    (hadamardProduct_analytic hf hf0 hsum w (mem_univ w)).differentiableAt
  have hlog (w : ℂ) (hw : -1 < w.re) :
      logDeriv f w = c + ∑' i : ZeroCopy f, ((w - zeroCopyPoint f i)⁻¹ + (zeroCopyPoint f i)⁻¹) := by
    have hfw : f w ≠ 0 := fun h => (not_le_of_gt hw) (hleft w h)
    have hwq : ∀ i : ZeroCopy f, w ≠ zeroCopyPoint f i := by
      intro i h
      exact hfw (h ▸ apply_zeroCopyPoint hf i)
    have hPw : P w ≠ 0 := by
      intro h
      apply hfw
      rw [hfac w]
      change Complex.exp (c * w + d) * P w = 0
      rw [h, mul_zero]
    have heq : f = fun u => Complex.exp (c * u + d) * P u := funext hfac
    have hlf : logDeriv f w = logDeriv (fun u => Complex.exp (c * u + d) * P u) w := by
      rw [heq]
    rw [hlf, logDeriv_mul (f := fun u => Complex.exp (c * u + d)) (g := P) w
      (Complex.exp_ne_zero _) hPw (by fun_prop) (hPd w)]
    change logDeriv (fun u => Complex.exp (c * u + d)) w +
      logDeriv (RHTower.canonicalProductE1Indexed (zeroCopyPoint f)) w = _
    rw [RHTower.logDeriv_canonicalProductE1Indexed hane hsum hwq]
    congr 1
    have hd : HasDerivAt (fun u => Complex.exp (c * u + d)) (Complex.exp (c * w + d) * c) w := by
      simpa using (((hasDerivAt_id w).const_mul c).add_const d).cexp
    rw [logDeriv_apply, hd.deriv]
    field_simp
  have heq : logDeriv f =ᶠ[𝓝 z] fun w =>
      c + ∑' i : ZeroCopy f, ((w - zeroCopyPoint f i)⁻¹ + (zeroCopyPoint f i)⁻¹) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz] with w hw
    exact hlog w hw
  rw [heq.iteratedDeriv_eq (n + 1), iteratedDeriv_const_add (Nat.succ_pos n)]
  exact iteratedDeriv_tsum_regularized_resolvent ha hsum n hz

open GaloisForLFunctions.HTGeometry _root_.RHTower

variable {q : ℕ} [NeZero q]

/-- The entire completion of the repulsion auxiliary product. -/
def exceptionalCompletion (χ : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  xi s * (q : ℂ) ^ (s / 2) * DirichletCharacter.completedLFunction χ s

theorem exceptionalCompletion_entire {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) :
    Differentiable ℂ (exceptionalCompletion χ) := by
  have hxi : Differentiable ℂ xi := by
    have heq : xi = riemannXi := funext xi_eq_riemannXi
    rw [heq]
    exact differentiable_riemannXi
  have hpow : Differentiable ℂ (fun s : ℂ => (q : ℂ) ^ (s / 2)) :=
    (differentiable_id.div_const 2).const_cpow (.inl (Nat.cast_ne_zero.mpr (NeZero.ne q)))
  exact (hxi.mul hpow).mul (DirichletCharacter.differentiable_completedLFunction hχ)

theorem exceptionalCompletion_orderOne {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) :
    OrderOneEnvelope (exceptionalCompletion χ) := by
  have hxi : OrderOneEnvelope xi :=
    orderOneEnvelope_riemannXi.congr fun s => (xi_eq_riemannXi s).symm
  have hpow : OrderOneEnvelope (fun s : ℂ => (q : ℂ) ^ (s / 2)) := by
    refine (orderOneEnvelope_exp_mul (Complex.log (q : ℂ) / 2)).congr fun s => ?_
    rw [Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr (NeZero.ne q))]
    congr 1
    ring
  exact (hxi.mul hpow).mul (completedLFunction_orderOneEnvelope hχ)

theorem exceptionalCompletion_reflection {χ : DirichletCharacter ℂ q}
    (hprim : χ.IsPrimitive) (hreal : χ.IsQuadratic) (s : ℂ) :
    exceptionalCompletion χ (1 - s) = χ.rootNumber * exceptionalCompletion χ s := by
  rw [exceptionalCompletion, exceptionalCompletion, xi_one_sub,
    hprim.completedLFunction_one_sub, hreal.inv]
  have hpow : (q : ℂ) ^ ((1 - s) / 2) * (q : ℂ) ^ (s - 1 / 2) = (q : ℂ) ^ (s / 2) := by
    rw [← Complex.cpow_add _ _ (Nat.cast_ne_zero.mpr (NeZero.ne q))]
    congr 1
    ring
  calc
    _ = χ.rootNumber * (xi s * ((q : ℂ) ^ ((1 - s) / 2) * (q : ℂ) ^ (s - 1 / 2)) *
        DirichletCharacter.completedLFunction χ s) := by ring
    _ = _ := by rw [hpow]

theorem exceptionalCompletion_zero_strip {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) {ρ : ℂ} (hρ : exceptionalCompletion χ ρ = 0) :
    0 < ρ.re ∧ ρ.re < 1 := by
  rcases mul_eq_zero.mp hρ with hleft | hL
  · rcases mul_eq_zero.mp hleft with hxi | hpow
    · constructor
      · by_contra h
        have hre : 1 ≤ ((1 : ℂ) - ρ).re := by
          rw [sub_re, one_re]
          linarith only [not_lt.mp h]
        exact xi_ne_zero_of_one_le_re hre (by rw [xi_one_sub]; exact hxi)
      · by_contra h
        exact xi_ne_zero_of_one_le_re (not_lt.mp h) hxi
    · rw [Complex.cpow_eq_zero_iff] at hpow
      exact False.elim ((Nat.cast_ne_zero.mpr (NeZero.ne q)) hpow.1)
  · exact completedLFunction_zero_mem_openUnitStrip hχ hprim hL

theorem exceptionalCompletion_two_ne_zero {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) : exceptionalCompletion χ 2 ≠ 0 := by
  intro h
  have hh := (exceptionalCompletion_zero_strip hχ hprim h).2
  norm_num at hh

/-- Multiplicity copies of the completed divisor, indexed away from a
nonzero point. Central zeros are retained. -/
abbrev ExceptionalZeroCopy (χ : DirichletCharacter ℂ q) :=
  ZeroCopy (fun z : ℂ => exceptionalCompletion χ (z + 2))

def exceptionalZero (χ : DirichletCharacter ℂ q) (i : ExceptionalZeroCopy χ) : ℂ :=
  zeroCopyPoint (fun z : ℂ => exceptionalCompletion χ (z + 2)) i + 2

/-- The complete nontrivial divisor of `ζL(χ)` gives every higher jet of
its entire completion. No nonvanishing at the central point is required. -/
theorem exceptionalCompletion_logarithmic_moments {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) (n : ℕ) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun i : ExceptionalZeroCopy χ => ‖((s - exceptionalZero χ i)⁻¹) ^ (n + 2)‖) ∧
    iteratedDeriv (n + 1) (logDeriv (exceptionalCompletion χ)) s =
      (-1 : ℂ) ^ (n + 1) * ((n + 1).factorial : ℂ) *
        ∑' i : ExceptionalZeroCopy χ, ((s - exceptionalZero χ i)⁻¹) ^ (n + 2) := by
  let f : ℂ → ℂ := fun w => exceptionalCompletion χ (w + 2)
  have hfd : Differentiable ℂ f := (exceptionalCompletion_entire hχ).comp (differentiable_id.add_const 2)
  have hf : AnalyticOnNhd ℂ f univ := hfd.differentiableOn.analyticOnNhd isOpen_univ
  have hf0 : f 0 ≠ 0 := by simpa only [f, zero_add] using exceptionalCompletion_two_ne_zero hχ hprim
  have hfg : OrderOneEnvelope f := by
    simpa only [f, one_mul] using (exceptionalCompletion_orderOne hχ).comp_affine 1 2
  obtain ⟨C, hC, hbound⟩ := hfg
  have hleft (w : ℂ) (hw : f w = 0) : w.re ≤ -1 := by
    have hh := (exceptionalCompletion_zero_strip hχ hprim hw).2
    norm_num at hh
    linarith only [hh]
  have hz : -1 < (s - 2).re := by
    change -1 < s.re - 2
    linarith only [hs]
  have hm := orderOne_entire_logarithmic_moments hC.le hf hf0 hbound hleft n hz
  have harg (u : ℂ) : s - 2 - u = s - (u + 2) := by ring
  simp_rw [harg] at hm
  have hlog : logDeriv f = fun w => logDeriv (exceptionalCompletion χ) (w - (-2)) := by
    funext w
    have heq : f = exceptionalCompletion χ ∘ (fun u : ℂ => u + 2) := rfl
    rw [heq, logDeriv_comp ((exceptionalCompletion_entire hχ) _) (by fun_prop)]
    simp only [deriv_add_const, deriv_id'', mul_one, sub_neg_eq_add]
  rw [hlog, iteratedDeriv_comp_sub_const] at hm
  simpa only [sub_neg_eq_add, sub_add_cancel, f, exceptionalZero, ExceptionalZeroCopy] using! hm

theorem exceptionalZero_is_zero {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1)
    (i : ExceptionalZeroCopy χ) : exceptionalCompletion χ (exceptionalZero χ i) = 0 := by
  have hfd := (exceptionalCompletion_entire hχ).comp (differentiable_id.add_const 2)
  exact RHTower.CompletionZeroPairs.apply_zeroCopyPoint
    (hfd.differentiableOn.analyticOnNhd isOpen_univ) i

theorem exceptionalZero_strip {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) (i : ExceptionalZeroCopy χ) :
    0 < (exceptionalZero χ i).re ∧ (exceptionalZero χ i).re < 1 :=
  exceptionalCompletion_zero_strip hχ hprim (exceptionalZero_is_zero hχ i)

private theorem re_inv_lower {v : ℂ} {α : ℝ} (h : α ≤ v.re) :
    α / ‖v‖ ^ 2 ≤ (v⁻¹).re := by
  rw [inv_re, normSq_eq_norm_sq]
  exact div_le_div_of_nonneg_right h (sq_nonneg _)

/-- Reflection controls the full reciprocal-square mass by the real
logarithmic derivative. No central-value premise or zero truncation occurs. -/
theorem exceptionalCompletion_mass_le_logDeriv {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) (hreal : χ.IsQuadratic)
    {s : ℂ} (hs : 1 < s.re) :
    (s.re - 1) * (∑' i : ExceptionalZeroCopy χ, 1 / ‖s - exceptionalZero χ i‖ ^ 2) ≤
      2 * (logDeriv (exceptionalCompletion χ) s).re := by
  have hEs : exceptionalCompletion χ s ≠ 0 := by
    intro h
    exact (not_lt_of_gt hs) (exceptionalCompletion_zero_strip hχ hprim h).2
  obtain ⟨C, hC, hbound⟩ := exceptionalCompletion_orderOne hχ
  have hpair : HasSum (fun i : ExceptionalZeroCopy χ =>
      (1 / 2 : ℂ) * RHTower.WeilLineIntegral.gPair (exceptionalZero χ i) s)
      (logDeriv (exceptionalCompletion χ) s) := by
    simpa only [ExceptionalZeroCopy, exceptionalZero] using!
      RHTower.CompletionZeroPairs.hasSum_logDeriv_zeroPairs
        (exceptionalCompletion_entire hχ) (rootNumber_ne_zero hprim)
        (exceptionalCompletion_reflection hprim hreal) hC.le hbound
        (exceptionalCompletion_two_ne_zero hχ hprim) hEs
  have hpairRe := hasSum_re hpair
  have hmass : Summable (fun i : ExceptionalZeroCopy χ => 1 / ‖s - exceptionalZero χ i‖ ^ 2) := by
    simpa only [zero_add, norm_pow, norm_inv, inv_pow, one_div] using
      (exceptionalCompletion_logarithmic_moments hχ hprim 0 hs).1
  have hpoint (i : ExceptionalZeroCopy χ) :
      (s.re - 1) * (1 / ‖s - exceptionalZero χ i‖ ^ 2) ≤
        2 * ((1 / 2 : ℂ) * RHTower.WeilLineIntegral.gPair (exceptionalZero χ i) s).re := by
    obtain ⟨hlo, hhi⟩ := exceptionalZero_strip hχ hprim i
    have h₁ := re_inv_lower (v := s - exceptionalZero χ i)
      (show s.re - 1 ≤ (s - exceptionalZero χ i).re by rw [sub_re]; linarith only [hhi])
    have h₂ : 0 ≤ ((s - (1 - exceptionalZero χ i))⁻¹).re := by
      rw [inv_re]
      apply div_nonneg
      · simp only [sub_re, one_re]
        linarith only [hlo, hs]
      · exact normSq_nonneg _
    rw [one_div_mul_eq_div, Complex.div_ofNat_re, RHTower.WeilLineIntegral.gPair, add_re]
    simp only [div_eq_mul_inv, one_mul] at h₁ ⊢
    norm_num only at ⊢
    linarith only [h₁, h₂]
  have hle := Summable.tsum_le_tsum hpoint (hmass.mul_left (s.re - 1)) (hpairRe.summable.mul_left 2)
  rw [tsum_mul_left, tsum_mul_left, hpairRe.tsum_eq] at hle
  exact hle


end GaloisForLFunctions.ExceptionalLayerTheory

#print axioms GaloisForLFunctions.ExceptionalLayerTheory.exceptionalCompletion_logarithmic_moments
#print axioms GaloisForLFunctions.ExceptionalLayerTheory.exceptionalCompletion_mass_le_logDeriv
