import GaloisForLFunctions.SquareRootThreshold.InghamInequalityForSeparatedSpectra

/-!
# Ingham's inequality with tilts

The near-collision constraint of `HidingNeedsNearCollisions` rests on Ingham's inequality for real
frequencies. Tilted points enter the lag structure through complex frequencies `γ_j − iσ_j`, i.e.
through `e^{iγ_j t} e^{σ_j t}`. This module extends Ingham's inequality to them.

* **The tilted kernel** (`tiltedKernel_eq`). With `a = π/(2T)` and `μ = σ + ix`,
  `∫_{−T}^{T} cos(at) e^{μt} dt = 2a cosh(μT)/(μ² + a²)`.
* **Bounds** (`norm_tiltedKernel_le`, `tiltedKernel_diag`). `|K(x, σ)| ≤ 2a cosh(σT)/(x² − σ² − a²)`
  for `x² > σ² + a²`, and the diagonal is `2a cosh(2σT)/(4σ² + a²) ≥ 2a/(4σ² + a²)`.
* **The inequality** (`tilted_ingham_inequality`). For `g`-separated heights `γ_j`, tilts
  `|σ_j| ≤ s`, and `a' = √(a² + 4s²)` with `g > 2a'`:
  `(2a/a'²)(1 − cosh(2sT) B') Σ|c_j|² ≤ ∫_{−T}^{T} |Σ_j c_j e^{iγ_j t} e^{σ_j t}|² dt`,
  `B' = Σ_{n ≥ 1} 2/((g/a')² n² − 1) < 1`.

* **Pairs** (`pairGap_pos`, `block_ingham_inequality`). The two points `γ ∓ iδ` of an FE pair share
  their height, so they form one site with a `2×2` block. Its smallest eigenvalue is the pair gap
  `A(2δ) − A(0)`, `A(σ) = 2a cosh(σT)/(σ² + a²)`. It is positive for `δ ≠ 0` because
  `2a² sinh²(δT) ≥ (π²/2)δ² > 4δ²`, and it is of order `δ²`. For `g`-separated sites with pair gaps
  `≥ D₀`, `(D₀ − 2R) Σ_k (|p_k|² + |q_k|²) ≤ ∫ |Σ_k e^{iγ_k t}(p_k e^{δ_k t} + q_k e^{−δ_k t})|²`,
  `R = 2a cosh(2sT) B'/a'²`. The pair gap is the worst case: it is attained in the antialigned
  direction `p_k = −q_k`. Sites with aligned coefficients, `Re(p_k q̄_k) ≥ 0`, enter with the gap
  `A(0) = 2/a` whatever their depth; this covers sites with one real frequency (`q_k = 0`).
* **Vanishing pair sums** (`eq_zero_of_pairSum_eq_zero`). A summable pair sum vanishing on
  `[−V, V]` has all coefficients zero once the block constant is positive: truncate, and compare
  the block inequality with the small tail.

The constant is positive exactly when `cosh(2sT) B' < 1`: tilts below `~1/T` are resolved like
real frequencies, and the threshold `g > π/T` moves to `g > 2√((π/2T)² + 4s²)`. Deep tilts cost the
factor `cosh(2sT)`: the camera of aperture `T` sees depth `s` with amplitude `e^{sT}`, and this
amplification must be beaten by the separation, as in the depth signal of `TheCameraAndTheTilt`.
For pairs the resolution degenerates like `δ²` as the depth goes to zero: a shallow pair is a
near-collision, and resolving it needs separation of the other sites growing like `1/δ²`.
-/

open Complex MeasureTheory
open scoped ComplexConjugate Real

noncomputable section

namespace GaloisForLFunctions.ZeroConfigurationGeometry

open SquareRootThreshold

/-- The tilted Ingham kernel `∫_{−T}^{T} cos(πt/(2T)) e^{(ix + σ)t} dt`. -/
def tiltedKernel (T x σ : ℝ) : ℂ :=
  ∫ t in -T..T, ((Real.cos (π / (2 * T) * t) : ℝ) : ℂ) * cexp ((I * x + σ) * t)

theorem exp_I_mul_pi_div_two : cexp (I * ((π : ℂ) / 2)) = I := by
  rw [mul_comm, Complex.exp_mul_I,
    show (π : ℂ) / 2 = ((π / 2 : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_cos,
    ← Complex.ofReal_sin, Real.cos_pi_div_two, Real.sin_pi_div_two]
  simp

/-- **The tilted kernel in closed form.** -/
theorem tiltedKernel_eq {T x σ : ℝ} (hT : 0 < T)
    (hμ : ((σ : ℂ) + I * x) ^ 2 + ((π / (2 * T) : ℝ) : ℂ) ^ 2 ≠ 0) :
    tiltedKernel T x σ = 2 * ((π / (2 * T) : ℝ) : ℂ) * Complex.cosh (((σ : ℂ) + I * x) * T) /
      (((σ : ℂ) + I * x) ^ 2 + ((π / (2 * T) : ℝ) : ℂ) ^ 2) := by
  set a : ℝ := π / (2 * T) with ha
  set μ : ℂ := (σ : ℂ) + I * x with hμdef
  have hp : μ + I * a ≠ 0 := fun h => hμ (by
    rw [show μ ^ 2 + (a : ℂ) ^ 2 = (μ + I * a) * (μ - I * a) by ring_nf; rw [Complex.I_sq]; ring, h,
      zero_mul])
  have hm : μ - I * a ≠ 0 := fun h => hμ (by
    rw [show μ ^ 2 + (a : ℂ) ^ 2 = (μ + I * a) * (μ - I * a) by ring_nf; rw [Complex.I_sq]; ring, h,
      mul_zero])
  have hsplit : ∀ t : ℝ, ((Real.cos (a * t) : ℝ) : ℂ) * cexp ((I * x + σ) * t) =
      (cexp ((μ + I * a) * t) + cexp ((μ - I * a) * t)) / 2 := by
    intro t
    rw [Complex.ofReal_cos, Complex.cos,
      show cexp ((μ + I * a) * t) = cexp (((a * t : ℝ) : ℂ) * I) * cexp ((I * x + σ) * t) by
        rw [← Complex.exp_add]; congr 1; rw [hμdef]; push_cast; ring,
      show cexp ((μ - I * a) * t) = cexp (-((a * t : ℝ) : ℂ) * I) * cexp ((I * x + σ) * t) by
        rw [← Complex.exp_add]; congr 1; rw [hμdef]; push_cast; ring]
    push_cast; ring
  have hint : ∀ ν : ℂ, IntervalIntegrable (fun t : ℝ => cexp (ν * t)) volume (-T) T :=
    fun ν => (by fun_prop : Continuous fun t : ℝ => cexp (ν * t)).intervalIntegrable _ _
  rw [tiltedKernel, ← ha]
  simp_rw [hsplit]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_add (hint _) (hint _),
    integral_exp_mul_complex hp, integral_exp_mul_complex hm]
  have hT' : (T : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hT.ne'
  have haT : (a : ℂ) * T = (π : ℂ) / 2 := by
    rw [ha]; push_cast; field_simp
  have e1 : cexp ((μ + I * a) * T) = I * cexp (μ * T) := by
    rw [show (μ + I * a) * T = μ * T + I * ((π : ℂ) / 2) by linear_combination I * haT,
      Complex.exp_add, exp_I_mul_pi_div_two]; ring
  have e2 : cexp ((μ + I * a) * ((-T : ℝ) : ℂ)) = -I * cexp (-(μ * T)) := by
    rw [show (μ + I * a) * ((-T : ℝ) : ℂ) = -(μ * T) + -(I * ((π : ℂ) / 2)) by
      push_cast; linear_combination (-I) * haT, Complex.exp_add, Complex.exp_neg (I * _),
      exp_I_mul_pi_div_two, Complex.inv_I]; ring
  have e3 : cexp ((μ - I * a) * T) = -I * cexp (μ * T) := by
    rw [show (μ - I * a) * T = μ * T + -(I * ((π : ℂ) / 2)) by linear_combination (-I) * haT,
      Complex.exp_add, Complex.exp_neg (I * _), exp_I_mul_pi_div_two, Complex.inv_I]; ring
  have e4 : cexp ((μ - I * a) * ((-T : ℝ) : ℂ)) = I * cexp (-(μ * T)) := by
    rw [show (μ - I * a) * ((-T : ℝ) : ℂ) = -(μ * T) + I * ((π : ℂ) / 2) by
      push_cast; linear_combination I * haT, Complex.exp_add, exp_I_mul_pi_div_two]; ring
  rw [e1, e2, e3, e4, Complex.cosh]
  have hμa : μ ^ 2 + (a : ℂ) ^ 2 = (μ + I * a) * (μ - I * a) := by
    ring_nf; rw [Complex.I_sq]; ring
  rw [hμa]
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

theorem norm_cosh_le (z : ℂ) : ‖Complex.cosh z‖ ≤ Real.cosh z.re := by
  rw [Complex.cosh, Real.cosh_eq, norm_div, Complex.norm_two]
  have h := norm_add_le (cexp z) (cexp (-z))
  rw [Complex.norm_exp, Complex.norm_exp, Complex.neg_re] at h
  linarith

/-- The diagonal of the tilted kernel: `K(0, σ) = 2a cosh(σT)/(σ² + a²)`, real and positive. -/
theorem tiltedKernel_diag {T : ℝ} (hT : 0 < T) (σ : ℝ) :
    tiltedKernel T 0 σ =
      ((2 * (π / (2 * T)) * Real.cosh (σ * T) / (σ ^ 2 + (π / (2 * T)) ^ 2) : ℝ) : ℂ) := by
  have ha : 0 < π / (2 * T) := by positivity
  have hne : ((σ : ℂ) + I * ((0 : ℝ) : ℂ)) ^ 2 + ((π / (2 * T) : ℝ) : ℂ) ^ 2 ≠ 0 := by
    rw [Complex.ofReal_zero, mul_zero, add_zero]
    exact_mod_cast (by positivity : (0 : ℝ) < σ ^ 2 + (π / (2 * T)) ^ 2).ne'
  rw [tiltedKernel_eq hT hne, Complex.ofReal_zero, mul_zero, add_zero]
  push_cast
  rw [← Complex.ofReal_mul, ← Complex.ofReal_cosh]

/-- **The off-diagonal bound.** For `x² > σ² + a²`, `|K(x, σ)| ≤ 2a cosh(σT)/(x² − σ² − a²)`. -/
theorem norm_tiltedKernel_le {T x σ : ℝ} (hT : 0 < T)
    (hx : σ ^ 2 + (π / (2 * T)) ^ 2 < x ^ 2) :
    ‖tiltedKernel T x σ‖ ≤
      2 * (π / (2 * T)) * Real.cosh (σ * T) / (x ^ 2 - σ ^ 2 - (π / (2 * T)) ^ 2) := by
  set a := π / (2 * T) with ha
  have ha0 : 0 < a := by positivity
  set μ : ℂ := (σ : ℂ) + I * x with hμ
  have hre : (μ ^ 2 + (a : ℂ) ^ 2).re = σ ^ 2 - x ^ 2 + a ^ 2 := by
    rw [hμ]; simp [sq, Complex.mul_re]
  have hden : x ^ 2 - σ ^ 2 - a ^ 2 ≤ ‖μ ^ 2 + (a : ℂ) ^ 2‖ := by
    have := Complex.abs_re_le_norm (μ ^ 2 + (a : ℂ) ^ 2)
    rw [hre, abs_of_neg (by linarith)] at this
    linarith
  have hne : μ ^ 2 + (a : ℂ) ^ 2 ≠ 0 := fun h => by
    rw [h, norm_zero] at hden; linarith
  have hcosh : ‖Complex.cosh (μ * T)‖ ≤ Real.cosh (σ * T) := by
    refine (norm_cosh_le _).trans (le_of_eq ?_)
    congr 1; rw [hμ]; simp
  rw [tiltedKernel_eq hT hne, norm_div, norm_mul, norm_mul, Complex.norm_two, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos ha0]
  have hpos : 0 < x ^ 2 - σ ^ 2 - a ^ 2 := by linarith
  rw [div_le_div_iff₀ (lt_of_lt_of_le hpos hden) hpos]
  have h1 : 2 * a * ‖Complex.cosh (μ * T)‖ * (x ^ 2 - σ ^ 2 - a ^ 2) ≤
      2 * a * Real.cosh (σ * T) * (x ^ 2 - σ ^ 2 - a ^ 2) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcosh (by positivity)) hpos.le
  have h2 : 2 * a * Real.cosh (σ * T) * (x ^ 2 - σ ^ 2 - a ^ 2) ≤
      2 * a * Real.cosh (σ * T) * ‖μ ^ 2 + (a : ℂ) ^ 2‖ :=
    mul_le_mul_of_nonneg_left hden (by positivity)
  linarith

/-- **The weighted mean square as a quadratic form in the tilted kernel.** -/
theorem integral_cos_mul_normSq_tiltedSum {ι : Type*} [Fintype ι] (γ σ : ι → ℝ) (c : ι → ℂ)
    (T : ℝ) :
    ∫ t in -T..T, Real.cos (π / (2 * T) * t) * ‖∑ j, c j * cexp ((I * γ j + σ j) * t)‖ ^ 2 =
      (∑ j, ∑ l, c j * conj (c l) * tiltedKernel T (γ j - γ l) (σ j + σ l)).re := by
  set G : ℝ → ℂ := fun t => ∑ j, ∑ l, c j * conj (c l) *
    (((Real.cos (π / (2 * T) * t) : ℝ) : ℂ) *
      cexp ((I * ((γ j - γ l : ℝ) : ℂ) + ((σ j + σ l : ℝ) : ℂ)) * t)) with hG
  have hpt : ∀ t : ℝ, Real.cos (π / (2 * T) * t) * ‖∑ j, c j * cexp ((I * γ j + σ j) * t)‖ ^ 2 =
      (G t).re := by
    intro t
    have hn : ‖∑ j, c j * cexp ((I * γ j + σ j) * t)‖ ^ 2 =
        ((∑ j, c j * cexp ((I * γ j + σ j) * t)) *
          conj (∑ j, c j * cexp ((I * γ j + σ j) * t))).re := by
      rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
    rw [hn, ← Complex.re_ofReal_mul, hG, map_sum, Finset.sum_mul, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_mul, ← Complex.exp_conj, map_mul, map_add, map_mul, Complex.conj_I,
      Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_ofReal]
    rw [show cexp ((I * ((γ j - γ l : ℝ) : ℂ) + ((σ j + σ l : ℝ) : ℂ)) * t) =
      cexp ((I * γ j + σ j) * t) * cexp ((-I * γ l + σ l) * t) by
        rw [← Complex.exp_add]; congr 1; push_cast; ring]
    ring
  have hcont : Continuous G := by rw [hG]; fun_prop
  rw [intervalIntegral.integral_congr (fun t _ => hpt t),
    show (∫ t in -T..T, (G t).re) = (∫ t in -T..T, G t).re from
      intervalIntegral.intervalIntegral_re (hcont.intervalIntegrable _ _), hG]
  congr 1
  rw [intervalIntegral.integral_finsetSum fun j _ =>
    (by fun_prop : Continuous fun t : ℝ => ∑ l, c j * conj (c l) *
      (((Real.cos (π / (2 * T) * t) : ℝ) : ℂ) *
        cexp ((I * ((γ j - γ l : ℝ) : ℂ) + ((σ j + σ l : ℝ) : ℂ)) * t))).intervalIntegrable _ _]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [intervalIntegral.integral_finsetSum fun l _ =>
    (by fun_prop : Continuous fun t : ℝ => c j * conj (c l) *
      (((Real.cos (π / (2 * T) * t) : ℝ) : ℂ) *
        cexp ((I * ((γ j - γ l : ℝ) : ℂ) + ((σ j + σ l : ℝ) : ℂ)) * t))).intervalIntegrable _ _]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [intervalIntegral.integral_const_mul, tiltedKernel]

/-- The tilted Ingham constant `(2a/a'²)(1 − cosh(2sT) B')`, `a = π/(2T)`, `a' = √(a² + 4s²)`,
`B' = Σ_{n ≥ 1} 2/((g/a')²n² − 1)`. -/
def tiltedInghamConst (T g s : ℝ) : ℝ :=
  2 * (π / (2 * T)) / (Real.sqrt ((π / (2 * T)) ^ 2 + 4 * s ^ 2)) ^ 2 *
    (1 - Real.cosh (2 * s * T) * ∑' n : ℕ,
      2 / ((g / Real.sqrt ((π / (2 * T)) ^ 2 + 4 * s ^ 2)) ^ 2 * ((n : ℝ) + 1) ^ 2 - 1))

/-- **Ingham's inequality with tilts.** -/
theorem tilted_ingham_inequality {ι : Type*} [Fintype ι] (γ σ : ι → ℝ) (c : ι → ℂ) {g T s : ℝ}
    (hg : 0 < g) (hT : 0 < T) (hs : 0 ≤ s) (hσ : ∀ j, |σ j| ≤ s)
    (hsep : ∀ j l, j ≠ l → g ≤ |γ j - γ l|)
    (hgap : 2 * Real.sqrt ((π / (2 * T)) ^ 2 + 4 * s ^ 2) < g) :
    tiltedInghamConst T g s * ∑ j, ‖c j‖ ^ 2 ≤
      ∫ t in -T..T, ‖∑ j, c j * cexp ((I * γ j + σ j) * t)‖ ^ 2 := by
  classical
  set a := π / (2 * T) with ha
  have ha0 : 0 < a := by positivity
  set a' := Real.sqrt (a ^ 2 + 4 * s ^ 2) with ha'
  have ha'0 : 0 < a' := Real.sqrt_pos.mpr (by positivity)
  have ha'sq : a' ^ 2 = a ^ 2 + 4 * s ^ 2 := Real.sq_sqrt (by positivity)
  set b := g / a' with hb
  have hb2 : 2 < b := by rw [hb, lt_div_iff₀ ha'0]; linarith
  have hgab : g = b * a' := by rw [hb]; field_simp
  obtain ⟨hbs, -⟩ := tsum_two_div_sq_sub_one_lt_one hb2
  set B := ∑' n : ℕ, (2 : ℝ) / (b ^ 2 * ((n : ℝ) + 1) ^ 2 - 1) with hB
  set K := Real.cosh (2 * s * T) with hK
  have hga' : a' < g := by linarith
  -- the comparison function
  set ψ : ℝ → ℝ := fun x => 2 * a * K / (x ^ 2 - a' ^ 2) with hψ
  have hK0 : 0 < K := Real.cosh_pos _
  have hψ0 : ∀ x, g ≤ x → 0 ≤ ψ x := fun x hx =>
    div_nonneg (by positivity) (by nlinarith)
  have hψmono : ∀ x y, g ≤ x → x ≤ y → ψ y ≤ ψ x := fun x y hx hxy =>
    div_le_div_of_nonneg_left (by positivity) (by nlinarith) (by nlinarith)
  have hψn : ∀ n : ℕ, ψ (((n : ℝ) + 1) * g) =
      a * K / a' ^ 2 * (2 / (b ^ 2 * ((n : ℝ) + 1) ^ 2 - 1)) := by
    intro n
    have hpos : 0 < b ^ 2 * ((n : ℝ) + 1) ^ 2 - 1 := by
      have : (4 : ℝ) ≤ b ^ 2 := by nlinarith
      nlinarith [sq_nonneg ((n : ℝ) + 1), (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    rw [hψ, hgab]
    simp only
    rw [show (((n : ℝ) + 1) * (b * a')) ^ 2 - a' ^ 2 =
      a' ^ 2 * (b ^ 2 * ((n : ℝ) + 1) ^ 2 - 1) by ring]
    field_simp
  have hψs : Summable fun n : ℕ => ψ (((n : ℝ) + 1) * g) :=
    (hbs.mul_left (a * K / a' ^ 2)).congr fun n => (hψn n).symm
  have hψt : 2 * ∑' n : ℕ, ψ (((n : ℝ) + 1) * g) = 2 * a * K / a' ^ 2 * B := by
    rw [tsum_congr hψn, tsum_mul_left, hB]
    ring
  have hrow : ∀ j, ∑ l ∈ Finset.univ.filter (· ≠ j), ψ |γ j - γ l| ≤ 2 * a * K / a' ^ 2 * B :=
    fun j => (sum_offDiag_le_two_tsum γ hg hsep hψ0 hψmono hψs j).trans_eq hψt
  have hk : ∀ j l, j ≠ l → ‖tiltedKernel T (γ j - γ l) (σ j + σ l)‖ ≤ ψ |γ j - γ l| := by
    intro j l hjl
    have hd := hsep j l hjl
    have hσs : |σ j + σ l| ≤ 2 * s := (abs_add_le _ _).trans (by linarith [hσ j, hσ l])
    have hσsq : (σ j + σ l) ^ 2 ≤ 4 * s ^ 2 := by
      rw [← sq_abs]; nlinarith [abs_nonneg (σ j + σ l)]
    have hx : (σ j + σ l) ^ 2 + a ^ 2 < (γ j - γ l) ^ 2 := by
      rw [← sq_abs (γ j - γ l)]; nlinarith
    have h := norm_tiltedKernel_le hT hx
    rw [← ha] at h
    refine h.trans ?_
    rw [hψ]
    simp only
    rw [sq_abs]
    have hnum : Real.cosh ((σ j + σ l) * T) ≤ K := by
      rw [hK, Real.cosh_le_cosh, abs_mul, abs_mul, abs_of_pos hT, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * s)]
      exact mul_le_mul_of_nonneg_right hσs hT.le
    have hden1 : 0 < (γ j - γ l) ^ 2 - a' ^ 2 := by
      rw [← sq_abs (γ j - γ l)]; nlinarith
    have hden2 : (γ j - γ l) ^ 2 - a' ^ 2 ≤ (γ j - γ l) ^ 2 - (σ j + σ l) ^ 2 - a ^ 2 := by
      rw [ha'sq]; linarith
    exact div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hnum (by positivity)) hden1 hden2
  -- the weight `cos(at) ≤ 1`
  set f : ℝ → ℂ := fun t => ∑ j, c j * cexp ((I * γ j + σ j) * t) with hf
  have hfc : Continuous fun t => ‖f t‖ ^ 2 := by rw [hf]; fun_prop
  have h1 : ∫ t in -T..T, Real.cos (a * t) * ‖f t‖ ^ 2 ≤ ∫ t in -T..T, ‖f t‖ ^ 2 :=
    intervalIntegral.integral_mono_on (by linarith)
      ((show Continuous fun t : ℝ => Real.cos (a * t) * ‖f t‖ ^ 2 from
        (Real.continuous_cos.comp (continuous_const.mul continuous_id)).mul hfc).intervalIntegrable _ _)
      (hfc.intervalIntegrable _ _) fun t _ =>
        mul_le_of_le_one_left (by positivity) (Real.cos_le_one _)
  have hQ := integral_cos_mul_normSq_tiltedSum γ σ c T
  rw [← ha] at hQ
  refine le_trans ?_ (hQ ▸ h1)
  -- the quadratic form is bounded below
  rw [Complex.re_sum]
  have hX : ∀ j, (∑ l, c j * conj (c l) * tiltedKernel T (γ j - γ l) (σ j + σ l)).re ≥
      2 * a / a' ^ 2 * ‖c j‖ ^ 2 -
        ∑ l ∈ Finset.univ.filter (· ≠ j), ‖c j‖ * ‖c l‖ * ψ |γ j - γ l| := by
    intro j
    rw [Finset.filter_ne', ← Finset.add_sum_erase _ _ (Finset.mem_univ j), Complex.add_re,
      Complex.re_sum, sub_self, tiltedKernel_diag hT, Complex.mul_conj, ← Complex.ofReal_mul,
      Complex.ofReal_re, Complex.normSq_eq_norm_sq]
    rw [← ha]
    have hdiag : 2 * a / a' ^ 2 * ‖c j‖ ^ 2 ≤
        ‖c j‖ ^ 2 * (2 * a * Real.cosh ((σ j + σ j) * T) / ((σ j + σ j) ^ 2 + a ^ 2)) := by
      have hc1 : 1 ≤ Real.cosh ((σ j + σ j) * T) := Real.one_le_cosh _
      have hDj : (σ j + σ j) ^ 2 + a ^ 2 ≤ a' ^ 2 := by
        rw [ha'sq]
        have : (σ j + σ j) ^ 2 = 4 * σ j ^ 2 := by ring
        have : σ j ^ 2 ≤ s ^ 2 := by rw [← sq_abs (σ j)]; nlinarith [hσ j, abs_nonneg (σ j)]
        nlinarith
      have hDj0 : 0 < (σ j + σ j) ^ 2 + a ^ 2 := by positivity
      have hle : 2 * a / a' ^ 2 ≤
          2 * a * Real.cosh ((σ j + σ j) * T) / ((σ j + σ j) ^ 2 + a ^ 2) :=
        div_le_div₀ (by positivity) (le_mul_of_one_le_right (by positivity) hc1) hDj0 hDj
      calc 2 * a / a' ^ 2 * ‖c j‖ ^ 2 = ‖c j‖ ^ 2 * (2 * a / a' ^ 2) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hle (sq_nonneg _)
    have hoff : ∀ l ∈ Finset.univ.erase j, -(‖c j‖ * ‖c l‖ * ψ |γ j - γ l|) ≤
        (c j * conj (c l) * tiltedKernel T (γ j - γ l) (σ j + σ l)).re := fun l hl => by
      have hne : j ≠ l := (Finset.ne_of_mem_erase hl).symm
      have h := (abs_le.mp (Complex.abs_re_le_norm
        (c j * conj (c l) * tiltedKernel T (γ j - γ l) (σ j + σ l)))).1
      rw [norm_mul, norm_mul, Complex.norm_conj] at h
      have := hk j l hne
      nlinarith [norm_nonneg (c j), norm_nonneg (c l),
        mul_nonneg (norm_nonneg (c j)) (norm_nonneg (c l)),
        norm_nonneg (tiltedKernel T (γ j - γ l) (σ j + σ l))]
    have hsoff := Finset.sum_le_sum hoff
    rw [Finset.sum_neg_distrib] at hsoff
    linarith only [hdiag, hsoff]
  have hswap : ∀ F : ι → ι → ℝ, ∑ j, ∑ l ∈ Finset.univ.filter (· ≠ j), F j l =
      ∑ l, ∑ j ∈ Finset.univ.filter (· ≠ l), F j l := by
    intro F
    simp only [Finset.sum_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => ?_
    by_cases h : j = l
    · subst h; simp
    · simp [h, Ne.symm h]
  have hschur : ∑ j, ∑ l ∈ Finset.univ.filter (· ≠ j), ‖c j‖ * ‖c l‖ * ψ |γ j - γ l| ≤
      2 * a * K / a' ^ 2 * B * ∑ j, ‖c j‖ ^ 2 := by
    have hamgm : ∀ j, ∀ l ∈ Finset.univ.filter (· ≠ j), ‖c j‖ * ‖c l‖ * ψ |γ j - γ l| ≤
        ‖c j‖ ^ 2 * ψ |γ j - γ l| / 2 + ‖c l‖ ^ 2 * ψ |γ j - γ l| / 2 := fun j l hl => by
      have hψ' : 0 ≤ ψ |γ j - γ l| :=
        hψ0 _ (hsep j l (Ne.symm (Finset.mem_filter.mp hl).2))
      nlinarith [sq_nonneg (‖c j‖ - ‖c l‖), mul_nonneg hψ' (sq_nonneg (‖c j‖ - ‖c l‖))]
    have hfirst : ∑ j, ∑ l ∈ Finset.univ.filter (· ≠ j), ‖c j‖ ^ 2 * ψ |γ j - γ l| / 2 ≤
        2 * a * K / a' ^ 2 * B * ∑ j, ‖c j‖ ^ 2 / 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun j _ => ?_
      rw [← Finset.sum_div, ← Finset.mul_sum]
      have := mul_le_mul_of_nonneg_left (hrow j) (sq_nonneg ‖c j‖)
      linarith
    have hsecond : ∑ j, ∑ l ∈ Finset.univ.filter (· ≠ j), ‖c l‖ ^ 2 * ψ |γ j - γ l| / 2 ≤
        2 * a * K / a' ^ 2 * B * ∑ j, ‖c j‖ ^ 2 / 2 := by
      rw [hswap (fun j l => ‖c l‖ ^ 2 * ψ |γ j - γ l| / 2), Finset.mul_sum]
      refine Finset.sum_le_sum fun l _ => ?_
      rw [← Finset.sum_div, ← Finset.mul_sum]
      have hr := hrow l
      have hrow' : ∑ j ∈ Finset.univ.filter (· ≠ l), ψ |γ j - γ l| ≤ 2 * a * K / a' ^ 2 * B := by
        simpa only [abs_sub_comm] using hr
      have := mul_le_mul_of_nonneg_left hrow' (sq_nonneg ‖c l‖)
      linarith
    calc ∑ j, ∑ l ∈ Finset.univ.filter (· ≠ j), ‖c j‖ * ‖c l‖ * ψ |γ j - γ l|
        ≤ ∑ j, ∑ l ∈ Finset.univ.filter (· ≠ j),
            (‖c j‖ ^ 2 * ψ |γ j - γ l| / 2 + ‖c l‖ ^ 2 * ψ |γ j - γ l| / 2) :=
          Finset.sum_le_sum fun j _ => Finset.sum_le_sum (hamgm j)
      _ = ∑ j, ∑ l ∈ Finset.univ.filter (· ≠ j), ‖c j‖ ^ 2 * ψ |γ j - γ l| / 2 +
          ∑ j, ∑ l ∈ Finset.univ.filter (· ≠ j), ‖c l‖ ^ 2 * ψ |γ j - γ l| / 2 := by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun j _ => Finset.sum_add_distrib
      _ ≤ 2 * a * K / a' ^ 2 * B * ∑ j, ‖c j‖ ^ 2 / 2 +
          2 * a * K / a' ^ 2 * B * ∑ j, ‖c j‖ ^ 2 / 2 := add_le_add hfirst hsecond
      _ = 2 * a * K / a' ^ 2 * B * ∑ j, ‖c j‖ ^ 2 := by rw [← Finset.sum_div]; ring
  have hsum := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => hX j
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at hsum
  have hc : tiltedInghamConst T g s = 2 * a / a' ^ 2 * (1 - K * B) := by
    rw [tiltedInghamConst, hB, hb, ha', hK, ha]
  have : 2 * a / a' ^ 2 * (1 - K * B) * ∑ j, ‖c j‖ ^ 2 =
      2 * a / a' ^ 2 * ∑ j, ‖c j‖ ^ 2 - 2 * a * K / a' ^ 2 * B * ∑ j, ‖c j‖ ^ 2 := by ring
  rw [hc]
  linarith

/-- The constant is positive when the amplification `cosh(2sT)` is beaten by the separation. -/
theorem tiltedInghamConst_pos {T g s : ℝ} (hT : 0 < T)
    (hcond : Real.cosh (2 * s * T) * ∑' n : ℕ,
      2 / ((g / Real.sqrt ((π / (2 * T)) ^ 2 + 4 * s ^ 2)) ^ 2 * ((n : ℝ) + 1) ^ 2 - 1) < 1) :
    0 < tiltedInghamConst T g s := by
  have ha0 : 0 < π / (2 * T) := by positivity
  have ha'0 : 0 < Real.sqrt ((π / (2 * T)) ^ 2 + 4 * s ^ 2) := Real.sqrt_pos.mpr (by positivity)
  unfold tiltedInghamConst
  exact mul_pos (by positivity) (by linarith)

/-! ### Pairs: the block inequality -/

/-- The off-diagonal kernel bound in the form used by the Schur argument. -/
theorem norm_tiltedKernel_le_of_sep {T g s x σ : ℝ} (hT : 0 < T) (hs : 0 ≤ s)
    (hgap : 2 * Real.sqrt ((π / (2 * T)) ^ 2 + 4 * s ^ 2) < g) (hx : g ≤ |x|)
    (hσ : |σ| ≤ 2 * s) :
    ‖tiltedKernel T x σ‖ ≤ 2 * (π / (2 * T)) * Real.cosh (2 * s * T) /
      (x ^ 2 - (Real.sqrt ((π / (2 * T)) ^ 2 + 4 * s ^ 2)) ^ 2) := by
  set a := π / (2 * T) with ha
  have ha0 : 0 < a := by positivity
  set a' := Real.sqrt (a ^ 2 + 4 * s ^ 2) with ha'
  have ha'0 : 0 < a' := Real.sqrt_pos.mpr (by positivity)
  have ha'sq : a' ^ 2 = a ^ 2 + 4 * s ^ 2 := Real.sq_sqrt (by positivity)
  have hσsq : σ ^ 2 ≤ 4 * s ^ 2 := by rw [← sq_abs]; nlinarith [abs_nonneg σ]
  have hxx : a' ^ 2 < x ^ 2 := by rw [← sq_abs x]; nlinarith
  have hx' : σ ^ 2 + a ^ 2 < x ^ 2 := by nlinarith
  have h := norm_tiltedKernel_le hT hx'
  rw [← ha] at h
  refine h.trans ?_
  have hnum : Real.cosh (σ * T) ≤ Real.cosh (2 * s * T) := by
    rw [Real.cosh_le_cosh, abs_mul, abs_mul, abs_of_pos hT,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * s)]
    exact mul_le_mul_of_nonneg_right hσ hT.le
  have hden1 : 0 < x ^ 2 - a' ^ 2 := by linarith
  have hden2 : x ^ 2 - a' ^ 2 ≤ x ^ 2 - σ ^ 2 - a ^ 2 := by rw [ha'sq]; linarith
  exact div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hnum (by positivity)) hden1 hden2

/-- The diagonal gap of a pair: `A(2δ) − A(0)`, `A(σ) = 2a cosh(σT)/(σ² + a²)`. -/
def pairGap (T δ : ℝ) : ℝ :=
  2 * (π / (2 * T)) * Real.cosh (2 * δ * T) / ((2 * δ) ^ 2 + (π / (2 * T)) ^ 2) -
    2 * (π / (2 * T)) / (π / (2 * T)) ^ 2

/-- **A tilted pair is resolved from its doubled centre.** The diagonal gap is positive for
`δ ≠ 0` (`π²/2 > 4`), and of order `δ²` near a collision. -/
theorem pairGap_pos {T δ : ℝ} (hT : 0 < T) (hδ : δ ≠ 0) : 0 < pairGap T δ := by
  set a := π / (2 * T) with ha
  have ha0 : 0 < a := by positivity
  have haT : a * T = π / 2 := by rw [ha]; field_simp
  unfold pairGap
  rw [← ha]
  have hD : 0 < (2 * δ) ^ 2 + a ^ 2 := by positivity
  rw [sub_pos, div_lt_div_iff₀ (by positivity) hD]
  -- `cosh(2δT) a² > 4δ² + a²` from `cosh(2x) = 1 + 2 sinh² x ≥ 1 + 2x²`
  have hsh : δ * T ≤ |Real.sinh (δ * T)| := by
    rcases le_total 0 (δ * T) with h | h
    · rw [abs_of_nonneg (Real.sinh_nonneg_iff.mpr h)]; exact Real.self_le_sinh_iff.mpr h
    · exact h.trans (abs_nonneg _)
  have hsh2 : (δ * T) ^ 2 ≤ Real.sinh (δ * T) ^ 2 := by
    rw [← sq_abs (Real.sinh _)]
    rcases le_total 0 (δ * T) with h | h
    · exact pow_le_pow_left₀ h hsh 2
    · have : -(δ * T) ≤ |Real.sinh (δ * T)| := by
        rw [abs_of_nonpos (Real.sinh_nonpos_iff.mpr h)]
        have := Real.self_le_sinh_iff.mpr (neg_nonneg.mpr h)
        rw [Real.sinh_neg] at this; linarith
      rw [← neg_sq]; exact pow_le_pow_left₀ (by linarith) this 2
  have hcosh : Real.cosh (2 * δ * T) = 1 + 2 * Real.sinh (δ * T) ^ 2 := by
    rw [show 2 * δ * T = 2 * (δ * T) by ring, Real.cosh_two_mul, Real.cosh_sq]; ring
  have hpi : (8 : ℝ) < π ^ 2 := by nlinarith [Real.pi_gt_three]
  have hδT : 0 < (δ * T) ^ 2 := by positivity
  have key : 4 * δ ^ 2 < 2 * a ^ 2 * (δ * T) ^ 2 := by
    have : a ^ 2 * T ^ 2 = π ^ 2 / 4 := by rw [← mul_pow, haT]; ring
    have hδ2 : 0 < δ ^ 2 := by positivity
    nlinarith
  rw [hcosh]
  nlinarith [mul_le_mul_of_nonneg_left hsh2 (by positivity : (0 : ℝ) ≤ 2 * a ^ 2)]

theorem pairGap_nonneg {T : ℝ} (hT : 0 < T) (δ : ℝ) : 0 ≤ pairGap T δ := by
  rcases eq_or_ne δ 0 with h | h
  · subst h; simp [pairGap]
  · exact (pairGap_pos hT h).le

/-- `a = π/(2T)`. -/
def inghamA (T : ℝ) : ℝ := π / (2 * T)

/-- `a' = √(a² + 4s²)`. -/
def tiltA (T s : ℝ) : ℝ := Real.sqrt (inghamA T ^ 2 + 4 * s ^ 2)

/-- `B' = Σ_{n ≥ 1} 2/((g/a')²n² − 1)`. -/
def tiltB (T g s : ℝ) : ℝ := ∑' n : ℕ, 2 / ((g / tiltA T s) ^ 2 * ((n : ℝ) + 1) ^ 2 - 1)

/-- The comparison function `ψ(x) = 2a cosh(2sT)/(x² − a'²)`. -/
def tiltPsi (T s x : ℝ) : ℝ := 2 * inghamA T * Real.cosh (2 * s * T) / (x ^ 2 - tiltA T s ^ 2)

/-- **Row sums of the comparison function.** -/
theorem tilted_rowSum_le {ι : Type*} [Fintype ι] [DecidableEq ι] (γ : ι → ℝ) {g T s : ℝ}
    (hg : 0 < g) (hT : 0 < T) (hsep : ∀ j l, j ≠ l → g ≤ |γ j - γ l|)
    (hgap : 2 * tiltA T s < g) (j : ι) :
    ∑ l ∈ Finset.univ.filter (· ≠ j), tiltPsi T s |γ j - γ l| ≤
      2 * inghamA T * Real.cosh (2 * s * T) / tiltA T s ^ 2 * tiltB T g s := by
  have ha0 : 0 < inghamA T := by unfold inghamA; positivity
  have ha'0 : 0 < tiltA T s := Real.sqrt_pos.mpr (by positivity)
  set a := inghamA T
  set a' := tiltA T s
  set K := Real.cosh (2 * s * T)
  have hK0 : 0 < K := Real.cosh_pos _
  set b := g / a' with hb
  have hb2 : 2 < b := by rw [hb, lt_div_iff₀ ha'0]; linarith
  have hgab : g = b * a' := by rw [hb]; field_simp
  obtain ⟨hbs, -⟩ := tsum_two_div_sq_sub_one_lt_one hb2
  have hga' : a' < g := by linarith
  have hψ0 : ∀ x, g ≤ x → 0 ≤ tiltPsi T s x := fun x hx =>
    div_nonneg (by positivity) (by nlinarith)
  have hψmono : ∀ x y, g ≤ x → x ≤ y → tiltPsi T s y ≤ tiltPsi T s x := fun x y hx hxy =>
    div_le_div_of_nonneg_left (by positivity) (by nlinarith) (by nlinarith)
  have hψn : ∀ n : ℕ, tiltPsi T s (((n : ℝ) + 1) * g) =
      a * K / a' ^ 2 * (2 / (b ^ 2 * ((n : ℝ) + 1) ^ 2 - 1)) := by
    intro n
    have hpos : 0 < b ^ 2 * ((n : ℝ) + 1) ^ 2 - 1 := by
      have : (4 : ℝ) ≤ b ^ 2 := by nlinarith
      nlinarith [sq_nonneg ((n : ℝ) + 1), (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    show 2 * a * K / ((((n : ℝ) + 1) * g) ^ 2 - a' ^ 2) = _
    rw [hgab, show (((n : ℝ) + 1) * (b * a')) ^ 2 - a' ^ 2 =
      a' ^ 2 * (b ^ 2 * ((n : ℝ) + 1) ^ 2 - 1) by ring]
    field_simp
  have hψs : Summable fun n : ℕ => tiltPsi T s (((n : ℝ) + 1) * g) :=
    (hbs.mul_left (a * K / a' ^ 2)).congr fun n => (hψn n).symm
  have hψt : 2 * ∑' n : ℕ, tiltPsi T s (((n : ℝ) + 1) * g) = 2 * a * K / a' ^ 2 * tiltB T g s := by
    rw [tsum_congr hψn, tsum_mul_left, tiltB]
    ring
  exact (sum_offDiag_le_two_tsum γ hg hsep hψ0 hψmono hψs j).trans_eq hψt

/-- **Schur bound.** For symmetric nonnegative weights with row sums at most `R`,
`Σ_k Σ_{l ≠ k} w_k w_l ψ_{kl} ≤ R Σ_k w_k²`. -/
theorem schur_offDiag_le {ι : Type*} [Fintype ι] [DecidableEq ι] (w : ι → ℝ) (ψ : ι → ι → ℝ)
    (hψ0 : ∀ k l, k ≠ l → 0 ≤ ψ k l) (hsymm : ∀ k l, ψ k l = ψ l k) {R : ℝ}
    (hrow : ∀ k, ∑ l ∈ Finset.univ.filter (· ≠ k), ψ k l ≤ R) :
    ∑ k, ∑ l ∈ Finset.univ.filter (· ≠ k), w k * w l * ψ k l ≤ R * ∑ k, w k ^ 2 := by
  have hamgm : ∀ k, ∀ l ∈ Finset.univ.filter (· ≠ k), w k * w l * ψ k l ≤
      w k ^ 2 * ψ k l / 2 + w l ^ 2 * ψ k l / 2 := fun k l hl => by
    have h := hψ0 k l (Ne.symm (Finset.mem_filter.mp hl).2)
    nlinarith [mul_nonneg h (sq_nonneg (w k - w l))]
  have hswap : ∑ k, ∑ l ∈ Finset.univ.filter (· ≠ k), w l ^ 2 * ψ k l / 2 =
      ∑ l, ∑ k ∈ Finset.univ.filter (· ≠ l), w l ^ 2 * ψ l k / 2 := by
    simp only [Finset.sum_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
    by_cases h : k = l
    · subst h; simp
    · simp [h, Ne.symm h, hsymm k l]
  have hrow' : ∀ k, ∑ l ∈ Finset.univ.filter (· ≠ k), w k ^ 2 * ψ k l / 2 ≤ R * (w k ^ 2 / 2) :=
    fun k => by
      rw [← Finset.sum_div, ← Finset.mul_sum]
      have := mul_le_mul_of_nonneg_left (hrow k) (sq_nonneg (w k))
      linarith
  calc ∑ k, ∑ l ∈ Finset.univ.filter (· ≠ k), w k * w l * ψ k l
      ≤ ∑ k, ∑ l ∈ Finset.univ.filter (· ≠ k), (w k ^ 2 * ψ k l / 2 + w l ^ 2 * ψ k l / 2) :=
        Finset.sum_le_sum fun k _ => Finset.sum_le_sum (hamgm k)
    _ = ∑ k, ∑ l ∈ Finset.univ.filter (· ≠ k), w k ^ 2 * ψ k l / 2 +
        ∑ k, ∑ l ∈ Finset.univ.filter (· ≠ k), w l ^ 2 * ψ k l / 2 := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun k _ => Finset.sum_add_distrib
    _ ≤ ∑ k, R * (w k ^ 2 / 2) + ∑ k, R * (w k ^ 2 / 2) := by
        rw [hswap]
        exact add_le_add (Finset.sum_le_sum fun k _ => hrow' k)
          (Finset.sum_le_sum fun k _ => hrow' k)
    _ = R * ∑ k, w k ^ 2 := by
        rw [← Finset.sum_add_distrib, Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring

theorem tiltB_nonneg {T g s : ℝ} (hT : 0 < T) (hgap : 2 * tiltA T s < g) : 0 ≤ tiltB T g s := by
  have ha'0 : 0 < tiltA T s := Real.sqrt_pos.mpr (by unfold inghamA; positivity)
  have hb2 : 2 < g / tiltA T s := by rw [lt_div_iff₀ ha'0]; linarith
  refine tsum_nonneg fun n => div_nonneg (by norm_num) ?_
  have : (4 : ℝ) ≤ (g / tiltA T s) ^ 2 := by nlinarith
  nlinarith [sq_nonneg ((n : ℝ) + 1), (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

/-- **The block Ingham inequality for pairs.** Sites `k` at `g`-separated heights `γ_k`, each
carrying the FE pair of frequencies `γ_k ∓ iδ_k` with coefficients `p_k, q_k` and `|δ_k| ≤ s`. If
every pair gap `A(2δ_k) − A(0)` is at least `D₀` (or the site has aligned coefficients,
`Re(p_k q̄_k) ≥ 0`, and `D₀ ≤ A(0) = 2/a`), then
`(D₀ − 2R) Σ_k (|p_k|² + |q_k|²) ≤ ∫_{−T}^{T} |Σ_k e^{iγ_k t}(p_k e^{δ_k t} + q_k e^{−δ_k t})|² dt`,
`R = 2a cosh(2sT) B'/a'²`. -/
theorem block_ingham_inequality {ι : Type*} [Fintype ι] [DecidableEq ι] (γ δ : ι → ℝ)
    (p q : ι → ℂ) {g T s D₀ : ℝ} (hg : 0 < g) (hT : 0 < T) (hs : 0 ≤ s)
    (hδ : ∀ k, |δ k| ≤ s) (hsep : ∀ j l, j ≠ l → g ≤ |γ j - γ l|) (hgap : 2 * tiltA T s < g)
    (hD : ∀ k, D₀ ≤ pairGap T (δ k) ∨ (D₀ ≤ 2 / inghamA T ∧ 0 ≤ (p k * conj (q k)).re)) :
    (D₀ - 2 * (2 * inghamA T * Real.cosh (2 * s * T) / tiltA T s ^ 2 * tiltB T g s)) *
        ∑ k, (‖p k‖ ^ 2 + ‖q k‖ ^ 2) ≤
      ∫ t in -T..T, ‖∑ k, cexp (I * γ k * t) *
        (p k * cexp ((δ k : ℂ) * t) + q k * cexp (-(δ k : ℂ) * t))‖ ^ 2 := by
  classical
  -- the pair sum as a tilted sum over `ι × Bool`
  set c' : ι × Bool → ℂ := fun x => if x.2 then p x.1 else q x.1 with hc'
  set γ' : ι × Bool → ℝ := fun x => γ x.1 with hγ'
  set σ' : ι × Bool → ℝ := fun x => if x.2 then δ x.1 else -δ x.1 with hσ'
  have hF : ∀ t : ℝ, (∑ k, cexp (I * γ k * t) *
      (p k * cexp ((δ k : ℂ) * t) + q k * cexp (-(δ k : ℂ) * t))) =
        ∑ x, c' x * cexp ((I * γ' x + σ' x) * t) := by
    intro t
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Fintype.sum_bool]
    simp only [hc', hγ', hσ', if_true, Bool.false_eq_true, if_false]
    rw [show cexp ((I * γ k + δ k) * t) = cexp (I * γ k * t) * cexp ((δ k : ℂ) * t) by
        rw [← Complex.exp_add]; ring_nf,
      show cexp ((I * γ k + ((-δ k : ℝ) : ℂ)) * t) = cexp (I * γ k * t) * cexp (-(δ k : ℂ) * t) by
        rw [← Complex.exp_add]; push_cast; ring_nf]
    ring
  set a := π / (2 * T) with ha
  have ha0 : 0 < a := by positivity
  set R := 2 * inghamA T * Real.cosh (2 * s * T) / tiltA T s ^ 2 * tiltB T g s with hR
  have hR0 : 0 ≤ R := by
    have ha'0 : 0 < tiltA T s := Real.sqrt_pos.mpr (by unfold inghamA; positivity)
    have : 0 < inghamA T := by unfold inghamA; positivity
    have := tiltB_nonneg hT hgap
    have := Real.cosh_pos (2 * s * T)
    positivity
  -- the weight `cos(at) ≤ 1` and the quadratic form
  set f : ℝ → ℂ := fun t => ∑ x, c' x * cexp ((I * γ' x + σ' x) * t) with hf
  have hfc : Continuous fun t => ‖f t‖ ^ 2 := by rw [hf]; fun_prop
  have h1 : ∫ t in -T..T, Real.cos (a * t) * ‖f t‖ ^ 2 ≤ ∫ t in -T..T, ‖f t‖ ^ 2 :=
    intervalIntegral.integral_mono_on (by linarith)
      ((show Continuous fun t : ℝ => Real.cos (a * t) * ‖f t‖ ^ 2 from
        (Real.continuous_cos.comp (continuous_const.mul continuous_id)).mul hfc).intervalIntegrable _ _)
      (hfc.intervalIntegrable _ _) fun t _ =>
        mul_le_of_le_one_left (by positivity) (Real.cos_le_one _)
  have hQ := integral_cos_mul_normSq_tiltedSum γ' σ' c' T
  rw [← ha] at hQ
  have hint : (∫ t in -T..T, ‖∑ k, cexp (I * γ k * t) *
      (p k * cexp ((δ k : ℂ) * t) + q k * cexp (-(δ k : ℂ) * t))‖ ^ 2) =
        ∫ t in -T..T, ‖f t‖ ^ 2 := by
    congr 1 with t; rw [hF t]
  rw [hint]
  refine le_trans ?_ (hQ ▸ h1)
  -- blocks
  set blk : ι → ι → ℂ := fun k l => ∑ b : Bool, ∑ b' : Bool,
    c' (k, b) * conj (c' (l, b')) * tiltedKernel T (γ k - γ l) (σ' (k, b) + σ' (l, b')) with hblk
  have hsplit : (∑ x, ∑ y, c' x * conj (c' y) * tiltedKernel T (γ' x - γ' y) (σ' x + σ' y)) =
      ∑ k, ∑ l, blk k l := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Fintype.sum_prod_type, hblk]
    rw [Finset.sum_comm]
  rw [hsplit, Complex.re_sum]
  set w : ι → ℝ := fun k => ‖p k‖ + ‖q k‖ with hw
  set S : ι → ℝ := fun k => ‖p k‖ ^ 2 + ‖q k‖ ^ 2 with hS
  -- the diagonal block
  have hdiag : ∀ k, D₀ * S k ≤ (blk k k).re := by
    intro k
    set A2 := 2 * a * Real.cosh (2 * δ k * T) / ((2 * δ k) ^ 2 + a ^ 2) with hA2
    set A0 := 2 * a / a ^ 2 with hA0
    have k1 : tiltedKernel T (γ k - γ k) (δ k + δ k) = (A2 : ℂ) := by
      rw [sub_self, tiltedKernel_diag hT, ← ha]; congr 1; rw [hA2]; ring_nf
    have k2 : tiltedKernel T (γ k - γ k) (δ k + -δ k) = (A0 : ℂ) := by
      rw [sub_self, add_neg_cancel, tiltedKernel_diag hT, ← ha]; congr 1; simp [hA0]
    have k3 : tiltedKernel T (γ k - γ k) (-δ k + δ k) = (A0 : ℂ) := by
      rw [sub_self, neg_add_cancel, tiltedKernel_diag hT, ← ha]; congr 1; simp [hA0]
    have k4 : tiltedKernel T (γ k - γ k) (-δ k + -δ k) = (A2 : ℂ) := by
      rw [sub_self, tiltedKernel_diag hT, ← ha]; congr 1
      rw [hA2, show (-δ k + -δ k) * T = -(2 * δ k * T) by ring, Real.cosh_neg]; ring_nf
    have hblkk : blk k k = ((A2 * S k : ℝ) : ℂ) + (A0 : ℂ) * (p k * conj (q k) + q k * conj (p k)) := by
      simp only [hblk, Fintype.sum_bool, hc', hσ', if_true, Bool.false_eq_true, if_false]
      rw [k1, k2, k3, k4, Complex.mul_conj, Complex.mul_conj, Complex.normSq_eq_norm_sq,
        Complex.normSq_eq_norm_sq, hS]
      push_cast; ring
    have e : (p k * conj (q k) + q k * conj (p k)).re = 2 * (p k * conj (q k)).re := by
      rw [Complex.add_re, show q k * conj (p k) = conj (p k * conj (q k)) by
        rw [map_mul, Complex.conj_conj]; ring, Complex.conj_re]; ring
    have hcross : -(S k) ≤ (p k * conj (q k) + q k * conj (p k)).re := by
      rw [e]
      have h2 := (abs_le.mp (Complex.abs_re_le_norm (p k * conj (q k)))).1
      rw [norm_mul, Complex.norm_conj] at h2
      rw [hS]
      nlinarith [sq_nonneg (‖p k‖ - ‖q k‖)]
    have hgapk : A2 - A0 = pairGap T (δ k) := by rw [hA2, hA0, pairGap]
    have hA0' : A0 = 2 / inghamA T := by rw [hA0, inghamA, ← ha]; field_simp
    have hA0 : 0 < A0 := by rw [hA0]; positivity
    rw [hblkk, Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul]
    have hSk : 0 ≤ S k := by rw [hS]; positivity
    rcases hD k with hDk | ⟨hDk, hal⟩
    · nlinarith [mul_le_mul_of_nonneg_left hcross hA0.le]
    · -- aligned coefficients: the cross term is nonnegative and `A(2δ) ≥ A(0)`
      have hA2A0 : A0 ≤ A2 := by linarith [pairGap_nonneg hT (δ k)]
      have hcr : 0 ≤ (p k * conj (q k) + q k * conj (p k)).re := by rw [e]; linarith
      rw [← hA0'] at hDk
      nlinarith [mul_le_mul_of_nonneg_right hDk hSk, mul_le_mul_of_nonneg_right hA2A0 hSk,
        mul_nonneg hA0.le hcr]
  -- the off-diagonal blocks
  have hoff : ∀ k l, k ≠ l → ‖blk k l‖ ≤ w k * w l * tiltPsi T s |γ k - γ l| := by
    intro k l hkl
    have hker : ∀ b b' : Bool, ‖tiltedKernel T (γ k - γ l) (σ' (k, b) + σ' (l, b'))‖ ≤
        tiltPsi T s |γ k - γ l| := by
      intro b b'
      have hσb : |σ' (k, b) + σ' (l, b')| ≤ 2 * s := by
        have e1 : |σ' (k, b)| ≤ s := by
          simp only [hσ']; split_ifs <;> simp [abs_neg, hδ]
        have e2 : |σ' (l, b')| ≤ s := by
          simp only [hσ']; split_ifs <;> simp [abs_neg, hδ]
        exact (abs_add_le _ _).trans (by linarith)
      have h := norm_tiltedKernel_le_of_sep hT hs hgap (hsep k l hkl) hσb
      unfold tiltPsi tiltA inghamA
      rw [sq_abs]
      exact h
    have hψ0 : 0 ≤ tiltPsi T s |γ k - γ l| := (norm_nonneg _).trans (hker true true)
    calc ‖blk k l‖ ≤ ∑ b : Bool, ∑ b' : Bool, ‖c' (k, b)‖ * ‖c' (l, b')‖ * tiltPsi T s |γ k - γ l| := by
          simp only [hblk]
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b' _ => ?_)
          rw [norm_mul, norm_mul, Complex.norm_conj]
          exact mul_le_mul_of_nonneg_left (hker b b') (by positivity)
      _ = w k * w l * tiltPsi T s |γ k - γ l| := by
          simp only [Fintype.sum_bool, hc', if_true, Bool.false_eq_true, if_false, hw]; ring
  -- assemble
  have hrowk : ∀ k, D₀ * S k - ∑ l ∈ Finset.univ.filter (· ≠ k), w k * w l * tiltPsi T s |γ k - γ l| ≤
      (∑ l, blk k l).re := by
    intro k
    rw [Finset.filter_ne', ← Finset.add_sum_erase _ _ (Finset.mem_univ k), Complex.add_re,
      Complex.re_sum (Finset.univ.erase k) (blk k)]
    have hlow : ∀ l ∈ Finset.univ.erase k, -(w k * w l * tiltPsi T s |γ k - γ l|) ≤
        (blk k l).re := fun l hl => by
      have hne : k ≠ l := (Finset.ne_of_mem_erase hl).symm
      have h := (abs_le.mp (Complex.abs_re_le_norm (blk k l))).1
      linarith [hoff k l hne]
    have := Finset.sum_le_sum hlow
    rw [Finset.sum_neg_distrib] at this
    linarith [hdiag k]
  have hschur := schur_offDiag_le w (fun k l => tiltPsi T s |γ k - γ l|)
    (fun k l hkl => by
      have ha'0 : 0 < tiltA T s := Real.sqrt_pos.mpr (by unfold inghamA; positivity)
      have hx := hsep k l hkl
      have hlt : tiltA T s < |γ k - γ l| := by linarith
      unfold tiltPsi
      refine div_nonneg (by unfold inghamA; positivity) ?_
      nlinarith)
    (fun k l => by simp only [abs_sub_comm])
    (fun k => tilted_rowSum_le γ hg hT hsep hgap k)
  have hw2 : ∑ k, w k ^ 2 ≤ 2 * ∑ k, S k := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun k _ => by
      simp only [hw, hS]; nlinarith [sq_nonneg (‖p k‖ - ‖q k‖)]
  have hsumk := Finset.sum_le_sum fun k (_ : k ∈ Finset.univ) => hrowk k
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at hsumk
  have := mul_le_mul_of_nonneg_left hw2 hR0
  rw [← hR] at hschur
  nlinarith

/-- **Pair resolution of a vanishing exponential sum.** Let sites `k` at `g`-separated heights
carry FE pairs `γ_k ∓ iδ_k` with summable coefficients `p_k, q_k`, depths `|δ_k| ≤ s` and pair gaps
`≥ D₀`. If `Σ_k e^{iγ_k v}(p_k e^{δ_k v} + q_k e^{−δ_k v})` vanishes on `[−V, V]` and the block
constant `D₀ − 2R` is positive, every coefficient vanishes. -/
theorem eq_zero_of_pairSum_eq_zero {κ : Type*} (γ δ : κ → ℝ) (p q : κ → ℂ) {g V s D₀ : ℝ}
    (hg : 0 < g) (hV : 0 < V) (hs : 0 ≤ s) (hδ : ∀ k, |δ k| ≤ s)
    (hsep : ∀ j l, j ≠ l → g ≤ |γ j - γ l|) (hgap : 2 * tiltA V s < g)
    (hD : ∀ k, D₀ ≤ pairGap V (δ k) ∨ (D₀ ≤ 2 / inghamA V ∧ 0 ≤ (p k * conj (q k)).re))
    (hpos : 0 < D₀ - 2 * (2 * inghamA V * Real.cosh (2 * s * V) / tiltA V s ^ 2 * tiltB V g s))
    (hsum : Summable fun k => ‖p k‖ + ‖q k‖)
    (hzero : ∀ v ∈ Set.Icc (-V) V, ∑' k, cexp (I * γ k * v) *
      (p k * cexp ((δ k : ℂ) * v) + q k * cexp (-(δ k : ℂ) * v)) = 0) :
    ∀ k, p k = 0 ∧ q k = 0 := by
  classical
  by_contra hne
  push Not at hne
  obtain ⟨k₀, hk₀⟩ := hne
  set C := D₀ - 2 * (2 * inghamA V * Real.cosh (2 * s * V) / tiltA V s ^ 2 * tiltB V g s) with hC
  set M := ‖p k₀‖ ^ 2 + ‖q k₀‖ ^ 2 with hM
  have hM0 : 0 < M := by
    by_cases hp : p k₀ = 0
    · have hq : q k₀ ≠ 0 := hk₀ hp
      have := norm_pos_iff.mpr hq
      rw [hM]; positivity
    · have := norm_pos_iff.mpr hp
      rw [hM]; positivity
  -- each term is bounded by `e^{sV}` times the coefficient mass
  set E := Real.exp (s * V) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have hterm : ∀ k, ∀ v ∈ Set.Icc (-V) V, ‖cexp (I * γ k * v) *
      (p k * cexp ((δ k : ℂ) * v) + q k * cexp (-(δ k : ℂ) * v))‖ ≤ E * (‖p k‖ + ‖q k‖) := by
    intro k v hv
    have hdv : |δ k * v| ≤ s * V := by
      rw [abs_mul]
      exact mul_le_mul (hδ k) (abs_le.mpr hv) (abs_nonneg _) hs
    have h1 : ‖cexp ((δ k : ℂ) * v)‖ ≤ E := by
      rw [Complex.norm_exp, show ((δ k : ℂ) * v).re = δ k * v by simp, hE]
      exact Real.exp_le_exp.mpr ((le_abs_self _).trans hdv)
    have h2 : ‖cexp (-(δ k : ℂ) * v)‖ ≤ E := by
      rw [Complex.norm_exp, show (-(δ k : ℂ) * v).re = -(δ k * v) by simp, hE]
      exact Real.exp_le_exp.mpr ((neg_le_abs _).trans hdv)
    have h0 : ‖cexp (I * γ k * v)‖ = 1 := by
      rw [show I * (γ k : ℂ) * (v : ℂ) = ((γ k * v : ℝ) : ℂ) * I by push_cast; ring]
      exact Complex.norm_exp_ofReal_mul_I _
    rw [norm_mul, h0, one_mul]
    calc ‖p k * cexp ((δ k : ℂ) * v) + q k * cexp (-(δ k : ℂ) * v)‖
        ≤ ‖p k‖ * ‖cexp ((δ k : ℂ) * v)‖ + ‖q k‖ * ‖cexp (-(δ k : ℂ) * v)‖ := by
          refine (norm_add_le _ _).trans ?_; rw [norm_mul, norm_mul]
      _ ≤ ‖p k‖ * E + ‖q k‖ * E := by gcongr
      _ = E * (‖p k‖ + ‖q k‖) := by ring
  -- choose a truncation with small tail
  set ε := Real.sqrt (C * M / (2 * V * E ^ 2 + 1)) with hε
  have hε0 : 0 < ε := Real.sqrt_pos.mpr (by have := mul_pos hpos hM0; positivity)
  have hε2 : 2 * V * (E * ε) ^ 2 < C * M := by
    have hCM : 0 < C * M := mul_pos hpos hM0
    rw [mul_pow, hε, Real.sq_sqrt (by positivity)]
    rw [show 2 * V * (E ^ 2 * (C * M / (2 * V * E ^ 2 + 1))) =
      (2 * V * E ^ 2) / (2 * V * E ^ 2 + 1) * (C * M) by ring]
    have : (2 * V * E ^ 2) / (2 * V * E ^ 2 + 1) < 1 := by
      rw [div_lt_one (by positivity)]; linarith
    nlinarith
  obtain ⟨F, hF₀, hFtail⟩ : ∃ F : Finset κ, k₀ ∈ F ∧
      ∑' x : {x // x ∉ F}, (‖p x‖ + ‖q x‖) < ε := by
    have h := (tendsto_tsum_compl_atTop_zero (fun k => ‖p k‖ + ‖q k‖)).eventually
      (gt_mem_nhds hε0)
    obtain ⟨F, hF⟩ := (h.and (Filter.eventually_ge_atTop {k₀})).exists
    exact ⟨F, hF.2 (Finset.mem_singleton_self _), hF.1⟩
  -- the truncation is small on `[−V, V]`
  have hsmall : ∀ v ∈ Set.Icc (-V) V, ‖∑ k ∈ F, cexp (I * γ k * v) *
      (p k * cexp ((δ k : ℂ) * v) + q k * cexp (-(δ k : ℂ) * v))‖ ≤ E * ε := by
    intro v hv
    set u : κ → ℂ := fun k => cexp (I * γ k * v) *
      (p k * cexp ((δ k : ℂ) * v) + q k * cexp (-(δ k : ℂ) * v)) with hu
    have husum : Summable u :=
      Summable.of_norm_bounded (hsum.mul_left E) fun k => hterm k v hv
    have hsplit := husum.sum_add_tsum_subtype_compl F
    rw [hzero v hv] at hsplit
    have htn : Summable fun x : {x // x ∉ F} => ‖p x‖ + ‖q x‖ :=
      hsum.comp_injective Subtype.val_injective
    rw [show ∑ k ∈ F, u k = -∑' x : {x // x ∉ F}, u x by linear_combination hsplit, norm_neg]
    calc ‖∑' x : {x // x ∉ F}, u x‖ ≤ ∑' x : {x // x ∉ F}, E * (‖p x‖ + ‖q x‖) :=
          tsum_of_norm_bounded (htn.mul_left E).hasSum fun x => hterm x v hv
      _ = E * ∑' x : {x // x ∉ F}, (‖p x‖ + ‖q x‖) := tsum_mul_left
      _ ≤ E * ε := mul_le_mul_of_nonneg_left hFtail.le hE0.le
  -- the block inequality on the truncation
  have hblock := block_ingham_inequality (ι := F) (fun k => γ k) (fun k => δ k)
    (fun k => p k) (fun k => q k) hg hV hs (fun k => hδ k)
    (fun j l hjl => hsep j l fun h => hjl (Subtype.ext h)) hgap (fun k => hD k)
  rw [← hC] at hblock
  have hrw : ∀ v : ℝ, ∑ k : F, cexp (I * ((γ k : ℝ) : ℂ) * v) *
      (p k * cexp (((δ k : ℝ) : ℂ) * v) + q k * cexp (-((δ k : ℝ) : ℂ) * v)) =
        ∑ k ∈ F, cexp (I * γ k * v) *
          (p k * cexp ((δ k : ℂ) * v) + q k * cexp (-(δ k : ℂ) * v)) := fun v =>
    Finset.sum_coe_sort F (fun k => cexp (I * γ k * v) *
      (p k * cexp ((δ k : ℂ) * v) + q k * cexp (-(δ k : ℂ) * v)))
  simp_rw [hrw] at hblock
  have hint : ∫ v in -V..V, ‖∑ k ∈ F, cexp (I * γ k * v) *
      (p k * cexp ((δ k : ℂ) * v) + q k * cexp (-(δ k : ℂ) * v))‖ ^ 2 ≤ 2 * V * (E * ε) ^ 2 := by
    have hcont : Continuous fun v : ℝ => ‖∑ k ∈ F, cexp (I * γ k * v) *
        (p k * cexp ((δ k : ℂ) * v) + q k * cexp (-(δ k : ℂ) * v))‖ ^ 2 := by fun_prop
    calc _ ≤ ∫ _v in -V..V, (E * ε) ^ 2 := intervalIntegral.integral_mono_on (by linarith)
          (hcont.intervalIntegrable _ _) intervalIntegrable_const fun v hv =>
            pow_le_pow_left₀ (norm_nonneg _) (hsmall v hv) 2
      _ = 2 * V * (E * ε) ^ 2 := by rw [intervalIntegral.integral_const, smul_eq_mul]; ring
  have hsq : M ≤ ∑ k : F, (‖p k‖ ^ 2 + ‖q k‖ ^ 2) := by
    rw [Finset.sum_coe_sort F (fun k => ‖p k‖ ^ 2 + ‖q k‖ ^ 2)]
    exact Finset.single_le_sum (f := fun k => ‖p k‖ ^ 2 + ‖q k‖ ^ 2)
      (fun _ _ => by positivity) hF₀
  have : C * M ≤ 2 * V * (E * ε) ^ 2 :=
    (mul_le_mul_of_nonneg_left hsq hpos.le).trans (hblock.trans hint)
  linarith

end GaloisForLFunctions.ZeroConfigurationGeometry
