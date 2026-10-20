import GaloisForLFunctions.SquareRootThreshold.OneParameterLagFamilyDecidesTheCriticalLine
import GaloisForLFunctions.SquareRootThreshold.OneParameterLagFamilyDeterminesTheConfiguration

/-!
# Finite lag windows: the record-potential law

Let `φ(v) = 2 Re S(v) = Σ_z D(z) e^{zv}` be the lag function of a bump `b`
(`two_re_lagStructure_eq`), so that the difference test `f_v = b(· + v/2) − b(· − v/2)` has
`Re W(f_v, f_v) = φ(0) − φ(v)` (`re_W_lag_eq`). Suppose the family is nonnegative only on a
*finite* range of lags `0 ≤ v ≤ V`.

**Laplace window.** `G(s) = ∫_0^V e^{−sv} (φ(0) − φ(v)) dv` is the transform of a nonnegative
function, so `|G(σ + it)| ≤ G(σ)`; termwise, `G(s) = φ(0) E_V(−s) − Σ_z D(z) E_V(z − s)` with the
finite Laplace kernel `E_V(z) = ∫_0^V e^{zu} du` (`lapWin`, `integral_lagWindow_eq`).

**Record-potential law** (`norm_evenCoeff_mul_lapWin_le`). At `s = σ + i Im z₀` the kernel of the
exponent `z₀` is real, `E_V(z₀ − s) = E_V(Re z₀ − σ) ≈ e^{(Re z₀ − σ)V}/(Re z₀ − σ)`, so

`|D(z₀)| |E_V(z₀ − s)| ≤ |φ(0)| (|E_V(−σ)| + |E_V(−s)|) + Σ_z |D(z)| |E_V(z − σ)|
  + Σ_{z ≠ z₀} |D(z)| |E_V(z − s)|`.

This is Landau's theorem made effective. Landau needs the one-sided bound on a half-line and
continues the transform up to the top pole, so only a top can be seen, and on lag grids only an
attained top. On a finite window *every* exponent is tested: the inequality holds for each `z₀`,
and fails as soon as one pole dominates the potential `Σ |D(z)| |E_V(z − s)|` of the others. The
attainment premise is replaced by the loudness ratio `N = Σ_z |D(z)| e^{Re z·V} / (|D(z₀)| e^{Re z₀·V})`
at the lag `V` itself. It is finite at every lag. At a *Legendre record*, a maximizer of
`|D(z)| e^{Re z·V}`, every term is at most the record's, so `N` counts its competitors; a record
exists at every lag whether or not the top depth is attained.

**Explicit lag** (`exists_lag_neg_of_loudness`). Let `|Im z| ≥ η` on the exponents, let the other
exponents keep distance `g` from `s = σ + i Im z₀`, put `κ = 1/η + 1/g`, `θ = Re z₀ − σ > 0` with
`2κNθ ≤ 1`. If `κ N |D(z₀)| (e^{θV} − 2) > 4|φ(0)|/σ + κ Σ_z |D(z)|`, some lag `v ∈ [0, V]` has
`Re W(f_v, f_v) < 0`. So the first negative lag is at most
`(1/θ) log(2 + (4|φ(0)|/σ + κ Σ|D|)/(κ N |D(z₀)|))`: logarithmic in the coefficient of the zero,
linear in its loudness ratio and in the inverse separations.

**For `ζ`: the crowding law** (`zeta_crowding_of_lag_primeWindow_nonneg`). Nontrivial zeros have
`|Im ρ| ≥ 4`, so `η = 4`. If the dyadic window functionals `P_v` of a width `w ∈ (0, ½ log 2)` are
nonnegative for all `v ∈ [0, V]`, every off-line zero `ρ₀ = ½ + z₀` satisfies
`κ N |D(z₀)| (e^{θV} − 2) ≤ 4|φ(0)|/σ + κ Σ|D|`: it is either quiet at lag `V` or crowded, with
loudness ratio `N ≳ θ⁻¹`. Finite prime data force companions at the record.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower

/-! ### The finite Laplace kernel -/

/-- The finite Laplace kernel `E_V(z) = ∫_0^V e^{zu} du`. -/
def lapWin (V : ℝ) (z : ℂ) : ℂ := ∫ u in (0 : ℝ)..V, cexp (z * u)

theorem lapWin_eq (V : ℝ) {z : ℂ} (hz : z ≠ 0) : lapWin V z = (cexp (z * V) - 1) / z := by
  rw [lapWin, integral_exp_mul_complex hz]
  simp

/-- `|E_V(z)| ≤ ∫_0^V e^{Re z · u} du`. -/
theorem norm_lapWin_le {V : ℝ} (hV : 0 ≤ V) (z : ℂ) :
    ‖lapWin V z‖ ≤ ∫ u in (0 : ℝ)..V, Real.exp (z.re * u) := by
  refine (intervalIntegral.norm_integral_le_integral_norm hV).trans_eq ?_
  refine intervalIntegral.integral_congr fun u _ => ?_
  simp [Complex.norm_exp]

/-- `|E_V(z)| ≤ (e^{Re z · V} + 1)/|z|`. -/
theorem norm_lapWin_le_div (V : ℝ) {z : ℂ} (hz : z ≠ 0) :
    ‖lapWin V z‖ ≤ (Real.exp (z.re * V) + 1) / ‖z‖ := by
  rw [lapWin_eq V hz, norm_div]
  gcongr
  refine (norm_sub_le _ _).trans_eq ?_
  simp [Complex.norm_exp]

/-- `|E_V(z)| ≤ V e^{|Re z| V}`. -/
theorem norm_lapWin_le_const {V : ℝ} (hV : 0 ≤ V) (z : ℂ) :
    ‖lapWin V z‖ ≤ V * Real.exp (|z.re| * V) := by
  refine (norm_lapWin_le hV z).trans ?_
  have h : ∫ u in (0 : ℝ)..V, Real.exp (z.re * u) ≤ ∫ _u in (0 : ℝ)..V, Real.exp (|z.re| * V) :=
    intervalIntegral.integral_mono_on hV
      ((by fun_prop : Continuous fun u : ℝ => Real.exp (z.re * u)).intervalIntegrable _ _)
      intervalIntegrable_const fun u hu => Real.exp_le_exp.mpr
        ((mul_le_mul_of_nonneg_right (le_abs_self _) hu.1).trans
          (mul_le_mul_of_nonneg_left hu.2 (abs_nonneg _)))
  simpa using h

/-- For real `x`, `E_V(x)` is the real integral `∫_0^V e^{xu} du`. -/
theorem lapWin_ofReal (V x : ℝ) :
    lapWin V x = ((∫ u in (0 : ℝ)..V, Real.exp (x * u) : ℝ) : ℂ) := by
  rw [lapWin, ← intervalIntegral.integral_ofReal]
  refine intervalIntegral.integral_congr fun u _ => ?_
  push_cast
  rfl

/-- For `x > 0`, `E_V(x) = (e^{xV} − 1)/x`. -/
theorem norm_lapWin_ofReal_pos {V : ℝ} (hV : 0 ≤ V) {x : ℝ} (hx : 0 < x) :
    ‖lapWin V x‖ = (Real.exp (x * V) - 1) / x := by
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  rw [lapWin_eq V hx0, ← Complex.ofReal_mul, ← Complex.ofReal_exp, ← Complex.ofReal_one,
    ← Complex.ofReal_sub, ← Complex.ofReal_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg]
  exact div_nonneg (by linarith [Real.one_le_exp (mul_nonneg hx.le hV)]) hx.le

/-! ### The Laplace window of the lag function -/

/-- The exponents of the lag function lie in the strip `|Re z| ≤ ½`. -/
theorem abs_re_le_of_evenCoeff_ne_zero {Z : ZeroConfig} {b : ℝ → ℂ} {z : ℂ}
    (hz : evenCoeff Z b z ≠ 0) : |z.re| ≤ 1 / 2 := by
  rcases mem_of_evenCoeff_ne_zero hz with h | h
  · have := Z.strip _ h; simp at this; exact abs_le.mpr ⟨by linarith, by linarith⟩
  · have := Z.strip _ h; simp at this; exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem summable_norm_evenCoeff (Z : ZeroConfig) (hZ : TemperedConfig Z) {b : ℝ → ℂ}
    (hb : ContDiff ℝ 2 b) {w : ℝ} (hbs : ∀ u, b u ≠ 0 → |u| ≤ w) :
    Summable fun z : ℂ => ‖evenCoeff Z b z‖ := by
  have h0 := (two_re_lagStructure_eq Z hZ hb hbs 0).1.norm
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one] at h0
  exact h0

/-- A coefficient times a factor bounded on the strip is summable. -/
theorem summable_norm_evenCoeff_mul (Z : ZeroConfig) (hZ : TemperedConfig Z) {b : ℝ → ℂ}
    (hb : ContDiff ℝ 2 b) {w : ℝ} (hbs : ∀ u, b u ≠ 0 → |u| ≤ w) {F : ℂ → ℝ} {C : ℝ}
    (hF0 : ∀ z, 0 ≤ F z) (hF : ∀ z, evenCoeff Z b z ≠ 0 → F z ≤ C) :
    Summable fun z : ℂ => ‖evenCoeff Z b z‖ * F z := by
  refine Summable.of_nonneg_of_le (fun z => mul_nonneg (norm_nonneg _) (hF0 z)) (fun z => ?_)
    ((summable_norm_evenCoeff Z hZ hb hbs).mul_right C)
  by_cases h : evenCoeff Z b z = 0
  · simp [h]
  · exact mul_le_mul_of_nonneg_left (hF z h) (norm_nonneg _)

/-- **The Laplace window, termwise.** `∫_0^V e^{−su} φ(u) du = Σ_z D(z) E_V(z − s)`. -/
theorem integral_lagWindow_eq (Z : ZeroConfig) (hZ : TemperedConfig Z) {b : ℝ → ℂ}
    (hb : ContDiff ℝ 2 b) {w : ℝ} (hbs : ∀ u, b u ≠ 0 → |u| ≤ w) {V : ℝ} (hV : 0 ≤ V) (s : ℂ) :
    ∫ u in (0 : ℝ)..V, cexp (-s * u) * ((2 * (lagStructure Z b u).re : ℝ) : ℂ) =
      ∑' z : ℂ, evenCoeff Z b z * lapWin V (z - s) := by
  classical
  set ι : Set ℂ := {z | evenCoeff Z b z ≠ 0} with hι
  haveI : Countable ι := (countable_evenCoeff_support Z b).to_subtype
  have hD : Summable fun t : ι => ‖evenCoeff Z b t‖ :=
    (summable_norm_evenCoeff Z hZ hb hbs).subtype ι
  have hrep : ∀ u : ℝ, cexp (-s * u) * ((2 * (lagStructure Z b u).re : ℝ) : ℂ) =
      ∑' t : ι, evenCoeff Z b t * cexp (((t : ℂ) - s) * u) := by
    intro u
    have hsub : Function.support (fun z : ℂ => evenCoeff Z b z * cexp (z * u)) ⊆ ι :=
      fun z hz h0 => hz (show evenCoeff Z b z * cexp (z * u) = 0 by rw [h0, zero_mul])
    rw [(two_re_lagStructure_eq Z hZ hb hbs u).2, ← tsum_subtype_eq_of_support_subset hsub,
      ← tsum_mul_left]
    refine tsum_congr fun t => ?_
    rw [mul_left_comm, ← Complex.exp_add]
    congr 2
    ring
  set K : ℝ := V * Real.exp ((1 / 2 + |s.re|) * V) with hK
  have hpt : ∀ (t : ι) (u : ℝ), u ∈ Icc (0 : ℝ) V →
      ‖evenCoeff Z b t * cexp (((t : ℂ) - s) * u)‖ ≤ ‖evenCoeff Z b t‖ *
        Real.exp ((1 / 2 + |s.re|) * V) := by
    intro t u hu
    rw [norm_mul, Complex.norm_exp]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
    have hre := abs_re_le_of_evenCoeff_ne_zero t.2
    have e : ((((t : ℂ) - s) * (u : ℂ))).re = ((t : ℂ).re - s.re) * u := by simp
    rw [e]
    have h1 : (t : ℂ).re - s.re ≤ 1 / 2 + |s.re| := by
      linarith [(abs_le.mp hre).2, neg_abs_le s.re]
    calc ((t : ℂ).re - s.re) * u ≤ (1 / 2 + |s.re|) * u :=
          mul_le_mul_of_nonneg_right h1 hu.1
      _ ≤ (1 / 2 + |s.re|) * V :=
          mul_le_mul_of_nonneg_left hu.2 (by positivity)
  have hF : ∀ t : ι, Integrable (fun u : ℝ => evenCoeff Z b t * cexp (((t : ℂ) - s) * u))
      (volume.restrict (Ioc 0 V)) := fun t =>
    ((by fun_prop : Continuous fun u : ℝ => evenCoeff Z b t * cexp (((t : ℂ) - s) * u)
      ).integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hsum : Summable fun t : ι =>
      ∫ u in Ioc 0 V, ‖evenCoeff Z b t * cexp (((t : ℂ) - s) * u)‖ := by
    refine Summable.of_nonneg_of_le (fun t => setIntegral_nonneg measurableSet_Ioc
      fun _ _ => norm_nonneg _) (fun t => ?_) (hD.mul_right K)
    rw [← intervalIntegral.integral_of_le hV]
    calc ∫ u in (0 : ℝ)..V, ‖evenCoeff Z b t * cexp (((t : ℂ) - s) * u)‖
        ≤ ∫ _u in (0 : ℝ)..V, ‖evenCoeff Z b t‖ * Real.exp ((1 / 2 + |s.re|) * V) :=
          intervalIntegral.integral_mono_on hV ((by fun_prop : Continuous fun u : ℝ =>
            ‖evenCoeff Z b t * cexp (((t : ℂ) - s) * u)‖).intervalIntegrable _ _)
            intervalIntegrable_const (hpt t)
      _ = ‖evenCoeff Z b t‖ * K := by simp [hK]
  have hsupp : Function.support (fun z : ℂ => evenCoeff Z b z * lapWin V (z - s)) ⊆ ι :=
    fun z hz h0 => hz (show evenCoeff Z b z * lapWin V (z - s) = 0 by rw [h0, zero_mul])
  simp_rw [hrep]
  rw [intervalIntegral.integral_of_le hV, ← integral_tsum_of_summable_integral_norm hF hsum,
    ← tsum_subtype_eq_of_support_subset hsupp]
  refine tsum_congr fun t => ?_
  rw [integral_const_mul, ← intervalIntegral.integral_of_le hV, lapWin]

/-- **Positivity of the window.** For `g ≥ 0` on `[0, V]`, the transform
`G(s) = ∫_0^V e^{−su} g(u) du` satisfies `|G(σ + it)| ≤ G(σ)`, and `G(σ)` is real. -/
theorem norm_integral_cexp_mul_le {V : ℝ} (hV : 0 ≤ V) {g : ℝ → ℝ}
    (hg : ∀ u ∈ Icc (0 : ℝ) V, 0 ≤ g u) (s : ℂ) :
    ‖∫ u in (0 : ℝ)..V, cexp (-s * u) * ((g u : ℝ) : ℂ)‖ ≤
      (∫ u in (0 : ℝ)..V, cexp (-(s.re : ℂ) * u) * ((g u : ℝ) : ℂ)).re := by
  have hreal : ∫ u in (0 : ℝ)..V, cexp (-(s.re : ℂ) * u) * ((g u : ℝ) : ℂ) =
      ((∫ u in (0 : ℝ)..V, Real.exp (-s.re * u) * g u : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]
    refine intervalIntegral.integral_congr fun u _ => ?_
    push_cast
    rfl
  rw [hreal, Complex.ofReal_re]
  refine (intervalIntegral.norm_integral_le_integral_norm hV).trans_eq ?_
  refine intervalIntegral.integral_congr fun u hu => ?_
  rw [Set.uIcc_of_le hV] at hu
  simp only [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (hg u hu)]
  congr 2
  simp

/-! ### The record-potential law -/

/-- **Record-potential law.** If the difference tests `b(t + v/2) − b(t − v/2)` are Weil
nonnegative for all `v ∈ [0, V]`, then for every exponent `z₀` and all real `σ, t`, with
`s = σ + it` and `M = 2 Re S(0)`:
`|D(z₀) E_V(z₀ − s)| ≤ |M| (|E_V(−σ)| + |E_V(−s)|) + Σ_z |D(z)||E_V(z − σ)|
  + Σ_{z ≠ z₀} |D(z)||E_V(z − s)|`. -/
theorem norm_evenCoeff_mul_lapWin_le (Z : ZeroConfig) (hZ : TemperedConfig Z) {b : ℝ → ℂ}
    (hb : ContDiff ℝ 2 b) {w : ℝ} (hbs : ∀ u, b u ≠ 0 → |u| ≤ w) {V : ℝ} (hV : 0 ≤ V)
    (hm : ∀ v ∈ Icc (0 : ℝ) V, 0 ≤ (Z.W (twoBump b v (-1)) (twoBump b v (-1))).re)
    (z₀ : ℂ) (σ t : ℝ) :
    ‖evenCoeff Z b z₀ * lapWin V (z₀ - (σ + t * I))‖ ≤
      |2 * (lagStructure Z b 0).re| * (‖lapWin V (-σ)‖ + ‖lapWin V (-(σ + t * I))‖) +
      ∑' z : ℂ, ‖evenCoeff Z b z‖ * ‖lapWin V (z - σ)‖ +
      ∑' z : ℂ, (if z = z₀ then 0 else ‖evenCoeff Z b z‖ * ‖lapWin V (z - (σ + t * I))‖) := by
  classical
  set D := evenCoeff Z b with hDdef
  set M : ℝ := 2 * (lagStructure Z b 0).re with hM
  set φ : ℝ → ℝ := fun u => 2 * (lagStructure Z b u).re with hφ
  have hg : ∀ u ∈ Icc (0 : ℝ) V, 0 ≤ M - φ u := fun u hu => by
    have := hm u hu
    rwa [re_W_lag_eq Z hZ hb hbs u] at this
  have hφc : Continuous φ :=
    continuous_const.mul (Complex.continuous_re.comp (continuous_lagStructure Z hZ hb hbs))
  -- the transform `G(s) = M E_V(−s) − Σ_z D(z) E_V(z − s)`
  have hG : ∀ s : ℂ, ∫ u in (0 : ℝ)..V, cexp (-s * u) * ((M - φ u : ℝ) : ℂ) =
      M * lapWin V (-s) - ∑' z : ℂ, D z * lapWin V (z - s) := by
    intro s
    have e : ∀ u : ℝ, cexp (-s * u) * ((M - φ u : ℝ) : ℂ) =
        M * cexp (-s * u) - cexp (-s * u) * ((φ u : ℝ) : ℂ) := fun u => by push_cast; ring
    simp_rw [e]
    have hi1 : IntervalIntegrable (fun u : ℝ => (M : ℂ) * cexp (-s * u)) volume 0 V :=
      (by fun_prop : Continuous fun u : ℝ => (M : ℂ) * cexp (-s * u)).intervalIntegrable _ _
    have hi2 : IntervalIntegrable (fun u : ℝ => cexp (-s * u) * ((φ u : ℝ) : ℂ)) volume 0 V :=
      (Continuous.mul (by fun_prop) (Complex.continuous_ofReal.comp hφc)).intervalIntegrable _ _
    rw [intervalIntegral.integral_sub hi1 hi2, intervalIntegral.integral_const_mul, integral_lagWindow_eq Z hZ hb hbs hV s, lapWin]
  have hsD := summable_norm_evenCoeff Z hZ hb hbs
  -- summability of the potentials
  have hsumL : ∀ s : ℂ, Summable fun z : ℂ => ‖D z‖ * ‖lapWin V (z - s)‖ := fun s =>
    summable_norm_evenCoeff_mul Z hZ hb hbs (C := V * Real.exp ((1 / 2 + |s.re|) * V))
      (fun _ => norm_nonneg _) fun z hz => (norm_lapWin_le_const hV _).trans
        (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by
          rw [Complex.sub_re]
          exact (abs_sub _ _).trans (by linarith [abs_re_le_of_evenCoeff_ne_zero hz]))
          hV)) hV)
  have hsumC : ∀ s : ℂ, Summable fun z : ℂ => D z * lapWin V (z - s) := fun s =>
    (hsumL s).of_norm_bounded fun z => (norm_mul _ _).le
  set s : ℂ := σ + t * I with hs
  have hsre : s.re = σ := by simp [hs]
  -- `|G(s)| ≤ G(σ) = Re G(σ)`
  have hpos := norm_integral_cexp_mul_le hV hg s
  rw [hsre] at hpos
  have hGs := hG s
  have hGσ := hG σ
  -- isolate the term of `z₀`
  have hsplit := (hsumC s).tsum_eq_add_tsum_ite z₀
  have hrest : ‖∑' z : ℂ, (if z = z₀ then 0 else D z * lapWin V (z - s))‖ ≤
      ∑' z : ℂ, (if z = z₀ then 0 else ‖D z‖ * ‖lapWin V (z - s)‖) := by
    have hn : ∀ z : ℂ, ‖(if z = z₀ then 0 else D z * lapWin V (z - s))‖ =
        (if z = z₀ then 0 else ‖D z‖ * ‖lapWin V (z - s)‖) := fun z => by
      split_ifs <;> simp
    have hs' : Summable fun z : ℂ => (if z = z₀ then 0 else ‖D z‖ * ‖lapWin V (z - s)‖) :=
      (hsumL s).of_nonneg_of_le (fun z => by split_ifs <;> positivity)
        fun z => by split_ifs <;> first | positivity | exact le_rfl
    refine (norm_tsum_le_tsum_norm ?_).trans_eq (tsum_congr hn)
    simp_rw [hn]
    exact hs'
  have hGre : (M * lapWin V (-(σ : ℂ)) - ∑' z : ℂ, D z * lapWin V (z - σ)).re ≤
      |M| * ‖lapWin V (-σ)‖ + ∑' z : ℂ, ‖D z‖ * ‖lapWin V (z - σ)‖ := by
    rw [Complex.sub_re]
    have h1 : (M * lapWin V (-(σ : ℂ))).re ≤ |M| * ‖lapWin V (-σ)‖ := by
      refine (Complex.re_le_norm _).trans_eq ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have h2 : -(∑' z : ℂ, D z * lapWin V (z - σ)).re ≤ ∑' z : ℂ, ‖D z‖ * ‖lapWin V (z - σ)‖ := by
      refine (neg_le_abs _).trans ((Complex.abs_re_le_norm _).trans ?_)
      refine (norm_tsum_le_tsum_norm (hsumC σ).norm).trans_eq ?_
      simp
    linarith
  have hkey : D z₀ * lapWin V (z₀ - s) = M * lapWin V (-s) -
      (∫ u in (0 : ℝ)..V, cexp (-s * u) * ((M - φ u : ℝ) : ℂ)) -
      ∑' z : ℂ, (if z = z₀ then 0 else D z * lapWin V (z - s)) := by
    rw [hGs, hsplit]; ring
  rw [hkey]
  set Gs := ∫ u in (0 : ℝ)..V, cexp (-s * u) * ((M - φ u : ℝ) : ℂ) with hGsdef
  set R := ∑' z : ℂ, (if z = z₀ then 0 else D z * lapWin V (z - s)) with hRdef
  have htri : ‖M * lapWin V (-s) - Gs - R‖ ≤ ‖M * lapWin V (-s)‖ + ‖Gs‖ + ‖R‖ :=
    (norm_sub_le _ _).trans (by linarith [norm_sub_le (M * lapWin V (-s)) Gs])
  have hMn : ‖(M : ℂ) * lapWin V (-s)‖ = |M| * ‖lapWin V (-s)‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hGb : ‖Gs‖ ≤ |M| * ‖lapWin V (-σ)‖ + ∑' z : ℂ, ‖D z‖ * ‖lapWin V (z - σ)‖ := by
    refine hpos.trans ?_
    rw [hGσ]
    exact hGre
  have hs1 : (-s : ℂ) = -(σ + t * I) := by rw [hs]
  rw [← hs1]
  linarith

/-! ### Explicit lags -/

/-- `|E_V(z − s)| ≤ (e^{(Re z − Re s)V} + 1)/g` when `|z − s| ≥ g > 0`. -/
theorem norm_lapWin_sub_le {V g : ℝ} {z s : ℂ} (hg : 0 < g) (hzs : g ≤ ‖z - s‖) :
    ‖lapWin V (z - s)‖ ≤ (Real.exp ((z.re - s.re) * V) + 1) / g := by
  have hne : z - s ≠ 0 := fun h => by rw [h, norm_zero] at hzs; linarith
  refine (norm_lapWin_le_div V hne).trans ?_
  rw [Complex.sub_re]
  exact div_le_div_of_nonneg_left (by positivity) hg hzs

/-- **Loudness bound.** Let the difference tests be Weil nonnegative on `[0, V]`. Let
`|Im z| ≥ η` on the exponents, let the exponents `z ≠ z₀` keep distance `g` from
`s = σ + i Im z₀`, `κ = 1/η + 1/g`, `θ = Re z₀ − σ > 0` with `2κNθ ≤ 1`, and suppose the loudness at
lag `V` is at most `N` times that of `z₀`: `Σ_z |D(z)| e^{Re z·V} ≤ N |D(z₀)| e^{Re z₀·V}`. Then
`κ N |D(z₀)| (e^{θV} − 2) ≤ 4|M|/σ + κ Σ_z |D(z)|`, `M = 2 Re S(0)`. -/
theorem loudness_bound_of_lag_nonneg (Z : ZeroConfig) (hZ : TemperedConfig Z) {b : ℝ → ℂ}
    (hb : ContDiff ℝ 2 b) {w : ℝ} (hbs : ∀ u, b u ≠ 0 → |u| ≤ w) {V : ℝ} (hV : 0 ≤ V)
    (hm : ∀ v ∈ Icc (0 : ℝ) V, 0 ≤ (Z.W (twoBump b v (-1)) (twoBump b v (-1))).re)
    {η g σ N : ℝ} (hη : 0 < η) (hηz : ∀ z, evenCoeff Z b z ≠ 0 → η ≤ |z.im|) (hg : 0 < g)
    {z₀ : ℂ} (hσ : 0 < σ) (hθ : σ < z₀.re)
    (hsep : ∀ z, z ≠ z₀ → evenCoeff Z b z ≠ 0 → g ≤ ‖z - (σ + z₀.im * I)‖)
    (hθN : 2 * (1 / η + 1 / g) * N * (z₀.re - σ) ≤ 1)
    (hL : ∑' z : ℂ, ‖evenCoeff Z b z‖ * Real.exp (z.re * V) ≤
      N * ‖evenCoeff Z b z₀‖ * Real.exp (z₀.re * V)) :
    (1 / η + 1 / g) * N * ‖evenCoeff Z b z₀‖ * (Real.exp ((z₀.re - σ) * V) - 2) ≤
      4 * |2 * (lagStructure Z b 0).re| / σ + (1 / η + 1 / g) * ∑' z : ℂ, ‖evenCoeff Z b z‖ := by
  classical
  set D := evenCoeff Z b with hDdef
  set M : ℝ := 2 * (lagStructure Z b 0).re with hM
  set κ : ℝ := 1 / η + 1 / g with hκ
  set θ : ℝ := z₀.re - σ with hθdef
  have hθ0 : 0 < θ := by rw [hθdef]; linarith
  have hκ0 : 0 < κ := by rw [hκ]; positivity
  set s : ℂ := σ + z₀.im * I with hs
  have hsre : s.re = σ := by simp [hs]
  have hcore := norm_evenCoeff_mul_lapWin_le Z hZ hb hbs hV hm z₀ σ z₀.im
  rw [← hs] at hcore
  -- the kernel of `z₀` is real at `s`
  have hz₀s : z₀ - s = (θ : ℂ) := by
    apply Complex.ext <;> simp [hs, hθdef]
  have hLHS : ‖D z₀ * lapWin V (z₀ - s)‖ = ‖D z₀‖ * ((Real.exp (θ * V) - 1) / θ) := by
    rw [norm_mul, hz₀s, norm_lapWin_ofReal_pos hV hθ0]
  -- the archimedean-pole kernels
  have hE1 : ‖lapWin V (-(σ : ℂ))‖ ≤ 2 / σ := by
    have hne : (-(σ : ℂ)) ≠ 0 := by
      rw [neg_ne_zero]; exact_mod_cast hσ.ne'
    refine (norm_lapWin_le_div V hne).trans ?_
    rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hσ]
    gcongr
    have : (-(σ : ℂ)).re * V ≤ 0 := by simp; nlinarith
    linarith [Real.exp_le_one_iff.mpr this]
  have hE2 : ‖lapWin V (-s)‖ ≤ 2 / σ := by
    have hsn : σ ≤ ‖s‖ := by
      have := Complex.abs_re_le_norm s; rw [hsre, abs_of_pos hσ] at this; exact this
    have hne : -s ≠ 0 := fun h => by
      rw [neg_eq_zero] at h; rw [h, norm_zero] at hsn; linarith
    refine (norm_lapWin_le_div V hne).trans ?_
    rw [norm_neg]
    have : (-s).re * V ≤ 0 := by rw [Complex.neg_re, hsre]; nlinarith
    calc (Real.exp ((-s).re * V) + 1) / ‖s‖ ≤ 2 / ‖s‖ := by
          gcongr; linarith [Real.exp_le_one_iff.mpr this]
      _ ≤ 2 / σ := div_le_div_of_nonneg_left (by norm_num) hσ hsn
  -- the potentials
  set T : ℝ := ∑' z : ℂ, ‖D z‖ * (Real.exp ((z.re - σ) * V) + 1) with hT
  have hsL : Summable fun z : ℂ => ‖D z‖ * Real.exp (z.re * V) :=
    summable_norm_evenCoeff_mul Z hZ hb hbs (C := Real.exp (1 / 2 * V)) (fun _ => (Real.exp_pos _).le)
      fun z hz => Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
        ((le_abs_self _).trans (abs_re_le_of_evenCoeff_ne_zero hz)) hV)
  have hsD := summable_norm_evenCoeff Z hZ hb hbs
  have hTeq : T = Real.exp (-σ * V) * ∑' z : ℂ, ‖D z‖ * Real.exp (z.re * V) +
      ∑' z : ℂ, ‖D z‖ := by
    rw [hT, ← tsum_mul_left, ← (hsL.mul_left _).tsum_add hsD]
    refine tsum_congr fun z => ?_
    rw [show (z.re - σ) * V = -σ * V + z.re * V by ring, Real.exp_add]
    ring
  have hsT : Summable fun z : ℂ => ‖D z‖ * (Real.exp ((z.re - σ) * V) + 1) := by
    refine ((hsL.mul_left (Real.exp (-σ * V))).add hsD).congr fun z => ?_
    rw [show (z.re - σ) * V = -σ * V + z.re * V by ring, Real.exp_add]
    ring
  have hP1 : ∑' z : ℂ, ‖D z‖ * ‖lapWin V (z - σ)‖ ≤ T / η := by
    rw [hT, ← tsum_div_const]
    refine Summable.tsum_le_tsum (fun z => ?_) ?_ (hsT.div_const η)
    · by_cases hz : D z = 0
      · simp [hz]
      · have hzs : η ≤ ‖z - (σ : ℂ)‖ := (hηz z hz).trans (by
          have := Complex.abs_im_le_norm (z - (σ : ℂ)); simpa using this)
        have := norm_lapWin_sub_le (V := V) hη hzs
        rw [Complex.ofReal_re] at this
        calc ‖D z‖ * ‖lapWin V (z - σ)‖ ≤ ‖D z‖ * ((Real.exp ((z.re - σ) * V) + 1) / η) :=
              mul_le_mul_of_nonneg_left this (norm_nonneg _)
          _ = _ := by ring
    · exact summable_norm_evenCoeff_mul Z hZ hb hbs (C := V * Real.exp ((1 / 2 + |σ|) * V))
        (fun _ => norm_nonneg _) fun z hz => (norm_lapWin_le_const hV _).trans
          (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by
            rw [Complex.sub_re, Complex.ofReal_re]
            exact (abs_sub _ _).trans (by linarith [abs_re_le_of_evenCoeff_ne_zero hz]))
            hV)) hV)
  have hP2 : ∑' z : ℂ, (if z = z₀ then 0 else ‖D z‖ * ‖lapWin V (z - s)‖) ≤ T / g := by
    rw [hT, ← tsum_div_const]
    refine Summable.tsum_le_tsum (fun z => ?_) ?_ (hsT.div_const g)
    · split_ifs with hzz
      · positivity
      · by_cases hz : D z = 0
        · simp [hz]
        · have := norm_lapWin_sub_le (V := V) hg (hsep z hzz hz)
          rw [hsre] at this
          calc ‖D z‖ * ‖lapWin V (z - s)‖ ≤ ‖D z‖ * ((Real.exp ((z.re - σ) * V) + 1) / g) :=
                mul_le_mul_of_nonneg_left this (norm_nonneg _)
            _ = _ := by ring
    · refine (hsT.div_const g).of_nonneg_of_le (fun z => by split_ifs <;> positivity) fun z => ?_
      split_ifs with hzz
      · positivity
      · by_cases hz : D z = 0
        · simp [hz]
        · have := norm_lapWin_sub_le (V := V) hg (hsep z hzz hz)
          rw [hsre] at this
          calc ‖D z‖ * ‖lapWin V (z - s)‖ ≤ ‖D z‖ * ((Real.exp ((z.re - σ) * V) + 1) / g) :=
                mul_le_mul_of_nonneg_left this (norm_nonneg _)
            _ = _ := by ring
  -- the loudness hypothesis at `s`
  have hTb : T ≤ N * ‖D z₀‖ * Real.exp (θ * V) + ∑' z : ℂ, ‖D z‖ := by
    rw [hTeq]
    have h1 : Real.exp (-σ * V) * ∑' z : ℂ, ‖D z‖ * Real.exp (z.re * V) ≤
        N * ‖D z₀‖ * Real.exp (θ * V) := by
      calc Real.exp (-σ * V) * ∑' z : ℂ, ‖D z‖ * Real.exp (z.re * V)
          ≤ Real.exp (-σ * V) * (N * ‖D z₀‖ * Real.exp (z₀.re * V)) :=
            mul_le_mul_of_nonneg_left hL (Real.exp_pos _).le
        _ = N * ‖D z₀‖ * Real.exp (θ * V) := by
            rw [hθdef, show (z₀.re - σ) * V = -σ * V + z₀.re * V by ring, Real.exp_add]; ring
    linarith
  -- assemble
  have hbig : ‖D z₀‖ * ((Real.exp (θ * V) - 1) / θ) ≤ 4 * |M| / σ + κ * T := by
    rw [← hLHS]
    refine hcore.trans ?_
    have hM0 := abs_nonneg M
    have h1 : |M| * (‖lapWin V (-(σ : ℂ))‖ + ‖lapWin V (-s)‖) ≤ 4 * |M| / σ := by
      calc |M| * (‖lapWin V (-(σ : ℂ))‖ + ‖lapWin V (-s)‖) ≤ |M| * (2 / σ + 2 / σ) :=
            mul_le_mul_of_nonneg_left (add_le_add hE1 hE2) hM0
        _ = 4 * |M| / σ := by ring
    have hT0 : 0 ≤ T := tsum_nonneg fun z => by positivity
    have h2 : T / η + T / g = κ * T := by rw [hκ]; ring
    linarith
  have hexp : 0 ≤ Real.exp (θ * V) - 1 := by
    linarith [Real.one_le_exp (mul_nonneg hθ0.le hV)]
  have hlow : 2 * κ * N * ‖D z₀‖ * (Real.exp (θ * V) - 1) ≤
      ‖D z₀‖ * ((Real.exp (θ * V) - 1) / θ) := by
    have h1 : 2 * κ * N ≤ 1 / θ := by rw [le_div_iff₀ hθ0]; linarith
    calc 2 * κ * N * ‖D z₀‖ * (Real.exp (θ * V) - 1)
        = (2 * κ * N) * (‖D z₀‖ * (Real.exp (θ * V) - 1)) := by ring
      _ ≤ (1 / θ) * (‖D z₀‖ * (Real.exp (θ * V) - 1)) :=
          mul_le_mul_of_nonneg_right h1 (mul_nonneg (norm_nonneg _) hexp)
      _ = _ := by ring
  have hκT : κ * T ≤ κ * (N * ‖D z₀‖ * Real.exp (θ * V)) + κ * ∑' z : ℂ, ‖D z‖ := by
    rw [← mul_add]; exact mul_le_mul_of_nonneg_left hTb hκ0.le
  nlinarith

/-- **Explicit first negative lag.** Under the hypotheses of `loudness_bound_of_lag_nonneg`, if
`κ N |D(z₀)| (e^{θV} − 2) > 4|M|/σ + κ Σ_z |D(z)|`, then some lag `v ∈ [0, V]` has
`Re W(f_v, f_v) < 0`. -/
theorem exists_lag_neg_of_loudness (Z : ZeroConfig) (hZ : TemperedConfig Z) {b : ℝ → ℂ}
    (hb : ContDiff ℝ 2 b) {w : ℝ} (hbs : ∀ u, b u ≠ 0 → |u| ≤ w) {V : ℝ} (hV : 0 ≤ V)
    {η g σ N : ℝ} (hη : 0 < η) (hηz : ∀ z, evenCoeff Z b z ≠ 0 → η ≤ |z.im|) (hg : 0 < g)
    {z₀ : ℂ} (hσ : 0 < σ) (hθ : σ < z₀.re)
    (hsep : ∀ z, z ≠ z₀ → evenCoeff Z b z ≠ 0 → g ≤ ‖z - (σ + z₀.im * I)‖)
    (hθN : 2 * (1 / η + 1 / g) * N * (z₀.re - σ) ≤ 1)
    (hL : ∑' z : ℂ, ‖evenCoeff Z b z‖ * Real.exp (z.re * V) ≤
      N * ‖evenCoeff Z b z₀‖ * Real.exp (z₀.re * V))
    (hbig : 4 * |2 * (lagStructure Z b 0).re| / σ + (1 / η + 1 / g) * ∑' z : ℂ, ‖evenCoeff Z b z‖ <
      (1 / η + 1 / g) * N * ‖evenCoeff Z b z₀‖ * (Real.exp ((z₀.re - σ) * V) - 2)) :
    ∃ v ∈ Icc (0 : ℝ) V, (Z.W (twoBump b v (-1)) (twoBump b v (-1))).re < 0 := by
  by_contra h
  push Not at h
  exact (loudness_bound_of_lag_nonneg Z hZ hb hbs hV h hη hηz hg hσ hθ hsep hθN hL).not_gt hbig

/-! ### For `ζ`: the crowding law -/

/-- The exponents of the lag function of `ζ` keep distance `4` from the real axis. -/
theorem four_le_abs_im_of_evenCoeff_zeta {b : ℝ → ℂ} {z : ℂ}
    (hz : evenCoeff zetaZeroConfig b z ≠ 0) : 4 ≤ |z.im| := by
  have key : ∀ ρ ∈ zetaZeroConfig.carrier, 4 ≤ |ρ.im| := fun ρ hρ => by
    by_contra hlt
    push Not at hlt
    have h : 0 < ρ.re ∧ ρ.re < 1 := hρ.2
    exact riemannZeta_ne_zero_of_abs_im_lt_four h.1 h.2 hlt hρ.1
  rcases mem_of_evenCoeff_ne_zero hz with h | h
  · simpa using key _ h
  · simpa using key _ h

/-- **The crowding law for `ζ`.** Let `0 < w < ½ log 2` and suppose the dyadic window functionals
`P_v` of the difference tests `κ_w(t + v/2) − κ_w(t − v/2)` are nonnegative for every lag
`v ∈ [0, V]`. Then every exponent `z₀` of the lag function (an off-line zero `½ + z₀` when
`Re z₀ > 0`) satisfies, for `0 < σ < Re z₀`, separation `g` of the others from `σ + i Im z₀`,
`κ = 1/4 + 1/g`, `2κN(Re z₀ − σ) ≤ 1` and loudness ratio `N` at lag `V`:
`κ N |D(z₀)| (e^{(Re z₀ − σ)V} − 2) ≤ 4|M|/σ + κ Σ_z |D(z)|`. A zero that is loud at lag `V`
must be crowded: its companions carry a loudness of order `N`. -/
theorem zeta_crowding_of_lag_primeWindow_nonneg {w V : ℝ} (hw : 0 < w) (hw2 : 2 * w < Real.log 2)
    (hV : 0 ≤ V)
    (hP : ∀ v ∈ Icc (0 : ℝ) V, 0 ≤ (lagPrimeWindowRHS v w (EF.weilTest
      (twoBump (modScaledBump w 0) v (-1)) (twoBump (modScaledBump w 0) v (-1)))).re)
    {g σ N : ℝ} (hg : 0 < g) {z₀ : ℂ} (hσ : 0 < σ) (hθ : σ < z₀.re)
    (hsep : ∀ z, z ≠ z₀ → evenCoeff zetaZeroConfig (modScaledBump w 0) z ≠ 0 →
      g ≤ ‖z - (σ + z₀.im * I)‖)
    (hθN : 2 * (1 / 4 + 1 / g) * N * (z₀.re - σ) ≤ 1)
    (hL : ∑' z : ℂ, ‖evenCoeff zetaZeroConfig (modScaledBump w 0) z‖ * Real.exp (z.re * V) ≤
      N * ‖evenCoeff zetaZeroConfig (modScaledBump w 0) z₀‖ * Real.exp (z₀.re * V)) :
    (1 / 4 + 1 / g) * N * ‖evenCoeff zetaZeroConfig (modScaledBump w 0) z₀‖ *
        (Real.exp ((z₀.re - σ) * V) - 2) ≤
      4 * |2 * (lagStructure zetaZeroConfig (modScaledBump w 0) 0).re| / σ +
        (1 / 4 + 1 / g) * ∑' z : ℂ, ‖evenCoeff zetaZeroConfig (modScaledBump w 0) z‖ := by
  have hm : ∀ v ∈ Icc (0 : ℝ) V, 0 ≤ (zetaZeroConfig.W (twoBump (modScaledBump w 0) v (-1))
      (twoBump (modScaledBump w 0) v (-1))).re := fun v hv => by
    rw [zeta_W_eq_literatureRHS (f := twoBump (modScaledBump w 0) v (-1))
      (contDiff_bumpTest (contDiff_modScaledBump_two w 0) v ![1, -1])
      (hasCompactSupport_twoBump (hasCompactSupport_of_support_subset_abs
        (modScaledBump_support hw 0)) v (-1)),
      literatureRHS_twoBump_eq_lagPrimeWindowRHS (modScaledBump_support hw 0) hw2 hv.1]
    exact hP v hv
  exact loudness_bound_of_lag_nonneg zetaZeroConfig temperedConfig_zetaZeroConfig
    (contDiff_modScaledBump_two w 0) (modScaledBump_support hw 0) hV hm (by norm_num)
    (fun z hz => four_le_abs_im_of_evenCoeff_zeta hz) hg hσ hθ hsep hθN hL

end GaloisForLFunctions.SquareRootThreshold
