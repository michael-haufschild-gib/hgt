import GaloisForLFunctions.ArithmeticGaugeTheory.TheLiouvilleTwinInequality
import GaloisForLFunctions.ArithmeticGaugeTheory.TheDirichletPointsCancelThroughPeriodicity
import GaloisForLFunctions.RHTower.DirichletUniformAbel
import GaloisForLFunctions.RHTower.DirichletPolyBoundedAbel
import GaloisForLFunctions.RHTower.DirichletLSeriesBridge
import GaloisForLFunctions.RHTower.BoundedExponentPoissonNonlanding

/-!
# The twin pairs have a quarter floor

Let `F_x(s) = Σ μ(n) χ_x(n) n^{−s} = Π_p (1 − χ_x(p) p^{−s})` be the Möbius series of a gauge point `x`
(`moebiusLSeries`), and let `y` be its Liouville twin, `χ_y(p) = −χ_x(p)`, and `z` its double,
`χ_z(p) = χ_x(p)²`. Prime by prime `(1 − χ_x(p)p^{−s})(1 + χ_x(p)p^{−s}) = 1 − χ_x(p)² p^{−2s}`, so

* **the doubling law** (`moebiusLSeries_mul_twin`): `F_x(s) F_y(s) = F_z(2s)` on `Re s > 1`.

A power bound `O(N^θ)` on the twisted Möbius sums continues the Möbius series holomorphically to
`Re s > θ` (`exists_continuation_of_gaugePowerBound`, Abel summation). So if both twins are bounded at
`θ`, the product continues `F_z(2s)` to `Re s > θ` (`exists_continuation_double`): the Möbius exponents of
a twin pair control the analytic continuation of the doubled point at half the height.

At an order-two point (`χ_x(p) = ±1`) the double is the trivial point and `F_0(2s) = 1/ζ(2s)`, with poles
at `ρ/2` for every zero `ρ`. Hence

* **the quarter floor** (`zetaZeroAbscissa_le_two_mul_max_gaugeExponent`, `quarter_le_max_gaugeExponent`):
  `Θ ≤ 2 max(θ_μ(x), θ_μ(y))`, in particular `max(θ_μ(x), θ_μ(y)) ≥ 1/4`.

The Liouville translation lowers the Möbius exponent of an order-two point below `1/2` only at the
price of its twin: the pair together must carry the poles of `1/ζ(2s)` on `Re s = Θ/2`. This is the
lower companion of the twin inequality `θ_μ(y) ≤ (1 + 2θ_1(x) + θ_μ(2x)/2)/3`.

For the constant source the same doubling law reads `L_x(s) L_y(s) = L_{2x}(2s)` for the fibres
(`oneLSeries_mul_twin`); at order-two points the product is `ζ(2s)`, whose pole at `s = 1/2` gives

* **the half floor** (`half_le_max_gaugeExponent_one`): `max(θ_1(x), θ_1(y)) ≥ 1/2`.

At a real Dirichlet point `θ_1 = 0`, so its Liouville twin has constant-source exponent at least the
typical value `1/2`: twin duality holds for the constant source with the sides exchanged.
-/

open Finset Filter Topology Complex
open scoped ArithmeticFunction.Moebius

noncomputable section

namespace GaloisForLFunctions.ArithmeticGaugeTheory

open ArithmeticCorrelationGeometry

/-- The Möbius series `Σ μ(n) χ_x(n) n^{−s}` of a gauge point. -/
def moebiusLSeries (x : GaugeTorus) (s : ℂ) : ℂ :=
  LSeries (fun n => moebiusSource n * twist x n) s

/-! ### The Euler product -/

private theorem moebiusSource_twist_one (x : GaugeTorus) : moebiusSource 1 * twist x 1 = 1 := by
  simp [moebiusSource]

private theorem norm_moebiusSource_twist_le (x : GaugeTorus) (n : ℕ) :
    ‖moebiusSource n * twist x n‖ ≤ 1 := by
  rw [norm_mul, norm_twist, mul_one]
  exact norm_moebiusSource_le n

/-- The Euler factor of the Möbius series at a prime. -/
private theorem tsum_term_prime_pow (x : GaugeTorus) (s : ℂ) {p : ℕ} (hp : p.Prime) :
    ∑' e : ℕ, LSeries.term (fun n => moebiusSource n * twist x n) s (p ^ e) =
      1 - twist x p * (p : ℂ) ^ (-s) := by
  have hzero : ∀ e ∉ Finset.range 2,
      LSeries.term (fun n => moebiusSource n * twist x n) s (p ^ e) = 0 := by
    intro e he
    have he2 : 2 ≤ e := by simp at he; omega
    have hpe : p ^ e ≠ 0 := pow_ne_zero _ hp.ne_zero
    rw [LSeries.term_of_ne_zero hpe, moebiusSource,
      ArithmeticFunction.moebius_apply_prime_pow hp (by omega), if_neg (by omega)]
    simp
  rw [tsum_eq_sum hzero, Finset.sum_range_succ, Finset.sum_range_one, pow_zero, pow_one,
    LSeries.term_of_ne_zero one_ne_zero, LSeries.term_of_ne_zero hp.ne_zero, moebiusSource_twist_one,
    moebiusSource, ArithmeticFunction.moebius_apply_prime hp, Complex.cpow_neg]
  push_cast
  simp only [Complex.one_cpow, div_one]
  ring

/-- **The Euler product of the Möbius series**: `F_x(s) = Π_p (1 − χ_x(p) p^{−s})` on `Re s > 1`. -/
theorem hasProd_moebiusLSeries (x : GaugeTorus) {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun p : Nat.Primes => 1 - twist x p * ((p : ℕ) : ℂ) ^ (-s)) (moebiusLSeries x s) := by
  set g : ℕ → ℂ := fun n => moebiusSource n * twist x n with hg
  set f : ℕ → ℂ := fun n => LSeries.term g s n with hf
  have hf₁ : f 1 = 1 := by
    simp only [hf, LSeries.term_of_ne_zero one_ne_zero, hg, moebiusSource_twist_one, Nat.cast_one,
      Complex.one_cpow, div_one]
  have hmul : ∀ {m n : ℕ}, Nat.Coprime m n → f (m * n) = f m * f n := by
    intro m n hmn
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [hf]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hf]
    have hm0 : m ≠ 0 := hm.ne'
    have hn0 : n ≠ 0 := hn.ne'
    simp only [hf, LSeries.term_of_ne_zero (mul_ne_zero hm0 hn0), LSeries.term_of_ne_zero hm0,
      LSeries.term_of_ne_zero hn0, hg, moebiusSource]
    rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hmn, twist_mul x hm0 hn0,
      Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
    push_cast
    ring
  have hsum : Summable (‖f ·‖) := by
    have h := LSeriesSummable_of_bounded_of_one_lt_re (m := 1)
      (fun n _ => norm_moebiusSource_twist_le x n) hs
    exact (summable_norm_iff (E := ℂ)).mpr h
  have hf₀ : f 0 = 0 := LSeries.term_zero _ _
  have h := EulerProduct.eulerProduct_hasProd hf₁ hmul hsum hf₀
  have hfac : (fun p : Nat.Primes => ∑' e : ℕ, f ((p : ℕ) ^ e)) =
      fun p : Nat.Primes => 1 - twist x p * ((p : ℕ) : ℂ) ^ (-s) := by
    funext p
    exact tsum_term_prime_pow x s p.prop
  rw [hfac] at h
  exact h

/-- **The doubling law.** For the Liouville twin `y` and the double `z` of `x`,
`F_x(s) F_y(s) = F_z(2s)` on `Re s > 1`. -/
theorem moebiusLSeries_mul_twin {x y z : GaugeTorus}
    (hy : ∀ p, p.Prime → twist y p = -twist x p) (hz : ∀ p, p.Prime → twist z p = twist x p ^ 2)
    {s : ℂ} (hs : 1 < s.re) :
    moebiusLSeries x s * moebiusLSeries y s = moebiusLSeries z (2 * s) := by
  have hs2 : 1 < (2 * s).re := by
    rw [show (2 * s).re = 2 * s.re by simp]; linarith
  have hprod := (hasProd_moebiusLSeries x hs).mul (hasProd_moebiusLSeries y hs)
  have hfac : (fun p : Nat.Primes => (1 - twist x p * ((p : ℕ) : ℂ) ^ (-s)) *
      (1 - twist y p * ((p : ℕ) : ℂ) ^ (-s))) =
      fun p : Nat.Primes => 1 - twist z p * ((p : ℕ) : ℂ) ^ (-(2 * s)) := by
    funext p
    have hp0 : ((p : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr p.prop.ne_zero
    have hpow : ((p : ℕ) : ℂ) ^ (-(2 * s)) = ((p : ℕ) : ℂ) ^ (-s) * ((p : ℕ) : ℂ) ^ (-s) := by
      rw [← Complex.cpow_add _ _ hp0]; ring_nf
    rw [hy p p.prop, hz p p.prop, hpow]
    ring
  rw [hfac] at hprod
  exact hprod.unique (hasProd_moebiusLSeries z hs2)

/-- The Möbius series of the trivial point inverts `ζ`: `F_0(s) ζ(s) = 1` on `Re s > 1`. -/
theorem moebiusLSeries_zero_mul_riemannZeta {s : ℂ} (hs : 1 < s.re) :
    moebiusLSeries 0 s * riemannZeta s = 1 := by
  have hprod := (hasProd_moebiusLSeries 0 hs).mul (riemannZeta_eulerProduct_hasProd hs)
  have hfac : (fun p : Nat.Primes => (1 - twist 0 p * ((p : ℕ) : ℂ) ^ (-s)) *
      (1 - ((p : ℕ) : ℂ) ^ (-s))⁻¹) = fun _ => 1 := by
    funext p
    have hlt : ‖((p : ℕ) : ℂ) ^ (-s)‖ < 1 := by
      rw [Complex.norm_natCast_cpow_of_pos p.prop.pos, Complex.neg_re]
      exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast p.prop.one_lt) (by linarith)
    have hne : (1 : ℂ) - ((p : ℕ) : ℂ) ^ (-s) ≠ 0 := by
      intro h
      have : ((p : ℕ) : ℂ) ^ (-s) = 1 := by linear_combination -h
      rw [this, norm_one] at hlt
      exact lt_irrefl _ hlt
    rw [twist_zero, one_mul, mul_inv_cancel₀ hne]
  rw [hfac] at hprod
  exact hprod.unique hasProd_one

/-! ### Continuation from a power bound -/

/-- **A power bound continues the twisted series.** If `‖Σ_{n ≤ N} a(n) χ_x(n)‖ ≤ C (N+1)^θ` with
`‖a‖ ≤ 1`, the series `Σ a(n) χ_x(n) n^{−s}` continues holomorphically to `Re s > θ`. -/
theorem exists_continuation_of_gaugePowerBound {a : ℕ → ℂ} (ha : ∀ n, ‖a n‖ ≤ 1)
    {x : GaugeTorus} {θ : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ < 1) (h : GaugePowerBound a x θ) :
    ∃ F : ℂ → ℂ, DifferentiableOn ℂ F {s : ℂ | θ < s.re} ∧
      ∀ s : ℂ, 1 < s.re → F s = LSeries (fun n => a n * twist x n) s := by
  obtain ⟨C, hC, hb⟩ := h
  set b : ℕ → ℂ := fun n => a n * twist x n with hbdef
  set c : ℕ → ℂ := fun n => b (n + 1) with hcdef
  have hb0 : ‖b 0‖ ≤ 1 := by rw [hbdef]; simp only [norm_mul, norm_twist, mul_one]; exact ha 0
  have hbound : ∀ N : ℕ, ‖∑ n ∈ range N, c n‖ ≤ (C + 1) * ((N : ℝ) + 1) ^ θ := by
    intro N
    have hsplit := Finset.sum_range_succ' b N
    have : ∑ n ∈ range N, c n = ∑ n ∈ range (N + 1), b n - b 0 := by rw [hsplit]; ring
    rw [this]
    have hone : (1 : ℝ) ≤ ((N : ℝ) + 1) ^ θ := Real.one_le_rpow (by linarith [N.cast_nonneg (α := ℝ)]) hθ
    calc ‖∑ n ∈ range (N + 1), b n - b 0‖ ≤ ‖∑ n ∈ range (N + 1), b n‖ + ‖b 0‖ := norm_sub_le _ _
      _ ≤ C * ((N : ℝ) + 1) ^ θ + 1 * ((N : ℝ) + 1) ^ θ := add_le_add (hb N) (by linarith)
      _ = (C + 1) * ((N : ℝ) + 1) ^ θ := by ring
  have hconv : ∀ s : ℂ, θ < s.re → RHTower.DirichletConvergesAt c s := fun s hs =>
    RHTower.tendsto_dirichlet_partialSum_of_poly_bounded (by linarith) hθ hbound hs
  refine ⟨RHTower.dirichletSum c, ?_, ?_⟩
  · intro s hs
    have hs' : θ < s.re := hs
    set s₀ : ℂ := (((θ + s.re) / 2 : ℝ) : ℂ) with hs₀
    have hs₀re : s₀.re = (θ + s.re) / 2 := by simp [hs₀]
    have hd := RHTower.differentiableOn_dirichletSum (hconv s₀ (by rw [hs₀re]; linarith))
    have hopen : IsOpen {w : ℂ | s₀.re < w.re} := isOpen_lt continuous_const Complex.continuous_re
    have hmem : s ∈ {w : ℂ | s₀.re < w.re} := by
      show s₀.re < s.re; rw [hs₀re]; linarith
    exact ((hd s hmem).differentiableAt (hopen.mem_nhds hmem)).differentiableWithinAt
  · intro s hs
    have hlim₁ := RHTower.tendsto_dirichletSum (hconv s (by linarith))
    have hsum : LSeriesSummable b s := LSeriesSummable_of_bounded_of_one_lt_re (m := 1)
      (fun n _ => by rw [hbdef, norm_mul, norm_twist, mul_one]; exact ha n) hs
    have hlim₂ : Tendsto (fun N => ∑ n ∈ range (N + 1), LSeries.term b s n) atTop
        (𝓝 (LSeries b s)) :=
      hsum.LSeriesHasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
    have heq : ∀ N, RHTower.dirichletPartialSum c N s = ∑ n ∈ range (N + 1), LSeries.term b s n := by
      intro N
      rw [Finset.sum_range_succ', LSeries.term_zero, add_zero]
      exact Finset.sum_congr rfl fun n _ => (RHTower.term_succ_eq b s n).symm
    exact tendsto_nhds_unique hlim₁ (hlim₂.congr fun N => (heq N).symm)

/-- **The twins continue the double.** If both twins carry a power bound at `θ`, the series `F_z(2s)`
of the double continues holomorphically to `Re s > θ`. -/
theorem exists_continuation_double {x y z : GaugeTorus}
    (hy : ∀ p, p.Prime → twist y p = -twist x p) (hz : ∀ p, p.Prime → twist z p = twist x p ^ 2)
    {θ : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ < 1) (hbx : GaugePowerBound moebiusSource x θ)
    (hby : GaugePowerBound moebiusSource y θ) :
    ∃ G : ℂ → ℂ, DifferentiableOn ℂ G {s : ℂ | θ < s.re} ∧
      ∀ s : ℂ, 1 < s.re → G s = moebiusLSeries z (2 * s) := by
  obtain ⟨Fx, hFx, hFxeq⟩ := exists_continuation_of_gaugePowerBound norm_moebiusSource_le hθ hθ1 hbx
  obtain ⟨Fy, hFy, hFyeq⟩ := exists_continuation_of_gaugePowerBound norm_moebiusSource_le hθ hθ1 hby
  refine ⟨fun s => Fx s * Fy s, hFx.mul hFy, fun s hs => ?_⟩
  show Fx s * Fy s = _
  rw [hFxeq s hs, hFyeq s hs]
  exact moebiusLSeries_mul_twin hy hz hs

/-! ### The quarter floor -/

/-- **The twins of an order-two point bound the zero abscissa.** If `χ_x(p) = ±1` and both `x` and its
Liouville twin `y` have Möbius sums `O(N^θ)`, then `Θ ≤ 2θ`. -/
theorem zetaZeroAbscissa_le_two_mul_of_twins {x y : GaugeTorus}
    (hx : ∀ p, p.Prime → twist x p ^ 2 = 1) (hy : ∀ p, p.Prime → twist y p = -twist x p)
    {θ : ℝ} (hθ : 0 ≤ θ) (hbx : GaugePowerBound moebiusSource x θ)
    (hby : GaugePowerBound moebiusSource y θ) :
    RHTower.zetaZeroAbscissa ≤ 2 * θ := by
  by_contra hlt
  push Not at hlt
  have hθ1 : θ < 1 / 2 := by linarith [RHTower.zetaZeroAbscissa_le_one]
  obtain ⟨G, hG, hGeq⟩ := exists_continuation_double hy (fun p hp => by rw [twist_zero, hx p hp])
    hθ (by linarith) hbx hby
  obtain ⟨ρ, hρzero, hρ1, hρre⟩ := RHTower.exists_zetaZero_mem_openStrip_lt_re hlt
  -- `H(s) = (2s − 1) ζ(2s) G(s)` equals `2s − 1` on `Re s > 1`, hence on `Re s > θ`.
  set U : Set ℂ := {s : ℂ | θ < s.re} with hU
  set H : ℂ → ℂ := fun s => RHTower.zetaEntire (2 * s) * G s with hH
  have hUopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hHd : DifferentiableOn ℂ H U :=
    ((RHTower.differentiable_zetaEntire.comp (differentiable_id.const_mul 2)).differentiableOn).mul hG
  have hLd : DifferentiableOn ℂ (fun s : ℂ => 2 * s - 1) U :=
    ((differentiable_id.const_mul 2).sub_const 1).differentiableOn
  have hright : ∀ s : ℂ, 1 < s.re → H s = 2 * s - 1 := by
    intro s hs
    have hs2 : 1 < (2 * s).re := by rw [show (2 * s).re = 2 * s.re by simp]; linarith
    have hne : 2 * s ≠ 1 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    simp only [hH]
    rw [RHTower.zetaEntire_eq hne, hGeq s hs]
    have hinv := moebiusLSeries_zero_mul_riemannZeta hs2
    linear_combination (2 * s - 1) * hinv
  have h2 : (2 : ℂ) ∈ U := by show θ < (2 : ℂ).re; simp; linarith
  have hev : H =ᶠ[𝓝 (2 : ℂ)] fun s => 2 * s - 1 := by
    have hopen1 : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen1.mem_nhds (show (1 : ℝ) < (2 : ℂ).re by simp)] with s hs
    exact hright s hs
  have hEq := (hHd.analyticOnNhd hUopen).eqOn_of_preconnected_of_eventuallyEq
    (hLd.analyticOnNhd hUopen) (convex_halfSpace_re_gt θ).isPreconnected h2 hev
  -- At `s₀ = ρ/2` the left side vanishes and the right side is `ρ − 1 ≠ 0`.
  set s₀ : ℂ := ρ / 2 with hs₀
  have hs₀U : s₀ ∈ U := by
    show θ < (ρ / 2).re
    rw [Complex.div_re]; simp; nlinarith
  have hρne : ρ ≠ 1 := by intro h; rw [h] at hρ1; simp at hρ1
  have h2s₀ : 2 * s₀ = ρ := by rw [hs₀]; ring
  have hval := hEq hs₀U
  simp only [hH, h2s₀, RHTower.zetaEntire_eq hρne, hρzero, mul_zero, zero_mul] at hval
  have : ρ - 1 = 0 := by linear_combination -hval
  exact hρne (sub_eq_zero.mp this)

/-- **The quarter floor, sharp form.** At an order-two point `x` with Liouville twin `y`,
`Θ ≤ 2 max(θ_μ(x), θ_μ(y))`. -/
theorem zetaZeroAbscissa_le_two_mul_max_gaugeExponent {x y : GaugeTorus}
    (hx : ∀ p, p.Prime → twist x p ^ 2 = 1) (hy : ∀ p, p.Prime → twist y p = -twist x p) :
    RHTower.zetaZeroAbscissa ≤
      2 * max (gaugeExponent moebiusSource x) (gaugeExponent moebiusSource y) := by
  set m := max (gaugeExponent moebiusSource x) (gaugeExponent moebiusSource y) with hm
  have hm0 : 0 ≤ m := (gaugeExponent_nonneg norm_moebiusSource_le).trans (le_max_left _ _)
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  have hθ : m < m + ε / 4 := by linarith
  have hbx := gaugePowerBound_of_gaugeExponent_lt norm_moebiusSource_le
    ((le_max_left _ _).trans_lt hθ)
  have hby := gaugePowerBound_of_gaugeExponent_lt norm_moebiusSource_le
    ((le_max_right _ _).trans_lt hθ)
  have h := zetaZeroAbscissa_le_two_mul_of_twins hx hy (by linarith) hbx hby
  linarith

/-- **The quarter floor.** A twin pair of order-two gauge points cannot both have Möbius exponent
below `1/4`. -/
theorem quarter_le_max_gaugeExponent {x y : GaugeTorus}
    (hx : ∀ p, p.Prime → twist x p ^ 2 = 1) (hy : ∀ p, p.Prime → twist y p = -twist x p) :
    1 / 4 ≤ max (gaugeExponent moebiusSource x) (gaugeExponent moebiusSource y) := by
  have h := zetaZeroAbscissa_le_two_mul_max_gaugeExponent hx hy
  linarith [RHTower.half_le_zetaZeroAbscissa]

/-! ### The constant source: the half floor -/

/-- The fibre `n ↦ χ_x(n) n^{−s}` as a completely multiplicative function. -/
private def fibreHom (x : GaugeTorus) (s : ℂ) : ℕ →*₀ ℂ where
  toFun n := if n = 0 then 0 else twist x n * (n : ℂ) ^ (-s)
  map_zero' := by simp
  map_one' := by simp
  map_mul' m n := by
    by_cases hm : m = 0
    · simp [hm]
    by_cases hn : n = 0
    · simp [hn]
    simp only [mul_eq_zero, hm, hn, or_self, if_false, Nat.cast_mul]
    rw [twist_mul x hm hn, Complex.natCast_mul_natCast_cpow]
    ring

private theorem fibreHom_eq_term (x : GaugeTorus) (s : ℂ) (n : ℕ) :
    fibreHom x s n = LSeries.term (fun n => oneSource n * twist x n) s n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [fibreHom]
  · show (if n = 0 then 0 else twist x n * (n : ℂ) ^ (-s)) = _
    rw [if_neg hn, LSeries.term_of_ne_zero hn, oneSource, one_mul, Complex.cpow_neg, div_eq_mul_inv]

/-- **The Euler product of the fibre**: `L_x(s) = Π_p (1 − χ_x(p) p^{−s})^{−1}` on `Re s > 1`. -/
theorem hasProd_oneLSeries (x : GaugeTorus) {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun p : Nat.Primes => (1 - twist x p * ((p : ℕ) : ℂ) ^ (-s))⁻¹)
      (LSeries (fun n => oneSource n * twist x n) s) := by
  have hsum0 := LSeriesSummable_of_bounded_of_one_lt_re (m := 1)
    (f := fun n => oneSource n * twist x n) (fun n _ => by simp [oneSource, norm_twist]) hs
  have hsum : Summable (‖fibreHom x s ·‖) := by
    have : (fun n => ‖fibreHom x s n‖) = fun n => ‖LSeries.term (fun n => oneSource n * twist x n) s n‖ :=
      funext fun n => by rw [fibreHom_eq_term]
    rw [this]
    exact (summable_norm_iff (E := ℂ)).mpr hsum0
  have h := EulerProduct.eulerProduct_completely_multiplicative_hasProd hsum
  have hval : ∑' n, fibreHom x s n = LSeries (fun n => oneSource n * twist x n) s :=
    tsum_congr fun n => fibreHom_eq_term x s n
  have hfac : (fun p : Nat.Primes => (1 - fibreHom x s p)⁻¹) =
      fun p : Nat.Primes => (1 - twist x p * ((p : ℕ) : ℂ) ^ (-s))⁻¹ := by
    funext p
    show (1 - (if (p : ℕ) = 0 then 0 else twist x p * ((p : ℕ) : ℂ) ^ (-s)))⁻¹ = _
    rw [if_neg p.prop.ne_zero]
  rw [hval, hfac] at h
  exact h

/-- **The doubling law for the fibres.** `L_x(s) L_y(s) = L_z(2s)` on `Re s > 1`. -/
theorem oneLSeries_mul_twin {x y z : GaugeTorus}
    (hy : ∀ p, p.Prime → twist y p = -twist x p) (hz : ∀ p, p.Prime → twist z p = twist x p ^ 2)
    {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => oneSource n * twist x n) s * LSeries (fun n => oneSource n * twist y n) s =
      LSeries (fun n => oneSource n * twist z n) (2 * s) := by
  have hs2 : 1 < (2 * s).re := by
    rw [show (2 * s).re = 2 * s.re by simp]; linarith
  have hprod := (hasProd_oneLSeries x hs).mul (hasProd_oneLSeries y hs)
  have hfac : (fun p : Nat.Primes => (1 - twist x p * ((p : ℕ) : ℂ) ^ (-s))⁻¹ *
      (1 - twist y p * ((p : ℕ) : ℂ) ^ (-s))⁻¹) =
      fun p : Nat.Primes => (1 - twist z p * ((p : ℕ) : ℂ) ^ (-(2 * s)))⁻¹ := by
    funext p
    have hp0 : ((p : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr p.prop.ne_zero
    have hpow : ((p : ℕ) : ℂ) ^ (-(2 * s)) = ((p : ℕ) : ℂ) ^ (-s) * ((p : ℕ) : ℂ) ^ (-s) := by
      rw [← Complex.cpow_add _ _ hp0]; ring_nf
    rw [hy p p.prop, hz p p.prop, hpow, ← mul_inv]
    ring_nf
  rw [hfac] at hprod
  exact hprod.unique (hasProd_oneLSeries z hs2)

private theorem zetaEntire_one : RHTower.zetaEntire 1 = 1 := by
  simp [RHTower.zetaEntire, Complex.Gammaℝ_one]

/-- **The half floor.** At an order-two gauge point `x` with Liouville twin `y`, the constant-source
exponents satisfy `max(θ_1(x), θ_1(y)) ≥ 1/2`: the product of the two fibres is `ζ(2s)`, whose pole at
`s = 1/2` no pair of series bounded below `1/2` can carry. -/
theorem half_le_max_gaugeExponent_one {x y : GaugeTorus}
    (hx : ∀ p, p.Prime → twist x p ^ 2 = 1) (hy : ∀ p, p.Prime → twist y p = -twist x p) :
    1 / 2 ≤ max (gaugeExponent oneSource x) (gaugeExponent oneSource y) := by
  by_contra hlt
  push Not at hlt
  set m := max (gaugeExponent oneSource x) (gaugeExponent oneSource y) with hm
  have hm0 : 0 ≤ m := (gaugeExponent_nonneg norm_oneSource_le).trans (le_max_left _ _)
  set θ : ℝ := (m + 1 / 2) / 2 with hθdef
  have hθ0 : 0 ≤ θ := by rw [hθdef]; linarith
  have hθm : m < θ := by rw [hθdef]; linarith
  have hθh : θ < 1 / 2 := by rw [hθdef]; linarith
  obtain ⟨Fx, hFx, hFxeq⟩ := exists_continuation_of_gaugePowerBound norm_oneSource_le hθ0
    (by linarith) (gaugePowerBound_of_gaugeExponent_lt norm_oneSource_le ((le_max_left _ _).trans_lt hθm))
  obtain ⟨Fy, hFy, hFyeq⟩ := exists_continuation_of_gaugePowerBound norm_oneSource_le hθ0
    (by linarith) (gaugePowerBound_of_gaugeExponent_lt norm_oneSource_le ((le_max_right _ _).trans_lt hθm))
  -- `(2s − 1) Fx Fy` and `(2s − 1) ζ(2s)` agree on `Re s > 1`, hence on `Re s > θ`; at `s = 1/2` the first
  -- vanishes and the second is the residue `1`.
  set U : Set ℂ := {s : ℂ | θ < s.re} with hU
  have hUopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  set H : ℂ → ℂ := fun s => (2 * s - 1) * (Fx s * Fy s) with hH
  have hHd : DifferentiableOn ℂ H U :=
    (((differentiable_id.const_mul 2).sub_const 1).differentiableOn).mul (hFx.mul hFy)
  have hZd : DifferentiableOn ℂ (fun s : ℂ => RHTower.zetaEntire (2 * s)) U :=
    (RHTower.differentiable_zetaEntire.comp (differentiable_id.const_mul 2)).differentiableOn
  have hright : ∀ s : ℂ, 1 < s.re → H s = RHTower.zetaEntire (2 * s) := by
    intro s hs
    have hne : 2 * s ≠ 1 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    simp only [hH]
    rw [RHTower.zetaEntire_eq hne, hFxeq s hs, hFyeq s hs,
      oneLSeries_mul_twin hy (z := 0) (fun p hp => by rw [twist_zero, hx p hp]) hs]
    have hs2 : 1 < (2 * s).re := by rw [show (2 * s).re = 2 * s.re by simp]; linarith
    have hz : LSeries (fun n => oneSource n * twist 0 n) (2 * s) = riemannZeta (2 * s) := by
      rw [← (hasProd_oneLSeries 0 hs2).tprod_eq, ← (riemannZeta_eulerProduct_hasProd hs2).tprod_eq]
      exact tprod_congr fun p => by rw [twist_zero, one_mul]
    rw [hz]
  have h2 : (2 : ℂ) ∈ U := by show θ < (2 : ℂ).re; simp; linarith
  have hev : H =ᶠ[𝓝 (2 : ℂ)] fun s => RHTower.zetaEntire (2 * s) := by
    have hopen1 : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen1.mem_nhds (show (1 : ℝ) < (2 : ℂ).re by simp)] with s hs
    exact hright s hs
  have hEq := (hHd.analyticOnNhd hUopen).eqOn_of_preconnected_of_eventuallyEq
    (hZd.analyticOnNhd hUopen) (convex_halfSpace_re_gt θ).isPreconnected h2 hev
  have hhalf : (1 / 2 : ℂ) ∈ U := by show θ < (1 / 2 : ℂ).re; norm_num; linarith
  have hval := hEq hhalf
  simp only [hH] at hval
  rw [show (2 : ℂ) * (1 / 2) = 1 by norm_num, zetaEntire_one] at hval
  norm_num at hval

/-- **Twin duality for the constant source.** At a real nonprincipal Dirichlet point the constant
source has exponent `0`; its Liouville twin has exponent at least the typical value `1/2`. -/
theorem half_le_gaugeExponent_one_liouvilleTwin {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) (hχ2 : χ ^ 2 = 1) {y : GaugeTorus}
    (hy : ∀ p, p.Prime → twist y p = -twist (dirichletGauge χ) p) :
    1 / 2 ≤ gaugeExponent oneSource y := by
  have hx : ∀ p, p.Prime → twist (dirichletGauge χ) p ^ 2 = 1 := by
    intro p hp
    by_cases hcop : Nat.Coprime p q
    · rw [twist_dirichletGauge χ hp.ne_zero hcop, sq, ← Pi.mul_apply, ← MulChar.coeToFun_mul, ← sq,
        hχ2, MulChar.one_apply ((ZMod.isUnit_iff_coprime p q).mpr hcop)]
    · rw [twist_prime _ hp, show dirichletGauge χ p = 0 from if_neg hcop]
      simp
  have h := half_le_max_gaugeExponent_one hx hy
  rwa [gaugeExponent_one_dirichletGauge χ hχ, max_eq_right (gaugeExponent_nonneg norm_oneSource_le)]
    at h

end GaloisForLFunctions.ArithmeticGaugeTheory

end
