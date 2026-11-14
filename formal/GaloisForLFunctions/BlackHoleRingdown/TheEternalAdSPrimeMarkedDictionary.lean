import GaloisForLFunctions.BlackHoleRingdown.TheModularBlackHoleIsAQuotientOfAntiDeSitter
import GaloisForLFunctions.BlackHoleRingdown.TheSharpAnalyticBoundary
import GaloisForLFunctions.BlackHoleRingdown.TheRingdownRateIsTheZeroFreeStrip
import GaloisForLFunctions.RHTower.XiLaguerrePolya
import GaloisForLFunctions.MetaplecticMobiusDescent.Detector.QuasiRiemannHypothesis
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries

/-!
# The Eternal-AdS Prime-Marked Boundary Dictionary

This module establishes the global two-boundary Kruskal–Maldacena geometry of the massless
topological `AdS₄` black hole, the independent prime-cycle gate construction of the modular cusp
echo source, unconditional global Lax–Phillips Schur passivity on the causal half-plane, and the
complete multiplicity-preserving boundary singularity dictionary for both single-boundary retarded
(`G_R`) and two-boundary thermofield Wightman (`G_{RL}`) correlators at Hawking inverse temperature
`β_H = 2π`:

1. **Global Kruskal–Maldacena two-boundary `AdS₄` geometry** (`wedgeReflection`,
   `leftAdsEmbedding`, `kruskalEmbedding`):
   - `Θ_{RL}(X₀,X₁,X₂,X₃,X₄) = (X₀,X₁,X₂,-X₃,-X₄)` is an `SO(3,2)` isometry exchanging the
     disjoint right and left Rindler wedges `W_R, W_L`, realized by the Euclidean half-period KMS
     shift `t ↦ t - iπ`, and commuting identically with `ambientLorentz` for every `γ ∈ SL₂(ℝ)`.
   - `kruskalEmbedding U V x y` (`1 + U V ≠ 0`, `y > 0`) maps into the `AdS₄` quadric `⟨X, X⟩ = -1`,
     covers both exteriors (`W_R` and `W_L`) and the bifurcate horizon `U V = 0`, and is
     `SL₂(ℝ)`-equivariant across the entire two-sided spacetime.

2. **Independent prime-marked cycle gates** (`primeEchoSeries`, `primeEchoGate`,
   `hasProd_primeEchoGate`):
   - At each rational prime `p`, the local cycle transfer series of primitive delay `2 log p` sums
     to `(1 - p^{-(2w+1)}) / (1 - p^{-2w})` on `Re w > 0`.
   - Without assuming `ζ` in the local gate definition, the Euler product over `Nat.Primes` on
     `Re w > 1/2` equals `ζ(2w) / ζ(2w + 1)`, and multiplying by the `AdS` worldline bounce
     `B(w, 1/2)` recovers the Laplace transform `Λ(2w) / Λ(2w + 1)` of `echoKernel`.

3. **Unconditional Hadamard–Schur passivity** (`norm_xi_two_mul_le_of_re_nonneg`,
   `norm_modularReducedScattering_le_one`):
   - Using the unconditional Hadamard product of `XiC` exhausted over reflection-paired divisor
     subsets, `‖xi(2w)‖ ≤ ‖xi(1 + 2w)‖` holds across the entire closed causal half-plane `Re w ≥ 0`.

4. **Complete eternal-AdS single- and two-boundary singularity dictionary**
   (`modularRetardedCorrelator_order_at_zero`, `modularWightmanRL_order_lower`,
   `modularWightmanRL_isPole_iff`, `riemannHypothesis_iff_modularWightmanRL_quarter_strip`,
   `modularWightmanRL_analyticOnNhd_one_sixteenth`):
   - On `0 < |Im ω| < 1/2`, all Hawking–Matsubara poles `ω = i k` (`k ∈ ℤ`) are strictly excluded,
     and the poles of `G_{RL}(ω)` coincide with `{± i(ρ - 1)/2 : ξ(ρ) = 0}` with exact multiplicity
     `-ord_ρ ξ`.
   - Quarter-strip analyticity `0 < |Im ω| < 1/4` of `G_{RL}` is equivalent to `RiemannHypothesis`
     and to quarter-rate pulse ringdown, while `0 < |Im ω| < 1/16` holds unconditionally.
-/

set_option autoImplicit false

open Complex MeasureTheory Set Filter Topology
open scoped MatrixGroups

namespace GaloisForLFunctions.BlackHoleRingdown

open _root_.RHTower
open GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
  (riemannZeta_zero_mem_quasiRH_strip)

noncomputable section

/-! ## 1. Global Two-Boundary Kruskal–Maldacena `AdS₄` Geometry -/

/-- Wedge-reversing involution `Θ_{RL}(X₀,X₁,X₂,X₃,X₄) = (X₀,X₁,X₂,-X₃,-X₄)` in `ℝ^{3,2}`
exchanging the right and left Rindler exteriors of the eternal `AdS₄` black hole. -/
def wedgeReflection (X : Fin 5 → ℝ) : Fin 5 → ℝ :=
  ![X 0, X 1, X 2, -X 3, -X 4]

@[simp]
theorem wedgeReflection_involutive (X : Fin 5 → ℝ) :
    wedgeReflection (wedgeReflection X) = X := by
  funext i
  fin_cases i <;> simp [wedgeReflection]

/-- `Θ_{RL}` preserves the `ℝ^{3,2}` quadratic form. -/
theorem ambientForm_wedgeReflection (X X' : Fin 5 → ℝ) :
    ambientForm (wedgeReflection X) (wedgeReflection X') = ambientForm X X' := by
  simp only [ambientForm, wedgeReflection, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
    Matrix.tail_cons]
  ring

/-- `Θ_{RL}` commutes identically with every Möbius Lorentz transformation `Λ_γ`. -/
theorem wedgeReflection_comm_ambientLorentz (a b c d : ℝ) (X : Fin 5 → ℝ) :
    wedgeReflection (ambientLorentz a b c d X) =
      ambientLorentz a b c d (wedgeReflection X) := by
  funext i
  fin_cases i <;> simp [wedgeReflection, ambientLorentz]

/-- Embedding of the left Rindler exterior `W_L` into `ℝ^{3,2}`. -/
def leftAdsEmbedding (t r x y : ℝ) : Fin 5 → ℝ :=
  wedgeReflection (adsEmbedding t r x y)

theorem ambientForm_leftAdsEmbedding (t : ℝ) {r : ℝ} (hr : 1 ≤ r) (x : ℝ) {y : ℝ} (hy : y ≠ 0) :
    ambientForm (leftAdsEmbedding t r x y) (leftAdsEmbedding t r x y) = -1 := by
  rw [leftAdsEmbedding, ambientForm_wedgeReflection]
  exact ambientForm_adsEmbedding t hr x hy

/-- `leftAdsEmbedding` maps `r > 1, y > 0` into the left Rindler wedge `X₃ < -|X₄|`, `X₀ > X₁`. -/
theorem leftAdsEmbedding_mem_leftWedge (t : ℝ) {r : ℝ} (hr : 1 < r) (x : ℝ) {y : ℝ} (hy : 0 < y) :
    leftAdsEmbedding t r x y 3 < -|leftAdsEmbedding t r x y 4| ∧
      leftAdsEmbedding t r x y 1 < leftAdsEmbedding t r x y 0 := by
  obtain ⟨h34, h01⟩ := adsEmbedding_mem_wedge t hr x hy
  refine ⟨?_, ?_⟩
  · simp only [leftAdsEmbedding, wedgeReflection, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, abs_neg]
    linarith
  · simpa [leftAdsEmbedding, wedgeReflection] using h01

/-- The right and left exterior Rindler wedges are strictly disjoint. -/
theorem adsEmbedding_ne_leftAdsEmbedding (t : ℝ) {r : ℝ} (hr : 1 < r) (x : ℝ) {y : ℝ} (hy : 0 < y)
    (t' : ℝ) {r' : ℝ} (hr' : 1 < r') (x' : ℝ) {y' : ℝ} (hy' : 0 < y') :
    adsEmbedding t r x y ≠ leftAdsEmbedding t' r' x' y' := by
  intro heq
  have hR := (adsEmbedding_mem_wedge t hr x hy).1
  have hL := (leftAdsEmbedding_mem_leftWedge t' hr' x' hy').1
  have h3 := congrFun heq 3
  have h0R : 0 < adsEmbedding t r x y 3 := lt_of_le_of_lt (abs_nonneg _) hR
  have h0L : leftAdsEmbedding t' r' x' y' 3 < 0 :=
    lt_of_lt_of_le hL (neg_nonpos.mpr (abs_nonneg _))
  linarith

/-- Complexified Rindler KMS half-period shift `t ↦ t - iπ` (`β_H = 2π`) negates `(cosh t, sinh t)`,
implementing the thermofield wedge reflection `Θ_{RL}`. -/
theorem kmsHalfPeriod_cosh_sinh (t : ℝ) :
    Complex.cosh ((t : ℂ) - Real.pi * I) = -(Real.cosh t : ℂ) ∧
      Complex.sinh ((t : ℂ) - Real.pi * I) = -(Real.sinh t : ℂ) := by
  have hc : Complex.cosh ((Real.pi : ℂ) * I) = -1 := by
    rw [Complex.cosh_mul_I, Complex.cos_pi]
  have hs : Complex.sinh ((Real.pi : ℂ) * I) = 0 := by
    rw [Complex.sinh_mul_I, Complex.sin_pi, zero_mul]
  constructor
  · rw [Complex.cosh_sub, hc, hs, Complex.ofReal_cosh]
    ring
  · rw [Complex.sinh_sub, hc, hs, Complex.ofReal_sinh]
    ring

/-- Global Kruskal–Maldacena map covering both exterior Rindler wedges (`UV < 0`), the bifurcate
Killing horizon (`UV = 0`), and the future and past black/white-hole interiors (`0 < UV < 1`). -/
def kruskalEmbedding (U V x y : ℝ) : Fin 5 → ℝ :=
  ![((1 - U * V) / (1 + U * V)) * hyperboloid x y 0,
    ((1 - U * V) / (1 + U * V)) * hyperboloid x y 1,
    ((1 - U * V) / (1 + U * V)) * hyperboloid x y 2,
    (V - U) / (1 + U * V),
    (V + U) / (1 + U * V)]

/-- Every point of the Kruskal chart (`1 + U V ≠ 0`, `y ≠ 0`) lies on the `AdS₄` quadric
`⟨X, X⟩ = -1`. -/
theorem ambientForm_kruskalEmbedding {U V : ℝ} (hUV : 1 + U * V ≠ 0) (x : ℝ) {y : ℝ} (hy : y ≠ 0) :
    ambientForm (kruskalEmbedding U V x y) (kruskalEmbedding U V x y) = -1 := by
  have hY := hyperboloid_lorentz (x := x) hy
  simp only [ambientForm, kruskalEmbedding, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
    Matrix.tail_cons]
  have hsplit :
      -(((1 - U * V) / (1 + U * V) * hyperboloid x y 0) *
          ((1 - U * V) / (1 + U * V) * hyperboloid x y 0)) +
        ((1 - U * V) / (1 + U * V) * hyperboloid x y 1) *
          ((1 - U * V) / (1 + U * V) * hyperboloid x y 1) +
        ((1 - U * V) / (1 + U * V) * hyperboloid x y 2) *
          ((1 - U * V) / (1 + U * V) * hyperboloid x y 2) =
        ((1 - U * V) / (1 + U * V)) ^ 2 *
          (-(hyperboloid x y 0) ^ 2 + (hyperboloid x y 1) ^ 2 + (hyperboloid x y 2) ^ 2) := by
    ring
  rw [hsplit, hY]
  field_simp
  ring

/-- Kruskal reflection `(U, V) ↦ (-U, -V)` implements the `SO(3,2)` wedge reflection `Θ_{RL}`. -/
theorem kruskalEmbedding_neg (U V x y : ℝ) :
    kruskalEmbedding (-U) (-V) x y = wedgeReflection (kruskalEmbedding U V x y) := by
  funext i
  fin_cases i <;> simp [kruskalEmbedding, wedgeReflection] <;> ring

/-- On the bifurcate Killing horizon `U V = 0`, `X₃² = X₄²`. -/
theorem kruskalEmbedding_horizon_null {U V : ℝ} (h0 : U * V = 0) (x y : ℝ) :
    (kruskalEmbedding U V x y 3) ^ 2 = (kruskalEmbedding U V x y 4) ^ 2 := by
  simp only [kruskalEmbedding, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
    Matrix.tail_cons, h0, add_zero, div_one]
  linear_combination -4 * h0

/-- Right-exterior Kruskal null coordinate `U = -√((r - 1)/(r + 1)) e^{-t}`. -/
def kruskalU (t r : ℝ) : ℝ := -Real.sqrt ((r - 1) / (r + 1)) * Real.exp (-t)

/-- Right-exterior Kruskal null coordinate `V = √((r - 1)/(r + 1)) e^t`. -/
def kruskalV (t r : ℝ) : ℝ := Real.sqrt ((r - 1) / (r + 1)) * Real.exp t

/-- On the right exterior `r > 1`, `kruskalEmbedding` restricts to `adsEmbedding`. -/
theorem kruskalEmbedding_right_exterior (t : ℝ) {r : ℝ} (hr : 1 < r) (x y : ℝ) :
    kruskalEmbedding (kruskalU t r) (kruskalV t r) x y = adsEmbedding t r x y := by
  have hrp : 0 < r + 1 := by linarith
  have hrm : 0 ≤ r - 1 := by linarith
  have hsq : Real.sqrt ((r - 1) / (r + 1)) ^ 2 = (r - 1) / (r + 1) :=
    Real.sq_sqrt (div_nonneg hrm hrp.le)
  have hexp : Real.exp (-t) * Real.exp t = 1 := by rw [← Real.exp_add]; simp
  have hUV : kruskalU t r * kruskalV t r = -((r - 1) / (r + 1)) := by
    unfold kruskalU kruskalV
    calc (-Real.sqrt ((r - 1) / (r + 1)) * Real.exp (-t)) *
          (Real.sqrt ((r - 1) / (r + 1)) * Real.exp t)
        = -(Real.sqrt ((r - 1) / (r + 1)) ^ 2) * (Real.exp (-t) * Real.exp t) := by ring
      _ = -((r - 1) / (r + 1)) := by rw [hsq, hexp, mul_one]
  have hden : 1 + kruskalU t r * kruskalV t r = 2 / (r + 1) := by
    rw [hUV]
    field_simp
    ring
  have hrad : (1 - kruskalU t r * kruskalV t r) / (1 + kruskalU t r * kruskalV t r) = r := by
    rw [hden, hUV]
    field_simp
    ring
  have hprod_sqrt : ((r + 1) / 2) * Real.sqrt ((r - 1) / (r + 1)) =
      Real.sqrt (r ^ 2 - 1) / 2 := by
    have h1 : r + 1 = Real.sqrt (r + 1) * Real.sqrt (r + 1) := (Real.mul_self_sqrt hrp.le).symm
    rw [Real.sqrt_div hrm]
    have hsne : Real.sqrt (r + 1) ≠ 0 := (Real.sqrt_pos.mpr hrp).ne'
    have hmul : Real.sqrt (r + 1) * Real.sqrt (r - 1) = Real.sqrt (r ^ 2 - 1) := by
      rw [← Real.sqrt_mul hrp.le]
      congr 1
      ring
    calc ((r + 1) / 2) * (Real.sqrt (r - 1) / Real.sqrt (r + 1))
        = (Real.sqrt (r + 1) * Real.sqrt (r - 1)) / 2 := by
          nth_rw 1 [h1]
          field_simp
      _ = Real.sqrt (r ^ 2 - 1) / 2 := by rw [hmul]
  funext i
  fin_cases i
  · simp [kruskalEmbedding, adsEmbedding, hrad]
  · simp [kruskalEmbedding, adsEmbedding, hrad]
  · simp [kruskalEmbedding, adsEmbedding, hrad]
  · dsimp [kruskalEmbedding, adsEmbedding]
    rw [hden, Real.cosh_eq]
    unfold kruskalU kruskalV
    calc (Real.sqrt ((r - 1) / (r + 1)) * Real.exp t -
            -Real.sqrt ((r - 1) / (r + 1)) * Real.exp (-t)) / (2 / (r + 1))
        = (((r + 1) / 2) * Real.sqrt ((r - 1) / (r + 1))) * (Real.exp t + Real.exp (-t)) := by
          field_simp; ring
      _ = Real.sqrt (r ^ 2 - 1) * ((Real.exp t + Real.exp (-t)) / 2) := by
          rw [hprod_sqrt]; ring
  · dsimp [kruskalEmbedding, adsEmbedding]
    rw [hden, Real.sinh_eq]
    unfold kruskalU kruskalV
    calc (Real.sqrt ((r - 1) / (r + 1)) * Real.exp t +
            -Real.sqrt ((r - 1) / (r + 1)) * Real.exp (-t)) / (2 / (r + 1))
        = (((r + 1) / 2) * Real.sqrt ((r - 1) / (r + 1))) * (Real.exp t - Real.exp (-t)) := by
          field_simp; ring
      _ = Real.sqrt (r ^ 2 - 1) * ((Real.exp t - Real.exp (-t)) / 2) := by
          rw [hprod_sqrt]; ring

/-- On the opposite Kruskal sector `(-U, -V)`, `kruskalEmbedding` restricts to `leftAdsEmbedding`. -/
theorem kruskalEmbedding_left_exterior (t : ℝ) {r : ℝ} (hr : 1 < r) (x y : ℝ) :
    kruskalEmbedding (-kruskalU t r) (-kruskalV t r) x y = leftAdsEmbedding t r x y := by
  rw [kruskalEmbedding_neg, kruskalEmbedding_right_exterior t hr x y, leftAdsEmbedding]

/-- Global `SL₂(ℝ)`-equivariance of `kruskalEmbedding` across both boundaries, horizons, and
interiors (`g ∈ SL₂(ℝ)`). -/
theorem kruskalEmbedding_smul_SL2R (U V : ℝ) (g : SL(2, ℝ)) (z : UpperHalfPlane) :
    kruskalEmbedding U V (g • z).re (g • z).im =
      ambientLorentz (g 0 0) (g 0 1) (g 1 0) (g 1 1) (kruskalEmbedding U V z.re z.im) := by
  have hdet : (g 0 0 : ℝ) * g 1 1 - g 0 1 * g 1 0 = 1 := by
    have h := Matrix.SpecialLinearGroup.det_coe g
    rwa [Matrix.det_fin_two] at h
  have hz : ((g • z : UpperHalfPlane) : ℂ) =
      (((g 0 0 : ℝ) : ℂ) * (z : ℂ) + (g 0 1 : ℝ)) /
        (((g 1 0 : ℝ) : ℂ) * (z : ℂ) + (g 1 1 : ℝ)) := by
    rw [UpperHalfPlane.coe_specialLinearGroup_apply]
    simp
  set D : ℝ := (g 1 0 * z.re + g 1 1) ^ 2 + (g 1 0 * z.im) ^ 2 with hDdef
  have hDne : D ≠ 0 := by
    intro h0
    have hc : g 1 0 * z.im = 0 := by
      rw [hDdef] at h0
      nlinarith [sq_nonneg (g 1 0 * z.re + g 1 1), sq_nonneg (g 1 0 * z.im)]
    have hc0 : g 1 0 = 0 := (mul_eq_zero.mp hc).resolve_right z.im_pos.ne'
    have hd0 : g 1 1 = 0 := by
      rw [hDdef, hc0] at h0
      nlinarith [sq_nonneg (g 1 1)]
    rw [hc0, hd0] at hdet
    norm_num at hdet
  have hnormSq : Complex.normSq (((g 1 0 : ℝ) : ℂ) * (z : ℂ) + (g 1 1 : ℝ)) = D := by
    rw [hDdef, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, zero_mul, sub_zero, Complex.add_im,
      Complex.mul_im, add_zero]
    ring
  have hre : (g • z).re = ((g 0 0 * z.re + g 0 1) * (g 1 0 * z.re + g 1 1) +
      g 0 0 * g 1 0 * z.im ^ 2) / D := by
    rw [← UpperHalfPlane.coe_re, hz, Complex.div_re, hnormSq]
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, zero_mul, sub_zero, Complex.add_im,
      Complex.mul_im, add_zero]
    field_simp
  have him : (g • z).im = z.im / D := by
    rw [← UpperHalfPlane.coe_im, hz, Complex.div_im, hnormSq]
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, add_zero, Complex.add_im, Complex.mul_im, UpperHalfPlane.coe_re,
      UpperHalfPlane.coe_im]
    field_simp
    linear_combination hdet
  have hY := hyperboloid_moebius hdet z.re z.im_pos
  rw [hre, him]
  funext i
  fin_cases i
  · simp only [kruskalEmbedding, ambientLorentz]
    rw [hY]
    simp [moebiusLorentz]
    ring
  · simp only [kruskalEmbedding, ambientLorentz]
    rw [hY]
    simp [moebiusLorentz]
    ring
  · simp only [kruskalEmbedding, ambientLorentz]
    rw [hY]
    simp [moebiusLorentz]
    ring
  · simp [kruskalEmbedding, ambientLorentz]
  · simp [kruskalEmbedding, ambientLorentz]

/-! ## 2. Independent Prime-Marked Cycle Gate Construction -/

/-- Prime-marked cycle transfer series at primitive cycle length `2 log p` (`p ∈ ℙ`), defined
from multiple traversals `2(k + 1) log p` and branch weight `1 - 1/p` without naming `ζ`. -/
def primeEchoSeries (p : Nat.Primes) (w : ℂ) : ℂ :=
  1 + ∑' k : ℕ, (1 - 1 / (p : ℂ)) *
    Complex.exp (-w * ((2 * ((k + 1 : ℕ) : ℝ) * Real.log (p : ℕ) : ℝ) : ℂ))

/-- Closed prime-marked transfer gate `(1 - p^{-(2w+1)}) / (1 - p^{-2w})`. -/
def primeEchoGate (p : Nat.Primes) (w : ℂ) : ℂ :=
  (1 - (p : ℂ) ^ (-(2 * w + 1))) / (1 - (p : ℂ) ^ (-(2 * w)))

/-- On `Re w > 0`, the prime-cycle geometric echo series sums to `primeEchoGate p w`. -/
theorem primeEchoSeries_eq_primeEchoGate {w : ℂ} (hw : 0 < w.re) (p : Nat.Primes) :
    primeEchoSeries p w = primeEchoGate p w := by
  have hp2 : (2 : ℝ) ≤ (p : ℕ) := by exact_mod_cast p.prop.two_le
  have hppos : (0 : ℝ) < (p : ℕ) := by linarith
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hppos.ne'
  set z : ℂ := (p : ℂ) ^ (-(2 * w)) with hzdef
  have hznorm : ‖z‖ < 1 := by
    rw [hzdef, show (p : ℂ) = (((p : ℕ) : ℝ) : ℂ) by norm_cast,
      Complex.norm_cpow_eq_rpow_re_of_pos hppos]
    have hre : (-(2 * w)).re = -2 * w.re := by simp
    rw [hre]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by linarith) (by linarith)
  have h1z : 1 - z ≠ 0 := sub_ne_zero.mpr fun h => by
    rw [← h, norm_one] at hznorm
    exact lt_irrefl _ hznorm
  have hexp_pow : ∀ k : ℕ,
      Complex.exp (-w * ((2 * ((k + 1 : ℕ) : ℝ) * Real.log (p : ℕ) : ℝ) : ℂ)) =
        z * z ^ k := by
    intro k
    have hz_exp : z = Complex.exp (-(2 * w) * ((Real.log (p : ℕ) : ℝ) : ℂ)) := by
      rw [hzdef, Complex.cpow_def_of_ne_zero hpC, ← Complex.natCast_log, mul_comm]
    rw [hz_exp, ← pow_succ', ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hzp : (p : ℂ) ^ (-(2 * w + 1)) = z / (p : ℂ) := by
    rw [hzdef, show -(2 * w + 1) = -(2 * w) - 1 by ring, Complex.cpow_sub _ _ hpC, Complex.cpow_one]
  unfold primeEchoSeries primeEchoGate
  simp_rw [hexp_pow, ← mul_assoc]
  rw [tsum_mul_left, tsum_geometric_of_norm_lt_one hznorm, hzp, ← hzdef]
  field_simp
  ring

/-- On `Re w > 1/2`, the Euler product of the prime-marked cycle gates over all rational primes
converges to `ζ(2w) / ζ(2w + 1)`. -/
theorem hasProd_primeEchoGate {w : ℂ} (hw : 1 / 2 < w.re) :
    HasProd (fun p : Nat.Primes => primeEchoGate p w)
      (riemannZeta (2 * w) / riemannZeta (2 * w + 1)) := by
  have h1 : 1 < (2 * w).re := by simp; linarith
  have h2 : 1 < (2 * w + 1).re := by simp; linarith
  have hp1 := riemannZeta_eulerProduct_hasProd h1
  have hp2 := riemannZeta_eulerProduct_hasProd h2
  have hz2 : riemannZeta (2 * w + 1) ≠ 0 := riemannZeta_ne_zero_of_one_le_re h2.le
  have hinv : HasProd (fun p : Nat.Primes => 1 - (p : ℂ) ^ (-(2 * w + 1)))
      (riemannZeta (2 * w + 1))⁻¹ := by
    have htend : Tendsto (fun s : Finset Nat.Primes =>
        (∏ p ∈ s, (1 - (p : ℂ) ^ (-(2 * w + 1)))⁻¹)⁻¹) atTop
        (𝓝 (riemannZeta (2 * w + 1))⁻¹) :=
      Filter.Tendsto.inv₀ hp2 hz2
    refine htend.congr fun s => ?_
    rw [← Finset.prod_inv_distrib]
    exact Finset.prod_congr rfl fun p _ => inv_inv _
  have hmul := hinv.mul hp1
  rw [div_eq_mul_inv, mul_comm]
  exact hmul.congr_fun fun p => (div_eq_mul_inv _ _).symm

/-- On `Re w > 1/2`, the Laplace transform of the modular cusp echo train equals the `AdS`
worldline Beta bounce `B(w, 1/2)` times the infinite product of `primeEchoGate p w`. -/
theorem echoKernel_laplace_eq_beta_mul_tprod_primeEchoGate {w : ℂ} (hw : 1 / 2 < w.re) :
    (∫ τ : ℝ, Complex.exp (-w * (τ : ℂ)) * ((echoKernel τ : ℝ) : ℂ)) =
      Complex.betaIntegral w (1 / 2) * (∏' p : Nat.Primes, primeEchoGate p w) := by
  rw [integral_cexp_mul_echoKernel hw, (hasProd_primeEchoGate hw).tprod_eq]

/-! ## 3. Unconditional Global Hadamard–Schur Passivity on `Re w ≥ 0` -/

/-- Centered spectral map `z(s) = (s - 1/2) * (-i)` satisfying `XiC (z s) = xi s`. -/
private def xiCenterCoord (s : ℂ) : ℂ := (s - 1 / 2) * (-I)

private theorem XiC_xiCenterCoord (s : ℂ) : XiC (xiCenterCoord s) = xi s := by
  rw [XiC, xiCenterCoord]
  congr 1
  linear_combination (-(s - 1 / 2)) * I_sq

/-- **Global Hadamard–Schur Inequality.** Across the entire closed causal half-plane `Re w ≥ 0`,
`‖xi(2w)‖ ≤ ‖xi(1 + 2w)‖`. -/
theorem norm_xi_two_mul_le_of_re_nonneg {w : ℂ} (hw : 0 ≤ w.re) :
    ‖xi (2 * w)‖ ≤ ‖xi (1 + 2 * w)‖ := by
  set s₁ : ℂ := 1 - 2 * starRingEnd ℂ w with hs₁
  set s₂ : ℂ := 1 + 2 * w with hs₂
  have hsym : ‖xi (2 * w)‖ = ‖xi s₁‖ := by
    have hconj : s₁ = starRingEnd ℂ (1 - 2 * w) := by
      simp [hs₁, map_ofNat]
    rw [← xi_one_sub (2 * w), hconj, xi_conj, Complex.norm_conj]
  rw [hsym, ← XiC_xiCenterCoord s₁, ← XiC_xiCenterCoord s₂]
  have hfac1 := congrFun XiC_eq_constant_mul_canonicalProduct (xiCenterCoord s₁)
  have hfac2 := congrFun XiC_eq_constant_mul_canonicalProduct (xiCenterCoord s₂)
  simp only [Pi.mul_apply] at hfac1 hfac2
  rw [hfac1, hfac2, norm_mul, norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have ht1 : Tendsto (fun F : Finset XiDivisorSupport =>
      ‖xiPairedE1Product F (xiCenterCoord s₁)‖) atTop
      (𝓝 ‖xiCanonicalProduct (xiCenterCoord s₁)‖) :=
    (xiPairedE1Product_tendstoLocallyUniformlyOn.tendsto_at (mem_univ _)).norm
  have ht2 : Tendsto (fun F : Finset XiDivisorSupport =>
      ‖xiPairedE1Product F (xiCenterCoord s₂)‖) atTop
      (𝓝 ‖xiCanonicalProduct (xiCenterCoord s₂)‖) :=
    (xiPairedE1Product_tendstoLocallyUniformlyOn.tendsto_at (mem_univ _)).norm
  refine le_of_tendsto_of_tendsto ht1 ht2 (Eventually.of_forall fun F => ?_)
  dsimp only
  rw [xiPairedE1Product_eq_linear_product, xiPairedE1Product_eq_linear_product,
    norm_prod, norm_prod]
  refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun q _ => ?_
  have hζne : xiSpectralPoint q ≠ 0 := xiSpectralPoint_ne_zero q
  have hlin : ∀ s : ℂ, 1 - xiCenterCoord s / xiSpectralPoint q =
      (((q.1 : ℂ) - s) * (-I)) / xiSpectralPoint q := by
    intro s
    have hdef : xiSpectralPoint q = ((q.1 : ℂ) - 1 / 2) * (-I) := rfl
    rw [eq_div_iff hζne, sub_mul, one_mul, div_mul_cancel₀ _ hζne, hdef, xiCenterCoord]
    ring
  rw [hlin s₁, hlin s₂, norm_div, norm_div, norm_mul, norm_mul, norm_neg, norm_I, mul_one, mul_one]
  refine div_le_div_of_nonneg_right ?_ (norm_nonneg _)
  have hβ1 : (q.1 : ℂ).re < 1 := by
    have him := (abs_lt.mp (abs_im_xiSpectralPoint_lt_half q)).1
    have hqim : (xiSpectralPoint q).im = 1 / 2 - (q.1 : ℂ).re := by simp [xiSpectralPoint]
    linarith
  have hsq : Complex.normSq ((q.1 : ℂ) - s₁) ≤ Complex.normSq ((q.1 : ℂ) - s₂) := by
    have hre1 : ((q.1 : ℂ) - s₁).re = ((q.1 : ℂ).re - 1) + 2 * w.re := by
      simp [hs₁]; ring
    have hre2 : ((q.1 : ℂ) - s₂).re = ((q.1 : ℂ).re - 1) - 2 * w.re := by
      simp [hs₂]; ring
    have him12 : ((q.1 : ℂ) - s₁).im = ((q.1 : ℂ) - s₂).im := by
      simp [hs₁, hs₂]
    rw [Complex.normSq_apply, Complex.normSq_apply, hre1, hre2, him12]
    nlinarith
  have hpow : ‖(q.1 : ℂ) - s₁‖ ^ 2 ≤ ‖(q.1 : ℂ) - s₂‖ ^ 2 := by
    rwa [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp hpow

/-- Pole-cleared Lax–Phillips modular scattering symbol `S_red(w) = xi(2w) / xi(1 + 2w)`. -/
def modularReducedScattering (w : ℂ) : ℂ :=
  xi (2 * w) / xi (1 + 2 * w)

/-- Global Lax–Phillips Schur contractivity `‖S_red(w)‖ ≤ 1` across `Re w ≥ 0`. -/
theorem norm_modularReducedScattering_le_one {w : ℂ} (hw : 0 ≤ w.re) :
    ‖modularReducedScattering w‖ ≤ 1 := by
  unfold modularReducedScattering
  have hne : xi (1 + 2 * w) ≠ 0 := xi_ne_zero_of_one_le_re (by simp; linarith)
  rw [norm_div, div_le_one (norm_pos_iff.mpr hne)]
  exact norm_xi_two_mul_le_of_re_nonneg hw

/-- `modularReducedScattering` is holomorphic across `{w | 0 ≤ Re w}`. -/
theorem differentiableAt_modularReducedScattering {w : ℂ} (hw : 0 ≤ w.re) :
    DifferentiableAt ℂ modularReducedScattering w := by
  have hne : xi (1 + 2 * w) ≠ 0 := xi_ne_zero_of_one_le_re (by simp; linarith)
  exact ((xi_differentiable _).comp w (by fun_prop)).div
    ((xi_differentiable _).comp w (by fun_prop)) hne

/-- Positive-real-part Herglotz boundary admittance `Re((1 - S)/(1 + S)) ≥ 0` on `Re w ≥ 0`
whenever `S_red(w) ≠ -1`. -/
theorem re_herglotzAdmittance_modularReducedScattering_nonneg {w : ℂ} (hw : 0 ≤ w.re) :
    0 ≤ ((1 - modularReducedScattering w) / (1 + modularReducedScattering w)).re := by
  set S := modularReducedScattering w
  have hS : Complex.normSq S ≤ 1 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_modularReducedScattering_le_one hw, norm_nonneg S]
  by_cases hden : 1 + S = 0
  · rw [hden, div_zero, zero_re]
  · rw [Complex.div_re]
    have hnum : (1 - S).re * (1 + S).re + (1 - S).im * (1 + S).im = 1 - Complex.normSq S := by
      rw [Complex.normSq_apply]
      simp
      ring
    rw [← add_div, hnum]
    exact div_nonneg (by linarith) (Complex.normSq_nonneg _)

/-- Full modular Eisenstein scattering reflection phase
`φ_ℚ(w) = ((1 + 2w) / (2w - 1)) · (xi(2w) / xi(1 + 2w)) = Λ(2w) / Λ(1 + 2w)`. -/
def modularScatteringPhase (w : ℂ) : ℂ :=
  ((1 + 2 * w) / (2 * w - 1)) * (xi (2 * w) / xi (1 + 2 * w))

/-- Away from `{0, 1/2, -1/2}`, `modularScatteringPhase w = completedRiemannZeta (2w) /
completedRiemannZeta (1 + 2w)`. -/
theorem completedRiemannZeta_div_eq_modularScatteringPhase {w : ℂ}
    (hw0 : w ≠ 0) (hwhalf : 2 * w - 1 ≠ 0) (hwneg : 1 + 2 * w ≠ 0)
    (hwone : 2 * w ≠ 1) (hwm1 : 1 + 2 * w ≠ 1) :
    completedRiemannZeta (2 * w) / completedRiemannZeta (1 + 2 * w) =
      modularScatteringPhase w := by
  have h2w0 : 2 * w ≠ 0 := mul_ne_zero two_ne_zero hw0
  have hxi1 : xi (2 * w) = w * (2 * w - 1) * completedRiemannZeta (2 * w) := by
    rw [xi_eq_half_mul h2w0 hwone]; ring
  have hxi2 : xi (1 + 2 * w) = w * (1 + 2 * w) * completedRiemannZeta (1 + 2 * w) := by
    rw [xi_eq_half_mul hwneg hwm1]; ring
  unfold modularScatteringPhase
  rw [hxi1, hxi2]
  field_simp

/-- Continuous-spectrum unitarity `‖φ_ℚ(it)‖ = 1` for all `t ∈ ℝ`. -/
theorem norm_modularScatteringPhase_axis (t : ℝ) :
    ‖modularScatteringPhase ((t : ℂ) * I)‖ = 1 := by
  set z : ℂ := 1 + 2 * ((t : ℂ) * I) with hz
  have hzre : z.re = 1 := by rw [hz]; simp
  have hzne : z ≠ 0 := fun h => by rw [h] at hzre; simp at hzre
  have hxine : xi z ≠ 0 := xi_ne_zero_of_one_le_re (by linarith)
  have hconjz : starRingEnd ℂ z = 1 - 2 * ((t : ℂ) * I) := by
    rw [hz]; simp [map_ofNat]; ring
  have hden : 2 * ((t : ℂ) * I) - 1 = -starRingEnd ℂ z := by rw [hconjz]; ring
  have hxi_num : xi (2 * ((t : ℂ) * I)) = starRingEnd ℂ (xi z) := by
    have h1 : (2 : ℂ) * ((t : ℂ) * I) = 1 - starRingEnd ℂ z := by rw [hconjz]; ring
    rw [h1, xi_one_sub, xi_conj]
  unfold modularScatteringPhase
  rw [show 1 + 2 * ((t : ℂ) * I) = z from rfl, hden, hxi_num, norm_mul, norm_div, norm_div,
    norm_neg, Complex.norm_conj, Complex.norm_conj,
    div_self (norm_ne_zero_iff.mpr hzne), div_self (norm_ne_zero_iff.mpr hxine), mul_one]

theorem differentiableAt_modularScatteringPhase {w : ℂ}
    (hne : w ≠ 1 / 2) (hxi : xi (1 + 2 * w) ≠ 0) :
    DifferentiableAt ℂ modularScatteringPhase w := by
  have hd : 2 * w - 1 ≠ 0 := fun h0 => hne (by linear_combination h0 / 2)
  exact ((by fun_prop : DifferentiableAt ℂ (fun v : ℂ => 1 + 2 * v) w).div (by fun_prop) hd).mul
    (((xi_differentiable _).comp w (by fun_prop)).div
      ((xi_differentiable _).comp w (by fun_prop)) hxi)

theorem xi_two_mul_ne_zero_of_re_nonpos {w : ℂ} (hw : w.re ≤ 0) : xi (2 * w) ≠ 0 := by
  rw [← xi_one_sub]
  exact xi_ne_zero_of_one_le_re (by simp; linarith)

theorem zero_mem_openStrip_of_xi_eq_zero {s : ℂ} (hz : xi s = 0) :
    0 < s.re ∧ s.re < 1 := by
  have hlt1 : s.re < 1 := lt_of_not_ge fun h => xi_ne_zero_of_one_le_re h hz
  have hgt0 : 0 < s.re := by
    by_contra hle
    push Not at hle
    exact xi_ne_zero_of_one_le_re (by simp; linarith : 1 ≤ (1 - s).re)
      (by rw [xi_one_sub]; exact hz)
  exact ⟨hgt0, hlt1⟩

/-! ## 4. Eternal-AdS Two-Boundary Schwinger–Keldysh Singularity Dictionary -/

/-- Single-boundary retarded modular-horizon correlator `G_R(ω) = φ_ℚ(-iω)`. -/
def modularRetardedCorrelator (ω : ℂ) : ℂ :=
  modularScatteringPhase (-I * ω)

/-- Single-boundary advanced modular-horizon correlator `G_A(ω) = φ_ℚ(iω)`. -/
def modularAdvancedCorrelator (ω : ℂ) : ℂ :=
  modularScatteringPhase (I * ω)

/-- Eternal-AdS two-boundary thermofield Wightman correlator at Hawking inverse temperature
`β_H = 2π`: `G_{RL}(ω) = (G_R(ω) - G_A(ω)) / (2 i sinh(π ω))`. -/
def modularWightmanRL (ω : ℂ) : ℂ :=
  (modularRetardedCorrelator ω - modularAdvancedCorrelator ω) /
    (2 * I * Complex.sinh (Real.pi * ω))

/-- All Hawking–Matsubara poles `ω = i k` (`k ∈ ℤ`) lie outside the punctured strip
`0 < |Im ω| < 1`. -/
theorem sinh_pi_mul_ne_zero_of_abs_im_lt_one {ω : ℂ}
    (h0 : 0 < |ω.im|) (h1 : |ω.im| < 1) :
    Complex.sinh (Real.pi * ω) ≠ 0 := by
  intro hsinh
  have hexp_eq : Complex.exp (Real.pi * ω) = Complex.exp (-(Real.pi * ω)) := by
    rw [Complex.sinh] at hsinh
    have hsub : Complex.exp (Real.pi * ω) - Complex.exp (-(Real.pi * ω)) = 0 :=
      (div_eq_zero_iff.mp hsinh).resolve_right two_ne_zero
    exact sub_eq_zero.mp hsub
  have hexp1 : Complex.exp (2 * (Real.pi : ℂ) * ω) = 1 := by
    calc Complex.exp (2 * (Real.pi : ℂ) * ω)
        = Complex.exp ((Real.pi : ℂ) * ω + (Real.pi : ℂ) * ω) := by congr 1; ring
      _ = Complex.exp ((Real.pi : ℂ) * ω) * Complex.exp ((Real.pi : ℂ) * ω) :=
          Complex.exp_add _ _
      _ = Complex.exp (-((Real.pi : ℂ) * ω)) * Complex.exp ((Real.pi : ℂ) * ω) := by
          rw [hexp_eq]
      _ = Complex.exp (-((Real.pi : ℂ) * ω) + (Real.pi : ℂ) * ω) := (Complex.exp_add _ _).symm
      _ = 1 := by simp
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hexp1
  have hpi : (2 * (Real.pi : ℂ)) ≠ 0 :=
    mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hω : ω = (n : ℂ) * I := by
    apply mul_left_cancel₀ hpi
    linear_combination hn
  have him : ω.im = (n : ℝ) := by rw [hω]; simp
  rw [him] at h0 h1
  have hn0 : n ≠ 0 := fun h => by simp [h] at h0
  have hn1 : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hn0
  linarith

/-- Generic meromorphic pole-order formula for a completed scattering phase
`((1 + 2w)/(2w - 1)) * (Ξ(2w)/Ξ(1 + 2w))` at any zero `ρ` of an entire function `Ξ` whose zeros
lie in `0 < Re s < 1` and which does not vanish on `Re s ≥ 1`. -/
theorem scatteringPhase_meromorphicOrderAt_at_zero {Ξ : ℂ → ℂ}
    (hΞ_diff : Differentiable ℂ Ξ)
    (hΞ_ge_one : ∀ s : ℂ, 1 ≤ s.re → Ξ s ≠ 0)
    (hΞ_one_sub : ∀ s : ℂ, Ξ (1 - s) = Ξ s)
    {ρ : ℂ} (hρ : Ξ ρ = 0) :
    meromorphicOrderAt
        (fun w : ℂ => ((1 + 2 * w) / (2 * w - 1)) * (Ξ (2 * w) / Ξ (1 + 2 * w)))
        ((ρ - 1) / 2) =
      -meromorphicOrderAt Ξ ρ := by
  have hlt1 : ρ.re < 1 := lt_of_not_ge fun h => hΞ_ge_one ρ h hρ
  have hgt0 : 0 < ρ.re := by
    by_contra hle
    push Not at hle
    exact hΞ_ge_one (1 - ρ) (by simp; linarith) (by rw [hΞ_one_sub]; exact hρ)
  set w₀ : ℂ := (ρ - 1) / 2 with hw₀
  have hw₀1 : 1 + 2 * w₀ = ρ := by rw [hw₀]; ring
  have hw₀re : w₀.re = (ρ.re - 1) / 2 := by rw [hw₀]; simp
  have h2w₀_ne1 : 2 * w₀ - 1 ≠ 0 := by
    intro h0
    have := congrArg Complex.re h0
    simp [hw₀re] at this
    linarith
  have h12w₀_ne0 : 1 + 2 * w₀ ≠ 0 := by
    rw [hw₀1]
    exact fun h0 => by rw [h0] at hgt0; simp at hgt0
  have hΞ2w₀ : Ξ (2 * w₀) ≠ 0 := by
    rw [← hΞ_one_sub (2 * w₀)]
    exact hΞ_ge_one (1 - 2 * w₀) (by simp [hw₀re]; linarith)
  set num : ℂ → ℂ := fun w => ((1 + 2 * w) / (2 * w - 1)) * Ξ (2 * w)
  have hnum_an : AnalyticAt ℂ num w₀ := by
    have hrat : AnalyticAt ℂ (fun w : ℂ => (1 + 2 * w) / (2 * w - 1)) w₀ :=
      (by fun_prop : AnalyticAt ℂ (fun w : ℂ => 1 + 2 * w) w₀).div (by fun_prop) h2w₀_ne1
    exact hrat.mul ((hΞ_diff.analyticAt _).comp (by fun_prop))
  have hnum_ne : num w₀ ≠ 0 := mul_ne_zero (div_ne_zero h12w₀_ne0 h2w₀_ne1) hΞ2w₀
  have hfun : (fun w : ℂ => ((1 + 2 * w) / (2 * w - 1)) * (Ξ (2 * w) / Ξ (1 + 2 * w))) =
      num * (fun w => Ξ (1 + 2 * w))⁻¹ := by
    funext w
    simp [num, div_eq_mul_inv, mul_assoc]
  have hcomp_ord : meromorphicOrderAt (fun w : ℂ => Ξ (1 + 2 * w)) w₀ =
      meromorphicOrderAt Ξ ρ := by
    rw [← hw₀1]
    have hd : HasDerivAt (fun w : ℂ => 1 + 2 * w) 2 w₀ := by
      simpa using ((hasDerivAt_id w₀).const_mul (2 : ℂ)).const_add (1 : ℂ)
    exact meromorphicOrderAt_comp_of_deriv_ne_zero (by fun_prop)
      (by rw [hd.deriv]; norm_num)
  rw [hfun, meromorphicOrderAt_mul_of_ne_zero hnum_an hnum_ne, meromorphicOrderAt_inv, hcomp_ord]

/-- Any zero of `Ξ` has strictly positive finite meromorphic order (hence `-ord_ρ Ξ < 0`) when `Ξ`
is entire and nonvanishing on `Re s ≥ 1`. -/
theorem meromorphicOrderAt_pos_of_entire_zero {Ξ : ℂ → ℂ}
    (hΞ_diff : Differentiable ℂ Ξ)
    (hΞ_ge_one : ∀ s : ℂ, 1 ≤ s.re → Ξ s ≠ 0)
    {ρ : ℂ} (hρ : Ξ ρ = 0) :
    0 < meromorphicOrderAt Ξ ρ ∧ -meromorphicOrderAt Ξ ρ < 0 ∧ meromorphicOrderAt Ξ ρ ≠ ⊤ := by
  have han : AnalyticAt ℂ Ξ ρ := hΞ_diff.analyticAt ρ
  have hntop : analyticOrderAt Ξ ρ ≠ ⊤ := by
    intro htop
    have hev : Ξ =ᶠ[𝓝 ρ] 0 := analyticOrderAt_eq_top.mp htop
    have hall : AnalyticOnNhd ℂ Ξ univ := fun z _ => hΞ_diff.analyticAt z
    have hz2 := hall.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
      (mem_univ ρ) hev (mem_univ (2 : ℂ))
    exact hΞ_ge_one 2 (by norm_num) hz2
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hntop
  have hmpos : 0 < m := by
    rcases Nat.eq_zero_or_pos m with rfl | hp
    · exfalso
      exact ((analyticOrderAt_eq_zero.mp hm.symm).resolve_left (not_not.mpr han)) hρ
    · exact hp
  rw [han.meromorphicOrderAt_eq, ← hm, ENat.map_coe]
  refine ⟨by exact_mod_cast hmpos, ?_, WithTop.coe_ne_top⟩
  exact WithTop.coe_lt_coe.mpr (by dsimp; linarith)

/-- **Exact retarded boundary dictionary.** Every nontrivial zero `ρ` of `ξ` produces a pole of
`modularRetardedCorrelator` at `ω_ρ = i(ρ - 1)/2` of exact multiplicity `-ord_ρ ξ < 0`. -/
theorem modularRetardedCorrelator_order_at_zero {ρ : ℂ} (hρ : xi ρ = 0) :
    meromorphicOrderAt modularRetardedCorrelator (I * (ρ - 1) / 2) =
      -meromorphicOrderAt xi ρ := by
  have hcoord : -I * (I * (ρ - 1) / 2) = (ρ - 1) / 2 := by
    linear_combination (-(ρ - 1) / 2) * I_sq
  have hd : HasDerivAt (fun ω : ℂ => -I * ω) (-I) (I * (ρ - 1) / 2) :=
    hasDerivAt_const_mul (-I)
  have hcomp : meromorphicOrderAt modularRetardedCorrelator (I * (ρ - 1) / 2) =
      meromorphicOrderAt modularScatteringPhase ((ρ - 1) / 2) := by
    rw [← hcoord]
    exact meromorphicOrderAt_comp_of_deriv_ne_zero (by fun_prop)
      (by rw [hd.deriv]; exact neg_ne_zero.mpr I_ne_zero)
  rw [hcomp]
  exact scatteringPhase_meromorphicOrderAt_at_zero xi_differentiable
    (fun _ => xi_ne_zero_of_one_le_re) xi_one_sub hρ

/-- Off the trivial pole `ω = i/2`, `modularRetardedCorrelator` has a pole at `ω` if and only if
`xi(1 - 2iω) = 0`. -/
theorem modularRetardedCorrelator_isPole_iff {ω : ℂ} (hne : ω ≠ I / 2) :
    meromorphicOrderAt modularRetardedCorrelator ω < 0 ↔ xi (1 - 2 * I * ω) = 0 := by
  constructor
  · intro hp
    by_contra hnz
    have hw_ne : -I * ω ≠ 1 / 2 := fun h => hne (by linear_combination I * h + ω * I_sq)
    have hdiff : DifferentiableAt ℂ modularRetardedCorrelator ω :=
      (differentiableAt_modularScatteringPhase hw_ne
        (by simpa [sub_eq_add_neg, mul_assoc, mul_left_comm] using hnz)).comp ω (by fun_prop)
    have hopen : IsOpen {z : ℂ | z ≠ I / 2 ∧ xi (1 - 2 * I * z) ≠ 0} :=
      isOpen_ne.inter (isOpen_ne.preimage (xi_differentiable.continuous.comp (by fun_prop)))
    have han : AnalyticAt ℂ modularRetardedCorrelator ω :=
      (DifferentiableOn.analyticOnNhd (fun z hz => by
        have hzne : -I * z ≠ 1 / 2 := fun h => hz.1 (by linear_combination I * h + z * I_sq)
        exact ((differentiableAt_modularScatteringPhase hzne
          (by simpa [sub_eq_add_neg, mul_assoc, mul_left_comm] using hz.2)).comp z
            (by fun_prop)).differentiableWithinAt) hopen) ω ⟨hne, hnz⟩
    exact (not_lt_of_ge han.meromorphicOrderAt_nonneg) hp
  · intro hz
    have hω_eq : ω = I * ((1 - 2 * I * ω) - 1) / 2 := by
      linear_combination ω * I_sq
    rw [hω_eq, modularRetardedCorrelator_order_at_zero hz]
    exact (meromorphicOrderAt_pos_of_entire_zero xi_differentiable
      (fun _ => xi_ne_zero_of_one_le_re) hz).2.1

/-- Analyticity of `modularRetardedCorrelator` at `ω ≠ i/2` when `xi(1 - 2iω) ≠ 0`. -/
theorem analyticAt_modularRetardedCorrelator {ω : ℂ} (hne : ω ≠ I / 2)
    (hnz : xi (1 - 2 * I * ω) ≠ 0) :
    AnalyticAt ℂ modularRetardedCorrelator ω := by
  have hopen : IsOpen {z : ℂ | z ≠ I / 2 ∧ xi (1 - 2 * I * z) ≠ 0} :=
    isOpen_ne.inter (isOpen_ne.preimage (xi_differentiable.continuous.comp (by fun_prop)))
  refine (DifferentiableOn.analyticOnNhd (fun z hz => ?_) hopen) ω ⟨hne, hnz⟩
  have hzne : -I * z ≠ 1 / 2 := fun h => hz.1 (by linear_combination I * h + z * I_sq)
  exact ((differentiableAt_modularScatteringPhase hzne
    (by simpa [sub_eq_add_neg, mul_assoc, mul_left_comm] using hz.2)).comp z
      (by fun_prop)).differentiableWithinAt

/-- Analyticity of `modularAdvancedCorrelator` at `ω ≠ -i/2` when `xi(1 + 2iω) ≠ 0`. -/
theorem analyticAt_modularAdvancedCorrelator {ω : ℂ} (hne : ω ≠ -(I / 2))
    (hnz : xi (1 + 2 * I * ω) ≠ 0) :
    AnalyticAt ℂ modularAdvancedCorrelator ω := by
  have hopen : IsOpen {z : ℂ | z ≠ -(I / 2) ∧ xi (1 + 2 * I * z) ≠ 0} :=
    isOpen_ne.inter (isOpen_ne.preimage (xi_differentiable.continuous.comp (by fun_prop)))
  refine (DifferentiableOn.analyticOnNhd (fun z hz => ?_) hopen) ω ⟨hne, hnz⟩
  have hzne : I * z ≠ 1 / 2 := fun h => hz.1 (by linear_combination (-I) * h + z * I_sq)
  exact ((differentiableAt_modularScatteringPhase hzne
    (by simpa [mul_assoc] using hz.2)).comp z (by fun_prop)).differentiableWithinAt

/-- **Two-boundary eternal-AdS pole order in the lower strip `-1/2 < Im ω < 0`.**
Every zero of `xi(1 - 2iω)` produces a pole of `modularWightmanRL` of exact multiplicity
`-ord_{1 - 2iω} xi < 0`, with zero Matsubara or advanced-correlator cancellation. -/
theorem modularWightmanRL_order_lower {ω : ℂ}
    (hlo : -(1 / 2 : ℝ) < ω.im) (hhi : ω.im < 0) (hz : xi (1 - 2 * I * ω) = 0) :
    meromorphicOrderAt modularWightmanRL ω = -meromorphicOrderAt xi (1 - 2 * I * ω) := by
  have habs0 : 0 < |ω.im| := abs_pos.mpr hhi.ne
  have habs1 : |ω.im| < 1 := by rw [abs_of_neg hhi]; linarith
  have hsinh_ne : 2 * I * Complex.sinh (Real.pi * ω) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero I_ne_zero)
      (sinh_pi_mul_ne_zero_of_abs_im_lt_one habs0 habs1)
  have hadv_ne : ω ≠ -(I / 2) := fun h => by
    have := congrArg Complex.im h; simp at this; linarith
  have hadv_xi : xi (1 + 2 * I * ω) ≠ 0 :=
    xi_ne_zero_of_one_le_re (by simp; linarith)
  have hadv_an : AnalyticAt ℂ (fun z => -modularAdvancedCorrelator z) ω :=
    (analyticAt_modularAdvancedCorrelator hadv_ne hadv_xi).neg
  have hω_eq : ω = I * ((1 - 2 * I * ω) - 1) / 2 := by linear_combination ω * I_sq
  have hret_ord : meromorphicOrderAt modularRetardedCorrelator ω =
      -meromorphicOrderAt xi (1 - 2 * I * ω) := by
    nth_rw 1 [hω_eq]
    exact modularRetardedCorrelator_order_at_zero hz
  have hret_neg : meromorphicOrderAt modularRetardedCorrelator ω < 0 := by
    rw [hret_ord]
    exact (meromorphicOrderAt_pos_of_entire_zero xi_differentiable
      (fun _ => xi_ne_zero_of_one_le_re) hz).2.1
  have hlt : meromorphicOrderAt modularRetardedCorrelator ω <
      meromorphicOrderAt (fun z => -modularAdvancedCorrelator z) ω :=
    lt_of_lt_of_le hret_neg hadv_an.meromorphicOrderAt_nonneg
  have hden_an : AnalyticAt ℂ (fun z => (2 * I * Complex.sinh (Real.pi * z))⁻¹) ω :=
    AnalyticAt.inv (by fun_prop) hsinh_ne
  have hW : modularWightmanRL =
      (fun z => (2 * I * Complex.sinh (Real.pi * z))⁻¹) *
        (modularRetardedCorrelator + (fun z => -modularAdvancedCorrelator z)) := by
    funext z
    simp only [modularWightmanRL, Pi.mul_apply, Pi.add_apply]
    ring
  rw [hW, meromorphicOrderAt_mul_of_ne_zero hden_an (inv_ne_zero hsinh_ne),
    meromorphicOrderAt_add_eq_left_of_lt hadv_an.meromorphicAt hlt, hret_ord]

/-- **Two-boundary eternal-AdS pole order in the upper strip `0 < Im ω < 1/2`.** -/
theorem modularWightmanRL_order_upper {ω : ℂ}
    (hlo : 0 < ω.im) (hhi : ω.im < 1 / 2) (hz : xi (1 + 2 * I * ω) = 0) :
    meromorphicOrderAt modularWightmanRL ω = -meromorphicOrderAt xi (1 + 2 * I * ω) := by
  have habs0 : 0 < |ω.im| := abs_pos.mpr hlo.ne'
  have habs1 : |ω.im| < 1 := by rw [abs_of_pos hlo]; linarith
  have hsinh_ne : 2 * I * Complex.sinh (Real.pi * ω) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero I_ne_zero)
      (sinh_pi_mul_ne_zero_of_abs_im_lt_one habs0 habs1)
  have hret_ne : ω ≠ I / 2 := fun h => by
    have := congrArg Complex.im h; simp at this; linarith
  have hret_xi : xi (1 - 2 * I * ω) ≠ 0 :=
    xi_ne_zero_of_one_le_re (by simp; linarith)
  have hret_an : AnalyticAt ℂ modularRetardedCorrelator ω :=
    analyticAt_modularRetardedCorrelator hret_ne hret_xi
  have hneg_ord : meromorphicOrderAt (fun z => -modularAdvancedCorrelator z) ω =
      -meromorphicOrderAt xi (1 + 2 * I * ω) := by
    rw [show (fun z => -modularAdvancedCorrelator z) = -modularAdvancedCorrelator from rfl,
      ← meromorphicOrderAt_neg]
    have hadv_eq : modularAdvancedCorrelator = fun z => modularRetardedCorrelator (-z) := by
      funext z; simp [modularAdvancedCorrelator, modularRetardedCorrelator]
    rw [hadv_eq]
    have hd : HasDerivAt (fun z : ℂ => -z) (-1) ω := (hasDerivAt_id ω).neg
    have hcomp : meromorphicOrderAt (fun z => modularRetardedCorrelator (-z)) ω =
        meromorphicOrderAt modularRetardedCorrelator (-ω) :=
      meromorphicOrderAt_comp_of_deriv_ne_zero (f := modularRetardedCorrelator)
        (g := fun z : ℂ => -z) (by fun_prop) (by rw [hd.deriv]; norm_num)
    rw [hcomp]
    have hω_eq : -ω = I * ((1 + 2 * I * ω) - 1) / 2 := by linear_combination (-ω) * I_sq
    nth_rw 1 [hω_eq]
    exact modularRetardedCorrelator_order_at_zero hz
  have hadv_neg : meromorphicOrderAt (fun z => -modularAdvancedCorrelator z) ω < 0 := by
    rw [hneg_ord]
    exact (meromorphicOrderAt_pos_of_entire_zero xi_differentiable
      (fun _ => xi_ne_zero_of_one_le_re) hz).2.1
  have hlt : meromorphicOrderAt (fun z => -modularAdvancedCorrelator z) ω <
      meromorphicOrderAt modularRetardedCorrelator ω :=
    lt_of_lt_of_le hadv_neg hret_an.meromorphicOrderAt_nonneg
  have hden_an : AnalyticAt ℂ (fun z => (2 * I * Complex.sinh (Real.pi * z))⁻¹) ω :=
    AnalyticAt.inv (by fun_prop) hsinh_ne
  have hW : modularWightmanRL =
      (fun z => (2 * I * Complex.sinh (Real.pi * z))⁻¹) *
        (modularRetardedCorrelator + (fun z => -modularAdvancedCorrelator z)) := by
    funext z
    simp only [modularWightmanRL, Pi.mul_apply, Pi.add_apply]
    ring
  rw [hW, meromorphicOrderAt_mul_of_ne_zero hden_an (inv_ne_zero hsinh_ne),
    meromorphicOrderAt_add_eq_right_of_lt hret_an.meromorphicAt hlt, hneg_ord]

/-- Analyticity of `modularWightmanRL` on `0 < |Im ω| < 1/2` away from zeros of `xi(1 ∓ 2iω)`. -/
theorem analyticAt_modularWightmanRL {ω : ℂ}
    (h0 : 0 < |ω.im|) (h1 : |ω.im| < 1 / 2)
    (hz1 : xi (1 - 2 * I * ω) ≠ 0) (hz2 : xi (1 + 2 * I * ω) ≠ 0) :
    AnalyticAt ℂ modularWightmanRL ω := by
  have hne1 : ω ≠ I / 2 := fun h => by
    rw [h] at h1; simp at h1
  have hne2 : ω ≠ -(I / 2) := fun h => by
    rw [h] at h1; simp at h1
  have hsinh_ne : 2 * I * Complex.sinh (Real.pi * ω) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero I_ne_zero)
      (sinh_pi_mul_ne_zero_of_abs_im_lt_one h0 (by linarith))
  exact ((analyticAt_modularRetardedCorrelator hne1 hz1).sub
    (analyticAt_modularAdvancedCorrelator hne2 hz2)).div (by fun_prop) hsinh_ne

/-- **Complete Two-Boundary Eternal-AdS Singularity Dictionary.**
On the punctured strip `0 < |Im ω| < 1/2`, `modularWightmanRL` has a pole at `ω` if and only if
`xi(1 - 2iω) = 0` or `xi(1 + 2iω) = 0`. -/
theorem modularWightmanRL_isPole_iff {ω : ℂ}
    (h0 : 0 < |ω.im|) (h1 : |ω.im| < 1 / 2) :
    meromorphicOrderAt modularWightmanRL ω < 0 ↔
      xi (1 - 2 * I * ω) = 0 ∨ xi (1 + 2 * I * ω) = 0 := by
  constructor
  · intro hp
    by_contra hnor
    push Not at hnor
    exact (not_lt_of_ge (analyticAt_modularWightmanRL h0 h1 hnor.1 hnor.2).meromorphicOrderAt_nonneg) hp
  · intro hor
    have hne0 : ω.im ≠ 0 := abs_pos.mp h0
    rcases lt_or_gt_of_ne hne0 with hneg | hpos
    · have hlo : -(1 / 2 : ℝ) < ω.im := by rw [abs_of_neg hneg] at h1; linarith
      have hz1 : xi (1 - 2 * I * ω) = 0 :=
        hor.resolve_right (xi_ne_zero_of_one_le_re (by simp; linarith))
      rw [modularWightmanRL_order_lower hlo hneg hz1]
      exact (meromorphicOrderAt_pos_of_entire_zero xi_differentiable
        (fun _ => xi_ne_zero_of_one_le_re) hz1).2.1
    · have hhi : ω.im < 1 / 2 := by rwa [abs_of_pos hpos] at h1
      have hz2 : xi (1 + 2 * I * ω) = 0 :=
        hor.resolve_left (xi_ne_zero_of_one_le_re (by simp; linarith))
      rw [modularWightmanRL_order_upper hpos hhi hz2]
      exact (meromorphicOrderAt_pos_of_entire_zero xi_differentiable
        (fun _ => xi_ne_zero_of_one_le_re) hz2).2.1

/-- **Strip Analyticity vs. Zero-Free Strip.** For `0 < δ ≤ 1/4`, `modularWightmanRL` is analytic on
the punctured strip `0 < |Im ω| < δ` if and only if every zero of `ζ` with `Re ρ > 0` satisfies
`Re ρ ≤ 1 - 2δ`. -/
theorem modularWightmanRL_analyticOnNhd_strip_iff {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 4) :
    AnalyticOnNhd ℂ modularWightmanRL {ω : ℂ | 0 < |ω.im| ∧ |ω.im| < δ} ↔
      ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re ≤ 1 - 2 * δ := by
  constructor
  · intro han ρ hζ hρ0
    by_contra hlt
    push Not at hlt
    have hρ1 : ρ.re < 1 := lt_of_not_ge fun h1 => riemannZeta_ne_zero_of_one_le_re h1 hζ
    have hne1 : ρ ≠ 1 := fun h => by rw [h, one_re] at hρ1; exact lt_irrefl _ hρ1
    have hxi : xi ρ = 0 := (xi_eq_zero_iff hρ0 hne1).mpr hζ
    set ω : ℂ := I * (ρ - 1) / 2 with hω
    have him : ω.im = (ρ.re - 1) / 2 := by rw [hω]; simp
    have hmem : ω ∈ {z : ℂ | 0 < |z.im| ∧ |z.im| < δ} := by
      refine ⟨?_, ?_⟩
      · rw [him, abs_of_neg (by linarith)]
        linarith
      · rw [him, abs_of_neg (by linarith)]
        linarith
    have h12 : 1 - 2 * I * ω = ρ := by rw [hω]; linear_combination (1 - ρ) * I_sq
    have hpole : meromorphicOrderAt modularWightmanRL ω < 0 :=
      (modularWightmanRL_isPole_iff hmem.1 (by linarith [hmem.2])).mpr (Or.inl (by rwa [h12]))
    exact (not_lt_of_ge (han ω hmem).meromorphicOrderAt_nonneg) hpole
  · intro hz ω hω
    refine analyticAt_modularWightmanRL hω.1 (by linarith [hω.2]) ?_ ?_
    · intro hxi1
      obtain ⟨h0, h1⟩ := zero_mem_openStrip_of_xi_eq_zero hxi1
      have hne1 : 1 - 2 * I * ω ≠ 1 := fun h => by rw [h, one_re] at h1; exact lt_irrefl _ h1
      have hζ1 := (xi_eq_zero_iff h0 hne1).mp hxi1
      have hre1 : (1 - 2 * I * ω).re = 1 + 2 * ω.im := by simp
      have hb := hz _ hζ1 h0
      have habs := abs_lt.mp hω.2
      linarith
    · intro hxi2
      obtain ⟨h0, h1⟩ := zero_mem_openStrip_of_xi_eq_zero hxi2
      have hne1 : 1 + 2 * I * ω ≠ 1 := fun h => by rw [h, one_re] at h1; exact lt_irrefl _ h1
      have hζ2 := (xi_eq_zero_iff h0 hne1).mp hxi2
      have hre2 : (1 + 2 * I * ω).re = 1 - 2 * ω.im := by simp; ring
      have hb := hz _ hζ2 h0
      have habs := abs_lt.mp hω.2
      linarith

/-- **Eternal-AdS Quarter-Strip Equivalence.** Strip-free analyticity of the two-boundary
Wightman correlator `modularWightmanRL` on `0 < |Im ω| < 1/4` is equivalent both to
`RiemannHypothesis` and to quarter-rate reflected-pulse ringdown. -/
theorem riemannHypothesis_iff_modularWightmanRL_quarter_strip :
    RiemannHypothesis ↔
      AnalyticOnNhd ℂ modularWightmanRL {ω : ℂ | 0 < |ω.im| ∧ |ω.im| < 1 / 4} := by
  rw [modularWightmanRL_analyticOnNhd_strip_iff (by norm_num) le_rfl,
    RingdownRate.zeroFreeStrip_iff_pulse_ringdown (by norm_num) le_rfl,
    RingdownRate.riemannHypothesis_iff_pulse_ringdown]

/-- **Unconditional Eternal-AdS `1/16` Strip Analyticity.** The two-boundary Wightman correlator
`modularWightmanRL` is unconditionally analytic on `0 < |Im ω| < 1/16`. -/
theorem modularWightmanRL_analyticOnNhd_one_sixteenth :
    AnalyticOnNhd ℂ modularWightmanRL {ω : ℂ | 0 < |ω.im| ∧ |ω.im| < 1 / 16} := by
  rw [modularWightmanRL_analyticOnNhd_strip_iff (by norm_num) (by norm_num)]
  intro ρ hζ h0
  have hmem := riemannZeta_zero_mem_quasiRH_strip h0 hζ
  linarith [hmem.2]

/-- Quasinormal boundary frequency `ω_ρ = i(ρ - 1)/2` associated to a completed-zeta zero `ρ`. -/
def quasinormalFreq (ρ : ℂ) : ℂ :=
  I * (ρ - 1) / 2

/-- **Midpoint-Shift Separation Law.** Functional-equation reflection `ρ ↦ 1 - ρ̄` pairs
quasinormal damping rates around `1/4`: their sum is `1/2`, their minimum is
`1/4 - |Re ρ - 1/2|/2`, and quarter-rate damping holds if and only if `Re ρ = 1/2`. -/
theorem quasinormal_midpoint_shift_law (ρ : ℂ) :
    (-(quasinormalFreq ρ).im) + (-(quasinormalFreq (1 - starRingEnd ℂ ρ)).im) = 1 / 2 ∧
      min (-(quasinormalFreq ρ).im) (-(quasinormalFreq (1 - starRingEnd ℂ ρ)).im) =
        1 / 4 - |ρ.re - 1 / 2| / 2 ∧
      (1 / 4 ≤ min (-(quasinormalFreq ρ).im) (-(quasinormalFreq (1 - starRingEnd ℂ ρ)).im) ↔
        ρ.re = 1 / 2) := by
  have hd1 : -(quasinormalFreq ρ).im = (1 - ρ.re) / 2 := by
    simp [quasinormalFreq]; ring
  have hd2 : -(quasinormalFreq (1 - starRingEnd ℂ ρ)).im = ρ.re / 2 := by
    simp [quasinormalFreq]; ring
  rw [hd1, hd2]
  refine ⟨by ring, ?_, ?_⟩
  · rcases le_or_gt ρ.re (1 / 2) with hle | hgt
    · rw [min_eq_right (by linarith), abs_of_nonpos (by linarith)]
      ring
    · rw [min_eq_left (by linarith), abs_of_pos (by linarith)]
      ring
  · constructor
    · intro h
      have h1 : 1 / 4 ≤ (1 - ρ.re) / 2 := le_trans h (min_le_left _ _)
      have h2 : 1 / 4 ≤ ρ.re / 2 := le_trans h (min_le_right _ _)
      linarith
    · intro h
      rw [h]
      norm_num

end

end GaloisForLFunctions.BlackHoleRingdown
