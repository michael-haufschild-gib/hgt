import GaloisForLFunctions.HTGeometry.SimultaneousDirichlet
import Mathlib

/-!
# Prime-by-prime payment cannot use the Gamma factor

Frustration is a theorem about scalar conductances. The natural repair is kernel-valued: an Agler-type
decomposition of a Schur function on a half-plane,

`1 − S(s) conj S(s') = Σ_p (1 − p^{−s} conj p^{−s'}) K_p(s,s') + (1 − G(s) conj G(s')) K_∞(s,s')`,

with `K_p, K_∞` positive kernels, pays the energy prime by prime with weights that may depend on the height.
Here `G` is an archimedean coordinate, a Gamma-like Schur factor with `G(σ + it) → 0` as `t → ∞`.

**Theorem** (`norm_le_of_returns`, `agler_wall`). If such a decomposition exists, then `|S(s)| ≤ |G(s)|` at every
point, as soon as `S` also tends to `0` vertically. So the quotient `S/G` is Schur: the Gamma coordinate carries
all of `S`, and the prime conductances pay for nothing the archimedean coordinate does not already dominate.

**Mechanism.** Test the decomposition on the two points `s` and `s + iτ`, with `τ` a return of the primes, against
the vector `(1, −1)`. Every prime term is nonnegative up to the return error, since the coordinate `p^{−s}` barely
moves. The archimedean term is bounded by its diagonal, since `G(s + iτ)` is tiny, and the diagonal at `s` is
bounded by the equation itself. What remains is `|S(s)|² ≤ |G(s)|²(1 − |S(s)|²)/(1 − |G(s)|²)`, which is
`|S(s)| ≤ |G(s)|`. Only `2 × 2` positivity is used, so the theorem holds for kernels that are merely `2`-positive.

**The wall is sharp.**

* `aglerDecompositionMulTwo`: for `S = G' z₁ z₂` the decomposition exists explicitly, so the criterion
  `|S| ≤ |G'|` cannot be weakened on the positive side.
* `two_primes_first_test`: `S(s) = (1 + 2^{−s} + 3^{−s})/(s + 3)` is Schur on `Re s > 0`, yet it has no
  decomposition in the coordinates `2^{−s}, 3^{−s}, 1/(s+3)`. The coordinate `3/(s+3)` would be needed, which is the
  whole Euler size paid by the base: over all primes the size diverges.

**What survives.**

* `two_point_inequality` holds for arbitrary coordinates. Any certificate that passes the wall must use coordinates that
  do *not* return: the prime terms contribute `|z(s) − z(s + iτ)|²/((1 − |z(s)|²)(1 − |z(s + iτ)|²))`. A coordinate
  must see absolute height, and must differ from its value along returns by the size of what it pays.
* `norm_sub_sq_le_of_general`: with a general archimedean term `T(s,s') = (s + conj s') Q(s,s')`, the prime terms pay
  nothing at a return, so `|T(s, s+iτ)| + |T(s+iτ, s)| ≥ |S(s) − S(s+iτ)|²` up to the return error: `Q` cannot decay
  faster than `|S(s)|²/(2τ)`, a fixed proportion of the Szegő kernel. The archimedean term remembers every return.
-/

open Complex Finset Filter Topology

namespace GaloisForLFunctions.PrimeTorusTheory

noncomputable section

local notation "conj" => starRingEnd ℂ

/-- The Hermitian form of a `2 × 2` matrix at `(u, v)`. -/
def form2 (A B C D u v : ℂ) : ℂ :=
  u * conj u * A + u * conj v * B + v * conj u * C + v * conj v * D

/-- A kernel is `2`-positive if its form is nonnegative at every pair of points. -/
def TwoPositive {X : Type*} (K : X → X → ℂ) : Prop :=
  ∀ (x y : X) (u v : ℂ), 0 ≤ (form2 (K x x) (K x y) (K y x) (K y y) u v).re

theorem TwoPositive.diag_re_nonneg {X : Type*} {K : X → X → ℂ} (h : TwoPositive K) (x : X) :
    0 ≤ (K x x).re := by
  have := h x x 1 0
  simpa [form2] using this

theorem form2_scale (A B C D z u v : ℂ) :
    form2 A B C D (z * u) (z * v) = ((‖z‖ ^ 2 : ℝ) : ℂ) * form2 A B C D u v := by
  have hz : z * conj z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  unfold form2
  simp only [map_mul]
  rw [← hz]
  ring

theorem form2_zero_left (A B C D v : ℂ) :
    form2 A B C D 0 v = ((‖v‖ ^ 2 : ℝ) : ℂ) * D := by
  have hz : v * conj v = ((‖v‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  unfold form2
  simp only [map_zero, zero_mul, mul_zero, zero_add, add_zero]
  rw [hz]

theorem form2_zero_right (A B C D u : ℂ) :
    form2 A B C D u 0 = ((‖u‖ ^ 2 : ℝ) : ℂ) * A := by
  have hz : u * conj u = ((‖u‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  unfold form2
  simp only [map_zero, zero_mul, mul_zero, add_zero]
  rw [hz]

/-- The parallelogram identity of a sesquilinear form with a real scale. -/
theorem form2_parallelogram (A B C D a₁ a₂ b₁ b₂ : ℂ) {α : ℝ} (hα : α ≠ 0) :
    form2 A B C D (a₁ + b₁) (a₂ + b₂) +
        form2 A B C D ((α : ℂ) * a₁ - ((α⁻¹ : ℝ) : ℂ) * b₁) ((α : ℂ) * a₂ - ((α⁻¹ : ℝ) : ℂ) * b₂) =
      (1 + (α : ℂ) ^ 2) * form2 A B C D a₁ a₂ +
        (1 + ((α⁻¹ : ℝ) : ℂ) ^ 2) * form2 A B C D b₁ b₂ := by
  have hα' : (α : ℂ) ≠ 0 := by exact_mod_cast hα
  have hinv : ((α⁻¹ : ℝ) : ℂ) * (α : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, inv_mul_cancel₀ hα, Complex.ofReal_one]
  unfold form2
  simp only [map_add, map_sub, map_mul, Complex.conj_ofReal]
  linear_combination (-(a₁ * conj b₁ * A + a₁ * conj b₂ * B + b₁ * conj a₁ * A + b₁ * conj a₂ * B +
    conj a₁ * b₂ * C + conj b₁ * a₂ * C + conj a₂ * b₂ * D + conj b₂ * a₂ * D)) * hinv

/-- Young's inequality for a nonnegative form. -/
theorem re_form2_add_le {A B C D : ℂ} (hpsd : ∀ u v : ℂ, 0 ≤ (form2 A B C D u v).re)
    (a₁ a₂ b₁ b₂ : ℂ) {α : ℝ} (hα : α ≠ 0) :
    (form2 A B C D (a₁ + b₁) (a₂ + b₂)).re ≤
      (1 + α ^ 2) * (form2 A B C D a₁ a₂).re + (1 + (α⁻¹) ^ 2) * (form2 A B C D b₁ b₂).re := by
  have h := form2_parallelogram A B C D a₁ a₂ b₁ b₂ hα
  have hre := congrArg Complex.re h
  have e1 : (1 + (α : ℂ) ^ 2) = ((1 + α ^ 2 : ℝ) : ℂ) := by push_cast; ring
  have e2 : (1 + ((α⁻¹ : ℝ) : ℂ) ^ 2) = ((1 + (α⁻¹) ^ 2 : ℝ) : ℂ) := by push_cast; ring
  rw [e1, e2, Complex.add_re, Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul] at hre
  have := hpsd ((α : ℂ) * a₁ - ((α⁻¹ : ℝ) : ℂ) * b₁) ((α : ℂ) * a₂ - ((α⁻¹ : ℝ) : ℂ) * b₂)
  linarith

/-- The real part of the form at `(0, v)`. -/
theorem re_form2_zero_left (A B C D v : ℂ) :
    (form2 A B C D 0 v).re = ‖v‖ ^ 2 * D.re := by
  rw [form2_zero_left, Complex.re_ofReal_mul]

theorem re_form2_zero_right (A B C D u : ℂ) :
    (form2 A B C D u 0).re = ‖u‖ ^ 2 * A.re := by
  rw [form2_zero_right, Complex.re_ofReal_mul]

/-- **The prime term.** A coordinate that barely moves between the two points contributes a nonnegative amount
to the test vector `(1, −1)`, up to `|δ|²` times the diagonal. -/
theorem prime_term_lower {A B C D : ℂ} (hpsd : ∀ u v : ℂ, 0 ≤ (form2 A B C D u v).re) {z₁ z₂ : ℂ}
    (hr : ‖z₁‖ < 1) :
    -(‖z₁ - z₂‖ ^ 2 * D.re / (1 - ‖z₁‖ ^ 2)) ≤
      (form2 A B C D 1 (-1) - form2 A B C D z₁ (-z₂)).re := by
  have hr0 : 0 ≤ ‖z₁‖ := norm_nonneg _
  have hden : 0 < 1 - ‖z₁‖ ^ 2 := by nlinarith
  have hDnn : 0 ≤ D.re := by
    have := hpsd 0 1
    rw [re_form2_zero_left] at this
    simpa using this
  have hQ1 := hpsd 1 (-1)
  have hsplit : form2 A B C D z₁ (-z₂) =
      form2 A B C D (z₁ * 1 + 0) (z₁ * (-1) + (z₁ - z₂)) := by
    congr 1 <;> ring
  rw [Complex.sub_re, hsplit]
  have hbq : (form2 A B C D 0 (z₁ - z₂)).re = ‖z₁ - z₂‖ ^ 2 * D.re := re_form2_zero_left _ _ _ _ _
  have hbn : 0 ≤ ‖z₁ - z₂‖ ^ 2 * D.re := by positivity
  rcases hr0.eq_or_lt with hz | hz
  · -- `z₁ = 0`.
    have hz0 : z₁ = 0 := norm_eq_zero.mp hz.symm
    subst hz0
    simp only [zero_mul, add_zero, zero_add] at *
    rw [hbq]
    have : ‖(0 : ℂ) - z₂‖ ^ 2 * D.re / (1 - ‖(0 : ℂ)‖ ^ 2) = ‖(0 : ℂ) - z₂‖ ^ 2 * D.re := by
      simp
    rw [this]
    linarith
  · set r := ‖z₁‖ with hrdef
    have hr2 : 0 < r ^ 2 := by positivity
    have hα2 : 0 < 1 / r ^ 2 - 1 := by
      rw [sub_pos, lt_div_iff₀ hr2]
      nlinarith
    set α := √(1 / r ^ 2 - 1) with hα
    have hα0 : α ≠ 0 := (Real.sqrt_pos.mpr hα2).ne'
    have hαsq : α ^ 2 = 1 / r ^ 2 - 1 := Real.sq_sqrt hα2.le
    have hY := re_form2_add_le hpsd (z₁ * 1) (z₁ * (-1)) 0 (z₁ - z₂) hα0
    have hscale : (form2 A B C D (z₁ * 1) (z₁ * (-1))).re =
        r ^ 2 * (form2 A B C D 1 (-1)).re := by
      rw [form2_scale, Complex.re_ofReal_mul]
    have h1 : (1 + α ^ 2) * r ^ 2 = 1 := by
      rw [hαsq]
      field_simp
      ring
    have h2 : 1 + (α⁻¹) ^ 2 = 1 / (1 - r ^ 2) := by
      rw [inv_pow, hαsq]
      have hne : (1 / r ^ 2 - 1) ≠ 0 := hα2.ne'
      have hne2 : (1 : ℝ) - r ^ 2 ≠ 0 := hden.ne'
      have e : 1 / r ^ 2 - 1 = (1 - r ^ 2) / r ^ 2 := by
        field_simp
      rw [e]
      field_simp
      ring
    rw [hscale, hbq, h2] at hY
    have h3 : (1 + α ^ 2) * (r ^ 2 * (form2 A B C D 1 (-1)).re) = (form2 A B C D 1 (-1)).re := by
      rw [← mul_assoc, h1, one_mul]
    rw [h3] at hY
    have h4 : 1 / (1 - r ^ 2) * (‖z₁ - z₂‖ ^ 2 * D.re) = ‖z₁ - z₂‖ ^ 2 * D.re / (1 - r ^ 2) := by ring
    rw [h4] at hY
    linarith

/-! ### The decomposition and its two-point inequality -/

/-- An Agler-type decomposition of `S` in the coordinates `z_k` and the archimedean coordinate `G`, with
`2`-positive kernels. -/
structure AglerDecomposition {X ι : Type*} [Fintype ι] (S G : X → ℂ) (z : ι → X → ℂ) where
  /-- The conductance of the coordinate `z_k`. -/
  K : ι → X → X → ℂ
  /-- The conductance of the archimedean coordinate. -/
  K₀ : X → X → ℂ
  psd : ∀ k, TwoPositive (K k)
  psd₀ : TwoPositive K₀
  eq : ∀ x y, 1 - S x * conj (S y) =
    ∑ k, (1 - z k x * conj (z k y)) * K k x y + (1 - G x * conj (G y)) * K₀ x y

section Decomposition

variable {X ι : Type*} [Fintype ι] {S G : X → ℂ} {z : ι → X → ℂ}

/-- `1 − w conj w` is real. -/
theorem one_sub_mul_conj (w : ℂ) : 1 - w * conj w = ((1 - ‖w‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  ring

/-- The diagonal of the decomposition. -/
theorem AglerDecomposition.diag (D : AglerDecomposition S G z) (x : X) :
    1 - ‖S x‖ ^ 2 =
      ∑ k, (1 - ‖z k x‖ ^ 2) * (D.K k x x).re + (1 - ‖G x‖ ^ 2) * (D.K₀ x x).re := by
  have h := congrArg Complex.re (D.eq x x)
  simp only [one_sub_mul_conj, Complex.add_re, Complex.re_sum, Complex.re_ofReal_mul,
    Complex.ofReal_re] at h
  exact h

/-- Each coordinate pays at most the deficit of `S` on the diagonal. -/
theorem AglerDecomposition.coord_le (D : AglerDecomposition S G z) (hz : ∀ k x, ‖z k x‖ < 1)
    (hG : ∀ x, ‖G x‖ < 1) (k : ι) (x : X) :
    (1 - ‖z k x‖ ^ 2) * (D.K k x x).re ≤ 1 - ‖S x‖ ^ 2 := by
  have hnn : ∀ j ∈ Finset.univ, 0 ≤ (1 - ‖z j x‖ ^ 2) * (D.K j x x).re := fun j _ =>
    mul_nonneg (by nlinarith [hz j x, norm_nonneg (z j x)]) ((D.psd j).diag_re_nonneg x)
  have h1 := Finset.single_le_sum hnn (Finset.mem_univ k)
  have h2 : 0 ≤ (1 - ‖G x‖ ^ 2) * (D.K₀ x x).re :=
    mul_nonneg (by nlinarith [hG x, norm_nonneg (G x)]) (D.psd₀.diag_re_nonneg x)
  rw [D.diag]
  linarith

theorem AglerDecomposition.arch_le (D : AglerDecomposition S G z) (hz : ∀ k x, ‖z k x‖ < 1)
    (x : X) : (1 - ‖G x‖ ^ 2) * (D.K₀ x x).re ≤ 1 - ‖S x‖ ^ 2 := by
  have hnn : 0 ≤ ∑ k, (1 - ‖z k x‖ ^ 2) * (D.K k x x).re := Finset.sum_nonneg fun j _ =>
    mul_nonneg (by nlinarith [hz j x, norm_nonneg (z j x)]) ((D.psd j).diag_re_nonneg x)
  rw [D.diag]
  linarith

/-- The decomposition forces `|S| ≤ 1` on the diagonal. -/
theorem AglerDecomposition.norm_le_one (D : AglerDecomposition S G z) (hz : ∀ k x, ‖z k x‖ < 1)
    (hG : ∀ x, ‖G x‖ < 1) (x : X) : ‖S x‖ ^ 2 ≤ 1 := by
  have h2 := D.arch_le hz x
  have h3 : 0 ≤ (1 - ‖G x‖ ^ 2) * (D.K₀ x x).re :=
    mul_nonneg (by nlinarith [hG x, norm_nonneg (G x)]) (D.psd₀.diag_re_nonneg x)
  linarith

/-- The coordinate term of the test vector `(1, −1)`. -/
theorem form2_test (A B C D z₁ z₂ : ℂ) :
    (1 - z₁ * conj z₁) * A - (1 - z₁ * conj z₂) * B -
        ((1 - z₂ * conj z₁) * C - (1 - z₂ * conj z₂) * D) =
      form2 A B C D 1 (-1) - form2 A B C D z₁ (-z₂) := by
  simp only [form2, map_one, map_neg]
  ring

/-- The decomposition tested on `(1, −1)` at two points. -/
theorem AglerDecomposition.test (D : AglerDecomposition S G z) (x₁ x₂ : X) :
    -‖S x₁ - S x₂‖ ^ 2 =
      ∑ k, (form2 (D.K k x₁ x₁) (D.K k x₁ x₂) (D.K k x₂ x₁) (D.K k x₂ x₂) 1 (-1) -
          form2 (D.K k x₁ x₁) (D.K k x₁ x₂) (D.K k x₂ x₁) (D.K k x₂ x₂) (z k x₁) (-z k x₂)).re +
        (form2 (D.K₀ x₁ x₁) (D.K₀ x₁ x₂) (D.K₀ x₂ x₁) (D.K₀ x₂ x₂) 1 (-1) -
          form2 (D.K₀ x₁ x₁) (D.K₀ x₁ x₂) (D.K₀ x₂ x₁) (D.K₀ x₂ x₂) (G x₁) (-G x₂)).re := by
  have hc : ((-‖S x₁ - S x₂‖ ^ 2 : ℝ) : ℂ) =
      (1 - S x₁ * conj (S x₁)) - (1 - S x₁ * conj (S x₂)) -
        ((1 - S x₂ * conj (S x₁)) - (1 - S x₂ * conj (S x₂))) := by
    have := Complex.mul_conj (S x₁ - S x₂)
    rw [Complex.normSq_eq_norm_sq] at this
    rw [Complex.ofReal_neg, ← this]
    simp only [map_sub]
    ring
  have hR : (-‖S x₁ - S x₂‖ ^ 2 : ℝ) =
      ((1 - S x₁ * conj (S x₁)) - (1 - S x₁ * conj (S x₂)) -
        ((1 - S x₂ * conj (S x₁)) - (1 - S x₂ * conj (S x₂)))).re := by
    rw [← hc, Complex.ofReal_re]
  rw [hR, D.eq x₁ x₁, D.eq x₁ x₂, D.eq x₂ x₁, D.eq x₂ x₂, ← Complex.re_sum, ← Complex.add_re]
  congr 1
  rw [← form2_test, Finset.sum_congr rfl fun k _ => (form2_test _ _ _ _ (z k x₁) (z k x₂)).symm]
  simp only [Finset.sum_sub_distrib]
  ring

/-- **The two-point inequality.** For every scale `α ≠ 0`,
`|S₁ − S₂|² ≤ Σ_k |z_k(x₁) − z_k(x₂)|²/((1 − |z_k(x₁)|²)(1 − |z_k(x₂)|²))
  + (1 + α²)|G₁|²(1 − |S₁|²)/(1 − |G₁|²) + (1 + α⁻²)|G₂|²/(1 − |G₂|²)`. -/
theorem two_point_inequality (D : AglerDecomposition S G z) (hz : ∀ k x, ‖z k x‖ < 1)
    (hG : ∀ x, ‖G x‖ < 1) (x₁ x₂ : X) {α : ℝ} (hα : α ≠ 0) :
    ‖S x₁ - S x₂‖ ^ 2 ≤
      ∑ k, ‖z k x₁ - z k x₂‖ ^ 2 / ((1 - ‖z k x₁‖ ^ 2) * (1 - ‖z k x₂‖ ^ 2)) +
        (1 + α ^ 2) * (‖G x₁‖ ^ 2 * (1 - ‖S x₁‖ ^ 2) / (1 - ‖G x₁‖ ^ 2)) +
        (1 + (α⁻¹) ^ 2) * (‖G x₂‖ ^ 2 / (1 - ‖G x₂‖ ^ 2)) := by
  have hden : ∀ w : ℂ, ‖w‖ < 1 → 0 < 1 - ‖w‖ ^ 2 := fun w hw => by nlinarith [norm_nonneg w]
  -- The prime terms.
  have hprime : ∀ k, -(‖z k x₁ - z k x₂‖ ^ 2 / ((1 - ‖z k x₁‖ ^ 2) * (1 - ‖z k x₂‖ ^ 2))) ≤
      (form2 (D.K k x₁ x₁) (D.K k x₁ x₂) (D.K k x₂ x₁) (D.K k x₂ x₂) 1 (-1) -
        form2 (D.K k x₁ x₁) (D.K k x₁ x₂) (D.K k x₂ x₁) (D.K k x₂ x₂) (z k x₁) (-z k x₂)).re := by
    intro k
    refine le_trans ?_ (prime_term_lower (D.psd k x₁ x₂) (hz k x₁))
    have hd1 := hden _ (hz k x₁)
    have hd2 := hden _ (hz k x₂)
    have hDle : (D.K k x₂ x₂).re ≤ 1 / (1 - ‖z k x₂‖ ^ 2) := by
      rw [le_div_iff₀ hd2]
      have h1 := D.coord_le hz hG k x₂
      nlinarith [sq_nonneg ‖S x₂‖]
    have hnn : 0 ≤ ‖z k x₁ - z k x₂‖ ^ 2 := by positivity
    rw [neg_le_neg_iff, div_le_div_iff₀ hd1 (mul_pos hd1 hd2)]
    have := mul_le_mul_of_nonneg_left hDle hnn
    have e : ‖z k x₁ - z k x₂‖ ^ 2 * (1 / (1 - ‖z k x₂‖ ^ 2)) * (1 - ‖z k x₂‖ ^ 2) =
        ‖z k x₁ - z k x₂‖ ^ 2 := by
      field_simp
    have h3 : ‖z k x₁ - z k x₂‖ ^ 2 * (D.K k x₂ x₂).re * (1 - ‖z k x₂‖ ^ 2) ≤
        ‖z k x₁ - z k x₂‖ ^ 2 := by
      have := mul_le_mul_of_nonneg_right this hd2.le
      linarith
    nlinarith
  -- The archimedean term.
  have harch : -((1 + α ^ 2) * (‖G x₁‖ ^ 2 * (1 - ‖S x₁‖ ^ 2) / (1 - ‖G x₁‖ ^ 2)) +
      (1 + (α⁻¹) ^ 2) * (‖G x₂‖ ^ 2 / (1 - ‖G x₂‖ ^ 2))) ≤
      (form2 (D.K₀ x₁ x₁) (D.K₀ x₁ x₂) (D.K₀ x₂ x₁) (D.K₀ x₂ x₂) 1 (-1) -
        form2 (D.K₀ x₁ x₁) (D.K₀ x₁ x₂) (D.K₀ x₂ x₁) (D.K₀ x₂ x₂) (G x₁) (-G x₂)).re := by
    have hd1 := hden _ (hG x₁)
    have hd2 := hden _ (hG x₂)
    have hY := re_form2_add_le (D.psd₀ x₁ x₂) (G x₁) 0 0 (-G x₂) hα
    simp only [add_zero, zero_add] at hY
    rw [re_form2_zero_right, re_form2_zero_left, norm_neg] at hY
    have hA : (D.K₀ x₁ x₁).re ≤ (1 - ‖S x₁‖ ^ 2) / (1 - ‖G x₁‖ ^ 2) := by
      rw [le_div_iff₀ hd1]
      have := D.arch_le hz x₁
      linarith
    have hB : (D.K₀ x₂ x₂).re ≤ 1 / (1 - ‖G x₂‖ ^ 2) := by
      rw [le_div_iff₀ hd2]
      have := D.arch_le hz x₂
      nlinarith [sq_nonneg ‖S x₂‖]
    have h1 : ‖G x₁‖ ^ 2 * (D.K₀ x₁ x₁).re ≤ ‖G x₁‖ ^ 2 * (1 - ‖S x₁‖ ^ 2) / (1 - ‖G x₁‖ ^ 2) := by
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_left hA (by positivity)
    have h2 : ‖G x₂‖ ^ 2 * (D.K₀ x₂ x₂).re ≤ ‖G x₂‖ ^ 2 / (1 - ‖G x₂‖ ^ 2) := by
      have := mul_le_mul_of_nonneg_left hB (sq_nonneg ‖G x₂‖)
      rwa [mul_one_div] at this
    have h3 := D.psd₀ x₁ x₂ 1 (-1)
    rw [Complex.sub_re]
    have h4 : (1 + α ^ 2) * (‖G x₁‖ ^ 2 * (D.K₀ x₁ x₁).re) ≤
        (1 + α ^ 2) * (‖G x₁‖ ^ 2 * (1 - ‖S x₁‖ ^ 2) / (1 - ‖G x₁‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have h5 : (1 + (α⁻¹) ^ 2) * (‖G x₂‖ ^ 2 * (D.K₀ x₂ x₂).re) ≤
        (1 + (α⁻¹) ^ 2) * (‖G x₂‖ ^ 2 / (1 - ‖G x₂‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    linarith
  have htest := D.test x₁ x₂
  have hsum := Finset.sum_le_sum fun k (_ : k ∈ Finset.univ) => hprime k
  rw [Finset.sum_neg_distrib] at hsum
  linarith

/-- **The wall.** If `x₂ j` is a sequence along which every coordinate returns to its value at `x₁` while `S` and
`G` tend to `0`, then `|S(x₁)| ≤ |G(x₁)|`. -/
theorem norm_le_of_returns (D : AglerDecomposition S G z) (hz : ∀ k x, ‖z k x‖ < 1)
    (hG : ∀ x, ‖G x‖ < 1) (x₁ : X) (x₂ : ℕ → X)
    (hS0 : Tendsto (fun j => S (x₂ j)) atTop (𝓝 0)) (hG0 : Tendsto (fun j => G (x₂ j)) atTop (𝓝 0))
    (hret : ∀ k, Tendsto (fun j => z k (x₂ j)) atTop (𝓝 (z k x₁))) : ‖S x₁‖ ≤ ‖G x₁‖ := by
  have hden : ∀ w : ℂ, ‖w‖ < 1 → 0 < 1 - ‖w‖ ^ 2 := fun w hw => by nlinarith [norm_nonneg w]
  set W := ‖G x₁‖ ^ 2 * (1 - ‖S x₁‖ ^ 2) / (1 - ‖G x₁‖ ^ 2) with hW
  have hstep : ∀ α : ℝ, α ≠ 0 → ‖S x₁‖ ^ 2 ≤ (1 + α ^ 2) * W := by
    intro α hα
    have hL : Tendsto (fun j => ‖S x₁ - S (x₂ j)‖ ^ 2) atTop (𝓝 (‖S x₁‖ ^ 2)) := by
      have := ((tendsto_const_nhds (x := S x₁)).sub hS0).norm.pow 2
      simpa using this
    have hP : Tendsto (fun j => ∑ k, ‖z k x₁ - z k (x₂ j)‖ ^ 2 /
        ((1 - ‖z k x₁‖ ^ 2) * (1 - ‖z k (x₂ j)‖ ^ 2))) atTop (𝓝 0) := by
      have hz1 : ∀ k, Tendsto (fun j => ‖z k x₁ - z k (x₂ j)‖ ^ 2 /
          ((1 - ‖z k x₁‖ ^ 2) * (1 - ‖z k (x₂ j)‖ ^ 2))) atTop (𝓝 0) := by
        intro k
        have h1 : Tendsto (fun j => ‖z k x₁ - z k (x₂ j)‖ ^ 2) atTop (𝓝 0) := by
          have := ((tendsto_const_nhds (x := z k x₁)).sub (hret k)).norm.pow 2
          simpa using this
        have h2 : Tendsto (fun j => (1 - ‖z k x₁‖ ^ 2) * (1 - ‖z k (x₂ j)‖ ^ 2)) atTop
            (𝓝 ((1 - ‖z k x₁‖ ^ 2) * (1 - ‖z k x₁‖ ^ 2))) :=
          tendsto_const_nhds.mul (tendsto_const_nhds.sub ((hret k).norm.pow 2))
        have h3 := h1.div h2 (mul_pos (hden _ (hz k x₁)) (hden _ (hz k x₁))).ne'
        rw [zero_div] at h3
        exact h3
      have := tendsto_finsetSum (Finset.univ : Finset ι) fun k _ => hz1 k
      simpa using this
    have hA : Tendsto (fun j => (1 + (α⁻¹) ^ 2) * (‖G (x₂ j)‖ ^ 2 / (1 - ‖G (x₂ j)‖ ^ 2))) atTop
        (𝓝 0) := by
      have h1 : Tendsto (fun j => ‖G (x₂ j)‖ ^ 2) atTop (𝓝 0) := by
        have := hG0.norm.pow 2
        simpa using this
      have h2 : Tendsto (fun j => 1 - ‖G (x₂ j)‖ ^ 2) atTop (𝓝 (1 - 0)) := tendsto_const_nhds.sub h1
      have h3 := (h1.div h2 (by norm_num)).const_mul (1 + (α⁻¹) ^ 2)
      simpa using h3
    have hR := (hP.add (tendsto_const_nhds (x := (1 + α ^ 2) * W))).add hA
    have hle := le_of_tendsto_of_tendsto' hL hR fun j => two_point_inequality D hz hG x₁ (x₂ j) hα
    simpa using hle
  have hW0 : ‖S x₁‖ ^ 2 ≤ W := by
    have hlim : Tendsto (fun n : ℕ => (1 + (1 / ((n : ℝ) + 1)) ^ 2) * W) atTop (𝓝 ((1 + 0 ^ 2) * W)) := by
      have := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
      exact ((tendsto_const_nhds.add (this.pow 2))).mul_const W
    have hle : ‖S x₁‖ ^ 2 ≤ (1 + 0 ^ 2) * W :=
      ge_of_tendsto' hlim fun n => hstep _ (by positivity)
    simpa using hle
  have hd := hden _ (hG x₁)
  rw [hW, le_div_iff₀ hd] at hW0
  have hsq : ‖S x₁‖ ^ 2 ≤ ‖G x₁‖ ^ 2 := by nlinarith
  exact abs_le_of_sq_le_sq' hsq (norm_nonneg _) |>.2

end Decomposition

/-! ### The half-plane -/

/-- The half-plane `Re s > 0`. -/
abbrev HalfPlane : Type := {s : ℂ // 0 < s.re}

/-- The vertical translate of a point of the half-plane. -/
def vshift (s : HalfPlane) (τ : ℝ) : HalfPlane :=
  ⟨s.1 + (τ : ℂ) * I, by simpa using s.2⟩

/-- The prime coordinate `p^{−s}`. -/
def primeCoord (P : Finset ℕ) (p : P) (s : HalfPlane) : ℂ := ((p : ℕ) : ℂ) ^ (-s.1)

theorem norm_primeCoord_lt {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (p : P) (s : HalfPlane) :
    ‖primeCoord P p s‖ < 1 := by
  have hp := (hP p p.2).one_lt
  have hp0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast (hP p p.2).pos
  have hp1 : (1 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast hp
  unfold primeCoord
  rw [Complex.norm_natCast_cpow_of_pos (hP p p.2).pos]
  have hre : (-s.1).re < 0 := by simpa using s.2
  exact Real.rpow_lt_one_of_one_lt_of_neg hp1 hre

/-- A time sequence tending to `+∞` along which all the phases of a finite set of primes return to `1`. -/
theorem exists_returns (P : Finset ℕ) :
    ∃ τ : ℕ → ℝ, Tendsto τ atTop atTop ∧
      ∀ p ∈ P, Tendsto (fun j => cexp (-(((τ j * Real.log p : ℝ) : ℂ) * I))) atTop (𝓝 1) := by
  classical
  have hstep : ∀ j : ℕ, ∃ τ : ℝ, (j : ℝ) + 1 ≤ τ ∧ ∀ p ∈ P,
      ‖cexp (-(((τ * Real.log p : ℝ) : ℂ) * I)) - 1‖ ≤ 2 * Real.pi / ((j : ℝ) + 1) := by
    intro j
    let e := P.equivFin
    obtain ⟨q, hq1, -, hq⟩ := HTGeometry.exists_simultaneous_dirichlet
      (fun i : Fin P.card => ((j : ℝ) + 1) * Real.log ((e.symm i : P) : ℕ) / (2 * Real.pi))
      (Q := j + 1) (Nat.succ_pos j)
    refine ⟨(q : ℝ) * ((j : ℝ) + 1), ?_, ?_⟩
    · have : (1 : ℝ) ≤ q := by exact_mod_cast hq1
      nlinarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
    · intro p hp
      obtain ⟨m, hm⟩ := hq (e ⟨p, hp⟩)
      simp only [Equiv.symm_apply_apply] at hm
      have hpi : 0 < Real.pi := Real.pi_pos
      have hj : (0 : ℝ) < (j : ℝ) + 1 := by positivity
      set x := (q : ℝ) * ((j : ℝ) + 1) * Real.log p with hx
      have hclose : |x - 2 * Real.pi * m| ≤ 2 * Real.pi / ((j : ℝ) + 1) := by
        have e1 : x - 2 * Real.pi * m = (2 * Real.pi) *
            ((q : ℝ) * (((j : ℝ) + 1) * Real.log p / (2 * Real.pi)) - m) := by
          rw [hx]
          field_simp
        rw [e1, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
        have h2 := hm.le
        push_cast at h2
        calc
          2 * Real.pi * |(q : ℝ) * (((j : ℝ) + 1) * Real.log p / (2 * Real.pi)) - m|
              ≤ 2 * Real.pi * (1 / ((j : ℝ) + 1)) :=
                mul_le_mul_of_nonneg_left h2 (by positivity)
          _ = 2 * Real.pi / ((j : ℝ) + 1) := by ring
      have hper : cexp (-((x : ℂ) * I)) = cexp (-(((x - 2 * Real.pi * m : ℝ) : ℂ) * I)) := by
        have h3 : -((x : ℂ) * I) = -(((x - 2 * Real.pi * m : ℝ) : ℂ) * I) + ((-m : ℤ) : ℂ) * (2 * Real.pi * I) := by
          push_cast
          ring
        rw [h3, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
      rw [hper]
      have hn : ‖cexp (-(((x - 2 * Real.pi * m : ℝ) : ℂ) * I)) - 1‖ ≤ |x - 2 * Real.pi * m| := by
        have h4 : -(((x - 2 * Real.pi * m : ℝ) : ℂ) * I) = ((-(x - 2 * Real.pi * m) : ℝ) : ℂ) * I := by
          push_cast
          ring
        rw [h4]
        have := Real.norm_exp_I_mul_ofReal_sub_one_le (x := -(x - 2 * Real.pi * m))
        rw [mul_comm] at this
        rw [abs_sub_comm]
        simpa using this
      exact hn.trans hclose
  choose τ hτ1 hτ2 using hstep
  refine ⟨τ, ?_, ?_⟩
  · refine tendsto_atTop_mono (fun j => (hτ1 j)) ?_
    exact tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  · intro p hp
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) (fun j => hτ2 j p hp) ?_
    have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (2 * Real.pi)
    simp only [mul_zero] at this
    refine this.congr fun j => ?_
    ring

/-- The prime coordinate returns along the return times. -/
theorem primeCoord_vshift {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (p : P) (s : HalfPlane) (τ : ℝ) :
    primeCoord P p (vshift s τ) =
      primeCoord P p s * cexp (-(((τ * Real.log (p : ℕ) : ℝ) : ℂ) * I)) := by
  unfold primeCoord vshift
  have hp0 : ((p : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (hP p p.2).ne_zero
  rw [neg_add, Complex.cpow_add _ _ hp0]
  congr 1
  rw [Complex.cpow_def_of_ne_zero hp0, ← Complex.natCast_log]
  congr 1
  push_cast
  ring

/-- **The Agler wall.** Let `P` be a finite set of primes, and `S`, `G` functions on the half-plane with `|G| < 1`, both
tending to `0` vertically. If `S` has an Agler decomposition in the coordinates `p^{−s}` and `G`, then `|S| ≤ |G|`. -/
theorem agler_wall {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) {S G : HalfPlane → ℂ}
    (D : AglerDecomposition S G (primeCoord P)) (hG : ∀ x, ‖G x‖ < 1)
    (hGv : ∀ s, Tendsto (fun τ => G (vshift s τ)) atTop (𝓝 0))
    (hSv : ∀ s, Tendsto (fun τ => S (vshift s τ)) atTop (𝓝 0)) (s : HalfPlane) : ‖S s‖ ≤ ‖G s‖ := by
  obtain ⟨τ, hτ, hret⟩ := exists_returns P
  refine norm_le_of_returns D (fun k x => norm_primeCoord_lt hP k x) hG s (fun j => vshift s (τ j))
    ((hSv s).comp hτ) ((hGv s).comp hτ) fun p => ?_
  have := (hret p p.2).const_mul (primeCoord P p s)
  rw [mul_one] at this
  exact this.congr fun j => (primeCoord_vshift hP p s (τ j)).symm

/-- A Gamma-like factor pays no Euler size: if `S = G · F` has a decomposition, then `|F| ≤ 1` where `G ≠ 0`. -/
theorem norm_le_one_of_agler {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) {G F : HalfPlane → ℂ}
    (D : AglerDecomposition (fun s => G s * F s) G (primeCoord P)) (hG : ∀ x, ‖G x‖ < 1)
    (hGv : ∀ s, Tendsto (fun τ => G (vshift s τ)) atTop (𝓝 0))
    (hSv : ∀ s, Tendsto (fun τ => G (vshift s τ) * F (vshift s τ)) atTop (𝓝 0)) {s : HalfPlane}
    (hs : G s ≠ 0) : ‖F s‖ ≤ 1 := by
  have h := agler_wall hP D hG hGv hSv s
  simp only [norm_mul] at h
  have hpos : 0 < ‖G s‖ := norm_pos_iff.mpr hs
  nlinarith

/-! ### Sharpness: the first test -/

/-- The kernel of a single function is `2`-positive. -/
theorem twoPositive_rankOne {X : Type*} (h : X → ℂ) :
    TwoPositive fun x y => h x * conj (h y) := by
  intro x y u v
  have e : form2 (h x * conj (h x)) (h x * conj (h y)) (h y * conj (h x)) (h y * conj (h y)) u v =
      ((‖u * h x + v * h y‖ ^ 2 : ℝ) : ℂ) := by
    have := Complex.mul_conj (u * h x + v * h y)
    rw [Complex.normSq_eq_norm_sq] at this
    rw [← this]
    simp only [form2, map_add, map_mul]
    ring
  rw [e, Complex.ofReal_re]
  positivity

/-- **The positive side.** If `S = G' z₁ z₂` for Schur coordinates, the decomposition exists explicitly: the archimedean
coordinate `G'` dominates `S`, and each prime coordinate pays what the previous ones leave. -/
def aglerDecompositionMulTwo {X : Type*} (G' z₁ z₂ : X → ℂ) :
    AglerDecomposition (fun x => G' x * z₁ x * z₂ x) G' (fun k : Fin 2 => if k = 0 then z₁ else z₂) where
  K k := if k = 0 then fun x y => G' x * conj (G' y)
    else fun x y => (G' x * z₁ x) * conj (G' y * z₁ y)
  K₀ _ _ := 1
  psd k := by
    by_cases hk : k = 0
    · simpa [hk] using twoPositive_rankOne G'
    · simpa [hk] using twoPositive_rankOne fun x => G' x * z₁ x
  psd₀ := by
    have := twoPositive_rankOne fun _ : X => (1 : ℂ)
    simpa using this
  eq x y := by
    simp only [Fin.sum_univ_two, Fin.isValue, if_true, map_mul]
    simp only [show ((1 : Fin 2) = 0) = False by decide, if_false]
    ring

/-- `(1 + 2^{−s} + 3^{−s})/(s + 3)`. -/
def firstTestS (s : HalfPlane) : ℂ :=
  (1 + (2 : ℂ) ^ (-s.1) + (3 : ℂ) ^ (-s.1)) / (s.1 + 3)

/-- `1/(s + 3)`. -/
def firstTestG (s : HalfPlane) : ℂ := 1 / (s.1 + 3)

theorem three_lt_norm_add_three (s : HalfPlane) : 3 < ‖s.1 + 3‖ := by
  have h := Complex.abs_re_le_norm (s.1 + 3)
  have hre : (s.1 + 3).re = s.1.re + 3 := by simp
  rw [hre, abs_of_pos (by linarith [s.2])] at h
  linarith [s.2]

theorem norm_firstTest_numerator_le (s : HalfPlane) :
    ‖1 + (2 : ℂ) ^ (-s.1) + (3 : ℂ) ^ (-s.1)‖ ≤ 3 := by
  have h2 : ‖(2 : ℂ) ^ (-s.1)‖ ≤ 1 := by
    have := Complex.norm_natCast_cpow_of_pos (n := 2) (by norm_num) (-s.1)
    norm_cast at this
    rw [this]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by simpa using s.2.le)
  have h3 : ‖(3 : ℂ) ^ (-s.1)‖ ≤ 1 := by
    have := Complex.norm_natCast_cpow_of_pos (n := 3) (by norm_num) (-s.1)
    norm_cast at this
    rw [this]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by simpa using s.2.le)
  calc
    _ ≤ ‖(1 : ℂ) + (2 : ℂ) ^ (-s.1)‖ + ‖(3 : ℂ) ^ (-s.1)‖ := norm_add_le _ _
    _ ≤ ‖(1 : ℂ)‖ + ‖(2 : ℂ) ^ (-s.1)‖ + ‖(3 : ℂ) ^ (-s.1)‖ := by
        gcongr
        exact norm_add_le _ _
    _ ≤ 3 := by
        rw [norm_one]
        linarith

/-- The first test function is Schur on the half-plane. -/
theorem norm_firstTestS_lt (s : HalfPlane) : ‖firstTestS s‖ < 1 := by
  unfold firstTestS
  rw [norm_div, div_lt_one (by linarith [three_lt_norm_add_three s])]
  linarith [norm_firstTest_numerator_le s, three_lt_norm_add_three s]

theorem norm_firstTestG_lt (s : HalfPlane) : ‖firstTestG s‖ < 1 := by
  unfold firstTestG
  rw [norm_div, norm_one, div_lt_one (by linarith [three_lt_norm_add_three s])]
  linarith [three_lt_norm_add_three s]

theorem tendsto_inv_vshift (s : HalfPlane) :
    Tendsto (fun τ : ℝ => ‖(vshift s τ).1 + 3‖⁻¹) atTop (𝓝 0) := by
  refine tendsto_inv_atTop_zero.comp ?_
  refine tendsto_atTop_mono (f := fun τ : ℝ => τ + s.1.im) (fun τ => ?_) ?_
  · have h := Complex.abs_im_le_norm ((vshift s τ).1 + 3)
    have him : ((vshift s τ).1 + 3).im = s.1.im + τ := by
      simp [vshift]
    rw [him] at h
    have := le_abs_self (s.1.im + τ)
    linarith
  · exact tendsto_atTop_add_const_right _ _ tendsto_id

theorem tendsto_firstTestG (s : HalfPlane) :
    Tendsto (fun τ => firstTestG (vshift s τ)) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine (tendsto_inv_vshift s).congr fun τ => ?_
  unfold firstTestG
  rw [norm_div, norm_one, one_div]

theorem tendsto_firstTestS (s : HalfPlane) :
    Tendsto (fun τ => firstTestS (vshift s τ)) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h3 := (tendsto_inv_vshift s).const_mul 3
  rw [mul_zero] at h3
  refine squeeze_zero (fun _ => norm_nonneg _) (fun τ => ?_) h3
  unfold firstTestS
  rw [norm_div, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right (norm_firstTest_numerator_le _) (inv_nonneg.mpr (norm_nonneg _))

/-- The point `s = 1`. -/
def pointOne : HalfPlane := ⟨1, by simp⟩

/-- **The first test.** `S(s) = (1 + 2^{−s} + 3^{−s})/(s + 3)` is Schur on the half-plane, tends to `0` vertically, and has
*no* decomposition in the coordinates `2^{−s}`, `3^{−s}` and `1/(s+3)`. -/
theorem two_primes_first_test :
    (∀ s, ‖firstTestS s‖ < 1) ∧
      IsEmpty (AglerDecomposition firstTestS firstTestG (primeCoord ({2, 3} : Finset ℕ))) := by
  refine ⟨norm_firstTestS_lt, ⟨fun D => ?_⟩⟩
  have hP : ∀ p ∈ ({2, 3} : Finset ℕ), p.Prime := by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl <;> norm_num
  have h := agler_wall hP D norm_firstTestG_lt tendsto_firstTestG tendsto_firstTestS pointOne
  have hS : firstTestS pointOne = ((11 / 24 : ℝ) : ℂ) := by
    unfold firstTestS pointOne
    simp only [Complex.cpow_neg, Complex.cpow_one]
    push_cast
    norm_num
  have hG : firstTestG pointOne = ((1 / 4 : ℝ) : ℂ) := by
    unfold firstTestG pointOne
    push_cast
    norm_num
  rw [hS, hG, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (by norm_num), abs_of_pos (by norm_num)] at h
  norm_num at h

/-! ### What survives: a general archimedean term cannot be local -/

/-- A decomposition with a general archimedean term `T`, nonnegative on the diagonal, on two points. The trivial
decomposition of a Schur function on the half-plane is of this type with `T = 1 − S conj S`, `K_k = 0`. Here `T` is
bounded below by what the prime terms cannot pay. -/
theorem norm_sub_sq_le_of_general {ι : Type*} [Fintype ι] {S₁ S₂ : ℂ} {z₁ z₂ : ι → ℂ}
    {A B C E : ι → ℂ} {T₁₁ T₁₂ T₂₁ T₂₂ : ℂ}
    (hpsd : ∀ k, ∀ u v : ℂ, 0 ≤ (form2 (A k) (B k) (C k) (E k) u v).re)
    (hz₁ : ∀ k, ‖z₁ k‖ < 1) (hz₂ : ∀ k, ‖z₂ k‖ < 1)
    (h₁₁ : 1 - S₁ * conj S₁ = ∑ k, (1 - z₁ k * conj (z₁ k)) * A k + T₁₁)
    (h₁₂ : 1 - S₁ * conj S₂ = ∑ k, (1 - z₁ k * conj (z₂ k)) * B k + T₁₂)
    (h₂₁ : 1 - S₂ * conj S₁ = ∑ k, (1 - z₂ k * conj (z₁ k)) * C k + T₂₁)
    (h₂₂ : 1 - S₂ * conj S₂ = ∑ k, (1 - z₂ k * conj (z₂ k)) * E k + T₂₂)
    (hT₁₁ : 0 ≤ T₁₁.re) (hT₂₂ : 0 ≤ T₂₂.re) :
    ‖S₁ - S₂‖ ^ 2 ≤
      ∑ k, ‖z₁ k - z₂ k‖ ^ 2 / ((1 - ‖z₁ k‖ ^ 2) * (1 - ‖z₂ k‖ ^ 2)) + ‖T₁₂‖ + ‖T₂₁‖ := by
  have hden : ∀ w : ℂ, ‖w‖ < 1 → 0 < 1 - ‖w‖ ^ 2 := fun w hw => by nlinarith [norm_nonneg w]
  have hEnn : ∀ k, 0 ≤ (E k).re := fun k => by
    have := hpsd k 0 1
    rw [re_form2_zero_left] at this
    simpa using this
  -- The diagonal at the second point.
  have hdiag : ∀ k, (1 - ‖z₂ k‖ ^ 2) * (E k).re ≤ 1 := by
    intro k
    have h := congrArg Complex.re h₂₂
    simp only [one_sub_mul_conj, Complex.add_re, Complex.re_sum, Complex.re_ofReal_mul,
      Complex.ofReal_re] at h
    have hnn : ∀ j ∈ Finset.univ, 0 ≤ (1 - ‖z₂ j‖ ^ 2) * (E j).re := fun j _ =>
      mul_nonneg (hden _ (hz₂ j)).le (hEnn j)
    have h1 := Finset.single_le_sum hnn (Finset.mem_univ k)
    nlinarith [sq_nonneg ‖S₂‖]
  have hprime : ∀ k, -(‖z₁ k - z₂ k‖ ^ 2 / ((1 - ‖z₁ k‖ ^ 2) * (1 - ‖z₂ k‖ ^ 2))) ≤
      (form2 (A k) (B k) (C k) (E k) 1 (-1) - form2 (A k) (B k) (C k) (E k) (z₁ k) (-z₂ k)).re := by
    intro k
    refine le_trans ?_ (prime_term_lower (hpsd k) (hz₁ k))
    have hd1 := hden _ (hz₁ k)
    have hd2 := hden _ (hz₂ k)
    have hle : (E k).re ≤ 1 / (1 - ‖z₂ k‖ ^ 2) := by
      rw [le_div_iff₀ hd2]
      linarith [hdiag k]
    have hnn : 0 ≤ ‖z₁ k - z₂ k‖ ^ 2 := by positivity
    rw [neg_le_neg_iff, div_le_div_iff₀ hd1 (mul_pos hd1 hd2)]
    have h3 : ‖z₁ k - z₂ k‖ ^ 2 * (E k).re * (1 - ‖z₂ k‖ ^ 2) ≤ ‖z₁ k - z₂ k‖ ^ 2 := by
      have := hdiag k
      nlinarith
    nlinarith
  have hc : ((-‖S₁ - S₂‖ ^ 2 : ℝ) : ℂ) =
      (1 - S₁ * conj S₁) - (1 - S₁ * conj S₂) - ((1 - S₂ * conj S₁) - (1 - S₂ * conj S₂)) := by
    have := Complex.mul_conj (S₁ - S₂)
    rw [Complex.normSq_eq_norm_sq] at this
    rw [Complex.ofReal_neg, ← this]
    simp only [map_sub]
    ring
  have hR : (-‖S₁ - S₂‖ ^ 2 : ℝ) =
      ((1 - S₁ * conj S₁) - (1 - S₁ * conj S₂) - ((1 - S₂ * conj S₁) - (1 - S₂ * conj S₂))).re := by
    rw [← hc, Complex.ofReal_re]
  have hsum : ((1 - S₁ * conj S₁) - (1 - S₁ * conj S₂) - ((1 - S₂ * conj S₁) - (1 - S₂ * conj S₂))) =
      ∑ k, (form2 (A k) (B k) (C k) (E k) 1 (-1) - form2 (A k) (B k) (C k) (E k) (z₁ k) (-z₂ k)) +
        (T₁₁ - T₁₂ - (T₂₁ - T₂₂)) := by
    rw [h₁₁, h₁₂, h₂₁, h₂₂, Finset.sum_congr rfl fun k _ => (form2_test _ _ _ _ (z₁ k) (z₂ k)).symm]
    simp only [Finset.sum_sub_distrib]
    ring
  rw [hsum, Complex.add_re, Complex.re_sum] at hR
  have hS := Finset.sum_le_sum fun k (_ : k ∈ Finset.univ) => hprime k
  rw [Finset.sum_neg_distrib] at hS
  have hT : (T₁₁ - T₁₂ - (T₂₁ - T₂₂)).re ≥ -(‖T₁₂‖ + ‖T₂₁‖) := by
    simp only [Complex.sub_re]
    have h1 := Complex.re_le_norm T₁₂
    have h2 := Complex.re_le_norm T₂₁
    linarith
  linarith

end

end GaloisForLFunctions.PrimeTorusTheory
