import GaloisForLFunctions.RHTower.BesselKZeroMoments
import GaloisForLFunctions.RHTower.MaassAxisUniqueContinuation

/-!
# Bessel series on the upper half-plane

For a coefficient sequence `g` of polynomial growth and `α ∈ ℝ`, `j, k ∈ ℕ`, `b ∈ {cos, sin}` put

`S_{α,j,k,b}(x + iy) = Σ_{n ≥ 1} g_n · n^k y^α K_j(2πny) · trig_b(2πnx)`  (`besselSeries`),

with the moments `K_j` of `BesselKZeroMoments`.  On every horizontal strip `y₁ < y < y₂`, `y₁ > 0`,
the terms and their derivatives are `O(n^m e^{−2πny₁})`, so the series may be differentiated termwise
(`hasFDerivAt_besselSeries`):

* `∂ₓ S_{α,j,k,b} = 2π·sgn(b)·S_{α,j,k+1,b̄}`, where `cos' = −sin`, `sin' = cos`;
* `∂ᵧ S_{α,j,k,b} = α S_{α−1,j,k,b} − 2π S_{α,j+1,k+1,b}`, from `K_j' = −K_{j+1}`.

The complex span of all `S_{α,j,k,b}` is therefore closed under `∂ₓ` and `∂ᵧ`, and every member is
`C^∞` on the upper half-plane (`contDiffOn_of_mem_besselSpan`).
-/

open Complex Set Filter Topology
open scoped ContDiff

noncomputable section

namespace RHTower.MaassBesselSeries

open BesselKZero MaassAxisContinuation

/-! ## The one-variable factors -/

/-- `cos` (`false`) or `sin` (`true`). -/
def trigFun (b : Bool) (θ : ℝ) : ℝ := if b then Real.sin θ else Real.cos θ

/-- `cos' = −sin`, `sin' = cos`. -/
def trigSign (b : Bool) : ℝ := if b then 1 else -1

theorem hasDerivAt_trigFun (b : Bool) (θ : ℝ) :
    HasDerivAt (trigFun b) (trigSign b * trigFun (!b) θ) θ := by
  cases b
  · simpa [trigFun, trigSign] using Real.hasDerivAt_cos θ
  · simpa [trigFun, trigSign] using Real.hasDerivAt_sin θ

theorem abs_trigFun_le (b : Bool) (θ : ℝ) : |trigFun b θ| ≤ 1 := by
  cases b
  · exact Real.abs_cos_le_one θ
  · exact Real.abs_sin_le_one θ

/-- `n^k y^α K_j(2πny)`. -/
def yPart (α : ℝ) (j k n : ℕ) (y : ℝ) : ℝ := (n : ℝ) ^ k * y ^ α * kMoment j (2 * Real.pi * n * y)

/-- `trig_b(2πnx)`. -/
def xPart (b : Bool) (n : ℕ) (x : ℝ) : ℝ := trigFun b (2 * Real.pi * n * x)

theorem hasDerivAt_yPart (α : ℝ) (j k : ℕ) {n : ℕ} (hn : 1 ≤ n) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (yPart α j k n)
      (α * yPart (α - 1) j k n y - 2 * Real.pi * yPart α (j + 1) (k + 1) n y) y := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hr : 0 < 2 * Real.pi * n * y := by positivity
  have hpow : HasDerivAt (fun y : ℝ => y ^ α) (α * y ^ (α - 1)) y :=
    Real.hasDerivAt_rpow_const (Or.inl hy.ne')
  have hlin : HasDerivAt (fun y : ℝ => 2 * Real.pi * n * y) (2 * Real.pi * n) y := by
    simpa using (hasDerivAt_id y).const_mul (2 * Real.pi * n)
  have hK : HasDerivAt (fun y : ℝ => kMoment j (2 * Real.pi * n * y))
      (-kMoment (j + 1) (2 * Real.pi * n * y) * (2 * Real.pi * n)) y :=
    (hasDerivAt_kMoment j hr).comp y hlin
  have h := ((hpow.const_mul ((n : ℝ) ^ k)).mul hK)
  refine h.congr_deriv ?_
  unfold yPart
  rw [pow_succ]
  ring

theorem hasDerivAt_xPart (b : Bool) (n : ℕ) (x : ℝ) :
    HasDerivAt (xPart b n) (2 * Real.pi * n * trigSign b * xPart (!b) n x) x := by
  have hlin : HasDerivAt (fun x : ℝ => 2 * Real.pi * n * x) (2 * Real.pi * n) x := by
    simpa using (hasDerivAt_id x).const_mul (2 * Real.pi * n)
  have h := (hasDerivAt_trigFun b (2 * Real.pi * n * x)).comp x hlin
  refine h.congr_deriv ?_
  unfold xPart
  ring

/-! ## The terms -/

/-- `n^k y^α K_j(2πny) trig_b(2πnx)` at `z = x + iy`. -/
def bterm (α : ℝ) (j k : ℕ) (b : Bool) (n : ℕ) (z : ℂ) : ℝ := yPart α j k n z.im * xPart b n z.re

/-- The `x`-derivative of a term. -/
def btermDx (α : ℝ) (j k : ℕ) (b : Bool) (n : ℕ) (z : ℂ) : ℝ :=
  2 * Real.pi * trigSign b * bterm α j (k + 1) (!b) n z

/-- The `y`-derivative of a term. -/
def btermDy (α : ℝ) (j k : ℕ) (b : Bool) (n : ℕ) (z : ℂ) : ℝ :=
  α * bterm (α - 1) j k b n z - 2 * Real.pi * bterm α (j + 1) (k + 1) b n z

/-- The real-linear map `v ↦ c₁ Re v + c₂ Im v`. -/
def coordCLM (c₁ c₂ : ℝ) : ℂ →L[ℝ] ℝ := c₁ • reCLM + c₂ • imCLM

theorem coordCLM_apply (c₁ c₂ : ℝ) (v : ℂ) : coordCLM c₁ c₂ v = c₁ * v.re + c₂ * v.im := by
  simp [coordCLM]

theorem hasFDerivAt_bterm (α : ℝ) (j k : ℕ) (b : Bool) {n : ℕ} (hn : 1 ≤ n) {z : ℂ}
    (hz : 0 < z.im) :
    HasFDerivAt (bterm α j k b n)
      (coordCLM (btermDx α j k b n z) (btermDy α j k b n z)) z := by
  have hy := (hasDerivAt_yPart α j k hn hz).comp_hasFDerivAt z imCLM.hasFDerivAt
  have hx := (hasDerivAt_xPart b n z.re).comp_hasFDerivAt z reCLM.hasFDerivAt
  have h := hy.mul hx
  refine h.congr_fderiv ?_
  ext v
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    coordCLM_apply, btermDx, btermDy, bterm, Function.comp, reCLM_apply, imCLM_apply]
  unfold yPart xPart
  rw [pow_succ]
  ring

/-! ## Bounds on horizontal strips -/

theorem yPart_abs_le {α : ℝ} {j k n : ℕ} (hn : 1 ≤ n) {y₁ y₂ y : ℝ} (hy₁ : 0 < y₁) (h₁ : y₁ ≤ y)
    (h₂ : y ≤ y₂) :
    |yPart α j k n y| ≤ (n : ℝ) ^ k * (y₁ ^ α + y₂ ^ α) *
      (Real.exp (2 * Real.pi * y₁) * kMoment j (2 * Real.pi * y₁)) *
        Real.exp (-(2 * Real.pi * y₁) * n) := by
  have hn0 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hy : 0 < y := lt_of_lt_of_le hy₁ h₁
  have hr₁ : 0 < 2 * Real.pi * y₁ := by positivity
  have hle : 2 * Real.pi * y₁ ≤ 2 * Real.pi * n * y := by
    have : y₁ ≤ n * y := by nlinarith
    nlinarith [Real.pi_pos]
  have hK := kMoment_le_exp_mul j hr₁ hle
  have hK0 := kMoment_nonneg j (2 * Real.pi * n * y)
  have hpow : y ^ α ≤ y₁ ^ α + y₂ ^ α := by
    rcases le_total 0 α with hα | hα
    · have := Real.rpow_le_rpow hy.le h₂ hα
      linarith [Real.rpow_nonneg hy₁.le α]
    · have := Real.rpow_le_rpow_of_nonpos hy₁ h₁ hα
      linarith [Real.rpow_nonneg (le_trans hy₁.le (h₁.trans h₂)) α]
  have hexp : Real.exp (-(2 * Real.pi * n * y - 2 * Real.pi * y₁)) ≤
      Real.exp (2 * Real.pi * y₁) * Real.exp (-(2 * Real.pi * y₁) * n) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [Real.pi_pos]
  unfold yPart
  rw [abs_mul, abs_mul, abs_of_nonneg (pow_nonneg (Nat.cast_nonneg n) k),
    abs_of_nonneg (Real.rpow_nonneg hy.le α), abs_of_nonneg hK0]
  have hKM : 0 ≤ kMoment j (2 * Real.pi * y₁) := kMoment_nonneg _ _
  calc (n : ℝ) ^ k * y ^ α * kMoment j (2 * Real.pi * n * y)
      ≤ (n : ℝ) ^ k * (y₁ ^ α + y₂ ^ α) *
          (Real.exp (-(2 * Real.pi * n * y - 2 * Real.pi * y₁)) * kMoment j (2 * Real.pi * y₁)) := by
        gcongr
    _ ≤ (n : ℝ) ^ k * (y₁ ^ α + y₂ ^ α) *
          (Real.exp (2 * Real.pi * y₁) * Real.exp (-(2 * Real.pi * y₁) * n) *
            kMoment j (2 * Real.pi * y₁)) := by
        have h0 : 0 ≤ (n : ℝ) ^ k * (y₁ ^ α + y₂ ^ α) := by
          have := Real.rpow_nonneg hy₁.le α
          have := Real.rpow_nonneg (le_trans hy₁.le (h₁.trans h₂)) α
          positivity
        gcongr
    _ = _ := by ring

theorem bterm_abs_le {α : ℝ} {j k : ℕ} {b : Bool} {n : ℕ} (hn : 1 ≤ n) {y₁ y₂ : ℝ} (hy₁ : 0 < y₁)
    {z : ℂ} (h₁ : y₁ ≤ z.im) (h₂ : z.im ≤ y₂) :
    |bterm α j k b n z| ≤ (n : ℝ) ^ k * (y₁ ^ α + y₂ ^ α) *
      (Real.exp (2 * Real.pi * y₁) * kMoment j (2 * Real.pi * y₁)) *
        Real.exp (-(2 * Real.pi * y₁) * n) := by
  unfold bterm
  rw [abs_mul]
  have h := yPart_abs_le (α := α) (j := j) (k := k) hn hy₁ h₁ h₂
  have ht := abs_trigFun_le b (2 * Real.pi * n * z.re)
  calc |yPart α j k n z.im| * |xPart b n z.re| ≤ |yPart α j k n z.im| * 1 := by
        gcongr; exact ht
    _ ≤ _ := by rw [mul_one]; exact h

/-- `Σ_n (n + 1)^m e^{−c(n+1)} < ∞`. -/
theorem summable_pow_mul_exp_neg (m : ℕ) {c : ℝ} (hc : 0 < c) :
    Summable fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ m * Real.exp (-c * ((n + 1 : ℕ) : ℝ)) :=
  (summable_nat_add_iff 1).mpr (Real.summable_pow_mul_exp_neg_nat_mul m hc)

/-! ## The series -/

/-- Polynomial growth `‖g n‖ ≤ C (n + 1)^A`. -/
def PolyGrowth (g : ℕ → ℂ) : Prop := ∃ C : ℝ, 0 ≤ C ∧ ∃ A : ℕ, ∀ n, ‖g n‖ ≤ C * ((n : ℝ) + 1) ^ A

variable (g : ℕ → ℂ)

/-- The term `g_n · n^k y^α K_j(2πny) trig_b(2πnx)` of index `n + 1`. -/
def sterm (α : ℝ) (j k : ℕ) (b : Bool) (n : ℕ) (z : ℂ) : ℂ :=
  g (n + 1) * (bterm α j k b (n + 1) z : ℂ)

/-- The Bessel series `S_{α,j,k,b}`. -/
def besselSeries (α : ℝ) (j k : ℕ) (b : Bool) (z : ℂ) : ℂ := ∑' n, sterm g α j k b n z

/-- `(1/2)` of the horizontal strip `y₁ < y < y₂`. -/
def strip (y₁ y₂ : ℝ) : Set ℂ := {z | y₁ < z.im ∧ z.im < y₂}

theorem isOpen_strip (y₁ y₂ : ℝ) : IsOpen (strip y₁ y₂) :=
  (isOpen_lt continuous_const continuous_im).inter (isOpen_lt continuous_im continuous_const)

theorem isPreconnected_strip (y₁ y₂ : ℝ) : IsPreconnected (strip y₁ y₂) := by
  refine (Convex.isPreconnected ?_)
  intro z hz w hw a c ha hc hac
  simp only [strip, mem_setOf_eq] at *
  simp only [add_im, smul_im, smul_eq_mul]
  constructor <;> nlinarith

variable {g}

/-- A uniform summable bound for the terms on a strip. -/
theorem norm_sterm_le (hg : PolyGrowth g) (α : ℝ) (j k : ℕ) (b : Bool) {y₁ y₂ : ℝ}
    (hy₁ : 0 < y₁) :
    ∃ u : ℕ → ℝ, Summable u ∧ ∀ n, ∀ z : ℂ, y₁ ≤ z.im → z.im ≤ y₂ → ‖sterm g α j k b n z‖ ≤ u n := by
  obtain ⟨C, hC, A, hA⟩ := hg
  set M : ℝ := (y₁ ^ α + y₂ ^ α) * (Real.exp (2 * Real.pi * y₁) * kMoment j (2 * Real.pi * y₁))
    with hM
  have hc : 0 < 2 * Real.pi * y₁ := by positivity
  refine ⟨fun n => C * 2 ^ A * |M| * (((n + 1 : ℕ) : ℝ) ^ (A + k) *
      Real.exp (-(2 * Real.pi * y₁) * ((n + 1 : ℕ) : ℝ))),
    ((summable_pow_mul_exp_neg (A + k) hc).mul_left (C * 2 ^ A * |M|)), fun n z h₁ h₂ => ?_⟩
  have hb := bterm_abs_le (α := α) (j := j) (k := k) (b := b) (Nat.succ_le_succ (Nat.zero_le n))
    hy₁ h₁ h₂
  have hgn := hA (n + 1)
  unfold sterm
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hn1 : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  have hpos : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ k := by positivity
  calc ‖g (n + 1)‖ * |bterm α j k b (n + 1) z|
      ≤ (C * (((n + 1 : ℕ) : ℝ) + 1) ^ A) *
          (((n + 1 : ℕ) : ℝ) ^ k * (y₁ ^ α + y₂ ^ α) *
            (Real.exp (2 * Real.pi * y₁) * kMoment j (2 * Real.pi * y₁)) *
              Real.exp (-(2 * Real.pi * y₁) * ((n + 1 : ℕ) : ℝ))) := by
        refine mul_le_mul ?_ hb (abs_nonneg _) (by positivity)
        simpa [hn1] using hgn
    _ ≤ (C * (2 * ((n + 1 : ℕ) : ℝ)) ^ A) *
          (((n + 1 : ℕ) : ℝ) ^ k * |M| * Real.exp (-(2 * Real.pi * y₁) * ((n + 1 : ℕ) : ℝ))) := by
        have h1 : (((n + 1 : ℕ) : ℝ) + 1) ≤ 2 * ((n + 1 : ℕ) : ℝ) := by
          rw [hn1]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
        have hMle : (y₁ ^ α + y₂ ^ α) * (Real.exp (2 * Real.pi * y₁) * kMoment j (2 * Real.pi * y₁))
            ≤ |M| := le_abs_self _
        have : ((n + 1 : ℕ) : ℝ) ^ k * (y₁ ^ α + y₂ ^ α) *
            (Real.exp (2 * Real.pi * y₁) * kMoment j (2 * Real.pi * y₁)) ≤
            ((n + 1 : ℕ) : ℝ) ^ k * |M| := by
          rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hMle hpos
        gcongr
    _ = C * 2 ^ A * |M| * (((n + 1 : ℕ) : ℝ) ^ (A + k) *
          Real.exp (-(2 * Real.pi * y₁) * ((n + 1 : ℕ) : ℝ))) := by
        rw [mul_pow, pow_add]
        ring

end RHTower.MaassBesselSeries
