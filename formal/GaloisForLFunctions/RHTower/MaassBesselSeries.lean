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
  · have h : trigFun false = Real.cos := by funext t; simp [trigFun]
    rw [h]
    simpa [trigFun, trigSign] using Real.hasDerivAt_cos θ
  · have h : trigFun true = Real.sin := by funext t; simp [trigFun]
    rw [h]
    simpa [trigFun, trigSign] using Real.hasDerivAt_sin θ

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
  simp only [coordCLM_apply, btermDx, btermDy, bterm, Function.comp]
  simp
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
  have hy₂ : 0 < y₂ := lt_of_lt_of_le hy h₂
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

theorem isPreconnected_strip (y₁ y₂ : ℝ) : IsPreconnected (strip y₁ y₂) :=
  ((convex_halfSpace_im_gt y₁).inter (convex_halfSpace_im_lt y₂)).isPreconnected

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
  have hy₂ : 0 < y₂ := lt_of_lt_of_le hy₁ (h₁.trans h₂)
  have hK0 := kMoment_nonneg j (2 * Real.pi * y₁)
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

/-- The summable strip bound in real form: `‖g_{n+1}‖ |term_{n+1}| ≤ u_n`. -/
theorem exists_summable_bterm_bound (hg : PolyGrowth g) (α : ℝ) (j k : ℕ) (b : Bool) {y₁ y₂ : ℝ}
    (hy₁ : 0 < y₁) :
    ∃ u : ℕ → ℝ, Summable u ∧ ∀ n, ∀ z : ℂ, y₁ ≤ z.im → z.im ≤ y₂ →
      ‖g (n + 1)‖ * |bterm α j k b (n + 1) z| ≤ u n := by
  obtain ⟨u, hu, hbd⟩ := norm_sterm_le (g := g) hg α j k b (y₂ := y₂) hy₁
  refine ⟨u, hu, fun n z h₁ h₂ => ?_⟩
  have := hbd n z h₁ h₂
  unfold sterm at this
  rwa [norm_mul, Complex.norm_real, Real.norm_eq_abs] at this

/-- `v ↦ Re v` and `v ↦ Im v` as real-linear maps `ℂ → ℂ`. -/
def reL : ℂ →L[ℝ] ℂ := ofRealCLM.comp reCLM

/-- `v ↦ Im v` as a real-linear map `ℂ → ℂ`. -/
def imL : ℂ →L[ℝ] ℂ := ofRealCLM.comp imCLM

@[simp] theorem reL_apply (v : ℂ) : reL v = (v.re : ℂ) := rfl
@[simp] theorem imL_apply (v : ℂ) : imL v = (v.im : ℂ) := rfl

theorem norm_reL_le : ‖reL‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by
    simp [Complex.norm_real, Complex.abs_re_le_norm]

theorem norm_imL_le : ‖imL‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by
    simp [Complex.norm_real, Complex.abs_im_le_norm]

/-- The term derivative `g_{n+1}(∂ₓ term · Re + ∂ᵧ term · Im)`. -/
def stermD (α : ℝ) (j k : ℕ) (b : Bool) (n : ℕ) (z : ℂ) : ℂ →L[ℝ] ℂ :=
  (g (n + 1) * (btermDx α j k b (n + 1) z : ℂ)) • reL +
    (g (n + 1) * (btermDy α j k b (n + 1) z : ℂ)) • imL

theorem hasFDerivAt_sterm (α : ℝ) (j k : ℕ) (b : Bool) (n : ℕ) {z : ℂ} (hz : 0 < z.im) :
    HasFDerivAt (sterm g α j k b n) (stermD (g := g) α j k b n z) z := by
  have hb := hasFDerivAt_bterm α j k b (Nat.succ_le_succ (Nat.zero_le n)) hz
  have h := (ofRealCLM.hasFDerivAt.comp z hb).const_mul (g (n + 1))
  refine h.congr_fderiv ?_
  ext v
  simp [stermD, coordCLM_apply]
  ring

theorem norm_stermD_le (α : ℝ) (j k : ℕ) (b : Bool) (n : ℕ) (z : ℂ) :
    ‖stermD (g := g) α j k b n z‖ ≤
      ‖g (n + 1)‖ * |btermDx α j k b (n + 1) z| + ‖g (n + 1)‖ * |btermDy α j k b (n + 1) z| := by
  unfold stermD
  refine (norm_add_le _ _).trans ?_
  gcongr
  · rw [norm_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc ‖g (n + 1)‖ * |btermDx α j k b (n + 1) z| * ‖reL‖
        ≤ ‖g (n + 1)‖ * |btermDx α j k b (n + 1) z| * 1 := by gcongr; exact norm_reL_le
      _ = _ := mul_one _
  · rw [norm_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc ‖g (n + 1)‖ * |btermDy α j k b (n + 1) z| * ‖imL‖
        ≤ ‖g (n + 1)‖ * |btermDy α j k b (n + 1) z| * 1 := by gcongr; exact norm_imL_le
      _ = _ := mul_one _

theorem exists_summable_stermD_bound (hg : PolyGrowth g) (α : ℝ) (j k : ℕ) (b : Bool) {y₁ y₂ : ℝ}
    (hy₁ : 0 < y₁) :
    ∃ u : ℕ → ℝ, Summable u ∧ ∀ n, ∀ z : ℂ, y₁ ≤ z.im → z.im ≤ y₂ →
      ‖stermD (g := g) α j k b n z‖ ≤ u n := by
  obtain ⟨u₁, hu₁, h₁⟩ := exists_summable_bterm_bound (g := g) hg α j (k + 1) (!b) (y₂ := y₂) hy₁
  obtain ⟨u₂, hu₂, h₂⟩ := exists_summable_bterm_bound (g := g) hg (α - 1) j k b (y₂ := y₂) hy₁
  obtain ⟨u₃, hu₃, h₃⟩ := exists_summable_bterm_bound (g := g) hg α (j + 1) (k + 1) b (y₂ := y₂) hy₁
  refine ⟨fun n => 2 * Real.pi * u₁ n + (|α| * u₂ n + 2 * Real.pi * u₃ n),
    ((hu₁.mul_left _).add ((hu₂.mul_left _).add (hu₃.mul_left _))), fun n z hz₁ hz₂ => ?_⟩
  refine (norm_stermD_le (g := g) α j k b n z).trans ?_
  have hx : ‖g (n + 1)‖ * |btermDx α j k b (n + 1) z| ≤ 2 * Real.pi * u₁ n := by
    unfold btermDx
    have hs : |trigSign b| = 1 := by cases b <;> simp [trigSign]
    rw [abs_mul, abs_mul, abs_mul, hs, abs_of_pos (by positivity : (0 : ℝ) < 2),
      abs_of_pos Real.pi_pos]
    have := h₁ n z hz₁ hz₂
    nlinarith [Real.pi_pos, norm_nonneg (g (n + 1))]
  have hy : ‖g (n + 1)‖ * |btermDy α j k b (n + 1) z| ≤ |α| * u₂ n + 2 * Real.pi * u₃ n := by
    unfold btermDy
    have ha := h₂ n z hz₁ hz₂
    have hb := h₃ n z hz₁ hz₂
    have htri : |α * bterm (α - 1) j k b (n + 1) z - 2 * Real.pi * bterm α (j + 1) (k + 1) b (n + 1) z|
        ≤ |α| * |bterm (α - 1) j k b (n + 1) z| + 2 * Real.pi * |bterm α (j + 1) (k + 1) b (n + 1) z| := by
      refine (abs_sub _ _).trans ?_
      rw [abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
    calc ‖g (n + 1)‖ * |α * bterm (α - 1) j k b (n + 1) z -
          2 * Real.pi * bterm α (j + 1) (k + 1) b (n + 1) z|
        ≤ ‖g (n + 1)‖ * (|α| * |bterm (α - 1) j k b (n + 1) z| +
          2 * Real.pi * |bterm α (j + 1) (k + 1) b (n + 1) z|) :=
          mul_le_mul_of_nonneg_left htri (norm_nonneg _)
      _ = |α| * (‖g (n + 1)‖ * |bterm (α - 1) j k b (n + 1) z|) +
          2 * Real.pi * (‖g (n + 1)‖ * |bterm α (j + 1) (k + 1) b (n + 1) z|) := by ring
      _ ≤ _ := by gcongr
  linarith

theorem summable_sterm (hg : PolyGrowth g) (α : ℝ) (j k : ℕ) (b : Bool) {z : ℂ} (hz : 0 < z.im) :
    Summable fun n => sterm g α j k b n z := by
  obtain ⟨u, hu, hbd⟩ := norm_sterm_le (g := g) hg α j k b (y₂ := z.im) hz
  exact hu.of_norm_bounded (fun n => hbd n z le_rfl le_rfl)

theorem mem_strip_half_double {z : ℂ} (hz : 0 < z.im) : z ∈ strip (z.im / 2) (2 * z.im) := by
  constructor <;> linarith

/-- The Bessel series is real-differentiable on the upper half-plane, with derivative the series of
termwise derivatives. -/
theorem hasFDerivAt_besselSeries_tsum (hg : PolyGrowth g) (α : ℝ) (j k : ℕ) (b : Bool) {z : ℂ}
    (hz : 0 < z.im) :
    HasFDerivAt (besselSeries g α j k b) (∑' n, stermD (g := g) α j k b n z) z := by
  have hy₁ : 0 < z.im / 2 := by positivity
  obtain ⟨u, hu, hbd⟩ := exists_summable_stermD_bound (g := g) hg α j k b (y₂ := 2 * z.im) hy₁
  exact hasFDerivAt_tsum_of_isPreconnected hu (isOpen_strip _ _) (isPreconnected_strip _ _)
    (fun n w hw => hasFDerivAt_sterm α j k b n (lt_trans hy₁ hw.1))
    (fun n w hw => hbd n w hw.1.le hw.2.le) (mem_strip_half_double hz)
    (summable_sterm hg α j k b hz) (mem_strip_half_double hz)

/-- The `x`-derivative series `2π sgn(b) S_{α,j,k+1,b̄}`. -/
def seriesDx (α : ℝ) (j k : ℕ) (b : Bool) (z : ℂ) : ℂ :=
  (2 * Real.pi * trigSign b : ℝ) * besselSeries g α j (k + 1) (!b) z

/-- The `y`-derivative series `α S_{α−1,j,k,b} − 2π S_{α,j+1,k+1,b}`. -/
def seriesDy (α : ℝ) (j k : ℕ) (b : Bool) (z : ℂ) : ℂ :=
  (α : ℂ) * besselSeries g (α - 1) j k b z - (2 * Real.pi : ℝ) * besselSeries g α (j + 1) (k + 1) b z

/-- **Termwise differentiation.**  `D S_{α,j,k,b}(z) = ∂ₓS · Re + ∂ᵧS · Im`. -/
theorem hasFDerivAt_besselSeries (hg : PolyGrowth g) (α : ℝ) (j k : ℕ) (b : Bool) {z : ℂ}
    (hz : 0 < z.im) :
    HasFDerivAt (besselSeries g α j k b)
      (seriesDx (g := g) α j k b z • reL + seriesDy (g := g) α j k b z • imL) z := by
  refine (hasFDerivAt_besselSeries_tsum hg α j k b hz).congr_fderiv ?_
  have hsx : Summable fun n => g (n + 1) * (btermDx α j k b (n + 1) z : ℂ) := by
    have := (summable_sterm hg α j (k + 1) (!b) hz).mul_left ((2 * Real.pi * trigSign b : ℝ) : ℂ)
    refine this.congr fun n => ?_
    simp only [sterm, btermDx]
    push_cast
    ring
  have hsy : Summable fun n => g (n + 1) * (btermDy α j k b (n + 1) z : ℂ) := by
    have := ((summable_sterm hg (α - 1) j k b hz).mul_left (α : ℂ)).sub
      ((summable_sterm hg α (j + 1) (k + 1) b hz).mul_left ((2 * Real.pi : ℝ) : ℂ))
    refine this.congr fun n => ?_
    simp only [sterm, btermDy]
    push_cast
    ring
  have hx : ∑' n, g (n + 1) * (btermDx α j k b (n + 1) z : ℂ) = seriesDx (g := g) α j k b z := by
    rw [seriesDx, besselSeries, ← tsum_mul_left]
    congr 1
    funext n
    simp only [sterm, btermDx]
    push_cast
    ring
  have hy : ∑' n, g (n + 1) * (btermDy α j k b (n + 1) z : ℂ) = seriesDy (g := g) α j k b z := by
    rw [seriesDy, besselSeries, besselSeries, ← tsum_mul_left, ← tsum_mul_left,
      ← Summable.tsum_sub ((summable_sterm hg (α - 1) j k b hz).mul_left _)
        ((summable_sterm hg α (j + 1) (k + 1) b hz).mul_left _)]
    congr 1
    funext n
    simp only [sterm, btermDy]
    push_cast
    ring
  unfold stermD
  rw [Summable.tsum_add (hsx.smul_const reL) (hsy.smul_const imL), hsx.tsum_smul_const,
    hsy.tsum_smul_const, hx, hy]

/-! ## The span of the Bessel series -/

/-- The four parameters `(α, j, k, b)` of a Bessel series. -/
abbrev Param := ℝ × ℕ × ℕ × Bool

/-- The Bessel series with parameters `p`. -/
def seriesOf (g : ℕ → ℂ) (p : Param) : ℂ → ℂ := besselSeries g p.1 p.2.1 p.2.2.1 p.2.2.2

/-- The complex span of all Bessel series. -/
def besselSpan (g : ℕ → ℂ) : Submodule ℂ (ℂ → ℂ) := Submodule.span ℂ (Set.range (seriesOf g))

theorem seriesOf_mem (g : ℕ → ℂ) (p : Param) : seriesOf g p ∈ besselSpan g :=
  Submodule.subset_span ⟨p, rfl⟩

/-- **The span is closed under `∂ₓ` and `∂ᵧ`.** -/
theorem exists_derivs_of_mem (hg : PolyGrowth g) {f : ℂ → ℂ} (hf : f ∈ besselSpan g) :
    ∃ fx ∈ besselSpan g, ∃ fy ∈ besselSpan g, ∀ z : ℂ, 0 < z.im →
      HasFDerivAt f (fx z • reL + fy z • imL) z := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨⟨α, j, k, b⟩, rfl⟩ := hx
      refine ⟨fun z => seriesDx (g := g) α j k b z, ?_, fun z => seriesDy (g := g) α j k b z, ?_,
        fun z hz => hasFDerivAt_besselSeries hg α j k b hz⟩
      · have : (fun z => seriesDx (g := g) α j k b z) =
            (((2 * Real.pi * trigSign b : ℝ) : ℂ)) • seriesOf g (α, j, k + 1, !b) := by
          funext z; simp [seriesDx, seriesOf]
        rw [this]
        exact Submodule.smul_mem _ _ (seriesOf_mem g _)
      · have : (fun z => seriesDy (g := g) α j k b z) =
            (α : ℂ) • seriesOf g (α - 1, j, k, b) -
              ((2 * Real.pi : ℝ) : ℂ) • seriesOf g (α, j + 1, k + 1, b) := by
          funext z; simp [seriesDy, seriesOf]
        rw [this]
        exact Submodule.sub_mem _ (Submodule.smul_mem _ _ (seriesOf_mem g _))
          (Submodule.smul_mem _ _ (seriesOf_mem g _))
  | zero =>
      refine ⟨0, Submodule.zero_mem _, 0, Submodule.zero_mem _, fun z _ => ?_⟩
      have h0 : (0 : ℂ → ℂ) z • reL + (0 : ℂ → ℂ) z • imL = 0 := by
        ext v; simp
      rw [h0]
      exact hasFDerivAt_const (𝕜 := ℝ) (0 : ℂ) z
  | add x y _ _ hx hy =>
      obtain ⟨fx, hfx, fy, hfy, h⟩ := hx
      obtain ⟨gx, hgx, gy, hgy, h'⟩ := hy
      refine ⟨fx + gx, Submodule.add_mem _ hfx hgx, fy + gy, Submodule.add_mem _ hfy hgy,
        fun z hz => ?_⟩
      refine ((h z hz).add (h' z hz)).congr_fderiv ?_
      ext v
      simp
      ring
  | smul a x _ hx =>
      obtain ⟨fx, hfx, fy, hfy, h⟩ := hx
      refine ⟨a • fx, Submodule.smul_mem _ a hfx, a • fy, Submodule.smul_mem _ a hfy,
        fun z hz => ?_⟩
      refine ((h z hz).const_smul a).congr_fderiv ?_
      ext v
      simp
      ring

/-- **Every member of the span is `C^∞` on the upper half-plane.** -/
theorem contDiffOn_of_mem_besselSpan (hg : PolyGrowth g) {f : ℂ → ℂ} (hf : f ∈ besselSpan g) :
    ContDiffOn ℝ ∞ f upper := by
  rw [contDiffOn_infty]
  intro m
  induction m generalizing f with
  | zero =>
      obtain ⟨fx, -, fy, -, h⟩ := exists_derivs_of_mem hg hf
      exact contDiffOn_zero.mpr fun z hz => (h z hz).continuousAt.continuousWithinAt
  | succ m ih =>
      obtain ⟨fx, hfx, fy, hfy, h⟩ := exists_derivs_of_mem hg hf
      rw [show ((m + 1 : ℕ) : WithTop ℕ∞) = (m : WithTop ℕ∞) + 1 by push_cast; rfl,
        contDiffOn_succ_iff_fderiv_of_isOpen isOpen_upper]
      refine ⟨fun z hz => (h z hz).differentiableAt.differentiableWithinAt, by simp, ?_⟩
      have hcd : ContDiffOn ℝ m (fun z => fx z • reL + fy z • imL) upper :=
        ((ih hfx).smul contDiffOn_const).add ((ih hfy).smul contDiffOn_const)
      exact hcd.congr fun z hz => (h z hz).fderiv

end RHTower.MaassBesselSeries
