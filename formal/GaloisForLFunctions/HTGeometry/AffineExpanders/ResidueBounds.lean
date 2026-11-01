/-
Pointwise residue estimates adapted from girving/aks, AKS/MGG/Young.lean,
revision c7fb62ed80a4a610f87f34db0082cadbd7c00c9f, Apache-2.0.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic

/-!
# Reciprocal weights for the affine shear estimate

Natural representatives allow the distance comparisons to reduce to linear arithmetic.
Inside the central diamond, neighbor distances control the four weights directly.
Outside, a cosine-square bound and a pair-weight-square bound give the same estimate.
-/

set_option autoImplicit false
namespace GaloisForLFunctions.HTGeometry.MGGResidueBounds
open BigOperators Finset Real
open scoped Real

/-- Distance to 0 in `Z/nZ`: `zmodDist n x = min(x, n - x)`. -/
def zmodDist (n x : ℕ) : ℕ := min x (n - x)

/-- `zmodDist n x ≤ n / 2` for `x < n`. -/
theorem zmodDist_le_half (n x : ℕ) (hx : x < n) : zmodDist n x ≤ n / 2 := by
  unfold zmodDist; omega

/-- Fourier-domain shear S₁: `(α₁, α₂) ↦ (α₁ - 2α₂ mod n, α₂)`.
    Preserves `α₂`. -/
def shearS1 (n α₁ α₂ : ℕ) : ℕ × ℕ := ((α₁ + n - (2 * α₂) % n) % n, α₂)

/-- Fourier-domain shear S₂: `(α₁, α₂) ↦ (α₁, α₂ - 2α₁ mod n)`.
    Preserves `α₁`. -/
def shearS2 (n α₁ α₂ : ℕ) : ℕ × ℕ := (α₁, (α₂ + n - (2 * α₁) % n) % n)

/-- Inverse Fourier-domain shear S₁⁻¹: `(α₁, α₂) ↦ (α₁ + 2α₂ mod n, α₂)`.
    Preserves `α₂`. Satisfies `S₁(S₁⁻¹(α)) = α` and `S₁⁻¹(S₁(α)) = α`. -/
def shearS1Inv (n α₁ α₂ : ℕ) : ℕ × ℕ := ((α₁ + (2 * α₂) % n) % n, α₂)

/-- Inverse Fourier-domain shear S₂⁻¹: `(α₁, α₂) ↦ (α₁, α₂ + 2α₁ mod n)`.
    Preserves `α₁`. Satisfies `S₂(S₂⁻¹(α)) = α` and `S₂⁻¹(S₂(α)) = α`. -/
def shearS2Inv (n α₁ α₂ : ℕ) : ℕ × ℕ := (α₁, (α₂ + (2 * α₁) % n) % n)

/-- Partial order on `(Z/nZ)²` by distance to axes: `α ≻ β` iff
    `zmodDist n α₁ ≥ zmodDist n β₁` and `zmodDist n α₂ ≥ zmodDist n β₂`
    with at least one strict inequality (α is "farther from axes"). -/
def zmodDistGt (n α₁ α₂ β₁ β₂ : ℕ) : Bool :=
  zmodDist n β₁ ≤ zmodDist n α₁ && zmodDist n β₂ ≤ zmodDist n α₂ &&
  (zmodDist n β₁ < zmodDist n α₁ || zmodDist n β₂ < zmodDist n α₂)

/-- Weight function ψ with parameter `α = √2`:
    - `√2` if α > β (α farther from axes → BIG weight)
    - `√2/2` if α < β (α closer → SMALL weight)
    - `1` if incomparable
    Product property: `ψ(α,β) · ψ(β,α) = 1`. -/
noncomputable def psiWeight (n α₁ α₂ β₁ β₂ : ℕ) : ℝ :=
  if zmodDistGt n α₁ α₂ β₁ β₂ = true then √2
  else if zmodDistGt n β₁ β₂ α₁ α₂ = true then √2 / 2
  else 1

/-- `zmodDistGt` is antisymmetric. -/
lemma zmodDistGt_antisymm (n α₁ α₂ β₁ β₂ : ℕ) :
    zmodDistGt n α₁ α₂ β₁ β₂ = true → zmodDistGt n β₁ β₂ α₁ α₂ = false := by
  unfold zmodDistGt
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
    decide_eq_false_iff_not, Bool.and_eq_false_iff, Bool.or_eq_false_iff, not_le, not_lt]
  omega

/-- The weight function satisfies `ψ(α,β) · ψ(β,α) = 1`. -/
theorem psiWeight_mul_comm (n α₁ α₂ β₁ β₂ : ℕ) :
    psiWeight n α₁ α₂ β₁ β₂ * psiWeight n β₁ β₂ α₁ α₂ = 1 := by
  have hsq : √2 * √2 = 2 := mul_self_sqrt (by norm_num)
  unfold psiWeight
  by_cases h1 : zmodDistGt n α₁ α₂ β₁ β₂ = true
  · rw [if_pos h1, if_neg (by simp [zmodDistGt_antisymm n α₁ α₂ β₁ β₂ h1]),
      if_pos h1]; nlinarith [sqrt_pos.mpr (show (0:ℝ) < 2 by norm_num)]
  · rw [if_neg h1]
    by_cases h2 : zmodDistGt n β₁ β₂ α₁ α₂ = true
    · rw [if_pos h2, if_pos h2]
      nlinarith [sqrt_pos.mpr (show (0:ℝ) < 2 by norm_num)]
    · rw [if_neg h2, if_neg h1, if_neg h2]; ring

/-- Each ψ value is positive. -/
theorem psiWeight_pos (n α₁ α₂ β₁ β₂ : ℕ) : 0 < psiWeight n α₁ α₂ β₁ β₂ := by
  unfold psiWeight; split <;> [positivity; split <;> positivity]

/-- The pointwise condition (*) for a single frequency α ≠ 0.
    After DFT + Young's inequality, the sufficient condition pairs each cosine
    with the shear that **preserves** that coordinate:
    - `|cos(πα₁/n)|` pairs with `S₂, S₂⁻¹` (which preserve `α₁`)
    - `|cos(πα₂/n)|` pairs with `S₁, S₁⁻¹` (which preserve `α₂`)

    This is because the substitution `α' = S_i α` in Young's inequality
    requires the cosine factor to be invariant under `S_i`. -/
def pointwiseCondition (n α₁ α₂ : ℕ) : Prop :=
  let s1 := shearS1 n α₁ α₂        -- S₁α (preserves α₂)
  let s1i := shearS1Inv n α₁ α₂    -- S₁⁻¹α (preserves α₂)
  let s2 := shearS2 n α₁ α₂        -- S₂α (preserves α₁)
  let s2i := shearS2Inv n α₁ α₂    -- S₂⁻¹α (preserves α₁)
  -- cos₁ with S₂ (preserves α₁), cos₂ with S₁ (preserves α₂)
  |cos (π * α₁ / n)| * (psiWeight n α₁ α₂ s2.1 s2.2 + psiWeight n α₁ α₂ s2i.1 s2i.2) +
  |cos (π * α₂ / n)| * (psiWeight n α₁ α₂ s1.1 s1.2 + psiWeight n α₁ α₂ s1i.1 s1i.2)
    ≤ 5 * √2 / 2

/-- `|cos(πa/n)| = cos(π · zmodDist(n,a) / n)` for `a < n`. -/
lemma abs_cos_eq_cos_zmodDist (n a : ℕ) (ha : a < n) (hn : 0 < n) :
    |cos (π * ↑a / ↑n)| = cos (π * ↑(zmodDist n a) / ↑n) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hpi := pi_pos
  unfold zmodDist
  by_cases h : a ≤ n - a
  · rw [min_eq_left h, abs_of_nonneg]
    apply cos_nonneg_of_mem_Icc
    constructor
    · linarith [div_nonneg (mul_nonneg hpi.le (Nat.cast_nonneg (α := ℝ) a)) hn'.le]
    · have : 2 * (a : ℝ) ≤ n := by
        have := Nat.cast_le (α := ℝ).mpr h; rw [Nat.cast_sub ha.le] at this; linarith
      rw [div_le_div_iff₀ hn' two_pos]; nlinarith
  · push Not at h
    rw [min_eq_right h.le, show π * (↑(n - a) : ℝ) / ↑n = π - π * ↑a / ↑n from by
      rw [Nat.cast_sub ha.le]; field_simp]
    rw [cos_pi_sub, abs_of_nonpos]
    apply cos_nonpos_of_pi_div_two_le_of_le
    · have : (n : ℝ) < 2 * a := by
        have := Nat.cast_lt (α := ℝ).mpr h; rw [Nat.cast_sub ha.le] at this; linarith
      rw [le_div_iff₀ hn']; nlinarith
    · rw [div_le_iff₀ hn']; nlinarith [Nat.cast_lt (α := ℝ).mpr ha]

/-- `cos y ≤ sin x` when `x + y > π/2` and `x, y ∈ [0, π/2]`.
    Follows from strict antitonicity of `cos` on `[0, π]`. -/
lemma cos_le_sin_of_sum_gt (x y : ℝ)
    (hx' : x ≤ π / 2) (hy' : y ≤ π / 2)
    (hsum : π / 2 < x + y) :
    cos y ≤ sin x := by
  have hpi := pi_pos
  calc cos y
      ≤ cos (π / 2 - x) :=
        cos_le_cos_of_nonneg_of_le_pi (by linarith) (by linarith) (by linarith)
    _ = sin x := cos_pi_div_two_sub x

/-- Cauchy-Schwarz inequality for two components:
    `a₁b₁ + a₂b₂ ≤ √(a₁²+a₂²) · √(b₁²+b₂²)` when all terms are non-negative. -/
lemma cauchy_schwarz_two (a₁ a₂ b₁ b₂ : ℝ) (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂)
    (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂) :
    a₁ * b₁ + a₂ * b₂ ≤ √(a₁ ^ 2 + a₂ ^ 2) * √(b₁ ^ 2 + b₂ ^ 2) := by
  have h : 0 ≤ a₁ * b₁ + a₂ * b₂ := by positivity
  rw [← Real.sqrt_mul (by positivity : 0 ≤ a₁ ^ 2 + a₂ ^ 2)]
  rw [Real.le_sqrt h (by positivity)]
  nlinarith [sq_nonneg (a₁ * b₂ - a₂ * b₁)]

/-- Outside the diamond, `cos²(πα₁/n) + cos²(πα₂/n) ≤ 1`.
    Follows from `cos(πd₂/n) ≤ sin(πd₁/n)` when `d₁ + d₂ > n/2`. -/
lemma cos_sq_sum_le_one (n α₁ α₂ : ℕ) (hn : 0 < n)
    (hα₁ : α₁ < n) (hα₂ : α₂ < n)
    (hout : n / 2 < zmodDist n α₁ + zmodDist n α₂) :
    |cos (π * α₁ / n)| ^ 2 + |cos (π * α₂ / n)| ^ 2 ≤ 1 := by
  -- Rewrite |cos| to cos of zmodDist
  rw [abs_cos_eq_cos_zmodDist n α₁ hα₁ hn, abs_cos_eq_cos_zmodDist n α₂ hα₂ hn]
  set d₁ := zmodDist n α₁; set d₂ := zmodDist n α₂
  -- Use cos_sum_le_sqrt2 gives cos d₁ + cos d₂ ≤ √2
  -- More specifically: cos d₂ ≤ sin d₁ (from d₁ + d₂ > n/2 → θ₁ + θ₂ > π/2)
  -- Then cos²d₁ + cos²d₂ ≤ cos²d₁ + sin²d₁ = 1
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hpi := pi_pos
  have hd₁_le : d₁ ≤ n / 2 := zmodDist_le_half n α₁ hα₁
  have hd₂_le : d₂ ≤ n / 2 := zmodDist_le_half n α₂ hα₂
  have hd_gt : n < 2 * (d₁ + d₂) := by omega
  have hd₁_2 : 2 * d₁ ≤ n := by omega
  have hd₂_2 : 2 * d₂ ≤ n := by omega
  have hd₁_r : 2 * (d₁ : ℝ) ≤ n := by exact_mod_cast hd₁_2
  have hd₂_r : 2 * (d₂ : ℝ) ≤ n := by exact_mod_cast hd₂_2
  have hd_gt_r : (n : ℝ) < 2 * ((d₁ : ℝ) + d₂) := by exact_mod_cast hd_gt
  -- θ₁ = πd₁/n, θ₂ = πd₂/n
  set θ₁ := π * (d₁ : ℝ) / n; set θ₂ := π * (d₂ : ℝ) / n
  have hθ₁_nn : 0 ≤ θ₁ := by positivity
  have hθ₂_nn : 0 ≤ θ₂ := by positivity
  have hθ₁_le : θ₁ ≤ π / 2 := by
    show π * ↑d₁ / ↑n ≤ π / 2
    rw [div_le_div_iff₀ hn' (by norm_num : (0:ℝ) < 2)]; nlinarith
  have hθ₂_le : θ₂ ≤ π / 2 := by
    show π * ↑d₂ / ↑n ≤ π / 2
    rw [div_le_div_iff₀ hn' (by norm_num : (0:ℝ) < 2)]; nlinarith
  have hθ_sum : π / 2 < θ₁ + θ₂ := by
    show π / 2 < π * ↑d₁ / ↑n + π * ↑d₂ / ↑n
    rw [show π * ↑d₁ / ↑n + π * ↑d₂ / ↑n = π * (↑d₁ + ↑d₂) / ↑n from by ring]
    rw [lt_div_iff₀ hn']; nlinarith
  have hcos₂_le : cos θ₂ ≤ sin θ₁ := cos_le_sin_of_sum_gt θ₁ θ₂ hθ₁_le hθ₂_le hθ_sum
  have hcos₂_nn : 0 ≤ cos θ₂ := cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
  nlinarith [sq_le_sq' (by linarith : -sin θ₁ ≤ cos θ₂) hcos₂_le, sin_sq_add_cos_sq θ₁]

/-- `psiWeight` is at most `√2`. -/
lemma psiWeight_le_sqrt2 (n α₁ α₂ β₁ β₂ : ℕ) : psiWeight n α₁ α₂ β₁ β₂ ≤ √2 := by
  have hsq : (√2 : ℝ) ^ 2 = 2 := sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  have hpos : (0:ℝ) < √2 := sqrt_pos.mpr (by norm_num)
  unfold psiWeight; split <;> [linarith; split]
  · linarith
  · nlinarith [sq_nonneg (√2 - 1)]

/-- `psiWeight` is at most `1` when `α` is NOT farther from axes than `β`. -/
lemma psiWeight_le_one_of_not_gt (n α₁ α₂ β₁ β₂ : ℕ)
    (h : zmodDistGt n α₁ α₂ β₁ β₂ = false) : psiWeight n α₁ α₂ β₁ β₂ ≤ 1 := by
  have hsq : (√2 : ℝ) ^ 2 = 2 := sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  unfold psiWeight
  rw [if_neg (Bool.eq_false_iff.mp h)]
  split
  · nlinarith [sq_nonneg (√2 - 2)]
  · linarith

/-- `psiWeight` equals `√2` when `α` IS farther from axes than `β`. -/
lemma psiWeight_eq_sqrt2_of_gt (n α₁ α₂ β₁ β₂ : ℕ)
    (h : zmodDistGt n α₁ α₂ β₁ β₂ = true) : psiWeight n α₁ α₂ β₁ β₂ = √2 := by
  unfold psiWeight; rw [if_pos h]

/-- `psiWeight` equals `√2/2` when `β` IS farther from axes than `α`. -/
lemma psiWeight_eq_sqrt2_div2_of_rev_gt (n α₁ α₂ β₁ β₂ : ℕ)
    (h1 : zmodDistGt n α₁ α₂ β₁ β₂ = false)
    (h2 : zmodDistGt n β₁ β₂ α₁ α₂ = true) : psiWeight n α₁ α₂ β₁ β₂ = √2 / 2 := by
  unfold psiWeight; rw [if_neg (Bool.eq_false_iff.mp h1), if_pos h2]

/-- When S₂ preserves the first coordinate (`s2.1 = α₁`), `zmodDistGt` reduces to
    comparing the second coordinate distances. -/
lemma zmodDistGt_of_fst_eq (n α₁ α₂ β₂ : ℕ) :
    zmodDistGt n α₁ α₂ α₁ β₂ = decide (zmodDist n β₂ < zmodDist n α₂) := by
  unfold zmodDistGt
  simp only [le_refl, lt_irrefl, decide_true, decide_false, Bool.true_and, Bool.false_or]
  cases Nat.decLt (zmodDist n β₂) (zmodDist n α₂) with
  | isTrue h => simp [h, h.le]
  | isFalse h => simp [h]

/-- When S₁ preserves the second coordinate (`s1.2 = α₂`), `zmodDistGt` reduces to
    comparing the first coordinate distances. -/
lemma zmodDistGt_of_snd_eq (n α₁ α₂ β₁ : ℕ) :
    zmodDistGt n α₁ α₂ β₁ α₂ = decide (zmodDist n β₁ < zmodDist n α₁) := by
  unfold zmodDistGt
  simp only [le_refl, lt_irrefl, decide_true, decide_false, Bool.and_true, Bool.or_false]
  cases Nat.decLt (zmodDist n β₁) (zmodDist n α₁) with
  | isTrue h => simp [h, h.le]
  | isFalse h => simp [h]

/-- Shear S₂ preserves the first coordinate. -/
lemma shearS2_fst (n α₁ α₂ : ℕ) : (shearS2 n α₁ α₂).1 = α₁ := rfl

/-- Shear S₂⁻¹ preserves the first coordinate. -/
lemma shearS2Inv_fst (n α₁ α₂ : ℕ) : (shearS2Inv n α₁ α₂).1 = α₁ := rfl

/-- Shear S₁ preserves the second coordinate. -/
lemma shearS1_snd (n α₁ α₂ : ℕ) : (shearS1 n α₁ α₂).2 = α₂ := rfl

/-- Shear S₁⁻¹ preserves the second coordinate. -/
lemma shearS1Inv_snd (n α₁ α₂ : ℕ) : (shearS1Inv n α₁ α₂).2 = α₂ := rfl

/-- Eliminates outer `%` from `min ((a + n - δ) % n) (n - (a + n - δ) % n)`. -/
theorem zd_sub (n a δ : ℕ) (ha : a < n) (hδ : δ < n) :
    min ((a + n - δ) % n) (n - (a + n - δ) % n) =
    if a < δ then min (a + n - δ) (δ - a) else min (a - δ) (n - a + δ) := by
  by_cases h : a < δ
  · rw [if_pos h, Nat.mod_eq_of_lt (by omega)]; simp only [Nat.min_def]; split_ifs <;> omega
  · rw [if_neg h, show a + n - δ = (a - δ) + n from by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    simp only [Nat.min_def]; split_ifs <;> omega

/-- Eliminates outer `%` from `min ((a + δ) % n) (n - (a + δ) % n)`. -/
theorem zd_add (n a δ : ℕ) (ha : a < n) (hδ : δ < n) :
    min ((a + δ) % n) (n - (a + δ) % n) =
    if a + δ < n then min (a + δ) (n - a - δ) else min (a + δ - n) (2 * n - a - δ) := by
  by_cases h : a + δ < n
  · rw [if_pos h, Nat.mod_eq_of_lt h]; simp only [Nat.min_def]; split_ifs <;> omega
  · rw [if_neg h, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    simp only [Nat.min_def]; split_ifs <;> omega

/-- `zmodDist n (shearS2 n α₁ α₂).2` without outer `%`. -/
theorem zd_S2 (n α₁ α₂ : ℕ) (_ : α₁ < n) (h : α₂ < n) (hn : 0 < n) :
    zmodDist n (shearS2 n α₁ α₂).2 =
    if α₂ < (2*α₁)%n then min (α₂+n-(2*α₁)%n) ((2*α₁)%n-α₂)
    else min (α₂-(2*α₁)%n) (n-α₂+(2*α₁)%n) := by
  unfold zmodDist shearS2; simp only; exact zd_sub n α₂ _ h (Nat.mod_lt _ hn)

/-- `zmodDist n (shearS2Inv n α₁ α₂).2` without outer `%`. -/
theorem zd_S2I (n α₁ α₂ : ℕ) (_ : α₁ < n) (h : α₂ < n) (hn : 0 < n) :
    zmodDist n (shearS2Inv n α₁ α₂).2 =
    if α₂+(2*α₁)%n < n then min (α₂+(2*α₁)%n) (n-α₂-(2*α₁)%n)
    else min (α₂+(2*α₁)%n-n) (2*n-α₂-(2*α₁)%n) := by
  unfold zmodDist shearS2Inv; simp only; exact zd_add n α₂ _ h (Nat.mod_lt _ hn)

/-- `zmodDist n (shearS1 n α₁ α₂).1` without outer `%`. -/
theorem zd_S1 (n α₁ α₂ : ℕ) (h : α₁ < n) (_ : α₂ < n) (hn : 0 < n) :
    zmodDist n (shearS1 n α₁ α₂).1 =
    if α₁ < (2*α₂)%n then min (α₁+n-(2*α₂)%n) ((2*α₂)%n-α₁)
    else min (α₁-(2*α₂)%n) (n-α₁+(2*α₂)%n) := by
  unfold zmodDist shearS1; simp only; exact zd_sub n α₁ _ h (Nat.mod_lt _ hn)

/-- `zmodDist n (shearS1Inv n α₁ α₂).1` without outer `%`. -/
theorem zd_S1I (n α₁ α₂ : ℕ) (h : α₁ < n) (_ : α₂ < n) (hn : 0 < n) :
    zmodDist n (shearS1Inv n α₁ α₂).1 =
    if α₁+(2*α₂)%n < n then min (α₁+(2*α₂)%n) (n-α₁-(2*α₂)%n)
    else min (α₁+(2*α₂)%n-n) (2*n-α₁-(2*α₂)%n) := by
  unfold zmodDist shearS1Inv; simp only; exact zd_add n α₁ _ h (Nat.mod_lt _ hn)

/-- `(2 * α) % n = 2 * α` when `2α < n`. -/
theorem double_mod_lo (n α : ℕ) (h : 2 * α < n) : (2 * α) % n = 2 * α :=
  Nat.mod_eq_of_lt h

/-- `(2 * α) % n = 2 * α - n` when `2α ≥ n`. -/
theorem double_mod_hi (n α : ℕ) (hα : α < n) (h : ¬(2 * α < n)) :
    (2 * α) % n = 2 * α - n := by
  rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

/-- Cross-constraint forward: both S₂ closer ∧ S₁ closer ⟹ S₁⁻¹ strictly farther. -/
theorem cross_constraint_fwd (n α₁ α₂ : ℕ) (hn : 3 ≤ n) (hα₁ : α₁ < n) (hα₂ : α₂ < n)
    (hs2 : zmodDist n (shearS2 n α₁ α₂).2 < zmodDist n α₂)
    (hs2i : zmodDist n (shearS2Inv n α₁ α₂).2 < zmodDist n α₂)
    (hs1 : zmodDist n (shearS1 n α₁ α₂).1 < zmodDist n α₁) :
    zmodDist n α₁ < zmodDist n (shearS1Inv n α₁ α₂).1 := by
  rw [zd_S2 n α₁ α₂ hα₁ hα₂ (by omega)] at hs2
  rw [zd_S2I n α₁ α₂ hα₁ hα₂ (by omega)] at hs2i
  rw [zd_S1 n α₁ α₂ hα₁ hα₂ (by omega)] at hs1
  rw [zd_S1I n α₁ α₂ hα₁ hα₂ (by omega)]
  unfold zmodDist at hs2 hs2i hs1 ⊢
  by_cases h1 : 2 * α₁ < n <;> by_cases h2 : 2 * α₂ < n
  · simp only [double_mod_lo n α₁ h1, double_mod_lo n α₂ h2,
      Nat.min_eq_left (by omega : α₁ ≤ n - α₁),
      Nat.min_eq_left (by omega : α₂ ≤ n - α₂)] at hs2 hs2i hs1 ⊢
    simp only [Nat.min_def] at hs2 hs2i hs1 ⊢
    split_ifs at hs2 <;> (try omega) <;> split_ifs at hs2i <;> (try omega) <;>
      split_ifs at hs1 <;> omega
  · simp only [double_mod_lo n α₁ h1, double_mod_hi n α₂ hα₂ h2,
      Nat.min_eq_left (by omega : α₁ ≤ n - α₁),
      Nat.min_eq_right (by omega : n - α₂ ≤ α₂)] at hs2 hs2i hs1 ⊢
    simp only [Nat.min_def] at hs2 hs2i hs1 ⊢
    split_ifs at hs2 <;> (try omega) <;> split_ifs at hs2i <;> (try omega) <;>
      split_ifs at hs1 <;> (try omega) <;> split_ifs <;> omega
  · simp only [double_mod_hi n α₁ hα₁ h1, double_mod_lo n α₂ h2,
      Nat.min_eq_right (by omega : n - α₁ ≤ α₁),
      Nat.min_eq_left (by omega : α₂ ≤ n - α₂)] at hs2 hs2i hs1 ⊢
    simp only [Nat.min_def] at hs2 hs2i hs1 ⊢
    split_ifs at hs2 <;> (try omega) <;> split_ifs at hs2i <;> (try omega) <;>
      split_ifs at hs1 <;> (try omega) <;> split_ifs <;> omega
  · simp only [double_mod_hi n α₁ hα₁ h1, double_mod_hi n α₂ hα₂ h2,
      Nat.min_eq_right (by omega : n - α₁ ≤ α₁),
      Nat.min_eq_right (by omega : n - α₂ ≤ α₂)] at hs2 hs2i hs1 ⊢
    simp only [Nat.min_def] at hs2 hs2i hs1 ⊢
    split_ifs at hs2 <;> (try omega) <;> split_ifs at hs2i <;> (try omega) <;>
      split_ifs at hs1 <;> omega

/-- Cross-constraint reverse: both S₂ closer ∧ S₁⁻¹ closer ⟹ S₁ strictly farther. -/
theorem cross_constraint_rev (n α₁ α₂ : ℕ) (hn : 3 ≤ n) (hα₁ : α₁ < n) (hα₂ : α₂ < n)
    (hs2 : zmodDist n (shearS2 n α₁ α₂).2 < zmodDist n α₂)
    (hs2i : zmodDist n (shearS2Inv n α₁ α₂).2 < zmodDist n α₂)
    (hs1i : zmodDist n (shearS1Inv n α₁ α₂).1 < zmodDist n α₁) :
    zmodDist n α₁ < zmodDist n (shearS1 n α₁ α₂).1 := by
  rw [zd_S2 n α₁ α₂ hα₁ hα₂ (by omega)] at hs2
  rw [zd_S2I n α₁ α₂ hα₁ hα₂ (by omega)] at hs2i
  rw [zd_S1I n α₁ α₂ hα₁ hα₂ (by omega)] at hs1i
  rw [zd_S1 n α₁ α₂ hα₁ hα₂ (by omega)]
  unfold zmodDist at hs2 hs2i hs1i ⊢
  by_cases h1 : 2 * α₁ < n <;> by_cases h2 : 2 * α₂ < n
  · simp only [double_mod_lo n α₁ h1, double_mod_lo n α₂ h2,
      Nat.min_eq_left (by omega : α₁ ≤ n - α₁),
      Nat.min_eq_left (by omega : α₂ ≤ n - α₂)] at hs2 hs2i hs1i ⊢
    simp only [Nat.min_def] at hs2 hs2i hs1i ⊢
    split_ifs at hs2 <;> (try omega) <;> split_ifs at hs2i <;> (try omega) <;>
      split_ifs at hs1i <;> (try omega) <;> split_ifs <;> omega
  · simp only [double_mod_lo n α₁ h1, double_mod_hi n α₂ hα₂ h2,
      Nat.min_eq_left (by omega : α₁ ≤ n - α₁),
      Nat.min_eq_right (by omega : n - α₂ ≤ α₂)] at hs2 hs2i hs1i ⊢
    simp only [Nat.min_def] at hs2 hs2i hs1i ⊢
    split_ifs at hs2 <;> (try omega) <;> split_ifs at hs2i <;> (try omega) <;>
      split_ifs at hs1i <;> omega
  · simp only [double_mod_hi n α₁ hα₁ h1, double_mod_lo n α₂ h2,
      Nat.min_eq_right (by omega : n - α₁ ≤ α₁),
      Nat.min_eq_left (by omega : α₂ ≤ n - α₂)] at hs2 hs2i hs1i ⊢
    simp only [Nat.min_def] at hs2 hs2i hs1i ⊢
    split_ifs at hs2 <;> (try omega) <;> split_ifs at hs2i <;> (try omega) <;>
      split_ifs at hs1i <;> omega
  · simp only [double_mod_hi n α₁ hα₁ h1, double_mod_hi n α₂ hα₂ h2,
      Nat.min_eq_right (by omega : n - α₁ ≤ α₁),
      Nat.min_eq_right (by omega : n - α₂ ≤ α₂)] at hs2 hs2i hs1i ⊢
    simp only [Nat.min_def] at hs2 hs2i hs1i ⊢
    split_ifs at hs2 <;> (try omega) <;> split_ifs at hs2i <;> (try omega) <;>
      split_ifs at hs1i <;> (try omega) <;> split_ifs <;> omega

/-- When both S₂ neighbors are strictly closer, the S₁ pair sum is at most `3√2/2`.

    Proof: S₁ preserves `α₂`, so ψ for S₁ neighbors depends only on the first coordinate.
    By `cross_constraint_fwd`/`_rev`, at most one of `{S₁, S₁⁻¹}` can be closer:
    - If S₁ closer: S₁⁻¹ farther → pair₂ = `√2 + √2/2 = 3√2/2`.
    - If S₁⁻¹ closer: S₁ farther → pair₂ = `√2/2 + √2 = 3√2/2`.
    - If neither closer: each ψ ≤ 1 → pair₂ ≤ 2 ≤ 3√2/2. -/
theorem pair_bound_when_both_S2_closer (n α₁ α₂ : ℕ) (hn : 3 ≤ n)
    (hα₁ : α₁ < n) (hα₂ : α₂ < n)
    (h_s2 : zmodDist n (shearS2 n α₁ α₂).2 < zmodDist n α₂)
    (h_s2i : zmodDist n (shearS2Inv n α₁ α₂).2 < zmodDist n α₂) :
    psiWeight n α₁ α₂ (shearS1 n α₁ α₂).1 (shearS1 n α₁ α₂).2 +
    psiWeight n α₁ α₂ (shearS1Inv n α₁ α₂).1 (shearS1Inv n α₁ α₂).2
      ≤ 3 * √2 / 2 := by
  set s1 := shearS1 n α₁ α₂
  set s1i := shearS1Inv n α₁ α₂
  have hs1_snd : s1.2 = α₂ := shearS1_snd n α₁ α₂
  have hs1i_snd : s1i.2 = α₂ := shearS1Inv_snd n α₁ α₂
  have hgt_s1 : zmodDistGt n α₁ α₂ s1.1 s1.2 = decide (zmodDist n s1.1 < zmodDist n α₁) := by
    rw [hs1_snd]; exact zmodDistGt_of_snd_eq n α₁ α₂ s1.1
  have hgt_s1i : zmodDistGt n α₁ α₂ s1i.1 s1i.2 = decide (zmodDist n s1i.1 < zmodDist n α₁) := by
    rw [hs1i_snd]; exact zmodDistGt_of_snd_eq n α₁ α₂ s1i.1
  -- Also get the reverse direction zmodDistGt
  have hgt_s1_rev : zmodDistGt n s1.1 s1.2 α₁ α₂ = decide (zmodDist n α₁ < zmodDist n s1.1) := by
    rw [hs1_snd]; exact zmodDistGt_of_snd_eq n s1.1 α₂ α₁
  have hgt_s1i_rev : zmodDistGt n s1i.1 s1i.2 α₁ α₂ = decide (zmodDist n α₁ < zmodDist n s1i.1) := by
    rw [hs1i_snd]; exact zmodDistGt_of_snd_eq n s1i.1 α₂ α₁
  have hsq2 : (√2 : ℝ) ^ 2 = 2 := sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  have hpos : (0:ℝ) < √2 := sqrt_pos.mpr (by norm_num)
  -- Case split on S₁ closer
  by_cases h_s1_closer : zmodDist n s1.1 < zmodDist n α₁
  · -- S₁ closer: ψ(α, S₁α) = √2
    have hψ1 := psiWeight_eq_sqrt2_of_gt n α₁ α₂ s1.1 s1.2
      (by rw [hgt_s1]; simp [h_s1_closer])
    -- By cross_constraint_fwd: S₁⁻¹ farther
    have h_s1i_farther : zmodDist n α₁ < zmodDist n s1i.1 :=
      cross_constraint_fwd n α₁ α₂ hn hα₁ hα₂ h_s2 h_s2i h_s1_closer
    -- ψ(α, S₁⁻¹α) = √2/2 (α < S₁⁻¹α in the partial order)
    have hψ2 := psiWeight_eq_sqrt2_div2_of_rev_gt n α₁ α₂ s1i.1 s1i.2
      (by rw [hgt_s1i]; simp [not_lt.mpr h_s1i_farther.le])
      (by rw [hgt_s1i_rev]; simp [h_s1i_farther])
    rw [hψ1, hψ2]; nlinarith [sq_nonneg (√2 - 1)]
  · by_cases h_s1i_closer : zmodDist n s1i.1 < zmodDist n α₁
    · -- S₁⁻¹ closer: ψ(α, S₁⁻¹α) = √2
      have hψ2 := psiWeight_eq_sqrt2_of_gt n α₁ α₂ s1i.1 s1i.2
        (by rw [hgt_s1i]; simp [h_s1i_closer])
      -- By cross_constraint_rev: S₁ farther
      have h_s1_farther : zmodDist n α₁ < zmodDist n s1.1 :=
        cross_constraint_rev n α₁ α₂ hn hα₁ hα₂ h_s2 h_s2i h_s1i_closer
      -- ψ(α, S₁α) = √2/2
      have hψ1 := psiWeight_eq_sqrt2_div2_of_rev_gt n α₁ α₂ s1.1 s1.2
        (by rw [hgt_s1]; simp [not_lt.mpr h_s1_farther.le])
        (by rw [hgt_s1_rev]; simp [h_s1_farther])
      rw [hψ1, hψ2]; nlinarith [sq_nonneg (√2 - 1)]
    · -- Neither closer: each ψ ≤ 1
      have hψ1 := psiWeight_le_one_of_not_gt n α₁ α₂ s1.1 s1.2
        (by rw [hgt_s1]; exact decide_eq_false h_s1_closer)
      have hψ2 := psiWeight_le_one_of_not_gt n α₁ α₂ s1i.1 s1i.2
        (by rw [hgt_s1i]; exact decide_eq_false h_s1i_closer)
      -- 2 ≤ 3√2/2 since √2 ≥ 4/3
      nlinarith [sq_nonneg (3 * √2 - 4)]

/-- Symmetric version: when both S₁ neighbors are strictly closer, the S₂ pair sum
    is at most `3√2/2`. Proved by the same cross-constraint argument with
    coordinates swapped. -/
theorem pair_bound_when_both_S1_closer (n α₁ α₂ : ℕ) (hn : 3 ≤ n)
    (hα₁ : α₁ < n) (hα₂ : α₂ < n)
    (h_s1 : zmodDist n (shearS1 n α₁ α₂).1 < zmodDist n α₁)
    (h_s1i : zmodDist n (shearS1Inv n α₁ α₂).1 < zmodDist n α₁) :
    psiWeight n α₁ α₂ (shearS2 n α₁ α₂).1 (shearS2 n α₁ α₂).2 +
    psiWeight n α₁ α₂ (shearS2Inv n α₁ α₂).1 (shearS2Inv n α₁ α₂).2
      ≤ 3 * √2 / 2 := by
  set s2 := shearS2 n α₁ α₂
  set s2i := shearS2Inv n α₁ α₂
  have hs2_fst : s2.1 = α₁ := shearS2_fst n α₁ α₂
  have hs2i_fst : s2i.1 = α₁ := shearS2Inv_fst n α₁ α₂
  have hgt_s2 : zmodDistGt n α₁ α₂ s2.1 s2.2 = decide (zmodDist n s2.2 < zmodDist n α₂) := by
    rw [hs2_fst]; exact zmodDistGt_of_fst_eq n α₁ α₂ s2.2
  have hgt_s2i : zmodDistGt n α₁ α₂ s2i.1 s2i.2 = decide (zmodDist n s2i.2 < zmodDist n α₂) := by
    rw [hs2i_fst]; exact zmodDistGt_of_fst_eq n α₁ α₂ s2i.2
  have hgt_s2_rev : zmodDistGt n s2.1 s2.2 α₁ α₂ = decide (zmodDist n α₂ < zmodDist n s2.2) := by
    rw [hs2_fst]; exact zmodDistGt_of_fst_eq n α₁ s2.2 α₂
  have hgt_s2i_rev : zmodDistGt n s2i.1 s2i.2 α₁ α₂ = decide (zmodDist n α₂ < zmodDist n s2i.2) := by
    rw [hs2i_fst]; exact zmodDistGt_of_fst_eq n α₁ s2i.2 α₂
  have hsq2 : (√2 : ℝ) ^ 2 = 2 := sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  have hpos : (0:ℝ) < √2 := sqrt_pos.mpr (by norm_num)
  -- Case split on S₂ closer
  by_cases h_s2_closer : zmodDist n s2.2 < zmodDist n α₂
  · -- S₂ closer: ψ(α, S₂α) = √2
    have hψ1 := psiWeight_eq_sqrt2_of_gt n α₁ α₂ s2.1 s2.2
      (by rw [hgt_s2]; simp [h_s2_closer])
    -- By cross_constraint_fwd(α₂, α₁): S₂⁻¹ farther
    have h_s2i_farther : zmodDist n α₂ < zmodDist n s2i.2 :=
      cross_constraint_fwd n α₂ α₁ hn hα₂ hα₁ h_s1 h_s1i h_s2_closer
    have hψ2 := psiWeight_eq_sqrt2_div2_of_rev_gt n α₁ α₂ s2i.1 s2i.2
      (by rw [hgt_s2i]; simp [not_lt.mpr h_s2i_farther.le])
      (by rw [hgt_s2i_rev]; simp [h_s2i_farther])
    rw [hψ1, hψ2]; nlinarith [sq_nonneg (√2 - 1)]
  · by_cases h_s2i_closer : zmodDist n s2i.2 < zmodDist n α₂
    · -- S₂⁻¹ closer: ψ(α, S₂⁻¹α) = √2
      have hψ2 := psiWeight_eq_sqrt2_of_gt n α₁ α₂ s2i.1 s2i.2
        (by rw [hgt_s2i]; simp [h_s2i_closer])
      -- By cross_constraint_rev(α₂, α₁): S₂ farther
      have h_s2_farther : zmodDist n α₂ < zmodDist n s2.2 :=
        cross_constraint_rev n α₂ α₁ hn hα₂ hα₁ h_s1 h_s1i h_s2i_closer
      have hψ1 := psiWeight_eq_sqrt2_div2_of_rev_gt n α₁ α₂ s2.1 s2.2
        (by rw [hgt_s2]; simp [not_lt.mpr h_s2_farther.le])
        (by rw [hgt_s2_rev]; simp [h_s2_farther])
      rw [hψ1, hψ2]; nlinarith [sq_nonneg (√2 - 1)]
    · -- Neither closer: each ψ ≤ 1
      have hψ1 := psiWeight_le_one_of_not_gt n α₁ α₂ s2.1 s2.2
        (by rw [hgt_s2]; exact decide_eq_false h_s2_closer)
      have hψ2 := psiWeight_le_one_of_not_gt n α₁ α₂ s2i.1 s2i.2
        (by rw [hgt_s2i]; exact decide_eq_false h_s2i_closer)
      nlinarith [sq_nonneg (3 * √2 - 4)]

/-- The pair squared sum bound for outside-diamond frequencies.
    For `α ≠ 0` with `zmodDist n α₁ + zmodDist n α₂ > n/2`:
    `pair₁² + pair₂² ≤ 25/2`, where `pairᵢ` are the ψ-weighted pair sums.

    Proof: case split on whether pair₁ or pair₂ equals `2√2`.
    - If pair₁ = 2√2: by `pair_bound_when_both_S2_closer`, pair₂ ≤ 3√2/2.
      Then (2√2)² + (3√2/2)² = 8 + 9/2 = 25/2. ✓
    - If pair₂ = 2√2: symmetric. ✓
    - If neither: each pair ≤ 1+√2 (gap in discrete values).
      Then 2(1+√2)² = 6+4√2 < 25/2. ✓ -/
theorem pair_sq_sum_le_outside (n α₁ α₂ : ℕ) (hn : 3 ≤ n)
    (hα₁ : α₁ < n) (hα₂ : α₂ < n) :
    let s1 := shearS1 n α₁ α₂
    let s1i := shearS1Inv n α₁ α₂
    let s2 := shearS2 n α₁ α₂
    let s2i := shearS2Inv n α₁ α₂
    (psiWeight n α₁ α₂ s2.1 s2.2 + psiWeight n α₁ α₂ s2i.1 s2i.2) ^ 2 +
    (psiWeight n α₁ α₂ s1.1 s1.2 + psiWeight n α₁ α₂ s1i.1 s1i.2) ^ 2
      ≤ 25 / 2 := by
  simp only
  -- Abbreviations
  set s2 := shearS2 n α₁ α₂
  set s2i := shearS2Inv n α₁ α₂
  set s1 := shearS1 n α₁ α₂
  set s1i := shearS1Inv n α₁ α₂
  set pair₁ := psiWeight n α₁ α₂ s2.1 s2.2 + psiWeight n α₁ α₂ s2i.1 s2i.2
  set pair₂ := psiWeight n α₁ α₂ s1.1 s1.2 + psiWeight n α₁ α₂ s1i.1 s1i.2
  -- Common facts about √2
  have hsq : (√2 : ℝ) ^ 2 = 2 := sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  have hpos : (0:ℝ) < √2 := sqrt_pos.mpr (by norm_num)
  -- Each ψ is positive and ≤ √2
  have hψ_s2 := psiWeight_le_sqrt2 n α₁ α₂ s2.1 s2.2
  have hψ_s2i := psiWeight_le_sqrt2 n α₁ α₂ s2i.1 s2i.2
  have hψ_s1 := psiWeight_le_sqrt2 n α₁ α₂ s1.1 s1.2
  have hψ_s1i := psiWeight_le_sqrt2 n α₁ α₂ s1i.1 s1i.2
  have hψ_s2_pos := (psiWeight_pos n α₁ α₂ s2.1 s2.2).le
  have hψ_s2i_pos := (psiWeight_pos n α₁ α₂ s2i.1 s2i.2).le
  have hψ_s1_pos := (psiWeight_pos n α₁ α₂ s1.1 s1.2).le
  have hψ_s1i_pos := (psiWeight_pos n α₁ α₂ s1i.1 s1i.2).le
  -- S₂ preserves first coordinate, S₁ preserves second
  have hs2_fst : s2.1 = α₁ := shearS2_fst n α₁ α₂
  have hs2i_fst : s2i.1 = α₁ := shearS2Inv_fst n α₁ α₂
  have hs1_snd : s1.2 = α₂ := shearS1_snd n α₁ α₂
  have hs1i_snd : s1i.2 = α₂ := shearS1Inv_snd n α₁ α₂
  -- Rewrite zmodDistGt using coordinate preservation
  have hgt_s2 : zmodDistGt n α₁ α₂ s2.1 s2.2 = decide (zmodDist n s2.2 < zmodDist n α₂) := by
    rw [hs2_fst]; exact zmodDistGt_of_fst_eq n α₁ α₂ s2.2
  have hgt_s2i : zmodDistGt n α₁ α₂ s2i.1 s2i.2 = decide (zmodDist n s2i.2 < zmodDist n α₂) := by
    rw [hs2i_fst]; exact zmodDistGt_of_fst_eq n α₁ α₂ s2i.2
  have hgt_s1 : zmodDistGt n α₁ α₂ s1.1 s1.2 = decide (zmodDist n s1.1 < zmodDist n α₁) := by
    rw [hs1_snd]; exact zmodDistGt_of_snd_eq n α₁ α₂ s1.1
  have hgt_s1i : zmodDistGt n α₁ α₂ s1i.1 s1i.2 = decide (zmodDist n s1i.1 < zmodDist n α₁) := by
    rw [hs1i_snd]; exact zmodDistGt_of_snd_eq n α₁ α₂ s1i.1
  -- Case split: are BOTH S₂ neighbors strictly closer?
  by_cases h_both_s2 : zmodDist n s2.2 < zmodDist n α₂ ∧ zmodDist n s2i.2 < zmodDist n α₂
  · -- Case 1: pair₁ = 2√2. Key lemma gives pair₂ ≤ 3√2/2.
    obtain ⟨h_s2_lt, h_s2i_lt⟩ := h_both_s2
    have hpair₂_le := pair_bound_when_both_S2_closer n α₁ α₂ hn hα₁ hα₂ h_s2_lt h_s2i_lt
    -- pair₁ = √2 + √2 = 2√2
    have hpair₁_eq : pair₁ = 2 * √2 := by
      show psiWeight n α₁ α₂ s2.1 s2.2 + psiWeight n α₁ α₂ s2i.1 s2i.2 = 2 * √2
      rw [psiWeight_eq_sqrt2_of_gt n α₁ α₂ s2.1 s2.2 (by rw [hgt_s2]; simp [h_s2_lt]),
          psiWeight_eq_sqrt2_of_gt n α₁ α₂ s2i.1 s2i.2 (by rw [hgt_s2i]; simp [h_s2i_lt])]
      ring
    -- (2√2)² + pair₂² ≤ 8 + (3√2/2)² = 8 + 9/2 = 25/2
    rw [hpair₁_eq]
    nlinarith [sq_nonneg (pair₂ - 3 * √2 / 2)]
  · -- pair₁ < 2√2, so at least one S₂ ψ ≤ 1, giving pair₁ ≤ 1 + √2
    by_cases h_both_s1 : zmodDist n s1.1 < zmodDist n α₁ ∧ zmodDist n s1i.1 < zmodDist n α₁
    · -- Case 2: pair₂ = 2√2. Symmetric key lemma gives pair₁ ≤ 3√2/2.
      obtain ⟨h_s1_lt, h_s1i_lt⟩ := h_both_s1
      have hpair₁_le := pair_bound_when_both_S1_closer n α₁ α₂ hn hα₁ hα₂ h_s1_lt h_s1i_lt
      have hpair₂_eq : pair₂ = 2 * √2 := by
        show psiWeight n α₁ α₂ s1.1 s1.2 + psiWeight n α₁ α₂ s1i.1 s1i.2 = 2 * √2
        rw [psiWeight_eq_sqrt2_of_gt n α₁ α₂ s1.1 s1.2 (by rw [hgt_s1]; simp [h_s1_lt]),
            psiWeight_eq_sqrt2_of_gt n α₁ α₂ s1i.1 s1i.2 (by rw [hgt_s1i]; simp [h_s1i_lt])]
        ring
      rw [hpair₂_eq]
      nlinarith [sq_nonneg (pair₁ - 3 * √2 / 2)]
    · -- Case 3: neither pair is 2√2. Each pair ≤ 1 + √2.
      -- At least one S₂ ψ ≤ 1
      have hpair₁_le : pair₁ ≤ 1 + √2 := by
        rcases not_and_or.mp h_both_s2 with h | h
        · -- First S₂ ψ ≤ 1 (not closer)
          have := psiWeight_le_one_of_not_gt n α₁ α₂ s2.1 s2.2
            (by rw [hgt_s2]; exact decide_eq_false h)
          linarith
        · -- Second S₂ ψ ≤ 1 (not closer)
          have := psiWeight_le_one_of_not_gt n α₁ α₂ s2i.1 s2i.2
            (by rw [hgt_s2i]; exact decide_eq_false h)
          linarith
      -- At least one S₁ ψ ≤ 1
      have hpair₂_le : pair₂ ≤ 1 + √2 := by
        rcases not_and_or.mp h_both_s1 with h | h
        · have := psiWeight_le_one_of_not_gt n α₁ α₂ s1.1 s1.2
            (by rw [hgt_s1]; exact decide_eq_false h)
          linarith
        · have := psiWeight_le_one_of_not_gt n α₁ α₂ s1i.1 s1i.2
            (by rw [hgt_s1i]; exact decide_eq_false h)
          linarith
      -- 2(1+√2)² = 6+4√2 < 25/2
      nlinarith [sq_nonneg (pair₁ - (1 + √2)), sq_nonneg (pair₂ - (1 + √2)),
                 sq_nonneg (√2 * 8 - 13)]

/-- Inside the diamond, both S₂ neighbors cannot simultaneously be strictly closer. -/
theorem diamond_no_both_S2_closer (n α₁ α₂ : ℕ) (hn : 3 ≤ n)
    (hα₁ : α₁ < n) (hα₂ : α₂ < n)
    (hdiam : zmodDist n α₁ + zmodDist n α₂ ≤ n / 2) :
    ¬(zmodDist n (shearS2 n α₁ α₂).2 < zmodDist n α₂ ∧
      zmodDist n (shearS2Inv n α₁ α₂).2 < zmodDist n α₂) := by
  intro ⟨hs2, hs2i⟩
  rw [zd_S2 n α₁ α₂ hα₁ hα₂ (by omega)] at hs2
  rw [zd_S2I n α₁ α₂ hα₁ hα₂ (by omega)] at hs2i
  unfold zmodDist at hdiam hs2 hs2i
  by_cases h1 : 2 * α₁ < n
  · simp only [double_mod_lo n α₁ h1] at hs2 hs2i
    simp only [Nat.min_def] at hs2 hs2i hdiam; split_ifs at hdiam hs2 hs2i <;> omega
  · simp only [double_mod_hi n α₁ hα₁ h1] at hs2 hs2i
    simp only [Nat.min_def] at hs2 hs2i hdiam; split_ifs at hdiam hs2 hs2i <;> omega

/-- Inside the diamond, both S₁ neighbors cannot simultaneously be strictly closer.
    Symmetric version of `diamond_no_both_S2_closer`. -/
theorem diamond_no_both_S1_closer (n α₁ α₂ : ℕ) (hn : 3 ≤ n)
    (hα₁ : α₁ < n) (hα₂ : α₂ < n)
    (hdiam : zmodDist n α₁ + zmodDist n α₂ ≤ n / 2) :
    ¬(zmodDist n (shearS1 n α₁ α₂).1 < zmodDist n α₁ ∧
      zmodDist n (shearS1Inv n α₁ α₂).1 < zmodDist n α₁) := by
  intro ⟨hs1, hs1i⟩
  rw [zd_S1 n α₁ α₂ hα₁ hα₂ (by omega)] at hs1
  rw [zd_S1I n α₁ α₂ hα₁ hα₂ (by omega)] at hs1i
  unfold zmodDist at hdiam hs1 hs1i
  by_cases h2 : 2 * α₂ < n
  · simp only [double_mod_lo n α₂ h2] at hs1 hs1i
    simp only [Nat.min_def] at hs1 hs1i hdiam; split_ifs at hdiam hs1 hs1i <;> omega
  · simp only [double_mod_hi n α₂ hα₂ h2] at hs1 hs1i
    simp only [Nat.min_def] at hs1 hs1i hdiam; split_ifs at hdiam hs1 hs1i <;> omega

/-- In the strict diamond (`2(d₁+d₂) < n`), if S₂ is closer then the other 3
    neighbors are strictly farther. -/
theorem strict_diamond_closer_S2_all_farther (n α₁ α₂ : ℕ) (hn : 3 ≤ n)
    (hα₁ : α₁ < n) (hα₂ : α₂ < n)
    (hstrict : 2 * (zmodDist n α₁ + zmodDist n α₂) + 1 ≤ n)
    (hs2 : zmodDist n (shearS2 n α₁ α₂).2 < zmodDist n α₂) :
    zmodDist n α₂ < zmodDist n (shearS2Inv n α₁ α₂).2 ∧
    zmodDist n α₁ < zmodDist n (shearS1 n α₁ α₂).1 ∧
    zmodDist n α₁ < zmodDist n (shearS1Inv n α₁ α₂).1 := by
  rw [zd_S2 n α₁ α₂ hα₁ hα₂ (by omega)] at hs2
  rw [zd_S2I n α₁ α₂ hα₁ hα₂ (by omega),
      zd_S1 n α₁ α₂ hα₁ hα₂ (by omega),
      zd_S1I n α₁ α₂ hα₁ hα₂ (by omega)]
  unfold zmodDist at hstrict hs2 ⊢
  by_cases h1 : 2 * α₁ < n <;> by_cases h2 : 2 * α₂ < n
  · simp only [double_mod_lo n α₁ h1, double_mod_lo n α₂ h2,
      Nat.min_eq_left (by omega : α₁ ≤ n - α₁),
      Nat.min_eq_left (by omega : α₂ ≤ n - α₂)] at hstrict hs2 ⊢
    simp only [Nat.min_def] at hs2 ⊢; split_ifs at hs2 <;> (refine ⟨?_, ?_, ?_⟩ <;> split_ifs <;> omega)
  · simp only [double_mod_lo n α₁ h1, double_mod_hi n α₂ hα₂ h2,
      Nat.min_eq_left (by omega : α₁ ≤ n - α₁),
      Nat.min_eq_right (by omega : n - α₂ ≤ α₂)] at hstrict hs2 ⊢
    simp only [Nat.min_def] at hs2 ⊢; split_ifs at hs2 <;> (refine ⟨?_, ?_, ?_⟩ <;> split_ifs <;> omega)
  · simp only [double_mod_hi n α₁ hα₁ h1, double_mod_lo n α₂ h2,
      Nat.min_eq_right (by omega : n - α₁ ≤ α₁),
      Nat.min_eq_left (by omega : α₂ ≤ n - α₂)] at hstrict hs2 ⊢
    simp only [Nat.min_def] at hs2 ⊢; split_ifs at hs2 <;> (refine ⟨?_, ?_, ?_⟩ <;> split_ifs <;> omega)
  · simp only [double_mod_hi n α₁ hα₁ h1, double_mod_hi n α₂ hα₂ h2,
      Nat.min_eq_right (by omega : n - α₁ ≤ α₁),
      Nat.min_eq_right (by omega : n - α₂ ≤ α₂)] at hstrict hs2 ⊢
    simp only [Nat.min_def] at hs2 ⊢; split_ifs at hs2 <;> (refine ⟨?_, ?_, ?_⟩ <;> split_ifs <;> omega)

/-- Symmetric: if S₂⁻¹ closer in strict diamond, all other 3 are farther. -/
theorem strict_diamond_closer_S2Inv_all_farther (n α₁ α₂ : ℕ) (hn : 3 ≤ n)
    (hα₁ : α₁ < n) (hα₂ : α₂ < n)
    (hstrict : 2 * (zmodDist n α₁ + zmodDist n α₂) + 1 ≤ n)
    (hs2i : zmodDist n (shearS2Inv n α₁ α₂).2 < zmodDist n α₂) :
    zmodDist n α₂ < zmodDist n (shearS2 n α₁ α₂).2 ∧
    zmodDist n α₁ < zmodDist n (shearS1 n α₁ α₂).1 ∧
    zmodDist n α₁ < zmodDist n (shearS1Inv n α₁ α₂).1 := by
  rw [zd_S2I n α₁ α₂ hα₁ hα₂ (by omega)] at hs2i
  rw [zd_S2 n α₁ α₂ hα₁ hα₂ (by omega),
      zd_S1 n α₁ α₂ hα₁ hα₂ (by omega),
      zd_S1I n α₁ α₂ hα₁ hα₂ (by omega)]
  unfold zmodDist at hstrict hs2i ⊢
  by_cases h1 : 2 * α₁ < n <;> by_cases h2 : 2 * α₂ < n
  · simp only [double_mod_lo n α₁ h1, double_mod_lo n α₂ h2,
      Nat.min_eq_left (by omega : α₁ ≤ n - α₁),
      Nat.min_eq_left (by omega : α₂ ≤ n - α₂)] at hstrict hs2i ⊢
    simp only [Nat.min_def] at hs2i ⊢; split_ifs at hs2i <;> (refine ⟨?_, ?_, ?_⟩ <;> split_ifs <;> omega)
  · simp only [double_mod_lo n α₁ h1, double_mod_hi n α₂ hα₂ h2,
      Nat.min_eq_left (by omega : α₁ ≤ n - α₁),
      Nat.min_eq_right (by omega : n - α₂ ≤ α₂)] at hstrict hs2i ⊢
    simp only [Nat.min_def] at hs2i ⊢; split_ifs at hs2i <;> (refine ⟨?_, ?_, ?_⟩ <;> split_ifs <;> omega)
  · simp only [double_mod_hi n α₁ hα₁ h1, double_mod_lo n α₂ h2,
      Nat.min_eq_right (by omega : n - α₁ ≤ α₁),
      Nat.min_eq_left (by omega : α₂ ≤ n - α₂)] at hstrict hs2i ⊢
    simp only [Nat.min_def] at hs2i ⊢; split_ifs at hs2i <;> (refine ⟨?_, ?_, ?_⟩ <;> split_ifs <;> omega)
  · simp only [double_mod_hi n α₁ hα₁ h1, double_mod_hi n α₂ hα₂ h2,
      Nat.min_eq_right (by omega : n - α₁ ≤ α₁),
      Nat.min_eq_right (by omega : n - α₂ ≤ α₂)] at hstrict hs2i ⊢
    simp only [Nat.min_def] at hs2i ⊢; split_ifs at hs2i <;> (refine ⟨?_, ?_, ?_⟩ <;> split_ifs <;> omega)

/-- In strict diamond, S₂ pair both E implies S₁ pair both farther. -/
theorem strict_diamond_S2_both_eq_implies_S1_farther (n α₁ α₂ : ℕ) (hn : 3 ≤ n)
    (hα₁ : α₁ < n) (hα₂ : α₂ < n) (hne : ¬(α₁ = 0 ∧ α₂ = 0))
    (hstrict : 2 * (zmodDist n α₁ + zmodDist n α₂) + 1 ≤ n)
    (hs2_eq : zmodDist n (shearS2 n α₁ α₂).2 = zmodDist n α₂)
    (hs2i_eq : zmodDist n (shearS2Inv n α₁ α₂).2 = zmodDist n α₂) :
    zmodDist n α₁ < zmodDist n (shearS1 n α₁ α₂).1 ∧
    zmodDist n α₁ < zmodDist n (shearS1Inv n α₁ α₂).1 := by
  rw [zd_S2 n α₁ α₂ hα₁ hα₂ (by omega)] at hs2_eq
  rw [zd_S2I n α₁ α₂ hα₁ hα₂ (by omega)] at hs2i_eq
  rw [zd_S1 n α₁ α₂ hα₁ hα₂ (by omega),
      zd_S1I n α₁ α₂ hα₁ hα₂ (by omega)]
  unfold zmodDist at hstrict hs2_eq hs2i_eq ⊢
  by_cases h1 : 2 * α₁ < n <;> by_cases h2 : 2 * α₂ < n
  · simp only [double_mod_lo n α₁ h1, double_mod_lo n α₂ h2,
      Nat.min_eq_left (by omega : α₁ ≤ n - α₁),
      Nat.min_eq_left (by omega : α₂ ≤ n - α₂)] at hstrict hs2_eq hs2i_eq ⊢
    simp only [Nat.min_def] at hs2_eq hs2i_eq ⊢
    split_ifs at hs2_eq <;> (try omega) <;> split_ifs at hs2i_eq <;> (try omega);
      constructor <;> split_ifs <;> omega
  · simp only [double_mod_lo n α₁ h1, double_mod_hi n α₂ hα₂ h2,
      Nat.min_eq_left (by omega : α₁ ≤ n - α₁),
      Nat.min_eq_right (by omega : n - α₂ ≤ α₂)] at hstrict hs2_eq hs2i_eq ⊢
    simp only [Nat.min_def] at hs2_eq hs2i_eq ⊢
    split_ifs at hs2_eq <;> (try omega); split_ifs at hs2i_eq <;> (try omega);
      constructor <;> split_ifs <;> omega
  · simp only [double_mod_hi n α₁ hα₁ h1, double_mod_lo n α₂ h2,
      Nat.min_eq_right (by omega : n - α₁ ≤ α₁),
      Nat.min_eq_left (by omega : α₂ ≤ n - α₂)] at hstrict hs2_eq hs2i_eq ⊢
    simp only [Nat.min_def] at hs2_eq hs2i_eq ⊢
    split_ifs at hs2_eq <;> omega
  · simp only [double_mod_hi n α₁ hα₁ h1, double_mod_hi n α₂ hα₂ h2,
      Nat.min_eq_right (by omega : n - α₁ ≤ α₁),
      Nat.min_eq_right (by omega : n - α₂ ≤ α₂)] at hstrict hs2_eq hs2i_eq ⊢
    simp only [Nat.min_def] at hs2_eq hs2i_eq ⊢
    split_ifs at hs2_eq <;> (try omega); split_ifs at hs2i_eq <;> omega

/-- Symmetric: S₁ pair both E implies S₂ pair both farther. -/
theorem strict_diamond_S1_both_eq_implies_S2_farther (n α₁ α₂ : ℕ) (hn : 3 ≤ n)
    (hα₁ : α₁ < n) (hα₂ : α₂ < n) (hne : ¬(α₁ = 0 ∧ α₂ = 0))
    (hstrict : 2 * (zmodDist n α₁ + zmodDist n α₂) + 1 ≤ n)
    (hs1_eq : zmodDist n (shearS1 n α₁ α₂).1 = zmodDist n α₁)
    (hs1i_eq : zmodDist n (shearS1Inv n α₁ α₂).1 = zmodDist n α₁) :
    zmodDist n α₂ < zmodDist n (shearS2 n α₁ α₂).2 ∧
    zmodDist n α₂ < zmodDist n (shearS2Inv n α₁ α₂).2 := by
  rw [zd_S1 n α₁ α₂ hα₁ hα₂ (by omega)] at hs1_eq
  rw [zd_S1I n α₁ α₂ hα₁ hα₂ (by omega)] at hs1i_eq
  rw [zd_S2 n α₁ α₂ hα₁ hα₂ (by omega),
      zd_S2I n α₁ α₂ hα₁ hα₂ (by omega)]
  unfold zmodDist at hstrict hs1_eq hs1i_eq ⊢
  by_cases h1 : 2 * α₁ < n <;> by_cases h2 : 2 * α₂ < n
  · simp only [double_mod_lo n α₁ h1, double_mod_lo n α₂ h2,
      Nat.min_eq_left (by omega : α₁ ≤ n - α₁),
      Nat.min_eq_left (by omega : α₂ ≤ n - α₂)] at hstrict hs1_eq hs1i_eq ⊢
    simp only [Nat.min_def] at hs1_eq hs1i_eq ⊢
    split_ifs at hs1_eq <;> (try omega) <;> split_ifs at hs1i_eq <;> (try omega);
      constructor <;> split_ifs <;> omega
  · simp only [double_mod_lo n α₁ h1, double_mod_hi n α₂ hα₂ h2,
      Nat.min_eq_left (by omega : α₁ ≤ n - α₁),
      Nat.min_eq_right (by omega : n - α₂ ≤ α₂)] at hstrict hs1_eq hs1i_eq ⊢
    simp only [Nat.min_def] at hs1_eq hs1i_eq ⊢
    split_ifs at hs1_eq <;> omega
  · simp only [double_mod_hi n α₁ hα₁ h1, double_mod_lo n α₂ h2,
      Nat.min_eq_right (by omega : n - α₁ ≤ α₁),
      Nat.min_eq_left (by omega : α₂ ≤ n - α₂)] at hstrict hs1_eq hs1i_eq ⊢
    simp only [Nat.min_def] at hs1_eq hs1i_eq ⊢
    split_ifs at hs1_eq <;> (try omega); split_ifs at hs1i_eq <;> (try omega);
      constructor <;> split_ifs <;> omega
  · simp only [double_mod_hi n α₁ hα₁ h1, double_mod_hi n α₂ hα₂ h2,
      Nat.min_eq_right (by omega : n - α₁ ≤ α₁),
      Nat.min_eq_right (by omega : n - α₂ ≤ α₂)] at hstrict hs1_eq hs1i_eq ⊢
    simp only [Nat.min_def] at hs1_eq hs1i_eq ⊢
    split_ifs at hs1_eq <;> (try omega); split_ifs at hs1i_eq <;> omega

/-- In the strict diamond, if S₁ is closer then the other 3 neighbors are strictly farther.
    Mirrors `strict_diamond_closer_S2_all_farther` with S₁/S₂ roles swapped. -/
theorem strict_diamond_closer_S1_all_farther (n α₁ α₂ : ℕ) (hn : 3 ≤ n)
    (hα₁ : α₁ < n) (hα₂ : α₂ < n)
    (hstrict : 2 * (zmodDist n α₁ + zmodDist n α₂) + 1 ≤ n)
    (hs1 : zmodDist n (shearS1 n α₁ α₂).1 < zmodDist n α₁) :
    zmodDist n α₁ < zmodDist n (shearS1Inv n α₁ α₂).1 ∧
    zmodDist n α₂ < zmodDist n (shearS2 n α₁ α₂).2 ∧
    zmodDist n α₂ < zmodDist n (shearS2Inv n α₁ α₂).2 := by
  rw [zd_S1 n α₁ α₂ hα₁ hα₂ (by omega)] at hs1
  rw [zd_S1I n α₁ α₂ hα₁ hα₂ (by omega),
      zd_S2 n α₁ α₂ hα₁ hα₂ (by omega),
      zd_S2I n α₁ α₂ hα₁ hα₂ (by omega)]
  unfold zmodDist at hstrict hs1 ⊢
  by_cases h1 : 2 * α₁ < n <;> by_cases h2 : 2 * α₂ < n
  · simp only [double_mod_lo n α₁ h1, double_mod_lo n α₂ h2,
      Nat.min_eq_left (by omega : α₁ ≤ n - α₁),
      Nat.min_eq_left (by omega : α₂ ≤ n - α₂)] at hstrict hs1 ⊢
    simp only [Nat.min_def] at hs1 ⊢; split_ifs at hs1 <;> (refine ⟨?_, ?_, ?_⟩ <;> split_ifs <;> omega)
  · simp only [double_mod_lo n α₁ h1, double_mod_hi n α₂ hα₂ h2,
      Nat.min_eq_left (by omega : α₁ ≤ n - α₁),
      Nat.min_eq_right (by omega : n - α₂ ≤ α₂)] at hstrict hs1 ⊢
    simp only [Nat.min_def] at hs1 ⊢; split_ifs at hs1 <;> (refine ⟨?_, ?_, ?_⟩ <;> split_ifs <;> omega)
  · simp only [double_mod_hi n α₁ hα₁ h1, double_mod_lo n α₂ h2,
      Nat.min_eq_right (by omega : n - α₁ ≤ α₁),
      Nat.min_eq_left (by omega : α₂ ≤ n - α₂)] at hstrict hs1 ⊢
    simp only [Nat.min_def] at hs1 ⊢; split_ifs at hs1 <;> (refine ⟨?_, ?_, ?_⟩ <;> split_ifs <;> omega)
  · simp only [double_mod_hi n α₁ hα₁ h1, double_mod_hi n α₂ hα₂ h2,
      Nat.min_eq_right (by omega : n - α₁ ≤ α₁),
      Nat.min_eq_right (by omega : n - α₂ ≤ α₂)] at hstrict hs1 ⊢
    simp only [Nat.min_def] at hs1 ⊢; split_ifs at hs1 <;> (refine ⟨?_, ?_, ?_⟩ <;> split_ifs <;> omega)

/-- Symmetric: if S₁⁻¹ closer in strict diamond, all other 3 are farther. -/
theorem strict_diamond_closer_S1Inv_all_farther (n α₁ α₂ : ℕ) (hn : 3 ≤ n)
    (hα₁ : α₁ < n) (hα₂ : α₂ < n)
    (hstrict : 2 * (zmodDist n α₁ + zmodDist n α₂) + 1 ≤ n)
    (hs1i : zmodDist n (shearS1Inv n α₁ α₂).1 < zmodDist n α₁) :
    zmodDist n α₁ < zmodDist n (shearS1 n α₁ α₂).1 ∧
    zmodDist n α₂ < zmodDist n (shearS2 n α₁ α₂).2 ∧
    zmodDist n α₂ < zmodDist n (shearS2Inv n α₁ α₂).2 := by
  rw [zd_S1I n α₁ α₂ hα₁ hα₂ (by omega)] at hs1i
  rw [zd_S1 n α₁ α₂ hα₁ hα₂ (by omega),
      zd_S2 n α₁ α₂ hα₁ hα₂ (by omega),
      zd_S2I n α₁ α₂ hα₁ hα₂ (by omega)]
  unfold zmodDist at hstrict hs1i ⊢
  by_cases h1 : 2 * α₁ < n <;> by_cases h2 : 2 * α₂ < n
  · simp only [double_mod_lo n α₁ h1, double_mod_lo n α₂ h2,
      Nat.min_eq_left (by omega : α₁ ≤ n - α₁),
      Nat.min_eq_left (by omega : α₂ ≤ n - α₂)] at hstrict hs1i ⊢
    simp only [Nat.min_def] at hs1i ⊢; split_ifs at hs1i <;> (refine ⟨?_, ?_, ?_⟩ <;> split_ifs <;> omega)
  · simp only [double_mod_lo n α₁ h1, double_mod_hi n α₂ hα₂ h2,
      Nat.min_eq_left (by omega : α₁ ≤ n - α₁),
      Nat.min_eq_right (by omega : n - α₂ ≤ α₂)] at hstrict hs1i ⊢
    simp only [Nat.min_def] at hs1i ⊢; split_ifs at hs1i <;> (refine ⟨?_, ?_, ?_⟩ <;> split_ifs <;> omega)
  · simp only [double_mod_hi n α₁ hα₁ h1, double_mod_lo n α₂ h2,
      Nat.min_eq_right (by omega : n - α₁ ≤ α₁),
      Nat.min_eq_left (by omega : α₂ ≤ n - α₂)] at hstrict hs1i ⊢
    simp only [Nat.min_def] at hs1i ⊢; split_ifs at hs1i <;> (refine ⟨?_, ?_, ?_⟩ <;> split_ifs <;> omega)
  · simp only [double_mod_hi n α₁ hα₁ h1, double_mod_hi n α₂ hα₂ h2,
      Nat.min_eq_right (by omega : n - α₁ ≤ α₁),
      Nat.min_eq_right (by omega : n - α₂ ≤ α₂)] at hstrict hs1i ⊢
    simp only [Nat.min_def] at hs1i ⊢; split_ifs at hs1i <;> (refine ⟨?_, ?_, ?_⟩ <;> split_ifs <;> omega)

/-- When `2(d₁+d₂) < n`, the ψ pair sum is at most `5√2/2` inside the diamond.
    Verified for `n ≤ 200`. The tight case is CFFF (one closer, three farther):
    `√2 + 3·(√2/2) = 5√2/2`.

    Proof uses three structural facts about the strict diamond:
    1. If any neighbor is closer, all other 3 are farther (`*_all_farther`).
    2. If S₂ pair both E, S₁ pair both F (`S2_both_eq_implies_S1_farther`).
    3. Symmetric for S₁. -/
theorem strict_diamond_pair_sum_le (n α₁ α₂ : ℕ) (hn : 3 ≤ n)
    (hα₁ : α₁ < n) (hα₂ : α₂ < n) (hne : ¬(α₁ = 0 ∧ α₂ = 0))
    (hstrict : 2 * (zmodDist n α₁ + zmodDist n α₂) + 1 ≤ n) :
    (psiWeight n α₁ α₂ (shearS2 n α₁ α₂).1 (shearS2 n α₁ α₂).2 +
     psiWeight n α₁ α₂ (shearS2Inv n α₁ α₂).1 (shearS2Inv n α₁ α₂).2) +
    (psiWeight n α₁ α₂ (shearS1 n α₁ α₂).1 (shearS1 n α₁ α₂).2 +
     psiWeight n α₁ α₂ (shearS1Inv n α₁ α₂).1 (shearS1Inv n α₁ α₂).2) ≤ 5 * √2 / 2 := by
  -- Abbreviations
  set s2 := shearS2 n α₁ α₂; set s2i := shearS2Inv n α₁ α₂
  set s1 := shearS1 n α₁ α₂; set s1i := shearS1Inv n α₁ α₂
  -- Coordinate preservation
  have hs2_fst : s2.1 = α₁ := shearS2_fst n α₁ α₂
  have hs2i_fst : s2i.1 = α₁ := shearS2Inv_fst n α₁ α₂
  have hs1_snd : s1.2 = α₂ := shearS1_snd n α₁ α₂
  have hs1i_snd : s1i.2 = α₂ := shearS1Inv_snd n α₁ α₂
  -- zmodDistGt reductions
  have hgt_s2 : zmodDistGt n α₁ α₂ s2.1 s2.2 = decide (zmodDist n s2.2 < zmodDist n α₂) := by
    rw [hs2_fst]; exact zmodDistGt_of_fst_eq n α₁ α₂ s2.2
  have hgt_s2i : zmodDistGt n α₁ α₂ s2i.1 s2i.2 = decide (zmodDist n s2i.2 < zmodDist n α₂) := by
    rw [hs2i_fst]; exact zmodDistGt_of_fst_eq n α₁ α₂ s2i.2
  have hgt_s1 : zmodDistGt n α₁ α₂ s1.1 s1.2 = decide (zmodDist n s1.1 < zmodDist n α₁) := by
    rw [hs1_snd]; exact zmodDistGt_of_snd_eq n α₁ α₂ s1.1
  have hgt_s1i : zmodDistGt n α₁ α₂ s1i.1 s1i.2 = decide (zmodDist n s1i.1 < zmodDist n α₁) := by
    rw [hs1i_snd]; exact zmodDistGt_of_snd_eq n α₁ α₂ s1i.1
  -- Reverse zmodDistGt
  have hgt_s2_r : zmodDistGt n s2.1 s2.2 α₁ α₂ = decide (zmodDist n α₂ < zmodDist n s2.2) := by
    rw [hs2_fst]; exact zmodDistGt_of_fst_eq n α₁ s2.2 α₂
  have hgt_s2i_r : zmodDistGt n s2i.1 s2i.2 α₁ α₂ = decide (zmodDist n α₂ < zmodDist n s2i.2) := by
    rw [hs2i_fst]; exact zmodDistGt_of_fst_eq n α₁ s2i.2 α₂
  have hgt_s1_r : zmodDistGt n s1.1 s1.2 α₁ α₂ = decide (zmodDist n α₁ < zmodDist n s1.1) := by
    rw [hs1_snd]; exact zmodDistGt_of_snd_eq n s1.1 α₂ α₁
  have hgt_s1i_r : zmodDistGt n s1i.1 s1i.2 α₁ α₂ = decide (zmodDist n α₁ < zmodDist n s1i.1) := by
    rw [hs1i_snd]; exact zmodDistGt_of_snd_eq n s1i.1 α₂ α₁
  -- √2 facts
  have hsq : (√2 : ℝ) ^ 2 = 2 := sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  have hpos : (0:ℝ) < √2 := sqrt_pos.mpr (by norm_num)
  -- Case split: is any S₂ neighbor closer?
  by_cases h_s2_closer : zmodDist n s2.2 < zmodDist n α₂
  · -- S₂ closer: all other 3 are farther
    have h_all := strict_diamond_closer_S2_all_farther n α₁ α₂ hn hα₁ hα₂ hstrict h_s2_closer
    have h_s2i_f : zmodDist n α₂ < zmodDist n s2i.2 := h_all.1
    have h_s1_f : zmodDist n α₁ < zmodDist n s1.1 := h_all.2.1
    have h_s1i_f : zmodDist n α₁ < zmodDist n s1i.1 := h_all.2.2
    rw [psiWeight_eq_sqrt2_of_gt n α₁ α₂ s2.1 s2.2 (by rw [hgt_s2]; simp [h_s2_closer]),
        psiWeight_eq_sqrt2_div2_of_rev_gt n α₁ α₂ s2i.1 s2i.2
          (by rw [hgt_s2i]; simp [not_lt.mpr h_s2i_f.le])
          (by rw [hgt_s2i_r]; simp [h_s2i_f]),
        psiWeight_eq_sqrt2_div2_of_rev_gt n α₁ α₂ s1.1 s1.2
          (by rw [hgt_s1]; simp [not_lt.mpr h_s1_f.le])
          (by rw [hgt_s1_r]; simp [h_s1_f]),
        psiWeight_eq_sqrt2_div2_of_rev_gt n α₁ α₂ s1i.1 s1i.2
          (by rw [hgt_s1i]; simp [not_lt.mpr h_s1i_f.le])
          (by rw [hgt_s1i_r]; simp [h_s1i_f])]
    nlinarith [sq_nonneg (√2 - 1)]
  · by_cases h_s2i_closer : zmodDist n s2i.2 < zmodDist n α₂
    · -- S₂⁻¹ closer: all other 3 are farther
      have h_all := strict_diamond_closer_S2Inv_all_farther n α₁ α₂ hn hα₁ hα₂ hstrict h_s2i_closer
      have h_s2_f : zmodDist n α₂ < zmodDist n s2.2 := h_all.1
      have h_s1_f : zmodDist n α₁ < zmodDist n s1.1 := h_all.2.1
      have h_s1i_f : zmodDist n α₁ < zmodDist n s1i.1 := h_all.2.2
      rw [psiWeight_eq_sqrt2_div2_of_rev_gt n α₁ α₂ s2.1 s2.2
            (by rw [hgt_s2]; simp [not_lt.mpr h_s2_f.le])
            (by rw [hgt_s2_r]; simp [h_s2_f]),
          psiWeight_eq_sqrt2_of_gt n α₁ α₂ s2i.1 s2i.2 (by rw [hgt_s2i]; simp [h_s2i_closer]),
          psiWeight_eq_sqrt2_div2_of_rev_gt n α₁ α₂ s1.1 s1.2
            (by rw [hgt_s1]; simp [not_lt.mpr h_s1_f.le])
            (by rw [hgt_s1_r]; simp [h_s1_f]),
          psiWeight_eq_sqrt2_div2_of_rev_gt n α₁ α₂ s1i.1 s1i.2
            (by rw [hgt_s1i]; simp [not_lt.mpr h_s1i_f.le])
            (by rw [hgt_s1i_r]; simp [h_s1i_f])]
      nlinarith [sq_nonneg (√2 - 1)]
    · -- No S₂ closer. Check S₁.
      by_cases h_s1_closer : zmodDist n s1.1 < zmodDist n α₁
      · -- S₁ closer: all other 3 are farther
        have h_all := strict_diamond_closer_S1_all_farther n α₁ α₂ hn hα₁ hα₂ hstrict h_s1_closer
        have h_s1i_f : zmodDist n α₁ < zmodDist n s1i.1 := h_all.1
        have h_s2_f : zmodDist n α₂ < zmodDist n s2.2 := h_all.2.1
        have h_s2i_f : zmodDist n α₂ < zmodDist n s2i.2 := h_all.2.2
        rw [psiWeight_eq_sqrt2_div2_of_rev_gt n α₁ α₂ s2.1 s2.2
              (by rw [hgt_s2]; simp [not_lt.mpr h_s2_f.le])
              (by rw [hgt_s2_r]; simp [h_s2_f]),
            psiWeight_eq_sqrt2_div2_of_rev_gt n α₁ α₂ s2i.1 s2i.2
              (by rw [hgt_s2i]; simp [not_lt.mpr h_s2i_f.le])
              (by rw [hgt_s2i_r]; simp [h_s2i_f]),
            psiWeight_eq_sqrt2_of_gt n α₁ α₂ s1.1 s1.2 (by rw [hgt_s1]; simp [h_s1_closer]),
            psiWeight_eq_sqrt2_div2_of_rev_gt n α₁ α₂ s1i.1 s1i.2
              (by rw [hgt_s1i]; simp [not_lt.mpr h_s1i_f.le])
              (by rw [hgt_s1i_r]; simp [h_s1i_f])]
        nlinarith [sq_nonneg (√2 - 1)]
      · by_cases h_s1i_closer : zmodDist n s1i.1 < zmodDist n α₁
        · -- S₁⁻¹ closer: all other 3 are farther
          have h_all := strict_diamond_closer_S1Inv_all_farther n α₁ α₂ hn hα₁ hα₂ hstrict h_s1i_closer
          have h_s1_f : zmodDist n α₁ < zmodDist n s1.1 := h_all.1
          have h_s2_f : zmodDist n α₂ < zmodDist n s2.2 := h_all.2.1
          have h_s2i_f : zmodDist n α₂ < zmodDist n s2i.2 := h_all.2.2
          rw [psiWeight_eq_sqrt2_div2_of_rev_gt n α₁ α₂ s2.1 s2.2
                (by rw [hgt_s2]; simp [not_lt.mpr h_s2_f.le])
                (by rw [hgt_s2_r]; simp [h_s2_f]),
              psiWeight_eq_sqrt2_div2_of_rev_gt n α₁ α₂ s2i.1 s2i.2
                (by rw [hgt_s2i]; simp [not_lt.mpr h_s2i_f.le])
                (by rw [hgt_s2i_r]; simp [h_s2i_f]),
              psiWeight_eq_sqrt2_div2_of_rev_gt n α₁ α₂ s1.1 s1.2
                (by rw [hgt_s1]; simp [not_lt.mpr h_s1_f.le])
                (by rw [hgt_s1_r]; simp [h_s1_f]),
              psiWeight_eq_sqrt2_of_gt n α₁ α₂ s1i.1 s1i.2 (by rw [hgt_s1i]; simp [h_s1i_closer])]
          nlinarith [sq_nonneg (√2 - 1)]
        · -- No closer at all. Each ψ ≤ 1.
          by_cases h_s2_eq : zmodDist n s2.2 = zmodDist n α₂ ∧ zmodDist n s2i.2 = zmodDist n α₂
          · -- S₂ pair both E → S₁ pair both F
            obtain ⟨hs2e, hs2ie⟩ := h_s2_eq
            have h_all := strict_diamond_S2_both_eq_implies_S1_farther
              n α₁ α₂ hn hα₁ hα₂ hne hstrict hs2e hs2ie
            have h_s1_f : zmodDist n α₁ < zmodDist n s1.1 := h_all.1
            have h_s1i_f : zmodDist n α₁ < zmodDist n s1i.1 := h_all.2
            have hψ_s2 : psiWeight n α₁ α₂ s2.1 s2.2 = 1 := by
              have h1 : zmodDistGt n α₁ α₂ s2.1 s2.2 = false := by
                rw [hgt_s2]; exact decide_eq_false (not_lt.mpr (le_of_eq hs2e.symm))
              have h2 : zmodDistGt n s2.1 s2.2 α₁ α₂ = false := by
                rw [hgt_s2_r]; exact decide_eq_false (not_lt.mpr (le_of_eq hs2e))
              simp only [psiWeight, h1, h2, Bool.false_eq_true, ↓reduceIte]
            have hψ_s2i : psiWeight n α₁ α₂ s2i.1 s2i.2 = 1 := by
              have h1 : zmodDistGt n α₁ α₂ s2i.1 s2i.2 = false := by
                rw [hgt_s2i]; exact decide_eq_false (not_lt.mpr (le_of_eq hs2ie.symm))
              have h2 : zmodDistGt n s2i.1 s2i.2 α₁ α₂ = false := by
                rw [hgt_s2i_r]; exact decide_eq_false (not_lt.mpr (le_of_eq hs2ie))
              simp only [psiWeight, h1, h2, Bool.false_eq_true, ↓reduceIte]
            rw [hψ_s2, hψ_s2i,
                psiWeight_eq_sqrt2_div2_of_rev_gt n α₁ α₂ s1.1 s1.2
                  (by rw [hgt_s1]; simp [not_lt.mpr h_s1_f.le])
                  (by rw [hgt_s1_r]; simp [h_s1_f]),
                psiWeight_eq_sqrt2_div2_of_rev_gt n α₁ α₂ s1i.1 s1i.2
                  (by rw [hgt_s1i]; simp [not_lt.mpr h_s1i_f.le])
                  (by rw [hgt_s1i_r]; simp [h_s1i_f])]
            nlinarith [sq_nonneg (3 * √2 - 4)]
          · -- S₂ pair NOT both E → at least one S₂ is farther
            push Not at h_s2_eq
            by_cases h_s1_eq : zmodDist n s1.1 = zmodDist n α₁ ∧ zmodDist n s1i.1 = zmodDist n α₁
            · -- S₁ pair both E → S₂ pair both F
              obtain ⟨hs1e, hs1ie⟩ := h_s1_eq
              have h_all := strict_diamond_S1_both_eq_implies_S2_farther
                n α₁ α₂ hn hα₁ hα₂ hne hstrict hs1e hs1ie
              have h_s2_f : zmodDist n α₂ < zmodDist n s2.2 := h_all.1
              have h_s2i_f : zmodDist n α₂ < zmodDist n s2i.2 := h_all.2
              have hψ_s1 : psiWeight n α₁ α₂ s1.1 s1.2 = 1 := by
                have h1 : zmodDistGt n α₁ α₂ s1.1 s1.2 = false := by
                  rw [hgt_s1]; exact decide_eq_false (not_lt.mpr (le_of_eq hs1e.symm))
                have h2 : zmodDistGt n s1.1 s1.2 α₁ α₂ = false := by
                  rw [hgt_s1_r]; exact decide_eq_false (not_lt.mpr (le_of_eq hs1e))
                simp only [psiWeight, h1, h2, Bool.false_eq_true, ↓reduceIte]
              have hψ_s1i : psiWeight n α₁ α₂ s1i.1 s1i.2 = 1 := by
                have h1 : zmodDistGt n α₁ α₂ s1i.1 s1i.2 = false := by
                  rw [hgt_s1i]; exact decide_eq_false (not_lt.mpr (le_of_eq hs1ie.symm))
                have h2 : zmodDistGt n s1i.1 s1i.2 α₁ α₂ = false := by
                  rw [hgt_s1i_r]; exact decide_eq_false (not_lt.mpr (le_of_eq hs1ie))
                simp only [psiWeight, h1, h2, Bool.false_eq_true, ↓reduceIte]
              rw [hψ_s1, hψ_s1i,
                  psiWeight_eq_sqrt2_div2_of_rev_gt n α₁ α₂ s2.1 s2.2
                    (by rw [hgt_s2]; simp [not_lt.mpr h_s2_f.le])
                    (by rw [hgt_s2_r]; simp [h_s2_f]),
                  psiWeight_eq_sqrt2_div2_of_rev_gt n α₁ α₂ s2i.1 s2i.2
                    (by rw [hgt_s2i]; simp [not_lt.mpr h_s2i_f.le])
                    (by rw [hgt_s2i_r]; simp [h_s2i_f])]
              nlinarith [sq_nonneg (3 * √2 - 4)]
            · -- Neither pair both E. Each pair has at most 1 E (so at least 1 F).
              push Not at h_s1_eq
              -- S₂ pair: not both E, no closer → at least one F. pair ≤ 1 + √2/2.
              have hp1 : psiWeight n α₁ α₂ s2.1 s2.2 + psiWeight n α₁ α₂ s2i.1 s2i.2
                  ≤ 1 + √2 / 2 := by
                have hle1 := psiWeight_le_one_of_not_gt n α₁ α₂ s2.1 s2.2
                  (by rw [hgt_s2]; exact decide_eq_false h_s2_closer)
                have hle2 := psiWeight_le_one_of_not_gt n α₁ α₂ s2i.1 s2i.2
                  (by rw [hgt_s2i]; exact decide_eq_false h_s2i_closer)
                -- Case split: is s2 equal (E) or farther (F)?
                rcases eq_or_lt_of_le (Nat.le_of_not_lt h_s2_closer) with hs2_eq | hs2_lt
                · -- s2 is E → by h_s2_eq, s2i is not E → s2i is F
                  have h_s2i_ne := h_s2_eq hs2_eq.symm
                  have h_s2i_f : zmodDist n α₂ < zmodDist n s2i.2 :=
                    lt_of_le_of_ne (Nat.le_of_not_lt h_s2i_closer) (Ne.symm h_s2i_ne)
                  rw [psiWeight_eq_sqrt2_div2_of_rev_gt n α₁ α₂ s2i.1 s2i.2
                    (by rw [hgt_s2i]; simp [not_lt.mpr h_s2i_f.le])
                    (by rw [hgt_s2i_r]; simp [h_s2i_f])]
                  linarith
                · -- s2 is F
                  rw [psiWeight_eq_sqrt2_div2_of_rev_gt n α₁ α₂ s2.1 s2.2
                    (by rw [hgt_s2]; simp [not_lt.mpr hs2_lt.le])
                    (by rw [hgt_s2_r]; simp [hs2_lt])]
                  linarith
              -- S₁ pair: similarly, ≤ 1 + √2/2.
              have hp2 : psiWeight n α₁ α₂ s1.1 s1.2 + psiWeight n α₁ α₂ s1i.1 s1i.2
                  ≤ 1 + √2 / 2 := by
                have hle1 := psiWeight_le_one_of_not_gt n α₁ α₂ s1.1 s1.2
                  (by rw [hgt_s1]; exact decide_eq_false h_s1_closer)
                have hle2 := psiWeight_le_one_of_not_gt n α₁ α₂ s1i.1 s1i.2
                  (by rw [hgt_s1i]; exact decide_eq_false h_s1i_closer)
                -- Case split: is s1 equal (E) or farther (F)?
                rcases eq_or_lt_of_le (Nat.le_of_not_lt h_s1_closer) with hs1_eq | hs1_lt
                · -- s1 is E → by h_s1_eq, s1i is not E → s1i is F
                  have h_s1i_ne := h_s1_eq hs1_eq.symm
                  have h_s1i_f : zmodDist n α₁ < zmodDist n s1i.1 :=
                    lt_of_le_of_ne (Nat.le_of_not_lt h_s1i_closer) (Ne.symm h_s1i_ne)
                  rw [psiWeight_eq_sqrt2_div2_of_rev_gt n α₁ α₂ s1i.1 s1i.2
                    (by rw [hgt_s1i]; simp [not_lt.mpr h_s1i_f.le])
                    (by rw [hgt_s1i_r]; simp [h_s1i_f])]
                  linarith
                · -- s1 is F
                  rw [psiWeight_eq_sqrt2_div2_of_rev_gt n α₁ α₂ s1.1 s1.2
                    (by rw [hgt_s1]; simp [not_lt.mpr hs1_lt.le])
                    (by rw [hgt_s1_r]; simp [hs1_lt])]
                  linarith
              calc (psiWeight n α₁ α₂ s2.1 s2.2 + psiWeight n α₁ α₂ s2i.1 s2i.2) +
                  (psiWeight n α₁ α₂ s1.1 s1.2 + psiWeight n α₁ α₂ s1i.1 s1i.2)
                  ≤ (1 + √2 / 2) + (1 + √2 / 2) := add_le_add hp1 hp2
                _ = 2 + √2 := by ring
                _ ≤ 5 * √2 / 2 := by nlinarith [sq_nonneg (3 * √2 - 4)]

/-- When `2(d₁+d₂) = n` (even `n`, `d₁+d₂ = n/2` exactly): `cos²(πd₁/n) + cos²(πd₂/n) = 1`.
    Follows from `d₂ = n/2 - d₁`, giving `cos(πd₂/n) = sin(πd₁/n)`. -/
theorem cos_sq_sum_eq_one_of_double_eq (n α₁ α₂ : ℕ) (hn : 0 < n)
    (hα₁ : α₁ < n) (hα₂ : α₂ < n)
    (hdb : 2 * (zmodDist n α₁ + zmodDist n α₂) = n) :
    |cos (↑π * ↑α₁ / ↑n)| ^ 2 + |cos (↑π * ↑α₂ / ↑n)| ^ 2 = 1 := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  rw [abs_cos_eq_cos_zmodDist n α₁ hα₁ hn, abs_cos_eq_cos_zmodDist n α₂ hα₂ hn]
  set d₁ := zmodDist n α₁
  set d₂ := zmodDist n α₂
  -- d₂ = n/2 - d₁, so πd₂/n = π/2 - πd₁/n
  have hd₂_eq : (d₂ : ℝ) = n / 2 - d₁ := by
    have : (2 : ℝ) * (↑d₁ + ↑d₂) = ↑n := by exact_mod_cast hdb
    linarith
  rw [show π * (d₂ : ℝ) / n = π / 2 - π * d₁ / n from by
    rw [hd₂_eq]; field_simp]
  rw [cos_pi_div_two_sub, add_comm]
  exact sin_sq_add_cos_sq _

/-- Inside the diamond, when pair sums exceed `5√2/2`, the cosine squared sum is at most 1.
    Proof: excess contradicts `strict_diamond_pair_sum_le`, so `2(d₁+d₂) = n`,
    and then `cos_sq_sum_eq_one_of_double_eq` gives `cos² = 1 ≤ 1`. -/
theorem diamond_excess_cos_sq_le_one (n α₁ α₂ : ℕ) (hn : 3 ≤ n)
    (hα₁ : α₁ < n) (hα₂ : α₂ < n) (hne : ¬(α₁ = 0 ∧ α₂ = 0))
    (hdiam : zmodDist n α₁ + zmodDist n α₂ ≤ n / 2)
    (hexcess : 5 * √2 / 2 <
      (psiWeight n α₁ α₂ (shearS2 n α₁ α₂).1 (shearS2 n α₁ α₂).2 +
       psiWeight n α₁ α₂ (shearS2Inv n α₁ α₂).1 (shearS2Inv n α₁ α₂).2) +
      (psiWeight n α₁ α₂ (shearS1 n α₁ α₂).1 (shearS1 n α₁ α₂).2 +
       psiWeight n α₁ α₂ (shearS1Inv n α₁ α₂).1 (shearS1Inv n α₁ α₂).2)) :
    |cos (↑π * ↑α₁ / ↑n)| ^ 2 + |cos (↑π * ↑α₂ / ↑n)| ^ 2 ≤ 1 := by
  -- 2(d₁+d₂) ≥ n, since otherwise strict_diamond_pair_sum_le contradicts excess
  have h2d : ¬ (2 * (zmodDist n α₁ + zmodDist n α₂) + 1 ≤ n) := by
    intro hstrict
    have hle := strict_diamond_pair_sum_le n α₁ α₂ hn hα₁ hα₂ hne hstrict
    linarith
  -- 2(d₁+d₂) ≤ n from diamond: d₁+d₂ ≤ n/2 → 2(d₁+d₂) ≤ 2(n/2) ≤ n
  have h2d_le : 2 * (zmodDist n α₁ + zmodDist n α₂) ≤ n := by
    have hd₁ := zmodDist_le_half n α₁ hα₁
    have hd₂ := zmodDist_le_half n α₂ hα₂
    omega
  -- So 2(d₁+d₂) = n
  have h2d_eq : 2 * (zmodDist n α₁ + zmodDist n α₂) = n := by omega
  rw [cos_sq_sum_eq_one_of_double_eq n α₁ α₂ (by omega) hα₁ hα₂ h2d_eq]

/-- Inside the diamond, the pointwise condition (*) holds.
    Proof structure:
    1. No CC inside diamond (each pair ≤ `1+√2`).
    2. If pair_sum ≤ `5√2/2`: direct bound using `|cos| ≤ 1`.
    3. If pair_sum > `5√2/2`: Cauchy-Schwarz with `cos² ≤ 1` and
       `pair² ≤ 2(1+√2)² = 6+4√2 < 25/2`. -/
theorem diamond_psi_bound (n α₁ α₂ : ℕ) (hn : 3 ≤ n)
    (hα₁ : α₁ < n) (hα₂ : α₂ < n) (hne : ¬(α₁ = 0 ∧ α₂ = 0))
    (hdiam : zmodDist n α₁ + zmodDist n α₂ ≤ n / 2) :
    pointwiseCondition n α₁ α₂ := by
  unfold pointwiseCondition
  simp only
  set s1 := shearS1 n α₁ α₂
  set s1i := shearS1Inv n α₁ α₂
  set s2 := shearS2 n α₁ α₂
  set s2i := shearS2Inv n α₁ α₂
  set pair₁ := psiWeight n α₁ α₂ s2.1 s2.2 + psiWeight n α₁ α₂ s2i.1 s2i.2
  set pair₂ := psiWeight n α₁ α₂ s1.1 s1.2 + psiWeight n α₁ α₂ s1i.1 s1i.2
  set c₁ := |cos (↑π * ↑α₁ / ↑n)|
  set c₂ := |cos (↑π * ↑α₂ / ↑n)|
  have hc₁_le : c₁ ≤ 1 := abs_cos_le_one _
  have hc₂_le : c₂ ≤ 1 := abs_cos_le_one _
  have hc₁ : 0 ≤ c₁ := abs_nonneg _
  have hc₂ : 0 ≤ c₂ := abs_nonneg _
  have hp₁ : 0 ≤ pair₁ := add_nonneg (psiWeight_pos n α₁ α₂ s2.1 s2.2).le
    (psiWeight_pos n α₁ α₂ s2i.1 s2i.2).le
  have hp₂ : 0 ≤ pair₂ := add_nonneg (psiWeight_pos n α₁ α₂ s1.1 s1.2).le
    (psiWeight_pos n α₁ α₂ s1i.1 s1i.2).le
  -- √2 facts
  have hsq2 : (√2 : ℝ) ^ 2 = 2 := sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  have hpos : (0:ℝ) < √2 := sqrt_pos.mpr (by norm_num)
  -- S₂ preserves first coordinate, S₁ preserves second
  have hs1_snd : s1.2 = α₂ := shearS1_snd n α₁ α₂
  have hs1i_snd : s1i.2 = α₂ := shearS1Inv_snd n α₁ α₂
  have hs2_fst : s2.1 = α₁ := shearS2_fst n α₁ α₂
  have hs2i_fst : s2i.1 = α₁ := shearS2Inv_fst n α₁ α₂
  -- Rewrite zmodDistGt using coordinate preservation
  have hgt_s2 : zmodDistGt n α₁ α₂ s2.1 s2.2 = decide (zmodDist n s2.2 < zmodDist n α₂) := by
    rw [hs2_fst]; exact zmodDistGt_of_fst_eq n α₁ α₂ s2.2
  have hgt_s2i : zmodDistGt n α₁ α₂ s2i.1 s2i.2 = decide (zmodDist n s2i.2 < zmodDist n α₂) := by
    rw [hs2i_fst]; exact zmodDistGt_of_fst_eq n α₁ α₂ s2i.2
  have hgt_s1 : zmodDistGt n α₁ α₂ s1.1 s1.2 = decide (zmodDist n s1.1 < zmodDist n α₁) := by
    rw [hs1_snd]; exact zmodDistGt_of_snd_eq n α₁ α₂ s1.1
  have hgt_s1i : zmodDistGt n α₁ α₂ s1i.1 s1i.2 = decide (zmodDist n s1i.1 < zmodDist n α₁) := by
    rw [hs1i_snd]; exact zmodDistGt_of_snd_eq n α₁ α₂ s1i.1
  -- No CC inside diamond: at most one S₂ neighbor is closer
  have h_no_cc_s2 := diamond_no_both_S2_closer n α₁ α₂ hn hα₁ hα₂ hdiam
  have h_no_cc_s1 := diamond_no_both_S1_closer n α₁ α₂ hn hα₁ hα₂ hdiam
  -- Each pair ≤ 1 + √2 (at least one ψ ≤ 1 per pair, since no CC)
  have hpair₁_le : pair₁ ≤ 1 + √2 := by
    rcases not_and_or.mp h_no_cc_s2 with h | h
    · have := psiWeight_le_one_of_not_gt n α₁ α₂ s2.1 s2.2
        (by rw [hgt_s2]; exact decide_eq_false h)
      linarith [psiWeight_le_sqrt2 n α₁ α₂ s2i.1 s2i.2]
    · have := psiWeight_le_one_of_not_gt n α₁ α₂ s2i.1 s2i.2
        (by rw [hgt_s2i]; exact decide_eq_false h)
      linarith [psiWeight_le_sqrt2 n α₁ α₂ s2.1 s2.2]
  have hpair₂_le : pair₂ ≤ 1 + √2 := by
    rcases not_and_or.mp h_no_cc_s1 with h | h
    · have := psiWeight_le_one_of_not_gt n α₁ α₂ s1.1 s1.2
        (by rw [hgt_s1]; exact decide_eq_false h)
      linarith [psiWeight_le_sqrt2 n α₁ α₂ s1i.1 s1i.2]
    · have := psiWeight_le_one_of_not_gt n α₁ α₂ s1i.1 s1i.2
        (by rw [hgt_s1i]; exact decide_eq_false h)
      linarith [psiWeight_le_sqrt2 n α₁ α₂ s1.1 s1.2]
  -- Split on pair sum
  by_cases hsum : pair₁ + pair₂ ≤ 5 * √2 / 2
  · -- Direct bound: LHS ≤ 1·pair₁ + 1·pair₂ = pair_sum ≤ 5√2/2
    calc c₁ * pair₁ + c₂ * pair₂
        ≤ 1 * pair₁ + 1 * pair₂ := by nlinarith
      _ = pair₁ + pair₂ := by ring
      _ ≤ 5 * √2 / 2 := hsum
  · -- Cauchy-Schwarz case: pair_sum > 5√2/2
    push Not at hsum
    -- cos² ≤ 1 for excess cases
    have hcos_sq : c₁ ^ 2 + c₂ ^ 2 ≤ 1 :=
      diamond_excess_cos_sq_le_one n α₁ α₂ hn hα₁ hα₂ hne hdiam (by linarith)
    -- pair₁² + pair₂² ≤ 2(1+√2)² = 6+4√2 < 25/2
    have hpair_sq : pair₁ ^ 2 + pair₂ ^ 2 ≤ 25 / 2 := by
      have h1 : pair₁ ^ 2 ≤ (1 + √2) ^ 2 := by nlinarith [sq_nonneg (pair₁ - (1 + √2))]
      have h2 : pair₂ ^ 2 ≤ (1 + √2) ^ 2 := by nlinarith [sq_nonneg (pair₂ - (1 + √2))]
      nlinarith [sq_nonneg (√2 * 8 - 13)]
    -- CS: c₁p₁ + c₂p₂ ≤ √(c²) · √(p²) ≤ √1 · √(25/2) = 5√2/2
    have hCS := cauchy_schwarz_two c₁ c₂ pair₁ pair₂ hc₁ hc₂ hp₁ hp₂
    have hn' : 0 < n := by omega
    have h25 : √(25 / 2 : ℝ) = 5 * √2 / 2 := by
      rw [show (25 : ℝ) / 2 = (5 * √2 / 2) ^ 2 from by nlinarith]
      exact sqrt_sq (by positivity)
    calc c₁ * pair₁ + c₂ * pair₂
        ≤ √(c₁ ^ 2 + c₂ ^ 2) * √(pair₁ ^ 2 + pair₂ ^ 2) := hCS
      _ ≤ √1 * √(25 / 2) := by
          apply mul_le_mul (Real.sqrt_le_sqrt hcos_sq) (Real.sqrt_le_sqrt hpair_sq)
            (sqrt_nonneg _) (sqrt_nonneg _)
      _ = 5 * √2 / 2 := by rw [sqrt_one, one_mul, h25]

/-- Outside the diamond, the pointwise condition (*) holds.
    Uses Cauchy-Schwarz on ℝ²: `cos₁·p₁ + cos₂·p₂ ≤ √(cos₁²+cos₂²)·√(p₁²+p₂²) ≤ 1·5√2/2`.
    Relies on `cos_sq_sum_le_one` (cos₁²+cos₂² ≤ 1) and `pair_sq_sum_le_outside` (p₁²+p₂² ≤ 25/2). -/
theorem outside_diamond_psi_bound (n α₁ α₂ : ℕ) (hn : 3 ≤ n)
    (hα₁ : α₁ < n) (hα₂ : α₂ < n)
    (hout : n / 2 < zmodDist n α₁ + zmodDist n α₂) :
    pointwiseCondition n α₁ α₂ := by
  unfold pointwiseCondition
  simp only
  -- Name the pair sums
  set s1 := shearS1 n α₁ α₂
  set s1i := shearS1Inv n α₁ α₂
  set s2 := shearS2 n α₁ α₂
  set s2i := shearS2Inv n α₁ α₂
  set pair₁ := psiWeight n α₁ α₂ s2.1 s2.2 + psiWeight n α₁ α₂ s2i.1 s2i.2
  set pair₂ := psiWeight n α₁ α₂ s1.1 s1.2 + psiWeight n α₁ α₂ s1i.1 s1i.2
  set c₁ := |cos (↑π * ↑α₁ / ↑n)|
  set c₂ := |cos (↑π * ↑α₂ / ↑n)|
  have hc₁ : 0 ≤ c₁ := abs_nonneg _
  have hc₂ : 0 ≤ c₂ := abs_nonneg _
  have hp₁ : 0 ≤ pair₁ := add_nonneg (psiWeight_pos n α₁ α₂ s2.1 s2.2).le
    (psiWeight_pos n α₁ α₂ s2i.1 s2i.2).le
  have hp₂ : 0 ≤ pair₂ := add_nonneg (psiWeight_pos n α₁ α₂ s1.1 s1.2).le
    (psiWeight_pos n α₁ α₂ s1i.1 s1i.2).le
  have hn' : 0 < n := by omega
  -- Cauchy-Schwarz: c₁·p₁ + c₂·p₂ ≤ √(c₁²+c₂²) · √(p₁²+p₂²)
  have hCS := cauchy_schwarz_two c₁ c₂ pair₁ pair₂ hc₁ hc₂ hp₁ hp₂
  have hcos_sq := cos_sq_sum_le_one n α₁ α₂ hn' hα₁ hα₂ hout
  have hpair_sq := pair_sq_sum_le_outside n α₁ α₂ hn hα₁ hα₂
  -- √(c²) ≤ √1 = 1 and √(p²) ≤ √(25/2) = 5√2/2
  have hsq2 : (0 : ℝ) < √2 := sqrt_pos.mpr (by norm_num : (0:ℝ) < 2)
  have hsq2_sq : (√2 : ℝ) ^ 2 = 2 := sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  -- √(25/2) = 5/(√2) = 5√2/2
  have h25 : √(25 / 2 : ℝ) = 5 * √2 / 2 := by
    rw [show (25 : ℝ) / 2 = (5 * √2 / 2) ^ 2 from by nlinarith]
    exact sqrt_sq (by positivity)
  calc c₁ * pair₁ + c₂ * pair₂
      ≤ √(c₁ ^ 2 + c₂ ^ 2) * √(pair₁ ^ 2 + pair₂ ^ 2) := hCS
    _ ≤ √1 * √(25 / 2) := by
        apply mul_le_mul (Real.sqrt_le_sqrt hcos_sq) (Real.sqrt_le_sqrt hpair_sq)
          (sqrt_nonneg _) (sqrt_nonneg _)
    _ = 5 * √2 / 2 := by rw [sqrt_one, one_mul, h25]

/-- The pointwise condition holds for all nonzero `α ∈ (Z/nZ)²`.
    Combines `diamond_psi_bound` (inside) and `outside_diamond_psi_bound` (outside). -/
theorem pointwiseCondition_forall (n α₁ α₂ : ℕ) (hn : 3 ≤ n)
    (hα₁ : α₁ < n) (hα₂ : α₂ < n) (hne : ¬(α₁ = 0 ∧ α₂ = 0)) :
    pointwiseCondition n α₁ α₂ := by
  by_cases hdiam : zmodDist n α₁ + zmodDist n α₂ ≤ n / 2
  · exact diamond_psi_bound n α₁ α₂ hn hα₁ hα₂ hne hdiam
  · exact outside_diamond_psi_bound n α₁ α₂ hn hα₁ hα₂ (by omega)

end GaloisForLFunctions.HTGeometry.MGGResidueBounds
