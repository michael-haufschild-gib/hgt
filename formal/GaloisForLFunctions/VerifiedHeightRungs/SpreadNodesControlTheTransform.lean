import GaloisForLFunctions.VerifiedHeightRungs.SeparatedNodesControlTheTransform

/-!
# Nodes spread around a point control the transform there

`norm_paperFT_le_of_nodes` expands the transform `Φ` of `f` at the origin and reads the Taylor polynomial off
nodes on one side. Modulating `f` by `e^{ixu}` moves the expansion point to an arbitrary `x`, since
`Φ_{f e^{ix·}}(y) = Φ_f(x + y)`. Hence: if `n + 1` nodes are pairwise `nodeStep a`-separated
(`|v_i − v_j| ≥ nodeStep a · |i − j|`) and lie within `3(n+1)·nodeStep a` of `x`, then

  `|Φ(x)| ≤ 48ⁿ Σ_j |Φ(v_j)| + ‖f‖₁ 48^{−2n}` (`norm_paperFT_le_of_spread_nodes`),

and `|Φ(x)|² ≤ 2(n+1) 48^{2n} Σ_j |Φ(v_j)|² + 2 (‖f‖₁ 48^{−2n})²` (`norm_sq_paperFT_le_of_spread_nodes`).
The nodes may sit on both sides of `x`; only their spacing and their distance to `x` matter.
-/

open Finset Polynomial
open scoped Nat

namespace GaloisForLFunctions.VerifiedHeightRungs

open _root_.RHTower Zeta23

noncomputable section

/-- The test modulated to the frequency `x`. -/
def modulate (f : ℝ → ℂ) (x : ℝ) (u : ℝ) : ℂ := f u * Complex.exp (Complex.I * x * u)

theorem paperFT_modulate (f : ℝ → ℂ) (x y : ℝ) :
    paperFT (modulate f x) y = paperFT f ((x + y : ℝ) : ℂ) := by
  rw [paperFT_def, paperFT_def]
  congr 1
  funext u
  unfold modulate
  rw [mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

theorem norm_modulate (f : ℝ → ℂ) (x u : ℝ) : ‖modulate f x u‖ = ‖f u‖ := by
  unfold modulate
  rw [norm_mul, show Complex.I * (x : ℂ) * (u : ℂ) = ((x * u : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I, mul_one]

theorem continuous_modulate {f : ℝ → ℂ} (hf : Continuous f) (x : ℝ) : Continuous (modulate f x) := by
  unfold modulate
  fun_prop

theorem hasCompactSupport_modulate {f : ℝ → ℂ} (hfc : HasCompactSupport f) (x : ℝ) :
    HasCompactSupport (modulate f x) :=
  hfc.mul_right (f' := fun u : ℝ => Complex.exp (Complex.I * x * u))

/-- **Spread nodes control the transform at a point.** -/
theorem norm_paperFT_le_of_spread_nodes {f : ℝ → ℂ} {a : ℝ} (ha : 0 < a) (hf : Continuous f)
    (hfc : HasCompactSupport f) (hsupp : ∀ u, f u ≠ 0 → |u| ≤ a) {n : ℕ} (v : ℕ → ℝ) {x : ℝ}
    (hsep : ∀ i ∈ range (n + 1), ∀ j ∈ range (n + 1), nodeStep a * |(i : ℝ) - j| ≤ |v i - v j|)
    (hnear : ∀ j ∈ range (n + 1), |v j - x| ≤ 3 * ((n : ℝ) + 1) * nodeStep a) :
    ‖paperFT f x‖ ≤ 48 ^ n * ∑ j ∈ range (n + 1), ‖paperFT f (v j)‖ +
      (∫ u, ‖f u‖) * ((48 : ℝ) ^ (2 * n))⁻¹ := by
  set g := modulate f x with hgdef
  have hg : Continuous g := continuous_modulate hf x
  have hgc : HasCompactSupport g := hasCompactSupport_modulate hfc x
  have hgs : ∀ u, g u ≠ 0 → |u| ≤ a := fun u hu => hsupp u fun h0 => hu (by simp [hgdef, modulate, h0])
  have hnorm : ∫ u, ‖g u‖ = ∫ u, ‖f u‖ := by simp only [hgdef, norm_modulate]
  have hσ := nodeStep_pos ha
  obtain ⟨σ, hσdef⟩ : ∃ σ, σ = nodeStep a := ⟨_, rfl⟩
  rw [← hσdef] at hσ hsep hnear
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hF0 : 0 ≤ ∫ u, ‖f u‖ := MeasureTheory.integral_nonneg fun _ => norm_nonneg _
  set w : ℕ → ℝ := fun j => v j - x with hwdef
  have hΦx : paperFT g ((0 : ℝ) : ℂ) = paperFT f x := by rw [paperFT_modulate, add_zero]
  have hΦw : ∀ j, paperFT g (w j) = paperFT f (v j) := fun j => by
    rw [paperFT_modulate, hwdef]
    congr 2
    ring
  have hsepw : ∀ i ∈ range (n + 1), ∀ j ∈ range (n + 1), σ * |(i : ℝ) - j| ≤ |w i - w j| := by
    intro i hi j hj
    rw [hwdef, show v i - x - (v j - x) = v i - v j by ring]
    exact hsep i hi j hj
  have hw0 : ∀ i ∈ range (n + 1), ‖((0 : ℝ) : ℂ) - (w i : ℂ)‖ ≤ 4 * ((n : ℝ) + 1) * σ := by
    intro i hi
    rw [show ((0 : ℝ) : ℂ) - (w i : ℂ) = ((-(w i) : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_neg]
    have := hnear i hi
    nlinarith only [this, hσ]
  have hL := norm_eval_le_of_nodes (taylorPoly g n) (natDegree_taylorPoly_le g n) hσ w hsepw hw0
  obtain ⟨d, hd⟩ : ∃ d, d = (∫ u, ‖f u‖) * (2 * ((48 ^ 4 : ℝ)⁻¹) ^ (n + 1)) := ⟨_, rfl⟩
  have hd0 : 0 ≤ d := by rw [hd]; positivity
  have hT0 : ‖paperFT g ((0 : ℝ) : ℂ) - (taylorPoly g n).eval ((0 : ℝ) : ℂ)‖ ≤ d := by
    rw [hd, ← hnorm]
    refine norm_paperFT_sub_taylor_le_of_step ha hg hgc hgs ?_
    rw [abs_zero, ← hσdef]
    positivity
  have hvT : ∀ j ∈ range (n + 1), ‖(taylorPoly g n).eval (w j : ℂ)‖ ≤ ‖paperFT f (v j)‖ + d := by
    intro j hj
    have h := norm_paperFT_sub_taylor_le_of_step ha hg hgc hgs (n := n) (y := w j) (by
      rw [← hσdef]
      exact hnear j hj)
    rw [hnorm, ← hd, hΦw] at h
    have h2 := norm_sub_norm_le ((taylorPoly g n).eval (w j : ℂ)) (paperFT f (v j))
    rw [norm_sub_rev] at h2
    linarith only [h, h2]
  have h48 : (1 : ℝ) ≤ 48 ^ n := one_le_pow₀ (by norm_num)
  have hsum : ∑ j ∈ range (n + 1), ‖(taylorPoly g n).eval (w j : ℂ)‖ ≤
      ∑ j ∈ range (n + 1), ‖paperFT f (v j)‖ + ((n : ℝ) + 1) * d := by
    refine (sum_le_sum hvT).trans (le_of_eq ?_)
    rw [sum_add_distrib, sum_const, card_range, nsmul_eq_mul]
    push_cast
    ring
  have hP : ‖paperFT f x‖ ≤ d + ‖(taylorPoly g n).eval ((0 : ℝ) : ℂ)‖ := by
    rw [hΦx] at hT0
    have := norm_sub_norm_le (paperFT f x) ((taylorPoly g n).eval ((0 : ℝ) : ℂ))
    linarith only [this, hT0]
  have hnpow : (n : ℝ) + 1 ≤ 48 ^ n := by
    have h := one_add_mul_le_pow (a := (47 : ℝ)) (by norm_num) n
    norm_num at h
    nlinarith only [h, hn0]
  have hadd : d * (1 + 48 ^ n * ((n : ℝ) + 1)) ≤ (∫ u, ‖f u‖) * ((48 : ℝ) ^ (2 * n))⁻¹ := by
    rw [hd, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hF0
    have h1 : 1 + (48 : ℝ) ^ n * ((n : ℝ) + 1) ≤ 2 * 48 ^ (2 * n) := by
      have e : (48 : ℝ) ^ (2 * n) = 48 ^ n * 48 ^ n := by rw [two_mul, pow_add]
      rw [e]
      nlinarith only [hnpow, h48]
    have h2 : ((48 ^ 4 : ℝ)⁻¹) ^ (n + 1) * (4 * 48 ^ (2 * n)) ≤ ((48 : ℝ) ^ (2 * n))⁻¹ := by
      have hpos : (0 : ℝ) < 48 ^ (2 * n) := by positivity
      rw [inv_pow, ← div_eq_inv_mul, div_le_iff₀ (by positivity), ← div_eq_inv_mul,
        le_div_iff₀ hpos]
      have e : ((48 : ℝ) ^ 4) ^ (n + 1) = 48 ^ (2 * n) * 48 ^ (2 * n) * 48 ^ 4 := by
        rw [← pow_mul, ← pow_add, ← pow_add]
        congr 1
        ring
      rw [e]
      have : (1 : ℝ) ≤ 48 ^ (2 * n) := one_le_pow₀ (by norm_num)
      nlinarith only [mul_pos hpos hpos]
    calc
      2 * ((48 ^ 4 : ℝ)⁻¹) ^ (n + 1) * (1 + 48 ^ n * ((n : ℝ) + 1))
          ≤ 2 * ((48 ^ 4 : ℝ)⁻¹) ^ (n + 1) * (2 * 48 ^ (2 * n)) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = ((48 ^ 4 : ℝ)⁻¹) ^ (n + 1) * (4 * 48 ^ (2 * n)) := by ring
      _ ≤ _ := h2
  have hL' : ‖(taylorPoly g n).eval ((0 : ℝ) : ℂ)‖ ≤
      48 ^ n * ∑ j ∈ range (n + 1), ‖(taylorPoly g n).eval (w j : ℂ)‖ := hL
  calc
    ‖paperFT f x‖ ≤ d + 48 ^ n * (∑ j ∈ range (n + 1), ‖paperFT f (v j)‖ + ((n : ℝ) + 1) * d) :=
      hP.trans (add_le_add le_rfl (hL'.trans (mul_le_mul_of_nonneg_left hsum (by positivity))))
    _ = 48 ^ n * ∑ j ∈ range (n + 1), ‖paperFT f (v j)‖ + d * (1 + 48 ^ n * ((n : ℝ) + 1)) := by
      ring
    _ ≤ _ := add_le_add le_rfl hadd

/-- **Squared form.** -/
theorem norm_sq_paperFT_le_of_spread_nodes {f : ℝ → ℂ} {a : ℝ} (ha : 0 < a) (hf : Continuous f)
    (hfc : HasCompactSupport f) (hsupp : ∀ u, f u ≠ 0 → |u| ≤ a) {n : ℕ} (v : ℕ → ℝ) {x : ℝ}
    (hsep : ∀ i ∈ range (n + 1), ∀ j ∈ range (n + 1), nodeStep a * |(i : ℝ) - j| ≤ |v i - v j|)
    (hnear : ∀ j ∈ range (n + 1), |v j - x| ≤ 3 * ((n : ℝ) + 1) * nodeStep a) :
    ‖paperFT f x‖ ^ 2 ≤ 2 * ((n : ℝ) + 1) * ((48 : ℝ) ^ n) ^ 2 *
        ∑ j ∈ range (n + 1), ‖paperFT f (v j)‖ ^ 2 +
      2 * ((∫ u, ‖f u‖) * ((48 : ℝ) ^ (2 * n))⁻¹) ^ 2 := by
  have h := norm_paperFT_le_of_spread_nodes ha hf hfc hsupp v hsep hnear
  obtain ⟨A, hA⟩ : ∃ A, A = ∑ j ∈ range (n + 1), ‖paperFT f (v j)‖ := ⟨_, rfl⟩
  rw [← hA] at h
  have hCS := sq_sum_le_card_mul_sum_sq (s := range (n + 1)) (f := fun j => ‖paperFT f (v j)‖)
  rw [← hA, card_range] at hCS
  push_cast at hCS
  obtain ⟨B, hB⟩ : ∃ B, B = (∫ u, ‖f u‖) * ((48 : ℝ) ^ (2 * n))⁻¹ := ⟨_, rfl⟩
  rw [← hB] at h ⊢
  have h0 : 0 ≤ ‖paperFT f x‖ := norm_nonneg _
  have hsq : ‖paperFT f x‖ ^ 2 ≤ (48 ^ n * A + B) ^ 2 := pow_le_pow_left₀ h0 h 2
  have h2 : (48 ^ n * A + B) ^ 2 ≤ 2 * (48 ^ n * A) ^ 2 + 2 * B ^ 2 := by
    nlinarith only [sq_nonneg ((48 : ℝ) ^ n * A - B)]
  have h3 : (48 ^ n * A) ^ 2 ≤
      ((48 : ℝ) ^ n) ^ 2 * (((n : ℝ) + 1) * ∑ j ∈ range (n + 1), ‖paperFT f (v j)‖ ^ 2) := by
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_left hCS (sq_nonneg _)
  nlinarith only [hsq, h2, h3]

end

end GaloisForLFunctions.VerifiedHeightRungs
