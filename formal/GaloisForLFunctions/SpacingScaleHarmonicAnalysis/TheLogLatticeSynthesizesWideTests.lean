import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.WeilsFormIsContinuousInTheLevyNorm

/-!
# The log-lattice synthesizes wide tests

Narrow atoms at the points `log n` can rebuild a fixed wide test. Let the cells of a partition
`a₀ < a₁ < … < a_K` carry the weights `x_k = ∫_{a_k}^{a_{k+1}} F` of a test `F`, and put a copy of a
narrow bump `ψ` at each node: `S(r) = Σ_k x_k ψ(r − a_k)`.

* **Cell lemma** (`abs_cellSum_sub_le`): `|S(r) − ∫ F(t) ψ(r − t) dt| ≤ ‖F‖_∞ · h · ‖ψ′‖₁`, where `h` is
  the largest gap. On each cell `|ψ(r − a_k) − ψ(r − t)| ≤ ∫_{cell} |ψ′(r − s)| ds`, and the cells are
  disjoint, so the error carries the `L¹` norm of `ψ′`, not its supremum.
* **The log-lattice** (`logNode`, `logNode_gap_le`): the nodes `a_k = log(n₀ + k) − c` have gaps at
  most `1/n₀`.
* **Dilated bumps** (`dilate`): `φ_k(s) = k φ(ks)` has `∫ φ_k = ∫ φ`, `‖φ_k′‖₁ = k ‖φ′‖₁`, and its first
  moment is at most `1/k` times that of `φ` for a profile supported in `[−1, 1]`.

For a narrow bump of width `1/k` this gives an error `O(k/n₀)` in the supremum, so the atoms near
height `n₀` synthesize a fixed test as soon as `k = o(n₀)`: widths `N^{−θ}` with `θ < 1`.
-/

noncomputable section

open MeasureTheory Set intervalIntegral
open scoped Real

namespace GaloisForLFunctions.SpacingScaleHarmonicAnalysis

/-! ### The cell lemma -/

/-- The cell weight `∫_{a_k}^{a_{k+1}} F`. -/
def cellWeight (F : ℝ → ℝ) (a : ℕ → ℝ) (k : ℕ) : ℝ := ∫ t in a k..a (k + 1), F t

/-- The synthesis `S(r) = Σ_{k < K} x_k ψ(r − a_k)`. -/
def cellSum (F ψ : ℝ → ℝ) (a : ℕ → ℝ) (K : ℕ) (r : ℝ) : ℝ :=
  ∑ k ∈ Finset.range K, cellWeight F a k * ψ (r - a k)

/-- On a cell, `|ψ(r − a) − ψ(r − t)| ≤ ∫_a^b |ψ′(r − s)| ds` for `a ≤ t ≤ b`. -/
theorem abs_sub_le_integral_deriv {ψ ψ' : ℝ → ℝ} (hψ : ∀ s, HasDerivAt ψ (ψ' s) s)
    (hψ' : Continuous ψ') (r : ℝ) {a b t : ℝ} (hat : a ≤ t) (htb : t ≤ b) :
    |ψ (r - a) - ψ (r - t)| ≤ ∫ s in a..b, |ψ' (r - s)| := by
  -- `s ↦ −ψ(r − s)` has derivative `ψ′(r − s)`
  have hd : ∀ s ∈ uIcc a t, HasDerivAt (fun s => -ψ (r - s)) (ψ' (r - s)) s := fun s _ => by
    have h2 := ((hψ (r - s)).comp s ((hasDerivAt_id s).const_sub r)).neg
    exact h2.congr_deriv (by simp)
  have hc : Continuous fun s => ψ' (r - s) := hψ'.comp (continuous_const.sub continuous_id)
  have hftc := integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable a t)
  have e : ψ (r - a) - ψ (r - t) = ∫ s in a..t, ψ' (r - s) := by rw [hftc]; ring
  rw [e]
  calc |∫ s in a..t, ψ' (r - s)| ≤ ∫ s in a..t, |ψ' (r - s)| :=
        abs_integral_le_integral_abs hat
    _ ≤ ∫ s in a..b, |ψ' (r - s)| :=
        integral_mono_interval le_rfl hat htb (Filter.Eventually.of_forall fun s => abs_nonneg _)
          (hc.abs.intervalIntegrable a b)

/-- **The cell lemma**: `|Σ_k x_k ψ(r − a_k) − ∫ F(t) ψ(r − t) dt| ≤ M h ‖ψ′‖₁` for `F` supported in
`[a₀, a_K]`, `|F| ≤ M`, gaps at most `h`. -/
theorem abs_cellSum_sub_le {F ψ ψ' : ℝ → ℝ} {a : ℕ → ℝ} {K : ℕ} {h M : ℝ}
    (ha : Monotone a) (hh : 0 ≤ h) (hgap : ∀ k < K, a (k + 1) - a k ≤ h) (hF : Continuous F)
    (hFM : ∀ t, |F t| ≤ M) (hFsupp : ∀ t, t ∉ Icc (a 0) (a K) → F t = 0)
    (hψ : ∀ s, HasDerivAt ψ (ψ' s) s) (hψc : Continuous ψ) (hψ' : Continuous ψ')
    (hψ'int : Integrable ψ') (r : ℝ) :
    |cellSum F ψ a K r - ∫ t, F t * ψ (r - t)| ≤ M * h * ∫ s, |ψ' s| := by
  have hM : 0 ≤ M := (abs_nonneg _).trans (hFM 0)
  set g : ℝ → ℝ := fun t => F t * ψ (r - t)
  have hgc : Continuous g := hF.mul (hψc.comp (continuous_const.sub continuous_id))
  -- the integral is the sum of the cell integrals
  have hsupp : ∫ t, g t = ∫ t in a 0..a K, g t := by
    rw [intervalIntegral.integral_of_le (ha (Nat.zero_le K)), ← integral_Icc_eq_integral_Ioc]
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht => ?_).symm
    simp only [g, hFsupp t ht, zero_mul]
  have hcells : ∫ t in a 0..a K, g t = ∑ k ∈ Finset.range K, ∫ t in a k..a (k + 1), g t :=
    (sum_integral_adjacent_intervals fun k _ => hgc.intervalIntegrable _ _).symm
  -- the cell differences
  have hV : ∀ k < K, |cellWeight F a k * ψ (r - a k) - ∫ t in a k..a (k + 1), g t| ≤
      M * h * ∫ s in a k..a (k + 1), |ψ' (r - s)| := by
    intro k hk
    have hak : a k ≤ a (k + 1) := ha (Nat.le_succ k)
    set V := ∫ s in a k..a (k + 1), |ψ' (r - s)|
    have hV0 : 0 ≤ V := integral_nonneg hak fun s _ => abs_nonneg _
    have e : cellWeight F a k * ψ (r - a k) - ∫ t in a k..a (k + 1), g t =
        ∫ t in a k..a (k + 1), F t * (ψ (r - a k) - ψ (r - t)) := by
      unfold cellWeight
      rw [← intervalIntegral.integral_mul_const, ← intervalIntegral.integral_sub
        (f := fun t => F t * ψ (r - a k)) (g := g)
        ((hF.mul continuous_const).intervalIntegrable _ _) (hgc.intervalIntegrable _ _)]
      congr 1; funext t; simp only [g]; ring
    rw [e]
    calc |∫ t in a k..a (k + 1), F t * (ψ (r - a k) - ψ (r - t))|
        ≤ ∫ t in a k..a (k + 1), |F t * (ψ (r - a k) - ψ (r - t))| :=
          abs_integral_le_integral_abs hak
      _ ≤ ∫ t in a k..a (k + 1), M * V := by
          refine integral_mono_on hak
            ((hF.mul (continuous_const.sub (hψc.comp (continuous_const.sub continuous_id)))).abs.intervalIntegrable _ _)
            intervalIntegrable_const fun t ht => ?_
          rw [abs_mul]
          exact mul_le_mul (hFM t) (abs_sub_le_integral_deriv hψ hψ' r ht.1 ht.2) (abs_nonneg _) hM
      _ = (a (k + 1) - a k) * (M * V) := by rw [intervalIntegral.integral_const, smul_eq_mul]
      _ ≤ h * (M * V) := mul_le_mul_of_nonneg_right (hgap k hk) (by positivity)
      _ = M * h * V := by ring
  -- sum the cells
  have hsumV : ∑ k ∈ Finset.range K, ∫ s in a k..a (k + 1), |ψ' (r - s)| ≤ ∫ s, |ψ' s| := by
    have hcont : Continuous fun s => |ψ' (r - s)| :=
      (hψ'.comp (continuous_const.sub continuous_id)).abs
    rw [sum_integral_adjacent_intervals (f := fun s => |ψ' (r - s)|) fun k _ =>
      hcont.intervalIntegrable _ _]
    have hint : Integrable fun s => |ψ' (r - s)| := (hψ'int.comp_sub_left r).abs
    calc ∫ s in a 0..a K, |ψ' (r - s)| ≤ ∫ s, |ψ' (r - s)| := by
          rw [intervalIntegral.integral_of_le (ha (Nat.zero_le K))]
          exact setIntegral_le_integral hint (Filter.Eventually.of_forall fun s => abs_nonneg _)
      _ = ∫ s, |ψ' s| := integral_sub_left_eq_self (fun s => |ψ' s|) volume r
  have hMh : 0 ≤ M * h := mul_nonneg hM hh
  unfold cellSum
  rw [hsupp, hcells, ← Finset.sum_sub_distrib]
  calc |∑ k ∈ Finset.range K, (cellWeight F a k * ψ (r - a k) - ∫ t in a k..a (k + 1), g t)|
      ≤ ∑ k ∈ Finset.range K, |cellWeight F a k * ψ (r - a k) - ∫ t in a k..a (k + 1), g t| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range K, M * h * ∫ s in a k..a (k + 1), |ψ' (r - s)| :=
        Finset.sum_le_sum fun k hk => hV k (Finset.mem_range.mp hk)
    _ = M * h * ∑ k ∈ Finset.range K, ∫ s in a k..a (k + 1), |ψ' (r - s)| := by
        rw [Finset.mul_sum]
    _ ≤ M * h * ∫ s, |ψ' s| := mul_le_mul_of_nonneg_left hsumV hMh

/-! ### The convolution step -/

/-- **Convolution with a narrow probability profile**: if `∫ ψ = 1` and `ψ` lives in `[−ρ, ρ]`, then
`|∫ F(t) ψ(r − t) dt − F(r)| ≤ L ρ ‖ψ‖₁` for an `L`-Lipschitz `F`. -/
theorem abs_integral_mul_sub_le {F ψ : ℝ → ℝ} (hF : Continuous F) (hψ : Continuous ψ)
    (hψc : HasCompactSupport ψ) (hψ1 : ∫ s, ψ s = 1) {ρ L : ℝ}
    (hψρ : ∀ s, ρ < |s| → ψ s = 0) (hL : ∀ u v, |F u - F v| ≤ L * |u - v|) (r : ℝ) :
    |(∫ t, F t * ψ (r - t)) - F r| ≤ L * ρ * ∫ s, |ψ s| := by
  have hψi : Integrable ψ := hψ.integrable_of_hasCompactSupport hψc
  have hsub : ∫ t, F t * ψ (r - t) = ∫ s, F (r - s) * ψ s := by
    rw [← integral_sub_left_eq_self (fun t => F t * ψ (r - t)) volume r]
    simp only [sub_sub_cancel]
  have hint1 : Integrable fun s => F (r - s) * ψ s :=
    ((hF.comp (continuous_const.sub continuous_id)).mul hψ).integrable_of_hasCompactSupport
      hψc.mul_left
  have e : (∫ s, F (r - s) * ψ s) - F r = ∫ s, (F (r - s) - F r) * ψ s := by
    rw [show (fun s => (F (r - s) - F r) * ψ s) = fun s => F (r - s) * ψ s - F r * ψ s by
      funext s; ring, integral_sub hint1 (hψi.const_mul _), MeasureTheory.integral_const_mul, hψ1, mul_one]
  rw [hsub, e]
  have hρ0 : 0 ≤ ρ ∨ ∀ s, ψ s = 0 := by
    by_cases hρ : 0 ≤ ρ
    · exact Or.inl hρ
    · right; intro s; exact hψρ s (by linarith [abs_nonneg s])
  rcases hρ0 with hρ0 | hzero
  · calc |∫ s, (F (r - s) - F r) * ψ s| ≤ ∫ s, |(F (r - s) - F r) * ψ s| :=
          abs_integral_le_integral_abs
      _ ≤ ∫ s, L * ρ * |ψ s| := by
          have hint2 : Integrable fun s => (F (r - s) - F r) * ψ s :=
            (((hF.comp (continuous_const.sub continuous_id)).sub continuous_const).mul
              hψ).integrable_of_hasCompactSupport hψc.mul_left
          refine integral_mono hint2.abs ((hψi.abs).const_mul _) fun s => ?_
          rw [abs_mul]
          by_cases hs : ρ < |s|
          · rw [hψρ s hs, abs_zero, mul_zero, mul_zero]
          · push Not at hs
            have hL0 : 0 ≤ L := by
              have := hL 1 0
              simp at this
              linarith [abs_nonneg (F 1 - F 0)]
            have := hL (r - s) r
            rw [show r - s - r = -s by ring, abs_neg] at this
            exact mul_le_mul_of_nonneg_right (this.trans (mul_le_mul_of_nonneg_left hs hL0))
              (abs_nonneg _)
      _ = L * ρ * ∫ s, |ψ s| := MeasureTheory.integral_const_mul _ _
  · simp [hzero] at hψ1

/-! ### Derivatives of syntheses -/

theorem hasDerivAt_cellSum {F ψ ψ' : ℝ → ℝ} {a : ℕ → ℝ} {K : ℕ}
    (hψ : ∀ s, HasDerivAt ψ (ψ' s) s) (r : ℝ) :
    HasDerivAt (cellSum F ψ a K) (cellSum F ψ' a K r) r := by
  unfold cellSum
  have h : ∀ k ∈ Finset.range K, HasDerivAt (fun r => cellWeight F a k * ψ (r - a k))
      (cellWeight F a k * ψ' (r - a k)) r := fun k _ => by
    have := (hψ (r - a k)).comp r ((hasDerivAt_id r).sub_const (a k))
    simpa using this.const_mul (cellWeight F a k)
  exact HasDerivAt.fun_sum h

/-- **Mean value theorem**: a derivative bounded by `B` makes a function `B`-Lipschitz. -/
theorem abs_sub_le_of_hasDerivAt {f f' : ℝ → ℝ} (hf : ∀ r, HasDerivAt f (f' r) r) {B : ℝ}
    (hB : ∀ r, |f' r| ≤ B) (u v : ℝ) : |f u - f v| ≤ B * |u - v| := by
  have hd : Differentiable ℝ f := fun r => (hf r).differentiableAt
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (s := Set.univ) (fun r _ => hd r)
    (fun r _ => by rw [(hf r).deriv, Real.norm_eq_abs]; exact hB r) convex_univ (mem_univ v)
    (mem_univ u)
  simpa [Real.norm_eq_abs] using h

/-! ### The log-lattice -/

/-- The log-lattice nodes `a_j = log(n₀ + j) − c`. -/
def logNode (n₀ : ℕ) (c : ℝ) (j : ℕ) : ℝ := Real.log ((n₀ + j : ℕ) : ℝ) - c

theorem logNode_monotone {n₀ : ℕ} (hn₀ : 1 ≤ n₀) (c : ℝ) : Monotone (logNode n₀ c) := by
  intro i j hij
  unfold logNode
  have hi : (0 : ℝ) < ((n₀ + i : ℕ) : ℝ) := by exact_mod_cast (show 0 < n₀ + i by omega)
  have := Real.log_le_log hi (Nat.cast_le.mpr (show n₀ + i ≤ n₀ + j by omega))
  linarith

/-- The log-lattice gaps are at most `1/n₀`. -/
theorem logNode_gap_le {n₀ : ℕ} (hn₀ : 1 ≤ n₀) (c : ℝ) (j : ℕ) :
    logNode n₀ c (j + 1) - logNode n₀ c j ≤ 1 / n₀ := by
  unfold logNode
  have hj : (0 : ℝ) < ((n₀ + j : ℕ) : ℝ) := by exact_mod_cast (show 0 < n₀ + j by omega)
  have hn : (0 : ℝ) < n₀ := by exact_mod_cast hn₀
  rw [sub_sub_sub_cancel_right, ← Real.log_div (by positivity) hj.ne']
  have h1 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < ((n₀ + (j + 1) : ℕ) : ℝ) / ((n₀ + j : ℕ) : ℝ)
    by positivity)
  have h2 : ((n₀ + (j + 1) : ℕ) : ℝ) / ((n₀ + j : ℕ) : ℝ) - 1 = 1 / ((n₀ + j : ℕ) : ℝ) := by
    push_cast; field_simp; ring
  have h3 : 1 / ((n₀ + j : ℕ) : ℝ) ≤ 1 / n₀ :=
    one_div_le_one_div_of_le hn (by exact_mod_cast (show n₀ ≤ n₀ + j by omega))
  linarith

/-! ### Dilated profiles -/

/-- The dilate `φ_k(s) = k φ(ks)`: same mass, width divided by `k`. -/
def dilate (k : ℝ) (φ : ℝ → ℝ) (s : ℝ) : ℝ := k * φ (k * s)

theorem integral_dilate {k : ℝ} (hk : 0 < k) (φ : ℝ → ℝ) : ∫ s, dilate k φ s = ∫ s, φ s := by
  unfold dilate
  rw [MeasureTheory.integral_const_mul, Measure.integral_comp_mul_left (fun s => φ s) k, smul_eq_mul,
    abs_inv, abs_of_pos hk]
  field_simp

theorem integral_abs_dilate {k : ℝ} (hk : 0 < k) (φ : ℝ → ℝ) :
    ∫ s, |dilate k φ s| = ∫ s, |φ s| := by
  unfold dilate
  simp_rw [abs_mul, abs_of_pos hk]
  rw [MeasureTheory.integral_const_mul, Measure.integral_comp_mul_left (fun s => |φ s|) k, smul_eq_mul,
    abs_inv, abs_of_pos hk]
  field_simp

theorem hasDerivAt_dilate {k : ℝ} {φ φ' : ℝ → ℝ} (hφ : ∀ s, HasDerivAt φ (φ' s) s) (s : ℝ) :
    HasDerivAt (dilate k φ) (dilate k (fun s => k * φ' s) s) s := by
  unfold dilate
  have := ((hφ (k * s)).comp s ((hasDerivAt_id s).const_mul k)).const_mul k
  simpa [mul_comm, mul_left_comm, mul_assoc] using this

theorem dilate_eq_zero {k : ℝ} (hk : 0 < k) {φ : ℝ → ℝ} (hφ : ∀ s, 1 < |s| → φ s = 0) {s : ℝ}
    (hs : 1 / k < |s|) : dilate k φ s = 0 := by
  unfold dilate
  rw [hφ (k * s) (by rw [abs_mul, abs_of_pos hk]; rwa [div_lt_iff₀ hk, mul_comm] at hs), mul_zero]

end GaloisForLFunctions.SpacingScaleHarmonicAnalysis
