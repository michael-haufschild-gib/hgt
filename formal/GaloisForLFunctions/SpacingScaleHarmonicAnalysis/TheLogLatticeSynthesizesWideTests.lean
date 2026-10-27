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
    (ha : Monotone a) (hgap : ∀ k < K, a (k + 1) - a k ≤ h) (hF : Continuous F)
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
  have hMh : 0 ≤ M * h := by
    rcases Nat.eq_zero_or_pos K with rfl | hK
    · simp at hsumV ⊢
      exact hM
    · exact mul_nonneg hM ((sub_nonneg.mpr (ha (Nat.le_succ 0))).trans (hgap 0 hK))
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

end GaloisForLFunctions.SpacingScaleHarmonicAnalysis
