import GaloisForLFunctions.HTGeometry.ScaledCutoff
import GaloisForLFunctions.HTGeometry.TaylorVanishingBound

/-!
# The localised product of a cutoff with a function vanishing to finite order

If `φ` vanishes to order `N` at the origin, then on the support of the cutoff at scale `ε` its
`(n-i)`-th derivative is `O(ε^{N+1-n+i})` while the `i`-th derivative of the cutoff is `O(ε^{-i})`.
The Leibniz bound therefore gives

`‖D^n (χ_ε φ)(x)‖ ≤ C ε^{N+1-n}`   for `n ≤ N`,

with a constant independent of `ε`: every derivative of the cutoff is paid for by an extra order of
vanishing of `φ`.
-/

open Set

namespace GaloisForLFunctions.HTGeometry

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The constant of the localised Leibniz estimate. -/
noncomputable def cutoffProductConst (M : ℝ) (N n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n+1),
    (n.choose i : ℝ) * cutoffConst i * (M / (Nat.factorial (N - n + 1 + i)))
      * 2 ^ (N - n + 1 + i)

/-- **The localised Leibniz estimate.** -/
theorem norm_iteratedFDeriv_cutoff_smul_le {φ : ℝ → X} {N : ℕ} {M : ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hvanish : ∀ j, j ≤ N → iteratedDeriv j φ 0 = 0)
    (hM : ∀ t ∈ Icc (-1:ℝ) 1, ‖iteratedDeriv (N+1) φ t‖ ≤ M)
    {n : ℕ} (hn : n ≤ N) {ε : ℝ} (hε : 0 < ε) (hε1 : 2 * ε ≤ 1) {x : ℝ} (hx : |x| ≤ 2 * ε) :
    ‖iteratedFDeriv ℝ n (fun y => cutoffScaled ε y • φ y) x‖
      ≤ cutoffProductConst M N n * ε ^ (N - n + 1) := by
  have hxmem : x ∈ Icc (-1:ℝ) 1 := by
    have h := abs_le.mp (le_trans hx hε1)
    exact ⟨h.1, h.2⟩
  have hTaylor := norm_iteratedDeriv_le_of_vanishing (f := φ) (M := M) (b := 1) (N := N)
    hφ hvanish hM
  have hleib := norm_iteratedFDeriv_smul_le (𝕜 := ℝ) (f := cutoffScaled ε) (g := φ)
    (contDiff_cutoffScaled ε) hφ x (n := n) (by exact_mod_cast le_top)
  refine le_trans hleib ?_
  rw [cutoffProductConst, Finset.sum_mul]
  refine Finset.sum_le_sum fun i hi => ?_
  have hile : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  -- the cutoff factor
  have hcut : ‖iteratedFDeriv ℝ i (cutoffScaled ε) x‖ ≤ cutoffConst i * (ε⁻¹) ^ i := by
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
    exact abs_iteratedDeriv_cutoffScaled_le i hε x
  -- the amplitude factor
  have hindex : N + 1 - (N - n + 1 + i) = n - i := by omega
  have hd : N - n + 1 + i ≤ N + 1 := by omega
  have hamp : ‖iteratedFDeriv ℝ (n - i) φ x‖
      ≤ M * |x| ^ (N - n + 1 + i) / (Nat.factorial (N - n + 1 + i)) := by
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    have h := hTaylor (N - n + 1 + i) hd x hxmem
    rwa [hindex] at h
  -- combine
  have hxpow : |x| ^ (N - n + 1 + i) ≤ (2 * ε) ^ (N - n + 1 + i) :=
    pow_le_pow_left₀ (abs_nonneg x) hx _
  have hMnn : 0 ≤ M := by
    have := hM 0 ⟨by norm_num, by norm_num⟩
    exact le_trans (norm_nonneg _) this
  have hamp' : ‖iteratedFDeriv ℝ (n - i) φ x‖
      ≤ M * (2 * ε) ^ (N - n + 1 + i) / (Nat.factorial (N - n + 1 + i)) := by
    refine le_trans hamp ?_
    gcongr
  have hchoose : (0:ℝ) ≤ (n.choose i : ℝ) := by positivity
  have hstep : (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (cutoffScaled ε) x‖
        * ‖iteratedFDeriv ℝ (n - i) φ x‖
      ≤ (n.choose i : ℝ) * (cutoffConst i * (ε⁻¹) ^ i)
        * (M * (2 * ε) ^ (N - n + 1 + i) / (Nat.factorial (N - n + 1 + i))) := by
    have h1 : (0:ℝ) ≤ (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (cutoffScaled ε) x‖ := by positivity
    refine mul_le_mul ?_ hamp' (norm_nonneg _)
      (mul_nonneg hchoose (mul_nonneg (cutoffConst_nonneg i) (by positivity)))
    exact mul_le_mul_of_nonneg_left hcut hchoose
  refine le_trans hstep (le_of_eq ?_)
  have hεne : ε ≠ 0 := ne_of_gt hε
  rw [inv_pow]
  field_simp
  ring

theorem cutoffProductConst_nonneg {M : ℝ} (hM : 0 ≤ M) (N n : ℕ) :
    0 ≤ cutoffProductConst M N n := by
  rw [cutoffProductConst]
  refine Finset.sum_nonneg fun i _ => ?_
  have h1 : (0:ℝ) ≤ (n.choose i : ℝ) := by positivity
  have h2 := cutoffConst_nonneg i
  have h3 : (0:ℝ) ≤ M / (Nat.factorial (N - n + 1 + i)) := by positivity
  have h4 : (0:ℝ) ≤ (2:ℝ) ^ (N - n + 1 + i) := by positivity
  have := mul_nonneg (mul_nonneg (mul_nonneg h1 h2) h3) h4
  exact this

/-- Outside the support of the cutoff every derivative of the localised product vanishes. -/
theorem iteratedFDeriv_cutoff_smul_eq_zero {φ : ℝ → X} {ε : ℝ} (hε : 0 < ε) (n : ℕ) {x : ℝ}
    (hx : 2 * ε < |x|) :
    iteratedFDeriv ℝ n (fun y => cutoffScaled ε y • φ y) x = 0 := by
  have hnhds : (fun y => cutoffScaled ε y • φ y) =ᶠ[nhds x] (fun _ => (0 : X)) := by
    have hopen : IsOpen {y : ℝ | 2 * ε < |y|} := by
      have : {y : ℝ | 2 * ε < |y|} = (fun y : ℝ => |y|) ⁻¹' (Set.Ioi (2 * ε)) := rfl
      rw [this]
      exact (continuous_abs.isOpen_preimage _ isOpen_Ioi)
    have hmem : {y : ℝ | 2 * ε < |y|} ∈ nhds x := hopen.mem_nhds hx
    filter_upwards [hmem] with y hy
    have : cutoffScaled ε y = 0 := cutoffScaled_eq_zero hε (le_of_lt hy)
    rw [this, zero_smul]
  have heq := Filter.EventuallyEq.iteratedFDeriv ℝ hnhds n
  have hval := heq.eq_of_nhds
  rw [hval]
  simp

/-- **The localised seminorm estimate.**  Every Schwartz seminorm of the localised product is
`O(ε^{k + N + 1 - n})`, hence tends to zero with the localisation scale. -/
theorem abs_pow_mul_norm_iteratedFDeriv_cutoff_smul_le {φ : ℝ → X} {N : ℕ} {M : ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hvanish : ∀ j, j ≤ N → iteratedDeriv j φ 0 = 0)
    (hM : ∀ t ∈ Icc (-1:ℝ) 1, ‖iteratedDeriv (N+1) φ t‖ ≤ M)
    (k : ℕ) {n : ℕ} (hn : n ≤ N) {ε : ℝ} (hε : 0 < ε) (hε1 : 2 * ε ≤ 1) (x : ℝ) :
    |x| ^ k * ‖iteratedFDeriv ℝ n (fun y => cutoffScaled ε y • φ y) x‖
      ≤ ((2:ℝ) ^ k * cutoffProductConst M N n) * ε ^ (k + (N - n + 1)) := by
  have hMnn : 0 ≤ M := by
    have := hM 0 ⟨by norm_num, by norm_num⟩
    exact le_trans (norm_nonneg _) this
  rcases le_or_gt (|x|) (2 * ε) with hx | hx
  · have hmain := norm_iteratedFDeriv_cutoff_smul_le hφ hvanish hM hn hε hε1 hx
    have hxk : |x| ^ k ≤ (2 * ε) ^ k := pow_le_pow_left₀ (abs_nonneg x) hx _
    calc |x| ^ k * ‖iteratedFDeriv ℝ n (fun y => cutoffScaled ε y • φ y) x‖
        ≤ (2 * ε) ^ k * (cutoffProductConst M N n * ε ^ (N - n + 1)) := by
          refine mul_le_mul hxk hmain (norm_nonneg _) (by positivity)
      _ = ((2:ℝ) ^ k * cutoffProductConst M N n) * ε ^ (k + (N - n + 1)) := by
          rw [mul_pow, pow_add]
          ring
  · rw [iteratedFDeriv_cutoff_smul_eq_zero hε n hx, norm_zero, mul_zero]
    have := cutoffProductConst_nonneg hMnn N n
    positivity

end GaloisForLFunctions.HTGeometry
