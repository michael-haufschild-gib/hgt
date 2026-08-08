import GaloisForLFunctions.RHTower.ChebyshevPsiScaling
import GaloisForLFunctions.HTGeometry.SignSinBlock
import GaloisForLFunctions.HTGeometry.AntitoneBlockTelescope

/-!
# The value of a dilated von Mangoldt sum on one half-period block

On an index block whose dilated argument `α T / m` stays inside the `k`-th half period, the weight
`sgn (sin (α T / m))` is the constant `(-1)^k`, so the weighted von Mangoldt sum is
`(-1)^k (ψ b - ψ a)`.  The single exception is an index with `α T / m = k π` exactly, where the sign
is `0` rather than `±1`; since `m` is then determined, that costs one term of size
`Λ m ≤ log m` (`abs_sum_block_vonMangoldt_sign_sub_le`).

Summed over `K` blocks the total discrepancy is `O(K log T)`, which is `o(T)` at fixed `K` — the
error budget the endpoint asymptotic needs.
-/

open Filter Finset ArithmeticFunction Real
open GaloisForLFunctions.HTGeometry
open scoped BigOperators Topology

namespace RHTower

/-- The indices of a block at which the dilated sine vanishes form a subsingleton. -/
theorem card_filter_dilate_eq_le_one {α T : ℝ} (hα : 0 < α) (hT : 0 < T) {k : ℕ} {a b : ℕ} :
    ((Finset.Ioc a b).filter (fun m : ℕ => α * T / m = (k : ℝ) * π)).card ≤ 1 := by
  classical
  refine Finset.card_le_one.mpr fun x hx y hy => ?_
  simp only [Finset.mem_filter, Finset.mem_Ioc] at hx hy
  have hx0 : (0 : ℝ) < x := by
    have : 0 < x := by omega
    exact_mod_cast this
  have hy0 : (0 : ℝ) < y := by
    have : 0 < y := by omega
    exact_mod_cast this
  have hαT : (0 : ℝ) < α * T := mul_pos hα hT
  have hxy : α * T / x = α * T / y := by rw [hx.2, hy.2]
  rw [div_eq_div_iff (ne_of_gt hx0) (ne_of_gt hy0)] at hxy
  have hcancel := mul_left_cancel₀ (ne_of_gt hαT) hxy
  exact_mod_cast hcancel.symm

/-- **The block value.**  If the dilated argument stays in the `k`-th half period across
`Ioc a b`, the weighted von Mangoldt sum is `(-1)^k (ψ b - ψ a)` up to one `log` term. -/
theorem abs_sum_block_vonMangoldt_sign_sub_le {α T : ℝ} (hα : 0 < α) (hT : 0 < T)
    {k : ℕ} {a b : ℕ} (hab : a ≤ b)
    (hlo : ∀ m : ℕ, a < m → m ≤ b → (k : ℝ) * π ≤ α * T / m)
    (hhi : ∀ m : ℕ, a < m → m ≤ b → α * T / m < ((k : ℝ) + 1) * π) :
    |(∑ m ∈ Finset.Ioc a b, (vonMangoldt m : ℝ) * Real.sign (Real.sin (α * T / m)))
        - (-1) ^ k * (chebyshevPsi b - chebyshevPsi a)| ≤ Real.log b := by
  classical
  have hαT : (0 : ℝ) < α * T := mul_pos hα hT
  have hrange : ∀ m ∈ Finset.Ioc a b,
      (k : ℝ) * π ≤ α * T / m ∧ α * T / m < ((k : ℝ) + 1) * π := by
    intro m hm
    rw [Finset.mem_Ioc] at hm
    exact ⟨hlo m hm.1 hm.2, hhi m hm.1 hm.2⟩
  have hsub : (∑ m ∈ Finset.Ioc a b, (vonMangoldt m : ℝ) * Real.sign (Real.sin (α * T / m)))
      - (-1) ^ k * (chebyshevPsi b - chebyshevPsi a)
      = ∑ m ∈ Finset.Ioc a b,
          (vonMangoldt m : ℝ) * (Real.sign (Real.sin (α * T / m)) - (-1) ^ k) := by
    rw [chebyshevPsi_sub hab, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun m _ => by ring
  rw [hsub]
  set P : ℕ → Prop := fun m => α * T / m = (k : ℝ) * π with hP
  have hzero : ∀ m ∈ (Finset.Ioc a b).filter (fun m => ¬ P m),
      (vonMangoldt m : ℝ) * (Real.sign (Real.sin (α * T / m)) - (-1) ^ k) = 0 := by
    intro m hm
    rw [Finset.mem_filter] at hm
    obtain ⟨hmem, hnot⟩ := hm
    have hr := hrange m hmem
    have hlt : (k : ℝ) * π < α * T / m := lt_of_le_of_ne hr.1 (fun h => hnot h.symm)
    rw [sign_sin_of_mem_Ioo hlt hr.2, sub_self, mul_zero]
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.Ioc a b) P
    (fun m : ℕ => (vonMangoldt m : ℝ) * (Real.sign (Real.sin (α * T / m)) - (-1) ^ k))
  rw [← hsplit, Finset.sum_eq_zero hzero, add_zero]
  rcases Nat.eq_zero_or_pos b with rfl | hb0
  · simp
  have hlogb : 0 ≤ Real.log b := Real.log_nonneg (by exact_mod_cast hb0)
  have hterm : ∀ m ∈ (Finset.Ioc a b).filter P,
      |(vonMangoldt m : ℝ) * (Real.sign (Real.sin (α * T / m)) - (-1) ^ k)| ≤ Real.log b := by
    intro m hm
    rw [Finset.mem_filter, Finset.mem_Ioc] at hm
    have hmb : m ≤ b := hm.1.2
    have hm1 : 1 ≤ m := by omega
    have hΛ : (vonMangoldt m : ℝ) ≤ Real.log b := by
      refine le_trans vonMangoldt_le_log ?_
      exact Real.log_le_log (by exact_mod_cast hm1) (by exact_mod_cast hmb)
    have hΛ0 : (0 : ℝ) ≤ vonMangoldt m := vonMangoldt_nonneg
    have hs : Real.sign (Real.sin (α * T / m)) = 0 := by
      have hsin : Real.sin (α * T / m) = 0 := by
        rw [hm.2]
        simp
      rw [hsin]
      simp [Real.sign]
    rw [hs, zero_sub, abs_mul, abs_neg, abs_of_nonneg hΛ0, abs_pow, abs_neg, abs_one, one_pow,
      mul_one]
    exact hΛ
  calc |∑ m ∈ (Finset.Ioc a b).filter P,
          (vonMangoldt m : ℝ) * (Real.sign (Real.sin (α * T / m)) - (-1) ^ k)|
      ≤ ∑ m ∈ (Finset.Ioc a b).filter P,
          |(vonMangoldt m : ℝ) * (Real.sign (Real.sin (α * T / m)) - (-1) ^ k)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _m ∈ (Finset.Ioc a b).filter P, Real.log b := Finset.sum_le_sum hterm
    _ = ((Finset.Ioc a b).filter P).card * Real.log b := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 1 * Real.log b := by
        refine mul_le_mul_of_nonneg_right ?_ hlogb
        exact_mod_cast card_filter_dilate_eq_le_one hα hT (k := k) (a := a) (b := b)
    _ = Real.log b := one_mul _

/-! ### The half-period endpoints of a dilation -/

/-- The index endpoints cutting `[1, T]` at the half periods of `α T / ·`.  The `min` makes every
block below the first half period empty, so no case split on `⌊α/π⌋` is needed. -/
noncomputable def blockEndpoint (α T : ℝ) (k : ℕ) : ℕ :=
  if k = 0 then ⌊T⌋₊ else min ⌊T⌋₊ ⌊α * T / ((k : ℝ) * π)⌋₊

theorem blockEndpoint_zero (α T : ℝ) : blockEndpoint α T 0 = ⌊T⌋₊ := by
  simp [blockEndpoint]

theorem blockEndpoint_le_floor (α T : ℝ) (k : ℕ) : blockEndpoint α T k ≤ ⌊T⌋₊ := by
  rw [blockEndpoint]
  split_ifs with h
  · exact le_rfl
  · exact min_le_left _ _

theorem blockEndpoint_antitone {α T : ℝ} (hα : 0 < α) (hT : 0 < T) :
    Antitone (blockEndpoint α T) := by
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have hαT : (0 : ℝ) < α * T := mul_pos hα hT
  refine antitone_nat_of_succ_le fun k => ?_
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [blockEndpoint_zero]
    exact blockEndpoint_le_floor α T 1
  · have hk1 : k + 1 ≠ 0 := by omega
    have hk0 : k ≠ 0 := by omega
    rw [blockEndpoint, blockEndpoint, if_neg hk1, if_neg hk0]
    refine min_le_min le_rfl (Nat.floor_mono ?_)
    have hkR : (0 : ℝ) < (k : ℝ) * π := by
      have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      nlinarith
    have hk1R : (0 : ℝ) < ((k : ℝ) + 1) * π := by nlinarith
    refine div_le_div_of_nonneg_left hαT.le hkR ?_
    push_cast
    nlinarith

/-! ### The finite block decomposition of a dilated von Mangoldt sum -/

/-- **The `K`-block decomposition with its error budget.**  Up to `K log T`, the dilated von
Mangoldt sum over the first `K` half periods is the alternating telescope of Chebyshev values at
the endpoints. -/
theorem abs_sum_blocks_vonMangoldt_sign_sub_le {α T : ℝ} (hα : 0 < α) (hT : 1 ≤ T) (K : ℕ) :
    |(∑ m ∈ Finset.Ioc (blockEndpoint α T K) ⌊T⌋₊,
          (vonMangoldt m : ℝ) * Real.sign (Real.sin (α * T / m)))
        - ∑ k ∈ Finset.range K, (-1) ^ k *
            (chebyshevPsi (blockEndpoint α T k)
              - chebyshevPsi (blockEndpoint α T (k + 1)))|
      ≤ K * Real.log ⌊T⌋₊ := by
  classical
  have hT0 : (0 : ℝ) < T := by linarith
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have hαT : (0 : ℝ) < α * T := mul_pos hα hT0
  have hmono := blockEndpoint_antitone hα hT0
  have hfloor1 : 1 ≤ ⌊T⌋₊ := Nat.le_floor (by simpa using hT)
  have hlogT : 0 ≤ Real.log ⌊T⌋₊ := Real.log_nonneg (by exact_mod_cast hfloor1)
  -- the block bound, uniform in `k`
  have hblock : ∀ k : ℕ,
      |(∑ m ∈ Finset.Ioc (blockEndpoint α T (k + 1)) (blockEndpoint α T k),
            (vonMangoldt m : ℝ) * Real.sign (Real.sin (α * T / m)))
          - (-1) ^ k * (chebyshevPsi (blockEndpoint α T k)
              - chebyshevPsi (blockEndpoint α T (k + 1)))|
        ≤ Real.log ⌊T⌋₊ := by
    intro k
    have hab : blockEndpoint α T (k + 1) ≤ blockEndpoint α T k := hmono (Nat.le_succ k)
    have hmemPos : ∀ m : ℕ, blockEndpoint α T (k + 1) < m → (0 : ℝ) < m := by
      intro m hm
      have : 0 < m := by omega
      exact_mod_cast this
    have hlo : ∀ m : ℕ, blockEndpoint α T (k + 1) < m → m ≤ blockEndpoint α T k →
        (k : ℝ) * π ≤ α * T / m := by
      intro m h1 h2
      have hm0 : (0 : ℝ) < m := hmemPos m h1
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp only [Nat.cast_zero, zero_mul]
        positivity
      · have hk0 : k ≠ 0 := by omega
        have hmle : (m : ℝ) ≤ α * T / ((k : ℝ) * π) := by
          have hstep : m ≤ ⌊α * T / ((k : ℝ) * π)⌋₊ := by
            have hh := h2
            rw [blockEndpoint, if_neg hk0] at hh
            omega
          have hcast : (m : ℝ) ≤ (⌊α * T / ((k : ℝ) * π)⌋₊ : ℝ) := by exact_mod_cast hstep
          exact hcast.trans (Nat.floor_le (by positivity))
        have hkR : (0 : ℝ) < (k : ℝ) * π := by
          have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
          nlinarith
        rw [le_div_iff₀ hkR] at hmle
        rw [le_div_iff₀ hm0]
        linarith
    have hhi : ∀ m : ℕ, blockEndpoint α T (k + 1) < m → m ≤ blockEndpoint α T k →
        α * T / m < ((k : ℝ) + 1) * π := by
      intro m h1 h2
      have hm0 : (0 : ℝ) < m := hmemPos m h1
      have hk1 : k + 1 ≠ 0 := by omega
      have hcase : ⌊α * T / (((k : ℝ) + 1) * π)⌋₊ < m := by
        rw [blockEndpoint, if_neg hk1] at h1
        have hmT : m ≤ ⌊T⌋₊ := le_trans h2 (blockEndpoint_le_floor α T k)
        have hcast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
        rw [hcast] at h1
        omega
      have hlt : α * T / (((k : ℝ) + 1) * π) < (m : ℝ) := by
        refine lt_of_lt_of_le (Nat.lt_floor_add_one _) ?_
        exact_mod_cast hcase
      have hk1R : (0 : ℝ) < ((k : ℝ) + 1) * π := by positivity
      rw [div_lt_iff₀ hk1R] at hlt
      rw [div_lt_iff₀ hm0]
      linarith
    have hbnd := abs_sum_block_vonMangoldt_sign_sub_le hα hT0 hab hlo hhi
    refine hbnd.trans ?_
    rcases Nat.eq_zero_or_pos (blockEndpoint α T k) with hz | hz
    · rw [hz]
      simpa using hlogT
    · exact Real.log_le_log (by exact_mod_cast hz)
        (by exact_mod_cast blockEndpoint_le_floor α T k)
  -- telescope and add the block errors
  rw [← blockEndpoint_zero α T,
    GaloisForLFunctions.HTGeometry.sum_Ioc_eq_sum_blocks
      (fun m : ℕ => (vonMangoldt m : ℝ) * Real.sign (Real.sin (α * T / m)))
      (blockEndpoint α T) hmono K,
    ← Finset.sum_sub_distrib]
  calc |∑ k ∈ Finset.range K,
          ((∑ m ∈ Finset.Ioc (blockEndpoint α T (k + 1)) (blockEndpoint α T k),
              (vonMangoldt m : ℝ) * Real.sign (Real.sin (α * T / m)))
            - (-1) ^ k * (chebyshevPsi (blockEndpoint α T k)
                - chebyshevPsi (blockEndpoint α T (k + 1))))|
      ≤ ∑ k ∈ Finset.range K,
          |(∑ m ∈ Finset.Ioc (blockEndpoint α T (k + 1)) (blockEndpoint α T k),
              (vonMangoldt m : ℝ) * Real.sign (Real.sin (α * T / m)))
            - (-1) ^ k * (chebyshevPsi (blockEndpoint α T k)
                - chebyshevPsi (blockEndpoint α T (k + 1)))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ Finset.range K, Real.log ⌊T⌋₊ := Finset.sum_le_sum fun k _ => hblock k
    _ = K * Real.log ⌊T⌋₊ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-! ### The head limit -/

/-- The limiting proportion carried by the `k`-th endpoint. -/
noncomputable def blockScale (α : ℝ) (k : ℕ) : ℝ :=
  if k = 0 then 1 else min 1 (α / ((k : ℝ) * π))

theorem blockScale_pos {α : ℝ} (hα : 0 < α) (k : ℕ) : 0 < blockScale α k := by
  rw [blockScale]
  split_ifs with h
  · norm_num
  · have hk : 1 ≤ (k : ℝ) := by
      have : 1 ≤ k := by omega
      exact_mod_cast this
    have : (0 : ℝ) < (k : ℝ) * π := by nlinarith [Real.pi_pos]
    exact lt_min (by norm_num) (by positivity)

theorem floor_min_eq_min_floor (x y : ℝ) : ⌊min x y⌋₊ = min ⌊x⌋₊ ⌊y⌋₊ := by
  rcases le_total x y with h | h
  · rw [min_eq_left h, min_eq_left (Nat.floor_mono h)]
  · rw [min_eq_right h, min_eq_right (Nat.floor_mono h)]

theorem blockEndpoint_eq_floor_scale {α T : ℝ} (hα : 0 < α) (hT : 0 < T) (k : ℕ) :
    blockEndpoint α T k = ⌊blockScale α k * T⌋₊ := by
  rw [blockEndpoint, blockScale]
  split_ifs with h
  · rw [one_mul]
  · have hk : 1 ≤ (k : ℝ) := by
      have : 1 ≤ k := by omega
      exact_mod_cast this
    have hkπ : (0 : ℝ) < (k : ℝ) * π := by nlinarith [Real.pi_pos]
    have hsplit : min 1 (α / ((k : ℝ) * π)) * T = min T (α * T / ((k : ℝ) * π)) := by
      rw [min_mul_of_nonneg _ _ hT.le, one_mul]
      congr 1
      field_simp
    rw [hsplit, floor_min_eq_min_floor]

/-- **Each endpoint carries its limiting proportion.** -/
theorem tendsto_chebyshevPsi_blockEndpoint_div {α : ℝ} (hα : 0 < α) (k : ℕ) :
    Tendsto (fun T : ℝ => chebyshevPsi (blockEndpoint α T k) / T) atTop
      (𝓝 (blockScale α k)) := by
  have h := tendsto_chebyshevPsiReal_scaled (blockScale_pos hα k)
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  rw [chebyshevPsiReal, blockEndpoint_eq_floor_scale hα hT k]

/-- **The head limit.**  The alternating telescope over the first `K` half periods converges to the
alternating telescope of the limiting proportions. -/
theorem tendsto_head_blocks {α : ℝ} (hα : 0 < α) (K : ℕ) :
    Tendsto (fun T : ℝ => (∑ k ∈ Finset.range K, (-1) ^ k *
        (chebyshevPsi (blockEndpoint α T k) - chebyshevPsi (blockEndpoint α T (k + 1)))) / T)
      atTop (𝓝 (∑ k ∈ Finset.range K, (-1) ^ k * (blockScale α k - blockScale α (k + 1)))) := by
  have hterm : ∀ k ∈ Finset.range K,
      Tendsto (fun T : ℝ => (-1 : ℝ) ^ k *
          ((chebyshevPsi (blockEndpoint α T k) / T) - (chebyshevPsi (blockEndpoint α T (k + 1)) / T)))
        atTop (𝓝 ((-1) ^ k * (blockScale α k - blockScale α (k + 1)))) := by
    intro k _
    exact ((tendsto_chebyshevPsi_blockEndpoint_div hα k).sub
      (tendsto_chebyshevPsi_blockEndpoint_div hα (k + 1))).const_mul _
  have hsum := tendsto_finsetSum (Finset.range K) hterm
  refine hsum.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun k _ => ?_
  field_simp

end RHTower
