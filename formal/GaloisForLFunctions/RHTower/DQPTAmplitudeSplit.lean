import GaloisForLFunctions.RHTower.DQPTPartitionRate

/-!
# DQPT: the recursive amplitude split and its rotation angles

Supplementary Note 4 of arXiv:2511.11199 (published Supplementary Note 5), equations
(4.5)–(4.6), (4.10)–(4.12) and (4.84).

The truncated state `|ψ₀⟩₁ ∝ ∑_{n₀ ≤ n < n₁} n^{−β/2}|n − n₀⟩` is prepared by `k` recursive
amplitude splits.  At each split the branch weights satisfy `c_w² = c_{w0}² + c_{w1}²`, and the
rotation angle is `θ = arctan √(S₁/S₀) = arcsin √(S₁/(S₀+S₁))`.

Main results:
* `dqptBlock_split` — **(4.6)**: `c_w² = c_{w0}² + c_{w1}²`;
* `dqptSplitAngle_sin_sq`, `dqptSplitAngle_cos_sq`, `dqptSplitAngle_tan_sq` — **(4.10)**;
* `dqptSplitAngle_eq_arctan` — **(4.12)**;
* `dqpt_postselection_ratio` — **(4.84)**: the post-selection success probability exceeds `1/2`.
-/

namespace RHTower.DQPT

open Filter Topology Set

noncomputable section

/-! ## The block sums and the split identity -/

/-- `S(a, b, β) = ∑_{n=a}^{b} n^{−β}`, the paper's partial sum. -/
def dqptS (β : ℝ) (a b : ℕ) : ℝ := ∑ n ∈ Finset.Icc a b, (n : ℝ) ^ (-β)

/-- The `M`-term block starting at `base`. -/
def dqptBlock (β : ℝ) (base M : ℕ) : ℝ :=
  ∑ i ∈ Finset.range M, ((base + i : ℕ) : ℝ) ^ (-β)

theorem dqptBlock_nonneg (β : ℝ) (base M : ℕ) : 0 ≤ dqptBlock β base M :=
  Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (by positivity) _)

/-- **(4.6).**  The block of length `2M` splits into two blocks of length `M`. -/
theorem dqptBlock_split (β : ℝ) (base M : ℕ) :
    dqptBlock β base (2 * M) = dqptBlock β base M + dqptBlock β (base + M) M := by
  rw [dqptBlock, dqptBlock, dqptBlock, show 2 * M = M + M from by ring,
    Finset.sum_range_add]
  congr 1
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hidx : base + M + i = base + (M + i) := by omega
  rw [hidx]

/-- The block sum in the `S(a,b,β)` notation. -/
theorem dqptBlock_eq_dqptS {β : ℝ} {base M : ℕ} (hM : 1 ≤ M) (hbase : 1 ≤ base) :
    dqptBlock β base M = dqptS β base (base + M - 1) := by
  rw [dqptBlock, dqptS, ← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
  have hlen : base + M - 1 + 1 - base = M := by omega
  rw [hlen]

/-! ## The split angle -/

/-- The amplitude-split rotation angle `θ = arcsin √(S₁/(S₀+S₁))`. -/
def dqptSplitAngle (S₀ S₁ : ℝ) : ℝ := Real.arcsin (Real.sqrt (S₁ / (S₀ + S₁)))

theorem dqpt_sqrt_ratio_mem {S₀ S₁ : ℝ} (h₀ : 0 < S₀) (h₁ : 0 ≤ S₁) :
    -1 ≤ Real.sqrt (S₁ / (S₀ + S₁)) ∧ Real.sqrt (S₁ / (S₀ + S₁)) ≤ 1 := by
  have hsum : 0 < S₀ + S₁ := by linarith
  have hle : S₁ / (S₀ + S₁) ≤ 1 := by
    rw [div_le_one hsum]
    linarith
  refine ⟨le_trans (by norm_num) (Real.sqrt_nonneg _), ?_⟩
  rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
  exact Real.sqrt_le_sqrt hle

/-- **(4.10).**  `sin²θ = S₁/(S₀+S₁)`. -/
theorem dqptSplitAngle_sin_sq {S₀ S₁ : ℝ} (h₀ : 0 < S₀) (h₁ : 0 ≤ S₁) :
    Real.sin (dqptSplitAngle S₀ S₁) ^ 2 = S₁ / (S₀ + S₁) := by
  have hsum : 0 < S₀ + S₁ := by linarith
  obtain ⟨hm1, hm2⟩ := dqpt_sqrt_ratio_mem h₀ h₁
  rw [dqptSplitAngle, Real.sin_arcsin hm1 hm2, Real.sq_sqrt (by positivity)]

/-- **(4.10).**  `cos²θ = S₀/(S₀+S₁)`. -/
theorem dqptSplitAngle_cos_sq {S₀ S₁ : ℝ} (h₀ : 0 < S₀) (h₁ : 0 ≤ S₁) :
    Real.cos (dqptSplitAngle S₀ S₁) ^ 2 = S₀ / (S₀ + S₁) := by
  have hsum : 0 < S₀ + S₁ := by linarith
  have hpy := Real.sin_sq_add_cos_sq (dqptSplitAngle S₀ S₁)
  have hs := dqptSplitAngle_sin_sq h₀ h₁
  have hval : S₀ / (S₀ + S₁) = 1 - S₁ / (S₀ + S₁) := by
    field_simp
    ring
  rw [hval]
  linarith

/-- The split identity in amplitude form: `cos²θ·(S₀+S₁) = S₀` and `sin²θ·(S₀+S₁) = S₁`. -/
theorem dqptSplitAngle_amplitudes {S₀ S₁ : ℝ} (h₀ : 0 < S₀) (h₁ : 0 ≤ S₁) :
    Real.cos (dqptSplitAngle S₀ S₁) ^ 2 * (S₀ + S₁) = S₀
      ∧ Real.sin (dqptSplitAngle S₀ S₁) ^ 2 * (S₀ + S₁) = S₁ := by
  have hsum : 0 < S₀ + S₁ := by linarith
  rw [dqptSplitAngle_cos_sq h₀ h₁, dqptSplitAngle_sin_sq h₀ h₁]
  constructor <;> field_simp

/-- **(4.10).**  `tan²θ = S₁/S₀`. -/
theorem dqptSplitAngle_tan_sq {S₀ S₁ : ℝ} (h₀ : 0 < S₀) (h₁ : 0 ≤ S₁) :
    Real.tan (dqptSplitAngle S₀ S₁) ^ 2 = S₁ / S₀ := by
  have hsum : 0 < S₀ + S₁ := by linarith
  have hc := dqptSplitAngle_cos_sq h₀ h₁
  have hs := dqptSplitAngle_sin_sq h₀ h₁
  have hcne : Real.cos (dqptSplitAngle S₀ S₁) ≠ 0 := by
    intro hzero
    rw [hzero] at hc
    have : (0 : ℝ) = S₀ / (S₀ + S₁) := by simpa using hc
    have hpos : 0 < S₀ / (S₀ + S₁) := by positivity
    linarith [this, hpos]
  rw [Real.tan_eq_sin_div_cos, div_pow, hs, hc]
  field_simp

/-- **(4.12).**  `θ = arctan √(S₁/S₀)`. -/
theorem dqptSplitAngle_eq_arctan {S₀ S₁ : ℝ} (h₀ : 0 < S₀) (h₁ : 0 ≤ S₁) :
    Real.arctan (Real.sqrt (S₁ / S₀)) = dqptSplitAngle S₀ S₁ := by
  have hsum : 0 < S₀ + S₁ := by linarith
  rw [Real.arctan_eq_arcsin, dqptSplitAngle]
  congr 1
  have hx : Real.sqrt (S₁ / S₀) ^ 2 = S₁ / S₀ := Real.sq_sqrt (by positivity)
  rw [hx]
  have hone : (1 : ℝ) + S₁ / S₀ = (S₀ + S₁) / S₀ := by field_simp
  rw [hone]
  have hs0 : (0 : ℝ) < Real.sqrt S₀ := Real.sqrt_pos.mpr h₀
  have hs1 : (0 : ℝ) < Real.sqrt (S₀ + S₁) := Real.sqrt_pos.mpr hsum
  rw [Real.sqrt_div h₁, Real.sqrt_div (le_of_lt hsum), Real.sqrt_div h₁]
  field_simp

/-! ## Supplementary Note 4 (4.84): the post-selection success probability -/

theorem dqptPartition_le_of_le {β : ℝ} (hβ : 0 ≤ β) {N M : ℕ} (hN : 1 ≤ N) (hNM : N ≤ M) :
    dqptPartition β M ≤ (M : ℝ) / (N : ℝ) * dqptPartition β N := by
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hlow : (N : ℝ) * (N : ℝ) ^ (-β) ≤ dqptPartition β N := by
    have h := dqptPartition_rpow_le hβ hN
    have hsplit : (N : ℝ) ^ (1 - β) = (N : ℝ) * (N : ℝ) ^ (-β) := by
      rw [show (1 - β : ℝ) = 1 + (-β) by ring, Real.rpow_add hN0, Real.rpow_one]
    rw [hsplit] at h
    exact h
  have htail : dqptPartition β M - dqptPartition β N
      ≤ ((M : ℝ) - (N : ℝ)) * (N : ℝ) ^ (-β) := by
    have hsub : dqptPartition β M - dqptPartition β N
        = ∑ n ∈ Finset.Ioc N M, (n : ℝ) ^ (-β) := by
      have hsubset : Finset.Icc 1 N ⊆ Finset.Icc 1 M := by
        intro a ha
        rw [Finset.mem_Icc] at ha ⊢
        omega
      have hsdiff : Finset.Icc 1 M \ Finset.Icc 1 N = Finset.Ioc N M := by
        ext a
        simp only [Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_Ioc]
        omega
      have hsum := Finset.sum_sdiff (f := fun n : ℕ => (n : ℝ) ^ (-β)) hsubset
      rw [hsdiff] at hsum
      rw [dqptPartition, dqptPartition]
      linarith [hsum]
    rw [hsub]
    have hterm : ∀ n ∈ Finset.Ioc N M, (n : ℝ) ^ (-β) ≤ (N : ℝ) ^ (-β) := by
      intro n hn
      rw [Finset.mem_Ioc] at hn
      have hnN : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast le_of_lt hn.1
      exact Real.rpow_le_rpow_of_nonpos hN0 hnN (by linarith)
    have hcard : (Finset.Ioc N M).card = M - N := by simp
    calc ∑ n ∈ Finset.Ioc N M, (n : ℝ) ^ (-β)
        ≤ ∑ _n ∈ Finset.Ioc N M, (N : ℝ) ^ (-β) := Finset.sum_le_sum hterm
      _ = ((M - N : ℕ) : ℝ) * (N : ℝ) ^ (-β) := by rw [Finset.sum_const, hcard, nsmul_eq_mul]
      _ = ((M : ℝ) - (N : ℝ)) * (N : ℝ) ^ (-β) := by
          congr 1
          have hc : ((M - N : ℕ) : ℝ) = (M : ℝ) - (N : ℝ) := by
            exact_mod_cast Nat.cast_sub (R := ℝ) hNM
          exact hc
  have hMN : (0 : ℝ) ≤ (M : ℝ) - (N : ℝ) := by
    have : (N : ℝ) ≤ (M : ℝ) := by exact_mod_cast hNM
    linarith
  have hkey : ((M : ℝ) - (N : ℝ)) * (N : ℝ) ^ (-β)
      ≤ ((M : ℝ) - (N : ℝ)) / (N : ℝ) * dqptPartition β N := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hN0]
    nlinarith [hlow, hMN]
  have hfin : (M : ℝ) / (N : ℝ) * dqptPartition β N
      = dqptPartition β N + ((M : ℝ) - (N : ℝ)) / (N : ℝ) * dqptPartition β N := by
    field_simp
    ring
  linarith [htail, hkey, hfin]

/-- **(4.84).**  If the truncation point `M` is below `2N`, post-selection onto the first `N`
levels succeeds with probability more than `1/2`. -/
theorem dqpt_postselection_ratio {β : ℝ} (hβ : 0 ≤ β) {N M : ℕ} (hN : 1 ≤ N) (hNM : N ≤ M)
    (hM : M < 2 * N) :
    1 / 2 < dqptPartition β N / dqptPartition β M := by
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hZN : (0 : ℝ) < dqptPartition β N :=
    lt_of_lt_of_le zero_lt_one (one_le_dqptPartition β hN)
  have hZM : (0 : ℝ) < dqptPartition β M :=
    lt_of_lt_of_le zero_lt_one (one_le_dqptPartition β (by omega))
  have hMlt : (M : ℝ) < 2 * (N : ℝ) := by exact_mod_cast hM
  have hle := dqptPartition_le_of_le hβ hN hNM
  have hstrict : dqptPartition β M < 2 * dqptPartition β N := by
    have hratio : (M : ℝ) / (N : ℝ) < 2 := by
      rw [div_lt_iff₀ hN0]
      linarith
    nlinarith [hle, hratio, hZN]
  rw [lt_div_iff₀ hZM]
  linarith

end

end RHTower.DQPT
