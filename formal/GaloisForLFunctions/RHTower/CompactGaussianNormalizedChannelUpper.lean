import GaloisForLFunctions.RHTower.CompactGaussianNormalizedChannel

open Filter Topology Finset Complex
noncomputable section
namespace RHTower

/-- Every literal truncation has one uniform bound across a whole abscissa half-plane,
all phases, and all bounded positive cofactor scales. -/
theorem exists_truncatedFullGaussianCofactor_uniform_abscissa_bound (b U : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, s.re ≤ b → ∀ R : ℝ, 0 < R → R ≤ U →
      ∀ L : ℕ, ∀ ω : SteinhausModel.Omega, ‖truncatedFullGaussianCofactor s R L ω‖ ≤ C := by
  obtain ⟨B, _, htail⟩ := exists_fullGaussianCofactor_uniform_abscissa_tail b U (by norm_num : (0 : ℝ) < 1)
  let H : ℝ := ∑ n ∈ range B, ‖((n + 1 : ℕ) : ℂ) ^ ((b : ℂ) - 1)‖
  have hH : 0 ≤ H := sum_nonneg fun _ _ => norm_nonneg _
  have hhead (L : ℕ) (hLB : L ≤ B) (s : ℂ) (hs : s.re ≤ b) (R : ℝ) (hR : 0 < R)
      (ω : SteinhausModel.Omega) : ‖truncatedFullGaussianCofactor s R L ω‖ ≤ H := by
    unfold truncatedFullGaussianCofactor
    calc
      _ ≤ ∑ n ∈ range L, ‖SteinhausModel.X (n + 1) ω * ((n + 1 : ℕ) : ℂ) ^ (s - 1) *
          smoothAFECutoff (((n + 1 : ℕ) : ℝ) / R)‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ range L, ‖((n + 1 : ℕ) : ℂ) ^ ((b : ℂ) - 1)‖ := by
        apply sum_le_sum
        intro n _
        have hp : ‖((n + 1 : ℕ) : ℂ) ^ (s - 1)‖ ≤
            ‖((n + 1 : ℕ) : ℂ) ^ ((b : ℂ) - 1)‖ := by
          apply Complex.norm_natCast_cpow_le_norm_natCast_cpow_of_pos (Nat.succ_pos n)
          simpa only [Complex.sub_re, Complex.ofReal_re, Complex.one_re] using sub_le_sub_right hs 1
        simp only [norm_mul, SteinhausModel.norm_X, one_mul]
        calc
          _ ≤ ‖((n + 1 : ℕ) : ℂ) ^ (s - 1)‖ * 1 :=
            mul_le_mul_of_nonneg_left (norm_smoothAFECutoff_le_one (by positivity)) (norm_nonneg _)
          _ ≤ _ := by simpa only [mul_one] using hp
      _ ≤ H := sum_le_sum_of_subset_of_nonneg (range_mono hLB) (fun _ _ _ => norm_nonneg _)
  refine ⟨H + 2, by linarith, ?_⟩
  intro s hs R hR hRU L ω
  by_cases hLB : L ≤ B
  · exact (hhead L hLB s hs R hR ω).trans (by linarith)
  · have hBL : B ≤ L := by omega
    have hb := htail B le_rfl s hs R hR hRU ω
    have hl := htail L hBL s hs R hR hRU ω
    have hf : ‖steinhausFullGaussianCofactor s R ω‖ ≤ H + 1 := by
      calc
        _ = ‖(steinhausFullGaussianCofactor s R ω - truncatedFullGaussianCofactor s R B ω) +
              truncatedFullGaussianCofactor s R B ω‖ := by congr 1; ring
        _ ≤ ‖steinhausFullGaussianCofactor s R ω - truncatedFullGaussianCofactor s R B ω‖ +
              ‖truncatedFullGaussianCofactor s R B ω‖ := norm_add_le _ _
        _ ≤ 1 + H := add_le_add hb.le (hhead B le_rfl s hs R hR ω)
        _ = H + 1 := by ring
    calc
      _ = ‖steinhausFullGaussianCofactor s R ω +
            (truncatedFullGaussianCofactor s R L ω - steinhausFullGaussianCofactor s R ω)‖ := by
        congr 1
        ring
      _ ≤ ‖steinhausFullGaussianCofactor s R ω‖ +
            ‖truncatedFullGaussianCofactor s R L ω - steinhausFullGaussianCofactor s R ω‖ := norm_add_le _ _
      _ ≤ (H + 1) + 1 := by rw [norm_sub_rev]; exact add_le_add hf hl.le
      _ = H + 2 := by ring

/-- The mode-independent normalized column is uniformly O(N^(-1/2)) across a whole
nonnegative abscissa band, all phases, all cutoffs, and all bounded scales R>=1. -/
theorem exists_compactGaussianNormalizedPrimeChannel_uniform_bound (b U : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ N p : ℝ, 0 < N → 0 < p → 1 ≤ N / p → N / p ≤ U →
      ∀ s : ℂ, 0 ≤ s.re → s.re ≤ b → ∀ tau : ℝ, ∀ L : ℕ, ∀ ω : SteinhausModel.Omega,
        ‖compactGaussianNormalizedPrimeChannel s N p tau L ω‖ ≤ C / Real.sqrt N := by
  obtain ⟨C, hC, hbound⟩ := exists_truncatedFullGaussianCofactor_uniform_abscissa_bound b U
  refine ⟨(|U| + 1) * C, by positivity, ?_⟩
  intro N p hN hp hR1 hRU s hs0 hsb tau L ω
  have hR : 0 < N / p := div_pos hN hp
  have hpow : ‖((N / p : ℝ) : ℂ) ^ (-s)‖ ≤ 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hR, Complex.neg_re]
    exact Real.rpow_le_one_of_one_le_of_nonpos hR1 (neg_nonpos.mpr hs0)
  have hn : ‖truncatedFullGaussianCofactor s (N / p) L ω * ((N / p : ℝ) : ℂ) ^ (-s)‖ ≤ C := by
    rw [norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) hpow).trans (hbound s hsb _ hR hRU L ω)
  rw [norm_compactGaussianNormalizedPrimeChannel hN hp]
  calc
    _ ≤ ((|U| + 1) / Real.sqrt N) * C :=
      mul_le_mul (div_le_div_of_nonneg_right (hRU.trans (by linarith [le_abs_self U]))
        (Real.sqrt_nonneg N)) hn (norm_nonneg _) (by positivity)
    _ = _ := by ring

end RHTower
