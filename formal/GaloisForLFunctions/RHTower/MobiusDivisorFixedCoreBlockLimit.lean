import GaloisForLFunctions.RHTower.FixedCoreSquarefreeMoments
import GaloisForLFunctions.RHTower.MobiusDivisorFixedCoreProfile

/-!
# Exact quadratic limits of actual fixed-core quotient blocks

The clipped head is affine in the physical square-root clock on each
quotient cell. The complete arithmetic cell is an exact difference of two
squarefree prefix sums, so its quadratic limit follows from the proved
weighted source moments. Summing unbounded quotient depth and controlling
signed prime reserve are not asserted here.
-/

noncomputable section
open Filter Topology
open Finset
namespace RHTower

/-- Slope of the actual processed head in its square-root interpolation clock. -/
def mobiusDivisorHeadBlockSlope (P : Finset ℕ) (n : ℕ) : ℝ :=
  (mobiusDivisorSelectionFibre (n+1) P ∅-mobiusDivisorSelectionFibre n P ∅)/
    (Real.sqrt (n+1 : ℕ)-Real.sqrt n)

/-- Intercept of that same actual head block. -/
def mobiusDivisorHeadBlockIntercept (P : Finset ℕ) (n : ℕ) : ℝ :=
  mobiusDivisorSelectionFibre n P ∅-mobiusDivisorHeadBlockSlope P n*Real.sqrt n

/-- Primitive of the square-root-affine square on one quotient block. -/
def mobiusDivisorHeadBlockPrimitive (P : Finset ℕ) (n : ℕ) (c : ℝ) : ℝ :=
  (mobiusDivisorHeadBlockSlope P n)^(2 : ℕ)*c+
    (4/3:ℝ)*mobiusDivisorHeadBlockSlope P n*mobiusDivisorHeadBlockIntercept P n*c*Real.sqrt c+
      (mobiusDivisorHeadBlockIntercept P n)^(2 : ℕ)*c^(2 : ℕ)/2

/-- Full actual arithmetic energy in the quotient cell M/r=n. -/
def mobiusDivisorFixedCoreBlockEnergy (P : Finset ℕ) (M n : ℕ) : ℝ :=
  ∑ r ∈ (fixedCoreSquarefreeIndices P M).filter (fun r => M/r=n),
    (r : ℝ)*(mobiusDivisorInterpolatedFibre M r P ∅)^(2 : ℕ)

/-- Exact affine form of every clipped sample within its actual quotient cell. -/
theorem mobiusDivisorInterpolatedHead_eq_block_affine
    (P : Finset ℕ) {M r n : ℕ} (hr : 0 < r) (hn : M/r=n) :
    Real.sqrt r*mobiusDivisorInterpolatedFibre M r P ∅ =
      mobiusDivisorHeadBlockSlope P n*Real.sqrt M+
        mobiusDivisorHeadBlockIntercept P n*Real.sqrt r := by
  have hden : 0 < Real.sqrt (n+1 : ℕ)-Real.sqrt n := by
    apply sub_pos.mpr
    apply Real.sqrt_lt_sqrt (Nat.cast_nonneg _)
    exact_mod_cast Nat.lt_succ_self n
  have hslope : mobiusDivisorHeadBlockSlope P n*
      (Real.sqrt (n+1 : ℕ)-Real.sqrt n) =
        mobiusDivisorSelectionFibre (n+1) P ∅-mobiusDivisorSelectionFibre n P ∅ :=
    div_mul_cancel₀ _ hden.ne'
  have hc := divisorPrimeClipWeight_mul_step M r hr
  rw [hn] at hc
  push_cast at hc
  rw [Real.sqrt_mul (Nat.cast_nonneg r)] at hc
  unfold mobiusDivisorInterpolatedFibre
  rw [hn]
  calc
    _ = Real.sqrt r*mobiusDivisorSelectionFibre n P ∅+
        (divisorPrimeClipWeight M r*Real.sqrt r)*
          (mobiusDivisorSelectionFibre (n+1) P ∅-mobiusDivisorSelectionFibre n P ∅) := by ring
    _ = Real.sqrt r*mobiusDivisorSelectionFibre n P ∅+
        mobiusDivisorHeadBlockSlope P n*(divisorPrimeClipWeight M r*Real.sqrt r*
          (Real.sqrt (n+1 : ℕ)-Real.sqrt n)) := by rw [← hslope]; ring
    _ = _ := by
      push_cast
      rw [hc]
      unfold mobiusDivisorHeadBlockIntercept
      ring

private lemma block_term (P : Finset ℕ) {M r n : ℕ}
    (hM : 0 < M) (hr : 0 < r) (hn : M/r=n) :
    (r : ℝ)*(mobiusDivisorInterpolatedFibre M r P ∅)^(2 : ℕ) =
      (M : ℝ)*(mobiusDivisorHeadBlockSlope P n+
        mobiusDivisorHeadBlockIntercept P n*Real.sqrt ((r : ℝ)/M))^(2 : ℕ) := by
  have he := mobiusDivisorInterpolatedHead_eq_block_affine P hr hn
  have hs : Real.sqrt (M : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr (by exact_mod_cast hM)
  have he' : Real.sqrt r*mobiusDivisorInterpolatedFibre M r P ∅ =
      Real.sqrt M*(mobiusDivisorHeadBlockSlope P n+
        mobiusDivisorHeadBlockIntercept P n*Real.sqrt ((r : ℝ)/M)) := by
    rw [he, Real.sqrt_div (Nat.cast_nonneg r)]
    field_simp
  have h := congrArg (fun x : ℝ => x^(2 : ℕ)) he'
  simpa only [mul_pow, Real.sq_sqrt (Nat.cast_nonneg r),
    Real.sq_sqrt (Nat.cast_nonneg M)] using h

private lemma block_indices (P : Finset ℕ) (M : ℕ) {n : ℕ} (hn : 0 < n) :
    (fixedCoreSquarefreeIndices P M).filter (fun r => M/r=n) =
      fixedCoreSquarefreeIndices P (M/n) \ fixedCoreSquarefreeIndices P (M/(n+1)) := by
  ext r
  simp only [fixedCoreSquarefreeIndices, mem_filter, Finset.mem_sdiff, mem_Icc]
  constructor
  · rintro ⟨⟨hr, hsf⟩, he⟩
    have hhi : r ≤ M/n := (Nat.le_div_iff_mul_le hn).mpr (by
      have h := Nat.div_mul_le_self M r
      rw [he] at h
      simpa [mul_comm] using h)
    have hlo : ¬r ≤ M/(n+1) := by
      intro hlo
      have hm := (Nat.le_div_iff_mul_le (by omega : 0<n+1)).mp hlo
      have hle : n+1 ≤ M/r := (Nat.le_div_iff_mul_le hr.1).mpr (by simpa [mul_comm] using hm)
      omega
    exact ⟨⟨⟨hr.1,hhi⟩,hsf⟩, fun h => hlo h.1.2⟩
  · rintro ⟨⟨hr, hsf⟩, hlo⟩
    have hrM := hr.2.trans (Nat.div_le_self M n)
    refine ⟨⟨⟨hr.1,hrM⟩,hsf⟩, ?_⟩
    have hge : n ≤ M/r := (Nat.le_div_iff_mul_le hr.1).mpr (by
      have h := (Nat.le_div_iff_mul_le hn).mp hr.2
      simpa [mul_comm] using h)
    have hnot : ¬n+1 ≤ M/r := by
      intro h
      apply hlo
      have hm := (Nat.le_div_iff_mul_le hr.1).mp h
      exact ⟨⟨hr.1, (Nat.le_div_iff_mul_le (by omega : 0<n+1)).mpr
        (by simpa [mul_comm] using hm)⟩,hsf⟩
    omega

/-- Exact normalized source cell as the difference of two arithmetic
square-root-affine prefix sums. -/
theorem mobiusDivisorFixedCoreBlockEnergy_div_sq (P : Finset ℕ) {M n : ℕ}
    (hM : 0 < M) (hn : 0 < n) :
    mobiusDivisorFixedCoreBlockEnergy P M n/(M : ℝ)^(2 : ℕ) =
      (∑ r ∈ fixedCoreSquarefreeIndices P (M/n),
        (mobiusDivisorHeadBlockSlope P n+
          mobiusDivisorHeadBlockIntercept P n*Real.sqrt ((r : ℝ)/M))^(2 : ℕ))/(M : ℝ) -
      (∑ r ∈ fixedCoreSquarefreeIndices P (M/(n+1)),
        (mobiusDivisorHeadBlockSlope P n+
          mobiusDivisorHeadBlockIntercept P n*Real.sqrt ((r : ℝ)/M))^(2 : ℕ))/(M : ℝ) := by
  have hsub : fixedCoreSquarefreeIndices P (M/(n+1)) ⊆ fixedCoreSquarefreeIndices P (M/n) := by
    intro r hr
    obtain ⟨hr, hs⟩ := mem_filter.mp hr
    have hr' := mem_Icc.mp hr
    apply mem_filter.mpr
    exact ⟨mem_Icc.mpr ⟨hr'.1, hr'.2.trans (Nat.div_le_div_left (by omega : n≤n+1) hn)⟩, hs⟩
  unfold mobiusDivisorFixedCoreBlockEnergy
  have he : (∑ r ∈ (fixedCoreSquarefreeIndices P M).filter (fun r => M/r=n),
      (r : ℝ)*(mobiusDivisorInterpolatedFibre M r P ∅)^(2 : ℕ)) =
      (M : ℝ)*∑ r ∈ (fixedCoreSquarefreeIndices P M).filter (fun r => M/r=n),
        (mobiusDivisorHeadBlockSlope P n+
          mobiusDivisorHeadBlockIntercept P n*Real.sqrt ((r : ℝ)/M))^(2 : ℕ) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro r hr
    exact block_term P hM (mem_Icc.mp (mem_filter.mp (mem_filter.mp hr).1).1).1
      (mem_filter.mp hr).2
  rw [he, block_indices P M hn, sum_sdiff_eq_sub hsub]
  have hMR : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  field_simp

/-- Every fixed actual quotient block has an explicit quadratic-scale limit. -/
theorem tendsto_mobiusDivisorFixedCoreBlockEnergy_div_sq
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) {n : ℕ} (hn : 0 < n) :
    Tendsto (fun M : ℕ => mobiusDivisorFixedCoreBlockEnergy P M n/(M : ℝ)^(2 : ℕ)) atTop
      (𝓝 ((Sieve.squarefreeDensity * ∏ p ∈ P, (p : ℝ)/(p+1))*
        (mobiusDivisorHeadBlockPrimitive P n (1/(n : ℝ))-
          mobiusDivisorHeadBlockPrimitive P n (1/((n : ℝ)+1))))) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have h0 := tendsto_fixedCoreSquarefree_scaled_affine_sqrt_square P hP
    (mobiusDivisorHeadBlockSlope P n) (mobiusDivisorHeadBlockIntercept P n)
    (show 0 < 1/(n : ℝ) by positivity)
  have h1 := tendsto_fixedCoreSquarefree_scaled_affine_sqrt_square P hP
    (mobiusDivisorHeadBlockSlope P n) (mobiusDivisorHeadBlockIntercept P n)
    (show 0 < 1/((n : ℝ)+1) by positivity)
  have h := h0.sub h1
  have hc (M d : ℕ) : ⌊(1/(d : ℝ))*(M : ℝ)⌋₊ = M/d := by
    rw [one_div, mul_comm, ← div_eq_mul_inv, Nat.floor_div_natCast, Nat.floor_natCast]
  have he : (Sieve.squarefreeDensity * ∏ p ∈ P, (p : ℝ)/(p+1))*
      mobiusDivisorHeadBlockPrimitive P n (1/(n : ℝ)) -
      (Sieve.squarefreeDensity * ∏ p ∈ P, (p : ℝ)/(p+1))*
      mobiusDivisorHeadBlockPrimitive P n (1/((n : ℝ)+1)) =
      (Sieve.squarefreeDensity * ∏ p ∈ P, (p : ℝ)/(p+1))*
        (mobiusDivisorHeadBlockPrimitive P n (1/(n : ℝ))-
          mobiusDivisorHeadBlockPrimitive P n (1/((n : ℝ)+1))) := by ring
  change Tendsto _ atTop (𝓝 (_ * mobiusDivisorHeadBlockPrimitive P n (1/(n : ℝ)) -
    _ * mobiusDivisorHeadBlockPrimitive P n (1/((n : ℝ)+1)))) at h
  rw [he] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with M hM
  rw [mobiusDivisorFixedCoreBlockEnergy_div_sq P hM hn, hc]
  have hc' : ⌊(1/((n : ℝ)+1))*(M : ℝ)⌋₊ = M/(n+1) := by
    simpa using hc M (n+1)
  rw [hc']

end RHTower
