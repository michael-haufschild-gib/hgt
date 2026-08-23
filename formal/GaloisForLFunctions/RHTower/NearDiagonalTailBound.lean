import GaloisForLFunctions.RHTower.NearDiagonalInnerSum
import GaloisForLFunctions.RHTower.SqrtTelescopeSums

/-!
# The near-diagonal tail double sum

Summing equation (4) over the shift `r` with the harmonic weight `1/r`.
-/

namespace RHTower

noncomputable section

/-- The near-diagonal tail: the harmonically weighted double sum over `m` and the shift `r`. -/
def nearDiagonalTail (T ε : ℝ) (mLo mHi rLo : ℕ) : ℂ :=
  ∑ m ∈ Finset.Icc mLo mHi, ∑ r ∈ Finset.Icc rLo ⌊(m : ℝ) * ε⌋₊,
    Complex.exp (((2 * Real.pi * nearDiagonalPhase T r m : ℝ) : ℂ) * Complex.I) / r

/-- The shift ceiling is monotone in the modulus. -/
theorem shiftCeil_mono {ε : ℝ} (hε : 0 ≤ ε) {m m' : ℕ} (h : m ≤ m') :
    ⌊(m : ℝ) * ε⌋₊ ≤ ⌊(m' : ℝ) * ε⌋₊ := by
  refine Nat.floor_le_floor ?_
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast h) hε

/-- Exchanging the order of summation in the near-diagonal tail. -/
theorem nearDiagonalTail_swap (T ε : ℝ) (hε : 0 ≤ ε) (mLo mHi rLo : ℕ) :
    nearDiagonalTail T ε mLo mHi rLo
      = ∑ r ∈ Finset.Icc rLo ⌊(mHi : ℝ) * ε⌋₊,
          ∑ m ∈ (Finset.Icc mLo mHi).filter (fun m : ℕ => r ≤ ⌊(m : ℝ) * ε⌋₊),
            Complex.exp (((2 * Real.pi * nearDiagonalPhase T r m : ℝ) : ℂ) * Complex.I) / r := by
  rw [nearDiagonalTail]
  refine Finset.sum_comm' ?_
  intro m r
  simp only [Finset.mem_Icc, Finset.mem_filter]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    exact ⟨⟨⟨h1, h2⟩, h4⟩, h3, le_trans h4 (shiftCeil_mono hε h2)⟩
  · rintro ⟨⟨⟨h1, h2⟩, h4⟩, h3, -⟩
    exact ⟨⟨h1, h2⟩, h3, h4⟩

/-- The set of moduli admitting a given shift is an interval. -/
theorem filter_shiftCeil_eq_Ico {ε : ℝ} (hε : 0 ≤ ε) (mLo mHi r : ℕ)
    (hne : ((Finset.Icc mLo mHi).filter (fun m : ℕ => r ≤ ⌊(m : ℝ) * ε⌋₊)).Nonempty) :
    (Finset.Icc mLo mHi).filter (fun m : ℕ => r ≤ ⌊(m : ℝ) * ε⌋₊)
      = Finset.Ico (((Finset.Icc mLo mHi).filter (fun m : ℕ => r ≤ ⌊(m : ℝ) * ε⌋₊)).min' hne)
          (mHi + 1) := by
  have hmin := Finset.min'_mem _ hne
  simp only [Finset.mem_filter, Finset.mem_Icc] at hmin
  ext m
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ico]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨Finset.min'_le _ _ ?_, by omega⟩
    simp only [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨h1, h2⟩, h3⟩
  · rintro ⟨h1, h2⟩
    refine ⟨⟨le_trans hmin.1.1 h1, by omega⟩, ?_⟩
    exact le_trans hmin.2 (shiftCeil_mono hε h1)

/-- Equation (4) applied to the moduli admitting a fixed shift `r`. -/
theorem norm_inner_shift_le {T ε : ℝ} (hT : 0 < T) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    {mLo mHi r : ℕ} (hmLo : 1 ≤ mLo) (hr : 1 ≤ r)
    (hlam : nearDiagonalLambda T r (mLo : ℝ) ≤ 1) :
    ‖∑ m ∈ (Finset.Icc mLo mHi).filter (fun m : ℕ => r ≤ ⌊(m : ℝ) * ε⌋₊),
        Complex.exp (((2 * Real.pi * nearDiagonalPhase T r m : ℝ) : ℂ) * Complex.I)‖
      ≤ 2500 * Real.sqrt (T * r / (36 * Real.pi * mLo))
        + 22 * Real.sqrt (36 * Real.pi / (T * r)) * Real.sqrt (((mHi + 1 : ℕ) : ℝ) ^ 3) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hmLoR : (0 : ℝ) < (mLo : ℝ) := by exact_mod_cast hmLo
  by_cases hne : ((Finset.Icc mLo mHi).filter (fun m : ℕ => r ≤ ⌊(m : ℝ) * ε⌋₊)).Nonempty
  · set A := ((Finset.Icc mLo mHi).filter (fun m : ℕ => r ≤ ⌊(m : ℝ) * ε⌋₊)).min' hne with hA
    have hmem := Finset.min'_mem _ hne
    simp only [Finset.mem_filter, Finset.mem_Icc] at hmem
    have hmLoA : mLo ≤ A := hmem.1.1
    have hA1 : 1 ≤ A := le_trans hmLo hmLoA
    have hAR : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA1
    have hrA : (r : ℝ) ≤ (A : ℝ) := by
      have h1 : (r : ℝ) ≤ ((⌊(A : ℝ) * ε⌋₊ : ℕ) : ℝ) := by exact_mod_cast hmem.2
      have h2 : ((⌊(A : ℝ) * ε⌋₊ : ℕ) : ℝ) ≤ (A : ℝ) * ε :=
        Nat.floor_le (by positivity)
      nlinarith
    have hlamA : nearDiagonalLambda T r (A : ℝ) ≤ 1 :=
      le_trans (nearDiagonalLambda_anti hT hrR hmLoR (by exact_mod_cast hmLoA)) hlam
    rw [filter_shiftCeil_eq_Ico hε0 mLo mHi r hne]
    have hsum : ∑ m ∈ Finset.Ico A (mHi + 1),
        Complex.exp (((2 * Real.pi * nearDiagonalPhase T r m : ℝ) : ℂ) * Complex.I)
        = nearDiagonalSum T r A (mHi + 1) := rfl
    rw [hsum]
    refine le_trans (norm_nearDiagonalSum_le_final hT hrR A (mHi + 1) hA1 hrA hlamA) ?_
    have hfirst : Real.sqrt (T * r / (36 * Real.pi * A))
        ≤ Real.sqrt (T * r / (36 * Real.pi * mLo)) := by
      refine Real.sqrt_le_sqrt ?_
      refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
      have : (mLo : ℝ) ≤ (A : ℝ) := by exact_mod_cast hmLoA
      nlinarith
    have hcast : (((mHi + 1 : ℕ)) : ℝ) = ((mHi : ℝ) + 1) := by push_cast; ring
    have hs2 : (0 : ℝ) ≤ Real.sqrt (36 * Real.pi / (T * r)) := Real.sqrt_nonneg _
    have h3 : (0 : ℝ) ≤ Real.sqrt (((mHi : ℝ) + 1) ^ 3) := Real.sqrt_nonneg _
    rw [hcast]
    nlinarith
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne, Finset.sum_empty, norm_zero]
    positivity

/-- Splitting off the shift dependence of the equation-(4) bound after the harmonic weight. -/
theorem shift_weight_identity {T mLoR B r : ℝ} (hT : 0 < T) (hmLoR : 0 < mLoR) (hr : 0 < r) :
    (2500 * Real.sqrt (T * r / (36 * Real.pi * mLoR))
        + 22 * Real.sqrt (36 * Real.pi / (T * r)) * B) / r
      = 2500 * Real.sqrt (T / (36 * Real.pi * mLoR)) * (1 / Real.sqrt r)
        + 22 * Real.sqrt (36 * Real.pi / T) * B * (1 / Real.sqrt (r ^ 3)) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hs0 : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr
  have hss : Real.sqrt r * Real.sqrt r = r := Real.mul_self_sqrt hr.le
  have h1 : Real.sqrt (T * r / (36 * Real.pi * mLoR))
      = Real.sqrt (T / (36 * Real.pi * mLoR)) * Real.sqrt r := by
    rw [← Real.sqrt_mul (by positivity)]
    congr 1
    field_simp
  have h2aux : Real.sqrt (36 * Real.pi / (T * r)) * Real.sqrt r
      = Real.sqrt (36 * Real.pi / T) := by
    rw [← Real.sqrt_mul (by positivity)]
    congr 1
    field_simp
  have h2 : Real.sqrt (36 * Real.pi / (T * r))
      = Real.sqrt (36 * Real.pi / T) / Real.sqrt r := by
    rw [← h2aux]
    field_simp
  have h3 : Real.sqrt (r ^ 3) = r * Real.sqrt r := by
    rw [show r ^ 3 = r ^ 2 * r by ring, Real.sqrt_mul (by positivity), Real.sqrt_sq hr.le]
  rw [h1, h2, h3]
  field_simp
  rw [Real.sq_sqrt hr.le]

/-- **Equation (5), abstract form.**  The harmonically weighted near-diagonal tail. -/
theorem norm_nearDiagonalTail_le {T ε : ℝ} (hT : 0 < T) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    {mLo mHi rLo : ℕ} (hmLo : 1 ≤ mLo) (hrLo : 2 ≤ rLo)
    (hlam : nearDiagonalLambda T ((⌊(mHi : ℝ) * ε⌋₊ : ℕ) : ℝ) (mLo : ℝ) ≤ 1) :
    ‖nearDiagonalTail T ε mLo mHi rLo‖
      ≤ 5000 * Real.sqrt (T / (36 * Real.pi * mLo))
            * Real.sqrt ((⌊(mHi : ℝ) * ε⌋₊ : ℕ) : ℝ)
        + 44 * Real.sqrt (36 * Real.pi / T) * Real.sqrt ((((mHi + 1 : ℕ)) : ℝ) ^ 3)
            / Real.sqrt ((rLo - 1 : ℕ) : ℝ) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hmLoR : (0 : ℝ) < (mLo : ℝ) := by exact_mod_cast hmLo
  set rMax := ⌊(mHi : ℝ) * ε⌋₊ with hrMaxDef
  set C1 : ℝ := 2500 * Real.sqrt (T / (36 * Real.pi * mLo)) with hC1
  set C2 : ℝ := 22 * Real.sqrt (36 * Real.pi / T)
      * Real.sqrt ((((mHi + 1 : ℕ)) : ℝ) ^ 3) with hC2
  have hC1nn : 0 ≤ C1 := by rw [hC1]; positivity
  have hC2nn : 0 ≤ C2 := by rw [hC2]; positivity
  rw [nearDiagonalTail_swap T ε hε0 mLo mHi rLo]
  by_cases hcase : rLo ≤ rMax
  · refine le_trans (norm_sum_le _ _) ?_
    have key : ∀ r ∈ Finset.Icc rLo rMax,
        ‖∑ m ∈ (Finset.Icc mLo mHi).filter (fun m : ℕ => r ≤ ⌊(m : ℝ) * ε⌋₊),
            Complex.exp (((2 * Real.pi * nearDiagonalPhase T r m : ℝ) : ℂ) * Complex.I) / r‖
          ≤ C1 * (1 / Real.sqrt r) + C2 * (1 / Real.sqrt ((r : ℝ) ^ 3)) := by
      intro r hr
      rw [Finset.mem_Icc] at hr
      have hr1 : 1 ≤ r := by omega
      have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr1
      have hlamr : nearDiagonalLambda T (r : ℝ) (mLo : ℝ) ≤ 1 := by
        refine le_trans ?_ hlam
        rw [nearDiagonalLambda, nearDiagonalLambda]
        have hrle : (r : ℝ) ≤ ((rMax : ℕ) : ℝ) := by exact_mod_cast hr.2
        gcongr
      have hbase := norm_inner_shift_le (T := T) (ε := ε) hT hε0 hε1
        (mLo := mLo) (mHi := mHi) (r := r) hmLo hr1 hlamr
      rw [← Finset.sum_div, norm_div, Complex.norm_natCast]
      calc ‖∑ m ∈ (Finset.Icc mLo mHi).filter (fun m : ℕ => r ≤ ⌊(m : ℝ) * ε⌋₊),
              Complex.exp (((2 * Real.pi * nearDiagonalPhase T r m : ℝ) : ℂ) * Complex.I)‖
              / (r : ℝ)
          ≤ (2500 * Real.sqrt (T * r / (36 * Real.pi * mLo))
              + 22 * Real.sqrt (36 * Real.pi / (T * r))
                  * Real.sqrt ((((mHi + 1 : ℕ)) : ℝ) ^ 3)) / (r : ℝ) := by
            gcongr
        _ = C1 * (1 / Real.sqrt r) + C2 * (1 / Real.sqrt ((r : ℝ) ^ 3)) := by
            rw [hC1, hC2]
            rw [shift_weight_identity (T := T) (mLoR := (mLo : ℝ))
              (B := Real.sqrt ((((mHi + 1 : ℕ)) : ℝ) ^ 3)) (r := (r : ℝ)) hT hmLoR hrR]
    refine le_trans (Finset.sum_le_sum key) ?_
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have hS1 : ∑ r ∈ Finset.Icc rLo rMax, 1 / Real.sqrt (r : ℝ)
        ≤ 2 * Real.sqrt ((rMax : ℕ) : ℝ) := by
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_) (sum_inv_sqrt_le rMax)
      · intro x hx
        rw [Finset.mem_Icc] at hx ⊢
        omega
      · intro i _ _
        positivity
    have hS2 : ∑ r ∈ Finset.Icc rLo rMax, 1 / Real.sqrt ((r : ℝ) ^ 3)
        ≤ 2 / Real.sqrt ((rLo - 1 : ℕ) : ℝ) := sum_inv_sqrt_cube_le hrLo rMax (by omega)
    have hgoal1 : C1 * (∑ r ∈ Finset.Icc rLo rMax, 1 / Real.sqrt (r : ℝ))
        ≤ C1 * (2 * Real.sqrt ((rMax : ℕ) : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hS1 hC1nn
    have hgoal2 : C2 * (∑ r ∈ Finset.Icc rLo rMax, 1 / Real.sqrt ((r : ℝ) ^ 3))
        ≤ C2 * (2 / Real.sqrt ((rLo - 1 : ℕ) : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hS2 hC2nn
    have hfin : C1 * (2 * Real.sqrt ((rMax : ℕ) : ℝ))
          + C2 * (2 / Real.sqrt ((rLo - 1 : ℕ) : ℝ))
        = 5000 * Real.sqrt (T / (36 * Real.pi * mLo)) * Real.sqrt ((rMax : ℕ) : ℝ)
          + 44 * Real.sqrt (36 * Real.pi / T) * Real.sqrt ((((mHi + 1 : ℕ)) : ℝ) ^ 3)
              / Real.sqrt ((rLo - 1 : ℕ) : ℝ) := by
      rw [hC1, hC2]; ring
    linarith
  · have hempty : Finset.Icc rLo rMax = ∅ := by
      rw [Finset.Icc_eq_empty_iff]
      omega
    rw [hempty, Finset.sum_empty, norm_zero]
    positivity

/-! ## The Kubalalika localization -/

/-- The localization width `T^{-1/4}`. -/
def kubalalikaEps (T : ℝ) : ℝ := 1 / Real.sqrt (Real.sqrt T)

/-- The unweighted near-diagonal tail at the Kubalalika localization. -/
def kubalalikaTailSum (T : ℝ) : ℂ :=
  nearDiagonalTail T (kubalalikaEps T)
    ⌈T / ((1 + kubalalikaEps T) * (Real.log T) ^ 2)⌉₊
    ⌊T * (1 + kubalalikaEps T)⌋₊
    ⌈Real.sqrt (Real.sqrt T)⌉₊

theorem kubalalikaEps_pow {u : ℝ} (hu : 1 ≤ u) : kubalalikaEps (u ^ 8) = 1 / u ^ 2 := by
  have hu0 : (0 : ℝ) ≤ u := by linarith
  rw [kubalalikaEps, show u ^ 8 = (u ^ 4) ^ 2 by ring, Real.sqrt_sq (by positivity),
    show u ^ 4 = (u ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]

theorem sqrt_sqrt_pow {u : ℝ} (hu : 1 ≤ u) : Real.sqrt (Real.sqrt (u ^ 8)) = u ^ 2 := by
  have hu0 : (0 : ℝ) ≤ u := by linarith
  rw [show u ^ 8 = (u ^ 4) ^ 2 by ring, Real.sqrt_sq (by positivity),
    show u ^ 4 = (u ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]

theorem log_pow_eight_le {u : ℝ} (hu : 1 ≤ u) : Real.log (u ^ 8) ≤ 16 * Real.sqrt u := by
  have hu0 : (0 : ℝ) < u := by linarith
  have h1 : Real.log (u ^ 8) = 8 * Real.log u := by rw [Real.log_pow]; norm_num
  have h2 : Real.log (Real.sqrt u) ≤ Real.sqrt u - 1 :=
    Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hu0)
  rw [Real.log_sqrt hu0.le] at h2
  have hs : 0 ≤ Real.sqrt u := Real.sqrt_nonneg _
  linarith

set_option maxHeartbeats 1600000 in
/-- **Equation (5).**  The unweighted near-diagonal tail is `O(T^{7/8} + T^{3/8} log T)`. -/
theorem norm_kubalalikaTailSum_le_pow {u : ℝ} (hu : 20 ≤ u) :
    ‖kubalalikaTailSum (u ^ 8)‖ ≤ 5000 * (u ^ 7 + u ^ 3 * Real.log (u ^ 8)) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hpi3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hpi4 : Real.pi ≤ 4 := Real.pi_le_four
  have hu0 : (0 : ℝ) < u := by linarith
  have hu1 : (1 : ℝ) ≤ u := by linarith
  have hT : (0 : ℝ) < u ^ 8 := by positivity
  have hu8 : (20 : ℝ) ^ 8 ≤ u ^ 8 := pow_le_pow_left₀ (by norm_num) hu 8
  have hT1 : (1 : ℝ) < u ^ 8 := by norm_num at hu8; linarith
  have hu2 : (400 : ℝ) ≤ u ^ 2 := by nlinarith
  have heps : kubalalikaEps (u ^ 8) = 1 / u ^ 2 := kubalalikaEps_pow hu1
  have hsq : Real.sqrt (Real.sqrt (u ^ 8)) = u ^ 2 := sqrt_sqrt_pow hu1
  have hepsnn : 0 ≤ kubalalikaEps (u ^ 8) := by rw [heps]; positivity
  have hepsle : kubalalikaEps (u ^ 8) ≤ 1 := by
    rw [heps, div_le_one (by positivity)]; linarith
  simp only [kubalalikaTailSum]
  set L := Real.log (u ^ 8) with hLdef
  have hL0 : 0 < L := Real.log_pos hT1
  have hL16 : L ≤ 16 * Real.sqrt u := log_pow_eight_le hu1
  have hL6 : L ^ 6 ≤ 16 ^ 6 * u ^ 3 := by
    have h1 : L ^ 6 ≤ (16 * Real.sqrt u) ^ 6 := pow_le_pow_left₀ hL0.le hL16 6
    have h2 : (16 * Real.sqrt u) ^ 6 = 16 ^ 6 * u ^ 3 := by
      rw [mul_pow]
      congr 1
      rw [show (6 : ℕ) = 2 * 3 by norm_num, pow_mul, Real.sq_sqrt hu0.le]
    linarith
  clear_value L
  clear hLdef hL16
  have hVpos : 0 < u ^ 8 / ((1 + kubalalikaEps (u ^ 8)) * L ^ 2) := by
    have h1 : (0 : ℝ) < 1 + kubalalikaEps (u ^ 8) := by linarith
    positivity
  set mLo := ⌈u ^ 8 / ((1 + kubalalikaEps (u ^ 8)) * L ^ 2)⌉₊ with hmLodef
  set mHi := ⌊u ^ 8 * (1 + kubalalikaEps (u ^ 8))⌋₊ with hmHidef
  set rLo := ⌈Real.sqrt (Real.sqrt (u ^ 8))⌉₊ with hrLodef
  have hmLo1 : 1 ≤ mLo := Nat.ceil_pos.mpr hVpos
  have hmLoR : u ^ 8 / (2 * L ^ 2) ≤ (mLo : ℝ) := by
    refine le_trans ?_ (Nat.le_ceil _)
    have hden : (0 : ℝ) < (1 + kubalalikaEps (u ^ 8)) * L ^ 2 := by
      have h1 : (0 : ℝ) < 1 + kubalalikaEps (u ^ 8) := by linarith
      positivity
    rw [div_le_div_iff₀ (by positivity) hden]
    nlinarith [mul_le_mul_of_nonneg_left hepsle (show (0:ℝ) ≤ u ^ 8 * L ^ 2 by positivity)]
  have hrLoR : u ^ 2 ≤ (rLo : ℝ) := by
    rw [hrLodef, hsq]; exact Nat.le_ceil _
  have hrLo2 : 2 ≤ rLo := by
    have h : (2 : ℝ) ≤ (rLo : ℝ) := by linarith
    exact_mod_cast h
  have hmHiR : (mHi : ℝ) ≤ 2 * u ^ 8 := by
    refine le_trans (Nat.floor_le (by positivity)) ?_
    nlinarith
  clear_value mLo mHi rLo
  clear hmLodef hmHidef hrLodef hVpos hsq
  have hmLoRpos : (0 : ℝ) < (mLo : ℝ) := by exact_mod_cast hmLo1
  have hrMaxR : ((⌊(mHi : ℝ) * kubalalikaEps (u ^ 8)⌋₊ : ℕ) : ℝ) ≤ 2 * u ^ 6 := by
    refine le_trans (Nat.floor_le (by positivity)) ?_
    rw [heps, show (mHi : ℝ) * (1 / u ^ 2) = (mHi : ℝ) / u ^ 2 by ring,
      div_le_iff₀ (by positivity)]
    nlinarith [hmHiR, pow_pos hu0 2]
  have hu7 : (1280000000 : ℝ) ≤ u ^ 7 := by
    have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 20) hu 7
    norm_num at h; linarith
  have hL6b : L ^ 6 ≤ (27 / 4) * u ^ 10 := by
    have h3 : (0 : ℝ) < u ^ 3 := by positivity
    have heq : u ^ 10 = u ^ 7 * u ^ 3 := by ring
    nlinarith [hL6, hu7, h3]
  have hlam : nearDiagonalLambda (u ^ 8)
      ((⌊(mHi : ℝ) * kubalalikaEps (u ^ 8)⌋₊ : ℕ) : ℝ) (mLo : ℝ) ≤ 1 := by
    rw [nearDiagonalLambda, div_le_one (by positivity)]
    have hA : u ^ 8 * ((⌊(mHi : ℝ) * kubalalikaEps (u ^ 8)⌋₊ : ℕ) : ℝ) ≤ 2 * u ^ 14 := by
      nlinarith [hrMaxR, pow_pos hu0 8]
    have hC : 2 * u ^ 14 ≤ 108 * (u ^ 8 / (2 * L ^ 2)) ^ 3 := by
      have heq : (108 : ℝ) * (u ^ 8 / (2 * L ^ 2)) ^ 3 = (27 / 2) * u ^ 24 / L ^ 6 := by
        field_simp; ring
      rw [heq, le_div_iff₀ (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_left hL6b (show (0:ℝ) ≤ 2 * u ^ 14 by positivity)]
    have hmLo3 : (u ^ 8 / (2 * L ^ 2)) ^ 3 ≤ (mLo : ℝ) ^ 3 :=
      pow_le_pow_left₀ (by positivity) hmLoR 3
    have hB : (108 : ℝ) * (mLo : ℝ) ^ 3 ≤ 36 * Real.pi * (mLo : ℝ) ^ 3 := by
      nlinarith [pow_pos hmLoRpos 3]
    linarith
  refine le_trans (norm_nearDiagonalTail_le hT hepsnn hepsle hmLo1 hrLo2 hlam) ?_
  have hA : Real.sqrt (u ^ 8 / (36 * Real.pi * (mLo : ℝ))) ≤ L / 7 := by
    refine le_trans (Real.sqrt_le_sqrt ?_) (le_of_eq (Real.sqrt_sq (by positivity)))
    rw [div_le_iff₀ (by positivity)]
    have hml : (108 : ℝ) * (u ^ 8 / (2 * L ^ 2)) ≤ 36 * Real.pi * (mLo : ℝ) := by
      nlinarith [hmLoR]
    have hsqr : (L / 7) ^ 2 = L ^ 2 / 49 := by ring
    have hprod : (L ^ 2 / 49) * (108 * (u ^ 8 / (2 * L ^ 2)))
        ≤ (L ^ 2 / 49) * (36 * Real.pi * (mLo : ℝ)) := by
      have : (0 : ℝ) ≤ L ^ 2 / 49 := by positivity
      nlinarith [hml]
    have heq : (L ^ 2 / 49) * (108 * (u ^ 8 / (2 * L ^ 2))) = 54 * u ^ 8 / 49 := by
      field_simp; ring
    rw [hsqr]
    nlinarith [hprod, heq, hT]
  have hB : Real.sqrt (((⌊(mHi : ℝ) * kubalalikaEps (u ^ 8)⌋₊ : ℕ) : ℝ)) ≤ (3 / 2) * u ^ 3 := by
    refine le_trans (Real.sqrt_le_sqrt ?_) (le_of_eq (Real.sqrt_sq (by positivity)))
    nlinarith [hrMaxR, pow_pos hu0 6]
  have hC : Real.sqrt (36 * Real.pi / u ^ 8) ≤ 12 / u ^ 4 := by
    refine le_trans (Real.sqrt_le_sqrt ?_) (le_of_eq (Real.sqrt_sq (by positivity)))
    rw [div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : ((u : ℝ) ^ 4) ^ 2 = u ^ 8 := by ring
    rw [h1]
    nlinarith [pow_pos hu0 8]
  have hD : Real.sqrt ((((mHi + 1 : ℕ)) : ℝ) ^ 3) ≤ (26 / 5) * u ^ 12 := by
    refine le_trans (Real.sqrt_le_sqrt ?_) (le_of_eq (Real.sqrt_sq (by positivity)))
    have hcast : (((mHi + 1 : ℕ)) : ℝ) = (mHi : ℝ) + 1 := by push_cast; ring
    rw [hcast]
    have h1 : (mHi : ℝ) + 1 ≤ 3 * u ^ 8 := by nlinarith [pow_pos hu0 8]
    have h2 : (0 : ℝ) ≤ (mHi : ℝ) + 1 := by positivity
    have h3 : ((mHi : ℝ) + 1) ^ 3 ≤ (3 * u ^ 8) ^ 3 := pow_le_pow_left₀ h2 h1 3
    nlinarith [pow_pos hu0 24]
  have hE : (2 / 3) * u ≤ Real.sqrt (((rLo - 1 : ℕ)) : ℝ) := by
    have hcast : (((rLo - 1 : ℕ)) : ℝ) = (rLo : ℝ) - 1 := by
      have h1 : 1 ≤ rLo := by omega
      push_cast [Nat.cast_sub h1]; ring
    rw [hcast]
    refine le_trans (le_of_eq (Real.sqrt_sq (by positivity)).symm) (Real.sqrt_le_sqrt ?_)
    nlinarith
  have hEpos : (0 : ℝ) < Real.sqrt (((rLo - 1 : ℕ)) : ℝ) := by
    have h1 : (0 : ℝ) < (2 / 3) * u := by positivity
    linarith
  have hBnn : (0 : ℝ) ≤ Real.sqrt (((⌊(mHi : ℝ) * kubalalikaEps (u ^ 8)⌋₊ : ℕ) : ℝ)) :=
    Real.sqrt_nonneg _
  have hDnn : (0 : ℝ) ≤ Real.sqrt ((((mHi + 1 : ℕ)) : ℝ) ^ 3) := Real.sqrt_nonneg _
  have hterm1 : 5000 * Real.sqrt (u ^ 8 / (36 * Real.pi * (mLo : ℝ)))
      * Real.sqrt (((⌊(mHi : ℝ) * kubalalikaEps (u ^ 8)⌋₊ : ℕ) : ℝ)) ≤ 5000 * (u ^ 3 * L) := by
    have hprod : Real.sqrt (u ^ 8 / (36 * Real.pi * (mLo : ℝ)))
        * Real.sqrt (((⌊(mHi : ℝ) * kubalalikaEps (u ^ 8)⌋₊ : ℕ) : ℝ))
        ≤ (L / 7) * ((3 / 2) * u ^ 3) := mul_le_mul hA hB hBnn (by positivity)
    nlinarith [hprod, mul_nonneg (le_of_lt (pow_pos hu0 3)) hL0.le]
  have hterm2 : 44 * Real.sqrt (36 * Real.pi / u ^ 8)
      * Real.sqrt ((((mHi + 1 : ℕ)) : ℝ) ^ 3) / Real.sqrt (((rLo - 1 : ℕ)) : ℝ)
      ≤ 5000 * u ^ 7 := by
    rw [div_le_iff₀ hEpos]
    have hprod : Real.sqrt (36 * Real.pi / u ^ 8) * Real.sqrt ((((mHi + 1 : ℕ)) : ℝ) ^ 3)
        ≤ (12 / u ^ 4) * ((26 / 5) * u ^ 12) := mul_le_mul hC hD hDnn (by positivity)
    have heq : (12 / u ^ 4) * ((26 / 5) * u ^ 12) = (312 / 5) * u ^ 8 := by
      field_simp; ring
    have h1 : 44 * Real.sqrt (36 * Real.pi / u ^ 8)
        * Real.sqrt ((((mHi + 1 : ℕ)) : ℝ) ^ 3) ≤ (13728 / 5) * u ^ 8 := by
      nlinarith [hprod, heq]
    have h2 : 5000 * u ^ 7 * ((2 / 3) * u) ≤ 5000 * u ^ 7 * Real.sqrt (((rLo - 1 : ℕ)) : ℝ) := by
      nlinarith [hE, pow_pos hu0 7]
    have h3 : (5000 : ℝ) * u ^ 7 * ((2 / 3) * u) = (10000 / 3) * u ^ 8 := by ring
    nlinarith [h1, h2, h3, pow_pos hu0 8]
  linarith

set_option maxHeartbeats 800000 in
/-- **Equation (5), in the original variable.**  Eventually in `T`, the unweighted near-diagonal
tail is at most `5000 (T^{7/8} + T^{3/8} log T)`. -/
theorem norm_kubalalikaTailSum_le :
    ∀ᶠ T : ℝ in Filter.atTop,
      ‖kubalalikaTailSum T‖
        ≤ 5000 * (T ^ ((7 : ℝ) / 8) + T ^ ((3 : ℝ) / 8) * Real.log T) := by
  filter_upwards [Filter.eventually_ge_atTop ((20 : ℝ) ^ 8)] with T hT
  have hT0 : (0 : ℝ) < T := by
    have : (0 : ℝ) < (20 : ℝ) ^ 8 := by norm_num
    linarith
  set u := T ^ ((1 : ℝ) / 8) with hudef
  have hu0 : (0 : ℝ) < u := Real.rpow_pos_of_pos hT0 _
  have hu8 : u ^ 8 = T := by
    rw [hudef, ← Real.rpow_natCast (T ^ ((1 : ℝ) / 8)) 8, ← Real.rpow_mul hT0.le]
    norm_num
  have hu : 20 ≤ u := by
    have h1 : ((20 : ℝ) ^ 8) ^ ((1 : ℝ) / 8) ≤ u :=
      Real.rpow_le_rpow (by norm_num) hT (by norm_num)
    have h2 : ((20 : ℝ) ^ 8) ^ ((1 : ℝ) / 8) = 20 := by
      rw [← Real.rpow_natCast (20 : ℝ) 8, ← Real.rpow_mul (by norm_num)]
      norm_num
    linarith [h2 ▸ h1]
  have h7 : T ^ ((7 : ℝ) / 8) = u ^ 7 := by
    rw [← hu8, ← Real.rpow_natCast u 8, ← Real.rpow_mul hu0.le]
    norm_num
  have h3 : T ^ ((3 : ℝ) / 8) = u ^ 3 := by
    rw [← hu8, ← Real.rpow_natCast u 8, ← Real.rpow_mul hu0.le]
    norm_num
  rw [h7, h3, ← hu8]
  exact norm_kubalalikaTailSum_le_pow hu

end

end RHTower
