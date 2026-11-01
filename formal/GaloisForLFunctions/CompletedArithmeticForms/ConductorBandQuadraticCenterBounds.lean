import GaloisForLFunctions.CompletedArithmeticForms.ConductorBandPrimeAndCenterBounds
import GaloisForLFunctions.HTGeometry.HilbertMatrixNormBound

/-!
# Quadratic center-collar decay

The reciprocal-sum kernel uses the Hilbert bound, the truncated difference kernel
uses its logarithmic row sum, and the far mean-zero row uses periodic cancellation.
Both arguments retain their linear horizon moment.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Finset Filter Topology ArithmeticFunction
open scoped BigOperators RealInnerProductSpace Classical
namespace GaloisForLFunctions.CompletedArithmeticForms
open SignedArithmeticHodgeTheory RenormalizedArithmeticPotentialTheory
  CriticalArithmeticCorrelationTheory SuccessorShellArithmetic
  ArithmeticIntersectionTheory ArithmeticEffectivityTheory ArithmeticElectrostatics
  BezoutValuationIncidence HTGeometry RenormalizedBiarithmeticGeometry SpacingScaleHarmonicAnalysis

private theorem arithmeticPoleKernel_bilinear_eq_zero {N : ℕ} {a b : ℕ → ℝ}
    (ha : SelectiveMultiscaleArithmeticPositivity.harmonicSum N a = 0)
    (hb : SelectiveMultiscaleArithmeticPositivity.harmonicSum N b = 0) :
    (∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N, b n * a j * arithmeticPoleKernel n j) = 0 := by
  unfold SelectiveMultiscaleArithmeticPositivity.harmonicSum at ha hb
  have hterm (n j : ℕ) : b n * a j * arithmeticPoleKernel n j =
      (b n * Real.sqrt n) * (a j / Real.sqrt j) +
        (b n / Real.sqrt n) * (a j * Real.sqrt j) := by
    unfold arithmeticPoleKernel
    ring
  simp only [hterm, sum_add_distrib, ← mul_sum, ← sum_mul]
  rw [ha, hb]
  ring

private theorem sum_range_normalizedRamanujanMode_eq_zero_of_two_le {m : ℕ} (hm : 2 ≤ m) :
    (∑ j ∈ range m, normalizedRamanujanMode m j) = 0 := by
  have hm0 : 0 < m := by omega
  have hp := periodMean_normalizedRamanujanMode_mul hm0 one_pos dvd_rfl (one_dvd m) hm0
  rw [if_neg (by omega : m ≠ 1)] at hp
  unfold periodMean at hp
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm0.ne'
  have hsum0 : (∑ j ∈ range m, normalizedRamanujanMode m j * normalizedRamanujanMode 1 j) = 0 :=
    (div_eq_zero_iff.mp hp).resolve_right hmR
  have hmode1 : ∀ j, normalizedRamanujanMode 1 j = 1 := fun j => by
    rw [normalizedRamanujanMode, ramanujanMode_one, Nat.totient_one, Nat.cast_one,
      Real.sqrt_one, div_one]
  simpa only [hmode1, mul_one] using hsum0

private theorem abs_sum_far_lower_div_sub_le {g : ℕ → ℝ} {B : ℝ} {n D : ℕ}
    (hB : ∀ l k : ℕ, l ≤ k → |∑ j ∈ Ico l k, g j| ≤ B) (hB0 : 0 ≤ B)
    (hD : 0 < D) (hn : D + 1 < n) :
    |∑ j ∈ Icc 1 (n - D - 1), g j / ((n : ℝ) - j)| ≤ B / (D : ℝ) := by
  let L := n - D - 1
  have hL1 : 1 ≤ L := by dsimp only [L]; omega
  have hpartial (k : ℕ) (hk : k ≤ L) : |∑ i ∈ range k, g (L - i)| ≤ B := by
    rw [← Nat.Ico_zero_eq_range, sum_Ico_reflect g 0 (show k ≤ L + 1 by omega), Nat.sub_zero]
    exact hB (L + 1 - k) (L + 1) (Nat.sub_le _ _)
  have hD0 : (0 : ℝ) < D := by exact_mod_cast hD
  have h := abs_sum_mul_le_of_finite_partial
    (g := fun i => g (L - i)) (w := fun i => 1 / ((D : ℝ) + 1 + i))
    L hpartial (fun i => by positivity)
    (fun i => by apply one_div_le_one_div_of_le (by positivity); push_cast; linarith)
  have heq : (∑ i ∈ range L, 1 / ((D : ℝ) + 1 + i) * g (L - i)) =
      ∑ j ∈ Icc 1 L, g j / ((n : ℝ) - j) := by
    refine sum_bij (fun i _ => L - i) ?_ ?_ ?_ ?_
    · intro i hi; have := mem_range.mp hi; exact mem_Icc.mpr ⟨by omega, by omega⟩
    · intro i hi j hj hij
      have := mem_range.mp hi; have := mem_range.mp hj
      change L - i = L - j at hij; omega
    · intro j hj; obtain ⟨h1, h2⟩ := mem_Icc.mp hj
      refine ⟨L - j, mem_range.mpr (by omega), by omega⟩
    · intro i hi
      have hi' := mem_range.mp hi
      have hnat : n - (L - i) = D + 1 + i := by dsimp only [L]; omega
      have hsub : (n : ℝ) - ((L - i : ℕ) : ℝ) = (D : ℝ) + 1 + i := by
        rw [← Nat.cast_sub (show L - i ≤ n by dsimp only [L]; omega), hnat]
        push_cast; ring
      rw [hsub]; ring
  rw [heq, Nat.cast_zero, add_zero] at h
  exact h.trans (by
    rw [mul_one_div]
    exact div_le_div_of_nonneg_left hB0 hD0 (by linarith))

private theorem abs_sum_far_erase_div_abs_sub_le {g : ℕ → ℝ} {B : ℝ} {n D N : ℕ}
    (hn : n ∈ Icc 1 N) (hD : 0 < D) (hB0 : 0 ≤ B)
    (hB : ∀ l k : ℕ, l ≤ k → |∑ j ∈ Ico l k, g j| ≤ B) :
    |∑ j ∈ (Icc 1 N).filter (fun j : ℕ => (D : ℝ) < |(n : ℝ) - j|),
      (g j / |(n : ℝ) - j|)| ≤ 2 * B / (D : ℝ) := by
  have hD0 : (0 : ℝ) < D := by exact_mod_cast hD
  let S_lo := (Icc 1 N).filter (fun j : ℕ => j + D < n)
  let S_hi := (Icc 1 N).filter (fun j : ℕ => n + D < j)
  have hpart : (Icc 1 N).filter (fun j : ℕ => (D : ℝ) < |(n : ℝ) - j|) = S_lo ∪ S_hi := by
    ext j
    simp only [S_lo, S_hi, mem_filter, mem_union]
    constructor
    · rintro ⟨hj, hgt⟩
      rcases lt_or_ge j n with hlt | hge
      · left
        refine ⟨hj, ?_⟩
        have habs : |(n : ℝ) - j| = (n : ℝ) - j :=
          abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hlt.le))
        rw [habs] at hgt
        have hcast : ((j + D : ℕ) : ℝ) < n := by push_cast; linarith only [hgt]
        exact_mod_cast hcast
      · right
        refine ⟨hj, ?_⟩
        have habs : |(n : ℝ) - j| = (j : ℝ) - n := by
          rw [abs_sub_comm]; exact abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hge))
        rw [habs] at hgt
        have hcast : ((n + D : ℕ) : ℝ) < j := by push_cast; linarith only [hgt]
        exact_mod_cast hcast
    · rintro (⟨hj, hlo⟩ | ⟨hj, hhi⟩)
      · refine ⟨hj, ?_⟩
        have hcast : ((j + D : ℕ) : ℝ) < n := by exact_mod_cast hlo
        have habs : |(n : ℝ) - j| = (n : ℝ) - j :=
          abs_of_nonneg (sub_nonneg.mpr (by push_cast at hcast; linarith))
        rw [habs]; push_cast at hcast; linarith
      · refine ⟨hj, ?_⟩
        have hcast : ((n + D : ℕ) : ℝ) < j := by exact_mod_cast hhi
        have habs : |(n : ℝ) - j| = (j : ℝ) - n := by
          rw [abs_sub_comm]; exact abs_of_nonneg (sub_nonneg.mpr (by push_cast at hcast; linarith))
        rw [habs]; push_cast at hcast; linarith
  have hdisj : Disjoint S_lo S_hi := by
    rw [Finset.disjoint_left]
    intro j hj1 hj2
    simp only [S_lo, S_hi, mem_filter] at hj1 hj2
    omega
  have hlo_bound : |∑ j ∈ S_lo, (g j / |(n : ℝ) - j|)| ≤ B / (D : ℝ) := by
    by_cases hbig : D + 1 < n
    · have hS_lo : S_lo = Icc 1 (n - D - 1) := by
        have hnN := (mem_Icc.mp hn).2
        ext j; simp only [S_lo, mem_filter, mem_Icc]; omega
      rw [hS_lo]
      have hcongr : (∑ j ∈ Icc 1 (n - D - 1), g j / |(n : ℝ) - j|) =
          ∑ j ∈ Icc 1 (n - D - 1), g j / ((n : ℝ) - j) :=
        sum_congr rfl fun j hj => by
          rw [abs_of_nonneg (sub_nonneg.mpr (by
            have := (mem_Icc.mp hj).2; exact_mod_cast (show j ≤ n by omega)))]
      rw [hcongr]
      exact abs_sum_far_lower_div_sub_le hB hB0 hD hbig
    · have hempty : S_lo = ∅ := by
        ext j; simp only [S_lo, mem_filter, mem_Icc, notMem_empty, iff_false]; omega
      rw [hempty, sum_empty, abs_zero]
      exact div_nonneg hB0 hD0.le
  have hhi_bound : |∑ j ∈ S_hi, (g j / |(n : ℝ) - j|)| ≤ B / (D : ℝ) := by
    have hS_hi : S_hi = Ico (n + D + 1) (N + 1) := by
      ext j; simp only [S_hi, mem_filter, mem_Icc, mem_Ico]; omega
    rw [hS_hi]
    have hcongr : (∑ j ∈ Ico (n + D + 1) (N + 1), g j / |(n : ℝ) - j|) =
        ∑ j ∈ Ico (n + D + 1) (N + 1), g j / (-(n : ℝ) + j) :=
      sum_congr rfl fun j hj => by
        have hjlo := (mem_Ico.mp hj).1
        rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast (show n ≤ j by omega)))]
        congr 1; ring
    rw [hcongr]
    have hab := abs_sum_Ico_div_add_le (r := -(n : ℝ)) hB (n + D + 1) (N + 1)
      (by push_cast; linarith only [hD0])
    have hden : -(n : ℝ) + (n + D + 1 : ℕ) = (D : ℝ) + 1 := by push_cast; ring
    rw [hden] at hab
    exact hab.trans (div_le_div_of_nonneg_left hB0 hD0 (by linarith))
  rw [hpart, sum_union hdisj]
  calc
    |(∑ j ∈ S_lo, (g j / |(n : ℝ) - j|)) + (∑ j ∈ S_hi, (g j / |(n : ℝ) - j|))| ≤
        |∑ j ∈ S_lo, (g j / |(n : ℝ) - j|)| + |∑ j ∈ S_hi, (g j / |(n : ℝ) - j|)| := abs_add_le _ _
    _ ≤ B / D + B / D := add_le_add hlo_bound hhi_bound
    _ = 2 * B / D := by ring

private def collarKernel (N : ℕ) (n j : ℕ) : ℝ :=
  (1 / (N : ℝ)) * archimedeanCenterKernel n j

private def collarNearKernel (D : ℕ) (n j : ℕ) : ℝ :=
  if n ≠ j ∧ |(n : ℝ) - j| ≤ D then (1 / 2 : ℝ) / |(n : ℝ) - j| else 0

private def collarRowSumHalf (R N : ℕ) (b : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ (Icc 1 N).erase n,
    (Real.sqrt n * Real.sqrt j / (2 * (N : ℝ) * ((n : ℝ) + j))) *
      primeHorizonExtension (∑ m ∈ Icc 1 R, b m • normalizedRamanujanHorizonVector m N) j

private def collarRowNear (R N : ℕ) (b : ℕ → ℝ) (n : ℕ) : ℝ :=
  Real.sqrt ((n : ℝ) / N) * ∑ j ∈ Icc 1 N, collarNearKernel (R ^ 4) n j *
    (Real.sqrt ((j : ℝ) / N) *
      primeHorizonExtension (∑ m ∈ Icc 1 R, b m • normalizedRamanujanHorizonVector m N) j)

private def collarRowFar (R N : ℕ) (b : ℕ → ℝ) (n : ℕ) : ℝ :=
  (Real.sqrt n / (2 * (N : ℝ) * Real.sqrt (Real.log N))) *
    ∑ j ∈ (Icc 1 N).filter (fun j : ℕ => ((R ^ 4 : ℕ) : ℝ) < |(n : ℝ) - j|),
      (∑ m ∈ Icc 1 R, b m * normalizedRamanujanMode m j) / |(n : ℝ) - j|

private theorem collarRow_eq_sum_three {R N : ℕ} (hR : 2 ≤ R) (hN1 : 1 ≤ N)
    (hL : 0 < Real.log N) (b : ℕ → ℝ) {n : ℕ} (hn : n ∈ Icc 1 N) :
    (∑ j ∈ Icc 1 N, collarKernel N n j *
        primeHorizonExtension (∑ m ∈ Icc 1 R, b m • normalizedRamanujanHorizonVector m N) j) =
      collarRowSumHalf R N b n + collarRowNear R N b n + collarRowFar R N b n := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hsL : 0 < Real.sqrt (Real.log N) := Real.sqrt_pos.mpr hL
  have hD0 : 0 < R ^ 4 := pow_pos (by omega : 0 < R) 4
  set uTilde := ∑ m ∈ Icc 1 R, b m • normalizedRamanujanHorizonVector m N
  have huTilde_ext : ∀ j ∈ Icc 1 N, primeHorizonExtension uTilde j =
      (Real.sqrt (Real.log N))⁻¹ * ((∑ m ∈ Icc 1 R, b m * normalizedRamanujanMode m j) / Real.sqrt j) := by
    intro j hj
    rw [primeHorizonExtension_coe _ ⟨j, hj⟩]
    change (PiLp.projₗ (𝕜 := ℝ) 2 (fun _ : PrimeHorizonIndex N => ℝ) ⟨j, hj⟩) uTilde = _
    dsimp only [uTilde]
    rw [map_sum, sum_div, mul_sum]
    refine sum_congr rfl fun m _ => ?_
    change b m * ((Real.sqrt (Real.log N))⁻¹ * (normalizedRamanujanMode m j / Real.sqrt j)) = _
    ring
  rw [← sum_erase_add (Icc 1 N) (fun j => collarKernel N n j * primeHorizonExtension uTilde j) hn]
  have hdiag : collarKernel N n n * primeHorizonExtension uTilde n = 0 := by
    unfold collarKernel; rw [archimedeanCenterKernel_self, mul_zero, zero_mul]
  rw [hdiag, add_zero]
  have hterm_erase : ∀ j ∈ (Icc 1 N).erase n,
      collarKernel N n j * primeHorizonExtension uTilde j =
        (Real.sqrt n * Real.sqrt j / (2 * (N : ℝ) * ((n : ℝ) + j))) *
          primeHorizonExtension uTilde j +
        (Real.sqrt n * Real.sqrt j / (2 * (N : ℝ) * |(n : ℝ) - j|)) *
          primeHorizonExtension uTilde j := by
    intro j hj
    obtain ⟨hjn, hjI⟩ := mem_erase.mp hj
    have h := archimedeanCenterKernel_div_sqrt_mul (mem_Icc.mp hn).1
      (mem_Icc.mp hjI).1 (Ne.symm hjn)
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
    have hj0 : (0 : ℝ) < j := by exact_mod_cast (mem_Icc.mp hjI).1
    have hsn := (Real.sqrt_pos.mpr hn0).ne'
    have hsj := (Real.sqrt_pos.mpr hj0).ne'
    unfold collarKernel
    have hker : archimedeanCenterKernel n j =
        (1 / 2 : ℝ) * (1 / |(n : ℝ) - j| + 1 / ((n : ℝ) + j)) *
          (Real.sqrt n * Real.sqrt j) :=
      (div_eq_iff (mul_ne_zero hsn hsj)).mp h
    have hadd_ne : (n : ℝ) + j ≠ 0 := by positivity
    have hsub_ne : |(n : ℝ) - j| ≠ 0 :=
      abs_ne_zero.mpr (sub_ne_zero.mpr (by exact_mod_cast Ne.symm hjn))
    rw [hker]
    field_simp [hN0.ne', hadd_ne, hsub_ne]
    ring
  rw [sum_congr rfl hterm_erase, sum_add_distrib]
  change collarRowSumHalf R N b n + _ =
    collarRowSumHalf R N b n + collarRowNear R N b n + collarRowFar R N b n
  rw [add_assoc]
  congr 1
  have near_eq : collarRowNear R N b n =
      ∑ j ∈ ((Icc 1 N).erase n).filter (fun j : ℕ => |(n : ℝ) - j| ≤ (R ^ 4 : ℕ)),
        (Real.sqrt n * Real.sqrt j / (2 * (N : ℝ) * |(n : ℝ) - j|)) *
          primeHorizonExtension uTilde j := by
    unfold collarRowNear collarNearKernel
    rw [mul_sum]
    have hsub : ((Icc 1 N).erase n).filter (fun j : ℕ => |(n : ℝ) - j| ≤ (R ^ 4 : ℕ)) ⊆ Icc 1 N :=
      fun j hj => (mem_erase.mp (mem_filter.mp hj).1).2
    rw [← sum_subset hsub]
    · refine sum_congr rfl fun j hj => ?_
      obtain ⟨hje, hle⟩ := mem_filter.mp hj
      have hne : n ≠ j := Ne.symm (mem_erase.mp hje).1
      rw [if_pos ⟨hne, hle⟩, Real.sqrt_div (Nat.cast_nonneg n),
        Real.sqrt_div (Nat.cast_nonneg j)]
      field_simp [hN0.ne', (Real.sqrt_pos.mpr hN0).ne']
      rw [Real.sq_sqrt hN0.le]
      dsimp only [uTilde]
      ring
    · intro j hjI hnot
      have hfalse : ¬(n ≠ j ∧ |(n : ℝ) - j| ≤ (R ^ 4 : ℕ)) := by
        rintro ⟨hne, hle⟩
        exact hnot (mem_filter.mpr ⟨mem_erase.mpr ⟨hne.symm, hjI⟩, hle⟩)
      rw [if_neg hfalse, zero_mul, mul_zero]
  have far_eq : collarRowFar R N b n =
      ∑ j ∈ ((Icc 1 N).erase n).filter (fun j : ℕ => ¬|(n : ℝ) - j| ≤ (R ^ 4 : ℕ)),
        (Real.sqrt n * Real.sqrt j / (2 * (N : ℝ) * |(n : ℝ) - j|)) *
          primeHorizonExtension uTilde j := by
    unfold collarRowFar
    have hf_eq : ((Icc 1 N).erase n).filter (fun j : ℕ => ¬|(n : ℝ) - j| ≤ (R ^ 4 : ℕ)) =
        (Icc 1 N).filter (fun j : ℕ => ((R ^ 4 : ℕ) : ℝ) < |(n : ℝ) - j|) := by
      ext j; simp only [mem_filter, mem_erase, not_le]
      constructor
      · rintro ⟨⟨_, hj⟩, hlt⟩; exact ⟨hj, hlt⟩
      · rintro ⟨hj, hlt⟩
        refine ⟨⟨?_, hj⟩, hlt⟩
        intro h; subst h; simp only [sub_self, abs_zero] at hlt
        linarith [show (0 : ℝ) < (R ^ 4 : ℕ) by exact_mod_cast hD0]
    rw [hf_eq, mul_sum]
    refine sum_congr rfl fun j hj => ?_
    have hjI := (mem_filter.mp hj).1
    have hj0 : (0 : ℝ) < j := by exact_mod_cast (mem_Icc.mp hjI).1
    have hsj := (Real.sqrt_pos.mpr hj0).ne'
    rw [huTilde_ext j hjI]
    field_simp [hN0.ne', hsL.ne', hsj]
  rw [near_eq, far_eq, sum_filter_add_sum_filter_not]

private theorem collar_v1_row_le {N n : ℕ} (hN1 : 1 ≤ N)
    (hL1 : 1 ≤ Real.log N) (hn : n ∈ Icc 1 N) :
    (∑ j ∈ Icc 1 N, collarKernel N n j *
      primeHorizonExtension (normalizedRamanujanHorizonVector 1 N) j) ≤
        3 * Real.sqrt (Real.log N) * Real.sqrt n / N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hL := zero_lt_one.trans_le hL1
  have hsL := Real.sqrt_pos.mpr hL
  have heq : (∑ j ∈ Icc 1 N, collarKernel N n j *
      primeHorizonExtension (normalizedRamanujanHorizonVector 1 N) j) =
      (1 / (N : ℝ)) * (Real.sqrt (Real.log N))⁻¹ *
        ∑ j ∈ Icc 1 N, archimedeanCenterKernel n j / Real.sqrt j := by
    rw [mul_sum]
    refine sum_congr rfl fun j hj => ?_
    rw [primeHorizonExtension_coe _ ⟨j, hj⟩]
    change (1 / (N : ℝ)) * archimedeanCenterKernel n j *
      ((Real.sqrt (Real.log N))⁻¹ * (normalizedRamanujanMode 1 j / Real.sqrt j)) = _
    have hm1 : normalizedRamanujanMode 1 j = 1 := by
      rw [normalizedRamanujanMode, ramanujanMode_one, Nat.totient_one, Nat.cast_one,
        Real.sqrt_one, div_one]
    rw [hm1]; ring
  rw [heq]
  have hH := sum_archimedeanCenterKernel_div_sqrt_le hn
  have hHN : (harmonic N : ℝ) + 1 ≤ 3 * Real.log N := by
    have hh := harmonic_le_one_add_log N
    linarith only [hh, hL1]
  calc
    (1 / (N : ℝ)) * (Real.sqrt (Real.log N))⁻¹ *
        (∑ j ∈ Icc 1 N, archimedeanCenterKernel n j / Real.sqrt j) ≤
        (1 / (N : ℝ)) * (Real.sqrt (Real.log N))⁻¹ *
          (Real.sqrt n * (3 * Real.log N)) :=
      mul_le_mul_of_nonneg_left
        (hH.trans (mul_le_mul_of_nonneg_left hHN (Real.sqrt_nonneg _))) (by positivity)
    _ = 3 * Real.sqrt (Real.log N) * Real.sqrt n / N := by
      field_simp [hN0.ne', hsL.ne']
      rw [Real.sq_sqrt hL.le]
      ring

private theorem collarNearKernel_row_le (R N : ℕ) :
    ∀ n ∈ Icc 1 N, (∑ j ∈ Icc 1 N, collarNearKernel (R ^ 4) n j) ≤
      5 * (1 + Real.log R) := by
  let D := R ^ 4
  intro n _
  let S_lo := (Icc 1 N).filter (fun j : ℕ => j < n ∧ n - j ≤ D)
  let S_hi := (Icc 1 N).filter (fun j : ℕ => n < j ∧ j - n ≤ D)
  have hsupp : ∀ j ∈ Icc 1 N, j ∉ S_lo ∪ S_hi → collarNearKernel D n j = 0 := by
    intro j hjI hnot
    unfold collarNearKernel
    rw [if_neg]
    rintro ⟨hne, hle⟩
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · apply hnot; refine mem_union.mpr (Or.inr (mem_filter.mpr ⟨hjI, hlt, ?_⟩))
      rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hlt.le))] at hle
      have hc : ((j - n : ℕ) : ℝ) ≤ D := by
        rw [Nat.cast_sub hlt.le]; exact hle
      exact_mod_cast hc
    · apply hnot; refine mem_union.mpr (Or.inl (mem_filter.mpr ⟨hjI, hgt, ?_⟩))
      rw [abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hgt.le))] at hle
      have hc : ((n - j : ℕ) : ℝ) ≤ D := by
        rw [Nat.cast_sub hgt.le]; exact hle
      exact_mod_cast hc
  have hdisj : Disjoint S_lo S_hi := by
    rw [Finset.disjoint_left]; intro j hj1 hj2
    simp only [S_lo, S_hi, mem_filter] at hj1 hj2; omega
  have hsub : S_lo ∪ S_hi ⊆ Icc 1 N := union_subset (filter_subset _ _) (filter_subset _ _)
  rw [← sum_subset hsub hsupp, sum_union hdisj]
  have hlo : (∑ j ∈ S_lo, collarNearKernel D n j) ≤ (1 / 2 : ℝ) * (harmonic D : ℝ) := by
    have hinj : ∀ j ∈ S_lo, n - j ∈ Icc 1 D := fun j hj => by
      obtain ⟨_, hlt, hle⟩ := mem_filter.mp hj; exact mem_Icc.mpr ⟨by omega, hle⟩
    calc
      (∑ j ∈ S_lo, collarNearKernel D n j) = ∑ j ∈ S_lo, (1 / 2 : ℝ) * (1 / ((n - j : ℕ) : ℝ)) := by
        refine sum_congr rfl fun j hj => ?_
        obtain ⟨_, hlt, hle⟩ := mem_filter.mp hj
        have habs : |(n : ℝ) - j| = ((n - j : ℕ) : ℝ) := by
          rw [abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hlt.le)), Nat.cast_sub hlt.le]
        unfold collarNearKernel
        rw [if_pos ⟨by omega, by rw [habs]; exact_mod_cast hle⟩, habs]; ring
      _ = ∑ h ∈ S_lo.image (fun j => n - j), (1 / 2 : ℝ) * (1 / (h : ℝ)) := by
        rw [sum_image]; intro a ha b' hb hab
        dsimp only at hab
        obtain ⟨_, hal, _⟩ := mem_filter.mp ha; obtain ⟨_, hbl, _⟩ := mem_filter.mp hb
        omega
      _ ≤ ∑ h ∈ Icc 1 D, (1 / 2 : ℝ) * (1 / (h : ℝ)) :=
        sum_le_sum_of_subset_of_nonneg (image_subset_iff.mpr hinj) fun _ _ _ => by positivity
      _ = (1 / 2 : ℝ) * (harmonic D : ℝ) := by
        rw [← mul_sum, harmonic_eq_sum_Icc]
        congr 1; push_cast; exact sum_congr rfl fun h _ => by simp [one_div]
  have hhi : (∑ j ∈ S_hi, collarNearKernel D n j) ≤ (1 / 2 : ℝ) * (harmonic D : ℝ) := by
    have hinj : ∀ j ∈ S_hi, j - n ∈ Icc 1 D := fun j hj => by
      obtain ⟨_, hlt, hle⟩ := mem_filter.mp hj; exact mem_Icc.mpr ⟨by omega, hle⟩
    calc
      (∑ j ∈ S_hi, collarNearKernel D n j) = ∑ j ∈ S_hi, (1 / 2 : ℝ) * (1 / ((j - n : ℕ) : ℝ)) := by
        refine sum_congr rfl fun j hj => ?_
        obtain ⟨_, hlt, hle⟩ := mem_filter.mp hj
        have habs : |(n : ℝ) - j| = ((j - n : ℕ) : ℝ) := by
          rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hlt.le)),
            Nat.cast_sub hlt.le]
        unfold collarNearKernel
        rw [if_pos ⟨by omega, by rw [habs]; exact_mod_cast hle⟩, habs]; ring
      _ = ∑ h ∈ S_hi.image (fun j => j - n), (1 / 2 : ℝ) * (1 / (h : ℝ)) := by
        rw [sum_image]; intro a ha b' hb hab
        dsimp only at hab
        obtain ⟨_, hal, _⟩ := mem_filter.mp ha; obtain ⟨_, hbl, _⟩ := mem_filter.mp hb
        omega
      _ ≤ ∑ h ∈ Icc 1 D, (1 / 2 : ℝ) * (1 / (h : ℝ)) :=
        sum_le_sum_of_subset_of_nonneg (image_subset_iff.mpr hinj) fun _ _ _ => by positivity
      _ = (1 / 2 : ℝ) * (harmonic D : ℝ) := by
        rw [← mul_sum, harmonic_eq_sum_Icc]
        congr 1; push_cast; exact sum_congr rfl fun h _ => by simp [one_div]
  have hHD : (harmonic D : ℝ) ≤ 5 * (1 + Real.log R) := by
    have hh := harmonic_le_one_add_log D
    have hlogD : Real.log (D : ℝ) = 4 * Real.log R := by
      dsimp only [D]; rw [Nat.cast_pow, Real.log_pow]; ring
    have hR0 := Real.log_natCast_nonneg R
    linarith only [hh, hlogD, hR0]
  linarith only [hlo, hhi, hHD]

private theorem collarRowFar_abs_le {R N : ℕ} (hR : 2 ≤ R) (hN1 : 1 ≤ N)
    (hL : 0 < Real.log N) (b : ℕ → ℝ) (hb1 : b 1 = 0) {S : ℝ} (hS0 : 0 ≤ S)
    (hb_sq : (∑ m ∈ Icc 1 R, b m ^ 2) ≤ 2 * S ^ 2) :
    ∀ n ∈ Icc 1 N, |collarRowFar R N b n| ≤
      Real.sqrt n / ((N : ℝ) * Real.sqrt (Real.log N)) * S := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hD0 : 0 < R ^ 4 := pow_pos (by omega : 0 < R) 4
  -- Boundary periods cost R² times the coefficient norm; truncation at R⁴ pays this.
  set B' := 2 * (R : ℝ) ^ 2 * Real.sqrt (∑ m ∈ Icc 1 R, b m ^ 2)
  have hB'0 : 0 ≤ B' := by dsimp only [B']; positivity
  have hg_Ico : ∀ l k : ℕ, l ≤ k →
      |∑ j ∈ Ico l k, ∑ m ∈ Icc 1 R, b m * normalizedRamanujanMode m j| ≤ B' := by
    intro l k hlk
    have hswap : (∑ j ∈ Ico l k, ∑ m ∈ Icc 1 R, b m * normalizedRamanujanMode m j) =
        ∑ m ∈ Icc 1 R, b m * ∑ j ∈ Ico l k, normalizedRamanujanMode m j := by
      rw [sum_comm]
      exact sum_congr rfl fun m _ => (mul_sum ..).symm
    have hm_bound : ∀ m ∈ Icc 1 R,
        |b m * ∑ j ∈ Ico l k, normalizedRamanujanMode m j| ≤ |b m| * (2 * R) := by
      intro m hm
      obtain ⟨hm1, hmR⟩ := mem_Icc.mp hm
      rcases eq_or_lt_of_le hm1 with rfl | hm2
      · simp [hb1]
      · rw [abs_mul]
        have hm0 : 0 < m := by omega
        have hper_le := abs_sum_Ico_le_of_periodic hm0 (normalizedRamanujanMode_periodic hm0)
          (sum_range_normalizedRamanujanMode_eq_zero_of_two_le hm2) l k hlk
        have hL1_m := sum_range_abs_normalizedRamanujanMode_le hm0
        have hmR_cast : (m : ℝ) ≤ R := by exact_mod_cast hmR
        exact mul_le_mul_of_nonneg_left (by linarith only [hper_le, hL1_m, hmR_cast]) (abs_nonneg _)
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Icc 1 R) (fun m => |b m|) (fun _ => (1 : ℝ))
    simp only [mul_one, sq_abs, one_pow, sum_const, Nat.card_Icc, Nat.add_sub_cancel,
      nsmul_eq_mul] at hcs
    have hsum_abs : (∑ m ∈ Icc 1 R, |b m|) ≤
        (R : ℝ) * Real.sqrt (∑ m ∈ Icc 1 R, b m ^ 2) := by
      have hR1 : (1 : ℝ) ≤ R := by exact_mod_cast (show 1 ≤ R by omega)
      have hsq : (∑ m ∈ Icc 1 R, |b m|) ^ 2 ≤
          ((R : ℝ) * Real.sqrt (∑ m ∈ Icc 1 R, b m ^ 2)) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (sum_nonneg fun _ _ => sq_nonneg _)]
        have hRR : (R : ℝ) ≤ (R : ℝ) ^ 2 := by nlinarith only [hR1]
        exact hcs.trans ((mul_comm _ _).trans_le
          (mul_le_mul_of_nonneg_right hRR (sum_nonneg fun _ _ => sq_nonneg _)))
      have hrhs0 : 0 ≤ (R : ℝ) * Real.sqrt (∑ m ∈ Icc 1 R, b m ^ 2) := by positivity
      nlinarith only [hsq, hrhs0]
    rw [hswap]
    calc
      |∑ m ∈ Icc 1 R, b m * ∑ j ∈ Ico l k, normalizedRamanujanMode m j| ≤
          ∑ m ∈ Icc 1 R, |b m| * (2 * R) :=
        (abs_sum_le_sum_abs _ _).trans (sum_le_sum hm_bound)
      _ = (2 * (R : ℝ)) * ∑ m ∈ Icc 1 R, |b m| := by
        rw [mul_sum]; exact sum_congr rfl fun _ _ => by ring
      _ ≤ (2 * (R : ℝ)) * ((R : ℝ) * Real.sqrt (∑ m ∈ Icc 1 R, b m ^ 2)) :=
        mul_le_mul_of_nonneg_left hsum_abs (by positivity)
      _ = B' := by dsimp only [B']; ring
  have h2BD : 2 * B' / ((R ^ 4 : ℕ) : ℝ) ≤ 2 * S := by
    have hR2 : (2 : ℝ) ≤ R := by exact_mod_cast hR
    have hR0 : (0 : ℝ) < R := by positivity
    have hsqrt_le : Real.sqrt (∑ m ∈ Icc 1 R, b m ^ 2) ≤ 2 * S := by
      have h4 : (∑ m ∈ Icc 1 R, b m ^ 2) ≤ (2 * S) ^ 2 := by
        nlinarith only [hb_sq, sq_nonneg S]
      exact (Real.sqrt_le_sqrt h4).trans_eq (Real.sqrt_sq (by positivity))
    have hquot : 2 * B' / ((R ^ 4 : ℕ) : ℝ) =
        (4 / (R : ℝ) ^ 2) * Real.sqrt (∑ m ∈ Icc 1 R, b m ^ 2) := by
      dsimp only [B']
      rw [Nat.cast_pow]
      field_simp [hR0.ne']
      ring
    have hfrac1 : 4 / (R : ℝ) ^ 2 ≤ 1 := by
      rw [div_le_one (sq_pos_of_pos hR0)]; nlinarith only [hR2]
    rw [hquot]
    calc
      (4 / (R : ℝ) ^ 2) * Real.sqrt (∑ m ∈ Icc 1 R, b m ^ 2) ≤ 1 * (2 * S) :=
        mul_le_mul hfrac1 hsqrt_le (Real.sqrt_nonneg _) zero_le_one
      _ = 2 * S := one_mul _
  intro n hn
  unfold collarRowFar
  rw [abs_mul, abs_of_nonneg (by positivity)]
  calc
    _ ≤ (Real.sqrt n / (2 * (N : ℝ) * Real.sqrt (Real.log N))) * (2 * S) :=
      mul_le_mul_of_nonneg_left
        ((abs_sum_far_erase_div_abs_sub_le hn hD0 hB'0 hg_Ico).trans h2BD) (by positivity)
    _ = _ := by ring

/-- Weighted Schur applied to `|a|+|b|` controls a bilinear collar pairing. -/
private theorem sum_abs_pair_le_of_weighted_rows (S : Finset ℕ)
    (K : ℕ → ℕ → ℝ) (w a b : ℕ → ℝ) {H : ℝ} (hH : 0 ≤ H)
    (hw : ∀ n ∈ S, 0 < w n) (hK0 : ∀ n ∈ S, ∀ j ∈ S, 0 ≤ K n j)
    (hKsym : ∀ n j, K n j = K j n)
    (hrow : ∀ n ∈ S, ∑ j ∈ S, K n j * w j ≤ H * w n) :
    (∑ n ∈ S, ∑ j ∈ S, |a n| * |b j| * K n j) ≤
      2 * H * ((∑ n ∈ S, a n ^ 2) + ∑ n ∈ S, b n ^ 2) := by
  let z := fun n => |a n| + |b n|
  have hz0 : ∀ n, 0 ≤ z n := fun n => add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hschur := weighted_double_sum_le_weightedRowBound
    (ι := ↥S) (b := fun n : ↥S => z n) (w := fun n : ↥S => w n)
    (H := H) (K := fun n j : ↥S => K n j)
    (fun n => hw n n.property) (fun n j => hKsym n j)
    (fun n j => hK0 n n.property j j.property) (fun n => by
      rw [sum_coe_sort S (fun j : ℕ => K (n : ℕ) j * w j)]
      exact hrow n n.property)
  have hschur' : (∑ n ∈ S, ∑ j ∈ S, z n * z j * K n j) ≤
      H * ∑ n ∈ S, z n ^ 2 := by
    have hdouble : (∑ n : ↥S, ∑ j : ↥S, |z (n : ℕ)| * |z (j : ℕ)| * K n j) =
        ∑ n ∈ S, ∑ j ∈ S, |z n| * |z j| * K n j := by
      rw [sum_coe_sort S (fun n : ℕ => ∑ j : ↥S, |z n| * |z (j : ℕ)| * K n j)]
      exact sum_congr rfl fun n _ => sum_coe_sort S (fun j : ℕ => |z n| * |z j| * K n j)
    rw [hdouble, sum_coe_sort S (fun n : ℕ => z n ^ 2)] at hschur
    simpa only [abs_of_nonneg (hz0 _)] using hschur
  have hzsq : (∑ n ∈ S, z n ^ 2) ≤
      2 * ((∑ n ∈ S, a n ^ 2) + ∑ n ∈ S, b n ^ 2) := by
    rw [mul_add, mul_sum, mul_sum, ← sum_add_distrib]
    apply sum_le_sum
    intro n _
    dsimp only [z]
    nlinarith only [sq_nonneg (|a n| - |b n|), sq_abs (a n), sq_abs (b n)]
  calc
    _ ≤ ∑ n ∈ S, ∑ j ∈ S, z n * z j * K n j := by
      apply sum_le_sum
      intro n hn
      apply sum_le_sum
      intro j hj
      apply mul_le_mul_of_nonneg_right _ (hK0 n hn j hj)
      exact mul_le_mul (le_add_of_nonneg_right (abs_nonneg _))
        (le_add_of_nonneg_left (abs_nonneg _)) (abs_nonneg _) (hz0 n)
    _ ≤ H * ∑ n ∈ S, z n ^ 2 := hschur'
    _ ≤ H * (2 * ((∑ n ∈ S, a n ^ 2) + ∑ n ∈ S, b n ^ 2)) :=
      mul_le_mul_of_nonneg_left hzsq hH
    _ = _ := by ring

private theorem sum_abs_hilbert_pair_le (S : Finset ℕ) (a b : ℕ → ℝ) :
    (∑ n ∈ S, ∑ j ∈ S,
      |a n| * |b j| * (1 / ((n : ℝ) + j + 1))) ≤
      2 * Real.pi * ((∑ n ∈ S, a n ^ 2) + ∑ n ∈ S, b n ^ 2) := by
  apply sum_abs_pair_le_of_weighted_rows S
    (fun n j => 1 / ((n : ℝ) + j + 1))
    (fun n => (Real.sqrt ((n : ℝ) + 1 / 2))⁻¹) a b Real.pi_pos.le
  · intro n _
    exact inv_pos.mpr (Real.sqrt_pos.mpr (by positivity))
  · intro n _ j _
    positivity
  · intro n j
    rw [add_comm (n : ℝ) (j : ℝ)]
  · intro n _
    have h := hilbert_weighted_row_bound n S
    simpa only [Nat.cast_add, Nat.cast_one, one_div, div_eq_mul_inv, mul_inv_rev, one_mul, mul_comm] using h

private theorem sum_sqrt_mul_abs_packet_le {R N : ℕ} (hR : 2 ≤ R)
    (hRN4 : R ^ 4 ≤ N) (hlog : 18 * (1 + Real.log R) ≤ Real.log N)
    {u : EuclideanSpace ℝ (PrimeHorizonIndex N)} (hu : u ∈ conductorSubspace R N) :
    (∑ n ∈ Icc 1 N, Real.sqrt n / N * |primeHorizonExtension u n|) ≤
      2 / Real.sqrt (Real.log N) * ‖u‖ := by
  have hN1 : 1 ≤ N := (pow_pos (by omega : 0 < R) 4).trans_le hRN4
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hL0 : 0 < Real.log N := by
    have hR0 := Real.log_natCast_nonneg R
    linarith only [hlog, hR0]
  have hlin := sum_linear_moment_sq_le_four_div_log hR hRN4 hlog hu
  have hlin' : (∑ n ∈ Icc 1 N, ((n : ℝ) / N) * primeHorizonExtension u n ^ 2) ≤
      4 / Real.log N * ‖u‖ ^ 2 := by
    rw [div_mul_eq_mul_div]
    exact (le_div_iff₀' hL0).mpr hlin
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Icc 1 N)
    (fun _ => (1 : ℝ)) (fun n => Real.sqrt n / N * |primeHorizonExtension u n|)
  simp only [one_mul, one_pow, sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul,
    mul_one] at hcs
  have heq : (N : ℝ) *
      (∑ n ∈ Icc 1 N, (Real.sqrt n / N * |primeHorizonExtension u n|) ^ 2) =
      ∑ n ∈ Icc 1 N, ((n : ℝ) / N) * primeHorizonExtension u n ^ 2 := by
    rw [mul_sum]
    apply sum_congr rfl
    intro n _
    rw [mul_pow, div_pow, Real.sq_sqrt (Nat.cast_nonneg n), sq_abs]
    field_simp [hN0.ne']
  have hsq : (∑ n ∈ Icc 1 N, Real.sqrt n / N * |primeHorizonExtension u n|) ^ 2 ≤
      (2 / Real.sqrt (Real.log N) * ‖u‖) ^ 2 := by
    rw [mul_pow, div_pow, Real.sq_sqrt hL0.le]
    rw [heq] at hcs
    have hh : (4 : ℝ) / Real.log N * ‖u‖ ^ 2 =
        (2 : ℝ) ^ 2 / Real.log N * ‖u‖ ^ 2 := by norm_num
    exact hcs.trans (hlin'.trans_eq hh)
  have hright0 : 0 ≤ 2 / Real.sqrt (Real.log N) * ‖u‖ := by positivity
  have hleft0 : 0 ≤ ∑ n ∈ Icc 1 N, Real.sqrt n / N * |primeHorizonExtension u n| :=
    sum_nonneg fun n _ => mul_nonneg (div_nonneg (Real.sqrt_nonneg (n : ℝ)) hN0.le)
      (abs_nonneg (primeHorizonExtension u n))
  nlinarith only [hsq, hright0, hleft0]

private theorem collar_half_pair_le {R N : ℕ} (hN1 : 1 ≤ N)
    (b x : ℕ → ℝ) :
    |∑ n ∈ Icc 1 N, x n * collarRowSumHalf R N b n| ≤
      2 * Real.pi * ((∑ n ∈ Icc 1 N, ((n : ℝ) / N) * x n ^ 2) +
        ∑ n ∈ Icc 1 N, ((n : ℝ) / N) *
          primeHorizonExtension (∑ m ∈ Icc 1 R,
            b m • normalizedRamanujanHorizonVector m N) n ^ 2) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  let v := primeHorizonExtension (∑ m ∈ Icc 1 R, b m • normalizedRamanujanHorizonVector m N)
  let X := fun n : ℕ => Real.sqrt ((n : ℝ) / N) * x n
  let Y := fun n : ℕ => Real.sqrt ((n : ℝ) / N) * v n
  have hpt : ∀ n ∈ Icc 1 N, ∀ j ∈ Icc 1 N,
      |x n * (Real.sqrt n * Real.sqrt j / (2 * (N : ℝ) * ((n : ℝ) + j)) * v j)| ≤
      |X n| * |Y j| * (1 / ((n : ℝ) + j + 1)) := by
    intro n hn j hj
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (mem_Icc.mp hn).1
    have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast (mem_Icc.mp hj).1
    have hsum0 : 0 < (n : ℝ) + j := by linarith only [hn1, hj1]
    have hid : x n * (Real.sqrt n * Real.sqrt j /
        (2 * (N : ℝ) * ((n : ℝ) + j)) * v j) =
        X n * Y j * (1 / (2 * ((n : ℝ) + j))) := by
      dsimp only [X, Y]
      rw [Real.sqrt_div (Nat.cast_nonneg n), Real.sqrt_div (Nat.cast_nonneg j)]
      field_simp [hN0.ne', (Real.sqrt_pos.mpr hN0).ne', hsum0.ne']
      rw [Real.sq_sqrt hN0.le]
      ring
    rw [hid, abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 1 / (2 * ((n : ℝ) + j)))]
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    exact one_div_le_one_div_of_le (by positivity) (by linarith only [hn1, hj1])
  have hbound : |∑ n ∈ Icc 1 N, x n * collarRowSumHalf R N b n| ≤
      ∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N, |X n| * |Y j| * (1 / ((n : ℝ) + j + 1)) := by
    apply (abs_sum_le_sum_abs _ _).trans
    apply sum_le_sum
    intro n hn
    unfold collarRowSumHalf
    rw [mul_sum]
    refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum fun j hj => ?_).trans
      (sum_le_sum_of_subset_of_nonneg (erase_subset n (Icc 1 N)) fun _ _ _ => by positivity))
    exact hpt n hn j (mem_erase.mp hj).2
  have hs := hbound.trans (sum_abs_hilbert_pair_le (Icc 1 N) X Y)
  have hx : ∀ n, X n ^ 2 = ((n : ℝ) / N) * x n ^ 2 := by
    intro n; dsimp only [X]; rw [mul_pow, Real.sq_sqrt (by positivity)]
  have hy : ∀ n, Y n ^ 2 = ((n : ℝ) / N) * v n ^ 2 := by
    intro n; dsimp only [Y]; rw [mul_pow, Real.sq_sqrt (by positivity)]
  simpa only [hx, hy] using hs

private theorem collar_near_pair_le {R N : ℕ} (b x : ℕ → ℝ) :
    |∑ n ∈ Icc 1 N, x n * collarRowNear R N b n| ≤
      10 * (1 + Real.log R) * ((∑ n ∈ Icc 1 N, ((n : ℝ) / N) * x n ^ 2) +
        ∑ n ∈ Icc 1 N, ((n : ℝ) / N) *
          primeHorizonExtension (∑ m ∈ Icc 1 R,
            b m • normalizedRamanujanHorizonVector m N) n ^ 2) := by
  let v := primeHorizonExtension (∑ m ∈ Icc 1 R, b m • normalizedRamanujanHorizonVector m N)
  let X := fun n : ℕ => Real.sqrt ((n : ℝ) / N) * x n
  let Y := fun n : ℕ => Real.sqrt ((n : ℝ) / N) * v n
  have hK0 : ∀ n j, 0 ≤ collarNearKernel (R ^ 4) n j := by
    intro n j; unfold collarNearKernel; split_ifs <;> positivity
  have hKsym : ∀ n j, collarNearKernel (R ^ 4) n j = collarNearKernel (R ^ 4) j n := by
    intro n j
    unfold collarNearKernel
    split_ifs with hnj hjn hjn
    · rw [abs_sub_comm]
    · exact False.elim (hjn ⟨hnj.1.symm, by simpa only [abs_sub_comm] using hnj.2⟩)
    · exact False.elim (hnj ⟨hjn.1.symm, by simpa only [abs_sub_comm] using hjn.2⟩)
    · rfl
  have hrows := sum_abs_pair_le_of_weighted_rows (Icc 1 N) (collarNearKernel (R ^ 4))
    (fun _ => 1) X Y (show 0 ≤ 5 * (1 + Real.log R) by positivity)
    (fun _ _ => zero_lt_one) (fun n _ j _ => hK0 n j) hKsym
    (fun n hn => by simpa only [mul_one] using collarNearKernel_row_le R N n hn)
  have hbound : |∑ n ∈ Icc 1 N, x n * collarRowNear R N b n| ≤
      ∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N, |X n| * |Y j| * collarNearKernel (R ^ 4) n j := by
    apply (abs_sum_le_sum_abs _ _).trans
    apply sum_le_sum
    intro n _
    unfold collarRowNear
    rw [mul_sum, mul_sum]
    apply (abs_sum_le_sum_abs _ _).trans
    apply sum_le_sum
    intro j _
    have hid : x n * (Real.sqrt ((n : ℝ) / N) *
        (collarNearKernel (R ^ 4) n j * (Real.sqrt ((j : ℝ) / N) * v j))) =
        X n * Y j * collarNearKernel (R ^ 4) n j := by dsimp only [X, Y]; ring
    rw [hid, abs_mul, abs_mul, abs_of_nonneg (hK0 n j)]
  have hx : ∀ n, X n ^ 2 = ((n : ℝ) / N) * x n ^ 2 := by
    intro n; dsimp only [X]; rw [mul_pow, Real.sq_sqrt (by positivity)]
  have hy : ∀ n, Y n ^ 2 = ((n : ℝ) / N) * v n ^ 2 := by
    intro n; dsimp only [Y]; rw [mul_pow, Real.sq_sqrt (by positivity)]
  simpa only [hx, hy, show (2 : ℝ) * (5 * (1 + Real.log R)) =
    10 * (1 + Real.log R) by ring] using hbound.trans hrows

private theorem collar_v1_inner_le {R N : ℕ} (hR : 2 ≤ R) (hRN4 : R ^ 4 ≤ N)
    (hlog : 18 * (1 + Real.log R) ≤ Real.log N)
    {u : EuclideanSpace ℝ (PrimeHorizonIndex N)} (hu : u ∈ conductorSubspace R N) :
    |⟪Matrix.toEuclideanLin (horizonKernelMatrix (collarKernel N) N)
      (normalizedRamanujanHorizonVector 1 N), u⟫| ≤ 6 * ‖u‖ := by
  have hN1 : 1 ≤ N := (pow_pos (by omega : 0 < R) 4).trans_le hRN4
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hL1 : 1 ≤ Real.log N := by
    have hR0 := Real.log_natCast_nonneg R; linarith only [hlog, hR0]
  have hL0 := zero_lt_one.trans_le hL1
  have hsL0 := Real.sqrt_pos.mpr hL0
  rw [horizonKernelMatrix_bilinear]
  have hid : (∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N,
      primeHorizonExtension u n * primeHorizonExtension (normalizedRamanujanHorizonVector 1 N) j *
        collarKernel N n j) =
      ∑ n ∈ Icc 1 N, primeHorizonExtension u n *
        ∑ j ∈ Icc 1 N, collarKernel N n j *
          primeHorizonExtension (normalizedRamanujanHorizonVector 1 N) j := by
    apply sum_congr rfl
    intro n _
    rw [mul_sum]
    exact sum_congr rfl fun j _ => by ring
  rw [hid]
  have hrow0 : ∀ n, 0 ≤ ∑ j ∈ Icc 1 N, collarKernel N n j *
      primeHorizonExtension (normalizedRamanujanHorizonVector 1 N) j := by
    intro n
    apply sum_nonneg
    intro j hj
    rw [primeHorizonExtension_coe _ ⟨j, hj⟩]
    change 0 ≤ (1 / (N : ℝ)) * archimedeanCenterKernel n j *
      ((Real.sqrt (Real.log N))⁻¹ * (normalizedRamanujanMode 1 j / Real.sqrt j))
    rw [normalizedRamanujanMode, ramanujanMode_one, Nat.totient_one, Nat.cast_one,
      Real.sqrt_one, div_one]
    have hh := archimedeanCenterKernel_nonneg n j
    positivity
  calc
    _ ≤ ∑ n ∈ Icc 1 N, |primeHorizonExtension u n| *
        (3 * Real.sqrt (Real.log N) * Real.sqrt n / N) := by
      apply (abs_sum_le_sum_abs _ _).trans
      apply sum_le_sum
      intro n hn
      rw [abs_mul, abs_of_nonneg (hrow0 n)]
      exact mul_le_mul_of_nonneg_left (collar_v1_row_le hN1 hL1 hn) (abs_nonneg _)
    _ = 3 * Real.sqrt (Real.log N) *
        ∑ n ∈ Icc 1 N, Real.sqrt n / N * |primeHorizonExtension u n| := by
      rw [mul_sum]
      exact sum_congr rfl fun n _ => by ring
    _ ≤ 3 * Real.sqrt (Real.log N) * (2 / Real.sqrt (Real.log N) * ‖u‖) :=
      mul_le_mul_of_nonneg_left (sum_sqrt_mul_abs_packet_le hR hRN4 hlog hu) (by positivity)
    _ = _ := by
      field_simp [hsL0.ne']
      ring

/-- Testing both collar arguments against their linear moment gives full logarithmic decay. -/
theorem abs_fullWeilCenterMatrix_self_inner_le_of_mem_conductorSubspace (α : ℝ)
    {R N : ℕ} (hR : 2 ≤ R) (hRN4 : R ^ 4 ≤ N)
    (hlog : 18 * (1 + Real.log R) ≤ Real.log N)
    {u : EuclideanSpace ℝ (PrimeHorizonIndex N)}
    (hu : u ∈ conductorSubspace R N) (hu1 : u ∈ (conductorSubspace 1 N)ᗮ) :
    |⟪Matrix.toEuclideanLin (fullWeilCenterMatrix α N) u, u⟫| ≤
      600 * |α| * (1 + Real.log R) / Real.log N * ‖u‖ ^ 2 := by
  have hRN2 : R * R ≤ N := by
    have hh := (Nat.pow_le_pow_right (by omega : 0 < R) (by norm_num : 2 ≤ 4)).trans hRN4
    simpa only [sq] using hh
  have hN2 : 2 ≤ N := by have hh := Nat.mul_le_mul hR hR; omega
  have hN1 : 1 ≤ N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hL1 : 1 ≤ Real.log N := by
    have hR0 := Real.log_natCast_nonneg R; linarith only [hlog, hR0]
  have hL : 0 < Real.log N := zero_lt_one.trans_le hL1
  have hsL := Real.sqrt_pos.mpr hL
  have hH1 : 1 ≤ 1 + Real.log R := by have hh := Real.log_natCast_nonneg R; linarith only [hh]
  have hinner_eq : ⟪Matrix.toEuclideanLin (fullWeilCenterMatrix α N) u, u⟫ =
      -α * ⟪Matrix.toEuclideanLin (horizonKernelMatrix (collarKernel N) N) u, u⟫ := by
    change ⟪Matrix.toEuclideanLin
      (horizonKernelMatrix (fun n j =>
        (α / N) * (arithmeticPoleKernel n j - archimedeanCenterKernel n j)) N) u, u⟫ = _
    rw [horizonKernelMatrix_bilinear, horizonKernelMatrix_bilinear]
    have hterm (n j : ℕ) :
        primeHorizonExtension u n * primeHorizonExtension u j *
            ((α / N) * (arithmeticPoleKernel n j - archimedeanCenterKernel n j)) =
          (α / N) * (primeHorizonExtension u n * primeHorizonExtension u j *
            arithmeticPoleKernel n j) -
          α * (primeHorizonExtension u n * primeHorizonExtension u j * collarKernel N n j) := by
      unfold collarKernel; ring
    simp only [hterm, sum_sub_distrib, ← mul_sum]
    rw [arithmeticPoleKernel_bilinear_eq_zero
      (harmonicSum_eq_zero_of_mem_orthog_one hN2 hu1)
      (harmonicSum_eq_zero_of_mem_orthog_one hN2 hu1)]
    ring
  obtain ⟨a, -, hu_eq⟩ := (mem_conductorSubspace_iff (M := R) (N := N) (x := u)).mp hu
  -- Remove the constant mode; every remaining mode has zero period mean.
  set aTilde : ℕ → ℝ := fun m => if m = 1 then 0 else a m
  set uTilde := ∑ m ∈ Icc 1 R, aTilde m • normalizedRamanujanHorizonVector m N
  have hu_split : u = a 1 • normalizedRamanujanHorizonVector 1 N + uTilde := by
    rw [hu_eq]
    have h1mem : (1 : ℕ) ∈ Icc 1 R := mem_Icc.mpr ⟨le_rfl, by omega⟩
    rw [← add_sum_erase _ _ h1mem]
    congr 1
    dsimp only [uTilde]
    rw [← add_sum_erase _ _ h1mem]
    have hz : aTilde 1 • normalizedRamanujanHorizonVector 1 N = 0 := by simp [aTilde]
    rw [hz, zero_add]
    refine sum_congr rfl fun m hm => ?_
    have hm1 : m ≠ 1 := (mem_erase.mp hm).1
    simp [aTilde, hm1]
  have ha1_le : |a 1| ≤ 36 * (1 + Real.log R) / Real.log N * ‖u‖ := by
    have hlow := (low_band_norm_le_of_mem_orthogonal (by omega : 1 ≤ 1) (by omega : 1 ≤ R)
      hR hRN2 hlog (hu_eq ▸ hu1)).1
    rw [← hu_eq] at hlow
    have h1sq : Real.sqrt (∑ m ∈ Icc 1 1, a m ^ 2) = |a 1| := by
      rw [Icc_self, sum_singleton, Real.sqrt_sq_eq_abs]
    rwa [h1sq] at hlow
  have ha_sq : (∑ m ∈ Icc 1 R, aTilde m ^ 2) ≤ 2 * ‖u‖ ^ 2 := by
    have hle : (∑ m ∈ Icc 1 R, aTilde m ^ 2) ≤ ∑ m ∈ Icc 1 R, a m ^ 2 :=
      sum_le_sum fun m _ => by dsimp only [aTilde]; split_ifs <;> simp [sq_nonneg]
    have hr := (half_and_three_halves_riesz_of_log_le hR hRN2 hlog a).1
    rw [← hu_eq] at hr
    linarith only [hle, hr]
  have huTilde_mem : uTilde ∈ conductorSubspace R N :=
    sum_normalizedRamanujanHorizonVector_mem_conductorSubspace R N aTilde
  have huTilde_norm : ‖uTilde‖ ≤ 2 * ‖u‖ := by
    have hr := (half_and_three_halves_riesz_of_log_le hR hRN2 hlog aTilde).2
    have hsq : ‖uTilde‖ ^ 2 ≤ (2 * ‖u‖) ^ 2 := by
      calc
        ‖uTilde‖ ^ 2 ≤ (3 / 2 : ℝ) * ∑ m ∈ Icc 1 R, aTilde m ^ 2 := hr
        _ ≤ (3 / 2 : ℝ) * (2 * ‖u‖ ^ 2) := mul_le_mul_of_nonneg_left ha_sq (by norm_num)
        _ ≤ (2 * ‖u‖) ^ 2 := by nlinarith only [sq_nonneg ‖u‖]
    nlinarith only [hsq, norm_nonneg uTilde, norm_nonneg u]
  have hlin_uTilde : (∑ j ∈ Icc 1 N, ((j : ℝ) / N) * primeHorizonExtension uTilde j ^ 2) ≤
      16 / Real.log N * ‖u‖ ^ 2 := by
    have hm := sum_linear_moment_sq_le_four_div_log hR hRN4 hlog huTilde_mem
    have h4 : ‖uTilde‖ ^ 2 ≤ 4 * ‖u‖ ^ 2 := by
      nlinarith only [huTilde_norm, norm_nonneg uTilde, norm_nonneg u]
    rw [div_mul_eq_mul_div, le_div_iff₀' hL]
    linarith only [hm, h4]
  have hlin_u : (∑ n ∈ Icc 1 N, ((n : ℝ) / N) * primeHorizonExtension u n ^ 2) ≤
      4 / Real.log N * ‖u‖ ^ 2 := by
    rw [div_mul_eq_mul_div]
    exact (le_div_iff₀' hL).mpr (sum_linear_moment_sq_le_four_div_log hR hRN4 hlog hu)
  have hhalf : |∑ n ∈ Icc 1 N, primeHorizonExtension u n * collarRowSumHalf R N aTilde n| ≤
      (40 * Real.pi) / Real.log N * ‖u‖ ^ 2 := by
    calc
      _ ≤ 2 * Real.pi * ((∑ n ∈ Icc 1 N, ((n : ℝ) / N) * primeHorizonExtension u n ^ 2) +
          ∑ n ∈ Icc 1 N, ((n : ℝ) / N) * primeHorizonExtension uTilde n ^ 2) :=
        collar_half_pair_le hN1 aTilde (primeHorizonExtension u)
      _ ≤ 2 * Real.pi * (4 / Real.log N * ‖u‖ ^ 2 + 16 / Real.log N * ‖u‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (add_le_add hlin_u hlin_uTilde) (by positivity)
      _ = _ := by ring
  have hnear : |∑ n ∈ Icc 1 N, primeHorizonExtension u n * collarRowNear R N aTilde n| ≤
      (200 * (1 + Real.log R)) / Real.log N * ‖u‖ ^ 2 := by
    calc
      _ ≤ 10 * (1 + Real.log R) *
          ((∑ n ∈ Icc 1 N, ((n : ℝ) / N) * primeHorizonExtension u n ^ 2) +
          ∑ n ∈ Icc 1 N, ((n : ℝ) / N) * primeHorizonExtension uTilde n ^ 2) :=
        collar_near_pair_le aTilde (primeHorizonExtension u)
      _ ≤ 10 * (1 + Real.log R) *
          (4 / Real.log N * ‖u‖ ^ 2 + 16 / Real.log N * ‖u‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (add_le_add hlin_u hlin_uTilde) (by positivity)
      _ = _ := by ring
  have hfar : |∑ n ∈ Icc 1 N, primeHorizonExtension u n * collarRowFar R N aTilde n| ≤
      2 / Real.log N * ‖u‖ ^ 2 := by
    have hrow := collarRowFar_abs_le hR hN1 hL aTilde (by simp [aTilde]) (norm_nonneg u) ha_sq
    calc
      _ ≤ ∑ n ∈ Icc 1 N, |primeHorizonExtension u n| *
          (Real.sqrt n / ((N : ℝ) * Real.sqrt (Real.log N)) * ‖u‖) := by
        apply (abs_sum_le_sum_abs _ _).trans
        apply sum_le_sum
        intro n hn
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hrow n hn) (abs_nonneg _)
      _ = (‖u‖ / Real.sqrt (Real.log N)) *
          ∑ n ∈ Icc 1 N, Real.sqrt n / N * |primeHorizonExtension u n| := by
        rw [mul_sum]
        exact sum_congr rfl fun n _ => by ring
      _ ≤ (‖u‖ / Real.sqrt (Real.log N)) * (2 / Real.sqrt (Real.log N) * ‖u‖) :=
        mul_le_mul_of_nonneg_left (sum_sqrt_mul_abs_packet_le hR hRN4 hlog hu) (by positivity)
      _ = _ := by field_simp [hL.ne', hsL.ne']; rw [Real.sq_sqrt hL.le]
  have htilde : |⟪Matrix.toEuclideanLin (horizonKernelMatrix (collarKernel N) N) uTilde, u⟫| ≤
      (40 * Real.pi + 200 * (1 + Real.log R) + 2) / Real.log N * ‖u‖ ^ 2 := by
    have hid : ⟪Matrix.toEuclideanLin (horizonKernelMatrix (collarKernel N) N) uTilde, u⟫ =
        (∑ n ∈ Icc 1 N, primeHorizonExtension u n * collarRowSumHalf R N aTilde n) +
        (∑ n ∈ Icc 1 N, primeHorizonExtension u n * collarRowNear R N aTilde n) +
        (∑ n ∈ Icc 1 N, primeHorizonExtension u n * collarRowFar R N aTilde n) := by
      rw [horizonKernelMatrix_bilinear, ← sum_add_distrib, ← sum_add_distrib]
      apply sum_congr rfl
      intro n hn
      have heq : (∑ j ∈ Icc 1 N, primeHorizonExtension u n *
          primeHorizonExtension uTilde j * collarKernel N n j) =
          primeHorizonExtension u n * ∑ j ∈ Icc 1 N,
            collarKernel N n j * primeHorizonExtension uTilde j := by
        rw [mul_sum]; exact sum_congr rfl fun j _ => by ring
      rw [heq, collarRow_eq_sum_three hR hN1 hL aTilde hn]
      ring
    rw [hid]
    calc
      _ ≤ |∑ n ∈ Icc 1 N, primeHorizonExtension u n * collarRowSumHalf R N aTilde n| +
          |∑ n ∈ Icc 1 N, primeHorizonExtension u n * collarRowNear R N aTilde n| +
          |∑ n ∈ Icc 1 N, primeHorizonExtension u n * collarRowFar R N aTilde n| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ _ := by
        simp only [div_eq_mul_inv] at hhalf hnear hfar ⊢
        linarith only [hhalf, hnear, hfar]
  have hcol : |⟪Matrix.toEuclideanLin (horizonKernelMatrix (collarKernel N) N) u, u⟫| ≤
      600 * (1 + Real.log R) / Real.log N * ‖u‖ ^ 2 := by
    have hmap := congrArg (Matrix.toEuclideanLin (horizonKernelMatrix (collarKernel N) N)) hu_split
    rw [map_add, map_smul] at hmap
    rw [hmap, inner_add_left, real_inner_smul_left]
    have hcoef : 216 * (1 + Real.log R) + (40 * Real.pi + 200 * (1 + Real.log R) + 2) ≤
        600 * (1 + Real.log R) := by linarith only [Real.pi_lt_four, hH1]
    calc
      _ ≤ |a 1| * |⟪Matrix.toEuclideanLin (horizonKernelMatrix (collarKernel N) N)
          (normalizedRamanujanHorizonVector 1 N), u⟫| +
          |⟪Matrix.toEuclideanLin (horizonKernelMatrix (collarKernel N) N) uTilde, u⟫| := by
        simpa only [abs_mul] using abs_add_le
          (a 1 * ⟪Matrix.toEuclideanLin (horizonKernelMatrix (collarKernel N) N)
            (normalizedRamanujanHorizonVector 1 N), u⟫)
          ⟪Matrix.toEuclideanLin (horizonKernelMatrix (collarKernel N) N) uTilde, u⟫
      _ ≤ (36 * (1 + Real.log R) / Real.log N * ‖u‖) * (6 * ‖u‖) +
          (40 * Real.pi + 200 * (1 + Real.log R) + 2) / Real.log N * ‖u‖ ^ 2 :=
        add_le_add (mul_le_mul ha1_le (collar_v1_inner_le hR hRN4 hlog hu)
          (abs_nonneg _) (by positivity)) htilde
      _ = (216 * (1 + Real.log R) + (40 * Real.pi + 200 * (1 + Real.log R) + 2)) /
          Real.log N * ‖u‖ ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hcoef hL.le) (sq_nonneg _)
  rw [hinner_eq, abs_mul, abs_neg]
  calc
    _ ≤ |α| * (600 * (1 + Real.log R) / Real.log N * ‖u‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hcol (abs_nonneg _)
    _ = _ := by ring

end GaloisForLFunctions.CompletedArithmeticForms

#print axioms GaloisForLFunctions.CompletedArithmeticForms.abs_fullWeilCenterMatrix_self_inner_le_of_mem_conductorSubspace
