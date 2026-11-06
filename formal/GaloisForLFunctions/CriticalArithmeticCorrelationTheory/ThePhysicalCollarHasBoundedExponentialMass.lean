import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheOverlapGramHasBoundedRows
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.AtomicSynthesisRecoversLipschitzTests
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheTopCollarHasADyadicSeventhPowerReserve

/-!
# Local overlap controls the weighted physical collar

At the atom centered at `log n`, the overlap count is proportional to `n`.
Keeping this local count allows an exponential conjugation to recover the
seventh-power coefficient weight in the eighth-power physical mass.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Finset Filter Topology
namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open SpacingScaleHarmonicAnalysis ArithmeticElectrostatics ArithmeticHodgeTheoryOfDegenerations
  RenormalizedArithmeticPotentialTheory

private theorem log_window_row_le {w : ℝ} (hw : 0 ≤ w) {N m : ℕ}
    (hm : m ∈ Icc 1 N) :
    (∑ n ∈ Icc 1 N, if |Real.log n - Real.log m| ≤ w then (1 : ℝ) else 0) ≤
      1 + 2 * m * (Real.exp w - 1) := by
  let S := (Icc 1 N).filter (fun n : ℕ => |Real.log n - Real.log m| ≤ w)
  let T := (Icc 1 N).filter
    (fun n => n ≠ m ∧ |(n : ℝ) - m| ≤ m * (Real.exp w - 1))
  have he : 0 ≤ Real.exp w - 1 := by linarith only [Real.add_one_le_exp w, hw]
  have hsub : S ⊆ insert m T := by
    intro n hn
    obtain ⟨hnN, hlog⟩ := mem_filter.mp hn
    by_cases hnm : n = m
    · exact mem_insert.mpr (Or.inl hnm)
    · refine mem_insert.mpr (Or.inr (mem_filter.mpr ⟨hnN, hnm, ?_⟩))
      exact abs_sub_le_of_abs_log_le
        (by exact_mod_cast (mem_Icc.mp hnN).1)
        (by exact_mod_cast (mem_Icc.mp hm).1) hlog
  have hcard : (S.card : ℝ) ≤ 1 + 2 * m * (Real.exp w - 1) := by
    have hnear := card_near_le (Icc 1 N) m (show 0 ≤ (m : ℝ) * (Real.exp w - 1) by positivity)
    have hsubR : (S.card : ℝ) ≤ (insert m T).card := by exact_mod_cast card_le_card hsub
    have hinsR : ((insert m T).card : ℝ) ≤ (T.card : ℝ) + 1 := by
      exact_mod_cast card_insert_le m T
    change (T.card : ℝ) ≤ 2 * ((m : ℝ) * (Real.exp w - 1)) at hnear
    linarith only [hsubR, hinsR, hnear]
  simpa only [S, ← sum_filter, sum_const, nsmul_eq_mul, mul_one] using hcard

/-- The Gram bound keeps the local overlap at each atom instead of the largest horizon overlap. -/
theorem integral_atomicTest_sq_le_local_overlap {g : ℝ → ℝ} {w : ℝ}
    (hg : Continuous g) (hgc : HasCompactSupport g)
    (hsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) (hw : 0 ≤ w)
    (N : ℕ) (x : ℕ → ℝ) :
    (∫ u, atomicTest N x g u ^ 2) ≤
      (∫ u, g u ^ 2) * ∑ n ∈ Icc 1 N, x n ^ 2 * (1 + 2 * n * (Real.exp w - 1)) := by
  let G := ∫ u, g u ^ 2
  let B : ℕ → ℕ → ℝ := fun m n => if |Real.log n - Real.log m| ≤ w then 1 else 0
  have hG : 0 ≤ G := integral_nonneg fun u => sq_nonneg _
  have hB : ∀ m n, 0 ≤ B m n := fun m n => by dsimp only [B]; split_ifs <;> norm_num
  have hBs : ∀ m n, B n m = B m n := fun m n => by simp only [B, abs_sub_comm]
  have hc : ∀ m n : ℕ, |bumpCorr g (-(Real.log n - Real.log m))| ≤ G * B m n := by
    intro m n
    dsimp only [B]
    by_cases h : |Real.log n - Real.log m| ≤ w
    · rw [if_pos h, mul_one]
      exact abs_bumpCorr_le hg hgc _
    · rw [if_neg h, mul_zero, bumpCorr_eq_zero hsupp (by simpa only [abs_neg] using not_le.mp h), abs_zero]
  have hpoint : ∀ m n, x m * x n * bumpCorr g (-(Real.log n - Real.log m)) ≤
      (G / 2) * (x m ^ 2 * B m n + x n ^ 2 * B m n) := by
    intro m n
    have hx : |x m * x n| ≤ (x m ^ 2 + x n ^ 2) / 2 := by
      rw [abs_mul]
      nlinarith only [sq_nonneg (|x m| - |x n|), sq_abs (x m), sq_abs (x n)]
    calc
      _ ≤ |x m * x n * bumpCorr g (-(Real.log n - Real.log m))| := le_abs_self _
      _ = |x m * x n| * |bumpCorr g (-(Real.log n - Real.log m))| := abs_mul _ _
      _ ≤ ((x m ^ 2 + x n ^ 2) / 2) * (G * B m n) :=
        mul_le_mul hx (hc m n) (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have hswap : (∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, x n ^ 2 * B m n) =
      ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, x m ^ 2 * B m n := by
    rw [sum_comm]
    exact sum_congr rfl fun m _ => sum_congr rfl fun n _ => by rw [hBs]
  have hrow : ∀ m ∈ Icc 1 N, (∑ n ∈ Icc 1 N, B m n) ≤
      1 + 2 * m * (Real.exp w - 1) := fun m hm => log_window_row_le hw hm
  rw [integral_atomicTest_sq_eq_gram hg hgc]
  calc
    _ ≤ ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N,
        (G / 2) * (x m ^ 2 * B m n + x n ^ 2 * B m n) :=
      sum_le_sum fun m _ => sum_le_sum fun n _ => hpoint m n
    _ = G * ∑ m ∈ Icc 1 N, x m ^ 2 * ∑ n ∈ Icc 1 N, B m n := by
      simp only [← mul_sum, sum_add_distrib, hswap]
      ring
    _ ≤ G * ∑ m ∈ Icc 1 N, x m ^ 2 * (1 + 2 * m * (Real.exp w - 1)) :=
      mul_le_mul_of_nonneg_left
        (sum_le_sum fun m hm => mul_le_mul_of_nonneg_left (hrow m hm) (sq_nonneg _)) hG


/-- Exponential multiplication of an atomic sum moves the center factor into its coefficients. -/
theorem atomicTest_exponential_conjugate (g : ℝ → ℝ) (x : ℕ → ℝ) (N : ℕ) (a u : ℝ) :
    atomicTest N (fun n => Real.exp (a * Real.log n) * x n)
      (fun v => Real.exp (a * v) * g v) u = Real.exp (a * u) * atomicTest N x g u := by
  unfold atomicTest
  rw [mul_sum]
  apply sum_congr rfl
  intro n hn
  calc
    _ = (Real.exp (a * Real.log n) * Real.exp (a * (u - Real.log n))) *
        (x n * g (u - Real.log n)) := by ring
    _ = _ := by
      rw [← Real.exp_add, show a * Real.log n + a * (u - Real.log n) = a * u by ring]

/-- A decreasing exponential does not increase the square mass of a one-sided atom. -/
theorem integral_exponential_atom_sq_le {g : ℝ → ℝ}
    (hg : Continuous g) (hgc : HasCompactSupport g)
    (hs : ∀ u, u < 0 → g u = 0) :
    (∫ u, (Real.exp ((-4) * u) * g u) ^ 2) ≤ ∫ u, g u ^ 2 := by
  have hgc2 : HasCompactSupport (fun u => g u ^ 2) := by
    rw [hasCompactSupport_iff_eventuallyEq] at hgc ⊢
    exact hgc.mono fun u hu => by
      change g u = 0 at hu
      change g u ^ 2 = 0
      rw [hu, zero_pow (by decide : (2 : ℕ) ≠ 0)]
  have hgcw : HasCompactSupport (fun u => (Real.exp ((-4) * u) * g u) ^ 2) := by
    rw [hasCompactSupport_iff_eventuallyEq] at hgc2 ⊢
    exact hgc2.mono fun u hu => by
      change g u ^ 2 = 0 at hu
      change (Real.exp ((-4) * u) * g u) ^ 2 = 0
      rw [mul_pow, hu, mul_zero]
  have hcw : Continuous (fun u => (Real.exp ((-4) * u) * g u) ^ 2) := by fun_prop
  apply integral_mono (hcw.integrable_of_hasCompactSupport hgcw)
    ((hg.pow 2).integrable_of_hasCompactSupport hgc2)
  intro u
  change (Real.exp ((-4) * u) * g u) ^ 2 ≤ g u ^ 2
  by_cases hu : 0 ≤ u
  · have he : Real.exp ((-4) * u) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith only [hu])
    rw [mul_pow]
    exact mul_le_of_le_one_left (sq_nonneg _) (pow_le_one₀ (Real.exp_pos _).le he)
  · simp only [hs u (lt_of_not_ge hu), mul_zero, zero_pow (by norm_num : 2 ≠ 0), le_refl]

/-- The eighth exponential mass is the ordinary mass of an exponentially conjugated atomic sum. -/
theorem integral_normalized_synthesis_exponential_mass_eq
    (φ : ℝ → ℝ) (x : ℕ → ℝ) (c : ℝ) (N : ℕ) :
    (∫ y, normalizedCentredAtomicTest φ x c N y ^ 2 * Real.exp (-(8 * y))) =
      ((N : ℝ) / c ^ 2 * Real.exp (8 * Real.log N)) *
        ∫ u, atomicTest N (fun n => Real.exp ((-4) * Real.log n) * x n)
          (fun v => Real.exp ((-4) * v) * atomDilate φ (c / N) v) u ^ 2 := by
  let A := atomicTest N (fun n => Real.exp ((-4) * Real.log n) * x n)
    (fun v => Real.exp ((-4) * v) * atomDilate φ (c / N) v)
  have hpoint (y : ℝ) : normalizedCentredAtomicTest φ x c N y ^ 2 * Real.exp (-(8 * y)) =
      ((N : ℝ) / c ^ 2 * Real.exp (8 * Real.log N)) * A (y + Real.log N) ^ 2 := by
    have heq := atomicTest_exponential_conjugate (atomDilate φ (c / N)) x N (-4) (y + Real.log N)
    change A (y + Real.log N) = _ at heq
    rw [heq, mul_pow, ← Real.exp_nat_mul]
    have he : Real.exp (8 * Real.log (N : ℝ)) *
        Real.exp ((2 : ℝ) * ((-4) * (y + Real.log N))) = Real.exp (-(8 * y)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    dsimp only [normalizedCentredAtomicTest, centredAtomicTest]
    rw [mul_pow, div_pow, Real.sq_sqrt (Nat.cast_nonneg N)]
    calc
      _ = ((N : ℝ) / c ^ 2) *
          (Real.exp (8 * Real.log N) * Real.exp (2 * ((-4) * (y + Real.log N)))) *
          atomicTest N x (atomDilate φ (c / N)) (y + Real.log N) ^ 2 := by
        rw [he]
        ring
      _ = _ := by ring
  simp_rw [hpoint]
  rw [integral_const_mul, integral_add_right_eq_self (fun u => A u ^ 2) (Real.log N)]

private theorem exponential_row_coefficient_le {c D : ℝ} {N n : ℕ}
    (hc : 0 < c) (hN : 0 < (N : ℝ)) (hn : 0 < (n : ℝ))
    (hcN : c ≤ N) (hqn : (N : ℝ) / n ≤ D * c) :
    (1 / c) * ((N : ℝ) / n) ^ 8 * (1 + 2 * n * (Real.exp (c / N) - 1)) ≤
      (D + 2 * Real.exp 1) * ((N : ℝ) / n) ^ 7 := by
  have he : (N : ℝ) / c * (Real.exp (c / N) - 1) ≤ Real.exp 1 := by
    calc
      _ ≤ (N : ℝ) / c * ((c / N) * Real.exp (c / N)) :=
        mul_le_mul_of_nonneg_left exp_sub_one_le_mul_exp (div_nonneg hN.le hc.le)
      _ = Real.exp (c / N) := by field_simp
      _ ≤ Real.exp 1 := Real.exp_le_exp.mpr ((div_le_one hN).mpr hcN)
  have hq : ((N : ℝ) / n) / c ≤ D := (div_le_iff₀ hc).mpr hqn
  have h := mul_le_mul_of_nonneg_right (show (N : ℝ) / n / c +
      2 * ((N : ℝ) / c * (Real.exp (c / N) - 1)) ≤ D + 2 * Real.exp 1 by
        linarith only [hq, he]) (pow_nonneg (div_nonneg hN.le hn.le) 7)
  calc
    _ = ((N : ℝ) / n / c + 2 * ((N : ℝ) / c * (Real.exp (c / N) - 1))) *
        ((N : ℝ) / n) ^ 7 := by
      field_simp [hc.ne', hN.ne', hn.ne']
    _ ≤ _ := h

/-- The normalized collar has uniformly bounded eighth exponential mass in its
seventh-power coefficient norm. The constant is independent of aperture and overlap. -/
theorem normalized_tail_exponential_mass_le {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hφs : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    {c : ℝ} (hc1 : 1 ≤ c) {N : ℕ} (hLN : linearDefectCutoff c ≤ N) (x : ℕ → ℝ) :
    (∫ y, normalizedCentredAtomicTest φ
      (atomicTailCoefficients (N / linearDefectCutoff c) x) c N y ^ 2 * Real.exp (-(8 * y))) ≤
      (256 * Real.exp 2 + 4 + 2 * Real.exp 1) * (∫ u, φ u ^ 2) *
        topCollarSeventhMass (N / linearDefectCutoff c) N x := by
  let L := linearDefectCutoff c
  let M := N / L
  let w : ℝ := c / N
  let g := atomDilate φ w
  let y := atomicTailCoefficients M x
  let z : ℕ → ℝ := fun n => Real.exp ((-4) * Real.log n) * y n
  let g₄ : ℝ → ℝ := fun u => Real.exp ((-4) * u) * g u
  let W : ℝ := (N : ℝ) / c ^ 2 * Real.exp (8 * Real.log N)
  let D : ℝ := 256 * Real.exp 2 + 4
  obtain ⟨hL3, h4c, _, hLup⟩ := linearDefectCutoff_bounds hc1
  have hc : 0 < c := zero_lt_one.trans_le hc1
  have hN0 : 0 < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hcN : c ≤ N := by
    have hln : (linearDefectCutoff c : ℝ) ≤ N := by exact_mod_cast hLN
    linarith only [h4c, hln, hc]
  have hw : 0 < w := div_pos hc hN0
  have hg : Continuous g := hφ.comp (continuous_id.div_const _)
  have hgs : ∀ u, u ∉ Set.Icc 0 w → g u = 0 := by
    intro u hu
    apply hφs
    intro hu'
    apply hu
    have hlo := hu'.1
    rw [le_div_iff₀ hw, zero_mul] at hlo
    exact ⟨hlo, (div_le_one hw).mp hu'.2⟩
  have hgc : HasCompactSupport g := HasCompactSupport.intro isCompact_Icc hgs
  have hg₄ : Continuous g₄ := (by fun_prop : Continuous (fun u : ℝ => Real.exp ((-4) * u))).mul hg
  have hg₄c : HasCompactSupport g₄ := hgc.mul_left
  have hg₄s : ∀ u, u ∉ Set.Icc 0 w → g₄ u = 0 := by
    intro u hu
    simp only [g₄, hgs u hu, mul_zero]
  have hmass := integral_exponential_atom_sq_le hg hgc (fun u hu =>
    hgs u (fun h => (not_lt_of_ge h.1) hu))
  have hrows := integral_atomicTest_sq_le_local_overlap hg₄ hg₄c hg₄s hw.le N z
  have he0 : 0 ≤ Real.exp w - 1 := sub_nonneg.mpr (Real.one_le_exp hw.le)
  have hs0 : 0 ≤ ∑ n ∈ Icc 1 N, z n ^ 2 * (1 + 2 * n * (Real.exp w - 1)) :=
    sum_nonneg fun n _ => mul_nonneg (sq_nonneg _) (by positivity)
  have hbound := hrows.trans (mul_le_mul_of_nonneg_right hmass hs0)
  change (∫ u, atomicTest N z g₄ u ^ 2) ≤ (∫ u, atomDilate φ w u ^ 2) *
    ∑ n ∈ Icc 1 N, z n ^ 2 * (1 + 2 * n * (Real.exp w - 1)) at hbound
  rw [SpacingScaleHarmonicAnalysis.integral_atomDilate_sq hw] at hbound
  have hW : 0 ≤ W := mul_nonneg (div_nonneg hN0.le (sq_nonneg c)) (Real.exp_pos _).le
  have hscaled := mul_le_mul_of_nonneg_left hbound hW
  rw [integral_normalized_synthesis_exponential_mass_eq]
  change W * (∫ u, atomicTest N z g₄ u ^ 2) ≤ _
  refine hscaled.trans ?_
  have heN : Real.exp (8 * Real.log (N : ℝ)) = (N : ℝ) ^ 8 := by
    rw [show (8 : ℝ) = ((8 : ℕ) : ℝ) from rfl, Real.exp_nat_mul, Real.exp_log hN0]
  have heqn : W * (w * (∫ u, φ u ^ 2) *
      ∑ n ∈ Icc 1 N, z n ^ 2 * (1 + 2 * n * (Real.exp w - 1))) =
      (∫ u, φ u ^ 2) * ∑ n ∈ Icc 1 N,
        ((1 / c) * ((N : ℝ) / n) ^ 8 * (1 + 2 * n * (Real.exp w - 1))) * y n ^ 2 := by
    simp only [mul_sum]
    apply sum_congr rfl
    intro n hn
    have hn0 : 0 < (n : ℝ) := by exact_mod_cast (mem_Icc.mp hn).1
    have hen : Real.exp ((-4) * Real.log (n : ℝ)) = 1 / (n : ℝ) ^ 4 := by
      rw [neg_mul, Real.exp_neg, show (4 : ℝ) = ((4 : ℕ) : ℝ) from rfl,
        Real.exp_nat_mul, Real.exp_log hn0, one_div]
    dsimp only [W, z, w]
    rw [heN, hen]
    field_simp [hc.ne', hN0.ne', hn0.ne']
  rw [heqn]
  have hpoint : ∀ n ∈ Icc 1 N,
      ((1 / c) * ((N : ℝ) / n) ^ 8 * (1 + 2 * n * (Real.exp w - 1))) * y n ^ 2 ≤
        (D + 2 * Real.exp 1) * (((N : ℝ) / n) ^ 7 * y n ^ 2) := by
    intro n hn
    by_cases hMn : M < n
    · have hn0 : 0 < (n : ℝ) := by exact_mod_cast (mem_Icc.mp hn).1
      have hL0 : 0 < L := by dsimp only [L]; omega
      have hdn : N / L + 1 ≤ n := by change N / L < n at hMn; omega
      have hmul := Nat.mul_le_mul_left L hdn
      have hmod := Nat.mod_lt N hL0
      have hid := Nat.mod_add_div N L
      have hNn : N < L * n := by nlinarith only [hmul, hmod, hid]
      have hq : (N : ℝ) / n ≤ D * c := by
        have hlt : (N : ℝ) / n < L := (div_lt_iff₀ hn0).mpr (by exact_mod_cast hNn)
        exact hlt.le.trans hLup
      have h := mul_le_mul_of_nonneg_right
        (exponential_row_coefficient_le hc hN0 hn0 hcN hq) (sq_nonneg (y n))
      simpa only [mul_assoc] using h
    · simp only [y, atomicTailCoefficients, if_neg hMn, zero_pow (by norm_num : 2 ≠ 0), mul_zero, le_refl]
  have hsum : (∑ n ∈ Icc 1 N, ((N : ℝ) / n) ^ 7 * y n ^ 2) = topCollarSeventhMass M N x := by
    simp only [y, atomicTailCoefficients_sq, mul_ite, mul_zero, ← sum_filter]
    have hfilter : (Icc (1 : ℕ) N).filter (fun n => M < n) = Ioc M N := by
      ext n
      simp only [mem_filter, mem_Icc, mem_Ioc]
      constructor
      · rintro ⟨⟨_, hnN⟩, hMn⟩
        exact ⟨hMn, hnN⟩
      · rintro ⟨hMn, hnN⟩
        exact ⟨⟨Nat.succ_le_of_lt ((Nat.zero_le M).trans_lt hMn), hnN⟩, hMn⟩
    rw [hfilter]
    rfl
  have hφmass : 0 ≤ ∫ u, φ u ^ 2 := integral_nonneg fun u => sq_nonneg (φ u)
  have h := mul_le_mul_of_nonneg_left (sum_le_sum hpoint) hφmass
  rw [← mul_sum, hsum] at h
  exact h.trans_eq (by dsimp only [D, M, L]; ring)

#print axioms integral_atomicTest_sq_le_local_overlap
#print axioms atomicTest_exponential_conjugate
#print axioms integral_normalized_synthesis_exponential_mass_eq
#print axioms normalized_tail_exponential_mass_le
end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
