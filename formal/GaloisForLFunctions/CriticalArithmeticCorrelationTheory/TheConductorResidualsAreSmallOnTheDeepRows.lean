import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheBandFarCrossBelowTheEighthRoot
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.QuadraticOverlapConductorResiduals
import GaloisForLFunctions.CompletedArithmeticForms.ExceptionalConductorsVanishAbovePolylog
import GaloisForLFunctions.SignedArithmeticHodgeTheory.OneArithmeticRemainderControlsEveryRamanujanResidual
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.ActualUpwardRowsHaveUniformConductorBounds
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.PrimeBoundaryErrorsHavePolynomialHarmonicBounds
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.SmallWidthRealizesTheUpwardPrimeOffsets

/-!
# The conductor residuals are small on the deep rows

The residual `r_m = W v_m − E_m v_m` of a Ramanujan conductor has squared norm `≍ c²/log N`,
carried by the near channels on the top rows `N ≤ 2ce² n`. On the deep rows `nX ≤ N`
(`deepRows`, `deepMass`), with `X > 2ce²`:

* the near-Gamma-downward and near-center channels vanish (`nearRowIndices` is empty and the
  downward windows contain no integer partner);
* the center residual is `O(α² m² (log N)²/(X² log N))` (exact center kernel
  `√(nj)/2·(1/|n−j| + 1/(n+j))`, partial Ramanujan sums `≤ m`);
* the separated cross error is `O(m c²/(X² log N) + m c⁴/(N X log N))` (row bound);
* the upward residual is the logarithmic linearization (small on all rows), the prime-index
  boundary window (`O(B²φ(m)/(X log N))`) and the shifted affine shell errors (rate `ρ/√n`);
* the prime residual keeps its total `O(m(1 + log m)²/log N)`, independent of `c`; the self and
  pole errors are `O(m c²/N²)` and `O(m c¹⁰ (log N/N)²)`.

`exists_deepMass_conductorResidual_le` collects these into `deepResidualBudget`.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Finset Filter Topology
open scoped RealInnerProductSpace Matrix

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory

open BezoutValuationIncidence RenormalizedArithmeticPotentialTheory CompletedArithmeticForms
  RenormalizedArithmeticPotentialTheory.CompletedShell SpacingScaleHarmonicAnalysis
  CriticalScaleArithmeticRigidity

/-! ### Deep rows -/

/-- The deep rows `n X ≤ N`. -/
def deepRows (N : ℕ) (X : ℝ) : Finset ℕ := (Icc 1 N).filter fun n : ℕ => (n : ℝ) * X ≤ N

/-- The square mass of a horizon vector on the deep rows. -/
def deepMass {N : ℕ} (X : ℝ) (v : EuclideanSpace ℝ (PrimeHorizonIndex N)) : ℝ :=
  ∑ n ∈ deepRows N X, primeHorizonExtension v n ^ 2

theorem deepMass_nonneg {N : ℕ} (X : ℝ) (v : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    0 ≤ deepMass X v := sum_nonneg fun _ _ => sq_nonneg _

theorem deepMass_le_norm_sq {N : ℕ} (X : ℝ) (v : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    deepMass X v ≤ ‖v‖ ^ 2 := by
  rw [← sum_primeHorizonExtension_sq]
  exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => sq_nonneg _

theorem deepMass_smul {N : ℕ} (X r : ℝ) (v : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    deepMass X (r • v) = r ^ 2 * deepMass X v := by
  unfold deepMass
  rw [mul_sum]
  refine sum_congr rfl fun n hn => ?_
  have hn' := (mem_filter.mp hn).1
  rw [primeHorizonExtension_coe _ ⟨n, hn'⟩, primeHorizonExtension_coe _ ⟨n, hn'⟩]
  change (r * v ⟨n, hn'⟩) ^ 2 = _
  ring

theorem primeHorizonExtension_add' {N : ℕ} (x y : EuclideanSpace ℝ (PrimeHorizonIndex N))
    {n : ℕ} (hn : n ∈ Icc 1 N) :
    primeHorizonExtension (x + y) n = primeHorizonExtension x n + primeHorizonExtension y n := by
  rw [primeHorizonExtension_coe _ ⟨n, hn⟩, primeHorizonExtension_coe _ ⟨n, hn⟩,
    primeHorizonExtension_coe _ ⟨n, hn⟩]
  rfl

theorem primeHorizonExtension_sub' {N : ℕ} (x y : EuclideanSpace ℝ (PrimeHorizonIndex N))
    {n : ℕ} (hn : n ∈ Icc 1 N) :
    primeHorizonExtension (x - y) n = primeHorizonExtension x n - primeHorizonExtension y n := by
  rw [primeHorizonExtension_coe _ ⟨n, hn⟩, primeHorizonExtension_coe _ ⟨n, hn⟩,
    primeHorizonExtension_coe _ ⟨n, hn⟩]
  rfl

theorem primeHorizonExtension_neg' {N : ℕ} (x : EuclideanSpace ℝ (PrimeHorizonIndex N))
    {n : ℕ} (hn : n ∈ Icc 1 N) :
    primeHorizonExtension (-x) n = -primeHorizonExtension x n := by
  rw [primeHorizonExtension_coe _ ⟨n, hn⟩, primeHorizonExtension_coe _ ⟨n, hn⟩]
  rfl

/-- **Eight channels on the deep rows.** -/
theorem deepMass_eight_le {N : ℕ} (X : ℝ) (p s c x q y z u : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    deepMass X (-p + s + c - x + q + (y + z) - u) ≤
      8 * (deepMass X p + deepMass X s + deepMass X c + deepMass X x + deepMass X q +
        deepMass X y + deepMass X z + deepMass X u) := by
  unfold deepMass
  simp only [← sum_add_distrib, mul_sum]
  refine sum_le_sum fun n hn => ?_
  have hn' := (mem_filter.mp hn).1
  simp only [primeHorizonExtension_sub' _ _ hn', primeHorizonExtension_add' _ _ hn',
    primeHorizonExtension_neg' _ hn']
  set a₁ := primeHorizonExtension p n
  set a₂ := primeHorizonExtension s n
  set a₃ := primeHorizonExtension c n
  set a₄ := primeHorizonExtension x n
  set a₅ := primeHorizonExtension q n
  set a₆ := primeHorizonExtension y n
  set a₇ := primeHorizonExtension z n
  set a₈ := primeHorizonExtension u n
  have key : ∀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ : ℝ,
      (b₁ + b₂ + b₃ + b₄ + b₅ + b₆ + b₇ + b₈) ^ 2 ≤
        8 * (b₁ ^ 2 + b₂ ^ 2 + b₃ ^ 2 + b₄ ^ 2 + b₅ ^ 2 + b₆ ^ 2 + b₇ ^ 2 + b₈ ^ 2) := by
    intro b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈
    have e : 8 * (b₁ ^ 2 + b₂ ^ 2 + b₃ ^ 2 + b₄ ^ 2 + b₅ ^ 2 + b₆ ^ 2 + b₇ ^ 2 + b₈ ^ 2) -
        (b₁ + b₂ + b₃ + b₄ + b₅ + b₆ + b₇ + b₈) ^ 2 =
        (b₁ - b₂) ^ 2 + (b₁ - b₃) ^ 2 + (b₁ - b₄) ^ 2 + (b₁ - b₅) ^ 2 + (b₁ - b₆) ^ 2 +
        (b₁ - b₇) ^ 2 + (b₁ - b₈) ^ 2 + (b₂ - b₃) ^ 2 + (b₂ - b₄) ^ 2 + (b₂ - b₅) ^ 2 +
        (b₂ - b₆) ^ 2 + (b₂ - b₇) ^ 2 + (b₂ - b₈) ^ 2 + (b₃ - b₄) ^ 2 + (b₃ - b₅) ^ 2 +
        (b₃ - b₆) ^ 2 + (b₃ - b₇) ^ 2 + (b₃ - b₈) ^ 2 + (b₄ - b₅) ^ 2 + (b₄ - b₆) ^ 2 +
        (b₄ - b₇) ^ 2 + (b₄ - b₈) ^ 2 + (b₅ - b₆) ^ 2 + (b₅ - b₇) ^ 2 + (b₅ - b₈) ^ 2 +
        (b₆ - b₇) ^ 2 + (b₆ - b₈) ^ 2 + (b₇ - b₈) ^ 2 := by ring
    have : 0 ≤ (b₁ - b₂) ^ 2 + (b₁ - b₃) ^ 2 + (b₁ - b₄) ^ 2 + (b₁ - b₅) ^ 2 + (b₁ - b₆) ^ 2 +
        (b₁ - b₇) ^ 2 + (b₁ - b₈) ^ 2 + (b₂ - b₃) ^ 2 + (b₂ - b₄) ^ 2 + (b₂ - b₅) ^ 2 +
        (b₂ - b₆) ^ 2 + (b₂ - b₇) ^ 2 + (b₂ - b₈) ^ 2 + (b₃ - b₄) ^ 2 + (b₃ - b₅) ^ 2 +
        (b₃ - b₆) ^ 2 + (b₃ - b₇) ^ 2 + (b₃ - b₈) ^ 2 + (b₄ - b₅) ^ 2 + (b₄ - b₆) ^ 2 +
        (b₄ - b₇) ^ 2 + (b₄ - b₈) ^ 2 + (b₅ - b₆) ^ 2 + (b₅ - b₇) ^ 2 + (b₅ - b₈) ^ 2 +
        (b₆ - b₇) ^ 2 + (b₆ - b₈) ^ 2 + (b₇ - b₈) ^ 2 := by positivity
    linarith
  have h := key (-a₁) a₂ a₃ (-a₄) a₅ a₆ a₇ (-a₈)
  simp only [neg_sq] at h
  linarith

/-! ### The near channels vanish on the deep rows -/

theorem one_div_succ_le_abs_log_sub {a n : ℕ} (ha : 1 ≤ a) (hn : 1 ≤ n) (hne : a ≠ n) :
    1 / ((n : ℝ) + 1) ≤ |Real.log a - Real.log n| := by
  have ha0 : (0 : ℝ) < a := by exact_mod_cast ha
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hp : 0 < 1 / ((n : ℝ) + 1) := by positivity
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hle : (a : ℝ) + 1 ≤ n := by exact_mod_cast hlt
    have h := Real.log_le_sub_one_of_pos (div_pos ha0 hn0)
    rw [Real.log_div ha0.ne' hn0.ne'] at h
    have hfrac : (a : ℝ) / n ≤ 1 - 1 / ((n : ℝ) + 1) := by
      rw [div_le_iff₀ hn0]
      have : (1 - 1 / ((n : ℝ) + 1)) * n = n - n / ((n : ℝ) + 1) := by ring
      rw [this]
      have : (n : ℝ) / ((n : ℝ) + 1) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
      linarith
    rw [abs_of_neg (by linarith)]
    linarith
  · have hle : (n : ℝ) + 1 ≤ a := by exact_mod_cast hgt
    have h := Real.log_le_sub_one_of_pos (div_pos hn0 ha0)
    rw [Real.log_div hn0.ne' ha0.ne'] at h
    have hfrac : (n : ℝ) / a ≤ 1 - 1 / ((n : ℝ) + 1) := by
      rw [div_le_iff₀ ha0]
      have e : (1 - 1 / ((n : ℝ) + 1)) = n / ((n : ℝ) + 1) := by field_simp; ring
      rw [e, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      nlinarith
    rw [abs_of_pos (by linarith)]
    linarith

theorem nearRowIndices_eq_empty_of_deep {c X : ℝ} {N n : ℕ} (hc : 0 < c) (hw : c / N ≤ 1)
    (hX : linearNearRowRadius c < X) (hn : n ∈ deepRows N X) : nearRowIndices c N n = ∅ := by
  obtain ⟨hnI, hnX⟩ := mem_filter.mp hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (mem_Icc.mp hnI).1
  rw [Finset.eq_empty_iff_forall_notMem]
  intro j hj
  have h := (nearRow_geometry_small_width hc hnI hj hw).2.1
  nlinarith

theorem primeHorizonExtension_nearCenterVector_deep (φ : ℝ → ℝ) {c X : ℝ} {N n : ℕ} (m : ℕ)
    (hc : 0 < c) (hw : c / N ≤ 1) (hX : linearNearRowRadius c < X) (hn : n ∈ deepRows N X) :
    primeHorizonExtension (nearCenterVector φ c N m) n = 0 := by
  have hnI := (mem_filter.mp hn).1
  rw [primeHorizonExtension_coe _ ⟨n, hnI⟩]
  change (∑ j ∈ nearRowIndices c N n, _) / _ = 0
  rw [nearRowIndices_eq_empty_of_deep hc hw hX hn, sum_empty, zero_div]

/-- The downward windows of a deep row contain no integer partner. -/
theorem downwardPrimeRow_eq_zero_of_deep {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) {c : ℝ} {N n : ℕ} (hc : 0 < c) (hN : 1 ≤ N)
    (hn : 1 ≤ n) (hdeep : ((n : ℝ) + 1) * (c / N) < 1) (x : ℕ → ℝ) :
    downwardPrimeRow (atomDilate φ (c / N)) N x n = 0 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hw : 0 < c / N := div_pos hc hN0
  obtain ⟨-, hgs, -⟩ := atomDilate_facts hφ hsupp hw
  unfold downwardPrimeRow
  have hterm : ∀ k : ℕ, _root_.RHTower.vonMangoldtAtom k * ∑ j ∈ Icc 1 N, x j *
      (if n = k * j then 0 else bumpCorr (atomDilate φ (c / N)) (Real.log k - (Real.log n - Real.log j))) = 0 := by
    intro k
    rcases lt_or_ge k 2 with hk2 | hk2
    · rw [vonMangoldtAtom_eq_zero_of_lt_two hk2, zero_mul]
    · rw [sum_eq_zero, mul_zero]
      intro j hj
      have hj1 := (mem_Icc.mp hj).1
      split_ifs with heq
      · rw [mul_zero]
      · have hkj : 1 ≤ k * j := Nat.mul_pos (by omega) hj1
        have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
        have hj0 : (0 : ℝ) < j := by exact_mod_cast hj1
        have hlog := one_div_succ_le_abs_log_sub hkj hn (Ne.symm heq)
        have he : Real.log k - (Real.log n - Real.log j) = Real.log ((k * j : ℕ) : ℝ) - Real.log n := by
          push_cast; rw [Real.log_mul hk0.ne' hj0.ne']; ring
        have hn0 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
        have hlt : c / N < |Real.log k - (Real.log n - Real.log j)| := by
          rw [he]
          refine lt_of_lt_of_le ?_ hlog
          rw [lt_div_iff₀ hn0]; linarith
        rw [bumpCorr_eq_zero hgs hlt, mul_zero]
  simp only [hterm, tsum_zero]

theorem primeHorizonExtension_nearGammaDownward_deep {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) {c X : ℝ} {N n : ℕ} (m : ℕ) (hc : 0 < c)
    (hN : 1 ≤ N) (hw : c / N ≤ 1) (hX : linearNearRowRadius c < X) (hX2 : 2 * c < X)
    (hn : n ∈ deepRows N X) :
    primeHorizonExtension (normalizedFullNearGammaDownwardVector φ c N m) n = 0 := by
  obtain ⟨hnI, hnX⟩ := mem_filter.mp hn
  have hn1 := (mem_Icc.mp hnI).1
  have hn1R : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hdeep : ((n : ℝ) + 1) * (c / N) < 1 := by
    rw [mul_div_assoc', div_lt_one hN0]
    have h1 : ((n : ℝ) + 1) * c ≤ 2 * n * c := by nlinarith
    have h2 : 2 * (n : ℝ) * c < n * X := by nlinarith
    linarith
  rw [primeHorizonExtension_coe _ ⟨n, hnI⟩]
  change ((∑ j ∈ nearRowIndices c N n, _) - _) / _ = 0
  rw [nearRowIndices_eq_empty_of_deep hc hw hX hn, sum_empty,
    downwardPrimeRow_eq_zero_of_deep hφ hsupp hc hN hn1 hdeep, zero_div, sub_zero, zero_div]

/-! ### The center residual on the deep rows -/

theorem primeHorizonExtension_horizonKernel_apply (K : ℕ → ℕ → ℝ) {N n : ℕ}
    (x : EuclideanSpace ℝ (PrimeHorizonIndex N)) (hn : n ∈ Icc 1 N) :
    primeHorizonExtension (Matrix.toEuclideanLin (horizonKernelMatrix K N) x) n =
      ∑ j ∈ Icc 1 N, K n j * primeHorizonExtension x j := by
  rw [primeHorizonExtension_coe _ ⟨n, hn⟩]
  change (∑ j : PrimeHorizonIndex N, horizonKernelMatrix K N ⟨n, hn⟩ j * x j) = _
  rw [← sum_coe_sort (Icc 1 N)]
  refine sum_congr rfl fun j _ => ?_
  rw [primeHorizonExtension_coe x j]
  rfl

theorem harmonic_le_one_add_log' (N : ℕ) : (harmonic N : ℝ) ≤ 1 + Real.log N :=
  harmonic_le_one_add_log N

/-- **Center residual, one row.** `|C_α v_m − [m = 1]α v_m|(n) ≤
α/(N√log N)·(m/√n + 3m√n(H_N + 1))`. -/
theorem abs_centerResidual_row_le {α : ℝ} (hα : 0 ≤ α) {m N n : ℕ} (hm : 1 ≤ m)
    (hn : n ∈ Icc 1 N) (hL : 0 < Real.log N) :
    |primeHorizonExtension (Matrix.toEuclideanLin (fullWeilCenterMatrix α N)
        (normalizedRamanujanHorizonVector m N) -
      (if m = 1 then α else 0) • normalizedRamanujanHorizonVector m N) n| ≤
      α / (N * Real.sqrt (Real.log N)) *
        ((m : ℝ) / Real.sqrt n + 3 * m * Real.sqrt n * ((harmonic N : ℝ) + 1)) := by
  have hN1 : 1 ≤ N := (mem_Icc.mp hn).1.trans (mem_Icc.mp hn).2
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
  have hsL : 0 < Real.sqrt (Real.log N) := Real.sqrt_pos.mpr hL
  have hH0 : (0 : ℝ) ≤ harmonic N := by
    have : (0 : ℚ) ≤ harmonic N := by unfold harmonic; positivity
    exact_mod_cast this
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have habs_sub : ∀ x y : ℝ, |x - y| ≤ |x| + |y| := fun x y => by
    rw [sub_eq_add_neg]; exact (abs_add_le x (-y)).trans_eq (by rw [abs_neg])
  set S := ∑ j ∈ Icc 1 N, normalizedRamanujanMode m j / (j : ℝ) with hS
  set T := ∑ j ∈ Icc 1 N, normalizedRamanujanMode m j with hT
  set A := ∑ j ∈ Icc 1 N, archimedeanCenterKernel n j * normalizedRamanujanMode m j / Real.sqrt j
    with hA
  have hvm : ∀ j ∈ Icc 1 N, primeHorizonExtension (normalizedRamanujanHorizonVector m N) j =
      (Real.sqrt (Real.log N))⁻¹ * (normalizedRamanujanMode m j / Real.sqrt j) := by
    intro j hj
    rw [primeHorizonExtension_normalizedRamanujan hj, ramanujanPoleProfile]
  have hC : fullWeilCenterMatrix α N = horizonKernelMatrix
      (fun n j => (α / N) * (arithmeticPoleKernel n j - archimedeanCenterKernel n j)) N := rfl
  have hrow : primeHorizonExtension (Matrix.toEuclideanLin (fullWeilCenterMatrix α N)
      (normalizedRamanujanHorizonVector m N)) n =
      α / (N * Real.sqrt (Real.log N)) * (Real.sqrt n * S + T / Real.sqrt n - A) := by
    rw [hC, primeHorizonExtension_horizonKernel_apply _ _ hn, sum_congr rfl fun j hj => by rw [hvm j hj]]
    have hpole : ∀ j ∈ Icc 1 N, arithmeticPoleKernel n j * (normalizedRamanujanMode m j / Real.sqrt j) =
        Real.sqrt n * (normalizedRamanujanMode m j / (j : ℝ)) +
          normalizedRamanujanMode m j / Real.sqrt n := by
      intro j hj
      have hj0 : (0 : ℝ) < j := by exact_mod_cast (mem_Icc.mp hj).1
      have hsj : 0 < Real.sqrt j := Real.sqrt_pos.mpr hj0
      unfold arithmeticPoleKernel
      field_simp
      simp only [Real.sq_sqrt hn0.le, Real.sq_sqrt hj0.le]
      ring
    have e : ∀ j ∈ Icc 1 N, α / N * (arithmeticPoleKernel n j - archimedeanCenterKernel n j) *
        ((Real.sqrt (Real.log N))⁻¹ * (normalizedRamanujanMode m j / Real.sqrt j)) =
        α / (N * Real.sqrt (Real.log N)) * (Real.sqrt n * (normalizedRamanujanMode m j / (j : ℝ)) +
          normalizedRamanujanMode m j / Real.sqrt n -
          archimedeanCenterKernel n j * normalizedRamanujanMode m j / Real.sqrt j) := by
      intro j hj
      rw [← hpole j hj]
      field_simp
    rw [sum_congr rfl e, ← mul_sum, sum_sub_distrib, sum_add_distrib, ← mul_sum, ← sum_div]
  have hA_abs : |A| ≤ Real.sqrt m * (Real.sqrt n * ((harmonic N : ℝ) + 1)) := by
    have hsum := sum_archimedeanCenterKernel_div_sqrt_le hn
    calc |A| ≤ ∑ j ∈ Icc 1 N, |archimedeanCenterKernel n j * normalizedRamanujanMode m j /
          Real.sqrt j| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ Icc 1 N, Real.sqrt m * (archimedeanCenterKernel n j / Real.sqrt j) := by
          refine sum_le_sum fun j hj => ?_
          have hj0 : (0 : ℝ) < j := by exact_mod_cast (mem_Icc.mp hj).1
          have hsj : 0 < Real.sqrt j := Real.sqrt_pos.mpr hj0
          have hK := archimedeanCenterKernel_nonneg n j
          have hmode := SignedArithmeticHodgeTheory.abs_normalizedRamanujanMode_le_sqrt_totient
            (by omega : 0 < m) j
          have htot : Real.sqrt (m.totient : ℝ) ≤ Real.sqrt m :=
            Real.sqrt_le_sqrt (by exact_mod_cast Nat.totient_le m)
          rw [abs_div, abs_mul, abs_of_nonneg hK, abs_of_pos hsj]
          calc archimedeanCenterKernel n j * |normalizedRamanujanMode m j| / Real.sqrt j ≤
              archimedeanCenterKernel n j * Real.sqrt m / Real.sqrt j := by
                apply div_le_div_of_nonneg_right _ hsj.le
                exact mul_le_mul_of_nonneg_left (hmode.trans htot) hK
            _ = _ := by ring
      _ = Real.sqrt m * ∑ j ∈ Icc 1 N, archimedeanCenterKernel n j / Real.sqrt j := (mul_sum ..).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hsum (Real.sqrt_nonneg _)
  have hsm : Real.sqrt m ≤ m := by
    rw [Real.sqrt_le_left (by linarith)]; nlinarith
  have hcoef : 0 ≤ α / (N * Real.sqrt (Real.log N)) := by positivity
  rw [primeHorizonExtension_sub' _ _ hn, hrow]
  by_cases h1 : m = 1
  · subst h1
    have hS1 : S = harmonic N := by
      rw [hS]
      simp only [normalizedRamanujanMode_one]
      rw [harmonic_eq_sum_Icc]; push_cast
      exact sum_congr rfl fun j _ => by rw [one_div]
    have hT1 : T = N := by
      rw [hT]; simp only [normalizedRamanujanMode_one, sum_const, Nat.card_Icc, Nat.add_sub_cancel,
        nsmul_eq_mul, mul_one]
    rw [if_pos rfl, primeHorizonExtension_coe _ ⟨n, hn⟩]
    change |α / (N * Real.sqrt (Real.log N)) * (Real.sqrt n * S + T / Real.sqrt n - A) -
      α * normalizedRamanujanHorizonVector 1 N ⟨n, hn⟩| ≤ _
    have hv : normalizedRamanujanHorizonVector 1 N ⟨n, hn⟩ = (Real.sqrt (Real.log N))⁻¹ *
        (1 / Real.sqrt n) := by
      have := hvm n hn
      rw [primeHorizonExtension_coe _ ⟨n, hn⟩, normalizedRamanujanMode_one] at this
      exact this
    rw [hv, hS1, hT1]
    have e : α / (N * Real.sqrt (Real.log N)) * (Real.sqrt n * harmonic N + (N : ℝ) / Real.sqrt n - A) -
        α * ((Real.sqrt (Real.log N))⁻¹ * (1 / Real.sqrt n)) =
        α / (N * Real.sqrt (Real.log N)) * (Real.sqrt n * harmonic N - A) := by
      field_simp; ring
    rw [e, abs_mul, abs_of_nonneg hcoef]
    apply mul_le_mul_of_nonneg_left _ hcoef
    have h1 : |Real.sqrt n * harmonic N - A| ≤ Real.sqrt n * harmonic N + |A| := by
      have := habs_sub (Real.sqrt n * (harmonic N : ℝ)) A
      rw [abs_of_nonneg (mul_nonneg hsn.le hH0)] at this; exact this
    simp only [Nat.cast_one, Real.sqrt_one, one_mul] at hA_abs ⊢
    have h2 : 0 ≤ 1 / Real.sqrt n := by positivity
    have h3 : Real.sqrt n * (harmonic N : ℝ) ≤ Real.sqrt n * ((harmonic N : ℝ) + 1) := by
      nlinarith
    have h4 : 0 ≤ Real.sqrt n * ((harmonic N : ℝ) + 1) := by positivity
    linarith
  · have hm2 : 2 ≤ m := by omega
    rw [if_neg h1, zero_smul, primeHorizonExtension_coe 0 ⟨n, hn⟩]
    change |α / (N * Real.sqrt (Real.log N)) * (Real.sqrt n * S + T / Real.sqrt n - A) - 0| ≤ _
    rw [sub_zero, abs_mul, abs_of_nonneg hcoef]
    apply mul_le_mul_of_nonneg_left _ hcoef
    have hSb : |S| ≤ m := CompletedArithmeticForms.abs_sum_Icc_normalizedRamanujanMode_div_le hm2 N
    have hTb : |T| ≤ m := by
      have := CompletedArithmeticForms.abs_sum_Ico_normalizedRamanujanMode_le hm2 (by omega : 1 ≤ N + 1)
      rw [hT]
      have he : Icc 1 N = Ico 1 (N + 1) := by ext j; simp only [mem_Icc, mem_Ico]; omega
      rwa [he]
    have h1 : |Real.sqrt n * S + T / Real.sqrt n - A| ≤ Real.sqrt n * |S| + |T| / Real.sqrt n + |A| := by
      have := habs_sub (Real.sqrt n * S + T / Real.sqrt n) A
      have h2 := abs_add_le (Real.sqrt n * S) (T / Real.sqrt n)
      rw [abs_mul, abs_of_pos hsn, abs_div, abs_of_pos hsn] at h2
      linarith
    have hH1 : (1 : ℝ) ≤ harmonic N + 1 := by linarith
    have hT' : |T| / Real.sqrt n ≤ m / Real.sqrt n := div_le_div_of_nonneg_right hTb hsn.le
    have hmn0 : 0 ≤ (m : ℝ) * Real.sqrt n := by positivity
    have hS' : Real.sqrt n * |S| ≤ m * Real.sqrt n * ((harmonic N : ℝ) + 1) := by
      have h5 := mul_le_mul_of_nonneg_left hSb hsn.le
      have h6 := mul_le_mul_of_nonneg_left hH1 hmn0
      linarith
    have hA' : |A| ≤ m * Real.sqrt n * ((harmonic N : ℝ) + 1) := by
      refine hA_abs.trans ?_
      have : 0 ≤ Real.sqrt n * ((harmonic N : ℝ) + 1) := by positivity
      have := mul_le_mul_of_nonneg_right hsm this
      linarith
    have h7 : 0 ≤ (m : ℝ) * Real.sqrt n * ((harmonic N : ℝ) + 1) := by positivity
    linarith

/-! ### The separated cross error on the deep rows -/

theorem abs_mode_le_sqrt_conductor_deep {m : ℕ} (hm : 0 < m) (n : ℕ) :
    |normalizedRamanujanMode m n| ≤ Real.sqrt (m : ℝ) :=
  (SignedArithmeticHodgeTheory.abs_normalizedRamanujanMode_le_sqrt_totient hm n).trans
    (Real.sqrt_le_sqrt (by exact_mod_cast Nat.totient_le m))

theorem sum_range_sub_le_first_deep (g : ℕ → ℝ) (hg : ∀ k, 0 ≤ g k) (M : ℕ) :
    (∑ k ∈ range M, (g k - g (k + 1))) ≤ g 0 := by
  have htel : ∀ m : ℕ, (∑ k ∈ range m, (g k - g (k + 1))) = g 0 - g m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      ring
  rw [htel M]
  linarith only [hg M]

/-- Quantitative inverse-square tail starting at integer gap `d ≥ 1`:
`∑_{k = d}^N 1 / k^2 ≤ 2 / d`. -/

theorem sum_Icc_inv_sq_from_le_deep {d N : ℕ} (hd : 1 ≤ d) :
    (∑ k ∈ Icc d N, 1 / (k : ℝ) ^ 2) ≤ 2 / (d : ℝ) := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := zero_lt_one.trans_le hd1
  by_cases hdN : d ≤ N
  · have hsplit : Icc d N = insert d (Ioc d N) := by
      ext k; simp only [mem_Icc, mem_insert, mem_Ioc]; omega
    have hmem : d ∉ Ioc d N := by simp only [mem_Ioc]; omega
    rw [hsplit, sum_insert hmem]
    have hfirst : 1 / (d : ℝ) ^ 2 ≤ 1 / (d : ℝ) := by
      rw [div_le_div_iff₀ (sq_pos_of_pos hd0) hd0]
      nlinarith only [hd1]
    have hreindex : (∑ k ∈ Ioc d N, 1 / (k : ℝ) ^ 2) =
        ∑ i ∈ range (N - d), 1 / ((d : ℝ) + (i + 1 : ℕ)) ^ 2 := by
      refine sum_bij (fun k _ => k - (d + 1)) ?_ ?_ ?_ ?_
      · intro k hk; obtain ⟨h1, h2⟩ := mem_Ioc.mp hk; exact mem_range.mpr (by omega)
      · intro k₁ h1 k₂ h2 heq
        obtain ⟨hk1, _⟩ := mem_Ioc.mp h1; obtain ⟨hk2, _⟩ := mem_Ioc.mp h2
        change k₁ - (d + 1) = k₂ - (d + 1) at heq; omega
      · intro i hi
        have hi' := mem_range.mp hi
        exact ⟨d + (i + 1), mem_Ioc.mpr ⟨by omega, by omega⟩, by omega⟩
      · intro k hk
        obtain ⟨hk1, _⟩ := mem_Ioc.mp hk
        have hkeq : (k : ℝ) = (d : ℝ) + ((k - (d + 1) + 1 : ℕ) : ℝ) := by
          exact_mod_cast (show k = d + (k - (d + 1) + 1) by omega)
        rw [hkeq]
    have hstep : ∀ i : ℕ, 1 / ((d : ℝ) + (i + 1 : ℕ)) ^ 2 ≤
        1 / ((d : ℝ) + i) - 1 / ((d : ℝ) + (i + 1 : ℕ)) := by
      intro i
      have ha : 0 < (d : ℝ) + i := by positivity
      have hb : 0 < (d : ℝ) + (i + 1 : ℕ) := by positivity
      have hdiff : 1 / ((d : ℝ) + i) - 1 / ((d : ℝ) + (i + 1 : ℕ)) =
          1 / (((d : ℝ) + i) * ((d : ℝ) + (i + 1 : ℕ))) := by
        field_simp [ha.ne', hb.ne']
        push_cast
        ring
      rw [hdiff, div_le_div_iff₀ (sq_pos_of_pos hb) (mul_pos ha hb)]
      push_cast
      nlinarith only [ha]
    have htail : (∑ k ∈ Ioc d N, 1 / (k : ℝ) ^ 2) ≤ 1 / (d : ℝ) := by
      rw [hreindex]
      calc
        (∑ i ∈ range (N - d), 1 / ((d : ℝ) + (i + 1 : ℕ)) ^ 2) ≤
            ∑ i ∈ range (N - d), (1 / ((d : ℝ) + i) - 1 / ((d : ℝ) + (i + 1 : ℕ))) :=
          sum_le_sum fun i _ => hstep i
        _ ≤ 1 / ((d : ℝ) + (0 : ℕ)) :=
          sum_range_sub_le_first_deep (fun i => 1 / ((d : ℝ) + i)) (fun _ => by positivity) (N - d)
        _ = 1 / (d : ℝ) := by simp
    linarith only [hfirst, htail, (by ring : 1 / (d : ℝ) + 1 / (d : ℝ) = 2 / (d : ℝ))]
  · rw [Icc_eq_empty hdN, sum_empty]
    positivity

/-! ## Section 2: Prime Residual, Self-Error, Cross-Error, Pole-Error, and Near-Center Channels -/


/-- The separated cross-error kernel. -/
def sepModeKernel (φ : ℝ → ℝ) (c : ℝ) (N n j : ℕ) : ℝ :=
  if 2 * (c / N) < |Real.log j - Real.log n| then atomCrossErrorKernel (atomDilate φ (c / N)) n j
  else 0

/-- **Separated cross error, one row.** -/
theorem separatedCrossError_mode_row_sq_le {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2) {m : ℕ} (hm : 0 < m)
    {c : ℝ} (hc : 1 ≤ c) {N : ℕ} (hN : 1 ≤ N) {n : ℕ} (hn : n ∈ Icc 1 N) :
    (∑ j ∈ Icc 1 N, sepModeKernel φ c N n j * (normalizedRamanujanMode m j / Real.sqrt j)) ^ 2 ≤
      2048 * (152 * (∫ u, |φ u|) ^ 2 / (∫ u, φ u ^ 2)) ^ 2 * (m : ℝ) * c ^ 2 * (n : ℝ) /
          (N : ℝ) ^ 2 +
        32 * (152 * (∫ u, |φ u|) ^ 2 / (∫ u, φ u ^ 2)) ^ 2 * (m : ℝ) * c ^ 4 / (N : ℝ) ^ 2 := by
  set K₀ := 152 * (∫ u, |φ u|) ^ 2 / (∫ u, φ u ^ 2) with hK₀
  have hK₀0 : 0 ≤ K₀ := by rw [hK₀]; positivity
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨hn1, hnN⟩ := mem_Icc.mp hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
  let d : ℕ := max 1 ⌈c * (n : ℝ) / N⌉₊
  have hd1 : 1 ≤ d := le_max_left _ _
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd1
  have hcd : c * (n : ℝ) / N ≤ (d : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right 1 ⌈c * (n : ℝ) / N⌉₊))
  have hinv_d : 1 / (d : ℝ) ≤ (N : ℝ) / (c * n) := by
    have hpos : 0 < c * (n : ℝ) / N := div_pos (mul_pos hc0 hn0) hN0
    exact (one_div_le_one_div_of_le hpos hcd).trans_eq (one_div_div _ _)
  let S_mod := (Icc 1 N).filter (fun j : ℕ => 2 * (c / N) < |Real.log (j : ℝ) - Real.log n| ∧
    (n ≤ 2 * j ∧ j ≤ 2 * n))
  have hterm_pt : ∀ j ∈ Icc 1 N,
      |sepModeKernel φ c N n j * (normalizedRamanujanMode m j / Real.sqrt j)| ≤
        K₀ * (c / N) ^ 2 * Real.sqrt m *
          ((if j ∈ S_mod then 8 * (n : ℝ) * Real.sqrt n / |(n : ℝ) - j| ^ 2 else 0) + 4) := by
    intro j hj
    have hj1 := (mem_Icc.mp hj).1
    have hj0 : (0 : ℝ) < j := by exact_mod_cast hj1
    have hsj : 0 < Real.sqrt (j : ℝ) := Real.sqrt_pos.mpr hj0
    have hsj1 : 1 ≤ Real.sqrt (j : ℝ) := by
      simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (by exact_mod_cast hj1 : (1 : ℝ) ≤ j)
    by_cases hgap : 2 * (c / N) < |Real.log j - Real.log n|
    · have hne : n ≠ j := by
        intro heq; subst heq; simp only [sub_self, abs_zero] at hgap
        linarith only [hgap, div_pos hc0 hN0]
      have hd_pos : 0 < |(n : ℝ) - j| :=
        abs_pos.mpr (sub_ne_zero.mpr (by exact_mod_cast hne))
      have hd2 : 0 < |(n : ℝ) - j| ^ 2 := sq_pos_of_pos hd_pos
      have hm0 : 0 ≤ max (n : ℝ) j := hn0.le.trans (le_max_left _ _)
      have hentry := abs_separatedCrossError_le hφ hsupp hM hc0 hN hn hj
      change |sepModeKernel φ c N n j| ≤ K₀ * (c / N) ^ 2 * (max (n : ℝ) j) ^ 2 / |(n : ℝ) - j| ^ 2 at hentry
      have ha : |normalizedRamanujanMode m j / Real.sqrt j| ≤ Real.sqrt m / Real.sqrt j := by
        rw [abs_div, abs_of_pos hsj]
        exact div_le_div_of_nonneg_right (abs_mode_le_sqrt_conductor_deep hm j) hsj.le
      have hprod := mul_le_mul hentry ha (abs_nonneg _) (by positivity)
      rw [← abs_mul] at hprod
      have hrew : K₀ * (c / N) ^ 2 * (max (n : ℝ) j) ^ 2 / |(n : ℝ) - j| ^ 2 *
          (Real.sqrt m / Real.sqrt j) =
          K₀ * (c / N) ^ 2 * Real.sqrt m *
            ((max (n : ℝ) j) ^ 2 / (Real.sqrt j * |(n : ℝ) - j| ^ 2)) := by ring
      rw [hrew] at hprod
      refine hprod.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
      by_cases hnear : n ≤ 2 * j ∧ j ≤ 2 * n
      · rw [if_pos (mem_filter.mpr ⟨hj, hgap, hnear⟩)]
        have hnjR : (n : ℝ) ≤ 2 * j := by exact_mod_cast hnear.1
        have hjnR : (j : ℝ) ≤ 2 * n := by exact_mod_cast hnear.2
        have hs_cmp : Real.sqrt (n : ℝ) ≤ 2 * Real.sqrt (j : ℝ) := by
          by_contra h
          have hlt : 2 * Real.sqrt (j : ℝ) < Real.sqrt (n : ℝ) := lt_of_not_ge h
          have hp := mul_pos (sub_pos.mpr hlt) (by positivity :
            0 < Real.sqrt (n : ℝ) + 2 * Real.sqrt (j : ℝ))
          nlinarith only [hp, Real.sq_sqrt hn0.le, Real.sq_sqrt hj0.le, hnjR, hj0]
        have hm_le : max (n : ℝ) j ≤ 2 * n := max_le (by linarith only [hn0]) hjnR
        have hm2 : (max (n : ℝ) j) ^ 2 ≤ 4 * (n : ℝ) ^ 2 := by
          have hsq := mul_self_le_mul_self hm0 hm_le
          nlinarith only [hsq]
        have hnum : (max (n : ℝ) j) ^ 2 ≤ 8 * (n : ℝ) * Real.sqrt n * Real.sqrt j := by
          calc
            _ ≤ 4 * (n : ℝ) ^ 2 := hm2
            _ = (4 * (n : ℝ) * Real.sqrt n) * Real.sqrt n := by
              rw [mul_assoc (4 * (n : ℝ)), ← pow_two, Real.sq_sqrt hn0.le]; ring
            _ ≤ (4 * (n : ℝ) * Real.sqrt n) * (2 * Real.sqrt j) :=
              mul_le_mul_of_nonneg_left hs_cmp (by positivity)
            _ = _ := by ring
        have ht : (max (n : ℝ) j) ^ 2 / (Real.sqrt j * |(n : ℝ) - j| ^ 2) ≤
            8 * (n : ℝ) * Real.sqrt n / |(n : ℝ) - j| ^ 2 := by
          rw [div_le_div_iff₀ (mul_pos hsj hd2) hd2]
          nlinarith only [mul_nonneg (sub_nonneg.mpr hnum) hd2.le]
        linarith only [ht]
      · rw [if_neg (fun h => hnear (mem_filter.mp h).2.2), zero_add]
        have hm_far : max (n : ℝ) j ≤ 2 * |(n : ℝ) - j| := by
          rcases not_and_or.mp hnear with h | h
          · have hnR' : 2 * (j : ℝ) < n := by exact_mod_cast (lt_of_not_ge h)
            rw [max_eq_left (by linarith only [hnR', hj0]),
              abs_of_pos (by linarith only [hnR', hj0])]
            linarith only [hnR']
          · have hjR' : 2 * (n : ℝ) < j := by exact_mod_cast (lt_of_not_ge h)
            rw [max_eq_right (by linarith only [hjR', hn0]),
              abs_of_neg (by linarith only [hjR', hn0])]
            linarith only [hjR']
        have hm2 : (max (n : ℝ) j) ^ 2 ≤ 4 * |(n : ℝ) - j| ^ 2 := by
          have hsq := mul_self_le_mul_self hm0 hm_far
          nlinarith only [hsq]
        rw [div_le_iff₀ (mul_pos hsj hd2)]
        nlinarith only [hm2, mul_nonneg (sub_nonneg.mpr hsj1) hd2.le]
    · have hz : sepModeKernel φ c N n j = 0 := by unfold sepModeKernel; rw [if_neg hgap]
      rw [hz, zero_mul, abs_zero]
      have hif0 : 0 ≤ (if j ∈ S_mod then 8 * (n : ℝ) * Real.sqrt n / |(n : ℝ) - j| ^ 2 else 0) + 4 := by
        split_ifs <;> positivity
      exact mul_nonneg (by positivity) hif0
  -- Every `j ∈ S_mod` satisfies integer distance `≥ d`.
  have hgap_mod : ∀ j ∈ S_mod, c * (n : ℝ) / N < |(n : ℝ) - j| := by
    intro j hjS
    obtain ⟨hj, hgap, hnj2, hjn2⟩ := mem_filter.mp hjS
    have hj0 : (0 : ℝ) < j := by exact_mod_cast (mem_Icc.mp hj).1
    have hnjR : (n : ℝ) ≤ 2 * j := by exact_mod_cast hnj2
    have hne : j ≠ n := by
      intro heq; subst heq; simp only [sub_self, abs_zero] at hgap
      linarith only [hgap, div_pos hc0 hN0]
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hjlt : (j : ℝ) < n := by exact_mod_cast hlt
      have hlog_ub := Real.log_le_sub_one_of_pos (div_pos hn0 hj0)
      rw [Real.log_div hn0.ne' hj0.ne', show (n : ℝ) / j - 1 = ((n : ℝ) - j) / j by
        field_simp [hj0.ne']] at hlog_ub
      have hlog_eq : |Real.log j - Real.log n| = Real.log n - Real.log j := by
        rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log hj0 hjlt.le))]
      have hfrac : ((n : ℝ) - j) / j ≤ 2 * ((n : ℝ) - j) / n := by
        rw [div_le_div_iff₀ hj0 hn0]
        nlinarith only [hnjR, sub_pos.mpr hjlt]
      have habs_eq : |(n : ℝ) - j| = (n : ℝ) - j := abs_of_pos (sub_pos.mpr hjlt)
      have hlt2 : 2 * c / N < 2 * |(n : ℝ) - j| / n := by
        rw [habs_eq, show 2 * c / (N : ℝ) = 2 * (c / N) by ring]
        linarith only [hgap, hlog_eq, hlog_ub, hfrac]
      have hmul := (div_lt_div_iff₀ hN0 hn0).mp hlt2
      exact (div_lt_iff₀ hN0).mpr (by linarith only [hmul])
    · have hngt : (n : ℝ) < j := by exact_mod_cast hgt
      have hlog_ub := Real.log_le_sub_one_of_pos (div_pos hj0 hn0)
      rw [Real.log_div hj0.ne' hn0.ne', show (j : ℝ) / n - 1 = ((j : ℝ) - n) / n by
        field_simp [hn0.ne']] at hlog_ub
      have hlog_eq : |Real.log j - Real.log n| = Real.log j - Real.log n :=
        abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log hn0 hngt.le))
      have habs_eq : |(n : ℝ) - j| = (j : ℝ) - n := by
        rw [abs_sub_comm, abs_of_pos (sub_pos.mpr hngt)]
      have hpos_diff : 0 < ((j : ℝ) - n) / n := div_pos (sub_pos.mpr hngt) hn0
      have h2diff : ((j : ℝ) - n) / n ≤ 2 * ((j : ℝ) - n) / n := by
        rw [mul_div_assoc]; linarith only [hpos_diff]
      have hlt2 : 2 * c / N < 2 * |(n : ℝ) - j| / n := by
        rw [habs_eq, show 2 * c / (N : ℝ) = 2 * (c / N) by ring]
        linarith only [hgap, hlog_eq, hlog_ub, h2diff]
      have hmul := (div_lt_div_iff₀ hN0 hn0).mp hlt2
      exact (div_lt_iff₀ hN0).mpr (by linarith only [hmul])
  -- Tail sum over `S_mod` is at most `4 / d ≤ 4 * N / (c * n)`.
  have hsum_mod : (∑ j ∈ S_mod, 1 / |(n : ℝ) - j| ^ 2) ≤ 4 * (N : ℝ) / (c * n) := by
    let L_set := S_mod.filter (fun j => j < n)
    let R_set := S_mod.filter (fun j => n < j)
    have hsplit_LR : (∑ j ∈ S_mod, 1 / |(n : ℝ) - j| ^ 2) =
        (∑ j ∈ L_set, 1 / |(n : ℝ) - j| ^ 2) + ∑ j ∈ R_set, 1 / |(n : ℝ) - j| ^ 2 := by
      simp only [L_set, R_set, sum_filter, ← sum_add_distrib]
      refine sum_congr rfl fun j _ => ?_
      rcases lt_trichotomy j n with h | rfl | h
      · rw [if_pos h, if_neg (not_lt_of_ge h.le), add_zero]
      · simp
      · rw [if_neg (not_lt_of_ge h.le), if_pos h, zero_add]
    have hL_bound : (∑ j ∈ L_set, 1 / |(n : ℝ) - j| ^ 2) ≤ 2 / (d : ℝ) := by
      have hinj : ∀ i ∈ L_set, ∀ j ∈ L_set, n - i = n - j → i = j := by
        intro i hi j hj hij
        have := (mem_filter.mp hi).2; have := (mem_filter.mp hj).2
        change n - i = n - j at hij; omega
      have hmap : (∑ j ∈ L_set, 1 / |(n : ℝ) - j| ^ 2) =
          ∑ k ∈ L_set.image (fun j => n - j), 1 / (k : ℝ) ^ 2 := by
        rw [sum_image hinj]
        refine sum_congr rfl fun j hj => ?_
        have hlt := (mem_filter.mp hj).2
        rw [Nat.cast_sub hlt.le, abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hlt.le))]
      have hsub_d : L_set.image (fun j => n - j) ⊆ Icc d N := by
        intro k hk
        obtain ⟨j, hjL, rfl⟩ := mem_image.mp hk
        obtain ⟨hjS, hlt⟩ := mem_filter.mp hjL
        have hgj := hgap_mod j hjS
        rw [abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hlt.le)),
          ← Nat.cast_sub hlt.le] at hgj
        have hceil : ⌈c * (n : ℝ) / N⌉₊ ≤ n - j := Nat.ceil_le.mpr hgj.le
        have hd_le : d ≤ n - j := max_le (by omega) hceil
        exact mem_Icc.mpr ⟨hd_le, (Nat.sub_le n j).trans hnN⟩
      rw [hmap]
      exact (sum_le_sum_of_subset_of_nonneg (f := fun k : ℕ => 1 / (k : ℝ) ^ 2)
        hsub_d (fun _ _ _ => by positivity)).trans (sum_Icc_inv_sq_from_le_deep hd1)
    have hR_bound : (∑ j ∈ R_set, 1 / |(n : ℝ) - j| ^ 2) ≤ 2 / (d : ℝ) := by
      have hinj : ∀ i ∈ R_set, ∀ j ∈ R_set, i - n = j - n → i = j := by
        intro i hi j hj hij
        have := (mem_filter.mp hi).2; have := (mem_filter.mp hj).2
        change i - n = j - n at hij; omega
      have hmap : (∑ j ∈ R_set, 1 / |(n : ℝ) - j| ^ 2) =
          ∑ k ∈ R_set.image (fun j => j - n), 1 / (k : ℝ) ^ 2 := by
        rw [sum_image hinj]
        refine sum_congr rfl fun j hj => ?_
        have hlt := (mem_filter.mp hj).2
        rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hlt.le)),
          Nat.cast_sub hlt.le]
      have hsub_d : R_set.image (fun j => j - n) ⊆ Icc d N := by
        intro k hk
        obtain ⟨j, hjR, rfl⟩ := mem_image.mp hk
        obtain ⟨hjS, hlt⟩ := mem_filter.mp hjR
        have hjN := (mem_Icc.mp (mem_filter.mp hjS).1).2
        have hgj := hgap_mod j hjS
        rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hlt.le)),
          ← Nat.cast_sub hlt.le] at hgj
        have hceil : ⌈c * (n : ℝ) / N⌉₊ ≤ j - n := Nat.ceil_le.mpr hgj.le
        have hd_le : d ≤ j - n := max_le (by omega) hceil
        exact mem_Icc.mpr ⟨hd_le, (Nat.sub_le j n).trans hjN⟩
      rw [hmap]
      exact (sum_le_sum_of_subset_of_nonneg (f := fun k : ℕ => 1 / (k : ℝ) ^ 2)
        hsub_d (fun _ _ _ => by positivity)).trans (sum_Icc_inv_sq_from_le_deep hd1)
    rw [hsplit_LR]
    have h4d : (∑ j ∈ L_set, 1 / |(n : ℝ) - j| ^ 2) + ∑ j ∈ R_set, 1 / |(n : ℝ) - j| ^ 2 ≤
        4 * (1 / (d : ℝ)) :=
      (add_le_add hL_bound hR_bound).trans_eq (by ring)
    exact h4d.trans ((mul_le_mul_of_nonneg_left hinv_d (by norm_num)).trans_eq (by ring))
  have hrow_abs : |∑ j ∈ Icc 1 N, sepModeKernel φ c N n j * (normalizedRamanujanMode m j / Real.sqrt j)| ≤
      32 * K₀ * Real.sqrt m * c * Real.sqrt n / N + 4 * K₀ * Real.sqrt m * c ^ 2 / N := by
    have hsub_S : (Icc 1 N).filter (fun j => j ∈ S_mod) = S_mod := by
      ext j; simp only [S_mod, mem_filter]
      exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩
    calc
      |∑ j ∈ Icc 1 N, sepModeKernel φ c N n j * (normalizedRamanujanMode m j / Real.sqrt j)| ≤
          ∑ j ∈ Icc 1 N, |sepModeKernel φ c N n j * (normalizedRamanujanMode m j / Real.sqrt j)| :=
        abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ Icc 1 N, K₀ * (c / N) ^ 2 * Real.sqrt m *
            ((if j ∈ S_mod then 8 * (n : ℝ) * Real.sqrt n / |(n : ℝ) - j| ^ 2 else 0) + 4) :=
        sum_le_sum hterm_pt
      _ = K₀ * (c / N) ^ 2 * Real.sqrt m *
            ((8 * (n : ℝ) * Real.sqrt n) * (∑ j ∈ S_mod, 1 / |(n : ℝ) - j| ^ 2) + 4 * N) := by
        rw [← mul_sum, sum_add_distrib, ← sum_filter, hsub_S, sum_const, nsmul_eq_mul,
          Nat.card_Icc, Nat.add_sub_cancel, mul_sum]
        congr 2
        · exact sum_congr rfl fun _ _ => by ring
        · ring
      _ ≤ K₀ * (c / N) ^ 2 * Real.sqrt m *
            ((8 * (n : ℝ) * Real.sqrt n) * (4 * (N : ℝ) / (c * n)) + 4 * N) :=
        mul_le_mul_of_nonneg_left
          (add_le_add (mul_le_mul_of_nonneg_left hsum_mod (by positivity)) le_rfl)
          (by positivity)
      _ = 32 * K₀ * Real.sqrt m * c * Real.sqrt n / N + 4 * K₀ * Real.sqrt m * c ^ 2 / N := by
        field_simp [hc0.ne', hn0.ne', hN0.ne']; ring
  have hsq := mul_self_le_mul_self (abs_nonneg _) hrow_abs
  rw [← sq, sq_abs, ← sq] at hsq
  let u₁ := 32 * K₀ * Real.sqrt m * c * Real.sqrt n / N
  let u₂ := 4 * K₀ * Real.sqrt m * c ^ 2 / N
  have h2sq : (u₁ + u₂) ^ 2 ≤ 2 * u₁ ^ 2 + 2 * u₂ ^ 2 := by
    nlinarith only [sq_nonneg (u₁ - u₂)]
  have hu1 : 2 * u₁ ^ 2 = 2048 * K₀ ^ 2 * (m : ℝ) * c ^ 2 * (n : ℝ) / (N : ℝ) ^ 2 := by
    dsimp only [u₁]
    rw [div_pow, mul_pow, mul_pow, mul_pow, mul_pow,
      Real.sq_sqrt (Nat.cast_nonneg m), Real.sq_sqrt hn0.le]
    ring
  have hu2 : 2 * u₂ ^ 2 = 32 * K₀ ^ 2 * (m : ℝ) * c ^ 4 / (N : ℝ) ^ 2 := by
    dsimp only [u₂]
    rw [div_pow, mul_pow, mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg m)]
    ring
  exact hsq.trans (h2sq.trans_eq (by rw [hu1, hu2]))

/-! ### Square sums over the deep rows -/

theorem le_of_mem_deepRows {N n : ℕ} {X : ℝ} (hX : 0 < X) (hn : n ∈ deepRows N X) :
    (n : ℝ) ≤ N / X := by
  rw [le_div_iff₀ hX]; exact (mem_filter.mp hn).2

theorem card_deepRows_le {N : ℕ} {X : ℝ} (hX : 0 < X) :
    ((deepRows N X).card : ℝ) ≤ N / X := by
  have hsub : deepRows N X ⊆ Icc 1 ⌊(N : ℝ) / X⌋₊ := by
    intro n hn
    have h1 := (mem_Icc.mp (mem_filter.mp hn).1).1
    exact mem_Icc.mpr ⟨h1, Nat.le_floor (le_of_mem_deepRows hX hn)⟩
  have h := card_le_card hsub
  rw [Nat.card_Icc, Nat.add_sub_cancel] at h
  have h2 : (⌊(N : ℝ) / X⌋₊ : ℝ) ≤ N / X := Nat.floor_le (by positivity)
  have : ((deepRows N X).card : ℝ) ≤ ⌊(N : ℝ) / X⌋₊ := by exact_mod_cast h
  linarith

/-- **Deep square sums from row bounds.** If every deep row has `v_n² ≤ a/n + b + e n`, then
`Σ_deep v_n² ≤ a H_N + b N/X + e (N/X)²`. -/
theorem deepMass_le_of_row {N : ℕ} {X : ℝ} (hX : 0 < X) (v : EuclideanSpace ℝ (PrimeHorizonIndex N))
    {a b e : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (he : 0 ≤ e)
    (h : ∀ n ∈ deepRows N X, primeHorizonExtension v n ^ 2 ≤ a / n + b + e * n) :
    deepMass X v ≤ a * harmonic N + b * (N / X) + e * (N / X) ^ 2 := by
  unfold deepMass
  refine (sum_le_sum h).trans ?_
  rw [sum_add_distrib, sum_add_distrib]
  have h1 : (∑ n ∈ deepRows N X, a / (n : ℝ)) ≤ a * harmonic N := by
    rw [harmonic_eq_sum_Icc]; push_cast
    rw [mul_sum]
    refine (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun n _ _ => ?_).trans
      (le_of_eq (sum_congr rfl fun n _ => by rw [div_eq_mul_inv]))
    positivity
  have h2 : (∑ n ∈ deepRows N X, b) ≤ b * (N / X) := by
    rw [sum_const, nsmul_eq_mul, mul_comm]
    exact mul_le_mul_of_nonneg_left (card_deepRows_le hX) hb
  have h3 : (∑ n ∈ deepRows N X, e * (n : ℝ)) ≤ e * (N / X) ^ 2 := by
    rw [← mul_sum]
    apply mul_le_mul_of_nonneg_left _ he
    calc (∑ n ∈ deepRows N X, (n : ℝ)) ≤ ∑ n ∈ deepRows N X, (N : ℝ) / X :=
          sum_le_sum fun n hn => le_of_mem_deepRows hX hn
      _ = ((deepRows N X).card : ℝ) * (N / X) := by rw [sum_const, nsmul_eq_mul]
      _ ≤ (N / X) * (N / X) :=
          mul_le_mul_of_nonneg_right (card_deepRows_le hX) (by positivity)
      _ = (N / X) ^ 2 := by ring
  linarith

/-- **The center residual on the deep rows.** -/
theorem deepMass_centerResidual_le {α X : ℝ} (hα : 0 ≤ α) (hX : 0 < X) {m N : ℕ} (hm : 1 ≤ m)
    (hL : 0 < Real.log N) :
    deepMass X (Matrix.toEuclideanLin (fullWeilCenterMatrix α N)
        (normalizedRamanujanHorizonVector m N) -
      (if m = 1 then α else 0) • normalizedRamanujanHorizonVector m N) ≤
      2 * α ^ 2 * (m : ℝ) ^ 2 * harmonic N / ((N : ℝ) ^ 2 * Real.log N) +
        18 * α ^ 2 * (m : ℝ) ^ 2 * ((harmonic N : ℝ) + 1) ^ 2 / (X ^ 2 * Real.log N) := by
  have hN1 : 1 ≤ N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · rw [h, Nat.cast_zero, Real.log_zero] at hL; exact absurd hL (lt_irrefl 0)
    · exact h
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  set K := α / (N * Real.sqrt (Real.log N)) with hK
  have hK2 : K ^ 2 = α ^ 2 / ((N : ℝ) ^ 2 * Real.log N) := by
    rw [hK, div_pow, mul_pow, Real.sq_sqrt hL.le]
  have hH0 : (0 : ℝ) ≤ harmonic N := by
    have : (0 : ℚ) ≤ harmonic N := by unfold harmonic; positivity
    exact_mod_cast this
  have hb := deepMass_le_of_row hX _ (a := 2 * K ^ 2 * (m : ℝ) ^ 2) (b := 0)
    (e := 18 * K ^ 2 * (m : ℝ) ^ 2 * ((harmonic N : ℝ) + 1) ^ 2) (by positivity) le_rfl
    (by positivity) (fun n hn => by
      have hnI := (mem_filter.mp hn).1
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hnI).1
      have hr := abs_centerResidual_row_le hα hm hnI hL
      rw [← hK] at hr
      have h2 := pow_le_pow_left₀ (abs_nonneg _) hr 2
      rw [sq_abs] at h2
      refine h2.trans ?_
      have hsn : Real.sqrt n ^ 2 = n := Real.sq_sqrt hn0.le
      have hsn0 : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
      have e : (K * ((m : ℝ) / Real.sqrt n + 3 * m * Real.sqrt n * ((harmonic N : ℝ) + 1))) ^ 2 =
          K ^ 2 * ((m : ℝ) ^ 2 / n + 6 * m ^ 2 * ((harmonic N : ℝ) + 1) +
            9 * m ^ 2 * n * ((harmonic N : ℝ) + 1) ^ 2) := by
        field_simp; rw [hsn]; ring
      rw [e]
      have hineq : 6 * (m : ℝ) ^ 2 * ((harmonic N : ℝ) + 1) ≤
          (m : ℝ) ^ 2 / n + 9 * m ^ 2 * n * ((harmonic N : ℝ) + 1) ^ 2 := by
        have hH1 : (1 : ℝ) ≤ harmonic N + 1 := by linarith
        have h1 : (m : ℝ) ^ 2 / n + 9 * m ^ 2 * n * ((harmonic N : ℝ) + 1) ^ 2 -
            6 * m ^ 2 * ((harmonic N : ℝ) + 1) =
            (m : ℝ) ^ 2 * (1 - 3 * n * ((harmonic N : ℝ) + 1)) ^ 2 / n := by
          field_simp; ring
        have : 0 ≤ (m : ℝ) ^ 2 * (1 - 3 * n * ((harmonic N : ℝ) + 1)) ^ 2 / n := by positivity
        linarith
      have hK0 : 0 ≤ K ^ 2 := sq_nonneg _
      have := mul_le_mul_of_nonneg_left hineq hK0
      have e2 : 2 * K ^ 2 * (m : ℝ) ^ 2 / n + 0 + 18 * K ^ 2 * (m : ℝ) ^ 2 *
          ((harmonic N : ℝ) + 1) ^ 2 * n = 2 * (K ^ 2 * ((m : ℝ) ^ 2 / n +
            9 * m ^ 2 * n * ((harmonic N : ℝ) + 1) ^ 2)) := by ring
      rw [e2]
      nlinarith)
  refine hb.trans (le_of_eq ?_)
  rw [hK2]
  field_simp
  ring

/-- **The separated cross error on the deep rows.** -/
theorem deepMass_separated_le {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2) {m : ℕ} (hm : 0 < m)
    {c X : ℝ} (hc : 1 ≤ c) (hX : 0 < X) {N : ℕ} (hL : 0 < Real.log N) :
    deepMass X (Matrix.toEuclideanLin (separatedCrossErrorMatrix φ c N)
        (normalizedRamanujanHorizonVector m N)) ≤
      32 * (152 * (∫ u, |φ u|) ^ 2 / (∫ u, φ u ^ 2)) ^ 2 * (m : ℝ) * c ^ 4 /
          ((N : ℝ) * X * Real.log N) +
        2048 * (152 * (∫ u, |φ u|) ^ 2 / (∫ u, φ u ^ 2)) ^ 2 * (m : ℝ) * c ^ 2 /
          (X ^ 2 * Real.log N) := by
  have hN1 : 1 ≤ N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · rw [h, Nat.cast_zero, Real.log_zero] at hL; exact absurd hL (lt_irrefl 0)
    · exact h
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  set K₀ := 152 * (∫ u, |φ u|) ^ 2 / (∫ u, φ u ^ 2) with hK₀
  have hK₀0 : 0 ≤ K₀ := by rw [hK₀]; positivity
  have hsep : separatedCrossErrorMatrix φ c N = horizonKernelMatrix (sepModeKernel φ c N) N := rfl
  have hb := deepMass_le_of_row hX (Matrix.toEuclideanLin (separatedCrossErrorMatrix φ c N)
      (normalizedRamanujanHorizonVector m N)) (a := 0)
    (b := 32 * K₀ ^ 2 * (m : ℝ) * c ^ 4 / ((N : ℝ) ^ 2 * Real.log N))
    (e := 2048 * K₀ ^ 2 * (m : ℝ) * c ^ 2 / ((N : ℝ) ^ 2 * Real.log N)) le_rfl (by positivity)
    (by positivity) (fun n hn => by
      have hnI := (mem_filter.mp hn).1
      have hrow := separatedCrossError_mode_row_sq_le hφ hsupp hM hm hc hN1 hnI
      rw [← hK₀] at hrow
      rw [hsep, primeHorizonExtension_horizonKernel_apply _ _ hnI]
      have e : (∑ j ∈ Icc 1 N, sepModeKernel φ c N n j *
          primeHorizonExtension (normalizedRamanujanHorizonVector m N) j) =
          (Real.sqrt (Real.log N))⁻¹ * ∑ j ∈ Icc 1 N, sepModeKernel φ c N n j *
            (normalizedRamanujanMode m j / Real.sqrt j) := by
        rw [mul_sum]
        refine sum_congr rfl fun j hj => ?_
        rw [primeHorizonExtension_normalizedRamanujan hj, ramanujanPoleProfile]; ring
      rw [e, mul_pow, inv_pow, Real.sq_sqrt hL.le]
      calc (Real.log N)⁻¹ * (∑ j ∈ Icc 1 N, sepModeKernel φ c N n j *
            (normalizedRamanujanMode m j / Real.sqrt j)) ^ 2 ≤
          (Real.log N)⁻¹ * (2048 * K₀ ^ 2 * (m : ℝ) * c ^ 2 * (n : ℝ) / (N : ℝ) ^ 2 +
            32 * K₀ ^ 2 * (m : ℝ) * c ^ 4 / (N : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left hrow (by positivity)
        _ = 0 / (n : ℝ) + 32 * K₀ ^ 2 * (m : ℝ) * c ^ 4 / ((N : ℝ) ^ 2 * Real.log N) +
            2048 * K₀ ^ 2 * (m : ℝ) * c ^ 2 / ((N : ℝ) ^ 2 * Real.log N) * n := by
          field_simp; ring)
  refine hb.trans (le_of_eq ?_)
  field_simp
  ring

/-! ### The upward residual on the deep rows -/

theorem natDiv_ge_half {N n : ℕ} (hn : 1 ≤ n) (h : n ≤ N) :
    (N : ℝ) / n / 2 ≤ ((N / n : ℕ) : ℝ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hq := Nat.lt_div_mul_add (a := N) (show 0 < n by omega)
  have hq1 : 1 ≤ N / n := Nat.div_pos h (by omega)
  have : (N : ℝ) < ((N / n : ℕ) : ℝ) * n + n := by exact_mod_cast hq
  have hq1R : (1 : ℝ) ≤ ((N / n : ℕ) : ℝ) := by exact_mod_cast hq1
  rw [div_div, div_le_iff₀ (by positivity)]
  nlinarith

/-- **The upward residual on the deep rows.** With `B = ⌈ce⌉`, on rows `nX ≤ N` the upward row
error splits into the logarithmic linearization (bounded on all rows), the prime-index boundary
window (`O(B²φ²/X)` in square sum) and the shifted affine shell errors, assumed `≤ ρ/√n`. -/
theorem exists_deepMass_upwardResidual_le {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {m N : ℕ} {c X ρ : ℝ}, 0 < m → 1 ≤ N → 1 ≤ Real.log N → 1 ≤ c →
      c / N ≤ 1 → 2 * ((Real.exp 1 + 3) * c) * linearPrimeStrip c ≤ (N : ℝ) →
      2 * (linearPrimeStrip c : ℝ) + 3 ≤ X →
      (∀ n ∈ Icc 1 N, (n : ℝ) * X ≤ N →
        |shiftedReciprocalUpwardRowError φ c id N m n| ≤ ρ / Real.sqrt n ∧
        |shiftedReciprocalUpwardRowError φ c (reflectedAffineShift m) N m n| ≤ ρ / Real.sqrt n) →
      deepMass X (normalizedUpwardPrimeResidual φ c N m) ≤
        3 * (K * (m.totient : ℝ) ^ 2 * c ^ 4 * ((linearPrimeStrip c : ℝ) + 1) ^ 6 *
            (Real.log N / N) ^ 2 +
          2048 * (linearPrimeStrip c : ℝ) ^ 2 * ((linearPrimeStrip c : ℝ) + 1) ^ 2 *
            (m.totient : ℝ) ^ 2 / (X * Real.log N) +
          ρ ^ 2 * harmonic N / Real.log N) := by
  obtain ⟨K, hK, hlog⟩ := exists_logarithmicUpward_uniform_conductor_harmonic_bound hφ hsupp hM
  refine ⟨K, hK, ?_⟩
  intro m N c X ρ hm hN hL1 hc1 hw hkernel hX hrate
  set B := linearPrimeStrip c with hBdef
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hL0 : 0 < Real.log N := zero_lt_one.trans_le hL1
  have hX0 : 0 < X := by have : (0 : ℝ) ≤ B := Nat.cast_nonneg B; linarith
  have hcN : c ≤ N := (div_le_one hN0).mp hw
  have hBN : B ≤ N := by
    have h1 : (B : ℝ) ≤ 2 * ((Real.exp 1 + 3) * c) * B := by
      have : 1 ≤ 2 * ((Real.exp 1 + 3) * c) := by
        have := Real.exp_pos 1; nlinarith
      nlinarith [(Nat.cast_nonneg B : (0 : ℝ) ≤ B)]
    exact_mod_cast h1.trans hkernel
  have hB : ⌈c⌉₊ ≤ B := by
    rw [hBdef, linearPrimeStrip]
    apply Nat.ceil_le_ceil
    have := Real.add_one_le_exp (1 : ℝ)
    nlinarith
  set a : ℕ → ℝ := fun n => (logarithmicUpwardCoefficient φ c B N m n -
    linearizedUpwardCoefficient φ c B N m n) / Real.sqrt n with ha
  set b : ℕ → ℝ := fun n => (linearizedUpwardCoefficient φ c B N m n -
    reciprocalUpwardCoefficient φ c B N m n) / Real.sqrt n with hb
  set r : ℕ → ℝ := fun n => (reciprocalUpwardCoefficient φ c B N m n -
    ramanujanLagCoefficient m n * shellCorrection φ c m) / Real.sqrt n with hr
  have hrow : ∀ n ∈ Icc 1 N, actualUpwardRowError φ c N m n = a n + b n + r n := by
    intro n hn
    have hsqrt : Real.sqrt n ≠ 0 := (Real.sqrt_pos.mpr
      (by exact_mod_cast (mem_Icc.mp hn).1 : (0 : ℝ) < n)).ne'
    have hu : upwardPrimeRow (atomDilate φ (c / N)) N
        (fun j => ramanujanLagCoefficient m j / Real.sqrt j) n /
          (∫ u, atomDilate φ (c / N) u ^ 2) =
        logarithmicUpwardCoefficient φ c B N m n / Real.sqrt n := by
      apply (eq_div_iff hsqrt).mpr
      simpa only [mul_comm] using sqrt_mul_upwardRamanujanRow_eq_logarithmicCoefficient_small_width
        hsupp hc0 hn hw m
    rw [actualUpwardRowError, hu]
    simp only [ha, hb, hr]; ring
  -- the logarithmic linearization, on all rows
  have hA := hlog m N hN hL1 c hc1 hw B hBN hkernel
  -- the boundary window, on the deep rows
  have hbrow : ∀ n ∈ deepRows N X, b n ^ 2 ≤
      2048 * (B : ℝ) ^ 2 * ((B : ℝ) + 1) ^ 2 * (m.totient : ℝ) ^ 2 / N := by
    intro n hn
    obtain ⟨hnI, hnX⟩ := mem_filter.mp hn
    have hn1 := (mem_Icc.mp hnI).1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hsn : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
    have hY : (N : ℝ) / n ≥ X := by rw [ge_iff_le, le_div_iff₀ hn0]; linarith
    have hYn := natDiv_ge_half hn1 (mem_Icc.mp hnI).2
    have hY2 : 2 * B + 2 ≤ N / n := by
      have h1 : (2 * (B : ℝ) + 2) < ((N / n : ℕ) : ℝ) + 1 := by
        have := Nat.lt_floor_add_one ((N : ℝ) / n)
        rw [Nat.floor_div_eq_div] at this
        linarith
      have : (2 * B + 2 : ℕ) < N / n + 1 := by exact_mod_cast h1
      omega
    have hbound := abs_linearizedUpwardCoefficient_sub_reciprocal_le hφ hsupp hM hc0
      (B := B) (by omega : 1 ≤ m) hn1 hcN
    have hmass := primeIndexBoundaryMass_le_sqrt hY2
    have hYpos : (0 : ℝ) < ((N / n : ℕ) : ℝ) := by
      have : 0 < N / n := by omega
      exact_mod_cast this
    have hsY : Real.sqrt ((N : ℝ) / n / 2) ≤ Real.sqrt ((N / n : ℕ) : ℝ) := Real.sqrt_le_sqrt hYn
    have hφ0 : (0 : ℝ) ≤ m.totient := Nat.cast_nonneg _
    have hB0 : (0 : ℝ) ≤ B := Nat.cast_nonneg B
    -- `|b n| ≤ 32 B (B + 1) φ(m) √2 / √N`
    have hb_abs : |b n| ≤ 32 * B * ((B : ℝ) + 1) * m.totient * Real.sqrt 2 / Real.sqrt N := by
      rw [hb, abs_div, abs_of_pos hsn]
      have h1 : |linearizedUpwardCoefficient φ c B N m n - reciprocalUpwardCoefficient φ c B N m n| ≤
          4 * B * m.totient * (8 * ((B : ℝ) + 1) / Real.sqrt ((N / n : ℕ) : ℝ)) :=
        hbound.trans (mul_le_mul_of_nonneg_left hmass (by positivity))
      have hsq2 : Real.sqrt ((N : ℝ) / n / 2) * Real.sqrt n * Real.sqrt 2 = Real.sqrt N := by
        rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (by positivity)]
        congr 1; field_simp
      have hsN : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN0
      have hs2 : 0 < Real.sqrt ((N : ℝ) / n / 2) := Real.sqrt_pos.mpr (by positivity)
      rw [div_le_div_iff₀ hsn hsN]
      calc |linearizedUpwardCoefficient φ c B N m n - reciprocalUpwardCoefficient φ c B N m n| *
            Real.sqrt N ≤ 4 * B * m.totient * (8 * ((B : ℝ) + 1) /
              Real.sqrt ((N / n : ℕ) : ℝ)) * Real.sqrt N :=
            mul_le_mul_of_nonneg_right h1 hsN.le
        _ ≤ 4 * B * m.totient * (8 * ((B : ℝ) + 1) / Real.sqrt ((N : ℝ) / n / 2)) *
              Real.sqrt N := by
            apply mul_le_mul_of_nonneg_right _ hsN.le
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact div_le_div_of_nonneg_left (by positivity) hs2 hsY
        _ = 32 * B * ((B : ℝ) + 1) * m.totient * Real.sqrt 2 * Real.sqrt n := by
            rw [← hsq2]; field_simp; ring
    have h2 := pow_le_pow_left₀ (abs_nonneg _) hb_abs 2
    rw [sq_abs] at h2
    refine h2.trans (le_of_eq ?_)
    rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sq_sqrt hN0.le]
    ring
  -- the shifted shell errors, on the deep rows
  have hrrow : ∀ n ∈ deepRows N X, r n ^ 2 ≤ ρ ^ 2 / n := by
    intro n hn
    obtain ⟨hnI, hnX⟩ := mem_filter.mp hn
    have hn1 := (mem_Icc.mp hnI).1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hsn : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
    obtain ⟨h1, h2⟩ := hrate n hnI hnX
    have hid : r n = (shiftedReciprocalUpwardRowError φ c id N m n +
        shiftedReciprocalUpwardRowError φ c (reflectedAffineShift m) N m n) / 2 := by
      rw [hr]
      simp only []
      rw [reciprocalUpwardCoefficient_eq_shifted_corrections hφ hsupp hc0 hB N m n hn1]
      unfold shiftedReciprocalUpwardRowError
      rw [shellCorrectionOfShift_reflected (by omega : 1 ≤ m)]
      have hsid : shellCorrectionOfShift φ c m id = shellCorrection φ c m := rfl
      rw [hsid]
      ring
    have habs : |r n| ≤ ρ / Real.sqrt n := by
      rw [hid, abs_div, abs_two]
      have := abs_add_le (shiftedReciprocalUpwardRowError φ c id N m n)
        (shiftedReciprocalUpwardRowError φ c (reflectedAffineShift m) N m n)
      linarith
    calc r n ^ 2 ≤ (ρ / Real.sqrt n) ^ 2 := by
          rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) habs 2
      _ = ρ ^ 2 / n := by rw [div_pow, Real.sq_sqrt hn0.le]
  -- assemble
  have hpt : ∀ n ∈ deepRows N X, primeHorizonExtension (normalizedUpwardPrimeResidual φ c N m) n ^ 2 ≤
      3 * (a n ^ 2 + b n ^ 2 + r n ^ 2) / Real.log N := by
    intro n hn
    have hnI := (mem_filter.mp hn).1
    rw [primeHorizonExtension_coe _ ⟨n, hnI⟩]
    change (actualUpwardRowError φ c N m n / Real.sqrt (Real.log N)) ^ 2 ≤ _
    rw [div_pow, Real.sq_sqrt hL0.le, hrow n hnI]
    apply div_le_div_of_nonneg_right _ hL0.le
    nlinarith [sq_nonneg (a n - b n), sq_nonneg (a n - r n), sq_nonneg (b n - r n)]
  unfold deepMass
  refine (sum_le_sum hpt).trans ?_
  rw [← sum_div, ← mul_sum, sum_add_distrib, sum_add_distrib]
  have hAdeep : (∑ n ∈ deepRows N X, a n ^ 2) ≤
      K * (m.totient : ℝ) ^ 2 * c ^ 4 * ((B : ℝ) + 1) ^ 6 * (Real.log N / N) ^ 2 * Real.log N := by
    have h1 : (∑ n ∈ deepRows N X, a n ^ 2) ≤ ∑ n ∈ Icc 1 N, a n ^ 2 :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => sq_nonneg _
    have h2 := (div_le_iff₀ hL0).mp hA
    exact h1.trans h2
  have hBdeep : (∑ n ∈ deepRows N X, b n ^ 2) ≤
      2048 * (B : ℝ) ^ 2 * ((B : ℝ) + 1) ^ 2 * (m.totient : ℝ) ^ 2 / X := by
    calc _ ≤ ∑ n ∈ deepRows N X, 2048 * (B : ℝ) ^ 2 * ((B : ℝ) + 1) ^ 2 * (m.totient : ℝ) ^ 2 / N :=
          sum_le_sum hbrow
      _ = ((deepRows N X).card : ℝ) * (2048 * (B : ℝ) ^ 2 * ((B : ℝ) + 1) ^ 2 *
            (m.totient : ℝ) ^ 2 / N) := by rw [sum_const, nsmul_eq_mul]
      _ ≤ (N / X) * (2048 * (B : ℝ) ^ 2 * ((B : ℝ) + 1) ^ 2 * (m.totient : ℝ) ^ 2 / N) :=
          mul_le_mul_of_nonneg_right (card_deepRows_le hX0) (by positivity)
      _ = _ := by field_simp
  have hRdeep : (∑ n ∈ deepRows N X, r n ^ 2) ≤ ρ ^ 2 * harmonic N := by
    calc _ ≤ ∑ n ∈ deepRows N X, ρ ^ 2 / n := sum_le_sum hrrow
      _ ≤ ∑ n ∈ Icc 1 N, ρ ^ 2 / n :=
          sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => by positivity
      _ = ρ ^ 2 * harmonic N := by
          rw [harmonic_eq_sum_Icc]; push_cast; rw [mul_sum]
          exact sum_congr rfl fun n _ => by rw [div_eq_mul_inv]
  have e : 3 * (K * (m.totient : ℝ) ^ 2 * c ^ 4 * ((B : ℝ) + 1) ^ 6 * (Real.log N / N) ^ 2 +
      2048 * (B : ℝ) ^ 2 * ((B : ℝ) + 1) ^ 2 * (m.totient : ℝ) ^ 2 / (X * Real.log N) +
      ρ ^ 2 * harmonic N / Real.log N) =
      3 * (K * (m.totient : ℝ) ^ 2 * c ^ 4 * ((B : ℝ) + 1) ^ 6 * (Real.log N / N) ^ 2 * Real.log N +
        2048 * (B : ℝ) ^ 2 * ((B : ℝ) + 1) ^ 2 * (m.totient : ℝ) ^ 2 / X +
        ρ ^ 2 * harmonic N) / Real.log N := by
    field_simp
  rw [e]
  apply div_le_div_of_nonneg_right _ hL0.le
  linarith

/-! ### The conductor residual on the deep rows -/

theorem deepMass_eq_zero_of_rows {N : ℕ} {X : ℝ} {v : EuclideanSpace ℝ (PrimeHorizonIndex N)}
    (h : ∀ n ∈ deepRows N X, primeHorizonExtension v n = 0) : deepMass X v = 0 := by
  unfold deepMass
  exact sum_eq_zero fun n hn => by rw [h n hn]; ring

/-- The deep-row residual budget of conductor `m`. -/
def deepResidualBudget (C_p C_s C_q K₀ K_up : ℝ) (m N : ℕ) (c X ρ : ℝ) : ℝ :=
  C_p * ((m : ℝ) * (1 + Real.log m) ^ 2) / Real.log N + C_s * (m : ℝ) * c ^ 2 / (N : ℝ) ^ 2 +
    (2 * c ^ 2 * (m : ℝ) ^ 2 * harmonic N / ((N : ℝ) ^ 2 * Real.log N) +
      18 * c ^ 2 * (m : ℝ) ^ 2 * ((harmonic N : ℝ) + 1) ^ 2 / (X ^ 2 * Real.log N)) +
    (32 * K₀ ^ 2 * (m : ℝ) * c ^ 4 / ((N : ℝ) * X * Real.log N) +
      2048 * K₀ ^ 2 * (m : ℝ) * c ^ 2 / (X ^ 2 * Real.log N)) +
    C_q * (m : ℝ) * c ^ 10 * (Real.log N / N) ^ 2 +
    3 * (K_up * (m.totient : ℝ) * c ^ 4 * ((linearPrimeStrip c : ℝ) + 1) ^ 6 * (Real.log N / N) ^ 2 +
      2048 * (linearPrimeStrip c : ℝ) ^ 2 * ((linearPrimeStrip c : ℝ) + 1) ^ 2 *
        (m.totient : ℝ) / (X * Real.log N) +
      ρ ^ 2 * harmonic N / Real.log N)

theorem harmonic_nonneg_real (N : ℕ) : (0 : ℝ) ≤ harmonic N := by
  have : (0 : ℚ) ≤ harmonic N := by unfold harmonic; positivity
  exact_mod_cast this

/-- The center channel with `α ≤ c`. -/
theorem deepMass_centerChannel_le {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2) {m N : ℕ} {c X : ℝ}
    (hm : 1 ≤ m) (hc0 : 0 < c) (hX0 : 0 < X) (hL0 : 0 < Real.log N) :
    deepMass X (Matrix.toEuclideanLin (fullWeilCenterMatrix (completeWeilPoleShift φ c) N)
        (normalizedRamanujanHorizonVector m N) -
      (if m = 1 then completeWeilPoleShift φ c else 0) • normalizedRamanujanHorizonVector m N) ≤
      2 * c ^ 2 * (m : ℝ) ^ 2 * harmonic N / ((N : ℝ) ^ 2 * Real.log N) +
        18 * c ^ 2 * (m : ℝ) ^ 2 * ((harmonic N : ℝ) + 1) ^ 2 / (X ^ 2 * Real.log N) := by
  have hα0 : 0 ≤ completeWeilPoleShift φ c := completeWeilPoleShift_nonneg φ hc0.le
  have hαc : completeWeilPoleShift φ c ≤ c :=
    completeWeilPoleShift_le hφ.continuous hsupp hM hc0.le
  have h3 := deepMass_centerResidual_le (α := completeWeilPoleShift φ c) hα0 hX0 (N := N) hm hL0
  have hα2 : completeWeilPoleShift φ c ^ 2 ≤ c ^ 2 := pow_le_pow_left₀ hα0 hαc 2
  have hH0 := harmonic_nonneg_real N
  refine h3.trans (add_le_add ?_ ?_)
  · apply div_le_div_of_nonneg_right _ (by positivity)
    have := mul_le_mul_of_nonneg_right hα2 (by positivity : (0 : ℝ) ≤ 2 * (m : ℝ) ^ 2 * harmonic N)
    linarith
  · apply div_le_div_of_nonneg_right _ (by positivity)
    have := mul_le_mul_of_nonneg_right hα2
      (by positivity : (0 : ℝ) ≤ 18 * (m : ℝ) ^ 2 * ((harmonic N : ℝ) + 1) ^ 2)
    linarith

theorem upward_channel_arith {t K B X L H ρ c Q : ℝ} (ht : 1 ≤ t) (hX : 0 < X)
    (hL : 0 < L) (hH : 0 ≤ H) :
    t⁻¹ * (3 * (K * t ^ 2 * c ^ 4 * (B + 1) ^ 6 * Q + 2048 * B ^ 2 * (B + 1) ^ 2 * t ^ 2 / (X * L) +
      ρ ^ 2 * H / L)) ≤
    3 * (K * t * c ^ 4 * (B + 1) ^ 6 * Q + 2048 * B ^ 2 * (B + 1) ^ 2 * t / (X * L) +
      ρ ^ 2 * H / L) := by
  have ht0 : 0 < t := by linarith
  have h0 : 0 ≤ ρ ^ 2 * H / L := by positivity
  have hti : t⁻¹ ≤ 1 := inv_le_one_of_one_le₀ ht
  have e : t⁻¹ * (3 * (K * t ^ 2 * c ^ 4 * (B + 1) ^ 6 * Q + 2048 * B ^ 2 * (B + 1) ^ 2 * t ^ 2 /
      (X * L) + ρ ^ 2 * H / L)) = 3 * (K * t * c ^ 4 * (B + 1) ^ 6 * Q +
      2048 * B ^ 2 * (B + 1) ^ 2 * t / (X * L) + t⁻¹ * (ρ ^ 2 * H / L)) := by
    field_simp
  rw [e]
  have := mul_le_mul_of_nonneg_right hti h0
  linarith

/-- The upward channel through its affine shell rate. -/
theorem deepMass_upwardChannel_le {φ : ℝ → ℝ} {K_up : ℝ} {m N : ℕ} {c X ρ : ℝ}
    (hm : 0 < m) (hX0 : 0 < X) (hL0 : 0 < Real.log N)
    (hu : deepMass X (normalizedUpwardPrimeResidual φ c N m) ≤
        3 * (K_up * (m.totient : ℝ) ^ 2 * c ^ 4 * ((linearPrimeStrip c : ℝ) + 1) ^ 6 *
            (Real.log N / N) ^ 2 +
          2048 * (linearPrimeStrip c : ℝ) ^ 2 * ((linearPrimeStrip c : ℝ) + 1) ^ 2 *
            (m.totient : ℝ) ^ 2 / (X * Real.log N) +
          ρ ^ 2 * harmonic N / Real.log N)) :
    deepMass X (upwardPrimeVector φ c N (normalizedRamanujanHorizonVector m N) -
      shellCorrection φ c m • normalizedRamanujanHorizonVector m N) ≤
      3 * (K_up * (m.totient : ℝ) * c ^ 4 * ((linearPrimeStrip c : ℝ) + 1) ^ 6 * (Real.log N / N) ^ 2 +
        2048 * (linearPrimeStrip c : ℝ) ^ 2 * ((linearPrimeStrip c : ℝ) + 1) ^ 2 *
          (m.totient : ℝ) / (X * Real.log N) +
        ρ ^ 2 * harmonic N / Real.log N) := by
  rw [upwardPrimeVector_ramanujan_residual_eq φ c N hm, deepMass_smul, inv_pow,
    Real.sq_sqrt (Nat.cast_nonneg _)]
  have htot : (1 : ℝ) ≤ m.totient := by exact_mod_cast Nat.totient_pos.mpr hm
  refine (mul_le_mul_of_nonneg_left hu (by positivity)).trans ?_
  exact upward_channel_arith htot hX0 hL0 (harmonic_nonneg_real N)

/-- **The conductor residual on the deep rows.** On the rows `nX ≤ N`, `X > 2ce²`, the residual
`r_m = W v_m − E_m v_m` keeps only its prime part (`O(m(1 + log m)²/log N)`, independent of `c`);
all other channels are either zero there (near Gamma, near center) or carry inverse powers of
`X` or `N`, the upward one up to its shifted affine shell errors `≤ ρ/√n`. -/
theorem exists_deepMass_conductorResidual_le {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2) :
    ∃ C_p C_s C_q K_up : ℝ, 0 ≤ C_p ∧ 0 ≤ C_s ∧ 0 ≤ C_q ∧ 0 ≤ K_up ∧
      ∀ {m N : ℕ} {c X ρ : ℝ}, 0 < m → 1 ≤ N → 1 ≤ Real.log N → 1 ≤ c → c / N ≤ 1 →
      2 * ((Real.exp 1 + 3) * c) * linearPrimeStrip c ≤ (N : ℝ) →
      2 * (linearPrimeStrip c : ℝ) + 3 ≤ X → linearNearRowRadius c < X → 2 * c < X →
      (∀ n ∈ Icc 1 N, (n : ℝ) * X ≤ N →
        |shiftedReciprocalUpwardRowError φ c id N m n| ≤ ρ / Real.sqrt n ∧
        |shiftedReciprocalUpwardRowError φ c (reflectedAffineShift m) N m n| ≤ ρ / Real.sqrt n) →
      deepMass X (Matrix.toEuclideanLin (completeWeilMatrix φ c N) (normalizedRamanujanHorizonVector m N) -
          completedConductorEnergy φ c m • normalizedRamanujanHorizonVector m N) ≤
        8 * deepResidualBudget C_p C_s C_q (152 * (∫ u, |φ u|) ^ 2 / (∫ u, φ u ^ 2)) K_up m N c X ρ := by
  obtain ⟨C_p, hCp, hp⟩ := exists_primeResidual_quad_bound
  obtain ⟨C_s, hCs, hs⟩ := exists_selfError_quad_bound hφ hsupp hM
  obtain ⟨C_q, hCq, hq⟩ := exists_poleError_quadratic_conductor_bound hφ hsupp hM
  obtain ⟨K_up, hKup, hup⟩ := exists_deepMass_upwardResidual_le hφ hsupp hM
  refine ⟨C_p, C_s, C_q, K_up, hCp.le, hCs.le, hCq, hKup, ?_⟩
  intro m N c X ρ hm hN hL1 hc1 hw hkernel hXB hXR hX2 hrate
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hL0 : 0 < Real.log N := zero_lt_one.trans_le hL1
  have hcN : c ≤ N := (div_le_one hN0).mp hw
  have hX0 : 0 < X := by linarith
  rw [completeWeilMatrix_ramanujan_residual_eq_at_every_overlap hφ hsupp hM hc0 hN hm]
  refine (deepMass_eight_le X _ _ _ _ _ _ _ _).trans ?_
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  have h1 := (deepMass_le_norm_sq X _).trans (hp m hm N)
  have h2 := (deepMass_le_norm_sq X _).trans (hs m hm N hN hL1 c hc0 hcN)
  have h3 := deepMass_centerChannel_le hφ hsupp hM (N := N) hm hc0 hX0 hL0
  have h4 := deepMass_separated_le hφ hsupp hM hm hc1 hX0 (N := N) hL0
  have h5 := (deepMass_le_norm_sq X _).trans (hq m hm c hc1 N hN hL1 hcN)
  have h6 : deepMass X ((Real.sqrt (m.totient : ℝ))⁻¹ • normalizedFullNearGammaDownwardVector φ c N m) = 0 := by
    rw [deepMass_smul, deepMass_eq_zero_of_rows fun n hn =>
      primeHorizonExtension_nearGammaDownward_deep hφ hsupp m hc0 hN hw hXR hX2 hn, mul_zero]
  have h7 : deepMass X (nearCenterVector φ c N m) = 0 :=
    deepMass_eq_zero_of_rows fun n hn => primeHorizonExtension_nearCenterVector_deep φ m hc0 hw hXR hn
  have h8 := deepMass_upwardChannel_le (φ := φ) (c := c) hm hX0 hL0
    (hup hm hN hL1 hc1 hw hkernel hXB hrate)
  unfold deepResidualBudget
  linarith only [h1, h2, h3, h4, h5, h6, h7, h8]

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
