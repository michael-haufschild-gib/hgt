import GaloisForLFunctions.RHTower.MertensSquareRootOmega
import GaloisForLFunctions.RHTower.Deninger.DeningerHarmonicPartial
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic


/-!
# The moving square cutoff in the triangular Liouville sum

Write `W(y) = Σ_{k ≤ √y} (y/k² - 1)` and
`A(U) = Σ_{m ≤ U} μ(m) W(U²/m)`. The short head obeys
`A(U) - ζ(2) U² Σ_{m ≤ U} μ(m)/m = o(U √U)`, but `A(U)` itself is not `o(U √U)`.

The bounded lattice remainder in `W(y) = ζ(2)y - 2√y + O(1)` and the prime number
theorem give the asymptotic identity. Inverse Abel summation and the unconditional
square-root oscillation of the Mertens function give the obstruction. Thus the
linear short head in a quadratic-cutoff reconstruction cannot be paid separately
by an absolute estimate at every half-plus-epsilon exponent in `x = U²`.
-/

open Filter Topology Asymptotics Finset
noncomputable section
namespace RHTower.LiouvilleTriangularShortHead

private def rootStep (n : ℕ) : ℝ := Real.sqrt (n + 1) - Real.sqrt n

private theorem rootStep_nonneg (n : ℕ) : 0 ≤ rootStep n := by
  exact sub_nonneg.mpr (Real.sqrt_le_sqrt (by linarith))

private theorem rootStep_mul (n : ℕ) :
    rootStep n * (Real.sqrt (n + 1) + Real.sqrt n) = 1 := by
  unfold rootStep
  nlinarith [Real.sq_sqrt (show 0 ≤ (n : ℝ) + 1 by positivity),
    Real.sq_sqrt (show 0 ≤ (n : ℝ) by positivity)]

private theorem inv_sqrt_le_step {n : ℕ} (hn : 1 ≤ n) :
    (Real.sqrt n)⁻¹ ≤ 3 * rootStep n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hs := Real.sqrt_pos.mpr hn0
  have hs1 := Real.sqrt_nonneg ((n : ℝ) + 1)
  have hle : Real.sqrt (n + 1) ≤ 2 * Real.sqrt n := by
    nlinarith [Real.sq_sqrt hn0.le,
      Real.sq_sqrt (show 0 ≤ (n : ℝ) + 1 by positivity),
      show (1 : ℝ) ≤ n by exact_mod_cast hn]
  rw [inv_eq_one_div, div_le_iff₀ hs]
  have h := mul_le_mul_of_nonneg_left (show Real.sqrt (n + 1) + Real.sqrt n ≤
      3 * Real.sqrt n by linarith) (rootStep_nonneg n)
  rw [rootStep_mul] at h
  nlinarith

private theorem sum_rootStep (N : ℕ) :
    ∑ n ∈ range N, rootStep n = Real.sqrt N := by
  simpa [rootStep] using sum_range_sub (fun n : ℕ => Real.sqrt n) N

private theorem inv_sqrt_isBigO_step :
    (fun n : ℕ => (Real.sqrt n)⁻¹) =O[atTop] rootStep := by
  refine IsBigO.of_bound 3 ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  simpa only [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)),
    abs_of_nonneg (rootStep_nonneg _)] using inv_sqrt_le_step hn

private theorem littleO_inv_sqrt_sum {f : ℕ → ℝ}
    (hf : f =o[atTop] fun n : ℕ => (Real.sqrt n)⁻¹) :
    (fun N => ∑ n ∈ range N, f n) =o[atTop] fun N : ℕ => Real.sqrt N := by
  have h := (hf.trans_isBigO inv_sqrt_isBigO_step).sum_range rootStep_nonneg
    (by simpa only [sum_rootStep, Function.comp_def] using
      Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ)))
  simpa only [sum_rootStep] using h

private theorem abel (a w : ℕ → ℝ) (N : ℕ) :
    ∑ n ∈ range N, a n * w n =
      (∑ n ∈ range N, a n) * w N +
      ∑ n ∈ range N, (∑ k ∈ range (n + 1), a k) * (w n - w (n + 1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    simp only [Finset.sum_range_succ] at ih ⊢
    rw [ih]
    ring

private theorem weighted_sqrt_step (n : ℕ) :
    0 ≤ (n + 1 : ℝ) * ((Real.sqrt (n + 1))⁻¹ - (Real.sqrt (n + 2))⁻¹) ∧
    (n + 1 : ℝ) * ((Real.sqrt (n + 1))⁻¹ - (Real.sqrt (n + 2))⁻¹) ≤
      rootStep (n + 1) := by
  have h1 : 0 < Real.sqrt (n + 1) := Real.sqrt_pos.mpr (by positivity)
  have h2 : 0 < Real.sqrt (n + 2) := Real.sqrt_pos.mpr (by positivity)
  have h12 : Real.sqrt (n + 1) ≤ Real.sqrt (n + 2) :=
    Real.sqrt_le_sqrt (by linarith)
  have heq : (n + 1 : ℝ) * ((Real.sqrt (n + 1))⁻¹ - (Real.sqrt (n + 2))⁻¹) =
      (Real.sqrt (n + 2) - Real.sqrt (n + 1)) *
        (Real.sqrt (n + 1) / Real.sqrt (n + 2)) := by
    field_simp
    nlinarith [Real.sq_sqrt (show 0 ≤ (n : ℝ) + 1 by positivity)]
  rw [heq]
  have hr : 0 ≤ Real.sqrt (n + 1) / Real.sqrt (n + 2) := by positivity
  have hr1 : Real.sqrt (n + 1) / Real.sqrt (n + 2) ≤ 1 := (div_le_one h2).mpr h12
  constructor
  · exact mul_nonneg (sub_nonneg.mpr h12) hr
  · simpa only [rootStep, Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using
      mul_le_of_le_one_right (sub_nonneg.mpr h12) hr1

private theorem sum_rootStep_succ (N : ℕ) :
    ∑ n ∈ range N, rootStep (n + 1) = Real.sqrt (N + 1) - 1 := by
  simpa [rootStep, Nat.cast_add, Nat.cast_one, add_assoc] using
    sum_range_sub (fun n : ℕ => Real.sqrt (n + 1)) N

private theorem rootStep_sum_succ_isBigO :
    (fun N => ∑ n ∈ range N, rootStep (n + 1)) =O[atTop]
      fun N : ℕ => Real.sqrt N := by
  refine IsBigO.of_bound 1 (Filter.Eventually.of_forall fun N => ?_)
  rw [sum_rootStep_succ, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), one_mul,
    abs_of_nonneg (by
      have := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ N + 1 by linarith [Nat.cast_nonneg (α := ℝ) N])
      simpa only [Real.sqrt_one] using sub_nonneg.mpr this)]
  have h := Real.sqrt_nonneg (N : ℝ)
  have h1 := Real.sqrt_nonneg ((N : ℝ) + 1)
  nlinarith [Real.sq_sqrt (show 0 ≤ (N : ℝ) by positivity),
    Real.sq_sqrt (show 0 ≤ (N : ℝ) + 1 by positivity)]

private theorem weighted_sqrt_littleO {a : ℕ → ℝ}
    (hM : (fun N => ∑ n ∈ range N, a n) =o[atTop] fun N : ℕ => (N : ℝ)) :
    (fun N => ∑ n ∈ range N, a n / Real.sqrt (n + 1)) =o[atTop]
      fun N : ℕ => Real.sqrt N := by
  let M := fun N => ∑ n ∈ range N, a n
  let D := fun n : ℕ => (Real.sqrt (n + 1))⁻¹ - (Real.sqrt (n + 2))⁻¹
  have hD (n : ℕ) : 0 ≤ D n := by
    dsimp [D]
    exact sub_nonneg.mpr (inv_anti₀ (Real.sqrt_pos.mpr (by positivity))
      (Real.sqrt_le_sqrt (by linarith)))
  have hterm : (fun n => M (n + 1) * D n) =o[atTop] fun n => rootStep (n + 1) := by
    refine isLittleO_iff.mpr fun eps heps => ?_
    filter_upwards [(hM.comp_tendsto (tendsto_add_atTop_nat 1)).bound heps] with n hn
    simp only [Function.comp_def, Real.norm_eq_abs, Nat.cast_add, Nat.cast_one,
      abs_of_nonneg (show 0 ≤ (n : ℝ) + 1 by positivity)] at hn
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hD n),
      Real.norm_eq_abs, abs_of_nonneg (rootStep_nonneg _)]
    calc
      |M (n + 1)| * D n ≤ (eps * (n + 1)) * D n :=
        mul_le_mul_of_nonneg_right hn (hD n)
      _ = eps * ((n + 1) * D n) := by ring
      _ ≤ eps * rootStep (n + 1) :=
        mul_le_mul_of_nonneg_left (weighted_sqrt_step n).2 heps.le
  have hsum := (hterm.sum_range (fun n => rootStep_nonneg (n + 1))
    (by
      simp only [sum_rootStep_succ]
      simpa only [Function.comp_def, sub_eq_add_neg] using
        (Real.tendsto_sqrt_atTop.comp
          ((tendsto_natCast_atTop_atTop (R := ℝ)).atTop_add
            (show Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) from tendsto_const_nhds))).atTop_add
          (show Tendsto (fun _ : ℕ => (-1 : ℝ)) atTop (𝓝 (-1)) from tendsto_const_nhds))).trans_isBigO rootStep_sum_succ_isBigO
  have hboundary : (fun N => M N / Real.sqrt (N + 1)) =o[atTop]
      fun N : ℕ => Real.sqrt N := by
    refine isLittleO_iff.mpr fun eps heps => ?_
    filter_upwards [hM.bound heps] with N hN
    simp only [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) N)] at hN
    rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (Real.sqrt_nonneg _),
      Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    have hpos : 0 < Real.sqrt (N + 1) := Real.sqrt_pos.mpr (by positivity)
    have hle : (N : ℝ) ≤ Real.sqrt N * Real.sqrt (N + 1) := by
      calc
        (N : ℝ) = Real.sqrt N * Real.sqrt N := (Real.mul_self_sqrt (by positivity)).symm
        _ ≤ Real.sqrt N * Real.sqrt (N + 1) :=
          mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by linarith)) (Real.sqrt_nonneg _)
    apply (div_le_iff₀ hpos).mpr
    exact hN.trans (by nlinarith)
  refine (hboundary.add hsum).congr_left fun N => ?_
  symm
  simpa only [div_eq_mul_inv, M, D, Nat.cast_add, Nat.cast_one,
    add_assoc, one_add_one_eq_two] using abel a (fun n => (Real.sqrt (n + 1))⁻¹) N

private theorem inverse_abel (a : ℕ → ℝ) (N : ℕ) :
    ∑ n ∈ range N, a n =
      (N : ℝ) * (∑ n ∈ range N, a n / (n + 1)) -
      ∑ k ∈ range N, (∑ n ∈ range k, a n / (n + 1)) := by
  let H := fun k => ∑ n ∈ range k, a n / (n + 1)
  have h := abel (fun n => a n / (n + 1)) (fun n => (n : ℝ) + 1) N
  have hleft : ∑ n ∈ range N, (a n / (n + 1)) * (n + 1) = ∑ n ∈ range N, a n := by
    apply sum_congr rfl
    intro n _
    exact div_mul_cancel₀ _ (by positivity)
  have hsum : ∑ n ∈ range N, H (n + 1) = (∑ n ∈ range N, H n) + H N := by
    have h0 : H 0 = 0 := by simp [H]
    have hs := Finset.sum_range_succ' H N
    rw [h0, add_zero, Finset.sum_range_succ] at hs
    exact hs.symm
  have hdiff (n : ℕ) : (n : ℝ) + 1 - ((n + 1 : ℕ) + 1 : ℝ) = -1 := by push_cast; ring
  rw [hleft] at h
  simp only [hdiff, mul_neg_one, sum_neg_distrib] at h
  change (∑ n ∈ range N, a n) = H N * ((N : ℝ) + 1) - ∑ n ∈ range N, H (n + 1) at h
  rw [hsum] at h
  change (∑ n ∈ range N, a n) = (N : ℝ) * H N - ∑ n ∈ range N, H n
  linarith

private theorem harmonic_littleO_imp {a : ℕ → ℝ}
    (hH : (fun N => ∑ n ∈ range N, a n / (n + 1)) =o[atTop]
      fun N : ℕ => (Real.sqrt N)⁻¹) :
    (fun N => ∑ n ∈ range N, a n) =o[atTop] fun N : ℕ => Real.sqrt N := by
  have hb := hH.mul_isBigO (isBigO_refl (fun N : ℕ => (N : ℝ)) atTop)
  have heq (N : ℕ) : (Real.sqrt N)⁻¹ * (N : ℝ) = Real.sqrt N := by
    calc
      (Real.sqrt N)⁻¹ * (N : ℝ) = (Real.sqrt N)⁻¹ * (Real.sqrt N * Real.sqrt N) := by
        rw [Real.mul_self_sqrt (show 0 ≤ (N : ℝ) by positivity)]
      _ = Real.sqrt N := by
        by_cases h : Real.sqrt N = 0
        · rw [h]; simp
        · field_simp
  have hb' : (fun N : ℕ => (N : ℝ) * (∑ n ∈ range N, a n / (n + 1))) =o[atTop]
      fun N : ℕ => Real.sqrt N := by
    exact hb.congr (fun N => mul_comm _ _) heq
  exact (hb'.sub (littleO_inv_sqrt_sum hH)).congr_left fun N => (inverse_abel a N).symm

private theorem reciprocal_differences_hasSum {q : ℝ} (hq : 0 < q) :
    HasSum (fun n : ℕ => ((n : ℝ) + q)⁻¹ - ((n : ℝ) + q + 1)⁻¹) q⁻¹ := by
  apply (hasSum_iff_tendsto_nat_of_nonneg (fun n =>
    sub_nonneg.mpr (inv_anti₀ (by positivity) (by linarith))) _).mpr
  have heq (N : ℕ) :
      ∑ n ∈ range N, (((n : ℝ) + q)⁻¹ - ((n : ℝ) + q + 1)⁻¹) =
        q⁻¹ - ((N : ℝ) + q)⁻¹ := by
    simpa [Nat.cast_add, Nat.cast_one, add_right_comm, add_comm, add_assoc] using
      sum_range_sub' (fun n : ℕ => ((n : ℝ) + q)⁻¹) N
  simp only [heq]
  have ht : Tendsto (fun N : ℕ => ((N : ℝ) + q)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp
      (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  simpa using tendsto_const_nhds.sub ht

/-- The reciprocal-square mass of the positive integers. -/
def squareMass : ℝ := ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 2

private theorem squareSeries_summable : Summable fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2 := by
  simpa only [Nat.cast_add, Nat.cast_one] using
    ((summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by omega : 1 < 2)))

private theorem squareTail_bounds {q : ℕ} (hq : 1 ≤ q) :
    ((q : ℝ) + 1)⁻¹ ≤ squareMass - ∑ n ∈ range q, 1 / ((n : ℝ) + 1)^2 ∧
    squareMass - ∑ n ∈ range q, 1 / ((n : ℝ) + 1)^2 ≤ (q : ℝ)⁻¹ := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hs : Summable fun n : ℕ => 1 / ((n : ℝ) + q + 1)^2 := by
    simpa only [Nat.cast_add] using (summable_nat_add_iff q).mpr squareSeries_summable
  have hid : squareMass - ∑ n ∈ range q, 1 / ((n : ℝ) + 1)^2 =
      ∑' n : ℕ, 1 / ((n : ℝ) + q + 1)^2 := by
    have h := squareSeries_summable.sum_add_tsum_nat_add q
    simp only [Nat.cast_add] at h
    unfold squareMass
    linarith
  rw [hid]
  have hl := reciprocal_differences_hasSum (show 0 < (q : ℝ) + 1 by positivity)
  have hu := reciprocal_differences_hasSum hq0
  constructor
  · rw [← hl.tsum_eq]
    apply Summable.tsum_le_tsum _ hl.summable hs
    intro n
    have h1 : 0 < (n : ℝ) + q + 1 := by positivity
    have h2 : 0 < (n : ℝ) + q + 1 + 1 := by positivity
    simp only [← add_assoc]
    field_simp
    nlinarith
  · rw [← hu.tsum_eq]
    apply Summable.tsum_le_tsum _ hs hu.summable
    intro n
    have h1 : 0 < (n : ℝ) + q := by positivity
    have h2 : 0 < (n : ℝ) + q + 1 := by positivity
    field_simp
    nlinarith

/-- The triangular transform of the square indicator. -/
def squareTriangle (y : ℝ) : ℝ :=
  ∑ n ∈ range ⌊Real.sqrt y⌋₊, (y / ((n : ℝ) + 1)^2 - 1)

private theorem squareTriangle_eq (y : ℝ) :
    squareTriangle y = y * (∑ n ∈ range ⌊Real.sqrt y⌋₊, 1 / ((n : ℝ) + 1)^2) -
      (⌊Real.sqrt y⌋₊ : ℝ) := by
  simp only [squareTriangle, sum_sub_distrib, sum_const, card_range, nsmul_eq_mul, mul_one,
    mul_sum, mul_one_div]

/-- The full square tail leaves a uniformly bounded triangular remainder. -/
theorem squareTriangle_remainder {y : ℝ} (hy : 1 ≤ y) :
    |squareTriangle y - squareMass * y + 2 * Real.sqrt y| ≤ 1 := by
  let q := ⌊Real.sqrt y⌋₊
  have hy0 : 0 ≤ y := by linarith
  have hq1 : 1 ≤ q := Nat.le_floor (by
    have := Real.sqrt_le_sqrt hy
    simpa only [Real.sqrt_one, Nat.cast_one] using this)
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  have hq0 : (0 : ℝ) < q := by linarith
  have hqlo : (q : ℝ) ≤ Real.sqrt y := Nat.floor_le (Real.sqrt_nonneg _)
  have hqhi : Real.sqrt y < (q : ℝ) + 1 := Nat.lt_floor_add_one _
  have hsq := Real.sq_sqrt hy0
  have htail := squareTail_bounds hq1
  have hupper := mul_le_mul_of_nonneg_left htail.2 hy0
  have hlower := mul_le_mul_of_nonneg_left htail.1 hy0
  simp only [← div_eq_mul_inv] at hupper hlower
  have hu : y / q + q - 2 * Real.sqrt y ≤ 1 := by
    have he : (Real.sqrt y - q)^2 ≤ 1 := by nlinarith
    have hh : y ≤ (1 - q + 2 * Real.sqrt y) * q := by nlinarith
    have := (div_le_iff₀ hq0).mpr hh
    linarith
  have hl : -1 ≤ y / ((q : ℝ) + 1) + q - 2 * Real.sqrt y := by
    have hh : (-1 - q + 2 * Real.sqrt y) * (q + 1) ≤ y := by
      nlinarith [sq_nonneg (Real.sqrt y - (q + 1))]
    have := (le_div_iff₀ (show 0 < (q : ℝ) + 1 by positivity)).mpr hh
    linarith
  rw [squareTriangle_eq, abs_le]
  change -1 ≤ y * (∑ n ∈ range q, 1 / ((n : ℝ) + 1)^2) - q - squareMass * y +
      2 * Real.sqrt y ∧
    y * (∑ n ∈ range q, 1 / ((n : ℝ) + 1)^2) - q - squareMass * y +
      2 * Real.sqrt y ≤ 1
  constructor <;> nlinarith

private theorem squareMass_pos : 0 < squareMass := by
  have h := (squareTail_bounds (q := 1) le_rfl).1
  norm_num at h
  linarith

/-- Short square-indicator term at the moving quadratic cutoff. -/
private def shortHead (a : ℕ → ℝ) (U : ℕ) : ℝ :=
  ∑ n ∈ range U, a n * squareTriangle ((U : ℝ)^2 / (n + 1))

/-- Exact first-order expansion of the actual short source, with bounded lattice remainder. -/
private theorem shortHead_remainder {a : ℕ → ℝ} (ha : ∀ n, |a n| ≤ 1)
    (U : ℕ) :
    |shortHead a U - squareMass * (U : ℝ)^2 * (∑ n ∈ range U, a n / (n + 1)) +
      2 * U * (∑ n ∈ range U, a n / Real.sqrt (n + 1))| ≤ (U : ℝ) := by
  have heq : shortHead a U - squareMass * (U : ℝ)^2 * (∑ n ∈ range U, a n / (n + 1)) +
      2 * U * (∑ n ∈ range U, a n / Real.sqrt (n + 1)) =
      ∑ n ∈ range U, a n * (squareTriangle ((U : ℝ)^2 / (n + 1)) -
        squareMass * ((U : ℝ)^2 / (n + 1)) + 2 * Real.sqrt ((U : ℝ)^2 / (n + 1))) := by
    simp only [shortHead, mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
    apply sum_congr rfl
    intro n _
    rw [Real.sqrt_div (sq_nonneg _), Real.sqrt_sq (Nat.cast_nonneg _)]
    ring
  rw [heq]
  calc
    _ ≤ ∑ n ∈ range U, |a n * (squareTriangle ((U : ℝ)^2 / (n + 1)) -
        squareMass * ((U : ℝ)^2 / (n + 1)) + 2 * Real.sqrt ((U : ℝ)^2 / (n + 1)))| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ range U, (1 : ℝ) := by
      apply sum_le_sum
      intro n hn
      have hnU : (n : ℝ) + 1 ≤ U := by exact_mod_cast Nat.add_one_le_iff.mpr (mem_range.mp hn)
      have hU : (1 : ℝ) ≤ U := le_trans (by linarith [Nat.cast_nonneg (α := ℝ) n]) hnU
      have hy : 1 ≤ (U : ℝ)^2 / (n + 1) := by
        apply (le_div_iff₀ (show 0 < (n : ℝ) + 1 by positivity)).mpr
        nlinarith
      rw [abs_mul]
      exact (mul_le_mul (ha n) (squareTriangle_remainder hy) (abs_nonneg _) zero_le_one).trans_eq
        (one_mul 1)
    _ = U := by simp

private theorem nat_littleO_threeHalves :
    (fun N : ℕ => (N : ℝ)) =o[atTop] fun N : ℕ => (N : ℝ) * Real.sqrt N := by
  have hs : (fun _ : ℕ => (1 : ℝ)) =o[atTop] fun N : ℕ => Real.sqrt N := by
    apply isLittleO_const_left.mpr (Or.inr ?_)
    simpa only [Function.comp_def, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)] using
      Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have h := hs.mul_isBigO (isBigO_refl (fun N : ℕ => (N : ℝ)) atTop)
  simpa only [one_mul, mul_one, mul_comm] using h

private theorem shortHead_asymptotic {a : ℕ → ℝ} (ha : ∀ n, |a n| ≤ 1)
    (hM : (fun N => ∑ n ∈ range N, a n) =o[atTop] fun N : ℕ => (N : ℝ)) :
    (fun U : ℕ => shortHead a U - squareMass * (U : ℝ)^2 *
      (∑ n ∈ range U, a n / (n + 1))) =o[atTop]
      fun U : ℕ => (U : ℝ) * Real.sqrt U := by
  have herror : (fun U : ℕ => shortHead a U - squareMass * (U : ℝ)^2 *
      (∑ n ∈ range U, a n / (n + 1)) +
      2 * U * (∑ n ∈ range U, a n / Real.sqrt (n + 1))) =O[atTop]
      fun U : ℕ => (U : ℝ) := by
    refine IsBigO.of_bound 1 (Filter.Eventually.of_forall fun U => ?_)
    simpa only [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) U), one_mul] using
      shortHead_remainder ha U
  have hcor := ((weighted_sqrt_littleO hM).mul_isBigO
    (isBigO_refl (fun U : ℕ => (U : ℝ)) atTop)).const_mul_left 2
  have hcor' : (fun U : ℕ => 2 * U * (∑ n ∈ range U, a n / Real.sqrt (n + 1))) =o[atTop]
      fun U : ℕ => (U : ℝ) * Real.sqrt U := by
    exact hcor.congr (fun U => by ring) (fun U => mul_comm _ _)
  exact ((herror.trans_isLittleO nat_littleO_threeHalves).sub hcor').congr_left
    fun U => by ring

private theorem shortHead_littleO_imp_harmonic {a : ℕ → ℝ} (ha : ∀ n, |a n| ≤ 1)
    (hM : (fun N => ∑ n ∈ range N, a n) =o[atTop] fun N : ℕ => (N : ℝ))
    (hA : shortHead a =o[atTop] fun U : ℕ => (U : ℝ) * Real.sqrt U) :
    (fun U => ∑ n ∈ range U, a n / (n + 1)) =o[atTop]
      fun U : ℕ => (Real.sqrt U)⁻¹ := by
  have h := hA.sub (shortHead_asymptotic ha hM)
  have hmain : (fun U : ℕ => squareMass * (U : ℝ)^2 *
      (∑ n ∈ range U, a n / (n + 1))) =o[atTop]
      fun U : ℕ => (U : ℝ) * Real.sqrt U :=
    h.congr_left fun U => by ring
  refine isLittleO_iff.mpr fun eps heps => ?_
  filter_upwards [hmain.bound (mul_pos heps squareMass_pos), eventually_ge_atTop 1] with U hU hpos
  have hUr : (0 : ℝ) < U := by exact_mod_cast hpos
  have hs : 0 < Real.sqrt U := Real.sqrt_pos.mpr hUr
  simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg squareMass_pos.le,
    abs_of_nonneg (sq_nonneg (U : ℝ)), abs_of_pos hUr, abs_of_pos hs] at hU
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hs.le)]
  have h1 : |∑ n ∈ range U, a n / (n + 1)| * Real.sqrt U ≤ eps := by
    have hzpos := squareMass_pos
    apply (mul_le_mul_iff_right₀
      (show 0 < squareMass * (U : ℝ) * Real.sqrt U by positivity)).mp
    calc
      (squareMass * (U : ℝ) * Real.sqrt U) *
          (|∑ n ∈ range U, a n / (n + 1)| * Real.sqrt U) =
          squareMass * (U : ℝ)^2 * |∑ n ∈ range U, a n / (n + 1)| := by
        calc
          _ = squareMass * (U : ℝ) * |∑ n ∈ range U, a n / (n + 1)| * (Real.sqrt U)^2 := by ring
          _ = _ := by rw [Real.sq_sqrt hUr.le]; ring
      _ ≤ (squareMass * (U : ℝ) * Real.sqrt U) * eps := by nlinarith only [hU]
  simpa only [div_eq_mul_inv] using (le_div_iff₀ hs).mpr h1

private def mobiusCoefficient (n : ℕ) : ℝ :=
  ((ArithmeticFunction.moebius (n + 1) : ℤ) : ℝ)

private theorem mobiusCoefficient_bound (n : ℕ) : |mobiusCoefficient n| ≤ 1 := by
  unfold mobiusCoefficient
  rw [← Int.cast_abs]
  exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n + 1)

private theorem mobius_prefix_eq (N : ℕ) :
    (∑ n ∈ range N, mobiusCoefficient n) = RHTower.Sieve.mertensM N := by
  simp [RHTower.Sieve.mertensM, Finset.sum_range_succ', mobiusCoefficient]

private theorem mobius_harmonic_eq (N : ℕ) :
    (∑ n ∈ range N, mobiusCoefficient n / (n + 1)) = RHTower.deningerHarmonicPartial N := by
  simp [RHTower.deningerHarmonicPartial, Finset.sum_range_succ', mobiusCoefficient]

private theorem mobius_prefix_littleO :
    (fun N => ∑ n ∈ range N, mobiusCoefficient n) =o[atTop]
      fun N : ℕ => (N : ℝ) := by
  have h : (fun N => |RHTower.Sieve.mertensM N|) =o[atTop] fun N : ℕ => (N : ℝ) := by
    apply (isLittleO_iff_tendsto (fun N hN => ?_)).mpr RHTower.Sieve.tendsto_abs_mertensM_div
    have hN0 : N = 0 := by exact_mod_cast hN
    subst N
    simp [RHTower.Sieve.mertensM]
  exact (isLittleO_abs_left.mp h).congr_left fun N => (mobius_prefix_eq N).symm

private theorem mertens_real_prefix (x : ℝ) :
    RHTower.mertensFunctionReal x = ∑ n ∈ range ⌊x⌋₊, mobiusCoefficient n := by
  unfold RHTower.mertensFunctionReal
  have heq (N : ℕ) : (∑ n ∈ Icc 1 N, ((ArithmeticFunction.moebius n : ℤ) : ℝ)) =
      ∑ n ∈ range N, mobiusCoefficient n := by
    induction N with
    | zero => simp
    | succ N ih =>
      rw [sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]
      rfl
  exact heq _

/-- The actual harmonic Möbius prefixes do not decay faster than the inverse square root. -/
theorem not_harmonic_isLittleO_inv_sqrt :
    ¬ RHTower.deningerHarmonicPartial =o[atTop] fun N : ℕ => (Real.sqrt N)⁻¹ := by
  intro h
  have hH : (fun N => ∑ n ∈ range N, mobiusCoefficient n / (n + 1)) =o[atTop]
      fun N : ℕ => (Real.sqrt N)⁻¹ := h.congr_left fun N => (mobius_harmonic_eq N).symm
  have hM := harmonic_littleO_imp hH
  have hfloor : Tendsto (fun x : ℝ => ⌊x⌋₊) atTop atTop := by
    apply tendsto_atTop.mpr
    intro N
    filter_upwards [eventually_ge_atTop (N : ℝ)] with x hx
    exact Nat.le_floor hx
  have hsqrt : (fun x : ℝ => Real.sqrt ⌊x⌋₊) =O[atTop] fun x : ℝ => Real.sqrt x := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    simp only [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), one_mul]
    exact Real.sqrt_le_sqrt (Nat.floor_le hx)
  apply RHTower.not_mertensFunctionReal_isLittleO_sqrt
  exact ((hM.comp_tendsto hfloor).trans_isBigO hsqrt).congr_left
    fun x => (mertens_real_prefix x).symm

/-- The first short term in the triangular Liouville reconstruction at `x = U²`. -/
def mobiusShortHead (U : ℕ) : ℝ := shortHead mobiusCoefficient U

/-- At the three-quarter scale in `x`, the short head retains the moving harmonic prefix. -/
theorem mobiusShortHead_asymptotic :
    (fun U : ℕ => mobiusShortHead U - squareMass * (U : ℝ)^2 *
      RHTower.deningerHarmonicPartial U) =o[atTop]
      fun U : ℕ => (U : ℝ) * Real.sqrt U := by
  simpa only [mobiusShortHead, mobius_harmonic_eq] using
    shortHead_asymptotic mobiusCoefficient_bound mobius_prefix_littleO

/-- The actual short head admits no separate absolute estimate below its three-quarter scale in `x`. -/
theorem not_mobiusShortHead_isLittleO :
    ¬ mobiusShortHead =o[atTop] fun U : ℕ => (U : ℝ) * Real.sqrt U := by
  intro h
  have hH := shortHead_littleO_imp_harmonic mobiusCoefficient_bound mobius_prefix_littleO h
  exact not_harmonic_isLittleO_inv_sqrt (hH.congr_left mobius_harmonic_eq)

end RHTower.LiouvilleTriangularShortHead
