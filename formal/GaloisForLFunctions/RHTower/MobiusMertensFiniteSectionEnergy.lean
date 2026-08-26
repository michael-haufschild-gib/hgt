import GaloisForLFunctions.RHTower.MobiusLaplaceMellinPlancherelBridge
import GaloisForLFunctions.RHTower.MobiusMertensLittlewood
import GaloisForLFunctions.RHTower.MellinOrderOneEnvelope
import GaloisForLFunctions.RHTower.MixedConvolutionSubpowerAbelBound
import GaloisForLFunctions.RHTower.MobiusWoldBreadthGibbsCost

/-!
# Mertens cancellation closes finite-section energy

A power bound for partial sums controls every finite Laplace section uniformly in its cutoff.
Applying this universal Abel estimate to the Möbius coefficients under Littlewood's criterion gives
one common two-sided exponential envelope for all logarithmic Mellin sections.  The resulting
uniform L² ceiling closes the finite-section and Gamma--Hankel RH interfaces.
-/

open scoped BigOperators
open Complex MeasureTheory

namespace RHTower

/-- Exact finite Abel summation for a complex sequence indexed from one. -/
theorem finiteLaplaceSection_eq_endpoint_add_prefixes
    (b : ℕ → ℂ) (hb0 : b 0 = 0) (N : ℕ) (r : ℂ) :
    (∑ j ∈ Finset.range N, b (j + 1) * r ^ (j + 1)) =
      partialSumSeq b N * r ^ (N + 1) +
        ∑ j ∈ Finset.range N, partialSumSeq b (j + 1) *
          (r ^ (j + 1) - r ^ (j + 2)) := by
  induction N with
  | zero => simp [partialSumSeq, hb0]
  | succ N ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
      simp only [partialSumSeq, Finset.sum_range_succ]
      ring

/-- The exponential moment estimate, normalized by the shared subpower Abel constant. -/
theorem tsum_natSucc_rpow_exp_neg_le_mixedSubpowerAbelConstant
    {theta x : ℝ} (htheta : 0 ≤ theta) (hx : 0 < x) (hx1 : x ≤ 1) :
    (∑' n : ℕ, ((n : ℝ) + 1) ^ theta * Real.exp (-((n : ℝ) * x))) ≤
      mixedSubpowerAbelConstant theta * (1 / x) ^ (theta + 1) := by
  obtain ⟨_, hmoment⟩ := summable_natSucc_rpow_exp_neg_and_tsum_le htheta hx
  have hxinv : 1 ≤ 1 / x := (one_le_div hx).2 hx1
  have hpow : 1 ≤ (1 / x) ^ (theta + 1) :=
    Real.one_le_rpow hxinv (by linarith)
  have hexp : Real.exp x ≤ Real.exp 1 := Real.exp_le_exp.mpr hx1
  have hgamma : 0 ≤ Real.Gamma (theta + 1) :=
    (Real.Gamma_pos_of_pos (by linarith)).le
  have hfactor : 0 ≤ 2 ^ theta * (1 / x) ^ (theta + 1) * Real.Gamma (theta + 1) := by
    positivity
  have hstep :
      1 + Real.exp x * 2 ^ theta * (1 / x) ^ (theta + 1) * Real.Gamma (theta + 1) ≤
        1 + Real.exp 1 * 2 ^ theta * (1 / x) ^ (theta + 1) *
          Real.Gamma (theta + 1) := by
    nlinarith
  calc
    (∑' n : ℕ, ((n : ℝ) + 1) ^ theta * Real.exp (-((n : ℝ) * x))) ≤
        1 + Real.exp x * 2 ^ theta * (1 / x) ^ (theta + 1) *
          Real.Gamma (theta + 1) := hmoment
    _ ≤ 1 + Real.exp 1 * 2 ^ theta * (1 / x) ^ (theta + 1) *
          Real.Gamma (theta + 1) := hstep
    _ ≤ mixedSubpowerAbelConstant theta * (1 / x) ^ (theta + 1) := by
      unfold mixedSubpowerAbelConstant
      have hpos : 0 ≤ Real.exp 1 * 2 ^ theta * Real.Gamma (theta + 1) := by
        positivity
      nlinarith

/-- A cutoff endpoint is uniformly bounded at the same Laplace scale as the bulk. -/
theorem natSucc_rpow_mul_exp_neg_le_uniform
    {theta x : ℝ} (htheta : 0 ≤ theta) (hx : 0 < x) (N : ℕ) :
    ((N : ℝ) + 1) ^ theta * Real.exp (-(((N : ℝ) + 1) * x)) ≤
      Real.exp (theta ^ 2) * (1 / x) ^ theta := by
  let y : ℝ := ((N : ℝ) + 1) * x
  have hy : 0 < y := by
    dsimp [y]
    positivity
  have hybound : y ^ theta * Real.exp (-y) ≤ Real.exp (theta ^ 2) := by
    by_cases hy1 : 1 ≤ y
    · simpa only [one_mul, div_one] using rpow_mul_exp_neg_le htheta one_pos hy1
    · have hy_le : y ≤ 1 := le_of_not_ge hy1
      have hyr : y ^ theta ≤ 1 := by
        simpa only [Real.one_rpow] using Real.rpow_le_rpow hy.le hy_le htheta
      have he : Real.exp (-y) ≤ 1 := by
        rw [← Real.exp_zero]
        exact Real.exp_le_exp.mpr (by linarith)
      calc
        y ^ theta * Real.exp (-y) ≤ 1 * 1 :=
          mul_le_mul hyr he (Real.exp_nonneg _) (by norm_num)
        _ = 1 := by ring
        _ ≤ Real.exp (theta ^ 2) := by
          rw [← Real.exp_zero]
          exact Real.exp_le_exp.mpr (sq_nonneg theta)
  have hfactor : ((N : ℝ) + 1) = y * (1 / x) := by
    dsimp [y]
    field_simp
  rw [hfactor]
  have hyx : (y * (1 / x)) * x = y := by field_simp [hx.ne']
  calc
    (y * (1 / x)) ^ theta * Real.exp (-((y * (1 / x)) * x)) =
        (y ^ theta * Real.exp (-y)) * (1 / x) ^ theta := by
      rw [Real.mul_rpow hy.le (by positivity), hyx]
      ring
    _ ≤ Real.exp (theta ^ 2) * (1 / x) ^ theta :=
      mul_le_mul_of_nonneg_right hybound (Real.rpow_nonneg (by positivity) theta)

/-- Universal cutoff-uniform Laplace bound obtained from a power bound on partial sums. -/
theorem norm_finiteLaplaceSection_le_of_partialSumSeq_rpow
    {b : ℕ → ℂ} (hb0 : b 0 = 0) {theta C x : ℝ}
    (htheta : 0 ≤ theta) (hC : 0 ≤ C) (hx : 0 < x) (hx1 : x ≤ 1)
    (hb : ∀ n : ℕ, ‖partialSumSeq b n‖ ≤ C * ((n : ℝ) + 1) ^ theta)
    (N : ℕ) :
    ‖∑ j ∈ Finset.range N,
        b (j + 1) * ((Real.exp (-((j + 1 : ℕ) : ℝ) * x) : ℝ) : ℂ)‖ ≤
      C * (Real.exp (theta ^ 2) + 2 ^ theta * mixedSubpowerAbelConstant theta) *
        (1 / x) ^ theta := by
  let r : ℂ := ((Real.exp (-x) : ℝ) : ℂ)
  have hrpow (n : ℕ) : r ^ n = ((Real.exp (-((n : ℝ) * x)) : ℝ) : ℂ) := by
    dsimp [r]
    norm_cast
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hleft :
      (∑ j ∈ Finset.range N,
        b (j + 1) * ((Real.exp (-((j + 1 : ℕ) : ℝ) * x) : ℝ) : ℂ)) =
      partialSumSeq b N * r ^ (N + 1) +
        ∑ j ∈ Finset.range N, partialSumSeq b (j + 1) *
          (r ^ (j + 1) - r ^ (j + 2)) := by
    rw [← finiteLaplaceSection_eq_endpoint_add_prefixes b hb0 N r]
    apply Finset.sum_congr rfl
    intro j _
    rw [hrpow]
    congr 3
    push_cast
    ring
  rw [hleft]
  have hend : ‖partialSumSeq b N * r ^ (N + 1)‖ ≤
      C * Real.exp (theta ^ 2) * (1 / x) ^ theta := by
    rw [norm_mul, hrpow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    calc
      ‖partialSumSeq b N‖ * Real.exp (-(((N + 1 : ℕ) : ℝ) * x)) ≤
          (C * ((N : ℝ) + 1) ^ theta) *
            Real.exp (-(((N : ℝ) + 1) * x)) := by
        have hcast : (((N + 1 : ℕ) : ℝ)) = (N : ℝ) + 1 := by norm_num
        rw [hcast]
        exact mul_le_mul_of_nonneg_right (hb N) (Real.exp_nonneg _)
      _ ≤ C * (Real.exp (theta ^ 2) * (1 / x) ^ theta) := by
        simpa only [mul_assoc] using
          mul_le_mul_of_nonneg_left
            (natSucc_rpow_mul_exp_neg_le_uniform htheta hx N) hC
      _ = C * Real.exp (theta ^ 2) * (1 / x) ^ theta := by ring
  have hdiff (j : ℕ) : ‖r ^ (j + 1) - r ^ (j + 2)‖ =
      Real.exp (-(((j + 1 : ℕ) : ℝ) * x)) * (1 - Real.exp (-x)) := by
    rw [show r ^ (j + 2) = r ^ (j + 1) * r by ring]
    rw [show r ^ (j + 1) - r ^ (j + 1) * r = r ^ (j + 1) * (1 - r) by ring,
      norm_mul, hrpow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    have hr0 : 0 ≤ Real.exp (-x) := (Real.exp_pos _).le
    have hr1 : Real.exp (-x) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    dsimp only [r]
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hr1)]
  have hmoment :=
    tsum_natSucc_rpow_exp_neg_le_mixedSubpowerAbelConstant htheta hx hx1
  have hsummable := (summable_natSucc_rpow_exp_neg_and_tsum_le htheta hx).1
  have hsum :
      ‖∑ j ∈ Finset.range N, partialSumSeq b (j + 1) *
          (r ^ (j + 1) - r ^ (j + 2))‖ ≤
        C * 2 ^ theta * mixedSubpowerAbelConstant theta * (1 / x) ^ theta := by
    calc
      ‖∑ j ∈ Finset.range N, partialSumSeq b (j + 1) *
          (r ^ (j + 1) - r ^ (j + 2))‖ ≤
          ∑ j ∈ Finset.range N, ‖partialSumSeq b (j + 1) *
            (r ^ (j + 1) - r ^ (j + 2))‖ := norm_sum_le _ _
      _ ≤ ∑ j ∈ Finset.range N,
          C * 2 ^ theta * (((j : ℝ) + 1) ^ theta * Real.exp (-((j : ℝ) * x))) *
            (1 - Real.exp (-x)) := by
        apply Finset.sum_le_sum
        intro j _
        rw [norm_mul, hdiff]
        have hbase : ((j + 1 : ℕ) : ℝ) + 1 ≤ 2 * ((j : ℝ) + 1) := by
          push_cast
          linarith
        have hpow : (((j + 1 : ℕ) : ℝ) + 1) ^ theta ≤
            2 ^ theta * ((j : ℝ) + 1) ^ theta := by
          calc
            (((j + 1 : ℕ) : ℝ) + 1) ^ theta ≤
                (2 * ((j : ℝ) + 1)) ^ theta :=
              Real.rpow_le_rpow (by positivity) hbase htheta
            _ = 2 ^ theta * ((j : ℝ) + 1) ^ theta :=
              Real.mul_rpow (by norm_num) (by positivity)
        have hnonneg : 0 ≤ Real.exp (-(((j + 1 : ℕ) : ℝ) * x)) *
            (1 - Real.exp (-x)) := by
          have : Real.exp (-x) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
          positivity
        have hsub : 0 ≤ 1 - Real.exp (-x) := by
          rw [sub_nonneg, ← Real.exp_zero]
          exact Real.exp_le_exp.mpr (by linarith)
        have hexp : Real.exp (-(((j + 1 : ℕ) : ℝ) * x)) ≤
            Real.exp (-((j : ℝ) * x)) := by
          apply Real.exp_le_exp.mpr
          push_cast
          nlinarith
        have hcoeff : C * (((j + 1 : ℕ) : ℝ) + 1) ^ theta ≤
            C * (2 ^ theta * ((j : ℝ) + 1) ^ theta) :=
          mul_le_mul_of_nonneg_left hpow hC
        have hweight :
            Real.exp (-(((j + 1 : ℕ) : ℝ) * x)) * (1 - Real.exp (-x)) ≤
              Real.exp (-((j : ℝ) * x)) * (1 - Real.exp (-x)) :=
          mul_le_mul_of_nonneg_right hexp hsub
        calc
          ‖partialSumSeq b (j + 1)‖ *
              (Real.exp (-(((j + 1 : ℕ) : ℝ) * x)) * (1 - Real.exp (-x))) ≤
            (C * (((j + 1 : ℕ) : ℝ) + 1) ^ theta) *
              (Real.exp (-(((j + 1 : ℕ) : ℝ) * x)) * (1 - Real.exp (-x))) :=
                mul_le_mul_of_nonneg_right (hb (j + 1)) hnonneg
          _ ≤ (C * (2 ^ theta * ((j : ℝ) + 1) ^ theta)) *
              (Real.exp (-((j : ℝ) * x)) * (1 - Real.exp (-x))) := by
                exact mul_le_mul hcoeff hweight (by positivity) (by positivity)
          _ = C * 2 ^ theta * (((j : ℝ) + 1) ^ theta *
              Real.exp (-((j : ℝ) * x))) * (1 - Real.exp (-x)) := by ring
      _ ≤ (C * 2 ^ theta *
          (∑' j : ℕ, ((j : ℝ) + 1) ^ theta * Real.exp (-((j : ℝ) * x)))) *
            (1 - Real.exp (-x)) := by
        have hfinite :=
          hsummable.sum_le_tsum (Finset.range N) (fun _ _ => by positivity)
        have hfac : 0 ≤ C * 2 ^ theta * (1 - Real.exp (-x)) := by
          have hsub : 0 ≤ 1 - Real.exp (-x) := by
            rw [sub_nonneg, ← Real.exp_zero]
            exact Real.exp_le_exp.mpr (by linarith)
          positivity
        calc
          ∑ j ∈ Finset.range N,
              C * 2 ^ theta * (((j : ℝ) + 1) ^ theta * Real.exp (-((j : ℝ) * x))) *
                (1 - Real.exp (-x)) =
              (C * 2 ^ theta * (1 - Real.exp (-x))) *
                ∑ j ∈ Finset.range N,
                  ((j : ℝ) + 1) ^ theta * Real.exp (-((j : ℝ) * x)) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            ring
          _ ≤ (C * 2 ^ theta * (1 - Real.exp (-x))) *
              ∑' j : ℕ, ((j : ℝ) + 1) ^ theta * Real.exp (-((j : ℝ) * x)) :=
            mul_le_mul_of_nonneg_left hfinite hfac
          _ = (C * 2 ^ theta *
              (∑' j : ℕ, ((j : ℝ) + 1) ^ theta * Real.exp (-((j : ℝ) * x)))) *
                (1 - Real.exp (-x)) := by ring
      _ ≤ (C * 2 ^ theta *
          (mixedSubpowerAbelConstant theta * (1 / x) ^ (theta + 1))) * x := by
        have hfac : 0 ≤ C * 2 ^ theta := by positivity
        have hsub : 0 ≤ 1 - Real.exp (-x) := by
          rw [sub_nonneg, ← Real.exp_zero]
          exact Real.exp_le_exp.mpr (by linarith)
        have hleftNonneg : 0 ≤ C * 2 ^ theta *
            (∑' j : ℕ, ((j : ℝ) + 1) ^ theta * Real.exp (-((j : ℝ) * x))) := by
          positivity
        have hrightNonneg : 0 ≤ C * 2 ^ theta *
            (mixedSubpowerAbelConstant theta * (1 / x) ^ (theta + 1)) := by
          have hA := mixedSubpowerAbelConstant_nonneg htheta
          positivity
        exact mul_le_mul (mul_le_mul_of_nonneg_left hmoment hfac)
          (one_sub_exp_neg_le x) hsub hrightNonneg
      _ = C * 2 ^ theta * mixedSubpowerAbelConstant theta * (1 / x) ^ theta := by
        rw [Real.rpow_add (by positivity), Real.rpow_one]
        field_simp [hx.ne']
  calc
    ‖partialSumSeq b N * r ^ (N + 1) +
        ∑ j ∈ Finset.range N, partialSumSeq b (j + 1) *
          (r ^ (j + 1) - r ^ (j + 2))‖ ≤
      ‖partialSumSeq b N * r ^ (N + 1)‖ +
        ‖∑ j ∈ Finset.range N, partialSumSeq b (j + 1) *
          (r ^ (j + 1) - r ^ (j + 2))‖ := norm_add_le _ _
    _ ≤ C * Real.exp (theta ^ 2) * (1 / x) ^ theta +
        C * 2 ^ theta * mixedSubpowerAbelConstant theta * (1 / x) ^ theta :=
      add_le_add hend hsum
    _ = C * (Real.exp (theta ^ 2) + 2 ^ theta * mixedSubpowerAbelConstant theta) *
        (1 / x) ^ theta := by ring

private theorem norm_mobiusDiscreteLaplaceFiniteSection_le_exp_neg
    (N : ℕ) {x : ℝ} (hx : 1 ≤ x) :
    ‖mobiusDiscreteLaplaceFiniteSection N x‖ ≤
      Real.exp (-x) * ∑' n : ℕ, Real.exp (-(n : ℝ)) := by
  have hgeom : Summable (fun n : ℕ => Real.exp (-x) * Real.exp (-(n : ℝ))) :=
    Real.summable_exp_neg_nat.mul_left _
  unfold mobiusDiscreteLaplaceFiniteSection
  calc
    ‖∑ n ∈ Finset.range N, mobiusDiscreteLaplaceTerm x (n + 1)‖ ≤
        ∑ n ∈ Finset.range N, ‖mobiusDiscreteLaplaceTerm x (n + 1)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.range N, Real.exp (-x) * Real.exp (-(n : ℝ)) := by
      apply Finset.sum_le_sum
      intro n _
      rw [mobiusDiscreteLaplaceTerm, norm_mul, Complex.norm_exp]
      have hmu : ‖((ArithmeticFunction.moebius (n + 1) : ℤ) : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_intCast]
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n + 1)
      have hexp : Real.exp (-(((n + 1 : ℕ) : ℝ) * x)) ≤
          Real.exp (-x) * Real.exp (-(n : ℝ)) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
        push_cast
        nlinarith
      exact (mul_le_mul_of_nonneg_right hmu (Real.exp_pos _).le).trans
        (by simpa using hexp)
    _ ≤ ∑' n : ℕ, Real.exp (-x) * Real.exp (-(n : ℝ)) :=
      hgeom.sum_le_tsum (Finset.range N) (fun _ _ => by positivity)
    _ = Real.exp (-x) * ∑' n : ℕ, Real.exp (-(n : ℝ)) := by
      rw [tsum_mul_left]

private noncomputable def twoSidedExpEnvelope (A B p q u : ℝ) : ℝ :=
  if u ≤ 0 then B * Real.exp (q * u) else A * Real.exp (-p * u)

private theorem memLp_twoSidedExpEnvelope
    {A B p q : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hp : 0 < p) (hq : 0 < q) :
    MemLp (twoSidedExpEnvelope A B p q) 2 volume := by
  have hmeas : AEStronglyMeasurable (twoSidedExpEnvelope A B p q) volume := by
    apply Measurable.aestronglyMeasurable
    unfold twoSidedExpEnvelope
    exact Measurable.piecewise measurableSet_Iic (by fun_prop) (by fun_prop)
  apply (memLp_two_iff_integrable_sq_norm hmeas).2
  have hposMajor : IntegrableOn
      (fun u : ℝ => A ^ 2 * Real.exp ((-2 * p) * u)) (Set.Ioi 0) :=
    (integrableOn_exp_mul_Ioi (by linarith) 0).const_mul (A ^ 2)
  have hpos : IntegrableOn
      (fun u : ℝ => ‖twoSidedExpEnvelope A B p q u‖ ^ 2) (Set.Ioi 0) := by
    apply hposMajor.congr_fun
    · intro u hu
      have hu' : ¬ u ≤ 0 := by simpa using hu
      simp only [twoSidedExpEnvelope, if_neg hu']
      rw [Real.norm_of_nonneg (by positivity), mul_pow, ← Real.exp_nat_mul]
      congr 2
      ring
    · exact measurableSet_Ioi
  have hnegMajor : IntegrableOn
      (fun u : ℝ => B ^ 2 * Real.exp ((2 * q) * u)) (Set.Iic 0) :=
    (integrableOn_exp_mul_Iic (by linarith) 0).const_mul (B ^ 2)
  have hneg : IntegrableOn
      (fun u : ℝ => ‖twoSidedExpEnvelope A B p q u‖ ^ 2) (Set.Iic 0) := by
    apply hnegMajor.congr_fun
    · intro u hu
      have hu' : u ≤ 0 := by simpa using hu
      simp only [twoSidedExpEnvelope, if_pos hu']
      rw [Real.norm_of_nonneg (by positivity), mul_pow, ← Real.exp_nat_mul]
      congr 2
      ring
    · exact measurableSet_Iic
  simpa [Set.Ioi_union_Iic] using hpos.union hneg

private theorem exists_finiteSection_envelope_of_mertensBound
    {theta C sigma : ℝ} (htheta : 0 ≤ theta) (hC : 0 ≤ C)
    (hM : ∀ n : ℕ, ‖mobiusMertensPartialSum n‖ ≤
      C * ((n : ℝ) + 1) ^ theta) :
    ∃ m : ℕ, sigma < m ∧ ∀ N : ℕ, ∀ u : ℝ,
      ‖mobiusLaplaceFiniteSectionLogMellinLineSource N sigma u‖ ≤
        twoSidedExpEnvelope
          (C * (Real.exp (theta ^ 2) + 2 ^ theta * mixedSubpowerAbelConstant theta))
          ((∑' k : ℕ, Real.exp (-(k : ℝ))) * (Nat.factorial m : ℝ))
          (sigma - theta) ((m : ℝ) - sigma) u := by
  obtain ⟨m : ℕ, hm⟩ := exists_nat_gt sigma
  refine ⟨m, hm, fun N u => ?_⟩
  let A : ℝ := C * (Real.exp (theta ^ 2) + 2 ^ theta * mixedSubpowerAbelConstant theta)
  let B : ℝ := (∑' k : ℕ, Real.exp (-(k : ℝ))) * (Nat.factorial m : ℝ)
  by_cases hu : u ≤ 0
  · have hx : 1 ≤ Real.exp (-u) := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by linarith)
    have hfinite := norm_mobiusDiscreteLaplaceFiniteSection_le_exp_neg N hx
    have hsuper := exp_neg_exp_neg_le_factorial_mul_exp_nat_mul m u
    unfold mobiusLaplaceFiniteSectionLogMellinLineSource
    rw [norm_smul, Real.norm_of_nonneg (Real.exp_nonneg _)]
    simp only [twoSidedExpEnvelope, if_pos hu]
    calc
      Real.exp (-sigma * u) *
          ‖mobiusDiscreteLaplaceFiniteSection N (Real.exp (-u))‖ ≤
        Real.exp (-sigma * u) *
          (Real.exp (-Real.exp (-u)) * ∑' k : ℕ, Real.exp (-(k : ℝ))) :=
        mul_le_mul_of_nonneg_left hfinite (Real.exp_nonneg _)
      _ = (∑' k : ℕ, Real.exp (-(k : ℝ))) *
          (Real.exp (-sigma * u) * Real.exp (-Real.exp (-u))) := by ring
      _ ≤ (∑' k : ℕ, Real.exp (-(k : ℝ))) *
          (Real.exp (-sigma * u) *
            ((Nat.factorial m : ℝ) * Real.exp ((m : ℝ) * u))) := by
        gcongr
      _ = B * Real.exp (((m : ℝ) - sigma) * u) := by
        dsimp only [B]
        calc
          (∑' k : ℕ, Real.exp (-(k : ℝ))) *
              (Real.exp (-sigma * u) *
                ((Nat.factorial m : ℝ) * Real.exp ((m : ℝ) * u))) =
            (∑' k : ℕ, Real.exp (-(k : ℝ))) * (Nat.factorial m : ℝ) *
              (Real.exp (-sigma * u) * Real.exp ((m : ℝ) * u)) := by ring
          _ = _ := by
            rw [← Real.exp_add]
            congr 2
            ring
  · have hu0 : 0 ≤ u := le_of_not_ge hu
    have hx : 0 < Real.exp (-u) := Real.exp_pos _
    have hx1 : Real.exp (-u) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have hpartial : ∀ n : ℕ,
        ‖partialSumSeq (fun k => (ArithmeticFunction.moebius k : ℂ)) n‖ ≤
          C * ((n : ℝ) + 1) ^ theta := by
      intro n
      simpa [partialSumSeq, mobiusMertensPartialSum, mobiusComplexCoefficient] using hM n
    have hfinite := norm_finiteLaplaceSection_le_of_partialSumSeq_rpow
      (b := fun n => (ArithmeticFunction.moebius n : ℂ)) (by simp)
      htheta hC hx hx1 hpartial N
    have hfinite' :
        ‖mobiusDiscreteLaplaceFiniteSection N (Real.exp (-u))‖ ≤
          A * (1 / Real.exp (-u)) ^ theta := by
      have heq : mobiusDiscreteLaplaceFiniteSection N (Real.exp (-u)) =
          ∑ j ∈ Finset.range N,
            (ArithmeticFunction.moebius (j + 1) : ℂ) *
              ((Real.exp (-((j + 1 : ℕ) : ℝ) * Real.exp (-u)) : ℝ) : ℂ) := by
        unfold mobiusDiscreteLaplaceFiniteSection
        apply Finset.sum_congr rfl
        intro j _
        rw [mobiusDiscreteLaplaceTerm]
        exact congrArg
          (fun z : ℂ => (ArithmeticFunction.moebius (j + 1) : ℂ) * z)
          (by
            rw [← Complex.ofReal_neg]
            convert
              (Complex.ofReal_exp (-(((j + 1 : ℕ) : ℝ) * Real.exp (-u)))).symm using 1
            ring)
      rw [heq]
      simpa only [A] using hfinite
    have hinv : 1 / Real.exp (-u) = Real.exp u := by
      rw [one_div, ← Real.exp_neg]
      ring_nf
    unfold mobiusLaplaceFiniteSectionLogMellinLineSource
    rw [norm_smul, Real.norm_of_nonneg (Real.exp_nonneg _)]
    simp only [twoSidedExpEnvelope, if_neg hu]
    calc
      Real.exp (-sigma * u) *
          ‖mobiusDiscreteLaplaceFiniteSection N (Real.exp (-u))‖ ≤
        Real.exp (-sigma * u) * (A * (1 / Real.exp (-u)) ^ theta) :=
          mul_le_mul_of_nonneg_left hfinite' (Real.exp_nonneg _)
      _ = A * Real.exp (-(sigma - theta) * u) := by
        rw [hinv, Real.rpow_def_of_pos (Real.exp_pos u), Real.log_exp]
        calc
          Real.exp (-sigma * u) * (A * Real.exp (u * theta)) =
              A * (Real.exp (-sigma * u) * Real.exp (u * theta)) := by ring
          _ = _ := by
            rw [← Real.exp_add]
            congr 2
            ring

/-- A strict power saving for Mertens sums gives one cutoff-independent L² ceiling for all
finite logarithmic Möbius--Laplace sections on every line to its right. -/
theorem mobiusLaplaceFiniteSectionEnergyBounded_of_mertensBound
    {theta C sigma : ℝ} (htheta : 0 ≤ theta) (hC : 0 ≤ C)
    (hthetaSigma : theta < sigma)
    (hM : ∀ n : ℕ, ‖mobiusMertensPartialSum n‖ ≤
      C * ((n : ℝ) + 1) ^ theta) :
    ∃ E : ENNReal, E ≠ ⊤ ∧ ∀ N : ℕ,
      eLpNorm (mobiusLaplaceFiniteSectionLogMellinLineSource N sigma) 2 volume ≤ E := by
  obtain ⟨m, hm, henvelope⟩ :=
    exists_finiteSection_envelope_of_mertensBound (sigma := sigma) htheta hC hM
  let A : ℝ := C * (Real.exp (theta ^ 2) + 2 ^ theta * mixedSubpowerAbelConstant theta)
  let B : ℝ := (∑' k : ℕ, Real.exp (-(k : ℝ))) * (Nat.factorial m : ℝ)
  let g : ℝ → ℝ := twoSidedExpEnvelope A B (sigma - theta) ((m : ℝ) - sigma)
  have hA : 0 ≤ A := by
    dsimp [A]
    have hAbel := mixedSubpowerAbelConstant_nonneg htheta
    positivity
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  have hp : 0 < sigma - theta := sub_pos.mpr hthetaSigma
  have hq : 0 < (m : ℝ) - sigma := sub_pos.mpr (by exact_mod_cast hm)
  have hg : MemLp g 2 volume :=
    memLp_twoSidedExpEnvelope hA hB hp hq
  let E : ENNReal := eLpNorm g 2 volume
  refine ⟨E, ne_of_lt hg.eLpNorm_lt_top, fun N => ?_⟩
  apply eLpNorm_mono_ae
  exact Filter.Eventually.of_forall fun u => by
    have hgu : 0 ≤ g u := by
      dsimp only [g, twoSidedExpEnvelope]
      split_ifs <;> positivity
    rw [Real.norm_of_nonneg hgu]
    simpa only [g, A, B] using henvelope N u

/-- Littlewood's Mertens estimate under RH yields uniform finite-section logarithmic energy on
Mellin lines cofinal from the right at one half. -/
theorem riemannHypothesis_implies_mobiusLaplaceCofinalFiniteSectionEnergyBounded :
    RiemannHypothesis → MobiusLaplaceCofinalFiniteSectionEnergyBounded := by
  intro hRH epsilon hepsilon
  let eta : ℝ := min (epsilon / 4) (1 / 8)
  let theta : ℝ := 1 / 2 + eta
  let sigma : ℝ := 1 / 2 + 2 * eta
  have heta : 0 < eta := by
    dsimp [eta]
    positivity
  have hetaUpper : eta ≤ epsilon / 4 := min_le_left _ _
  have htheta : 0 ≤ theta := by
    dsimp [theta]
    linarith
  have hthetaSigma : theta < sigma := by
    dsimp [theta, sigma]
    linarith
  have hsigmaHalf : 1 / 2 < sigma := by
    dsimp [sigma]
    linarith
  have hsigmaUpper : sigma < 1 / 2 + epsilon := by
    dsimp [sigma]
    linarith
  obtain ⟨C, hC, hM⟩ :=
    riemannHypothesis_implies_mobiusMertensAllStrictHalfPowerBound hRH eta heta
  obtain ⟨E, hEtop, hE⟩ :=
    mobiusLaplaceFiniteSectionEnergyBounded_of_mertensBound
      htheta hC hthetaSigma hM
  exact ⟨sigma, E, hsigmaHalf, hsigmaUpper, hEtop, hE⟩

/-- Uniform finite logarithmic Möbius sections cofinal at the critical line are exactly RH. -/
theorem mobiusLaplaceCofinalFiniteSectionEnergyBounded_iff_riemannHypothesis :
    MobiusLaplaceCofinalFiniteSectionEnergyBounded ↔ RiemannHypothesis :=
  ⟨mobiusLaplaceCofinalFiniteSectionEnergyBounded_implies_riemannHypothesis,
    riemannHypothesis_implies_mobiusLaplaceCofinalFiniteSectionEnergyBounded⟩

/-- Explicit cofinal sequence of strict-right Mellin abscissas. -/
noncomputable def mobiusLaplaceCanonicalAbscissa (k : ℕ) : ℝ :=
  1 / 2 + 1 / ((k + 2 : ℕ) : ℝ)

/-- Canonical-schedule finite-section frontier: at every prescribed abscissa, all finite
Möbius--Laplace sections share one finite `L²` ceiling. -/
noncomputable def MobiusLaplaceCanonicalFiniteSectionEnergyBounded : Prop :=
  ∀ k : ℕ, ∃ C : ENNReal, C ≠ ⊤ ∧ ∀ N : ℕ,
    eLpNorm (mobiusLaplaceFiniteSectionLogMellinLineSource N
      (mobiusLaplaceCanonicalAbscissa k)) 2 volume ≤ C

/-- Littlewood's RH consequence controls every abscissa in the canonical cofinal schedule. -/
theorem mobiusLaplaceCanonicalFiniteSectionEnergyBounded_of_riemannHypothesis
    (hRH : RiemannHypothesis) :
    MobiusLaplaceCanonicalFiniteSectionEnergyBounded := by
  intro k
  let d : ℝ := ((k + 2 : ℕ) : ℝ)
  let eta : ℝ := 1 / (4 * d)
  let theta : ℝ := 1 / 2 + eta
  let sigma : ℝ := mobiusLaplaceCanonicalAbscissa k
  have hd : 0 < d := by
    dsimp only [d]
    positivity
  have heta : 0 < eta := by
    dsimp only [eta]
    positivity
  have htheta : 0 ≤ theta := by
    dsimp only [theta]
    positivity
  have hthetaSigma : theta < sigma := by
    have h4d : d < 4 * d := by nlinarith
    have hfrac : 1 / (4 * d) < 1 / d :=
      one_div_lt_one_div_of_lt hd h4d
    dsimp only [theta, eta, sigma, mobiusLaplaceCanonicalAbscissa]
    dsimp only [d] at hfrac
    linarith
  obtain ⟨C, hC, hM⟩ :=
    riemannHypothesis_implies_mobiusMertensAllStrictHalfPowerBound hRH eta heta
  obtain ⟨E, hEtop, hE⟩ :=
    mobiusLaplaceFiniteSectionEnergyBounded_of_mertensBound
      htheta hC hthetaSigma hM
  exact ⟨E, hEtop, hE⟩

/-- The explicit abscissas are cofinal, so their finite-section ceilings discharge the older
existential line-selection interface. -/
theorem mobiusLaplaceCofinalFiniteSectionEnergyBounded_of_canonical
    (h : MobiusLaplaceCanonicalFiniteSectionEnergyBounded) :
    MobiusLaplaceCofinalFiniteSectionEnergyBounded := by
  intro epsilon hepsilon
  obtain ⟨k, hk⟩ := exists_nat_gt (1 / epsilon)
  have hden : (0 : ℝ) < ((k + 2 : ℕ) : ℝ) := by positivity
  have hepsmul : 1 < epsilon * (k : ℝ) := by
    calc
      1 = epsilon * (1 / epsilon) := by field_simp
      _ < epsilon * (k : ℝ) := mul_lt_mul_of_pos_left hk hepsilon
  have hepsden : 1 < epsilon * ((k + 2 : ℕ) : ℝ) := by
    norm_num at hepsmul ⊢
    nlinarith
  have hinvlt : 1 / ((k + 2 : ℕ) : ℝ) < epsilon :=
    (div_lt_iff₀ hden).2 (by simpa [mul_comm] using hepsden)
  obtain ⟨C, hCtop, hC⟩ := h k
  refine ⟨mobiusLaplaceCanonicalAbscissa k, C, ?_, ?_, hCtop, hC⟩
  · dsimp only [mobiusLaplaceCanonicalAbscissa]
    have hinvpos : 0 < 1 / ((k + 2 : ℕ) : ℝ) := one_div_pos.mpr hden
    linarith
  · dsimp only [mobiusLaplaceCanonicalAbscissa]
    linarith

/-- **Canonical finite Möbius--Laplace criterion.** RH is equivalent to uniform cutoff energy
bounds on the single explicit abscissa schedule `1/2 + 1/(k+2)`. -/
theorem mobiusLaplaceCanonicalFiniteSectionEnergyBounded_iff_riemannHypothesis :
    MobiusLaplaceCanonicalFiniteSectionEnergyBounded ↔ RiemannHypothesis := by
  constructor
  · intro h
    exact mobiusLaplaceCofinalFiniteSectionEnergyBounded_implies_riemannHypothesis
      (mobiusLaplaceCofinalFiniteSectionEnergyBounded_of_canonical h)
  · exact mobiusLaplaceCanonicalFiniteSectionEnergyBounded_of_riemannHypothesis

/-- Cofinal one-sided Gamma--Hankel covariance ceilings are exactly RH. -/
theorem mobiusLaplaceCofinalGammaHankelOffDiagonalUpperBounded_iff_riemannHypothesis :
    MobiusLaplaceCofinalGammaHankelOffDiagonalUpperBounded ↔ RiemannHypothesis :=
  mobiusLaplaceCofinalFiniteSectionEnergyBounded_iff_gammaHankelOffDiagonalUpperBounded.symm.trans
    mobiusLaplaceCofinalFiniteSectionEnergyBounded_iff_riemannHypothesis

/-- Even bounded returns of cofinal one-sided Gamma--Hankel covariance are exactly RH. -/
theorem mobiusLaplaceCofinalGammaHankelOffDiagonalFrequentlyUpperBounded_iff_riemannHypothesis :
    MobiusLaplaceCofinalGammaHankelOffDiagonalFrequentlyUpperBounded ↔ RiemannHypothesis := by
  constructor
  · exact
      mobiusLaplaceCofinalGammaHankelOffDiagonalFrequentlyUpperBounded_implies_riemannHypothesis
  · intro hRH
    exact mobiusLaplaceCofinalGammaHankelOffDiagonalFrequentlyUpperBounded_of_upperBounded
      (mobiusLaplaceCofinalGammaHankelOffDiagonalUpperBounded_of_finiteSectionEnergy
        (riemannHypothesis_implies_mobiusLaplaceCofinalFiniteSectionEnergyBounded hRH))

end RHTower
