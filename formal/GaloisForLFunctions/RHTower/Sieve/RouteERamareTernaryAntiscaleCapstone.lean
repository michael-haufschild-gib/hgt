import GaloisForLFunctions.RHTower.Sieve.RouteERamareGibbsMeanLeakage
import GaloisForLFunctions.RHTower.Sieve.RouteERamareTernaryAntiscale

/-!
# Route E Ramaré–ternary capstone

This module closes every dependency-closed finite claim in the Route E Ramaré recombination and
ternary antiscale paper card. It removes zero-padded nonsquarefree support, identifies the literal
integer shared-incidence diagonal with the original prime-block diagonal, proves the exact
collision/distinct-integer split and coprime firewall, and recovers the full squarefree Gram.

For the ternary marker it upgrades cofinal near-saturation to exact least-upper-bound statements on
every late-time tail, proves the real cosine product formulae, and derives the explicit measurable
large-value laws for both uniform and reciprocal Gibbs histories. All statements are unconditional
finite mathematics; no computation, route premise, or asymptotic placeholder is used.
-/

namespace RHTower.Sieve

open Finset MeasureTheory
open scoped ArithmeticFunction.Moebius
open HTGeometry.ConstraintMotiveRelativity

noncomputable section

/-- Literal squarefree support used by the paper's Ramaré recombination. -/
def ramareSquarefreeActiveSet (P : Finset ℕ) (M : ℕ) : Finset ℕ :=
  (ramareActiveSet P M).filter Squarefree

theorem moebiusPhase_eq_zero_of_not_squarefree (w : ℝ) {n : ℕ}
    (hn : ¬ Squarefree n) : moebiusPhase w n = 0 := by
  rw [moebiusPhase, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hn]
  simp

theorem sum_ramareActiveSet_moebiusPhase_eq_squarefree
    (P : Finset ℕ) (M : ℕ) (w : ℝ) :
    (∑ n ∈ ramareActiveSet P M, moebiusPhase w n) =
      ∑ n ∈ ramareSquarefreeActiveSet P M, moebiusPhase w n := by
  classical
  rw [ramareSquarefreeActiveSet, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hsf : Squarefree n
  · simp [hsf]
  · simp [hsf, moebiusPhase_eq_zero_of_not_squarefree w hsf]

theorem ramareBilinear_eq_squarefreeActiveSum
    {P : Finset ℕ} (hPprime : ∀ p ∈ P, p.Prime) (M : ℕ) (w : ℝ) :
    ramareBilinear P M w =
      ∑ n ∈ ramareSquarefreeActiveSet P M, moebiusPhase w n := by
  classical
  rw [ramareBilinear_eq_sum]
  calc
    (∑ p ∈ P, moebiusPhase w p * ramareCofactorPoly P M p w) =
        ∑ p ∈ P, routeENormalizedIncidenceBlock
          (ramareActiveSet P M) (primeFactorsIn P) (moebiusPhase w) p := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [ramarePrimeBlock_eq_activeIndicatorBlock hPprime hp]
      rfl
    _ = ∑ n ∈ ramareActiveSet P M, moebiusPhase w n := by
      apply routeE_sum_normalizedIncidenceBlock
      · intro n hn q hq
        exact (mem_primeFactorsIn.mp hq).1
      · intro n hn
        exact (Finset.mem_filter.mp hn).2
    _ = _ := sum_ramareActiveSet_moebiusPhase_eq_squarefree P M w

/-- Shared-prime incidence ratio complementary to `ramareIncidenceComplement`. -/
noncomputable def ramareSharedIncidenceRatio (P : Finset ℕ) (n m : ℕ) : ℝ :=
  (((primeFactorsIn P n) ∩ (primeFactorsIn P m)).card : ℝ) /
    (((primeFactorsIn P n).card : ℝ) * ((primeFactorsIn P m).card : ℝ))

/-- Literal integer form of the prime-block diagonal. -/
noncomputable def ramarePrimeDiagonalInteger
    (P : Finset ℕ) (M : ℕ) (W : ℝ) : ℝ :=
  ∑ n ∈ ramareSquarefreeActiveSet P M,
    ∑ m ∈ ramareSquarefreeActiveSet P M,
      (((μ n : ℤ) : ℝ) * ((μ m : ℤ) : ℝ) * ramareSharedIncidenceRatio P n m) *
        ramareMellinPairKernel W n m

/-- Full squarefree active integer Gram after diagonal/off-diagonal recombination. -/
noncomputable def ramareFullIntegerGram
    (P : Finset ℕ) (M : ℕ) (W : ℝ) : ℝ :=
  ∑ n ∈ ramareSquarefreeActiveSet P M,
    ∑ m ∈ ramareSquarefreeActiveSet P M,
      (((μ n : ℤ) : ℝ) * ((μ m : ℤ) : ℝ)) * ramareMellinPairKernel W n m

theorem ramarePrimeOffDiagonal_eq_squarefreeIntegerIncidence
    {P : Finset ℕ} (hPprime : ∀ p ∈ P, p.Prime) (M : ℕ) (W : ℝ) :
    ramarePrimeOffDiagonal P M W =
      ∑ n ∈ ramareSquarefreeActiveSet P M,
        ∑ m ∈ ramareSquarefreeActiveSet P M,
          (((μ n : ℤ) : ℝ) * ((μ m : ℤ) : ℝ) * ramareIncidenceComplement P n m) *
            ramareMellinPairKernel W n m := by
  classical
  rw [ramarePrimeOffDiagonal_eq_integerIncidence hPprime]
  rw [ramareSquarefreeActiveSet, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hsn : Squarefree n
  · simp only [hsn, ↓reduceIte]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro m hm
    by_cases hsm : Squarefree m
    · simp [hsm]
    · simp [hsm, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsm]
  · simp [hsn, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsn]

theorem ramareSharedIncidenceRatio_add_complement
    (P : Finset ℕ) (n m : ℕ) :
    ramareSharedIncidenceRatio P n m + ramareIncidenceComplement P n m = 1 := by
  rw [ramareSharedIncidenceRatio, ramareIncidenceComplement]
  ring

theorem ramarePrimeDiagonal_add_offDiagonal_eq_fullIntegerGram
    {P : Finset ℕ} (hPprime : ∀ p ∈ P, p.Prime) (M : ℕ) (W : ℝ) :
    ramarePrimeDiagonalInteger P M W + ramarePrimeOffDiagonal P M W =
      ramareFullIntegerGram P M W := by
  classical
  rw [ramarePrimeOffDiagonal_eq_squarefreeIntegerIncidence hPprime]
  rw [ramarePrimeDiagonalInteger, ramareFullIntegerGram, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  have hinc := ramareSharedIncidenceRatio_add_complement P n m
  calc
    (((μ n : ℤ) : ℝ) * ((μ m : ℤ) : ℝ) * ramareSharedIncidenceRatio P n m) *
          ramareMellinPairKernel W n m +
        (((μ n : ℤ) : ℝ) * ((μ m : ℤ) : ℝ) * ramareIncidenceComplement P n m) *
          ramareMellinPairKernel W n m =
        (ramareSharedIncidenceRatio P n m + ramareIncidenceComplement P n m) *
          (((μ n : ℤ) : ℝ) * ((μ m : ℤ) : ℝ)) * ramareMellinPairKernel W n m := by ring
    _ = _ := by rw [hinc]; ring

theorem normSq_squarefreeActiveSum_eq_pairwisePhase
    (P : Finset ℕ) (M : ℕ) (w : ℝ) :
    ‖∑ n ∈ ramareSquarefreeActiveSet P M, moebiusPhase w n‖ ^ 2 =
      ∑ n ∈ ramareSquarefreeActiveSet P M,
        ∑ m ∈ ramareSquarefreeActiveSet P M,
          (((μ n : ℤ) : ℝ) * ((μ m : ℤ) : ℝ)) *
            (unitLogPhase w n * (starRingEnd ℂ) (unitLogPhase w m)).re := by
  rw [normSq_sum_eq_double]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro m hm
  exact re_moebiusPhase_mul_conj_eq_signs_mul_phase w n m

theorem integral_normSq_squarefreeActiveSum_eq_fullIntegerGram
    (P : Finset ℕ) (M : ℕ) (W : ℝ) :
    (∫ w in Set.Icc (-W) W,
        ‖∑ n ∈ ramareSquarefreeActiveSet P M, moebiusPhase w n‖ ^ 2) =
      ramareFullIntegerGram P M W := by
  classical
  rw [setIntegral_congr_fun measurableSet_Icc
    (fun w _ => normSq_squarefreeActiveSum_eq_pairwisePhase P M w)]
  have hcont : ∀ n m : ℕ, Continuous fun w : ℝ =>
      (((μ n : ℤ) : ℝ) * ((μ m : ℤ) : ℝ)) *
        (unitLogPhase w n * (starRingEnd ℂ) (unitLogPhase w m)).re := by
    intro n m
    exact (Complex.continuous_re.comp
      ((continuous_unitLogPhase n).mul
        (Complex.continuous_conj.comp (continuous_unitLogPhase m)))).const_mul _
  have hint : ∀ n m : ℕ, IntegrableOn (fun w : ℝ =>
      (((μ n : ℤ) : ℝ) * ((μ m : ℤ) : ℝ)) *
        (unitLogPhase w n * (starRingEnd ℂ) (unitLogPhase w m)).re)
      (Set.Icc (-W) W) volume := fun n m => (hcont n m).integrableOn_Icc
  have hintRow : ∀ n ∈ ramareSquarefreeActiveSet P M, IntegrableOn (fun w : ℝ =>
      ∑ m ∈ ramareSquarefreeActiveSet P M,
        (((μ n : ℤ) : ℝ) * ((μ m : ℤ) : ℝ)) *
          (unitLogPhase w n * (starRingEnd ℂ) (unitLogPhase w m)).re)
      (Set.Icc (-W) W) volume :=
    fun n _ => integrable_finsetSum _ fun m _ => hint n m
  rw [integral_finsetSum _ hintRow]
  rw [ramareFullIntegerGram]
  apply Finset.sum_congr rfl
  intro n hn
  rw [integral_finsetSum _ (fun m _ => hint n m)]
  apply Finset.sum_congr rfl
  intro m hm
  rw [MeasureTheory.integral_const_mul]
  rfl

theorem ramarePrimeDiagonal_add_offDiagonal_eq_integral_squarefreeActive
    {P : Finset ℕ} (hPprime : ∀ p ∈ P, p.Prime) (M : ℕ) (W : ℝ) :
    ramarePrimeDiagonalInteger P M W + ramarePrimeOffDiagonal P M W =
      ∫ w in Set.Icc (-W) W,
        ‖∑ n ∈ ramareSquarefreeActiveSet P M, moebiusPhase w n‖ ^ 2 := by
  rw [ramarePrimeDiagonal_add_offDiagonal_eq_fullIntegerGram hPprime]
  exact (integral_normSq_squarefreeActiveSum_eq_fullIntegerGram P M W).symm

/-- Exact tail supremum statement behind the unweighted cofinal saturation law. -/
theorem routeETernaryReporter_tail_isLUB (Q : Finset Nat.Primes) (T : ℝ) :
    IsLUB
      (Set.range fun t : {t : ℝ // T < t} => ‖routeETernaryReporter Q t.1‖)
      ((3 : ℝ) ^ Q.card) := by
  constructor
  · rintro y ⟨t, rfl⟩
    exact routeETernaryReporter_norm_le_pow Q t.1
  · intro b hb
    by_contra hnot
    have hlt : b < (3 : ℝ) ^ Q.card := lt_of_not_ge hnot
    obtain ⟨t, htT, ht⟩ :=
      exists_gt_routeETernaryReporter_norm_gt_pow_sub Q T (sub_pos.mpr hlt)
    have hbelow : b < ‖routeETernaryReporter Q t‖ := by
      have heq : (3 : ℝ) ^ Q.card - ((3 : ℝ) ^ Q.card - b) = b := by ring
      rwa [heq] at ht
    have habove : ‖routeETernaryReporter Q t‖ ≤ b :=
      hb (Set.mem_range_self (⟨t, htT⟩ : {t : ℝ // T < t}))
    linarith

/-- Exact tail supremum statement behind reciprocal Gibbs cofinal saturation. -/
theorem routeETernaryWeightedReporter_tail_isLUB
    (Q : Finset Nat.Primes) (T : ℝ) :
    IsLUB
      (Set.range fun t : {t : ℝ // T < t} => ‖routeETernaryWeightedReporter Q t.1‖)
      1 := by
  constructor
  · rintro y ⟨t, rfl⟩
    exact routeETernaryWeightedReporter_norm_le_one Q t.1
  · intro b hb
    by_contra hnot
    have hlt : b < 1 := lt_of_not_ge hnot
    obtain ⟨t, htT, ht⟩ :=
      exists_gt_routeETernaryWeightedReporter_norm_gt_one_sub Q T (sub_pos.mpr hlt)
    have hbelow : b < ‖routeETernaryWeightedReporter Q t‖ := by
      have heq : (1 : ℝ) - (1 - b) = b := by ring
      rwa [heq] at ht
    have habove : ‖routeETernaryWeightedReporter Q t‖ ≤ b :=
      hb (Set.mem_range_self (⟨t, htT⟩ : {t : ℝ // T < t}))
    linarith

theorem continuous_routeETernaryReporter (Q : Finset Nat.Primes) :
    Continuous (routeETernaryReporter Q) := by
  change Continuous fun t : ℝ => ∏ p : Q,
    (1 - (starRingEnd ℂ) (phaseCovec t p) - phaseCovec t p)
  apply continuous_finsetProd
  intro p hp
  have hc : Continuous fun t : ℝ => phaseCovec t p := by
    simpa [phaseCovec] using continuous_portCoef (θ := primeLog)
      (c := fun _ : Nat.Primes => (1 : ℂ)) p
  exact continuous_const.sub (Complex.continuous_conj.comp hc) |>.sub hc

theorem continuous_routeETernaryWeightedReporter (Q : Finset Nat.Primes) :
    Continuous (routeETernaryWeightedReporter Q) := by
  change Continuous fun t : ℝ => ∏ p : Q,
    (let u := routeETernaryReciprocalRadius p;
      (1 - (u : ℂ) * (starRingEnd ℂ) (phaseCovec t p) -
        (u : ℂ) * phaseCovec t p) / (1 + 2 * u))
  apply continuous_finsetProd
  intro p hp
  have hc : Continuous fun t : ℝ => phaseCovec t p := by
    simpa [phaseCovec] using continuous_portCoef (θ := primeLog)
      (c := fun _ : Nat.Primes => (1 : ℂ)) p
  fun_prop

/-- Restricted-volume Chebyshev law in the exact form used by both ternary reporters. -/
theorem routeE_restrictVolume_norm_ge_le_of_intervalIntegral_sq_le
    (f : ℝ → ℂ) (hf : Continuous f) {W A B : ℝ}
    (hW : 0 < W) (hA : 0 < A)
    (hmean : (∫ t in (-W)..W, ‖f t‖ ^ 2) ≤ B) :
    (volume.restrict (Set.Icc (-W) W)).real {t | A ≤ ‖f t‖} ≤ B / A ^ 2 := by
  let μW : Measure ℝ := volume.restrict (Set.Icc (-W) W)
  have hint : Integrable (fun t : ℝ => ‖f t‖ ^ 2) μW := by
    exact (hf.norm.pow 2).integrableOn_Icc
  have hnonneg : 0 ≤ᵐ[μW] fun t : ℝ => ‖f t‖ ^ 2 :=
    Filter.Eventually.of_forall fun t => sq_nonneg ‖f t‖
  have hmark := MeasureTheory.mul_meas_ge_le_integral_of_nonneg
    hnonneg hint (A ^ 2)
  have hset : {t : ℝ | A ^ 2 ≤ ‖f t‖ ^ 2} = {t : ℝ | A ≤ ‖f t‖} := by
    ext t
    simp only [Set.mem_setOf_eq]
    constructor
    · intro hsq
      nlinarith [norm_nonneg (f t)]
    · intro h
      exact pow_le_pow_left₀ hA.le h 2
  rw [hset] at hmark
  have hintegral : (∫ t, ‖f t‖ ^ 2 ∂μW) ≤ B := by
    change (∫ t in Set.Icc (-W) W, ‖f t‖ ^ 2) ≤ B
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith : -W ≤ W)]
    exact hmean
  apply (le_div_iff₀ (sq_pos_of_pos hA)).2
  simpa [μW, mul_comm] using hmark.trans hintegral

/-- Equation (28): exact finite-height rarity of unweighted antiscale peaks. -/
theorem routeETernaryReporter_largeValue_relativeMeasure_le
    (Q : Finset Nat.Primes) {W lambda : ℝ}
    (hW : 0 < W) (hlambda : 0 < lambda) :
    (volume.restrict (Set.Icc (-W) W)).real
        {t | lambda * (3 : ℝ) ^ Q.card ≤ ‖routeETernaryReporter Q t‖} / (2 * W) ≤
      (1 + 2 * (routeETernaryPrimorial Q : ℝ) ^ 2 *
          (1 + (Q.card : ℝ) * Real.log 3) / W) /
        (lambda ^ 2 * (3 : ℝ) ^ Q.card) := by
  have hA : 0 < lambda * (3 : ℝ) ^ Q.card := mul_pos hlambda (by positivity)
  have hbase := routeE_restrictVolume_norm_ge_le_of_intervalIntegral_sq_le
    (routeETernaryReporter Q) (continuous_routeETernaryReporter Q) hW hA
    (routeETernaryReporter_meanValue_le Q W)
  calc
    (volume.restrict (Set.Icc (-W) W)).real
        {t | lambda * (3 : ℝ) ^ Q.card ≤ ‖routeETernaryReporter Q t‖} / (2 * W) ≤
        (((2 * W + 4 * (routeETernaryPrimorial Q : ℝ) ^ 2 *
            (1 + (Q.card : ℝ) * Real.log 3)) * (3 : ℝ) ^ Q.card) /
          (lambda * (3 : ℝ) ^ Q.card) ^ 2) / (2 * W) := by
      exact div_le_div_of_nonneg_right hbase (by positivity)
    _ = _ := by
      field_simp
      ring

/-- Equation (30f): reciprocal Gibbs large values carry the exact dissipative mass `V_Q`. -/
theorem routeETernaryWeightedReporter_largeValue_relativeMeasure_le
    (Q : Finset Nat.Primes) {W lambda : ℝ}
    (hW : 0 < W) (hlambda : 0 < lambda) :
    (volume.restrict (Set.Icc (-W) W)).real
        {t | lambda ≤ ‖routeETernaryWeightedReporter Q t‖} / (2 * W) ≤
      ((1 + 2 * (routeETernaryPrimorial Q : ℝ) ^ 2 *
          (1 + (Q.card : ℝ) * Real.log 3) / W) /
        lambda ^ 2) * routeETernaryWeightedMeanSquareMass Q := by
  have hbase := routeE_restrictVolume_norm_ge_le_of_intervalIntegral_sq_le
    (routeETernaryWeightedReporter Q)
    (continuous_routeETernaryWeightedReporter Q) hW hlambda
    (routeETernaryWeightedReporter_meanValue_le Q W)
  calc
    (volume.restrict (Set.Icc (-W) W)).real
        {t | lambda ≤ ‖routeETernaryWeightedReporter Q t‖} / (2 * W) ≤
        (((2 * W + 4 * (routeETernaryPrimorial Q : ℝ) ^ 2 *
            (1 + (Q.card : ℝ) * Real.log 3)) *
              routeETernaryWeightedMeanSquareMass Q) / lambda ^ 2) / (2 * W) := by
      exact div_le_div_of_nonneg_right hbase (by positivity)
    _ = _ := by
      field_simp
      ring

/-- Equation (28) with the large-value set written literally inside `[-W,W]`. -/
theorem routeETernaryReporter_largeValueSet_relativeMeasure_le
    (Q : Finset Nat.Primes) {W lambda : ℝ}
    (hW : 0 < W) (hlambda : 0 < lambda) :
    volume.real (Set.Icc (-W) W ∩
        {t | lambda * (3 : ℝ) ^ Q.card ≤ ‖routeETernaryReporter Q t‖}) / (2 * W) ≤
      (1 + 2 * (routeETernaryPrimorial Q : ℝ) ^ 2 *
          (1 + (Q.card : ℝ) * Real.log 3) / W) /
        (lambda ^ 2 * (3 : ℝ) ^ Q.card) := by
  simpa [Set.inter_comm] using
    routeETernaryReporter_largeValue_relativeMeasure_le Q hW hlambda

/-- Equation (30f) with the Gibbs large-value set written literally inside `[-W,W]`. -/
theorem routeETernaryWeightedReporter_largeValueSet_relativeMeasure_le
    (Q : Finset Nat.Primes) {W lambda : ℝ}
    (hW : 0 < W) (hlambda : 0 < lambda) :
    volume.real (Set.Icc (-W) W ∩
        {t | lambda ≤ ‖routeETernaryWeightedReporter Q t‖}) / (2 * W) ≤
      ((1 + 2 * (routeETernaryPrimorial Q : ℝ) ^ 2 *
          (1 + (Q.card : ℝ) * Real.log 3) / W) /
        lambda ^ 2) * routeETernaryWeightedMeanSquareMass Q := by
  simpa [Set.inter_comm] using
    routeETernaryWeightedReporter_largeValue_relativeMeasure_le Q hW hlambda

/-- Literal real-cosine form of one ternary local factor. -/
theorem routeETernaryLocalFactor_eq_cos
    (p : Nat.Primes) (t : ℝ) :
    1 - (starRingEnd ℂ) (phaseCovec t p) - phaseCovec t p =
      ((1 - 2 * Real.cos (t * Real.log (p : ℕ)) : ℝ) : ℂ) := by
  have hphase : phaseCovec t p =
      ((Real.cos (t * Real.log (p : ℕ)) : ℝ) : ℂ) -
        ((Real.sin (t * Real.log (p : ℕ)) : ℝ) : ℂ) * Complex.I := by
    rw [phaseCovec_eq]
    have hexponent :
        -(Complex.I * (((t * Real.log (p : ℕ) : ℝ)) : ℂ)) =
          (((-(t * Real.log (p : ℕ)) : ℝ)) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [hexponent, Complex.exp_mul_I]
    rw [← Complex.ofReal_cos, ← Complex.ofReal_sin]
    simp [Real.cos_neg, Real.sin_neg]
    ring
  rw [hphase]
  simp only [map_sub, map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

/-- Equation (20), exactly as a product of real cosine factors. -/
theorem routeETernaryReporter_eq_cosProduct
    (Q : Finset Nat.Primes) (t : ℝ) :
    routeETernaryReporter Q t =
      ∏ p : Q, ((1 - 2 * Real.cos (t * Real.log (p : ℕ)) : ℝ) : ℂ) := by
  rw [routeETernaryReporter]
  apply Finset.prod_congr rfl
  intro p hp
  exact routeETernaryLocalFactor_eq_cos p t

/-- Literal real-cosine form of one reciprocal Gibbs ternary factor. -/
theorem routeETernaryWeightedLocalFactor_eq_cos
    (p : Nat.Primes) (t : ℝ) :
    let u := routeETernaryReciprocalRadius p
    (1 - (u : ℂ) * (starRingEnd ℂ) (phaseCovec t p) -
      (u : ℂ) * phaseCovec t p) / (1 + 2 * u) =
        (((1 - 2 * u * Real.cos (t * Real.log (p : ℕ))) / (1 + 2 * u) : ℝ) : ℂ) := by
  dsimp only
  rw [show (1 - (routeETernaryReciprocalRadius p : ℂ) *
      (starRingEnd ℂ) (phaseCovec t p) -
      (routeETernaryReciprocalRadius p : ℂ) * phaseCovec t p) =
      1 - (routeETernaryReciprocalRadius p : ℂ) *
        ((starRingEnd ℂ) (phaseCovec t p) + phaseCovec t p) by ring]
  have hsum := routeETernaryLocalFactor_eq_cos p t
  have hsum' : (starRingEnd ℂ) (phaseCovec t p) + phaseCovec t p =
      ((2 * Real.cos (t * Real.log (p : ℕ)) : ℝ) : ℂ) := by
    calc
      (starRingEnd ℂ) (phaseCovec t p) + phaseCovec t p =
          1 - (1 - (starRingEnd ℂ) (phaseCovec t p) - phaseCovec t p) := by ring
      _ = 1 - ((1 - 2 * Real.cos (t * Real.log (p : ℕ)) : ℝ) : ℂ) := by
        rw [hsum]
      _ = _ := by push_cast; ring
  rw [hsum']
  push_cast
  ring

/-- Equation (30b), exactly as a product of reciprocal real-cosine factors. -/
theorem routeETernaryWeightedReporter_eq_cosProduct
    (Q : Finset Nat.Primes) (t : ℝ) :
    routeETernaryWeightedReporter Q t =
      ∏ p : Q,
        let u := routeETernaryReciprocalRadius p
        (((1 - 2 * u * Real.cos (t * Real.log (p : ℕ))) / (1 + 2 * u) : ℝ) : ℂ) := by
  rw [routeETernaryWeightedReporter]
  apply Finset.prod_congr rfl
  intro p hp
  exact routeETernaryWeightedLocalFactor_eq_cos p t

theorem primeFactorsIn_inter_eq_empty_of_coprime
    {P : Finset ℕ} (hPprime : ∀ p ∈ P, p.Prime) {n m : ℕ}
    (hnm : Nat.Coprime n m) :
    primeFactorsIn P n ∩ primeFactorsIn P m = ∅ := by
  ext p
  constructor
  · intro hpinter
    have hpn := (Finset.mem_inter.mp hpinter).1
    have hpm := (Finset.mem_inter.mp hpinter).2
    have hpP : p ∈ P := (mem_primeFactorsIn.mp hpn).1
    have hp : p.Prime := hPprime p hpP
    have hpdvd : p ∣ n.gcd m :=
      Nat.dvd_gcd (mem_primeFactorsIn.mp hpn).2 (mem_primeFactorsIn.mp hpm).2
    rw [hnm.gcd_eq_one] at hpdvd
    exact (hp.not_dvd_one hpdvd).elim
  · intro hpempty
    simp at hpempty

/-- Equation (14): common-prime incidence is exactly blind to coprime pairs. -/
theorem ramareIncidenceComplement_eq_one_of_coprime
    {P : Finset ℕ} (hPprime : ∀ p ∈ P, p.Prime) {n m : ℕ}
    (hnm : Nat.Coprime n m) :
    ramareIncidenceComplement P n m = 1 := by
  rw [ramareIncidenceComplement,
    primeFactorsIn_inter_eq_empty_of_coprime hPprime hnm]
  simp

theorem ramareSharedIncidenceRatio_self
    {P : Finset ℕ} {n : ℕ} (hn : (primeFactorsIn P n).Nonempty) :
    ramareSharedIncidenceRatio P n n = 1 / ((primeFactorsIn P n).card : ℝ) := by
  rw [ramareSharedIncidenceRatio, Finset.inter_self]
  have hc : ((primeFactorsIn P n).card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.mpr hn).ne'
  field_simp

theorem ramareIncidenceComplement_self
    {P : Finset ℕ} {n : ℕ} (hn : (primeFactorsIn P n).Nonempty) :
    ramareIncidenceComplement P n n =
      1 - 1 / ((primeFactorsIn P n).card : ℝ) := by
  rw [ramareIncidenceComplement, Finset.inter_self]
  have hc : ((primeFactorsIn P n).card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.mpr hn).ne'
  field_simp

theorem ramareMellinPairKernel_self {W : ℝ} (hW : 0 ≤ W) (n : ℕ) :
    ramareMellinPairKernel W n n = 2 * W := by
  rw [ramareMellinPairKernel]
  have hfun : (fun w : ℝ =>
      (unitLogPhase w n * (starRingEnd ℂ) (unitLogPhase w n)).re) = fun _ => 1 := by
    funext w
    rw [Complex.mul_conj, ← Complex.sq_norm, norm_unitLogPhase]
    norm_num
  rw [hfun, setIntegral_const, MeasureTheory.measureReal_def, Real.volume_Icc,
    ENNReal.toReal_ofReal (by linarith)]
  simp
  ring

theorem moebius_real_mul_self_eq_one_of_squarefree
    {n : ℕ} (hn : Squarefree n) :
    (((μ n : ℤ) : ℝ) * ((μ n : ℤ) : ℝ)) = 1 := by
  have hmu := ArithmeticFunction.moebius_sq_eq_one_of_squarefree hn
  have hmu' : μ n * μ n = 1 := by simpa [pow_two] using hmu
  exact_mod_cast hmu'

/-- Equation (11): split exact integer incidence into positive collisions and distinct pairs. -/
theorem ramarePrimeOffDiagonal_eq_collision_add_distinctInteger
    {P : Finset ℕ} (hPprime : ∀ p ∈ P, p.Prime) (M : ℕ) {W : ℝ} (hW : 0 ≤ W) :
    ramarePrimeOffDiagonal P M W =
      2 * W * (∑ n ∈ ramareSquarefreeActiveSet P M,
        (1 - 1 / ((primeFactorsIn P n).card : ℝ))) +
      ∑ n ∈ ramareSquarefreeActiveSet P M,
        ∑ m ∈ (ramareSquarefreeActiveSet P M).erase n,
          (((μ n : ℤ) : ℝ) * ((μ m : ℤ) : ℝ) * ramareIncidenceComplement P n m) *
            ramareMellinPairKernel W n m := by
  classical
  rw [ramarePrimeOffDiagonal_eq_squarefreeIntegerIncidence hPprime]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  rw [← Finset.add_sum_erase (ramareSquarefreeActiveSet P M)
    (fun m => (((μ n : ℤ) : ℝ) * ((μ m : ℤ) : ℝ) *
      ramareIncidenceComplement P n m) * ramareMellinPairKernel W n m) hn]
  have hsf : Squarefree n := (Finset.mem_filter.mp hn).2
  have hactive : n ∈ ramareActiveSet P M := (Finset.mem_filter.mp hn).1
  have hne : (primeFactorsIn P n).Nonempty := (Finset.mem_filter.mp hactive).2
  rw [moebius_real_mul_self_eq_one_of_squarefree hsf,
    one_mul, ramareIncidenceComplement_self hne,
    ramareMellinPairKernel_self hW]
  ring

/-- The integer shared-incidence diagonal is exactly the original prime-block diagonal. -/
theorem ramarePrimeDiagonalInteger_eq_primeBlockDiagonal
    {P : Finset ℕ} (hPprime : ∀ p ∈ P, p.Prime) (M : ℕ) (W : ℝ) :
    ramarePrimeDiagonalInteger P M W =
      ∑ p ∈ P, ∫ w in Set.Icc (-W) W, ‖ramareCofactorPoly P M p w‖ ^ 2 := by
  have hsum :
      (∫ w in Set.Icc (-W) W,
          ‖∑ n ∈ ramareSquarefreeActiveSet P M, moebiusPhase w n‖ ^ 2) =
        ∫ w in Set.Icc (-W) W, ‖ramareBilinear P M w‖ ^ 2 := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro w hw
    change ‖∑ n ∈ ramareSquarefreeActiveSet P M, moebiusPhase w n‖ ^ 2 =
      ‖ramareBilinear P M w‖ ^ 2
    rw [ramareBilinear_eq_squarefreeActiveSum hPprime]
  have htotal :=
    ramarePrimeDiagonal_add_offDiagonal_eq_integral_squarefreeActive hPprime M W
  rw [hsum, integral_normSq_ramareBilinear_eq hPprime M W] at htotal
  linarith

/-- Equation (15): same-integer collision is positive and costs at most `2 W M`. -/
theorem ramareCollision_nonneg_and_le
    (P : Finset ℕ) (M : ℕ) {W : ℝ} (hW : 0 ≤ W) :
    0 ≤ 2 * W * (∑ n ∈ ramareSquarefreeActiveSet P M,
        (1 - 1 / ((primeFactorsIn P n).card : ℝ))) ∧
    2 * W * (∑ n ∈ ramareSquarefreeActiveSet P M,
        (1 - 1 / ((primeFactorsIn P n).card : ℝ))) ≤ 2 * W * M := by
  have hterm : ∀ n ∈ ramareSquarefreeActiveSet P M,
      0 ≤ 1 - 1 / ((primeFactorsIn P n).card : ℝ) ∧
        1 - 1 / ((primeFactorsIn P n).card : ℝ) ≤ 1 := by
    intro n hn
    have hactive : n ∈ ramareActiveSet P M := (Finset.mem_filter.mp hn).1
    have hne : (primeFactorsIn P n).Nonempty := (Finset.mem_filter.mp hactive).2
    have hcNat : 1 ≤ (primeFactorsIn P n).card := Finset.one_le_card.mpr hne
    have hc : (1 : ℝ) ≤ ((primeFactorsIn P n).card : ℝ) := by exact_mod_cast hcNat
    have hcpos : (0 : ℝ) < ((primeFactorsIn P n).card : ℝ) := lt_of_lt_of_le zero_lt_one hc
    constructor
    · have hinv : 1 / ((primeFactorsIn P n).card : ℝ) ≤ 1 := by
        exact (div_le_one hcpos).2 hc
      linarith
    · have hinv : 0 ≤ 1 / ((primeFactorsIn P n).card : ℝ) := by positivity
      linarith
  have hsum0 : 0 ≤ ∑ n ∈ ramareSquarefreeActiveSet P M,
      (1 - 1 / ((primeFactorsIn P n).card : ℝ)) :=
    Finset.sum_nonneg fun n hn => (hterm n hn).1
  have hsumCard : (∑ n ∈ ramareSquarefreeActiveSet P M,
      (1 - 1 / ((primeFactorsIn P n).card : ℝ))) ≤
        (ramareSquarefreeActiveSet P M).card := by
    calc
      (∑ n ∈ ramareSquarefreeActiveSet P M,
          (1 - 1 / ((primeFactorsIn P n).card : ℝ))) ≤
          ∑ _n ∈ ramareSquarefreeActiveSet P M, (1 : ℝ) := by
        exact Finset.sum_le_sum fun n hn => (hterm n hn).2
      _ = (ramareSquarefreeActiveSet P M).card := by simp
  have hcard : (ramareSquarefreeActiveSet P M).card ≤ M := by
    have hsubset : ramareSquarefreeActiveSet P M ⊆ Finset.Icc 1 M := by
      intro n hn
      exact (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).1
    have hc := Finset.card_le_card hsubset
    simpa using hc
  constructor
  · positivity
  · have hsumM : (∑ n ∈ ramareSquarefreeActiveSet P M,
        (1 - 1 / ((primeFactorsIn P n).card : ℝ))) ≤ (M : ℝ) := by
      exact hsumCard.trans (by exact_mod_cast hcard)
    exact mul_le_mul_of_nonneg_left hsumM (mul_nonneg (by norm_num) hW)

end

end RHTower.Sieve
