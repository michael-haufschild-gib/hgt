import GaloisForLFunctions.RHTower.Sieve.HeathBrownDyadicPerron
import GaloisForLFunctions.RHTower.DivisorBound

/-!
# Coefficient bounds for dyadic Heath--Brown boxes

Every nonzero coefficient of a positive-degree box is an ordered multiplicative factorisation.
All Möbius and zeta factors have norm at most one, while the unique logarithmic factor contributes
at most `log n`.  Repeated divisor-fibre counting therefore gives an unconditional bound by a
fixed power of the divisor function times one logarithm.  The exponent depends only on the fixed
Heath--Brown degree, never on the cutoffs or dyadic choices.
-/

noncomputable section

namespace RHTower.Sieve

open Finset ArithmeticFunction

/-- Divisor count is monotone under divisibility away from zero. -/
theorem card_divisors_mono_of_dvd {a n : ℕ} (han : a ∣ n) (hn : n ≠ 0) :
    a.divisors.card ≤ n.divisors.card := by
  classical
  obtain ⟨c, rfl⟩ := han
  have ha : a ≠ 0 := by
    intro ha
    simp [ha] at hn
  have hc : c ≠ 0 := by
    intro hc
    simp [hc] at hn
  refine Finset.card_le_card_of_injOn (fun d : ℕ => d * c) ?_ ?_
  · intro d hd
    have hd' : d ∈ a.divisors := hd
    have hout : d * c ∈ (a * c).divisors := by
      rw [Nat.mem_divisors] at hd' ⊢
      exact ⟨Nat.mul_dvd_mul_right hd'.1 c, Nat.mul_ne_zero ha hc⟩
    exact hout
  · intro x hx y hy hxy
    exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hc) hxy

theorem card_divisorsAntidiagonal_eq_card_divisors (n : ℕ) :
    n.divisorsAntidiagonal.card = n.divisors.card := by
  rw [Finset.card_eq_sum_ones, Finset.card_eq_sum_ones,
    ← Nat.sum_divisorsAntidiagonal (fun _ _ => (1 : ℕ))]

/-- Product of `r` pointwise unit-bounded arithmetic functions has coefficients bounded by
`d(n)^r`.  This deliberately uniform form also covers empty products and is stable under further
convolution. -/
theorem norm_finsetProd_apply_le_divisors_pow
    {ι : Type*} (u : Finset ι) (F : ι → ArithmeticFunction ℝ)
    (hF : ∀ i ∈ u, ∀ n, ‖F i n‖ ≤ 1) (n : ℕ) :
    ‖(∏ i ∈ u, F i) n‖ ≤ (n.divisors.card : ℝ) ^ u.card := by
  classical
  induction u using Finset.induction_on generalizing n with
  | empty =>
      by_cases hn : n = 1 <;> simp [hn]
  | @insert a u ha ih =>
      rw [Finset.prod_insert ha, ArithmeticFunction.mul_apply]
      calc
        ‖∑ x ∈ n.divisorsAntidiagonal, F a x.1 * (∏ i ∈ u, F i) x.2‖
            ≤ ∑ x ∈ n.divisorsAntidiagonal,
                ‖F a x.1 * (∏ i ∈ u, F i) x.2‖ := norm_sum_le _ _
        _ ≤ ∑ _x ∈ n.divisorsAntidiagonal,
                (n.divisors.card : ℝ) ^ u.card := by
          apply Finset.sum_le_sum
          intro x hx
          have hn0 : n ≠ 0 := (Nat.mem_divisorsAntidiagonal.mp hx).2
          have hxn : x.2 ∣ n :=
            Nat.dvd_of_mem_divisors (Nat.snd_mem_divisors_of_mem_antidiagonal hx)
          have hcard : (x.2.divisors.card : ℝ) ≤ (n.divisors.card : ℝ) := by
            exact_mod_cast card_divisors_mono_of_dvd hxn hn0
          rw [norm_mul]
          calc
            ‖F a x.1‖ * ‖(∏ i ∈ u, F i) x.2‖
                ≤ 1 * ((x.2.divisors.card : ℝ) ^ u.card) := by
              gcongr
              · exact hF a (Finset.mem_insert_self a u) x.1
              · exact (ih (fun i hi => hF i (Finset.mem_insert_of_mem hi))) x.2
            _ ≤ (n.divisors.card : ℝ) ^ u.card := by
              simpa using pow_le_pow_left₀ (by positivity) hcard u.card
        _ = (n.divisors.card : ℝ) ^ (insert a u).card := by
          rw [Finset.sum_const, nsmul_eq_mul, card_divisorsAntidiagonal_eq_card_divisors,
            Finset.card_insert_of_notMem ha]
          ring

theorem norm_arithmeticDyadicBlock_le_one
    {F : ArithmeticFunction ℝ} (hF : ∀ n, ‖F n‖ ≤ 1) (q n : ℕ) :
    ‖arithmeticDyadicBlock F q n‖ ≤ 1 := by
  by_cases hq : Nat.log 2 n = q
  · simpa [arithmeticDyadicBlock, hq] using hF n
  · simp [arithmeticDyadicBlock, hq]

theorem norm_truncatedMoebius_le_one (L n : ℕ) :
    ‖truncatedMoebius L n‖ ≤ 1 := by
  by_cases hn : n ≤ L
  · rw [truncatedMoebius_apply, if_pos hn, Real.norm_eq_abs, ← Int.cast_abs]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  · simp [truncatedMoebius_apply, hn]

theorem norm_coeffTrunc_zeta_le_one (X n : ℕ) :
    ‖coeffTrunc (zeta : ArithmeticFunction ℝ) X n‖ ≤ 1 := by
  by_cases hnX : n ≤ X
  · rw [coeffTrunc_apply_of_le _ hnX]
    by_cases hn0 : n = 0 <;> simp [ArithmeticFunction.zeta_apply, hn0]
  · rw [coeffTrunc_apply_of_lt _ (Nat.lt_of_not_ge hnX)]
    simp

theorem norm_dyadicBlockProduct_le_divisors_pow
    {F : ArithmeticFunction ℝ} (hF : ∀ n, ‖F n‖ ≤ 1)
    (r : ℕ) (q : Fin r → ℕ) (n : ℕ) :
    ‖dyadicBlockProduct F r q n‖ ≤ (n.divisors.card : ℝ) ^ r := by
  simpa [dyadicBlockProduct] using
    norm_finsetProd_apply_le_divisors_pow (Finset.univ : Finset (Fin r))
      (fun i => arithmeticDyadicBlock F (q i))
      (fun i hi n => norm_arithmeticDyadicBlock_le_one hF (q i) n) n

/-- Convolution adds the divisor exponents and one extra fibre count. -/
theorem norm_mul_apply_le_divisors_pow_add_succ
    {F G : ArithmeticFunction ℝ} {r s : ℕ}
    (hF : ∀ n, ‖F n‖ ≤ (n.divisors.card : ℝ) ^ r)
    (hG : ∀ n, ‖G n‖ ≤ (n.divisors.card : ℝ) ^ s) (n : ℕ) :
    ‖(F * G) n‖ ≤ (n.divisors.card : ℝ) ^ (r + s + 1) := by
  rw [ArithmeticFunction.mul_apply]
  calc
    ‖∑ x ∈ n.divisorsAntidiagonal, F x.1 * G x.2‖
        ≤ ∑ x ∈ n.divisorsAntidiagonal, ‖F x.1 * G x.2‖ := norm_sum_le _ _
    _ ≤ ∑ _x ∈ n.divisorsAntidiagonal,
        (n.divisors.card : ℝ) ^ (r + s) := by
      apply Finset.sum_le_sum
      intro x hx
      have hn0 : n ≠ 0 := (Nat.mem_divisorsAntidiagonal.mp hx).2
      have hx1 : x.1 ∣ n :=
        Nat.dvd_of_mem_divisors (Nat.fst_mem_divisors_of_mem_antidiagonal hx)
      have hx2 : x.2 ∣ n :=
        Nat.dvd_of_mem_divisors (Nat.snd_mem_divisors_of_mem_antidiagonal hx)
      have hc1 : (x.1.divisors.card : ℝ) ≤ (n.divisors.card : ℝ) := by
        exact_mod_cast card_divisors_mono_of_dvd hx1 hn0
      have hc2 : (x.2.divisors.card : ℝ) ≤ (n.divisors.card : ℝ) := by
        exact_mod_cast card_divisors_mono_of_dvd hx2 hn0
      rw [norm_mul]
      calc
        ‖F x.1‖ * ‖G x.2‖
            ≤ ((x.1.divisors.card : ℝ) ^ r) *
                ((x.2.divisors.card : ℝ) ^ s) := mul_le_mul (hF x.1) (hG x.2)
              (norm_nonneg _) (by positivity)
        _ ≤ ((n.divisors.card : ℝ) ^ r) *
                ((n.divisors.card : ℝ) ^ s) := by gcongr
        _ = (n.divisors.card : ℝ) ^ (r + s) := by rw [← pow_add]
    _ = (n.divisors.card : ℝ) ^ (r + s + 1) := by
      rw [Finset.sum_const, nsmul_eq_mul, card_divisorsAntidiagonal_eq_card_divisors]
      rw [pow_succ']

theorem norm_arithmeticDyadicLogBlock_le_log
    (X q : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    ‖arithmeticDyadicBlock (coeffTrunc ArithmeticFunction.log X) q n‖ ≤
      Real.log (n : ℝ) := by
  by_cases hq : Nat.log 2 n = q
  · rw [arithmeticDyadicBlock_apply, if_pos hq]
    by_cases hnX : n ≤ X
    · rw [coeffTrunc_apply_of_le _ hnX, ArithmeticFunction.log_apply,
        Real.norm_eq_abs, abs_of_nonneg]
      exact Real.log_nonneg (by exact_mod_cast hn)
    · rw [coeffTrunc_apply_of_lt _ (Nat.lt_of_not_ge hnX), norm_zero]
      exact Real.log_nonneg (by exact_mod_cast hn)
  · rw [arithmeticDyadicBlock_apply, if_neg hq, norm_zero]
    exact Real.log_nonneg (by exact_mod_cast hn)

/-- A divisor-power coefficient convolved with one logarithmic block keeps exactly one logarithm. -/
theorem norm_mul_dyadicLogBlock_le_divisors_pow_mul_log
    {F : ArithmeticFunction ℝ} {r X q : ℕ}
    (hF : ∀ n, ‖F n‖ ≤ (n.divisors.card : ℝ) ^ r)
    {n : ℕ} (hn : 1 ≤ n) :
    ‖(F * arithmeticDyadicBlock (coeffTrunc ArithmeticFunction.log X) q) n‖ ≤
      (n.divisors.card : ℝ) ^ (r + 1) * Real.log (n : ℝ) := by
  rw [ArithmeticFunction.mul_apply]
  calc
    ‖∑ x ∈ n.divisorsAntidiagonal,
        F x.1 * arithmeticDyadicBlock (coeffTrunc ArithmeticFunction.log X) q x.2‖
        ≤ ∑ x ∈ n.divisorsAntidiagonal,
          ‖F x.1 * arithmeticDyadicBlock
            (coeffTrunc ArithmeticFunction.log X) q x.2‖ := norm_sum_le _ _
    _ ≤ ∑ _x ∈ n.divisorsAntidiagonal,
        (n.divisors.card : ℝ) ^ r * Real.log (n : ℝ) := by
      apply Finset.sum_le_sum
      intro x hx
      have hn0 : n ≠ 0 := by omega
      have hx1mem := Nat.fst_mem_divisors_of_mem_antidiagonal hx
      have hx2mem := Nat.snd_mem_divisors_of_mem_antidiagonal hx
      have hx1 : x.1 ∣ n := Nat.dvd_of_mem_divisors hx1mem
      have hx2 : x.2 ∣ n := Nat.dvd_of_mem_divisors hx2mem
      have hx2pos : 1 ≤ x.2 := Nat.pos_of_mem_divisors hx2mem
      have hx2le : x.2 ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hx2
      have hc1 : (x.1.divisors.card : ℝ) ≤ (n.divisors.card : ℝ) := by
        exact_mod_cast card_divisors_mono_of_dvd hx1 hn0
      have hlog : Real.log (x.2 : ℝ) ≤ Real.log (n : ℝ) := by
        exact Real.log_le_log (by positivity) (by exact_mod_cast hx2le)
      rw [norm_mul]
      calc
        ‖F x.1‖ *
            ‖arithmeticDyadicBlock (coeffTrunc ArithmeticFunction.log X) q x.2‖
            ≤ ((x.1.divisors.card : ℝ) ^ r) * Real.log (x.2 : ℝ) :=
              mul_le_mul (hF x.1) (norm_arithmeticDyadicLogBlock_le_log X q hx2pos)
                (norm_nonneg _) (by positivity)
        _ ≤ (n.divisors.card : ℝ) ^ r * Real.log (n : ℝ) := by gcongr
    _ = (n.divisors.card : ℝ) ^ (r + 1) * Real.log (n : ℝ) := by
      rw [Finset.sum_const, nsmul_eq_mul, card_divisorsAntidiagonal_eq_card_divisors]
      rw [pow_succ']
      ring

/-- **Coefficient-exact dyadic core bound.**  Uniform in all cutoffs and dyadic choices; only the
fixed degree `j` controls the divisor exponent, and only one logarithm is lost. -/
theorem norm_heathBrownDyadicCoreBox_le_divisors_pow_mul_log
    (L X j : ℕ) (a : Fin j → ℕ) (b : Fin (j - 1) → ℕ) (q : ℕ)
    {n : ℕ} (hn : 1 ≤ n) :
    ‖heathBrownDyadicCoreBox L X j a b q n‖ ≤
      (n.divisors.card : ℝ) ^ (j + (j - 1) + 2) * Real.log (n : ℝ) := by
  rw [heathBrownDyadicCoreBox]
  apply norm_mul_dyadicLogBlock_le_divisors_pow_mul_log
  apply norm_mul_apply_le_divisors_pow_add_succ
  · exact norm_dyadicBlockProduct_le_divisors_pow
      (norm_truncatedMoebius_le_one L) j a
  · exact norm_dyadicBlockProduct_le_divisors_pow
      (norm_coeffTrunc_zeta_le_one X) (j - 1) b
  exact hn

/-- A natural arithmetic-function scalar acts by ordinary coefficient scaling under Dirichlet
convolution. -/
theorem natCast_mul_apply (c n : ℕ) (F : ArithmeticFunction ℝ) :
    ((c : ArithmeticFunction ℝ) * F) n = (c : ℝ) * F n := by
  induction c with
  | zero => simp
  | succ c ih =>
      rw [Nat.cast_succ, add_mul, ArithmeticFunction.add_apply, ih, one_mul]
      push_cast
      ring

/-- The alternating sign in a Heath--Brown term does not change coefficient norms. -/
theorem norm_negOnePow_mul_apply (p n : ℕ) (F : ArithmeticFunction ℝ) :
    ‖(((-1 : ArithmeticFunction ℝ) ^ p) * F) n‖ = ‖F n‖ := by
  rcases neg_one_pow_eq_or (ArithmeticFunction ℝ) p with hs | hs
  · rw [hs]
    simp
  · rw [hs]
    simp

/-- Complete signed boxes inherit the core divisor bound, with only the fixed binomial scalar. -/
theorem norm_heathBrownDyadicTermBox_le_divisors_pow_mul_log
    (L X k m : ℕ) (a : Fin (k - m) → ℕ) (b : Fin (k - m - 1) → ℕ) (q : ℕ)
    {n : ℕ} (hn : 1 ≤ n) :
    ‖heathBrownDyadicTermBox L X k m a b q n‖ ≤
      (k.choose m : ℝ) *
        ((n.divisors.card : ℝ) ^ ((k - m) + (k - m - 1) + 2) *
          Real.log (n : ℝ)) := by
  rw [heathBrownDyadicTermBox, mul_assoc, norm_negOnePow_mul_apply, natCast_mul_apply,
    norm_mul, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ k.choose m)]
  exact mul_le_mul_of_nonneg_left
    (norm_heathBrownDyadicCoreBox_le_divisors_pow_mul_log
      L X (k - m) a b q hn) (by positivity)

/-- Complex coefficient form consumed by Perron and Dirichlet-polynomial estimates. -/
theorem norm_complexCoeff_heathBrownDyadicTermBox_le_divisors_pow_mul_log
    (L X k m : ℕ) (a : Fin (k - m) → ℕ) (b : Fin (k - m - 1) → ℕ) (q : ℕ)
    {n : ℕ} (hn : 1 ≤ n) :
    ‖complexCoeff (heathBrownDyadicTermBox L X k m a b q) n‖ ≤
      (k.choose m : ℝ) *
        ((n.divisors.card : ℝ) ^ ((k - m) + (k - m - 1) + 2) *
          Real.log (n : ℝ)) := by
  simpa [complexCoeff_apply, Complex.norm_real, Real.norm_eq_abs] using
    norm_heathBrownDyadicTermBox_le_divisors_pow_mul_log L X k m a b q hn

/-- **Arbitrarily small-power coefficient bound for every fixed signed box.**  The constant depends
only on `ε`, `k`, and `m`; it is independent of both cutoffs and every dyadic choice. -/
theorem exists_norm_complexCoeff_heathBrownDyadicTermBox_le_rpow_mul_log
    {ε : ℝ} (hε : 0 < ε) (k m : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (L X : ℕ) (a : Fin (k - m) → ℕ) (b : Fin (k - m - 1) → ℕ)
        (q n : ℕ), 1 ≤ n →
        ‖complexCoeff (heathBrownDyadicTermBox L X k m a b q) n‖ ≤
          (k.choose m : ℝ) * C * (n : ℝ) ^ ε * Real.log (n : ℝ) := by
  let r : ℕ := (k - m) + (k - m - 1) + 2
  have hr : 0 < r := by
    dsimp [r]
    omega
  have hδ : 0 < ε / (r : ℝ) := div_pos hε (by exact_mod_cast hr)
  obtain ⟨C₀, hC₀, hdiv⟩ := RHTower.card_divisors_le_const_mul_rpow hδ
  refine ⟨C₀ ^ r, pow_pos hC₀ r, ?_⟩
  intro L X a b q n hn
  have hdivn := hdiv n hn
  have hnstep : ((n : ℝ) ^ (ε / (r : ℝ))) ^ r =
      (n : ℝ) ^ ((ε / (r : ℝ)) * (r : ℝ)) := by
    calc
      ((n : ℝ) ^ (ε / (r : ℝ))) ^ r =
          ((n : ℝ) ^ (ε / (r : ℝ))) ^ (r : ℝ) :=
            (Real.rpow_natCast _ r).symm
      _ = (n : ℝ) ^ ((ε / (r : ℝ)) * (r : ℝ)) :=
            (Real.rpow_mul (by positivity) _ _).symm
  have hpow : (n.divisors.card : ℝ) ^ r ≤
      C₀ ^ r * (n : ℝ) ^ ε := by
    calc
      (n.divisors.card : ℝ) ^ r
          ≤ (C₀ * (n : ℝ) ^ (ε / (r : ℝ))) ^ r :=
            pow_le_pow_left₀ (by positivity) hdivn r
      _ = C₀ ^ r * ((n : ℝ) ^ (ε / (r : ℝ))) ^ r := by rw [mul_pow]
      _ = C₀ ^ r * (n : ℝ) ^ ((ε / (r : ℝ)) * (r : ℝ)) := by
            rw [hnstep]
      _ = C₀ ^ r * (n : ℝ) ^ ε := by
            have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hr)
            rw [div_mul_cancel₀ ε hr0]
  have hbase := norm_complexCoeff_heathBrownDyadicTermBox_le_divisors_pow_mul_log
    L X k m a b q hn
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  calc
    ‖complexCoeff (heathBrownDyadicTermBox L X k m a b q) n‖
        ≤ (k.choose m : ℝ) *
          ((n.divisors.card : ℝ) ^ r * Real.log (n : ℝ)) := by
            simpa [r] using hbase
    _ ≤ (k.choose m : ℝ) *
          ((C₀ ^ r * (n : ℝ) ^ ε) * Real.log (n : ℝ)) := by
            gcongr
    _ = (k.choose m : ℝ) * C₀ ^ r * (n : ℝ) ^ ε *
          Real.log (n : ℝ) := by ring

/-- Uniform prefix form: on `1 ≤ n ≤ M`, one constant controls every coefficient by
`M^ε log M`. -/
theorem exists_norm_complexCoeff_heathBrownDyadicTermBox_le_prefix_rpow_mul_log
    {ε : ℝ} (hε : 0 < ε) (k m : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (L X : ℕ) (a : Fin (k - m) → ℕ) (b : Fin (k - m - 1) → ℕ)
        (q M n : ℕ), 1 ≤ n → n ≤ M →
        ‖complexCoeff (heathBrownDyadicTermBox L X k m a b q) n‖ ≤
          (k.choose m : ℝ) * C * (M : ℝ) ^ ε * Real.log (M : ℝ) := by
  obtain ⟨C, hC, hbox⟩ :=
    exists_norm_complexCoeff_heathBrownDyadicTermBox_le_rpow_mul_log hε k m
  refine ⟨C, hC, ?_⟩
  intro L X a b q M n hn hnM
  have hM : 1 ≤ M := hn.trans hnM
  have hpow : (n : ℝ) ^ ε ≤ (M : ℝ) ^ ε :=
    Real.rpow_le_rpow (by positivity) (by exact_mod_cast hnM) hε.le
  have hlog : Real.log (n : ℝ) ≤ Real.log (M : ℝ) :=
    Real.log_le_log (by positivity) (by exact_mod_cast hnM)
  calc
    ‖complexCoeff (heathBrownDyadicTermBox L X k m a b q) n‖
        ≤ (k.choose m : ℝ) * C * (n : ℝ) ^ ε * Real.log (n : ℝ) :=
          hbox L X a b q n hn
    _ ≤ (k.choose m : ℝ) * C * (M : ℝ) ^ ε * Real.log (M : ℝ) := by
      gcongr

end RHTower.Sieve
