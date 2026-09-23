import GaloisForLFunctions.RHTower.Sieve.CriticalDivisorAffineMeanSquare
import GaloisForLFunctions.RHTower.Sieve.IntervalMultiples

/-!
# Short intervals for fixed generalized-divisor coefficients

The product-scale boundary in Matomäki--Teräväinen's Proposition 2.2 is a genuinely short
multiplicative collar.  A prefix divisor-moment estimate loses that collar.  This file proves the
elementary local replacement: if `T ^ r ≤ L`, then every ordered `r`-factorization of an integer in
`(L,U]` has a factor larger than `T`.  Distinguished-factor summation gives a main term of length
`U-L` and an endpoint error of size `U/T`.

No short-interval theorem about primes is used here; this is finite hyperbola summation only.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction
open scoped ArithmeticFunction.zeta

noncomputable section

/-- Positive integers at most `T`, viewed as a truncated zeta coefficient sequence. -/
def generalizedDivisorHeadZeta (T : ℕ) : ArithmeticFunction ℕ :=
  ⟨fun n => if 0 < n ∧ n ≤ T then 1 else 0, by simp⟩

/-- Positive integers larger than `T`, viewed as the complementary zeta coefficient sequence. -/
def generalizedDivisorTailZeta (T : ℕ) : ArithmeticFunction ℕ :=
  ⟨fun n => if T < n then 1 else 0, by simp⟩

theorem generalizedDivisorHeadZeta_add_tailZeta (T : ℕ) :
    generalizedDivisorHeadZeta T + generalizedDivisorTailZeta T =
      (ArithmeticFunction.zeta : ArithmeticFunction ℕ) := by
  ext n
  rcases n.eq_zero_or_pos with rfl | hn
  · simp [generalizedDivisorHeadZeta, generalizedDivisorTailZeta]
  · by_cases hnT : n ≤ T
    · have hn0 : n ≠ 0 := Nat.ne_of_gt hn
      have hTn : ¬T < n := not_lt_of_ge hnT
      simp [generalizedDivisorHeadZeta, generalizedDivisorTailZeta, hn, hn0, hnT, hTn,
        ArithmeticFunction.zeta_apply]
    · have hTn : T < n := lt_of_not_ge hnT
      have hn0 : n ≠ 0 := Nat.ne_of_gt hn
      simp [generalizedDivisorHeadZeta, generalizedDivisorTailZeta, hn, hn0, hnT, hTn,
        ArithmeticFunction.zeta_apply]

/-- Dirichlet convolution preserves coefficientwise inequalities over `ℕ`. -/
theorem arithmeticFunction_mul_apply_le_mul_apply
    {f₁ f₂ g₁ g₂ : ArithmeticFunction ℕ}
    (hf : ∀ n, f₁ n ≤ f₂ n) (hg : ∀ n, g₁ n ≤ g₂ n) (n : ℕ) :
    (f₁ * g₁) n ≤ (f₂ * g₂) n := by
  rw [ArithmeticFunction.mul_apply, ArithmeticFunction.mul_apply]
  apply Finset.sum_le_sum
  intro de hde
  exact Nat.mul_le_mul (hf de.1) (hg de.2)

/-- Powers preserve coefficientwise inequalities over nonnegative arithmetic functions. -/
theorem arithmeticFunction_pow_apply_le_pow_apply
    {f g : ArithmeticFunction ℕ} (hfg : ∀ n, f n ≤ g n) (r n : ℕ) :
    (f ^ r) n ≤ (g ^ r) n := by
  induction r generalizing n with
  | zero => simp
  | succ r ih =>
      rw [pow_succ, pow_succ]
      exact arithmeticFunction_mul_apply_le_mul_apply ih hfg n

theorem generalizedDivisorHeadZeta_apply_le_zeta (T n : ℕ) :
    generalizedDivisorHeadZeta T n ≤
      (ArithmeticFunction.zeta : ArithmeticFunction ℕ) n := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp [generalizedDivisorHeadZeta]
  · have hn0 : n ≠ 0 := Nat.ne_of_gt hn
    rw [ArithmeticFunction.zeta_apply_ne hn0]
    change (if 0 < n ∧ n ≤ T then 1 else 0) ≤ 1
    split <;> omega

/-- A product of `r` head factors is supported on integers at most `T ^ r`. -/
theorem generalizedDivisorHeadZeta_pow_apply_eq_zero_of_pow_lt
    (T r n : ℕ) (hpow : T ^ r < n) :
    (generalizedDivisorHeadZeta T ^ r) n = 0 := by
  induction r generalizing n with
  | zero =>
      norm_num at hpow
      have hn1 : n ≠ 1 := by omega
      simp [hn1]
  | succ r ih =>
      rw [pow_succ, ArithmeticFunction.mul_apply]
      apply Finset.sum_eq_zero
      intro de hde
      by_cases hleft : (generalizedDivisorHeadZeta T ^ r) de.1 = 0
      · simp [hleft]
      have hleftScale : de.1 ≤ T ^ r := by
        by_contra hnot
        exact hleft (ih de.1 (lt_of_not_ge hnot))
      by_cases hright : generalizedDivisorHeadZeta T de.2 = 0
      · simp [hright]
      have hrightScale : de.2 ≤ T := by
        by_contra hnot
        have hT : T < de.2 := lt_of_not_ge hnot
        exact hright (by simp [generalizedDivisorHeadZeta, hT])
      obtain ⟨hprod, _hn0⟩ := Nat.mem_divisorsAntidiagonal.mp hde
      have hscale : de.1 * de.2 ≤ T ^ r * T :=
        Nat.mul_le_mul hleftScale hrightScale
      have : n ≤ T ^ (r + 1) := by
        rw [pow_succ]
        simpa [hprod] using hscale
      omega

/-- Difference-of-powers identity in subtraction-free form. -/
theorem pow_eq_pow_add_mul_geometricSum
    {R : Type*} [CommSemiring R] (a b c : R) (habc : a = b + c) (r : ℕ) :
    a ^ r = b ^ r + c * ∑ j ∈ Finset.range r, a ^ j * b ^ (r - 1 - j) := by
  subst a
  induction r with
  | zero => simp
  | succ r ih =>
      have hsum :
          ∑ j ∈ Finset.range (r + 1), (b + c) ^ j * b ^ (r + 1 - 1 - j) =
            (∑ j ∈ Finset.range r, (b + c) ^ j * b ^ (r - 1 - j)) * b +
              (b + c) ^ r := by
        rw [Finset.sum_range_succ, Finset.sum_mul]
        apply congrArg₂ (· + ·)
        · apply Finset.sum_congr rfl
          intro j hj
          have hjr : j < r := Finset.mem_range.mp hj
          rw [show r + 1 - 1 - j = r - j by omega]
          rw [show r - j = (r - 1 - j) + 1 by omega, pow_succ]
          ring
        · simp
      rw [pow_succ, ih, hsum, ih]
      ring

private theorem generalizedDivisor_finset_sum_apply
    {ι : Type*} (S : Finset ι) (F : ι → ArithmeticFunction ℕ) (n : ℕ) :
    (∑ i ∈ S, F i) n = ∑ i ∈ S, F i n := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih => simp [hi, ih]

/-- Above `T ^ r`, every `r`-fold zeta coefficient is paid by one distinguished tail factor.
The factor `r` is the union bound over its possible positions. -/
theorem zeta_pow_apply_le_card_mul_tailZeta_mul_zeta_pow
    (T r n : ℕ) (hr : 1 ≤ r) (hpow : T ^ r < n) :
    ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ r) n ≤
      r * ((generalizedDivisorTailZeta T) *
        (ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ (r - 1)) n := by
  let z := (ArithmeticFunction.zeta : ArithmeticFunction ℕ)
  let head := generalizedDivisorHeadZeta T
  let tail := generalizedDivisorTailZeta T
  have hz : z = head + tail := by
    simpa [z, head, tail] using (generalizedDivisorHeadZeta_add_tailZeta T).symm
  have hid := pow_eq_pow_add_mul_geometricSum z head tail hz r
  have hheadZero : (head ^ r) n = 0 := by
    simpa [head] using generalizedDivisorHeadZeta_pow_apply_eq_zero_of_pow_lt T r n hpow
  have hmixed : ∀ j ∈ Finset.range r, ∀ m,
      (z ^ j * head ^ (r - 1 - j)) m ≤ (z ^ (r - 1)) m := by
    intro j hj m
    have hjr : j < r := Finset.mem_range.mp hj
    calc
      (z ^ j * head ^ (r - 1 - j)) m ≤
          (z ^ j * z ^ (r - 1 - j)) m :=
        arithmeticFunction_mul_apply_le_mul_apply (fun _ => le_rfl)
          (fun k => arithmeticFunction_pow_apply_le_pow_apply
            (generalizedDivisorHeadZeta_apply_le_zeta T) (r - 1 - j) k) m
      _ = (z ^ (r - 1)) m := by
        rw [← pow_add]
        congr 2
        omega
  have htailMixed : ∀ j ∈ Finset.range r,
      (tail * (z ^ j * head ^ (r - 1 - j))) n ≤
        (tail * z ^ (r - 1)) n := by
    intro j hj
    exact arithmeticFunction_mul_apply_le_mul_apply (fun _ => le_rfl) (hmixed j hj) n
  have hidn := congrArg (fun f : ArithmeticFunction ℕ => f n) hid
  simp only [ArithmeticFunction.add_apply, hheadZero, zero_add] at hidn
  rw [hidn]
  rw [Finset.mul_sum]
  rw [generalizedDivisor_finset_sum_apply]
  calc
    ∑ j ∈ Finset.range r, (tail * (z ^ j * head ^ (r - 1 - j))) n ≤
        ∑ _j ∈ Finset.range r, (tail * z ^ (r - 1)) n :=
      Finset.sum_le_sum htailMixed
    _ = r * (tail * z ^ (r - 1)) n := by simp
    _ = r * (generalizedDivisorTailZeta T *
        (ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ (r - 1)) n := by
      rfl

/-- The tail-zeta prefix is the literal number of integers in `(T,N]`. -/
theorem sum_generalizedDivisorTailZeta_Icc (T N : ℕ) :
    ∑ d ∈ Finset.Icc 1 N, generalizedDivisorTailZeta T d = N - T := by
  change ∑ d ∈ Finset.Icc 1 N, (if T < d then 1 else 0) = N - T
  rw [← Finset.card_filter]
  calc
    #{d ∈ Finset.Icc 1 N | T < d} = #(Finset.Ioc T N) := by
      congr 1
      ext d
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
      omega
    _ = N - T := Nat.card_Ioc T N

/-- Hyperbola summation with one distinguished factor above `T`. -/
theorem sum_Icc_zeta_pow_mul_tailZeta
    (r T N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N,
        (((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ r) *
          generalizedDivisorTailZeta T) n =
      ∑ m ∈ Finset.Icc 1 N,
        ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ r) m * (N / m - T) := by
  rw [RHTower.sum_Icc_mul_apply]
  apply Finset.sum_congr rfl
  intro m hm
  rw [sum_generalizedDivisorTailZeta_Icc]

private theorem sum_Ioc_natCast_eq_sum_Icc_sub
    (f : ℕ → ℕ) {L U : ℕ} (hL : 1 ≤ L) (hLU : L ≤ U) :
    ∑ n ∈ Finset.Ioc L U, (f n : ℝ) =
      (∑ n ∈ Finset.Icc 1 U, (f n : ℝ)) -
        ∑ n ∈ Finset.Icc 1 L, (f n : ℝ) := by
  have hunion : Finset.Icc 1 L ∪ Finset.Ioc L U = Finset.Icc 1 U := by
    ext n
    simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc]
    omega
  have hdisj : Disjoint (Finset.Icc 1 L) (Finset.Ioc L U) := by
    rw [Finset.disjoint_left]
    intro n hnL hnU
    simp only [Finset.mem_Icc] at hnL
    simp only [Finset.mem_Ioc] at hnU
    omega
  have hsum := Finset.sum_union hdisj (f := fun n => (f n : ℝ))
  rw [hunion] at hsum
  linarith

/-- Exact distinguished-factor formula on a short interval.  Only complementary products
`m ≤ U/T` can occur. -/
theorem sum_Ioc_zeta_pow_mul_tailZeta_cast_eq
    (r T L U : ℕ) (hT : 1 ≤ T) (hL : 1 ≤ L) (hLU : L ≤ U) :
    ∑ n ∈ Finset.Ioc L U,
        (((((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ r) *
          generalizedDivisorTailZeta T) n : ℕ) : ℝ) =
      ∑ m ∈ Finset.Icc 1 (U / T),
        (((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ r) m : ℝ) *
          ((((U / m - T : ℕ) : ℝ) - ((L / m - T : ℕ) : ℝ))) := by
  let a := fun m => ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ r) m
  have hinterval := sum_Ioc_natCast_eq_sum_Icc_sub
    (fun n => ((((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ r) *
      generalizedDivisorTailZeta T) n)) hL hLU
  have hprefixU :
      ∑ n ∈ Finset.Icc 1 U,
          (((((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ r) *
            generalizedDivisorTailZeta T) n : ℕ) : ℝ) =
        ∑ m ∈ Finset.Icc 1 U, (a m : ℝ) * ((U / m - T : ℕ) : ℝ) := by
    exact_mod_cast sum_Icc_zeta_pow_mul_tailZeta r T U
  have hprefixL :
      ∑ n ∈ Finset.Icc 1 L,
          (((((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ r) *
            generalizedDivisorTailZeta T) n : ℕ) : ℝ) =
        ∑ m ∈ Finset.Icc 1 L, (a m : ℝ) * ((L / m - T : ℕ) : ℝ) := by
    exact_mod_cast sum_Icc_zeta_pow_mul_tailZeta r T L
  have hsetLU : Finset.Icc 1 L ⊆ Finset.Icc 1 U :=
    Finset.Icc_subset_Icc le_rfl hLU
  have hextendL :
      ∑ m ∈ Finset.Icc 1 L, (a m : ℝ) * ((L / m - T : ℕ) : ℝ) =
        ∑ m ∈ Finset.Icc 1 U, (a m : ℝ) * ((L / m - T : ℕ) : ℝ) := by
    apply Finset.sum_subset hsetLU
    intro m hmU hmL
    have hmData := Finset.mem_Icc.mp hmU
    have hmOutside : L < m := by
      by_contra hnot
      exact hmL (Finset.mem_Icc.mpr ⟨hmData.1, le_of_not_gt hnot⟩)
    have hdiv : L / m = 0 := Nat.div_eq_of_lt hmOutside
    simp [hdiv]
  have hsetUT : Finset.Icc 1 (U / T) ⊆ Finset.Icc 1 U :=
    Finset.Icc_subset_Icc le_rfl (Nat.div_le_self U T)
  calc
    ∑ n ∈ Finset.Ioc L U,
        (((((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ r) *
          generalizedDivisorTailZeta T) n : ℕ) : ℝ) =
        (∑ n ∈ Finset.Icc 1 U,
          (((((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ r) *
            generalizedDivisorTailZeta T) n : ℕ) : ℝ)) -
          ∑ n ∈ Finset.Icc 1 L,
            (((((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ r) *
              generalizedDivisorTailZeta T) n : ℕ) : ℝ) := hinterval
    _ = (∑ m ∈ Finset.Icc 1 U, (a m : ℝ) * ((U / m - T : ℕ) : ℝ)) -
          ∑ m ∈ Finset.Icc 1 U, (a m : ℝ) * ((L / m - T : ℕ) : ℝ) := by
      rw [hprefixU, hprefixL, hextendL]
    _ = ∑ m ∈ Finset.Icc 1 U, (a m : ℝ) *
          (((U / m - T : ℕ) : ℝ) - ((L / m - T : ℕ) : ℝ)) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro m hm
      ring
    _ = ∑ m ∈ Finset.Icc 1 (U / T), (a m : ℝ) *
          (((U / m - T : ℕ) : ℝ) - ((L / m - T : ℕ) : ℝ)) := by
      symm
      apply Finset.sum_subset hsetUT
      intro m hmU hmUT
      have hmData := Finset.mem_Icc.mp hmU
      have hmOutside : U / T < m := by
        by_contra hnot
        exact hmUT (Finset.mem_Icc.mpr ⟨hmData.1, le_of_not_gt hnot⟩)
      have hUmul : U < m * T := Nat.lt_mul_of_div_lt hmOutside hT
      have hUdiv : U / m < T := Nat.div_lt_of_lt_mul hUmul
      have hLdiv : L / m < T :=
        (Nat.div_le_div_right hLU).trans_lt hUdiv
      simp [Nat.sub_eq_zero_of_le hUdiv.le, Nat.sub_eq_zero_of_le hLdiv.le]
    _ = ∑ m ∈ Finset.Icc 1 (U / T),
        (((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ r) m : ℝ) *
          (((U / m - T : ℕ) : ℝ) - ((L / m - T : ℕ) : ℝ)) := rfl

/-- Removing the same lower cutoff from two quotient counts costs at most the usual interval
length divided by the modulus, plus one endpoint. -/
theorem tailQuotientDifference_le_length_div_add_one
    (T L U m : ℕ) (hm : 1 ≤ m) (hLU : L ≤ U) :
    ((U / m - T : ℕ) : ℝ) - ((L / m - T : ℕ) : ℝ) ≤
      ((U - L : ℕ) : ℝ) / (m : ℝ) + 1 := by
  have hquot : L / m ≤ U / m := Nat.div_le_div_right hLU
  have hclip : L / m - T ≤ U / m - T := Nat.sub_le_sub_right hquot T
  have hclipDiff :
      U / m - T - (L / m - T) ≤ U / m - L / m := by omega
  have hquotCast :
      ((U / m - L / m : ℕ) : ℝ) =
        ((U / m : ℕ) : ℝ) - ((L / m : ℕ) : ℝ) := by
    rw [Nat.cast_sub hquot]
  obtain ⟨hUlower, _hUupper⟩ := cast_div_bounds (d := m) (n := U) hm
  obtain ⟨_hLlower, hLupper⟩ := cast_div_bounds (d := m) (n := L) hm
  calc
    ((U / m - T : ℕ) : ℝ) - ((L / m - T : ℕ) : ℝ) =
        ((U / m - T - (L / m - T) : ℕ) : ℝ) := by
      rw [Nat.cast_sub hclip]
    _ ≤ ((U / m - L / m : ℕ) : ℝ) := by exact_mod_cast hclipDiff
    _ = ((U / m : ℕ) : ℝ) - ((L / m : ℕ) : ℝ) := hquotCast
    _ ≤ ((U - L : ℕ) : ℝ) / (m : ℝ) + 1 := by
      rw [Nat.cast_sub hLU]
      have hmR : (0 : ℝ) < m := by exact_mod_cast hm
      rw [sub_div]
      linarith

/-- Local convolution bound before estimating the two generalized-divisor prefix moments. -/
theorem sum_Ioc_zeta_pow_mul_tailZeta_cast_le
    (r T L U : ℕ) (hT : 1 ≤ T) (hL : 1 ≤ L) (hLU : L ≤ U) :
    ∑ n ∈ Finset.Ioc L U,
        (((((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ r) *
          generalizedDivisorTailZeta T) n : ℕ) : ℝ) ≤
      ((U - L : ℕ) : ℝ) * generalizedDivisorHarmonicSum r (U / T) +
        (generalizedDivisorNatSum r (U / T) : ℝ) := by
  rw [sum_Ioc_zeta_pow_mul_tailZeta_cast_eq r T L U hT hL hLU]
  calc
    ∑ m ∈ Finset.Icc 1 (U / T),
        (((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ r) m : ℝ) *
          (((U / m - T : ℕ) : ℝ) - ((L / m - T : ℕ) : ℝ)) ≤
        ∑ m ∈ Finset.Icc 1 (U / T),
          (((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ r) m : ℝ) *
            (((U - L : ℕ) : ℝ) / (m : ℝ) + 1) := by
      apply Finset.sum_le_sum
      intro m hm
      exact mul_le_mul_of_nonneg_left
        (tailQuotientDifference_le_length_div_add_one T L U m
          (Finset.mem_Icc.mp hm).1 hLU) (by positivity)
    _ = ∑ m ∈ Finset.Icc 1 (U / T),
          (((U - L : ℕ) : ℝ) *
              ((((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ r) m : ℝ) / (m : ℝ)) +
            (((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ r) m : ℝ)) := by
      apply Finset.sum_congr rfl
      intro m hm
      ring
    _ = ((U - L : ℕ) : ℝ) *
          (∑ m ∈ Finset.Icc 1 (U / T),
            (((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ r) m : ℝ) / (m : ℝ)) +
          ∑ m ∈ Finset.Icc 1 (U / T),
            (((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ r) m : ℝ) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ = ((U - L : ℕ) : ℝ) * generalizedDivisorHarmonicSum r (U / T) +
          (generalizedDivisorNatSum r (U / T) : ℝ) := by
      unfold generalizedDivisorHarmonicSum generalizedDivisorNatSum
      push_cast
      rfl

/-- Short-interval generalized-divisor estimate with exact harmonic moments. -/
theorem sum_Ioc_zeta_pow_cast_le_harmonic
    (r T L U : ℕ) (hr : 2 ≤ r) (hT : 1 ≤ T) (hL : 1 ≤ L)
    (hLU : L ≤ U) (hpow : T ^ r ≤ L) :
    ∑ n ∈ Finset.Ioc L U,
        ((((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ r) n : ℕ) : ℝ) ≤
      (r : ℝ) *
        (((U - L : ℕ) : ℝ) * generalizedDivisorHarmonicSum (r - 1) (U / T) +
          (generalizedDivisorNatSum (r - 1) (U / T) : ℝ)) := by
  calc
    ∑ n ∈ Finset.Ioc L U,
        ((((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ r) n : ℕ) : ℝ) ≤
        ∑ n ∈ Finset.Ioc L U, (r : ℝ) *
          (((((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ (r - 1)) *
            generalizedDivisorTailZeta T) n : ℕ) : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      have hnLower : L < n := (Finset.mem_Ioc.mp hn).1
      have hcoeff := zeta_pow_apply_le_card_mul_tailZeta_mul_zeta_pow
        T r n (by omega) (hpow.trans_lt hnLower)
      have hcoeff' :
          ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ r) n ≤
            r * ((((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ (r - 1)) *
              generalizedDivisorTailZeta T) n) := by
        calc
          ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ r) n ≤
              r * (generalizedDivisorTailZeta T *
                (ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ (r - 1)) n := hcoeff
          _ = r * (((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ (r - 1) *
                generalizedDivisorTailZeta T) n) := by
            congr 1
            exact congrArg (fun f : ArithmeticFunction ℕ => f n)
              (mul_comm (generalizedDivisorTailZeta T)
                ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ (r - 1)))
      exact_mod_cast hcoeff'
    _ = (r : ℝ) *
        (∑ n ∈ Finset.Ioc L U,
          (((((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ (r - 1)) *
            generalizedDivisorTailZeta T) n : ℕ) : ℝ)) := by
      rw [Finset.mul_sum]
    _ ≤ (r : ℝ) *
        (((U - L : ℕ) : ℝ) * generalizedDivisorHarmonicSum (r - 1) (U / T) +
          (generalizedDivisorNatSum (r - 1) (U / T) : ℝ)) := by
      exact mul_le_mul_of_nonneg_left
        (sum_Ioc_zeta_pow_mul_tailZeta_cast_le (r - 1) T L U hT hL hLU)
        (Nat.cast_nonneg r)

/-- Explicit polylogarithmic form of the short-interval generalized-divisor estimate. -/
theorem sum_Ioc_zeta_pow_cast_le_polylog
    (r T L U : ℕ) (hr : 2 ≤ r) (hT : 1 ≤ T) (hL : 1 ≤ L)
    (hLU : L ≤ U) (hTU : T ≤ U) (hpow : T ^ r ≤ L) :
    ∑ n ∈ Finset.Ioc L U,
        ((((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ r) n : ℕ) : ℝ) ≤
      (r : ℝ) *
        (((U - L : ℕ) : ℝ) * (1 + Real.log (U / T : ℕ)) ^ (r - 1) +
          ((U / T : ℕ) : ℝ) * (1 + Real.log (U / T : ℕ)) ^ (r - 2)) := by
  let N := U / T
  have hN : 1 ≤ N := by
    exact (Nat.one_le_div_iff (by omega)).mpr hTU
  have hH0 : 0 ≤ (((harmonic N : ℚ) : ℝ)) := by
    have hz := harmonic_cast_mono (Nat.zero_le N)
    simpa using hz
  have hlog0 : 0 ≤ 1 + Real.log (N : ℝ) := by
    have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have := Real.log_nonneg hNreal
    linarith
  have hHarmonic :
      generalizedDivisorHarmonicSum (r - 1) N ≤
        (1 + Real.log (N : ℝ)) ^ (r - 1) := by
    calc
      generalizedDivisorHarmonicSum (r - 1) N ≤
          (((harmonic N : ℚ) : ℝ)) ^ (r - 1) :=
        generalizedDivisorHarmonicSum_le_harmonic_pow (r - 1) N (by omega) hN
      _ ≤ (1 + Real.log (N : ℝ)) ^ (r - 1) :=
        pow_le_pow_left₀ hH0 (harmonic_le_one_add_log N) (r - 1)
  have hNat :
      (generalizedDivisorNatSum (r - 1) N : ℝ) ≤
        (N : ℝ) * (1 + Real.log (N : ℝ)) ^ (r - 2) := by
    have horder : r - 2 + 1 = r - 1 := by omega
    calc
      (generalizedDivisorNatSum (r - 1) N : ℝ) =
          (generalizedDivisorNatSum (r - 2 + 1) N : ℝ) := by rw [horder]
      _ ≤ (N : ℝ) * (((harmonic N : ℚ) : ℝ) ^ (r - 2)) :=
        generalizedDivisorNatSum_cast_le_harmonic (r - 2) N hN
      _ ≤ (N : ℝ) * (1 + Real.log (N : ℝ)) ^ (r - 2) :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ hH0 (harmonic_le_one_add_log N) (r - 2))
          (Nat.cast_nonneg N)
  calc
    ∑ n ∈ Finset.Ioc L U,
        ((((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ r) n : ℕ) : ℝ) ≤
        (r : ℝ) *
          (((U - L : ℕ) : ℝ) * generalizedDivisorHarmonicSum (r - 1) N +
            (generalizedDivisorNatSum (r - 1) N : ℝ)) :=
      sum_Ioc_zeta_pow_cast_le_harmonic r T L U hr hT hL hLU hpow
    _ ≤ (r : ℝ) *
          (((U - L : ℕ) : ℝ) * (1 + Real.log (N : ℝ)) ^ (r - 1) +
            (N : ℝ) * (1 + Real.log (N : ℝ)) ^ (r - 2)) := by
      gcongr
    _ = (r : ℝ) *
        (((U - L : ℕ) : ℝ) * (1 + Real.log (U / T : ℕ)) ^ (r - 1) +
          ((U / T : ℕ) : ℝ) * (1 + Real.log (U / T : ℕ)) ^ (r - 2)) := rfl

/-- Fixed divisor powers inherit the same local estimate through the coefficientwise
`d(n)^K ≤ d_{2^K}(n)` domination. -/
theorem sum_card_divisors_pow_Ioc_le_polylog
    (K T L U : ℕ) (hK : 1 ≤ K) (hT : 1 ≤ T) (hL : 1 ≤ L)
    (hLU : L ≤ U) (hTU : T ≤ U) (hpow : T ^ (2 ^ K) ≤ L) :
    ∑ n ∈ Finset.Ioc L U, ((n.divisors.card : ℝ) ^ K) ≤
      ((2 ^ K : ℕ) : ℝ) *
        (((U - L : ℕ) : ℝ) * (1 + Real.log (U / T : ℕ)) ^ (2 ^ K - 1) +
          ((U / T : ℕ) : ℝ) * (1 + Real.log (U / T : ℕ)) ^ (2 ^ K - 2)) := by
  calc
    ∑ n ∈ Finset.Ioc L U, ((n.divisors.card : ℝ) ^ K) ≤
        ∑ n ∈ Finset.Ioc L U,
          ((((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ (2 ^ K)) n : ℕ) : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      have hn0 : n ≠ 0 := by
        have hnLower : L < n := (Finset.mem_Ioc.mp hn).1
        have hnpos : 0 < n := by omega
        omega
      exact_mod_cast card_divisors_pow_le_zeta_pow K n hn0
    _ ≤ ((2 ^ K : ℕ) : ℝ) *
        (((U - L : ℕ) : ℝ) * (1 + Real.log (U / T : ℕ)) ^ (2 ^ K - 1) +
          ((U / T : ℕ) : ℝ) * (1 + Real.log (U / T : ℕ)) ^ (2 ^ K - 2)) :=
      sum_Ioc_zeta_pow_cast_le_polylog (2 ^ K) T L U
        (by
          calc
            2 = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ K := Nat.pow_le_pow_right (by norm_num) hK)
        hT hL hLU hTU hpow

/-- Sharp local square domination for stars-and-bars coefficients.  The adjacent-coefficient
ratio reduces the claim to `(a+r)^(2 : ℕ) ≤ (a+1)(a+r^(2 : ℕ))`. -/
theorem multichoose_sq_le_multichoose_sq_order
    (r a : ℕ) (hr : 1 ≤ r) :
    (r.multichoose a) ^ 2 ≤ (r ^ 2).multichoose a := by
  induction a with
  | zero => simp
  | succ a ih =>
      have hrSq : 1 ≤ r ^ 2 := one_le_pow₀ hr
      have hratio := multichoose_succ_ratio r a hr
      have hratioSq := multichoose_succ_ratio (r ^ 2) a hrSq
      have hpoly : (a + r) ^ 2 ≤ (a + 1) * (a + r ^ 2) := by
        have hpolyR : (((a + r) ^ 2 : ℕ) : ℝ) ≤
            (((a + 1) * (a + r ^ 2) : ℕ) : ℝ) := by
          push_cast
          nlinarith [mul_nonneg (Nat.cast_nonneg a) (sq_nonneg ((r : ℝ) - 1))]
        exact_mod_cast hpolyR
      have hscaled :
          (a + r) ^ 2 * (r.multichoose a) ^ 2 ≤
            ((a + 1) * (a + r ^ 2)) * (r ^ 2).multichoose a :=
        Nat.mul_le_mul hpoly ih
      have hmul :
          (a + 1) ^ 2 * (r.multichoose (a + 1)) ^ 2 ≤
            (a + 1) ^ 2 * (r ^ 2).multichoose (a + 1) := by
        calc
          (a + 1) ^ 2 * (r.multichoose (a + 1)) ^ 2 =
              ((a + 1) * r.multichoose (a + 1)) ^ 2 := by ring
          _ = ((a + r) * r.multichoose a) ^ 2 := by rw [hratio]
          _ = (a + r) ^ 2 * (r.multichoose a) ^ 2 := by ring
          _ ≤ ((a + 1) * (a + r ^ 2)) * (r ^ 2).multichoose a := hscaled
          _ = (a + 1) * ((a + r ^ 2) * (r ^ 2).multichoose a) := by ring
          _ = (a + 1) * ((a + 1) * (r ^ 2).multichoose (a + 1)) := by
            rw [hratioSq]
          _ = (a + 1) ^ 2 * (r ^ 2).multichoose (a + 1) := by ring
      exact Nat.le_of_mul_le_mul_left hmul (by positivity)

/-- The square of an `r`-fold generalized-divisor coefficient is bounded by the corresponding
`r^(2 : ℕ)`-fold coefficient, prime by prime. -/
theorem zeta_pow_apply_sq_le_zeta_sq_order
    (r n : ℕ) (hr : 1 ≤ r) (hn : n ≠ 0) :
    (((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ r) n) ^ 2 ≤
      ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ (r ^ 2)) n := by
  rw [ArithmeticFunction.IsMultiplicative.multiplicative_factorization
    ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ r)
    ArithmeticFunction.isMultiplicative_zeta.pow hn]
  rw [ArithmeticFunction.IsMultiplicative.multiplicative_factorization
    ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ (r ^ 2))
    ArithmeticFunction.isMultiplicative_zeta.pow hn]
  rw [Nat.prod_factorization_eq_prod_primeFactors,
    Nat.prod_factorization_eq_prod_primeFactors]
  rw [← Finset.prod_pow]
  apply Finset.prod_le_prod
  · intro p hp
    exact Nat.zero_le _
  · intro p hp
    rw [zeta_pow_apply_prime_pow r (n.factorization p) p
      (Nat.prime_of_mem_primeFactors hp)]
    rw [zeta_pow_apply_prime_pow (r ^ 2) (n.factorization p) p
      (Nat.prime_of_mem_primeFactors hp)]
    exact multichoose_sq_le_multichoose_sq_order r (n.factorization p) hr

/-- Local mean square of one fixed generalized-divisor coefficient. -/
theorem sum_zeta_pow_sq_Ioc_le_polylog
    (r T L U : ℕ) (hr : 2 ≤ r) (hT : 1 ≤ T) (hL : 1 ≤ L)
    (hLU : L ≤ U) (hTU : T ≤ U) (hpow : T ^ (r ^ 2) ≤ L) :
    ∑ n ∈ Finset.Ioc L U,
        ((((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ r) n : ℝ) ^ 2) ≤
      ((r ^ 2 : ℕ) : ℝ) *
        (((U - L : ℕ) : ℝ) * (1 + Real.log (U / T : ℕ)) ^ (r ^ 2 - 1) +
          ((U / T : ℕ) : ℝ) * (1 + Real.log (U / T : ℕ)) ^ (r ^ 2 - 2)) := by
  calc
    ∑ n ∈ Finset.Ioc L U,
        ((((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ r) n : ℝ) ^ 2) ≤
        ∑ n ∈ Finset.Ioc L U,
          ((((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ (r ^ 2)) n : ℕ) : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      have hn0 : n ≠ 0 := by
        have hnLower : L < n := (Finset.mem_Ioc.mp hn).1
        omega
      exact_mod_cast zeta_pow_apply_sq_le_zeta_sq_order r n (by omega) hn0
    _ ≤ ((r ^ 2 : ℕ) : ℝ) *
        (((U - L : ℕ) : ℝ) * (1 + Real.log (U / T : ℕ)) ^ (r ^ 2 - 1) +
          ((U / T : ℕ) : ℝ) * (1 + Real.log (U / T : ℕ)) ^ (r ^ 2 - 2)) :=
      sum_Ioc_zeta_pow_cast_le_polylog (r ^ 2) T L U
        (by
          exact hr.trans (by
            simpa using Nat.pow_le_pow_right (by omega : 0 < r) (show 1 ≤ 2 by omega)))
        hT hL hLU hTU hpow

end

end RHTower.Sieve
