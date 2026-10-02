import GaloisForLFunctions.RHTower.MobiusDivisorLatePrimeHeadAsymptotic
import GaloisForLFunctions.RHTower.MobiusDivisorClippedHomothety
import GaloisForLFunctions.RHTower.Sieve.MoebiusMaximalWindow
import GaloisForLFunctions.RHTower.DeningerAbelSummation
import GaloisForLFunctions.RHTower.DivisorSmoothSquareMaximum

/-!
# Native fixed hyperbolic boundary strips

The clipped homothety gives an exact affine square-root law on each quotient
cell. Discrete Abel summation bounds its Möbius sums by the native Mertens
supremum. Subtracting finitely many cells from the full signed-channel mean
pays every fixed quotient prefix, pair row, finite strip, and finite corner.
These unconditional limits are inputs to the complete Route RP pair-sector
estimate; they do not bound the complementary pairs or the native square debts.
-/

noncomputable section
open Finset Filter Topology
namespace RHTower

private lemma sqrt_mobius_prefix_bound (M L : ℕ) (hLM : L ≤ M) :
    |∑ n ∈ range (L+1), (ArithmeticFunction.moebius n:ℝ)*Real.sqrt n| ≤
      2*Real.sqrt M*Sieve.mertensSup M := by
  have hS := Sieve.mertensSup_nonneg M
  have hid := deningerAbelSummation (fun n => (ArithmeticFunction.moebius n:ℝ))
    (fun n => Real.sqrt n) L
  change _ = Sieve.mertensM L*Real.sqrt L+
    ∑ n ∈ range L, Sieve.mertensM n*(Real.sqrt n-Real.sqrt (n+1:ℕ)) at hid
  have hstep (n : ℕ) : 0 ≤ Real.sqrt (n+1:ℕ)-Real.sqrt n :=
    sub_nonneg.mpr (Real.sqrt_le_sqrt (by exact_mod_cast Nat.le_succ n))
  have htail : |∑ n ∈ range L, Sieve.mertensM n*(Real.sqrt n-Real.sqrt (n+1:ℕ))| ≤
      Sieve.mertensSup M*Real.sqrt L := by
    calc
      _ ≤ ∑ n ∈ range L, |Sieve.mertensM n*(Real.sqrt n-Real.sqrt (n+1:ℕ))| :=
        abs_sum_le_sum_abs _ _
      _ ≤ ∑ n ∈ range L, Sieve.mertensSup M*(Real.sqrt (n+1:ℕ)-Real.sqrt n) := by
        apply sum_le_sum
        intro n hn
        rw [abs_mul,abs_sub_comm,abs_of_nonneg (hstep n)]
        exact mul_le_mul_of_nonneg_right
          (Sieve.abs_mertensM_le_mertensSup ((mem_range.mp hn).le.trans hLM)) (hstep n)
      _ = _ := by
        rw [← mul_sum]
        have htel := sum_range_sub (fun n : ℕ => Real.sqrt (n:ℝ)) L
        simpa using congrArg (fun x : ℝ => Sieve.mertensSup M*x) htel
  have hboundary : |Sieve.mertensM L*Real.sqrt L| ≤ Sieve.mertensSup M*Real.sqrt L := by
    rw [abs_mul,abs_of_nonneg (Real.sqrt_nonneg (L:ℝ))]
    exact mul_le_mul_of_nonneg_right (Sieve.abs_mertensM_le_mertensSup hLM)
      (Real.sqrt_nonneg _)
  rw [hid]
  calc
    _ ≤ |Sieve.mertensM L*Real.sqrt L|+
        |∑ n ∈ range L, Sieve.mertensM n*(Real.sqrt n-Real.sqrt (n+1:ℕ))| := abs_add_le _ _
    _ ≤ Sieve.mertensSup M*Real.sqrt L+Sieve.mertensSup M*Real.sqrt L :=
      add_le_add hboundary htail
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left
        (Real.sqrt_le_sqrt (show (L:ℝ) ≤ M by exact_mod_cast hLM)) hS
      linarith only [h]

private lemma interval_eq_prefix_sub (f : ℕ → ℝ) (L U : ℕ) (hLU : L ≤ U) :
    (∑ n ∈ Ioc L U, f n) = (∑ n ∈ range (U+1), f n)-(∑ n ∈ range (L+1), f n) := by
  have he : Ioc L U = Ico (L+1) (U+1) := by ext n; simp
  rw [he,sum_Ico_eq_sub _ (by omega : L+1 ≤ U+1)]

private lemma mobius_interval_bound (M L U : ℕ) (hLU : L ≤ U) (hUM : U ≤ M) :
    |∑ n ∈ Ioc L U, (ArithmeticFunction.moebius n:ℝ)| ≤ 2*Sieve.mertensSup M := by
  rw [interval_eq_prefix_sub _ L U hLU]
  change |Sieve.mertensM U-Sieve.mertensM L| ≤ _
  exact (abs_sub _ _).trans (by
    have hU := Sieve.abs_mertensM_le_mertensSup hUM
    have hL := Sieve.abs_mertensM_le_mertensSup (hLU.trans hUM)
    linarith only [hU,hL])

private lemma sqrt_mobius_interval_bound (M L U : ℕ) (hLU : L ≤ U) (hUM : U ≤ M) :
    |∑ n ∈ Ioc L U, (ArithmeticFunction.moebius n:ℝ)*Real.sqrt n| ≤
      4*Real.sqrt M*Sieve.mertensSup M := by
  rw [interval_eq_prefix_sub _ L U hLU]
  exact (abs_sub _ _).trans (by
    have hU := sqrt_mobius_prefix_bound M U hUM
    have hL := sqrt_mobius_prefix_bound M L (hLU.trans hUM)
    linarith only [hU,hL])

private lemma quotient_cell (M j e : ℕ) (hj : 0 < j)
    (he : e ∈ Ioc (M/(j+1)) (M/j)) : M/e = j := by
  have he0 : 0 < e := lt_of_le_of_lt (Nat.zero_le _) (mem_Ioc.mp he).1
  have hlow : e*j ≤ M := (Nat.le_div_iff_mul_le hj).mp (mem_Ioc.mp he).2
  have hhi : M < e*(j+1) := by
    have h := (Nat.div_lt_iff_lt_mul (show 0 < j+1 by omega)).mp (mem_Ioc.mp he).1
    simpa only [Nat.mul_comm] using h
  apply le_antisymm
  · have h : M/e < j+1 := (Nat.div_lt_iff_lt_mul he0).mpr (by simpa [Nat.mul_comm] using hhi)
    omega
  · exact (Nat.le_div_iff_mul_le he0).mpr (by simpa [Nat.mul_comm] using hlow)

/-- Exact affine square-root law on a literal quotient cell. -/
theorem routeP_channel_quotient_cell (M j e : ℕ) (hj : 0 < j)
    (he : e ∈ Ioc (M/(j+1)) (M/j)) :
    mobiusDivisorDilationChannel M e = (ArithmeticFunction.moebius e:ℝ)*
      (Real.sqrt e*(divisorUnsignedDilationChannel j 1-Real.sqrt j*primeFreeDivisorDefect j)+
        Real.sqrt M*primeFreeDivisorDefect j) := by
  have he0 : 0 < e := lt_of_le_of_lt (Nat.zero_le _) (mem_Ioc.mp he).1
  have hq := quotient_cell M j e hj he
  have hid := divisorUnsignedDilationChannel_mul_add e (M/e) (M%e) 1 he0 (Nat.mod_lt M he0).le
  have hM : e*(M/e)+M%e = M := by have := Nat.mod_add_div M e; omega
  rw [hM,Nat.mul_one,Nat.div_one,hq] at hid
  push_cast at hid
  rw [Real.sqrt_mul (Nat.cast_nonneg e)] at hid
  rw [mobiusDivisorDilationChannel_eq_moebius_unsigned,hid]
  ring

/-- Each fixed quotient cell is paid by the ordinary Mertens supremum. -/
theorem routeP_quotient_cell_bound (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ M : ℕ,
      |∑ e ∈ Ioc (M/(j+2)) (M/(j+1)), mobiusDivisorDilationChannel M e| ≤
        C*Real.sqrt M*Sieve.mertensSup M := by
  let a := divisorUnsignedDilationChannel (j+1) 1-
    Real.sqrt (j+1:ℕ)*primeFreeDivisorDefect (j+1)
  let b := primeFreeDivisorDefect (j+1)
  refine ⟨4*|a|+2*|b|,by positivity,?_⟩
  intro M
  have hLU : M/(j+2) ≤ M/(j+1) := Nat.div_le_div_left (by omega) (by omega)
  have hUM : M/(j+1) ≤ M := Nat.div_le_self _ _
  have hs := sqrt_mobius_interval_bound M _ _ hLU hUM
  have hm := mobius_interval_bound M _ _ hLU hUM
  have hid : (∑ e ∈ Ioc (M/(j+2)) (M/(j+1)), mobiusDivisorDilationChannel M e) =
      a*(∑ e ∈ Ioc (M/(j+2)) (M/(j+1)), (ArithmeticFunction.moebius e:ℝ)*Real.sqrt e)+
      (Real.sqrt M*b)*(∑ e ∈ Ioc (M/(j+2)) (M/(j+1)), (ArithmeticFunction.moebius e:ℝ)) := by
    rw [mul_sum,mul_sum,← sum_add_distrib]
    apply sum_congr rfl
    intro e he
    rw [routeP_channel_quotient_cell M (j+1) e (by omega) (by simpa [Nat.add_assoc] using he)]
    dsimp [a,b]
    ring
  rw [hid]
  calc
    _ ≤ |a*(∑ e ∈ Ioc (M/(j+2)) (M/(j+1)), (ArithmeticFunction.moebius e:ℝ)*Real.sqrt e)|+
        |(Real.sqrt M*b)*(∑ e ∈ Ioc (M/(j+2)) (M/(j+1)), (ArithmeticFunction.moebius e:ℝ))| :=
      abs_add_le _ _
    _ ≤ |a| * (4*Real.sqrt M*Sieve.mertensSup M)+
        (Real.sqrt M*|b|)*(2*Sieve.mertensSup M) := by
      rw [abs_mul,abs_mul,abs_mul,abs_of_nonneg (Real.sqrt_nonneg (M:ℝ))]
      exact add_le_add (mul_le_mul_of_nonneg_left hs (abs_nonneg a))
        (mul_le_mul_of_nonneg_left hm (by positivity))
    _ = _ := by ring

/-- Every fixed literal quotient cell vanishes at the boundary-strip scale. -/
theorem routeP_quotient_cell_normalized_tendsto (j : ℕ) :
    Tendsto (fun M : ℕ =>
      (∑ e ∈ Ioc (M/(j+2)) (M/(j+1)), mobiusDivisorDilationChannel M e)/
        ((M:ℝ)*Real.sqrt M)) atTop (𝓝 0) := by
  obtain ⟨C,hC,hbound⟩ := routeP_quotient_cell_bound j
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _
    (by simpa using Sieve.tendsto_mertensSup_div.const_mul C)
  filter_upwards [eventually_ge_atTop (1:ℕ)] with M hM
  have hm : (0:ℝ) < M := by exact_mod_cast hM
  have hs : 0 < Real.sqrt (M:ℝ) := Real.sqrt_pos.mpr hm
  rw [Real.norm_eq_abs,abs_div,abs_of_pos (mul_pos hm hs),div_le_iff₀ (mul_pos hm hs)]
  calc
    _ ≤ C*Real.sqrt M*Sieve.mertensSup M := hbound M
    _ = _ := by field_simp

private lemma full_channels_normalized_tendsto :
    Tendsto (fun M : ℕ =>
      (∑ e ∈ Icc 1 M, mobiusDivisorDilationChannel M e)/((M:ℝ)*Real.sqrt M)) atTop (𝓝 0) := by
  have hi : Tendsto (fun M : ℕ => (Real.log (M:ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have h := tendsto_sum_mobiusDivisorDilationChannel_log_normalized.mul hi
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (2:ℕ)] with M hM
  have hl : 0 < Real.log (M:ℝ) := Real.log_pos (by exact_mod_cast hM)
  field_simp

private lemma prefix_difference (f : ℕ → ℝ) (L U : ℕ) (hLU : L ≤ U) :
    (∑ e ∈ Icc 1 L, f e) = (∑ e ∈ Icc 1 U, f e)-(∑ e ∈ Ioc L U, f e) := by
  have hL : Icc 1 L = Ico 1 (L+1) := by ext n; simp
  have hU : Icc 1 U = Ico 1 (U+1) := by ext n; simp
  have hI : Ioc L U = Ico (L+1) (U+1) := by ext n; simp
  have h := sum_Ico_consecutive f (show 1 ≤ L+1 by omega) (show L+1 ≤ U+1 by omega)
  rw [hL,hU,hI]
  linarith only [h]

/-- Actual fixed-quotient prefix channels cancel at the boundary-strip scale. -/
theorem routeP_fixed_quotient_prefix_tendsto (K : ℕ) :
    Tendsto (fun M : ℕ =>
      (∑ e ∈ Icc 1 (M/(K+1)), mobiusDivisorDilationChannel M e)/
        ((M:ℝ)*Real.sqrt M)) atTop (𝓝 0) := by
  induction K with
  | zero => simpa using full_channels_normalized_tendsto
  | succ K ih =>
    have h := ih.sub (routeP_quotient_cell_normalized_tendsto K)
    simp only [sub_zero] at h
    convert h using 1
    funext M
    rw [prefix_difference (mobiusDivisorDilationChannel M) (M/(K+2)) (M/(K+1))
      (Nat.div_le_div_left (by omega) (by omega)),sub_div]

private lemma channel_abs_bound (M d : ℕ) :
    |mobiusDivisorDilationChannel M d| ≤ (3/5:ℝ)*Real.sqrt M := by
  rw [mobiusDivisorDilationChannel_eq_moebius_unsigned,abs_mul,
    abs_of_nonneg (divisorUnsignedDilationChannel_nonneg M d)]
  have hm : |(ArithmeticFunction.moebius d:ℝ)| ≤ 1 := by
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n:=d)
  calc
    _ ≤ 1*divisorUnsignedDilationChannel M d :=
      mul_le_mul_of_nonneg_right hm (divisorUnsignedDilationChannel_nonneg M d)
    _ ≤ _ := by simpa using divisorUnsignedDilationChannel_le_three_fifths_sqrt M d

/-- A complete signed hyperbolic row vanishes at critical pair normalization. -/
theorem routeP_fixed_pair_row_tendsto (d : ℕ) :
    Tendsto (fun M : ℕ => mobiusDivisorDilationChannel M (d+1)*
      (∑ e ∈ Icc 1 (M/(d+1)), mobiusDivisorDilationChannel M e)/(M:ℝ)^2)
      atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _
    (by simpa only [norm_zero,mul_zero] using (routeP_fixed_quotient_prefix_tendsto d).norm.const_mul (3/5:ℝ))
  filter_upwards [eventually_ge_atTop (1:ℕ)] with M hM
  have hm : (0:ℝ) < M := by exact_mod_cast hM
  have hs : 0 < Real.sqrt (M:ℝ) := Real.sqrt_pos.mpr hm
  have hden : Real.sqrt (M:ℝ)*((M:ℝ)*Real.sqrt M) = (M:ℝ)^2 := by
    calc
      _ = (M:ℝ)*(Real.sqrt M)^2 := by ring
      _ = _ := by rw [Real.sq_sqrt hm.le]; ring
  have heq : mobiusDivisorDilationChannel M (d+1)*
      (∑ e ∈ Icc 1 (M/(d+1)), mobiusDivisorDilationChannel M e)/(M:ℝ)^2 =
      (mobiusDivisorDilationChannel M (d+1)/Real.sqrt M)*
      ((∑ e ∈ Icc 1 (M/(d+1)), mobiusDivisorDilationChannel M e)/((M:ℝ)*Real.sqrt M)) := by
    symm
    calc
      _ = (mobiusDivisorDilationChannel M (d+1)*
        (∑ e ∈ Icc 1 (M/(d+1)), mobiusDivisorDilationChannel M e))/
          (Real.sqrt (M:ℝ)*((M:ℝ)*Real.sqrt M)) := by ring
      _ = _ := by rw [hden]
  have hA : ‖mobiusDivisorDilationChannel M (d+1)/Real.sqrt M‖ ≤ (3/5:ℝ) := by
    rw [Real.norm_eq_abs,abs_div,abs_of_pos hs,div_le_iff₀ hs]
    exact channel_abs_bound M (d+1)
  rw [heq,norm_mul]
  exact mul_le_mul_of_nonneg_right hA (norm_nonneg (((∑ e ∈ Icc 1 (M/(d+1)), mobiusDivisorDilationChannel M e)/((M:ℝ)*Real.sqrt M)):ℝ))

/-- Every fixed-width boundary strip of the literal pair sector is paid. -/
theorem routeP_fixed_pair_strip_tendsto (K : ℕ) :
    Tendsto (fun M : ℕ =>
      (∑ d ∈ range K, mobiusDivisorDilationChannel M (d+1)*
        (∑ e ∈ Icc 1 (M/(d+1)), mobiusDivisorDilationChannel M e))/(M:ℝ)^2)
      atTop (𝓝 0) := by
  induction K with
  | zero => simp
  | succ K ih =>
    have h := ih.add (routeP_fixed_pair_row_tendsto K)
    simp only [add_zero] at h
    convert h using 1
    funext M
    rw [Finset.sum_range_succ,add_div]

/-- The finite corner shared by two fixed boundary strips is also negligible. -/
theorem routeP_fixed_pair_corner_tendsto (K : ℕ) :
    Tendsto (fun M : ℕ =>
      (∑ d ∈ range K, mobiusDivisorDilationChannel M (d+1))^2/(M:ℝ)^2)
      atTop (𝓝 0) := by
  let C : ℝ := ((K:ℝ)*(3/5))^2
  have hg : Tendsto (fun M : ℕ => C/(M:ℝ)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,mul_zero,Function.comp_apply] using
      (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop :
        Tendsto (fun M : ℕ => (M:ℝ)) atTop atTop)).const_mul C
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ hg
  filter_upwards [eventually_ge_atTop (1:ℕ)] with M hM
  have hm : (0:ℝ) < M := by exact_mod_cast hM
  have hA : |∑ d ∈ range K, mobiusDivisorDilationChannel M (d+1)| ≤
      ((K:ℝ)*(3/5))*Real.sqrt M := by
    calc
      _ ≤ ∑ d ∈ range K, |mobiusDivisorDilationChannel M (d+1)| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _ ∈ range K, (3/5:ℝ)*Real.sqrt M :=
        sum_le_sum (fun d _ => channel_abs_bound M (d+1))
      _ = _ := by simp; ring
  have hsq : (∑ d ∈ range K, mobiusDivisorDilationChannel M (d+1))^2 ≤ C*(M:ℝ) := by
    have h := mul_self_le_mul_self (abs_nonneg _) hA
    calc
      _ = |∑ d ∈ range K, mobiusDivisorDilationChannel M (d+1)|^2 := (sq_abs _).symm
      _ ≤ (((K:ℝ)*(3/5))*Real.sqrt M)^2 := by nlinarith only [h]
      _ = _ := by simp only [C,mul_pow,Real.sq_sqrt (Nat.cast_nonneg M)]
  rw [Real.norm_eq_abs,abs_of_nonneg (div_nonneg (sq_nonneg _) (sq_nonneg _)),
    div_le_iff₀ (sq_pos_of_pos hm)]
  calc
    _ ≤ C*(M:ℝ) := hsq
    _ = _ := by field_simp

end RHTower
