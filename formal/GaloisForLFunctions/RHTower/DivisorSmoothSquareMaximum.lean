import GaloisForLFunctions.RHTower.DivisorUniformSquareRootBound
import GaloisForLFunctions.RHTower.HarmonicStirlingExactBounds

/-!
# A uniform smooth ceiling from consecutive square endpoints

The fixed-modulus smooth remainder has increasing discrete increments between
consecutive squares. Its transition to each next square is upward. The global
maximum is therefore controlled by square endpoints, where Stirling and the
harmonic twelfth-square correction give a three-fifths ceiling. Signed centered
time cancellation and exact clipped homothety transfer it to every unsigned
Abel channel.
-/

noncomputable section
open Finset Filter Topology HTGeometry
namespace RHTower
private def squareProfile (s N : ℕ) : ℝ :=
  (∑ m ∈ Icc 1 N, Real.log m) - (2*(N:ℝ)+1)*((harmonic s:ℚ):ℝ)+
    (s:ℝ)^(2 : ℕ)+s+2*Real.eulerMascheroniConstant*N
private lemma profile_step (s N : ℕ) :
    squareProfile s (N+1)-squareProfile s N =
      Real.log (N+1:ℕ)-2*((harmonic s:ℚ):ℝ)+2*Real.eulerMascheroniConstant := by
  unfold squareProfile
  rw [sum_Icc_succ_top (by omega : 1 ≤ N+1)]
  push_cast
  ring
private lemma convex_nat_max (f : ℕ → ℝ)
    (hmono : Monotone (fun n => f (n+1)-f n)) {a n b : ℕ} (han : a ≤ n) (hnb : n ≤ b) :
    f n  ≤  max (f a) (f b) := by
  by_cases hs : 0 ≤ f (n+1)-f n
  · have hg : MonotoneOn f {k : ℕ | n ≤ k} := monotoneOn_nat_Ici_of_le_succ (fun k hk => by
      have hh := hmono hk
      linarith)
    exact (hg (by simp) hnb hnb).trans (le_max_right _ _)
  · have hdown : ∀ k : ℕ, a ≤ k → k ≤ n → f k ≤ f a := by
      intro k hak
      induction k,hak using Nat.le_induction with
      | base => intro _; exact le_rfl
      | succ k hak ih =>
        intro hkn
        have hk : k ≤ n := by omega
        have hh := hmono hk
        have hi := ih hk
        linarith
    exact (hdown n han le_rfl).trans (le_max_left _ _)
private lemma gamma_lower : (0.5768:ℝ)  ≤  Real.eulerMascheroniConstant := by
  have h := (harmonic_mascheroni_half_bounds (n := 16) (by norm_num)).2
  have hlog : Real.log (16:ℝ)=4*Real.log 2 := by
    rw [show (16:ℝ)=2^(4 : ℕ) by norm_num,Real.log_pow]; norm_num
  norm_num [harmonic,Finset.sum_range_succ,hlog] at h
  linarith [Real.log_two_lt_d9]
private lemma smooth_square_bound {s : ℕ} (hs : 1 ≤ s) :
    divisorHyperbolaSmoothRemainder (s^(2 : ℕ))  ≤  (3/5:ℝ) := by
  have hsR : (1:ℝ) ≤ s := by exact_mod_cast hs
  have hs0 : (0:ℝ) < s := by positivity
  have hF := sum_log_Icc_le_half_log_stirling (N:=s^(2 : ℕ)) (by nlinarith only [hs])
  have hH := harmonic_mascheroni_ge_half_sub_twelfth hs
  have hHmul := mul_le_mul_of_nonneg_left hH (show (0:ℝ) ≤ 2*(s:ℝ)^(2 : ℕ)+1 by positivity)
  have hrat : (2*(s:ℝ)^(2 : ℕ)+1)*(1/(2*(s:ℝ))-1/(12*(s:ℝ)^(2 : ℕ))) =
      (s:ℝ)-1/6+1/(2*(s:ℝ))-1/(12*(s:ℝ)^(2 : ℕ)) := by field_simp; ring
  rw [hrat] at hHmul
  have hsmall : 1/(12*(s:ℝ)^(2 : ℕ)) ≤ 1/(2*(s:ℝ)) := by
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith only [hsR]
  norm_num only [Nat.cast_pow,Real.log_pow,Nat.cast_ofNat] at hF
  unfold divisorHyperbolaSmoothRemainder
  rw [Nat.sqrt_eq']
  push_cast
  nlinarith only [hF,hHmul,hsmall,gamma_lower]
private lemma profile_last_le_square (s : ℕ) :
    squareProfile s ((s+1)^(2 : ℕ)-1)  ≤  divisorHyperbolaSmoothRemainder ((s+1)^(2 : ℕ)) := by
  let t := s+1
  have ht : 1 ≤ t := by dsimp [t]; omega
  have ht0 : (0:ℝ)<t := by positivity
  have hH := (harmonic_mascheroni_half_bounds ht).2
  have hstep := profile_step s (t^(2 : ℕ)-1)
  rw [Nat.sub_add_cancel (by nlinarith only [ht] : 1 ≤ t^(2 : ℕ))] at hstep
  have hharm : ((harmonic t:ℚ):ℝ)=((harmonic s:ℚ):ℝ)+(t:ℝ)⁻¹ := by
    dsimp [t]
    rw [harmonic_succ,Rat.cast_add,Rat.cast_inv,Rat.cast_natCast]
  have he : squareProfile s (t^(2 : ℕ)) = divisorHyperbolaSmoothRemainder (t^(2 : ℕ))+(t:ℝ)⁻¹ := by
    unfold squareProfile divisorHyperbolaSmoothRemainder
    rw [Nat.sqrt_eq',hharm]
    have hi : (t:ℝ)*(t:ℝ)⁻¹=1 := mul_inv_cancel₀ (ne_of_gt ht0)
    have hts : (t:ℝ)=(s:ℝ)+1 := by simp [t]
    push_cast
    nlinarith [congrArg (fun x : ℝ => 2*(t:ℝ)*x) hi]
  rw [he] at hstep
  norm_num only [Nat.cast_pow,Real.log_pow,Nat.cast_ofNat] at hstep
  have hhalf : 2*(1/(2*(t:ℝ)))=(t:ℝ)⁻¹ := by field_simp
  change squareProfile s (t^(2 : ℕ)-1) ≤ _
  rw [hharm] at hH
  linarith

/-- Every smooth divisor-hyperbola remainder lies below three fifths. -/
theorem divisorHyperbolaSmoothRemainder_le_three_fifths (N : ℕ) :
    divisorHyperbolaSmoothRemainder N  ≤  (3/5:ℝ) := by
  by_cases hN : N=0
  · subst N; norm_num [divisorHyperbolaSmoothRemainder]
  let s := Nat.sqrt N
  have hs : 1 ≤ s := Nat.le_sqrt.mpr (by simpa using Nat.one_le_iff_ne_zero.mpr hN)
  have hlo : s^(2 : ℕ) ≤ N := Nat.sqrt_le' N
  have hhi : N ≤ (s+1)^(2 : ℕ)-1 := by
    have h := Nat.lt_succ_sqrt' N
    change N < (s+1)^(2 : ℕ) at h
    omega
  have hm : Monotone (fun k => squareProfile s (k+1)-squareProfile s k) := by
    intro k l hkl
    dsimp only
    rw [profile_step,profile_step]
    have hlog := Real.log_le_log (by positivity : (0:ℝ)<(k+1:ℕ))
      (show ((k+1:ℕ):ℝ) ≤ (l+1:ℕ) by exact_mod_cast Nat.add_le_add_right hkl 1)
    linarith
  have hmax := convex_nat_max (squareProfile s) hm hlo hhi
  have hleft : squareProfile s (s^(2 : ℕ)) ≤ (3/5:ℝ) := by
    simpa [squareProfile,divisorHyperbolaSmoothRemainder,Nat.sqrt_eq'] using smooth_square_bound hs
  have hright := (profile_last_le_square s).trans (smooth_square_bound (s:=s+1) (by omega))
  exact hmax.trans (max_le hleft hright)

/-- Centered time cancellation transfers the smooth ceiling to the unit Abel channel. -/
theorem divisorUnsignedDilationChannel_one_le_three_fifths_sqrt (M : ℕ) :
    divisorUnsignedDilationChannel M 1 ≤ (3/5:ℝ)*Real.sqrt M := by
  have htel : (∑ k ∈ range M,halfOrderAbelStep 0 k)=Real.sqrt M := by
    simpa only [halfOrderAbelStep,Nat.zero_add,Nat.cast_zero,Real.sqrt_zero,sub_zero]
      using Finset.sum_range_sub (fun k : ℕ => Real.sqrt k) M
  have hs : divisorHyperbolaSmoothAbel M ≤ (3/5:ℝ)*Real.sqrt M := by
    unfold divisorHyperbolaSmoothAbel
    calc
      _ ≤ ∑ k ∈ range M,(3/5:ℝ)*halfOrderAbelStep 0 k :=
        sum_le_sum (fun k _ => mul_le_mul_of_nonneg_right
          (divisorHyperbolaSmoothRemainder_le_three_fifths k) (halfOrderAbelStep_nonneg 0 k))
      _ = _ := by rw [← mul_sum,htel]
  have hid := mobiusDivisorDilationChannel_one_eq_hyperbola M
  rw [mobiusDivisorDilationChannel_eq_moebius_unsigned] at hid
  simp only [ArithmeticFunction.moebius_apply_one,Int.cast_one,one_mul] at hid
  have hc := (centeredDivisorHyperbolaAbel_bounds M).2
  linarith only [hid,hs,hc]

/-- Every unsigned dilation has the same three-fifths square-root ceiling. -/
theorem divisorUnsignedDilationChannel_le_three_fifths_sqrt (M d : ℕ) :
    divisorUnsignedDilationChannel M d ≤ (3/5:ℝ)*Real.sqrt M := by
  by_cases hd : d=0
  · subst d
    simp [divisorUnsignedDilationChannel,primeFreeDivisorDefect,Real.sqrt_nonneg]
  have hd0 : 0 < d := by omega
  have hw0 := divisorPrimeClipWeight_nonneg M d hd0
  have hw1 : 0 ≤ 1-divisorPrimeClipWeight M d := by
    have h := divisorPrimeClipWeight_lt_one M d hd0
    linarith
  have hA := mul_le_mul_of_nonneg_left (divisorUnsignedDilationChannel_one_le_three_fifths_sqrt (M/d)) hw1
  have hB := mul_le_mul_of_nonneg_left (divisorUnsignedDilationChannel_one_le_three_fifths_sqrt (M/d+1)) hw0
  have hsum := mul_le_mul_of_nonneg_left (add_le_add hA hB) (Real.sqrt_nonneg (d:ℝ))
  have hc := divisorUnsignedDilationChannel_prime_interpolation M d 1 hd0
  simp only [Nat.mul_one] at hc
  have hclock := divisorPrimeClipWeight_mul_step M d hd0
  push_cast at hclock
  rw [Real.sqrt_mul (Nat.cast_nonneg d)] at hclock
  rw [hc]
  push_cast at hsum ⊢
  nlinarith only [hsum,hclock]
end RHTower
