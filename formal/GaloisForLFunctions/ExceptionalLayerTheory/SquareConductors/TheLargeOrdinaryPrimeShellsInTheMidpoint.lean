import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.ThePrimeFloorRowBeyondTheSquareRoot
import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheTotientTermInTheReflectedCompositePrice
import GaloisForLFunctions.PrimeExponentialSums.ReciprocalHarmonicsOnTheReflectedPrimeShell

/-!
# Ordinary prime shells in the reflected midpoint

The finite harmonic estimate applies separately at the three scaled
product endpoints of a single prime block. Dropping higher prime powers
costs only their Chebyshev mass, uniformly in the terminal prime.
-/

noncomputable section
open Finset Filter ArithmeticFunction GaloisForLFunctions.PrimeExponentialSums
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- At every sufficiently large integer center the sharp signed ordinary
prime block costs n^(t+ε) throughout the wider Vaughan range. -/
theorem large_midpoint_prime_block {t ε : ℝ} (ht : 1/2 ≤ t) (ht1 : t < 1) (he : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop, ∀ {A B : ℕ}, A ≤ B → B ≤ 2*A →
      (n:ℝ)^t ≤ A → (A:ℝ) ≤ (n:ℝ)^(reflectedPrimeShellExponent t) →
      |midpointFloorPrimeBlock n A B| ≤ C*(n:ℝ)^(t+ε) := by
  obtain ⟨D,hD⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  refine ⟨4+2*|D|,by positivity,?_⟩
  have hnat := (tendsto_natCast_atTop_atTop (R:=ℝ)).eventually (reflected_shell_mangoldt_saw ht ht1 he)
  filter_upwards [hnat,eventually_ge_atTop 1] with n hfreq hn
  intro A B hAB hd hlo hhi
  have hn1 := (Nat.one_le_cast (α:=ℝ)).mpr hn
  have hA : 1 ≤ A := by exact_mod_cast (Real.one_le_rpow hn1 (by linarith only [ht] : 0 ≤ t)).trans hlo
  obtain ⟨_,ha,_⟩ := reflected_prime_shell_exponents ht ht1
  change reflectedPrimeShellExponent t < 1 at ha
  have hcut := hhi.trans ((Real.rpow_le_rpow_of_exponent_le hn1 ha.le).trans_eq (Real.rpow_one _))
  have hB : B ≤ 4*n := by
    have hAn : A ≤ n := Nat.cast_le.mp hcut
    omega
  let s := Ico A B
  let F (k : ℝ) := ∑ p ∈ s,vonMangoldt p*(Int.fract (k*n/p)-1/2)
  let f (p : ℕ) := vonMangoldt p*midpointFloorWeight n p
  have hsum : (∑ p ∈ s,f p)=2*F 3-F 2-F 4 := by
    simp only [F,mul_sum,←sum_sub_distrib]
    exact sum_congr rfl fun p _ => by dsimp only [f]; rw [midpoint_floor_weight_as_sawtooths]; ring
  have hF (k : ℝ) (h : 2 ≤ k) (h' : k ≤ 4) : |F k| ≤ (n:ℝ)^(t+ε) :=
    hfreq hAB hd hlo hhi h h'
  have hf2 := abs_le.mp (hF 2 (by norm_num) (by norm_num))
  have hf3 := abs_le.mp (hF 3 (by norm_num) (by norm_num))
  have hf4 := abs_le.mp (hF 4 (by norm_num) (by norm_num))
  have hall : |∑ p ∈ s,f p| ≤ 4*(n:ℝ)^(t+ε) := by
    rw [hsum,abs_le]
    constructor <;> linarith only [hf2.1,hf2.2,hf3.1,hf3.2,hf4.1,hf4.2]
  let T := s.filter (fun p => ¬p.Prime)
  have hpr : (∑ p ∈ s.filter Nat.Prime,f p)=midpointFloorPrimeBlock n A B := by
    exact sum_congr rfl fun p hp => by dsimp only [f]; rw [vonMangoldt_apply_prime (mem_filter.mp hp).2]
  have hsplit := sum_filter_add_sum_filter_not s Nat.Prime f
  rw [hpr] at hsplit
  have hprice : |∑ p ∈ T,f p| ≤ Chebyshev.psi (4*n:ℕ)-Chebyshev.theta (4*n:ℕ) := by
    rw [Chebyshev.psi_sub_theta_eq_sum_not_prime,Nat.floor_natCast]
    apply (abs_sum_le_sum_abs _ _).trans
    apply le_trans (b:=∑ p ∈ T,vonMangoldt p)
    · apply sum_le_sum
      intro p hp
      have hp0 := hA.trans (mem_Ico.mp (mem_filter.mp hp).1).1
      dsimp only [f]
      rw [abs_mul,abs_of_nonneg vonMangoldt_nonneg]
      exact mul_le_of_le_one_right vonMangoldt_nonneg (abs_midpoint_division_le_one hp0 n)
    · apply sum_le_sum_of_subset_of_nonneg _ (fun _ _ _ => vonMangoldt_nonneg)
      intro p hp
      obtain ⟨hs,hp⟩ := mem_filter.mp hp
      obtain ⟨hl,hu⟩ := mem_Ico.mp hs
      exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨hA.trans hl,hu.le.trans hB⟩,hp⟩
  have hs : Real.sqrt (4*n:ℕ) ≤ 2*(n:ℝ)^(t+ε) := by
    rw [Nat.cast_mul,Nat.cast_ofNat,Real.sqrt_mul (by norm_num : (0:ℝ)≤4),
      show Real.sqrt 4=2 by norm_num,Real.sqrt_eq_rpow]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [ht,he])) (by norm_num)
  have he' := hprice.trans ((hD ((4*n:ℕ):ℝ)).trans (mul_le_mul (le_abs_self D) hs
    (Real.sqrt_nonneg _) (abs_nonneg _)))
  have heq : midpointFloorPrimeBlock n A B=(∑ p ∈ s,f p)-(∑ p ∈ T,f p) := by
    change _ + (∑ p ∈ T,f p)=_ at hsplit
    linarith only [hsplit]
  rw [heq]
  exact (abs_sub _ _).trans ((add_le_add hall he').trans_eq (by ring))

#print axioms large_midpoint_prime_block

/-- Summing dyadic blocks whose individual bound is L costs at most a
fixed multiple of L B^σ for any positive σ. -/
private theorem dyadic_terminal_bound {σ : ℝ} (hσ : 0 < σ) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ (B A n : ℕ) {L : ℝ}, 0 ≤ L → 1 ≤ A → A ≤ B →
      (∀ X Y : ℕ,A ≤ X → X < Y → Y ≤ B → Y ≤ 2*X → |midpointFloorPrimeBlock n X Y| ≤ L) →
      |midpointFloorPrimeBlock n A B| ≤ K*L*(B:ℝ)^σ := by
  let q := (3/4:ℝ)^σ
  have hq0 : 0 ≤ q := Real.rpow_nonneg (by norm_num) _
  have hq : q < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hσ
  let K := 1/(1-q)
  have hK : 1 ≤ K := (le_div_iff₀ (sub_pos.mpr hq)).mpr (by linarith only [hq0])
  have hKq : K*(1-q)=1 := div_mul_cancel₀ _ (sub_ne_zero.mpr hq.ne')
  have hcontract : (K+1)*q ≤ K := by linarith only [hKq,hq]
  refine ⟨K,hK,?_⟩
  intro B
  induction B using Nat.strong_induction_on with
  | h B ih =>
    intro A n L hL hA hAB hlocal
    have hK0 : 0 ≤ K := zero_le_one.trans hK
    have hsmall {X : ℕ} (hX : 1 ≤ X) : L ≤ L*(X:ℝ)^σ :=
      le_mul_of_one_le_right hL (Real.one_le_rpow (Nat.one_le_cast.mpr hX) hσ.le)
    rcases eq_or_lt_of_le hAB with rfl | hAB'
    · simp only [midpointFloorPrimeBlock,Ico_self,filter_empty,sum_empty,abs_zero]
      positivity
    by_cases hshort : B ≤ 2*A
    · have h := (hlocal A B le_rfl hAB' le_rfl hshort).trans (hsmall (hA.trans hAB'.le))
      exact h.trans ((mul_le_mul_of_nonneg_right (le_mul_of_one_le_left hL hK) (by positivity)))
    · let M := (B+1)/2
      have ham : A ≤ M := by dsimp only [M]; omega
      have hmb : M < B := by dsimp only [M]; omega
      have h2 : B ≤ 2*M := by dsimp only [M]; omega
      have hratio : (M:ℝ) ≤ (3/4:ℝ)*B := by
        have h : 4*M ≤ 3*B := by dsimp only [M]; omega
        have hh : 4*(M:ℝ) ≤ 3*B := by exact_mod_cast h
        linarith only [hh]
      have hscale := Real.rpow_le_rpow (Nat.cast_nonneg _) hratio hσ.le
      rw [Real.mul_rpow (by norm_num : (0:ℝ)≤3/4) (Nat.cast_nonneg B)] at hscale
      have hl := ih M hmb A n hL hA ham (fun X Y hX hXY hY hdy => hlocal X Y hX hXY (hY.trans hmb.le) hdy)
      have hr := (hlocal M B ham hmb le_rfl h2).trans (hsmall (hA.trans ham))
      rw [←midpoint_floor_block_append n ham hmb.le]
      apply (abs_add_le _ _).trans
      calc _ ≤ (K+1)*L*(M:ℝ)^σ := (add_le_add hl hr).trans_eq (by ring)
           _ ≤ (K+1)*L*(q*(B:ℝ)^σ) := mul_le_mul_of_nonneg_left hscale (by positivity)
           _ ≤ _ := by
             rw [show (K+1)*L*(q*(B:ℝ)^σ)=((K+1)*q)*L*(B:ℝ)^σ by ring]
             exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcontract hL) (by positivity)

private theorem absolute_floor_block (n A B : ℕ) (ha : 1 ≤ A) :
    |midpointFloorPrimeBlock n A B| ≤ 7*B := by
  apply (abs_sum_le_sum_abs _ _).trans
  calc _ ≤ ∑ p ∈ (Ico A B).filter Nat.Prime,vonMangoldt p := by
              apply sum_le_sum
              intro p hp
              have hpr := (mem_filter.mp hp).2
              rw [abs_mul,abs_of_nonneg (Real.log_natCast_nonneg p),vonMangoldt_apply_prime hpr]
              exact mul_le_of_le_one_right (Real.log_natCast_nonneg p) (abs_midpoint_division_le_one hpr.pos n)
       _ ≤ ∑ p ∈ Icc 1 B,vonMangoldt p := by
              apply sum_le_sum_of_subset_of_nonneg _ (fun _ _ _ => vonMangoldt_nonneg)
              intro p hp
              obtain ⟨hl,hu⟩ := mem_Ico.mp (mem_filter.mp hp).1
              exact mem_Icc.mpr ⟨ha.trans hl,hu.le⟩
       _ ≤ _ := _root_.RHTower.sum_vonMangoldt_Icc_le_seven B

/-- All ordinary-prime intervals below the power cutoff have price at
most a constant times n^(t+ε), at every integer center. -/
theorem large_midpoint_prime_shell {t ε : ℝ} (ht : 1/2 ≤ t) (ht1 : t < 1) (he : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {n A B : ℕ}, 1 ≤ n → 1 ≤ A → A ≤ B →
      B ≤ ⌊(n:ℝ)^(reflectedPrimeShellExponent t)⌋₊+1 →
      |midpointFloorPrimeBlock n A B| ≤ C*(n:ℝ)^(t+ε) := by
  let η := ε/3
  have hη : 0 < η := by dsimp only [η]; linarith only [he]
  obtain ⟨D,hD,hblocks⟩ := large_midpoint_prime_block ht ht1 hη
  obtain ⟨K,hK,hsum⟩ := dyadic_terminal_bound hη
  obtain ⟨N,hN⟩ := eventually_atTop.mp hblocks
  let a := reflectedPrimeShellExponent t
  let C := 14+K*D*(2:ℝ)^η+14*(N:ℝ)
  have hK0 := zero_le_one.trans hK
  have hc : 0 ≤ C := by dsimp only [C]; positivity
  refine ⟨C,hc,?_⟩
  intro n A B hn ha hab hB
  let P (r : ℝ) := (n:ℝ)^r
  have hn1 := (Nat.one_le_cast (α:=ℝ)).mpr hn
  have pos (r : ℝ) : 0 < P r := Real.rpow_pos_of_pos (zero_lt_one.trans_le hn1) _
  have mono {r s : ℝ} (h : r ≤ s) : P r ≤ P s := Real.rpow_le_rpow_of_exponent_le hn1 h
  have hp1 : 1 ≤ P t := Real.one_le_rpow hn1 (by linarith only [ht])
  obtain ⟨_,ha1,_⟩ := reflected_prime_shell_exponents ht ht1
  change a < 1 at ha1
  have hPa : P a ≤ n := (mono ha1.le).trans_eq (Real.rpow_one _)
  have hcap : B ≤ 2*n := by
    have hf : ⌊P a⌋₊ ≤ n := Nat.cast_le.mp ((Nat.floor_le (pos a).le).trans hPa)
    change B ≤ ⌊P a⌋₊+1 at hB
    omega
  by_cases hlate : N ≤ n
  · let Z := ⌈P t⌉₊
    have hZ : (Z:ℝ) ≤ 2*P t := (Nat.ceil_lt_add_one (pos t).le).le.trans (by linarith only [hp1])
    let M := min B (max A Z)
    have ham : A ≤ M := le_min hab (le_max_left _ _)
    have hmb : M ≤ B := min_le_left _ _
    have hz1 := mul_nonneg (mul_nonneg hK0 hD) (Real.rpow_nonneg (by norm_num : (0:ℝ)≤2) η)
    have heT : P t ≤ P (t+ε) := mono (by linarith only [he])
    have hl : |midpointFloorPrimeBlock n A M| ≤ 14*P (t+ε) := by
      by_cases hz : Z ≤ A
      · have hM : M=A := by dsimp only [M]; rw [max_eq_left hz,min_eq_right hab]
        simp only [hM,midpointFloorPrimeBlock,Ico_self,filter_empty,sum_empty,abs_zero]
        positivity
      · have hmz : M ≤ Z := by dsimp only [M]; rw [max_eq_right (le_of_not_ge hz)]; exact min_le_right _ _
        have hh := absolute_floor_block n A M ha
        have hh' := (Nat.cast_le (α:=ℝ)).mpr hmz
        linarith only [hh,hh',hZ,heT]
    have hr : |midpointFloorPrimeBlock n M B| ≤ K*D*(2:ℝ)^η*P (t+ε) := by
      obtain hEq | hneq := eq_or_lt_of_le hmb
      · rw [hEq,midpointFloorPrimeBlock,Ico_self,filter_empty,sum_empty,abs_zero]
        positivity
      · have hzm : Z ≤ M := by
          dsimp only [M] at hneq ⊢
          rw [min_eq_right (by omega : max A Z ≤ B)]
          exact le_max_right _ _
        have hfra : (B:ℝ)^η ≤ (2:ℝ)^η*P η := by
          rw [←Real.mul_rpow (by norm_num : (0:ℝ)≤2) (Nat.cast_nonneg n)]
          exact Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hcap) hη.le
        have htall := hsum B M n (L:=D*P (t+η)) (mul_nonneg hD (pos _).le) (ha.trans ham) hmb
          (fun X Y hMX hXY hY hdy => by
            have hXu : X ≤ ⌊P a⌋₊ := by change B ≤ ⌊P a⌋₊+1 at hB; omega
            have hXl : P t ≤ (X:ℝ) := (Nat.le_ceil _).trans (Nat.cast_le.mpr (hzm.trans hMX))
            exact hN n hlate hXY.le hdy hXl ((Nat.cast_le.mpr hXu).trans (Nat.floor_le (pos a).le)))
        have hprod : P (t+η)*P η ≤ P (t+ε) := by
          dsimp only [P]
          rw [←Real.rpow_add (zero_lt_one.trans_le hn1)]
          exact mono (by dsimp only [η]; linarith only [he])
        apply htall.trans ((mul_le_mul_of_nonneg_left hfra (by positivity)).trans ?_)
        calc _ = (K*D*(2:ℝ)^η)*(P (t+η)*P η) := by ring
             _ ≤ _ := mul_le_mul_of_nonneg_left hprod hz1
    rw [←midpoint_floor_block_append n ham hmb]
    apply (abs_add_le _ _).trans ((add_le_add hl hr).trans ?_)
    dsimp only [C]
    linarith only [mul_nonneg (Nat.cast_nonneg (α:=ℝ) N) (pos (t+ε)).le]
  · have hh := absolute_floor_block n A B ha
    have hsmall : B ≤ 2*N := by omega
    have hB' : (B:ℝ) ≤ 2*N := by exact_mod_cast hsmall
    have hp : 1 ≤ P (t+ε) := hp1.trans (mono (by linarith only [he]))
    apply (le_mul_of_one_le_right hc hp).trans' ?_
    dsimp only [C]
    linarith only [hh,hB',mul_nonneg (mul_nonneg hK0 hD) (Real.rpow_nonneg (by norm_num : (0:ℝ)≤2) η)]

#print axioms large_midpoint_prime_shell

/-- After moving the prime cutoff through the wider shell, the remaining
joint cofactor price retains its full factorial center at the target power. -/
theorem midpoint_after_large_ordinary_prime_shell {t ε : ℝ} (ht : 1/2 ≤ t) (ht1 : t < 1)
    (he : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {n Q : ℕ}, 1 ≤ n → Q ≤ ⌊(n:ℝ)^(reflectedPrimeShellExponent t)⌋₊ →
      |unrestrictedLargePrimePrice n Q-completeMidpointFactorial n-primeMidpointPrice n| ≤
        C*(n:ℝ)^(t+ε) := by
  obtain ⟨K,hK,hshell⟩ := large_midpoint_prime_shell ht ht1 he
  obtain ⟨D,hD⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  refine ⟨2*|D|+K,by positivity,?_⟩
  intro n Q hn hQ
  have hn1 := (Nat.one_le_cast (α:=ℝ)).mpr hn
  obtain ⟨_,ha,_⟩ := reflected_prime_shell_exponents ht ht1
  have hQt : (Q:ℝ) ≤ n := (Nat.cast_le.mpr hQ).trans ((Nat.floor_le (by positivity)).trans
    ((Real.rpow_le_rpow_of_exponent_le hn1 ha.le).trans_eq (Real.rpow_one _)))
  have hcap : Q ≤ 2*n := (Nat.cast_le.mp hQt).trans (by omega)
  have hi : Ico 1 (Q+1)=Ioc 0 Q := by ext p; simp only [mem_Ico,mem_Ioc]; omega
  have hj : midpointFloorPrimeBlock n 1 (Q+1)+unrestrictedLargePrimePrice n Q=unrestrictedLargePrimePrice n 0 := by
    simp only [midpointFloorPrimeBlock,hi,unrestrictedLargePrimePrice,sum_filter]
    exact sum_Ioc_consecutive _ (Nat.zero_le _) hcap
  have heq : unrestrictedLargePrimePrice n Q-completeMidpointFactorial n-primeMidpointPrice n =
      (unrestrictedLargePrimePrice n 0-completeMidpointFactorial n-primeMidpointPrice n)-
        midpointFloorPrimeBlock n 1 (Q+1) := by linarith only [hj]
  have hbase := unrestricted_large_prime_factorial_error (n:=n) hn (Nat.zero_le (2*n))
  have hzero : Chebyshev.psi (0:ℕ)=0 := by simp [Chebyshev.psi]
  rw [hzero,zero_add] at hbase
  have hs : Real.sqrt (4*n:ℕ) ≤ 2*(n:ℝ)^(t+ε) := by
    rw [Nat.cast_mul,Nat.cast_ofNat,Real.sqrt_mul (by norm_num : (0:ℝ)≤4),
      show Real.sqrt 4=2 by norm_num,Real.sqrt_eq_rpow]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [ht,he])) (by norm_num)
  have hh := hbase.trans ((hD ((4*n:ℕ):ℝ)).trans (mul_le_mul (le_abs_self D) hs
    (Real.sqrt_nonneg _) (abs_nonneg _)))
  have hlow := hshell (A:=1) (B:=Q+1) hn le_rfl (by omega) (Nat.add_le_add_right hQ 1)
  rw [heq]
  exact (abs_sub _ _).trans ((add_le_add hh hlow).trans_eq (by ring))

#print axioms midpoint_after_large_ordinary_prime_shell

/-- The linear center of the unrestricted cofactor price at the wider
prime cut is independent of the arithmetic of the center n. -/
theorem large_prime_shell_linear_center {b ε : ℝ} (hb : 1/2 ≤ b) (hb1 : b < 1) (he : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {n Q : ℕ}, 1 ≤ n → Q ≤ ⌊(n:ℝ)^(reflectedPrimeShellExponent b)⌋₊ →
      |unrestrictedLargePrimePrice n Q-reflectedDensity*n-primeMidpointPrice n| ≤ C*(n:ℝ)^(b+ε) := by
  obtain ⟨K,hK,h⟩ := midpoint_after_large_ordinary_prime_shell hb hb1 he
  let J := (Real.log 4-2*Real.log 3+Real.log 2)/2
  refine ⟨K+1+|J|,by positivity,?_⟩
  intro n Q hn hQ
  have hF : |completeMidpointFactorial n-reflectedDensity*n-J| ≤ 1/(n:ℝ) := reflected_factorial_center hn
  have hF' := hF.trans (div_le_self zero_le_one (Nat.one_le_cast.mpr hn))
  have hh := h hn hQ
  have hp : 1 ≤ (n:ℝ)^(b+ε) := Real.one_le_rpow (Nat.one_le_cast.mpr hn) (by linarith only [hb,he])
  have hJ := le_mul_of_one_le_right (abs_nonneg J) hp
  have h := abs_le.mp hh
  have hf := abs_le.mp hF'
  rw [abs_le]
  constructor <;> linarith only [h.1,h.2,hf.1,hf.2,hJ,neg_abs_le J,le_abs_self J,hp]

/-- At this prime cut the one-sided all-center price bound still has
the exact zeta-zero abscissa as its threshold. -/
theorem large_prime_shell_upper_spectrum {b : ℝ} (hb : 1/2 ≤ b) (hb1 : b < 1) :
    (∀ t : ℝ,b < t → t < 1 → ∃ C : ℝ,∀ n : ℕ,1 ≤ n →
      unrestrictedLargePrimePrice n ⌊(n:ℝ)^(reflectedPrimeShellExponent b)⌋₊-reflectedDensity*n ≤
        C*(n:ℝ)^t) ↔ _root_.RHTower.zetaZeroAbscissa ≤ b := by
  rw [←prime_midpoint_upper_spectrum_iff hb]
  constructor <;> intro h t ht ht1 <;> obtain ⟨K,hK⟩ := h t ht ht1 <;>
    obtain ⟨A,_,hA⟩ := large_prime_shell_linear_center hb hb1 (sub_pos.mpr ht) <;>
    refine ⟨K+A,fun n hn => ?_⟩
  · have h := abs_le.mp (hA hn (le_refl ⌊(n:ℝ)^(reflectedPrimeShellExponent b)⌋₊))
    rw [show b+(t-b)=t by ring] at h
    linarith only [h.1,hK n hn]
  · have h := abs_le.mp (hA hn (le_refl ⌊(n:ℝ)^(reflectedPrimeShellExponent b)⌋₊))
    rw [show b+(t-b)=t by ring] at h
    linarith only [h.2,hK n hn]

#print axioms large_prime_shell_linear_center
#print axioms large_prime_shell_upper_spectrum

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
