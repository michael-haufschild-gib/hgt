import GaloisForLFunctions.ExceptionalLayerTheory.CenteringTheFactorialPrimeWeight
import GaloisForLFunctions.PrimeExponentialSums.FractionalPartsOnIntegerReciprocalBlocks
import GaloisForLFunctions.RHTower.Sieve.KubalalikaDyadic

/-!
# Integer cancellation on middle divisor intervals

The reciprocal phase has controlled curvature near the square root.
Summing the sharp dyadic estimates also covers each truncated divisor progression.
-/

noncomputable section
open Finset RHTower
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

private theorem middle_divisor_block :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {T e d A B : ℕ}, 1 ≤ T → 1 ≤ e → 1 ≤ d → 1 ≤ A → A < B → B ≤ 2*A →
      (T : ℝ)^(49/100 : ℝ) ≤ e*(A : ℝ) → (A : ℝ) ≤ (T : ℝ)^(51/100 : ℝ) →
      |∑ t ∈ Ico A B, centeredQuotient T (e*t) d| ≤ C*(d*e : ℕ)*(T : ℝ)^(47/100 : ℝ) := by
  obtain ⟨C,hC,h⟩ := PrimeExponentialSums.centered_fractional_reciprocal_integer_block
  refine ⟨4*C,by positivity,?_⟩
  intro T e d A B hT he hd hA hAB hB hlo hhi
  have hx : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hx₀ := zero_lt_one.trans_le hx
  have hA₀ : (0 : ℝ) < A := by exact_mod_cast hA
  have he₁ : (1 : ℝ) ≤ e := by exact_mod_cast he
  have hd₁ : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hde := one_le_mul_of_one_le_of_one_le hd₁ he₁
  have hde₀ := zero_lt_one.trans_le hde
  let P (b : ℝ) := (T : ℝ)^b
  have pos (b : ℝ) : 0 < P b := Real.rpow_pos_of_pos hx₀ _
  have mul (a b : ℝ) : P a*P b=P (a+b) := (Real.rpow_add hx₀ _ _).symm
  have powr (a b : ℝ) : (P a)^b = P (a*b) := (Real.rpow_mul hx₀.le _ _).symm
  have mono {a b : ℝ} (hz : a ≤ b) : P a ≤ P b := Real.rpow_le_rpow_of_exponent_le hx hz
  have one : P 1 = T := Real.rpow_one _
  let Z := (T : ℝ)/((d : ℝ)*e)
  let curvature := 2*Z/(2*(A : ℝ))^3
  let δ := P (-(4/100))
  have hZ : 0 < Z := div_pos hx₀ hde₀
  have curvature_pos : 0 < curvature := by dsimp [curvature]; positivity
  have hδ : 0 < δ := pos _
  have curvature_identity : curvature*(4*((d : ℝ)*e)*(A : ℝ)^3)=T := by
    dsimp [curvature,Z]; field_simp; ring
  have sqrt_sq := Real.sq_sqrt curvature_pos.le
  have first : (A : ℝ)*Real.sqrt curvature ≤ P (255/1000) := by
    have four : (1 : ℝ) ≤ 4*(d : ℝ) := by linarith only [hd₁]
    have scale := le_mul_of_one_le_left (mul_nonneg (Nat.cast_nonneg e) hA₀.le) four
    have lower : P (49/100) ≤ 4*((d : ℝ)*e)*A := hlo.trans (scale.trans_eq (by ring))
    have hlower : (T : ℝ) ≤ (P (255/1000))^2*(4*((d : ℝ)*e)*A) := by
      calc (T : ℝ) = (P (255/1000))^2*P (49/100) := by
              rw [←Real.rpow_natCast _ 2,powr,mul]; norm_num [P]
           _ ≤ _ := mul_le_mul_of_nonneg_left lower (sq_nonneg _)
    have hs : ((A : ℝ)*Real.sqrt curvature)^2*(4*((d : ℝ)*e)*A)=T := by
      rw [mul_pow,sqrt_sq,←curvature_identity]; ring
    have hh := le_of_mul_le_mul_right (hs.trans_le hlower) (by positivity : 0 < 4*((d : ℝ)*e)*A)
    nlinarith only [hh,(pos (255/1000)).le,mul_nonneg hA₀.le (Real.sqrt_nonneg curvature)]
  have second : 1/Real.sqrt curvature ≤ 2*((d : ℝ)*e)*P (265/1000) := by
    have hcube := pow_le_pow_left₀ hA₀.le hhi 3
    change (A : ℝ)^3 ≤ (P (51/100))^3 at hcube
    have ht : (P (265/1000))^2*T = (P (51/100))^3 := by
      rw [←Real.rpow_natCast _ 2,←Real.rpow_natCast _ 3,powr,powr,←one,mul]; norm_num
    have hs : (2*((d : ℝ)*e)*P (265/1000)*Real.sqrt curvature)^2*(A : ℝ)^3 =
        ((d : ℝ)*e)*((P (265/1000))^2*T) := by
      rw [mul_pow,sqrt_sq,←curvature_identity]; ring
    have hl := hcube.trans (le_mul_of_one_le_left (by positivity) hde)
    rw [←ht,←hs] at hl
    have hh := le_of_mul_le_mul_right (by simpa only [one_mul] using hl :
      1*(A : ℝ)^3 ≤ (2*((d : ℝ)*e)*P (265/1000)*Real.sqrt curvature)^2*(A : ℝ)^3) (pow_pos hA₀ 3)
    apply (div_le_iff₀ (Real.sqrt_pos.mpr curvature_pos)).mpr
    nlinarith only [hh,show 0 ≤ 2*((d : ℝ)*e)*P (265/1000)*Real.sqrt curvature by positivity]
  have small : δ*(A : ℝ) ≤ P (47/100) := by
    apply (mul_le_mul_of_nonneg_left hhi hδ.le).trans_eq
    dsimp only [δ]; rw [mul]; norm_num
  have large : ((A : ℝ)*Real.sqrt curvature+1/Real.sqrt curvature)/δ ≤ 3*((d : ℝ)*e)*P (47/100) := by
    apply (div_le_iff₀ hδ).mpr
    have hb : P (265/1000) ≤ P (47/100)*δ := by
      dsimp only [δ]; rw [mul]; apply mono; norm_num
    have hh := (first.trans (mono (by norm_num : (255/1000:ℝ) ≤ 265/1000))).trans
      (le_mul_of_one_le_left (pos _).le hde)
    have hm := mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ 3*((d : ℝ)*e))
    linarith only [hh,second,hm]
  have hsum := h hA le_rfl hAB.le hB hZ hδ
  have ht : (∑ t ∈ Ico A B, centeredQuotient T (e*t) d) =
      ∑ t ∈ Ico A B, (Int.fract (Z/t)-1/2) := by
    apply sum_congr rfl
    intro t _
    dsimp only [centeredQuotient,Z]
    rw [Nat.cast_mul,div_mul_eq_div_div,div_mul_eq_div_div]
  rw [ht,Nat.cast_mul]
  apply hsum.trans
  have hsmall := small.trans (le_mul_of_one_le_left (pos _).le hde)
  exact (mul_le_mul_of_nonneg_left (add_le_add hsmall large) hC).trans_eq (by dsimp [P]; ring)

/-- Centered fractional quotients on any middle interval of a divisor progression. -/
theorem middle_divisor_interval :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {T L U e d : ℕ}, 1 ≤ T → 1 ≤ e → 1 ≤ d →
      (T : ℝ)^(49/100 : ℝ) < (L : ℝ)+1 → (U : ℝ) ≤ (T : ℝ)^(51/100 : ℝ) →
      |∑ t ∈ Ioc (L/e) (U/e), centeredQuotient T (e*t) d| ≤
        C*(d*e : ℕ)*(1+Real.log T)*(T : ℝ)^(47/100 : ℝ) := by
  obtain ⟨C,hC,h⟩ := middle_divisor_block
  refine ⟨4*C,by positivity,?_⟩
  intro T L U e d hT he hd hlo hhi
  let lo := L/e+1
  let hi := U/e+1
  have hx : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hlog := Real.log_natCast_nonneg T
  have huT : U ≤ T := by exact_mod_cast hhi.trans ((Real.rpow_le_rpow_of_exponent_le hx
    (by norm_num : (51/100 : ℝ) ≤ 1)).trans_eq (Real.rpow_one _))
  have heq : Ioc (L/e) (U/e) = Ico lo hi := by ext t; simp only [mem_Ioc,mem_Ico,lo,hi]; omega
  rw [heq]
  by_cases hhh : lo ≤ hi
  swap
  · rw [Ico_eq_empty (by omega),sum_empty,abs_zero]
    positivity
  let M := C*(d*e : ℕ)*(T : ℝ)^(47/100 : ℝ)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hdya := Sieve.norm_sum_Ico_le_of_blocks (fun t => centeredQuotient T (e*t) d) M hhh
    (Nat.succ_pos _) hM (fun A B hA hAB hB hl hu => by
      rw [Real.norm_eq_abs]
      rcases hAB.eq_or_lt with rfl | hlt
      · simpa only [Ico_self,sum_empty,abs_zero] using hM
      · have hmul := (Nat.div_lt_iff_lt_mul he).mp (show L/e < A by exact hl)
        have hAl : (L : ℝ)+1 ≤ e*(A : ℝ) := by
          have hlt : L < e*A := by simpa only [Nat.mul_comm] using hmul
          exact_mod_cast (by omega : L+1 ≤ e*A)
        have hAu : A ≤ U := (show A ≤ U/e by dsimp [hi] at hu; omega).trans (Nat.div_le_self ..)
        exact h hT he hd hA hlt hB (hlo.le.trans hAl) ((by exact_mod_cast hAu : (A : ℝ) ≤ U).trans hhi))
  have hhi' : (hi : ℝ) ≤ 2*T := by
    have hh : hi ≤ T+1 := Nat.succ_le_succ ((Nat.div_le_self ..).trans huT)
    exact_mod_cast (by omega : hi ≤ 2*T)
  have hl := Real.log_le_log (by dsimp [hi]; positivity : (0 : ℝ) < hi) hhi'
  rw [Real.log_mul (by norm_num) (zero_lt_one.trans_le hx).ne'] at hl
  have hloghi : 1+Real.log hi ≤ 2*(1+Real.log T) := by
    linarith only [hl,hlog,Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hloghi (by norm_num : (0 : ℝ) ≤ 2)) hM
  rw [Real.norm_eq_abs] at hdya
  exact hdya.trans (hh.trans_eq (by dsimp [M]; ring))

/-- The full short side of the divisor hyperbola has a power saving.
Small divisors cost their length and all larger divisors lie in the
sharp middle interval. -/
theorem sum_centered_quotient_to_sqrt :
    ∃ C : ℝ, 0≤C ∧ ∀ {N : ℕ}, 1≤N →
      |∑ d ∈ Icc 1 (Nat.sqrt N), centeredQuotient N d 1| ≤
        C*(1+Real.log N)*(N : ℝ)^(49/100 : ℝ) := by
  obtain ⟨K,hK,h⟩ := middle_divisor_interval
  refine ⟨1+K,by positivity,?_⟩
  intro N hN
  let L := ⌊(N : ℝ)^(49/100 : ℝ)⌋₊
  let s := Nat.sqrt N
  let P := (N : ℝ)^(49/100 : ℝ)
  let J := 1+Real.log N
  have hn : (1 : ℝ)≤N := by exact_mod_cast hN
  have hP : 0≤P := by dsimp [P]; positivity
  have hJ : 1≤J := le_add_of_nonneg_right (Real.log_natCast_nonneg _)
  have hL : (L : ℝ)≤P := Nat.floor_le hP
  have hhalf : P≤Real.sqrt N := by
    rw [Real.sqrt_eq_rpow]; exact Real.rpow_le_rpow_of_exponent_le hn (by norm_num)
  have hLs : L ≤ s := by
    apply Nat.le_sqrt.mpr
    have hz := mul_self_le_mul_self (Nat.cast_nonneg L) (hL.trans hhalf)
    rw [Real.mul_self_sqrt (Nat.cast_nonneg N)] at hz
    exact_mod_cast hz
  have hsmall : |∑ d ∈ Ioc 0 L, centeredQuotient N d 1|≤P := by
    apply (abs_sum_le_sum_abs _ _).trans
    calc _ ≤ ∑ _d ∈ Ioc 0 L, (1 : ℝ) := by
              apply sum_le_sum; intro d _
              unfold centeredQuotient; rw [abs_le]
              constructor <;> linarith only [Int.fract_nonneg (((N : ℝ)/1)/d),Int.fract_lt_one (((N : ℝ)/1)/d)]
         _ = (L : ℝ) := by simp
         _ ≤ _ := hL
  have htop : (s : ℝ)≤(N : ℝ)^(51/100 : ℝ) := by
    apply (Real.nat_sqrt_le_real_sqrt (a := N)).trans
    rw [Real.sqrt_eq_rpow]; exact Real.rpow_le_rpow_of_exponent_le hn (by norm_num)
  have hmiddle := h (e := 1) (d := 1) hN (by decide) (by decide)
    (show (N : ℝ)^(49/100 : ℝ)<(L : ℝ)+1 from Nat.lt_floor_add_one _) htop
  simp only [Nat.div_one,Nat.one_mul,Nat.cast_one,mul_one] at hmiddle
  have hex : (N : ℝ)^(47/100 : ℝ)≤P := Real.rpow_le_rpow_of_exponent_le hn (by norm_num)
  have hcost := mul_le_mul_of_nonneg_left hex (mul_nonneg hK (zero_le_one.trans hJ))
  have hshort := le_mul_of_one_le_left hP hJ
  rw [show Icc 1 s=Ioc 0 s by ext d; simp only [mem_Icc,mem_Ioc]; omega,
    ←sum_Ioc_consecutive (fun d => centeredQuotient N d 1) (Nat.zero_le L) hLs]
  apply (abs_add_le _ _).trans ((add_le_add hsmall (hmiddle.trans hcost)).trans _)
  change P+K*J*P≤(1+K)*J*P
  linarith only [hshort]

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
