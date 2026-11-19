import GaloisForLFunctions.PrimeExponentialSums.FractionalPartsOnIntegerReciprocalBlocks
import GaloisForLFunctions.RHTower.BourgainPartialSummation
import GaloisForLFunctions.RHTower.ZetaSymbolArchimedeanHorizon

/-!
# Centered floor errors at moving divisor endpoints

Fixing the divisor in the floor of m^(r+1)/d leaves a contiguous interval
of conductors. Its polynomial phase has curvature comparable to k/D
throughout D ≤ m ≤ 2D and d comparable to D^r. Summing conductors before
divisors gives a power saving after normalization by the product horizon,
uniformly over signed weights dominated by the von Mangoldt function.
-/

noncomputable section
open Finset

namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

private theorem monomial_derivative (a b x : ℝ) (n : ℕ) :
    HasDerivAt (fun y : ℝ => a*y^(n+1)+b) (a*((n:ℝ)+1)*x^n) x := by
  convert! ((((hasDerivAt_id x).pow (n+1)).const_mul a).add_const b) using 1
  simp only [id_eq,Nat.cast_succ,Nat.add_sub_cancel,mul_one]
  ring

private theorem monomial_derivative' (a x : ℝ) (n : ℕ) :
    HasDerivAt (fun y : ℝ => a*y^(n+1)) (a*((n:ℝ)+1)*x^n) x := by
  simpa only [add_zero] using monomial_derivative a 0 x n

/-- Every positive integral frequency has square-root cancellation up
to its frequency loss, uniformly over both ends of the conductor interval. -/
theorem conductor_monomial_phase_bound (s : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {D d k a b : ℝ} {N : ℕ}, 0 < D → 1 ≤ k →
      D^(s+1) ≤ d → d ≤ 2*(2*D)^(s+1) → D ≤ a →
      a+((N-1:ℕ):ℝ) ≤ 2*D → (N:ℝ) ≤ D →
      ‖∑ n ∈ range N, Complex.exp (((2*Real.pi*((k/d)*(a+n)^(s+2)+b) : ℝ) : ℂ)*Complex.I)‖ ≤
        C*Real.sqrt (D*k) := by
  let G : ℝ := ((s:ℝ)+2)*((s:ℝ)+1)*2^s
  let L : ℝ := 2*2^(s+1)
  have hG : 0 ≤ G := by dsimp only [G]; positivity
  have hL : 1 ≤ L := by
    have hh := one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2) (n := s+1)
    dsimp only [L]; linarith
  have hC : 1 ≤ 8*G+12*Real.sqrt L+1 := by linarith only [hG,Real.sqrt_nonneg L]
  refine ⟨8*G+12*Real.sqrt L+1,hC,?_⟩
  intro D d k a b N hD hk hdlo hdhi ha hend hN
  have hkpos : 0 < k := zero_lt_one.trans_le hk
  have hd : 0 < d := (pow_pos hD _).trans_le hdlo
  have hroot := Real.sqrt_nonneg (D*k)
  have hsq := Real.sq_sqrt (mul_pos hD hkpos).le
  rcases eq_zero_or_pos N with rfl | hlen
  · simp only [range_zero,sum_empty,norm_zero]
    positivity
  by_cases hkD : k ≤ D
  · let A := k/d
    let t := A*D^s
    have hA : 0 < A := div_pos hkpos hd
    have ht : 0 < t := mul_pos hA (pow_pos hD _)
    have htd : t*D ≤ k := by
      change (k/d*D^s)*D ≤ k
      rw [mul_assoc,←pow_succ,div_mul_eq_mul_div,div_le_iff₀ hd]
      exact mul_le_mul_of_nonneg_left hdlo hkpos.le
    have ht1 : t ≤ 1 := (le_div_iff₀ hD).mpr (htd.trans hkD) |>.trans_eq (div_self hD.ne')
    have hdL : d ≤ L*D^(s+1) := by simpa only [L,mul_pow,mul_assoc] using hdhi
    have hkt : k ≤ L*(t*D) := by
      change k ≤ L*((k/d*D^s)*D)
      rw [mul_assoc (k/d),←pow_succ]
      calc k = (k/d)*d := (div_mul_cancel₀ _ hd.ne').symm
           _ ≤ (k/d)*(L*D^(s+1)) := mul_le_mul_of_nonneg_left hdL hA.le
           _ = _ := by ring
    let c := (s:ℝ)+2
    let e := (s:ℝ)+1
    have hce : 1 ≤ c*e := by
      apply one_le_mul_of_one_le_of_one_le <;> dsimp only [c,e] <;> linarith only [Nat.cast_nonneg (α:=ℝ) s]
    have hh := _root_.RHTower.Sieve.second_derivative_test'
      (fun x => A*x^(s+2)+b) (fun x => (A*c)*x^(s+1)) (fun x => (A*c*e)*x^s) a N hlen ht ht1
      (fun x _ => by simpa only [c,Nat.cast_succ,add_assoc,one_add_one_eq_two] using monomial_derivative A b x (s+1))
      (fun x _ => monomial_derivative' (A*c) x s)
      (fun x hx => by
        have h1 := pow_le_pow_left₀ hD.le (ha.trans hx.1) s
        calc t ≤ A*x^s := mul_le_mul_of_nonneg_left h1 hA.le
             _ ≤ c*e*(A*x^s) := le_mul_of_one_le_left (mul_nonneg hA.le (pow_nonneg (hD.le.trans (ha.trans hx.1)) _)) hce
             _ = _ := by ring)
      (hgrow := G)
      (fun x hx => by
        have h1 := pow_le_pow_left₀ (hD.le.trans (ha.trans hx.1)) (hx.2.trans hend) s
        have hp : 0 ≤ A*c*e := by dsimp only [c,e]; positivity
        calc A*c*e*x^s ≤ A*c*e*(2*D)^s := mul_le_mul_of_nonneg_left h1 hp
             _ = G*t := by dsimp only [G,t,c,e]; rw [mul_pow]; ring)
    have hprod : D*Real.sqrt t ≤ Real.sqrt (D*k) := by
      apply (Real.le_sqrt (by positivity) (by positivity)).mpr
      rw [mul_pow,Real.sq_sqrt ht.le]
      calc D^2*t = D*(t*D) := by ring
           _ ≤ D*k := mul_le_mul_of_nonneg_left htd hD.le
    have hk1 : 1 ≤ k^2 := one_le_pow₀ hk
    have hinv : 1/Real.sqrt t ≤ Real.sqrt L*Real.sqrt (D*k) := by
      rw [div_le_iff₀ (Real.sqrt_pos.mpr ht)]
      have h1 := mul_le_mul_of_nonneg_right hkt hkpos.le
      have h2 : 1 ≤ (Real.sqrt L*Real.sqrt (D*k)*Real.sqrt t)^2 := by
        simp only [mul_pow,Real.sq_sqrt (zero_le_one.trans hL),Real.sq_sqrt (mul_pos hD hkpos).le,Real.sq_sqrt ht.le]
        nlinarith only [hk1,h1]
      exact le_of_not_gt fun hz => (not_lt_of_ge h2) (by nlinarith only [mul_self_lt_mul_self (by positivity : 0 ≤ Real.sqrt L*Real.sqrt (D*k)*Real.sqrt t) hz])
    have hm := (mul_le_mul_of_nonneg_right hN (Real.sqrt_nonneg t)).trans hprod
    have hu := add_le_add (mul_le_mul_of_nonneg_left hm (by positivity : 0 ≤ 8*G))
      (mul_le_mul_of_nonneg_left hinv (by norm_num : (0:ℝ) ≤ 12))
    change _ ≤ 8*(N:ℝ)*G*Real.sqrt t+12/Real.sqrt t at hh
    apply hh.trans
    calc _ = 8*G*((N:ℝ)*Real.sqrt t)+12*(1/Real.sqrt t) := by ring
         _ ≤ _ := hu
         _ ≤ _ := by linarith only [hroot]
  · have hsmall : D ≤ Real.sqrt (D*k) := (Real.le_sqrt hD.le (mul_pos hD hkpos).le).mpr (by
      nlinarith only [mul_le_mul_of_nonneg_left (le_of_not_ge hkD) hD.le])
    apply (norm_sum_le _ _).trans
    simp only [Complex.norm_exp,Complex.mul_I_re,Complex.ofReal_im,neg_zero,Real.exp_zero,
      sum_const,card_range,nsmul_eq_mul,mul_one]
    exact (hN.trans hsmall).trans (le_mul_of_one_le_left hroot hC)

/-- Centered fractional parts on every subinterval, including divisibilities.
Taking δ equal to D^(-1/4) gives total discrepancy of order D^(3/4). -/
theorem centered_power_quotient_fragment (s : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ {D d a : ℝ} {N : ℕ}, 0 < D → D^(s+1) ≤ d →
      d ≤ 2*(2*D)^(s+1) → D ≤ a → a+((N-1:ℕ):ℝ) ≤ 2*D → (N:ℝ) ≤ D →
      ∀ δ : ℝ, 0 < δ →
        |∑ n ∈ range N, (Int.fract ((a+n)^(s+2)/d)-1/2)| ≤ B*(δ*D+Real.sqrt D/δ) := by
  obtain ⟨C,hC,hf⟩ := conductor_monomial_phase_bound s
  obtain ⟨K,hK,hs⟩ := GaloisForLFunctions.PrimeExponentialSums.sawtooth_of_sqrt_harmonics
  have hC0 := zero_le_one.trans hC
  refine ⟨K*C,mul_nonneg hK hC0,?_⟩
  intro D d a N hD hlo hhi ha he hN δ hδ
  let y (n : ℕ) := (a+n)^(s+2)/d
  have posmode (k : ℤ) (hk : 0 < k) :
      ‖∑ n ∈ range N, fourier k (y n : UnitAddCircle)‖ ≤ C*Real.sqrt D*Real.sqrt |(k:ℝ)| := by
    have hk1 : (1:ℝ) ≤ k := by exact_mod_cast (show (1:ℤ) ≤ k by omega)
    have ht := hf (b := 0) hD hk1 hlo hhi ha he hN
    rw [Real.sqrt_mul hD.le] at ht
    rw [mul_assoc,abs_of_pos (zero_lt_one.trans_le hk1)]
    apply le_trans _ ht
    apply le_of_eq
    congr 1
    apply sum_congr rfl
    intro n _
    rw [fourier_coe_apply]
    dsimp only [y]
    congr 1
    push_cast
    ring
  have mode (k : ℤ) (hk : k ≠ 0) :
      ‖∑ n ∈ range N, fourier k (y n : UnitAddCircle)‖ ≤ C*Real.sqrt D*Real.sqrt |(k:ℝ)| := by
    rcases lt_or_gt_of_ne hk with hn | hp
    · simpa only [fourier_neg,←map_sum,RCLike.norm_conj,Int.cast_neg,abs_neg] using posmode (-k) (neg_pos.mpr hn)
    · exact posmode k hp
  have ht := hs (range N) y (fun _ => (1:ℂ)) (fun _ => (1:ℝ)) hδ
    (mul_nonneg hC0 (Real.sqrt_nonneg D)) (fun _ => by simp) (fun k hk => by
      simpa only [Complex.ofReal_one,one_mul,and_self] using mode k hk)
  have hu : |∑ n ∈ range N, (Int.fract ((a+n)^(s+2)/d)-1/2)| ≤
      K*(δ*N+(C*Real.sqrt D)/δ) := by
    simpa only [one_mul,←Complex.ofReal_sum,Complex.norm_real,Real.norm_eq_abs,
      GaloisForLFunctions.HTGeometry.SmoothedSawtooth.saw,y,sum_const,card_range,nsmul_eq_mul,mul_one] using ht
  have hmul := (mul_le_mul_of_nonneg_left hN hδ.le).trans
    (le_mul_of_one_le_left (mul_nonneg hδ.le hD.le) hC)
  apply hu.trans
  calc K*(δ*N+(C*Real.sqrt D)/δ) ≤ K*(C*(δ*D)+(C*Real.sqrt D)/δ) :=
           mul_le_mul_of_nonneg_left (add_le_add hmul le_rfl) hK
       _ = _ := by ring

#print axioms conductor_monomial_phase_bound
#print axioms centered_power_quotient_fragment
private def eligibleConductors (s D K d : ℕ) :=
  (Ioc D K).filter (fun m => m^(s+1) < d ∧ d ≤ 2*m^(s+1))

private theorem conductor_interval {s D K d : ℕ} (h : (eligibleConductors s D K d).Nonempty) :
    ∃ a b : ℕ, D < a ∧ b ≤ K ∧ a ≤ b ∧ eligibleConductors s D K d=Icc a b := by
  let S := eligibleConductors s D K d
  let a := S.min' h
  let b := S.max' h
  have ha : a ∈ S := min'_mem _ _
  have hb : b ∈ S := max'_mem _ _
  obtain ⟨haI,haL,haR⟩ := mem_filter.mp ha
  obtain ⟨hbI,hbL,hbR⟩ := mem_filter.mp hb
  refine ⟨a,b,(mem_Ioc.mp haI).1,(mem_Ioc.mp hbI).2,S.min'_le b hb,?_⟩
  ext m
  constructor
  · intro hm
    exact mem_Icc.mpr ⟨S.min'_le _ hm,S.le_max' _ hm⟩
  · intro hm
    obtain ⟨hl,hu⟩ := mem_Icc.mp hm
    exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨(mem_Ioc.mp haI).1.trans_le hl,hu.trans (mem_Ioc.mp hbI).2⟩,
      (Nat.pow_le_pow_left hu _).trans_lt hbL,haR.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hl _))⟩

/-- Centered fractional part of the original multiplication horizon divided by d. -/
def centeredQuotient (s d m : ℕ) : ℝ := Int.fract ((m:ℝ)^(s+2)/d)-1/2

/-- At a fixed divisor the eligible power-sampled conductors form a
single sharp interval, even on an incomplete octave. -/
private theorem centered_conductors_at_divisor (s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {D K d : ℕ}, 1 ≤ D → K ≤ 2*D →
      ∀ δ : ℝ, 0 < δ →
      |∑ m ∈ eligibleConductors s D K d,centeredQuotient s d m| ≤
        C*(δ*D+Real.sqrt D/δ) := by
  obtain ⟨C,hC,hs⟩ := centered_power_quotient_fragment s
  refine ⟨C,hC,?_⟩
  intro D K d hD hK δ hδ
  rcases (eligibleConductors s D K d).eq_empty_or_nonempty with hz | hn
  · rw [hz,sum_empty,abs_zero]
    positivity
  obtain ⟨a,b,ha,hb,hab,he⟩ := conductor_interval hn
  have hma : a ∈ eligibleConductors s D K d := he ▸ left_mem_Icc.mpr hab
  obtain ⟨_,haL,haR⟩ := mem_filter.mp hma
  have hdlo : (D:ℝ)^(s+1) ≤ d := by
    exact_mod_cast (Nat.pow_le_pow_left ha.le (s+1)).trans haL.le
  have hdhi : (d:ℝ) ≤ 2*(2*(D:ℝ))^(s+1) := by
    exact_mod_cast haR.trans (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left (hab.trans (hb.trans hK)) (s+1)))
  let N := b+1-a
  have hN : (N:ℝ) ≤ D := by exact_mod_cast (show N ≤ D by dsimp only [N]; omega)
  have hend : (a:ℝ)+((N-1:ℕ):ℝ) ≤ 2*D := by
    exact_mod_cast (show a+(N-1) ≤ 2*D by dsimp only [N]; omega)
  have h := hs (Nat.cast_pos.mpr hD) hdlo hdhi (Nat.cast_le.mpr ha.le) hend hN δ hδ
  rw [he,←Ico_add_one_right_eq_Icc,sum_Ico_eq_sum_range]
  simpa only [centeredQuotient,Nat.cast_add,N] using h

private def signedFloorCoefficient (s d m : ℕ) : ℝ :=
  if m^(s+1) < d ∧ d ≤ 2*m^(s+1) then centeredQuotient s d m else 0

/-- A decreasing conductor weight costs only its first value on each
sharp fragment of the moving divisor interval. -/
private theorem weighted_conductors_at_divisor (s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {D K : ℕ}, 1 ≤ D → D ≤ K → K ≤ 2*D →
      ∀ (d : ℕ) (δ : ℝ), 0 < δ →
      |∑ m ∈ Ioc D K, ((m:ℝ)^(s+2))⁻¹*signedFloorCoefficient s d m| ≤
        C*(δ*D+Real.sqrt D/δ)*((D:ℝ)^(s+2))⁻¹ := by
  obtain ⟨C,hC,h⟩ := centered_conductors_at_divisor s
  refine ⟨C,hC,?_⟩
  intro D K hD hDK hK d δ hδ
  have hp : 0 < (D:ℝ) := Nat.cast_pos.mpr hD
  have hB : 0 ≤ C*(δ*D+Real.sqrt D/δ) := by positivity
  rcases hDK.eq_or_lt with rfl | hlt
  · rw [Ioc_self,sum_empty,abs_zero]; positivity
  let w (m : ℕ) := ((m:ℝ)^(s+2))⁻¹
  have hw {a b : ℕ} (ha : 0 < a) (hab : a ≤ b) : w b ≤ w a :=
    inv_anti₀ (pow_pos (Nat.cast_pos.mpr ha) _) (pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.cast_le.mpr hab) _)
  have pref (n : ℕ) (hn : n ∈ Ioc D K) :
      ‖∑ m ∈ Ioc D n, ((signedFloorCoefficient s d m:ℝ):ℂ)‖ ≤ C*(δ*D+Real.sqrt D/δ) := by
    rw [←Complex.ofReal_sum,Complex.norm_real,Real.norm_eq_abs]
    simpa only [eligibleConductors,sum_filter,signedFloorCoefficient] using h hD ((mem_Ioc.mp hn).2.trans hK) (d := d) δ hδ
  have hb := _root_.RHTower.norm_sum_Ioc_weight_mul_le (fun m => ((signedFloorCoefficient s d m:ℝ):ℂ)) w hlt
    (fun m => by dsimp only [w]; positivity) (fun m hm => hw (hD.trans (mem_Ioc.mp hm).1.le) (Nat.le_succ _)) pref
  simp only [←Complex.ofReal_mul,←Complex.ofReal_sum,Complex.norm_real,Real.norm_eq_abs] at hb
  exact hb.trans (mul_le_mul_of_nonneg_left (hw hD (Nat.le_succ _)) hB)

#print axioms weighted_conductors_at_divisor

/-- Total centered division error, normalized by the product horizon,
on one arbitrary partial octave of conductors. -/
def sparseFloorFragment (s D K : ℕ) (w : ℕ → ℝ) : ℝ :=
  ∑ m ∈ Ioc D K, ((m:ℝ)^(s+2))⁻¹*
    ∑ d ∈ Ioc (m^(s+1)) (2*m^(s+1)), w d*centeredQuotient s d m

private theorem transpose_floor_fragment (s D K : ℕ) (hK : K ≤ 2*D) (w : ℕ → ℝ) :
    sparseFloorFragment s D K w =
      ∑ d ∈ Icc 1 (2*(2*D)^(s+1)),w d *
        ∑ m ∈ Ioc D K,((m:ℝ)^(s+2))⁻¹*signedFloorCoefficient s d m := by
  let U := 2*(2*D)^(s+1)
  have he (m : ℕ) (hm : m ∈ Ioc D K) :
      (∑ d ∈ Ioc (m^(s+1)) (2*m^(s+1)), w d*centeredQuotient s d m)=
        ∑ d ∈ Icc 1 U, w d*signedFloorCoefficient s d m := by
    have hu : 2*m^(s+1) ≤ U := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ((mem_Ioc.mp hm).2.trans hK) _)
    have hset : (Icc 1 U).filter (fun d => m^(s+1) < d ∧ d ≤ 2*m^(s+1)) =
        Ioc (m^(s+1)) (2*m^(s+1)) := by
      ext d; simp only [mem_filter,mem_Icc,mem_Ioc]; omega
    rw [←hset,sum_filter]
    exact sum_congr rfl fun d _ => by dsimp only [signedFloorCoefficient]; split_ifs <;> simp
  rw [sparseFloorFragment,sum_congr rfl (fun (m : ℕ) hm => congrArg (fun z : ℝ => ((m:ℝ)^(s+2))⁻¹*z) (he m hm))]
  simp only [mul_sum]
  rw [sum_comm]
  exact sum_congr rfl fun d _ => sum_congr rfl fun m _ => by ring

/-- The centered floor term costs a summable power on each octave even
after assigning independent signed weights up to Λ(d) to its divisors. -/
theorem sparse_floor_fragment_uniform (s : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {D K : ℕ}, 1 ≤ D → D ≤ K → K ≤ 2*D →
      ∀ w : ℕ → ℝ, (∀ d, |w d| ≤ ArithmeticFunction.vonMangoldt d) →
      |sparseFloorFragment s D K w| ≤ A*(D:ℝ)^(-(1/4):ℝ) := by
  obtain ⟨C,hC,h⟩ := weighted_conductors_at_divisor s
  let L : ℝ := 2*2^(s+1)
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  refine ⟨14*L*C,by positivity,?_⟩
  intro D K hD hDK hK w hw
  have hDr : 0 < (D:ℝ) := Nat.cast_pos.mpr hD
  let δ := (D:ℝ)^(-(1/4):ℝ)
  have hδ : 0 < δ := Real.rpow_pos_of_pos hDr _
  let U := 2*(2*D)^(s+1)
  let V := C*(δ*D+Real.sqrt D/δ)*((D:ℝ)^(s+2))⁻¹
  have hV : 0 ≤ V := by dsimp only [V]; positivity
  let f (d : ℕ) := ∑ m ∈ Ioc D K,((m:ℝ)^(s+2))⁻¹*signedFloorCoefficient s d m
  have hsum : |sparseFloorFragment s D K w| ≤ (7*(U:ℝ))*V := by
    rw [transpose_floor_fragment _ _ _ hK]
    apply (abs_sum_le_sum_abs _ _).trans
    calc (∑ d ∈ Icc 1 U, |w d*f d|) ≤ ∑ d ∈ Icc 1 U,ArithmeticFunction.vonMangoldt d*V := by
           apply sum_le_sum
           intro d _
           rw [abs_mul]
           exact mul_le_mul (hw _) (h hD hDK hK d δ hδ) (abs_nonneg _) ArithmeticFunction.vonMangoldt_nonneg
         _ ≤ _ := by rw [←sum_mul]; exact mul_le_mul_of_nonneg_right (_root_.RHTower.sum_vonMangoldt_Icc_le_seven U) hV
  have hu : (U:ℝ)=L*(D:ℝ)^(s+1) := by dsimp only [U,L]; push_cast; rw [mul_pow]; ring
  have he : Real.sqrt D/δ=δ*D := by
    change Real.sqrt D/(D:ℝ)^(-(1/4):ℝ)=(D:ℝ)^(-(1/4):ℝ)*D
    calc _ = (D:ℝ)^((1/2:ℝ)-(-(1/4):ℝ)) := by rw [Real.sqrt_eq_rpow,Real.rpow_sub hDr]
         _ = (D:ℝ)^((-(1/4):ℝ)+1) := by norm_num
         _ = _ := by rw [Real.rpow_add hDr,Real.rpow_one]
  apply hsum.trans_eq
  rw [hu]
  dsimp only [V]
  rw [he,show (D:ℝ)^(s+2)=(D:ℝ)^(s+1)*D by rw [pow_succ]]
  change _=14*L*C*δ
  field_simp
  ring

#print axioms sparse_floor_fragment_uniform

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
