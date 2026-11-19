import GaloisForLFunctions.PrimeExponentialSums.ReciprocalVaughanOnPowerRanges
import GaloisForLFunctions.RHTower.VonMangoldtLogSummatory
import GaloisForLFunctions.GreenCalculusOfThePrimeFreeWindow.TheFloorGraphNormAndTopOctaveBlindnessOfWindowGluing

/-!
# Reciprocal phases over ordinary primes

The logarithmic Vaughan phase T log(1+r/n) tends to S/n when r decreases
to zero with Tr=S. Its complete block estimate survives the limit. Asymmetric
cutoffs give a fixed power saving when S is close to the square of the block scale.
-/

noncomputable section

open Filter Finset ArithmeticFunction RHTower RHTower.Sieve Topology

namespace GaloisForLFunctions.PrimeExponentialSums

/-- Reciprocal phase with frequency S in radians. -/
def reciprocalPhase (S : ℝ) (n : ℕ) : ℂ := Complex.exp (((S/(n : ℝ) : ℝ) : ℂ)*Complex.I)

private theorem norm_reciprocalPhase (S : ℝ) (n : ℕ) : ‖reciprocalPhase S n‖ = 1 := by
  simp [reciprocalPhase,Complex.norm_exp]

/-- At large block scale the five terms of the envelope all save a power. -/
private theorem large_block {D S : ℝ} {A B : ℕ} (hD : 0 < D) (hA : 1 ≤ A)
    (hAB : A ≤ B) (hB : B ≤ 2*A)
    (hbig : (10 : ℝ)^27 ≤ (A : ℝ)^(1/1000 : ℝ))
    (hl : (A : ℝ)^(199/100 : ℝ) ≤ S) (hu : S ≤ (A : ℝ)^(201/100 : ℝ)) :
    ∃ U V : ℕ, 1 ≤ U ∧ 1 ≤ V ∧ U < A ∧ U*V ≤ A ∧
      S*((U*V : ℕ) : ℝ)^3 ≤ 72*Real.pi*(A : ℝ)^4 ∧ (10 : ℝ)^27*A ≤ S ∧
      kubalalikaBlockPower D S 1 A B U V ≤
        80*D*(1+Real.log A)^4*(A : ℝ)^(49/50 : ℝ) := by
  let p (b : ℝ) := (A : ℝ)^b
  have ha : (1 : ℝ) ≤ A := by exact_mod_cast hA
  have ha0 : (0 : ℝ) < A := zero_lt_one.trans_le ha
  have pos (b : ℝ) : 0 < p b := Real.rpow_pos_of_pos ha0 _
  have mono {a b : ℝ} (h : a ≤ b) : p a ≤ p b := Real.rpow_le_rpow_of_exponent_le ha h
  have mul (a b : ℝ) : p a*p b = p (a+b) := (Real.rpow_add ha0 a b).symm
  have powr (a b : ℝ) : (p a)^b = p (a*b) := (Real.rpow_mul ha0.le a b).symm
  have one : p 1 = A := Real.rpow_one _
  have up {z a b : ℝ} (hz : 0 ≤ z) (h : z ≤ p a) (hb : 0 ≤ b) : z^b ≤ p (a*b) := by
    rw [← powr]; exact Real.rpow_le_rpow hz h hb
  have down {z a b : ℝ} (h : p a ≤ z) (hb : b ≤ 0) : z^b ≤ p (a*b) := by
    rw [← powr]; exact Real.rpow_le_rpow_of_nonpos (pos _) h hb
  have htwo : 2 < p (1/1000) := lt_of_lt_of_le (by norm_num : (2 : ℝ)<10^27) hbig
  have twice (a : ℝ) : 2*p a < p (a+1/1000) := by
    rw [add_comm, ← mul]; exact mul_lt_mul_of_pos_right htwo (pos _)
  let U := ⌈p (11/20)⌉₊
  let V := ⌈p (1/20)⌉₊
  have lower (a : ℝ) : p a ≤ (⌈p a⌉₊ : ℝ) := Nat.le_ceil _
  have upper (a : ℝ) (ha' : 0 ≤ a) : (⌈p a⌉₊ : ℝ) < p (a+1/1000) := by
    have h₁ : (⌈p a⌉₊ : ℝ) < p a+1 := Nat.ceil_lt_add_one (pos _).le
    have h₂ : 1 ≤ p a := Real.one_le_rpow ha ha'
    exact h₁.trans_le ((by linarith only [h₂] : p a + 1 ≤ 2*p a).trans (twice a).le)
  have hU : (U : ℝ) < p (11/20+1/1000) := upper _ (by norm_num)
  have hV : (V : ℝ) ≤ p (1/20+1/1000) := (upper _ (by norm_num)).le
  have huv : ((U*V : ℕ) : ℝ) ≤ p (602/1000) := by
    rw [Nat.cast_mul, show (602/1000 : ℝ) = (11/20+1/1000)+(1/20+1/1000) by norm_num, ← mul]
    exact mul_le_mul hU.le hV (by positivity) (pos _).le
  have hBR : (B : ℝ) ≤ p (1+1/1000) := by
    have hbr : (B : ℝ) ≤ 2*(A : ℝ) := by exact_mod_cast hB
    exact hbr.trans (by simpa only [one] using (twice 1).le)
  have hS := (pos _).trans_le hl
  refine ⟨U,V,(Nat.one_le_ceil_iff).mpr (pos _),(Nat.one_le_ceil_iff).mpr (pos _),?_,?_,?_,?_,?_⟩
  · exact_mod_cast hU.trans_le ((mono (by norm_num : (11/20+1/1000 : ℝ) ≤ 1)).trans_eq one)
  · exact_mod_cast huv.trans ((mono (by norm_num : (602/1000 : ℝ) ≤ 1)).trans_eq one)
  · have hb3 : (((U*V : ℕ) : ℝ))^3 ≤ p (602/1000*3) := by
      rw [← Real.rpow_natCast _ 3]
      simpa only [Nat.cast_ofNat] using
        up (Nat.cast_nonneg (α := ℝ) (U*V)) huv (by norm_num : (0 : ℝ) ≤ 3)
    have hfour : p 4 = (A : ℝ)^4 := by dsimp [p]; norm_num
    calc
      _ ≤ p (201/100)*p (602/1000*3) := mul_le_mul hu hb3 (by positivity) (pos _).le
      _ ≤ p 4 := by rw [mul]; exact mono (by norm_num)
      _ ≤ _ := by rw [hfour]; exact le_mul_of_one_le_left (by positivity) (by linarith only [Real.pi_gt_three])
  · calc
      _ ≤ p (1/1000) * p 1 := by rw [one]; exact mul_le_mul_of_nonneg_right hbig ha0.le
      _ ≤ p (199/100) := by rw [mul]; exact mono (by norm_num)
      _ ≤ S := hl
  · have h₁ : p (1/3)*S^(1/6 : ℝ)*Real.sqrt (U*V : ℕ) ≤ p (49/50) := by
      rw [Real.sqrt_eq_rpow]
      calc
        _ ≤ p (1/3)*p (201/100*(1/6))*p (602/1000*(1/2)) := by
          apply mul_le_mul
          · exact mul_le_mul_of_nonneg_left (up hS.le hu (by norm_num)) (pos _).le
          · exact up (by positivity) huv (by norm_num)
          · positivity
          · exact mul_nonneg (pos _).le (pos _).le
        _ ≤ _ := by rw [mul,mul]; exact mono (by norm_num)
    have h₂ : (B : ℝ)^(3/2 : ℝ)*S^(-(1/2 : ℝ)) ≤ p (49/50) := by
      calc
        _ ≤ p ((1+1/1000)*(3/2))*p (199/100*(-(1/2))) :=
          mul_le_mul (up (by positivity) hBR (by norm_num)) (down hl (by norm_num))
            (Real.rpow_nonneg hS.le _) (pos _).le
        _ ≤ _ := by rw [mul]; exact mono (by norm_num)
    have hvneg : (V : ℝ)^(-(1/2 : ℝ)) ≤ p (1/20*(-(1/2))) := down (lower _) (by norm_num)
    have huneg : (U : ℝ)^(-(1/2 : ℝ)) ≤ p (11/20*(-(1/2))) := down (lower _) (by norm_num)
    have h₃ : (B : ℝ)*(V : ℝ)^(-(1/2 : ℝ)) ≤ p (49/50) := by
      apply (mul_le_mul hBR hvneg (by positivity) (pos _).le).trans
      rw [mul]; exact mono (by norm_num)
    have h₄ : S^(1/4 : ℝ)*(B : ℝ)^(3/4 : ℝ)*(U : ℝ)^(-(1/2 : ℝ)) ≤ p (49/50) := by
      have hsb := mul_le_mul (up hS.le hu (by norm_num : (0 : ℝ) ≤ 1/4))
        (up (Nat.cast_nonneg B) hBR (by norm_num : (0 : ℝ) ≤ 3/4)) (by positivity) (pos _).le
      apply (mul_le_mul hsb huneg (by positivity) (mul_nonneg (pos _).le (pos _).le)).trans
      rw [mul,mul]; exact mono (by norm_num)
    have h₅ : (B : ℝ)*(U : ℝ)^(-(1/2 : ℝ)) ≤ p (49/50) := by
      apply (mul_le_mul hBR huneg (by positivity) (pos _).le).trans
      rw [mul]; exact mono (by norm_num)
    have hlogA := Real.log_natCast_nonneg A
    have h2B : Real.log B ≤ Real.log 2 + Real.log A := by
      rw [← Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) ha0.ne']
      exact Real.log_le_log (by exact_mod_cast (hA.trans hAB) : (0 : ℝ) < B) (by exact_mod_cast hB)
    have hlog : (1+Real.log B)^4 ≤ (2*(1+Real.log A))^4 := by
      apply pow_le_pow_left₀ (by have := Real.log_natCast_nonneg B; positivity)
      have hh := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
      linarith only [hh,h2B,hlogA]
    simp only [kubalalikaBlockPower,mul_one]
    have hs : p (1/3)*S^(1/6 : ℝ)*Real.sqrt (U*V : ℕ) +
        (B : ℝ)^(3/2 : ℝ)*S^(-(1/2 : ℝ)) + (B : ℝ)*(V : ℝ)^(-(1/2 : ℝ)) +
        S^(1/4 : ℝ)*(B : ℝ)^(3/4 : ℝ)*(U : ℝ)^(-(1/2 : ℝ)) +
        (B : ℝ)*(U : ℝ)^(-(1/2 : ℝ)) ≤ 5*p (49/50) := by
      linarith only [h₁,h₂,h₃,h₄,h₅]
    calc
      _ ≤ (D*(2*(1+Real.log A))^4)*(5*p (49/50)) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hlog hD.le)
        · simpa only [Nat.cast_mul] using hs
        · positivity
        · positivity
      _ = _ := by dsimp [p]; ring

private theorem abs_mangoldt_block (S : ℝ) {A B : ℕ} (hA : 1 ≤ A) :
    ‖∑ n ∈ Ico A B, (vonMangoldt n : ℂ)*reciprocalPhase S n‖ ≤ 7*B := by
  calc
    _ ≤ ∑ n ∈ Ico A B, vonMangoldt n := by
      refine (norm_sum_le _ _).trans (sum_le_sum fun n _ => ?_)
      simp [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg vonMangoldt_nonneg,norm_reciprocalPhase]
    _ ≤ ∑ n ∈ Icc 1 B, vonMangoldt n := by
      apply sum_le_sum_of_subset_of_nonneg
      · exact fun n hn => mem_Icc.mpr ⟨hA.trans (mem_Ico.mp hn).1,(mem_Ico.mp hn).2.le⟩
      · exact fun _ _ _ => vonMangoldt_nonneg
    _ ≤ _ := chebyshevPsi_le_seven B

/-- Reciprocal oscillation saves a fixed power in every sharp subinterval
of a dyadic block, uniformly over frequencies near its squared length. -/
theorem reciprocal_mangoldt_block :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (A B : ℕ) (S : ℝ), 1 ≤ A → A ≤ B → B ≤ 2*A →
      (A : ℝ)^(199/100 : ℝ) ≤ S → S ≤ (A : ℝ)^(201/100 : ℝ) →
      ‖∑ n ∈ Ico A B, (vonMangoldt n : ℂ)*reciprocalPhase S n‖ ≤ C*(A : ℝ)^(99/100 : ℝ) := by
  obtain ⟨D,hD,henv⟩ := reciprocal_vaughan_envelope
  have hb : ∀ᶠ x : ℝ in atTop, (10 : ℝ)^27 ≤ x^(1/1000 : ℝ) := by
    simpa only [pow_zero,mul_one] using (eventually_const_mul_one_add_log_pow_le_rpow
      (by norm_num : (0 : ℝ) < 1/1000) (show (0 : ℝ) < 10^27 by norm_num) 0)
  have hl := eventually_const_mul_one_add_log_pow_le_rpow (by norm_num : (0 : ℝ)<1/100)
    (show 0 < 80*D by positivity) 4
  obtain ⟨Y,hY⟩ := eventually_atTop.mp (hb.and hl)
  let C := 1+14*|Y|
  have hC : 1 ≤ C := by dsimp [C]; linarith only [abs_nonneg Y]
  refine ⟨C,zero_le_one.trans hC,fun A B S hA hAB hB hLo hHi => ?_⟩
  have ha : (1 : ℝ) ≤ A := by exact_mod_cast hA
  by_cases hAY : Y ≤ A
  · obtain ⟨hbig,hlog⟩ := hY _ hAY
    obtain ⟨U,V,hU,hV,hu,huv,hs,ht,hp⟩ := large_block hD hA hAB hB hbig hLo hHi
    have hS : 0 < S := (Real.rpow_pos_of_pos (zero_lt_one.trans_le ha) _).trans_le hLo
    apply (henv hS hA hAB hB hU hV hu huv hs ht).trans (hp.trans ?_)
    calc
      _ ≤ (A : ℝ)^(1/100 : ℝ)*(A : ℝ)^(49/50 : ℝ) :=
        mul_le_mul_of_nonneg_right hlog (by positivity)
      _ = (A : ℝ)^(99/100 : ℝ) := by
        rw [← Real.rpow_add (zero_lt_one.trans_le ha)]; norm_num
      _ ≤ _ := le_mul_of_one_le_left (by positivity) hC
  · apply (abs_mangoldt_block S hA).trans
    have habs := le_abs_self Y
    have hbr : (B : ℝ) ≤ 2*(A : ℝ) := by exact_mod_cast hB
    have hrad := Real.one_le_rpow ha (by norm_num : (0 : ℝ) ≤ 99/100)
    exact (show (7 : ℝ)*B ≤ C by dsimp [C]; linarith only [not_le.mp hAY,habs,hbr]).trans
      (le_mul_of_one_le_right (zero_le_one.trans hC) hrad)

/-- Power saving for the actual ordinary primes in the reciprocal phases
of a sharp block, with uniform endpoints and frequency. -/
theorem reciprocal_ordinary_prime_block :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (A B : ℕ) (S : ℝ), 1 ≤ A → A ≤ B → B ≤ 2*A →
      (A : ℝ)^(199/100 : ℝ) ≤ S → S ≤ (A : ℝ)^(201/100 : ℝ) →
      ‖∑ n ∈ Ico A B with n.Prime, (Real.log n : ℂ)*reciprocalPhase S n‖ ≤ C*(A : ℝ)^(99/100 : ℝ) := by
  obtain ⟨C,hC,h⟩ := reciprocal_mangoldt_block
  let K := 3*(Real.log 4+4)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨C+2*K,by positivity,fun A B S hA hAB hB hLo hHi => ?_⟩
  let I := Ico A B
  let f (n : ℕ) := (vonMangoldt n : ℂ)*reciprocalPhase S n
  have hsplit := sum_filter_add_sum_filter_not I Nat.Prime f
  have hmass : (∑ n ∈ I.filter (fun n => ¬n.Prime), vonMangoldt n) ≤ K*Real.sqrt B := by
    have hsub : I.filter (fun n => ¬n.Prime) ⊆ (Ioc 0 B).filter (fun n => ¬n.Prime) := by
      intro n hn
      obtain ⟨hm,hp⟩ := mem_filter.mp hn
      obtain ⟨ha,hu⟩ := mem_Ico.mp hm
      exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨hA.trans ha,hu.le⟩,hp⟩
    have hψ := GreenCalculusOfThePrimeFreeWindow.psi_sub_theta_le_three_mul_sqrt (B : ℝ)
    rw [Chebyshev.psi_sub_theta_eq_sum_not_prime,Nat.floor_natCast] at hψ
    exact (sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => vonMangoldt_nonneg)).trans hψ
  have htail : ‖∑ n ∈ I.filter (fun n => ¬n.Prime), f n‖ ≤ K*Real.sqrt B := by
    apply (norm_sum_le _ _).trans
    apply le_trans _ hmass
    apply sum_le_sum
    intro n _
    simp [f, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg vonMangoldt_nonneg,norm_reciprocalPhase]
  have he : (∑ n ∈ I with n.Prime, (Real.log n : ℂ)*reciprocalPhase S n) =
      (∑ n ∈ I, f n) - ∑ n ∈ I.filter (fun n => ¬n.Prime), f n := by
    rw [← hsplit, add_sub_cancel_right]
    exact sum_congr rfl fun n hn => by simp only [f,vonMangoldt_apply_prime (mem_filter.mp hn).2]
  have hsq : Real.sqrt B ≤ 2*(A : ℝ)^(99/100 : ℝ) := by
    have h₁ : Real.sqrt B ≤ Real.sqrt (4*(A : ℝ)) :=
      Real.sqrt_le_sqrt (by exact_mod_cast (show B ≤ 4*A by omega))
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4),show Real.sqrt 4 = 2 by norm_num] at h₁
    simp only [Real.sqrt_eq_rpow] at h₁ ⊢
    exact h₁.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast hA : (1 : ℝ) ≤ A) (by norm_num : (1/2 : ℝ) ≤ 99/100)) (by norm_num))
  rw [he]
  apply (norm_sub_le _ _).trans
  exact (add_le_add (h A B S hA hAB hB hLo hHi)
    (htail.trans (mul_le_mul_of_nonneg_left hsq hK))).trans_eq (by ring)

#print axioms reciprocal_ordinary_prime_block

end GaloisForLFunctions.PrimeExponentialSums
