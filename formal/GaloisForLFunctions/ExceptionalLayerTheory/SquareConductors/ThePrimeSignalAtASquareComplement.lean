import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.SquareDilationOfThePrimeMesh
import GaloisForLFunctions.ExceptionalLayerTheory.TheInnerWeightOnLargePrimeMultiples

/-!
# The ordinary-prime signal at a single square complement

At a square of a prime above the unit stencil's divisor support, the
inner jump is minus one. Keeping only that complementary factor in the
coprime row therefore recovers a dilated prime error. The coprimality,
first-prime cutoff and moving lower product endpoint cost square-root
precision. At a multiple of the complementary prime the dilation is exact.
-/

noncomputable section
open Finset ArithmeticFunction
open GaloisForLFunctions.CountingHolography.Sections
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- The fibre v=ℓ² in the complete unit-stencil coprime product. -/
def squareComplementRow (ℓ k : ℕ) : ℝ :=
  ∑ p ∈ Icc 1 (k/ℓ^2),
    if p.Prime ∧ 4<p ∧ p.Coprime (ℓ^2) ∧ productLower 1 k<p*ℓ^2 then
      innerJump 1 (ℓ^2)*(vonMangoldt p*centeredPrimeWeight 1 (k/ℓ^2/p)) else 0

private theorem square_jump {ℓ : ℕ} (hℓ : ℓ.Prime) (h₄ : 4<ℓ) : innerJump 1 (ℓ^2) = -1 := by
  rw [sq,innerJump_prime_multiple le_rfl hℓ h₄ hℓ.pos,if_neg hℓ.ne_one,sub_zero,
    innerJump_at_prime le_rfl hℓ h₄]

/-- Restoring all Mangoldt terms costs the small prime mass and the
proper prime-power mass if every prime above T was retained. -/
theorem ordinary_mangoldt_omission_bound {X T : ℕ} (keep : ℕ → Prop) [DecidablePred keep] (w : ℕ → ℝ)
    {F : ℝ} (hF : 0≤F) (hw : ∀ p, |w p|≤F) (hc : ∀ p, p.Prime → T<p → keep p) :
    |(∑ p ∈ Icc 1 X, (if keep p then vonMangoldt p*w p else 0))-
      ∑ p ∈ Icc 1 X, vonMangoldt p*w p| ≤ F*(7*T+(Chebyshev.psi X-Chebyshev.theta X)) := by
  have hsmall : (∑ p ∈ Icc 1 X, (if p≤T then vonMangoldt p else 0)) ≤ 7*T := by
    rw [←sum_filter]
    apply le_trans _ (_root_.RHTower.chebyshevPsi_le_seven T)
    apply sum_le_sum_of_subset_of_nonneg
    · intro p hp
      exact mem_Icc.mpr ⟨(mem_Icc.mp (mem_filter.mp hp).1).1,(mem_filter.mp hp).2⟩
    · exact fun _ _ _ => vonMangoldt_nonneg
  have hproper : (∑ p ∈ Icc 1 X, (if p.Prime then 0 else vonMangoldt p)) =
      Chebyshev.psi X-Chebyshev.theta X := by
    rw [Chebyshev.psi_sub_theta_eq_sum_not_prime,Nat.floor_natCast,sum_filter,
      show Ioc 0 X=Icc 1 X by ext j; simp only [mem_Ioc,mem_Icc]; omega]
    exact sum_congr rfl fun p _ => by by_cases hp : p.Prime <;> simp [hp]
  rw [←sum_sub_distrib]
  apply (abs_sum_le_sum_abs _ _).trans
  calc _ ≤ ∑ p ∈ Icc 1 X, F*((if p≤T then vonMangoldt p else 0)+(if p.Prime then 0 else vonMangoldt p)) := by
          apply sum_le_sum; intro p _
          have hp₀ : 0≤vonMangoldt p := vonMangoldt_nonneg
          by_cases h : keep p
          · rw [if_pos h,sub_self,abs_zero]
            apply mul_nonneg hF
            apply add_nonneg <;> split <;> first | exact hp₀ | exact le_rfl
          · rw [if_neg h,zero_sub,abs_neg,abs_mul,abs_of_nonneg hp₀]
            apply (mul_le_mul_of_nonneg_left (hw p) hp₀).trans
            rw [mul_comm (vonMangoldt p)]
            apply mul_le_mul_of_nonneg_left _ hF
            by_cases hp : p.Prime
            · have hle : p≤T := le_of_not_gt (fun ht => h (hc p hp ht))
              rw [if_pos hp,if_pos hle,add_zero]
            · rw [if_neg hp]
              exact le_add_of_nonneg_left (by split <;> first | exact hp₀ | rfl)
       _ ≤ _ := by
          rw [←mul_sum,sum_add_distrib,hproper]
          exact mul_le_mul_of_nonneg_left (add_le_add hsmall le_rfl) hF

/-- The square fibre recovers the negative prime error at the divided
horizon, including the original moving product cutoff. -/
theorem squareComplementRow_prime_error {ℓ : ℕ} (hℓ : ℓ.Prime) (h₄ : 4<ℓ) :
    ∃ C : ℝ, 0≤C ∧ ∀ k : ℕ, 1≤k →
      |squareComplementRow ℓ k+(Chebyshev.psi (k/ℓ^2:ℕ)-(k/ℓ^2:ℕ))| ≤
        C*(1+Real.log k)^6*Real.sqrt k := by
  obtain ⟨F,hF,hw⟩ := centeredPrimeWeight_uniform
  obtain ⟨P,hP⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  let J : ℕ := 128*(128*1^2+1)
  let A := 420*(1+mass 1)*(5+Real.log J)
  have hmass := (abs_nonneg _).trans (abs_prefix_le_mass (R := 1) le_rfl 0)
  have hJ := Real.log_natCast_nonneg J
  have hA : 0≤A := by dsimp [A]; positivity
  let B := F*(7*((ℓ:ℝ)^2+6)+|P|)
  have hB : 0≤B := by dsimp [B]; positivity
  refine ⟨A+B,add_nonneg hA hB,fun k hk => ?_⟩
  let X := k/ℓ^2
  let T := ℓ^2+4+2*k.sqrt
  let good (p : ℕ) := p.Prime ∧ 4<p ∧ p.Coprime (ℓ^2) ∧ productLower 1 k<p*ℓ^2
  let w (p : ℕ) := centeredPrimeWeight 1 (X/p)
  let S := ∑ p ∈ Icc 1 X, vonMangoldt p*w p
  let H := 1+Real.log k
  have hH : 1≤H := le_add_of_nonneg_right (Real.log_natCast_nonneg k)
  have hk' : (1:ℝ)≤k := by exact_mod_cast hk
  have hs : 1≤Real.sqrt k := Real.one_le_sqrt.mpr hk'
  have hXk : X≤k := Nat.div_le_self ..
  have hY : productLower 1 k≤T := by
    rw [productLower,Real.nat_floor_real_sqrt_eq_nat_sqrt]
    exact (min_le_right ..).trans (by dsimp [T]; omega)
  have hgood (p : ℕ) (hp : p.Prime) (ht : T<p) : good p := by
    have hl : ℓ^2<p := by dsimp [T] at ht; omega
    exact ⟨hp,by dsimp [T] at ht; omega,
      hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (pow_pos hℓ.pos 2) hl),
      (hY.trans_lt ht).trans_le (Nat.le_mul_of_pos_right p (pow_pos hℓ.pos 2))⟩
  have hsgn : squareComplementRow ℓ k = -(∑ p ∈ Icc 1 X, (if good p then vonMangoldt p*w p else 0)) := by
    unfold squareComplementRow
    rw [←sum_neg_distrib]
    apply sum_congr rfl; intro p _
    change (if good p then innerJump 1 (ℓ^2)*(vonMangoldt p*w p) else 0) =
      -(if good p then vonMangoldt p*w p else 0)
    by_cases hp : good p <;> simp only [hp,if_true,if_false,square_jump hℓ h₄,neg_one_mul,neg_zero]
  have hδ := ordinary_mangoldt_omission_bound (X := X) good w hF (fun p => by simpa only [Nat.cast_one,mul_one] using hw (R := 1) le_rfl (X/p)) hgood
  have he : |squareComplementRow ℓ k+S| ≤ B*Real.sqrt k := by
    rw [hsgn,neg_add_eq_sub,abs_sub_comm]
    apply hδ.trans
    have hnat : (k.sqrt:ℝ)≤Real.sqrt k := (Real.le_sqrt (Nat.cast_nonneg _) (Nat.cast_nonneg _)).mpr
      (by exact_mod_cast (show k.sqrt^2≤k by simpa only [sq] using Nat.sqrt_le k))
    have hT : (T:ℝ)≤((ℓ:ℝ)^2+6)*Real.sqrt k := by
      dsimp [T]; push_cast
      linarith only [hnat,hs,le_mul_of_one_le_right (sq_nonneg (ℓ:ℝ)) hs]
    have hp := (hP X).trans (mul_le_mul (le_abs_self P) (Real.sqrt_le_sqrt (by exact_mod_cast hXk))
      (Real.sqrt_nonneg _) (abs_nonneg _))
    apply (mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left hT (by norm_num : (0:ℝ)≤7)) hp) hF).trans_eq
    dsimp [B]; ring
  have hf : |(Chebyshev.psi X-X)-S| ≤ A*H := by
    rcases Nat.eq_zero_or_pos X with hX | hX
    · simp only [S,hX,Chebyshev.psi_zero,Nat.cast_zero,sub_zero,Icc_eq_empty_of_lt Nat.zero_lt_one,
        sum_empty,abs_zero]
      exact mul_nonneg hA (zero_le_one.trans hH)
    · apply (centeredPrimeWeight_factorial (R := 1) le_rfl hX).trans
      have hl := Real.log_le_log (by exact_mod_cast hX : (0:ℝ)<X) (by exact_mod_cast hXk : (X:ℝ)≤k)
      change 420*(1+mass 1)*(3+Real.log J+2*Real.log X) ≤ _
      have hh := le_mul_of_one_le_right (add_nonneg (by norm_num : (0:ℝ)≤3) hJ) hH
      have hscale : 3+Real.log J+2*Real.log X≤(5+Real.log J)*H := by
        dsimp only [H] at hh ⊢
        linarith only [hh,hl,Real.log_natCast_nonneg k]
      exact (mul_le_mul_of_nonneg_left hscale (by positivity : 0≤420*(1+mass 1))).trans_eq
        (by dsimp only [A]; ring)
  have h₁ : H≤H^6*Real.sqrt k := (le_self_pow₀ hH (by decide : 6≠0)).trans
    (le_mul_of_one_le_right (by positivity) hs)
  have h₂ : Real.sqrt k≤H^6*Real.sqrt k :=
    le_mul_of_one_le_left (Real.sqrt_nonneg _) (one_le_pow₀ hH)
  have hid : squareComplementRow ℓ k+(Chebyshev.psi X-X) =
      ((Chebyshev.psi X-X)-S)+(squareComplementRow ℓ k+S) := by ring
  change |squareComplementRow ℓ k+(Chebyshev.psi X-X)| ≤ (A+B)*H^6*Real.sqrt k
  rw [hid]
  apply (abs_add_le _ _).trans ((add_le_add hf he).trans _)
  linarith only [mul_le_mul_of_nonneg_left h₁ hA,mul_le_mul_of_nonneg_left h₂ hB]

/-- Every fixed prime-square complement above the divisor support carries
the negative of the full ordinary-prime signal at the divided conductor,
up to six logarithms. -/
theorem squareComplementRow_dyadicPrimeContact {ℓ : ℕ} (hℓ : ℓ.Prime) (h₄ : 4<ℓ) :
    ∃ C : ℝ, 0≤C ∧ ∀ {m : ℕ}, 0<m →
      |(ℓ:ℝ)*splineCountReading (ℓ*m) (squareComplementRow ℓ)+dyadicPrimeContact m| ≤
        C*((1+Real.log (splineHorizon (ℓ*m)))^6+(1+Real.log (splineHorizon m))^6) := by
  let E (j : ℕ) := Chebyshev.psi j-j
  have hE₀ : E 0=0 := by simp [E,Chebyshev.psi_zero]
  have hE : ∃ C : ℝ, 0≤C ∧ ∀ k : ℕ, 1≤k →
      |(Chebyshev.theta k-k)-E k| ≤ C*(1+Real.log k)^6*Real.sqrt k := by
    obtain ⟨P,hP⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
    refine ⟨|P|,abs_nonneg _,fun k _ => ?_⟩
    rw [show (Chebyshev.theta k-k)-E k = -(Chebyshev.psi k-Chebyshev.theta k) by dsimp [E]; ring,
      abs_neg,abs_of_nonneg (sub_nonneg.mpr (Chebyshev.theta_le_psi _))]
    have hh : 1≤(1+Real.log (k:ℝ))^6 := one_le_pow₀ (le_add_of_nonneg_right (Real.log_natCast_nonneg _))
    exact (hP k).trans (mul_le_mul_of_nonneg_right ((le_abs_self P).trans
      (le_mul_of_one_le_right (abs_nonneg _) hh)) (Real.sqrt_nonneg _))
  obtain ⟨A,hA,ha⟩ := dyadicPrimeContact_of_count_approximation E hE
  let Z (k : ℕ) := squareComplementRow ℓ k+E (k/ℓ^2)
  obtain ⟨B,hB,hb⟩ := splineCountReading_sqrt_error Z (squareComplementRow_prime_error hℓ h₄)
  have hl : (0:ℝ)<ℓ := Nat.cast_pos.mpr hℓ.pos
  refine ⟨ℓ*B+A,by positivity,fun {m} hm => ?_⟩
  have hid : splineCountReading (ℓ*m) Z =
      splineCountReading (ℓ*m) (squareComplementRow ℓ)+splineCountReading m E/ℓ := by
    rw [←splineCountReading_square_dilation hm hℓ.pos E hE₀]
    simp only [splineCountReading,Z,add_mul,sum_add_distrib]
  have he : (ℓ:ℝ)*splineCountReading (ℓ*m) (squareComplementRow ℓ)+dyadicPrimeContact m =
      ℓ*splineCountReading (ℓ*m) Z+(dyadicPrimeContact m-splineCountReading m E) := by
    rw [hid]; field_simp <;> ring
  rw [he]
  apply (abs_add_le _ _).trans
  rw [abs_mul,abs_of_pos hl]
  let H := (1+Real.log (splineHorizon (ℓ*m)))^6
  let G := (1+Real.log (splineHorizon m))^6
  have hH : 0≤H := by dsimp [H]; positivity
  have hG : 0≤G := by dsimp [G]; positivity
  apply (add_le_add (mul_le_mul_of_nonneg_left (hb (Nat.mul_pos hℓ.pos hm)) hl.le) (ha hm)).trans
  change (ℓ:ℝ)*(B*H)+A*G ≤ (ℓ*B+A)*(H+G)
  linarith only [mul_nonneg (mul_nonneg hl.le hB) hG,mul_nonneg hA hH]

#print axioms squareComplementRow_prime_error
#print axioms squareComplementRow_dyadicPrimeContact
end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
