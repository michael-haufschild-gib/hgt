import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheIntegralOnTheRescaledProductShell
import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheCenteredMangoldtTailOfTheProduct
import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheQuotientCellsOfTheCappedSpline

/-!
# The ordinary prime error below a quadratic product cut

On a single conductor a subquadratic band lies before the first spline
sample. Its remaining mesh, paired with the centered Mangoldt measure,
obeys the ordinary prime-error exponent at the upper product cutoff.
-/

noncomputable section
open Finset Filter ArithmeticFunction
open GaloisForLFunctions.CountingHolography.Sections
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- Uniform two-cut transfer back to the original capped coprime product. -/
theorem shell_centering_transfer :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (V U : ℕ → ℕ) (N M : ℕ),
      |(∑ n ∈ Ioc N M, (n:ℝ)^2*(cappedUpperProductReading (V n) n n -
          cappedUpperProductReading (U n) n n)) -
        ∑ n ∈ Ioc N M, (n:ℝ)^2*(centeredProductReading (V n) n -
          centeredProductReading (U n) n)| ≤ C*(M:ℝ)^3*conductorLog M := by
  obtain ⟨K,hK,h⟩ := partial_prefix_centered_product_transfer
  refine ⟨K+K,add_nonneg hK hK,fun V U N M => ?_⟩
  let E (D : ℕ → ℕ) := ∑ n ∈ Ioc N M, (n:ℝ)^2*(centeredProductReading (D n) n -
    cappedUpperProductReading (D n) n n)
  have he : (∑ n ∈ Ioc N M, (n:ℝ)^2*(cappedUpperProductReading (V n) n n -
        cappedUpperProductReading (U n) n n)) -
        ∑ n ∈ Ioc N M, (n:ℝ)^2*(centeredProductReading (V n) n -
          centeredProductReading (U n) n) = E U - E V := by
    simp only [E,←sum_sub_distrib]
    exact sum_congr rfl fun _ _ => by ring
  rw [he]
  exact (abs_sub _ _).trans ((add_le_add (h U N M) (h V N M)).trans_eq (by ring))

/-- Late subquadratic cuts lie before spline support, while the coprime
cofactor cap already lies below the lower product cut. -/
theorem subquadratic_cut_geometry {α β c : ℝ} (hα : 1 < α) (hαβ : α ≤ β) (hβ : β < 2)
    (hc : 1 ≤ c) (hc' : c ≤ 2) :
    ∀ᶠ n : ℕ in atTop,
      let V := ⌊(n:ℝ)^α⌋₊
      let U := ⌊c*(n:ℝ)^β⌋₊
      V ≤ U ∧ U ≤ splineHorizon n ∧ productLower 1 (splineHorizon n) ≤ V ∧
        (U:ℝ)+1 < Real.exp (-8)*(n:ℝ)^2 := by
  obtain ⟨A,hA,hwin⟩ := successorSquare_window_bound
  have hg : Tendsto (fun n : ℕ => (n:ℝ)^(2-β)) atTop atTop :=
    (tendsto_rpow_atTop (sub_pos.mpr hβ)).comp tendsto_natCast_atTop_atTop
  have hd : Tendsto (fun n : ℕ => (n:ℝ)^(α-1)) atTop atTop :=
    (tendsto_rpow_atTop (sub_pos.mpr hα)).comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop (1:ℕ),hg.eventually_ge_atTop (4*Real.exp 8),
    hd.eventually_ge_atTop (2*A)] with n hn hgap hcap
  let X := (n:ℝ)^β
  let U := ⌊c*X⌋₊
  have hn1 : 1 ≤ (n:ℝ) := by exact_mod_cast hn
  have hn0 := zero_lt_one.trans_le hn1
  have hX1 : 1 ≤ X := Real.one_le_rpow hn1 ((zero_lt_one.trans hα).le.trans hαβ)
  have hX := zero_lt_one.trans_le hX1
  have hU : (U:ℝ) ≤ 2*X := (Nat.floor_le (mul_nonneg (zero_le_one.trans hc) hX.le)).trans
    (mul_le_mul_of_nonneg_right hc' hX.le)
  have hpow : X*(n:ℝ)^(2-β) = (n:ℝ)^2 := by
    dsimp only [X]; rw [←Real.rpow_add hn0,show β+(2-β)=2 by ring,Real.rpow_two]
  have hx4 : 4 ≤ Real.exp (-8)*(n:ℝ)^(2-β) := by
    rw [Real.exp_neg,inv_mul_eq_div,le_div_iff₀ (Real.exp_pos 8)]
    exact hgap
  have hbefore : (U:ℝ)+1 < Real.exp (-8)*(n:ℝ)^2 := by
    have hh := mul_le_mul_of_nonneg_left hx4 hX.le
    rw [mul_left_comm X,hpow] at hh
    linarith only [hX1,hU,hh]
  have hscale := successorSquareWindowScale_bounds n
  have hL : (n:ℝ)^2 ≤ (splineHorizon n:ℝ) := by
    dsimp only [splineHorizon]
    push_cast
    linarith only [hscale.1,hscale.2.2,Nat.cast_nonneg (α := ℝ) (windowEnd ((2*n+1)^2+1))]
  have huL : (U:ℝ) ≤ splineHorizon n := by
    have hh := mul_le_mul_of_nonneg_right (Real.exp_le_one_iff.mpr (by norm_num : (-8:ℝ) ≤ 0))
      (sq_nonneg (n:ℝ))
    linarith only [hbefore,hL,hh]
  refine ⟨Nat.floor_mono ((Real.rpow_le_rpow_of_exponent_le hn1 hαβ).trans
    (le_mul_of_one_le_left hX.le hc)),Nat.cast_le.mp huL,?_,hbefore⟩
  apply Nat.le_floor
  have hr := Real.sqrt_le_sqrt (hwin hn)
  rw [Real.sqrt_sq (mul_nonneg (zero_le_one.trans hA) hn0.le)] at hr
  have hpl : (productLower 1 (splineHorizon n):ℝ) ≤ 2*Real.sqrt (splineHorizon n) := by
    refine (Nat.cast_le.mpr (min_le_right _ _)).trans ?_
    push_cast
    exact mul_le_mul_of_nonneg_left (Nat.floor_le (Real.sqrt_nonneg _)) (by norm_num)
  have he : (n:ℝ)^(α-1)*n=(n:ℝ)^α := by
    calc _ = (n:ℝ)^(α-1)*(n:ℝ)^(1:ℝ) := by rw [Real.rpow_one]
         _ = _ := by rw [←Real.rpow_add hn0,sub_add_cancel]
  rw [←he]
  linarith only [hpl,hr,mul_le_mul_of_nonneg_right hcap hn0.le]

/-- The signed change between two subquadratic power cuts on one conductor.
The final prime-error sample is taken at the actual upper product. -/
theorem subquadratic_centered_band {α β γ : ℝ} (hα : 1 < α) (hab : α ≤ β)
    (hβ : β < 2) (hγ : _root_.RHTower.zeroReSup < γ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 0 < n →
      |(n:ℝ)^2*(centeredProductReading ⌊(n:ℝ)^α⌋₊ n-centeredProductReading ⌊(n:ℝ)^β⌋₊ n)| ≤
        C*(n:ℝ)^(1+β*γ) := by
  obtain ⟨C,hC,h⟩ := quotientMeshProfile_prime_interval hγ
  have hγ' : 0 < γ := (by norm_num : (0:ℝ)<1/2).trans_le (_root_.RHTower.half_le_zeroReSup.trans hγ.le)
  have hβ' := (zero_lt_one.trans hα).trans_le hab
  have geo := subquadratic_cut_geometry (c := 1) hα hab hβ le_rfl (by norm_num)
  simp only [one_mul] at geo
  obtain ⟨k,hk⟩ := eventually_atTop.mp geo
  let row (n : ℕ) := (n:ℝ)^2*(centeredProductReading ⌊(n:ℝ)^α⌋₊ n-centeredProductReading ⌊(n:ℝ)^β⌋₊ n)
  let D := ∑ j ∈ range k, |row j|
  have hD : 0 ≤ D := sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨C+D,add_nonneg hC hD,fun n hn => ?_⟩
  have hn' : (0:ℝ) < n := Nat.cast_pos.mpr hn
  by_cases hkn : k ≤ n
  · let V := ⌊(n:ℝ)^α⌋₊
    let U := ⌊(n:ℝ)^β⌋₊
    let b := splineHorizon n+1
    let a (q : ℕ) := vonMangoldt q-1
    obtain ⟨hVU,hUL,hY,hbefore⟩ := hk n hkn
    have hs := detached_signed_product_shell hn hVU hUL hY hbefore a
    change centeredProductReading V n - centeredProductReading U n = _ at hs
    have he : row n = n*∑ q ∈ Ioc V U, a q*quotientMeshProfile b (q*(1/(n:ℝ)^2)) := by
      change (n:ℝ)^2*(centeredProductReading V n-centeredProductReading U n) = _
      rw [hs,mul_sum,mul_sum]
      apply sum_congr rfl
      intro q hq
      have hq' := (Nat.zero_le V).trans_lt (mem_Ioc.mp hq).1
      have hb : splineHorizon n < q*b := (Nat.lt_succ_self _).trans_le (Nat.le_mul_of_pos_left b hq')
      rw [←div_eq_mul_one_div,←mul_assoc,mul_comm (n:ℝ) (a q),mul_assoc,
        ←unitHorizonPair_real_profile hn hq' hb]
      ring
    change |row n| ≤ _
    rw [he,abs_mul,abs_of_pos hn']
    have hc := mul_le_mul_of_nonneg_left (h b V U (one_div_pos.mpr (sq_pos_of_pos hn')) hVU) hn'.le
    apply hc.trans
    have hp := Real.rpow_le_rpow (Nat.cast_nonneg U) (Nat.floor_le (Real.rpow_nonneg hn'.le β)) hγ'.le
    rw [←Real.rpow_mul hn'.le] at hp
    have he' := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hp hC) hn'.le
    apply he'.trans
    rw [Real.rpow_add hn',Real.rpow_one]
    exact (le_of_eq (by ring)).trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hD)
      (mul_nonneg hn'.le (Real.rpow_nonneg hn'.le _)))
  · have h₁ : (1:ℝ) ≤ n := by exact_mod_cast hn
    have hp : 1 ≤ (n:ℝ)^(1+β*γ) := Real.one_le_rpow h₁ (by positivity)
    have he : |row n| ≤ D := single_le_sum (fun j _ => abs_nonneg (row j)) (mem_range.mpr (lt_of_not_ge hkn))
    exact he.trans ((le_add_of_nonneg_left hC).trans (le_mul_of_one_le_right (add_nonneg hC hD) hp))

/-- The original capped, coprime band on every conductor fragment. The
cubic log pays for arithmetic centering at both moving cuts. The remaining
signed prime term has exponent 2+βγ for every γ above the zero abscissa. -/
theorem subquadratic_capped_band {α β γ : ℝ} (hα : 1 < α) (hab : α ≤ β)
    (hβ : β < 2) (hγ : _root_.RHTower.zeroReSup < γ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ J M : ℕ, 0 < M →
      |∑ n ∈ Ioc J M, (n:ℝ)^2*(cappedUpperProductReading ⌊(n:ℝ)^α⌋₊ n n -
        cappedUpperProductReading ⌊(n:ℝ)^β⌋₊ n n)| ≤
        C*((M:ℝ)^3*conductorLog M+(M:ℝ)^(2+β*γ)) := by
  obtain ⟨A,hA,ha⟩ := subquadratic_centered_band hα hab hβ hγ
  obtain ⟨B,hB,hb⟩ := shell_centering_transfer
  let V (n : ℕ) := ⌊(n:ℝ)^α⌋₊
  let U (n : ℕ) := ⌊(n:ℝ)^β⌋₊
  let S (n : ℕ) := (n:ℝ)^2*(cappedUpperProductReading (V n) n n-cappedUpperProductReading (U n) n n)
  let E (n : ℕ) := (n:ℝ)^2*(centeredProductReading (V n) n-centeredProductReading (U n) n)
  have hγ' : 0 < γ := (by norm_num : (0:ℝ)<1/2).trans_le (_root_.RHTower.half_le_zeroReSup.trans hγ.le)
  have hβ' := (zero_lt_one.trans hα).trans_le hab
  refine ⟨A+B,add_nonneg hA hB,fun J M hM => ?_⟩
  have hM' : (0:ℝ) < M := Nat.cast_pos.mpr hM
  let X := (M:ℝ)^(1+β*γ)
  have hX : 0 ≤ X := Real.rpow_nonneg hM'.le _
  have hsum : |∑ n ∈ Ioc J M, E n| ≤ A*(M:ℝ)^(2+β*γ) := by
    apply (abs_sum_le_sum_abs _ _).trans
    calc _ ≤ ∑ _n ∈ Ioc J M, A*X := by
              apply sum_le_sum
              intro n hn
              exact (ha n ((Nat.zero_le J).trans_lt (mem_Ioc.mp hn).1)).trans (mul_le_mul_of_nonneg_left
                (Real.rpow_le_rpow (Nat.cast_nonneg n) (Nat.cast_le.mpr (mem_Ioc.mp hn).2) (by positivity)) hA)
         _ ≤ M*(A*X) := by
              rw [sum_const,Nat.card_Ioc,nsmul_eq_mul]
              exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Nat.sub_le M J)) (mul_nonneg hA hX)
         _ = _ := by
              rw [show 2+β*γ=1+(1+β*γ) by ring,Real.rpow_add hM',Real.rpow_one]
              dsimp only [X]; ring
  let logPrice := (M:ℝ)^3*conductorLog M
  have hlog : 0 ≤ logPrice := mul_nonneg (pow_nonneg hM'.le 3) (zero_le_one.trans (conductorLog_one_le M))
  have hdiff : |(∑ n ∈ Ioc J M, S n)-(∑ n ∈ Ioc J M, E n)| ≤ B*logPrice := by
    simpa only [logPrice,mul_assoc] using hb V U J M
  change |∑ n ∈ Ioc J M, S n| ≤ (A+B)*(logPrice+_)
  have ht := abs_add_le ((∑ n ∈ Ioc J M, S n)-(∑ n ∈ Ioc J M, E n)) (∑ n ∈ Ioc J M, E n)
  rw [sub_add_cancel] at ht
  apply ht.trans ((add_le_add hdiff hsum).trans ?_)
  linarith only [mul_nonneg hA hlog,mul_nonneg hB (Real.rpow_nonneg hM'.le (2+β*γ))]

/-- The prime-error term on every fixed subquadratic band has a strict power
gap below the critical price exponent 2+2Θ. Only cubic logarithmic rounding
remains at Θ=1/2. -/
theorem subquadratic_capped_band_at_zero_abscissa {α β : ℝ} (hα : 1 < α)
    (hab : α ≤ β) (hβ : β < 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ J M : ℕ, 0 < M →
      |∑ n ∈ Ioc J M, (n:ℝ)^2*(cappedUpperProductReading ⌊(n:ℝ)^α⌋₊ n n -
        cappedUpperProductReading ⌊(n:ℝ)^β⌋₊ n n)| ≤
        C*((M:ℝ)^3*conductorLog M+(M:ℝ)^(2+2*_root_.RHTower.zeroReSup-(2-β)/4)) := by
  let Θ := _root_.RHTower.zeroReSup
  let γ := Θ+(2-β)/8
  have hγ : Θ < γ := lt_add_of_pos_right _ (div_pos (sub_pos.mpr hβ) (by norm_num))
  obtain ⟨C,hC,h⟩ := subquadratic_capped_band hα hab hβ hγ
  refine ⟨C,hC,fun J M hM => (h J M hM).trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl ?_) hC)⟩
  apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hM : (1:ℝ) ≤ M)
  have hhalf : 1/2 ≤ Θ := _root_.RHTower.half_le_zeroReSup
  have hcoef : 0 ≤ Θ-β/8-1/4 := by linarith only [hhalf,hβ]
  change 2+β*(Θ+(2-β)/8) ≤ 2+2*Θ-(2-β)/4
  linarith only [mul_nonneg (sub_nonneg.mpr hβ.le) hcoef]

#print axioms subquadratic_centered_band
#print axioms subquadratic_capped_band
#print axioms subquadratic_capped_band_at_zero_abscissa
end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
