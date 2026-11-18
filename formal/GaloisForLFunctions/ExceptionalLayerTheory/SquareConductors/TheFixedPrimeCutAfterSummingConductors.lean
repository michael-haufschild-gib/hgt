import GaloisForLFunctions.CountingHolography.Sections.TheMellinKernelOfSquareConductorPrices

/-!
# A fixed prime cutoff after summing square conductors

The integrated prefix profile is exactly linear below the first knot.
Its slope is the Mellin transform of the single-conductor profile at −1.
Consequently an upper cutoff fixed at the terminal conductor transfers
a positive multiple of the first prime moment to the lower side.
-/

noncomputable section
open Finset MeasureTheory Zeta23 GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge
open GaloisForLFunctions.CountingHolography.Sections
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- Slope of the integrated prime weight below the first spline knot. -/
def innerPrimeSlope : ℝ := 15/8*(Real.sinh (3/2)/(3/2))^8

theorem innerPrimeSlope_pos : 0 < innerPrimeSlope :=
  mul_pos (by norm_num) (pow_pos (div_pos (Real.sinh_pos_iff.mpr (by norm_num)) (by norm_num)) _)

/-- The exponent −1 selects the first prime moment in the conductor prefix. -/
theorem mellin_squarePrimeWeight_neg_one :
    mellin squarePrimeWeight (-1) = (innerPrimeSlope:ℂ) := by
  have hlog : Real.log 4 = 2*Real.log 2 := by
    rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow]; norm_num
  have hexp : Real.exp ((-(3/2):ℝ)*Real.log 4) = 1/8 := by
    rw [hlog,show (-(3/2):ℝ)*(2*Real.log 2) = -(3*Real.log 2) by ring,
      Real.exp_neg,←show Real.log (2^3:ℝ)=3*Real.log 2 by rw [Real.log_pow]; norm_num]
    norm_num [Real.exp_log (by norm_num : (0:ℝ)<2^3)]
  rw [mellin_squarePrimeWeight_formula]
  norm_num only [show (-1:ℂ)-1/2=-(3/2) by norm_num]
  let a := (3/2:ℂ)
  have hm := GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments.paperFT_cubicSpline_div_I
    (z := -a) (by dsimp only [a]; norm_num)
  have hp := GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments.paperFT_cubicSpline_div_I
    (z := a) (by dsimp only [a]; norm_num)
  have he : Complex.exp (-a*(Real.log 4:ℝ))=((1/8:ℝ):ℂ) := by
    rw [←hexp,Complex.ofReal_exp]; congr 1; push_cast; ring
  change (2-Complex.exp (-a*(Real.log 4:ℝ)))*
    (paperFT (fun x => (cubicSpline x:ℂ)) (-a/Complex.I) *
     paperFT (fun x => (cubicSpline x:ℂ)) (-(-a/Complex.I))) = _
  rw [he,hm,←neg_div,neg_neg,hp,Complex.sinh_neg,neg_div_neg_eq]
  simp only [a,innerPrimeSlope,Complex.ofReal_mul,Complex.ofReal_div,Complex.ofReal_ofNat,
    Complex.ofReal_pow,Complex.ofReal_sinh]
  ring

/-- On the entire inner interval the integrated weight is a positive linear
function, although each individual conductor has a zero weight there. -/
theorem squarePrefixPrimeWeight_before_first_knot {v : ℝ} (hv : 0 < v)
    (hcut : v ≤ Real.exp (-8)) :
    squarePrefixPrimeWeight v = (v:ℂ)*innerPrimeSlope := by
  let g (t : ℝ) := squarePrimeWeight t/(t:ℂ)^2
  have hm : mellin squarePrimeWeight (-1) = ∫ t in Set.Ioi (0:ℝ), g t := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _
    simp only [g,show (-1:ℂ)-1=-(2:ℂ) by norm_num,Complex.cpow_neg,Complex.cpow_two,smul_eq_mul,
      div_eq_mul_inv,mul_comm]
  have he : (∫ t in Set.Ici v, g t) = ∫ t in Set.Ioi (0:ℝ), g t := by
    have hsub : Set.Ici v ⊆ Set.Ioi (0:ℝ) := fun _ ht => hv.trans_le ht
    rw [←Measure.restrict_restrict_of_subset hsub (μ := volume),←integral_indicator measurableSet_Ici]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    by_cases hk : v ≤ t
    · exact Set.indicator_of_mem hk _
    · have hzero := squarePrimeWeight_zero_outside ht (fun h => (lt_of_not_ge hk).not_ge (hcut.trans h.1))
      rw [Set.indicator_of_notMem (show t ∉ Set.Ici v from hk)]
      simp only [g,hzero,zero_div]
  rw [squarePrefixPrimeWeight_tail hv,←mellin_squarePrimeWeight_neg_one,hm]
  exact congrArg (fun z : ℂ => (v:ℂ)*z) he

/-- For any terminal N, every retained prime up to a fixed cutoff K below
the first knot has exactly the same multiplier of p log p. -/
theorem fixed_inner_prime_price {N K : ℕ} (hN : 0 < N)
    (hK : (K:ℝ) ≤ Real.exp (-8)*(N:ℝ)^2) :
    (N:ℂ)^2*(∑ p ∈ ordinaryPrimeLags K, (Real.log p:ℂ)*squarePrefixPrimeWeight ((p:ℝ)/(N:ℝ)^2)) =
      (innerPrimeSlope:ℂ)*∑ p ∈ ordinaryPrimeLags K, (p:ℂ)*Real.log p := by
  have hn : (0:ℝ) < N := Nat.cast_pos.mpr hN
  rw [mul_sum,mul_sum]
  apply sum_congr rfl
  intro p hp
  have h := mem_filter.mp hp
  have hk := (Nat.cast_le.mpr (mem_Icc.mp h.1).2 : (p:ℝ) ≤ K).trans hK
  rw [squarePrefixPrimeWeight_before_first_knot (div_pos (Nat.cast_pos.mpr h.2.pos) (sq_pos_of_pos hn))
    ((div_le_iff₀ (sq_pos_of_pos hn)).mpr hk)]
  push_cast
  field_simp [Nat.cast_ne_zero.mpr hN.ne' : (N:ℂ) ≠ 0] <;> ring

/-- The rational price with the first prime moment restored at the same
terminal conductor. The uniform cubic error is charged once for both sides. -/
theorem fixed_prime_cut_price_comparison :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {N K : ℕ}, 0 < N → (K:ℝ) ≤ Real.exp (-8)*(N:ℝ)^2 →
      let H := ⌊((N:ℝ)/squareConductorBVWindow.lower)^2⌋₊
      ‖(Real.log (squareGeneratorPrefix N:ℝ):ℂ) -
        ((innerPrimeSlope:ℂ)*(∑ p ∈ ordinaryPrimeLags K, (p:ℂ)*Real.log p) +
          (N:ℂ)^2*∑ p ∈ (ordinaryPrimeLags H).filter (K < ·),
            (Real.log p:ℂ)*squarePrefixPrimeWeight ((p:ℝ)/(N:ℝ)^2))‖ ≤ C*(N:ℝ)^3 := by
  obtain ⟨C,hC,hprice⟩ := squareGeneratorPrefix_prime_profile
  refine ⟨C,hC,fun {N K} hN hK => ?_⟩
  let H := ⌊((N:ℝ)/squareConductorBVWindow.lower)^2⌋₊
  let f (p : ℕ) := (Real.log p:ℂ)*squarePrefixPrimeWeight ((p:ℝ)/(N:ℝ)^2)
  have he : Real.exp (-8) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
  have hKH : K ≤ H := by
    apply Nat.le_floor
    apply hK.trans
    have hlo : squareConductorBVWindow.lower ≤ 1 := he
    have hsmall := mul_le_of_le_one_left (sq_nonneg (N:ℝ)) he
    exact hsmall.trans (pow_le_pow_left₀ (Nat.cast_nonneg N)
      (le_div_self (Nat.cast_nonneg N) squareConductorBVWindow.lower_pos.le hlo) 2)
  have hpr : (Ioc 0 H).filter Nat.Prime = ordinaryPrimeLags H := by
    ext p
    simp only [ordinaryPrimeLags,mem_filter,mem_Ioc,mem_Icc]
    exact ⟨fun h => ⟨⟨h.2.two_le,h.1.2⟩,h.2⟩,fun h => ⟨⟨h.2.pos,h.1.2⟩,h.2⟩⟩
  have hlow : (ordinaryPrimeLags H).filter (· ≤ K) = ordinaryPrimeLags K := by
    ext p
    simp only [ordinaryPrimeLags,mem_filter,mem_Icc]
    exact ⟨fun h => ⟨⟨h.1.1.1,h.2⟩,h.1.2⟩,
      fun h => ⟨⟨⟨h.1.1,h.1.2.trans hKH⟩,h.2⟩,h.1.2⟩⟩
  have hsplit := sum_filter_add_sum_filter_not (ordinaryPrimeLags H) (· ≤ K) f
  simp only [hlow,not_le] at hsplit
  have hp := hprice hN
  change ‖(Real.log (squareGeneratorPrefix N:ℝ):ℂ) -
    (N:ℂ)^2*∑ p ∈ (Ioc 0 H).filter Nat.Prime, f p‖ ≤ _ at hp
  rw [hpr,←hsplit,mul_add] at hp
  simpa only [f,fixed_inner_prime_price hN hK] using hp

#print axioms mellin_squarePrimeWeight_neg_one
#print axioms squarePrefixPrimeWeight_before_first_knot
#print axioms fixed_inner_prime_price
#print axioms fixed_prime_cut_price_comparison
end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
