import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMNativeFourierBesselValue
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMEisensteinRamanujanProductDirichletSeries

/-! The literal native Fourier coefficients give the original two-shift divisor Dirichlet series. -/
open Complex MeasureTheory Set Filter Topology
namespace RHTower.D4BMCuspProjection
open D4BMGlobalAngularResponse D4BMAngularSeries
noncomputable section

private theorem divisorArithmetic_sum (a : ℂ) (n : ℕ) :
    d4BMGeneralizedDivisorArithmetic a n = ∑ d ∈ n.divisors, (d:ℂ)^a := by
  rw [d4BMGeneralizedDivisorArithmetic,ArithmeticFunction.coe_zeta_mul_apply]
  apply Finset.sum_congr rfl
  intro d hd
  have hd0 : d ≠ 0 := by intro h; subst d; simp at hd
  simp only [d4BMPowerArithmetic_apply,ArithmeticFunction.natCoe_apply,
    ArithmeticFunction.zeta_apply,if_neg hd0,Nat.cast_one,one_mul]

/-- The squared original Whittaker coefficient is exactly the corresponding divisor-series term. -/
theorem originalCoefficient_eq_dirichletTerm (u s : ℂ) (N : ℕ) :
    coefficient u 0 N^(2 : ℕ)*((N+1:ℕ):ℂ)^(-s) =
      LSeries.term (d4BMDivisorProductArithmetic (-2*u) (-2*u)) (s-2*u) (N+1) := by
  have hn : ((N+1:ℕ):ℂ) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero N)
  rw [LSeries.term_of_ne_zero (Nat.succ_ne_zero N),d4BMDivisorProductArithmetic_apply,
    divisorArithmetic_sum,coefficient,d4BMCompletedEisensteinWhittakerCoefficient]
  simp only [pow_zero,mul_one,mul_pow,div_eq_mul_inv,← Complex.cpow_neg]
  have hp : (((N+1:ℕ):ℂ)^u)^(2 : ℕ)*((N+1:ℕ):ℂ)^(-s) = ((N+1:ℕ):ℂ)^(-(s-2*u)) := by
    rw [pow_two,← Complex.cpow_add _ _ hn,← Complex.cpow_add _ _ hn]
    congr 1
    ring
  calc
    _ = ((((N+1:ℕ):ℂ)^u)^(2 : ℕ)*((N+1:ℕ):ℂ)^(-s))*(∑ d ∈ (N+1).divisors, (d:ℂ)^(-2*u))^(2 : ℕ) := by ring
    _ = _ := by rw [hp]; ring

private theorem lseries_eq_positive_tsum (f : ℕ → ℂ) (s : ℂ) :
    LSeries f s = ∑' N : ℕ, LSeries.term f s (N+1) := by
  unfold LSeries
  by_cases h : Summable (LSeries.term f s)
  · rw [h.tsum_eq_zero_add,LSeries.term_zero,zero_add]
  · have hn : ¬ Summable (fun N : ℕ => LSeries.term f s (N+1)) :=
      fun hh => h ((summable_nat_add_iff 1).mp hh)
    rw [tsum_eq_zero_of_not_summable h,tsum_eq_zero_of_not_summable hn]

/-- The entire original arithmetic coefficient series has the exact two-shift L-series expression. -/
theorem originalCoefficient_tsum_eq_lseries (u s : ℂ) :
    (∑' N : ℕ, coefficient u 0 N^(2 : ℕ)*((N+1:ℕ):ℂ)^(-s)) =
      LSeries (d4BMDivisorProductArithmetic (-2*u) (-2*u)) (s-2*u) := by
  simp_rw [originalCoefficient_eq_dirichletTerm]
  exact (lseries_eq_positive_tsum _ _).symm

/-- The original admitted Fourier integral is identified with its actual Bessel--Dirichlet value. -/
theorem nativeFourierMellin_lseries (q : XiZeroCopy) (s : ℂ) (hs : 2 < s.re) :
    (∫ y in Ioi (0:ℝ), (y:ℂ)^(s-2)*(∑' N, amplitude (center q) y N^(2 : ℕ))) =
      ((((2*Real.pi:ℝ):ℂ)^(-s)*nativeBesselMellinFactor q s)*
        LSeries (d4BMDivisorProductArithmetic (-2*center q) (-2*center q)) (s-2*center q)) := by
  rw [nativeFourierMellin_value q s hs,originalCoefficient_tsum_eq_lseries]

private def nativeRamanujanChamber (q : XiZeroCopy) (hq : 1/2 < (q.1:ℂ).re)
    (s : ℂ) (hs : 2 < s.re) : D4BMRamanujanProductChamber where
  a := ⟨-2*center q,by simp [D4BMGlobalAngularResponse.center]; linarith⟩
  b := ⟨-2*center q,by simp [D4BMGlobalAngularResponse.center]; linarith⟩
  w := s-2*center q
  w_re_gt_one := by
    have hu := (xi_divisor_support_re_mem_open_unit q.1).2
    simp [D4BMGlobalAngularResponse.center]
    linarith

/-- Right-half Xi sources give a genuinely convergent divisor-product L-series in the original chamber. -/
theorem nativeRamanujan_summable (q : XiZeroCopy) (hq : 1/2 < (q.1:ℂ).re)
    (s : ℂ) (hs : 2 < s.re) :
    LSeriesSummable (d4BMDivisorProductArithmetic (-2*center q) (-2*center q)) (s-2*center q) := by
  let X := nativeRamanujanChamber q hq s hs
  exact d4BMDivisorProductArithmetic_LSeriesSummable X.a X.b X.w_re_gt_one

/-- The actual native divisor-product series has its derived four-zeta value. -/
theorem nativeRamanujan_value (q : XiZeroCopy) (hq : 1/2 < (q.1:ℂ).re)
    (s : ℂ) (hs : 2 < s.re) :
    LSeries (d4BMDivisorProductArithmetic (-2*center q) (-2*center q)) (s-2*center q) =
      riemannZeta (s-2*center q)*riemannZeta s^(2 : ℕ)*riemannZeta (s+2*center q)/riemannZeta (2*s) := by
  have h := LSeries_d4BMDivisorProductArithmetic_eq_fourZetaQuotient (nativeRamanujanChamber q hq s hs)
  simp only [nativeRamanujanChamber,d4BMRamanujanFourZetaValue,d4BMRamanujanPolarZetaValue] at h
  rw [show (s-2*center q)-(-2*center q)=s by ring,
    show (s-2*center q)-((-2*center q)+(-2*center q))=s+2*center q by ring,
    show 2*(s-2*center q)-(-2*center q)-(-2*center q)=2*s by ring] at h
  simpa only [pow_two,mul_assoc] using h

end
end RHTower.D4BMCuspProjection
