import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMNativeFourierMellinInterchange
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEisensteinTwoKBesselMellinProduct

/-! The original diagonal Fourier integrals have their derived two-Bessel Gamma value. -/
open Complex MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry
namespace RHTower.D4BMCuspProjection
open D4BMGlobalAngularResponse D4BMAngularSeries
noncomputable section

/-- The exact Gamma factor produced by the repeated original Bessel order. -/
def nativeBesselMellinFactor (q : XiZeroCopy) (s : ℂ) : ℂ :=
  (2:ℂ)^(s-3)/Complex.Gamma s *
    (Complex.Gamma (s/2+center q)*Complex.Gamma (s/2)^(2 : ℕ)*Complex.Gamma (s/2-center q))

/-- Every Xi source lies in the actual two-K chamber for the Mellin parameters used here. -/
theorem nativeBesselMellin_chamber (q : XiZeroCopy) (s : ℂ) (hs : 2 < s.re) :
    |(center q).re|+|(center q).re| < s.re := by
  have hq := xi_divisor_support_re_mem_open_unit q.1
  have hc : |(center q).re| < 1/2 := by
    rw [abs_lt]
    have he : (center q).re = (q.1:ℂ).re-1/2 := by simp [D4BMGlobalAngularResponse.center]
    rw [he]
    constructor <;> linarith [hq.1,hq.2]
  linarith

/-- The unchanged repeated Bessel integral has its exact Gamma product for every Xi source. -/
theorem nativeBesselMellin_value (q : XiZeroCopy) (s : ℂ) (hs : 2 < s.re) :
    (∫ x in Ioi (0:ℝ), (x:ℂ)^(s-1)*modifiedBesselKOrder x (center q)^(2 : ℕ)) =
      nativeBesselMellinFactor q s := by
  have h := GaloisForLFunctions.RHTower.integral_cpow_mul_modifiedBesselKOrder_mul_modifiedBesselKOrder
    (nativeBesselMellin_chamber q s hs)
  rw [show (s+center q+center q)/2=s/2+center q by ring,
    show (s+center q-center q)/2=s/2 by ring,
    show (s-center q+center q)/2=s/2 by ring,
    show (s-center q-center q)/2=s/2-center q by ring] at h
  simpa only [nativeBesselMellinFactor,pow_two,mul_assoc] using h

private theorem bessel_mellin_scale (u s : ℂ) (c : ℝ) (hc : 0 < c) :
    (∫ y in Ioi (0:ℝ), (y:ℂ)^(s-1)*modifiedBesselKOrder (c*y) u^(2 : ℕ)) =
      (c:ℂ)^(-s)*∫ x in Ioi (0:ℝ), (x:ℂ)^(s-1)*modifiedBesselKOrder x u^(2 : ℕ) := by
  let F : ℝ → ℂ := fun x => (x:ℂ)^(s-1)*modifiedBesselKOrder x u^(2 : ℕ)
  have hn : (c:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
  have he (y : ℝ) (hy : 0 < y) :
      (y:ℂ)^(s-1)*modifiedBesselKOrder (c*y) u^(2 : ℕ) = (c:ℂ)^(1-s)*F (c*y) := by
    dsimp [F]
    rw [Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg hc.le hy.le]
    have hp : (c:ℂ)^(1-s)*(c:ℂ)^(s-1) = 1 := by
      rw [← Complex.cpow_add _ _ hn,show (1-s)+(s-1)=0 by ring,Complex.cpow_zero]
    calc
      _ = ((c:ℂ)^(1-s)*(c:ℂ)^(s-1))*((y:ℂ)^(s-1)*modifiedBesselKOrder (c*y) u^(2 : ℕ)) := by rw [hp,one_mul]
      _ = _ := by ring
  have hi : (∫ y in Ioi (0:ℝ), (y:ℂ)^(s-1)*modifiedBesselKOrder (c*y) u^(2 : ℕ)) =
      ∫ y in Ioi (0:ℝ), (c:ℂ)^(1-s)*F (c*y) :=
    setIntegral_congr_fun measurableSet_Ioi he
  rw [hi,integral_const_mul,integral_comp_mul_left_Ioi F 0 hc]
  simp only [mul_zero,Complex.real_smul,Complex.ofReal_inv]
  have hp : (c:ℂ)^(1-s)*(c:ℂ)⁻¹ = (c:ℂ)^(-s) := by
    calc
      _ = (c:ℂ)^(1-s)*(c:ℂ)^(-1:ℂ) := by rw [Complex.cpow_neg_one]
      _ = _ := by rw [← Complex.cpow_add _ _ hn]; congr 1; ring
  rw [← mul_assoc,hp]

private theorem original_mode_integrand (q : XiZeroCopy) (s : ℂ) (N : ℕ) (y : ℝ) (hy : 0 < y) :
    nativeFourierMellinTerm q s N y = coefficient (center q) 0 N^(2 : ℕ) *
      ((y:ℂ)^(s-1)*modifiedBesselKOrder (2*Real.pi*((N:ℝ)+1)*y) (center q)^(2 : ℕ)) := by
  have hn : (y:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
  have hhalf : ((y^(1/2:ℝ):ℝ):ℂ)^(2 : ℕ) = (y:ℂ) := by
    rw [← Complex.ofReal_pow]
    congr 1
    rw [← Real.rpow_natCast,← Real.rpow_mul hy.le]
    norm_num
  have hp : (y:ℂ)^(s-2)*(y:ℂ) = (y:ℂ)^(s-1) := by
    calc
      _ = (y:ℂ)^(s-2)*(y:ℂ)^(1:ℂ) := by rw [Complex.cpow_one]
      _ = _ := by rw [← Complex.cpow_add _ _ hn]; congr 1; ring
  simp only [nativeFourierMellinTerm,amplitude,mul_pow,Real.rpow_eq_pow,hhalf]
  calc
    _ = coefficient (center q) 0 N^(2 : ℕ) *
      (((y:ℂ)^(s-2)*(y:ℂ))*modifiedBesselKOrder (2*Real.pi*((N:ℝ)+1)*y) (center q)^(2 : ℕ)) := by ring
    _ = _ := by rw [hp]

/-- Each actual weighted Fourier mode has its derived scaled Bessel Mellin value. -/
theorem nativeFourierMellinTerm_value (q : XiZeroCopy) (s : ℂ) (hs : 2 < s.re) (N : ℕ) :
    (∫ y in Ioi (0:ℝ), nativeFourierMellinTerm q s N y) =
      coefficient (center q) 0 N^(2 : ℕ) *
        ((2*Real.pi*((N:ℝ)+1):ℝ):ℂ)^(-s)*nativeBesselMellinFactor q s := by
  have he := setIntegral_congr_fun (μ := volume) measurableSet_Ioi (original_mode_integrand q s N)
  rw [he,integral_const_mul,bessel_mellin_scale _ _ _ (by positivity),nativeBesselMellin_value q s hs]
  ring

/-- The original diagonal integral reduces to its actual arithmetic coefficient series with all Gamma factors. -/
theorem nativeFourierMellin_value (q : XiZeroCopy) (s : ℂ) (hs : 2 < s.re) :
    (∫ y in Ioi (0:ℝ), (y:ℂ)^(s-2)*(∑' N, amplitude (center q) y N^(2 : ℕ))) =
      (((2*Real.pi:ℝ):ℂ)^(-s)*nativeBesselMellinFactor q s)*
        ∑' N : ℕ, coefficient (center q) 0 N^(2 : ℕ) * ((N+1:ℕ):ℂ)^(-s) := by
  rw [nativeFourierMellin_integral_eq_tsum q s hs]
  have ht (N : ℕ) : (∫ y in Ioi (0:ℝ), (y:ℂ)^(s-2)*amplitude (center q) y N^(2 : ℕ)) =
      (((2*Real.pi:ℝ):ℂ)^(-s)*nativeBesselMellinFactor q s)*
        (coefficient (center q) 0 N^(2 : ℕ) * ((N+1:ℕ):ℂ)^(-s)) := by
    change (∫ y in Ioi (0:ℝ), nativeFourierMellinTerm q s N y) = _
    rw [nativeFourierMellinTerm_value q s hs,Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (by positivity : (0:ℝ)≤2*Real.pi) (by positivity : (0:ℝ)≤(N:ℝ)+1)]
    push_cast
    ring
  simp_rw [ht]
  exact tsum_mul_left

end
end RHTower.D4BMCuspProjection
