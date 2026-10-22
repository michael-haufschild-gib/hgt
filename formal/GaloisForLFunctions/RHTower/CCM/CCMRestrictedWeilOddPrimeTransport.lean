import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilOddPrimeCutoff
import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilGroundParity

/-!
# Actual prime transport on literal parity poles

The self-adjoint transport operator and reflection give the exact parity
matrix. Its odd entry is the hyperbolic cutoff kernel, including the literal
normalization of every visible atom. Each fixed integer transport atom changes
sign as aperture grows; positive Mangoldt weights preserve this reversal for
prime powers. The complete finite prime operator is the sum of these kernels.
-/

open Complex Set
open scoped InnerProduct BigOperators
noncomputable section
namespace RHTower

private theorem atom_minus_self (a : SuzukiPositiveAperture) (n : ℕ) :
    inner ℂ (ccmPrimeTransportOperator a n (ccmPolarApertureVector a (-1/2)))
      (ccmPolarApertureVector a (-1/2)) =
    inner ℂ (ccmPrimeTransportOperator a n (ccmPolarApertureVector a (1/2)))
      (ccmPolarApertureVector a (1/2)) := by
  have hm : ccmPolarL2Vector a (-1/2)=l2Reflection (ccmPolarL2Vector a (1/2)) := by
    simpa only [neg_div] using (l2Reflection_ccmPolarL2Vector a (1/2)).symm
  rw [inner_ccmPrimeTransportOperator,inner_ccmPrimeTransportOperator]
  simp only [ccmPolarApertureVector_coe,hm,inner_logTranslationCLM_reflection,neg_neg]
  ring

private theorem atom_minus_cross (a : SuzukiPositiveAperture) {n : ℕ}
    (hn : 2≤n) (hv : Real.log n≤2*a.1) :
    inner ℂ (ccmPrimeTransportOperator a n (ccmPolarApertureVector a (-1/2)))
      (ccmPolarApertureVector a (1/2)) =
      (((2*a.1-Real.log n)*(1+1/(n:ℝ)):ℝ):ℂ) := by
  have hs := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    (ccmPrimeTransportOperator_isSelfAdjoint a n)
  have hc : (starRingEnd ℂ) (inner ℂ (ccmPrimeTransportOperator a n (ccmPolarApertureVector a (1/2)))
      (ccmPolarApertureVector a (-1/2))) =
      inner ℂ (ccmPrimeTransportOperator a n (ccmPolarApertureVector a (-1/2)))
        (ccmPolarApertureVector a (1/2)) := by
    exact hs.conj_inner_sym (ccmPolarApertureVector a (1/2)) (ccmPolarApertureVector a (-1/2))
  rw [← hc,ccmPrimeTransport_polar_cross a hn hv,Complex.conj_ofReal]

/-- The actual prime operator on either literal parity pole has its exact two-entry energy. -/
theorem ccmPrimeTransport_polar_parity (a : SuzukiPositiveAperture) {n : ℕ}
    (hn : 2≤n) (hv : Real.log n≤2*a.1) {r : ℝ} (hr : r=1 ∨ r=-1) :
    inner ℂ (ccmPrimeTransportOperator a n
      (ccmPolarApertureVector a (1/2)+(r:ℂ) • ccmPolarApertureVector a (-1/2)))
      (ccmPolarApertureVector a (1/2)+(r:ℂ) • ccmPolarApertureVector a (-1/2)) =
      ((2*(2*(Real.exp a.1/n-Real.exp (-a.1))+
        r*(2*a.1-Real.log n)*(1+1/(n:ℝ))):ℝ):ℂ) := by
  simp only [map_add,map_smul,inner_add_left,inner_add_right,
    inner_smul_left (E:=suzukiApertureHilbert a),inner_smul_right (E:=suzukiApertureHilbert a),
    Complex.conj_ofReal,atom_minus_self,ccmPrimeTransport_polar_self a hn hv,
    ccmPrimeTransport_polar_cross a hn hv,atom_minus_cross a hn hv]
  rcases hr with rfl | rfl <;> push_cast <;> ring

private theorem kernel_exp_identity (a h : ℝ) :
    8*Real.exp (-h)*ccmOddPolePrimeKernel a h =
      4*(Real.exp a/Real.exp (2*h)-Real.exp (-a))-
        4*(a-h)*(1+1/Real.exp (2*h)) := by
  rw [ccmOddPolePrimeKernel,Real.sinh_eq,Real.cosh_eq,neg_sub,
    Real.exp_sub,Real.exp_sub,show 2*h=h+h by ring,Real.exp_add]
  simp only [Real.exp_neg]
  field_simp
  ring

/-- Exact hyperbolic kernel of every visible actual prime atom on the odd pole. -/
theorem ccmPrimeTransport_polar_odd_kernel (a : SuzukiPositiveAperture) {n : ℕ}
    (hn : 2≤n) (hv : Real.log n≤2*a.1) :
    inner ℂ (ccmPrimeTransportOperator a n
      (ccmPolarApertureVector a (1/2)-ccmPolarApertureVector a (-1/2)))
      (ccmPolarApertureVector a (1/2)-ccmPolarApertureVector a (-1/2)) =
      ((8*Real.exp (-(Real.log n/2))*ccmOddPolePrimeKernel a.1 (Real.log n/2):ℝ):ℂ) := by
  have hp := ccmPrimeTransport_polar_parity a hn hv (r := -1) (Or.inr rfl)
  simp only [Complex.ofReal_neg,Complex.ofReal_one,neg_one_smul,← sub_eq_add_neg] at hp
  rw [hp,kernel_exp_identity]
  have hnR : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  rw [show (2:ℝ)*(Real.log n/2)=Real.log n by ring,Real.exp_log hnR]
  push_cast
  ring

/-- Every integer transport atom with index at least two reverses its odd sign as
the aperture grows. A positive Mangoldt weight preserves this reversal for prime powers. -/
theorem ccmPrimeTransport_polar_odd_changes_sign {n : ℕ} (hn : 2≤n) :
    ∃ a b : SuzukiPositiveAperture, a.1<b.1 ∧
      (inner ℂ (ccmPrimeTransportOperator a n
        (ccmPolarApertureVector a (1/2)-ccmPolarApertureVector a (-1/2)))
        (ccmPolarApertureVector a (1/2)-ccmPolarApertureVector a (-1/2))).re<0 ∧
      0<(inner ℂ (ccmPrimeTransportOperator b n
        (ccmPolarApertureVector b (1/2)-ccmPolarApertureVector b (-1/2)))
        (ccmPolarApertureVector b (1/2)-ccmPolarApertureVector b (-1/2))).re := by
  have hl : 0<Real.log (n:ℝ) := Real.log_pos (by exact_mod_cast (show 1<n by omega))
  let a : SuzukiPositiveAperture := ⟨Real.log n,hl⟩
  let b : SuzukiPositiveAperture := ⟨3*Real.log n/2,by positivity⟩
  refine ⟨a,b,by dsimp [a,b]; linarith,?_,?_⟩
  · rw [ccmPrimeTransport_polar_odd_kernel a hn (by dsimp [a]; linarith),Complex.ofReal_re]
    apply mul_neg_of_pos_of_neg (by positivity)
    exact ccmOddPolePrimeKernel_neg_of_half_le a (by rfl) (by dsimp [a]; linarith)
  · rw [ccmPrimeTransport_polar_odd_kernel b hn (by dsimp [b]; linarith),Complex.ofReal_re]
    apply mul_pos (by positivity)
    exact ccmOddPolePrimeKernel_pos_of_le_third b (by linarith) (by dsimp [b]; linarith)

/-- Mangoldt-weighted odd prime-operator energy, with the actual transport normalization. -/
def ccmOddPolePrimeWeight (a : SuzukiPositiveAperture) (n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n *
    (8*Real.exp (-(Real.log n/2))*ccmOddPolePrimeKernel a.1 (Real.log n/2))

/-- The complete odd prime energy is exactly the finite sum of the classified kernels. -/
theorem ccmFinitePrimeOperator_polar_odd (a : SuzukiPositiveAperture) :
    inner ℂ (ccmFinitePrimeOperator a
      (ccmPolarApertureVector a (1/2)-ccmPolarApertureVector a (-1/2)))
      (ccmPolarApertureVector a (1/2)-ccmPolarApertureVector a (-1/2)) =
      ((∑ n ∈ Finset.Icc 2 ⌊Real.exp (2*a.1)⌋₊,ccmOddPolePrimeWeight a n : ℝ):ℂ) := by
  rw [inner_ccmFinitePrimeOperator,Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hnR : (0:ℝ)<n := by exact_mod_cast (show 0<n by have := (Finset.mem_Icc.mp hn).1; omega)
  have hv : Real.log n≤2*a.1 := (Real.log_le_iff_le_exp hnR).mpr
    ((Nat.le_floor_iff (Real.exp_pos _).le).mp (Finset.mem_Icc.mp hn).2)
  rw [ccmPrimeTransport_polar_odd_kernel a (Finset.mem_Icc.mp hn).1 hv,ccmOddPolePrimeWeight]
  push_cast
  rfl

end RHTower
