import GaloisForLFunctions.RHTower.CCMRestrictedWeilOddPrimeTransport
import GaloisForLFunctions.RHTower.CCMRestrictedWeilPoleCompression

/-!
# Exact old and recent prime budgets for the odd Weil pole

The unique half-log cutoff partitions every visible Mangoldt term into an
old-prime loss and a recent-prime gain. Both budgets are nonnegative, and their
difference is the negative of the actual finite prime-operator energy.
Every genuine prime power reverses its contribution at two increasing apertures.
The complete odd Weil energy retains its exact Gamma and polar terms; its sign
is equivalent to the stated aggregate budget comparison, which remains open.
-/

open Complex Set
open scoped InnerProduct BigOperators
noncomputable section
namespace RHTower

private theorem visible_shift (a : SuzukiPositiveAperture) {n : ℕ}
    (hn : n∈Finset.Icc 2 ⌊Real.exp (2*a.1)⌋₊) : 0<Real.log (n:ℝ)/2 ∧ Real.log (n:ℝ)/2≤a.1 := by
  have hn1 : (1:ℝ)<n := by exact_mod_cast (show 1<n by have := (Finset.mem_Icc.mp hn).1; omega)
  have hl := Real.log_pos hn1
  have hv : Real.log n≤2*a.1 := (Real.log_le_iff_le_exp (by linarith : (0:ℝ)<n)).mpr
    ((Nat.le_floor_iff (Real.exp_pos _).le).mp (Finset.mem_Icc.mp hn).2)
  constructor <;> linarith

/-- The old-prime loss in odd Weil energy, retaining every visible prime power. -/
def ccmOddPoleOldPrimeBudget (a : SuzukiPositiveAperture) : ℝ :=
  ∑ n ∈ (Finset.Icc 2 ⌊Real.exp (2*a.1)⌋₊).filter
    (fun n : ℕ => Real.log (n:ℝ)/2≤ccmOddPolePrimeCutoff a),ccmOddPolePrimeWeight a n

/-- The recent-prime gain in odd Weil energy, with the exact same cutoff and normalization. -/
def ccmOddPoleRecentPrimeBudget (a : SuzukiPositiveAperture) : ℝ :=
  ∑ n ∈ (Finset.Icc 2 ⌊Real.exp (2*a.1)⌋₊).filter
    (fun n : ℕ => ccmOddPolePrimeCutoff a<Real.log (n:ℝ)/2),-ccmOddPolePrimeWeight a n

/-- The exact old-prime budget is nonnegative without any arithmetic sign premise. -/
theorem ccmOddPoleOldPrimeBudget_nonneg (a : SuzukiPositiveAperture) :
    0≤ccmOddPoleOldPrimeBudget a := by
  apply Finset.sum_nonneg
  intro n hn
  obtain ⟨hn,hcut⟩ := Finset.mem_filter.mp hn
  have hv := visible_shift a hn
  have hk : 0≤ccmOddPolePrimeKernel a.1 (Real.log n/2) := by
    rcases lt_or_eq_of_le hcut with ht | he
    · exact ((ccmOddPolePrimeKernel_pos_iff a
        ⟨hv.1,by linarith [(ccmOddPolePrimeCutoff_bounds a).2,a.2]⟩).mpr ht).le
    · rw [he,ccmOddPolePrimeKernel_cutoff]
  exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
    (mul_nonneg (by positivity) hk)

/-- The exact recent-prime budget is nonnegative, including zero terms at prime entry. -/
theorem ccmOddPoleRecentPrimeBudget_nonneg (a : SuzukiPositiveAperture) :
    0≤ccmOddPoleRecentPrimeBudget a := by
  apply Finset.sum_nonneg
  intro n hn
  obtain ⟨hn,hcut⟩ := Finset.mem_filter.mp hn
  have hv := visible_shift a hn
  have hk : ccmOddPolePrimeKernel a.1 (Real.log n/2)≤0 := by
    rcases lt_or_eq_of_le hv.2 with ht | he
    · exact ((ccmOddPolePrimeKernel_neg_iff a ⟨hv.1,ht⟩).mpr hcut).le
    · rw [he,ccmOddPolePrimeKernel_entry]
  apply neg_nonneg.mpr
  exact mul_nonpos_of_nonneg_of_nonpos ArithmeticFunction.vonMangoldt_nonneg
    (mul_nonpos_of_nonneg_of_nonpos (by positivity) hk)

/-- Exact signed decomposition: the prime part of odd Weil energy is recent gain minus old loss. -/
theorem ccmOddPolePrimeBudget_sub (a : SuzukiPositiveAperture) :
    ccmOddPoleRecentPrimeBudget a-ccmOddPoleOldPrimeBudget a =
      -(∑ n ∈ Finset.Icc 2 ⌊Real.exp (2*a.1)⌋₊,ccmOddPolePrimeWeight a n) := by
  classical
  rw [ccmOddPoleRecentPrimeBudget,ccmOddPoleOldPrimeBudget,Finset.sum_filter,Finset.sum_filter,
    ← Finset.sum_sub_distrib,← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hc : Real.log (n:ℝ)/2≤ccmOddPolePrimeCutoff a
  · simp [hc,not_lt.mpr hc]
  · simp [hc,lt_of_not_ge hc]

/-- The signed budgets are the exact quadratic value of the actual finite prime operator. -/
theorem ccmFinitePrimeOperator_polar_odd_eq_budgets (a : SuzukiPositiveAperture) :
    -(inner ℂ (ccmFinitePrimeOperator a
      (ccmPolarApertureVector a (1/2)-ccmPolarApertureVector a (-1/2)))
      (ccmPolarApertureVector a (1/2)-ccmPolarApertureVector a (-1/2))).re =
      ccmOddPoleRecentPrimeBudget a-ccmOddPoleOldPrimeBudget a := by
  rw [ccmFinitePrimeOperator_polar_odd,Complex.ofReal_re,ccmOddPolePrimeBudget_sub]

/-- Every strictly visible genuine prime power has its exact cutoff sign. -/
theorem ccmOddPolePrimeWeight_sign (a : SuzukiPositiveAperture) {n : ℕ}
    (hn : IsPrimePow n) (hv : Real.log (n:ℝ)/2∈Ioo 0 a.1) :
    (0<ccmOddPolePrimeWeight a n ↔ Real.log (n:ℝ)/2<ccmOddPolePrimeCutoff a) ∧
    (ccmOddPolePrimeWeight a n<0 ↔ ccmOddPolePrimeCutoff a<Real.log (n:ℝ)/2) := by
  have hp := ArithmeticFunction.vonMangoldt_pos_iff.mpr hn
  constructor
  · rw [ccmOddPolePrimeWeight,mul_pos_iff_of_pos_left hp,
      mul_pos_iff_of_pos_left (by positivity : 0<8*Real.exp (-(Real.log (n:ℝ)/2)))]
    exact ccmOddPolePrimeKernel_pos_iff a hv
  · have hneg : ccmOddPolePrimeWeight a n<0 ↔
        ccmOddPolePrimeKernel a.1 (Real.log n/2)<0 := by
      unfold ccmOddPolePrimeWeight
      have he : 0<8*Real.exp (-(Real.log (n:ℝ)/2)) := by positivity
      constructor
      · intro h
        by_contra hn
        have hk : 0≤ccmOddPolePrimeKernel a.1 (Real.log n/2) := le_of_not_gt hn
        have hprod := mul_nonneg hp.le (mul_nonneg he.le hk)
        linarith
      · intro hk
        exact mul_neg_of_pos_of_neg hp (mul_neg_of_pos_of_neg he hk)
    exact hneg.trans (ccmOddPolePrimeKernel_neg_iff a hv)

/-- For every genuine prime power, its actual contribution to the full odd Weil
energy is positive at one aperture and negative at a larger aperture. -/
theorem ccmOddPole_primePower_contribution_changes_sign {n : ℕ} (hn : IsPrimePow n) :
    ∃ a b : SuzukiPositiveAperture, a.1<b.1 ∧
      0< -(ArithmeticFunction.vonMangoldt n *
        (inner ℂ (ccmPrimeTransportOperator a n
          (ccmPolarApertureVector a (1/2)-ccmPolarApertureVector a (-1/2)))
          (ccmPolarApertureVector a (1/2)-ccmPolarApertureVector a (-1/2))).re) ∧
      -(ArithmeticFunction.vonMangoldt n *
        (inner ℂ (ccmPrimeTransportOperator b n
          (ccmPolarApertureVector b (1/2)-ccmPolarApertureVector b (-1/2)))
          (ccmPolarApertureVector b (1/2)-ccmPolarApertureVector b (-1/2))).re)<0 := by
  obtain ⟨a,b,hab,ha,hb⟩ := ccmPrimeTransport_polar_odd_changes_sign (n := n) hn.one_lt
  have hp := ArithmeticFunction.vonMangoldt_pos_iff.mpr hn
  exact ⟨a,b,hab,neg_pos.mpr (mul_neg_of_pos_of_neg hp ha),neg_neg_of_pos (mul_pos hp hb)⟩

private theorem finite_odd_matrix (a : SuzukiPositiveAperture) :
    inner ℂ (ccmFinitePrimeOperator a
      (ccmPolarApertureVector a (1/2)-ccmPolarApertureVector a (-1/2)))
      (ccmPolarApertureVector a (1/2)-ccmPolarApertureVector a (-1/2)) =
      ((2*(2*Real.exp a.1*ccmReciprocalMangoldtCumulative (Real.exp (2*a.1))-
        2*Real.exp (-a.1)*Chebyshev.psi (Real.exp (2*a.1))-ccmPolarPrimeTent a):ℝ):ℂ) := by
  have hmm : inner ℂ (ccmFinitePrimeOperator a (ccmPolarApertureVector a (-1/2)))
      (ccmPolarApertureVector a (-1/2)) =
      inner ℂ (ccmFinitePrimeOperator a (ccmPolarApertureVector a (1/2)))
        (ccmPolarApertureVector a (1/2)) := by
    simpa only [ccmArchimedeanFormReflection_polar,ccmArchimedeanFormToAperture_polar,neg_div] using
      inner_ccmFinitePrimeOperator_reflection a (ccmPolarFormVector a (1/2))
  have hs := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    (ccmFinitePrimeOperator_isSelfAdjoint a)
  have hmp : inner ℂ (ccmFinitePrimeOperator a (ccmPolarApertureVector a (-1/2)))
      (ccmPolarApertureVector a (1/2)) = (ccmPolarPrimeTent a:ℂ) := by
    have hc : (starRingEnd ℂ) (inner ℂ (ccmFinitePrimeOperator a (ccmPolarApertureVector a (1/2)))
        (ccmPolarApertureVector a (-1/2))) =
        inner ℂ (ccmFinitePrimeOperator a (ccmPolarApertureVector a (-1/2)))
          (ccmPolarApertureVector a (1/2)) := by
      exact hs.conj_inner_sym (ccmPolarApertureVector a (1/2)) (ccmPolarApertureVector a (-1/2))
    rw [← hc,ccmFinitePrimeOperator_polar_cross,Complex.conj_ofReal]
  rw [map_sub,inner_sub_left,inner_sub_right,inner_sub_right,hmm,hmp,
    ccmFinitePrimeOperator_polar_self,ccmFinitePrimeOperator_polar_cross]
  push_cast
  ring

/-- Gamma and pole part of the odd Weil energy, with the negative odd pole square retained. -/
def ccmOddPoleGammaPolarBalance (a : SuzukiPositiveAperture) : ℝ :=
  2*((-Real.eulerMascheroniConstant-Real.log (2*Real.pi))*(2*Real.sinh a.1-2*a.1)-
    Real.exp a.1+(2*a.1+1)*Real.exp (-a.1)+2*a.1^(2 : ℕ)+
    ccmGammaPoleSelfBoundaryMass a-ccmGammaPoleCrossBoundaryMass a-
    (2*Real.sinh a.1-2*a.1)^(2 : ℕ))

/-- Exact full-source decomposition: odd energy is Gamma–pole balance plus recent-prime
gain minus old-prime loss. Both prime budgets have unconditional nonnegative proofs. -/
theorem ccmWeilOddPole_eq_prime_budgets (a : SuzukiPositiveAperture) :
    ccmRestrictedWeilSourceQuadratic a (ccmPolarParityFormVector a (-1)) =
      ccmOddPoleGammaPolarBalance a+ccmOddPoleRecentPrimeBudget a-ccmOddPoleOldPrimeBudget a := by
  have hs := congrArg Complex.re ((ccmFinitePrimeOperator_polar_odd a).symm.trans (finite_odd_matrix a))
  simp only [Complex.ofReal_re] at hs
  rw [show ccmOddPoleGammaPolarBalance a+ccmOddPoleRecentPrimeBudget a-ccmOddPoleOldPrimeBudget a =
      ccmOddPoleGammaPolarBalance a+(ccmOddPoleRecentPrimeBudget a-ccmOddPoleOldPrimeBudget a) by ring,
    ccmOddPolePrimeBudget_sub,hs,ccmWeilPoleCompression_parity_energy a (Or.inr rfl),
    ccmWeilPoleDiagonal_eq,ccmWeilPoleCross_eq,ccmOddPoleGammaPolarBalance]
  ring

/-- The remaining odd arithmetic sign is precisely one comparison between the exact budgets. -/
theorem ccmWeilOddPole_nonneg_iff_prime_budget (a : SuzukiPositiveAperture) :
    0≤ccmRestrictedWeilSourceQuadratic a (ccmPolarParityFormVector a (-1)) ↔
      ccmOddPoleOldPrimeBudget a≤ccmOddPoleGammaPolarBalance a+ccmOddPoleRecentPrimeBudget a := by
  rw [ccmWeilOddPole_eq_prime_budgets,sub_nonneg]

end RHTower
