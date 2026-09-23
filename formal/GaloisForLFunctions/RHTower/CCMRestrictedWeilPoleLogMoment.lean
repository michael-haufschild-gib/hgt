import GaloisForLFunctions.RHTower.CCMRestrictedWeilPoleFirstJets

/-!
# The value moment missing from the pole first jets

The actual cross value retains a weighted logarithmic Mangoldt moment, giving
an exact even-energy threshold. For arbitrary nonnegative weights on 2, 3, 4,
we classify every weight triple with fixed ordinary and reciprocal masses.
Its diagonal response and cross derivative are fixed but its cross value fills
a nondegenerate sharp interval. This diagnoses a generic recovery shortcut;
the auxiliary weights are not the actual Mangoldt coefficients.
-/

open Set MeasureTheory Filter
open scoped BigOperators Topology
noncomputable section
namespace RHTower

/-- The exact logarithmic arithmetic moment retained by the frozen cross value. -/
def ccmWeilPolePrimeLogMoment (a : SuzukiPositiveAperture) : ℝ :=
  ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2*a.1)⌋₊,
    ArithmeticFunction.vonMangoldt n*(1+1/(n:ℝ))*Real.log n

/-- The cross value retains one logarithmic moment beyond the two masses in its first jet. -/
theorem ccmWeilPoleChamberCross_eq_logMoment (a : SuzukiPositiveAperture) (s : ℝ) :
    ccmWeilPoleChamberCross a s = ccmWeilPoleCrossSmooth s-
      2*s*(Chebyshev.psi (Real.exp (2*a.1))+
        ccmReciprocalMangoldtCumulative (Real.exp (2*a.1)))+ccmWeilPolePrimeLogMoment a := by
  rw [ccmWeilPoleChamberCross_eq_sum_atoms,← ccmWeilPrimeChamberWeight_eq_cumulatives]
  have hsum : (∑ n ∈ Finset.Icc 2 ⌊Real.exp (2*a.1)⌋₊, ccmWeilPolePrimeCrossAtom n s) =
      2*s*ccmWeilPrimeChamberWeight a-ccmWeilPolePrimeLogMoment a := by
    unfold ccmWeilPrimeChamberWeight ccmWeilPolePrimeLogMoment
    rw [Finset.mul_sum,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    unfold ccmWeilPolePrimeCrossAtom
    ring
  rw [hsum]
  ring

/-- The exact threshold for the additional arithmetic moment required by the even value. -/
theorem ccmWeilEvenPole_nonneg_iff_logMoment (a : SuzukiPositiveAperture) :
    0 ≤ ccmRestrictedWeilSourceQuadratic a (ccmPolarParityFormVector a 1) ↔
      2*a.1*(Chebyshev.psi (Real.exp (2*a.1))+
        ccmReciprocalMangoldtCumulative (Real.exp (2*a.1)))-
        ccmWeilPoleDiagonal a-ccmWeilPoleCrossSmooth a.1 ≤ ccmWeilPolePrimeLogMoment a := by
  rw [ccmWeilPoleCompression_parity_energy a (Or.inl rfl),
    ccmWeilPoleCross_eq_chamber_of_floor_eq a a rfl,ccmWeilPoleChamberCross_eq_logMoment]
  constructor <;> intro h <;> linarith

/-- General positive-weight diagonal response on the genuine prime-power support 2, 3, 4. -/
def ccmWeilThreeAtomDiagonal (u v w s : ℝ) : ℝ :=
  2*u*(Real.exp s/2-Real.exp (-s))+
    2*v*(Real.exp s/3-Real.exp (-s))+2*w*(Real.exp s/4-Real.exp (-s))

/-- General cross response on the same support; these weights are not asserted to be Mangoldt weights. -/
def ccmWeilThreeAtomCross (u v w s : ℝ) : ℝ :=
  u*(1+1/2)*(2*s-Real.log 2)+v*(1+1/3)*(2*s-Real.log 3)+
    w*(1+1/4)*(2*s-Real.log 4)

/-- The logarithmic value separation along the fixed-mass positive family. -/
def ccmWeilThreeAtomLogSeparation : ℝ := 13*Real.log 2-8*Real.log 3

/-- The separation is strictly positive by the exact integer inequality 3^(8 : ℕ) < 2^(13 : ℕ). -/
theorem ccmWeilThreeAtomLogSeparation_pos : 0 < ccmWeilThreeAtomLogSeparation := by
  have h := Real.log_lt_log (by norm_num : (0:ℝ)<3^(8 : ℕ)) (by norm_num : (3:ℝ)^(8 : ℕ)<2^(13 : ℕ))
  rw [Real.log_pow,Real.log_pow] at h
  unfold ccmWeilThreeAtomLogSeparation
  norm_num at h
  linarith

/-- Complete classification of nonnegative weights with ordinary mass six and reciprocal mass two. -/
theorem ccmWeilThreeAtom_mass_classification (u v w : ℝ) :
    (0≤u ∧ 0≤v ∧ 0≤w ∧ u+v+w=6 ∧ u/2+v/3+w/4=2) ↔
      ∃ t ∈ Icc (0:ℝ) 1, u=2*t ∧ v=6*(1-t) ∧ w=4*t := by
  constructor
  · rintro ⟨hu,hv,hw,hS,hR⟩
    refine ⟨w/4,⟨by linarith,by linarith⟩,?_,?_,?_⟩ <;> linarith
  · rintro ⟨t,ht,rfl,rfl,rfl⟩
    constructor
    · linarith [ht.1]
    constructor
    · linarith [ht.2]
    constructor
    · linarith [ht.1]
    constructor <;> ring

/-- The entire diagonal response is constant along the classified family. -/
theorem ccmWeilThreeAtomDiagonal_family (t s : ℝ) :
    ccmWeilThreeAtomDiagonal (2*t) (6*(1-t)) (4*t) s = 4*Real.exp s-12*Real.exp (-s) := by
  unfold ccmWeilThreeAtomDiagonal
  ring

/-- The entire cross response separates into a common slope and a strictly changing logarithmic intercept. -/
theorem ccmWeilThreeAtomCross_family (t s : ℝ) :
    ccmWeilThreeAtomCross (2*t) (6*(1-t)) (4*t) s =
      16*s-8*Real.log 3-t*ccmWeilThreeAtomLogSeparation := by
  have h4 : Real.log 4 = 2*Real.log 2 := by
    simpa only [show (2:ℝ)^(2 : ℕ)=4 by norm_num,Nat.cast_ofNat] using Real.log_pow (2:ℝ) 2
  unfold ccmWeilThreeAtomCross ccmWeilThreeAtomLogSeparation
  rw [h4]
  ring

/-- Every member has precisely the same cross first jet at every real radius. -/
theorem hasDerivAt_ccmWeilThreeAtomCross_family (t s : ℝ) :
    HasDerivAt (ccmWeilThreeAtomCross (2*t) (6*(1-t)) (4*t)) 16 s := by
  have hf := funext (ccmWeilThreeAtomCross_family t)
  rw [hf]
  convert! (((hasDerivAt_id s).const_mul 16).sub_const (8*Real.log 3)).sub_const
    (t*ccmWeilThreeAtomLogSeparation) using 1
  ring

/-- The exact sharp range of cross values at fixed ordinary and reciprocal masses. -/
theorem ccmWeilThreeAtomCross_range {u v w s : ℝ}
    (hm : 0≤u ∧ 0≤v ∧ 0≤w ∧ u+v+w=6 ∧ u/2+v/3+w/4=2) :
    16*s-13*Real.log 2 ≤ ccmWeilThreeAtomCross u v w s ∧
      ccmWeilThreeAtomCross u v w s ≤ 16*s-8*Real.log 3 := by
  obtain ⟨t,ht,rfl,rfl,rfl⟩ := (ccmWeilThreeAtom_mass_classification u v w).mp hm
  rw [ccmWeilThreeAtomCross_family]
  have h0 := mul_nonneg ht.1 ccmWeilThreeAtomLogSeparation_pos.le
  have h1 := mul_le_mul_of_nonneg_right ht.2 ccmWeilThreeAtomLogSeparation_pos.le
  unfold ccmWeilThreeAtomLogSeparation at *
  constructor <;> nlinarith

/-- An unconditional witness: equal mass data and entire diagonal, equal cross derivatives,
but strictly different cross values. This is a weight-model obstruction, not an assertion about actual Mangoldt coefficients. -/
theorem ccmWeilThreeAtom_equal_jets_different_values :
    ((2:ℝ)+0+4=0+6+0) ∧ ((2:ℝ)/2+0/3+4/4=0/2+6/3+0/4) ∧
    (∀ s, ccmWeilThreeAtomDiagonal 2 0 4 s = ccmWeilThreeAtomDiagonal 0 6 0 s) ∧
    (∀ s, deriv (ccmWeilThreeAtomCross 2 0 4) s = deriv (ccmWeilThreeAtomCross 0 6 0) s) ∧
    (∀ s, ccmWeilThreeAtomCross 2 0 4 s < ccmWeilThreeAtomCross 0 6 0 s) := by
  refine ⟨by norm_num,by norm_num,?_,?_,?_⟩
  · intro s
    have h1 := ccmWeilThreeAtomDiagonal_family 1 s
    have h0 := ccmWeilThreeAtomDiagonal_family 0 s
    norm_num at h1 h0
    exact h1.trans h0.symm
  · intro s
    have h1 := (hasDerivAt_ccmWeilThreeAtomCross_family 1 s).deriv
    have h0 := (hasDerivAt_ccmWeilThreeAtomCross_family 0 s).deriv
    norm_num at h1 h0
    exact h1.trans h0.symm
  · intro s
    have h1 := ccmWeilThreeAtomCross_family 1 s
    have h0 := ccmWeilThreeAtomCross_family 0 s
    norm_num at h1 h0
    rw [h1,h0]
    linarith [ccmWeilThreeAtomLogSeparation_pos]

/-- Every point of the sharp interval is realized by nonnegative weights with the same two masses. -/
theorem ccmWeilThreeAtomCross_range_iff (s y : ℝ) :
    (∃ u v w : ℝ, (0≤u ∧ 0≤v ∧ 0≤w ∧ u+v+w=6 ∧ u/2+v/3+w/4=2) ∧
      ccmWeilThreeAtomCross u v w s=y) ↔
      16*s-13*Real.log 2≤y ∧ y≤16*s-8*Real.log 3 := by
  constructor
  · rintro ⟨u,v,w,hm,rfl⟩
    exact ccmWeilThreeAtomCross_range hm
  · rintro ⟨hlo,hhi⟩
    let t := (16*s-8*Real.log 3-y)/ccmWeilThreeAtomLogSeparation
    have ht0 : 0≤t := div_nonneg (by linarith) ccmWeilThreeAtomLogSeparation_pos.le
    have ht1 : t≤1 := by
      apply (div_le_one ccmWeilThreeAtomLogSeparation_pos).mpr
      unfold ccmWeilThreeAtomLogSeparation
      linarith
    refine ⟨2*t,6*(1-t),4*t,?_,?_⟩
    · exact (ccmWeilThreeAtom_mass_classification _ _ _).mpr ⟨t,⟨ht0,ht1⟩,rfl,rfl,rfl⟩
    · rw [ccmWeilThreeAtomCross_family]
      dsimp [t]
      rw [div_mul_cancel₀ _ (ne_of_gt ccmWeilThreeAtomLogSeparation_pos)]
      ring

end RHTower
