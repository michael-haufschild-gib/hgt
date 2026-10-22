import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBifurcateNonlinearBeatObstruction

/-!
# Causal redshift classification of the reflected/conjugate Xi pair

The two exact Birmingham--Mokhtari characters have decay exponents
`4n + 3 - re rho` and `4n + 2 + re rho`.  Both are positive throughout the
critical strip, so their physical future energy decays for every Xi divisor,
including tilted divisors.  Removing their common redshift `4n + 5/2` leaves
the projective variant

`exp (delta t) + exp (-delta t)`, where `delta = re rho - 1/2`.

Thus causal decay is insensitive to RH, while relative channel drift records
the critical-line defect exactly.  The redshift-normalized beat energy is the
normalized causal pair energy at doubled relative time.
-/

open Complex Real Set Filter Topology

namespace RHTower

noncomputable section

/-- Time character of the theta-reflected Birmingham--Mokhtari mode. -/
def d4ThetaHawkingReflectedQNMCharacter
    (n : ℕ) (q : XiZeroCopy) (t : ℝ) : ℂ :=
  Complex.exp (-Complex.I *
    thetaCuspHawkingTopologicalBlackHoleQNMPlus n
      (xiSpectralPoint (xiZeroCopyReflectEquiv q)) * (t : ℂ))

/-- Time character of the Schwarz-conjugated Birmingham--Mokhtari mode. -/
def d4ThetaHawkingConjugateQNMCharacter
    (n : ℕ) (q : XiZeroCopy) (t : ℝ) : ℂ :=
  Complex.exp (-Complex.I *
    thetaCuspHawkingTopologicalBlackHoleQNMPlus n
      (xiSpectralPoint (xiZeroCopyConjEquiv q)) * (t : ℂ))

/-- Physical causal energy of the reflected/conjugate pair. -/
def d4ThetaHawkingReflectedConjugateCausalEnergy
    (n : ℕ) (q : XiZeroCopy) (t : ℝ) : ℝ :=
  Complex.normSq (d4ThetaHawkingReflectedQNMCharacter n q t) +
    Complex.normSq (d4ThetaHawkingConjugateQNMCharacter n q t)

private lemma normSq_qnmCharacter (omega : ℂ) (t : ℝ) :
    Complex.normSq (Complex.exp (-Complex.I * omega * (t : ℂ))) =
      Real.exp (2 * omega.im * t) := by
  rw [Complex.normSq_eq_norm_sq, Complex.norm_exp]
  simp only [Complex.mul_re, Complex.neg_re, Complex.I_re, zero_mul,
    Complex.I_im, neg_mul, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
    sub_zero, zero_sub, pow_two, ← Real.exp_add]
  congr 1
  ring

/-- Exact damping of the theta-reflected QNM character. -/
theorem d4ThetaHawkingReflectedQNM_im
    (n : ℕ) (q : XiZeroCopy) :
    (thetaCuspHawkingTopologicalBlackHoleQNMPlus n
      (xiSpectralPoint (xiZeroCopyReflectEquiv q))).im =
      -((2 : ℝ) * n + 3 / 2 - (q.1 : ℂ).re / 2) := by
  rw [xiSpectralPoint_reflect]
  simp [thetaCuspHawkingTopologicalBlackHoleQNMPlus,
    thetaCuspHawkingTopologicalBlackHoleAngularMomentum,
    thetaCuspHawkingTopologicalBlackHoleConformalDecay,
    xiSpectralPoint]
  ring

/-- Exact damping of the Schwarz-conjugated QNM character. -/
theorem d4ThetaHawkingConjugateQNM_im
    (n : ℕ) (q : XiZeroCopy) :
    (thetaCuspHawkingTopologicalBlackHoleQNMPlus n
      (xiSpectralPoint (xiZeroCopyConjEquiv q))).im =
      -((2 : ℝ) * n + 1 + (q.1 : ℂ).re / 2) := by
  rw [xiSpectralPoint_copyConj]
  simp [thetaCuspHawkingTopologicalBlackHoleQNMPlus,
    thetaCuspHawkingTopologicalBlackHoleAngularMomentum,
    thetaCuspHawkingTopologicalBlackHoleConformalDecay,
    xiSpectralPoint]
  ring

/-- Closed physical-energy formula before redshift normalization. -/
theorem d4ThetaHawkingReflectedConjugateCausalEnergy_eq
    (n : ℕ) (q : XiZeroCopy) (t : ℝ) :
    d4ThetaHawkingReflectedConjugateCausalEnergy n q t =
      Real.exp (-((4 : ℝ) * n + 3 - (q.1 : ℂ).re) * t) +
      Real.exp (-((4 : ℝ) * n + 2 + (q.1 : ℂ).re) * t) := by
  rw [d4ThetaHawkingReflectedConjugateCausalEnergy,
    d4ThetaHawkingReflectedQNMCharacter,
    d4ThetaHawkingConjugateQNMCharacter, normSq_qnmCharacter,
    normSq_qnmCharacter, d4ThetaHawkingReflectedQNM_im,
    d4ThetaHawkingConjugateQNM_im]
  congr 1 <;> congr 1 <;> ring

/-- Causal pair energy after removing the common Birmingham--Mokhtari redshift. -/
def d4ThetaHawkingRedshiftNormalizedCausalEnergy
    (n : ℕ) (q : XiZeroCopy) (t : ℝ) : ℝ :=
  Real.exp (((4 : ℝ) * n + 5 / 2) * t) *
    d4ThetaHawkingReflectedConjugateCausalEnergy n q t

/-- Common-redshift removal exposes exactly the FE--Schwarz projective drift. -/
theorem d4ThetaHawkingRedshiftNormalizedCausalEnergy_eq
    (n : ℕ) (q : XiZeroCopy) (t : ℝ) :
    d4ThetaHawkingRedshiftNormalizedCausalEnergy n q t =
      Real.exp (d4ThetaHawkingBMBeatRate q * t) +
      Real.exp (-d4ThetaHawkingBMBeatRate q * t) := by
  rw [d4ThetaHawkingRedshiftNormalizedCausalEnergy,
    d4ThetaHawkingReflectedConjugateCausalEnergy_eq, mul_add,
    ← Real.exp_add, ← Real.exp_add]
  congr 1 <;> congr 1 <;> unfold d4ThetaHawkingBMBeatRate <;> ring

/-- The earlier projective beat is the actual causal pair after common-redshift removal and
doubling of relative time. -/
theorem d4ThetaHawkingProjectiveBeatEnergy_eq_redshiftNormalizedCausalEnergy
    (amplitude : ℂ) (n : ℕ) (q : XiZeroCopy) (t : ℝ) :
    d4ThetaHawkingBifurcateNonlinearBeatEnergy amplitude q t =
      Complex.normSq (d4ThetaHawkingNonlinearBeatCarrier amplitude q) *
        d4ThetaHawkingRedshiftNormalizedCausalEnergy n q (2 * t) := by
  rw [d4ThetaHawkingBifurcateNonlinearBeatEnergy_eq,
    d4ThetaHawkingRedshiftNormalizedCausalEnergy_eq]
  congr 1
  congr 1 <;> congr 1 <;> ring

/-- Every Xi-labelled reflected/conjugate QNM pair decays in future physical time. -/
theorem d4ThetaHawkingReflectedConjugateCausalEnergy_tendsto_zero
    (n : ℕ) (q : XiZeroCopy) :
    Tendsto (d4ThetaHawkingReflectedConjugateCausalEnergy n q) atTop (𝓝 0) := by
  rw [show d4ThetaHawkingReflectedConjugateCausalEnergy n q = fun t =>
      Real.exp (-((4 : ℝ) * n + 3 - (q.1 : ℂ).re) * t) +
      Real.exp (-((4 : ℝ) * n + 2 + (q.1 : ℂ).re) * t) by
    funext t
    exact d4ThetaHawkingReflectedConjugateCausalEnergy_eq n q t]
  have hstrip := xi_divisor_support_re_mem_open_unit q.1
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have h1 : 0 < (4 : ℝ) * n + 3 - (q.1 : ℂ).re := by
    linarith [hstrip.2]
  have h2 : 0 < (4 : ℝ) * n + 2 + (q.1 : ℂ).re := by
    linarith [hstrip.1]
  have hdecay (b : ℝ) (hb : 0 < b) :
      Tendsto (fun t : ℝ => Real.exp (-(b * t))) atTop (𝓝 0) := by
    have hlin : Tendsto (fun t : ℝ => b * t) atTop atTop := by
      simpa using tendsto_id.const_mul_atTop hb
    exact Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hlin)
  have hsum := (hdecay _ h1).add (hdecay _ h2)
  convert hsum using 1
  · funext t
    congr 1 <;> congr 1 <;> ring
  · simp

/-- No decaying QNM pair has uniformly bounded energy on the full two-sided time axis, even on
the critical line. -/
theorem d4ThetaHawkingReflectedConjugateCausalEnergy_not_twoSidedBounded
    (n : ℕ) (q : XiZeroCopy) :
    ¬ ∃ M : ℝ, ∀ t : ℝ,
      d4ThetaHawkingReflectedConjugateCausalEnergy n q t ≤ M := by
  rintro ⟨M, hM⟩
  let a : ℝ := (4 : ℝ) * n + 3 - (q.1 : ℂ).re
  have hstrip := xi_divisor_support_re_mem_open_unit q.1
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have ha : 0 < a := by
    dsimp [a]
    linarith [hstrip.2]
  have hlin : Tendsto (fun k : ℕ => a * (k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop ha
  have hexp : Tendsto (fun k : ℕ => Real.exp (a * (k : ℝ))) atTop atTop :=
    Real.tendsto_exp_atTop.comp hlin
  obtain ⟨k, hk⟩ := (Filter.tendsto_atTop.1 hexp (M + 1)).exists
  have hbound := hM (-(k : ℝ))
  rw [d4ThetaHawkingReflectedConjugateCausalEnergy_eq] at hbound
  have hfirst :
      Real.exp (a * (k : ℝ)) ≤
        Real.exp (-((4 : ℝ) * n + 3 - (q.1 : ℂ).re) * (-(k : ℝ))) +
        Real.exp (-((4 : ℝ) * n + 2 + (q.1 : ℂ).re) * (-(k : ℝ))) := by
    have hnonneg :
        0 ≤ Real.exp
          (-((4 : ℝ) * n + 2 + (q.1 : ℂ).re) * (-(k : ℝ))) := by
      positivity
    dsimp [a]
    rw [show -((4 : ℝ) * n + 3 - (q.1 : ℂ).re) * (-(k : ℝ)) =
      ((4 : ℝ) * n + 3 - (q.1 : ℂ).re) * (k : ℝ) by ring]
    linarith
  linarith

end


end RHTower
