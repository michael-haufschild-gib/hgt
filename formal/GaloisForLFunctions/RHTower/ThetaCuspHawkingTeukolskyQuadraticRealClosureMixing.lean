import GaloisForLFunctions.RHTower.ThetaCuspHawkingTopologicalDarbouxAlgebraicallySpecialCrossing
import GaloisForLFunctions.RHTower.CentralReciprocalMoments

/-!
# Real closure of quadratic theta--Teukolsky return sectors

The local quadratic cusp weight is twice the Eisenstein scattering parameter, hence equals the
Xi divisor coordinate `rho`. Functional-equation covariance closes it under `rho ↦ 1-rho`, while
reality of the Einstein field closes it under complex conjugation.

At a nonreal Xi divisor the theta pair always has two members. Its joint functional-equation and
Schwarz closure has two members exactly on the critical line and four members off it. Therefore a
tilted quadratic return cannot remain in a real two-sector theta block: every finite real,
theta-closed return packet containing it has at least four distinct weights. The controlled AIME
cross-branch numerator is nonzero on all four divisor sectors for every nonzero seed amplitude.
-/

open Complex

noncomputable section

namespace RHTower

/-- Doubled Eisenstein weight carried by the local quadratic chiral return. -/
def d4ThetaTeukolskyQuadraticReturnWeight (q : XiZeroCopy) : ℂ :=
  2 * thetaCuspHawkingOpticalCuspResonanceParameter (xiSpectralPoint q)

/-- Weight doubling removes the half-weight alias and recovers the Xi divisor coordinate. -/
theorem d4ThetaTeukolskyQuadraticReturnWeight_eq (q : XiZeroCopy) :
    d4ThetaTeukolskyQuadraticReturnWeight q = (q.1 : ℂ) := by
  rw [d4ThetaTeukolskyQuadraticReturnWeight,
    thetaCuspHawkingOpticalCuspResonanceParameter]
  unfold xiSpectralPoint
  ring_nf
  rw [Complex.I_sq]
  ring

/-- Functional-equation pair of quadratic return weights. -/
def d4ThetaTeukolskyQuadraticThetaPair (q : XiZeroCopy) : Finset ℂ :=
  {d4ThetaTeukolskyQuadraticReturnWeight q,
    d4ThetaTeukolskyQuadraticReturnWeight (xiZeroCopyReflectEquiv q)}

/-- Minimal weight packet closed under both functional equation and Lorentzian reality. -/
def d4ThetaTeukolskyQuadraticRealClosure (q : XiZeroCopy) : Finset ℂ :=
  {d4ThetaTeukolskyQuadraticReturnWeight q,
    d4ThetaTeukolskyQuadraticReturnWeight (xiZeroCopyReflectEquiv q),
    d4ThetaTeukolskyQuadraticReturnWeight (xiZeroCopyConjEquiv q),
    d4ThetaTeukolskyQuadraticReturnWeight
      (xiZeroCopyReflectEquiv (xiZeroCopyConjEquiv q))}

lemma d4ThetaTeukolskyQuadraticThetaPair_eq (q : XiZeroCopy) :
    d4ThetaTeukolskyQuadraticThetaPair q =
      {(q.1 : ℂ), 1 - (q.1 : ℂ)} := by
  rw [d4ThetaTeukolskyQuadraticThetaPair,
    d4ThetaTeukolskyQuadraticReturnWeight_eq,
    d4ThetaTeukolskyQuadraticReturnWeight_eq,
    xiZeroCopyReflectEquiv_rho]

lemma d4ThetaTeukolskyQuadraticRealClosure_eq (q : XiZeroCopy) :
    d4ThetaTeukolskyQuadraticRealClosure q =
      {(q.1 : ℂ), 1 - (q.1 : ℂ),
        starRingEnd ℂ (q.1 : ℂ), 1 - starRingEnd ℂ (q.1 : ℂ)} := by
  rw [d4ThetaTeukolskyQuadraticRealClosure,
    d4ThetaTeukolskyQuadraticReturnWeight_eq,
    d4ThetaTeukolskyQuadraticReturnWeight_eq,
    d4ThetaTeukolskyQuadraticReturnWeight_eq,
    d4ThetaTeukolskyQuadraticReturnWeight_eq,
    xiZeroCopyReflectEquiv_rho,
    xiZeroCopyReflectEquiv_rho]
  have hconj := deningerDivisorThetaEigen_conjEquiv q
  change ((xiZeroCopyConjEquiv q).1 : ℂ) =
    (starRingEnd ℂ) (q.1 : ℂ) at hconj
  rw [hconj]

private lemma d4XiRho_conj_ne_self (q : XiZeroCopy) :
    starRingEnd ℂ (q.1 : ℂ) ≠ (q.1 : ℂ) := by
  intro h
  have him := congrArg Complex.im h
  simp at him
  exact xi_divisor_support_im_ne_zero q.1 (by linarith)

private lemma d4XiRho_ne_reflect (q : XiZeroCopy) :
    (q.1 : ℂ) ≠ 1 - (q.1 : ℂ) := by
  intro h
  have him := congrArg Complex.im h
  simp at him
  exact xi_divisor_support_im_ne_zero q.1 (by linarith)

private lemma d4XiRho_conj_ne_reflect_of_tilted (q : XiZeroCopy)
    (htilt : (q.1 : ℂ).re ≠ 1 / 2) :
    starRingEnd ℂ (q.1 : ℂ) ≠ 1 - (q.1 : ℂ) := by
  intro h
  have hre := congrArg Complex.re h
  simp at hre
  exact htilt (by linarith)

private lemma d4XiRho_reflectConj_ne_self_of_tilted (q : XiZeroCopy)
    (htilt : (q.1 : ℂ).re ≠ 1 / 2) :
    1 - starRingEnd ℂ (q.1 : ℂ) ≠ (q.1 : ℂ) := by
  intro h
  have hre := congrArg Complex.re h
  simp at hre
  exact htilt (by linarith)

private lemma d4XiRho_reflectConj_ne_reflect (q : XiZeroCopy) :
    1 - starRingEnd ℂ (q.1 : ℂ) ≠ 1 - (q.1 : ℂ) := by
  intro h
  have him := congrArg Complex.im h
  simp at him
  exact xi_divisor_support_im_ne_zero q.1 (by linarith)

private lemma d4XiRho_reflectConj_ne_conj (q : XiZeroCopy) :
    1 - starRingEnd ℂ (q.1 : ℂ) ≠ starRingEnd ℂ (q.1 : ℂ) := by
  intro h
  have him := congrArg Complex.im h
  have hre := congrArg Complex.re h
  simp at him hre
  exact xi_divisor_support_im_ne_zero q.1 (by linarith)

/-- The functional-equation pair is nondegenerate at every Xi divisor. -/
theorem card_d4ThetaTeukolskyQuadraticThetaPair (q : XiZeroCopy) :
    (d4ThetaTeukolskyQuadraticThetaPair q).card = 2 := by
  rw [d4ThetaTeukolskyQuadraticThetaPair_eq]
  simp [d4XiRho_ne_reflect q]

/-- A tilted quadratic return has four distinct FE--Schwarz weights. -/
theorem card_d4ThetaTeukolskyQuadraticRealClosure_of_tilted
    (q : XiZeroCopy) (htilt : (q.1 : ℂ).re ≠ 1 / 2) :
    (d4ThetaTeukolskyQuadraticRealClosure q).card = 4 := by
  rw [d4ThetaTeukolskyQuadraticRealClosure_eq]
  rw [Finset.card_insert_of_notMem]
  · rw [Finset.card_insert_of_notMem]
    · rw [Finset.card_insert_of_notMem]
      · simp
      · simp only [Finset.mem_singleton]
        exact (d4XiRho_reflectConj_ne_conj q).symm
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨(d4XiRho_conj_ne_reflect_of_tilted q htilt).symm,
        (d4XiRho_reflectConj_ne_reflect q).symm⟩
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨d4XiRho_ne_reflect q,
      (d4XiRho_conj_ne_self q).symm,
      (d4XiRho_reflectConj_ne_self_of_tilted q htilt).symm⟩

/-- On the critical line Schwarz conjugation adds no sector beyond theta reflection. -/
theorem d4ThetaTeukolskyQuadraticRealClosure_eq_thetaPair_of_onLine
    (q : XiZeroCopy) (hline : (q.1 : ℂ).re = 1 / 2) :
    d4ThetaTeukolskyQuadraticRealClosure q =
      d4ThetaTeukolskyQuadraticThetaPair q := by
  have hconj : starRingEnd ℂ (q.1 : ℂ) = 1 - (q.1 : ℂ) := by
    apply Complex.ext
    · simp [hline]
      norm_num
    · simp
  have hsub : 1 - (1 - (q.1 : ℂ)) = (q.1 : ℂ) := by ring
  ext z
  simp only [d4ThetaTeukolskyQuadraticRealClosure_eq,
    d4ThetaTeukolskyQuadraticThetaPair_eq, hconj, hsub, Finset.mem_insert,
    Finset.mem_singleton]
  tauto

/-- Two-channel real closure is equivalent to critical-line placement. -/
theorem d4ThetaTeukolskyQuadraticRealClosure_card_eq_two_iff
    (q : XiZeroCopy) :
    (d4ThetaTeukolskyQuadraticRealClosure q).card = 2 ↔
      (q.1 : ℂ).re = 1 / 2 := by
  constructor
  · intro hcard
    by_contra htilt
    rw [card_d4ThetaTeukolskyQuadraticRealClosure_of_tilted q htilt] at hcard
    norm_num at hcard
  · intro hline
    rw [d4ThetaTeukolskyQuadraticRealClosure_eq_thetaPair_of_onLine q hline,
      card_d4ThetaTeukolskyQuadraticThetaPair]

/-- Reality forces a tilted return to acquire a weight outside its theta pair. -/
theorem d4ThetaTeukolsky_tilted_realClosure_forces_externalWeight
    (q : XiZeroCopy) (htilt : (q.1 : ℂ).re ≠ 1 / 2)
    (support : Set ℂ)
    (hq : d4ThetaTeukolskyQuadraticReturnWeight q ∈ support)
    (hreal : ∀ z ∈ support, starRingEnd ℂ z ∈ support) :
    ∃ z ∈ support, z ∉ d4ThetaTeukolskyQuadraticThetaPair q := by
  have hrho : (q.1 : ℂ) ∈ support := by
    rw [← d4ThetaTeukolskyQuadraticReturnWeight_eq q]
    exact hq
  refine ⟨starRingEnd ℂ (q.1 : ℂ), hreal _ hrho, ?_⟩
  rw [d4ThetaTeukolskyQuadraticThetaPair_eq]
  simp [d4XiRho_conj_ne_self q,
    d4XiRho_conj_ne_reflect_of_tilted q htilt]

/-- Joint theta and real closure contains the canonical FE--Schwarz packet. -/
theorem d4ThetaTeukolskyQuadraticRealClosure_subset_closedPacket
    (q : XiZeroCopy) (support : Finset ℂ)
    (hq : d4ThetaTeukolskyQuadraticReturnWeight q ∈ support)
    (htheta : ∀ z ∈ support, 1 - z ∈ support)
    (hreal : ∀ z ∈ support, starRingEnd ℂ z ∈ support) :
    d4ThetaTeukolskyQuadraticRealClosure q ⊆ support := by
  have hrho : (q.1 : ℂ) ∈ support := by
    rw [← d4ThetaTeukolskyQuadraticReturnWeight_eq q]
    exact hq
  have hreflect : 1 - (q.1 : ℂ) ∈ support := htheta _ hrho
  have hconj : starRingEnd ℂ (q.1 : ℂ) ∈ support := hreal _ hrho
  have hreflectConj : 1 - starRingEnd ℂ (q.1 : ℂ) ∈ support :=
    htheta _ hconj
  intro z hz
  rw [d4ThetaTeukolskyQuadraticRealClosure_eq] at hz
  simp only [Finset.mem_insert, Finset.mem_singleton] at hz
  rcases hz with rfl | rfl | rfl | rfl
  · exact hrho
  · exact hreflect
  · exact hconj
  · exact hreflectConj

/-- Every finite real, theta-closed tilted return packet has at least four weights. -/
theorem d4ThetaTeukolsky_tilted_closedPacket_card_ge_four
    (q : XiZeroCopy) (htilt : (q.1 : ℂ).re ≠ 1 / 2)
    (support : Finset ℂ)
    (hq : d4ThetaTeukolskyQuadraticReturnWeight q ∈ support)
    (htheta : ∀ z ∈ support, 1 - z ∈ support)
    (hreal : ∀ z ∈ support, starRingEnd ℂ z ∈ support) :
    4 ≤ support.card := by
  have hsub := d4ThetaTeukolskyQuadraticRealClosure_subset_closedPacket
    q support hq htheta hreal
  have hcard := Finset.card_le_card hsub
  rw [card_d4ThetaTeukolskyQuadraticRealClosure_of_tilted q htilt] at hcard
  exact hcard

/-- Controlled cross-branch AIME return is nonzero on the complete FE--Schwarz quartet. -/
theorem d4AIME_feSchwarzQuartet_numerators_ne_zero
    (amplitude : ℂ) (ha : amplitude ≠ 0)
    (q : XiZeroCopy) :
    d4FundamentalQNMCrossBranchAIMENumerator amplitude (xiSpectralPoint q) ≠ 0 ∧
    d4FundamentalQNMCrossBranchAIMENumerator amplitude
        (xiSpectralPoint (xiZeroCopyReflectEquiv q)) ≠ 0 ∧
    d4FundamentalQNMCrossBranchAIMENumerator amplitude
        (xiSpectralPoint (xiZeroCopyConjEquiv q)) ≠ 0 ∧
    d4FundamentalQNMCrossBranchAIMENumerator amplitude
        (xiSpectralPoint
          (xiZeroCopyReflectEquiv (xiZeroCopyConjEquiv q))) ≠ 0 := by
  exact ⟨
    (d4FundamentalQNMCrossBranchAIMENumerator_xi_ne_zero_iff amplitude q).2 ha,
    (d4FundamentalQNMCrossBranchAIMENumerator_xi_ne_zero_iff amplitude
      (xiZeroCopyReflectEquiv q)).2 ha,
    (d4FundamentalQNMCrossBranchAIMENumerator_xi_ne_zero_iff amplitude
      (xiZeroCopyConjEquiv q)).2 ha,
    (d4FundamentalQNMCrossBranchAIMENumerator_xi_ne_zero_iff amplitude
      (xiZeroCopyReflectEquiv (xiZeroCopyConjEquiv q))).2 ha⟩

/-- Tilt makes all four distinct quadratic weights carry nonzero controlled AIME return. -/
theorem d4AIME_tilted_realClosure_card_and_numerators_ne_zero
    (amplitude : ℂ) (ha : amplitude ≠ 0)
    (q : XiZeroCopy) (htilt : (q.1 : ℂ).re ≠ 1 / 2) :
    (d4ThetaTeukolskyQuadraticRealClosure q).card = 4 ∧
    d4FundamentalQNMCrossBranchAIMENumerator amplitude (xiSpectralPoint q) ≠ 0 ∧
    d4FundamentalQNMCrossBranchAIMENumerator amplitude
        (xiSpectralPoint (xiZeroCopyReflectEquiv q)) ≠ 0 ∧
    d4FundamentalQNMCrossBranchAIMENumerator amplitude
        (xiSpectralPoint (xiZeroCopyConjEquiv q)) ≠ 0 ∧
    d4FundamentalQNMCrossBranchAIMENumerator amplitude
        (xiSpectralPoint
          (xiZeroCopyReflectEquiv (xiZeroCopyConjEquiv q))) ≠ 0 := by
  exact ⟨card_d4ThetaTeukolskyQuadraticRealClosure_of_tilted q htilt,
    d4AIME_feSchwarzQuartet_numerators_ne_zero amplitude ha q⟩

/-- Starobinsky crossing determinant after adjoining the Schwarz-conjugate theta pair. -/
def d4BMXiThetaMirrorStarobinskyRealClosureProduct
    (n : ℕ) (M : ℝ) (q : XiZeroCopy) : ℝ :=
  d4BMXiThetaMirrorStarobinskyCrossingProduct n M q ^ (2 : ℕ)

/-- Full FE--Schwarz closure turns the signed two-sector product into a square. -/
theorem d4BMXiThetaMirrorStarobinskyRealClosureProduct_nonnegative
    (n : ℕ) (M : ℝ) (q : XiZeroCopy) :
    0 ≤ d4BMXiThetaMirrorStarobinskyRealClosureProduct n M q := by
  exact sq_nonneg _

/-- At a tilted midpoint, the two-sector product is negative but its real closure is positive. -/
theorem d4BMXiThetaMirrorStarobinsky_midpoint_sign_repaired_by_realClosure
    (n : ℕ) (q : XiZeroCopy) (htilt : (q.1 : ℂ).re ≠ 1 / 2) :
    d4BMXiThetaMirrorStarobinskyCrossingProduct n
          (d4BMXiThetaMirrorAlgebraicallySpecialMassMidpoint n q) q < 0 ∧
      0 < d4BMXiThetaMirrorStarobinskyRealClosureProduct n
        (d4BMXiThetaMirrorAlgebraicallySpecialMassMidpoint n q) q := by
  have hneg := d4BMXiThetaMirrorStarobinskyCrossingProduct_midpoint_neg_of_tilted
    n q htilt
  refine ⟨hneg, ?_⟩
  rw [d4BMXiThetaMirrorStarobinskyRealClosureProduct]
  exact sq_pos_of_ne_zero (ne_of_lt hneg)

end RHTower
