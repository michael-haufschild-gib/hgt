import GaloisForLFunctions.RHTower.XiShiftedStrictFrontierAllContactArithmeticSource
import GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionEvenContactSource
import GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionDegreeCenteredArithmeticSource

/-!
# Native adaptive mixed/completed source at every strict-frontier contact

The parity-uniform bilinear contact source can be sharpened to the native completed source algebra.
At even first contact, one admitted null lift enters the diagonal adaptive mixed `P^sharp` source.
At odd first contact, one admitted null lift enters the nondegenerate null-flag completed source;
its unit odd channel prevents zero barycenter from erasing the contact.  Both sources are formed
before rational--Gamma and von-Mangoldt aggregation.

Thus every finite strict-frontier contact has an exact, signed adaptive mixed/completed arithmetic
producer.  No orientation map, fixed linear reporter, numerical estimate, or RH premise enters.
-/

open Matrix Polynomial

namespace RHTower

noncomputable section

/-- Parity-complete native source law at a first Padé contact.  Even contact uses the diagonal
adaptive mixed source.  Odd contact uses the nondegenerate null-flag completion with the same
admitted amplitude in both slots.  In either branch source is formed before arithmetic
aggregation and carries the alternating contact sign. -/
def XiShiftedAdaptiveMixedCompletedFirstContactSourceLaw
    (w : ℝ) (n d : ℕ) (c : Fin (n + 1) → ℝ) : Prop :=
  let P := HTGeometry.finiteHankelNullMonicPolynomial c
  let delta := xiShiftedHankelBoundaryPadeDefect (w ^ 2) c (2 * n + d)
  (∃ r : ℕ, 0 < r ∧ d = 2 * r ∧
      xiShiftedAdaptiveMixedCompletedArithmeticSource w (P * X ^ (r - 1)) =
        ((2 * n + d : ℕ) : ℝ) * delta ∧
      0 < (-1 : ℝ) ^ d *
        xiShiftedAdaptiveMixedCompletedArithmeticSource w (P * X ^ (r - 1))) ∨
    (∃ r : ℕ, d = 2 * r + 1 ∧
      xiShiftedNondegenerateNullFlagCompletedArithmeticSource
          w (n + r) (P * X ^ r) (P * X ^ r) = 2 * delta ∧
      0 < (-1 : ℝ) ^ d *
        xiShiftedNondegenerateNullFlagCompletedArithmeticSource
          w (n + r) (P * X ^ r) (P * X ^ r))

/-- **Parity-complete adaptive mixed/completed arithmetic source law.**  Every positive first
contact is carried by a literal native completed source.  Diagonal adaptive mixed formation covers
even contact.  Nondegenerate null-flag formation covers odd contact, including simple contact,
without a barycenter nonvanishing assumption. -/
theorem xiShifted_adaptiveMixedCompletedFirstContactSourceLaw
    {w : ℝ} (hw : 1 / 2 < w) {n d : ℕ} (hn : 0 < n) (hd : 0 < d)
    (c : Fin (n + 1) → ℝ) (hlast : c (Fin.last n) ≠ 0)
    (hzero : ∀ k < 2 * n + d,
      xiShiftedHankelBoundaryPadeDefect (w ^ 2) c k = 0)
    (hsigned : 0 < (-1 : ℝ) ^ d *
      xiShiftedHankelBoundaryPadeDefect (w ^ 2) c (2 * n + d)) :
    XiShiftedAdaptiveMixedCompletedFirstContactSourceLaw w n d c := by
  dsimp only [XiShiftedAdaptiveMixedCompletedFirstContactSourceLaw]
  rcases Nat.even_or_odd d with ⟨r, hr⟩ | ⟨r, hr⟩
  · have hdform : d = 2 * r := by omega
    have hrpos : 0 < r := by omega
    left
    refine ⟨r, hrpos, hdform, ?_, ?_⟩
    · have hsource :=
        xiShiftedAdaptiveMixedCompletedArithmeticSource_firstEvenContact_eq_evenPadeDefect
          hw hrpos c hlast (by
            intro k hk
            exact hzero k (by omega))
      dsimp only at hsource
      calc
        xiShiftedAdaptiveMixedCompletedArithmeticSource w
            (HTGeometry.finiteHankelNullMonicPolynomial c * X ^ (r - 1)) =
            2 * ((n + r : ℕ) : ℝ) *
              xiShiftedHankelBoundaryPadeDefect (w ^ 2) c (2 * n + 2 * r) :=
          hsource
        _ = ((2 * n + d : ℕ) : ℝ) *
              xiShiftedHankelBoundaryPadeDefect (w ^ 2) c (2 * n + d) := by
          rw [hdform]
          push_cast
          ring
    · have hfactor : 0 < (((2 * n + d : ℕ) : ℝ)) := by positivity
      rw [show xiShiftedAdaptiveMixedCompletedArithmeticSource w
          (HTGeometry.finiteHankelNullMonicPolynomial c * X ^ (r - 1)) =
          ((2 * n + d : ℕ) : ℝ) *
            xiShiftedHankelBoundaryPadeDefect (w ^ 2) c (2 * n + d) by
        have hsource :=
          xiShiftedAdaptiveMixedCompletedArithmeticSource_firstEvenContact_eq_evenPadeDefect
            hw hrpos c hlast (by
              intro k hk
              exact hzero k (by omega))
        dsimp only at hsource
        calc
          _ = 2 * ((n + r : ℕ) : ℝ) *
                xiShiftedHankelBoundaryPadeDefect (w ^ 2) c (2 * n + 2 * r) := hsource
          _ = _ := by rw [hdform]; push_cast; ring]
      calc
        (-1 : ℝ) ^ d *
            (((2 * n + d : ℕ) : ℝ) *
              xiShiftedHankelBoundaryPadeDefect (w ^ 2) c (2 * n + d)) =
            ((2 * n + d : ℕ) : ℝ) *
              ((-1 : ℝ) ^ d *
                xiShiftedHankelBoundaryPadeDefect (w ^ 2) c (2 * n + d)) := by ring
        _ > 0 := mul_pos hfactor hsigned
  · have hdform : d = 2 * r + 1 := by omega
    right
    refine ⟨r, hdform, ?_, ?_⟩
    · have hsource :=
        xiShiftedNondegenerateNullFlagCompletedArithmeticSource_liftedNull_eq_two_mul_firstOddDefect
          (m := r) hw hn c hlast (by
            intro k hk
            exact hzero k (by omega))
          (HTGeometry.finiteHankelNullMonicPolynomial c * X ^ r)
      dsimp only at hsource
      simpa only [hdform] using hsource
    · have hsource :=
        xiShiftedNondegenerateNullFlagCompletedArithmeticSource_liftedNull_eq_two_mul_firstOddDefect
          (m := r) hw hn c hlast (by
            intro k hk
            exact hzero k (by omega))
          (HTGeometry.finiteHankelNullMonicPolynomial c * X ^ r)
      dsimp only at hsource
      rw [hsource]
      calc
        (-1 : ℝ) ^ d *
            (2 * xiShiftedHankelBoundaryPadeDefect (w ^ 2) c
              (2 * n + (2 * r + 1))) =
            2 * ((-1 : ℝ) ^ d *
              xiShiftedHankelBoundaryPadeDefect (w ^ 2) c (2 * n + d)) := by
          rw [hdform]
          ring
        _ > 0 := mul_pos (by norm_num) hsigned

/-- Native adaptive mixed/completed first-contact law at the canonical strict frontier. -/
def XiShiftedStrictFrontierAdaptiveMixedCompletedContactLaw (n : ℕ) : Prop :=
  let y := xiShiftedHigherBlockTerminalFrontier (n + 1)
  let m := n + 2
  let c := xiShiftedStrictFrontierNullVector n
  ∃ d : ℕ, 0 < d ∧
    (∀ k < 2 * m + d, xiShiftedStrictFrontierPadeDefect n k = 0) ∧
    0 < (-1 : ℝ) ^ d * xiShiftedStrictFrontierPadeDefect n (2 * m + d) ∧
    XiShiftedAdaptiveMixedCompletedFirstContactSourceLaw (Real.sqrt y) m d c

/-- Every occupied physical strict frontier has a finite first contact carried by the native
adaptive mixed/completed `P^sharp` source algebra. -/
theorem xiShiftedStrictFrontier_adaptiveMixedCompletedContactLaw
    {n : ℕ} (hne : (xiShiftedHigherBlockFailureSet n).Nonempty)
    (hstrict : xiShiftedHigherBlockTerminalFrontier n <
      xiShiftedHigherBlockTerminalFrontier (n + 1))
    (hphysical : 1 / 4 < xiShiftedHigherBlockTerminalFrontier (n + 1)) :
    XiShiftedStrictFrontierAdaptiveMixedCompletedContactLaw n := by
  let y := xiShiftedHigherBlockTerminalFrontier (n + 1)
  let m := n + 2
  let c := xiShiftedStrictFrontierNullVector n
  have hold := xiShiftedStrictFrontier_finiteArithmeticContactLaw hne hstrict hphysical
  dsimp only [XiShiftedStrictFrontierFiniteArithmeticContactLaw] at hold
  obtain ⟨d, hd, hzero, hsigned, _⟩ := hold
  have hy0 : 0 ≤ y := by
    dsimp only [y]
    linarith
  have hsq : (Real.sqrt y) ^ 2 = y := Real.sq_sqrt hy0
  have hsqrt : 1 / 2 < Real.sqrt y := by
    have hsqrt0 := Real.sqrt_nonneg y
    change 1 / 4 < y at hphysical
    nlinarith
  have hlast : c (Fin.last m) ≠ 0 := by
    simp [c, xiShiftedStrictFrontierNullVector, m]
  have hzero' : ∀ k < 2 * m + d,
      xiShiftedHankelBoundaryPadeDefect ((Real.sqrt y) ^ 2) c k = 0 := by
    intro k hk
    rw [hsq]
    simpa only [m, c, xiShiftedStrictFrontierPadeDefect, y,
      xiShiftedStrictFrontierNullVector] using hzero k hk
  have hsigned' : 0 < (-1 : ℝ) ^ d *
      xiShiftedHankelBoundaryPadeDefect ((Real.sqrt y) ^ 2) c (2 * m + d) := by
    rw [hsq]
    simpa only [m, c, xiShiftedStrictFrontierPadeDefect, y,
      xiShiftedStrictFrontierNullVector] using hsigned
  have hsource := xiShifted_adaptiveMixedCompletedFirstContactSourceLaw
    hsqrt (by omega : 0 < m) hd c hlast hzero' hsigned'
  dsimp only [XiShiftedStrictFrontierAdaptiveMixedCompletedContactLaw]
  exact ⟨d, hd, hzero, hsigned, hsource⟩

/-- False-RH alternative in native adaptive mixed/completed source coordinates. -/
def XiShiftedCofinalAdaptiveMixedCompletedContactPhase : Prop :=
  ∀ A : ℝ, ∃ n : ℕ,
    (xiShiftedHigherBlockFailureSet n).Nonempty ∧
      A < xiShiftedHigherBlockTerminalFrontier n ∧
      xiShiftedHigherBlockTerminalFrontier n <
        xiShiftedHigherBlockTerminalFrontier (n + 1) ∧
      1 / 4 < xiShiftedHigherBlockTerminalFrontier (n + 1) ∧
      XiShiftedStrictFrontierAdaptiveMixedCompletedContactLaw n

theorem xiShiftedCofinalAdaptiveMixedCompletedContactPhase_of_not_riemannHypothesis
    (hnot : ¬RiemannHypothesis) :
    XiShiftedCofinalAdaptiveMixedCompletedContactPhase := by
  intro A
  obtain ⟨n, hne, hA, hstrict, _⟩ :=
    exists_cofinal_sourceAdaptive_frontierCertificate_of_not_riemannHypothesis hnot
      (max A (1 / 4))
  have hA' : A < xiShiftedHigherBlockTerminalFrontier n :=
    lt_of_le_of_lt (le_max_left _ _) hA
  have hphysical : 1 / 4 < xiShiftedHigherBlockTerminalFrontier (n + 1) :=
    lt_trans (lt_of_le_of_lt (le_max_right _ _) hA) hstrict
  exact ⟨n, hne, hA', hstrict, hphysical,
    xiShiftedStrictFrontier_adaptiveMixedCompletedContactLaw hne hstrict hphysical⟩

theorem not_xiShiftedCofinalAdaptiveMixedCompletedContactPhase_of_riemannHypothesis
    (hRH : RiemannHypothesis) :
    ¬XiShiftedCofinalAdaptiveMixedCompletedContactPhase := by
  intro hphase
  obtain ⟨n, hne, _⟩ := hphase 0
  rw [xiShiftedHigherBlockFailureSet_eq_empty_of_riemannHypothesis hRH n] at hne
  exact Set.not_nonempty_empty hne

/-- Premise-free phase closure with the requested native adaptive mixed/completed source. -/
theorem riemannHypothesis_iff_not_xiShiftedCofinalAdaptiveMixedCompletedContactPhase :
    RiemannHypothesis ↔ ¬XiShiftedCofinalAdaptiveMixedCompletedContactPhase := by
  constructor
  · exact not_xiShiftedCofinalAdaptiveMixedCompletedContactPhase_of_riemannHypothesis
  · intro hnotPhase
    by_contra hnotRH
    exact hnotPhase
      (xiShiftedCofinalAdaptiveMixedCompletedContactPhase_of_not_riemannHypothesis hnotRH)

end

end RHTower
