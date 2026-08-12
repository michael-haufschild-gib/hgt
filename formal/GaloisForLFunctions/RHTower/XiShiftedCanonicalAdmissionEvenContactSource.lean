import GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionSingularSourceLaw
import GaloisForLFunctions.RHTower.XiShiftedHankelBoundaryAdaptiveArithmeticSourceLaw

/-!
# Canonical arithmetic source at every even Padé contact

At a first nonzero even Padé contact, the predecessor parity lift of the admitted monic null
polynomial emits exactly that defect through the completed adaptive mixed-amplitude source.  A
positive even defect can fill one terminal Hankel rank, but the following principal block is
necessarily indefinite.  Thus one fixed flat face has no unbounded rank-filled escape.
-/

open Matrix Polynomial

namespace RHTower

noncomputable section

/-- In a positive-semidefinite finite moment block, a represented zero-norm polynomial is
orthogonal to every other represented polynomial. -/
theorem momentInner_eq_zero_of_self_eq_zero_of_hankelPosSemidef
    {s : ℕ → ℝ} {N : ℕ}
    (hpsd : (HTGeometry.momentHankelMatrix s N).PosSemidef)
    {P Q : Polynomial ℝ} (hPdeg : P.natDegree < N) (hQdeg : Q.natDegree < N)
    (hPzero : HTGeometry.momentInner s P P = 0) :
    HTGeometry.momentInner s P Q = 0 := by
  let a : Fin N → ℝ := Polynomial.toFn N P
  let b : Fin N → ℝ := Polynomial.toFn N Q
  have hPof : Polynomial.ofFn N a = P :=
    Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt hPdeg
  have hQof : Polynomial.ofFn N b = Q :=
    Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt hQdeg
  have hquad : a ⬝ᵥ (HTGeometry.momentHankelMatrix s N).mulVec a = 0 := by
    rw [← HTGeometry.momentInner_ofFn_ofFn, hPof, hPzero]
  have hkernel : HTGeometry.momentHankelMatrix s N *ᵥ a = 0 :=
    (hpsd.dotProduct_mulVec_zero_iff a).mp (by simpa using hquad)
  calc
    HTGeometry.momentInner s P Q = HTGeometry.momentInner s Q P :=
      HTGeometry.momentInner_comm _ _ _
    _ = b ⬝ᵥ (HTGeometry.momentHankelMatrix s N).mulVec a := by
      rw [← hPof, ← hQof, HTGeometry.momentInner_ofFn_ofFn]
    _ = 0 := by rw [hkernel, dotProduct_zero]

/-- **Even-contact completed source law.**  If all Padé defects before `2n+2m` vanish, the
completed adaptive packet of the admitted predecessor lift `P X^(m-1)` is exactly
`2(n+m)` times the first even defect. -/
theorem xiShiftedCompletedMomentAggregate_firstEvenContact_eq_evenPadeDefect
    {y : ℝ} (hy : 0 < y) {n m : ℕ} (hm : 0 < m)
    (c : Fin (n + 1) → ℝ) (hlast : c (Fin.last n) ≠ 0)
    (hzero : ∀ k < 2 * n + 2 * m,
      xiShiftedHankelBoundaryPadeDefect y c k = 0) :
    let P := HTGeometry.finiteHankelNullMonicPolynomial c
    let A := P * X ^ (m - 1)
    xiShiftedCompletedMomentAggregate y 2
        (xiShiftedBoundaryAdaptiveMidpointCoefficients 1
          (xiShiftedOddCrossingCoefficientPacket A)) =
      2 * ((n + m : ℕ) : ℝ) *
        xiShiftedHankelBoundaryPadeDefect y c (2 * n + 2 * m) := by
  dsimp only
  let P := HTGeometry.finiteHankelNullMonicPolynomial c
  let A := P * X ^ (m - 1)
  have hzero' : ∀ k < 2 * n + (2 * (m - 1) + 1),
      xiShiftedHankelBoundaryPadeDefect y c k = 0 := by
    intro k hk
    exact hzero k (by omega)
  have hsource :=
    xiShiftedCompletedMomentAggregate_adaptiveNullPacket_eq_adjacentDefects
      hy c hlast hzero'
  dsimp only at hsource
  have hodd : xiShiftedHankelBoundaryPadeDefect y c
      (2 * n + (2 * (m - 1) + 1)) = 0 :=
    hzero _ (by omega)
  rw [hodd, mul_zero, zero_add] at hsource
  have hfactor : n + (m - 1) + 1 = n + m := by omega
  have hindex : 2 * n + (2 * (m - 1) + 1) + 1 = 2 * n + 2 * m := by omega
  simpa only [hfactor, hindex, mul_assoc] using hsource

/-- Literal rational-Gamma-minus-von-Mangoldt form of the even-contact source law.  Admission and
parity lift occur before common-amplitude arithmetic formation. -/
theorem xiShiftedAdaptiveMixedCompletedArithmeticSource_firstEvenContact_eq_evenPadeDefect
    {w : ℝ} (hw : 1 / 2 < w) {n m : ℕ} (hm : 0 < m)
    (c : Fin (n + 1) → ℝ) (hlast : c (Fin.last n) ≠ 0)
    (hzero : ∀ k < 2 * n + 2 * m,
      xiShiftedHankelBoundaryPadeDefect (w ^ 2) c k = 0) :
    let P := HTGeometry.finiteHankelNullMonicPolynomial c
    xiShiftedAdaptiveMixedCompletedArithmeticSource w (P * X ^ (m - 1)) =
      2 * ((n + m : ℕ) : ℝ) *
        xiShiftedHankelBoundaryPadeDefect (w ^ 2) c (2 * n + 2 * m) := by
  dsimp only
  have hsource :=
    xiShiftedCompletedMomentAggregate_firstEvenContact_eq_evenPadeDefect
      (sq_pos_of_pos (by linarith : 0 < w)) hm c hlast hzero
  dsimp only at hsource
  rw [xiShiftedCompletedMomentAggregate_adaptiveOddPacket_eq_arithmeticSource hw] at hsource
  exact hsource

/-- **Even-contact one-block capacity.**  A nonzero first even defect may fill the current
terminal rank, but the next principal Hankel block cannot be positive semidefinite. -/
theorem xiShiftedMomentHankelMatrix_succ_not_posSemidef_of_first_even_contact
    {y : ℝ} {n m : ℕ} (hm : 0 < m) (c : Fin (n + 1) → ℝ)
    (hlast : c (Fin.last n) ≠ 0)
    (hzero : ∀ k < 2 * n + 2 * m,
      xiShiftedHankelBoundaryPadeDefect y c k = 0)
    (hfirst : xiShiftedHankelBoundaryPadeDefect y c (2 * n + 2 * m) ≠ 0) :
    ¬ (xiShiftedMomentHankelMatrix y (n + m + 2)).PosSemidef := by
  intro hpsd
  let P := HTGeometry.finiteHankelNullMonicPolynomial c
  let U := P * X ^ (m - 1)
  let V := P * X ^ (m + 1)
  have hP : P.Monic := HTGeometry.finiteHankelNullMonicPolynomial_monic c hlast
  have hPdeg : P.natDegree = n :=
    HTGeometry.finiteHankelNullMonicPolynomial_natDegree c hlast
  have hUdeg : U.natDegree < n + m + 2 := by
    dsimp only [U]
    rw [hP.natDegree_mul (Polynomial.monic_X_pow (m - 1)), hPdeg,
      Polynomial.natDegree_X_pow]
    omega
  have hVdeg : V.natDegree < n + m + 2 := by
    dsimp only [V]
    rw [hP.natDegree_mul (Polynomial.monic_X_pow (m + 1)), hPdeg,
      Polynomial.natDegree_X_pow]
    omega
  have hzero' : ∀ k < 2 * n + (2 * (m - 1) + 1),
      xiShiftedHankelBoundaryPadeDefect y c k = 0 := by
    intro k hk
    exact hzero k (by omega)
  have hUU : HTGeometry.momentInner
      (fun k => (xiShiftedReciprocalMoment y k).re) U U = 0 := by
    simpa only [U, P] using
      (momentInner_liftedNullPair_eq_zero_of_odd_contact
        (y := y) (n := n) (m := m - 1) (i := m - 1) (j := m - 1)
        c hlast hzero' (by omega))
  have hpoly : U * V = (P * X ^ m) ^ 2 := by
    dsimp only [U, V]
    calc
      (P * X ^ (m - 1)) * (P * X ^ (m + 1)) =
          P ^ 2 * (X ^ (m - 1) * X ^ (m + 1)) := by ring
      _ = P ^ 2 * X ^ ((m - 1) + (m + 1)) := by
        congr 1
        exact (pow_add X (m - 1) (m + 1)).symm
      _ = P ^ 2 * X ^ (2 * m) := by
        rw [show (m - 1) + (m + 1) = 2 * m by omega]
      _ = P ^ 2 * (X ^ m * X ^ m) := by
        rw [show 2 * m = m + m by omega, pow_add]
      _ = (P * X ^ m) ^ 2 := by ring
  have hUV : HTGeometry.momentInner
      (fun k => (xiShiftedReciprocalMoment y k).re) U V =
        xiShiftedHankelBoundaryPadeDefect y c (2 * n + 2 * m) := by
    have heven := xiShiftedHankelBoundaryPadeDefect_first_even_eq_liftedSquare
      c hlast hm hzero
    rw [HTGeometry.momentInner_def]
    rw [hpoly]
    exact heven.symm
  change (HTGeometry.momentHankelMatrix
    (fun k => (xiShiftedReciprocalMoment y k).re) (n + m + 2)).PosSemidef at hpsd
  have hforced := momentInner_eq_zero_of_self_eq_zero_of_hankelPosSemidef
    hpsd hUdeg hVdeg hUU
  exact hfirst (hUV.symm.trans hforced)

/-- The actual inverse-Hankel canonical admission obeys the all-even-contact arithmetic source
law without a posterior normalization choice. -/
theorem xiShiftedAdaptiveMixedCompletedArithmeticSource_canonicalAdmission_firstEvenContact
    {w : ℝ} (hw : 1 / 2 < w) {n m : ℕ} (hm : 0 < m)
    (hzero : ∀ k < 2 * n + 2 * m,
      xiShiftedHankelBoundaryPadeDefect (w ^ 2)
        (HTGeometry.monicMomentAdmissionVector (xiShiftedRealMomentSequence w) n) k = 0) :
    xiShiftedAdaptiveMixedCompletedArithmeticSource w
        (HTGeometry.monicMomentAdmissionPolynomial (xiShiftedRealMomentSequence w) n *
          X ^ (m - 1)) =
      2 * ((n + m : ℕ) : ℝ) *
        xiShiftedHankelBoundaryPadeDefect (w ^ 2)
          (HTGeometry.monicMomentAdmissionVector (xiShiftedRealMomentSequence w) n)
          (2 * n + 2 * m) := by
  let c := HTGeometry.monicMomentAdmissionVector (xiShiftedRealMomentSequence w) n
  have hlast : c (Fin.last n) ≠ 0 := by simp [c]
  have hsource :=
    xiShiftedAdaptiveMixedCompletedArithmeticSource_firstEvenContact_eq_evenPadeDefect
      hw hm c hlast hzero
  rw [finiteHankelNullMonicPolynomial_monicMomentAdmissionVector] at hsource
  exact hsource

/-- **Canonical source/rank/escape trichotomy at first even contact.**  A positive first even
defect is a strictly positive literal arithmetic source, fills exactly one PSD rank, and is then
exhausted by failure of the following principal block. -/
theorem xiShiftedCanonicalAdmission_firstEvenContact_source_pos_rankFill_then_escape
    {w : ℝ} (hw : 1 / 2 < w) {n m : ℕ} (hm : 0 < m)
    (hhead : (xiShiftedMomentHankelMatrix (w ^ 2) n).PosDef)
    (hflat : xiShiftedMomentHankelMatrix (w ^ 2) (n + 1) *ᵥ
      HTGeometry.monicMomentAdmissionVector (xiShiftedRealMomentSequence w) n = 0)
    (hzero : ∀ k < 2 * n + 2 * m,
      xiShiftedHankelBoundaryPadeDefect (w ^ 2)
        (HTGeometry.monicMomentAdmissionVector (xiShiftedRealMomentSequence w) n) k = 0)
    (hfirst : 0 < xiShiftedHankelBoundaryPadeDefect (w ^ 2)
      (HTGeometry.monicMomentAdmissionVector (xiShiftedRealMomentSequence w) n)
      (2 * n + 2 * m)) :
    0 < xiShiftedAdaptiveMixedCompletedArithmeticSource w
        (HTGeometry.monicMomentAdmissionPolynomial (xiShiftedRealMomentSequence w) n *
          X ^ (m - 1)) ∧
      (xiShiftedMomentHankelMatrix (w ^ 2) (n + m + 1)).PosSemidef ∧
      ¬ (xiShiftedMomentHankelMatrix (w ^ 2) (n + m + 2)).PosSemidef := by
  let c := HTGeometry.monicMomentAdmissionVector (xiShiftedRealMomentSequence w) n
  have hlast : c (Fin.last n) ≠ 0 := by simp [c]
  have hsource :=
    xiShiftedAdaptiveMixedCompletedArithmeticSource_canonicalAdmission_firstEvenContact
      hw hm hzero
  have hsourcePos : 0 < xiShiftedAdaptiveMixedCompletedArithmeticSource w
      (HTGeometry.monicMomentAdmissionPolynomial (xiShiftedRealMomentSequence w) n *
        X ^ (m - 1)) := by
    rw [hsource]
    exact mul_pos (mul_pos (by norm_num) (by positivity)) hfirst
  refine ⟨hsourcePos, ?_, ?_⟩
  · exact xiShiftedMomentHankelMatrix_posSemidef_rankOneFilled_of_even_contact
      c hhead hflat hlast hzero hfirst.le
  · exact xiShiftedMomentHankelMatrix_succ_not_posSemidef_of_first_even_contact
      hm c hlast hzero hfirst.ne'

/-- **Automatic finite extension exit.**  No positive singular shifted-Xi Hankel face can remain
positive semidefinite through every higher principal extension.  The infinite Xi divisor forces a
finite first Padé defect.  Odd contact makes the next lifted extension indefinite; even contact
may fill one terminal rank, but its following extension is already indefinite.  No compactness,
local finiteness, or global moment representation is assumed. -/
theorem exists_xiShiftedMomentHankelMatrix_higher_not_posSemidef_of_flatFace
    {y : ℝ} (hy : 0 < y) {n : ℕ} (c : Fin (n + 1) → ℝ)
    (hhead : (xiShiftedMomentHankelMatrix y n).PosDef)
    (hc : xiShiftedMomentHankelMatrix y (n + 1) *ᵥ c = 0)
    (hlast : c (Fin.last n) ≠ 0) :
    ∃ N : ℕ, n + 1 < N ∧
      ¬ (xiShiftedMomentHankelMatrix y N).PosSemidef := by
  obtain ⟨d, hd, hzero, hfirst⟩ :=
    exists_first_xiShiftedHankelBoundaryPadeDefect hy c hhead hc hlast
  rcases Nat.even_or_odd d with ⟨m, hm⟩ | ⟨m, hm⟩
  · have hdform : d = 2 * m := by omega
    have hmpos : 0 < m := by omega
    refine ⟨n + m + 2, by omega, ?_⟩
    apply xiShiftedMomentHankelMatrix_succ_not_posSemidef_of_first_even_contact
      hmpos c hlast
    · intro k hk
      exact hzero k (by omega)
    · simpa only [hdform] using hfirst
  · have hdform : d = 2 * m + 1 := by omega
    refine ⟨n + m + 2, by omega, ?_⟩
    apply xiShiftedMomentHankelMatrix_succ_not_posSemidef_of_first_odd_contact
      c hhead hc hlast
    · intro k hk
      exact hzero k (by omega)
    · simpa only [hdform] using hfirst

end

end RHTower
