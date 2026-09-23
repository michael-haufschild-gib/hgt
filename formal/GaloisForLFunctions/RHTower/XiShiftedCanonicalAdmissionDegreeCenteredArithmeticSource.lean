import GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionAdaptiveArithmeticSourceDegreeConnection
import GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionBilinearContactSource
import GaloisForLFunctions.RHTower.XiShiftedHankelBoundaryPadeContactParity
import GaloisForLFunctions.RHTower.XiShiftedHankelCassiniSourceJet
import GaloisForLFunctions.HTGeometry.ColumnDegreeDeterminant
import GaloisForLFunctions.HTGeometry.DegreeCenteredOrthogonalSourceJacobiHistory

/-!
# Degree-centered arithmetic source at a canonical singular face

The usual adaptive shear uses `X P' + P` and therefore lands on two adjacent Padé defects at a
flat face: first odd extension plus first even successor.  Centering Euler at admitted degree,
`X P' - n P`, cancels the even top coefficient before arithmetic formation.

For current monic null admission `P`, resulting literal rational--Gamma-minus-von-Mangoldt source
is exactly `-2 * P.nextCoeff` times canonical odd monic remainder.  No tangency hypothesis,
orientation map, post-aggregation reporter, or positivity of a following block occurs.  Under
negative canonical barycenter, positivity of this one source-first producer is exactly positive
extension orientation and therefore excludes a right-hand first crossing.
-/

open Filter Matrix Polynomial Set Topology
open scoped BigOperators

namespace RHTower

noncomputable section

def xiShiftedBoundaryDegreeCenteredEuler
    (n : ℕ) (A : Polynomial ℝ) : Polynomial ℝ :=
  X * A.derivative - (n : ℝ) • A

def xiShiftedBoundaryDegreeCenteredShearPolynomial
    (n : ℕ) (A : Polynomial ℝ) : Polynomial ℝ :=
  (X * A) * (X * xiShiftedBoundaryDegreeCenteredEuler n A)

def xiShiftedDegreeCenteredCompletedArithmeticSource
    (w : ℝ) (n : ℕ) (A : Polynomial ℝ) : ℝ :=
  2 * xiShiftedPolynomialCompletedArithmeticSource w
    (xiShiftedBoundaryDegreeCenteredShearPolynomial n A)

theorem xiShiftedDegreeCenteredCompletedArithmeticSource_eq_momentFunctional
    {w : ℝ} (hw : 1 / 2 < w) (n : ℕ) (A : Polynomial ℝ) :
    xiShiftedDegreeCenteredCompletedArithmeticSource w n A =
      2 * HTGeometry.momentFunctional (xiShiftedRealMomentSequence w)
        (xiShiftedBoundaryDegreeCenteredShearPolynomial n A) := by
  rw [xiShiftedDegreeCenteredCompletedArithmeticSource,
    xiShiftedPolynomialCompletedArithmeticSource_eq_momentFunctional hw]

/-- Degree-centered shifted-Xi shear is the universal degree-centered orthogonal source when its
amplitude is the admitted monic orthogonal polynomial. -/
theorem xiShiftedBoundaryDegreeCenteredShearPolynomial_monicOrtho
    (s : ℕ → ℝ) (n : ℕ) :
    xiShiftedBoundaryDegreeCenteredShearPolynomial n (HTGeometry.monicOrtho s n) =
      HTGeometry.degreeCenteredOrthoSourcePolynomial s n := by
  rfl

/-- **Admission-sensitive completed source law.**  On a positive moment chamber, literal
rational--Gamma-minus-von-Mangoldt degree-centered source is exactly twice admitted norm times
causal Jacobi history.  Formation precedes every observation or reflection aggregation. -/
theorem xiShiftedDegreeCenteredCompletedArithmeticSource_eq_norm_mul_jacobiHistory
    {w : ℝ} (hw : 1 / 2 < w) {n : ℕ} (hn : 0 < n)
    (h : HTGeometry.PositiveMomentForm (xiShiftedRealMomentSequence w)) :
    xiShiftedDegreeCenteredCompletedArithmeticSource w n
        (HTGeometry.monicOrtho (xiShiftedRealMomentSequence w) n) =
      2 * HTGeometry.monicOrthoNormSq (xiShiftedRealMomentSequence w) n *
        HTGeometry.degreeCenteredOrthoJacobiHistory
          (xiShiftedRealMomentSequence w) n := by
  rw [xiShiftedDegreeCenteredCompletedArithmeticSource_eq_momentFunctional hw,
    xiShiftedBoundaryDegreeCenteredShearPolynomial_monicOrtho,
    HTGeometry.momentFunctional_degreeCenteredOrthoSourcePolynomial_eq_jacobiHistory h hn]
  ring

theorem xiShiftedBoundaryDegreeCenteredShearPolynomial_eq_adaptive_sub_square
    (n : ℕ) (A : Polynomial ℝ) :
    xiShiftedBoundaryDegreeCenteredShearPolynomial n A =
      xiShiftedBoundaryAdaptiveShearPolynomial A -
        (n + 1 : ℝ) • ((X * A) ^ (2 : ℕ)) := by
  simp only [xiShiftedBoundaryDegreeCenteredShearPolynomial,
    xiShiftedBoundaryDegreeCenteredEuler,
    xiShiftedBoundaryAdaptiveShearPolynomial,
    xiShiftedBoundaryShiftedEuler, Polynomial.smul_eq_C_mul]
  rw [map_add, map_one]
  ring

theorem xiShiftedDegreeCenteredCompletedArithmeticSource_eq_adaptive_sub_square
    {w : ℝ} (hw : 1 / 2 < w) (n : ℕ) (A : Polynomial ℝ) :
    xiShiftedDegreeCenteredCompletedArithmeticSource w n A =
      xiShiftedAdaptiveMixedCompletedArithmeticSource w A -
        2 * (n + 1 : ℝ) *
          xiShiftedPolynomialCompletedArithmeticSource w ((X * A) ^ (2 : ℕ)) := by
  rw [xiShiftedDegreeCenteredCompletedArithmeticSource_eq_momentFunctional hw,
    xiShiftedPolynomialCompletedArithmeticSource_eq_momentFunctional hw,
    xiShiftedBoundaryDegreeCenteredShearPolynomial_eq_adaptive_sub_square,
    HTGeometry.momentFunctional_sub, HTGeometry.momentFunctional_smul,
    ← two_mul_xiShiftedAdaptiveShear_eq_arithmeticSource hw]
  change
    2 * (HTGeometry.momentInner (xiShiftedRealMomentSequence w)
        (X * A) (X * xiShiftedBoundaryShiftedEuler 1 A) -
      (n + 1 : ℝ) *
        HTGeometry.momentFunctional (xiShiftedRealMomentSequence w) ((X * A) ^ (2 : ℕ))) =
      2 * HTGeometry.momentInner (xiShiftedRealMomentSequence w)
          (X * A) (X * xiShiftedBoundaryShiftedEuler 1 A) -
        2 * (n + 1 : ℝ) *
          HTGeometry.momentFunctional (xiShiftedRealMomentSequence w) ((X * A) ^ (2 : ℕ))
  ring

theorem natDegree_xiShiftedBoundaryDegreeCenteredEuler_le
    {n : ℕ} (hn : 0 < n) {A : Polynomial ℝ}
    (hAdeg : A.natDegree = n) :
    (xiShiftedBoundaryDegreeCenteredEuler n A).natDegree ≤ n - 1 := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro k hk
  have hnk : n ≤ k := by omega
  rcases k with _ | k
  · omega
  rw [xiShiftedBoundaryDegreeCenteredEuler, Polynomial.coeff_sub,
    Polynomial.coeff_X_mul, Polynomial.coeff_derivative,
    Polynomial.coeff_smul]
  by_cases heq : k + 1 = n
  · rw [← heq]
    push_cast
    ring
  · have hlt : n < k + 1 := by omega
    have hzero : A.coeff (k + 1) = 0 := by
      apply Polynomial.coeff_eq_zero_of_natDegree_lt
      rwa [hAdeg]
    rw [hzero]
    ring

theorem coeff_xiShiftedBoundaryDegreeCenteredEuler_top
    {n : ℕ} (hn : 0 < n) {A : Polynomial ℝ}
    (hAdeg : A.natDegree = n) :
    (xiShiftedBoundaryDegreeCenteredEuler n A).coeff (n - 1) =
      -A.nextCoeff := by
  have hcoeff : A.coeff (n - 1) = A.nextCoeff := by
    rw [Polynomial.nextCoeff_of_natDegree_pos (by rwa [hAdeg]), hAdeg]
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  rcases m with _ | m
  · simpa [xiShiftedBoundaryDegreeCenteredEuler] using hcoeff
  · rw [xiShiftedBoundaryDegreeCenteredEuler, Polynomial.coeff_sub,
      Nat.succ_sub_one, Polynomial.coeff_X_mul, Polynomial.coeff_derivative,
      Polynomial.coeff_smul]
    simp only [Nat.succ_sub_one] at hcoeff
    rw [hcoeff]
    push_cast
    ring

theorem natDegree_xiShiftedBoundaryDegreeCenteredShearPolynomial_le
    {n : ℕ} (hn : 0 < n) {A : Polynomial ℝ}
    (hAdeg : A.natDegree = n) :
    (xiShiftedBoundaryDegreeCenteredShearPolynomial n A).natDegree ≤
      2 * n + 1 := by
  unfold xiShiftedBoundaryDegreeCenteredShearPolynomial
  calc
    ((X * A) *
        (X * xiShiftedBoundaryDegreeCenteredEuler n A)).natDegree ≤
        (X * A).natDegree +
          (X * xiShiftedBoundaryDegreeCenteredEuler n A).natDegree :=
      Polynomial.natDegree_mul_le
    _ ≤ 2 * n + 1 := by
      have hleft : (X * A).natDegree ≤ n + 1 := by
        calc
          (X * A).natDegree ≤ X.natDegree + A.natDegree :=
            Polynomial.natDegree_mul_le
          _ = n + 1 := by rw [hAdeg, Polynomial.natDegree_X]; omega
      have hright :
          (X * xiShiftedBoundaryDegreeCenteredEuler n A).natDegree ≤ n := by
        calc
          _ ≤ X.natDegree +
              (xiShiftedBoundaryDegreeCenteredEuler n A).natDegree :=
            Polynomial.natDegree_mul_le
          _ ≤ 1 + (n - 1) := by
            rw [Polynomial.natDegree_X]
            exact Nat.add_le_add_left
              (natDegree_xiShiftedBoundaryDegreeCenteredEuler_le hn hAdeg) 1
          _ = n := by omega
      omega

theorem coeff_xiShiftedBoundaryDegreeCenteredShearPolynomial_top
    {n : ℕ} (hn : 0 < n) {A : Polynomial ℝ}
    (hA : A.Monic) (hAdeg : A.natDegree = n) :
    (xiShiftedBoundaryDegreeCenteredShearPolynomial n A).coeff (2 * n + 1) =
      -A.nextCoeff := by
  have hleft : (X * A).natDegree ≤ n + 1 := by
    rw [Polynomial.monic_X.natDegree_mul hA, Polynomial.natDegree_X, hAdeg]
    omega
  have hright :
      (X * xiShiftedBoundaryDegreeCenteredEuler n A).natDegree ≤ n := by
    calc
      _ ≤ X.natDegree +
          (xiShiftedBoundaryDegreeCenteredEuler n A).natDegree :=
        Polynomial.natDegree_mul_le
      _ ≤ 1 + (n - 1) := by
        rw [Polynomial.natDegree_X]
        exact Nat.add_le_add_left
          (natDegree_xiShiftedBoundaryDegreeCenteredEuler_le hn hAdeg) 1
      _ = n := by omega
  have hXcenter :
      (X * xiShiftedBoundaryDegreeCenteredEuler n A).coeff n =
        (xiShiftedBoundaryDegreeCenteredEuler n A).coeff (n - 1) := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
    rw [Nat.succ_sub_one, Polynomial.coeff_X_mul]
  rw [xiShiftedBoundaryDegreeCenteredShearPolynomial,
    show 2 * n + 1 = (n + 1) + n by omega,
    GaloisForLFunctions.HTGeometry.coeff_mul_of_natDegree_le hleft hright,
    hXcenter,
    coeff_xiShiftedBoundaryDegreeCenteredEuler_top hn hAdeg]
  have hlead : (X * A).coeff (n + 1) = 1 := by
    rw [Polynomial.coeff_X_mul, ← hAdeg]
    exact hA.coeff_natDegree
  rw [hlead, one_mul]

theorem xiShiftedDegreeCenteredCompletedArithmeticSource_eq_monicRemainder
    {w : ℝ} (hw : 1 / 2 < w) {n : ℕ} (hn : 0 < n)
    (c : Fin (n + 1) → ℝ)
    (hhead : (xiShiftedMomentHankelMatrix (w ^ (2 : ℕ)) n).PosDef)
    (hflat : xiShiftedMomentHankelMatrix (w ^ (2 : ℕ)) (n + 1) *ᵥ c = 0)
    (hlast : c (Fin.last n) ≠ 0) :
    let P := HTGeometry.finiteHankelNullMonicPolynomial c
    xiShiftedDegreeCenteredCompletedArithmeticSource w n P =
      -2 * P.nextCoeff * xiShiftedHankelBoundaryMonicRemainder (w ^ (2 : ℕ)) c := by
  dsimp only
  let P := HTGeometry.finiteHankelNullMonicPolynomial c
  let Q := xiShiftedBoundaryDegreeCenteredShearPolynomial n P
  have hP : P.Monic := HTGeometry.finiteHankelNullMonicPolynomial_monic c hlast
  have hPdeg : P.natDegree = n :=
    HTGeometry.finiteHankelNullMonicPolynomial_natDegree c hlast
  have hzero : ∀ k < 2 * n + 1,
      xiShiftedHankelBoundaryPadeDefect (w ^ (2 : ℕ)) c k = 0 := by
    intro k hk
    exact xiShiftedHankelBoundaryPadeDefect_eq_zero_of_le
      c hhead hflat hlast (by omega)
  have hfactor : ∃ R : Polynomial ℝ, Q = P * R := by
    refine ⟨X ^ (2 : ℕ) * xiShiftedBoundaryDegreeCenteredEuler n P, ?_⟩
    dsimp only [Q, xiShiftedBoundaryDegreeCenteredShearPolynomial]
    ring
  obtain ⟨R, hQR⟩ := hfactor
  have hdefect :
      HTGeometry.momentFunctional (xiShiftedRealMomentSequence w) Q =
        HTGeometry.momentFunctional
          (xiShiftedHankelBoundaryPadeDefect (w ^ (2 : ℕ)) c) Q := by
    rw [hQR]
    exact (momentFunctional_finiteHankelBoundaryPadeDefect_null_mul
      (xiShiftedRealMomentSequence w) c R).symm
  rw [xiShiftedDegreeCenteredCompletedArithmeticSource_eq_momentFunctional hw]
  change 2 * HTGeometry.momentFunctional (xiShiftedRealMomentSequence w) Q = _
  rw [hdefect,
    momentFunctional_eq_top_of_sequence_eq_zero_below hzero
      (natDegree_xiShiftedBoundaryDegreeCenteredShearPolynomial_le hn hPdeg),
    coeff_xiShiftedBoundaryDegreeCenteredShearPolynomial_top hn hP hPdeg]
  have hfirst := xiShiftedHankelBoundaryPadeDefect_first_eq_monicRemainder
    c hhead hflat hlast
  rw [hfirst]
  ring

/-- Canonical source-first specialization: inverse-Hankel admission is performed before degree
centering and before rational--Gamma/von Mangoldt formation. -/
theorem xiShiftedCanonicalAdmissionDegreeCenteredCompletedArithmeticSource_eq_monicRemainder
    {w : ℝ} (hw : 1 / 2 < w) {n : ℕ} (hn : 0 < n)
    (hhead : (xiShiftedMomentHankelMatrix (w ^ (2 : ℕ)) n).PosDef)
    (hflat : xiShiftedMomentHankelMatrix (w ^ (2 : ℕ)) (n + 1) *ᵥ
      HTGeometry.monicMomentAdmissionVector (xiShiftedRealMomentSequence w) n = 0) :
    let P := HTGeometry.monicMomentAdmissionPolynomial (xiShiftedRealMomentSequence w) n
    xiShiftedDegreeCenteredCompletedArithmeticSource w n P =
      -2 * P.nextCoeff *
        xiShiftedHankelBoundaryMonicRemainder (w ^ (2 : ℕ))
          (HTGeometry.monicMomentAdmissionVector (xiShiftedRealMomentSequence w) n) := by
  dsimp only
  let c := HTGeometry.monicMomentAdmissionVector (xiShiftedRealMomentSequence w) n
  have hlast : c (Fin.last n) ≠ 0 := by simp [c]
  have h := xiShiftedDegreeCenteredCompletedArithmeticSource_eq_monicRemainder
    hw hn c hhead hflat hlast
  rw [finiteHankelNullMonicPolynomial_monicMomentAdmissionVector] at h
  exact h

/-- A terminal-normalized monic null flag over a positive leading block is exactly the degree-`n`
monic orthogonal polynomial.  This identification remains valid when its own norm vanishes at the
next singular block. -/
theorem finiteHankelNullMonicPolynomial_eq_monicOrtho_of_head_posDef
    {s : ℕ → ℝ} {n : ℕ} (c : Fin (n + 1) → ℝ)
    (hhead : (HTGeometry.momentHankelMatrix s n).PosDef)
    (hflat : HTGeometry.momentHankelMatrix s (n + 1) *ᵥ c = 0)
    (hlast : c (Fin.last n) ≠ 0) :
    HTGeometry.finiteHankelNullMonicPolynomial c = HTGeometry.monicOrtho s n := by
  have hdet : (HTGeometry.momentHankelMatrix s n).det ≠ 0 := ne_of_gt hhead.det_pos
  have hP : (HTGeometry.finiteHankelNullMonicPolynomial c).Monic :=
    HTGeometry.finiteHankelNullMonicPolynomial_monic c hlast
  have hPdeg : (HTGeometry.finiteHankelNullMonicPolynomial c).natDegree = n :=
    HTGeometry.finiteHankelNullMonicPolynomial_natDegree c hlast
  have hPAdmission : HTGeometry.finiteHankelNullMonicPolynomial c =
      HTGeometry.monicMomentAdmissionPolynomial s n := by
    apply HTGeometry.eq_monicMomentAdmissionPolynomial_of_monic_of_orthogonal
      hdet hP hPdeg
    intro i
    rw [show X ^ (i : ℕ) * HTGeometry.finiteHankelNullMonicPolynomial c =
        HTGeometry.finiteHankelNullMonicPolynomial c * X ^ (i : ℕ) by ring,
      ← HTGeometry.momentInner_def]
    apply HTGeometry.momentInner_finiteHankelNullMonicPolynomial_eq_zero_of_kernel hflat
    rw [Polynomial.natDegree_X_pow]
    omega
  let hbelow := HTGeometry.positiveMomentFormBelow_of_hankelPosDef hhead
  have hOrthoAdmission : HTGeometry.monicOrtho s n =
      HTGeometry.monicMomentAdmissionPolynomial s n := by
    apply HTGeometry.eq_monicMomentAdmissionPolynomial_of_monic_of_orthogonal
      hdet (HTGeometry.monicOrtho_monic s n)
      (HTGeometry.natDegree_monicOrtho s n)
    intro i
    rw [show X ^ (i : ℕ) * HTGeometry.monicOrtho s n =
        HTGeometry.monicOrtho s n * X ^ (i : ℕ) by ring,
      ← HTGeometry.momentInner_def]
    apply HTGeometry.monicOrtho_inner_eq_zero_of_degree_lt_below hbelow le_rfl
    rw [Polynomial.degree_X_pow]
    exact_mod_cast i.isLt
  rw [hPAdmission, hOrthoAdmission]

/-- The flat null flag's negative next coefficient is exactly the cumulative lower diagonal
Jacobi trace. -/
theorem finiteHankelNullMonicPolynomial_nextCoeff_eq_neg_alpha_sum
    {s : ℕ → ℝ} {n : ℕ} (hn : 0 < n) (c : Fin (n + 1) → ℝ)
    (hhead : (HTGeometry.momentHankelMatrix s n).PosDef)
    (hflat : HTGeometry.momentHankelMatrix s (n + 1) *ᵥ c = 0)
    (hlast : c (Fin.last n) ≠ 0) :
    (HTGeometry.finiteHankelNullMonicPolynomial c).nextCoeff =
      -(∑ j ∈ Finset.range n, HTGeometry.monicOrthoAlpha s j) := by
  rw [finiteHankelNullMonicPolynomial_eq_monicOrtho_of_head_posDef
    c hhead hflat hlast]
  have hnext : (HTGeometry.monicOrtho s n).nextCoeff =
      HTGeometry.monicOrthoFirstCoeff s n := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
    rw [Polynomial.nextCoeff_of_natDegree_pos]
    · simp [HTGeometry.natDegree_monicOrtho, HTGeometry.monicOrthoFirstCoeff]
    · rw [HTGeometry.natDegree_monicOrtho]
      omega
  rw [hnext]
  exact HTGeometry.monicOrthoFirstCoeff_eq_neg_sum_below
    (HTGeometry.positiveMomentFormBelow_of_hankelPosDef hhead) le_rfl

/-- **Singular compactification of the causal source law.**  At a flat face, centered arithmetic
source is twice cumulative lower Jacobi trace times the first odd Padé remainder.  Current norm
and every even successor have disappeared. -/
theorem xiShiftedDegreeCenteredCompletedArithmeticSource_eq_alphaTrace_mul_monicRemainder
    {w : ℝ} (hw : 1 / 2 < w) {n : ℕ} (hn : 0 < n)
    (c : Fin (n + 1) → ℝ)
    (hhead : (xiShiftedMomentHankelMatrix (w ^ (2 : ℕ)) n).PosDef)
    (hflat : xiShiftedMomentHankelMatrix (w ^ (2 : ℕ)) (n + 1) *ᵥ c = 0)
    (hlast : c (Fin.last n) ≠ 0) :
    xiShiftedDegreeCenteredCompletedArithmeticSource w n
        (HTGeometry.finiteHankelNullMonicPolynomial c) =
      2 * (∑ j ∈ Finset.range n,
        HTGeometry.monicOrthoAlpha (xiShiftedRealMomentSequence w) j) *
        xiShiftedHankelBoundaryMonicRemainder (w ^ (2 : ℕ)) c := by
  have hmatrix (m : ℕ) :
      HTGeometry.momentHankelMatrix (xiShiftedRealMomentSequence w) m =
        xiShiftedMomentHankelMatrix (w ^ (2 : ℕ)) m := by
    ext i j
    rfl
  have hhead' : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence w) n).PosDef := by
    rwa [hmatrix]
  have hflat' : HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence w) (n + 1) *ᵥ c = 0 := by
    rwa [hmatrix]
  have hnext := finiteHankelNullMonicPolynomial_nextCoeff_eq_neg_alpha_sum
    hn c hhead' hflat' hlast
  rw [xiShiftedDegreeCenteredCompletedArithmeticSource_eq_monicRemainder
    hw hn c hhead hflat hlast, hnext]
  ring

/-- Negative null-root barycenter makes centered arithmetic-source positivity exactly the desired
positive monic extension orientation. -/
theorem xiShiftedDegreeCenteredCompletedArithmeticSource_pos_iff_monicRemainder_pos
    {w : ℝ} (hw : 1 / 2 < w) {n : ℕ} (hn : 0 < n)
    (c : Fin (n + 1) → ℝ)
    (hhead : (xiShiftedMomentHankelMatrix (w ^ (2 : ℕ)) n).PosDef)
    (hflat : xiShiftedMomentHankelMatrix (w ^ (2 : ℕ)) (n + 1) *ᵥ c = 0)
    (hlast : c (Fin.last n) ≠ 0)
    (hnext : (HTGeometry.finiteHankelNullMonicPolynomial c).nextCoeff < 0) :
    0 < xiShiftedDegreeCenteredCompletedArithmeticSource w n
        (HTGeometry.finiteHankelNullMonicPolynomial c) ↔
      0 < xiShiftedHankelBoundaryMonicRemainder (w ^ (2 : ℕ)) c := by
  rw [xiShiftedDegreeCenteredCompletedArithmeticSource_eq_monicRemainder
    hw hn c hhead hflat hlast]
  constructor <;> intro h <;> nlinarith

/-- At any right-hand first crossing whose canonical barycenter remains negative, the centered
arithmetic producer is nonpositive.  Strict positivity of this same literal producer would
therefore exclude the crossing. -/
theorem xiShiftedHankelFirstCrossing_degreeCenteredArithmeticSource_nonpos
    {w : ℝ} (hw : 1 / 2 < w) {n : ℕ} (hn : 0 < n)
    (c : Fin (n + 1) → ℝ) (hcne : c ≠ 0)
    (hhead : (xiShiftedMomentHankelMatrix (w ^ (2 : ℕ)) n).PosDef)
    (hflat : xiShiftedMomentHankelMatrix (w ^ (2 : ℕ)) (n + 1) *ᵥ c = 0)
    (hmin : IsLocalMinOn
      (fun y => xiShiftedMomentHankelQuadratic y (n + 1) c)
      (Ici (w ^ (2 : ℕ))) (w ^ (2 : ℕ)))
    (hnext : (HTGeometry.finiteHankelNullMonicPolynomial c).nextCoeff < 0) :
    xiShiftedDegreeCenteredCompletedArithmeticSource w n
        (HTGeometry.finiteHankelNullMonicPolynomial c) ≤ 0 := by
  have hlast := xiShiftedHankelNullVector_terminal_ne_zero_of_head_posDef
    (w ^ (2 : ℕ)) n c hhead hcne hflat
  have hrem := xiShiftedHankelFirstCrossing_monicRemainder_nonpos
    (sq_pos_of_pos (by linarith : 0 < w)) n c hhead hcne hflat hmin
  rw [xiShiftedDegreeCenteredCompletedArithmeticSource_eq_monicRemainder
    hw hn c hhead hflat hlast]
  nlinarith

/-! ## Endogenous trace coupling removes the barycenter-sign hypothesis -/

/-- Cubic, admission-sensitive producer: the negative next coefficient is multiplied into the
degree-centered shear polynomial before rational--Gamma/von-Mangoldt aggregation.  This is not a
sign classifier or a post-aggregation orientation map. -/
def xiShiftedTraceCoupledDegreeCenteredCompletedArithmeticSource
    (w : ℝ) (n : ℕ) (A : Polynomial ℝ) : ℝ :=
  2 * xiShiftedPolynomialCompletedArithmeticSource w
    ((-A.nextCoeff) • xiShiftedBoundaryDegreeCenteredShearPolynomial n A)

/-- Trace coupling occurs inside source formation and equals endogenous trace times raw centered
source only after the arithmetic identity is proved. -/
theorem xiShiftedTraceCoupledDegreeCenteredCompletedArithmeticSource_eq_mul
    {w : ℝ} (hw : 1 / 2 < w) (n : ℕ) (A : Polynomial ℝ) :
    xiShiftedTraceCoupledDegreeCenteredCompletedArithmeticSource w n A =
      -A.nextCoeff * xiShiftedDegreeCenteredCompletedArithmeticSource w n A := by
  rw [xiShiftedTraceCoupledDegreeCenteredCompletedArithmeticSource,
    xiShiftedPolynomialCompletedArithmeticSource_eq_momentFunctional hw,
    HTGeometry.momentFunctional_smul,
    xiShiftedDegreeCenteredCompletedArithmeticSource_eq_momentFunctional hw]
  ring

/-- At a flat face, trace-coupled source is a square coefficient times the first odd remainder.
Thus no barycenter sign survives. -/
theorem xiShiftedTraceCoupledDegreeCenteredCompletedArithmeticSource_eq_sq_mul_monicRemainder
    {w : ℝ} (hw : 1 / 2 < w) {n : ℕ} (hn : 0 < n)
    (c : Fin (n + 1) → ℝ)
    (hhead : (xiShiftedMomentHankelMatrix (w ^ (2 : ℕ)) n).PosDef)
    (hflat : xiShiftedMomentHankelMatrix (w ^ (2 : ℕ)) (n + 1) *ᵥ c = 0)
    (hlast : c (Fin.last n) ≠ 0) :
    let P := HTGeometry.finiteHankelNullMonicPolynomial c
    xiShiftedTraceCoupledDegreeCenteredCompletedArithmeticSource w n P =
      2 * P.nextCoeff ^ (2 : ℕ) *
        xiShiftedHankelBoundaryMonicRemainder (w ^ (2 : ℕ)) c := by
  dsimp only
  rw [xiShiftedTraceCoupledDegreeCenteredCompletedArithmeticSource_eq_mul hw,
    xiShiftedDegreeCenteredCompletedArithmeticSource_eq_monicRemainder
      hw hn c hhead hflat hlast]
  ring

/-- **Universal first-crossing sign.**  Every right-hand first crossing makes the literal
trace-coupled producer nonpositive, with no sign hypothesis on admitted barycenter. -/
theorem xiShiftedHankelFirstCrossing_traceCoupledDegreeCenteredArithmeticSource_nonpos
    {w : ℝ} (hw : 1 / 2 < w) {n : ℕ} (hn : 0 < n)
    (c : Fin (n + 1) → ℝ) (hcne : c ≠ 0)
    (hhead : (xiShiftedMomentHankelMatrix (w ^ (2 : ℕ)) n).PosDef)
    (hflat : xiShiftedMomentHankelMatrix (w ^ (2 : ℕ)) (n + 1) *ᵥ c = 0)
    (hmin : IsLocalMinOn
      (fun y => xiShiftedMomentHankelQuadratic y (n + 1) c)
      (Ici (w ^ (2 : ℕ))) (w ^ (2 : ℕ))) :
    xiShiftedTraceCoupledDegreeCenteredCompletedArithmeticSource w n
        (HTGeometry.finiteHankelNullMonicPolynomial c) ≤ 0 := by
  have hlast := xiShiftedHankelNullVector_terminal_ne_zero_of_head_posDef
    (w ^ (2 : ℕ)) n c hhead hcne hflat
  have hrem := xiShiftedHankelFirstCrossing_monicRemainder_nonpos
    (sq_pos_of_pos (by linarith : 0 < w)) n c hhead hcne hflat hmin
  rw [xiShiftedTraceCoupledDegreeCenteredCompletedArithmeticSource_eq_sq_mul_monicRemainder
    hw hn c hhead hflat hlast]
  exact mul_nonpos_of_nonneg_of_nonpos
    (mul_nonneg (by norm_num) (sq_nonneg _)) hrem

/-! ## Riccati completion preserves the flat-face landing -/

/-- Add the unique elementary trace-square correction used by cumulative Riccati flux.  It is
formed inside the polynomial source and has degree at most `2n`, hence vanishes against a flat
degree-`n` null row. -/
def xiShiftedBoundaryRiccatiCompletedDegreeCenteredShearPolynomial
    (n : ℕ) (A : Polynomial ℝ) : Polynomial ℝ :=
  xiShiftedBoundaryDegreeCenteredShearPolynomial n A +
    (2 * A.nextCoeff ^ (2 : ℕ)) • A ^ (2 : ℕ)

def xiShiftedRiccatiCompletedDegreeCenteredArithmeticSource
    (w : ℝ) (n : ℕ) (A : Polynomial ℝ) : ℝ :=
  2 * xiShiftedPolynomialCompletedArithmeticSource w
    (xiShiftedBoundaryRiccatiCompletedDegreeCenteredShearPolynomial n A)

/-- Trace-coupled Riccati completion.  Both trace multiplication and square completion occur
before rational--Gamma/von-Mangoldt aggregation. -/
def xiShiftedTraceCoupledRiccatiCompletedDegreeCenteredArithmeticSource
    (w : ℝ) (n : ℕ) (A : Polynomial ℝ) : ℝ :=
  2 * xiShiftedPolynomialCompletedArithmeticSource w
    ((-A.nextCoeff) •
      xiShiftedBoundaryRiccatiCompletedDegreeCenteredShearPolynomial n A)

theorem xiShiftedBoundaryRiccatiCompletedDegreeCenteredShearPolynomial_monicOrtho
    (s : ℕ → ℝ) {n : ℕ} (hn : 0 < n) :
    xiShiftedBoundaryRiccatiCompletedDegreeCenteredShearPolynomial n
        (HTGeometry.monicOrtho s n) =
      HTGeometry.riccatiCompletedDegreeCenteredOrthoSourcePolynomial s n := by
  rw [xiShiftedBoundaryRiccatiCompletedDegreeCenteredShearPolynomial,
    HTGeometry.riccatiCompletedDegreeCenteredOrthoSourcePolynomial,
    xiShiftedBoundaryDegreeCenteredShearPolynomial_monicOrtho,
    HTGeometry.monicOrtho_nextCoeff_eq_firstCoeff s hn]

theorem xiShiftedRiccatiCompletedDegreeCenteredArithmeticSource_eq_momentFunctional
    {w : ℝ} (hw : 1 / 2 < w) (n : ℕ) (A : Polynomial ℝ) :
    xiShiftedRiccatiCompletedDegreeCenteredArithmeticSource w n A =
      2 * HTGeometry.momentFunctional (xiShiftedRealMomentSequence w)
        (xiShiftedBoundaryRiccatiCompletedDegreeCenteredShearPolynomial n A) := by
  rw [xiShiftedRiccatiCompletedDegreeCenteredArithmeticSource,
    xiShiftedPolynomialCompletedArithmeticSource_eq_momentFunctional hw]

theorem xiShiftedTraceCoupledRiccatiCompletedDegreeCenteredArithmeticSource_eq_mul
    {w : ℝ} (hw : 1 / 2 < w) (n : ℕ) (A : Polynomial ℝ) :
    xiShiftedTraceCoupledRiccatiCompletedDegreeCenteredArithmeticSource w n A =
      -A.nextCoeff *
        xiShiftedRiccatiCompletedDegreeCenteredArithmeticSource w n A := by
  rw [xiShiftedTraceCoupledRiccatiCompletedDegreeCenteredArithmeticSource,
    xiShiftedPolynomialCompletedArithmeticSource_eq_momentFunctional hw,
    HTGeometry.momentFunctional_smul,
    xiShiftedRiccatiCompletedDegreeCenteredArithmeticSource_eq_momentFunctional hw]
  ring

/-! ## Nondegenerate adjacent completion -/

/-- Admission-sensitive two-amplitude completion.  Current amplitude carries the odd null-flag
channel.  Adjacent amplitude enters only in a lower even channel, which vanishes on a flat current
face but completes the positive-chamber history to a sum of squares plus one. -/
def xiShiftedBoundaryNondegenerateNullFlagCompletedShearPolynomial
    (n : ℕ) (A B : Polynomial ℝ) : Polynomial ℝ :=
  xiShiftedBoundaryRiccatiCompletedDegreeCenteredShearPolynomial n A +
    (1 + A.nextCoeff) • (X * A ^ (2 : ℕ)) +
    ((A.nextCoeff - B.nextCoeff) ^ (2 : ℕ) -
      (A.nextCoeff - B.nextCoeff) + 1) • A ^ (2 : ℕ)

/-- Literal rational--Gamma-minus-von-Mangoldt formation of the nondegenerate adjacent
completion.  Both admitted amplitudes are selected before source aggregation. -/
def xiShiftedNondegenerateNullFlagCompletedArithmeticSource
    (w : ℝ) (n : ℕ) (A B : Polynomial ℝ) : ℝ :=
  2 * xiShiftedPolynomialCompletedArithmeticSource w
    (xiShiftedBoundaryNondegenerateNullFlagCompletedShearPolynomial n A B)

/-- On an actual adjacent orthogonal pair, the two-amplitude polynomial is exactly the universal
nondegenerate null-flag completion. -/
theorem xiShiftedBoundaryNondegenerateNullFlagCompletedShearPolynomial_monicOrtho
    {s : ℕ → ℝ} {N n : ℕ} (h : HTGeometry.PositiveMomentFormBelow s N)
    (hn : 0 < n) (hnN : n + 2 ≤ N) :
    xiShiftedBoundaryNondegenerateNullFlagCompletedShearPolynomial n
        (HTGeometry.monicOrtho s n) (HTGeometry.monicOrtho s (n + 1)) =
      HTGeometry.nondegenerateNullFlagCompletedDegreeCenteredOrthoSourcePolynomial s n := by
  have hsucc := HTGeometry.monicOrthoFirstCoeff_succ_below h
    (by omega : n + 1 ≤ N)
  rw [xiShiftedBoundaryNondegenerateNullFlagCompletedShearPolynomial,
    HTGeometry.nondegenerateNullFlagCompletedDegreeCenteredOrthoSourcePolynomial,
    xiShiftedBoundaryRiccatiCompletedDegreeCenteredShearPolynomial_monicOrtho s hn,
    HTGeometry.monicOrtho_nextCoeff_eq_firstCoeff s hn,
    HTGeometry.monicOrtho_nextCoeff_eq_firstCoeff s (by omega : 0 < n + 1),
    hsucc]
  congr 2
  all_goals ring

theorem xiShiftedNondegenerateNullFlagCompletedArithmeticSource_eq_momentFunctional
    {w : ℝ} (hw : 1 / 2 < w) (n : ℕ) (A B : Polynomial ℝ) :
    xiShiftedNondegenerateNullFlagCompletedArithmeticSource w n A B =
      2 * HTGeometry.momentFunctional (xiShiftedRealMomentSequence w)
        (xiShiftedBoundaryNondegenerateNullFlagCompletedShearPolynomial n A B) := by
  rw [xiShiftedNondegenerateNullFlagCompletedArithmeticSource,
    xiShiftedPolynomialCompletedArithmeticSource_eq_momentFunctional hw]

/-- Square-mass realization of the actual adjacent nondegenerate producer.  Both inverse-Hankel
amplitudes are admitted at the current mass before the completed polynomial is evaluated. -/
def xiShiftedCanonicalNondegenerateNullFlagCompletedSourceMass
    (y : ℝ) (n : ℕ) : ℝ :=
  let s : ℕ → ℝ := fun k => (xiShiftedReciprocalMoment y k).re
  2 * HTGeometry.momentFunctional s
    (xiShiftedBoundaryNondegenerateNullFlagCompletedShearPolynomial n
      (HTGeometry.monicMomentAdmissionPolynomial s n)
      (HTGeometry.monicMomentAdmissionPolynomial s (n + 1)))

/-- At physical square mass, the mass producer is literally the rational--Gamma minus von
Mangoldt arithmetic source. -/
theorem xiShiftedCanonicalNondegenerateNullFlagCompletedSourceMass_sq_eq_arithmetic
    {w : ℝ} (hw : 1 / 2 < w) (n : ℕ) :
    xiShiftedCanonicalNondegenerateNullFlagCompletedSourceMass (w ^ (2 : ℕ)) n =
      xiShiftedNondegenerateNullFlagCompletedArithmeticSource w n
        (HTGeometry.monicMomentAdmissionPolynomial
          (xiShiftedRealMomentSequence w) n)
        (HTGeometry.monicMomentAdmissionPolynomial
          (xiShiftedRealMomentSequence w) (n + 1)) := by
  rw [xiShiftedNondegenerateNullFlagCompletedArithmeticSource_eq_momentFunctional hw]
  rfl

/-- **Division-free arithmetic boundary-layer law.**  In every positive adjacent chamber, twice
the square of the actual odd current is bounded by admitted norm times the literal nondegenerate
completed source.  Hence a nonzero odd contact cannot be reached with both collapsing norm and a
locally bounded completed producer. -/
theorem two_mul_xiShiftedCanonicalAdmissionOddCurrent_sq_le_norm_mul_nondegenerateSourceMass
    {y : ℝ} {n : ℕ} (hn : 0 < n)
    (hH : (xiShiftedMomentHankelMatrix y (n + 2)).PosDef) :
    2 * xiShiftedCanonicalAdmissionOddCurrent y n ^ (2 : ℕ) ≤
      xiShiftedCanonicalAdmissionNorm y n *
        xiShiftedCanonicalNondegenerateNullFlagCompletedSourceMass y n := by
  let s : ℕ → ℝ := fun k => (xiShiftedReciprocalMoment y k).re
  change (HTGeometry.momentHankelMatrix s (n + 2)).PosDef at hH
  let hbelow := HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH
  have hPn : HTGeometry.monicMomentAdmissionPolynomial s n =
      HTGeometry.monicOrtho s n :=
    xiShiftedCanonicalAdmissionPolynomial_eq_monicOrtho_of_hankelPosDef
      (xiShiftedMomentHankel_posDef_of_le (by omega) hH)
  have hPnext : HTGeometry.monicMomentAdmissionPolynomial s (n + 1) =
      HTGeometry.monicOrtho s (n + 1) :=
    xiShiftedCanonicalAdmissionPolynomial_eq_monicOrtho_of_hankelPosDef
      (xiShiftedMomentHankel_posDef_of_le (by omega) hH)
  have hcoercive :=
    HTGeometry.sq_momentInner_monicOrtho_X_le_norm_mul_nondegenerateSource_below
      hbelow hn (by omega : n + 2 ≤ n + 2)
  rw [xiShiftedCanonicalAdmissionOddCurrent,
    xiShiftedCanonicalAdmissionNorm,
    xiShiftedCanonicalNondegenerateNullFlagCompletedSourceMass,
    hPn, hPnext,
    xiShiftedBoundaryNondegenerateNullFlagCompletedShearPolynomial_monicOrtho
      hbelow hn (by omega : n + 2 ≤ n + 2)]
  have htwo := mul_le_mul_of_nonneg_left hcoercive (by norm_num : (0 : ℝ) ≤ 2)
  simpa only [HTGeometry.monicOrthoNormSq, s, mul_assoc, mul_left_comm, mul_comm] using htwo

/-- **Exact arithmetic projective source law.**  In an actual positive adjacent chamber, admitted
norm times the completed rational--Gamma/von-Mangoldt source is exactly twice odd-current square
plus a regular lower-history term carrying two powers of the collapsing norm. -/
theorem xiShiftedCanonicalAdmissionNorm_mul_nondegenerateSourceMass_eq_odd_sq_add_regular
    {y : ℝ} {n : ℕ} (hn : 0 < n)
    (hH : (xiShiftedMomentHankelMatrix y (n + 2)).PosDef) :
    xiShiftedCanonicalAdmissionNorm y n *
        xiShiftedCanonicalNondegenerateNullFlagCompletedSourceMass y n =
      2 * xiShiftedCanonicalAdmissionOddCurrent y n ^ (2 : ℕ) +
        2 * xiShiftedCanonicalAdmissionNorm y n ^ (2 : ℕ) *
          ((∑ j ∈ Finset.range n,
              HTGeometry.monicOrthoAlpha
                (fun k => (xiShiftedReciprocalMoment y k).re) j ^ (2 : ℕ)) +
            2 * (∑ j ∈ Finset.range n,
              HTGeometry.monicOrthoBeta
                (fun k => (xiShiftedReciprocalMoment y k).re) j) +
            2 * HTGeometry.monicOrthoFirstCoeff
                (fun k => (xiShiftedReciprocalMoment y k).re) n ^ (2 : ℕ) + 1) := by
  let s : ℕ → ℝ := fun k => (xiShiftedReciprocalMoment y k).re
  change (HTGeometry.momentHankelMatrix s (n + 2)).PosDef at hH
  let hbelow := HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH
  have hPn : HTGeometry.monicMomentAdmissionPolynomial s n =
      HTGeometry.monicOrtho s n :=
    xiShiftedCanonicalAdmissionPolynomial_eq_monicOrtho_of_hankelPosDef
      (xiShiftedMomentHankel_posDef_of_le (by omega) hH)
  have hPnext : HTGeometry.monicMomentAdmissionPolynomial s (n + 1) =
      HTGeometry.monicOrtho s (n + 1) :=
    xiShiftedCanonicalAdmissionPolynomial_eq_monicOrtho_of_hankelPosDef
      (xiShiftedMomentHankel_posDef_of_le (by omega) hH)
  have hexact :=
    HTGeometry.norm_mul_momentFunctional_nondegenerateSource_eq_odd_sq_add_regular_below
      hbelow hn (by omega : n + 2 ≤ n + 2)
  have htwo := congrArg (fun z : ℝ => 2 * z) hexact
  rw [xiShiftedCanonicalAdmissionOddCurrent,
    xiShiftedCanonicalAdmissionNorm,
    xiShiftedCanonicalNondegenerateNullFlagCompletedSourceMass,
    hPn, hPnext,
    xiShiftedBoundaryNondegenerateNullFlagCompletedShearPolynomial_monicOrtho
      hbelow hn (by omega : n + 2 ≤ n + 2)]
  simpa only [HTGeometry.monicOrthoNormSq, s, mul_assoc, mul_left_comm, mul_comm,
    mul_add] using htwo

/-- **No bounded completed producer at a surviving odd contact.**  Along any nontrivial filter of
positive adjacent chambers, if the admitted norm collapses to zero while the odd current converges
to a nonzero value, then the actual admission-sensitive completed source is not eventually bounded
above by any real constant.  This is the exact effectivity obstruction left by the division-free
boundary-layer law: source formation exists, but its adjacent monic amplitude becomes singular. -/
theorem not_eventually_nondegenerateSourceMass_le_of_oddCurrent_survives_norm_collapse
    {ι : Type*} {l : Filter ι} [NeBot l] {f : ι → ℝ} {n : ℕ} (hn : 0 < n) {J : ℝ}
    (hH : ∀ᶠ x in l, (xiShiftedMomentHankelMatrix (f x) (n + 2)).PosDef)
    (hnorm : Tendsto (fun x => xiShiftedCanonicalAdmissionNorm (f x) n) l (nhds 0))
    (hodd : Tendsto (fun x => xiShiftedCanonicalAdmissionOddCurrent (f x) n) l (nhds J))
    (hJ : J ≠ 0) :
    ∀ C : ℝ, ¬ ∀ᶠ x in l,
      xiShiftedCanonicalNondegenerateNullFlagCompletedSourceMass (f x) n ≤ C := by
  intro C hsource
  have hJsq : 0 < J ^ (2 : ℕ) := sq_pos_of_ne_zero hJ
  have hoddSq : Tendsto
      (fun x => xiShiftedCanonicalAdmissionOddCurrent (f x) n ^ (2 : ℕ)) l (nhds (J ^ (2 : ℕ))) :=
    hodd.pow 2
  have hoddLower : ∀ᶠ x in l, J ^ (2 : ℕ) / 2 <
      xiShiftedCanonicalAdmissionOddCurrent (f x) n ^ (2 : ℕ) :=
    hoddSq.eventually (Ioi_mem_nhds (by linarith))
  have hnormScaled : Tendsto
      (fun x => xiShiftedCanonicalAdmissionNorm (f x) n * C) l (nhds 0) := by
    simpa only [zero_mul] using hnorm.mul_const C
  have hnormUpper : ∀ᶠ x in l,
      xiShiftedCanonicalAdmissionNorm (f x) n * C < J ^ (2 : ℕ) :=
    hnormScaled.eventually (Iio_mem_nhds hJsq)
  have hfalse : ∀ᶠ x in l, False := by
    filter_upwards [hH, hsource, hoddLower, hnormUpper] with x hHx hsourcex hoddx hnormx
    have hcoercive :=
      two_mul_xiShiftedCanonicalAdmissionOddCurrent_sq_le_norm_mul_nondegenerateSourceMass
        hn hHx
    have hnormPos : 0 < xiShiftedCanonicalAdmissionNorm (f x) n := by
      rw [xiShiftedCanonicalAdmissionNorm_eq_monicOrthoNorm hHx]
      change (HTGeometry.momentHankelMatrix
        (fun k => (xiShiftedReciprocalMoment (f x) k).re) (n + 2)).PosDef at hHx
      let hbelow := HTGeometry.positiveMomentFormBelow_of_hankelPosDef hHx
      rw [HTGeometry.monicOrthoNormSq]
      exact HTGeometry.monicOrtho_inner_self_pos_below hbelow (by omega)
    have hsourceScaled :
        xiShiftedCanonicalAdmissionNorm (f x) n *
            xiShiftedCanonicalNondegenerateNullFlagCompletedSourceMass (f x) n ≤
          xiShiftedCanonicalAdmissionNorm (f x) n * C :=
      mul_le_mul_of_nonneg_left hsourcex hnormPos.le
    nlinarith
  exact (hfalse.exists).elim fun _ hx => hx

/-- **Pointwise odd-contact admission moat.**  A flat monic relation with nonzero
first omitted remainder cannot extend to a positive semidefinite next Hankel block.  The missing
odd coupling creates a hyperbolic direction before any source normalization is available. -/
theorem xiShiftedMomentHankelMatrix_succ_not_posSemidef_of_flatFace_nonzero_monicRemainder
    {y : ℝ} {n : ℕ}
    (hflat : xiShiftedMomentHankelMatrix y (n + 1) *ᵥ
      HTGeometry.monicMomentAdmissionVector
        (fun k => (xiShiftedReciprocalMoment y k).re) n = 0)
    (hodd : xiShiftedHankelBoundaryMonicRemainder y
      (HTGeometry.monicMomentAdmissionVector
        (fun k => (xiShiftedReciprocalMoment y k).re) n) ≠ 0) :
    ¬ (xiShiftedMomentHankelMatrix y (n + 2)).PosSemidef := by
  let s : ℕ → ℝ := fun k => (xiShiftedReciprocalMoment y k).re
  let c : Fin (n + 1) → ℝ := HTGeometry.monicMomentAdmissionVector s n
  apply xiShiftedMomentHankelMatrix_succ_not_posSemidef_of_kernel_of_coupling_ne_zero
    y (n + 1) c hflat
  intro hcoupling
  have hterminal :=
    HTGeometry.terminal_mul_hankelFirstOmittedCoupling_eq_sq_mul_monicRemainder
      s c (by simp [c])
  change GaloisForLFunctions.HTGeometry.hankelFirstOmittedCoupling s (n + 1) c = 0 at hcoupling
  rw [hcoupling, mul_zero, zero_eq_mul] at hterminal
  rcases hterminal with hzero | hremzero
  · simp [c] at hzero
  · apply hodd
    simpa only [xiShiftedHankelBoundaryMonicRemainder,
      HTGeometry.finiteHankelBoundaryMonicRemainder, s, c] using hremzero

/-- **PSD extension rigidity.**  A flat monic face can remain admitted in the next block only if
its odd arithmetic remainder vanishes.  This is the exact dual of the pointwise admission moat. -/
theorem xiShiftedHankelBoundaryMonicRemainder_eq_zero_of_flatFace_of_succ_posSemidef
    {y : ℝ} {n : ℕ}
    (hflat : xiShiftedMomentHankelMatrix y (n + 1) *ᵥ
      HTGeometry.monicMomentAdmissionVector
        (fun k => (xiShiftedReciprocalMoment y k).re) n = 0)
    (hpsd : (xiShiftedMomentHankelMatrix y (n + 2)).PosSemidef) :
    xiShiftedHankelBoundaryMonicRemainder y
      (HTGeometry.monicMomentAdmissionVector
        (fun k => (xiShiftedReciprocalMoment y k).re) n) = 0 := by
  by_contra hodd
  exact
    (xiShiftedMomentHankelMatrix_succ_not_posSemidef_of_flatFace_nonzero_monicRemainder
      hflat hodd) hpsd

/-- **Open odd-contact admission moat.**  At positive shift, the pointwise hyperbolic direction
persists on a full neighborhood.  Hence no positive adjacent `(n+2)` chamber can approach this
flat face; failure is geometric exclusion, not a coefficient pole in a chart that remains open. -/
theorem eventually_xiShiftedMomentHankelMatrix_succ_not_posSemidef_of_flatFace_nonzero_monicRemainder
    {y : ℝ} (hy : 0 < y) {n : ℕ}
    (hflat : xiShiftedMomentHankelMatrix y (n + 1) *ᵥ
      HTGeometry.monicMomentAdmissionVector
        (fun k => (xiShiftedReciprocalMoment y k).re) n = 0)
    (hodd : xiShiftedHankelBoundaryMonicRemainder y
      (HTGeometry.monicMomentAdmissionVector
        (fun k => (xiShiftedReciprocalMoment y k).re) n) ≠ 0) :
    ∀ᶠ v in nhds y, ¬ (xiShiftedMomentHankelMatrix v (n + 2)).PosSemidef := by
  have hnot :=
    xiShiftedMomentHankelMatrix_succ_not_posSemidef_of_flatFace_nonzero_monicRemainder
      hflat hodd
  rw [Matrix.posSemidef_iff_dotProduct_mulVec] at hnot
  have hnotall : ¬ ∀ x,
      0 ≤ star x ⬝ᵥ xiShiftedMomentHankelMatrix y (n + 2) *ᵥ x := by
    intro hall
    exact hnot ⟨xiShiftedMomentHankelMatrix_isHermitian y (n + 2), hall⟩
  push Not at hnotall
  obtain ⟨x, hx⟩ := hnotall
  have hneg : xiShiftedMomentHankelQuadratic y (n + 2) x < 0 := by
    simpa only [xiShiftedMomentHankelQuadratic, star_trivial] using hx
  have hcont :=
    (hasDerivAt_xiShiftedMomentHankelQuadratic hy (n + 2) x).continuousAt
  have hev : ∀ᶠ v in nhds y,
      xiShiftedMomentHankelQuadratic v (n + 2) x < 0 :=
    hcont.eventually_lt continuousAt_const hneg
  filter_upwards [hev] with v hv
  intro hpsd
  have hnonneg := hpsd.dotProduct_mulVec_nonneg x
  simpa only [xiShiftedMomentHankelQuadratic, star_trivial] using
    (not_lt_of_ge hnonneg hv)

/-- Exact source-first expansion into existing adaptive mixed/Riccati source and two completed
amplitude channels.  This is formation, not a post-aggregation reporter. -/
theorem xiShiftedNondegenerateNullFlagCompletedArithmeticSource_eq_riccati_add_odd_add_even
    {w : ℝ} (hw : 1 / 2 < w) (n : ℕ) (A B : Polynomial ℝ) :
    xiShiftedNondegenerateNullFlagCompletedArithmeticSource w n A B =
      xiShiftedRiccatiCompletedDegreeCenteredArithmeticSource w n A +
        2 * (1 + A.nextCoeff) *
          xiShiftedPolynomialCompletedArithmeticSource w (X * A ^ (2 : ℕ)) +
        2 * ((A.nextCoeff - B.nextCoeff) ^ (2 : ℕ) -
          (A.nextCoeff - B.nextCoeff) + 1) *
          xiShiftedPolynomialCompletedArithmeticSource w (A ^ (2 : ℕ)) := by
  rw [xiShiftedNondegenerateNullFlagCompletedArithmeticSource_eq_momentFunctional hw,
    xiShiftedBoundaryNondegenerateNullFlagCompletedShearPolynomial,
    HTGeometry.momentFunctional_add, HTGeometry.momentFunctional_add,
    HTGeometry.momentFunctional_smul, HTGeometry.momentFunctional_smul,
    xiShiftedRiccatiCompletedDegreeCenteredArithmeticSource_eq_momentFunctional hw,
    xiShiftedPolynomialCompletedArithmeticSource_eq_momentFunctional hw,
    xiShiftedPolynomialCompletedArithmeticSource_eq_momentFunctional hw]
  ring

/-- **Unconditional positive-chamber source.**  On every finite positive `(n+2)` block, the
actual adjacent amplitudes make the source equal twice admitted norm times a manifest sum of
squares plus one.  No trace, flux, or terminal sign premise remains. -/
theorem xiShiftedNondegenerateNullFlagCompletedArithmeticSource_monicOrtho_eq_history
    {w : ℝ} (hw : 1 / 2 < w) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence w) (n + 2)).PosDef) :
    xiShiftedNondegenerateNullFlagCompletedArithmeticSource w n
        (HTGeometry.monicOrtho (xiShiftedRealMomentSequence w) n)
        (HTGeometry.monicOrtho (xiShiftedRealMomentSequence w) (n + 1)) =
      2 * HTGeometry.monicOrthoNormSq (xiShiftedRealMomentSequence w) n *
        HTGeometry.nondegenerateNullFlagCompletedDegreeCenteredOrthoJacobiHistory
          (xiShiftedRealMomentSequence w) n := by
  let hbelow := HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH
  rw [xiShiftedNondegenerateNullFlagCompletedArithmeticSource_eq_momentFunctional hw,
    xiShiftedBoundaryNondegenerateNullFlagCompletedShearPolynomial_monicOrtho
      hbelow hn le_rfl,
    HTGeometry.momentFunctional_nondegenerateNullFlagCompletedDegreeCenteredOrthoSourcePolynomial_eq_history_below
      hbelow hn le_rfl]
  ring

theorem xiShiftedNondegenerateNullFlagCompletedArithmeticSource_monicOrtho_pos
    {w : ℝ} (hw : 1 / 2 < w) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence w) (n + 2)).PosDef) :
    0 < xiShiftedNondegenerateNullFlagCompletedArithmeticSource w n
      (HTGeometry.monicOrtho (xiShiftedRealMomentSequence w) n)
      (HTGeometry.monicOrtho (xiShiftedRealMomentSequence w) (n + 1)) := by
  let hbelow := HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH
  rw [xiShiftedNondegenerateNullFlagCompletedArithmeticSource_eq_momentFunctional hw,
    xiShiftedBoundaryNondegenerateNullFlagCompletedShearPolynomial_monicOrtho
      hbelow hn le_rfl]
  exact mul_pos (by norm_num)
    (HTGeometry.momentFunctional_nondegenerateNullFlagCompletedDegreeCenteredOrthoSourcePolynomial_pos_below
      hbelow hn le_rfl)

/-- Canonical inverse-Hankel specialization of positive-chamber coercivity. -/
theorem xiShiftedCanonicalAdjacentNondegenerateNullFlagCompletedArithmeticSource_pos
    {w : ℝ} (hw : 1 / 2 < w) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence w) (n + 2)).PosDef) :
    0 < xiShiftedNondegenerateNullFlagCompletedArithmeticSource w n
      (HTGeometry.monicMomentAdmissionPolynomial (xiShiftedRealMomentSequence w) n)
      (HTGeometry.monicMomentAdmissionPolynomial
        (xiShiftedRealMomentSequence w) (n + 1)) := by
  unfold xiShiftedRealMomentSequence at hH ⊢
  have hcurrent := xiShiftedCanonicalAdmissionPolynomial_eq_monicOrtho hH
  have hnextBlock : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence w) (n + 1)).PosDef :=
    xiShiftedMomentHankel_posDef_of_le (by omega) hH
  have hnext :=
    xiShiftedCanonicalAdmissionPolynomial_eq_monicOrtho_of_hankelPosDef hnextBlock
  rw [hcurrent, hnext]
  exact xiShiftedNondegenerateNullFlagCompletedArithmeticSource_monicOrtho_pos
    hw hn hH

/-- **Null-flag source landing.**  Suppose a degree-`n` monic null polynomial has Padé defect
zero through the odd contact immediately preceding `2n+2m+1`.  After admission-sensitive parity
lift by `X^m`, the Riccati-completed source lands exactly on that first surviving odd defect.
The square completion is formed before arithmetic aggregation but vanishes on the complete visible
null flag.  No positive-definite inverse or quotient is used on the plateau. -/
theorem xiShiftedRiccatiCompletedDegreeCenteredArithmeticSource_liftedNull_eq_firstOddDefect
    {w : ℝ} (hw : 1 / 2 < w) {n m : ℕ} (hn : 0 < n)
    (c : Fin (n + 1) → ℝ) (hlast : c (Fin.last n) ≠ 0)
    (hzero : ∀ k < 2 * n + (2 * m + 1),
      xiShiftedHankelBoundaryPadeDefect (w ^ (2 : ℕ)) c k = 0) :
    let P := HTGeometry.finiteHankelNullMonicPolynomial c
    let A := P * X ^ m
    xiShiftedRiccatiCompletedDegreeCenteredArithmeticSource w (n + m) A =
      -2 * A.nextCoeff *
        xiShiftedHankelBoundaryPadeDefect (w ^ (2 : ℕ)) c
          (2 * n + (2 * m + 1)) := by
  dsimp only
  let P := HTGeometry.finiteHankelNullMonicPolynomial c
  let A := P * X ^ m
  let Q := xiShiftedBoundaryDegreeCenteredShearPolynomial (n + m) A
  have hP : P.Monic := HTGeometry.finiteHankelNullMonicPolynomial_monic c hlast
  have hPdeg : P.natDegree = n :=
    HTGeometry.finiteHankelNullMonicPolynomial_natDegree c hlast
  have hA : A.Monic := hP.mul (Polynomial.monic_X_pow m)
  have hAdeg : A.natDegree = n + m := by
    dsimp only [A]
    rw [hP.natDegree_mul (Polynomial.monic_X_pow m), hPdeg,
      Polynomial.natDegree_X_pow]
  have hnm : 0 < n + m := by omega
  have htop : 2 * (n + m) + 1 = 2 * n + (2 * m + 1) := by omega
  have hQfactor : ∃ R : Polynomial ℝ, Q = P * R := by
    refine ⟨X ^ (m + 1) *
      (X * xiShiftedBoundaryDegreeCenteredEuler (n + m) A), ?_⟩
    dsimp only [Q, xiShiftedBoundaryDegreeCenteredShearPolynomial, A]
    ring
  have hQmoment :
      HTGeometry.momentFunctional (xiShiftedRealMomentSequence w) Q =
        -A.nextCoeff *
          xiShiftedHankelBoundaryPadeDefect (w ^ (2 : ℕ)) c
            (2 * n + (2 * m + 1)) := by
    obtain ⟨R, hQR⟩ := hQfactor
    have hdefect :
        HTGeometry.momentFunctional (xiShiftedRealMomentSequence w) Q =
          HTGeometry.momentFunctional
            (xiShiftedHankelBoundaryPadeDefect (w ^ (2 : ℕ)) c) Q := by
      rw [hQR]
      exact (momentFunctional_finiteHankelBoundaryPadeDefect_null_mul
        (xiShiftedRealMomentSequence w) c R).symm
    rw [hdefect,
      momentFunctional_eq_top_of_sequence_eq_zero_below hzero
        (by
          rw [← htop]
          exact natDegree_xiShiftedBoundaryDegreeCenteredShearPolynomial_le
            hnm hAdeg)]
    have hQcoeff : Q.coeff (2 * n + (2 * m + 1)) = -A.nextCoeff := by
      rw [← htop]
      exact coeff_xiShiftedBoundaryDegreeCenteredShearPolynomial_top hnm hA hAdeg
    rw [hQcoeff]
  have hAsqFactor : ∃ R : Polynomial ℝ, A ^ (2 : ℕ) = P * R := by
    refine ⟨P * X ^ (2 * m), ?_⟩
    dsimp only [A]
    ring
  have hAsqMoment :
      HTGeometry.momentFunctional (xiShiftedRealMomentSequence w) (A ^ (2 : ℕ)) = 0 := by
    obtain ⟨R, hAR⟩ := hAsqFactor
    have hdefect :
        HTGeometry.momentFunctional (xiShiftedRealMomentSequence w) (A ^ (2 : ℕ)) =
          HTGeometry.momentFunctional
            (xiShiftedHankelBoundaryPadeDefect (w ^ (2 : ℕ)) c) (A ^ (2 : ℕ)) := by
      rw [hAR]
      exact (momentFunctional_finiteHankelBoundaryPadeDefect_null_mul
        (xiShiftedRealMomentSequence w) c R).symm
    rw [hdefect]
    apply HTGeometry.momentFunctional_eq_zero_of_sequence_eq_zero_below hzero
    rw [hA.natDegree_pow, hAdeg]
    omega
  rw [xiShiftedRiccatiCompletedDegreeCenteredArithmeticSource_eq_momentFunctional hw,
    xiShiftedBoundaryRiccatiCompletedDegreeCenteredShearPolynomial,
    HTGeometry.momentFunctional_add, HTGeometry.momentFunctional_smul]
  change 2 * (HTGeometry.momentFunctional (xiShiftedRealMomentSequence w) Q +
    2 * A.nextCoeff ^ (2 : ℕ) *
      HTGeometry.momentFunctional (xiShiftedRealMomentSequence w) (A ^ (2 : ℕ))) = _
  rw [hQmoment, hAsqMoment]
  ring

/-- Trace coupling turns the odd null-flag landing into an even, gauge-invariant square amplitude.
This is the exact adaptive mixed/completed `P^sharp` aggregate requested by the singular face: the
odd arithmetic defect enters the even null-flag shear before rational--Gamma/von-Mangoldt
aggregation, and reversal of the null vector cannot change the result. -/
theorem xiShiftedTraceCoupledRiccatiCompletedSource_liftedNull_eq_sq_mul_firstOddDefect
    {w : ℝ} (hw : 1 / 2 < w) {n m : ℕ} (hn : 0 < n)
    (c : Fin (n + 1) → ℝ) (hlast : c (Fin.last n) ≠ 0)
    (hzero : ∀ k < 2 * n + (2 * m + 1),
      xiShiftedHankelBoundaryPadeDefect (w ^ (2 : ℕ)) c k = 0) :
    let P := HTGeometry.finiteHankelNullMonicPolynomial c
    let A := P * X ^ m
    xiShiftedTraceCoupledRiccatiCompletedDegreeCenteredArithmeticSource w (n + m) A =
      2 * A.nextCoeff ^ (2 : ℕ) *
        xiShiftedHankelBoundaryPadeDefect (w ^ (2 : ℕ)) c
          (2 * n + (2 * m + 1)) := by
  dsimp only
  rw [xiShiftedTraceCoupledRiccatiCompletedDegreeCenteredArithmeticSource_eq_mul hw,
    xiShiftedRiccatiCompletedDegreeCenteredArithmeticSource_liftedNull_eq_firstOddDefect
      hw hn c hlast hzero]
  ring

/-- **Nondegenerate null-flag landing.**  The unit odd channel cancels the trace-dependent top
coefficient of the Riccati source.  Every lower completion vanishes on the visible null flag, so
the full two-amplitude source lands on twice the first odd defect with coefficient one.  Adjacent
amplitude is arbitrary at the singular face: admission loss cannot change this landing. -/
theorem xiShiftedNondegenerateNullFlagCompletedArithmeticSource_liftedNull_eq_two_mul_firstOddDefect
    {w : ℝ} (hw : 1 / 2 < w) {n m : ℕ} (hn : 0 < n)
    (c : Fin (n + 1) → ℝ) (hlast : c (Fin.last n) ≠ 0)
    (hzero : ∀ k < 2 * n + (2 * m + 1),
      xiShiftedHankelBoundaryPadeDefect (w ^ (2 : ℕ)) c k = 0)
    (B : Polynomial ℝ) :
    let P := HTGeometry.finiteHankelNullMonicPolynomial c
    let A := P * X ^ m
    xiShiftedNondegenerateNullFlagCompletedArithmeticSource w (n + m) A B =
      2 * xiShiftedHankelBoundaryPadeDefect (w ^ (2 : ℕ)) c
        (2 * n + (2 * m + 1)) := by
  dsimp only
  let P := HTGeometry.finiteHankelNullMonicPolynomial c
  let A := P * X ^ m
  have hP : P.Monic := HTGeometry.finiteHankelNullMonicPolynomial_monic c hlast
  have hPdeg : P.natDegree = n :=
    HTGeometry.finiteHankelNullMonicPolynomial_natDegree c hlast
  have hA : A.Monic := hP.mul (Polynomial.monic_X_pow m)
  have hAdeg : A.natDegree = n + m := by
    dsimp only [A]
    rw [hP.natDegree_mul (Polynomial.monic_X_pow m), hPdeg,
      Polynomial.natDegree_X_pow]
  have htop : 2 * (n + m) + 1 = 2 * n + (2 * m + 1) := by omega
  have hriccati :=
    xiShiftedRiccatiCompletedDegreeCenteredArithmeticSource_liftedNull_eq_firstOddDefect
      hw hn c hlast hzero
  dsimp only at hriccati
  have hoddFactor : ∃ R : Polynomial ℝ, X * A ^ (2 : ℕ) = P * R := by
    refine ⟨X * P * X ^ (2 * m), ?_⟩
    dsimp only [A]
    ring
  have hoddMonic : (X * A ^ (2 : ℕ)).Monic := Polynomial.monic_X.mul (hA.pow 2)
  have hoddDeg : (X * A ^ (2 : ℕ)).natDegree = 2 * n + (2 * m + 1) := by
    rw [Polynomial.monic_X.natDegree_mul (hA.pow 2), Polynomial.natDegree_X,
      hA.natDegree_pow, hAdeg]
    omega
  have hoddMoment :
      HTGeometry.momentFunctional (xiShiftedRealMomentSequence w) (X * A ^ (2 : ℕ)) =
        xiShiftedHankelBoundaryPadeDefect (w ^ (2 : ℕ)) c
          (2 * n + (2 * m + 1)) := by
    obtain ⟨R, hAR⟩ := hoddFactor
    calc
      HTGeometry.momentFunctional (xiShiftedRealMomentSequence w) (X * A ^ (2 : ℕ)) =
          HTGeometry.momentFunctional
            (xiShiftedHankelBoundaryPadeDefect (w ^ (2 : ℕ)) c) (X * A ^ (2 : ℕ)) := by
        rw [hAR]
        exact (momentFunctional_finiteHankelBoundaryPadeDefect_null_mul
          (xiShiftedRealMomentSequence w) c R).symm
      _ = xiShiftedHankelBoundaryPadeDefect (w ^ (2 : ℕ)) c
          (2 * n + (2 * m + 1)) :=
        momentFunctional_monic_eq_first_of_zero_below hzero hoddMonic hoddDeg
  have hAsqFactor : ∃ R : Polynomial ℝ, A ^ (2 : ℕ) = P * R := by
    refine ⟨P * X ^ (2 * m), ?_⟩
    dsimp only [A]
    ring
  have hAsqMoment :
      HTGeometry.momentFunctional (xiShiftedRealMomentSequence w) (A ^ (2 : ℕ)) = 0 := by
    obtain ⟨R, hAR⟩ := hAsqFactor
    have hdefect :
        HTGeometry.momentFunctional (xiShiftedRealMomentSequence w) (A ^ (2 : ℕ)) =
          HTGeometry.momentFunctional
            (xiShiftedHankelBoundaryPadeDefect (w ^ (2 : ℕ)) c) (A ^ (2 : ℕ)) := by
      rw [hAR]
      exact (momentFunctional_finiteHankelBoundaryPadeDefect_null_mul
        (xiShiftedRealMomentSequence w) c R).symm
    rw [hdefect]
    apply HTGeometry.momentFunctional_eq_zero_of_sequence_eq_zero_below hzero
    rw [hA.natDegree_pow, hAdeg]
    omega
  rw [xiShiftedNondegenerateNullFlagCompletedArithmeticSource_eq_riccati_add_odd_add_even
      hw,
    hriccati,
    xiShiftedPolynomialCompletedArithmeticSource_eq_momentFunctional hw,
    xiShiftedPolynomialCompletedArithmeticSource_eq_momentFunctional hw,
    hoddMoment, hAsqMoment]
  ring

/-- **Higher odd-contact bilinear landing.**  For positive lift depth, the nondegenerate source is
exactly the literal adaptive bilinear completed arithmetic source on the two consecutive null
lifts `P * X^m` and `P * X^(m-1)`, up to the forced total-degree normalization.  Thus the odd
Padé/Gamma contact is injected into the even current null-flag producer before rational--Gamma and
von Mangoldt aggregation; this identity does not factor through an orientation reporter. -/
theorem xiShiftedNondegenerateNullFlagCompletedArithmeticSource_eq_adaptiveBilinear_of_liftedNull
    {w : ℝ} (hw : 1 / 2 < w) {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (c : Fin (n + 1) → ℝ) (hlast : c (Fin.last n) ≠ 0)
    (hzero : ∀ k < 2 * n + (2 * m + 1),
      xiShiftedHankelBoundaryPadeDefect (w ^ (2 : ℕ)) c k = 0)
    (B : Polynomial ℝ) :
    let P := HTGeometry.finiteHankelNullMonicPolynomial c
    let A := P * X ^ m
    let C := P * X ^ (m - 1)
    (((2 * n + (2 * m + 1) : ℕ) : ℝ) *
        xiShiftedNondegenerateNullFlagCompletedArithmeticSource w (n + m) A B) =
      2 * xiShiftedAdaptiveBilinearCompletedArithmeticSource w A C := by
  dsimp only
  have hnondeg :=
    xiShiftedNondegenerateNullFlagCompletedArithmeticSource_liftedNull_eq_two_mul_firstOddDefect
      hw hn c hlast hzero B
  dsimp only at hnondeg
  have hbilinear := xiShiftedAdaptiveBilinearCompletedArithmeticSource_eq_firstPadeDefect
    (i := m) (j := m - 1) hw (by omega : 2 ≤ 2 * m + 1)
      (by omega : m + (m - 1) + 2 = 2 * m + 1) c hlast hzero
  dsimp only at hbilinear
  rw [hnondeg, hbilinear]
  ring

/-- The Riccati-completed producer is exactly the existing adaptive mixed `P^sharp` arithmetic
aggregate with two source-side completion channels: admitted-degree square subtraction and the
forced trace-square correction.  Every term is formed before rational--Gamma/von-Mangoldt
aggregation. -/
theorem xiShiftedRiccatiCompletedDegreeCenteredArithmeticSource_eq_adaptive_sub_square_add_traceSquare
    {w : ℝ} (hw : 1 / 2 < w) (n : ℕ) (A : Polynomial ℝ) :
    xiShiftedRiccatiCompletedDegreeCenteredArithmeticSource w n A =
      xiShiftedAdaptiveMixedCompletedArithmeticSource w A -
        2 * (n + 1 : ℝ) *
          xiShiftedPolynomialCompletedArithmeticSource w ((X * A) ^ (2 : ℕ)) +
        4 * A.nextCoeff ^ (2 : ℕ) *
          xiShiftedPolynomialCompletedArithmeticSource w (A ^ (2 : ℕ)) := by
  calc
    xiShiftedRiccatiCompletedDegreeCenteredArithmeticSource w n A =
        2 * HTGeometry.momentFunctional (xiShiftedRealMomentSequence w)
            (xiShiftedBoundaryDegreeCenteredShearPolynomial n A) +
          4 * A.nextCoeff ^ (2 : ℕ) *
            HTGeometry.momentFunctional (xiShiftedRealMomentSequence w) (A ^ (2 : ℕ)) := by
      rw [xiShiftedRiccatiCompletedDegreeCenteredArithmeticSource_eq_momentFunctional hw,
        xiShiftedBoundaryRiccatiCompletedDegreeCenteredShearPolynomial,
        HTGeometry.momentFunctional_add, HTGeometry.momentFunctional_smul]
      ring
    _ = xiShiftedDegreeCenteredCompletedArithmeticSource w n A +
          4 * A.nextCoeff ^ (2 : ℕ) *
            xiShiftedPolynomialCompletedArithmeticSource w (A ^ (2 : ℕ)) := by
      rw [xiShiftedDegreeCenteredCompletedArithmeticSource_eq_momentFunctional hw,
        xiShiftedPolynomialCompletedArithmeticSource_eq_momentFunctional hw]
    _ = _ := by
      rw [xiShiftedDegreeCenteredCompletedArithmeticSource_eq_adaptive_sub_square hw]

/-- **Adaptive-mixed arithmetic source law.**  The nondegenerate two-amplitude producer is the
existing adaptive mixed `P^sharp` rational--Gamma-minus-von-Mangoldt aggregate, corrected by four
literal polynomial source channels before aggregation.  In particular, adjacent admission changes
the source polynomial itself; no scalar orientation is read after aggregation. -/
theorem xiShiftedNondegenerateNullFlagCompletedArithmeticSource_eq_adaptiveMixed
    {w : ℝ} (hw : 1 / 2 < w) (n : ℕ) (A B : Polynomial ℝ) :
    xiShiftedNondegenerateNullFlagCompletedArithmeticSource w n A B =
      xiShiftedAdaptiveMixedCompletedArithmeticSource w A -
        2 * (n + 1 : ℝ) *
          xiShiftedPolynomialCompletedArithmeticSource w ((X * A) ^ (2 : ℕ)) +
        4 * A.nextCoeff ^ (2 : ℕ) *
          xiShiftedPolynomialCompletedArithmeticSource w (A ^ (2 : ℕ)) +
        2 * (1 + A.nextCoeff) *
          xiShiftedPolynomialCompletedArithmeticSource w (X * A ^ (2 : ℕ)) +
        2 * ((A.nextCoeff - B.nextCoeff) ^ (2 : ℕ) -
          (A.nextCoeff - B.nextCoeff) + 1) *
          xiShiftedPolynomialCompletedArithmeticSource w (A ^ (2 : ℕ)) := by
  rw [xiShiftedNondegenerateNullFlagCompletedArithmeticSource_eq_riccati_add_odd_add_even
      hw,
    xiShiftedRiccatiCompletedDegreeCenteredArithmeticSource_eq_adaptive_sub_square_add_traceSquare
      hw]

/-- Finite-chamber source law: Riccati-completed arithmetic source is norm times completed causal
history under one finite Hankel hypothesis. -/
theorem xiShiftedRiccatiCompletedDegreeCenteredArithmeticSource_monicOrtho_eq_history
    {w : ℝ} (hw : 1 / 2 < w) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence w) (n + 2)).PosDef) :
    xiShiftedRiccatiCompletedDegreeCenteredArithmeticSource w n
        (HTGeometry.monicOrtho (xiShiftedRealMomentSequence w) n) =
      2 * HTGeometry.monicOrthoNormSq (xiShiftedRealMomentSequence w) n *
        HTGeometry.riccatiCompletedDegreeCenteredOrthoJacobiHistory
          (xiShiftedRealMomentSequence w) n := by
  let hbelow := HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH
  rw [xiShiftedRiccatiCompletedDegreeCenteredArithmeticSource_eq_momentFunctional hw,
    xiShiftedBoundaryRiccatiCompletedDegreeCenteredShearPolynomial_monicOrtho
      (xiShiftedRealMomentSequence w) hn,
    HTGeometry.momentFunctional_riccatiCompletedDegreeCenteredOrthoSourcePolynomial_eq_history_below
      hbelow hn le_rfl]
  ring

/-- A positive solve block already identifies the actual canonical first coefficient with the
Gram--Schmidt first coefficient.  The older convenience theorem requested two extra rows; this
localized form records the exact admission burden. -/
theorem xiShiftedCanonicalAdmissionFirstCoeff_eq_monicOrthoFirstCoeff_of_hankelPosDef
    {y : ℝ} {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) n).PosDef) :
    xiShiftedCanonicalAdmissionFirstCoeff y n =
      HTGeometry.monicOrthoFirstCoeff
        (fun k => (xiShiftedReciprocalMoment y k).re) n := by
  rw [xiShiftedCanonicalAdmissionFirstCoeff,
    xiShiftedCanonicalAdmissionPolynomial_eq_monicOrtho_of_hankelPosDef hH]
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  rfl

/-- **Adjacent-trace Riccati law.**  On one positive `(n+2)` block, cumulative flux equals the
negative sum of the current and next actual inverse-Hankel first coefficients.  Flux therefore
contains no independent scalar datum. -/
theorem xiShiftedCanonicalAdmissionCumulativeJacobiFlux_eq_neg_adjacentFirstCoeff
    {y : ℝ} {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef) :
    xiShiftedCanonicalAdmissionCumulativeJacobiFlux y n =
      -xiShiftedCanonicalAdmissionFirstCoeff y n -
        xiShiftedCanonicalAdmissionFirstCoeff y (n + 1) := by
  let s : ℕ → ℝ := fun k => (xiShiftedReciprocalMoment y k).re
  let hbelow := HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH
  have hcurrent : xiShiftedCanonicalAdmissionFirstCoeff y n =
      HTGeometry.monicOrthoFirstCoeff s n := by
    simpa only [s] using
      xiShiftedCanonicalAdmissionFirstCoeff_eq_monicOrthoFirstCoeff hn hH
  have hnextBlock : (HTGeometry.momentHankelMatrix s (n + 1)).PosDef :=
    xiShiftedMomentHankel_posDef_of_le (by omega) hH
  have hnext : xiShiftedCanonicalAdmissionFirstCoeff y (n + 1) =
      HTGeometry.monicOrthoFirstCoeff s (n + 1) := by
    simpa only [s] using
      xiShiftedCanonicalAdmissionFirstCoeff_eq_monicOrthoFirstCoeff_of_hankelPosDef
        (y := y) (n := n + 1) (by omega) hnextBlock
  have halpha := xiShiftedCanonicalAdmissionAlpha_eq_monicOrthoAlpha hH
  have hsucc := HTGeometry.monicOrthoFirstCoeff_succ_below hbelow
    (by omega : n + 1 ≤ n + 2)
  rw [xiShiftedCanonicalAdmissionCumulativeJacobiFlux, hcurrent, hnext, halpha,
    hsucc]
  ring

/-- Structural chamber positivity supplied by negative admission trace and positive cumulative
Riccati flux.  No far-right limit or degree-dependent threshold enters this pointwise theorem. -/
theorem xiShiftedRiccatiCompletedDegreeCenteredArithmeticSource_monicOrtho_pos
    {w : ℝ} (hw : 1 / 2 < w) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence w) (n + 2)).PosDef)
    (hfirst : HTGeometry.monicOrthoFirstCoeff
      (xiShiftedRealMomentSequence w) n < 0)
    (hflux : 0 < -2 * HTGeometry.monicOrthoFirstCoeff
        (xiShiftedRealMomentSequence w) n +
      HTGeometry.monicOrthoAlpha (xiShiftedRealMomentSequence w) n) :
    0 < xiShiftedRiccatiCompletedDegreeCenteredArithmeticSource w n
      (HTGeometry.monicOrtho (xiShiftedRealMomentSequence w) n) := by
  rw [xiShiftedRiccatiCompletedDegreeCenteredArithmeticSource_eq_momentFunctional hw,
    xiShiftedBoundaryRiccatiCompletedDegreeCenteredShearPolynomial_monicOrtho
      (xiShiftedRealMomentSequence w) hn]
  exact mul_pos (by norm_num)
    (HTGeometry.momentFunctional_riccatiCompletedDegreeCenteredOrthoSourcePolynomial_pos_below
      (HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH) hn le_rfl hfirst hflux)

/-- Canonical inverse-Hankel form of structural chamber positivity. -/
theorem xiShiftedCanonicalAdmissionTraceCoupledRiccatiCompletedDegreeCenteredArithmeticSource_pos
    {w : ℝ} (hw : 1 / 2 < w) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence w) (n + 2)).PosDef)
    (hfirst : xiShiftedCanonicalAdmissionFirstCoeff (w ^ (2 : ℕ)) n < 0)
    (hflux : 0 < xiShiftedCanonicalAdmissionCumulativeJacobiFlux (w ^ (2 : ℕ)) n) :
    0 < xiShiftedTraceCoupledRiccatiCompletedDegreeCenteredArithmeticSource w n
      (HTGeometry.monicMomentAdmissionPolynomial
        (xiShiftedRealMomentSequence w) n) := by
  unfold xiShiftedRealMomentSequence at hH ⊢
  have hfirst' : HTGeometry.monicOrthoFirstCoeff
      (fun k => (xiShiftedReciprocalMoment (w ^ (2 : ℕ)) k).re) n < 0 := by
    have hfirstEq :=
      xiShiftedCanonicalAdmissionFirstCoeff_eq_monicOrthoFirstCoeff hn hH
    rw [hfirstEq] at hfirst
    exact hfirst
  have hfirstSum := HTGeometry.monicOrthoFirstCoeff_eq_neg_sum_below
    (HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH) (by omega : n ≤ n + 2)
  have hfluxEq := xiShiftedCanonicalAdmissionCumulativeJacobiFlux_eq_trace hn hH
  have hfluxExpanded : 0 < 2 * (∑ j ∈ Finset.range n,
      HTGeometry.monicOrthoAlpha
        (fun k => (xiShiftedReciprocalMoment (w ^ (2 : ℕ)) k).re) j) +
      HTGeometry.monicOrthoAlpha
        (fun k => (xiShiftedReciprocalMoment (w ^ (2 : ℕ)) k).re) n := by
    rw [hfluxEq] at hflux
    exact hflux
  have hflux' : 0 < -2 * HTGeometry.monicOrthoFirstCoeff
        (fun k => (xiShiftedReciprocalMoment (w ^ (2 : ℕ)) k).re) n +
      HTGeometry.monicOrthoAlpha
        (fun k => (xiShiftedReciprocalMoment (w ^ (2 : ℕ)) k).re) n := by
    rw [hfirstSum]
    linarith
  have hadmission := xiShiftedCanonicalAdmissionPolynomial_eq_monicOrtho hH
  rw [hadmission,
    xiShiftedTraceCoupledRiccatiCompletedDegreeCenteredArithmeticSource_eq_mul hw,
    HTGeometry.monicOrtho_nextCoeff_eq_firstCoeff
      (fun k => (xiShiftedReciprocalMoment (w ^ (2 : ℕ)) k).re) hn]
  have hraw :=
    xiShiftedRiccatiCompletedDegreeCenteredArithmeticSource_monicOrtho_pos
      hw hn hH hfirst' hflux'
  unfold xiShiftedRealMomentSequence at hraw
  exact mul_pos (neg_pos.mpr hfirst')
    hraw

/-- **Adjacent-trace chamber criterion.**  Two negative neighboring actual admission traces force
strict positivity of the literal trace-coupled arithmetic producer.  The cumulative-flux sign is
derived internally and is not an additional premise. -/
theorem xiShiftedCanonicalAdmissionTraceCoupledRiccatiCompletedSource_pos_of_adjacentFirstCoeff_neg
    {w : ℝ} (hw : 1 / 2 < w) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence w) (n + 2)).PosDef)
    (hcurrent : xiShiftedCanonicalAdmissionFirstCoeff (w ^ (2 : ℕ)) n < 0)
    (hnext : xiShiftedCanonicalAdmissionFirstCoeff (w ^ (2 : ℕ)) (n + 1) < 0) :
    0 < xiShiftedTraceCoupledRiccatiCompletedDegreeCenteredArithmeticSource w n
      (HTGeometry.monicMomentAdmissionPolynomial
        (xiShiftedRealMomentSequence w) n) := by
  unfold xiShiftedRealMomentSequence at hH ⊢
  have hfluxEq :=
    xiShiftedCanonicalAdmissionCumulativeJacobiFlux_eq_neg_adjacentFirstCoeff hn hH
  have hflux : 0 < xiShiftedCanonicalAdmissionCumulativeJacobiFlux (w ^ (2 : ℕ)) n := by
    rw [hfluxEq]
    linarith
  exact
    xiShiftedCanonicalAdmissionTraceCoupledRiccatiCompletedDegreeCenteredArithmeticSource_pos
      hw hn hH hcurrent hflux

/-- Inside a positive block, nonpositivity of the completed producer has one exact explanation:
at least one of the two neighboring admission traces has re-entered the nonnegative half-line. -/
theorem current_or_nextFirstCoeff_nonneg_of_traceCoupledRiccatiCompletedSource_nonpos
    {w : ℝ} (hw : 1 / 2 < w) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence w) (n + 2)).PosDef)
    (hsource :
      xiShiftedTraceCoupledRiccatiCompletedDegreeCenteredArithmeticSource w n
        (HTGeometry.monicMomentAdmissionPolynomial
          (xiShiftedRealMomentSequence w) n) ≤ 0) :
    0 ≤ xiShiftedCanonicalAdmissionFirstCoeff (w ^ (2 : ℕ)) n ∨
      0 ≤ xiShiftedCanonicalAdmissionFirstCoeff (w ^ (2 : ℕ)) (n + 1) := by
  by_contra hneg
  push Not at hneg
  exact (not_lt_of_ge hsource)
    (xiShiftedCanonicalAdmissionTraceCoupledRiccatiCompletedSource_pos_of_adjacentFirstCoeff_neg
      hw hn hH hneg.1 hneg.2)

/-- The Riccati correction vanishes exactly on a flat null row.  Hence the completed source has
the same first odd remainder landing as the uncompleted centered source. -/
theorem xiShiftedRiccatiCompletedDegreeCenteredArithmeticSource_eq_monicRemainder
    {w : ℝ} (hw : 1 / 2 < w) {n : ℕ} (hn : 0 < n)
    (c : Fin (n + 1) → ℝ)
    (hhead : (xiShiftedMomentHankelMatrix (w ^ (2 : ℕ)) n).PosDef)
    (hflat : xiShiftedMomentHankelMatrix (w ^ (2 : ℕ)) (n + 1) *ᵥ c = 0)
    (hlast : c (Fin.last n) ≠ 0) :
    let P := HTGeometry.finiteHankelNullMonicPolynomial c
    xiShiftedRiccatiCompletedDegreeCenteredArithmeticSource w n P =
      -2 * P.nextCoeff *
        xiShiftedHankelBoundaryMonicRemainder (w ^ (2 : ℕ)) c := by
  dsimp only
  let P := HTGeometry.finiteHankelNullMonicPolynomial c
  have hmatrix : HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence w) (n + 1) =
      xiShiftedMomentHankelMatrix (w ^ (2 : ℕ)) (n + 1) := by
    ext i j
    rfl
  have hflat' : HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence w) (n + 1) *ᵥ c = 0 := by
    rwa [hmatrix]
  have hsquare := HTGeometry.momentFunctional_finiteHankelNullMonicPolynomial_sq_eq_zero
    (xiShiftedRealMomentSequence w) c hflat' hlast
  rw [xiShiftedRiccatiCompletedDegreeCenteredArithmeticSource_eq_momentFunctional hw,
    xiShiftedBoundaryRiccatiCompletedDegreeCenteredShearPolynomial,
    HTGeometry.momentFunctional_add, HTGeometry.momentFunctional_smul]
  change 2 * (HTGeometry.momentFunctional (xiShiftedRealMomentSequence w)
      (xiShiftedBoundaryDegreeCenteredShearPolynomial n P) +
    2 * P.nextCoeff ^ (2 : ℕ) *
      HTGeometry.momentFunctional (xiShiftedRealMomentSequence w) (P ^ (2 : ℕ))) = _
  rw [show P ^ (2 : ℕ) = P * P by ring, hsquare, mul_zero, add_zero]
  have hcenter := xiShiftedDegreeCenteredCompletedArithmeticSource_eq_monicRemainder
    hw hn c hhead hflat hlast
  dsimp only at hcenter
  rw [xiShiftedDegreeCenteredCompletedArithmeticSource_eq_momentFunctional hw] at hcenter
  exact hcenter

theorem xiShiftedTraceCoupledRiccatiCompletedDegreeCenteredArithmeticSource_eq_sq_mul_monicRemainder
    {w : ℝ} (hw : 1 / 2 < w) {n : ℕ} (hn : 0 < n)
    (c : Fin (n + 1) → ℝ)
    (hhead : (xiShiftedMomentHankelMatrix (w ^ (2 : ℕ)) n).PosDef)
    (hflat : xiShiftedMomentHankelMatrix (w ^ (2 : ℕ)) (n + 1) *ᵥ c = 0)
    (hlast : c (Fin.last n) ≠ 0) :
    let P := HTGeometry.finiteHankelNullMonicPolynomial c
    xiShiftedTraceCoupledRiccatiCompletedDegreeCenteredArithmeticSource w n P =
      2 * P.nextCoeff ^ (2 : ℕ) *
        xiShiftedHankelBoundaryMonicRemainder (w ^ (2 : ℕ)) c := by
  dsimp only
  rw [xiShiftedTraceCoupledRiccatiCompletedDegreeCenteredArithmeticSource_eq_mul hw,
    xiShiftedRiccatiCompletedDegreeCenteredArithmeticSource_eq_monicRemainder
      hw hn c hhead hflat hlast]
  ring

/-- **Riccati-completed first-crossing sign.**  Completion improves positive-chamber coercivity
without changing the unconditional nonpositive landing at any right-hand first crossing. -/
theorem xiShiftedHankelFirstCrossing_traceCoupledRiccatiCompletedDegreeCenteredArithmeticSource_nonpos
    {w : ℝ} (hw : 1 / 2 < w) {n : ℕ} (hn : 0 < n)
    (c : Fin (n + 1) → ℝ) (hcne : c ≠ 0)
    (hhead : (xiShiftedMomentHankelMatrix (w ^ (2 : ℕ)) n).PosDef)
    (hflat : xiShiftedMomentHankelMatrix (w ^ (2 : ℕ)) (n + 1) *ᵥ c = 0)
    (hmin : IsLocalMinOn
      (fun y => xiShiftedMomentHankelQuadratic y (n + 1) c)
      (Ici (w ^ (2 : ℕ))) (w ^ (2 : ℕ))) :
    xiShiftedTraceCoupledRiccatiCompletedDegreeCenteredArithmeticSource w n
        (HTGeometry.finiteHankelNullMonicPolynomial c) ≤ 0 := by
  have hlast := xiShiftedHankelNullVector_terminal_ne_zero_of_head_posDef
    (w ^ (2 : ℕ)) n c hhead hcne hflat
  have hrem := xiShiftedHankelFirstCrossing_monicRemainder_nonpos
    (sq_pos_of_pos (by linarith : 0 < w)) n c hhead hcne hflat hmin
  rw [xiShiftedTraceCoupledRiccatiCompletedDegreeCenteredArithmeticSource_eq_sq_mul_monicRemainder
    hw hn c hhead hflat hlast]
  exact mul_nonpos_of_nonneg_of_nonpos
    (mul_nonneg (by norm_num) (sq_nonneg _)) hrem

/-- **Genuine-crossing producer normal form.**  A hypothetical two-sided shifted-Xi loss selects
one parity-lifted null amplitude `A = P X^m`.  The same `m` is simultaneously plateau length,
first failing extension, and landing index of the adaptive mixed/completed source.  The producer
equals an even square amplitude times the strictly negative completed prime--Gamma shifted-square
channel.  It is therefore nonpositive unconditionally and strictly negative unless the retained
null-root barycenter vanishes. -/
theorem exists_liftedNull_traceCoupledRiccatiCompletedSource_landing_of_genuine_crossing
    {w : ℝ} (hw : 1 / 2 < w) (hwmax : w ^ (2 : ℕ) < 41 / 2)
    {n : ℕ} (hn : 0 < n) (c : Fin (n + 1) → ℝ)
    (hhead : (xiShiftedMomentHankelMatrix (w ^ (2 : ℕ)) n).PosDef)
    (hc : xiShiftedMomentHankelMatrix (w ^ (2 : ℕ)) (n + 1) *ᵥ c = 0)
    (hlast : c (Fin.last n) ≠ 0)
    (hright : ∀ᶠ u in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      (xiShiftedMomentHankelMatrix (w ^ (2 : ℕ) + u) (n + 1)).PosSemidef)
    (hleft : ∀ᶠ u in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      ¬ (xiShiftedMomentHankelMatrix (w ^ (2 : ℕ) - u) (n + 1)).PosSemidef) :
    ∃ m : ℕ,
      (∀ k < 2 * n + (2 * m + 1),
        primeArchShiftedHankelBoundaryPadeDefect (w ^ (2 : ℕ)) c k = 0) ∧
      (xiShiftedMomentHankelMatrix (w ^ (2 : ℕ)) (n + m + 1)).PosSemidef ∧
      xiShiftedMomentHankelMatrix (w ^ (2 : ℕ)) (n + m + 1) *ᵥ
          xiShiftedHankelBoundaryLiftedNullVector c m = 0 ∧
      ¬ (xiShiftedMomentHankelMatrix (w ^ (2 : ℕ)) (n + m + 2)).PosSemidef ∧
      let P := HTGeometry.finiteHankelNullMonicPolynomial c
      let A := P * X ^ m
      let S := HTGeometry.momentFunctional
        (fun k => (primeArchShiftedReciprocalMoment (w ^ (2 : ℕ)) k).re)
        (X * A ^ (2 : ℕ))
      S < 0 ∧
      xiShiftedTraceCoupledRiccatiCompletedDegreeCenteredArithmeticSource w (n + m) A =
        2 * A.nextCoeff ^ (2 : ℕ) * S ∧
      xiShiftedTraceCoupledRiccatiCompletedDegreeCenteredArithmeticSource w (n + m) A ≤ 0 ∧
      (A.nextCoeff ≠ 0 →
        xiShiftedTraceCoupledRiccatiCompletedDegreeCenteredArithmeticSource w (n + m) A < 0) := by
  have hy : 0 < w ^ (2 : ℕ) := sq_pos_of_pos (by linarith)
  obtain ⟨m, hzeroPA, hplateau, hkernel, hnext, hnegative⟩ :=
    exists_flatPlateau_kernel_nextFailure_and_negativeSource_of_genuine_crossing
      hy hwmax c hhead hc hlast hright hleft
  refine ⟨m, hzeroPA, hplateau, hkernel, hnext, ?_⟩
  dsimp only
  let P := HTGeometry.finiteHankelNullMonicPolynomial c
  let A := P * X ^ m
  let S := HTGeometry.momentFunctional
    (fun k => (primeArchShiftedReciprocalMoment (w ^ (2 : ℕ)) k).re) (X * A ^ (2 : ℕ))
  have hzeroXi : ∀ k < 2 * n + (2 * m + 1),
      xiShiftedHankelBoundaryPadeDefect (w ^ (2 : ℕ)) c k = 0 := by
    intro k hk
    rw [xiShiftedHankelBoundaryPadeDefect_eq_primeArch hy.le hwmax]
    exact hzeroPA k hk
  have hlanding :=
    xiShiftedTraceCoupledRiccatiCompletedSource_liftedNull_eq_sq_mul_firstOddDefect
      hw hn c hlast hzeroXi
  dsimp only at hlanding
  have hfirstPA :=
    primeArchShiftedHankelBoundaryPadeDefect_first_odd_eq_liftedShiftedSquare
      c hlast hzeroPA
  have hdefectEq :
      xiShiftedHankelBoundaryPadeDefect (w ^ (2 : ℕ)) c
          (2 * n + (2 * m + 1)) = S := by
    rw [xiShiftedHankelBoundaryPadeDefect_eq_primeArch hy.le hwmax, hfirstPA]
  have hsourceEq :
      xiShiftedTraceCoupledRiccatiCompletedDegreeCenteredArithmeticSource w
          (n + m) A = 2 * A.nextCoeff ^ (2 : ℕ) * S := by
    rw [hlanding, hdefectEq]
  have hSneg : S < 0 := by
    simpa only [S, A, P] using hnegative
  refine ⟨hSneg, hsourceEq, ?_, ?_⟩
  · rw [hsourceEq]
    exact mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg (by norm_num) (sq_nonneg _)) hSneg.le
  · intro htrace
    rw [hsourceEq]
    exact mul_neg_of_pos_of_neg
      (mul_pos (by norm_num) (sq_pos_of_ne_zero htrace)) hSneg

/-- **Nondegenerate genuine-crossing landing.**  The completed two-amplitude producer is strictly
positive on every effective chamber, yet every hypothetical genuine loss selects a flat null flag
where the same source equals twice a strictly negative completed prime--Gamma shifted square.
The singular landing is independent of the unavailable adjacent amplitude, so neither trace zero
nor admission totalization can erase it. -/
theorem exists_liftedNull_nondegenerateNullFlagCompletedSource_strictNeg_of_genuine_crossing
    {w : ℝ} (hw : 1 / 2 < w) (hwmax : w ^ (2 : ℕ) < 41 / 2)
    {n : ℕ} (hn : 0 < n) (c : Fin (n + 1) → ℝ)
    (hhead : (xiShiftedMomentHankelMatrix (w ^ (2 : ℕ)) n).PosDef)
    (hc : xiShiftedMomentHankelMatrix (w ^ (2 : ℕ)) (n + 1) *ᵥ c = 0)
    (hlast : c (Fin.last n) ≠ 0)
    (hright : ∀ᶠ u in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      (xiShiftedMomentHankelMatrix (w ^ (2 : ℕ) + u) (n + 1)).PosSemidef)
    (hleft : ∀ᶠ u in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      ¬ (xiShiftedMomentHankelMatrix (w ^ (2 : ℕ) - u) (n + 1)).PosSemidef) :
    ∃ m : ℕ,
      (∀ k < 2 * n + (2 * m + 1),
        primeArchShiftedHankelBoundaryPadeDefect (w ^ (2 : ℕ)) c k = 0) ∧
      (xiShiftedMomentHankelMatrix (w ^ (2 : ℕ)) (n + m + 1)).PosSemidef ∧
      xiShiftedMomentHankelMatrix (w ^ (2 : ℕ)) (n + m + 1) *ᵥ
          xiShiftedHankelBoundaryLiftedNullVector c m = 0 ∧
      ¬ (xiShiftedMomentHankelMatrix (w ^ (2 : ℕ)) (n + m + 2)).PosSemidef ∧
      let P := HTGeometry.finiteHankelNullMonicPolynomial c
      let A := P * X ^ m
      let S := HTGeometry.momentFunctional
        (fun k => (primeArchShiftedReciprocalMoment (w ^ (2 : ℕ)) k).re)
        (X * A ^ (2 : ℕ))
      S < 0 ∧
      ∀ B : Polynomial ℝ,
        xiShiftedNondegenerateNullFlagCompletedArithmeticSource w (n + m) A B =
            2 * S ∧
          xiShiftedNondegenerateNullFlagCompletedArithmeticSource w (n + m) A B < 0 := by
  have hy : 0 < w ^ (2 : ℕ) := sq_pos_of_pos (by linarith)
  obtain ⟨m, hzeroPA, hplateau, hkernel, hnext, hnegative⟩ :=
    exists_flatPlateau_kernel_nextFailure_and_negativeSource_of_genuine_crossing
      hy hwmax c hhead hc hlast hright hleft
  refine ⟨m, hzeroPA, hplateau, hkernel, hnext, ?_⟩
  dsimp only
  let P := HTGeometry.finiteHankelNullMonicPolynomial c
  let A := P * X ^ m
  let S := HTGeometry.momentFunctional
    (fun k => (primeArchShiftedReciprocalMoment (w ^ (2 : ℕ)) k).re) (X * A ^ (2 : ℕ))
  have hzeroXi : ∀ k < 2 * n + (2 * m + 1),
      xiShiftedHankelBoundaryPadeDefect (w ^ (2 : ℕ)) c k = 0 := by
    intro k hk
    rw [xiShiftedHankelBoundaryPadeDefect_eq_primeArch hy.le hwmax]
    exact hzeroPA k hk
  have hfirstPA :=
    primeArchShiftedHankelBoundaryPadeDefect_first_odd_eq_liftedShiftedSquare
      c hlast hzeroPA
  have hdefectEq :
      xiShiftedHankelBoundaryPadeDefect (w ^ (2 : ℕ)) c
          (2 * n + (2 * m + 1)) = S := by
    rw [xiShiftedHankelBoundaryPadeDefect_eq_primeArch hy.le hwmax, hfirstPA]
  have hSneg : S < 0 := by
    simpa only [S, A, P] using hnegative
  refine ⟨hSneg, ?_⟩
  intro B
  have hlanding :=
    xiShiftedNondegenerateNullFlagCompletedArithmeticSource_liftedNull_eq_two_mul_firstOddDefect
      hw hn c hlast hzeroXi B
  dsimp only at hlanding
  have hsourceEq :
      xiShiftedNondegenerateNullFlagCompletedArithmeticSource w (n + m) A B =
        2 * S := by
    rw [hlanding, hdefectEq]
  refine ⟨hsourceEq, ?_⟩
  rw [hsourceEq]
  exact mul_neg_of_pos_of_neg (by norm_num) hSneg

/-- **Structural terminal positivity.**  For each fixed positive degree, trace orientation and
degree-free Riccati contraction make the completed trace-coupled producer positive on one whole
terminal ray.  No asymptotic evaluation of this source is used. -/
theorem exists_xiShiftedCanonicalAdmissionTraceCoupledRiccatiCompletedSource_terminal_pos
    {n : ℕ} (hn : 0 < n) :
    ∃ W : ℝ, 1 < W ∧ ∀ w, W < w →
      0 < xiShiftedTraceCoupledRiccatiCompletedDegreeCenteredArithmeticSource w n
        (HTGeometry.monicMomentAdmissionPolynomial
          (xiShiftedRealMomentSequence w) n) := by
  obtain ⟨AH, hAH, hchamber⟩ :=
    exists_xiShiftedCanonicalAdmissionTerminalChamber n
  obtain ⟨AT, hAT, htrace⟩ :=
    RHTower.XiShiftedCanonicalAdmission.exists_xiShiftedCanonicalAdmissionFirstCoeff_terminal_neg_increasing_to_zero hn
  obtain ⟨AU, hAU, hflux⟩ :=
    exists_xiShiftedCanonicalAdmissionRenormalizedJacobiFlux_terminal_pos hn
  let A : ℝ := max AH (max AT AU)
  have hA0 : 0 ≤ A := le_trans hAH (le_max_left _ _)
  refine ⟨A + 2, by linarith, ?_⟩
  intro w hw
  have hw1 : 1 < w := lt_trans (by linarith : 1 < A + 2) hw
  have hAw : A < w := by linarith
  have hww : w < w ^ (2 : ℕ) := by
    have hw0 : 0 < w := lt_trans zero_lt_one hw1
    nlinarith [mul_pos hw0 (by linarith : 0 < w - 1)]
  have hAwSq : A < w ^ (2 : ℕ) := lt_trans hAw hww
  have hAHle : AH ≤ A := le_max_left _ _
  have hATle : AT ≤ A := le_trans (le_max_left _ _) (le_max_right _ _)
  have hAUle : AU ≤ A := le_trans (le_max_right _ _) (le_max_right _ _)
  have hHactual := hchamber (w ^ (2 : ℕ)) (lt_of_le_of_lt hAHle hAwSq)
  have hfirst := (htrace (w ^ (2 : ℕ)) (lt_of_le_of_lt hATle hAwSq)).1
  have hrenorm := hflux (w ^ (2 : ℕ)) (lt_of_le_of_lt hAUle hAwSq)
  have hweight : 0 < (2 * n + 1 : ℝ) := by positivity
  have hmul := mul_pos hrenorm hweight
  have hcancel :
      xiShiftedCanonicalAdmissionRenormalizedJacobiFlux (w ^ (2 : ℕ)) n *
          (2 * n + 1 : ℝ) =
        xiShiftedCanonicalAdmissionCumulativeJacobiFlux (w ^ (2 : ℕ)) n := by
    rw [xiShiftedCanonicalAdmissionRenormalizedJacobiFlux]
    field_simp
  rw [hcancel] at hmul
  have hH : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence w) (n + 2)).PosDef := by
    unfold xiShiftedRealMomentSequence
    exact hHactual
  exact xiShiftedCanonicalAdmissionTraceCoupledRiccatiCompletedDegreeCenteredArithmeticSource_pos
    (by linarith) hn hH hfirst hmul

/-- Cumulative-flux dissipation exceeds current trace velocity by a manifestly positive adjacent
Jacobi reserve.  This is the quantitative reason the next trace also moves forward. -/
theorem xiShiftedCanonicalAdmissionAdjacentTraceDissipationGap_pos
    {y : ℝ} (hy : 0 < y) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef) :
    0 < xiShiftedCanonicalAdmissionCumulativeJacobiDissipation y n -
      (finitePolynomialVelocity
        (xiShiftedCanonicalAdmissionVelocity y n)).coeff (n - 1) := by
  let s : ℕ → ℝ := fun k => (xiShiftedReciprocalMoment y k).re
  let hbelow := HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH
  rw [coeff_finitePolynomialVelocity_xiShiftedCanonicalAdmission_prev_eq_jacobiEnergy
    hy hn hH]
  exact HTGeometry.adjacentTraceDissipationGap_pos_below hbelow hn (by omega)

/-- **One-block improvement for the next trace clock.**  A positive `(n+2)` block already forces
strict increase of the degree-`n+1` canonical first coefficient.  Applying the older fixed-degree
theorem directly would have requested an unnecessary `(n+3)` block. -/
theorem deriv_xiShiftedCanonicalAdmissionFirstCoeff_succ_pos_of_add_two_posDef
    {y : ℝ} (hy : 0 < y) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef) :
    0 < deriv (fun v => xiShiftedCanonicalAdmissionFirstCoeff v (n + 1)) y := by
  let a : ℝ → ℝ := fun v => xiShiftedCanonicalAdmissionFirstCoeff v n
  let aNext : ℝ → ℝ := fun v => xiShiftedCanonicalAdmissionFirstCoeff v (n + 1)
  let F : ℝ → ℝ := fun v => xiShiftedCanonicalAdmissionCumulativeJacobiFlux v n
  let adot : ℝ := (finitePolynomialVelocity
    (xiShiftedCanonicalAdmissionVelocity y n)).coeff (n - 1)
  let aNextDot : ℝ := (finitePolynomialVelocity
    (xiShiftedCanonicalAdmissionVelocity y (n + 1))).coeff n
  let D : ℝ := xiShiftedCanonicalAdmissionCumulativeJacobiDissipation y n
  have hdet := xiShiftedMomentHankel_det_ne_zero_of_add_two_posDef hH
  have hnextBlock : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 1)).PosDef :=
    xiShiftedMomentHankel_posDef_of_le (by omega) hH
  have hnextDet : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 1)).det ≠ 0 :=
    ne_of_gt hnextBlock.det_pos
  have ha : HasDerivAt a adot y := by
    simpa only [a, adot] using
      hasDerivAt_xiShiftedCanonicalAdmissionFirstCoeff hy hn hdet
  have haNext : HasDerivAt aNext aNextDot y := by
    simpa only [aNext, aNextDot, Nat.add_sub_cancel] using
      hasDerivAt_xiShiftedCanonicalAdmissionFirstCoeff hy (by omega : 0 < n + 1) hnextDet
  have hF : HasDerivAt F (-D) y := by
    simpa only [F, D] using
      hasDerivAt_xiShiftedCanonicalAdmissionCumulativeJacobiFlux hy hn hH
  have hH' : (xiShiftedMomentHankelMatrix y (n + 2)).PosDef := hH
  have hchamber := eventually_posDef_xiShiftedMomentHankelMatrix_add hy hH'
  have hsub : Tendsto (fun v : ℝ => v - y) (nhds y) (nhds 0) := by
    have hc : ContinuousAt (fun _ : ℝ => y) y := continuousAt_const
    change Tendsto ((id : ℝ → ℝ) - fun _ : ℝ => y) (nhds y) (nhds 0)
    have ht : Tendsto ((id : ℝ → ℝ) - fun _ : ℝ => y) (nhds y)
        (nhds (((id : ℝ → ℝ) - fun _ : ℝ => y) y)) :=
      (continuousAt_id.sub hc).tendsto
    have hval : ((id : ℝ → ℝ) - fun _ : ℝ => y) y = (0 : ℝ) := by
      simp [Pi.sub_apply]
    rw [hval] at ht
    exact ht
  have hchamberAt : ∀ᶠ v in nhds y,
      (xiShiftedMomentHankelMatrix v (n + 2)).PosDef := by
    filter_upwards [hsub.eventually hchamber] with v hv
    simpa only [add_sub_cancel] using hv
  have hevent :
      F =ᶠ[nhds y] (fun v => -a v - aNext v) := by
    filter_upwards [hchamberAt] with v hv
    simpa only [F, a, aNext] using
      xiShiftedCanonicalAdmissionCumulativeJacobiFlux_eq_neg_adjacentFirstCoeff
        (y := v) hn hv
  have hrhs : HasDerivAt (fun v => -a v - aNext v)
      (-adot - aNextDot) y := ha.neg.sub haNext
  have hderivEq : -D = -adot - aNextDot :=
    (hF.congr_of_eventuallyEq hevent.symm).unique hrhs
  have hgap : 0 < D - adot := by
    simpa only [D, adot] using
      xiShiftedCanonicalAdmissionAdjacentTraceDissipationGap_pos hy hn hH
  have hnextValue : aNextDot = D - adot := by linarith
  rw [haNext.deriv, hnextValue]
  exact hgap

/-! ## Backward rigidity on the terminal positive component -/

/-- **Terminal-component source rigidity.**  Terminal trace and cumulative-flux signs propagate
backwards through every connected positive `(n+2)`-block chamber.  Therefore the Riccati-completed
trace source is positive on the whole positive component containing the terminal chamber, not
merely on a far-right ray. -/
theorem xiShiftedCanonicalAdmissionTraceCoupledRiccatiCompletedSource_pos_of_terminalConnected
    {w z : ℝ} (hw : 1 / 2 < w) {n : ℕ} (hn : 0 < n)
    (hwz : w ^ (2 : ℕ) ≤ z)
    (hchamber : ∀ y ∈ Set.Icc (w ^ (2 : ℕ)) z,
      (HTGeometry.momentHankelMatrix
        (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef)
    (hfirstz : xiShiftedCanonicalAdmissionFirstCoeff z n < 0)
    (hfluxz : 0 < xiShiftedCanonicalAdmissionCumulativeJacobiFlux z n) :
    0 < xiShiftedTraceCoupledRiccatiCompletedDegreeCenteredArithmeticSource w n
      (HTGeometry.monicMomentAdmissionPolynomial
        (xiShiftedRealMomentSequence w) n) := by
  let a : ℝ → ℝ := fun y => xiShiftedCanonicalAdmissionFirstCoeff y n
  let F : ℝ → ℝ := fun y => xiShiftedCanonicalAdmissionCumulativeJacobiFlux y n
  have hw0 : 0 < w := lt_trans (by norm_num) hw
  have hsq0 : 0 < w ^ (2 : ℕ) := sq_pos_of_pos hw0
  have hconta : ContinuousOn a (Set.Icc (w ^ (2 : ℕ)) z) := by
    intro y hy
    have hy0 : 0 < y := lt_of_lt_of_le hsq0 hy.1
    have hdet := xiShiftedMomentHankel_det_ne_zero_of_add_two_posDef
      (hchamber y hy)
    exact (hasDerivAt_xiShiftedCanonicalAdmissionFirstCoeff hy0 hn hdet).continuousAt
      |>.continuousWithinAt
  have hmonoa : StrictMonoOn a (Set.Icc (w ^ (2 : ℕ)) z) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc (w ^ (2 : ℕ)) z) hconta
    intro y hy
    rw [interior_Icc] at hy
    exact deriv_xiShiftedCanonicalAdmissionFirstCoeff_pos
      (lt_trans hsq0 hy.1) hn (hchamber y ⟨hy.1.le, hy.2.le⟩)
  have hcontF : ContinuousOn F (Set.Icc (w ^ (2 : ℕ)) z) := by
    intro y hy
    have hy0 : 0 < y := lt_of_lt_of_le hsq0 hy.1
    exact (hasDerivAt_xiShiftedCanonicalAdmissionCumulativeJacobiFlux
      hy0 hn (hchamber y hy)).continuousAt.continuousWithinAt
  have hantiF : StrictAntiOn F (Set.Icc (w ^ (2 : ℕ)) z) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc (w ^ (2 : ℕ)) z) hcontF
    intro y hy
    rw [interior_Icc] at hy
    exact deriv_xiShiftedCanonicalAdmissionCumulativeJacobiFlux_neg
      (lt_trans hsq0 hy.1) hn (hchamber y ⟨hy.1.le, hy.2.le⟩)
  have hwmem : w ^ (2 : ℕ) ∈ Set.Icc (w ^ (2 : ℕ)) z := ⟨le_rfl, hwz⟩
  have hzmem : z ∈ Set.Icc (w ^ (2 : ℕ)) z := ⟨hwz, le_rfl⟩
  have hfirstw : xiShiftedCanonicalAdmissionFirstCoeff (w ^ (2 : ℕ)) n < 0 := by
    rcases hwz.eq_or_lt with heq | hlt
    · rw [heq]
      exact hfirstz
    · have hlt' := hmonoa hwmem hzmem hlt
      dsimp only [a] at hlt'
      exact lt_trans hlt' hfirstz
  have hfluxw : 0 < xiShiftedCanonicalAdmissionCumulativeJacobiFlux (w ^ (2 : ℕ)) n := by
    rcases hwz.eq_or_lt with heq | hlt
    · rw [heq]
      exact hfluxz
    · have hlt' := hantiF hwmem hzmem hlt
      dsimp only [F] at hlt'
      exact lt_trans hfluxz hlt'
  exact
    xiShiftedCanonicalAdmissionTraceCoupledRiccatiCompletedDegreeCenteredArithmeticSource_pos
      hw hn (hchamber (w ^ (2 : ℕ)) hwmem) hfirstw hfluxw

/-- **Adjacent-trace terminal-component rigidity.**  Two neighboring negative terminal traces
propagate backwards through the same connected positive `(n+2)` block chamber.  The next trace
uses the one-block derivative improvement above, so no `(n+3)` positivity hypothesis and no
separate cumulative-flux terminal premise are needed. -/
theorem xiShiftedCanonicalAdmissionTraceCoupledRiccatiCompletedSource_pos_of_terminalAdjacentConnected
    {w z : ℝ} (hw : 1 / 2 < w) {n : ℕ} (hn : 0 < n)
    (hwz : w ^ (2 : ℕ) ≤ z)
    (hchamber : ∀ y ∈ Set.Icc (w ^ (2 : ℕ)) z,
      (HTGeometry.momentHankelMatrix
        (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef)
    (hcurrentz : xiShiftedCanonicalAdmissionFirstCoeff z n < 0)
    (hnextz : xiShiftedCanonicalAdmissionFirstCoeff z (n + 1) < 0) :
    0 < xiShiftedTraceCoupledRiccatiCompletedDegreeCenteredArithmeticSource w n
      (HTGeometry.monicMomentAdmissionPolynomial
        (xiShiftedRealMomentSequence w) n) := by
  let a : ℝ → ℝ := fun y => xiShiftedCanonicalAdmissionFirstCoeff y n
  let aNext : ℝ → ℝ := fun y => xiShiftedCanonicalAdmissionFirstCoeff y (n + 1)
  have hw0 : 0 < w := lt_trans (by norm_num) hw
  have hsq0 : 0 < w ^ (2 : ℕ) := sq_pos_of_pos hw0
  have hconta : ContinuousOn a (Set.Icc (w ^ (2 : ℕ)) z) := by
    intro y hy
    have hy0 : 0 < y := lt_of_lt_of_le hsq0 hy.1
    have hdet := xiShiftedMomentHankel_det_ne_zero_of_add_two_posDef
      (hchamber y hy)
    exact (hasDerivAt_xiShiftedCanonicalAdmissionFirstCoeff hy0 hn hdet).continuousAt
      |>.continuousWithinAt
  have hmonoa : StrictMonoOn a (Set.Icc (w ^ (2 : ℕ)) z) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc (w ^ (2 : ℕ)) z) hconta
    intro y hy
    rw [interior_Icc] at hy
    exact deriv_xiShiftedCanonicalAdmissionFirstCoeff_pos
      (lt_trans hsq0 hy.1) hn (hchamber y ⟨hy.1.le, hy.2.le⟩)
  have hcontNext : ContinuousOn aNext (Set.Icc (w ^ (2 : ℕ)) z) := by
    intro y hy
    have hy0 : 0 < y := lt_of_lt_of_le hsq0 hy.1
    have hnextBlock : (HTGeometry.momentHankelMatrix
        (fun k => (xiShiftedReciprocalMoment y k).re) (n + 1)).PosDef :=
      xiShiftedMomentHankel_posDef_of_le (by omega) (hchamber y hy)
    have hnextDet : (HTGeometry.momentHankelMatrix
        (fun k => (xiShiftedReciprocalMoment y k).re) (n + 1)).det ≠ 0 :=
      ne_of_gt hnextBlock.det_pos
    exact (hasDerivAt_xiShiftedCanonicalAdmissionFirstCoeff hy0
      (by omega : 0 < n + 1) hnextDet).continuousAt.continuousWithinAt
  have hmonoNext : StrictMonoOn aNext (Set.Icc (w ^ (2 : ℕ)) z) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc (w ^ (2 : ℕ)) z) hcontNext
    intro y hy
    rw [interior_Icc] at hy
    exact deriv_xiShiftedCanonicalAdmissionFirstCoeff_succ_pos_of_add_two_posDef
      (lt_trans hsq0 hy.1) hn (hchamber y ⟨hy.1.le, hy.2.le⟩)
  have hwmem : w ^ (2 : ℕ) ∈ Set.Icc (w ^ (2 : ℕ)) z := ⟨le_rfl, hwz⟩
  have hzmem : z ∈ Set.Icc (w ^ (2 : ℕ)) z := ⟨hwz, le_rfl⟩
  have hcurrentw : xiShiftedCanonicalAdmissionFirstCoeff (w ^ (2 : ℕ)) n < 0 := by
    rcases hwz.eq_or_lt with heq | hlt
    · rw [heq]
      exact hcurrentz
    · have hlt' := hmonoa hwmem hzmem hlt
      dsimp only [a] at hlt'
      exact lt_trans hlt' hcurrentz
  have hnextw : xiShiftedCanonicalAdmissionFirstCoeff (w ^ (2 : ℕ)) (n + 1) < 0 := by
    rcases hwz.eq_or_lt with heq | hlt
    · rw [heq]
      exact hnextz
    · have hlt' := hmonoNext hwmem hzmem hlt
      dsimp only [aNext] at hlt'
      exact lt_trans hlt' hnextz
  exact
    xiShiftedCanonicalAdmissionTraceCoupledRiccatiCompletedSource_pos_of_adjacentFirstCoeff_neg
      hw hn (hchamber (w ^ (2 : ℕ)) hwmem) hcurrentw hnextw

/-- **Source-to-higher-face escalation.**  If the completed trace source is nonpositive before a
future point carrying terminal trace/flux signs, some `(n+2)` Hankel block on the intervening
closed mass interval is not positive definite.  Thus a source zero cannot be hidden inside the
terminal positive component: it forces a higher-face gap. -/
theorem exists_xiShiftedHigherBlockGap_of_traceCoupledRiccatiCompletedSource_nonpos
    {w z : ℝ} (hw : 1 / 2 < w) {n : ℕ} (hn : 0 < n)
    (hwz : w ^ (2 : ℕ) ≤ z)
    (hfirstz : xiShiftedCanonicalAdmissionFirstCoeff z n < 0)
    (hfluxz : 0 < xiShiftedCanonicalAdmissionCumulativeJacobiFlux z n)
    (hsource :
      xiShiftedTraceCoupledRiccatiCompletedDegreeCenteredArithmeticSource w n
        (HTGeometry.monicMomentAdmissionPolynomial
          (xiShiftedRealMomentSequence w) n) ≤ 0) :
    ∃ y ∈ Set.Icc (w ^ (2 : ℕ)) z,
      ¬(HTGeometry.momentHankelMatrix
        (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef := by
  by_contra hgap
  have hchamber : ∀ y ∈ Set.Icc (w ^ (2 : ℕ)) z,
      (HTGeometry.momentHankelMatrix
        (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef := by
    intro y hy
    by_contra hnot
    exact hgap ⟨y, hy, hnot⟩
  exact (not_lt_of_ge hsource)
    (xiShiftedCanonicalAdmissionTraceCoupledRiccatiCompletedSource_pos_of_terminalConnected
      hw hn hwz hchamber hfirstz hfluxz)

/-- **Adjacent-trace source-to-higher-face escalation.**  If the completed producer is
nonpositive before a point where both neighboring traces are negative, then the intervening
`(n+2)` block cannot remain positive definite.  This is the flux-free form of escalation. -/
theorem exists_xiShiftedHigherBlockGap_of_traceCoupledRiccatiCompletedSource_nonpos_of_terminalAdjacent
    {w z : ℝ} (hw : 1 / 2 < w) {n : ℕ} (hn : 0 < n)
    (hwz : w ^ (2 : ℕ) ≤ z)
    (hcurrentz : xiShiftedCanonicalAdmissionFirstCoeff z n < 0)
    (hnextz : xiShiftedCanonicalAdmissionFirstCoeff z (n + 1) < 0)
    (hsource :
      xiShiftedTraceCoupledRiccatiCompletedDegreeCenteredArithmeticSource w n
        (HTGeometry.monicMomentAdmissionPolynomial
          (xiShiftedRealMomentSequence w) n) ≤ 0) :
    ∃ y ∈ Set.Icc (w ^ (2 : ℕ)) z,
      ¬(HTGeometry.momentHankelMatrix
        (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef := by
  by_contra hgap
  have hchamber : ∀ y ∈ Set.Icc (w ^ (2 : ℕ)) z,
      (HTGeometry.momentHankelMatrix
        (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef := by
    intro y hy
    by_contra hnot
    exact hgap ⟨y, hy, hnot⟩
  exact (not_lt_of_ge hsource)
    (xiShiftedCanonicalAdmissionTraceCoupledRiccatiCompletedSource_pos_of_terminalAdjacentConnected
      hw hn hwz hchamber hcurrentz hnextz)

/-- A nonpositive source value at a point where the `(n+2)` block is positive definite forces a
strictly later failure of that higher block before the terminal component.  This turns every
interior source zero into an actual degree-escalation event. -/
theorem exists_future_xiShiftedHigherBlockGap_of_traceCoupledRiccatiCompletedSource_nonpos
    {w : ℝ} (hw : 1 / 2 < w) {n : ℕ} (hn : 0 < n)
    (hcurrent : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment (w ^ (2 : ℕ)) k).re) (n + 2)).PosDef)
    (hsource :
      xiShiftedTraceCoupledRiccatiCompletedDegreeCenteredArithmeticSource w n
        (HTGeometry.monicMomentAdmissionPolynomial
          (xiShiftedRealMomentSequence w) n) ≤ 0) :
    ∃ z y : ℝ, w ^ (2 : ℕ) < z ∧ y ∈ Set.Ioc (w ^ (2 : ℕ)) z ∧
      ¬(HTGeometry.momentHankelMatrix
        (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef := by
  obtain ⟨AT, hAT, htrace⟩ :=
    RHTower.XiShiftedCanonicalAdmission.exists_xiShiftedCanonicalAdmissionFirstCoeff_terminal_neg_increasing_to_zero hn
  obtain ⟨ANext, hANext, htraceNext⟩ :=
    RHTower.XiShiftedCanonicalAdmission.exists_xiShiftedCanonicalAdmissionFirstCoeff_terminal_neg_increasing_to_zero
      (by omega : 0 < n + 1)
  let z : ℝ := max (w ^ (2 : ℕ)) (max AT ANext) + 1
  have hwz : w ^ (2 : ℕ) < z := lt_of_le_of_lt (le_max_left _ _) (lt_add_one _)
  have hATz : AT < z := by
    have : AT ≤ max (w ^ (2 : ℕ)) (max AT ANext) :=
      le_trans (le_max_left _ _) (le_max_right _ _)
    linarith
  have hANextz : ANext < z := by
    have : ANext ≤ max (w ^ (2 : ℕ)) (max AT ANext) :=
      le_trans (le_max_right _ _) (le_max_right _ _)
    linarith
  have hfirstz := (htrace z hATz).1
  have hnextz := (htraceNext z hANextz).1
  obtain ⟨y, hy, hnot⟩ :=
    exists_xiShiftedHigherBlockGap_of_traceCoupledRiccatiCompletedSource_nonpos_of_terminalAdjacent
      hw hn hwz.le hfirstz hnextz hsource
  have hyne : y ≠ w ^ (2 : ℕ) := by
    intro heq
    rw [heq] at hnot
    exact hnot hcurrent
  refine ⟨z, y, hwz, ⟨?_, hy.2⟩, hnot⟩
  exact lt_of_le_of_ne hy.1 (Ne.symm hyne)

/-! ## Source-first adaptive odd-contact witness -/

/-- For canonical monic admission, first omitted coupling is literally canonical monic
remainder.  Thus no orientation choice or terminal normalization separates odd arithmetic source
from Hankel boundary coupling. -/
theorem xiShiftedCanonicalAdmissionFirstOmittedCoupling_eq_monicRemainder
    (y : ℝ) (n : ℕ) :
    let s : ℕ → ℝ := fun k => (xiShiftedReciprocalMoment y k).re
    let c : Fin (n + 1) → ℝ := HTGeometry.monicMomentAdmissionVector s n
    GaloisForLFunctions.HTGeometry.hankelFirstOmittedCoupling s (n + 1) c =
      xiShiftedHankelBoundaryMonicRemainder y c := by
  let s : ℕ → ℝ := fun k => (xiShiftedReciprocalMoment y k).re
  let c : Fin (n + 1) → ℝ := HTGeometry.monicMomentAdmissionVector s n
  have hterminal :=
    HTGeometry.terminal_mul_hankelFirstOmittedCoupling_eq_sq_mul_monicRemainder
      s c (by simp [c])
  simpa only [xiShiftedHankelBoundaryMonicRemainder,
    HTGeometry.finiteHankelBoundaryMonicRemainder,
    c, s, HTGeometry.monicMomentAdmissionVector_last, one_mul, one_pow] using hterminal

/-- **Exact arithmetic determinant curvature.**  At a canonical flat admission face, determinant
two degrees higher is preceding determinant times negative odd monic source amplitude squared.
This identifies scalar Hankel loss and source-first odd contact without a sign reporter. -/
theorem det_xiShiftedMomentHankelMatrix_add_two_of_flatFace_eq
    {y : ℝ} {n : ℕ}
    (hflat : xiShiftedMomentHankelMatrix y (n + 1) *ᵥ
      HTGeometry.monicMomentAdmissionVector
        (fun k => (xiShiftedReciprocalMoment y k).re) n = 0) :
    (xiShiftedMomentHankelMatrix y (n + 2)).det =
      -(xiShiftedHankelBoundaryMonicRemainder y
          (HTGeometry.monicMomentAdmissionVector
            (fun k => (xiShiftedReciprocalMoment y k).re) n)) ^ (2 : ℕ) *
        (xiShiftedMomentHankelMatrix y n).det := by
  let s : ℕ → ℝ := fun k => (xiShiftedReciprocalMoment y k).re
  let c : Fin (n + 1) → ℝ := HTGeometry.monicMomentAdmissionVector s n
  have hdet := GaloisForLFunctions.HTGeometry.det_finiteHankelMatrix_add_two_of_monic_kernel
    s n c (by simp [c]) (by simpa only [s, c, xiShiftedMomentHankelMatrix] using hflat)
  rw [xiShiftedCanonicalAdmissionFirstOmittedCoupling_eq_monicRemainder] at hdet
  simpa only [s, c, xiShiftedMomentHankelMatrix] using hdet

/-- On an effective flat face, nonzero odd arithmetic source is equivalent to strict negativity
of determinant two degrees higher.  This is exact scalar classification, stronger than non-PSD. -/
theorem det_xiShiftedMomentHankelMatrix_add_two_neg_iff_monicRemainder_ne_zero_of_head_posDef
    {y : ℝ} {n : ℕ}
    (hhead : (xiShiftedMomentHankelMatrix y n).PosDef)
    (hflat : xiShiftedMomentHankelMatrix y (n + 1) *ᵥ
      HTGeometry.monicMomentAdmissionVector
        (fun k => (xiShiftedReciprocalMoment y k).re) n = 0) :
    (xiShiftedMomentHankelMatrix y (n + 2)).det < 0 ↔
      xiShiftedHankelBoundaryMonicRemainder y
        (HTGeometry.monicMomentAdmissionVector
          (fun k => (xiShiftedReciprocalMoment y k).re) n) ≠ 0 := by
  rw [det_xiShiftedMomentHankelMatrix_add_two_of_flatFace_eq hflat]
  let Δ := xiShiftedHankelBoundaryMonicRemainder y
    (HTGeometry.monicMomentAdmissionVector
      (fun k => (xiShiftedReciprocalMoment y k).re) n)
  have hdet : 0 < (xiShiftedMomentHankelMatrix y n).det := hhead.det_pos
  constructor
  · intro hneg hzero
    rw [hzero, zero_pow (by norm_num), neg_zero, zero_mul] at hneg
    exact (lt_irrefl 0) hneg
  · intro hne
    have hsquare : 0 < Δ ^ (2 : ℕ) := sq_pos_of_ne_zero hne
    exact mul_neg_of_neg_of_pos (neg_neg_of_pos hsquare) hdet

private theorem hankelTerminalBasis_succ_eq_indicator_last
    {n : ℕ} :
    GaloisForLFunctions.HTGeometry.hankelTerminalBasis (n + 2) =
      (fun i : Fin (n + 2) => if i = Fin.last (n + 1) then 1 else 0) := by
  funext i
  simp only [GaloisForLFunctions.HTGeometry.hankelTerminalBasis]
  by_cases hi : i = Fin.last (n + 1)
  · subst i
    simp
  · rw [if_neg hi]
    have hval : (i : ℕ) + 1 ≠ n + 2 := by
      intro h
      apply hi
      apply Fin.ext
      simpa using Nat.add_right_cancel h
    rw [if_neg hval]

/-- **Adaptive mixed source producer.**  Pad current null admission by one zero and shear only its
new terminal coefficient.  Shear amplitude is computed bilinearly from first omitted coupling and
completed by terminal moment magnitude.  This happens before any reflection or trace aggregation;
it is neither a fixed linear reporter nor an orientation map. -/
def xiShiftedOddContactAdaptiveHankelWitness
    (y : ℝ) (n : ℕ) (c : Fin (n + 1) → ℝ) : Fin (n + 2) → ℝ :=
  let s : ℕ → ℝ := fun k => (xiShiftedReciprocalMoment y k).re
  let γ := GaloisForLFunctions.HTGeometry.hankelFirstOmittedCoupling s (n + 1) c
  let a := s (2 * (n + 1))
  GaloisForLFunctions.HTGeometry.padTerminalZero c +
    (-γ / (|a| + 1)) •
      GaloisForLFunctions.HTGeometry.hankelTerminalBasis (n + 2)

@[simp] theorem xiShiftedOddContactAdaptiveHankelWitness_castSucc
    (y : ℝ) (n : ℕ) (c : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    xiShiftedOddContactAdaptiveHankelWitness y n c i.castSucc = c i := by
  have hi : (i : ℕ) ≠ n + 1 := by omega
  simp [xiShiftedOddContactAdaptiveHankelWitness,
    GaloisForLFunctions.HTGeometry.padTerminalZero,
    GaloisForLFunctions.HTGeometry.hankelTerminalBasis, hi]

@[simp] theorem xiShiftedOddContactAdaptiveHankelWitness_last
    (y : ℝ) (n : ℕ) (c : Fin (n + 1) → ℝ) :
    xiShiftedOddContactAdaptiveHankelWitness y n c (Fin.last (n + 1)) =
      -GaloisForLFunctions.HTGeometry.hankelFirstOmittedCoupling
          (fun k => (xiShiftedReciprocalMoment y k).re) (n + 1) c /
        (|(xiShiftedReciprocalMoment y (2 * (n + 1))).re| + 1) := by
  simp [xiShiftedOddContactAdaptiveHankelWitness,
    GaloisForLFunctions.HTGeometry.padTerminalZero,
    GaloisForLFunctions.HTGeometry.hankelTerminalBasis]

/-- Ordinary coefficient mass of adaptive witness is exactly current admission mass plus source
amplitude divided by terminal completion.  Supports are disjoint, so triangle inequality loses
nothing. -/
theorem sum_abs_xiShiftedOddContactAdaptiveHankelWitness
    (y : ℝ) (n : ℕ) (c : Fin (n + 1) → ℝ) :
    let s : ℕ → ℝ := fun k => (xiShiftedReciprocalMoment y k).re
    let γ := GaloisForLFunctions.HTGeometry.hankelFirstOmittedCoupling s (n + 1) c
    let a := s (2 * (n + 1))
    (∑ i : Fin (n + 2), |xiShiftedOddContactAdaptiveHankelWitness y n c i|) =
      (∑ i : Fin (n + 1), |c i|) + |γ| / (|a| + 1) := by
  let s : ℕ → ℝ := fun k => (xiShiftedReciprocalMoment y k).re
  let γ := GaloisForLFunctions.HTGeometry.hankelFirstOmittedCoupling s (n + 1) c
  let a := s (2 * (n + 1))
  rw [Fin.sum_univ_castSucc]
  simp only [xiShiftedOddContactAdaptiveHankelWitness_castSucc,
    xiShiftedOddContactAdaptiveHankelWitness_last]
  change (∑ i : Fin (n + 1), |c i|) + |-γ / (|a| + 1)| =
    (∑ i : Fin (n + 1), |c i|) + |γ| / (|a| + 1)
  rw [abs_div, abs_neg, abs_of_pos (by positivity : 0 < |a| + 1)]

/-- Half-degree-weighted coefficient mass has the same exact disjoint-support decomposition. -/
theorem sum_abs_mul_halfDegree_xiShiftedOddContactAdaptiveHankelWitness
    (y : ℝ) (n : ℕ) (c : Fin (n + 1) → ℝ) :
    let s : ℕ → ℝ := fun k => (xiShiftedReciprocalMoment y k).re
    let γ := GaloisForLFunctions.HTGeometry.hankelFirstOmittedCoupling s (n + 1) c
    let a := s (2 * (n + 1))
    (∑ i : Fin (n + 2),
      |xiShiftedOddContactAdaptiveHankelWitness y n c i| * ((i : ℝ) + 1 / 2)) =
      (∑ i : Fin (n + 1), |c i| * ((i : ℝ) + 1 / 2)) +
        |γ| / (|a| + 1) * ((n : ℝ) + 1 + 1 / 2) := by
  let s : ℕ → ℝ := fun k => (xiShiftedReciprocalMoment y k).re
  let γ := GaloisForLFunctions.HTGeometry.hankelFirstOmittedCoupling s (n + 1) c
  let a := s (2 * (n + 1))
  rw [Fin.sum_univ_castSucc]
  simp only [xiShiftedOddContactAdaptiveHankelWitness_castSucc,
    xiShiftedOddContactAdaptiveHankelWitness_last, Fin.val_castSucc, Fin.val_last]
  change (∑ i : Fin (n + 1), |c i| * ((i : ℝ) + 1 / 2)) +
      |-γ / (|a| + 1)| * (((n + 1 : ℕ) : ℝ) + 1 / 2) = _
  rw [abs_div, abs_neg, abs_of_pos (by positivity : 0 < |a| + 1)]
  push_cast
  simp only [s, γ, a]

/-- Exact bilinear landing law before adaptive completion.  On a flat current block, terminal
shear receives no old quadratic contribution: only twice odd omitted coupling times amplitude and
terminal completed amplitude-square survive. -/
theorem xiShiftedMomentHankelQuadratic_padTerminalZero_add_terminal_eq
    {y : ℝ} {n : ℕ}
    (c : Fin (n + 1) → ℝ)
    (hflat : xiShiftedMomentHankelMatrix y (n + 1) *ᵥ c = 0)
    (t : ℝ) :
    let s : ℕ → ℝ := fun k => (xiShiftedReciprocalMoment y k).re
    let u : Fin (n + 2) → ℝ := GaloisForLFunctions.HTGeometry.padTerminalZero c
    let e : Fin (n + 2) → ℝ :=
      GaloisForLFunctions.HTGeometry.hankelTerminalBasis (n + 2)
    let γ := GaloisForLFunctions.HTGeometry.hankelFirstOmittedCoupling s (n + 1) c
    let a := s (2 * (n + 1))
    xiShiftedMomentHankelQuadratic y (n + 2) (u + t • e) =
      2 * t * γ + t ^ (2 : ℕ) * a := by
  let s : ℕ → ℝ := fun k => (xiShiftedReciprocalMoment y k).re
  let M := GaloisForLFunctions.HTGeometry.finiteHankelMatrix s (n + 2)
  let u : Fin (n + 2) → ℝ := GaloisForLFunctions.HTGeometry.padTerminalZero c
  let e : Fin (n + 2) → ℝ := fun i => if i = Fin.last (n + 1) then 1 else 0
  let γ := GaloisForLFunctions.HTGeometry.hankelFirstOmittedCoupling s (n + 1) c
  let a := s (2 * (n + 1))
  have hUU : u ⬝ᵥ (M *ᵥ u) = 0 := by
    simpa only [u, M, s] using
      GaloisForLFunctions.HTGeometry.dotProduct_finiteHankelMatrix_padTerminalZero_eq_zero
        s (n + 1) c hflat
  have hUe : u ⬝ᵥ (M *ᵥ e) = γ := by
    simp only [u, e, M, γ, s, dotProduct, Matrix.mulVec,
      GaloisForLFunctions.HTGeometry.finiteHankelMatrix,
      GaloisForLFunctions.HTGeometry.padTerminalZero]
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc,
      Fin.val_last, zero_mul, add_zero]
    simp only [GaloisForLFunctions.HTGeometry.hankelFirstOmittedCoupling]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_eq_single (Fin.last (n + 1))]
    · simp only [if_pos, mul_one, Fin.val_last]
      ring
    · intro j _ hj
      simp [hj]
    · simp
  have heU : e ⬝ᵥ (M *ᵥ u) = γ := by
    simp only [u, e, M, γ, s, dotProduct, Matrix.mulVec,
      GaloisForLFunctions.HTGeometry.finiteHankelMatrix,
      GaloisForLFunctions.HTGeometry.padTerminalZero]
    rw [Finset.sum_eq_single (Fin.last (n + 1))]
    · simp only [if_pos, one_mul, Fin.val_last]
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.lastCases_castSucc, Fin.val_castSucc, Fin.lastCases_last,
        mul_zero, add_zero]
      simp only [GaloisForLFunctions.HTGeometry.hankelFirstOmittedCoupling]
      apply Finset.sum_congr rfl
      intro j _
      ring
    · intro j _ hj
      simp [hj]
    · simp
  have hee : e ⬝ᵥ (M *ᵥ e) = a := by
    simp only [e, M, a, s, dotProduct, Matrix.mulVec,
      GaloisForLFunctions.HTGeometry.finiteHankelMatrix]
    rw [Finset.sum_eq_single (Fin.last (n + 1))]
    · simp only [if_pos, one_mul, Fin.val_last]
      rw [Finset.sum_eq_single (Fin.last (n + 1))]
      · simp only [if_pos, mul_one, Fin.val_last]
        congr 2
        all_goals omega
      · intro j _ hj
        simp [hj]
      · simp
    · intro i _ hi
      simp [hi]
    · simp
  rw [hankelTerminalBasis_succ_eq_indicator_last]
  change (u + t • e) ⬝ᵥ (M *ᵥ (u + t • e)) = 2 * t * γ + t ^ (2 : ℕ) * a
  rw [Matrix.mulVec_add, Matrix.mulVec_smul,
    add_dotProduct, dotProduct_add, dotProduct_smul,
    smul_dotProduct, dotProduct_add, dotProduct_smul,
    hUU, hUe, heU, hee]
  simp only [smul_eq_mul]
  ring

/-- Exact negative energy produced by adaptive odd-contact completion.  Numerator is odd source
amplitude squared times a universally positive terminal completion factor. -/
theorem xiShiftedMomentHankelQuadratic_oddContactAdaptiveHankelWitness_eq
    {y : ℝ} {n : ℕ}
    (c : Fin (n + 1) → ℝ)
    (hflat : xiShiftedMomentHankelMatrix y (n + 1) *ᵥ c = 0) :
    let s : ℕ → ℝ := fun k => (xiShiftedReciprocalMoment y k).re
    let γ := GaloisForLFunctions.HTGeometry.hankelFirstOmittedCoupling s (n + 1) c
    let a := s (2 * (n + 1))
    xiShiftedMomentHankelQuadratic y (n + 2)
        (xiShiftedOddContactAdaptiveHankelWitness y n c) =
      -(γ ^ (2 : ℕ) * (2 * (|a| + 1) - a) / (|a| + 1) ^ (2 : ℕ)) := by
  let s : ℕ → ℝ := fun k => (xiShiftedReciprocalMoment y k).re
  let γ := GaloisForLFunctions.HTGeometry.hankelFirstOmittedCoupling s (n + 1) c
  let a := s (2 * (n + 1))
  have hD : |a| + 1 ≠ 0 := ne_of_gt (by positivity)
  rw [xiShiftedOddContactAdaptiveHankelWitness,
    xiShiftedMomentHankelQuadratic_padTerminalZero_add_terminal_eq c hflat]
  dsimp only [s, γ, a]
  field_simp
  ring

/-- Source amplitude cannot be hidden by terminal completion: adaptive negative energy dominates
odd coupling squared divided by one plus terminal moment magnitude. -/
theorem hankelFirstOmittedCoupling_sq_div_terminalMomentAbs_add_one_le_neg_adaptiveEnergy
    {y : ℝ} {n : ℕ}
    (c : Fin (n + 1) → ℝ)
    (hflat : xiShiftedMomentHankelMatrix y (n + 1) *ᵥ c = 0) :
    let s : ℕ → ℝ := fun k => (xiShiftedReciprocalMoment y k).re
    let γ := GaloisForLFunctions.HTGeometry.hankelFirstOmittedCoupling s (n + 1) c
    let a := s (2 * (n + 1))
    γ ^ (2 : ℕ) / (|a| + 1) ≤
      -xiShiftedMomentHankelQuadratic y (n + 2)
        (xiShiftedOddContactAdaptiveHankelWitness y n c) := by
  let s : ℕ → ℝ := fun k => (xiShiftedReciprocalMoment y k).re
  let γ := GaloisForLFunctions.HTGeometry.hankelFirstOmittedCoupling s (n + 1) c
  let a := s (2 * (n + 1))
  rw [xiShiftedMomentHankelQuadratic_oddContactAdaptiveHankelWitness_eq c hflat]
  simp only [neg_neg]
  change γ ^ (2 : ℕ) / (|a| + 1) ≤
    γ ^ (2 : ℕ) * (2 * (|a| + 1) - a) / (|a| + 1) ^ (2 : ℕ)
  have hD : 0 < |a| + 1 := by positivity
  have hleft : γ ^ (2 : ℕ) / (|a| + 1) =
      γ ^ (2 : ℕ) * (|a| + 1) / (|a| + 1) ^ (2 : ℕ) := by
    field_simp
  rw [hleft, div_le_div_iff_of_pos_right (sq_pos_of_pos hD)]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg γ)
  linarith [le_abs_self a]

theorem xiShiftedMomentHankelQuadratic_oddContactAdaptiveHankelWitness_neg
    {y : ℝ} {n : ℕ}
    (c : Fin (n + 1) → ℝ)
    (hflat : xiShiftedMomentHankelMatrix y (n + 1) *ᵥ c = 0)
    (hcoupling : GaloisForLFunctions.HTGeometry.hankelFirstOmittedCoupling
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 1) c ≠ 0) :
    xiShiftedMomentHankelQuadratic y (n + 2)
      (xiShiftedOddContactAdaptiveHankelWitness y n c) < 0 := by
  let s : ℕ → ℝ := fun k => (xiShiftedReciprocalMoment y k).re
  let γ := GaloisForLFunctions.HTGeometry.hankelFirstOmittedCoupling s (n + 1) c
  let a := s (2 * (n + 1))
  rw [xiShiftedMomentHankelQuadratic_oddContactAdaptiveHankelWitness_eq c hflat]
  have hγ : 0 < γ ^ (2 : ℕ) := sq_pos_of_ne_zero (by simpa only [γ, s] using hcoupling)
  have hfactor : 0 < 2 * (|a| + 1) - a := by
    have ha : a ≤ |a| := le_abs_self a
    linarith [abs_nonneg a]
  have hden : 0 < (|a| + 1) ^ (2 : ℕ) := sq_pos_of_pos (by positivity)
  exact neg_neg_of_pos (div_pos (mul_pos hγ hfactor) hden)

/-- Canonical specialization: adaptive witness energy is an exact nonlinear transform of odd
arithmetic monic remainder.  Squaring removes orientation only after source has already selected
and sheared terminal null flag. -/
theorem xiShiftedCanonicalOddContactAdaptiveHankelWitness_energy_eq
    {y : ℝ} {n : ℕ}
    (hflat : xiShiftedMomentHankelMatrix y (n + 1) *ᵥ
      HTGeometry.monicMomentAdmissionVector
        (fun k => (xiShiftedReciprocalMoment y k).re) n = 0) :
    let s : ℕ → ℝ := fun k => (xiShiftedReciprocalMoment y k).re
    let c : Fin (n + 1) → ℝ := HTGeometry.monicMomentAdmissionVector s n
    let a := s (2 * (n + 1))
    let Δ := xiShiftedHankelBoundaryMonicRemainder y c
    xiShiftedMomentHankelQuadratic y (n + 2)
        (xiShiftedOddContactAdaptiveHankelWitness y n c) =
      -(Δ ^ (2 : ℕ) * (2 * (|a| + 1) - a) / (|a| + 1) ^ (2 : ℕ)) := by
  dsimp only
  rw [xiShiftedMomentHankelQuadratic_oddContactAdaptiveHankelWitness_eq _ hflat]
  rw [xiShiftedCanonicalAdmissionFirstOmittedCoupling_eq_monicRemainder]

theorem xiShiftedCanonicalOddContactAdaptiveHankelWitness_neg
    {y : ℝ} {n : ℕ}
    (hflat : xiShiftedMomentHankelMatrix y (n + 1) *ᵥ
      HTGeometry.monicMomentAdmissionVector
        (fun k => (xiShiftedReciprocalMoment y k).re) n = 0)
    (hodd : xiShiftedHankelBoundaryMonicRemainder y
      (HTGeometry.monicMomentAdmissionVector
        (fun k => (xiShiftedReciprocalMoment y k).re) n) ≠ 0) :
    xiShiftedMomentHankelQuadratic y (n + 2)
      (xiShiftedOddContactAdaptiveHankelWitness y n
        (HTGeometry.monicMomentAdmissionVector
          (fun k => (xiShiftedReciprocalMoment y k).re) n)) < 0 := by
  apply xiShiftedMomentHankelQuadratic_oddContactAdaptiveHankelWitness_neg
    _ hflat
  rw [xiShiftedCanonicalAdmissionFirstOmittedCoupling_eq_monicRemainder]
  exact hodd

/-! ## Canonical terminal-frontier quotient of the escalation tower -/

/-- Nonnegative square masses at which the positive block required by degree-`n` completed
admission is ineffective. -/
def xiShiftedHigherBlockFailureSet (n : ℕ) : Set ℝ :=
  {y | 0 ≤ y ∧
    ¬(HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef}

/-- Supremal ineffective mass for the degree-`n` higher block.  Fixed-block far-right positivity
makes this a finite real number without choosing a crossing or a branch. -/
noncomputable def xiShiftedHigherBlockTerminalFrontier (n : ℕ) : ℝ :=
  sSup (xiShiftedHigherBlockFailureSet n)

/-- Every fixed-degree higher-block failure set is bounded above by a terminal chamber entrance. -/
theorem bddAbove_xiShiftedHigherBlockFailureSet (n : ℕ) :
    BddAbove (xiShiftedHigherBlockFailureSet n) := by
  obtain ⟨A, hA, hterminal⟩ := exists_xiShiftedCanonicalAdmissionTerminalChamber n
  refine ⟨A, ?_⟩
  intro y hy
  by_contra hAy
  have hlt : A < y := lt_of_not_ge hAy
  exact hy.2 (hterminal y hlt)

/-- Every actual ineffective mass lies below the canonical terminal frontier. -/
theorem le_xiShiftedHigherBlockTerminalFrontier_of_mem
    {n : ℕ} {y : ℝ} (hy : y ∈ xiShiftedHigherBlockFailureSet n) :
    y ≤ xiShiftedHigherBlockTerminalFrontier n := by
  exact le_csSup (bddAbove_xiShiftedHigherBlockFailureSet n) hy

/-- **Quantitative arithmetic frontier displacement.**  Any fixed negative direction at mass
`y` remains negative for a literal interval whose width is its negative energy divided by twice
one plus its global shifted-Xi Hankel Lipschitz weight.  Hence the degree-`n` terminal frontier
lies at least that far to the right.  This upgrades qualitative non-PSD separation to an explicit,
source-measurable lower displacement without a compactness or local-boundedness choice. -/
theorem add_negHankelQuadratic_div_lipschitzWeight_le_terminalFrontier
    {n : ℕ} {y : ℝ} (hy : 0 < y) (x : Fin (n + 2) → ℝ)
    (hneg : xiShiftedMomentHankelQuadratic y (n + 2) x < 0) :
    y + (-xiShiftedMomentHankelQuadratic y (n + 2) x) /
        (2 * (xiShiftedMomentHankelQuadraticLipschitzWeight x + 1)) ≤
      xiShiftedHigherBlockTerminalFrontier n := by
  let q : ℝ := xiShiftedMomentHankelQuadratic y (n + 2) x
  let W : ℝ := xiShiftedMomentHankelQuadraticLipschitzWeight x
  let δ : ℝ := -q
  let D : ℝ := 2 * (W + 1)
  let r : ℝ := δ / D
  have hW : 0 ≤ W := xiShiftedMomentHankelQuadraticLipschitzWeight_nonneg x
  have hD : 0 < D := by dsimp only [D]; positivity
  have hδ : 0 < δ := by dsimp only [δ, q]; linarith
  have hr : 0 < r := div_pos hδ hD
  have hyv : y ≤ y + r := le_add_of_nonneg_right hr.le
  have hLip := abs_xiShiftedMomentHankelQuadratic_sub_le hy hyv x
  have hfrac : W / D < 1 := by
    rw [div_lt_iff₀ hD]
    dsimp only [D]
    nlinarith
  have hWr : W * r < δ := by
    calc
      W * r = δ * (W / D) := by
        dsimp only [r]
        field_simp
      _ < δ * 1 := mul_lt_mul_of_pos_left hfrac hδ
      _ = δ := mul_one δ
  have hquadNeg :
      xiShiftedMomentHankelQuadratic (y + r) (n + 2) x < 0 := by
    have hdiff :
        xiShiftedMomentHankelQuadratic (y + r) (n + 2) x -
            xiShiftedMomentHankelQuadratic y (n + 2) x ≤
          xiShiftedMomentHankelQuadraticLipschitzWeight x * r :=
      le_trans (le_abs_self _) (by simpa only [add_sub_cancel_left] using hLip)
    dsimp only [δ, q, W] at hWr
    linarith
  apply le_xiShiftedHigherBlockTerminalFrontier_of_mem
  refine ⟨(hy.le.trans hyv), ?_⟩
  intro hpos
  have hnonneg := hpos.posSemidef.dotProduct_mulVec_nonneg x
  exact (not_lt_of_ge hnonneg) hquadNeg

/-- A negative shifted-Xi Hankel direction has strictly positive global integral Lipschitz weight.
Zero weight would freeze that negative energy into known far-right positive chamber. -/
theorem xiShiftedMomentHankelQuadraticLipschitzWeight_pos_of_neg
    {n : ℕ} {y : ℝ} (hy : 0 < y) (x : Fin (n + 2) → ℝ)
    (hneg : xiShiftedMomentHankelQuadratic y (n + 2) x < 0) :
    0 < xiShiftedMomentHankelQuadraticLipschitzWeight x := by
  let q : ℝ := xiShiftedMomentHankelQuadratic y (n + 2) x
  let W : ℝ := xiShiftedMomentHankelQuadraticLipschitzWeight x
  have hxne : x ≠ 0 := by
    intro hx
    rw [hx] at hneg
    exact (lt_irrefl (0 : ℝ))
      (by simpa only [xiShiftedMomentHankelQuadratic, zero_dotProduct] using hneg)
  have hWnonneg : 0 ≤ W := xiShiftedMomentHankelQuadraticLipschitzWeight_nonneg x
  have hWne : W ≠ 0 := by
    intro hWzero
    obtain ⟨A, _hA, hterminal⟩ := exists_xiShiftedCanonicalAdmissionTerminalChamber n
    let z : ℝ := max A y + 1
    have hyz : y ≤ z := le_trans (le_max_right A y) (le_add_of_nonneg_right zero_le_one)
    have hAz : A < z := lt_of_le_of_lt (le_max_left A y) (lt_add_one _)
    have hLip := abs_xiShiftedMomentHankelQuadratic_sub_le hy hyz x
    change |xiShiftedMomentHankelQuadratic z (n + 2) x - q| ≤ W * (z - y) at hLip
    rw [hWzero, zero_mul] at hLip
    have hEq : xiShiftedMomentHankelQuadratic z (n + 2) x = q := by
      have hzero : |xiShiftedMomentHankelQuadratic z (n + 2) x - q| = 0 :=
        le_antisymm hLip (abs_nonneg _)
      exact sub_eq_zero.mp (abs_eq_zero.mp hzero)
    have hstrict := (hterminal z hAz).dotProduct_mulVec_pos hxne
    have hmatrix : HTGeometry.momentHankelMatrix
        (fun k => (xiShiftedReciprocalMoment z k).re) (n + 2) =
        xiShiftedMomentHankelMatrix z (n + 2) := rfl
    rw [hmatrix] at hstrict
    have hqpos : 0 < xiShiftedMomentHankelQuadratic z (n + 2) x := hstrict
    dsimp only [q] at hEq
    linarith
  exact lt_of_le_of_ne hWnonneg (Ne.symm hWne)

/-- **Sharp integral-Lipschitz frontier displacement.**  Negative quadratic energy can be
transported all the way to zero, because terminal failure excludes positive definiteness.  Its
Lipschitz weight is automatically positive: weight zero would propagate a negative direction
into the known far-right positive chamber.  Hence no artificial `+1` or factor `2` remains. -/
theorem add_negHankelQuadratic_div_lipschitzWeight_le_terminalFrontier_sharp
    {n : ℕ} {y : ℝ} (hy : 0 < y) (x : Fin (n + 2) → ℝ)
    (hneg : xiShiftedMomentHankelQuadratic y (n + 2) x < 0) :
    y + (-xiShiftedMomentHankelQuadratic y (n + 2) x) /
        xiShiftedMomentHankelQuadraticLipschitzWeight x ≤
      xiShiftedHigherBlockTerminalFrontier n := by
  let q : ℝ := xiShiftedMomentHankelQuadratic y (n + 2) x
  let W : ℝ := xiShiftedMomentHankelQuadraticLipschitzWeight x
  have hxne : x ≠ 0 := by
    intro hx
    rw [hx] at hneg
    exact (lt_irrefl (0 : ℝ))
      (by simpa only [xiShiftedMomentHankelQuadratic, zero_dotProduct] using hneg)
  have hW : 0 < W := xiShiftedMomentHankelQuadraticLipschitzWeight_pos_of_neg hy x hneg
  let δ : ℝ := -q
  let r : ℝ := δ / W
  have hδ : 0 < δ := by dsimp only [δ, q]; linarith
  have hr : 0 < r := div_pos hδ hW
  have hyv : y ≤ y + r := le_add_of_nonneg_right hr.le
  have hLip := abs_xiShiftedMomentHankelQuadratic_sub_le hy hyv x
  have hWr : W * r = δ := by
    dsimp only [r]
    field_simp
  have hquadNonpos : xiShiftedMomentHankelQuadratic (y + r) (n + 2) x ≤ 0 := by
    have hdiff :
        xiShiftedMomentHankelQuadratic (y + r) (n + 2) x -
            xiShiftedMomentHankelQuadratic y (n + 2) x ≤ W * r :=
      le_trans (le_abs_self _) (by simpa only [add_sub_cancel_left, W] using hLip)
    dsimp only [δ, q] at hWr
    linarith
  apply le_xiShiftedHigherBlockTerminalFrontier_of_mem
  refine ⟨hy.le.trans hyv, ?_⟩
  intro hpos
  have hstrict := hpos.dotProduct_mulVec_pos hxne
  have hquadPos : 0 < xiShiftedMomentHankelQuadratic (y + r) (n + 2) x := by
    exact hstrict
  exact (not_lt_of_ge hquadNonpos) hquadPos

/-- Choice-free quantitative landing of odd arithmetic source into frontier geometry.  Witness is
the adaptive mixed/completed shear itself, not an existentially selected eigenvector. -/
theorem add_adaptiveOddContactNegativeEnergy_div_lipschitzWeight_le_terminalFrontier
    {y : ℝ} (hy : 0 < y) {n : ℕ}
    (hflat : xiShiftedMomentHankelMatrix y (n + 1) *ᵥ
      HTGeometry.monicMomentAdmissionVector
        (fun k => (xiShiftedReciprocalMoment y k).re) n = 0)
    (hodd : xiShiftedHankelBoundaryMonicRemainder y
      (HTGeometry.monicMomentAdmissionVector
        (fun k => (xiShiftedReciprocalMoment y k).re) n) ≠ 0) :
    let c := HTGeometry.monicMomentAdmissionVector
      (fun k => (xiShiftedReciprocalMoment y k).re) n
    let x := xiShiftedOddContactAdaptiveHankelWitness y n c
    y + (-xiShiftedMomentHankelQuadratic y (n + 2) x) /
        (2 * (xiShiftedMomentHankelQuadraticLipschitzWeight x + 1)) ≤
      xiShiftedHigherBlockTerminalFrontier n := by
  dsimp only
  apply add_negHankelQuadratic_div_lipschitzWeight_le_terminalFrontier hy
  exact xiShiftedCanonicalOddContactAdaptiveHankelWitness_neg hflat hodd

/-- Sharp choice-free quantitative landing of odd arithmetic source into frontier geometry. -/
theorem add_adaptiveOddContactNegativeEnergy_div_lipschitzWeight_le_terminalFrontier_sharp
    {y : ℝ} (hy : 0 < y) {n : ℕ}
    (hflat : xiShiftedMomentHankelMatrix y (n + 1) *ᵥ
      HTGeometry.monicMomentAdmissionVector
        (fun k => (xiShiftedReciprocalMoment y k).re) n = 0)
    (hodd : xiShiftedHankelBoundaryMonicRemainder y
      (HTGeometry.monicMomentAdmissionVector
        (fun k => (xiShiftedReciprocalMoment y k).re) n) ≠ 0) :
    let c := HTGeometry.monicMomentAdmissionVector
      (fun k => (xiShiftedReciprocalMoment y k).re) n
    let x := xiShiftedOddContactAdaptiveHankelWitness y n c
    y + (-xiShiftedMomentHankelQuadratic y (n + 2) x) /
        xiShiftedMomentHankelQuadraticLipschitzWeight x ≤
      xiShiftedHigherBlockTerminalFrontier n := by
  dsimp only
  apply add_negHankelQuadratic_div_lipschitzWeight_le_terminalFrontier_sharp hy
  exact xiShiftedCanonicalOddContactAdaptiveHankelWitness_neg hflat hodd

/-- Exact sharp source-expanded frontier displacement. -/
theorem add_oddRemainderAdaptiveEnergy_div_lipschitzWeight_le_terminalFrontier_sharp
    {y : ℝ} (hy : 0 < y) {n : ℕ}
    (hflat : xiShiftedMomentHankelMatrix y (n + 1) *ᵥ
      HTGeometry.monicMomentAdmissionVector
        (fun k => (xiShiftedReciprocalMoment y k).re) n = 0)
    (hodd : xiShiftedHankelBoundaryMonicRemainder y
      (HTGeometry.monicMomentAdmissionVector
        (fun k => (xiShiftedReciprocalMoment y k).re) n) ≠ 0) :
    let s : ℕ → ℝ := fun k => (xiShiftedReciprocalMoment y k).re
    let c := HTGeometry.monicMomentAdmissionVector s n
    let a := s (2 * (n + 1))
    let Δ := xiShiftedHankelBoundaryMonicRemainder y c
    let x := xiShiftedOddContactAdaptiveHankelWitness y n c
    y + (Δ ^ (2 : ℕ) * (2 * (|a| + 1) - a) / (|a| + 1) ^ (2 : ℕ)) /
        xiShiftedMomentHankelQuadraticLipschitzWeight x ≤
      xiShiftedHigherBlockTerminalFrontier n := by
  have hfront :=
    add_adaptiveOddContactNegativeEnergy_div_lipschitzWeight_le_terminalFrontier_sharp
      hy hflat hodd
  dsimp only at hfront ⊢
  rw [xiShiftedCanonicalOddContactAdaptiveHankelWitness_energy_eq hflat] at hfront
  simpa only [neg_neg] using hfront

/-- Sharp robust source quotient with no completion artifact in frontier denominator. -/
theorem add_oddRemainderSq_div_terminalAbs_div_lipschitzWeight_le_terminalFrontier_sharp
    {y : ℝ} (hy : 0 < y) {n : ℕ}
    (hflat : xiShiftedMomentHankelMatrix y (n + 1) *ᵥ
      HTGeometry.monicMomentAdmissionVector
        (fun k => (xiShiftedReciprocalMoment y k).re) n = 0)
    (hodd : xiShiftedHankelBoundaryMonicRemainder y
      (HTGeometry.monicMomentAdmissionVector
        (fun k => (xiShiftedReciprocalMoment y k).re) n) ≠ 0) :
    let s : ℕ → ℝ := fun k => (xiShiftedReciprocalMoment y k).re
    let c := HTGeometry.monicMomentAdmissionVector s n
    let a := s (2 * (n + 1))
    let Δ := xiShiftedHankelBoundaryMonicRemainder y c
    let x := xiShiftedOddContactAdaptiveHankelWitness y n c
    y + (Δ ^ (2 : ℕ) / (|a| + 1)) /
        xiShiftedMomentHankelQuadraticLipschitzWeight x ≤
      xiShiftedHigherBlockTerminalFrontier n := by
  let s : ℕ → ℝ := fun k => (xiShiftedReciprocalMoment y k).re
  let c : Fin (n + 1) → ℝ := HTGeometry.monicMomentAdmissionVector s n
  let a := s (2 * (n + 1))
  let Δ := xiShiftedHankelBoundaryMonicRemainder y c
  let x := xiShiftedOddContactAdaptiveHankelWitness y n c
  have hneg : xiShiftedMomentHankelQuadratic y (n + 2) x < 0 := by
    exact xiShiftedCanonicalOddContactAdaptiveHankelWitness_neg hflat hodd
  have hfront :=
    add_negHankelQuadratic_div_lipschitzWeight_le_terminalFrontier_sharp hy x hneg
  have hlower :=
    hankelFirstOmittedCoupling_sq_div_terminalMomentAbs_add_one_le_neg_adaptiveEnergy
      c (by simpa only [s, c] using hflat)
  dsimp only at hfront hlower
  have hcoup : GaloisForLFunctions.HTGeometry.hankelFirstOmittedCoupling
      s (n + 1) c = Δ := by
    simpa only [s, c, Δ] using
      xiShiftedCanonicalAdmissionFirstOmittedCoupling_eq_monicRemainder y n
  rw [hcoup] at hlower
  change Δ ^ (2 : ℕ) / (|a| + 1) ≤
    -xiShiftedMomentHankelQuadratic y (n + 2) x at hlower
  have hW : 0 < xiShiftedMomentHankelQuadraticLipschitzWeight x :=
    xiShiftedMomentHankelQuadraticLipschitzWeight_pos_of_neg hy x hneg
  change y + (Δ ^ (2 : ℕ) / (|a| + 1)) /
      xiShiftedMomentHankelQuadraticLipschitzWeight x ≤
    xiShiftedHigherBlockTerminalFrontier n
  calc
    y + (Δ ^ (2 : ℕ) / (|a| + 1)) /
          xiShiftedMomentHankelQuadraticLipschitzWeight x ≤
        y + (-xiShiftedMomentHankelQuadratic y (n + 2) x) /
          xiShiftedMomentHankelQuadraticLipschitzWeight x := by
      exact add_le_add_right ((div_le_div_iff_of_pos_right hW).mpr hlower) y
    _ ≤ xiShiftedHigherBlockTerminalFrontier n := hfront

/-- Fully source-expanded displacement law.  Frontier advance is bounded below by odd monic
remainder squared, terminal-moment completion, and explicit global integral Lipschitz cost of the
same adaptive witness. -/
theorem add_oddRemainderAdaptiveEnergy_div_lipschitzWeight_le_terminalFrontier
    {y : ℝ} (hy : 0 < y) {n : ℕ}
    (hflat : xiShiftedMomentHankelMatrix y (n + 1) *ᵥ
      HTGeometry.monicMomentAdmissionVector
        (fun k => (xiShiftedReciprocalMoment y k).re) n = 0)
    (hodd : xiShiftedHankelBoundaryMonicRemainder y
      (HTGeometry.monicMomentAdmissionVector
        (fun k => (xiShiftedReciprocalMoment y k).re) n) ≠ 0) :
    let s : ℕ → ℝ := fun k => (xiShiftedReciprocalMoment y k).re
    let c := HTGeometry.monicMomentAdmissionVector s n
    let a := s (2 * (n + 1))
    let Δ := xiShiftedHankelBoundaryMonicRemainder y c
    let x := xiShiftedOddContactAdaptiveHankelWitness y n c
    y + (Δ ^ (2 : ℕ) * (2 * (|a| + 1) - a) / (|a| + 1) ^ (2 : ℕ)) /
        (2 * (xiShiftedMomentHankelQuadraticLipschitzWeight x + 1)) ≤
      xiShiftedHigherBlockTerminalFrontier n := by
  have hfront :=
    add_adaptiveOddContactNegativeEnergy_div_lipschitzWeight_le_terminalFrontier
      hy hflat hodd
  dsimp only at hfront ⊢
  rw [xiShiftedCanonicalOddContactAdaptiveHankelWitness_energy_eq hflat] at hfront
  simpa only [neg_neg] using hfront

/-- Robust source quotient.  Exact completion factor can be discarded without losing strict
content: odd remainder squared over terminal magnitude and actual integral Lipschitz cost still
forces a literal frontier displacement. -/
theorem add_oddRemainderSq_div_terminalAbs_div_lipschitzWeight_le_terminalFrontier
    {y : ℝ} (hy : 0 < y) {n : ℕ}
    (hflat : xiShiftedMomentHankelMatrix y (n + 1) *ᵥ
      HTGeometry.monicMomentAdmissionVector
        (fun k => (xiShiftedReciprocalMoment y k).re) n = 0)
    (hodd : xiShiftedHankelBoundaryMonicRemainder y
      (HTGeometry.monicMomentAdmissionVector
        (fun k => (xiShiftedReciprocalMoment y k).re) n) ≠ 0) :
    let s : ℕ → ℝ := fun k => (xiShiftedReciprocalMoment y k).re
    let c := HTGeometry.monicMomentAdmissionVector s n
    let a := s (2 * (n + 1))
    let Δ := xiShiftedHankelBoundaryMonicRemainder y c
    let x := xiShiftedOddContactAdaptiveHankelWitness y n c
    y + (Δ ^ (2 : ℕ) / (|a| + 1)) /
        (2 * (xiShiftedMomentHankelQuadraticLipschitzWeight x + 1)) ≤
      xiShiftedHigherBlockTerminalFrontier n := by
  let s : ℕ → ℝ := fun k => (xiShiftedReciprocalMoment y k).re
  let c : Fin (n + 1) → ℝ := HTGeometry.monicMomentAdmissionVector s n
  let a := s (2 * (n + 1))
  let Δ := xiShiftedHankelBoundaryMonicRemainder y c
  let x := xiShiftedOddContactAdaptiveHankelWitness y n c
  have hfront :=
    add_adaptiveOddContactNegativeEnergy_div_lipschitzWeight_le_terminalFrontier
      hy hflat hodd
  have hlower :=
    hankelFirstOmittedCoupling_sq_div_terminalMomentAbs_add_one_le_neg_adaptiveEnergy
      c (by simpa only [s, c] using hflat)
  dsimp only at hfront hlower
  have hcoup : GaloisForLFunctions.HTGeometry.hankelFirstOmittedCoupling
      s (n + 1) c = Δ := by
    simpa only [s, c, Δ] using
      xiShiftedCanonicalAdmissionFirstOmittedCoupling_eq_monicRemainder y n
  rw [hcoup] at hlower
  change Δ ^ (2 : ℕ) / (|a| + 1) ≤
    -xiShiftedMomentHankelQuadratic y (n + 2) x at hlower
  have hden : 0 < 2 * (xiShiftedMomentHankelQuadraticLipschitzWeight x + 1) := by
    have hW := xiShiftedMomentHankelQuadraticLipschitzWeight_nonneg x
    positivity
  change y + (Δ ^ (2 : ℕ) / (|a| + 1)) /
      (2 * (xiShiftedMomentHankelQuadraticLipschitzWeight x + 1)) ≤
    xiShiftedHigherBlockTerminalFrontier n
  calc
    y + (Δ ^ (2 : ℕ) / (|a| + 1)) /
          (2 * (xiShiftedMomentHankelQuadraticLipschitzWeight x + 1)) ≤
        y + (-xiShiftedMomentHankelQuadratic y (n + 2) x) /
          (2 * (xiShiftedMomentHankelQuadraticLipschitzWeight x + 1)) := by
      exact add_le_add_right ((div_le_div_iff_of_pos_right hden).mpr hlower) y
    _ ≤ xiShiftedHigherBlockTerminalFrontier n := by
      simpa only [s, c, x] using hfront

/-- **Quantitative odd-contact admission moat.**  A nonzero first omitted monic remainder produces
an actual negative Hankel direction whose normalized negative energy gives a literal lower bound
for displacement to the degree-`n` terminal frontier.  This is the exact arithmetic ratio that
future cumulative-growth arguments must bound from below. -/
theorem exists_add_negHankelQuadratic_div_lipschitzWeight_le_terminalFrontier_of_flatFace_nonzero_monicRemainder
    {y : ℝ} (hy : 0 < y) {n : ℕ}
    (hflat : xiShiftedMomentHankelMatrix y (n + 1) *ᵥ
      HTGeometry.monicMomentAdmissionVector
        (fun k => (xiShiftedReciprocalMoment y k).re) n = 0)
    (hodd : xiShiftedHankelBoundaryMonicRemainder y
      (HTGeometry.monicMomentAdmissionVector
        (fun k => (xiShiftedReciprocalMoment y k).re) n) ≠ 0) :
    ∃ x : Fin (n + 2) → ℝ,
      0 < -xiShiftedMomentHankelQuadratic y (n + 2) x ∧
      y + (-xiShiftedMomentHankelQuadratic y (n + 2) x) /
          (2 * (xiShiftedMomentHankelQuadraticLipschitzWeight x + 1)) ≤
        xiShiftedHigherBlockTerminalFrontier n := by
  let s : ℕ → ℝ := fun k => (xiShiftedReciprocalMoment y k).re
  let c : Fin (n + 1) → ℝ := HTGeometry.monicMomentAdmissionVector s n
  let x : Fin (n + 2) → ℝ := xiShiftedOddContactAdaptiveHankelWitness y n c
  have hcoupling : GaloisForLFunctions.HTGeometry.hankelFirstOmittedCoupling
      s (n + 1) c ≠ 0 := by
    rw [xiShiftedCanonicalAdmissionFirstOmittedCoupling_eq_monicRemainder]
    simpa only [s, c] using hodd
  have hneg : xiShiftedMomentHankelQuadratic y (n + 2) x < 0 := by
    exact xiShiftedMomentHankelQuadratic_oddContactAdaptiveHankelWitness_neg
      c (by simpa only [s, c] using hflat) hcoupling
  exact ⟨x, neg_pos.mpr hneg,
    add_negHankelQuadratic_div_lipschitzWeight_le_terminalFrontier hy x hneg⟩

/-- Every nonnegative mass strictly beyond the terminal frontier is in the positive chamber. -/
theorem xiShiftedHigherBlock_posDef_of_terminalFrontier_lt
    {n : ℕ} {y : ℝ} (hy0 : 0 ≤ y)
    (hy : xiShiftedHigherBlockTerminalFrontier n < y) :
    (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef := by
  by_contra hnot
  have hle := le_xiShiftedHigherBlockTerminalFrontier_of_mem
    (n := n) (y := y) ⟨hy0, hnot⟩
  exact (not_lt_of_ge hle) hy

/-- Every positive mass at or beyond a fixed terminal frontier has a positive-semidefinite block.
Strict inequality gives positive definiteness; equality is its closed quadratic-form limit from the
right. -/
theorem xiShiftedHigherBlock_posSemidef_of_terminalFrontier_le
    {n : ℕ} {y : ℝ} (hy : 0 < y)
    (hfront : xiShiftedHigherBlockTerminalFrontier n ≤ y) :
    (xiShiftedMomentHankelMatrix y (n + 2)).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨xiShiftedMomentHankelMatrix_isHermitian y (n + 2), ?_⟩
  intro x
  by_contra hnonneg
  rw [star_trivial] at hnonneg
  have hneg : xiShiftedMomentHankelQuadratic y (n + 2) x < 0 := by
    simpa only [xiShiftedMomentHankelQuadratic] using lt_of_not_ge hnonneg
  have hcontinuous : ContinuousAt
      (fun z => xiShiftedMomentHankelQuadratic z (n + 2) x) y :=
    (hasDerivAt_xiShiftedMomentHankelQuadratic hy (n + 2) x).continuousAt
  have heventuallyNeg : ∀ᶠ z in nhds y,
      xiShiftedMomentHankelQuadratic z (n + 2) x < 0 :=
    hcontinuous.eventually_lt continuousAt_const hneg
  have hright : ∀ᶠ z in nhdsWithin y (Set.Ioi y), y < z :=
    self_mem_nhdsWithin
  have heventuallyNegWithin : ∀ᶠ z in nhdsWithin y (Set.Ioi y),
      xiShiftedMomentHankelQuadratic z (n + 2) x < 0 :=
    heventuallyNeg.filter_mono inf_le_left
  obtain ⟨z, hzneg, hyz⟩ := (heventuallyNegWithin.and hright).exists
  have hz0 : 0 ≤ z := hy.le.trans hyz.le
  have hzpos : (xiShiftedMomentHankelMatrix z (n + 2)).PosDef :=
    xiShiftedHigherBlock_posDef_of_terminalFrontier_lt hz0
      (lt_of_le_of_lt hfront hyz)
  have hznonneg := hzpos.posSemidef.dotProduct_mulVec_nonneg x
  exact (not_lt_of_ge hznonneg) hzneg

/-- **Terminal-frontier odd-contact exclusion.**  At or beyond the closed degree-`n` terminal
frontier, every flat monic lower face has zero first omitted remainder.  Nonzero odd arithmetic
contact is therefore forced strictly into the ineffective region before that frontier. -/
theorem xiShiftedHankelBoundaryMonicRemainder_eq_zero_of_flatFace_of_terminalFrontier_le
    {y : ℝ} (hy : 0 < y) {n : ℕ}
    (hfront : xiShiftedHigherBlockTerminalFrontier n ≤ y)
    (hflat : xiShiftedMomentHankelMatrix y (n + 1) *ᵥ
      HTGeometry.monicMomentAdmissionVector
        (fun k => (xiShiftedReciprocalMoment y k).re) n = 0) :
    xiShiftedHankelBoundaryMonicRemainder y
      (HTGeometry.monicMomentAdmissionVector
        (fun k => (xiShiftedReciprocalMoment y k).re) n) = 0 := by
  exact xiShiftedHankelBoundaryMonicRemainder_eq_zero_of_flatFace_of_succ_posSemidef
    hflat (xiShiftedHigherBlock_posSemidef_of_terminalFrontier_le hy hfront)

/-- A genuinely indefinite block lies strictly before, not on, its fixed-degree terminal
frontier.  Frontier equality is always positive semidefinite by the preceding closure law. -/
theorem lt_xiShiftedHigherBlockTerminalFrontier_of_not_posSemidef
    {n : ℕ} {y : ℝ} (hy : 0 < y)
    (hnot : ¬ (xiShiftedMomentHankelMatrix y (n + 2)).PosSemidef) :
    y < xiShiftedHigherBlockTerminalFrontier n := by
  by_contra hle
  exact hnot
    (xiShiftedHigherBlock_posSemidef_of_terminalFrontier_le hy (le_of_not_gt hle))

/-- **Immediate odd-contact frontier separation.**  A nonzero first omitted monic remainder
does not merely force eventual exit at some higher degree: it forces the very next block to be
indefinite, hence places the contact strictly before its degree-`n` terminal frontier. -/
theorem lt_xiShiftedHigherBlockTerminalFrontier_of_flatFace_nonzero_monicRemainder
    {y : ℝ} (hy : 0 < y) {n : ℕ}
    (hflat : xiShiftedMomentHankelMatrix y (n + 1) *ᵥ
      HTGeometry.monicMomentAdmissionVector
        (fun k => (xiShiftedReciprocalMoment y k).re) n = 0)
    (hodd : xiShiftedHankelBoundaryMonicRemainder y
      (HTGeometry.monicMomentAdmissionVector
        (fun k => (xiShiftedReciprocalMoment y k).re) n) ≠ 0) :
    y < xiShiftedHigherBlockTerminalFrontier n := by
  exact lt_xiShiftedHigherBlockTerminalFrontier_of_not_posSemidef hy
    (xiShiftedMomentHankelMatrix_succ_not_posSemidef_of_flatFace_nonzero_monicRemainder
      hflat hodd)

/-- **Flat-face frontier escalation.**  Every positive effective singular face forces a strictly
larger terminal frontier at some finite weakly higher degree.  This combines deterministic finite
extension exit with closed frontier geometry, eliminating the putative branch where all higher
extensions remain positive semidefinite at the same mass. -/
theorem exists_later_xiShiftedHigherBlockTerminalFrontier_gt_of_flatFace
    {y : ℝ} (hy : 0 < y) {n : ℕ} (c : Fin (n + 1) → ℝ)
    (hhead : (xiShiftedMomentHankelMatrix y n).PosDef)
    (hc : xiShiftedMomentHankelMatrix y (n + 1) *ᵥ c = 0)
    (hlast : c (Fin.last n) ≠ 0) :
    ∃ k : ℕ, n ≤ k ∧ y < xiShiftedHigherBlockTerminalFrontier k := by
  obtain ⟨N, hN, hnot⟩ :=
    exists_xiShiftedMomentHankelMatrix_higher_not_posSemidef_of_flatFace
      hy c hhead hc hlast
  have hNtwo : 2 ≤ N := by omega
  refine ⟨N - 2, by omega, ?_⟩
  apply lt_xiShiftedHigherBlockTerminalFrontier_of_not_posSemidef
    (n := N - 2) hy
  have hidx : N - 2 + 2 = N := Nat.sub_add_cancel hNtwo
  rw [hidx]
  exact hnot

/-- A positive occupied terminal frontier is attained by an actual failed block.  This uses
closure of the supremum together with local openness of shifted-Xi positive definiteness, and
therefore removes nonattainment without assuming a rightmost determinant zero. -/
theorem xiShiftedHigherBlockTerminalFrontier_mem_failureSet
    {n : ℕ} (hne : (xiShiftedHigherBlockFailureSet n).Nonempty)
    (hfront : 0 < xiShiftedHigherBlockTerminalFrontier n) :
    xiShiftedHigherBlockTerminalFrontier n ∈ xiShiftedHigherBlockFailureSet n := by
  let τ := xiShiftedHigherBlockTerminalFrontier n
  have hclosure : τ ∈ closure (xiShiftedHigherBlockFailureSet n) :=
    csSup_mem_closure hne (bddAbove_xiShiftedHigherBlockFailureSet n)
  refine ⟨hfront.le, ?_⟩
  intro hpos
  have hposAdd := eventually_posDef_xiShiftedMomentHankelMatrix_add hfront hpos
  have hsub : Tendsto (fun v : ℝ => v - τ) (nhds τ) (nhds 0) := by
    have hc : ContinuousAt (fun _ : ℝ => τ) τ := continuousAt_const
    change Tendsto ((id : ℝ → ℝ) - fun _ : ℝ => τ) (nhds τ) (nhds 0)
    have ht : Tendsto ((id : ℝ → ℝ) - fun _ : ℝ => τ) (nhds τ)
        (nhds (((id : ℝ → ℝ) - fun _ : ℝ => τ) τ)) :=
      (continuousAt_id.sub hc).tendsto
    have hval : ((id : ℝ → ℝ) - fun _ : ℝ => τ) τ = (0 : ℝ) := by
      simp [Pi.sub_apply]
    rw [hval] at ht
    exact ht
  have hposAt : ∀ᶠ v in nhds τ,
      (xiShiftedMomentHankelMatrix v (n + 2)).PosDef := by
    filter_upwards [hsub.eventually hposAdd] with v hv
    simpa [τ] using hv
  have hfreq : ∃ᶠ v in nhds τ, v ∈ xiShiftedHigherBlockFailureSet n :=
    mem_closure_iff_frequently.mp hclosure
  obtain ⟨v, hvbad, hvpos⟩ := (hfreq.and_eventually hposAt).exists
  exact hvbad.2 hvpos

/-- Higher-block terminal frontiers are monotone in admission degree whenever the lower failure
set is occupied.  This follows from principal-block nesting, not from a chosen realization tree. -/
theorem xiShiftedHigherBlockTerminalFrontier_mono_succ
    {n : ℕ} (hne : (xiShiftedHigherBlockFailureSet n).Nonempty) :
    xiShiftedHigherBlockTerminalFrontier n ≤
      xiShiftedHigherBlockTerminalFrontier (n + 1) := by
  apply csSup_le hne
  intro y hy
  apply le_xiShiftedHigherBlockTerminalFrontier_of_mem
  refine ⟨hy.1, ?_⟩
  intro hlarge
  exact hy.2 (xiShiftedMomentHankel_posDef_of_le (by omega) hlarge)

/-- **Strict-frontier admission classification.**  A strict step of the canonical frontier
sequence is automatically an effective higher face: at the next frontier the previous principal
block is positive definite while the new block fails.  Simultaneous lower-head loss can therefore
occur only on a frontier plateau. -/
theorem xiShiftedHigherBlockTerminalFrontier_strict_step_effective
    {n : ℕ} (hne : (xiShiftedHigherBlockFailureSet n).Nonempty)
    (hstrict : xiShiftedHigherBlockTerminalFrontier n <
      xiShiftedHigherBlockTerminalFrontier (n + 1)) :
    let y := xiShiftedHigherBlockTerminalFrontier (n + 1)
    (xiShiftedMomentHankelMatrix y (n + 2)).PosDef ∧
      ¬(xiShiftedMomentHankelMatrix y (n + 3)).PosDef := by
  let y := xiShiftedHigherBlockTerminalFrontier (n + 1)
  have hneNext : (xiShiftedHigherBlockFailureSet (n + 1)).Nonempty := by
    obtain ⟨v, hv⟩ := hne
    refine ⟨v, hv.1, ?_⟩
    intro hlarge
    exact hv.2 (xiShiftedMomentHankel_posDef_of_le (by omega) hlarge)
  obtain ⟨v, hv⟩ := hne
  have hvle := le_xiShiftedHigherBlockTerminalFrontier_of_mem hv
  have hfrontPos : 0 < y := lt_of_le_of_lt (hv.1.trans hvle) hstrict
  have hyFail := xiShiftedHigherBlockTerminalFrontier_mem_failureSet hneNext hfrontPos
  have hhead : (xiShiftedMomentHankelMatrix y (n + 2)).PosDef :=
    xiShiftedHigherBlock_posDef_of_terminalFrontier_lt hyFail.1 hstrict
  refine ⟨hhead, ?_⟩
  change ¬(HTGeometry.momentHankelMatrix
    (fun k => (xiShiftedReciprocalMoment y k).re) (n + 3)).PosDef
  simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hyFail.2

/-- A strict terminal-frontier step is an actual singular positive-semidefinite higher face.
Right-of-frontier positivity and determinant analyticity exclude a negative determinant at the
frontier; the positive principal head then upgrades determinant nonnegativity to PSD. -/
theorem xiShiftedHigherBlockTerminalFrontier_strict_step_posSemidef
    {n : ℕ} (hne : (xiShiftedHigherBlockFailureSet n).Nonempty)
    (hstrict : xiShiftedHigherBlockTerminalFrontier n <
      xiShiftedHigherBlockTerminalFrontier (n + 1)) :
    let y := xiShiftedHigherBlockTerminalFrontier (n + 1)
    (xiShiftedMomentHankelMatrix y (n + 2)).PosDef ∧
      (xiShiftedMomentHankelMatrix y (n + 3)).PosSemidef ∧
      ¬(xiShiftedMomentHankelMatrix y (n + 3)).PosDef := by
  let y := xiShiftedHigherBlockTerminalFrontier (n + 1)
  have heffective :=
    xiShiftedHigherBlockTerminalFrontier_strict_step_effective hne hstrict
  dsimp only at heffective
  obtain ⟨v, hv⟩ := hne
  have hvle := le_xiShiftedHigherBlockTerminalFrontier_of_mem hv
  have hypos : 0 < y := lt_of_le_of_lt (hv.1.trans hvle) hstrict
  have hdet : 0 ≤ (xiShiftedMomentHankelMatrix y (n + 3)).det := by
    by_contra hnot
    have hdetneg : (xiShiftedMomentHankelMatrix y (n + 3)).det < 0 :=
      lt_of_not_ge hnot
    let f : ℝ → ℝ := fun u => (xiShiftedMomentHankelMatrix (y + u) (n + 3)).det
    have hf : ContinuousAt f 0 := by
      simpa only [f] using
        (hasFPowerSeriesAt_det_xiShiftedMomentHankelMatrix_add hypos (n + 3)).continuousAt
    have hf0 : f 0 < 0 := by
      simpa only [f, add_zero] using hdetneg
    have hneg : ∀ᶠ u in nhds 0, f u < 0 :=
      hf.eventually_lt continuousAt_const hf0
    have hnegWithin : ∀ᶠ u in nhdsWithin 0 (Set.Ioi 0), f u < 0 :=
      hneg.filter_mono inf_le_left
    have hright : ∀ᶠ u : ℝ in nhdsWithin 0 (Set.Ioi 0), 0 < u :=
      self_mem_nhdsWithin
    obtain ⟨u, hfu, hu⟩ := (hnegWithin.and hright).exists
    have hrightPos : (xiShiftedMomentHankelMatrix (y + u) (n + 3)).PosDef := by
      apply xiShiftedHigherBlock_posDef_of_terminalFrontier_lt (n := n + 1)
      · exact add_nonneg hypos.le hu.le
      · dsimp only [y]
        linarith
    have hdetpos := hrightPos.det_pos
    dsimp only [f] at hfu
    linarith
  have hpsd : (xiShiftedMomentHankelMatrix y (n + 3)).PosSemidef := by
    have hgate := xiShiftedMomentHankelMatrix_succ_posSemidef_iff_det_nonneg_of_head_posDef
      heffective.1
    have hdet' : 0 ≤ (xiShiftedMomentHankelMatrix y (n + 2 + 1)).det := by
      simpa only [Nat.add_assoc] using hdet
    have hpsd' := hgate.2 hdet'
    simpa only [Nat.add_assoc] using hpsd'
  exact ⟨heffective.1, hpsd, heffective.2⟩

/-- **No terminal plateau after a strict step.**  Every strict frontier step forces another
strictly larger frontier at some finite later degree.  The intervening contact may have either
parity and may contain finite rank-filled plateaus, but finite atomic exclusion and one-block
capacity prevent those plateaus from absorbing the escalation forever. -/
theorem exists_later_strict_xiShiftedHigherBlockTerminalFrontier_of_strict_step
    {n : ℕ} (hne : (xiShiftedHigherBlockFailureSet n).Nonempty)
    (hstrict : xiShiftedHigherBlockTerminalFrontier n <
      xiShiftedHigherBlockTerminalFrontier (n + 1)) :
    ∃ k : ℕ, n + 2 ≤ k ∧
      xiShiftedHigherBlockTerminalFrontier (n + 1) <
        xiShiftedHigherBlockTerminalFrontier k := by
  let y := xiShiftedHigherBlockTerminalFrontier (n + 1)
  have hface :=
    xiShiftedHigherBlockTerminalFrontier_strict_step_posSemidef hne hstrict
  dsimp only at hface
  have hy : 0 < y := by
    obtain ⟨v, hv⟩ := hne
    have hvle := le_xiShiftedHigherBlockTerminalFrontier_of_mem hv
    exact lt_of_le_of_lt (hv.1.trans hvle) hstrict
  have hdet : (xiShiftedMomentHankelMatrix y (n + 3)).det = 0 := by
    exact not_ne_iff.mp ((hface.2.1.posDef_iff_det_ne_zero).not.mp hface.2.2)
  obtain ⟨c, hcne, hc⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hlast : c (Fin.last (n + 2)) ≠ 0 :=
    xiShiftedHankelNullVector_terminal_ne_zero_of_head_posDef
      y (n + 2) c hface.1 hcne hc
  exact exists_later_xiShiftedHigherBlockTerminalFrontier_gt_of_flatFace
    hy c hface.1 hc hlast

/-- **Scalarized escalation law.**  A nonpositive literal completed producer inside an effective
block forces current mass strictly below the canonical last-failure frontier.  The existential
higher-face gap is therefore not genuine branching data; all choices project to one monotone
scalar obstruction. -/
theorem sq_lt_xiShiftedHigherBlockTerminalFrontier_of_traceCoupledSource_nonpos
    {w : ℝ} (hw : 1 / 2 < w) {n : ℕ} (hn : 0 < n)
    (hcurrent : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment (w ^ (2 : ℕ)) k).re) (n + 2)).PosDef)
    (hsource :
      xiShiftedTraceCoupledRiccatiCompletedDegreeCenteredArithmeticSource w n
        (HTGeometry.monicMomentAdmissionPolynomial
          (xiShiftedRealMomentSequence w) n) ≤ 0) :
    w ^ (2 : ℕ) < xiShiftedHigherBlockTerminalFrontier n := by
  obtain ⟨z, y, hwz, hy, hnot⟩ :=
    exists_future_xiShiftedHigherBlockGap_of_traceCoupledRiccatiCompletedSource_nonpos
      hw hn hcurrent hsource
  have hy0 : 0 ≤ y := by
    have hw0 : 0 < w := lt_trans (by norm_num) hw
    exact (sq_pos_of_pos hw0).le.trans hy.1.le
  have hle := le_xiShiftedHigherBlockTerminalFrontier_of_mem
    (n := n) (y := y) ⟨hy0, hnot⟩
  exact hy.1.trans_le hle

/-- The same source obstruction makes the degree-`n` failure set genuinely occupied. -/
theorem xiShiftedHigherBlockFailureSet_nonempty_of_traceCoupledSource_nonpos
    {w : ℝ} (hw : 1 / 2 < w) {n : ℕ} (hn : 0 < n)
    (hcurrent : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment (w ^ (2 : ℕ)) k).re) (n + 2)).PosDef)
    (hsource :
      xiShiftedTraceCoupledRiccatiCompletedDegreeCenteredArithmeticSource w n
        (HTGeometry.monicMomentAdmissionPolynomial
          (xiShiftedRealMomentSequence w) n) ≤ 0) :
    (xiShiftedHigherBlockFailureSet n).Nonempty := by
  obtain ⟨z, y, hwz, hy, hnot⟩ :=
    exists_future_xiShiftedHigherBlockGap_of_traceCoupledRiccatiCompletedSource_nonpos
      hw hn hcurrent hsource
  refine ⟨y, ?_⟩
  have hw0 : 0 < w := lt_trans (by norm_num) hw
  exact ⟨(sq_pos_of_pos hw0).le.trans hy.1.le, hnot⟩

/-- Under an actual completed-source obstruction, the canonical frontier is an attained failed
block rather than a merely supremal or nonclosed escape point. -/
theorem xiShiftedHigherBlockTerminalFrontier_mem_failureSet_of_traceCoupledSource_nonpos
    {w : ℝ} (hw : 1 / 2 < w) {n : ℕ} (hn : 0 < n)
    (hcurrent : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment (w ^ (2 : ℕ)) k).re) (n + 2)).PosDef)
    (hsource :
      xiShiftedTraceCoupledRiccatiCompletedDegreeCenteredArithmeticSource w n
        (HTGeometry.monicMomentAdmissionPolynomial
          (xiShiftedRealMomentSequence w) n) ≤ 0) :
    xiShiftedHigherBlockTerminalFrontier n ∈ xiShiftedHigherBlockFailureSet n := by
  apply xiShiftedHigherBlockTerminalFrontier_mem_failureSet
    (xiShiftedHigherBlockFailureSet_nonempty_of_traceCoupledSource_nonpos
      hw hn hcurrent hsource)
  have hw0 : 0 < w := lt_trans (by norm_num) hw
  exact (sq_pos_of_pos hw0).trans
    (sq_lt_xiShiftedHigherBlockTerminalFrontier_of_traceCoupledSource_nonpos
      hw hn hcurrent hsource)

/-- Source obstruction also activates monotone passage to the next terminal frontier. -/
theorem xiShiftedHigherBlockTerminalFrontier_le_succ_of_traceCoupledSource_nonpos
    {w : ℝ} (hw : 1 / 2 < w) {n : ℕ} (hn : 0 < n)
    (hcurrent : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment (w ^ (2 : ℕ)) k).re) (n + 2)).PosDef)
    (hsource :
      xiShiftedTraceCoupledRiccatiCompletedDegreeCenteredArithmeticSource w n
        (HTGeometry.monicMomentAdmissionPolynomial
          (xiShiftedRealMomentSequence w) n) ≤ 0) :
    xiShiftedHigherBlockTerminalFrontier n ≤
      xiShiftedHigherBlockTerminalFrontier (n + 1) :=
  xiShiftedHigherBlockTerminalFrontier_mono_succ
    (xiShiftedHigherBlockFailureSet_nonempty_of_traceCoupledSource_nonpos
      hw hn hcurrent hsource)

end
end RHTower
