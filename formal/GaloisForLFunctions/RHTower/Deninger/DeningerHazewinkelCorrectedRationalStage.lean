import GaloisForLFunctions.RHTower.Deninger.DeningerRationalWittCanonicalMultiplication
import GaloisForLFunctions.RHTower.Deninger.DeningerRationalWittHazewinkelHankel

/-!
# Corrected quantitative stages for rational Witt multiplication

Deninger's asserted stage law
`W_rat^{≤n} * W_rat^{≤m} ⊆ W_rat^{≤n+m}` is false.  This module supplies the
unconditional replacement over every commutative ring, including rings with nilpotents.

For normalized fractions `P/Q` and `R/S`, the four canonical resultant factors have degree
bounds `deg(P)deg(R)`, `deg(Q)deg(S)`, `deg(P)deg(S)`, and `deg(Q)deg(R)`.  Consequently the
cross-fraction product lies in stage

`(n - 1)(m - 1) + nm + 1`.

The proof first establishes the exact resultant degree over an algebraically closed field, descends
it through the universal integral coefficient ring, and then evaluates into an arbitrary target.
It also proves exhaustive and monotone rational stages, the valid additive `n+m` law, monotonicity
of Hankel-rank bounds, and the corrected product's explicit finite-Hankel-rank consequence.
-/

namespace RHTower

noncomputable section

open scoped BigOperators

/-- Ordinary multiplication on the literal rational-Witt additive carrier is commutative.

The carrier is presented as the kernel of a monoid hom, so this fact is not supplied by its
inherited typeclass even though the ambient localization is commutative. -/
lemma deningerRationalWittAdditive_mul_comm
    {A : Type*} [CommRing A] (x y : DeningerRationalWittAdditive A) :
    x * y = y * x := by
  apply Subtype.ext
  apply Units.ext
  change (x.1 : DeningerRationalWittLocalization A) *
      (y.1 : DeningerRationalWittLocalization A) = _
  exact mul_comm _ _

/-- Over an algebraically closed field, the normalized Witt resultant has exact product degree. -/
theorem deningerWittTensorPolynomial_natDegree_eq_mul_of_isAlgClosed
    {K : Type*} [Field K] [IsAlgClosed K]
    (P Q : Polynomial K) (hP : P.coeff 0 = 1) (hQ : Q.coeff 0 = 1) :
    (deningerWittTensorPolynomial P Q P.natDegree Q.natDegree).natDegree =
      P.natDegree * Q.natDegree := by
  let s := deningerNormalizedPolynomialRootUnits P hP
  let t := deningerNormalizedPolynomialRootUnits Q hQ
  have hPs : P = deningerRationalWittAtomPolynomial s := by
    simpa only [s, deningerRationalWittAtomPolynomial] using
      deningerPolynomial_eq_prod_normalizedRootUnits P hP
  have hQt : Q = deningerRationalWittAtomPolynomial t := by
    simpa only [t, deningerRationalWittAtomPolynomial] using
      deningerPolynomial_eq_prod_normalizedRootUnits Q hQ
  rw [hPs, hQt, deningerRationalWittAtomPolynomial_natDegree,
    deningerRationalWittAtomPolynomial_natDegree,
    deningerWittTensorPolynomial_atoms,
    deningerRationalWittAtomPolynomial_natDegree]
  simp [deningerPairAtoms, Multiset.card_bind]

/-- Exact product degree over the universal integral coefficient ring. -/
theorem deningerWittTensorPolynomial_natDegree_eq_mul_universal
    (P Q : Polynomial DeningerRationalWittUniversalRing)
    (hP : P.coeff 0 = 1) (hQ : Q.coeff 0 = 1) :
    (deningerWittTensorPolynomial P Q P.natDegree Q.natDegree).natDegree =
      P.natDegree * Q.natDegree := by
  let f := deningerRationalWittUniversalEmbedding
  have hf : Function.Injective f := deningerRationalWittUniversalEmbedding_injective
  have hmap := deningerWittTensorPolynomial_map f P Q P.natDegree Q.natDegree le_rfl hQ
  have hP0 : (P.map f).coeff 0 = 1 := by simp [hP]
  have hQ0 : (Q.map f).coeff 0 = 1 := by simp [hQ]
  have hPdeg : (P.map f).natDegree = P.natDegree :=
    Polynomial.natDegree_map_eq_of_injective hf P
  have hQdeg : (Q.map f).natDegree = Q.natDegree :=
    Polynomial.natDegree_map_eq_of_injective hf Q
  have htdeg :
      ((deningerWittTensorPolynomial P Q P.natDegree Q.natDegree).map f).natDegree =
        (deningerWittTensorPolynomial P Q P.natDegree Q.natDegree).natDegree :=
    Polynomial.natDegree_map_eq_of_injective hf _
  rw [hmap] at htdeg
  rw [← htdeg]
  simpa only [hPdeg, hQdeg] using
    deningerWittTensorPolynomial_natDegree_eq_mul_of_isAlgClosed
      (P.map f) (Q.map f) hP0 hQ0

/-- The canonical normalized Witt resultant has degree at most the product of input degrees over
every commutative ring.  Equality may drop after evaluation because coefficients may vanish or
become nilpotent; the upper bound survives without any reducedness hypothesis. -/
theorem deningerWittTensorPolynomial_natDegree_le_mul
    {A : Type*} [CommRing A]
    (P Q : Polynomial A) (hP : P.coeff 0 = 1) (hQ : Q.coeff 0 = 1) :
    (deningerWittTensorPolynomial P Q P.natDegree Q.natDegree).natDegree ≤
      P.natDegree * Q.natDegree := by
  let PU := deningerUniversalNormalizedPolynomial (0 : Fin 2) P.natDegree
  let QU := deningerUniversalNormalizedPolynomial (1 : Fin 2) Q.natDegree
  let ev := deningerUniversalNormalizedPolynomialEval P Q
  have hPU0 : PU.coeff 0 = 1 := by simp [PU]
  have hQU0 : QU.coeff 0 = 1 := by simp [QU]
  have hPUmap : PU.map ev = P := by
    simpa [PU, ev] using deningerUniversalNormalizedPolynomial_map_zero P Q hP
  have hQUmap : QU.map ev = Q := by
    simpa [QU, ev] using deningerUniversalNormalizedPolynomial_map_one P Q hQ
  have hPUdeg : PU.natDegree = P.natDegree := by simp [PU]
  have hQUdeg : QU.natDegree = Q.natDegree := by simp [QU]
  have hmap := deningerWittTensorPolynomial_map ev PU QU P.natDegree Q.natDegree
    (by simpa [hQUdeg]) hQU0
  rw [hPUmap, hQUmap] at hmap
  have hsource :
      (deningerWittTensorPolynomial PU QU P.natDegree Q.natDegree).natDegree =
        P.natDegree * Q.natDegree := by
    simpa only [hPUdeg, hQUdeg] using
      deningerWittTensorPolynomial_natDegree_eq_mul_universal PU QU hPU0 hQU0
  rw [← hmap]
  exact Polynomial.natDegree_map_le.trans_eq hsource

/-- Literal Deninger rational-Witt stage `W_rat^{≤n}`: numerator degree is `< n` and denominator
degree is `≤ n`. -/
def DeningerCanonicalRationalWittStageLE
    {A : Type*} [CommRing A]
    (n : ℕ) (w : DeningerCanonicalRationalWittRing A) : Prop :=
  ∃ (P Q : Polynomial A) (hP : P.coeff 0 = 1) (hQ : Q.coeff 0 = 1),
    P.natDegree + 1 ≤ n ∧ Q.natDegree ≤ n ∧
      w.additiveVal = Additive.ofMul
        (deningerRationalWittNormalizedFraction P Q hP hQ)

/-- Rational-Witt stages form an increasing filtration. -/
theorem DeningerCanonicalRationalWittStageLE.mono
    {A : Type*} [CommRing A] {n m : ℕ}
    {w : DeningerCanonicalRationalWittRing A}
    (h : DeningerCanonicalRationalWittStageLE n w) (hnm : n ≤ m) :
    DeningerCanonicalRationalWittStageLE m w := by
  obtain ⟨P, Q, hP, hQ, hPdeg, hQdeg, hw⟩ := h
  exact ⟨P, Q, hP, hQ, hPdeg.trans hnm, hQdeg.trans hnm, hw⟩

/-- The rational-Witt ring is exhausted by its finite normalized-fraction stages. -/
theorem deningerCanonicalRationalWitt_exists_stage
    {A : Type*} [CommRing A] (w : DeningerCanonicalRationalWittRing A) :
    ∃ n : ℕ, DeningerCanonicalRationalWittStageLE n w := by
  obtain ⟨P, Q, hQmem, hP, hQ, hw⟩ :=
    deningerRationalWittAdditive_exists_normalized_fraction A
      (Additive.toMul w.additiveVal)
  have heq := deningerRationalWitt_eq_normalizedFraction_of_val
    (Additive.toMul w.additiveVal) P Q hQmem hP hQ hw
  let n := max (P.natDegree + 1) Q.natDegree
  refine ⟨n, P, Q, hP, hQ, le_max_left _ _, le_max_right _ _, ?_⟩
  exact congrArg Additive.ofMul heq

/-- Deninger's additive `n+m` stage law is valid. -/
theorem DeningerCanonicalRationalWittStageLE.add
    {A : Type*} [CommRing A] {n m : ℕ}
    {x y : DeningerCanonicalRationalWittRing A}
    (hx : DeningerCanonicalRationalWittStageLE n x)
    (hy : DeningerCanonicalRationalWittStageLE m y) :
    DeningerCanonicalRationalWittStageLE (n + m) (x + y) := by
  obtain ⟨P, Q, hP, hQ, hPdeg, hQdeg, hx⟩ := hx
  obtain ⟨R, S, hR, hS, hRdeg, hSdeg, hy⟩ := hy
  have hPR : (P * R).coeff 0 = 1 := by simp [hP, hR]
  have hQS : (Q * S).coeff 0 = 1 := by simp [hQ, hS]
  refine ⟨P * R, Q * S, hPR, hQS, ?_, ?_, ?_⟩
  · calc
      (P * R).natDegree + 1 ≤ P.natDegree + R.natDegree + 1 :=
        Nat.add_le_add_right Polynomial.natDegree_mul_le 1
      _ ≤ n + m := by omega
  · exact Polynomial.natDegree_mul_le.trans (Nat.add_le_add hQdeg hSdeg)
  · rw [deningerCanonicalRationalWittRing_additiveVal_add, hx, hy]
    apply congrArg Additive.ofMul
    change deningerRationalWittNormalizedFraction P Q hP hQ *
        deningerRationalWittNormalizedFraction R S hR hS =
      deningerRationalWittNormalizedFraction (P * R) (Q * S) hPR hQS
    simp only [deningerRationalWittNormalizedFraction]
    rw [deningerRationalWittNormalizedPolynomial_mul P R hP hR,
      deningerRationalWittNormalizedPolynomial_mul Q S hQ hS, mul_inv_rev]
    letI : CommGroup (DeningerRationalWittAdditive A) :=
      { (inferInstance : Group (DeningerRationalWittAdditive A)) with
        mul_comm := deningerRationalWittAdditive_mul_comm }
    ac_rfl

/-- Corrected universal target stage for multiplication of rational-Witt stages `n` and `m`. -/
def deningerCorrectedWittMulStageBound (n m : ℕ) : ℕ :=
  (n - 1) * (m - 1) + n * m + 1

lemma deningerCorrectedWittMul_denominatorDegree_le_bound (n m : ℕ) :
    (n - 1) * m + n * (m - 1) ≤ deningerCorrectedWittMulStageBound n m := by
  cases n with
  | zero => simp [deningerCorrectedWittMulStageBound]
  | succ n =>
      cases m with
      | zero => simp [deningerCorrectedWittMulStageBound]
      | succ m =>
          simp only [Nat.succ_sub_one, deningerCorrectedWittMulStageBound]
          nlinarith

/-- Corrected quantitative multiplication theorem for Deninger's rational-Witt stages.

For inputs represented by `P/Q` and `R/S`, the output numerator is the product of the `PR` and
`QS` Witt resultants, while its denominator is the product of the `PS` and `QR` resultants. -/
theorem DeningerCanonicalRationalWittStageLE.mul
    {A : Type*} [CommRing A] {n m : ℕ}
    {x y : DeningerCanonicalRationalWittRing A}
    (hx : DeningerCanonicalRationalWittStageLE n x)
    (hy : DeningerCanonicalRationalWittStageLE m y) :
    DeningerCanonicalRationalWittStageLE
      (deningerCorrectedWittMulStageBound n m) (x * y) := by
  obtain ⟨P, Q, hP, hQ, hPdeg, hQdeg, hx⟩ := hx
  obtain ⟨R, S, hR, hS, hRdeg, hSdeg, hy⟩ := hy
  let PR := deningerWittTensorPolynomial P R P.natDegree R.natDegree
  let QS := deningerWittTensorPolynomial Q S Q.natDegree S.natDegree
  let PS := deningerWittTensorPolynomial P S P.natDegree S.natDegree
  let QR := deningerWittTensorPolynomial Q R Q.natDegree R.natDegree
  have hPR : PR.coeff 0 = 1 := by
    simpa [PR] using deningerWittTensorPolynomial_coeff_zero_arbitrary P R hP hR
  have hQS : QS.coeff 0 = 1 := by
    simpa [QS] using deningerWittTensorPolynomial_coeff_zero_arbitrary Q S hQ hS
  have hPS : PS.coeff 0 = 1 := by
    simpa [PS] using deningerWittTensorPolynomial_coeff_zero_arbitrary P S hP hS
  have hQR : QR.coeff 0 = 1 := by
    simpa [QR] using deningerWittTensorPolynomial_coeff_zero_arbitrary Q R hQ hR
  let N := PR * QS
  let D := PS * QR
  have hN : N.coeff 0 = 1 := by simp [N, hPR, hQS]
  have hD : D.coeff 0 = 1 := by simp [D, hPS, hQR]
  have hp : P.natDegree ≤ n - 1 := by omega
  have hr : R.natDegree ≤ m - 1 := by omega
  have hPRdeg : PR.natDegree ≤ P.natDegree * R.natDegree := by
    simpa [PR] using deningerWittTensorPolynomial_natDegree_le_mul P R hP hR
  have hQSdeg : QS.natDegree ≤ Q.natDegree * S.natDegree := by
    simpa [QS] using deningerWittTensorPolynomial_natDegree_le_mul Q S hQ hS
  have hPSdeg : PS.natDegree ≤ P.natDegree * S.natDegree := by
    simpa [PS] using deningerWittTensorPolynomial_natDegree_le_mul P S hP hS
  have hQRdeg : QR.natDegree ≤ Q.natDegree * R.natDegree := by
    simpa [QR] using deningerWittTensorPolynomial_natDegree_le_mul Q R hQ hR
  have hNdeg : N.natDegree + 1 ≤ deningerCorrectedWittMulStageBound n m := by
    calc
      N.natDegree + 1 ≤ PR.natDegree + QS.natDegree + 1 :=
        Nat.add_le_add_right Polynomial.natDegree_mul_le 1
      _ ≤ (P.natDegree * R.natDegree + Q.natDegree * S.natDegree) + 1 :=
        Nat.add_le_add_right (Nat.add_le_add hPRdeg hQSdeg) 1
      _ ≤ ((n - 1) * (m - 1) + n * m) + 1 :=
        Nat.add_le_add_right
          (Nat.add_le_add (Nat.mul_le_mul hp hr) (Nat.mul_le_mul hQdeg hSdeg)) 1
      _ = deningerCorrectedWittMulStageBound n m := rfl
  have hDdeg : D.natDegree ≤ deningerCorrectedWittMulStageBound n m := by
    calc
      D.natDegree ≤ PS.natDegree + QR.natDegree := Polynomial.natDegree_mul_le
      _ ≤ P.natDegree * S.natDegree + Q.natDegree * R.natDegree :=
        Nat.add_le_add hPSdeg hQRdeg
      _ ≤ (n - 1) * m + n * (m - 1) :=
        Nat.add_le_add (Nat.mul_le_mul hp hSdeg) (Nat.mul_le_mul hQdeg hr)
      _ ≤ deningerCorrectedWittMulStageBound n m :=
        deningerCorrectedWittMul_denominatorDegree_le_bound n m
  let x0 : DeningerCanonicalRationalWittRing A :=
    ⟨Additive.ofMul (deningerRationalWittNormalizedFraction P Q hP hQ)⟩
  let y0 : DeningerCanonicalRationalWittRing A :=
    ⟨Additive.ofMul (deningerRationalWittNormalizedFraction R S hR hS)⟩
  let u : DeningerCanonicalRationalWittRing A :=
    ⟨Additive.ofMul (deningerRationalWittNormalizedFraction N D hN hD)⟩
  have hx0 : x = x0 := by
    apply DeningerCanonicalRationalWittRing.ext
    exact hx
  have hy0 : y = y0 := by
    apply DeningerCanonicalRationalWittRing.ext
    exact hy
  have hu0 : u = x0 * y0 := by
    apply deningerCanonicalRationalWittEmbedding_injective
    rw [map_mul]
    change deningerRationalBigWittElement
        (deningerRationalWittNormalizedFraction N D hN hD) =
      deningerRationalBigWittElement
          (deningerRationalWittNormalizedFraction P Q hP hQ) *
        deningerRationalBigWittElement
          (deningerRationalWittNormalizedFraction R S hR hS)
    rw [deningerRationalBigWittElement_normalizedFraction,
      deningerNormalizedPolynomialBigWitt_add PR QS hPR hQS,
      deningerNormalizedPolynomialBigWitt_add PS QR hPS hQR,
      deningerRationalBigWittElement_normalizedFraction,
      deningerRationalBigWittElement_normalizedFraction]
    have hPRmul := deningerWittTensorPolynomial_bigWitt_mul_arbitrary P R hP hR
    have hQSmul := deningerWittTensorPolynomial_bigWitt_mul_arbitrary Q S hQ hS
    have hPSmul := deningerWittTensorPolynomial_bigWitt_mul_arbitrary P S hP hS
    have hQRmul := deningerWittTensorPolynomial_bigWitt_mul_arbitrary Q R hQ hR
    change deningerNormalizedPolynomialBigWitt PR hPR +
          deningerNormalizedPolynomialBigWitt QS hQS -
          (deningerNormalizedPolynomialBigWitt PS hPS +
            deningerNormalizedPolynomialBigWitt QR hQR) = _
    rw [show deningerNormalizedPolynomialBigWitt PR hPR =
        deningerNormalizedPolynomialBigWitt P hP *
          deningerNormalizedPolynomialBigWitt R hR by simpa [PR] using hPRmul.symm,
      show deningerNormalizedPolynomialBigWitt QS hQS =
        deningerNormalizedPolynomialBigWitt Q hQ *
          deningerNormalizedPolynomialBigWitt S hS by simpa [QS] using hQSmul.symm,
      show deningerNormalizedPolynomialBigWitt PS hPS =
        deningerNormalizedPolynomialBigWitt P hP *
          deningerNormalizedPolynomialBigWitt S hS by simpa [PS] using hPSmul.symm,
      show deningerNormalizedPolynomialBigWitt QR hQR =
        deningerNormalizedPolynomialBigWitt Q hQ *
          deningerNormalizedPolynomialBigWitt R hR by simpa [QR] using hQRmul.symm]
    ring
  have hu : u = x * y := by simpa [hx0, hy0] using hu0
  rw [← hu]
  exact ⟨N, D, hN, hD, hNdeg, hDdeg, rfl⟩

/-- The literal normalized fraction has its defining power-series identity. -/
theorem deningerRationalWittNormalizedFraction_powerSeries_mul_denominator
    {A : Type*} [CommRing A]
    (P Q : Polynomial A) (hP : P.coeff 0 = 1) (hQ : Q.coeff 0 = 1) :
    deningerBigWittSeries (deningerRationalWittToBigWittAdditive A
        (deningerRationalWittNormalizedFraction P Q hP hQ)) *
      (Q : PowerSeries A) = (P : PowerSeries A) := by
  have hwval := deningerRationalWittNormalizedFraction_val P Q hP hQ
  rw [eq_comm, IsLocalization.mk'_eq_iff_eq_mul] at hwval
  have hwvalps := congrArg (deningerRationalWittLocalizationToPowerSeries A) hwval
  have hwvalps' : (P : PowerSeries A) =
      deningerRationalWittLocalizationToPowerSeries A
          (((deningerRationalWittNormalizedFraction P Q hP hQ).1 :
            (DeningerRationalWittLocalization A)ˣ) :
            DeningerRationalWittLocalization A) *
        (Q : PowerSeries A) := by
    simpa [deningerRationalWittLocalizationToPowerSeries,
      IsLocalization.lift_eq] using hwvalps
  exact hwvalps'.symm

/-- Vanishing of all `d`-minors implies vanishing of every larger minor over an arbitrary
commutative ring. -/
theorem DeningerBigWittHankelRankLT.mono
    {A : Type*} [CommRing A] {d e : ℕ} {w : DeningerBigWittAdditive A}
    (h : DeningerBigWittHankelRankLT d w) (hde : d ≤ e) :
    DeningerBigWittHankelRankLT e w := by
  intro rows cols
  let H := deningerBigWittHankel w
  have hmem : (H.submatrix rows cols).det ∈ deningerMatrixMinorIdeal e H :=
    deningerMatrixMinorDet_mem e H rows cols
  have hcontain : deningerMatrixMinorIdeal e H ≤
      deningerMatrixMinorIdeal d H * deningerMatrixMinorIdeal (e - d) H := by
    calc
      deningerMatrixMinorIdeal e H =
          deningerMatrixMinorIdeal (d + (e - d)) H := by
            rw [Nat.add_sub_of_le hde]
      _ ≤ deningerMatrixMinorIdeal d H * deningerMatrixMinorIdeal (e - d) H :=
        deningerMatrixMinorIdeal_add_le_mul d (e - d) H
  have hId : deningerMatrixMinorIdeal d H = ⊥ := by
    apply le_antisymm
    · rw [deningerMatrixMinorIdeal, Ideal.span_le]
      rintro z ⟨r, c, rfl⟩
      simpa [H] using h r c
    · exact bot_le
  have hzero : (H.submatrix rows cols).det ∈ (⊥ : Ideal A) := by
    have hz := hcontain hmem
    simpa [hId] using hz
  simpa [H] using hzero

/-- Underlying big-Witt carrier of the canonical rational-Witt ring. -/
def deningerCanonicalRationalWittBigWittCarrier
    {A : Type*} [CommRing A]
    (w : DeningerCanonicalRationalWittRing A) : DeningerBigWittAdditive A :=
  Additive.toMul (deningerCanonicalRationalWittEmbedding w).additiveVal

/-- A rational vector in stage `n` has all `(n+1)`-Hankel minors zero. -/
theorem DeningerCanonicalRationalWittStageLE.hankelRankLT
    {A : Type*} [CommRing A] {n : ℕ}
    {w : DeningerCanonicalRationalWittRing A}
    (hstage : DeningerCanonicalRationalWittStageLE n w) :
    DeningerBigWittHankelRankLT (n + 1)
      (deningerCanonicalRationalWittBigWittCarrier w) := by
  obtain ⟨P, Q, hP, hQ, hPdeg, hQdeg, hw⟩ := hstage
  let d := max (P.natDegree + 1) Q.natDegree
  have hd : d ≤ n := max_le hPdeg hQdeg
  have hwcarrier : deningerCanonicalRationalWittBigWittCarrier w =
      deningerRationalWittToBigWittAdditive A
        (deningerRationalWittNormalizedFraction P Q hP hQ) := by
    change Additive.toMul
        (deningerRationalBigWittElement (Additive.toMul w.additiveVal)).additiveVal = _
    rw [hw]
    rfl
  rw [hwcarrier]
  let F := deningerBigWittSeries (deningerRationalWittToBigWittAdditive A
    (deningerRationalWittNormalizedFraction P Q hP hQ))
  have hrec : DeningerLinearRecurrenceFrom
      (fun k => PowerSeries.coeff k F) Q.coeff d := by
    apply linearRecurrenceFrom_of_powerSeries_mul_polynomial F P Q hQ
    exact deningerRationalWittNormalizedFraction_powerSeries_mul_denominator P Q hP hQ
  have hcol : DeningerHankelColumnGenerated
      (fun k => PowerSeries.coeff k F) d :=
    columnGenerated_of_linearRecurrenceFrom _ Q.coeff d hrec
  have hrank : DeningerBigWittHankelRankLT (d + 1)
      (deningerRationalWittToBigWittAdditive A
        (deningerRationalWittNormalizedFraction P Q hP hQ)) := by
    intro rows cols
    change (Matrix.submatrix (fun i j => PowerSeries.coeff (i + j) F)
      rows cols).det = 0
    exact hankelRankLT_succ_of_columnGenerated
      (fun k => PowerSeries.coeff k F) d hcol rows cols
  exact hrank.mono (Nat.add_le_add_right hd 1)

/-- Corrected finite-Hankel-rank output theorem for multiplication of rational stages. -/
theorem deningerCanonicalRationalWitt_mul_hankelRankLT_corrected
    {A : Type*} [CommRing A] {n m : ℕ}
    {x y : DeningerCanonicalRationalWittRing A}
    (hx : DeningerCanonicalRationalWittStageLE n x)
    (hy : DeningerCanonicalRationalWittStageLE m y) :
    DeningerBigWittHankelRankLT
      (deningerCorrectedWittMulStageBound n m + 1)
      (deningerCanonicalRationalWittBigWittCarrier (x * y)) :=
  (hx.mul hy).hankelRankLT

end

end RHTower
