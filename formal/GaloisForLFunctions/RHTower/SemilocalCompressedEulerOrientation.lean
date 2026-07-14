import GaloisForLFunctions.RHTower.SoninEulerFiniteGramLower
import GaloisForLFunctions.RHTower.SoninEssentialNormExtensions
import GaloisForLFunctions.RHTower.XiPrimeSeamCoherenceCollapse

/-!
# Semilocal orientation is a commutator created by the constraint

The concrete Hardy--Titchmarsh prime Euler Gram operators are commuting multiplication
operators.  Their compressions to the Sonin boundary carrier need not commute.  This file proves
that the compressed commutator is exactly the negative antisymmetric cross-boundary Gram.

For a finite prime packet and coefficients `u_p`, the resulting orientation Gram is

`sum_(p,q) (u_p-u_q) C_p^* C_q`,

where `C_p` is the literal positive Euler corner.  Hence this Gram is the negative commutator of
the compression of the `u`-weighted Euler source with the compression of the unweighted source.
The existing finite quadratic Calkin injection then proves that this commutator is compact exactly
when every coefficient in the packet agrees.

For the canonical Xi prime-seam coefficients, essential commutation on every actual Xi divisor
fibre implies prime-seam coherence, cofinal decay kills the common charge, and RH follows.  The
remaining source problem is therefore a concrete essential-commutation value relation; no moving
projection, zero-locus selection, or limiting measure occurs in its statement.
-/

open Complex
open MeasureTheory
open scoped InnerProductSpace

namespace RHTower

noncomputable section

variable {E : Type*} [Ring E]

/-- Compressing two commuting elements creates precisely the negative skew product of their
opposite boundary corners. -/
theorem compression_commutator_eq_neg_boundary_skew
    {e a b : E} (he : IsIdempotentElem e) (hab : a * b = b * a) :
    (e * a * e) * (e * b * e) - (e * b * e) * (e * a * e) =
      -((e * a * (1 - e)) * ((1 - e) * b * e) -
        (e * b * (1 - e)) * ((1 - e) * a * e)) := by
  have hsemi_ab := compression_semicommutator he a b
  have hsemi_ba := compression_semicommutator he b a
  have hX : (e * a * e) * (e * b * e) =
      e * (a * b) * e - (e * a * (1 - e)) * ((1 - e) * b * e) := by
    calc
      (e * a * e) * (e * b * e) =
          e * (a * b) * e -
            (e * (a * b) * e - (e * a * e) * (e * b * e)) := by abel
      _ = _ := by rw [hsemi_ab]
  have hY : (e * b * e) * (e * a * e) =
      e * (b * a) * e - (e * b * (1 - e)) * ((1 - e) * a * e) := by
    calc
      (e * b * e) * (e * a * e) =
          e * (b * a) * e -
            (e * (b * a) * e - (e * b * e) * (e * a * e)) := by abel
      _ = _ := by rw [hsemi_ba]
  have hZ : e * (a * b) * e = e * (b * a) * e := by rw [hab]
  rw [hX, hY, hZ]
  abel

/-- The adjoint of a lower corner is the upper corner of the adjoint source. -/
theorem adjoint_crossBoundary_eq_upperBoundary_of_adjoint_eq
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (P A B : H →L[ℂ] H)
    (hP : ContinuousLinearMap.adjoint P = P)
    (hA : ContinuousLinearMap.adjoint A = B) :
    ContinuousLinearMap.adjoint (crossBoundary P A) = upperBoundary P B := by
  unfold crossBoundary upperBoundary
  change ContinuousLinearMap.adjoint (((1 - P) * A) ∘L P) = _
  rw [ContinuousLinearMap.adjoint_comp]
  change ContinuousLinearMap.adjoint P ∘L
    ContinuousLinearMap.adjoint ((1 - P) ∘L A) = _
  rw [ContinuousLinearMap.adjoint_comp, adjoint_one_sub hP, hA, hP]
  rfl

/-- Self-adjoint specialization of the lower/upper corner adjoint identity. -/
theorem adjoint_crossBoundary_eq_upperBoundary
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (P A : H →L[ℂ] H)
    (hP : ContinuousLinearMap.adjoint P = P)
    (hA : ContinuousLinearMap.adjoint A = A) :
    ContinuousLinearMap.adjoint (crossBoundary P A) = upperBoundary P A :=
  adjoint_crossBoundary_eq_upperBoundary_of_adjoint_eq P A A hP hA

/-- Literal prime Euler Grams commute before imposing the Sonin constraint: they are pointwise
multipliers on the common Hardy--Titchmarsh line. -/
theorem archimedeanPrimeEulerGram_commute
    (p q : ℝ) (hp : 1 < p) (hq : 1 < q) :
    archimedeanPrimeEulerGram p * archimedeanPrimeEulerGram q =
      archimedeanPrimeEulerGram q * archimedeanPrimeEulerGram p := by
  apply ContinuousLinearMap.ext
  intro g
  apply Lp.ext
  filter_upwards [
    archimedeanPrimeEulerGram_ae q hq g,
    archimedeanPrimeEulerGram_ae p hp (archimedeanPrimeEulerGram q g),
    archimedeanPrimeEulerGram_ae p hp g,
    archimedeanPrimeEulerGram_ae q hq (archimedeanPrimeEulerGram p g)] with
      s hqg hpq hpg hqp
  change archimedeanPrimeEulerGram p (archimedeanPrimeEulerGram q g) s =
    archimedeanPrimeEulerGram q (archimedeanPrimeEulerGram p g) s
  rw [hpq, hqp, hqg, hpg]
  ring

/-- A finite coefficient-weighted sum of literal Euler Gram multipliers. -/
def finiteArchimedeanEulerSource
    {n : ℕ} (r : Fin n → ℝ) (c : Fin n → ℂ) :
    ArchimedeanWeightedL2 →L[ℂ] ArchimedeanWeightedL2 :=
  ∑ i, c i • archimedeanPrimeEulerGram (r i)

/-- Adjointing a finite Euler source conjugates its coefficient packet. -/
theorem adjoint_finiteArchimedeanEulerSource
    {n : ℕ} (r : Fin n → ℝ) (c : Fin n → ℂ) :
    ContinuousLinearMap.adjoint (finiteArchimedeanEulerSource r c) =
      finiteArchimedeanEulerSource r (fun i ↦ star (c i)) := by
  classical
  unfold finiteArchimedeanEulerSource
  change star (∑ i ∈ Finset.univ, c i • archimedeanPrimeEulerGram (r i)) = _
  rw [star_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [star_smul]
  change star (c i) • ContinuousLinearMap.adjoint
    (archimedeanPrimeEulerGram (r i)) = _
  rw [adjoint_archimedeanPrimeEulerGram]

/-- Any two finite Euler sources on the same scale packet commute before compression. -/
theorem finiteArchimedeanEulerSource_commute
    {n : ℕ} (r : Fin n → ℝ) (hr : ∀ i, 1 < r i)
    (c d : Fin n → ℂ) :
    finiteArchimedeanEulerSource r c * finiteArchimedeanEulerSource r d =
      finiteArchimedeanEulerSource r d * finiteArchimedeanEulerSource r c := by
  classical
  unfold finiteArchimedeanEulerSource
  simp only [Finset.sum_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  have hcomm := archimedeanPrimeEulerGram_commute
    (r i) (r j) (hr i) (hr j)
  rw [smul_mul_assoc, mul_smul_comm, smul_mul_assoc, mul_smul_comm]
  rw [hcomm]
  module

/-- Compression of a finite Euler source by the actual archimedean Sonin carrier projection. -/
def finiteArchimedeanEulerCompression
    {n : ℕ} (a : ℝ) (r : Fin n → ℝ) (c : Fin n → ℂ) :
    ArchimedeanWeightedL2 →L[ℂ] ArchimedeanWeightedL2 :=
  compression (archimedeanBoundaryCarrierProjection a)
    (finiteArchimedeanEulerSource r c)

/-- The zero-diagonal orientation matrix attached to a coefficient packet. -/
def finiteEulerOrientationMatrix
    {n : ℕ} (u : Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j ↦ u i - u j

/-- The literal finite Euler Gram carrying every ordered coefficient difference. -/
def finiteArchimedeanEulerOrientationGram
    {n : ℕ} (a : ℝ) (r : Fin n → ℝ) (u : Fin n → ℂ) :
    ArchimedeanWeightedL2 →L[ℂ] ArchimedeanWeightedL2 :=
  finiteArchimedeanPrimeEulerGramCombination a r (finiteEulerOrientationMatrix u)

/-- The boundary corner of a finite source is the corresponding finite sum of literal Euler
corners. -/
theorem crossBoundary_finiteArchimedeanEulerSource
    {n : ℕ} (a : ℝ) (r : Fin n → ℝ) (c : Fin n → ℂ) :
    crossBoundary (archimedeanBoundaryCarrierProjection a)
        (finiteArchimedeanEulerSource r c) =
      ∑ i, c i • archimedeanPrimeEulerCorner a (r i) := by
  classical
  unfold finiteArchimedeanEulerSource archimedeanPrimeEulerCorner crossBoundary
  simp only [Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc]

/-- Exterior factorization of the finite orientation Gram by the conjugate, universal, and
original source sections. -/
theorem finiteArchimedeanEulerOrientationGram_eq_boundary_skew
    {n : ℕ} (a : ℝ) (r : Fin n → ℝ) (u : Fin n → ℂ) :
    finiteArchimedeanEulerOrientationGram a r u =
      ContinuousLinearMap.adjoint
          (crossBoundary (archimedeanBoundaryCarrierProjection a)
            (finiteArchimedeanEulerSource r (fun i ↦ star (u i)))) *
        crossBoundary (archimedeanBoundaryCarrierProjection a)
          (finiteArchimedeanEulerSource r (fun _ ↦ 1)) -
      ContinuousLinearMap.adjoint
          (crossBoundary (archimedeanBoundaryCarrierProjection a)
            (finiteArchimedeanEulerSource r (fun _ ↦ 1))) *
        crossBoundary (archimedeanBoundaryCarrierProjection a)
          (finiteArchimedeanEulerSource r u) := by
  classical
  rw [crossBoundary_finiteArchimedeanEulerSource,
    crossBoundary_finiteArchimedeanEulerSource,
    crossBoundary_finiteArchimedeanEulerSource]
  unfold finiteArchimedeanEulerOrientationGram
    finiteArchimedeanPrimeEulerGramCombination finiteEulerOrientationMatrix
  simp only [one_smul]
  change (∑ i, ∑ j, (u i - u j) •
      (ContinuousLinearMap.adjoint (archimedeanPrimeEulerCorner a (r i)) ∘L
        archimedeanPrimeEulerCorner a (r j))) = _
  change _ = star (∑ i, star (u i) • archimedeanPrimeEulerCorner a (r i)) *
      (∑ j, archimedeanPrimeEulerCorner a (r j)) -
    star (∑ i, archimedeanPrimeEulerCorner a (r i)) *
      (∑ j, u j • archimedeanPrimeEulerCorner a (r j))
  simp only [star_sum, star_smul, star_star, Finset.sum_mul, Finset.mul_sum,
    mul_smul_comm, smul_mul_assoc]
  conv_rhs =>
    lhs
    rw [Finset.sum_comm]
  conv_rhs =>
    rhs
    simp only [Finset.smul_sum]
    rw [Finset.sum_comm]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  module

/-- Constraint--orientation identity: the finite orientation Gram is the negative commutator of
the weighted and universal compressed Euler sources. -/
theorem finiteArchimedeanEulerOrientationGram_eq_neg_compression_commutator
    {n : ℕ} (a : ℝ) (r : Fin n → ℝ) (hr : ∀ i, 1 < r i)
    (u : Fin n → ℂ) :
    finiteArchimedeanEulerOrientationGram a r u =
      -(finiteArchimedeanEulerCompression a r u *
          finiteArchimedeanEulerCompression a r (fun _ ↦ 1) -
        finiteArchimedeanEulerCompression a r (fun _ ↦ 1) *
          finiteArchimedeanEulerCompression a r u) := by
  let P := archimedeanBoundaryCarrierProjection a
  let A := finiteArchimedeanEulerSource r u
  let Astar := finiteArchimedeanEulerSource r (fun i ↦ star (u i))
  let B := finiteArchimedeanEulerSource r (fun _ ↦ 1)
  have hPidem : IsIdempotentElem P :=
    isIdempotentElem_archimedeanBoundaryCarrierProjection a
  have hPadj : ContinuousLinearMap.adjoint P = P :=
    adjoint_archimedeanBoundaryCarrierProjection a
  have hAstar : ContinuousLinearMap.adjoint Astar = A := by
    dsimp [Astar, A]
    rw [adjoint_finiteArchimedeanEulerSource]
    congr 1
    funext i
    simp
  have hBadj : ContinuousLinearMap.adjoint B = B := by
    dsimp [B]
    rw [adjoint_finiteArchimedeanEulerSource]
    congr 1
    funext i
    simp
  have hcomm : A * B = B * A := by
    exact finiteArchimedeanEulerSource_commute r hr u (fun _ ↦ 1)
  have hboundaryA : ContinuousLinearMap.adjoint (crossBoundary P Astar) =
      upperBoundary P A :=
    adjoint_crossBoundary_eq_upperBoundary_of_adjoint_eq P Astar A hPadj hAstar
  have hboundaryB : ContinuousLinearMap.adjoint (crossBoundary P B) =
      upperBoundary P B :=
    adjoint_crossBoundary_eq_upperBoundary P B hPadj hBadj
  have hcommutator := compression_commutator_eq_neg_boundary_skew
    hPidem hcomm
  rw [finiteArchimedeanEulerOrientationGram_eq_boundary_skew]
  change ContinuousLinearMap.adjoint (crossBoundary P Astar) * crossBoundary P B -
      ContinuousLinearMap.adjoint (crossBoundary P B) * crossBoundary P A = _
  rw [hboundaryA, hboundaryB]
  change upperBoundary P A * crossBoundary P B -
      upperBoundary P B * crossBoundary P A =
    -(compression P A * compression P B - compression P B * compression P A)
  unfold upperBoundary crossBoundary compression
  rw [hcommutator]
  simp

/-- A finite orientation matrix vanishes exactly when its coefficient packet is constant. -/
theorem finiteEulerOrientationMatrix_eq_zero_iff
    {n : ℕ} (u : Fin n → ℂ) :
    finiteEulerOrientationMatrix u = 0 ↔ ∀ i j, u i = u j := by
  constructor
  · intro hzero i j
    have hij := congrFun (congrFun hzero i) j
    simpa [finiteEulerOrientationMatrix] using sub_eq_zero.mp hij
  · intro hcoh
    ext i j
    simp [finiteEulerOrientationMatrix, hcoh i j]

/-- Finite quadratic Calkin faithfulness: the orientation Gram is compact exactly for a constant
coefficient packet. -/
theorem finitePrimeArchimedeanEulerOrientationGram_isCompactOperator_iff
    {n : ℕ} (a : ℝ) (ha : 0 < a) (p : Fin n → ℕ)
    (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (u : Fin n → ℂ) :
    IsCompactOperator
        (finiteArchimedeanEulerOrientationGram a (fun i ↦ (p i : ℝ)) u) ↔
      ∀ i j, u i = u j := by
  constructor
  · intro hcompact i j
    by_contra hij
    have hmatrix : finiteEulerOrientationMatrix u ≠ 0 := by
      exact (finiteEulerOrientationMatrix_eq_zero_iff u).not.mpr
        (not_forall.mpr ⟨i, not_forall.mpr ⟨j, hij⟩⟩)
    exact finitePrimeArchimedeanEulerGram_not_isCompactOperator_of_ne_zero
      a ha p hp hinj (finiteEulerOrientationMatrix u) hmatrix hcompact
  · intro hcoh
    have hmatrix : finiteEulerOrientationMatrix u = 0 :=
      (finiteEulerOrientationMatrix_eq_zero_iff u).mpr hcoh
    rw [finiteArchimedeanEulerOrientationGram, hmatrix]
    simp [finiteArchimedeanPrimeEulerGramCombination]
    exact isCompactOperator_zero

/-- Essential commutation of the two compressed finite sources is equivalent to constancy of the
coefficient packet. -/
theorem finitePrimeArchimedeanEulerCompression_commutator_isCompactOperator_iff
    {n : ℕ} (a : ℝ) (ha : 0 < a) (p : Fin n → ℕ)
    (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (u : Fin n → ℂ) :
    IsCompactOperator
        (finiteArchimedeanEulerCompression a (fun i ↦ (p i : ℝ)) u *
            finiteArchimedeanEulerCompression a (fun i ↦ (p i : ℝ)) (fun _ ↦ 1) -
          finiteArchimedeanEulerCompression a (fun i ↦ (p i : ℝ)) (fun _ ↦ 1) *
            finiteArchimedeanEulerCompression a (fun i ↦ (p i : ℝ)) u) ↔
      ∀ i j, u i = u j := by
  let r : Fin n → ℝ := fun i ↦ (p i : ℝ)
  let hr : ∀ i, 1 < r i := fun i ↦ by
    change (1 : ℝ) < (p i : ℝ)
    exact_mod_cast (hp i).one_lt
  let T := finiteArchimedeanEulerCompression a r u *
      finiteArchimedeanEulerCompression a r (fun _ ↦ 1) -
    finiteArchimedeanEulerCompression a r (fun _ ↦ 1) *
      finiteArchimedeanEulerCompression a r u
  have horientation : finiteArchimedeanEulerOrientationGram a r u = -T :=
    finiteArchimedeanEulerOrientationGram_eq_neg_compression_commutator
      a r hr u
  rw [← finitePrimeArchimedeanEulerOrientationGram_isCompactOperator_iff
    a ha p hp hinj u]
  change IsCompactOperator T ↔
    IsCompactOperator (finiteArchimedeanEulerOrientationGram a r u)
  rw [horientation]
  constructor
  · exact fun hT ↦ hT.neg
  · intro hneg
    have h := hneg.neg
    have heq : -(fun x ↦ (-T) x) = (fun x ↦ T x) := by
      funext x
      simp
    rw [heq] at h
    exact h

/-- On every Xi divisor fibre, every finite packet of seam-weighted and unweighted compressed
Euler sources commutes modulo compact operators. -/
def XiFiniteEulerCompressionEssentiallyCommuting (a : ℝ) : Prop :=
  ∀ (rho : XiDivisorSupport) (n : ℕ) (p : Fin n → ℕ),
    (∀ i, (p i).Prime) → Function.Injective p →
      IsCompactOperator
        (finiteArchimedeanEulerCompression a (fun i ↦ (p i : ℝ))
              (fun i ↦ orbitwiseNatPrimeSeamCharge (p i) (rho : ℂ)) *
            finiteArchimedeanEulerCompression a (fun i ↦ (p i : ℝ)) (fun _ ↦ 1) -
          finiteArchimedeanEulerCompression a (fun i ↦ (p i : ℝ)) (fun _ ↦ 1) *
            finiteArchimedeanEulerCompression a (fun i ↦ (p i : ℝ))
              (fun i ↦ orbitwiseNatPrimeSeamCharge (p i) (rho : ℂ)))

/-- Top-down endpoint: essential commutation of the concrete finite Euler source compressions on
all Xi divisor fibres is equivalent to RH. -/
theorem xiFiniteEulerCompressionEssentiallyCommuting_iff_riemannHypothesis
    (a : ℝ) (ha : 0 < a) :
    XiFiniteEulerCompressionEssentiallyCommuting a ↔ RiemannHypothesis := by
  constructor
  · intro hsource
    apply riemannHypothesis_of_xiPrimeSeamChargesCoherent
    intro rho p q hp hq
    by_cases hpq : p = q
    · simp [hpq]
    let packet : Fin 2 → ℕ := ![p, q]
    have hpacketPrime : ∀ i, (packet i).Prime := by
      intro i
      fin_cases i <;> simp [packet, hp, hq]
    have hpacketInj : Function.Injective packet := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [packet]
    have hcompact := hsource rho 2 packet hpacketPrime hpacketInj
    have hcoh :=
      (finitePrimeArchimedeanEulerCompression_commutator_isCompactOperator_iff
        a ha packet hpacketPrime hpacketInj
        (fun i ↦ orbitwiseNatPrimeSeamCharge (packet i) (rho : ℂ))).mp hcompact
    have h01 := hcoh (0 : Fin 2) (1 : Fin 2)
    simpa [packet] using h01
  · intro hRH rho n p hp hinj
    have hcoherent : XiPrimeSeamChargesCoherent :=
      xiPrimeSeamChargesCoherent_iff_riemannHypothesis.mpr hRH
    exact (finitePrimeArchimedeanEulerCompression_commutator_isCompactOperator_iff
      a ha p hp hinj
      (fun i ↦ orbitwiseNatPrimeSeamCharge (p i) (rho : ℂ))).mpr
        (fun i j ↦ hcoherent rho (p i) (p j) (hp i) (hp j))

end

end RHTower
