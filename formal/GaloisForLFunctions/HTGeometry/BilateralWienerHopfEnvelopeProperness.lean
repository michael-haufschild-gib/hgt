import GaloisForLFunctions.HTGeometry.ConstitutiveMonoidBialgebraHopfEnvelope
import GaloisForLFunctions.HTGeometry.DirectedLiteralSourceFormationRecoveryProperness

/-!
# Bilateral Wiener--Hopf envelope properness

The coefficient `ell^(1 : ℕ)` source size on finite Laurent packets admits bounded evaluation exactly at
unitary characters.  Actual marked formation and exact rank recovery are one Laurent identity.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open _root_.RHTower

/-- Finite coefficient-native packets in the reversible rank Hopf envelope. -/
abbrev BilateralWienerPacket := LaurentPolynomial ℂ

/-- Coefficient `ell^(1 : ℕ)` size of a finite bilateral source packet. -/
def bilateralWienerPacketNorm (f : BilateralWienerPacket) : ℝ :=
  f.coeff.sum fun _ a => ‖a‖

/-- Multiplicative character `e ↦ z^e` of the integer rank group. -/
def bilateralWienerCharacterHom (z : ℂ) (hz : z ≠ 0) : Multiplicative ℤ →* ℂ :=
  (Units.coeHom ℂ).comp (zpowersHom ℂˣ (Units.mk0 z hz))

/-- Algebraic evaluation of a finite Laurent source packet at a nonzero character. -/
def bilateralWienerEval (z : ℂ) (hz : z ≠ 0) :
    BilateralWienerPacket →ₐ[ℂ] ℂ :=
  AddMonoidAlgebra.lift ℂ ℂ ℤ (bilateralWienerCharacterHom z hz)

/-- Coefficient formula for bilateral evaluation. -/
theorem bilateralWienerEval_eq_sum
    (z : ℂ) (hz : z ≠ 0) (f : BilateralWienerPacket) :
    bilateralWienerEval z hz f = f.coeff.sum fun e a => a * z ^ e := by
  rw [bilateralWienerEval, AddMonoidAlgebra.lift_apply]
  apply Finsupp.sum_congr
  intro e _he
  simp [bilateralWienerCharacterHom, smul_eq_mul]

/-- Evaluation of one Laurent rank basis packet. -/
@[simp] theorem bilateralWienerEval_T
    (z : ℂ) (hz : z ≠ 0) (e : ℤ) :
    bilateralWienerEval z hz (LaurentPolynomial.T e) = z ^ e := by
  rw [LaurentPolynomial.T, bilateralWienerEval, AddMonoidAlgebra.lift_single]
  simp [bilateralWienerCharacterHom]

/-- Every Laurent rank basis packet has coefficient size one. -/
@[simp] theorem bilateralWienerPacketNorm_T (e : ℤ) :
    bilateralWienerPacketNorm (LaurentPolynomial.T e : BilateralWienerPacket) = 1 := by
  rw [bilateralWienerPacketNorm]
  change (Finsupp.single e (1 : ℂ)).sum (fun _ a => ‖a‖) = 1
  simp

/-- A unitary evaluation character is contractive for coefficient `ell^(1 : ℕ)`. -/
theorem norm_bilateralWienerEval_le
    {z : ℂ} (hz : z ≠ 0) (hunit : ‖z‖ = 1) (f : BilateralWienerPacket) :
    ‖bilateralWienerEval z hz f‖ ≤ bilateralWienerPacketNorm f := by
  rw [bilateralWienerEval_eq_sum]
  change ‖∑ e ∈ f.coeff.support, f.coeff e * z ^ e‖ ≤
    ∑ e ∈ f.coeff.support, ‖f.coeff e‖
  calc
    ‖∑ e ∈ f.coeff.support, f.coeff e * z ^ e‖ ≤
        ∑ e ∈ f.coeff.support, ‖f.coeff e * z ^ e‖ := norm_sum_le _ _
    _ = ∑ e ∈ f.coeff.support, ‖f.coeff e‖ := by
      apply Finset.sum_congr rfl
      intro e _he
      simp [norm_zpow, hunit]

/-- Boundedness of a Laurent evaluation on the coefficient-native source norm. -/
def BilateralWienerEvalBounded (z : ℂ) (hz : z ≠ 0) : Prop :=
  ∃ C : ℝ, ∀ f : BilateralWienerPacket,
    ‖bilateralWienerEval z hz f‖ ≤ C * bilateralWienerPacketNorm f

/-- **Bilateral Wiener character theorem.** A Laurent evaluation is bounded exactly on the unit
circle. -/
theorem bilateralWienerEvalBounded_iff
    {z : ℂ} (hz : z ≠ 0) :
    BilateralWienerEvalBounded z hz ↔ ‖z‖ = 1 := by
  constructor
  · rintro ⟨C, hC⟩
    have hpos : ∀ n : ℕ, ‖z‖ ^ n ≤ C := by
      intro n
      have h := hC (LaurentPolynomial.T (n : ℤ))
      simpa [norm_zpow, zpow_natCast] using h
    have hneg : ∀ n : ℕ, ‖z⁻¹‖ ^ n ≤ C := by
      intro n
      have h := hC (LaurentPolynomial.T (-((n : ℕ) : ℤ)))
      simpa [norm_zpow, zpow_neg, zpow_natCast] using h
    have hzle : ‖z‖ ≤ 1 := by
      by_contra hnot
      have hgt : 1 < ‖z‖ := lt_of_not_ge hnot
      obtain ⟨n, _hn, hn⟩ := exists_one_le_and_pow_gt_poly hgt C 0
      have hle := hpos n
      have hn' : C < ‖z‖ ^ n := by simpa using hn
      exact (not_lt_of_ge hle) hn'
    have hinvle : ‖z⁻¹‖ ≤ 1 := by
      by_contra hnot
      have hgt : 1 < ‖z⁻¹‖ := lt_of_not_ge hnot
      obtain ⟨n, _hn, hn⟩ := exists_one_le_and_pow_gt_poly hgt C 0
      have hle := hneg n
      have hn' : C < ‖z⁻¹‖ ^ n := by simpa only [pow_zero, mul_one] using hn
      exact (not_lt_of_ge hle) hn'
    have hzge : 1 ≤ ‖z‖ := by
      rw [norm_inv] at hinvle
      exact (inv_le_one₀ (norm_pos_iff.mpr hz)).mp hinvle
    exact le_antisymm hzle hzge
  · intro hunit
    refine ⟨1, fun f => ?_⟩
    simpa using norm_bilateralWienerEval_le hz hunit f

/-- Laurent packet for one coherent marked source edge. -/
def bilateralWienerSourceEdge (m : ℕ) : BilateralWienerPacket :=
  LaurentPolynomial.T (m : ℤ) - LaurentPolynomial.T ((m + 1 : ℕ) : ℤ)

/-- Laurent packet implementing exact inverse-rank recovery. -/
def bilateralWienerRankRecovery (m : ℕ) : BilateralWienerPacket :=
  LaurentPolynomial.T (-((m : ℕ) : ℤ))

/-- Source formation and rank recovery are one exact identity in the Laurent Hopf envelope. -/
theorem bilateralWienerRankRecovery_mul_sourceEdge (m : ℕ) :
    bilateralWienerRankRecovery m * bilateralWienerSourceEdge m =
      1 - LaurentPolynomial.T 1 := by
  rw [bilateralWienerRankRecovery, bilateralWienerSourceEdge, mul_sub,
    ← LaurentPolynomial.T_add, ← LaurentPolynomial.T_add]
  have h0 : -((m : ℕ) : ℤ) + (m : ℤ) = 0 := by ring
  have h1 : -((m : ℕ) : ℤ) + ((m + 1 : ℕ) : ℤ) = 1 := by push_cast; ring
  rw [h0, h1, LaurentPolynomial.T_zero]

/-- Evaluation of the Laurent source edge is the coherent character edge. -/
theorem bilateralWienerEval_sourceEdge
    (z : ℂ) (hz : z ≠ 0) (m : ℕ) :
    bilateralWienerEval z hz (bilateralWienerSourceEdge m) =
      complexCharacterEdge z m := by
  rw [bilateralWienerSourceEdge, map_sub, bilateralWienerEval_T,
    bilateralWienerEval_T, zpow_natCast, zpow_natCast, complexCharacterEdge]

/-- Evaluation of inverse-rank recovery is the canonical natural-rank gauge. -/
theorem bilateralWienerEval_rankRecovery
    (z : ℂ) (hz : z ≠ 0) (m : ℕ) :
    bilateralWienerEval z hz (bilateralWienerRankRecovery m) =
      (z⁻¹) ^ m := by
  simp [bilateralWienerRankRecovery, zpow_neg, zpow_natCast]

/-- Actual normalized depth-12 marked execution is evaluation of the coefficient-native Laurent
source edge. -/
theorem bilateralWienerEval_sourceEdge_rankTwelve
    {p : ℕ} (hp : p.Prime) (z : ℂ) (hz : z ≠ 0) (j : ℕ) :
    bilateralWienerEval z hz (bilateralWienerSourceEdge (12 + j)) =
      rankTwelveLiteralSourceMarkedExecution p z j := by
  rw [bilateralWienerEval_sourceEdge,
    rankTwelveLiteralSourceMarkedExecution_eq hp]

/-- Prime half-density evaluation is bounded on the bilateral Wiener source exactly on the
critical line. -/
theorem bilateralWienerHalfDensityEvalBounded_iff
    {p : ℕ} (hp : 2 ≤ p) (s : ℂ) :
    BilateralWienerEvalBounded
        (bilateralHalfDensityCharacter p s)
        (bilateralHalfDensityCharacter_ne_zero
          (lt_of_lt_of_le two_pos hp) s) ↔
      s.re = 1 / 2 := by
  exact (bilateralWienerEvalBounded_iff
    (bilateralHalfDensityCharacter_ne_zero
      (lt_of_lt_of_le two_pos hp) s)).trans
      (norm_bilateralHalfDensityCharacter_eq_one_iff hp s)

end

end GaloisForLFunctions.HTGeometry
