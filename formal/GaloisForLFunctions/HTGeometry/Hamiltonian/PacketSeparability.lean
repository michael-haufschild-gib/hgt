import GaloisForLFunctions.HTGeometry.JacobianAlgebraicIndependence
import GaloisForLFunctions.HTGeometry.TwoPacketRationalPrimitiveRigidity

/-!
# Separability of polynomial packet Hamiltonians

The Levi--Civita defect used by Martinusi, arXiv:2611.18083, vanishes
when the second canonical packet enters through one scalar polynomial
(Lemma 2.1(b)). Independent packet energies also have zero defect.
In contrast, the corpus's addition comultiplication couples an oscillator:
its defect is exactly minus eight times its energy.
-/

open MvPolynomial
namespace GaloisForLFunctions.HTGeometry
noncomputable section

abbrev CanonicalPacketPolynomial := MvPolynomial (Fin 2) ℝ
abbrev TwoCanonicalPacketPolynomial := MvPolynomial (Fin 2 ⊕ Fin 2) ℝ

/-- The mixed Levi--Civita expression for the two canonical pairs. -/
def packetSeparabilityDefect (H : TwoCanonicalPacketPolynomial) : TwoCanonicalPacketPolynomial :=
  -pderiv (Sum.inl 1) H * pderiv (Sum.inr 1) H *
      pderiv (Sum.inl 0) (pderiv (Sum.inr 0) H) +
    pderiv (Sum.inl 0) H * pderiv (Sum.inr 1) H *
      pderiv (Sum.inl 1) (pderiv (Sum.inr 0) H) +
    pderiv (Sum.inl 1) H * pderiv (Sum.inr 0) H *
      pderiv (Sum.inl 0) (pderiv (Sum.inr 1) H) -
    pderiv (Sum.inl 0) H * pderiv (Sum.inr 0) H *
      pderiv (Sum.inl 1) (pderiv (Sum.inr 1) H)

/-- Independent energies have no mixed defect, without conditions on either polynomial. -/
theorem packetSeparabilityDefect_independent (U V : CanonicalPacketPolynomial) :
    packetSeparabilityDefect (rename Sum.inl U + rename Sum.inr V) = 0 := by
  simp only [packetSeparabilityDefect, map_add, pderiv_rename_inl,
    pderiv_rename_inr, pderiv_rename_inl_cross, pderiv_rename_inr_cross,
    map_zero, add_zero, zero_add, mul_zero, sub_zero]

/-- A scalar observation of the second packet, together with the first canonical pair. -/
def nestedPacketSubstitution (K : CanonicalPacketPolynomial) :
    Fin 3 → TwoCanonicalPacketPolynomial :=
  ![X (Sum.inl 0), X (Sum.inl 1), rename Sum.inr K]

def nestedPacketHamiltonian (Φ : MvPolynomial (Fin 3) ℝ)
    (K : CanonicalPacketPolynomial) : TwoCanonicalPacketPolynomial :=
  aeval (nestedPacketSubstitution K) Φ

/-- The second-packet gradient factors through its one scalar observation. -/
theorem pderiv_nestedPacket_right (Φ : MvPolynomial (Fin 3) ℝ)
    (K : CanonicalPacketPolynomial) (j : Fin 2) :
    pderiv (Sum.inr j) (nestedPacketHamiltonian Φ K) =
      nestedPacketHamiltonian (pderiv 2 Φ) K * rename Sum.inr (pderiv j K) := by
  rw [nestedPacketHamiltonian, pderiv_aeval_chain, Fin.sum_univ_three]
  simp [nestedPacketSubstitution, nestedPacketHamiltonian, pderiv_rename_inr]

/-- Each mixed Hessian row contains the same second-packet gradient factor. -/
theorem pderiv_nestedPacket_mixed (Φ : MvPolynomial (Fin 3) ℝ)
    (K : CanonicalPacketPolynomial) (i j : Fin 2) :
    pderiv (Sum.inl i) (pderiv (Sum.inr j) (nestedPacketHamiltonian Φ K)) =
      pderiv (Sum.inl i) (nestedPacketHamiltonian (pderiv 2 Φ) K) *
        rename Sum.inr (pderiv j K) := by
  rw [pderiv_nestedPacket_right, pderiv_mul, pderiv_rename_inr_cross, mul_zero, add_zero]

/-- The polynomial kernel family from Martinusi's Lemma 2.1(b). -/
theorem packetSeparabilityDefect_nested (Φ : MvPolynomial (Fin 3) ℝ)
    (K : CanonicalPacketPolynomial) :
    packetSeparabilityDefect (nestedPacketHamiltonian Φ K) = 0 := by
  unfold packetSeparabilityDefect
  rw [pderiv_nestedPacket_mixed, pderiv_nestedPacket_mixed,
    pderiv_nestedPacket_mixed, pderiv_nestedPacket_mixed,
    pderiv_nestedPacket_right, pderiv_nestedPacket_right]
  ring

/-- The standard oscillator energy on one canonical packet. -/
def packetOscillator : CanonicalPacketPolynomial := X 0 ^ 2 + X 1 ^ 2

/-- Adding packet coordinates before taking energy produces an exact nonzero defect. -/
theorem packetSeparabilityDefect_addedOscillator :
    packetSeparabilityDefect (freeCoordinateAddPolynomialMap ℝ (Fin 2) packetOscillator) =
      -8 * freeCoordinateAddPolynomialMap ℝ (Fin 2) packetOscillator := by
  simp [packetSeparabilityDefect, freeCoordinateAddPolynomialMap,
    packetOscillator, pderiv_mul, pderiv_pow]
  ring

/-- The obstruction is negative energy, so its real zero locus is exact packet cancellation. -/
theorem packetSeparabilityDefect_addedOscillator_eval_zero (x : Fin 2 ⊕ Fin 2 → ℝ) :
    eval x (packetSeparabilityDefect
      (freeCoordinateAddPolynomialMap ℝ (Fin 2) packetOscillator)) = 0 ↔
      x (Sum.inl 0) + x (Sum.inr 0) = 0 ∧ x (Sum.inl 1) + x (Sum.inr 1) = 0 := by
  rw [packetSeparabilityDefect_addedOscillator]
  simp only [map_mul, map_neg, map_ofNat, freeCoordinateAddPolynomialMap,
    packetOscillator, map_add, map_pow, aeval_X, eval_add, eval_X]
  constructor
  · intro h
    have hq := sq_nonneg (x (Sum.inl 0) + x (Sum.inr 0))
    have hp := sq_nonneg (x (Sum.inl 1) + x (Sum.inr 1))
    constructor <;> nlinarith only [h, hq, hp]
  · rintro ⟨hq, hp⟩
    rw [hq, hp]
    ring

#print axioms packetSeparabilityDefect_independent
#print axioms packetSeparabilityDefect_nested
#print axioms packetSeparabilityDefect_addedOscillator
#print axioms packetSeparabilityDefect_addedOscillator_eval_zero

end
end GaloisForLFunctions.HTGeometry
