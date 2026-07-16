import GaloisForLFunctions.HTGeometry.ClockCapacityHilbertBoundary

/-!
# Finite-rank clock-capacity boundary

The scalar Riesz--Fischer classification applies coordinatewise to any finite response packet.
Coordinatewise `ℓ²` is equivalent to summability of the squared finite-dimensional innovation
norm, yielding the finite-rank normal-boundary criterion.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped ENNReal NNReal lp

noncomputable section

/-- Coordinatewise square summability of a finite innovation packet. -/
def PacketMemℓp {r : ℕ} (eta : ℕ → Fin r → ℂ) : Prop :=
  ∀ a, Memℓp (fun n => eta n a) 2

/-- The unique normal boundary packet reconstructed coordinatewise by Riesz--Fischer. -/
noncomputable def hilbertPacketBoundary
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {r : ℕ} (b : HilbertBasis ℕ ℂ E) (eta : ℕ → Fin r → ℂ)
    (heta : PacketMemℓp eta) (a : Fin r) : E :=
  hilbertBoundaryOfSquareSummable b (fun n => eta n a) (heta a)

theorem inner_hilbertPacketBoundary
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {r : ℕ} (b : HilbertBasis ℕ ℂ E) (eta : ℕ → Fin r → ℂ)
    (heta : PacketMemℓp eta) (a : Fin r) (n : ℕ) :
    inner ℂ (b n) (hilbertPacketBoundary b eta heta a) = star (eta n a) :=
  inner_hilbertBoundaryOfSquareSummable b (fun n => eta n a) (heta a) n

theorem packetMemℓp_iff_summable_norm_sq {r : ℕ} (eta : ℕ → Fin r → ℂ) :
    PacketMemℓp eta ↔ Summable (fun n => ∑ a, ‖eta n a‖ ^ 2) := by
  constructor
  · intro heta
    exact summable_sum fun a _ =>
      (memℓp_two_iff_summable_norm_sq (fun n => eta n a)).mp (heta a)
  · intro hsum a
    apply (memℓp_two_iff_summable_norm_sq (fun n => eta n a)).mpr
    apply Summable.of_nonneg_of_le
    · exact fun n => sq_nonneg ‖eta n a‖
    · intro n
      exact Finset.single_le_sum (fun j _ => sq_nonneg ‖eta n j‖) (Finset.mem_univ a)
    · exact hsum

/-- **Finite-rank Riesz--Fischer classification.**  A finite response packet has a unique normal
Hilbert representative exactly when its vector innovation sequence is square-summable. -/
theorem existsUnique_hilbertPacket_coordinates_iff_summable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {r : ℕ} (b : HilbertBasis ℕ ℂ E) (eta : ℕ → Fin r → ℂ) :
    (∃! y : Fin r → E,
      ∀ a n, inner ℂ (b n) (y a) = star (eta n a)) ↔
      Summable (fun n => ∑ a, ‖eta n a‖ ^ 2) := by
  rw [← packetMemℓp_iff_summable_norm_sq]
  constructor
  · rintro ⟨y, hy, _⟩ a
    exact memℓp_two_of_hilbertBasis_coordinates b (fun n => eta n a) (y a) (hy a)
  · intro heta
    refine ⟨hilbertPacketBoundary b eta heta, inner_hilbertPacketBoundary b eta heta, ?_⟩
    intro y hy
    funext a
    exact hilbertBasis_coordinates_unique b (fun n => eta n a) (y a)
      (hilbertPacketBoundary b eta heta a) (hy a)
      (inner_hilbertPacketBoundary b eta heta a)

end

end GaloisForLFunctions.HTGeometry
