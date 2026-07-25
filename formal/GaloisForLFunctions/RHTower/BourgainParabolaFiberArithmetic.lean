/-
# Elementary arithmetic of parabola triple fibers

For a fixed value of `(Σn, Σn²)`, a triple is determined by its first
coordinate and the ordering of the remaining two coordinates.  This gives
the unconditional elementary bound `2H` for every triple fiber.

The sharp planar decoupling input replaces this linear loss by `H^ε`; the
present result isolates the exact arithmetic point at which the divisor
bound for the quadratic form `u² + 3v²` must enter.
-/
import GaloisForLFunctions.RHTower.BourgainFiniteFiberL2

open scoped BigOperators

namespace RHTower

noncomputable section

/-- First coordinate together with the ordering of the other two
coordinates. -/
def bourgainParabolaTripleCode {H : ℕ}
    (h : Fin 3 → Fin H) : Fin H × Bool :=
  (h 0, decide (bourgainIndex (h 1) ≤ bourgainIndex (h 2)))

/-- On a fixed `(Σn, Σn²)` fiber, the elementary code is injective. -/
theorem bourgainParabolaTripleCode_injective_on_fiber
    {H : ℕ} {h k : Fin 3 → Fin H}
    (hmoment :
      bourgainParabolaTripleMoment h =
        bourgainParabolaTripleMoment k)
    (hcode :
      bourgainParabolaTripleCode h =
        bourgainParabolaTripleCode k) :
    h = k := by
  have hzero : h 0 = k 0 := congrArg Prod.fst hcode
  have horder :
      decide (bourgainIndex (h 1) ≤ bourgainIndex (h 2)) =
        decide (bourgainIndex (k 1) ≤ bourgainIndex (k 2)) := by
    exact congrArg Prod.snd hcode
  have hsum := congrArg Prod.fst hmoment
  have hsquares := congrArg Prod.snd hmoment
  simp only [bourgainParabolaTripleMoment, Fin.sum_univ_three] at hsum hsquares
  rw [hzero] at hsum hsquares
  have hsumTail :
      bourgainIndex (h 1) + bourgainIndex (h 2) =
        bourgainIndex (k 1) + bourgainIndex (k 2) := by
    omega
  have hsquaresTail :
      bourgainIndex (h 1) ^ (2 : ℕ) +
          bourgainIndex (h 2) ^ (2 : ℕ) =
        bourgainIndex (k 1) ^ (2 : ℕ) +
          bourgainIndex (k 2) ^ (2 : ℕ) := by
    omega
  have honeIndex :
      bourgainIndex (h 1) = bourgainIndex (k 1) := by
    by_cases hhk :
        bourgainIndex (h 1) ≤ bourgainIndex (h 2)
    · have hkk :
          bourgainIndex (k 1) ≤ bourgainIndex (k 2) := by
        simpa [hhk] using horder
      nlinarith
    · have hhk' :
          bourgainIndex (h 2) ≤ bourgainIndex (h 1) :=
        Nat.le_of_lt (Nat.lt_of_not_ge hhk)
      have hkk' :
          bourgainIndex (k 2) ≤ bourgainIndex (k 1) := by
        have : ¬ bourgainIndex (k 1) ≤ bourgainIndex (k 2) := by
          simpa [hhk] using horder
        exact Nat.le_of_lt (Nat.lt_of_not_ge this)
      nlinarith
  have htwoIndex :
      bourgainIndex (h 2) = bourgainIndex (k 2) := by
    omega
  funext j
  fin_cases j
  · exact hzero
  · apply Fin.ext
    simpa [bourgainIndex] using honeIndex
  · apply Fin.ext
    simpa [bourgainIndex] using htwoIndex

/-- Every fixed `(Σn, Σn²)` triple fiber has at most `2H` elements. -/
theorem card_bourgainParabolaTripleMoment_fiber_le
    (H : ℕ) (y : ℕ × ℕ) :
    ((Finset.univ : Finset (Fin 3 → Fin H)).filter
      fun h => bourgainParabolaTripleMoment h = y).card ≤ 2 * H := by
  classical
  let fiber : Finset (Fin 3 → Fin H) :=
    (Finset.univ : Finset (Fin 3 → Fin H)).filter
      fun h => bourgainParabolaTripleMoment h = y
  have hmaps :
      ∀ h ∈ fiber,
        bourgainParabolaTripleCode h ∈
          (Finset.univ : Finset (Fin H × Bool)) := by
    simp
  have hinj :
      Set.InjOn bourgainParabolaTripleCode
        (↑fiber : Set (Fin 3 → Fin H)) := by
    intro h hh k hk heq
    apply bourgainParabolaTripleCode_injective_on_fiber
    · have hh' := (Finset.mem_filter.mp hh).2
      have hk' := (Finset.mem_filter.mp hk).2
      exact hh'.trans hk'.symm
    · exact heq
  calc
    ((Finset.univ : Finset (Fin 3 → Fin H)).filter
        fun h => bourgainParabolaTripleMoment h = y).card =
        fiber.card := rfl
    _ ≤ (Finset.univ : Finset (Fin H × Bool)).card :=
      Finset.card_le_card_of_injOn _ hmaps hinj
    _ = 2 * H := by
      rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
        Fintype.card_bool]
      omega

/-- Unconditional elementary planar `L⁶` fiber estimate with linear loss. -/
theorem bourgainParabolaFiberL2_le_two_mul
    (H : ℕ) (a : Fin H → ℂ) :
    ∑ y ∈
        (Finset.univ : Finset (Fin 3 → Fin H)).image
          bourgainParabolaTripleMoment,
      ‖∑ h ∈ (Finset.univ : Finset (Fin 3 → Fin H)).filter
          (fun h => bourgainParabolaTripleMoment h = y),
        bourgainTripleWeight a h‖ ^ (2 : ℕ) ≤
      (2 * H : ℝ) *
        (∑ n : Fin H, ‖a n‖ ^ (2 : ℕ)) ^ (3 : ℕ) := by
  apply bourgainParabolaFiberL2_le
  intro y _
  exact_mod_cast card_bourgainParabolaTripleMoment_fiber_le H y

end

end RHTower
