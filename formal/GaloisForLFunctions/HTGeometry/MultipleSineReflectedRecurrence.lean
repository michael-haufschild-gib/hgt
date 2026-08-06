import GaloisForLFunctions.HTGeometry.MultipleSineReflectedSource

/-!
# The multiple-sine recurrence transports through the reflection

The Barnes ladder step is proved in the corpus: deleting one direction from the frame,

```text
(T_k - 1) Psi_S + Psi_{S∖k}   is differentially algebraic.
```

The multiple sine is the Barnes object reflected, `L_S(z) = Psi_S(z) - eps_S · Psi_S(c_S - z)` with
`c_S = ∑_{i ∈ S} omega_i` and `eps_S = (-1)^{|S|+1}`.  This file proves the exact bookkeeping that
carries the ladder across the reflection, with no analysis and no hypotheses:

* the shift difference of a reflected source is the shift difference of the source at `z` plus
  `eps` times the same shift difference at the *deleted-frame* reflected point `(c - a) - z`
  (`shiftDiff_reflectedSource`);
* consequently a ladder relation for `Psi` becomes a ladder relation for the reflected source, with
  the deleted frame's reflection point and the *flipped* parity sign
  (`shiftDiff_reflectedSource_of_ladder`);
* the same with an explicit remainder, so the differentially algebraic defect of the Barnes ladder
  transports to a reflected combination of that defect
  (`shiftDiff_reflectedSource_of_ladder_remainder`).

Both bookkeeping facts the transport needs are then checked: deleting a direction subtracts its
period from the reflection point, and flips the parity sign.  Together these are equation `(2)`
`(T_j - 1) L_A = -L_{A∖{j}}` for the reflected source, reduced to the Barnes ladder.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex GaloisForLFunctions
open scoped BigOperators

noncomputable section

/-! ### Shift differences of reflected sources -/

/-- The shift difference `(T_a - 1) f`. -/
def shiftDiff (a : ℂ) (f : ℂ → ℂ) : ℂ → ℂ := fun z => f (z + a) - f z

/-- The reflected combination `z ↦ Psi z - eps · Psi (c - z)`. -/
def reflectedSource (ε c : ℂ) (Ψ : ℂ → ℂ) : ℂ → ℂ := fun z => Ψ z - ε * Ψ (c - z)

/-- **Reflection transport of the shift difference.**  The reflected part contributes the same
shift difference read at the reflected point of the *deleted* frame. -/
theorem shiftDiff_reflectedSource (ε c a : ℂ) (Ψ : ℂ → ℂ) (z : ℂ) :
    shiftDiff a (reflectedSource ε c Ψ) z =
      shiftDiff a Ψ z + ε * shiftDiff a Ψ ((c - a) - z) := by
  unfold shiftDiff reflectedSource
  have h₁ : c - (z + a) = c - a - z := by ring
  have h₂ : c - a - z + a = c - z := by ring
  rw [h₁, h₂]
  ring

/-- **The ladder transports.**  An exact ladder relation `(T_a - 1) Psi = -Phi` becomes an exact
ladder relation for the reflected source, at the deleted frame's reflection point and with the
parity sign flipped. -/
theorem shiftDiff_reflectedSource_of_ladder (ε c a : ℂ) (Ψ Φ : ℂ → ℂ)
    (hladder : ∀ z, shiftDiff a Ψ z = -Φ z) (z : ℂ) :
    shiftDiff a (reflectedSource ε c Ψ) z = -(reflectedSource (-ε) (c - a) Φ) z := by
  rw [shiftDiff_reflectedSource, hladder, hladder]
  unfold reflectedSource
  ring

/-- **The ladder transports with its defect.**  A ladder relation with remainder `R` becomes one
whose remainder is the reflected combination of `R`; the differentially algebraic sector is closed
under that combination, so a DA defect stays a DA defect. -/
theorem shiftDiff_reflectedSource_of_ladder_remainder (ε c a : ℂ) (Ψ Φ R : ℂ → ℂ)
    (hladder : ∀ z, shiftDiff a Ψ z = -Φ z + R z) (z : ℂ) :
    shiftDiff a (reflectedSource ε c Ψ) z =
      -(reflectedSource (-ε) (c - a) Φ) z + (R z + ε * R ((c - a) - z)) := by
  rw [shiftDiff_reflectedSource, hladder, hladder]
  unfold reflectedSource
  ring

/-! ### Frame bookkeeping: reflection point and parity sign -/

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Reflection point of the subframe carried by a finite set of directions. -/
def frameReflectionPoint (ω : ι → ℂ) (S : Finset ι) : ℂ := ∑ i ∈ S, ω i

omit [Fintype ι] in
/-- **Deleting a direction subtracts its period from the reflection point.** -/
theorem frameReflectionPoint_erase (ω : ι → ℂ) {S : Finset ι} {k : ι} (hk : k ∈ S) :
    frameReflectionPoint ω S - ω k = frameReflectionPoint ω (S.erase k) := by
  unfold frameReflectionPoint
  rw [← Finset.add_sum_erase S ω hk]
  ring

omit [DecidableEq ι] in
theorem frameReflectionPoint_univ (ω : ι → ℂ) :
    frameReflectionPoint ω Finset.univ = barnesReflectionPoint ω := rfl

/-- Parity sign of a subframe: `eps_S = (-1)^{|S|+1}`. -/
def frameSign (S : Finset ι) : ℂ := (-1) ^ (S.card + 1)

omit [Fintype ι] in
/-- **Deleting a direction flips the parity sign.** -/
theorem frameSign_erase {S : Finset ι} {k : ι} (hk : k ∈ S) :
    frameSign (S.erase k) = -frameSign S := by
  unfold frameSign
  rw [Finset.card_erase_of_mem hk]
  have hcard : 1 ≤ S.card := Finset.card_pos.2 ⟨k, hk⟩
  rw [show S.card + 1 = (S.card - 1 + 1) + 1 by omega, pow_succ]
  ring

omit [DecidableEq ι] in
theorem frameSign_univ_eq_multipleSineExponent [Nonempty ι] :
    frameSign (Finset.univ : Finset ι) = (multipleSineExponent ι : ℂ) := by
  unfold frameSign multipleSineExponent
  push_cast
  rw [Finset.card_univ]

/-! ### Equation `(2)` for the reflected source -/

omit [Fintype ι] in
/-- **Equation `(2)` for the reflected multiple-sine source.**  Given the Barnes ladder at direction
`k` of a frame `S`, the reflected sources of `S` and of `S.erase k` — each with its own reflection
point and parity sign — satisfy `(T_k - 1) L_S = -L_{S∖k}`.

Every ingredient is checked: the deleted frame's reflection point is `c_S - omega_k`, and its parity
sign is `-eps_S`. -/
theorem shiftDiff_frameReflectedSource (ω : ι → ℂ) {S : Finset ι} {k : ι} (hk : k ∈ S)
    (Ψ Φ : ℂ → ℂ) (hladder : ∀ z, shiftDiff (ω k) Ψ z = -Φ z) (z : ℂ) :
    shiftDiff (ω k)
        (reflectedSource (frameSign S) (frameReflectionPoint ω S) Ψ) z =
      -(reflectedSource (frameSign (S.erase k))
        (frameReflectionPoint ω (S.erase k)) Φ) z := by
  rw [← frameReflectionPoint_erase ω hk, frameSign_erase hk]
  exact shiftDiff_reflectedSource_of_ladder _ _ _ Ψ Φ hladder z

omit [DecidableEq ι] in
/-- The multiple-sine source of the full frame is the reflected combination the transport law
consumes. -/
theorem multipleSineSource_eq_reflectedSource [Nonempty ι] (ω : ι → ℂ) :
    multipleSineSource ω =
      reflectedSource (frameSign (Finset.univ : Finset ι))
        (frameReflectionPoint ω Finset.univ) (logDeriv (barnesConeProduct ω)) := by
  funext z
  rw [frameSign_univ_eq_multipleSineExponent, frameReflectionPoint_univ]
  rfl

end

end GaloisForLFunctions.HTGeometry
