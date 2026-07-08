/-
Combining the two readings of the level-1 ladder charge: `ApexIndependence` (local) and the
seam reflection collapse (`SeamArfCollapse`, global).

`ApexIndependence` studies the additive ladder charge `wCharge n idx = (idx : ZMod n)`: when it
is nonzero it lies outside every torsion reading of the prime-flux lattice, and at `n = 2^k` it
is realized by an integer symplectic weld class.  Every ξ statement there is gated on the
*pointwise* nontriviality `xiDeckCharge k ρ ≠ 1` — an unexplained hypothesis about one zero.

`SeamArfCollapse` studies the same object at `n = 2` — the deck parity `xiDeckParity ρ` — and
shows the functional equation's conjugate-pairing makes it *sum to zero* over any
conjugation-closed reflection family, its quadratic (Arf) refinement collapsing to it.

The bridge `xiDeckParity ρ = wCharge 2 (ord_ρ ξ)` identifies the two objects, and the
combination is a single conservation law paired with the independence:

* **local** — each nonzero level-1 ladder charge is outside every prime-flux torsion reading
  (`ApexIndependence`);
* **global** — those same charges sum to `0` over the reflection family (the seam collapse).

So the apex charge is prime-flux-*independent* at each point yet *conserved* across the seam:
a constraint (a conservation law), not a flow.  The nontriviality hypothesis of
`ApexIndependence` is thereby localized — it is *vacuous* at the functional equation's fixed
point (`xi_apex_level1_trivial_at_center`), where the order is even, and it can be sourced only
by genuinely unpaired off-line order, exactly the residue `SignatureParity` isolates.  Finally,
the quadratic Arf refinement produces the linear ladder charge itself
(`xi_arf_density_eq_ladder_charge`): there is no new apex invariant at the quadratic level.
-/
import GaloisForLFunctions.RHTower.SeamArfCollapse
import GaloisForLFunctions.RHTower.ApexIndependence

open scoped BigOperators

namespace GaloisForLFunctions
namespace RHTower

/-! ### §1 Bridge: the deck parity is the level-1 additive ladder charge -/

/-- **The deck parity is `wCharge 2` of the vanishing order.**  `xiDeckParity ρ`, the mod-2
vanishing order of ξ, equals the additive level-1 ladder charge `wCharge 2 (ord_ρ ξ)` — the
`SeamArfCollapse` object and the `ApexIndependence` object are the same. -/
theorem xiDeckParity_eq_wCharge_two (ρ : ℂ) :
    _root_.RHTower.xiDeckParity ρ
      = _root_.RHTower.wCharge 2 ((analyticOrderAt _root_.RHTower.xi ρ).toNat : ℤ) := by
  unfold _root_.RHTower.xiDeckParity
  exact (Int.cast_natCast _).symm

/-! ### §2 The seam conservation law in charge language -/

/-- **Level-1 apex charges are conserved across the seam.**  Over a conjugation-closed,
fixed-point-free reflection family of ξ-zeros, the additive level-1 ladder charges sum to `0`
— the functional equation's conjugate-pairing annihilates the total charge.  This is
`xi_arf_no_new_obstruction_conj` read through the bridge. -/
theorem xi_ladder_charge_reflection_sum_zero {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (ρ : ι → ℂ) (σ : ι → ι)
    (hσs : ∀ i ∈ s, σ i ∈ s) (hσσ : ∀ i ∈ s, σ (σ i) = i) (hfix : ∀ i ∈ s, σ i ≠ i)
    (hconj : ∀ i ∈ s, ρ (σ i) = (starRingEnd ℂ) (ρ i)) :
    ∑ i ∈ s, _root_.RHTower.wCharge 2 ((analyticOrderAt _root_.RHTower.xi (ρ i)).toNat : ℤ)
      = 0 := by
  have hbridge : ∀ i,
      _root_.RHTower.wCharge 2 ((analyticOrderAt _root_.RHTower.xi (ρ i)).toNat : ℤ)
        = _root_.RHTower.xiDeckParity (ρ i) := fun i => (xiDeckParity_eq_wCharge_two (ρ i)).symm
  simp_rw [hbridge]
  exact (_root_.RHTower.xi_arf_no_new_obstruction_conj s ρ σ hσs hσσ hfix hconj).2

/-! ### §3 The synthesis: locally apex-independent, globally conserved -/

/-- **Local independence, global conservation.**  For a conjugation-closed, fixed-point-free
reflection family of ξ-zeros:

* every *nonzero* level-1 ladder charge lies outside every torsion reading of the prime-flux
  lattice (`ApexIndependence.nontrivial_wCharge_ne_primeFlux_charge`);
* the level-1 ladder charges *sum to zero* over the family (the seam collapse).

The apex charge is prime-flux-independent at each point yet conserved across the seam — the two
apices' independence coexists with a conservation law from the functional equation, a
constraint rather than a flow. -/
theorem xi_apex_local_seam_global {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (ρ : ι → ℂ) (σ : ι → ι)
    (hσs : ∀ i ∈ s, σ i ∈ s) (hσσ : ∀ i ∈ s, σ (σ i) = i) (hfix : ∀ i ∈ s, σ i ≠ i)
    (hconj : ∀ i ∈ s, ρ (σ i) = (starRingEnd ℂ) (ρ i)) :
    (∀ i ∈ s,
      _root_.RHTower.wCharge 2 ((analyticOrderAt _root_.RHTower.xi (ρ i)).toNat : ℤ) ≠ 0 →
        ∀ (φ : secondConstraintCohomology (G := WeldGroup) (A := ℝ) →+ ZMod 2)
          (c : Nat.Primes →₀ ℤ),
          φ (primeFluxHom c) ≠
            _root_.RHTower.wCharge 2 ((analyticOrderAt _root_.RHTower.xi (ρ i)).toNat : ℤ)) ∧
      ∑ i ∈ s, _root_.RHTower.wCharge 2 ((analyticOrderAt _root_.RHTower.xi (ρ i)).toNat : ℤ)
        = 0 :=
  ⟨fun _i _hmem hnz φ c => nontrivial_wCharge_ne_primeFlux_charge φ hnz c,
    xi_ladder_charge_reflection_sum_zero s ρ σ hσs hσσ hfix hconj⟩

/-! ### §4 The nontriviality hypothesis is vacuous at the fixed point -/

/-- **The level-1 apex charge vanishes at the functional equation's fixed point.**  At the
central point `s = 1/2` the vanishing order of ξ is even (`xi_central_order_even`), so its
level-1 ladder charge is `0`.  `ApexIndependence`'s nontriviality hypothesis
`xiDeckCharge 1 (1/2) ≠ 1` is therefore false: apex independence has no content at the fixed
point.  The reflection fixes parity exactly at its ramified locus, which for the functional
equation is `1/2` alone — off it the charge must be sourced by genuinely unpaired order. -/
theorem xi_apex_level1_trivial_at_center :
    _root_.RHTower.wCharge 2 ((analyticOrderAt _root_.RHTower.xi (1 / 2 : ℂ)).toNat : ℤ) = 0 := by
  rw [← xiDeckParity_eq_wCharge_two]
  unfold _root_.RHTower.xiDeckParity
  obtain ⟨k, hk⟩ := _root_.RHTower.xi_central_order_even
  rw [hk]; push_cast; exact CharTwo.add_self_eq_zero _

/-! ### §5 No new apex invariant at the quadratic level -/

/-- **The quadratic Arf density is the linear ladder charge.**  For a conjugation-closed family,
the Arf density `xiDeckParity (ρ i) * xiDeckParity (ρ (σ i))` of the seam's unique `ZMod 2`
symplectic refinement equals the additive level-1 ladder charge `wCharge 2 (ord_{ρ i} ξ)`.  So
the quadratic refinement contributes exactly the linear apex charge — there is no independent
apex invariant at the quadratic level for `ApexIndependence` to read. -/
theorem xi_arf_density_eq_ladder_charge {ι : Type*}
    (s : Finset ι) (ρ : ι → ℂ) (σ : ι → ι)
    (hconj : ∀ i ∈ s, ρ (σ i) = (starRingEnd ℂ) (ρ i)) :
    ∀ i ∈ s,
      _root_.RHTower.xiDeckParity (ρ i) * _root_.RHTower.xiDeckParity (ρ (σ i))
        = _root_.RHTower.wCharge 2 ((analyticOrderAt _root_.RHTower.xi (ρ i)).toNat : ℤ) := by
  intro i hi
  rw [(_root_.RHTower.xi_arf_collapses_conj s ρ σ hconj).1 i hi, xiDeckParity_eq_wCharge_two]

end RHTower
end GaloisForLFunctions
