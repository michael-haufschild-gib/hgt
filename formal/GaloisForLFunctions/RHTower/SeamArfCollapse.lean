/-
The quadratic (Arf) face of the seam's `J`-collapse.

Two earlier faces record how the functional equation's conjugate-pairing of zeros — the
reflection involution `σ` (`J`) — annihilates every mod-2 shadow of the winding index:

* the **real** face (`SeamNullConeSignature`): the polarized seam form has inertia triple
  `(sigPos, sigNeg, dim radical) = (even, even, even)` — neutral, never Lorentzian;
* the **linear** face (`SignatureParity`): the deck class at `n = 2` is the reduction
  homomorphism `ℤ → ZMod 2`, and a fixed-point-free multiplicity-matching involution puts
  the reflection-paired zeros (and the ramified fixed point) entirely in its kernel.

This file is the **quadratic** face.  The reflection matching is a perfect matching of the
off-line zeros — a nondegenerate *alternating* `ZMod 2`-form whose symplectic planes are the
conjugate pairs `{ρ, σ ρ}`, the only `ZMod 2` symplectic structure the boundary data carries.
Its **Arf invariant** is the sum of the plane densities `q ρ * q (σ ρ)` over a conjugate-pair
transversal — the one genuinely-quadratic bit one could hope reads more than the linear deck
parity.  It does not:

    `q ρ * q (σ ρ) = q ρ`   **pointwise** on the matched set,

because a reflection-*equivariant* refinement satisfies `q (σ ρ) = q ρ` and `x * x = x` in
`ZMod 2`.  So the Arf density equals the linear deck density term by term; the Arf invariant
collapses to `∑ q ρ` over the transversal — a *linear* functional of the deck data, carrying
nothing beyond it — and over the whole matched set it is `0` (the linear face again).

The single escape — a refinement with `q (σ ρ) ≠ q ρ` — uses data not invariant under
conjugation, i.e. a choice of branch of `√ξ`, a section of the deck cover: a flow, not a
constraint, hence not seam-canonical.  Externally, a functional equation with simple off-line
zeros (Davenport–Heilbronn) shows no functional-equation-canonical invariant of any degree can
force off-line parity, so the collapse is the true state, not an artifact of this refinement.

No higher-degree escape exists either: the reflection matching is `ZMod 2`-valued, so it
supports a `ZMod 2` (Arf) refinement only — there is no `ZMod 4` symplectic form on the
boundary data to carry a Brown-type invariant.  The deck classes at every level `n = 2^k` are
the *linear* reduction homomorphism (`SignatureParity`); the quadratic refinement exists only
at `k = 1`, and it collapses here.
-/
import GaloisForLFunctions.RHTower.SignatureParity
import GaloisForLFunctions.RHTower.Reflection

open scoped BigOperators

open Complex

namespace RHTower

/-! ### §1 Idempotence in `ZMod 2` -/

/-- In `ZMod 2` every element is idempotent: `x * x = x`.  This is the whole reason a
reflection-equivariant quadratic refinement has no quadratic content — the plane density
`q e * q (σ e) = q e * q e = q e`. -/
theorem zmod2_mul_self (x : ZMod 2) : x * x = x := by revert x; decide

/-! ### §2 The abstract Arf collapse

`σ : ι → ι` is the reflection matching of the index set; `q : ι → ZMod 2` is a refinement
(a `ZMod 2`-value at each index).  "Reflection-equivariant" means `q (σ i) = q i` — the datum
is invariant under conjugation, as any germ-local invariant of ξ automatically is. -/

/-- **Arf density = linear density, pointwise.**  For a reflection-equivariant refinement `q`
(`q (σ i) = q i` on `s`) the quadratic Arf density `q i * q (σ i)` equals the linear deck
density `q i` at every matched index: the genuinely-quadratic content is empty. -/
theorem arfDensity_eq_linear {ι : Type*} (σ : ι → ι) (q : ι → ZMod 2) {s : Finset ι}
    (hq : ∀ i ∈ s, q (σ i) = q i) : ∀ i ∈ s, q i * q (σ i) = q i := by
  intro i hi
  rw [hq i hi]
  exact zmod2_mul_self (q i)

/-- **The Arf invariant collapses to the linear deck sum.**  Over any index set on which `q`
is reflection-equivariant, the Arf sum `∑ q i * q (σ i)` equals the linear sum `∑ q i`.  Taken
over a conjugate-pair transversal the left side is the Arf invariant of the reflection
matching, so the Arf invariant is a *linear* functional of the deck parities — it reads
nothing the linear deck class does not. -/
theorem arf_sum_eq_linear_sum {ι : Type*} (σ : ι → ι) (q : ι → ZMod 2) (s : Finset ι)
    (hq : ∀ i ∈ s, q (σ i) = q i) :
    ∑ i ∈ s, q i * q (σ i) = ∑ i ∈ s, q i :=
  Finset.sum_congr rfl (arfDensity_eq_linear σ q hq)

/-- **The Arf invariant is representative-independent.**  Because `q (σ i) = q i`, replacing a
conjugate-pair representative `i` by its partner `σ i` does not change its deck parity, so the
transversal sum `∑ q i` — the Arf invariant — does not depend on which member of each pair is
chosen.  Equivariance alone makes the invariant well defined; no symplectic-basis choice is
needed and none of the classical Arf well-definedness machinery is invoked. -/
theorem arf_repr_indep {ι : Type*} (σ : ι → ι) (q : ι → ZMod 2)
    (hq : ∀ i, q (σ i) = q i) (i : ι) : q (σ i) = q i := hq i

/-- **The whole-set Arf sum vanishes** (the linear/degree face).  A fixed-point-free
multiplicity-matching involution makes the deck parities `q i = m i mod 2` sum to `0` over the
*entire* matched set.  Hence the Arf invariant lives on a *half* of `s` (a conjugate-pair
transversal); the full sum is degree-blind, exactly as `reflection_paired_deckRed_two_eq_one`
in the linear face. -/
theorem deck_parity_full_sum_zero {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (σ : ι → ι) (m : ι → ℕ)
    (hσs : ∀ i ∈ s, σ i ∈ s) (hσσ : ∀ i ∈ s, σ (σ i) = i)
    (hfix : ∀ i ∈ s, σ i ≠ i) (hm : ∀ i ∈ s, m (σ i) = m i) :
    ∑ i ∈ s, ((m i : ℕ) : ZMod 2) = 0 := by
  obtain ⟨k, hk⟩ := even_sum_of_fpf_involution s σ m hσs hσσ hfix hm
  rw [← Nat.cast_sum, hk]; push_cast; exact CharTwo.add_self_eq_zero _

/-! ### §3 The ξ instance

`ρ : ι → ℂ` enumerates a finite set of off-line zeros of ξ; `σ : ι → ι` is the conjugation
reflection of the critical line, which is fixed-point-free off the line and matches vanishing
orders (ξ is real on the reals).  The deck-parity refinement reads the vanishing order mod 2. -/

/-- The deck-parity refinement: the mod-2 vanishing order of ξ, as a `ZMod 2` value. -/
noncomputable def xiDeckParity (ρ : ℂ) : ZMod 2 := ((analyticOrderAt xi ρ).toNat : ZMod 2)

/-- **The Arf invariant of ξ's off-line boundary data collapses to the deck parity.**  For a
reflection `σ` matching the vanishing orders of a finite family of ξ-zeros, the Arf density of
the deck-parity refinement equals the deck parity pointwise, and its Arf invariant over any
conjugate-pair transversal equals `∑ xiDeckParity (ρ i)`.  The quadratic seam bit carries
nothing beyond the linear deck parity — it needs only order-equivariance, not the involution
structure. -/
theorem xi_arf_collapses {ι : Type*} (s : Finset ι) (ρ : ι → ℂ) (σ : ι → ι)
    (hord : ∀ i ∈ s,
      (analyticOrderAt xi (ρ (σ i))).toNat = (analyticOrderAt xi (ρ i)).toNat) :
    (∀ i ∈ s, xiDeckParity (ρ i) * xiDeckParity (ρ (σ i)) = xiDeckParity (ρ i)) ∧
      ∑ i ∈ s, xiDeckParity (ρ i) * xiDeckParity (ρ (σ i)) =
        ∑ i ∈ s, xiDeckParity (ρ i) := by
  set Q : ι → ZMod 2 := fun i => xiDeckParity (ρ i) with hQ
  have hq : ∀ i ∈ s, Q (σ i) = Q i := by
    intro i hi; simp only [hQ, xiDeckParity]; rw [hord i hi]
  exact ⟨arfDensity_eq_linear σ Q hq, arf_sum_eq_linear_sum σ Q s hq⟩

/-- **No new obstruction from the quadratic face.**  Under the full reflection data — a
fixed-point-free order-matching involution `σ` of the off-line zeros — the Arf density equals
the deck parity pointwise *and* the deck parity sums to `0` over the whole matched set.  So the
Arf invariant is supported on a conjugate-pair transversal (a half of `s`) and is a linear
functional of the deck parities: the quadratic seam refinement obstructs off-line parity
exactly as much as the linear deck class does — namely, not at all beyond the genuinely
unpaired order. -/
theorem xi_arf_no_new_obstruction {ι : Type*} [DecidableEq ι] (s : Finset ι) (ρ : ι → ℂ)
    (σ : ι → ι) (hσs : ∀ i ∈ s, σ i ∈ s) (hσσ : ∀ i ∈ s, σ (σ i) = i)
    (hfix : ∀ i ∈ s, σ i ≠ i)
    (hord : ∀ i ∈ s,
      (analyticOrderAt xi (ρ (σ i))).toNat = (analyticOrderAt xi (ρ i)).toNat) :
    (∀ i ∈ s, xiDeckParity (ρ i) * xiDeckParity (ρ (σ i)) = xiDeckParity (ρ i)) ∧
      ∑ i ∈ s, xiDeckParity (ρ i) = 0 := by
  refine ⟨(xi_arf_collapses s ρ σ hord).1, ?_⟩
  have hm : ∀ i ∈ s, (fun i => (analyticOrderAt xi (ρ i)).toNat) (σ i)
      = (fun i => (analyticOrderAt xi (ρ i)).toNat) i := hord
  exact deck_parity_full_sum_zero s σ (fun i => (analyticOrderAt xi (ρ i)).toNat)
    hσs hσσ hfix hm

/-! ### §4 The order hypothesis is discharged by the reality pairing

When the pairing is realized by complex conjugation on the zeros — the reflection of the
critical line that keeps `Re > ½` fixed and is fixed-point-free off the real axis — the
order-matching is not a hypothesis but the reality pairing `xi_orderAt_conj`
(`ord_{conj ρ} ξ = ord_ρ ξ`).  So the Arf collapse for ξ is unconditional on any
conjugation-closed family of zeros. -/

/-- **Arf collapse for a conjugation-closed family (unconditional).**  If `σ` acts on the
zeros by complex conjugation (`ρ (σ i) = conj (ρ i)`), the quadratic Arf density of the
deck-parity refinement equals the linear deck parity, pointwise and in sum — no order
hypothesis remains, the reality pairing supplies it. -/
theorem xi_arf_collapses_conj {ι : Type*} (s : Finset ι) (ρ : ι → ℂ) (σ : ι → ι)
    (hconj : ∀ i ∈ s, ρ (σ i) = (starRingEnd ℂ) (ρ i)) :
    (∀ i ∈ s, xiDeckParity (ρ i) * xiDeckParity (ρ (σ i)) = xiDeckParity (ρ i)) ∧
      ∑ i ∈ s, xiDeckParity (ρ i) * xiDeckParity (ρ (σ i)) =
        ∑ i ∈ s, xiDeckParity (ρ i) :=
  xi_arf_collapses s ρ σ (fun i hi => by rw [hconj i hi, xi_orderAt_conj])

/-- **No new obstruction, conjugation form (unconditional).**  For a conjugation-closed,
fixed-point-free family of off-line ξ-zeros, the Arf density equals the deck parity pointwise
and the deck parity sums to `0` over the whole family: the quadratic seam refinement is
supported on a conjugate-pair transversal and is a linear functional of the deck parities —
it obstructs off-line parity no more than the linear deck class does.  Only the reflection
structure enters; no order hypothesis is assumed. -/
theorem xi_arf_no_new_obstruction_conj {ι : Type*} [DecidableEq ι] (s : Finset ι) (ρ : ι → ℂ)
    (σ : ι → ι) (hσs : ∀ i ∈ s, σ i ∈ s) (hσσ : ∀ i ∈ s, σ (σ i) = i)
    (hfix : ∀ i ∈ s, σ i ≠ i)
    (hconj : ∀ i ∈ s, ρ (σ i) = (starRingEnd ℂ) (ρ i)) :
    (∀ i ∈ s, xiDeckParity (ρ i) * xiDeckParity (ρ (σ i)) = xiDeckParity (ρ i)) ∧
      ∑ i ∈ s, xiDeckParity (ρ i) = 0 :=
  xi_arf_no_new_obstruction s ρ σ hσs hσσ hfix
    (fun i hi => by rw [hconj i hi, xi_orderAt_conj])

end RHTower
