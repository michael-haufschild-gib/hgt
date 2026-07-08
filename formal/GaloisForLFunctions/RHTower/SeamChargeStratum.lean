/-
The Arf collapse, read positively: the *charge stratum* of RH-invariants — its floor, its
ceiling, and the residual that decides RH one level above it.

The negative result — no mod-2 winding/charge invariant of ξ's boundary data reads the divisor
mod 2 — is, turned over, a **location theorem** for RH inside the lattice of boundary invariants,
and a conservation law of the functional equation:

* **Floor — functional-equation conservation.**  Over a conjugation-closed family the total
  winding charge is `0` (`deck_parity_full_sum_zero`): the FE conserves the mod-2 charge to a
  value independent of RH.  The argument-principle / degree reading is pinned to `0` and sees
  nothing about the hypothesis.
* **Ceiling — the Arf collapse.**  The quadratic refinement equals the linear deck parity
  (`arfDensity_eq_linear`): there is no charge above the linear one.  The charge stratum is
  exhausted between floor and ceiling.
* **Residual — one level above the stratum.**  A single nonzero deck parity at a right-half
  point refutes RH (`xiDeckParity_ne_zero_imp_not_rh`).  This bit is reflection-conserved to `0`
  in total — no charge *sum* can certify it — yet a single set bit refutes RH.  It lives in the
  divisor sector, exactly where `rh2_tfae` places the deck coboundary `RHLadder 1`.

So RH is not a charge statement.  The functional equation pins every charge (degree, linear,
quadratic) to an RH-blind value; RH resolution requires the divisor/reality strata *above* the
charge ceiling.  A constraint — the conservation law — not a flow.
-/
import GaloisForLFunctions.RHTower.SeamArfCollapse

open Complex

namespace RHTower

/-! ### §1 The one-way RH obstruction carried by a single deck parity -/

/-- **A nonzero deck parity right of the line refutes RH.**  If `ξ` has odd vanishing order at a
point with `Re > 1/2`, that point is an off-line zero, so mathlib's `RiemannHypothesis` fails.  A
single mod-2 bit of the boundary divisor data is a sufficient condition for RH-failure — the
residual the charge stratum cannot certify but a set bit refutes. -/
theorem xiDeckParity_ne_zero_imp_not_rh {ρ : ℂ} (hρ : ρ ∈ rightHalf)
    (h : xiDeckParity ρ ≠ 0) : ¬ RiemannHypothesis := by
  rw [rh_iff_xi_ne_zero_right]
  intro hall
  have htoNat : (analyticOrderAt xi ρ).toNat ≠ 0 := by
    intro hz; apply h; unfold xiDeckParity; rw [hz]; simp
  have hord : analyticOrderAt xi ρ ≠ 0 := by
    intro hz; rw [hz] at htoNat; simp at htoNat
  exact hall ρ hρ (analyticOrderAt_ne_zero.mp hord).2

/-- **The half-parity obstruction.**  For any finite family of right-half points, a nonzero summed
deck parity refutes RH — some member is an odd-order off-line zero.  Over a conjugation-*symmetric*
family this total is `0` (the FE conservation), so the obstruction is carried by the upper-half
transversal alone: the *half-parity*, not the total charge. -/
theorem xi_sum_deckParity_ne_zero_imp_not_rh {ι : Type*} (s : Finset ι) (ρ : ι → ℂ)
    (hρ : ∀ i ∈ s, ρ i ∈ rightHalf)
    (h : ∑ i ∈ s, xiDeckParity (ρ i) ≠ 0) : ¬ RiemannHypothesis := by
  intro hrh
  apply h
  refine Finset.sum_eq_zero (fun i hi => ?_)
  by_contra hne
  exact xiDeckParity_ne_zero_imp_not_rh (hρ i hi) hne hrh

/-! ### §2 The charge stratum: floor, ceiling, residual -/

/-- **The charge stratum of RH.**  For a conjugation-closed, fixed-point-free family of off-line
ξ-zeros:

* **floor** — the total winding charge is `0` (functional-equation conservation, RH-independent);
* **ceiling** — the quadratic Arf density equals the linear deck parity (no charge above linear);
* **residual** — a single nonzero deck parity at a right-half point refutes RH.

RH is decided *above* this stratum, in the divisor sector; every charge reading is pinned to an
RH-blind value by the functional equation.  This is the Arf collapse read as a location theorem:
it fixes the floor and ceiling of what any winding/charge invariant of the seam can say, and shows
the hypothesis lives strictly higher. -/
theorem xi_charge_stratum {ι : Type*} [DecidableEq ι] (s : Finset ι) (ρ : ι → ℂ) (σ : ι → ι)
    (hσs : ∀ i ∈ s, σ i ∈ s) (hσσ : ∀ i ∈ s, σ (σ i) = i) (hfix : ∀ i ∈ s, σ i ≠ i)
    (hconj : ∀ i ∈ s, ρ (σ i) = (starRingEnd ℂ) (ρ i))
    (hR : ∀ i ∈ s, ρ i ∈ rightHalf) :
    (∑ i ∈ s, xiDeckParity (ρ i) = 0) ∧
      (∀ i ∈ s, xiDeckParity (ρ i) * xiDeckParity (ρ (σ i)) = xiDeckParity (ρ i)) ∧
      (∀ i ∈ s, xiDeckParity (ρ i) ≠ 0 → ¬ RiemannHypothesis) :=
  ⟨(xi_arf_no_new_obstruction_conj s ρ σ hσs hσσ hfix hconj).2,
    (xi_arf_collapses_conj s ρ σ hconj).1,
    fun i hi hne => xiDeckParity_ne_zero_imp_not_rh (hR i hi) hne⟩

end RHTower
