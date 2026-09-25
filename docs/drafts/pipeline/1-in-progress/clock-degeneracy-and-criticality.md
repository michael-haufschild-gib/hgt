# The clock, its degeneracy, and why the system is critical

**Status:** infrastructure Lean-closed (axiom-clean). Producer **specified, not built**.
**Module:** `RHTower/ClockDegeneracy.lean`.
**Ledger:** MUST-410, CANNOT-411 (on CANNOT-405/407, MUST-406/408).

## The dictionary is forced

Three involutions of `ℂ` preserve `Div(ξ)`:

| map | ordinate | real part | physics |
|---|---|---|---|
| `ρ ↦ ρ̄` | reversed | fixed | **T** |
| `ρ ↦ 1 − ρ` | reversed | reflected | **PT** |
| `σ : ρ ↦ 1 − ρ̄` | **fixed** | reflected | **P** |

The hypothesis is the triviality of the third. So **RH = parity is unbroken**; a free orbit is a
**parity doublet** — two distinct states at one instant.

## What is proved

```
ncard_xiSlice t :
  (xiSlice t).ncard = (xiSliceFixed t).ncard + 2 * (xiSliceLeft t).ncard
ncard_xiSliceFixed_le_one t : (xiSliceFixed t).ncard ≤ 1          -- unconditional
riemannHypothesis_iff_ncard_xiSlice_le_one :
  RiemannHypothesis ↔ ∀ t, (xiSlice t).ncard ≤ 1
odd_ncard_xiSlice_iff t :
  Odd ((xiSlice t).ncard) ↔ (xiSliceFixed t).Nonempty              -- unconditional
```

**RH = the clock is a complete observable**: reading the time determines the state. And with no
hypothesis at all: **the number of states at an instant is odd exactly when the critical point at
that height is a zero.**

## Falsifier test on the previous cycle's producer (MUST-409 discipline)

- *Does a space with the `ℤ/2`-action exist?* **Yes** — `(ℂ, σ)` is a real form whose fixed locus is
  the critical line, and the informative object is `ℂ ∖ Div(ξ)`.
- *Is Kirwan the machine?* **No.** Kirwan needs a compact connected group and a Hamiltonian action;
  `ℤ/2` is finite. **Wrong machine — rejected before development, as MUST-409 requires.**
- *What is the right machine?* Smith theory for real varieties. For `X = ℂ ∖ Div`, Smith–Thom reads
  `N₀ ≤ N_distinct` with **equality ⟺ RH**: the hypothesis is **Harnack maximality** of the
  complement of the zero set. Honest note: equality is again the critical-zero count, so this is a
  translation, not yet leverage.

## The criticality diagnosis (CANNOT-411)

The heat deformation moves zeros by a Calogero flow; off-line pairs merge and become critical. Its
threshold `Λ` satisfies `Λ ≤ 0 ⟺ RH` and `Λ ≥ 0` unconditionally (Rodgers–Tao). Hence

> **RH ⟺ `Λ = 0`** — the configuration sits exactly on the parity-breaking boundary, from the
> unbroken side. In equivariant terms `Λ` is *the time required to make the action formal*, and RH
> says none is required and none is to spare.

This explains the ledger's most repeated pattern in one stroke. Eight separate walls —

- every estimate one power of `log` short (CANNOT-402);
- no mollifier profile improves the exponent `2θ` (CANNOT-304/305);
- the certifiable Gaussian widths are exactly the trivial ones (CANNOT-333);
- lag exponent `½` provable, `0` is RH, nothing between (MUST-242);
- Weil rate `e^A` trivial, any rate `<1` is a zero-free strip (MUST-261);
- positivity marginal, no spectral gap on any window (MUST-234);
- every prime power load-bearing (MUST-233);
- any nonzero change of one prime weight breaks positivity (MUST-363)

— are not eight coincidences. They are the universal signature of a system **at a critical point**,
where the true value saturates every bound.

## The producer's specification

**A producer cannot be an inequality.** At criticality no inequality has slack; that is what the
eight walls measure. It must be an **exact marginality identity**: a statement that a marginal
quantity is exactly marginal — a *vanishing derivative*, not a *bound on a size*.

Concretely, the target is: show `Λ = 0` directly, i.e. that the flow requires no time — equivalently
that the parity action is already formal — by an identity rather than an estimate.

## Falsifiers

1. `Λ ≥ 0` is a deep theorem (Rodgers–Tao) not in the corpus; any argument leaning on `Λ = 0`
   must either import it or avoid it.
2. "Exact marginality identity" is a specification, not a construction. If no candidate identity is
   exhibited in one cycle, this card is a diagnosis only and should be marked so.
3. Smith–Thom equality for `ℂ ∖ Div` is a translation of the critical-zero count, not leverage;
   do not cite it as progress.
