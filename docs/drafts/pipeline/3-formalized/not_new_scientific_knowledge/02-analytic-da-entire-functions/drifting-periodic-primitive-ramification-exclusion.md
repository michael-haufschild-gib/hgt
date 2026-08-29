# Drifting periodic primitives have no totally ramified values

- **ID:** `drifting-periodic-primitive-ramification-exclusion`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Scientific status:** `[BRIDGE] [PROVED HERE] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Lane:** general hypertranscendence; primitive ramification
- **Statement:** A primitive of a periodic entire function with nonzero additive period drift has no totally ramified finite value.

## Theorem

Let `W` be a nonconstant entire function. Suppose there are nonzero constants `T,C` such that

`W(z+T)=W(z)+C.`

Then `W` has no totally ramified finite value.

## Proof

Differentiation gives

`W'(z+T)=W'(z)`.

Assume that `a` is a totally ramified value of `W`. For every integer `n`, the value

`a+nC`

is also totally ramified. Indeed, if `W(z)=a+nC`, then

`W(z-nT)=a`,

so `W'(z-nT)=0`; periodicity of `W'` gives `W'(z)=0`.

The values `a+nC` are pairwise distinct. This produces infinitely many totally ramified finite values, contradicting the Nevanlinna ramification theorem, according to which a nonconstant entire function has at most two totally ramified finite values. Therefore no such `a` exists.

## Autonomous first-order corollary

Let `w` be a transcendental entire autonomous first-order DA function and let `W'=w`. The Briot--Bouquet classification gives

`w(z)=L(exp(az))`

for a nonconstant Laurent polynomial `L` and `a!=0`. With `T=2 pi i/a`, integration gives

`W(z)=c_0 z+M(exp(az))`,

where `c_0` is the constant Laurent coefficient of `L`. Hence

`W(z+T)-W(z)=c_0 T.`

If `c_0=0`, then `W` is algebraic over `C(exp(az))`, and `exp(az)` is algebraic over `C(w)`; thus `W` is algebraic over the derivative field and its primitive defect is zero.

If the primitive defect is one, necessarily `c_0!=0`. The theorem applies and shows that `W` has no totally ramified finite value.

Consequently an autonomous first-order entire derivative cannot realize the quadratic matching residue

`W=a+g^2`

with an entire function `g` and primitive defect one.

## Parent-theory verdict

The proof is a direct application of quasi-periodic drift and the classical Nevanlinna ramification bound. It is useful boundary closure, not new scientific knowledge.

## Gates

- [x] Complete proof.
- [x] Autonomous first-order primitive-defect dichotomy.
- [x] Quadratic matching consequence.
- [x] Anti-theatre gate; bridge verdict.

## Primary references

1. Classical Nevanlinna second main theorem with ramification.
2. Classical Briot--Bouquet classification, as recorded in A. E. Eremenko, *Meromorphic solutions of algebraic differential equations*, Russian Math. Surveys 37:4 (1982), 61--95.

## Formalization (2026-08-29) — complete

`formal/GaloisForLFunctions/HTGeometry/DriftPeriodicRamification.lean` and
`formal/GaloisForLFunctions/HTGeometry/DriftRamificationExclusion.lean`, both wired into
`GaloisForLFunctions.HTGeometry`.  Every statement is unconditional; `#print axioms` gives only
`propext, Classical.choice, Quot.sound`.

| Card step | Lean name |
|---|---|
| total ramification of a value | `TotallyRamified` |
| `W(z + nT) = W(z) + nC` for every `n ∈ ℤ` | `drift_zsmul` |
| **`W'` is `T`-periodic** | `deriv_drift_periodic`, `deriv_drift_zsmul` |
| **`a` totally ramified ⟹ so is `a + nC`** | `totallyRamified_add_zsmul` |
| the values `a + nC` are pairwise distinct | `drift_values_injective` |
| arbitrarily many totally ramified finite values | `exists_finset_totallyRamified_card_ge` |
| **the theorem: no totally ramified finite value** | `not_totallyRamified_of_drift` |
| **quadratic matching consequence** | `not_quadratic_matching_of_drift` |
| the normal form `c₀z + M(e^{αz})` drifts by `c₀·2πi/α` | `drift_of_exp_normalForm` |

The Nevanlinna ramification bound the proof contradicts is itself now Lean-proved, unconditionally,
as `card_totallyRamified_le_four` in
`formal/GaloisForLFunctions/HTGeometry/NevanlinnaRamification.lean`: an entire function has at most
four pairwise separated totally ramified finite values.  Four rather than the sharp two is
deliberate — the drift supplies arbitrarily many ramified values, so any finite bound closes the
card, and the constant `4` is what the clean form `(q/2 − 2)·T(r,f) ≤ S(r,f) + O(1)` of the second
main theorem gives without the sharpening.  The full chain behind it is recorded in the folder
ledger under **I5**.

Two points of the informal proof needed correction or supplementation in Lean:

* `TotallyRamified W a` as formalised (`∀ z, W z = a → W' z = 0`) is also satisfied by a value `W`
  omits.  The affine case `W(z) = (C/T)z + W(0)` is therefore handled separately, by exhibiting the
  `a`-point `(a − W(0))·T/C` at which `W' = C/T ≠ 0`.
* The ramification bound needs `W` transcendental, in the form of two growth conditions on its
  characteristic.  These are not extra hypotheses here but consequences of the drift, by an argument
  that avoids Picard's theorem entirely: `g(z) := W(z) − (C/T)z − W(0)` vanishes at every lattice
  point `nT`, so `N(r, 0, g) ≥ (log 2)(r/‖T‖ − 2)` (`logCounting_zero_ge_of_lattice_zeros`); the
  first main theorem converts this into a linear lower bound for `T(r,g)`
  (`exists_characteristic_ge_of_lattice_zeros`), and subtracting the affine part costs only a
  logarithm (`drift_characteristic_growth`).  If instead `g ≡ 0` then `W` is affine, the case
  already dealt with.

The autonomous first-order corollary quotes the Briot–Bouquet classification, as the card's own
reference list records; the two steps that follow it — that the normal form drifts, and that the
drift excludes the quadratic matching residue — are the Lean statements above.
