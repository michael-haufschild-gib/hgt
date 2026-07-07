# 131 — The cross-boundary cochain: the σ_p-defect that escapes the pinned-germ collapse [PROVED HERE]

Formal home: `formal/GaloisForLFunctions/RHTower/CutoffCochain.lean`
(all endpoints axiom-clean; abstract structural lemmas depend only on `propext`; the matrix witnesses
on `[propext, Classical.choice, Quot.sound]`; full `MainTheorems` gate green, 9260 jobs).

Doc 130 proved every **pinned-germ** model of the `{σ_p}`-defect is fake (freeness, unit, commutator
— three collapses). It named the surviving form: a **non-commutator cross-boundary cochain**, σ_p
pushing mass across a cutoff. This document **constructs that object** as an abstract operator-algebra
structure, proves it exists and escapes the collapse, and identifies exactly the one remaining step —
which is the literature/apex boundary, not an un-attempted lemma.

## 1. The object, built [PROVED HERE]

A **cutoff** is an idempotent `e` in an operator ring `E` (`e² = e`): the projection onto the kept
region of a two-region split (inside/outside `|x| = λ`). The **cross-boundary cochain** of an operator
`a` is the lower corner `crossBoundary e a = (1 − e)·a·e` — the mass `a` pushes out of the cutoff. Its
proved structure:

- **Additive** (`crossBoundary_add`), **kills the identity** (`crossBoundary_one`): a genuine linear
  cochain, and the cutoff does not cross itself.
- **A corner of the inner derivation** (`crossBoundary_eq_corner_commutator`):
  `(1 − e)·a·e = −(1 − e)·[e, a]`, `[e,a] = e·a − a·e`. The cochain measures the failure of `a` to
  commute with the cutoff — a commutator with the **cutoff** `e`, sharply distinct from the fake
  commutator with the divisor **presentation** `A` (doc 130).
- **Square-zero** (`crossBoundary_mul_crossBoundary`): `(crossBoundary e a)·(crossBoundary e b) = 0`,
  because `e·(1 − e) = 0` — mass cannot cross out twice in a row. The cochains span a square-zero set:
  the first-order (defect) structure.
- **Semicommutator / Toeplitz–Hankel law** (`compression_semicommutator`, `compression_mul`): the
  compression `c(a) = e·a·e` multiplies up to a boundary correction,
  `c(ab) = c(a)·c(b) + upper(a)·lower(b)`. (Peirce/Toeplitz–Hankel algebra is classical; the object it
  is applied to — the σ_p-defect — is the lane's.)

## 2. The collapse, unified [PROVED HERE]

`crossBoundary_eq_zero_of_commute`: if `a` commutes with the cutoff `e`, the cochain is `0`.
`crossBoundary_smul_one`: a **central scalar** `c·1` crosses no boundary. At a pinned germ the prime
action `σ_p` is multiplication by the unit `p^(−s)` — a scalar, hence central, hence commuting with
**every** cutoff. So its cross-boundary cochain is `0`. This is the **single algebraic root** of all
three doc-127/128/130 collapses: the free reference is a coboundary, the unit has order 0, the
commutator with the presentation is fake — because *a germ-local action is central, and a central
action crosses no boundary*. One theorem now explains the whole no-go stack.

## 3. The escape exists [PROVED HERE]

`exists_nonfake_crossBoundary`: there is a cutoff `e`, a boundary-**crossing** action `σ` (not
commuting with `e`), and a torsion seam presentation `A` with `det A = Xᵐ`, such that the
cross-boundary cochain `(1 − e)·σ·e` has a **nonzero** Fitting boundary class in `R[X]/(Xᵐ)`.
`exists_nonfake_crossBoundary_not_commutator`: that cochain is therefore **not** a commutator with the
presentation (doc 130). Moreover it is outside **both** fake classes:
`exists_crossBoundary_not_right_factor_mod_X_pow` (`Δ ∉ A·End + (Xᵐ)` — the charter §13 target
theorem, now instantiated by the cross-boundary construction) and
`exists_crossBoundary_not_left_factor_mod_X_pow` (`Δ ∉ End·A + (Xᵐ)` — not a source basis-change
artifact). The object doc 130 said must exist, exists — and only for a non-central, boundary-crossing
action. The pinned-germ collapse is not a wall; it is a **selection rule**: it excludes exactly the
central (germ-local) actions and admits exactly the boundary-crossing ones.

## 4. The two-cutoff asymmetry — the Sonin shape [PROVED HERE]

`crossBoundary_two_cutoff_asymmetry`: there are two cutoffs `e, f` and an action `σ` that commutes
with `e` (so `crossBoundary e σ = 0`) yet crosses `f` (`crossBoundary f σ ≠ 0`). Compatibility with
one boundary does not imply compatibility with another. This is the abstract Sonin double-vanishing
obstruction: an action can respect one cutoff while crossing the other. It is exactly why the σ_p
defect is invisible to the physical cutoff (σ_p = scaling by `p` preserves the large-`|x|` region) and
visible only to the Fourier cutoff (the dual condition `f̂|_{|x|<λ} = 0`) — the two cutoffs do not
commute, and σ_p crosses the second.

## 5. What is proved, and the one remaining step (the exact boundary)

**Proved, unconditionally, in Lean:** the cross-boundary cochain is a well-defined square-zero
derivation-corner cochain; it vanishes on exactly the central/germ-local actions (unifying every prior
collapse); a boundary-crossing action produces a non-fake, non-commutator instance; and the two-cutoff
asymmetry realizes the Sonin shape. The abstract object is complete — every structural fact it carries
is banked.

**The one remaining step is the arithmetic realization**, and it is precisely the literature/apex
boundary, not an un-attempted lemma:

- Realize the two cutoffs as the **physical** and **Fourier** cutoffs on an actual local/semilocal
  field, and σ as the actual scaling/`p`-place action. That construction **is** the Connes–Consani–
  Moscovici semilocal Sonin/prolate space (doc 129 §2; arXiv:2310.18423) — **literature**, not to be
  reproduced (rule 8). The lane's instruments (the collapse selection rule §2, the non-fake criterion
  §3) are what that construction must be tested against, and are the contribution.
- Produce the germ-level intrinsic version — a cross-boundary cochain built from the primes and `∂_s`
  **without importing ζ** whose class is the ξ-divisor — is the **missing Weil cohomology / Hilbert–
  Pólya apex** (doc 129 §4). Known-open. Not faked, not claimed.

The reason the only known construction (Connes' trace formula) is **trace-level** and not
**germ-level** is now a theorem, not a slogan: §2 proves every germ-local (central) σ_p-action has zero
cross-boundary cochain, so a nonzero one *must* be non-local — it must move mass across the cutoff,
which is a trace-level/adelic operation. The pinned-germ register is closed by a selection rule; the
live register is the cutoff-crossing (non-local) one; and the passage from the abstract cutoff-crossing
cochain (built here) to the arithmetic one (the two actual Sonin cutoffs with the actual σ_p) is the
single, sharply-located step that is either the cited literature or the named apex. There is no
intermediate pinned-germ construction left to attempt — the collapse selection rule (§2) proves there
cannot be one.

## 6. The deck ↔ cross-boundary bridge is refuted [PROVED HERE]

The lane carries **two** two-region structures. The deck ladder is a **multiplicative** two-chart
gluing cocycle: `deckClass g₁ g₂ = (g₁/g₂)|_{chart⁺} / (g₁/g₂)|_{chart⁻}`, valued in roots of unity,
equal to `exp(2πi·m/2^k)` (`XiDeck`). The natural conjecture was that the cross-boundary cochain is
its additive `log`-face — the two readings of one obstruction. **That is false, and provably so:**

- `crossBoundary_eq_zero_comm`: in a **commutative** ring the cross-boundary cochain is **identically
  zero** (`(1 − e)·a·e = a·(e − e²) = 0`). The deck class is a commutative object — a ratio of scalar
  function values, valued in the abelian group `μ_{2^k}`. Where the deck class lives, the
  cross-boundary cochain vanishes; it cannot be its `log`.
- `crossBoundary_trace_zero`: the cross-boundary cochain is **traceless**
  (`tr((1 − e)·a·e) = tr((e(1 − e))·a) = 0`). The deck class factors through an abelian/trace-type
  invariant; the cross-boundary lives entirely in the traceless part. They are orthogonal, not
  `log`/`exp`-related.

So the deck ladder (commutative, abelian, circular — doc 128) and the cross-boundary cochain
(non-commutative, traceless, non-circular) are **not** the two faces of one gluing datum. The
cross-boundary cochain carries content **only** in a genuinely non-commutative operator algebra — it
needs the action not to commute with the cutoff, which is the non-local Fourier structure. A real
coupling of the two would have to pair the non-commutative traceless cochain with the abelian deck
class through a nontrivial pairing — and a pairing of a traceless operator cochain with an abelian
class over a non-commutative algebra **is** Connes' cyclic cohomology / the trace-formula pairing:
literature (rule 8) or the missing-Weil apex. The last non-barred forward move collapses into the §5
boundary: there is no elementary deck ↔ cochain bridge, and the only coupling is the cited
trace-level construction. The abelian ladder and the non-commutative cochain meet only where Connes
already put them — at the trace, not at a germ.
