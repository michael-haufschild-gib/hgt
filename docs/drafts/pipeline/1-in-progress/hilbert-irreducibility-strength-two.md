# Hilbert irreducibility, strength two: multivariate + Galois-preserving

- **ID:** hilbert-irreducibility-strength-two
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper complete) — target is an unconditional Lean 4 proof
- **Depends on:** `3-formalized/hilbert-irreducibility-theorem.md` (strength one, CLOSED)

## Why a second strength

Strength one (`hilbert_irreducibility`, Lean-closed) says: `F ∈ ℚ[X][Y]` irreducible ⇒ infinitely
many `b ∈ ℚ` with `F(b,Y)` irreducible.  Neither top-level card can consume that directly:

* `algebraic-two-local-instant-exact-complexity` §1 needs *"a Zariski-dense set of rational
  coefficient specializations whose characteristic polynomial still has Galois group `S_D`; we may
  simultaneously avoid the discriminant and any prescribed nonzero polynomial"* — i.e. **several
  parameters**, **Galois group preserved**, **avoidance**.
* `arithmetic-static-local-hardness-recurrence-window-law` Theorem C step 1 needs the same, and
  cites Castillo–Dietmann `(41)` for it.  **But it uses `(41)` only existentially** — the counting
  exponent `H^{m-1+[S_D:K]^{-1}+η}` is a vehicle for "the bad set is `o(H^m)`, so some good point
  exists in the box".  A qualitative multivariate Galois-preserving statement discharges it, and
  the Castillo–Dietmann citation can be dropped.

So the honest second strength is **not** the counting theorem: it is

> **Target.** For `f ∈ (ℚ[Y₁,…,Y_m])[X]` monic of degree `D`, separable, with Galois group `S_D`
> over `ℚ(Y₁,…,Y_m)`, and any nonzero `g ∈ ℚ[Y₁,…,Y_m]`, there exists `y ∈ ℚ^m` with `g(y) ≠ 0`
> and `Fintype.card ((f.map (eval y)).Gal) = D !`.

The literal Castillo–Dietmann counting bound is recorded below as an optional strength three; it is
*not* needed by either card.

## Route (all elementary; Coleman–Zwald arXiv:1809.10977 §2–§3)

**Step 0 — finite families.**  Kronecker needs "infinitely many `b` making *all* of
`g₁(b,·),…,g_r(b,·)` irreducible".  Coleman–Zwald get this from their Lemma 2/Prop 3 Galois
machinery (Theorem 2).  **We get it much more cheaply**: our own proof already assembles finitely
many gap-thin sets, so we only have to (i) split `hilbert_irreducibility_int` into a `s₀`-parameterised
"thin bad set" theorem and the assembly, and (ii) choose one regular `s₀` for the whole family and
index by `Σ j, Idx j`.

**Step 1 — Kronecker specialization** (CZ §3).  `S_d(f)(X,Y) = f(X, Y, Y^d, …, Y^{d^{k-2}})` is an
algebra map, hence automatically multiplicative; the only real content is that it is *injective on
the polynomials of degree `< d` in each of `X₂,…,X_k`*, by uniqueness of base-`d` digits.

**Step 2 — CZ Theorem 4 + Corollary 2.**  Factor `S_d(f) = g(X)·∏ g_i(X,Y)` into irreducibles; by
Step 0 infinitely many `b` make every `g_i(b,·)` irreducible; a factorisation of `f(b,X₂,…,X_k)`
would pull back through the Kronecker bijection to a factorisation of `f`.  Induction on the number
of specialised variables, discarding the roots of a prescribed `p`, gives avoidance.

**Step 3 — the Galois resolvent.**  Choose `c ∈ ℚ^D` with trivial `S_D`-stabiliser for
`θ = Σ cᵢαᵢ` (the bad `c` form a finite union of proper subspaces).  Put
`Res(f)(T) = ∏_{σ∈S_D} (T − Σᵢ cᵢ α_{σ(i)})`.  Its coefficients are symmetric in the roots, so by
the corpus' `SymmetricEsymmRepresentation.exists_eval₂_esymm_repr_of_isSymmetric` they are given by
a **fixed** polynomial in the elementary symmetric functions, i.e. in the coefficients of `f` —
hence `Res` is a universal construction and **commutes with specialisation**:
`Res(f)_y = Res(f_y)`.

**Step 4 — Galois preservation.**  `Gal(f/K) = S_D` ⇒ `Res(f)` is irreducible over `K` (one Galois
orbit of size `D!`).  Apply Step 2 to `Res(f)` (avoiding `g` and the discriminant).  At a good `y`,
`Res(f_y)` is irreducible of degree `D!`, so `[ℚ(θ_y):ℚ] = D!`; `θ_y` lies in the splitting field of
`f_y`, so `D! ≤ |Gal(f_y)| ≤ D!`.  **No specialisation-of-Galois-extensions machinery is needed** —
this is the payoff of the resolvent being universal.

## Lean module plan (`HTGeometry/HilbertIrreducibility/`)
| # | module | content | state |
|---|---|---|---|
| 15 | `Family` | `s₀`-parameterised thin-bad-set form; HIT for a finite family | |
| 16 | `Kronecker` | `S_d`, injectivity on bounded-degree polynomials | |
| 17 | `Multivariate` | CZ Theorem 4; Corollary 2 (avoidance, several variables) | |
| 18 | `GaloisResolvent` | universal `Res(f)`, `Res(f)_y = Res(f_y)`, separating `c` | |
| 19 | `GaloisSpecialization` | `Gal(f_y) = S_D` for a Zariski-dense set of `y` | |

## Assets already owned (do not rebuild)
* strength-one HIT: `HilbertIrreducibility.hilbert_irreducibility` (+ `_int`, thin-set stack).
* fundamental theorem of symmetric polynomials: `HTGeometry.SymmetricEsymmRepresentation`
  (`exists_bind₁_esymm_of_isSymmetric`, `exists_eval₂_esymm_repr_of_isSymmetric`),
  `SymmetricCoefficientNonSquare.esymmAlgEquiv`, `SymmetricCoefficientField`.
* generic Galois group is `S_D`: `HTGeometry.GenericPolynomialSplitting.genericMonicGaloisEquiv`,
  `CenteredGenericGalois.centeredGaloisEquiv`, `PermutationAction.symmetricFixedFieldGaloisEquiv`.
* Gauss's lemma, resultants, `Polynomial.Gal`, `galActionHom` — mathlib.

## Optional strength three (NOT needed by either card)
Castillo–Dietmann, *On Hilbert's irreducibility theorem* (arXiv:1602.00314): the number of
`Y ∈ ℤ^m`, `‖Y‖_∞ ≤ H`, whose specialised Galois group lies in a fixed proper `K < G` is
`O_{f,η}(H^{m-1+[G:K]^{-1}+η})`.  This is a genuine counting theorem (large sieve / Lang–Weil
input) and is a separate project.  Record it as *not* on the critical path.

## Log
- 2026-08-21 — created after strength one closed; both cards analysed and shown to need the same
  multivariate Galois-preserving statement; Castillo–Dietmann shown to be used only existentially.
