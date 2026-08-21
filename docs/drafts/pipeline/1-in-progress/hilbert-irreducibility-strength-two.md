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
| 15 | (in `Main`) | `exists_thin_bad`, `infinite_of_thin_bad`, `exists_regular_int_family`, `hilbert_irreducibility_family` | **DONE** |
| 16 | `Kronecker` | digits, `kron`, `kron_injOn`, `exists_kron_eq` (pullback) | **DONE** |
| 17 | `Multivariate` | `exists_factorisation`, `exists_exclusion`, `exists_infinite_specialisation` (CZ Thm 4) | **DONE** |
| 17b | `SeveralVariables` | `killFirst`/`kill1`/`spec0` frame, `step_emb`, `hilbert_several`, `hilbert_multivariate` | **DONE** |
| 17c | `HTGeometry/PrimeSubsetFactor` | divisor of a product of primes is a sub-product (reusable UFD lemma) | **DONE** |
| 18 | `GaloisResolvent` | `resolvent` of a monic polynomial; product formula; specialization | |
| 19 | `SeparatingLabel` | a `k : Fin D → ℚ` making the `D!` labelled actions distinct | |
| 20 | `ResolventIrreducible` | `card Gal(F) = D!` ⇒ `resolvent F` irreducible over `K` | |
| 21 | `GaloisSpecialization` | `card Gal(f_y) = D!` avoiding a prescribed `g` | |

### Step 3–4 detailed plan (the Galois layer)

**Already owned — do not rebuild.**  `HTGeometry.LabeledActionSymmetricPolynomial` *is* the universal
Galois resolvent:
* `labeledAction k π = ∑ j, C (k j) * X (π j)`, `rename_labeledAction` (equivariance),
* `labeledActionPoly k = ∏ π : Equiv.Perm σ, (Y - C (labeledAction k π))`,
* `isSymmetric_coeff_labeledActionPoly`, `exists_esymmAlgHom_coeff_labeledActionPoly`
  (**each coefficient is a polynomial in the elementary symmetric functions**),
* `eval_map_labeledActionPoly` (every labelled action value is a root).
`HTGeometry.ActionValueProduct` adds `isSymmetric_prod_of_equivariant` and the `eval₂` calculus.
`HTGeometry.SymmetricEsymmRepresentation.eval₂_of_bind₁_esymm` converts `esymmAlgHom` images into
evaluation at the elementary symmetric functions of a spectrum.

**18 — `GaloisResolvent`.**  For `A` commutative and `p : A[T]` monic of degree `D`, put
`esymmCoord p : Fin D → A`, `esymmCoord p i = (-1)^(i+1) * p.coeff (D - 1 - i)`, and
`resolvent k p := ∑ m, C (eval (esymmCoord p) (Q m)) * T^m` where `Q m` is the `esymm`
representative of `(labeledActionPoly k).coeff m`.  Two theorems:
* **product formula** — if `p = ∏ j, (T - β j)` in `A[T]` then
  `resolvent k p = ∏ π, (T - ∑ j, k j * β (π j))`;
* **specialization** — for any ring hom `φ : A →+* B`, `(resolvent k p).map φ = resolvent k (p.map φ)`
  (immediate: `resolvent` is a polynomial expression in the coefficients).
Also `Monic (resolvent k p)` and `natDegree = D !`.

**19 — `SeparatingLabel`.**  With `β : Fin D → L` injective (`L` a field of characteristic zero),
the bad `k` are the zeros of `∏_{π ≠ ρ} (∑ j, k j * (β (π j) - β (ρ j)))`, a nonzero polynomial in
`k`.  Needs: *a nonzero multivariate polynomial over an infinite integral domain has a non-root in
any infinite subring* — build by induction on the number of variables from
`Polynomial.eq_zero_of_infinite_isRoot`.

**20 — `ResolventIrreducible`.**  `F : K[T]` monic separable of degree `D`, `card F.Gal = D !`.
The `D!` labelled actions are the Galois orbit of one of them, so the minimal polynomial of
`θ = ∑ k_j β_j` has degree `D !`; it divides `resolvent k F` which is monic of the same degree,
so they are equal and `resolvent k F` is irreducible.

**21 — `GaloisSpecialization`.**  `resolvent k f` lives already in `(MvPolynomial (Fin m) ℚ)[T]`
(no denominator clearing).  It is monic and irreducible over `K`, hence irreducible over the UFD by
Gauss.  Apply `hilbert_multivariate`, avoiding `g`.  At a good `y`, `resolvent k (f_y)` is
irreducible of degree `D !`; it splits in the splitting field `L_y` of `f_y`, so
`D ! = [ℚ(θ_y) : ℚ]` divides `[L_y : ℚ] = card (f_y).Gal ≤ D !`.  Separability of `f_y` comes free:
a repeated root of `f_y` collides two labelled actions, contradicting irreducibility in
characteristic zero.

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
- 2026-08-21 — Step 2 done, axiom-clean.  `exists_infinite_specialisation` (CZ Theorem 4) and
  `hilbert_multivariate`:

      hilbert_multivariate : ∀ {m} {G : Polynomial (MvPolynomial (Fin m) ℚ)}, Irreducible G →
        1 ≤ G.natDegree → ∀ {g}, g ≠ 0 → ∃ y : Fin m → ℚ, eval y g ≠ 0 ∧
          Irreducible (G.map (eval y)) ∧ (G.map (eval y)).natDegree = G.natDegree

  Three design choices carried it: (i) the Kronecker map keeps the *specialized* variable in the
  **coefficient ring**, so `S_d : MvPolynomial (Fin k) ℚ[X] → ℚ[X][Y]` lands exactly in the shape the
  one-parameter theorem consumes; (ii) the subset-of-factors step is a general UFD lemma
  (`PrimeSubsetFactor`), not a bespoke argument; (iii) the induction never tracks the composite
  substitution — at the end any ℚ-algebra hom out of `MvPolynomial (Fin m) ℚ` *is* an `eval y`.
  The degree statement `natDegree` is preserved is carried through the induction for free by
  excluding the roots of `spec0 · G.leadingCoeff`.
- 2026-08-21 — Step 0 and Step 1 done.  `hilbert_irreducibility_family` (finite families) is proved
  and axiom-clean — obtained by splitting the strength-one proof at the regular parameter `s₀` and
  indexing the gap-thin sets by `Σ i, Idx i`, which is *much* cheaper than Coleman–Zwald's own
  route to it (their Theorem 2 goes through the Lemma-2 Galois machinery).  `Kronecker` is complete:
  `kron_injOn` (base-`d` digit uniqueness) and `exists_kron_eq` (digit existence).  Next: CZ
  Theorem 4.
- 2026-08-21 — created after strength one closed; both cards analysed and shown to need the same
  multivariate Galois-preserving statement; Castillo–Dietmann shown to be used only existentially.
