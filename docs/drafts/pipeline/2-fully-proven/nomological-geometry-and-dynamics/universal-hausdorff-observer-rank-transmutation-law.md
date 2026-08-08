# Universal Hausdorff observer and rank-complementarity law

- **ID:** `clg-universal-hausdorff-observer-rank-complementarity`
- **Stage:** 2 — fully proved on paper
- **Status:** `[PAPER-PROVED] [ROUTE-INDEPENDENT OBSERVER THEOREM] [NON-RH]`
  `[NO LEAN WRITTEN OR BUILT]`
- **Purpose:** identify the canonical information seen by every Hausdorff group observer of a
  nonclosed quotient and compute its exact cofinal rank ledger with hypertranscendental depth and
  stack isotropy in the multiple-Gamma lawstack.

## 1. Universal theorem

Let `G` be a Hausdorff topological abelian group and `H subset G` any subgroup. Give `G/H` the
quotient topology and write `bar H` for the closure of `H`.

### Theorem 1.1 — Hausdorff reflection of a quotient group

The canonical map

\[
 \eta_H:G/H\longrightarrow G/\overline H
\tag{1}
\]

is the universal continuous homomorphism from `G/H` to a Hausdorff topological group. Precisely,
for every Hausdorff topological group `Y` and every continuous homomorphism `f:G/H->Y`, there is a
unique continuous homomorphism `bar f:G/bar H->Y` with `f=bar f eta_H`.

Moreover,

\[
 \ker\eta_H=\overline H/H,
\tag{2}
\]

this kernel is the closure of the identity in `G/H`, and `G/H` is Hausdorff exactly when `H` is
closed.

#### Proof

Let `q:G->G/H`. The composite `F=fq:G->Y` is continuous and vanishes on `H`. Since `Y` is
Hausdorff, `{0}` is closed, so `ker F` is closed. Hence `bar H subset ker F`, and `F` factors
uniquely through a continuous homomorphism `bar f:G/bar H->Y`. The identity `f=bar f eta_H` follows
because `q` is quotient. Uniqueness follows from surjectivity of `G->G/bar H`.

Formula `(2)` is immediate. Since `q^(-1)(q(bar H))=bar H`, the quotient definition makes
`q(bar H)` closed. Conversely, if `C subset G/H` is closed and contains the identity coset, then
`q^(-1)(C)` is closed and contains `H`, hence contains `bar H`; therefore `C` contains `q(bar H)`.
So `q(bar H)=bar H/H` is exactly the closure of the identity. The identity is closed exactly when
`H=bar H`; for a topological group, `T_1` and Hausdorffness of the quotient by a subgroup are
equivalent to closedness of that subgroup. ∎

## 2. Multiple-Gamma observer theorem

Use the marked period subgroups

\[
 \Lambda_m=
 \left(\mathbb Z+\frac\pi m\mathbb Z\right)+i\mathbb Z
 \quad(m<\infty),
 \qquad
 \Lambda_\infty=\mathbb Z+i\mathbb Z.
\tag{3}
\]

Let

\[
 Q_m=\mathbb C/\Lambda_m,
 \qquad
 Q_m^{\rm H}=\mathbb C/\overline{\Lambda_m}
\tag{4}
\]

be the coarse quotient and its universal Hausdorff observer. Define `h_m` as the real Lie
dimension of `Q_m^H`.

### Theorem 2.1 — observer-dimension wall

For finite `m`,

\[
 Q_m^{\rm H}cong\mathbb R/\mathbb Z,
 \qquad h_m=1.
\tag{5}
\]

At the boundary,

\[
 Q_\infty^{\rm H}=Q_\infty
 \cong\mathbb R^2/\mathbb Z^2,
 \qquad h_\infty=2.
\tag{6}
\]

Every continuous homomorphism from `Q_m` to any Hausdorff group factors through `(5)` or `(6)`.
Thus at finite `m` every regular Hausdorff observer erases the entire dense real closure direction;
at the boundary that direction becomes a genuine observable circle.

#### Proof

For finite `m`, density of `Z+(pi/m)Z` in `R` gives

\[
 \overline{\Lambda_m}=\mathbb R+i\mathbb Z.
\]

The map `z->Im(z) mod Z` has exactly that kernel, proving `(5)`. At the boundary `Lambda_infinity`
is already a lattice, proving `(6)`. Universal factorization is Theorem 1.1. ∎

## 3. Three-way rank conservation

Let `d_m=d_DA(Gamma_m)` be the proved transverse differential-algebraic depth, let
`s_m=rank_Z Stab(P_m)` be the rank of the period-action lawstack stabilizer, and let `h_m` be the
Hausdorff observer dimension above.

### Corollary 3.1

For every finite `m` and at the boundary,

\[
 \boxed{d_m+s_m=1,}
 \qquad
 \boxed{d_m+h_m=2,}
 \qquad
 \boxed{h_m-s_m=1.}
\tag{7}
\]

#### Proof

For finite `m`, `(d_m,s_m,h_m)=(1,0,1)`. At the boundary it is `(0,1,2)`. Substitute. ∎

Equation `(7)` gives an exact three-organ complementarity ledger:

\[
 \text{finite ledger }(d,s,h)=(1,0,1),
 \qquad
 \text{boundary ledger }(d,s,h)=(0,1,2).
\tag{8}
\]

The word “unit” refers to rank bookkeeping in `(7)`, not to an isomorphism between the three
objects. No transport functor between the finite quotients and boundary quotient is constructed,
so the theorem does not assert causal conversion of one organ into another.

## 4. Coordinate-free consequence

This theorem isolates a recurring corpus mechanism without selecting a route:

1. nonclosed source orbits contain information that no Hausdorff group observer can read;
2. completing/closing the source does not recover that information—it quotients it by `bar H/H`;
3. a wall can convert an invisible dense direction into a visible compact direction while
   simultaneously creating stack isotropy;
4. the full lawstack retains both coarse observer and isotropy data, whereas either alone gives an
   incomplete account.

This is a precise version of “making one face exact makes another face hidden.” It is not a
Heisenberg inequality and does not claim that every corpus obstruction comes from a quotient
group.

## 5. Scope

- Theorem 1.1 is classical topological-group mathematics; significance here is its exact coupling
  to the non-RH HT lawstack.
- Only continuous **homomorphisms** to Hausdorff groups satisfy the stated universal property.
  Arbitrary nonlinear set-valued observers are outside the theorem.
- The multiple-Gamma DA-depth input is imported; it is not re-proved here.
- No RH statement, Xi zero, positivity, or source selector occurs.
- No metric cost follows from Hausdorff reflection.

## 6. Corpus support

The period closure and DA-depth facts are imported from:

- `multiple-gamma-period-action-lawstack-three-shadow-theorem.md`;
- `pipeline/3-formalized/new_scientific_knowledge/gamma/multiple-gamma-period-excess-closure-phase-transition.md`.

Formal files were read only. No Lean code was written or built.

## 7. Formalization boundary

Do not write Lean now. A later formalization needs a declared category of topological groups and
quotient topology; the rank identities can then be separated from special-function imports.
