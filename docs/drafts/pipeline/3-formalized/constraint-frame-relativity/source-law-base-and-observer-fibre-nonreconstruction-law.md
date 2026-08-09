# Source-law base and observer-fibre nonreconstruction law

- **ID:** `cfr-source-law-base-nonreconstruction`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper) / HIGHER-FIELD PIVOT
- **Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [HT AND STOKES CALIBRATIONS] [NOT RH] [FORMALIZED IN LEAN]`
- **Formalized companion:** `source-law-base-and-observer-fibre-nonreconstruction-law-formalized.md`
- **Statement:** Coefficient-doctrine choice, prolongation index, aperture, and history do not determine the governing constraint law. The theorem forces an additional law variable; modeling it by a stratified base is provisional.

## Goal

Hostile test of the original four-axis CFR ontology. Construct two exact families in which the four
observer indexing coordinates remain fixed while the governing law changes a decisive outcome.
This does not assert equality of every realized coefficient/contact datum.

## 1. Differential-law counterexample

Let `K` be a characteristic-zero field and let

\[
 L=K(u_0,u_1,u_2,\ldots)
\]

be the rational function field on an algebraically independent countable packet. Give `K` the
trivial derivation. Every assignment on the transcendence basis extends uniquely to a `K`-linear
derivation of `L`.

Define

\[
 D_+u_j=u_{j+1}\qquad(j\ge0).
\tag{SL.1}
\]

For a fixed `m>=0`, define another derivation by

\[
 D_mu_j=u_{j+1}\quad(0\le j<m),
 \qquad
 D_mu_m=0,
\tag{SL.2}
\]

and, for definiteness, `D_m u_j=0` for `j>m`.

### Theorem 1.1 — same observer indices, opposite jet law

After forgetting derivation, both objects have the same ordinary coefficient field `L`, named
source packet, aperture, and trivial history. Fix the same observed jet depth `N>=m+1`. Their
governing derivations differ. Nevertheless,

\[
 D_+^n u_0=u_n
\]

for every `n`, so the complete `D_+`-jet is algebraically independent, whereas

\[
 D_m^{m+1}u_0=0,
\]

so the `D_m`-jet is algebraically dependent and the `D_m`-orbit of `u_0` is contained in
`span_K{u_0,...,u_m}`.

### Proof

Equation `(SL.1)` gives `D_+^n u_0=u_n` by induction; algebraic independence follows from the
definition of `L`. Equation `(SL.2)` gives `D_m^j u_0=u_j` for `0<=j<=m` and then
`D_m^(m+1)u_0=D_mu_m=0`. Hence the first `m+2` jets are linearly dependent. `[PROVED HERE]`

This is the constant-symbol instance of the stronger formalized graded-principal-symbol law in
`../../3-formalized/graded-principal-symbol-characteristic-arrangement.md`: a nonzero symbol at
every layer gives an algebraically independent jet tower, while one vanished layer traps all
future jets in a finite filtration stage.

The difference is not a change of the ordinary coefficient doctrine after forgetting derivation,
nor of observed jet depth; it is a change of differential law.

## 2. Stokes-law counterexample

Let a Puiseux label set split as `A=U disjoint_union V`. Suppose every cross pair has contact
`ell`. Activate a new coefficient at order `k>ell`, constant within each cluster and unequal
between them. For

\[
 X_U=\sum_{a\in U}x_a,
 \qquad
 X_V=\sum_{b\in V}x_b,
 \qquad
 M=X_U+X_V,
\]

the exact Stage-2 Puiseux cluster-split theorem gives

\[
 \boxed{
 Q_{\mathrm{after}}-Q_{\mathrm{before}}
 =-2(k-\ell)X_UX_V
 ={k-\ell\over2}\bigl((X_U-X_V)^2-M^2\bigr).}
\tag{SL.3}
\]

The label set, coefficient doctrine, chosen aperture, history, physical-rank port `M`, and
determinant character `lambda^M` stay fixed.

### Theorem 2.1 — fixed observer coordinates, changed Lorentz law

The structural intervention `(SL.3)` can change Stokes inertia while all listed observer-fibre
coordinates remain fixed.

### Proof

For two branches with contact `j`, the exact form is

\[
 Q_j={1+j\over2}z^2+{3-j\over2}t^2,
 \qquad z=x_1-x_2,\quad t=x_1+x_2.
\tag{SL.4}
\]

At `j=1`, both coefficients are positive and the negative index is zero. At `j=4`, the `t^2`
coefficient is negative and the negative index is one. The port remains `t=M`, and its determinant
exponent is unchanged. This is a change in the contact/Cartan law, not an observer reparameterization.
`[PROVED HERE]`

The full dependency-closed source calculation is
`../constraint-motive-relativity/puiseux-cluster-split-one-port-lorentz-exchange-law.md`.

## 3. Nonreconstruction theorem

### Theorem 3.1

No invariant depending only on

\[
 (\text{coefficient doctrine},\text{ prolongation index},
   \text{ aperture},\text{ history})
\tag{SL.5}
\]

determines the governing constraint law on all CFR calibrations.

### Proof

The derivation pair in Theorem 1.1 has identical data `(SL.5)` but opposite finite-type behavior.
The Stokes pair in Theorem 2.1 has identical data `(SL.5)` and the same rank/determinant port but
different Lorentz forms and inertia. Either pair is a counterexample to determination by `(SL.5)`.
`[PROVED HERE]`

## 4. Strongest positive survivor

The theorem proves that a governing-law variable must be added to the observer tuple. A provisional
repaired schema is a fibration

\[
 \pi:\mathcal X\longrightarrow\mathcal L
\tag{SL.6}
\]

over a source-law base `L`, whose fibres carry coefficient, prolongation-index, aperture, and
history data. A semidirect-product description requires an explicit action of law morphisms on
these fibres and is not proved here.

Source-law morphisms may alter relation, differential, contact, domain, exactness, or inertia laws.
Only invertible law morphisms preserving every marking can be gauges. Characteristic-symbol zeros,
contact collisions, domain births, and exactness changes are candidate law events on a stratified
base.

This theorem does not prove that all HGT routes arise from one law space. It proves the original
four observer directions are not complete on the class containing these calibrations.

## 5. Lean-return notes

- The differential-law theorem is elementary; the stronger filtered result is already formalized
  in `formal/GaloisForLFunctions/HTGeometry/GradedPrincipalSymbolHorizon.lean`.
- The Stokes cluster-split theorem is paper-proved but not formalized in this card.
- No Lean file has been written or built.

## Gates

- [x] fixed-coefficient differential counterexample
- [x] fixed-port Stokes counterexample
- [x] necessity of a separate law-base coordinate
- [ ] action/semidirect law constructed
- [x] no RH claim
- [ ] common source-law fibration
- [ ] two-organ constitutive section
- [ ] Lean formalization of Stokes clause

## Log

- 2026-08-09 — created after whole-corpus hostile audit showed the original four axes describe observer fibres but omit the governing law field.
