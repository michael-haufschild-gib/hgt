# Equivariant intervention-response blindness and transverse-mark necessity law

- **ID:** ULF-EIR-1
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** constitutive experimental mathematics and radial-source stress test
- **Statement:** Interventions equivariant under an observer-blind symmetry have invariant first responses and cannot recover the hidden symmetry coordinate.

## Goal

Turn the source radial-gauge obstruction into a route-independent CEM theorem and identify the exact
kind of new datum required.

## Gates

- [x] 0 → 1: invariant doctrine and equivariant intervention formulation
- [x] 1 → 2: one-line naturality proof plus exact source instantiation
- [ ] 2 → 3: no Lean formalization
- [ ] 3 → 4: no novelty/priority claim

## Theorem 1 — equivariant response blindness

Let a group (G) act smoothly on a manifold (X). Let

\[
P:X\longrightarrow Q
\tag{1}
\]

be a (G)-invariant doctrine map: (P(gx)=P(x)). Let (V) be a (G)-equivariant legal
intervention vector field:

\[
V(gx)=g_*V(x).
\tag{2}
\]

Define its first doctrine response

\[
\mathcal R_V(x)=dP_x(V(x))\in T_{P(x)}Q.
\tag{3}
\]

Then (\mathcal R_V) is (G)-invariant:

\[
\mathcal R_V(gx)=\mathcal R_V(x).
\tag{4}
\]

Consequently any family of equivariant interventions has combined first-response map constant on
(G)-orbits. It cannot identify a hidden coordinate along those orbits.

### Proof

Differentiate (P\circ g=P) at (x):

\[
dP_{gx}\circ g_*=dP_x.
\]

Apply this identity to (V(x)) and use (2). ∎

## Corollary 2 — necessity, not sufficiency, of a transverse mark

If a doctrine quotient hides a nontrivial (G)-orbit and its legal interventions are all
(G)-equivariant, no first-order response coframe can recover that orbit. A necessary escape is at
least one of:

1. a legal intervention not equivariant under (G);
2. a source mark whose stabilizer is a proper subgroup of (G);
3. a doctrine map that is not (G)-invariant;
4. a higher/nonlocal response not determined by the equivariant first jets.

None is sufficient by itself; its source naturality and separation power must still be proved.

## 2. Exact radial-source instantiation

The paper theorem
`identity-sector-radial-gauge-blindness-and-cross-grade-selection-law.md` constructs radial
automorphisms (\Gamma_c) of the literal graded source and proves:

- the total-grade-one cyclic sector is fixed by every (\Gamma_c);
- endpoint traces are invariant;
- the Kummer derivation commutes with (\Gamma_c);
- the logarithmic cyclic cocycle satisfies
  \[
  \phi_{\log}(\Gamma_ca_0,\Gamma_ca_1)=\phi_{\log}(a_0,a_1).
  \tag{5}
  \]

Separately,
`valuation-coframe-operation-defect-rank-and-determinant-line-law.md` proves that the valuation
coframe separates finite prime classes and obstructs exactification when preserved.

These facts have a precise CEM interpretation:

- the valuation/Kummer family is a strong passive/source reporter coframe;
- it is nevertheless equivariant under the hidden radial symmetry;
- therefore it cannot be the transverse intervention-response coframe of
  `positive-doctrine-additive-intervention-nondescendence-and-response-coframe-law.md`.

This is unconditional source leverage: adding more equivariant cyclic reporters, higher degrees, or
coframe-preserving exactifications cannot select the radial origin. A live source-normal mechanism
must break equivariance through a legal mark/intervention or leave the current doctrine.

## 3. What this does not prove

It does not construct that transverse operation, prove the physical dagger class null, or imply RH.
It also does not say non-equivariance alone selects a unique source point. The theorem closes one
entire class of explanations while specifying the next field-level object to search for.

## 4. Significance

This is the first CEM law with a literal corpus instantiation. Its mathematical mechanism is elementary
naturality, but its use is structural: it separates **reporter richness** from **interventional
identifiability**. A complete coframe can still be blind to the constitutive coordinate one needs.

## Log

- 2026-08-09 — general theorem and literal radial-source instantiation recorded; no Lean.
