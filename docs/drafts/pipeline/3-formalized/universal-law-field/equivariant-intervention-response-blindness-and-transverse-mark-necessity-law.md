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
- [x] 2 → 3: Lean certified — `HTGeometry.ConstitutiveEquivariantResponseBlindness`
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

## Lean certification status (2026-08-09) — COMPLETE

Module: `GaloisForLFunctions.HTGeometry.ConstitutiveEquivariantResponseBlindness`
(wired into `HTGeometry.UniversalLawField`).

**Theorem 1.**  Stated on a genuine manifold, not on a linear model: `X` and `Q` are charted spaces
over models with corners `I` and `J`, `doctrineResponse I J P V x = dP_x (V x)` is equation (3), and
`mfderiv_comp_eq_of_invariant` is the naturality identity `dP_{Φx} ∘ Φ_* = dP_x` obtained from the
manifold chain rule and `P ∘ Φ = P`.  `doctrineResponse_eq_of_equivariant` is equation (4) for a
single symmetry and `doctrineResponse_smul` is equation (4) for a group acting by smooth maps.
`responseCoframe` is the combined first response of an arbitrary indexed family of interventions;
`responseCoframe_constant_on_orbit` proves it constant on `G`-orbits and `orbitResponseCoframe`
exhibits it as a function on `MulAction.orbitRel.Quotient G X` — the exact sense in which the family
"cannot identify a hidden coordinate along those orbits".

**Corollary 2.**  `separation_forces_escape` is the necessity half in exact contrapositive form: if a
first-order response coframe separates `x` from `g • x`, then the doctrine map is not `G`-invariant,
or some member of the family is not `G`-equivariant, or the action is not smooth, or the doctrine map
is not differentiable.  The card's escape route 4 — a higher or nonlocal response — is the statement
that the separating datum is not of the form `dP_x(V x)` at all, which is precisely what the theorem
quantifies over.

Non-sufficiency is certified concretely on one model: `X = Q = ℂ` with `G = Circle` acting by
rotation and the invariant doctrine map `circleDoctrine z = z · conj z` (`circleDoctrine_smul`,
`mdifferentiable_circleDoctrine`, `mdifferentiable_rot`, `mfderiv_rot`).

- `circleModel_escape_separates`: the conjugation field `conjField z = conj z` is **not**
  equivariant (`conjField_not_equivariant`) and its response does separate two points of one
  rotation orbit — `−2` at `i` against `2` at `1`.  So escape route 1 is real.
- `circleModel_escape_not_sufficient`: the orbit-tangent modulated field
  `tangentModulatedField z = (Re z) · i · z` is **equally** non-equivariant
  (`tangentModulatedField_not_equivariant`) and yet its first response vanishes identically
  (`doctrineResponse_tangentModulatedField`), so it separates nothing whatsoever.  Non-equivariance
  alone is therefore not sufficient — exactly the card's "its source naturality and separation power
  must still be proved".

**§2 exact radial-source instantiation.**  The literal graded source, its radial gauge family
`Γ_c = gradeDiag (radialMultiplier ν c)`, the identity-sector trace, the Kummer derivation and its
cyclic one-cocycle are **reused verbatim** from the already-formalized module
`HTGeometry.ConstraintRelativity.IdentitySectorRadialBlindness`; nothing there is rebuilt.  The new
content is the CEM reading: `kummerReporter` bundles the trace and the cocycle into one reporter
coframe, `kummerReporter_gradeDiag` proves the whole coframe invariant under every character gauge,
and `kummerReporter_radial` / `kummerReporter_not_separating` specialise this to the radial family —
the coframe takes the same value at every member of a radial orbit, so no amount of additional
equivariant cyclic reporting selects the radial origin.  `reporter_eq_of_mem_orbit` and
`orbitReporter` give the general set-level statement that an invariant reporter is a function of the
orbit alone.  `absoluteGrade_zero` removes the normalisation hypothesis `ν 0 = 1` by deriving it
from positivity and multiplicativity.

`#print axioms` on `mfderiv_comp_eq_of_invariant`, `doctrineResponse_eq_of_equivariant`,
`doctrineResponse_smul`, `responseCoframe_constant_on_orbit`, `orbitResponseCoframe`,
`separation_forces_escape`, `circleModel_escape_separates`, `circleModel_escape_not_sufficient`,
`orbitReporter`, `kummerReporter_radial`, and `kummerReporter_not_separating` reports only
`propext`, `Classical.choice`, and `Quot.sound`.
