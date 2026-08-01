# Full Cauchy restriction descends and detects cohomology

- **ID:** `deninger-cauchy-cohomology-descent`
- **Stage:** 3-formalized
- **Type:** THEOREM · LEAN 4 THEOREM
- **Labels:** `DAC_CAUCHY_COHOMOLOGY_DESCENT`,
  `DAC_LOCAL_CAUCHY_ENERGY_GLOBAL_DETECTION`
- **Parent:** `deninger-global-green-energy-radical`
- **Statement:** boundary-preserving Cauchy maps descend to quotient
  cohomology; if simultaneous local boundary membership classifies
  global boundaries, their local energies jointly detect global
  cohomology.

## Theorem

Let \(B\subset V\) and \(L\subset W\) be submodules and let
\[
 r_\alpha:V\longrightarrow W
\]
be linear maps satisfying \(r_\alpha(B)\subset L\).  They induce
\[
 \bar r_\alpha:V/B\longrightarrow W/L.
\]
Assume the conservative boundary law
\[
 \bigl(\forall\alpha,\ r_\alpha(x)\in L\bigr)
 \Longrightarrow x\in B.                                    \tag{1}
\]
Then
\[
 \bigl(\forall\alpha,\ \bar r_\alpha([x])=0\bigr)
 \Longleftrightarrow [x]=0.                                  \tag{2}
\]

If local energies
\(\mathcal E_\alpha:W/L\to\mathbb R\) satisfy
\[
 \mathcal E_\alpha(q)=0\Longleftrightarrow q=0,
\]
then
\[
 \bigl(\forall\alpha,\mathcal E_\alpha(\bar r_\alpha(q))=0\bigr)
 \Longleftrightarrow q=0.                                    \tag{3}
\]

## Proof

The map \(r_\alpha\) descends by \(r_\alpha(B)\subset L\).
For a representative \(x\), the left side of `(2)` says precisely
that every \(r_\alpha(x)\) belongs to \(L\).  Condition `(1)` gives
\(x\in B\), hence \([x]=0\).  The reverse implication is linearity.
Substituting the local energy zero laws yields `(3)`.

## Arithmetic consequence

The local-to-global radical problem is reduced to one source
conservativity conjecture:
\[
 [\text{CONJECTURE}]
 [\text{DAC\_FULL\_CAUCHY\_BOUNDARY\_CLASSIFICATION}]
 \quad
 \bigl(\forall\alpha,\ r_\alpha(x)
       \text{ is a local boundary}\bigr)
 \Longrightarrow
 x\in\overline{Q\mathcal E^0_{\mathrm{arith}}}.
\]
Chain compatibility supplies \(r_\alpha(B)\subset L_\alpha\).
Local Dirichlet positivity and full Cauchy uniqueness supply local
energy-zero laws.  Remaining arithmetic content is conservativity
modulo the strict Arakelov endpoint.

For a full three-term source complex, chain compatibility is packaged
as maps in degrees \(0,1,2\) commuting with both differentials.  Such
a map automatically preserves cocycles and boundaries and therefore
induces maps on all three cohomology groups.  Thus source-specific
Cauchy work need only construct these component maps and prove the two
commuting squares; quotient well-definedness is no longer a separate
obligation.

For the actual two-column Rost--Schmid/signature totalization, five
component restrictions in bidegrees \(00,10,01,11\) and the real
signature summand produce a three-term chain map provided they commute
with six source arrows:

1. degree-zero horizontal residue;
2. degree-zero vertical coefficient differential;
3. degree-one horizontal residue;
4. degree-one vertical coefficient differential;
5. the \(10\)-signature boundary;
6. the \(01\)-signature boundary.

The signed total differential and real reciprocity component then
commute automatically.

## Lean

Formalized in
`formal/GaloisForLFunctions/RHTower/DeningerArithmeticCauchyCohomologyDescent.lean`:

- `deningerCauchyQuotientRestriction`;
- `deningerCauchyQuotientRestriction_mk`;
- `deningerCauchyQuotientRestrictions_eq_zero_iff`;
- `deningerLocalCauchyEnergy_zero_iff_globalClass_zero`;
- `DeningerArithmeticThreeTermChainMap`;
- `DeningerArithmeticThreeTermChainMap.mapH0`;
- `DeningerArithmeticThreeTermChainMap.mapH1`;
- `DeningerArithmeticThreeTermChainMap.mapH2`;
- `deningerTwoColumnComponentMap`;
- `deningerTwoColumnSignatureCauchyChainMap`.

The two theorems are the card verbatim, in the card's own generality — submodules `B ⊂ V` and
`L ⊂ W`, a family `r_α` with `r_α(B) ⊆ L`, and the conservative boundary law `(1)` as an explicit
hypothesis:

- `deningerCauchyQuotientRestrictions_eq_zero_iff` is `(2)`;
- `deningerLocalCauchyEnergy_zero_iff_globalClass_zero` is `(3)`.

### Verification

- Direct command:
  `lake env lean GaloisForLFunctions/RHTower/DeningerArithmeticCauchyCohomologyDescent.lean`
- Cached module build: `lake build GaloisForLFunctions.RHTower.DeningerArithmeticCauchyCohomologyDescent`
  completes successfully.
- Scratch `#print axioms` on all ten declarations: only the Lean/mathlib standard `propext`,
  `Classical.choice`, and `Quot.sound`; three of them do not even use choice.
- No `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` declaration.
- Imported by the `GaloisForLFunctions.RHTower` umbrella.

Both parts of the stage-3 gate the card named — cached module and declaration-axiom audit — are
now discharged.

## Gates

- [x] 0 → 1 in-progress: exact descent statement
- [x] 1 → 2 fully-proven: complete paper proof
- [x] 2 → 3 formalized: `GaloisForLFunctions.RHTower.DeningerArithmeticCauchyCohomologyDescent`,
  cached build green, axiom audit clean
- [ ] 3 → 4 publication-ready: the arithmetic content is the conservativity conjecture
  `DAC_FULL_CAUCHY_BOUNDARY_CLASSIFICATION`, which supplies hypothesis `(1)` and is not proved
  here

## Falsifiers

- Boundary preservation alone does not imply joint detection.
- Raw Cauchy data must be taken modulo local boundaries.
- Endpoint/product-formula channel cannot be omitted from `(1)`.
- No zero divisor, RH premise, CCM object, or numerical calculation is
  used.

## Log

- 2026-08-01 — Discharged the stage-3 gate the card itself named: ran the cached module build and
  the declaration-axiom audit, both clean, and moved the card.  Note what the Lean theorems do and
  do not say: `(1)` is a hypothesis on the given data, and supplying it for the arithmetic
  situation is exactly the open conjecture `DAC_FULL_CAUCHY_BOUNDARY_CLASSIFICATION`.
