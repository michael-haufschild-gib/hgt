# Arithmetic three-slot singular formation descent

- **ID:** ULF-SPCM-D1
- **Stage:** 1-in-progress
- **Status:** conjectural source law; receiver and RH closure formally proved
- **Open core:** construct and prove one source-native deletion/formation naturality square

## 1. Big-picture interpretation of the higher law

Current corpus is not asking for another operator. It exhibits a mechanism with four layers:

\[
\text{source formation history}
\longrightarrow \text{stable additive class}
\longrightarrow \text{central holonomy/work}
\longrightarrow \text{positive singular support}.
\]

Local proof routes are readers of final layers. Missing law belongs at first arrow.

Proposed higher principle is **singular formation naturality**: for actual arithmetic source, forming
three source slots and deleting one slot must agree with deleting first and then forming, after
quotienting constant histories and absolutely summable principal corrections. This is a
Beck--Chevalley/face-map law for formation histories, not a statement about a chosen Xi zero.

Why singular quotient is essential:

- ordinary `L²` completion erases principal history and makes normalized boundary graph nonclosed;
- raw algebraic history retains too much and has no proper topology;
- quotient by constants supplies exact algebraic reporter;
- quotient by `ℓ¹` corrections retains unique reciprocal-prime principal class.

Functional-equation action supplies two reflected laws. Two-slot symmetry cannot distinguish their
alternation. Three-slot deletion does: its defect is tensor square of law difference. Thus source
naturality at three slots is first arity capable of selection.

## 2. Lean-corpus evidence related to this law

Fresh `scripts/formal_tools.py research` audit gives:

1. `witt_formation_conservation`: exact source-side inverse law `E(-t)H(t)=1`; valid for arbitrary
   modes, so alone cannot select.
2. `canonicalCohomologicalExactReporter`: quotient of coinduced histories by constants is exact,
   equivariant, and surjective; Hilbert/topological admission remains open.
3. `summable_gammaSixFilteredBoundaryPrincipalCorrection_iff`: reciprocal-prime coefficient is
   unique modulo `ℓ¹` correction.
4. `thetaInternalJetHellingerGammaNormalizedBoundaryGraph_not_isClosed` and its vertical-vector
   theorem: same-`L²` continuous descent is impossible off-neutral.
5. `involutiveFormationLift_informationNeutral`: functional-equation action lifts through common
   recovery without information loss; information neutrality does not kill defect.
6. `iSup_formationCapital_fe_split`: functional-equation transport plus split recovery preserves
   capital and cannot manufacture boundedness.
7. `symAlternatingCylinder_gap`, `phaseAveragedThinningConsistent_iff_laws_eq`, and
   `exchangeableFormationSelection_capstone`: three-slot deletion defect is exactly half the
   squared reporter difference and vanishes exactly when reflected laws agree.
8. `xiFormationThreeSlotExchangeDefect_eq`: for actual Xi reflected reporter laws, defect is
   exactly `2a(q)^2`.
9. `xiFormationStratification_zeroLaw`: bounded formation work, zero stable class, zero central
   anomaly, and zero singular escape are one stratum.
10. `xiFormationEscapePrincipalClass_fourOrganLaw`: Gamma-six, Möbius double-log, resolved Green,
    and Kakutani/Hellinger organs reconstruct same escape class.
11. `xiFunctionalEquationFormationAtom_ne_self`: bare functional-equation atom invariance is
    impossible even on critical line; conjecture must concern reflected reporter laws/history, not
    fixed atoms.
12. `sourceHorizonEscapeConservation_law`: compact observers can lose arbitrarily large source
    charge; compactness or bounded jets alone cannot prove proposed square.

No searched declaration constructs three-slot face naturality for literal arithmetic source in
constant-plus-`ℓ¹` singular quotient.

## 3. Exact RH closure

Let `A(q)` and `A*(q)` be recovered forward/reflected one-coordinate laws. Corpus proves
`A*(q)=-A(q)` and `A(q)=a(q)`.

Required source square must descend under coefficient-faithful recovery to

\[
P_{\rm skipped}(A(q),A^*(q))
=P_{\rm adjacent}(A(q),A^*(q)).                       \tag{D1.1}
\]

Existing three-slot theorem turns `(D1.1)` into

\[
0=\frac{(A(q)-A^*(q))^2}{2}=2a(q)^2,
\]

so `a(q)=0`. Existing centered-rate theorem gives `Re(q)=1/2`. Applying to every
multiplicity-labelled Xi copy proves RH. No further analytic or selection premise remains.

Equivalently, `(D1.1)` makes each formation block have zero work; ULF-SPCM-02 then yields zero
stable class, zero central holonomy, zero principal escape, and simultaneous vanishing in all four
reconstruction organs.

## Conjecture D1 -- singular arithmetic face naturality

There exists a source-defined three-slot formation object `F₃(S)` for literal completed
Möbius--theta/Gamma--Witt source `S`, a two-slot object `F₂(S)`, and two source face operations

\[
d_{\rm skipped},d_{\rm adjacent}:F_3(S)\to F_2(S)
\]

with following laws:

1. **Pre-divisor construction.** `S`, `F₂`, `F₃`, and both faces use only arithmetic source data,
   Witt/exterior-complete formation, functional-equation action, and internal source jets; no zero
   location, centered rate, or RH-equivalent predicate occurs in definitions.
2. **Singular landing.** Both faces land in coinduced histories modulo constant histories and the
   unique `ℓ¹` prime--Gamma correction. Reciprocal-prime principal coefficient is retained.
3. **Face naturality.** `d_skipped(F₃(S)) = d_adjacent(F₃(S))` in that quotient.
4. **Common recovery.** For every Xi-zero copy `q`, internal-jet/Gamma recovery sends two faces to
   phase-averaged skipped and adjacent laws of `xiFormationForwardReporterLaw q` and
   `xiFormationReflectedReporterLaw q`.
5. **Coefficient faithfulness.** Equality after source recovery reflects equality of retained
   principal coefficients; recovery cannot factor through ordinary `L²`, scalar codiagonal, or
   reflection-odd quotient.

## Construction target

Build in this order:

1. typed finite three-slot source packet from existing Witt exterior/complete/ghost generators;
2. two face maps as actual slot deletion versus adjacent formation;
3. quotient by `coinducedFormationConstantSubgroup` plus explicit `ℓ¹` principal correction;
4. exact finite face identity before completion;
5. singular landing/admission theorem;
6. common recovery square into existing Möbius-internal-jet and Gamma principal readers;
7. invoke `xiFormationThreeSlotExchangeDefect_eq` and global RH equivalence.

## Kill gates

Retire or reformulate D1 immediately if any occurs:

- finite arithmetic degree-three face difference is nonzero before completion;
- equality holds only after erasing reciprocal-prime principal coefficient;
- construction uses a divisor location or centered rate;
- recovery is bounded on ordinary `L²` despite known vertical graph obstruction;
- square reduces definitionally to `a(q)=0`, trace-class admission, fixed-source untwisting, or RH;
- functional equation alone is claimed to imply face naturality;
- only two-slot symmetry is obtained;
- an `ℓ¹` counterterm must cancel a nonzero harmonic principal coefficient.

## Status gates

- [x] higher mechanism isolated
- [x] full corpus search at relevant interfaces
- [x] recovered defect computed exactly as `2a²`
- [x] four-organ consequence formalized
- [x] RH closure formalized
- [ ] finite source packet and faces
- [ ] singular quotient landing
- [ ] source face identity
- [ ] coefficient-faithful recovery square
- [ ] unconditional RH theorem
