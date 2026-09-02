# Bilateral Wiener–Hopf envelope properness

- **ID:** ULF-BWHEP-1
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `WienerFormationScale` + `ConstitutiveMonoidBialgebraHopfEnvelope` +
  `DirectedLiteralSourceFormationRecoveryProperness`
- **Lean module:** `GaloisForLFunctions.HTGeometry.BilateralWienerHopfEnvelopeProperness`
- **Statement:** The coefficient-native `ell^1` norm on the Laurent Hopf envelope admits a bounded
  evaluation character exactly on the unit circle; actual marked source formation and rank recovery
  are one algebraic identity in this envelope.

## Big-picture law and RH closure

One-sided formation lives in the monoid algebra of nonnegative ranks; exact recovery adjoins inverse
ranks and therefore forces its Hopf envelope, the Laurent algebra on `Z`.  Algebraic Hopf completion
exists for every nonzero complex character, so it cannot select.  The missing universal datum is the
**source-bornological Hopf envelope**: complete finite Laurent packets in coefficient `ell^1`, using
one norm for formation and recovery.

Its spectrum is not a disc or an annulus chosen after seeing a zero.  Both generators `T` and
`T^-1` have source norm one, so every bounded character must send them to reciprocal complex numbers
of norm at most one.  Their product is one; hence both norms are one.  Criticality is therefore the
proper character spectrum of reversible source completion.

Exact RH closure: for any nontrivial zero `rho` and prime `p`, let
`z=p^(1/2-rho)`.  If the literal functional-equation packet evaluation extends as a bounded
character of this single coefficient-native Laurent completion, then `|z|=1` and
`Re rho=1/2`.  A uniform pre-divisor extension theorem for all Xi occurrences implies RH.  This
paper builds and classifies the required completion core; it does not assume that extension.

## Corpus audit

- `WienerFormationScale` constructs the one-sided coefficient norm
  `sum_n |a_n| R^n` and classifies bounded characters by the closed disc `|z|<=R`.
- `ConstitutiveMonoidBialgebraHopfEnvelope` proves that adjoining inverse formation makes
  `C[N]` into the Laurent Hopf envelope `C[Z]`, but carries no source norm.
- `LiteralSourceReflectionRankGaugeLinearization` proves natural-rank recovery uses `z^-m`.
- `DirectedLiteralSourceFormationRecoveryProperness` proves actual formation and recovery occupy
  opposite moderation chambers and intersect at `|z|=1`.
- Bilateral moderation and compact-circle modules classify sequence growth after evaluation, but no
  corpus theorem equips the Laurent Hopf envelope itself with coefficient `ell^1`, classifies its
  bounded evaluation characters, or embeds the actual marked source/recovery identity into it.

## Definitions

Let `A=C[Z]` be the finite Laurent packet algebra with basis `T^e`, `e in Z`.  Define

`||sum_e a_e T^e||_W = sum_e |a_e|`.

For `z!=0`, define the algebraic evaluation character

`ev_z(sum_e a_e T^e)=sum_e a_e z^e`.

Call `ev_z` Wiener-bounded when some finite `C` satisfies

`|ev_z(f)| <= C ||f||_W`

for every finite Laurent packet `f`.

Define source edge and recovery packets

`E_m=T^m-T^(m+1)`,

`R_m=T^(-m)`.

## Theorem

For every `z!=0`:

1. `ev_z` is an algebra character; in particular `ev_z(fg)=ev_z(f)ev_z(g)`.
2. `ev_z(T^e)=z^e` for every integer `e`.
3. `ev_z` is Wiener-bounded if and only if `|z|=1`.  On the unit circle it is contractive:
   `|ev_z(f)|<=||f||_W`.
4. In the Laurent source algebra,
   `R_m E_m=1-T`; hence after evaluation
   `z^(-m)(z^m-z^(m+1))=1-z`.
5. `ev_z(E_m)=complexCharacterEdge z m`, and at `m=12+j` this is the actual normalized
   depth-12 marked source execution.
6. For prime half-density character `z=p^(1/2-s)`, Wiener-boundedness is equivalent to
   `Re s=1/2`.

## Proof

Laurent evaluation is the algebra map induced by the group homomorphism `e -> z^e`, proving items
1 and 2.  If `|z|=1`, triangle inequality gives

`|sum_e a_e z^e| <= sum_e |a_e||z|^e = sum_e |a_e|`,

so evaluation is contractive.

Conversely suppose evaluation is bounded by `C`.  Testing the basis packets `T^n` gives

`|z|^n<=C`

for every `n>=0`; exponential growth forces `|z|<=1`.  Testing `T^(-n)` gives

`|z^-1|^n<=C`,

so `|z^-1|<=1`, hence `1<=|z|`.  Therefore `|z|=1`.  This proves item 3 without a spectral theorem
or completion assumption.

The group law for Laurent monomials gives

`T^(-m)(T^m-T^(m+1))=T^0-T^1=1-T`,

proving item 4.  Evaluation yields the coherent edge `z^m-z^(m+1)`, already identified with actual
marked source execution, proving item 5.  The half-density norm formula then proves item 6.
`[PROVED HERE]`

## Hostile assessment

- **New object:** coefficient-bornological Hopf envelope of source rank formation.  It combines the
  previously separate one-sided Wiener receiver and algebraic Laurent Hopf envelope.
- **New route-independent theorem:** bounded character spectrum is forced to the phase quotient;
  no positivity, divisor measure, recurrence estimate, or raw reflection curvature enters.
- **Not RH:** Xi zero evaluation has not yet been proved bounded on this completion.  Declaring it
  continuous would insert RH.
- **Prediction:** every source organ that genuinely supports both formation generator and exact
  inverse recovery in one coefficient-contracting algebra must see only unitary horizontal
  characters.  Off-line models must break common boundedness, source-faithful inversion, or the
  single-norm requirement.
- **Required producer:** construct the literal FE packet-to-Laurent map before zero specialization
  and prove its evaluation/recovery action is bounded in coefficient `ell^1`.

## Lean certification

- Algebra-character packaging and coefficient formula:
  `bilateralWienerEval`, `bilateralWienerEval_eq_sum`.
- Laurent monomial evaluation and unit coefficient norm:
  `bilateralWienerEval_T`, `bilateralWienerPacketNorm_T`.
- Contractivity and exact bounded-character spectrum:
  `norm_bilateralWienerEval_le`, `bilateralWienerEvalBounded_iff`.
- Exact source-formation/recovery identity and both evaluated factors:
  `bilateralWienerRankRecovery_mul_sourceEdge`, `bilateralWienerEval_sourceEdge`,
  `bilateralWienerEval_rankRecovery`.
- Actual normalized depth-12 marked execution:
  `bilateralWienerEval_sourceEdge_rankTwelve`.
- Prime half-density critical-line equivalence:
  `bilateralWienerHalfDensityEvalBounded_iff`.
- Imports wired into `HTGeometry/UniversalLawField.lean` and `HTGeometry.lean`; umbrella builds not
  run.

## Gates

- [x] 0 -> 1: big-picture law, corpus audit, and exact RH closure stated
- [x] 1 -> 2: dependency-closed proof; `[PROVED HERE]`
- [x] 2 -> 3: exact Lean declarations above; direct file check and targeted module build pass
- [ ] 3 -> 4: publication-ready extraction

## Log

- 2026-09-01 — coefficient-bornological Hopf envelope and bounded-character theorem isolated;
  paper proof closed.
- 2026-09-01 — Lean module scratch-checked, directly checked, exact-target built, and axiom-audited;
  only standard `propext`, `Classical.choice`, and `Quot.sound` dependencies remain.
- 2026-09-02 — exact six-clause coverage audited against the paper statement; direct file check and
  targeted module build pass; dedicated and theorem-area umbrella imports present; promoted to
  Stage 3. Global lint reports only unrelated pre-existing umbrella-reachability failures and no
  issue in this module.
