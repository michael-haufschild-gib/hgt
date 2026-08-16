# Paracyclic anomaly on the P/CCM two-sheet ghost carrier

- **ID:** `frankenstein-paracyclic-ghost-two-sheet-anomaly`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / `[BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Statement:** Dressing the coefficient-faithful Route-P/CCM two-sheet orientation cell by the
  literal Möbius--theta paracyclic anomaly cancels mass trace but retains the complete anomaly in
  orientation, CCM-third-jet, and Sonin-physical readouts; the dressed cell vanishes exactly on
  the critical line.

## Physics correction and exact translation

The sine-Gordon interaction does not itself require Faddeev--Popov ghosts.  Faddeev--Popov ghosts
arise after gauge-fixing an actual gauge redundancy.  In BRST language the antighost--multiplier
doublet is cohomologically trivial: it changes presentation, not physical cohomology.

The corpus already has the exact analogue.  `ResiduePromotionAnomaly.lean` proves that a fitted
residue compensator splits as the old complex plus a contractible two-term complex and carries
zero residue in split coordinates.  Hence a genuine contractible ghost pair cannot annihilate the
physical horizontal residue.  The correct use of the idea is instead to keep the odd channel as a
mass-neutral, orientation-faithful carrier and ask whether a separately derived source law kills
its retained anomaly.

## Source data

Fix:

- `n >= 2`, the physical half-density mate scale;
- `rho : XiDivisorSupport`, retaining its support multiplicity through
  `xiSupportMultiplicity rho` and its first nonzero Xi jet;
- `pe : Nat.Primes × Nat`, retaining Route-P prime/depth provenance.

Let

\[
 a_{n,\rho,p}
 =\operatorname{Res}_{\rm cyc}
   \bigl(\operatorname{Def}_{\rm para}
      (L_{n,\rho},J_\rho)(x_p)\bigr),
 \qquad p=\operatorname{fst}(pe),
\]

where `x_p` is the literal ordinary-prime trace-one cyclic source atom.  The established
paracyclic transgression formula gives

\[
 a_{n,\rho,p}
 =\bigl(g_n(\rho)-1\bigr)c_\rho,
 \tag{1}
\]

with `g_n(rho)=n^(2 Re rho-1)` and nonzero leading jet coefficient `c_rho`.

Let `P_pe>0` be `routePPrimitiveBurnolApertureDefectFlux pe`, and let `v_or` be the canonical
two-sheet orientation vector, whose mass trace is zero and orientation trace is one.  Define

\[
 \mathcal G_{n,\rho,pe}
   :=a_{n,\rho,p}\,P_{pe}\,v_{\rm or}.
 \tag{2}
\]

Equivalently, this is the physical anomaly multiplying the existing
`frankensteinRoutePTailFluxTwoSheetCell pe`.

## Theorem and complete proof

### 1. Exact coefficient

Equation `(1)` is
`ccmMobiusThetaTwoLegParacyclicDefect_residue` specialized to
`ccmRationalAdelicOrdinaryPrimeCycleAtom pe.1`; its source trace is exactly one.  No prime,
divisor, or target coefficient is divided out.

### 2. Ghost mass cancellation

Linearity and the established identity

\[
 \operatorname{Tr}_{\rm mass}(P_{pe}v_{\rm or})=0
\]

give

\[
 \operatorname{Tr}_{\rm mass}(\mathcal G_{n,\rho,pe})=0.
 \tag{3}
\]

This is the only literal ghost cancellation: the even/odd sheets cancel total mass.

### 3. Coefficient-faithful orientation and cofinal-homology readouts

Because `Tr_or(v_or)=1`,

\[
 \operatorname{Tr}_{\rm or}(\mathcal G_{n,\rho,pe})
 =a_{n,\rho,p}P_{pe}.
 \tag{4}
\]

The cofinal Tate-relative source-homology coordinate of the same trace-one atom is exactly
`a_{n,rho,p}` by
`ccmMobiusThetaCofinalSourceHomologyLanding_readout_eq_physicalDefect`.  Thus `(4)` is also

\[
 P_{pe}\,\operatorname{coord}_{H^1_{\rm cof}}
   (\operatorname{landing}_{n,\rho}(x_p)).
 \tag{5}
\]

This identifies the paracyclic Bockstein and P/CCM two-sheet orientation before bounded
scalarization.

### 4. CCM and physical transport

The existing two-sheet readouts are linear.  Therefore the CCM third-jet matrix is

\[
 a_{n,\rho,p}P_{pe}\,J^{(3)}_{\rm CCM},
 \tag{6}
\]

and, at horizontal grade `g`, the Sonin physical transport is

\[
 T_g(\mathcal G_{n,\rho,pe})
 =a_{n,\rho,p}P_{pe}\,R_g.
 \tag{7}
\]

Hence mass cancellation does not cancel either physical orientation receiver.

### 5. Exact vanishing classification

Since `P_pe>0`, it is nonzero.  Since `Tr_or(v_or)=1`, the map
`z |-> z v_or` is injective.  Therefore

\[
 \mathcal G_{n,\rho,pe}=0
 \Longleftrightarrow a_{n,\rho,p}=0.
\]

By `literal_defect_anomaly_eq_zero_iff`, using `n>=2`, `c_rho != 0`, and the trace-one source
atom,

\[
 a_{n,\rho,p}=0
 \Longleftrightarrow \Re\rho=\tfrac12.
 \tag{8}
\]

Thus the dressed cell vanishes exactly on the critical line.  Quantifying `(8)` over all Xi
support points is equivalent to RH, but no such global vanishing is asserted here.

### 6. Uniqueness of a same-line cancelling ghost

For any scalar `b`,

\[
 \mathcal G_{n,\rho,pe}+bP_{pe}v_{\rm or}=0
 \Longleftrightarrow b=-a_{n,\rho,p}.
 \tag{9}
\]

Apply `Tr_or` and cancel the nonzero `P_pe` for the forward implication; substitute for the
reverse implication.  Hence a ghost confined to this coefficient-faithful orientation line can
cancel the anomaly only by being fitted with the exact negative target anomaly.  This is the
finite-dimensional form of the corpus's general fitted-compensator splitting theorem, not a
source producer.

## Hostile audit

1. **Not a source annihilation theorem.**  The coefficient uses the Xi-support stalk and its first
   nonzero jet.  It transports the exact anomaly; it does not derive its vanishing.
2. **No fake prime faithfulness.**  The trace-one paracyclic residue alone is independent of the
   chosen ordinary prime.  Prime/depth provenance is retained through the exact positive Route-P
   coefficient `P_pe`, not inferred from the trace-one atom.
3. **Contractible ghosts cannot help.**  A fitted opposite cell is uniquely the negative of the
   anomaly and splits off as a contractible presentation change.  Treating `(9)` as a law would
   insert the desired conclusion into the compensator.
4. **No holomorphic universal ghost.**  The corpus already proves that the real-part-dependent
   defect coefficient has no holomorphic compensator on a connected open source region where the
   leading jet is nonzero.
5. **Scientific status.**  BRST-doublet triviality and residue-anomaly compensation are known
   parent mechanisms.  The exact P/CCM/Möbius-theta/Gamma-six identification is a project-specific
   bridge; priority and broader significance are not claimed.

## External boundary

- Faddeev--Popov ghosts represent the determinant produced by gauge fixing an actual gauge orbit;
  they are not forced by a Taylor expansion of a scalar interaction.
- In standard BRST treatments the antighost and multiplier form a cohomologically trivial
  doublet.  This matches, rather than evades, the corpus theorem that a fitted compensator splits
  as a contractible two-term summand.

## Lean formalization

`GaloisForLFunctions.RHTower.FrankensteinParacyclicGhostTwoSheetAnomaly` formalizes `(1)`--`(9)`,
including exact cofinal-homology, CCM-third-jet, and Sonin-physical readouts.  The exact leaf build,
direct source check, and targeted forbidden-declaration scan pass.  Headline declarations depend
only on `propext`, `Classical.choice`, and `Quot.sound`.  Repository-wide lint reaches this module
but remains red on unrelated unreachable modules `GaussLowModeKernelBound` and
`XiMassGradedLogRetreat` already present in the shared worktree.

## Gates

- [x] 0 → 1: exact carrier and hostile falsifiers fixed
- [x] 1 → 2: dependency-closed proof `(1)`--`(9)` complete
- [x] 2 → 3: exact Lean theorem, leaf build, axiom audit, lint, umbrella wiring
- [ ] 3 → 4: publication integration

## Log

- 2026-08-16 — Literal sine-Gordon/FP analogy rejected.  Surviving exact claim reframed as a
  mass-neutral but anomaly-faithful two-sheet lift; complete proof and hostile audit closed.
- 2026-08-16 — Formalized exact coefficient, zero mass trace, cofinal-H¹/CCM/Sonin readouts,
  critical-line vanishing classification, same-line compensation rigidity, and global RH
  equivalence.  Direct `lake env lean`, exact leaf build, targeted lint scan, axiom audit, and
  umbrella wiring pass; global lint is blocked only by two unrelated umbrella reachability errors.
