# Source-horizontal shell Green / prime-clock profile base-change law

- **ID:** `source-horizontal-shell-green-prime-clock-profile`
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper) / THEOREM (Lean) / OPEN PRODUCER
- **Source:** `rh-current-frontier-map.md`; Route L Gamma-six shell Green class;
  `SourceHorizontalWoldPrimeClockProfile.lean`; source-dagger cyclic boundary-defect law
- **Statement:** The Gamma-six singular Green carrier and the source-horizontal Wold carrier have
  the same complete logarithmic tangent profile.  Equality of its two reflected strict-edge
  responses on each multiplicity-labelled Xi carrier is exactly RH.

## Goal

Construct a genuine Frankenstein junction rather than another receiver: identify the singular
Gamma-six shell trace from Route L with the nonlinear source-horizontal prime-clock response from
Routes R/T, retaining shell multiplicity, prime/source provenance, Xi multiplicity copies, and both
reflected orientations.  Then attack the one remaining base-change theorem which would force the
two oriented responses to agree before bounded scalarization.

## Gates

- [x] 0 -> 1 in-progress: exact source objects, coefficient formula, falsifiers, and RH receiver
  identified.
- [x] Paper theorem: exact shell trace mass, every moment, full odd profile, finite resummation,
  and pointwise/global receiver proved.
- [x] Lean theorem: unconditional scalar trace/profile junction formalized without `sorry`,
  `axiom`, `opaque`, or an RH premise.
- [ ] Prove source-character/singular-trace base change, or falsify it and extract its strongest
  positive replacement.
- [ ] Final targeted Lean build, axiom audit, formal lint, and umbrella import audit.

## Exact setup

The Gamma-six Green principal class has shell multiplicity and eigenvalue

\[
 d_m=5\cdot 6^m,\qquad \lambda_m=6^{-m}.
\]

Hence one complete shell has exact ordinary trace mass

\[
 d_m\lambda_m=5. \tag{1}
\]

For cutoff \(N\), reverse logarithmic shell coordinate

\[
 x_{N,j}=1-\frac jN,\qquad 0\le j<N,
\]

and normalized shell moment

\[
 M_{N,r}=\frac1N\sum_{j<N}\frac{d_{N-j}\lambda_{N-j}}5x_{N,j}^r
 =\frac1N\sum_{j<N}x_{N,j}^r. \tag{2}
\]

The antitone Riemann-sum theorem and the exact power integral give

\[
 \lim_{N\to\infty}M_{N,r}=\int_0^1(1-x)^r\,dx=\frac1{r+1}. \tag{3}
\]

These are exactly the already-proved Wold normalized prime-clock moments.  Define the finite shell
profile

\[
 F_N^{\rm sh}(u)=\sum_{k\ge0}\frac{u^{2k+1}}{(2k+1)!}
   \bigl(M_{N,2k}-1\bigr). \tag{4}
\]

Uniform domination \(0\le M_{N,r}\le1\) permits horizon/Taylor exchange, so

\[
 F_N^{\rm sh}(u)\longrightarrow
 F(u):=\sum_{k\ge0}\frac{u^{2k+1}}{(2k+1)!}
   \left(\frac1{2k+1}-1\right), \tag{5}
\]

the existing Wold universal profile.  At every positive finite cutoff, no coefficient is hidden:

\[
 F_N^{\rm sh}(u)=\frac1N\sum_{j<N}
   \frac{\sinh(ux_{N,j})}{x_{N,j}}-\sinh u. \tag{6}
\]

The existing Wold theorems prove

\[
 F(-u)=-F(u),\qquad F(u)=0\Longleftrightarrow u=0. \tag{7}
\]

Thus this is not similarity of cubic jets.  Equations (1)--(6) identify the entire odd response,
coefficient by coefficient, from the literal shell multiplicity and Green eigenvalue.

## Heavy conjecture -> prove/fail -> pivot loop

### C0 -- fixed-degree low/high closure

**Conjecture.** Combine Route G hereditary tail completeness with a fixed low-height Wold test to
exclude every off-line class.

**Verdict: FALSIFIED.** Fixed-degree tests remain height-limited.  Moving an off-line pair high
enough defeats every fixed polynomial degree; increasing degree restores detection but also the
coefficient price.  A low/high cutoff alone supplies no uniform contradiction.

**Positive survivor.** Any closure must use either a complete nonlinear response or a strict
source ideal, not a fixed finite moment packet.

### C1 -- reflection automatically gives strict-edge equality

**Conjecture.** The source involution itself identifies the two evaluated Gamma-six orientations
in the critical quotient.

**Verdict: FALSIFIED.** Reflection exchanges the two classes.  It gives \(F(u)\mapsto F(-u)=-F(u)\),
not \(F(u)=F(-u)\).  For fixed nonzero horizontal character one of the two Gamma-six evaluated
symbols leaves the required projective critical-edge ideal.  Ambient Hilbert-space transport does
not repair strict landing.

**Positive survivor.** Equality of the two responses is the precise additional relation needed;
by (7), it forces \(u=0\).

### C2 -- trace-class cancellation of the odd shell symbol

**Conjecture.** The coefficient-faithful completed source makes
\(G_6^{1-\delta}-G_6^{1+\delta}\) trace class.

**Verdict: RECEIVER PROVED; PRODUCER OPEN.** Shell \(m\) has multiplicity \(5\cdot6^m\), so the
two trace masses are \(5\cdot6^{m\delta}\) and \(5\cdot6^{-m\delta}\).  Their difference can be
summable only at \(\delta=0\).  But existing source reflection does not prove the asserted
trace-class difference; asserting it is the missing comparison in another form.

**Positive survivor.** Replace a raw trace-class assertion by its logarithmic tangent family,
which is defined at every finite cutoff and retains every coefficient.  This yields C3.

### C3 -- Gamma-six/Wold tangent-profile identity

**Conjecture.** The logarithmically normalized Gamma-six shell Green trace has the same all-order
tangent profile as the Wold prime clock.

**Verdict: PROVED on paper and in Lean.** Equations (1)--(6) prove the claim.  The constant trace
mass in (1) is the higher principle behind the Wold moment law: both carriers are uniform measure
on logarithmic depth after source normalization.

**Novel content.** Route L's weak-trace boundary and Routes R/T's prime-clock properness are one
object in different coordinates.  The first is a singular-shell realization; the second is its
nonlinear tangent character.

### C4 -- use the source-dagger cyclic theorem directly on the shell quotient

**Conjecture.** Route L's Wold coface modulo trace class plus the nonzero shell quotient class
instantiates the existing source-dagger boundary-class theorem and proves RH without a physical
Green comparison.

**Verdict: FALSIFIED as stated.** The evaluated off-neutral character is not simultaneously in
the two strict critical-edge domains.  Therefore the quotient-valued landing required by the
cyclic theorem is undefined precisely where it would need to exclude an off-line Xi point.
Using the quotient theorem there silently assumes the domain-preserving base change.

**Positive survivor.** The obstruction is not missing cyclic algebra or non-erasure: both exist.
It is failure of source-character evaluation to commute with formation of the singular trace
quotient.

### C5 -- source/singular-trace Beck--Chevalley law

**Current conjecture.** Let `ev_u` be horizontal-character evaluation on the complete marked
source, `Q` the Gamma-six shell quotient by trace class, and `R` source reflection.  Construct a
non-equivariant comparison on the *finite logarithmic tangent family* such that

\[
 Q\,\mathrm{ev}_u\,R \quad\text{and}\quad Q\,R\,\mathrm{ev}_u
\]

have the same centered shell boundary response.  Coefficient faithfulness requires the equality
before codiagonalization over primes, Xi multiplicity copies, or reflection slots.  By C3 the
base-change defect is \(F(u)-F(-u)=2F(u)\), so vanishing forces \(u=0\).

This formulation is deliberately non-equivariant: strict equivariance off the neutral character
is already ruled out by the source-dagger cyclic monodromy theorem.  It asks instead for equality
of two source-derived finite-cutoff boundary traces, whose common horizon is known.

**Status: OPEN.** No corpus theorem currently proves this commutation.  Route L's strict completed-
Green comparison would imply it, but C5 may be strictly weaker because it only compares the
centered logarithmic tangent response rather than constructing the entire target operator.

## Exact RH receiver

For a multiplicity-labelled Xi divisor copy \(q\), put

\[
 u_q=2\operatorname{Re}(q)-1.
\]

Source reflection sends \(u_q\) to \(-u_q\).  The pointwise proposition

\[
 F(u_q)=F(-u_q) \tag{8}

\]

is equivalent to \(\operatorname{Re}(q)=1/2\).  Requiring (8) for every `XiZeroCopy` is equivalent
to `RiemannHypothesis`.  These equivalences are unconditional Lean theorems; they do not assert
(8).

## No-go closure

- **Exact killing theorem/mechanism:** equivariant or quotient-valued reflected landing cannot be
  formed off-neutral without already paying the strict-domain condition.  Reflection supplies
  negation, not equality.
- **Strongest positive survivor:** exact all-order shell/Wold profile identity and a strictly weaker
  source/singular-trace base-change producer C5.
- **New insight:** repeated route stalls are shadows of one noncommuting square: horizontal
  character specialization, reflection, and singular-quotient formation do not commute away from
  the critical character.  The universal profile `F` is the explicit base-change anomaly.
- **Status:** C3 and the RH receiver are paper-proved and Lean-formalized in
  `SourceHorizontalShellGreenPrimeClockProfile.lean`.  C5 remains open.

## Hostile audit

1. No RH premise, numerical experiment, zero-density estimate, or selected Xi-zero location enters
   (1)--(7).
2. Shell multiplicity is literal `5 * 6^m`; dropping it destroys constant trace mass and the
   singular wall.
3. Green decay is literal `(1/6)^m`; no damping was fitted to reproduce Wold moments.
4. Prime/Xi labels are not averaged in the RH receiver: equality is required for every
   `XiZeroCopy` separately.
5. Reflection is retained as two oriented responses, not replaced by their square or codiagonal
   sum.
6. C5 may not define the target quotient domain by desired membership or assume boundedness of the
   nonlinear polar work.
7. The finite trace formula (6) prevents a formal power-series analogy from being counted as the
   source theorem.
8. C4 records why invoking cyclicity of a singular trace before domain-preserving evaluation is
   theater.

## Lean certificate

Module:
`formal/GaloisForLFunctions/RHTower/SourceHorizontalShellGreenPrimeClockProfile.lean`

Key declarations:

- `sourceHorizontalGammaSixShellGreenTraceMass_eq_five`
- `tendsto_sourceHorizontalGammaSixShellNormalizedMoment`
- `sourceHorizontalGammaSixShellMoment_matches_Wold`
- `tendsto_sourceHorizontalGammaSixShellPrimeClockProfileSeries`
- `sourceHorizontalGammaSixShellPrimeClockProfileSeries_eq_finiteTrace`
- `tendsto_sourceHorizontalGammaSixShellReflectionBaseChangeDefect`
- `sourceHorizontalGammaSixShellReflectionBaseChangeLimit_eq_zero_iff`
- `sourceZeroHorizontalGammaSixShellReflectedResponseIdentified_iff`
- `sourceZeroHorizontalGammaSixShellReflectedResponsesIdentified_iff_riemannHypothesis`

## Log

- 2026-08-11 -- Updated frontier audited; fixed-degree tail closure and reflection-only strict
  landing falsified.
- 2026-08-11 -- Exact Gamma-six shell mass/Wold all-order tangent-profile identity proved on paper
  and in Lean; finite trace resummation and exact RH receiver added.
- 2026-08-11 -- Direct cyclic-quotient bypass falsified; source/singular-trace base-change law C5
  isolated as strictly weaker possible producer.
