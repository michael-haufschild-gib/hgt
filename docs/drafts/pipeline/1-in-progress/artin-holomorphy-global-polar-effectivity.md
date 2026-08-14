# Artin holomorphy via global polar effectivity

- **ID:** `artin-holomorphy-global-polar-effectivity`
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** user goal, opened 2026-08-14
- **Statement:** For every finite Galois extension `K/F` of number fields and every nontrivial
  irreducible complex character `chi` of `Gal(K/F)`, the Artin L-function
  `L(s, chi, K/F)` is entire.

## Goal

Prove or disprove Artin's holomorphy conjecture unconditionally.  No criterion equivalent to
holomorphy, automorphy assumed as input, static virtual-character reformulation, finite-height
verification, or conditional zero count closes this card.

## Gates

- [x] 0 -> 1 in-progress: exact classical statement; internal and external frontier audit opened
- [ ] 1 -> 2 fully-proven: complete paper proof or explicit counterexample; no open dependency
- [ ] 2 -> 3 formalized: exact unconditional Lean theorem; no hypotheses or new axioms
- [ ] 3 -> 4 publication-ready: standalone proof, priority audit, Lean certificate

## Internal frontier `[LOCAL-RESEARCH]` / `[CORPUS]`

1. `selberg-orthogonality-working-log.md` records Murty's implication from Selberg orthogonality to
   Artin holomorphy.  Its own exact wall is quadratic/functorial: Selberg axioms expose linear prime
   data but do not construct the Rankin--Selberg pairing needed for orthogonality.  Importing this
   implication would replace Artin by a stronger open problem.
2. `verified-height-amplification.md` imports Bellotti--Wong's Artin zero count only under Artin
   holomorphy.  It is a conditional consumer and cannot source holomorphy.
3. `[CORPUS]` `phaseDefect_eq_iff_exists_character` and
   `no_phaseDefect_criterion_detects_criticalLine` in
   `formal/GaloisForLFunctions/RHTower/AdelicPhaseDefectCharacterBlindnessLaw.lean` prove that a
   coboundary/reciprocity layer quotients out character twists.  Any Artin route using only
   reciprocity defects is therefore structurally blind to the irreducible character coordinate.
4. `[CORPUS]` `positiveDefiniteOnReal_canonicalEulerLogZeta_vertical` in
   `formal/GaloisForLFunctions/RHTower/CriticalPrimeTailEulerLogPositiveDefinite.lean` proves
   Euler-log positive definiteness only in the absolute-convergence chamber.  The companion wall
   shows this source positivity does not cross the critical boundary for free.
5. `[LOCAL-RESEARCH]` `orbitwise-source-divisor-seam-obstruction.md` proves that a faithful
   first-prime detector can still be an exact coboundary; source detection alone supplies no
   non-character coupling to divisor germs.
6. `[LOCAL-RESEARCH]` `inverse-tilted-dyadic-prime-full-divisor-tomography.md` recovers a complete
   divisor and exact multiplicities from one prime source but leaves line/effectivity selection
   unchanged.  Complete tomography is a bridge, not positivity.
7. Generated Lean API and `scripts/formal_tools.py research` contain no Artin L-function,
   Heilbronn-character, or Brauer-induction theorem surface.  `Procesi / Artin` in the consolidated
   index is character-variety invariant theory and unrelated.

## External frontier `[LITERATURE]`

1. Brauer induction gives meromorphic continuation.  Degree-one and monomial characters give
   entire L-functions by class field theory/induction.
2. Langlands--Tunnell proves strong Artin for irreducible two-dimensional representations with
   solvable image.  Khare--Wintenberger's proof of Serre modularity gives the odd irreducible
   two-dimensional case over `Q`.  Ramakrishnan proves solvable `GO(4)`-type cases; Calegari proves
   specified `S_5` cases.  None supplies general finite-image automorphy.
3. Stark's order character satisfies
   `sum_chi n(chi)^2 <= ord(zeta_K, s0)^2`; a simple Dedekind-zeta zero therefore gives local
   holomorphy.  Foote--Murty, Foote--Wales, Wong, and Gun--Hazra--Sahu strengthen multiplicity
   thresholds for solvable groups, but retain explicit zero-order hypotheses.
4. Lemke Oliver--Thorner--Zaman prove large holomorphic/nonvanishing regions for faithful Artin
   representations for almost all fields in specified families.  This is an average regional
   theorem, not global holomorphy for every representation.
5. Ginsberg constructs minimal Heilbronn virtual noncharacters for `PSL(2,q)`: they restrict to
   characters on every proper subgroup and quotient and pair nonnegatively with every monomial
   character.  Thus the fixed-point character cone is strictly larger than the genuine character
   cone even after the standard minimal-counterexample tests.
6. Bellotti--Wong (arXiv:2606.31441) assumes Artin holomorphy for its general Artin zero-counting
   formula; it cannot be reversed without a new pole-separation theorem.

Primary sources currently audited:

- Gun--Hazra--Sahu, *On holomorphy and non-vanishing of Artin L-functions* (2025),
  https://doi.org/10.1007/s00605-025-02060-7
- Ginsberg, *Unfaithful minimal Heilbronn characters of L2(q)* (2013),
  https://doi.org/10.1017/S0013091512000168
- Lemke Oliver--Thorner--Zaman, *An approximate form of Artin's holomorphy conjecture* (2023),
  https://arxiv.org/abs/2012.14422
- Booker, *Poles of Artin L-functions and the strong Artin conjecture* (2003),
  https://doi.org/10.4007/annals.2003.158.1089
- Ramakrishnan, *Modularity of solvable Artin representations of GO(4)-type* (2002),
  https://arxiv.org/abs/math/0102231
- Calegari, *The Artin Conjecture for some S5-extensions* (2012),
  https://arxiv.org/abs/1112.1152
- Bellotti--Wong, *Counting zeros of Artin L-functions* (2026),
  https://arxiv.org/abs/2606.31441

## Exact residue

At a hypothetical pole `s0 != 1`, the order vector

```text
theta_s0 = sum_(chi in Irr(G)) ord_(s=s0) L(s,chi) * chi
```

is a virtual Heilbronn character.  Artin holomorphy is coefficientwise effectivity of every such
`theta_s0`.  Proper-subgroup restriction, quotient descent, monomial testing, and Stark's norm
bound do not yet force effectivity.  Automorphy does force it, but is stronger open input.  Exact
unsettled residue: find an arithmetic, globally coherent source-to-divisor constraint that excludes
minimal Heilbronn noncharacters without assuming component holomorphy or automorphy.

## Hostile conjecture loop

### C1 -- static Stark-Heilbronn effectivity `[FALSIFIED]`

**Claim.** A virtual character that is minimal Heilbronn and satisfies Stark's norm inequality
`||theta||^2 <= theta(1)^2` is a genuine character.

**Killing mechanism.** In Ginsberg's case (ii), take `G = PSL(2,q)` for an odd prime `q > 5`,
`P1 = P`, and the Steinberg character `sigma` of degree `q`.  Theorems 1.1--1.2 give a minimal
Heilbronn noncharacter `theta` with

```text
theta(1) = q,            ||theta||^2 = 2q + 1.
```

Since `q > 5`, `2q+1 <= q^2`.  The fake passes the Stark inequality and every static
proper-subgroup/quotient/monomial test, but is not a character.

**Verdict:** `FALSE`.  Static character theory, even strengthened by the global Stark norm bound,
cannot prove Artin holomorphy.

**Positive survivor `[PAPER-PROVED] [BRIDGE] [NOVELTY UNVERIFIED]`.** The displayed family is an
explicit sharp firewall: any successful criterion must distinguish arithmetic realizability from
abstract minimal Heilbronn admissibility.  Its paper proof is the cited Ginsberg construction plus
the elementary inequality above.  Exact Lean status: not formalized; the project lacks the needed
`PSL(2,q)` character-table and Heilbronn infrastructure.  Formalizing only the numerical inequality
would be theatre and would not formalize the survivor.

**Representation lesson.** The pole object cannot be treated pointwise as a virtual character
fixed by subgroup constraints.  Needed information must couple the whole meromorphic divisor to
Euler sources across a genuine evolution (twist, base change, or spectral parameter), while
remaining visible after character projection.

### Relentless interrogation after C1

Based on what killed C1, the replacement may not add another static cone inequality.  It must use
global arithmetic realizability.  Candidate formation remains open until an exact non-circular
divisor-flow law is stated and attacked.  Functional-equation orbit symmetry alone is insufficient:
one can place a Ginsberg fake and its duals on a four-point symmetry orbit without changing any
pointwise character constraint.  Euler-log positivity only in the convergence chamber is also
insufficient by the local corpus wall.

## `[OPEN CORE]`

State and prove an exact arithmetic realizability law for the full family of order characters that
is stronger than static Heilbronn/Stark admissibility, survives Ginsberg's `PSL(2,q)` fakes, and is
not equivalent by definition to Artin holomorphy or strong Artin automorphy.

## Lean gate

Closed paper proof absent.  Under the mandatory cost gate, no Artin Lean definitions or proof
infrastructure may be written yet.  Read-only corpus inspection only.

## Log

- 2026-08-14 -- opened at Stage 1; internal corpus and current external frontier audited.
- 2026-08-14 -- C1 killed by Ginsberg's Steinberg-derived minimal Heilbronn family, which also
  satisfies Stark's norm inequality.  Pivot forced from static character cones to global
  arithmetic divisor-flow realizability.
