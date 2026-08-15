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

### C2 -- divisor-formalism effectivity `[FALSIFIED]`

**Claim.** Full proper-subgroup and quotient compatibility, induction, holomorphy of every
monomial package, non-vanishing in the absolute-convergence half-plane, Stark's norm bound,
complex conjugation, and functional-equation symmetry force every order character to be genuine.

**Killing model `[PAPER-PROVED]`.** Keep `G = PSL(2,q)`, `q > 5` an odd prime, and take the
real-valued Steinberg-derived minimal Heilbronn noncharacter `theta` from C1.  Put

```text
Z = {1/3+i, 1/3-i, 2/3+i, 2/3-i},
P(s) = product_(z in Z) (s-z).
```

Then `P(1-s)=P(s)`, `P(conj(s))=conj(P(s))`, and `P` has no zero in `Re(s)>1`.  For every
virtual character `psi` of `G`, define the synthetic meromorphic package

```text
mathcalL_G(s,psi) = P(s)^<theta,psi>.
```

For `H <= G`, define `mathcalL_H(s,phi)=P(s)^<Res_H(theta),phi>`.  Integer-valuedness of
character inner products makes these single-valued meromorphic functions.  They have all of the
following properties.

1. Additivity becomes multiplicativity:
   `mathcalL(s,psi_1+psi_2)=mathcalL(s,psi_1)mathcalL(s,psi_2)`.
2. Frobenius reciprocity gives exact induction compatibility:
   `mathcalL_G(s,Ind_H^G phi)=mathcalL_H(s,phi)`.
3. If `H<G`, minimality says `Res_H(theta)` is a genuine character, so every
   `mathcalL_H(s,phi)` for genuine `phi` is entire.  If `m` is monomial on `G`, Heilbronn
   positivity gives `<theta,m> >= 0`, so `mathcalL_G(s,m)` is entire.
4. Every package is holomorphic and non-zero in `Re(s)>1` because `P` is.
5. Real-valuedness of `theta` and the two displayed symmetries of `P` give complex-conjugation
   compatibility and the exact functional equation `mathcalL_G(1-s,psi)=mathcalL_G(s,psi)`.
6. The regular factor is entire: `<theta,Reg_G>=theta(1)=q>0`.  The order character at every
   `z in Z` is exactly `theta`, and it still obeys `||theta||^2=2q+1<=q^2=theta(1)^2`.
7. Since `theta` is not genuine, some irreducible coefficient `<theta,chi>` is negative; the
   corresponding `mathcalL_G(s,chi)` has a pole at every point of `Z`.

Thus the claim is false even after all divisor-level constraints are imposed simultaneously.
The construction is deliberately not an Artin L-function: it has no Frobenius-determinant local
Euler factors.  That omission is the exact information boundary exposed by the countermodel, not
a proposed counterexample to Artin holomorphy.

**Positive survivor `[PAPER-PROVED] [BRIDGE] [NOVELTY UNVERIFIED]`.** Any proof using only
integer order characters, restriction/induction, monomial effectivity, zero-free source chamber,
Stark norm, and functional-equation orbits cannot prove Artin holomorphy.  A successful route must
use a law that sees the genuine Frobenius-local determinant Euler factors and constrains their
continued divisor without factoring through the pointwise order character.  This is the common
source-to-divisor seam behind C1, the local phase-defect blindness law, and full-divisor tomography.

**Lean status.** Exact survivor depends on Ginsberg's explicit `PSL(2,q)` character construction.
No such finite-group character-table infrastructure exists in the project.  Formalizing the scalar
polynomial shell alone would omit the theorem's killing witness and violate the anti-theatre cost
gate, so no Lean file is opened.

### Relentless interrogation after C2

- Another pointwise inequality cannot work: the same `theta` can be installed at a complete
  functional-equation orbit while retaining every known static inequality.
- More divisor tomography cannot work: the model already specifies the complete divisor exactly.
- Prime-source positivity only in `Re(s)>1` cannot work: the model is zero-free there, yet its
  continuation has poles.
- A replacement must use the *shape* of genuine local factors
  `det(1-rho(Frob_p)N(p)^(-s) | V^{I_p})^(-1)` across infinitely many primes.  Merely assuming an
  Euler product in its convergence chamber and then forgetting those factors loses the needed
  information again.
- Calling this missing law automorphy, Selberg orthogonality, or positivity of a hypothetical
  Rankin--Selberg convolution is circular unless that law is independently constructed from the
  finite-image Euler data.

## `[OPEN CORE]`

State and prove an exact arithmetic realizability law for the full family of order characters that
is stronger than static Heilbronn/Stark admissibility, survives Ginsberg's `PSL(2,q)` fakes, and is
not equivalent by definition to Artin holomorphy or strong Artin automorphy.  C2 sharpens this:
the law must couple Frobenius-determinant Euler factors to the continued divisor and cannot factor
through any pointwise order-character package, even one carrying full functional-equation orbits.

## Lean gate

The open-core conjecture has no closed paper proof and may not be formalized through a surrogate
interface.  The user has explicitly authorized formalization of paper-closed, standard literature
infrastructure first.  That authorization is narrow: every such module must state its exact
classical theorem, record its non-novel status, and leave the open source-to-divisor law untouched.
Current priority is the integral finite-abelian Fourier basis in
`artin-finite-abelian-integral-fourier-basis.md`; then the genuine Frobenius--inertia local Euler
polynomial, then the Brauer/Heilbronn/Stark layers.  No module may claim to prove this card until
the non-factorizing arithmetic source-to-divisor law itself is closed on paper.

## Log

- 2026-08-14 -- opened at Stage 1; internal corpus and current external frontier audited.
- 2026-08-14 -- C1 killed by Ginsberg's Steinberg-derived minimal Heilbronn family, which also
  satisfies Stark's norm inequality.  Pivot forced from static character cones to global
  arithmetic divisor-flow realizability.
- 2026-08-14 -- C2 killed by an explicit symmetric synthetic L-package realizing the same fake
  order character while satisfying all divisor-formalism constraints.  Pivot sharpened from
  global divisor coherence to a non-factorizing Frobenius-source-to-divisor law.
- 2026-08-15 -- user correction: build missing paper-closed literature infrastructure before any
  new route; opened the integral finite-abelian Fourier basis as first audited bridge.
- 2026-08-15 -- finite-abelian integral Fourier basis formalized and target-built; it closes the
  complex-span/integral-closure interface only and leaves the non-factorizing
  Frobenius-source-to-divisor open core unchanged.
- 2026-08-15 -- genuine Frobenius--inertia local Euler polynomials formalized and target-built
  in `ArtinLocalEulerFactor.lean`, including arithmetic lift-independence.  This closes the
  local source definition absent from C2, but it still supplies no global Euler product,
  continuation, or source-to-divisor/effectivity law.
- 2026-08-15 -- local Euler polynomials formalized to multiply under actual binary direct sums in
  `ArtinLocalEulerProduct.lean`.  This closes the first source-additivity identity, while prime
  descent, global product/continuation, and the non-factorizing source-to-divisor law remain open.
- 2026-08-15 -- Maschke’s actual finite simple-module decomposition formalized in
  `ArtinMaschkeDecomposition.lean`.  It supplies the carrier below irreducible-character and
  Brauer-lattice work, but does not itself establish any analytic continuation or effectivity.
- 2026-08-15 -- virtual-character Frobenius reciprocity formalized in
  `ArtinVirtualFrobeniusReciprocity.lean`: every monomial coefficient is the corresponding
  linear multiplicity after restriction.  This is the exact finite transport underlying a future
  Heilbronn restriction law, not that analytic law itself.
- 2026-08-15 -- monomial-multiplicity separation formalized in
  `ArtinMonomialMultiplicitySeparation.lean`: all induced-linear multiplicities jointly determine
  a concrete virtual character.  This is a finite-character detection theorem, not integral
  Brauer induction or analytic effectivity.
- 2026-08-15 -- conjugate-prime invariance of the actual local Artin Euler polynomial formalized
  in `ArtinLocalEulerPrimeDescent.lean`, including inertia transport, invariant-space conjugacy,
  conjugated arithmetic Frobenius, and residue-finiteness transport.  Arbitrary base-prime choice,
  global product/continuation, and the non-factorizing source-to-divisor law remain open.
- 2026-08-15 -- the arbitrary-prime choice is now removed at the number-field finite-place level:
  `ArtinNumberFieldLocalEulerFactor.lean` defines a canonical polynomial on
  `HeightOneSpectrum (𝓞 K)` and proves every prime above that base finite prime computes it.  This
  supplies the genuine local source C2 lacked, but still neither an infinite Euler product nor a
  law connecting that product's continuation to coefficientwise polar effectivity.
- 2026-08-15 -- direct-sum multiplicativity now holds for that exact finite-place polynomial in
  `ArtinNumberFieldLocalEulerProduct.lean`.  Thus the local source is choice-free and additive in
  actual representations; the next missing mathematical object is a convergent global Euler
  product, not another local compatibility wrapper.
- 2026-08-15 -- `ArtinFormalEulerSource.lean` constructs the genuine coefficientwise global Euler
  source from the canonical local factors and proves finite-product stabilization at every
  coefficient.  It closes the formal global-source gap but not absolute/local-uniform convergence
  in `Re(s)>1`, equality with an analytic product, continuation, or polar effectivity.
- 2026-08-15 -- renewed literature/frontier audit identifies full integral Brauer induction from
  linear characters of Brauer-elementary subgroups as the first nonlocal continuation bridge.
  Rational Artin induction and monomial-profile separation are explicitly insufficient.  The new
  `artin-brauer-integral-monomial-induction` card remains at Stage 1 pending a complete concrete
  finite-lattice paper-to-Lean proof plan.
- 2026-08-15 -- formalized unconditional number-field finite-prime norm summability for every
  exponent greater than one, including the complex-norm form needed for Euler arguments.  This is
  the actual M-test budget missing from the formal Euler source; a uniform local-factor estimate
  and locally uniform product proof remain open.
- 2026-08-15 -- isolated the next source-side literature bridge in
  `artin-euler-product-absolute-locally-uniform-convergence.md`: finite image must first give a
  uniform reciprocal-local-factor estimate, then compact M-test machinery gives a holomorphic
  product only on `Re(s)>1`.  This does not touch continuation or the non-factorizing
  source-to-divisor open core.
- 2026-08-15 -- split out the prerequisite `artin-finite-order-local-polynomial-bound` card.
  The exact finite-order local action is now formalized; characteristic-polynomial root control
  and the quantitative inverse bound are the remaining source-side proof obligation.
- 2026-08-15 -- target-built the finite-order action and finite-order characteristic-root norm
  lemmas with a standard-foundations-only axiom audit.  This makes the root-of-unity input real;
  it still does not establish local-factor nonvanishing or an Euler product.
- 2026-08-15 -- completed and target-built the root-free local-polynomial bridge: finite-order
  characteristic roots have norm one, the reversed characteristic polynomial factors as
  `∏(1-μT)`, and every actual Frobenius--inertia polynomial is nonzero on `|T|<1`.  The missing
  uniform reciprocal estimate and compact product proof remain, so no analytic continuation or
  polar-effectivity conclusion follows.
- 2026-08-15 -- transported that nonvanishing to every canonical base finite place at the genuine
  Euler argument whenever `Re(s)>0`, with source/target/axiom checks.  This eliminates no global
  pole and does not make an infinite product; quantitative local control remains the next gap.
