# Zeta source-effectivity arithmetic equivalence principle

- **ID:** `zeta-source-effectivity-arithmetic-equivalence-principle`
- **Stage:** 1-in-progress
- **Type:** FROZEN CONJECTURE / THIRD-COMPLETION AXIOM
- **Scientific status:** `[TRUTH-HUNCH] [PROOF UNKNOWN] [LITERATURE-NOVELTY PROVISIONAL]`
  `[IMPLIES RH]`
- **Parents:**
  - `source-curved-prime-torus-conormal-temperedness.md`;
  - `completed-euler-divisor-incidence-stack-conjecture.md`;
  - `../3-formalized/source-producer-integral-realization-minimality.md`;
  - `high-shell-critical-hardy-conormal-uniformization.md`;
  - `adelic-mfree-shell-fourier-rank-one-fracture.md`.
- **Statement:** The all-zero holomorphic Xi conormal and the unitary half-density
  Euler-incidence realization are two conservative realizations of one source-effective completed
  zeta object, so their multiplicity-graded conormal representations are canonically isomorphic.

## Goal

Explain why every nontrivial zero lies on the critical line by identifying two structures that the
current corpus treats separately:

```text
completed ordinary-prime source transport
  =
Xi principal-conormal transport in half-density coordinates.                 (A1)
```

This is an arithmetic equivalence principle, not a proposed proof technique.  Based on the
positive shell frame, exact co-Poisson continuation, six-channel HT minimality, and the contrast
between all-zero and critical-only spectral realizations, the equality in `(A1)` now appears
plausible.  No method for proving it is known.  Provability is not part of the conjecture.

## Forced source object

Let

```text
G=Q_(>0)^x=direct-sum_(p prime) Z
```

act by actual rational dilation on the algebraic BV/co-Poisson source core.  For every finite
prime set `P`, let `E_P` be the pointed Euler action groupoid of genuine source changes, not a
free group imposed on prime labels.  Let `I_P` retain the six independently forced channels:

```text
1. external Euler source action;
2. signed Hermitian/reflection polarization;
3. critical Gevrey product bornology;
4. complete controlled nonabelian transport germ;
5. distinguished source-generated completed section;
6. integral/ramified ordinary-prime lattice and comparison maps.             (A2)
```

The coefficient, Gamma, and trace components are the actual completed zeta source components.
They may not be reconstructed from a target divisor.  Prime enlargement must preserve existing
arrows, source coordinates, and trace moments.

Let

```text
S_pr(G)=colim_(P finite) S(Z^P)
```

be the finite-prime Schwartz Ind-space.  Its half-density rigging is

```text
S_pr(G) subset ell2(G) subset S_pr(G)'.                                  (A3)
```

Prime translations are unitary in the middle and continuous on both outer terms.  Every unitary
character survives in the dual; an exponentially growing two-sided character does not.

Independently, let `U` be the shifted nontrivial Xi strip, let `Lambda` be the completed
co-Poisson multiplier, and put

```text
N_Xi=O(U)/(Lambda).                                                       (A4)
```

This is the all-zero holomorphic principal-conormal realization, including multiplicity jets.
For a jointly noncensoring BV family `W_sep`, pole cancellation defines before any zero is chosen

```text
J_Xi^alg : C[G] tensor W_sep -> N_Xi,
J_Xi^alg(g tensor W)=[Lambda F_(g.W)].                                   (A5)
```

## Frozen conjecture

> **[CONJECTURE — ZETA SOURCE-EFFECTIVITY ARITHMETIC EQUIVALENCE PRINCIPLE.]**
> The cofinal pointed system `(I_P)_P` has a canonical source-effective half-density
> linearization `H_zeta` with test space `(A3)`, and the source-generated comparison induced by
> `(A5)` identifies its multiplicity-graded distributional conormal representation with `(A4)`:
>
> ```text
> R_hd(H_zeta) ~= R_hol(N_Xi).                                             (A6)
> ```
>
> The isomorphism is `G`-equivariant, reflection-polarized, integral-lattice compatible,
> presentation-independent, and nonzero on the top jet of every nontrivial Xi divisor point.
> Forgetting to the arrow direction, `(A6)` is exactly the continuous extension of `(A5)` from
> `C[G]` to `S_pr(G)`.

The word **source-effective** is load-bearing.  The comparison must be produced by the completed
ordinary-prime section and the incidence functors `(I_P)` before a zero, divisor character, Weil
sign, or target Hilbert vector is selected.  The analytic germ or its zero set may not be stored
as hidden source data.

The conjecture is one equality of realizations, not a conjunction of proof lemmas.  A Wold
mapping cone, a Scaling-Site sheaf comparison, a derived fracture totalization, or a
prime--Gamma transform might eventually prove it, but none belongs to the conjecture.

## Conditional RH theorem

Let `rho` be a nontrivial Xi zero.  The top nonzero jet of `(A5)` transforms on the one-prime
subgroup `p^Z` by

```text
k |-> polynomial(k) p^(k(rho-1/2)).                                      (A7)
```

By `(A6)`, this jet is a continuous distribution on `S(Z)`.  A two-sided exponential sequence is
tempered exactly when its exponential modulus is one.  Polynomial jet factors do not alter the
criterion.  Hence

```text
|p^(rho-1/2)|=1,
Re(rho)=1/2.                                                              (A8)
```

The same argument handles every multiplicity.  Thus `(A6)` implies RH.

This consequence does not prove `(A6)`.  In the natural compact-open quotient topology, the
underlying prime-Schwartz continuity statement is itself equivalent to RH.  Conjecture value is
explanatory and source-categorical: it says why that continuity should exist—because holomorphic
divisor transport and positive ordinary-prime half-density transport are one effective object.

## Why the hunch is plausible

1. The high-exponent positive shells provide an infinite ordinary-prime source frame carrying the
   complete strict-right Xi divisor with multiplicity and maximal relative HT rank.
2. Their pole residues are exact finite-adele Haar shell masses, not chosen Hilbert weights.
3. The residue completion has the exact Hardy wall `Re(s)=1/2`; reflected normal jets occupy
   opposite regularity layers off the line.
4. Finite clocks retain evaluation but leak dilation covariance.  Scalar adelic `L2` restores
   covariance but loses point fibres.  The rigging `(A3)` has exactly the missing capability:
   unitary covariance in the middle and tempered point fibres in the dual.
5. The coefficient Wold tower, Gamma determinant, BV first trace, and Xi conormal have already
   been typed on one valuation-layer renewal.  They are not unrelated analogies.
6. The six-channel minimality theorem explains why earlier scalar, unpolarized, nonintegral, or
   target-defined completions could not be conservative.
7. Existing all-zero nuclear spectral realizations and critical-only unitary realizations are the
   two external shadows predicted by `(A6)`.

## Hostile corpus tests

The conjecture is designed to fail every known false shortcut.

1. **Bare HT fails.**  Exponent-zero sparse Euler gauges preserve a complete divisor while changing
   the source frame.  `(A6)` retains the source action, effective section, and integral comparison.
2. **Generalized-prime countermodels fail.**  Positive generalized-prime systems with off-line
   zeros need not carry the ordinary-prime integral lattice and source-effective cofinal incidence
   system in `(A2)`.
3. **Scalar codiagonal fails.**  Shell labels remain in the pointed groupoid and half-density
   realization; no nonclosable unit-weight row erases them.
4. **Bare adelic Fourier fails.**  Its high-shell cross-Gram is rank one and pole-only.  `(A6)`
   concerns the full nonproduct completed incidence, not a separable finite-adele transform.
5. **One Hilbert shell norm fails.**  It makes the right half-strip the bounded-evaluation
   interior.  `(A3)` is the full two-sided prime-Schwartz rigging, not that one residue Hilbert
   space.
6. **Functional equation alone fails.**  Reflection polarization is one channel of `(A2)`, while
   source effectivity and integral comparison supply independent data.
7. **Abstract self-adjointness fails.**  `H_zeta` must linearize the named source system and
   comparison `(A5)`; an operator tuned from zeros or Xi phase does not satisfy the conjecture.

## Falsifiers

Retire or narrow the conjecture if any one of the following is proved.

1. No cofinal source-derived incidence functor can retain the six channels in `(A2)` while its
   arrow test space has prime-Schwartz topology.
2. The algebraic map `(A5)` depends on a window presentation or fails a genuine algebraic source
   relation before zero specialization.
3. A source-effective half-density comparison necessarily has a nonzero kernel on a proved
   noncensoring Xi top jet.
4. An explicit off-line system carries the same ordinary-prime integral source section, completed
   Gamma/co-Poisson incidence, and compatible half-density comparison `(A6)`.
5. External literature already proves or refutes the all-zero/critical-unitary source-effective
   comparison, not merely one of its two realizations.

## Literature boundary

Parent theories already contain both sides separately.

- Meyer constructs an operator on a nuclear Fréchet space whose spectrum is the complete
  nontrivial zeta divisor.
- Connes--Consani construct a Scaling-Site Schwartz/Hilbert quotient whose scaling spectrum is the
  critical zero divisor.
- Connes--Consani--Moscovici construct semilocal self-adjoint approximants and identify convergence
  to Xi as the missing theorem.
- Burnol's co-Poisson and Sonine theory supplies source quotients and zero evaluators.
- Tate/Ind--Pro, rigged representations, transformation groupoids, and systems of realizations are
  parent categories.

Targeted searches found no theorem deriving a canonical isomorphism between the complete
holomorphic conormal divisor and the critical unitary representation from the completed
ordinary-prime source, with six-channel effectivity, integral lattice, and multiplicity jets.
Only this exact comparison is a novelty candidate.  Discoveries already present in this research
corpus remain usable accumulated progress; novelty is judged against external literature.

## Post-conjecture research questions

These questions concern proof and may all be replaced without changing the conjecture.

1. Does the cofinal pointed Euler incidence functor exist already on every finite prime packet?
2. Is its half-density linearization a fracture pullback of Meyer's nuclear representation and
   the Connes--Consani Scaling-Site quotient?
3. Which nonproduct prime--Gamma incidence creates transverse coupling beyond the finite-adele
   rank-one pole mode?
4. Does the source-generated comparison have closed positive image, avoiding the
   closure-only critical nonattainment phase?
5. Can the Wold--Gamma/BV relative class compute the obstruction to `(A6)` without defining that
   obstruction from a zero?

## Gates

- [x] 0 → 1: truth-hunch stated independently of proof visibility
- [x] source object, comparison, and RH consumer typed
- [x] internal no-gos incorporated as accumulated progress
- [x] preliminary external literature boundary checked
- [ ] finite-cutoff source incidence functor constructed
- [ ] cofinal six-channel effectivity proved
- [ ] source half-density linearization constructed
- [ ] comparison `(A6)` constructed before zero specialization
- [ ] comparison proved conservative and multiplicity-faithful
- [ ] independent specialist novelty audit
- [ ] dependency-closed paper proof
- [ ] unconditional Lean formalization
- [ ] RH

## Log

- 2026-07-28 — Froze arithmetic equivalence principle after separating conjecture generation from
  proof design.  Combined prime-Schwartz conormal temperedness, six-channel HT source effectivity,
  pointed Euler groupoid, positive high-shell Haar frame, adelic Fourier rank-one fracture, and the
  external all-zero versus critical-only spectral realizations.  Internal corpus discoveries are
  treated as inherited advances; novelty gate is external literature only.
