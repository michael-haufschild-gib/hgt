# Rational-adelic prime-isotropy relative complex and strict Xi comparison

- **ID:** RA-PRIME-ISOTROPY-XI
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper)
- **Source:** `rh-current-frontier-map.md` strict cyclic-provenance audit; shared Route-R/Bockstein producer
- **Statement:** The zero-adele fixed-point comparison for one ordinary-prime scaling has a genuine three-term relative complex with a retained prime-isotropy `H¹` class, and that complex admits a strict prime-faithful comparison to the resolved actual-Xi cochain complex.

## Goal

Replace the invalid use of the product trace on an unproved Hochschild cycle.  Construct the
relative object before any divisor is selected, prove its prime class survives for an analytic
reason, and make the existing resolved Xi annihilation a component of a strict chain map.  This
closes chain provenance only; it does not identify resolved and scalar Cartier descent and hence
does not prove RH.

## Gates

- [x] 0 → 1 in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [ ] 1 → 2 fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3 formalized: Lean theorem names below, targeted build green, axiom audit PASS
- [ ] 3 → 4 publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Exact construction

Let

```text
A = S(R) tensor_C S(A_f)
```

be the already constructed algebraic rational adelic Bruhat--Schwartz core.  For an ordinary
prime `p`, let `alpha_p` be inverse diagonal rational scaling and let

```text
epsilon_0 : A -> C
```

be zero-adele evaluation.  The fixed-point identity is

```text
epsilon_0(alpha_p x) = epsilon_0(x).
```

The two-term prime-resolution coefficient complex `A --(alpha_p-1)--> A` therefore maps to the
zero-adele isotropy complex `C --0--> C`.  Rotate its mapping cone to the cochain convention

```text
C^0_p = A,
C^1_p = A x C,
C^2_p = C,

D_0(x)   = (alpha_p x - x, epsilon_0(x)),
D_1(y,z) = epsilon_0(y).
```

The ordinary-prime isotropy cocycle is

```text
eta_p = (0,1) in C^1_p.
```

This construction is the low-degree identity-sector relative groupoid complex for the inclusion
of the zero-adele isotropy of the prime cyclic subgroup.  It is not the old raw bar tensor
`(e U_p) tensor (e U_p^-1)` and does not use its product trace.

## Theorem A: unconditional complex law

**Claim.** `D_1 D_0 = 0`.

**Proof.** For every `x in A`,

```text
D_1 D_0(x) = epsilon_0(alpha_p x - x)
             = epsilon_0(alpha_p x) - epsilon_0(x)
             = 0.
```

Only fixed-point invariance of zero evaluation is used. `[PROVED HERE]`

## Theorem B: fixed vectors have zero zero-adele value

Define finite-zero partial evaluation

```text
P : A -> S(R),
P(f tensor phi) = phi(0) f.
```

Then

```text
P(alpha_p x) = alpha_p^infinity(Px),
epsilon_0(x) = (Px)(0).
```

**Claim.** If `alpha_p x=x`, then `epsilon_0(x)=0`.

**Proof.** Put `g=Px`.  The covariance identity makes `g` invariant under inverse scaling:

```text
g(t/p)=g(t).
```

Iteration gives `g(p^n)=g(1)` and `g(p^(-n))=g(1)` for every `n`.  Since `p>1`, `p^n` escapes
every compact subset of `R`.  Schwartz decay gives `g(p^n)->0`, hence `g(1)=0`.  Also
`p^(-n)->0`; continuity gives `g(p^(-n))->g(0)`, while the left side is constantly zero.
Therefore `g(0)=0`, and `epsilon_0(x)=0`. `[PROVED HERE]`

The proof applies to every algebraic tensor, not merely to the Gaussian prime atom.  No orbit
linear-independence premise is needed.

## Theorem C: retained ordinary-prime class

**Claim.** `eta_p` is a degree-one cocycle and its class in `H^1(C_p)` is nonzero.

**Proof.** `D_1(eta_p)=epsilon_0(0)=0`.  If `eta_p=D_0(x)`, comparison of coordinates gives

```text
alpha_p x=x,
epsilon_0(x)=1.
```

Theorem B gives `epsilon_0(x)=0`, contradiction.  Thus `eta_p` is not a boundary. `[PROVED HERE]`

This is the retained ordinary-prime class missing from the previous cyclic-source account.

## Theorem D: strict source-to-Xi chain map

Let `X^0 -> X^1 -> X^2` be the already constructed divisor-resolved Route-R complex with
`delta_0 = primeDepthBVWoldXiResolvedCovariantD0` and
`delta_1 = primeDepthBVWoldXiResolvedCovariantD1`.  Its transition-frame composition proves
`delta_1 delta_0=0` unconditionally.

For fixed `p`, let `L_p in X^0` be the prime-localized actual leading Xi conormal:

```text
L_p(rho)(q,e) = if q=p
                then (0, XiC^(m_rho)(rho))
                else 0.
```

Define

```text
Phi^0_p(x)   = epsilon_0(x) L_p,
Phi^1_p(y,z) = z delta_0(L_p),
Phi^2_p(w)   = 0.
```

**Claim.** `Phi_p` is a strict cochain map.

**Proof.** Linearity of `delta_0` gives

```text
delta_0 Phi^0_p(x)
  = epsilon_0(x) delta_0(L_p)
  = Phi^1_p(alpha_p x-x, epsilon_0(x))
  = Phi^1_p D_0(x).
```

The second square is

```text
delta_1 Phi^1_p(y,z)
  = z delta_1 delta_0(L_p)
  = 0
  = Phi^2_p D_1(y,z).
```

Thus strictness is unconditional and is inherited from actual source-frame composition, not from
critical-line location. `[PROVED HERE]`

The retained prime class lands as

```text
Phi^1_p(eta_p) = delta_0(L_p).
```

This landing is nonzero.  On the same-prime edge from depth zero to depth one, both endpoint
values of `L_p` are the nonzero leading Xi jet `j_rho`.  The second resolved coordinate is

```text
(lambda_(p,1)/lambda_(p,0)-1) j_rho = (2-1) j_rho = j_rho != 0.
```

Hence prime, depth, divisor, and conormal provenance all survive at chain level.  Applying
`delta_1` gives unconditional source-derived annihilation

```text
delta_1 Phi^1_p(eta_p) = delta_1 delta_0(L_p) = 0.
```

## Hostile circularity audit

- `eta_p` is defined before Xi divisors and uses no critical-line parameter.
- Retention follows from Schwartz decay plus continuity, not from a quotient coordinate defined to
  be nonzero.
- `Phi_p` uses only zero-adele evaluation and the independently constructed actual leading Xi
  conormal.
- Strictness uses resolved frame flatness, valid for every centered rate `a`.
- The map does **not** prove the scalar BV--Wold square vanishes.  Its image is a target boundary,
  and the resolved target is gauge-flat for every `a`.
- Replacing the resolved target by the scalar curved target would make the second chain-map square
  equivalent, on the retained class, to critical-line location.  That replacement is exactly the
  still-open singular Cartier rigidity theorem and cannot be smuggled into this construction.

## Parent-theory and novelty audit

Fixed-point localization, groupoid/crossed-product cyclic complexes, and Koszul models are parent
theory.  Brodzki--Dave--Nistor explicitly organize crossed-product periodic cyclic homology by
fixed-point strata and Koszul complexes; Crainic treats cyclic cohomology of etale groupoids,
including hyperbolic components; Ponge constructs explicit quasi-isomorphisms for crossed-product
cyclic homology.  None supplies this rational-adelic zero-isotropy retention theorem, its Schwartz
fixed-vector proof, or the prime-faithful strict comparison to the project-specific resolved Xi
complex.  Novelty claim is therefore scoped to this concrete arithmetic bridge, not to mapping
cones or fixed-point localization themselves.

## Lean target

Planned module:

```text
GaloisForLFunctions.RHTower.CCMRationalAdelicPrimeIsotropyRelativeXiChainMap
```

Required declarations:

```text
ccmRationalAdelicFiniteZeroPartialEval
ccmRationalAdelicFiniteZeroPartialEval_scaling
ccmRationalArchimedeanPrimeScaling_fixed_zero
ccmRationalAdelicPrimeScaling_fixed_zeroEval
ccmRationalAdelicPrimeRelativeD0
ccmRationalAdelicPrimeRelativeD1
ccmRationalAdelicPrimeRelativeD1_comp_D0
ccmRationalAdelicPrimeRelativeComplex
ccmRationalAdelicPrimeRelativeClass
ccmRationalAdelicPrimeRelativeClass_ne_zero
primeDepthBVWoldXiPrimeLocalizedLeadingConormal
ccmRationalAdelicPrimeRelativeXiComparison0
ccmRationalAdelicPrimeRelativeXiComparison1
ccmRationalAdelicPrimeRelativeXiComparison2
ccmRationalAdelicPrimeRelativeXiComparison_commutes_d0
ccmRationalAdelicPrimeRelativeXiComparison_commutes_d1
ccmRationalAdelicPrimeRelativeXiComparison_class_landing
ccmRationalAdelicPrimeRelativeXiComparison_class_landing_ne_zero
ccmRationalAdelicPrimeRelativeXiComparison_class_annihilated
```

## Log

- 2026-08-04 — strict-provenance gap isolated after rejecting product trace as Hochschild-homology reader.
- 2026-08-04 — zero-adele prime-isotropy mapping cone frozen; complete paper proof and hostile scalar-descent audit recorded.
