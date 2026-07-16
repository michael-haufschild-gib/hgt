# FE-weld rate blindness and the finite-source activation obstruction

- **ID:** weld-krein-rate-blindness
- **Stage:** 3-formalized
- **Type:** THEOREM / ROUTE NO-GO / ACTIVATION OBSTRUCTION, `[PROVED HERE]`
- **Date:** 2026-07-10
- **Parents:** `weld-class-determines-area-not-j.md`,
  `../../3-formalized/prime-divisor-atoms-no-go.md`
- **Lean:** `formal/GaloisForLFunctions/RHTower/WeldKreinRateBlindness.lean`
- **Statement:** `[PROVED]` All positive-rate FE weld planes are invertibly congruent, so their
  Krein isometry class forgets the prime rate.  A scalar-activated logarithmic block is
  Krein-nonnegative exactly when its activation scalar is zero.  Every pinned finite-prime source
  map forces all those scalars, and hence all associated FE blocks, to zero even at a `xi`-zero,
  where the completed divisor order is nonzero.  More strongly, no zero-preserving function of the
  simultaneous orders of all individual Euler factors and the archimedean factor can recover the
  completed divisor order there.

## 1. Positive-rate blindness

For a real rate `theta`, the FE-reflected weld Gram is

`H_theta = [[0,theta],[theta,0]]`.

Let `theta,eta>0` and put

`P_(theta,eta)=sqrt(theta/eta) I_2`.

Its determinant is `theta/eta`, hence is nonzero.  Direct multiplication gives

`P_(theta,eta)^* H_eta P_(theta,eta)=H_theta`.                 (1)

Therefore all positive-rate blocks have the same invertible congruence class.  In particular,
although `log p` determines the scale of the explicit Gram, the Krein isometry class cannot recover
`p`, `log p`, or any relative prime magnitude.

## 2. Exact activation gate

For `theta>0`, the vector `(1,-1)` has value `-2 theta` under `H_theta`.  For `theta<0`, the vector
`(1,1)` has value `2 theta`.  Thus every nonzero `H_theta` has a negative direction, while `H_0=0`.
Consequently

`KreinNonneg(H_theta) <-> theta=0`.                              (2)

If a fixed base rate `theta` is nonzero, (2) yields

`KreinNonneg(H_(a theta)) <-> a=0`.                              (3)

For every integer `p>=2`, `log p>0`, so

`KreinNonneg(H_(a log p)) <-> a=0`.                              (4)

Nonnegativity detects only whether the block is activated.  It does not detect which positive prime
rate the block carries.

## 3. Finite-prime activation is identically zero

Let `A : N -> N` be a pinned `SigmaSourceMap` at a point `rho` with `Re rho>0`.  By definition,
`A(p)` is bounded by the analytic order at `rho` of the local Euler factor for `p`.  Every such
factor is a unit on this half-plane, hence has order zero.  Therefore

`A(p)=0` for every `p>=2`.                                       (5)

Attaching the FE block with rate `A(p) log p` gives, by (5),

`H_(A(p) log p)=0` for every `p>=2`.                             (6)

If also `xi(rho)=0`, analyticity of `xi` gives

`analyticOrderAt(xi,rho) != 0`.                                 (7)

Equations (6) and (7) are the finite-source activation obstruction: exactly where the completed
divisor is nontrivial, every block activated from the primes' own finite local divisor content is
zero.

## 4. No factorwise order assembler

Package all individual local divisor orders, without choosing a cutoff, as the fixed profile

`L(rho)=((ord_rho (1-p^(-s))^(-1))_(p>=2), ord_rho G_infinity)`.

Every coordinate of `L(rho)` is zero whenever `Re rho>0`; therefore `L(rho)=0`.  Let `assemble` be
an arbitrary function from these profiles to divisor orders satisfying only the pointed condition

`assemble(0)=0`.                                                (8)

At a `xi`-zero, no such function can satisfy

`assemble(L(rho))=analyticOrderAt(xi,rho)`,                       (9)

because the left side is zero by (8), while the right side is nonzero by (7).  No additivity,
continuity, computability, or finite-support assumption is used.  Thus even the simultaneous datum
of all factorwise local orders is insufficient: the missing completed datum is not an aggregation
of those orders.

## 5. Attack on the previous open core

The previous local theorem identified `H_(log p)` exactly with the one-pair factored Krein form.  A
tempting conclusion was that a prime-log incidence map could select and assemble these blocks into
the completed divisor form.  The present theorem defeats that conclusion in both available finite
readings:

1. If incidence depends only on the local Krein isometry class, all positive prime rates are
   indistinguishable by (1).
2. If incidence is sourced by the primes' pinned local divisor atoms, every activation coefficient
   is zero by (5).
3. If incidence is any zero-preserving function of all factorwise prime and archimedean orders, it
   cannot recover the completed order by (8)-(9).

Thus the local identification is a shape theorem, not an arithmetic detector.  Declaring one block
for each prime would insert universal background indefiniteness unrelated to the zero set; sourcing
blocks from finite local orders inserts none.

The missing datum cannot be repaired by taking a moving family of finite prime atlases and passing
to `P -> infinity`: that constructs the answer by a cutoff flow.  Nor may it be repaired by defining
the activation coefficient to be the `xi`-multiplicity itself: that merely renames the divisor and
does not derive the RH-deciding form.

## Surviving open core

The only live constraint-side question exposed by the no-go is:

> `[OPEN CORE]` Is there a fixed completed obstruction class attached directly to the completed
> Euler-FE datum whose restriction to every finite Euler/archimedean subalgebra is zero, but whose
> boundary at a divisor point supplies the FE-Witt activation?  Its construction must be intrinsic
> to the completed object, not a cutoff limit, carrier, prime-by-prime source map, or repackaging of
> `analyticOrderAt xi`.

The existing sheared Fitting presentation does not by itself provide this class: it is unimodularly
equivalent to the split presentation.  Its nonzero boundary depends on a relative cutoff/defect
alignment.  Functional-equation coefficient parity canonically supplies the required static flag,
and the shear is non-split under every parity-preserving automorphism of one fixed target.  The full
semilinear audit nevertheless kills this candidate: with fixed source/target FE parity the shear is
not equivariant, while transporting target parity makes it explicitly split-equivalent; see
`sheared-seam-gauge-trivialization.md`.  What remains is a genuinely non-split FE-semilinear
extension, not another coordinate shear, together with a map to the Witt block that does not read
the answer from `analyticOrderAt xi`.

Before proposing such a class, one must prove that its target quotient retains more than the
universal hyperbolic shape and that its vanishing criterion is not tautologically equivalent to the
zero multiplicity used to define it.

## Novelty and significance gates

- **NOVEL:** The earlier theorem constructed the local FE hyperbolic block but did not test whether
  it retained prime arithmetic or could be activated from pinned prime divisor data.  The new
  congruence theorem proves rate blindness; the source-map combination proves exact block
  vanishing; and the pointed-assembler no-go rules out every nonlinear aggregation of the complete
  factorwise order profile.
- **SIGNIFICANT:** This retires the finite prime-log incidence route rather than promoting a local
  shape match into a false global mechanism.  It isolates the required new object as a genuinely
  non-factorwise completed extension datum, not a different summation rule for local orders.
- **SELF-ATTACK:** The last paragraph is an open specification, not an existence claim.  No
  completed obstruction class has yet been constructed.
- **FLOW TEST:** Every proved statement is pinned at fixed rates and a fixed strip point.  No cutoff
  parameter, transport, or limiting family appears.

## Gates

- [x] 0 -> 1: rate congruence, exact nonnegativity gate, and finite-source test stated.
- [x] 1 -> 2: paper proofs of invertibility, congruence, activation equivalence, divisor mismatch,
  and the universal pointed-assembler no-go.
- [x] 2 -> 3: theorem family formalized in Lean with targeted module and axiom checks.
- [ ] 3 -> 4: construct or decisively rule out the fixed completed obstruction in the open core.
