# BAG full tangential profile and complete integer defect action

- **Stage:** 3-formalized

Route: signed physical BAG cubic. All three leaves pass production and standard-axiom audits.
No signed saving or RH.

## Full tangential fibre [PAPER PROVED; LEAN PRODUCTION PASSES]

For prime p, A=1-1/p and b(a)=1_(a=0)-1/p on F_p. For ANY complex
H(a,b), push the signed mass b(a)b(b)H(a,b) through d=a*b.
At d=0 the two coordinate axes intersect once, giving exactly

    A^2 H(0,0)-A/p*(sum_(u!=0) H(u,0)+sum_(u!=0) H(0,u)).

For d!=0, every point has a unique nonzero a=u and b=d/u. Both base
coefficients are -1/p. Hence the full fibre equals

    p^-2 * sum_(u in F_p^*) H(u,d/u).

Finite regrouping pairs this law with EVERY defect test Phi(d), retaining
both axes, intersection and every nonzero inverse fibre. The previous
product-only identity is a special case; H is not replaced by a constant.
The exact prime-square base reduction from the prior leaf attaches this
law to every literal prime-square node at physical prime frequency.

Use the unnormalized two-variable finite Fourier transform Hhat(m,n).
Applying one-variable inversion in each coordinate gives

    H(a,b)=p^-2 sum_(m,n) Hhat(m,n)*e((m*a+n*b)/p).

On the inverse curve, finite summation yields

    sum_u H(u,d/u)=p^-2 sum_(m,n) Hhat(m,n)*S(m,n*d;p).

This retains BOTH tangential frequencies and their zero modes. S is the
corpus's actual complete Kloosterman sum. No spectral or cancellation
hypothesis appears. Existing fixed-modulus norm p alone does not provide
the required growing signed estimate.

## All integer defect coordinates [PAPER PROVED; LEAN PRODUCTION PASSES]

For positive integer Q and any integer shift numerator s, the map

    A=Q*k1-s1, B=Q*k2-s2,
    D=Q^2*k3-Q*s3+A*B

is a bijection from Z^3 to triples satisfying

    Q | A+s1, Q | B+s2, Q^2 | D-A*B+Q*s3.

The inverse is given by the three exact integer quotients. The physical
node is (A/Q,B/Q,(D-A*B)/Q^2), so its transverse defect is EXACTLY D/Q^2.
This is the full shifted lattice, not a bounded defect range. Reindexing
preserves the proved absolute Fourier lattice summability for every
Schwartz amplitude. For the actual amplitude, the exact transverse phase
is exp(-2*pi*i*r*D/Q^2), with the full two-coordinate transition and entire
physical-window Mellin line unchanged. The lattice sum remains outside
the r integral; no unproved sum/integral interchange is taken.

## Both contraction projectors and actual source [PAPER PROVED; LEAN PRODUCTION PASSES]

At a common grid denominator Q, a translation by u/D0 in direction(1,0,-1)
and v/D0 in direction(0,1,-1) has denominator L=Q*D0 and numerator

    (D0*s1+Q*u, D0*s2+Q*v, D0*s3-Q*u-Q*v).

Apply the complete defect bijection separately to the unshifted term,
both single averages and the double average. Their signed combination
is exactly the original noncontracting projector, including its mixed
term. The extra projector denominator D0 remains explicit.

For the literal critical atoms Q=rad(P)^2. The integer numerator before
modular reduction is a1*(Q/d1)+a2*(Q/d2^2). Since both denominators divide
Q, its quotient by Q is exactly the original atom node. The triple tensor
therefore attaches every critical atom to the projected integer-defect
sum. Every original weight, atom, lift and contraction is retained.
The existing actual Schwartz cutoff family then gives this action equal
to the smoothed physical cubic and preserves the ORIGINAL negligible
sharp/smooth error. No congruence or product formula is called a saving.

## Hard gap

A signed growing estimate for this exact action is still needed. The
local weighted inverse-fibre law must be joined to the full lifted,
projected source with all remaining prime factors. No uniform CRT/cofactor
estimate or absolute interchange with the r integral has been proved.
Full pole/near-cone/tail coupling at complex norm o(N/log^2 N), growing
moments, moving cofactors, common-height self-return and RH remain open.

## Lean audit — continuation01ai

ChiRamanujanTransverseProfileFibres:181 lines/10 public declarations,
production82029 empty. ChiPrimeGaussianCubicIntegerDefect:166 lines/15 public,
production8278 empty. ChiPrimeGaussianCubicDefectAction:10 public,
production91163 empty. Combined axiom57927 checks all35: no proof debt or
added axioms; only propext, Classical.choice and Quot.sound. Every import
occurs once in RHTower. Index38355 completes; API refreshed. Lint22402 has24
unrelated unreachable modules, inspected; no finding in these leaves.
Global lint is not clean. Audit logs remain under /tmp/*01ai.log.

Searches68221/4633/60369: nonpartial65796/65796/65798, noerrors;
background refresh incomplete and compiler metadata mostly pending/source_only.
All20 candidates and20 source arguments per search, ingredients/ideas read.
The principal-unit quotient lift and Fourier-Borel annulus ingredients are
unrelated to the physical defect problem and were rejected. Useful mechanisms
were finite Fourier inversion, actual Kloosterman units, full Schwartz lattice
summability and shifted Poisson. Candidate applicability verified in Lean.

Assessment: exact full-profile arithmetic and full projected integer action
are closed. Uniform signed cancellation is not. Next attack is partial
Poisson in the third lift followed by its actual prime-r source, keeping both
tangential frequencies. Existing post-integral absolute Fourier summability
cannot justify a pre-integral lattice exchange. Goal remains ACTIVE.

## Lean certificate (2026-10-08 promotion audit)

Every claim of this card was re-read against the public statements below; each statement
is unconditional (structural domain subtypes only, no analytic or arithmetic premise).

| Module | Public theorems |
|-|-|
| `GaloisForLFunctions.RHTower.ChiPrimeGaussianCubicDefectAction` | `bagCriticalAtomNumerator_node`, `bagCriticalTripleNumerator_node`, `bagCriticalDefectAction_eq`, `primeGaussianCubicSmoothedOffDiagonal_eq_defectAction`, `exists_bagCompleteIntegerDefectFamily` |
| `GaloisForLFunctions.RHTower.ChiPrimeGaussianCubicIntegerDefect` | `bagDefectNode_equiv`, `bagDefectNode_defect`, `summable_norm_bagDefectLiftedTest`, `bagDefectLiftedTest_eq`, `bagDefectNode_physical`, `bagProjectedNumerator_shift`, `bagProjectedDefectTest_eq` |
| `GaloisForLFunctions.RHTower.ChiRamanujanTransverseProfileFibres` | `criticalProfileFibre_zero`, `criticalProfileFibre_eq`, `criticalProfile_pairing`, `criticalProfileFourier_inversion`, `criticalProfileInverse_kloosterman`, `criticalGridBase_profile_pairing` |

- `lake env lean <module source>`: every module above compiles with no errors (2026-10-08).
- Axiom audit: every declaration of these modules (643 declarations across the 83 BAG modules)
  depends only on `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx`.
- Each module is imported exactly once in its area umbrella (`RHTower.lean` / `HTGeometry.lean`).
- Open targets recorded on this card (route-level obligations, RH) are not claimed.

## Log (promotion)

- 2026-10-08 — promotion audit passed; moved from `2-fully-proven/route BAG` to `3-formalized/route BAG`.
