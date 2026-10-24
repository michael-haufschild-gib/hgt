# Carry additive characters through the Route-T receiver

- **ID:** twin-prime-character-route-t-receiver
- **Stage:** 1-in-progress
- **Type:** FORMALIZATION TARGET / BRIDGE
- **Source:** [character-uniform nonpretentiousness](twin-prime-character-uniform-nonpretentiousness.md).
- **Statement:** Retain arbitrary additive frequency in the actual logarithmic-phase receiver, then derive a uniform bound for periodic Dirichlet-character coefficients.

## Exact first target

Extend `norm_routeTZetaBlockSum_le_explicitQuarticSaving` to

```text
sum_(X<n<=X') n^(-sigma) exp(i*t*log n + 2*pi*i*alpha*n),
```

for every real `alpha`, with precisely the same right-hand side

```text
6912 X B^(-1/(5000000000000000*v^4)) (X+1)^(-sigma),
B = routeTLogRootBase(X)^routeTLogCentreExponent,
```

and the same arithmetic domain:

```text
1 <= X < X' <= 2X,
0 <= sigma,
2^(routeTLogCentreExponent *
   (routeTLogReceiverDegreeNineConstant *
      (routeTLogRealShellIndex(X,t)+1)^9 + 1)) <= X,
B^(4*141) < t <= B^(4*v).
```

No estimate on the actual sum or on a character enters as a
premise. The displayed conditions only define the scale and
frequency range in which the receiver applies.

## Inspected reuse

`RouteTZetaBlock.lean` transfers the actual negative logarithmic
phase to `MontgomeryVaughanArbitraryLogPhaseReceiver.lean` by
conjugation and exact complex-power identities.
`MontgomeryVaughanLogPhaseReceiver.lean` proves
`routeTLogPhase_receiver_inequality` using
`norm_mvCoefficientBlockSum_mul_mvPhaseBlockSum_le`.
Its only oscillatory input is
`norm_routeTLogTwistedShiftBilinearSum_le_two_rpow_of_shell`,
already uniform over every real linear frequency `beta`.

The proposed transport is the exact identity, on the product
multiplicity's support `k<r`,

```text
e(alpha*(r-k)) e(beta*k) = e(alpha*r) e((beta-alpha)*k),
e(u)=exp(2*pi*i*u).
```

The outside factor has norm one. The existing all-`beta` bound
therefore suggests the same receiver cost. Unlike a direct
change of the amplifier coefficients, this substitution should
preserve the positive amplifier mass. The natural-number
subtraction requires the actual support inequality; it must not
be rewritten as integer subtraction away from that support.

## Remaining proof obligations

1. Verify the exact finite convolution identity on all supported
   indices, including zero multiplicities outside the support.
2. Carry the identity through the receiver and the arbitrary
   center/root-cell and Abel-weight passages with unchanged constants.
3. Prove the finite additive Fourier assembly for the actual
   periodic character and retain its coefficient-norm cost.
4. Only then derive character L-function growth, a uniform
   zero-free region, and the twisted prime-tail estimate.

**[OPEN CORE]** The actual character analytic assembly in step 4.
The receiver transport itself has not yet been completed on
paper or in Lean. This card introduces no assumed growth bound.

## Attack and rate boundary

Verdict **BRIDGE**. Fourier modulation and the classical
Montgomery–Vaughan receiver are established mechanisms; no
scientific novelty is claimed for this transport.

The current Route-T strip has exponent `9/10`. Even a successful
character transport at that exponent would not by itself supply
the `1/4 log log N` distance needed by the proposed simplification
of Appendix A. The proof must either strengthen the region or
retain the source's near-resonant branch. Parameter choices and
decay rates must be audited before selecting either continuation.

## Gates

- [x] Exact target and source declarations identified and inspected.
- [ ] Dependency-closed paper proof of the actual additive receiver.
- [ ] Lean receiver transport and own umbrella import.
- [ ] Actual periodic-character Fourier assembly and axiom audit.
- [ ] Character analytic growth and twisted prime-tail theorem.
