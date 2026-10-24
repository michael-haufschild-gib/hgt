# Actual character-uniform Liouville distance

- **ID:** twin-prime-character-uniform-nonpretentiousness
- **Stage:** 1-in-progress
- **Type:** FORMALIZATION TARGET / BRIDGE
- **Source:** [actual short Fourier estimate](twin-prime-short-fourier-formalization.md).
- **Statement:** Prove the actual Liouville pretentious-distance lower bound uniformly over the required growing moduli and frequencies.

## Exact target

For a positive modulus `q`, a complex Dirichlet character `chi`
modulo `q`, and real `t`, define the actual finite prime sum

```text
D(N,chi,t) = sum_(p<=N, p prime) [1 + Re(chi(p) p^(it))]/p.
```

Prove absolute `C>0` and `N0` such that, for every `N>=N0`,
every `q <= (log N)^(1/125)`, every such character, and
every `|t|<=N`,

```text
D(N,chi,t) >= (1/4) log(log N) - C.
```

The modulus/frequency ranges are the domain of the conclusion.
No distance estimate, zero-free region, cancellation condition,
or unproved character-uniform constant may enter as an assumption.
The identity with the distance of the actual Liouville row must
also be certified using `lambda(p)=-1` at primes.

This is a weaker instance of (1.12) in
[Matomäki--Radziwiłł--Tao](https://arxiv.org/pdf/1503.05121v3),
not a new scientific conjecture. Verdict **BRIDGE**.
It is sufficient eventually to exceed the `1/8 log(log N)`
threshold used to remove Appendix A's near-resonant branch.

## Newly located corpus inputs

The initial searches did not surface the relevant files. Following
the exact imports of `DirichletLLogStrip` located these actual results:

- `RHTower.norm_LFunction_le_log` in `DirichletLLogStrip.lean`:
  `|L(sigma+it,chi)| <= K(q) log|t|`, where
  `K(q)=(2+6q)e+17*2^(omega(q))`. The modulus dependence is explicit.
- `DirichletCharacter.norm_LFunction_product_ge_one`:
  the actual principal/character/squared-character 3-4-1 product.
- `RHTower.norm_LFunction_lower_log_strip` in
  `DirichletLLogDerivativeStrip.lean`: a quantitative floor on a
  strip of width `a(q)/log^9|t|`, with
  `a(q)=1/(4*32^4*K(q)^8)`.
- `RHTower.exists_norm_inv_LFunction_le_log_pow` in
  `DirichletLReciprocalRightOfTheOneLine.lean`: reciprocal growth
  `C log^7|t|`; its displayed proof gives explicit dependence on
  `K(q)` and `a(q)` at large heights. Its bounded-height compactness
  theorem has character-dependent constants and cannot be used
  uniformly without another argument.
- `RHTower.siegel_LFunction_one` and `RHTower.siegel_zero_free`:
  unconditional power bounds for nonprincipal quadratic characters,
  uniform in modulus with a fixed exponent. The constants are
  ineffective; this does not prevent an unconditional existence
  theorem, but no effective constant is claimed from that route.

The capstone statements and relevant source proofs were inspected.
All six selected inputs passed a transitive axiom audit containing
only `propext`, `Classical.choice`, and `Quot.sound`. Existing modules
were imported for that audit, not rebuilt. The complete analytic
assembly below has not been proved.

## Exact missing work

1. The [finite 3-4-1 assembly](../3-formalized/twin-prime-character-quarter-distance.md)
   is now fully formalized and axiom-audited. Direct
   primewise positivity removes the principal pole cost: the
   bound loses only `(1/4)log q`, and gives coefficient `6/125`
   when `log|t| <= (log N)^(4/5)` in the required modulus range.
   Its Euler-logarithm, tail, and shift errors are absolute.
2. Pay bounded heights using the actual character estimates;
   finite-modulus compactness alone is insufficient as `q` grows.
3. Prove the high-frequency twisted prime-tail estimate. The
   available logarithmic strip has exponent nine and does not by
   itself reach the required range. The corpus's stronger Route-T
   result is currently stated for zeta; no character-uniform
   extension has yet been checked.
4. Assemble the actual finite sum and prove all threshold choices
   uniformly in the stated modulus and height ranges.

**[OPEN CORE]** Step 3, together with uniform assembly of Step 2.
The `1/4` full-frequency target is not a theorem of this project yet.
The exact next receiver task is recorded in the
[character Route-T card](twin-prime-character-route-t-receiver.md).

### High-frequency source inspection

Following the actual Route-T import graph leads to
`RouteTZetaBlock` and `MontgomeryVaughanArbitraryLogPhaseReceiver`.
Their bounds concern the literal logarithmic phase at arbitrary
integer centers; they do not currently provide a Dirichlet
character twist. Inspection of `routeTLogPhase_receiver_inequality`
found a more specific reusable input:
`norm_routeTLogTwistedShiftBilinearSum_le_two_rpow_of_shell`
already permits every real linear frequency. In the convolution
slice, adding `alpha*n` to the original phase should factor out
`exp(2*pi*i*alpha*r)` and replace the receiver frequency `beta`
by `beta-alpha`. This suggests no new Taylor estimate is needed.
The exact finite-support identity and its substitution into the
receiver still need proof. Then finite additive Fourier expansion
of the periodic character should pay its Fourier coefficient norm.
No character growth or zero-free theorem is claimed from this
inspection alone.

The existing Route-T envelope has exponent `9/10`. Extending it
alone would not establish the source's `1/4` distance target by
the tail-mass argument: even an optimized tail cutoff would
retain less than `1/10` of `log log N`. A weaker global distance
would require retaining and formalizing Appendix A's near-resonant
branch, or a stronger character-region theorem must be proved.

If a weaker distance is pursued, its effect on the final Fourier
rate must be paid explicitly: Theorem 1.7 contains `exp(-M/20)`.
The plain-row coefficient `0.01` alone would yield exponent
`1/2000`, not the requested `1/700`. It also does not remove
the near-resonant branch at the source's stated threshold.

## Gates

- [x] Exact actual-row statement and external parent identified.
- [x] Relevant corpus character estimates located and statements checked.
- [x] Transitive axiom audit of selected existing inputs.
- [x] Complete paper and Lean proof of the middle-frequency assembly.
- [ ] Complete dependency-closed paper proof of full-frequency assembly.
- [ ] Lean proof of the actual target and all necessary inputs.
- [ ] Foreground leaf check and own umbrella import.

## Log

- 2026-10-24 — Located explicit character logarithmic-strip and
  Siegel inputs while closing the short-window endpoint certificate.

- 2026-10-24 — Formalized finite character 3–4–1 positivity, the
  absolute Euler comparison, the quarter modulus loss, and the
  actual middle-frequency Liouville distance. Nine capstones
  passed standard-foundation audits; the foreground leaf passed
  without warnings and its umbrella import is present.
