# Arithmetic parity as reversal of the RH damping parameter

- **ID:** goldbach-damping-reflection-parity
- **Stage:** 3-formalized
- **Type:** BRIDGE; structural reformulation, no scientific novelty claimed
- **Source:** the actual divisor source and its squarefree tangent in `goldbach/RiemannHypothesisBridge.lean`; the user's request to work in the RH programmes' mechanisms.
- **Constraint:** no unproved analytic estimate may enter a Lean statement as a premise. The original Goldbach theorem remains the completion criterion of the main goal.

## Previous turn classification

Progress: authoritative Lean source now contains checked unconditional
Goldbach equivalences using the actual damped divisor source, reflection
defect, parity energies and SAEI incidence energy. The closures were audited.
This completes the requested language bridge; it does not complete the
original Goldbach goal.

## Exact structural candidate

Use the existing squarefree, unit-removed source a_ε(k). For every k and real ε,

    a_{−ε}(k) = μ(k) k^ε a_ε(k).                         (1)

After the symmetric gauge b_ε(k)=k^{ε/2}a_ε(k), this becomes

    b_{−ε}(k) = μ(k)b_ε(k).                              (2)

Thus its odd part in the damping variable,

    o_ε(k)=(b_ε(k)−b_{−ε}(k))/2,

is exactly the squarefree negative-Möbius source. Arithmetic factor-count
parity is the reflection ε↦−ε of the same damped source. This transports
the sign problem into the hyperbolic-multiplier and continuation languages
without assuming cancellation.

## Dependency-closed finite paper proof

On the retained support k is squarefree and greater than one. Its prime
factors form a finite set P, k=∏_{p∈P}p and μ(k)=(-1)^|P|. In each factor,
1−p^ε=−p^ε(1−p^(−ε)). Multiplication proves (1). Multiplying by k^(−ε/2)
and combining real powers proves (2). Off the retained support both sides
vanish. Consequently

    b_ε(k)=∏_{p∈P}2sinh(ε log p/2),
    o_ε(k)=b_ε(k) when |P| is odd, and 0 when |P| is even.

The first derivative is the actual prime logarithmic weight; the gauge
has value one at zero and the original projected source vanishes there.
Taking its odd part preserves this derivative. Finite multiplication
and summation therefore give, for each fixed N,

    lim_{ε→0, ε≠0} Σ_{k+l=N}o_ε(k)o_ε(l)/ε² = G(N).   (3)

The overlap is even in ε. The leading coefficient is the same weighted
Goldbach count already identified by the checked unsymmetrized tangent
bridge. No damping/horizon limit exchange is used.

## Attack and useful boundary

The normalized odd overlap has nonnegative Taylor coefficients; for positive
ε it increases rather than supplying a decreasing upper envelope. Positive
overlap at one positive damping cannot force a positive quadratic coefficient:
higher odd factor-count layers also contribute. Analytic continuation as an
identity is therefore distinct from a bound on its backwards or odd part.

The new task is to derive actual control of this odd reflected source, keeping
the target N. It is not to assume a continuation estimate or to claim that
positivity of the whole finite product proves positivity of its first layer.
No route is retired merely because an estimate remains open.

## A finite two-scale certificate

Write O_N(ε)=Σ_{k+l=N}o_ε(k)o_ε(l). The hyperbolic product gives the exact
doubling law

    o_{2ε}(k)=D_ε(k)o_ε(k),
    D_ε(k)=∏_{p|k}2cosh(ε log p/2) ≥ 2^{ω(k)}.

For positive ε the odd source is nonnegative. Every nonzero endpoint has
negative Möbius sign and at least one prime factor. If such an endpoint is
composite, squarefreeness and negative sign force at least three factors.
Consequently every supported pair except a prime pair amplifies by at least
16 when damping doubles. This proves, for every N, the exact equivalence

    N has a prime pair  ⇔  ∃ε>0, O_N(2ε)<16 O_N(ε).      (4)

The reverse implication sums the amplification bound under absence of a
prime pair. For the forward implication the checked tangent limit gives
O_N(ε)/ε²→G(N)>0 and O_N(2ε)/ε²→4G(N); hence
(16O_N(ε)−O_N(2ε))/ε²→12G(N)>0. No uniformity in N is needed for this
equivalence. Equation (4) is a finite two-scale restatement: proving its
strict inequality for every even target is still required.

The sharper quartic remainder and decreasing quantitative minorant are
proved separately on the [coefficient-extraction card](../../2-fully-proven/goldbach-odd-damping-extraction-minorant.md).
Those paper-level refinements are not included in this card's Lean claims.

## Scale audit for the next analytic attack

Undo the gauge and put v_ε(k)=exp(−ε log k/2)o_ε(k), with overlap V_N.
This is exactly the negative-Möbius part of a_ε, as in the earlier C3
weight. On a supported pair (k,l), doubling multiplies its weight by

    (kl)^(−ε/2) D_ε(k)D_ε(l).

For ε>0, a pair containing a composite therefore amplifies by at least
16N^(−ε), since k,l≤N. A prime pair amplifies by
(1+p^(−ε))(1+q^(−ε))≤4. This uniform comparison separates the two
classes only in ε log N<log 4. It explains exactly why a fixed-positive-
damping mass estimate cannot simply be substituted into this argument:
the useful range shrinks with the target. The next analytic estimate must
retain that joint scale, as well as the squarefree and odd-sector masks.
This scale audit is paper-level and supplies no missing lower bound.

## Verification status

- Corpus audit found the exact Euler product, squarefree Möbius sign law,
  hyperbolic dyadic defect, and existing RH parity-pair constructions. The
  inspected results do not already state this damping reversal and its
  Goldbach two-scale certificate. No claim of external novelty.
- Finite identities (1)–(3) and equivalence (4) formalized in
  [RiemannHypothesisBridge.lean](../../../../../formal/GaloisForLFunctions/goldbach/RiemannHypothesisBridge.lean).
- Direct check: `lake --old env lean GaloisForLFunctions/goldbach/RiemannHypothesisBridge.lean`
  from `formal/`, exit 0, no warnings.
- Six dependency closures audited with `#print axioms`: only `propext`,
  `Classical.choice`, `Quot.sound`. Audit directives removed; proof bodies unchanged.
  Log: `/tmp/hgt-goldbach-damping-parity-audit.log`.
- No analytic input or conjectural premise added.
- The original all-even Goldbach positivity estimate remains unproved.

## Lean declarations

- `squarefreeDampedSource_neg`
- `symmetricDampedSource_neg`
- `symmetricDampedSource_eq_prod_sinh`
- `oddDampedSource_eq_negativeMoebius`
- `hasDerivAt_oddDampedSource_zero`
- `tendsto_oddDampedReflectionOverlap_div_sq`
- `oddDampedSource_two_mul`
- `primeFactorPower_le_dampingDoublingMultiplier`
- `tendsto_oddDampedDyadicDefect_div_sq`
- `primePair_iff_positive_oddDampedDyadicDefect`
- `goldbach_iff_positive_oddDampedDyadicDefect`

The first, third, fourth, ninth, tenth and eleventh declarations above
were the six audited closures. The finite criterion quantifies over all
natural targets; the final theorem specializes it to every even target
at least four. The [finite minorant and dyadic compensation](goldbach-finite-damping-bracket.md)
are now formalized. The scale audit and full coefficient-series refinement
remain explicitly paper-only.
