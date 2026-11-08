# Exact-event theory of Euler products

## Motivation

An Euler product controls a Dirichlet series where it converges absolutely. Its functional
equation relates opposite sides of the critical line. Neither operation alone explains why
one zero should force zeros at arbitrarily large heights. This programme studies that missing
interaction for the continued, infinite Euler product.

For ζ, write Θ for the supremum of zero real parts and Θ∞ for the corresponding supremum
after arbitrary finite-height deletions. The asymptotic abscissa law (AAL) is Θ = Θ∞.
Its failure is an isolated finite top layer over an infinite remainder. The target is to
exclude such a layer using arithmetic, or construct one within a precisely specified class
of Dirichlet series with Euler product and functional equation.

## Objects and language

- An **exact event** is a zero of the continued Dirichlet series, equivalently a zero of
  every Euler tail at that point. A small value is an approximate event, not an exact one.
- At prime cutoff y, the Euler head E_y is nonzero in Re s > 0 and the continued tail is
  ζ/E_y. Exact cancellation is ζ−E_y = −E_y, including phase.
- **Transport** sends a zero to unbounded heights with arbitrarily small loss in real part.
  **Recurrence** concerns translates of functions; **zero-disc control** concerns their
  behavior around a particular zero. Neither word presupposes an arithmetic theorem.
- The **dial** records Θ, Θ∞ and the linear bounds
  Θ−½ ≤ C(Θ∞−½). Exceptional rank counts the finite modes above a chosen remainder.
- Prime phases, vertical translates, and conditional Euler tails must be studied together.
  An average over the prime torus does not by itself describe an exceptional orbit event.

## Mechanisms to investigate

1. Local analytic stability: identify precisely which boundary information preserves a
   zero and whether arithmetic supplies it along unbounded vertical shifts.
2. Vanishing targets: separate approximation of a zero-bearing function from universality
   for nonvanishing targets. Identify the compactness or noncollapse needed at this boundary.
3. Euler–functional-equation coupling: compare reflected and translated tail events without
   freezing a head whose length grows beyond the recurrence scale.
4. Exceptional-rank rigidity: combine finite top oscillations, positive annihilators and
   their oscillating inverses with information from the infinite remainder.
5. Relative thick counts: connect an arithmetic bound at the remainder's exponent to a
   fixed linear slope, then determine whether that slope can approach one.

## Foundations already available in the corpus

These are inherited results, not contributions claimed by this programme.

| Foundation | Mathematical role |
|---|---|
| AAL iff zero transport iff Euler-tail transport | Exact-event target |
| Near-full cancellation has positive lower density | Explains why η > 0 is insufficient |
| Uniform recurrence with local holomorphic control transports zeros | Analytic receiver; arithmetic recurrence remains to prove |
| Strict linear dial and finite-rank Chebyshev exponent | Quantifies intermediate goals |
| Finite Euler product plus appropriate FE forces local squares | Finite-rank calibration, not the infinite theorem |
| Two-scale blindness, precision cap, positive one-offs | Tests for invalid proposed mechanisms |

New pillar theorems must be stated here only after their exact Lean statements and transitive
axioms have been checked. No new pillar theorem is asserted in this initial foundation.

## Tools and questions

| Required tool | Question it must resolve |
|---|---|
| Weak recurrence with zero-disc control | Which arithmetic recurrence can transport a zero without uniform almost periodicity in the strip? |
| Exact-tail existence theorem (B96) | What supplies an event at η = 0 rather than a density estimate for η > 0? |
| FE-to-transport principle (B112) | How can height reflection and Euler arithmetic jointly produce new heights? |
| Relative thick crude count (B116) | Can a bound tied to Θ∞ force a finite slope, and ultimately slope one? |
| Finite-layer exclusion over an approaching remainder (B111) | Does Θ∞ = ½ force Θ = ½? |
| Euler–FE finite-layer classification (B103, B84) | Which precisely defined classes admit a finite layer; what FE defect is necessary? |
| Shift-family stability | Does the trivial linear slope remain bounded as the shift tends to zero? |

All questions in this table remain open here. An implication assuming its missing arithmetic
input does not count as construction of the required tool.

## Traps and calibration

Positive-density near-cancellation does not supply exact cancellation. Convergence of small
values need not retain a nonzero analytic limit. The functional equation preserves absolute
height. A fixed Euler cutoff is a nonvanishing multiplier and cannot remove a zero. Absolute
convergence cannot be silently extended into the critical strip.

Every proposed transport mechanism must recover Bohr recurrence in its domain and the curve
and exponential-polynomial cases. Its arithmetic input must distinguish ζ from the relevant
cosh, heat, Beurling one-off, harmonic-depth, one-pair and Wolff calibrations. AAL must respect
vertical shifts. A line-dependent claim must explain its use of the FE involution and Hardy
zeros. Quantitative improvements with no effect on an open input are not contributions.

## Position in the wider research

TailArithmeticOfThePrimeOrbit supplies Euler heads, tails and exact cancellation.
ArithmeticInnerFunctionTheory studies recurrence and analytic rigidity.
ZeroConfigurationGeometry supplies transport, the dial and separating configurations.
InfiniteRankWeilTheory translates the dial into finite-rank prime-error and thick-tower laws.
ArithmeticPositiveDuality supplies Euler–FE calibrations, annihilators and surgery obstructions.
ArithmeticCastelnuovoSeveri and ArithmeticOrientationGeometry supply the curve comparison and
the count/positivity receivers. ExactEventTheory must provide arithmetic existence or rigidity
inputs for these receivers, rather than duplicate their equivalent formulations.

## Contribution and success criteria

Each module must prove a nontrivial theorem about the infinite problem, identify which open
input it advances, and distinguish its contribution from existing corpus results. A negative
result must expose and formalize its strongest positive survivor. Proofs must be dependency
closed, kernel checked, and free of unproved arithmetic assumptions or numerical evidence.

The programme is complete only when the original tools and questions above are resolved,
with the scope of every classification specified and all asserted proofs formalized. AAL,
ZAL ⇒ RH, and Euler–FE finite-layer exclusion are not asserted as established.
