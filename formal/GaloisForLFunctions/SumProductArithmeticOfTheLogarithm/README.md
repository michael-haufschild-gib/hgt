# Sum-product arithmetic of the logarithm

Namespace `GaloisForLFunctions.SumProductArithmeticOfTheLogarithm`;
umbrella `SumProductArithmeticOfTheLogarithm.lean`.

## Motivation

The phase `φ_t(n) = t log n` has two simultaneous structures: multiplication of
integers becomes addition of phases, while translation of integers produces a
smooth, curved phase. This programme studies their compatibility at one fixed
height, retaining the integer winding numbers lost on passage to the circle.
Its source is §2.9 of [Obstacles summary](../../../docs/reports/review-0711/obstacles-summary.md).

The intended arithmetic input uses neither positivity of a quadratic form nor a
self-adjoint operator. Exact identities alone do not exclude a zeta zero: the
cut calculus already annihilates every zero mode. A useful new input must bound
an actual count, phase concentration, or carry distribution.

## Objects and language

* **Phase level set:** integers in an interval whose `t log n` lie in a prescribed
  arc modulo `2π`. The location of the arc and the height are part of the data.
* **Shifted product signature:** products of a tuple before and after integer
  translations. Simultaneous coincidences couple addition to multiplication.
* **Mixed collision count:** number of tuples with equal product signatures.
  This is a combinatorial count, without a quadratic-form sign assumption.
* **Winding:** the integer removed when reducing a real phase modulo `2π`.
  **Carry:** the correction to winding under an addition or multiplication law.
* **First return:** least height at least one aligning the primes below a given
  cutoff to prescribed precision. An upper bound and a lower bound are different
  problems; recurrence by itself supplies no exclusion.
* **Finite oscillation:** the trigonometric leading term in a putative finite
  layer of right zeros. A contradiction must use more than its exact dilation
  annihilator.
* **Count distance:** discrepancy between the integer counting functions of
  two Beurling systems, with exponent as well as amplitude retained.

## Mechanisms and foundational questions

Two translated product readings can recover information absent from either
reading alone. The initial algebraic question is to classify their common
fibres, then establish quantitative separation of different fibres. The
analytic question is whether the winding numbers can be controlled at the
precision required to transfer that separation to a fixed height.

The integer gap makes distinct products distinguishable at inverse-product
resolution. Translation exposes coefficients of the polynomial
`∏ᵢ(X + nᵢ)`. Carries record the difference between an exact real identity and
its reduction modulo a period. These mechanisms must be combined with counts
of actual integers, rather than arbitrary torus points.

## Tools and open research topics

| Required tool | Mathematical target |
|---|---|
| Energy beyond diagonal moments | Bound simultaneous shifted-product concentration of actual phase level sets, including nonzero windings. |
| Exponential sums beyond the polynomial barrier | Savings for `t log(n+h)` when the necessary Taylor degree exceeds `(log length)²`. |
| Carry contradiction for finite oscillations | Decide whether the rigid finite-zero asymptotic can coexist with `N(x)=⌊x⌋`. |
| Effective Kronecker in both directions | Quantitative return bounds that retain the start of the height orbit. |
| Beurling metric geometry above the isolation gap | Determine the smallest count distance carrying an exceptional zero, beyond the known deletion-exponent obstruction. |

Four questions organize the programme. What information survives when a dilation
is written as an average of translations? Which density and interval-length
conditions make small-arc concentration constrain the height? Can carries rule
out a single off-line zero? What count distance is necessary and sufficient to
insert one among integer-norm systems? The small-arc question needs an explicit
dependence of cutoff on height. Even an entire fixed finite interval returns
arbitrarily close to alignment at arbitrarily large heights, by simultaneous
Dirichlet approximation. Thus the target concerns the first return as the
cutoff grows, or exclusion in a specified initial height range.

## Relation to the corpus and calibration

**PrimeTorusTheory** supplies integer-log separation, finite-time recurrence,
non-alignment estimates, and the word/polynomial-phase ceilings. This programme
asks for information involving translations of the integer argument.
**RigidArithmeticOfCuts** supplies exact carries, dilation averages, zero-mode
blindness, parity/strip equivalence, and Beurling isolation. Its exact identities
are boundary conditions for a new inequality, not the inequality itself.
**ArithmeticCastelnuovoSeveri** and **ArithmeticOrientationGeometry** explain the
spectral receivers and impure models; their positivity mechanisms are outside
this programme's allowed inputs.

Finite-field calibration must recover Hasse–Weil in counting language through
Stepanov, including the scope of the existing split-hyperelliptic theorem.
Further tests are Burgess, smooth moduli and depth aspect, continuous Beurling
systems without integer carries, and the Golden discrete model. A theorem about
all integer sets alone cannot distinguish rational primes from a different
integer-norm system; that distinction also requires the prime amplitude.

The distinction between integer counts and Beurling systems is essential.
`RigidArithmeticOfCuts/ABoundedCountWithANewZero.lean` gives nonnegative integral
multiplicative coefficients with bounded count error and new right zeros.
Its Euler generators have negative multiplicities, and its added zeros form
vertical progressions. It supplies neither a positive-generator Beurling
counterexample nor a single exceptional zero pair.

## Traps and success criteria

Multiplicative energies of additive shifts already belong to classical
sum-product theory; see [Rudnev–Shkredov–Stevens](https://arxiv.org/abs/1607.05053).
Moreover, arbitrarily large real sets can have both `AA` and `(A+1)(A+1)`
of size `O(|A|^{2-c})` for a fixed `c>0`, by
[Roche-Newton–Schildkraut–Warren](https://arxiv.org/abs/2606.24583).
Thus near-quadratic growth of one projection is not a general real-set
principle. Any proposed improvement must state its integer and phase inputs.

An exact collision classification is foundational algebra, not a fixed-height
cancellation theorem. Small real phase difference and small difference modulo
`2π` must never be interchanged. Diagonal moments, one word, and one Taylor
polynomial have proved ceilings. Complete multiplicativity makes an untreated
Type II factorization empty. A power-saving parity claim must expose its
zero-free-strip consequence. Typical-height information does not exclude an
exceptional height or a finite exceptional zero set.

A contribution must state an unconditional theorem, identify the arithmetic
input and the quantitative range, give its exact Lean declaration, and explain
what it adds beyond existing corpus results. Foundational identities are labeled
as such. A claimed advance on the open core must improve a named estimate or
exclude a named obstruction and must survive the relevant fake-model tests.

Completion requires the five tools above, answers to the four organizing
questions, finite-field calibration, and an explicit strip output for any
power-saving parity mechanism. Establishing only algebraic foundations does
not complete this programme. No improvement beyond Vinogradov–Korobov or
exclusion of a finite right-zero layer is currently asserted here.
