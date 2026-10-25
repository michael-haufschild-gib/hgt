# Regularly varying energy with a nonstationary covariance phase

- **ID:** biarithmetic-logarithmic-chirp-tangents
- **Stage:** 1-in-progress
- **Type:** CANDIDATE (Lean formalization incomplete)
- **Proof status:** Only statements with completed Lean checks and axiom audits are proved. Paper arguments below are proof plans; every significant claim remains a formalization obligation.
- **Parent:** [Biarithmetic Geometry](../1-in-progress/biarithmetic-geometry-foundations.md), A3.
- **Statement:** A smooth real scalar row with bounded increments and regularly varying pronic energy has a compact family of infinite-rank cofactor tangents, none individually homogeneous. The family has exact dilation transport, an explicit positive boundary-loss identity, and a stationary diagonal average.

## Proposed source and exact candidate family

Fix `1/2<β<1`, put `α=2β-1`, and define `v(0)=0`,
`v(n)=n^β cos((log n)²)` for positive integers. Its derivative on the positive line is
`x^(β-1)[β cos((log x)²)-2 log x sin((log x)²)]`, tending to zero at infinity.
The derivative tends to zero and is bounded on every compact subinterval of `[1,∞)`.
The mean-value theorem, together with the first increment, proves bounded integer increments.

The pronic energy has asymptotic

`E(T)=Σ_(n=1)^T v(n)²/(n(n+1)) ~ T^α/(2α)`.

For fixed positive integers `j,k`, put `a=log j-log k`, `b=(log j)²-(log k)²`.
The normalized mixed covariance is

`(jk)^(-β) Re[exp(-2i log(T) a + i b) α/(α-2ia)] + o(1)`.

This follows by the cosine-product identity and `u=log(T/x)`: the difference phase is
`-2 log(T)a+2ua+b`, whereas the sum phase has frequency tending to infinity.
Along a common subsequence with `z_j=lim exp(-2i log(T)log j)`, the tangent is

`K_z(j,k)=(jk)^(-β) Re[z_j conjugate(z_k) exp(i b) α/(α-2ia)]`.

The phase coordinates are completely multiplicative and unit-modulus. Simultaneous dilation
changes the phase by `z_j ↦ z_j exp(2i log(p)log j)`; it does not fix an individual kernel.

## Why individual homogeneity is impossible

For the pairs `(2^r,2^(r+1))`, homogeneous scaling by 2 would require a cosine progression
with nonzero amplitude and increment `2(log 2)²` to be constant for all `r≥0`.
The increment lies strictly between 0 and π. The three-term cosine recurrence forces a
constant progression to be zero; two consecutive zero values then contradict the nonzero
amplitude and nonzero sine of the increment. This argument avoids any unproved irrationality
claim about `π` and logarithms.

## Discrete-to-continuous error proof

For fixed `j,k` and sufficiently large `x`, the source and its derivative obey
`|v(x/j)|≤C_j x^β` and `|(d/dx)v(x/j)|≤C_j x^(β-1)(1+log x)`.
The mean-value theorem on each floor cell therefore bounds the difference between
`v(floor(n/j))v(floor(n/k))` and `v(n/j)v(n/k)` by
`C_(j,k) n^(2β-1)(1+log n)`. After multiplication by the pronic weight, its absolute
sum is finite because `2β-3<-1`. Replacing `1/(n(n+1))` by `1/n²` also has a finite
absolute error, bounded by a constant times `Σ n^(2β-3)`.

The derivative of `x^-2 v(x/j)v(x/k)` is bounded by
`C_(j,k) x^(2β-3)(1+log x)`, an integrable function at infinity. Applying the fundamental
theorem of calculus on every unit interval bounds the difference between its sum and integral
uniformly in the upper horizon. The finitely many initial floor cells contribute a fixed
constant. Thus the complete discrete covariance differs from its continuous integral by `O(1)`.

## Oscillatory integral proof

The cosine-product identity splits the integral into difference and sum phases. The difference
phase integrates exactly:

`∫ x^(α-1) exp(i[-2a log x+b]) dx = exp(ib) x^(α-2ia)/(α-2ia)`.

For the sum phase set `u=log x`, `L=log T`, and `s=log j+log k`. Apart from a constant
unit phase the integral is `∫ exp(αu+i(2u²-2su)) du`. Its part below `L/2` is
`O(exp(αL/2))`. On `[L/2,L]`, once `L` exceeds a fixed multiple of `|s|+1`,
`|α+i(4u-2s)|≥L`. Integrating by parts using the derivative of the full exponential gives
two endpoint terms of size at most `2 exp(αL)/L` and a remainder bounded by
`4 exp(αL)/(αL²)`. Hence the sum phase is `O(T^α/log T)`.

Combining both phases and the discrete error proves

`Σ_(n≤T) v(floor(n/j))v(floor(n/k))/(n(n+1))`
`= (jk)^(-β) Re[exp(ib) T^(α-2ia)/(2(α-2ia))] + O_(j,k)(T^α/log T+1)`.

The case `j=k=1` gives the stated energy asymptotic. Division by it proves the normalized
kernel formula and regular variation of index `α`, including horizons `floor(T/p)`.

## Complete tangent family

Let `χ(t)_j=exp(-2it log j)` and let `G` be the closure of `χ(R)` in the countable product
of unit circles. It is a compact metrizable group. Every element has `z_1=1` and
`z_(jk)=z_j z_k`, since these closed identities hold on `χ(R)`.

Every element of `G` is approached by `χ(t_n)` with `t_n→+∞`. For a finite collection of
coordinates, approximate the target by one orbit point and then add an arbitrarily large
simultaneous almost-period. The corpus's finite Bohr recurrence theorem supplies that
almost-period. A diagonal choice over the countable coordinates gives the assertion.
Replacing `exp(t_n)` by its ceiling changes its logarithm by a quantity tending to zero,
so integer horizons realize the same phases.

Thus every `K_z`, `z∈G`, is a source tangent. Conversely any convergent kernel subsequence
has a further convergent phase subsequence by compactness, and the explicit asymptotic identifies
its limit as `K_z`. The set of all source tangents is exactly the compact image of `G` under
`z↦K_z`. Injectivity of this parametrization is not asserted or needed.

## Positive survivor: exact boundary-loss representation

For a finite real packet `c`, define the explicit exponential polynomial

`F_(z,c)(u)=Σ_j c_j j^(-β) z_j exp(i(log j)²) exp(2iu log j)`.

Its kernel quadratic form is

`Q_z(c)=∫₀^∞ α exp(-αu) |F_(z,c)(u)|² du`.

This proves positivity directly. Distinct frequencies `2 log j` give linearly independent
exponentials on every nonempty interval: differentiating a vanishing finite exponential
polynomial yields an invertible Vandermonde system. Thus every finite Gram matrix on distinct
cofactors is positive definite, and every tangent has infinite rank.

Dilation of cofactor indices is represented on these functions by

`V_p F(u)=p^(-β) z_p exp(i(log p)²) exp(2iu log p) F(u+log p)`.

The multiplicative phase identity proves `V_p V_q=V_(pq)`. Changing variables in the norm gives
the exact positive boundary law

`Q_z(c with indices dilated by p)`
`=p^-1 [Q_z(c)-∫₀^(log p) α exp(-αu)|F_(z,c)(u)|² du]`.

Consequently the usual critical packet contraction holds for every tangent. It is strict on
every nonzero finite packet when `p>1`. This formula identifies the precise lost boundary mass;
it is stronger than merely exhibiting nonhomogeneity. Taking the closure of the explicitly
spanned packet functions supplies a cyclic real Hilbert representation with these bounded
operators. No representation or norm estimate is postulated.

The exact family transport is

`K_z(pj,pk)=p^(-2β) K_(z χ(-log p))(j,k)`.

The diagonal remains `K_z(j,j)=j^(-2β)`. For the three pairs `(1,2),(2,4),(4,8)`, the
normalized off-diagonal values form `Re(A exp(-2ir(log 2)²))`, `r=0,1,2`, with `A≠0`.
The argument above shows they cannot all agree. Hence no tangent is homogeneous even under
dilation 2. Since the difference from the putative stronger contracted Gram form has zero
diagonal and a nonzero mixed entry, one of the corresponding signed two-vector packets also
violates contraction by `2^(-2β)`.

## Stationary average and its failure of realization

Average over normalized Haar measure on `G`. For `j≠k`, the character `z↦z_j conjugate(z_k)`
is nontrivial: its value on `χ(t)` is `exp(-2it log(j/k))`, which is not identically one.
Haar invariance makes its integral zero. Therefore

`∫_G K_z(j,k) dz = 1_(j=k) j^(-2β)`.

This average is homogeneous and positive. It cannot be one source tangent, since every
individual tangent fails homogeneity. Thus stationary averaging and subsequence extraction
are provably different operations even for this smooth scalar source with bounded increments.

## Verification and novelty

- [x] Dependency-closed paper derivation of the discrete energy and every fixed mixed covariance.
- [x] Proof plans recorded for tangent-family classification, nonhomogeneity, and positive boundary representation.
- [x] Proof plan recorded for the stationary Haar average and its exclusion as an individual tangent.
- [ ] Lean formalization of the exact paper theorem.
- [ ] Full external novelty audit. No claim of priority or new general regular-variation theory.

Primary literature calibration: the classical Lamperti correspondence relates full
self-similarity to stationarity after logarithmic change of scale; see the explicit
[Lamperti theorem in Voutilainen's stationary-process treatment](https://vmsta.org/journal/VMSTA/article/102/text).
That correspondence assumes a full process scaling law. It does not supply mixed covariance
stationarity from a scalar energy asymptotic. Searches for chirp/regular-variation covariance
did not identify this exact discrete example; that absence is not evidence of novelty.

## Scope

This is an explicit scalar calibration source, not the Möbius receiver. Bounded increments
remove a defect of the earlier discontinuous logarithmic square-wave candidate, but no actual
Möbius or absolutely summable-mean divisor-source realization is claimed. The paper theorem
refutes only the inference from scalar regular variation and the coarse cofactor constraints
to individual stationary homogeneity. Lean results must not use it before formalization.

Pending source check: `/tmp/BiarithmeticChirpPhaseRigidity.lean` contains the three-rotation rigidity argument and the exact nondegenerate prime-two angle. It does not yet identify these three samples with actual source tangents; the discrete asymptotics, tangent realization, and boundary-loss representation remain outstanding.

Pending source check: `/tmp/BiarithmeticChirpPhaseGroup.lean` constructs the
compact closure group of the actual logarithmic phase flow and derives its
cofactor multiplicativity by closedness. Realization along diverging integer
horizons remains a separate obligation.

Pending source check: `/tmp/BiarithmeticChirpCauchyKernel.lean` identifies
the explicit kernel as a diagonal congruence of the corpus's strict Cauchy
Gram. It drafts strict positivity for every finite set of distinct
cofactors and arbitrary unit phases. Four audits remain unchecked.
The actual source asymptotics and weighted packet integral remain separate.

Pending source check: `/tmp/BiarithmeticChirpSourceRegularity.lean` defines
the actual scalar row, differentiates its positive-line interpolation,
proves derivative decay, and gives an explicit bound for every integer
increment. Four audits are drafted; no check has yet passed.

Pending source check: `/tmp/BiarithmeticChirpPacketIntegral.lean` identifies
the exact weighted half-line packet integral with the explicit real kernel,
including integrability and strict positive energy. It reduces to the existing
half-line exponential Gram theorem. Three audits are drafted; the Cauchy-kernel
dependency and this source are unchecked. The boundary-loss law and source
asymptotics remain separate obligations.
