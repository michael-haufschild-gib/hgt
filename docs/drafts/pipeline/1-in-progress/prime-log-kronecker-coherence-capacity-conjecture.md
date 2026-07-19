# Prime-log Kronecker coherence-capacity conjecture

- **ID:** `prime-log-kronecker-coherence-capacity-conjecture`
- **Stage:** 1-in-progress
- **Type:** CONJECTURE / PRIME-PHASE LARGE-DEVIATION LAW / CONNES BOUNDARY CARRIER
- **Scientific status:** `[FRONTIER CONJECTURE] [ANTI-THEATRE PASS 2026-07-19]`
  `[NOT AN RH RESTATEMENT] [NOT PROVED]`
- **Statement:** Every fixed macroscopic coherence level of the critical prime--polar boundary
  source has a strictly positive exponential cost per independent prime direction.  Equivalently,
  `log T=o(pi(X))` forces uniform dephasing.  The stronger profile conjecture predicts the exact
  cost from a weighted large-deviation variational law, while the formalized delayed recurrence
  proves that no superexponential cost is needed.

## Goal

The finite critical Mellin source has two apparently incompatible limits.

1. The prime number theorem makes its rescaled boundary measure converge weakly to the Laplace
   density `e^{-r/2}dr`.
2. At each finite aperture the source is atomic.  Its Fourier transform therefore has recurrent
   high-frequency phases and cannot converge uniformly to the Fourier transform of the continuous
   limit.

Fixed-frequency PNT convergence and abstract weak compactness do not identify where the missing
operator norm goes.  This conjecture predicts the complete phase diagram of that loss.  It is a
quantitative statement about one deterministic orbit in a torus whose dimension tends to
infinity, not an invocation of random independent prime phases.

For the Connes--Consani--Moscovici route, the conjecture would close a structural hole in the
prolate--boundary normal-form programme.  It would prove that carrier-frequency escape is absent
throughout every logarithmic Gamma graph window and becomes macroscopic only after the phase-time
budget reaches order `\pi(X)`.  Thus the low-energy normal form may contain prolate and spatial
boundary profiles without an additional uncontrolled prime-phase channel.

## 1. The exact critical boundary transform

Put

```text
X>1,
k_X=pi(X),

D_X(t)
 =X^(-1/2) sum_(n<=X) Lambda(n)n^(-1/2)
      exp(i t(log X-log n))
  -1/(1/2-it).                                               (1)
```

The first term is the Fourier transform of the rescaled prime boundary measure

```text
mu_X
 =X^(-1/2) sum_(n<=X)Lambda(n)n^(-1/2)
      delta_(log X-log n),                                   (2)
```

and the second is the Fourier transform of

```text
nu(dr)=exp(-r/2)1_(r>=0)dr.                                  (3)
```

The prime number theorem gives

```text
mu_X => nu,
mu_X(R)->2,
D_X(t)->0 for every fixed t.                                 (4)
```

At each fixed `X`, however, the formalized cofinal annular recurrence of the finitely many prime
logarithms gives

```text
limsup_(|t|->infinity)|D_X(t)|=mu_X(R).                      (5)
```

Thus pointwise convergence and uniform convergence differ by an asymptotic norm exactly equal to
`2`.  The open question is only the least phase-time budget needed to recover a prescribed
fraction of that norm as `k_X->infinity`; full cofinal recurrence and simultaneous polar decay are
already unconditional.

## 2. The candidate rate function

Let `I_0` denote the modified Bessel function.  For `lambda>=0` define

```text
Lambda_*(lambda)
 =integral_0^1 log I_0(lambda/(2 sqrt(v)))dv,                 (6)

I_*(q)
 =sup_(lambda>=0){lambda q-Lambda_*(lambda)},
       0<=q<1.                                               (7)
```

The integral in `(6)` is finite.  It is the limiting logarithmic moment functional of the
independent-phase comparison model

```text
(1/(2 sqrt(X))) sum_(p<=X)(log p)/sqrt(p) exp(i theta_p),     (8)
```

at speed `pi(X)`.  The nonconstant weight `1/(2sqrt(v))` is forced by the prime density and the
critical coefficient `(log p)/sqrt(p)`; replacing it by an iid equal-weight model changes the
rate function and is not admissible.

Let `q_*(tau)` be the unique value in `[0,1)` satisfying

```text
I_*(q_*(tau))=tau,
q_*(0)=0.                                                    (9)
```

Equivalently, `q_*` is the inverse radial large-deviation cost.  It is increasing,
`q_*(tau)->1` as `tau->infinity`, and contains no zeta zero or RH hypothesis.

## 3. Master conjecture: positive prime coherence entropy

For `0<q<1`, define the first macroscopic coherence clock

```text
H_X(q)=inf{T>=1:
  sup_(1<=|t|<=T)|D_X(t)|>=2q}.                              (10a)
```

### Prime coherence-entropy law `[MASTER CONJECTURE]`

For every `q in (0,1)`,

```text
liminf_(X->infinity) log H_X(q)/pi(X)>0.                    (10b)
```

Equivalently, for every positive time scale `T_X`,

```text
log T_X=o(pi(X))
  => sup_(1<=|t|<=T_X)|D_X(t)|->0.                          (10c)
```

This is the irreducible theorem target.  It says positively that every nonzero macroscopic
prime--polar coherence level must pay a positive exponential cost in the number of independent
prime phases.  It is a deterministic statement about the actual orbit `t(log p)_p`; random phases,
almost-every frequency vectors, and infinite-time Bohr recovery do not imply it.

The opposite finiteness statement is unconditional.  The delayed positive-weight recurrence gives,
for every integer `Q>=0` and every clock floor `L>=1`, a return by time

```text
L(Q+1)^(pi(X)+o(pi(X)))                                    (10d)
```

whose relative phase loss is at most `2pi^2/(Q+1)^2` and whose polar loss is at most `1/L`.
Consequently, for each `q<1`,

```text
limsup_(X->infinity) log H_X(q)/pi(X)
 <=inf{log(Q+1): 1-2pi^2/(Q+1)^2>q}<infinity.               (10e)
```

In particular, the proved high-coherence cost has the correct square-root resolution order

```text
log H_X(q)/pi(X)
 <=(1/2)log(1/(1-q))+O(1)       as q->1-.                  (10f)
```

Thus the genuine frontier is not whether the coherence clock is at most exponential.  It is the
matching positive lower entropy `(10b)` for the one arithmetic prime-log orbit.

## 4. Strong refinement: the complete capacity profile

For `tau>=0`, set

```text
C_X(tau)=sup_{1<=|t|<=exp(tau pi(X))}|D_X(t)|.               (10)
```

### Prime-log coherence-capacity profile `[STRONG CONJECTURE]`

For every `tau>=0`,

```text
lim_(X->infinity) C_X(tau)=2 q_*(tau).                       (11)
```

The convergence is locally uniform in `tau`.  More generally, for every positive time scale
`T_X`, writing

```text
tau_X=log T_X/pi(X),                                        (12)
```

one has the trichotomy

```text
tau_X->0       => sup_(1<=|t|<=T_X)|D_X(t)|->0,
tau_X->tau     => sup_(1<=|t|<=T_X)|D_X(t)|->2q_*(tau),
tau_X->infinity=> sup_(1<=|t|<=T_X)|D_X(t)|->2.              (13)
```

Prime powers of exponent at least two do not alter `(11)`: their total critical weight is
`o(sqrt(X))`.  The subtraction in `(1)` is load-bearing.  It removes the deterministic continuum
coherence visible at bounded `t`; without it, the value at `t=0` would make every capacity equal
to the trivial total mass.

The Bessel profile in `(11)` is a sharpened candidate, not protected from falsification.  The
irreducible frontier statement is `(10b)`--`(10c)`, equivalently the first implication in `(13)`:

```text
log T_X=o(pi(X))
  => sup_(1<=|t|<=T_X)|D_X(t)|->0.                          (13a)
```

If deterministic prime-log correlations change `q_*` at critical scale while `(13a)` survives,
the exact profile claim is retired but the Connes consequence remains.  If `(13a)` fails, the
two-channel prolate--boundary architecture must retain an independent phase carrier.

## 5. Equivalent aperture exponent law

Write `X=e^(2a)`.  For `theta>=0`, define

```text
E_theta(a)
 =sup_(1<=|t|<=exp(exp(theta a)))|D_(exp(2a))(t)|.           (14)
```

Since

```text
pi(exp(2a))~exp(2a)/(2a),                                   (15)
```

equation `(13)` predicts the sharp exponent transition

```text
theta<2 => E_theta(a)->0,
theta>2 => E_theta(a)->2.                                   (16)
```

The line `theta=2` has a logarithmic boundary layer.  Its nontrivial coordinate is

```text
log T/pi(exp(2a)),                                          (17)
```

and its universal profile is `2q_*`.  Thus the exponent `2` is not dimensional decoration: it is
the prime-counting cost of resolving the `pi(e^(2a))` independent phase directions.

## 6. Connes consequence

The archimedean multiplier in the corrected CCM symbol grows like

```text
m_Gamma(t)=log(2+|t|)+O(1).                                 (18)
```

A state whose Gamma energy is at most the natural aperture frame scale `e^a` can therefore occupy
only frequencies satisfying

```text
log(2+|t|)=O(e^a).                                          (19)
```

But

```text
e^a=o(pi(e^(2a))).                                          (20)
```

The subcritical clause of `(13)` then gives

```text
sup_(log(2+|t|)<=C e^a)|D_(e^(2a))(t)|->0                  (21)
```

for every fixed `C`.  Hence prime-phase recurrence cannot carry a nonzero leading boundary
defect inside the Gamma-admissible low-energy window.

In fact `(21)` and the uniform mass bound imply the global moving-graph estimate

```text
sup_(t in R)
 |D_(e^(2a))(t)|/[1+e^(-a)log(2+|t|)] ->0.                  (21a)
```

To see the implication, first restrict to `log(2+|t|)<=C e^a` and use `(21)`; on the complement
the denominator is at least `C`, while the numerator is bounded by the total prime and Laplace
masses.  Let `a->infinity` and then `C->infinity`.  Equation `(21a)` is the exact relative
operator-norm statement: the normalized prime--polar boundary defect is infinitesimal with
respect to the natural logarithmic Gamma graph weight.

This is the precise positive structural statement needed by the cofinal prolate--boundary
normal-form conjecture:

```text
bounded Gamma budget
  => subcritical prime-phase capacity
  => uniform boundary dephasing
  => no independent carrier-frequency escape channel.       (22)
```

The remaining RH-bearing term is still the sign of the subleading assembled boundary form.  The
conjecture does not call that sign new and does not derive it from `(11)`.

## 7. Why this is not a known theorem in disguise

The following parent results do not imply `(11)`.

1. **Kronecker and Dirichlet approximation.**  They prove density and a coarse recurrence upper
   bound at each fixed dimension.  They do not give an extreme-value law when the dimension is
   `pi(X)` and the observation time is exponential in that dimension.
2. **Prime number theorem.**  It proves `(4)` at each fixed frequency and on compact frequency
   sets.  It gives no control of the exponentially growing window `(10)`.
3. **Random Euler products and zeta value distribution.**  They replace prime phases by random
   independent phases or average over `t`.  Equation `(11)` is a deterministic supremum law for
   the one actual prime-log orbit.
4. **Resonance methods.**  They construct selected large values of zeta or its logarithmic
   derivative.  They do not identify the complete capacity curve, its weighted Bessel rate, or
   the subcritical uniform dephasing threshold.
5. **Infinite-torus Kronecker dynamics.**  Minimality and unique ergodicity do not give the
   growing-dimensional hitting-time asymptotic `(11)`.

A targeted Google/arXiv audit through 2026-07-19 found work on quantitative Kronecker density,
simultaneous Diophantine approximation, random Euler products, resonance methods, and
infinite-dimensional Kronecker minimality, but no deterministic growing-dimensional
large-deviation law of the form `(11)` and no critical-Mellin/Connes consequence `(21)`.

## 8. Anti-theatre kill tests

This card is killed, not promoted, if any of the following occurs.

1. **Fixed-dimension collapse.**  The proof holds only after fixing a finite prime set.
2. **Random-model substitution.**  Independent random phases prove `(7)` but are silently
   substituted for the deterministic orbit in `(10)`.
3. **Average-for-supremum substitution.**  A mean-value theorem in `t` is presented as the
   deterministic extreme law `(11)` without a hitting-time theorem.
4. **PNT theatre.**  Only compact-frequency convergence in `(4)` is proved.
5. **Dirichlet theatre.**  Only the supercritical recurrence `limsup>=2` is obtained.
6. **Wrong normalization.**  The continuum transform in `(1)`, the prime weights, or the speed
   `pi(X)` is changed to force a convenient iid model.
7. **RH circularity.**  A zero-free region of RH strength, the Weil criterion, or positivity of
   the completed boundary form is used to prove `(11)`.
8. **Literature collision.**  A published theorem already supplies the deterministic weighted
   extreme-value curve `(11)` for the prime-log orbit.  Generic Kronecker, Cramer, or resonance
   theorems do not meet this test.

## 9. Research attack

The proof problem has four sharply separated gates.

### A. Independent-phase variational law

Prove the weighted triangular-array large-deviation principle with cumulant `(6)`, including the
radial contraction `(7)` and the negligibility of higher prime powers.  This is parent-theory
infrastructure and is not the new core.

### B. Deterministic exponential-time upper bound

For every `q` and `epsilon>0`, prove

```text
meas{t in [1,T]: |D_X(t)|>=2q}
 <=T exp(-(I_*(q)-epsilon)pi(X))                             (23)
```

uniformly for `log T=O(pi(X))`, with an error strong enough to imply absence of a hit when
`log T<(I_*(q)-2epsilon)pi(X)`.  This is the principal new Diophantine/exponential-sum gate.

### C. Deterministic hitting lower bound

Prove that every superlevel with `I_*(q)<tau` is hit before `exp(tau pi(X))`.  A quantitative
Kronecker theorem must be weighted and asymptotically rate-optimal; the ordinary pigeonhole bound
does not recover the curve.

The endpoint `tau_X->infinity` is already proved by the delayed weighted recurrence.  Phase
resolution `Q` and clock floor `L` are independent and cost at most

```text
log L+pi(X)log(Q+1),                                       (24)
```

while the phase error is at most `2pi/(Q+1)` and the polar term is at most `1/L`.  Taking
`Q,L->infinity` sufficiently slowly under `tau_X->infinity` proves full coherence.  Gate C
therefore concerns only the finite critical-rate curve, not eventual full coherence or polar
decay.

### D. Gamma-window transfer

Transfer the subcritical result through the exact critical Mellin Stieltjes pairing and the
variable-width parity principalization.  Prove `(21)` as an operator estimate in the logarithmic
Gamma graph norm, then insert it into the prolate--boundary relative normal form without changing
the subleading Weil sign.

## Gates

- [x] source-pure observable `(1)` identified
- [x] correct growing dimension and critical time scale identified
- [x] candidate weighted variational rate `(6)`--`(9)` derived
- [x] anti-theatre and initial literature audit completed
- [x] sharp finite-dimensional pigeonhole budget formalized in
  `quantitative-finite-prime-log-phase-recurrence.md`
- [x] weighted-source recurrence and deterministic norm-capacity floor formalized in the same
  card
- [x] delay--resolution recurrence with simultaneous critical-pole decay formalized; the
  `tau_X->infinity` branch is unconditional
- [ ] prove the independent-phase triangular-array LDP
- [ ] prove deterministic exponential-time upper bound `(23)`
- [ ] prove deterministic rate-optimal hitting
- [ ] prove the master capacity law `(11)`
- [ ] formalize every unconditional layer in Lean
- [ ] transfer the subcritical law and `(21a)` to the exact CCM Gamma graph

## Preliminary comparison sources

- K. Soundararajan, *Extreme values of zeta and L-functions*, arXiv:0708.3990.
- L. Guth and J. Maynard, *New large value estimates for Dirichlet polynomials*,
  arXiv:2405.20552, v2 (2026).  This is the nearest serious parent for Gate B, but it does not
  state the finite-time prime-log capacity law `(11)` or the subcritical uniform dephasing
  assertion `(13a)`.
- O. F. Brevig, *On the Sidon Constant for Dirichlet Polynomials*, arXiv:1306.0403.  Infinite-time
  Bohr/Sidon norm recovery is parent theory; the growing finite-time horizon is the missing datum.
- A. Gorodnik and P. Vishe, *Simultaneous Diophantine approximation -- logarithmic
  improvements*, arXiv:1601.03525.
- L. Baroni, *Kronecker Flow on the Infinite Torus*, arXiv:2604.02213.
- Classical Kronecker and Dirichlet simultaneous approximation theorems.
- Classical Cramer/Gartner--Ellis large-deviation theory for triangular arrays.

## Log

- 2026-07-19 -- Created after the variable-width boundary principalization exposed an omitted
  carrier-frequency channel.  Compact-frequency PNT and fixed Sobolev regularization were demoted
  as parent theory; the surviving frontier is the deterministic `log T~pi(X)` capacity curve.
