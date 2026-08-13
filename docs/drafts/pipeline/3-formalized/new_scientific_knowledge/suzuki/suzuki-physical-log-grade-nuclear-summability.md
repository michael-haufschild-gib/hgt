# Suzuki inverse-log grades are nuclear directly in the physical Gamma measure

- **ID:** `suzuki-physical-log-grade-nuclear-summability`
- **Stage:** 3 — formalized in Lean 4
- **Type:** EXACT CARRIER SUMMABILITY THEOREM / SOURCE-ARCHITECTURE REPLACEMENT
- **Scientific status:** `[PROVED HERE] [NEW SCIENTIFIC KNOWLEDGE]`
  `[NOVELTY UNVERIFIED] [NOT RH]`
- **Inputs:** `suzuki-completed-zero-mode-corona-seam-law.md`,
  `suzuki-two-root-valuation-wiener-lift.md`,
  `suzuki-scalar-analytic-forcing-trace-zero-h1.md`
- **Route:** Connes/CCM restricted-Weil form through Suzuki completed zero modes

## 1. Result

The false route

```text
global Fourier Wiener coefficients
 -> inverse Fourier in the spatial variable
 -> upgrade dr to dr/r
```

is unnecessary.  Suzuki's physical seam carrier can be nuclear directly in boundary-log
coordinates if the already identified word grades obey their natural first-arrival majorant.

Let \(I_k\) be the finite family of oriented prime-valuation words of physical inverse-log grade
\(k\ge1\).  Let \(a_{k,\nu}\ge0\) satisfy

```text
sum_(nu in I_k) a_(k,nu) <=M^k.                         (1)
```

Suppose the physical profiles satisfy, for \(L\ge L_0>0\),

```text
||F_(k,nu)(L)||
 <=C a_(k,nu) L^(-k-1/2).                               (2)
```

If

```text
q=M/L_0<1,                                               (3)
```

then

```text
sum_(k>=1) sum_(nu in I_k)
  ||F_(k,nu)||_(L2((L_0,infinity),dL))
 <=C/sqrt(2) * q/(1-q)<infinity.                        (4)
```

Consequently the descendant state belongs to

```text
ell1(descendants;L2(dL))
 subset L2(dL;ell1)
 subset L2(dL;ell2).                                    (5)
```

This is the physical Gamma measure itself.  No \(dr/r\) upgrade appears because
\(dL=dr/r\) was built in before summation.

The grade-zero sector is separate and finite-dimensional.  Its half-log component is the only
possible non-\(L^2(dL)\) term.  Zero trace, after the two low-frequency boundary counterterms are
attached, puts grade zero in \(L^2(dL)\) by the exact Gamma scattering classification.  Therefore

```text
zero matched half-log trace
 + physical word majorant (1)--(2)
 -> full ell1 subset ell2 physical Gamma carrier.       (6)
```

This is the correct E1 target.

## 2. Nuclear proof

For \(k\ge1\),

```text
integral_(L_0)^infinity L^(-2k-1)dL
 =L_0^(-2k)/(2k).                                       (7)
```

Equation `(2)` gives

```text
||F_(k,nu)||_L2
 <=C a_(k,nu)L_0^(-k)/sqrt(2k).                         (8)
```

Sum first over the finite grade:

```text
sum_(nu in I_k)||F_(k,nu)||_L2
 <=C/sqrt(2k) (M/L_0)^k
 <=C/sqrt(2) q^k.                                       (9)
```

The geometric sum of `(9)` is `(4)`.  Absolute convergence in
\(\ell^1(L^2)\) and Minkowski prove `(5)`. `QED`

The \(1/\sqrt{k}\) gain in `(9)` is real but not needed for convergence.  Threshold \(L_0>M\) is
sufficient, not asserted sharp.

## 3. Why the majorant is source-natural

At fixed aperture, Suzuki's visible prime adjacency is

```text
T_a
 =sum_(p^j<=exp(2a)) w_(p,j)
   [shift_(j e_p)+shift_(-j e_p)],

w_(p,j)=(log p)/p^(j/2)>0,                              (10)
```

with total absolute mass

```text
M_a=2 sum_(p^j<=exp(2a))w_(p,j)<infinity.               (11)
```

Every length-\(k\) translation word has weight equal to the product of its step weights.  Summing
over all words gives exactly \(M_a^k\).  Collisions can only reduce the coefficientwise absolute
majorant, so `(1)` holds with \(M=M_a\).

The exact trace-zero Volterra inverse explains `(2)`.  If

```text
Phi(L)=A L^(-alpha),
P F=Phi,
P F=2L F-integral F,
lim sqrt(L)F(L)=0,                                      (12)
```

then

```text
F(L)
 =-1/(2sqrt(L)) integral_L^infinity Phi'(t)/sqrt(t)dt
 =alpha/(2alpha+1) A L^(-alpha-1).                     (13)
```

Thus one prime step raises inverse-log exponent by exactly one and multiplies the absolute
coefficient by at most its source weight.  Starting from the half-log exponent
\(\alpha=1/2\), grade \(k\) has exponent \(k+1/2\), exactly `(2)`.

The coefficient is sharper than that bound.  At the \(j\)-th propagation,

```text
alpha_j=j+1/2,
alpha_j/(2alpha_j+1)=(2j+1)/(4j+4).                     (13a)
```

Therefore a length-\(k\) word carries the universal Volterra factor

```text
theta_k
 =product_(j=0)^(k-1) (2j+1)/(4j+4)
 =(2k)!/[8^k(k!)^2]
 =binom(2k,k)/8^k
 <=2^(-k).                                              (13b)
```

In particular the first transported seam coefficient is exactly

```text
theta_1 w_(p,j) beta=(1/4)w_(p,j)beta                   (13c)
```

in the unit-normalized physical equation, with the Suzuki source sign inherited from `(10)`.
Thus the source-specialized grade majorant is

```text
sum_nu a_(k,nu) <=theta_k M_a^k<=(M_a/2)^k.             (13d)
```

Applying Sections 1--2 with effective mass \(M_a/2\) improves the sufficient physical-tail
threshold to

```text
L_0>M_a/2.                                              (13e)
```

This factor is not a heuristic smallness gain; it is forced by the exact Volterra indicial
recurrence.

The Gamma jump remainder is better by two orders on a controlled power germ:

```text
R[L^(-alpha)]
 =O_alpha(L^(-alpha-2))+O(exp(-L/2)).                   (14)
```

It therefore cannot worsen the word grade.  Smooth polar and cutoff blocks are
Gamma-subcritical.  The only missing step for literal Suzuki application is a uniform version of
`(13)`--`(14)` for the exact recursively forced weak solution, with coefficient constants
controlled by one exponential word budget rather than separately at each fixed grade.

## 4. Exact replacement of the broken carrier

Two distinct carriers must not be conflated:

```text
global Fourier carrier:
  solves the whole-line multiplier equation at |xi|>>1,
  is nuclear in ordinary position L2(dr),
  but generally fails physical dr/r after spatial inverse Fourier;

physical log-graded carrier:
  is constructed from endpoint/seam normal expansions in L=-log r,
  has grade decay L^(-k-1/2),
  and is nuclear directly in L2(dL) by (4).              (15)
```

The first remains useful for global exterior algebra and two-port matching.  It is not the
physical Gamma state.  The second is the correct input to self-adjoint prime adjacency, Gamma
scattering, block Hardy transfer, and weighted-tail coercivity.

The bridge between them is not an impossible coordinatewise Fourier theorem.  It is a
source-normal expansion theorem:

```text
SUZUKI-UNIFORM-PHYSICAL-WORD-MAJORANT:
every completed zero mode admits exact oriented normal profiles
satisfying (1)--(2), with grade zero equal to its matched endpoint
Gamma scattering state.                                 (16)
```

Once `(16)` is proved, `(4)`--`(6)` supply the complete physical carrier automatically.

## 5. Stronger consequence: no infinite-grade summation debt after the majorant

The earlier finite-detector theorem showed that countable convergence was not logically necessary
for kernel exclusion.  The present result is stronger analytically: the natural source majorant
would make the entire descendant hierarchy converge in the exact physical Hilbert space.

In particular:

```text
support-pruned density of seam locations
does not cause norm divergence;
only failure of the uniform coefficient majorant can.   (17)
```

Dense geometry and Hilbert summability are separated.  The obstruction is now quantitative
source transport, not countability or seam collision.

## 6. Hostile audit

1. **No reuse of the false Fourier upgrade.**  Profiles in `(2)` are physical log-normal germs.
2. **No pointwise-to-norm leap.**  Integral `(7)` and nuclear order of summation prove `(4)`.
3. **No grade-zero smuggling.**  Its half-log defect is isolated and requires trace-zero Gamma
   gluing.
4. **No cancellation assumption.**  Positive absolute word weights give `(1)`.
5. **No claim that fixed-grade asymptotics are uniform.**  Uniformity across all \(k\) is exactly
   open conjecture `(16)`.
6. **No RH claim.**  Even `(16)` plus carrier coercivity still leaves two-ended corona return and
   raw Evans injectivity.

## 7. Lean boundary

Integral `(7)` and the geometric series are standard.  Formalizing only `(1)`--`(4)` with abstract
numbers would certify no Suzuki source connector and would be theorem theatre.  Lean
formalization should begin when the exact physical word-profile object and its coefficient
recursion exist; then `(4)` becomes the terminal summability theorem for that concrete series.

The first source-bearing recurrence is now formalized unconditionally in

```text
formal/GaloisForLFunctions/RHTower/
  SuzukiVolterraLogGradeRecurrence.lean
```

It defines

```text
suzukiVolterraRaisedCoefficient(alpha,A)
 =alpha/(2alpha+1) A
```

and proves both the exact differentiated recurrence and nonvanishing for every positive grade.
Thus the universal coefficient in `(13)` is kernel-checked rather than left as the earlier
unspecified constant `C_a`.  It also proves the norm contraction

```text
||suzukiVolterraRaisedCoefficient(alpha,A)||
 <=(1/2)||A||,       alpha>0,                            (18a)
```

which certifies the uniform `2^(-k)` bound in `(13b)` under iteration.

Existing unconditional Lean infrastructure already supplies:

```text
prime-valuation coordinate injectivity and collision laws;
bounded self-adjoint finite-prime adjacency;
positive exterior Feshbach return;
Gamma weighted-tail coercivity;
two-boundary-counterterm algebra.
```

The missing formal object is precisely `(16)`, not a geometric-sum lemma.

## 8. Novelty boundary

Power-tail integration and geometric word majorants are classical.  Candidate-new source
knowledge is the exact Route-O synthesis:

```text
Suzuki grade k = k+1/2
 + exact Volterra factor binom(2k,k)/8^k
 + von-Mangoldt total word mass M_a^k
 -> nuclear convergence in physical L2(dL) on L_0>M_a/2
 -> no dr/r Fourier upgrade is needed.                  (18)
```

No prior corpus card or targeted source search identified `(18)`.  Priority remains unverified.

## Gates

- [x] prove exact gradewise physical \(L^2\) norm
- [x] sum all oriented words in nuclear order
- [x] isolate grade-zero half-log sector
- [x] combine zero-trace Gamma classification with descendant summability
- [x] replace false Fourier-to-physical interface by source-normal word majorant
- [x] formalize exact Volterra grade coefficient and nonvanishing in Lean
- [x] derive exact central-binomial word factor and improved threshold \(L_0>M_a/2\)
- [ ] prove exact physical profile recursion for the full Suzuki source
- [ ] prove one uniform word coefficient majorant across all grades
- [ ] instantiate `(4)` for every completed zero mode
- [ ] apply Gamma coercivity and prove trace-zero \(H^1\)
- [ ] prove corona and raw Evans injectivity
- [ ] RH

### The terminal summability theorem for the concrete series EXISTS — Section 7's boundary is met

Section 7 said formalization should begin when "the exact physical word-profile object and its
coefficient recursion exist; then `(4)` becomes the terminal summability theorem for that concrete
series."  Both now exist, in `RHTower/SuzukiPhysicalLogGradeNuclearSummability.lean`, built on the
corpus's own `suzukiPrimePowerWeight` (the card's `(10)`) and `suzukiPrimeNormalGradeFactor` (the
Volterra recursion of `(13a)`):

- `sum_prod_suzukiWordWeights` — **`(1)` with equality**: the length-`k` word sum is exactly
  `M_a^k` (the multinomial expansion, so collisions can only help);
- `suzukiPrimeNormalGradeFactor_eq_centralBinom` — **`(13b)`'s closed form**
  `θ_k = binom(2k,k)/8^k`, by the central-binomial recurrence, with the corpus's `θ_k ≤ 2^{-k}`;
- `sum_suzukiWordCoefficient_le` / `sum_suzukiWordCoefficient_subtype_le` — **`(13d)`**: total
  grade coefficient `= θ_k M_a^k ≤ (M_a/2)^k`;
- `integral_sq_suzukiGradeProfile`, `norm_suzukiGradeProfileLp` — **`(7)`–`(8)` exactly**: the
  grade profile's tail energy is `c² L₀^{-2k}/(2k)` and its `L²(dL)` norm is
  `|c| L₀^{-k}/√(2k)`;
- `suzukiVolterraInverse_integral` — **`(13)`**: the trace-zero Volterra inverse of the
  differentiated power source is exactly `α/(2α+1) · A · L^{-α-1}`;
- `sum_norm_suzukiWordProfileLp_le`, `summable_norm_suzukiWordProfileLp`,
  `tsum_norm_suzukiWordProfileLp_le` — **`(4)` at the improved threshold `(13e)`**: for
  `L₀ > M_a/2` the norm series over all positive grades and all words is summable with the exact
  bound `C/√2 · q/(1-q)`, `q = M_a/(2L₀)`;
- `summable_suzukiWordProfileLp` — **`(5)`'s Hilbert-carrier content**: the grade-word profiles
  are absolutely summable in `L²(dL)` itself, so the descendant state exists in the physical
  Gamma measure with no `dr/r` upgrade anywhere.

All audit to exactly `[propext, Classical.choice, Quot.sound]`; umbrella wired.  What remains
open is exactly what the card names: the uniform majorant `(16)` for the actual recursively
forced weak solution, which is the correct-E1-target research conjecture, not a summability
lemma.
