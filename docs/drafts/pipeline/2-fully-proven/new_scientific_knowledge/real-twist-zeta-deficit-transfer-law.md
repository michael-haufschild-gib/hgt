# Real-twist spectral gap from the zeta one-line deficit

- **ID:** `real-twist-zeta-deficit-transfer-law`
- **Stage:** `2-fully-proven`
- **Type:** `THEOREM (paper) [CORPUS] [BRIDGE] [PROJECT-LOCAL NEW KNOWLEDGE]`
- **Sources:** `../not_new_scientific_knowledge/halasz-ghs-adaptive-coarea-completion.md`,
  `../../1-in-progress/mr-splice-wide-range-mean-square.md`
- **Statement:** For real multiplicative functions, the uniform twist gap needed by the
  Matomäki--Radziwiłł Halász polynomial receives the universal one-quarter share of the deficit of
  `log|zeta|` below its trivial `log log x` scale.  The sharp GHS `L`-norm transports that
  gap while isolating the bounded antitwist cell cluster at cost `1/|t|`.  The corpus's completed
  Littlewood line-rate chain supplies an unconditional `log log log x` deficit, yielding both an
  `o(1)` MR long-factor bound and a divergent antiscale frame on every polynomial frequency
  horizon.

## Novelty calibration

The pretentious triangle inequality, the real-valued separation lemma, and its
Vinogradov--Korobov application are `[LITERATURE]`.  The project-local new result is the
deficit formulation and its exact splice into the GHS cell norm.  It separates three logically
different inputs which the live proof map had conflated:

```text
zeta one-line deficit -> real character gap -> twisted GHS polynomial saving.
```

Corpus search found all algebraic transfer pieces, a newly formalized exponent-one zero-free
region, and—after corpus growth—the completed Littlewood line-rate chain, but not this quantitative
dependency law, its prefix-uniform shifted transport, or the polynomial-horizon antiscale corollary.
No external publication novelty is claimed without expert audit.

## Setup

For functions `a,b` on the primes with values in the closed unit disc, write

```text
D_x(a,b)^2=sum_(p<=x) (1-Re(a(p)conj(b(p))))/p.         (Z1)
```

Let `0<=Delta(x)<=log log x`; a larger deficit may always be truncated to this range.  Fix
`B>0`.  Assume the shifted one-line upper bound

```text
log|zeta(1+1/log x+i tau)|
  <= log log x-Delta(x)+C_B                             (Z2)
```

for all sufficiently large `x` and every `1<=|tau|<=x^B`.

The shift `1/log x` is part of the theorem.  It makes the Euler series absolutely convergent
while its prime tail beyond `x` and the change from `p^(-1-1/log x)` to `p^(-1)` both cost only
an absolute constant.

## Exact deficit identity `[PAPER-PROVED]`

Uniformly in every real `tau`,

```text
log log x-log|zeta(1+1/log x+i tau)|
 = sum_(p<=x) (1-cos(tau log p))/p+O(1).                (Z2a)
```

Indeed the two-sided Euler-log comparison, rather than only its upper half, gives

```text
log|zeta(1+1/log x+i tau)|
 = sum_p cos(tau log p)/p^(1+1/log x)+O(1).             (Z2b)
```

Prime powers contribute `O(sum_p p^(-2))=O(1)`.  The absolute tail and abscissa-shift estimates
are exactly `(Z5)`--`(Z6)` below, so `(Z2b)` becomes the finite cosine sum at exponent one with
`O(1)` error.  Mertens' theorem then proves `(Z2a)`.

Thus shifted zeta deficit is, up to bounded normalization, squared prime-clock distance
`D_x(1,n^(i tau))^2`.  Analytic one-line control and growing-prime bounded-horizon nonrecurrence
are not merely analogous routes; they are quantitatively equivalent formulations of the same
energy.

## Littlewood shift completion from the grown corpus `[PAPER-PROVED] [CORPUS]`

The new derivative-test chain closes `(Z2)` with an unbounded, though subpower, deficit.  For every
fixed `B>0`,

```text
sup_(1<=|tau|<=x^B) |zeta(1+1/log x+i tau)|
  <= C_B log x/log log x.                              (Z2c)
```

Consequently `(Z2)` holds with

```text
Delta_L(x)=log log log x-O_B(1).                       (Z2d)
```

This conclusion does not follow from the exponent-one zero-free region.  It comes from the
independent Littlewood derivative-test programme now present in
`RHTower/Sieve/DirichletBlockAbel.lean`, `DirichletExplicitRHS.lean`,
`DirichletOrderRate.lean`, `ZetaPartialSumTruncation.lean`, and `ZetaLineRate.lean`.

### Proof of `(Z2c)`

For `tau` above a fixed absolute threshold, the proof underlying
`norm_riemannZeta_line_rate_clean` gives

```text
B(tau) << log|tau|/log log|tau|                        (Z2e)
```

for the partial sum of `n^(-1-i tau)` up to the canonical truncation
`N_tau asymp |tau|^3`.  The same bound is uniform in every prefix `M<=N_tau`.  Below the split
point this is the harmonic head bound.  Above it, `DirichletBlockAbel` proves the derivative-test
estimate on an arbitrary terminal subinterval `Ico N M`, not only on a completed dyadic block;
the dyadic assembly can therefore stop at any `M` with no new loss.

Put `delta=1/log x`.  Discrete Abel summation with the decreasing weight `n^(-delta)` gives

```text
|sum_(n<=N_tau) n^(-1-delta-i tau)|
 <= B(tau)N_tau^(-delta)
    +delta B(tau) integral_1^N_tau u^(-delta-1)du
 <= 2B(tau).                                           (Z2f)
```

The zeta truncation with the partial sum retained contributes at most

```text
N_tau^(-delta)/|delta+i tau|
  + |1+delta+i tau| N_tau^(-1-delta)/(1+delta) << 1.   (Z2g)
```

Thus the Littlewood rate is uniform on `Re(s)=1+delta`.  Since `log t/log log t` is eventually
increasing, `(Z2e)`--`(Z2g)` are at most the right side of `(Z2c)` throughout
`T_0<=|tau|<=x^B`.  The compact range `1<=|tau|<=T_0` is uniformly bounded because it stays away
from the pole at `1`; conjugation handles negative `tau`.  Taking logarithms proves `(Z2d)`.

## The zeta-deficit transfer `[PAPER-PROVED]`

Let `g : N -> [-1,1]` be multiplicative.  Under `(Z2)`, uniformly for
`1<=|alpha|<=x^(B-1)`,

```text
D_x(g,n^(i alpha))^2 >= Delta(x)/4-O_B(1).              (Z3)
```

### Proof

Euler-product comparison at

```text
s=1+1/log x+2i alpha
```

gives

```text
sum_p cos(2 alpha log p)/p^(1+1/log x)
  <= log|zeta(s)|+O(1).                                (Z4)
```

The contribution of `p>x` in `(Z4)` is `O(1)`:

```text
sum_(p>x) p^(-1-1/log x)
 <= C integral_x^infinity dt/(t^(1+1/log x)log t)
 =  C integral_1^infinity exp(-u)/u du.                (Z5)
```

Partial summation with Chebyshev's bound also gives

```text
sum_(p<=x) (1/p-p^(-1-1/log x)) <= C.                  (Z6)
```

The frequency `2 alpha` lies in the range of `(Z2)` after increasing `B` by one.  Therefore
`(Z2)`--`(Z6)` imply

```text
sum_(p<=x) cos(2 alpha log p)/p
 <= log log x-Delta(x)+O_B(1).                         (Z7)
```

Mertens' lower bound and `(Z7)` yield the character separation

```text
D_x(n^(-i alpha),n^(i alpha))^2
 = sum_(p<=x) (1-cos(2 alpha log p))/p
 >= Delta(x)-O_B(1).                                   (Z8)
```

Because `g(p)` is real,

```text
D_x(n^(-i alpha),g)=D_x(g,n^(i alpha)).                (Z9)
```

The triangle inequality for `D_x`, followed by `(Z8)`--`(Z9)`, gives directly

```text
Delta(x)-O_B(1)
 <= D_x(n^(-i alpha),n^(i alpha))^2
 <= 4D_x(g,n^(i alpha))^2.                             (Z10)
```

This proves `(Z3)`, including the case in which its right side is negative.  The factor `1/4`
is exactly the loss from reflection through a real
coefficient sequence.

## Cellwise GHS transfer `[PAPER-PROVED]`

Let `Y>=X^(1/4)`, `1<=|t|<=X^A`, and define

```text
h(n)=g(n)n^(-it).
```

Assume `(Z2)` at every scale comparable with `Y`.  Let `L_h(Y)` be the GHS Lorentzian Euler norm.
Then

```text
L_h(Y)/log Y
 <= C_A(exp(-Delta(Y)/4)+1/|t|).                       (Z11)
```

### Proof

On the GHS cell centred at an integer `j`, the Euler product of `h` is evaluated at frequency

```text
alpha=t+j+O(1).
```

All but `O(1)` cells have `|alpha|>=1`; the cell range in the definition of `L_h` also gives
`|alpha|<=Y^(4A+4)`.  On those ordinary cells, `(Z3)` and the Euler-distance inequality imply

```text
|H_Y(1+iv)|
 <= C log Y exp(-Delta(Y)/4).                          (Z12)
```

On the `O(1)` cells meeting `alpha=0`, use the trivial `C log Y` Euler bound.  Their centres
satisfy `|j|` comparable with `|t|`, so their Lorentzian weights are `O(t^(-2))`.  Sum the
squared cell bounds and take a square root.  This gives `(Z11)`.

Applying the sharp GHS theorem to `h`, using monotonicity of

```text
u |-> u log(C log Y/u),
```

and then partial summation gives the dyadic reciprocal polynomial bound

```text
|sum_(Y<=n<=2Y) g(n)n^(-1-it)|
 <= C_A exp(-Delta(Y)/4)(1+Delta(Y))
      +C_A (1+log(2+|t|))/|t|
      +C_A log log Y/log Y.                            (Z13)
```

Indeed, if `rho=L_h(Y)/log Y`, the GHS main term is `rho log(C/rho)`.  For `a,b>0`,

```text
(a+b)log(C/(a+b)) <= a log(C/a)+b log(C/b),            (Z13a)
```

whenever the displayed entropy terms lie in their increasing range.  Take
`a=exp(-Delta/4)` and `b=1/|t|`; bounded complementary cases are absorbed into the constant.
Then `a log(C/a)<<a(1+Delta)` and
`b log(C/b)<<b(1+log(2+|t|))`.  This exact entropy split is essential for subpower deficits:
replacing it by the crude `rho log log Y` loses the Littlewood saving.  No frequency-uniform
pretentious minimum is substituted after twisting; exceptional antitwist cells retain their
original Lorentzian weights.

## Power-law corollary and exact constants

If, for some `0<=theta<1`,

```text
|zeta(1+1/log x+i tau)| <= C_B (log x)^theta,           (Z14)
```

then `(Z2)` holds with

```text
Delta(x)=(1-theta)log log x-O_B(1).                    (Z15)
```

Consequently

```text
D_x(g,n^(i alpha))^2
 >= (1-theta)/4*log log x-O_B(1),                      (Z16)

L_h(x)/log x
 <= C_B((log x)^(-(1-theta)/4)+1/|t|).                 (Z17)
```

If `|t|>=(log X)^eta`, `(Z13)` supplies every exponent strictly below

```text
min(eta,(1-theta)/4).                                  (Z18)
```

For the classical Vinogradov--Korobov one-line exponent `theta=2/3+o(1)`, `(Z16)` is

```text
D_x(g,n^(i alpha))^2 >= (1/12-o(1))log log x,
```

which is precisely the constant in the published MR real-valued separation lemma.  With
`eta=1/16`, the antitwist cell, not ordinary cells, is the bottleneck; the frozen Halász card's
`1/17` follows after absorbing `log log X`.

For the corpus Littlewood deficit `(Z2d)`, `(Z13)` instead gives the unconditional qualitative
rate

```text
|sum_(Y<=n<=2Y) g(n)n^(-1-it)|
 <= C_A (log log Y)^(-1/4) log log log Y
      +C_A (1+log(2+|t|))/|t|
      +C_A log log Y/log Y.                            (Z18a)
```

In particular this is `o_A(1)` uniformly when
`(log X)^eta<=|t|<=X^A` and `Y>=X^(1/4)`.  Littlewood does not recover a fixed negative power of
`log X`; it closes exactly the qualitative real-twist/Halász subclause.

## Boundary classification for the grown corpus

The current Lean corpus now contains:

- `RHTower/Sieve/ZeroFreeRegionKappaOne.lean`: unconditional width
  `1/(10000 log|gamma|)`;
- `ZetaLogDerivRegionBound.lean`: `zeta'/zeta=O(log^2|gamma|)` inside that region;
- `DirichletOrderRate.lean` and `ZetaLineRate.lean`: the derivative-test Littlewood rate
  `|zeta(1+it)|<<log|t|/log log|t|`;
- `ZetaLogPrimeSum.lean`, `PrimeCosineSum.lean`, and `PrimeCosineSumUpper.lean`: the exact Euler,
  tail, and abscissa-shift transfers used in `(Z4)`--`(Z7)`;
- `MultiplicativeDistance.lean` and `FrequencySeparation.lean`: distance algebra;
- the GHS Lorentzian/cell infrastructure used in `(Z11)`.

The exponent-one zero-free region alone still gives only the boundary one-line scale

```text
|zeta(1+it)| << log|t|,
```

which corresponds to `theta=1` when `|t|` is a power of `x`.  Equation `(Z16)` then has zero
logarithmic gap.  Thus `ZeroFreeRegionKappaOne` is enough for classical PNT decay but not, by
itself, for the MR real-twist power saving.  The separate Littlewood chain, however, proves
`(Z2c)` and hence positive subpower deficit `(Z2d)`.  This closes qualitative real-twist
separation without Vinogradov--Korobov.

There are two rate classes of surviving upgrade relevant to this consumer:

1. a power deficit `theta<1` (Vinogradov--Korobov gives `theta=2/3+o(1)`), producing a
   `(log X)^(-c)` MR saving;
2. an unbounded subpower deficit, provided its entropy-decayed form
   `exp(-Delta/4)(1+Delta)` tends to zero.  In particular

   ```text
   log|zeta(1+it)| <= log log x-c log log log x+O(1),
   ```

   produces `(log log X)^(-c/4)log log log X` through `(Z13)`.  Every fixed `c>0` is enough for
   an `o(1)` consumer.  The corpus Littlewood theorem supplies `c=1`.

The second option is strictly weaker than a fixed `theta<1` and is the correct minimal target if
Route E only consumes convergence without a rate.

## Exact impact on Route E `[HOSTILE AUDIT]`

The grown corpus closes one auxiliary wall, not Route E's source theorem.  Combining `(Z18a)` with
the smooth/rough factorization in the sharp Halász card gives an `o(1)` long-factor estimate for
the real-twist Matomäki--Radziwiłł polynomial.  This removes Vinogradov--Korobov from any consumer
that needs only qualitative decay.  A consumer demanding the published fixed log-power still needs
a power deficit such as `(Z14)`.

Route E's current hard core is stronger and differently typed: physical-power breaking of the
literal moving-boundary Gibbs parity-class escape, or equivalently a source-specific coherent
cross-prime theorem before scalarization.  Halász/MR controls frequency-averaged fluctuation and
does not control the surviving coherent block mean.  Therefore `(Z18a)` reduces the analytic
same-parity subclause but does not imply the `x^(1/2-o(1))` normalized-current bound.

## Polynomial-horizon antiscale frame `[PAPER-PROVED] [NEW CORPUS CONSEQUENCE]`

The same Littlewood transfer gives a genuinely stronger Route E frame theorem than the former
`log log x-7log log T` estimate.  For every fixed `B>0` and all sufficiently large `x`,

```text
inf_(|t|<=x^B) sum_(p<=x) |1+p^(it)|^2/p
  >= (1/2)log log log x-O_B(1).                         (Z18b)
```

### Proof

First suppose `1<=|t|<=x^B`.  Let `lambda` be the completely multiplicative function with
`lambda(p)=-1`.  Then

```text
D_x(lambda,n^(it))^2=sum_(p<=x)(1+cos(t log p))/p,
sum_(p<=x)|1+p^(it)|^2/p=2D_x(lambda,n^(it))^2.         (Z18c)
```

Apply `(Z3)` with the Littlewood deficit `(Z2d)` and the horizon exponent enlarged by one to
obtain `(Z18b)` in this range.

Now suppose `|t|<=1`.  On the compact rectangle
`1<=Re(s)<=2`, `|Im(s)|<=1`, the pole-removed function `(s-1)zeta(s)` is continuous and
nonzero.  Hence `|zeta(1+1/log x+it)|` has an absolute positive lower bound.  The two-sided
Euler comparison `(Z2a)` with the plus sign therefore gives

```text
sum_(p<=x)(1+cos(t log p))/p >= log log x-O(1).         (Z18d)
```

This is stronger than `(Z18b)` and completes the proof.

Thus the growing-prime bounded-horizon nonrecurrence statement `(Z21)` is no longer open as a
statement: the Littlewood chain proves it with an unbounded `log log log x` margin throughout
every polynomial clock.  What remains open is a direct prime-clock proof independent of zeta and,
for Route E, transport from this common harmonic frame into prefix-dependent literal Gibbs weights
without losing the coherent block mean or the required physical power.

## Finite-prime hypertranscendence is not a substitute `[PAPER-PROVED NO-GO]`

The grown HTGeometry corpus proves rational independence of finite prime-log packets and
Kronecker density of their diagonal flow.  That structure does not force uniform twist
dissipation; it forces recurrent near-alignment.

Let `P` be any fixed finite set of primes.  For every `epsilon>0` and `T_0>0`, there is
`t>T_0` such that

```text
max_(p in P) |p^(it)-1|<epsilon.                        (Z19)
```

### Proof

Choose `p_0 in P`.  The numbers

```text
1, log p/log p_0  (p in P, p!=p_0)
```

are rationally independent: clearing denominators and exponentiating any rational relation would
give a nontrivial equality between products of distinct primes.  Discrete Kronecker approximation
therefore makes

```text
q |-> (q log p/log p_0 mod 1)_(p!=p_0)
```

dense in the finite torus.  It enters every neighbourhood of zero at arbitrarily large positive
integers `q`.  Taking `t=2pi q/log p_0` aligns `p_0` exactly and proves `(Z19)` for all other
coordinates.

There is also a quantitative aperture obstruction.  Suppose `2 in P`, put `m=|P|-1`, and let
`Q>=2`.  The pigeonhole proof of simultaneous Dirichlet approximation produces

```text
1<=q<=Q^m,
max_(p in P, p!=2) dist(q log p/log 2,Z)<=1/Q.          (Z19b)
```

Thus, for `t=2pi q/log 2`,

```text
1<t<=2pi/log 2*Q^m,
max_(p in P)|p^(it)-1|<=2pi/Q.                         (Z19c)
```

At any fixed tolerance `epsilon`, take `Q>=2pi/epsilon`.  If

```text
(2pi/epsilon)^(|P|-1) <= c x^B,                        (Z19d)
```

then a near-complete alignment occurs inside the target horizon `1<t<=x^B` after adjusting the
absolute constant.  Consequently a fixed-tolerance bounded-horizon nonrecurrence proof based on a
prime prefix needs at least `Omega_B(log x)` active prime coordinates.  Infinite prime-frequency
rank is therefore qualitatively necessary but quantitatively insufficient; aperture growth rate is
the missing datum.

Consequently

```text
sum_(p in P) (1-cos(t log p))/p
 <= epsilon^2/2 * sum_(p in P) 1/p.                    (Z20)
```

The same conclusion holds for every finite collection of prime-clock derivatives: a derivative
only multiplies the recurring phase by a fixed power of `log p`.  Hence no theorem depending on a
fixed finite prime packet, any fixed jet order, or only finite-dimensional prime-log algebraic
independence can imply a positive twist gap uniformly at unbounded frequencies.

This is not a no-go against the HTGeometry corpus.  It identifies its correct role.  The exact
replacement statement is a **growing-prime bounded-horizon nonrecurrence theorem**:

```text
P=P(x) grows,       1<=|t|<=x^B,
sum_(p in P(x)) (1-cos(2t log p))/p >= Delta(x).        (Z21)
```

Unlike `(Z19)`, the recurrence time of a torus whose dimension grows with `x` need not fit inside
`x^B`.  By `(Z2a)`, equation `(Z21)` is the prime-clock geometric form of `(Z2)`, equivalent up
to an absolute constant.  The Littlewood route now proves `(Z21)` for `P(x)={p:p<=x}` and
`Delta(x)=log log log x-O_B(1)`.  A direct HTGeometry proof would remain a genuine alternative
architecture, but it needs quantitative bounded-horizon exclusion, not more algebraic
independence or hypertranscendence.  Existing
`HTGeometry/PrimeTorusKroneckerDensity.lean` proves the qualitative recurrence side;
`PrimeFrequencyInfiniteRank.lean` proves growth of frequency rank.  Neither controls the first
return time as the aperture grows.

## Conjecture/failure loop

1. `[CONJECTURE]` Any exponent-one zero-free region closes the MR real-frequency separation.
   `[FALSIFIED]` It permits one-line growth at the full `log t` scale, so `(Z16)` has coefficient
   zero.  `[SURVIVOR]` Track the one-line deficit `Delta`, not zero-free width alone.
2. `[CONJECTURE]` After twisting, the fixed-horizon Halász distance can be reused uniformly.
   `[FALSIFIED]` The cell meeting `-t` has zero effective frequency.  `[SURVIVOR]` Its Lorentzian
   weight is `O(t^(-2))`, producing the exact `1/|t|` escape term in `(Z11)`.
3. `[CONJECTURE]` The Vinogradov--Korobov `1/16` in MR comes from its ordinary real-distance
   cells.  `[FALSIFIED]` Those cells allow exponent almost `1/12`; threshold
   `|t|>=(log X)^(1/16)` makes the antitwist cell the bottleneck.  `[SURVIVOR]` Formula `(Z18)`
   separates the two sources and permits independent optimization.
4. `[CONJECTURE]` Prime-log hypertranscendence can replace the analytic zeta deficit directly.
   `[FALSIFIED]` Every fixed finite prime torus has the unbounded near-returns `(Z19)`.
   `[POSITIVE SURVIVOR]` Bounded-horizon nonrecurrence requires growing aperture.  The Littlewood
   chain now proves its exact statement `(Z21)` analytically; a direct geometric proof remains open.
5. `[CONJECTURE]` The corpus's Littlewood theorem is confined to `Re(s)=1` and cannot feed the
   shifted Euler comparison.  `[FALSIFIED]` Its block estimates are prefix-uniform, so Abel
   weighting by `n^(-1/log x)` costs at most two; the retained zeta truncation proves `(Z2c)`.
   `[POSITIVE SURVIVOR]` The corpus already supplies `Delta=log log log x-O(1)`.
6. `[CONJECTURE]` A subpower deficit is destroyed by the logarithm in sharp Halász.
   `[FALSIFIED]` This uses the crude bound `rho log log Y`.  The exact entropy split `(Z13a)` gives
   `exp(-Delta/4)(1+Delta)`.  `[POSITIVE SURVIVOR]` Littlewood produces explicit `o(1)` rate
   `(Z18a)`.

## Lean notes only

No Lean was written or built.  Later formalization should first state `(Z2)` as an abstract
one-line deficit hypothesis.  Prove `(Z3)` using the existing prime-series comparison and distance
triangle before choosing a zeta theorem.  This keeps the sharp Halász theorem independent of
Vinogradov--Korobov and makes every future one-line improvement an interchangeable input.
For `(Z2c)`, reuse the arbitrary-terminal-block prefix estimate in `DirichletBlockAbel`, then one
Abel weighting and `ZetaPartialSumTruncation`; do not rebuild the derivative test.  For the low
frequency half of `(Z18b)`, use `riemannZeta_ne_zero_of_one_le_re` on the pole-removed compact
rectangle and the existing two-sided Euler/prime-shift lemmas.

## Gates

- [x] 0 -> 1: exact missing quantitative invariant identified
- [x] 1 -> 2: zeta deficit -> real distance -> GHS cell norm proved
- [x] exact zeta-deficit/prime-clock-energy identity proved
- [x] exponent-one corpus theorem classified at the correct boundary
- [x] corpus Littlewood rate transported to the shifted Euler abscissa
- [x] exact GHS entropy loss retained; Littlewood qualitative MR saving proved
- [x] polynomial-horizon growing-prime antiscale frame proved
- [x] power and subpower surviving targets separated
- [x] finite-prime hypertranscendence route falsified; growing-aperture survivor isolated
- [ ] 2 -> 3: paused by user during Lean corpus refactor

## Log

- 2026-08-08 -- extracted during hostile review of the weighted MR transfer; a hidden appeal to
  real-frequency separation was exposed and replaced by the quantitative deficit law.
- 2026-08-08 -- corpus-growth reorientation found the completed Littlewood line-rate chain.
  Prefix-uniform Abel transport proves shifted deficit `(Z2d)`; exact GHS entropy then proves
  qualitative MR rate `(Z18a)` without Vinogradov--Korobov.  Reflection through the Liouville
  character also proves polynomial-horizon antiscale coercivity `(Z18b)`.
