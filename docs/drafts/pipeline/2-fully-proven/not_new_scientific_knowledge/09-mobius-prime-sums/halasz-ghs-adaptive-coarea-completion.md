# Sharp Halász by adaptive prime mean square and reciprocal cofactor shells

- **ID:** `halasz-ghs-adaptive-coarea-completion`
- **Stage:** `2-fully-proven`
- **Type:** `THEOREM (paper) [LITERATURE] [BRIDGE] [PAPER-PROVED]`
- **Source:** `../../1-in-progress/halasz-ghs-proof-map.md` and
  `../../1-in-progress/mr-splice-wide-range-mean-square.md`
- **Statement:** The Granville--Harper--Soundararajan sharp form of Halász's theorem follows
  unconditionally from a prime-supported mean square with a Brun--Titchmarsh level chosen
  separately at each prime, a geometric partition in the complementary variable
  `log(x/p)`, and a factor-aware truncated Perron error.  The same theorem supplies the
  Halász component of the weighted nonmultiplicative polynomial bound used by the
  Matomäki--Radziwiłł splice; its separate real-twist zeta input is exposed below.

## Status and novelty labels

- `[LITERATURE]` Sharp Halász theorem, triple convolution, prime mean-square lemma, cofactor
  shells, and the Matomäki--Radziwiłł weighted transfer are published arguments.
- `[CORPUS]` Required elementary arithmetic and analytic mechanisms already occur separately in
  `PNTPlus/BrunTitchmarsh.lean`, `RHTower/Sieve/GallagherAlmostDiagonal.lean`,
  `RHTower/Sieve/MultiplicativeLogRecursion.lean`, `SecondLogRecursion.lean`,
  `PerronFiniteSum.lean`, `RamareWeight.lean`, `SmoothSum.lean`, and `SmoothTilt.lean`.
- `[BRIDGE]` New project result is a dependency reduction: adaptive pointwise sieve choice and
  complementary-scale blocking replace the global sieve-level, p-dyadic Minkowski, and
  `p <= sqrt(x)` branches of the in-progress proof map.
- No external mathematical novelty is claimed in this card.

## Frozen theorem

Let `f : N -> C` be multiplicative in the ordinary coprime sense and satisfy `|f(n)| <= 1`.
For `x >= 3`, put

```text
S_f(x) = sum_(n <= x) f(n),

F_x(s) = product_(p <= x) (1 + sum_(j >= 1) f(p^j) p^(-js)),

L_f(x)^2 = sum_(|h| <= (log x)^2 + 1)
              1/(h^2+1) sup_(|t-h| <= 1/2) |F_x(1+it)|^2.
```

There is an absolute constant `C` such that

```text
|S_f(x)| <= C x L_f(x)/log x * log(100 log x/L_f(x))
            + C x log log x/log x.                         (H1)
```

Enlarging `C` handles the bounded range in which `100 log x/L_f(x)` is not already
bounded away from one.  If

```text
M_f(x) = min_(|t| <= (log x)^2+2)
           sum_(p <= x) (1-Re(f(p)p^(-it)))/p,
```

then

```text
|S_f(x)| <= C x ((1+M_f(x)) exp(-M_f(x))
                  + log log x/log x).                      (H2)
```

Every constant is absolute and no zero-free region, density theorem, RH, or unproved
hypothesis enters `(H1)`--`(H2)`.

## Lemma A: elementary prime and Euler bounds

The proof uses only the following absolute-constant estimates, for `2 <= a <= b`:

```text
theta(b) := sum_(p <= b) log p                         <= C b,       (A1)
sum_(p <= b) log p/p                                  <= C log b,  (A2)
sum_(a < p <= b) log p/p                              <= C(1+log(b/a)),
product_(p <= b) (1-1/p)^(-1)                         <= C log b.  (A3)
```

`(A1)` is Chebyshev.  Partial summation gives `(A2)` and `(A3)`; the last estimate is
Mertens' Euler-product upper bound.  Only upper bounds are used.

Two consequences will be used repeatedly.  Write `v_p = log(x/p)`.  If
`u <= v_p <= e u` and `u >= log 2`, then

```text
sum_p log p/(p v_p)       <= C,                         (A4)
sum_p log p/(p v_p^2)     <= C/u.                       (A5)
```

Indeed the primes lie in `(x exp(-eu), x exp(-u)]`, whose logarithmic endpoint
difference is `(e-1)u`.  Apply `(A3)` and divide by `u` or `u^2`; its additive constant
is absorbed because `u >= log 2`.  Also

```text
sum_(q <= exp(eu)) log q/q <= C u.                      (A6)
```

## Lemma B: adaptive Gallagher--Brun--Titchmarsh mean square

`[PAPER-PROVED]` There is an absolute `C` such that, for `T >= 1`, arbitrary complex
coefficients `a_p`, and `Y >= T^2`,

```text
int_(-T)^T | sum_(T^2 <= p <= Y) a_p log p / p^(1+it) |^2 dt
  <= C sum_(T^2 <= p <= Y) |a_p|^2 log p/p.             (B1)
```

The point of `(B1)` is one `log p`, not `(log p)^2`, on the right.

### Proof

Gallagher's almost-diagonal inequality, after the harmless normalization `t = 2 pi w`,
reduces the left side to

```text
C T sum_p |b_p|^2 N_T(p),

b_p = a_p log p/p,
N_T(p) = #{q prime : |log(q/p)| <= c/T}.                (B2)
```

The multiplicative window in `(B2)` is an ordinary interval of length `H_p <= C p/T`.
Since `p >= T^2`, its natural sieve length is at least a constant multiple of `p/T >= T`.
Apply the Selberg Brun--Titchmarsh bound

```text
pi(z+H)-pi(z) <= 2H/log Z + 6Z(1+log Z)^3              (B3)
```

with `Z = sqrt(H)` at each value of `p`, not once globally.  For large `H`, the error
in `(B3)` is at most a constant multiple of `H/log H`.  This follows directly from

```text
sqrt(H)(1+log H)^3 = o(H/log H).
```

The remaining bounded values of `H` are absorbed by increasing the absolute constant.
Moreover `p >= T^2` gives

```text
log H >= c log p
```

outside another bounded range: `H` is comparable to `p/T`, and
`log(p/T) >= (log p)/2`.  Thus

```text
N_T(p) <= C p/(T log p).                                (B4)
```

Substitution of `(B4)` in `(B2)` gives

```text
T |b_p|^2 N_T(p)
 <= C T |a_p|^2 (log p)^2/p^2 * p/(T log p)
 =  C |a_p|^2 log p/p.
```

Summing proves `(B1)`.  All level choices are deterministic functions of the current
prime and `T`; no distributional hypothesis is hidden in the proof.  This is exactly why a
single global pair `(z,Y)` is the wrong interface for this lemma.

## Lemma C: logarithmic recursion for ordinary multiplicative functions

`[PAPER-PROVED]` Uniformly for `y >= 3`,

```text
S_f(y)
 = 1/log y sum_(pm <= y, p prime) f(p)f(m) log p
   + O(y/log y).                                        (C1)
```

### Proof

Use `log n = sum_(d|n) Lambda(d)`:

```text
sum_(n <= y) f(n) log n
 = sum_(dm <= y) Lambda(d) f(dm).                       (C2)
```

Replace `d` by a prime `p` and `f(pm)` by `f(p)f(m)`.  The discarded `d=p^j`,
`j>=2`, contribute at most

```text
y sum_p sum_(j>=2) log p/p^j <= C y.                    (C3)
```

For `d=p`, multiplicativity can fail only when `p|m`; that contribution is at most

```text
2y sum_p log p/p^2 <= C y.                              (C4)
```

Hence `(C2)` equals the prime double sum up to `O(y)`.  Finally

```text
sum_(n <= y) |log(y/n)| <= C y,
```

by comparison with `int_1^y log(y/t) dt`.  Replacing `log n` by `log y` in `(C2)`
therefore costs `O(y)`, proving `(C1)`.

Applying `(C1)` a second time at `y=x/p` gives

```text
S_f(x)
 = 1/log x sum_(log^4 x < p <= x/2)
       f(p) log p/log(x/p)
       sum_(qn <= x/p) f(q)log q f(n)
   + O(x log log x/log x).                              (C5)
```

For the error, sum `(x/p)/log(x/p)` against `log p/log x`; `(A4)` after geometric
blocking gives `O(x log log x/log x)`.  The omitted primes `p <= log^4 x` cost the
same amount by `(A2)`, and `p>x/2` cost `O(x/log x)` by `(A1)`.

This proof is the missing ordinary-multiplicative correction to the corpus recursion, whose
present theorem assumes `f(ab)=f(a)f(b)` without a coprimality condition.  It is required for
Möbius and for the general Matomäki--Radziwiłł input.

## Lemma D: reciprocal cofactor shells

Put

```text
u_k = exp(-k) log x,
P_k = {p prime : log^4 x < p <= x/2,
                   u_k < log(x/p) <= e u_k}.            (D1)
```

The nonempty shells have `1 <= k <= log log x + O(1)`.  Define

```text
S_k(x) = sum_(p q n <= x, p in P_k)
           f(p)log p/log(x/p) * f(q)log q * f(n).        (D2)
```

Then `(C5)` becomes

```text
|S_f(x)|
 <= 1/log x sum_k |S_k(x)| + C x log log x/log x.       (D3)
```

The trivial estimate is

```text
|S_k(x)| <= C x exp(-k) log x.                          (D4)
```

Indeed sum first over `n`, use `# {n<=x/(pq)} <= x/(pq)`, then `(A4)` and `(A6)`.

## Lemma E: factor-aware truncated Perron error

`[PAPER-PROVED]` Let `T=(log x)^2`.  For every nonempty shell,

```text
S_k(x)
 = 1/(2 pi i) int_(1-iT)^(1+iT) A_k(s) B_k(s) F_x(s) x^s/s ds
   + O(x),                                              (E1)

A_k(s) = sum_(p in P_k) f(p)log p/(p^s log(x/p)),
B_k(s) = sum_(q <= exp(eu_k), q prime) f(q)log q/q^s.   (E2)
```

The error `O(x)` is uniform in `k`.

### Lattice estimate near the cutoff

For `X,d>0` and `T>=2`, ordering the multiples `dn` by distance from `X` gives

```text
sum_(X/(2d) <= n <= 2X/d)
  min(1, X/(T |X-dn|))
 <= C(1 + X log(2T)/(Td)).                              (E3)
```

There is at most one closest lattice point, contributing at most one.  On either side, the
`j`-th further point has distance at least `(j-1/2)d`; summing `1/j` only until the
minimum reaches one gives `(E3)`.

### Proof of `(E1)`

The truncated Perron error is bounded by

```text
sum_(p in P_k) sum_(q <= exp(eu_k)) sum_(P+(n)<=x)
  log p/log(x/p) * log q * x/(pqn)
  * min(1, 1/(T |log(x/(pqn))|)).                       (E4)
```

Split `(E4)` according as `1/2 <= x/(pqn) <= 2`.

On the near part, `|log(x/(pqn))|` is comparable to `|x-pqn|/x`.  Apply `(E3)`
with `d=pq`.  Since the near condition also forces `q <= 2x/p`, `(A1)`, `(A4)`,
and `(A6)` give

```text
E_near
 <= C sum_(p in P_k) log p/log(x/p)
          sum_(q <= min(exp(eu_k),2x/p)) log q
             (1 + x log T/(Tpq))
 <= Cx + C x u_k log T/T
 <= Cx.                                                 (E5)
```

On the far part, `|log(x/(pqn))|` is bounded below by an absolute constant.  Absolute
summation and `(A3)` give

```text
sum_(P+(n)<=x) 1/n
 = product_(r<=x) (1-1/r)^(-1) <= C log x.
```

Consequently

```text
E_far
 <= C x/T
      (sum_(p in P_k) log p/(p log(x/p)))
      (sum_(q <= exp(eu_k)) log q/q)
      (sum_(P+(n)<=x)1/n)
 <= C x u_k log x/T
 <= Cx.                                                 (E6)
```

Here `u_k<=log x` and `T=(log x)^2`.  Equations `(E5)`--`(E6)` prove `(E1)`.
This error estimate retains the `(p,q,n)` factorization; collapsing first to a uniformly
bounded one-dimensional coefficient sequence discards the two cancellations in `(E5)` and
manufactures a need for much larger height.

## Lemma F: the two reciprocal energies

For `T=(log x)^2`, all primes in `P_k` exceed `T^2`.  Lemma B and `(A5)` give

```text
I_1(k) := int_(-T)^T |A_k(1+it)|^2 dt
        <= C sum_(p in P_k) log p/(p log^2(x/p))
        <= C/u_k = C exp(k)/log x.                      (F1)
```

For the other two factors, split `[-T,T]` into unit intervals centered at integers `h`.
On the cell `|t-h|<=1/2`, pull out

```text
sup_(|v-h|<=1/2) |F_x(1+iv)|^2/(h^2+1).
```

Apply Lemma B with height one to `B_k`, after twisting its coefficients by `q^(-ih)`.
Using `(A6)` and the definition of `L_f(x)` gives

```text
I_2(k) := int_(-T)^T |B_k(1+it)|^2 |F_x(1+it)|^2/(1+t^2) dt
        <= C L_f(x)^2 u_k
        =  C L_f(x)^2 exp(-k)log x.                     (F2)
```

The factors `u_k^(-1)` and `u_k` are exact reciprocals.  Cauchy--Schwarz in `(E1)`
therefore yields

```text
|S_k(x)| <= Cx sqrt(I_1(k) I_2(k)) + Cx
          <= Cx(L_f(x)+1),                              (F3)
```

uniformly in `k`.  No restriction `p<=sqrt(x)` appears.

## Proof of the frozen theorem

Let

```text
K_0 = floor(log(100 log x/L_f(x))).
```

For `k<=K_0`, sum `(F3)`.  For `k>K_0`, sum the geometric tail `(D4)`.
Substitute both estimates in `(D3)`:

```text
|S_f(x)|
 <= C x L_f(x) K_0/log x
    + C x K_0/log x
    + C x exp(-K_0)
    + C x log log x/log x.
```

The second term is absorbed by the last because `K_0=O(log log x)`; the third is
`O(xL_f(x)/log x)`.  This proves `(H1)`.

For every `t`, Euler-product expansion and absolute convergence give

```text
log |F_x(1+it)|
 <= sum_(p<=x) Re(f(p)p^(-it))/p + C
 =  sum_(p<=x)1/p - D(f,n^(it);x)^2 + C.
```

Mertens' bound implies

```text
|F_x(1+it)| <= C log x exp(-D(f,n^(it);x)^2),
L_f(x)      <= C log x exp(-M_f(x)).                    (F4)
```

To insert `(F4)` in `(H1)`, one must keep the product with its logarithm; the
standalone inequality `log(100 log x/L_f(x)) << 1+M_f(x)` need not hold when
`L_f(x)` is exceptionally small.  Put

```text
Phi_x(u)=u log(100 log x/u).
```

This function is increasing on `0<u<=100 log x/e`.  If
`U=C log x exp(-M_f(x))` lies in that interval, `(F4)` gives

```text
Phi_x(L_f(x)) <= Phi_x(U)
              <= C log x (1+M_f(x))exp(-M_f(x)).        (F5)
```

For completeness, the Euler product and
`sum_(h in Z)1/(1+h^2)<4` give the independent numerical bound
`L_f(x)<=6log x` for all sufficiently large `x` (enlarge constants on the bounded range).
Replace `U` by `V=min(U,6log x)`.  Then `L_f(x)<=V<100log x/e`, so monotonicity applies.
If `V=U`, the displayed estimate proves `(F5)`; if `V=6log x`, the inequality `U>=6log x`
forces `M_f(x)=O(1)`, while `Phi_x(V)=O(log x)`, again proving `(F5)`.  Thus `(H1)`,
`(F5)` prove `(H2)` without a false standalone logarithm bound.

## Exact Matomäki--Radziwiłł consumer

Sharp Halász is consumed after a Buchstab/Ramaré weight has made the coefficient sequence
nonmultiplicative.  The required transfer is therefore recorded explicitly rather than hidden
under the phrase “apply Halász.”

Let `f : N -> [-1,1]` be multiplicative, `X>=Q>=P>=2`, put
`u=log X/log Q`, and assume the corridor used by the current Route-B consumer

```text
3 <= u <= sqrt(Q).
```

Define

```text
omega_[P,Q](n) = #{p in [P,Q] : p|n},
R_(P,Q)(s) = sum_(X<=n<=2X) f(n)n^(-s)/(omega_[P,Q](n)+1).
```

For fixed `A>0` and `(log X)^(1/16) <= |t| <= X^A`, one has the
route-B-sufficient bound

```text
|R_(P,Q)(1+it)|
 <= C_A log Q/((log X)^(1/17) log P)
    + C_A log X exp(-(log X)/(3log Q)
                       * log(log X/log Q)).             (MR1)
```

### Proof of `(MR1)`

Factor each `n` uniquely as `n=n_1n_2`, where every prime factor of `n_1` lies in
`[P,Q]` and no prime factor of `n_2` does.  If `n_1<=X^(3/4)`, hold `n_1` fixed.
The inner `n_2`-sum is a dyadic partial sum of the multiplicative function

```text
g(n)=f(n) 1_(no prime divisor of n lies in [P,Q]).
```

The additional published real-valued distance separation

```text
D(g,n^(it);Y)^2 >= c log log Y-O(1)
```

holds uniformly for `Y` between `X^(1/4)` and `2X`; it follows by the triangle
inequality from the zeta one-line bound used in MR Lemma 2.  It is unconditional, but it is
not a consequence of sharp Halász.  The exact dependency and the factor `1/13` are proved in
`../new_scientific_knowledge/real-twist-zeta-deficit-transfer-law.md`.  To apply `(H1)` to
`h(n)=g(n)n^(-it)`, inspect its `L`-sum cell by cell.  On the cell centred at the
integer `j`, its Euler frequency is `t+j+O(1)`.  Except for `O(1)` cells meeting
`|t+j+O(1)|<1`, the real-valued distance lemma applies.  Its constant may be fixed so
that

```text
D(g,n^(i alpha);Y)^2 >= (1/13)log log Y-O_A(1)          (MR2a)
```

whenever `1<=|alpha|<=Y^(4A+4)`.  The stated ranges of `t,j,Y` lie inside this
frequency window.  The Euler bound used in `(F4)` then gives `(log Y)^(12/13)` on
every ordinary cell.  On each exceptional cell use the trivial `O(log Y)` Euler
bound; because `|j|` is comparable to `|t|`, its weight is `O(t^(-2))`.  Summing the
cell weights and taking the square root proves

```text
L_h(Y)/log Y <= C_A((log Y)^(-1/13)+1/|t|).             (MR2b)
```

Insert `(MR2b)` in `(H1)`.  The logarithm in `(H1)` costs at most `O_A(log log X)`;
partial summation converts prefix sums to the reciprocal dyadic sum.  Since
`Y>=X^(1/4)` and `|t|>=(log X)^(1/16)`, both terms, including that logarithmic loss,
are `O_A((log X)^(-1/17))`.  Thus

```text
|sum_(Y<=n<=2Y) g(n)n^(-1-it)|
 <= C_A log log X/(log X)^(1/16)
 <= C_A (log X)^(-1/17).                               (MR2)
```

The last inequality holds after enlarging the constant over a bounded initial range.
The published parameterized Halász theorem gives exponent `1/16`; the slightly weaker
`1/17` is proved here from the frozen GHS `L`-form alone and is more than sufficient for
the MR large-value bookkeeping.

The grown RHTower corpus now supplies a second, weaker but self-contained input.  Its
Littlewood derivative-test chain proves the shifted bound

```text
|zeta(1+1/log Y+i alpha)| <<_A log Y/log log Y
```

uniformly for `1<=|alpha|<=Y^A`; the prefix-uniform Abel transport and exact deficit conversion
are proved on paper in
`../new_scientific_knowledge/real-twist-zeta-deficit-transfer-law.md`.  The resulting deficit is
`Delta(Y)=log log log Y-O_A(1)`.  Retaining the exact GHS entropy, rather than charging it by
`log log Y`, gives

```text
epsilon_LW(Y)
 = (log log Y)^(-1/4) log log log Y
   + (1+log(2+|t|))/|t| + log log Y/log Y,

|sum_(Y<=n<=2Y) g(n)n^(-1-it)| <<_A epsilon_LW(Y).     (MR2-LW)
```

Thus `epsilon_LW(Y)=o_A(1)` when `|t|>=(log X)^eta` and `Y>=X^(1/4)`.  This closes the
qualitative real-twist/Halász subclause without Vinogradov--Korobov.  It does not replace the
fixed log-power in `(MR1)` when downstream large-value bookkeeping explicitly consumes that rate.

The outer reciprocal mass is

```text
sum_(n_1 : p|n_1 => p in [P,Q])
  1/(n_1(omega(n_1)+1))
 <= product_(P<=p<=Q)(1-1/p)^(-1)
 <= C log Q/log P.                                     (MR3)
```

Equations `(MR2)`--`(MR3)` give the first term of `(MR1)`.

If `n_1>X^(3/4)`, then `n_2<=2X^(1/4)<X^(1/2)`.  Drop all signs.  The remaining
inner integers are `Q`-smooth and at least `X/n_2>=X^(1/2)`.  Rankin's trick gives,
uniformly for `Y>=X^(1/2)`,

```text
sum_(Y<=m<=2Y, P+(m)<=Q) 1/m
 <= C log X exp(-(log X)/(3log Q)
                    * log(log X/log Q)).                (MR4)
```

For completeness, take

```text
alpha = 3 log u/(4 log Q).
```

The corridor gives `0<alpha<=3/8`.  Rankin's inequality is

```text
1_(m>=Y)/m <= Y^(-alpha)m^(-1+alpha),
sum_(P+(m)<=Q)m^(-1+alpha)
 = product_(p<=Q)(1-p^(-1+alpha))^(-1).
```

Since `alpha<=3/8`, expanding the logarithm and summing the geometric powers gives

```text
log product_(p<=Q)(1-p^(-1+alpha))^(-1)
 <= C sum_(p<=Q) p^(-1+alpha).
```

Separating the Mertens product at `alpha=0` and applying partial summation to the
increment from `p^alpha-1` yields

```text
product_(p<=Q)(1-p^(-1+alpha))^(-1)
 <= C log Q exp(C u^(3/4)).                             (MR5)
```

For `Y>=X^(1/2)`, the Rankin prefactor is

```text
Y^(-alpha) <= exp(-(3/8)u log u).
```

For sufficiently large `u`, `C u^(3/4) <= (1/24)u log u`, so the combined exponent
is at most `-(1/3)u log u`.  For bounded `u`, the exponential on the right of `(MR4)`
is bounded below by a positive absolute constant while `(MR5)` is `O(log Q)`; this is
absorbed by the prefactor `log X`.  Thus `(MR4)` holds throughout the corridor.
Summing the `n_2` reciprocal mass contributes no more than the displayed `log X`.
This proves the second term of `(MR1)` and completes the weighted transfer in the
parameter corridor used by MR.

`(MR1)` is the exact structural role of sharp Halász in the Matomäki--Radziwiłł proof,
with an inessential `1/17` in place of the published `1/16`; ordinary `(H2)` alone must
not be advertised as completing that consumer.  The corpus now supplies the positive Littlewood
subpower deficit and hence `(MR2-LW)` at paper level; Vinogradov--Korobov remains necessary only
for the displayed fixed log-power version `(MR1)`.  The exponent-one zero-free region by itself
still lies on the zero-deficit boundary.

## Conjecture/failure loop and positive survivors

1. `[CONJECTURE]` Discard or induct away `p>sqrt(x)` so the outer quadratic mass is bounded.
   `[FALSIFIED]` The published sharp proof retains every `log^4 x<p<=x/2`; removing that range
   has main-term cost.  `[POSITIVE SURVIVOR]` Partition by `log(x/p)` and retain the dual
   cofactor length.
2. `[CONJECTURE]` A single global Selberg pair can be optimized after p-dyadic Minkowski.
   `[FALSIFIED]` Its additive fibre error forces a low level at the smallest block and the
   outer triangle sum preserves the manufactured loss.  `[POSITIVE SURVIVOR]` Choose the
   Brun--Titchmarsh level at each current prime inside the neighbour count, proving `(B1)`
   before any block summation.
3. `[CONJECTURE]` A generic uniform coefficient bound is the right Perron interface.
   `[FALSIFIED]` It forgets the hyperbolic product `pqn` and forces a much larger height.
   `[POSITIVE SURVIVOR]` The lattice estimate `(E3)` retains `p,q`; `(A4)` and `(A6)` then
   close the error already at `T=(log x)^2`.
4. `[CONJECTURE]` Standard sharp Halász is the complete MR input.
   `[FALSIFIED]` The long polynomial carries `1/(omega_[P,Q]+1)` and is not multiplicative.
   `[POSITIVE SURVIVOR]` The unique smooth/rough factorization plus the cellwise `(H1)` norm
   gives `(MR1)`.

## Lean formalization map -- notes only

No Lean was written or built while this card was produced.

1. Strengthen `PNTPlus.BrunTitchmarsh.primesBetween_le` to the pointwise logarithmic-window
   corollary `(B4)`.  Consume it directly in `GallagherAlmostDiagonal`; do not route through
   the fixed-parameter `PrimeLogWindowCount.logNeighbourCount_le_sieve`.
2. State `(B1)` as the reusable GHS prime mean-square theorem.  Existing
   `GeneralizedDirichletMeanValue` is an exact identity but does not supply prime sparsity;
   `LargeValuesDuality` serves later MR large-value steps, not `(B1)`.
3. Generalize `MultiplicativeLogRecursion` from complete multiplicativity to coprime
   multiplicativity by formalizing errors `(C3)`--`(C4)`.  Existing Mertens tail theorems
   already bound both series.
4. Introduce cofactor shells `(D1)`, not p-dyadic blocks.  Reuse the existing quotient-window
   estimates and prime Mertens bounds.
5. Formalize the lattice lemma `(E3)` and factor-aware error `(E4)`--`(E6)` next to
   `PerronFiniteSum`; do not first convolve into a coefficient sup bound.
6. Assemble `(F1)`--`(F3)` and `(H1)` in a new capstone.  Existing Euler-distance modules
   then give `(H2)`.
7. For the MR consumer, reuse `RamareWeight`, `SmoothRough`, `SmoothSum`, and `SmoothTilt` to
   formalize `(MR1)` as a separate theorem.  It must not be folded into the sharp Halász
   declaration.

## Hostile closure audit

- No p-range is discarded except the two ranges whose total contributions were evaluated.
- Prime-square and noncoprime errors are included, so Möbius is covered.
- Brun--Titchmarsh levels depend only on `p,T`, never on coefficients or cancellation.
- Perron near/far errors include the infinite x-smooth Euler tail.
- Every use of Cauchy--Schwarz occurs after complementary support lengths are frozen.
- The MR nonmultiplicative weight is transferred explicitly.
- The separate real-twist zeta deficit used by MR is exposed rather than attributed to sharp
  Halász.
- This card proves a known theorem and a known consumer bridge; it does not claim RH, the full
  Matomäki--Radziwiłł theorem, or Route E's coherent Hall/seam statement.

## Gates

- [x] 0 -> 1: exact sharp theorem, consumer, and false branches identified
- [x] 1 -> 2: dependency-closed paper proof of `(H1)`--`(H2)`
- [x] adaptive prime mean square `(B1)` proved from corpus-grade Brun--Titchmarsh
- [x] ordinary-multiplicative recursion correction included
- [x] factor-aware polylog-height Perron error included
- [x] MR weighted transfer `(MR1)` included
- [x] literature/corpus novelty labels separated
- [ ] 2 -> 3: paused by user during corpus refactor; no Lean changes in this pass

## Primary sources

- A. Granville, A. J. Harper, K. Soundararajan, *A more intuitive proof of a sharp
  version of Halász's theorem* (2018).
- A. Granville, A. J. Harper, K. Soundararajan, *A new proof of Halász's theorem, and
  its consequences*, arXiv:1706.03749.
- K. Matomäki, M. Radziwiłł, *Multiplicative functions in short intervals*,
  arXiv:1501.04585.
- S. Menon, *Improved bounds for multiplicative functions in almost all short intervals*,
  arXiv:2607.15574.  This latest refinement confirms that final prime ranges and their
  complementary cofactors must remain coupled; it does not justify deleting large primes.

## Log

- 2026-08-08 -- paper completion written after falsifying the `p<=sqrt(x)` branch and
  replacing three globalized estimates by adaptive/complementary-scale statements.
