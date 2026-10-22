# Suzuki critical-radical anchoring and finite-head reduction

- **ID:** `suzuki-critical-radical-anchor-finite-head-reduction`
- **Stage:** 3 — formalized in Lean 4
- **Type:** THEOREM / SUZUKI SAFE-SHIFT COERCIVITY
- **Scientific status:** `[PAPER-PROVED] [UNCONDITIONAL] [SOURCE-SPECIFIC]`
  `[CANDIDATE-NEW-MECHANISM] [NOVELTY-SEARCHED] [NOT AN RH PROOF]`
- **Parents:** `suzuki-safe-shift-response-charge-cancellation`,
  `suzuki-safe-shift-transverse-charge-budget`
- **RH used:** no
- **Lean status:** fully formalized; every `[PROVED]` statement has an unconditional Lean declaration

## Result

At Suzuki's safe shift, write

```text
lambda_q = xiShiftedReciprocalSquare(1,q),
a_q      = Re(lambda_q),
tau_q    = Re(lambda_q^2)/a_q,
chi_q    = Im(lambda_q)^2 |lambda_q|^2/a_q,
A        = sum_q a_q.
```

The known exact decomposition is

```text
AC-B^2 = H-Q,
H = A sum_q a_q tau_q^2-(sum_q a_q tau_q)^2,
Q = A sum_q chi_q.
```

This card proves two new statements.

1. **Critical-radical anchoring.** One critical-line Xi atom pays the transverse charge of every
   atom outside a finite response head. Consequently there is a finite set `F` such that

   ```text
   H > A sum_(q notin F) chi_q,
   AC-B^2 > -A sum_(q in F) chi_q.                       (SR-64.1)
   ```

   Thus the complete infinite tail cannot be the source of a negative Suzuki safe minor. Any
   failure is carried by finitely many off-line response atoms.

2. **Quantitative annular payment.** If an off-line copy `q`, of squared ordinate `h`, has two
   critical-line copies with squared ordinates in

   ```text
   [3h,(432/25)h],                                       (SR-64.2)
   ```

   then their two cross-dispersion terms strictly exceed the complete-mass-normalized transverse
   charge of `q`. The published unconditional bound `liminf N_0(T)/N(T)>5/12` forces such a
   witness pair for every sufficiently high `q`. Hence `(SR-64.1)` also has a height-tail form.

The first statement needs only existence of a critical-line zero and the safe-shift sector. The
second exposes an exact scale match between the factor `5/12` and the annulus
`[sqrt(3)T,(12 sqrt(3)/5)T]`; it is retained because it is the route toward an effective finite
head.

## Conjecture loop

### SR-64A: strict dispersion alone pays all charge `[FALSE]`

`H>0` and `Q` small do not imply `H>=Q`. A finite packet can place an off-line atom at the same
response slope as its background and make its cross-dispersion arbitrarily small while retaining
positive transverse charge. The existing absolute cap on `Q` does not repair this.

### SR-64B: a zero-charge atom makes the response tail coercive `[PROVED]`

A critical-line atom has positive response mass, zero transverse charge, and a fixed positive
slope. All other shifted slopes and shifted atom norms tend to zero off finite sets. Cross terms
with that one fixed atom therefore stay bounded below relative to each tail mass, while transverse
charge divided by that mass tends to zero. This is the missing asymptotic degree separation.

### SR-64C: the cofinite reduction is only qualitative `[FALSE]`

The relative-scale refinement is quantitative. Two critical-line copies in `(SR-64.2)` pay one
off-line copy with the exact margin

```text
32/675 - 29/625 = 425/421875 > 0.                        (SR-64.3)
```

The five-twelfths theorem supplies the required critical-line copies at all sufficiently high
relative scales.

### SR-64D: annular payment proves the safe wall `[FAILS AT A FINITE HEAD]`

The positive-proportion theorem is asymptotic and supplies no explicit starting height in the form
needed here. It eliminates the complete high tail but does not pay the remaining finite low atoms.
Promoting `(SR-64.1)` to `H>Q` requires a finite-head certificate, a source-side proof of the
equivalent theta skewness wall, or an effective critical-line anchor budget. None is proved here.

## Complete paper proof

### 1. Pairwise form of the Hilbert dispersion

All terms below are nonnegative and the parent cards prove the required absolute summability.
Finite exhaustion, followed by monotone convergence, gives

```text
H = (1/2) sum_(q,r) a_q a_r (tau_q-tau_r)^2.             (SR-64.4)
```

Indeed, on every finite set,

```text
(1/2) sum_(q,r) a_q a_r(tau_q-tau_r)^2
 = (sum_q a_q)(sum_q a_q tau_q^2)-(sum_q a_q tau_q)^2.
```

The full identity follows because `sum a_q`, `sum a_q tau_q`, and `sum a_q tau_q^2` converge.
Equivalently, each unordered pair `{q,r}` contributes exactly

```text
a_q a_r(tau_q-tau_r)^2.                                 (SR-64.5)
```

### 2. A fixed critical-line radical atom pays the cofinite tail

Choose a critical-line Xi copy `r`. Existence is unconditional; for example it follows from the
classical theorem that infinitely many zeta zeros lie on the critical line. Put

```text
c=a_r=tau_r=1/(1+Im(r)^2)>0,   chi_r=0.                 (SR-64.6)
```

The safe sector gives, for `lambda_q=a+ib`,

```text
84 b^2<a^2.
```

Therefore

```text
chi_q/a_q
 =(b^2/a^2)|lambda_q|^2
 <|lambda_q|^2/84.                                      (SR-64.7)
```

The parent theorem proves, on the cofinite filter,

```text
tau_q -> 0,   |lambda_q| -> 0.                           (SR-64.8)
```

Since `A>0`, there is a finite set `F`, enlarged to contain `r`, such that for every `q` outside
`F`,

```text
tau_q<c/2,
A |lambda_q|^2/84<c^3/4.                                (SR-64.9)
```

Equations `(SR-64.7)--(SR-64.9)` imply

```text
a_r(tau_q-tau_r)^2
 > c(c/2)^2
 = c^3/4
 > A chi_q/a_q.
```

After multiplication by `a_q>0`,

```text
a_q a_r(tau_q-tau_r)^2>A chi_q.                         (SR-64.10)
```

The unordered pairs `{q,r}`, for `q` outside `F`, are all distinct. Extracting precisely those
nonnegative summands from `(SR-64.4)` and summing `(SR-64.10)` gives

```text
H>A sum_(q notin F) chi_q.                               (SR-64.11)
```

Subtracting `Q=A sum_q chi_q` proves `(SR-64.1)`. Because the Xi divisor is locally finite, `F`
is contained in some finite height window. In particular, if all copies in `F` lie on the critical
line, then their charges vanish and

```text
AC-B^2=H-Q>0.                                           (SR-64.12)
```

This is a finite-head implication, not an unconditional proof that the head is charge-free.

### 3. Exact coordinates for one off-line atom

Let `q` be off the critical line and write

```text
u = Re(q)-1/2,
h = Im(q)^2,
X = 1+h-u^2,
Y = -2u Im(q),
D = X^2+Y^2.
```

At the safe shift,

```text
lambda_q = 1/(X+iY),
a_q      = X/D,
tau_q    = (X^2-Y^2)/(X D),
chi_q/a_q=Y^2/(X^2 D).                                  (SR-64.13)
```

The unconditional strip, height, sector, and source-mass inputs are

```text
u^2<1/4,
h>295/2,
84Y^2<X^2,
A<29/625.                                               (SR-64.14)
```

Only `h>141/2` is needed below; the stronger `295/2` is already proved in the source corpus
without zero computation.

### 4. Uniform charge bound at the atom's own height

From `(SR-64.13)` and `D>=X^2`,

```text
chi_q/a_q <=Y^2/X^4<h/(h+3/4)^4.                        (SR-64.15)
```

The last inequality uses `Y^2=4u^2h<h` and `X>h+3/4`. The exact polynomial identity

```text
(h+3/4)^4-h(1+h)^3
 = (3/8)h^2+(11/16)h+81/256>0                          (SR-64.16)
```

turns `(SR-64.15)` into

```text
A chi_q/a_q<29/[625(1+h)^3].                            (SR-64.17)
```

### 5. Two critical-line witnesses pay this charge

The sector in `(SR-64.14)` gives

```text
tau_q
 >(83/85)/X
 >83/[85(1+h)].                                         (SR-64.18)
```

Let `r` be a critical-line copy and put `k=Im(r)^2`. If

```text
3h<=k<=(432/25)h,
```

then

```text
a_r=tau_r=1/(1+k),
a_r>=25/[432(1+h)].                                     (SR-64.19)
```

Also

```text
(tau_q-tau_r)(1+h)
 >83/85-(1+h)/(1+3h)
 =(164h-2)/[85(1+3h)]
 >16/25.                                                (SR-64.20)
```

The final inequality is equivalent to `h>141/2`, already contained in `(SR-64.14)`. Hence one
witness contributes

```text
a_r(tau_q-tau_r)^2
 > [25/432][256/625]/(1+h)^3
 =16/[675(1+h)^3].                                      (SR-64.21)
```

For two distinct critical-line copies `r_1,r_2` in the band, `(SR-64.21)` and `(SR-64.17)` give

```text
sum_(j=1)^2 a_(r_j)(tau_q-tau_(r_j))^2
 >32/[675(1+h)^3]
 >29/[625(1+h)^3]
 >A chi_q/a_q.                                          (SR-64.22)
```

The middle inequality is exactly `(SR-64.3)`. Multiplication by `a_q` proves the quantitative
annular payment theorem.

### 6. Five-twelfths forces the annular witnesses cofinally

Let `N(T)` count positive-ordinate nontrivial zeros with multiplicity and `N_0(T)` count those on
the critical line. Pratt--Robles--Zaharescu--Zeindler prove

```text
liminf_(T->infinity) N_0(T)/N(T)>5/12.                  (SR-64.23)
```

Set

```text
alpha=sqrt(3),   beta=12sqrt(3)/5.
```

Choose `kappa>5/12` below the liminf. The Riemann--von Mangoldt asymptotic gives

```text
N_0(beta T)-N_0(alpha T)
 >=kappa N(beta T)-N(alpha T)
 =[(kappa beta-alpha)/(2pi)+o(1)]T log T.                (SR-64.24)
```

Here

```text
kappa beta-alpha
 =sqrt(3)(12kappa/5-1)>0.                               (SR-64.25)
```

Thus every sufficiently large `T` has a positive-ordinate critical-line zero in
`[alpha T,beta T]`. Schwarz symmetry supplies its distinct negative-ordinate copy. These two
multiplicity copies have squared ordinates in `[3T^2,(432/25)T^2]` and therefore satisfy
`(SR-64.22)`.

For every sufficiently high off-line copy `q`, choose this conjugate witness pair with
`T=|Im(q)|`. Pairs selected for distinct off-line multiplicity copies remain distinct even when
the same critical-line witness is reused. Extracting all selected pairs from the nonnegative
double sum `(SR-64.4)` proves

```text
H>A sum_(q off-line, |Im(q)|>=T_*) chi_q                (SR-64.26)
```

up to adding harmless nonnegative terms; if the displayed tail is empty, strictness follows from
the already-proved strict dispersion law. Consequently

```text
AC-B^2
 >-A sum_(q off-line, |Im(q)|<T_*) chi_q.               (SR-64.27)
```

This is the height-tail form of the finite-head reduction.

## Hostile audit

1. **No global sign claim.** `(SR-64.1)` and `(SR-64.27)` leave a finite transverse head. They do
   not prove `H>=Q`, the safe wall, Suzuki convergence, or RH.
2. **No strict-sum sleight of hand.** Pairwise dispersion is a nonnegative double series. The
   selected pairs are injectively indexed by the off-line copy and therefore cannot be counted
   twice. One strict selected term already makes the summed inequality strict.
3. **Multiplicity is correct.** `N`, `N_0`, and `XiZeroCopy` count multiplicity. The positive and
   negative copies of one nonzero critical-line ordinate are distinct and legitimately provide
   the two terms in `(SR-64.22)`.
4. **No numerical zero verification.** Constants come from exact rational inequalities, the
   source-proved off-line height band, and the published asymptotic proportion theorem.
5. **No misuse of density.** `(SR-64.24)` uses `N_0(alpha T)<=N(alpha T)` and the full
   Riemann--von Mangoldt asymptotic. Positive global proportion alone would not imply an additive
   short-interval zero; the multiplicative annulus is essential.
6. **No generic positivity theorem.** A single off-line atom is still negative. Coercivity comes
   specifically from cross pairs with zero-charge critical-line atoms and from the different
   tail orders of response and charge.
7. **Finite does not mean verified.** The threshold `T_*` inherited from the proportion theorem
   is not made explicit. Calling the remaining head computationally closed would be false.
8. **Other Suzuki gates remain.** Source-selected two-angle meromorphic normality,
   nondegeneration, and Xi/de Branges identification are untouched.

## Novelty and significance boundary

- Classical inputs: the pairwise variance identity, existence and positive proportion of
  critical-line zeros, Riemann--von Mangoldt zero counting, and elementary inverse-coordinate
  algebra.
- Existing corpus: exact safe-shift response/charge cancellation, sector `84Y^2<X^2`, source mass
  `A<29/625`, off-line height gap, cofinite slope decay, and strict total dispersion.
- New candidate mechanism: a zero-charge critical-line atom is a **radical anchor** that makes the
  complete Suzuki response tail coercive against transverse charge; the infinite RH obstruction
  localizes to a finite head. The quantitative refinement gives the exact two-copy annular payment
  and the scale match `5/12 <-> [sqrt(3),12sqrt(3)/5]`.
- Targeted searches of the repository and broad current arXiv searches for Xi reciprocal Hankel
  determinants, Turan inequalities, critical-line zero density, and weighted reciprocal-zero
  dispersion found no statement of `(SR-64.1)`, `(SR-64.22)`, or `(SR-64.27)`. Priority remains
  subject to specialist review.
- The theorem moves the Suzuki target frontier: the safe-shift obstruction is no longer an
  uncontrolled competition over the whole Xi divisor. It does not by itself clear a standalone
  journal significance threshold because a finite, non-effective head remains.

## Lean handoff after refactor

Read-only providers already present:

```text
formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiSafeShiftResponseChargeCancellation.lean
formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiSafeShiftTransverseChargeBudget.lean
formal/GaloisForLFunctions/RHTower/SquaredXiCompleteMonotonicity.lean
formal/GaloisForLFunctions/RHTower/XiCenteredOrdersSeventeenEighteenSourcePositivity.lean
```

Future formalization should first add a reusable pairwise infinite-variance identity, then prove
the fixed-anchor cofinite theorem. The annular corollary additionally needs formal providers for
Riemann--von Mangoldt and the published `>5/12` theorem; no hypothesis wrapper or axiom should be
introduced in their place.

## References

- K. Pratt, N. Robles, A. Zaharescu, D. Zeindler, *More than five-twelfths of the zeros of zeta
  are on the critical line*, Research in the Mathematical Sciences 7 (2020), Article 2,
  arXiv:1802.10521.
- H. M. Bui, B. Conrey, M. P. Young, *More than 41% of the zeros of the zeta function are on the
  critical line*, Acta Arithmetica 150 (2011), 35--64, arXiv:1002.4127.

## Gates

- [x] fixed-radical-anchor cofinite payment proved
- [x] pair extraction and no-double-counting proved
- [x] exact atomwise height-charge bound proved
- [x] exact two-witness annular payment proved
- [x] five-twelfths multiplicative-annulus coverage proved
- [x] internal collision search
- [x] broad current arXiv collision search
- [ ] specialist priority audit
- [ ] finite-head charge elimination
- [ ] safe-shift minor positivity
- [ ] source-selected two-angle Suzuki limit and Xi identification
- [ ] RH

## Log

- 2026-08-08 — Conjectured annular critical-line payment after rejecting the false inference that
  strict response dispersion must exceed the explicit charge cap.
- 2026-08-08 — Proved exact two-witness constants, derived the five-twelfths annulus, then found the
  stronger radical-anchor principle showing that only a finite response head can obstruct the safe
  wall.

## Sharpening — the five-twelfths constant is an artefact of using two witnesses

`(SR-64.22)` fixes the number of critical-line witnesses at two, and that choice alone is what
forces the tight band `(SR-64.2)` and hence the input `(SR-64.23)`.  Nothing in sections 4–5 uses
the count.

### SR-64.28 Tail-sum form of the annular payment `[PROVED]`

Let `q` be off the critical line with `h=Im(q)^2>141/2`, and let `S` be any finite set of
critical-line copies with squared ordinates `k_r>=3h`. Sections 4 and 5 give, for each `r in S`,

```text
a_r(tau_q-tau_r)^2 > (16/25)^2 a_r/(1+h)^2,   a_r = 1/(1+k_r),
A chi_q/a_q < 29/[625(1+h)^3].
```

Therefore the whole payment condition is the single scalar inequality

```text
sum_(r in S) 1/(1+k_r) > 29/[256(1+h)].                  (SR-64.28)
```

Specialisation check: two witnesses in the card's band `[3h,(432/25)h]` give
`50/[432(1+h)] = 0.115740.../(1+h)` against `29/256 = 0.113281...`, which is exactly the margin
`(SR-64.3)`. So `(SR-64.22)` is the two-element case of `(SR-64.28)`.

### SR-64.29 Any fixed annulus suffices if it carries enough witnesses `[PROVED]`

Put `Gamma=sqrt(3h)` and let `S` consist of `n` conjugate witness pairs with ordinates in
`[Gamma,K Gamma]` for a fixed `K>1`. Then `1+k_r <= 1+K^2 Gamma^2` for each, so the left side of
`(SR-64.28)` is at least `2n/(1+K^2Gamma^2)`, and `(SR-64.28)` holds as soon as

```text
n >= (87/512)K^2.                                        (SR-64.29)
```

`K` is fixed, so the required witness count is a **constant**. The band ratio is no longer capped.

### SR-64.30 The required zero-counting input drops below every published proportion `[PROVED]`

Consequently the annular payment theorem needs only

```text
exists K>1, exists C, exists Gamma_0, for all Gamma>=Gamma_0:
  #{critical-line ordinates in [Gamma,K Gamma]} >= C.    (SR-64.30)
```

Three ways to obtain `(SR-64.30)`, in decreasing strength:

1. Any positive proportion `liminf N_0(T)/N(T)>=kappa>0`, with `K>1/kappa`: then
   `N_0(K Gamma)-N_0(Gamma) >= kappa N(K Gamma)-N(Gamma) -> infinity`. Selberg (1942) suffices;
   Pratt--Robles--Zaharescu--Zeindler is not needed.
2. Hardy--Littlewood's 1921 gap theorem, `N_0(T+H)-N_0(T) >> H` for `H=T^(3/4+eps)`: on `[Gamma,2Gamma]`
   this already gives `>> Gamma` witnesses, so `K=2` works and no proportion theorem is used.
3. Any lower bound `N_0(T) >> T^delta`, `delta>0`, combined with the same partial-summation step
   applied to the full tail rather than to one annulus.

Riemann--von Mangoldt enters only in route 1, to convert a proportion into an annular count. Under
route 2 it is not used at all. The `riemann-von-mangoldt-zero-counting` card is therefore no longer
on the critical path for gate five.

The exact scale match `5/12 <-> [sqrt(3),12 sqrt(3)/5]` recorded in the novelty boundary is real,
but it is the *two-witness* optimum, not a feature of the mechanism. The optimum two-witness band
ratio is `(255/83)*(1250/29)*(83/85-83/255)^2 = 5.945...` in the squared ordinate, i.e. `2.438...`
in the ordinate, which corresponds to the threshold `kappa>0.4102...`; the card's `[sqrt(3),12sqrt(3)/5]`
attains `2.4` and threshold `5/12`. Both are superseded by `(SR-64.30)`.

## Sharpening II — the witnesses need not be on the critical line

`(SR-64.28)` restricted the witnesses to critical-line copies purely because that is where the
coordinates `a_r = tau_r = 1/(1+k_r)` are explicit. The strip bound already pins both coordinates of
an **arbitrary** copy. With `X = 1 + k - u`, `Y^2 = 4uk` for `k = Im(r)^2`, `u = (Re(r)-1/2)^2 < 1/4`,

```text
tau_r = (X^2-Y^2)/(X(X^2+Y^2)) <= 1/X <= 1/(k+3/4),   (SR-64.31)
a_r   = X/(X^2+Y^2)            >= 1/(k+3),            (SR-64.32)
```

the second because `X(k+3) - X^2 = X(2+u) >= 2k+3/2 > 4uk = Y^2`.

### SR-64.33 The general payment criterion `[PROVED]`

Substituting `(SR-64.31)` for the witness slope, the sector gap `(SR-64.18)` still leaves

```text
tau_q - tau_r > 83/[85(1+h)] - 143/[425(1+h)] = 16/[25(1+h)]
```

as soon as `k_r >= 3(1+h)` — the band floor moves from `3h` to `3(1+h)`, nothing else changes. So
for an arbitrary finite family `S` of Xi copies with `k_r >= 3(1+h)`,

```text
sum_(r in S) a_r >= 29/[256(1+h)]                       (SR-64.33)
```

pays the complete-mass-normalized charge of `q`, and by `(SR-64.32)` a fixed annulus
`k_r <= 3K^2(1+h)` clears `(SR-64.33)` once it carries

```text
#S >= (87/256)K^2 + 1                                   (SR-64.34)
```

copies. **The critical line has left the statement.** The zero-counting input is therefore no
longer a proportion theorem, nor even a critical-line counting theorem: it is

```text
exists K>1, exists Gamma_0, for all Gamma >= Gamma_0:
  #{Xi zeros with |ordinate| in [Gamma, K Gamma]} >= (87/256)K^2 + 1.   (SR-64.35)
```

which is plain Riemann--von Mangoldt counting.  Under the two-sided bound
`c_1 T log T <= N(T) <= c_2 T log T` any `K > c_2/c_1` works, since
`N(K Gamma) - N(Gamma) >= (c_1 K - c_2) Gamma log Gamma` grows while the required count is a
constant. Selberg, Hardy--Littlewood and Pratt--Robles--Zaharescu--Zeindler are all off the critical
path; the five-twelfths layer of `riemann-von-mangoldt-zero-counting` is not needed at all.

Hardy's theorem is likewise not needed for `(SR-64.1)`: the anchored cofinite payment holds for an
*arbitrary* anchor copy, because the anchor's own charge is absorbed into the finite head.

## Gates (revised)

- [x] tail-sum form of the annular payment
- [x] fixed-annulus witness-count criterion
- [x] reduction of the zero-counting input below every published proportion theorem
- [x] Lean: the tail-sum payment inequality
      — `RHTower/Suzuki/SuzukiAnnularTailSumPayment.lean`
- [x] removal of the critical-line restriction on the witnesses
      — `RHTower/Suzuki/SuzukiGeneralWitnessAnnularPayment.lean`
- [x] provider: the qualitative anchor of `(SR-64.1)` — not needed; the anchored payment
      `RHTower.exists_finset_anchor_payment` holds for an arbitrary anchor
- [x] provider: one unconditional instance of `(SR-64.35)` — closed
      — `RHTower/XiAnnularCopyCount.lean`, `RHTower.exists_annular_copies`, built on the four
      closed gates of `riemann-von-mangoldt-zero-counting`

## Log (continued)

- 2026-08-16 — Removed the five-twelfths dependence: the payment condition is a tail sum, the
  witness count is free, and the annulus ratio is therefore unconstrained. Recorded the
  two-witness optimum `2.438...` and its threshold `0.4102...` for the record, and retired the
  Riemann--von Mangoldt provider from the critical path.

- 2026-08-17 — Removed the critical line from the payment criterion. The strip bound alone gives
  `tau_r <= 1/(k_r+3/4)` and `a_r >= 1/(k_r+3)` for every copy, so the witnesses may be arbitrary Xi
  zeros and the required input is plain zero counting `(SR-64.35)`, not a proportion theorem. Also
  recorded that `(SR-64.1)` needs no critical-line anchor at all: the Lean statement
  `RHTower.exists_finset_anchor_payment` is proved for an arbitrary anchor, since the anchor's own
  charge sits inside the finite head. Both remaining literature providers of the previous gate list
  are therefore retired, and the single open input is the Riemann--von Mangoldt annular count.

- 2026-08-17 (later) — **The zero-counting provider is closed and the card moves to Stage 3.**

  `(SR-64.35)` is now an unconditional Lean theorem.  The chain, all in
  `formal/GaloisForLFunctions/`:

  ```text
  RHTower/XiRectangleZeroCount.lean      (1/2πi)∮ ξ'/ξ = divisor mass          [gate C]
  RHTower/GammaVerticalPhaseAsymptotic   ∫₀^T Re ψ(σ+it) dt ~ T log T          [gate D]
  RHTower/ZetaStripPolynomialBound       ‖ζ‖ ≤ 2 + 8|Im s| right of 1/4
  RHTower/ZetaRealTraceDiscCount         Backlund: #zeros of Re ζ ≤ c log T    [gate E]
  HTGeometry/ArgumentVariationSignChanges |Δ arg| ≤ (#sign changes + 1)π
  RHTower/XiLogDerivSymmetry             the two symmetries of ξ'/ξ
  RHTower/XiRectangleFold                the quarter-path formula
  RHTower/XiVerticalPhaseTwo             the vertical splitting and its two π-bounds
  RHTower/ZetaHorizontalArgument         the constructed branch of log ζ
  HTGeometry/DistinctZerosLeDivisor      #distinct zeros ≤ divisor mass
  RHTower/XiHorizontalBound              |∫ Im(ξ'/ξ)| = O(log T)               [gate F]
  RHTower/XiVerticalRatioLimit           the vertical ratio is 1/2
  RHTower/XiSymmetricMassBounds          (1/2π)T log T ≤ mass ≤ (2/π)T log T
  RHTower/XiAdmissibleHeights            admissible heights are dense; annular mass
  RHTower/XiOrdinateBandCopies           mass difference = band copy count
  RHTower/XiAnnularCopyCount             exists_annular_copies                 [(SR-64.35)]
                                         exists_annular_payment_of_large_height
  ```

  The final statement is unconditional and hypothesis-free in the aperture:

  ```text
  exists_annular_payment_of_large_height :
    ∃ h₀, ∀ q : XiZeroCopy, h₀ ≤ Im(q)²,
      ∃ S : Finset XiZeroCopy,
        A · χ_q < a_q · Σ_{r ∈ S} a_r (τ_q − τ_r)².
  ```

  Two things made this reachable.  First, `(SR-64.33)` removed the critical line from the payment,
  so the counting input became plain Riemann--von Mangoldt rather than a proportion theorem.
  Second, the sharp asymptotic was never needed: the two-sided constants `1/2π` and `2/π` differ by
  a factor four, so an annulus of ratio `10` is comfortable and the required witness count
  `(87/256)·10² + 1 = 35` copies is supplied with room to spare.
