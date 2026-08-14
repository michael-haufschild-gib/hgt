# Gamma transport and prime-normal flow have the same physical corona

- **ID:** `suzuki-gamma-prime-normal-corona-equivalence`
- **Stage:** 3 — formalized in Lean 4
- **Type:** EXACT CORONA SEQUENCE / PRIME--GAMMA COMPARISON
- **Scientific status:** `[PROVED HERE] [NEW SCIENTIFIC KNOWLEDGE]`
  `[NOVELTY UNVERIFIED] [NOT RH]`
- **Inputs:** `suzuki-gamma-homogeneous-half-log-scattering-classification.md`,
  `suzuki-prime-normal-binomial-resolvent.md`
- **Route:** Connes/CCM restricted-Weil form through Suzuki completed zero modes

## 1. Result

Let \(X\) be a complex Hilbert space, let \(T=T^*\in\mathcal B(X)\), and let
\(\mathcal G_T\) be the physical terminal-half-line representatives of the tempered homogeneous
solutions of

```text
(2L I+R-T)F'(L)+F(L)=0,                                (1)
```

where \(R\) is the literal polar--Gamma jump.  Let

```text
N=L2((L_0,infinity);X)                                 (2)
```

for any sufficiently large \(L_0\).  The exact Gamma scattering theorem assigns to every
\(F\in\mathcal G_T\) a half-log trace

```text
tau(F)=beta in X,
F(L)=L^(-1/2)beta+O_X(L^(-1)).                         (3)
```

Then:

1. \(\tau:\mathcal G_T\to X\) is a surjective linear map;
2. its kernel is exactly the physical square-integrable homogeneous sector:

   ```text
   ker(tau)=G_T intersect N;                            (4)
   ```

3. consequently there is a canonical short exact corona sequence

   ```text
   0 -> G_T intersect N -> G_T -> X -> 0;               (5)
   ```

4. the prime-normal binomial resolvent

   ```text
   P_T(beta)(L)=(L I-T/2)^(-1/2)beta                   (6)
   ```

   is a cross-section of `(5)` modulo \(N\): for every Gamma solution \(F\),

   ```text
   F-P_T(tau(F)) belongs to N.                          (7)
   ```

Equivalently, the literal Gamma jump creates no additional non-\(L^2\) corona direction and
removes none.  Complete dense prime transport and complete Gamma transport have the same
singular physical quotient, namely one copy of the half-log trace space \(X\).

For Suzuki's support-pruned carrier, take

```text
X=H_a,
T=T_a^Gamma=-T_a.                                      (8)
```

This closes prime--Gamma coupling at the singular-corona level.  It does **not** construct the
completed-source forcing or the exterior/Feshbach return.

## 2. Exactness of the Gamma corona sequence

The homogeneous Gamma classification gives unique frequency channel vectors \(c_+,c_-\in X\)
and

```text
tau(F)
 =1/(2 sqrt(pi))
  [exp(i pi/4)c_+ + exp(-i pi/4)c_-].                  (9)
```

This map is surjective: for prescribed \(\beta\), choose

```text
c_+=2 sqrt(pi) exp(-i pi/4) beta,
c_-=0.                                                 (10)
```

The resulting homogeneous solution has trace \(\beta\).

If \(\tau(F)=0\), the exact upper-strip gluing theorem gives

```text
exp(sigma L)F in L2((L_0,infinity);X)
for every 0<sigma<1,                                   (11)
```

so \(F\in N\).

Conversely, suppose \(\beta=\tau(F)\ne0\).  From `(3)`, there are \(C,L_1>0\) such that

```text
||F(L)-L^(-1/2)beta|| <= C L^(-1)                      (12)
```

for \(L\ge L_1\).  Increase \(L_1\) until \(C L^{-1}\le
\|\beta\|L^{-1/2}/2\).  The reverse triangle inequality gives

```text
||F(L)|| >= (||beta||/2)L^(-1/2).                      (13)
```

Therefore

```text
integral_(L_1)^infinity ||F(L)||^2 dL
 >=(||beta||^2/4) integral_(L_1)^infinity dL/L
 =infinity.                                            (14)
```

Thus \(F\notin N\).  This proves `(4)`, and linearity and surjectivity give exactness of `(5)`.
`QED`

## 3. The prime resolvent is the canonical corona model

For \(L>\|T\|/2\),

```text
P_T(beta)(L)
 =L^(-1/2)(I-T/(2L))^(-1/2)beta.                       (15)
```

On \(L\ge \|T\|\), the scalar derivative of \((1-x)^{-1/2}\) is uniformly bounded for
\(|x|\le1/2\).  Continuous functional calculus therefore gives

```text
||(I-T/(2L))^(-1/2)-I|| <= C_T/L.                      (16)
```

Hence

```text
P_T(beta)(L)=L^(-1/2)beta+O_X(L^(-3/2)).               (17)
```

Subtracting `(17)` from the exact Gamma asymptotic `(3)` yields

```text
F(L)-P_T(tau(F))(L)=O_X(L^(-1)).                       (18)
```

The right-hand side is square integrable on every terminal half-line, proving `(7)`.

The cross-section is faithful modulo \(N\).  If \(\beta\ne0\), estimate `(17)` gives the same
lower bound as `(13)`, so \(P_T(\beta)\notin N\).  Thus

```text
beta |-> [P_T(beta)]
```

embeds \(X\) into the ambient physical corona, and `(7)` says its image is exactly the image of
the Gamma homogeneous sector. `QED`

## 4. All prime words survive in one corona representative

The exact expansion

```text
P_T(beta)(L)
 =sum_(k>=0)
   [binom(2k,k)/8^k]L^(-k-1/2)T^k beta                (19)
```

shows what `(7)` identifies.

- Grade zero is the entire non-\(L^2\) class \(L^{-1/2}\beta\).
- Every prime descendant \(k\ge1\) is already in \(N\).
- The Gamma jump changes the chosen \(N\)-representative, but not the class.
- Colliding dense prime words are already summed inside \(T^k\); no seam separation is used.

For Suzuki's \(\ell^1\) valuation realization with prime mass \(M_a\), the descendant series is
nuclear on every tail \(L_0>M_a/2\).  Thus the full dense prime tree is a concrete, positive,
source-normalized representative of the same corona class detected abstractly by Gamma
scattering.

## 5. Exact frontier movement

Before this comparison, the open connector was described as a Duhamel coupling of prime breadth
to the Gamma jump.  That description was too large.  At the only singular physical level relevant
to half-log completion, no such coupling remains:

```text
prime breadth:
  exact binomial corona representative;                [CLOSED]

Gamma jump:
  changes representative by physical L2 only;          [CLOSED MOD L2]

low-frequency band:
  two endpoint counterterms plus Gamma-subcritical
  remainder;                                           [CLOSED LOCALLY]

completed exterior/Feshbach source:
  prove its forced correction belongs to the exact
  physical L2 domain and obeys the cutoff equation.     [OPEN SOURCE CORE] (20)
```

The next theorem must therefore be source-bearing.  It must identify the literal completed
zero-mode forcing \(G_{\mathrm{ext}}\), on the support-pruned/Feshbach carrier, and prove solvability
of

```text
(2L I+R-T)E'(L)+E(L)=G_ext(L)                           (21)
```

with \(E\in N\), with the two matched endpoint counterterms and the exact cutoff identity.  A
generic abstract Duhamel estimate that never constructs \(G_{\mathrm{ext}}\) would not move the
route.

## 6. Hostile audit

1. **Not equality of solutions.**  \(P_T(\beta)\) solves the prime equation, not the Gamma
   equation.  The theorem asserts equality of their physical corona classes only.
2. **No false injective trace.**  Gamma has nonzero trace-zero upper-strip solutions.  They lie
   in \(N\) and are exactly why `(5)` is a quotient statement.
3. **No hidden converse.**  The lower bound `(13)` proves nonzero trace is incompatible with
   physical \(L^2\); `(4)` is an iff, not only the previously known forward implication.
4. **No Fourier-tail deletion.**  The \(O(L^{-1})\) Gamma remainder used in `(18)` includes the
   complete high-frequency Gamma phase.
5. **No source theorem claimed.**  Exterior elimination, endpoint injection, cutoff commutators,
   and Feshbach return are inhomogeneous and absent from \(\mathcal G_T\).
6. **No whole-Connes verdict.**  Direct prolate and Euler--Gamma incidence producer classes remain
   live independently of this Suzuki subroute.

## 7. Novelty boundary

Short exact sequences, asymptotic comparison modulo \(L^2\), and the binomial resolvent are
classical mechanisms.  Candidate-new source knowledge is the exact Suzuki identification

```text
literal Gamma homogeneous corona
 = prime-normal binomial corona
 = half-log trace space H_a,                            (22)
```

with every dense valuation word contained in the explicit representative `(19)`.  Corpus search
found no previous statement of `(5)`, `(7)`, or `(22)`.  External priority remains unverified.

## 8. Lean decision

The load-bearing ingredients already have unconditional Lean certificates:

```text
SuzukiGammaStripCarrierIntegrability.lean
SuzukiVolterraLogGradeRecurrence.lean
```

The new implication `(3)` plus `(17)` implies `(7)` by the elementary integrability of
\(L^{-1}\).  Formalizing only that asymptotic bookkeeping while the vector-valued oscillatory
Fourier theorem `(3)` remains paper-only would be theorem theatre.  The correct formal target is
the source-bearing forced-domain theorem `(21)`, after the concrete completed-source carrier and
cutoff intertwiner have been constructed.

## Gates

- [x] prove Gamma trace map is surjective
- [x] prove zero trace iff physical homogeneous \(L^2\)
- [x] derive exact corona sequence
- [x] compare Gamma solution to prime binomial cross-section modulo \(L^2\)
- [x] retain complete high-frequency Gamma phase
- [x] retain all colliding prime valuation words
- [ ] construct literal completed exterior/Feshbach forcing
- [ ] prove forced \(L^2\) domain solvability with matched endpoint counterterms
- [ ] prove exact cutoff-equation intertwining
- [ ] identify two-ended corona packet with raw Evans packet
- [ ] RH or whole-program no-go
