# Ramification-power phase/history time-dilation law

- **ID:** `cfr-ramification-power-phase-history`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper) / THIRD OBSERVER-DOCTRINE RESPONSE
- **Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [BRIDGE] [PARENT-ROUTINE TIME REPARAMETRIZATION] [SAME SOURCE POWER MORPHISM] [NOT A WORMHOLE THEOREM] [NOT RH] [FORMALIZED IN LEAN]`
- **Formalized companion:** `ramification-power-phase-history-time-dilation-law-formalized.md`
- **Statement:** Under the same shell power morphism `P_r:m->rm`, the observed finite-prime phase orbit and its torus closure are unchanged up to time reparametrization, while the marked universal-cover history, generator, and fixed-clock homogeneous costs dilate by exact powers of `r`.

## Goal

Test the physical-time component of CFR on the already constructed source-law event. No new source
arrow may be introduced. The theorem must distinguish:

- compact recurrent observed closure;
- open lifted history;
- external-clock normalization;
- path cost.

It must not infer a black-hole interior, wormhole length, or quantum complexity from recurrence
alone.

## 1. Finite prime phase observer

Fix a finite nonempty prime set `F`. Let `H_F=C^F` with basis `(e_p)_(p in F)`, and write

\[
 \lambda=(\log p)_{p\in F}\in\mathbb R^F.
\tag{PH.1}
\]

For integer shell depth `m>=2`, define the diagonal generator and its unitary flow by

\[
 D_me_p=m\log p\,e_p,
 \qquad
 U_m(t)e_p=e^{-itm\log p}e_p.
\tag{PH.2}
\]

Let

\[
 \mathcal O_m=\{U_m(t):t\in\mathbb R\}
\tag{PH.3}
\]

inside the diagonal unitary torus `T^F`. Mark the lift beginning at the origin,

\[
 h_m(t)=-tm\lambda\in\mathbb R^F,
 \qquad
 \exp(ih_m(t))=U_m(t).
\tag{PH.4}
\]

Here `exp:R^F->T^F` is the ordinary finite-dimensional universal covering map.

## 2. Exact time dilation under the source power event

Let `r>=2` be an integer. The source morphism is the same arithmetic map from the preceding card:

\[
 P_r(k)=k^r,
 \qquad
 a_{rm}(P_r(k))=a_m(k).
\tag{PH.5}
\]

### Theorem 2.1 — observed orbit invariance and lifted dilation

One has

\[
 \boxed{
 D_{rm}=rD_m,
 \qquad
 U_{rm}(t)=U_m(rt),
 \qquad
 h_{rm}(t)=rh_m(t).}
\tag{PH.6}
\]

Consequently

\[
 \boxed{
 \mathcal O_{rm}=\mathcal O_m,
 \qquad
 \overline{\mathcal O_{rm}}=\overline{\mathcal O_m}.}
\tag{PH.7}
\]

After compensating the external clock,

\[
 U_{rm}(t/r)=U_m(t),
 \qquad
 h_{rm}(t/r)=h_m(t).
\tag{PH.8}
\]

### Proof

On each prime basis vector,

\[
 D_{rm}e_p=rm\log p\,e_p=rD_me_p,
\]

and exponentiation gives `U_(rm)(t)=U_m(rt)`. Formula `(PH.4)` gives the lift identity. Since
`t->rt` is a bijection of `R`, the two orbit sets coincide, proving `(PH.7)`. Substitution
`t->t/r` proves `(PH.8)`. `[PROVED HERE]`

Thus phase-orbit geometry treats ramification depth as a clock gauge, while a fixed external clock
sees an exact dilation.

### Corollary 2.2 — fixed-clock representation separation

For nonempty `F` and `r>1`, the fixed-clock representations `U_m` and `U_(rm)` are not linearly
conjugate. If `|F|>=2`, they are not projectively conjugate either.

### Proof

Linear conjugacy for every `t` would, after differentiation at zero, conjugate `D_m` to `D_(rm)`.
But

\[
 \operatorname{tr}D_{rm}=r\operatorname{tr}D_m\ne\operatorname{tr}D_m,
\]

because every prime logarithm is positive. For projective conjugacy, scalar characters may shift
the generator by a multiple of the identity, but cannot change centered spectral variance. That
variance is nonzero for at least two distinct primes and scales by `r^2`, so projective conjugacy
is impossible. `[PROVED HERE]`

## 3. Dense recurrence and open history

### Theorem 3.1 — compact recurrent closure, unbounded marked lift

The common orbit in `(PH.7)` is dense in `T^F`. In particular, there are arbitrarily large return
times `t_j` such that

\[
 U_m(t_j)\longrightarrow I,
\tag{PH.9}
\]

while

\[
 \|h_m(t_j)\|=m|t_j|\|\lambda\|\longrightarrow\infty.
\tag{PH.10}
\]

### Proof

The character annihilator of the one-parameter subgroup is

\[
 \left\{(n_p)\in\mathbb Z^F:
 \sum_{p\in F}n_p m\log p=0\right\}.
\]

Divide the displayed sum by the positive integer `m`. Exponentiation then gives

\[
 \prod_{p\in F}p^{n_p}=1.
\]

Unique factorization forces every `n_p=0`. The character criterion for subgroups of a torus
therefore gives `closure(O_m)=T^F`. The continuous Kronecker recurrence theorem then supplies
arbitrarily large returns to every neighborhood of the identity. Formula `(PH.10)` follows
directly from `(PH.4)` and `lambda!=0`. `[PROVED HERE]`

This is the precise finite theorem behind “compact recurrent observer closure with open lifted
history.” The orbit itself is dense and generally not closed when `|F|>=2`.
It is not caused by hypertranscendence: only prime-log character independence is used.

## 4. Cost response and clock gauge

Let `Phi:R^F->[0,infinity)` be continuous and positively `q`-homogeneous for some `q>0`:

\[
 \Phi(cx)=c^q\Phi(x)\qquad(c\ge0).
\tag{PH.11}
\]

For `T>=0`, define endpoint cost and fixed-clock action

\[
 K_m(t)=\Phi(h_m(t)),
 \qquad
 \mathcal A_m(T)=\int_0^T\Phi(\dot h_m(t))\,dt
 =T\Phi(-m\lambda).
\tag{PH.12}
\]

### Theorem 4.1 — exact homogeneous cost dilation

At fixed external time,

\[
 \boxed{
 K_{rm}(t)=r^qK_m(t),
 \qquad
 \mathcal A_{rm}(T)=r^q\mathcal A_m(T).}
\tag{PH.13}
\]

For the same geometric lifted path with compensated duration,

\[
 \boxed{
 \mathcal A_{rm}(T/r)=r^{q-1}\mathcal A_m(T).}
\tag{PH.14}
\]

Hence a degree-one length is reparametrization invariant, while a quadratic kinetic action gains
one factor `r` when the same path is traversed `r` times faster.

### Proof

Equations `(PH.6)` and `(PH.11)` give the endpoint identity. Since
`dot h_(rm)=-rm lambda=r dot h_m`, homogeneity gives the fixed-clock action identity. Replacing
`T` by `T/r` proves `(PH.14)`. `[PROVED HERE]`

The cost is observer data, not forced by phase recurrence. The theorem is conditional on the
chosen homogeneous `Phi`; it classifies how every such marked cost transforms.

## 5. Third-doctrine consequence for CFR

For the shared three-doctrine event, assume `m>=2` and `|F|>=2`. The single source morphism `P_r`
then has exact responses in three distinct observer doctrines:

1. fixed-temperature positive capacity contracts for sufficiently deep events;
2. the full-shell Dirichlet observer gains a nonzero positive analytic excess;
3. the observed phase orbit is invariant, while marked history and fixed-clock costs dilate.

This is not yet a three-way comparison cell: the theorem constructs three exact,
composition-compatible responses to one source arrow, but no target functors or natural
transformation among them. It therefore advances the source-law event gate and corpus coverage
without completing CFR Gate III.

Nor is the phase/history response independent of the full finite-temperature Gibbs data. At fixed
`tau>0`, those weights satisfy

\[
 {q_p(m\tau)\over1-q_p(m\tau)}=e^{-\tau m\log p},
 \qquad
 m\log p=-{1\over\tau}\log{q_p(m\tau)\over1-q_p(m\tau)}.
\tag{PH.15a}
\]

Thus the full Gibbs weight vector reconstructs the raw phase generator. Only a coarser positive
observer, such as the scalar capacity, fails to do so. The third doctrine is a distinct marked
target, not new independent constitutive information.

The result also gives a falsifiable physics constraint. Any claimed physical length or complexity
deduced only from the recurrent phase orbit is underdetermined: all depths have the same orbit.
Such a quantity can distinguish depth only through a marked lift, external clock, generator, or
cost. Compensating the clock by `(PH.8)` erases the lift difference, and degree-one path length is
unchanged; fixed-clock quadratic action is not.

The source arrow does not choose whether raw time or normalized time is physical. The existing
normalized clock `-(La_m)(p^m)/m=log p` erases all depth dependence. Therefore this card constructs
no source-derived physical action or canonical time dilation.

## 6. Conjecture / proof / fail loops

1. **Ramification depth changes recurrence closure.** Failed: `(PH.7)` gives the same orbit set.
   **Survivor:** depth is a time-dilation gauge at phase level.
2. **Same recurrence implies same history.** Failed at fixed external time: `h_(rm)=r h_m`.
   **Survivor:** the cover/lift is load-bearing observer data.
3. **The lift difference is gauge invariant.** Failed under `t->t/r`: `(PH.8)` identifies the
   lifted paths. **Survivor:** only a marked external clock or parametrized cost detects depth.
4. **Every cost is a scalar multiple of length.** Failed: homogeneous degree `q` produces the
   distinct laws `(PH.13)`--`(PH.14)`. **Survivor:** the cost degree is constitutive data.
5. **Closed phase plus open lift implies a wormhole.** Failed: this finite prime torus already has
   both. **Survivor:** gravity additionally needs a source-derived symplectic pairing, edge charge,
   Hamiltonian, reconstruction map, and physical cost.
6. **The third observer completes CFR.** Failed: responses coexist, but no comparison 2-cell or
   Bianchi law is constructed. **Survivor:** use `P_r` as the fixed source arrow for the next
   comparison-coherence attack.
7. **The phase doctrine adds independent constitutive information.** Failed when full Gibbs
   weights are retained: `(PH.15a)` reconstructs the generator. **Survivor:** it is independent
   only relative to coarser positive scalarizations.

## 7. Scope and parents

- Nonempty finite `F` is load-bearing for open-history escape. Infinite-prime phase requires a
  declared topology, domain, and continuity law.
- Orbit-set equality uses continuous time `t in R`. Under sampled time `t in Z`, multiplication by
  `r` is not surjective on the clock and the orbit sets need not agree.
- The reparametrization identities hold for any finite real frequency vector. Prime labels and
  unique factorization are used specifically to prove full-torus density; dependent frequencies
  close on a proper subtorus.
- The history is the basepoint-zero universal-cover lift. Unmarked phase endpoints determine it
  only modulo `2pi Z^F` and cannot recover the escape or cost.
- This is a source-specific specialization of classical Kronecker torus dynamics and homogeneous
  action scaling; no novelty claim is needed.
- Existing corpus parents include the Euler prime-orbit recurrence, prime-phase port,
  `PrimeTorusKroneckerDensity.lean`, `SummablePurePointEscapeReturnLaw.lean`, and framed phase-fibre
  cost cards. The new content is reuse of the same `P_r` ledger, not a new recurrence mechanism.
- No statement concerns Xi zeros, source null-homology, black-hole interiors, or RH.
- No Lean file has been written or built.

## Lean-return notes

- Diagonal identities and lift scaling are finite-coordinate algebra.
- Reuse existing prime-log integer-independence and finite-torus recurrence declarations.
- Formalize cost scaling only after choosing the intended homogeneous-cost interface.
- No Lean file has been written or built.

## Gates

- [x] same source power morphism as two-organ event
- [x] exact observed orbit invariance
- [x] dense recurrence and unbounded lift
- [x] exact fixed-clock and reparametrized cost laws
- [x] third distinct observer-doctrine response
- [ ] third independent constitutive invariant
- [ ] three-way comparison cell
- [ ] source-derived physical cost
- [ ] infinite-prime completion
- [ ] wormhole or RH leverage
- [ ] Lean formalization

## Log

- 2026-08-09 — derived as the recurrence/time response of the existing ramification-power law event; no new source arrow introduced.
