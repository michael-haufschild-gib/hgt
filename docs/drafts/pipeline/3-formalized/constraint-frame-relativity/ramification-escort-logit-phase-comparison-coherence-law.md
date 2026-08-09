# Ramification escort--logit--phase comparison coherence law

- **ID:** `cfr-ramification-escort-logit-phase`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper) / GATE-III CALIBRATION / SCALAR NON-DESCENT
- **Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [STRICT SEMIGROUP COHERENCE] [FINITE MARKED APERTURE] [FLAT GAUGE COMPARISON] [SCALAR-CAPACITY NON-DESCENT] [NOT A NONTRIVIAL GATE-III CELL] [NOT PHYSICAL TIME] [NOT RH] [FORMALIZED IN LEAN]`
- **Formalized companion:** `ramification-escort-logit-phase-comparison-coherence-law-formalized.md`
- **Statement:** Ramification power acts on finite Gibbs probabilities by an escort map and on raw prime clocks by scalar dilation; log-odds is an equivariant analytic coordinate conjugating the two actions, and exponentiation gives the phase time-dilation square with strict multiplicative coherence.

## Goal

Calibrate the three-response ledger for `P_r(k)=k^r` by one actual observer comparison. The map must
be defined on an entire marked observer space, not only on the shell orbit, and must satisfy
composition before any RH target is mentioned.

The result also tests the slogan “positivity is a phase quotient.” Full Gibbs probability data
should retain the phase generator; only later scalarization may erase it.

## 1. Two semigroup observer spaces

Fix a finite nonempty marked prime set `F` and `tau>0`. Let

\[
 \mathcal Q_F=(0,1)^F
\tag{EL.1}
\]

be the full Bernoulli-probability observer. For every integer `r>=1`, define the escort map

\[
 (\mathcal R_rq)_p
 ={q_p^r\over q_p^r+(1-q_p)^r}.
\tag{EL.2}
\]

Let the raw-clock observer be `C_F=R^F`, with dilation

\[
 \mathcal S_r(x)=rx.
\tag{EL.3}
\]

Let `M=(N_(>0),times)` be the multiplicative monoid, regarded as a one-object category. The maps
`R_r` and `S_r` will make `Q_F` and `C_F` into `M`-objects; an equivariant map between them is the
typed comparison cell in this finite chart.

Finally define the signed log-odds clock

\[
 \mathcal L_\tau(q)_p
 =-{1\over\tau}\log{q_p\over1-q_p}.
\tag{EL.4}
\]

The map `L_tau:Q_F->R^F` is a real-analytic diffeomorphism, with inverse

\[
 \mathcal L_\tau^{-1}(x)_p={e^{-\tau x_p}\over1+e^{-\tau x_p}}.
\tag{EL.5}
\]

## 2. Strict comparison theorem

### Theorem 2.1 — escort semigroup, linearization, and coherence

For positive integers `r,s`,

\[
 \boxed{
 \mathcal R_1=\operatorname{id},
 \qquad
 \mathcal R_s\mathcal R_r=\mathcal R_{sr},}
\tag{EL.6}
\]

and

\[
 \boxed{
 \mathcal L_\tau\mathcal R_r
 =\mathcal S_r\mathcal L_\tau
 =r\mathcal L_\tau.}
\tag{EL.7}
\]

Thus `L_tau` is an equivariant analytic isomorphism between the multiplicative-integer action on
Gibbs probability space and scalar dilation on clock space. The square

\[
 \begin{CD}
 \mathcal Q_F @>{\mathcal R_r}>> \mathcal Q_F\\
 @V{\mathcal L_\tau}VV @VV{\mathcal L_\tau}V\\
 \mathbb R^F @>>{\mathcal S_r}> \mathbb R^F
 \end{CD}
\tag{EL.8}
\]

commutes strictly, and these squares compose according to multiplication `r,s->sr`.

### Proof

Write `o(q)=q/(1-q)` coordinatewise. Direct calculation gives

\[
 {\mathcal R_r(q)\over1-\mathcal R_r(q)}=o(q)^r.
\tag{EL.9}
\]

Taking the `s`-th escort raises the odds to the `rs`-th power, proving `(EL.6)`. Taking
`-tau^-1 log` in `(EL.9)` gives `(EL.7)`. Formula `(EL.5)` proves bijectivity and analyticity.
Strict composition follows from `(EL.6)` and `S_sS_r=S_(sr)`. `[PROVED HERE]`

This is a flat comparison: there is no residual curvature or anomaly in the square.

## 3. Literal shell Gibbs section

For shell depth `m>=2`, define

\[
 q_p^{(m)}={p^{-m\tau}\over1+p^{-m\tau}}.
\tag{EL.10}
\]

### Corollary 3.1 — source power naturality

For the literal source morphism `P_r:a_m->a_(rm)`,

\[
 \boxed{
 \mathcal R_r(q^{(m)})=q^{(rm)},
 \qquad
 \mathcal L_\tau(q^{(m)})=(m\log p)_{p\in F}.}
\tag{EL.11}
\]

Consequently the normalized clock is invariant:

\[
 {1\over rm}\mathcal L_\tau(q^{(rm)})
 ={1\over m}\mathcal L_\tau(q^{(m)})
 =(\log p)_{p\in F}.
\tag{EL.12}
\]

### Proof

The odds of `q_p^(m)` are `p^(-m tau)`. Equation `(EL.9)` raises them to
`p^(-rm tau)`, proving the first identity. Equation `(EL.4)` gives the second and then `(EL.12)`.
`[PROVED HERE]`

The same source event is therefore nontrivial at fixed raw clock and pure gauge after normalized
clock reduction.

## 4. Phase comparison cell

For `x in R^F`, define the diagonal phase observer

\[
 \operatorname{Ph}_t(x)
 =\operatorname{diag}(e^{-itx_p})_{p\in F}.
\tag{EL.13}
\]

Let `Flow(T^F)` be the set of continuous phase histories `V:R->T^F`, with `M`-action

\[
 (\mathcal T_rV)(t)=V(rt).
\tag{EL.13a}
\]

The map `Psi_tau:Q_F->Flow(T^F)` is `Psi_tau(q)(t)=Ph_t(L_tau(q))`.

### Theorem 4.1 — Gibbs-to-phase time-dilation square

For every real `t`,

\[
 \boxed{
 \operatorname{Ph}_t(\mathcal L_\tau(\mathcal R_rq))
 =\operatorname{Ph}_{rt}(\mathcal L_\tau(q)).}
\tag{EL.14}
\]

On the literal section `q^(m)`, this is exactly

\[
 U_{rm}(t)=U_m(rt).
\tag{EL.15}
\]

Equivalently,

\[
 \Psi_\tau\mathcal R_r=\mathcal T_r\Psi_\tau,
\tag{EL.15a}
\]

so the phase square is an equivariant map of `M`-objects, not only a pointwise identity.

### Proof

Substitute `(EL.7)` into `(EL.13)`:

\[
 \operatorname{Ph}_t(r\mathcal L_\tau(q))
 =\operatorname{Ph}_{rt}(\mathcal L_\tau(q)).
\]

Equation `(EL.11)` identifies the literal prime clocks. `[PROVED HERE]`

This is the represented flat comparison missing from the previous phase/history card: full Gibbs data
determine the phase generator, and ramification transport commutes with that determination.

## 5. Information loss occurs after scalarization

The log-odds comparison is invertible, so the full positive Gibbs observer loses no raw clock or
phase-generator information. By contrast, the Route-E Schur capacity is one scalar function of
the vector `q` and the marked prime clocks. Explicitly, write `lambda_p=log p`,

\[
 w_p=q_p(1-q_p),\quad A=\sum_pw_p,\quad B=\sum_pw_p\lambda_p,
 \quad C=\sum_pw_p\lambda_p^2,
 \quad D_F(q)=\pi^2(A-B^2/C).
\tag{EL.15b}
\]

This scalar does not reconstruct `q`: one has

\[
 D_F(q)=D_F(1-q),
 \qquad
 \mathcal L_\tau(1-q)=-\mathcal L_\tau(q).
\tag{EL.15c}
\]

For any `q` with some `q_p!=1/2`, these are distinct Gibbs states with identical scalar capacity
and opposite raw clock.

This gives the exact restricted correction to the CFR positivity slogan:

\[
 \boxed{
 \text{full positive Gibbs state}
 \xleftrightarrow[\mathcal L_\tau^{-1}]{\mathcal L_\tau}
 \text{raw clock vector}
 \longrightarrow
 \text{scalar capacity}.}
\tag{EL.16}
\]

The first arrow is an equivalence; information loss can occur at the final scalarization. Positive
structure itself is not universally a phase quotient.

### Theorem 5.1 — escort evolution does not descend through scalar capacity

Assume `F={p_1,p_2}` with `0<lambda_1<lambda_2`, and put

\[
 a=\lambda_1^2,
 \qquad b=\lambda_2^2,
 \qquad K=\pi^2(\lambda_2-\lambda_1)^2.
\tag{EL.17}
\]

For Bernoulli variances `w_i=q_i(1-q_i)`, the capacity is

\[
 D(w_1,w_2)=K{w_1w_2\over aw_1+bw_2}.
\tag{EL.18}
\]

There is no scalar function `psi_2` such that

\[
 D_F(\mathcal R_2q)=\psi_2(D_F(q))
 \qquad\hbox{for every }q\in(0,1)^2.
\tag{EL.19}
\]

### Proof

Under the second escort, a Bernoulli variance transforms by

\[
 f(w)={w^2\over(1-2w)^2}.
\tag{EL.20}
\]

Set

\[
 k={2a\over2a+b},
 \qquad A(c)=(c,c),
 \qquad B(c)=(2c,kc),
 \qquad 0<c\le {1\over8}.
\tag{EL.21}
\]

Every coordinate in these pairs lies in `(0,1/4]`, so each pair is realized by Bernoulli
parameters in `(0,1)`. Direct substitution gives

\[
 D(A(c))=D(B(c))=K{c\over a+b}.
\tag{EL.22}
\]

Since `f(w)/w^2->1` as `w->0`,

\[
 {D(f(A(c)))\over Kc^2}\longrightarrow {1\over a+b},
 \qquad
 {D(f(B(c)))\over Kc^2}\longrightarrow {4k^2\over4a+bk^2}.
\tag{EL.23}
\]

The two limits differ: the strict inequality

\[
 {4k^2\over4a+bk^2}<{1\over a+b}
\tag{EL.24}
\]

is equivalent after substitution to

\[
 a(4a+3b)<(2a+b)^2,
\]

whose right side minus left side is `ab+b^2>0`. Hence for all sufficiently small positive `c`,
the two initial capacities agree while their escorted capacities differ. Equation `(EL.19)` is
impossible. `[PROVED HERE]`

The exact loss is therefore dynamical, not only pointwise: scalar capacity neither reconstructs
the Gibbs state nor carries the source-induced escort action. Full Gibbs coordinates are required
before the flat clock/phase comparison can be formed.

## 6. CFR consequence

Within the marked finite-prime ramification sector, `(EL.8)` is one genuine equivariant comparison
of observer coordinates and `(EL.6)` is its strict coherence law. It is not fitted to Route E, HT,
or Xi: escort
transport is induced by the arithmetic power operation on Gibbs odds.

This remains a restricted flat gauge chart, not a nontrivial Gate-III cell. `L_tau` is invertible,
`R_r=L_tau^(-1) S_r L_tau`, and every square pastes strictly. More importantly, the source power
morphism is non-surjective and creates analytic excess, while every `R_r` is invertible after
allowing the positive-real inverse escort. The observer has forgotten the source asymmetry.
Theorem 5.1 proves that this flat comparison cannot descend through the scalar Route-E capacity.
CFR Gate III still asks for multiple nontrivial comparison cells and higher coherence across
distinct doctrines. No Stokes curvature, analytic-excess comparison, source-normal global
section, physical time choice, or RH leverage is supplied.

## 7. Conjecture / proof / fail loops

1. **Full positivity necessarily erases phase.** Failed: `L_tau` is invertible. **Survivor:**
   identify the exact positive scalarization or quotient that loses phase.
2. **Ramification is nonlinear in every coordinate.** Failed: log-odds linearizes it exactly.
   **Survivor:** nonlinear probability transport is a coordinate shadow of clock dilation.
3. **The phase/history response is independent of Gibbs data.** Failed by `(EL.11)`.
   **Survivor:** it is distinct only relative to coarse capacity observers.
4. **This comparison detects source-law curvature.** Failed: `(EL.8)` is an invertible coordinate
   conjugacy and commutes strictly. **Survivor:** use it as a flat calibration; curvature requires
   a second comparison that retains source asymmetry.
5. **Normalized and raw clock are equivalent physical choices.** Not source-determined.
   **Survivor:** normalized clock makes ramification invisible, while raw clock detects it; a
   physical theory must select the external clock convention.
6. **One flat calibration completes CFR Gate III.** Failed. No comparison to analytic excess or
   Stokes contact is built, and scalar capacity does not inherit escort evolution. **Survivor:**
   hold `P_r` fixed and attack a second cell that detects the non-surjective source complement.

## 8. Scope and boundaries

- Marked coordinates `p in F` and fixed `tau>0` are load-bearing. Changing `tau` rescales `L_tau`.
- The open cube `(0,1)^F` is load-bearing. At `q_p=0` or `1`, log-odds diverges; these are admission
  boundary strata, not points of this chart.
- Positive integer `r` is load-bearing for the literal source power semigroup, although the escort
  formula analytically makes sense for positive real `r`.
- Prime arithmetic is needed for the literal Gibbs section; Theorem 2.1 itself is an ordinary
  exponential-family identity.
- No source-derived physical clock, action, black-hole geometry, Xi-zero condition, or RH theorem
  is asserted.
- No Lean file has been written or built.

## Lean-return notes

- Formalize escort odds and semigroup composition over positive real coordinates.
- Package the finite marked prime specialization only after the analytic identity is formalized.
- Reuse the existing raw shell clock and phase declarations; do not duplicate recurrence proofs.
- No Lean file has been written or built.

## Gates

- [x] observer maps defined on full finite marked chart
- [x] source power induces escort transport
- [x] invertible Gibbs--clock comparison
- [x] strict multiplicative coherence
- [x] phase time-dilation square
- [x] exact raw/normalized clock separation
- [x] flat Gate-III calibration cell
- [x] scalar-capacity non-descent under escort transport
- [ ] first nontrivial Gate-III comparison cell
- [ ] second incompatible comparison cell
- [ ] nonzero interchange defect/curvature
- [ ] analytic-excess or Stokes comparison
- [ ] physical clock/cost selection
- [ ] Lean formalization

## Log

- 2026-08-09 — extracted from hostile proof that the phase generator is reconstructible from full Gibbs weights under the same ramification-power event.
