# Scalar-recurrence / traceless-replica decoupling law

- **ID:** `scalar-recurrence-traceless-replica-decoupling-law`
- **Stage:** 1 — in progress
- **Type:** WILD CONJECTURE
- **Status:** `[CONJECTURE] [OPEN CORE] [SURVIVES PRELIMINARY ATTACK]`
- **Parent:** `quenched-observer-spectral-action-law.md`
- **Date:** 2026-08-06

## Public sentence

A closed quantum system has one universal easy direction: return toward the
identity.  Remove that shared recurrence once, and every shallow circuit
direction is predicted to become Haar-rare under one fixed generic local
Hamiltonian.

## Why the old variable is wrong

For a normalized finite spectral measure

\[
             \mu_H={1\over d}\sum_{j=1}^d\delta_{E_j(H)},
\]

the identity target contributes to the positive replica partition

\[
 Z_r(\mathcal C;H,\delta)
 =\sum_{C\in\mathcal C}
   M_{C,r}(H,\delta)
\]

whenever the circuit dictionary contains the empty circuit.  The companion
card `../3-formalized/replica-crowding-central-limit-floor.md` proves that
this one contribution is at least

\[
 {9\delta\over16(\delta+4\sigma_H\sqrt r)}-
 C_r(\mu_H),                                                \tag{1}
\]

where `sigma_H` is spectral standard deviation and `C_r` is exact collision
mass.  For normalized generic spectra this is of order `delta/sqrt(r)`, not
Haar scale.  Therefore no exponentially small upper bound on the positive
`Z_r` can survive.  Summing this same shared return channel once per circuit
word is the wrong representation.

## Exact scalar/traceless split

Put `d=2^n` and use normalized trace `tau_d=d^{-1}Tr`.  For every unitary
target `U`, set

\[
 \alpha_U=\tau_d(U),\qquad U^\circ=U-\alpha_UI,
 \qquad \tau_d(U^\circ)=0.                                 \tag{2}
\]

For every Hamiltonian `H` and time `t`,

\[
 \tau_d(U^*e^{-itH})
 =\overline{\alpha_U}\,\tau_d(e^{-itH})
   +\tau_d((U^\circ)^*e^{-itH}).                            \tag{3}
\]

Consequently, for every `theta>0` and every target family `A`,

\[
 \bigcup_{U\in A}
 \{|\tau_d(U^*e^{-itH})|\ge\theta\}
 \subseteq
 \{|\tau_d(e^{-itH})|\ge\theta/2\}
 \cup
 \bigcup_{U\in A}
 \{|\tau_d((U^\circ)^*e^{-itH})|\ge\theta/2\}.             \tag{4}
\]

The first event is the common recurrence channel and occurs once.  Only the
second union should pay circuit entropy.

## Full fixed-H model

Fix `q>=2`.  For `n>=q`, let

\[
 H_n(J)=m_{n,q}^{-1/2}
 \sum_{P:\,1\le\operatorname{wt}P\le q}J_PP,
 \qquad
 m_{n,q}=\sum_{k=1}^q3^k{n\choose k},                        \tag{5}
\]

with independent standard Gaussian coefficients.  Fix a finite universal
two-qubit gate alphabet.  Let `C_(n,s)` be the distinct unitaries represented
by at most `s` gates, with clean ancillas returned to zero.  Targets are fixed
before `J` is sampled.

For a simple-spectrum `H=V diag(E)V^*`, define

\[
 c_j^\circ(U,H)={1\over d}
   \langle E_j,(U^\circ)^*E_j\rangle                         \tag{6}
\]

and, for a multiplicity vector `p` of mass `r`,

\[
 c_p^\circ={r!\over\prod_jp_j!}\prod_j(c_j^\circ)^{p_j}.
\]

The signed off-collision replica window is

\[
 \mathscr R_r^\circ(U;H,\delta)=
 \sum_{\substack{|p|=|p'|=r\\
      0<|p\cdot E-p'\cdot E|<\delta}}
       c_p^\circ\overline{c_{p'}^\circ}.                    \tag{7}
\]

Unlike `Z_r`, `(7)` preserves the cancellations belonging to the physical
overlap and vanishes identically for the identity target.

## Frozen conjecture

For every fixed `q>=2` and fixed capture threshold `0<theta<1`, there are
constants `a_q,b_q,c_q,C_q>0` such that, for all sufficiently large `n`, all

\[
 1\le r\le \exp(c_qd),\qquad
 0<\delta\le1,\qquad
 0\le s\le a_q\min\{d\log(1+r),d^2\},                       \tag{8}
\]

the full Gaussian Pauli ensemble obeys the quenched growing-replica bound

\[
 \boxed{
 \Pr_J\!\left\{
   \sup_{U\in\mathcal C_{n,s}}
     |\mathscr R_r^\circ(U;H_n(J),\delta)|
       > C_q\delta+e^{-c_q(d\log(1+r)-b_qs)}
 \right\}
 \le e^{-c_qm_{n,q}}.}                                     \tag{Q}
\]

The `d log(1+r)` exponent is the completed spectral-torus capacity.  Taking
`r` as large as `exp(c d)` reaches the `d^2` plateau scale.  The statement is
about one ordinary time-independent local Hamiltonian: no fresh disorder is
inserted in time.

## Shadows and risky consequence

| Known theorem or obstruction | Shadow of `(Q)` |
|---|---|
| positive `Z_r` weighted-crowding law | absolute-value relaxation before scalar removal |
| central-limit floor `(1)` | common identity recurrence cannot be union-bounded |
| exact phase-shift invariance | scalar recurrence is a shared orbit channel |
| all-replica local Hall expansion | local disorder reaches every noncommutant replica direction |
| one-replica planar cavity decay | order-one traceless channel has no surviving atom |
| permanent local/Haar distinguishability | Haar-rarity here concerns target overlap, not loss of Hamiltonian locality |

The risky new assertion is simultaneous quenched cancellation of `(7)` for
the entire shallow-circuit family at replica order growing to
`exp(c d)`.  Neither Hall rank, level repulsion, a spectral form factor, nor
one-replica cavity decay implies it.

## Preliminary hostile attack

1. **Identity target.**  It kills an exponential bound on positive `Z_r`, but
   `(7)` is exactly zero because `I^circ=0`.
2. **Targets with large trace.**  Their large component is charged to the
   common event in `(4)`; only their actual traceless remainder enters `(Q)`.
3. **Repeated/padded circuit words.**  `C_(n,s)` is a set of distinct
   unitaries, so multiplicity cannot falsify the supremum.
4. **Integrable `q=1` dynamics.**  Excluded.  Product rotations give coherent
   traceless channels and are a genuine counterexample to a statement for
   every `q`.
5. **Small-H and easy-generator tubes.**  They remain potential falsifiers.
   Their Gaussian cost is polynomial in resolution, while `(Q)` demands an
   `exp(-c m)` exceptional set independent of `delta`.  A completed-orbit
   capacity condition may be forced if one such tube violates `(Q)`.
6. **Eigenvalue crossings.**  They have Gaussian measure zero but cannot be
   discarded in a quantitative proof; the proof must be basis-free or use
   spectral projectors.
7. **Large replica order.**  The conjecture deliberately crosses the usual
   `r<<d` moment range.  Collision capacity changes from `r!d^{-r}` to a
   `d log r` law; using the small-`r` factorial estimate here would be false.

**Verdict:** `SURVIVES PRELIMINARY ATTACK`, with item 5 the live falsifier.

## Exact open core

Prove a basis-free traceless replica-cancellation theorem for the common-
disorder Liouvillian

\[
 L_r(H)=\sum_{a=1}^r H^{(a)}-
        \sum_{b=1}^r H^{(r+b)},                              \tag{9}
\]

on the orthogonal complement of the scalar recurrence sector, uniformly for
the circuit secant set.  The required estimate is not a minimum-gap or rank
bound: it must control the signed spectral projection of `(9)` while keeping
the same quenched `J` in every replica.

No paper or Lean theorem may cite `(Q)` until this open core is closed.

## Gates

- [x] 0 -> 1: exact statement, falsifiers, and open core frozen
- [ ] 1 -> 2: dependency-closed paper proof
- [ ] 2 -> 3: axiom-clean Lean formalization
- [ ] 3 -> 4: external priority audit and manuscript propagation

## Log

- 2026-08-06 — Positive `Z_r` exponential decay conjecture killed by the
  identity-target central-limit floor.  Replaced it with the scalar-once,
  traceless-signed quenched law `(Q)`.

## Krylov-carrier attack and representation change — 2026-08-06

The scalar/traceless split is not the terminal invariant.  A fixed local
Pauli target has a conserved first Krylov component

\[
 \tau_d(PH_n(J))=J_P/\sqrt{m_{n,q}},
\]

and higher shallow targets can couple to higher powers of `H`.  Tracelessness
removes only the zeroth spectral moment.  The correct nested carrier is

\[
 \operatorname{span}\{I\}\subset
 \operatorname{span}\{I,H,\ldots,H^K\}\subset
 \{H\}'.
\]

Two exact replacement theorems are now closed:

1. `../3-formalized/krylov-replica-moment-amplification-law.md` proves that
   annihilating moments through `K` forces paired replica moments through
   order `2r(K+1)-1` to vanish.
2. `../3-formalized/krylov-causal-replica-sieve-law.md` proves that the
   observed `2r`th moment of every such residual is bounded by a factorial
   Krylov-horizon law, with no level-spacing premise.

Moment cancellation does not by itself make the signed near-action window
small; clustered finite-difference spectra can retain large near-window mass.
It instead controls the physical finite-time kernel directly.  Therefore
`(Q)` remains unproved and is no longer the preferred proof variable.

**Stronger replacement conjecture.**  For the fixed-`q` Gaussian Pauli
ensemble, the canonical Krylov split of every shallow-circuit target obeys a
quenched dichotomy: its Krylov-null residual satisfies the universal causal
sieve, while any carrier component large enough to produce capture at time
`t` requires circuit size `Omega(t)` until the carrier reaches spectral
dimension.  The statement must be formulated as a quantitative
transversality theorem for the complete circuit secant set, not as the desired
complexity conclusion hidden in a hypothesis.

**New `[OPEN CORE]`.**  Find and prove the non-circular carrier invariant that
turns large projection onto `span{I,H,...,H^K}` into an `Omega(K)` shallow-
circuit obstruction for the ordinary fixed-local ensemble.  The exact
residual channel is closed; only the carrier channel remains.
