# Traceless local evolution has a permanent same-protocol Haar separator

- **ID:** `traceless-local-two-query-haar-separation-law`
- **Stage:** 3-formalized
- **Formalized companion:** `./traceless-local-two-query-haar-separation-law-formalized.md`
- **Type:** THEOREM (paper) / PHYSICAL TWO-QUERY PROTOCOL / MASTER O6
- **Source:** Cui--Schuster--Mao--Huang--Brandao, *Random unitaries from
  Hamiltonian dynamics*, arXiv:2510.08434, Appendix C; exact internal port
- **Statement:** One explicit forward-only two-query experiment separates every
  traceless fixed-`q` autonomous Pauli evolution from Haar at every time by the
  exact gap `3^(-q)/M_q - 1/(2^n+1)`.

## Goal

Close the same-experiment and identity-coordinate gaps in the permanent
locality--Haar clause of `../1-in-progress/static-local-complexity-law.md`.
The experiment receives no Hamiltonian description. It samples only from the
universal nonidentity Pauli dictionary of weight at most `q`, so the theorem
applies unchanged when the Hamiltonian and time are jointly random.

## Gates

- [x] 0 → 1 in-progress: exact protocol, quantifiers, and collision audit
- [x] 1 → 2 fully-proven: complete proof below, `[PROVED HERE]`
- [x] 2 → 3 formalized: literal traceless dictionary, physical score, exact
  Haar value, and comparison capstone — all four closed; see the companion
- [ ] 3 → 4 publication-ready: use only inside the completed master theorem

## Setup

Let `D=2^n`. Write `P_n` for the `n`-qubit Pauli strings, normalized by

\[
 D^{-1}\operatorname{Tr}(PQ)=\mathbf 1_{P=Q}.
\]

For `q≥1`, let

\[
 \mathcal P_q^*=\{P\in\mathcal P_n:P\ne I,\ \operatorname{wt}(P)\le q\},
 \qquad M_q=|\mathcal P_q^*|.
\]

Let `Stab_1={|±X>,|±Y>,|±Z>}` and let `Stab_prod=Stab_1^n`, with the uniform
probability law. For a unitary `U`, define the literal protocol score

\[
 \mathscr S_q(U)=\frac1{M_q}\sum_{P\in\mathcal P_q^*}
   \mathbb E_{u\in\mathrm{Stab}_{\rm prod}}
   \langle u|U^\dagger P U|u\rangle^2.                 \tag{1}
\]

Operationally, one trial samples `P` and `u`, prepares two copies of `u`,
applies the same unknown `U` once to each copy, measures `P` on each output,
and multiplies the two signs. The expected sign product is `(1)`. The trial
uses exactly two forward oracle queries.

## Theorem

Let

\[
 H=\sum_{P\in\mathcal P_q^*}h_P P\ne0,
 \qquad h_P\in\mathbb R,
 \qquad U_t=e^{-itH}.
\]

Then for every real `t`,

\[
 \boxed{\mathscr S_q(U_t)\ge {3^{-q}\over M_q}.}        \tag{2}
\]

For normalized Haar probability on `U(D)`, the *same score* obeys

\[
 \boxed{\mathbb E_{V\sim\mathrm{Haar}}\mathscr S_q(V)
        ={1\over D+1}.}                                \tag{3}
\]

Consequently, whenever `M_q3^q<D+1`, the protocol separates autonomous local
evolution from Haar at every time by expectation gap

\[
 \boxed{\Delta_{n,q}\ge {3^{-q}\over M_q}-{1\over D+1}>0.} \tag{4}
\]

The same inequalities hold after averaging over an arbitrary joint
distribution of traceless nonzero `q`-local Hamiltonians and arbitrary
evolution times.

## Proof

`[PROVED HERE]` Expand conjugation in the Pauli basis:

\[
 U^\dagger P U=\sum_{Q\in\mathcal P_n}C_{QP}(U)Q,
 \qquad C_{QP}(U)=D^{-1}\operatorname{Tr}(Q U^\dagger P U).
\]

The exact six-state single-qubit twirl is

\[
 \mathbb E_{u_1\in\mathrm{Stab}_1}
 \langle u_1|A|u_1\rangle\langle u_1|B|u_1\rangle
 =\begin{cases}
 1,&A=B=I,\\
 1/3,&A=B\in\{X,Y,Z\},\\
 0,&A\ne B.
 \end{cases}
\]

Independence over sites therefore gives

\[
 \mathbb E_u\langle u|U^\dagger P U|u\rangle^2
 =\sum_{Q\in\mathcal P_n}3^{-\operatorname{wt}(Q)}C_{QP}(U)^2. \tag{5}
\]

All terms are nonnegative. Retaining only `Q∈P_q^*`, using
`3^{-wt(Q)}≥3^{-q}`, and averaging over `P∈P_q^*` gives

\[
 \mathscr S_q(U_t)\ge {3^{-q}\over M_q}
 \sum_{P,Q\in\mathcal P_q^*}C_{QP}(U_t)^2.              \tag{6}
\]

Let `h=(h_P)`. Exact energy conservation `U_t^\dagger H U_t=H` says that the
principal traceless local transfer block satisfies `C(U_t)h=h`. Since `h≠0`,
Cauchy--Schwarz gives

\[
 \sum_{P,Q}C_{QP}(U_t)^2=\|C(U_t)\|_F^2
 \ge {\|C(U_t)h\|_2^2\over\|h\|_2^2}=1.               \tag{7}
\]

Equations `(6)` and `(7)` prove `(2)`.

For `(3)`, fix `P∈P_q^*` and a product stabilizer state `u`. Every nonidentity
Pauli is Hermitian, satisfies `P^2=I`, and has trace zero. The normalized Haar
second moment of a pure-state expectation is therefore

\[
 \mathbb E_V\langle u|V^\dagger P V|u\rangle^2
 ={\operatorname{Tr}(P^2)+\operatorname{Tr}(P)^2\over D(D+1)}
 ={1\over D+1}.                                        \tag{8}
\]

This value is independent of `P` and `u`; both finite averages in `(1)` leave
it unchanged. This proves `(3)`. Subtraction proves `(4)`. Averaging pointwise
inequality `(2)` over any Hamiltonian--time law proves the ensemble statement.

## Efficient decision rule

Each trial returns a sign in `{-1,1}`. With threshold halfway between the two
expectations, the variance is at most one. Chebyshev's inequality gives error
at most `4/(N Delta_{n,q}^2)` after `N` independent trials. Thus
`N≥12/Delta_{n,q}^2` gives error at most `1/3`.

For all-to-all fixed locality,

\[
 M_q=\sum_{w=1}^{\min(q,n)}3^w{n\choose w}\le(4n)^q.
\]

If `D+1≥2M_q3^q`, then `Delta_{n,q}≥1/(2M_q3^q)`, so the trial count and all
state-preparation, Pauli-measurement, and classical-sampling work are
polynomial in `n` for fixed `q`.

## Hostile audit

- **Identity contamination:** `I` is excluded from both sampled dictionary and
  Hamiltonian. Including it would create a conserved Haar contribution and
  invalidate the claimed same-score benchmark.
- **Same experiment:** `(2)` and `(3)` evaluate the identical random-`P`,
  random-product-stabilizer, two-copy sign-product experiment. No comparison
  with a different balanced probe is used.
- **Unknown Hamiltonian:** protocol samples from the universal dictionary, not
  from the nonzero support and not from Hamiltonian-dependent probabilities.
- **No backward oracle:** both copies receive one forward application of the
  same `U`; no `U^dagger` query is performed physically.
- **Time quantifier:** conservation is exact for every real `t`; no late-time,
  genericity, spectral, or mixing premise occurs.
- **Ensemble quantifier:** pointwise bound survives arbitrary averaging over
  Hamiltonians and times.
- **Scalar branch:** stated theorem is the traceless nonzero branch used by the
  target Gaussian Pauli ensemble. A universal theorem including scalar
  Hamiltonians must treat their global-phase evolution separately; it must not
  smuggle identity into `P_q^*`.
- **What this does not prove:** this is the permanent non-Haar clause only. It
  proves neither complexity growth nor a plateau hitting time.

## Lean plan — closed

1. `FiniteQTracelessPauliLabel`, `finiteQTracelessPauliTransferMatrix`,
   `finiteQTracelessEnergyCoordinates`.
2. `finiteQTracelessPauliTransferMatrix_fixes_energyCoordinates`,
   `finiteQTracelessEnergyCoordinates_ne_zero`; and the identity-coordinate gap is closed by
   `hasZeroPauliIdentityCoordinate_of_trace_eq_zero`, so literal tracelessness is the hypothesis.
3. `literalTwoQueryScore_ge_of_trace_eq_zero` (`(2)` on the literal score).
4. `haar_sq_trace_pure_state_conjugation` (`(8)` on any finite register, for every pure state and
   every traceless Hermitian involution).
5. `literalTwoQueryScore`, `average_sq_trace_eq_sum_twirl` (`(5)`),
   `haar_literalTwoQueryScore_eq` (`(3)`), and
   `haarBenchmark_lt_literalTwoQueryScore_of_trace_eq_zero` (`(4)`).

## Novelty status

No priority claim. Core no-go and protocol are due to Cui et al. The purpose
is an exact unconditional internal certificate consumed by the master paper.

## Log

- 2026-08-04 — Hostile audit found identity contamination and different-probe
  comparison in the existing concrete packaging. Rebuilt exact traceless
  same-protocol theorem and completed paper proof.
- 2026-08-04 — Formalized normalized finite-unitary Haar right invariance and
  the exact `1/(D+1)` mean-square law for every fixed preparation unitary and
  every traceless Hermitian involution. Formalized that every nonidentity
  finite Pauli string is Hermitian, traceless, and squares to the identity.
  Remaining formal edge is finite-index reindexing plus the literal
  product-stabilizer score average; no different-probe comparison remains in
  the mathematical core.

- 2026-08-09 — all five Lean layers closed unconditionally.  The two genuinely missing pieces were
  a pure state as a *prepared coordinate state* (`exists_unitary_trace_mul_eq_conj_entry`, from the
  spectral theorem for a Hermitian idempotent of unit trace) and Haar transport across a change of
  matrix index type (`measurePreserving_unitaryGroupReindex`, from Haar uniqueness).  Promoted to
  stage 3.
