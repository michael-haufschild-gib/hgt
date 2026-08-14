# Selberg Conjecture 3 via ramified atomicity

- **ID:** `selberg-conjecture-3-ramified-atomicity`
- **Status:** Stage 1 — exact conjecture frozen; paper proof open
- **Started:** 2026-08-14
- **Scope:** Selberg's third conjecture, not the Selberg orthogonality conjectures
- **Lean status:** no formalization; exact analytic carrier absent

## Exact frozen target

Let `S` be the Selberg class. Let

\[
F=\prod_{i=1}^m F_i\in S
\]

be a factorization into primitive elements of `S`, let `chi` be a primitive Dirichlet character,
and put

\[
F^\chi(s)=\sum_{n\ge 1}\frac{\chi(n)a_F(n)}{n^s}.
\]

**Selberg Conjecture 3.** If `F^chi` belongs to `S`, then every `F_i^chi` belongs to `S` and is
primitive; consequently `F^chi=prod_i F_i^chi` is a primitive factorization.

No conditional substitute, abstract proposition interface, or theorem about a narrower class counts
as closure of this card.

## Internal frontier audit

- No exact Conjecture 3 card, Selberg-class carrier, Dirichlet-twist carrier, or exact Lean theorem
  exists in `formal/` or the paper-proof pipeline.
- `selberg-orthogonality-working-log.md` targets Conjectures 1–2. Its assertion that general
  Dirichlet twists are unconditionally available in `S^sharp` is false at the current literature
  frontier and cannot be imported here.
- Existing cyclotomic-detection and degree-two linear/standard-twist work studies Euler-product
  recognition or different twist operators. It does not imply coefficientwise Dirichlet-twist
  closure or primitivity.

## External frontier audit

- Selberg's exact Conjecture 3 is the target stated above:
  <https://en.wikipedia.org/wiki/Selberg_class#Conjectures>.
- Kaczorowski–Perelli explicitly state that for general `F in S` there are no general theorems
  placing `F^chi` in `S` or even `S^sharp`:
  <https://arxiv.org/abs/2405.03186>.
- Their 2024 degree-two theorem assumes all relevant twists already belong to `S^sharp`, plus
  saturation and local polynomial splitting, and proves only invariance of degree and internal
  shift. It does not prove membership or primitivity.
- Their 2023 work likewise describes twist membership as expected and wide open, then obtains
  polynomial Euler products from explicit weak twist-regularity hypotheses:
  <https://arxiv.org/abs/2303.02417>, <https://arxiv.org/abs/2303.02420>.
- The stronger coprime-conductor twist conjecture and the accompanying primitive-if-and-only-if
  conjecture remain stated as conjectures in Perelli's survey:
  <https://www.rivmat.unipr.it/fulltext/2004-3s/pdf/04.pdf>.
- Distinct Selberg-class functions are linearly independent over the ring of Dirichlet series
  supported on finitely many primes. In particular, a nontrivial finite Euler-factor modification
  of a Selberg-class element cannot also be in the Selberg class:
  <https://mathreports.ca/article/linear-independence-in-the-selberg-class/>.

**Novelty label:** exact full conjecture is open; the ramified-localization formulation below is a
candidate new reduction until a direct literature collision is found.

## Exact algebra before conjecturing

Let `q` be the conductor of `chi`. In the monoid of normalized multiplicative Dirichlet series,
coefficientwise twist is multiplicative:

\[
(AB)^\chi=A^\chi B^\chi.
\]

If `E_q` erases every Euler factor at a prime dividing `q`, then

\[
(A^\chi)^{\bar\chi}=E_qA.
\]

Thus twist is not a group action on the original monoid. It is an automorphism only on the
`q`-depleted localization. This loss of invertibility is exactly where the routine argument
"twist back and use primitivity" fails.

Define the analytic re-entry monoid

\[
R_\chi=\{A\in S:A^\chi\in S\}.
\]

Conjecture 3 asserts more than closure of `R_chi`: if a product of atoms lies in `R_chi`, every atom
lies in `R_chi`, and its image is again an atom of `S`.

## Heavy conjecturing loop

### Cycle 1 — global twist closure

`[CONJECTURE A]` Dirichlet twisting preserves `S` for every primitive character.

**Attack.** This is stronger than the frozen target and is itself a named open twist conjecture.
Current degree-two work assumes the needed analytic continuation and functional equations rather
than deriving them.

**Verdict:** fail; no progress unless a new continuation mechanism is supplied.

### Cycle 2 — twist back and use primitivity

`[CONJECTURE B]` If `P,P^chi in S` and `P` is primitive, then factoring `P^chi=AB` and twisting by
`bar chi` contradicts primitivity of `P`.

**Attack.** `A^bar chi` and `B^bar chi` are not known to lie in `S`, while
`(P^chi)^bar chi=E_qP`, not `P`. The apparent proof assumes both missing twist closure and
invertibility across ramified primes.

**Verdict:** fail; identifies ramified erasure as exact obstruction.

### Cycle 3 — finite-prime rigidity

`[PROVED IN LITERATURE]` If `G,H in S` and `H=D G` for a Dirichlet series `D` supported on finitely
many primes, then `D=1` and `H=G`.

**Reason.** Otherwise `H-DG=0` contradicts linear independence of distinct Selberg-class functions
over the ring of finite-prime Dirichlet series.

This kills nontrivial finite Euler-factor modifications *once both endpoints are known to be in
`S`*. It does not place an unknown twist or depleted function in `S`.

**Verdict:** genuine boundary theorem, insufficient for Conjecture 3.

### Cycle 4 — ramified atomicity

`[CONJECTURE C]` Analytic re-entry is divisor-reflecting and atom-reflecting: whenever
`prod_i P_i` is a product of atoms in `S` and its `chi`-twist lies in `S`, every `P_i^chi` lies in
`S`, and every such twist is an atom.

**Attack.** This is exactly the frozen target in localization language unless it is reduced to an
independently checkable analytic law. Calling it saturation is theatre, not a proof.

**Verdict:** rejected as a purported reduction.

## Big-picture universal principle

Orthogonality controls averages over all primes and is blind to finitely many ramified places.
Dirichlet twisting is unitary away from `q` but annihilates the local data at `p|q`. The obstruction
therefore lives in a different layer:

> **Ramified superselection principle.** Analytic continuation plus a Selberg functional equation
> cannot arise through cancellation between separate multiplicative sectors whose individual
> `q`-depleted twists lack Selberg functional equations; nor can inverse local factors at the
> ramified primes cancel across primitive Selberg factors.

This principle simultaneously explains:

1. why prime-average orthogonality cannot see Conjecture 3;
2. why twisting back loses exactly the information needed for primitivity;
3. why finite-prime linear independence is necessary but not sufficient.

**Risky consequence.** A counterexample to Conjecture 3 must exhibit analytic-continuation or
functional-equation cancellation between at least two non-Selberg twisted primitive factors; it
cannot be obtained by a finite Euler-factor modification of known Selberg functions.

## Exact open core

Prove or disprove the ramified superselection principle from Selberg's five axioms in a form that
forces both:

1. factorwise analytic re-entry `F_i^chi in S`;
2. absence of nontrivial Selberg factorizations of each `F_i^chi`.

Until this analytic core is dependency-closed on paper, Lean work would formalize an assumption
rather than Selberg Conjecture 3 and is forbidden by the task.

## Gates

- [x] Exact conjecture frozen
- [x] Internal prior-work audit
- [x] Primary external frontier audit
- [x] False closure claim identified and rejected
- [x] Ramified erasure obstruction isolated
- [ ] Independent theorem implying ramified superselection
- [ ] Hostile paper-proof audit
- [ ] Exact Lean formalization
