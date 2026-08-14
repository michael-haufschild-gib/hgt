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

## Cycle 5 — low-output-degree atom preservation

### Theorem 1 `[PROVED HERE]` `[NOVELTY UNRESOLVED]`

Let `P in S` be primitive and let `chi` be a primitive Dirichlet character of conductor `q`.
Assume `P^chi in S`. If `P^chi` admits a factorization

\[
P^\chi=G_1\cdots G_r,\qquad r\ge2,
\]

with every `G_j in S` of degree one, then a contradiction follows. Consequently, every
nontrivial primitive factorization of `P^chi` contains a factor of degree at least two.

Since `S` has no nontrivial elements of degree below one and none of degree strictly between one
and two, this gives the unconditional boundary consequence

\[
d_{P^\chi}<3\quad\Longrightarrow\quad P^\chi\text{ is primitive}.
\]

Here “unconditional” means that the only assumptions are those occurring in the displayed
statement; no Selberg orthogonality, degree conjecture, twist-closure conjecture, or new analytic
axiom is used.

### Proof

The degree-one classification says that every `G_j` is either `zeta(s)` or
`L(s+i tau_j, eta_j)` for a primitive Dirichlet character `eta_j`. Twist the displayed
factorization coefficientwise by `bar chi`. Multiplicativity of twist gives

\[
E_qP=(P^\chi)^{\bar\chi}=\prod_{j=1}^r G_j^{\bar\chi}.
\]

For each `j`, the product character underlying `G_j^{bar chi}` is induced by a primitive
character `rho_j`. Therefore

\[
G_j^{\bar\chi}(s)=D_j(s)L(s+i\tau_j,\rho_j),
\]

where `D_j` is a nonzero Dirichlet series supported on finitely many primes. For a zeta factor,
this formula is read with `tau_j=0` and primitive character `bar chi`.

There is one edge case: `rho_j` can be principal. If `tau_j != 0`, the right side contains
`zeta(s+i tau_j)` and has a pole at `s=1-i tau_j`. Every other primitive Dirichlet `L`-function
is nonzero on `Re(s)=1`, and every finite missing Euler factor is also nonzero there because its
local variable has modulus `1/p`. Thus this pole cannot cancel in the product. But `E_qP` has no
pole away from `s=1`: `P` has none, and the finitely many reciprocal local Euler factors defining
`E_q` are holomorphic and nonzero for `Re(s)>theta` with `theta<1/2`. Hence the edge case is
impossible. If `tau_j=0`, the principal primitive base is `zeta(s) in S`.

It follows that every

\[
H_j(s):=L(s+i\tau_j,\rho_j)
\]

appearing above belongs to `S` and has degree one. Put `H=prod_j H_j in S` and
`D=prod_j D_j`. On the other hand,

\[
E_qP=D_P P,
\]

where `D_P=prod_{p|q}P_p^{-1}` is a nonzero finite-prime Dirichlet series. Therefore

\[
D_P P-DH=0.
\]

The linear-independence theorem over finite-prime Dirichlet series forces `P=H`; otherwise two
distinct elements of `S` satisfy a nontrivial linear relation over that ring. But `H` is a product
of `r>=2` nontrivial degree-one elements of `S`, contradicting primitivity of `P`. This proves the
first assertion.

For the consequence, suppose `d_(P^chi)<3` and `P^chi` is not primitive. Factor it into at least
two primitive elements. Each factor has degree at least one. If one had degree at least two, degree
additivity would give total degree at least three. Hence every factor has degree in `[1,2)`, and
the gap theorem for `S` forces degree exactly one. The first assertion gives the contradiction.

### Hostile checks

1. No inverse-twist closure is assumed: degree-one classification explicitly computes every
   inverse twist up to finite Euler factors.
2. Ramified erasure is retained as `E_qP`, not silently replaced by `P`.
3. The finite-prime linear-independence theorem is applied only to `P,H in S`; neither `E_qP` nor
   an individual inverse twist is assumed to be in `S`.
4. The shifted-principal-character pole is handled before declaring `H_j in S`.
5. The degree corollary uses the proved gaps `d<1` and `1<d<2`, not the open integer-degree
   conjecture.

### Significance and limitation

This rules out the entire abelian/degree-one factorization locus as a source of counterexamples to
primitive stability. Any primitive counterexample to Selberg Conjecture 3 must have twisted output
degree at least three and must contain a primitive factor of degree at least two. It does not prove
factorwise analytic re-entry for a product of several original primitives and therefore does not
close the frozen target.

## Cycle 6 — finite-prime completion obstruction

### Theorem 2 `[PROVED HERE]` `[NOVELTY UNRESOLVED]`

Under the hypotheses of Theorem 1, suppose `P^chi` is not primitive and fix a primitive
factorization

\[
P^\chi=G_1\cdots G_r,\qquad r\ge2.
\]

Then at least one `G_j` has the following property:

\[
G_j^{\bar\chi}\ne D H
\]

for every `H in S` and every nonzero finite-prime Dirichlet series `D`.

In words: every primitive counterexample contains an output factor whose inverse twist has no
Selberg completion even after arbitrary changes at finitely many primes.

### Proof

Assume instead that `G_j^bar chi=D_jH_j` for every `j`, with `H_j in S` and `D_j` nonzero and
finite-prime. Multiplying and using ramified erasure gives

\[
D_PP=E_qP=(P^\chi)^{\bar\chi}=\left(\prod_jD_j\right)\left(\prod_jH_j\right).
\]

No `H_j` can equal `1`. Indeed, then `G_j^bar chi` is finite-prime; twisting once more shows that
`E_qG_j` is finite-prime, so `G_j` satisfies a nontrivial finite-prime linear relation with
`1 in S`. Linear independence forces `G_j=1`, contrary to primitive factorization.

Thus `H=prod_jH_j` is a nontrivial factorization in `S`. Linear independence applied to
`D_PP-DH=0` forces `P=H`, contradicting primitivity of `P`. Therefore at least one `G_j` is not
finite-prime completable.

### Why this is a real reduction

Theorem 2 excludes every route in which inverse twists can be repaired by choosing finitely many
ramified Euler factors. A proof of the frozen conjecture may now focus on one exact analytic claim:

> A primitive divisor of a Selberg-class Dirichlet twist always has a finite-prime Selberg
> completion after inverse twist.

Unlike Cycle 4, this statement is independently falsifiable: one counterexample is a specific
primitive `G in S` dividing `P^chi` for which the multiplicative Dirichlet series `G^bar chi`
cannot be completed at finitely many primes to satisfy a Selberg functional equation.

### Minimal-degree descent attack

`[CONJECTURE D]` Choose a primitive counterexample `P` minimizing `d_(P^chi)`. A non-completable
primitive factor `G` from Theorem 2 has smaller degree and should generate a smaller counterexample
after twisting back.

**Attack.** `G^bar chi` is precisely not known to belong to `S`, even after finite completion.
Therefore it is not an admissible input to Selberg Conjecture 3 and no smaller counterexample has
been constructed. Minimality supplies no descent.

**Verdict:** fail. The failed descent identifies finite-prime completion existence—not degree—as
the next analytic core.

## Cycle 7 — multiple-standard-twist spectral separation

`[CONJECTURE E]` The polar hyperplanes of Kaczorowski–Perelli's multiple standard twist separate
the primitive factors of `P^chi` and force the finite-prime completions required by Theorem 2.

**Attack.** For a factorization `P^chi=prod_jG_j`, choose
`kappa_j=1/d_(P^chi)` and restrict the multiple twist of the `G_j` to the diagonal
`s_1=...=s_r=s`. The multiple series then equals the ordinary standard twist of the product,
because both the convolution coefficient and the nonlinear phase depend only on `prod_j n_j`.
The resulting polar identity is therefore tautological. Its hyperplanes record the additive totals
of degrees and internal shifts. They do not reconstruct the periodic multipliers `bar chi(n)` on
an individual factor. Away from the diagonal, no corresponding function built from `P` is
available for comparison.

The mismatch is structural: a standard twist uses `e(-alpha n^(1/d))`, whereas a Dirichlet twist
uses the periodic completely multiplicative multiplier `chi(n)`. The 2026 continuation theorem
does not convert one into the other.

**Verdict:** fail. Joint standard-twist poles cannot by themselves prove inverse-twist completion.
The failure rules out the newest apparent spectral-separation route rather than merely failing to
execute it.

## Cycle 8 — full Conjecture 3 on the degree-one-generated submonoid

### Theorem 3 `[PROVED HERE]` `[KNOWN-BOUNDARY LABEL]`

Let

\[
F=\prod_{i=1}^mF_i
\]

be a primitive factorization in `S` with `d_(F_i)=1` for every `i`. Let `chi` be primitive and
assume `F^chi in S`. Then every `F_i^chi` belongs to `S` and is primitive. Thus Selberg
Conjecture 3 holds exactly on the submonoid generated by degree-one elements.

### Proof

By degree-one classification, each `F_i` is `zeta(s)` or
`L(s+i tau_i,psi_i)` with `psi_i` primitive. Hence

\[
F_i^\chi(s)=D_i(s)L(s+i\tau_i,\rho_i),
\]

where `rho_i` is the primitive character inducing `psi_i chi` and `D_i` is a finite product of
missing Euler polynomials

\[
1-\rho_i(p)p^{-i\tau_i}p^{-s}.
\]

For a zeta input, `F_i^chi=L(s,chi)` and `D_i=1`.

If `rho_i` is principal and `tau_i != 0`, the factor has a pole at `1-i tau_i`. No other
degree-one primitive Dirichlet `L`-factor or missing Euler polynomial vanishes on `Re(s)=1`, so
this pole cannot cancel in `F^chi=prod_iF_i^chi`. Since an element of `S` has no pole away from
`s=1`, this case is impossible. Therefore every base

\[
H_i(s)=L(s+i\tau_i,\rho_i)
\]

belongs to `S` (with the principal case necessarily `zeta(s)`). Put `H=prod_iH_i in S` and
`D=prod_iD_i`. Multiplicativity of character twist gives

\[
F^\chi=DH.
\]

Both `F^chi` and `H` lie in `S`, so finite-prime linear independence forces `F^chi=H` and
`D=1`. Each `D_i` is a polynomial with constant term one in the finitely many independent local
variables `p^{-s}`. Their product can be the unit `1` only if every `D_i=1`. Thus
`F_i^chi=H_i in S`. Its degree is one, so it is primitive: a nontrivial factorization would split
degree one into two positive Selberg degrees, while every nontrivial Selberg element has degree at
least one.

### Novelty audit

Kaczorowski–Molteni–Perelli proved unique factorization for subsemigroups of the extended Selberg
class generated by degree-zero and degree-one functions. The theorem above is therefore labeled a
known-boundary consequence unless a later line-by-line comparison establishes a genuinely new
formulation:
<https://doi.org/10.1007/s00208-007-0197-9>.

### Consequence for the exact frontier

Any counterexample to full Selberg Conjecture 3 must contain an original primitive factor of degree
at least two. Combined with Theorems 1–2, a primitive atom-stability counterexample must also have
twisted output degree at least three and contain a non-finite-prime-completable primitive output
factor of degree at least two.
