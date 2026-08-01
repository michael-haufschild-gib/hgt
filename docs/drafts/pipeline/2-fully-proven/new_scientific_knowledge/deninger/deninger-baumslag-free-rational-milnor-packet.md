# Baumslag free-rational Milnor packet

- **ID:** `deninger-baumslag-free-rational-milnor-packet`
- **Stage:** 2-fully-proven
- **Type:** SOURCE FINITE-STAGE TOPOLOGICAL THEOREM
- **Label:** `DAC_BAUMSLAG_FREE_RATIONAL_MILNOR_PACKET`
- **Parent:** `deninger-baumslag-milnor-pro-realization`
- **Lean module:**
  `GaloisForLFunctions.RHTower.DeningerUniquelyDivisibleKernel` (clauses 1 and 2)

## Statement

Let \(U\) be an \(m\)-dimensional rational vector space.  After choosing a
basis of the dual \(A=U^\vee\), let \(F_m\) be the free group on that basis
and let
\[
 R_U:=\operatorname{Bau}(F_m)
\]
be its Baumslag rationalization.  Then there is a surjective homomorphism
\[
 a_U:R_U\twoheadrightarrow A                                      \tag{1}
\]
such that:

1. \(R_U\) and \(K_U:=\ker(a_U)\) are uniquely divisible;
2. \(K_U\) has no nontrivial finite quotient;
3. the induced map
   \[
   Ba_U:BR_U\longrightarrow BA=K(A,1)                              \tag{2}
   \]
   is an isomorphism on \(H^1(-;\mathbb Q)\);
4. the rational cohomology algebra is
   \[
   H^\ast(BR_U;\mathbb Q)\cong\mathbb Q\oplus U[-1],\qquad U^2=0;   \tag{3}
   \]
   and any connected rational CDGA cochain model of \(BR_U\) is formal;
5. the homotopy fiber of `(2)` is connected and has fundamental group
   \(K_U\).  Consequently every homotopy pullback of `(2)` has a connected
   divisible \(\pi_1\)-kernel over its base and preserves finite covering
   categories by `DAC_DIVISIBLE_FIBER_FINITE_COVER_INVARIANCE`.

The packet is noncanonical because a basis of \(A\) was chosen.

## Proof

Send the free generators of \(F_m\) to the chosen basis of \(A\).  Since
\(A\) is a rational group, the universal property of Baumslag
rationalization extends this surjection uniquely to `(1)`.

By definition \(R_U\) is uniquely divisible.  If \(k\in K_U\) and
\(x^n=k\) in \(R_U\), then
\[
 n\,a_U(x)=a_U(k)=0.
\]
The rational vector space \(A\) is torsion-free, so \(a_U(x)=0\); uniqueness
of roots in \(R_U\) shows that \(K_U\) is uniquely divisible.  Its finite
quotients are trivial by
`DAC_DIVISIBLE_FIBER_FINITE_COVER_INVARIANCE`.

Casacuberta--Peschke's theorem for free groups, as summarized by Ivanov,
gives
\[
 H_\ast(R_U;\mathbb Q)\cong H_\ast(F_m;\mathbb Q).
\]
The latter is \(\mathbb Q\) in degree zero, \(\mathbb Q^m\) in degree one,
and zero above degree one.  Universal coefficients yield `(3)`, including
the square-zero product.  The map `(1)` is the rational abelianization on
degree one, giving clause 3.  `DAC_TWO_TERM_CDGA_FORMALITY` gives the final
formality assertion.

Since `(1)` is surjective, the homotopy fiber of the map of classifying
spaces is \(BK_U\), hence connected with fundamental group \(K_U\).
Homotopy pullback preserves that fiber.  Clause 5 follows from the
divisible-fiber theorem.

## Formalized statement

`GaloisForLFunctions/RHTower/DeningerUniquelyDivisibleKernel.lean` proves clauses 1 and 2 in the
generality in which the card's own proof argues them — nothing about Baumslag rationalization is
used, only unique divisibility of `R_U` and torsion-freeness of `A`:

- `DeningerUniquelyDivisible R` : every element has a unique `n`-th root for every `n ≥ 1`;
- `deningerPowerDivisible_of_uniquelyDivisible` : unique divisibility implies divisibility;
- `deningerKer_uniquelyDivisible` : for `f : R →* A` with `R` uniquely divisible and `A`
  torsion-free, `ker f` is uniquely divisible.  This is clause 1, and the proof is the card's:
  the `n`-th root `x` of `k ∈ ker f` satisfies `f(x)ⁿ = 1`, so `f(x) = 1` by torsion-freeness,
  and uniqueness in `R` gives uniqueness in `ker f`;
- `deningerKer_noFiniteQuotient` : that kernel admits no nontrivial homomorphism to a finite
  group.  This is clause 2, obtained from
  `DAC_DIVISIBLE_FIBER_FINITE_COVER_INVARIANCE` as already formalized in
  `GaloisForLFunctions.RHTower.DeningerDivisibleFiberFiniteCoverInvariance`, exactly as the card
  cites it.

### What is formalized and what is not

Formalized: clauses 1 and 2, unconditionally.  `DeningerUniquelyDivisible` and
`deningerPowerDivisible_of_uniquelyDivisible` use no axioms at all;
`deningerKer_uniquelyDivisible` uses only `propext`.

Not formalized, and none of it is a mathlib gap of the ordinary kind:

- the construction of `R_U = Bau(F_m)` itself and the surjection `(1)`.  Baumslag rationalization
  does not exist in mathlib, and building it is a separate construction card;
- clauses 3 and 4, which quote Casacuberta--Peschke via Ivanov for
  `H_*(R_U;ℚ) ≅ H_*(F_m;ℚ)`, plus `DAC_TWO_TERM_CDGA_FORMALITY`.  These need rational homology of
  classifying spaces and a CDGA category, neither of which the corpus has;
- clause 5, the homotopy fibre statement, for the same reason.

### Verification

- Direct command:
  `lake env lean GaloisForLFunctions/RHTower/DeningerUniquelyDivisibleKernel.lean`
  — passes with no errors and no warnings.
- Cached module build:
  `lake build GaloisForLFunctions.RHTower.DeningerUniquelyDivisibleKernel` completes.
- Scratch `#print axioms` on all four declarations: no axioms, `propext`, or the standard
  `propext, Classical.choice, Quot.sound`.
- Imported by the `GaloisForLFunctions.RHTower` umbrella.

## Gates

- [x] 0 → 1 in-progress: packet statement isolated
- [x] 1 → 2 fully-proven: complete paper proof
- [x] 2 → 3 formalized, clauses 1 and 2
  (`GaloisForLFunctions.RHTower.DeningerUniquelyDivisibleKernel`)
- [ ] 2 → 3 formalized, clause 3--5: blocked on Baumslag rationalization, rational homology of
  classifying spaces, and a CDGA category, none of which exist in mathlib or the corpus
- [ ] 3 → 4 publication-ready: `GL(U)`, Galois and power-map functoriality of the packet

## Hostile audit

- The packet depends on a basis.  It does not yet carry coherent
  \(GL(U)\), Galois, or power-map functoriality.
- Equation `(3)` is rational only; Baumslag rationalization does not
  construct torsion-free integral Milnor cohomology.
- Pulling `(2)` back over \(X_F\) preserves finite covers, but its cohomology
  is not computed by a naïve tensor product without a twisted
  Eilenberg--Moore theorem.
- Baumslag rationalization and Malcev/\(\mathbb Q\)-completion are
  different.  Replacing the former by the latter reintroduces nonzero
  \(H_2\).

**Verdict:** `FULLY PROVEN ON PAPER`.

## References

- Gilbert Baumslag, *Some aspects of groups with unique roots*.
- Carles Casacuberta and Georg Peschke, *Localizing with respect to
  self-maps of the circle*.
- Sergei O. Ivanov, *An overview of rationalization theories of
  non-simply connected spaces and non-nilpotent groups*, Equation (5.3):
  https://arxiv.org/abs/2111.10694

## Log

- 2026-08-01 — Formalized clauses 1 and 2 unconditionally, reusing the already formalized
  divisible-fiber theorem for clause 2.  Clauses 3--5 are recorded as blocked on objects that do
  not exist yet, not on missing proofs.
