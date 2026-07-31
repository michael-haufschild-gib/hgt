# Baumslag free-rational Milnor packet

- **ID:** `deninger-baumslag-free-rational-milnor-packet`
- **Stage:** 2-fully-proven
- **Type:** SOURCE FINITE-STAGE TOPOLOGICAL THEOREM
- **Label:** `DAC_BAUMSLAG_FREE_RATIONAL_MILNOR_PACKET`
- **Parent:** `deninger-baumslag-milnor-pro-realization`

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
