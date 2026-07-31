# Divisible-fiber finite-cover invariance

- **ID:** `deninger-divisible-fiber-finite-cover-invariance`
- **Stage:** 2-fully-proven
- **Type:** SOURCE TOPOLOGICAL THEOREM
- **Label:** `DAC_DIVISIBLE_FIBER_FINITE_COVER_INVARIANCE`
- **Parent:** `deninger-relative-sullivan-milnor-character-space`

## Statement

Let \(f:Y\to X\) be a map of connected spaces in a category where finite
covering spaces are classified by finite \(\pi_1\)-sets.  Suppose
\[
 1\longrightarrow K\longrightarrow\pi_1(Y)
 \xrightarrow{f_*}\pi_1(X)\longrightarrow1                         \tag{1}
\]
is exact and \(K\) is divisible: for every \(k\in K\) and every
\(n\ge1\), there is \(u\in K\) with \(u^n=k\).  Then restriction along
\(f_*\) induces an equivalence
\[
 \operatorname{FinSet}_{\pi_1(X)}
 \xrightarrow{\sim}
 \operatorname{FinSet}_{\pi_1(Y)},                                  \tag{2}
\]
and hence
\[
 \operatorname{FEC}(X)\simeq\operatorname{FEC}(Y).                   \tag{3}
\]
In particular, \(\pi_1(X)\) and \(\pi_1(Y)\) have canonically isomorphic
profinite completions.

The same conclusion holds when \(K\) is merely a group with no nontrivial
finite quotient.  Divisibility is a sufficient source condition.

## Proof

First prove that a divisible group has no nontrivial finite quotient.  Let
\(\varphi:K\to H\) have finite image \(J\), and put \(n=|J|\).  For every
\(k\in K\), choose \(u\in K\) with \(u^n=k\).  Lagrange's theorem gives
\[
 \varphi(k)=\varphi(u)^n=1.
\]
Thus \(\varphi\) is trivial.

Let \(S\) be a finite \(\pi_1(Y)\)-set.  Its action is a homomorphism
\[
 \rho:\pi_1(Y)\longrightarrow\operatorname{Sym}(S).
\]
The restriction \(\rho|_K\) has finite image, so it is trivial by the first
paragraph.  Exactness of `(1)` therefore gives a unique action of
\(\pi_1(X)\) on \(S\) whose pullback is the original action.  The same
factorization applies to equivariant maps, so restriction is essentially
surjective and fully faithful.  This proves `(2)`.  Classification by
finite \(\pi_1\)-sets gives `(3)`.

Finite quotients are the actions on finite groups by left translation, so
the categories in `(2)` determine the same cofiltered system of finite
quotients.  Their profinite completions are canonically isomorphic.

## Application to the Milnor character realization

For
\[
 \alpha_F:X_F^M\longrightarrow X_F,
\]
it is enough to construct a connected homotopy fiber and prove:

1. \((\alpha_F)_*\) is surjective on fundamental groups;
2. its kernel is the image of the fiber fundamental group;
3. that image is divisible.

Unique divisibility and pro-unipotence are stronger than required for
finite covers.  Higher homotopy divisibility is irrelevant to `(3)`,
though it remains relevant to a full profinite-homotopy comparison.

## Hostile audit

- Divisibility of a rational DGA does not prove divisibility of an actual
  fiber fundamental group.  The realization theorem must still supply it.
- Exactness in `(1)` is essential.  An uncontrolled \(\pi_0\) of the fiber
  or failure of surjectivity can change finite covers.
- The theorem proves finite-cover and profinite-\(\pi_1\) invariance, not an
  equivalence of full profinite homotopy types.
- No nilpotence or finite-type hypothesis is used after `(1)` is known.

**Verdict:** `FULLY PROVEN ON PAPER`.
