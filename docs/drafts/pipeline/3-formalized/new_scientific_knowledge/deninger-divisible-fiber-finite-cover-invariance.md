# Divisible-fiber finite-cover invariance

- **ID:** `deninger-divisible-fiber-finite-cover-invariance`
- **Stage:** 3-formalized
- **Type:** SOURCE TOPOLOGICAL THEOREM · LEAN 4 THEOREM
- **Label:** `DAC_DIVISIBLE_FIBER_FINITE_COVER_INVARIANCE`
- **Parent:** `deninger-relative-sullivan-milnor-character-space`
- **Lean module:**
  `GaloisForLFunctions.RHTower.Deninger.DeningerDivisibleFiberFiniteCoverInvariance`

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

## Formalized statement

The whole group-theoretic content is formalized for a surjection
`f : G →* H` of groups with `K = f.ker`, which is exactly the data of
`(1)`.

Divisibility and the weaker hypothesis actually used:

- `DeningerPowerDivisible K`: `∀ n ≥ 1, ∀ k : K, ∃ u : K, u ^ n = k`;
- `DeningerNoFiniteQuotient K`: every homomorphism from `K` to a finite
  group is trivial;
- `deningerNoFiniteQuotient_of_powerDivisible`: divisibility implies the
  latter.

Finite-cover invariance `(2)`–`(3)`, with `Action FintypeCat G` the
category of finite `G`-sets and `Action.res FintypeCat f` restriction
along `f`:

- `deningerRho_ker_eq_id`: the kernel acts trivially on every finite
  `G`-set;
- `deningerDescend`, `deningerDescend_rho`, `deningerDescendIso`: every
  finite `G`-set descends along `f`, compatibly with the action;
- `deningerRes_essSurj`: restriction is essentially surjective;
- `deningerRes_isEquivalence`: restriction is faithful, full and
  essentially surjective, hence an equivalence of categories;
- `deningerFiniteActionEquiv` : `Action FintypeCat H ≌ Action FintypeCat G`,
  with `deningerFiniteActionEquiv_functor` identifying its functor with
  restriction of scalars;
- `deningerFiniteActionEquivOfDivisible`: the divisible-kernel form.

Finite quotients:

- `deningerKer_le_of_finiteIndex`: the kernel lies in every normal subgroup
  of finite index;
- `deningerFiniteIndexNormalEquiv` :
  `FiniteIndexNormalSubgroup H ≃o FiniteIndexNormalSubgroup G`, taking
  preimages;
- `deningerQuotientEquiv` : `G ⧸ N.comap f ≃* H ⧸ N` for the matched
  quotients.

Profinite completions:

- `deningerEta_ker`, `deningerEtaDescend`, `deningerEtaDescend_comp`: the
  completion unit of `G` factors through `H`;
- `deningerIsIso_profiniteCompletion_map`:
  `IsIso (profiniteCompletion.map (GrpCat.ofHom f))`;
- `deningerProfiniteCompletionIso`,
  `deningerProfiniteCompletionIsoOfDivisible`: the resulting isomorphism
  `profiniteCompletion.obj (GrpCat.of G) ≅ profiniteCompletion.obj (GrpCat.of H)`.

The passage from `(2)` to `(3)` is the classification hypothesis of the
card, so the Lean statement is the full mathematical content: the source
condition, the equivalence of categories of finite sets with action, the
bijection of finite quotients, and the profinite-completion isomorphism.

## Verification

- Direct command:
  `lake env lean GaloisForLFunctions/RHTower/Deninger/DeningerDivisibleFiberFiniteCoverInvariance.lean`
- Result: passed with no errors and no warnings.
- Scratch `#print axioms` on all 26 declarations: only the Lean/mathlib
  standard `propext`, `Classical.choice`, and `Quot.sound`.
- No `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` declaration; no
  hypothesis-carrying `Prop` interface: every statement is unconditional in
  its explicit group-theoretic hypotheses.
- Imported by the `GaloisForLFunctions.RHTower` umbrella.

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
- The Lean development proves the group theory, not the classification of
  finite covers by finite \(\pi_1\)-sets, which is the card's standing
  hypothesis on the ambient category of spaces.

## Gates

- [x] 0 → 1 in-progress: exact statement
- [x] 1 → 2 fully-proven: complete paper proof
- [x] 2 → 3 formalized: Lean module
  `GaloisForLFunctions.RHTower.Deninger.DeningerDivisibleFiberFiniteCoverInvariance`,
  unconditional, standard axioms only
- [ ] 3 → 4 publication-ready

**Verdict:** `FULLY PROVEN ON PAPER AND FORMALIZED IN LEAN 4`.
