# Raw MW rational-Witt degree-zero comparison

- **ID:** `deninger-raw-mw-rational-witt-degree-zero`
- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Parent:** `deninger-derived-mw-rational-witt-coefficient`
- **Failed statement:** The raw reduced MW correspondence complex has degree-zero rank
  isomorphic to Deninger's ordinary rational-Witt correspondence sheaf.

## Exact killing mechanism

Milnor--Witt finite correspondences carry Grothendieck--Witt coefficients.  The rank map
\[
 \operatorname{rk}:GW(k)\longrightarrow\mathbb Z
\]
has nonzero kernel whenever the Witt/signature channel is nontrivial.  Over a real base,
\[
 \epsilon=\langle1\rangle-\langle-1\rangle
\]
has rank zero but nonzero signature.  Decorating the graph of the section
\(1:\operatorname{Spec}k\to\mathbb A^1_k\) gives
\[
 \epsilon[\Gamma_1]\in
 \widetilde{\operatorname{Corr}}(\operatorname{Spec}k,\mathbb A^1)/
 \widetilde{\operatorname{Corr}}(\operatorname{Spec}k,\{0\}).
\]
Its ordinary rank image is zero, but the class is not removed by quotienting the zero section:
its support is \(\Gamma_1\), and signature detects its coefficient.  Thus the raw MW
degree-zero rank map cannot be injective.

This obstruction already occurs before Suslin localization or Rost--Schmid resolution.  Those
functors do not justify declaring the detected degree-zero class zero.

## Strongest positive survivor

`[CONJECTURE] [DAC_RANK_CONNECTED_MW_REPLACEMENT]`

Let
\[
 M_{\mathrm{St}}
 =
 \mathfrak R_{\mathrm{MW}}^{\mathrm{mult}}
 \left(Ra_f\widetilde W_{\mathrm{rat}}^{\,0}\right)
 \mathop{\otimes}^{\mathbb L}_{
   \operatorname{Free}_{E_\infty}^{+}(S_{\mathrm{St}})}
 \mathbbm1,
 \qquad
 O_{\mathrm{rat}}
 =
 Ra_fW_{\mathrm{rat}}^{\,0},
\]
and let \(r:M_{\mathrm{St}}\to O_{\mathrm{rat}}\) be rank.  Here the first factor is the
selective non-\(\mathbb A^1\)-localized bar--residue envelope; full Suslin localization is
separately falsified by `deninger-a1-localized-rational-witt-coefficient`.  Put
\[
 F_{\mathrm W}=\operatorname{Fib}(r),\qquad
 J_{\mathrm W}=\tau_{\le0}F_{\mathrm W},\qquad
 P_{\mathrm W}=\operatorname{Free}_{E_\infty}^{+}(J_{\mathrm W})
\]
and define the relative rank-connected replacement
\[
 M_{\mathrm{rc}}
 :=
 M_{\mathrm{St}}\mathop{\otimes}^{\mathbb L}_{P_{\mathrm W}}\mathbbm1 .
                                                                         \tag{1}
\]
The first map \(P_{\mathrm W}\to M_{\mathrm{St}}\) is induced by
\(J_{\mathrm W}\to F_{\mathrm W}\to M_{\mathrm{St}}\); the second sends all generators to
zero.  Thus `(1)` is a homotopy pushout in commutative algebras and does not require a
multiplicative section of rank.  The rank map factors through
\[
 r_{\mathrm{rc}}:M_{\mathrm{rc}}\longrightarrow O_{\mathrm{rat}}.       \tag{2}
\]
If the complexes are connective and the image of \(H^0(J_{\mathrm W})\) generates exactly the
kernel of \(H^0(r)\), the \(\pi_0\) calculation for `(1)` gives
\[
 H^0(r_{\mathrm{rc}}):H^0(M_{\mathrm{rc}})
   \xrightarrow{\sim}H^0(O_{\mathrm{rat}})=W_{\mathrm{rat}},             \tag{3}
\]
while higher homotopy retains the derived Witt and Tor correction.  The earlier
stable-category cofiber formula would identify the positive fiber with
\(\tau_{\ge1}F_{\mathrm W}\), but that is only a linear approximation and is false without
an additional flatness/cotangent-complex theorem.

## New insight

Deninger's missing \(R\alpha_*\mathscr G\) should not be the raw MW enhancement.  It should be
its **relative rank-connected cover** over the ordinary rational-Witt object.  This places
quadratic correction data in higher cohomological degrees, exactly where a derived correction
belongs, without corrupting Deninger's already correct degree-zero rational-Witt functions.

The construction also explains why the Witt channel can contribute to middle cohomology after
the dynamical suspension even though \(H^0\) remains ordinary.

## Survivor obligations

1. Construct the required \(t\)-structure on finite-topology MW complexes over the arithmetic
   base.
2. Prove \(O_{\mathrm{rat}}\) connective and identify its \(H^0\) with Deninger's
   correspondence presentation.
3. Prove the \(\pi_0\) formula for the connective algebra pushout `(1)` and deduce `(3)`.
4. Compute the positive homotopy of `(1)` via its bar/cotangent-complex filtration; do not
   replace it by an unproved module cofiber.
5. Show Steinberg null-homotopies, products, Gysin maps, and Frobenius/Verschiebung operations
   preserve \(J_{\mathrm W}\), its free-algebra action, and descend to \(M_{\mathrm{rc}}\).
6. Prove duality survives the replacement; positivity is still an archimedean theorem.

## Status

Raw candidate retired.  Positive survivor `(1)` is an active multiplicative conjectural
replacement.  Its degree-zero calculation is dependency-closed once the stated connectivity
and kernel-generation inputs are constructed; positive homotopy still requires the bar or
cotangent-complex analysis.  Lean formalization waits for the concrete categorical model.

## References

- Tom Bachmann, Baptiste Calmès, Frédéric Déglise, Jean Fasel, Paul Arne Østvær,
  *Milnor-Witt Motives*: https://arxiv.org/abs/2004.06634
- Håkon Kolderup, Oliver Röndigs, Paul Arne Østvær,
  *Hermitian K-theory and Milnor-Witt motivic cohomology over \(\mathbb Z\)*:
  https://arxiv.org/abs/2509.16404
- Jacob Lurie, *Higher Algebra*, §§3.1.3, 3.2.3, 5.4.4, 7.1.3:
  https://www.math.ias.edu/~lurie/papers/HA.pdf

## Log

- 2026-07-26 — raw degree-zero rank-isomorphism claim killed by the rank-zero signature
  class; relative Postnikov replacement extracted.
- 2026-07-26 — module-cofiber survivor replaced by free-\(E_\infty\)-algebra homotopy pushout;
  multiplicativity no longer assumes an unproved ideal or rank section.
