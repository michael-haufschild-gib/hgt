# Multiplicative derived rank quotient

- **ID:** `deninger-derived-rank-quotient-universal-property`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Parent:** `deninger-derived-mw-rational-witt-coefficient`
- **Statement:** Killing the low rank fiber by a free-\(E_\infty\)-algebra homotopy pushout
  gives the universal multiplicative quotient and has the expected degree-zero ring.

## Setup

We use homotopy grading.  Thus \(\mathcal C_{\ge0}\) means
\(\pi_i=0\) for \(i<0\), and arithmetic degree \(q\) is displayed as \(\pi_q\).

Let \(\mathcal C^\otimes\) be a presentable symmetric monoidal stable
\(\infty\)-category whose tensor product preserves colimits separately.  Assume
\(\mathcal C\) has a tensor-compatible accessible \(t\)-structure.  Let
\[
 r:A\longrightarrow B
\]
be a morphism of connective commutative algebra objects.  Let \(J\in\mathcal C_{\ge0}\),
let \(j:J\to A\) be a morphism of underlying objects, and fix a null-homotopy of
\(rj:J\to B\).

Write
\[
 P=\operatorname{Free}_{E_\infty}^{+}(J)
\]
for the free unital commutative algebra.  The maps \(j:J\to A\) and \(0:J\to\mathbbm1\)
induce algebra maps \(P\to A\) and \(P\to\mathbbm1\).  Define
\[
 Q(A,J):=
 A\mathop{\otimes}^{\mathbb L}_{P}\mathbbm1,                            \tag{1}
\]
the pushout in \(\operatorname{CAlg}(\mathcal C)\).

## Universal theorem

`[PROVED HERE] [DAC_DERIVED_RANK_QUOTIENT_UNIVERSAL_PROPERTY]`

The object `(1)` is a commutative algebra, the map \(A\to Q(A,J)\) is initial among
commutative-algebra maps out of \(A\) equipped with a coherent null-homotopy of the image of
\(J\), and the chosen null-homotopy of \(rj\) induces a canonical factorization
\[
 A\longrightarrow Q(A,J)\xrightarrow{\bar r}B.                         \tag{2}
\]
More precisely, for every commutative algebra \(T\),
\[
 \operatorname{Map}_{\operatorname{CAlg}}(Q(A,J),T)
 \simeq
 \operatorname{Map}_{\operatorname{CAlg}}(A,T)
 \mathop{\times}^{h}_{
   \operatorname{Map}_{\operatorname{CAlg}}(P,T)}
 \operatorname{Map}_{\operatorname{CAlg}}(\mathbbm1,T).                \tag{3}
\]
Under the free-forgetful adjunction, the right side is exactly an algebra map
\(A\to T\) together with a coherent null-homotopy of \(J\to A\to T\).

### Proof

Presentability and separate colimit preservation give free commutative algebras and colimits
in \(\operatorname{CAlg}(\mathcal C)\).  Formula `(1)` is the pushout of
\[
 A\longleftarrow P\longrightarrow\mathbbm1.
\]
Mapping a colimit into \(T\) gives the homotopy limit `(3)`.  The free-forgetful adjunction
identifies a map \(P\to T\) with a map \(J\to U(T)\); the map
\(\mathbbm1\to T\) selects its zero restriction.  This proves the universal property.
Applying it to \(T=B\), the map \(r\), and the specified null-homotopy of \(rj\) gives `(2)`.
No section \(B\to A\) and no ideal object inside \(A\) is used.

## Degree-zero theorem

`[PROVED HERE] [DAC_DERIVED_RANK_QUOTIENT_PI0]`

Assume additionally that connective tensor products satisfy the standard convergent bar
spectral sequence and that
\[
 \pi_0P\simeq\operatorname{Sym}^{+}_{\pi_0\mathbbm1}(\pi_0J).
\]
Then \(Q(A,J)\) is connective and
\[
 \pi_0Q(A,J)
 \cong
 \pi_0A\otimes_{\operatorname{Sym}^{+}(\pi_0J)}\pi_0\mathbbm1
 \cong
 \pi_0A/\langle\operatorname{im}(\pi_0j)\rangle.                        \tag{4}
\]

### Proof

The two-sided bar construction
\[
 \operatorname{Bar}_\bullet(A,P,\mathbbm1)
\]
realizes to `(1)`.  Every simplicial term is connective.  Tensor compatibility makes its
homotopy spectral sequence first-quadrant, so no positive Tor term can contribute to total
degree zero.  Hence its degree-zero edge is the ordinary tensor product
\[
 \pi_0A\otimes_{\pi_0P}\pi_0\mathbbm1.
\]
The augmentation
\(\operatorname{Sym}^{+}(\pi_0J)\to\pi_0\mathbbm1\) sends every generator to zero.
The displayed tensor product is therefore the quotient of \(\pi_0A\) by the ideal generated
by the image of \(\pi_0J\), proving `(4)`.

## Arithmetic corollary

`[PROVED HERE] [DAC_DERIVED_RANK_QUOTIENT_H0_COROLLARY]`

Take
\[
 A=\mathcal C_F^{MW},\qquad
 B=\mathcal C_F^M,\qquad
 J=\tau_{\le0}\operatorname{Fib}(r)
\]
in the homotopy grading fixed above.  If

1. \(H^0(r):H^0(\mathcal C_F^{MW})\to H^0(\mathcal C_F^M)\) is surjective;
2. the image of \(H^0(J)\) generates \(\ker H^0(r)\) as an ideal; and
3. the unit-amalgamated cochain category satisfies the connectivity hypotheses above,

then
\[
 H^0\!\left(
 \mathcal C_F^{MW}
 \mathop{\otimes}^{\mathbb L}_{
   \operatorname{Free}_{E_\infty}^{+}(J)}
 \mathbbm1\right)
 \xrightarrow{\sim}
 H^0(\mathcal C_F^M).                                                   \tag{5}
\]
In the Deninger coefficient conjecture the target is the ordinary Milnor-corrected cochain
algebra, so its required degree zero is \(\mathbb Z\) locally and \(\mathbb R\) after
realification—not the rational-Witt coordinate ring.

The isomorphism is `(4)` plus assumptions 1--2.  Thus the abstract multiplicative and
degree-zero arguments are closed.  Remaining arithmetic work is construction of \(A,r,J\)
on Deninger's rational-Witt space and proof of assumptions 1--3 there.

## Higher homotopy warning

The bar filtration has higher derived symmetric-power and Tor terms.  Therefore no canonical
triangle
\[
 \tau_{\ge1}\operatorname{Fib}(r)\to Q(A,J)\to B
\]
follows from `(1)`.  Such a triangle would require a separate flatness or cotangent-complex
degeneration theorem.  The stable module cofiber is only the linear approximation to the
multiplicative quotient.

## Hostile audit

- Replacing `(1)` by an underlying-module cofiber loses multiplication.
- Unitalizing a positive augmentation ideal would require a multiplicative rank section,
  which quadratic transfers do not supply.
- Formula `(4)` proves degree zero only.  It neither identifies nor discards higher Witt/Tor
  classes.
- The theorem is generic higher algebra.  It does not construct the arithmetic site object,
  real regulator, Hodge metric, or zeta comparison.

## References

- Jacob Lurie, *Higher Algebra*, §§3.1.3, 3.2.3, 4.4.2, 5.4.4, 7.1.3:
  https://www.math.ias.edu/~lurie/papers/HA.pdf
- Christopher Deninger, *Rational Witt vectors and associated sheaves*:
  https://arxiv.org/abs/2508.05329

## Log

- 2026-07-26 — multiplicative quotient universal property and degree-zero theorem proved;
  false stable-cofiber higher-fiber identification explicitly excluded.
