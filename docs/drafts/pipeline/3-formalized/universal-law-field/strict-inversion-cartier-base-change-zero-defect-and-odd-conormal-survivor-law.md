# Strict inversion/Cartier base change, zero defect, and odd-conormal survivor law

- **ID:** ULF-INV-1
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean-certified, ring-level chart)
- **Lean module:** `GaloisForLFunctions.HTGeometry.ConstitutiveStrictInversionCartier`
- **Status:** [LEAN-CERTIFIED] [UNIVERSAL-LAW FIELD]
  [LIVE-SOURCE STRESS TEST] [STRICT BECK--CHEVALLEY]
  [ZERO K-THEORY DEFECT] [ODD CONORMAL SURVIVOR]
  [BRIDGE/CORPUS COLLISION] [NOT RH] [NO PROJECT AXIOMS]

## 1. Algebraic square

Let \(k\) be a commutative ring and set

\[
 R=k[q,q^{-1}],
 \qquad
 I=(q-1),
 \qquad
 S=R/I\cong k.
\tag{IC.1}
\]

Let

\[
 \sigma:R\longrightarrow R,
 \qquad
 \sigma(q)=q^{-1},
\tag{IC.2}
\]

and let \(\varepsilon:R\to S\) be Cartier specialization \(q\mapsto1\).

## 2. Strict base-change theorem

### Theorem 2.1

The ideal \(I\) is \(\sigma\)-stable, the induced involution on \(S\) is the identity, and

\[
 \varepsilon\circ\sigma=\varepsilon.
\tag{IC.3}
\]

Consequently, on perfect complexes there is a canonical natural equivalence

\[
 S\otimes_R^{\mathbb L}\sigma^*(-)
 \simeq
 S\otimes_R^{\mathbb L}(-).
\tag{IC.4}
\]

The Beck--Chevalley comparison for inversion followed by Cartier specialization is therefore an
equivalence. Its fibre and cofiber vanish after every functor that preserves equivalences,
including algebraic \(K\)-theory.

### Proof

One computes

\[
 \sigma(q-1)=q^{-1}-1=-q^{-1}(q-1),
\tag{IC.5}
\]

so \(\sigma(I)=I\). Equation (IC.3) follows because both composites send \(q\) to \(1\).
The two \(R\)-module structures on \(S\) used in (IC.4) are therefore identical. Derived tensor
with identical bimodules gives the natural equivalence. Functoriality proves the last statement.

## 3. Odd conormal survivor

The strict square has no comparison defect, but inversion acts nontrivially on the derived normal
direction.

### Theorem 3.1

Let

\[
 e=[q-1]\in I/I^2.
\tag{IC.6}
\]

Then

\[
 \boxed{\sigma(e)=-e.}
\tag{IC.7}
\]

Moreover

\[
 \operatorname{Tor}_1^R(S,S)\cong I/I^2\cong S e,
\tag{IC.8}
\]

and the induced inversion action on this Tor line is multiplication by \(-1\).

### Proof

Modulo \(I^2\), equation (IC.5) has coefficient

\[
 -q^{-1}\equiv-1\pmod I,
\]

which proves (IC.7). The standard resolution

\[
 0\to R\xrightarrow{q-1}R\to S\to0
\]

computes (IC.8), compatibly with the conormal identification.

## 4. Positive square

Define the inversion-invariant positive displacement

\[
 E(q)=q+q^{-1}-2.
\tag{IC.9}
\]

Then

\[
 E(q)=\frac{(q-1)^2}{q},
\tag{IC.10}
\]

so its initial normal term is \(e^2\). Inversion erases the orientation sign after squaring:

\[
 \sigma(e^2)=e^2.
\tag{IC.11}
\]

Thus the strict algebraic package contains:

1. zero Beck--Chevalley defect;
2. a nonzero odd Tor/conormal line;
3. an even positive square.

## 5. Multiplicative Moore no-selection corollary

For a prime \(p\) and real \(a\), the radial mate gain

\[
 \delta_p(a)=p^{2a}
\tag{IC.12}
\]

is always a square in \(\mathbb R_{>0}\):

\[
 \delta_p(a)=(p^a)^2.
\tag{IC.13}
\]

Therefore any coefficient-relative law that declares a multiplicative defect trivial merely when
it has a positive square root declares \(\delta_p(a)\) trivial for every \(a\), not only \(a=0\).
Moore-cell fillability cannot select the critical radial origin.

## 6. Exact route leverage

This theorem rules out two field mechanisms for the source-normal dagger landing:

1. it cannot be the Beck--Chevalley defect of the strict algebraic inversion/Cartier square,
   because that defect is zero;
2. it cannot be positive square-root fillability of the multiplicative mate gain, because every
   radial gain is already a positive square.

The only algebraic survivor is the odd conormal/Tor orientation. A successful construction must
compare it with an additional analytic, topological, bornological, or source-marked dagger
doctrine whose comparison is not already the strict square (IC.4).

## 7. Hostile scope

1. The strict square and odd conormal are already implicit in the corpus's derived-selection
   geometry. This card is a field-native consolidation, not a novelty claim.
2. A nonzero defect may arise after completion, domain restriction, or non-exact functors; the
   theorem does not rule those out.
3. The theorem does not construct the required analytic comparison.
4. It provides unconditional elimination of two candidate mechanisms, not an RH proof.


## 8. Certified scope recorded at Lean certification (ULF-INV-1)

Certified at the ring level, over `R = k[q,q⁻¹]` for an arbitrary commutative ring `k`:
`ε ∘ σ = ε` for every element of `R` (`cartier_inversion`), the exact identity
`σ(q−1) = −q⁻¹(q−1)` and hence `σ`-stability of `I = (q−1)`, the oddness of the conormal class
`σ(e) + e ∈ I²`, the identity `q + q⁻¹ − 2 = (q−1)²q⁻¹` with `σ`-invariance of that displacement,
and the multiplicative no-selection corollary `p^{2a} = (p^a)²` for every real `a`.

Not certified: the derived statement (IC.4) and the identification (IC.8) of `Tor₁(S,S)` with the
conormal line. Both are formal consequences of `ε ∘ σ = ε` and of the free resolution
`0 → R →(q−1) R → S → 0`, but the derived-functor layer is not constructed in the corpus; the
certified content is the ring-level input those statements consume, which is exactly what the
elimination argument of §6 uses.
