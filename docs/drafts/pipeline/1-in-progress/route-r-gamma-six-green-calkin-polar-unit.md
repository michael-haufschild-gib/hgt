# Route R Gamma-six Green/Calkin polar unit

- **ID:** `route-r-gamma-six-green-calkin-polar-unit`
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper) / POSITIVE POLAR SOURCE / NO-GO
- **Parents:**
  `route-r-cross-prime-stokes-calkin-compression-landing.md` and
  `../2-fully-proven/new_scientific_knowledge/deninger/deninger-gamma-six-shell-green-trace-ideal-transgression.md`
- **Status:** `[PAPER-PROVED] [SOURCE POLAR UNIT CONSTRUCTED]
  [STOKES-FLATNESS DOES NOT ANNIHILATE] [LEAN DEFERRED DURING REFACTOR] [NOT RH]`
- **Exact advance:** the corrected Gamma-six Möbius tensor square admits a canonical unbounded
  Green renormalization whose bounded extension is an essentially isometric, coefficient-faithful
  Calkin polar unit.  This constructs the nonfunctorial positive source metric demanded by the
  terminal pre-polar Route-R audit on the Gamma-six/Wold chart.  Its induced Stokes flatness is
  nevertheless compatible with every nonzero constant Calkin symbol, so it does not annihilate
  the fixed cross-prime curvature.

## 1. Source input

Retain the notation of the Gamma-six shell Green transgression.  For

\[
 I_m=\{k:6^m\le k<6^{m+1}\},\qquad |I_m|=5\cdot6^m,
\]

let \(G_6e_k=6^{-m}e_k\) on \(I_m\).  The corrected source tensor square is the rectangular shell
operator

\[
 \mathcal W e_k=W_m\otimes e_k,
 \qquad W_m=6^{-m}v+E_m,
 \qquad v=\Theta\otimes\Theta\ne0,
\tag{1}
\]

and the dependency-closed source estimate is

\[
 \sum_{m\ge3}6^m\lVert E_m\rVert<\infty.
\tag{2}
\]

Thus \(\mathcal W\in\mathcal L^{1,\infty}\setminus\mathcal L^1\) and
\(\mathcal W-\mathcal G_v\in\mathcal L^1\), where
\(\mathcal G_ve_k=6^{-m}v\otimes e_k\).

The inverse \(G_6^{-1}\) is unbounded.  It is therefore not legitimate to apply it to an arbitrary
weak-trace class.  The full-source estimate (2), rather than ideal formalism, is what makes the
following renormalization exist.

## 2. Green right-renormalization theorem

Define initially on the finite shell core

\[
 \mathcal R_6:=\mathcal W G_6^{-1}.
\tag{3}
\]

Let \(V_v\) be the constant coefficient embedding

\[
 V_ve_k=v\otimes e_k.
\tag{4}
\]

### Theorem 2.1 — bounded Calkin polar unit

The operator in (3) extends uniquely to a bounded operator and

\[
 \boxed{\mathcal R_6=V_v+K_6,\qquad K_6\text{ compact}.}
\tag{5}
\]

Consequently

\[
 \boxed{
 \mathcal R_6^*\mathcal R_6-\lVert v\rVert^2I\text{ is compact},
 \qquad
 \lVert[\mathcal R_6]\rVert_{\mathrm{Calkin}}=\lVert v\rVert>0.}
\tag{6}
\]

### Proof

For \(k\in I_m\),

\[
 \mathcal R_6e_k
   =6^mW_m\otimes e_k
   =(v+6^mE_m)\otimes e_k.
\tag{7}
\]

Equation (2) implies \(6^m\lVert E_m\rVert\to0\), and also bounds the sequence.  Hence the shell
diagonal error

\[
 K_6e_k=6^mE_m\otimes e_k
\]

is bounded.  Every shell has finite multiplicity, while its block norm tends to zero, so truncation
to the first finitely many shells converges to \(K_6\) in operator norm.  Therefore \(K_6\) is
compact, proving (5).

The constant embedding satisfies \(V_v^*V_v=\lVert v\rVert^2I\).  Expanding
\((V_v+K_6)^*(V_v+K_6)\) shows that its difference from \(\lVert v\rVert^2I\) is compact.  The
Calkin image of \(V_v\) is a scaled isometry, so its norm, and hence the norm of
\([\mathcal R_6]\), is \(\lVert v\rVert\).  Since \(v\ne0\), the class is nonzero.  ∎

### Corollary 2.2 — coefficient faithfulness

For any bounded coefficient reader \(\lambda_v\) with \(\lambda_v(v)=1\),

\[
 (\lambda_v\otimes1)\mathcal R_6=I+K_{\lambda},
 \qquad K_{\lambda}\text{ compact}.
\tag{8}
\]

Thus the source polar unit maps to the unit Calkin class.  It does not erase the Gamma-six
coefficient or replace it by a target-selected scalar.

## 3. Renormalized Stokes flatness

The source coface satisfies

\[
 \mathcal C_6(\mathcal W)-\frac16\mathcal W\in\mathcal L^1,
\qquad
 \mathcal C_6(\mathcal A_6(X))_m=X_{m+1}.
\tag{9}
\]

On the right-renormalized blocks, (9) becomes

\[
 (\mathcal C_6\mathcal R_6-\mathcal R_6)_m
 =6^{m+1}\left(W_{m+1}-\frac16W_m\right).
\tag{10}
\]

Trace-class membership in (9) gives

\[
 \sum_m6^m\left\lVert W_{m+1}-\frac16W_m\right\rVert<\infty.
\]

Therefore the block norms in (10) tend to zero.  The same finite-shell truncation argument proves

\[
 \boxed{\mathcal C_6(\mathcal R_6)-\mathcal R_6\text{ is compact}.}
\tag{11}
\]

The Green normalization converts the weight-\(1/6\) weak-trace principal class into a weight-one
Calkin polar unit.  This is a genuine period-one source Stokes law before Xi specialization.

## 4. Conjecture, proof-or-failure loop

### C1 — the unbounded Green inverse destroys the full corrected source

`[FALSIFIED]`.  The trace-order remainder (2) is stronger than needed: it makes the renormalized
remainder block norms tend to zero, so the full source has the bounded extension (5).

### C2 — right renormalization supplies the missing positive polar reduction

`[PROVED ON THE GAMMA-SIX/WOLD SOURCE CHART]`.  Formula (6) is a canonical positive fixed metric
modulo compacts, selected by the literal first surviving Möbius atom and ordinary-integer shell
multiplicity.  It is nonfunctorial under the horizontal hyperbolic gauge because the fixed Green
inverse has chosen the critical exponent.  Thus it lies outside the C33 naturality no-go for the
pre-polar source.

This does not yet identify the source shell Hilbert space with the fixed archimedean Sonin carrier.
That target comparison remains part of the physical landing theorem.

### C3 — renormalized Stokes flatness annihilates the Route-R curvature

`[FALSIFIED]`.  Equation (11) is compatible with every constant nonzero Calkin symbol.  In the
exact model \(E_m=0\), \(\mathcal R_6=V_v\), and for any bounded shell-constant operator \(T\),

\[
 \mathcal C_6(V_vT)=V_vT
\]

while \([V_vT]\ne0\) whenever \([T]\ne0\).  Hence period-one flatness of the polar unit, or of its
product with a constant orientation symbol, cannot imply compactness.  In particular it cannot
annihilate the fixed two-prime Sonin class, whose nonzero off-neutral coefficient is already
Calkin-injective.

### C4 — transport the singular source trace as a positive cyclic trace on the Calkin target

`[FALSIFIED ON THE FULL CALKIN ALGEBRA]`.  A positive unital trace on the Calkin algebra cannot
exist.  If \(s_1,s_2\) are two isometries with orthogonal ranges, traciality would give
\(\tau(s_is_i^*)=\tau(s_i^*s_i)=\tau(1)\) for both \(i\), while positivity and
\(s_1s_1^*+s_2s_2^*\le1\) give \(2\tau(1)\le\tau(1)\).  Thus a nonzero positive trace cannot be
transported through (5).

The restricted Sonin principal-relative cyclic trace avoids this full-algebra obstruction, but it
does not annihilate a commutator square: cyclicity kills the signed commutator, while the positive
quantity lives in \(C^*C\).  Finite matrices already exhibit a nonzero commutator with positive
trace of its adjoint square.  Therefore cyclicity supplies no missing radical law.

### C5 — the polar unit makes the physical comparison automatic

`[FALSIFIED]`.  Equation (8) identifies the source coefficient with a fixed metric unit only on the
Gamma-six/Wold shell chart.  A coefficient-faithful map to the fixed Sonin/Xi conormal must still
preserve the noncompact cross-prime symbol.  Existing corona descent kills that finite atom, and
bounded or norm-summable descent is already impossible.  Universal Hilbert-space stabilization
would discard prime/depth/orientation provenance and is not an arithmetic comparison.

## 5. Frontier effect

The strongest surviving Route-R producer has split into two logically distinct parts.

1. **Positive source polarization:** now constructed explicitly on the full corrected Gamma-six
   shell source by (5)--(8).  Its Stokes-flatness law (11) is unconditional.
2. **Zero-specific physical radical law:** still open.  One must construct a place-marked,
   coefficient-faithful comparison from this polar source to the fixed Sonin/Xi Calkin carrier and
   prove, using the actual Xi zero equation and a genuinely bilinear/nonlocal Euler--Gamma--Poisson
   identity, that the retained cross-prime curvature lies in the polar radical.

The second statement cannot be replaced by flatness, cyclicity, corona quotienting, trace-class
descent, norm-summable correction, or an abstract unitary identification.  In the fixed `(2,3)`
chart it remains exactly

\[
 [C_A(2\operatorname{Re}\rho-1)]=0,
\]

equivalently the physical modular square vanishes.  The new theorem removes absence of a positive
source polar unit as an excuse; it does not prove this zero-specific radical identity and therefore
does not prove RH.

## 6. Lean plan after the corpus refactor

No new functional analysis is required.  Formalization should use a generic finite-multiplicity
block-diagonal lemma:

```text
summable (fun m => 6^m * ‖E m‖)
  -> isCompact (blockDiagonal (fun m => 6^m • E m))
```

and then instantiate the paper-proved Gamma-six trace-order remainder.  Required declarations:

```text
gammaSixGreenRightRenormalization
gammaSixGreenRightRenormalization_compactEq_constantEmbedding
gammaSixGreenRightRenormalization_adjoint_mul_compactEq
gammaSixGreenRightRenormalization_coface_compactEq_self
```

Do not formalize a source-to-Sonin comparison until its mathematical construction is proved.

## Log

- 2026-08-11 — C1 falsified; C2 proved on the full corrected Gamma-six/Wold source; C3--C5
  falsified.  The source polar unit exists and is Stokes-flat, but annihilation remains the
  zero-specific nonlocal comparison law.
