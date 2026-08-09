# Reporter-constrained promotion selection and strictification trilemma law

- **ID:** ULF-OPM-4
- **Stage:** 2-fully-proven
- **Type:** PROMOTION-SELECTION MECHANISM THEOREM
- **Statement:** A source reporter descends through minimal exchange strictification exactly when it
  is constant on the generated exchange congruence; any reporter detecting a critical pair makes
  commuting strictification, law executability, and reporter preservation jointly impossible.
- **Status:** [PAPER-PROVED] [DEPENDENCY-CLOSED] [SELECTION LAW]
  [STRICT VERSUS HISTORY PROMOTION] [LEAN-CERTIFIED] [NOT RH]

## 1. Setup

Let `f,g:X->X`, let `R_(f,g)` be the least exchange congruence from ULF-OPM-2, and write

\[
 \pi:X\longrightarrow Q_{f,g}=X/R_{f,g}.
 \tag{PS.1}
\]

Let

\[
 r:X\longrightarrow B
 \tag{PS.2}
\]

be a source reporter fixed before strictification.

## 2. Exact reporter-descent criterion

### Theorem 2.1

The following are equivalent.

1. There exists a reporter `rbar:Q_(f,g)->B` such that

   \[
     r=\bar r\pi.
     \tag{PS.3}
   \]

2. The reporter is constant on the full generated exchange congruence:

   \[
     R_{f,g}(x,y)\Longrightarrow r(x)=r(y).
     \tag{PS.4}
   \]

When it exists, `rbar` is unique.

### Proof

If `(PS.3)` holds and `R_(f,g)(x,y)`, then `pi(x)=pi(y)`, so applying `rbar` gives `(PS.4)`.
Conversely, `(PS.4)` says exactly that `r` is constant on quotient classes, so quotient
elimination defines `rbar`. Surjectivity of `pi` gives uniqueness. QED.

### Corollary 2.2 -- critical-pair detector no-go

If there is an `x` with

\[
 r(f(gx))\neq r(g(fx)),
 \tag{PS.5}
\]

then no reporter on the strict quotient pulls back to `r`.

### Proof

The pair `(f(gx),g(fx))` belongs to `R_(f,g)`, contradicting `(PS.4)`. QED.

## 3. Strictification trilemma

### Theorem 3.1

Let `q:X->Y` be any observer. Suppose there are laws `F,G:Y->Y` such that

\[
 qf=Fq,
 \qquad
 qg=Gq,
 \qquad
 FG=GF.
 \tag{PS.6}
\]

If `r` detects one exchange pair as in `(PS.5)`, there is no reporter `R:Y->B` satisfying

\[
 r=Rq.
 \tag{PS.7}
\]

Therefore no mechanism can retain all three:

1. execution of both source laws after observation;
2. strict commutation after observation;
3. preservation of a critical-pair-detecting source reporter.

At least one must be promoted differently or abandoned.

### Proof

Equations `(PS.6)` give

\[
\begin{aligned}
q(f(gx))
 &=F(G(qx))\\
 &=G(F(qx))\\
 &=q(g(fx)).
\end{aligned}
\]

If `(PS.7)` held, applying `R` would give equality of the two reporter values, contradicting
`(PS.5)`. QED.

This is a selection mechanism, not another stored field. A declared conserved reporter can forbid
strict quotient promotion and force extension-valued, higher-coherent, or singular promotion.

## 4. Heisenberg calibration

Use the same-residual comparison ULF-OPM-3. Let

\[
 H\xrightarrow{\pi}\mathbb Z^2
 \]

be the Heisenberg strict observer and let

\[
 c(a,b,z)=z
 \tag{PS.8}
\]

be the central-history reporter. For the exchange generators,

\[
 c(FG)=1,
 \qquad
 c(GF)=0.
 \tag{PS.9}
\]

Hence `c` does not descend through `pi`. By contrast, the coordinate reporters

\[
 x(a,b,z)=a,
 \qquad
 y(a,b,z)=b
 \tag{PS.10}
\]

do descend. The declared reporter family therefore makes the promotion decision exact:

- preserving only multiplicities permits strict abelianization;
- preserving exchange history forbids it and requires central promotion.

No appeal to route provenance, novelty, curvature, or hidden-object geometry is used.

## 5. Strongest positive survivor

Strictification is neither good nor bad intrinsically. It is the universal promotion relative to a
reporter doctrine that annihilates `R_(f,g)`. The precise invariant is the restriction map

\[
 \{\text{source reporters}\}
 \longrightarrow
 \{\text{reporters constant on }R_{f,g}\}.
 \tag{PS.11}
\]

Its kernel/blind sector is exactly the information sacrificed by strict promotion. A source-normal
selection theorem must therefore declare which reporter coframe is conserved before choosing a
promotion mode.

## 6. Sharp boundaries

1. The theorem does not construct the reporter; source provenance remains load-bearing.
2. A reporter may fail to descend yet still become a relative, affine, or higher reporter after
   promotion. The theorem forbids only ordinary endpoint factorization.
3. If all declared reporters are constant on `R_(f,g)`, strictification is permitted but not forced;
   an unreported history may still exist.
4. Joint faithfulness of a reporter family can forbid every nontrivial quotient, but only after
   faithfulness is proved.
5. No topology, positivity, HT, physical cost, or RH conclusion follows.

## Lean certification

Formalized without project axioms in
`GaloisForLFunctions.HTGeometry.ConstitutiveExchangePromotionSelection`:

1. reporter descent iff exchange-congruence constancy;
2. uniqueness of descended reporter;
3. critical-pair detector no-go;
4. strictification trilemma for arbitrary commuting descended laws;
5. Heisenberg central reporter nonfactorization and coordinate-reporter factorization.

The module is wired into `GaloisForLFunctions.HTGeometry.UniversalLawField`.

## Log

- 2026-08-09 -- conserved reporters identified as the first exact promotion-mode selector.
