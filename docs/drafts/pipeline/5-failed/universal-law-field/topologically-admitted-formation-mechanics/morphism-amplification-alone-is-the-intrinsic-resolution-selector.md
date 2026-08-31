# Morphism amplification alone is the intrinsic resolution selector

- **ID:** ULF-TAFM-NG3
- **Status:** `[FALSIFIED]`
- **Killed claim:** divergence of one formation kernel's Lipschitz amplification is an intrinsic,
  representation-independent selection obstruction
- **Positive survivor:** ULF-TAFM-5, gauge-covariant formation--detector action
- **Lean status:** survivor paper-proved; Lean open; missing infrastructure must be built later

## Claim tested

ULF-TAFM-3 correctly proves, after equipping every finite tensor target with the discrete metric,
that exact nonneutral formation forces kernel amplification to diverge. The stronger interpretation
tested here was

\[
 \text{kernel amplification itself is the coordinate-free missing selector.}
 \tag{NG3.1}
\]

## Exact killing countermodel

Let \(Y=\{0,1\}\), choose distinct full-support Bernoulli laws \(p_0,p_1\), and put

\[
 X=Y^{\mathbb N},
 \qquad
 \mu_i=p_i^{\otimes\mathbb N}.
\]

Equip \(X\) with the prefix ultrametric

\[
 d_\theta(x,x')=\theta^{m(x,x')},
 \qquad 0<\theta<1.
\]

The prefix map \(\pi_d:X\to Y^d\) exactly forms \(p_i^{\otimes d}\).

1. With the discrete metric on \(Y^d\),

   \[
   \alpha(\pi_d)=\theta^{-(d-1)}.
   \]

2. With the inherited prefix ultrametric on \(Y^d\),

   \[
   \alpha(\pi_d)=1.
   \]

3. For a Neyman--Pearson threshold detector \(f_d\), its Lipschitz cost is respectively

   \[
   1
   \qquad\text{and}\qquad
   \theta^{-(d-1)}.
   \]

4. In both gauges the pulled-back source effect is identical and has exact cost

   \[
   \operatorname{Lip}(f_d\circ\pi_d)=\theta^{-(d-1)}.
   \]

Thus the same mathematical formation has either diverging or unit morphism amplification. The
target detector absorbs the reciprocal change. Claim `(NG3.1)` is false.

## Exact why

An operator norm belongs to a morphism **between two gauged effect spaces**. Rescaling or changing
the target gauge changes the operator norm. Treating it as an invariant of the underlying Markov
kernel forgets half its type.

The failure indicts the representation, not the fixed-gauge theorem. Resolution cannot be assigned
canonically to one edge without a source law selecting gauges on both endpoints.

## Relentless-interrogation replacement

Based on what killed the idea, the stronger conjecture was:

> Resolution belongs to a complete formation--detector path. Local edge prices transform as gauge
> potentials; intermediate changes cancel; composition loss is a gauge-invariant cocycle.

ULF-TAFM-5 proves this exactly:

\[
 \mathcal R^q_\mu(r)
 \le q_X(K^*f)
 \le\left(\prod_j\alpha_q(K_j)\right)q_Y(f).
\]

Under scalar gauge changes, the product and detector factors telescope. For positive finite edge
norms, the logarithmic composition defect is nonnegative, gauge invariant, and obeys the exact
two-cocycle identity.

## Positive survivor and insight delta

The survivor is not “use a different norm.” It is an allocation law:

\[
 \boxed{
 \text{unbounded source distinction can migrate among formation, detector, analytic modulus,
 observer resolution, and path length, but cannot disappear}.}
\]

This corrects the RH gate. A useful source theorem must bound the complete endpoint-fixed action,
not one conveniently gauged kernel norm.

## Audit

- **Paper status:** ULF-TAFM-5 is dependency-closed and `[PAPER-PROVED]`.
- **Lean status:** open; current phase forbids Lean writes/builds. All missing infrastructure is a
  future proof obligation, not a pivot condition.
- **Parent-theory status:** operator norm submultiplicativity and Dobrushin coefficients are known;
  survivor is labelled `[BRIDGE]`. Its value is the exact countermodel and corrected corpus gate.
- **Further salvage:** finite Feller admission itself was separately classified in ULF-TAFM-4.

## Closure

Route retired. No morphism-only amplification claim should be used as coordinate-free selection.
Only complete source-fixed formation--detector action survives.
