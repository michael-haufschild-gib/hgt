# Deninger Gamma--Green quadratic mate curvature

- **Stage:** 3-formalized

- **ID:** `deninger-gamma-green-quadratic-mate-curvature`
- **Route:** L / Deninger arithmetic cohomology
- **Status:** fully proved on paper; RH not proved
- **Parent:** `deninger-gamma-green-positive-gauge-admission`
- **Frontier input:** the source-inverse/analytic-adjoint fracture and the
  completed Green provenance

## Result

Let (q) be an actual Xi-divisor copy and put

\[
  f_q=\operatorname{fract}(q)=2\bigl(\Re\rho_q-	frac12\bigr)\in\mathbb R.
\]

Let (b_q) be the actual ordered ((2,3)) Gamma/co-Poisson boundary
coefficient, (g_q>0) its already constructed Gamma--Green gauge, and

\[
  \beta_q=\frac{b_q}{1+|b_q|}.
\]

The positive-gauge theorem gives (b_q=f_qg_q).  Define the normalized
mate-curvature gauge and energy by

\[
  \widehat g_q=\frac{g_q}{1+|b_q|},
  \qquad
  E_q=f_q^2\widehat g_q.
  \tag{1}
\]

Then:

1. (widehat g_q>0);
2. (E_q\geq0);
3. (E_q=0) if and only if (Re\rho_q=1/2);
4. (E_q>0) at every off-line divisor copy;
5. for every completed Xi coefficient (a), every divisor copy (q), and
   every all-cross-prime packet coordinate (i),

\[
 \bigl(A_\Gamma C G_a\bigr)(q,i)
 =E_q\,
   \bigl(H_{\mathrm{or}}(Ra)\bigr)(q)\,h_{\mathrm{CW}}(i).
 \tag{2}
\]

Here (G_a) is completed Green provenance, (R) is completed Riesz
conjugation, (H_{\mathrm{or}}) is oriented Hodge transport,
(h_{\mathrm{CW}}) is the nonzero Calderon--Witt incidence horizon,
(C) is the isometric Xi-to-incidence comparison, and (A_\Gamma) is the
bounded normalized Gamma admission operator.

Thus Gamma admission does not pair two odd factors with opposite signs.
It converts the Deninger duality--adjunction fracture in Green provenance
into a positive second-order mate curvature.

## Proof

The denominator in `(1)` is strictly positive because
(1+|b_q|\geq1).  Since (g_q>0), this proves
(widehat g_q>0).

The actual Gamma factorization is

\[
 b_q=f_qg_q.
 \tag{3}
\]

Dividing `(3)` by the same positive real denominator gives

\[
 \beta_q=f_q\widehat g_q.
 \tag{4}
\]

Completed Green provenance is coefficientwise

\[
 G_a(q)=f_q\bigl(H_{\mathrm{or}}(Ra)\bigr)(q).
 \tag{5}

The incidence comparison tensors a coefficient with the fixed horizon,

\[
 (Cx)(q,i)=x(q)h_{\mathrm{CW}}(i),
 \tag{6}

and Gamma admission is fibrewise multiplication by (eta_q).  Substitute
`(4)` and `(5)` into `(6)`:

\[
\begin{aligned}
 (A_\Gamma C G_a)(q,i)
 &=\beta_qG_a(q)h_{\mathrm{CW}}(i)\\
 &=f_q\widehat g_q\,
   f_q\bigl(H_{\mathrm{or}}(Ra)\bigr)(q)
   h_{\mathrm{CW}}(i)\\
 &=E_q\bigl(H_{\mathrm{or}}(Ra)\bigr)(q)
   h_{\mathrm{CW}}(i).
\end{aligned}
\]

This proves `(2)`.  Nonnegativity of (E_q) follows from
(f_q^2\geq0) and (widehat g_q>0).  Because the second factor is strictly
positive, (E_q=0\iff f_q^2=0\iff f_q=0\).  The exact fracture formula then
gives

\[
 E_q=0\iff \Re\rho_q=\tfrac12.
\]

Its negation and strict positivity of both factors give item 4.

No zero-location, RH, source-null-homotopy, analytic continuation, or
positivity conjecture is used.

## Scientific content and novelty boundary

The individual ingredients were known in this repository:

- the duality--adjunction fracture (f_q);
- completed Green provenance (G_a=f_qH_{\mathrm{or}}(Ra));
- the actual Gamma factorization (b_q=f_qg_q), (g_q>0);
- bounded normalized Gamma admission.

The new theorem is their exact composition `(2)` and the radical
classification of the resulting scalar (E_q).  Corpus search found no
prior theorem identifying (A_\Gamma C G_a) with a positive square of the
source mate fracture.

This is not a proof of RH and not a construction of the missing Cartier
comparison.  It is a sharp obstruction/classification theorem.  It removes
three false Deninger mechanisms:

1. reflection-odd cancellation cannot annihilate (A_\Gamma C G_a), since
   its two fracture signs multiply and its scalar curvature is nonnegative
   on both reflection sides;
2. a scalar codiagonal or bar-parity identity cannot supply the
   null-homotopy, since both fracture occurrences have the same sign;
3. a nowhere-zero Frobenius/Nakayama gauge cannot help, since it changes
   only (widehat g_q>0) and preserves the exact radical.

## Deninger-only frontier exposed

Other Route-L constructions already provide Gamma transport, Green
provenance, Hellinger completion, and Calderon--Witt incidence.  Deninger's
unique remaining contribution is now narrower:

> Construct the finite prime/depth failure-nerve mate from the actual
> rational-Witt/Frobenius source, pass it strictly and nonannihilatingly
> through cofinal Cartier base change, and prove that its source
> transpose--analytic dagger curvature realizes the left side of `(2)`.
> A source Bianchi/null-homotopy theorem must then kill this *positive
> quadratic curvature*, not an odd scalar defect.

The comparison and its null-homotopy must be source-first.  Defining either
from Xi coordinates, from (E_q), or by requiring its image to vanish is
circular and is rejected.

## Hostile falsifiers

- If the normalized Gamma coefficient is not `(4)`, theorem fails.
- If completed Green provenance has another independent summand, `(2)`
  fails and that summand is the positive survivor.
- If the all-cross-prime comparison changes packet coefficients, `(2)`
  fails.
- If a source-generated horizontal boundary cancels `(2)` by ordinary
  reflection parity alone, it contradicts (E_q>0) off line.
- If the proposed Cartier mate is defined only after choosing (q), it is
  not the needed arithmetic source construction.

## Formalization target

New Lean module should prove, unconditionally:

- positivity of (widehat g_q);
- the exact normalized factorization `(4)`;
- nonnegativity, strict off-line positivity, and radical of (E_q);
- pointwise operator identity `(2)` for arbitrary completed provenance.

- 2026-08-06 — Formalization re-verified on this toolchain: the named Lean module exists, is wired into `GaloisForLFunctions.RHTower`, builds, uses no `native_decide`, and every audited declaration depends only on `propext, Classical.choice, Quot.sound`.  Every gate this card states is closed; what the card lists as still open is its declared successor core, not this theorem.  Card moves to `3-formalized`.
