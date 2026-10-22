# Naive adelic \(L^2\) Kummer completion

- **ID:** `deninger-naive-adelic-l2-kummer-completion`
- **Stage:** 5-failed
- **Type:** FALSIFIED with literature-proved positive survivor
- **Label:** `DAC_NAIVE_ADELIC_L2_KUMMER_COMPLETION_NO_GO`
- **Parent:** `deninger-derived-coefficient-hilbert-hodge-descent`
- **Statement:** completing the logarithmic Kummer coefficient only in
  adelic \(L^2\) gives a canonical polarization but destroys the closed
  product-formula constraint and has scalar centered power action.

## Source construction

Let \(Y\) be the Allcock--Vaaler space of places of
\(\overline{\mathbb Q}\), with its Galois-invariant regular measure
\(\lambda\).  For
\[
 \mathcal G=\overline{\mathbb Q}^{\times}/\operatorname{Tor}
\]
write
\[
 f_\alpha(y)=\log\|\alpha\|_y .
\]
Every \(f_\alpha\) is locally constant with compact support.  If a
number field \(K\) contains \(\alpha,\beta\), then
\[
 B_2(\alpha,\beta)
 =\int_Y f_\alpha f_\beta\,d\lambda
 =\frac1{[K:\mathbb Q]}
   \sum_{v\in M_K}[K_v:\mathbb Q_v]\,
       \log|\alpha|_v\log|\beta|_v.                              \tag{1}
\]
The right side is independent of \(K\): after a finite extension
\(L/K\), local degrees above each \(v\) sum to the old normalized local
degree.  The form is positive definite on \(\mathcal G\), because
\(B_2(\alpha,\alpha)=0\) forces every logarithmic absolute value to
vanish, hence the Weil height is zero and \(\alpha\) is torsion.

Allcock--Vaaler prove:

1. the \(L^1\)-closure of the \(f_\alpha\) is the codimension-one
   product-formula hyperplane
   \[
     \mathcal X=\{f\in L^1(Y,\lambda):\int_Yf\,d\lambda=0\};
                                                                    \tag{2}
   \]
2. for every \(1<p<\infty\), their closure in \(L^p\) is all of
   \(L^p(Y,\lambda)\).  In particular,
   \[
     \overline{\{f_\alpha\}}^{\,L^2}=L^2(Y,\lambda).                 \tag{3}
   \]

Thus `(1)` supplies a canonical source Hilbert metric, but `(3)` says
that the product formula is not a closed \(L^2\) condition.

## Tate-power classification

Deninger defines \(\mathbb R(s)\) so that \(q\in\mathbb Q_{>0}\) acts
by \(q^{-s}\).  Since
\[
 f_{\alpha^n}=n f_\alpha ,
\]
the \(s\)-twisted power map is
\[
 P_n^{(s)}f_\alpha=n^{-s}f_{\alpha^n}
                  =n^{1-s}f_\alpha.                               \tag{4}
\]
Consequently
\[
 B_2(P_n^{(s)}x,P_n^{(s)}y)
 =n^{2-2s}B_2(x,y).                                                \tag{5}
\]
For \(n>1\), the weight-one Hodge scaling law
\(B_2(P_nx,P_ny)=nB_2(x,y)\) holds precisely at \(s=\tfrac12\).
At that twist,
\[
 P_n^{(1/2)}=\sqrt n\,\mathrm{id},
 \qquad n^{-1/2}P_n^{(1/2)}=\mathrm{id}.                           \tag{6}
\]
At Deninger's regulator twist \(s=1\), the Kummer power is invariant,
exactly as in his equivariant regulator construction.

## No-go theorem

`[PROVED HERE] [DAC_NAIVE_ADELIC_L2_KUMMER_COMPLETION_NO_GO]`

There is no nonzero continuous functional
\[
 I:L^2(Y,\lambda)\longrightarrow\mathbb R
\]
whose restriction to every logarithmic Kummer function is the
product-formula integral.  Indeed, that restriction vanishes and its
domain is dense by `(3)`, so continuity forces \(I=0\).

Moreover `(6)` makes the centered power action the identity on the
entire \(L^2\)-completion.  Any strongly continuous suspension of this
action has scalar centered generator and cannot supply the nontrivial
zeta-zero spectrum.

This rules out bare \(L^2(Y,\lambda)\) as Deninger's global arithmetic
\(H^1\).  It does not rule out using `(1)` as one part of the source
coefficient topology.

## No-go closure

- **Exact killing theorem/mechanism:** the product-formula Kummer
  functions are dense in \(L^2\), so their vanishing integral has no
  nonzero continuous extension; the half-Tate centered power action is
  also scalar.
- **Strongest positive survivor:** `(1)` is a canonical positive
  Galois-invariant Kummer form, `(5)` classifies its Tate scaling, and
  \(s=\tfrac12\) is the unique weight-one normalization.
- **New insight:** retain the arithmetic relation in an \(L^1\) or
  residue-graph topology and use \(L^2\) only for polarization energy.
  Non-scalar middle spectrum must survive in the Rost--Schmid
  coherence-defect quotient, not in the completed local Kummer line.
- **Status:** source density imported from Allcock--Vaaler; field
  independence, positivity, scaling, and the dense-kernel no-go are
  paper-proved.  Abstract scaling and dense-kernel consequences are
  written in
  `RHTower/Deninger/DeningerArithmeticAdelicKummerNoGo.lean`; direct check is
  deferred while unrelated Lean builds saturate the workspace.

## References

- Daniel Allcock and Jeffrey D. Vaaler, *A Banach space determined by
  the Weil height*: https://arxiv.org/abs/0808.1038
- Paul Fili and Zachary Miner, *Orthogonal decomposition of the space
  of algebraic numbers and Lehmer's problem*:
  https://arxiv.org/abs/0911.1975
- Christopher Deninger, *Dynamical systems for arithmetic schemes*,
  §12: https://arxiv.org/abs/1807.06400

## Log

- 2026-07-26 — Retired bare \(L^2\) completion after primary-source
  audit; extracted mixed \(L^1/L^2\) coefficient as positive survivor.
