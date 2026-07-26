# Deninger polarized-transfer half-density law

- **ID:** `deninger-polarized-transfer-half-density`
- **Stage:** 2-fully-proven
- **Type:** ABSTRACT SOURCE THEOREM / SPECIALIZATION GATE
- **Parent:** `deninger-mw-gamma-brst-complex`
- **Lean status:** pending

## Statement

Let \(H_r\) be coefficient spaces indexed by a positive modulus \(r\).  Suppose that a degree
\(n\) finite-syntomic power correspondence supplies pullback and pushforward maps
\[
 V_n:H_r\longrightarrow H_{nr},
 \qquad
 F_n:H_{nr}\longrightarrow H_r.
\]
Let \(B_r\) be Poincare pairings and \(J_r\) odd Hodge operators.  Define
\[
 g_r(x,y)=B_r(x,J_ry).
\]
Assume:

1. projection-formula adjunction
   \[
   B_{nr}(V_nx,z)=B_r(x,F_nz);                                    \tag{1}
   \]
2. Hodge naturality
   \[
   J_{nr}V_n=V_nJ_r;                                               \tag{2}
   \]
3. polarized degree law
   \[
   F_nV_n=n\,\mathrm{id}_{H_r}.                                   \tag{3}
   \]

Then
\[
 g_{nr}(V_nx,V_ny)=n\,g_r(x,y).                                  \tag{4}
\]
Consequently the half-density normalized transfer
\[
 U_n=n^{-1/2}V_n
\]
is an isometry:
\[
 g_{nr}(U_nx,U_ny)=g_r(x,y).                                     \tag{5}
\]
If \(V_mV_n=V_{mn}\), the positive square-root normalization is multiplicative and
\[
 U_mU_n=U_{mn}.                                                    \tag{6}
\]

For Milnor--Witt power transfers, `(3)` is replaced before polarized realization by
\[
 F_nV_n=n_\epsilon .
\]
Thus the exact source-realization obligation is
\[
 \operatorname{Real}^{\mathrm{pol}}_\Gamma(n_\epsilon)
   =n\,\mathrm{id}.                                                \tag{7}
\]
Equation `(7)` is a rank-collapse law inside the Gamma-polarized metric; it is not the false
claim that the bare real quadratic form \(n_\epsilon\) is positive.

## Proof

Using `(1)`, `(2)`, and `(3)`,
\[
\begin{aligned}
g_{nr}(V_nx,V_ny)
 &=B_{nr}(V_nx,J_{nr}V_ny)\\
 &=B_{nr}(V_nx,V_nJ_ry)\\
 &=B_r(x,F_nV_nJ_ry)\\
 &=B_r(x,nJ_ry)\\
 &=n\,g_r(x,y).
\end{aligned}
\]
This proves `(4)`.  Sesquilinearity and the positive real scalar \(n^{-1/2}\) give
\[
g_{nr}(U_nx,U_ny)=n^{-1}g_{nr}(V_nx,V_ny)=g_r(x,y),
\]
which is `(5)`.  Finally
\[
U_mU_n
  =m^{-1/2}n^{-1/2}V_mV_n
  =(mn)^{-1/2}V_{mn}
  =U_{mn},
\]
proving `(6)`.

## Deninger consequence

At discrete time \(t=\log n\), the unnormalized transfer decomposes as
\[
 V_n=e^{t/2}U_n.
\]
Therefore its infinitesimal generator, wherever the discrete semigroup extends to a strongly
continuous flow, has the forced form
\[
 \Theta=\frac12+A
\]
with \(A\) skew-symmetric for the Gamma-polarized metric.  This obtains Deninger's weight-one
half shift from finite-syntomic degree and Poincare adjunction, before any Xi-divisor comparison.

The theorem does not supply:

1. the Gamma-polarized realization or positivity;
2. equation `(7)`;
3. extension from the rational-time power semigroup to a closed continuous generator;
4. spectral comparison with Xi.

Those are separate construction theorems.

## Hostile audit

- Bare \(n_\epsilon\) is indefinite.  Replacing `(7)` by “\(n_\epsilon>0\)” is false.
- \(F_nV_n=n_\epsilon\) has the correct order only when \(V_n\) is pullback and \(F_n\) is
  pushforward.  Swapping them would require the generally false scalar law for \(V_nF_n\).
- Projection onto an analytic cutoff may break `(1)` and `(3)`.  Half-density normalization must
  be imposed before compression.
- Equation `(2)` must be proved from the moving Gamma/rectangular polarization.  Proving it by
  comparing with Xi zeros would assume the purity conclusion.

## Novelty audit

The projection formula and degree formula are standard.  New content is the exact extraction
showing that Deninger's half shift follows from their Gamma-polarized combination and that the
only quadratic obstruction is the explicit rank-collapse law `(7)`.

