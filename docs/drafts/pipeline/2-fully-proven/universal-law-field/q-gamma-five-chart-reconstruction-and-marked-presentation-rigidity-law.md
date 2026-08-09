# q-Gamma five-chart reconstruction and marked presentation-rigidity law

- **ID:** ULF-QG5R-1
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / PRESENTATION-INVARIANCE CALIBRATION
- **Source:** doctrine-change gate for Constitutive Process Mathematics
- **Statement:** Within the Jackson \(q\)-Gamma family, parameter, atomic probability law, characteristic process, minimal cyclic GNS realization, and analytic response germ determine one another; equal observed process responses force marked unitary equivalence and identical withheld tilt laws.
- **Status:** [PAPER-PROVED] [FIVE CHARTS] [EXACT RECONSTRUCTION] [MARKED PRESENTATION RIGIDITY] [WITHHELD RESPONSE INVARIANT] [CLASSICAL FOURIER/GNS/MOMENT PARENTS] [NOT RH] [NO LEAN]

## 1. Five charts

For \(0<q<1\), retain the data from ULF-QGPRH-1:

\[
w_n(q)=(q;q)_\infty\frac{q^n}{(q;q)_n},
\qquad
x_n(q)=n\log q-\log(1-q),
\tag{1}
\]

\[
\mu_q=\sum_{n\ge0}w_n(q)\delta_{x_n(q)},
\qquad
C_q(t)=\int e^{itx}\,d\mu_q(x),
\tag{2}
\]

\[
F_q(s)=\Gamma_q(1+s)=\int e^{sx}\,d\mu_q(x)
\qquad(\operatorname{Re}s>-1),
\tag{3}
\]

and the minimal cyclic spectral realization

\[
\mathcal G_q=(\mathcal H_q,U^q,\Omega_q),
\qquad
C_q(t)=\langle\Omega_q,U_t^q\Omega_q\rangle.
\tag{4}
\]

The five presentations are:

1. parameter \(q\);
2. probability law \(\mu_q\);
3. characteristic process \(C_q\);
4. marked minimal GNS triple \(\mathcal G_q\);
5. analytic germ \([F_q]_0\).

## 2. Reconstruction theorem

### Theorem 2.1

Every one of the five presentations determines the other four. More precisely:

1. \(q\) gives (1)--(4) explicitly;
2. \(\mu_q\) recovers \(q\) from the unique maximal support point
   \[
   \max\operatorname{supp}\mu_q=x_0(q)=-\log(1-q);
   \tag{5}
   \]
3. \(C_q\) uniquely determines \(\mu_q\) by Fourier uniqueness;
4. \(\mathcal G_q\) determines \(C_q\) by its cyclic matrix coefficient;
5. the germ \([F_q]_0\) uniquely determines \(\mu_q\), because it is a moment-generating function
   finite on a neighborhood of \(0\).

Consequently all five recover

\[
\boxed{q=1-\exp(-x_0).}
\tag{6}
\]

### Proof

Only the reverse reconstructions require proof.

The support points satisfy

\[
x_{n+1}(q)-x_n(q)=\log q<0,
\]

so \(x_0(q)\) is the unique maximal point. Equation (6) follows from (5).

The uniqueness theorem for characteristic functions reconstructs a finite Borel measure from
\(C_q\). The marked GNS triple gives \(C_q\) directly by (4).

Finally, \(F_q\) is finite on the open half-plane \(\operatorname{Re}s>-1\), so in particular on
a real neighborhood of \(0\). Equality of two such germs gives equality of all moments and of the
moment-generating functions on a neighborhood of \(0\); the standard uniqueness theorem for
moment-generating functions gives equality of their probability laws. Equivalently, exponential
integrability makes the Hamburger moment problem determinate. QED.

## 3. Marked GNS presentation rigidity

Two marked cyclic unitary presentations

\[
(\mathcal H,U,\Omega),
\qquad
(\mathcal H',U',\Omega')
\tag{7}
\]

are **process equivalent** when

\[
\langle\Omega,U_t\Omega\rangle
=\langle\Omega',U'_t\Omega'\rangle
\qquad(t\in\mathbb R)
\tag{8}
\]

and the cyclic spans of \(\Omega,\Omega'\) are dense.

### Theorem 3.1

If (8) holds, there is a unique unitary

\[
V:\mathcal H\longrightarrow\mathcal H'
\tag{9}
\]

such that

\[
V\Omega=\Omega',
\qquad
VU_t=U'_tV
\qquad(t\in\mathbb R).
\tag{10}
\]

Hence two minimal GNS presentations of \(C_q\) are not merely analogous: they are uniquely
equivalent as marked process realizations.

### Proof

On the algebraic cyclic span define

\[
V_0\left(\sum_jc_jU_{t_j}\Omega\right)
=\sum_jc_jU'_{t_j}\Omega'.
\tag{11}
\]

All inner products between such vectors are determined by the common function in (8):

\[
\left\langle U_s\Omega,U_t\Omega\right\rangle=C(t-s).
\]

Thus \(V_0\) is well-defined and isometric. Cyclicity makes its domain and range dense, so it
extends to a unitary \(V\). Equations (10) hold on a dense spanning set and hence everywhere.
Uniqueness follows from the same cyclicity. QED.

## 4. Full five-chart rigidity

### Corollary 4.1

For \(q,q'\in(0,1)\), the following are equivalent:

\[
\boxed{
q=q'
\Longleftrightarrow
\mu_q=\mu_{q'}
\Longleftrightarrow
C_q=C_{q'}
\Longleftrightarrow
\mathcal G_q\simeq\mathcal G_{q'}
\Longleftrightarrow
[F_q]_0=[F_{q'}]_0.}
\tag{12}
\]

Here \(\simeq\) means the unique marked unitary equivalence of Theorem 3.1.

### Proof

Forward implications are explicit. Every reverse implication reconstructs \(\mu_q\), then \(x_0\),
then \(q\) by Theorem 2.1. QED.

This is the first concrete presentation-invariance theorem for the CPM field programme.

## 5. Invariance of memory and withheld interventions

Once any chart reconstructs \(q\), it reconstructs:

- every atom \(x_n(q)\) and weight \(w_n(q)\);
- the positive moment matrices;
- the compact-resolvent generator \(X_q\);
- the recurrent orbit and marked open lift;
- the full hypertranscendental germ \(F_q\);
- the exponential tilt
  \[
  \widetilde w_n=e^{x_n}w_n;
  \tag{13}
  \]
- its characteristic response and information costs
  \[
  \widetilde C_q(t)
  =\frac{1-q^{1+it}}{1-q}C_q(t),
  \tag{14}
  \]
  \[
  D(\widetilde w\|w)=F_q'(1),
  \qquad
  D(w\|\widetilde w)=-F_q'(0).
  \tag{15}
  \]

### Corollary 5.1

Every quantity above is invariant under marked process equivalence. In particular, the withheld
tilt response (14) is independent of whether the source was presented as a probability law,
positive kernel, cyclic operator system, analytic germ, or \(q\)-parameter.

This is stronger than chartwise agreement after fitting: a single observed complete response
\(C_q\) reconstructs the parameter and forces all other charts.

## 6. Doctrine atlas interpretation

Let \(\mathsf{Pres}_q\) be the groupoid with the five presentations as objects and the reconstruction
equivalences above as arrows. The response functor

\[
\mathcal R:\mathsf{Pres}_q\longrightarrow\mathsf{Proc},
\tag{16}
\]

sending each chart to the common characteristic process, is conservative on this groupoid:
an arrow is an equivalence exactly when it preserves the complete response.

This gives the smallest exact CPM doctrine atlas:

- probability and positive-kernel presentations are related by Fourier/Bochner reconstruction;
- positive-kernel and operator presentations are related by minimal GNS reconstruction;
- probability and analytic presentations are related by Mellin/moment-generating reconstruction;
- the \(q\)-difference law acts as a represented intervention on the reconstructed process.

No claim is made that an arbitrary doctrine equivalence preserves every chosen notion of memory.
The marking by the complete response and cyclic source vector is load-bearing.

## 7. Hostile boundaries

1. Minimality/cyclicity is required. One can add an arbitrary orthogonal spectator representation
   without changing \(C_q\).
2. The complete characteristic function is required. Finite samples or finitely many moments do
   not reconstruct an infinite atomic law.
3. The analytic germ must be known exactly, not through a finite jet.
4. The result proves marked presentation invariance inside one family, not a general Morita theorem
   for all process doctrines.
5. The tilt law is not determined by a bare positive-definite function outside the reconstructed
   \(q\)-Gamma family.
6. No higher-slot causal process, physical clock/cost, RH statement, or arithmetic zero consequence
   is obtained.

## Classical parents

- uniqueness of characteristic functions and moment-generating functions;
- Bochner/GNS reconstruction and uniqueness of minimal cyclic representations;
- determinate moment problems under exponential integrability;
- Jackson's \(q\)-Gamma and Pastro's \(q\)-Hölder theorem.

## Log

- 2026-08-09 — all five \(q\)-Gamma charts proved mutually reconstructive; minimal GNS
  equivalence and invariance of the entropy-tilt prediction closed the first marked
  presentation-rigidity gate.
