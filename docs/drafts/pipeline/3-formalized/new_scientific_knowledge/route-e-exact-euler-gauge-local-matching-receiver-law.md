# Route E exact Euler-gauge and local matching receiver law

- **ID:** `ROUTE-E-EXACT-EULER-GAUGE-LOCAL-RECEIVER-001`
- **Stage:** 3-formalized
- **Type:** `[PAPER-PROVED] [EXACT SOURCE LAW] [SHARP PHYSICAL RECEIVER]`
- **Parent:** `route-e-source-faithful-euler-tilt-unit-shell-law.md`
- **Source:** `OPEN-SOURCE-001`
- **RH used:** no
- **Computation used:** no
- **Lean status:** complete in
  `GaloisForLFunctions.RHTower.RouteESourceFaithfulEulerTiltUnitShell`; umbrella-reachable,
  direct Lean and targeted build green, standard axioms only
- **Scientific status:** `[BRIDGE]`; project-local source/receiver synthesis, no global novelty claim

## 1. Exact theorem

Let (P) be a finite prime set. For (T\subseteq P), put

\[
 m_T=\prod_{p\in T}p,
 \qquad E_T=\log m_T,
 \qquad
 \mathcal P_{\sigma,P}=\prod_{p\in P}(1+p^{-\sigma}),
\]

and let

\[
 \nu_{\sigma,P}(T)=\frac{m_T^{-\sigma}}{\mathcal P_{\sigma,P}},
 \qquad
 W_{\sigma,x}(T)=\exp(\sigma E_T-xe^{E_T}).
\]

For every real observable (F) on subsets of (P), every real (sigma,x),

\[
 \boxed{
 \mathcal P_{\sigma,P}
 \sum_{T\subseteq P}\nu_{\sigma,P}(T)W_{\sigma,x}(T)F(T)
 =\sum_{T\subseteq P}e^{-xm_T}F(T).}
 \tag{1}
\]

Both denominators are positive, so normalization gives

\[
 \boxed{
 \frac{\sum_T\nu_{\sigma,P}(T)W_{\sigma,x}(T)F(T)}
      {\sum_T\nu_{\sigma,P}(T)W_{\sigma,x}(T)}
 =
 \frac{\sum_Te^{-xm_T}F(T)}{\sum_Te^{-xm_T}}.}
 \tag{2}
\]

Thus the Euler parameter is an exact gauge for every predeclared normalized observable. It can
locate the source mass but cannot create a transfer error or improve the literal Gibbs current.

Now let (I) be finite. Fix (X>0), (H\ge0), paired physical atoms
((m_i,n_i)_{i\in I}) satisfying

\[
 |m_i-n_i|\le H,
\]

and unmatched positive and negative masses (r_+,r_-\ge0). Define

\[
 \begin{aligned}
 Z_{\rm mat}&=\sum_{i\in I}(e^{-m_i/X}+e^{-n_i/X}),\\
 R&=r_++r_-,\qquad Z=Z_{\rm mat}+R>0,\\
 J&=\sum_{i\in I}(e^{-m_i/X}-e^{-n_i/X})+r_+-r_-,\\
 u&=R/Z.
 \end{aligned}
 \tag{3}
\]

Then each pair obeys the exact polarization law

\[
 \boxed{
 \frac{|e^{-m/X}-e^{-n/X}|}{e^{-m/X}+e^{-n/X}}
 =\tanh\!\left(\frac{|m-n|}{2X}\right),}
 \tag{4}
\]

and the full matching obeys

\[
 \boxed{
 \frac{|J|}{Z}
 \le u+\tanh\!\left(\frac{H}{2X}\right)
 \le u+\frac{H}{2X}.}
 \tag{5}
\]

No injectivity, arithmetic incidence, column-load, or asymptotic hypothesis is hidden in `(5)`.
Those conditions belong to the producer of the matching, not this receiver.

## 2. Paper proof

The occupied-subset probability is

\[
 \nu_{\sigma,P}(T)=m_T^{-\sigma}/\mathcal P_{\sigma,P}.
\]

Since (e^{E_T}=m_T), atomwise cancellation gives

\[
 \mathcal P_{\sigma,P}\nu_{\sigma,P}(T)W_{\sigma,x}(T)
 =m_T^{-\sigma}m_T^\sigma e^{-xm_T}=e^{-xm_T}.
\]

Multiplication by arbitrary (F(T)) and finite summation proves `(1)`. Taking (F=1) proves the
denominator identity. Every Gibbs atom is positive, so its finite sum is positive; division proves
`(2)`.

For `(4)`, assume (m\le n); the other order follows by symmetry. Put

\[
 c=e^{-(m+n)/(2X)},\qquad d=(n-m)/(2X)\ge0.
\]

Then (e^{-m/X}=ce^d), (e^{-n/X}=ce^{-d}), and hence

\[
 \frac{e^{-m/X}-e^{-n/X}}{e^{-m/X}+e^{-n/X}}
 =\frac{e^d-e^{-d}}{e^d+e^{-d}}=\tanh d.
\]

Let (	au=\tanh(H/(2X))\ge0). Monotonicity of (	anh) and `(4)` give

\[
 |e^{-m_i/X}-e^{-n_i/X}|
 \le\tau(e^{-m_i/X}+e^{-n_i/X}).
\]

Summing and applying the triangle inequality to the unmatched signed mass gives

\[
 |J|\le \tau Z_{\rm mat}+R.
\]

Because (Z_{\rm mat}/Z\le1), division by (Z>0) yields the first inequality in `(5)`.
Finally (	anh y\le y) for (y\ge0), proving the second.

## 3. Anti-theatre audit and frontier consequence

`(1)`--`(2)` do not estimate the Gibbs current; they prove that changing (sigma) cannot do so.
`(5)` does not construct a matching; it states the exact rate any physical matching must deliver.
Consequently the remaining Route E producer is unchanged and sharper:

\[
 u_X\le X^{-1/2+o(1)},
 \qquad H_X\le X^{1/2+o(1)},
\]

for one source-predeclared opposite-parity flow which also has unit physical column load, preserves
the zero/one-large-prime seam, and is compatible with prime-dilation recurrence. The Euler gauge,
finite conditional-mean comparison, and local Gibbs receiver are no longer open proof burdens.

## 4. Gates

- [x] 0 → 1 in-progress: exact source-pure theorem and receiver identified
- [x] 1 → 2 fully-proven: atomwise cancellation and aggregate polarization proof are complete
- [x] 2 → 3 formalized: exact theorem is umbrella-reachable; direct Lean and targeted build pass;
      `#print axioms` reports only `propext`, `Classical.choice`, `Quot.sound`; repository lint has
      unrelated pre-existing umbrella reachability debt and no violation in this module
- [ ] 3 → 4 publication-ready: standalone priority audit and exposition pending

## 5. Log

- 2026-08-11 — extracted exact paper-only Section 9 claims from parent card and completed Lean proof
