# Monotone-source Gram contraction: exact obstruction and scale boundary

- **ID:** MONOTONE-SOURCE-GRAM-CONTRACTION
- **Stage:** 5-failed — general monotonicity mechanism only
- **Type:** FALSIFIED, with exact positive classification
- **Scope:** Even probability densities decreasing on the positive half-line do not always satisfy `B <= D`. The actual theta-source inequality and RH remain open.
- **Lean:** `formal/GaloisForLFunctions/RHTower/MonotoneSourceGramContraction.lean`, namespace `RHTower.MonotoneSourceGram`.

## Frozen claim and exact falsifier

For normalized even source moments `m_k`, put

\[
D_{ij}=\frac{m_{i+j+1}}{(2i+1)!(2j+1)!},\qquad
B_{ij}=2\sum_{k=0}^{\min(i,j)}
 \frac{(i+j+1-2k)m_{i+j+1-k}m_k}{(2i+2j+2-2k)!(2k)!}.
\]

These are the raw odd Gram coefficients and sign-adjusted coefficients of the cleared logarithmic moment kernel used in the theta source route. The conjectured representation was `0 <= B <= D` for every decreasing even probability density. Its upper inequality already fails.

Let `U_r` be the uniform probability law on `[-r,r]`. Its moments are
`u_k(r)=r^(2k)/(2k+1)`, by direct integration. Use the density of
`(U_1+U_4)/2`, so `m_k=(1+4^(2k))/(2(2k+1))`. It is even, nonnegative,
normalized, and decreasing on `[0,infinity)`.

Restrict `D-B` to indices `{1,2}`. Its entries are

\[
\begin{pmatrix}
85/32 & 65/32\\
65/32 & 49691/32256
\end{pmatrix}.
\]

The vector `(-13,17)` has value `-119221/32256 < 0`.
This exact rational identity, the density properties, and the integral-to-moment identification are proved in Lean. The witness is a symbolic proof, with no numerical experiment or approximation premise.

## Strongest positive survivor: exact two-scale compression classification

For `0<t<1`, positive distinct radii `a,b`, write `A=a^2`, `B=b^2`,
`c=t(1-t)`, and `m=t*u(a)+(1-t)*u(b)`. The compressed difference is

\[
c(A-B)^2
\begin{pmatrix}
(A+B)/360 & (A^2+AB+B^2)/7560\\
(A^2+AB+B^2)/7560 &
(A+B)(11A^2+6AB+11B^2)/1814400
\end{pmatrix}.
\]

Its determinant is

\[
\frac{c^2(A-B)^4}{4572288000}
\left[-3A^4+36A^3B-2A^2B^2+36AB^3-3B^4\right].
\]

The first diagonal entry is positive. Completing the square therefore proves that this compression is positive semidefinite **if and only if**

\[
3(A^2+B^2)^2\le36AB(A^2+B^2)+4A^2B^2.
\]

All formulas follow by substituting the integrated uniform moments into the coefficient definition and collecting powers. Lean checks the polynomial identities and both directions of the sign classification. The theorem permits any real radii with different squares; positive radii give the probability interpretation.

**New insight:** the obstruction is scale spread; its exact sign is independent of the nontrivial mixing weight. Small positive weight on the second scale cannot repair a failing compression. This is a sharp classification of this two-dimensional compression only, with no assertion about the remaining matrix entries.

## What does this mean for the whole route?

Monotonicity of the actual theta density cannot by itself justify the proposed contraction. A theta-specific proof must use additional information. The failure of the upper inequality `B <= D` neither disproves positivity of `B` nor supplies a zeta zero. Other Gram representations, and the actual theta contraction itself, remain undecided.

This does not retire the all-degree Hankel route. It removes one general mechanism that might otherwise be mistaken for its source producer. The precise open target remains the sign of the full arithmetic source form on every polynomial.

## Audit

- Paper proof: dependency-closed coefficient identities, integrated uniform moments, and completion of the square.
- Scratch: complete file passed `lake env lean /tmp/rh_uniform_gram.lean` without warnings.
- Main unconditional theorem: `exists_monotone_density_gap_negative`.
- Exact survivor: `form_nonneg_iff_radius_boundary`.
- Source check and named leaf build passed without warnings; module is imported by `RHTower.lean`. No full or umbrella build was run.
- All 21 theorem axiom audits returned only `propext`, `Classical.choice`, and `Quot.sound`. Main existential theorem has no premises; no computation axiom or proof placeholder.
- Corpus indexes regenerated. `scripts/formal_tools.py lint --check-generated` passed, with existing large-file warnings elsewhere in the corpus.
- Corpus search: hybrid/deep and direct text inspection found the prior actual-theta Gram comparison and raw-moment growth obstruction, but no duplicate of this scale classification. No external novelty claim is made.
