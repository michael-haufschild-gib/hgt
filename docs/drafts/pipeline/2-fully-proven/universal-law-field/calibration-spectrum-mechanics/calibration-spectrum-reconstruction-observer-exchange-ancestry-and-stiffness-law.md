# Calibration-Spectrum Reconstruction, Observer Exchange, Ancestry, and Stiffness Law

**Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [UNCONDITIONAL] [PRE-RH]`

## 1. Finite marked setup

Let `I,X,Y,Z` be finite sets.  Let

\[
 a=(a_i(x))_{i\in I,x\in X}\in\mathbb C^{I\times X}
\]

be a marked source packet.  Let `T=(T_yx)` and `S=(S_zy)` be nonnegative real kernels.  Define

\[
 E_T(a)(y)=\sum_{i,x}T_{yx}|a_i(x)|,
 \qquad
 C_T(a)(y)=\sum_{i,x}T_{yx}a_i(x),
 \tag{CSR.1}
\]

and

\[
 D_T(a)(y)=E_T(a)(y)-|C_T(a)(y)|.
 \tag{CSR.2}
\]

For a unit complex calibrator `u`, define the challenge spectrum

\[
 R_T(a)(y,u)=E_T(a)(y)-\operatorname{Re}(\overline u C_T(a)(y)).
 \tag{CSR.3}
\]

For `c in C`, use the total phase

\[
 p(c)=\begin{cases}1,&c=0,\\c/|c|,&c\ne0,\end{cases}
 \tag{CSR.4}
\]

and the elementary residual

\[
 \rho(u,c)=|c|-\operatorname{Re}(\overline u c).
 \tag{CSR.5}
\]

## 2. Reconstruction and ground response

### Theorem 2.1 — nonnegativity, minimization, and four-point reconstruction

For every `y` and every unit `u`:

\[
 R_T(a)(y,u)\ge0.
 \tag{CSR.6}
\]

Moreover,

\[
 \boxed{\min_{|u|=1}R_T(a)(y,u)=D_T(a)(y),}
 \tag{CSR.7}
\]

with minimizer `u=p(C_T(a)(y))`.  Finally the four values at `1,-1,i,-i` reconstruct both
envelope and coherent output:

\[
 \boxed{
 E_T(a)(y)=\frac{R(1)+R(-1)}2,\quad
 \operatorname{Re}C_T(a)(y)=\frac{R(-1)-R(1)}2,\quad
 \operatorname{Im}C_T(a)(y)=\frac{R(-i)-R(i)}2.}
 \tag{CSR.8}
\]

### Proof

The triangle inequality gives `E_T(a)(y)>=|C_T(a)(y)|`.  Since

\[
 \operatorname{Re}(\overline u c)\le|\overline u c|=|c|,
\]

equation `(CSR.6)` follows.  The same inequality shows

\[
 R_T(a)(y,u)\ge E_T(a)(y)-|C_T(a)(y)|.
\]

If `c=C_T(a)(y)` is nonzero, `u=c/|c|` makes `conj(u)c=|c|`; if `c=0`, every unit calibrator
does.  This proves `(CSR.7)`.  Substitution of the four stated units into `(CSR.3)` gives

\[
 R(1)=E-\operatorname{Re}c,\quad R(-1)=E+\operatorname{Re}c,
\]

\[
 R(i)=E-\operatorname{Im}c,\quad R(-i)=E+\operatorname{Im}c,
\]

which proves `(CSR.8)`.  QED.

Thus the scalar defect is the minimum of a reconstructive spectrum, not the complete state.

## 3. Positive observation and adaptive-calibration exchange

Composition of positive kernels is

\[
 (ST)_{zx}=\sum_yS_{zy}T_{yx}.
\]

### Theorem 3.1 — exact spectral transport

For every `z` and unit `u`,

\[
 \boxed{R_{ST}(a)(z,u)=\sum_yS_{zy}R_T(a)(y,u).}
 \tag{CSR.9}
\]

### Proof

Positivity gives `E_(ST)=S E_T`; linearity gives `C_(ST)=S C_T`.  Taking real parts commutes
with multiplication by nonnegative real scalars and finite sums.  Substitute into `(CSR.3)`.
QED.

### Theorem 3.2 — minimization/observation exchange defect

For every `z`,

\[
\boxed{
 \min_{|u|=1}\sum_yS_{zy}R_T(a)(y,u)
 -\sum_yS_{zy}\min_{|u|=1}R_T(a)(y,u)
 =\sum_yS_{zy}|C_T(a)(y)|-|C_{ST}(a)(z)|.}
\tag{CSR.10}
\]

The right side is nonnegative.  It vanishes exactly when all nonzero `C_T(a)(y)` with
`S_zy>0` have one common phase.

### Proof

Apply `(CSR.7)` to the left term after `(CSR.9)` and separately to each summand:

\[
 \min_u R_{ST}(z,u)=E_{ST}(z)-|C_{ST}(z)|,
\]

while

\[
 \sum_yS_{zy}\min_uR_T(y,u)=
 \sum_yS_{zy}(E_T(y)-|C_T(y)|).
\]

The envelope terms cancel because `E_(ST)=S E_T`, giving `(CSR.10)`.  Nonnegativity and the
equality classification are the finite complex triangle inequality and its equality case.  QED.

This is a genuine operation law: observation is linear on spectra, while choosing an optimal
calibrator after observation is not.

## 4. Exact source ancestry

### Theorem 4.1 — one-stage source-residual disintegration

For every `y`,

\[
\boxed{
 D_T(a)(y)=\sum_{i,x}T_{yx}\rho\bigl(p(C_T(a)(y)),a_i(x)\bigr).}
\tag{CSR.11}
\]

Every summand is nonnegative.

### Proof

Let `u=p(C_T(a)(y))`.  Then `Re(conj(u)C_T(a)(y))=|C_T(a)(y)|`.  Therefore

\[
\begin{aligned}
 D_T(a)(y)
 &=\sum_{i,x}T_{yx}|a_i(x)|
   -\operatorname{Re}\left(\overline u\sum_{i,x}T_{yx}a_i(x)\right)\\
 &=\sum_{i,x}T_{yx}
   \left(|a_i(x)|-\operatorname{Re}(\overline u a_i(x))\right).
\end{aligned}
\]

Each residual is nonnegative because `Re(conj(u)c)<=|c|`.  QED.

### Theorem 4.2 — serial ancestry conservation

For every `z`,

\[
\boxed{
 D_{ST}(a)(z)
 =\sum_yS_{zy}D_T(a)(y)
 +\sum_yS_{zy}\rho\bigl(p(C_{ST}(a)(z)),C_T(a)(y)\bigr).}
\tag{CSR.12}
\]

The first term is inherited source residual.  The second is observer-created phase frustration.
Both are nonnegative.

### Proof

Put `u=p(C_(ST)(a)(z))`.  Add and subtract `sum_y S_zy |C_T(a)(y)|`:

\[
\begin{aligned}
 D_{ST}(a)(z)
 &=\sum_yS_{zy}E_T(a)(y)-|C_{ST}(a)(z)|\\
 &=\sum_yS_{zy}(E_T(a)(y)-|C_T(a)(y)|)\\
 &\quad+\sum_yS_{zy}
 \left(|C_T(a)(y)|-\operatorname{Re}(\overline u C_T(a)(y))\right).
\end{aligned}
\]

The equality `Re(conj(u)C_(ST))=|C_(ST)|` closes the calculation.  QED.

Equation `(CSR.12)` is stronger than a scalar chain rule: it identifies the marked ancestry of
every unit of defect.

## 5. Generation and response prediction

Suppose a refinement changes an envelope from `e` to `e+h`, with `h>=0`, while preserving the
coherent output `c`.

### Theorem 5.1 — phase-neutral generation

\[
 \boxed{R_{e+h,c}(u)=R_{e,c}(u)+h}
 \tag{CSR.13}
\]

for every unit calibrator `u`.

### Proof

Immediate from the definition `(CSR.3)`.  QED.

This recovers the exact refinement increment of Marked Variation Dynamics as a vertical
translation of the entire response spectrum, not merely a change of its minimum.

Now write `u=e^(i theta)` and

\[
 r_{e,c}(\theta)=e-\operatorname{Re}(e^{-i\theta}c).
 \tag{CSR.14}
\]

### Theorem 5.2 — fourth-organ stiffness conservation

If `c ne 0` and `theta_c=arg(c)`, then

\[
 r'_{e,c}(\theta_c)=0,
 \qquad
 r''_{e,c}(\theta_c)=|c|.
 \tag{CSR.15}
\]

Consequently, for every observer row `z`,

\[
\boxed{
 \sum_yS_{zy}\,r''_{E_T(y),C_T(y)}(\theta_y)
 -r''_{E_{ST}(z),C_{ST}(z)}(\theta_z)
 =\sum_yS_{zy}|C_T(y)|-|C_{ST}(z)|,}
\tag{CSR.16}
\]

where zero coherent values contribute zero stiffness.  Thus the observer exchange defect predicted
in `(CSR.10)` is exactly lost response stiffness.

### Proof

Write `c=|c|e^(i theta_c)`.  Then

\[
 r_{e,c}(\theta)=e-|c|\cos(\theta-\theta_c).
\]

Differentiate twice and evaluate at `theta_c` to obtain `(CSR.15)`.  Substitute the resulting
stiffness `|c|` into the two sides of `(CSR.16)`.  QED.

This is the promised fourth-organ prediction: an infinitesimal response measurement recovers the
same conserved defect as the finite observer/calibration exchange.

## 6. Joint reconstruction statement

The following data determine one another pointwise:

1. `(E_T(a)(y),C_T(a)(y))`;
2. the full calibration spectrum `u mapsto R_T(a)(y,u)`;
3. the four values at `1,-1,i,-i`.

From any of them one obtains the ground response, minimizing phase, and nonzero response stiffness.
Across a positive observer, the full spectrum transports linearly and its ground response obeys
the exact conservation law `(CSR.12)`.  This is a joint reconstruction/conservation theorem across
generation, positive capacity, coherent phase, observation, and response.

## 7. Hostile scope

1. The pointwise spectrum is equivalent to `(e,c)`; significance lies in the exchange, ancestry,
   and generation laws, not terminology.
2. Positivity of observer weights is load-bearing.  Signed weights destroy the envelope transport
   and nonnegative ancestry.
3. Marked source entries are load-bearing for `(CSR.11)`; the aggregate pair `(e,c)` cannot recover
   which source entries created the defect.
4. Four calibrators are sufficient over `C`; two recover only the real part.  No claim of minimality
   is needed for the theorem.
5. The stiffness formula is local and finite.  It supplies no Hamiltonian time evolution.
6. No source-normal global calibration section, cofinal admission theorem, RH selector, or zero
   statement is constructed.
7. This theorem predicts the type of missing RH mechanism: a pre-zero source law must generate a
   coherent calibration section and preserve its residual ancestry through all relevant observer
   exits.  That existence statement remains open.

## 8. Internal parents and formalization target

Internal parents:

- Coherent History Mechanics: positive envelope and coherent phase;
- Marked Variation Dynamics: scalar defect, observer chain rule, and refinement increment;
- endogenous challenge transduction: challenge must be source-produced;
- positive observer descent: positivity/admission boundary.

Lean target: finite reconstruction, nonnegativity, spectral transport, exchange identity, one-stage
ancestry, and serial ancestry.  The analytic stiffness statement may be formalized separately from
the finite algebraic core.
