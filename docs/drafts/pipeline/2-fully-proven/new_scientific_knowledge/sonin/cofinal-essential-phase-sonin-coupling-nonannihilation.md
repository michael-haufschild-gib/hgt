# Cofinal essential-phase Sonin coupling nonannihilation

- **ID:** `cofinal-essential-phase-sonin-coupling-nonannihilation`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / SOURCE-TEST BOUNDARY CONSTRUCTION
- **Scientific status:** `[PROVED HERE] [CORPUS-NEW] [EXTERNAL NOVELTY PROVISIONAL] [NOT RH]`
- **Parents:** `sonin-principal-shell-cyclic-trace.md`,
  `SoninCouplingBranchEstimate.lean`, `SoninProjectionCorrection.lean`
- **Statement:** Every strict Sonin aperture shell has a cofinal family of normalized,
  Poisson-admissible, essential-phase wavepackets on which the successive-layer coupling tends
  isometrically to the inverse-dilated packet. In particular, the coupling is nonzero for every
  sufficiently large dilation scale.

## Goal

Settle the open nonannihilation horn left by Theorem Q of
`sonin-principal-shell-cyclic-trace.md`. The result constructs an actual source-test mode at the
cofinal phase-space boundary. It does **not** yet land a Xi conormal and therefore is not the
missing RH theorem.

## Setup

Work in the even subspace of \(L^2(\mathbb R)\), with Fourier convention
\[
\widehat f(\xi)=\int_{\mathbb R}f(x)e^{-2\pi i x\xi}\,dx.
\]
Let
\[
A_s=1_{\{|x|\le s\}},\qquad R_s=\mathcal F^{-1}A_s\mathcal F,\qquad
Q_s=\text{the orthogonal projection onto }K_s=\ker A_s\cap\ker R_s.
\]
Write
\[
C_s=Q_s-(1-A_s-R_s),\qquad L_{a,b}=Q_a-Q_b.
\]
The corpus proves that \(C_s\) is Schatten--\(1\), hence compact, and that \(L_{a,b}\) is an
orthogonal projection when \(a\le b\). For \(r>1\), put
\[
D_r=U_r+U_{1/r},\qquad (U_r f)(x)=r^{1/2}f(rx),
\]
and define the successive-layer coupling
\[
Z_r=L_{a,b}D_rL_{b,c}.
\]

Fix
\[
0<a<q<b<c.
\]
Choose a nonzero real, even, nonnegative
\(\phi\in C_c^\infty(\{x:b<|x|<c\})\). For \(r>1\), define
\[
\mu_r=
\frac{\int_{\mathbb R}\phi(x)\cos(2\pi r qx)\,dx}
     {\int_{\mathbb R}\phi(x)\,dx},
\qquad
u_r(x)=\phi(x)\bigl(\cos(2\pi r qx)-\mu_r\bigr),
\qquad
w_r=\frac{u_r}{\|u_r\|_2}.
\tag{1}
\]

Each \(u_r\) is an even compactly supported smooth function satisfying
\[
u_r(0)=0,\qquad \widehat u_r(0)=\int_{\mathbb R}u_r=0.
\tag{2}
\]
Thus \(u_r\) is an exact Meyer Poisson-source test, not merely an \(L^2\) witness.

## Theorem

For the family `(1)`, as \(r\to+\infty\),
\[
\left\|Z_r w_r-U_{1/r}w_r\right\|_2\longrightarrow0.
\tag{3}
\]
Consequently
\[
\|Z_r w_r\|_2\longrightarrow1,\qquad
\liminf_{r\to\infty}\|Z_r\|\ge1,
\tag{4}
\]
and \(Z_r\ne0\) for every sufficiently large \(r\). In particular, every fixed strict flag
\(0<a<b<c\) lies in the strict-curvature chamber for all sufficiently large dilation scales:
\[
\operatorname{Re}\operatorname{Tr}\kappa(a,b,c;r)
=-\|Z_r\|_{\mathrm{HS}}^2<0.
\tag{5}
\]

The conclusions remain true along the integer clock \(r=N\to\infty\), along every prime-power
clock \(r=p^k\to\infty\), and along every other cofinal subnet.

## Proof

### 1. Normalization and weak escape

Riemann--Lebesgue gives \(\mu_r\to0\). Also,
\[
\|\phi\cos(2\pi r q\,\cdot)\|_2^2
=\frac12\|\phi\|_2^2+
  \frac12\int_{\mathbb R}|\phi(x)|^2\cos(4\pi r qx)\,dx
\longrightarrow\frac12\|\phi\|_2^2.
\]
Therefore
\[
\|u_r\|_2\longrightarrow2^{-1/2}\|\phi\|_2>0.
\tag{6}
\]
For every \(g\in L^2(\mathbb R)\), the product \(\phi\overline g\) is in \(L^1\), so another
application of Riemann--Lebesgue, `(6)`, and \(\mu_r\to0\) gives
\[
w_r\rightharpoonup0.
\tag{7}
\]
Compactness of \(C_b\) now gives
\[
\|C_bw_r\|_2\longrightarrow0.
\tag{8}
\]

### 2. The original packet leaves the central Fourier band

The modulation identity gives
\[
\widehat{\phi\cos(2\pi r q\,\cdot)}(\xi)
=\frac12\bigl(\widehat\phi(\xi-rq)+\widehat\phi(\xi+rq)\bigr).
\tag{9}
\]
Translations of an \(L^2\) function have vanishing mass in any fixed bounded interval when the
translation tends to infinity. The correction \(\mu_r\widehat\phi\) tends to zero in \(L^2\).
Hence
\[
\|R_bw_r\|_2\longrightarrow0.
\tag{10}
\]

### 3. Inverse dilation converts essential phase into shell frequency

Put
\[
v_r=U_{1/r}w_r.
\]
Its physical support is contained in
\(\{x:rb<|x|<rc\}\), so
\[
A_av_r=A_bv_r=0.
\tag{11}
\]
Fourier conjugates \(U_{1/r}\) to \(U_r\). Applying \(U_r\) to `(9)` produces two packets centred
at \(\xi=\pm q\), each with width \(O(r^{-1})\):
\[
\mathcal Fv_r(\xi)
=\frac{\sqrt r}{2\|u_r\|_2}
 \bigl(\widehat\phi(r(\xi-q))+\widehat\phi(r(\xi+q))\bigr)+o_{L^2}(1).
\tag{12}
\]
Because \(a<q<b\), \(L^2\)-tail exhaustion in `(12)` yields
\[
\|R_bv_r-v_r\|_2\longrightarrow0,\qquad
\|R_av_r\|_2\longrightarrow0.
\tag{13}
\]

The supports of \(v_r\) escape every bounded set while \(\|v_r\|_2=1\); hence
\[
v_r\rightharpoonup0.
\tag{14}
\]
Compactness of \(C_a\) and \(C_b\) gives
\[
\|(C_a-C_b)v_r\|_2\longrightarrow0.
\tag{15}
\]
Using
\[
L_{a,b}=(A_b-A_a)+(R_b-R_a)+(C_a-C_b)
\]
with `(11)`, `(13)`, and `(15)`, we obtain
\[
\|L_{a,b}v_r-v_r\|_2\longrightarrow0.
\tag{16}
\]

### 4. The opposite branch and exact correction vanish

The corpus's two-branch estimate applies because
\[
A_bw_r=0,\qquad A_cw_r=w_r,
\]
and, eventually, \(c<ra\):
\[
\left\|Z_rw_r-
\left(L_{a,b}U_{1/r}w_r-L_{a,b}U_rR_bw_r\right)\right\|_2
\le2\|C_bw_r\|_2.
\tag{17}
\]
Since \(L_{a,b}\) is a contraction and \(U_r\) is unitary, `(10)` gives
\[
\|L_{a,b}U_rR_bw_r\|_2\le\|R_bw_r\|_2\longrightarrow0.
\tag{18}
\]
Equations `(8)`, `(16)`, `(17)`, and `(18)` prove `(3)`. Unitarity gives
\(\|U_{1/r}w_r\|_2=1\), so `(4)` follows. The curvature identity already proved in the corpus gives
`(5)`.

No zero, divisor point, numerical experiment, unproved positivity, or RH premise occurs.

## Boundary interpretation

Let
\[
\mathcal H_\infty=
\ell^\infty((1,\infty),L^2_{\mathrm{even}}(\mathbb R))/
\{f_r:\|f_r\|_2\to0\}.
\tag{19}
\]
This is a Hausdorff Banach corona. Pullback \(r\mapsto pr\) by every prime \(p\) is isometric.
The classes
\[
[w]=[(w_r)],\qquad [v]=[(U_{1/r}w_r)]
\]
are nonzero, and `(3)` says that the cofinal coupling family has the exact nonzero boundary value
\[
[(Z_rw_r)]=[v].
\tag{20}
\]
Every fixed compact correction vanishes on these weakly escaping packets, while the Sonin coupling
survives. The phase
\[
\cos(2\pi rq x)=\cos(2\pi qx/h),\qquad h=r^{-1},
\]
is essential at \(h=0\): it is invisible to every fixed finite Rees/Taylor order. This supplies a
literal model of the corpus principle that infinite rank is insufficient and an essential
singularity is required.

Microlocally, `(20)` identifies the missing boundary face: simultaneous physical escape
\(|x|\asymp h^{-1}\) and finite nonzero rescaled frequency \(\xi\to\pm q\). A completion that keeps
only ordinary \(L^2\) weak limits loses this face; a phase-space/scattering corona retains it.
Fourier reflection acts internally on `(19)` and exchanges the two polarizations.

## Exact contribution to the RH frontier

This theorem proves three facts that were previously open in the Sonin lane:

1. successive-layer curvature is genuinely strict, not merely nonpositive;
2. exact Poisson-source tests, rather than generic Hilbert vectors, reach the strict boundary;
3. the required singularity can be exhibited concretely as a frequency-locked
   \(e^{iqx/h}\) phase at the scattering corner.

It does **not** prove:

1. that a Xi conormal maps to `[w]` or `[v]`;
2. preservation of Xi multiplicity jets;
3. that functional-equation reflection identifies two Xi conormals as one same-grade mode;
4. RH.

The remaining source theorem is therefore narrower than “find a third completion”:

> Construct, from the ordinary-integer Euler--Poisson--Gamma complex before zero specialization,
> a boundary-normal morphism into the phase-space corona `(19)` whose indicial normal operator
> sends the already-proved prime-tail Xi profiles
> \(x^{-\rho}(\log x)^j\), \(0\le j<m_\rho\), to nonzero
> essential-phase classes, intertwines prime incidence, and makes Fourier reflection an
> equality in one indicial grade rather than a swap of two grades.

Only the last clause can force \(\Re\rho=\tfrac12\). Omitting it allows an off-line reflected
doublet and is another restatement of the functional equation.

## Hostile audit

- **Could compactness force \(Z_r w_r\to0\)?** No. The operator varies with \(r\); compactness of
  each fixed \(Z_r\) says nothing about the diagonal family. Fixed compact corrections do vanish,
  and that is used in the proof.
- **Is the witness merely normalized after reading a zero?** No. \(a,q,b,c,\phi\) are chosen
  independently of Xi and before any divisor specialization.
- **Is Poisson admissibility being weakened?** No. Compact support away from zero gives
  \(u_r(0)=0\), and the scalar correction gives the exact second condition
  \(\widehat u_r(0)=\int u_r=0\).
- **Does the corona itself prove RH?** No. It retains source modes but permits distinct reflected
  indicial grades. Same-grade reflection remains the source-specific open theorem.
- **Could a finite-Rees construction reproduce the witness?** No. Its \(h\)-dependence contains
  \(e^{\pm2\pi iqx/h}\), which has no finite-order expansion at \(h=0\).

## Literature audit

Targeted searches found the following adjacent results:

- J.-F. Burnol, [*Sur les espaces de Sonine associés par de Branges à la transformation de
  Fourier*](https://www.numdam.org/item/CRMATH_2002__335_8_689_0/) gives the exact Sonine projection
  through the prolate operator and constructs Fourier-invariant/anti-invariant Sonine
  distributions.
- J.-F. Burnol, [*Two complete and minimal systems associated with the zeros of the Riemann zeta
  function*](https://arxiv.org/abs/math/0203120) connects co-Poisson source functions, extended
  Sonine spaces, and zeta evaluation vectors.
- A. Israel and A. Mayeli,
  [*On the Eigenvalue Distribution of Spatio-Spectral Limiting Operators in Higher
  Dimensions*](https://arxiv.org/abs/2301.09616) use phase-space wavepackets as approximate
  eigenvectors of time-frequency limiting operators.

These sources contain the ingredients “Sonine projection,” “co-Poisson,” and “wavepacket
localization,” but the search did not locate the specific cofinal theorem `(3)`, the strict
successive-aperture curvature consequence `(5)`, or the boundary-normal interpretation `(20)`.
External novelty remains provisional pending a broader bibliography and citation-chain audit.

## Gates

- [x] 0 → 1 in-progress: exact source-pure statement and attack identified
- [x] 1 → 2 fully-proven: complete unconditional paper proof, `[PROVED HERE]`
- [ ] 2 → 3 formalized: explicit smooth compact-annulus wavepacket and all five limit lemmas in Lean
- [ ] 3 → 4 publication-ready: standalone paper, external novelty audit, Lean certificate

## Lean plan

Do not formalize an abstract “if five limits then nonzero” wrapper; that would not certify the new
mathematics. Required dependency-closed sequence:

1. construct one even \(C_c^\infty\) bump supported in a prescribed strict annulus;
2. prove its modulated zero-integral correction is an exact Meyer test;
3. prove `(6)`--`(10)` by the available Riemann--Lebesgue theorem and Plancherel;
4. prove the scaled packet estimates `(11)`--`(15)`;
5. combine with
   `norm_evenSoninApertureSuccessiveLayerTransition_sub_branches_le`.

Final target theorem:

```text
tendsto_norm_evenSoninApertureSuccessiveLayerTransition_apply
  ... :
  Tendsto
    (fun r => ‖evenSoninApertureSuccessiveLayerTransition a b c r ... (w r)‖)
    atTop
    (𝓝 1)
```

## Log

- 2026-07-31 — Constructed the frequency-locked annular Meyer wavepacket, proved asymptotic
  isometric nonannihilation, identified the phase-space/scattering corona boundary, and isolated
  the remaining Xi indicial-grade landing theorem.
