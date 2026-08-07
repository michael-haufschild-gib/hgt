# Cofinal essential-phase Sonin coupling nonannihilation

- **ID:** `cofinal-essential-phase-sonin-coupling-nonannihilation`
- **Stage:** 3-formalized
- **Formalized companion:** `cofinal-essential-phase-sonin-coupling-nonannihilation-formalized.md`
- **Type:** THEOREM (paper) / SOURCE-TEST BOUNDARY CONSTRUCTION
- **Scientific status:** `[PROVED HERE] [CORPUS-NEW] [EXTERNAL NOVELTY PROVISIONAL] [NOT RH]`
- **Parents:** `sonin-principal-shell-cyclic-trace.md`,
  `SoninCouplingBranchEstimate.lean`, `SoninProjectionCorrection.lean`
- **Statement:** Every strict Sonin aperture shell has a cofinal family of normalized,
  Poisson-admissible, essential-phase wavepackets on which the successive-layer coupling and its
  adjoint become inverse isometries. In particular, the coupling is nonzero for every sufficiently
  large dilation scale.

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

### Adjoint theorem

For the same packets \(v_r=U_{1/r}w_r\),
\[
\left\|Z_r^*v_r-w_r\right\|_2\longrightarrow0.
\tag{4a}
\]
Consequently
\[
\|Z_r^*Z_rw_r-w_r\|_2\longrightarrow0,\qquad
\|Z_rZ_r^*v_r-v_r\|_2\longrightarrow0.
\tag{4b}
\]
Thus the cofinal boundary transition is a genuine partial unitary on the two nonzero packet
classes, and its Hilbert adjoint is its inverse there.

### Mellin-blindness theorem

Let
\[
\mathcal M w_r(s)=\int_0^\infty w_r(x)x^{-s}\,dx.
\]
For every fixed \(s\in\mathbb C\) and every \(N\ge0\),
\[
r^N\mathcal M w_r(s)\longrightarrow0.
\tag{4c}
\]
Thus this strict Sonin boundary sector is all-orders invisible to every fixed Mellin evaluation
and hence to every fixed Xi conormal. The theorem closes the Sonin sharpness question but also
proves that smooth essential-phase packets alone cannot be the source-to-Xi landing.

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

### 5. The adjoint returns the packet

Since the layers and \(D_r\) are self-adjoint,
\[
Z_r^*=L_{b,c}D_rL_{a,b}.
\tag{19a}
\]
Equation `(16)` and the uniform bound \(\|D_r\|\le2\) reduce `(4a)` to the action of
\(L_{b,c}D_r\) on \(v_r\). The two dilation branches are
\[
D_rv_r=w_r+z_r,\qquad z_r=U_{1/r^2}w_r.
\tag{19b}
\]
The original packet obeys
\[
Q_bw_r\longrightarrow w_r,\qquad Q_cw_r=0,
\]
because \(A_bw_r=0\), \(R_bw_r\to0\), \(C_bw_r\to0\), and \(A_cw_r=w_r\).
Hence
\[
L_{b,c}w_r\longrightarrow w_r.
\tag{19c}
\]

The support of \(z_r\) escapes at radius \(r^2\), so \(A_bz_r=A_cz_r=0\) and
\(z_r\rightharpoonup0\). Its Fourier packets are centred at
\(\pm q/r\), with width \(O(r^{-2})\), so
\[
R_bz_r-z_r\longrightarrow0,\qquad R_cz_r-z_r\longrightarrow0.
\]
Compactness gives \(C_bz_r,C_cz_r\to0\). Therefore
\[
L_{b,c}z_r
=(A_c-A_b)z_r+(R_c-R_b)z_r+(C_b-C_c)z_r
\longrightarrow0.
\tag{19d}
\]
Equations `(19a)`--`(19d)` prove `(4a)`.

For `(4b)`, use `(3)`, `(4a)`, and the uniform operator bounds
\(\|Z_r\|,\|Z_r^*\|\le2\):
\[
\|Z_r^*Z_rw_r-w_r\|
\le2\|Z_rw_r-v_r\|+\|Z_r^*v_r-w_r\|\to0,
\]
and similarly in the other order.

### 6. Fixed Mellin conormals cannot see the packet

On the compact support of \(\phi\), \(x^{-s}\) is smooth. Repeated integration by parts in the
oscillatory integral gives, for every \(N\),
\[
\int_0^\infty\phi(x)x^{-s}\cos(2\pi rqx)\,dx=O_{s,N}(r^{-N}).
\tag{19e}
\]
The same argument without \(x^{-s}\) gives
\(\mu_r=O_N(r^{-N})\). Equation `(6)` keeps the normalization bounded away from zero, proving
`(4c)`.

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
The adjoint theorem gives the reverse value
\[
[(Z_r^*v_r)]=[w],
\tag{21}
\]
so the boundary operator and its Hilbert adjoint are mutually inverse on these source-pointed
classes.
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
3. source inverse and Hilbert adjoint are one internal partial-unitary boundary transition on
   these packets;
4. the required singularity can be exhibited concretely as a frequency-locked
   \(e^{iqx/h}\) phase at the scattering corner.

It also proves a route closure: the strict high-frequency Sonin face and the fixed-indicial Xi
face are disjoint. A successful source boundary must use the nonsmooth/irregular ordinary-prime
sector, whose jumps survive fixed Mellin testing, rather than a smooth wavepacket completion.

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
- **Does `(21)` supply the missing Xi dagger?** No. It supplies a genuine dagger on explicit
  Poisson wavepackets. A separate source-normal theorem must identify the prime-tail Xi indicial
  germs with these classes. Declaring that identification would restate the open cross-landing.
- **Can such an identification be continuous for the ordinary Mellin topology?** Not on this
  packet sector: `(4c)` proves every fixed Mellin conormal vanishes to all Rees orders. The
  ordinary-prime jump/irregular sector must enter essentially.
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
- [x] 2 → 3 formalized: explicit smooth compact-annulus wavepacket and all five limit lemmas in Lean
- [x] the statement's own **normalized** family, not only the raw profile — `SoninNormalizedPacket.lean`
      builds `w = u/‖u‖` and its inverse dilate, proves both are unit vectors and that the raw
      packet is eventually nonzero, carries both Meyer conditions across the normalization, and
      restates `(3)`, `(4)`, `(4a)`, `(4b)`, `(4c)` for the unit family — so `‖Z_r w_r‖ → 1` is a
      theorem about the packets the card actually defines
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

## Lean progress

Formalized so far (all unconditional, `#print axioms` clean, wired into `GaloisForLFunctions.RHTower`):

| plan step | content | Lean |
|---|---|---|
| 1 | even smooth bump strictly inside the annulus `b < |x| < c` | `soninAnnulusBump` |
| 1 | evenness, nonnegativity, smoothness, strict support, value 1 at the midpoint, compact support | `soninAnnulusBump_even`, `soninAnnulusBump_nonneg`, `contDiff_soninAnnulusBump`, `soninAnnulusBump_support_subset`, `soninAnnulusBump_midpoint`, `hasCompactSupport_soninAnnulusBump` |
| 1 | positive total mass, so the mean in `(1)` is well defined | `integral_soninAnnulusBump_pos` |
| 2 | the modulated zero-mean packet `u` of `(1)`, with the frequency carried as one parameter | `soninPacketMean`, `soninPacket` |
| 2 | **first Meyer condition** `u(0) = 0` | `soninPacket_zero` |
| 2 | **second Meyer condition** `\hat u(0) = \int u = 0` | `integral_soninPacket` |
| 2 | evenness, smoothness, strict annulus support, compact support, integrability | `soninPacket_even`, `contDiff_soninPacket`, `soninPacket_support_subset`, `hasCompactSupport_soninPacket`, `integrable_soninPacket` |

| 3 | Riemann--Lebesgue for real cosine modulation, from mathlib's `Real.zero_at_infty_fourier` | `tendsto_integral_mul_cos_atTop`, `tendsto_integral_mul_cos_freq_atTop` |
| 3 | the mean correction dies, `mu -> 0` | `tendsto_soninPacketMean_atTop` |
| 3 | the oscillatory energy moments die | `tendsto_integral_soninAnnulusBump_sq_mul_cos_atTop`, `tendsto_integral_soninAnnulusBump_sq_mul_cos_two_atTop` |
| 3 | exact expansion of the packet energy | `integral_soninPacket_sq_eq` |
| 3 | **normalisation `(6)`**: the packet energy tends to half the profile energy | `tendsto_integral_soninPacket_sq_atTop` |
| 3 | the limit is positive, so the normalisation never degenerates | `integral_soninAnnulusBump_sq_pos` |

| 3 | Riemann--Lebesgue upgraded to merely *integrable* weights, real and complex | `tendsto_integral_mul_cos_atTop`, `tendsto_integral_complex_mul_cos_atTop`, `tendsto_integral_complex_mul_cos_freq_atTop` |
| 3 | **weak escape `(7)`**: every fixed weight integrable against the profile pairs to zero with the packet | `tendsto_integral_mul_soninPacket_atTop` |

| 3 | the packet as an `L²` vector, and as a vector of the **even** subspace | `soninPacketL2`, `soninPacketL2_mem_evenSubspace`, `soninPacketEven` |
| 3 | **weak escape in `L²`**: `< g , w_kappa > -> 0` for every fixed `L²` weight | `tendsto_inner_soninPacketL2_atTop` |
| 3 | uniform `L²` bound, from `|mu| <= 1` and `|u| <= 2 phi` | `abs_soninPacketMean_le_one`, `abs_soninPacket_le`, `norm_soninPacketL2_le` |

| 3 | **`(8)`**: every compact operator, and in particular the exact Sonin projection correction and every element of the relative ideal, dies along the family | `tendsto_norm_compactOperator_apply_soninPacketEven`, `tendsto_norm_evenSoninProjectionCorrection_apply_soninPacketEven`, `tendsto_norm_isSoninPrincipalRelativeIdeal_apply_soninPacketEven` |
| 4 | vanishing at infinity is uniform outside a radius — the form of Riemann--Lebesgue the frequency escape `(10)` needs | `exists_forall_norm_le_of_tendsto_cocompact` |

| 4 | the packet's Fourier transform as an explicit pairing, its pointwise vanishing, and a frequency-independent sup bound | `fourier_soninPacket_eq`, `tendsto_fourier_soninPacket_atTop`, `norm_fourier_soninPacket_le` |

| 4 | the `L²` Fourier transform of the packet is the classical Fourier integral | `fourierUnitary_soninPacketL2_coeFn` |
| 4 | the Fourier-band energy as an explicit integral | `norm_sq_evenFourierCutoff_soninPacketEven` |
| 4 | **Fourier escape `(10)`**: the packet eventually carries no energy in any fixed central Fourier band | `tendsto_norm_evenFourierCutoff_soninPacketEven` |

| 4 | the two hypotheses of the corpus two-branch estimate: `A_b w = 0` and `A_c w = w`, and their monotone forms | `evenIndicatorCutoff_soninPacketEven_eq_zero`, `evenIndicatorCutoff_soninPacketEven_eq_self`, `..._eq_zero_of_le`, `..._eq_self_of_le` |
| 4 | **`(11)`**: the inverse-dilated packet misses every aperture below `r b` and is fixed above `r c` | `evenIndicatorCutoff_evenDilationCLM_inv_soninPacketEven_eq_zero`, `evenIndicatorCutoff_evenDilationCLM_inv_soninPacketEven_eq_self` |

| 4 | `L²` tails vanish outside a growing central interval | `tendsto_norm_sub_indicatorCutoff_atTop` |
| 4 | **`(14)`**: a bounded family annihilated by physical cutoffs of growing aperture is weakly null | `tendsto_inner_of_evenIndicatorCutoff_apply_eq_zero` |

| 4 | the dilated packet `v = U_{1/r} w` as a named family, isometric to the packet | `soninDilatedPacket`, `norm_soninDilatedPacket`, `norm_soninDilatedPacket_le` |
| 4 | **`(15)`**: every compact operator, and in particular the projection correction, dies on the dilated family | `tendsto_norm_compactOperator_apply_of_evenIndicatorCutoff_apply_eq_zero`, `tendsto_norm_compactOperator_apply_soninDilatedPacket`, `tendsto_norm_evenSoninProjectionCorrection_apply_soninDilatedPacket` |

| 4 | **modulation identity** `(9)`: multiplying by `exp(2 pi i a x)` translates the transform | `fourier_exp_mul` |
| 4 | **`(12)`**: the packet's transform is the average of two translates of `phihat`, minus the mean multiple | `fourier_soninPacket_eq_shift` |

| 4 | Fourier cutoffs conjugated through a dilation: `||R_s U_{1/r} v|| = ||R_{rs} v||`, and the same for the complement | `evenFourierCutoff_evenDilationCLM_inv_apply`, `norm_evenFourierCutoff_evenDilationCLM_inv`, `norm_sub_evenFourierCutoff_evenDilationCLM_inv` |
| 4 | outer tails of an integrable energy density vanish at a growing radius | `tendsto_integral_indicator_outer_atTop` |

| 4 | shifting an energy density past a band: inside a central band, and outside a band | `integral_indicator_centralInterval_comp_add_le`, `integral_indicator_outer_comp_add_le` |

| 4 | the profile's spectral energy density `|phihat|^2`: integrable (Plancherel for the profile), nonnegative, with vanishing outer tails | `soninBumpSpectralDensity`, `integrable_soninBumpSpectralDensity`, `tendsto_integral_indicator_outer_soninBumpSpectralDensity` |

| 4 | the packet's own spectral density, and the band energy as its band integral | `soninPacketSpectralDensity`, `integrable_soninPacketSpectralDensity`, `norm_sq_evenFourierCutoff_soninPacketEven_eq_density` |
| 4 | **band energy bound**, the quantitative half of `(13)`: with carrier `a`, the energy inside the band of radius `t` is at most `3(T(|a|-t)/2 + mu^2 E)` where `T` is the profile's spectral tail and `E` its total spectral energy | `norm_sq_evenFourierCutoff_soninPacketEven_le` |

| 4 | **`(13)`, low horn**: with aperture and carrier on one clock and the aperture rate strictly smaller, the packet keeps no energy below the aperture; equivalently the *dilated* packet leaves every fixed band below the carrier ratio | `tendsto_norm_evenFourierCutoff_soninPacketEven_scaled`, `tendsto_norm_evenFourierCutoff_soninDilatedPacket` |

| 4 | the energy the packet leaves *outside* a central band, bounded by the outer band integral of its spectral density | `norm_sq_sub_evenFourierCutoff_soninPacketEven_le_outer` |
| 4 | the three-term spectral bound over an *arbitrary* measurable band, so the low and high horns share one lemma | `integral_indicator_soninPacketSpectralDensity_le` |

| 4 | **`(13)`, high horn**: the packet loses no energy above an aperture growing faster than the carrier; equivalently the dilated packet loses none above a fixed aperture | `norm_sq_sub_evenFourierCutoff_soninPacketEven_le`, `tendsto_norm_sub_evenFourierCutoff_soninPacketEven_scaled`, `tendsto_norm_sub_evenFourierCutoff_soninDilatedPacket` |

| 5 | exact splitting of the aperture layer into physical shell + Fourier shell + correction difference | `evenSoninApertureLayer_eq_shell_add_correctionDiff` |
| 5 | **`(16)`**: the aperture layer fixes the dilated wavepacket in the limit | `tendsto_norm_evenSoninApertureLayer_soninDilatedPacket_sub` |

| 5 | **`(3)`**: along any clock past the crossing threshold, the coupling carries the wavepacket to its inverse dilate | `tendsto_norm_soninApertureCoupling_soninPacketEven_sub` |

| 5 | **`(4)`**: the coupling's action on the packet family has the packet's own limiting norm, which is positive | `norm_sq_soninPacketEven`, `tendsto_norm_soninPacketEven`, `sqrt_half_energy_pos`, `tendsto_norm_soninApertureCoupling_apply_soninPacketEven` |
| 5 | **the coupling is nonzero for every large clock** | `eventually_soninApertureCoupling_ne_zero` |

| 5 | **`(5)`**: strict negativity of the successive-aperture curvature along a large clock | `eventually_re_opTrace_evenSoninApertureRestrictionCurvature_neg` |
| 5 | a concrete clock past the crossing threshold, so nothing is vacuous | `soninCrossingClock`, `one_lt_soninCrossingClock`, `lt_soninCrossingClock_mul`, `tendsto_soninCrossingClock` |
| 5 | **scale-free statements**: an actual dilation scale at which the coupling is nonzero and the curvature strictly negative | `exists_scale_soninApertureCoupling_ne_zero`, `exists_scale_re_opTrace_evenSoninApertureRestrictionCurvature_neg` |

| 6 | **`(19a)`** the adjoint coupling is the reversed product; **`(19b)`** the dilation sum on an inverse dilate; **`(19c)`** the outer layer fixes the packet in the limit | `adjoint_evenSoninApertureSuccessiveLayerTransition`, `evenDilationSum_evenDilationCLM_inv_apply`, `tendsto_norm_evenSoninApertureLayer_soninPacketEven_sub` |

| 6 | both concentration limits in **gap form**: aperture and carrier arbitrary sequences, only their difference matters | `tendsto_norm_evenFourierCutoff_soninPacketEven_gap`, `tendsto_norm_sub_evenFourierCutoff_soninPacketEven_gap` |

| 6 | **`(19d)`**: the outer aperture layer annihilates the doubly contracted packet | `tendsto_sq_mul_atTop`, `tendsto_sq_gap_atTop`, `tendsto_norm_evenSoninApertureLayer_doublyContracted` |

| 6 | **`(4a)`**: the adjoint coupling carries the dilated wavepacket back to the wavepacket | `tendsto_norm_adjoint_soninApertureCoupling_soninDilatedPacket_sub` |

| 6 | the coupling and its adjoint are contractions up to a factor two | `norm_evenSoninApertureSuccessiveLayerTransition_apply_le`, `norm_adjoint_evenSoninApertureSuccessiveLayerTransition_apply_le` |
| 6 | **`(4b)`**: the coupling and its Hilbert adjoint are mutually inverse on the two packet classes | `tendsto_norm_adjoint_mul_soninApertureCoupling_soninPacketEven_sub`, `tendsto_norm_soninApertureCoupling_adjoint_soninDilatedPacket_sub` |

| 7 | **rapid decay**: the Fourier transform of a smooth compactly supported function beats every polynomial rate — the analytic core of `(4c)` | `tendsto_pow_mul_norm_fourier_atTop` |

| 7 | the Mellin weight `phi(x) x^{-s}` on the annulus: smooth, compactly supported, and equal to the profile times `x^{-s}` on the positive axis | `soninPositiveBump`, `soninMellinWeight`, `soninMellinWeight_eq_cpow`, `contDiff_soninMellinWeight`, `hasCompactSupport_soninMellinWeight` |
| 7 | rapid decay of the Mellin-weighted oscillatory integral | `tendsto_pow_mul_norm_fourier_soninMellinWeight` |

| 7 | rapid decay in the negative direction as well | `tendsto_pow_mul_norm_fourier_neg_atTop` |
| 7 | the packet's Mellin transform, its split into an oscillatory integral plus a constant multiple, and that integral as the average of two transform values | `soninPacketMellin`, `soninPacketMellin_eq`, `integral_soninMellinWeight_mul_cos_eq` |

| 7 | the cosine-modulated integral of any continuous compactly supported weight as an average of two transform values, and its rapid decay | `integral_mul_cos_eq_fourier_avg`, `tendsto_pow_mul_norm_integral_mul_cos` |

| 7 | **`(4c)`**: every fixed Mellin exponent is blind to the wavepacket to all orders in the carrier | `tendsto_pow_mul_abs_soninPacketMean`, `tendsto_pow_mul_norm_soninPacketMellin` |

| 8 | **`(4)` in operator-norm form**: `liminf ||Z_r|| >= 1`, stated as an eventual bound below every level under one | `eventually_one_sub_le_norm_soninApertureCoupling` |
| 8 | uniform energy floor and its consequences: no lower floor for the packet channel | `eventually_le_hsNormSq_soninApertureCoupling`, `exists_soninAperturePacketCurvature_re_opTrace_lt`, `not_exists_lower_bound_soninAperturePacketCurvature_re_opTrace` |
| 9 | **`(19)`**: the boundary corona as an algebraic quotient — bounded families modulo norm-null families — with the criterion that two classes agree exactly when the difference is norm-null | `soninBoundedFamilies`, `soninNullFamilies`, `soninNullFamilies_le_soninBoundedFamilies`, `soninNullInBounded`, `SoninCorona`, `soninBoundaryClass`, `soninBoundaryClass_eq_iff` |
| 9 | the four families as boundary points: the packet, its inverse dilate, and the two coupling images | `soninPacketFamily`, `soninDilatedPacketFamily`, `soninCouplingFamily`, `soninAdjointCouplingFamily`, `soninBoundaryClass_eq_zero_iff` |
| 9 | **`(20)`** and **`(21)`** as literal equalities of boundary classes, together with the nonvanishing of both packet classes | `soninBoundaryClass_soninCouplingFamily`, `soninBoundaryClass_soninAdjointCouplingFamily`, `soninBoundaryClass_soninPacketFamily_ne_zero`, `soninBoundaryClass_soninDilatedPacketFamily_ne_zero`, `soninBoundaryTransition_nontrivial` |
| 9 | **`(19)` is a Hausdorff Banach corona**: bounded families under the supremum norm, null families a *closed* subspace, quotient complete and `T2`; and the algebraic corona is the same object | `SoninBoundedSeq`, `soninNullSeq`, `isClosed_soninNullSeq`, `SoninCoronaSpace`, `soninCoronaClass`, `soninCoronaSpace_t2`, `soninCoronaSpace_completeSpace`, `soninCoronaClass_eq_iff`, `norm_soninCoronaClass_le`, `soninBoundedEquiv`, `map_soninNullInBounded`, `soninCoronaEquiv` |
| 9 | `(20)`, `(21)` and the strictly positive class norms inside the Banach corona | `soninCoronaClass_soninCouplingFamily`, `soninCoronaClass_soninAdjointCouplingFamily`, `norm_soninCoronaClass_soninPacketFamily_pos`, `norm_soninCoronaClass_soninDilatedPacketFamily_pos` |
| 9 | clock pullback: reindexing is linear, contractive, isometric for a surjective clock, and descends to the corona along an escaping clock | `soninReindex`, `norm_soninReindex_le`, `norm_soninReindex`, `soninReindexₗ`, `soninCoronaReindex` |

| 10 | **the unit family `w = u/‖u‖` of `(1)` itself**, and its inverse dilate `v = U_{1/r}w`; the dilate of the normalization is the normalization of the dilate | `soninNormalizedPacket`, `soninNormalizedDilatedPacket`, `soninNormalizedDilatedPacket_eq` |
| 10 | both are genuine unit vectors, and the raw packet is eventually nonzero along an escaping clock so the normalization is never degenerate | `norm_soninNormalizedPacket`, `norm_soninNormalizedDilatedPacket`, `eventually_soninPacketEven_ne_zero`, `eventually_norm_soninNormalizedPacket_eq_one` |
| 10 | the unit packet read as a function, with **both Meyer conditions** `w(0)=0` and `∫w=0`, evenness, smoothness, compact support, and the identification of its `L²` class with the unit vector | `soninNormalizedPacketFun`, `soninNormalizedPacketFun_zero`, `integral_soninNormalizedPacketFun`, `soninNormalizedPacketFun_even`, `contDiff_soninNormalizedPacketFun`, `hasCompactSupport_soninNormalizedPacketFun`, `soninNormalizedPacket_coeFn` |
| 10 | **`(3)` on the unit family**: `‖Z_r w_r − U_{1/r} w_r‖ → 0` | `tendsto_norm_soninApertureCoupling_soninNormalizedPacket_sub` |
| 10 | **`(4)` on the unit family**: `‖Z_r w_r‖ → 1` | `tendsto_norm_soninApertureCoupling_apply_soninNormalizedPacket` |
| 10 | **`(4a)` and `(4b)` on the unit family**: adjoint and coupling are mutually inverse on the two unit classes | `tendsto_norm_adjoint_soninApertureCoupling_soninNormalizedDilatedPacket_sub`, `tendsto_norm_adjoint_mul_soninApertureCoupling_soninNormalizedPacket_sub`, `tendsto_norm_soninApertureCoupling_adjoint_soninNormalizedDilatedPacket_sub` |
| 10 | **`(4c)` on the unit family**: every fixed Mellin exponent is blind to the unit packet to all polynomial orders | `soninNormalizedPacketMellin`, `tendsto_pow_mul_norm_soninNormalizedPacketMellin` |

Files: `formal/GaloisForLFunctions/RHTower/SoninAnnulusBump.lean`,
`formal/GaloisForLFunctions/RHTower/SoninAnnulusPacket.lean`,
`formal/GaloisForLFunctions/RHTower/SoninCosineRiemannLebesgue.lean`,
`formal/GaloisForLFunctions/RHTower/SoninAnnulusPacketAsymptotics.lean`,
`formal/GaloisForLFunctions/RHTower/SoninPacketWeakEscape.lean`,
`formal/GaloisForLFunctions/RHTower/SoninPacketL2.lean`,
`formal/GaloisForLFunctions/RHTower/SoninPacketCompactVanishing.lean`,
`formal/GaloisForLFunctions/RHTower/SoninFourierUniformDecay.lean`,
`formal/GaloisForLFunctions/RHTower/SoninPacketFourierPointwise.lean`,
`formal/GaloisForLFunctions/RHTower/SoninPacketFourierEscape.lean`,
`formal/GaloisForLFunctions/RHTower/SoninPacketSupportCutoffs.lean`,
`formal/GaloisForLFunctions/RHTower/SoninPhysicalTailVanishing.lean`,
`formal/GaloisForLFunctions/RHTower/SoninDilatedPacketCompactVanishing.lean`,
`formal/GaloisForLFunctions/RHTower/SoninPacketFourierModulation.lean`,
`formal/GaloisForLFunctions/RHTower/SoninFourierCutoffDilation.lean`,
`formal/GaloisForLFunctions/RHTower/SoninOuterTailIntegral.lean`,
`formal/GaloisForLFunctions/RHTower/SoninShiftedTailBound.lean`,
`formal/GaloisForLFunctions/RHTower/SoninBumpFourierL2.lean`,
`formal/GaloisForLFunctions/RHTower/SoninPacketBandEnergyBound.lean`,
`formal/GaloisForLFunctions/RHTower/SoninPacketLowBandEscape.lean`,
`formal/GaloisForLFunctions/RHTower/SoninPacketHighBandCapture.lean`,
`formal/GaloisForLFunctions/RHTower/SoninPacketFourierConcentration.lean`,
`formal/GaloisForLFunctions/RHTower/SoninDilatedPacketLayerLimit.lean`,
`formal/GaloisForLFunctions/RHTower/SoninCouplingPacketLimit.lean`,
`formal/GaloisForLFunctions/RHTower/SoninCouplingNonannihilation.lean`,
`formal/GaloisForLFunctions/RHTower/SoninStrictApertureCurvature.lean`,
`formal/GaloisForLFunctions/RHTower/SoninCouplingAdjointSetup.lean`,
`formal/GaloisForLFunctions/RHTower/SoninPacketBandGapLimits.lean`,
`formal/GaloisForLFunctions/RHTower/SoninDoublyContractedPacket.lean`,
`formal/GaloisForLFunctions/RHTower/SoninCouplingAdjointLimit.lean`,
`formal/GaloisForLFunctions/RHTower/SoninCouplingPartialUnitary.lean`,
`formal/GaloisForLFunctions/RHTower/SoninRapidFourierDecay.lean`,
`formal/GaloisForLFunctions/RHTower/SoninMellinWeight.lean`,
`formal/GaloisForLFunctions/RHTower/SoninMellinBlindness.lean`,
`formal/GaloisForLFunctions/RHTower/SoninCouplingEnergyLowerBound.lean`,
`formal/GaloisForLFunctions/RHTower/SoninCouplingOperatorNormFloor.lean`,
`formal/GaloisForLFunctions/RHTower/SoninUnboundedSourcePacket.lean`,
`formal/GaloisForLFunctions/RHTower/SoninNoAperturePacketFloor.lean`,
`formal/GaloisForLFunctions/RHTower/SoninBoundaryCorona.lean`,
`formal/GaloisForLFunctions/RHTower/SoninBoundaryTransition.lean`,
`formal/GaloisForLFunctions/RHTower/SoninCoronaBanach.lean`,
`formal/GaloisForLFunctions/RHTower/SoninNormalizedPacket.lean`.

Note the family is read along a sequence `kappa : N -> R` tending to infinity, matching the card's
own integer-clock phrasing; that is also what the corpus's compact-operator lemma expects.

The modulation identity of the paper proof was not needed: `F(u_kappa)(xi)` is literally the
pairing of the packet against the unimodular weight `exp(-2 pi i x xi)`, so `(7)` gives pointwise
vanishing directly, and `|u| <= 2 phi` gives a frequency-independent sup bound; dominated
convergence on the bounded band finishes `(10)`.

The whole chain `(3)`--`(5)`, `(4a)`--`(4c)`, `(6)`--`(16)`, `(19a)`--`(19d)` and the boundary
interpretation `(19)`--`(21)` is now unconditional Lean. The discrete model reads the clock along a
sequence `r : N -> R` tending to infinity rather than over the real ray `(1, infinity)`; every
statement of the paper proof is a statement about such clocks, and the crossing clock
`soninCrossingClock` exhibits one, so nothing is lost.

In the Banach model the corona is `lp (fun _ : N => evenSubspace) infinity` modulo the null
sequences; closedness of the null subspace is the only new analytic input, and it is the standard
uniform-approximation argument.

## Log

- 2026-08-01 — **the boundary interpretation `(19)`--`(21)` is now Lean.**  The corona exists twice:
  as the algebraic quotient of bounded families by null families, and as the Hausdorff Banach
  quotient of `lp(N, L^2_even)` at exponent infinity by the *closed* subspace of null sequences,
  the two being linearly isomorphic.  `(20)` and `(21)` are literal equalities of boundary classes
  — `(3)` and `(4a)` say exactly that the relevant differences are norm-null — and both packet
  classes are nonzero, hence of strictly positive corona norm.  Clock pullback is a contraction,
  isometric for a surjective clock, and descends to the corona along an escaping clock.
- 2026-08-01 — the `liminf ||Z_r|| >= 1` half of `(4)` is now Lean in operator-norm form, closing
  the last statement of the card that had only been formalized in packet-norm form.
- 2026-08-01 — **`(4c)` proved.  Every theorem on this card is now formalized unconditionally.**
  The three results of the card — the cofinal nonannihilation `(3)`-`(5)`, the adjoint/partial-unitary
  theorem `(4a)`-`(4b)`, and Mellin blindness `(4c)` — are all Lean, with no hypothesis beyond the
  strict flag `0 < a < q < b < c` and a clock past the crossing threshold.
- 2026-08-01 — the oscillatory-integral decay is now stated for an arbitrary smooth compactly
  supported weight, so the same lemma serves the Mellin weight and the profile itself.  `(4c)` is
  the sum of those two applications.
- 2026-08-01 — the Mellin transform of the packet is now a corpus object, split into the
  oscillatory integral against the fixed weight and the mean correction, with the oscillatory part
  written as the average of the weight's transform at `+w` and `-w`.  Both directions of rapid
  decay are available, so `(4c)` is now the limit assembly plus the rapid decay of the mean.
- 2026-08-01 — the Mellin weight is now a corpus object with the two properties the decay lemma
  needs.  Smoothness is by cases: away from the origin the kernel is smooth, near the origin the
  profile vanishes on a whole neighbourhood, so the product is locally constant zero there.  The
  kernel is carried as `exp(-s log x)` rather than `cpow`, with the identification on the positive
  axis recorded separately — that keeps the branch cut out of the smoothness argument entirely.
- 2026-08-01 — started `(4c)`.  The paper proof does repeated integration by parts; in Lean the
  same content is one step, because mathlib already has "smooth compactly supported implies
  Schwartz" and "Schwartz transforms decay faster than every power".  What is left for `(4c)` is
  to see the Mellin weight `x^{-s}` cut to the annulus as a smooth compactly supported function —
  which it is, since the annulus avoids the origin.
- 2026-08-01 — **the adjoint theorem is complete**: `(4a)` and both halves of `(4b)`.  The
  cofinal boundary transition is a genuine partial unitary on the two packet classes, with the
  Hilbert adjoint as its inverse there — unconditionally in Lean.  Only the Mellin-blindness
  theorem `(4c)` remains unformalized on this card.
- 2026-08-01 — **`(4a)` proved**: `|| Z_r^* v_r - w_r || -> 0`.  With `(3)` this is the adjoint
  theorem's first half — the coupling and its Hilbert adjoint carry the two packet classes to each
  other.  `(4b)`, the partial-unitary statement, is now pure triangle inequality on `(3)` and
  `(4a)` with the uniform bound `||Z_r|| <= 2`.
- 2026-08-01 — **`(19d)` proved**: the outer layer kills the doubly contracted packet.  Note the
  asymmetry with `(16)`: there the Fourier shell converged to the *identity*, here it converges to
  *zero*, because both apertures now capture the packet rather than straddling its carrier.  All
  four ingredients `(19a)`-`(19d)` of the adjoint theorem are now in Lean.
- 2026-08-01 — the two concentration limits restated in gap form, with the aperture and carrier
  free sequences.  The band-energy bounds only ever saw the difference, so tying them to a common
  clock was an artefact of the first packaging; `(19d)` needs carrier `~ r` against aperture
  `~ r^2`, which the gap form covers directly.
- 2026-08-01 — started the *adjoint* theorem `(4a)`--`(4b)`, which the gate line did not name but
  which is proved on this card and therefore in scope: `(19a)`, `(19b)`, `(19c)` are now Lean.
  Remaining for `(4a)`: `(19d)`, the vanishing of the outer layer on the doubly contracted packet,
  whose spectrum sits at `q/r^2` and whose support escapes at radius `r^2 b`.
- 2026-08-01 — **2 → 3 gate closed.**  `(5)` proved, and the two scale-free capstones: for every
  strict aperture flag `0 < a < q < b < c` there is an actual dilation scale `r` with `c < r a` at
  which the successive-layer coupling is nonzero and the aperture curvature is strictly negative.
  Stated with an explicit clock so the hypotheses are demonstrably inhabited — the result is not a
  statement about an empty family.
- 2026-08-01 — **`(4)` proved, and with it the headline nonannihilation**: the coupling is nonzero
  for every sufficiently large clock, unconditionally in Lean.  The packet is not normalised in the
  formalisation, so `(4)` reads as convergence to the packet's own limiting norm
  `sqrt(||phi||^2 / 2) > 0` rather than to `1`; dividing by the packet norm recovers the card's
  statement.  Only `(5)`, the strict-curvature restatement, is left.
- 2026-08-01 — **`(3)` proved**, the theorem of the card: `|| Z_r w_r - U_{1/r} w_r || -> 0` along
  any clock with `1 < r_n`, `c <= r_n a`, `r_n -> infinity`.  The corpus two-branch estimate does
  the algebra and the three limits `(8)`, `(10)`, `(16)` kill the three error terms.  What is left
  is bookkeeping: `(4)` and `(5)` follow from `(3)` plus the already-proved normalisation `(6)`.
- 2026-08-01 — **`(16)` proved**: `||L_{a,b} v_r - v_r|| -> 0`.  The three summands of the exact
  layer splitting behave differently and each needs its own mechanism — the physical shell
  vanishes *eventually and exactly* (escaped support), the Fourier shell converges (concentration),
  the corrections converge (compactness).  Paper steps `(6)`-`(16)` are now all in Lean; only the
  final assembly with the corpus branch estimate remains.
- 2026-08-01 — **`(13)` is complete**: both horns, in the packet form and in the fixed-aperture
  dilated form.  With `0 < a < q < b` the dilated packet has `||R_a v_r|| -> 0` and
  `||v_r - R_b v_r|| -> 0`, so its spectrum is asymptotically trapped between the two apertures of
  the flag.  Paper steps `(6)`-`(15)` are now all formalized; what is left is `(16)` and the
  combination with the corpus branch estimate.
- 2026-08-01 — the outer-band energy bound and the band-independent three-term spectral bound.
  The second is the band-energy estimate stated over an arbitrary measurable set rather than a
  central interval, so the remaining high horn is the same two shift applications as the low one.
- 2026-08-01 — the low horn of `(13)` is proved, in both the packet form and the fixed-aperture
  dilated form `||R_{a0} v_r|| -> 0`.  The dilation conjugation makes the two statements the same
  fact, so the fixed-aperture version costs one `congr`.
- 2026-08-01 — the quantitative half of `(13)` is proved: an explicit bound on the packet's energy
  inside a central Fourier band, in terms of the profile's spectral tail beyond the gap between the
  carrier and the band edge, plus the squared mean.  Taking `t = r a` and carrier `r q` with
  `a < q` makes the gap `r(q-a)`, so both terms vanish and the low horn of `(13)` follows.
- 2026-08-01 — the profile's spectral energy density is now a named corpus object with all three
  properties the estimate consumes.  Every remaining piece of `(13)` is an application of lemmas
  already proved; the step left is the arithmetic assembly.
- 2026-08-01 — the two shift-past-a-band bounds added, both with the gap written as the distance
  between the shift and the band edge.  With `phihat` as the density and the carrier as the shift,
  the gaps are exactly `r(q-a)` and `r(b-q)`, so the outer-tail estimate applies to both horns of
  `(13)` with one lemma each.
- 2026-08-01 — both remaining ingredients of `(13)` built: the dilation conjugation that turns a
  Fourier band of the dilate into a band of the packet at the rescaled aperture, and the outer-tail
  integral estimate.  `(13)` is now the assembly `(12)` + translation of the integration variable +
  outer tail, with the two apertures `ra < rq < rb` separating at rate `r`.
- 2026-08-01 — `(9)` and `(12)` proved: the modulation identity, and the packet's transform as
  `(phihat(xi-a) + phihat(xi+a))/2 - mu phihat(xi)`.  The carrier *translates* the profile's
  transform without deforming it, which is what makes the leftover mass near the origin an `L^2`
  tail of a fixed function at radius growing with the carrier.
- 2026-08-01 — `(15)` proved.  Steps `(6)`, `(7)`, `(8)`, `(10)`, `(11)`, `(14)`, `(15)` of the
  paper proof are now Lean.  What is left is the Fourier concentration `(13)`, and the route is
  now clear: conjugating the dilation through the Fourier transform turns `||R_a v_r||` into
  `||R_{ra} w_r||`, and the modulation identity makes that an `L^2` tail of `phihat` at radius
  `r(q-a) -> infinity`, which the tail lemma of the previous step already covers.
- 2026-08-01 — `(14)` proved, in the reusable form "support escaping to infinity implies weakly
  null".  Worth distinguishing from `(7)`: the packet escapes weakly because it *oscillates*, the
  dilated packet because its *support leaves every bounded set* — two different mechanisms, and
  only the second one survives the dilation.
- 2026-08-01 — `(11)` proved, together with the two physical-cutoff hypotheses the corpus
  two-branch estimate consumes.  The dilation covariance of the physical cutoff does all the work,
  so no support computation on the dilated function is needed.
- 2026-08-01 — `(10)` proved: the packet leaves every fixed central Fourier band, by dominated
  convergence on the band against the corpus bridge from the `L^2` Fourier transform to the
  classical integral.  Steps `(6)`, `(7)`, `(8)`, `(10)` of the paper proof are now all in Lean.
- 2026-08-01 — pointwise Fourier escape plus a uniform sup bound.  Note the modulation identity in
  the paper proof is not needed in Lean: the transform at a fixed frequency *is* a weak pairing, so
  `(7)` covers it directly.  `(10)` now reduces to dominated convergence on a bounded band.
- 2026-08-01 — `(8)` proved: compact corrections vanish along the family, via Fréchet--Riesz and
  the corpus's compact-operator/weakly-null lemma.  Stated for arbitrary compact operators, so it
  covers the projection correction and every element of the relative ideal at once.
- 2026-08-01 — the packet now lives in the corpus as an actual vector of the even Sonin space,
  with weak escape against every `L²` weight and a frequency-independent norm bound.  Both
  hypotheses of the corpus's compact-operator/weakly-null lemma are therefore available.
- 2026-08-01 — weak escape `(7)` proved in Lean, after upgrading the cosine Riemann--Lebesgue
  lemma from continuous-compactly-supported to merely integrable weights (real and complex), which
  is what pairing against an arbitrary `L²` vector needs.
- 2026-08-01 — Lean plan step 3 half done: cosine Riemann--Lebesgue built on mathlib's
  `Real.zero_at_infty_fourier`, and the normalisation `(6)` proved — the packet energy tends to
  half the profile energy, which is positive, so the family is cofinal and not degenerate.
- 2026-08-01 — Lean plan steps 1 and 2 done: the annular bump and the modulated zero-mean packet
  exist in the corpus with both exact Meyer conditions proved unconditionally.
- 2026-07-31 — Constructed the frequency-locked annular Meyer wavepacket, proved asymptotic
  isometric nonannihilation, identified the phase-space/scattering corona boundary, and isolated
  the remaining Xi indicial-grade landing theorem.
