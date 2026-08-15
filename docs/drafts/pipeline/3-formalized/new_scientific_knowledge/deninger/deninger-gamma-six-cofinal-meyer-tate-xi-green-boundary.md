# Deninger Gamma-six cofinal Meyer--Tate Xi Green boundary

- **Stage:** 3 — formalized
- **Route:** L
- **Status:** `[NEW SOURCE PRODUCER] [PAPER PROVED] [LEAN FORMALIZED]`
- **RH used:** no
- **Xi-zero location used:** no
- **Added axiom used:** no
- **Computation used:** no

## Frontier moved

Previous Route-L endpoint had explicit singular graph

\[
 \mathcal G_6=\ell^2(\mathbf N)\oplus_2\mathbf C,
 \qquad \omega_6=(0,1),
\]

and unique actual-Gamma transport

\[
 \widehat\Gamma_g(\omega_6)=T_g.
\]

What remained unspecified was whether `omega_6` occurred as a completed
arithmetic differential and whether its divisor fibre was the existing
completed Xi Green vector. This module constructs both facts.

## Literal Tate differential

Let

\[
 I_{\mathrm{Tate}}=\coprod_{m\ge0}\operatorname{Fin}(m+2),
 \qquad C^0_{\mathrm{Tate}}=\mathbf C^{(I_{\mathrm{Tate}})}.
\]

At stage `m`, let `b_m` be the new top-coordinate atom. It is proved
coordinatewise to equal the literal naturality defect

\[
 b_m=
 S_{m+1}\,\iota_m(e_m)-\iota_m\,S_m(e_m),
\tag{MT1}
\]

where `S_m` is the finite Tate forward arrow and `iota_m` appends a zero
coordinate. Thus `b_m` is not a declared mapping-cone generator.

The direct-sum differential

\[
 d_{\mathrm T}:\mathbf C^{(\mathbf N)}\longrightarrow
 C^0_{\mathrm{Tate}},
 \qquad d_{\mathrm T}(e_m)=b_m
\tag{MT2}
\]

has an explicit top-coordinate left inverse `r_T`:

\[
 r_{\mathrm T}d_{\mathrm T}=1.
\tag{MT3}
\]

Hence it is injective and retains every cofinal depth label.

## Arithmetic degree-one producer

Let `C_CCM,1` be the literal rational-adelic degree-one cyclic bar source and
`epsilon_1` its trace augmentation. Define

\[
 C^1_{\mathrm{MT}}=C_{\mathrm{CCM},1}\otimes
 \mathbf C^{(\mathbf N)},
 \qquad d_{\mathrm{MT}}=\epsilon_1\otimes d_{\mathrm T}.
\tag{MT4}
\]

For every ordinary prime `p`, the actual cycle atom `P_p=p tensor p^{-1}`
has `epsilon_1(P_p)=1`. Therefore

\[
 d_{\mathrm{MT}}(P_p\otimes c)=d_{\mathrm T}(c).
\tag{MT5}
\]

Decoding the top coordinates into the previously fixed singular graph gives
a strict completed differential `D_MT`. Lean proves

\[
 D_{\mathrm{MT}}(P_p\otimes c)=j(c),
\tag{MT6}
\]

where `j(c)=(c,sum c)` is finite graph admission. One fixed prime atom
already realizes the whole finite graph, so `D_MT` has dense range.

This yields a sharp no-go as part of the positive construction: every
continuous graph reader annihilating **all** Meyer--Tate boundaries is zero.
The RH-bearing Stokes theorem cannot be universal boundary-blindness on this
completion. It must use additional arithmetic structure of the distinguished
Xi Green chain.

## Exact completed Xi Green landing

For an actual divisor copy `q`, including multiplicity, write `g_G(q)` for
the already constructed reflected-Gaussian completed Green provenance
coefficient. Define

\[
 \Omega_G(q)=g_G(q)\omega_6,
 \qquad
 x_{p,q,N}=P_p\otimes g_G(q)u_N,
\tag{MT7}
\]

where `u_N` is the uniform cofinal averaging packet. Then

\[
 D_{\mathrm{MT}}x_{p,q,N}\longrightarrow\Omega_G(q),
 \qquad
 \pi_0\Omega_G(q)=0,
 \qquad
 \pi_s\Omega_G(q)=g_G(q).
\tag{MT8}
\]

Equation (MT8) is the coefficient-faithful landing demanded by the previous
frontier. Its trace is an existing completed Xi Green fibre, not a quotient
or norm defined by desired vanishing.

At total grade `g(q)=2 Re(q)-1`, strict actual-Gamma transport agrees at every
finite stage and at the completed limit:

\[
 \widehat\Gamma_{g(q)}D_{\mathrm{MT}}x_{p,q,N}
 =g_G(q)T_{g(q)}
 =\widehat\Gamma_{g(q)}\Omega_G(q).
\tag{MT9}
\]

Both `g_G(q)` and `T_{g(q)}` have exact critical-line radical, so

\[
 \widehat\Gamma_{g(q)}\Omega_G(q)=0
 \quad\Longleftrightarrow\quad
 \Re q=\frac12.
\tag{MT10}
\]

This is a classifier, not an annihilation assertion.

## Anti-theatre audit

- `d_T` is coordinatewise the finite Tate forward/inclusion commutator.
- `r_T d_T=1` prevents coefficient erasure.
- Arithmetic input is a literal CCM cyclic-bar atom with independently
  proved trace one.
- Divisor multiplicity is retained by `XiZeroCopy`.
- Green coefficient is imported from existing source-horizon construction;
  it is not defined from graph transport or physical vanishing.
- Actual Gamma/Sonin value is proved on every finite chain before passage to
  the limit.
- Dense-range theorem explicitly prevents falsely declaring a universal
  continuous Stokes reader.

## Novelty audit

Finite mapping telescopes, cyclic augmentations, and nonclosable graph
completions are standard separately. Novel claim is exact conjunction:
literal cofinal Tate naturality differential, rational-adelic trace-one prime
cycle, source-selected Gamma graph, multiplicity-aware completed Xi Green
fibre, and fixed actual Sonin receiver. No audited primary source supplies
this Route-L chain.

## Remaining frontier

Prove a **distinguished**, non-universal arithmetic Stokes identity for the
specific Green-weighted chain `(MT7)`. Because `D_MT` has dense range, no
nonzero continuous reader can kill every boundary. Required identity must
retain resolved divisor/prime provenance and use extra Meyer/Rost--Schmid or
co-Poisson common-test structure to annihilate only this selected Green
boundary. By `(MT10)`, that is now sole RH-bearing operation.

## Lean certificate

Module:
`GaloisForLFunctions/RHTower/DeningerGammaSixCofinalMeyerTateXiGreenBoundary.lean`.

Capstones:

- `deningerGammaSixCofinalTateNaturalityAtom_stage`;
- `deningerGammaSixCofinalTateTopReadout_comp_naturalityDifferential`;
- `deningerGammaSixCofinalMeyerTateCompletedDifferential_primeAtom`;
- `deningerGammaSixCofinalMeyerTateCompletedDifferential_dense`;
- `continuousLinearMap_eq_zero_of_forall_meyerTateBoundary_eq_zero`;
- `tendsto_deningerGammaSixCofinalMeyerTateCompletedDifferential_xiGreenChain`;
- `deningerGammaSixCofinalGraphTrace_xiGreenVerticalBoundary`;
- `deningerGammaSixCofinalGraphPhysicalTransport_xiGreenFiniteChain`;
- `deningerGammaSixCofinalGraphPhysicalTransport_xiGreenBoundary_eq_zero_iff`.

Verification:

- direct `lake env lean` passed;
- leaf-only `lake build GaloisForLFunctions.RHTower.DeningerGammaSixCofinalMeyerTateXiGreenBoundary`
  passed;
- capstone axiom audit reports only `propext`, `Classical.choice`, and
  `Quot.sound`;
- umbrella import is wired; umbrella was not built.
