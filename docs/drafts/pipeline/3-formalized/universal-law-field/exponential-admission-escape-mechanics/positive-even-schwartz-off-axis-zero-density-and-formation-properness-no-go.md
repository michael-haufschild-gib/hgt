# Positive-even Schwartz off-axis-zero density and formation-properness no-go

- **ID:** ULF-EAEM-2
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `../../../1-in-progress/universal-law-field/exponential-admission-escape-mechanics/field-programme.md`
- **Statement:** At every fixed point with nonzero real and imaginary parts, strictly positive even
  Schwartz sources with a bilateral-Laplace zero there are dense in the nonnegative even Schwartz
  cone. They retain functional-equation symmetry, arbitrary common split recovery, exact
  information conservation, and strict reflected Jeffreys properness. Therefore generic positive
  symmetric formation/properness cannot select a critical fixed locus; source admission must control
  exponential tails or impose a stronger variation-diminishing law.

## Goal

Test the strongest generic selection package presently available:

\[
 \text{positive source}
 +\text{functional equation}
 +\text{common recovery}
 +\text{information conservation}
 +\text{global properness}.
\]

The theorem constructs sources satisfying all five properties with prescribed off-axis zeros. It
then identifies the exact missing mechanism: ordinary Schwartz topology is too weak for horizontal
Laplace evaluation.

## 1. Setup

Let `S_even^+` denote the cone of real, even, nonnegative Schwartz functions on `R`. For a function
having the required exponential moment, write

\[
 \mathcal L_z f=\int_{\mathbb R}e^{zx}f(x)\,dx,
 \qquad z=a+i\tau.
 \tag{EA.1}
\]

Fix throughout

\[
 a\ne0,\qquad \tau\ne0.
 \tag{EA.2}
\]

Because an even source satisfies `L_{-z}f=L_zf`, it is enough in the construction to take `a>0`.
The case `a<0` follows by replacing `z` with `-z`.

Let

\[
 g(x)=\pi^{-1/2}e^{-x^2},\qquad
 g_R(x)=g(x-R)+g(x+R).
 \tag{EA.3}
\]

Then `g_R` is strictly positive, even, and Schwartz, and

\[
 \mathcal L_zg_R=2G(z)\cosh(zR),
 \qquad G(z)=\mathcal L_zg=e^{z^2/4}\ne0.
 \tag{EA.4}
\]

## 2. Explicit positive two-shell witness

Put

\[
 A=\frac{\pi a}{|\tau|},\qquad
 x=\frac{\pi}{|\tau|}.
 \tag{EA.5}
\]

For `tau>0`, direct periodicity gives

\[
 \cosh(zx)=-\cosh A,
 \qquad
 \cosh(2zx)=\cosh(2A).
 \tag{EA.6}
\]

The same identities hold after conjugation when `tau<0`. Hence the positive even atomic measure

\[
 \mu_z=cosh(2A)(\delta_x+\delta_{-x})
       +\cosh(A)(\delta_{2x}+\delta_{-2x})
 \tag{EA.7}
\]

satisfies

\[
 \mathcal L_z\mu_z
 =2\cosh(2A)\cosh(zx)+2\cosh(A)\cosh(2zx)=0.
 \tag{EA.8}
\]

Both weights are strictly positive. Convolving with `g` gives a strictly positive even Schwartz
density

\[
 f_z=g*\mu_z,
 \qquad
 \mathcal L_wf_z=G(w)\mathcal L_w\mu_z.
 \tag{EA.9}
\]

Therefore `L_z f_z=0`. Reality and evenness give the entire quartet

\[
 \mathcal L_{z}f_z=\mathcal L_{-z}f_z
 =\mathcal L_{\bar z}f_z=\mathcal L_{-\bar z}f_z=0.
 \tag{EA.10}
\]

This already refutes selection from positivity, smoothness, rapid decay, and functional-equation
symmetry.

## 3. Exponential evaluation is discontinuous in Schwartz topology

### Theorem 3.1 — remote-packet escape

There is a sequence of strictly positive even Schwartz functions `q_N` such that

\[
 q_N\longrightarrow0
 \quad\text{in Schwartz topology},
 \qquad
 \mathcal L_zq_N\longrightarrow G(z)\ne0.
 \tag{EA.11}
\]

Consequently bilateral evaluation at any `z` with `Re z != 0` has no continuous extension from
the entire-Laplace Schwartz subspace to ordinary Schwartz space.

### Proof

Take

\[
 R_N=\frac{2\pi N}{|\tau|},\qquad
 q_N=e^{-aR_N}g_{R_N}.
 \tag{EA.12}
\]

For every Schwartz seminorm

\[
 p_{m,n}(f)=\sup_x|x|^m|f^{(n)}(x)|,
\]

translation gives

\[
 p_{m,n}(g_R)\le C_{m,n}(1+R)^m.
 \tag{EA.13}
\]

Thus `p_{m,n}(q_N)` is bounded by an exponential decay times a polynomial and tends to zero.
Meanwhile `exp(i tau R_N)=1`, so `(EA.4)` gives

\[
 \mathcal L_zq_N
 =G(z)\left(1+e^{-2aR_N}\right)
 \longrightarrow G(z).
 \tag{EA.14}
\]

This proves the theorem. QED.

## 4. Density of positive off-axis-zero sources

### Theorem 4.1 — zero-insertion density

Let `f` be any nonnegative even Schwartz function. Every Schwartz neighborhood of `f` contains a
strictly positive even Schwartz function `F` whose bilateral Laplace transform is entire and
satisfies

\[
 \mathcal L_zF=0.
 \tag{EA.15}
\]

Equivalently, within the entire-Laplace positive-even sources, the zero locus at every fixed
off-axis `z` is dense for the inherited Schwartz topology.

### Proof

**Step 1: compact positive approximation.** Choose even cutoffs `chi_j` with
`0<=chi_j<=1`, compact support, and `chi_j=1` on `[-j,j]`. Then

\[
 h_j=\chi_jf\longrightarrow f
 \tag{EA.16}
\]

in Schwartz topology. Each `h_j` is nonnegative, even, compactly supported, and has an entire
bilateral Laplace transform. It suffices to insert a zero by an arbitrarily small positive even
Schwartz perturbation of one fixed `h=h_j`.

**Step 2: three remote phases.** Put

\[
 \theta_0=0,\qquad \theta_1=2\pi/3,\qquad \theta_2=4\pi/3,
\]

and, for large integers `N`,

\[
 R_{N,j}=\frac{2\pi N+\theta_j}{|\tau|}.
 \tag{EA.17}
\]

Define normalized response vectors

\[
 u_{N,j}=2e^{-aR_{N,j}}\cosh(zR_{N,j}).
 \tag{EA.18}
\]

Up to reversing their cyclic order when `tau<0`,

\[
 u_{N,j}longrightarrow e^{i\theta_j}.
 \tag{EA.19}
\]

The origin lies in the interior of the equilateral triangle with vertices
`1,e^{2pi i/3},e^{4pi i/3}`. Interior containment is open under perturbation of the vertices.
Therefore, for all sufficiently large `N`, the positive cone generated by the three `u_{N,j}` is
all of `C`. More quantitatively, there is a radius `r>0`, independent of large `N`, such that

\[
 \{w:|w|\le r\}\subset
 \operatorname{conv}\{u_{N,0},u_{N,1},u_{N,2}\}.
 \tag{EA.20}
\]

Hence every fixed complex number `W` has a representation

\[
 W=\sum_{j=0}^2\beta_{N,j}u_{N,j},
 \qquad \beta_{N,j}\ge0,
 \qquad \sum_j\beta_{N,j}\le |W|/r.
 \tag{EA.21}
\]

When `W=0`, use instead a positive barycentric representation of the origin and multiply all
coefficients by any small positive scalar.

**Step 3: exact cancellation with topology-small mass.** Set

\[
 W=-\frac{\mathcal L_zh}{G(z)},
 \qquad
 k_N=\sum_{j=0}^2\beta_{N,j}e^{-aR_{N,j}}g_{R_{N,j}}.
 \tag{EA.22}
\]

Equations `(EA.4)`, `(EA.18)`, and `(EA.21)` give

\[
 \mathcal L_zk_N=-\mathcal L_zh.
 \tag{EA.23}
\]

At least one coefficient is positive, so `k_N` is strictly positive on all of `R`. It is even,
Schwartz, and has an entire bilateral Laplace transform. The uniform coefficient bound in
`(EA.21)` and the translation estimate `(EA.13)` give

\[
 p_{m,n}(k_N)
 \le C'_{m,n}(1+R_N)^m e^{-aR_N}\longrightarrow0.
 \tag{EA.24}
\]

Thus `F_N=h+k_N` is strictly positive and even, converges to `h` in Schwartz topology, and satisfies
`L_zF_N=0`. Combining with `(EA.16)` proves density at the original `f`. QED.

## 5. Functional equation, recovery, information, and proper work all survive

Normalize one constructed source to a probability density `P_0`. Since it is a finite Gaussian
mixture, every exponential moment exists. Define the exponential family

\[
 dP_t(x)=e^{tx-A(t)}dP_0(x),
 \qquad
 A(t)=\log\int e^{tx}\,dP_0(x).
 \tag{EA.25}
\]

Evenness gives `A(-t)=A(t)` and reflection `R(x)=-x` gives

\[
 R_*P_t=P_{-t}.
 \tag{EA.26}
\]

Let `K` be any parameter-independent Markov recovery kernel and let `E_K(P_t)` be the split packet.
The prior split-formation theorem gives

\[
 D(E_KP_t\Vert E_KP_s)=D(P_t\Vert P_s).
 \tag{EA.27}
\]

Thus functional-equation reflection lifts canonically and information-neutrally through the common
recovery kernel.

Because `P_0` is not a point mass,

\[
 A''(t)=\operatorname{Var}_{P_t}(X)>0.
 \tag{EA.28}
\]

Hence `A'` is strictly increasing and odd. The reflected Jeffreys work is

\[
 J(t)=D(P_t\Vert P_{-t})+D(P_{-t}\Vert P_t)
     =4tA'(t)>0
 \qquad(t\ne0).
 \tag{EA.29}
\]

The same work is retained by `E_K` through `(EA.27)`. Therefore one source simultaneously has:

1. strict positivity and Schwartz regularity;
2. exact functional-equation reflection;
3. a prescribed off-axis zero quartet;
4. canonical common recovery;
5. exact relative-entropy conservation;
6. strict reflected-work properness.

## 6. Exact no-go and positive survivor

### Countertheorem 6.1 — generic packet selection is impossible

No theorem using only the six properties above can force all zeros onto the reflection-fixed axis.
The sources in Sections 2--5 are explicit countermodels.

### Corollary 6.2 — no Schwartz-open selection law

For fixed off-axis `z`, the set of positive even entire-Laplace Schwartz sources with
`L_zf != 0` has empty interior in the inherited Schwartz topology. Therefore no admission property
that is open and stable in ordinary Schwartz topology can imply nonvanishing at `z`.

### Strongest positive survivor — reporter-dominating admission

The obstruction identifies the needed topology exactly. On a source space controlling

\[
 \int e^{a|x|}|f(x)|\,dx,
 \tag{EA.30}
\]

evaluation at every `z` with `|Re z|<=a` is continuous, since

\[
 |\mathcal L_zf|\le\int e^{a|x|}|f(x)|\,dx.
 \tag{EA.31}
\]

Thus the missing ingredient is not stronger generic properness. It is a source-generated admission
law whose topology dominates the analytic reporters, possibly strengthened by a
variation-diminishing / total-positive formation law. Continuity alone does not prove
nonvanishing, but without it robust selection is impossible.

## 7. Scope and hostile audit

1. The theorem does not claim every positive source has off-axis zeros; it proves such sources are
   dense in the topology currently used by the generic formation package.
2. Pointwise positivity is much weaker than total positivity. Schoenberg/Pólya-frequency theory is
   therefore a plausible source of stronger laws, not a collision with this no-go.
3. The inserted source is not arithmetic. That is deliberate: it falsifies any theorem whose
   hypotheses forgot arithmetic lineage.
4. Gaussian smoothing does not create the zero; it preserves the exact atomic cancellation.
5. Properness is not false. It is orthogonal to zero selection unless source admission controls the
   exponential reporter.
6. Common recovery is not false. It is an information isometry and therefore faithfully transports
   the counterexample.
7. No RH conclusion is claimed.

## 8. Parent mathematics

All analytic ingredients are classical: Schwartz translation estimates, Gaussian convolution,
bilateral Laplace transforms, and convexity of log-partition functions. Total positivity is a known
stronger mechanism; see:

- A. Khare, <https://arxiv.org/abs/2008.05121>;
- D. Pickrell, <https://arxiv.org/abs/2104.05143>.

The theorem's use here is to separate, in one exact model, source topology, exponential
continuation, functional equation, recovery, and proper work.

## 9. Gates

- [x] explicit positive two-shell cancellation
- [x] positive even Schwartz smoothing
- [x] remote-packet discontinuity theorem
- [x] density theorem with exact positive-cone construction
- [x] functional-equation quartet
- [x] common-recovery information neutrality
- [x] strict reflected Jeffreys properness
- [x] exact topology survivor
- [x] Lean certification of finite algebraic core in
  `ConstitutivePositiveEvenLaplaceEscape.lean`
- [ ] source-generated exponential admission
- [ ] selection consequence


## Lean certificate

- [x] 2 → 3: Lean `GaloisForLFunctions.HTGeometry.PositiveEvenSchwartzLaplaceEscape`, `GaloisForLFunctions.HTGeometry.PositiveEvenSchwartzZeroDensity`, `GaloisForLFunctions.HTGeometry.PositiveEvenSourceFormationPackage`; `lake env lean` + module build pass; axiom audit `[propext, Classical.choice, Quot.sound]` only

Modules `GaloisForLFunctions.HTGeometry.PositiveEvenSchwartzLaplaceEscape` (70 constants), `GaloisForLFunctions.HTGeometry.PositiveEvenSchwartzZeroDensity` (50 constants), `GaloisForLFunctions.HTGeometry.PositiveEvenSourceFormationPackage` (21 constants), all axiom-audit clean; with the finite core `ConstitutivePositiveEvenLaplaceEscape`. Namespace `PositiveEvenLaplaceEscape`.

| Claim | Lean declaration |
|-|-|
| (EA.1) bilateral Laplace transform; entire-Laplace sources | `bilateralLaplace`, `HasEntireLaplace`, `entireLaplaceSubmodule` |
| entire-Laplace sources have entire (holomorphic) transform | `HasEntireLaplace.differentiable` |
| even source: `𝓛_{-z} = 𝓛_z`; real source: `𝓛_{z̄} = conj 𝓛_z`; reduction to `a, τ > 0` | `bilateralLaplace_neg_of_even`, `bilateralLaplace_conj`, `bilateralLaplace_eq_zero_iff_abs` |
| (EA.3)–(EA.4) `g = π^{-1/2}e^{-x²}` Schwartz, positive, even, `𝓛_z g = e^{z²/4}` | `gaussianPacket`, `gaussianPacket_apply`, `gaussianPacket_pos`, `gaussianPacket_neg`, `bilateralLaplace_gaussianPacket` |
| (EA.3)–(EA.4) `g_R` positive even Schwartz, `𝓛_z g_R = 2G(z)cosh(zR)` | `evenPacket`, `evenPacket_pos`, `evenPacket_neg`, `hasEntireLaplace_evenPacket`, `bilateralLaplace_evenPacket_eq_cosh` |
| §2 (EA.5)–(EA.10) explicit positive two-shell source, zero at `a+iτ`, full quartet | `twoShellSource`, `twoShellSource_pos`, `twoShellSource_neg`, `bilateralLaplace_twoShellSource`, `bilateralLaplace_twoShellSource_eq_zero`, `twoShellSource_quartet`, `positiveEvenTwoShellLaplace_offAxis_zero` |
| (EA.13) Schwartz translation estimate | `seminorm_compSubConst_le`, `seminorm_evenPacket_le` |
| Thm 3.1 (EA.11)–(EA.14) remote-packet escape | `remotePacketEscape`, `bilateralLaplace_remotePacket`, `tendsto_remotePacket_zero`, `exists_remote_periods` |
| Thm 3.1 consequence: no continuous extension / discontinuity on the entire-Laplace subspace | `not_exists_continuous_extension`, `not_continuousAt_bilateralLaplace` |
| Thm 4.1 Step 1 (EA.16) compact positive even approximation in Schwartz topology | `cutoffApprox`, `cutoffApprox_nonneg`, `cutoffApprox_neg`, `hasEntireLaplace_cutoffApprox`, `tendsto_cutoffApprox` |
| Thm 4.1 Steps 2–3 (EA.17)–(EA.24) remote phases, exact nonnegative cancellation, topology-small mass | `phasePeriod`, `bilateralLaplace_evenPacket_phase`, `bilateralLaplace_phase_zero/quarter/half/neg_quarter`, `tendsto_smul_evenPacket_zero`, `exists_zeroInsertion` |
| Thm 4.1 (EA.15) density, closure and neighborhood forms | `mem_closure_offAxisZeroSources`, `exists_offAxisZeroSource_mem_nhds` |
| §5 (EA.25) normalized source law and exponential family | `sourceLaw`, `isProbabilityMeasure_sourceLaw`, `sourceFamily`, `integrable_exp_mul_sourceLaw` |
| (EA.26) `A(-t) = A(t)`, `R_*P_t = P_{-t}` | `FormationPackage` (1st, 2nd), `ReflectedExponentialFamily.map_reflection_tilt` |
| (EA.27) common recovery preserves relative entropy | `FormationPackage` (3rd), `klDiv_splitPacketLaw` |
| (EA.28) `A'' > 0` | `iteratedDeriv_two_cumulant_pos` |
| (EA.29) `J(t) = 4tA'(t) > 0`, retained by recovery | `FormationPackage` (5th–7th), `four_mul_deriv_cumulant_pos` |
| §5 six-property package for every positive even entire-Laplace source and every Markov kernel | `sourceFamily_formationPackage` |
| Countertheorem 6.1 | `exists_offAxis_formation_countermodel`, `no_generic_packet_selection` |
| Corollary 6.2 empty interior; no Schwartz-open selection law | `interior_nonvanishing_eq_empty`, `no_open_admission_selection` |
| Survivor (EA.30)–(EA.31) reporter bound and reporter-norm continuity | `norm_bilateralLaplace_le_reporter`, `norm_bilateralLaplace_sub_le_reporter` |

## Log

- 2026-08-14 — dependency-closed after the packet functional-equation lift showed recovery was an
  isometry rather than a selector. The new theorem identifies ordinary Schwartz admission as the
  exact generic failure point.
- 2026-09-28 — Lean certificate audited; every numbered claim mapped to a declaration; moved to 3-formalized.
