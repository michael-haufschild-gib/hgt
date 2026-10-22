# Cofinal prime-periodization tomography and its strict Hodge obstruction

- **ID:** `deninger-cofinal-prime-periodization-tomography-instability`
- **Stage:** 3-formalized
- **Type:** SOURCE TOMOGRAPHY / TOPOLOGICAL NO-GO / POSITIVE CLASSIFICATION
- **Labels:**
  - `DAC_DENINGER_COFINAL_PRIME_PERIODIZATION_TOMOGRAPHY`;
  - `DAC_DENINGER_COFINAL_PERIODIZATION_NONSTRICTNESS`;
  - `DAC_DENINGER_COMPACT_ORBIT_WEIGHT_ONE_NO_GO`;
  - `DAC_DENINGER_EULER_DEPLETED_HALF_DENSITY_RELATIVE_DEFECT`.
- **Parent:** Route L in `rh-current-frontier-map.md`
- **Input:** `DAC_DENINGER_EULER_DEPLETED_MEYER_PERIODIZATION_EXTENSION`
- **Claim:** cofinally many prime circles determine every all-weight Meyer cochain, and hence give
  an algebraically conservative cross-prime model of the Euler-depleted Meyer quotient. No finite
  prime family does. However, the cofinal tomography has nonclosed range in the ordinary product
  topology, and every rotation-invariant compact-orbit energy has flow weight zero rather than
  Tate weight one. Thus the remaining Route-L Hodge object must contain a noncompact relative
  Tate defect before compact periodization.

## 1. Setup

Let
\[
 H_-=\mathscr S_{\exp}(\mathbb R)
\]
with its all-derivative, all-exponential-weight nuclear Fr\'echet topology. For every prime $q$
put
\[
 L_q=\log q,\qquad
 (T_a h)(t)=h(t-a),\qquad
 \Delta_q=1-T_{-L_q},
\tag{1}
\]
so that $\Delta_qh(t)=h(t)-h(t+L_q)$. Define
\[
 \operatorname{Per}_q h(\bar t)
 =\sum_{j\in\mathbb Z}h(t+jL_q).
\tag{2}
\]
For a set $Q$ of primes, write
\[
 \mathcal P_Q:H_-\longrightarrow
 \prod_{q\in Q}C^\infty(\mathbb R/L_q\mathbb Z),
 \qquad
 \mathcal P_Qh=(\operatorname{Per}_qh)_{q\in Q}.
\tag{3}
\]
The target has the ordinary countable product Fr\'echet topology.

For the Fourier transform
\[
 \widehat h(z)=\int_{\mathbb R}h(t)e^{-izt}\,dt,
\tag{4}
\]
two-ended faster-than-exponential decay makes $\widehat h$ entire. Unfolding `(2)` gives the exact
Fourier-coefficient identity
\[
 \frac1{L_q}\int_0^{L_q}
   \operatorname{Per}_q h(t)e^{-2\pi i kt/L_q}\,dt
 =\frac1{L_q}\widehat h\!\left(\frac{2\pi k}{L_q}\right)
 \qquad(k\in\mathbb Z).
\tag{5}
\]

## 2. Cofinal prime tomography

`[PROVED HERE] [DAC_DENINGER_COFINAL_PRIME_PERIODIZATION_TOMOGRAPHY]`

If $Q$ is any infinite set of ordinary primes, then
\[
 \ker\mathcal P_Q=0.
\tag{6}
\]
In contrast, if $Q$ is finite, then
\[
 0\ne\Delta_QH_-
 \subseteq\ker\mathcal P_Q,
 \qquad
 \Delta_Q=\prod_{q\in Q}\Delta_q.
\tag{7}
\]

### Proof

Every infinite set of primes is unbounded. If $\mathcal P_Qh=0$, equation `(5)` with $k=1$
gives
\[
 \widehat h\!\left(\frac{2\pi}{\log q}\right)=0
 \qquad(q\in Q).
\]
These are distinct zeros converging to $0$. The identity theorem gives $\widehat h=0$, and
Fourier injectivity gives $h=0$. This proves `(6)`.

For finite $Q$, choose $0\ne\phi\in C_c^\infty(\mathbb R)$. Every $\Delta_q$ is injective on
$H_-$: an $L_q$-periodic element with positive-end decay is zero. Hence
$\Delta_Q\phi\ne0$. The difference operators commute, while
$\operatorname{Per}_q\Delta_q=0$; therefore
$\operatorname{Per}_q\Delta_Q\phi=0$ for every $q\in Q$. This proves `(7)`.

Fix a prime $p$ and put
\[
 K_p=\ker\operatorname{Per}_p=\Delta_pH_-,
 \qquad B_p=\Delta_pZ(H_\cap).
\tag{8}
\]
The Euler-depleted extension gives
\[
 K_p/B_p\cong M_\zeta.
\tag{9}
\]
If $Q$ is infinite and $p\notin Q$, `(6)` induces an algebraic injection
\[
 M_\zeta\cong K_p/B_p
 \hookrightarrow
 \left(\prod_{q\in Q}C^\infty(\mathbb R/L_q\mathbb Z)\right)
 \big/\mathcal P_Q(B_p),
 \qquad
 [h]\longmapsto[\mathcal P_Qh].
\tag{10}
\]
Indeed, if $\mathcal P_Qh=\mathcal P_Qb$ for some $b\in B_p$, then `(6)` gives $h=b$.
Thus cross-prime compact orbits are algebraically conservative after the exact Poisson-boundary
quotient. This is stronger than sparse positive-radius sampling: each complete periodization
contains the full Fourier lattice, and the prime lengths cofinally accumulate at Fourier
frequency zero.

## 3. The tomography is not strict

`[PROVED HERE] [DAC_DENINGER_COFINAL_PERIODIZATION_NONSTRICTNESS]`

For every fixed $p$ and every infinite $Q$ disjoint from $p$, the restricted map
\[
 \mathcal P_Q:K_p\longrightarrow
 \prod_{q\in Q}C^\infty(\mathbb R/L_q\mathbb Z)
\tag{11}
\]
is continuous and injective, but it is not a topological embedding. Its range is not closed.

### Proof

Choose $0\ne\phi\in C_c^\infty(\mathbb R)$ and put
$\psi=\Delta_p\phi\ne0$. Fix $a>0$ and define
\[
 h_n=e^{-an}T_n\psi\in K_p.
\tag{12}
\]
For each fixed $q$, periodization intertwines $T_n$ with rotation of the $q$-circle. Every
$C^\infty$ seminorm is therefore
\[
 \|\operatorname{Per}_qh_n\|_{C^r}
 =e^{-an}\|\operatorname{Per}_q\psi\|_{C^r}
 \longrightarrow0.
\tag{13}
\]
Hence $\mathcal P_Qh_n\to0$ in the product topology.

Choose $u_0$ with $\psi(u_0)\ne0$. For all large $n$, the defining Meyer seminorm
\[
 q_{a,0,0}(h)=\sup_t e^{a|t|}|h(t)|
\]
satisfies
\[
 q_{a,0,0}(h_n)
 \ge e^{-an}e^{a|n+u_0|}|\psi(u_0)|
 =e^{au_0}|\psi(u_0)|>0.
\tag{14}
\]
Thus $h_n\not\to0$ in $K_p$, proving that the inverse on the range of `(11)` is not continuous.
Since $K_p$ and the countable product target are Fr\'echet, a closed range would make that inverse
continuous by the open-mapping theorem. Therefore the range is not closed.

Equation `(14)` identifies the exact lost datum: compact periodizations remember the translated
shape only up to rotations and do not control escape in the noncompact logarithmic direction.
Algebraic analytic continuation from the prime Fourier lattices is unique but unstable.

## 4. Compact orbit energy has the wrong weight

`[PROVED HERE] [DAC_DENINGER_COMPACT_ORBIT_WEIGHT_ONE_NO_GO]`

Let $E$ be a positive semidefinite quadratic form on the product in `(3)` invariant under the
simultaneous circle rotations induced by $T_a$. Its pullback
\[
 Q(h)=E(\mathcal P_Qh)
\tag{15}
\]
is translation-invariant:
\[
 Q(T_ah)=Q(h).
\tag{16}
\]
If the same form is required to have arithmetic weight one,
\[
 Q(T_ah)=e^aQ(h),
\tag{17}
\]
then $Q=0$. Compare `(16)` and `(17)` at any $a\ne0$.

Even one compact orbit already forces this conclusion without assuming rotation invariance of a
chosen form: because
\[
 \operatorname{Per}_q(T_{L_q}h)=\operatorname{Per}_qh,
\]
any form factoring through that orbit is $L_q$-periodic under the source flow, whereas `(17)`
multiplies it by $e^{L_q}=q$. It must vanish.

Thus the cofinal trace quotient `(10)` is an algebraically faithful coefficient model, but no
rotation-natural positive norm on compact prime traces can be the weight-one Hodge metric. This
obstruction is independent of RH and stronger than the same-prime zero-periodization no-go: it
also excludes rotation-invariant energies using all cross-prime circles simultaneously.

## 5. Conjecture loop and exact survivor

1. **Conjecture: finitely many complete prime traces recover the Euler-depleted sector.**
   **Failed exactly by `(7)`.** The finite Euler difference $\Delta_Q\phi$ is a nonzero common
   kernel vector.
2. **Conjecture: cofinally many complete prime traces recover it.**
   **Proved algebraically by `(6)` and `(10)`.** Entire Fourier uniqueness turns prime lengths
   into a source-pure tomography set.
3. **Conjecture: ordinary product topology turns that tomography into a closed Hodge carrier.**
   **Failed exactly by `(12)`--`(14)`.** Noncompact translates disappear in every fixed compact
   trace while retaining a Meyer exponential seminorm.
4. **Conjecture: a rotation-invariant all-prime trace norm supplies Deninger's weight-one
   polarization.** **Failed exactly by `(16)`--`(17)`.** Compact orbit energy has weight zero.

### The already-existing noncompact survivor, localized exactly

The corpus audit rules out claiming that every noncompact defect is missing:
`DeningerMeyerHalfDensityL1Completion.lean` already constructs
\[
 p_{1/2}(g)=\int_{\mathbb R}e^{t/2}|g(t)|\,dt,
 \qquad
 \overline p_{1/2}([g])
 =\inf_{f\in H_\cap}p_{1/2}(g-Zf).
\tag{18}
\]
It proves exact isometry of the centered flow
\[
 V_a=e^{-a/2}T_a
\tag{19}
\]
and the exact selector: an actual Xi evaluation is bounded by
$\overline p_{1/2}$ if and only if its real part is $1/2$.

`[PROVED HERE] [TRANSPORT COROLLARY]`
`[DAC_DENINGER_EULER_DEPLETED_HALF_DENSITY_RELATIVE_DEFECT]`

The Euler Green inverse localizes `(18)` to the concrete sector `(8)`:
\[
 r_p(h)
 =\inf_{f\in H_\cap}
   p_{1/2}(G_ph-Zf),
 \qquad h\in K_p.
\tag{20}
\]
This is a continuous seminorm, and for every $g\in H_-$,
\[
 r_p(\Delta_pg)=\overline p_{1/2}([g]).
\tag{21}
\]
Consequently:

1. $r_p$ kills $B_p=\Delta_pZ(H_\cap)$;
2. $r_p(e^{-a/2}T_ah)=r_p(h)$;
3. the value in `(21)` is independent of the auxiliary prime $p$;
4. its exact radical is
   \[
   \ker r_p
   =\Delta_p\!\left(
      H_-\cap\overline{Z(H_\cap)}^{\,L^1(e^{t/2}dt)}
    \right).
   \tag{22}
   \]

These statements follow immediately from the homeomorphism
$G_p:K_p\to H_-$, commutation of $G_p$ with translations, and the definition of distance to
$Z(H_\cap)$ in weighted $L^1$. They are recorded as transport, not as an independent novelty
claim.

The localized seminorm is nonzero unconditionally. Choose any known critical-line Xi zero
$\rho$ and the logarithmic Gaussian $g_\ast$, whose Mellin transform never vanishes. Since
$E_\rho$ annihilates $Z(H_\cap)$ and
$|E_\rho(g)|\le p_{1/2}(g)$,
\[
 r_p(\Delta_pg_\ast)
 =\overline p_{1/2}([g_\ast])
 \ge |E_\rho(g_\ast)|>0.
\tag{23}
\]
The centered escape family
\[
 h_a=\Delta_pV_ag_\ast
\tag{24}
\]
therefore satisfies
\[
 r_p(h_a)=r_p(\Delta_pg_\ast)>0,
 \qquad
 \mathcal P_Qh_a\longrightarrow0
 \quad(a\to+\infty)
\tag{25}
\]
in every ordinary compact-prime product. Thus `(20)` supplies exactly the noncompact control
missing from `(11)`; compact tomography cannot replace it.

### Exact hard survivor

The remaining Route-L problem is not construction of another carrier or another noncompact
seminorm. It is to upgrade `(20)` by source arithmetic:

1. prove the exact relative closedness identity
   \[
   H_-\cap\overline{Z(H_\cap)}^{\,L^1(e^{t/2}dt)}
   =Z(H_\cap),
   \tag{26}
   \]
   equivalently $\ker r_p=B_p$;
2. construct a compatible sesquilinear Green/Paugam polarization, rather than merely the
   $L^1$ seminorm, whose cochain radical is the same;
3. derive from Gamma/co-Poisson and real-Fourier source geometry that every actual Xi evaluation
   is admitted continuously by that faithful centered completion.

Clause 3 is RH-strength by the already-formalized half-density selector. It cannot be asserted as
generic functional analysis. The first hard scientific identity is therefore `(26)` together with
its polarized Gamma/co-Poisson admission law. Compact traces in `(10)` remain an algebraically
conservative comparison target, not the Hodge norm.

## 6. Hostile audit

- **No zero divisor.** The only analyticity used is the Fourier transform of a two-ended
  faster-than-exponential source cochain.
- **No disguised RH.** Equations `(5)`--`(25)` are unconditional. Equation `(26)` and
  all-divisor admission remain explicitly open.
- **Not sparse prime sampling.** Full periodizations expose Fourier lattices; `(6)` would be false
  for one evaluation at each positive prime radius.
- **Not a positivity construction.** The theorem proves algebraic conservativity, localizes the
  pre-existing half-density seminorm, and proves why ordinary compact topology cannot supply the
  required polarization.
- **No completion theatre.** Nonclosedness is witnessed by the explicit source family `(12)`;
  the missing topology is not declared into existence.
- **No Lean claim.** Lean corpus was audited read-only during its refactor; no Lean file or build
  belongs to this result.

## 7. Novelty boundary

Poisson summation, the identity theorem for entire functions, and the open-mapping theorem are
standard. Repository and targeted primary-source searches found no composition of these facts
with Meyer's all-weight Poisson quotient and Deninger's prime lengths that states `(6)`, the
relative injection `(10)`, the explicit non-strictness witness `(12)`, and the Tate-weight no-go
`(17)` as one source theorem. Novelty is claimed only for that arithmetic-source composition and
its exact Route-L frontier consequence, not for the analytic ingredients separately.

## References

- Ralf Meyer, *A spectral interpretation for the zeros of the Riemann zeta function*,
  arXiv:math/0412277.
- Christopher Deninger, *Dynamical systems for arithmetic schemes*, arXiv:1807.06400.
- `DAC_DENINGER_EULER_DEPLETED_MEYER_PERIODIZATION_EXTENSION`.
- `DAC_MEYER_PRIME_SAMPLING_COHOMOLOGY_OBSTRUCTION`.
- `DeningerMeyerHalfDensityL1Completion.lean`.

## Lean status

`formal/GaloisForLFunctions/RHTower/Deninger/DeningerFinitePeriodizationKernel.lean`, on the periodization
layer `DeningerMeyerPeriodization.lean`, `DeningerGreenSumSource.lean`,
`DeningerEulerDepletionTower.lean`, `DeningerDepletedPoisson.lean`.  Axiom audit:
`propext, Classical.choice, Quot.sound`.

### Done

- `(1)`/`(2)` — `deningerExpShiftSource`, `deningerPeriodizationDefect`,
  `deningerPeriodizationSum` are corpus-owned; `deningerShiftInt_summable` gives absolute
  convergence of `(2)` at every point, geometrically in the lattice index.
- `Δ_q` injective — `deningerPeriodizationDefect_injective`: an `L_q`-periodic element of the
  source vanishes, because the source decays at `+∞`.  This is the card's own argument.
- `Per_q Δ_q = 0` and `ker Per_q = Δ_q H_-` — `deningerPeriodization_defect`,
  `deningerPeriodization_range_eq_kernel`.  The second is `(8)`'s `K_p = Δ_p H_-`.
- the defects commute — `deningerPeriodizationDefect_comm`; `deningerDepletion` is the operator
  `Δ_Q` of a finite family and `deningerDepletion_injective` is its injectivity.
- **`(7)`** — `deningerFinitePeriodization_kernel_nontrivial`: **`0 ≠ Δ_Q H_- ⊆ ker 𝒫_Q` for every
  finite `Q`.**  The nonzero witness is the Poisson boundary of the corpus's Meyer witness
  (`deningerSourceWitness_ne_zero`, from injectivity of `Z`), rather than a bump function.

### Not yet formalized

- **The entire Fourier--Laplace transform is now built** —
  `formal/GaloisForLFunctions/RHTower/Deninger/DeningerPaleyWiener.lean`:
  `deningerFourierLaplace`, `deningerFourierLaplace_integrable` (integrable against every
  polynomial moment, at every complex frequency), `deningerFourierLaplace_hasDerivAt` and
  **`deningerFourierLaplace_differentiable`: `ĥ` is entire.**  The kernel bound is
  `‖e^{-izt}‖ = e^{(Im z)t} ≤ e^{|Im z||t|}`, absorbed by the source margin; differentiating costs
  one factor of `t`, absorbed by the same margin; the domination is uniform on a unit ball of
  frequencies, so `hasDerivAt_integral_of_dominated_loc_of_deriv_le` applies.
- **`(5)` is proved in the form the theorem uses** —
  `formal/GaloisForLFunctions/RHTower/Deninger/DeningerLatticeFrequency.lean`:
  `deningerFourierLaplace_shift` (translation multiplies `ĥ` by `e^{izL}`),
  `deningerFourierLaplace_defect` (`ĥ = (1 - e^{izL})ĝ` on a defect) and
  **`deningerFourierLaplace_vanishes_at_lattice`: `Per_L h = 0` forces `ĥ(2πk/L) = 0` for every
  `k ∈ ℤ`.**  This is a shorter route than the card's own: because `ker Per_L = Δ_L H_-` is already
  proved, no unfolding of the periodization over a fundamental interval is needed — no interchange
  of sum and integral, and no tiling of the line.
- **`(6)` is proved unconditionally** —
  `formal/GaloisForLFunctions/RHTower/Deninger/DeningerTomographyInjective.lean`:
  `deningerFourierLaplace_real` (`ĥ(2πξ) = ℱh(ξ)`), `deningerSource_eq_zero_of_fourierLaplace_zero`
  (Fourier inversion), `deningerSource_eq_zero_of_zeros_tendsto` (identity theorem on the entire
  `ĥ` from zeros accumulating at the origin), **`deningerCofinalTomography`** (unbounded periods)
  and **`deningerCofinalPrimeTomography`**: for an infinite set of primes `Q`,
  `Per_{log q} h = 0` for all `q ∈ Q` forces `h = 0`.  This is `ker 𝒫_Q = 0`.
- **The algebraic content of `(10)` is proved unconditionally** — same module,
  **`deningerCofinalPrimeTomography_eq`**: two cochains with the same periodization on every prime
  circle of an infinite prime set are equal.  This is exactly the injectivity argument the card
  gives for `(10)` ("if `𝒫_Q h = 𝒫_Q b` for `b ∈ B_p`, then `(6)` gives `h = b`"), stated without
  reference to `M_ζ`, so it does not wait on the Euler-depleted extension `(9)`.
- **§4 is proved unconditionally** —
  `formal/GaloisForLFunctions/RHTower/Deninger/DeningerCompactOrbitWeightNoGo.lean`:
  `deningerPeriodizationSum_shift` (`Per_L ∘ T_L = Per_L`),
  **`deningerCompactOrbitEnergy_weight_one_eq_zero`** (a weight-one functional factoring through a
  single compact orbit vanishes — the card's stronger form, with no rotation hypothesis) and
  `deningerRotationInvariantEnergy_weight_one_eq_zero` (`(16)` vs `(17)`).
- **The quantitative core of §3 is proved unconditionally** —
  `formal/GaloisForLFunctions/RHTower/Deninger/DeningerTomographyNonstrict.lean`:
  `deningerPeriodizationSum_expShift` (translation ↦ rotation), `deningerPeriodizationSum_periodic`,
  `deningerEscapeFamily_periodizationSum` (`(13)`: every compact trace carries the damping factor
  `e^{-as}`) and **`deningerEscapeFamily_meyer_ge`** (`(14)`: the Meyer seminorm cancels the damping
  exactly, so `q_{a,0}(h_s) ≥ e^{au}‖h(u)‖` independently of `s`), with
  `deningerEscapeFamily_meyer_pos`.
- **The target of `(3)` is now a real object.**  The earlier note on this card that
  `C^∞(ℝ/Lℤ)` was missing was wrong: `RHTower/Deninger/DeningerSmoothPeriodic.lean` and
  `DeningerSmoothPeriodicNuclear.lean` already carried the space and its nuclearity.  The one
  genuinely missing link — that the periodization *lands* there — is now built:
  `formal/GaloisForLFunctions/RHTower/Deninger/DeningerPeriodCutoff.lean` and
  `DeningerPeriodizationSmooth.lean` prove **`deningerPeriodizationSum_contDiff`** (`Per_L h` is
  `C^∞`) and **`deningerPeriodizationMem`** (`Per_L h ∈ C^∞(ℝ/Lℤ)`), and
  `DeningerPeriodizationMap.lean` assembles **`deningerPeriodizationMap`** (`Per_L` as a linear map),
  `deningerPeriodizationMap_ker` (`ker Per_L = Δ_L H_-`), **`deningerTomographyMap`** — this is
  equation `(3)`, `𝒫_Q : H_- → ∏_{q} C^∞(ℝ/L_qℤ)` — and
  **`deningerTomographyMap_injective`**, which is `(6)` stated for that map.
  The lattice sum has no summable majorant on `ℝ`, so `contDiff_tsum` does not apply directly; the
  proof cuts by a `ContDiffBump` equal to `1` on one period, where `|t+jL| ≥ |j|L - R` restores a
  geometric majorant, then propagates smoothness by periodicity.
- **§3's primary statement is proved** — `formal/GaloisForLFunctions/RHTower/Deninger/DeningerTomographyNotEmbedding.lean`:
  `deningerEscape_trace_le` (every `C^r` circle seminorm of the escaped trace carries the damping
  factor `e^{-as}`, because the trace is a rotation of the original scaled by that factor),
  `deningerEscape_trace_tendsto_zero`, and **`deningerPeriodization_not_isEmbedding`**: the traces
  tend to `0` in every circle seminorm while the Meyer seminorm stays above a *positive* constant
  independent of the escape parameter.  That is `(12)`--`(14)`, i.e. the inverse on the range is
  discontinuous.
- **`(9)` and `(10)` are proved** —
  `formal/GaloisForLFunctions/RHTower/Deninger/DeningerTomographyConservative.lean`:
  **`deningerIotaEquiv`** is `M_ζ ≃ ker Per̄_p`, which is `(9)`, assembled from card
  `deninger-euler-depleted-meyer-periodization-extension`'s `deningerIota_injective` and
  `deningerIota_range_eq_perBar_ker`; and **`deningerCofinalTrace_mod_mem`** with
  `deningerCofinalTrace_quotient_injective` give `(10)` — cross-prime traces are conservative
  modulo any subspace, exactly the argument the card gives.

- **§3's corollary "the range is not closed" is now proved unconditionally.**  mathlib has the open
  mapping theorem only for Banach spaces, so the Fréchet version was built first, in
  `formal/GaloisForLFunctions/HTGeometry/`: `FrechetOpenMappingBaire.lean`,
  `FrechetHalvingBasis.lean`, `FrechetOpenMappingStep.lean`, `FrechetTelescoping.lean`,
  `FrechetCauchy.lean`, `FrechetOpenMapping.lean` (**`isOpenMap_of_surjective`**,
  `continuous_symm_of_continuous`) and `FrechetClosedRange.lean`
  (**`not_isClosed_range_of_not_continuous_symm`**).  The Baire step gives
  `closure (f '' U) ∈ 𝓝 0`; the closure is removed by writing a point of it as the sum of a series
  whose terms lie in successively smaller members of a halving basis of balanced neighbourhoods.
  The two Deninger spaces were then given the structure the theorem needs:
  * `DeningerCircleComplete.lean`, `DeningerCircleCompleteSpace.lean` and
    `DeningerMeyerComplete.lean`, `DeningerMeyerCompleteSpace.lean` prove
    **`DeningerCircle.instCompleteSpace`** and **`DeningerMeyerSource.instCompleteSpace`**, on the
    iterated-derivative uniform-limit theorem `HTGeometry/SmoothUniformLimit.lean`
    (**`contDiff_of_tendstoUniformly_iteratedDeriv`**) and `HTGeometry/PeriodicUniformComplete.lean`;
  * `DeningerFrechetInstances.lean` gives both spaces countably generated uniformities, hence
    **`IsCompletelyPseudoMetrizableSpace`**;
  * `DeningerCircleSeparating.lean` proves the `C^r` family **separates points**
    (`DeningerCircle.seminorms_separating`), hence `T₂`, hence
    **`deningerPeriodizationLM_isClosed_ker`**: `K_p` is closed, so it is itself a Fréchet space;
  * `DeningerTomographyProduct.lean` assembles **`deningerTomographyLM`** — `(3)` between the
    *topologised* spaces — with `deningerTomographyLM_continuous`, `deningerTomographyLM_injective`,
    and **`deningerEscapeSource_mem_ker`**: the escape family stays inside `K_p`, because
    periodization turns the translation into a rotation.
  The conclusion is `DeningerTomographyRangeNotClosed.lean`:
  **`deningerTomography_not_continuous_symm`** (the tomogram of the escape family tends to `0` in
  the countable product while its Meyer seminorm `q_{1,0}` stays above `‖ψ(0)‖ > 0`) and
  **`deningerTomography_not_isClosed_range`** — for every infinite prime set `Q` and every auxiliary
  period `p`, the range of `𝒫_Q : K_p → ∏_{q ∈ Q} C^∞(ℝ/L_qℤ)` **is not closed**.  That is `(11)`.
- **§5's transport corollary `(20)`--`(25)` is proved unconditionally** —
  `formal/GaloisForLFunctions/RHTower/Deninger/DeningerStrongLogEulerGreenTransport.lean`.  The corpus's
  half-density seminorm `p_{1/2}` and its quotient `p̄_{1/2}` live on
  `DeningerMeyerStrongLogTarget`, so the Euler defect and its Green inverse are built there:
  `deningerMeyerStrongLogDecay_tendsto_zero_atTop` (all-weight decay at `+∞`),
  `deningerMeyerStrongLogDecay_eq_zero_of_periodic` (a periodic all-weight cochain vanishes),
  `deningerStrongLogDefect` (`Δ_L = 1 - T_{-L}`) and **`deningerStrongLogDefect_injective`**, hence
  **`deningerStrongLogGreen`**, the Green inverse `G_L : K_L ≃ H`.  Then
  **`deningerStrongLogRelativeSeminorm`** is `(20)`, `r_L = p̄_{1/2} ∘ G_L`, and
  **`deningerStrongLogRelativeSeminorm_defect`** is `(21)`, `r_L(Δ_L g) = p̄_{1/2}([g])`.  The four
  listed consequences follow: `deningerStrongLogRelativeSeminorm_boundary` kills `B_p`;
  `deningerStrongLogDefect_centeredFlow` and
  **`deningerStrongLogRelativeSeminorm_centeredFlow`** give `r_L(V_a h) = r_L(h)`;
  **`deningerStrongLogRelativeSeminorm_independent`** shows the value does not depend on the
  auxiliary period; **`deningerStrongLogRelativeSeminorm_eq_zero_setOf`** is `(22)`, the radical
  transported through `G_L`.  Finally
  **`norm_xiSupportEvaluation_le_strongLogRelativeSeminorm`** is `(23)`: every critical actual Xi
  evaluation is bounded by `r_L`, so `r_L` is not the zero seminorm.  `(24)`--`(25)` are the
  conjunction of that with §3's `deningerTomography_not_isClosed_range`.
- Superseded note, kept for the record: `log q → ∞` along an infinite prime set,
  so the zeros `2π/log q` are distinct and accumulate at `0`; the identity theorem for the entire
  `ĥ` then gives `ĥ ≡ 0`, and matching `ĥ(2πξ)` with mathlib's `𝓕 h ξ` gives `h = 0` by Fourier
  injectivity.  Both analytic inputs — entirety and the lattice vanishing — are now in place.
- `(9)`--`(10)` and the nonclosed-range / weight-zero classification, which are statements about the
  product Fréchet topology and quotients by `𝒫_Q(B_p)`.

## Gates

- [x] 0 → 1 in-progress: tomography and instability falsifiers fixed
- [x] 1 → 2 fully-proven: dependency-closed proofs `(5)`--`(25)`
- [x] 2 → 3 formalized: `(1)`, `(2)`, `(5)`--`(14)`, `(16)`--`(17)` and `(20)`--`(25)` all proved
  unconditionally, including the Fréchet open mapping theorem the non-closed range needs.  Axiom
  audit throughout: `propext, Classical.choice, Quot.sound`.  `(26)` remains explicitly open, as the
  card states.
- [ ] 3 → 4 publication-ready

## Log

- 2026-08-12 — Formalized §5's transport `(20)`--`(25)`: the Euler defect and Green inverse on the
  all-weight logarithmic target, and the half-density quotient seminorm carried through it.  Card
  moved to stage 3.
- 2026-08-12 — Built the Fréchet open mapping theorem and the completeness, metrizability and
  Hausdorff structure of both Deninger spaces, then proved §3's corollary: the cofinal prime
  tomography restricted to `K_p` has non-closed range.  Only §5's transport remains.
- 2026-08-08 — Proved cofinal prime-periodization tomography, finite-family failure, ordinary
  product non-strictness, and compact-orbit Tate-weight obstruction. Corpus audit identified the
  existing half-density seminorm, localized it exactly by the Euler Green inverse, and moved the
  hard frontier to relative closedness `(26)` plus polarized all-divisor admission.
