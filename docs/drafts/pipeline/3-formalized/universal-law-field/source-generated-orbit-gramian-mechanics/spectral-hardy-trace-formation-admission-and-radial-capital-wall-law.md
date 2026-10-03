# Spectral Hardy-trace formation admission and radial-capital wall law

- **ID:** ULF-SGOGM-3
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source programme:**
  `../../../1-in-progress/universal-law-field/source-generated-orbit-gramian-mechanics/field-programme.md`
- **Orbit-capital parent:**
  `cyclic-heat-orbit-gramian-lyapunov-properness-and-corona-selection-law.md`
- **Recovery-neutrality parent:**
  `split-recovery-formation-capital-monotonicity-functional-equation-neutrality-law.md`
- **Internal uniqueness parent:**
  `../../../../../../formal/GaloisForLFunctions/RHTower/FrequencySectorBlaschkeCompleteness.lean`
- **Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [BRIDGE]`
  `[EXACT SOURCE-ADMISSION CLASSIFICATION] [RH-FACING FINITE-CAPITAL CRITERION]`
  `[LEAN-PROVED] [NOT RH]`

## 1. Purpose

The orbit-Gramian theorem reduces bounded properness to a source factorization `X=WB`. That is
still abstract until the range of `W` can be recognized directly from source data.

For diagonal source generators, the range is an exact Hardy trace space:

\[
 \boxed{
 m(L)v\text{ has finite formation capital}
 \iff
 m|_{\operatorname{spec}L}
 \text{ is the trace of an }H^2(\mathbb C_+)\text{ function}.}
 \tag{HTF.1}
\]

On the Euler shell the spectral set is Hardy-unique. This yields two sharp laws:

1. an exact-time source packet has infinite capital, while a width-`T` average costs exactly `1/T`;
2. the radial defect multiplier `n^(2a)-1` has finite capital exactly at `a=0`.

The second statement is a genuine selection criterion, but not RH: one must still prove that the
literal physical defect is admitted by this source formation.

## 2. Spectral multiplier packets

Use the source pair of `ULF-SGOGM-1`:

\[
 Le_j=\lambda_je_j,
 \qquad 0<\lambda_1<\lambda_2<\cdots\to\infty,
 \qquad v_j\ne0.
 \tag{HTF.2}
\]

For a scalar function `m` on the spectral set `Lambda={lambda_j}`, assume

\[
 \sum_j|v_j|^2|m(\lambda_j)|^2<\infty
 \tag{HTF.3}
\]

and define

\[
 x_m=m(L)v
 :=\sum_jv_jm(\lambda_j)e_j.
 \tag{HTF.4}
\]

For `h in L^2(0,infinity)`, put

\[
 (\mathcal Lh)(z)=\int_0^\infty h(t)e^{-zt}dt,
 \qquad \Re z>0.
 \tag{HTF.5}
\]

Normalize the Hardy norm by

\[
 \|H\|_{H^2(\mathbb C_+)}^2
 ={1\over2\pi}\sup_{x>0}\int_{-\infty}^{\infty}|H(x+iy)|^2dy.
 \tag{HTF.6}
\]

Paley--Wiener gives a unitary Laplace transform

\[
 \mathcal L:L^2(0,\infty)\overset\sim\longrightarrow H^2(\mathbb C_+).
 \tag{HTF.7}
\]

## 3. Main classification

### Theorem 3.1 — Hardy-trace formation law

Let `W` be the source reachability map

\[
 Wh=\int_0^\infty h(t)e^{-tL}vdt.
 \tag{HTF.8}
\]

Then

\[
 \boxed{
 x_m\in\operatorname{Ran}W
 \iff
 \exists H\in H^2(\mathbb C_+),\quad
 H(\lambda_j)=m(\lambda_j)\ \forall j.}
 \tag{HTF.9}
\]

Moreover its endogenous capital is the exact quotient norm

\[
 \boxed{
 q_G(x_m)
 =\min\left\{\|H\|_{H^2}^2:
 H(\lambda_j)=m(\lambda_j)\ \forall j\right\}.}
 \tag{HTF.10}
\]

The minimum is `+infinity` if the interpolation set is empty.

### Proof

The `j`th source coordinate is

\[
 \langle e_j,Wh\rangle
 =v_j\int_0^\infty h(t)e^{-\lambda_jt}dt
 =v_j(\mathcal Lh)(\lambda_j).
 \tag{HTF.11}
\]

Since every `v_j` is nonzero, `Wh=x_m` is equivalent to the interpolation equations in `(HTF.9)`.
Paley--Wiener identifies the control norm with the Hardy norm. The least-control identity from
`ULF-SGOGM-1` then gives `(HTF.10)`. QED.

### Corollary 3.2 — uniqueness turns quotient cost into an intrinsic norm

Assume the spectral set is an `H^2` uniqueness set:

\[
 H\in H^2(\mathbb C_+),quad
 H(\lambda_j)=0\ \forall j
 \Longrightarrow H=0.
 \tag{HTF.12}
\]

Then every admitted multiplier has a unique source history. If `m` itself extends to an
`H^2(C_+)` function, then

\[
 \boxed{q_G(x_m)=\|m\|_{H^2}^2.}
 \tag{HTF.13}
\]

If `m` belongs to the Nevanlinna class, is not in `H^2`, and the spectral set violates the
half-plane Blaschke condition, then

\[
 \boxed{q_G(x_m)=+\infty.}
 \tag{HTF.14}
\]

Indeed, an `H^2` interpolant `H` would make the Nevanlinna function `H-m` vanish on a non-Blaschke
sequence. It would vanish identically, forcing `H=m`, contrary to `m notin H^2`.

## 4. Euler-shell uniqueness

Fix an integer `m>=1` and `sigma>1`. On

\[
 H_{m,\sigma}=\ell^2(A_m),
 \qquad
 \lambda_n=\log n,
 \qquad
 v_n={n^{-\sigma/2}\over\sqrt{S_m(\sigma)}},
 \tag{HTF.15}
\]

the set `log(A_m)` violates the Blaschke condition. It contains

\[
 \log(2^mp)
 \qquad(p\text{ odd prime}),
 \tag{HTF.16}
\]

and

\[
 \sum_p{\log(2^mp)\over1+\log^2(2^mp)}=\infty
 \tag{HTF.17}
\]

because the summand is eventually bounded below by `c_m/p` and Euler proved
`sum_p 1/p=infinity`. The half-plane Blaschke theorem gives `(HTF.12)`.

This is the same prime-log completeness mechanism already formalized in
`RHTower/FrequencySectorBlaschkeCompleteness.lean`. The new use here is formation-capital
reconstruction, not a new zero-uniqueness theorem.

## 5. Exact-time versus averaged packets

For `a>=0`, the exact heat packet has multiplier

\[
 m_a(z)=e^{-az},
 \qquad x_{m_a}=e^{-aL}v.
 \tag{HTF.18}
\]

The function `m_a` belongs to `H^infinity(C_+)` but not `H^2(C_+)`: its boundary modulus is one.
Corollary 3.2 therefore gives

\[
 \boxed{q_G(e^{-aL}v)=+\infty\qquad(a\ge0).}
 \tag{HTF.19}
\]

Now fix `a>=0` and `T>0`. The normalized time-window packet

\[
 x_{a,T}={1\over T}\int_a^{a+T}e^{-tL}vdt
 \tag{HTF.20}
\]

has multiplier

\[
 m_{a,T}(z)
 ={e^{-az}(1-e^{-Tz})\over Tz}
 =\mathcal L\left(T^{-1}\mathbf1_{[a,a+T]}\right)(z).
 \tag{HTF.21}
\]

The Euler-shell uniqueness makes this control the only one. Hence

\[
 \boxed{
 q_G(x_{a,T})
 =\left\|T^{-1}\mathbf1_{[a,a+T]}\right\|_{L^2}^2
 ={1\over T}.}
 \tag{HTF.22}
\]

Exact source time is therefore an infinite-capital boundary. Positive-width temporal formation is
admitted, with a universal reciprocal-width law independent of the window location.

## 6. Radial-defect selection wall

For real `a`, define the radial multiplier

\[
 d_a(z)=e^{2az}-1.
 \tag{HTF.23}
\]

Whenever the packet `x_(d_a)` satisfies `(HTF.3)`, it has finite source-orbit capital exactly at
the neutral value:

\[
 \boxed{
 q_G(x_{d_a})<\infty
 \iff a=0,
 \qquad
 q_G(x_{d_0})=0.}
 \tag{HTF.24}
\]

### Proof

If `a=0`, the multiplier is zero. If `a>0`, every Hardy function satisfies the point-evaluation
bound

\[
 |H(x)|\le {\|H\|_{H^2}\over\sqrt{2x}}
 \qquad(x>0),
 \tag{HTF.25}
\]

under the Laplace normalization. But `|d_a(lambda_j)|->infinity`, so no Hardy interpolant exists.
If `a<0`, then `d_a(lambda_j)->-1`, again contradicting `(HTF.25)`. Theorem 3.1 proves
`(HTF.24)`. QED.

### Corollary 6.1 — one fixed Euler shell covers the critical strip

Let

\[
 a_\rho=\Re\rho-\frac12,
 \qquad 0<\Re\rho<1.
 \tag{HTF.26}
\]

Choose any `sigma>3`. Then

\[
 x_\rho(n)
 ={n^{-\sigma/2}\over\sqrt{S_m(\sigma)}}
  (n^{2a_\rho}-1)
 \tag{HTF.27}
\]

belongs to `ell^2(A_m)` for every such `rho`, because `4a_rho<2` and `sigma-4a_rho>1`. Moreover

\[
 \boxed{
 q_{G_{m,\sigma}}(x_\rho)<\infty
 \iff \Re\rho=\frac12.}
 \tag{HTF.28}
\]

This is parameter-free after choosing one admissible shell temperature `sigma>3`.

### Corollary 6.2 — positive divisor aggregation cannot hide an off-neutral component

Let `(rho_r)` be any finite or countable family in the critical strip, let `w_r>0`, and assume

\[
 T=\sum_rw_r|x_{\rho_r}\rangle\langle x_{\rho_r}|
 \tag{HTF.29}
\]

converges in trace norm. The positive-aggregation law gives

\[
 \boxed{
 \mathcal E_G(T)<\infty
 \iff
 \Re\rho_r={1\over2}\quad\text{for every }r.}
 \tag{HTF.30}
\]

Thus functional-equation pairing, height averaging, and positive divisor completion cannot cancel
the infinite-capital radial wall. Any regularization that does cancel it must use signed or
nonpositive interference and therefore leaves the positive selection mechanism.

## 7. Recovery and functional-equation invariance

Let `A` be an invertible functional-equation transport and `E` a common split recovery embedding.
The recovery-capital theorem gives

\[
 \mathfrak c_{EAW}(EAx_m)=\mathfrak c_W(x_m).
 \tag{HTF.31}
\]

Hence `(HTF.19)`, `(HTF.22)`, and `(HTF.28)` survive every information-neutral packet lift.
Neither functional reflection nor common recovery can turn an off-neutral radial defect into a
finite-capital source formation.

## 8. Exact RH boundary

Equation `(HTF.28)` is not RH. It proves an equivalence between the critical line and finite
capital for one explicit radial multiplier packet. To obtain RH one would need the global source
statement

\[
 \boxed{
 \Xi(\rho)=0
 \Longrightarrow
 x_\rho\text{ is admitted by the literal source formation}.}
 \tag{HTF.32}
\]

Combined with `(HTF.28)`, this implication would force `Re rho=1/2`. Globally over all nontrivial
zeros, `(HTF.32)` is itself equivalent to RH: RH makes every packet zero, while `(HTF.28)` gives the
converse. Nothing in Hardy interpolation, the functional equation, or common recovery proves it.
Installing it as an admission axiom is circular.

The advance is a sharp change of question. The missing result is no longer “find a proper cost” or
“make the functional equation informative.” It is:

> construct one parameter-free global source history before zero specialization, and only then
> prove that its divisor evaluation is the radial packet.

The per-zero admission statement is retired as an RH-equivalent selector. The surviving target is a
single global factorization whose definition does not mention a zero.

## 9. Hostile scope and parent boundary

1. Paley--Wiener, Hardy interpolation, Blaschke uniqueness, and quotient norms are classical.
2. Jacob--Partington--Pott,
   [*Applications of Laplace--Carleson embeddings to admissibility and controllability*](https://arxiv.org/abs/1203.2666),
   already characterize diagonal-semigroup control through weighted Laplace interpolation.
   Haak--Jacob--Pott--Partington,
   [*Admissibility and Controllability of diagonal Volterra equations with scalar inputs*](https://arxiv.org/abs/0803.0897),
   gives a closely related analytic-interpolation control parent.
3. Prime-log Blaschke completeness already exists in the Lean corpus.
4. The new corpus coupling is the exact identification of source-orbit properness with Hardy trace
   admission and the radial finite-capital criterion `(HTF.28)`.
5. A different source formation can have a different admission space; `H^2(C_+)` is forced here by
   continuous `L^2` source time, not declared universal.
6. Positive aggregation cannot regularize an off-neutral component; signed cancellation is a
   different mechanism and cannot be smuggled into a positive defect.
7. A noninjective recovery can erase the radial defect, but the recovery theorem classifies that as
   information loss.
8. No zero of `Xi` is used anywhere in the proof.

- [x] source range classified as a Hardy trace space;
- [x] least capital reconstructed as quotient norm;
- [x] Euler-shell uniqueness dependency closed;
- [x] exact-time/averaged-time wall proved;
- [x] radial finite-capital criterion proved;
- [x] critical-strip packet admission verified for one fixed `sigma>3`;
- [x] recovery/functional-equation neutrality inherited;
- [x] Lean formalization of the new coupling;
- [ ] parameter-free global source factorization preceding `(HTF.32)`;
- [ ] RH consequence.

Lean: every numbered claim (HTF.3)–(HTF.32) is formalized; see the Lean certificate below.

## Lean certificate

- [x] 2 → 3: Lean `GaloisForLFunctions.HTGeometry.SpectralHardyTraceFormation`, `GaloisForLFunctions.HTGeometry.EulerShellHardyTraceFormation`, `GaloisForLFunctions.HTGeometry.CyclicHeatOrbitCost`, `GaloisForLFunctions.HTGeometry.CyclicHeatOrbitAtomicWall`, `GaloisForLFunctions.HTGeometry.CyclicHeatOrbitFormationCapital`, `GaloisForLFunctions.HTGeometry.EulerShellHeatOrbit`, `GaloisForLFunctions.HTGeometry.PaleyWienerHalfPlane`, `GaloisForLFunctions.HTGeometry.HardyLineIsometry`, `GaloisForLFunctions.HTGeometry.LaplaceRayInjective`, `GaloisForLFunctions.HTGeometry.SplitRecoveryFormationCapital`, `GaloisForLFunctions.RHTower.SectorPrimeZeroUniqueness`, `GaloisForLFunctions.RHTower.ZetaXiZeroCorrespondence`, `GaloisForLFunctions.RHTower.EMAnnulusSupply`; `lake env lean` + module build pass; axiom audit `[propext, Classical.choice, Quot.sound]` only

New modules: `GaloisForLFunctions.HTGeometry.SpectralHardyTraceFormation` and `GaloisForLFunctions.HTGeometry.EulerShellHardyTraceFormation`.
They build on the orbit-Gramian modules of the parent card (`GaloisForLFunctions.HTGeometry.CyclicHeatOrbitCost`,
`GaloisForLFunctions.HTGeometry.CyclicHeatOrbitAtomicWall`, `GaloisForLFunctions.HTGeometry.CyclicHeatOrbitFormationCapital`,
`GaloisForLFunctions.HTGeometry.EulerShellHeatOrbit`), on the corpus Paley–Wiener layer (`GaloisForLFunctions.HTGeometry.PaleyWienerHalfPlane`,
`GaloisForLFunctions.HTGeometry.HardyLineIsometry`, `GaloisForLFunctions.HTGeometry.LaplaceRayInjective`), on the split-recovery capital
(`GaloisForLFunctions.HTGeometry.SplitRecoveryFormationCapital`), on the disk Blaschke condition and prime-log divergence of
`GaloisForLFunctions.RHTower.SectorPrimeZeroUniqueness`, and on `GaloisForLFunctions.RHTower.ZetaXiZeroCorrespondence` /
`GaloisForLFunctions.RHTower.EMAnnulusSupply` for the zeros of `ξ`. Both modules are clean under `lake env lean`, build as modules, and the axiom
audit shows only `[propext, Classical.choice, Quot.sound]`.
`H²(ℂ₊)` is `IsHalfPlaneHardy` (holomorphic on `Re > 0`, uniformly `L²` on vertical lines), with the norm (HTF.6) as `hardyNormSq`.
The Nevanlinna class is taken as bounded type, `IsHalfPlaneNevanlinna` (`G₁/G₂`, bounded holomorphic, `G₂` zero-free).
The half-plane Blaschke theorem is proved for bounded holomorphic functions on any shifted half-plane `Re > δ`, `δ ≥ 0`, and an
`H²` function is bounded on `Re > δ` for every `δ > 0`. Corollary 6.2 is proved for `HasSum` in operator norm, which trace-norm
convergence implies. The radial wall (HTF.24) needs an infinite spectrum, as in (HTF.2).

| Claim | Lean declaration |
|-|-|
| (HTF.4) spectral packet `x_m = m(L)v` under (HTF.3) | `HeatSource.spectralPacket`, `HeatSource.spectralPacket_apply`, `HeatSource.memℓp_spectralPacket` |
| (HTF.5)–(HTF.7) Laplace transform, Hardy norm, Paley–Wiener isometry onto `H²` | `laplaceRay`, `hardyNormSq`, `hardyNormSq_laplaceRay`, `hardyNormSq_eq_datum`, `paleyWiener_halfPlane` |
| (HTF.8)–(HTF.9) Theorem 3.1: `x_m ∈ Ran W ⟺ m|_Λ` is an `H²` trace | `HeatSource.heatReachability_eq_spectralPacket_iff`, `HeatSource.spectralPacket_mem_range_iff` |
| (HTF.10) `q_G(x_m) = min{‖H‖²_{H²} : H|_Λ = m|_Λ}`, `+∞` if empty; the minimum is attained | `CyclicHeatSource.orbitCostForm_spectralPacket`, `CyclicHeatSource.exists_hardy_interpolant_eq_orbitCostForm` |
| (HTF.11) `⟨e_j, Wh⟩ = v_j (ℒh)(λ_j)` | `HeatSource.heatReachability_apply_eq_laplace` |
| (HTF.12) uniqueness set; unique source history | `CyclicHeatSource.IsHardyUniquenessSet`, `CyclicHeatSource.heatReachability_injective_of_uniqueness` |
| (HTF.13) `q_G(x_m) = ‖m‖²_{H²}` for `m ∈ H²` | `CyclicHeatSource.orbitCostForm_spectralPacket_of_hardy` |
| (HTF.14) Nevanlinna `m ∉ H²` on a non-Blaschke spectrum: `q_G(x_m) = ∞`; half-plane Blaschke theorem | `IsHalfPlaneNevanlinna`, `eqOn_zero_of_bounded_of_blaschke_divergent`, `CyclicHeatSource.orbitCostForm_spectralPacket_eq_top_of_nevanlinna`, `CyclicHeatSource.isHardyUniquenessSet_of_not_summable`, `norm_le_of_isHalfPlaneHardy_of_lt` |
| (HTF.15)–(HTF.17) Euler shell: `log(2^m p) ∈ log A_m`, Blaschke divergence, uniqueness | `eulerShellSource`, `two_pow_mul_prime_mem`, `not_summable_eulerShell_blaschke`, `eulerShell_isHardyUniquenessSet` |
| (HTF.18)–(HTF.19) `e^{-aL}v = m_a(L)v`, `m_a ∈ H^∞ \ H²`, `q_G(e^{-aL}v) = ∞` | `HeatSource.heatOrbit_eq_spectralPacket`, `HeatSource.summable_expPacket`, `isHalfPlaneNevanlinna_exp`, `not_isHalfPlaneHardy_exp`, `orbitCostForm_heatOrbit_eq_top` |
| (HTF.20)–(HTF.21) `x_{a,T}`, multiplier `m_{a,T} = ℒ(T^{-1}1_{[a,a+T]})`, `x_{a,T} = W(T^{-1}1_{[a,a+T]})` | `HeatSource.offsetWindowPacket`, `offsetWindowMultiplier`, `HeatSource.offsetWindowPacket_apply`, `offsetWindowControl`, `laplaceRay_offsetWindowControl`, `integral_Ioc_expRay`, `HeatSource.offsetWindowPacket_eq` |
| (HTF.22) `q_G(x_{a,T}) = ‖T^{-1}1_{[a,a+T]}‖² = 1/T` | `norm_offsetWindowControl_sq`, `orbitCostForm_offsetWindowPacket_eq` |
| (HTF.23)–(HTF.25) radial multiplier `d_a`; `q_G(x_{d_a}) < ∞ ⟺ a = 0`, `q_G(x_{d_0}) = 0`; point bound `|H(x)| ≤ ‖H‖_{H²}/√(2x)` | `radialMultiplier`, `radialMultiplier_ofReal`, `CyclicHeatSource.orbitCostForm_radialPacket_lt_top_iff`, `CyclicHeatSource.orbitCostForm_radialPacket_eq_zero`, `HeatSource.spectralPacket_radialMultiplier_eq_zero`, `norm_le_hardyNormSq`, `CyclicHeatSource.tendsto_hardy_lam` |
| (HTF.26)–(HTF.28) Corollary 6.1: for `σ > 3`, `x_ρ ∈ ℓ²(A_m)` on the whole strip, explicit coordinates, `q_G(x_ρ) < ∞ ⟺ Re ρ = 1/2` | `summable_criticalPacket`, `criticalPacket`, `criticalPacket_apply`, `orbitCostForm_criticalPacket_lt_top_iff`, `orbitCostForm_criticalPacket_eq_top_iff`, `criticalPacket_eq_zero_iff` |
| (HTF.29)–(HTF.30) Corollary 6.2: `E_G(Σ w_r |x_{ρ_r}⟩⟨x_{ρ_r}|) < ∞ ⟺ Re ρ_r = 1/2 ∀r`; `E_G(|x⟩⟨x|) = q_G(x)` | `orbitDefectCost_criticalAggregate_lt_top_iff`, `CyclicHeatSource.orbitDefectCost_rankOne` |
| (HTF.31) `𝔠_{RW}(R x_ρ) = 𝔠_W(x_ρ) = q_G(x_ρ)` for injective `R` (functional-equation transport + common recovery) | `formationCapital_toSpanSingleton`, `formationCapital_comp_criticalPacket`, `formationCapital_comp_of_injective` |
| (HTF.32) global admission of every `ξ`-zero packet `⟺` RH; equivalently every such packet vanishes | `xi_zero_re_mem_Ioo`, `forall_xi_zero_criticalPacket_admitted_iff_riemannHypothesis`, `riemannHypothesis_iff_xi_zero_re_eq_half` |

## Log

- 2026-10-03 — Lean certificate audited; every numbered claim mapped to a declaration; moved to 3-formalized.
