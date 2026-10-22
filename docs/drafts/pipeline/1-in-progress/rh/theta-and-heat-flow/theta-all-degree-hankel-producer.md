# Actual theta source: all-degree Hankel producer

**Target:** Prove `Σᵢⱼ aᵢaⱼ M_(i+j) >= 0` for every finite real polynomial, where `Σ M_k t^(2k) = -Xi'(t)/(t Xi(t))` is derived from the actual theta density. The all-order moment identities and RH landing are closed. Degree one is closed by `ThetaGibbsSteinSourceMinor`; arbitrary degree is open.

## Candidate mechanisms under direct attack

1. **Atomwise source induction.** Extend the exact exponential-polynomial Stein method to the connected moment forms. Test whether the first theta atom is itself Hankel-positive beyond degree one and whether the existing uniform multiplicative tail enclosure preserves the relevant small eigenvalues. A failure must retain the full arithmetic theta tail rather than discard it by absolute comparison.
2. **Connected expansion.** The corpus's all-order hard-exclusion cumulant law collapses every nondiscrete partition and leaves a signed factorial times a positive product. Seek an actual source incidence with this property, or identify the nonvanishing connected terms that prevent it. Positivity of the raw theta density alone does not establish the required cumulant sign.
3. **Source Schur induction.** The vacuum/Feshbach identity isolates the next quadratic remainder after a positive block. Seek an integration-by-parts identity that expresses this remainder as a positive source norm at every degree. Reasserting positivity of the remainder as a hypothesis is not progress.
4. **Stability-preserving source representation.** The corpus's finite Ising/FK expansion gives positive synchronized-cluster representations. A useful application must construct the actual theta source in a class preserving the entire logarithmic-moment cone; arbitrary positive mixtures do not supply that property.
5. **Denominator-cleared source Gram comparison.** Put `F(q)=Σ c_j q^j`, `c_j=(-1)^j μ_j/(2j)!`, with `μ_j` the normalized full-source even moments. Clearing both factors of `F` from the Hankel generating kernel gives `B(q,r)=-2(qF'(q)F(r)-rF'(r)F(q))/(q-r)`. Its sign-adjusted coefficient matrix has entries `B⁺_ij=2Σ_(k≤min(i,j))(i+j+1-2k)μ_(i+j+1-k)μ_k/((2(i+j+1-k))!(2k)!)`. Compare it with the positive raw-source Gram matrix `D⁺_ij=μ_(i+j+1)/((2i+1)!(2j+1)!)`. Their first rows agree. Seek a source-derived positive operator realizing `B⁺` in this Gram space. Neither positive entries nor a bound above by `D⁺` proves the required lower bound. The all-rank operator comparison is under investigation; numerical finite-shell tests are diagnostics only.

## Evidence rules

All conjectures require source-specific proof or a concrete failure before pivoting. Exploratory high-precision calculations run only on the authorized Runpod and do not enter Lean as premises. Finite-degree checks do not prove the universal quantifier. No route is retired without a proved positive survivor.

## Conjecture tests and pivots

**Conjecture: the first atom supplies a positive foundation in every degree.** Independent direct-density and Ward-integral computations contradict it at degree 3. Its scaled Hankel matrix has smallest eigenvalue approximately `−4.678667293e−5`. The degree-3 monic Schur test is negative. These are numerical findings, not formal sign certificates.

**Pivot: include the second atom as a fixed positive foundation.** It passes the tested degrees 1–11 but fails at degree 12, with smallest eigenvalue approximately `−2.163911252e−18`. The third atom restores that tested block. The direct-density calculation at 160 digits and the independent Ward calculation at 220 digits agree in their displayed 45-digit results. Thus this fixed-prefix replacement also lacks the proposed all-degree property. No conclusion about every finite cutoff follows from the experiment alone.

**Conjecture: the lost source boundary cancellation is visible as an exact leading Fourier term.** Proved in Lean, without computations. For every nonempty finite prefix `P_N`, set `s_N=P_N'(0)>0` and `C_f(t)=integral_0^infinity f(x)cos(tx)dx`. Then `t² C_(P_N)→−s_N`, `t² C_(Phi)→0`, and `t² C_(Phi−P_N)→s_N`. The omitted tail restores the complete opposite leading term. [Exact theorem and proof scope](../../../3-formalized/theta-finite-shell-fourier-boundary.md).

**Pivot toward the producer:** retain the full arithmetic tail before attempting a positive decomposition, or prove a joint cutoff/degree estimate that controls the nonlinear logarithmic-moment transform and its small eigenvalues. Neither an entrywise raw-moment bound nor the existing fixed factor `3005/2997` establishes this by itself. Exact cancellation is now available, but its remaining sign is not proved.

The connected-partition and Ising/FK mechanisms remain unconstructed for the actual density. The source Schur identity isolates the required remainder but gives no sign. None is labelled a successful producer or a formally retired route.

**Conjecture: the cleared kernel is the literal odd-monomial source Gram matrix.** The row indexed by `1` would force `(2n+7) μ_(n+3) = 3(2n+5) μ_1 μ_(n+2)` for every `n`. This bounds all subsequent raw moment ratios by `3 μ_1`. But positivity of the complete source on every positive interval supplies geometric lower moment bounds with arbitrarily large bases. Lean proves that consecutive raw moment ratios tend to infinity, as well as the exact row difference and its eventual strict positivity. Hence this literal identification is impossible. This rules out that representation, not the Hankel route or other source-derived Gram representations. [Exact scope and positive survivor](../../../5-failed/theta-literal-odd-gram-identity.md).

**Pivot: a positive contraction in the odd source Gram space.** Runpod diagnostics of the generalized `B⁺/D⁺` spectrum retain the full stored six-shell density approximation, rather than testing a fixed first-atom foundation. Through degree 12 the tested eigenvalues lie in `[1.2447e-19,1]`; the upper bound also survives in the first- and second-shell examples with negative lower eigenvalues. Thus upper domination cannot be used as the missing positivity producer. The infinite-source lower bound remains open.

## Current mathematical result

No all-degree producer has been proved. Actual full-source degree-one Hankel positivity remains closed; quadratic and higher arbitrary tests remain open. Unconditional source results include exact Fourier boundary compensation across **every** finite theta-shell cutoff, and divergence of consecutive full-source raw moment ratios. The latter gives an eventual strict row deficit that excludes the literal odd source Gram identification. Neither theorem supplies the full Hankel sign. [Fixed-prefix computation](../../../2-fully-proven/computations/theta-all-degree-source-2026-09-06/REPORT.md); [Gram comparison, witnesses, and limitations](../../../2-fully-proven/computations/theta-source-gram-comparison-2026-09-06/REPORT.md).

`ThetaRawGramGrowthObstruction` passes scratch and source checks, its named leaf build, and formal lint; its six audited conclusions use only `propext`, `Classical.choice`, and `Quot.sound`. It is wired into `RHTower.lean`, and the corpus index is refreshed. No umbrella build or numerical premise is used. All processes started for these Lean checks and Runpod calculations have completed.
