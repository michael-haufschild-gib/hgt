# Near-line zero density, almost-all Bessel–Szegő window certificates, and the mollified log-mean

- **ID:** wd-near-line-density-bessel-certificate-and-log-mean
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `docs/reports/review-0211/obstacles-summary.md` §2.5.3 (Obstacles B16, B44)
- **Statement:** $\mathbb E_{[T,2T]}\log|\zeta M_S|=o(1)$ is unconditionally equivalent to $100\%$ critical-scale clustering, not to log-free density $(D_{\mathrm{zero}})$; almost-all `logDoorStage` Bessel–Szegő certificates are unconditionally equivalent to log-free window occupancy $(D_{\mathrm{win}})$; $(D_{\mathrm{zero}})\Rightarrow(D_{\mathrm{win}})\wedge(L)$, and no other implication among $(D_{\mathrm{win}})$, $(D_{\mathrm{zero}})$, $(L)$ holds at the level of RvM + $68\%$ simple critical zeros + arbitrary-rate Selberg density.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven
- [x] 2 → 3  formalized: modules below, `lake --old env lean` exit 0, axioms `propext`, `Classical.choice`, `Quot.sound` only

## Lean modules
- `formal/GaloisForLFunctions/ConjugateDiagonalGeometry/NearLineLogMean/ClusteringLogMeanAndMollifierEquivalence.lean`
- `formal/GaloisForLFunctions/ConjugateDiagonalGeometry/NearLineLogMean/NearLineDensityBesselCertificateAndSeparation.lean`

## Definitions
- $(D_{\mathrm{zero}})$ `LogFreeNearLineZeroDensity`: $\exists\varepsilon\to0$, $\forall A>0$, eventually $\sum_{z\in\mathrm{shellZeros}(V,2V),\,|\operatorname{Re}z-\frac12|\ge A/\log V}m_z\le\varepsilon(A)V$.
- $(D_{\mathrm{win}})$ `LogFreeNearLineWindowOccupancy`: $\exists\delta\to0$, $\forall A>0$, eventually $\#\{m\in[\lceil V\rceil,\lfloor2V\rfloor]:\exists\rho\in\mathrm{burnolUnitXiZeros}(m),\,|\operatorname{Re}\rho-\frac12|\ge A/\log V\}\le\delta(A)V$.
- $(\mathrm{Cert}_{\mathrm{alm}})$ `AlmostAllLogStageBesselCertificate`: $\exists\eta$, $\eta(c)\to0$ as $c\to0^+$, such that for each $c>0$ eventually at most $\eta(c)V$ windows fail `HasLogStageBesselCertificate c m` (order-$K$ certificate at `logDoorStage c m`, all $N\ge$ `doorSqrtPrefix m`).
- $(L)$: $T^{-1}\int_T^{2T}\log|\zeta(\frac12+it)|\,dt\to0$.

## Theorems

**T1 (8-way equivalence)** `criticalClustering_logMean_mollifier_hecke_tfae` ($0<c<\frac12$, $M>1$, finite $S$). Equivalent: (1) $(L)$; (2) $T^{-1}\int_T^{2T}\log|\zeta M_S|\to0$, $M_S=\prod_{p\in S}(1-p^{-s})$ (`eulerProductMollifier`); (3) linear-mollifier outer law for $\zeta\Psi_M$; (4) $T^{-1}\sum_{z\in\mathrm{shellZeros}(T,2T),\operatorname{Re}z>\frac12}m_z(\operatorname{Re}z-\frac12)\to0$; (5) $\forall\kappa>0$: $\mathrm{offLineCountBeyond}(\kappa/\log V,V)=o(V\log V)$; (6)–(8) $o(\log U)$ dyadic means of `unitWindowDepthCharge`, `heckeDefect`, `polynomialThetaSourceMomentReading`.

*Proof.* (1)⇔(4): two-sided all-heights Littlewood budget $|\int_T^{2T}\log|\zeta|-2\pi\sum m_z(\operatorname{Re}z-\frac12)|\le C+K\log 2T$ (`exists_zetaLine_littlewood_edge_budget_all_heights`). (1)⇔(2): $|\int_T^{2T}\log|M_S(\frac12+it)||\le C_S$ by Mercator expansion and $|\int_T^{2T}\cos(tk\log p)|\le 2/(k\log p)$ (`exists_abs_window_logIntegral_eulerProductMollifier_le`). (5)⇒(4): split at $\kappa/\log2T$ and $R/\log4T$; shallow band $\le4C_{\mathrm{tot}}\kappa T$ (`stripFinsetPos_orderSum_le_mul_log`), moderate band by (5), deep band $\le Be^{-R/28}T+K\log^2 4T$ (`exists_dyadic_offLineTailMoment_le_exp`). (4)⇒(5): dyadic telescoping. (5)⇔(6)⇔(7)⇔(8): `dyadicMean_corridor_and_polynomialTheta_littleO_log_up_to_half_tfae`. $\square$

**T2 (certificate ⇔ occupancy)** `almostAllLogStageBesselCertificate_iff_nearLineWindowOccupancy`: $(\mathrm{Cert}_{\mathrm{alm}})\Leftrightarrow(D_{\mathrm{win}})$.

*Proof.* (⇐) at $A=1/(64\min(c,\frac1{64}))$, a window with all zeros within $A/\log V$ has every enclosed zero of $A_N$ within $\frac1{8n}$ of the line (zero transfer at `exists_logStage_tail_lt`), so `besselSzegoCertificate_mul_loop_pos` applies. (⇒) at $c=\min(\frac18,\frac1{8A})$, a deep zero produces a zero of $A_{N_0}$ in the Zhukovsky band, forcing Fredholm index $\ge2$ on a window $m'$ with $|m'-m|\le3$; each failure accounts for $\le7$ windows. $\square$

**T3** `logFreeNearLineZeroDensity_implies_windowOccupancy_and_logMean`: $(D_{\mathrm{zero}})\Rightarrow(D_{\mathrm{win}})\wedge(\mathrm{Cert}_{\mathrm{alm}})\wedge$ T1(5) (hence all of T1). Each deep zero lies in $\le7$ Burnol windows; edge shells contribute $O(\log V)$; dyadic telescoping gives (5).

**T4 (second-moment converse)** `logFreeNearLineZeroDensity_of_windowOccupancy_and_sqMoment`: $(D_{\mathrm{win}})$ plus $\sum_{m\in[V,2V]}N_m(1,V)^2\le M_2V$ implies $(D_{\mathrm{zero}})$, by Cauchy–Schwarz over bad windows: $\sum_{B_A}N_m(A,V)\le\sqrt{\delta(A)M_2}\,V$.

**T5 (Planck windows for $\zeta$)** `planckWindow_nearLine_zeroFree_volume_le`, `planckWindow_nearLine_zeroFree_volume_le_fixed`: for $0<r<1$ there are $C_r,\kappa_r>0$ such that eventually, for $2\le A\le\kappa_r\log V$, $0<B\le\log V$,
$$\operatorname{vol}\{t\in[V,2V]:\exists\rho,\ \xi(\rho)=0,\ t\le\operatorname{Im}\rho\le t+\tfrac{B}{\log V},\ |\operatorname{Re}\rho-\tfrac12|\ge\tfrac{A}{\log V}\}\le C_rB\,\tfrac{e^{-rA}}{A}\,V.$$
*Proof.* Arbitrary-rate Selberg density (`exists_selberg_arbitraryRate_nearLine_zeroDensity`) at rate $r'=\frac{r+1}2$, reflection symmetry, and short-shell caps bound deep multiplicity in $\mathrm{shellZeros}(V-4,2V+4)$ by $C_d\frac{e^{-rA}}AV\log V$ (`deepExtendedShell_orderSum_le`); each zero blocks $t$-measure $B/\log V$. $\square$

**T6 (double-log certificate for $\zeta$)** `almostAll_doubleLogStage_besselSzegoCertificate`: for $0<c<\frac1{48}$, eventually all but $C_cV/\log\log V$ windows $m\in[\lceil V\rceil,\lfloor2V\rfloor]$ satisfy the explicit certificate at `doubleLogDoorStage c m` $=\max(6,\lceil c\log(m+5)/\log\log(m+64)\rceil)$ for every $N\ge$ `doorSqrtPrefix m`. Proof: T5 at $A\asymp\log\log V$ plus zero transfer.

**T7 (separation, no-go)** in the abstract class `UnitWindowStripZeroModel` (reflection symmetry, local RvM $|\#Z_m-\frac{\log m}{2\pi}|\le C$, $\ge\frac{17}{25}$ simple critical zeros, arbitrary-rate Selberg density for every $0<r<1$):
- `exists_clusteredPacketModel_cert_not_zeroDensity_not_logMean`: $\lfloor\log m/52\rfloor$ pairs at $\frac12\pm v_2(m)/(2\log m)$ when $1\le v_2(m)\le\frac18\log m$: $(D_{\mathrm{win}})$ holds with $\delta(A)=6e^{-A}$, while $(D_{\mathrm{zero}})$ and $(L)$ fail.
- `exists_sparseUniformModel_logMean_not_cert`: one pair at $\frac12\pm\frac18\log\log m/\log m$ in every window $m\ge256$: $(L)$ and clustering hold, while $(D_{\mathrm{win}})$ and $(D_{\mathrm{zero}})$ fail.

## No-go closure
- **Killing mechanism:** The proposed equivalence $(D_{\mathrm{zero}})\Leftrightarrow(\mathrm{Cert}_{\mathrm{alm}})$ is false: a window can carry $\asymp\log V$ deep zeros at no cost in bad-window count (T7, clustered). $(L)$ does not give certificates: one shallow-deep pair per window spoils every window at $o(V)$ moment (T7, sparse).
- **Strongest positive survivors:** T1 (the exact condition for $\mathbb E\log|\zeta M_S|=o(1)$ is critical-scale clustering), T2 (exact certificate condition is $(D_{\mathrm{win}})$), T4 (exact bridge), T5–T6 (unconditional almost-all certificates for $\zeta$ at Planck and double-log stage).
- **New insight:** the log-mean sees zeros at scale $\kappa/\log V$ for small $\kappa$; window certificates see occupancy at scale $1$; $(D_{\mathrm{zero}})$ is strictly stronger than both and is needed by neither.

## Log
- 2026-11-02 — formalized; promoted from 2-fully-proven.
