# The Bessel–Szegő certificate of the Zhukovsky collision loop

- **ID:** wd-bessel-szego-certificate
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** docs/reports/review-0111/route-WD.md block 2; obstacles B17 (sectorial multiplier).
- **Statement:** On every stage-`n` corridor window the collision loop is certified sectorial by an
  explicit zero-free multiplier `exp(2Σ_{k≤K}(1−ρ^{−2k})S_k u^k/k)` whose coefficients are
  alternating Bessel transforms of the source energy `|𝒵_N(t)|²`; at the logarithmic stage this
  certificate holds on all large windows iff `ξ` has an `A/log|γ|` zero-free corridor, and at every
  stage on every window iff RH.
- **Lean modules (`ConjugateDiagonalGeometry/SzegoCollision/`):**
  - `WindowEnergyLaplace`: `ReflectedWindow`, `pairExpSum_eq_normSq`, `pairResolvent_eq_integral`,
    `integrableOn_energy_iff`, `fredholmIndex_eq_zero_of_integrableOn_energy`,
    `integrableOn_energy_of_fredholmIndex_eq_zero`, `prod_pair_conj`.
  - `BesselSzegoCertificate`: `zhukovskyInnerRoot`, `norm_zhukovskyInnerRoot_lt_one`,
    `mul_norm_zhukovskyInnerRoot_le`, `zhukovskyLoop_sub_eq_inner`, `exactSzegoMultiplier`,
    `isDiskUnit_exactSzegoMultiplier`, `exactSzegoMultiplier_mul_loop_eq_pos`,
    `InCorridor.exactSzegoMultiplier_eq_exp`, `szegoCertificate`,
    `InCorridor.szegoCertificate_mul_loop_pos`, `besselI`, `integral_mode_mul_exp_neg_zhukovskyLoop`,
    `InCorridor.integral_mode_pairLogDerivSymbol`,
    `InCorridor.integral_cepstralModeWeight_mul_pairResolvent`.
  - `BesselCepstrumEnergy`: `InCorridor.cepstralCoeff_eq_bessel`,
    `InCorridor.neg_one_pow_mul_cepstralCoeff_eq_nonneg`, `besselSzegoCertificate`,
    `InCorridor.besselSzegoCertificate_mul_loop_pos`, `InCorridor.re_div_exactSzegoMultiplier_pos`
    (rigidity, item 11).
  - `LogStageBesselCertificate`: `centeredThetaWindow`, `centeredThetaExpSum`,
    `centeredThetaWindow_expSum`, `exists_xiZero_near_thetaZero`, `exists_logStage_inCorridor`,
    `logStage_besselSzego_iff_invLog_corridor`, `besselUnitPrefix`, `unitStage_tail_lt`,
    `riemannHypothesis_iff_unitStage_besselSzego`.
  - Audit: all four leaves compile directly; key theorems depend only on `propext`,
    `Classical.choice`, `Quot.sound`.

## Paper proof

### Notation
`n ≥ 6`, `a=(n−1)/(2n)`, `b=1/n`, `c=√(a²−b²)` (`zhukovskyFocal`), `ρ=(a+b)/c=√((n+1)/(n−3))∈(1,2)`
(`zhukovskyRadius`); `(c/2)(ρ+ρ⁻¹)=a`, `(c/2)(ρ−ρ⁻¹)=b`. `J(u)=½+(c/2)(ρu+(ρu)⁻¹)`
(`zhukovskyLoop`), `Re J ≥ g := ½−a = 1/(2n)`. `E(d)=(Re d−½)²/a²+(Im d)²/b²`
(`zhukovskyEllipseForm`).

Window data: finite `Z⊂ℂ`, multiplicities `m_z≥1`, closed under `z↦1−z̄` with `m` invariant.
`D=Σm_z`, `P(x)=Π_{z,w}(x−(z−w))^{m_zm_w}`, `B=P∘J`, `Λ=B²` (`polyZhukovskyLaurentLoop`).
`δ*=max(Re z−½)≥0`, `𝒵(t)=Σ m_z e^{t(z−½)}` — the window exponential sum; for theta data
`𝒵_N(t)=(2πi)⁻¹∮_{∂R} e^{t(z−½)}(−A_N'/A_N)(z)dz` is a contour integral of the source.

### Statements and proofs
1. **Pair energy.** `Σ_{z,w}m_zm_w e^{t(z−w)}=|𝒵(t)|²` (t real). *Proof.* Reindex `w↦1−w̄`:
   `Σ_w m_w e^{−tw}=e^{−t}\overline{Σ_w m_w e^{tw}}`.
2. **Pair real parts.** `Re(z−w)≤2δ*`, attained by the horizontal pair `(z*,1−z̄*)`, whose
   difference is the real number `2δ*`.
3. **Laplace energy identity.** For `Re x>2δ*`: `Σ_{z,w}m_zm_w/(x−(z−w))=∫₀^∞e^{−tx}|𝒵(t)|²dt`.
   *Proof.* `1/(x−d)=∫₀^∞e^{−t(x−d)}dt` for `Re(x−d)>0`; finite sum; item 1.
4. **Abscissa law.** For real `x`: `e^{−tx}|𝒵(t)|²∈L¹(0,∞) ⟺ x>2δ*`. *Proof.* (⇐) `|𝒵|≤De^{δ*t}`.
   (⇒) if integrable at `x≤2δ*`, then for every `y>2δ*` item 3 and `Re(1/(y−d))≥0` give
   `∫e^{−tx}|𝒵|² ≥ ∫e^{−ty}|𝒵|² ≥ 1/(y−2δ*)`, unbounded as `y↓2δ*`.
5. **Energy–index law.** `2δ*<g ⇒` every `E(z−w)>1` (as `|Re d−½|≥a+(g−2δ*)`) ⇒ index `0`.
   `g<2δ*<1−g ⇒ E(2δ*)<1` ⇒ index `≥2m_{z*}²≥2`.
6. **Outer root.** `E(d)>1`: roots `w₁,w₂=1/w₁` of `w²−2((d−½)/c)w+1`, `|w₁|>ρ`. Put
   `α=w₁/ρ`, `a_d=ρw₂` (`|a_d|<1`), `β_d=a_d/ρ²`. On `S¹`:
   `J(u)−d=(cρ/2)(−α)(1−a_du)·\overline{(1−β̄_du)}`; `a_{d̄}=ā_d`.
7. **Exact multiplier.** If every `E(z−w)>1`, with `S_k=Σm_zm_w a_{z−w}^k` (real, `|S_k|≤D²r^k`,
   `r=max|a_d|<1`): `F(u)=exp(2Σ_{k≥1}(1−ρ^{−2k})S_ku^k/k)=Π((1−β_du)/(1−a_du))^{2m}` is holomorphic
   on `|u|<1/r`, zero-free, and `F·Λ=κ²|H|⁴>0` on `S¹`, `H=Π(1−β̄_du)^m`,
   `κ=(cρ/2)^{D²}Π(−α_d)^m∈ℝ∖0`. *Proof.* `Σ_k w^k/k=−log(1−w)`; item 6; conjugation reindexing
   `(z,w)↦(1−w̄,1−z̄)` sends `d↦d̄`, so `Π(1−β_du)^m=Π(1−β̄_du)^m` and `κ=κ̄`.
8. **Alternating Bessel cepstrum.** If `2δ*<g`, then for `k≥1`
   `S_k=(−ρ)^k(c/2)∫₀^∞e^{−t/2}(I_{k−1}(ct)−I_{k+1}(ct))|𝒵(t)|²dt=(−ρ)^k k∫₀^∞e^{−t/2}I_k(ct)|𝒵(t)|²dt/t`,
   `I_j(x)=Σ_i(x/2)^{j+2i}/(i!(j+i)!)`; hence `(−1)^kS_k>0`.
   *Proof.* (i) `(cρ/2)(u−ρ^{−2}u^{−1})/(J(u)−d)=1+α/(u−α)+β/(u−β)=−Σ_{j≥1}a_d^ju^j+Σ_{j≥1}β_d^ju^{−j}`,
   so its `u^k`-coefficient is `−a_d^k`. (ii) Sum with weights and insert item 3 at `x=J(u)`
   (`Re J−2δ*≥g−2δ*>0`); Fubini, dominated by `(cρ)D²e^{−t(g−2δ*)}`. (iii) Fourier coefficients:
   `e^{−tJ(u)}=e^{−t/2}e^{Au}e^{A'/u}`, `A=−ctρ/2`, `A'=−ct/(2ρ)`, so the `u^j` coefficient is
   `e^{−t/2}(−ρ)^jI_j(ct)`. (iv) Collect: `S_k=(−ρ)^k(c/2)∫e^{−t/2}(I_{k−1}−I_{k+1})(ct)|𝒵|²dt`.
   (v) `I_{k−1}−I_{k+1}=(2k/x)I_k` termwise (`1/(i!(k−1+i)!)−1/((i−1)!(k+i)!)=k/(i!(k+i)!)`);
   `|𝒵(0)|²=D²>0`.
   *Reading.* On `[0,τ]`, `|𝒵(t)|²=|Σ_rσ_r t^r/r!|²` with `σ_r` the centered theta moments, so
   `(−1)^kS_k^{(τ)}=ρ^k⟨σ,𝐇^{(k,τ)}σ⟩`, `𝐇_{rs}=∫₀^τ t^{r+s}dμ_k/(r!s!)`, `dμ_k=ke^{−t/2}I_k(ct)dt/t`:
   a positive Hankel form of the centered theta moments. The worst point of the certificate is
   `u=−1` (`J(−1)=g`, nearest the pair differences).
9. **Finite certificate.** `F_K=exp(2Σ_{k≤K}(1−ρ^{−2k})S_ku^k/k)` is entire and zero-free
   (`IsDiskUnit`). If `2δ*≤g−η`, `η>0`: `r≤1−η` (from `(c/2)(R+R⁻¹)≥a+η`, `R−ρ≥2η/c>4η`,
   `ρ<2`, `η≤1/12`), and `2D²(1−η)^{K+1}/((K+1)η)<π/2` gives `Re(F_KΛ)>0` on `S¹`
   (`|arg(F_KΛ)|=|Im(log F−log F_K)|≤2Σ_{k>K}|S_k|/k`). Soundness: any `IsDiskUnit` certificate
   forces index `0` (`fredholmIndex_eq_zero_of_diskUnit_re_pos`).
10. **Log-stage certificate.** Transfer: if `tail(N) < c_good e^{−(m+3)}(r/8)^d` then every theta
    zero of the Burnol window lies within `r` of a ξ zero (peel ξ's window zeros; the cofactor has
    modulus `≥ c_good e^{−(m+3)}/8^d` by minimum modulus; at a theta zero `|ξ| ≤ tail`). With
    `r = 1/(16n)`, `n = logDoorStage c m`, the condition holds for all `N ≥ doorSqrtPrefix m` once
    `15m+13 > L₀ + C_u log(m+5)(L₁+log(m+5))` (uses `log²x ≤ 16√x`). Under the ξ corridor with
    `c = 1/(32A)`: `2(Re z−½) ≤ 2A/log(m−3) + 1/(8n) ≤ 1/(4n) = g_n − η`, `η = 1/(4n)`, as
    `16An ≤ ½log(m+5)+112A ≤ log(m−3)` for `m ≥ e^{1+224A}+3`. Converse: any order `K` with
    `2D²(1−η)^{K+1}/η < π/2` exists, the certificate is a disk unit, and item 3 of
    `logStage_sqrtPrefix_szego_iff_invLog_corridor` gives the corridor.
11. **Rigidity.** Any `F'` continuous on the closed disk, holomorphic inside, zero-free, with
    `Re(F'Λ)>0` on `S¹` equals `F·Ω` with `Re Ω>0` on the closed disk (`FΛ>0`, minimum principle).

### Insight
Block 2 is closed as a format: the certificate class is `{F_K}` — exponentials of a truncated
Bessel transform of the window energy `|𝒵_N(t)|²`, i.e. of a positive Hankel form in the centered
theta moments. Rigidity (11) shows no cheaper certificate exists: every certificate is `F` up to a
Carathéodory factor, and `F` converges on `S¹` exactly when the energy grows at rate `<g`
(items 4, 8). Positivity `Re(F_KΛ)>0` is therefore the stage-`n` corridor, and its arithmetic
input is growth control of `|𝒵(t)|²=𝒵(t)𝒵(−t)` for `t≲K/c` — block 1's object: through the
explicit formula `𝒵(t)` is a short prime sum near `e^t` at height `m`, so the certificate needs
`|Σ_{n≈e^t}Λ(n)n^{−½+im}w(log n−t)|²≤e^{(g−η)t}` for `t≲log m·loglog m`.
12. **Every stage.** Prefix `besselUnitPrefix m S = doorUnitPrefix m S + ⌈√B⌉ + 1`,
    `B = |log(C₀+1)| + |log c_good| + (m+3) + D_m log(128(S+6+2D_m²))`, `D_m = C_u log(m+5)`.
    Then `(N+1)² > B` gives the transfer at radius `1/(16n)` for every stage
    `n = doorUnitStage m S ≤ S+6+2d²`. Under RH every ξ zero has `Re = ½`, so theta zeros satisfy
    `2(Re z−½) ≤ 1/(8n) ≤ g_n − 1/(4n)` and the certificate holds. Conversely a positive certificate
    at `N₀ = besselUnitPrefix m S` gives index `0` there; the stabilization formula
    (`doorUnitStage_spec`) makes the index the same for all `N ≥ doorUnitPrefix m S`, so item 9 of
    `riemannHypothesis_door_opener_tfae` gives RH.
