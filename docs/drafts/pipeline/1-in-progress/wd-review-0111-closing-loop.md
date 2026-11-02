# Route WD closing loop (review-0111 todo, blocks 1–7)

- **ID:** wd-review-0111-closing-loop
- **Stage:** 1-in-progress
- **Type:** CONJECTURE LOOP + THEOREM (paper, block 2)
- **Source:** docs/reports/review-0111/route-WD.md (blocks 1–7); frontier map §WD; obstacles B17, B20–B25.
- **Statement:** Work the seven WD blocks in order; formalize every positive survivor.

## Block status

| Block | Status | Lean |
|---|---|---|
| 1 arithmetic input on the conjugate-diagonal side | open; the object is now explicit: the window energy `|𝒵(t)|²` (Thm 3, 8) | — |
| 2 certificate format | paper proof below (Bessel–Szegő certificate) | items 1–9 formalized: `SzegoCollision/{WindowEnergyLaplace,BesselSzegoCertificate,BesselCepstrumEnergy}`; open: item 10 (centered-theta/log-stage specialization, needs theta-zero→ξ-zero transfer) |
| 3 averaged rung `o(log U)` | open | — |
| 4 height uniformity | open | — |
| 5 corridor rung | open; ⟺ certificate at log stage (Cor 10) | — |
| 6 shallow zeros | open | — |
| 7 closing step | open | — |

## Block 2 — the Bessel–Szegő certificate

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
10. **Log-stage certificate.** At `n=logDoorStage c m`, `η≍1/log m`, `D≲log m` give
    `K(m)≍log m·log log m`; corridor ⟹ `F_{K(m)}` certifies every window from `m₀` on, and
    conversely (item 9 + `logStage_sqrtPrefix_szego_iff_invLog_corridor`). Needs the transfer
    "ξ-corridor ⇒ `2δ*(Z_N)≤g−η`" (theta zeros within `e^{−cm/log m}` of ξ zeros: min-modulus of
    the peeled cofactor, as in `exists_prefix_zero_in_ball_of_xi_zero`).
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

## Gates
- [x] 0 → 1  blocks fixed; block 2 attack fixed
- [x] 1 → 2  block 2 paper proof (items 1–9, 11)
- [ ] 2 → 3  block 2 Lean
- [ ] blocks 1, 3–7

## Ledger (conjecture loop)

| # | Block | Conjecture | Verdict | Insight |
|---|---|---|---|---|
| 1 | 2 | Re(FΛ)>0 is a quadratic form of the Hermite–Hankel matrix of centered moments | refined | the moment Hankel series diverges at the needed scale (`|z−mid|>½−c`); the convergent form is the Laplace/Bessel energy of `𝒵` (item 8) |
| 2 | 2 | canonical outer multiplier has a zero-free closed form in theta data | proved (7, 8) | cepstrum = alternating Bessel transform of `|𝒵|²` |
| 3 | 2 | a certificate cheaper than the cepstrum exists | refuted (11) | rigidity up to Carathéodory factors |
