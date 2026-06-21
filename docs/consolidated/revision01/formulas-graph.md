# Formulas — reduced graph

The 178 formulas of `formulas.md` refactored into a graph of **100 nodes** in **one connected
component, with zero isolated nodes**. Each node is a single formula (or a maximal `⟺`-chain /
restatement family); each edge is a named operation linking two nodes. No new mathematics is
claimed — this is a structural refactor. Every merge and every "cannot merge" verdict is recorded
in `formulas-graph.worklog.md` (the audit trail); the completeness ledger at the foot of this file
maps every F1–F178 to its node (verified: 178 covered exactly once).

- **Reduction:** 178 → 100 nodes (−44%). Biggest collapses: the positivity apex **PA1** absorbs 16
  formulas; the transcendence apex **TA1** absorbs 5; **κ₋-counting PA2**, **zero-power-sums PS-POW**,
  and the involution **IV1** each absorb 4–6.
- **Connectivity:** one component. The only conjectural edge (BR5, Lehmer↔function-field margin) is
  non-load-bearing — every node, including Lehmer, is already joined by mechanical/structural edges.

Merge operations used: `=` same equation; `⊃` special-case/restatement; `⟺` one predicate, many
equivalents; `:=` definition folded into its consumer. Anything introducing a *new object* stays a
node and gets an **edge** instead. Full rule and per-pair verdicts: worklog.

---

## Legend of clusters

`IV` involution/FE · `WD` weld + operator category 𝓜⁺ · `DF` phase-defect & phase-space experiment ·
`CW` off-line curvature window · `PH` Φ_k line curvature · `PA` positivity apex (RH⟺) · `TA`
transcendence/DSS apex · `PS` power-sums/Stieltjes/special values · `ST` statistical/RMT · `CO`
cocycle/coboundary/Koszul/F₁ · `GA` Γ/ψ/χ identities · `FF` Frobenius/function-field · `IN`
inertia (Bezoutian/Schur–Cohn) · `LX` log-ξ exterior calculus · `HD` Hadamard · `HT`
hypertranscendence foundations · `XF` explicit formula · `MS` Maass–Selberg/de Branges · `PE`
period domain · `ML`/`ZP` Lehmer / zero-perturbation.

---

## Nodes

Format: **ID** `canonical formula` ⟵ {absorbed originals}.

### IV — involution & functional equation
- **IV1** `ι:s↦1−s, ι²=id, Fix(ι)={Re s=½}; anti-holomorphic ῑ:s↦1−s̄ same locus` ⟵ {7,8,9,135}
- **IV2** `ξ(s)=ξ(1−s) ⟺ Λ(s)=Λ(1−s) ⟺ θ(1/t)=√t·θ(t) ⟺ Poisson (Ш̂=Ш)` ⟵ {10,11,51}
- **IV3** `ξ'/ξ(s)=−ξ'/ξ(1−s)` (Berry equalization) ⟵ {12}
- **IV4** `Ξ(w):=ξ(½+w), Ξ(w)=Ξ(−w), 𝒟={ρ−½}` ⟵ {13}
- **IV6** `s↦1−s ⟹ p^{−s}↦p^{−1}(p^{−s})^{−1}, i.e. ι_ζ:θ_p↦−θ_p` ⟵ {63,122}
- **IV7** `|p^{−s}|=p^{−½} ⟺ Re(s)=½` ⟵ {97}

### WD — weld & operator category 𝓜⁺
- **WD1** `H=∂_s log Λ=∂_s log Γ∞+ζ'/ζ; carrier M_Ξ=−Ξ'/Ξ=−(arch+prime)` ⟵ {2,69,155}
- **WD3** `ω=d log ξ=H ds (transport 1-form); r*ω=ω ⟺ H(s)=−H(1−s)` ⟵ {1,18}
- **WD2** `σ_p:x_p↦p^{−1}x_p; τ_p:=σ_p−1` ⟵ {16,56}
- **WD4** `⟨1,r⟩=𝔾_a⋊𝔾_m, transverse seam [𝔾_a,𝔾_m]` ⟵ {19,93}
- **WD5** `[∂_s,M_p]=−log p; [∂_s,σ_p]=0` (the two structure brackets) ⟵ {20,65}
- **WD6** `σ_p·e_m=p^{−m_p}e_m` ⟵ {21}
- **WD7** `∂_s=−Σ_p(log p)θ_p ⟹ ∂_s e_m=−(log n)e_m on M_ζ; ∂_s|M_∞=−½logπ+½ψ(s/2)` ⟵ {22,23,94,95}
- **WD9** `Π(S)=(|S|,Σ_{m∈S}m), shift −|S|log p` ⟵ {24}
- **WD11** `f=g·e^{zλ} solves the shift ODE` ⟵ {138}

### DF — phase-defect & phase-space experiment
- **DF1** `Δ=max(log|∂_s logΓ∞|,log|ζ'/ζ|)−log|∂_s logΓ∞+ζ'/ζ|` ⟵ {3}
- **DF2** `true field separated from finite: Δ_{ζ'/ζ}→log2 vs →0; d_transport≥c; co-failure≥c; λ₁ gap≥c` ⟵ {74,75,76,77}
- **DF4** `θ=arg(ζ'/ζ), O=log(1+|ζ'/ζ|); Cov(O,δV)>0; ∫O dθ>c>0` ⟵ {78,79,80}
- **DF5** `σ>1 ⟹ (ζ'/ζ)_N→ζ'/ζ` (control) ⟵ {82}
- **DF6** `K_q(σ,σ')=Corr(𝟙_{Δ(σ+it)>q},𝟙_{Δ(σ'+it)>q})` ⟵ {83}
- **DF7** `ω=dO∧dφ, O=log(1+|ζ'/ζ|), φ=arg(Γ∞+ζ'/ζ)` ⟵ {100}
- **DF8** `‖∂_t arg(Γ∞+ζ'/ζ)‖_{H^{1/2}}` ⟵ {146}

### CW — off-line curvature window
- **CW1** `C_a(τ)=2(a²−τ²)/(a²+τ²)², >0⟺|τ|<a; ∫C_a=0; C_a(0)=2/a²; width≈a/2` ⟵ {5,6,91,147}
- **CW2** `(½−β+iτ)^{−2}+(β−½+iτ)^{−2}=C_a(τ)` (off-line FE-quartet source) ⟵ {40,108}

### PH — Φ_k line curvature
- **PH1** `Φ_k(t)=Σ_ρ(½+it−ρ)^{−k}, k≥2 (= χ_n)` ⟵ {37,50}
- **PH2** `Φ_2(t)=(d/dt)²log ξ(½+it)` ⟵ {36}
- **PH3** `RH ⟹ Φ_2<0 ⟺ (d/dt)²log|ξ(½+it)|<0` ⟵ {38,39}
- **PH3b** *(guardrail)* `Φ_2<0 ∀t is RH-necessary but RH-INsufficient` — converse fails: a far-off-line
  high zero's bounded bump `C_a(0)=2/a²≥8` is drowned by the growing on-line background `|Φ_2|~(log t)²`
  (verified undetected at `γ≈180,260`). So PH3 is one-way; `Φ_2<0` is the low-order **crest shadow** of the
  wall, not the wall. Corrected hierarchy: `Φ_2<0` (necessary crest shadow) ⊊ `D₂(R)=0 ∀R` (local
  source-width confinement) ⟺ `Q_0[p]≥0 ∀p` (global source-aware wall) ⟺ RH.
- **PH4** `χ_n(ρ)/χ_n(1−ρ) n-independent ⟺ β=½` ⟵ {49}

### PA — positivity apex
- **PA1** *(master)* `RH ⟺ κ₋=0 ⟺ Q_W⪰0 (sig (1|∞)) ⟺ FE-polarization⪰0 ⟺ m_ξ∈ℕ₀ ⟺ det H_d≥0 ∀d,t
  (Hankel towers PSD) ⟺ Ω≽Π (‖P̃‖≤1, A_arch−ΣP_p≥0) ⟺ G5 unitary ⟺ uniform Jensen/Laguerre–Pólya
  (#non-real Jensen roots=0) ⟺ supp μ_ξ⊂{Re=½} ⟺ y_ρ>0 / {T_k}_{k≥1} Stieltjes ⟺ all occupation
  centres=½ ⟺ D2=0` ⟵ {41,53,70,81,85,86,87,90,150,152,153,165,169,172,175,177}
- **PA2** `κ₋=#{off-line conj. pairs}=2·#{off-line zeros}; one off-line⟹κ₋=2 (FE-doubling) = Sylvester index` ⟵ {54,68,72,140,141}
- **PA3** `κ₋=APS index; RH⟺Index=0` ⟵ {67}
- **PA5** `Q_W=𝔇, signature (1|∞) / finite-rank (1,ρ−1); V_arch=Reψ` ⟵ {84,164}
- **PA7** `Davenport–Heilbronn: inertia (1,0,10), κ₋=1` ⟵ {101}
- **PA9** `Turán g(n)=a_n²/(a_{n−1}a_{n+1})→1~c/n` ⟵ {176}

### TA — transcendence / DSS apex
- **TA1** *(master)* `corank^{(T)}=∞ ∀T≥2 ⟺ {log p} ℚ-alg-indep ⟺ trdeg=∞ ⟺ DSS ⟺ {γ_n} alg-indep / period field (mod Grothendieck)` ⟵ {32,89,159,168,173}
- **TA2** `corank_ℚ=∞, corank_ff=1, gap=∞−1` ⟵ {25,26,27}
- **TA3** `corank<∞ ⟺ M holonomic` ⟵ {28}
- **TA4** `trdeg≤corank, strict ({π,π²}: 1<2)` ⟵ {29,127}
- **TA5** `dim W=corank; internal fraction T/(N+T)` ⟵ {30,119}
- **TA6** `corank=∞ ⟺ {log p} ℚ-lin-indep ⟺ {m:Σm_p log p=0}={0}` ⟵ {31,134}
- **TA7** `corank=∞ robust: Zariski closure of (p^{−1})_p ∞-dim when Λ=0; rank=card(primes) after adjoining ∂_s` ⟵ {121,137}
- **TA8** `|m·ℓ|≥c_B H(m)^{−κ_B}` (Baker–Wüstholz) ⟵ {145}

### PS — power-sums / Stieltjes / special values
- **PS-POW** `P_k=Σρ^{−k} (=−ξ'/ξ / superzeta coeffs); M_k=Σ(ρ−½)^k (contour, diverges); S_k=Σ(ρ−½)^{−2k}=−k[w^{2k}]logΞ` ⟵ {131,142,151,154,156,174}
- **PS4** `λ_n=−ΣC(n,j)(−1)^j P_j` (Li) ⟵ {132}
- **PS11** `Σ(ρ−½)^{−2k}=2^{2k}−¼(2^{2k}−1)ζ(2k)−2^{2k−2}β(2k)−(2(2k−1)!)^{−1}(ζ'/ζ)^{(2k−1)}(½)` ⟵ {157}
- **PS1** `trdeg_ℚ{Stieltjes(ζ_S)}=corank_ℚ{log p:p∈S}` ⟵ {124}
- **PS2** `c_1=Σβ_p log p` ⟵ {129}
- **PS5** `ℚ({P_k})⊇{ζ(odd)}` ⟵ {133}
- **PS7** `κ_n=ζ(2n+1); κ_2>0,κ_4<0,…` (free cumulants) ⟵ {113,114}
- **PS8** `c_n=Λ(n)≥0` ⟵ {115}
- **PS9** `F^{(T)}(1)=(−1)^TΣC_a∏(log p)^{a_p}` ⟵ {107}
- **PS10** `n₀=πγ/(4δ); c=n₀δ/γ≈π/4` ⟵ {109,110}
- **PS12** `ζ(2k+1)=∫y^k dν (ν≥0); H_FID=[ζ(2(i+j)+3)]⪰0` (unconditional) ⟵ {158,178}
- **PS13** `γ_E∉ℚ` ⟵ {160}
- **PS14** `μ_{2k+1}=Σ(ρ−½)^{−(2k+1)}=0 (FE); D2=0⟺RH` ⟵ {163}

### ST — statistical / RMT
- **ST1** `𝓛(σ) conv a.s. ⟺ Σp^{−2σ}<∞ ⟺ σ>½` ⟵ {42,45}
- **ST2** `Var(Re𝓛)~½loglog; log|ζ(½+it)|/√(½loglog t)⇒𝒩(0,1)` ⟵ {43,44}
- **ST3** `σ_wall=max(½,1/k₀); crossover σ*∈(½,1)` ⟵ {4,149}
- **ST4** `‖ψ_s‖²=ζ(2σ)` ⟵ {47}
- **ST5** `g_F=(logζ)''(2σ)=Var_p(log n)~1/(2σ−1)²` ⟵ {48}
- **ST6** `⟨r⟩=0.611` (GUE) ⟵ {116}
- **ST7** `corr(log margin, gap)=−0.25` ⟵ {118}

### CO — cocycle / coboundary / Koszul / F₁
- **CO1** `C5=weld={one non-CC place}×{CC places}` ⟵ {17}
- **CO2** `a_Γ=s/2π; div=[0]−[∞], deg_ℤ=+1≠0` (arch non-CC) ⟵ {14,15}
- **CO3** `τ_p a_q=τ_q a_p` (additive 1-cocycle) ⟵ {57}
- **CO4** `d1∘d0=0` (Koszul) ⟵ {58}
- **CO5** `additive Euler cocycle = bounded L²-coboundary ⟺ σ≥½` ⟵ {46}
- **CO6** `g_p=g_p^{−1}⟹g_p=±1` ⟵ {52}
- **CO7** `a CC ⟺ a=c·σ(g)/g ⟺ deg_O(a)=0 on every orbit` ⟵ {59,120}
- **CO8** `RH ⟺ arch-completed Koszul acyclic ⟺ ω=0∈H²(G_L)` ⟵ {60,130}
- **CO8b** `ω=0 ⇏ RH` (plain class insufficient) ⟵ {88}
- **CO9** `ρ_∞(s)·ρ_ζ(s)=1` ⟵ {61}
- **CO10** `F₁ ⟺ (D=0)∧(corank finite); over ℚ (D=+1,corank=∞)` ⟵ {126}

### GA — Γ / ψ / χ identities
- **GA1** `Γ_ℝ(s+2)=(s/2π)Γ_ℝ(s)` ⟵ {96}
- **GA2** `ψ(s/2+1)=ψ(s/2)+2/s` ⟵ {136}
- **GA3** `χ(s)=Γ_ℝ(1−s)/Γ_ℝ(s)=π^{s−½}Γ((1−s)/2)/Γ(s/2)` ⟵ {62}
- **GA4** `∂_s log χ=log π−½ψ((1−s)/2)−½ψ(s/2)≠0` ⟵ {64}

### FF — Frobenius / function-field
- **FF1** `e_k(S)=q^k e_k(S^{−1}); ∏(1−ωT) FE-inv; |ω|=√q` ⟵ {111,139}
- **FF2** `polarization ⟺ single Frobenius ⟺ corank=1 ⟺ F_q` ⟵ {55}
- **FF3** `normalized margin=1−q^{−½}` ⟵ {112}
- **FF4** `γ_n^{(q)}=(B_n^+/n!)(log q)^n` (corank-1 collapse) ⟵ {125}
- **FF5** `trdeg(periods)=dim G; dim W=corank=1; ι unitary on Fix ⟺ RH/F_q` ⟵ {128}
- **FF6** `γ_n=n toy: S_k=(−1)^kζ(2k)∈ℚπ^{2k}; π²+6S_1=0; 5S_2=2S_1²` ⟵ {161}

### IN — inertia machinery
- **IN1** `Bezoutian f(s)g(t)−f(t)g(s)=(s−t)Σr_j f_j(s)f_j(t); sigNeg(scForm[f])=winding(f)=#inside(f)` ⟵ {143,144}

### LX — log-ξ exterior calculus
- **LX2** `∮ d arg=2πi(#zeros−#poles); (1/2πi)∮ d log ξ=#zeros` ⟵ {34,148}
- **LX3** `μ_ξ=(1/2π)Δ log|ξ|` ⟵ {35}
- **LX4** `(1/2πi)∮_{∂R}(ξ'/ξ)ds=0 off the line` ⟵ {71}
- **LX5** `φ'(T)=θ'(T)+πS'(T); θ'(T)=½log(T/2π)` ⟵ {98,99}

### HD — Hadamard
- **HD1** `ξ=ξ(0)e^{bs}∏(1−s/ρ)e^{s/ρ}; ξ'/ξ=b+Σ[1/(s−ρ)+1/ρ]` ⟵ {170,171}
- **HD2** `ξ'/ξ(s)~m_ρ/(s−ρ)+h(s)` ⟵ {33,73}
- **HD3** `e^{q((s−½)²)}ξ; (e^q ξ)'/(e^q ξ)=ξ'/ξ+q'` ⟵ {102,103}

### HT — hypertranscendence foundations
- **HT1** `∄ poly F(s,Γ,…,Γ^{(n)})≡0 (Hölder); HT±(D-algebraic)=HT` ⟵ {104,105}
- **HT2** `ζ∉K_B=ℂ(s,{p^{−s}})` ⟵ {92}
- **HT3** `Ĥ Ψ=0` (Wheeler–DeWitt constraint) ⟵ {106}

### Singletons (each its own framework)
- **XF1** `Σ_ρ h(γ_ρ)=arch−Σ_p(log p)…` (explicit formula) ⟵ {162}
- **MS1** `−(φ'/φ)(½+ir)=2[(ξ'/ξ)(1+2ir)−(ξ'/ξ)(2ir)]` ⟵ {66}
- **MS2** `K_MS(s,w)~(1−Θ(s)Θ̄(w))/(s+w̄−1)∈ℕ₀ ⟺ RH` ⟵ {167}
- **PE1** `RH ⟺ F_ζ elliptic, period interior to D_∞=Sp_∞(ℝ)/U(∞)` ⟵ {166}
- **ML** `M(L)=1.176280818` (Lehmer Mahler measure) ⟵ {117}
- **ZP** `dρ/dε=−n^{−ρ}/ζ'(ρ)` ⟵ {123}

---

## Constructed bridge formulas

New formulas built to chain otherwise-separate clusters (the worklog certifies each):

- **BR1** (GA1↔CO2), mechanical, numerically certified to 1e-31:
  `a_Γ(s) = Γ_ℝ(s+2)/Γ_ℝ(s) = s/2π`.
  The archimedean σ-orbit shift multiplier (deg=+1, non-CC) **is** the Γ_ℝ-recurrence ratio — this
  is *why* the archimedean place is the one non-CC place (CO1): its multiplier has div=[0]−[∞].
- **BR2** (IV2→IV3→WD3), mechanical: differentiating the FE gives `ξ'/ξ(s)=−ξ'/ξ(1−s)`, hence `H(s)=−H(1−s)`.
- **BR3** (WD carrier identity), mechanical: `ξ'/ξ = Λ'/Λ + 1/s + 1/(s−1)` (from ξ=½s(s−1)Λ); the
  weld's ξ- and Λ-carriers differ only by this FE-symmetric rational term (justifies the WD1/WD3 merges).
- **BR4** (PH1↔CW1) = node CW2: an off-line zero's FE-quartet contributes exactly `C_a(τ)` to Φ_2.
- **BR5** (ML↔FF3), `[BRIDGE-conj]`, non-load-bearing: `M(L)−1` as the number-field analogue of the
  function-field margin `1−q^{−½}` — "smallest positive excursion of a height above its trivial value."
- **BR6** (GA4↔LX5), mechanical, numerically certified to 1e-31:
  `∂_s log χ(½+iT) = −2·θ'(T)`, where `θ(T)=Im log Γ_ℝ(½+iT)` is the Riemann–Siegel theta.
  On the seam `|χ(½+iT)|=1` and `arg χ(½+iT)=−2θ(T)`, so `d/dT log χ = −2iθ'(T) = i·∂_s log χ`, giving the
  identity. The digamma asymptotics of GA4 (`Re ψ(¼+iT/2) ~ log(T/2)`) reproduce LX5's `θ'(T) ~ ½log(T/2π)`
  — so the **exact** GA4—LX5 identity upgrades the asymptotic-only GA1—LX5 edge: the Riemann–Siegel theta
  derivative *is* `−½ ∂_s log χ` on the critical line, the archimedean phase whose count gives `N(T)`.
  *(Significance: housekeeping — exact but classical, and GA4/LX5 already sit adjacent in the archimedean
  backbone, so it adds no new connectivity.)*
- **BR7** (PH2↔LX3), cross-cluster, numerically certified to 1e-28: the 2D harmonicity of `log|ξ|`
  (`= Re log ξ`, holomorphic off zeros) gives `Re Φ_2 = Re(log ξ)''(½+it) = ∂²_σ log|ξ| = −∂²_t log|ξ|`
  and `Δ log|ξ| = ∂²_σ log|ξ| + ∂²_t log|ξ| = 2π·μ_ξ` (LX3: `0` off zeros, a `δ` at each zero). This ties
  the **line-curvature** node PH2/Φ_2 to the **source-measure** node LX3 across the PH↔LX clusters, and
  re-reads PH3 (`RH ⟹ Φ_2<0`, log|ξ| concave along the line) as a **geometric** statement: under RH the
  critical line is a **crest/ridge of `log|ξ|`** — concave along the line (`∂²_t<0`), convex across it
  (`∂²_σ>0`). The **converse** (`Φ_2<0 ∀t ⟹ RH`) is *not* given by harmonicity; it reduces to the CW
  window — whether an off-line zero's positive bump `C_a(τ)` (CW1/CW2) always beats the on-line
  background — so BR7 also edges PH2—CW2. **Resolved numerically: the converse FAILS.** The bump is bounded
  (`C_a(0)=2/a² ≥ 8` for `a≤½`) while the on-line background `|Φ_2|` grows like `(log γ)²`, so a
  far-off-line zero is swamped at height (an `a=0.45` quartet is undetected at `γ≈180,260`). Hence
  `Φ_2<0 ∀t` is **necessary but not sufficient** for RH — RH-blind to far-off-line zeros (like the
  forward/secular Hankel), unlike the *faithful* reciprocal-Hankel `Q_0` (obstruction `Im y`, fixed sign
  at all heights). *(Significance: insight-bearing — rules the line-curvature chart out as a sufficient
  certificate with a verified blind spot, reinforcing why the bridge uses the reciprocal-Hankel; posted
  to #research, folded into bridge-theorem §4.)*
- **BR8** (IV4↔PS14), load-bearing, numerically certified: the even FE-orbit symmetry `Ξ(w)=Ξ(−w)` (IV4)
  makes the divisor `{w=ρ−½}` invariant under `w↦−w`, so **every odd-power moment vanishes identically** —
  `Σ_{±w} w^{−(2k+1)} = 0` (PS14: `μ_{2k+1}=0`) and likewise `Σ_{±w} w^{2k+1}=0` (M-side) — while the even
  ones `S_k=Σ w^{−2k}` survive (verified: `Σw^{−1,−3,−5}=0`, `Σw^{−2,−4}≠0`). This is **why the bridge
  coordinate is the reciprocal-*squared* `y=−w^{−2}`**: `w^{−1}` carries no information, so the first
  informative reciprocal moment is `w^{−2}`. Together with id939 (the centre `½` is the unique
  FE-folding/positivity centre) and the positivity sign (`w=iγ ⟹ −w^{−2}=γ^{−2}>0`), the coordinate
  `y_ρ=−(ρ−½)^{−2}` is **triply forced**: centre by FE-folding, power `−2` by parity, sign by on-line
  positivity. *(Significance: moderate/load-bearing — mechanism elementary (parity), but it joins IV4↔PS14
  with no prior edge and grounds the bridge's foundational coordinate choice, completing id939.)*
- **BR9** (seam-split form ↔ signature: WD1/Formula-155 ↔ PA5/IN1), numerically certified: the weld split
  `Ξ'/Ξ=A+P`, `S_k=−[w^{2k−1}](A+P)` (WD1, Formula 155) lifts to a **form-level** decomposition of the
  positivity apex. The reciprocal-Hankel `[T_{i+j+1}]` (PA1, source-aware `Q_0`) splits as `Q_arch+Q_prime`
  with `T^A_k=(−1)^kS_k^A`: the **archimedean Hankel has signature exactly `(d,1)`** — one negative
  direction (the `s=0,1` pole, `S_k^A=2^{2k}` ⟹ rank-1 negative `−4·uu*`, `u_i=(−4)^i`), the prime Hankel
  indefinite, the sum PD. So the `(2γ_1)^{2k}`-deep seam cancellation (Formula 156) is **rank-1** (the
  pole), and the arch `(d,1)` signature is the **finite-`d` shadow of the Weil/Hodge index `(1,∞)`/`(1,ρ−1)`
  carried by PA5/IN1** — directly edging the weld/seam-split (WD1, PS-POW) to the signature node. *(Proof
  shape: deflate the rank-1 pole, prove the residual PSD.)*

---

## Edges (adjacency)

Intra-cluster edges follow the chains above; cross-cluster edges below make the graph connected.
Notation `A—B (op)`.

**The two apexes and their satellites.** PA1 collects only *positivity/spectral* RH-equivalents;
RH-characterizations from other frameworks orbit it as edged satellites (merging them would erase
their own supporting structure and bury the caveat CO8b):
- PA1—PA2 (κ₋ value) —PA3 (APS) —PA5 (Q_W defn) —IN1 (signature=root count) —PA7 (DH witness) —PA9 (Turán≺LP).
- **WD1/PS-POW—PA5 (BR9: arch/prime form split of Q_0; arch Hankel sig (d,1) = rank-1 pole = finite-d shadow of Weil/Hodge (1,∞)/(1,ρ−1))**.
- PA1—CO8 (Koszul/ω, *with* caveat CO8b: ω=0⇏RH) —MS2 (de Branges) —PE1 (period domain) —FF5 (FF/ι-unitary) —LX2 (zero count) —LX3 (μ_ξ support) —HD3 (surrogate→Jensen) —PH3 (Φ_2<0) —ST7 (margin↔gap) —PS12 (unconditional Hankel cousin) —PS14 (D2=0).
- TA1—TA2,TA3,TA4,TA5,TA6,TA7,TA8 (internal) —PS1 (Stieltjes=corank, master value bridge) —HT2 (ζ∉K_B) —FF5/FF2 (FF corank) —CO10 (F₁).

**Inter-apex bridges** (the two apexes are *seam-joined*, not mutually implying):
- PA1—FF5—TA1 (in the function-field model, ι-unitary [PA] and corank=1 [TA] coincide).
- PA1—CO8—(relation lattice)—TA7—TA1 (the cohomology PA1 vanishes is built on the lattice TA measures).

**Weld as the central spine** (WD1 touches the most clusters):
- WD1—IV2 (FE) —WD3—LX2/LX3 (log-ξ calculus) —WD7—TA6 (∂_s=−Σlog p·θ_p) —CO9/CO1 (weld=arch×prime, C5) —DF1/DF4/DF7 (defect & phase) —PS-POW/PS8/PS11 (−ξ'/ξ, ζ'/ζ coeffs) —HD1/HD2/HD3 (Hadamard) —MS1/XF1 (scattering, explicit formula) —HT3 (constraint).

**Archimedean backbone:** GA1—BR1—CO2—CO1 (a_Γ=Γ_ℝ ratio, non-CC); GA1—GA2 (digamma); GA1—WD7 (M_∞ gen); GA3—IV2 (χ=FE factor); GA3—GA4—CO2 (∂_s log χ≠0); GA1—LX5 (θ'=½log(T/2π) asymptotic); **GA4—LX5 (BR6: ∂_s log χ(½+iT)=−2θ'(T), exact)**.

**σ=½ family:** IV7—ST1—CO5 (|p^{−s}|=p^{−½} ⟺ σ>½ ⟺ coboundary σ≥½); ST1—ST2,ST3,ST4,ST5; ST6—ST7.

**Curvature/zeros:** PH1—PH2—WD1 (Φ_2=line curvature of log ξ); PH1—CW2—CW1 (off-line quartet) —PA2 (off-line zeros); PH4—GA3/ZP; **PH2—LX3 (BR7: harmonicity of log|ξ|, Re Φ_2=−∂²_σ log|ξ|, Δlog|ξ|=2πμ_ξ; RH ⟹ critical line is a crest of log|ξ|, converse = CW-domination)**; **PH2—CW2 (BR7-converse: off-line bump C_a vs on-line background)**.

**Frobenius model:** FF1—FF2—FF3—FF4—FF5—FF6 internal; FF3—PA1 (margin) & FF3—BR5—ML; FF6—PS-POW (toy S_k); FF4—PS-POW (FF Stieltjes).

**Stieltjes web:** PS-POW—PS4—PS10 (Li, blind spot); PS-POW—PS11—GA3 (S_k value→ζ,β); PS-POW—PS5—PS12—PS7 (P_k→ζodd→moment/cumulant); PS-POW—PS14—IV2 (μ_{2k+1}=0 by FE); **IV4—PS14 (BR8: w↦−w parity ⟹ odd moments vanish ⟹ bridge uses y=−w^{−2}, the squared coordinate)**; **IV4—PS-POW (even-quotient dictionary, Formula 181: Φ(z)=Ξ(√z), T_k=−2k(−1)^k[z^k]logΦ; factor 2 = FE-pair trace weight 2m)**; PS1—PS13 (γ_E); PS2—TA6.

**Remaining tails (each joined):** ZP—HD2 (ζ'(ρ)); WD9—WD7 (passport); WD11—WD2,CO7 (gauge); HT1—TA1,WD1; DF5—DF2/ST1; DF6—DF1; DF8—DF7.

---

## Completeness ledger (F → node, verified 178/178 exactly once)

| F | node | F | node | F | node | F | node | F | node | F | node |
|---|---|---|---|---|---|---|---|---|---|---|---|
|1|WD3|31|TA6|61|CO9|91|CW1|121|TA7|151|PS-POW|
|2|WD1|32|TA1|62|GA3|92|HT2|122|IV6|152|PA1|
|3|DF1|33|HD2|63|IV6|93|WD4|123|ZP|153|PA1|
|4|ST3|34|LX2|64|GA4|94|WD7|124|PS1|154|PS-POW|
|5|CW1|35|LX3|65|WD5|95|WD7|125|FF4|155|WD1|
|6|CW1|36|PH2|66|MS1|96|GA1|126|CO10|156|PS-POW|
|7|IV1|37|PH1|67|PA3|97|IV7|127|TA4|157|PS11|
|8|IV1|38|PH3|68|PA2|98|LX5|128|FF5|158|PS12|
|9|IV1|39|PH3|69|WD1|99|LX5|129|PS2|159|TA1|
|10|IV2|40|CW2|70|PA1|100|DF7|130|CO8|160|PS13|
|11|IV2|41|PA1|71|LX4|101|PA7|131|PS-POW|161|FF6|
|12|IV3|42|ST1|72|PA2|102|HD3|132|PS4|162|XF1|
|13|IV4|43|ST2|73|HD2|103|HD3|133|PS5|163|PS14|
|14|CO2|44|ST2|74|DF2|104|HT1|134|TA6|164|PA5|
|15|CO2|45|ST1|75|DF2|105|HT1|135|IV1|165|PA1|
|16|WD2|46|CO5|76|DF2|106|HT3|136|GA2|166|PE1|
|17|CO1|47|ST4|77|DF2|107|PS9|137|TA7|167|MS2|
|18|WD3|48|ST5|78|DF4|108|CW2|138|WD11|168|TA1|
|19|WD4|49|PH4|79|DF4|109|PS10|139|FF1|169|PA1|
|20|WD5|50|PH1|80|DF4|110|PS10|140|PA2|170|HD1|
|21|WD6|51|IV2|81|PA1|111|FF1|141|PA2|171|HD1|
|22|WD7|52|CO6|82|DF5|112|FF3|142|PS-POW|172|PA1|
|23|WD7|53|PA1|83|DF6|113|PS7|143|IN1|173|TA1|
|24|WD9|54|PA2|84|PA5|114|PS7|144|IN1|174|PS-POW|
|25|TA2|55|FF2|85|PA1|115|PS8|145|TA8|175|PA1|
|26|TA2|56|WD2|86|PA1|116|ST6|146|DF8|176|PA9|
|27|TA2|57|CO3|87|PA1|117|ML|147|CW1|177|PA1|
|28|TA3|58|CO4|88|CO8b|118|ST7|148|LX2|178|PS12|
|29|TA4|59|CO7|89|TA1|119|TA5|149|ST3| | |
|30|TA5|60|CO8|90|PA1|120|CO7|150|PA1| | |

---

## What is irreducible, and why (fixed point)

The graph cannot be reduced further without either fabricating an equivalence or destroying real
structure. Concretely (full rejection log in worklog Phase D):

1. **The two apexes stay two.** PA1 (positivity) and TA1 (transcendence) are *seam-joined* via FF5
   and CO8/TA7, not collapsible: ω=0 (PA1's vanishing class, CO8) is built **on** the relation
   lattice whose corank TA1 measures, but neither predicate implies the other (CO8b: even ω=0⇏RH).
2. **Framework-distinct RH-characterizations are edges, not merges.** APS index (PA3), Koszul/ω
   (CO8), de Branges (MS2), period domain (PE1), FF ι-unitary (FF5) each carry their own supporting
   formulas; folding them into PA1 would erase those and bury the CO8b caveat.
3. **Linear ≠ algebraic independence** (TA6 vs TA1); **unconditional ≠ conditional** positivity
   (PS12's H_FID⪰0 vs PA1's det H_d≥0⟺RH); **definition ≠ predicate** (PA5 Q_W vs PA1 Q_W⪰0).
   Each such pair was tested and rejected.
4. **The rich tails (PS, CO, WD) are genuine webs of distinct formulas**, irreducible to single
   nodes but fully connected by edges — which is the requested outcome (few nodes, fewer isolates),
   not a single super-node that would hide the mathematics.

Audit trail: `formulas-graph.worklog.md` (Phase A normal forms · Phase B per-pair verdicts ·
Phase C edges/bridges · Phase D attack pass).
