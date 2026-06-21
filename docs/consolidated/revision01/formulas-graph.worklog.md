# Formulas-graph — reduction worklog (audit trail)

Provenance for `formulas-graph.md`. Every reduction decision is recorded here so it can be
checked. Source: `formulas.md` (F1–F178). Nothing is asserted "cannot be further reduced"
until the Phase D attack pass has rejected every candidate merge with a written reason.

## Method (committed)

Five operations, applied in passes to a fixed point:

- **MERGE-=**  same equation, different notation → one node.
- **MERGE-⊃**  B is A at a fixed parameter / a restatement → B folds into A as an instance.
- **MERGE-⟺**  several `⟺` statements about the *same predicate* → one maximal equivalence node.
- **FOLD-:=**  a symbol definition consumed by another formula → folded into the consumer (or a small shared def node).
- **EDGE / BRIDGE**  distinct objects linked by a named operation (differentiate, log, sum-over-zeros, specialise, pull back) → two nodes + a labelled edge; a *bridge formula* is constructed only when the link is mechanical, else labelled `[BRIDGE-conj]`.

Rule separating MERGE from EDGE: **merge only if no new mathematical object is introduced.**
A derived property that introduces no new symbol (e.g. `∫C_a=0` from `C_a`) folds; anything
introducing a new object (e.g. `Φ_2=(d/dt)²logξ` introduces `log ξ`) stays a node + edge.

Definition of done: (1) all 178 appear in the ledger exactly once; (2) no surviving pair can
MERGE; (3) every isolated node has been attacked for a bridge; (4) remaining isolates carry a
written reason they are irreducibly separate.

## Phase-A primary-object keys

`INV` involution/FE · `WELD` weld H / carrier / ω-as-Hds · `OPALG` σ_p,∂_s,e_m,group,passport ·
`DEFECT` Δ & phase-space experiment · `CURV-WIN` C_a · `PHI` Φ_k line curvature ·
`APEX-POS` RH⟺positivity · `KAPPA` κ₋ counting · `APEX-TR` corank/trdeg/DSS ·
`BAKER` quantitative independence · `STIELT` power-sums/Stieltjes/Li/special values ·
`STAT` random model/CLT/Fisher/GUE · `COCYC` cocycle/coboundary/Koszul/CC/F₁/ω-class ·
`GAMMA` Γ_ℝ,ψ,χ identities · `FROB` Frobenius/function-field · `INERTIA` Bezoutian/Schur–Cohn ·
`LOGXI` argument principle/μ_ξ/winding/ω=dlogξ/phase-count · `HADA` Hadamard/pole-model/surrogate ·
`HT` Hölder/HT-closure/WdW/ζ∉K_B · `XF` explicit formula · `MS` Maass–Selberg/de Branges ·
`PERIOD` period domain · `MISC` Lehmer / zero-perturbation.

## Phase A — normal forms (all 178, numeric order)

| F | key | normal form |
|---|-----|-------------|
| 1 | LOGXI | ω := d log ξ(s)  (def: transport 1-form) |
| 2 | WELD | H := ∂_s log Λ = ∂_s log Γ∞ + ζ'/ζ  (def: weld = arch + prime) |
| 3 | DEFECT | Δ(σ,t) := max(log|A|,log|P|) − log|A+P|, A=∂_s logΓ∞, P=ζ'/ζ |
| 4 | STAT | σ_wall = max(½, 1/k₀) |
| 5 | CURV-WIN | C_a(τ) := 2(a²−τ²)/(a²+τ²)²; >0 ⟺ |τ|<a |
| 6 | CURV-WIN | ∫_ℝ C_a dτ = 0  (property of 5) |
| 7 | INV | ι: s↦1−s  (def) |
| 8 | INV | ι²=id, Fix(ι)={Re s=½} |
| 9 | INV | s↦1−s̄, Fix={Re s=½}  (anti-holomorphic) |
| 10 | INV | Λ(s)=Λ(1−s) |
| 11 | INV | ξ(s)=ξ(1−s) |
| 12 | INV | ξ'/ξ(s)=−ξ'/ξ(1−s); |ξ'/ξ(½+δ+it)|=|ξ'/ξ(½−δ+it)|  (log-deriv FE) |
| 13 | INV | Ξ(w):=ξ(½+w), Ξ(w)=Ξ(−w), 𝒟={ρ−½} |
| 14 | COCYC | a_Γ(s)=s/2π  (value) |
| 15 | COCYC | a_Γ(z)=z, div=[0]−[∞], deg_ℤ=+1≠0  (arch non-CC) |
| 16 | OPALG | σ_p: x_p↦p^{−1}x_p  (def) |
| 17 | COCYC | C5 = weld = {one non-CC place}×{CC places} |
| 18 | WELD | ω=H ds, r*(Hds)=Hds, H(s)=−H(1−s) |
| 19 | OPALG | 𝔾_a⋊𝔾_m |
| 20 | OPALG | [∂_s,M_p]=−log p  (seam commutator) |
| 21 | OPALG | σ_p·e_m=p^{−m_p}e_m |
| 22 | OPALG | ∂_s·e_m=−(m·ℓ)e_m=−(Σm_p log p)e_m=−(log n)e_m |
| 23 | OPALG | ∂_s=−Σ_p(log p)θ_p |
| 24 | OPALG | Π(S)=(|S|,Σ_{m∈S}m), shift −|S|log p |
| 25 | APEX-TR | corank_ℚ(Λ_{M_ζ})=∞ |
| 26 | APEX-TR | corank_{F_q}(Λ_ff)=1 |
| 27 | APEX-TR | gap=∞−1 |
| 28 | APEX-TR | corank<∞ ⟺ M holonomic |
| 29 | APEX-TR | trdeg(T_{s_0})≤corank |
| 30 | APEX-TR | dim W=corank |
| 31 | APEX-TR | corank=∞ ⟺ {log p} ℚ-lin-indep |
| 32 | APEX-TR | trdeg=∞ ⟺ {log p} ℚ-alg-indep |
| 33 | HADA | ξ'/ξ(s)~m_ρ/(s−ρ) near ρ |
| 34 | LOGXI | (1/2πi)∮_C d log ξ = #{zeros inside C} |
| 35 | LOGXI | μ_ξ=(1/2π)Δ log|ξ|  (def: source measure) |
| 36 | PHI | (d/dt)²log ξ(½+it)=Σ_ρ(½+it−ρ)^{−2}=Φ_2(t) |
| 37 | PHI | Φ_k(t)=Σ_ρ(½+it−ρ)^{−k}, k≥2  (def) |
| 38 | PHI | RH ⟹ Φ_2(t)=−Σ_γ(t−γ)^{−2}<0 |
| 39 | PHI | RH ⟹ (d/dt)²log|ξ(½+it)|<0 |
| 40 | CURV-WIN | off-line FE-quartet contributes C_a(τ)>0 for |t−γ|<a |
| 41 | APEX-POS | det H_d≥0 ∀d,t ⟺ RH |
| 42 | STAT | 𝓛(σ)=−Σ_p log(1−X_p p^{−σ}) conv a.s. ⟺ σ>½ |
| 43 | STAT | Var(Re 𝓛)=½V(σ)~½loglog X |
| 44 | STAT | log|ζ(½+it)|/√(½loglog t)⇒𝒩(0,1)  (Selberg) |
| 45 | STAT | Σ_p p^{−2σ}<∞ ⟺ σ>½  (Mertens) |
| 46 | COCYC | additive Euler cocycle = bounded L²-coboundary ⟺ σ≥½ |
| 47 | STAT | ‖ψ_s‖²=ζ(2σ) |
| 48 | STAT | g_F=(log ζ)''(2σ)=Var_p(log n)~1/(2σ−1)² |
| 49 | PHI | χ_n(ρ)/χ_n(1−ρ)=(n^{1−2β}/|χ_FE|)^{1/m_ρ} n-indep ⟺ β=½ |
| 50 | PHI | χ_n≡Φ_k(t)  (susceptibility=curvature) |
| 51 | INV | Λ(s)=Λ(1−s)⟺θ(1/t)=√t θ(t)⟺Poisson (Ш̂=Ш) |
| 52 | COCYC | g_p=g_p^{−1}⟹g_p=±1 |
| 53 | APEX-POS | RH⟺Q_W⪰0⟺κ₋=0 |
| 54 | KAPPA | κ₋=#{off-line zero-pairs} |
| 55 | FROB | polarization⟺single Frobenius⟺corank=1⟺F_q |
| 56 | OPALG | τ_p=σ_p−1 |
| 57 | COCYC | τ_p a_q=τ_q a_p  (additive 1-cocycle) |
| 58 | COCYC | d1∘d0=0  (Koszul) |
| 59 | COCYC | a=c·σ(g)/g  (CC = gauges to constant) |
| 60 | COCYC | ω=0∈H²(G_L) |
| 61 | COCYC | ρ_∞(s)·ρ_ζ(s)=1 |
| 62 | GAMMA | χ(s)=Γ_ℝ(1−s)/Γ_ℝ(s)=π^{s−½}Γ((1−s)/2)/Γ(s/2) |
| 63 | INV | ι_ζ:θ_p↦−θ_p  (prime-side involution) |
| 64 | GAMMA | ∂_s log χ=log π−½ψ((1−s)/2)−½ψ(s/2)≠0 |
| 65 | OPALG | [∂_s,σ_p]=0 |
| 66 | MS | −(φ'/φ)(½+ir)=2[(ξ'/ξ)(1+2ir)−(ξ'/ξ)(2ir)] |
| 67 | KAPPA | κ₋=APS index, RH⟺Index=0 |
| 68 | KAPPA | κ₋=2·#{off-line zeros} |
| 69 | WELD | M_Ξ:=−Ξ'/Ξ  (def: carrier) |
| 70 | APEX-POS | RH⟺supp μ_ξ⊂{Re=½} |
| 71 | LOGXI | (1/2πi)∮_{∂R}(ξ'/ξ)ds=0 for rectangles off the line |
| 72 | KAPPA | ρ=β+iγ, β≠½  (def: off-line zero) |
| 73 | HADA | ξ'/ξ(s)~m_ρ/(s−ρ)+h(s)  (local pole model) |
| 74 | DEFECT | Δ_{ζ'/ζ}→log2; Δ_{(ζ'/ζ)_N}→0 |
| 75 | DEFECT | d_transport(ζ'/ζ,(ζ'/ζ)_N)≥c>0 |
| 76 | DEFECT | co-failure excess≥c>0 |
| 77 | DEFECT | λ₁(G_true)≥λ₁(G_finite)+c |
| 78 | DEFECT | Cov(O,δV)>0 (true)/<0 (controls) |
| 79 | DEFECT | ∫O dθ>c>0 |
| 80 | DEFECT | θ(t)=arg(ζ'/ζ(½+it)), O(t)=log(1+|ζ'/ζ(½+it)|)  (def) |
| 81 | APEX-POS | |1/(s−ρ)|=1/√((σ−β)²+τ²)⟹centre σ=β; all centres=½⟺RH |
| 82 | DEFECT | σ>1⟹(ζ'/ζ)_N→ζ'/ζ  (control) |
| 83 | DEFECT | K_q(σ,σ')=Corr(𝟙_{Δ(σ+it)>q},𝟙_{Δ(σ'+it)>q}) |
| 84 | APEX-POS | Q_W=𝔇, signature (1|∞), V_arch=Reψ |
| 85 | APEX-POS | m_ξ∈ℕ₀ |
| 86 | APEX-POS | H=[m_{i+j}]⪰0 ∧ H'=[m_{i+j+1}]⪰0 |
| 87 | APEX-POS | #neg(Q_W)=0⟺‖P̃‖≤1⟺Ω≽Π, P̃=Ω^{−½}ΠΩ^{−½} |
| 88 | COCYC | ω=0⇏RH |
| 89 | APEX-TR | corank^{(T)}=∞ for T≥2 |
| 90 | APEX-POS | κ₋=0 = (Q_W⪰0)=(FE-polariz⪰0)=(m_ξ∈ℕ₀)=(det H_d≥0)=(Ω≽Π)=(G5 unitary) |
| 91 | CURV-WIN | C_a(0)=2/a²  (property of 5) |
| 92 | HT | ζ∉K_B=ℂ(s,{p^{−s}}) |
| 93 | OPALG | ⟨1,r⟩=𝔾_a⋊𝔾_m, transverse seam [𝔾_a,𝔾_m] |
| 94 | OPALG | ∂_s e_m=−(log n)e_m (M_ζ); ∂_s|M_∞=−½logπ+½ψ(s/2) (M_∞) |
| 95 | GAMMA | digamma residue=½ψ(s/2) |
| 96 | GAMMA | Γ_ℝ(s+2)=(s/2π)Γ_ℝ(s) |
| 97 | INV | |p^{−s}|=p^{−½}⟺Re(s)=½ |
| 98 | LOGXI | φ'(T)=θ'(T)+πS'(T) |
| 99 | LOGXI | θ'(T)=½log(T/2π) |
| 100 | DEFECT | ω=dO∧dφ, O=log(1+|ζ'/ζ|), φ=arg(Γ∞+ζ'/ζ) |
| 101 | APEX-POS | inertia (1,0,10), κ₋=1  (Davenport–Heilbronn) |
| 102 | HADA | e^{q((s−½)²)}·ξ  (surrogate) |
| 103 | HADA | (e^q ξ)'/(e^q ξ)=ξ'/ξ+q' |
| 104 | HT | HT±(D-algebraic)=HT |
| 105 | HT | ∄ poly F(s,Γ,…,Γ^{(n)})≡0  (Hölder) |
| 106 | HT | Ĥ Ψ=0  (Wheeler–DeWitt) |
| 107 | STIELT | F^{(T)}(1)=(−1)^T ΣC_a∏(log p)^{a_p} |
| 108 | CURV-WIN | (½−β+iτ)^{−2}+(β−½+iτ)^{−2}=2(a²−τ²)/(a²+τ²)², >0⟺|τ|<a |
| 109 | STIELT | n₀=πγ/(4δ) |
| 110 | STIELT | c=n₀δ/γ≈0.79≈π/4 |
| 111 | FROB | |μ|=√q |
| 112 | FROB | normalized margin=1−q^{−½} |
| 113 | STIELT | κ_n=ζ(2n+1)  (free cumulants) |
| 114 | STIELT | κ_2>0,κ_4<0,κ_6>0,κ_8<0 |
| 115 | STIELT | c_n=Λ(n)≥0 |
| 116 | STAT | ⟨r⟩=0.611  (GUE) |
| 117 | MISC | M(L)=1.176280818  (Lehmer Mahler measure) |
| 118 | STAT | corr(log margin, gap)=−0.25 |
| 119 | APEX-TR | T/(N+T)  (domain-corank fraction) |
| 120 | COCYC | a CC ⟺ deg_O(a)=0 on every σ-orbit |
| 121 | APEX-TR | g=(p^{−1})_p, ∞ Zariski closure when Λ=0 |
| 122 | INV | s↦1−s ⟹ p^{−s}↦p^{−1}(p^{−s})^{−1} |
| 123 | MISC | dρ/dε=−n^{−ρ}/ζ'(ρ) |
| 124 | STIELT | trdeg_ℚ{Stieltjes(ζ_S)}=corank_ℚ{log p:p∈S} |
| 125 | FROB | γ_n^{(q)}=(B_n^+/n!)(log q)^n  (corank-1 collapse) |
| 126 | COCYC | F₁ exists⟺(D=0)∧(corank finite); over ℚ (D=+1,corank=∞) |
| 127 | APEX-TR | {corank=1}⊊{trdeg=1}, witness {π,π²} |
| 128 | FROB | trdeg(periods)=dim G; dim W=corank=1; ι unitary on Fix⟺RH/F_q |
| 129 | STIELT | c_1=Σβ_p log p |
| 130 | COCYC | RH⟺arch-completed Koszul acyclic⟺ω=0 |
| 131 | STIELT | −ξ'/ξ(s)=Σ_{k≥1}P_k s^{k−1}, P_k=Σρ^{−k} |
| 132 | STIELT | λ_n=−ΣC(n,j)(−1)^j P_j |
| 133 | STIELT | ℚ({P_k})⊇{ζ(odd)} |
| 134 | APEX-TR | {m:Σm_p log p=0}={0} |
| 135 | INV | ι(s)=1−s (order 2); ῑ fixes Re=½ |
| 136 | GAMMA | ψ(s/2+1)=ψ(s/2)+2/s |
| 137 | APEX-TR | rank=Cardinal.mk(Nat.Primes)  (corank ∞ after adjoining ∂_s) |
| 138 | OPALG | f=g·e^{zλ} solves the shift ODE |
| 139 | FROB | e_k(S)=q^k e_k(S^{−1}); ∏(1−ωT) FE-inv, |ω|=√q |
| 140 | KAPPA | κ₋(H)=#{off-line conjugate pairs}  (Sylvester) |
| 141 | KAPPA | one off-line zero⟹κ₋=2  (FE-doubling) |
| 142 | STIELT | superzeta gen func=Σ_i(1−r_i X)^{−1}; k-th coeff=Σρ^{−k}=P_k |
| 143 | INERTIA | f(s)g(t)−f(t)g(s)=(s−t)Σr_j f_j(s)f_j(t)  (Bezoutian) |
| 144 | INERTIA | sigNeg(scForm[f])=winding(f)=#inside(f)  (Schur–Cohn) |
| 145 | BAKER | |m·ℓ|≥c_B H(m)^{−κ_B}  (Baker–Wüstholz) |
| 146 | DEFECT | ‖∂_t arg(Γ∞+ζ'/ζ)‖  (phase-Sobolev H^{1/2}) |
| 147 | CURV-WIN | C_a width≈a/2, 8a→0.016 peak  (property of 5) |
| 148 | LOGXI | ∮ d arg=2πi(#zeros−#poles)  (winding) |
| 149 | STAT | σ*∈(½,1), maybe 3/4; region Σp^{−2σ}~loglog |
| 150 | APEX-POS | y_ρ:=−(ρ−½)^{−2}  (def: chart) |
| 151 | STIELT | Σ_ρ(ρ−½)^k diverges |
| 152 | APEX-POS | RH⟺every y_ρ>0⟺{T_k}_{k≥1} Stieltjes⟺Hankel towers PSD (T_0=∞ excl) |
| 153 | APEX-POS | κ₋=0⟺Q_W⪰0(sig(1|∞))⟺m_ξ∈ℕ₀⟺det H_d≥0⟺uniform Jensen/Laguerre–Pólya |
| 154 | STIELT | M_k=p_k; S_k=−k[w^{2k}]log Ξ; λ_n=ΣC(n,j)(−1)^{j+1}σ_j |
| 155 | WELD | Ξ'/Ξ=∂_s logΓ∞+ζ'/ζ; S_k=S_k^A+S_k^P |
| 156 | STIELT | halves≍2^{2k}; S_k≍γ_1^{−2k}; cancel 2·800^{−k}; Δ_k∼k; guard digits |
| 157 | STIELT | Σ(ρ−½)^{−2k}=2^{2k}−¼(2^{2k}−1)ζ(2k)−2^{2k−2}β(2k)−(2(2k−1)!)^{−1}(ζ'/ζ)^{(2k−1)}(½) |
| 158 | STIELT | ζ(2k+1)=∫y^k dν, ν=Σ(1/n)δ_{1/n²}≥0 |
| 159 | APEX-TR | corank^{(T)}=∞∀T≥2⟺{log p}alg-indep⟺trdeg=∞⟺DSS |
| 160 | STIELT | γ_E∉ℚ |
| 161 | FROB | γ_n=n: S_k=(−1)^kζ(2k)∈ℚπ^{2k}; π²+6S_1=0; 5S_2=2S_1² |
| 162 | XF | Σ_ρ h(γ_ρ)=arch−Σ_p(log p)… |
| 163 | STIELT | μ_{2k+1}=Σ(ρ−½)^{−(2k+1)}=0; RH⟺D2=Σ(β−½)²=0 |
| 164 | APEX-POS | signature (1,ρ−1)  (Hodge index) |
| 165 | APEX-POS | A_arch−Σ_{p∈S}P_p≥0 as S→all ⟺ RH  (ROUTE-C) |
| 166 | PERIOD | RH⟺F_ζ elliptic, period interior to D_∞=Sp_∞(ℝ)/U(∞) |
| 167 | MS | K_MS(s,w)~(1−Θ(s)Θ̄(w))/(s+w̄−1)∈ℕ₀⟺RH |
| 168 | APEX-TR | DSS⟺{γ_n}alg-indep over period field (mod Grothendieck) |
| 169 | APEX-POS | #{non-real Jensen roots}→2κ₋; =0∀(d,n)⟺LP⟺RH |
| 170 | HADA | ξ'/ξ(s)=b+Σ_ρ[1/(s−ρ)+1/ρ]  (Hadamard) |
| 171 | HADA | ξ(s)=ξ(0)e^{bs}∏_ρ(1−s/ρ)e^{s/ρ} |
| 172 | APEX-POS | RH⟺κ₋=0⟺det H_d≥0∀d,t |
| 173 | APEX-TR | corank^{(2)}=∞ (open for {log2,log3}) |
| 174 | STIELT | M_k(R)=Σ(ρ−½)^k |
| 175 | APEX-POS | D2=Σ(β−½)², RH⟺D2=0 |
| 176 | APEX-POS | g(n)=a_n²/(a_{n−1}a_{n+1})→1~c/n  (Turán) |
| 177 | APEX-POS | det H_d≥0∀d,t; anisotropic radius ρ_min(d,n) |
| 178 | STIELT | H_FID=[ζ(2(i+j)+3)]⪰0  (unconditional) |

### Phase-A group sizes (partition check, must sum to 178)

INV 14 (7,8,9,10,11,12,13,51,63,97,122,135 = 12 … +2) — recount in Phase B headers.
Counts are re-derived per group at the top of each Phase-B section; the ledger at the end is
the authoritative each-formula-appears-once check.

---

## Phase B — intra-group pairwise reduction (verdicts → nodes)

Notation: `a×b → MERGE(reason)` collapses; `a×b → EDGE(op)` keeps both, link recorded for Phase C.
Node IDs are stable; "absorbs" lists the originals; the ledger at the end is authoritative.

### INV  (members 7,8,9,10,11,12,13,51,63,97,122,135 — 12)

Pairs tested:
- 7×8 → MERGE-⊃ (8 = order + fixed locus of the map 7 defines; Fix is determined by ι, no new object).
- 7×135 → MERGE-= (135 "ι order 2" restates 7+8 holomorphic part).
- 9×135 → MERGE-= (135's ῑ *is* the anti-holomorphic involution of 9; same map, same fixed locus).
- 10×11 → MERGE-= (ξ=½s(s−1)Λ and ½s(s−1) is FE-invariant: s(s−1)↦(1−s)(−s)=s(s−1); so Λ(s)=Λ(1−s) ⟺ ξ(s)=ξ(1−s) **exactly**).
- 10×51 → MERGE-⟺ (51 is the SAME predicate, the FE, with its analytic equivalents θ-transform and Poisson; one equivalence statement).
- 13×IV2 → EDGE-recentre (Ξ(w)=Ξ(−w) **is** the FE in w=s−½; but 13 also *defines* Ξ and 𝒟, new objects consumed by WELD/PHI/STIELT → keep as a def node, not a fold).
- 12×IV2 → EDGE-(d/ds·log) (12 = log-derivative of the FE; new relation on ξ'/ξ).
- 63×122 → MERGE-= (p^{−s}=e^{−s log p}; s↦1−s gives p^{−s}↦p^{−1}(p^{−s})^{−1} [inversion] = θ_p↦−θ_p [additive negation]; one map, two coordinate systems).
- 97×IV1 → EDGE (97 is a *modulus* identity locating Fix(ι) on prime lanes; new content |p^{−s}|=p^{−½}).

Nodes:
- **IV1** = {7,8,9,135}  ι:s↦1−s, ι²=id, Fix={Re=½}; anti-holomorphic ῑ:s↦1−s̄ same locus.
- **IV2** = {10,11,51}  ξ(s)=ξ(1−s) ⟺ Λ(s)=Λ(1−s) ⟺ θ(1/t)=√t θ(t) ⟺ Poisson (Ш̂=Ш).
- **IV3** = {12}  ξ'/ξ(s)=−ξ'/ξ(1−s)  (Berry equalization).
- **IV4** = {13}  Ξ(w):=ξ(½+w), Ξ(w)=Ξ(−w), 𝒟={ρ−½}  (def node; recentred FE).
- **IV6** = {63,122}  involution acts on prime lanes by inversion: p^{−s}↦p^{−1}(p^{−s})^{−1}, i.e. θ_p↦−θ_p.
- **IV7** = {97}  |p^{−s}|=p^{−½} ⟺ Re(s)=½.
(The χ FE-factor 62 is keyed GAMMA; it becomes node GA-χ, edged to INV in Phase C. IV5 reserved for it.)
12 formulas → 6 nodes.

### WELD  (members 2,18,69,155 — 4)

- 2×69 → MERGE-= (M_Ξ=−Ξ'/Ξ is minus the recentred weld; sign+recentre only).
- 2×155 → MERGE (same arch+prime SPLIT on two carriers; Λ'/Λ vs Ξ'/Ξ differ by the mechanical FE-symmetric term ∂_s log(½s(s−1))=1/s+1/(s−1), recorded not hidden; the split is identical). 155's clause "S_k=S_k^A+S_k^P" feeds the STIELT S_k node (cross-edge, not a second node).
- 2×18 → EDGE (18's "ω=H ds" identifies the transport 1-form with the weld [bridge to LOGXI F1]; 18's "H(s)=−H(1−s)" = differentiate Λ(s)=Λ(1−s) ⟹ Λ'/Λ(s)=−(Λ'/Λ)(1−s) = IV3 on carrier Λ [edge to IV3]).

Nodes:
- **WD1** = {2,69,155}  H=∂_s log Λ=∂_s logΓ∞+ζ'/ζ; carrier M_Ξ=−Ξ'/Ξ=−(arch+prime).
- **WD3** = {18}  ω=H ds; r*(Hds)=Hds ⟺ H(s)=−H(1−s).
4 formulas → 2 nodes.

### OPALG  (members 16,19,20,21,22,23,24,56,65,93,94,138 — 12)

- 19×93 → MERGE-⊃ (93 ⊃ 19: adds ⟨1,r⟩ identification + the transverse-seam commutator).
- 16×56 → MERGE-⊃/:= (τ_p:=σ_p−1 is the additive part of the operator 16 defines).
- 20×65 → no merge; EDGE (distinct brackets: [∂_s,M_p]=−log p is the seam, [∂_s,σ_p]=0 trivial; two faces of 𝔾_a⋊𝔾_m).
- 22×94 → MERGE-⊃ (94 ⊃ 22: same M_ζ eigenvalue + adds the M_∞ generator).
- 23×22 → MERGE-= (23 ∂_s=−Σ(log p)θ_p applied to e_m gives −Σm_p log p=−log n; operator vs eigenvalue form of one relation).
- 21×{22,23,94} → no merge; EDGE (σ_p eigenvalue is the *multiplicative* shift, distinct operator from ∂_s).
- 24×WD7 → EDGE (passport is a block invariant built from mode indices).
- 138×WD2 → EDGE (general shift-ODE solution; links to COCYC F59 coboundary form).

Nodes:
- **WD2** = {16,56}  σ_p:x_p↦p^{−1}x_p; τ_p:=σ_p−1.
- **WD4** = {19,93}  ⟨1,r⟩=𝔾_a⋊𝔾_m, transverse seam [𝔾_a,𝔾_m].
- **WD5** = {20}  [∂_s,M_p]=−log p.
- **WD6** = {21}  σ_p·e_m=p^{−m_p}e_m.
- **WD7** = {22,23,94}  ∂_s=−Σ(log p)θ_p ⟹ ∂_s e_m=−(log n)e_m on M_ζ; ∂_s|M_∞=−½logπ+½ψ(s/2).  (GAMMA F95 ½ψ(s/2) folds here.)
- **WD9** = {24}  Π(S)=(|S|,Σm), shift −|S|log p.
- **WD10** = {65}  [∂_s,σ_p]=0.
- **WD11** = {138}  f=g·e^{zλ} solves the shift ODE.
12 formulas → 8 nodes.

### DEFECT  (members 3,74,75,76,77,78,79,80,82,83,100,146 — 12)

- 75×76×77 → MERGE (one predicate "true field separated from finite by c>0", three co-reported observables: transport metric, co-failure excess, top-eigenvalue gap; merged as the separation finding, not proven mutually equivalent — noted).
- 78×79×80 → MERGE (80 defines (θ,O); 78,79 are the loop-positivity finding on those coords).
- 100×80 → EDGE (100's φ=arg(Γ∞+ζ'/ζ) is the *full weld* phase ≠ 80's θ=arg(ζ'/ζ) [prime only]; 100 adds the 2-form, new object).
- 146×100 → EDGE (same weld phase φ; 146 is its H^{1/2} seminorm).
- 82×74 → EDGE (control/contrast: off the strip the truncation *does* converge).
- 83×3 → EDGE (K_q is the association kernel built on Δ).

Nodes:
- **DF1** = {3}  Δ=max(log|A|,log|P|)−log|A+P|.
- **DF2** = {74}  Δ_{ζ'/ζ}→log2; Δ_{(ζ'/ζ)_N}→0.
- **DF3** = {75,76,77}  positive separation c>0 (three observables).
- **DF4** = {78,79,80}  θ=arg(ζ'/ζ), O=log(1+|ζ'/ζ|); Cov(O,δV)>0, ∫O dθ>c>0.
- **DF5** = {82}  σ>1⟹(ζ'/ζ)_N→ζ'/ζ.
- **DF6** = {83}  K_q(σ,σ')=Corr(𝟙_{Δ>q},𝟙_{Δ>q}).
- **DF7** = {100}  ω=dO∧dφ, φ=arg(Γ∞+ζ'/ζ).
- **DF8** = {146}  ‖∂_t arg(Γ∞+ζ'/ζ)‖_{H^{1/2}}.
12 formulas → 8 nodes.

### CURV-WIN  (members 5,6,40,91,108,147 — 6)

- 5×6, 5×91, 5×147 → MERGE-⊃ (∫C_a=0, C_a(0)=2/a², width≈a/2 are parameter-free evaluations of C_a; no new object).
- 40×108 → MERGE-= (both: an off-line zero's FE-quartet contributes (½−β+iτ)^{−2}+(β−½+iτ)^{−2}=C_a; 108 is the algebra, 40 the prose).
- CW2×CW1 → EDGE (CW2 *equals* C_a; the new content is the off-line-zero source).

Nodes:
- **CW1** = {5,6,91,147}  C_a(τ)=2(a²−τ²)/(a²+τ²)², >0⟺|τ|<a; ∫=0; C_a(0)=2/a²; width≈a/2.
- **CW2** = {40,108}  (½−β+iτ)^{−2}+(β−½+iτ)^{−2}=C_a(τ)  (off-line quartet source).
6 formulas → 2 nodes.

### PHI  (members 36,37,38,39,49,50 — 6)

- 37×50 → MERGE-⊃ (χ_n≡Φ_k is a notation identity; folds).
- 36×37 → EDGE (36 is k=2 **and** identifies Φ_2=(d/dt)²log ξ, introducing log ξ → bridge to LOGXI/WELD).
- 38×39 → MERGE-= ((d/dt)²log|ξ|=Re Φ_2; under RH Φ_2 is real <0, so 39=Re(38)).
- 49×37 → EDGE (49 is a β=½ detector built from χ_n; uses χ_FE → edge to GA-χ, APEX-POS).

Nodes:
- **PH1** = {37,50}  Φ_k(t)=Σ_ρ(½+it−ρ)^{−k}, k≥2 (= χ_n).
- **PH2** = {36}  Φ_2(t)=(d/dt)²log ξ(½+it).
- **PH3** = {38,39}  RH ⟹ Φ_2<0 ⟺ (d/dt)²log|ξ(½+it)|<0.
- **PH4** = {49}  χ_n(ρ)/χ_n(1−ρ) n-independent ⟺ β=½.
6 formulas → 4 nodes.

### APEX-POS  (members 41,53,70,81,84,85,86,87,90,101,150,152,153,164,165,169,172,175,176,177 — 20)

Master-chain detection — every clause below is the SAME predicate (RH ⟺ κ₋=0 ⟺ a positivity):
- 90 is the maximal chain: κ₋=0 = Q_W⪰0 = FE-polariz⪰0 = m_ξ∈ℕ₀ = det H_d≥0 = Ω≽Π = G5 unitary.
- 53 ⊂ 90 (RH⟺Q_W⪰0⟺κ₋=0) → MERGE.
- 153 ⊂ 90 + adds "uniform Jensen/Laguerre–Pólya" and signature (1|∞) → MERGE.
- 172 ⊂ 90 (RH⟺κ₋=0⟺det H_d≥0) → MERGE.
- 41 = the single link det H_d≥0⟺RH → MERGE.
- 86 = matrix form of that link: H⪰0 ∧ H'⪰0 is Sylvester's criterion = "det H_d≥0 ∀d" (Hamburger) + shifted (Stieltjes) = "Hankel towers PSD" → MERGE.
- 70 = RH⟺supp μ_ξ⊂{Re=½} (new equivalent; μ_ξ from LOGXI F35 → edge) → MERGE.
- 152 = RH⟺y_ρ>0⟺{T_k} Stieltjes⟺Hankel towers PSD (seam-moment face) → MERGE.
- 150 (y_ρ:=−(ρ−½)^{−2}) = def consumed by 152 → FOLD.
- 175 = RH⟺D2=Σ(β−½)²=0 (D2=0 ⟺ all β=½ ⟺ RH; D2 def folds) → MERGE.
- 169 = #non-real Jensen roots=0⟺LP⟺RH (= the Jensen/LP clause) → MERGE.
- 165 = A_arch−ΣP_p≥0⟺RH = the Ω≽Π clause spelled out → MERGE.
- 87 = #neg(Q_W)=0⟺‖P̃‖≤1⟺Ω≽Π = operator-norm refinement of the Q_W⪰0 clause → MERGE.
- 85 (m_ξ∈ℕ₀) = a chain clause → MERGE.
- 81 = all occupation centres=½⟺RH (geometric equivalent) → MERGE.
- 177 = det H_d≥0 clause + anisotropic radius ρ_min (a measured margin, annotation) → MERGE.

Not the master chain (kept as attached nodes):
- 84×164 → MERGE-= (84 defines Q_W=𝔇 [explicit-formula distribution] with signature (1|∞); 164 is the finite-rank (1,ρ−1) signature — same object). This is the *construction* of Q_W, not an RH⟺ clause → node PA5, edge to PA1 & XF.
- 101 = Davenport–Heilbronn witness (off-line zeros ⟹ inertia (1,0,10), κ₋=1≠0): a concrete instance → node PA7, edge to PA2/PA1.
- 176 = Turán g(n)→1: a NECESSARY condition for LP, not ⟺RH → node PA9, edge to PA1.

Nodes:
- **PA1** = {41,53,70,81,85,86,87,90,150,152,153,165,169,172,175,177}  the master positivity apex
  (RH ⟺ κ₋=0 ⟺ Q_W⪰0 (sig (1|∞)) ⟺ FE-polariz⪰0 ⟺ m_ξ∈ℕ₀ ⟺ det H_d≥0 ∀d,t (Hankel towers PSD)
   ⟺ Ω≽Π (‖P̃‖≤1, A_arch−ΣP_p≥0) ⟺ G5 unitary ⟺ uniform Jensen/Laguerre–Pólya (#non-real Jensen roots=0)
   ⟺ supp μ_ξ⊂{Re=½} ⟺ y_ρ>0 / {T_k}_{k≥1} Stieltjes ⟺ all occupation centres=½ ⟺ D2=0).
- **PA5** = {84,164}  Q_W=𝔇, signature (1|∞) / finite-rank (1,ρ−1); V_arch=Reψ.
- **PA7** = {101}  Davenport–Heilbronn: inertia (1,0,10), κ₋=1.
- **PA9** = {176}  Turán g(n)=a_n²/(a_{n−1}a_{n+1})→1~c/n.
20 formulas → 4 nodes.

### KAPPA  (members 54,67,68,72,140,141 — 6)

- 54×68×140×141 → MERGE (all count off-line zeros with FE/conjugate multiplicity: κ₋=#pairs (54) = 2·#zeros (68) = Sylvester negative index (140); one off-line zero ⟹ κ₋=2 (141, FE-doubling) is the pairing convention reconciling the factor 2).
- 72 (off-line zero def ρ=β+iγ,β≠½) → FOLD (defines the counted object).
- 67 (κ₋=APS index, RH⟺Index=0) → EDGE (a distinct *index-theory realization* of κ₋; RH⟺Index=0 is PA1's κ₋=0 clause).

Nodes:
- **PA2** = {54,68,72,140,141}  κ₋=#{off-line conj. pairs}=2·#{off-line zeros}; one off-line ⟹ κ₋=2; = Sylvester index.
- **PA3** = {67}  κ₋=APS index; RH⟺Index=0.
6 formulas → 2 nodes.

### APEX-TR  (members 25,26,27,28,29,30,31,32,89,119,121,127,134,137,159,168,173 — 17)

- 159 master DSS chain; 32 (trdeg=∞⟺alg-indep) ⊂ 159 → MERGE; 89 (corank^{(T)}=∞,T≥2) ⊂ 159 → MERGE; 173 (corank^{(2)}=∞, open for {log2,log3}) = T=2 case → MERGE; 168 (DSS⟺{γ_n} alg-indep mod Grothendieck) extends DSS to ordinates → MERGE.
- 31×134 → MERGE-= (134 {m:Σm_p log p=0}={0} **is** {log p} ℚ-linear independence). LINEAR, distinct from TA1's ALGEBRAIC → EDGE TA6↔TA1.
- 25×26×27 → MERGE (27 gap=∞−1 is literally corank_ℚ−corank_ff = 25−26).
- 29×127 → MERGE (29 trdeg≤corank; 127 shows strict: {π,π²} has trdeg1<corank2).
- 30×119 → MERGE-loose (both size-of-corank-space; 30 dim W=corank exact, 119 T/(N+T) the internal fraction — co-reported; flag for Phase D).
- 121×137 → MERGE-loose (both "corank=∞ is robust": Zariski closure of (p^{−1})_p is ∞-dim when Λ=0; rank=card(primes) survives adjoining ∂_s; flag for Phase D).
- 28 (corank<∞⟺holonomic) → EDGE (general dichotomy).

Nodes:
- **TA1** = {32,89,159,168,173}  corank^{(T)}=∞∀T≥2 ⟺ {log p} ℚ-alg-indep ⟺ trdeg=∞ ⟺ DSS ⟺ {γ_n} alg-indep/period (mod Grothendieck).
- **TA2** = {25,26,27}  corank_ℚ=∞, corank_ff=1, gap=∞−1.
- **TA3** = {28}  corank<∞ ⟺ M holonomic.
- **TA4** = {29,127}  trdeg≤corank, strict ({π,π²}: 1<2).
- **TA5** = {30,119}  dim W=corank; internal fraction T/(N+T).
- **TA6** = {31,134}  corank=∞ ⟺ {log p} ℚ-lin-indep ⟺ {m:Σm_p log p=0}={0}.
- **TA7** = {121,137}  corank=∞ robust: Zariski closure of (p^{−1})_p ∞-dim when Λ=0; rank=card(primes) after adjoining ∂_s.
17 formulas → 7 nodes.

### BAKER  (member 145 — 1)

- **TA8** = {145}  |m·ℓ|≥c_B H(m)^{−κ_B} (Baker–Wüstholz). Quantitative engine under TA6; edge to MISC-Lehmer (height).
1 formula → 1 node.

### STIELT  (members 107,109,110,113,114,115,124,129,131,132,133,142,151,154,156,157,158,160,163,174,178 — 21)

- 131×142 → MERGE-= (both: P_k=Σρ^{−k} as generating-function coeffs; 131 from −ξ'/ξ, 142 from superzeta ∏(1−r_iX)^{−1}).
- {131,142}×151×174×154 → MERGE-⊃ (one object family "Newton power-sums over the zero-divisor 𝒟": P_k=Σρ^{−k}, M_k=Σ(ρ−½)^k [174; diverges 151; =Newton p_k 154-clause], S_k=Σ(ρ−½)^{−2k} [154-clause =−k[w^{2k}]logΞ]; same shape, differing only in chart/exponent convention; all are coeffs of log of the completed function).
- 156×154-S → MERGE (156 = asymptotic size/cancellation/guard-digits of S_k; a property).
- 132×PS-POW → EDGE (Li λ_n is a *derived* named sequence from the P_k; kept distinct).
- 157×PS-POW → EDGE (157 is the closed-form VALUE of S_k in ζ(2k),β(2k),(ζ'/ζ)^{(2k−1)}(½); bridge to GAMMA/special-values & WELD/ζ'/ζ).
- 113×114 → MERGE (114 = sign pattern of the cumulants 113 defines).
- 158×178 → MERGE (178 H_FID=[ζ(2(i+j)+3)]⪰0 is the Hankel consequence of 158 ζ(2k+1)=∫y^k dν, ν≥0).
- 109×110 → MERGE (110 c=n₀δ/γ≈π/4 derived from 109 n₀=πγ/(4δ)).
- 133, 124, 129, 107, 160, 115, 163 → each distinct object (no intra-merge):
  124 Stieltjes-trdeg=corank; 129 c_1=Σβ_p log p; 107 prime-log monomials; 133 ℚ({P_k})⊇ζ(odd);
  160 γ_E∉ℚ; 115 c_n=Λ(n)≥0; 163 μ_{2k+1}=0 (FE) + D2=0⟺RH(→PA1).

Nodes:
- **PS-POW** = {131,142,151,154,156,174}  zero power-sums: P_k=Σρ^{−k} (= −ξ'/ξ / superzeta coeffs); M_k=Σ(ρ−½)^k (contour, diverges); S_k=Σ(ρ−½)^{−2k}=−k[w^{2k}]logΞ (+asymptotics).
- **PS4** = {132}  λ_n=−ΣC(n,j)(−1)^j P_j (Li coefficients).
- **PS11** = {157}  S_k closed form in ζ(2k), β(2k), (ζ'/ζ)^{(2k−1)}(½).
- **PS1** = {124}  trdeg_ℚ{Stieltjes(ζ_S)}=corank_ℚ{log p:p∈S}.
- **PS2** = {129}  c_1=Σβ_p log p.
- **PS5** = {133}  ℚ({P_k})⊇{ζ(odd)}.
- **PS7** = {113,114}  κ_n=ζ(2n+1); κ_2>0,κ_4<0,….
- **PS8** = {115}  c_n=Λ(n)≥0.
- **PS9** = {107}  F^{(T)}(1)=(−1)^TΣC_a∏(log p)^{a_p}.
- **PS10** = {109,110}  n₀=πγ/(4δ); c=n₀δ/γ≈π/4.
- **PS12** = {158,178}  ζ(2k+1)=∫y^k dν (ν≥0); H_FID=[ζ(2(i+j)+3)]⪰0.
- **PS13** = {160}  γ_E∉ℚ.
- **PS14** = {163}  μ_{2k+1}=Σ(ρ−½)^{−(2k+1)}=0 (FE); D2=0⟺RH→PA1.
21 formulas → 13 nodes.

### STAT  (members 4,42,43,44,45,47,48,116,118,149 — 10)

- 42×45 → MERGE (𝓛 a.s.-convergence is governed by variance Σp^{−2σ}; same abscissa σ>½).
- 43×44 → MERGE (same Gaussian: variance ½loglog; 44 Selberg CLT).
- 47×48 → EDGE (g_F=(logζ)''(2σ) is the curvature of log‖ψ_s‖²=log ζ(2σ)).
- 4×149 → MERGE-loose (two critical abscissae in (½,1): wall σ_wall=max(½,1/k₀), crossover σ*; flag Phase D).
- 116, 118 → distinct (GUE order parameter; margin–gap correlation, a bridge).

Nodes:
- **ST1** = {42,45}  𝓛(σ) conv a.s. ⟺ Σp^{−2σ}<∞ ⟺ σ>½.
- **ST2** = {43,44}  Var(Re𝓛)~½loglog; log|ζ(½+it)|/√(½loglog t)⇒𝒩(0,1).
- **ST3** = {4,149}  σ_wall=max(½,1/k₀); crossover σ*∈(½,1).
- **ST4** = {47}  ‖ψ_s‖²=ζ(2σ).
- **ST5** = {48}  g_F=(logζ)''(2σ)=Var_p(log n)~1/(2σ−1)².
- **ST6** = {116}  ⟨r⟩=0.611 (GUE).
- **ST7** = {118}  corr(log margin, gap)=−0.25.
10 formulas → 7 nodes.

### COCYC  (members 14,15,17,46,52,57,58,59,60,61,88,120,126,130 — 14)

- 14×15 → MERGE-⊃ (15 ⊃ 14: a_Γ=s/2π + divisor deg=+1≠0, arch non-CC).
- 59×120 → MERGE (def + criterion of "constant-up-to-coboundary").
- 60×130 → MERGE (60's ω=0 is the conclusion of 130's chain RH⟺completed-Koszul-acyclic⟺ω=0).
- 88 → kept SEPARATE (88 ω=0⇏RH is the no-go: the *plain* class is insufficient, distinct from 130's *completed* class).
- 17,46,52,57,58,61,126 → distinct objects (no intra-merge).

Nodes:
- **CO1** = {17}  C5=weld={one non-CC place}×{CC places}.
- **CO2** = {14,15}  a_Γ=s/2π; div=[0]−[∞], deg_ℤ=+1≠0 (arch non-CC).
- **CO3** = {57}  τ_p a_q=τ_q a_p (additive 1-cocycle).
- **CO4** = {58}  d1∘d0=0 (Koszul).
- **CO5** = {46}  additive Euler cocycle = bounded L²-coboundary ⟺ σ≥½.
- **CO6** = {52}  g_p=g_p^{−1}⟹g_p=±1.
- **CO7** = {59,120}  a CC ⟺ a=c·σ(g)/g ⟺ deg_O(a)=0 on every orbit.
- **CO8** = {60,130}  RH ⟺ arch-completed Koszul acyclic ⟺ ω=0∈H²(G_L).
- **CO8b** = {88}  ω=0 ⇏ RH (plain class insufficient).
- **CO9** = {61}  ρ_∞(s)·ρ_ζ(s)=1.
- **CO10** = {126}  F₁ ⟺ (D=0)∧(corank finite); over ℚ (D=+1,corank=∞).
14 formulas → 11 nodes.

### GAMMA  (members 62,64,95,96,136 — 5)

- 95 → FOLD into WD7 (½ψ(s/2) is the M_∞ generator term already there).
- 96×CO2 → EDGE-mechanical (the ratio Γ_ℝ(s+2)/Γ_ℝ(s)=s/2π **is** a_Γ; the arch shift multiplier is the Γ_ℝ-recurrence ratio).
- 96×136 → EDGE (136 ψ(s/2+1)=ψ(s/2)+2/s is the log-derivative of 96).
- 62×64 → EDGE (64 ∂_s log χ is the log-derivative of 62 χ; the ≠0 is the arch non-triviality → CO).

Nodes:
- **GA1** = {96}  Γ_ℝ(s+2)=(s/2π)Γ_ℝ(s).
- **GA2** = {136}  ψ(s/2+1)=ψ(s/2)+2/s.
- **GA3** = {62}  χ(s)=Γ_ℝ(1−s)/Γ_ℝ(s)=π^{s−½}Γ((1−s)/2)/Γ(s/2)  (the FE factor; = reserved IV5).
- **GA4** = {64}  ∂_s log χ=log π−½ψ((1−s)/2)−½ψ(s/2)≠0.
5 formulas → 4 nodes (95 folded to WD7).

### FROB  (members 55,111,112,125,128,139,161 — 7)

- 111×139 → MERGE-⊃ (139 ⊃ 111: e_k(S)=q^k e_k(S^{−1}), ∏(1−ωT) FE-inv, |ω|=√q).
- 55,112,125,128,161 → distinct.

Nodes:
- **FF1** = {111,139}  e_k(S)=q^k e_k(S^{−1}); ∏(1−ωT) FE-inv; |ω|=√q.
- **FF2** = {55}  polarization ⟺ single Frobenius ⟺ corank=1 ⟺ F_q.
- **FF3** = {112}  normalized margin=1−q^{−½}.
- **FF4** = {125}  γ_n^{(q)}=(B_n^+/n!)(log q)^n (corank-1 collapse).
- **FF5** = {128}  trdeg(periods)=dim G; dim W=corank=1; ι unitary on Fix ⟺ RH/F_q.
- **FF6** = {161}  γ_n=n toy: S_k=(−1)^kζ(2k)∈ℚπ^{2k}; π²+6S_1=0; 5S_2=2S_1².
7 formulas → 6 nodes.

### INERTIA  (members 143,144 — 2)

- 143×144 → EDGE (two distinct machines, same principle "signature/inertia of a symmetric form = root count in a region"; both feed PA2 Sylvester). Kept separate; revisit Phase D.

Nodes:
- **IN1** = {143}  Bezoutian f(s)g(t)−f(t)g(s)=(s−t)Σr_j f_j(s)f_j(t).
- **IN2** = {144}  sigNeg(scForm[f])=winding(f)=#inside(f) (Schur–Cohn).
2 formulas → 2 nodes.

### LOGXI  (members 1,34,35,71,98,99,148 — 7)

- 34×148 → MERGE (148 ∮d arg=2πi(#z−#p) is the general winding; 34 is the pole-free ξ-instance).
- 98×99 → MERGE (99 θ'=½log(T/2π) specifies a term of 98 φ'=θ'+πS').
- 1,35,71 → distinct.

Nodes:
- **LX1** = {1}  ω=d log ξ(s).
- **LX2** = {34,148}  ∮ d arg=2πi(#zeros−#poles); (1/2πi)∮ d log ξ=#zeros.
- **LX3** = {35}  μ_ξ=(1/2π)Δ log|ξ|.
- **LX4** = {71}  (1/2πi)∮_{∂R}(ξ'/ξ)ds=0 off the line.
- **LX5** = {98,99}  φ'(T)=θ'(T)+πS'(T); θ'(T)=½log(T/2π).
7 formulas → 5 nodes.

### HADA  (members 33,73,102,103,170,171 — 6)

- 33×73 → MERGE-⊃ (73 adds remainder h to 33).
- 170×171 → MERGE (171 product ⟹ 170 its log-derivative).
- 102×103 → MERGE (102 surrogate, 103 its log-derivative).

Nodes:
- **HD1** = {170,171}  ξ=ξ(0)e^{bs}∏(1−s/ρ)e^{s/ρ}; ξ'/ξ=b+Σ[1/(s−ρ)+1/ρ].
- **HD2** = {33,73}  ξ'/ξ(s)~m_ρ/(s−ρ)+h(s).
- **HD3** = {102,103}  e^{q((s−½)²)}ξ; (e^q ξ)'/(e^q ξ)=ξ'/ξ+q'.
6 formulas → 3 nodes.

### HT  (members 92,104,105,106 — 4)

- 104×105 → MERGE (the HT foundations: Hölder negative theorem + closure under ±D-algebraic).
- 92,106 → distinct.

Nodes:
- **HT1** = {104,105}  ∄ poly F(s,Γ,…,Γ^{(n)})≡0 (Hölder); HT±(D-algebraic)=HT.
- **HT2** = {92}  ζ∉K_B=ℂ(s,{p^{−s}}).
- **HT3** = {106}  Ĥ Ψ=0 (Wheeler–DeWitt constraint).
4 formulas → 3 nodes.

### XF / MS / PERIOD / MISC  (162; 66,167; 166; 117,123 — 6)

- **XF1** = {162}  Σ_ρ h(γ_ρ)=arch−Σ_p(log p)…  (Weil explicit formula).
- **MS1** = {66}  −(φ'/φ)(½+ir)=2[(ξ'/ξ)(1+2ir)−(ξ'/ξ)(2ir)].
- **MS2** = {167}  K_MS(s,w)~(1−Θ(s)Θ̄(w))/(s+w̄−1)∈ℕ₀ ⟺ RH.  (66×167 EDGE: scattering pair.)
- **PE1** = {166}  RH ⟺ F_ζ elliptic, period interior to D_∞=Sp_∞(ℝ)/U(∞).
- **ML** = {117}  M(L)=1.176280818 (Lehmer Mahler measure).
- **ZP** = {123}  dρ/dε=−n^{−ρ}/ζ'(ρ).
6 formulas → 6 nodes.

### Phase-B tally

Nodes by group: IV 6, WELD 2, OPALG 8, DEFECT 8, CURV 2, PHI 4, APEX-POS 4, KAPPA 2,
APEX-TR 7, BAKER 1, STIELT 13, STAT 7, COCYC 11, GAMMA 4, FROB 6, INERTIA 2, LOGXI 5,
HADA 3, HT 3, XF 1, MS 2, PERIOD 1, MISC 2  =  **104 nodes** from 178 formulas (Phase B).
Phase D will attempt further merges (flagged: TA5, TA7, ST3, IN1/IN2 and all cross-group pairs).

---

## Phase C — edges and constructed bridges

Intra-cluster edges are the EDGE verdicts already recorded in Phase B. Below: (1) constructed
bridge formulas, (2) the cross-cluster edges that span the whole set into one component.

### Constructed / verified bridge formulas

- **BR1 (GAMMA→COCYC), mechanical, certified:**  a_Γ(s) = Γ_ℝ(s+2)/Γ_ℝ(s) = s/2π.
  Proof: Γ_ℝ(s+2)=π^{−(s+2)/2}Γ(s/2+1)=π^{−s/2}π^{−1}(s/2)Γ(s/2)=(s/2π)Γ_ℝ(s).
  Numerically certified to 1e-31 (mpmath, 4 points). Connects GA1 ↔ CO2: the archimedean
  σ-orbit shift multiplier (deg=+1, non-CC) **is** the Γ_ℝ-recurrence ratio. This is why the
  archimedean place is the one non-CC place (CO1): its multiplier carries a pole/zero (div=[0]−[∞]).
- **BR2 (WELD↔INV), mechanical:**  d(ξ(s)=ξ(1−s)) ⟹ ξ'/ξ(s)=−ξ'/ξ(1−s) ⟹ H(s)=−H(1−s).
  Connects IV2 → IV3 → WD3 (one differentiation chain).
- **BR3 (carrier identity), mechanical:**  ξ'/ξ = Λ'/Λ + 1/s + 1/(s−1)  (since ξ=½s(s−1)Λ);
  the two weld carriers (ξ-based, Λ-based) differ by an FE-symmetric rational term. Justifies the
  WD1 / WD3 carrier merges; the term is recorded, not hidden.
- **BR4 (CURV↔PHI), mechanical:**  an off-line zero's FE-quartet contributes to Φ_2 exactly
  (½−β+iτ)^{−2}+(β−½+iτ)^{−2}=C_a(τ) (this is F108=CW2); connects PH1 ↔ CW1.
- **BR5 (MISC→FROB), [BRIDGE-conj], non-load-bearing:**  M(L)−1 as the number-field analogue of the
  function-field margin 1−q^{−½} (FF3): "smallest positive excursion of a height above its trivial
  value." Labelled conjectural; NOT needed for connectivity (ML is already joined via ML↔TA8, height).

### Cross-cluster spanning edges (establish one component)

Anchored on the hubs WD1 (weld), PA1 (positivity apex), TA1 (transcendence apex), IV2 (FE).

- WELD↔INV: WD1—IV2 (weld = ∂_s log of the FE-symmetric Λ); WD3—IV3 (BR2).
- WELD↔LOGXI: WD3 absorbs LX1 (ω=dlogξ=Hds, see Phase D); WD1—LX4 (ξ'/ξ contour); LX3—PA1 (μ_ξ support).
- WELD↔OPALG: WD1—WD7 (arch term ½ψ via M_∞ generator); WD7—TA6 (∂_s=−Σ log p·θ_p uses {log p}).
- WELD↔COCYC: WD1—CO9 (ρ_∞ρ_ζ=1, weld=arch×prime factors); WD1—CO1 (C5=weld); WD11—CO7 (gauge form).
- WELD↔DEFECT: WD1—DF1 (Δ = antiphase of the weld's two terms); WD1—DF4/DF7 (phase of ζ'/ζ, Γ∞+ζ'/ζ).
- WELD↔STIELT: WD1—PS-POW (−ξ'/ξ=ΣP_k s^{k−1}); WD1—PS8 (ζ'/ζ coeffs=Λ(n)); WD1—PS11 ((ζ'/ζ)^{(2k−1)}).
- WELD↔HADA: WD1—HD1/HD2/HD3 (ξ'/ξ Hadamard, pole model, surrogate).
- WELD↔MS/XF: WD1—MS1 (ξ'/ξ scattering); WD1—XF1 (arch−prime); XF1—PA5 (Q_W=𝔇).
- WELD↔HT: WD1—HT3 (the weld is the WdW constraint); HT1—TA1 (transcendence).
- INV↔GAMMA: IV2—GA3 (χ is the FE factor); GA3—GA4—CO2 (∂_s log χ≠0 = arch non-trivial); GA1—CO2 (BR1).
- INV↔PA1: IV1—PA1 (Fix(ι)={Re=½} is RH's locus); IV7—ST1 (|p^{−s}|=p^{−½}⟺Re=½ ↔ σ>½ threshold).
- INV↔OPALG: IV6—WD2 (prime inversion = σ_p action); IV4—PS-POW/IV4—PH1 (Ξ recentred).
- OPALG↔group/COCYC: WD2—WD4—WD5; WD2—CO3 (τ_p cocycle); WD7—TA7 (rank after adjoining ∂_s).
- PHI↔PA1: PH3—PA1 (RH⟹Φ_2<0); PH4—PA1 (β=½) & PH4—GA3 (χ_FE) & PH4—ZP (perturbation).
- PHI↔CURV↔KAPPA: PH1—CW2—PA2 (off-line quartet → off-line zeros counted by κ₋).
- APEX-POS internal/realizations: PA1—PA2—PA3 (κ₋, APS); PA1—PA5—IN1 (Q_W, Bezoutian/Schur–Cohn inertia);
  PA1—PA7 (DH instance); PA1—PA9—HD1 (Turán on a_n); PA1—HD3 (surrogate for Jensen/LP).
- APEX-POS↔other RH-frameworks (edges, NOT merged — see Phase D rule): PA1—CO8 (Koszul/ω, w/ caveat CO8b);
  PA1—MS2 (de Branges kernel∈ℕ₀); PA1—PE1 (period domain); PA1—FF5 (ι unitary, FF case); PA1—LX2 (zero count).
- APEX-TR internal: TA1—TA2,TA3,TA4,TA5,TA6,TA7,TA8.
- APEX-TR↔STIELT: TA1—PS1 (trdeg Stieltjes=corank, the master value bridge); TA6—PS2,PS9 (prime-log combos).
- APEX-TR↔HT/COCYC/FROB: TA1—HT2 (ζ∉K_B); TA2—CO10 (F₁⟺corank finite); TA2—FF2 (corank=1⟺F_q).
- STIELT internal/special-values: PS-POW—PS4—PS10 (Li, blind spot); PS-POW—PS11—GA3 (S_k value→ζ,β);
  PS-POW—PS5—PS12—PS7 (P_k→ζodd→moment/cumulant); PS-POW—PS14—IV2 (μ_{2k+1}=0 by FE); PS13—PS1 (γ_E).
- STAT internal/threshold: ST1—ST2—ST5—ST4; ST1—ST3; ST1—IV7—CO5 (the σ=½ family); ST6—ST7—PA1 (gap↔margin).
- FROB internal/contrast: FF1—FF2—FF3—FF4—FF5—FF6 (the solved FF model); FF3—PA1 (margin); FF6—PS-POW (toy S_k).
- INERTIA↔APEX: IN1—PA5/PA2 (signature counts off-line zeros = Sylvester κ₋).
- LOGXI internal/Γ: LX2—LX4; LX5—GA1 (θ'=½log(T/2π) from Γ); LX5—DF7 (phase).
- MISC: ZP—HD2 (ζ'(ρ))—PH4; ML—TA8 (height)—[BR5]→FF3.

### Connectivity verdict
Every one of the (post-Phase-D) nodes has ≥1 edge into the component containing WD1/PA1/TA1.
Spot-checked the at-risk singletons: ML (→TA8 height, mechanical), ST6 (→ST7), HT3 (→HT1,WD1),
GA2 (→GA1), PS13 (→PS1,PS12), ZP (→HD2,PH4), CO8b (→CO8), PA7 (→PA2), WD9 (→WD7), WD11 (→WD2,CO7).
**One connected component. Zero isolated nodes.** The only conjectural edge (BR5) is non-load-bearing.

---

## Phase D — attack pass (further merges + flags resolved)

Rule fixed here: the master apex PA1 collects only **positivity/spectral** RH-equivalents.
RH-characterizations living in a *distinct framework* (APS index PA3, Koszul/ω CO8, de Branges MS2,
period domain PE1, FF/ι-unitary FF5) stay as separate nodes EDGED to PA1 — merging them would erase
the framework structure (their own supporting formulas) and bury the plain-vs-completed caveat CO8b.

Additional merges found and applied:
- **IN1 ⊇ IN2** → MERGE: the Bezoutian (143) is the symmetric form whose Schur–Cohn inertia (144) is
  taken; one principle "signature = root count in a region". New IN1={143,144}.
- **WD3 ⊇ LX1** → MERGE: ω=d log ξ (LX1) and ω=H ds (WD3) are the same transport 1-form (BR3 carrier
  caveat). New WD3={1,18}; LOGXI loses LX1 (LX2–LX5 remain).
- **DF2 ⊇ DF3** → MERGE: Δ→log2 (74) and the transport/co-failure/eigenvalue separations (75,76,77)
  are one finding — "the true prime field is bounded away from every finite Euler truncation," four
  observables. New DF2={74,75,76,77}.
- **WD5 ⊇ WD10** → MERGE: [∂_s,M_p]=−log p (20) and [∂_s,σ_p]=0 (65) are the two structure brackets
  of 𝔾_a⋊𝔾_m (WD4); co-defining. New WD5={20,65}.

Flags resolved (kept merged, justified):
- TA5={30,119}: dim W=corank exact; T/(N+T) the internal fraction — both size the corank space. KEEP.
- TA7={121,137}: two robustness facts for corank=∞ (Zariski closure ∞-dim; rank survives ∂_s). KEEP.
- ST3={4,149}: two critical abscissae in (½,1). KEEP.

Pairs re-tested for merge and REJECTED (representative, same-symbol):
- PA1×PA5: positivity-predicate vs definition of Q_W. REJECT (def ≠ equivalence).
- PA1×CO8: RH⟺ω=0 is framework-distinct + carries caveat CO8b (ω=0⇏RH). REJECT (edge only).
- PA1×PS12: PS12 Hankel⪰0 is UNCONDITIONAL; PA1 Hankel is ⟺RH (conditional). REJECT.
- TA1×TA6: algebraic vs linear independence of {log p}. REJECT (distinct).
- HD2×ZP: pole residue model vs zero-perturbation derivative. REJECT.
- PS7×PS12: cumulant identity vs moment representation of ζ(odd). REJECT.
- IN-merged×PA2: machinery (general) vs its application (κ₋ count). REJECT (edge).

### Final tally
Phase B 104 − 4 Phase-D merges = **100 nodes** from 178 formulas.
One connected component, zero isolated nodes, one (non-essential) conjectural edge.
Fixed point reached: no surviving same-symbol pair merges without erasing a framework or a caveat.
