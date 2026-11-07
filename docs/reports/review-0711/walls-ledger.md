# Walls ledger — status quo

**Corpus checkpoint:** commit `bf10668155` plus the working tree of 2026-11-07.

Three wall families carry the frontier. **Σ** is the critical sign of the window form, **Π** the precision and production of the prime count, **Γ** the selection of ζ and reflection of its zeros. RH ⇔ `κ=0` ⇔ `a*(ζ)=⊤` ⇔ `λ*(c)→0` ⇔ `N_d=0` for infinitely many `d` ⇔ ZAL ∧ AAL [L]. These receivers do not supply their arithmetic inputs.

[Frontier](../rh-current-frontier-map.md): **38 live formulations, 9 candidates** (APF, EGC, EWJ, FEL, IRK, MSC, RFHM, W1C, WBF). HJ→PA and BSH→CDC are aliases. [Scoped obstructions](../rh-killed-routes.md) separate failed mechanisms from open replacements.

- **Σ is the sign of every window, and nothing else.** RH ⇔ some weight is admissible on every window ⇔ `Ψ=½log H₁` is locally bounded ⇔ `Ω_ψ(a,X)≥0` on the whole plane [L]. The critical curve carries no further information: the high-conductor critical threshold equals `⨅_A windowThreshold(A) ≥ c₀e^{6a*(ζ)}` (Σ129) [S], and the low-packet polar payment at every ratio is RH (Σ130) [L]. Every certificate past the abscissa is a tail-good condition (Σ128). Parabolic structure cannot select `t=0`; the theta amplitude is not all-base torus-positive; Gårding fails on deep atoms [L].
- **Π is the same sign on the prime side.** One smoothed prime count matches the pole square within `W(f)` [L]. All unconditional savings sit at the VK curve; under RH the stencil exponent lies in `[¼,½]` (Π70). Zeros are the power-law kernel of the cut system (Π81). Farey discrepancy, the Mertens function and the Euler characteristic of the prime-star nerve are one number (Π105). The dark range runs from the Kronecker scale `≈log T`, where conditional tail laws stop (Π96), past `≈(log T)²`, where absolute non-alignment begins (Π87), to `exp((log T)^{2/3})` [L/D]. The first return of the prime orbit is bracketed at every precision; at bounded harmonic defect it exceeds `exp(c(log N)^{3/2}/log log N)` (Π94).
- **Γ is the same sign on the zero side.** RH splits as ZAL ∧ AAL [L]. Failure of AAL is one rigid finite oscillation of the prime error (Γ80, Γ81). Every one-off countermodel — continuous, discrete, integer-norm, rational-prime with multiplicative linear counting — fails at the critical line (Γ73, Γ124). A return at a right zero is tail-bad at every cut (Γ115, Γ123). ζ is isolated in three metrics (Γ84). Universal damping is not a law of wave dynamics, not even with the functional equation at genus two (Γ118); the separating law is the count (Γ96, Γ98). On the modular horizon, long closed horocycles equidistribute at rate `y^{1/2}` unconditionally and at `y^{3/4}` iff RH (Γ121); every resonant mode decays at `e^{−t/4}` iff RH (Γ122).

Status: **Solved** (the face is a theorem), **Partially solved**, **Sharpened** (open, with its exact form a theorem), **Open**, **No-go** (the mechanism is refuted), **Classified** (answered by a classification or identification), **Reduced** (theorem-level equivalent of the wall named), **Scoped** (a theorem whose stated hypothesis needs its scope read). Strength: **RH**, **≥qRH**, **sub**, **indep.**, **identity**, **method**. Evidence: `[L]` Lean source; `[K]` Lean with transitive axiom audit; `[S]` Lean source unfinished, unintegrated or uncommitted; `[P]` paper only; `[D]` deduction; `[N]` numerical; `[C]` classical, not formalized.

Notation. Windows `[−a,a]`; `c_ψ(t)=W(ψ(·−t),ψ)`; `w_n=Λ(n)n^{−1/2}`; `δ` sliver width `2c−log n` (in zero statements the depth `Re ρ−½`); `ρ³=ρ+1`; `a_k=weilFloorApertureTower k`, `181/500<a₀<181/500+5·10⁻⁷`; `λ*(c)` best margin; `N_d` non-real root count of `R_d(Ξ)`; `E` exceptional values of ζ; `r` anchor reflection, `L=artanh r`; `Ψ=½log H₁`, `q=Ψ′`; `ϱ` pseudo-hyperbolic ratio; `L=log T` in near-line statements, `L=log|t|`, `ℓ=log L` in orbit statements; `I(w)` inner field; `G` Green kernel of `Re s>½`; `R=c⁸/log N`; `W₈(H)=∫H²e^{−8y}`; `D_N(y)=Σ_{n≤N}Λ(n)n^{−½}cos(y log n)`; `Q₁=⌊(log N)^{13/32}⌋`; `R_c`, `R_high` whole-space and high-conductor critical thresholds; `R(y,η)` first return of the primes `≤y` at precision `η`; `E_y` Euler head, `ζM_y` Euler tail; `A_φ(y)` mean of a pseudo-Eisenstein series along the closed horocycle of height `y`.

## Σ — critical sign

| Wall | Status | Strength | Content |
|---|---|---|---|
| Σ1 Weil's sign | Sharpened | RH | RH ⇔ `Q≥0` on every window ⇔ `a*(ζ)=⊤` ⇔ two-site PD ⇔ band at the centre in both sectors ⇔ Stieltjes jet moments ⇔ lattice Schur parameters in `(−1,1)` ⇔ `windowThreshold≡⊤` ⇔ every critical threshold `=⊤` ⇔ `1∈ℋ(c)` ∀c ⇔ `λ*(c)→0` ⇔ every window cone nonempty ⇔ every growth step a translation contraction ⇔ Cayley ladders NSD ⇔ Suzuki first variation `≥0` ⇔ mollified Jensen stability ⇔ Krein positivity ⇔ prime-blind positivity ⇔ odd BPY Poincaré inequality ⇔ no finite contact ⇔ outer predictor at every window ⇔ every echo in its Schur band ⇔ every orbit correlation relatively compact ⇔ `Ω_ψ(a,X)≥0` ⇔ `Ψ` locally bounded [L]. |
| Σ1a Critical overlap and receivers | Solved | — | `c*_N≍L(log L)²`; tilted-spline and unit-bump receivers; one Beurling profile realizes every finite rational Gram [L]. |
| Σ1b Subcritical regime | Solved | sub | Complete matrix PD for `1≤c≤(log N)^α`, `α<1/8` [L]. |
| Σ1c Joint shell–pole payment | Solved | sub | Prime-successor edges pay nonconstant packet mass [L]. |
| Σ1d General profiles | Partially solved | sub | Every compact C² profile: energy `≥ae^{−Bc}‖x‖²` on conductors `≤N^θ`, `θ<¼`, `c≤b log log N`; subpolynomial spans carry super-log-log clocks [L]. |
| Σ1e Conductor barrier | Partially solved | sub | Count form uniform for `m=o(c)`; the low block `m≤Q₁` keeps half its diagonal plus its polar part at every ratio [K]. |
| Σ1f Defect-only confinement | No-go | — | `Q<2^k` witnesses [L]. |
| Σ1g Haar / Gamma graph | Partially solved | sub | All-detail prime–pole cancellation `O(e^{−√log Y/92160000})`; index `≤R+A`; growing Euler heads have unbounded index; nonfirst source keeps `1−ε` of Gamma [L]. Either sign of the unnormalized wave and the complete odd payment are open. |
| Σ1h Smooth logarithmic profile | Solved (to `ε₀c*`) | sub | Positive to `ε₀L(log L)²` [L]. |
| Σ1i Second order on horizon blocks | Classified | — | `κQ(H)+(βJ/K)∫e^{−(β+1)y}H²` [L]. |
| Σ1j Critical-curve decomposition | Partially solved | sub | Fixed independent mean-zero periodic families eventually PD at every ratio; distinct primitive conductors decouple at second order; frequency pole of order `β+1` with untwisted finite part `βJ/K` [L]. Growing families and coalescing frequencies open. |
| Σ1k Whole space at one critical multiple | Solved | sub | PD at `c≤2K₀(log N)^{1/8}` with complete Schur payment [K]. Every `K>0` is B6. Alternative receiver: cofinally `xiDampedSourceWork(n+4)≤2` ⇔ RH [L]. |
| Σ1l Window threshold | Reduced (to Σ56) | RH | `windowThreshold A=⊤ ⇔ A/2≤a*(ζ)`; `=⊤` for `A≤2a_k`; every critical pencil positive there [L]. If `windowThreshold A₀=⊤` then `windowThreshold A≥c₀e^{3A₀}` for every `A` [S]. |
| Σ1m Polarization inheritance | Partially solved | sub | Twisted sectors with positive scalar second order; short windows; cosh hyperplane [L]. |
| Σ1n Bulk below the grid | Classified | — | Reads only the pole [L]. |
| Σ1o Aperture-independent weighted floor | Solved (size-only) | — | `Q(H)≥−F(p)∫e^{−pu}H²`, `p>1`, explicit `F(p)` [L]. |
| Σ1p Terminal windows | Classified | — | Polar source with nontrivial kernel; long-index cancellation on near rows [L]. |
| Σ1q Receiving charges | Classified | — | Capacity `log log N+O(1)`; receiving vectors with vanishing physical energy read at `1/80`; gcd-twisted charges split into four channels; periodic `F`: `J_N=O(log N)` iff gcd profile; non-gcd twists have `J_N≥η²(log N)²/(16M²)` for every period `M` up to the admissible scale `M₀(N)→∞`, `M₀(N)≤log log N`, and their neutral charges are coercive [L/K]. Near-gcd families and periods beyond `M₀(N)` open. |
| Σ1r Conductor packets and correctors | Classified | — | Terminal sources concentrate at the pole; correctors cannot improve zero-source windows [L]. |
| Σ1s Far reserve and the high-conductor threshold | Classified | sub | `farMargin R=3D/(8R)−C−C′R`; coercive on conductors `>N^θ` for `0<R<R*`; joint complement of the low packet coercive for `0<R≤min(1,5R*/6)` [L]. On the complement of `V_{Q₁}`, eventual PD and PSD hold exactly below `R_high=⨅_A windowThreshold(A)` (Σ129) [S]. |
| Σ1t Prefix Schur cost | Partially solved | — | `(tail z)ᵀ(D−BᵀA⁻¹B)(tail z)=zᵀWz−rᵀA⁻¹r`, `A⁻¹≤20`; floor `(a/2)e^{−Bc}‖z‖²` on conductor blocks `≤(log N)^{1/32}` [L]. |
| Σ2 Edge, zero modes, hard Lefschetz | Sharpened | RH | RH ⇔ HL on the PSD locus; zero modes radical and two-site; Hodge index = Metzler sign of the Cayley ladder = Li positivity [L]. |
| Σ2a Interior-gap continuation | No-go | — | `κ(d)=1_{3∣d}` [L]. |
| Σ2b Edge singularity | Classified | — | No smooth eigenfunction, constrained ground state or capacity maximizer [L]. |
| Σ3 Stars and dilation monodromy | Partially solved | — / RH | Stars isometric; squarefree prime complex ≃ wedge of spheres over odd squarefree `N/2<m≤N` [L]. |
| Σ3a Coprime stratum | Sharpened | RH | Redheffer `det=M(N)` = reduced Euler characteristic of the nerve up to sign; `χ̃=Ω±(√N)`; RH ⇔ `χ̃=O(N^{½+δ})` [L]. |
| Σ4 Finite index / heat count | Sharpened | ≥qRH (`K_ζ`); RH (`K_ζ⊠K_ζ`) | `κ<∞` ⇒ Lindelöf; RH ⇔ index `0`; window index counts critical lengths; `N_d` bounded ⇔ `κ<∞`; under AAL finite index ⇔ RH [L]. |
| Σ5 Collision quantum / window integer | Reduced (to Π17) | RH | Index `0` ⇔ Wiener–Hopf invertibility [L]. |
| Σ6 Rank / degree uniformity | Partially solved | RH | TH ranks `≤14` PD for `0<a≤½`, the rank-14 payment `∫p²·current≥aE/250` for `deg p≤13`; rank `N` on the VK collar; rank `N` from verified height `41+6(N+2)log(N+2)` (`a≤½`), `D(N+1)³+1` (`a≤¾`); first-atom tails PD at every rank; `θ₁+θ₂` and every chain `q^n` PD at every rank [L]. All ranks reduce to the frequency-adaptive finite head of signed unequal pairs; the infinite remainder beyond a cutoff `≍|b|/2` costs at most half the first-atom Gamma reserve [S]. |
| Σ7 Window Markov capacity | Sharpened | RH | RH ⇔ `R≤½` on the odd sector [L]. |
| Σ8 Realization | Sharpened | RH | Every window has an `ℓ²(zeros)` realization ⇔ RH; no finite-dimensional norm realization on any positive window; `N` integer slopes need rank `≥N` under RH [L]. |
| Σ9 Explicit image / resolvent | Partially solved | RH in strip | Depth identity for `σ>1` [L]. |
| Σ10 Local signatures and gluing | Solved | — | `κ(φ_c)=κ+1` [L]. |
| Σ11 Product-formula gluing of the pole | Classified | — | Local poles add squares [L]. |
| Σ12 Running counterterm | Solved | — | `log N−γ` cancels the prime diagonal [L]. |
| Σ13 Tensor amplification | No-go | — | `K_ζ^n` PD ⇔ RH [L]. |
| Σ14 Deformation to a positive model | No-go as free input | — | Crossing-free path ⇔ PD [L]. |
| Σ15 Separable assemblies | Classified (no-go) | — | Additive prime-tower assemblies have zero coprime cross-differences; the cubic-spline correlation has a nonzero one [L]. |
| Σ16 Prime–pole coherence | Solved (identity) | — | Complete form = jump + incidence − shell + diagonal + boundary [L]. |
| Σ17 Inter-tower coupling | Sharpened | RH | Bounded Gaussian-damped two-prime coupling ⇔ RH; undamped coupling on one cone ⇒ AAL, with ZAL ⇔ RH [L]. |
| Σ18 Exact SOS on a two-prime lattice | Open | RH | Generic Hecke orbit carries the full Hodge defect [L]. |
| Σ19 Rank-one intertwining coefficient | Sharpened | RH | `κ_Hodge=#` band poles of `Λ(s)/Λ(s+1)` [L]. |
| Σ20 Scheduled prime sums | Open | RH | FU fixed-horizon payment; CFC tail lower bound; RP eventual linear floor exact, sublinear impossible; LI response floor `R(t)≥−C_εe^{εt}` suffices [L]. |
| Σ21 Extension / carrier | Classified | — | Escape, mixing, height decay ⇒ `κ∈{0,∞}` [L]. |
| Σ22 Lefschetz operators | Classified | — | Overlap-flow HL on the HR locus is RH [L]. |
| Σ23 Connected links | No-go (pure dilation complex) | — | Each tower is a clique; star-nerve signed face count is `M(N)` [L]. |
| Σ24 Finite divisor | Solved | — | Coercive off `i/2` [L]. |
| Σ25 Separate semilocal positive factors | No-go (specified factors) | — | Sonin factor and signed prime transports indefinite beyond `A>½log p`; complete form positive through `181/500` [L]. |
| Σ26 Approximation by RH-true objects | Classified | — | Closure class Laguerre–Pólya [L/D]. |
| Σ27 Window stages | Partially solved | sub | Floors `(1/20000)/2^k` on `a_k`; `a_k−a₀<10^{−7800000}`; `a_k<0.3621<½log 3` [L]. The tower supplies no window past `≈0.3621`. |
| Σ28 Window negativity budget | Sharpened | ≥qRH (exp `<½`); RH (subexp.) | Ground-energy floor `−Ce^{2σA}` ⇔ zero width `≤σ`; polar ground energy `μ₀(B)≥−C_εe^{εB}` ∀ε ⇒ AAL, and RH ⇔ ZAL ∧ that floor [L]. |
| Σ29 Low-frequency localization | Solved | — | Negativity only at the poles and below `τ₀(a)` [L]. |
| Σ30 The stage step | Reduced | RH (induction); each stage sub | Composite stages carry no fold; single-prime transport for all `A` ⇔ RH; transport across `p=2` unconditional [L]. |
| Σ31 Positivity across dimension zero | Classified | = Σ1 | Bare domination ⇔ `Q≥0` [L/D]. |
| Σ32 Prime-blind positivity / calibration | Sharpened | RH | Full positive cone `{Λ}` under RH, empty otherwise; one Euler factor suffices; blind energy `(1/π)∫\|𝓜f\|²(θ′+1−Re ζ(½+it))`; Carlson threshold `e^{(π/2)\|t\|}` [L]. |
| Σ33 Tate positivity horizon | Classified | — | Positive Tate dimensions `[0,κ(A)]`, `κ(A)→0`; finite templates iff spread `<27/5`; dimension one Tate-positive exactly on windows `A≤log 5` [L]. |
| Σ34 Canonical-degree horizon | Classified | — | Soft deformations paid by counts have horizon `≍e^{−A/2}` [L/D]. |
| Σ35 Canonical system of the tower | Solved (precontact) | identity | Lattice Levinson; precontact de Branges spaces; canonical system `H=diag(H₁,H₂)`, `H₁H₂=1`; anchor identity and flux; complete sampling bases [L]. |
| Σ36 Rational Hecke-graph reading | Solved (identity) | — | Window positivity ⇔ every finite rational Hecke graph of smaller spread [L]. |
| Σ37 Lattice canonical system | Solved (identity) | — | Window ⇔ its lattices [L]. |
| Σ38 Two-site decision | Classified | — | RH ⇔ two-site PD; `(γ,v)` decide the line [L]. |
| Σ39 Trivial-divisor transmission | Solved (identity) | — | Collar Hankel form, inertia `(1,∞)` [L]. |
| Σ40 Degenerations are curves | Classified | — | Degenerate lattice windows are finite curves [L]. |
| Σ41 Aperture–depth duality | Classified | — | Ground-energy fall rate = zero width; positivity at level `a` ⇒ `\|β−½\|<10⁶exp(−a/(1200log(\|γ\|+3)))`; `N(t,t+1]≤240log(\|t\|+3)`; positivity at `λ·½log(T/2π)`, `λ>1`, ⇒ depth `<exp(−c log³(T/2π))`; two-lobe cluster bound [L]. |
| Σ42 Markov and variance-free ground states | No-go | — | Markov part dies at `e^{−3/4}`; variance-dropped certificates fail for `c>273/400`; prime 3 as collar potential fails for `c≥287/500` [L/K]. |
| Σ43 Pole-charged ground-state calculus | Solved (identity) | — | `Ẑ(Φωu)=J_{Φω}(u)+∫u²ω𝒢_S(ω)+2V_s−2V_c` [L]. |
| Σ44 Collar locality of the kick | Classified | — | Collar ratio `2w_ne^h` sharp [L/D]. |
| Σ45 Reflection pairs and parity sectors | Solved (identity) | — | `W(f±f∘R)=2W(f)±2𝒞_m(f)`; coupling truncates to `n≤e^{2c}` [L]. |
| Σ46 Frustration of the odd sector | Classified | — | Odd prime reflection anti-Markov, not removable by gauge; OWU needs only compact C² odd `F` with `∫F sinh(x/2)=0` [L]. |
| Σ47 Odd unit window | Open (structural); rung available | sub | Positivity ⇔ `w₂∈unitBandWeights`; margin `≈2·10⁻⁴` [L/N]; follows from `RHVerifiedThrough(windowHeight ½)` [L]. |
| Σ48 Criticality | Classified | — | Zero slack; `1` is the only all-window multiplier [L/D]. |
| Σ49 Reality by continuation | Sharpened | RH | Real collision iff `Re Q(0)=Im Q′(0)=0`; exclusion at every positive time ⇔ RH; `c d²/log X≤Λ_X≤(6600/9991+ε)/log X` [L]. |
| Σ50 Below `log 4` | Sharpened; rung available | sub | Positivity ⇔ two-weight band ⇔ Hodge index ⇔ Künneth effectivity ⇔ `1∈ℋ(c)`; primitive `h¹` coercive for `a≤181/500` [L]. |
| Σ51 Sectors as moment problems | Solved (identity) | — | Even Hamburger, odd shifted Hamburger, window Stieltjes [L]. |
| Σ52 Prime-weight confinement | Solved (sharp) | — | Outer law `\|λ(n₀)\|≤√n₀(log(1/δ)+B)`; bands close at rate `2Ce^{Kn−c/1104}` [L]. |
| Σ53 Size versus sign of the kicks | Classified | — | Size certificates die at `E_c≥1`, crossing `c*∈(½log5,½log6]`; `H<0` at half-width `≤21/40` [L]. |
| Σ54 Sector order of the archimedean place | Classified | — | Gamma ladder; pole `+` square even, `−` square odd [L]. |
| Σ55 Euler-stage phase repulsion | Solved (above horizon) | — | Phase lattice above `2πe^{W_a}` for every real finite carrier [L]. |
| Σ56 Onset aperture of `ζ` | Sharpened | RH | RH ⇔ `a*(ζ)=⊤`; off RH contact is attained; ground energy crosses zero at most once; `log R_high≥6a*(ζ)+log c₀` [L/S]. |
| Σ57 Perron / Beurling–Deny | Classified (no-go past `log ρ`) | — | Even band Markov iff `c≤log ρ` [L]. |
| Σ58 Window visibility law | Classified | — | Universal pair-energy threshold; contact law at `c log T` [L]. |
| Σ59 Shielded zeros at fixed aperture | No-go | — | Cut crystal hides any fixed depth to aperture `(log T)/36` [L]. |
| Σ60 Switching to balance | No-go | — | Every nonconstant sign gauge creates negative conductance [L]. |
| Σ61 Hardy criticality | Sharpened | RH | `ℋ(c)` closed antitone interval; optimal Hardy term ⇔ RH [L]. |
| Σ62 Trace theory of certificates | Classified | — | `𝒥=𝒥_reg+𝒦`; Weil's form reads no point values [L]. |
| Σ63 Trivial zeros at the centre | Solved (identity) | — | Trivial zeros are not part of the frustration [L]. |
| Σ64 Signed certificate format | Solved (identity) | — | Neutral even gauge and shifted ground state represent both sectors on every window [L]. |
| Σ65 Finite-template reduction | No-go at spread `27/5` | — | [L]. |
| Σ66 Contact of the de Branges chain | Sharpened | RH | RH ⇔ no finite contact; contact forces kernel divergence; `q∈L¹` up to contact ⇒ RH; contact scaling `\|q\|≈(1+1/γ)m` [L]. Exact form Σ113. |
| Σ67 Untwisted–twisted coupling | Reduced (to head thresholds) | RH (all `d`) | Dirichlet-shift companions cancel tails; `d=2` unconditional; all `d` ⇔ RH [L]. |
| Σ68 Gauge freedom | Classified | — | Neutral gauges act only in the pole direction [L]. |
| Σ69 Width at bounded aperture | No-go | — | Every bounded aperture is consistent with every width [L]. |
| Σ70 Free-weight margin and bands | Sharpened | RH (sign); sub (rate) | `λ*(c)≤K exp(3c−(π/6)e^{2(c−13/12)})`; `λ*(a_k)≥(1/20000)/2^k`; bands of width `≥λ*√n`, `≤Ce^{Kn−c/1104}` [L]. RH ⇔ `λ*→0`; decay law open. |
| Σ71 Datum of the window cone | Classified | — | Critical log-conductor `=−λ*(c)`; datum region convex, `⊆{β≤1}`, `(β,0)` in it forces `β=1`, `(1,0)` in it ⇔ RH; `β≤1+K(1+\|s\|)/c` [L]. |
| Σ72 Centre jets and the slice band | Partially solved | RH (all orders); sub (band) | Taylor coefficients PF₂₀₀; slice coefficients `≥0` for `\|t\|≤133/2`; off-line zeros have `\|Im\|>67`; the fourth reciprocal trace excludes every zero with `\|Im ρ\|≤12` [L]. |
| Σ73 Hausdorff rows | Sharpened | RH | Rows nonnegative for `r≥min(C₀(k+1)²,S(k))`, `S(k)=⌈20K⌉+⌈KH²⌉+1`, `K=10(k+1)+20`, `H=max(e¹²,42(k+1)+44K)`; remaining entries ⇔ RH; HJ exterior diagonal at `218/25` [L]. |
| Σ74 Heat-grid detectors | Sharpened | RH | Two fixed grids at every degree ⇔ RH; bounded chirp ⇔ RH [L]. |
| Σ75 Hamiltonian density | Solved | identity | Finite Grams AC before contact, no atom, no singular part [L]. |
| Σ76 Theta endpoint energy | Partially solved | RH | `D_t+Q_t/2≥0`; boundedness ∀`0<t<½` ⇔ RH; one bound on a shrinking band [L]. |
| Σ77 Renewal joint nodes | Sharpened | RH | `det₂` represents `D`, not Ξ; two-ended formula recovers Ξ [L]. |
| Σ78 Cosine-source zero loss | Partially solved | RH | Strict Laguerre sign for `h≥½` and above VK; sign at every `0<h<½` ⇔ RH [L]. |
| Σ79 Quartic Schur charge | Partially solved | RH | Small late charges suffice; late charge `≤HS/400` [L]. |
| Σ80 Anchored cubic gate | Sharpened | RH | Trace class; enclosed multiplicity `≤` trace norm [L]. |
| Σ81 Center-tail fibres | No-go (numerical) | — | Tail density positive at 7 of the first 30 zeros [N/D]. |
| Σ82 Finite-rung principle | Partially solved | sub | Window, Li, Hausdorff, heat, Jensen, PF, slice, theta rungs from verified height; RH through height 67 in Lean [L]. No finite rung decides RH. |
| Σ83 Floors suffice | Solved (receiver) | RH | `−C∫F²` on odd tests, or `−C_σe^{2σr}∫F²` ∀σ>0, ⇒ RH [L]. |
| Σ84 Width axis | Classified | ≥qRH (interior) | Every interior value of every width parameter is a zero-free strip; unconditional savings sit at VK [L/D]. |
| Σ85 Anchor flow | Solved (identity); control open | RH | `L′=q−sinh 2L`; `Ψ=L+θ`; `(log K)′=2cosh 2L` [L]. |
| Σ86 Scale-invariant flow bound | Open | sub | Bounded variation of `r` free of `1/μ` [D]. |
| Σ87 Compactness at a critical ratio | Solved (assembly) | sub (each ratio) | Γ-liminf with weight `α_R` at every `R`; bounded form gives strong `L²` limits; physical and Fourier tails give precompactness [L]. Assembly: high-conductor nonpositive directions at `R<⨅wT` produce, by one-sided spline mollification and Kolmogorov–Riesz, a strong `L²+L¹` limit whose window mollifications have negative critical pencil; hence `R_high≥⨅wT` [S]. |
| Σ88 Limit pencil at a fixed ratio | Classified | sub | `κQ+(7J/R)∫e^{−8y}H²≥0` on smooth families is a window statement; nonpositive directions meet the top window of length `(1/8)log R+O(1)` [S]. |
| Σ89 Parabolic blindness | No-go | — | `Φe^{−τx²}` has the same parabolic laws and non-real zeros for `t<τ` [L]. |
| Σ90 Central inequality | Classified | stronger than RH | `g_t²≥c·min(t,log⁻²X)` everywhere ⇒ RH and `c(m+1)≤24` [L]. |
| Σ91 Gap dynamics | Solved (laws) | identity | Gap law, mesh bounds, profile gap `16/k≤μ²≤24/(k+1)`, maximum principle; all assume reality in the cylinder [L]. |
| Σ92 Crystal on typical heights | Partially solved | sub | `Λ_X log X→0` on density one; exceptional measure `≤T^{θ(κ)}`, `θ(κ)=1−κ³/41943040000`; crystal law outside `δT` [L]. |
| Σ93 Collision frequency | Sharpened | RH | `N(σ)<1` excludes a double zero; multiplicity `≤(3300/9991+ε)log X` [L]. |
| Σ94 Depth law | Partially solved | sub | Isolated simple zero: `d−7η≤Λ_Xlog(X/2π)≤d+17η` [L]; crowded and multiple zeros open. |
| Σ95 Pointwise two-prime payment | No-go | — | Negative at centre `log 6` [L]. |
| Σ96 Euler-operator theta spectrum | Solved (identity) | identity | `S=Π_pT_pA`, `T_p=(1−2cos(b log p)σ_p+σ_p²)^{−1}`; `A` not a positive Laplace mixture [L]. |
| Σ97 Torus-uniform theta positivity | No-go (numerical) | — | Negative once primes `≤19`–`47` are free [N]. |
| Σ98 Finite theta heads | No-go | — | No fixed head pays its uniform remainder at every rank [L]; a frequency-adaptive head (cutoff `≍\|b\|/2`) does pay the remainder by half the first-atom reserve [S] (Σ6). |
| Σ99 Local onset field | Partially solved | sub | `Ω_ψ(a,X)` sum over zeros; pair cost `≤(16/9)δ²a⁴‖ψ‖²`; RH ⇔ `Ω≥0` [L]. |
| Σ100 Runs on the critical line | Partially solved | sub | `≥N(T)/5000` starts of five consecutive simple critical zeros [L]. |
| Σ101 Causal certificate | Solved (identity) | RH (all windows) | PD ⇔ positive-margin outer predictor; RH ⇔ outer predictors on every window [L]. |
| Σ102 Szegő threshold | Classified | RH (position) | `s>0` square-summable reflectors, `s<0` negative witness, RH at `s=0` with `Σγ²=∞` [L]. |
| Σ103 Reflection coordinates | Classified | — | Reflection data free; passive iff each echo in its band; forward map causal injective [L]. |
| Σ104 A priori estimates free of `1/μ` | Solved (model) | sub | Born model `1−r_n²≥e^{−10A}/(2√n log n)` [L]. |
| Σ105 Soft prime kick | Solved | identity | `(Ψ(x)−Ψ(a))log(1/(x−a))→Λ(n)/√n` at `2a=log n` [L]. |
| Σ106 Green corner | Solved | identity | Kato contraction; `q_y→q` in `L¹` on compact precontact intervals [L]. |
| Σ107 Far-translate decoupling | No-go | — | `c_φ(t)↛0` for every nonzero test [L]. |
| Σ108 Insertion cone | Classified | — | Below left growth `½` Hecke cone = torus cone = exponential convexity; `½` exact threshold of the `L²` prime-pair cone; all-base torus-positive amplitudes with `κ<min(1,κ₀)` vanish; torus cones closed under `e^{−βy}` [L]. |
| Σ109 Fixed-amplitude locking | No-go | — | Locked positivity ⇔ torus positivity for fixed amplitudes; only amplitudes oscillating with the height escape; amplitudes bounded away from zero give nonsummable torus series [L]. |
| Σ110 Columns add | Classified | — | Infimum of signed columns = sum of minima; base pays by size when `Σlog p/(p^{½+a}−1)<½log(b/2π)` [L]. |
| Σ111 Curve flow | Solved (calibration) | — | Unitary ⇔ first `R` margins positive [L]. |
| Σ112 Theta current | Solved (explicit) | identity | `current=2\|Ξ\|²Re ξ′/ξ`; explicit core and tail; `\|current a b\|≤3.6·10⁷\|a\|e^{−(7/5)\|b\|}` for `\|a\|≤½` [L]. |
| Σ113 Restoring bound of the actual chain | Solved (identity); control open | RH | `\|L(x)\|≤artanh e^{−2(x−c)}+2osc_{[c,x]}Ψ`; RH ⇔ `L` locally bounded on precontact intervals ⇔ `Ψ` locally bounded; off RH `L` is unbounded above every base [L]. |
| Σ114 Bohr profile decomposition | Classified | RH (for ζ) | RH ⇔ every orbit correlation relatively compact [L]. |
| Σ115 Critical Γ-liminf | Solved | identity | `liminf Q(U_N)≥Q_T(F)+α_R∫_{y<0}F²e^{−8y}` [L]. |
| Σ116 Weighted Gårding | No-go (full horizon); Solved (top collar); Partially solved (complement) | sub | Fails on `(V₁)ᗮ` for every `B` (deep difference `z_N`, `W₈≍N⁸`) [L]. Top collar: `Q+B_R‖U_y‖²≥κ_R·seventhMass+a_RW₈` at every `R` [L]. Window-localized collar Gårding, far Gårding on `(V₁)ᗮ` and complement Gårding on `(V_{Q₁})ᗮ` [S]. |
| Σ117 Typical-height sign | Partially solved | sub | At `A=δlog T/(64M²)`, outside one set of measure `δT`, every shaped test has `Q_γ>0` [L]. The bad set has Gaussian tails `≤209(4kδ²)^kT`, exponential rarity `≤418e^{−5M²/δ}T`, and measure `≤T^{1−1/(64K)}` at `A=K log log T` [L]. |
| Σ118 All-height sign | Open | sub | Size reaches `a≈log log X−log 4` [D]; past it Π80, Π87. |
| Σ119 Tangent of the forward map | Solved | identity | `∂E_n/∂λ(n₀)=−(2/√n₀)A_n(log n₀)`; margins concave [L]. |
| Σ120 Certified passivity | Solved (certified windows) | sub | Full causal chain on total length `≤2a₀` [L]. |
| Σ121 Bounded extremals for every weight | Solved | identity | Attained bounded ground state, exact edge law, explicit sup bound [L]. |
| Σ122 Prefix–collar coupling at a critical ratio | Reduced (to Σ56) | RH (all ratios) | Every vector vanishing on the top window `Ioc(N/S_R,N)` has the floor `(κ₀/(2c⁷))‖x‖²` (Σ126) [S]. Physical tearing fails (Σ127) [S]. The low packet against windows at every ratio is RH (Σ130) [L]. |
| Σ123 Kernel-valued prime payment | No-go (returning coordinates) | — | `\|S\|≤\|G\|` for decompositions in returning prime coordinates [L]. Euler coordinates `z_p` cannot cross `Re s=1` (Σ128) [L]. |
| Σ124 Critical coupling of the base | Classified | — | `thetaAmp(x)e^{x/2}→½` [L]. |
| Σ125 Certificates on the orbit | Classified | — | Pointwise coefficients tautological; frozen ones cost size; for `σ>1` the Ξ-current lifts to `𝒥_σ(t,ω)=2\|ξ\|²(B−Σ_nΛ(n)n^{−σ}Re ω(n))` whose worst fibre point is the pole: a frozen certificate exists exactly when `−ζ′/ζ(σ)≤B(σ+it)` [L]. |
| Σ126 Top logarithmic window | Solved (non-escape) | sub | `∃C₀ ∀R ∃S_R`, `log S_R≤(1/8)log(R+1)+C₀`, eventually: every `x` vanishing on `Ioc(N/S_R,N)` has `completeWeilEnergy≥(κ₀/(2c⁷))‖x‖²` at every `c⁸≤R log N`; every nonpositive direction meets the top window [S]. Below `c₀e^{6a*(ζ)}` every nonzero nonpositive vector charges both `V_{Q₁}` and the top window [S]. |
| Σ127 Splitting order at a critical ratio | Classified | method | Prime quasimode `v_q−proj_{V_{Q₁}}v_q`, `q∈(Q₁,2Q₁]`, split across the collar boundary: Schur ratio `→4/13` at every `R` and every `B_R`. Keeping conductors `≤N^θ`, `θ=(1+log log N)^{−5}`, whole: `o(1)` Schur decoupling across the boundary [S]. |
| Σ128 Certificates past the abscissa | Classified | — | On `Re s>½`, `Σ_p\|1−E_p(s)\|<∞` ⇔ `Re s>1`; no summable perturbation crosses. Head–tail certificate: every finite factorization is a rank-one decomposition; the tail coordinate is Schur exactly where `\|S\|≤\|head\|` [L]. |
| Σ129 Critical positivity threshold law | Classified | RH (all thresholds `=⊤`) | `0<R_c≤R_pole≤R_high=R_high^{PSD}=⨅_{A≥0}windowThreshold(A)≥c₀e^{6a*(ζ)}`; whole-space, PSD, pole-orthogonal and high-conductor thresholds all `=⊤` ⇔ RH ⇔ `a*(ζ)=⊤` [S]. Whether `R_c=R_high` is open (B104). |
| Σ130 Low-packet payment at every ratio | Reduced (to Σ1) | RH | `PolarPaymentAt R A`: `S_A(h)²/D(R)≤a_φQ(H)+(7J(1)/R)M₈(H)` for every window test. Eventual PSD along a critical sequence ⇒ payment on every window; payment at `R` on `[−A,0]` ⇒ `R≤windowThreshold A`; payment at every `R` on windows of length `→∞`, e.g. `(1/8)log(R+1)+C₀`, ⇒ RH; payment holds on every window for `R≤(2K)⁸` [L]. |
| Σ131 The cone counts primes | Partially solved | sub (finite range) | Every weight system in `𝒜(c)`: local density `1+O(e^{−a})` at `e^{2a}`; short-interval law at every resolution; `Σ_{N<n≤2N}λ(n)²≤2N(log 2N+C_s)²`; positive entries in every log-window; `\|ψ_λ(X)−X\|≤CX^{5/6}log X` for `X₀≤X≤e^{2c−3}` [L; the `5/6` law S]. Window positivity is a count with power saving on the window's range. |
| Σ132 Frequency packets | Solved (identity) | identity | `∫Re W(f⋆φ_X)dX=2π‖φ‖₂²Re W(f)`; a negative test has negative packets on a set of frequencies of positive measure [L]. |

## Π — precision and production

| Wall | Status | Strength | Content |
|---|---|---|---|
| Π1 Global law | Solved (equivalence) | RH | `ψ(x)−x≤C√x log²x` ⇔ RH; Redheffer `det R_N=M(N)` [L]. |
| Π2 Deciding input | Open | RH | No unconditional input at square-root precision. Any count-implying input is parity-breaking, locally pure, precision-faithful against `εn^{−η}`, `η<½`, of unbounded aperture and length, stabilizer in the square-root class [L]. |
| Π3 Producer cost | Solved (exponent scale) | sub / qRH / RH | Balanced stencils reach `ψ,θ≤(1+ε)x+C_εlog²x`; a producer of rate `ε` gives `\|M(n)\|≤εn+12(w/m)√n+K` [L]. |
| Π4 Window precision | Sharpened | RH | Reflection-pair prime-count band ⇔ RH; WL, JAS, CTF, PBM, RB receivers [L]. |
| Π5 Conjugate diagonal | Sharpened | sub → ≥qRH → RH | Means `O_c(log U)`; one dyadic constant ⇔ RH [L]. |
| Π6 Averages versus all heights | Partially solved | — | Double-log stage outside `O(V/log log V)` windows [L]. |
| Π7 Census / pair surplus | Partially solved | sub | Simple critical `≥0.67250071`; positivity-only certificates cannot reach `3/4` [L]. |
| Π8 Depth visibility | Classified | — | Cluster-product horizon [L]. |
| Π9 Exceptional moduli | Partially solved | sub | Uniform zero-free region and Siegel for `q≤(log x)^A` [L]. |
| Π10 Frequency localization | Solved | — | Cyclotomic band abscissa `2Θ` [L]. |
| Π11a–e Cone, bidegree, fixed-rank, definite, Siegel counts | No-go (named ansätze) | — | Positive Tate coefficients and fixed-dimension domination do not force the sign [L]. |
| Π11f Logarithmic duality | Partially solved | sub | Abel completion, logarithmic RR [L]. |
| Π11g Boost transform | Solved (identity) | — | `∫Z⁺(s,u)e^{2wu}du=K(s,w)ζ(s+w)ζ(s−w)` [L]. |
| Π11h Source effectivity | Sharpened | RH | Source cone and all-aperture RR constructed; Bézout ⇔ source-energy sign ⇔ RH [L]. |
| Π12 Subconvexity / heat floor | Partially solved | sub | `μ(½)≤33/200`; heat floors `6600/9991` [L]. |
| Π13 Prefix scale | Solved | — | Strip zeros `Θ(N²log N)` [L]. |
| Π14 Amplifier rank | No-go (finite support) | — | Radius `Be^λ` [L]. |
| Π15 Critical-scale residual sign | Classified | — | Residual = aliasing + Weil's form [L]. |
| Π16 Genus function | Sharpened | indep. | Upper law open [L]. |
| Π17 Window energy | Sharpened | RH; ≥qRH (log stage) | Abscissa = twice maximal depth; bounded port ⇔ purity [L]. |
| Π18 Finite realizations | No-go | — | No finite-dimensional norm realization of `Q` on a window [L]. |
| Π19 Moment-only improvement of Jensen | No-go | — | Holomorphic moments do not determine the log-mean [L]. |
| Π20 Count identities at the first prime | No-go (finite-square format) | — | [L]. |
| Π21 Exact balance | Classified | — | Full positive cone `{Λ}` under RH, empty otherwise [L]. |
| Π22 Near-line density ladder | Sharpened | sub | Eight forms; `D_win` from any actual-zero detector with shifted `L²` saving; corridor exceptions `O(T/log^ηT)` [L]. |
| Π23 Inner caps | Reduced | RH; ≥qRH (fixed degree) | Inner-cap flux = off-line generating function + bounded + `L²` [L]. |
| Π24 Parity at dimension zero | Classified | — | [L]. |
| Π25 Euler-product pinning | Classified | — | Shifted-pole weight refuted [L]. |
| Π26 Bulk second order | Solved | — | `2γ₁+γ²` [L]. |
| Π27 Retained Gamma comparison | No-go (lossless) | — | [L]. |
| Π28 Gauge-torus spectrum | Classified | RH at the trivial point | Pole-subtracted exponents `[Θ,1]` [L/K]. |
| Π29 Square-root threshold | Classified | — | `λ=½` reads isolated zeros [L]. |
| Π30 Collective payment of the kicks | Sharpened | RH | Kicks beyond collar locality are the smoothed count [L]. |
| Π31 Terminal prime channels | Solved | — | [L]. |
| Π32 Elementary sieve inputs | Solved | — | [L]. |
| Π33 Finite free Gaussian capacity | Classified | — | [L]. |
| Π34 Euler-side stability and drift | Classified | — | Drift `θ_S/2` forced and sharp [L]. |
| Π35 Source-faithful finite free split | No-go | — | `J=Γ⊠Θ`, `Θ` never real-rooted [L]. |
| Π36 Mollified Jensen stability | Sharpened | RH | Infinitely many unshifted degrees real-rooted ⇔ RH [L]. |
| Π37 Zero-free half-planes and the exact count | Classified | — | Zero-free `Re s>σ` ⇔ shifted Jensen stability; `sup_dN_d` = off-line count; `N_d≤300√(d log d)` [L]. |
| Π38 Finite free Hardy theorem | Solved | — | `≥d−300√(d log d)` real roots [L]. |
| Π39 Archimedean Wiener–Hopf factorization | Solved (identity) | — | [L]. |
| Π40 Self-improvement of a strip | Open | sub | `Θ<1⇒Θ=½` false for shifted products [L]; no mechanism. |
| Π41 Necessary-length laws | Solved (necessary bounds) | — | Excess `K₀/log T` forces `log N≥log²T/(6K₀)−(4/3)log T`; moment `→1` forces `log N/log T→∞` [L]. In Euler form: near-unit moments need at least the length of an Euler mollifier over primes up to `≈c log²T` [D]. |
| Π42 Long-mollifier receivers | Sharpened | RH; ≥qRH | Slope exact; cofinal bound self-improves to `K=6`; strict slope saving ⇒ RH [L]. |
| Π43 Length–precision law | Classified | — | Length `T^θ` sees `εn^{−η}` iff `η<½−1/(2θ)` [L]. |
| Π44 Explicit contour and mass bounds | Solved | — | `\|M(T)−(T/π)(log T−log 2π−1)\|≤80+65log T` [L]. |
| Π45 Bulk statistics of Jensen roots | No-go | — | Cauchy law holds for every backward heat flow [L]. |
| Π46 Entry filters | Classified | — | Type I/II parity-blind; finite linear laws have a common perturbation [L]. |
| Π47 Signed incidence precision | Partially solved | RH | `\|cost\|≤Ke^rexp(−c(2r)^{3/5}(log 2r)^{−5/3})` [L]; need `C_σe^{2σr}`. |
| Π48 Factorial-Fock seam bound | Sharpened | RH | [L]. |
| Π49 Completed Suzuki residual | Partially solved | RH | `\|A_N\|≤C√N exp(−c·vkScale N)`; bounded ⇔ RH [L]. |
| Π50 Möbius critical energy | Partially solved | RH | `≤CTe^{−c·vkScale T}`; subpower ⇔ RH [L]. |
| Π51 Vinogradov–Korobov barrier | Open | sub | Every unconditional saving sits at VK; `\|ζ(σ+iτ)\|≪(log τ log log τ)^{2/3}` on `1≤σ≤2` explicit [L]. Short-sum form Π80. |
| Π52 Hyperbolic density | Partially solved | sub | Zeros of depth `[α/L,(α+1)/L]` with `N(ρ)≥B₀` number `≪(α+1)²TLe^{−2x}/B₀²+(α+1)L³√T` [L]. |
| Π53 Cluster wall | Open | sub | Rate 2 for isolated zeros; clusters only at rate `2θ` [L/D]. |
| Π54 Negative moments at zeros | Open | sub | `N(ρ)=exp(−Σ_{a≠ρ}m_aG(ρ,a))`; crowds exponentially rare [L]; no bound on deep `J`. |
| Π55 Barrier blindness | No-go | — | One Euler factor puts a depth `A/log V` zero in every unit window while the prime walk moves `≤8` [L]. |
| Π56 Last-scale floor | Classified | — | Mollifier length `≤V^θ`, `θ<½`: floor `c(e^{−2θa}/a)V` [L]. |
| Π57 One-logarithm loss | Sharpened | sub | [L]. |
| Π58 One-window width | Classified | RH at `β=0` | [L]. |
| Π59 Exponent rigidity | Classified | RH | RH ⇔ positive proportion of every length-2 window has `\|E_X\|≤X^ε` [L]. |
| Π60 Truncated Möbius collar | Classified | — | Collar reduces to pure Möbius moments [L]. |
| Π61 Prime field at the critical scale | Solved | sub | Selberg CLT; off-line `log\|ζ\|` = prime polynomial + bounded [L]. |
| Π62 Zero-damping hypercube | Sharpened | RH | [L]. |
| Π63 Second expression of the inner mass | Solved (identity); producer open | RH | `inf_Q∫\|ζ exp Q\|²P_w=exp(2∫log\|ζ\|P_w)`; budgets reach 1 ⇔ RH [L]. |
| Π64 Box budgets | Solved | identity | [L]. |
| Π65 Log-mean of ζ | Reduced | sub | Eight equivalent forms; Abel form ⇔ depth density `o(T)`. Selberg's mollifier gives off-line first moment `≤(67/1000)V`, depth `O(T)` in every window, `I(½+x+it)` bounded on `x≥1, \|t\|≤x`, Abel log-mean `≤11/2` at large `x` [L]. `o(T)` open. |
| Π66 Integrality over ℤ | Solved (exact) | RH at `√` scale | Nair lattice exact; Siegel half ⇔ lower count, Liouville half ⇔ upper count [L]. |
| Π67 Stencil ceilings | Classified | — | Floor `A(K)−1≥c/(√K(1+log K))`; no rate `K^{−a}`, `a>½` [L]. |
| Π68 Möbius zero condensation | Classified | RH | Zeros of `M_X` accumulate on `Re s=Θ` [L]. |
| Π69 Integer lag | Sharpened | RH | RH ⇔ lag `≤(2+γ−log 4π)√n`; `Ω±(√n)` [L]. |
| Π70 Rate of a stencil | Solved (exponent scale) | sub / qRH | Rate `K^{−a}` ⇒ `Re ρ≤1−a`; all `a<½` ⇒ RH; none past `½`; VK rates `exp(−(log K)^α)`, `α<3/5`; polynomial rate ⇔ strip. `\|M(n)\|≤Cn^{1−σ}` gives every `a<2σ/(3+2σ)` (compensated) and `a<σ/(2+σ)` (entangled); RH gives `a<¼`; under RH the exponent lies in `[¼,½]` [L]. |
| Π71 Laws of a producer | Solved | — | `c=μ∗h`; producer = mollifier on `Re s=1`; peak law; uncertainty; compensated stencils: all letters `(2y+2)`-smooth, compensation cost `1/y`, alphabet `y³/Y` [L]. |
| Π72 Ledger blindness | No-go | — | Complete ledger of a zero mode vanishes for every balanced stencil [L]. |
| Π73 Parity ledger | Classified | — | Sieve and producer cones disjoint; parity-neutral producers reach every rate [L]. |
| Π74 Fake prime measures | Classified | — | Slope LP with strong duality; unique fake at infinite level; extremal level-`K` fake has `≤K` atoms on an optimal sawtooth's tight set; level-`K` fakes lie within `≍1/log log K` of the pronic measure under a summable tail condition [L]. |
| Π75 Hecke action on producers | No-go (positive amplification) | — | [L]. |
| Π76 Frobenius as a stencil | Solved (calibration) | — | Over `𝔽_q[T]` the Carlitz stencil has rate 0 [L]. |
| Π77 Near-extremal rigidity | Solved | identity | Near-extremal families converge to `1/E` [L]. |
| Π78 Holomorphic Abel budgets | Open | RH | Over a curve Castelnuovo ⇔ budgets reach 1; boundary quotients nonselective [L/K]. |
| Π79 Arithmetic Carleson measure | Solved | identity | `μ(box)≤(5/2)xI`; `I→0` ⇔ depth density `o(T)` [L]. |
| Π80 Short-sum barrier | Open | sub | Depth `d` forces a large value of a prime polynomial of length `(log γ)^{O(1/d)}` [L]. Some height `≤T` has no cancellation below length `c log T`; off a set of measure `≪TY^{−2ε}` square-root cancellation holds at all dyadic lengths `Y..T/log T` at once [L]. Missing: the exceptional set past `log T` at all heights. |
| Π81 Kernel of the cut system | Classified | RH | Zeros = power-law kernel vectors; summable kernel vectors vanish; positivity reaches `Re s≥1`; absolutely convergent strip superpositions lie in the kernel iff each active point is a zero; finite-energy mass annihilation ⇒ RH [L]. |
| Π82 Ledger hierarchy | Solved | — | Degree `k` ledgers have order `m−k`; exact ledgers holomorphic off `s=1` [L]. |
| Π83 Twin at every degree | Solved | — | `T=A−2A(2s)` shares every leading pole of `A^k` at right zeros [L]. |
| Π84 Parity exponent | Solved | ≥qRH at power saving | `L(x)≪x^a` ∀`a>Θ` ⇔ zero-free `Re s>Θ`; the exact identity `Σ_{k≤x}F(⌊x/k⌋)=⌊√x⌋` forces `f=λ` [L]. Parity is a size statement, not missing information. |
| Π85 Exchange law | Solved | — | Exchange of exponent `<σ` keeps the zeros right of `σ`; a new zero needs exchange mass of exponent `≥β`; exchanges with `G(1)=1` have `N(x)=x+O(x^σ)` [L]. |
| Π86 Carry of the floor | Solved | — | A dilation of the count is an average of translations; every integer is a cut [L]. |
| Π87 Absolute non-alignment | Partially solved | sub | Low additive-energy squared words: `Σ_{p<N}(1−cos t log p)/√p≥8/(10⁹L⁶ℓ⁴)` and `‖Σ_{n<N}n^{it}‖≤N(1−1/(10⁷L⁶ℓ³))` at `N≥48L²ℓ`; `≥t^{−δ}` at length `L^A`, `A>1` [L]. Required at the size curve `≈εL/ℓ` [D]. |
| Π88 Rounded orbit | No-go | — | Same diagonal moments, exact return at `T` [L]. |
| Π89 Discrepancy and mixing time | Classified | — | Every window of length `exp(10y√(log y·log log y/δ))` enters every `δ`-box on primes `≤y`; a box of radius `ρ` is missed on `[0,T]` while `2(2^{J+1}Tθ(y)/π+(J+1)π(y))+1<2^{(J+1)π(y)}`, `ρ=π/2^{J+3}` [L]. So `½π(y)log(1/δ)≲log T_mix≲10y√(log y log log y/δ)`. |
| Π90 Energy past the diagonal | Partially solved | sub | Gap to truth = density of smooth numbers [L]. |
| Π91 Curve stencil | Solved (calibration) | — | Linear stencils stop at `\|a\|≤q+1` [L]. |
| Π92 Prime kernel as torsion energy | Solved (identity) | — | `Λ` = intersection number of torsion orbits; sign lost in `log(1/(1−r))Σx²` [L]. |
| Π93 Möbius as a cubic Gauss coefficient | Solved (identity); descent partial | past VK | Over `ℤ[ω]` ideal Möbius = cubic Gauss coefficient with fixed ray phase; cubic Eisenstein series, Fourier unfolding, Fredholm pencil, meromorphic resolvent; constant term = quotient of unramified ideal zeta functions, supported exactly on cubes; residue at `4/3` nonzero with `ΔR=(8/9)R` and cubic character; Fourier modes `V·A_h(s)·H_h(s)`, `A_h` continues to `Re s>1` with residue `Fourier_h(R)/(V H_h(4/3))`, `H_h(4/3)≠0` [L]. Fourier coefficients of the residue and rational transfer open. |
| Π94 First return of the prime orbit | Partially solved | sub | `R(y,η)≤Q^{π(y)}` when `2π²≤ηQ²`; `R→∞` for `η<1`; a weak return is a spike `\|ζ(1+1/log N+it)\|≍log N`; with the VK bound on the `1`-line, a weak return at bounded harmonic defect has `log t≥c(log N)^{3/2}/log log N`, so `R(N,η)≥exp(c(log N)^{3/2}/log log N)` when `η log log N≤D` [L]. Precision law: `R(y,η)>exp(√(y/(48log y)))` once `12η√y·y⁴<c`, `R(y,η)>exp(y^{1/A})` once `12η√y<exp(−δy^{1/A})` [L]. Constant precision open. |
| Π95 Proportional saving = heavy first return | Classified | — | Defect `<cS` forces a return at precision `η` on a subset of weight `>(1−c/η)S`; a return missing weight `κ` has defect `≤ηS+2κ` [L]. B46 is the absence of early heavy returns. |
| Π96 Conditional tail law and the Kronecker scale | Partially solved | sub | Head `R` on `y`-smooth, tail `B` on `y`-rough integers: `∫_T^{2T}\|R\|²\|B\|²=T‖r‖²‖b‖²+O(N log N‖r‖²‖b‖²)`; Gaussian conditional moments and large deviations while `log max A+k log Z≪log T` [L]. Fixed resonator: `(1/T)∫\|R\|²\|ζ(σ+it)\|²→(Σ_s\|c_s\|²)·Σ_u u^{−2σ}`, `½<σ<1` [L]. Arithmetic mean values (Π103) replace the generic length `max(head)·max(tail)` by collision counts. Past the Kronecker scale no distributional law is known. |
| Π97 Moving jet of the logarithm | Partially solved | method | `Δ_h^j log x=Δ_1^j log(x/h)`; coefficients move by `≥(j+1)!/(x+j+2)^{j+2}` per step; blocks with a coefficient near a lattice number `O(ηH+1)` [L]. No saving derived. |
| Π98 Archimedean place versus depth | Classified | — | Depth aspect: `u↦1+q₁u` exact homomorphism, `q`-differencing exact. Height: `h↦t log(1+h/x)` additive up to `\|t\|hh′/x²` [L]. |
| Π99 Count-distance rigidity | Solved | — | A positive integer-norm Beurling system other than the rational primes has count error `≥c log n` at arbitrarily large `n`; bounded multiplicities force unique factorization [L]. Odd primes plus labels of norms `3,4`: `N(x)=x+O(log²x)`, continuous profile `P(4x)=P(x)`, `P(x)+P(x/2)=½`, averaged deficit coefficient `1/(4log 3)` with a power rate, exactly ζ's zeros [L]. |
| Π100 Bounded count with a new zero | Solved (signed generators) | — | `a(n)=1−1_{2∣n}+4·1_{8∣n}`: nonnegative, multiplicative, `−3≤N(x)−x≤0`, zeros with `½<Re s<1` on a vertical progression; generators at 2 have negative multiplicity [L]. |
| Π101 The comb of a return | Solved (polynomial reach) | method | Level sets of `t log n/2π` are multiplicative approximate groups; a return lays `P`-smooth integers on a comb [L]. |
| Π102 Positive Euler products with a finite top layer | Solved (countermodels) | — | Integer norms `≥2`, nonnegative integer coefficients, linear counting, exactly `3/5±iγ` on `Re s>½` [L]. Rational-prime labels (repetition allowed, `q_k=nextPrime(e^{t_k})`): Euler product, multiplicative natural coefficients, `Σ_{n<N}a(n)/N→A>0`, holomorphic on `Re s>59/100` with zero set there exactly `{3/5±iγ}` [S]. Nonnegative two-prime polynomials `Σc_{ab}2^{−as}3^{−bs}`, `c_{00}=1`, vanish on any finite set in `Re s<1` and stay `ε`-close to `1` on `Re s≥1` [L]. |
| Π103 Arithmetic mean values of smooth × prime | Solved | sub | Smooth rows and prime columns in `(X,2X]`: `∫_{−T}^{T}\|Σc(m,p)(mp)^{−i(U+t)}\|²≤(5π/2)(T\|A\|\|B\|+8X²\|A\|²)`; rectangular `∫\|R\|²\|B\|²≤(5π/2)(TΣ\|r\|²Σ\|b\|²+4Z(X+Z)(Σ\|r\|)²K²)`; arbitrary smooth heads through the reduced-ratio height `H`: head mass `≥(2T−52H)R₂`, normalized `2k`-th tail moment `≤(5π/2)(k!B₂^k+C(k!)²/(TR₂))`, `C≤2Z(Z+H)R₁²` [L]. Collisions `mp+h=m′p′` force gcd classes; cumulative cost `≤` diagonal `+2⌊4X²δ⌋\|A\|²` [L]. A prime-density saving in the collision count is open. |
| Π104 Twin quarter floor | Solved | — | `F_x(s)F_y(s)=F_z(2s)` for a gauge point and its Liouville twin; `Θ≤2max(θ_μ(x),θ_μ(y))`; order-two twins have `max≥¼`, constant-source twins `≥½` [L]. |
| Π105 Farey, Mertens and the nerve | Solved (identity) | RH | RH ⇔ Farey `L¹` discrepancy `≤Cn^{½+δ}` ⇔ `L²` discrepancy `≤Cn^{−1+δ}`; `\|M(n)\|≤2π·L¹`-discrepancy; `M(N)=−χ̃` of the prime-star nerve; `χ̃=Ω±(√N)` [L]. With Γ121 the closed horocycles of the modular horizon carry the same number. |

## Γ — selection and reflection

| Wall | Status | Strength | Content |
|---|---|---|---|
| Γ1 Trivial gauge point / self-return | Open | RH | Cutoff-uniform positive Haar target mass on doubled discs ⇔ RH [L]. |
| Γ2 Prime-set flips | Solved | — | Every nontrivial pattern separated [L]. |
| Γ3 Twin-blindness of soft structure | No-go | — | [L]. |
| Γ4 Frobenius at infinity | Sharpened | RH | Window involution = twisted Krein reflection [L]. |
| Γ5 Source identification | Partially solved | RH | Actual-source receivers for ZCG, PTR, SEC, ACS, CDC, PCS [L]; candidates lack a landing. |
| Γ6 Boundary sign / coherence | Solved | — | [L]. |
| Γ7 Affine carrier | Solved | — | [L]. |
| Γ8 Poisson rigidity | Sharpened | RH | Zero-side positivity = RH [L/S]. |
| Γ9 Archimedean continuity vs height decay | No-go | — | [L]. |
| Γ10 Function-field indistinguishability | Sharpened | — | Cayley ladder over `𝔽_q` = sharp Weil bound [L]. |
| Γ11 Pole-blindness of the glue | No-go | — | [L]. |
| Γ12 General gauges | Solved | sub | [L]. |
| Γ13 Source-uniform extinction | No-go (PW-B) | — | [L]. |
| Γ14 Local counterterm selection | No-go | — | [L]. |
| Γ15 FE twins | Partially solved | sub | [L]. |
| Γ16 Selection–sign gap | Sharpened | RH | Source identification does not prove the sign [L]. |
| Γ17 Scattering recentering | Classified | — | Rational/two-locus reality forces constants or a horizontal line [L]. |
| Γ18 Divisor-identity selection | Solved | — | [L]. |
| Γ19 Correspondence algebra over ℤ | Sharpened | RH | Rosati positivity ⇔ orbit Hodge index [L]. |
| Γ20 Window selection | Classified | — | [L]. |
| Γ21 Density selection | No-go | — | [L]. |
| Γ22 Contractive scattering positivity | No-go | — | Blaschke insertion moves zeros and increases Schur forms [L]. |
| Γ23 Weil cone uniqueness | Solved (uniqueness) | — | Full positivity forces `Λ`; cone nonemptiness is RH [L]. |
| Γ24 Mayer reflection positivity | Sharpened | RH | `Q(H)=2Re[WH,WH]`; `D_s≤0`, zero iff `Re s=¼` [L]. |
| Γ25 Two reflection centres | Partially solved | — | Closed densely defined reflection survives [L/K]. |
| Γ26 Resonant-state selectors | No-go | — | [L]. |
| Γ27 Tate counts as selector | No-go | — | `ζ(s)ζ(s−ε)` [L]. |
| Γ28 Frobenius inside the window algebra | No-go | — | Same-window similitudes are scalar [L]. |
| Γ29 Linear Serre–Krein identification | No-go | — | [L]. |
| Γ30 Completed Tate family | Classified | — | [L]. |
| Γ31 Degeneration type over `𝔽_q` | Solved (calibration) | — | [L]. |
| Γ32 Hecke-equivariant completion | Solved (identity) | identity | [L]. |
| Γ33 Euler rigidity in the Selberg class | Solved | — | Degree one is `L(s+iθ,χ)` [K/L]. |
| Γ34 Hecke cones and periods | Solved | — | [L]. |
| Γ35 Beurling and Hamburger rigidity | Classified | — | Quantitative Hamburger uniqueness [L]. |
| Γ36 Identification by the explicit formula | Solved (sign-free) | sub | Isolated zeros at `λ>½`; configurations at `λ>1`; period-6 sharp [L]. |
| Γ37 Euler columns | Classified | — | Ramanujan = reality [L]. |
| Γ38 Retained Hecke channel | Classified | — | Sign of `¼−Re s` [L/K]. |
| Γ39 Blindness = density aperture | Solved | — | `πD` [L]. |
| Γ40 Positivity certifies thin configurations | Solved | — | [L]. |
| Γ41 Fakes at their first prime | Solved | — | `½log n₀` [L]. |
| Γ42 Legendre-invariant reality | Solved (identity) | identity | RH ⇔ `J(ρ)∈ℝ` [L]. |
| Γ43 Collide or repel over `𝔽_q` | Solved (calibration) | — | Finitely many power sums certify integral purity [L]. |
| Γ44 Second-order coalescent precision | Solved | sub | [L]. |
| Γ45 Domination as a selector | No-go (density-only) | — | [L]. |
| Γ46 Reality at near-coincidences | Partially solved | RH | FE pair at depth `δ` forces `\|ζ(½+iγ)\|≪\|γ\|^{33/200+ε}δ²` [L]. |
| Γ47 Sharp location from positivity | Solved (receiver) | sub | Depth `<e^{−c log³T}` at `λ·½log T`, `λ>1` [L]. |
| Γ48 Diophantine repulsion of carriers | Classified | — | Baker–Matveev repulsion; Liouville Satake angle defeats polynomial laws [L]. |
| Γ49 Exceptional values of ζ | Partially solved | indep. | Nonrepelling values: dense `G_δ` of dimension zero; `0∉E` open [L]. |
| Γ50 Weighted image vs atom count | No-go | — | [L]. |
| Γ51 Near-coincidence dictionary | Solved (identity) | — | [L]. |
| Γ52 Canonical repair | Sharpened | RH | CDC/BSH equality at every zero suffices [L]. |
| Γ53 Reflection-odd co-shift | Sharpened | RH | PCS: RH ⇔ `n^{−ρ}−n^{−(1−ρ̄)}∈ℓ²` [L]. |
| Γ54 Newton source-margin coverage | Sharpened | RH | [L]. |
| Γ55 Positive mimic = window sign | Solved (identity) | RH | [L]. |
| Γ56 Exact extremal blind test | Solved (existence) | indep. | `Φ=Ξg` blind at every `log n` [L]. |
| Γ57 Boundary norm of the Mayer carrier | Solved | sub | `\|ζ(1+it)\|≥1/(6250t³log²t)` [L]. |
| Γ58 Spectral-determinant reflection | No-go | — | [L]. |
| Γ59 Reach of unitary positivity | Classified | — | Maass–Selberg positivity lives on the unitary axis [D]. |
| Γ60 Theta–Eisenstein identification | Solved (identity) | identity | `Στ_b(N)N^{−s}=ζ(s−ib)ζ(s+ib)` [L]. |
| Γ61 Inner factor | Solved (identity) | RH | `I(w)=Σm_ρG(w,ρ)≥0`; RH ⇔ `I=0` at one point [L]. |
| Γ62 Hecke dispersion | Sharpened | RH | `V_p(ρ,Y)=2(1−p^{Re ρ−1})` [L]. |
| Γ63 Poisson-extended Hecke positivity | No-go | — | Every `T_n` is diagonal on Eisenstein, `T_nE_u=W_u(n)E_u`; on a truncated resonant state `⟨T_nt_Y,T_mt_Y⟩=‖t_Y‖²∫P_{−Re u}(t−Im u)W_{it}(n)W_{it}(m)dt` for all `n,m≥1`, `Y≥max(n,m)`, with the Hecke multiplication law: a positive Poisson measure for every `Re u<0`, not line-selective [L]. |
| Γ64 Cross-zero Gram law | Solved (identity) | identity | [L]. |
| Γ65 Cutoff line law | Solved (edge) | sub | [L]. |
| Γ66 Scattering Blaschke product | Solved | — | `φ(s)(s−1)/s` Blaschke over `(1+ρ)/2` [L]. |
| Γ67 Abscissa split | Solved (identity) | RH | RH ⇔ ZAL ∧ AAL; RH ⇔ ZAL ∧ zero-disc weak recurrence; under AAL eight RH-level statements coincide; `qRH ∨ AAL` [L/D]. |
| Γ68 Asymptotic abscissa law | Open | sub | ¬AAL ⇔ finite top and bottom layers, so the top excess is attained ⇔ `ψ(x)−x=x^βT(log x)+O(x^{β−η})` [L]. |
| Γ69 AAL producers | Partially solved | sub | Not-attained top; bounded lag on one progression; lag `≤Me^{aL}` off a set of lower Abel density zero; polar ground energy `μ₀(B)≥−C_εe^{εB}`; one generic discrete prime-window grid subexponential; log-dense integer lag bounded above; twisted plateaux; JAS dressed PSD; typical JAS positivity; bounded towers; one bounded cone; shell positivity; weak recurrence; infinitely many zeros near each right zero; slow aligned returns on right discs [L]. Each retains its source bound. |
| Γ70 Zero–one law of recurrence | Classified | — | [L]. |
| Γ71 Pair recurrence | Partially solved | sub | At density-`(1−δ)` base heights [L]. |
| Γ72 Returns at a zero | Classified | — | Rare and threshold-quantized [L]. |
| Γ73 One-off countermodels | No-go (positive data) | — | Continuous Beurling systems with nonnegative prime and integer densities, `N(x)−ρx−C→0`, exactly one off-line pair, no weak zero-disc recurrence [L]; discrete and integer-norm systems with linear counting [L]; rational-prime Euler products with multiplicative linear counting [S]. Classical FE and critical-line continuation absent in every model (Γ124). |
| Γ74 FE-defect rigidity | Partially solved | sub | Defect `≤1/6400` forces rational primes [L]. |
| Γ75 Inner field of a column | Solved | identity | [L]. |
| Γ76 Endpoint characters | Sharpened | RH | Column Young projections nonnegative; every Young projection of shape `\|λ\|≤4` nonnegative by dual Jacobi–Trudi; Toeplitz minors `≤200` nonnegative [L]. |
| Γ77 Tensor weights and compression | No-go (stated classes) | — | Golden passes; pure compression preserves even subspace iff RH [L]. |
| Γ78 Global trace on a family | Partially solved | RH | Kloosterman fibres pure by Stepanov; arithmetic family containing ζ open [L]. |
| Γ79 Displacement | Classified | — | Holomorphic data carry no weighting by displacement [L]. |
| Γ80 Finite oscillation | Solved | sub | Every witness has `β=Θ`, unique `T`, quantized coefficients, remainder ceiling, bounded-log-gap sign changes [L]. |
| Γ81 Dilation annihilation | Solved (identity) | sub | ¬AAL ⇔ two-prime annihilation of `ψ` to `O(x^{β−η})` [L]. |
| Γ82 Rightmost-zero jets | Solved | sub | Diagonal `→0`, off-diagonal `→m²`, short shifts `o(1)` [L]. |
| Γ83 Returns are prime returns | Solved | — | A return forces `n^{−iτ_j}→1` and a spike near the pole; limits fill the torus [L]. |
| Γ84 Isolation of ζ | Solved | identity | FE defect `≤1/6400` is one point; count distance `o(log n)` is one point (Π99); the exact parity identity pins `λ` (Π84) [L]. |
| Γ85 Rational zero relocation | No-go | — | Not Bohr almost periodic [L]. |
| Γ86 Modular horizon | Solved (exact solution) | RH (universal damping) | Exact metric, echo train, causal symbol, ringdown in the modes of the zeros; quarter-line bound ⇔ RH; the exterior is a chart of the Rindler wedge of AdS₄ and the black hole is its quotient by `SL₂(ℤ)⊂SO(2,1)⊂SO(3,2)`; the vacuum perturbation of every compact profile extends smoothly through the future horizon [L]. |
| Γ87 Raw echo decay | No-go | — | [L]. |
| Γ88 Near-arithmetic ladders | No-go | — | [L]. |
| Γ89 Blindness of physical positivity | Classified | — | Schur, KMS, reflection, `C*` positivity hold on every black hole [L]. |
| Γ90 Maximal-angle zero | Classified | RH | RH ⇔ `‖Q(tw)‖=‖Q(t̄w)‖` at zeros [L]. |
| Γ91 Lefschetz ratios | Solved | RH | Every right zero is read by `c_{m+1}/c_m→p^{ρ−½}` [L]. |
| Γ92 Fake black holes | Solved | — | Every local count is a tree quotient with flux and unitarity; `t²>4q` gives off-circle resonances [L]. |
| Γ93 Hecke rigidity on resonances | Solved | — | Commuting operators act by `X^d+Y^d`; positive families in every class exist on fakes [L]. |
| Γ94 Cuspidal sector | Classified | — | Independent Hecke content lives where there is no flux [L]. |
| Γ95 Krein flux law | Solved (identity) | RH (sign) | Flux `½𝒬_f≥0` ∀f ⇔ RH; on graphs the Lax–Phillips compression has rank two, `det Z=q`, Krein metric Hilbert ⇔ universal damping [L]. |
| Γ96 Count law | Solved | genus one | Parallelogram for the count at all probes ⇔ `t²≤4q` [L]. |
| Γ97 Integer probes | Sharpened | RH | RH ⇔ `Q(a)≥0` on `ℤ^N`; fake: count not quadratic; ℤ: quadratic not known count [L]. |
| Γ98 Manin's Hasse | Solved | genus one | `K(x,y)=ht(yP₀−xP₁)` on the twisted curve over `𝔽_q(T)`: parallelogram, `K(1,1)=#E(𝔽_q)`, Hasse from the count law [L]. |
| Γ99 Throat | Solved | — | Product of modes depends only on the index nearest the cusp; FE only at genus `≤1` on a path [L]. |
| Γ100 Rank barrier | Solved | — | A compact probe excites infinitely many modes over ℤ [L]. |
| Γ101 One clock | Solved | — | Hecke at `p` = modular time shift `log p` [L]. |
| Γ102 KMS midpoint | Classified | — | `¼` is the KMS midpoint rate [L]. |
| Γ103 Horocycle is the wave | Solved | graph | [L]. |
| Γ104 Bulk log-mean | Solved | sub | Abel log-mean `→0` ⇔ damping deficits of density zero [L]. |
| Γ105 Transport count | Classified | — | [L]. |
| Γ106 Missing input of transport | Solved (receiver) | sub | Bounded translates on a domain joining ρ to `Re s>1` ⇒ infinitely many zeros right of `Re ρ−r`; a bounded return at each zero ⇒ AAL; a head return of length `N≥11` has `N<τ+1` and, at large `τ`, `N<1024(log τ)⁴(log log τ)²` [L]. |
| Γ107 Effective transport | Solved | sub | On discs about `3+iγ` of radius `R>5/2`, `sup\|ζ(s+iτ)\|≥cτ^b` ⇒ the all-zero slow-return premise ⇔ RH; on discs with left edge `σ₀∈[½,β)` slow aligned returns at each right zero give AAL [L]. |
| Γ108 Tail at a zero | Solved | — | At a zero a positive proportion of prime returns are not returns of ζ [L]. |
| Γ109 Limit map | Solved | — | Limits on `Re s>1` fill the torus, twin included [L]. |
| Γ110 Hull over the torus | Classified | RH | Liouville fibre extends ⇔ RH; RH ⇔ every nonzero limit of translates zero-free [L]. |
| Γ111 Stieltjes sign | Solved (necessary law) | — | `Im(w₀Q″/Q′)≤0` [L]. |
| Γ112 Rotated relation classes | No-go (coefficient growth) | — | Coefficients of growth `exp(C√\|w\|)` force triviality; a non-vacuous relation has coefficients of the size of `Q` [L]. |
| Γ113 Naive height, five currencies | Sharpened | RH | Degree-two form `≥0` iff a function bounded below lies at bounded distance; window naive height exists ⇔ positive; length `≤3/5` exists [L]. |
| Γ114 Dilation quotient | Sharpened | RH | RH ⇔ zero dilation surplus ⇔ critical/shifted Szegő budget ratio equality; Euler prefixes invariant [L]. |
| Γ115 The tail of a return carries the zero | Solved | sub | Zeros of ζ on `Re s>0` = zeros of `ζM_y` at every cut; every return on an isolating disc at a right zero is tail-bad at every cut with tolerance independent of the cut; such returns have density zero [L]. |
| Γ116 Head frozen at its resolution | Solved | — | `\|log\|E_y(s+iv)\|−log\|E_y(s)\|\|≤2\|v\|(log y+log 4)` on `Re s≥1` [L]. |
| Γ117 Trivial zeros of a cusp | Solved | graph | Integrality forces genus `≤` trivial zeros `+1`; cusp index law `\|c₀−1\|=q^{1−g}` [L]. |
| Γ118 Genus two does not force damping | No-go | — | 11-vertex graph with the genus-two FE for every `q≥2`; all modes on `\|z\|²=q` iff `q≤3`; one-cusp variant fails damping for `q≥5` [L]. FE + flux + unitarity + Hecke leave damping open. |
| Γ119 Natural boundary of the hull | Solved | — | Haar-a.e. and fair-coin-a.e. fibres extend zero-free to `Re s>½` with natural boundary `½`; a.e. order-two point and its Liouville antipode both have the boundary while their product is `ζ(2s)`; the boundary is carried by the odd part of the logarithm; the Liouville point extends iff RH [L]. |
| Γ120 Extremal law has a model | No-go | — | `w²−2w+2` satisfies the full maximal-angle inequality with off-axis zeros [L]. |
| Γ121 Horocycle rate = zero-free region | Solved (Zagier) | RH (rate `¾`); ≥qRH (interior) | Mellin of the horocycle mean of a pseudo-Eisenstein series: `2ψ̃(s−1)+2(Λ(2s−1)/Λ(2s))ψ̃(−s)`. All-profile rate `y^α` ⇒ every zero has `Re ρ≤2−2α` [L]; zero-free `Re>θ` with polynomial `1/ζ` ⇒ rate `y^{1−θ/2−ε}`; rate `y^{1/2−ε}` unconditional; RH ⇔ rate `y^{3/4−ε}` for every profile [S]. |
| Γ122 Lax–Phillips decay on the modular surface | Solved (identity) | RH | Resonances `u=(ρ−1)/2`; truncated resonant states are `L²` eigenvectors of the Lax–Phillips semigroup, `Z(t)t_u=e^{ut}t_u`, `Z(t)` contracts and exhausts the interaction space; RH ⇔ every resonant mode decays at `e^{−t/4}` [S]. |
| Γ123 Recurrence dichotomy of the tail | Solved | sub | On the universal disc about every strip point, nonvanishing targets are approached at positive lower density; targets with an interior zero only at heights tail-bad at every cut, tolerance `m/4` [L]. |
| Γ124 One-offs stop at the critical line | Classified | method | Discrete one-offs blow up at `s=½` (`Σ1/p_k=∞`); in a countable system any displacement of primes or integers from the rational ones forces an explicit positive FE defect, and defect `≤1/6400` forces the rational primes; the continuous one-offs carry no FE [L/D]. The property of ζ no countermodel shares is continuation across `Re s=½` with the functional equation. |

## Scoped no-gos and surviving replacements

| Boundary | Exact scope and survivor |
|---|---|
| KR-TOR / KR-UCF / KR-R1 | Retired labels, not proved kills. BAG transfer closed (Γ1); PA Hermite-contour receiver (Σ73); TG Gaussian-passage receiver (Σ80). |
| KR-FPR | Finite and cofinal finite Hermitian KMS corrections cannot realize universal incidence passively [L]. |
| KR-SRP | Odd-only pole weight `β>1` impossible; even-only `β>1` not settled [L]. |
| KR-GAP | Excludes `E=QG₀(·+ih)`, `G₀` lower-Pólya; not arbitrary HB realizations [L]. |
| KR-R2 | Anchored 2-periodic loops realize every odd winding; not identified with renewal feedback [L]. |
| KR-R3 | Eventual upper bounds at every height ⇔ RH [L]. |
| Left-crossing slow returns | Discs reaching `Re s≤½` force `\|ζ\|≥cτ^b`; the polynomial premise there is RH. Right-edge discs carry the AAL receiver (Γ107) [L]. |
| Literal `riemannHypothesis_of_count` | `K:ℕ` equal to `Q(a)` needs integer values; the bounded-distance form Γ113 is the usable statement [D]. |
| Physical tearing at a critical ratio | Fails at Schur ratio `4/13` on prime quasimodes; conductor-adapted splitting survives [S]. |
| Low packet at a fixed ratio | Payment at one ratio `R` is a window rung (`R≤windowThreshold A`); payment at every ratio is RH (Σ130) [L]. |
| Extremal-angle contradiction | Polynomial model satisfies every order of the extremal law (Γ120); growth, log-concavity or arithmetic must enter [L]. |
| Bounded count as selector | Bounded count error admits a new zero with signed generators (Π100); with positive generators count error `o(log n)` forces ζ (Π99) [L]. |
| Positive Euler product + linear counting as AAL | Integer norms and rational-prime labels both carry a finite top layer (Π102); none continues to the critical line (Γ124) [L/S]. |
| Positive Dirichlet coefficients + proximity to 1 on `Re s≥1` as zero exclusion | Two-prime nonnegative polynomials kill any finite set (Π102) [L]. |

## Bridges

| Bridge | Anchor |
|---|---|
| Window index counts distinct right zeros; `sup_dN_d` counts off-line multiplicity; bounded `N_d` gives finite support only | AHD, CWS, FFP [L] |
| RH ⇔ `a*(ζ)=⊤` ⇔ `1∈ℋ(c)` ∀c ⇔ `λ*(c)→0` ⇔ no finite contact ⇔ `Ψ` locally bounded | WVL, FADF, CHT, CSTW, AIF [L] |
| Critical curve = window: `R_high=⨅windowThreshold`, `log R_high≥6a*(ζ)+log c₀`; low packet at every ratio = RH | AHD [S], CACT [L] |
| Window sign ⇔ two-site signs ⇔ reflection band ⇔ Stieltjes jets ⇔ two-bump family | GWZ, SWC, SRT [L] |
| Window positivity ⇒ local density, support density and PNT with exponent `5/6` on the window's range | CHT [L/S] |
| Reflection-pair coupling = collar Hankel − smoothed count = `c_φ(2m)` | SWC, FADF [L] |
| Below `log 4`: sign ⇔ two-weight band ⇔ Hodge index ⇔ Künneth effectivity; below `log 5`: `{2,3,4}` band; Tate dimension one through `log 5` | SWC, LST, AHD, FADF, WTZ [L] |
| Completed coefficient-space energy `=2Re[WH,WH]`; `D_s` negative weighted Hecke integral | RIT, ACP [L] |
| Isolated clusters ⇒ camera readout; positivity at `λ·½log T` ⇒ depth `<e^{−c log³T}` | ZCG [L] |
| RH ⇔ infinitely many unshifted Jensen degrees real ⇔ all positive-time heat zeros simple | FFP, RHTower, ZCG [L] |
| Suzuki first variation = Weil energy; Cayley ladder = Li; Li couplings `=−2` window form over `𝔽_q` | RHTower, ALG, GWZ [L] |
| Hodge index = Metzler sign of the Cayley ladder = Li positivity | ALG [L] |
| Anchor flow: contact is `Ψ` unbounded | CSTW, AIF [L] |
| Theta spectrum = Eisenstein coefficient sum; columns add; current `=2\|Ξ\|²Re ξ′/ξ`; Ξ-current lift with the pole as worst fibre point | CAF, TCS, AIF, PTT [L] |
| Isolation = Carleson separation; `N(ρ)=Πϱ^m`; rate 2 isolated, `2θ` otherwise | MZF, AIF [L/D] |
| Causal certificate ⇔ Schur band; over `𝔽_q` ⇔ Castelnuovo ⇔ Abel budgets reach 1 | GWZ, AIF [L] |
| Abel log-mean ⇔ `I` at infinity ⇔ depth density `o(T)` ⇔ density-zero damping deficits | AIF, ASH [L] |
| ¬AAL ⇔ finite oscillation of `ψ(x)−x` ⇔ two-prime dilation annihilation; ¬AAL ⇒ attained top excess | ZCG, RHTower [L] |
| Zeros = power-law kernel of the cut system; finite-energy kernel mass decides RH | RAC [L] |
| Λ = intersection number of torsion cycles; prime form = −renormalized positive torsion energy | AE [L] |
| Power-saving Liouville bound = zero-free strip; exact floor identity pins `λ`; twin pairs carry a quarter floor | RAC, AAD, AGT [L] |
| Count law ⇒ Hasse at genus one; FE at genus two does not force damping; integrality bounds genus by trivial zeros | ASH [L] |
| Krein square = degree form = Turán determinant of echoes = Castelnuovo–Severi defect; graph Lax–Phillips metric Hilbert ⇔ damping | ASH, AE [L] |
| Horocycle rate ⇔ zero-free region; Lax–Phillips decay `e^{−t/4}` ⇔ RH; Farey discrepancy ⇔ RH; Farey ↔ Mertens ↔ nerve Euler characteristic | BHR [L/S], RHTower, HWV [L] |
| Zeros of ζ = zeros of every Euler tail; returns at zeros tail-bad; head frozen below `1/log y`; recurrence dichotomy | TAPO [L] |
| Proportional saving ⇔ no early heavy return; first return bracketed at every precision | TAPO, PTT [L] |
| Certificates past the abscissa ⇔ tail-good heights | TAPO, PTT [L] |
| Conditional tail laws end at the Kronecker scale `≈log T`; arithmetic mean values pay off-diagonals by collision counts; necessary mollifier length `exp(c log²T)` = Euler mollifier over primes `≤c log²T` | APR, PTT, TAPO, SPAL [L/D] |
| ζ isolated in FE defect, count distance and exact parity identity; every one-off fails at the critical line | APD, SPAL, RAC [L/D] |

## Strength of the open walls

- **RH:** Σ1, Σ2, Σ3a, Σ6 (all ranks), Σ7, Σ8, Σ17, Σ18, Σ19, Σ20, Σ28 (subexponential), Σ30, Σ32, Σ49, Σ56, Σ61, Σ66, Σ67 (all `d`), Σ70 (sign), Σ72 (all orders), Σ73, Σ74, Σ76–80, Σ85, Σ93, Σ101, Σ113, Σ114, Σ122, Σ129, Σ130, Π2, Π4, Π11h, Π17, Π23, Π28 (trivial point), Π30, Π36, Π42, Π47–50, Π58, Π59, Π62, Π63, Π66, Π68, Π69, Π78, Π81 (finite energy), Π105, Γ1, Γ4, Γ5, Γ8, Γ16, Γ19, Γ24, Γ46, Γ52–54, Γ61, Γ62, Γ76, Γ78, Γ86, Γ90, Γ91, Γ95, Γ97, Γ110, Γ113, Γ114, Γ121 (rate `¾`), Γ122.
- **≥qRH:** Σ4 (`K_ζ`), Σ28 (exponent `<½`), Π5, Π17 (log stage), Π23 (fixed degree), Π42 (dyadic), Π70 (polynomial rate), Π84 (power saving), Γ121 (interior horocycle exponent), `N_d` bounded, ZAL, inner-field decay.
- **sub:** Σ82, Σ1d, Σ1e, Σ1g, Σ1j, Σ1m, Σ1q, Σ6 (each rank), Σ30 (each stage), Σ47, Σ50, Σ70 (rate), Σ72 (band), Σ86, Σ92, Σ94, Σ99, Σ100, Σ116, Σ117, Σ118, Σ131, Π7, Π9, Π11f, Π12, Π22, Π40, Π51–54, Π57, Π65, Π80, Π87, Π90, Π94, Π96, Π103, Γ15, Γ47, Γ57, Γ65, Γ68, Γ69, Γ71, Γ74, Γ104, Γ106, Γ123.
- **indep. / method:** Π16, Π97, Π101, Γ49, Γ56, Γ124, Σ127.
