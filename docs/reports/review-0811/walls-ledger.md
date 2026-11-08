# Walls ledger — status quo

**Corpus checkpoint:** commit `48ce5506c8` plus the working tree of 2026-11-08.

Three wall families carry the frontier. **Σ** is the critical sign of the window form, **Π** the precision and production of the prime count, **Γ** the selection of ζ and the reflection of its zeros. RH ⇔ `κ=0` ⇔ `a*(ζ)=⊤` ⇔ `λ*(c)→0` ⇔ `N_d=0` for infinitely many `d` ⇔ ZAL ∧ AAL ⇔ `Q` on integer probes is the Tate limit of a count [L]. None of these receivers supplies its arithmetic input.

**How the three families split one problem [D].** By the uncertainty principle no test is compactly supported on both sides of the explicit formula. Σ fixes a compact prime side (windows); the zero side then has infinite rank and only an exact sign can decide. Π localizes the zero side (Gaussian or band-limited weights); a crude bound then suffices (HCF: one upper bound per rational height ⇔ RH [L]) but the prime side is an infinite sum needing square-root precision. Γ is the involution `ρ↦1−ρ` (the functional equation) and the selection of ζ. On curves the functional equation, together with power-sum elimination, turns a crude count into the sharp bound (Γ125); over ℤ that self-improvement is AAL, literally "eventual abscissa bound ⇒ global bound" (Γ136), with the functional equation as the forced ingredient (Γ124). The curve proof in Lean has finite rank, a finite prime side and the functional equation at once; ℤ never has the first two together.

[Frontier](../rh-current-frontier-map.md): **38 live formulations, 9 candidates** (APF, EGC, EWJ, FEL, IRK, MSC, RFHM, W1C, WBF). HJ→PA and BSH→CDC are aliases. [Scoped obstructions](../rh-killed-routes.md) separate failed mechanisms from open replacements.

- **Σ is the sign of every window, and nothing else.** RH ⇔ some weight is admissible on every window ⇔ `Ψ=½log H₁` locally bounded ⇔ `Ω_ψ(a,X)≥0` [L]. At the critical curve the whole-space, PSD, polar-payment and high-conductor thresholds form one chain ending at `⨅_A windowThreshold(A)`, each `=⊤` iff RH (Σ129) [L]; at every fixed ratio every conductor channel except the pole is paid (Σ1v) [L], and the pole at every ratio is RH (Σ130) [L]. Below the onset the form bootstraps itself only by exchanging aperture for ratio (Σ1w) [L]. The theta all-rank problem is the sign of a head whose leading term is the square of a critical-line partial sum of ζ (Σ133) [L/D].
- **Π is the same sign on the prime side.** All unconditional savings sit at the VK curve; under RH the stencil exponent lies in `[¼,½]` (Π70). Farey discrepancy, the Mertens function, the Euler characteristic of the prime-star nerve and the reduced Euler characteristic of the connected prime core are one number (Π105, Π107). The persistence of the prime-product complex is classified completely and independently of `s` (Π106): homotopy and homology carry `M(N)` only as a signed count of a fixed barcode. Over ℤ there is no crude regime between strips and RH (Π111) [D/L].
- **Γ is the same sign on the zero side.** RH splits as ZAL ∧ AAL [L]; AAL is the implication from eventual to global abscissa bounds and is invariant under symmetric shifts `ξ(s+a)ξ(s−a)` (Γ136) [L]. Every one-off countermodel fails at the critical line (Γ124); positive two-prime polynomials and positive Hecke polynomials annihilate every finite zero set (Π102, Γ137); rational relocation of ζ's own zeros is detected by positivity at the first integer gap (Γ135). A count law has a quadratic half, which is the functional equation, and a count half, which is universal damping (Γ126); over ℤ the quadratic half holds unconditionally and the count half is RH (Γ131). The count law holds on every hyperelliptic curve, produced by Stepanov from a crude bound at every level (Γ125). Every horizon observable — pulse, horocycle, Farey count, Lax–Phillips mode, Narain remainder, cusp energy — reads the zero-free strip on the width axis, and the RH rate is `¾` in space and `e^{−t/4}` in time (Γ121, Γ122, Γ132, Γ134).

Status: **Solved** (the face is a theorem), **Partially solved**, **Sharpened** (open, with its exact form a theorem), **Open**, **No-go** (the mechanism is refuted), **Classified** (answered by a classification or identification), **Reduced** (theorem-level equivalent of the wall named), **Scoped** (a theorem whose stated hypothesis needs its scope read). Strength: **RH**, **≥qRH**, **sub**, **indep.**, **identity**, **method**. Evidence: `[L]` Lean source; `[K]` Lean with transitive axiom audit; `[S]` Lean source unfinished, unintegrated or uncommitted; `[P]` paper only; `[D]` deduction; `[N]` numerical; `[C]` classical, not formalized.

Notation. Windows `[−a,a]`; `c_ψ(t)=W(ψ(·−t),ψ)`; `w_n=Λ(n)n^{−1/2}`; `δ` sliver width `2c−log n` (in zero statements the depth `Re ρ−½`); `ρ³=ρ+1`; `a_k=weilFloorApertureTower k`, `181/500<a₀<181/500+5·10⁻⁷`; `λ*(c)` best margin; `N_d` non-real root count of `R_d(Ξ)`; `E` exceptional values of ζ; `r` anchor reflection, `L=artanh r`; `Ψ=½log H₁`, `q=Ψ′`; `ϱ` pseudo-hyperbolic ratio; `L=log T` in near-line statements, `L=log|t|`, `ℓ=log L` in orbit statements; `I(w)` inner field; `R=c⁸/log N`; `W₈(H)=∫H²e^{−8y}`; `Q₁=⌊(log N)^{13/32}⌋`; `R_c`, `R_polar`, `R_high` whole-space, polar-payment and high-conductor critical thresholds; `κ₀=2+γ−log 4π`; `R(y,η)` first return of the primes `≤y` at precision `η`; `E_y` Euler head, `ζM_y` Euler tail; `A_φ(y)` mean of a pseudo-Eisenstein series along the closed horocycle of height `y`; `m_g(y)` energy of a cusp form `g` on that horocycle; `Λ_g` completed Rankin–Selberg function of `g`; `A_YZ(y)` double target-horocycle heat average of the Narain scalar partition; `𝒬_t(x,y)=y²−txy+qx²` Krein square of a black hole `(q,t)`; `Q(a)` the Weil form on integer probes `a∈ℤ^N`.

## Σ — critical sign

| Wall | Status | Strength | Content |
|---|---|---|---|
| Σ1 Weil's sign | Sharpened | RH | RH ⇔ `Q≥0` on every window ⇔ `a*(ζ)=⊤` ⇔ two-site PD ⇔ band at the centre in both sectors ⇔ Stieltjes jet moments ⇔ lattice Schur parameters in `(−1,1)` ⇔ `windowThreshold≡⊤` ⇔ every critical threshold `=⊤` (incl. `R_polar`) ⇔ `1∈ℋ(c)` ∀c ⇔ `λ*(c)→0` ⇔ every window cone nonempty ⇔ every growth step a translation contraction ⇔ Cayley ladders NSD ⇔ Suzuki first variation `≥0` ⇔ mollified Jensen stability ⇔ Krein positivity ⇔ prime-blind positivity ⇔ odd BPY Poincaré inequality ⇔ no finite contact ⇔ outer predictor at every window ⇔ every echo in its Schur band ⇔ every orbit correlation relatively compact ⇔ `Ω_ψ(a,X)≥0` ⇔ `Ψ` locally bounded [L]. |
| Σ1a Critical overlap and receivers | Solved | — | `c*_N≍L(log L)²`; tilted-spline and unit-bump receivers; one Beurling profile realizes every finite rational Gram [L]. |
| Σ1b Subcritical regime | Solved | sub | Complete matrix PD for `1≤c≤(log N)^α`, `α<1/8` [L]. |
| Σ1c Joint shell–pole payment | Solved | sub | Prime-successor edges pay nonconstant packet mass [L]. |
| Σ1d General profiles | Partially solved | sub | Every compact C² profile: energy `≥ae^{−Bc}‖x‖²` on conductors `≤N^θ`, `θ<¼`, `c≤b log log N`; subpolynomial spans carry super-log-log clocks [L]. |
| Σ1e Conductor barrier | Partially solved | sub | Count form uniform for `m=o(c)`; low block `m≤Q₁` keeps half its diagonal plus its polar part at every ratio [K]. |
| Σ1f Defect-only confinement | No-go | — | `Q<2^k` witnesses [L]. |
| Σ1g Haar / Gamma graph | Partially solved | sub | All-detail prime–pole cancellation `O(e^{−√log Y/92160000})`; index `≤R+A`; growing Euler heads have unbounded index; nonfirst source keeps `1−ε` of Gamma [L]. Either sign of the unnormalized wave and the complete odd payment open. |
| Σ1h Smooth logarithmic profile | Solved (to `ε₀c*`) | sub | Positive to `ε₀L(log L)²` [L]. |
| Σ1i Second order on horizon blocks | Classified | — | `κQ(H)+(βJ/K)∫e^{−(β+1)y}H²` [L]. |
| Σ1j Critical-curve decomposition | Partially solved | sub | Fixed independent mean-zero periodic families eventually PD at every ratio; distinct primitive conductors decouple at second order; frequency pole of order `β+1` with untwisted finite part `βJ/K` [L]. Growing families and coalescing frequencies open. |
| Σ1k Whole space at one critical multiple | Solved | sub | PD at `c≤2K₀(log N)^{1/8}` with complete Schur payment [K]. Every `K>0` is B6. Cofinally `xiDampedSourceWork(n+4)≤2` ⇔ RH [L]. |
| Σ1l Window threshold | Reduced (to Σ56) | RH | `windowThreshold A=⊤ ⇔ A/2≤a*(ζ)`; `=⊤` for `A≤2a_k`; every critical pencil positive there. `windowThreshold A₀=⊤` ⇒ `windowThreshold A≥c e^{3A₀}` ∀A (IMS cutoff, prime `3/2` bound, pole moment cross) [L]. |
| Σ1m Polarization inheritance | Partially solved | sub | Twisted sectors with positive scalar second order; short windows; cosh hyperplane [L]. |
| Σ1n Bulk below the grid | Classified | — | Reads only the pole [L]. |
| Σ1o Aperture-independent weighted floor | Solved (size-only) | — | `Q(H)≥−F(p)∫e^{−pu}H²`, `p>1`, explicit `F(p)` [L]. |
| Σ1p Terminal windows | Classified | — | Polar source with nontrivial kernel; long-index cancellation on near rows [L]. |
| Σ1q Receiving charges | Classified | — | Capacity `log log N+O(1)`; receiving vectors with vanishing physical energy read at `1/80`; gcd-twisted charges split into four channels; fixed periodic `F`: `J_N=O(log N)` iff gcd profile; non-gcd twists coercive up to the admissible period scale `M₀(N)→∞` [L/K]. Near-gcd families and periods beyond `M₀(N)` open. |
| Σ1r Conductor packets and correctors | Classified | — | Terminal sources concentrate at the pole; correctors cannot improve zero-source windows [L]. |
| Σ1s Far reserve and the high-conductor threshold | Classified | sub | `farMargin R=3D/(8R)−C−C′R`; coercive on conductors `>N^θ` for `0<R<R*`; joint complement coercive for `0<R≤min(1,5R*/6)`; on the complement of `V_{Q₁}` eventual PD and PSD hold exactly below `R_high=⨅_A windowThreshold(A)` [L]. |
| Σ1t Prefix Schur cost | Partially solved | — | `(tail z)ᵀ(D−BᵀA⁻¹B)(tail z)=zᵀWz−rᵀA⁻¹r`, `A⁻¹≤20`; floor `(a/2)e^{−Bc}‖z‖²` on conductor blocks `≤(log N)^{1/32}` [L]. |
| Σ1u Polar payment threshold | Sharpened | RH (all `R`) | `R_polar` = sup of ratios paying polar capacity on every compact terminal window; `0<R_c≤R_c^{PSD}≤R_polar≤R_high`; `R_polar≥c₁e^{c₂a}` for every `0≤a≤a*(ζ)`, universal `c₁,c₂`, with zero log loss [L]. |
| Σ1v One remaining channel at a fixed ratio | Reduced (to Σ130) | RH (all `R`) | At `c_N⁸/log N→R>0`: physical Schur ratio `→4/13` for every collar debit; conductor-adapted far complement decouples; for every `ε` a finite conductor prefix `m₀(R,ε)` leaves residual coupling `≤ε`; eventual PSD of the complete matrix ⇒ polar payment on every window [L]. Every fixed nonpolar conductor has vanishing top-window `ℓ²` row, uniformly on critical bands; deep conductor residuals vanish at every ratio; whole-space collar Gårding: `completeWeilEnergy + cB‖U‖² + (Cc/log N)b₁²` dominates the low-packet, complement, collar, `W₈` and Lévy reserves, so the sole scalar loss is the conductor-one coefficient square `b₁²`; primitive nonpositive directions have compact collar profiles [L]. What remains is the pole channel `m=1`, its retained diagonal and the collar `L²` debit. |
| Σ1w Aperture exchange below the onset | Classified | sub (each `a`) | Window positivity at half-width `a` ⇒ no zero of depth `≥¼` up to height `e^{a/K}`; `|Φ(L)|≤Ce^{L/4}` for `K(L+2)≤a`; Mertens lag `≤Cx^{−1/4}`; sharp pole self-energy `|e^{−s}D(s)−κ₀|≤Ce^{−s/2}` and compressed pole cross pairing for `K(2s+2)≤a*`; `|Σ_{n≤e^t}Λ(n)/n−t+γ|≤Ce^{−t/8}` for `K(t+2)≤a`; `|ψ(x)−x|≤Cx^{7/8}` when all zeros to height `√x` have `β≤¾` [L]. Information moves from aperture to ratio and back at single-exponential exchange; `a*(ζ)` is not raised. |
| Σ1x Spline aliasing and Gamma reserves | Classified (no-go for uniform reserves) | — | Integer differences raise harmonic zeros but keep the order-seven alias notch, fixed by the spectral tail; the local leading Gamma energy is the physical autocorrelation Gram; resonant two-copy profiles defeat every uniform logarithmic coefficient-norm Gamma floor [L]. |
| Σ2 Edge, zero modes, hard Lefschetz | Sharpened | RH | RH ⇔ HL on the PSD locus; zero modes radical and two-site; Hodge index = Metzler sign of the Cayley ladder = Li positivity [L]. |
| Σ2a Interior-gap continuation | No-go | — | `κ(d)=1_{3∣d}` [L]. |
| Σ2b Edge singularity | Classified | — | No smooth eigenfunction, constrained ground state or capacity maximizer [L]. |
| Σ3 Stars and dilation monodromy | Partially solved | — / RH | Stars isometric; squarefree prime complex ≃ wedge of spheres over odd squarefree `N/2<m≤N` [L]. |
| Σ3a Coprime stratum | Sharpened | RH | Redheffer `det=M(N)` = reduced Euler characteristic of the nerve up to sign; `χ̃=Ω±(√N)`; RH ⇔ `χ̃=O(N^{½+δ})` [L]. Topology of the complex: Π106, Π107. |
| Σ4 Finite index / heat count | Sharpened | ≥qRH (`K_ζ`); RH (`K_ζ⊠K_ζ`) | `κ<∞` ⇒ Lindelöf; RH ⇔ index `0`; window index counts critical lengths; TFAE: `κ(K_ζ)<∞` ⇔ index finite on one two-prime lattice ⇔ finitely many off-line zeros ⇔ bounded non-real heat count for `t>0` ⇔ every zero above some height on the line; `N_d` bounded ⇔ `κ<∞`; under finite support RH ⇔ one non-blind prime tower PD [L/K]. Whether finite index forces index 0 is B13 (§3 of the summary). |
| Σ5 Collision quantum / window integer | Reduced (to Π17) | RH | Index `0` ⇔ Wiener–Hopf invertibility [L]. |
| Σ6 Rank / degree uniformity | Partially solved | RH | TH ranks `≤14` PD for `0<a≤½`; rank `N` on the VK collar; rank `N` from verified height `41+6(N+2)log(N+2)` (`a≤½`), `D(N+1)³+1` (`a≤¾`); first-atom tails PD at every rank; `θ₁+θ₂` and every chain `q^n` PD at every rank [L]. All ranks reduce to the frequency-adaptive head `M(b)=⌈|b|/2+B⌉`: the omitted pair sum costs at most half the first-atom floor `aC_Γ/cosh(πb/2)` in every polynomial-square integral [L]; the head is Σ133. |
| Σ7 Window Markov capacity | Sharpened | RH | RH ⇔ `R≤½` on the odd sector [L]. |
| Σ8 Realization | Sharpened | RH | Every window has an `ℓ²(zeros)` realization ⇔ RH; no finite-dimensional norm realization on any positive window; `N` integer slopes need rank `≥N` under RH [L]. |
| Σ9 Explicit image / resolvent | Partially solved | RH in strip | Depth identity for `σ>1` [L]. |
| Σ10 Local signatures and gluing | Solved | — | `κ(φ_c)=κ+1` [L]. |
| Σ11 Product-formula gluing of the pole | Classified | — | Local poles add squares [L]. |
| Σ12 Running counterterm | Solved | — | `log N−γ` cancels the prime diagonal [L]. |
| Σ13 Tensor amplification | No-go | — | `K_ζ^n` PD ⇔ RH; tensor-square index `∈{0,∞}` [L]. |
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
| Σ56 Onset aperture of `ζ` | Sharpened | RH | RH ⇔ `a*(ζ)=⊤`; off RH contact is attained; ground energy crosses zero at most once; `log R_high≥6a*(ζ)+log c₀`; `log R_polar≥c₂a*(ζ)+log c₁` [L]. |
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
| Σ71 Datum of the window cone | Classified | — | Critical log-conductor `=−λ*(c)`; datum region convex, `⊆{β≤1}`, `(1,0)` in it ⇔ RH; `β≤1+K(1+\|s\|)/c` [L]. |
| Σ72 Centre jets and the slice band | Partially solved | RH (all orders); sub (band) | Taylor coefficients PF₂₀₀; slice coefficients `≥0` for `\|t\|≤133/2`; off-line zeros have `\|Im\|>67`; the fourth reciprocal trace excludes every zero with `\|Im ρ\|≤12` [L]. |
| Σ73 Hausdorff rows | Sharpened | RH | Rows nonnegative for `r≥min(C₀(k+1)²,S(k))` with explicit shift `S(k)`; remaining entries ⇔ RH; HJ exterior diagonal at `218/25` [L]. |
| Σ74 Heat-grid detectors | Sharpened | RH | Two fixed grids at every degree ⇔ RH; bounded chirp ⇔ RH; one-sided Gaussian prime ceiling at every rational height ⇔ RH [L]. |
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
| Σ87 Compactness at a critical ratio | Solved (assembly) | sub (each ratio) | Γ-liminf with weight `α_R`; strong `L²` limits from bounded form; physical and Fourier tails give precompactness; one-sided spline mollification and Kolmogorov–Riesz give `R_high≥⨅wT` [L]. |
| Σ88 Limit pencil at a fixed ratio | Classified | sub | `κQ+(7J/R)∫e^{−8y}H²≥0` on smooth families is a window statement; nonpositive directions meet the top window of length `(1/8)log R+O(1)` [L]. |
| Σ89 Parabolic blindness | No-go | — | `Φe^{−τx²}` has the same parabolic laws and non-real zeros for `t<τ` [L]. |
| Σ90 Central inequality | Classified | stronger than RH | `g_t²≥c·min(t,log⁻²X)` everywhere ⇒ RH and `c(m+1)≤24` [L]. |
| Σ91 Gap dynamics | Solved (laws) | identity | Gap law, mesh bounds, profile gap `16/k≤μ²≤24/(k+1)`, maximum principle; all assume reality in the cylinder [L]. |
| Σ92 Crystal on typical heights | Partially solved | sub | `Λ_X log X→0` on density one; exceptional measure `≤T^{θ(κ)}`, `θ(κ)=1−κ³/41943040000`; crystal law outside `δT` [L]. |
| Σ93 Collision frequency | Sharpened | RH | `N(σ)<1` excludes a double zero; multiplicity `≤(3300/9991+ε)log X` [L]. |
| Σ94 Depth law | Partially solved | sub | Isolated simple zero: `d−7η≤Λ_Xlog(X/2π)≤d+17η` [L]; crowded and multiple zeros open. |
| Σ95 Pointwise two-prime payment | No-go | — | Negative at centre `log 6` [L]. |
| Σ96 Euler-operator theta spectrum | Solved (identity) | identity | `S=Π_pT_pA`, `T_p=(1−2cos(b log p)σ_p+σ_p²)^{−1}`; `A` not a positive Laplace mixture [L]. |
| Σ97 Torus-uniform theta positivity | No-go (numerical) | — | Negative once primes `≤19`–`47` are free [N]. |
| Σ98 Finite theta heads | No-go (fixed heads) | — | No fixed head pays its uniform remainder at every rank; no frequency-uniform summable absolute pair majorant on the Gamma scale (diagonal coefficients harmonic); no compact core funds every Gamma polynomial direction (monomials: core `≤2R`, Gamma `≥R·4^n/cosh(3πR/2)`) [L]. Survivor: the adaptive head (Σ6, Σ133). |
| Σ99 Local onset field | Partially solved | sub | `Ω_ψ(a,X)` sum over zeros; pair cost `≤(16/9)δ²a⁴‖ψ‖²`; RH ⇔ `Ω≥0` [L]. |
| Σ100 Runs on the critical line | Partially solved | sub | `≥N(T)/5000` starts of five consecutive simple critical zeros [L]. |
| Σ101 Causal certificate | Solved (identity) | RH (all windows) | PD ⇔ positive-margin outer predictor; RH ⇔ outer predictors on every window [L]. |
| Σ102 Szegő threshold | Classified | RH (position) | `s>0` square-summable reflectors, `s<0` negative witness, RH at `s=0` with `Σγ²=∞` [L]. |
| Σ103 Reflection coordinates | Classified | — | Reflection data free; passive iff each echo in its band; forward map causal injective [L]. |
| Σ104 A priori estimates free of `1/μ` | Solved (model) | sub | Born model `1−r_n²≥e^{−10A}/(2√n log n)` [L]. |
| Σ105 Soft prime kick | Solved | identity | `(Ψ(x)−Ψ(a))log(1/(x−a))→Λ(n)/√n` at `2a=log n` [L]. |
| Σ106 Green corner | Solved | identity | Kato contraction; `q_y→q` in `L¹` on compact precontact intervals [L]. |
| Σ107 Far-translate decoupling | No-go | — | `c_φ(t)↛0` for every nonzero test [L]. |
| Σ108 Insertion cone | Classified | — | Below left growth `½` Hecke cone = torus cone = exponential convexity; `½` exact threshold of the `L²` prime-pair cone; torus cones closed under `e^{−βy}` [L]. |
| Σ109 Fixed-amplitude locking | No-go | — | Locked positivity ⇔ torus positivity for fixed amplitudes; only amplitudes oscillating with the height escape [L]. |
| Σ110 Columns add | Classified | — | Infimum of signed columns = sum of minima; base pays by size when `Σlog p/(p^{½+a}−1)<½log(b/2π)` [L]. |
| Σ111 Curve flow | Solved (calibration) | — | Unitary ⇔ first `R` margins positive [L]. |
| Σ112 Theta current | Solved (explicit) | identity | `current=2\|Ξ\|²Re ξ′/ξ`; explicit core and tail; `\|current a b\|≤3.6·10⁷\|a\|e^{−(7/5)\|b\|}` for `\|a\|≤½` [L]. |
| Σ113 Restoring bound of the actual chain | Solved (identity); control open | RH | `\|L(x)\|≤artanh e^{−2(x−c)}+2osc_{[c,x]}Ψ`; RH ⇔ `L` locally bounded on precontact intervals ⇔ `Ψ` locally bounded; off RH `L` is unbounded above every base [L]. |
| Σ114 Bohr profile decomposition | Classified | RH (for ζ) | RH ⇔ every orbit correlation relatively compact [L]. |
| Σ115 Critical Γ-liminf | Solved | identity | `liminf Q(U_N)≥Q_T(F)+α_R∫_{y<0}F²e^{−8y}` [L]. |
| Σ116 Weighted Gårding | No-go (full horizon); Solved (top collar) | sub | Fails on `(V₁)ᗮ` for every `B` (deep atoms, `W₈≍N⁸`); top collar `Q+B_R‖U_y‖²≥κ_R·seventhMass+a_RW₈` at every `R` [L]. |
| Σ117 Typical-height sign | Partially solved | sub | At `A=δlog T/(64M²)`, outside one set of measure `δT`, every shaped test has `Q_γ>0`; bad set Gaussian-tailed `≤209(4kδ²)^kT`, `≤T^{1−1/(64K)}` at `A=K log log T` [L]. |
| Σ118 All-height sign | Open | sub | Size reaches `a≈log log X−log 4` [D]; past it Π80, Π87. |
| Σ119 Tangent of the forward map | Solved | identity | `∂E_n/∂λ(n₀)=−(2/√n₀)A_n(log n₀)`; margins concave [L]. |
| Σ120 Certified passivity | Solved (certified windows) | sub | Full causal chain on total length `≤2a₀` [L]. |
| Σ121 Bounded extremals for every weight | Solved | identity | Attained bounded ground state, exact edge law, explicit sup bound [L]. |
| Σ122 Prefix–collar coupling at a critical ratio | Reduced (to Σ130) | RH (all ratios) | Physical tearing fails at Schur ratio `4/13`; conductor-adapted splitting decouples; finite conductor prefixes resolve the low packet (Σ1v) [L]. |
| Σ123 Kernel-valued prime payment | No-go (returning coordinates) | — | `\|S\|≤\|G\|` for decompositions in returning prime coordinates; Euler coordinates cannot cross `Re s=1` [L]. |
| Σ124 Critical coupling of the base | Classified | — | `thetaAmp(x)e^{x/2}→½` [L]. |
| Σ125 Certificates on the orbit | Classified | — | For `σ>1` the Ξ-current lifts to `𝒥_σ(t,ω)` with the pole as worst fibre point: a frozen certificate exists exactly when `−ζ′/ζ(σ)≤B(σ+it)` [L]. |
| Σ126 Top logarithmic window | Solved (non-escape) | sub | `log S_R≤(1/8)log(R+1)+C₀`; every nonpositive direction meets the top window; below `c₀e^{6a*}` every nonzero nonpositive vector charges both `V_{Q₁}` and the top window; signed-PNT bridge confines nonpositive directions to `A_R≤¼log(R+1)+C` [L]. |
| Σ127 Splitting order at a critical ratio | Classified | method | Prime quasimode split across the collar: Schur ratio `→4/13` at every `R` and `B_R`; conductors `≤N^θ`, `θ=(1+log log N)^{−5}`, kept whole: `o(1)` decoupling [L]. |
| Σ128 Certificates past the abscissa | Classified | — | On `Re s>½`, `Σ_p\|1−E_p(s)\|<∞` ⇔ `Re s>1`; head–tail certificate Schur exactly where `\|S\|≤\|head\|` [L]. |
| Σ129 Critical positivity threshold law | Classified | RH (all thresholds `=⊤`) | `0<R_c≤R_c^{PSD}≤R_polar≤R_high=R_high^{PSD}=⨅_{A≥0}windowThreshold(A)≥c₀e^{6a*(ζ)}`; every stage `=⊤` ⇔ RH ⇔ `a*(ζ)=⊤` [L]. The pole-orthogonal threshold equals the window threshold: `R_pole=⨅_A windowThreshold(A)` [S]. Whether `R_c=R_high`, i.e. whether the pole direction lowers the whole-space threshold, is open (B104). |
| Σ130 Low-packet payment at every ratio | Reduced (to Σ1) | RH | `S_A(h)²/D(R)≤a_φQ(H)+(7J(1)/R)M₈(H)`; payment at `R` on `[−A,0]` ⇒ `R≤windowThreshold A`; payment at every `R` on windows of length `→∞` ⇒ RH; payment on every window for `R≤c₁e^{c₂a}`, `a≤a*` [L]. |
| Σ131 The cone counts primes | Partially solved | sub (finite range) | Every weight system in `𝒜(c)`: local density `1+O(e^{−a})`; short-interval law at every resolution; `\|ψ_λ(X)−X\|≤CX^{5/6}log X` for `X₀≤X≤e^{2c−3}` [L]. Window positivity is a count with power saving on the window's range. |
| Σ132 Frequency packets | Solved (identity) | identity | `∫Re W(f⋆φ_X)dX=2π‖φ‖₂²Re W(f)`; a negative test has negative packets on a set of positive measure [L]. |
| Σ133 The theta head is a critical-line partial sum | Sharpened | RH (all ranks) | For fixed `M`, the pair head at frequency `2τ` over the natural Gamma weight equals `(4/√π)\|Σ_{n≤M}n^{−½+2iτ}\|²+o(1)`, a positive Gram square [L]. The adaptive head has `M≈\|b\|/2`, i.e. a partial sum of length half the height, which approximates `ζ(½+ib)` to `O(\|b\|^{−½})` [C]; uniformity of the fixed-`M` asymptotic at `M=M(b)` is open [D]. The all-rank sign is decided where the leading square is small — near the critical zeros of ζ — by second-order terms. |
| Σ134 Reflected pairs at the decay boundary | Classified | — | Exponential evaluation pairs with rates `p/2±δ`: sharp bounds `1/p±1/√(p²−4δ²)` for `p>2\|δ\|`; no `L²` lower bound for `p≤2\|δ\|`; pair positivity iff `δ=0`, at every ordinate [L]. |

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
| Π40 Self-improvement of a strip | Open | sub | `Θ<1⇒Θ=½` false for shifted products `ξ(s+a)ξ(s−a)` (FE and Euler product retained) [L]; no mechanism. |
| Π41 Necessary-length laws | Solved (necessary bounds) | — | Excess `K₀/log T` forces `log N≥log²T/(6K₀)−(4/3)log T`; moment `→1` forces `log N/log T→∞` [L]; in Euler form, the length of an Euler mollifier over primes up to `≈c log²T` [D]. |
| Π42 Long-mollifier receivers | Sharpened | RH; ≥qRH | Slope exact; cofinal bound self-improves to `K=6`; strict slope saving ⇒ RH [L]. |
| Π43 Length–precision law | Classified | — | Length `T^θ` sees `εn^{−η}` iff `η<½−1/(2θ)` [L]. |
| Π44 Explicit contour and mass bounds | Solved | — | `\|M(T)−(T/π)(log T−log 2π−1)\|≤80+65log T` [L]. |
| Π45 Bulk statistics of Jensen roots | No-go | — | Cauchy law holds for every backward heat flow [L]. |
| Π46 Entry filters | Classified | — | Type I/II parity-blind; finite linear laws have a common perturbation [L]. |
| Π47 Signed incidence precision | Partially solved | RH | `\|cost\|≤Ke^rexp(−c(2r)^{3/5}(log 2r)^{−5/3})` [L]; need `C_σe^{2σr}`. |
| Π48 Factorial-Fock seam bound | Sharpened | RH | [L]. |
| Π49 Completed Suzuki residual | Partially solved | RH | `\|A_N\|≤C√N exp(−c·vkScale N)`; bounded ⇔ RH [L]. |
| Π50 Möbius critical energy | Partially solved | RH | `≤CTe^{−c·vkScale T}`; subpower ⇔ RH [L]. |
| Π51 Vinogradov–Korobov barrier | Open | sub | Every unconditional saving sits at VK; `\|ζ(σ+iτ)\|≪(log τ log log τ)^{2/3}` on `1≤σ≤2` explicit [L]. The Narain AdS₃ remainder carries exactly this saving (Γ132). |
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
| Π65 Log-mean of ζ | Reduced | sub | Eight equivalent forms; Abel form ⇔ depth density `o(T)`. Selberg's mollifier gives off-line first moment `≤(67/1000)V`, depth `O(T)` in every window, `I(½+x+it)` bounded on `x≥1, \|t\|≤x`, Abel log-mean `≤11/2` [L]. `o(T)` open. |
| Π66 Integrality over ℤ | Solved (exact) | RH at `√` scale | Nair lattice exact; Siegel half ⇔ lower count, Liouville half ⇔ upper count; Stepanov over ℤ = integrality floor + Nair ceiling, reaching Chebyshev; the gap is the integer Chebyshev problem [L]. |
| Π67 Stencil ceilings | Classified | — | Floor `A(K)−1≥c/(√K(1+log K))`; no rate `K^{−a}`, `a>½` [L]. |
| Π68 Möbius zero condensation | Classified | RH | Zeros of `M_X` accumulate on `Re s=Θ` [L]. |
| Π69 Integer lag | Sharpened | RH | RH ⇔ lag `≤(2+γ−log 4π)√n`; `Ω±(√n)` [L]. |
| Π70 Rate of a stencil | Solved (exponent scale) | sub / qRH | Rate `K^{−a}` ⇒ `Re ρ≤1−a`; all `a<½` ⇒ RH; none past `½`; VK rates `exp(−(log K)^α)`, `α<3/5`; polynomial rate ⇔ strip; `\|M(n)\|≤Cn^{1−σ}` gives every `a<2σ/(3+2σ)`; RH gives `a<¼`; under RH the exponent lies in `[¼,½]` [L]. |
| Π71 Laws of a producer | Solved | — | `c=μ∗h`; producer = mollifier on `Re s=1`; peak law; uncertainty; compensated stencils: letters `(2y+2)`-smooth, cost `1/y`, alphabet `y³/Y` [L]. |
| Π72 Ledger blindness | No-go | — | Complete ledger of a zero mode vanishes for every balanced stencil [L]. |
| Π73 Parity ledger | Classified | — | Sieve and producer cones disjoint; parity-neutral producers reach every rate [L]. |
| Π74 Fake prime measures | Classified | — | Slope LP with strong duality; unique fake at infinite level; extremal level-`K` fake has `≤K` atoms on an optimal sawtooth's tight set [L]. |
| Π75 Hecke action on producers | No-go (positive amplification) | — | [S]. |
| Π76 Frobenius as a stencil | Solved (calibration) | — | Over `𝔽_q[T]` the Frobenius is Carlitz's factorial stencil of `1−qX`, exact ledger, rate 0; over ℤ the inverse of ζ is an infinite series, every integer is a cut, rate `≥c/(√K(1+log K))` [L]. |
| Π77 Near-extremal rigidity | Solved | identity | Near-extremal families converge to `1/E` [L]. |
| Π78 Holomorphic Abel budgets | Open | RH | Over a curve Castelnuovo ⇔ budgets reach 1; boundary quotients nonselective [L/K]. |
| Π79 Arithmetic Carleson measure | Solved | identity | `μ(box)≤(5/2)xI`; `I→0` ⇔ depth density `o(T)` [L]. |
| Π80 Short-sum barrier | Open | sub | Depth `d` forces a large value of a prime polynomial of length `(log γ)^{O(1/d)}`; some height `≤T` has no cancellation below length `c log T`; off a set of measure `≪TY^{−2ε}` square-root cancellation at all dyadic lengths `Y..T/log T` [L]. Missing: the exceptional set past `log T` at all heights. |
| Π81 Kernel of the cut system | Classified | RH | Zeros = power-law kernel vectors; summable kernel vectors vanish; finite-energy mass annihilation ⇒ RH [L]. |
| Π82 Ledger hierarchy | Solved | — | Degree `k` ledgers have order `m−k`; exact ledgers holomorphic off `s=1` [L]. |
| Π83 Twin at every degree | Solved | — | `T=A−2A(2s)` shares every leading pole of `A^k` at right zeros [L]. |
| Π84 Parity exponent | Solved | ≥qRH at power saving | `L(x)≪x^a` ∀`a>Θ` ⇔ zero-free `Re s>Θ`; `Σ_{k≤x}F(⌊x/k⌋)=⌊√x⌋` forces `f=λ` [L]. |
| Π85 Exchange law | Solved | — | Exchange of exponent `<σ` keeps zeros right of `σ`; a new zero needs exchange mass of exponent `≥β` [L]. |
| Π86 Carry of the floor | Solved | — | A dilation of the count is an average of translations; every integer is a cut [L]. |
| Π87 Absolute non-alignment | Partially solved | sub | `Σ_{p<N}(1−cos t log p)/√p≥8/(10⁹L⁶ℓ⁴)` and `‖Σ_{n<N}n^{it}‖≤N(1−1/(10⁷L⁶ℓ³))` at `N≥48L²ℓ`; `≥t^{−δ}` at length `L^A`, `A>1` [L]. Required at the size curve `≈εL/ℓ` [D]. |
| Π88 Rounded orbit | No-go | — | Same diagonal moments, exact return at `T` [L]. |
| Π89 Discrepancy and mixing time | Classified | — | `½π(y)log(1/δ)≲log T_mix≲10y√(log y log log y/δ)` [L]. |
| Π90 Energy past the diagonal | Partially solved | sub | Gap to truth = density of smooth numbers [L]. |
| Π91 Curve stencil | Solved (calibration) | — | Linear stencils stop at `\|a\|≤q+1` [L]. |
| Π92 Prime kernel as torsion energy | Solved (identity) | — | `Λ` = intersection number of torsion orbits; sign lost in `log(1/(1−r))Σx²` [L]. Renormalized operator form: Π108. |
| Π93 Möbius as a cubic Gauss coefficient | Solved (identity); descent partial | past VK | Over `ℤ[ω]` ideal Möbius = cubic Gauss coefficient; cubic Eisenstein series, Fredholm pencil, meromorphic resolvent; residue at `4/3` nonzero with `ΔR=(8/9)R` and cubic character; Fourier modes `V·A_h(s)·H_h(s)` continued to `Re s>1` [L]. Fourier coefficients of the residue and rational transfer open. |
| Π94 First return of the prime orbit | Partially solved | sub | `R(y,η)≤Q^{π(y)}` when `2π²≤ηQ²`; weak return = spike `\|ζ(1+1/log N+it)\|≍log N`; at bounded harmonic defect `R(N,η)≥exp(c(log N)^{3/2}/log log N)`; `R(y,η)>exp(√(y/(48log y)))` once `12η√y·y⁴<c` [L]. Constant precision open. |
| Π95 Proportional saving = heavy first return | Classified | — | Defect `<cS` forces a return at precision `η` on a subset of weight `>(1−c/η)S` [L]. |
| Π96 Conditional tail law and the Kronecker scale | Partially solved | sub | Head `R` on `y`-smooth, tail `B` on `y`-rough integers: `∫_T^{2T}\|R\|²\|B\|²=T‖r‖²‖b‖²+O(N log N‖r‖²‖b‖²)`; Gaussian conditional moments while `log max A+k log Z≪log T`; fixed-resonator mean square of ζ [L]. Past the Kronecker scale no distributional law is known. |
| Π97 Moving jet of the logarithm | Partially solved | method | `Δ_h^j log x=Δ_1^j log(x/h)`; coefficients move by `≥(j+1)!/(x+j+2)^{j+2}` per step [L]. No saving derived. |
| Π98 Archimedean place versus depth | Classified | — | Depth aspect exact; height aspect additive up to `\|t\|hh′/x²` [L]. |
| Π99 Count-distance rigidity | Solved | — | Positive integer-norm Beurling system other than the rational primes has count error `≥c log n` infinitely often; odd primes plus labels of norms `3,4`: `N(x)=x+O(log²x)`, exactly ζ's zeros [L]. |
| Π100 Bounded count with a new zero | Solved (signed generators) | — | `a(n)=1−1_{2∣n}+4·1_{8∣n}`: `−3≤N(x)−x≤0`, zeros with `½<Re s<1` on a vertical progression [L]. |
| Π101 The comb of a return | Solved (polynomial reach) | method | Level sets of `t log n/2π` are multiplicative approximate groups [L]. |
| Π102 Positive Euler products with a finite top layer | Solved (countermodels) | — | Integer norms `≥2`, nonnegative integer coefficients, linear counting, exactly `3/5±iγ` on `Re s>½` [L]. Rational-prime labels, multiplicative natural coefficients, linear counting, holomorphic on `Re s>17/30` with zero set there exactly `{3/5±iγ}` [L]. Nonnegative two-prime polynomials vanish on any finite set in `Re s<1` and stay `ε`-close to `1` on `Re s≥1` [L]. Their accuracy is paid on the left: nonconstant mass is log-convex in `σ` and `≥1` at a zero, so mass `≤ε` at `σ_hi>Re ρ` forces mass `≥ε^{−(Re ρ−σ_lo)/(σ_hi−Re ρ)}` at `σ_lo<Re ρ`, sharp for monomials; at unit mass every cancelling phase is `−1`, the zero is simple and `Re` of the derivative is `≥log 2` [L]. |
| Π103 Arithmetic mean values of smooth × prime | Solved | sub | Smooth rows and prime columns: diagonal plus gcd-class collision counts; arbitrary smooth heads through the reduced-ratio height; normalized `2k`-th tail moment `≤(5π/2)(k!B₂^k+C(k!)²/(TR₂))` [L]. A prime-density saving in the collision count is open. |
| Π104 Twin quarter floor | Solved | — | `F_x(s)F_y(s)=F_z(2s)`; `Θ≤2max(θ_μ(x),θ_μ(y))`; order-two twins `max≥¼`, constant-source twins `≥½` [L]. |
| Π105 Farey, Mertens and the nerve | Solved (identity) | RH | RH ⇔ Farey `L¹` discrepancy `≤Cn^{½+δ}` ⇔ `L²` discrepancy `≤Cn^{−1+δ}`; `\|M(n)\|≤2π·L¹`-discrepancy; `M(N)=−χ̃` of the prime-star nerve; `χ̃=Ω±(√N)`; RH ⇔ every smoothed totient-weighted Farey count of order `C` is `m C²+O(C^{½+ε})`; rate `y^{½+δ−ε}` of every Farey count ⇔ zero-free `Re ρ≤1−2δ` [L]. |
| Π106 Persistence of the prime-product complex | Classified | — | Augmented homology persistence of prime supports with product `≤N` is naturally the interval module of odd squarefree `m` with bar `[m,2m)` in degree `ω(m)`, over every commutative ring; boundary at `N` = cycles at `N/2`; Dirichlet weighting `n^{−s}` gives an isomorphic persistence functor for every `s∈ℂ`. Prime-valued boundaries: free classes on `[m,2m)`, `ℤ/2` classes on squarefree labels coprime to 6 on `[2m,3m)`, torsion exponent exactly 2, nonsplit free-to-parity extension, map `N→3N` zero; two-prime block quotients compute the core over every ring; integer coefficient extension commutes with every height map [L]. |
| Π107 Connected prime core and fixed points | No-go (literal localization); Classified | — | Upper-half primes are isolated points; every self-map homotopic to the identity fixes them, hence has `≥N/(4log N)` fixed points eventually; the rest is one path component, homotopy equivalent to a bouquet of odd-squarefree composite spheres, with augmented Euler characteristic `M(N)+#primes(N/2,N]` [L]. |
| Π108 Renormalized torsion forms | Solved (convergence); sign open | RH (sign) | On `ℓ²(n^δ)`, `δ>0`, raw torsion forms are positive, absolutely convergent and, after the exact scalar counterterm `log(2ε)⟨x,y⟩`, converge in operator norm to the arithmetic limit at rate `O(ε^α)`, `2α<δ`; the counterterm limit is the tame different with conductor-uniform modulus; the conductor-1 × prime row is unbounded on unweighted `ℓ²`, `Σ_p err²p^{−δ}<∞ ⇔ δ>0`; the limit is a compact self-adjoint operator; the limit kernel is indefinite: single primes have positive energy, equal-coefficient vectors on `{p,2p}` have negative energy for large `p` [L]. The weight `δ>0` is forced, the critical form lives at `δ=0`, and the torsion form alone is not a count. |
| Π109 Sharp sources on the horizon | Classified | beyond RH | Sharp shells `a≤Im z<b`: mean `=4y(H(X_a)−H(X_b))`, `H(X)=Σ_dμ(d)Σ_m√((X/d)²−m²)`; exact decomposition; unconditional rate `y^{½}log(1/y)`; a `y^{¾}` rate needs `Σ_{d≤X}μ(d)E(X/d)=O(X^{½+ε})` with `E` the quarter-disc remainder, not controlled by RH [L]. |
| Π110 Thermal averages of the primon gas | Classified | — | Arithmetic thermal means are Euler factors: `Π_p∫KM_p·phaseLocalFactor=ζ(2e^β+1)` for every real `β`; finite Green determinant ratios multiply to `ζ(2N+3)/ζ(2)`; Kesten–McKay densities within `2/(p+1)` of Sato–Tate; likelihood span = even semicircle `L²`; logarithmic clocks non-closable [L]. All statements at real points `>1`. |
| Π111 No crude regime over ℤ | Classified | — | On curves a constant-factor bound `\|N_n−qⁿ−1\|≤Cq^{n/2}` at every level self-improves to the count law (finite rank) [L]. Over ℤ: `\|ψ(x)−x\|≤C√x` is false (`Ω±`, Π69) [L/C]; any exponent `½+ε` is RH; tensor index `∈{0,∞}` (Σ13); the only sub-RH coordinates are exponents `θ>½` (strips) and exceptional counts (ZAL, AAL) [D]. |

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
| Γ63 Poisson-extended Hecke positivity | No-go | — | Every `T_n` diagonal on Eisenstein; on a truncated resonant state the Hecke algebra has a positive Poisson measure for every `Re u<0`, not line-selective [L]. |
| Γ64 Cross-zero Gram law | Solved (identity) | identity | [L]. |
| Γ65 Cutoff line law | Solved (edge) | sub | [L]. |
| Γ66 Scattering Blaschke product | Solved | — | `φ(s)(s−1)/s` Blaschke over `(1+ρ)/2` [L]. |
| Γ67 Abscissa split | Solved (identity) | RH | RH ⇔ ZAL ∧ AAL; RH ⇔ ZAL ∧ zero-disc weak recurrence; under AAL eight RH-level statements coincide; `qRH ∨ AAL` [L/D]. |
| Γ68 Asymptotic abscissa law | Open | sub | ¬AAL ⇔ finite top and bottom layers, top excess attained ⇔ `ψ(x)−x=x^βT(log x)+O(x^{β−η})` [L]. Form of the statement: Γ136. |
| Γ69 AAL producers | Partially solved | sub | Not-attained top; bounded lag on one progression; lag `≤Me^{aL}` off a set of lower Abel density zero; polar ground energy `μ₀(B)≥−C_εe^{εB}`; one generic prime-window grid; log-dense integer lag bounded above; twisted plateaux; JAS dressed PSD, typical positivity, shell positivity (Turán power sums with a finite head); bounded towers; one bounded cone; weak recurrence; infinitely many zeros near each right zero; slow aligned returns on right discs [L]. Each retains its source bound. |
| Γ70 Zero–one law of recurrence | Classified | — | [L]. |
| Γ71 Pair recurrence | Partially solved | sub | At density-`(1−δ)` base heights [L]. |
| Γ72 Returns at a zero | Classified | — | Rare and threshold-quantized [L]. |
| Γ73 One-off countermodels | No-go (positive data) | — | Continuous Beurling systems with one off-line pair and regular integer count; discrete and integer-norm systems with linear counting (holomorphic on `Re s>½`); rational-prime Euler products with multiplicative linear counting, holomorphic on `Re s>17/30` [L]. Classical FE and critical-line continuation absent in every model (Γ124). |
| Γ74 FE-defect rigidity | Partially solved | sub | Defect `≤1/6400` forces rational primes [L]. |
| Γ75 Inner field of a column | Solved | identity | [L]. |
| Γ76 Endpoint characters | Sharpened | RH | Column Young projections nonnegative; every Young projection of shape `\|λ\|≤4` nonnegative; Toeplitz minors `≤200` nonnegative [L]. |
| Γ77 Tensor weights and compression | No-go (stated classes) | — | Golden passes; pure compression preserves even subspace iff RH [L]. |
| Γ78 Global trace on a family | Partially solved | RH | Kloosterman fibres pure by Stepanov; reciprocal tangent quadrics have exact projective counts over every extension with one excess eigenvalue `α^d`; arithmetic family containing ζ open [L]. |
| Γ79 Displacement | Classified | — | Holomorphic data carry no weighting by displacement [L]. |
| Γ80 Finite oscillation | Solved | sub | Every witness has `β=Θ`, unique `T`, quantized coefficients, remainder ceiling, bounded-log-gap sign changes [L]. |
| Γ81 Dilation annihilation | Solved (identity) | sub | ¬AAL ⇔ two-prime annihilation of `ψ` to `O(x^{β−η})` [L]. |
| Γ82 Rightmost-zero jets | Solved | sub | Diagonal `→0`, off-diagonal `→m²`, short shifts `o(1)` [L]. |
| Γ83 Returns are prime returns | Solved | — | A return forces `n^{−iτ_j}→1` and a spike near the pole [L]. |
| Γ84 Isolation of ζ | Solved | identity | FE defect `≤1/6400` is one point; count distance `o(log n)` is one point; the exact parity identity pins `λ` [L]. |
| Γ85 Rational zero relocation | No-go (Bohr) | — | Not Bohr almost periodic on `Re s>1`; invisible to mean spectra in the strip [L]. Positivity form: Γ135. |
| Γ86 Modular horizon | Solved (exact solution) | RH (universal damping) | Exact metric, echo train, causal symbol, ringdown in the modes of the zeros; quarter-line bound ⇔ RH; exterior = chart of the Rindler wedge of AdS₄, black hole = quotient by `SL₂(ℤ)⊂SO(2,1)⊂SO(3,2)`; vacuum perturbations of compact profiles extend smoothly through the future horizon [L]. Cusp channel: Γ133. |
| Γ87 Raw echo decay | No-go | — | [L]. |
| Γ88 Near-arithmetic ladders | No-go | — | [L]. |
| Γ89 Blindness of physical positivity | Classified | — | Schur, KMS, reflection, `C*` positivity hold on every black hole [L]. |
| Γ90 Maximal-angle zero | Classified | RH | RH ⇔ `‖Q(tw)‖=‖Q(t̄w)‖` at zeros [L]. |
| Γ91 Lefschetz ratios | Solved | RH | Every right zero is read by `c_{m+1}/c_m→p^{ρ−½}` [L]. |
| Γ92 Fake black holes | Solved | — | Every local count is a tree quotient with flux and unitarity; `t²>4q` gives off-circle resonances [L]. |
| Γ93 Hecke rigidity on resonances | Solved | — | Commuting operators act by `X^d+Y^d`; positive families in every class exist on fakes [L]. |
| Γ94 Cuspidal sector | Classified | — | Mirror-odd data are superpositions of cusp forms; zeros couple only to the mirror-even half [L]. |
| Γ95 Krein flux law | Solved (identity) | RH (sign) | Flux `½𝒬_f≥0` ∀f ⇔ RH; on graphs the Lax–Phillips compression has rank two, `det Z=q`, Krein metric Hilbert ⇔ universal damping [L]. |
| Γ96 Count law | Solved | every genus (hyperelliptic) | Count law at all probes ⇔ `t²≤4q` at genus one; at genus `g` the count law at level `n` is the genus form `gy²−a_nxy+gqⁿx²` (half the Castelnuovo–Severi defect), existing iff `a_n²≤4g²qⁿ`; the tower count law ⇔ unitary [L]. |
| Γ97 Integer probes | Sharpened | RH | RH ⇔ `Q(a)≥0` on `ℤ^N`; fake: count not quadratic; ℤ: quadratic, count missing (Γ131) [L]. |
| Γ98 Manin's Hasse | Solved | genus one; bielliptic genus two | `K(x,y)=ht(yP₀−xP₁)` on the twisted curve over `𝔽_q(T)`; for `y²=h(x²)` the count is the sum of the Manin counts of the two elliptic quotients [L]. |
| Γ99 Throat | Solved | — | Product of modes depends only on the index nearest the cusp; FE only at genus `≤1` on a path [L]. |
| Γ100 Rank barrier | Solved | — | A compact probe excites infinitely many modes over ℤ [L]. |
| Γ101 One clock | Solved | — | Hecke at `p` = modular time shift `log p` [L]. |
| Γ102 KMS midpoint | Classified | — | `¼` is the KMS midpoint rate [L]. |
| Γ103 Horocycle is the wave | Solved | graph | [L]. |
| Γ104 Bulk log-mean | Solved | sub | Abel log-mean `→0` ⇔ damping deficits of density zero [L]. |
| Γ105 Transport count | Classified | — | [L]. |
| Γ106 Missing input of transport | Solved (receiver) | sub | Bounded translates on a domain joining ρ to `Re s>1` ⇒ infinitely many zeros right of `Re ρ−r`; a bounded return at each zero ⇒ AAL; head returns `N<1024(log τ)⁴(log log τ)²` [L]. |
| Γ107 Effective transport | Solved | sub | Discs crossing `Re s=½` force `sup\|ζ\|≥cτ^b`; on discs with left edge `σ₀∈[½,β)` slow aligned returns at each right zero give AAL [L]. |
| Γ108 Tail at a zero | Solved | — | At a zero a positive proportion of prime returns are not returns of ζ [L]. |
| Γ109 Limit map | Solved | — | Limits on `Re s>1` fill the torus [L]. |
| Γ110 Hull over the torus | Classified | RH | Liouville fibre extends ⇔ RH; RH ⇔ every nonzero limit of translates zero-free [L]. |
| Γ111 Stieltjes sign | Solved (necessary law) | — | `Im(w₀Q″/Q′)≤0` [L]. |
| Γ112 Rotated relation classes | No-go (coefficient growth) | — | Coefficients of growth `exp(C√\|w\|)` force triviality [L]. |
| Γ113 Naive height, five currencies | Sharpened | RH | Degree-two form `≥0` iff a function bounded below lies at bounded distance; window naive height exists ⇔ positive; length `≤3/5` exists [L]. |
| Γ114 Dilation quotient | Sharpened | RH | RH ⇔ zero dilation surplus ⇔ Szegő budget ratio equality; Euler prefixes invariant [L]. |
| Γ115 The tail of a return carries the zero | Solved | sub | Zeros of ζ = zeros of `ζM_y` at every cut; returns at right zeros tail-bad at every cut, density zero [L]. |
| Γ116 Head frozen at its resolution | Solved | — | `\|log\|E_y(s+iv)\|−log\|E_y(s)\|\|≤2\|v\|(log y+log 4)` on `Re s≥1` [L]. |
| Γ117 Trivial zeros of a cusp | Solved | graph | Integrality forces genus `≤` trivial zeros `+1`; `\|c₀−1\|=q^{1−g}` [L]. |
| Γ118 Genus two does not force damping | No-go | — | 11-vertex graph with the genus-two FE for every `q≥2`; first-level count law iff `q≤19`; all levels and every positive covariant quadratic form iff `q≤3` [L]. FE, flux, unitarity, Hecke, integrality and the first-level count leave damping open. |
| Γ119 Natural boundary of the hull | Solved | — | Haar-a.e., fair-coin-a.e. and order-two fibres extend zero-free to `Re s>½` with natural boundary `½`; the Liouville point extends iff RH [L]. |
| Γ120 Extremal law has a model | No-go | — | `w²−2w+2` satisfies the full maximal-angle inequality with off-axis zeros [L]. |
| Γ121 Horocycle rate = zero-free region | Solved (Zagier) | RH (rate `¾`); ≥qRH (interior) | Horocycle mean of a pseudo-Eisenstein series = totient-weighted Farey count of order `C=y^{−½}`; unconditional rate `y^{½−ε}`; rate `y^α` ⇒ `Re ρ≤2−2α`; rate `y^{½+δ−ε}` for every profile ⇔ zero-free `Re ρ≤1−2δ`; RH ⇔ `y^{¾−ε}` [L]. Zero-free half-plane ⇔ polynomial lower bound for ζ on its vertical strips [L]. |
| Γ122 Lax–Phillips decay on the modular surface | Solved (identity) | RH | Resonances `u=(ρ−1)/2`; truncated resonant states are eigenvectors of the compressed dilation semigroup, which contracts and exhausts; pulse decay rate `δ` ⇔ zero-free `Re ρ≤1−2δ` ⇔ horocycle rate `y^{½+δ}`; RH ⇔ every resonant mode decays at `e^{−t/4}` [L]. |
| Γ123 Recurrence dichotomy of the tail | Solved | sub | Nonvanishing targets approached at positive lower density; targets with an interior zero only at tail-bad heights [L]. |
| Γ124 One-offs stop at the critical line | Classified | method | Discrete one-offs blow up at `s=½`; displacement of primes or integers forces a positive FE defect; defect `≤1/6400` forces the rational primes; continuous one-offs carry no FE [L/D]. |
| Γ125 Count law of every hyperelliptic curve | Solved | every genus | `y²=f(x)`, `f` squarefree, odd characteristic, any degree: RH and Hasse–Weil over every extension (even degree: one trivial reciprocal root `χ(lc f)` plus `deg f−2` roots of modulus `√q`); the channel numbers `g`, `g\|E\|`, `N_E+(g−1)(\|E\|+1)` extend to a count law over every finite extension; tower count law ⇔ a crude bound `\|N_n−qⁿ−1\|≤Cq^{n/2}` at every level, for any `C` (power-sum elimination plus FE) [L]. |
| Γ126 Born rule | Classified | — | Born rule `MᵀSM=qS` for the delay `M`: nondegenerate ⇒ partner law `α↦q/α` (the FE) and `(det M)²=q^d`; positive ⇒ every mode on `\|α\|²=q`; genus one: unique covariant count law `K(1)𝒬`, existing iff damped; banks: Born rules `Σc_k𝒬_{t_k}`, positive iff every oscillator damped; four off-circle modes carry a hyperbolic split form; throats with edge index `≠2` have none [L]. |
| Γ127 Boundary algebra of a black hole | Classified | — | Probe algebra `R[π]/(π²−tπ+q)` with partner involution `π*=q/π`: GNS form of every state is the Krein square; a positive state exists iff damped iff a `*`-representation on `ℂ` exists; with the Hilbert involution the algebra is `C*` on every black hole, fakes included [L]. |
| Γ128 Linear counts | No-go | — | An additive count with the parallelogram law vanishes; a count through one linear functional has discriminant 0; the Krein square factors through one linear count iff `t²=4q`. Shell, Farey and echo counts are linear in the source [L]. Survivor: a quadratic count of full rank, a sum of at least as many squares of linear counts as oscillating modes. |
| Γ129 Hecke supplies conservation | No-go (Hecke as law) | — | Every Hecke instance `K(1+πⁿ)+K(1−πⁿ)=2K(1)+2K(πⁿ)` holds on every black hole; a three-cusp overdamped fake (`q≥9`) has positive counts, conservation at every level and a delay-covariant count, and violates the law at `2−π` [L]. |
| Γ130 Second place of a Hecke triangle group | Classified | — | A place counts nonnegatively iff damped; non-arithmetic `G_q`, `q∉{3,4,6}`, has a real place where an explicit probe counts negatively (`G₅`: `T⁴S` gives `4−2√5`); arithmetic `G₃,G₄,G₆` have no second place [L; Takeuchi C]. |
| Γ131 Tate limit of a count over ℤ | Sharpened | RH | `Q(a)=Σa_ma_nC(log(m/n))`, a multiplicative Toeplitz form; any nonnegative `K` with `K(ma)/m²→Q(a)` forces `Q≥0`; RH ⇔ `Q` is the Tate limit of an `ℕ`-valued count (no parallelogram law needed); under RH `⌊Q⌋` is at distance `<1` and obeys the law up to 6; Hecke at `p` is an exact isometry of `Q` [L]. The content is a count defined without `Q`. |
| Γ132 Narain AdS₃ source | Sharpened | RH (rate `¾`) | Literal Narain partition: modular invariance, Mellin `2π^{−s}Γ(s)ζ(2s)E_s(ρ)E_s(σ)`, continuation `2N(u,ρ)N(u,σ)/[u(1+2u)ξ(1+2u)]`, every arithmetic pole on prescribed horocycles; double target average: exact main terms, Schwartz boundary, `∫H=0`; remainder `≤Cy^{½}exp(−L·vkWidth(L)/128)` with a target-independent exponent; global exponential majorant of the Mellin boundary; the source clock extends holomorphically to a fixed complex strip; mirror symmetry and independent modularity in all three moduli [L]; `O(y^{¾−ε})` ⇒ RH; every exponent `>¾` impossible (Hardy) [L]. |
| Γ133 Cusp channel of the horizon | Solved (classical theory) | — | Mirror-odd smooth cusp data exist; infinitely many Maass cusp forms for `SL₂(ℤ)`; discrete spectrum; `N(Λ)≍Λ`; heat trace finite; joint Laplace–Hecke eigenspaces of dimension `≤2`; Rankin–Selberg `Λ_g` holomorphic on `ℂ∖{0,½,1}` with `Λ_g(1−s)=Λ_g(s)`, `P_g=s(s−½)(s−1)Λ_g` entire and `≪(1+\|t\|)^Ne^{−π\|t\|}`; mean square `(1/N)Σ_{\|n\|<N}\|ρ(n)\|²→(24/π²)cosh(πt)‖g‖²`; `φ_g` polynomially bounded on `a≤Re s≤5/4`; log-Gaussian smoothed sums `Σf(m)φ_Δ(m/X)=Ae^{Δ²}Xe^{−1/X}+O(Δ^{−N−1}X^{3/4})` [L]. |
| Γ134 Cusp-energy horocycle rate | Sharpened | RH (with noncancellation) | `\|m_g(y)−(3/π)‖g‖²\|≤Cy^{½−ε}` unconditionally, `≤Cy^{¾−ε}` under RH, `y^{1−θ/2−ε}` from a zero-free `Re s>θ`; rate `y^α` ⇒ `Λ_g(ρ/2)=0` at every zero with `Re ρ>2−2α` [L]. A receiver needs an independent `¾` rate and `Λ_g(ρ/2)≠0` (B109). |
| Γ135 Relocation is seen at the first integer gap | Classified | — | Two actual critical pairs relocated to `¼,¾` with the rational multiplier normalized at `0` and `1`: Mellin density signed (positive at integers, negative at midpoints eventually), integrable, total mass zero, negative inverse moment; endpoint normalization forces a nonpositive quadratic trace, zero iff the target is critical; for every finite integer-dilation filter the filtered density is negative on `(1,1+ε)` [L]. Rational surgery on ζ's own zeros cannot preserve positivity of the density. |
| Γ136 AAL is eventual-to-global | Classified | sub | AAL ⇔ for every `σ`, a right bound `Re ≤σ` on zeros beyond some height implies it for all zeros; zeros of `F(s+a)F(s−a)` are translates; symmetric shifts preserve AAL [L]. At the single abscissa `σ=½` the law reads "eventual RH ⇒ RH", which is "finite off-line support ⇒ none" (Σ4, B13) [L/D]. An AAL proof cannot use the location `½` beyond the FE involution and Hardy's zeros. |
| Γ137 Positive Hecke annihilators | No-go (positivity as zero exclusion) | — | Any finite set of nontrivial zeros is annihilated, with prescribed multiplicities, by a polynomial with nonnegative coefficients in the normalized `T₂,T₃` and constant 1; such a polynomial dominates its tests and has constant-mode value `>2` [L]. |
| Γ138 Prime pairs retain the prime-power field | Solved (identity) | — | `P=−ζ′/ζ−H`; diagonal of `P²` analytic on `Re s>½`; at a zero of multiplicity `m` the simple Laurent coefficient of the distinct-pair source is that of `(ζ′/ζ)²` plus `2mH(ρ)` [L]. |
| Γ139 Principal series at the boundary | Classified | — | Continuous periodic data have injective inversion defect with closed range (no continuous modular fixed vector); the conformal principal series at weight `½+iε` has no highest or lowest weight vector [L]. |

## Scoped no-gos and surviving replacements

| Boundary | Exact scope and survivor |
|---|---|
| KR-TOR / KR-UCF / KR-R1 | Retired labels, not proved kills. BAG transfer closed (Γ1); PA Hermite-contour receiver (Σ73); TG Gaussian-passage receiver (Σ80). |
| KR-FPR | Finite and cofinal finite Hermitian KMS corrections cannot realize universal incidence passively [L]. |
| KR-SRP | Odd-only pole weight `β>1` impossible; even-only `β>1` not settled [L]. |
| KR-GAP | Excludes `E=QG₀(·+ih)`, `G₀` lower-Pólya; not arbitrary HB realizations [L]. |
| KR-R2 | Anchored 2-periodic loops realize every odd winding; not identified with renewal feedback [L]. |
| KR-R3 | Eventual upper bounds at every height ⇔ RH [L]. |
| Left-crossing slow returns | Discs reaching `Re s≤½` force `\|ζ\|≥cτ^b`; right-edge discs carry the AAL receiver (Γ107) [L]. |
| Literal fixed-point localization | Fixed points of maps homotopic to the identity number `≥N/(4log N)`; the core's Euler characteristic is `M(N)+#primes(N/2,N]`. Signed Lefschetz sums and core-relative invariants are outside the obstruction (Π107) [L]. |
| Persistence of the prime complex | Classified and `s`-independent; any cancellation must come from structure not present in the homotopy type or the persistence module (Π106) [L]. |
| Narain remainder past `¾` | Excluded at every target pair; the `¾` rate itself is RH (Γ132) [L]. |
| Linear horizon counts | Shell and Farey counts obey rate laws (Π105, Γ121) but never the count law (Γ128) [L]. |
| Hecke at a second place | Conservation only (Γ129); counts fail at the second place exactly for non-arithmetic triangle groups (Γ130) [L]. |
| Positive Hecke / two-prime annihilators | Kill any finite zero set; no Euler-product or FE conclusion; accuracy on the right forces growth on the left (Γ137, Π102) [L]. |
| Rational zero relocation | Detected by first-gap negativity of the density under every finite Dirichlet filter (Γ135); Beurling one-offs are not rational relocations of ζ [L]. |
| Low packet at a fixed ratio | Payment at one ratio is a window rung; at every ratio it is RH (Σ130) [L]. |
| Theta fixed heads and compact cores | Fixed heads, summable absolute majorants and compact cores fail; the adaptive head survives with leading term a critical partial-sum square (Σ98, Σ133) [L]. |
| Sharp horizon sources | `¾` for sharp shells needs Möbius × circle-problem cancellation beyond RH (Π109) [L]. |
| Torsion forms on unweighted `ℓ²` | Mixed prime row unbounded; every `δ>0` restores convergence; the limit is indefinite on prime pairs `{p,2p}` (Π108) [L]. |
| Extremal-angle contradiction | Polynomial model satisfies every order of the extremal law (Γ120) [L]. |
| Bounded count as selector | Bounded count error admits a new zero with signed generators (Π100); positive generators with count error `o(log n)` force ζ (Π99) [L]. |
| Positive Euler product + linear counting as AAL | Integer norms and rational-prime labels both carry a finite top layer (Π102); none continues to the critical line (Γ124) [L]. |

## Bridges

| Bridge | Anchor |
|---|---|
| Window index counts distinct right zeros; `sup_dN_d` counts off-line multiplicity; bounded `N_d` gives finite support only | AHD, CWS, FFP [L] |
| RH ⇔ `a*(ζ)=⊤` ⇔ `1∈ℋ(c)` ∀c ⇔ `λ*(c)→0` ⇔ no finite contact ⇔ `Ψ` locally bounded | WVL, FADF, CHT, CSTW, AIF [L] |
| Critical curve = window: `R_c≤R_polar≤R_high=⨅windowThreshold`; only the pole channel is unpaid at a fixed ratio (whole-space collar Gårding loses only `b₁²`); the pole at every ratio is RH | AHD, CACT [L] |
| Aperture ⇄ ratio exchange below the onset: depth-¼ exclusion to `e^{a/K}`, sharp pole self-energy, Mertens lag, `R_polar≥c₁e^{c₂a}` | AHD [L] |
| Window sign ⇔ two-site signs ⇔ reflection band ⇔ Stieltjes jets ⇔ two-bump family | GWZ, SWC, SRT [L] |
| Window positivity ⇒ local density, support density and PNT with exponent `5/6` on the window's range | CHT [L] |
| Below `log 4`: sign ⇔ two-weight band ⇔ Hodge index ⇔ Künneth effectivity; `{2,3,4}` band below `log 5`; Tate dimension one through `log 5` | SWC, LST, AHD, FADF, WTZ [L] |
| Theta adaptive head ↔ critical-line partial sums of ζ of length half the height | CAF, TCS [L]; [C/D] |
| Completed coefficient-space energy `=2Re[WH,WH]`; `D_s` negative weighted Hecke integral | RIT, ACP [L] |
| Isolated clusters ⇒ camera readout; positivity at `λ·½log T` ⇒ depth `<e^{−c log³T}` | ZCG [L] |
| RH ⇔ infinitely many unshifted Jensen degrees real ⇔ all positive-time heat zeros simple | FFP, RHTower, ZCG [L] |
| Hodge index = Metzler sign of the Cayley ladder = Li positivity | ALG [L] |
| Abel log-mean ⇔ `I` at infinity ⇔ depth density `o(T)` ⇔ density-zero damping deficits | AIF, ASH [L] |
| ¬AAL ⇔ finite oscillation of `ψ(x)−x` ⇔ two-prime dilation annihilation; AAL ⇔ eventual-to-global abscissa bounds; shift-invariant | ZCG, RHTower [L] |
| Zeros = power-law kernel of the cut system; finite-energy kernel mass decides RH | RAC [L] |
| Λ = intersection number of torsion cycles; renormalized torsion forms converge on `ℓ²(n^δ)`, `δ>0` | AE, HHAC [L] |
| Power-saving Liouville bound = zero-free strip; exact floor identity pins `λ`; twin pairs carry a quarter floor | RAC, AAD, AGT [L] |
| Count law on every hyperelliptic curve from a crude bound at every level; Born rule = FE + damping; boundary algebra Krein; linear counts degenerate; Hecke gives conservation only | CTH, ASH [L] |
| RH ⇔ `Q` on integer probes is the Tate limit of a count; Hecke isometry of `Q` | CTH [L] |
| Horocycle rate ⇔ zero-free region ⇔ Farey count rate ⇔ pulse ringdown ⇔ Lax–Phillips decay; `¾` ⇔ RH; Farey ↔ Mertens ↔ nerve ↔ core Euler characteristic | BHR, CTH, RHTower, HWV, HHAC [L] |
| Narain AdS₃ remainder = VK saving; `¾` ⇒ RH | ASH ModularBootstrap [L] |
| Cusp energy rate reads `Λ_g(ρ/2)` | BHR [L] |
| Zeros of ζ = zeros of every Euler tail; returns at zeros tail-bad; recurrence dichotomy | TAPO [L] |
| Proportional saving ⇔ no early heavy return; first return bracketed at every precision | TAPO, PTT [L] |
| Conditional tail laws end at the Kronecker scale; arithmetic mean values pay off-diagonals by collision counts; necessary mollifier length = Euler mollifier over primes `≤c log²T` | APR, PTT, TAPO, SPAL [L/D] |
| ζ isolated in FE defect, count distance and exact parity identity; every one-off fails at the critical line; rational relocation fails positivity at the first gap; positivity annihilates every finite zero set | APD, SPAL, RAC, ACP [L/D] |
| Stepanov over ℤ = integrality + Nair ceiling (Chebyshev); Frobenius over `𝔽_q[T]` = factorial stencil of rate 0, over ℤ rate = Mertens level | AE, AAD [L] |
| Primon thermal means = Euler factors at `2e^β+1` | SEL/Primon [L] |

## Strength of the open walls

- **RH:** Σ1, Σ1u, Σ1v (all ratios), Σ2, Σ3a, Σ6 (all ranks), Σ7, Σ8, Σ17, Σ18, Σ19, Σ20, Σ28 (subexponential), Σ30, Σ32, Σ49, Σ56, Σ61, Σ66, Σ67 (all `d`), Σ70 (sign), Σ72 (all orders), Σ73, Σ74, Σ76–80, Σ85, Σ93, Σ101, Σ113, Σ114, Σ122, Σ129, Σ130, Σ133, Π2, Π4, Π11h, Π17, Π23, Π28 (trivial point), Π30, Π36, Π42, Π47–50, Π58, Π59, Π62, Π63, Π66, Π68, Π69, Π78, Π81 (finite energy), Π105, Π108 (sign), Γ1, Γ4, Γ5, Γ8, Γ16, Γ19, Γ24, Γ46, Γ52–54, Γ61, Γ62, Γ76, Γ78, Γ86, Γ90, Γ91, Γ95, Γ97, Γ110, Γ113, Γ114, Γ121 (rate `¾`), Γ122, Γ131, Γ132 (rate `¾`), Γ134 (with B109).
- **≥qRH:** Σ4 (`K_ζ`), Σ28 (exponent `<½`), Π5, Π17 (log stage), Π23 (fixed degree), Π42 (dyadic), Π70 (polynomial rate), Π84 (power saving), Γ121/Γ122/Γ132 (interior exponents), `N_d` bounded, ZAL, inner-field decay.
- **sub:** Σ82, Σ1d, Σ1e, Σ1g, Σ1j, Σ1m, Σ1q, Σ1w, Σ6 (each rank), Σ30 (each stage), Σ47, Σ50, Σ70 (rate), Σ72 (band), Σ86, Σ92, Σ94, Σ99, Σ100, Σ116, Σ117, Σ118, Σ131, Π7, Π9, Π11f, Π12, Π22, Π40, Π51–54, Π57, Π65, Π80, Π87, Π90, Π94, Π96, Π103, Γ15, Γ47, Γ57, Γ65, Γ68, Γ69, Γ71, Γ74, Γ104, Γ106, Γ123, Γ136.
- **indep. / method / beyond RH:** Π16, Π97, Π101, Π109 (beyond RH), Γ49, Γ56, Γ124, Σ127.
