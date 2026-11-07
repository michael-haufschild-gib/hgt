# Walls ledger — status quo

**Corpus checkpoint:** commit `1500534c93` plus the working tree of 2026-11-07.

Three wall families carry the frontier. **Σ** is the critical sign of the window form, **Π** the precision and production of the prime count, **Γ** the selection of ζ and reflection of its zeros. RH ⇔ `κ=0` ⇔ `a*(ζ)=⊤` ⇔ `λ*(c)→0` ⇔ `N_d=0` for infinitely many `d` ⇔ ZAL ∧ AAL [L]. These receivers do not supply their arithmetic inputs.

[Frontier](../rh-current-frontier-map.md): **38 live formulations, 9 candidates** (APF, EGC, EWJ, FEL, IRK, MSC, RFHM, W1C, WBF). HJ→PA and BSH→CDC are aliases. [Scoped obstructions](../rh-killed-routes.md) separate failed mechanisms from open replacements.

- **Σ is the sign of every window.** RH ⇔ some weight is admissible on every window, ⇔ `Ψ=½log H₁` is locally bounded, ⇔ `Ω_ψ(a,X)≥0` on the whole plane [L/D]. At a fixed critical ratio a nonpositive direction of the complete matrix must meet the top logarithmic window of length `(1/8)log R+O(1)`; everything below it is positive by rescaling to the unconditional critical multiple (Σ126) [S]. The split must be by conductor first: physical tearing fails at Schur ratio `4/13` (Σ127) [S]. Every certificate past the abscissa is a tail-good condition (Σ128). Parabolic structure cannot select `t=0`; the theta amplitude is not all-base torus-positive; Gårding fails on deep atoms [L].
- **Π is the same sign on the prime side.** One smoothed prime count matches the pole square within `W(f)` [L]. All unconditional savings sit at the VK curve, stencils included; under RH the stencil exponent lies in `[¼,½]` (Π70). Zeros are the power-law kernel of the cut system, and the finite-energy kernel decides RH (Π81). The dark range runs from the Kronecker scale `≈log T`, where conditional tail laws stop (Π96), past `≈(log T)²`, where absolute non-alignment begins (Π87) and whose Euler length is the necessary length of a near-unit mollifier (Π41), to `exp((log T)^{2/3})` [L/D]. The first return of the prime orbit is bracketed at every precision and open at constant precision (Π94).
- **Γ is the same sign on the zero side.** RH splits as ZAL ∧ AAL [L]. Failure of AAL is one rigid finite oscillation of the prime error (Γ80, Γ81). A return at a right zero is tail-bad at every cut and has density zero (Γ115). ζ is isolated in three metrics: FE defect, count distance, exact parity identity (Γ84, Π99) [L]. Universal damping is not a law of wave dynamics, not even with the functional equation at genus two (Γ118); the separating law is the count (Γ96, Γ98). Over ℤ the form is quadratic and not known to be a count (Γ97, Γ113).

Status: **Solved** (the face is a theorem), **Partially solved**, **Sharpened** (open, with its exact form a theorem), **Open**, **No-go** (the mechanism is refuted), **Classified** (answered by a classification or identification), **Reduced** (theorem-level equivalent of the wall named), **Scoped** (a theorem whose stated hypothesis needs its scope read). Strength: **RH**, **≥qRH**, **sub**, **indep.**, **identity**, **method**. Evidence: `[L]` Lean source; `[K]` Lean with transitive axiom audit; `[S]` Lean source unfinished, unintegrated or uncommitted; `[P]` paper only; `[D]` deduction; `[N]` numerical; `[C]` classical, not formalized.

Notation. Windows `[−a,a]`; `c_ψ(t)=W(ψ(·−t),ψ)`; `w_n=Λ(n)n^{−1/2}`; `δ` sliver width `2c−log n` (in zero statements the depth `Re ρ−½`); `ρ³=ρ+1`; `a_k=weilFloorApertureTower k`, `181/500<a₀<181/500+5·10⁻⁷`; `λ*(c)` best margin; `N_d` non-real root count of `R_d(Ξ)`; `E` exceptional values of ζ; `r` anchor reflection, `L=artanh r`; `Ψ=½log H₁`, `q=Ψ′`; `ϱ` pseudo-hyperbolic ratio; `L=log T` in near-line statements, `L=log|t|`, `ℓ=log L` in orbit statements; `I(w)` inner field; `G` Green kernel of `Re s>½`; `R=c⁸/log N`; `W₈(H)=∫H²e^{−8y}`; `D_N(y)=Σ_{n≤N}Λ(n)n^{−½}cos(y log n)`; `Q₁=⌊(log N)^{13/32}⌋`; `R(y,η)` first return of the primes `≤y` at precision `η`; `E_y` Euler head, `ζM_y` Euler tail.

## Σ — critical sign

| Wall | Status | Strength | Content |
|---|---|---|---|
| Σ1 Weil's sign | Sharpened | RH | RH ⇔ `Q≥0` on every window ⇔ `a*(ζ)=⊤` ⇔ two-site PD ⇔ band at the centre in both sectors ⇔ Stieltjes jet moments ⇔ lattice Schur parameters in `(−1,1)` ⇔ `windowThreshold≡⊤` ⇔ `1∈ℋ(c)` ∀c ⇔ `λ*(c)→0` ⇔ every window cone nonempty ⇔ every growth step a translation contraction ⇔ Cayley ladders NSD ⇔ Suzuki first variation `≥0` ⇔ mollified Jensen stability ⇔ Krein positivity ⇔ prime-blind positivity ⇔ odd BPY Poincaré inequality ⇔ no finite contact ⇔ outer predictor at every window ⇔ every echo in its Schur band ⇔ every orbit correlation relatively compact ⇔ `Ω_ψ(a,X)≥0` [L] ⇔ `Ψ` locally bounded [D]. |
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
| Σ1l Window threshold | Reduced (to Σ56) | RH | `windowThreshold A=⊤ ⇔ A/2≤a*(ζ)`; `=⊤` for `A≤2a_k`; every critical pencil positive there [L]. |
| Σ1m Polarization inheritance | Partially solved | sub | Twisted sectors with positive scalar second order; short windows; cosh hyperplane [L]. |
| Σ1n Bulk below the grid | Classified | — | Reads only the pole [L]. |
| Σ1o Aperture-independent weighted floor | Solved (size-only) | — | `Q(H)≥−F(p)∫e^{−pu}H²`, `p>1`, explicit `F(p)` [L]. |
| Σ1p Terminal windows | Classified | — | Polar source with nontrivial kernel; long-index cancellation on near rows [L]. |
| Σ1q Receiving charges | Classified | — | Capacity `log log N+O(1)`; receiving vectors with vanishing physical energy read at `1/80`; gcd-twisted charges split into four channels, mixed error `→0` on `2α<β`, `β+2α<½`; periodic `F`: `J_N=O(log N)` iff gcd profile [L/K]. |
| Σ1r Conductor packets and correctors | Classified | — | Terminal sources concentrate at the pole; correctors cannot improve zero-source windows [L]. |
| Σ1s Far reserve | Partially solved | sub | `farMargin R=3D/(8R)−C−C′R`; coercive on conductors `>N^θ` for `0<R<R*`; joint complement of the low packet coercive for `0<R≤min(1,5R*/6)`, `c≥(log N)^{1/16}` [L]. Above `R*`: Gårding with an `L²` defect on `(V_{Q₁})ᗮ` at every ratio (Σ116) [S]; sign is Σ126. |
| Σ1t Prefix Schur cost | Partially solved | — | `(tail z)ᵀ(D−BᵀA⁻¹B)(tail z)=zᵀWz−rᵀA⁻¹r`, `A⁻¹≤20`; floor `(a/2)e^{−Bc}‖z‖²` on conductor blocks `≤(log N)^{1/32}` [L]. |
| Σ2 Edge, zero modes, hard Lefschetz | Sharpened | RH | RH ⇔ HL on the PSD locus; zero modes radical and two-site; Hodge index = Metzler sign of the Cayley ladder = Li positivity [L]. |
| Σ2a Interior-gap continuation | No-go | — | `κ(d)=1_{3∣d}` [L]. |
| Σ2b Edge singularity | Classified | — | No smooth eigenfunction, constrained ground state or capacity maximizer [L]. |
| Σ3 Stars and dilation monodromy | Partially solved | — / RH | Stars isometric; squarefree prime complex ≃ wedge of spheres over odd squarefree `N/2<m≤N` [L]. |
| Σ3a Coprime stratum | Sharpened | RH | Redheffer `det=M(N)` = reduced Euler characteristic up to sign [L]. |
| Σ4 Finite index / heat count | Sharpened | ≥qRH (`K_ζ`); RH (`K_ζ⊠K_ζ`) | `κ<∞` ⇒ Lindelöf; RH ⇔ index `0`; window index counts critical lengths; `N_d` bounded ⇔ `κ<∞`; under AAL finite index ⇔ RH [L]. |
| Σ5 Collision quantum / window integer | Reduced (to Π17) | RH | Index `0` ⇔ Wiener–Hopf invertibility [L]. |
| Σ6 Rank / degree uniformity | Partially solved | RH | TH ranks `≤10` PD for `0<a≤½`; rank `N` on the VK collar; rank `N` from verified height `41+6(N+2)log(N+2)` (`a≤½`), `D(N+1)³+1` (`a≤¾`); first-atom tails PD at every rank; `θ₁+θ₂` and every chain `q^n` PD at every rank [L]. Rank `≥11` of the full source and the cross-chain aggregate open. |
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
| Σ28 Window negativity budget | Sharpened | ≥qRH (exp `<½`); RH (subexp.) | Ground-energy floor `−Ce^{2σA}` ⇔ zero width `≤σ` [L]. |
| Σ29 Low-frequency localization | Solved | — | Negativity only at the poles and below `τ₀(a)` [L]. |
| Σ30 The stage step | Reduced | RH (induction); each stage sub | Composite stages carry no fold; single-prime transport for all `A` ⇔ RH; transport across `p=2` unconditional [L]. |
| Σ31 Positivity across dimension zero | Classified | = Σ1 | Bare domination ⇔ `Q≥0` [L/D]. |
| Σ32 Prime-blind positivity / calibration | Sharpened | RH | Full positive cone `{Λ}` under RH, empty otherwise; one Euler factor suffices; blind energy `(1/π)∫\|𝓜f\|²(θ′+1−Re ζ(½+it))`; Carlson threshold `e^{(π/2)\|t\|}` [L]. |
| Σ33 Tate positivity horizon | Classified | — | Positive Tate dimensions `[0,κ(A)]`, `κ(A)→0`; finite templates iff spread `<27/5`; dimension one through `log(9/2)` [L]. |
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
| Σ56 Onset aperture of `ζ` | Sharpened | RH | RH ⇔ `a*(ζ)=⊤`; off RH contact is attained; ground energy crosses zero at most once [L]. |
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
| Σ71 Datum of the window cone | Classified | — | Critical log-conductor `=−λ*(c)` [L]. |
| Σ72 Centre jets and the slice band | Partially solved | RH (all orders); sub (band) | Taylor coefficients PF₂₀₀; slice coefficients `≥0` for `\|t\|≤133/2`; off-line zeros have `\|Im\|>67` [L]. |
| Σ73 Hausdorff rows | Sharpened | RH | Rows nonnegative for `r≥C₀(k+1)²`; remaining entries ⇔ RH; HJ exterior diagonal at `218/25` [L]. |
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
| Σ87 Compactness at a critical ratio | Partially solved | sub (one ratio) | Γ-liminf with weight `α_R` at every `R`; bounded form gives strong `L²` limits; physical and Fourier tails give precompactness [L]. `W₈` bounded on collar-supported negative sequences, unbounded on deep atoms (Σ116). Assembly A10 open. |
| Σ88 Limit pencil at a fixed ratio | Classified | sub | `κQ+(7J/R)∫e^{−8y}H²≥0` on smooth families follows from a window of half-width `O(log R)` [D]; Σ126 places nonpositive directions on a top window of length `(1/8)log R+O(1)` [S]. |
| Σ89 Parabolic blindness | No-go | — | `Φe^{−τx²}` has the same parabolic laws and non-real zeros for `t<τ` [L]. |
| Σ90 Central inequality | Classified | stronger than RH | `g_t²≥c·min(t,log⁻²X)` everywhere ⇒ RH and `c(m+1)≤24` [L]. |
| Σ91 Gap dynamics | Solved (laws) | identity | Gap law, mesh bounds, profile gap `16/k≤μ²≤24/(k+1)`, maximum principle; all assume reality in the cylinder [L]. |
| Σ92 Crystal on typical heights | Partially solved | sub | `Λ_X log X→0` on density one; exceptional measure `≤T^{θ(κ)}`, `θ(κ)=1−κ³/41943040000`; crystal law outside `δT` [L]. |
| Σ93 Collision frequency | Sharpened | RH | `N(σ)<1` excludes a double zero; multiplicity `≤(3300/9991+ε)log X` [L]. |
| Σ94 Depth law | Partially solved | sub | Isolated simple zero: `d−7η≤Λ_Xlog(X/2π)≤d+17η` [L]; crowded and multiple zeros open. |
| Σ95 Pointwise two-prime payment | No-go | — | Negative at centre `log 6` [L]. |
| Σ96 Euler-operator theta spectrum | Solved (identity) | identity | `S=Π_pT_pA`, `T_p=(1−2cos(b log p)σ_p+σ_p²)^{−1}`; `A` not a positive Laplace mixture [L]. |
| Σ97 Torus-uniform theta positivity | No-go (numerical) | — | Negative once primes `≤19`–`47` are free [N]. |
| Σ98 Finite theta heads | No-go | — | No fixed head pays its uniform remainder at every rank [L]. |
| Σ99 Local onset field | Partially solved | sub | `Ω_ψ(a,X)` sum over zeros; pair cost `≤(16/9)δ²a⁴‖ψ‖²`; RH ⇔ `Ω≥0` [L]. |
| Σ100 Runs on the critical line | Partially solved | sub | `≥N(T)/5000` starts of five consecutive simple critical zeros [L]. |
| Σ101 Causal certificate | Solved (identity) | RH (all windows) | PD ⇔ positive-margin outer predictor; RH ⇔ outer predictors on every window [L]. |
| Σ102 Szegő threshold | Classified | RH (position) | `s>0` square-summable reflectors, `s<0` negative witness, RH at `s=0` with `Σγ²=∞` [L]. |
| Σ103 Reflection coordinates | Classified | — | Reflection data free; passive iff each echo in its band; forward map causal injective [L]. |
| Σ104 A priori estimates free of `1/μ` | Solved (model) | sub | Born model `1−r_n²≥e^{−10A}/(2√n log n)` [L]. |
| Σ105 Soft prime kick | Solved | identity | `(Ψ(x)−Ψ(a))log(1/(x−a))→Λ(n)/√n` at `2a=log n` [L]. |
| Σ106 Green corner | Solved | identity | Kato contraction; `q_y→q` in `L¹` on compact precontact intervals [L]. |
| Σ107 Far-translate decoupling | No-go | — | `c_φ(t)↛0` for every nonzero test [L]. |
| Σ108 Insertion cone | Classified | — | Below left growth `½` Hecke cone = torus cone = exponential convexity; `½` exact threshold of the `L²` prime-pair cone; all-base torus-positive amplitudes with `κ<min(1,κ₀)` vanish; oscillatory and signed-Laplace dichotomies at `α=1`; torus cones closed under `e^{−βy}` [L]. |
| Σ109 Fixed-amplitude locking | No-go | — | Locked positivity ⇔ torus positivity for fixed amplitudes; only amplitudes oscillating with the height escape [L]. Convergence is essential: amplitudes bounded away from zero give nonsummable torus series [L]. |
| Σ110 Columns add | Classified | — | Infimum of signed columns = sum of minima; base pays by size when `Σlog p/(p^{½+a}−1)<½log(b/2π)` [L]. |
| Σ111 Curve flow | Solved (calibration) | — | Unitary ⇔ first `R` margins positive [L]. |
| Σ112 Theta current | Solved (explicit) | identity | `current=2\|Ξ\|²Re ξ′/ξ`; explicit core and tail [L]. |
| Σ113 Restoring bound of the actual chain | Solved (identity); control open | RH | `\|L(x)\|≤artanh e^{−2(x−c)}+2osc_{[c,x]}Ψ` [L]; RH ⇔ `Ψ` locally bounded [D]. |
| Σ114 Bohr profile decomposition | Classified | RH (for ζ) | RH ⇔ every orbit correlation relatively compact [L]. |
| Σ115 Critical Γ-liminf | Solved | identity | `liminf Q(U_N)≥Q_T(F)+α_R∫_{y<0}F²e^{−8y}` [L]. |
| Σ116 Weighted Gårding | No-go (full horizon); Solved (top collar); Partially solved (complement) | sub | Fails on `(V₁)ᗮ` for every `B` (deep difference `z_N`, `W₈≍N⁸`) [L]. Top collar: `Q+B_R‖U_y‖²≥κ_R·seventhMass+a_RW₈` at every `R` [L]. Window-localized: nonpositive collars keep `≥½` their `L²` mass in `(−A_R,1]`, `A_R=O(log(R+1)+1)` [S]. All-ratio far Gårding on `(V₁)ᗮ` and complement Gårding on `(V_{Q₁})ᗮ`, retaining `(κ₀+2)‖z‖²`, prefix mass, seventh mass, `W₈` and Lévy energy at cost `cB_far∫U_w²` [S]. |
| Σ117 Typical-height sign | Partially solved | sub | At `A=δlog T/(64M²)`, outside one set of measure `δT`, every shaped test has `Q_γ>0` [L]. |
| Σ118 All-height sign | Open | sub | Size reaches `a≈log log X−log 4` [D]; past it Π80, Π87. |
| Σ119 Tangent of the forward map | Solved | identity | `∂E_n/∂λ(n₀)=−(2/√n₀)A_n(log n₀)`; margins concave [L]. |
| Σ120 Certified passivity | Solved (certified windows) | sub | Full causal chain on total length `≤2a₀` [L]. |
| Σ121 Bounded extremals for every weight | Solved | identity | Attained bounded ground state, exact edge law, explicit sup bound [L]. |
| Σ122 Prefix–collar coupling at a critical ratio | Partially solved | sub | Every vector vanishing on the top window `Ioc(N/S_R,N)` has the floor `(κ₀/(2c⁷))‖x‖²` (Σ126) [S]. Physical tearing on `(V_{Q₁})ᗮ` fails (Σ127) [S]. Conductor-adapted far splitting decouples (Σ127) [S]. Open: low packet against the top window. |
| Σ123 Kernel-valued prime payment | No-go (returning coordinates) | — | `\|S\|≤\|G\|` for decompositions in returning prime coordinates [L]. Euler coordinates `z_p` cannot cross `Re s=1` (Σ128) [L]. |
| Σ124 Critical coupling of the base | Classified | — | `thetaAmp(x)e^{x/2}→½` [L]. |
| Σ125 Certificates on the orbit | Classified | — | Pointwise coefficients tautological; frozen ones cost size; for `σ>1` the Ξ-current lifts to `𝒥_σ(t,ω)=2\|ξ\|²(B−Σ_nΛ(n)n^{−σ}Re ω(n))` whose worst fibre point is the pole: a frozen certificate exists exactly when `−ζ′/ζ(σ)≤B(σ+it)` [L]. |
| Σ126 Top logarithmic window | Solved (non-escape) | sub | `∃C₀ ∀R ∃S_R`, `log S_R≤(1/8)log(R+1)+C₀`, eventually: every `x` vanishing on `Ioc(N/S_R,N)` has `completeWeilEnergy≥(κ₀/(2c⁷))‖x‖²` at every `c⁸≤R log N`; every nonpositive direction meets the top window. Mechanism: rescale to horizon `N/S_R`, where the overlap falls below the unconditional multiple `2K₁(log M)^{1/8}` [S]. |
| Σ127 Splitting order at a critical ratio | Classified | method | Prime quasimode `v_q−proj_{V_{Q₁}}v_q`, `q∈(Q₁,2Q₁]`, split across the collar boundary: Schur ratio `→4/13` at every `R` and every `B_R`. Keeping conductors `≤N^θ`, `θ=(1+log log N)^{−5}`, whole: `o(1)` Schur decoupling across the boundary [S: stated in source, proofs unfinished]. |
| Σ128 Certificates past the abscissa | Classified | — | On `Re s>½`, `Σ_p\|1−E_p(s)\|<∞` ⇔ `Re s>1`; no summable perturbation crosses. Head–tail certificate: every finite factorization is a rank-one decomposition; the tail coordinate is Schur exactly where `\|S\|≤\|head\|` [L]. Certificates past the abscissa are the tail-good property. |

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
| Π51 Vinogradov–Korobov barrier | Open | sub | Every unconditional saving sits at VK [L]. Short-sum form Π80. |
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
| Π65 Log-mean of ζ | Reduced | sub | Eight equivalent forms; Abel form ⇔ depth density `o(T)` [L]. Empty mollifier gives `O(T log log T)` [L]; Selberg `O(T)` [C]. Open. |
| Π66 Integrality over ℤ | Solved (exact) | RH at `√` scale | Nair lattice exact; Siegel half ⇔ lower count, Liouville half ⇔ upper count [L]. |
| Π67 Stencil ceilings | Classified | — | Floor `A(K)−1≥c/(√K(1+log K))`; no rate `K^{−a}`, `a>½` [L]. |
| Π68 Möbius zero condensation | Classified | RH | Zeros of `M_X` accumulate on `Re s=Θ` [L]. |
| Π69 Integer lag | Sharpened | RH | RH ⇔ lag `≤(2+γ−log 4π)√n`; `Ω±(√n)` [L]. |
| Π70 Rate of a stencil | Solved (exponent scale) | sub / qRH | Rate `K^{−a}` ⇒ `Re ρ≤1−a`; all `a<½` ⇒ RH; none past `½`; VK rates `exp(−(log K)^α)`, `α<3/5`; polynomial rate ⇔ strip. `\|M(n)\|≤Cn^{1−σ}` gives every `a<2σ/(3+2σ)`; a strip at `Θ` gives `a<2(1−Θ)/(5−2Θ)`; RH gives `a<¼`. Under RH the exponent lies in `[¼,½]` [L]. |
| Π71 Laws of a producer | Solved | — | `c=μ∗h`; producer = mollifier on `Re s=1`; peak law; uncertainty [L]. Compensated stencils: all letters `(2y+2)`-smooth, compensation cost `1/y`, alphabet `y³/Y` [L]. |
| Π72 Ledger blindness | No-go | — | Complete ledger of a zero mode vanishes for every balanced stencil [L]. |
| Π73 Parity ledger | Classified | — | Sieve and producer cones disjoint; parity-neutral producers reach every rate [L]. |
| Π74 Fake prime measures | Classified | — | Slope LP with strong duality; unique fake at infinite level; extremal level-`K` fake has `≤K` atoms, carried by the tight set of an optimal sawtooth [L/S]; level-`K` fakes lie within `≍1/log log K` of the pronic measure under a summable tail condition [L]. |
| Π75 Hecke action on producers | No-go (positive amplification) | — | [L]. |
| Π76 Frobenius as a stencil | Solved (calibration) | — | Over `𝔽_q[T]` the Carlitz stencil has rate 0 [L]. |
| Π77 Near-extremal rigidity | Solved | identity | Near-extremal families converge to `1/E` [L]. |
| Π78 Holomorphic Abel budgets | Open | RH | Over a curve Castelnuovo ⇔ budgets reach 1; boundary quotients nonselective [L/K]. |
| Π79 Arithmetic Carleson measure | Solved | identity | `μ(box)≤(5/2)xI`; `I→0` ⇔ depth density `o(T)` [L]. |
| Π80 Short-sum barrier | Open | sub | Depth `d` forces a large value of a prime polynomial of length `(log γ)^{O(1/d)}` [L]. Some height `≤T` has no cancellation below length `c log T`; off a set of measure `≪TY^{−2ε}` square-root cancellation holds at all dyadic lengths `Y..T/log T` at once [L]. Missing: the exceptional set past `log T` at all heights. |
| Π81 Kernel of the cut system | Classified | RH | Zeros = power-law kernel vectors; summable kernel vectors vanish; positivity reaches `Re s≥1` [L]. Absolutely convergent strip superpositions lie in the kernel iff each active point is a zero; a finite-energy kernel vector of mass `1` exists for every `Re s>½` zero, so finite-energy mass annihilation ⇒ RH [L]. |
| Π82 Ledger hierarchy | Solved | — | Degree `k` ledgers have order `m−k`; exact ledgers holomorphic off `s=1` [L]. |
| Π83 Twin at every degree | Solved | — | `T=A−2A(2s)` shares every leading pole of `A^k` at right zeros [L]. |
| Π84 Parity exponent | Solved | ≥qRH at power saving | `L(x)≪x^a` ∀`a>Θ` ⇔ zero-free `Re s>Θ`; the exact identity `Σ_{k≤x}F(⌊x/k⌋)=⌊√x⌋` forces `f=λ` [L]. Parity is a size statement, not missing information. |
| Π85 Exchange law | Solved | — | Exchange of exponent `<σ` keeps the zeros right of `σ`; a new zero needs exchange mass of exponent `≥β`; exchanges with `G(1)=1` have `N(x)=x+O(x^σ)` [L]. |
| Π86 Carry of the floor | Solved | — | A dilation of the count is an average of translations; every integer is a cut [L]. |
| Π87 Absolute non-alignment | Partially solved | sub | Low additive-energy squared words: `Σ_{p<N}(1−cos t log p)/√p≥8/(10⁹L⁶ℓ⁴)` and `‖Σ_{n<N}n^{it}‖≤N(1−1/(10⁷L⁶ℓ³))` at `N≥48L²ℓ` [L]; `≥t^{−δ}` at length `L^A`, `A>1` [L]. Required at the size curve `≈εL/ℓ` [D]. |
| Π88 Rounded orbit | No-go | — | Same diagonal moments, exact return at `T` [L]. |
| Π89 Discrepancy and mixing time | Classified | — | Every window of length `exp(10y√(log y·log log y/δ))` enters every `δ`-box on primes `≤y` [L]; some box of radius `ρ` is missed below `log T≈π(y)log(π/(4ρ))` [S]. So `½π(y)log(1/δ)≲log T_mix≲10y√(log y log log y/δ)`. |
| Π90 Energy past the diagonal | Partially solved | sub | Gap to truth = density of smooth numbers [L]. |
| Π91 Curve stencil | Solved (calibration) | — | Linear stencils stop at `\|a\|≤q+1` [L]. |
| Π92 Prime kernel as torsion energy | Solved (identity) | — | `Λ` = intersection number of torsion orbits; sign lost in `log(1/(1−r))Σx²` [L]. |
| Π93 Möbius as a cubic Gauss coefficient | Solved (identity); descent partial | past VK | Over `ℤ[ω]` ideal Möbius = cubic Gauss coefficient with fixed ray phase; cubic Eisenstein series with primitive rows and Kubota character, Fourier unfolding, Fredholm pencil, meromorphic resolvent at `4/3`, finite-dimensional residue [L]; constant term supported on cubes [S]. Residue nonvanishing and rational transfer open. |
| Π94 First return of the prime orbit | Partially solved | sub | `R(y,η)≤Q^{π(y)}` when `2π²≤ηQ²`; `R≥exp(c(log y)^{1−η})`; `R→∞` for `η<1`; a weak return is a spike `\|ζ(1+1/log N+it)\|≍log N` [L]. Precision law: savings exclude returns, so `R(y,η)>exp(√(y/(48log y)))` once `12η√y·y⁴<c` (RH bracket at precision `≍y^{−9/2}`) and `R(y,η)>exp(y^{1/A})` once `12η√y<exp(−δy^{1/A})` [L]. Constant precision open: `log R(y,η)` known in `[(log y)^{1−η}, Cy/log y]`. |
| Π95 Proportional saving = heavy first return | Classified | — | Defect `<cS` forces a return at precision `η` on a subset of weight `>(1−c/η)S`; a return missing weight `κ` has defect `≤ηS+2κ` [L]. B46 is the absence of early heavy returns. |
| Π96 Conditional tail law and the Kronecker scale | Partially solved | sub | Head `R` on `y`-smooth, tail `B` on `y`-rough integers: `∫_T^{2T}\|R\|²\|B\|²=T‖r‖²‖b‖²+O(N log N‖r‖²‖b‖²)`; conditional mean `O(N(Σ\|r\|)²Σ\|b\|)`; Gaussian conditional moments `k!‖b‖^{2k}` and large deviations while `log max A+k log Z≪log T` [L]. Past the Kronecker scale (head resonator as long as the height) nothing is known. |
| Π97 Moving jet of the logarithm | Partially solved | method | `Δ_h^j log x=Δ_1^j log(x/h)`; coefficients move by `≥(j+1)!/(x+j+2)^{j+2}` per step; blocks with a coefficient near a lattice number `O(ηH+1)` [L/S]. The binomial ceiling `2/(k+1)` binds one block, not a moving family. No saving derived yet. |
| Π98 Archimedean place versus depth | Classified | — | Depth aspect: `u↦1+q₁u` exact homomorphism, `q`-differencing exact. Height: `h↦t log(1+h/x)` additive up to `\|t\|hh′/x²`, an additive character only on `H≪x/√\|t\|` [L]. The archimedean place lacks exactness. |
| Π99 Count-distance rigidity | Solved | — | A positive integer-norm Beurling system other than the rational primes has count error `≥c log n` at arbitrarily large `n`; bounded multiplicities force unique factorization [L]. Odd primes plus labels of norms `3,4` give `N(x)=x+O(log²x)`, exact ternary-carry identity, averaged deficit `≍X log X` [L]. The threshold lies between `log` and `log²`. |
| Π100 Bounded count with a new zero | Solved (signed generators) | — | `a(n)=1−1_{2∣n}+4·1_{8∣n}`: nonnegative, multiplicative, `−3≤N(x)−x≤0`, zeros with `½<Re s<1` on a vertical progression, FE defect not sublinear; generators at 2 have negative multiplicity [L]. With nonnegative generators the question is open. |
| Π101 The comb of a return | Solved (polynomial reach) | method | Level sets of `t log n/2π` are multiplicative approximate groups; a return lays `P`-smooth integers on a comb; consecutive smooth blocks are excluded once `X≳t` at precision `≲1/k` [L]. Reach: first returns polynomial in the length. |

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
| Γ63 Poisson-extended Hecke positivity | No-go | — | [L]. |
| Γ64 Cross-zero Gram law | Solved (identity) | identity | [L]. |
| Γ65 Cutoff line law | Solved (edge) | sub | [L]. |
| Γ66 Scattering Blaschke product | Solved | — | `φ(s)(s−1)/s` Blaschke over `(1+ρ)/2` [L]. |
| Γ67 Abscissa split | Solved (identity) | RH | RH ⇔ ZAL ∧ AAL; under AAL eight RH-level statements coincide; `qRH ∨ AAL` [L/D]. |
| Γ68 Asymptotic abscissa law | Open | sub | ¬AAL ⇔ finite top and bottom layers ⇔ `ψ(x)−x=x^βT(log x)+O(x^{β−η})` [L]. |
| Γ69 AAL producers | Partially solved | sub | Bounded lags, twisted plateaux, JAS, towers, cone, shell positivity, typical JAS positivity, finite-measure excursions; a bounded phase return at each right zero; slow aligned returns on right discs [L]. Each retains its source bound. |
| Γ70 Zero–one law of recurrence | Classified | — | [L]. |
| Γ71 Pair recurrence | Partially solved | sub | At density-`(1−δ)` base heights [L]. |
| Γ72 Returns at a zero | Classified | — | Rare and threshold-quantized [L]. |
| Γ73 One-off countermodels | No-go (positive continuous data) | — | Continuous Beurling systems with exactly one off-line pair [L]. |
| Γ74 FE-defect rigidity | Partially solved | sub | Defect `≤1/6400` forces rational primes [L]. |
| Γ75 Inner field of a column | Solved | identity | [L]. |
| Γ76 Endpoint characters | Sharpened | RH | Column Young projections nonnegative; Toeplitz minors `≤200` nonnegative [L]. |
| Γ77 Tensor weights and compression | No-go (stated classes) | — | Golden passes; pure compression preserves even subspace iff RH [L]. |
| Γ78 Global trace on a family | Partially solved | RH | Kloosterman fibres pure by Stepanov; arithmetic family containing ζ open [L]. |
| Γ79 Displacement | Classified | — | Holomorphic data carry no weighting by displacement [L]. |
| Γ80 Finite oscillation | Solved | sub | Every witness has `β=Θ`, unique `T`, quantized coefficients, remainder ceiling, bounded-log-gap sign changes [L]. |
| Γ81 Dilation annihilation | Solved (identity) | sub | ¬AAL ⇔ two-prime annihilation of `ψ` to `O(x^{β−η})` [L]. |
| Γ82 Rightmost-zero jets | Solved | sub | Diagonal `→0`, off-diagonal `→m²`, short shifts `o(1)` [L]. |
| Γ83 Returns are prime returns | Solved | — | A return forces `n^{−iτ_j}→1` and a spike near the pole; limits fill the torus [L]. |
| Γ84 Isolation of ζ | Solved | identity | FE defect `≤1/6400` is one point; count distance `o(log n)` is one point (Π99); the exact parity identity pins `λ` (Π84) [L]. |
| Γ85 Rational zero relocation | No-go | — | Not Bohr almost periodic [L]. |
| Γ86 Modular horizon | Solved (exact solution) | RH (universal damping) | Exact metric, echo train, causal symbol, ringdown in the modes of the zeros; quarter-line bound ⇔ RH [L]. |
| Γ87 Raw echo decay | No-go | — | [L]. |
| Γ88 Near-arithmetic ladders | No-go | — | [L]. |
| Γ89 Blindness of physical positivity | Classified | — | Schur, KMS, reflection, `C*` positivity hold on every black hole [L]. |
| Γ90 Maximal-angle zero | Classified | RH | RH ⇔ `‖Q(tw)‖=‖Q(t̄w)‖` at zeros [L]. |
| Γ91 Lefschetz ratios | Solved | RH | Every right zero is read by `c_{m+1}/c_m→p^{ρ−½}` [L]. |
| Γ92 Fake black holes | Solved | — | Every local count is a tree quotient with flux and unitarity; `t²>4q` gives off-circle resonances [L]. |
| Γ93 Hecke rigidity on resonances | Solved | — | Commuting operators act by `X^d+Y^d`; positive families in every class exist on fakes [L]. |
| Γ94 Cuspidal sector | Classified | — | Independent Hecke content lives where there is no flux [L]. |
| Γ95 Krein flux law | Solved (identity) | RH (sign) | Flux `½𝒬_f≥0` ∀f ⇔ RH [L]. |
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
| Γ106 Missing input of transport | Solved (receiver) | sub | Bounded translates on a domain joining ρ to `Re s>1` ⇒ infinitely many zeros right of `Re ρ−r`; a bounded return at each zero ⇒ AAL; a head return of length `N≥11` has `N<τ+1` and, at large `τ`, `N<1024(log τ)⁴(log log τ)²`; for `2/log N≤τ≤N−1` some `n≤N` has `‖n^{−iτ}−1‖≥1/8` [L]. |
| Γ107 Effective transport | Solved | sub | On discs about `3+iγ` of radius `R>5/2`, `sup\|ζ(s+iτ)\|≥cτ^b` ⇒ the all-zero slow-return premise ⇔ RH; on discs with left edge `σ₀∈[½,β)` transport holds with explicit `transportExponent`, and slow aligned returns at each right zero give AAL [L]. |
| Γ108 Tail at a zero | Solved | — | At a zero a positive proportion of prime returns are not returns of ζ [L]. |
| Γ109 Limit map | Solved | — | Limits on `Re s>1` fill the torus, twin included [L]. |
| Γ110 Hull over the torus | Classified | RH | Liouville fibre extends ⇔ RH; RH ⇔ every nonzero limit of translates zero-free [L]. |
| Γ111 Stieltjes sign | Solved (necessary law) | — | `Im(w₀Q″/Q′)≤0` [L]. |
| Γ112 Rotated relation classes | No-go (coefficient growth) | — | Coefficients of growth `exp(C√\|w\|)` force triviality; a non-vacuous relation has coefficients of the size of `Q` [L]. |
| Γ113 Naive height, five currencies | Sharpened | RH | Degree-two form `≥0` iff a function bounded below lies at bounded distance; window naive height exists ⇔ positive; length `≤3/5` exists [L]. |
| Γ114 Dilation quotient | Sharpened | RH | Fixed `δ`: Poisson mean of `log\|ζ(½+iτ)/ζ(½+δ+iτ)\|` = outer term + surplus `I(1)−I_δ(1)≥0`; RH ⇔ zero surplus ⇔ critical/shifted Szegő budget ratio equality; Euler prefixes invariant; Dirichlet Gram = Abel squares = Laguerre energy [L]. |
| Γ115 The tail of a return carries the zero | Solved | sub | Zeros of ζ on `Re s>0` = zeros of the Euler tail `ζM_y` at every cut; along a bounded phase return the head returns and the tail carries the zero; every return on an isolating disc at a right zero is tail-bad at every cut with tolerance independent of the cut; such returns have density zero [L]. |
| Γ116 Head frozen at its resolution | Solved | — | `\|log\|E_y(s+iv)\|−log\|E_y(s)\|\|≤2\|v\|(log y+log 4)` on `Re s≥1`; resolution `y^{σ−1}` in the strip; finer features of `\|ζ\|` belong to the tail [L]. |
| Γ117 Trivial zeros of a cusp | Solved | graph | Mode polynomial `R(x)=det((x²+q)I−xA−q diag c)`, `R(0)=q^{#T}Π(1−c_v)`; integrality forces genus `≤` trivial zeros `+1`; cusp index law `\|c₀−1\|=q^{1−g}` [L]. |
| Γ118 Genus two does not force damping | No-go | — | Explicit 11-vertex graph with the genus-two curve FE for every `q≥2`; all modes on `\|z\|²=q` iff `q≤3`; slow resonance for `q≥4` [L]. FE + flux + unitarity + Hecke leave damping open. |
| Γ119 Natural boundary of the hull | Solved | — | Haar-a.e. fibre extends zero-free to `Re s>½` with natural boundary `Re s=½`; the same for a.e. fair-coin `±1` point; the Liouville point (all coins `−1`) extends iff RH [L]. |
| Γ120 Extremal law has a model | No-go | — | `w²−2w+2` satisfies the full maximal-angle inequality with off-axis zeros: no law from the extremal position alone excludes an off-axis zero [L]. |

## Scoped no-gos and surviving replacements

| Boundary | Exact scope and survivor |
|---|---|
| KR-TOR / KR-UCF / KR-R1 | Retired labels, not proved kills. BAG transfer closed (Γ1); PA Hermite-contour receiver (Σ73); TG Gaussian-passage receiver (Σ80). |
| KR-FPR | Finite and cofinal finite Hermitian KMS corrections cannot realize universal incidence passively [L]. |
| KR-SRP | Odd-only pole weight `β>1` impossible; even-only `β>1` not settled [L]. |
| KR-GAP | Excludes `E=QG₀(·+ih)`, `G₀` lower-Pólya; not arbitrary HB realizations [L]. |
| KR-R2 | Anchored 2-periodic loops realize every odd winding; not identified with renewal feedback [L]. |
| KR-R3 | Eventual upper bounds at every height ⇔ RH [L]. |
| Left-crossing slow returns | Discs reaching `Re s≤½` force `\|ζ\|≥cτ^b`; the stated polynomial premise there is RH. Right-edge discs carry the AAL receiver (Γ107) [L]. |
| Literal `riemannHypothesis_of_count` | `K:ℕ` equal to `Q(a)` needs integer values; the bounded-distance form Γ113 is the usable statement [D]. |
| Physical tearing at a critical ratio | Fails at Schur ratio `4/13` on prime quasimodes; conductor-adapted splitting survives [S]. |
| Extremal-angle contradiction | Polynomial model satisfies every order of the extremal law (Γ120); growth, log-concavity or arithmetic must enter [L]. |
| Bounded count as selector | Bounded count error admits a new zero with signed generators (Π100); positive generators: open [L]. |

## Bridges

| Bridge | Anchor |
|---|---|
| Window index counts distinct right zeros; `sup_dN_d` counts off-line multiplicity; bounded `N_d` gives finite support only | AHD, CWS, FFP [L] |
| RH ⇔ `a*(ζ)=⊤` ⇔ `1∈ℋ(c)` ∀c ⇔ `λ*(c)→0` ⇔ no finite contact ⇔ `Ψ` locally bounded | WVL, FADF, CHT, CSTW, AIF [L/D] |
| Window sign ⇔ two-site signs ⇔ reflection band ⇔ Stieltjes jets ⇔ two-bump family | GWZ, SWC, SRT [L] |
| Reflection-pair coupling = collar Hankel − smoothed count = `c_φ(2m)` | SWC, FADF [L] |
| Below `log 4`: sign ⇔ two-weight band ⇔ Hodge index ⇔ Künneth effectivity; below `log 5`: `{2,3,4}` band | SWC, LST, AHD, FADF [L] |
| Complete matrix at ratio `R`: below the top log window positive by rescaling; nonpositive directions meet the window; complement Gårding at every ratio | CACT [S] |
| Completed coefficient-space energy `=2Re[WH,WH]`; `D_s` negative weighted Hecke integral | RIT, ACP [L] |
| Isolated clusters ⇒ camera readout; positivity at `λ·½log T` ⇒ depth `<e^{−c log³T}` | ZCG [L] |
| RH ⇔ infinitely many unshifted Jensen degrees real ⇔ all positive-time heat zeros simple | FFP, RHTower, ZCG [L] |
| Suzuki first variation = Weil energy; Cayley ladder = Li; Li couplings `=−2` window form over `𝔽_q` | RHTower, ALG, GWZ [L] |
| Zero-free half-planes ⇔ finite free stability of shifted Jensen polynomials | FFP [L] |
| Hodge index = Metzler sign of the Cayley ladder = Li positivity | ALG [L] |
| Anchor flow: contact is `Ψ` unbounded | CSTW, AIF [L/D] |
| Theta spectrum = Eisenstein coefficient sum; columns add; current `=2\|Ξ\|²Re ξ′/ξ`; Ξ-current lift with the pole as worst fibre point | CAF, TCS, AIF, PTT [L] |
| Isolation = Carleson separation; `N(ρ)=Πϱ^m`; rate 2 isolated, `2θ` otherwise | MZF, AIF [L/D] |
| Causal certificate ⇔ Schur band; over `𝔽_q` ⇔ Castelnuovo ⇔ Abel budgets reach 1 | GWZ, AIF [L] |
| Abel log-mean ⇔ `I` at infinity ⇔ depth density `o(T)` ⇔ density-zero damping deficits | AIF, ASH [L] |
| ¬AAL ⇔ finite oscillation of `ψ(x)−x` ⇔ two-prime dilation annihilation | ZCG [L] |
| Zeros = power-law kernel of the cut system; finite-energy kernel mass decides RH; positivity of the cut system = edge `Re s=1` | RAC [L] |
| Λ = intersection number of torsion cycles; prime form = −renormalized positive torsion energy | AE [L] |
| Power-saving Liouville bound = zero-free strip; exact floor identity pins `λ` | RAC, AAD [L] |
| Count law ⇒ Hasse at genus one; FE at genus two does not force damping; integrality bounds genus by trivial zeros | ASH [L] |
| Krein square = degree form = Turán determinant of echoes = Castelnuovo–Severi defect | ASH, AE [L] |
| Zeros of ζ = zeros of every Euler tail; returns at zeros tail-bad; head frozen below `1/log y` | TAPO [L] |
| Proportional saving ⇔ no early heavy return; first return bracketed at every precision | TAPO, PTT [L] |
| Certificates past the abscissa ⇔ tail-good heights | TAPO, PTT [L] |
| Conditional tail laws end at the Kronecker scale `≈log T`; necessary mollifier length `exp(c log²T)` = length of an Euler mollifier over primes `≤c log²T`, where absolute non-alignment begins | APR, PTT, TAPO [L/D] |
| ζ isolated in FE defect, count distance and exact parity identity | APD, SPAL, RAC [L] |

## Strength of the open walls

- **RH:** Σ1, Σ2, Σ3a, Σ6 (all ranks), Σ7, Σ8, Σ17, Σ18, Σ19, Σ20, Σ28 (subexponential), Σ30, Σ32, Σ49, Σ56, Σ61, Σ66, Σ67 (all `d`), Σ70 (sign), Σ72 (all orders), Σ73, Σ74, Σ76–80, Σ85, Σ87 (all ratios), Σ93, Σ101, Σ113, Σ114, Π2, Π4, Π11h, Π17, Π23, Π28 (trivial point), Π30, Π36, Π42, Π47–50, Π58, Π59, Π62, Π63, Π66, Π68, Π69, Π78, Π81 (finite energy), Γ1, Γ4, Γ5, Γ8, Γ16, Γ19, Γ24, Γ46, Γ52–54, Γ61, Γ62, Γ76, Γ78, Γ86, Γ90, Γ91, Γ95, Γ97, Γ110, Γ113, Γ114.
- **≥qRH:** Σ4 (`K_ζ`), Σ28 (exponent `<½`), Π5, Π17 (log stage), Π23 (fixed degree), Π42 (dyadic), Π70 (polynomial rate), Π84 (power saving), `N_d` bounded, ZAL, inner-field decay.
- **sub:** Σ82, Σ1d, Σ1e, Σ1g, Σ1j, Σ1m, Σ1s, Σ6 (each rank), Σ30 (each stage), Σ47, Σ50, Σ70 (rate), Σ72 (band), Σ86, Σ87 (one ratio), Σ92, Σ94, Σ99, Σ100, Σ116, Σ117, Σ118, Σ122, Π7, Π9, Π11f, Π12, Π22, Π40, Π51–54, Π57, Π65, Π80, Π87, Π90, Π94, Π96, Γ15, Γ47, Γ57, Γ65, Γ68, Γ69, Γ71, Γ74, Γ104, Γ106.
- **indep. / method:** Π16, Π97, Π101, Γ49, Γ56, Σ127.
