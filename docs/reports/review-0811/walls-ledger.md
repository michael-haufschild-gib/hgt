# Walls ledger — status quo

**Corpus checkpoint:** commit `906b3c709c` plus the working tree of 2026-11-08. Working log: `logs/review-0811-status-research.md`.

Three wall families carry the frontier. **Σ** is the critical sign of the window form, **Π** the precision and production of the prime count, **Γ** the selection of ζ, the reflection of its zeros and the transport of its zeros in height. RH ⇔ `κ=0` ⇔ `a*(ζ)=⊤` ⇔ `λ*(c)→0` ⇔ `N_d=0` for infinitely many `d` ⇔ ZAL ∧ AAL ⇔ ZAL ∧ a thick `O(√X)` prime deviation ⇔ `Q` on integer probes is the Tate limit of a count [L]. None of these receivers supplies its arithmetic input.

**How the three families split one problem [D].** No test is compactly supported on both sides of the explicit formula. Σ fixes a compact prime side (windows); the zero side then has infinite rank and only an exact sign decides. Π localizes the zero side (Gaussian or band-limited weights, geometric scales of a tower); a crude bound then suffices — one upper bound per rational height ⇔ RH, a square-root bound on a thick set of scales plus ZAL ⇔ RH [L] — but the prime side needs square-root precision. Γ is the involution `ρ↦1−ρ̄`, the selection of ζ and the vertical transport of its zeros. The curve proof has finite rank (elimination is algebra, ZAL in tower form is automatic) and periodic zeros (AAL is automatic); ζ has neither [L].

[Frontier](../rh-current-frontier-map.md): **38 live formulations, 9 candidates** (APF, EGC, EWJ, FEL, IRK, MSC, RFHM, W1C, WBF). HJ→PA and BSH→CDC are aliases. [Scoped obstructions](../rh-killed-routes.md) separate failed mechanisms from open replacements.

- **Σ is the sign of every window, and nothing else.** RH ⇔ some weight is admissible on every window ⇔ `Ψ=½log H₁` locally bounded ⇔ Hasse–Weil along the cubic-spline orbit [L]. At the critical curve `R_c≤R_pole=R_high=W=⨅_A windowThreshold(A)` and below `W` the complete matrix is decided by its pole channel (Σ129, Σ135) [L/S]; the pole at every ratio is RH (Σ130). The theta all-rank problem is the sign of a head whose leading term is `|ζ(½+ib)|²` (Σ133) [L].
- **Π is the same sign on the prime side.** All unconditional savings sit at the VK curve. Over ℤ there is no crude regime in the size coordinate; crude regimes exist in the exceptional coordinate and on thick sets of geometric scales, where infinite-rank elimination works (Π111–Π114) [L]. The archimedean Frobenius substitute exists only approximately: returns freeze smooth polynomials, and the prime orbit has one fixed point (Π115) [L]. Farey discrepancy, the Mertens function, the nerve and core Euler characteristics and the sum of prime-vertex singular indices carry one number (Π105–Π107, Π119).
- **Γ is the same sign on the zero side, plus transport.** RH splits as ZAL ∧ AAL for every configuration; AAL is zero transport and tail transport (Γ142) [L]. No property depending only on zeros above a height or only below a fixed height decides the finite stratum (Γ140); FE, order one and reality admit every finite layer (Γ141); every positive class tested carries a finite layer and the law ignores the position of the line (Γ145) [L]. A count law has a quadratic half (FE) and a count half (damping); over ℤ the quadratic half holds and the count half is RH (Γ131); on true curves the defect is a point count (Γ154); the off-diagonal of Weil's form is assembled from two half-products and the sign sits in the diagonal, which renormalization cannot sign (Γ149–Γ153) [L]. Internal modular conjugation collapses to the Hilbert adjoint (Γ148) [L]. Every horizon observable is on the width axis.

Status: **Solved** (the face is a theorem), **Partially solved**, **Sharpened** (open, exact form a theorem), **Open**, **No-go** (mechanism refuted), **Classified**, **Reduced** (theorem-level equivalent of the wall named), **Scoped**. Strength: **RH**, **≥qRH**, **AAL** (implies AAL), **sub**, **indep.**, **identity**, **method**, **beyond RH**. Evidence: `[L]` Lean source; `[K]` Lean with transitive axiom audit; `[S]` Lean source unfinished, unintegrated or uncommitted; `[P]` paper only; `[D]` deduction; `[N]` numerical; `[C]` classical, not formalized.

Notation. Windows `[−a,a]`; `c_ψ(t)=W(ψ(·−t),ψ)`; `w_n=Λ(n)n^{−1/2}`; `δ` sliver width `2c−log n` (in zero statements the depth `Re ρ−½`); `ρ³=ρ+1`; `a_k=weilFloorApertureTower k`; `λ*(c)` best margin; `N_d` non-real root count of `R_d(Ξ)`; `Ψ=½log H₁`, `q=Ψ′`; `L=log T` in near-line statements, `L=log|t|`, `ℓ=log L` in orbit statements; `R=c⁸/log N`; `W₈(H)=∫H²e^{−8y}`; `Q₁=⌊(log N)^{13/32}⌋`; `R_c`, `R_pole`, `R_polar`, `R_high` whole-space, primitive-hyperplane, polar-payment and high-conductor critical thresholds, `W=⨅_A windowThreshold(A)`; `κ₀=2+γ−log 4π`; `R(y,η)` first return; `E_y` Euler head, `ζM_y` Euler tail; `A_φ(y)` horocycle mean; `m_g(y)` cusp energy; `Λ_g` completed Rankin–Selberg function; `𝒬_t(x,y)=y²−txy+qx²`; `Q(a)` the Weil form on integer probes; tower modes `e^{ℓ(ρ−½)}`, level sums `S(ν)`, thick = arbitrarily long runs arbitrarily far out; `primeDeviation(X)=(X−ψ(X))+X(Σ_{n≤X}Λ(n)/n−log X+γ)+O(1)`; `C_∞` archimedean compensation.

## Σ — critical sign

| Wall | Status | Strength | Content |
|---|---|---|---|
| Σ1 Weil's sign | Sharpened | RH | RH ⇔ `Q≥0` on every window ⇔ `a*(ζ)=⊤` ⇔ two-site PD ⇔ band at the centre in both sectors ⇔ Stieltjes jet moments ⇔ lattice Schur parameters in `(−1,1)` ⇔ `windowThreshold≡⊤` ⇔ every critical threshold `=⊤` ⇔ `1∈ℋ(c)` ∀c ⇔ `λ*(c)→0` ⇔ every window cone nonempty ⇔ Cayley ladders NSD ⇔ Suzuki first variation `≥0` ⇔ mollified Jensen stability ⇔ Krein positivity ⇔ prime-blind positivity ⇔ no finite contact ⇔ outer predictor at every window ⇔ every echo in its Schur band ⇔ every orbit correlation relatively compact ⇔ `Ω_ψ(a,X)≥0` ⇔ `Ψ` locally bounded ⇔ Hasse–Weil along the cubic-spline orbit ⇔ spline-orbit correlation `O(e^{εt})` ∀ε ⇔ prime-side Gram of the rank-two Hecke orbit `k log p+l log q` PSD [L]. |
| Σ1a Critical overlap and receivers | Solved | — | `c*_N≍L(log L)²`; tilted-spline and unit-bump receivers; one Beurling profile realizes every finite rational Gram [L]. |
| Σ1b Subcritical regime | Solved | sub | Complete matrix PD for `1≤c≤(log N)^α`, `α<1/8` [L]. |
| Σ1c Joint shell–pole payment | Solved | sub | Prime-successor edges pay nonconstant packet mass [L]. |
| Σ1d General profiles | Partially solved | sub | Every compact C² profile: energy `≥ae^{−Bc}‖x‖²` on conductors `≤N^θ`, `θ<¼`, `c≤b log log N` [L]. |
| Σ1e Conductor barrier | Partially solved | sub | Count form uniform for `m=o(c)`; low block `m≤Q₁` keeps half its diagonal plus its polar part at every ratio [K]. |
| Σ1f Defect-only confinement | No-go | — | `Q<2^k` witnesses [L]. |
| Σ1g Haar / Gamma graph | Partially solved | sub | All-detail prime–pole cancellation `O(e^{−√log Y/92160000})`; index `≤R+A`; growing Euler heads have unbounded index; nonfirst source keeps `1−ε` of Gamma [L]. |
| Σ1h Smooth logarithmic profile | Solved (to `ε₀c*`) | sub | Positive to `ε₀L(log L)²` [L]. |
| Σ1i Second order on horizon blocks | Classified | — | `κQ(H)+(βJ/K)∫e^{−(β+1)y}H²` [L]. |
| Σ1j Critical-curve decomposition | Partially solved | sub | Fixed independent mean-zero periodic families eventually PD at every ratio; distinct primitive conductors decouple at second order [L]. Growing families and coalescing frequencies open. |
| Σ1k Whole space at one critical multiple | Solved | sub | PD at `c≤2K₀(log N)^{1/8}` with complete Schur payment [K]. Cofinally `xiDampedSourceWork(n+4)≤2` ⇔ RH [L]. |
| Σ1l Window threshold | Reduced (to Σ56) | RH | `windowThreshold A=⊤ ⇔ A/2≤a*(ζ)`; `windowThreshold A₀=⊤` ⇒ `windowThreshold A≥ce^{3A₀}` ∀A [L]. |
| Σ1m Polarization inheritance | Partially solved | sub | Twisted sectors with positive scalar second order; short windows; cosh hyperplane [L]. |
| Σ1n Bulk below the grid | Classified | — | Reads only the pole [L]. |
| Σ1o Aperture-independent weighted floor | Solved (size-only) | — | `Q(H)≥−F(p)∫e^{−pu}H²`, `p>1` [L]. |
| Σ1p Terminal windows | Classified | — | Polar source with nontrivial kernel [L]. |
| Σ1q Receiving charges | Classified | — | Capacity `log log N+O(1)`; gcd-twisted charges split into four channels; non-gcd twists coercive up to `M₀(N)→∞` [L/K]. Near-gcd families and periods beyond `M₀(N)` open. |
| Σ1r Conductor packets and correctors | Classified | — | Terminal sources concentrate at the pole [L]. |
| Σ1s Far reserve and the high-conductor threshold | Classified | sub | `farMargin R=3D/(8R)−C−C′R`; on the complement of `V_{Q₁}` eventual PD and PSD hold exactly below `R_high=W` [L]. |
| Σ1t Prefix Schur cost | Partially solved | — | `(tail z)ᵀ(D−BᵀA⁻¹B)(tail z)=zᵀWz−rᵀA⁻¹r`, `A⁻¹≤20` [L]. |
| Σ1u Polar payment threshold | Sharpened | RH (all `R`) | `0<R_c≤R_c^{PSD}`, `R_c≤R_polar`, `R_c≤R_pole=R_high=W`; `R_polar≥c₁e^{c₂a}` for `0≤a≤a*(ζ)` [L]; `R_pole=W` [S]. |
| Σ1v One remaining channel at a fixed ratio | Reduced (to Σ130, Σ135) | RH (all `R`) | Physical Schur ratio `→4/13`; conductor-adapted far complement decouples; finite conductor prefixes leave residual coupling `≤ε`; fixed nonpolar conductors have vanishing top-window rows; whole-space collar Gårding loses only `b₁²` [L]. A fixed Schur multiplier is absorbed by band reserves; every low-packet cross term except the literal polar collar pairing costs an arbitrarily small packet diagonal; the low packet retains its exact scalar pole energy; Gårding and the far bridge share one decomposition [S]. |
| Σ1w Aperture exchange below the onset | Classified | sub (each `a`) | Window positivity at `a` ⇒ no zero of depth `≥¼` up to height `e^{a/K}`; Mertens lag `≤Cx^{−1/4}`; sharp pole self-energy; `|ψ(x)−x|≤Cx^{7/8}` from `β≤¾` to height `√x` [L]. `a*(ζ)` is not raised. |
| Σ1x Spline aliasing and Gamma reserves | Classified (no-go for uniform reserves) | — | Order-seven alias notch fixed by the spectral tail; resonant two-copy profiles defeat uniform logarithmic coefficient-norm Gamma floors [L]. |
| Σ2 Edge, zero modes, hard Lefschetz | Sharpened | RH | RH ⇔ HL on the PSD locus; zero modes radical and two-site; Hodge index = Metzler sign = Li positivity [L]. |
| Σ2a Interior-gap continuation | No-go | — | `κ(d)=1_{3∣d}` [L]. |
| Σ2b Edge singularity | Classified | — | No smooth eigenfunction, constrained ground state or capacity maximizer [L]. |
| Σ3 Stars and dilation monodromy | Partially solved | — / RH | Stars isometric; squarefree prime complex ≃ wedge of spheres [L]. |
| Σ3a Coprime stratum | Sharpened | RH | Redheffer `det=M(N)=−χ̃`; `χ̃=Ω±(√N)`; RH ⇔ `χ̃=O(N^{½+δ})` [L]. |
| Σ4 Finite index / heat count | Sharpened | ≥qRH (`K_ζ`); RH (`K_ζ⊠K_ζ`) | `κ<∞` ⇒ Lindelöf; RH ⇔ index `0`; TFAE: `κ(K_ζ)<∞` ⇔ finite index on one two-prime lattice ⇔ finitely many off-line zeros ⇔ bounded heat count ⇔ RH above some height; eventual slice positivity ⇔ finite off-line support; under finite support RH ⇔ one non-blind prime tower PD [L/K]. Whether finite index forces index 0 is B13; no asymptotic or local-below property decides it (Γ140). |
| Σ5 Collision quantum / window integer | Reduced (to Π17) | RH | Index `0` ⇔ Wiener–Hopf invertibility [L]. |
| Σ6 Rank / degree uniformity | Partially solved | RH | TH ranks `≤14` PD for `0<a≤½`; rank `N` from verified height; first-atom tails PD at every rank; all ranks reduce to the adaptive head (Σ133) [L]. |
| Σ7 Window Markov capacity | Sharpened | RH | RH ⇔ `R≤½` on the odd sector [L]. |
| Σ8 Realization | Sharpened | RH | Every window has an `ℓ²(zeros)` realization ⇔ RH; no finite-dimensional realization [L]. |
| Σ9 Explicit image / resolvent | Partially solved | RH in strip | Depth identity for `σ>1` [L]. |
| Σ10 Local signatures and gluing | Solved | — | `κ(φ_c)=κ+1` [L]. |
| Σ11 Product-formula gluing of the pole | Classified | — | Local poles add squares [L]. |
| Σ12 Running counterterm | Solved | — | `log N−γ` cancels the prime diagonal [L]. |
| Σ13 Tensor amplification | No-go | — | `K_ζ^n` PD ⇔ RH; tensor-square index `∈{0,∞}` [L]. |
| Σ14 Deformation to a positive model | No-go as free input | — | Crossing-free path ⇔ PD [L]. |
| Σ15 Separable assemblies | Classified (no-go) | — | Additive prime-tower assemblies have zero coprime cross-differences [L]. |
| Σ16 Prime–pole coherence | Solved (identity) | — | Complete form = jump + incidence − shell + diagonal + boundary [L]. |
| Σ17 Inter-tower coupling | Sharpened | RH | Bounded Gaussian-damped two-prime coupling ⇔ RH; undamped coupling on one cone ⇒ AAL [L]. |
| Σ18 Exact SOS on a two-prime lattice | Open | RH | Generic Hecke orbit carries the full Hodge defect [L]. |
| Σ19 Rank-one intertwining coefficient | Sharpened | RH | `κ_Hodge=#` band poles of `Λ(s)/Λ(s+1)` [L]. |
| Σ20 Scheduled prime sums | Open | RH | FU, CFC, RP, LI floors [L]. |
| Σ21 Extension / carrier | Classified | — | Escape, mixing, height decay ⇒ `κ∈{0,∞}` [L]. |
| Σ22 Lefschetz operators | Classified | — | Overlap-flow HL on the HR locus is RH [L]. |
| Σ23 Connected links | No-go (pure dilation complex) | — | Each tower is a clique [L]. |
| Σ24 Finite divisor | Solved | — | Coercive off `i/2` [L]. |
| Σ25 Separate semilocal positive factors | No-go (specified factors) | — | Indefinite beyond `A>½log p`; complete form positive through `181/500` [L]. |
| Σ26 Approximation by RH-true objects | Classified | — | Closure class Laguerre–Pólya [L/D]. |
| Σ27 Window stages | Partially solved | sub | Floors `(1/20000)/2^k` on `a_k`; `a_k<0.3621<½log 3` [L]. |
| Σ28 Window negativity budget | Sharpened | ≥qRH (exp `<½`); RH (subexp.) | Ground-energy floor `−Ce^{2σA}` ⇔ width `≤σ`; subexponential polar ground energy ⇒ AAL [L]. |
| Σ29 Low-frequency localization | Solved | — | Negativity only at the poles and below `τ₀(a)` [L]. |
| Σ30 The stage step | Reduced | RH (induction) | Single-prime transport for all `A` ⇔ RH; across `p=2` unconditional [L]. |
| Σ31 Positivity across dimension zero | Classified | = Σ1 | Bare domination ⇔ `Q≥0` [L/D]. |
| Σ32 Prime-blind positivity / calibration | Sharpened | RH | Full positive cone `{Λ}` under RH, empty otherwise; Carlson threshold `e^{(π/2)|t|}` [L]. |
| Σ33 Tate positivity horizon | Classified | — | Positive Tate dimensions `[0,κ(A)]`; finite templates iff spread `<27/5`; dimension one through `log 5` [L]. |
| Σ34 Canonical-degree horizon | Classified | — | Horizon `≍e^{−A/2}` [L/D]. |
| Σ35 Canonical system of the tower | Solved (precontact) | identity | Lattice Levinson; precontact de Branges spaces; `H₁H₂=1`; anchor flux; sampling bases [L]. |
| Σ36 Rational Hecke-graph reading | Solved (identity) | — | Window positivity ⇔ every finite rational Hecke graph of smaller spread [L]. |
| Σ37 Lattice canonical system | Solved (identity) | — | Window ⇔ its lattices [L]. |
| Σ38 Two-site decision | Classified | — | RH ⇔ two-site PD; `(γ,v)` decide the line; on two smoothed Frobenius graphs the defect is the genus form `[[c_B(0),c],[c,c_B(0)]]` and Hasse–Weil for every integer pair ⇔ RH [L/S]. |
| Σ39 Trivial-divisor transmission | Solved (identity) | — | Collar Hankel form, inertia `(1,∞)` [L]. |
| Σ40 Degenerations are curves | Classified | — | Degenerate lattice windows are finite curves [L]. |
| Σ41 Aperture–depth duality | Classified | — | Positivity at level `a` ⇒ `|β−½|<10⁶exp(−a/(1200log(|γ|+3)))`; `N(t,t+1]≤240log(|t|+3)` [L]. |
| Σ42 Markov and variance-free ground states | No-go | — | Markov dies at `e^{−3/4}`; variance-dropped fails for `c>273/400`; prime 3 as collar potential fails for `c≥287/500` [L/K]. |
| Σ43 Pole-charged ground-state calculus | Solved (identity) | — | `Ẑ(Φωu)=J_{Φω}(u)+∫u²ω𝒢_S(ω)+2V_s−2V_c` [L]. |
| Σ44 Collar locality of the kick | Classified | — | Collar ratio `2w_ne^h` sharp [L/D]. |
| Σ45 Reflection pairs and parity sectors | Solved (identity) | — | `W(f±f∘R)=2W(f)±2𝒞_m(f)` [L]. |
| Σ46 Frustration of the odd sector | Classified | — | Odd prime reflection anti-Markov, not removable by gauge [L]. |
| Σ47 Odd unit window | Open (structural); rung available | sub | Positivity ⇔ `w₂∈unitBandWeights`; margin `≈2·10⁻⁴` [L/N]. |
| Σ48 Criticality | Classified | — | Zero slack; `1` the only all-window multiplier [L/D]. |
| Σ49 Reality by continuation | Sharpened | RH | Real collision iff `Re Q(0)=Im Q′(0)=0`; exclusion at every positive time ⇔ RH [L]. |
| Σ50 Below `log 4` | Sharpened; rung available | sub | Positivity ⇔ two-weight band ⇔ Hodge index ⇔ Künneth effectivity [L]. |
| Σ51 Sectors as moment problems | Solved (identity) | — | Even Hamburger, odd shifted Hamburger, window Stieltjes [L]. |
| Σ52 Prime-weight confinement | Solved (sharp) | — | Outer law `|λ(n₀)|≤√n₀(log(1/δ)+B)` [L]. |
| Σ53 Size versus sign of the kicks | Classified | — | Size certificates die at `E_c≥1`, `c*∈(½log5,½log6]` [L]. |
| Σ54 Sector order of the archimedean place | Classified | — | Gamma ladder [L]. |
| Σ55 Euler-stage phase repulsion | Solved (above horizon) | — | Phase lattice above `2πe^{W_a}` [L]. |
| Σ56 Onset aperture of `ζ` | Sharpened | RH | RH ⇔ `a*(ζ)=⊤`; `log R_high≥6a*(ζ)+log c₀` [L]. |
| Σ57 Perron / Beurling–Deny | Classified (no-go past `log ρ`) | — | Even band Markov iff `c≤log ρ` [L]. |
| Σ58 Window visibility law | Classified | — | Universal pair-energy threshold [L]. |
| Σ59 Shielded zeros at fixed aperture | No-go | — | Cut crystal hides any fixed depth to `(log T)/36` [L]. |
| Σ60 Switching to balance | No-go | — | Every nonconstant sign gauge creates negative conductance [L]. |
| Σ61 Hardy criticality | Sharpened | RH | `ℋ(c)` closed antitone interval [L]. |
| Σ62 Trace theory of certificates | Classified | — | Weil's form reads no point values [L]. |
| Σ63 Trivial zeros at the centre | Solved (identity) | — | Not part of the frustration [L]. |
| Σ64 Signed certificate format | Solved (identity) | — | Neutral even gauge and shifted ground state [L]. |
| Σ65 Finite-template reduction | No-go at spread `27/5` | — | [L]. |
| Σ66 Contact of the de Branges chain | Sharpened | RH | RH ⇔ no finite contact; contact forces kernel divergence [L]. |
| Σ67 Untwisted–twisted coupling | Reduced | RH (all `d`) | `d=2` unconditional; all `d` ⇔ RH [L]. |
| Σ68 Gauge freedom | Classified | — | Neutral gauges act only in the pole direction [L]. |
| Σ69 Width at bounded aperture | No-go | — | Every bounded aperture is consistent with every width [L]. |
| Σ70 Free-weight margin and bands | Sharpened | RH (sign); sub (rate) | `λ*(c)≤K exp(3c−(π/6)e^{2(c−13/12)})`; RH ⇔ `λ*→0` [L]. |
| Σ71 Datum of the window cone | Classified | — | Datum region convex, `⊆{β≤1}`, `(1,0)` in it ⇔ RH [L]. |
| Σ72 Centre jets and the slice band | Partially solved | RH (all orders) | PF₂₀₀; slice coefficients `≥0` for `|t|≤133/2`; off-line zeros have `|Im|>67` [L]. |
| Σ73 Hausdorff rows | Sharpened | RH | Rows nonnegative past an explicit shift; remaining entries ⇔ RH [L]. |
| Σ74 Heat-grid detectors | Sharpened | RH | Two grids at every degree ⇔ RH; one-sided Gaussian prime ceiling at every rational height ⇔ RH [L]. |
| Σ75 Hamiltonian density | Solved | identity | Finite Grams AC before contact [L]. |
| Σ76 Theta endpoint energy | Partially solved | RH | Boundedness ∀`0<t<½` ⇔ RH [L]. |
| Σ77 Renewal joint nodes | Sharpened | RH | `det₂` represents `D`, not Ξ [L]. |
| Σ78 Cosine-source zero loss | Partially solved | RH | Strict Laguerre for `h≥½` and above VK [L]. |
| Σ79 Quartic Schur charge | Partially solved | RH | Late charge `≤HS/400` [L]. |
| Σ80 Anchored cubic gate | Sharpened | RH | Enclosed multiplicity `≤` trace norm [L]. |
| Σ81 Center-tail fibres | No-go (numerical) | — | [N/D]. |
| Σ82 Finite-rung principle | Partially solved | sub | RH through height 67 in Lean [L]; no finite rung decides RH, B13 or AAL (Γ140). |
| Σ83 Floors suffice | Solved (receiver) | RH | `−C_σe^{2σr}∫F²` ∀σ>0 ⇒ RH [L]. |
| Σ84 Width axis | Classified | ≥qRH (interior) | Every interior value of every width parameter is a zero-free strip [L/D]. |
| Σ85 Anchor flow | Solved (identity); control open | RH | `L′=q−sinh 2L` [L]. |
| Σ86 Scale-invariant flow bound | Open | sub | Bounded variation of `r` free of `1/μ` [D]. |
| Σ87 Compactness at a critical ratio | Solved (assembly) | sub | Γ-liminf with weight `α_R`; Kolmogorov–Riesz; `R_high≥W` [L]. |
| Σ88 Limit pencil at a fixed ratio | Classified | sub | Nonpositive directions meet the top window of length `(1/8)log R+O(1)` [L]. |
| Σ89 Parabolic blindness | No-go | — | `Φe^{−τx²}` has the same parabolic laws [L]. |
| Σ90 Central inequality | Classified | stronger than RH | [L]. |
| Σ91 Gap dynamics | Solved (laws) | identity | [L]. |
| Σ92 Crystal on typical heights | Partially solved | sub | `Λ_X log X→0` on density one [L]. |
| Σ93 Collision frequency | Sharpened | RH | Multiplicity `≤(3300/9991+ε)log X` [L]. |
| Σ94 Depth law | Partially solved | sub | Isolated simple zeros [L]. |
| Σ95 Pointwise two-prime payment | No-go | — | Negative at centre `log 6` [L]. |
| Σ96 Euler-operator theta spectrum | Solved (identity) | identity | `S=Π_pT_pA`; `A` not a positive Laplace mixture; the reflected squared theta product has no finite positive or signed Laplace representation [L]. |
| Σ97 Torus-uniform theta positivity | No-go (numerical) | — | [N]. |
| Σ98 Finite theta heads | No-go (fixed heads) | — | No fixed head pays every rank; no summable absolute pair majorant; no compact core [L/S]. Survivor: the adaptive head (Σ133). |
| Σ99 Local onset field | Partially solved | sub | `Ω_ψ(a,X)` sum over zeros; RH ⇔ `Ω≥0` [L]. |
| Σ100 Runs on the critical line | Partially solved | sub | `≥N(T)/5000` starts of five consecutive simple critical zeros [L]. |
| Σ101 Causal certificate | Solved (identity) | RH (all windows) | PD ⇔ positive-margin outer predictor [L]. |
| Σ102 Szegő threshold | Classified | RH (position) | [L]. |
| Σ103 Reflection coordinates | Classified | — | Reflection data free; forward map causal injective [L]. |
| Σ104 A priori estimates free of `1/μ` | Solved (model) | sub | Born model [L]. |
| Σ105 Soft prime kick | Solved | identity | [L]. |
| Σ106 Green corner | Solved | identity | `q_y→q` in `L¹` [L]. |
| Σ107 Far-translate decoupling | No-go | — | `c_φ(t)↛0` [L]. |
| Σ108 Insertion cone | Classified | — | Below left growth `½` Hecke cone = torus cone = exponential convexity [L]. |
| Σ109 Fixed-amplitude locking | No-go | — | Only amplitudes oscillating with the height escape [L]. |
| Σ110 Columns add | Classified | — | Infimum of signed columns = sum of minima [L]. |
| Σ111 Curve flow | Solved (calibration) | — | Unitary ⇔ first `R` margins positive [L]. |
| Σ112 Theta current | Solved (explicit) | identity | `current=2|Ξ|²Re ξ′/ξ` [L]. |
| Σ113 Restoring bound of the actual chain | Solved (identity); control open | RH | RH ⇔ `Ψ` locally bounded on precontact intervals [L]. |
| Σ114 Bohr profile decomposition | Classified | RH (for ζ) | RH ⇔ every orbit correlation relatively compact [L]. |
| Σ115 Critical Γ-liminf | Solved | identity | `liminf Q(U_N)≥Q_T(F)+α_R∫_{y<0}F²e^{−8y}` [L]. |
| Σ116 Weighted Gårding | No-go (full horizon); Solved (top collar) | sub | [L]. |
| Σ117 Typical-height sign | Partially solved | sub | Bad set Gaussian-tailed; asymptotic property in the sense of Γ140 [L]. |
| Σ118 All-height sign | Open | sub | Size reaches `a≈log log X−log 4` [D]; past it Π80, Π87. |
| Σ119 Tangent of the forward map | Solved | identity | [L]. |
| Σ120 Certified passivity | Solved (certified windows) | sub | Total length `≤2a₀` [L]. |
| Σ121 Bounded extremals for every weight | Solved | identity | [L]. |
| Σ122 Prefix–collar coupling at a critical ratio | Reduced (to Σ130, Σ135) | RH (all ratios) | Physical tearing fails at `4/13`; conductor-adapted splitting decouples [L]. |
| Σ123 Kernel-valued prime payment | No-go (returning coordinates) | — | Euler coordinates cannot cross `Re s=1` [L]. |
| Σ124 Critical coupling of the base | Classified | — | `thetaAmp(x)e^{x/2}→½` [L]. |
| Σ125 Certificates on the orbit | Classified | — | Frozen certificate exactly when `−ζ′/ζ(σ)≤B(σ+it)` [L]. |
| Σ126 Top logarithmic window | Solved (non-escape) | sub | Below `c₀e^{6a*}` every nonpositive vector charges both `V_{Q₁}` and the top window [L]. |
| Σ127 Splitting order at a critical ratio | Classified | method | Conductor first, position second [L]. |
| Σ128 Certificates past the abscissa | Classified | — | `Σ_p|1−E_p(s)|<∞` ⇔ `Re s>1` [L]. |
| Σ129 Critical positivity threshold law | Classified | RH (all thresholds `=⊤`) | `0<R_c≤R_c^{PSD}`, `R_c≤R_pole≤R_high=R_high^{PSD}=W≥c₀e^{6a*(ζ)}`; every threshold `=⊤` ⇔ RH [L]; `R_pole=W` [S]. Whether `R_c=W` is Σ135. |
| Σ130 Low-packet payment at every ratio | Reduced (to Σ1) | RH | Payment at `R` on `[−A,0]` ⇒ `R≤windowThreshold A`; payment at every `R` on growing windows ⇒ RH [L]. |
| Σ131 The cone counts primes | Partially solved | sub (finite range) | `|ψ_λ(X)−X|≤CX^{5/6}log X` for `X≤e^{2c−3}` [L]. |
| Σ132 Frequency packets | Solved (identity) | identity | `∫Re W(f⋆φ_X)dX=2π‖φ‖₂²Re W(f)` [L]. |
| Σ133 The theta head is ζ on the critical line | Sharpened | RH (all ranks) | Fixed `M`: pair head `=(4/√π)|Σ_{n≤M}n^{−½+2iτ}|²+o(1)` [L]; below the grid `|Σ_{k≤M}k^{−½−ib}−ζ(½+ib)|≤9M^{−½}+M^{½}/|b|`; for `M(b)=⌈|b|/2⌉+B` the error is `(9√2+√(1+2(B+1)))|b|^{−½}` and the leading term is `|ζ(½+ib)|²+O(|ζ||b|^{−½}+|b|^{−1})` [L]. Uniform Gamma-weighted transport of the fixed-`M` asymptotic to `M=M(b)` and a strict signed floor near critical zeros are open. |
| Σ134 Reflected pairs at the decay boundary | Classified | — | Pair positivity iff `δ=0` [L]. |
| Σ135 The critical matrix is decided by the pole channel | Reduced (to B104) | method | Positivity on `ℝ^N` = positivity on the primitive hyperplane + positivity on `x+w`, `0≠x` polar, `w` primitive; below `W` the complete matrix is PD iff its pole channel is; `R_c=W` ⇔ the pole channel pays at every `R<W` [L]. |
| Σ136 Charged profiles at the critical curve | Partially solved | method | Strong subsequential limits with unit joint mass (profile + pole coordinate); polar row converges to its sampled profile on each terminal fraction; polar source continuous in the exponential norm; payment at a larger ratio leaves explicit `W₈` and pole reserves; polar payment at a strictly larger ratio excludes nonzero charged limit profiles [S]. The full physical pairing for actual nonpositive sequences remains (A44). |

## Π — precision and production

| Wall | Status | Strength | Content |
|---|---|---|---|
| Π1 Global law | Solved (equivalence) | RH | `ψ(x)−x≤C√x log²x` ⇔ RH [L]. |
| Π2 Deciding input | Open | RH | No unconditional input at square-root precision; any count-implying input is parity-breaking, locally pure, precision-faithful, of unbounded aperture [L]. |
| Π3 Producer cost | Solved (exponent scale) | sub / qRH / RH | Balanced stencils reach `ψ,θ≤(1+ε)x+C_εlog²x` [L]. |
| Π4 Window precision | Sharpened | RH | Reflection-pair prime-count band ⇔ RH [L]. |
| Π5 Conjugate diagonal | Sharpened | sub → ≥qRH → RH | One dyadic constant ⇔ RH [L]. |
| Π6 Averages versus all heights | Partially solved | — | [L]. |
| Π7 Census / pair surplus | Partially solved | sub | Simple critical `≥0.67250071`; positivity-only certificates cannot reach `3/4` [L]. |
| Π8 Depth visibility | Classified | — | [L]. |
| Π9 Exceptional moduli | Partially solved | sub | Siegel for `q≤(log x)^A` [L]. |
| Π10 Frequency localization | Solved | — | [L]. |
| Π11a–e Cone, bidegree, fixed-rank, definite, Siegel counts | No-go (named ansätze) | — | [L]. |
| Π11f Logarithmic duality | Partially solved | sub | [L]. |
| Π11g Boost transform | Solved (identity) | — | `∫Z⁺(s,u)e^{2wu}du=K(s,w)ζ(s+w)ζ(s−w)` [L]. |
| Π11h Source effectivity | Sharpened | RH | Bézout ⇔ source-energy sign ⇔ RH [L]. |
| Π12 Subconvexity / heat floor | Partially solved | sub | `μ(½)≤33/200` [L]. |
| Π13 Prefix scale | Solved | — | [L]. |
| Π14 Amplifier rank | No-go (finite support) | — | [L]. |
| Π15 Critical-scale residual sign | Classified | — | [L]. |
| Π16 Genus function | Sharpened | indep. | [L]. |
| Π17 Window energy | Sharpened | RH; ≥qRH (log stage) | Bounded port ⇔ purity [L]. |
| Π18 Finite realizations | No-go | — | [L]. |
| Π19 Moment-only improvement of Jensen | No-go | — | [L]. |
| Π20 Count identities at the first prime | No-go (finite-square format) | — | [L]. |
| Π21 Exact balance | Classified | — | [L]. |
| Π22 Near-line density ladder | Sharpened | sub | Corridor exceptions `O(T/log^ηT)` [L]. |
| Π23 Inner caps | Reduced | RH; ≥qRH (fixed degree) | [L]. |
| Π24 Parity at dimension zero | Classified | — | [L]. |
| Π25 Euler-product pinning | Classified | — | [L]. |
| Π26 Bulk second order | Solved | — | `2γ₁+γ²` [L]. |
| Π27 Retained Gamma comparison | No-go (lossless) | — | [L]. |
| Π28 Gauge-torus spectrum | Classified | RH at the trivial point | Pole-subtracted exponents `[Θ,1]` [L/K]. |
| Π29 Square-root threshold | Classified | — | [L]. |
| Π30 Collective payment of the kicks | Sharpened | RH | [L]. |
| Π31 Terminal prime channels | Solved | — | [L]. |
| Π32 Elementary sieve inputs | Solved | — | [L]. |
| Π33 Finite free Gaussian capacity | Classified | — | [L]. |
| Π34 Euler-side stability and drift | Classified | — | [L]. |
| Π35 Source-faithful finite free split | No-go | — | `Θ` never real-rooted [L]. |
| Π36 Mollified Jensen stability | Sharpened | RH | [L]. |
| Π37 Zero-free half-planes and the exact count | Classified | — | `sup_dN_d` = off-line count; `N_d≤300√(d log d)` [L]. |
| Π38 Finite free Hardy theorem | Solved | — | [L]. |
| Π39 Archimedean Wiener–Hopf factorization | Solved (identity) | — | [L]. |
| Π40 Self-improvement of a strip | Open | sub | `Θ<1⇒Θ=½` false for shifted products [L]. |
| Π41 Necessary-length laws | Solved (necessary bounds) | — | Excess `K₀/log T` forces `log N≥log²T/(6K₀)−(4/3)log T`; an Euler mollifier `Π_{p≤y}(1−p^{−s})` (length `y#≤4^y`) with near-unit second moment needs `y≥min(1/24,1/(14K₀))log²T/log 4` [L]. |
| Π42 Long-mollifier receivers | Sharpened | RH; ≥qRH | [L]. |
| Π43 Length–precision law | Classified | — | [L]. |
| Π44 Explicit contour and mass bounds | Solved | — | [L]. |
| Π45 Bulk statistics of Jensen roots | No-go | — | [L]. |
| Π46 Entry filters | Classified | — | Type I/II parity-blind [L]. |
| Π47 Signed incidence precision | Partially solved | RH | [L]. |
| Π48 Factorial-Fock seam bound | Sharpened | RH | [L]. |
| Π49 Completed Suzuki residual | Partially solved | RH | [L]. |
| Π50 Möbius critical energy | Partially solved | RH | [L]. |
| Π51 Vinogradov–Korobov barrier | Open | sub | Every unconditional saving sits at VK [L]. |
| Π52 Hyperbolic density | Partially solved | sub | [L]. |
| Π53 Cluster wall | Open | sub | [L/D]. |
| Π54 Negative moments at zeros | Open | sub | [L]. |
| Π55 Barrier blindness | No-go | — | [L]. |
| Π56 Last-scale floor | Classified | — | [L]. |
| Π57 One-logarithm loss | Sharpened | sub | [L]. |
| Π58 One-window width | Classified | RH at `β=0` | [L]. |
| Π59 Exponent rigidity | Classified | RH | [L]. |
| Π60 Truncated Möbius collar | Classified | — | [L]. |
| Π61 Prime field at the critical scale | Solved | sub | Selberg CLT [L]. |
| Π62 Zero-damping hypercube | Sharpened | RH | [L]. |
| Π63 Second expression of the inner mass | Solved (identity); producer open | RH | [L]. |
| Π64 Box budgets | Solved | identity | [L]. |
| Π65 Log-mean of ζ | Reduced | sub | Abel form ⇔ depth density `o(T)`; Selberg: depth `O(T)`; squared off-line depth moment `o(V)` [L]. `o(T)` open; an asymptotic property in the sense of Γ140. |
| Π66 Integrality over ℤ | Solved (exact) | RH at `√` scale | Stepanov over ℤ = integrality floor + Nair ceiling, reaching Chebyshev [L]. |
| Π67 Stencil ceilings | Classified | — | [L]. |
| Π68 Möbius zero condensation | Classified | RH | [L]. |
| Π69 Integer lag | Sharpened | RH | [L]. |
| Π70 Rate of a stencil | Solved (exponent scale) | sub / qRH | Under RH the exponent lies in `[¼,½]` [L]. |
| Π71 Laws of a producer | Solved | — | [L]. |
| Π72 Ledger blindness | No-go | — | [L]. |
| Π73 Parity ledger | Classified | — | [L]. |
| Π74 Fake prime measures | Classified | — | [L]. |
| Π75 Hecke action on producers | No-go (positive amplification) | — | [S]. |
| Π76 Frobenius as a stencil | Solved (calibration) | — | [L]. |
| Π77 Near-extremal rigidity | Solved | identity | [L]. |
| Π78 Holomorphic Abel budgets | Open | RH | [L/K]. |
| Π79 Arithmetic Carleson measure | Solved | identity | [L]. |
| Π80 Short-sum barrier | Open | sub | [L]. |
| Π81 Kernel of the cut system | Classified | RH | [L]. |
| Π82 Ledger hierarchy | Solved | — | [L]. |
| Π83 Twin at every degree | Solved | — | [L]. |
| Π84 Parity exponent | Solved | ≥qRH at power saving | [L]. |
| Π85 Exchange law | Solved | — | [L]. |
| Π86 Carry of the floor | Solved | — | [L]. |
| Π87 Absolute non-alignment | Partially solved | sub | [L]. |
| Π88 Rounded orbit | No-go | — | [L]. |
| Π89 Discrepancy and mixing time | Classified | — | [L]. |
| Π90 Energy past the diagonal | Partially solved | sub | [L]. |
| Π91 Curve stencil | Solved (calibration) | — | [L]. |
| Π92 Prime kernel as torsion energy | Solved (identity) | — | [L]. |
| Π93 Möbius as a cubic Gauss coefficient | Solved (identity); descent partial | past VK | [L]. |
| Π94 First return of the prime orbit | Partially solved | sub | Constant precision open [L]. |
| Π95 Proportional saving = heavy first return | Classified | — | [L]. |
| Π96 Conditional tail law and the Kronecker scale | Partially solved | sub | [L]. |
| Π97 Moving jet of the logarithm | Partially solved | method | [L]. |
| Π98 Archimedean place versus depth | Classified | — | [L]. |
| Π99 Count-distance rigidity | Solved | — | [L]. |
| Π100 Bounded count with a new zero | Solved (signed generators) | — | [L]. |
| Π101 The comb of a return | Solved (polynomial reach) | method | [L]. |
| Π102 Positive Euler products with a finite top layer | Solved (countermodels) | — | Integer norms and rational-prime labels carry a finite top layer; nonnegative two-prime polynomials annihilate any finite set; accuracy on the right forces growth on the left; arbitrary multiplicity at mass arbitrarily close to 1; harmonic packets of `m` points force mass `≥m`, equality iff phases are nontrivial `(m+1)`st roots of unity, attained with the prime 2 [L]. |
| Π103 Arithmetic mean values of smooth × prime | Solved | sub | [L]. |
| Π104 Twin quarter floor | Solved | — | [L]. |
| Π105 Farey, Mertens and the nerve | Solved (identity) | RH | [L]. |
| Π106 Persistence of the prime-product complex | Classified | — | Interval module of odd squarefree `m`, bar `[m,2m)`, `s`-independent; prime-valued boundaries; two-prime block quotients [L]. |
| Π107 Connected prime core and fixed points | No-go (literal localization); Classified | — | Maps homotopic to the identity fix the upper-half primes; core ≃ bouquet with augmented Euler characteristic `M(N)+#primes(N/2,N]` [L]. |
| Π108 Renormalized torsion forms | Solved (convergence); Classified (sign) | — | On `ℓ²(n^δ)`, `δ>0`: operator-norm convergence; compact self-adjoint limit; definite subspaces of every dimension of both signs, surviving every finite family of linear constraints and every finite-rank correction; Hilbert–Schmidt iff `δ>½` [L]. Renormalization carries no sign (Γ149). |
| Π109 Sharp sources on the horizon | Classified | beyond RH | Sharp shells: log-free `O(√y)` (`|E(Y)|≤8√Y`, `|H(X)−3X²/(2π)|≤19X`); one shell at `y^α` forces `Re ρ≤2−2α`; one shell at the RH rate ⇔ RH ∧ `Σ_{d≤X}μ(d)E(X/d)=O(X^{½+ε})` [L]. |
| Π110 Thermal averages of the primon gas | Classified | — | Euler factors at real points `>1` [L]. |
| Π111 No crude regime in the size coordinate | Classified | — | `|ψ(x)−x|≤C√x` false; any exponent `½+ε` is RH; tensor index `∈{0,∞}`. Crude regimes exist in the exceptional coordinate (ZAL, AAL) and on thick sets of scales (Π112–Π114) [L]. |
| Π112 The exceptional rank decides the window | Classified | method | Distinct visible top points of modulus `R` over a remainder `≤r`: `|S(ν)|≥εRᵛ−(Σ|b|)rᵛ` on every window of `k` levels; excursions syndetic with gap the exceptional rank; no thick set carries a bound below `R`; hiding a top on the window at position `M` costs trace norm `≥εR^{M+1}`. Rank barrier: roots-of-unity towers vanish off `kℤ` (density `1−1/k`, runs `k−1`), surviving any critical remainder; `N` unimodular modes cancel any `N` values [L]. |
| Π113 Infinite-rank Hasse–Weil principle | Solved (principle) | method | Well-founded outer part + reflection-compatible weights + `|S|≤C` on a thick set ⇒ only `|z|=1` visible; curves: thick trace or point-count bounds ⇒ unitary; ZAL ⇔ well-foundedness of the tower at every base; Wolff configurations show well-foundedness is needed [L]. |
| Π114 Thick crude count over ℤ | Sharpened | AAL; RH with ZAL | Lag along a tower of ζ = level sum with weights `1/(q(1−q))`, every point visible; thick lag bound of exponent 0 at one base ⇒ AAL; `primeDeviation=O(X^{½+a})` on a thick set of geometric scales of one base ∀`a>0` ⇒ AAL; RH ⇔ ZAL ∧ thick `O(X^{½})` [L]. Open for ζ (B110). |
| Π115 Returns freeze smooth polynomials | Classified | method | At a `δ`-return of `P`, `|n^{−it}−1|≤Ω(n)δ` for `P`-smooth `n`; Dirichlet polynomials on `P`-smooth integers move by `≤δΣ|c_nn^{−s}|Ω(n)`; `J` moment conditions force approximate vanishing to order `J` at every return; two distinct primes have no common exact return (one fixed point) [L]. The Frobenius substitute is approximate. |
| Π116 Long mean values are collision counts | Solved (identity) | identity | Fejér-weighted mean value of any Dirichlet polynomial = `Σa_ma_nκ_T(log n−log m)`; for `1_{[1,N]}`, `N≥T`, exact order `N²` against diagonal `TN/2`; prime polynomials: collision count of prime pairs with `|log(p′/p)|≤π/T` [L]. |
| Π117 Completed prime boundary | Classified | — | `Σp^{−s}a_p` on `Σp^δ|a_p|²` extends boundedly and closedly iff `2Re s+δ>1`; at or below, unit boundary at arbitrarily small norm and no closed extension; imaginary gauges unitary in every exterior degree [L]. |
| Π118 Torsion compensation boundary | Classified | — | Prime-star positivity on all finite stars ⇔ summable Schur payment; leaf diagonal `p^δ` iff `δ>0`; logarithmic `(log p)^α` iff `α>2`; full torsion matrix compensated by `CΣ(1+log n)^αx_n²` iff `α>2` [L/S]. Compensates torsion, not Weil's form. |
| Π119 Prime-vertex dynamics and singular indices | Classified | — | Face-preserving cutoff-natural self-map homotopic to the identity with fixed points exactly the prime vertices; compact isolating blocks with exit ≃ upper link; relative singular index `1−#{q>p: pq≤N}` for `p≤N≤p³`, unbounded below [L]; finite face realizations have Euler characteristic the alternating face count [S]. |

## Γ — selection, reflection and transport

| Wall | Status | Strength | Content |
|---|---|---|---|
| Γ1 Trivial gauge point / self-return | Open | RH | Cutoff-uniform positive Haar target mass on doubled discs ⇔ RH [L]. |
| Γ2 Prime-set flips | Solved | — | [L]. |
| Γ3 Twin-blindness of soft structure | No-go | — | [L]. |
| Γ4 Frobenius at infinity | Sharpened | RH | Window involution = twisted Krein reflection [L]. |
| Γ5 Source identification | Partially solved | RH | [L]. |
| Γ6 Boundary sign / coherence | Solved | — | [L]. |
| Γ7 Affine carrier | Solved | — | [L]. |
| Γ8 Poisson rigidity | Sharpened | RH | Zero-side positivity = RH [L/S]. |
| Γ9 Archimedean continuity vs height decay | No-go | — | [L]. |
| Γ10 Function-field indistinguishability | Sharpened | — | [L]. |
| Γ11 Pole-blindness of the glue | No-go | — | [L]. |
| Γ12 General gauges | Solved | sub | [L]. |
| Γ13 Source-uniform extinction | No-go (PW-B) | — | [L]. |
| Γ14 Local counterterm selection | No-go | — | [L]. |
| Γ15 FE twins | Partially solved | sub | [L]. |
| Γ16 Selection–sign gap | Sharpened | RH | [L]. |
| Γ17 Scattering recentering | Classified | — | [L]. |
| Γ18 Divisor-identity selection | Solved | — | [L]. |
| Γ19 Correspondence algebra over ℤ | Sharpened | RH | Rosati positivity ⇔ orbit Hodge index [L]. |
| Γ20 Window selection | Classified | — | [L]. |
| Γ21 Density selection | No-go | — | [L]. |
| Γ22 Contractive scattering positivity | No-go | — | [L]. |
| Γ23 Weil cone uniqueness | Solved (uniqueness) | — | [L]. |
| Γ24 Mayer reflection positivity | Sharpened | RH | `Q(H)=2Re[WH,WH]`; `D_s≤0`, zero iff `Re s=¼` [L]. |
| Γ25 Two reflection centres | Partially solved | — | [L/K]. |
| Γ26 Resonant-state selectors | No-go | — | [L]. |
| Γ27 Tate counts as selector | No-go | — | [L]. |
| Γ28 Frobenius inside the window algebra | No-go | — | [L]. |
| Γ29 Linear Serre–Krein identification | No-go | — | [L]. |
| Γ30 Completed Tate family | Classified | — | [L]. |
| Γ31 Degeneration type over `𝔽_q` | Solved (calibration) | — | [L]. |
| Γ32 Hecke-equivariant completion | Solved (identity) | identity | [L]. |
| Γ33 Euler rigidity in the Selberg class | Solved | — | Degree one is `L(s+iθ,χ)` [K/L]. |
| Γ34 Hecke cones and periods | Solved | — | [L]. |
| Γ35 Beurling and Hamburger rigidity | Classified | — | [L]. |
| Γ36 Identification by the explicit formula | Solved (sign-free) | sub | [L]. |
| Γ37 Euler columns | Classified | — | [L]. |
| Γ38 Retained Hecke channel | Classified | — | [L/K]. |
| Γ39 Blindness = density aperture | Solved | — | [L]. |
| Γ40 Positivity certifies thin configurations | Solved | — | [L]. |
| Γ41 Fakes at their first prime | Solved | — | [L]. |
| Γ42 Legendre-invariant reality | Solved (identity) | identity | [L]. |
| Γ43 Collide or repel over `𝔽_q` | Solved (calibration) | — | [L]. |
| Γ44 Second-order coalescent precision | Solved | sub | [L]. |
| Γ45 Domination as a selector | No-go (density-only) | — | [L]. |
| Γ46 Reality at near-coincidences | Partially solved | RH | FE pair at depth `δ` forces `|ζ(½+iγ)|≪|γ|^{33/200+ε}δ²` [L]. |
| Γ47 Sharp location from positivity | Solved (receiver) | sub | [L]. |
| Γ48 Diophantine repulsion of carriers | Classified | — | [L]. |
| Γ49 Exceptional values of ζ | Partially solved | indep. | `0∉E` open [L]. |
| Γ50 Weighted image vs atom count | No-go | — | [L]. |
| Γ51 Near-coincidence dictionary | Solved (identity) | — | [L]. |
| Γ52 Canonical repair | Sharpened | RH | [L]. |
| Γ53 Reflection-odd co-shift | Sharpened | RH | [L]. |
| Γ54 Newton source-margin coverage | Sharpened | RH | [L]. |
| Γ55 Positive mimic = window sign | Solved (identity) | RH | [L]. |
| Γ56 Exact extremal blind test | Solved (existence) | indep. | [L]. |
| Γ57 Boundary norm of the Mayer carrier | Solved | sub | [L]. |
| Γ58 Spectral-determinant reflection | No-go | — | [L]. |
| Γ59 Reach of unitary positivity | Classified | — | [D]. |
| Γ60 Theta–Eisenstein identification | Solved (identity) | identity | [L]. |
| Γ61 Inner factor | Solved (identity) | RH | [L]. |
| Γ62 Hecke dispersion | Sharpened | RH | [L]. |
| Γ63 Poisson-extended Hecke positivity | No-go | — | [L]. |
| Γ64 Cross-zero Gram law | Solved (identity) | identity | [L]. |
| Γ65 Cutoff line law | Solved (edge) | sub | [L]. |
| Γ66 Scattering Blaschke product | Solved | — | [L]. |
| Γ67 Abscissa split | Solved (identity) | RH | Purity ⇔ ZAL ∧ AAL for every zero configuration; RH ⇔ ZAL ∧ AAL ⇔ ZAL ∧ zero-disc weak recurrence ⇔ ZAL ∧ thick `O(√X)` prime deviation; `qRH ∨ AAL` [L/D]. |
| Γ68 Asymptotic abscissa law | Open | sub | ¬AAL ⇔ isolated top ⇔ finite top and bottom layers at the same heights, all higher zeros in `|Re z−½|≤h` ⇔ `ψ(x)−x=x^βT(log x)+O(x^{β−η})` [L]. |
| Γ69 AAL producers | Partially solved | sub | Not-attained top; bounded lag on a progression; Abel-density-zero lag excursions; polar ground energy; one prime-window grid; log-dense integer lag; twisted plateaux; JAS dressed, typical and shell positivity; bounded towers; one bounded cone; weak recurrence; infinitely many zeros near each right zero; slow aligned returns on right discs; thick lag bound at one base; thick prime deviation `O(X^{½+a})` ∀`a>0` [L]. Each retains its source bound. |
| Γ70 Zero–one law of recurrence | Classified | — | [L]. |
| Γ71 Pair recurrence | Partially solved | sub | [L]. |
| Γ72 Returns at a zero | Classified | — | Rare and threshold-quantized [L]. |
| Γ73 One-off countermodels | No-go (positive data) | — | Continuous Beurling systems with one off-line pair (rational zeta continuing across `Re s=½`); integer-norm systems with linear counting; rational-prime Euler products with multiplicative linear counting [L]. Calibration battery: the integer-norm one-off satisfies ZAL and violates AAL [L]. |
| Γ74 FE-defect rigidity | Partially solved | sub | Defect `≤1/6400` forces rational primes [L]. |
| Γ75 Inner field of a column | Solved | identity | [L]. |
| Γ76 Endpoint characters | Sharpened | RH | [L]. |
| Γ77 Tensor weights and compression | No-go (stated classes) | — | [L]. |
| Γ78 Global trace on a family | Partially solved | RH | [L]. |
| Γ79 Displacement | Classified | — | [L]. |
| Γ80 Finite oscillation | Solved | sub | [L]. |
| Γ81 Dilation annihilation | Solved (identity) | sub | ¬AAL ⇔ two-prime annihilation of `ψ` [L]. |
| Γ82 Rightmost-zero jets | Solved | sub | Off-diagonal `→m²` [L]. |
| Γ83 Returns are prime returns | Solved | — | [L]. |
| Γ84 Isolation of ζ | Solved | identity | [L]. |
| Γ85 Rational zero relocation | No-go (Bohr) | — | Positivity form: Γ135. |
| Γ86 Modular horizon | Solved (exact solution) | RH (universal damping) | Exterior = chart of the Rindler wedge of AdS₄, black hole = quotient by `SL₂(ℤ)` [L]. |
| Γ87 Raw echo decay | No-go | — | [L]. |
| Γ88 Near-arithmetic ladders | No-go | — | [L]. |
| Γ89 Blindness of physical positivity | Classified | — | Schur, KMS, reflection, `C*` positivity hold on every black hole; internal modular conjugation reduces to the Hilbert adjoint (Γ148) [L]. |
| Γ90 Maximal-angle zero | Classified | RH | [L]. |
| Γ91 Lefschetz ratios | Solved | RH | [L]. |
| Γ92 Fake black holes | Solved | — | [L]. |
| Γ93 Hecke rigidity on resonances | Solved | — | [L]. |
| Γ94 Cuspidal sector | Classified | — | [L]. |
| Γ95 Krein flux law | Solved (identity) | RH (sign) | [L]. |
| Γ96 Count law | Solved | every genus (hyperelliptic) | [L]. |
| Γ97 Integer probes | Sharpened | RH | RH ⇔ `Q(a)≥0` on `ℤ^N` [L]. |
| Γ98 Manin's Hasse | Solved | genus one; bielliptic genus two | [L]. |
| Γ99 Throat | Solved | — | [L]. |
| Γ100 Rank barrier | Solved | — | A compact probe excites infinitely many modes over ℤ [L]. |
| Γ101 One clock | Solved | — | Hecke at `p` = modular time shift `log p` [L]. |
| Γ102 KMS midpoint | Classified | — | [L]. |
| Γ103 Horocycle is the wave | Solved | graph | [L]. |
| Γ104 Bulk log-mean | Solved | sub | [L]. |
| Γ105 Transport count | Classified | — | [L]. |
| Γ106 Missing input of transport | Solved (receiver) | sub | Bounded return at each zero ⇒ AAL [L]. |
| Γ107 Effective transport | Solved | sub | Discs crossing `Re s=½` force power growth; right-edge discs carry AAL [L]. |
| Γ108 Tail at a zero | Solved | — | [L]. |
| Γ109 Limit map | Solved | — | [L]. |
| Γ110 Hull over the torus | Classified | RH | Liouville fibre extends ⇔ RH [L]. |
| Γ111 Stieltjes sign | Solved (necessary law) | — | [L]. |
| Γ112 Rotated relation classes | No-go (coefficient growth) | — | [L]. |
| Γ113 Naive height, five currencies | Sharpened | RH | [L]. |
| Γ114 Dilation quotient | Sharpened | RH | [L]. |
| Γ115 The tail of a return carries the zero | Solved | sub | [L]. |
| Γ116 Head frozen at its resolution | Solved | — | [L]. |
| Γ117 Trivial zeros of a cusp | Solved | graph | [L]. |
| Γ118 Genus two does not force damping | No-go | — | FE, flux, unitarity, Hecke, integrality and the first-level count leave damping open [L]. |
| Γ119 Natural boundary of the hull | Solved | — | [L]. |
| Γ120 Extremal law has a model | No-go | — | [L]. |
| Γ121 Horocycle rate = zero-free region | Solved (Zagier) | RH (rate `¾`); ≥qRH (interior) | Rate `y^{½+δ−ε}` for every profile ⇔ zero-free `Re ρ≤1−2δ`; RH ⇔ `y^{¾−ε}`; smooth profiles and smoothed Farey counts thermalize unconditionally at `y^{½}exp(−√(−log y))`, hence `o(y^{½})` and every logarithmic power past `y^{½}`; ceiling `y^{¾}` [L]. |
| Γ122 Lax–Phillips decay on the modular surface | Solved (identity) | RH | RH ⇔ every resonant mode decays at `e^{−t/4}` [L]. |
| Γ123 Recurrence dichotomy of the tail | Solved | sub | [L]. |
| Γ124 One-offs stop at the critical line | Classified | method | Discrete one-offs blow up at `s=½`; FE defect `≤1/6400` forces the rational primes; continuous one-offs continue but carry no FE (Γ145) [L/D]. |
| Γ125 Count law of every hyperelliptic curve | Solved | every genus | RH and Hasse–Weil over every extension; tower count law ⇔ a crude bound at every level [L]. |
| Γ126 Born rule | Classified | — | Nondegenerate ⇒ partner law (FE); positive ⇒ damping [L]. |
| Γ127 Boundary algebra of a black hole | Classified | — | Positive state for the partner involution iff damped; `C*` on every black hole [L]. |
| Γ128 Linear counts | No-go | — | Additive counts with the parallelogram law vanish [L]. |
| Γ129 Hecke supplies conservation | No-go (Hecke as law) | — | [L]. |
| Γ130 Second place of a Hecke triangle group | Classified | — | Non-arithmetic `G_q` count negatively at a second place [L; Takeuchi C]. |
| Γ131 Tate limit of a count over ℤ | Sharpened | RH | `Q(a)=Σa_ma_nC(log(m/n))`; RH ⇔ `Q` is the Tate limit of an `ℕ`-count; Tate principle in both directions; Hecke at `p` an exact isometry of `Q` [L]. The content is a count defined without `Q` (Γ154). |
| Γ132 Narain AdS₃ source | Sharpened | RH (rate `¾`) | Literal partition, modular invariance, Mellin continuation retaining every arithmetic pole; central orders classified with one exceptional height `Y*=exp(2−4Re ξ′(1))`; boundary moment jets; remainder `≤Cy^{½}exp(−L·vkWidth(L)/128)`; `O(y^{¾−ε})` ⇒ RH; exponents `>¾` impossible [L]. |
| Γ133 Cusp channel of the horizon | Solved (classical theory) | — | Maass cusp forms, discrete spectrum, `N(Λ)≍Λ`; Rankin–Selberg continuation; Rankin's bound `|ρ(n)|≤C|n|^{½−δ}`; Rankin–Selberg Euler product of normalized Hecke sequences, diagonal `ζ(s)L(Sym²g,s)/ζ(2s)` [L]; eigenform series and RS integral as that product on `Re s>2` [S]. |
| Γ134 Cusp-energy horocycle rate | Sharpened | RH (with noncancellation) | Rate `y^α` ⇒ `Λ_g(ρ/2)=0` at every zero with `Re ρ>2−2α` [L]. |
| Γ135 Relocation is seen at the first integer gap | Classified | — | Rational surgery on ζ's zeros cannot preserve positivity of the density [L]. |
| Γ136 AAL is eventual-to-global | Classified | sub | AAL ⇔ eventual right bounds are global at every `σ≥½`; symmetric shifts preserve AAL; an AAL proof may use the FE only as an involution [L]. |
| Γ137 Positive Hecke annihilators | No-go (positivity as zero exclusion) | — | Any finite set of zeros annihilated by a nonnegative polynomial in `T₂,T₃` with constant 1; constant-mode value `>2` [L]. |
| Γ138 Prime pairs retain the prime-power field | Solved (identity) | — | [L]. |
| Γ139 Principal series at the boundary | Classified | — | [L]. |
| Γ140 No asymptotic or local property decides the finite stratum | No-go (scale-separated inputs) | — | A property depending only on zeros above some height (densities, pair statistics, gaps, count growth), or only on zeros below a fixed height (finite verification), that holds on a pure configuration holds on a configuration with ZAL and ¬AAL at `h=0` (add one reflection pair) [L]. An input for B13 or AAL must couple both scales. |
| Γ141 The FE admits every finite layer | No-go | — | `cosh(s−½)·Π_{q∈Q}(s−q)(s−q̄)(s−1+q)(s−1+q̄)`: entire, order one, FE, reality, other zeros critical; ZAL holds, AAL fails [L]. On tower level sums the FE acts only as `S(−ν)=conj S(ν)` [L]. An exclusion must use the Dirichlet series. |
| Γ142 AAL is zero transport and tail transport | Classified | sub | AAL ⇔ every right zero has, ∀ε, T, a zero with `Re>Re ρ−ε`, `|Im|>T`; ⇔ every right zero transports to arbitrarily high points where every Euler tail vanishes and `|ζ−E_y|=|E_y|≥Π_{p≤y}(1+p^{−σ})^{−1}`; such heights are tail-bad at every cut; events from returns have density zero [L]. |
| Γ143 Free AAL | Solved (classes) | — | Vertically recurrent configurations; zero sets of exponential polynomials (finite Dirichlet polynomials); curves; configurations with a vertical period; strip almost periodic functions (zeros recur with bounded gaps); Dirichlet series uniformly approximated by partial sums on closed strips [L]. Almost periodicity at large height alone is insufficient (the rational one-off tends to 1 vertically and violates AAL) [L]. |
| Γ144 The curve proof splits at the abscissa law | Classified | — | For every curve datum in the strip: AAL holds; crude count at every level ⇔ ZAL ⇔ purity ⇔ unitarity. Stepanov and power sums sit inside ZAL; AAL is the periodicity of the Frobenius [L]. |
| Γ145 Critical-line firewall | No-go | — | Half-plane AAL fails with a finite nonempty top layer for continuous Beurling systems (continuing across `Re s=½`), integer-norm and rational-prime Euler products with linear counting, and one reflection pair; AAL of ζ is invariant under `ξ(s+a)ξ(s−a)` [L]. The reflection keeps heights; an FE-based input must turn the FE into transport in height. |
| Γ146 Towers of ζ | Sharpened | sub | ¬AAL ⇒ ∃ exceptional rank `k` and `a>0`: at every base `ℓ`, every window of `k` levels eventually contains `|Φ(νℓ)|>Ce^{aνℓ}`; a single top pair `Θ±iγ` gives exceptional rank 1 at base `π/γ`, and the lag is large at every level [L]. |
| Γ147 Partial returns | Classified | — | Relative approximation on all but a short arc: a zero in the disc (carried by every Euler tail) or an exponentially deep relative small value on the omitted arc; an Euler head approximating a central zero on all but angle `δ` needs logarithmic prime mass `≳1/δ`, hence `≳log|τ|` at `δ≤1/log(2+|τ|)` [L]. |
| Γ148 Modular conjugation is not the partner involution | No-go (internal); Sharpened | RH | Right AdS₄ wedge strictly spacelike from every `SL₂(ℤ)`-image of the left wedge; the boost-commuting wedge exchange fixes cusp height; KMS period `2π` against `1`; `GL₂(ℤ)` symmetries fix pseudo-Eisenstein series; Tomita central collapse (`Z,JZJ∈M` ⇒ `Z` central, `JZJ=Z*`, pairing `‖ZΩ‖²`); graph partner standard forms iff `t²≤4q`; RH ⇔ a standard form with rational dilations, `JU(r)J=U(r^{−1})`, natural-cone form on integer sources `Q` (or Tate limit `Q`) [L]. |
| Γ149 The critical weight | Classified | — | Damping `ρ^{|ν|}` Toeplitz positive; damping lossless (all damped kernels positive ⇒ undamped positive); critical layers Toeplitz positive; for every symmetric `Q` and counterterm `c(δ)→∞`, `Q+c(δ)I` is eventually PSD and renormalizes to `Q` [L]. A count at the critical weight must be a damping of something positive. |
| Γ150 Two half-products | Solved (off-diagonal) | identity | 𝔽₁-zonotope surface: `Γ_m·Γ_n=m+n`; defect `2Σ_k(Σ_{n>k}a_n)²` (Hodge index by counting); cusp channel = first archimedean channel. `Γ_m·Γ_n:=(m+n)−√(mn)W(m,n)=min/(1−(min/max)²)+G(m,n)I(m,n)`: one 𝔽₁-cusp with its even jets plus gcd-twisted torsion on `ℙ¹_ℤ`; every local index `≥0`; zonotope Tate limit is a count [L]. The diagonal `Γ_n²=n(2−2g)`, `g=∞`, is supplied by no half-product. |
| Γ151 Point count of Spec ℤ | Sharpened | RH | `N(n)=Λ(n)+1+1/(n²−1)`, trace `a(n)=n−Λ(n)−1/(n²−1)`; the two-term defect is indefinite at every finite genus for large `n` (atomic graphs have infinite genus); jets = even-sector trace of the dilation of `ℝ` [L]. Smoothed graphs: RH ⇔ Hasse–Weil for every pair of integer degrees (genus `c_B(0)/2`) [S]. |
| Γ152 Carriers of the archimedean place | No-go | — | No metric on `ℙ¹_ℤ` carries the jets (Arakelov pairing = −finite intersection + rank two; jet block on `{2,3,5}×{7,11,13}` nonsingular); toric pairings of coprime orbits depend on `mn`, Weil's on `m/n`; no continuous Hecke kernel (primes are jumps at `log pᵏ`) [L]. |
| Γ153 Torsion energy against the jets | Solved (identity); sign open | RH (sign) | Off the diagonal `W(m,n)=lim_{r→1}(C_∞(m,n)+T̃_r(m,n))`, `T̃_r` positive kernels; `√(mn)C_∞=(m+n)−min/(1−(min/max)²)`, sign-changing (`√2C_∞(1,2)=5/3`, `√20C_∞(4,5)=−19/9`) [L]. The compensation is `C_∞`, not an Arakelov metric. |
| Γ154 Count door of a curve and of ℤ | Classified | RH | Curves: integral CS defect is the Tate limit of a count on every span iff unitary; on true hyperelliptic curves the defect of every integral class is a natural number (an integer polynomial in `q` and the point counts), exactly homogeneous [L]. Over ℤ every ingredient except the count is present [L/D]. |

## Scoped no-gos and surviving replacements

| Boundary | Exact scope and survivor |
|---|---|
| KR-TOR / KR-UCF / KR-R1 | Retired labels, not proved kills. BAG transfer closed (Γ1); PA Hermite-contour receiver (Σ73); TG Gaussian-passage receiver (Σ80). |
| Scale-separated AAL inputs | Asymptotic (above a height) and local-below properties cannot decide B13 or AAL (Γ140). Survivor: inputs defined by the Dirichlet series at all scales — prime-side bounds on thick sets of scales (Π114), windows, transport events. |
| FE and analytic shape as AAL inputs | FE + order one + reality admit every finite layer (Γ141); the reflection keeps heights (Γ145). Survivor: the FE converted into vertical transport (B112). |
| Positive Euler products, linear counting, continuation | Carry finite top layers (Γ73, Γ145, Π102). Survivor: Euler product and FE together (no known model with a finite layer has both). |
| Density statements on levels | Density `1−1/k` sets do not self-improve (Π112). Survivor: thick sets, including every density-one set (Π113, Π114). |
| Elimination without well-foundedness | Wolff configurations cancel at every level (Π113). Survivor: elimination gives AAL on thick sets; RH needs ZAL in addition. |
| Exact Frobenius over ℤ | No common exact return of two primes (Π115). Survivor: approximate forced vanishing at returns, controlled by the `J`-th exponential tail. |
| Internal modular conjugation | Tomita central collapse; geometric wedge involution fixes cusp height (Γ148). Survivor: standard forms whose dilations are not internal; the RH-equivalent standard-form criterion. |
| Renormalized counts | Renormalization carries no sign (Γ149); renormalized torsion limits indefinite under every finite constraint (Π108). Survivor: damping presentations (B88). |
| Metrics and kernels for the archimedean place | No metric on `ℙ¹_ℤ`, no toric Green function, no continuous Hecke kernel (Γ152). Survivor: the archimedean compensation `C_∞` with its explicit sign pattern (Γ153). |
| Finite-genus atomic Frobenius graphs | Every finite genus fails the two-term Hasse–Weil test (Γ151). Survivor: smoothed graphs, whose Hasse–Weil test is RH. |
| Torsion compensation | Logarithmic diagonal compensation exists exactly above exponent 2 (Π118); compensates torsion only. |
| Completed prime boundary | Closed extension exactly on `2Re s+δ>1`; vertical gauges unitary (Π117). |
| Fixed-point localization | Maps homotopic to the identity fix exactly the primes, with local indices unbounded below (Π119); the core's Euler characteristic is `M(N)+#primes(N/2,N]` (Π107). Survivor: signed or relative localization (B106). |
| Persistence | Classified and `s`-independent (Π106). |
| Narain remainder past `¾` | Excluded; `¾` is RH (Γ132). |
| Linear horizon counts | Never the count law (Γ128). |
| Hecke at a second place | Conservation only; non-arithmetic triangle groups fail (Γ129, Γ130). |
| Positive annihilators | Kill any finite zero set at any multiplicity; harmonic packets cost mass `≥m`; accuracy on the right forces growth on the left (Γ137, Π102). |
| Rational zero relocation | Detected by first-gap negativity (Γ135). |
| Low packet at a fixed ratio | Payment at one ratio is a window rung; at every ratio it is RH (Σ130); below `W` the pole channel decides (Σ135). |
| Theta fixed heads and compact cores | Fail; the adaptive head survives with leading term `|ζ(½+ib)|²` (Σ98, Σ133). |
| Sharp horizon sources | RH rate ⇔ RH ∧ Möbius × circle remainder (Π109). |
| Extremal-angle contradiction | Polynomial model (Γ120). |
| Bounded count as selector | Signed generators admit a new zero (Π100). |

## Bridges

| Bridge | Anchor |
|---|---|
| Window index counts distinct right zeros; `sup_dN_d` counts off-line multiplicity; bounded `N_d` gives finite support only | AHD, CWS, FFP [L] |
| RH ⇔ `a*(ζ)=⊤` ⇔ `1∈ℋ(c)` ∀c ⇔ `λ*(c)→0` ⇔ no finite contact ⇔ `Ψ` locally bounded ⇔ spline-orbit Hasse–Weil | WVL, FADF, CHT, CSTW, AIF, AOG [L] |
| Critical curve = window + pole channel: `R_c≤R_pole=R_high=W`; below `W` the pole channel decides | AHD, CACT [L/S] |
| Aperture ⇄ ratio exchange below the onset | AHD [L] |
| Window sign ⇔ two-site signs ⇔ reflection band ⇔ smoothed Frobenius pairs | GWZ, SWC, SRT, SOSZ [L/S] |
| Window positivity ⇒ PNT with exponent `5/6` on the window's range | CHT [L] |
| Theta adaptive head ↔ `|ζ(½+ib)|²` | CAF, TCS, AHD [L] |
| RH ⇔ ZAL ∧ AAL (every configuration) ⇔ ZAL ∧ thick `O(√X)`; AAL ⇔ zero transport ⇔ tail transport | ZCG, IWT, TAPO [L] |
| ¬AAL ⇔ isolated top ⇔ finite oscillation of `ψ(x)−x` ⇔ two-prime dilation annihilation ⇔ syndetic lag excursions at every base | ZCG, RHTower, IWT [L] |
| Curve template split: AAL free by periodicity; crude count ⇔ ZAL ⇔ purity; elimination at infinite rank on thick sets | ZCG, IWT [L] |
| Firewall: positivity, Euler products, linear counting, continuation and reflection symmetry each carry finite layers; FE admits every finite layer | APD, IWT [L] |
| Count law = Born rule (FE) + positivity (damping); RH ⇔ `Q` is the Tate limit of a count; on curves the defect is a point count | CTH, ASH [L] |
| Off-diagonal Weil = 𝔽₁-cusp with jets + torsion on `ℙ¹_ℤ` = `C_∞` + Abel limit of positive torsion energy | SOSZ, AE [L] |
| Damping lossless; renormalization signless | IWT [L] |
| RH ⇔ standard form with partner modular conjugation; internal realizations collapse | CTH [L] |
| Horocycle rate ⇔ zero-free region ⇔ Farey count rate ⇔ pulse ringdown ⇔ Lax–Phillips decay; unconditional `y^{½}exp(−√(−log y))`; sharp shells ⇔ RH ∧ Möbius–circle | BHR, CTH [L] |
| Narain AdS₃ remainder = VK saving; `¾` ⇒ RH | ASH ModularBootstrap [L] |
| Cusp energy rate reads `Λ_g(ρ/2)`; RS Euler product = `ζ(s)L(Sym²g,s)/ζ(2s)` | BHR [L/S] |
| Zeros of ζ = zeros of every Euler tail; partial returns transport or create small values | TAPO, HTG [L] |
| Necessary mollifier length = Euler mollifier over primes `≤c log²T`; long mean values = collision counts | APR, IWT [L] |
| Returns freeze smooth Dirichlet polynomials (approximate Frobenius) | IWT [L] |
| `M(N)` = Farey discrepancy = nerve and core Euler characteristics; localization of `χ` to prime vertices | RHTower, HWV, HHAC, RIAC [L] |
| Stepanov over ℤ = integrality + Nair (Chebyshev); Frobenius over `𝔽_q[T]` = factorial stencil of rate 0 | AE, AAD [L] |
| Hecke state on `Aff(ℚ)` PD iff `s≥½`; Bost–Connes states PD for `β>1` | APD [L/S] |

## Strength of the open walls

- **RH:** Σ1, Σ1u, Σ1v (all ratios), Σ2, Σ3a, Σ6 (all ranks), Σ7, Σ8, Σ17, Σ18, Σ19, Σ20, Σ28 (subexponential), Σ30, Σ32, Σ49, Σ56, Σ61, Σ66, Σ67 (all `d`), Σ70 (sign), Σ72 (all orders), Σ73, Σ74, Σ76–80, Σ85, Σ93, Σ101, Σ113, Σ114, Σ122, Σ129, Σ130, Σ133, Π2, Π4, Π11h, Π17, Π23, Π28 (trivial point), Π30, Π36, Π42, Π47–50, Π58, Π59, Π62, Π63, Π66, Π68, Π69, Π78, Π81 (finite energy), Π105, Π114 (with ZAL), Γ1, Γ4, Γ5, Γ8, Γ16, Γ19, Γ24, Γ46, Γ52–54, Γ61, Γ62, Γ76, Γ78, Γ86, Γ90, Γ91, Γ95, Γ97, Γ110, Γ113, Γ114, Γ121 (rate `¾`), Γ122, Γ131, Γ132 (rate `¾`), Γ134 (with B109), Γ148, Γ151, Γ153 (sign), Γ154.
- **≥qRH:** Σ4 (`K_ζ`), Σ28 (exponent `<½`), Π5, Π17 (log stage), Π23 (fixed degree), Π42 (dyadic), Π70 (polynomial rate), Π84 (power saving), Γ121/Γ122/Γ132 (interior exponents), `N_d` bounded, ZAL, inner-field decay.
- **AAL:** Π114 (thick crude count, all `a>0`).
- **sub:** Σ82, Σ1d, Σ1e, Σ1g, Σ1j, Σ1m, Σ1q, Σ1w, Σ6 (each rank), Σ30 (each stage), Σ47, Σ50, Σ70 (rate), Σ72 (band), Σ86, Σ92, Σ94, Σ99, Σ100, Σ116, Σ117, Σ118, Σ131, Π7, Π9, Π11f, Π12, Π22, Π40, Π51–54, Π57, Π65, Π80, Π87, Π90, Π94, Π96, Π103, Γ15, Γ47, Γ57, Γ65, Γ68, Γ69, Γ71, Γ74, Γ104, Γ106, Γ123, Γ136, Γ142, Γ146.
- **method / indep. / beyond RH:** Σ127, Σ135, Σ136, Π16, Π97, Π101, Π109 (beyond RH), Π112, Π113, Π115, Γ49, Γ56, Γ124.
