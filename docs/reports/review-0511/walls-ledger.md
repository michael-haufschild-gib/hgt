# Walls ledger — status quo

Three wall families block every route: **Σ** the critical sign, **Π** precision and production, **Γ**
selection and reflection. All three read one even integer `κ = #` distinct zeros right of the critical line and
one number, the onset aperture `a*(ζ)`: RH ⇔ `κ = 0` ⇔ `a*(ζ) = ⊤`. All three are decided on the two-site
window `{f, f∘R}` of a test and its mirror image, and all three reduce to one sign read in three coordinate
systems.

- **Σ is the sign of every window: a critical, frustrated, signed Hardy inequality.** RH ⇔ the arithmetic
  part `P` is an admissible Hardy term for the archimedean–polar form `H` on every window ⇔ `a*(ζ) = ⊤` [L].
  The multiple `1` is the only one admissible on all windows, and no Hardy weight survives on odd tests [L]:
  the inequality is critical with a unique admissible constant. The certificate format is exact on every
  window (neutral signed theta gauge, shifted ground state), its gauge freedom acting only in the pole direction
  [L]; Perron structure ends at `log ρ` and
  frustration survives every sign gauge [L]; size payment ends before half-width `21/40` [L]. Before contact
  each window is a de Branges space; contact is a kernel blow-up [L].
- **Π is the same sign on the prime side.** `𝒞_m(f) = 𝓗_m(f) − Σ_nΛ(n)n^{−1/2}(f⋆f)(2m − log n)` [L]: the
  band is one smoothed prime count matching the pole square within `W(f)`, identified with every classical
  one-sided count criterion [L]. Production by counts is closed [D]; the inner caps of WD are the generating
  function of the off-line zeros [L]; finite free stability reproduces de Bruijn–Newman criticality [L].
- **Γ is the same sign on the zero side.** Identification is complete: at aperture `λ·½log(T/2π)` the explicit
  formula fixes ζ's zeros up to clusters of diameter `e^{−c log³T}` and reads, inside isolated polynomially
  small clusters, centres, squared gaps and discriminants from finitely many prime-side images [L]. Reality at
  a near-coincidence is the sign of `𝓗 = 4(W₁² − W₀W₂)/W₀²` [L]; FE-pair squared gaps `≥ 0` at every zero ⇔ RH
  [L]. The PM defect has a second expression with the same sign factor [L]. Selection is automatic after
  positivity [L].

Status: **Solved** (the face is a theorem), **Partially solved**, **Sharpened** (open, with its exact form a
theorem), **Open**, **No-go** (the mechanism is refuted), **Classified** (answered by a classification or
identification theorem), **Reduced** (theorem-level equivalent of the wall named). Strength: **RH**, **≥qRH**
(zero-free half-plane or Lindelöf), **sub**, **indep.**, **identity**, **method**. Evidence: `[L]` committed
Lean; `[W]` working-tree Lean; `[P]` pipeline-card paper proof; `[D]` derived here; `[N]` numerical. Window
half-widths `a` or `c`; `c_ψ(t) = W(ψ(· − t), ψ)`; `w_n = Λ(n)n^{−1/2}`; `δ` sliver width `2c − log n` (in
zero statements, the depth `Re ρ − ½`); `ρ³ = ρ + 1`; `a₁ = successorWeilFloorAperture`, `181/500 < a₁ < 181/500 + 5×10⁻⁷`; `a_∞` the limit of the floor-aperture tower.

## Σ — critical sign

| Wall | Status | Strength | Content |
|---|---|---|---|
| Σ1 Weil's sign | Sharpened | RH | RH ⇔ `Q ≥ 0` on every window ⇔ `a*(ζ) = ⊤` ⇔ two-site PD ⇔ band at the centre in both sectors ⇔ Stieltjes moments of jet energies ⇔ lattice Schur parameters in `(−1,1)` ⇔ `R₁ ≡ ⊤` ⇔ `1 ∈ ℋ(c)` ∀c ⇔ `⋂ℋ(c) = {1}` ⇔ every growth step a translation contraction ⇔ two-parameter two-bump family ⇔ Cayley ladders NSD [W] ⇔ Suzuki first variation `≥ 0` ⇔ mollified Jensen stability ⇔ Krein positivity ⇔ prime-blind positivity [L]. |
| Σ1a Critical overlap and receivers | Solved | — | `c*_N ≍ L(log L)²`; tilted-spline and unit-bump receivers; one Beurling profile realizes every finite rational Gram [L]. |
| Σ1b Subcritical regime | Solved | sub | Complete matrix PD for `1 ≤ c ≤ (log N)^α`, `α < 1/8` [L]. |
| Σ1c Joint shell–pole payment | Solved | sub | Prime-successor edges pay nonconstant packet mass [L]. |
| Σ1d General profiles | Partially solved | sub | Spans `θ < 1/1080` through `b_φ log log N`; polylog spans through `K log log N` [L]. |
| Σ1e Conductor barrier | Partially solved | sub | Count form uniform for `m = o(c)`; low block `≤ ⌊(log N)^{13/32}⌋` keeps half its diagonal plus the polar part [L]. |
| Σ1f Defect-only confinement | No-go | — | `Q < 2^k` witnesses [L]. |
| Σ1g Haar / Gamma graph | Partially solved | sub | All-detail prime–pole cancellation; index `≤ R + A`; growing Euler heads unbounded [L]. |
| Σ1h Smooth logarithmic profile | Solved (to `ε₀c*`) | sub | Positive to `ε₀L(log L)²` [L]. |
| Σ1i Second order on horizon blocks | Classified | — | `κQ(H) + (βJ/K)∫e^{−(β+1)y}H²` [L]. |
| Σ1j Critical-curve decomposition | Partially solved | sub | Ramanujan, periodic, trigonometric, primitive characters; characters graded by conductor and parity [L/W], with `L(s, ψ̄₁ψ₂)` coupling within grades; joint periodic windows keep the mass Gram; frequency pole of order `β+1` with untwisted finite part [L]. Open: moving frequencies. |
| Σ1k Whole space at one critical multiple | Solved | sub | PD at `c ≤ 2K₀(log N)^{1/8}`; one aperture-independent multiple across every prime entry [L]. |
| Σ1l Window threshold | Reduced (to Σ56) | RH | `R₁(A) = ⊤ ⇔ A/2 ≤ a*(ζ)`; `R₁ = ⊤` for `A ≤ 2·weilFloorApertureTower k` (every `k`), every critical pencil positive there [L]. |
| Σ1m Polarization inheritance | Partially solved | sub | Twisted sectors with positive scalar second order; short windows; cosh hyperplane [L]. |
| Σ1n Bulk and growing overlap | Classified | — | Bulk below the grid reads only the pole [L]. |
| Σ1o Aperture-independent weighted floor | Solved (size-only) | — | `Q(H) ≥ −C(p)∫e^{−pu}H²`, `p > 1` [L]. |
| Σ1p Terminal windows | Classified | — | Polar source with nontrivial kernel; long-index cancellation on near rows and logarithmic annuli [L]. |
| Σ1q Receiving charges | Classified | — | Capacity `log log N + O(1)`; simultaneous receiving vectors on fixed and growing mode sets read at `1/80` with vanishing physical energy; literal three-range, short-row, Gram and tower bounds; physical energy does not control charge [L]. |
| Σ1r Conductor packets and correctors | Classified | — | Terminal sources concentrate at the pole; correctors cannot improve zero-source windows [L]. |
| Σ2 Edge, zero modes, hard Lefschetz | Sharpened | RH | RH ⇔ HL on the PSD locus; zero modes radical, two-site [L]; Hodge index = Metzler sign of the Cayley ladder = Li positivity [W]. |
| Σ2a Interior-gap continuation | No-go | — | `κ(d) = 1_{3∣d}` [L]. |
| Σ2b Edge singularity | Classified | — | No smooth eigenfunction, constrained ground state or capacity maximizer [L]. |
| Σ3 Stars and dilation monodromy | Partially solved | — / RH | Stars isometric; squarefree prime complex ≃ wedge of spheres over odd squarefree `N/2 < m ≤ N` [L]. |
| Σ3a Coprime stratum | Sharpened | RH | gcd stratification; Redheffer `det = M(N)` = reduced Euler characteristic up to sign [L]. |
| Σ4 Finite index / heat count | Sharpened | ≥qRH (`K_ζ`); RH (`K_ζ⊠K_ζ`) | `κ < ∞` ⇒ Lindelöf; RH ⇔ index `0`; window index counts critical lengths, locally finite [L]. |
| Σ5 Collision quantum / window integer | Reduced (to Π17) | RH | Index `0` ⇔ Wiener–Hopf invertibility [L]. |
| Σ6 Rank / degree uniformity | Partially solved | RH | Rank 9 PD for `0 < a < ½`; complete fifth even tails PD from scale 3; fifth even section strict from `q ≥ 5`; truncated quartic flux preserves every mixed entry, positive from `q ≥ 7` at every aperture, fails at scale 6; fixed load fails at scales 6 and 8, untruncated quartic at 32 (capacities exact); every finite native shifted Hankel matrix PD on a cofinal ray [L]. Open: all ranks. |
| Σ7 Window Markov capacity | Sharpened | RH | RH ⇔ `R ≤ ½` on the odd sector [L]. |
| Σ8 Realization | Sharpened | RH | `ℓ²(zeros)` realization ⇔ RH; no finite-rank realization [L]. |
| Σ9 Explicit image / resolvent | Partially solved | RH in strip | Depth identity for `σ > 1` [L]. |
| Σ10 Local signatures and gluing | Solved | — | `κ(φ_c) = κ + 1` [L]. |
| Σ11 Product-formula gluing of the pole | Classified | — | Local poles add squares [L]. |
| Σ12 Running counterterm | Solved | — | `log N − γ` cancels the prime diagonal [L]. |
| Σ13 Tensor amplification | No-go | — | `K_ζ^n` PD ⇔ RH [L]. |
| Σ14 Deformation to a positive model | No-go as free input | — | Crossing-free path ⇔ PD [L]. |
| Σ15 Separable assemblies | Classified (no-go) | — | Blind when truncated, non-convergent when untruncated [L]. |
| Σ16 Prime–pole coherence | Solved (identity) | — | Complete form = jump + incidence − shell + diagonal + boundary [L]. |
| Σ17 Inter-tower coupling | Sharpened | RH | Bounded damped coupling ⇔ RH; the damped coupling is an arithmetic heat average of the complete Weil functional [L]. |
| Σ18 Exact SOS on a two-prime lattice | Open | RH | Generic Hecke orbit carries the full Hodge defect [L]. |
| Σ19 Rank-one intertwining coefficient | Sharpened | RH | `κ_Hodge = #` band poles of `Λ(s)/Λ(s+1)` [L]. |
| Σ20 Scheduled prime sums | Open (FU, CFC, RP, EGC, FEL); Reduced to Σ1 (SZ, LI) | RH | Suzuki first variation = complete Weil energy; actual-clock Li primitive escapes off RH [L/W]. |
| Σ21 Extension / carrier | Classified | — | Escape, mixing, height decay ⇒ `κ ∈ {0, ∞}` [L]. |
| Σ22 Lefschetz operators | Classified | — | Overlap-flow HL on the HR locus is RH [L]. |
| Σ23 Connected links | No-go | — | Links disconnected [L]. |
| Σ24 Finite divisor | Solved | — | Coercive off `i/2` [L]. |
| Σ25 Semilocal and trace carriers | No-go | — | No `{∞,p}` positive carrier [L]. |
| Σ26 Approximation by RH-true objects | Classified | — | Closure class Laguerre–Pólya [L/D]. |
| Σ27 Window stages | Partially solved | sub (each stage); RH (all) | Floors `(1/20000)/2^k` on a strictly increasing tower of apertures from `a₁` (limit `a_∞`, steps `≍ e^{−C·2^k}`); multi-prime dilation modulus on every `[−R, R]`; first stage opens positive [L]. No sign theorem on `c ∈ (a_∞, log 2)` [N margins `1.5×10⁻⁵`, `5.6×10⁻⁸` at `½log 3`; `≈ 2×10⁻⁴` odd unit window]. Stages below half-width `4` carry no zero information [D]. |
| Σ28 Window negativity budget | Sharpened | ≥qRH (exponent `< ½`); RH (subexponential) | Ground-energy floor `−Ce^{2σA}` ⇔ zero width `≤ σ` [L]. |
| Σ29 Low-frequency localization | Solved | — | Negativity only at the poles and below `τ₀(a)` [L]. |
| Σ30 The stage step | Reduced | RH (as induction); each stage sub | Composite stages carry no fold; prime-power stages ⇔ stage form + signed fold energy pays the entering end mass; single-prime transport for all `A` ⇔ RH; unconditional transport across `p = 2` at `A₀ = 2·enlarged − log 2` [L]. |
| Σ31 Positivity across dimension zero | Classified | equivalent to Σ1 | Bare domination ⇔ `Q ≥ 0` [L/D]. |
| Σ32 Prime-blind positivity / calibration | Sharpened | RH | Weil cone `{Λ}`; calibration spaces `𝒜(c)` convex, cylinders beyond `e^{2c}`, every entering coordinate bounded, stage fibre a compact interval; real tests decide; RH ⇔ every `𝒜(c)` nonempty [L]; bands and best margins in summary 1.15 [N]. |
| Σ33 Tate positivity horizon | Classified | — | Positive Tate dimensions `[0, κ(A)]`, `κ(A) ≤ log(1+2√2)/log 2` once ratio 2 fits, `κ(A) → 0`; exact horizons through `log(81/16)` [L]. |
| Σ34 Canonical-degree horizon | Classified | — | Soft deformations paid by counts have horizon `≍ e^{−A/2}` [L/D]. |
| Σ35 Canonical system of the tower | Partially solved | identity | Lattice Levinson recursion; continuum margins; parity split [L]; **de Branges chain before contact**: complete Weil spaces, explicit Hermite–Biehler function with Christoffel–Darboux identity, unitary zero-moving, antiunitary conjugation, isometric inclusions; kernel blow-up at finite contact [L]. Hamiltonian not constructed. |
| Σ36 Rational Hecke-graph reading | Solved (identity) | — | Correlation-form window positivity ⇔ positivity of every finite rational Hecke graph of smaller spread; finite templates control spreads with finite Hecke orbits [L]. |
| Σ37 Lattice canonical system | Solved (identity) | — | Window ⇔ its lattices [L]. |
| Σ38 Two-site decision | Classified | — | RH ⇔ two-site PD; two real parameters `(γ, v)` decide the line [L]. |
| Σ39 Trivial-divisor transmission | Solved (identity) | — | Collar Hankel form, inertia `(1, ∞)` [L]. |
| Σ40 Degenerations are curves | Classified | — | Degenerate lattice windows are finite curves [L]. |
| Σ41 Aperture–depth duality | Classified | — | Fall rate of the ground energy = zero width; unshielded clusters excluded to doubly-exponential height; shielded depth-`1/a` zeros hide above single-exponential height; height non-locality [L]. Explicit: positivity at level `a` ⇒ `|β − ½| < 10⁶exp(−a/(480000 log(|γ|+3)))` for `|γ| ≥ 102`; `N(t, t+1] ≤ 240 log(|t|+3)` [L]. |
| Σ42 Markov, sign-blind and variance-free ground states | No-go | — | Markov part dies at `e^{−3/4}`; variance-dropped certificates fail for `c > 273/400`; prime `3` as a collar potential fails for `c ≥ 287/500` [L]. |
| Σ43 Pole-charged ground-state calculus | Solved (identity) | — | `Ẑ(Φωu) = J_{Φω}(u) + ∫u²ω𝒢_S(ω) + 2V_s − 2V_c` [L]. |
| Σ44 Collar locality of the kick | Classified | — | Collar ratio `2w_ne^h` sharp; outward edge `w_ne^h/2` [L/D]. |
| Σ45 Reflection pairs and parity sectors | Solved (identity) | — | `W(f ± f∘R) = 2W(f) ± 2𝒞_m(f)`; `W(f) − |𝒞_m(f)| = ½min(W(G₊), W(G₋))`; coupling truncates to `n ≤ e^{2c}`; floor `1/8000` through `enlarged` [L]. |
| Σ46 Frustration of the odd sector | Classified | — | Frozen odd form Markov, kick anti-Markov; odd light cone positive [L]. |
| Σ47 Odd unit window | Open | sub | Positivity ⇔ `w₂ ∈ unitBandWeights` (an interval) ⇔ Markov–Hankel inequality on `[−½, 0]`; margin `≈ 2×10⁻⁴` [L/N]. |
| Σ48 Criticality | Classified | — | Every exact reading sits on a zero-slack boundary; the Hardy form admits no Hardy weight on odd tests; only the multiple `1` is admissible on every window [L/D]. |
| Σ49 Reality by continuation | Sharpened | RH | Reality lost only through collision; RH ⇔ every zero of `H_t` simple ∀t > 0 ⇔ `Λ_X = 0` ∀X ⇔ FE-pair squared gaps `≥ 0`; `Λ_X ≤ (6600/9991 + ε)/log X`; saddle at `½/log(X/2π)`; pair models collide below every scale [L]. Open: collision exclusion on `(0, ½/log X]`. |
| Σ50 Below `log 4` | Sharpened | sub | Positivity ⇔ `(Λ(2)/√2, Λ(3)/√3) ∈ belowLogFourBandWeights c` (convex, compact after `½log 3`) ⇔ Hodge index ⇔ Künneth effectivity ⇔ `R₁(2c) = ⊤` ⇔ `1 ∈ ℋ(c)` [L]. Open: membership of the arithmetic point. |
| Σ51 Sectors as moment problems | Solved (identity) | — | Even ⇔ Hamburger, odd ⇔ shifted Hamburger, window ⇔ Stieltjes [L]. |
| Σ52 Prime-weight confinement and soft entry | Solved (sharp) | — | Each entering weight bounded; stage fibre a compact interval; outer law `|λ(n₀)| ≤ √n₀(log(1/δ) + B)`, inner radius `√n₀η(½log(1/δ) − ¼)`; beyond the sliver both bounds bounded [L]. |
| Σ53 Size versus sign of the kicks | Classified | — | Summed edge law `|P_μ| ≤ E_c(μ)𝒥`; size certificates die at `E_c ≥ 1`; for ζ the unique crossing is `c* ∈ (½log 5, ½log 6]`; `H` is negative at half-width `≤ 21/40`; beyond a finite window one test makes the prime part strictly negative for every admissible weight [L]. Below `log 5` the reflected kicks of `{2,3,4}` use `< 0.991` of the Lévy energy; in the half-window diagonal only `n = 2` acts for `c < log 3` [L]. |
| Σ54 Sector order of the archimedean place | Classified | — | Gamma ladder; pole `+` square even, `−` square odd [L]. |
| Σ55 Euler-stage phase repulsion | Solved (above the horizon) | — | Phase lattice above `2πe^{W_a}` for every real finite carrier [L]. |
| Σ56 Onset aperture of `ζ` | Sharpened | RH | Closed-interval law; RH ⇔ `a*(ζ) = ⊤`; off RH `a* = contact`, attained; `a*(ζ) ≥ a_∞` [L]. |
| Σ57 Perron / Beurling–Deny structure | Classified (no-go past `log ρ`) | — | Even band Markov iff `c ≤ log ρ`; past it every pole strength and all weights fail; robust Perron costs height [L]. |
| Σ58 Window visibility law | Classified | — | `k·pairEnergy(δ,a) ≤ L` (also for distinct clusters near one ordinate); shallow non-lattice hiding `a³W ≲ L`; contact law at `c log T` [L]. |
| Σ59 Shielded zeros at fixed aperture | No-go | — | Tapered crystal hides depth `1/a` for every `L ≥ 4a` [L]. |
| Σ60 Switching to balance | No-go | — | Every nonconstant sign gauge creates negative conductance next to its nodes; even sector frustrated in every gauge past `log ρ`; odd sector from `½log 2`; each acting prime power adds a frustrated anti-diagonal [L]. |
| Σ61 Hardy criticality of the arithmetic part | Sharpened | RH | `ℋ(c)` a closed interval, antitone, `= ℝ` before `½log 2`, bounded after; `1 ∈ ℋ(c)` through `enlarged`; scaling optimality and criticality unconditional; optimal Hardy term ⇔ RH [L]. |
| Σ62 Trace theory of window certificates | Classified | — | `𝒥 = 𝒥_reg + 𝒦`; plateau pure edge; no point traces; Weil's form reads no point values; prime reflections are `Ω`-weighted edge data [L]. |
| Σ63 Trivial zeros at the centre | Solved (identity) | — | Mode identities `m_α² + N_α = K_α`, `D_α = K_α + m_α²`; mirror mass ≤ centre killing; trivial zeros are not part of the frustration [L]. |
| Σ64 Signed certificate format on every window | Solved (identity) | — | Neutral signed even theta gauge (line-exact, positive on the window, zero pole charge) and shifted ground state represent both sectors on every reflection pair; below `log 5` jointly equivalent to the `{2,3,4}` sliver band; no window-independent nonsingular even gauge has nonnegative pole charge [L]. |
| Σ65 Finite-template reduction | No-go at spread 6 | — | The ×2/÷3 Hecke orbit in `[1,6)` is infinite: no finite template closed under ratios 2, 3 at spread 6 [L]. |
| Σ67 Non-orthogonal untwisted–twisted coupling | Reduced (to head thresholds) | RH (all `d`) | Dirichlet-shift companions `1_{d|n}g₀(log(n/N) + log d)/√n` couple at `O(1)` (orthogonal twists at `O(1/K)`), annihilate tail modes; stabilization of every direction forces `R₁(log d) = ⊤` and follows from `R₁(log d + ε) = ⊤`; unconditional for `d = 2`; for every `d` ⇔ RH [L]. |
| Σ68 Gauge freedom | Classified | — | The neutral gauge family acts only in the pole direction: on the pole-neutral hyperplane the representation is `archForm − primeSum` for every pocket position; receding pockets conserve the outside deficit; odd variance retention necessary above `273/400` for every shift [L]. |
| Σ66 Contact of the de Branges chain | Sharpened | RH | RH ⇔ no finite contact ⇔ every evaluation kernel bounded as the aperture grows; at contact the window stays positive and a fixed kernel diverges [L]. |
| Σ69 Width at bounded aperture | No-go | — | For every `a` and `δ ∈ (0, ½]` an off-line lattice of width `δ` has a nonnegative form at aperture `a`; a finite-aperture certificate is consistent with every width; the negativity rate along the lag family is the width [L]. |
| Σ70 Free-weight margin | Classified | — | `max_λ λ_min(W_λ|[−c,c])` collapses with `λ_min(W_Λ)`: gain below `500` for `c ≤ 0.66`; bands of `λ(2)`, `λ(3)` of width `5×10⁻⁷`, `2×10⁻⁴` at `c = 0.66` [N]. |

## Π — precision and production

| Wall | Status | Strength | Content |
|---|---|---|---|
| Π1 Global law | Solved (equivalence) | RH | `ψ(x) − x ≤ C√x log²x` ⇔ RH; Redheffer `det R_N = M(N)` [L]. |
| Π2 Deciding input | Open | RH | No unconditional source input at square-root precision. Any input implying the count is parity-breaking, precision-faithful against `εn^{−η}`, `η < ½`, of unbounded aperture, with stabilizer in the square-root class; PNT, Guth–Maynard and weaker error laws are precision-blind [L]. |
| Π3 Producer cost | Partially solved | sub / RH | Multivariate parity producers reach `(1+ε)x + C_εlog²x` [L]. |
| Π4 Window precision (kernel = coupling) | Sharpened | RH | The reflection-pair prime-count band ⇔ RH ⇔ Weil lag ⇔ JAS ⇔ CTF ⇔ PBM ⇔ eventual Robin [L]. |
| Π5 Conjugate diagonal | Sharpened | sub → ≥qRH → RH | Means `O_c(log U)`; one dyadic constant ⇔ RH [L]. |
| Π6 Averages versus all heights | Sharpened | — | Double-log stage outside `O(V/log log V)` windows [L]. |
| Π7 Census / pair surplus | Partially solved | sub | Simple critical `≥ 0.67250071`; positivity-only certificates cannot reach `3/4` [L]. |
| Π8 Depth visibility | Classified | — | Cluster-product horizon [L]; superseded by Σ58 (models) and Γ36 (camera). |
| Π9 Exceptional moduli | Partially solved | sub | Uniform zero-free region and Siegel for `q ≤ (log x)^A` [L]. |
| Π10 Frequency localization | Solved | — | Cyclotomic band abscissa `2Θ` [L]. |
| Π11a–e Cone, bidegree, fixed-rank, definite, Siegel counts | No-go | — | Excluded as sign producers [L]. |
| Π11f Logarithmic duality | Partially solved | sub | Abel completion, logarithmic RR [L]. |
| Π11g Boost transform | Solved (identity) | — | `∫Z⁺(s,u)e^{2wu}du = K(s,w)ζ(s+w)ζ(s−w)` [L]. |
| Π11h Count-valued primitive `h¹` | Sharpened; closed as mechanism | RH | Window `h¹ = ½Q` [L/D]. |
| Π12 Subconvexity / heat floor | Partially solved | sub | `μ(½) ≤ 33/200`; heat floors `133/200`, `6600/9991` [L]. |
| Π13 Prefix scale | Solved | — | Strip zeros `Θ(N² log N)` [L]. |
| Π14 Amplifier rank | No-go (finite support) | — | Radius `Be^λ` [L]. |
| Π15 Critical-scale residual sign | Classified | — | Residual = aliasing + Weil's form [L]. |
| Π16 Genus function | Sharpened | indep. | Upper law open [L]. |
| Π17 Window energy | Sharpened | RH; ≥qRH (log stage) | Abscissa = twice the maximal depth; bounded port ⇔ purity [L]. |
| Π18 Finite realizations | No-go | — | [L]. |
| Π19 Mollified log-mean from moments | No-go | — | [L]. |
| Π20 Count identities at the first prime | No-go | — | [L]. |
| Π21 Exact balance | Classified | — | Weil cone `{Λ}`; `μ(a) ≤ K exp((11/2)a − πe^{2(a−2)})` [L]. |
| Π22 Near-line density ladder | Sharpened | sub | Eight forms; `D_win` ⇔ thin Planck shadows [L]. |
| Π23 Inner caps | Reduced | RH (all degrees); ≥qRH (fixed degree) | Inner-cap flux = `Σ_{off-line}m_ρe^{(ρ−½)t}` + bounded + `L²`; Laplace cancellation at all exponents ⇔ no off-line zero in the window; fixed degree ⇔ corridor; all stages ⇔ RH; VK caps prefix-invariant [L]. |
| Π24 Parity at dimension zero | Classified | — | [L]. |
| Π25 Euler-product pinning | Classified | — | Shifted-pole weight refuted [L]. |
| Π26 Bulk second order | Solved | — | `2γ₁ + γ²`; polar growth [L]. |
| Π27 Retained Gamma comparison | No-go (lossless) | — | Survivor: higher reserve [L]. |
| Π28 Gauge-torus spectrum | Classified | RH at the trivial point | Exponents `[Θ, 1]` [L]. |
| Π29 Square-root threshold | Classified | — | `λ = ½` reads ζ's isolated zeros; sign-hiding only on an ℓ¹ ridge [L]. |
| Π30 Collective payment of the kicks | Sharpened | RH | Kicks beyond collar locality are the smoothed count; the coupling truncates to `n ≤ e^{2c}` [L]. |
| Π31 Terminal prime channels | Solved | — | [L]. |
| Π32 Elementary sieve inputs | Solved | — | Prime progressions to large moduli, affine collision mass, periodic profiles, centered affine samples [L]. |
| Π33 Finite free Gaussian capacity | Classified | — | Degree regime: `e^{(t/d²)D²}J_d` not real-rooted ∀t > 0, unboundedly many non-real roots, Bernoulli-robust; shift regime: capacity → Hermite value `½` [L]. |
| Π34 Euler-side stability and phase drift | Classified | — | Normalized Euler factors HB-stable at every degree; drift `θ_S/2` forced and sharp; no bounded translation stabilizes all finite products; symmetric carrier real ⇔ `c ≥ θ_S/2`; curved phase degree horizon `≈ δ²/(4a)` [L]. |
| Π35 Source-faithful finite free split | No-go | — | `J^{d,n} = Γ ⊠ Θ`, Γ Laguerre, Θ never real-rooted (strict log-convexity); Dirichlet pieces never real-rooted; ζ-side, Gamma-side and pole pieces unstable for every phase; degree-3 test non-discriminating [L]. |
| Π37 Zero-free half-planes as finite free stability | Classified | — | Zero-free `Re s > σ` (σ ≥ ½) ⇔ every Jensen polynomial of `ξ(σ + i·)` has roots in `Im ≤ 0` ⇔ bounded imaginary parts along infinitely many degrees; otherwise linear growth `κd`; strict and unconditional for `σ ≥ 1`; real-point Jensen polynomials Hurwitz stable ⇔ zero-free right of σ [L]. `R_d(Ξ)` is a limit of finite free products of rank-one zero pieces, all real-rooted iff RH [L]; `ξ` has no stability margin on any line, phase `c = 0` exactly critical; genus-one class classified by drift [W]. |
| Π38 Finite free Hardy theorem | Solved | — | `R_d(Ξ)` has at least `M` distinct real roots for all large `d`, every `M` [L]. |
| Π39 Wiener–Hopf factorization of the archimedean symbol | Solved (identity) | — | Logarithmic Poisson factor of `1 + ½log(1 + ξ²)`: slit-plane holomorphic, one simple negative zero, half-line support preserved, reciprocal a Stieltjes transform of a positive measure, positive causal kernel, renewal mass normalized [L]. Half-line inverse, explicit positive Green kernel, boundary readout with factor `√log(1/x)`, constant one [L/W]. |
| Π36 Mollified Jensen stability | Sharpened | RH | RH ⇔ `R_d(Ξ·M_S)` stable at infinitely many degrees ⇔ bounded imaginary parts along infinitely many degrees (any finite S, any phase) [L]; the converse direction does not use the mollifier [L/D]. |
| Π40 Self-improvement of a strip | Open | sub | `Θ < 1 ⇒ Θ = ½`; RH ⇔ `Θ < 1` plus this [D]; false for off-line lattices and, in analogue, for `ζ(s)ζ(s−ε)`; Hadamard and tensor powers carry RH at every degree, so the `𝔽_q` step has no analogue [L]; no mechanism. |

## Γ — selection and reflection

| Wall | Status | Strength | Content |
|---|---|---|---|
| Γ1 Trivial gauge point | Open | RH | `Θ ≥ ½`; Haar-a.e. `½`; Baire-generic `1` [L]. |
| Γ2 Prime-set flips | Solved | — | Every nontrivial pattern separated [L]. |
| Γ3 Twin-blindness of soft structure | No-go | — | [L]. |
| Γ4 Frobenius at infinity | Sharpened | RH | Window involution = twisted Krein reflection [L]. |
| Γ5 Source identification / pre-divisor | Partially solved | RH | Zero-independent forcing needed [L]. |
| Γ6 Boundary sign / coherence | Solved | — | [L]. |
| Γ7 Affine carrier | Solved | — | [L]. |
| Γ8 Poisson rigidity | Sharpened | RH | Zero-side positivity = RH [L]. |
| Γ9 Archimedean continuity vs height decay | No-go | — | [L]. |
| Γ10 Function-field indistinguishability | Sharpened | — | Camera identifies at the genus; Cayley ladder entries over `𝔽_q` = sharp Weil lower bound; ladder reflection positivity = RH for the curve [L/W]. |
| Γ11 Pole-blindness of the glue | No-go | — | [L]. |
| Γ12 General gauges | Solved | sub | [L]. |
| Γ13 Source-uniform extinction | No-go | — | [L]. |
| Γ14 Local counterterm selection | No-go | — | [L]. |
| Γ15 Functional-equation twins | Partially solved | sub | [L]. |
| Γ16 Selection–sign gap | Sharpened | RH | No selector gives positivity [L]. |
| Γ17 Scattering recentering | Classified (no-go) | — | [L]. |
| Γ18 Divisor-identity selection | Solved | — | [L]. |
| Γ19 Correspondence algebra over ℤ | Sharpened | RH | Rosati positivity ⇔ orbit Hodge index [L]. |
| Γ20 Window selection | Classified | — | [L]. |
| Γ21 Density selection | No-go | — | [L]. |
| Γ22 Contractive scattering positivity | No-go | — | [L]. |
| Γ23 Weil cone uniqueness | Solved | — | Full Weil positivity forces `Λ`; only the multiple `1` of `Λ` is admissible on every window [L]. |
| Γ24 Mayer reflection positivity | Sharpened | RH | Krein form `≥ 0` ⇔ RH; `−D_s(ψ_s)` = `K_σ`-weighted norm of `T_{p,s}ψ_s` (every prime) and of the three-term shift difference, `K_σ ∝ (b^{2σ−½} − b^{−(2σ−½)})²`; infinitely many critical resonances with `D = 0` and positive norms; any nonnegative representation ⇔ RH [L]. |
| Γ25 Two reflection centres | No-go | — | [P]. |
| Γ26 Resonant-state selectors | No-go | — | [L]. |
| Γ27 Tate counts as a selector | No-go | — | [L]. |
| Γ28 Frobenius inside the window algebra | No-go | — | [L]. |
| Γ29 Linear Serre–Krein identification | No-go | — | [L]. |
| Γ30 Completed Tate family | Classified | — | [L]. |
| Γ31 Degeneration type over `𝔽_q` | Solved (calibration) | — | [L]. |
| Γ32 Hecke-equivariant completion | Solved (identity) | identity | [L]. |
| Γ33 Euler rigidity in the Selberg class | Solved | — | [L]. |
| Γ34 Hecke cones and periods | Solved | — | [L]. |
| Γ35 Beurling and Hamburger rigidity | Classified | — | [L]. |
| Γ36 Identification by the explicit formula | Solved (sign-free) | sub | `λ > 1` RvM configurations up to near-collisions; `λ > ½` isolated zeros of ζ with multiplicity; one-depth configurations at the Ingham scale `π/(2a)`, mixed depths hide beyond it (any-depth `π/a`); cancelling clusters of ζ-mimics are near-coincidences within `exp(−κlog X/(1 + loglog X))` [L]. Period-`N` patterns never hide above `(N − 1)π/(Ng)`; period-6 mixed depths hide exactly to `5π/(6g)` [L]. |
| Γ37 Euler columns | Classified | — | Ramanujan = reality; columns hide below `log p/2`; bounded apertures cannot see Euler columns at `p > e^{2r}` in the curvature channel [L]. |
| Γ38 Retained Hecke channel | Classified | — | Sign of `¼ − Re s`, reversed under reflection [L]. |
| Γ39 Blindness = density aperture | Solved | — | `πD` [L]. |
| Γ40 Positivity certifies thin configurations | Solved | — | Split columns; mixed `(g − ½)ℓ` [L]. |
| Γ41 Fakes at their first prime | Solved | — | `½log n₀` [L]. |
| Γ42 Legendre-invariant reality | Solved (identity) | identity | RH ⇔ `J(ρ) ∈ ℝ` [L]. |
| Γ43 Collide or repel over `𝔽_q` | Solved (calibration) | — | A monic integer polynomial with all roots in `|z| ≤ 2√q` has a multiple root or separation `≥ (4√q)^{−poly(g)}` [L]. The disc bound is a hypothesis: a consequence of purity, not a route to it. Integrality quantizes impurity and does not exclude it; finitely many power sums then certify purity [W]. |
| Γ44 Second-order coalescent precision | Solved | sub | Moments of isolated clusters of radius `r ≤ T^{−(M'+κ_λ+1)}` read to `N r^{j+1}T^{M'+κ_λ} + e^{−K'log³T}`; centres `O(r²)`, squared gaps `O(r³)`, discriminants from `2k − 1` images, points by bordered Hankel determinants; dipoles collapse to `2e^{−K'log³T}` [L]. |
| Γ45 Domination as a selector | No-go | — | [L]. |
| Γ46 Reality at near-coincidences | Sharpened | RH | Reality of an isolated near-coincident pair is the sign of `𝓗 = 4(W₁² − W₀W₂)/W₀²` (on-line `≥ Δ² − B`, FE pair `≤ −4δ² + B`); FE-pair squared gaps `≥ 0` at every zero ⇔ RH; prime curvature `(log n)²`-weighted with opposite signs for real and FE pairs [L]. |
| Γ47 Sharp location from positivity | Open (assembly) | sub | Positivity at `a = λL_T`, `λ > 1` ⇒ off-line zeros near `T` have depth `≤ e^{−c log³T}`, by the negative test on the form with the camera's isolating windows; no on-line mimic needed [D]. A receiver, vacuous at known apertures. |

## Bridges

| Bridge | Anchor |
|---|---|
| `κ(K_ζ)` = right zeros = `sup_A ι(A)` = number of finite critical lengths = band poles of `Λ(s)/Λ(s+1)`; RH ⇔ `κ < 2` | HKT, RIT, CWS [L] |
| RH ⇔ `a*(ζ) = ⊤` ⇔ `1 ∈ ℋ(c)` ∀c ⇔ no finite contact of the de Branges chain | WVL, FADF, CSTW [L] |
| Window sign ⇔ two-site sign ⇔ band at the centre ⇔ Stieltjes moments ⇔ two-parameter two-bump family | GWZ, SWC, SRT [L] |
| Reflection-pair coupling = collar Hankel form − smoothed prime count = orbit correlation `c_φ(2m)` | SWC, FADF [L] |
| Below `log 4`: window sign ⇔ two-weight membership ⇔ retained-variance certificates ⇔ Hodge index ⇔ Künneth effectivity ⇔ `1 ∈ ℋ(c)` | SWC, LST, AHD, FADF [L] |
| Kick = positive source − anti-diagonal conductance; even frustration = the pole; trivial zeros paid at the centre | SWC, FADF [L] |
| Weil energy = Krein form of zero coordinates; Mayer defect = `K_σ`-weighted Hecke / three-term norm | RIT [L] |
| Weil image ⇒ configuration up to clusters `e^{−c log³T}`; squared gaps from three images | ZCG [L] |
| Heat collision ⇔ near-coincidence ⇔ sign of `w²` ⇔ sign of `𝓗` | RHTower, ZCG [L] |
| Euler stages, finite carriers, symmetric Euler carriers: real above the phase horizon `θ_S/2` (finite free) / `2πe^{W_a}` (analytic) | ZCG, FFP [L] |
| Jensen hyperbolicity ⇔ heat simplicity ⇔ finite free stability; Gaussian capacity `o(d⁻²)` ⇔ `Λ ≥ 0` | FFP, RHTower [L] |
| Suzuki first variation = complete Weil energy; Cayley ladder = paired Li coefficients | RHTower, ALG [L/W] |
| Inner-cap flux = off-line generating function | CDG [L] |
| Long windows = head windows under Dirichlet shifts: stabilization ⇔ `R₁(log d)` | AHD [L] |
| Window positivity at level `a` ⇒ explicit exponential depth corridor | SquareRootThreshold [L] |
| Archimedean symbol = product of causal logarithmic factors with a positive renewal kernel | CSTW [L] |
| Zero-free half-planes ⇔ finite free stability of shifted Jensen polynomials | FFP [L] |
| Correlation-form windows = finite rational Hecke graphs | WTZ [L] |
| Hodge index = Metzler sign of the Cayley ladder = Li positivity; over `𝔽_q` = sharp Weil bound | ALG [W] |

## Status counts

| Family | Solved | Partially solved | Sharpened | Open | No-go | Classified | Reduced |
|---|---|---|---|---|---|---|---|
| Σ (91) | 21 (Σ1a, Σ1b, Σ1c, Σ1h, Σ1k, Σ1o, Σ10, Σ12, Σ16, Σ24, Σ29, Σ36, Σ37, Σ39, Σ43, Σ45, Σ51, Σ52, Σ55, Σ63, Σ64) | 10 (Σ1d, Σ1e, Σ1g, Σ1j, Σ1m, Σ3, Σ6, Σ9, Σ27, Σ35) | 15 (Σ1, Σ2, Σ3a, Σ4, Σ7, Σ8, Σ17, Σ19, Σ28, Σ32, Σ49, Σ50, Σ56, Σ61, Σ66) | 3 (Σ18, Σ20, Σ47) | 11 (Σ1f, Σ2a, Σ13, Σ14, Σ23, Σ25, Σ42, Σ59, Σ60, Σ65, Σ69) | 27 (Σ1i, Σ1n, Σ1p, Σ1q, Σ1r, Σ2b, Σ11, Σ15, Σ21, Σ22, Σ26, Σ31, Σ33, Σ34, Σ38, Σ40, Σ41, Σ44, Σ46, Σ48, Σ53, Σ54, Σ57, Σ58, Σ62, Σ68, Σ70) | 4 (Σ1l → Σ56, Σ5 → Π17, Σ30 → single-prime transport, Σ67 → head thresholds) |
| Π (47) | 9 (Π1, Π10, Π11g, Π13, Π26, Π31, Π32, Π38, Π39) | 5 (Π3, Π7, Π9, Π11f, Π12) | 9 (Π4, Π5, Π6, Π11h, Π16, Π17, Π22, Π30, Π36) | 2 (Π2, Π40) | 11 (Π11a–e, Π14, Π18, Π19, Π20, Π27, Π35) | 10 (Π8, Π15, Π21, Π24, Π25, Π28, Π29, Π33, Π34, Π37) | 1 (Π23 → off-line generating function) |
| Γ (47) | 17 (Γ2, Γ6, Γ7, Γ12, Γ18, Γ23, Γ31, Γ32, Γ33, Γ34, Γ36, Γ39, Γ40, Γ41, Γ42, Γ43, Γ44) | 2 (Γ5, Γ15) | 7 (Γ4, Γ8, Γ10, Γ16, Γ19, Γ24, Γ46) | 2 (Γ1, Γ47) | 13 (Γ3, Γ9, Γ11, Γ13, Γ14, Γ21, Γ22, Γ25, Γ26, Γ27, Γ28, Γ29, Γ45) | 6 (Γ17, Γ20, Γ30, Γ35, Γ37, Γ38) | — |

Strength of the open walls:
- **RH:** Σ1 (minimal form: the band on reflection pairs ≡ `1 ∈ ℋ(c)` ∀c), Σ2, Σ3a, Σ6, Σ7, Σ8, Σ17, Σ18, Σ19,
  Σ20, Σ27 (all stages), Σ28 (subexponential), Σ30, Σ32, Σ49, Σ56, Σ61, Σ66, Σ67 (all `d`), Π2, Π4, Π11h, Π17 (polynomial
  stage), Π23 (all degrees), Π28 (trivial point), Π30, Π36, Γ1, Γ4, Γ5, Γ8, Γ16, Γ19, Γ24, Γ46.
- **identity:** Σ35 (Hamiltonian of the de Branges chain).
- **≥qRH:** Σ4 (`K_ζ`), Σ28 (exponent `< ½`), Π5 (fixed scale), Π17 (log stage), Π23 (fixed degree).
- **sub:** Σ1d, Σ1e, Σ1g, Σ1j, Σ1m, Σ4 (zero–one law), Σ27 (each stage), Σ30 (each stage), Σ47, Σ50, Π3, Π5
  (mean `o(log U)`), Π7, Π9, Π11f, Π12, Π22, Π40, Γ15, Γ47.
- **indep.:** Π16.
