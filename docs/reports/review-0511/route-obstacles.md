# Route obstacles — status quo

Scope: 38 live route formulations, 9 candidates and their supporting programmes, as classified in the
[frontier map](../rh-current-frontier-map.md) and [scoped obstructions](../rh-killed-routes.md).
For every route: path, what is established, the open estimate, the
mechanism class, the obstacles that are **(A) just work** and the obstacles that are **(B) open mathematics**
(no known solution).

Source checkpoint: `9c877bf`.

Evidence: `[L]` integrated, source-reviewed Lean; `[S]` unintegrated/unverified source; `[D]` consequence of stated results; `[N]` numerical. Strength: **RH**;
**≥qRH** (zero-free half-plane or Lindelöf); **sub** (strictly below quasi-RH); **identity**; **method**;
**indep.** (independent of RH). An A item is known mathematics, finite computation, effectivization or
assembly of proved pieces; `(difficulty unverified)` marks A items whose difficulty is not established.

Formulations are not independent mechanisms: HJ→PA, BSH→CDC; FEL's BSY criterion supports live CTF,
while its theta-history producer remains candidate. ADO and FFP are support, not additional candidates.
Criteria, quotient equalities, scalar grades and zero-selected diagnostics do not discharge arithmetic sign or vanishing.

Notation. Windows `[−a, a]` (half-width `a`) or half-windows `[−c, 0]`; `W` is Weil's form, `w_n = Λ(n)n^{−1/2}`,
`H` the archimedean–polar form (all prime weights `0`), `P` the arithmetic part, `𝒥` the Lévy energy. For `f`
left of `m` and its mirror `f∘R`, `R(v) = 2m − v`, the **coupling** is `𝒞_m(f) = 𝓗_m(f) − Σ_n w_n(f⋆f)(2m − log n)`
(collar Hankel form `𝓗_m`); the **band** is `|𝒞_m(f)| ≤ W(f)`. `a*(Z)` is the onset aperture (supremum of
half-widths with nonnegative form); `a*(ζ)` that of the zeros of ζ. `𝒜(c) = {λ : W_λ ≥ 0 on [−c, c]}` is the window cone,
`λ*(c) = sup_λ inf_f W_λ(f)/‖f‖²` the best margin, `ℋ(c) = {t : H − tP ≥ 0 on [−c, c]}` the Hardy interval.
`L_T = ½log(T/2π)`; camera aperture `λL_T`. `ρ³ = ρ + 1`, `log ρ ≈ 0.2812`. `a_k = weilFloorApertureTower k`,
`a₀ = successorWeilFloorAperture`, `181/500 < a₀ < 181/500 + 5×10⁻⁷`; `a_∞ = lim a_k` (strictly increasing, floors
`(1/20000)/2^k`, value not identified). `N_d` = number of non-real roots of the degree-`d` reversed Jensen
polynomial `R_d(Ξ)`. `Θ = sup Re ρ`. `E` = exceptional values of ζ (a dense `G_δ` null set of `a ∈ ℂ` whose
distinct `a`-points come superpolynomially close).

## 0. Mechanism classes

| Class | Mechanism | Status | Anchor |
|---|---|---|---|
| P1 | **Signed criticality.** Weil's form on a window as a frustrated signed Dirichlet form with pole charges; primes pay the archimedean–polar deficit by the sign of their sliver reflections; pole variance retained | live; format exact in both sectors (neutral signed theta gauge, shifted ground state); RH ⇔ the two certificates on every window; gauge freedom acts only in the pole direction; actual even form frustrated past `log ρ`, actual odd form whenever a negative prime reflection acts; globally admitted weights have eventual odd frustration, with weight-dependent onset; size payment dies before half-width `21/40`; below `log 5` the window is the `{2,3,4}` sliver band | SWC, FADF, ACT, WTZ, GWZ, CSTW, WVL [L] |
| P2 | **Prime-blind positivity / calibration.** Archimedean + pole part on signed blind combinations; the cones `𝒜(c)` | live; `𝒜(c)` convex, every entering coordinate bounded, stage fibre a compact interval; `⋂𝒜(c) = {Λ}` under RH, empty otherwise; **effective uniqueness** `\|λ(n) − Λ(n)\| ≤ C exp(Kn − c/1104)` on `𝒜(c)`; **margin law** `λ*(c) ≤ K exp(3c − (π/6)e^{2(c−13/12)})` over all weights; RH ⇔ `λ*(c) → 0`; datum classification by pole weight and log-conductor | RHTower PBAP, FADF, CHT [L] |
| P3 | **Reflection positivity of PM.** Krein positivity of the completed resonant space | reduced: both expressions of the defect carry `(b^{2σ−½} − b^{−(2σ−½)})²`; any nonnegative representation ⇔ RH | RIT [L] |
| P4 | **Square-root cancellation** of one smoothed short-window prime count: the band in prime form; long mollified second moments give conditional receivers | live; classical; parity barrier; one-sided count criteria overlap the band; long-moment upper bounds remain open, and necessary-length laws prove no attainability | SWC, GWZ, CSTW, AOG, APR, CDG [L] |
| P5 | **Reality by continuation / stability.** Actual heat/cosine collision criteria and Jensen all-root control | live receivers; half-Gaussian high-time exclusion at `(6600/9991+ε)/log X`, cosine strict Laguerre sign for `h ≥ ½`; small-time/open-depth sign remains. `N_d` nondecreasing with supremum the off-line zero multiplicity; eventually `N_d ≤ 300√(d log d)`; bulk reality is blind | ZCG, PTR, FFP, LA, TH [L] |
| — | Identification (camera) | complete: configurations fixed up to clusters of diameter `e^{−c log³T}`; squared gaps of isolated polynomially small clusters read from three prime-side images; explicit camera heights; **positivity at aperture `λL_T`, `λ > 1`, confines every zero at height `T` to depth `< exp(−c log³(T/2π))`** | ZCG [L] |
| — | Diophantine repulsion (collide or repel) | an amplifier, not a producer: finite Euler carriers, integral pure carriers and the two-prime cusp repel polynomially (Baker); a.e. value of ζ repels; `0 ∉ E` (polynomial repulsion of the zeros) is open and has no implication for real parts | ADO [L] |
| — | Counts / Hodge index / degeneration | named count-only and domination shortcuts obstructed; actual source-sign criteria remain live | S3, ACS, HF |
| — | Size-only layers (subcritical regime, one critical multiple, twisted sectors, receiving charges, terminal windows, aperture-independent floor) | true and blind [D] | S1 |

Closed mechanism families (anchors in `rh-killed-routes.md` where they exist):

- **Positivity-preserving certificates:** bare Markov supersolutions and Beurling–Deny comparison of the
  even band past `log ρ` at every pole strength and all weights, robust Perron margins beyond the pole-saturation
  gap [L]; **balanced switching**: every sign gauge leaves a negative conductance next to each node, the even sector
  of the actual form is frustrated in every gauge past `log ρ`; its odd sector is frustrated whenever a negative
  prime reflection acts (for Λ, past `½log 2`). Each globally admitted weight is eventually odd-frustrated;
  this supplies no common `½log 2` onset throughout every finite-window cone `𝒜(c)` [L: FADF, CHT].
  The compact folded-supersolution obstruction has unintegrated source [S].
- **Size-only payment of the primes:** edge-law certificates die at constant one (`c* ∈ (½log 5, ½log 6]`); `H < 0`
  on a window of half-width `≤ 21/40`; beyond a finite window one test makes the prime part strictly negative for
  the whole calibration space [L: FADF, SWC].
- **Cost-only and sign-blind fold payment; uncoupled stage loans; variance-dropped ground states;
  window-independent theta gauges; gauge optimization off the pole direction; point readings; orthogonal twisted
  repair of untwisted negativity; fixed and quartic theta cross-loads (capacities exact)** [L: WTZ, AHD, SWC, FADF,
  TCS].
- **Approximate or alternative weights:** the all-aperture cone is `{Λ}` or empty; every coordinate is pinned at rate
  `exp(Kn − c/1104)`; the best margin over all weights collapses doubly exponentially [L: RHTower, CHT].
- **Producers below square-root precision:** PNT, Guth–Maynard, every error law weaker than square root, finite
  systems of linear laws (Mertens), Type I information at level `N^{1−δ}`, Type II norms, every upper bound on
  `Re s ≥ ½` stable under an impure Euler factor; normalized unit-bounded mollifiers of fixed polynomial length
  cannot have normalized second moment → 1. In that family, excess `≤ K₀/log T` requires
  `log N ≥ log²T/(6K₀) − (4/3)log T`; a fixed leading coefficient `< 1/(6K₀)` is excluded [L: ASRP, APR, CDG].
- **Bulk statistics of Jensen roots:** the real roots of `R_d(Ξ)` at scale `½log d` follow the Cauchy law
  `1/(w+i)` for every `σ ≥ ½` and for every backward heat flow `H_{−τ}`, which has non-real zeros: density-one
  reality and the bulk law carry no arithmetic; all arithmetic sits in `o(d)` outliers [L: FFP].
- **Finite free factorizations:** Szegő on the source-faithful split, factorwise/phase shortcuts, Dirichlet
  pieces, ζ-side, Gamma and pole pieces, the degree-three test [L: FFP].
- **Integrality as a source of purity; fixed-aperture counts of atoms:** `collide_or_repel` assumes the disc
  bound; integrality quantizes impurity and does not exclude it; a fixed-aperture image cannot bound the number
  of atoms (flat lattice) [L: ADO, ZCG].
- **Finite structures, slack, counts, height-local decisions, universal density thresholds, domination as a
  selector, size-only heat repair, PM line selectors:** only the classes stated in `rh-killed-routes.md`.
  KR-TOR/UCF/R1 are retired labels, not proved kills; BAG/PA/TG retain actual receivers. KR-FPR excludes finite
  and cofinal growing finite Hermitian KMS corrections, not all passive carriers. KR-SRP excludes odd-only
  pole weight `β > 1`, not even-only; KR-GAP excludes the stated `Q(z)G₀(z+ih)` lower-Pólya class, not all HB realizations.

## 1. The picture

| Fact | Anchor | Consequence |
|---|---|---|
| RH ⇔ `a*(ζ) = ⊤`; nonnegative half-widths form `[0, a*(Z)]`; off RH `a*(ζ)` = contact, attained with zero ground energy; strictly positive apertures exclude contact; `windowThreshold A = ⊤ ⇔ A/2 ≤ a*(ζ)`; `windowThreshold A = ⊤` for `A ≤ 2a_k`, every `k`; hence `a*(ζ) ≥ a_∞` | WVL, AHD, AIP [L]; [D] | every window route measures one number |
| Single-prime stage transport for all `A` ⇔ RH; Dirichlet-shift stabilization for every divisor `d` ⇔ `R₁(log d) = ⊤` ∀d ⇔ RH; unconditional for `d = 2` at every aperture; joint periodic windows PD ⇔ joint independence | AHD [L] | HF's threshold is the onset aperture; long windows reduce to head windows |
| Positivity at aperture `λ·log(T/2π)/2`, `λ > 1`, `T ≥ zetaNegativeCameraHeight(λ, c)` ⇒ every zero of ζ at height `T` has depth `< exp(−c log³(T/2π))`; no on-line mimic, no separation premise | ZCG SharpLocation [L] | the excluded-depth corridor is cubic-logarithmic and explicit |
| Below `log 5`: window positivity ⇔ the `{2,3,4}` sliver band (only `n = 2` in the half-window diagonal; the three kicks use `< 0.991` of the Lévy energy) ⇔ the joint neutral-gauge/shifted-ground-state certificate | SWC [L] | the first stages are an exact three-power problem |
| `W(f ± f∘R) = 2W(f) ± 2𝒞_m(f)`; `W(f) − \|𝒞_m(f)\| = ½min(W(G₊), W(G₋))`; coupling truncates to `2 ≤ n ≤ e^{2c}`; collar floors `weilFloorTowerConst k ∫f²` for `c ≤ a_k` | SWC [L] | the minimal object is a reflection pair |
| Arithmetic part is an optimal Hardy term for `H` iff RH; scaling optimality and criticality unconditional; `⋂_cℋ(c) = {1}` ⇔ RH | FADF [L] | Weil positivity is a critical Hardy inequality with a unique admissible multiple |
| On `𝒜(c)`: `\|λ(n) − Λ(n)\| ≤ C exp(Kn − c/1104)` for `c ≥ 2`, `2 ≤ n ≤ e^{2c−1/6}`; bands are intervals of width `≥ λ*(c)√n`; `λ*(c) ≤ K exp(3c − (π/6)e^{2(c−13/12)})` and `≤` the Gaussian ceiling for all weights; `λ*(a_k) ≥ weilFloorTowerConst k`; RH ⇔ `λ*(c) → 0` | CHT [L] | the cone pins every coordinate at an exponential rate while its margin collapses doubly exponentially |
| Datum `(β, s)` (pole weight, log-conductor): at `β = 1`, `s < 0` cones eventually empty; at `s = 0` nonempty cones force `β ≥ 1 − K exp(3c − (π/6)e^{2(c−13/12)})`; pole-free cones eventually empty for small `s`; critical log-conductor `= −λ*(c)`; the window reads the residue | CHT [L] | the datum of ζ is the critical point of the cone family |
| Before contact each window carries a complete Weil Hilbert space (de Branges space, explicit Hermite–Biehler function, unitary zero-moving, isometric inclusions); growing the window adds an orthogonal kernel increment; exterior crossings bounded (`C_b‖u‖‖v‖`, collar-width independent); actual Riesz endpoint traces and fixed-aperture full-collar pointwise/scaled-L² limits hold; prime and polar responses continuous; `0 ≤ ∫_a^b G′ ≤ G(b) − G(a)`; finite contact forces a diagonal kernel to diverge | CSTW, CHT [L] | kernel absolute continuity, moving-window flux and contact-uniform bounds remain open; the derivative inequality alone is not absolute continuity |
| The archimedean symbol `1 + ½log(1 + ξ²)` factors through a logarithmic Poisson factor with positive causal kernel; the half-line Green operator `CC*` is explicit; the logarithmic form detects interval length (`≥ log(1/h)` per unit mass, `≤ log(1/h) + 3` attained) | CSTW [L] | Wiener–Hopf factorization of the archimedean part |
| Complete Weil collar energy/mass `≥ log(1/h) − C_a`; constant collars attain `≤ log(1/h) + 3 + C_a`, `C_a = ‖weilLogarithmicCorrection a‖` | CSTW [L] | prime/polar terms are included; constants depend on enclosing aperture |
| Correlation-form positivity on a window ⇔ positivity of every finite rational Hecke graph of smaller spread; at spread 6 the ×2/÷3 orbit is infinite | WTZ [L] | finite-matrix reduction ends before `log 6` |
| Camera: `λ > 1` fixes RvM configurations up to near-collisions; `λ > ½` reads isolated zeros of ζ with multiplicity at explicit heights (`zetaPointCameraHeight`); moments of isolated clusters read to `N r^{j+1}T^{M'+κ_λ} + e^{−K'log³T}`; `𝓗 = 4(W₁² − W₀W₂)/W₀²` is the squared gap; positive on-line mimics of ζ's image at fixed aperture have weighted count `Σw ≤ [θ(y−x)/(2π) + A]log(T/2π)` on the `T/2` band; a fixed-aperture image cannot bound the number of atoms (flat lattice with arbitrarily many atoms) | ZCG [L] | identification is complete; it reads weighted mass, never cardinality |
| For actual `Q = halfGaussTransform(t, xiLine X)`, a real collision is exactly `Re Q(0) = Im Q′(0) = 0`; no positive-time real collisions ⇔ RH. At large `X`, `t ≥ (6600/9991 + ε)/log X` excludes collisions; saddle at `½/log(X/2π)` | ZCG [L] | small-time exclusion and the bounded-height box remain; camera gap diagnostics supply no collision sign |
| `N_d` nondecreasing; `Ξ` has `≤ m` off-line zeros ⇔ `N_d ≤ m` for all (equivalently infinitely many) `d`; `sup_d N_d` = number of off-line zeros; `N_d` bounded ⇔ finite off-line support; RH ⇔ `N_d = 0` for infinitely many `d`; eventually `N_d ≤ 300√(d log d)`; saddle identity `R_d(x) = 2Re[(x+ia₀)^d G(τ₁)e^{−a₀τ₁}(1+ε)]`, `‖ε‖ ≤ ½`; at scale `½log d` the real roots follow the Cauchy law `1/(w+i)`, identically for `H_{−τ}` | FFP [L] | the off-line zero count is the exact limit of computable polynomial counts; the bulk is blind |
| Zero-free `Re s > σ` ⇔ Jensen polynomials of `ξ(σ + i·)` stable; `ξ` sits on the exact stability boundary (no margin on any line, phase `c = 0` critical); genus-one class classified by drift; Möbius-mollified stability at infinitely many degrees ⇔ RH | FFP [L] | finite free probability reproduces every zero-free half-plane and de Bruijn–Newman criticality |
| Every fixed Xi Jensen degree `d` is real-rooted for all shifts `n ≥ xiJensenRealRootednessHorizon d` (explicit) | RHTower/Jensen [L] | the fixed-degree regime is effective and decides nothing |
| Taylor coefficients of `ξ(½ + x)` at the centre form a PF₄₅ sequence; all coefficients of `ξ(½+x+it)ξ(½−x+it)` are `≥ 0` for `\|t\| ≤ 709/50`; off-line zeros have `\|Im\| ≥ 14.68` | RHTower XiSlice [L] | all-order positivity on an explicit band; PF_∞ at the centre is RH |
| RH ⇔ for every `k` the Hausdorff row `k` is nonnegative on the finite initial segment `r < explicitPrimeArchHausdorffShift k`; nonnegative for `r ≥ H(k)` unconditionally | SRT EffectiveHorizons [L] | PA's sign is an explicit finite segment per row, infinitely many rows |
| Every off-line zero of ξ gives a finite-degree negative test on one of the `log 2`, `log 3` heat grids at independently fixed offsets; `Σ_q‖xiGaussianHeatTerm h q‖ ≤ 6/h`; detection degree explicit from the finite outer spectrum | SRT EffectiveHorizons [L] | HCF requires all degrees on both fixed grids, not all offsets |
| Explicit ξ contour bounds `10T + 100 log T`; `xiSymmetricMass` within `εT log T` of `(1/π)T log T` at an explicit height | SRT EffectiveHorizons [L] | every height-dependent constant in the detector theorems is explicit |
| Mollified second moment: `∫_T^{2T}\|ζM(½+it)\|² ≥ (1 + 1/(8+6θ))T` for every normalized unit-bounded Dirichlet polynomial of length `T^θ` (real: `θ ≤ log T/24`; complex: `log N ≤ T^{1/60}`); excess `K₀/log T` forces `log N ≥ log²T/(6K₀) − (4/3)log T`; moment `→ 1` forces `log N/log T → ∞`; the credited Jensen budget diverges for `y ≤ (log T)^{1/8}` | APR, CDG [L] | fixed polynomial length excludes normalized moment → 1 in this unit-bounded family, not clustering by other mechanisms |
| Moment `→ 1` at length `exp(o(T))` ⇒ log-mean `→ 0` ⇒ `100%` critical-scale clustering; excess `K₀/log T` at length `exp(T/log T)` ⇒ `D_zero ∧ D_win` (real and complex coefficients) | APR, CDG [L] | the producer, if it existed, would deliver B20 and B21 |
| Dyadic `∫_T^{2T}\|ζM\|² ≤ CT` with prefix cancellation to `X₁ ≥ T^{θ₁}`, `θ₁ > ½` ⇒ all but finitely many zeros have depth `< 1/(2θ₁) + ε`; cofinal `∫_1^T\|ζM\|² ≤ C_θT^K` for arbitrarily large `θ` (`X₁ ≥ T^{3θ/4}`) ⇒ RH; a single off-line zero forces a critical-line spike `≥ (3/4)δe^{−2αδ²}Y^{2δ}` | CDG [L] | dyadic depth strip is nontrivial only when `1/(2θ₁) + ε < ½`; cofinal receiver gives RH |
| Critical-line proportion `N₀(V)/N(V) → 1` ⇒ every off-line count beyond `κ/log V` is `o(V log V)` ⇒ (L) and the eight equivalent forms; the `rootModel` (proportion `→ 1`, depth tails `≪_r e^{−ra}V` for every `r`, (L), clustering) violates `D_win` and `D_zero` | CDG [L] | B20 is critical-scale clustering, implied by proportion one; B21 needs stronger depth decay |
| `D_win` follows from any holomorphic actual-zero detector with shifted `L²` defect `≤ Ce^{−r(σ−½)log V}·V/log V`; the Fejér–Dirichlet detector vanishes in `≥ V/12` windows with `L^p` and `log⁺` defects `≪ V/log V` for every `p`; every subcritical polynomial mollifier has shifted defect `≥ c_{θ,A}V` and disc-corridor bound `≫ V log V`; Barban–Vehov two-length defect `≤ (T₂−T₁)A₀e^{−r(σ₀−½)log S} + 240S^{θ_X+½}`; Gallagher's `log N` is sharp | CDG [L] | the detection threshold `V/log V` is exact; the stated subcritical mollifier family cannot reach it |
| Deciding input: any property of weights implying the count `ψ(x) − x = O(√x log²x)` is parity-breaking, locally pure, precision-faithful against `εn^{−η}`, `η < ½`, of unbounded aperture, with stabilizer in the square-root class; Type I at level `N^{1−δ}`, Type II norms, finite linear laws, Mertens, PNT, every upper bound surviving `ζ(s)(1 − cp^{−s})`, `c > √p`, are inherited by weights failing the count; the Liouville twin `λΛ + 2` shares every error law above `√x`; prime polynomials of `λΛ` and `−Λ` agree in mean square to `O(T log T)` through `N ≤ T²` | ASRP, APR [L] | Π's entry test is sharp and excludes every classical producer |
| Second moment at length `T^θ` sees `εn^{−η}` iff `η < ½ − 1/(2θ)`; below the window only moduli are seen; square-root precision needs `θ → ∞`; `∫_{−T}^T\|P_a\|² ≤ (5π/2)T²S_a(N, 1/T)` (Selberg integral dictionary) | APR [L] | precision is a length statement |
| `Θ_a = Θ + a` for `ξ(s+a)ξ(s−a)`: self-improvement `Θ_a < 1 ⇒ Θ_a = ½` for all shifts iff `Θ = 1`; prime coefficient `≥ p^a log p` | APR [L] | B57 must use the Ramanujan bound or degree one |
| Distinct zeros of `∏(1 − p_i^{−s})`, of integral pure carriers `∏F_i(p_i^{−s})`, of `∏(1 − a_pp^{−s} + p^{−2s})` (`\|a_p\| ≤ 2`), and of the cusp carrier `(1−2^{−s})² − (1−3^{−s})³` at height `≤ T` are `≥ cT^{−C}` apart (Baker–Matveev); a Liouville Satake angle defeats every polynomial law, a.e. angle obeys one; near-coincidences of finite-prime carriers come exactly from consistent Bohr tangencies, algebraic tangencies are singular, the Euler product's only consistent tangency is `(1,1)` at `σ = 0`; `(1−2^{−s})(1−3^{−s})` has distinct zeros at every positive distance | ADO [L] | repulsion is Diophantine and depends on the rank of the frequency module |
| A near-coincidence flattens ζ: `‖ζ′(ρ)‖‖ρ′−ρ‖ ≤ 160e²(\|γ\|+2)(\|γ\|+5)‖ρ′−ρ‖²`; two zeros within `1/16` give joint small values at the midpoint and conversely (Rouché); an off-line zero at depth `δ` forces `\|ζ(½+iγ)\| ≤ 480e²(\|γ\|+2)(\|γ\|+5)δ²` | ADO [L] | an FE pair is a Lehmer-type near miss of `Z(t)`; depth is read on the line |
| For a.e. `a ∈ ℂ` the `a`-points of ζ in the strip repel polynomially; the exceptional set `E` is a dense `G_δ` of measure zero and every `a ∈ E` has superpolynomially close distinct `a`-points | ADO [L] | B54 (polynomial repulsion of the zeros) is the statement `0 ∉ E` |
| `collide_or_repel_of_monic`: integer polynomials with roots in `\|z\| ≤ R` have distinct roots `≥ (2R)^{−((n−1)²+n−2)}` apart; impurity is quantized; finitely many power sums certify integral purity (orders `> (q/9)^{1/4}`); continuous integer families are constant; a uniformly separated real family transports real-rootedness; loss of reality forces arbitrarily close distinct roots | ADO [L] | integrality amplifies a certificate and produces none; repulsion along a path is what carries reality |
| Ninth signed centre-mixed theta Hankel section PD at every `0 < a < ½`; complete fifth even native tail PD at every cutoff `r ≥ 0` by exact gamma-reserve allocation; every finite-rank repair tested has a sharp capacity `< 1` at some scale | TCS [L] | rank 9 closed; no single compensation works at all scales |
| Resonant `D_s` is minus the `mayerDefectWeight`-weighted Hecke integral divided by `abs(1+p^(1−2s))²`; negative on both off-line partners, zero on the quarter-line despite positive raw norms | RIT [L] | raw Hecke norm is not the defect; independent nonnegativity remains open |
| Inner-cap flux = `Σ_{off-line ρ}m_ρe^{(ρ−½)t}` + bounded − `L²` | CDG [L] | WD's estimate is a zero-free statement verbatim |
| Cayley ladder of ζ = Toeplitz ladder of paired Li coefficients; RH ⇔ NSD on primitive vectors ⇔ entrywise `≥ 0`; over `𝔽_q` the ladder entries are the sharp Weil lower bound | ALG [L] | Hodge index = Metzler sign = Li positivity |

## 2. Shared obstacle blocks

### S0. The band, the Hardy interval and reflection pairs

Routes: every route of C1, C4, C7, C14, C15, C19, C26.

Established [L]: RH ⇔ two-site PD ⇔ band on every reflection pair ⇔ `1 ∈ ℋ(c)` ∀c ⇔ every growth step a translation
contraction ⇔ positivity on the two-parameter family `κ_γ(t + v/2) ± κ_γ(t − v/2)` ⇔ `λ*(c) → 0`; collective sliver
identity and collar floors through the tower; `𝒞_m(φ) = c_φ(2m)` for even bumps; scaling optimality and criticality
of the Hardy form unconditional.

| | Obstacle | Strength |
|---|---|---|
| B1 | The band at every step and every test (`a*(ζ) = ⊤` ≡ `1 ∈ ℋ(c)` ∀c ≡ `λ*(c) → 0`) | RH |
| B10 | No zero mode at any length | RH |

### S1. Complete Weil family at the critical curve

Routes: HF, SRT, AIP, ACT (index), ACS-atomic, SC, CHMD (index). Programmes: CACT, AHD, CSAR, ACPL, ADT, RAPT, TM, SSHA, CAF, BVI.

Established [L]:

- Subcritical PD for `1 ≤ c ≤ (log N)^α`, `α < 1/8`; whole-space PD at one critical multiple; a uniform
  aperture-independent critical multiple across all prime entries.
- Every fixed critical ratio has a positive growing low packet through `⌊(log N)^(13/32)⌋`; this is not full-space positivity.
  Cofinal `xiDampedSourceWork(n+4) ≤ 2` is an RH-equivalent receiver, not an established ceiling.
- `windowThreshold A = ⊤` for `A ≤ 2a_k`, every `k`; every critical pencil positive on those windows.
- Stage transport: composite stages carry no fold; prime-power stages ⇔ `stageForm + w·foldEnergy ≥ w·end mass`;
  unconditional transport across `p = 2`; single-prime transport for all `A` ⇔ RH.
- Dirichlet-shift companions `1_{d|n}g₀(log(n/N) + log d)/√n`: `O(1)` cross term, tail modes annihilated at `O(1)`;
  stabilization of every direction forces `windowThreshold(log d) = ⊤` and follows from
  `windowThreshold(log d + ε) = ⊤`; unconditional for `d = 2` at every aperture and every `K > 0`; for every `d` ⇔ RH.
- Joint periodic windows (arbitrary moduli and profiles): complete complex Weil Gram eventually PD at every critical
  ratio iff the joint spatial/twist functions are independent; character windows graded by parity; distinct primitive
  conductors decouple at critical second order.
- Critical-curve second order, twisted sectors, frequency pole, bulk, terminal windows, conductor packets, receiving
  charges (capacity `log log N + O(1)`; complete physical energy does not control charge).

Status: every layer below the sign is size-only and classified; HF's sign content is `a*(ζ) = ⊤`; twisted directions
cannot pay untwisted negativity. The far-complement estimate loses `O(c)` against its `O(log N/c⁷)` reserve.

| | Obstacle | Strength |
|---|---|---|
| A1 | Explicit constants and horizons (`K₀`, eighth-root theorem, `1/9`, logarithmic profile, Beurling schedule, conductor range `M(N) = o(c_N)`) | — |
| A2 | General profiles past `θ = 1/1080` | — |
| A4 | Certified ratio interval at its size-only optimum; receiving complement inside it (difficulty unverified) | — |
| A9 | Literal channel norms critically small with growing periods, offsets and prime bands (difficulty unverified) | — |
| B6 | Twisted-sector positivity through all conductors and frequencies at every multiple | sub |
| B7 | Full-space sign at critical ratios beyond the size-only threshold | sub per ratio; RH all |
| B8 | General profiles past `log log N` on the full space | sub |
| B9 | Exact SOS on one two-prime lattice | RH |
| B16 | Window negativity exponent `< ½` (≡ zero width `< ½`) | ≥qRH |
| B55 | Head-window thresholds `windowThreshold(log d) = ⊤` for every `d`; stabilization forces this threshold and follows from `windowThreshold(log d + ε) = ⊤`. For `d = 3`, the necessary aperture is `½log 3`; a positive aperture margin suffices. The tower limit `a_∞` is unidentified | RH |
| B33 | HF-native arithmetic sign: a window beyond the base certified by the complete family itself (`windowThreshold A = ⊤ ⇔ A/2 ≤ a*`: the qualifier has no content) | sub; finite window |

### S2. The window tower, its canonical system and signed criticality

Routes: RW, EWU, OWU, ACT, AIP, CHMD, TT, HF, ACS, SRT, SZ, MSC. Programmes: CWS, WTZ, DZG, GWZ, CSTW, SWC, FADF, CHT.

Established [L]:

- Window datum, stage criterion, kick = collar Rosati pairing, frozen form; lattice canonical system; continuum jet
  Hankel limit; sectors ⇔ Hamburger / shifted Hamburger; window ⇔ Stieltjes.
- **De Branges chain before contact:** complete Weil Hilbert spaces, entire Fourier coordinates, explicit
  Hermite–Biehler function, unitary zero-moving, antiunitary conjugation, isometric inclusions; orthogonal kernel
  increments; bounded exterior crossings independent of collar width; actual Riesz endpoint traces with the `√log(1/t)` law
  and full-collar pointwise/scaled-L² limits at fixed apertures; complete collar energy/mass `log(1/h) + O_a(1)`, including
  prime/polar corrections; continuous prime and polar responses; evaluation Gram with `0 ≤ ∫G′ ≤ ΔG`; kernel blow-up at
  finite contact with the contact window nonnegative, not strictly positive; ¬RH forces a diagonal kernel to diverge.
  The derivative inequality neither proves absolute continuity nor identifies vanishing Gram-density singular part with RH.
- Weil symbol = logarithmic multiplier + bounded convolution; Riesz vectors bounded; Wiener–Hopf factorization of the
  archimedean symbol with positive causal kernel; half-line Green operator `CC*`; logarithmic form detects interval
  length.
- Full increment/collar equation and fixed-enclosure compatibility have unintegrated source [S]; kernel absolute
  continuity, moving-endpoint flux and contact-uniform arithmetic bounds remain open.
- Calibration cones `𝒜(c)`: convex, cylinders, each entering coordinate bounded, stage fibre a compact interval;
  sharp entry law; real tests decide; **effective uniqueness** at rate `exp(Kn − c/1104)`; bands are intervals of width
  `≥ λ*(c)√n`; **margin law** `λ*(c) ≤ K exp(3c − (π/6)e^{2(c−13/12)})` over all weights; `λ*(a_k) ≥ (1/20000)/2^k`;
  RH ⇔ `λ*(c) → 0`; datum classification (critical log-conductor `= −λ*(c)`); theta-smoothed pinning; quantitative
  Hamburger uniqueness (`η^{1/69}`).
- Below `log 4`: two-weight convex membership ⇔ Markov–Hankel pair ⇔ retained-variance certificates ⇔ Hodge index ⇔
  Künneth effectivity; neutral signed even theta gauge and shifted ground state exact on every window; below `log 5`
  the `{2,3,4}` sliver band; gauge freedom only in the pole direction; receding pockets conserve the outside deficit;
  odd variance retention necessary above `c = 273/400`.
- Floor tower `a_k`, strictly increasing, floors `(1/20000)/2^k`, on windows and reflection pairs; no upper bound on
  the tower is proved; `a_∞` not identified.
- Perron sign law; frustration localization; robust Perron costs height. Actual acting negative prime reflections
  force odd frustration; each globally admitted weight is eventually odd-frustrated. No common onset is asserted
  for all members of each finite-window cone.
- Trivial zeros paid by centre killing; `𝒥 = 𝒥_reg + 𝒦`; no point traces.
- Finite rational Hecke graphs decide correlation-form windows; exact Tate horizons through `log(81/16)`; positive Tate
  dimensions `[0, κ(A)]`, `κ(A) → 0`.

Status: the certificate format is exact on every window in both sectors; the cone is pinned at an exponential rate and
its margin collapses; what is open is the inequality the format states. No certificate is established for
`c ∈ (a_∞, log 2)`. These windows carry no zero information (S11).

| | Obstacle | Strength |
|---|---|---|
| A5 | Rigorous computer-assisted certificate of `(w₂, w₃) ∈ belowLogFourBandWeights c` for `c ∈ (a_∞, log 2)`; margins `1.5×10⁻⁵` (odd), `5.6×10⁻⁸` (even) at `c = ½log 3`, `≈ 2×10⁻⁴` on the odd unit window [N] | — |
| A6 | Exact Tate horizons of the remaining stages below spread `6` | — |
| A7 | Closed form of the first-stage complement `Φ_ε` | — |
| A28 | Atomic-lattice bound `λ_max ≤ ½log N` | — |
| A33 | Lévy sector margins at `c = ½log 3` in both sectors [N] | — |
| A43 | Identify the tower limit `a_∞` (closed form or bounds for `Σ_k a_k·multiPrimeApertureStep(a_k, (1/20000)/2^k)`); decide whether a finite tower stage passes `½log 3` | — |
| B2 | Kick admission at every stage | RH as induction; each stage sub |
| B3 | Frustration domination: the neutral signed theta-gauge inequality `2V ≤ J_{M⁺}` (even) and the shifted-ground-state inequality (odd) on every window | RH; fixed length sub |
| B4 | Structural certificate of the odd unit window (`w₂ ∈ unitBandWeights`) | sub |
| B5 | Structural certificate below `log 4` (`a*(ζ) ≥ log 2`), the prime `3` paid by sign | sub; finite window, no door |
| B56 | The `{2,3,4}` sliver band below `log 5` (`a*(ζ) ≥ ½log 5`) | sub |
| B49 | Signed ground-state structure past `log ρ` compatible with unswitchable frustration | method |
| B51 | Kernel absolute continuity and moving-window flux; contact-uniform arithmetic estimates excluding finite contact | method; contact exclusion RH |
| B59 | Actual asymptotic law of `λ*(c)`; coordinate pinning and the doubly exponential ceiling are upper bounds, not a two-sided rate. Nonnegativity for every `c` is B1 | sub (rate); RH (sign) |

### S3. Dimension zero, counts and the Hodge index

Routes: ACS, HF; programmes WTZ, DZG, ATD, AHD, LST, KPA.

Established [L]: Tate jets and signed counts; bare domination ⇔ `Q ≥ 0`; Künneth `h¹ = ½Q`; bidegree, fixed-rank,
definite and Siegel counts excluded; positive Tate dimensions shrink to `0`; below `log 4` window positivity ⇔ Künneth
effectivity ⇔ Hodge index; over `𝔽_q` the Cayley ladder entries are the sharp Weil lower bound and reflection positivity
of every ladder is RH for the curve.

Status: named count-only and fixed-domination shortcuts are obstructed. ACS's exact source cone and
all-aperture Riemann–Roch are constructed; all-aperture Bézout/source-energy sign remains open.
Independent count/height production of that sign is not supplied by the criterion.

| | Obstacle | Strength |
|---|---|---|
| A25 | Künneth primitive `h¹` at small degree; mixed jets | — |
| B24 | Genus upper law | indep. |
| B25 | Logarithmic Serre duality, primitive part | sub |

### S4. Kähler package, stars and gluing

Routes: HF, ACS-Hodge, TG, SC, RW; MC through the gluing determinant.

Established [L]: HR ∧ HL ⇔ strict HR; RH ⇔ HL on the PSD locus; squarefree prime complex ≃ wedge of spheres (reduced
Euler characteristic `−M(N)`); Redheffer `det = M(N)`; zero modes = radical; links disconnected; Möbius gluing of
stars exact.

| | Obstacle | Strength |
|---|---|---|
| A23 | Depth law, star horizons, gcd-strata tables | — |
| B10 | No zero mode at any length | RH |
| B11 | Top coprime stratum | RH |
| B35 | Band holomorphy of `Λ(s)/Λ(s+1)` | RH |
| B45 | Cross-tower gap through the archimedean channel | method |

### S5. Index and finite off-line support

Routes: HKT, AKLT, AID, SRT, CHMD, SC, RIT, CWS; LA/FFP through `N_d`.

Established [L]: finite index ⇒ Lindelöf; RH ⇔ index zero; window index counts critical lengths; `{0, ∞}` laws; index
`≤ R + A`; growing Euler heads unbounded; `N_d` bounded ⇔ finitely many off-line zeros ⇔ bounded de Bruijn–Newman
non-real counts; finite off-line support ⇒ Lindelöf and a zero-free half-plane.

| | Obstacle | Strength |
|---|---|---|
| B12 | Index ceiling uniform in resolution | ≥qRH; RH (tensor) |
| B13 | Zero–one law `κ ∈ {0, ∞}`: exclude finite positive off-line index; bounded `N_d` alone does not imply extinction | sub |
| B62 | Boundedness of `N_d` (≡ finite off-line support); its height law (which off-line zeros are counted at degree `d`) | ≥qRH |

### S6. Window energy, inner caps, near-line density

Routes: WD, LA, TG, HCF, SC-heat, TH-heat; census; HEF. Programmes: CDG, APR.

Established [L]: inner-cap flux = off-line generating function + bounded + `L²`; all exponents ⇔ no off-line zero in
the window; fixed degree ⇔ inverse-polynomial corridor; all stages ⇔ RH; eight near-line density forms (`criticalClustering_logMean_mollifier_hecke_tfae`);
`D_win` ⇔ thin Planck shadows; right-half squared-depth moment `o(V)`; proportion one ⇒ clustering; the root model
(proportion one, every exponential depth-tail rate, clustering) fails `D_win` and `D_zero`; `D_win` from any
holomorphic actual-zero detector with shifted defect `≤ Ce^{−r(σ−½)log V}V/log V`; the `V/log V` scale is sharp across
`L^p` and `log⁺`; universal subcritical floor `≥ c_{θ,A}V` and `V log V` disc-corridor divergence for every
polynomial mollifier; Barban–Vehov log-free at scale `V`; Gallagher's `log N` sharp; moment `→ 1` at `exp(o(T))` ⇒ (L)
⇒ clustering; excess `K₀/log T` at `exp(T/log T)` ⇒ `D_zero ∧ D_win`; necessary length `log N ≥ log²T/(6K₀) − (4/3)log T`
for that excess; dyadic long-mollifier boundedness gives eventual depth `< 1/(2θ₁) + ε`, nontrivial only when
that threshold is `< ½`; cofinal long-mollifier boundedness ⇒ RH;
single off-line zero ⇒ critical-line spike `(3/4)δe^{−2αδ²}Y^{2δ}`; occupied windows `≤ (4/3)⌈2R+7⌉e^{2αδ²}δ⁻¹Y^{−2δ}Msq`.
The integrated real/complex spike receiver bounds off-line occupied windows by critical-line second moments,
not critical-line proportion. Polynomial prefix cancellation still leaves a `log V` loss.

Status: WD's inner-cap bounds are zero-free receivers; moment and shifted-detector bounds give conditional
occupancy/clustering implications. Necessary `exp(log²T)` length supplies no attainable upper bound.
Holomorphic excess tends to zero at zero charge; otherwise it is not eventually bounded above, not necessarily
convergent to infinity (KR-R3).

| | Obstacle | Strength |
|---|---|---|
| B19 | Inner caps at every polynomial stage (≡ off-line generating function `L²(e^{−xt})` at every stage) | RH; fixed degree ≥qRH |
| B20 | `100%` critical-scale clustering; implied by suitable normalized moment `→ 1` with `log N = o(T)`, or by critical-line proportion `→ 1` | sub |
| B21 | `D_win` (≡ thin Planck shadows); `D_zero`; needs depth decay at rate `≍ log log V`, not a proportion or a fixed exponential rate | sub |
| B64 | A normalized unit-bounded complex mollifier family with excess `≤ K₀/log T` at length `exp(c log²T)` (the `D_zero`-forcing rate; fixed `c ≥ 1/(6K₀)` necessary) | sub (⇒ B21) |
| B65 | Cofinal boundedness `∫_1^T\|ζM\|² ≤ C_θT^K` with prefix cancellation `X₁ ≥ T^{3θ/4}` for arbitrarily large `θ` | RH |
| B22 | Hecke defect pointwise / dyadic | ≥qRH / RH |
| B23 | Distributional input beyond counts and moments | method |

### S7. Counts, producers, precision and the gauge torus

Routes: WL, MC, PBM, RB, JAS, CTF, ACS-effectivity, HF-RR, RW; census. Programmes: ASRP, APR, AGT.

Established [L]: one-sided count ⇔ RH; the reflection-pair prime-count band ⇔ Weil-lag ⇔ JAS ⇔ CTF ⇔ PBM ⇔ eventual
Robin; multivariate parity producers reach `(1+ε)x + C_εlog²x`; gauge exponents range over `[Θ, 1]`; simple-critical
proportion `≥ 0.67250071`; deciding-input entry test (parity-breaking, locally pure, precision-faithful, unbounded
aperture, stabilizer in `𝒬`); Type I/Type II/finite-linear-law/Mertens/impure-factor blindness; the Liouville twin
`λΛ + 2` only sees the pole; length–precision law; sharp Möbius mollifier never closes the sawtooth defect; linear
Möbius mollifier with bounded or subpolynomial dyadic defect ⇒ RH; `Θ_a = Θ + a` on shifted products.

| | Obstacle | Strength |
|---|---|---|
| A21 | Logarithmic two-point Chowla | — |
| A24 | Census items; Voronoi; Zwegers | — |
| B26 | `ε`-uniform producer; square-root source input (locally pure, parity-breaking, unbounded length) | sub; RH |
| B57 | Self-improvement of a strip: `Θ < 1 ⇒ Θ = ½` (no mechanism; false for shifted products, so degree one or Ramanujan must enter) | sub |
| B27 | First cyclotomic mode at square-root precision | RH |
| B28 | Signed pair information beyond bandwidth one | sub |
| B29 | First Epstein real zero on the boost line | sub |
| B32 | Half-power law at the trivial gauge point | RH |

### S8. Carriers, coupling, selection and the calibration cone

Routes: SC, ACS, HF; candidates; PBAP.

Established [L]: Gaussian-damped coupling = arithmetic heat average of the compact-test Weil functional; damped cone
⇔ RH; all-aperture Weil cone `{Λ}` under RH and empty otherwise; effective uniqueness and margin law on `𝒜(c)`;
total anti-diagonal kernel positive everywhere
exactly for `n ∈ {2,3,4,5,7,8,9,11,13}`; Selberg-class rigidity; Legendre `J(ρ)` real ⇔ RH.

| | Obstacle | Strength |
|---|---|---|
| A11 | Function-field calibration of the remaining receivers | — |
| A13 | Widths of the finite-level cones `𝒜(c)`; computed to `c = 0.66` [N]; bounded above by `Ce^{Kn−c/1104}` [L] | — |
| A31 | Selberg-class degree-one classification | — |
| B30 | Bounded damped cone coupling; unattained width | RH |
| B31 | Finite-sieve Hodge positivity → global | RH |
| B34 | Rosati positivity of the window reflection | RH |
| B36 | Selection at the trivial gauge point | RH |
| B37 | FE twins inside the full class with off-line zeros | sub |
| B42 | Prime-blind positivity on signed blind combinations | RH |

### S9. Realization and scattering

Routes: PM, RN; W1C realization candidate. PTR's cosine-source criterion is separate from PM positivity.

Established [L]: Mayer operator; resonance ⇔ `ζ(2s) = 0`; completed coefficient-space identity
`Q = 2Re[𝓦H, 𝓦H]`. Resonant `D_s` is minus the `mayerDefectWeight`-weighted Hecke integral divided by
`abs(1+p^(1−2s))²`, not minus a raw norm. It is negative on both off-line partners and zero at critical
resonances with positive raw norms. Independent `D_s ≥ 0` at every upper resonance would force RH.
RN's `det₂` gives denominator `D`, while two ends recover Ξ with multiplicities. Actual `D` has nonreal zeros,
the operator has nonreal spectrum, and loop Pick index is infinite in both signs.

Status: PM's defect sign detects `σ = ¼`; positive raw norms do not supply `D_s ≥ 0`.
RN's joint-node exclusion is separate from reality of its denominator spectrum.

| | Obstacle | Strength |
|---|---|---|
| A14 | Remaining classical carrier/transfer identifications (difficulty unverified); coefficient-space completion is established, physical signed descent belongs to B40 | — |
| A15 | Operator-native nonvanishing on `Re w = 1` (risk: reduces to the Euler product) | — |
| B38 | Independent arithmetic `D_s(ψ_s) ≥ 0` at every upper resonance; weighted negative-energy identity alone supplies no such sign | RH |
| B39 | Statistic of resonant states selecting the decay rate | method |
| B40 | Physical mixed-parameter realization and signed-form descent; independent positive arithmetic carrier | method; positivity with faithful RH landing |
| B46 | PM-native zero-free region for `ζ(2s)` from the carrier alone (route test) | sub |

### S10. Zero-configuration geometry, camera, continuation and repulsion

Routes: ZCG, LA, TH, HCF, XN, SRT; programmes ADO, RHTower DeBruijn, SquareRootThreshold, FFP.

Established [L]:

- Camera: blindness `πD`; one-depth configurations resolved at the Ingham scale `π/(2a)`, mixed depths hide beyond it
  (sharp `5π/(6g)` for period 6; general sufficient `π/a`); fakes caught above `½log n₀`; periodic mimics resolved above
  their last lag; local camera constant quasi-polynomial; explicit heights (`cameraPointHeight`, `cameraMomentHeight`,
  `zetaPointCameraHeight`); Lorentzian mass `< 33/100`; Backlund `100 log T`.
- Inversion: `λ > 1` RvM configurations; `λ > ½` every isolated zero of ζ with multiplicity at explicit height;
  cancelling clusters of ζ-mimics are near-coincidences within `exp(−κlog X/(1 + loglog X))`.
- Weighted images: positive on-line mimics at fixed aperture have `Σw ≤ [θ(y−x)/(2π) + A]log(T/2π)`, `θ > 1`, uniform
  over mimics; a fixed-aperture flat image carries arbitrarily many atoms (no unweighted count); one camera pair reads
  all bounded-mass complex weightings of an isolated cluster.
- Polynomial-scale second order: moments of isolated clusters of radius `r ≤ T^{−(M'+κ_λ+1)}` read to
  `N r^{j+1}T^{M'+κ_λ} + e^{−K'log³T}`; centres `O(r²)`, squared gaps `O(r³)`, discriminants from `2k − 1` images.
- **Sharp location:** two normalized convolution cameras at the cluster of a deep zero and its reflection make
  `Re W(f−g, f−g) < 0` at aperture `λ·log(T/2π)/2`, `λ > 1`, without separation premise; hence positivity at aperture
  `λ·log(T/2π)/2`, `λ > 1`, `T ≥ zetaNegativeCameraHeight` ⇒ depth `< exp(−c log³(T/2π))` for every zero at height `T`.
- Heat: `6600/9991` horizon; saddle `½/log(X/2π)`; pair-model collision below every scale; FE-pair squared gaps `≥ 0`
  ⇔ RH; actual half-Gaussian simultaneous-zero criterion and no-positive-time-collision ⇔ RH;
  Euler stages and finite real carriers real above `2πe^{W_a}`.
- Repulsion: polynomial collide-or-repel for finite Euler carriers, integral pure carriers, degree-two integral
  factors, the two-prime cusp carrier, a.e. Satake angle, a.e. value `a` of ζ; Liouville angles and two-prime real
  carriers defeat uniform repulsion; Bohr-lift classification of near-coincidences (consistent tangencies);
  near-coincidence ⇔ joint small values; depth of an FE pair read on the line; `E` dense `G_δ` null.
- Finite free: `N_d` exact count law, `N_d ≤ 300√(d log d)`, Cauchy bulk law, saddle identity; stability dictionary
  for zero-free half-planes; `ξ` on the stability boundary; explicit fixed-degree real-rootedness horizon.

Status: isolated-cluster identification is effective but supplies neither isolation nor a positive faithful mimic.
ZCG's actual collision criterion is live; small-time and bounded-height exclusion remain open. Camera gap signs
are diagnostics, not independent producers. Polynomial repulsion at the value zero remains open and alone
does not force real parts.

| | Obstacle | Strength |
|---|---|---|
| A38 | Sub-Weyl strip profile from the best known exponent pairs (horizon toward `½`; decides nothing about zeros) | — |
| A44 | Height law of `N_d`: which off-line zeros (by height) are counted at degree `d` (the outlier positions `x ≈ d/γ` in the saddle identity); explicit constants in `300√(d log d)` | — |
| A45 | Constants of the sharp-location theorem (`zetaNegativeCameraHeight`, the exponent `c`) toward the model constant | — |
| B14 | Actual half-Gaussian collision exclusion below the proved high-time horizon and in the bounded-height box | RH with established complementary region |
| B44 | Source-forced exact gap reality with isolation/global coverage; approximate readout on isolated clusters alone supplies no RH landing | method; full FE-pair reality RH |
| B52 | Stability of `R_d(Ξ·M_S)` at infinitely many degrees; equivalently `N_d = 0` for infinitely many `d` | RH |
| B53 | A source-faithful real-rooted (or HB-stable) finite free factorization of `J^{d,n}` other than the Γ ⊠ Θ split | method |
| B54 | `0 ∉ E`: distinct zeros of ζ at height `T` separated by `≥ T^{−C}` (open under RH; a.e. value of ζ has it; no implication for real parts; no route depends on it) | indep. |

### S11. Window visibility

Routes: every window route; WD, LA, ZCG through depth and density. Programme: WVL, SquareRootThreshold, DCI, ZCG.

Established [L]: closed-interval law; master law `k·pairEnergy(δ,a) ≤ L`; deep and cubic brackets; `e^{2(δ−σ)a}/δ`
unshielded-cluster law; tapered-crystal barrier; doubly-exponential non-locality; split-column certification;
contact law at `c log T`; explicit detector: `N(t, t+1] ≤ 240 log(|t|+3)`, positivity at level `a` confines
`|β − ½| < 10⁶exp(−a/(480000 log(|γ|+3)))`; at aperture `λL_T`, `λ > 1`, the cubic-logarithmic corridor
`exp(−c log³(T/2π))` (S10).

Status: classified in models; for ζ the laws require window positivity. Tower floors start at `a₀ > 181/500`,
but `a_∞` is unidentified and tower exhaustion is unproved. The sharp-location receiver converts positivity at aperture `≍ log T` into location and
produces no positivity.

| | Obstacle | Strength |
|---|---|---|
| A35 | Sharpen the explicit constants (`2²⁶·960`; detector `480000`, `10⁶`) toward the model constant `4δL/k` | — |
| A36 | Remaining onset-law items (general RvM shallow depth-mass bound under positivity; tapered crystal to `a ≍ log T`; two-bump interferometer) | — |

### S12. Finite free stability

Routes: LA, TH; supporting programme FFP.

Established [L]: Jensen dictionary `R_d(fg) = R_d(f) ⊞_d R_d(g)`; Walsh; Szegő; heat = `⊞_d` with Hermite;
`e^{(t/d²)D²}J_d` not real-rooted ∀t > 0; shift regime semicircular; source split `J^{d,n} = Γ ⊠ Θ` with Θ never
real-rooted; Dirichlet pieces never real-rooted; normalized Euler factors HB-stable with forced drift `θ_S/2`;
ζ/Gamma/pole pieces unstable; RH ⇔ infinitely many `J_d` real-rooted ⇔ mollified stability ⇔ bounded imaginary parts
(else linear growth `κd`); zero-free `Re s > σ` ⇔ Jensen polynomials of `ξ(σ + i·)` stable; Hurwitz form; genus-one
drift classification; `ξ` on the exact boundary; `R_d(Ξ)` a limit of rank-one zero pieces; **exact count**
`sup_d N_d` = number of off-line zeros, `N_d ≤ 300√(d log d)`; **bulk blindness** (Cauchy law at scale `½log d`,
shared with every `H_{−τ}`); saddle identity with error `≤ ½`.

| | Obstacle | Strength |
|---|---|---|
| B52 | Stability of `R_d(Ξ·M_S)` at infinitely many degrees | RH |
| B53 | A source-faithful stable finite free factorization of `J^{d,n}` other than Γ ⊠ Θ | method |
| B62 | `N_d` bounded (finite off-line support) | ≥qRH |

### Route-specific items

| | Obstacle | Routes | Strength |
|---|---|---|---|
| A17 | Tenth signed centre-mixed theta Hankel section at every `0 < a < ½` by the gamma-reserve allocation that pays the complete fifth even tail (difficulty unverified); every finite-rank repair tested has capacity `< 1` at some scale | TH | — |
| A18 | Jensen horizons, two-grid degrees, PF beyond 45 at the centre, the slice band beyond `709/50` | PA, LA, HCF | — |
| A19 | Certificates on the nine anti-diagonals `n ∈ {2,3,4,5,7,8,9,11,13}` where the pole pays nowhere | ACT | — |
| A20 | Mixed Schur debit; first-prime/coarse/polar costs | AIP, CHMD | — |
| B15 | Actual complete-history floors (FU, CFC, RP); SZ residual and LI lower-bound alternatives. EGC/FEL still need independent source landing | FU, CFC, RP, SZ, LI; EGC, FEL | RH for established receivers |
| B41 | Independent source forcing/landing; for live SEC/CDC/PCS the exact remaining bounds or vanishing are stated below | APF, EWJ, RFHM, WBF; SEC, CDC/BSH, PCS | method; instantiated live criteria RH |
| B66 | All-rank positivity of the signed centre-mixed theta Hankel sections at every `0 < a < ½` (ranks `≥ 10`) | TH | sub per rank; RH all |
| B67 | Hausdorff rows: nonnegativity on the finite initial segment `r < H(k)` for every `k` (RH ⇔ all rows) | PA | RH (all rows); finite per row |
| B68 | Heat-grid signs on pole-annihilating real polynomial squares at every degree, on both grids at independently fixed offsets | HCF | RH (all degrees) |

## 3. Live routes

Each entry: path; established; open; class; A; B.

### WL — Weil lag

- Path: actual prime-deficit critical energy bounded → RH.
- Established: bounded critical endpoint energy ⇔ RH; first cyclotomic band abscissa `2Θ`; gauge-torus exponents `[Θ, 1]`;
  the reflection-pair prime-count band ⇔ Weil-lag lower bound; deciding-input entry test; every classical producer
  excluded by an explicit theorem [L].
- Open: `∃C ∀t ≥ 0, E(t) ≤ C`, or signed square-root precision of one band; exponent `½` at the arithmetic point; an input
  that is locally pure and parity-breaking at unbounded length.
- Class P4. A: A25. B: B1, B26, B27, B32.

### RW — restricted Weil ground energy

- Path: `μ(a) ≥ 0` at every radius (≡ `a*(ζ) = ⊤`) → RH.
- Established: floors through the tower to `a_∞`; nonnegative apertures `[0, a*]`, with finite contact excluded from
  strictly positive apertures; de Branges chain before contact with
  explicit HB function, orthogonal increments, bounded exterior crossings, actual Riesz endpoint traces and fixed-aperture
  full-collar pointwise/scaled-L² limits; complete collar energy/mass `log(1/h) + O_a(1)`, including prime/polar terms;
  evaluation-Gram derivative inequality and kernel blow-up at contact; Riesz vectors bounded; two-site decision;
  below `log 4` two-weight band; Hardy
  interval; cone pinned at rate `e^{−c/1104}`; RH ⇔ `λ*(c) → 0` [L].
- Open: all-aperture sign or contact-excluding arithmetic kernel bound. Kernel absolute continuity, moving-support flux
  and Riesz-increment control remain; fixed-aperture traces are closed. Full increment/collar equation has unintegrated
  source [S]; aperture-dependent collar constants are not contact-uniform bounds.
- Class P1. A: A5, A7, A33, A35, A43. B: B1, B2, B3, B4, B5, B49, B51, B59.

### FU — signed prime scheduling

- Path: signed prime/Möbius history → one-sided sampled Abel bound → RH.
- Established: for each fixed `m`, one-sided boundedness of `A(j^m)/j^m` ⇔ RH; one controlled sample per backward
  window of length `N^{1−δ}` suffices. Exhaustive bounded-size prime blocks and insertion prefixes are paid at each
  block's fixed horizon [L].
- Open: samples across advancing clocks, retaining seed, drift, covariance and endpoints; fixed-horizon payment
  does not bound cross-clock debt.
- Class P4. B: B15.

### CFC — first-clock lower bound

- Path: first-clock sine coefficient bounded below on an aperture tail → RH.
- Established: exact tail criterion; unbounded below under ¬RH; phase-natural transport is the identity [L].
- Open: a lower bound retaining prime, archimedean and endpoint terms.
- Class P4. B: B15.

### RP — history floor

- Path: matched-quantile prime history → eventual linear defect floor → RH.
- Established: linear-floor criterion; low-LCM and copied-diagonal payment; sublinear floor impossible [L].
- Open: high-LCM pairs, moving core and singular-domain terms in one floor.
- Class P4. B: B15.

### PA — prime–archimedean passivity

- Path: prime − archimedean trace → current sign or subexponential mismatch → RH.
- Established: exact receivers; explicit `H(k) = explicitPrimeArchHausdorffShift k` with Hausdorff-row nonnegativity
  for `r ≥ H(k)`; RH ⇔ nonnegativity for every `k` and `r < H(k)`. HJ's continued prime−Gamma paired kernel has
  exterior scalar-diagonal sign ⇔ RH at radius `218/25` [L]; HJ is an alias, not another route.
- Open: the arithmetic sign on the finite initial segments, uniformly over unbounded `k`; finite per row is not a
  finite RH certificate. HJ alternative: `K(z,z) ≥ 0` at regular points with `0 < Im z < ½`, `Re z > 218/25`,
  or source Bernstein variation `TV(n)/qⁿ → 0` for every `q > 1`.
- Class P5 (order limit). A: A18. B: B67.

### MC — Möbius cancellation

- Path: Möbius/Liouville cancellation at half power → RH.
- Established: half-power and Redheffer criteria; squarefree prime complex ≃ wedge of spheres; bounded pronic energy;
  Möbius exponent Haar-a.e. `½`, Baire-generic `1`; explicit exponent-`½` gauge; flip points `max(θ, Θ)`; raw `μ/λ`
  second moments unbounded in length at every large height; Type I/Type II parity blindness [L].
- Bounded undamped Hilbert form is impossible; subpower growth is the receiver. Alternatively, arbitrarily small
  `ε > 0` with `sup_T E_ε(T) < ∞` ⇔ RH; constants may depend on `ε` [L].
- Open: trivial-gauge half-power cancellation or those cofinal damped bounds, including the signed long-modulus tail.
- Class P4. A: A21. B: B26, B27, B32, B36.

### TT — theta tail / Wold

- Path: actual theta/Wold residual → bounded weighted endpoint energy for every `0 < t < ½` → RH.
- Established: natural-weight residual decays `O(exp(−c√log N))`; `D_t + Q_t/2 = endpointEnergy_t/2 ≥ 0`.
  Boundedness for each `0 < t < ½` ⇔ RH; Φ-Doob identities retain all reflected-prime terms [L].
- Open: for each `0 < t < ½`, some `C_t` bounds `D_t(N) + Q_t(N)/2` for all `N`, with literal weights
  `(n+1)^(2t)`. Missing upper bound, not sign; endpoint `t = ½` fails. Odd-sign alternative overlaps OWU.
- Class P1 (odd-sign branch); endpoint-energy receiver. B: B1, B3, B4, B5, B49.

### LA — Jensen line anchor

- Path: actual Ξ Jensen polynomials → sublinear upper imaginary-root growth / all-root reality → RH.
- Established: every fixed Jensen degree real-rooted beyond an explicit shift horizon; RH ⇔ infinitely many `J_d`
  real-rooted. For a fixed finite Möbius mollifier, `σ > 0` and any phase, sublinear upper imaginary-root growth
  along infinitely many reversed Jensen degrees ⇔ RH; ¬RH forces eventual growth `≥ κd`.
  `N_d` nondecreasing, `sup_d N_d` = off-line count, `N_d ≤ 300√(d log d)`, `≥ d − 300√(d log d)` distinct real roots;
  Cauchy bulk law shared with every backward heat flow [L].
- Open: actual sublinear maximal upper-root-height bound or all-root reality. Bounded `N_d` gives only finite
  off-line support, not extinction; bulk reality supplies neither. Heat descent belongs to ZCG.
- Class P5. A: A18, A44. B: B52, B62.

### ZCG — zero-configuration geometry / heat descent

- Path: actual ξ half-Gaussian source → no positive-time real collisions → RH.
- Established: for `Q = halfGaussTransform(t, xiLine X)`, collision ⇔ `Re Q(0) = Im Q′(0) = 0`.
  No positive-time collision ⇔ RH; at large `X`, `t ≥ (6600/9991 + ε)/log X` excludes collisions [L].
- Open: simultaneous-zero exclusion in the remaining small-time region and bounded-height box. Below
  `1/(2log(X/2π))`, saddle control requires critical-strip cancellation. Camera readout supplies neither cluster
  isolation nor a positive faithful mimic; almost-every-fibre repulsion does not decide ζ's zero fibre.
- Class P5. A: A38, A45. B: B14, B44; B54 is support, not an RH forcing mechanism.

### TG — topological sub-unit gate

- Path: actual anchored cubic defect → trace norm `< 1` → integer zero count vanishes → RH.
- Established: defect constructed and trace class; exact integer trace, enclosed multiplicity ≤ trace norm;
  endpoint and Gaussian central-gap receivers [L].
- Open: for every formation rectangle `R`, some `x > 0` has `‖anchoredCubicDefect R x‖₁ < 1`. Alternative:
  bounded centered boundary-argument `L¹` oscillation along some `x_k ↓ 0` on every required circle; this scalar
  Gaussian passage needs no matrix construction. Scalar prime budget `< 1` is not a cubic trace-norm bound.
- Class P4 (inner caps). B: B10, B19.

### HF — Hodge / Hecke / complete cells

- Path: complete arithmetic form `≥ 0` → Hodge index → RH.
- Established: S1 in full; single-prime stage transport ⇔ RH; unconditional transport across `p = 2`; Dirichlet-shift
  companions reduce every long window to its head `windowThreshold(log d)` (unconditional for `d = 2` at every aperture
  and ratio); joint periodic windows PD iff jointly independent; `windowThreshold = ⊤` through `2a_k` for every `k` [L].
- Every fixed ratio has a positive growing low packet; cofinal `xiDampedSourceWork(n+4) ≤ 2` ⇔ RH [L].
- Open: full-space eventual sign at `c = 2K(log N)^(1/8)` for every `K > 0`, or that cofinal source-work ceiling.
  Full complement and source-kernel payment remain; far-complement loss `O(c)` exceeds `O(log N/c⁷)` at large ratios.
- Class: sign content P1; named count-only shortcuts obstructed; floor layer size-only.
  A: A1–A4, A9, A11, A23. B: B1, B2, B6, B7, B8, B9, B10, B11, B12, B16, B33, B34, B35, B40, B55.

### CHMD — causal hyperbolic–modular duality

- Path: one-sided bounded prime wave or odd Doob half-threshold bound → RH.
- Established: wave/Doob receivers; Haar transport; all-detail prime–pole cancellation `O(exp(−√log Y/92160000))` [L].
- Open: one-sided boundedness of the unnormalized prime wave, or the complete odd sign.
- Class P1 (odd sector). A: A20. B: B3, B12.

### TH — theta Hankel ranks

- Path: signed centre-mixed theta jets → all-rank Hankel positivity → RH.
- Established: rank 9 PD for `0 < a < ½` and `I₈(a) > 0`; complete fifth even native tail PD at every cutoff `r ≥ 0`
  (first-atom incomplete-gamma reserves `½ + 3/(8q) + 3/(32q²) − 3/(128q³)` pay all ordered pairs and the remainder;
  rational Schur certificates to degree 70); native fifth even section strict from `q ≥ 5` (floor `49/4000`); every
  finite-rank fixed, coherent, quartic or truncated-quartic repair fails at an exact scale (capacities `< 1`) [L].
- Open: rank 10 and all ranks: full signed-tail positivity at every `0 < a < ½` or a rank-uniform allocation law.
- Class P5 (rank limit; one-centre moment problem). A: A17. B: B66.

### RN — renewal

- Path: two-ended theta renewal → exclusion of joint energy/cross-flux nodes → RH.
- Established: compact cone-preserving operator; `det₂` gives denominator `D`, not Ξ. Two ends recover Ξ with
  multiplicities; full-divisor zeros are exactly joint nodes. Actual `D` has infinitely many nonreal zeros,
  spectrum is nonreal and loop Pick index is infinite in both signs [L].
- Open: joint-node exclusion for `0 < x < ¼`, `y > 0`, or all-profile Gamma/polar jump energy ≤ prime jump energy.
  This signed comparison overlaps RW; cone positivity does not supply it. `ThetaBoundaryDyadicClassification`
  realizes every negative odd winding in its stated dyadic loop class, not an identification with actual renewal feedback [L].
- Class P1 (energy comparison); joint-node receiver. B: B1.

### WD — Ward / collision / window energy

- Path: source current/window energy → collision charge `< 2`, all-resolution sectoriality, or cofinal long-mollifier
  moment control → RH.
- Established: S6 [L]: inner-cap flux = off-line generating function; every stage receiver an exact zero-free statement;
  moment `→ 1` ⇒ clustering; excess `K₀/log T` ⇒ `D_zero ∧ D_win` (real and complex); dyadic long-mollifier bound ⇒
  eventual depth `< 1/(2θ₁) + ε`, a nontrivial strip only when this is `< ½`; cofinal bound ⇒ RH.
  Shifted-defect detectors at scale `V/log V` ⇒ `D_win` (sharp scale); root model separates `D_win` from every proportion
  and exponential-rate statement. Normalized unit-bounded excess `≤ K₀/log T` requires
  `log N ≥ log²T/(6K₀) − (4/3)log T`.
- Integrated real/complex prefix-spike bounds control off-line occupied windows by critical-line second moments,
  not critical-line proportion; polynomial prefix cancellation leaves a `log V` loss [L].
- Open: an actual upper bound for a long mollified second moment (B64, B65); zero-rate right-port control; density
  branch needs vanishing cluster tail and depth decay at rate `log log V`. Necessary length is not attainability;
  finite/shallow exceptions still need exclusion.
- Class P4 (inner caps; mean-value face); density branch sub. B: B19, B20, B21, B22, B23, B64, B65.

### LI — paired Li and Cayley ladders

- Path: prime − Gamma history floor / Cayley ladder positivity → RH.
- Established: guarded history-zero set finite, RH ⇔ empty; ¬RH ⇒ the actual-clock primitive escapes to `−∞`; RH ⇔
  eventually bounded below; Cayley ladder = Toeplitz ladder of `2λ_n`; RH ⇔ every ladder NSD on primitive vectors ⇔
  entrywise `≥ 0`; paired Li coefficients never tend to `0` [L].
- Alternative receiver: for every `ε > 0`, response `R(t) ≥ −C_εe^(εt)` eventually [L].
- Open: Li positivity at every order, actual primitive lower bound or that subexponential response floor.
  Finite guarded history-zero set is not finite off-line ζ support.
- Class P4 (Li form of Σ1). B: B1.

### SZ — Suzuki screw

- Path: complete Ward/Abel residual bounded below/bounded → RH.
- Established: Suzuki first variation of every Lipschitz compact source = complete Weil energy; RH ⇔ nonnegative first
  variation on factorial-tent patterns ⇔ eventually on grid-tent patterns; unconditional deficits on `[−3/10, 3/10]`,
  odd tests on `[−181/500, 181/500]`, dyadic blocks, polynomial windows, lacunary unions [L].
- Coefficient-faithful completed Abel source `A_N` is constructed; boundedness ⇔ RH. Canonical signed
  correction/core → 1; aligned Gamma-completed energy has the same receiver [L].
- Open: `sup_(N≥2) abs(A_N) < ∞`, complete first-variation sign or rectangular Ward lower bound.
  Leading compensation does not bound the remaining signed residual.
- Class P1 (Krein–Schur face of the window form). B: B1, B51.

### PM — Gauss–Mayer physical realization

- Path: faithful scattering source → Krein/Lewis positivity or pole exclusion → RH.
- Established: S9 [L].
- Open: independent arithmetic `D_s ≥ 0` at every upper resonance or complete renormalized Krein positivity.
  Coefficient-space completion is closed; physical mixed-parameter realization and signed-form descent remain.
- Class P3. A: A14, A15. B: B38, B39, B40, B46.

### PTR — cosine-source zero-loss / photonic realization

- Path: actual `A_h = cosTransform(Φ cosh(hu))` → collision-free descent in `h` → RH.
- Established: exact nonlocal sech handoff to Ξ; strict Laguerre inequality `A_h′² − A_hA_h″ > 0` for `h ≥ ½`.
  The same sign for every `0 < h < ½`, `x ∈ ℝ` ⇔ RH; no real double zeros already suffices [L].
- Open: strict sign or collision exclusion in the open depth band. Independent prime-faithful lossless stack
  remains unconstructed; generic stacks and fixed-gap ports do not prove the actual source inequality.
- Class P5 (source continuation); independent physical realization B40.

### JAS, CTF, PBM, RB — one-sided counts

- All four are identified with the reflection-pair prime-count band and with each other [L: SWC].
- JAS: square-shell Riesz bounds on infinitely many `m` ⇔ RH; open: uniform arithmetic control. B: B26.
- CTF: bounded real rows reach every tolerance ⇔ RH; sawtooth defect identity; every off-line zero pins a Gram floor;
  linear Möbius taper isolates the Chebyshev error, bounded or subpolynomial dyadic defect ⇒ RH; sharp Möbius
  truncation never closes the defect. BSY integral `I = ∫log‖ζ(½+it)‖/(¼+t²)dt` is a nonnegative zero sum,
  `I ≤ 0` ⇔ RH [L]; open: vanishing-error rows, tapered-defect upper bound or BSY sign.
  FEL's theta-history producer remains candidate. B: B26.
- PBM: regularized prime-zeta convergence right of `½` ⇔ RH; open: coefficient cancellation. B: B26.
- RB: eventual Robin/Nicolas ⇔ RH without a `Θ < 1` premise; colossally abundant and `lcm(1,…,n)` reductions [L].
  Open: eventual extremal divisor-sum inequality or `robinLcmDefect(n) ≤ 1/(√n log n)`. B: B26.
- Class P4.

### HCF, XN, BAG, EWU, GTA, OWU

- HCF: heat explicit formula and two-grid criterion at independently fixed offsets; every off-line zero detected at
  explicit finite degree on `log 2` or `log 3`, heat mass `≤ 6/h` [L]. Open: source moment sign on every real
  pole-annihilating polynomial square on both grids; all degrees, not all offsets. Orthant positivity is only
  a small-positive-time result, not an all-time sign (KR-HFR). Class P5.
  A: A18. B: B68.
- XN: coverage/self-map criterion; nonnegative Laplacian of the interior margin [L]; open: an actual covering.
  Class P5.
- BAG: actual-flow/head-target transfer closed; cutoff-uniform positive Haar target mass at every tolerance on every
  doubled disc in `½ < Re s < 1` ⇔ RH [L]. Open: that uniform mass as cutoff → ∞. Weaker paired receiver needs
  both all-zero approach at each fixed depth and arbitrarily high returns on off-line-zero discs. B: B36.
- EWU: even sign ⇔ Hamburger moments ⇔ reflected trivial-zero form; neutral signed even theta gauge represents the even
  sector on every window; Markov exactly to `log ρ`, frustrated in every sign gauge beyond; gauge freedom only in the
  pole direction. Attained blind minimum `≥ 1/20` for `a ≤ (log 2 + 1/50)/2` [L]; open: blind minimum `≥ 0`
  beyond that interval, or `2V ≤ J_{M⁺}` on every window. Class P1 (even sector). A: A5, A33. B: B1, B3, B5, B49.
- GTA: canonical quartic Schur charge and strong finite-prefix convergence; full-mode compactness and finite-prefix
  operator-norm convergence each ⇔ RH [L]. Open: for every `ε > 0, N`, some `k ≥ N` admits a Schur packet of
  charge `< ε`. Ordinary skew energy has a strictly positive limit, refuting that producer, not the quartic receiver.
  Class P5 (compactness/cofinal charge).
- OWU: odd ⇔ shifted Hamburger ⇔ antireflected form; odd unit window ⇔ `w₂ ∈ unitBandWeights`. Actual odd form is
  frustrated in every sign gauge whenever a negative prime reflection acts; globally admitted weights are eventually
  odd-frustrated with weight-dependent onset, not a common finite-cone `½log 2` threshold. Variance retention
  necessary above `273/400` [L]. Open: sign at every aperture
  on compact C² real odd `F` with `∫F(x)sinh(x/2)dx = 0`; this restricted family suffices, without full complex tests.
  Class P1 (odd sector). A: A5, A33. B: B1, B3, B4, B5, B49.

### SRT, ACT, AIP — complete atomic matrix

- SRT: full-family/index receivers; two real parameters decide the line; split-column receiver; closed-contact
  receiver; distinct-cluster threshold; explicit all-height negative-test horizons; symmetric ξ-mass bounds with
  explicit height; **sharp location at aperture `λ·log(T/2π)/2`, `λ > 1`** [L]. Open: complementary-window sign,
  high-zero tail and source-kernel payment at every ratio. The stated cubic-log detector already assembles its tails;
  general schedules still need full payment. A: A1, A35, A45. B: B6, B7, B12.
- ACT: single-shift receiver `Ẑ(m_au) = 2S_a − D_a + 8V_c + 8τ_cA₂`; shifted ground states exact on every window;
  anti-diagonal classification [L]. Open: one shift, uniform in profile, paying `D_a` with retained variance.
  Class P1. A: A19. B: B1, B3, B5.
- AIP: exact allocation/decomposition; actual signed cost `O(e^(r−c√r))` times Sobolev mass; small-K full-space
  and all-R low-block positivity; capacity `log log N + O(1)` [L]. Open: for every `σ > 0`,
  `abs(reflectedPrimePolarCost(F,r)) ≤ C_σe^(2σr)(¼∫F² + ∫F′²)` for every odd compact C² `F` supported in `[−r,r]`.
  Packet branch still needs effective RH-complete schedules and full complementary payment.
  A: A1, A4, A9, A20, A43. B: B6, B7, B8.

### SC — Stokes/Witt–Krein

- Path: glued affine index `≤ 1` / bounded Gaussian-damped two-prime coupling → RH.
- Established: glued index `κ_ζ + 1`; damped cone ⇔ RH; the damped coupling is an arithmetic heat average of the
  complete compact-test Weil functional [L].
- Open: an arithmetic bound for the damped coupling, sublinear tensor loss, or glued index `≤ 1`.
- Class P4. A: A11. B: B1, B9, B10, B12, B30, B31.

### ACS — arithmetic Castelnuovo–Severi effectivity

- Path: actual Gamma/Lévy/horizon/Chebyshev source energy → all-aperture Bézout → RH.
- Established: concrete exact source cone and all-aperture Riemann–Roch; Bézout/ampleness ⇔ source-energy
  nonnegativity on every aperture ⇔ RH [L]. Criterion overlaps HF/WL/AIP.
- Open: `criticalDeficitSourceEnergy(r,(0,0,f)) ≥ 0` for every `r > 0`, `f ∈ realTestsAt r`.
  Source construction is closed; independent count/height/Rosati production of its sign remains open.
- Class P1 (source sign). B: B1, B34; named count-only shortcuts do not retire this criterion.

### SEC — adjacent prime seam / time-one Fock bound

- Path: actual prime−Gamma seam → factorial jet-energy bound at ξ zeros → RH.
- Established: every open-strip seam admitted in time-one Hilbert space; prime Dirichlet transform `F_ρ`
  identified. At any fixed `x₀ > 1`, `∀ρ, sup_N Σ_(n<N) abs(F_ρ^(n)(x₀))²/n! < ∞` over ξ zeros ⇔ RH [L].
- Open: this per-zero factorial-Fock bound; constants may depend on `ρ`, so no uniform zero bound is needed.
  Hilbert admission and asymptotic seam smallness do not supply it or exact adjacent compactness.
- B: B41 (actual bound, not source construction).

### CDC — constitutive dagger / BSH mate curvature

- Path: actual source-metric gain → marked-repair equality at ξ zeros → RH.
- Established: Euler-face metric, purified gain, curvature identification and calibration constructed;
  canonical potential fixed before zero selection. At `N = 1, n = 2`, marked-repair equality at every ξ zero
  suffices; BSH purified-curvature vanishing is the same grade criterion [L].
- Open: `RepairProofErasureConsistent` for that potential at every actual ξ zero, equivalently purified gain 1.
  Metric construction and finite trace identities do not force equality; full semantic descent is stronger than needed.
- B: B41; BSH is an alias, not independent forcing.

### PCS — singular prime co-shift

- Path: actual all-prime ground profile → reflection-odd singular class vanishes at ξ zeros → RH.
- Established: concrete co-shift/ground profile and RH-equivalent reflection-odd quotient criterion;
  finite-prime cutoffs converge strongly with persistent norm/ideal gap [L].
- Open: for every ξ zero `ρ`, `(n ↦ n^(−ρ) − n^(−(1−conj ρ))) ∈ ℓ²`. Independent source differential forcing
  remains open. CTF transport must retain the nonzero shift defect; injective literal intertwining is impossible.
- B: B41; quotient equality is a criterion, not a separate arithmetic mechanism.

## 4. Candidates

Nine candidates; an unproved final estimate alone does not demote an established source criterion.

| Candidate | Established | Promotion gap | Strength |
|---|---|---|---|
| APF | Source-first cycles and countable prime/grade/cap trace reconstruction on real Ξ labels [L] | Independent full-divisor exhaustion and RH landing; real-label reconstruction does not detect arbitrary off-line zeros | B41 |
| EGC | Complete zero-pair contour sum; cofinal admissible contours and vanishing mass-subtracted inner remainder; raw Gamma baseline persists [L] | Height-fibre isolation/global outer landing; inner cancellation counts every enclosed copy | B15, conditional landing |
| EWJ | All-depth reporter, compact-quotient character, multiplicity transport, strong prefixes; norm exhaustion iff `c = 0` or `−a+b+2d = 0` [L] | Faithful endpoint admission outside the blind plane; existing transverse norm exhaustion is false | B41 |
| FEL | Theta probability/KL and conditional entropy accounting; BSY criterion supports live CTF [L] | Predeclared calibrated source/history forcing BSY sign; adaptive bookkeeping supplies no such history | B15, conditional landing |
| IRK | Integral finite-idempotent traces, actual Meyer–Ξ finite free resolution and boundary trace classification [L] | Source-faithful projective/descent lift identifying analytic trace with Chern charge; free resolution is not projectivity | method |
| MSC | Unweighted critical discrepancy in `L²`; summatory transport preserves strict-right divisor multiplicity/conormal [L] | Sonin/Weil-sign landing; literal-column Bessel realization confined to `Re ρ > 1` | B1, conditional landing |
| RFHM | Full support/phase/grade admission, forward creation and strong cutoff exhaustion [L] | RH-sufficient source phase/depth orientation; energy loses grade, positive-coordinate ancestry sewing kills nonempty-support outputs | B41 |
| W1C | Finite ferromagnetic Lee–Yang receiver; convergence to Ξ/Ξ(0) on one real interval or all-moment convergence suffices [L] | Independent finite nonnegative couplings/masses with that convergence, or positive arithmetic reflection form; no slow-field convergence requirement | B40 |
| WBF | Gram determinants recover coefficient magnitudes/phase-gauge class; relative completion iff Hilbert–Schmidt weight [L] | Arithmetic certificate stream and faithful Ξ/Weil landing; magnitude recovery does not orient phase | B41 |

### Supporting programmes — ADO and FFP

ADO supplies finite-carrier and almost-every-fibre repulsion, not ζ zero-fibre repulsion or an independent
real-part selector (S10; B54).

FFP supports LA/TH:

- Path: Ξ (or `Ξ·M_S`) → real-rooted / Hermite–Biehler-stable Jensen polynomials at infinitely many degrees,
  certified by finite free convolution of stable source pieces → RH.
- Established: S12 [L].
- Obstructions: the tested source-faithful pieces except the Möbius Euler side are unstable; the Gaussian component is
  `o(d⁻²)`; the mollified criterion is a receiver whose converse does not use the mollifier; the bulk of the roots obeys
  a universal law shared with flows that have non-real zeros, so only the `o(d)` outliers carry arithmetic, and their
  count is the off-line zero count itself.
- Open: another source-faithful stable factorization or actual all-root control; the criterion alone supplies neither.
- Obstacles. A: A44. B: B52, B53, B62.

## 5. Decisive wall per route

| Wall | Routes |
|---|---|
| P1 — signed criticality, `a*(ζ) = ⊤` (≡ `1 ∈ ℋ(c)` ∀c ≡ `λ*(c) → 0`); kernel absolute continuity/contact-uniform bounds remain separate analytic gaps | RW, EWU, OWU, ACT, CHMD, TT (odd branch), SZ, RN (energy comparison), HF, ACS; MSC needs sign landing; CWS, WTZ, DZG, GWZ, CSTW, SWC, FADF, WVL, CHT |
| P1 at large ratios — untwisted windows (`windowThreshold ≡ ⊤`) | HF, SRT, AIP, SC; CACT, AHD, CSAR, ACPL |
| P4 — one-point square-root precision / actual energy and history bounds; long moments imply occupancy or RH only under their stated hypotheses | WL, MC, PBM, RB, JAS, CTF, LI, SC (coupling), FU, CFC, RP, SZ (Abel), TT (endpoint); WD (mean-value face); EGC/FEL need source landing |
| P4 — inner caps; sub-unit cubic trace norm or bounded Gaussian passage | WD, TG |
| P5 — all-rank/all-degree sign, cofinal quartic charge, actual source continuation; Jensen outlier control | TH, HCF, PA/HJ, GTA, LA, XN, ZCG, PTR; FFP support |
| P2 — prime-blind positivity / calibration (sign of `λ*(c)`) | PBAP, CHT |
| P3 — independent resonant/Krein sign; physical signed descent | PM; W1C positive-carrier candidate |
| Γ — trivial-gauge cancellation / uniform positive head-target mass | MC, BAG |
| Zero-parameter criteria — per-zero Fock bound, canonical proof-erasure, reflection-odd `ℓ²` | SEC, CDC/BSH, PCS; criteria are live, independent forcing open |
| Independent source landing / orientation | APF, EGC, EWJ, FEL, IRK, MSC, RFHM, W1C, WBF |
| Scoped count/realization obstructions, not a blanket geometry no-go | ACS/HF count-only shortcuts; IRK still needs projective descent |
