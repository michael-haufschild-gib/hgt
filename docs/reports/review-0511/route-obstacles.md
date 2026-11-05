# Route obstacles — status quo

Scope: 38 live route formulations, 9 candidates and their supporting programmes, as classified in the
[frontier map](../rh-current-frontier-map.md) and [scoped obstructions](../rh-killed-routes.md).
For every route: path, what is established, the open estimate, the
mechanism class, the obstacles that are **(A) just work** and the obstacles that are **(B) open mathematics**
(no known solution).

Source checkpoint: `9ebb2bd387`.

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
`a₀ = successorWeilFloorAperture`, `181/500 < a₀ < 181/500 + 5×10⁻⁷`; `a_∞ = lim a_k`, floors
`(1/20000)/2^k`, with `a_∞−a₀<10^(−7,800,000)` [D]. `N_d` = number of non-real roots of the degree-`d` reversed Jensen
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
| Each fixed rung follows from finite RH verification: window `a` from height `T₀(a)`, `log(T₀/2π)≳2Σ_{n≤e^{2a+s}}Λ(n)/√n`; TH rank `N` from height `≈CN`. RH verified to `3×10¹²` gives `a*(ζ)≥≈1.9` | [D]; TH mechanism `current_nonneg_on_frequency_window` [L] | finite windows and ranks are verification tasks and decide nothing about RH |
| One constant `−C∫F²` at all apertures, or `−C_σe^{2σr}∫F²` for all `σ>0`, implies RH; power saving against `−Cre^r` gives a strip | SquareRootThreshold [L] | the target is a budget, not an exact sign |
| RH ⇔ prime-blind positivity; blind energy `(1/π)∫\|𝓜f\|²(θ′+1−Re ζ(½+it))`; Carlson threshold `e^{(π/2)\|t\|}` | RHTower [L] | the problem can be stated with Gamma, pole and `log n` alone |
| `c d²/log X ≤ Λ_X ≤ (6600/9991+ε)/log X`; horizon `≈4μ(½)`, saddle `½` | RHTower, ZCG [L]; [D] | small-time ZCG contains strip-strength statements |
| First-atom center tails PD at every rank; fibrewise full tails negative at `b=2γ₄` for small `r` | CAF [L]; [N/D] | rank-uniform TH must keep the aperture weight |
| Precontact sampling atoms `1/K_a(x,x)` are positive on-line mimics; mimic at `a` ⇔ window at `a` | [D] | ZCG's mimic hypothesis is RW's sign |
| Increment bound `(log(1/h)−E(a,c))‖ΔE_z‖²≤` residual mass, with `E` containing `2C²/μ(a)`; translation isometries | CSTW [L] | kernel regularity is closed in substance [D]; contact control is the open part |
| RH ⇔ `a*(ζ) = ⊤`; nonnegative half-widths form `[0, a*(Z)]`; off RH `a*(ζ)` = contact, attained with zero ground energy; strictly positive apertures exclude contact; `windowThreshold A = ⊤ ⇔ A/2 ≤ a*(ζ)`; `windowThreshold A = ⊤` for `A ≤ 2a_k`, every `k`; hence `a*(ζ) ≥ a_∞`, numerically `a₀` | WVL, AHD, AIP [L]; [D] | every window route measures one number |
| Single-prime stage transport for all `A` ⇔ RH; Dirichlet-shift stabilization for every divisor `d` ⇔ `R₁(log d) = ⊤` ∀d ⇔ RH; unconditional for `d = 2` at every aperture; joint periodic windows PD ⇔ joint independence | AHD [L] | HF's threshold is the onset aperture; long windows reduce to head windows |
| Positivity at aperture `λ·log(T/2π)/2`, `λ > 1`, `T ≥ zetaNegativeCameraHeight(λ, c)` ⇒ every zero of ζ at height `T` has depth `< exp(−c log³(T/2π))`; no on-line mimic, no separation premise | ZCG SharpLocation [L] | the excluded-depth corridor is cubic-logarithmic and explicit |
| Below `log 5`: window positivity ⇔ the `{2,3,4}` sliver band (only `n = 2` in the half-window diagonal; the three kicks use `< 0.991` of the Lévy energy) ⇔ the joint neutral-gauge/shifted-ground-state certificate | SWC [L] | the first stages are an exact three-power problem |
| `W(f ± f∘R) = 2W(f) ± 2𝒞_m(f)`; `W(f) − \|𝒞_m(f)\| = ½min(W(G₊), W(G₋))`; coupling truncates to `2 ≤ n ≤ e^{2c}`; collar floors `weilFloorTowerConst k ∫f²` for `c ≤ a_k` | SWC [L] | the minimal object is a reflection pair |
| Arithmetic part is an optimal Hardy term for `H` iff RH; scaling optimality and criticality unconditional; `⋂_cℋ(c) = {1}` ⇔ RH | FADF [L] | Weil positivity is a critical Hardy inequality with a unique admissible multiple |
| On `𝒜(c)`: `\|λ(n) − Λ(n)\| ≤ C exp(Kn − c/1104)` for `c ≥ 2`, `2 ≤ n ≤ e^{2c−1/6}`; bands are intervals of width `≥ λ*(c)√n`; `λ*(c) ≤ K exp(3c − (π/6)e^{2(c−13/12)})` and `≤` the Gaussian ceiling for all weights; `λ*(a_k) ≥ weilFloorTowerConst k`; RH ⇔ `λ*(c) → 0` | CHT [L] | the cone pins every coordinate at an exponential rate while its margin collapses doubly exponentially |
| Datum `(β, s)` (pole weight, log-conductor): at `β = 1`, `s < 0` cones eventually empty; at `s = 0` nonempty cones force `β ≥ 1 − K exp(3c − (π/6)e^{2(c−13/12)})`; pole-free cones eventually empty for small `s`; critical log-conductor `= −λ*(c)`; the window reads the residue | CHT [L] | the datum of ζ is the critical point of the cone family |
| Before contact each window carries a complete Weil Hilbert space (de Branges space, explicit Hermite–Biehler function, unitary zero-moving, isometric inclusions); growing the window adds an orthogonal kernel increment; exterior crossings bounded; endpoint traces, collar equation and residual limits hold; finite contact forces a diagonal kernel to diverge | CSTW, CHT [L] | contact-uniform bounds remain open |
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
| B55 | Head-window thresholds `windowThreshold(log d) = ⊤` for every `d`; stabilization forces this threshold and follows from `windowThreshold(log d + ε) = ⊤`. For `d = 3`, the necessary aperture is `½log 3`; a positive margin suffices, and verified zeros supply it for small `d` [D] | RH |
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
- Weil symbol = logarithmic multiplier + bounded convolution; Riesz vectors bounded; Wiener–Hopf factorization of the
  archimedean symbol with positive causal kernel; half-line Green operator `CC*`; logarithmic form detects interval
  length.
- Exact collar equation, fixed-enclosure compatibility, strong residual limits, two-collar floor, increment bound and
  translation isometries [L]; absolute continuity follows [D]; contact-uniform arithmetic bounds remain open.
- Calibration cones `𝒜(c)`: convex, cylinders, each entering coordinate bounded, stage fibre a compact interval;
  sharp entry law; real tests decide; **effective uniqueness** at rate `exp(Kn − c/1104)`; bands are intervals of width
  `≥ λ*(c)√n`; **margin law** `λ*(c) ≤ K exp(3c − (π/6)e^{2(c−13/12)})` over all weights; `λ*(a_k) ≥ (1/20000)/2^k`;
  RH ⇔ `λ*(c) → 0`; datum classification (critical log-conductor `= −λ*(c)`); theta-smoothed pinning; quantitative
  Hamburger uniqueness (`η^{1/69}`).
- Below `log 4`: two-weight convex membership ⇔ Markov–Hankel pair ⇔ retained-variance certificates ⇔ Hodge index ⇔
  Künneth effectivity; neutral signed even theta gauge and shifted ground state exact on every window; below `log 5`
  the `{2,3,4}` sliver band; gauge freedom only in the pole direction; receding pockets conserve the outside deficit;
  odd variance retention necessary above `c = 273/400`.
- Floor tower `a_k`, strictly increasing, floors `(1/20000)/2^k`, on windows and reflection pairs; `a_∞−a₀<10^(−7,800,000)` [D].
- Perron sign law; frustration localization; robust Perron costs height. Actual acting negative prime reflections
  force odd frustration; each globally admitted weight is eventually odd-frustrated. No common onset is asserted
  for all members of each finite-window cone.
- Trivial zeros paid by centre killing; `𝒥 = 𝒥_reg + 𝒦`; no point traces.
- Finite rational Hecke graphs decide correlation-form windows; exact Tate horizons through `log(81/16)`; positive Tate
  dimensions `[0, κ(A)]`, `κ(A) → 0`.

Status: the certificate format is exact on every window in both sectors; the cone is pinned at an exponential rate and
its margin collapses; what is open is the inequality the format states. Lean has no certificate for
`c ∈ (a_∞, log 2)`; verified zeros supply one (A46–A47) [D]. These windows carry no zero information (S11).

| | Obstacle | Strength |
|---|---|---|
| A5 | Certificate of `(w₂, w₃) ∈ belowLogFourBandWeights c` for `c ∈ (a_∞, log 2)`, by A46–A47 or Galerkin; margins `1.5×10⁻⁵` (odd), `5.6×10⁻⁸` (even) at `c = ½log 3`, `≈ 2×10⁻⁴` on the odd unit window [N] | — |
| A6 | Exact Tate horizons of the remaining stages below spread `6` | — |
| A7 | Closed form of the first-stage complement `Φ_ε` | — |
| A28 | Atomic-lattice bound `λ_max ≤ ½log N` | — |
| A33 | Lévy sector margins at `c = ½log 3` in both sectors [N] | — |
| A43 | Lean bound `weilFloorApertureTower k < 0.3621` from the explicit step (`a_∞−a₀<10^(−7,800,000)` [D]) | — |
| A46 | Verified-height window theorem: `RHVerifiedThrough T₀(a) → ZetaWindowPositive a`, by entire spectral cutoff, zero-side positivity below `T₀`, prime-side size above | — |
| A47 | Lean-certified `RHVerifiedThrough T` for `T≈10²–10³`, from `hardySEM` brackets plus a Turing count | — |
| A49 | De Branges sampling theorem; discharge `zeta_positive_mimic_weighted_count` at precontact apertures | — |
| A50 | Lean assembly of kernel absolute continuity and `G′=\|τ_L\|²+\|τ_R\|²`; Krein-type system | — |
| B2 | Kick admission at every stage | RH as induction; each stage sub |
| B3 | Frustration domination: the neutral signed theta-gauge inequality `2V ≤ J_{M⁺}` (even) and the shifted-ground-state inequality (odd) on every window | RH; fixed length sub |
| B4 | Structural certificate of the odd unit window (`w₂ ∈ unitBandWeights`) | sub |
| B5 | Structural certificate below `log 4` (`a*(ζ) ≥ log 2`), the prime `3` paid by sign | sub; finite window, no door |
| B56 | The `{2,3,4}` sliver band below `log 5` (`a*(ζ) ≥ ½log 5`) | sub |
| B49 | Signed ground-state structure past `log ρ` compatible with unswitchable frustration | method |
| B51 | Contact-uniform arithmetic estimates excluding finite contact; every proved bound carries `2C²/μ(a)` | RH |
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

Status: classified in models; for ζ the laws require window positivity. Tower floors stay at `a₀ > 181/500` up to `10^(−7,800,000)` [D]. The sharp-location receiver converts positivity at aperture `≍ log T` into location and
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
| A17 | Tenth signed centre-mixed theta Hankel section at every `0 < a < ½`, by gamma-reserve allocation or A48 | TH | — |
| A48 | Finite ranks at all `a` from verified zeros; Vinogradov–Korobov collar from `current_nonneg_on_frequency_window` | TH | — |
| A51 | Heat horizon `(½+ε)/log X` on almost all heights, from mean values and the strip-profile law | ZCG | — |
| A52 | Explicit zero-free strip from a heat coefficient, via `exists_le_localNewmanConstant_of_offLine_zero` | ZCG | — |
| A53 | Lean certificate that `(Θ²)^(2γ₄)>0` makes a full-theta center tail fail at finite rank | TH | — |
| A54 | Verified-height bounds for PA rows, HCF degrees, Jensen degrees and Li entries | PA, HCF, LA, LI | — |
| A18 | Jensen horizons, two-grid degrees, PF beyond 45 at the centre, the slice band beyond `709/50` | PA, LA, HCF | — |
| A19 | Certificates on the nine anti-diagonals `n ∈ {2,3,4,5,7,8,9,11,13}` where the pole pays nowhere | ACT | — |
| A20 | Mixed Schur debit; first-prime/coarse/polar costs | AIP, CHMD | — |
| B15 | Actual complete-history floors (FU, CFC, RP); SZ residual and LI lower-bound alternatives. EGC/FEL still need independent source landing | FU, CFC, RP, SZ, LI; EGC, FEL | RH for established receivers |
| B41 | Independent source forcing/landing; for live SEC/CDC/PCS the exact remaining bounds or vanishing are stated below | APF, EWJ, RFHM, WBF; SEC, CDC/BSH, PCS | method; instantiated live criteria RH |
| B66 | All-rank positivity of the signed centre-mixed sections at every `0 < a < ½` | TH | RH |
| B69 | Unequal-atom payment with the aperture weight retained | TH | RH |
| B71 | Exact extremal blind test `Φ=Ξ·g` | PBAP | indep. |
| B72 | Floor `−Cexp(r−cr^α)`, `α>3/5` (beyond Vinogradov–Korobov) | window routes | sub |
| B73 | `Λ_X log X → 0` on density-one heights | ZCG | sub |
| B67 | Hausdorff rows: nonnegativity on the finite initial segment `r < H(k)` for every `k` (RH ⇔ all rows) | PA | RH (all rows); finite per row |
| B68 | Heat-grid signs on pole-annihilating real polynomial squares at every degree, on both grids at independently fixed offsets | HCF | RH (all degrees) |

## 3. Live routes

Each entry: path; established; **(a)** just work; **(b)** open mathematics.

### WL — Weil lag
- Path: bounded prime-deficit critical energy → RH.
- Established: bounded endpoint energy ⇔ RH; first cyclotomic band abscissa `2Θ`; gauge exponents `[Θ, 1]` [L].
- (a) Künneth/mixed jet calibration (A25).
- (b) `∃C ∀t, E(t) ≤ C`, or square-root precision of one band (B27); half-power at the trivial gauge (B32); a locally pure, parity-breaking producer (B26).

### RW — restricted Weil ground energy
- Path: `μ(a) > 0` at every radius → RH.
- Established: antitone attained minima; precontact de Branges chain; exact collar equation; strong residual limits; two-collar floor; increment bound; translation isometries; contact blow-up [L]. Bounded or subexponential floor ⇒ RH [L].
- (a) Lean: tower stall (A43); verified-height window theorem (A46, A47); absolute continuity and density identity (A50); sampling mimic (A49); `Φ_ε` (A7); constants (A35).
- (b) Contact-excluding arithmetic bound (B51), blocked because every bound contains `2C²/μ(a)`; all-aperture sign or subexponential floor (B1, B3); structural sign mechanism past `log ρ` (B49); decay law of the margin (B59).

### FU — signed prime scheduling
- Path: signed Möbius history → one-sided sampled Abel bound → RH.
- Established: fixed `m` one-sided criterion; one sample per backward window `N^{1−δ}`; fixed-horizon block payment [L].
- (a) None that moves the route.
- (b) Cross-clock debt across advancing clocks, retaining seed, drift, covariance, endpoints (B15).

### CFC — first-clock lower bound
- Path: first-clock sine coefficient bounded below on a tail → RH.
- Established: exact tail criterion [L].
- (a) None.
- (b) The lower bound with prime, archimedean and endpoint terms retained (B15).

### RP — history floor
- Path: matched-quantile history → eventual linear floor → RH.
- Established: exact linear-floor criterion; low-LCM payment; sublinear floor impossible [L].
- (a) None.
- (b) High-LCM pairs, moving core and singular-domain terms in one floor (B15).

### PA — prime–archimedean passivity (HJ alias)
- Path: prime−Gamma source sign → RH.
- Established: Hausdorff rows nonnegative for `r ≥ H(k)`; RH ⇔ initial segments; exterior diagonal criterion at `218/25` [L].
- (a) Row-by-row verified-height bounds and horizons (A18, A54).
- (b) Initial-segment signs uniformly in `k` (B67), or `K(z,z) ≥ 0` on the exterior sector.

### MC — Möbius cancellation
- Path: half-power Möbius/Liouville cancellation → RH.
- Established: subpower Hilbert form ⇔ RH; damped energy criterion; Redheffer/wedge dictionary; parity blindness of Type I/II [L].
- (a) Logarithmic two-point Chowla (A21).
- (b) Trivial-gauge cancellation (B32, B36); first cyclotomic mode (B27); signed long-modulus tail; parity-breaking producer (B26).

### TT — theta tail / Wold
- Path: weighted endpoint energy bounded for `0<t<½` → RH.
- Established: residual decay `O(exp(−c√log N))`; `D_t+Q_t/2 ≥ 0`; boundedness ⇔ RH; odd energy criterion [L].
- (a) None that moves the route.
- (b) The upper bound `C_t` for every `0<t<½`; odd-sign branch shares B1, B3, B4.

### LA — Jensen line anchor
- Path: Jensen polynomials real-rooted or sublinear root height → RH.
- Established: `N_d` nondecreasing, supremum is off-line multiplicity, `N_d ≤ 300√(d log d)`; bulk Cauchy law is blind; mollified dichotomy [L].
- (a) Height law of `N_d` (A44); finite degrees from verified zeros (A54); horizons (A18).
- (b) All-root reality at infinitely many degrees (B52); bounded `N_d` (B62, gives finite support only); finite-support extinction (B13).

### ZCG — zero-configuration geometry / heat descent
- Path: half-Gaussian source → no positive-time collision → RH.
- Established: collision ⇔ `Re Q(0)=Im Q′(0)=0`; `c d²/log X ≤ Λ_X ≤ (6600/9991+ε)/log X`; general strip-profile law; camera readout and sharp location; weighted mimic law [L].
- (a) Horizon toward `4μ(½)` (`≈0.619` with `μ(½)=13/84`) (A38); saddle horizon on almost all heights (A51); explicit strip from the heat coefficient (A52); mimic hypothesis discharged by sampling (A49); camera constants (A45).
- (b) Worst-case horizon to the saddle needs Lindelöf-strength control; below a fixed coefficient it forces a zero-free strip; all small-time and low-height collisions (B14, B44, B73). `0 ∉ E` (B54) is separate and decides no real part.

### TG — topological sub-unit gate
- Path: cubic defect trace norm `<1` → integer zero count vanishes → RH.
- Established: defect constructed, trace class; multiplicity ≤ trace norm; Gaussian passage criterion [L].
- (a) None that moves the route.
- (b) Trace norm `<1` on every rectangle, or bounded centered Gaussian oscillation (B19, B10).

### HF — Hodge / Hecke / complete cells
- Path: complete arithmetic form `≥0` → Hodge index → RH.
- Established: full-space PD through one small multiple; growing low packet at every ratio; joint periodic windows; Dirichlet-shift head reduction; `xiCopyTransverseEnergy ≤ 2 ⇔ RH` [L]. Heads for `d ≤ ≈50` follow from verified zeros [D].
- (a) Constants and profiles (A1, A2, A4, A9); Lean heads for small `d` via A46, A47; `𝔽_q` calibration (A11); strata (A23).
- (b) Full-space sign at one `K` past the size-only multiple (B7); far complement `O(c)` against `O(log N/c⁷)`; twisted sectors (B6); head windows for all `d` (B55); source-work ceiling; top coprime stratum (B11); Rosati/band poles (B34, B35).

### CHMD — causal hyperbolic–modular duality
- Path: bounded prime wave or odd Doob bound → RH.
- Established: wave and Doob receivers; normalized cancellation; nonfirst Gamma reserve [L].
- (a) Mixed Schur debit (A20).
- (b) One-sided bound on the unnormalized wave; complete odd sign (B3, B12).

### TH — theta Hankel ranks
- Path: signed center-mixed jets → all-rank Hankel → RH.
- Established: rank 9 at all `a`; logarithmic collar for every rank; first-atom center tails PD at every rank, `r ≥ 0` [L]. Integrated pair spectra have a positive radial factor times the log-ratio cosine: diagonal pairs positive, each unequal pair negative at some frequency [L]. Fibrewise full tails fail at `b=2γ₄`, small `r` [N/D].
- (a) Finite ranks at all `a` from verified zeros and Vinogradov–Korobov collar (A48); rank 10 (A17); Lean certificate of the tail failure (A53).
- (b) All ranks at every `a`, keeping the aperture weight, since fibrewise payment is false (B66, B69); unequal atom pairs carry the arithmetic.

### RN — renewal
- Path: two-ended theta renewal → no joint nodes → RH.
- Established: `det₂` gives `D`, not Ξ; two ends recover Ξ; energy comparison ⇔ RH; `D` has nonreal zeros [L].
- (a) None.
- (b) Joint-node exclusion on `0<x<¼, y>0`, or the energy comparison (B1).

### WD — Ward / collision / window energy
- Path: window energy or long-mollifier moments → RH.
- Established: inner caps read off-line zeros; moment `→1` ⇒ clustering; excess `O(1/log T)` ⇒ occupancy; cofinal prefix bound ⇒ RH; necessary length; root-model separation; detector sharpness [L].
- (a) Constants; Lean-level dictionary items.
- (b) Actual long-mollifier upper bounds (B64, B65); clustering (B20); `D_win` (B21); inner caps (B19); Hecke defect (B22); a distributional input (B23).

### LI — paired Li / Cayley ladders
- Path: primitive lower bound or Li sign → RH.
- Established: ladder = Li coefficients; RH ⇔ NSD on primitives; subexponential response criterion [L].
- (a) Finite ladder entries by verified zeros (A54).
- (b) Li positivity at every order, or the response floor (B1).

### SZ — Suzuki screw
- Path: completed Abel residual bounded → RH.
- Established: first variation = Weil energy; source `A_N`; signed compensation/core `→1` [L].
- (a) None that moves the route.
- (b) `sup|A_N|<∞`, complete first-variation sign (B1, B51).

### PM — Gauss–Mayer realization
- Path: scattering source → Krein/Lewis positivity → RH.
- Established: resonance ⇔ `ζ(2s)=0`; coefficient-space `Q=2Re[WH,WH]`; `D_s` is minus a weighted Hecke energy, zero iff `Re s=¼` [L].
- (a) Physical mixed-parameter realization and carrier identifications (A14, difficulty unverified).
- (b) Independent `D_s ≥ 0` or full Krein positivity (B38); selecting statistic (B39); positive physical carrier (B40); PM-native zero-free line (B46; A15 is its first attempt).

### PTR — cosine source
- Path: `A_h` collision-free descent → RH.
- Established: sech handoff; strict Laguerre for `h ≥ ½`; no double zero for `0<h<½` ⇔ RH [L].
- (a) None.
- (b) The sign at any `h<½`, a zero-free-strip strength step [D]; independent lossless stack (B40).

### JAS, CTF, PBM, RB — one-sided counts
- Established: all identified with the reflection-pair count band [L]. JAS square-shell criterion; CTF rows, BSY integral `=0 ⇔ RH`; PBM abscissa; RB Robin/lcm criteria [L].
- (a) None that moves these routes.
- (b) JAS uniform moving-window control; CTF vanishing rows, tapered defect or BSY sign; PBM coefficient cancellation; RB extremal inequality. All are B26.

### HCF — heat trace
- Established: any two primes, any offsets; negative test at explicit finite degree [L].
- (a) Finite degrees (A18, A54).
- (b) All degrees (B68).

### XN — Newton discs
- Established: covering-disc criteria; margin Laplacian nonnegative [L].
- (a) None.
- (b) An actual covering of every zero.

### BAG — self-return
- Established: flow/head-target transfer; uniform target mass ⇔ RH [L].
- (a) None.
- (b) Cutoff-uniform positive target mass (B36).

### EWU — even sector
- Established: Hamburger form; neutral gauge; Markov to `log ρ`; blind minimum `≥1/20` for `a ≤ (log 2+1/50)/2` [L].
- (a) Windows by verified zeros (A46, A47).
- (b) Blind minimum `≥0` at every aperture; `2V ≤ J_{M⁺}` (B3, B49).

### GTA — Schur charge
- Established: charge family; compactness ⇔ RH; trace cost `0` or `∞` [L].
- (a) None.
- (b) Cofinally small charge.

### OWU — odd sector
- Established: shifted Hamburger; unit window reads `w₂`; frustration; variance retention above `273/400` [L].
- (a) Unit window and `log 2` by verified zeros (A46, A47); sector margins (A33).
- (b) Sign at every aperture; structural unit-window certificate (B4, B5, B49).

### SRT — lag localization
- Established: full-family receivers; explicit horizons; sharp location [L].
- (a) Constants (A1, A35, A45).
- (b) Complementary-window sign, tails and source kernel at every ratio (B6, B7, B12).

### ACT — single shift
- Established: single-shift receiver; `{2,3,4}` band; anti-diagonal classification [L].
- (a) Nine anti-diagonals (A19).
- (b) One shift uniform in profile paying `D_a` (B1, B3).

### AIP — incidence
- Established: allocation; signed cost `O(e^{r−c√r})`; capacity `log log N+O(1)`; tower [L].
- (a) A1, A4, A9, A20, A43.
- (b) `C_σe^{2σr}` cost bound for every `σ` (B6–B8).

### SC — Stokes / Witt–Krein
- Established: glued index `κ+1`; bounded damped coupling ⇔ RH; heat-average form [L].
- (a) A11.
- (b) Arithmetic bound for the coupling; sublinear tensor loss; B9, B10, B30, B31.

### ACS — Castelnuovo–Severi
- Established: exact source cone; all-aperture Riemann–Roch; Bézout ⇔ RH [L].
- (a) A25, A31.
- (b) Source-energy sign; independent count/height/Rosati producer (B1, B24, B25, B34).

### SEC — seam / Fock
- Established: seam admitted; `F_ρ` identified; Fock bound ⇔ RH [L].
- (a) None.
- (b) Per-zero factorial bound (B41).

### CDC — dagger (BSH alias)
- Established: metric, gain, calibration; proof-erasure suffices [L].
- (a) None.
- (b) Equality at every ξ zero (B41).

### PCS — co-shift
- Established: profile; quotient vanishing ⇔ RH [L].
- (a) None.
- (b) `n^{−ρ}−n^{−(1−ρ̄)} ∈ ℓ²` at every zero; differential lift (B41).

## 4. Candidates

| Candidate | Established [L] | (a) Just work | (b) Open mathematics |
|---|---|---|---|
| APF | prime/grade trace reconstruction on real labels | none | full-divisor exhaustion and RH landing (B41) |
| EGC | double-Gaussian zero-pair contour; inner remainder vanishes | contour constants | height-fibre isolation; outer landing (B15) |
| EWJ | all-depth reporter; norm exhaustion only on blind plane | none | faithful endpoint admission (B41) |
| FEL | KL accounting; BSY criterion belongs to CTF | none | calibrated predeclared history forcing BSY sign (B15) |
| IRK | finite idempotent traces; Meyer–Ξ free resolution | none | projective lift identifying trace with Chern charge |
| MSC | unweighted `L²` discrepancy; conormal transport | none | Sonin/Weil sign landing (B1) |
| RFHM | support source; creation; strong exhaustion | none | RH-sufficient orientation law (B41) |
| W1C | Lee–Yang receiver; one-interval convergence suffices | none | finite ferromagnetic producer converging to Ξ (B40) |
| WBF | Gram recovers magnitudes and phase class | none | arithmetic stream and Ξ landing (B41) |

### Supporting programmes

| Programme | Established [L] | (a) Just work | (b) Open mathematics |
|---|---|---|---|
| PBAP (prime-blind) | RH ⇔ blind positivity; blind ζ dictionary; Carlson threshold; dilation family; Farkas tower | none | sign (B42); exact extremal test (B71); status of `PBAP(t)`, `t<1` |
| CHT | margin law; pinning; datum; bands | cone widths (A13) | margin decay law (B59) |
| FFP | see LA | A44 | B53, B62 |
| ADO | carrier repulsion; a.e. value; `E` residual | none | `0 ∉ E` (B54) |
| APR | necessary length; filters | constants | production at square-root precision (B26) |

## 5. Decisive wall per route

| Wall | Routes |
|---|---|
| Σ sign or subexponential budget | RW, EWU, OWU, ACT, CHMD, TT (odd), SZ, RN, HF, ACS, AIP, SRT, SC, LI, PBAP |
| Π square-root precision and long moments | WL, MC, PBM, RB, JAS, CTF, FU, CFC, RP, TT (endpoint), WD, TG |
| Continuation and all-degree sign | ZCG, PTR, LA, TH, HCF, PA, GTA, XN |
| Γ reflection and selection | PM, BAG, SEC, CDC, PCS |
| Missing source landing | APF, EGC, EWJ, FEL, IRK, MSC, RFHM, W1C, WBF |
