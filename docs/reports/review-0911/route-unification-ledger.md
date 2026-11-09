# Route unification ledger — status quo

The 38 live formulations and 9 candidates are faces of three core problems: **U-Σ** (sign), **U-Π** (precision and production) and **U-Γ** (selection, reflection and transport). Their RH-level endpoints meet at one object, and the corpus gives it a minimal form: **one inequality per prime**. For every prime `p`, the smoothed prime count in the window of `p` exceeds its archimedean-plus-pole prediction by at most a constant, `P(p)≤A(p)+K`; equivalently `c_B(log p)≥−K` (one side of Hasse–Weil for the smoothed Frobenius graph of degree `p`); equivalently Weil's form is bounded below on the single two-bump test `B+τ_{log p}B`; equivalently the effective class `Γ_1+Γ_p` carries a count with Tate limit `2c_B(0)+2c_B(log p)` [L]. U-Σ reads it as the sign of one test per prime, U-Π as a crude prime count at the prime degrees, U-Γ as the count half of a Born rule on one ray per prime. The window form (`1∈ℋ(c)`, `a*(ζ)=⊤`), the band `|𝒞_m(f)|≤W(f)`, `Q≥0` on integer probes and `Q` as a Tate limit of a count are the same object read on all windows at once.

Transversal to the three, RH splits into **ZAL** (finitely many zeros beyond each depth) and **AAL** (zero transport in height), with a strict **linear dial** between them: `Pure ⊊ AAL ⊊ LinAt C₁ ⊊ LinAt C₂ ⊊ (ZAL⇒RH) ⊊ B13`. On the prime side the dial has a producer form: a one-sided crude bound on a **sampling set** of primes gives AAL, and the full set of primes gives RH, because power-saving gaps supply the attainment that ZAL supplies otherwise [L]. Below the three lie four structural gaps that every family meets: the **dark range**, primes past the Kronecker scale where conditioning on the head needs a Dirichlet polynomial longer than the height and where transcendence bounds the depth but not the breadth of returns; the **missing diagonal**, a counterterm-free positive presentation of the diagonal of Weil's form, which atoms cannot supply (their locked diagonal is the discriminant) and smoothing must renormalize; the **two-scale Euler-product-and-FE input**, a Dirichlet-series statement that couples low and high zeros and turns the FE (which reflects a height to itself) into vertical transport; and the **exactness gap of the archimedean Frobenius**, which makes integrality act only on the torsion of the prime torus and caps every phase-freezing argument at the returns by the trivial bound.

**Why there are three cores [D].** No test is compact on both sides of the explicit formula. A compact prime side (U-Σ) leaves infinitely many zero modes and only an exact sign decides; a localized zero side (U-Π) lets a crude bound decide (one Gaussian prime ceiling per rational height ⇔ RH; one side of a crude bound at the prime degrees ⇔ RH; ZAL plus a square-root prime deviation on a thick set of scales ⇔ RH [L]) but leaves the prime side at square-root precision; U-Γ is the involution `ρ↦1−ρ̄`, the selection of ζ and the transport of its zeros. The curve proof uses two freebies that ζ lacks: finite rank, which makes elimination algebraic and ZAL in tower form automatic, and zeros periodic in height, which make AAL automatic [L]. At finite rank Euler product + FE force purity by local squares; at infinite rank FE + Euler product with integrable defect force the rational primes [L]; over ℤ the elimination step exists at infinite rank on thick sets and at the prime degrees by Landau's theorem, and the crude step is open.

Corpus checkpoint: commit `ad80866fec` (2026-11-09). Evidence: `[L]` Lean source; `[K]` with transitive axiom audit; `[S]` unfinished or unintegrated; `[D]` deduction; `[N]` numerical; `[C]` classical. Locators: [frontier map](../rh-current-frontier-map.md), [scoped obstructions](../rh-killed-routes.md), [walls](walls-ledger.md), [routes](route-obstacles.md), [summary](obstacles-summary.md).

**Equivalence through RH transfers truth, not mechanism.** Only an explicit source identity or a proved transport moves an estimate between routes. Section 3 separates the two.

## 0. Unifying statements

- **One inequality per prime [L].** RH ⇔ `c_B(log p)≥−K` at every prime ⇔ `c_B(log p)≤K` at every prime ⇔ `P(p)≤A(p)+K` ⇔ `Re W(B±τ_{log p}B)` bounded below at every prime; width `≤a` ⇔ the same with `Kp^a`; unconditionally `P−A=o(√p)`. The gap method iterates; Landau replaces Pringsheim; the absence of real zeros of ζ removes the Stepanov side's only blind spot; at the `p^k` the zero-free strip improves itself.
- **One tensor-power trick [L].** RH ⇔ the even tensor powers of the virtual motive of the zeros have a common abscissa ⇔ prime moments of `(2Re S(log p))^{2k}` grow like `N^{1+A}` uniformly in `k`; the Rankin square has abscissa `2maxRe ρ`. Positivity is free; uniformity is RH.
- **One sampling law [L].** A one-sided crude bound on a sampling set of primes (a residue class, the primes off a relative-density-zero set, the degrees `p^aq^b`) leaves no deepest off-line zero: AAL; with ZAL, RH. Finitely generated monoids of primes need an attained top; the primes and two-prime difference lags do not. One Frobenius aliases.
- **One split [L].** For every zero configuration, purity ⇔ ZAL ∧ AAL. For ζ: RH ⇔ ZAL ∧ AAL ⇔ ZAL ∧ `LinAt C` (any real `C`) ⇔ ZAL ∧ zero-disc weak recurrence ⇔ ZAL ∧ subexponential polar ground energy ⇔ ZAL ∧ thick `O(√X)` prime deviation ⇔ ZAL ∧ a positive count of one Weil tower. ZAL ⇒ qRH. `qRH ∨ AAL` [D].
- **One dial [L].** `LinAt C ⇔` eventual-to-global at slope `C`; `∃C` collapses to `ZAL⇒RH`; `AAL ⇔ ∀C>1`; the levels are strictly separated by explicit configurations (harmonic-depth configurations sit between `ZAL⇒RH` and B13). For ζ at `C≥1`: `LinAt C ⇔` finite-rank Chebyshev self-improvement ⇔ all-scale lag `O(e^{C(Θ∞−½)L})` ⇔ thick tower lag ⇔ thick prime deviation `O(X^{½+C(Θ∞−½)+ε})`.
- **One exponent [L].** `Θ∞` is the infimum exponent of `ψ(x)−x` modulo finite exponential sums. The finite stratum is `ψ(x)−x` = a finite exponential sum + `O(x^{½+ε})`.
- **One transport [L].** AAL ⇔ every right zero has zeros with real part `>Re ρ−ε` at arbitrarily large height ⇔ every right zero transports to arbitrarily high points where every Euler tail vanishes with full amplitude. Approximate tail cancellation (`η>0`) is abundant at every strip point; exact cancellation (`η=0`) near right zeros is the content of AAL. The FE reflects every height to itself (`N_tζ(s+it)≈conj ζ(1−s̄+it)`); under ¬AAL the raw prime current passes to `−ζ′/ζ` on a high strip; neither moves a zero.
- **One two-scale law [L].** No property of the zeros above a height and no property of the zeros below a fixed height decides the finite stratum, any linear law or AAL.
- **One family law [L].** A finite-stratum law valid on every heat deformation `H_t` (`t>0`) is RH; linear AAL along the heat flow is RH; among the heat deformations only `τ=0` has an absolutely convergent Dirichlet series.
- **One analytic freedom [L].** FE, order one and reality admit every finite top layer, also over a remainder at positive asymptotic abscissa. On tower level sums the FE acts only as `S(−ν)=conj S(ν)`.
- **One firewall [L].** Continuous Beurling systems, prime-square-corrected discrete and integer-norm Euler products with linear counting continued across `Re s=½`, rational-prime one-offs and one reflection pair each carry a finite top layer; positive two-prime and Hecke polynomials annihilate every finite zero set, at exponential mass cost in the multiplicity, and their inverses oscillate. Only the FE excludes the layer.
- **One calibration where Euler + FE succeed [L].** A finite Euler product with an FE of conductor `ΠP` has `a_p²=p` and every zero on `Re s=½`; a countable Beurling system whose theta function satisfies Riemann's FE up to an `L¹` or `L²` defect is the rational primes, with zero defect; a positive measure with gap `(−1,1)∖{0}` is tent-self-dual iff a Dirac comb.
- **One free class [L].** Recurrent configurations, exponential polynomials, curves, vertically periodic configurations, strip almost periodic functions and uniformly approximable Dirichlet series obey AAL.
- **One rigid alternative [L].** ¬AAL ⇔ an isolated top over an infinite remainder ⇔ finite top and bottom layers at the same heights ⇔ `ψ(x)−x` a finite oscillation at leading order ⇔ two-prime dilation annihilation ⇔ syndetic lag excursions at every base.
- **One elimination [L].** The exceptional rank decides Turán windows; no thick set carries a bound below an isolated top; density `1−1/k` sets do not self-improve; well-founded towers bounded on a thick set have only the critical layer visible; Wolff towers show well-foundedness is needed; continuous levels see every zero (a crude bound on all `L` is a zero-free region).
- **One finite stratum [L/K].** Finite negative index of `K_ζ` ⇔ finite index on one two-prime lattice ⇔ finitely many off-line zeros ⇔ bounded heat count ⇔ RH above some height ⇔ eventual slice positivity; in the stratum Lindelöf holds and RH ⇔ one non-blind prime tower PD ⇔ one Weil tower Toeplitz positive ⇔ one tower bounded on a thick set.
- **One scalar [L].** Every window route measures `a*(ζ)`. Contact is `Ψ=½log H₁` blowing up; RH ⇔ `Ψ` locally bounded.
- **The critical curve is the window plus one inequality [L].** `R_c=R_polar=R_halfline≤R_prim=R_high=W`; the charged compactness passage is closed; the gap is polar payment at every `R<W`; under ¬RH a unit half-line ground state lives at finite `W` and is polar-orthogonal if `R_polar=W`.
- **One exchange [L].** Below the onset, aperture `a` buys a depth-`¼` zero-free region to height `e^{a/K}`, which buys a sharp pole and `R_c≥c₁e^{c₂a}`; no step raises `a*(ζ)`.
- **One splitting order [L].** Conductor first, position second.
- **One sign plane [L/D].** Size reaches all heights to `a≈log log X`; typical heights to `a=δlog T/(64M²)`.
- **One frequency diagonal [L].** Weil's form is the average of its frequency packets.
- **One scale [L/D].** A near-unit mollifier needs length `exp(c log²T)`; an Euler mollifier reaching it uses every prime up to `≍log²T`; absolute non-alignment begins at length `≈L²`; conditional tail laws hold only below the Kronecker scale; past the height long mean values are collision counts of order `X²` whose constant is binary.
- **One tail [L].** Zeros of ζ are zeros of the Euler tail at every cut; returns at right zeros are tail-bad; every certificate past `Re s=1` is a tail-good condition.
- **One first return [L].** `R(y,η)` bracketed at every precision; weak return = extreme value of `ζ(1+it)`; proportional saving = no early heavy return; transcendence bounds the depth of a return (`t≥poly(1/δ)` for two primes) and bounded-height forms cannot bound its breadth past the Kronecker scale; by reciprocity a heavy return at height `t` is a configuration of zeros near `t` imitating the pole; return bounds are shared by `ζ(s−h)`, so a route from returns to ZAL must use the FE [S].
- **One Frobenius substitute, capped [L].** Returns freeze smooth Dirichlet polynomials; `J` moment conditions force approximate vanishing at every return; a Rouché copy needs `J≤e²r log N+log(1/δ)`. The exact Frobenius of integer auxiliaries is the Adams operation, Galois on the torsion of the prime torus and dilation on the orbit; integrality creates zeros only on the torsion; exact order costs the degree; the minimal auxiliary at the fixed points of all `Γ_n`, `n≤N`, has log length `ψ(N)`. Over ℤ the exact Stepanov count is Chebyshev's.
- **One collision arithmetic [L].** Smooth × prime mean squares are diagonal plus collision counts fixed by gcd classes.
- **One width axis [L/D].** Floor rate, damping rate, abscissa, gauge exponent, stability line, long-moment slope, Möbius zero abscissa, integrality exponent, stencil rate, PTR `h`, TH `a`, Hecke level, ringdown gap, horocycle, Farey, Narain, seed and cavity-energy exponents, spline-orbit growth rate, growth exponent of either side of Hasse–Weil at the primes or at any power-saving gap set: interior values are zero-free strips; all unconditional savings sit at VK.
- **One Mertens level [L].** Stencil rate = Mertens level; Farey discrepancy, the nerve and core Euler characteristics, the Farey count at order `C`, `1−Σ_p` prime-vertex indices, the integer gluing charge and the centred count of the orientation cover over ℤ are `M(N)`.
- **One topology [L].** The prime-product complex is a sphere bouquet with classified persistence, independent of `s`; prime-vertex self-maps homotopic to the identity fix exactly the primes, exits are bouquets, local indices are relative singular Euler characteristics summing to `1−M(N)` and unbounded below. The orientation cover over ℤ exists (fibres `1+μ(n)`); its middle cohomology never vanishes, has weight `≥½`, and weight `½` is RH.
- **One cancellation geometry over `𝔽_q` [L].** Möbius over `𝔽_q[T]` is the point defect of an orientation cover of exact size `qⁿ` (`n≥2`); elliptic and hyperelliptic orientation counts over `𝔽_q` have square-root discrepancy from the curve root bound; Möbius over `ℤ[ω]` is a cubic Gauss coefficient. Over ℤ the cover exists; its cancellation is RH.
- **One horizon [L].** Pulse ringdown, horocycle mean, Farey count, Lax–Phillips mode, Narain remainder, seed response and cavity energy read the poles `ρ/2`; gain `δ` past the trivial rate ⇔ strip `2δ`; RH ⇔ `y^{¾}` ⇔ `e^{−t/4}`. One cuspidal cavity function of Hecke eigenforms sees every resonance and is a sharp receiver; the dual side has no sign; the reflection Krein form of the cavity is PSD ⇔ RH; the horizon's own Krein form is blind.
- **One Born rule [L].** A count law = nondegenerate Born rule (the FE) + positivity (universal damping). The partner involution has a positive state iff damped; internal modular conjugation collapses to the Hilbert adjoint; vacuum-fixing partners and half-sided Borchers inclusions cannot carry `Q`; RH ⇔ an internal standard form realizes `Q`.
- **One count [L].** Tate principle both ways; curves: the integral defect is a point count; fakes: count, not quadratic; ℤ: quadratic, count missing, `Q` not integer-valued and no integral kernel reproduces it; one effective ray `Γ_1+Γ_p` per prime needs one count.
- **One surface [L].** Off the diagonal Weil's kernel is the pole minus the Green functions of all places at the critical parameter: `2πG_{1/2}` on the degree geodesic of `ℍ³` (cusp `k=0`, jets `k≥1`) and `log p((p−1)/√p)G^{T_p}_{1/2}` on the apartments of the Bruhat–Tits trees (the Ramanujan point); the archimedean compensation is spherical and changes sign at the plastic ratio; no hyperbolic quotient carries the primes; atomic graphs have genus `≍N log N`, their locked diagonal is the discriminant and never PSD; smoothed pairs pass one side of Hasse–Weil at the primes ⇔ RH; the sign sits in the diagonal.
- **One critical weight [L].** Damping is lossless; renormalization carries no sign; the smooth archimedean self-energy is logarithmic and needs one universal counterterm `‖f‖²log(1/(1−r²))`.
- **One crude regime absent in size, present at the primes [L/D].** In the size coordinate constant-factor bounds are false and `x^{½+ε}` is RH; crude regimes live in the exceptional coordinate, on thick sets of scales and at the prime degrees of the Frobenius graphs, where the self-improvement is free.
- **One blindness [L].** Floor identities annihilate every zero mode; exact ledgers are holomorphic off `s=1`.
- **One kernel [L].** Zeros are the power-law kernel vectors of the cut system; finite-energy kernel mass annihilation ⇒ RH.
- **One parity [L].** The exact identity `Σ_{k≤x}F(⌊x/k⌋)=⌊√x⌋` pins `λ`; a power-saving Liouville bound is a zero-free strip.
- **One edge [L/D].** Pronic domination, flux, Hermite–Biehler at `σ=1`, Euler coordinates, the Poisson measure of the Hecke algebra, primon thermal averages, the Hecke state on `Aff(ℚ)`: every positivity with a proved mechanism stops at `Re s=1` or at `Re s=½` as a threshold, not as a selector.
- **One inner factor [L].** On `Re s>½`, `E` has inner factor the Blaschke product of right zeros; RH ⇔ `I(w)=0` at one point.
- **One log-mean [L].** Eight forms of `T⁻¹∫log|ζ|→0`, depth density `o(T)`; an asymptotic property.
- **One certificate [L].** Causal: outer predictor, Schur band, sum of squares with margins as weights.
- **One column law [L].** On independent reflectors infima add; only amplitudes oscillating with the height cross columns.
- **One theta head [L].** The adaptive head is `|ζ(½+ib)|²` plus `O(|ζ(½+ib)||b|^{−½}+|b|^{−1})` and terms whose sign is decided near the critical zeros.
- **One Eisenstein carrier [L].** TH spectrum, PM carrier, BHR packets, horocycle means, Farey counts and the Narain scalar projection use `E*(z,½+ib)`; Hecke at `p` is time translation by `log p`.
- **One isolation [L].** ζ is a singleton in FE defect (any `L¹` or `L²` defect), in count distance `o(log n)` and under the exact parity identity.
- **One finite-rung rule [L].** Each fixed window, rank, degree, row, ratio and entry follows from verified zeros; no finite verification decides B13, any linear law or AAL.
- **One budget [L].** A floor `−C_σe^{2σr}∫F²` for every `σ>0` implies RH.

## 1. Faces of the one object

| Reading | Statement | Anchor |
|---|---|---|
| Index | `κ` counts distinct right zeros; RH ⇔ `κ=0` | HKT, AKLT, CWS [L] |
| Finite stratum | `κ<∞` ⇔ lattice index finite ⇔ finite off-line set ⇔ bounded heat count ⇔ eventual RH ⇔ eventual slice positivity | HKT, AKLT, FFP, ZCG [L/K] |
| Winding | predictor polynomial zero-free in the disc on every lattice | AIF [L/D] |
| Onset aperture | nonnegative half-widths `[0,a*]` | WVL, AHD [L] |
| Local onset | `Ω_ψ(a,X)≥0` everywhere | AIF [L] |
| Hardy interval | `⋂ℋ(c)={1}` ⇔ RH | FADF [L] |
| Cone and margin | `λ*(c)→0` ⇔ RH | CHT [L] |
| Datum region | `(1,0)` lies in it ⇔ RH | CHT [L] |
| Two sites | two-site PD | GWZ, SRT [L] |
| Spline orbit | Hasse–Weil along the cubic-spline orbit; orbit growth subexponential | AOG [L] |
| Frobenius graphs | one side of Hasse–Weil at the integer, square, `k`-th power, prime or prime-power degrees; either side; any power-saving gap set | SOSZ [L] |
| Prime two-bumps | `Re W(B±τ_{log p}B)≥0` (or bounded below) at every prime: one Weil test per prime | SOSZ [L] |
| Stepanov prime count | `P(p)≤A(p)+K` at every prime | SOSZ [L] |
| Tensor powers | prime moments of `(2Re S(log p))^{2k}` uniform in `k`; common abscissa of `M^{⊗2k}` | SOSZ [L] |
| Two Frobenii | one-sided bounds on the dense lags `log m−log n`, `m,n∈⟨p,q⟩`; binary counts on those planes | SOSZ [L] |
| Plane counts | a binary `ℕ`-count with Tate limit `δ_n` on every integer plane; one count per effective prime ray `Γ_1+Γ_p`; copositive prime planes | SOSZ [L] |
| Hamiltonian | `Ψ` locally bounded | CSTW, AIF [L] |
| Lattice | Schur parameters in `(−1,1)` | GWZ [L] |
| Causal | outer predictor at every window | AIF [L] |
| Bohr | orbit correlations relatively compact | AIF [L] |
| Critical thresholds | `R_c=R_polar=R_halfline`, `R_prim=R_high=W`, all `=⊤`; no finite critical half-line ground state | AHD [L] |
| Low packet | polar payment at every ratio | CACT [L] |
| Moments | Hamburger, shifted Hamburger, Stieltjes | SWC [L] |
| Li / Cayley | ladder NSD on primitives | ALG [L] |
| Suzuki | first variation = Weil energy | RHTower [L] |
| Single prime | one Euler factor; transport ⇔ RH | RHTower, AHD [L] |
| Heads | `windowThreshold(log d)` ∀d | AHD [L] |
| Heat | no positive-time collisions | RHTower, ZCG [L] |
| Heat linear law | linear AAL along `t→0⁺` | ZCG [L] |
| Gaussian ceiling | `P(ε,r)` bounded above for every rational `r≥½` | RHTower [L] |
| Cosine | strict Laguerre on the open strip | PTR [L] |
| Jensen | infinitely many degrees real | FFP [L] |
| Hausdorff | rows below the explicit shift | S [L] |
| Heat grids | every degree on two grids | RHTower [L] |
| Theta ranks | signed Hankel at every rank | RHTower, TCS [L] |
| Krein | `D_s≥0` | RIT [L] |
| Hecke dispersion | `V_p≤2(1−p^{−½})` at every zero | ACP [L] |
| Ringdown / Lax–Phillips | every mode at `e^{−t/4}` | BHR [L] |
| Horocycle / Farey count / cavity energy | rate `y^{¾−ε}` of the horocycle mean, the Farey count, one cuspidal cavity energy, every two-mode energy | BHR, CTH, AHMH [L] |
| Reflection Krein form | every reflection Krein form of the cavity PSD | AHMH [L] |
| Narain | remainder `O(y^{¾−ε})` (sufficient) | ASH [L] |
| Farey discrepancy | `L²≤n^{−1+δ}` | RHTower [L] |
| Long moments | cofinal `θ`; one window | CDG, MZF [L] |
| Positive proportion | every length-2 window | MZF [L] |
| BSY | `I≤0` | RHTower [L] |
| Budgets | `inf_Q budget=1` | AIF [L] |
| Dilation | one fixed-`δ` equality | AIF [L] |
| Count | `ψ(x)−x≪√x log²x`; integer lag | RHTower [L] |
| Tower count | ZAL ∧ thick `O(√X)` prime deviation; ZAL ∧ positive count of one tower | IWT [L] |
| Linear law | ZAL ∧ `LinAt C` | ZCG, IWT [L] |
| Integrality | Siegel or Liouville half at `√` scale | ASRP [L] |
| Stencil rate | rates `K^{−a}` ∀`a<½` | AAD [L] |
| Cut kernel | finite-energy kernel mass zero | RAC [L] |
| Möbius | subpower Hilbert form; one point; zero-free `M_X` | RHTower, MZF [L] |
| Redheffer / nerve / core / vertices / orientation cover | `det=M(N)=−χ̃`; `1−Σ index=M(N)`; centred cover count `M(N)`; `O(N^{½+δ})` (cover weight `½`) | HWV, ADT, HHAC, RIAC, HAT [L] |
| Recurrence | strong self-return; uniform target mass | RHTower [L] |
| Split | ZAL ∧ AAL | RHTower, ZCG, IWT [L] |
| Polar ground energy | ZAL ∧ subexponential `μ₀` | RHTower [L] |
| Source criteria | Fock bound, repair equality, co-shift class | RHTower [L] |
| Bézout | source-energy sign | ACS [L] |
| Characters | central class functions with Gram positivity | Representation [L] |
| Integer probes | `Q(a)≥0` on `ℤ^N`; naive heights | ASH, AE, CWS [L] |
| Tate limit | `Q` is the Tate limit of an `ℕ`-count | CTH [L] |
| Standard form | internal modular conjugation realizing `Q` | CTH [L] |
| Hull | Liouville fibre extends | PTT [L] |
| Parity | `L(x)≪x^{½+ε}` | RAC [L] |
| Log-torsion | `ψ(N)=N+O(√N log²N)` | AE [L] |
| Fixed-point auxiliary | `log N(A_N)=ψ(N)≤N+C√N log²N` | ALST [L] |
| Modulus balance | `\|Q(tw)\|=\|Q(t̄w)\|` at zeros | RAC [L] |
| Sampling-set bound + ZAL | one-sided crude bound at the primes `≡a (mod q)`, or off a relative-density-zero set, or at `p^aq^b`, together with ZAL | SOSZ [L] |
| Metric recurrence + ZAL | positive measure or dimension of recurrent lag bases at every rate, together with ZAL | IWT [L] |

## 2. Axes

### 2.1 Window axis
| Coordinate | Half-width `c` | Anchor |
|---|---|---|
| Markov death | `e^{−3/4}` | SWC [L] |
| Perron threshold; sign change of `C_∞` | `log ρ≈0.2812` (plastic) | SWC, FADF [L]; SOSZ [S] |
| Odd prime entry | `½log 2` | FADF [L] |
| Known sign, Lean | `<0.3621`; base `a₀>181/500` | AIP, LST, AIF [L] |
| Known sign, external numerics | `≈1.9` via `T₀=3·10¹²` | [D] |
| Odd unit window | `½`, margin `≈2·10⁻⁴` | SWC [L/N] |
| First prime stage | `2c=21/20` | WTZ, GWZ [L] |
| Prime-three entry | `2c=log 3` | SWC, AHD [L] |
| Variance-free certificates | fail for `c>273/400` | SWC [K] |
| `{2,3,4}` frontier | `2c<log 5` | SWC [L] |
| Tate dimension one | positive exactly for length `≤log 5` | WTZ [L] |
| Edge-law crossing | `c*∈(½log5,½log6]` | FADF [L] |
| End of finite templates | spread `27/5` | WTZ [L] |
| Zero information | from `c≥4`; `≈20` with present constants | WVL [L]; [D] |

### 2.2 Sign plane
| Curve in `(a,log X)` | Statement | Anchor |
|---|---|---|
| Height non-locality | low zeros do not decide | WVL [L] |
| All heights, size | `a≈log log X−log 4` | [L]/[D] |
| Typical heights | `a=δlog T/(64M²)`; bad set Gaussian-tailed | ACS [L] |
| Cut crystal | fixed depth hidden to `(log T)/36` | WVL [L] |
| Camera | isolated `λ>½`; configurations `λ>1` | ZCG [L] |
| Aperture exchange | depth-`¼` exclusion to height `e^{a/K}` | AHD [L] |

### 2.3 Width axis
| Route | Parameter | Interior value means | Known | Anchor |
|---|---|---|---|---|
| RW, AIP, OWU | floor rate `2σ` | width `≤σ` | VK | S, I [L] |
| SC | Gaussian coupling rate | width `≤σ` | bounded ⇔ RH | ACPL [L] |
| WL, MC | abscissa `2Θ`, gauge exponent | `Θ` | VK | CAF, AGT [L] |
| WL, IWT | continuous-level lag exponent `a` | zero-free `Re>½+a` | VK | IWT [L] |
| WD | long-moment slope | `w` | exact | CDG [L] |
| MC | zero abscissa of `M_X` | `Θ` | exact | MZF [L] |
| MC | twin Möbius exponent | `Θ≤2max` | floor `¼` | AGT [L] |
| LA | stability line | zero-free `Re s>σ` | `σ≥1` | FFP [L] |
| PTR | depth `h` | width `≤h` | `h>½−vkWidth` | PTR, ZCG [L] |
| TH | aperture `a` | width `≤a` | VK collar per rank | TCS [L] |
| ZCG | `Λ_Xlog X` | strip | `≤6600/9991+ε` | ZCG [L] |
| PM | Hecke level | half-plane | edge only | ACP [L] |
| PM | horocycle / Farey / pulse exponent `½+δ` | `Re ρ≤1−2δ` | `δ=0` with saving `exp(−√(−log y))` | BHR, CTH [L] |
| PM | sharp-shell exponent | `Re ρ≤2−2α` | `y^{½}` log-free | CTH [L] |
| PM | Narain remainder exponent | strip | VK saving at `½` | ASH [L] |
| PM | cusp- and cavity-energy exponent `α` | `Λ_g(ρ/2)=0` for `Re ρ>2−2α`; for one cavity function of Hecke eigenforms, zero-free `Re ρ≤2−2α` | `½` | BHR, AHMH [L] |
| AOG | spline-orbit growth `σ` | width `≤σ` | VK | AOG [L] |
| ACS, SOSZ | integer-degree crude Hasse–Weil exponent `σ` | width `≤σ` | VK | SOSZ [L] |
| ACS, SOSZ | growth exponent `a` of either one-sided bound at the primes (or any power-saving gap set) | width `≤a` | `a=½` with `o(1)` (PNT in every window) | SOSZ [L] |
| AAD | stencil rate | `Re ρ≤1−a` | VK; RH gives `[¼,½]` | AAD [L] |
| RAC | Liouville exponent | zero-free `Re s>Θ` | VK | RAC [L] |
| AE | integrality exponent | `Θ` | exact | ASRP [L] |
| IWT | thick prime-deviation exponent `½+a` | no isolated top above `½+a` | none | IWT [L] |
| TAPO | first-return exponent at constant precision | dark-range saving | `(log y)^{3/2−o(1)}` | TAPO [L] |
| HHAC | core Euler characteristic exponent | strip | `θ=1` up to VK | HHAC [L]; [D] |
| RIAC, HAT | weight of the orientation cover over ℤ | strip | `≥½` always; `½` ⇔ RH | HAT [L] |
| SOSZ | uniform tensor-moment exponent `A` | width `≤(1+A)/(2k)` for each `k` | none uniform | SOSZ [L] |

### 2.4 Finite rungs
| Ladder | Rung | Verified height | Anchor |
|---|---|---|---|
| RW, OWU, EWU, ACT | window `a` | `windowHeight a` | VHR [L] |
| HF, SRT | ratio `R` | window threshold `≥R` | AHD, CACT [L] |
| TH | rank `N` | `41+6(N+2)log(N+2)` | TCS [L] |
| LA | degree `d` | `2·10⁷d⁴≤T log T` | VHR [L] |
| LI | entry `n` | `n≤4.7T` | VHR [L] |
| PA | row `k`, `r` | `k+1≤1.5(T−1)`, `r≤RT³` | VHR, S [L] |
| HCF | degree | `deg+1≤T/4800` | VHR [L] |
| Centre PF | order `k` | `k+1≤3T` | VHR [L] |
| Cone | window `c` | PNT `5/6` on `X≤e^{2c−3}` | CHT [L] |
| SOSZ | degree `n` | smoothed pair at `log n` from window rungs | SOSZ, VHR [D] |
| B13, linear laws, AAL | none | no finite verification decides | ZCG [L] |

### 2.5 Exceptional coordinate
| Level | Statement | Receivers / producers | Strength |
|---|---|---|---|
| Finite stratum (B13) | finitely many off-line zeros ⇒ none | finite index, lattice index, heat count, `N_d`, eventual RH, eventual slice positivity, one non-blind tower, one Toeplitz-positive Weil tower in the stratum [L/K]; no family-uniform input (heat) | sub |
| `ZAL⇒RH` (B111) | `Θ∞=½ ⇒ Θ=½`; existential linear AAL | every ZAL receiver becomes an RH receiver [L] | sub |
| Fixed slope (B116) | `Θ−½≤C(Θ∞−½)` | finite-rank Chebyshev self-improvement at factor `C`; thick relative crude count [L] | sub |
| AAL (B83) | `Θ=Θ∞`; zero transport; tail transport | not-attained top, progressions, Abel-density-zero excursions, polar ground energy, prime-window grid, integer lag, plateaux, JAS, towers, cone, weak recurrence, slow returns on right discs, thick lag, thick prime deviation, positive count of one tower, a one-sided crude bound at a sampling set of primes, positive-measure lag recurrence, uniform tensor moments at a residue class [L] | sub |
| ZAL | well-foundedness of every tower | inner-field decay, subtracted lag, `Λ_Xlog X→0`, eventual Hadamard, LH with every cosine-shift level eventually real, high-collision counts [L] | ≥qRH |
| Thick crude count (B110) | `primeDeviation=O(X^{½+a})` on thick scales ∀`a>0` | ⇒ AAL; with ZAL at `a=0` ⇔ RH [L] | AAL |
| Sampling-set bound (B126) | one-sided crude bound of the spline traces at the primes `≡a (mod q)`, or off a relative-density-zero set, or at `p^aq^b` | ⇒ AAL; with ZAL ⇔ RH; at all primes ⇔ RH without ZAL [L] | AAL |

### 2.6 Scale axis of the prime orbit
| Range of primes at height `t` | What holds | Anchor |
|---|---|---|
| `p≲c log t` | prescribable: every box entered; no cancellation at some height | PTT, RAC [L] |
| Kronecker scale `≈log t` | conditional tail laws stop; first return of the head ≍ height | TAPO [L]; [D] |
| `≈(log t)²` | absolute non-alignment begins; Euler mollifier length for near-unit moments | PTT, APR [L] |
| `(log t)^A` | saving `t^{−δ}`; RH bracket at polynomial precision | PTT, TAPO [L] |
| `exp((log t)^{2/3})` | VK saving | TAPO [L] |
| between | absolute savings only; collision arithmetic gives upper bounds and the order `X²`; returns freeze smooth polynomials with precision-capped Rouché copies | PTT, TAPO, SPAL, IWT [L] |

### 2.7 The curve proof and its ℤ-counterparts
| Ingredient on a curve over `𝔽_q` | Lean anchor | ℤ-counterpart | Status over ℤ |
|---|---|---|---|
| Finite rank: elimination is algebra, outer part well-founded | CTH, IWT [L] | ZAL = well-foundedness of the towers of ζ | ≥qRH, open |
| Periodicity of the zeros in height ⇒ AAL | ZCG [L] | AAL = zero transport; produced by one-sided bounds at sampling sets of primes | open (B83, B126) |
| Euler product + FE at finite rank ⇒ local squares | RHTower [L] | Euler product + FE with integrable defect ⇒ rational primes | available as classification; transport (B112) open |
| Stepanov's bound `N_n≤qⁿ+1+Cq^{n/2}` | RHTower, CTH, IWT [L] | `P(p)≤A(p)+K` at the prime degrees (Σ138, Π123) | open (B130); RH |
| Stepanov's auxiliary vanishing at the rational points | AKLT [L] | the fixed-point auxiliary `A_N`, of log length `ψ(N)`; exactness only on the torsion | the exact count is Chebyshev's (Π125, Π126) |
| Bombieri's second count (twist) excludes real eigenvalues | SOSZ [L] | ζ has no real zero in the strip: the Stepanov side alone decides | available |
| Base change: counts over `𝔽_{q^{kn}}` | SOSZ [L] | traces at the degrees `n^k`, `p^k`; trace zeta `Σ_ze_zζ(s−kz)` | available as receiver |
| Self-improvement by power sums | IWT, SOSZ [L] | gap iteration and Landau at the prime degrees; window theorem at infinite rank on thick sets | available |
| Deligne's tensor-power trick | SOSZ [L] | moments of `(2Re S(log p))^{2k}` uniform in `k` | uniformity is RH |
| FE pins modes to the circle | CTH, ASH [L] | FE of ξ = Born rule; Hecke isometry of `Q` | quadratic half holds |
| Count half: the integral defect is a point count | CTH [L] | `Q` as Tate limit of a count on one ray per prime (B87); damping of the diagonal (B88) | open; `Q` not integer-valued, no integral kernel |
| Archimedean fibre | — | `ℍ³` Green function at `s=½` (cusp + jets) on one geodesic | available off the diagonal |
| Finite fibres | — | Bruhat–Tits trees, Green function at the Ramanujan point on the `p`-ladders | available off the diagonal |
| Middle cohomology of the orientation cover vanishes (`qⁿ` points) | RIAC [L] | cover over ℤ with centred count `M(N)`, weight `≥½` | weight `½` is RH |

## 3. Which routes are the same problem

### 3.1 Same problem by source identity or proved transport
| Family | Routes | Identity | Anchor |
|---|---|---|---|
| **Prime-degree inequality** | ACS (Frobenius graphs), SRT (prime two-bumps), WL (prime-window count), HF and RW through Σ141, ALST (Stepanov), SOSZ count door | `c_B(log p)=A(p)−P(p)` and `Re W(B+τ_{log p}B)=2c_B(0)+2c_B(log p)`: one quantity per prime is the Weil test, the Hasse–Weil defect, the prime-window error and the Tate limit on the effective ray | SOSZ [L] |
| Window scalar | RW, EWU, OWU, ACT, CHMD (odd), TT (odd), SZ, RN energy, ACS atomic, LI on primitives, HF, SRT, AIP critical branches | one form on one window; sectors exact; first variation = Weil energy; critical thresholds are the window threshold plus polar payment plus ground-state orthogonality | SWC, SZ, ALG, ACS, CACT, AHD [L] |
| Two-site / Frobenius graphs | GWZ two-site, AOG spline orbit, SOSZ Frobenius pairs and prime degrees, SRT two-bump | one rank-two test per scale; the prime degrees suffice from one side | GWZ, AOG, SOSZ [L] |
| Log-mean | WD near-line, CTF budgets, ZCG depth law, RW onset, AIF `I` at infinity, BHR bulk log-mean | eight-way equivalence; depth density | CDG, AIF, ASH [L] |
| Mertens level | MC, WL, AAD, AE, CTF defect, PBM, RB, Redheffer, RAC parity, Farey, nerve, core, prime-vertex indices, gluing charge, orientation cover | rate ⇔ level; `det=M(N)=−χ̃=1−Σ index`=centred cover count; Farey law ⇔ RH | AAD, RAC, RHTower, ADT, HWV, HHAC, CTH, RIAC, HAT [L] |
| Inner mass | CTF BSY, AIF budgets and dilation, MZF `N(ρ)`, KL index | one Blaschke product | AIF [L] |
| Horizon | PM, BHR, ASH, RIT, CTH horocycle, Narain, AHMH seeds and cavity | one scattering matrix; every observable reads `ρ/2`; one cavity function sees all of them | RIT, BHR, ASH, CTH, AHMH [L] |
| Abscissa / transport / dial | BAG, WL thick runs, JAS shell, SC undamped, ACS sampling branch, ZCG one-off, linear and tower layers, AKLT towers, AAD transport, TAPO, RW polar ground energy, IWT metric recurrence, EFT finite-layer world | ¬AAL as one rigid object; AAL = zero transport = tail transport; linear dial with prime-side TFAEs; sampling-set and metric producers; countermodels classified | ZCG, AKLT, AAD, TAPO, APD, IWT, SOSZ, EFT [L] |
| Count | ACS, HF, PM probes, CWS heights, LST Künneth, CTH Tate limit, SOSZ half-products and ray counts, RIAC arithmetic counts, standard forms | one quadratic form on integer probes; count law = Born rule + positivity; off-diagonal = adelic Green pairing; one ray per prime | AE, ASH, CWS, ACS, CTH, SOSZ, HAT [L] |
| Tail | BAG returns, TH certificates, PTT Ξ-current, AIF dilation | zeros of ζ = zeros of the Euler tail | TAPO, PTT, AIF [L] |
| Aliases | HJ→PA; BSH→CDC; FEL BSY→CTF | definitions | frontier |

### 3.2 Same endpoint, distinct mechanism
| Group | Routes | Common form only |
|---|---|---|
| Laguerre | TH, PTR, ZCG, LA, GTA, XN, HCF, PA | horizontal-line Laguerre form in a limit |
| Base against columns | TH, ZCG carriers, FFP | `½log(b/2π)` against Euler speed |
| Scheduled sums | FU, CFC, RP, LI | one-sided history floors |
| Source completions | SEC, CDC, PCS; APF, EWJ, RFHM, WBF | a source plus one vanishing at zero parameters |
| Integer gates | TG, WD charge, SC index | an integer that small norm kills |
| Dark-range inputs | B46, B57, B89, B96, B97, B121 | Dirichlet polynomials longer than the height; breadth of returns |
| Two-scale transport inputs | B13, B83, B110, B111, B112, B116, B126, B127, B128 | a Dirichlet-series statement with Euler product and FE seeing low and high zeros together; on the prime side a one-sided bound at a sampling set |
| Critical-line sizes | TH head (B102), ZCG FE-pair flatness (B76), Lindelöf-type bounds | values of ζ on `Re s=½` near its zeros |
| Diagonal sign | B87, B88, B114, B129 | a positive object whose limit is Weil's kernel including the diagonal |
| Deformation families | ZCG heat, linear law on shifts, PTR cosine | uniformity of a law as the deformation parameter tends to `0` |

### 3.3 Classes

| Class | Observable / endpoint | Routes | Identity or scoped receiver |
|---|---|---|---|
| C1 Window form | `Q≥0` on every window | HF, SRT, AIP, ACT, ACS, RW, EWU, OWU | window ⇔ threshold ⇔ Hardy admissibility [L] |
| C2 Glued state | `κ(φ_c)−1` | SC, AKG | Grams are compressions [L] |
| C3 Window integer | collision charge, glued index, multiplicity, winding | WD, SC, TG, HEF, AIF | integrality supplies no subunit norm [L] |
| C4 Sectors | odd, even sign | CHMD, TT, OWU, EWU, ACT | exact format [L] |
| C5 Laguerre / continuation | Laguerre form on lines | TH, PTR, ZCG, LA, GTA, XN, HCF, PA | distinct receivers [L] |
| C6 Scheduled prime sums | history floor | FU, CFC, RP, LI | receivers retain their schedules [L] |
| C7 One-point precision | `ψ−x`, `M`, cyclotomic mode, Gaussian ceiling | WL, MC, PBM, RB, JAS, CTF, HCF | band ⇔ classical criteria [L] |
| C8 Selection / recurrence | trivial gauge; self-return | MC, BAG | target mass open [L] |
| C9 Realization | Krein defect, renewal nodes, Lee–Yang, cosine, standard forms | RN, PM, PTR; W1C | producers missing; internal, vacuum-fixing and half-sided classes excluded [L] |
| C10 Source completion | factorial energy, repair, co-shift | SEC, CDC, PCS; APF, EWJ, RFHM, WBF | zero-parameter bounds open [L] |
| C11 Local zero location | depth, near-line density, inner caps | WD, census, HEF, SRT, MZF | eight forms [L] |
| C12 Hodge–Lefschetz | HL, zero modes, top stratum | HF, ACS, RIT, EHT, TG, DZG, GWZ, HWV | zero modes radical [L] |
| C13 Sections and counts | source cone, RR | ACS, HF; IRK; WTZ, LST, KPA | Bézout ⇔ RH [L] |
| C14 Reflection | Rosati, Lewis, Krein, dispersion | PM, HF; W1C | coefficient identity, `V_p` [L] |
| C15 Canonical flow | `r,q,Ψ` | CWS, WTZ, DZG, GWZ, CSTW, SWC, CHT, RW, SZ | restoring bound [L] |
| C16 Blind cone | `𝒜(c)`, blind tests | PBAP, FADF, CHT | pinning, exact null test [L] |
| C17 Dimension zero | domination of point counts | ATD, DZG | bare domination ⇔ `Q≥0` [L] |
| C18 Angle dictionary | Hurwitz forms | AHD, ACS, LST, GWZ | `𝔽_q` angle = frequency [L] |
| C19 Two-site band / Frobenius graphs | `\|𝒞_m(f)\|≤W(f)`; `c_B(log p)≥−K` | GWZ, AOG, SWC, SRT, SOSZ | two-parameter family; spline orbit; one side at the prime degrees; one Weil test per prime [L] |
| C20 Selberg rigidity | Euler discrepancy, degree | SEL; ACS, HF | degree one classified [L] |
| C21 Camera | Weil-image readout | ZCG, SRT, MZF | conditional on isolation [L] |
| C22 Jet moments | Hankel, Toeplitz, jets | SWC, TH, LA, GWZ, PA, HCF | own sign per sequence [L] |
| C23 Density apertures | completeness radius | ZCG | face of C21 [L] |
| C24 Hermite–Biehler phase | dominant `A` | ZCG, FFP, PTR, PM | one shift axis [L/D] |
| C25 Onset aperture | `a*(ζ)` | every window route | closed interval [L] |
| C26 Hardy interval | `1∈ℋ(c)` | FADF; C1, C4 | criticality unconditional [L] |
| C27 Contact | `Ψ`, `K` bounded | CSTW, CHT, RW, SZ | RH ⇔ local boundedness [L] |
| C28 Finite free | stability of `R_d`; `N_d` | FFP, LA, TH | `sup_dN_d` off-line multiplicity [L] |
| C29 Hecke graphs | finite rational graphs | WTZ, CWS | templates below `27/5` [L] |
| C30 Li ladders | `λ_n≥0` | LI, ACS, HF | Toeplitz ladder [L] |
| C31 Repulsion | separation of zeros | ADO, ZCG, LA | amplifier [L] |
| C32 Long moments | `∫\|ζM\|²` | APR, CDG, WD, MZF; MC, CTF, WL | slope rigid; necessary length; collision counts of order `X²` past the height [L] |
| C33 Finite-degree detectors | Hausdorff, heat grid, slice, Jensen | PA, HCF, LA, FFP | no fixed family decides [L] |
| C34 Width axis | zero-free parameter | §2.3 | interior is quasi-RH |
| C35 Finite rungs | fixed window, rank, degree, ratio | §2.4 | verification decides each, not B13 [L] |
| C36 Prime-blind duality | Gamma, pole, `log n` | PBAP, EWU, OWU, CHT | RH ⇔ blind positivity [L] |
| C37 Inner factor | Blaschke product | CTF, MZF, AKLT, GWZ, CSTW, AIF | identity, Carleson, `N(ρ)` [L] |
| C38 Eisenstein carrier | `E*(z,½+ib)` | TH, PM, BHR, CTH, ASH; W1C | edge positivity shared [L] |
| C39 Passive medium | echo train of `Λ(n)/√n` | RW, PA, PTR, CHMD, SC | Schur band, tangent [L] |
| C40 Near-line clusters | comparably deep zeros | MZF, NGF, WVL | isolated rate 2; cluster wall open [L] |
| C41 Parabolic flow | gap laws; heat family | NGF, ZCG | blind to `t=0`; family-uniform finite-stratum law = RH [L] |
| C42 Log-mean | `T⁻¹∫log\|ζ\|` | WD, CTF, RW, ZCG, MC, PM | equivalences; `O(T)` depth [L] |
| C43 Abscissa split and dial | ZAL, AAL, linear laws, finite oscillation | BAG, JAS, SC, WL, ZCG, RW, IWT | split for every configuration; strict dial; rigid ¬AAL; AAL shift-invariant, linear laws not [L] |
| C44 Torus and columns | phases, insertion cone | TH, ZCG, FFP | Bernstein, locking, columns add [L] |
| C45 Production | Nair lattice, stencils, Stepanov over ℤ | WL, MC; AE, AKLT, AAD, AGT | rate = Mertens level [L] |
| C46 Characters and weights | Young projections, global trace | ACS, HF | positivity through rank 4 [L] |
| C47 Bohr space | far dipoles, recurrence | RW, HF, BAG | profile decomposition [L] |
| C48 Sign plane | `Ω(a,X)` | RW, ACS, SRT, ZCG, WD | typical-height sign [L] |
| C49 Critical compactness | Γ-liminf, Gårding, threshold identities | HF, SRT, AIP | `R_c=R_polar≤W` [L] |
| C50 Forced mollifier | near-extremal rigidity, Abel budgets | CTF, WD, AIF | rigidity; Szegő ratio [L] |
| C51 Horizon scattering | ringdown, horocycles, Farey counts, Lax–Phillips, Narain, seed responses, cavity energy | PM, BHR, ASH, CTH, AHMH | width-axis dictionary; complete and sharp cavity receiver [L] |
| C52 Beurling isolation | FE defect, count distance | APD, SEL, BAG, SPAL | three isolation metrics [L] |
| C53 Count and height | naive height, Tate limit, point counts, plane and ray counts, arithmetic section heights | ACS, HF, PM, CWS, AE, ASH, CTH, SOSZ, RIAC | every hyperelliptic curve; ℤ RH-strength on one ray per prime; `Q` not integer-valued, no integral kernel [L] |
| C54 Cut kernel | power-law solutions | WL, MC, RAC, AAD, CTF | kernel = zeros [L] |
| C55 Ledgers and parity | degree-`k` ledgers, exact identity | WL, MC, RAC, AAD, AGT | parity is size [L] |
| C56 Prime torus at finite time | boxes, savings, rounded orbit, mixing time | BAG, TH, SRT, ZCG, PTT | absolute savings [L] |
| C57 Kernel-valued certificates | Agler, Euler, head–tail | TH, RW, PTT, PM | tail-good [L] |
| C58 Hull | fibres over the torus | BAG, ZCG, PTT, AIF | natural boundary `½` [L] |
| C59 Krein law | universal decay, flux sign, reflection Krein form of the cavity | PM, BHR, ASH, ACS, AHMH | sign ⇔ RH; the resonance Krein form is blind [L] |
| C60 Fakes of the black hole | `(q,G,D)`, throat, genus two | PM, ASH, CTH; W1C | damping not a wave law [L] |
| C61 Metaplectic descent | cubic Gauss coefficient | MC, MMD | nonzero residue at `4/3`; theta identification open [L] |
| C62 Transport | return count, tail at a zero, partial returns, near-full tail events | BAG, ZCG, AAD, RAC, TAPO, HTG | right discs; zero or small value; `η>0` abundant [L] |
| C63 First return | brackets, precision law, heavy returns | BAG, SRT, TH, PTT, TAPO | constant precision open [L] |
| C64 Conditional tail | head–tail decoupling, collision arithmetic | BAG, TH, WD, TAPO, SPAL | below the Kronecker scale [L] |
| C65 Farey and horocycle | Farey discrepancy, horocycle mean | MC, PM, HWV, CTH | Franel–Landau, Zagier [L] |
| C66 Countermodel boundary | finite top layers | BAG, ZCG, JAS, SC, APD, IWT, SOSZ | firewall incl. one-offs across the critical line; `cosh` and two-scale `cosh` models; Wolff towers at finite monoids [L] |
| C67 Born rule | partner law, damping, boundary algebra, standard forms | PM, ACS, CTH, ASH | quadratic half = FE; count half = damping; Tomita collapse; half-sided exclusion [L] |
| C68 Topology of the prime complex | homotopy, persistence, fixed points, singular indices, orientation cover | MC, HF, ACS; ESG, HHAC, HWV, ADT, RIAC, HAT | classified, `s`-blind; `Σ index=1−M(N)`; cover weight `≥½`, `½` ⇔ RH [L] |
| C69 Thermal averaging | primon gas | SEL/Primon | Euler factors at real points `>1` [L] |
| C70 Relocation positivity | first-gap negativity | APD; ZCG, BAG | rational surgery detected [L] |
| C71 Two-scale law | asymptotic and local-below properties | every AAL route | decides no level of the dial [L] |
| C72 Exceptional rank | Turán windows, rank barrier | WL, ZCG, ACS, JAS, IWT | thick sets self-improve [L] |
| C73 Tower elimination | well-founded towers, thick crude count, Toeplitz count | WL, ZCG, ACS, IWT | thick crude count ⇒ AAL; + ZAL ⇒ RH [L] |
| C74 Frobenius substitute | returns freeze smooth polynomials; Adams operation on the torsion | BAG, PTT, IWT, ALST | approximate on the orbit, capped by precision; exact only on the torsion [L] |
| C75 Half-products | 𝔽₁-zonotope, `ℙ¹_ℤ` torsion, `ℍ³` and tree fibres, Frobenius graphs | ACS, HF, PM; SOSZ, HAT, AE | adelic Green pairing off the diagonal; no hyperbolic quotient; diagonal missing [L] |
| C76 Critical weight | damping versus renormalization; locked dampings | ACS, HF, PM; IWT, HHAC, RIAC, HAT | renormalization signless; atomic locking gives the discriminant; smooth archimedean self-energy logarithmic [L] |
| C77 Euler + FE calibration | finite-rank local squares; complete FE rigidity | ZCG, BAG, APD, SEL, EFT | succeeds at finite rank and identifies ζ among all systems with integrable defect [L] |
| C78 Finite-field counts | resultant, radial, orbit and orientation counts | ACS, MC, RIAC, SOSZ | counts before the form; Möbius as point defect [L] |
| C79 Prime-degree sampling | one-sided bounds at gap sets and sampling sets; Landau; tensor powers | ACS, SRT, WL, ZCG, IWT; SOSZ | RH at the primes; AAL at sampling sets; attainment free at the primes [L] |
| C80 Finite-layer identities | prime current, rough variance, height reflection | BAG, ZCG; EFT | exact in the ¬AAL world; height-preserving [L] |
| C81 Lefschetz–Stepanov over ℤ | Adams Frobenius, torsion auxiliaries, closed-point counts | ACS, BAG, WL; ALST | exact count = Chebyshev; RH = degree bound `ψ(N)` [L] |
| C82 Cavity receivers | seeds, odd tents, Maass and Hecke pairs, Baire | PM; AHMH, BHR | one cavity function sees every resonance; rate open [L] |
| C83 Heat divisor budgets | elapsed-depth and logarithmic-depth actions | ZCG, LA, WD; AES | initial budgets pay survival; finiteness of budgets open [L] |
| C84 Returns and transcendence | depth law, return–form duality, breadth cap, reciprocity of returns | BAG, TH, SRT; TTPO, ALST | depth bounded by Baker, breadth dark; a return is a pole-imitating zero cluster [L] |

C1, C4, C16, C19, C25, C26, C48, C49 and C79 are exact window-form dictionaries; C19 and C79 are the minimal one (one test per prime). C5, C28, C33 require all-root or all-degree control. C11, C32, C40, C42, C48 are asymptotic and weaker than RH; by C71 they cannot reach any level of the dial. C13 closes source supply, not effectivity. C8–C10 and C21 retain source-specific bounds. C23, C24, C31, C52 supply calibration or amplification. C45, C34, C65 and C68 are one axis (the Mertens level). C56, C57, C62, C63, C64, C74, C84 are one programme on the dark range. C43, C52, C66, C70, C71, C72, C73, C77, C79, C80 are one programme on the exceptional coordinate. C51, C53, C59, C60, C67, C75, C76, C78, C82 are one programme on the count and the diagonal.

### 3.4 Constructive transfers and their limits

| Sources / routes | Established transfer | Input not transported |
|---|---|---|
| RW/HF/SRT/AIP/ACS | exact receivers for form, band and source energy [L] | all-aperture sign |
| CACT/AHD→RW | `R_c=R_polar≤R_prim=R_high=W`; charged compactness [L] | the window sign itself; polar payment at every ratio |
| AHD below the onset | aperture ⇄ ratio exchange [L] | any increase of `a*(ζ)` |
| RW→flow | canonical system, restoring bound [L] | bound on `osc Ψ` |
| RW→count | cone points obey PNT `5/6` on the window's range [L] | windows of every length |
| AOG/SOSZ→GWZ | spline orbit and smoothed Frobenius pairs are two-site tests; the prime degrees suffice from one side [L] | the pair inequality at every prime |
| SOSZ→width | growth exponent of either one-sided bound at the primes or at any power-saving gap set = width [L] | a crude bound at every prime |
| SOSZ→WL/ALST | the Stepanov bound is the prime-window count `P≤A+K` [L] | the count itself |
| SOSZ→ZCG/IWT/BAG | one-sided bound at a sampling set ⇒ no deepest off-line zero ⇒ AAL [L] | the bound on a sampling set |
| ACS→RW/SRT | typical-height sign with Gaussian tails [L] | fixed `λ`; exceptional heights |
| APR→PTT/TAPO | necessary mollifier length ↔ primes `≤c log²T` [L] | a near-unit mollifier |
| TH↔ζ on the line | adaptive head leading term `=\|ζ(½+ib)\|²` [L] | sign near critical zeros |
| PM↔TH, PM↔BHR↔CTH | Eisenstein coefficients; horocycle mean = Farey count [L] | any exponent past `½` |
| BHR/AHMH cavity→PM | rate `y^α` of one cavity energy of Hecke eigenforms forces `Re ρ≤2−2α` at every zero; RH ⇔ `y^{¾−ε}` [L] | the rate |
| ASH Narain→PM | `¾` ⇒ RH; remainder VK [L] | any rate past VK |
| CTH standard forms→PM | RH ⇔ internal standard form realizing `Q` [L] | a realization outside the excluded classes (B114) |
| IWT→WL/ZCG/ACS | thick crude count ⇒ AAL; RH ⇔ ZAL ∧ thick `√X`; linear six-way TFAE [L] | the thick crude count (B110), ZAL |
| ZCG dial→all AAL routes | quantifier collapse, strict hierarchy, finite-rank exponent [L] | any level of the dial for ζ |
| ZCG heat→B13 inputs | family-uniform finite-stratum laws are RH; the Dirichlet series selects `τ=0` [L] | an input that uses the selection to locate zeros |
| ZCG two-scale law→all AAL routes | scale-separated inputs cannot decide B13 [L] | a two-scale input |
| BAG/AAD/TAPO | transport on right discs; tail transport; partial returns; near-full events [L] | existence of an exact event at a zero |
| IWT/ALST forced vanishing→BAG/ACS | Rouché copies cost the trivial separation bound; integrality creates zeros only on the torsion [L] | a freezing control beyond the cap |
| AAL producers | sparse bounds ⇒ AAL [L] | each source bound |
| AAD↔MC | rate ⇔ Mertens level [L] | a level past VK |
| RAC↔CTF | finite-energy cut-kernel mass annihilation ⇒ RH [L] | the annihilation |
| SOSZ/HAT/AE/RIAC→CTH | off-diagonal = pole − `ℍ³` Green − tree Green on ladders, all channels positive dampings; locked atomic diagonal = discriminant [L] | the diagonal; a smoothed damping presentation (B88, B129) |
| IWT critical weight→HHAC/RIAC | renormalized torsion is a renormalization, not a damping [L] | a positive damping family |
| CTH curve→ℤ | count law from point counts on curves; Tate principle [L] | a point count over ℤ |
| RIAC/HAT finite fields→ℤ | orientation cover over `𝔽_q` and over ℤ; weight `≥½` over ℤ [L] | weight `½`; a bounded-index self-map (B106) |
| ESG/HHAC/RIAC→MC | `M(N)` as barcode count, core Euler characteristic and `1−Σ` prime-vertex indices [L] | any cancellation |
| APD firewall→ZCG/BAG | positive classes, continuation and reflection carry finite layers [L] | intrinsic layers of ζ |
| RHTower/EFT Euler FE→ZCG | Euler product + FE force purity at finite rank and the rational primes at infinite rank with integrable defect [L] | transport (B112) |
| EFT finite-layer world→BAG/ZCG | ¬AAL ⇒ raw prime-current passage, top multiplicity, rough variance; FE preserves height [L] | replication (B128) |
| TTPO→BAG/PTT | depth of returns polynomial in `1/δ`; breadth cap at the Kronecker scale; reciprocity of returns with the zeros near the height [L] | breadth (B97); an FE-dependent step from returns to zeros |

## 4. U-Σ — the sign

Core problem: `1∈ℋ(c)` for every `c`. In cone form, some weight on every window; in causal form, an outer predictor; in flow form, `Ψ` locally bounded; in plane form, `Ω≥0`; in pair form, Hasse–Weil along the spline orbit; in **minimal form, one Weil test per prime**, `Re W(B+τ_{log p}B)` bounded below; in matrix form, every critical threshold `=⊤`, which is the window threshold plus polar payment, and under ¬RH the exclusion of a polar-orthogonal half-line ground state at finite `W`; in Laguerre form, horizontal-line positivity of Ξ; in theta form, the sign of `|ζ(½+ib)|²` plus second-order terms near the zeros. One scalar: `a*(ζ)`.

| Face | Routes / programmes | Reduction |
|---|---|---|
| Complete atomic matrix | HF, SRT, AIP, ACT, CACT, CSAR, ACPL, RAPT, TM, ADT, AHD | `R_c=R_polar=R_halfline≤W`; compactness closed; polar payment below `W` and ground-state orthogonality open |
| Ground energy, chain, cone | RW, EWU, OWU, CSTW, CHT | `a*(ζ)`; `Ψ`; `λ*` |
| Causal chain | RW, GWZ, AIF | outer predictors; Schur bands |
| Pair tests and Frobenius graphs | GWZ, AOG, SOSZ, SRT, ACS | two-site PD; spline orbit; one side at the prime degrees; one Weil test per prime |
| Local onset | RW, ACS, SRT, AIF | typical-height sign; size curve |
| Sectors, ground states | CHMD, ACT, OWU, EWU, SWC, FADF | two-sector format |
| Hardy, calibration | FADF, PBAP, CHT | arithmetic point in `𝒜(c)` |
| Moment problems | SWC, TH, LA, PA, HCF | Stieltjes, Hamburger |
| Theta spectrum | TH, CAF, TCS, AIF, PTT | Euler operators; head = `\|ζ(½+ib)\|²` |
| Heat, cosine, Jensen | ZCG, PTR, LA, NGF, FFP | small time at all heights |
| Glued state | SC, AKG | Beurling-schedule sign |
| Window tower | CWS, WTZ, DZG, GWZ, SWC | kick admission; two sites |
| Visibility | WVL, SRT, DCI, ZCG | output of every window theorem |
| Edge, zero modes | EHT, HWV, DZG, GWZ | no zero mode |
| Effectivity, RR | ACS, LST, RIT, HF, KPA | Bézout is sign |
| Li, Cayley | LI, ALG | `λ_n≥0` |
| Suzuki | SZ | first variation |
| Scheduled sums | FU, CFC, RP, LI | history floors |
| Charge | GTA, TG | cofinally small charge |
| Renewal | RN | joint nodes |
| Adelic Green pairing and compensation | HHAC, AE, SOSZ, RIAC, HAT | pole − `ℍ³` Green − tree Green; spherical compensation; diagonal |

## 5. U-Π — precision and production

Core problem: square-root precision of one smoothed prime count; in **minimal form, the Stepanov bound at the prime degrees** `P(p)≤A(p)+K`; in tower form, a square-root prime deviation on a thick set of geometric scales together with ZAL; in Deligne form, prime moments of the traces uniform in the tensor power. Production, Farey discrepancy, the Farey count, the Euler characteristics of the nerve and core, the barcode, the prime-vertex indices, the gluing charge and the orientation cover read the same statement through integers, fractions, simplices, persistence, fixed points and discriminants; none has a mechanism independent of the Mertens level. The dark range is where every sub-RH precision question sits; the archimedean Frobenius substitute that would produce a crude count there is capped by precision, and exact vanishing over ℤ lives only on the torsion of the prime torus.

| Face | Routes / programmes | Reduction |
|---|---|---|
| Reflection-pair coupling | SWC, GWZ, CSTW, AOG | collar Hankel − smoothed count |
| Classical one-sided counts | WL, PBM, RB, JAS, CTF, HCF | RH-level equivalence; Gaussian ceiling |
| Thick tower counts and the dial | WL, ZCG, ACS, IWT | thick crude count ⇒ AAL; + ZAL ⇔ RH; relative counts = linear laws |
| Prime-degree crude bounds | ACS, SOSZ, WL | Stepanov bound = prime count at the primes; width = growth exponent; tensor moments |
| Collective kicks | SWC, FADF | beyond size, by sign |
| Cyclotomic mode, gauge torus | MC, CAF, AGT | exponent `½` at the trivial point |
| Integer producers | WL, AKLT, ASRP, AE, AAD, RAC, ALST | rate = Mertens level; exact Stepanov over ℤ = Chebyshev; fixed-point auxiliary of log length `ψ(N)` |
| Frobenius substitute | IWT, PTT, TAPO, ALST | returns freeze smooth polynomials; precision cap; exactness only on the torsion |
| Parity | WL, MC, RAC, APR | exact identity pins `λ` |
| Möbius, nerve, core, Farey, cover, descent | MC, HWV, ADT, HHAC, ESG, RIAC, HAT, CTH, MMD | half-power cancellation; weight of the orientation cover |
| Short-sum barrier | every route, PTT | absolute savings |
| First return | BAG, PTT, TAPO, TTPO | constant precision open; depth law by Baker, breadth cap at the Kronecker scale |
| Conditional tail and collisions | TAPO, SPAL, IWT | Gaussian below Kronecker; collision counts of order `X²` past the height |
| Near-line density | WD, CDG, MZF, AIF | log-mean; depth `O(T)` |
| Long moments | APR, CDG, WD, MZF; CTF | necessary length = primes `≤c log²T` |
| Budgets | CTF, AIF | second expression; Szegő ratio |
| Negative moments | MZF, MC, ADO | Green potential moments |
| Deciding-input filters | ASRP, APR | parity, purity, precision, aperture |
| Census | SRT, CDG | signed pair data past bandwidth one |
| Sharp horizon sources | CTH | Möbius × circle remainder, beyond RH |

## 6. U-Γ — selection, reflection and transport

Core problem: source-defined arithmetic control of `ρ↦1−ρ̄` and of vertical transport; in count form, the count half of a Born rule whose quadratic half holds, on one ray per prime; in horizon form, one rate or one reflection Krein sign of a complete cavity receiver; in configuration form, one level of the linear dial — a two-scale Dirichlet-series input that uses the Euler product and the FE together and converts the FE into transport; on the prime side, a one-sided bound at a sampling set of primes. FE + Euler product with integrable defect identify ζ, so every such input concerns the exact identities of ζ.

| Face | Routes / programmes | Status |
|---|---|---|
| Recurrence, gauge | MC, AGT, BAG, AAD, RAC, PTT, TAPO | transport closed on right discs; tail transport; exact events open |
| Abscissa split and dial | BAG, JAS, SC, WL, AKLT, ZCG, RW, IWT, SOSZ | split for every configuration; strict dial; rigid ¬AAL; two-scale law; family law; sampling-set and metric producers |
| One-off and FE models | APD, SPAL, RAC, AIF, ACP, IWT | firewall incl. one-offs across the critical line; `cosh` and two-scale `cosh` models; ζ isolated in every FE-defect class |
| Euler + FE calibration | RHTower, APD, SEL, EFT, ExactEventTheory | finite-rank purity; complete FE rigidity for `L¹`/`L²` defects; Poisson rigidity |
| Time-zero selection | ZCG, NGF | parabolic tools blind; family-uniform laws are RH; the Dirichlet series selects `τ=0` |
| Weil cone, lattices | RHTower, GWZ, FADF, CHT | at most `{Λ}`; nonempty iff RH |
| Selberg class | SEL | degree one classified |
| Camera identification | ZCG, SRT, MZF | conditional readout |
| Reality at near-coincidences | ZCG, ADO | FE pair forces small values |
| Diophantine repulsion | ADO, ZCG | `0∉E` open |
| Euler columns, carriers | ZCG, FFP, AIF, TAPO | Euler coordinates stop at `Re s=1` |
| Horizon and count | PM, BHR, ASH, AHMH, CTH; W1C, ACP | Krein law; Born rule; Tate limit; complete and sharp cavity receiver; reflection Krein form; internal, vacuum-fixing and half-sided realizations excluded; width axis |
| Rosati, Frobenius at infinity | CWS, WTZ, GWZ, AOG | sharpened |
| Source completions | CDC, SEC, PCS; RFHM, EWJ, APF, WBF | source versus forcing |
| Hull | PTT | Liouville point extreme |
| Surface of Spec ℤ | SOSZ, HAT, AE, RIAC | adelic Green pairing off the diagonal; no hyperbolic quotient; locked atomic diagonal = discriminant; diagonal missing |
| Finite-layer world | EFT, ZCG, BAG | prime-current passage; rough variance; height reflection; replication open |
| Function-field calibration | many | AAL free by periodicity; ZAL = purity; count law at every genus; orientation and orbit counts |

## 7. Cross-family seams

| Seam | Statement | Routes |
|---|---|---|
| Σ ∩ Π: reflection pairs | `W(f±f∘R)=2W(f)±2𝒞_m(f)` | SWC, GWZ, CSTW, AOG, WL [L] |
| Σ ∩ Π: Hardy form | `W=H−P` | FADF [L] |
| Σ ∩ Π: plane and barrier | sign past `log log X` needs short-sum bounds | ACS, AIF [L]; [D] |
| Σ ∩ Π: cone counts | window positivity ⇒ PNT `5/6` on its range | CHT [L] |
| Σ ∩ Π: aperture exchange | window positivity ⇒ depth-`¼` zero-free region | AHD [L] |
| Σ ∩ Π: theta head | head = `\|ζ(½+ib)\|²` | CAF, TCS, AHD [L] |
| Σ ∩ Π: spline orbit growth and integer degrees | orbit correlation growth = zero width; crude integer-degree bound = width | AOG, SOSZ [L] |
| Σ ∩ Γ: chain and mimic | sampling atoms are positive mimics | CSTW, ZCG [L] |
| Σ ∩ Γ: exact completion | coefficient Weil energy = Krein form | RIT [L] |
| Σ ∩ Γ: integer probes and Tate limit | Weil form on the Hecke lattice = Krein square; RH ⇔ Tate limit of a count; `Q` not integer-valued | ASH, CTH [L] |
| Σ ∩ Γ: Frobenius pairs | window sign ⇔ Hasse–Weil for smoothed graph pairs | SOSZ [L] |
| Σ ∩ Γ: Li and Hodge | Hodge index = Metzler sign = Li | ALG [L] |
| Σ ∩ Γ: archimedean fibre | Weil's archimedean + pole weight = `4πG_{1/2}−4cosh(u/2)` on `ℍ³` | SOSZ [L] |
| Π ∩ Γ: prime-side AAL and the dial | ¬AAL is a finite oscillation; thick crude count ⇒ AAL; relative thick counts = linear laws; `Θ∞` = finite-rank Chebyshev exponent | ZCG, IWT [L] |
| Π ∩ Γ: cut kernel | zeros are solutions of the Chebyshev moment system | RAC [L] |
| Π ∩ Γ: count | Λ is a torsion intersection number; off-diagonal Weil from dampings | AE, HHAC, SOSZ [L] |
| Π ∩ Γ: tail | zeros of ζ = zeros of every Euler tail; AAL = tail transport | TAPO [L] |
| Π ∩ Γ: first return and freezing | weak return = extreme value of `ζ(1+it)`; returns freeze smooth polynomials; precision cap | TAPO, IWT [L] |
| Π ∩ Γ: horocycle and Farey | horocycle rate = Farey count rate = zero-free region | BHR, CTH [L] |
| Π ∩ Γ: relocation | rational relocation fails positivity at the first gap | APD [L] |
| Π ∩ Γ: annihilators | positive annihilators kill finite layers at exponential cost; inverses oscillate | APD [L] |
| Σ ∩ Π: gluing and topology | Redheffer = reduced Euler characteristic; prime-vertex localization `1−M(N)` | HWV, ADT, HHAC, ESG, RIAC [L] |
| Σ ∩ Π ∩ Γ: one test per prime | `Re W(B+τ_{log p}B)=2c_B(0)+2c_B(log p)`, `c_B(log p)=A(p)−P(p)`; the defect of `Γ_1+Γ_p` | SOSZ [L] |
| Π ∩ Γ: sampling | a one-sided bound at a sampling set of primes leaves no deepest off-line zero | SOSZ [L] |
| Σ ∩ Γ: adelic Green formula | Weil's off-diagonal = pole − Green functions of `ℍ³` and of the trees `T_p` at the critical parameter | HAT [L] |
| Π ∩ Γ: exactness | integrality exact only on the torsion; minimal fixed-point auxiliary has log length `ψ(N)` | ALST [L] |
| Σ ∩ Γ: cavity | horocycle rate of one cavity energy = zero-free region; reflection Krein form PSD ⇔ RH | AHMH [L] |
| Π ∩ Γ: finite-layer current | ¬AAL ⇒ raw prime-current passage to `−ζ′/ζ` on a high strip | EFT [L] |

## 8. Route → core map

| Route | Core | Halves | Classes | Face |
|---|---|---|---|---|
| WL | Π (Σ) | both | C7, C19, C32, C43, C45, C54, C55, C72, C73, C79 | bounded endpoint energy; integer lag; prime-window count at the primes; thick tower count; linear dial |
| RW, EWU, OWU | Σ | both | C1, C4, C15, C16, C19, C22, C25–C27, C39, C43, C47, C48 | `a*(ζ)`; `Ψ`; causal; polar ground energy |
| FU, CFC, RP | Σ | both | C6 | full-history bounds |
| SZ | Σ | both | C15, C27 | completed Abel residual |
| LI | Σ (Π) | both | C30, C6 | Cayley–Li sign |
| PA (HJ) | Σ (Π) | both | C5, C22, C33, C39 | rows below the explicit shift |
| TH | Σ (Γ) | both | C5, C22, C33–C35, C38, C44, C56, C57, C64 | head = `\|ζ(½+ib)\|²`; amplitude oscillation |
| HCF | Σ (Π) | both | C5, C7, C22, C33 | two grids; Gaussian ceiling |
| LA | Σ | ZAL side | C5, C22, C28, C33 | outer roots |
| GTA | Σ | both | C5 | small charge |
| XN | Σ | both | C5 | covering discs |
| MC | Π (Γ) | both | C7, C8, C12, C32, C45, C54, C55, C61, C65, C68, C78 | trivial gauge; Farey; topology; orientation cover over ℤ |
| TT | Π (Σ) | both | C4 | endpoint upper bound |
| TG | Π, Σ | both | C3, C12 | subunit trace norm |
| HF | Σ (Π, Γ) | both | C1, C12–C15, C18, C25, C47, C49, C53, C75, C76, C79 | polar payment and ground-state orthogonality; head windows; one test per prime; count; diagonal |
| SRT, AIP, ACT | Σ (Π) | both | C1, C4, C11, C19, C21, C25, C48, C49 | complete matrix = window + polar payment |
| SC | Σ, Π (Γ) | AAL branch; both | C2, C3, C7, C39, C43 | glued state; undamped cone ⇒ AAL |
| CHMD | Σ | both | C4, C1, C39 | odd sector |
| RN | Σ | both | C9, C1 | joint nodes |
| WD | Π (Σ) | ZAL side | C3, C11, C32, C40, C42 | long moments; log-mean |
| PM | Γ (Σ) | both | C9, C14, C38, C51, C53, C59, C60, C65, C67, C82 | reflection Krein; cavity rate; count; standard forms |
| JAS | Π | AAL branch; both | C7, C19, C43, C72 | moving power; shell positivity |
| CTF | Π | both | C7, C19, C32, C37, C42, C50, C54 | BSY, budgets, cut kernel |
| PBM, RB | Π | both | C7, C19 | abscissa, extremal |
| BAG | Γ | AAL | C8, C43, C47, C52, C56, C58, C62–C64, C66, C70, C71, C74, C80, C84 | target mass; tail transport; finite-layer current; returns |
| ACS | Π (Σ, Γ) | both | C13, C1, C12, C18, C19, C20, C30, C46, C48, C53, C67, C73, C75, C78, C79, C81 | source sign; one side at the prime degrees; sampling sets; count law; Stepanov over ℤ |
| SEC, CDC, PCS | Γ | both | C10 | zero-parameter conditions |
| PTR | Σ (Γ) | both | C9, C5, C24, C39 | Laguerre below VK |
| ZCG | Γ (Σ) | ZAL side, AAL layers | C5, C21, C23, C24, C31, C40, C41, C43, C62, C66, C70–C72, C77, C79, C80, C83 | collisions; abscissa laws; dial; heat family and Dirichlet selector; heat budgets |
| Candidates APF, EWJ, RFHM, WBF | Γ (Π) | — | C10 | missing landing |
| Candidate IRK | Γ (Π) | — | C13 | trace with Chern charge |
| Candidates EGC, FEL, MSC | Σ (Π) | — | C6, C1 | landing; history; Sonin sign |
| Candidate W1C | Σ (Γ) | — | C9, C5, C38 | positive realization |
| IWT (support) | Π, Γ | both | C43, C71–C74, C76, C79 | exceptional coordinate; elimination; dial; metric recurrence |
| SOSZ (support) | Γ, Σ, Π | — | C19, C53, C75, C76, C79 | half-products; `ℍ³` fibre; prime degrees; sampling; tensor powers; count door |
| RIAC (support) | Π, Σ | — | C68, C76, C78 | prime boundary; compensation; vertex indices; gluing and section counts; orientation cover; finite-field counts |
| HAT (support) | Γ, Σ | — | C68, C75, C76 | carriers; trees; adelic Green formula; locked dampings; cover weight |
| ALST (support) | Π | — | C74, C81 | Adams Frobenius; torsion auxiliaries; Stepanov count = Chebyshev |
| AHMH (support) | Γ | — | C51, C59, C82 | seeds; cavity receivers; Krein forms |
| EFT, ExactEventTheory (support) | Γ | AAL | C77, C80 | FE rigidity; finite-layer current; height reflection |
| TTPO (support) | Π, Γ | — | C84 | linear forms; depth and breadth of returns |
| AES (support) | Σ | ZAL side | C41, C83 | heat-divisor budgets |
| TAPO, SPAL (support) | Π, Γ | AAL | C62–C64, C52 | first return; tail; collisions |
| PTT (support) | Π, Γ | — | C56–C58 | orbit at finite time; hull |
| AAD, RAC (support) | Π (Γ) | — | C45, C54, C55, C62 | stencils; kernel; parity; transport |
| ASH, BHR, CTH (support) | Γ | — | C51, C38, C53, C59, C60, C65, C67 | ringdown; Krein law; count law; standard forms |
| MMD (support) | Π | — | C61, C78 | cubic descent |
| AE, KPA, HHAC (support) | Σ, Π | — | C53, C45, C68, C76 | Tate law; torsion |
| ESG (support) | Π | — | C68 | persistence |
| APD, SEL, Primon (support) | Γ | AAL | C20, C52, C66, C69, C70, C77 | firewall; isolation; relocation; annihilators |
| VHR (support) | — | — | C35 | rungs |
| CSTW, CHT, AIF (programmes) | Σ, Π, Γ | both | C15, C16, C27, C37, C42, C50 | flow; cone; inner field |
| FADF, SWC, WVL, WTZ | Σ | — | C26, C4, C25, C29 | Hardy; format; visibility; graphs |
| APR, AKLT, ASRP | Π | — | C32, C7, C45 | length; filters; production |
| PBAP, W3 | Σ (Γ) | — | C16, C36 | blind positivity |
| Representation, AK | Γ (Σ) | — | C46 | characters; weights |
| HWV, ADT | Σ, Π | — | C12, C65, C68 | nerve; gluing determinant |

## 9. What a closing argument must supply

| Needed | Present over ℤ | Missing |
|---|---|---|
| Both halves of the split | split for every configuration; strict dial; rigid ¬AAL; AAL = transport [L] | one ZAL input; one AAL input, or `ZAL⇒RH` |
| A two-scale input for the dial | two-scale law, firewall, `cosh` models, heat family, free classes, finite-rank Euler + FE purity [L] | a Dirichlet-series statement using the Euler product and the FE together, seeing low and high zeros, converting the FE into vertical transport |
| An elimination step | exceptional-rank window theorem, thick sets, infinite-rank Hasse–Weil principle; free at the integer degrees [L] | none: elimination is available |
| A crude count | one side of Hasse–Weil at the prime degrees ⇔ RH; the Stepanov bound is the prime count `P(p)≤A(p)+K`; sampling sets ⇒ AAL; thick crude count ⇒ AAL; RH ⇔ ZAL ∧ thick `√X`; Stepanov over ℤ to Chebyshev [L] | the crude bound at the primes (B130); a well-founded tower (ZAL) |
| A Frobenius substitute | returns freeze smooth polynomials; approximate forced vanishing; the Adams operation is exact on the torsion [L] | exact returns do not exist; integrality gives no zeros at returns; Rouché copies capped by precision; a counting argument beyond the cap |
| Budget, not exact sign | subexponential floor ⇒ RH [L] | any such floor |
| Sign of the minimal object | band ⇔ `1∈ℋ(c)` ⇔ `λ*→0` ⇔ pair Hasse–Weil ⇔ one Weil test per prime [L] | the sign of `B+τ_{log p}B` at every prime |
| Uniformity in length | each length a rung; critical thresholds = window + polar payment [L] | every length; polar payment below `W` |
| Flow | restoring bound, `Ψ`-boundedness ⇔ RH [L] | a bound on `osc Ψ` up to contact |
| Heights | size curve [D]; typical-height sign [L] | sign past `log log X` at rare heights |
| Across primes | columns add; Euler coordinates stop at `Re s=1` [L] | amplitude oscillation |
| The critical line | theta head `=\|ζ(½+ib)\|²`; FE-pair flatness [L] | second-order sign at the critical zeros |
| Time selection | parabolic laws; family-uniform laws are RH; the Dirichlet series selects `τ=0` [L] | an arithmetic input that uses the selection at the zeros, not only at `σ→∞` |
| Precision, occupancy | rate 2 isolated; depth `O(T)` [L] | a non-outer control of the inner mass; cluster bound |
| Dark range | brackets; conditional tail below Kronecker; collision counts of order `X²` [L] | the tail law at the Kronecker scale; lower bounds for exact tail events; proportional saving |
| Count from geometry | off-diagonal as pole − `ℍ³` Green − tree Green, each a positive damping; Tate principle; point counts on curves; finite-field counts; locked atomic diagonal = discriminant [L] | the diagonal: a counterterm-free smoothed damping (B88, B129), a count without `Q` on one ray per prime (B87) |
| Archimedean carrier | `ℍ³` Green function at `s=½` on one geodesic; trees at the finite places; no hyperbolic quotient [L] | the self-energy of the configuration, i.e. the diagonal |
| Reflection | coefficient completion; complete and sharp cavity receivers; reflection Krein form; Born rule; standard-form trichotomy [L] | `D_s≥0`; reflection Krein PSD; a realization outside the excluded classes; any horizon exponent past `½` |
| Sparse exceptions | rigid ¬AAL; tower excursions; transport; partial returns [L] | an exact rare event at a zero or a contradiction in ¬AAL |
| The finite stratum | TFAE of finite index, lattice index, finite off-line set, heat count, eventual RH; towers decide; Lindelöf [L/K] | a two-scale Euler-product input excluding a finite off-line set (B13) |
| Production | exact integrality; VK rate; kernel; parity identity [L] | a level past VK |
| Topology | classified persistence; localization `Σ index=1−M(N)`; orientation cover over ℤ of weight `≥½` [L] | weight `½`: signed cancellation of the local indices at `√N`, a bounded-index self-map of the cover |
| FE as an identity | complete FE rigidity; finite-layer passage laws; FE preserves height [L] | an identity of ζ that moves a zero in height |
