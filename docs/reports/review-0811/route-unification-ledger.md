# Route unification ledger — status quo

The 38 live formulations and 9 candidates are faces of three core problems: **U-Σ** (sign), **U-Π** (precision and production) and **U-Γ** (selection, reflection and transport). Their RH-level endpoints meet at one object: the **arithmetic Hardy inequality** `P≤H` on every window, equivalently the **band** `|𝒞_m(f)|≤W(f)` of a test and its mirror, equivalently nonnegativity of one quadratic form `Q` on integer probes, equivalently **`Q` is the Tate limit of a count**, equivalently **Hasse–Weil for the smoothed Frobenius graphs of Spec ℤ at every integer degree**. U-Σ reads it as a form on the window, U-Π on the prime side, U-Γ on the zero side.

Transversal to the three, RH splits into **ZAL** (finitely many zeros beyond each depth) and **AAL** (zero transport in height), with a strict **linear dial** between them: `Pure ⊊ AAL ⊊ LinAt C₁ ⊊ LinAt C₂ ⊊ (ZAL⇒RH) ⊊ B13`. Below the three lie four structural gaps that every family meets: the **dark range**, primes past the Kronecker scale where conditioning on the head needs a Dirichlet polynomial longer than the height; the **missing count**, a nonnegative arithmetic function with quadratic Tate limit `Q`, equivalently a counterterm-free damping presentation of the diagonal of Weil's form; the **two-scale Euler-product-and-FE input**, a Dirichlet-series statement that couples low and high zeros, uses the Euler product (which the heat family lacks) and the FE (which the one-offs lack) together, and turns the FE into vertical transport; and the **precision cap of the archimedean Frobenius**, which makes every phase-freezing argument at the returns of the prime orbit cost exactly the trivial bound.

**Why there are three cores [D].** No test is compact on both sides of the explicit formula. A compact prime side (U-Σ) leaves infinitely many zero modes and only an exact sign decides; a localized zero side (U-Π) lets a crude bound decide (one Gaussian prime ceiling per rational height ⇔ RH; a bounded orbit correlation at the integer degrees ⇔ RH; ZAL plus a square-root prime deviation on a thick set of scales ⇔ RH [L]) but leaves the prime side at square-root precision; U-Γ is the involution `ρ↦1−ρ̄`, the selection of ζ and the transport of its zeros. The curve proof uses two freebies that ζ lacks: finite rank, which makes elimination algebraic and ZAL in tower form automatic, and zeros periodic in height, which make AAL automatic [L]. At finite rank even Euler product + FE alone force purity, by local squares [L]; over ℤ the elimination step exists at infinite rank on thick sets [L] and the crude step is open.

Corpus checkpoint: commit `99bc99520c` (2026-11-08). Evidence: `[L]` Lean source; `[K]` with transitive axiom audit; `[S]` unfinished or unintegrated; `[D]` deduction; `[N]` numerical; `[C]` classical. Locators: [frontier map](../rh-current-frontier-map.md), [scoped obstructions](../rh-killed-routes.md), [walls](walls-ledger.md), [routes](route-obstacles.md), [summary](obstacles-summary.md).

**Equivalence through RH transfers truth, not mechanism.** Only an explicit source identity or a proved transport moves an estimate between routes. Section 3 separates the two.

## 0. Unifying statements

- **One split [L].** For every zero configuration, purity ⇔ ZAL ∧ AAL. For ζ: RH ⇔ ZAL ∧ AAL ⇔ ZAL ∧ `LinAt C` (any real `C`) ⇔ ZAL ∧ zero-disc weak recurrence ⇔ ZAL ∧ subexponential polar ground energy ⇔ ZAL ∧ thick `O(√X)` prime deviation ⇔ ZAL ∧ a positive count of one Weil tower. ZAL ⇒ qRH. `qRH ∨ AAL` [D].
- **One dial [L].** `LinAt C ⇔` eventual-to-global at slope `C`; `∃C` collapses to `ZAL⇒RH`; `AAL ⇔ ∀C>1`; the levels are strictly separated by explicit configurations (harmonic-depth configurations sit between `ZAL⇒RH` and B13). For ζ at `C≥1`: `LinAt C ⇔` finite-rank Chebyshev self-improvement ⇔ all-scale lag `O(e^{C(Θ∞−½)L})` ⇔ thick tower lag ⇔ thick prime deviation `O(X^{½+C(Θ∞−½)+ε})`.
- **One exponent [L].** `Θ∞` is the infimum exponent of `ψ(x)−x` modulo finite exponential sums. The finite stratum is `ψ(x)−x` = a finite exponential sum + `O(x^{½+ε})`.
- **One transport [L].** AAL ⇔ every right zero has zeros with real part `>Re ρ−ε` at arbitrarily large height ⇔ every right zero transports to arbitrarily high points where every Euler tail vanishes with full amplitude. Approximate tail cancellation (`η>0`) is abundant at every strip point; exact cancellation (`η=0`) near right zeros is the content of AAL.
- **One two-scale law [L].** No property of the zeros above a height and no property of the zeros below a fixed height decides the finite stratum, any linear law or AAL.
- **One family law [L].** A finite-stratum law valid on every heat deformation `H_t` (`t>0`) is RH; linear AAL along the heat flow is RH.
- **One analytic freedom [L].** FE, order one and reality admit every finite top layer, also over a remainder at positive asymptotic abscissa. On tower level sums the FE acts only as `S(−ν)=conj S(ν)`.
- **One firewall [L].** Continuous Beurling systems, integer-norm and rational-prime Euler products with linear counting, and one reflection pair each carry a finite top layer; positive two-prime and Hecke polynomials annihilate every finite zero set, at exponential mass cost in the multiplicity, and their inverses oscillate. The one ingredient no countermodel combines is an Euler product together with the FE.
- **One calibration where Euler + FE succeed [L].** A finite Euler product with an FE of conductor `ΠP` has `a_p²=p` and every zero on `Re s=½`; a Beurling system with exact FE is the rational primes.
- **One free class [L].** Recurrent configurations, exponential polynomials, curves, vertically periodic configurations, strip almost periodic functions and uniformly approximable Dirichlet series obey AAL.
- **One rigid alternative [L].** ¬AAL ⇔ an isolated top over an infinite remainder ⇔ finite top and bottom layers at the same heights ⇔ `ψ(x)−x` a finite oscillation at leading order ⇔ two-prime dilation annihilation ⇔ syndetic lag excursions at every base.
- **One elimination [L].** The exceptional rank decides Turán windows; no thick set carries a bound below an isolated top; density `1−1/k` sets do not self-improve; well-founded towers bounded on a thick set have only the critical layer visible; Wolff towers show well-foundedness is needed; continuous levels see every zero (a crude bound on all `L` is a zero-free region).
- **One finite stratum [L/K].** Finite negative index of `K_ζ` ⇔ finite index on one two-prime lattice ⇔ finitely many off-line zeros ⇔ bounded heat count ⇔ RH above some height ⇔ eventual slice positivity; in the stratum Lindelöf holds and RH ⇔ one non-blind prime tower PD ⇔ one Weil tower Toeplitz positive ⇔ one tower bounded on a thick set.
- **One scalar [L].** Every window route measures `a*(ζ)`. Contact is `Ψ=½log H₁` blowing up; RH ⇔ `Ψ` locally bounded.
- **The critical curve is the window plus one inequality [L].** `R_c=R_polar≤R_prim=R_high=W`; the charged compactness passage is closed; the only gap is polar payment at every `R<W`.
- **One exchange [L].** Below the onset, aperture `a` buys a depth-`¼` zero-free region to height `e^{a/K}`, which buys a sharp pole and `R_c≥c₁e^{c₂a}`; no step raises `a*(ζ)`.
- **One splitting order [L].** Conductor first, position second.
- **One sign plane [L/D].** Size reaches all heights to `a≈log log X`; typical heights to `a=δlog T/(64M²)`.
- **One frequency diagonal [L].** Weil's form is the average of its frequency packets.
- **One scale [L/D].** A near-unit mollifier needs length `exp(c log²T)`; an Euler mollifier reaching it uses every prime up to `≍log²T`; absolute non-alignment begins at length `≈L²`; conditional tail laws hold only below the Kronecker scale; past the height long mean values are collision counts of order `X²` whose constant is binary.
- **One tail [L].** Zeros of ζ are zeros of the Euler tail at every cut; returns at right zeros are tail-bad; every certificate past `Re s=1` is a tail-good condition.
- **One first return [L].** `R(y,η)` bracketed at every precision; weak return = extreme value of `ζ(1+it)`; proportional saving = no early heavy return.
- **One Frobenius substitute, capped [L].** Returns freeze smooth Dirichlet polynomials; `J` moment conditions force approximate vanishing at every return; a Rouché copy needs `J≤e²r log N+log(1/δ)`, so the Stepanov count is the trivial separation bound; the prime orbit has one fixed point.
- **One collision arithmetic [L].** Smooth × prime mean squares are diagonal plus collision counts fixed by gcd classes.
- **One width axis [L/D].** Floor rate, damping rate, abscissa, gauge exponent, stability line, long-moment slope, Möbius zero abscissa, integrality exponent, stencil rate, PTR `h`, TH `a`, Hecke level, ringdown gap, horocycle, Farey, Narain and cusp-energy exponents, spline-orbit growth rate, integer-degree crude Hasse–Weil exponent, prime-gap exponent of the prime planes: interior values are zero-free strips; all unconditional savings sit at VK.
- **One Mertens level [L].** Stencil rate = Mertens level; Farey discrepancy, the nerve and core Euler characteristics, the Farey count at order `C` and `1−Σ_p` prime-vertex indices are `M(N)`.
- **One topology [L].** The prime-product complex is a sphere bouquet with classified persistence, independent of `s`; prime-vertex self-maps homotopic to the identity fix exactly the primes, exits are bouquets, local indices are relative singular Euler characteristics summing to `1−M(N)` and unbounded below.
- **One cancellation geometry over `𝔽_q` [L].** Möbius over `𝔽_q[T]` is the point defect of an orientation cover of exact size `qⁿ` (`n≥2`); Möbius over `ℤ[ω]` is a cubic Gauss coefficient. Over ℤ neither structure is constructed.
- **One horizon [L].** Pulse ringdown, horocycle mean, Farey count, Lax–Phillips mode, Narain remainder and cusp energy read the poles `ρ/2`; gain `δ` past the trivial rate ⇔ strip `2δ`; RH ⇔ `y^{¾}` ⇔ `e^{−t/4}`; the mirror-odd sector is a cavity, the zeros live in the mirror-even half.
- **One Born rule [L].** A count law = nondegenerate Born rule (the FE) + positivity (universal damping). The partner involution has a positive state iff damped; internal modular conjugation collapses to the Hilbert adjoint; vacuum-fixing partners and half-sided Borchers inclusions cannot carry `Q`; RH ⇔ an internal standard form realizes `Q`.
- **One count [L].** Tate principle both ways; curves: the integral defect is a point count; fakes: count, not quadratic; ℤ: quadratic, count missing, `Q` itself not integer-valued; every integer plane `⟨Γ₁,Γ_n⟩` needs one binary count.
- **One surface [L].** Off the diagonal Weil's kernel is a rank-two pole minus two positive dampings: the archimedean Frobenius `2π√(mn)G_{1/2}(d)` on `ℍ³` (cusp `k=0`, jets `k≥1`) and the twisted torsion energy on `ℙ¹_ℤ`; atomic graphs have genus `≍N log N`, carried by the jets; smoothed pairs pass Hasse–Weil ⇔ RH; the sign sits in the diagonal, the Newtonian self-energy of a point of `ℍ³`.
- **One critical weight [L].** Damping is lossless; renormalization carries no sign.
- **One crude regime absent [L/D].** In the size coordinate constant-factor bounds are false and `x^{½+ε}` is RH; crude regimes live in the exceptional coordinate, on thick sets of scales and at the integer degrees of the Frobenius graphs, where the self-improvement is free.
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
- **One isolation [L].** ζ is a singleton in FE defect `≤1/6400`, in count distance `o(log n)` and under the exact parity identity.
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
| Frobenius graphs | Hasse–Weil for every pair; at every integer degree; at the squares; at prime pairs | SOSZ [L] |
| Plane counts | a binary `ℕ`-count with Tate limit `δ_n` on every integer plane | SOSZ [L] |
| Hamiltonian | `Ψ` locally bounded | CSTW, AIF [L] |
| Lattice | Schur parameters in `(−1,1)` | GWZ [L] |
| Causal | outer predictor at every window | AIF [L] |
| Bohr | orbit correlations relatively compact | AIF [L] |
| Critical thresholds | `R_c=R_polar`, `R_prim=R_high=W`, all `=⊤` | AHD [L] |
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
| Horocycle / Farey count | rate `y^{¾−ε}` | BHR, CTH [L] |
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
| Redheffer / nerve / core / vertices | `det=M(N)=−χ̃`; `1−Σ index=M(N)`; `O(N^{½+δ})` | HWV, ADT, HHAC, RIAC [L] |
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
| Modulus balance | `\|Q(tw)\|=\|Q(t̄w)\|` at zeros | RAC [L] |

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
| PM | cusp-energy exponent | `Λ_g(ρ/2)=0` for `Re ρ>2−2α` | `½` | BHR [L] |
| AOG | spline-orbit growth `σ` | width `≤σ` | VK | AOG [L] |
| ACS, SOSZ | integer-degree crude Hasse–Weil exponent `σ` | width `≤σ` | VK | SOSZ [L] |
| ACS, SOSZ | prime-gap exponent `θ` of the prime planes | width `≤θ−½` | `θ>7/12` (`1/12`) [S]; `0.525` [C] | SOSZ [S] |
| AAD | stencil rate | `Re ρ≤1−a` | VK; RH gives `[¼,½]` | AAD [L] |
| RAC | Liouville exponent | zero-free `Re s>Θ` | VK | RAC [L] |
| AE | integrality exponent | `Θ` | exact | ASRP [L] |
| IWT | thick prime-deviation exponent `½+a` | no isolated top above `½+a` | none | IWT [L] |
| TAPO | first-return exponent at constant precision | dark-range saving | `(log y)^{3/2−o(1)}` | TAPO [L] |
| HHAC | core Euler characteristic exponent | strip | `θ=1` up to VK | HHAC [L]; [D] |

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
| AAL (B83) | `Θ=Θ∞`; zero transport; tail transport | not-attained top, progressions, Abel-density-zero excursions, polar ground energy, prime-window grid, integer lag, plateaux, JAS, towers, cone, weak recurrence, slow returns on right discs, thick lag, thick prime deviation, positive count of one tower [L] | sub |
| ZAL | well-foundedness of every tower | inner-field decay, subtracted lag, `Λ_Xlog X→0`, eventual Hadamard, LH with every cosine-shift level eventually real, high-collision counts [L] | ≥qRH |
| Thick crude count (B110) | `primeDeviation=O(X^{½+a})` on thick scales ∀`a>0` | ⇒ AAL; with ZAL at `a=0` ⇔ RH [L] | AAL |

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
| Periodicity of the zeros in height ⇒ AAL | ZCG [L] | AAL = zero transport | open (B83) |
| Euler product + FE at finite rank ⇒ local squares | RHTower [L] | Euler product + FE of ζ | the two-scale input (B112) |
| Crude count at every level (Stepanov) | RHTower, CTH, IWT [L] | thick crude count (B110); crude Hasse–Weil at every integer degree (Σ137) | open; phase-freezing producer capped by precision (Π121) |
| Self-improvement by power sums | IWT [L] | window theorem at infinite rank on thick sets; free at the integer degrees | available |
| FE pins modes to the circle | CTH, ASH [L] | FE of ξ = Born rule; Hecke isometry of `Q` | quadratic half holds |
| Count half: the integral defect is a point count | CTH [L] | `Q` as Tate limit of a count (B87); damping of the diagonal (B88) | open; `Q` not integer-valued |
| Archimedean fibre | — | `ℍ³` Green function at `s=½` (cusp + jets), damping positive off the diagonal | available off the diagonal |

## 3. Which routes are the same problem

### 3.1 Same problem by source identity or proved transport
| Family | Routes | Identity | Anchor |
|---|---|---|---|
| Window scalar | RW, EWU, OWU, ACT, CHMD (odd), TT (odd), SZ, RN energy, ACS atomic, LI on primitives, HF, SRT, AIP critical branches | one form on one window; sectors exact; first variation = Weil energy; critical thresholds are the window threshold plus polar payment | SWC, SZ, ALG, ACS, CACT, AHD [L] |
| Two-site / Frobenius graphs | GWZ two-site, AOG spline orbit, SOSZ Frobenius pairs and integer degrees, SRT two-bump | one rank-two test per scale; integer degrees suffice | GWZ, AOG, SOSZ [L] |
| Log-mean | WD near-line, CTF budgets, ZCG depth law, RW onset, AIF `I` at infinity, BHR bulk log-mean | eight-way equivalence; depth density | CDG, AIF, ASH [L] |
| Mertens level | MC, WL, AAD, AE, CTF defect, PBM, RB, Redheffer, RAC parity, Farey, nerve, core, prime-vertex indices | rate ⇔ level; `det=M(N)=−χ̃=1−Σ index`; Farey law ⇔ RH | AAD, RAC, RHTower, ADT, HWV, HHAC, CTH, RIAC [L] |
| Inner mass | CTF BSY, AIF budgets and dilation, MZF `N(ρ)`, KL index | one Blaschke product | AIF [L] |
| Horizon | PM, BHR, ASH, RIT, CTH horocycle, Narain | one scattering matrix; every observable reads `ρ/2` | RIT, BHR, ASH, CTH [L] |
| Abscissa / transport / dial | BAG, WL thick runs, JAS shell, SC undamped, ZCG one-off, linear and tower layers, AKLT towers, AAD transport, TAPO, RW polar ground energy, IWT | ¬AAL as one rigid object; AAL = zero transport = tail transport; linear dial with prime-side TFAEs; producers transfer; countermodels classified | ZCG, AKLT, AAD, TAPO, APD, IWT [L] |
| Count | ACS, HF, PM probes, CWS heights, LST Künneth, CTH Tate limit, SOSZ half-products and plane counts, standard forms | one quadratic form on integer probes; count law = Born rule + positivity; off-diagonal assembled | AE, ASH, CWS, ACS, CTH, SOSZ [L] |
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
| Dark-range inputs | B46, B57, B89, B96, B97, B121 | Dirichlet polynomials longer than the height |
| Two-scale transport inputs | B13, B83, B84, B103, B110, B111, B112, B116 | a Dirichlet-series statement with Euler product and FE seeing low and high zeros together |
| Critical-line sizes | TH head (B102), ZCG FE-pair flatness (B76), Lindelöf-type bounds | values of ζ on `Re s=½` near its zeros |
| Diagonal sign | B87, B88, B95, B114, B118 | a positive object whose limit is Weil's kernel including the diagonal |
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
| C19 Two-site band / Frobenius graphs | `\|𝒞_m(f)\|≤W(f)`; `\|c_B(log n)\|≤c_B(0)` | GWZ, AOG, SWC, SRT, SOSZ | two-parameter family; spline orbit; Frobenius pairs; integer degrees [L] |
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
| C51 Horizon scattering | ringdown, horocycles, Farey counts, Lax–Phillips, Narain, cusp energy | PM, BHR, ASH, CTH | width-axis dictionary [L] |
| C52 Beurling isolation | FE defect, count distance | APD, SEL, BAG, SPAL | three isolation metrics [L] |
| C53 Count and height | naive height, Tate limit, point counts, plane counts | ACS, HF, PM, CWS, AE, ASH, CTH, SOSZ | every hyperelliptic curve; ℤ RH-strength; `Q` not integer-valued [L] |
| C54 Cut kernel | power-law solutions | WL, MC, RAC, AAD, CTF | kernel = zeros [L] |
| C55 Ledgers and parity | degree-`k` ledgers, exact identity | WL, MC, RAC, AAD, AGT | parity is size [L] |
| C56 Prime torus at finite time | boxes, savings, rounded orbit, mixing time | BAG, TH, SRT, ZCG, PTT | absolute savings [L] |
| C57 Kernel-valued certificates | Agler, Euler, head–tail | TH, RW, PTT, PM | tail-good [L] |
| C58 Hull | fibres over the torus | BAG, ZCG, PTT, AIF | natural boundary `½` [L] |
| C59 Krein law | universal decay, flux sign | PM, BHR, ASH, ACS | sign ⇔ RH [L] |
| C60 Fakes of the black hole | `(q,G,D)`, throat, genus two | PM, ASH, CTH; W1C | damping not a wave law [L] |
| C61 Metaplectic descent | cubic Gauss coefficient | MC, MMD | nonzero residue at `4/3`; theta identification open [L] |
| C62 Transport | return count, tail at a zero, partial returns, near-full tail events | BAG, ZCG, AAD, RAC, TAPO, HTG | right discs; zero or small value; `η>0` abundant [L] |
| C63 First return | brackets, precision law, heavy returns | BAG, SRT, TH, PTT, TAPO | constant precision open [L] |
| C64 Conditional tail | head–tail decoupling, collision arithmetic | BAG, TH, WD, TAPO, SPAL | below the Kronecker scale [L] |
| C65 Farey and horocycle | Farey discrepancy, horocycle mean | MC, PM, HWV, CTH | Franel–Landau, Zagier [L] |
| C66 Countermodel boundary | finite top layers | BAG, ZCG, JAS, SC, APD, IWT | firewall; `cosh` and two-scale `cosh` models [L] |
| C67 Born rule | partner law, damping, boundary algebra, standard forms | PM, ACS, CTH, ASH | quadratic half = FE; count half = damping; Tomita collapse; half-sided exclusion [L] |
| C68 Topology of the prime complex | homotopy, persistence, fixed points, singular indices | MC, HF, ACS; ESG, HHAC, HWV, ADT, RIAC | classified, `s`-blind; `Σ index=1−M(N)` [L] |
| C69 Thermal averaging | primon gas | SEL/Primon | Euler factors at real points `>1` [L] |
| C70 Relocation positivity | first-gap negativity | APD; ZCG, BAG | rational surgery detected [L] |
| C71 Two-scale law | asymptotic and local-below properties | every AAL route | decides no level of the dial [L] |
| C72 Exceptional rank | Turán windows, rank barrier | WL, ZCG, ACS, JAS, IWT | thick sets self-improve [L] |
| C73 Tower elimination | well-founded towers, thick crude count, Toeplitz count | WL, ZCG, ACS, IWT | thick crude count ⇒ AAL; + ZAL ⇒ RH [L] |
| C74 Frobenius substitute | returns freeze smooth polynomials | BAG, PTT, IWT | approximate only; capped by precision [L] |
| C75 Half-products | 𝔽₁-zonotope, `ℙ¹_ℤ` torsion, `ℍ³` fibre, Frobenius graphs | ACS, HF, PM; SOSZ, AE | off-diagonal assembled as dampings; diagonal missing [L] |
| C76 Critical weight | damping versus renormalization | ACS, HF, PM; IWT, HHAC, RIAC | renormalization signless [L] |
| C77 Euler + FE calibration | finite-rank local squares; Beurling FE rigidity | ZCG, BAG, APD, SEL | succeeds at finite rank and identifies ζ in the Beurling class [L] |
| C78 Finite-field counts | resultant, radial, orbit and orientation counts | ACS, MC, RIAC, SOSZ | counts before the form; Möbius as point defect [L] |

C1, C4, C16, C19, C25, C26, C48 and C49 are exact window-form dictionaries. C5, C28, C33 require all-root or all-degree control. C11, C32, C40, C42, C48 are asymptotic and weaker than RH; by C71 they cannot reach any level of the dial. C13 closes source supply, not effectivity. C8–C10 and C21 retain source-specific bounds. C23, C24, C31, C52 supply calibration or amplification. C45, C34, C65 and C68 are one axis (the Mertens level). C56, C57, C62, C63, C64, C74 are one programme on the dark range. C43, C52, C66, C70, C71, C72, C73, C77 are one programme on the exceptional coordinate. C51, C53, C59, C60, C67, C75, C76, C78 are one programme on the count.

### 3.4 Constructive transfers and their limits

| Sources / routes | Established transfer | Input not transported |
|---|---|---|
| RW/HF/SRT/AIP/ACS | exact receivers for form, band and source energy [L] | all-aperture sign |
| CACT/AHD→RW | `R_c=R_polar≤R_prim=R_high=W`; charged compactness [L] | the window sign itself; polar payment at every ratio |
| AHD below the onset | aperture ⇄ ratio exchange [L] | any increase of `a*(ζ)` |
| RW→flow | canonical system, restoring bound [L] | bound on `osc Ψ` |
| RW→count | cone points obey PNT `5/6` on the window's range [L] | windows of every length |
| AOG/SOSZ→GWZ | spline orbit and smoothed Frobenius pairs are two-site tests; integer degrees suffice [L] | the pair inequality at every degree |
| SOSZ→width | crude integer-degree bound `Kn^σ` ⇔ width `≤σ`; prime planes width `≤θ−½` [L/S] | a crude bound at every degree |
| ACS→RW/SRT | typical-height sign with Gaussian tails [L] | fixed `λ`; exceptional heights |
| APR→PTT/TAPO | necessary mollifier length ↔ primes `≤c log²T` [L] | a near-unit mollifier |
| TH↔ζ on the line | adaptive head leading term `=\|ζ(½+ib)\|²` [L] | sign near critical zeros |
| PM↔TH, PM↔BHR↔CTH | Eisenstein coefficients; horocycle mean = Farey count [L] | any exponent past `½` |
| BHR cusp energy→PM | rate `y^α` forces `Λ_g(ρ/2)=0`; eigenform RS Euler product [L] | noncancellation (B109) |
| ASH Narain→PM | `¾` ⇒ RH; remainder VK [L] | any rate past VK |
| CTH standard forms→PM | RH ⇔ internal standard form realizing `Q` [L] | a realization outside the excluded classes (B114) |
| IWT→WL/ZCG/ACS | thick crude count ⇒ AAL; RH ⇔ ZAL ∧ thick `√X`; linear six-way TFAE [L] | the thick crude count (B110), ZAL |
| ZCG dial→all AAL routes | quantifier collapse, strict hierarchy, finite-rank exponent [L] | any level of the dial for ζ |
| ZCG heat→B13 inputs | family-uniform finite-stratum laws are RH [L] | an Euler-product input |
| ZCG two-scale law→all AAL routes | scale-separated inputs cannot decide B13 [L] | a two-scale input |
| BAG/AAD/TAPO | transport on right discs; tail transport; partial returns; near-full events [L] | existence of an exact event at a zero |
| IWT forced vanishing→BAG/ACS | Rouché copies cost the trivial separation bound [L] | a freezing control beyond the cap |
| AAL producers | sparse bounds ⇒ AAL [L] | each source bound |
| AAD↔MC | rate ⇔ Mertens level [L] | a level past VK |
| RAC↔CTF | finite-energy cut-kernel mass annihilation ⇒ RH [L] | the annihilation |
| SOSZ/AE/RIAC→CTH | off-diagonal = pole − `ℍ³` Green − torsion, all channels positive dampings [L] | the diagonal; a damping presentation (B88) |
| IWT critical weight→HHAC/RIAC | renormalized torsion is a renormalization, not a damping [L] | a positive damping family |
| CTH curve→ℤ | count law from point counts on curves; Tate principle [L] | a point count over ℤ |
| RIAC finite fields→ℤ | orientation cover and orbit counts over `𝔽_q` [L] | an orientation cover over ℤ (B120) |
| ESG/HHAC/RIAC→MC | `M(N)` as barcode count, core Euler characteristic and `1−Σ` prime-vertex indices [L] | any cancellation |
| APD firewall→ZCG/BAG | positive classes, continuation and reflection carry finite layers [L] | intrinsic layers of ζ |
| RHTower finite Euler FE→ZCG | Euler product + FE force purity at finite rank [L] | the infinite-rank form (B112) |

## 4. U-Σ — the sign

Core problem: `1∈ℋ(c)` for every `c`. In cone form, some weight on every window; in causal form, an outer predictor; in flow form, `Ψ` locally bounded; in plane form, `Ω≥0`; in pair form, Hasse–Weil along the spline orbit or for every pair of smoothed Frobenius graphs, equivalently at every integer degree; in matrix form, every critical threshold `=⊤`, which is the window threshold plus polar payment; in Laguerre form, horizontal-line positivity of Ξ; in theta form, the sign of `|ζ(½+ib)|²` plus second-order terms near the zeros. One scalar: `a*(ζ)`.

| Face | Routes / programmes | Reduction |
|---|---|---|
| Complete atomic matrix | HF, SRT, AIP, ACT, CACT, CSAR, ACPL, RAPT, TM, ADT, AHD | `R_c=R_polar≤W`; compactness closed; polar payment below `W` open |
| Ground energy, chain, cone | RW, EWU, OWU, CSTW, CHT | `a*(ζ)`; `Ψ`; `λ*` |
| Causal chain | RW, GWZ, AIF | outer predictors; Schur bands |
| Pair tests and Frobenius graphs | GWZ, AOG, SOSZ, SRT | two-site PD; spline orbit; integer degrees; crude bound = width |
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
| Torsion, `ℍ³` fibre and compensation | HHAC, AE, SOSZ, RIAC | pole − `ℍ³` Green − torsion; diagonal |

## 5. U-Π — precision and production

Core problem: square-root precision of one smoothed prime count; in tower form, a square-root prime deviation on a thick set of geometric scales together with ZAL; in graph form, a bounded orbit correlation at every integer degree. Production, Farey discrepancy, the Farey count, the Euler characteristics of the nerve and core, the barcode and the prime-vertex indices read the same statement through integers, fractions, simplices, persistence and fixed points; none has a mechanism independent of the Mertens level. The dark range is where every sub-RH precision question sits; the archimedean Frobenius substitute that would produce a crude count there is capped by precision.

| Face | Routes / programmes | Reduction |
|---|---|---|
| Reflection-pair coupling | SWC, GWZ, CSTW, AOG | collar Hankel − smoothed count |
| Classical one-sided counts | WL, PBM, RB, JAS, CTF, HCF | RH-level equivalence; Gaussian ceiling |
| Thick tower counts and the dial | WL, ZCG, ACS, IWT | thick crude count ⇒ AAL; + ZAL ⇔ RH; relative counts = linear laws |
| Integer-degree crude bounds | ACS, SOSZ | crude bound = width; sparse degrees; prime gaps |
| Collective kicks | SWC, FADF | beyond size, by sign |
| Cyclotomic mode, gauge torus | MC, CAF, AGT | exponent `½` at the trivial point |
| Integer producers | WL, AKLT, ASRP, AE, AAD, RAC | rate = Mertens level; Stepanov over ℤ = Chebyshev |
| Frobenius substitute | IWT, PTT, TAPO | returns freeze smooth polynomials; precision cap |
| Parity | WL, MC, RAC, APR | exact identity pins `λ` |
| Möbius, nerve, core, Farey, descent | MC, HWV, ADT, HHAC, ESG, RIAC, CTH, MMD | half-power cancellation |
| Short-sum barrier | every route, PTT | absolute savings |
| First return | BAG, PTT, TAPO | constant precision open |
| Conditional tail and collisions | TAPO, SPAL, IWT | Gaussian below Kronecker; collision counts of order `X²` past the height |
| Near-line density | WD, CDG, MZF, AIF | log-mean; depth `O(T)` |
| Long moments | APR, CDG, WD, MZF; CTF | necessary length = primes `≤c log²T` |
| Budgets | CTF, AIF | second expression; Szegő ratio |
| Negative moments | MZF, MC, ADO | Green potential moments |
| Deciding-input filters | ASRP, APR | parity, purity, precision, aperture |
| Census | SRT, CDG | signed pair data past bandwidth one |
| Sharp horizon sources | CTH | Möbius × circle remainder, beyond RH |

## 6. U-Γ — selection, reflection and transport

Core problem: source-defined arithmetic control of `ρ↦1−ρ̄` and of vertical transport; in count form, the count half of a Born rule whose quadratic half holds; in configuration form, one level of the linear dial — a two-scale Dirichlet-series input that uses the Euler product and the FE together and converts the FE into transport.

| Face | Routes / programmes | Status |
|---|---|---|
| Recurrence, gauge | MC, AGT, BAG, AAD, RAC, PTT, TAPO | transport closed on right discs; tail transport; exact events open |
| Abscissa split and dial | BAG, JAS, SC, WL, AKLT, ZCG, RW, IWT | split for every configuration; strict dial; rigid ¬AAL; two-scale law; family law |
| One-off and FE models | APD, SPAL, RAC, AIF, ACP, IWT | firewall; `cosh` and two-scale `cosh` models; ζ isolated in three metrics |
| Euler + FE calibration | RHTower, APD, SEL | finite-rank purity; Beurling FE rigidity |
| Time-zero selection | ZCG, NGF | parabolic tools blind; family-uniform laws are RH |
| Weil cone, lattices | RHTower, GWZ, FADF, CHT | at most `{Λ}`; nonempty iff RH |
| Selberg class | SEL | degree one classified |
| Camera identification | ZCG, SRT, MZF | conditional readout |
| Reality at near-coincidences | ZCG, ADO | FE pair forces small values |
| Diophantine repulsion | ADO, ZCG | `0∉E` open |
| Euler columns, carriers | ZCG, FFP, AIF, TAPO | Euler coordinates stop at `Re s=1` |
| Horizon and count | PM, BHR, ASH, CTH; W1C, ACP | Krein law; Born rule; Tate limit; internal, vacuum-fixing and half-sided realizations; width axis |
| Rosati, Frobenius at infinity | CWS, WTZ, GWZ, AOG | sharpened |
| Source completions | CDC, SEC, PCS; RFHM, EWJ, APF, WBF | source versus forcing |
| Hull | PTT | Liouville point extreme |
| Surface of Spec ℤ | SOSZ, AE, RIAC | off-diagonal assembled with `ℍ³` fibre; diagonal missing |
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

## 8. Route → core map

| Route | Core | Halves | Classes | Face |
|---|---|---|---|---|
| WL | Π | both | C7, C19, C32, C43, C45, C54, C55, C72, C73 | bounded endpoint energy; integer lag; thick tower count; linear dial |
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
| MC | Π (Γ) | both | C7, C8, C12, C32, C45, C54, C55, C61, C65, C68, C78 | trivial gauge; Farey; topology; Möbius as point defect |
| TT | Π (Σ) | both | C4 | endpoint upper bound |
| TG | Π, Σ | both | C3, C12 | subunit trace norm |
| HF | Σ (Π, Γ) | both | C1, C12–C15, C18, C25, C47, C49, C53, C75, C76 | polar payment; head windows; count |
| SRT, AIP, ACT | Σ (Π) | both | C1, C4, C11, C19, C21, C25, C48, C49 | complete matrix = window + polar payment |
| SC | Σ, Π (Γ) | AAL branch; both | C2, C3, C7, C39, C43 | glued state; undamped cone ⇒ AAL |
| CHMD | Σ | both | C4, C1, C39 | odd sector |
| RN | Σ | both | C9, C1 | joint nodes |
| WD | Π (Σ) | ZAL side | C3, C11, C32, C40, C42 | long moments; log-mean |
| PM | Γ (Σ) | both | C9, C14, C38, C51, C53, C59, C60, C65, C67 | Krein; horizon receivers; count; standard forms |
| JAS | Π | AAL branch; both | C7, C19, C43, C72 | moving power; shell positivity |
| CTF | Π | both | C7, C19, C32, C37, C42, C50, C54 | BSY, budgets, cut kernel |
| PBM, RB | Π | both | C7, C19 | abscissa, extremal |
| BAG | Γ | AAL | C8, C43, C47, C52, C56, C58, C62–C64, C66, C70, C71, C74 | target mass; tail transport |
| ACS | Π (Σ, Γ) | both | C13, C1, C12, C18, C19, C20, C30, C46, C48, C53, C67, C73, C75, C78 | source sign; count law; integer-degree Hasse–Weil |
| SEC, CDC, PCS | Γ | both | C10 | zero-parameter conditions |
| PTR | Σ (Γ) | both | C9, C5, C24, C39 | Laguerre below VK |
| ZCG | Γ (Σ) | ZAL side, AAL layers | C5, C21, C23, C24, C31, C40, C41, C43, C62, C66, C70–C72, C77 | collisions; abscissa laws; dial; heat family |
| Candidates APF, EWJ, RFHM, WBF | Γ (Π) | — | C10 | missing landing |
| Candidate IRK | Γ (Π) | — | C13 | trace with Chern charge |
| Candidates EGC, FEL, MSC | Σ (Π) | — | C6, C1 | landing; history; Sonin sign |
| Candidate W1C | Σ (Γ) | — | C9, C5, C38 | positive realization |
| IWT (support) | Π, Γ | both | C43, C71–C74, C76 | exceptional coordinate; elimination; dial |
| SOSZ (support) | Γ, Σ | — | C19, C53, C75, C76 | half-products; `ℍ³` fibre; Frobenius graphs |
| RIAC (support) | Π, Σ | — | C68, C76, C78 | prime boundary; compensation; vertex indices; finite-field counts |
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
| A crude count | thick crude count ⇒ AAL; RH ⇔ ZAL ∧ thick `√X`; crude integer-degree bound = width; Stepanov over ℤ to Chebyshev [L] | the thick crude count for ζ; a well-founded tower (ZAL); a crude bound at every integer degree |
| A Frobenius substitute | returns freeze smooth polynomials; approximate forced vanishing [L] | exact returns do not exist; Rouché copies capped by precision; a counting argument beyond the cap |
| Budget, not exact sign | subexponential floor ⇒ RH [L] | any such floor |
| Sign of the minimal object | band ⇔ `1∈ℋ(c)` ⇔ `λ*→0` ⇔ pair Hasse–Weil [L] | the band at every step |
| Uniformity in length | each length a rung; critical thresholds = window + polar payment [L] | every length; polar payment below `W` |
| Flow | restoring bound, `Ψ`-boundedness ⇔ RH [L] | a bound on `osc Ψ` up to contact |
| Heights | size curve [D]; typical-height sign [L] | sign past `log log X` at rare heights |
| Across primes | columns add; Euler coordinates stop at `Re s=1` [L] | amplitude oscillation |
| The critical line | theta head `=\|ζ(½+ib)\|²`; FE-pair flatness [L] | second-order sign at the critical zeros |
| Time selection | parabolic laws; family-uniform laws are RH [L] | an arithmetic input separating `Φ` from heated kernels |
| Precision, occupancy | rate 2 isolated; depth `O(T)` [L] | a non-outer control of the inner mass; cluster bound |
| Dark range | brackets; conditional tail below Kronecker; collision counts of order `X²` [L] | the tail law at the Kronecker scale; lower bounds for exact tail events; proportional saving |
| Count from geometry | off-diagonal as pole − `ℍ³` Green − torsion, each a positive damping; Tate principle; point counts on curves; finite-field counts [L] | the diagonal: a counterterm-free damping (B88), a count without `Q` (B87) |
| Archimedean carrier | `ℍ³` Green function at `s=½` [L] | the self-energy of a point, i.e. the diagonal |
| Reflection | coefficient completion; horizon receivers; Born rule; standard-form trichotomy [L] | `D_s≥0`; a realization outside the excluded classes; any horizon exponent past `½` |
| Sparse exceptions | rigid ¬AAL; tower excursions; transport; partial returns [L] | an exact rare event at a zero or a contradiction in ¬AAL |
| The finite stratum | TFAE of finite index, lattice index, finite off-line set, heat count, eventual RH; towers decide; Lindelöf [L/K] | a two-scale Euler-product input excluding a finite off-line set (B13) |
| Production | exact integrality; VK rate; kernel; parity identity [L] | a level past VK |
| Topology | classified persistence; localization `Σ index=1−M(N)` [L] | signed cancellation of the local indices at `√N`; an orientation cover over ℤ |
