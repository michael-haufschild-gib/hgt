# Route unification ledger — status quo

The 38 live formulations and 9 candidates are faces of three core problems: **U-Σ** (sign), **U-Π** (precision and production) and **U-Γ** (selection, reflection and transport). Their RH-level endpoints meet at the **arithmetic Hardy inequality** `P≤H` on every window, equivalently the **band** `|𝒞_m(f)|≤W(f)` of a test and its mirror, equivalently nonnegativity of one quadratic form `Q` on integer probes, equivalently **`Q` is the Tate limit of a count**, equivalently **Hasse–Weil for every pair of smoothed Frobenius graphs of Spec ℤ**. U-Σ reads it as a form on the window, U-Π on the prime side, U-Γ on the zero side.

Transversal to the three, RH splits into **ZAL** (finitely many zeros beyond each depth) and **AAL** (zero transport in height); the split holds for every zero configuration. Below the three lie three structural gaps that every family meets: the **dark range**, primes past the Kronecker scale where conditioning on the head needs a Dirichlet polynomial longer than the height; the **missing count**, a nonnegative arithmetic function with quadratic Tate limit `Q` — equivalently a counterterm-free damping presentation of the diagonal of Weil's form; and the **two-scale transport input**, a Dirichlet-series statement that couples low and high zeros and turns the functional equation into vertical transport, which every countermodel lacks.

**Why there are three cores [D].** No test is compact on both sides of the explicit formula. A compact prime side (U-Σ) leaves infinitely many zero modes and only an exact sign decides; a localized zero side (U-Π) lets a crude bound decide (one Gaussian prime ceiling per rational height ⇔ RH; ZAL plus a square-root prime deviation on a thick set of scales ⇔ RH [L]) but leaves the prime side at square-root precision; U-Γ is the involution `ρ↦1−ρ̄`, the selection of ζ and the transport of its zeros. The curve proof uses two freebies that ζ lacks: finite rank, which makes elimination algebraic and ZAL in tower form automatic, and zeros periodic in height, which make AAL automatic [L]. In the `s`-coordinate both of its steps (Stepanov's crude count, power-sum elimination) sit inside ZAL; over ℤ the elimination step exists at infinite rank on thick sets and turns a thick crude count into AAL, and into RH together with ZAL [L].

Corpus checkpoint: commit `906b3c709c` plus the working tree of 2026-11-08. Evidence: `[L]` Lean source; `[K]` with transitive axiom audit; `[S]` unfinished, unintegrated or uncommitted; `[D]` deduction; `[N]` numerical; `[C]` classical. Locators: [frontier map](../rh-current-frontier-map.md), [scoped obstructions](../rh-killed-routes.md), [walls](walls-ledger.md), [routes](route-obstacles.md), [summary](obstacles-summary.md).

**Equivalence through RH transfers truth, not mechanism.** Only an explicit source identity or a proved transport moves an estimate between routes. Section 3 separates the two.

## 0. Unifying statements

- **One split [L].** For every zero configuration, purity ⇔ ZAL ∧ AAL. For ζ: RH ⇔ ZAL ∧ AAL ⇔ ZAL ∧ zero-disc weak recurrence ⇔ ZAL ∧ subexponential polar ground energy ⇔ ZAL ∧ thick `O(√X)` prime deviation. ZAL ⇒ qRH. `qRH ∨ AAL` [D].
- **One transport [L].** AAL ⇔ every right zero has zeros with real part `>Re ρ−ε` at arbitrarily large height ⇔ every right zero transports to arbitrarily high points where every Euler tail vanishes and the tail cancels the head with full amplitude. AAL is the zero-level trace of recurrence; transported events are tail-bad and rare.
- **One two-scale law [L].** No property of the zeros above a height and no property of the zeros below a fixed height decides the finite stratum: adding one reflection pair at a single height keeps both kinds of property and breaks AAL at `h=0`. An input for B13 or AAL couples both scales — a Dirichlet-series statement.
- **One analytic freedom [L].** FE, order one and reality admit every finite top layer (`cosh(s−½)·Π quartets`). On tower level sums the FE acts only as `S(−ν)=conj S(ν)`; the reflection `ρ↦1−ρ̄` keeps heights.
- **One firewall [L].** Continuous Beurling systems (continuing across `Re s=½`), integer-norm and rational-prime Euler products with linear counting, and one reflection pair each carry a finite top layer; positive two-prime and Hecke polynomials annihilate every finite zero set at every multiplicity. AAL is invariant under symmetric shifts. The one ingredient no countermodel combines is an Euler product together with the FE.
- **One free class [L].** Recurrent configurations, exponential polynomials, curves, vertically periodic configurations, strip almost periodic functions and uniformly approximable Dirichlet series obey AAL. Almost periodicity at large height alone does not.
- **One rigid alternative [L].** ¬AAL ⇔ an isolated top over an infinite remainder ⇔ finite top and bottom layers at the same heights ⇔ `ψ(x)−x` a finite oscillation at leading order ⇔ two-prime dilation annihilation ⇔ syndetic lag excursions at every base, with exceptional rank 1 at the resonant base of a single top pair.
- **One elimination [L].** The exceptional rank decides Turán windows; no thick set of levels carries a bound below an isolated top; hiding a top costs trace norm growing with the window position; density `1−1/k` sets do not self-improve; well-founded towers bounded on a thick set have only the critical layer visible.
- **One finite stratum [L/K].** Finite negative index of `K_ζ` ⇔ finite index on one two-prime lattice ⇔ finitely many off-line zeros ⇔ bounded heat count ⇔ RH above some height ⇔ eventual slice positivity; in the stratum Lindelöf holds and one non-blind prime tower decides RH.
- **One scalar [L].** Every window route measures `a*(ζ)`. Contact is `Ψ=½log H₁` blowing up; RH ⇔ `Ψ` locally bounded.
- **The critical curve is the window plus one channel [L/S].** `R_c≤R_pole=R_high=W`; below `W` the complete matrix is decided by its pole channel; the pole at every ratio is RH.
- **One exchange [L].** Below the onset, aperture `a` buys a depth-`¼` zero-free region to height `e^{a/K}`, which buys a sharp pole and `R_polar≥c₁e^{c₂a}`; no step raises `a*(ζ)`.
- **One splitting order [L].** Conductor first, position second.
- **One sign plane [L/D].** Size reaches all heights to `a≈log log X`; typical heights to `a=δlog T/(64M²)`.
- **One frequency diagonal [L].** Weil's form is the average of its frequency packets.
- **One scale [L/D].** A near-unit mollifier needs length `exp(c log²T)`; an Euler mollifier reaching it uses every prime up to `≍log²T`; absolute non-alignment begins at length `≈L²`; conditional tail laws hold only below the Kronecker scale; past the height long mean values are collision counts.
- **One tail [L].** Zeros of ζ are zeros of the Euler tail at every cut; returns at right zeros are tail-bad; every certificate past `Re s=1` is a tail-good condition; partial returns transport a zero or create a deep small value.
- **One first return [L].** `R(y,η)` bracketed at every precision; weak return = extreme value of `ζ(1+it)`; proportional saving = no early heavy return.
- **One Frobenius substitute [L].** Returns freeze smooth Dirichlet polynomials; `J` moment conditions force approximate vanishing at every return; the prime orbit has one fixed point.
- **One collision arithmetic [L].** Smooth × prime mean squares are diagonal plus collision counts fixed by gcd classes.
- **One width axis [L/D].** Floor rate, damping rate, abscissa, gauge exponent, stability line, long-moment slope, Möbius zero abscissa, integrality exponent, stencil rate, PTR `h`, TH `a`, Hecke level, ringdown gap, horocycle, Farey, Narain and cusp-energy exponents, spline-orbit growth rate: interior values are zero-free strips; all unconditional savings sit at VK.
- **One Mertens level [L].** Stencil rate = Mertens level; Farey discrepancy, the nerve and core Euler characteristics and the Farey count at order `C` are `M(N)`; localized at prime vertices they are Möbius sums over integers of least prime factor `p`.
- **One topology [L].** The prime-product complex is a sphere bouquet with classified persistence, independent of `s`; prime-vertex self-maps homotopic to the identity fix exactly the primes, with indices unbounded below.
- **One horizon [L].** Pulse ringdown, horocycle mean, Farey count, Lax–Phillips mode, Narain remainder and cusp energy read the poles `ρ/2`; gain `δ` past the trivial rate ⇔ strip `2δ`; RH ⇔ `y^{¾}` ⇔ `e^{−t/4}`; unconditional smooth thermalization `y^{½}exp(−√(−log y))`.
- **One Born rule [L].** A count law = nondegenerate Born rule (the FE) + positivity (universal damping). The partner involution has a positive state iff damped; internal modular conjugation collapses to the Hilbert adjoint; RH ⇔ a standard form whose modular conjugation is the partner involution on rational dilations with natural-cone form `Q`.
- **One count [L].** Tate principle both ways; curves: the integral defect is a point count; fakes: count, not quadratic; ℤ: quadratic, count missing.
- **One surface [L/S].** The off-diagonal of Weil's form is one 𝔽₁-cusp with its even jets plus gcd-twisted torsion on `ℙ¹_ℤ`, equivalently `C_∞` plus the Abel limit of positive torsion energy; atomic Frobenius graphs have infinite genus; smoothed pairs pass Hasse–Weil ⇔ RH; the sign sits in the diagonal.
- **One critical weight [L].** Damping is lossless; renormalization carries no sign. A count at the critical weight is a damping of something positive.
- **One crude regime absent [L/D].** In the size coordinate constant-factor bounds are false and `x^{½+ε}` is RH; crude regimes live in the exceptional coordinate and on thick sets of scales.
- **One blindness [L].** Floor identities annihilate every zero mode; exact ledgers are holomorphic off `s=1`.
- **One kernel [L].** Zeros are the power-law kernel vectors of the cut system; finite-energy kernel mass annihilation ⇒ RH.
- **One parity [L].** The exact identity `Σ_{k≤x}F(⌊x/k⌋)=⌊√x⌋` pins `λ`; a power-saving Liouville bound is a zero-free strip.
- **One edge [L/D].** Pronic domination, flux, Hermite–Biehler at `σ=1`, Euler coordinates, the Poisson measure of the Hecke algebra, primon thermal averages, the Hecke state on `Aff(ℚ)` (PD iff `s≥½`): every positivity with a proved mechanism stops at `Re s=1` or exactly at `Re s=½` as a threshold, not as a selector.
- **One inner factor [L].** On `Re s>½`, `E` has inner factor the Blaschke product of right zeros; RH ⇔ `I(w)=0` at one point.
- **One log-mean [L].** Eight forms of `T⁻¹∫log|ζ|→0`, depth density `o(T)`, density-zero damping deficits; an asymptotic property.
- **One certificate [L].** Causal: outer predictor, Schur band, sum of squares with margins as weights.
- **One column law [L].** On independent reflectors infima add; only amplitudes oscillating with the height cross columns.
- **One theta head [L].** The adaptive head is `|ζ(½+ib)|²` plus `O(|ζ(½+ib)||b|^{−½}+|b|^{−1})` and terms whose sign is decided near the critical zeros.
- **One Eisenstein carrier [L].** TH spectrum, PM carrier, BHR packets, horocycle means, Farey counts and the Narain scalar projection use `E*(z,½+ib)`; Hecke at `p` is time translation by `log p`.
- **One isolation [L].** ζ is a singleton in FE defect `≤1/6400`, in count distance `o(log n)` and under the exact parity identity.
- **One finite-rung rule [L].** Each fixed window, rank, degree, row, ratio and entry follows from verified zeros; no finite verification decides B13 or AAL.
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
| Frobenius pairs | Hasse–Weil for every pair of smoothed Frobenius graphs | SOSZ [S] |
| Hamiltonian | `Ψ` locally bounded | CSTW, AIF [L] |
| Lattice | Schur parameters in `(−1,1)` | GWZ [L] |
| Causal | outer predictor at every window | AIF [L] |
| Bohr | orbit correlations relatively compact | AIF [L] |
| Critical thresholds | `R_c`, `R_pole`, `R_polar`, `R_high` all `=⊤` | AHD [L/S] |
| Low packet | polar payment at every ratio | CACT [L] |
| Moments | Hamburger, shifted Hamburger, Stieltjes | SWC [L] |
| Li / Cayley | ladder NSD on primitives | ALG [L] |
| Suzuki | first variation = Weil energy | RHTower [L] |
| Single prime | one Euler factor; transport ⇔ RH | RHTower, AHD [L] |
| Heads | `windowThreshold(log d)` ∀d | AHD [L] |
| Heat | no positive-time collisions | RHTower, ZCG [L] |
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
| Tower count | ZAL ∧ thick `O(√X)` prime deviation | IWT [L] |
| Integrality | Siegel or Liouville half at `√` scale | ASRP [L] |
| Stencil rate | rates `K^{−a}` ∀`a<½` | AAD [L] |
| Cut kernel | finite-energy kernel mass zero | RAC [L] |
| Möbius | subpower Hilbert form; one point; zero-free `M_X` | RHTower, MZF [L] |
| Redheffer / nerve / core | `det=M(N)=−χ̃`; `χ̃=O(N^{½+δ})` | HWV, ADT, HHAC [L] |
| Recurrence | strong self-return; uniform target mass | RHTower [L] |
| Split | ZAL ∧ AAL | RHTower, ZCG, IWT [L] |
| Polar ground energy | ZAL ∧ subexponential `μ₀` | RHTower [L] |
| Source criteria | Fock bound, repair equality, co-shift class | RHTower [L] |
| Bézout | source-energy sign | ACS [L] |
| Characters | central class functions with Gram positivity | Representation [L] |
| Integer probes | `Q(a)≥0` on `ℤ^N`; naive heights | ASH, AE, CWS [L] |
| Tate limit | `Q` is the Tate limit of an `ℕ`-count | CTH [L] |
| Standard form | modular conjugation = partner involution with natural-cone form `Q` | CTH [L] |
| Hull | Liouville fibre extends | PTT [L] |
| Parity | `L(x)≪x^{½+ε}` | RAC [L] |
| Log-torsion | `ψ(N)=N+O(√N log²N)` | AE [L] |
| Modulus balance | `\|Q(tw)\|=\|Q(t̄w)\|` at zeros | RAC [L] |

## 2. Axes

### 2.1 Window axis
| Coordinate | Half-width `c` | Anchor |
|---|---|---|
| Markov death | `e^{−3/4}` | SWC [L] |
| Perron threshold | `log ρ≈0.2812` | SWC, FADF [L] |
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
| B13, AAL | none | no finite verification decides | ZCG [L] |

### 2.5 Exceptional coordinate
| Half | Statement | Receivers / producers | Strength |
|---|---|---|---|
| Finite stratum (AAL at `h=0`) | finitely many off-line zeros ⇒ none (B13) | finite index, lattice index, heat count, `N_d`, eventual RH, eventual slice positivity, one non-blind tower [L/K] | sub |
| Linear AAL (B111) | `Θ−½≤C(Θ∞−½)`: finitely many beyond `½+h` ⇒ none beyond `½+Ch` | interpolates B13 (`C→∞`) and AAL (`C=1`) [D] | sub |
| ZAL | finitely many zeros beyond each positive depth = well-foundedness of every tower | inner-field decay, subtracted lag, `Λ_Xlog X→0`, eventual Hadamard, LH with every cosine-shift level eventually real, high-collision counts [L] | ≥qRH |
| AAL | zero transport; tail transport; eventual-to-global | not-attained top, lags on progressions, Abel-density-zero excursions, polar ground energy, prime-window grid, integer lag, plateaux, JAS, towers, cone, weak recurrence, slow returns on right discs, thick lag and thick prime deviation [L] | sub |
| Thick crude count (B110) | `primeDeviation=O(X^{½+a})` on thick scales ∀`a>0` | ⇒ AAL; with ZAL at `a=0` ⇔ RH [L] | AAL |

### 2.6 Scale axis of the prime orbit
| Range of primes at height `t` | What holds | Anchor |
|---|---|---|
| `p≲c log t` | prescribable: every box entered; no cancellation at some height | PTT, RAC [L] |
| Kronecker scale `≈log t` | conditional tail laws stop; first return of the head ≍ height | TAPO [L]; [D] |
| `≈(log t)²` | absolute non-alignment begins; Euler mollifier length for near-unit moments | PTT, APR [L] |
| `(log t)^A` | saving `t^{−δ}`; RH bracket at polynomial precision | PTT, TAPO [L] |
| `exp((log t)^{2/3})` | VK saving | TAPO [L] |
| between | absolute savings only; collision arithmetic gives upper bounds; returns freeze smooth polynomials approximately | PTT, TAPO, SPAL, IWT [L] |

### 2.7 The curve proof and its ℤ-counterparts
| Ingredient on a curve over `𝔽_q` | Lean anchor | ℤ-counterpart | Status over ℤ |
|---|---|---|---|
| Finite rank: elimination is algebra, outer part well-founded | CTH, IWT [L] | ZAL = well-foundedness of the towers of ζ | ≥qRH, open |
| Periodicity of the zeros in height (Frobenius) ⇒ AAL | ZCG AbscissaLaws [L] | AAL = zero transport; ζ not uniformly almost periodic in the strip | open (B83) |
| Crude count at every level (Stepanov's auxiliary polynomial, `x↦x^q`) | RHTower hyperelliptic, CTH [L] | thick crude count of the prime deviation (B110); producer: returns freeze smooth polynomials, approximately | open |
| Elimination of an isolated top by power sums | IWT window theorem [L] | the same theorem at infinite rank on thick sets [L] | available |
| Functional equation pins modes to the circle | CTH, ASH [L] | FE of ξ = Born rule; Hecke isometry of `Q` [L] | quadratic half holds |
| Count half: the integral defect is a point count | CTH [L] | `Q` as Tate limit of a count (B87); damping of the diagonal (B88) | open |

## 3. Which routes are the same problem

### 3.1 Same problem by source identity or proved transport
| Family | Routes | Identity | Anchor |
|---|---|---|---|
| Window scalar | RW, EWU, OWU, ACT, CHMD (odd), TT (odd), SZ, RN energy, ACS atomic, LI on primitives, HF, SRT, AIP critical branches | one form on one window; sectors exact; first variation = Weil energy; critical thresholds end at the window threshold; below it the pole channel decides | SWC, SZ, ALG, ACS, CACT, AHD [L] |
| Two-site / pair Hasse–Weil | GWZ two-site, AOG spline orbit, SOSZ smoothed Frobenius pairs, SRT two-bump | one rank-two test per scale | GWZ, AOG, SOSZ [L/S] |
| Log-mean | WD near-line, CTF budgets, ZCG depth law, RW onset, AIF `I` at infinity, BHR bulk log-mean | eight-way equivalence; depth density | CDG, AIF, ASH [L] |
| Mertens level | MC, WL, AAD, AE, CTF defect, PBM, RB, Redheffer, RAC parity, Farey, nerve, core, prime-vertex indices | rate ⇔ level; `det=M(N)=−χ̃`; Farey law ⇔ RH; Lefschetz localization | AAD, RAC, RHTower, ADT, HWV, HHAC, CTH, RIAC [L] |
| Inner mass | CTF BSY, AIF budgets and dilation, MZF `N(ρ)`, KL index | one Blaschke product | AIF [L] |
| Horizon | PM, BHR, ASH, RIT, CTH horocycle, Narain | one scattering matrix; every observable reads `ρ/2` | RIT, BHR, ASH, CTH [L] |
| Abscissa / transport | BAG, WL thick runs, JAS shell, SC undamped, ZCG one-off and tower layers, AKLT towers, AAD transport, TAPO, RW polar ground energy, IWT | ¬AAL as one rigid object; AAL = zero transport = tail transport; producers transfer; countermodels and FE models classified | ZCG, AKLT, AAD, TAPO, APD, IWT [L] |
| Count | ACS, HF, PM probes, CWS heights, LST Künneth, CTH Tate limit, SOSZ half-products, standard forms | one quadratic form on integer probes; count law = Born rule + positivity; off-diagonal assembled | AE, ASH, CWS, ACS, CTH, SOSZ [L] |
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
| Dark-range inputs | B46, B57, B89, B96, B97 | Dirichlet polynomials longer than the height |
| Two-scale transport inputs | B83, B84, B103, B110, B111, B112 | a Dirichlet-series statement seeing low and high zeros together |
| Critical-line sizes | TH head (B102), ZCG FE-pair flatness (B76), Lindelöf-type bounds | values of ζ on `Re s=½` near its zeros |
| Diagonal sign | B87, B88, B95, B114 | a positive object whose limit is Weil's kernel including the diagonal |

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
| C9 Realization | Krein defect, renewal nodes, Lee–Yang, cosine, standard forms | RN, PM, PTR; W1C | producers missing [L] |
| C10 Source completion | factorial energy, repair, co-shift | SEC, CDC, PCS; APF, EWJ, RFHM, WBF | zero-parameter bounds open [L] |
| C11 Local zero location | depth, near-line density, inner caps | WD, census, HEF, SRT, MZF | eight forms [L] |
| C12 Hodge–Lefschetz | HL, zero modes, top stratum | HF, ACS, RIT, EHT, TG, DZG, GWZ, HWV | zero modes radical [L] |
| C13 Sections and counts | source cone, RR | ACS, HF; IRK; WTZ, LST, KPA | Bézout ⇔ RH [L] |
| C14 Reflection | Rosati, Lewis, Krein, dispersion | PM, HF; W1C | coefficient identity, `V_p` [L] |
| C15 Canonical flow | `r,q,Ψ` | CWS, WTZ, DZG, GWZ, CSTW, SWC, CHT, RW, SZ | restoring bound [L] |
| C16 Blind cone | `𝒜(c)`, blind tests | PBAP, FADF, CHT | pinning, exact null test [L] |
| C17 Dimension zero | domination of point counts | ATD, DZG | bare domination ⇔ `Q≥0` [L] |
| C18 Angle dictionary | Hurwitz forms | AHD, ACS, LST, GWZ | `𝔽_q` angle = frequency [L] |
| C19 Two-site band | `\|𝒞_m(f)\|≤W(f)` | GWZ, AOG, SWC, SRT, SOSZ | two-parameter family; spline orbit; Frobenius pairs [L/S] |
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
| C32 Long moments | `∫\|ζM\|²` | APR, CDG, WD, MZF; MC, CTF, WL | slope rigid; necessary length; collision counts past the height [L] |
| C33 Finite-degree detectors | Hausdorff, heat grid, slice, Jensen | PA, HCF, LA, FFP | no fixed family decides [L] |
| C34 Width axis | zero-free parameter | §2.3 | interior is quasi-RH |
| C35 Finite rungs | fixed window, rank, degree, ratio | §2.4 | verification decides each, not B13 [L] |
| C36 Prime-blind duality | Gamma, pole, `log n` | PBAP, EWU, OWU, CHT | RH ⇔ blind positivity [L] |
| C37 Inner factor | Blaschke product | CTF, MZF, AKLT, GWZ, CSTW, AIF | identity, Carleson, `N(ρ)` [L] |
| C38 Eisenstein carrier | `E*(z,½+ib)` | TH, PM, BHR, CTH, ASH; W1C | edge positivity shared [L] |
| C39 Passive medium | echo train of `Λ(n)/√n` | RW, PA, PTR, CHMD, SC | Schur band, tangent [L] |
| C40 Near-line clusters | comparably deep zeros | MZF, NGF, WVL | isolated rate 2; cluster wall open [L] |
| C41 Parabolic flow | gap laws | NGF, ZCG | blind to `t=0` [L] |
| C42 Log-mean | `T⁻¹∫log\|ζ\|` | WD, CTF, RW, ZCG, MC, PM | equivalences; `O(T)` depth [L] |
| C43 Abscissa split | ZAL, AAL, finite oscillation | BAG, JAS, SC, WL, ZCG, RW, IWT | split for every configuration; rigid ¬AAL; shift-invariant [L] |
| C44 Torus and columns | phases, insertion cone | TH, ZCG, FFP | Bernstein, locking, columns add [L] |
| C45 Production | Nair lattice, stencils, Stepanov over ℤ | WL, MC; AE, AKLT, AAD, AGT | rate = Mertens level [L] |
| C46 Characters and weights | Young projections, global trace | ACS, HF | positivity through rank 4 [L] |
| C47 Bohr space | far dipoles, recurrence | RW, HF, BAG | profile decomposition [L] |
| C48 Sign plane | `Ω(a,X)` | RW, ACS, SRT, ZCG, WD | typical-height sign [L] |
| C49 Critical compactness | Γ-liminf, Gårding, threshold chain, pole channel | HF, SRT, AIP | critical curve = window + pole channel [L/S] |
| C50 Forced mollifier | near-extremal rigidity, Abel budgets | CTF, WD, AIF | rigidity; Szegő ratio [L] |
| C51 Horizon scattering | ringdown, horocycles, Farey counts, Lax–Phillips, Narain, cusp energy | PM, BHR, ASH, CTH | width-axis dictionary [L] |
| C52 Beurling isolation | FE defect, count distance | APD, SEL, BAG, SPAL | three isolation metrics [L] |
| C53 Count and height | naive height, Tate limit, point counts | ACS, HF, PM, CWS, AE, ASH, CTH | every hyperelliptic curve; ℤ RH-strength [L] |
| C54 Cut kernel | power-law solutions | WL, MC, RAC, AAD, CTF | kernel = zeros [L] |
| C55 Ledgers and parity | degree-`k` ledgers, exact identity | WL, MC, RAC, AAD, AGT | parity is size [L] |
| C56 Prime torus at finite time | boxes, savings, rounded orbit, mixing time | BAG, TH, SRT, ZCG, PTT | absolute savings [L] |
| C57 Kernel-valued certificates | Agler, Euler, head–tail | TH, RW, PTT, PM | tail-good [L] |
| C58 Hull | fibres over the torus | BAG, ZCG, PTT, AIF | natural boundary `½` [L] |
| C59 Krein law | universal decay, flux sign | PM, BHR, ASH, ACS | sign ⇔ RH [L] |
| C60 Fakes of the black hole | `(q,G,D)`, throat, genus two | PM, ASH, CTH; W1C | damping not a wave law [L] |
| C61 Metaplectic descent | cubic Gauss coefficient | MC, MMD | nonzero residue at `4/3` [L] |
| C62 Transport | return count, tail at a zero, partial returns | BAG, ZCG, AAD, RAC, TAPO, HTG | right discs; zero or small value [L] |
| C63 First return | brackets, precision law, heavy returns | BAG, SRT, TH, PTT, TAPO | constant precision open [L] |
| C64 Conditional tail | head–tail decoupling, collision arithmetic | BAG, TH, WD, TAPO, SPAL | below the Kronecker scale [L] |
| C65 Farey and horocycle | Farey discrepancy, horocycle mean | MC, PM, HWV, CTH | Franel–Landau, Zagier [L] |
| C66 Countermodel boundary | finite top layers | BAG, ZCG, JAS, SC, APD, IWT | firewall; `cosh` models [L] |
| C67 Born rule | partner law, damping, boundary algebra, standard forms | PM, ACS, CTH, ASH | quadratic half = FE; count half = damping; Tomita collapse [L] |
| C68 Topology of the prime complex | homotopy, persistence, fixed points, singular indices | MC, HF, ACS; ESG, HHAC, HWV, ADT, RIAC | classified, `s`-blind [L] |
| C69 Thermal averaging | primon gas | SEL/Primon | Euler factors at real points `>1` [L] |
| C70 Relocation positivity | first-gap negativity | APD; ZCG, BAG | rational surgery detected [L] |
| C71 Two-scale law | asymptotic and local-below properties | every AAL route | cannot decide B13 [L] |
| C72 Exceptional rank | Turán windows, rank barrier | WL, ZCG, ACS, JAS, IWT | thick sets self-improve [L] |
| C73 Tower elimination | well-founded towers, thick crude count | WL, ZCG, ACS, IWT | thick crude count ⇒ AAL; + ZAL ⇒ RH [L] |
| C74 Frobenius substitute | returns freeze smooth polynomials | BAG, PTT, IWT | approximate only [L] |
| C75 Half-products | 𝔽₁-zonotope, `ℙ¹_ℤ` torsion, Frobenius graphs | ACS, HF, PM; SOSZ, AE | off-diagonal assembled; diagonal missing [L/S] |
| C76 Critical weight | damping versus renormalization | ACS, HF, PM; IWT, HHAC, RIAC | renormalization signless [L] |

C1, C4, C16, C19, C25, C26, C48 and C49 are exact window-form dictionaries. C5, C28, C33 require all-root or all-degree control. C11, C32, C40, C42, C48 are asymptotic and weaker than RH; by C71 they cannot reach the AAL half. C13 closes source supply, not effectivity. C8–C10 and C21 retain source-specific bounds. C23, C24, C31, C52 supply calibration or amplification. C45, C34, C65 and C68 are one axis (the Mertens level). C56, C57, C62, C63, C64, C74 are one programme on the dark range. C43, C52, C66, C70, C71, C72, C73 are one programme on the exceptional coordinate. C51, C53, C59, C60, C67, C75, C76 are one programme on the count.

### 3.4 Constructive transfers and their limits

| Sources / routes | Established transfer | Input not transported |
|---|---|---|
| RW/HF/SRT/AIP/ACS | exact receivers for form, band and source energy [L] | all-aperture sign |
| CACT/AHD→RW | critical thresholds end at the window threshold; the pole channel decides below it [L/S] | the window sign itself; the pole channel at every ratio |
| AHD below the onset | aperture ⇄ ratio exchange [L] | any increase of `a*(ζ)` |
| RW→flow | canonical system, restoring bound [L] | bound on `osc Ψ` |
| RW→count | cone points obey PNT `5/6` on the window's range [L] | windows of every length |
| AOG/SOSZ→GWZ | spline orbit and smoothed Frobenius pairs are two-site tests [L/S] | the pair inequality at every scale |
| ACS→RW/SRT | typical-height sign with Gaussian tails [L] | fixed `λ`; exceptional heights |
| APR→PTT/TAPO | necessary mollifier length ↔ primes `≤c log²T` [L] | a near-unit mollifier |
| TH↔ζ on the line | adaptive head leading term `=\|ζ(½+ib)\|²` [L] | sign near critical zeros |
| PM↔TH, PM↔BHR↔CTH | Eisenstein coefficients; horocycle mean = Farey count [L] | any exponent past `½` |
| BHR cusp energy→PM | rate `y^α` forces `Λ_g(ρ/2)=0`; RS Euler product [L/S] | noncancellation (B109) |
| ASH Narain→PM | `¾` ⇒ RH; remainder VK [L] | any rate past VK |
| CTH standard forms→PM | RH ⇔ partner modular conjugation with form `Q` [L] | a positive-energy carrier (B114) |
| IWT→WL/ZCG/ACS | thick crude count ⇒ AAL; RH ⇔ ZAL ∧ thick `√X` [L] | the thick crude count (B110) and ZAL |
| ZCG two-scale law→all AAL routes | scale-separated inputs cannot decide B13 [L] | a two-scale input |
| BAG/AAD/TAPO | transport on right discs; tail transport; partial returns [L] | existence of a rare event at a zero |
| AAL producers | sparse bounds ⇒ AAL [L] | each source bound |
| AAD↔MC | rate ⇔ Mertens level [L] | a level past VK |
| RAC↔CTF | finite-energy cut-kernel mass annihilation ⇒ RH [L] | the annihilation |
| SOSZ/AE→CTH | off-diagonal = `C_∞` + Abel limit of positive torsion [L] | the diagonal; a damping presentation (B88) |
| IWT critical weight→HHAC/RIAC | renormalized torsion is a renormalization, not a damping [L] | a positive damping family |
| CTH curve→ℤ | count law from point counts on curves; Tate principle [L] | a point count over ℤ |
| ESG/HHAC/RIAC→MC | `M(N)` as signed barcode count, core Euler characteristic and sum of prime-vertex indices [L] | any cancellation |
| APD firewall→ZCG/BAG | positive classes, continuation and reflection carry finite layers [L] | intrinsic layers of ζ |

## 4. U-Σ — the sign

Core problem: `1∈ℋ(c)` for every `c`. In cone form, some weight on every window; in causal form, an outer predictor; in flow form, `Ψ` locally bounded; in plane form, `Ω≥0`; in pair form, Hasse–Weil along the spline orbit or for every pair of smoothed Frobenius graphs; in matrix form, every critical threshold `=⊤`, which below `W` is the pole channel alone; in Laguerre form, horizontal-line positivity of Ξ; in theta form, the sign of `|ζ(½+ib)|²` plus second-order terms near the zeros. One scalar: `a*(ζ)`.

| Face | Routes / programmes | Reduction |
|---|---|---|
| Complete atomic matrix | HF, SRT, AIP, ACT, CACT, CSAR, ACPL, RAPT, TM, ADT, AHD | threshold chain ends at the window; pole channel decides below `W` |
| Ground energy, chain, cone | RW, EWU, OWU, CSTW, CHT | `a*(ζ)`; `Ψ`; `λ*` |
| Causal chain | RW, GWZ, AIF | outer predictors; Schur bands |
| Pair tests | GWZ, AOG, SOSZ, SRT | two-site PD; spline orbit; Frobenius pairs |
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
| Torsion and compensation | HHAC, AE, SOSZ, RIAC | `C_∞` + positive torsion; diagonal |

## 5. U-Π — precision and production

Core problem: square-root precision of one smoothed prime count; in tower form, a square-root prime deviation on a thick set of geometric scales together with ZAL. Production, Farey discrepancy, the Farey count, the Euler characteristics of the nerve and core, the barcode and the prime-vertex indices read the same statement through integers, fractions, simplices, persistence and fixed points; none has a mechanism independent of the Mertens level. The dark range is where every sub-RH precision question sits.

| Face | Routes / programmes | Reduction |
|---|---|---|
| Reflection-pair coupling | SWC, GWZ, CSTW, AOG | collar Hankel − smoothed count |
| Classical one-sided counts | WL, PBM, RB, JAS, CTF, HCF | RH-level equivalence; Gaussian ceiling |
| Thick tower counts | WL, ZCG, ACS, IWT | thick crude count ⇒ AAL; + ZAL ⇔ RH |
| Collective kicks | SWC, FADF | beyond size, by sign |
| Cyclotomic mode, gauge torus | MC, CAF, AGT | exponent `½` at the trivial point |
| Integer producers | WL, AKLT, ASRP, AE, AAD, RAC | rate = Mertens level; Stepanov over ℤ = Chebyshev |
| Frobenius substitute | IWT, PTT, TAPO | returns freeze smooth polynomials |
| Parity | WL, MC, RAC, APR | exact identity pins `λ` |
| Möbius, nerve, core, Farey, descent | MC, HWV, ADT, HHAC, ESG, RIAC, CTH, MMD | half-power cancellation |
| Short-sum barrier | every route, PTT | absolute savings |
| First return | BAG, PTT, TAPO | constant precision open |
| Conditional tail and collisions | TAPO, SPAL, IWT | Gaussian below Kronecker; collision counts past the height |
| Near-line density | WD, CDG, MZF, AIF | log-mean; depth `O(T)` |
| Long moments | APR, CDG, WD, MZF; CTF | necessary length = primes `≤c log²T` |
| Budgets | CTF, AIF | second expression; Szegő ratio |
| Negative moments | MZF, MC, ADO | Green potential moments |
| Deciding-input filters | ASRP, APR | parity, purity, precision, aperture |
| Census | SRT, CDG | signed pair data past bandwidth one |
| Sharp horizon sources | CTH | Möbius × circle remainder, beyond RH |

## 6. U-Γ — selection, reflection and transport

Core problem: source-defined arithmetic control of `ρ↦1−ρ̄` and of vertical transport; in count form, the count half of a Born rule whose quadratic half holds; in configuration form, AAL — a two-scale Dirichlet-series input that converts the FE into transport.

| Face | Routes / programmes | Status |
|---|---|---|
| Recurrence, gauge | MC, AGT, BAG, AAD, RAC, PTT, TAPO | transport closed on right discs; tail transport; target mass open |
| Abscissa split | BAG, JAS, SC, WL, AKLT, ZCG, RW, IWT | split for every configuration; ¬AAL rigid; two-scale law; AAL open |
| One-off and FE models | APD, SPAL, RAC, AIF, ACP, IWT | firewall; `cosh` models; ζ isolated in three metrics |
| Time-zero selection | ZCG, NGF | parabolic tools blind |
| Weil cone, lattices | RHTower, GWZ, FADF, CHT | at most `{Λ}`; nonempty iff RH |
| Selberg class | SEL | degree one classified |
| Camera identification | ZCG, SRT, MZF | conditional readout |
| Reality at near-coincidences | ZCG, ADO | FE pair forces small values |
| Diophantine repulsion | ADO, ZCG | `0∉E` open |
| Euler columns, carriers | ZCG, FFP, AIF, TAPO | Euler coordinates stop at `Re s=1` |
| Horizon and count | PM, BHR, ASH, CTH; W1C, ACP | Krein law; Born rule; Tate limit; standard forms; width axis |
| Rosati, Frobenius at infinity | CWS, WTZ, GWZ, AOG | sharpened |
| Source completions | CDC, SEC, PCS; RFHM, EWJ, APF, WBF | source versus forcing |
| Hull | PTT | Liouville point extreme |
| Surface of Spec ℤ | SOSZ, AE, RIAC | off-diagonal assembled; diagonal and jets carrier missing |
| Function-field calibration | many | AAL free by periodicity; ZAL = purity; count law at every genus |

## 7. Cross-family seams

| Seam | Statement | Routes |
|---|---|---|
| Σ ∩ Π: reflection pairs | `W(f±f∘R)=2W(f)±2𝒞_m(f)` | SWC, GWZ, CSTW, AOG, WL [L] |
| Σ ∩ Π: Hardy form | `W=H−P` | FADF [L] |
| Σ ∩ Π: plane and barrier | sign past `log log X` needs short-sum bounds | ACS, AIF [L]; [D] |
| Σ ∩ Π: cone counts | window positivity ⇒ PNT `5/6` on its range | CHT [L] |
| Σ ∩ Π: aperture exchange | window positivity ⇒ depth-`¼` zero-free region | AHD [L] |
| Σ ∩ Π: theta head | head = `\|ζ(½+ib)\|²` | CAF, TCS, AHD [L] |
| Σ ∩ Π: spline orbit growth | orbit correlation growth = zero width | AOG [L] |
| Σ ∩ Γ: chain and mimic | sampling atoms are positive mimics | CSTW, ZCG [L] |
| Σ ∩ Γ: exact completion | coefficient Weil energy = Krein form | RIT [L] |
| Σ ∩ Γ: integer probes and Tate limit | Weil form on the Hecke lattice = Krein square; RH ⇔ Tate limit of a count | ASH, CTH [L] |
| Σ ∩ Γ: Frobenius pairs | window sign ⇔ Hasse–Weil for smoothed graph pairs | SOSZ [S] |
| Σ ∩ Γ: Li and Hodge | Hodge index = Metzler sign = Li | ALG [L] |
| Π ∩ Γ: prime-side AAL | ¬AAL is a finite oscillation; thick crude count ⇒ AAL | ZCG, IWT [L] |
| Π ∩ Γ: cut kernel | zeros are solutions of the Chebyshev moment system | RAC [L] |
| Π ∩ Γ: count | Λ is a torsion intersection number; off-diagonal Weil from half-products | AE, HHAC, SOSZ [L] |
| Π ∩ Γ: tail | zeros of ζ = zeros of every Euler tail; AAL = tail transport | TAPO [L] |
| Π ∩ Γ: first return | weak return = extreme value of `ζ(1+it)`; returns freeze smooth polynomials | TAPO, IWT [L] |
| Π ∩ Γ: horocycle and Farey | horocycle rate = Farey count rate = zero-free region | BHR, CTH [L] |
| Π ∩ Γ: relocation | rational relocation fails positivity at the first gap | APD [L] |
| Σ ∩ Π: gluing and topology | Redheffer = reduced Euler characteristic; prime-vertex localization | HWV, ADT, HHAC, ESG, RIAC [L] |

## 8. Route → core map

| Route | Core | Halves | Classes | Face |
|---|---|---|---|---|
| WL | Π | both | C7, C19, C32, C43, C45, C54, C55, C72, C73 | bounded endpoint energy; integer lag; thick tower count |
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
| MC | Π (Γ) | both | C7, C8, C12, C32, C45, C54, C55, C61, C65, C68 | trivial gauge; Farey; topology |
| TT | Π (Σ) | both | C4 | endpoint upper bound |
| TG | Π, Σ | both | C3, C12 | subunit trace norm |
| HF | Σ (Π, Γ) | both | C1, C12–C15, C18, C25, C47, C49, C53, C75, C76 | pole channel; head windows; count |
| SRT, AIP, ACT | Σ (Π) | both | C1, C4, C11, C19, C21, C25, C48, C49 | complete matrix = window + pole channel |
| SC | Σ, Π (Γ) | AAL branch; both | C2, C3, C7, C39, C43 | glued state; undamped cone ⇒ AAL |
| CHMD | Σ | both | C4, C1, C39 | odd sector |
| RN | Σ | both | C9, C1 | joint nodes |
| WD | Π (Σ) | ZAL side | C3, C11, C32, C40, C42 | long moments; log-mean |
| PM | Γ (Σ) | both | C9, C14, C38, C51, C53, C59, C60, C65, C67 | Krein; horizon receivers; count; standard forms |
| JAS | Π | AAL branch; both | C7, C19, C43, C72 | moving power; shell positivity |
| CTF | Π | both | C7, C19, C32, C37, C42, C50, C54 | BSY, budgets, cut kernel |
| PBM, RB | Π | both | C7, C19 | abscissa, extremal |
| BAG | Γ | AAL | C8, C43, C47, C52, C56, C58, C62–C64, C66, C70, C71, C74 | target mass; tail transport |
| ACS | Π (Σ, Γ) | both | C13, C1, C12, C18, C20, C30, C46, C48, C53, C67, C73, C75 | source sign; count law; thick curve counts |
| SEC, CDC, PCS | Γ | both | C10 | zero-parameter conditions |
| PTR | Σ (Γ) | both | C9, C5, C24, C39 | Laguerre below VK |
| ZCG | Γ (Σ) | ZAL side, AAL layers | C5, C21, C23, C24, C31, C40, C41, C43, C62, C66, C70, C71, C72 | collisions; abscissa laws; tower form |
| Candidates APF, EWJ, RFHM, WBF | Γ (Π) | — | C10 | missing landing |
| Candidate IRK | Γ (Π) | — | C13 | trace with Chern charge |
| Candidates EGC, FEL, MSC | Σ (Π) | — | C6, C1 | landing; history; Sonin sign |
| Candidate W1C | Σ (Γ) | — | C9, C5, C38 | positive realization |
| IWT (support) | Π, Γ | both | C43, C71–C74, C76 | exceptional coordinate; elimination |
| SOSZ (support) | Γ, Σ | — | C19, C53, C75, C76 | half-products; Frobenius pairs |
| RIAC (support) | Π, Σ | — | C68, C76 | prime boundary; compensation; vertex indices |
| TAPO, SPAL (support) | Π, Γ | AAL | C62–C64, C52 | first return; tail; collisions |
| PTT (support) | Π, Γ | — | C56–C58 | orbit at finite time; hull |
| AAD, RAC (support) | Π (Γ) | — | C45, C54, C55, C62 | stencils; kernel; parity; transport |
| ASH, BHR, CTH (support) | Γ | — | C51, C38, C53, C59, C60, C65, C67 | ringdown; Krein law; count law; standard forms |
| MMD (support) | Π | — | C61 | cubic descent |
| AE, KPA, HHAC (support) | Σ, Π | — | C53, C45, C68, C76 | Tate law; torsion |
| ESG (support) | Π | — | C68 | persistence |
| APD, SEL, Primon (support) | Γ | AAL | C20, C52, C66, C69, C70 | firewall; isolation; relocation |
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
| Both halves of the split | split for every configuration; rigid ¬AAL; AAL = transport [L] | one ZAL input; one AAL input |
| A two-scale input for AAL | two-scale law, firewall, `cosh` models, free classes [L] | a Dirichlet-series statement that sees low and high zeros together and converts the FE into vertical transport |
| An elimination step | exceptional-rank window theorem, thick sets, infinite-rank Hasse–Weil principle [L] | none: elimination is available |
| A crude count | thick crude count ⇒ AAL; RH ⇔ ZAL ∧ thick `√X`; Stepanov over ℤ to Chebyshev; Gaussian ceiling receiver [L] | the thick crude count for ζ; a well-founded tower (ZAL) |
| A Frobenius substitute | returns freeze smooth polynomials; approximate forced vanishing [L] | exact returns do not exist; a counting argument from approximate vanishing |
| Budget, not exact sign | subexponential floor ⇒ RH [L] | any such floor |
| Sign of the minimal object | band ⇔ `1∈ℋ(c)` ⇔ `λ*→0` ⇔ pair Hasse–Weil [L] | the band at every step |
| Uniformity in length | each length a rung; critical ratios = windows + pole channel [L/S] | every length; the pole channel |
| Flow | restoring bound, `Ψ`-boundedness ⇔ RH [L] | a bound on `osc Ψ` up to contact |
| Heights | size curve [D]; typical-height sign [L] | sign past `log log X` at rare heights |
| Across primes | columns add; Euler coordinates stop at `Re s=1` [L] | amplitude oscillation |
| The critical line | theta head `=\|ζ(½+ib)\|²` [L]; FE-pair flatness [L] | second-order sign at the critical zeros |
| Time selection | parabolic laws [L] | an arithmetic input separating `Φ` from heated kernels |
| Precision, occupancy | rate 2 isolated; depth `O(T)` [L] | a non-outer control of the inner mass; cluster bound |
| Dark range | brackets; conditional tail below Kronecker; collision counts [L] | the tail law at the Kronecker scale; lower bounds for tail events; proportional saving |
| Count from geometry | half-products assemble the off-diagonal; torsion energy positive; Tate principle; point counts on curves [L] | the diagonal: a counterterm-free damping of a positive object (B88), a count without `Q` (B87) |
| Archimedean carrier | `C_∞` explicit; no metric, toric or continuous carrier [L] | a carrier of the jets of the trivial zeros |
| Reflection | coefficient completion; horizon receivers; Born rule; standard-form criterion [L] | `D_s≥0`; a positive-energy carrier; any horizon exponent past `½` |
| Sparse exceptions | rigid ¬AAL; tower excursions; transport; partial returns [L] | a rare event at a zero or a contradiction in ¬AAL |
| The finite stratum | TFAE of finite index, lattice index, finite off-line set, heat count, eventual RH; towers decide; Lindelöf; single top pair seen at every level of its resonant tower [L/K] | a two-scale input excluding a finite off-line set (B13) |
| Production | exact integrality; VK rate; kernel; parity identity [L] | a level past VK |
| Topology | classified persistence; localization to prime vertices [L] | signed cancellation of the local indices at `√N` |
