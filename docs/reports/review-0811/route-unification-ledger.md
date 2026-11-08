# Route unification ledger — status quo

The 38 live formulations and 9 candidates are faces of three core problems: **U-Σ** (sign), **U-Π** (precision and production) and **U-Γ** (selection and reflection). Their RH-level endpoints meet at the **arithmetic Hardy inequality** `P≤H` on every window, equivalently the **band** `|𝒞_m(f)|≤W(f)` of a test and its mirror, equivalently nonnegativity of one quadratic form `Q` on integer probes, equivalently **`Q` is the Tate limit of a count**. U-Σ reads it as a form on the window, U-Π on the prime side, U-Γ on the zero side.

Transversal to the three, RH splits into **ZAL**, read by height-local receivers, and **AAL**, read by sparse receivers and recurrence. Below the three lie three structural gaps that every family meets: the **dark range**, primes past the Kronecker scale where conditioning on the head needs a Dirichlet polynomial longer than the height; the **missing count**, a nonnegative arithmetic function with quadratic Tate limit `Q`; and the **critical-line input**, the functional equation acting on `Re s=½`, which every one-off countermodel lacks.

**Why there are three cores [D].** No test is compact on both sides of the explicit formula. A compact prime side (U-Σ) leaves infinitely many zero modes, and only an exact sign decides; a localized zero side (U-Π) lets a crude bound decide (one Gaussian prime ceiling per rational height ⇔ RH [L]) but leaves an infinite prime sum at square-root precision; U-Γ is the involution `ρ↦1−ρ` and the selection of ζ among objects sharing its local data. The Lean proof of RH for every hyperelliptic curve has finite rank, a finite prime side and the functional equation together: a crude count at every level (Stepanov), self-improvement by power sums, and the functional equation pinning the modes [L]. Over ℤ the crude statement is ZAL (finitely many zeros beyond each depth) and the self-improvement is AAL (eventual abscissa bound ⇒ global) [L/D]; there is no constant-factor crude regime between strips and RH (Π111).

Corpus checkpoint: commit `48ce5506c8` plus the working tree of 2026-11-08. Evidence: `[L]` Lean source; `[K]` Lean with transitive axiom audit; `[S]` unfinished, unintegrated or uncommitted; `[D]` deduction; `[N]` numerical; `[C]` classical. Locators: [frontier map](../rh-current-frontier-map.md), [scoped obstructions](../rh-killed-routes.md), [walls](walls-ledger.md), [routes](route-obstacles.md).

**Equivalence through RH transfers truth, not mechanism.** Only an explicit source identity or a proved transport moves an estimate between routes. A shared endpoint is not a shared proof. Section 3 separates the two.

## 0. Unifying statements

- **One split [L].** RH ⇔ ZAL ∧ AAL ⇔ ZAL ∧ zero-disc weak recurrence ⇔ ZAL ∧ subexponential polar ground energy. ZAL ⇒ qRH. Under AAL eight RH-level statements coincide. `qRH ∨ AAL` [D].
- **One self-improvement [L].** AAL ⇔ for every `σ`, a bound `Re ρ≤σ` valid for all zeros beyond some height holds for all zeros; the law is invariant under `ξ(s)↦ξ(s+a)ξ(s−a)`, which keeps the FE and moves every abscissa by `a`. At `σ=½` it is "RH above some height ⇒ RH", the finite-stratum law B13.
- **One finite stratum [L/K].** Finite negative index of `K_ζ` ⇔ finite index on one two-prime lattice ⇔ finitely many off-line zeros ⇔ bounded heat count ⇔ RH above some height; in the stratum Lindelöf holds and one non-blind prime tower decides RH.
- **One rigid alternative [L].** ¬AAL ⇔ finite top and bottom layers ⇔ `ψ(x)−x` is one finite oscillation at leading order ⇔ two-prime dilation annihilation of `ψ`.
- **One countermodel boundary [L].** Positive Euler products — continuous, discrete, integer-norm, rational-prime with multiplicative linear counting — carry a finite top layer; none continues to `Re s=½`; FE defect `≤1/6400` forces the rational primes. Positive two-prime polynomials and positive Hecke polynomials annihilate any finite zero set. Rational relocation of ζ's own zeros fails positivity at the first integer gap.
- **One scalar [L].** Every window route measures `a*(ζ)`. Contact is `Ψ=½log H₁` blowing up; RH ⇔ `Ψ` locally bounded.
- **The critical curve is the window [L].** `R_c≤R_polar≤R_high=⨅_A windowThreshold(A)`; at a fixed ratio every conductor channel except the pole is paid; the pole at every ratio is RH. The critical-curve problem of HF, SRT, AIP and ACS is the window problem of RW.
- **One exchange [L].** Below the onset, aperture `a` buys a depth-`¼` zero-free region to height `e^{a/K}`, which buys a sharp pole and `R_polar≥c₁e^{c₂a}`; no step raises `a*(ζ)`.
- **One splitting order [L].** Physical tearing at the collar boundary fails at Schur ratio `4/13`; conductor-adapted splitting decouples. Conductor first, position second.
- **One sign plane [L/D].** `Ω(a,X)`: size reaches all heights to `a≈log log X`; typical heights to `a=δlog T/(64M²)` with Gaussian tails of the bad set.
- **One frequency diagonal [L].** Weil's form is the average of its frequency packets.
- **One scale [L/D].** A near-unit mollifier needs length at least `exp(c log²T)`, the length of an Euler mollifier over the primes `≤c log²T`; absolute non-alignment begins at length `≈L²`; conditional tail laws hold only below the Kronecker scale.
- **One tail [L].** Zeros of ζ are zeros of the Euler tail at every cut; returns at right zeros are tail-bad; every certificate past `Re s=1` is a tail-good condition.
- **One first return [L].** `R(y,η)` bracketed at every precision; weak return = extreme value of `ζ(1+it)`; proportional saving = no early heavy return.
- **One collision arithmetic [L].** Smooth × prime mean squares are diagonal plus collision counts fixed by gcd classes.
- **One width axis [L/D].** Floor rate, damping rate, abscissa, gauge exponent, stability line, long-moment slope, Möbius zero abscissa, integrality exponent, stencil rate, PTR `h`, TH `a`, Hecke level, ringdown gap, horocycle exponent, Farey count exponent, Narain remainder exponent, cusp-energy exponent: interior values are zero-free strips; all unconditional savings sit at VK.
- **One Mertens level [L].** Stencil rate = Mertens level; producer = mollifier on `Re s=1`; Farey discrepancy, the nerve Euler characteristic, the core Euler characteristic minus `#primes(N/2,N]`, and the Farey count at order `C` are `M(N)`.
- **One topology [L].** The prime-product complex is a sphere bouquet with classified persistence, independent of `s`; maps homotopic to the identity have `≥N/(4log N)` fixed points; `M(N)` is the signed count `Σμ(m)` of the barcode.
- **One horizon [L].** Pulse ringdown, horocycle mean, Farey count, Lax–Phillips mode, Narain remainder and cusp energy read the same poles `ρ/2`; gain `δ` past the trivial rate ⇔ strip `2δ`; RH ⇔ `y^{¾}` ⇔ `e^{−t/4}`.
- **One Born rule [L].** A count law = a nondegenerate Born rule (the functional equation, partner law `α↦q/α`) + positivity (universal damping). The boundary algebra with the partner involution has a positive state iff damped; with the Hilbert involution it is `C*` on every black hole.
- **One count [L].** A degree-two form is nonnegative iff a function bounded below lies at bounded distance, iff it is the Tate limit of a nonnegative count. Curve: Stepanov's crude bound at every level gives the count. Fake: count, not quadratic. ℤ: quadratic (Hecke isometry of `Q`), count missing. Linear counts never obey the law; Hecke gives conservation only.
- **One crude regime absent [L/D].** On curves constant-factor bounds self-improve (finite rank); over ℤ `|ψ(x)−x|≤C√x` is false and `x^{½+ε}` is RH.
- **One blindness [L].** Floor identities annihilate every zero mode; exact ledgers are holomorphic off `s=1`.
- **One kernel [L].** Zeros are the power-law kernel vectors of the cut system; finite-energy kernel mass annihilation ⇒ RH.
- **One parity [L].** The exact identity `Σ_{k≤x}F(⌊x/k⌋)=⌊√x⌋` pins `λ`; a power-saving Liouville bound is a zero-free strip; parity is a size statement.
- **One edge [L/D].** Pronic domination, flux, Hermite–Biehler at `σ=1`, Euler coordinates, `3+4cos+cos2`, the Poisson measure of the Hecke algebra, primon thermal averages at `2e^β+1`: every positivity with a proved mechanism stops at `Re s=1`.
- **One inner factor [L].** On `Re s>½`, `E` has inner factor the Blaschke product of right zeros; RH ⇔ `I(w)=0` at one point.
- **One second expression [L].** `exp(2I(1))=inf_Q∫|ζ exp Q|²dP₁`; the shifted/critical Szegő ratio decides RH.
- **One log-mean [L].** Eight forms of `T⁻¹∫log|ζ|→0`, Abel inner mass at infinity, depth density `o(T)`, density-zero damping deficits.
- **One certificate [L].** Causal: outer predictor, Schur band, sum of squares with margins as weights.
- **One column law [L].** On independent reflectors infima add; only amplitudes oscillating with the height cross columns.
- **One theta head [L/C/D].** The adaptive head is the square of a critical-line partial sum of ζ of length half the height, plus terms whose sign is decided near the critical zeros.
- **One Eisenstein carrier [L].** TH spectrum, PM carrier, BHR packets, horocycle means, Farey counts and the Narain scalar projection use `E*(z,½+ib)`; Hecke at `p` is time translation by `log p`.
- **One isolation [L].** ζ is a singleton in FE defect `≤1/6400`, in count distance `o(log n)` among positive integer-norm systems, and under the exact parity identity.
- **One functional equation is not enough [L].** On graphs FE + flux + unitarity + Hecke + integrality + the first-level count do not force damping at genus two; the count law at every level does.
- **One finite-rung rule [L].** Each fixed window, rank, degree, row, ratio and entry follows from verified zeros.
- **One budget [L].** A floor `−C_σe^{2σr}∫F²` for every `σ>0` implies RH.

## 1. Faces of the one object

| Reading | Statement | Anchor |
|---|---|---|
| Index | `κ` counts distinct right zeros; RH ⇔ `κ=0` | HKT, AKLT, CWS [L] |
| Finite stratum | `κ<∞` ⇔ two-prime lattice index finite ⇔ finite off-line set ⇔ bounded heat count ⇔ eventual RH; B13 asks that it be RH | HKT, AKLT, FFP, ZCG [L/K] |
| Winding | predictor polynomial zero-free in the disc on every lattice | AIF [L/D] |
| Onset aperture | nonnegative half-widths `[0,a*]` | WVL, AHD [L] |
| Local onset | `Ω_ψ(a,X)≥0` everywhere | AIF [L] |
| Hardy interval | `⋂ℋ(c)={1}` ⇔ RH | FADF [L] |
| Cone and margin | `λ*(c)→0` ⇔ RH | CHT [L] |
| Datum region | `(1,0)` lies in it ⇔ RH | CHT [L] |
| Two sites | two-site PD | GWZ, SRT [L] |
| Hamiltonian | `Ψ` locally bounded | CSTW, AIF [L] |
| Lattice | Schur parameters in `(−1,1)` | GWZ [L] |
| Causal | outer predictor at every window | AIF [L] |
| Bohr | orbit correlations relatively compact | AIF [L] |
| Critical thresholds | `R_c`, `R_polar`, `R_high` all `=⊤` | AHD [L] |
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
| Ringdown | universal damping; every pulse at `e^{−τ/4}` | BHR [L] |
| Lax–Phillips | every resonant mode decays at `e^{−t/4}` | BHR [L] |
| Horocycle | equidistribution rate `y^{¾−ε}` | BHR [L] |
| Farey count | smoothed totient-weighted Farey count `mC²+O(C^{½+ε})` | CTH [L] |
| Narain | remainder `O(y^{¾−ε})` (sufficient) | ASH [L] |
| Farey discrepancy | `L²≤n^{−1+δ}` | RHTower [L] |
| Long moments | cofinal `θ`; one window | CDG, MZF [L] |
| Positive proportion | every length-2 window | MZF [L] |
| BSY | `I≤0` | RHTower [L] |
| Budgets | `inf_Q budget=1` | AIF [L] |
| Dilation | one fixed-`δ` equality; Szegő ratio | AIF [L] |
| Count | `ψ(x)−x≪√x log²x`; integer lag | RHTower [L] |
| Integrality | Siegel or Liouville half at `√` scale | ASRP [L] |
| Stencil rate | rates `K^{−a}` ∀`a<½` | AAD [L] |
| Cut kernel | finite-energy kernel mass zero | RAC [L] |
| Möbius | subpower Hilbert form; one point; zero-free `M_X` | RHTower, MZF [L] |
| Redheffer / nerve / core | `det=M(N)=−χ̃`; `χ̃=O(N^{½+δ})`; core Euler characteristic `−#primes(N/2,N]` of size `N^{½+δ}` | HWV, ADT, HHAC [L] |
| Recurrence | strong self-return; uniform target mass | RHTower [L] |
| Split | ZAL ∧ AAL | RHTower, AIF [L] |
| Polar ground energy | ZAL ∧ subexponential `μ₀` | RHTower [L] |
| Source criteria | Fock bound, repair equality, co-shift class | RHTower [L] |
| Bézout | source-energy sign | ACS [L] |
| Characters | central class functions with Gram positivity | Representation [L] |
| Integer probes | `Q(a)≥0` on `ℤ^N`; naive heights | ASH, AE, CWS [L] |
| Tate limit | `Q` is the Tate limit of an `ℕ`-valued count | CTH [L] |
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
| Typical heights | `a=δlog T/(64M²)`; bad set Gaussian-tailed; `T^{1−1/(64K)}` at `K log log T` | ACS [L] |
| Cut crystal | fixed depth hidden to `(log T)/36` | WVL [L] |
| Camera | isolated `λ>½`; configurations `λ>1` | ZCG [L] |
| Isolated-zero entry | column bound at length `(log γ)^{O(1/δ)}` | PTT [L] |
| Aperture exchange | depth-`¼` exclusion to height `e^{a/K}` from window positivity at `a` | AHD [L] |

### 2.3 Width axis
| Route | Parameter | Interior value means | Known | Anchor |
|---|---|---|---|---|
| RW, AIP, OWU | floor rate `2σ` | width `≤σ` | VK | S, I [L] |
| SC | Gaussian coupling rate | width `≤σ` | bounded ⇔ RH | ACPL [L] |
| WL, MC | abscissa `2Θ`, gauge exponent | `Θ` | VK | CAF, AGT [L] |
| WD | long-moment slope `2wθ` | `w` | exact | CDG [L] |
| MC | zero abscissa of `M_X` | `Θ` | exact | MZF [L] |
| MC | twin Möbius exponent | `Θ≤2max` | floor `¼` | AGT [L] |
| LA | stability line | zero-free `Re s>σ` | `σ≥1` | FFP [L] |
| PTR | depth `h` | width `≤h` | `h>½−vkWidth` | PTR, ZCG [L] |
| TH | aperture `a` | width `≤a` | VK collar per rank | TCS [L] |
| ZCG | `Λ_Xlog X` | below a fixed `κ₀` gives a strip | `≤6600/9991+ε` | ZCG [L] |
| PM | Hecke level `β` | half-plane `β` | edge only | ACP [L] |
| PM | horocycle / Farey / pulse exponent `½+δ` | `Re ρ≤1−2δ` | `δ=0` (`y^{½−ε}`) | BHR, CTH [L] |
| PM | Narain remainder exponent | strip | VK saving at exponent `½` | ASH [L] |
| PM | cusp-energy exponent `α` | `Λ_g(ρ/2)=0` for `Re ρ>2−2α` | `½` | BHR [L] |
| AAD | stencil rate | `Re ρ≤1−a` | VK; RH gives `[¼,½]` | AAD [L] |
| RAC | Liouville exponent | zero-free `Re s>Θ` | VK | RAC [L] |
| AE | integrality exponent | `Θ` | exact | ASRP [L] |
| TAPO | first-return exponent at constant precision | dark-range saving | `(log y)^{3/2−o(1)}` at bounded harmonic defect | TAPO [L] |
| HHAC | core Euler characteristic exponent | `M(N)=O(N^θ)` ⇒ strip | `θ=1` up to VK | HHAC [L]; [D] |

### 2.4 Finite rungs
| Ladder | Rung | Verified height | Anchor |
|---|---|---|---|
| RW, OWU, EWU, ACT | window `a` | `windowHeight a` | VHR [L] |
| HF, SRT | ratio `R` | window threshold `≥R` | AHD, CACT [L] |
| TH | rank `N` | `41+6(N+2)log(N+2)`; rank 14 from height 67 | TCS [L] |
| LA | degree `d` | `2·10⁷d⁴≤T log T` | VHR [L] |
| LI | entry `n` | `n≤4.7T` | VHR [L] |
| PA | row `k`, `r` | `k+1≤1.5(T−1)`, `r≤RT³` | VHR, S [L] |
| HCF | degree | `deg+1≤T/4800` | VHR [L] |
| Centre PF | order `k` | `k+1≤3T` | VHR [L] |
| Cone | window `c` | PNT `5/6` on `X≤e^{2c−3}` | CHT [L] |

### 2.5 Abscissa split
| Half | Statement | Receivers / producers | Strength |
|---|---|---|---|
| Finite stratum (AAL at `σ=½`) | finitely many off-line zeros ⇒ none (B13) | finite index, lattice index, heat count, `N_d`, eventual RH, one non-blind tower [L/K] | sub |
| ZAL | finitely many zeros beyond each positive depth | inner-field decay, subtracted lag, `Λ_Xlog X→0`, eventual Hadamard, cosine levels, uniform high-collision counts [L] | ≥qRH |
| AAL | eventual abscissa bound ⇒ global; finite right of `½+h` forces none | not-attained top, lags on progressions, Abel-density-zero excursions, polar ground energy, prime-window grid, integer lag, plateaux, JAS (dressed, typical, shell via Turán power sums), towers, cone, weak recurrence, slow returns on right discs [L] | sub |

### 2.6 Scale axis of the prime orbit
| Range of primes at height `t` | What holds | Anchor |
|---|---|---|
| `p≲c log t` | prescribable: every box entered; no cancellation at some height | PTT, RAC [L] |
| Kronecker scale `≈log t` | conditional tail laws stop; first return of the head ≍ height | TAPO [L]; [D] |
| `≈(log t)²` | absolute non-alignment begins; necessary Euler mollifier length | PTT, APR [L]; [D] |
| `(log t)^A` | saving `t^{−δ}`; RH bracket for first return at polynomial precision | PTT, TAPO [L] |
| `exp((log t)^{2/3})` | VK saving; bounded-defect first return `exp(c(log N)^{3/2}/log log N)` | TAPO [L] |
| between | absolute savings only; collision arithmetic gives upper bounds | PTT, TAPO, SPAL [L]; [D] |

### 2.7 The curve proof and its ℤ-counterparts
| Step on a curve over `𝔽_q` | Lean anchor | ℤ-counterpart | Status over ℤ |
|---|---|---|---|
| Crude count at every level: `\|N_n−qⁿ−1\|≤Cq^{n/2}` | Stepanov (RHTower hyperelliptic, CTH) [L] | ZAL (finitely many zeros beyond each depth); crude zero-localized prime count (Gaussian ceiling) | ≥qRH; RH |
| Producer of the crude count | Stepanov's auxiliary polynomial with the Frobenius `x↦x^q` | Stepanov over ℤ = integrality + Nair (Chebyshev); Frobenius over `𝔽_q[T]` = factorial stencil of rate 0, over ℤ rate = Mertens level [L] | missing Frobenius |
| Self-improvement: crude ⇒ sharp by power sums (finite rank) | CTH tower count law ⇔ crude bound [L] | AAL: eventual ⇒ global (ZCG [L]); Turán power sums with a finite head (JAS [L]) | open (B83) |
| Functional equation pins the modes to the circle | CTH, ASH [L] | FE of ξ; Born rule over ℤ = Hecke isometry of `Q` [L] | quadratic half holds |
| Count half: a nonnegative count with quadratic Tate limit | Rosati/Manin/Stepanov counts [L] | RH ⇔ `Q` is the Tate limit of a count [L] | open (B87) |

## 3. Which routes are the same problem

### 3.1 Same problem by source identity or proved transport
| Family | Routes | Identity | Anchor |
|---|---|---|---|
| Window scalar | RW, EWU, OWU, ACT, CHMD (odd), TT (odd), SZ, RN energy, ACS atomic, LI on primitives, HF, SRT, AIP critical branches | one form on one window; sectors exact; first variation = Weil energy; Li form = window form over `𝔽_q`; critical thresholds end at the window threshold; only the pole channel is unpaid at a fixed ratio | SWC, SZ, ALG, ACS, CACT, AHD [L] |
| Log-mean | WD near-line, CTF budgets, ZCG depth law, RW onset at fixed constant, AIF `I` at infinity, BHR bulk log-mean | eight-way equivalence; depth density | CDG, AIF, ASH [L] |
| Mertens level | MC, WL, AAD, AE, CTF defect, PBM, RB, Redheffer, RAC parity, Farey, nerve, core, Farey count | rate ⇔ level; band ⇔ classical criteria; `det=M(N)=−χ̃`; core Euler characteristic; Farey discrepancy and square-root Farey law ⇔ RH | AAD, RAC, RHTower, ADT, HWV, HHAC, CTH [L] |
| Inner mass | CTF BSY, AIF budgets and dilation, MZF `N(ρ)`, KL index | one Blaschke product | AIF [L] |
| Horizon | PM, BHR, ASH, RIT, CTH horocycle, Narain | one scattering matrix; pulse decay, horocycle rate, Farey count rate, Lax–Phillips decay, Narain remainder and cusp-energy rate read the poles `ρ/2` | RIT, BHR, ASH, CTH [L] |
| One-offs | BAG, WL sparse, JAS shell, SC undamped, ZCG one-off layer, AKLT towers, AAD transport, TAPO, RW polar ground energy | ¬AAL as one rigid object; producers transfer; countermodels fail at the critical line | ZCG, AKLT, AAD, TAPO, APD [L] |
| Count | ACS, HF, PM probes, CWS heights, LST Künneth, CTH Tate limit | one quadratic form on integer probes; count law = Born rule + positivity | AE, ASH, CWS, ACS, CTH [L] |
| Tail | BAG returns, TH certificates, PTT Ξ-current, AIF dilation | zeros of ζ are zeros of the Euler tail; certificates = tail-good | TAPO, PTT, AIF [L] |
| Aliases | HJ→PA; BSH→CDC; FEL BSY→CTF | definitions | frontier |

### 3.2 Same endpoint, distinct mechanism
| Group | Routes | Common form only |
|---|---|---|
| Laguerre | TH, PTR, ZCG, LA, GTA, XN, HCF, PA | horizontal-line Laguerre form in a limit |
| Base against columns | TH, ZCG carriers, FFP | `½log(b/2π)` against Euler speed |
| Scheduled sums | FU, CFC, RP, LI | one-sided history floors |
| Source completions | SEC, CDC, PCS; APF, EWJ, RFHM, WBF | a source plus one vanishing at zero parameters |
| Integer gates | TG, WD charge, SC index | an integer that small norm kills |
| Dark-range inputs | B46, B57, B89, B96 | Dirichlet polynomials longer than the height |
| Critical-line inputs | B83, B84, B103 | the functional equation acting at `Re s=½` |
| Critical-line sizes | TH head (B102), ZCG FE-pair flatness (B76), Lindelöf-type bounds | values of ζ on `Re s=½` near its zeros |

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
| C8 Selection / recurrence | trivial gauge; self-return | MC, BAG | transfer closed; target mass open [L] |
| C9 Realization | Krein defect, renewal nodes, Lee–Yang, cosine | RN, PM, PTR; W1C | producers missing [L] |
| C10 Source completion | factorial energy, repair, co-shift | SEC, CDC, PCS; APF, EWJ, RFHM, WBF | zero-parameter bounds open [L] |
| C11 Local zero location | depth, near-line density, inner caps | WD, census, HEF, SRT, MZF | eight forms [L] |
| C12 Hodge–Lefschetz | HL, zero modes, top stratum | HF, ACS, RIT, EHT, TG, DZG, GWZ, HWV | zero modes radical [L] |
| C13 Sections and counts | source cone, RR | ACS, HF; IRK; WTZ, LST, KPA | Bézout ⇔ RH [L] |
| C14 Reflection | Rosati, Lewis, Krein, dispersion | PM, HF; W1C | coefficient identity, `V_p` [L] |
| C15 Canonical flow | `r,q,Ψ` | CWS, WTZ, DZG, GWZ, CSTW, SWC, CHT, RW, SZ | restoring bound; RH ⇔ `Ψ` locally bounded [L] |
| C16 Blind cone | `𝒜(c)`, blind tests | PBAP, FADF, CHT | pinning, exact null test, cone PNT `5/6` [L] |
| C17 Dimension zero | domination of point counts | ATD, DZG | bare domination ⇔ `Q≥0` [L] |
| C18 Angle dictionary | Hurwitz forms | AHD, ACS, LST, GWZ | `𝔽_q` angle = frequency [L] |
| C19 Two-site band | `\|𝒞_m(f)\|≤W(f)` | GWZ, AOG, SWC, SRT | two-parameter family [L] |
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
| C32 Long moments | `∫\|ζM\|²` | APR, CDG, WD, MZF; MC, CTF, WL | slope rigid; necessary length [L] |
| C33 Finite-degree detectors | Hausdorff, heat grid, slice, Jensen | PA, HCF, LA, FFP | no fixed family decides [L] |
| C34 Width axis | zero-free parameter | §2.3 | interior is quasi-RH |
| C35 Finite rungs | fixed window, rank, degree, ratio | §2.4 | verification decides each [L] |
| C36 Prime-blind duality | Gamma, pole, `log n` | PBAP, EWU, OWU, CHT | RH ⇔ blind positivity [L] |
| C37 Inner factor | Blaschke product | CTF, MZF, AKLT, GWZ, CSTW, AIF | identity, Carleson, `N(ρ)`, bounded at infinity [L] |
| C38 Eisenstein carrier | `E*(z,½+ib)` | TH, PM, BHR, CTH, ASH; W1C | edge positivity shared; Hecke diagonal [L] |
| C39 Passive medium | echo train of `Λ(n)/√n` | RW, PA, PTR, CHMD, SC | Schur band, tangent [L] |
| C40 Near-line clusters | comparably deep zeros | MZF, NGF, WVL | isolated rate 2; cluster wall open [L] |
| C41 Parabolic flow | gap laws | NGF, ZCG | blind to `t=0` [L] |
| C42 Log-mean | `T⁻¹∫log\|ζ\|` | WD, CTF, RW, ZCG, MC, PM | equivalences; `O(T)` depth [L] |
| C43 Abscissa split | `Θ∞`, finite oscillation | BAG, JAS, SC, WL, ZCG, RW | split, rigid ¬AAL, eventual-to-global, shift-invariant [L] |
| C44 Torus and columns | phases, insertion cone | TH, ZCG, FFP | Bernstein, locking, columns add [L] |
| C45 Production | Nair lattice, stencils, Stepanov over ℤ | WL, MC; AE, AKLT, AAD, AGT | rate = Mertens level [L] |
| C46 Characters and weights | Young projections, global trace | ACS, HF | positivity through rank 4 and column shapes [L] |
| C47 Bohr space | far dipoles, recurrence | RW, HF, BAG | profile decomposition [L] |
| C48 Sign plane | `Ω(a,X)` | RW, ACS, SRT, ZCG, WD | typical-height sign with Gaussian tails [L] |
| C49 Critical compactness | Γ-liminf, Gårding, non-escape, threshold chain, conductor resolution | HF, SRT, AIP | critical curve = window; only the pole channel [L] |
| C50 Forced mollifier | near-extremal rigidity, Abel budgets | CTF, WD, AIF | rigidity; Szegő ratio [L] |
| C51 Horizon scattering | ringdown, causal symbol, horocycles, Farey counts, Lax–Phillips, Narain, cusp energy | PM, BHR, ASH, CTH | exact solution; AdS₄ quotient; width-axis dictionary [L] |
| C52 Beurling isolation | FE defect, count distance | APD, SEL, BAG, SPAL | three isolation metrics; one-offs stop at the critical line [L] |
| C53 Count and height | naive height, parallelogram, Tate limit | ACS, HF, PM, CWS, AE, ASH, CTH | every hyperelliptic curve [L]; ℤ RH-strength |
| C54 Cut kernel | power-law solutions | WL, MC, RAC, AAD, CTF | kernel = zeros; finite energy decides [L] |
| C55 Ledgers and parity | degree-`k` ledgers, exact identity | WL, MC, RAC, AAD, AGT | parity is size; twin quarter floor [L] |
| C56 Prime torus at finite time | boxes, savings, rounded orbit, mixing time | BAG, TH, SRT, ZCG, PTT | absolute savings [L] |
| C57 Kernel-valued certificates | Agler, Euler, head–tail | TH, RW, PTT, PM | tail-good [L] |
| C58 Hull | fibres over the torus | BAG, ZCG, PTT, AIF | natural boundary `½`; Liouville-odd [L] |
| C59 Krein law | universal decay, flux sign | PM, BHR, ASH, ACS | sign ⇔ RH [L] |
| C60 Fakes of the black hole | `(q,G,D)`, throat, genus two | PM, ASH, CTH; W1C | damping not a wave law; FE and first-level counts present [L] |
| C61 Metaplectic descent | cubic Gauss coefficient | MC, MMD | nonzero residue at `4/3` [L]; transfer open |
| C62 Transport | return count, tail at a zero | BAG, ZCG, AAD, RAC, TAPO | right discs [L] |
| C63 First return | brackets, precision law, heavy returns | BAG, SRT, TH, PTT, TAPO | constant precision open [L] |
| C64 Conditional tail | head–tail decoupling, Gaussian moments, collision arithmetic | BAG, TH, WD, TAPO, SPAL | below the Kronecker scale; upper bounds past it [L] |
| C65 Farey and horocycle | Farey discrepancy, horocycle mean, Farey count | MC, PM, HWV, CTH | Franel–Landau, Zagier, square-root Farey law [L] |
| C66 Countermodel boundary | positive Euler products with a finite top layer | BAG, ZCG, JAS, SC, APD | all stop at `Re s=½` [L] |
| C67 Born rule | partner law, damping, boundary algebra | PM, ACS, CTH, ASH | quadratic half = FE; count half = damping [L] |
| C68 Topology of the prime complex | homotopy, persistence, fixed points, torsion forms | MC, HF, ACS; ESG, HHAC, HWV, ADT | classified, `s`-blind [L] |
| C69 Thermal averaging | primon gas, Kesten–McKay | SEL/Primon | Euler factors at real points `>1` [L] |
| C70 Relocation positivity | first-gap negativity of relocation densities | APD; ZCG, BAG | rational surgery on ζ detected [L] |

C1, C4, C16, C19, C25, C26, C48 and C49 are exact window-form dictionaries. C5, C28, C33 require all-root or all-degree control. C11, C32, C40, C42 are weaker than RH; RH receivers need finite and shallow exceptions controlled, which is C43. C13 closes source supply, not effectivity. C8–C10 and C21 retain source-specific bounds. C23, C24, C31, C52 supply calibration or amplification. C45, C34, C65 and C68 are one axis (the Mertens level). C56, C57, C62, C63, C64 are one programme on the dark range. C43, C52, C66 and C70 are one programme on the critical line. C51, C53, C59, C60 and C67 are one programme on the count.

### 3.4 Constructive transfers and their limits

| Sources / routes | Established transfer | Input not transported |
|---|---|---|
| RW/HF/SRT/AIP/ACS | exact receivers for form, band and source energy [L] | all-aperture sign |
| CACT/AHD→RW | critical thresholds end at the window threshold; conductor resolution leaves only the pole; low packet at every ratio ⇒ RH [L] | the window sign itself |
| AHD below the onset | aperture ⇄ ratio exchange [L] | any increase of `a*(ζ)` |
| RW→flow | canonical system, restoring bound, `Ψ`-boundedness ⇔ RH [L] | bound on `osc Ψ` |
| RW→count | cone points obey local density and PNT `5/6` on the window's range [L] | windows of every length |
| Primes→reflectors | exact tangent; first reflector reads `Λ(n₀)` [L] | size at large `n` |
| Verified heights→rungs | window, Li, Hausdorff, heat, Jensen, PF, theta [L] | verification past 67 |
| ACS→RW/SRT | typical-height sign at unbounded aperture with Gaussian tails [L] | fixed `λ`; exceptional heights |
| ZCG↔WD | depth law reads critical-scale clustering [D] | crowds |
| CDG/MZF→CTF | sharp defect → cofinal moment with `K=3` [L] | arithmetic upper bound |
| APR→PTT/TAPO | necessary mollifier length ↔ primes `≤c log²T` [D] | a near-unit mollifier |
| TH↔ζ on the line | adaptive head leading term = critical partial-sum square [L/C/D] | sign near critical zeros |
| TH↔ZCG | current `2\|Ξ\|²Re ξ′/ξ`; columns against Gamma base [L/D] | prime cancellation above `S*` |
| PTT→TH | Ξ-current lift; frozen certificate exactly above the size curve [L] | below the size curve |
| PM↔TH, PM↔BHR↔CTH | Eisenstein coefficients; same scattering; horocycle mean = Farey count [L] | off-axis positivity; any exponent past `½` |
| BHR cusp energy→PM | rate `y^α` forces `Λ_g(ρ/2)=0` [L] | noncancellation (B109) |
| ASH Narain→PM | Narain `¾` ⇒ RH; remainder carries the VK saving [L] | any rate past VK |
| RN→RW | two-ended formula, energy comparison [L] | joint-node exclusion |
| SZ→Weil | first variation, Abel source [L] | bounded residual |
| BAG/AAD/TAPO | transport on right discs; tail of a return; recurrence dichotomy [L] | a bounded return at a zero |
| TAPO/SPAL→BAG | arithmetic mean values on smooth heads and prime tails [L] | lower bounds for tail events |
| AAL producers | sparse bounds ⇒ AAL [L] | each source bound |
| AAD↔MC | rate ⇔ Mertens level [L] | a level past VK |
| AGT→MC | twin quarter floor [L] | the trivial gauge itself |
| RAC↔CTF | finite-energy cut-kernel mass annihilation ⇒ RH [L] | the annihilation |
| AE/HHAC→ASH/CTH | torsion intersection, renormalized torsion forms on `ℓ²(n^δ)`, compact self-adjoint limit, indefinite on `{p,2p}` [L] | Gamma/pole compensation at `δ=0` |
| CTH curve→ℤ | count law from a crude bound at every level; Tate limit over ℤ [L] | a crude producer over ℤ (no Frobenius; no crude regime) |
| ESG/HHAC→MC | `M(N)` as the signed barcode count and the core Euler characteristic [L] | any cancellation |
| APD relocation→ZCG/BAG | rational surgery fails positivity at the first gap [L] | intrinsic top layers |
| SPAL/RAC/APD→SEL | three isolation metrics; one-offs stop at the critical line [L/D] | anything about ζ's zeros |

## 4. U-Σ — the sign

Core problem: `1∈ℋ(c)` for every `c`. In cone form, some weight on every window; in causal form, an outer predictor; in flow form, `Ψ` locally bounded; in plane form, `Ω≥0`; in matrix form, every critical threshold `=⊤`, which at each fixed ratio is the pole channel alone; in Laguerre form, horizontal-line positivity of Ξ; in theta form, the sign of a critical-line partial-sum square near the zeros. One scalar: `a*(ζ)`.

| Face | Routes / programmes | Reduction |
|---|---|---|
| Complete atomic matrix | HF, SRT, AIP, ACT, CACT, CSAR, ACPL, RAPT, TM, ADT, AHD | threshold chain ends at the window; only the pole channel is unpaid; pole at every ratio = RH |
| Ground energy, chain, cone | RW, EWU, OWU, CSTW, CHT | `a*(ζ)`; `Ψ`; `λ*` |
| Causal chain | RW, GWZ, AIF | outer predictors; Schur bands |
| Local onset | RW, ACS, SRT, AIF | typical-height sign; size curve |
| Sectors, ground states | CHMD, ACT, OWU, EWU, SWC, FADF | two-sector format |
| Hardy, calibration | FADF, PBAP, CHT | arithmetic point in `𝒜(c)` |
| Count, height | AE, CWS, ASH, CTH, LST, KPA | Tate limit of a count; count law on curves |
| Moment problems | SWC, TH, LA, PA, HCF | Stieltjes, Hamburger |
| Theta spectrum | TH, CAF, TCS, AIF, PTT | Euler operators; adaptive head = critical partial-sum square |
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
| Torsion forms | HHAC, AE | renormalized sign at `δ=0` |

## 5. U-Π — precision and production

Core problem: square-root precision of one smoothed short-window prime count; equivalently a crude zero-localized prime count at every level. Production, Farey discrepancy, the Farey count, the Euler characteristics of the nerve and of the core and the barcode count of the prime complex are the same statement read through integers, fractions, simplices and persistence; none has a mechanism independent of the Mertens level. The dark range is where every sub-RH precision question sits.

| Face | Routes / programmes | Reduction |
|---|---|---|
| Reflection-pair coupling | SWC, GWZ, CSTW, AOG | collar Hankel − smoothed count |
| Classical one-sided counts | WL, PBM, RB, JAS, CTF, HCF | RH-level equivalence with the band; Gaussian ceiling |
| Collective kicks | SWC, FADF | beyond size, by sign |
| Cyclotomic mode, gauge torus | MC, CAF, AGT | exponent `½` at the trivial point; twin quarter floor |
| Integer producers | WL, AKLT, ASRP, AE, AAD, RAC | rate = Mertens level; Stepanov over ℤ = Chebyshev; zeros = kernel |
| Parity | WL, MC, RAC, APR | exact identity pins `λ`; power saving = strip |
| Möbius, nerve, core, Farey, descent | MC, HWV, ADT, HHAC, ESG, CTH, MMD | half-power cancellation; Euler characteristics; barcode; Farey law; cubic residue |
| Short-sum barrier | every route, PTT | absolute savings; proportional saving open |
| First return | BAG, PTT, TAPO | brackets; constant precision open |
| Conditional tail and collisions | TAPO, SPAL | Gaussian below Kronecker; collision upper bounds past it |
| Near-line density | WD, CDG, MZF, AIF | log-mean; depth `O(T)`; clusters; last scale |
| Long moments | APR, CDG, WD, MZF; CTF | slope rigid; necessary length = primes `≤c log²T` |
| Budgets | CTF, AIF | second expression; Szegő ratio |
| Negative moments | MZF, MC, ADO | Green potential moments |
| Deciding-input filters | ASRP, APR | parity, purity, precision, aperture, stabilizer |
| Census | SRT, CDG | signed pair data past bandwidth one |
| Sharp horizon sources | CTH | Möbius × circle remainder, beyond RH |

## 6. U-Γ — selection and reflection

Core problem: source-defined arithmetic control of `ρ↦1−ρ̄`; in count form, the count half of a Born rule whose quadratic half (FE, Hecke isometry) holds; in configuration form, AAL.

| Face | Routes / programmes | Status |
|---|---|---|
| Recurrence, gauge | MC, AGT, BAG, AAD, RAC, PTT, TAPO | transport closed on right discs; returns at zeros tail-bad; target mass and trivial gauge open |
| Abscissa split | BAG, JAS, SC, WL, AKLT, ZCG, RW | split and collapse proved; ¬AAL rigid; AAL = eventual-to-global, shift-invariant, open |
| One-off fakes | APD, SPAL, RAC, AIF, ACP | continuous, discrete, integer-norm, rational-prime one-offs; positive annihilators; rational relocation fails positivity at the first gap; ζ isolated in three metrics |
| Time-zero selection | ZCG, NGF | parabolic tools blind |
| Weil cone, lattices | RHTower, GWZ, FADF, CHT | at most `{Λ}`; nonempty iff RH |
| Selberg class | SEL | rigidity; degree one classified |
| Camera identification | ZCG, SRT, MZF | conditional readout |
| Reality at near-coincidences | ZCG, ADO | FE pair forces small values |
| Diophantine repulsion | ADO, ZCG | dimension zero; `0∉E` open |
| Euler columns, carriers | ZCG, FFP, AIF, TAPO | Euler coordinates stop at `Re s=1` |
| Horizon and count | PM, BHR, ASH, CTH; W1C, ACP | Krein law; Born rule; boundary algebra; count law on every hyperelliptic curve; Tate limit over ℤ; width-axis dictionary in space and time; Narain at VK; cusp energy with noncancellation |
| Rosati, Frobenius at infinity | CWS, WTZ, GWZ, AOG | sharpened |
| Source completions | CDC, SEC, PCS; RFHM, EWJ, APF, WBF | source versus forcing |
| Hull | PTT | Liouville point extreme among order-two points |
| Function-field calibration | many | Manin, Stepanov, Castelnuovo, Carlitz stencil, cut kernel, count law at every genus |

## 7. Cross-family seams

| Seam | Statement | Routes |
|---|---|---|
| Σ ∩ Π: reflection pairs | `W(f±f∘R)=2W(f)±2𝒞_m(f)` | SWC, GWZ, CSTW, AOG, WL [L] |
| Σ ∩ Π: Hardy form | `W=H−P`; unique multiple | FADF [L] |
| Σ ∩ Π: size versus sign | edge law; size exact across columns | FADF, SWC, AIF [L] |
| Σ ∩ Π: plane and barrier | sign past `log log X` needs short-sum bounds | ACS, AIF [L]; [D] |
| Σ ∩ Π: cone counts | window positivity ⇒ local density and PNT `5/6` on its range | CHT [L] |
| Σ ∩ Π: aperture exchange | window positivity ⇒ zero-free depth-`¼` region ⇒ sharp pole and Mertens lag | AHD [L] |
| Σ ∩ Π: certificates | frozen Ξ-current certificate exactly above the size curve; past `Re s=1` tail-good | PTT, TAPO [L] |
| Σ ∩ Π: theta head | adaptive head = critical partial-sum square of ζ | CAF, TCS [L/C/D] |
| Σ ∩ Γ: chain and mimic | sampling atoms are positive mimics | CSTW, ZCG [L] |
| Σ ∩ Γ: exact completion | coefficient Weil energy = Krein form | RIT [L] |
| Σ ∩ Γ: visibility | window sign reads depth | WVL, ZCG [L] |
| Σ ∩ Γ: Bohr | RH ⇔ compact orbits | AIF, BAG [L] |
| Σ ∩ Γ: integer probes and Tate limit | Weil form on the Hecke lattice = Krein square; RH ⇔ Tate limit of a count | ASH, CTH [L] |
| Σ ∩ Γ: Li and Hodge | Hodge index = Metzler sign = Li | ALG [L] |
| Π ∩ Γ: prime-side AAL | ¬AAL is a finite oscillation | ZCG [L] |
| Π ∩ Γ: cut kernel | zeros are solutions of the Chebyshev moment system | RAC [L] |
| Π ∩ Γ: count | Λ is a torsion intersection number | AE, HHAC [L] |
| Π ∩ Γ: tail | zeros of ζ = zeros of every Euler tail | TAPO [L] |
| Π ∩ Γ: first return | weak return = extreme value of `ζ(1+it)` | TAPO [L] |
| Π ∩ Γ: isolation | count distance `o(log)`; exact parity identity | SPAL, RAC [L] |
| Π ∩ Γ: horocycle and Farey | horocycle rate = Farey count rate = zero-free region; Farey discrepancy = Mertens level | BHR, CTH, RHTower [L] |
| Π ∩ Γ: mollifier and curve | Abel budgets reach 1 ⇔ Castelnuovo | AIF [L/K] |
| Π ∩ Γ: relocation | rational relocation fails positivity at the first integer gap | APD [L] |
| Σ ∩ Π: gluing and topology | Redheffer = reduced Euler characteristic; core Euler characteristic; barcode | HWV, ADT, HHAC, ESG [L] |

## 8. Route → core map

| Route | Core | Halves | Classes | Face |
|---|---|---|---|---|
| WL | Π | both | C7, C19, C32, C43, C45, C54, C55 | bounded endpoint energy; integer lag |
| RW, EWU, OWU | Σ | both | C1, C4, C15, C16, C19, C22, C25–C27, C39, C43, C47, C48 | `a*(ζ)`; `Ψ`; causal; two sectors; polar ground energy |
| FU, CFC, RP | Σ | both | C6 | full-history bounds |
| SZ | Σ | both | C15, C27 | completed Abel residual |
| LI | Σ (Π) | both | C30, C6 | Cayley–Li sign |
| PA (HJ) | Σ (Π) | both | C5, C22, C33, C39 | rows below the explicit shift |
| TH | Σ (Γ) | both | C5, C22, C33–C35, C38, C44, C56, C57, C64 | adaptive head = critical partial-sum square; amplitude oscillation |
| HCF | Σ (Π) | both | C5, C7, C22, C33 | two grids; Gaussian ceiling |
| LA | Σ | ZAL side | C5, C22, C28, C33 | outer roots |
| GTA | Σ | both | C5 | small charge |
| XN | Σ | both | C5 | covering discs |
| MC | Π (Γ) | both | C7, C8, C12, C32, C45, C54, C55, C61, C65, C68 | trivial gauge; twin floor; cubic descent; Farey; topology |
| TT | Π (Σ) | both | C4 | endpoint upper bound |
| TG | Π, Σ | both | C3, C12 | subunit trace norm |
| HF | Σ (Π, Γ) | both | C1, C12–C15, C18, C25, C47, C49, C53 | pole channel at every ratio; head windows |
| SRT, AIP, ACT | Σ (Π) | both | C1, C4, C11, C19, C21, C25, C48, C49 | complete matrix = window; sharp location |
| SC | Σ, Π (Γ) | AAL branch; both | C2, C3, C7, C39, C43 | glued state; undamped cone ⇒ AAL |
| CHMD | Σ | both | C4, C1, C39 | odd sector |
| RN | Σ | both | C9, C1 | joint nodes |
| WD | Π (Σ) | ZAL side | C3, C11, C32, C40, C42 | long moments; log-mean |
| PM | Γ (Σ) | both | C9, C14, C38, C51, C53, C59, C60, C65, C67 | Krein; dispersion; ringdown; horocycle; Farey count; Lax–Phillips; Narain; cusp energy; count |
| JAS | Π | AAL branch; both | C7, C19, C43 | moving power; shell positivity |
| CTF | Π | both | C7, C19, C32, C37, C42, C50, C54 | BSY, budgets, dilation, cut kernel |
| PBM, RB | Π | both | C7, C19 | abscissa, extremal |
| BAG | Γ | AAL | C8, C43, C47, C52, C56, C58, C62–C64, C66, C70 | target mass; returns; tail |
| ACS | Π (Σ, Γ) | both | C13, C1, C12, C18, C20, C30, C46, C48, C53, C67 | source sign; global trace; count law |
| SEC, CDC, PCS | Γ | both | C10 | zero-parameter conditions |
| PTR | Σ (Γ) | both | C9, C5, C24, C39 | Laguerre below VK |
| ZCG | Γ (Σ) | ZAL side and one-offs | C5, C21, C23, C24, C31, C40, C41, C43, C62, C66, C70 | collisions; finite oscillation; maximal angle |
| Candidates APF, EWJ, RFHM, WBF | Γ (Π) | — | C10 | missing landing |
| Candidate IRK | Γ (Π) | — | C13 | trace with Chern charge |
| Candidates EGC, FEL, MSC | Σ (Π) | — | C6, C1 | landing; history; Sonin sign |
| Candidate W1C | Σ (Γ) | — | C9, C5, C38 | positive realization |
| TAPO, SPAL (support) | Π, Γ | AAL | C62–C64, C52 | first return; tail; collisions; isolation |
| PTT (support) | Π, Γ | — | C56–C58 | orbit at finite time; hull; certificates |
| AAD, RAC (support) | Π (Γ) | — | C45, C54, C55, C62 | stencils; kernel; parity; transport |
| ASH, BHR, CTH (support) | Γ | — | C51, C38, C53, C59, C60, C65, C67 | ringdown; Krein law; count law; Born rule; horocycle; Farey; Narain; cusp channel |
| MMD (support) | Π | — | C61 | cubic descent |
| AE, KPA, HHAC (support) | Σ, Π | — | C53, C45, C68 | Tate law; torsion; torsion forms |
| ESG (support) | Π | — | C68 | persistence |
| APD, SEL, Primon (support) | Γ | AAL | C20, C52, C66, C69, C70 | rigidity; isolation; one-offs; relocation; thermal |
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
| Both halves of the split | split, collapse under AAL, rigid ¬AAL, AAL = eventual-to-global [L] | one ZAL input; one AAL input |
| A critical-line input for AAL | FE-defect rigidity at `1/6400`; every one-off stops at `Re s=½`; positivity annihilates finite zero sets; relocation fails at the first gap [L] | a mechanism by which the FE excludes a finite top layer |
| A self-improvement step | Turán power sums with a finite head; AAL producers [L] | an infinite-rank power-sum elimination for ζ (= AAL) |
| A crude producer | Stepanov over ℤ to Chebyshev; Gaussian ceiling receiver [L] | a Frobenius substitute; a crude zero-localized prime count |
| Budget, not exact sign | bounded or subexponential floor ⇒ RH [L] | any such floor |
| Sign of the minimal object | band ⇔ `1∈ℋ(c)` ⇔ `λ*→0` [L] | the band at every step |
| Uniformity in length | each length a rung; critical ratios = windows; pole channel alone [L] | every length |
| Flow | canonical system, restoring bound, `Ψ`-boundedness ⇔ RH [L] | a bound on `osc Ψ` up to contact |
| Heights | size curve [D]; typical-height sign with Gaussian tails [L] | sign past `log log X` at rare heights |
| Across primes | columns add; brackets; Agler wall; Euler coordinates stop at `Re s=1` [L] | amplitude oscillation; tail-good heights below the size curve |
| The critical line | theta head = critical partial-sum square [L/C/D]; FE-pair flatness [L] | second-order sign at the critical zeros |
| Time selection | parabolic laws [L] | an arithmetic input separating `Φ` from heated kernels |
| Precision, occupancy | rate 2 isolated; depth `O(T)`; log-mean equivalence [L] | a non-outer control of the inner mass at the first dark primes; cluster bound |
| Dark range | first-return brackets; conditional Gaussian tail below Kronecker; collision arithmetic; absolute savings [L] | the tail law at the Kronecker scale; lower bounds for tail events; proportional saving |
| Opposite sign | second expression; Szegő ratio; Castelnuovo over `𝔽_q` [L] | near-unit holomorphic budgets |
| Count from geometry | source cone and RR; Tate law; torsion intersection and renormalized torsion forms; Manin and Stepanov counts on curves; Tate limit over ℤ [L] | a nonnegative count with quadratic Tate limit `Q`, defined without `Q` |
| Reflection | coefficient completion; dispersion; ringdown; horocycle, Farey, Lax–Phillips, Narain and cusp receivers; Born rule [L] | `D_s≥0`; a physical carrier; any horizon exponent past `½` |
| Sparse exceptions | rigid ¬AAL; transport on right discs; tail of a return; recurrence dichotomy [L] | a bounded return at a zero or a contradiction in ¬AAL |
| The finite stratum | TFAE of finite index, lattice index, finite off-line set, bounded heat count, eventual RH; towers decide; Lindelöf; annihilators with left-growth cost; Turán on a finite set [L/K] | the FE excluding a finite off-line set (B13) |
| Production | exact integrality; VK rate; kernel; parity identity; twin floor; Frobenius = factorial stencil over `𝔽_q[T]` [L] | a level past VK; an input not blind to zeros |
| Topology | classified persistence; core bouquet; fixed-point lower bound [L] | a natural relative pair or signed localization at `√N` |
