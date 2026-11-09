# Route unification ledger — status quo

The 38 live formulations and 9 candidates are faces of three core problems: **U-Σ** (sign), **U-Π** (precision and production) and **U-Γ** (selection, reflection and transport). Their RH-level endpoints meet at one object, and that object is local in scale: **one inequality per prime, on the primes of sparse windows**. For every prime `p` the smoothed prime count in the window of `p` exceeds its archimedean-plus-pole prediction by at most a constant, `P(p)≤A(p)+K`; equivalently `c_B(log p)≥−K` (one side of Hasse–Weil for the smoothed Frobenius graph of degree `p`); equivalently Weil's form is bounded below on the two-bump test `B+τ_{log p}B`; equivalently the effective class `Γ_1+Γ_p` carries a count with Tate limit `2c_B(0)+2c_B(log p)`; and, with no sign at all, `|c_B(log p)|≤K` [L]. The primes need not all be used: for every `r>0` the bound at the primes of arbitrarily late windows `|log p−T|≤r√T` is RH [L]. U-Σ reads the object as the sign of one test per prime, U-Π as a crude prime count, U-Γ as the count half of a Born rule on one ray per prime. Unconditionally the error is `O(√d·exp(−(log d)^{3/5}/(10⁸log log d)))` [L].

Transversal to the three cores, RH has three atoms: **ZAL** (finitely many zeros beyond each positive depth), **B13** (finitely many off-line zeros ⇒ none) and **Landing** (ZAL ⇒ finitely many off-line zeros); RH ⇔ ZAL ∧ B13 ∧ Landing, AAL ⇔ B13 ∧ Landing ∧ DH, and no two atoms fail together [L]. Every atom needs the FE and the Euler product together (calibrations exist for each without one of them), couples low and high zeros (two-scale law), and is invisible in law (random Euler products have no zeros right of `½`) [L/D].

Four structural gaps lie under all three cores: the **dark range** (primes past the Kronecker scale; returns of the prime orbit are counted only beyond a transcendence depth floor that grows with the number of primes); the **diagonal** (a counterterm-free positive presentation of the diagonal of Weil's form: local Robin data give the discriminant, Gram coupling gives finite limits with a signed defect, and a discrete adelic quotient carries the degree points with no Green/Robin identity yet); the **two-scale FE–Euler input** (an inequality that the explicit formula does not imply, since the exact identities of the finite-layer world are consistent); and the **jump at ζ** (in the family of twists ζ is the fibre carrying the pole, so Deligne's family step cannot transfer generic purity to it).

**Why there are three cores [D].** No test is compact on both sides of the explicit formula. A compact prime side (U-Σ) leaves infinitely many zero modes, and only an exact sign decides. A localized zero side (U-Π) lets a crude bound decide but leaves the prime side at square-root precision. U-Γ is the involution `ρ↦1−ρ̄`, the selection of ζ and the transport of its zeros. The curve proof uses two freebies that ζ lacks: finite rank, which makes elimination algebraic and ZAL automatic, and zeros periodic in height, which make AAL automatic [L]. The prime side removes the need for attainment (decisive samples) and for global data (scale locality); the exceptional coordinate is reduced to three calibrated atoms.

Corpus checkpoint: commit `43e39a9cec` (2026-11-09); working log `logs/review-0911-statusquo-research-3.md`. Evidence: `[L]` Lean source; `[K]` with transitive axiom audit; `[S]` unfinished or unintegrated; `[D]` deduction; `[N]` numerical; `[C]` classical. Locators: [frontier map](../rh-current-frontier-map.md), [scoped obstructions](../rh-killed-routes.md), [walls](walls-ledger.md), [routes](route-obstacles.md), [summary](obstacles-summary.md).

**Equivalence through RH transfers truth, not mechanism.** Only an explicit source identity or a proved transport moves an estimate between routes. Section 3 separates the two.

## 0. Unifying statements

- **One inequality per prime [L].** RH ⇔ `c_B(log p)≥−K` at every prime ⇔ `≤K` ⇔ `P(p)≤A(p)+K` ⇔ `Re W(B±τ_{log p}B)` bounded below; width `≤a` ⇔ the same with `Kp^a`; unconditionally the VK saving.
- **One sign-free decision step [L].** RH ⇔ `|c_B(log p)|≤K`; width `≤σ` ⇔ `|c_B(log p)|≤Kp^σ`; the same on every power-saving gap set; absolute convergence, continuation and the Laplace rate theorem suffice.
- **One local decision [L].** A lower bound `c_B(u)≥−Ke^{αu}` on arbitrarily late windows `|u−T|≤r√T` puts every zero of a tempered real-zero-free configuration at depth `≤α`; at the primes, RH ⇔ the bound on the primes of arbitrarily late `√T` windows. Mechanism: infinite positive deletion (three-point probability averages, additive Gaussian cost), a surviving finite spectrum with bounded-gap negativity, exponentially small leakage.
- **One sample principle [L].** Decisiveness is compactness, not density or gaps: gappy prime samples and prime-power samples of zero convergence exponent decide; Bohr-dense sets decide attained tops; density-zero exceptions, very smooth degrees and finitely many Frobenii admit unattained tops; one Frobenius aliases; δ-separated configurations are decided by windows of length `80/δ`.
- **One tensor-power trick [L].** RH ⇔ the even tensor powers of the virtual motive of the zeros have a common abscissa ⇔ `A_k=o(k)`; every constituent of `M^{⊗m}` is a Tate twist with a pole; positivity is free, uniformity is RH.
- **One family [L].** The gauge torus of twists has big monodromy, Gaussian and pure generic fibres, and ζ's vertical family is equidistributed in it at every fixed degree; ζ is the jump fibre (the pole); trace constants are closed but blow up at ζ; exact monodromy transfers only the trivial bound; summable deformations keep the zeros.
- **One split and three atoms [L].** For every configuration purity ⇔ ZAL ∧ AAL ⇔ ZAL ∧ B13 ∧ Landing; AAL ⇔ B13 ∧ Landing ∧ DH; existential linear AAL ⇔ B13 ∧ Landing; the atoms never fail in pairs.
- **One gate [L].** Landing for ζ ⇔ eventual Hadamard positivity holds uniformly up to the line ⇔ the Hadamard threshold stays bounded as `σ↓½` ⇔ ZAL forces finite Krein–Langer index ⇔ ZAL forces bounded heat counts, slice positivity, the central-gap budget, finite odd bound states, the line above a height.
- **One dial [L].** `LinAt C ⇔` eventual-to-global at slope `C`; `∃C` collapses to `ZAL⇒RH`; `AAL ⇔ ∀C>1`; the levels are strictly separated by explicit configurations.
- **One exponent [L].** `Θ∞` is the infimum exponent of `ψ(x)−x` modulo finite exponential sums.
- **One transport [L].** AAL ⇔ zero transport ⇔ tail transport; the FE reflects every height to itself; the only exact symmetries of the prime orbit are the integer dilations.
- **One two-scale law [L].** No property of the zeros above a height and none below a fixed height decides B13, landing, any linear law or AAL.
- **One family law [L].** A finite-stratum law valid on every heat deformation is RH; heat finiteness (Ki–Kim–Lee) does not pass to `t=0`; only `τ=0` has a Dirichlet series.
- **One analytic freedom [L].** FE, order one and reality admit every finite top layer and remainders approaching the line.
- **One firewall [L].** Continuous Beurling systems, positive discrete and integer-norm Euler products with linear counting continued across `Re s=½`, rational-prime one-offs and one reflection pair carry finite top layers; integer-norm Euler products also carry approaching remainders and two-scale tops; positive annihilators price zeros and never exclude them. Only the FE excludes the layer, and only together with the Euler product.
- **One calibration where Euler + FE succeed [L].** A finite Euler product with an FE has every zero on the line; a countable Beurling system whose theta function satisfies Riemann's FE up to an `L¹` or `L²` defect is the rational primes.
- **One repulsion [L].** Real zeros of quadratic `L(s,χ)` repel the other zeros of `ζL(χ)` (Deuring–Heilbronn, constant uniform in conductor and height); ζ has no Siegel regime, so the mechanism has nothing to act on.
- **One rigid alternative [L].** ¬AAL ⇔ an isolated top over an infinite remainder ⇔ `ψ(x)−x` a finite oscillation at leading order ⇔ two-prime dilation annihilation ⇔ syndetic lag excursions at every base.
- **One exceptional current [L].** Under ¬AAL the corrected Gaussian current at exponential damping is the top mode times a finite wave; filters read each top mode with the remainder retained; the Euler series bounds the filters only above abscissa `1`. The identities are mutually consistent: none is a contradiction.
- **One random model [L/D].** Haar-a.e. Euler products are zero-free right of `½` with natural boundary `½`; off-line zeros of ζ, if any, sit on density-zero sets of heights; every in-law statement is blind to them.
- **One elimination [L].** The exceptional rank decides Turán windows; infinite power sums detect a maximal term; no thick set carries a bound below an isolated top; Wolff towers show well-foundedness is needed.
- **One finite stratum [L/K].** Finite negative index of `K_ζ` ⇔ finitely many off-line zeros ⇔ bounded heat count ⇔ RH above some height; in the stratum Lindelöf holds and RH ⇔ one non-blind prime tower PD.
- **One scalar [L].** Every window route measures `a*(ζ)`; RH ⇔ `Ψ` locally bounded.
- **The critical curve is the window plus one inequality [L].** `R_c=R_polar=R_halfline≤R_prim=R_high=W`; under ¬RH a unit half-line ground state lives at finite `W` and is polar-orthogonal if `R_polar=W`.
- **One scale of the prime orbit [L/D].** A near-unit mollifier needs length `exp(c log²T)`; conditional tail laws hold only below the Kronecker scale; past the height long mean values are collision counts of order `X²`; heavy subsets are silent to `log t=(log y)^{3/2−ε}`; collective return counts hold beyond a depth floor growing with the number of primes.
- **One Frobenius substitute, capped [L].** Returns freeze smooth Dirichlet polynomials with precision-capped Rouché copies; the Adams operation is the Frobenius of integer auxiliaries, exact only on the torsion; the exact Stepanov count over ℤ is Chebyshev's; no finitely generated ℤ-lattice of zero modes is stable under three prime Frobenii.
- **One width axis [L/D].** Every interior value of every growth or decay parameter is a zero-free strip; all unconditional savings sit at VK.
- **One Mertens level [L].** Stencil rate, Farey discrepancy, nerve and core Euler characteristics, prime-vertex indices, gluing charge and the centred count of the orientation cover are `M(N)`.
- **One horizon [L].** Pulse ringdown, horocycle mean, Farey count, Lax–Phillips mode, Narain remainder, seed response and cavity energy read the poles `ρ/2`; one cavity function of Hecke eigenforms sees every resonance; the reflection Krein form is PSD ⇔ RH.
- **One Born rule and one count [L].** A count law = nondegenerate Born rule (the FE) + positivity (damping); over ℤ the quadratic half holds; `Q` is not integer-valued; one effective ray `Γ_1+Γ_p` per prime needs one count.
- **One surface [L].** Off the diagonal Weil's kernel is the pole minus the Green functions of all places at their tempered edges: `2πG_{1/2}` on the degree geodesic of `ℍ³` and the tree Green functions at the Ramanujan point on the `p`-ladders; the archimedean compensation is spherical; atoms lock to the discriminant; ordered Gram coupling gives finite limits with an exact defect; a discrete adelic quotient by the rational split torus carries the degree points; the sign sits in the diagonal.
- **One Lefschetz identity [L].** The Ξ explicit formula is Deninger's distributional Lefschetz formula and the trace of the Meyer source flow; λ-ring effectivity reduces to the defect floor (Hodge index).
- **One finite-rung rule [L].** Each fixed window, rank, degree, row and ratio follows from verified zeros; no finite verification decides B13, landing, any linear law or AAL.

## 1. Faces of the one object

| Reading | Statement | Anchor |
|---|---|---|
| Index | `κ` counts distinct right zeros; RH ⇔ `κ=0` | HKT, AKLT, CWS [L] |
| Finite stratum | `κ<∞` ⇔ finite off-line set ⇔ bounded heat count ⇔ eventual RH ⇔ slice positivity ⇔ central-gap budget ⇔ finite odd bound states | HKT, AKLT, FFP, ZCG [L/K] |
| Three atoms | ZAL ∧ B13 ∧ Landing | ZCG, ELT [L] |
| Hadamard threshold | eventual Hadamard positivity with a threshold bounded as `σ↓½`, plus B13 | ELT [L] |
| Onset aperture | nonnegative half-widths `[0,a*]` | WVL, AHD [L] |
| Local onset | `Ω_ψ(a,X)≥0` everywhere | AIF [L] |
| Hardy interval | `⋂ℋ(c)={1}` | FADF [L] |
| Cone and margin | `λ*(c)→0` | CHT [L] |
| Two sites | two-site PD | GWZ, SRT [L] |
| Spline orbit | Hasse–Weil along the cubic-spline orbit | AOG [L] |
| Frobenius graphs | one side of Hasse–Weil at any power-saving gap set of degrees; either side | SOSZ [L] |
| Prime two-bumps | `Re W(B±τ_{log p}B)` bounded below at every prime | SOSZ [L] |
| Stepanov prime count | `P(p)≤A(p)+K` at every prime | SOSZ [L] |
| Two-sided prime count | `\|c_B(log p)\|≤K`, sign-free | CDGeo [L] |
| Local prime count | `P(p)≤A(p)+K` at the primes of arbitrarily late `√T` windows | SOSZ ScaleLocality [L] |
| Decisive samples | the Stepanov bound on gappy primes, on prime powers of zero convergence exponent, off power-thin exceptions | SOSZ [L] |
| Bohr-dense samples + ZAL | the Stepanov bound on runs of integers together with ZAL | SOSZ [L] |
| Tensor powers | `A_k=o(k)` | SOSZ, AWT [L] |
| Two Frobenii | one-sided bounds on the dense lags `log m−log n`, `m,n∈⟨p,q⟩` | SOSZ [L] |
| Plane counts | one count per effective prime ray; copositive prime planes | SOSZ [L] |
| Hamiltonian | `Ψ` locally bounded | CSTW, AIF [L] |
| Causal | outer predictor at every window | AIF [L] |
| Bohr | orbit correlations relatively compact | AIF [L] |
| Critical thresholds | `R_c=R_polar=R_halfline`, `R_prim=R_high=W`, all `=⊤` | AHD [L] |
| Low packet | polar payment at every ratio | CACT [L] |
| Moments | Hamburger, shifted Hamburger, Stieltjes | SWC [L] |
| Li / Cayley | ladder NSD on primitives | ALG [L] |
| Suzuki | first variation = Weil energy | RHTower [L] |
| Heat | no positive-time collisions | RHTower, ZCG [L] |
| Gaussian ceiling | `P(ε,r)` bounded above for every rational `r≥½` | RHTower [L] |
| Cosine | strict Laguerre on the open strip | PTR [L] |
| Jensen | infinitely many degrees real | FFP [L] |
| Hausdorff | rows below the explicit shift | S [L] |
| Theta ranks | signed Hankel at every rank | RHTower, TCS [L] |
| Krein | `D_s≥0` | RIT [L] |
| Ringdown / Lax–Phillips | every mode at `e^{−t/4}` | BHR [L] |
| Horocycle / Farey / cavity energy | rate `y^{¾−ε}` | BHR, CTH, AHMH [L] |
| Reflection Krein form | every reflection Krein form of the cavity PSD | AHMH [L] |
| Narain | remainder `O(y^{¾−ε})` (sufficient) | ASH [L] |
| Farey discrepancy | `L²≤n^{−1+δ}` | RHTower [L] |
| Long moments | cofinal `θ`; one window | CDG, MZF [L] |
| BSY / budgets / dilation | `I≤0`; `inf_Q budget=1`; one fixed-`δ` equality | RHTower, AIF [L] |
| Count | `ψ(x)−x≪√x log²x`; integer lag | RHTower [L] |
| Tower count | ZAL ∧ thick `O(√X)` prime deviation | IWT [L] |
| Linear law | ZAL ∧ `LinAt C` | ZCG, IWT [L] |
| Stencil rate | rates `K^{−a}` ∀`a<½` | AAD [L] |
| Cut kernel | finite-energy kernel mass zero | RAC [L] |
| Möbius / nerve / cover | `M(N)=O(N^{½+δ})`; cover weight `½` | RHTower, HWV, ADT, HHAC, RIAC, HAT [L] |
| Recurrence | strong self-return; uniform target mass | RHTower [L] |
| Polar ground energy | ZAL ∧ subexponential `μ₀` | RHTower [L] |
| Source criteria | Fock bound, repair equality, co-shift class | RHTower [L] |
| Bézout | source-energy sign | ACS [L] |
| Integer probes / Tate limit | `Q(a)≥0` on `ℤ^N`; `Q` the Tate limit of an `ℕ`-count | ASH, AE, CWS, CTH [L] |
| Standard form | internal modular conjugation realizing `Q` | CTH [L] |
| Hull | Liouville fibre extends | PTT [L] |
| Parity | `L(x)≪x^{½+ε}` | RAC [L] |
| Fixed-point auxiliary | `log N(A_N)=ψ(N)≤N+C√N log²N` | ALST [L] |
| Sampling-set bound + ZAL | one-sided bound at the primes `≡a (mod q)`, off a density-zero set or at `p^aq^b`, with ZAL | SOSZ [L] |
| Metric recurrence + ZAL | positive-dimensional recurrent lag bases at every rate, with ZAL | IWT [L] |

## 2. Axes

### 2.1 Window axis
| Coordinate | Half-width `c` | Anchor |
|---|---|---|
| Markov death | `e^{−3/4}` | SWC [L] |
| Perron threshold; sign change of `C_∞` | `log ρ≈0.2812` (plastic) | SWC, FADF, SOSZ [L] |
| Odd prime entry | `½log 2` | FADF [L] |
| Known sign, Lean | `<0.3621`; base `a₀>181/500` | AIP, LST, AIF [L] |
| Odd unit window | `½`, margin `≈2·10⁻⁴` | SWC [L/N] |
| Prime-three entry | `2c=log 3` | SWC, AHD [L] |
| Variance-free certificates | fail for `c>273/400` | SWC [K] |
| `{2,3,4}` frontier | `2c<log 5` | SWC [L] |
| Tate dimension one | positive exactly for length `≤log 5` | WTZ [L] |
| Edge-law crossing | `c*∈(½log5,½log6]` | FADF [L] |
| End of finite templates | spread `27/5` | WTZ [L] |

### 2.2 Sign plane
| Curve in `(a,log X)` | Statement | Anchor |
|---|---|---|
| Height non-locality | low zeros do not decide | WVL [L] |
| All heights, size | `a≈log log X−log 4` | [L]/[D] |
| Typical heights | `a=δlog T/(64M²)`; Gaussian-tailed bad set | ACS [L] |
| Cut crystal | fixed depth hidden to `(log T)/36` | WVL [L] |
| Aperture exchange | depth-`¼` exclusion to height `e^{a/K}` | AHD [L] |

### 2.3 Scale axis of the minimal face
| Window radius in `u=log p` around a late `T` | Decides | Anchor |
|---|---|---|
| all `u` (every prime, every power-saving gap set) | RH | SOSZ [L] |
| `r√T`, any `r>0`, along any sparse sequence of `T` | RH, every tempered configuration | SOSZ ScaleLocality [L] |
| `C·log²T` | ζ: leakage exponentially small; criterion not assembled | SOSZ ScaleLocality [L] |
| `40/δ` (bounded) | δ-separated configurations | SOSZ [L] |
| bounded | finite stratum [D]; ζ's zero counting: open (B140) | — |
| shrinking (`[x,x+x^θ]`, super-lacunary) | no | [D] |
| one prime's powers | no (aliasing) | SOSZ [L] |

### 2.4 Width axis
| Route | Parameter | Interior value means | Known | Anchor |
|---|---|---|---|---|
| RW, AIP, OWU | floor rate `2σ` | width `≤σ` | VK | S, I [L] |
| WL, MC | abscissa `2Θ`, gauge exponent | `Θ` | VK | CAF, AGT [L] |
| WL, IWT | continuous-level lag exponent `a` | zero-free `Re>½+a` | VK | IWT [L] |
| WD | long-moment slope | `w` | exact | CDG [L] |
| MC | zero abscissa of `M_X` | `Θ` | exact | MZF [L] |
| LA | stability line | zero-free `Re s>σ` | `σ≥1` | FFP [L] |
| PTR | depth `h` | width `≤h` | `h>½−vkWidth` | PTR [L] |
| TH | aperture `a` | width `≤a` | VK collar per rank | TCS [L] |
| ZCG | `Λ_Xlog X` | strip | `≤6600/9991+ε` | ZCG [L] |
| PM | horocycle / Farey / pulse / cavity exponent | `Re ρ≤1−2δ` | `δ=0` with stretched-exponential saving | BHR, CTH, AHMH [L] |
| PM | Narain remainder exponent | strip | VK saving at `½` | ASH [L] |
| ACS, SOSZ | growth exponent of either side at the primes, at any gap set, at `√T` windows | width | VK saving | SOSZ [L] |
| SOSZ, AWT | tensor-moment exponents `A_k` | `A_k≥2k·width−1` | none sublinear | AWT [L] |
| AAD | stencil rate | `Re ρ≤1−a` | VK; RH gives `[¼,½]` | AAD [L] |
| RAC | Liouville exponent | zero-free `Re s>Θ` | VK | RAC [L] |
| HAT, RIAC | weight of the orientation cover over ℤ | strip | `≥½`; `½` ⇔ RH | HAT [L] |
| TTPO | heavy-return exponent `log R≥y^c` | Littlewood-type size of `ζ(1+it)` | `(log y)^{3/2−ε}` | TTPO [L] |

### 2.5 Finite rungs
| Ladder | Rung | Verified height | Anchor |
|---|---|---|---|
| RW, OWU, EWU, ACT | window `a` | `windowHeight a` | VHR [L] |
| TH | rank `N` | `41+6(N+2)log(N+2)` | TCS [L] |
| LA | degree `d` | `2·10⁷d⁴≤T log T` | VHR [L] |
| LI | entry `n` | `n≤4.7T` | VHR [L] |
| PA | row `k`, `r` | `k+1≤1.5(T−1)`, `r≤RT³` | VHR, S [L] |
| HCF | degree | `deg+1≤T/4800` | VHR [L] |
| Centre PF | order `k` | `k+1≤3T` | VHR [L] |
| Cone | window `c` | PNT `5/6` on `X≤e^{2c−3}` | CHT [L] |
| B13, landing, linear laws, AAL | none | no finite verification decides | ZCG [L] |

### 2.6 Exceptional coordinate
| Level | Statement | Receivers / producers | Strength |
|---|---|---|---|
| ZAL | `Θ∞=½`; well-founded towers; eventual Hadamard positivity | inner-field decay, subtracted lag, `Λ_Xlog X→0`, high-collision counts, LH with cosine levels [L] | ≥qRH |
| Landing (B138) | ZAL ⇒ finite off-line set | eleven equivalent forms for ζ: bounded Hadamard threshold, finite Krein–Langer index, bounded heat counts, slice positivity, central gaps, odd bound states, line above a height [L]; fails for FE-only and Euler-only models [L] | sub |
| Finite stratum (B13) | finite off-line set ⇒ none | finite index, lattice index, heat count, `N_d`, eventual RH, one non-blind tower, one Toeplitz-positive tower [L/K]; no family-uniform input | sub |
| `ZAL⇒RH` (B111) | B13 ∧ Landing; existential linear AAL | every ZAL receiver becomes an RH receiver [L] | sub |
| Fixed slope (B116) | `Θ−½≤C(Θ∞−½)` | finite-rank Chebyshev self-improvement; thick relative crude count [L] | sub |
| DH (B141) | ¬AAL ⇒ ZAL; AAL on `¬ZAL` worlds | classical Deuring–Heilbronn for quadratic `L(s,χ)` [L]; refuted on integer-norm two-scale products [L]; AAL(ζ) ⇔ DH(`L_a`) [D] | sub |
| AAL (B83) | B13 ∧ Landing ∧ DH; zero transport | not-attained top, progressions, Abel-density-zero excursions, polar ground energy, prime-window grid, integer lag, JAS, towers, cone, weak recurrence, slow returns, thick lag, thick prime deviation, tower count, sampling-set or Bohr-dense bound, metric recurrence, tensor moments at a class [L] | sub |
| Thick crude count (B110) | `primeDeviation=O(X^{½+a})` on thick scales ∀`a>0` | ⇒ AAL; with ZAL at `a=0` ⇔ RH [L] | AAL |
| Sampling-set bound (B126) | one-sided bound on a sampling or Bohr-dense set | ⇒ AAL; with ZAL ⇔ RH; on a decisive sample ⇔ RH [L] | AAL |

### 2.7 Scale axis of the prime orbit
| Range of primes at height `t` | What holds | Anchor |
|---|---|---|
| `p≲c log t` | prescribable: every box entered | PTT, RAC [L] |
| Kronecker scale `≈log t` | conditional tail laws stop | TAPO [L]; [D] |
| `≈(log t)²` | absolute non-alignment; Euler mollifier length for near-unit moments | PTT, APR [L] |
| `(log t)^A` | saving `t^{−δ}` | PTT, TAPO [L] |
| `exp((log t)^{2/3+ε})` | no heavy subset aligned at precision `δ≤1/20` | TTPO [L] |
| beyond the depth floor `δ(k)^{−1}` | collective return counts `≤(5π/2)max(T/2,δ^{−1})e^{−W/(8M)}` | CDGeo [L] |
| between | absolute savings; collision arithmetic; precision-capped freezing | PTT, TAPO, SPAL, IWT [L] |

### 2.8 The curve proof and its ℤ-counterparts
| Ingredient on a curve over `𝔽_q` | ℤ-counterpart | Status over ℤ |
|---|---|---|
| Finite rank: elimination is algebra, outer part well-founded | ZAL = well-foundedness of the towers of ζ | ≥qRH, open |
| Periodicity of the zeros in height ⇒ AAL | AAL = zero transport; the only exact orbit symmetries are dilations | open (B83); no base change moving heights at fixed real part [D] |
| Euler product + FE at finite rank ⇒ purity | Euler product + FE with integrable defect ⇒ rational primes | classification; transport (B112) open |
| Stepanov's bound `N_n≤qⁿ+1+Cq^{n/2}` | `P(p)≤A(p)+K` on a decisive sample, local in scale; two-sided sign-free | open (B130); VK saving |
| Stepanov's auxiliary vanishing at rational points | fixed-point auxiliary of log length `ψ(N)`; exactness only on the torsion | exact count = Chebyshev |
| Bombieri's twist excludes real eigenvalues | ζ has no real zero in the strip | available |
| Base change: counts over `𝔽_{q^{kn}}` | traces at the degrees `n^k`; trace zeta | receiver |
| Self-improvement by power sums | gap iteration, Laplace rate theorem, window theorem, infinite Turán | available |
| Deligne's tensor-power trick | `A_k=o(k)`; constituents are Tate twists | uniformity is RH |
| Deligne's family: generic purity + specialization | gauge torus: generic purity, big monodromy, equidistribution of ζ's vertical family | ζ is the jump fibre; specialization missing (B142) |
| `H²_c` controls the top pole | the whole tensor power is geometrically constant | missing |
| FE pins modes to the circle | FE = Born rule; Hecke isometry of `Q` | quadratic half holds |
| Count half: the integral defect is a point count | `Q` as Tate limit of a count on one ray per prime | open (B87); `Q` not integer-valued |
| Finite-dimensional `H¹` with Frobenius | no finitely generated ℤ-lattice stable under three prime Frobenii; Meyer flow with Lefschetz trace | infinite rank |
| Archimedean and finite fibres | `ℍ³` Green function at `s=½`; trees at the Ramanujan point; discrete adelic quotient | available off the diagonal |
| Middle cohomology of the orientation cover vanishes (`qⁿ` points) | cover over ℤ with centred count `M(N)`, weight `≥½` | weight `½` is RH |

## 3. Which routes are the same problem

### 3.1 Same problem by source identity or proved transport
| Family | Routes | Identity | Anchor |
|---|---|---|---|
| **Prime-degree inequality** | ACS (Frobenius graphs), SRT (prime two-bumps), WL (prime-window count), HF and RW through Σ141, ALST (Stepanov), SOSZ count door, CDGeo two-sided bound | `c_B(log p)=A(p)−P(p)` and `Re W(B+τ_{log p}B)=2c_B(0)+2c_B(log p)`: one quantity per prime is the Weil test, the Hasse–Weil defect, the prime-window error, the Tate limit on the effective ray and, two-sided, the sign-free trace; all localize to `√T` windows | SOSZ, CDGeo [L] |
| Window scalar | RW, EWU, OWU, ACT, CHMD (odd), TT (odd), SZ, RN energy, ACS atomic, LI on primitives, HF, SRT, AIP critical branches | one form on one window; sectors exact; first variation = Weil energy; critical thresholds are the window threshold plus polar payment plus ground-state orthogonality | SWC, SZ, ALG, ACS, CACT, AHD [L] |
| Two-site / Frobenius graphs | GWZ two-site, AOG spline orbit, SOSZ Frobenius pairs and prime degrees, SRT two-bump | one rank-two test per scale | GWZ, AOG, SOSZ [L] |
| Exceptional atoms | ZCG landing, finite-stratum and linear branches, LA finite support, HF/HKT index, SC undamped, WL thick runs, ACS sampling branch, JAS shell, BAG, RW polar ground energy | RH = ZAL ∧ B13 ∧ Landing; AAL = B13 ∧ Landing ∧ DH; every finite-stratum receiver is a B13 face, every ZAL-to-finite receiver a landing face | ZCG, ELT, AKLT, IWT [L] |
| Log-mean | WD near-line, CTF budgets, ZCG depth law, RW onset, AIF `I` at infinity, BHR bulk log-mean | eight-way equivalence; depth density | CDG, AIF, ASH [L] |
| Mertens level | MC, WL, AAD, AE, CTF defect, PBM, RB, Redheffer, RAC parity, Farey, nerve, core, prime-vertex indices, gluing charge, orientation cover | rate ⇔ level; `det=M(N)=−χ̃=1−Σ index` = centred cover count | AAD, RAC, RHTower, ADT, HWV, HHAC, CTH, RIAC, HAT [L] |
| Inner mass | CTF BSY, AIF budgets and dilation, MZF `N(ρ)`, KL index | one Blaschke product | AIF [L] |
| Horizon | PM, BHR, ASH, RIT, CTH horocycle, Narain, AHMH seeds and cavity | one scattering matrix; every observable reads `ρ/2`; one cavity function sees all of them | RIT, BHR, ASH, CTH, AHMH [L] |
| Abscissa / transport / dial | BAG, WL thick runs, JAS shell, SC undamped, ACS sampling branch, ZCG one-off, linear and tower layers, AKLT towers, AAD transport, TAPO, RW polar ground energy, IWT metric recurrence, EFT and ELT finite-layer world | ¬AAL as one rigid object; AAL = zero transport = tail transport; countermodels classified; filters read the exceptional divisor | ZCG, AKLT, AAD, TAPO, APD, IWT, SOSZ, EFT, ELT [L] |
| Count and diagonal | ACS, HF, PM probes, CWS heights, LST Künneth, CTH Tate limit, SOSZ half-products and ray counts, RIAC arithmetic counts, HAT carriers and Gram coupling, standard forms | one quadratic form on integer probes; count law = Born rule + positivity; off-diagonal = adelic Green pairing; diagonal = Gram defect sign | AE, ASH, CWS, ACS, CTH, SOSZ, HAT [L] |
| Tensor and family | ACS tensor branch, SOSZ tensor powers, AK weight families, AWT gauge family | `A_k=o(k)` ⇔ RH; constituents are Tate twists; ζ is the jump fibre of the family | SOSZ, AK, AWT [L] |
| Tail | BAG returns, TH certificates, PTT Ξ-current, AIF dilation | zeros of ζ = zeros of the Euler tail | TAPO, PTT, AIF [L] |
| Aliases | HJ→PA; BSH→CDC; FEL BSY→CTF | definitions | frontier |

### 3.2 Same endpoint, distinct mechanism
| Group | Routes | Common form only |
|---|---|---|
| Laguerre | TH, PTR, ZCG, LA, GTA, XN, HCF, PA | horizontal-line Laguerre form in a limit |
| Scheduled sums | FU, CFC, RP, LI | one-sided history floors |
| Source completions | SEC, CDC, PCS; APF, EWJ, RFHM, WBF | a source plus one vanishing at zero parameters |
| Integer gates | TG, WD charge, SC index | an integer that small norm kills |
| Dark-range inputs | B46, B57, B89, B96, B97, B121, B137 | Dirichlet polynomials longer than the height; breadth of returns; a depth floor uniform in the number of primes |
| Exceptional-coordinate inputs | B13, B83, B110, B111, B112, B116, B126, B127, B128, B134, B138, B141 | a Dirichlet-series statement with Euler product and FE seeing low and high zeros together, not implied by the explicit formula, pointwise rather than in law |
| Critical-line sizes | TH head (B102), ZCG FE-pair flatness (B76), Lindelöf-type bounds | values of ζ on `Re s=½` near its zeros |
| Diagonal sign | B87, B88, B114, B133 | a positive object whose limit is Weil's kernel including the diagonal |
| Deformation families | ZCG heat, linear law on shifts, PTR cosine, AWT gauge family | uniformity of a law as the deformation parameter tends to the special point |

### 3.3 Classes

**Σ-classes (window form and its readings).**
| Class | Observable / endpoint | Routes | Identity or scoped receiver |
|---|---|---|---|
| C1 Window form | `Q≥0` on every window | HF, SRT, AIP, ACT, ACS, RW, EWU, OWU | window ⇔ threshold ⇔ Hardy admissibility [L] |
| C2 Glued state | `κ(φ_c)−1` | SC, AKG | Grams are compressions [L] |
| C4 Sectors | odd, even sign | CHMD, TT, OWU, EWU, ACT | exact format [L] |
| C5 Laguerre / continuation | Laguerre form on lines | TH, PTR, ZCG, LA, GTA, XN, HCF, PA | distinct receivers [L] |
| C6 Scheduled prime sums | history floor | FU, CFC, RP, LI | receivers retain their schedules [L] |
| C12 Hodge–Lefschetz | HL, zero modes, top stratum | HF, ACS, RIT, EHT, TG, DZG, GWZ, HWV | zero modes radical [L] |
| C15 Canonical flow | `r,q,Ψ` | CWS, WTZ, DZG, GWZ, CSTW, SWC, CHT, RW, SZ | restoring bound [L] |
| C16 Blind cone | `𝒜(c)`, blind tests | PBAP, FADF, CHT | pinning, exact null test [L] |
| C19 Two-site band / Frobenius graphs | `\|𝒞_m(f)\|≤W(f)`; `c_B(log p)≥−K` | GWZ, AOG, SWC, SRT, SOSZ | one Weil test per prime [L] |
| C22 Jet moments | Hankel, Toeplitz, jets | SWC, TH, LA, GWZ, PA, HCF | own sign per sequence [L] |
| C25–C27 Onset, Hardy, contact | `a*(ζ)`, `1∈ℋ(c)`, `Ψ` bounded | every window route | closed interval; criticality; local boundedness [L] |
| C30 Li ladders | `λ_n≥0` | LI, ACS, HF | Toeplitz ladder [L] |
| C36 Prime-blind duality | Gamma, pole, `log n` | PBAP, EWU, OWU, CHT | RH ⇔ blind positivity [L] |
| C39 Passive medium | echo train of `Λ(n)/√n` | RW, PA, PTR, CHMD, SC | Schur band [L] |
| C44 Torus and columns | phases, insertion cone | TH, ZCG, FFP | locking, columns add [L] |
| C48 Sign plane | `Ω(a,X)` | RW, ACS, SRT, ZCG, WD | typical-height sign [L] |
| C49 Critical compactness | Γ-liminf, Gårding, thresholds | HF, SRT, AIP | `R_c=R_polar≤W` [L] |

**Π-classes (precision, production, prime side).**
| Class | Observable / endpoint | Routes | Identity or scoped receiver |
|---|---|---|---|
| C7 One-point precision | `ψ−x`, `M`, cyclotomic mode, Gaussian ceiling | WL, MC, PBM, RB, JAS, CTF, HCF | band ⇔ classical criteria [L] |
| C11 Local zero location | depth, near-line density, inner caps | WD, census, HEF, SRT, MZF | eight forms [L] |
| C28 Finite free | stability of `R_d`; `N_d` | FFP, LA, TH | `sup_dN_d` off-line multiplicity [L] |
| C32 Long moments | `∫\|ζM\|²` | APR, CDG, WD, MZF; MC, CTF, WL | slope rigid; collision counts of order `X²` [L] |
| C34 Width axis | zero-free parameter | §2.4 | interior is quasi-RH |
| C45 Production | Nair lattice, stencils, Stepanov over ℤ | WL, MC; AE, AKLT, AAD, AGT | rate = Mertens level [L] |
| C54 Cut kernel | power-law solutions | WL, MC, RAC, AAD, CTF | kernel = zeros [L] |
| C55 Ledgers and parity | degree-`k` ledgers, exact identity | WL, MC, RAC, AAD, AGT | parity is size [L] |
| C56 Prime torus at finite time | boxes, savings, rounded orbit | BAG, TH, SRT, ZCG, PTT | absolute savings [L] |
| C63 First return | brackets, precision law, heavy returns | BAG, SRT, TH, PTT, TAPO | constant precision open [L] |
| C64 Conditional tail | head–tail decoupling | BAG, TH, WD, TAPO, SPAL | below the Kronecker scale [L] |
| C65 Farey and horocycle | Farey discrepancy, horocycle mean | MC, PM, HWV, CTH | Franel–Landau, Zagier [L] |
| C68 Topology of the prime complex | indices, persistence, orientation cover | MC, HF, ACS; ESG, HHAC, HWV, ADT, RIAC, HAT | `Σ index=1−M(N)`; cover weight `½` ⇔ RH [L] |
| C72 Exceptional rank | Turán windows, rank barrier, infinite power sums | WL, ZCG, ACS, JAS, IWT, ELT | thick sets self-improve; maximal term detected [L] |
| C73 Tower elimination | well-founded towers, thick crude count | WL, ZCG, ACS, IWT | thick crude count ⇒ AAL [L] |
| C74 Frobenius substitute | freezing; Adams operation on the torsion | BAG, PTT, IWT, ALST | exact only on the torsion; orbit symmetries are dilations [L] |
| C79 Prime-degree sampling | one- and two-sided bounds at gap sets | ACS, SRT, WL, ZCG, IWT; SOSZ | RH at the primes [L] |
| C81 Lefschetz–Stepanov over ℤ | Adams Frobenius, torsion auxiliaries | ACS, BAG, WL; ALST | exact count = Chebyshev [L] |
| C84 Returns and transcendence | depth law, breadth cap, reciprocity, VK breadth | BAG, TH, SRT; TTPO, ALST, CDGeo | breadth to VK [L] |
| C85 Sign-free decision | two-sided bound at a gap set | ACS, SRT, WL; CDGeo | RH and width without positivity [L] |
| C87 Sample boundary | which degree sets decide | ACS, SRT, WL, HF, ZCG, IWT; SOSZ | compactness, not density or gaps [L] |
| C89 Scale locality | `√T` windows, positive deletion, finite-spectrum oscillation, separated windows, log-square leakage | ACS, SRT, WL, ZCG, HF; SOSZ | RH on sparse local windows [L] |
| C90 Bohr-dense samples | lower and upper side; width law; runs of integers | ACS, SRT, ZCG; SOSZ | attained tops decided [L] |
| C94 Gauge family | big monodromy, Gaussian Frobenius, vertical equidistribution, jump at ζ | ACS, HF, SC; AWT, AK | generic purity free; specialization missing [L] |
| C96 Collective returns | rank depth, hereditary rank, weighted return counts | BAG, PTT, TH; CDGeo, TTPO | counts beyond the depth floor [L] |

**Γ-classes (selection, reflection, transport, count, diagonal).**
| Class | Observable / endpoint | Routes | Identity or scoped receiver |
|---|---|---|---|
| C3 Window integer | collision charge, glued index, multiplicity | WD, SC, TG, HEF, AIF | integrality supplies no subunit norm [L] |
| C8 Selection / recurrence | trivial gauge; self-return | MC, BAG | target mass open [L] |
| C9 Realization | Krein defect, renewal nodes, Lee–Yang, cosine, standard forms | RN, PM, PTR; W1C | producers missing [L] |
| C10 Source completion | factorial energy, repair, co-shift | SEC, CDC, PCS; APF, EWJ, RFHM, WBF | zero-parameter bounds open [L] |
| C13 Sections and counts | source cone, RR | ACS, HF; IRK; WTZ, LST, KPA | Bézout ⇔ RH [L] |
| C14 Reflection | Rosati, Lewis, Krein, dispersion | PM, HF; W1C | coefficient identity [L] |
| C20 Selberg rigidity | Euler discrepancy, degree | SEL; ACS, HF | degree one classified [L] |
| C21 Camera | Weil-image readout | ZCG, SRT, MZF | conditional on isolation [L] |
| C31 Repulsion | separation of zeros | ADO, ZCG, LA | amplifier [L] |
| C37 Inner factor | Blaschke product | CTF, MZF, AKLT, GWZ, CSTW, AIF | identity, Carleson [L] |
| C38 Eisenstein carrier | `E*(z,½+ib)` | TH, PM, BHR, CTH, ASH; W1C | edge positivity shared [L] |
| C41 Parabolic flow | gap laws; heat family | NGF, ZCG | blind to `t=0`; Ki–Kim–Lee does not land [L] |
| C43 Abscissa split and dial | ZAL, AAL, linear laws | BAG, JAS, SC, WL, ZCG, RW, IWT | strict dial; rigid ¬AAL [L] |
| C51 Horizon scattering | ringdown, horocycles, Farey, Lax–Phillips, Narain, seeds, cavity | PM, BHR, ASH, CTH, AHMH | complete and sharp cavity receiver [L] |
| C52 Beurling isolation | FE defect, count distance | APD, SEL, BAG, SPAL | three isolation metrics [L] |
| C53 Count and height | naive height, Tate limit, point counts, ray counts | ACS, HF, PM, CWS, AE, ASH, CTH, SOSZ, RIAC | one ray per prime; `Q` not integer-valued [L] |
| C58 Hull | fibres over the torus | BAG, ZCG, PTT, AIF | natural boundary `½`; random fibres zero-free [L] |
| C59 Krein law | universal decay, flux, reflection Krein form | PM, BHR, ASH, ACS, AHMH | sign ⇔ RH [L] |
| C60 Fakes of the black hole | graph black holes, genus two | PM, ASH, CTH; W1C | damping not a wave law [L] |
| C62 Transport | return count, tail at a zero, partial returns | BAG, ZCG, AAD, RAC, TAPO, HTG | right discs; `η>0` abundant [L] |
| C66 Countermodel boundary | finite top layers, approaching remainders | BAG, ZCG, JAS, SC, APD, IWT, SOSZ | firewall [L] |
| C67 Born rule | partner law, damping, standard forms | PM, ACS, CTH, ASH | quadratic half = FE [L] |
| C69 Thermal averaging | primon gas | SEL/Primon | real points `>1` [L] |
| C70 Relocation positivity | first-gap negativity | APD; ZCG, BAG | rational surgery detected [L] |
| C71 Two-scale law | asymptotic and local-below properties | every exceptional-coordinate route | decides no atom [L] |
| C75 Half-products | 𝔽₁-zonotope, `ℙ¹_ℤ` torsion, `ℍ³` and tree fibres | ACS, HF, PM; SOSZ, HAT, AE | adelic Green pairing off the diagonal [L] |
| C76 Critical weight | damping versus renormalization | ACS, HF, PM; IWT, HHAC, RIAC, HAT | renormalization signless; atoms give the discriminant [L] |
| C77 Euler + FE calibration | finite-rank purity; FE rigidity | ZCG, BAG, APD, SEL, EFT | identifies ζ [L] |
| C80 Finite-layer identities | prime current, rough variance, height reflection | BAG, ZCG; EFT | height-preserving [L] |
| C82 Cavity receivers | seeds, Maass and Hecke pairs, Baire | PM; AHMH, BHR | rate open [L] |
| C83 Heat divisor budgets | elapsed-depth actions | ZCG, LA, WD; AES | finiteness of budgets open [L] |
| C86 Exceptional current | corrected current at exponential damping | BAG, ZCG; ELT, EFT | top-layer wave [L] |
| C88 Locking at mass balance | scalar locking on smoothed packets | ACS, HF, PM; HAT, SOSZ | converges iff mass balance [L] |
| C91 Exceptional atoms | ZAL, B13, Landing, DH; Hadamard threshold | ZCG, BAG, LA, HF, SC, IWT; ELT | RH = ZAL ∧ B13 ∧ Landing [L] |
| C92 Damping filters | local and damping filters, contracting prime filters, Euler-region bounds | ZCG, BAG; ELT | detection and Euler decay ranges disjoint [L] |
| C93 Classical repulsion | Deuring–Heilbronn for quadratic `L(s,χ)`, no Siegel regime | ZCG, BAG; ELT | mechanism absent for ζ [L] |
| C95 Gram coupling and adelic quotient | ordered Gram coordinates; discrete split-torus quotient; prime unit; twisted fibres | ACS, HF, PM; HAT | finite limits; points carried; Green/Robin open [L] |
| C97 Witt / Λ / Lefschetz | Witt Frobenius, Galois descent, distributional Lefschetz, Meyer flow, λ-ring effectivity | HF, ACS, CDC; Deninger | explicit formula = Lefschetz trace; no finitely generated Frobenius-stable lattice [L] |

**Further classes.**
| Class | Observable / endpoint | Routes | Identity or scoped receiver |
|---|---|---|---|
| C17 Dimension zero | domination of point counts | ATD, DZG | bare domination ⇔ `Q≥0` [L] |
| C18 Angle dictionary | Hurwitz forms | AHD, ACS, LST, GWZ | `𝔽_q` angle = frequency [L] |
| C23 Density apertures | completeness radius | ZCG | face of C21 [L] |
| C24 Hermite–Biehler phase | dominant `A` | ZCG, FFP, PTR, PM | one shift axis [L/D] |
| C29 Hecke graphs | finite rational graphs | WTZ, CWS | templates below `27/5` [L] |
| C33 Finite-degree detectors | Hausdorff, heat grid, slice, Jensen | PA, HCF, LA, FFP | no fixed family decides [L] |
| C35 Finite rungs | fixed window, rank, degree, ratio | §2.5 | verification decides each, no atom [L] |
| C40 Near-line clusters | comparably deep zeros | MZF, NGF, WVL | isolated rate 2; cluster wall open [L] |
| C42 Log-mean | `T⁻¹∫log\|ζ\|` | WD, CTF, RW, ZCG, MC, PM | equivalences; `O(T)` depth [L] |
| C46 Characters and weights | Young projections, global trace | ACS, HF | positivity through rank 4 [L] |
| C47 Bohr space | far dipoles, recurrence | RW, HF, BAG | profile decomposition [L] |
| C50 Forced mollifier | near-extremal rigidity, Abel budgets | CTF, WD, AIF | Szegő ratio [L] |
| C57 Kernel-valued certificates | Agler, Euler, head–tail | TH, RW, PTT, PM | tail-good [L] |
| C61 Metaplectic descent | cubic Gauss coefficient | MC, MMD | nonzero residue at `4/3`; theta identification open [L] |
| C78 Finite-field counts | resultant, radial, orbit and orientation counts | ACS, MC, RIAC, SOSZ | counts before the form; Möbius as point defect [L] |

C1, C4, C16, C19, C25, C48, C49, C79, C85, C89 and C90 are exact window-form dictionaries; C19, C79, C85 and C89 are the minimal one (one test per prime, on sparse local windows). C5, C28 and C33 require all-root or all-degree control. C11, C32, C42 and C48 are asymptotic: by C71 they reach no atom. C45, C34, C65 and C68 are one axis (the Mertens level). C56, C63, C64, C74, C84 and C96 are one programme on the dark range. C43, C52, C66, C70–C73, C77, C80, C86, C91–C93 are one programme on the exceptional coordinate. C51, C53, C59, C60, C67, C75, C76, C88, C95 and C97 are one programme on the count and the diagonal. C94 is the family face of the tensor trick.

### 3.4 Constructive transfers and their limits

| Sources / routes | Established transfer | Input not transported |
|---|---|---|
| RW/HF/SRT/AIP/ACS | exact receivers for form, band and source energy [L] | all-aperture sign |
| CACT/AHD→RW | `R_c=R_polar≤R_prim=R_high=W`; charged compactness [L] | the window sign; polar payment at every ratio |
| RW→count | cone points obey PNT `5/6` on the window's range [L] | windows of every length |
| SOSZ→width | growth exponent of either side at the primes, at gap sets and at `√T` windows = width [L] | a crude bound at the primes |
| SOSZ→WL/ALST | the Stepanov bound is the prime-window count `P≤A+K` [L] | the count itself |
| SOSZ ScaleLocality→ACS/SRT/WL/HF | RH from the primes of sparse `√T` windows; positive deletion [L] | the bound on those windows |
| SOSZ→ZCG/IWT/BAG | sampling and Bohr-dense sets ⇒ AAL; with ZAL ⇒ RH [L] | the bound on a sampling set; ZAL |
| CDGeo→ACS/SRT/WL | two-sided bound at the primes ⇔ RH, sign-free [L] | the two-sided bound |
| ZCG/ELT atoms→LA/HF/HKT/SC | finite-stratum receivers = B13 faces; ZAL-to-finite receivers = landing faces [L] | ZAL, B13, landing for ζ |
| ELT→BAG/ZCG | ¬AAL ⇒ filters read the exceptional divisor; one ordinate diverges [L] | an inequality the explicit formula does not imply |
| ELT DH→ZCG | classical repulsion for quadratic `L(s,χ)` [L] | a Siegel regime for ζ (absent) |
| AWT→ACS/HF | generic purity, Gaussian law, vertical equidistribution [L] | specialization at the jump fibre |
| HAT→CTH/ACS/PM | Gram coupling: finite limits on every packet; discrete adelic quotient [L] | the sign of the Gram defect; Green/Robin realization |
| ACS→RW/SRT | typical-height sign with Gaussian tails [L] | fixed `λ`; exceptional heights |
| TH↔ζ on the line | adaptive head leading term `=\|ζ(½+ib)\|²` [L] | sign near critical zeros |
| BHR/AHMH cavity→PM | rate `y^α` of one cavity energy forces `Re ρ≤2−2α` [L] | the rate |
| ASH Narain→PM | `¾` ⇒ RH; remainder VK [L] | any rate past VK |
| CTH standard forms→PM | RH ⇔ internal standard form realizing `Q` [L] | a realization outside the excluded classes |
| IWT→WL/ZCG/ACS | thick crude count ⇒ AAL; RH ⇔ ZAL ∧ thick `√X` [L] | the thick crude count; ZAL |
| ZCG heat→B13 inputs | family-uniform laws are RH; the Dirichlet series selects `τ=0` [L] | an input that uses the selection at the zeros |
| BAG/AAD/TAPO/CDGeo | transport on right discs; tail transport; partial returns; heavy-return counts [L] | an exact event at a zero |
| IWT/ALST forced vanishing→BAG/ACS | Rouché copies cost the trivial separation bound; integrality only on the torsion [L] | freezing beyond the cap |
| AAD↔MC | rate ⇔ Mertens level [L] | a level past VK |
| RAC↔CTF | finite-energy cut-kernel mass annihilation ⇒ RH [L] | the annihilation |
| RIAC/HAT finite fields→ℤ | orientation cover over `𝔽_q` and over ℤ [L] | weight `½`; a bounded-index correspondence |
| APD firewall→ZCG/BAG | positive classes, continuation, reflection and approaching remainders carry layers [L] | intrinsic layers of ζ |
| RHTower/EFT Euler FE→ZCG | Euler product + FE force purity at finite rank and the rational primes with integrable defect [L] | transport |
| Deninger→HF/ACS | explicit formula = Lefschetz trace of the Meyer flow [L] | positivity (Hodge index) on the flow's cohomology |
| TTPO→BAG/PTT | depth of returns polynomial in `1/δ`; breadth cap; VK breadth; reciprocity [L] | breadth past VK; an FE-dependent step |

## 4. U-Σ — the sign

Core problem: `1∈ℋ(c)` for every `c`. In cone form, some weight on every window; in causal form, an outer predictor; in flow form, `Ψ` locally bounded; in plane form, `Ω≥0`; in pair form, Hasse–Weil along the spline orbit; in **minimal form, one Weil test per prime, on sparse local windows**; in matrix form, every critical threshold `=⊤`, which is the window threshold plus polar payment, and under ¬RH the exclusion of a polar-orthogonal half-line ground state at finite `W`; in Laguerre form, horizontal-line positivity of Ξ; in theta form, the sign of `|ζ(½+ib)|²` plus second-order terms near the zeros. One scalar: `a*(ζ)`.

| Face | Routes / programmes | Reduction |
|---|---|---|
| Complete atomic matrix | HF, SRT, AIP, ACT, CACT, CSAR, ACPL, RAPT, TM, ADT, AHD | `R_c=R_polar=R_halfline≤W`; polar payment below `W` and ground-state orthogonality open |
| Ground energy, chain, cone | RW, EWU, OWU, CSTW, CHT | `a*(ζ)`; `Ψ`; `λ*` |
| Causal chain | RW, GWZ, AIF | outer predictors; Schur bands |
| Pair tests and Frobenius graphs | GWZ, AOG, SOSZ, SRT, ACS | one Weil test per prime on sparse `√T` windows |
| Local onset | RW, ACS, SRT, AIF | typical-height sign; size curve |
| Sectors, ground states | CHMD, ACT, OWU, EWU, SWC, FADF | two-sector format |
| Moment problems | SWC, TH, LA, PA, HCF | Stieltjes, Hamburger |
| Theta spectrum | TH, CAF, TCS, AIF, PTT | head = `\|ζ(½+ib)\|²` |
| Heat, cosine, Jensen | ZCG, PTR, LA, NGF, FFP | small time at all heights |
| Glued state | SC, AKG | Beurling-schedule sign |
| Window tower | CWS, WTZ, DZG, GWZ, SWC | kick admission; two sites |
| Edge, zero modes | EHT, HWV, DZG, GWZ | no zero mode |
| Effectivity, RR, λ-rings | ACS, LST, RIT, HF, KPA | Bézout is sign; Hecke/Adams-stable cones force the defect floor |
| Li, Suzuki, scheduled sums, charge, renewal | LI, ALG, SZ, FU, CFC, RP, GTA, TG, RN | one-sided floors and gates |
| Adelic Green pairing and diagonal | HHAC, AE, SOSZ, RIAC, HAT | pole − `ℍ³` Green − tree Green; Gram defect; adelic quotient |

## 5. U-Π — precision and production

Core problem: square-root precision of one smoothed prime count; in **minimal form, the Stepanov bound on a decisive sample of prime degrees, local in scale**; in tower form, a square-root prime deviation on a thick set of scales together with ZAL; in Deligne form, prime moments of the traces uniform in the tensor power, which a family must supply and the gauge family cannot because ζ is its jump fibre. Production, Farey discrepancy, the nerve, the barcode, the prime-vertex indices, the gluing charge and the orientation cover read the Mertens level. The dark range is where every sub-RH precision question sits: returns of the primes are counted collectively only beyond a depth floor that grows with the number of primes.

| Face | Routes / programmes | Reduction |
|---|---|---|
| Reflection-pair coupling | SWC, GWZ, CSTW, AOG | collar Hankel − smoothed count |
| Classical one-sided counts | WL, PBM, RB, JAS, CTF, HCF | RH-level equivalence; Gaussian ceiling |
| Thick tower counts and the dial | WL, ZCG, ACS, IWT | thick crude count ⇒ AAL; + ZAL ⇔ RH |
| Prime-degree crude bounds | ACS, SOSZ, WL, CDGeo | Stepanov bound = prime count; local at `√T` windows; two-sided sign-free; VK saving |
| Tensor powers and families | ACS, SOSZ, AK, AWT | `A_k=o(k)`; Tate-twist constituents; jump at ζ |
| Cyclotomic mode, gauge torus | MC, CAF, AGT | exponent `½` at the trivial point |
| Integer producers | WL, AKLT, ASRP, AE, AAD, RAC, ALST | rate = Mertens level; exact Stepanov over ℤ = Chebyshev |
| Frobenius substitute | IWT, PTT, TAPO, ALST | precision cap; exactness only on the torsion; orbit symmetries are dilations |
| Möbius, nerve, core, Farey, cover, descent | MC, HWV, ADT, HHAC, ESG, RIAC, HAT, CTH, MMD | half-power cancellation; weight of the orientation cover |
| Short-sum barrier, first return | every route; BAG, PTT, TAPO, TTPO, CDGeo | proportional saving ⇔ no early heavy return; counts beyond the depth floor |
| Near-line density and long moments | WD, CDG, MZF, AIF, APR, CTF | log-mean; necessary length; collision counts |
| Sharp horizon sources | CTH | Möbius × circle remainder, beyond RH |

## 6. U-Γ — selection, reflection and transport

Core problem: source-defined arithmetic control of `ρ↦1−ρ̄` and of vertical transport; in atom form, ZAL ∧ B13 ∧ Landing, each needing the FE and the Euler product together, each pointwise rather than in law; in count form, the count half of a Born rule on one ray per prime; in diagonal form, the sign of the Gram defect, with a Green/Robin realization on the adelic quotient open; in horizon form, one rate or one reflection Krein sign of a complete cavity receiver. FE + Euler product with integrable defect identify ζ, so every such input concerns the exact identities of ζ; the exact identities are consistent, so the input must be an inequality they do not imply.

| Face | Routes / programmes | Status |
|---|---|---|
| Recurrence, gauge, transport | MC, AGT, BAG, AAD, RAC, PTT, TAPO, CDGeo | transport closed on right discs; tail transport; exact events open |
| Abscissa split, atoms and dial | BAG, JAS, SC, WL, AKLT, ZCG, RW, IWT, SOSZ, ELT | three atoms; landing with eleven forms; DH classified on models; strict dial |
| One-off and FE models | APD, SPAL, RAC, AIF, ACP, IWT | firewall incl. one-offs across the line and approaching remainders; ζ isolated in every FE-defect class |
| Euler + FE calibration | RHTower, APD, SEL, EFT | finite-rank purity; complete FE rigidity |
| Time-zero selection | ZCG, NGF, AES | parabolic tools blind; Ki–Kim–Lee does not land |
| Exceptional layers | ELT, EFT, ZCG, BAG | filters read the divisor; Euler-region bound above abscissa 1 |
| Horizon and count | PM, BHR, ASH, AHMH, CTH; W1C, ACP | Krein law; Born rule; Tate limit; complete and sharp cavity receiver; reflection Krein form |
| Surface of Spec ℤ | SOSZ, HAT, AE, RIAC | adelic Green pairing; Gram coupling; discrete adelic quotient; diagonal missing |
| Witt / Λ / Lefschetz | Deninger, ACS | Lefschetz = explicit formula; no finite integral cohomology |
| Function-field calibration | many | AAL free by periodicity; ZAL = purity; count law at every genus |

## 7. Cross-family seams

| Seam | Statement | Routes |
|---|---|---|
| Σ ∩ Π: reflection pairs | `W(f±f∘R)=2W(f)±2𝒞_m(f)` | SWC, GWZ, CSTW, AOG, WL [L] |
| Σ ∩ Π: Hardy form | `W=H−P` | FADF [L] |
| Σ ∩ Π: cone counts | window positivity ⇒ PNT `5/6` on its range | CHT [L] |
| Σ ∩ Π: aperture exchange | window positivity ⇒ depth-`¼` zero-free region | AHD [L] |
| Σ ∩ Π: theta head | head = `\|ζ(½+ib)\|²` | CAF, TCS, AHD [L] |
| Σ ∩ Π: spline orbit and prime degrees | orbit growth = zero width; crude bound at the primes = width; local at `√T` windows | AOG, SOSZ [L] |
| Σ ∩ Π ∩ Γ: one test per prime | `Re W(B+τ_{log p}B)=2c_B(0)+2c_B(log p)`, `c_B(log p)=A(p)−P(p)`, the defect of `Γ_1+Γ_p` | SOSZ [L] |
| Σ ∩ Γ: integer probes and Tate limit | Weil form on the Hecke lattice = Krein square; RH ⇔ Tate limit of a count | ASH, CTH [L] |
| Σ ∩ Γ: archimedean fibre | Weil's archimedean + pole weight `=4πG_{1/2}−4cosh(u/2)` on `ℍ³` | SOSZ [L] |
| Σ ∩ Γ: adelic Green formula and Gram coupling | off-diagonal = pole − Green functions of `ℍ³` and of the trees; coupled limits `Weil(f)+Δ_g` | HAT [L] |
| Σ ∩ Γ: λ-ring effectivity | Hecke/Adams-stable cones force the defect floor | ACS [L] |
| Σ ∩ Γ: cavity | horocycle rate of one cavity energy = zero-free region; reflection Krein form PSD ⇔ RH | AHMH [L] |
| Σ ∩ Γ: index and landing | finite Krein–Langer index ⇔ finite off-line set; ZAL ⇒ finite index is landing | HKT, ELT [L] |
| Π ∩ Γ: prime-side AAL and the dial | ¬AAL is a finite oscillation; thick crude count ⇒ AAL; Bohr-dense bounds ⇒ AAL | ZCG, IWT, SOSZ [L] |
| Π ∩ Γ: tail | zeros of ζ = zeros of every Euler tail; AAL = tail transport | TAPO [L] |
| Π ∩ Γ: returns | weak return = extreme value of `ζ(1+it)`; reciprocity of returns with the zeros near the height; collective counts | TAPO, TTPO, CDGeo [L] |
| Π ∩ Γ: horocycle and Farey | horocycle rate = Farey count rate = zero-free region | BHR, CTH [L] |
| Π ∩ Γ: families | tensor powers are Tate twists; ζ is the jump fibre of the gauge family | AWT [L] |
| Π ∩ Γ: exceptional current | ¬AAL ⇒ filters read each top mode; Euler-region bound above abscissa 1 | ELT [L] |
| Π ∩ Γ: exactness | integrality exact only on the torsion; orbit symmetries are dilations; no finitely generated Frobenius-stable lattice of zero modes | ALST, Deninger [L] |
| Σ ∩ Π: gluing and topology | Redheffer = reduced Euler characteristic; prime-vertex localization `1−M(N)` | HWV, ADT, HHAC, ESG, RIAC [L] |

## 8. Route → core map

| Route | Core | Halves / atoms | Classes | Face |
|---|---|---|---|---|
| WL | Π (Σ) | both | C7, C19, C32, C43, C45, C54, C55, C72, C73, C79, C89 | integer lag; prime-window count on local windows; thick tower count |
| RW, EWU, OWU | Σ | both | C1, C4, C15, C16, C19, C22, C25–C27, C39, C43, C47, C48 | `a*(ζ)`; `Ψ`; causal; polar ground energy |
| FU, CFC, RP | Σ | both | C6 | full-history bounds |
| SZ | Σ | both | C15, C27 | completed Abel residual |
| LI | Σ (Π) | both | C30, C6 | Cayley–Li sign |
| PA (HJ) | Σ (Π) | both | C5, C22, C39 | rows below the explicit shift |
| TH | Σ (Γ) | both | C5, C22, C38, C44, C56, C64 | head = `\|ζ(½+ib)\|²` |
| HCF | Σ (Π) | both | C5, C7, C22 | two grids; Gaussian ceiling |
| LA | Σ | ZAL side; B13 and landing for finite support | C5, C22, C28, C91 | outer roots |
| GTA, XN | Σ | both | C5 | small charge; covering discs |
| MC | Π (Γ) | both | C7, C8, C12, C32, C45, C54, C55, C61, C65, C68 | trivial gauge; Farey; topology |
| TT | Π (Σ) | both | C4 | endpoint upper bound |
| TG | Π, Σ | both | C3, C12 | subunit trace norm |
| HF | Σ (Π, Γ) | both | C1, C12–C15, C25, C49, C53, C75, C76, C79, C95, C97 | polar payment; one test per prime; count; diagonal; adelic quotient |
| SRT, AIP, ACT | Σ (Π) | both | C1, C4, C11, C19, C21, C25, C48, C49, C87, C89 | complete matrix = window + polar payment; decisive local samples |
| SC | Σ, Π (Γ) | AAL branch; ZAL | C2, C3, C7, C39, C43, C91 | glued state; undamped cone ⇒ AAL |
| CHMD | Σ | both | C4, C1, C39 | odd sector |
| RN | Σ | both | C9, C1 | joint nodes |
| WD | Π (Σ) | ZAL side | C3, C11, C32, C40, C42 | long moments; log-mean |
| PM | Γ (Σ) | both | C9, C14, C38, C51, C53, C59, C60, C65, C67, C82, C95 | reflection Krein; cavity rate; count; adelic carrier |
| JAS | Π | AAL branch | C7, C19, C43, C72 | moving power; shell positivity |
| CTF | Π | both | C7, C19, C32, C37, C42, C50, C54 | BSY, budgets, cut kernel |
| PBM, RB | Π | both | C7 | abscissa, extremal |
| BAG | Γ | AAL; DH | C8, C43, C52, C56, C58, C62–C64, C66, C70, C71, C74, C80, C84, C86, C91–C93, C96 | target mass; tail transport; returns; exceptional layers |
| ACS | Π (Σ, Γ) | both | C13, C1, C12, C19, C20, C30, C46, C48, C53, C67, C73, C75, C78, C79, C81, C85, C87, C89, C90, C94 | source sign; one side at the prime degrees; local windows; tensor family; count |
| SEC, CDC, PCS | Γ | both | C10, C97 | zero-parameter conditions |
| PTR | Σ (Γ) | both | C9, C5, C24, C39 | Laguerre below VK |
| ZCG | Γ (Σ) | ZAL side; all atoms | C5, C21, C24, C31, C40, C41, C43, C62, C66, C70–C72, C77, C79, C80, C83, C86, C89–C93 | collisions; abscissa laws; atoms; heat budgets; exceptional layers |
| Candidates APF, EWJ, RFHM, WBF | Γ (Π) | — | C10 | missing landing |
| Candidate IRK | Γ (Π) | — | C13 | trace with Chern charge |
| Candidates EGC, FEL, MSC | Σ (Π) | — | C6, C1 | landing; history; Sonin sign |
| Candidate W1C | Σ (Γ) | — | C9, C5, C38 | positive realization |

## 9. What a closing argument must supply

| Needed | Present over ℤ | Missing |
|---|---|---|
| The atoms of the split | RH = ZAL ∧ B13 ∧ Landing; AAL = B13 ∧ Landing ∧ DH; landing in eleven forms; calibrations for each atom [L] | ZAL; B13; Landing — each an FE ∧ Euler, two-scale, pointwise input |
| A crude count | one side (or both, sign-free) at a decisive sample of prime degrees, local in scale; VK saving [L] | the bound itself (B130), at any decisive sample |
| An elimination step | exceptional-rank window theorem, thick sets, infinite Turán, gap iteration, Laplace rate theorem, positive deletion [L] | none: elimination is available |
| A uniformity source | tensor-power trick; gauge family with big monodromy and generic purity [L] | specialization at the jump fibre (B142) |
| A Frobenius substitute | returns freeze smooth polynomials; Adams operation exact on the torsion; dilations the only exact orbit symmetries [L] | a counting argument beyond the precision cap |
| Breadth of returns | VK breadth; collective counts beyond the depth floor [L] | a depth floor uniform in `π(y)` (B97, B137) |
| Sign of the minimal object | one Weil test per prime; two-sided sign-free form [L] | the bound at every prime of the sample |
| Uniformity in length | each length a rung; critical thresholds = window + polar payment [L] | every length; polar payment below `W` |
| Flow | restoring bound; `Ψ`-boundedness ⇔ RH [L] | a bound on `osc Ψ` up to contact |
| Across primes | columns add; Euler coordinates stop at `Re s=1` [L] | amplitude oscillation |
| The critical line | theta head `=\|ζ(½+ib)\|²` [L] | second-order sign at the critical zeros |
| Time selection | family-uniform laws are RH; Ki–Kim–Lee does not land; the Dirichlet series selects `τ=0` [L] | an input that uses the selection at the zeros |
| Exceptional layers | rigid ¬AAL; filters read the divisor; Euler-region bounds above abscissa 1 [L] | an inequality not implied by the explicit formula (B134) |
| Count from geometry | adelic Green formula; Gram coupling with exact defect; discrete adelic quotient; Tate principle; point counts on curves [L] | the sign of the Gram defect (B88); a Green/Robin realization (B133); a count without `Q` on one ray per prime (B87) |
| Reflection | complete and sharp cavity receivers; reflection Krein form; Born rule; standard-form trichotomy [L] | `D_s≥0`; reflection Krein PSD; any horizon exponent past `½` |
| Production | exact integrality; VK rate; kernel; parity identity [L] | a level past VK |
| Topology | localization `Σ index=1−M(N)`; orientation cover of weight `≥½`; Lefschetz trace of the Meyer flow [L] | weight `½`; a bounded-index correspondence; positivity on an infinite-rank cohomology |
| FE as an identity | complete FE rigidity; finite-layer passage laws; FE preserves height [L] | an identity of ζ that moves a zero in height |
