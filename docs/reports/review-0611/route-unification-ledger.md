# Route unification ledger — status quo

The 38 live formulations and 9 candidates are faces of three core problems, **U-Σ** (sign), **U-Π** (precision and production) and **U-Γ** (selection and reflection). Their RH-level endpoints meet at the **arithmetic Hardy inequality** `P≤H` on every window, equivalently the **band** `|𝒞_m(f)|≤W(f)` of a test and its mirror. U-Σ reads it as a form on the window, U-Π on the prime side, U-Γ on the zero side. Transversal to the three, RH splits into two halves: **ZAL**, read by height-local receivers, and **AAL**, read by sparse receivers and recurrence.

Corpus checkpoint: commit `c7d60e30c6` plus the working tree of 2026-11-06. Evidence: `[L]` Lean source; `[S]` marked unfinished or unintegrated in the frontier map, or uncommitted; `[D]` deduction; `[N]` numerical. Scope and source locators: [frontier map](../rh-current-frontier-map.md), [scoped obstructions](../rh-killed-routes.md).

**Equivalence through RH transfers truth, not mechanism.** Only an explicit source identity or a proved transport moves an estimate between routes. A shared endpoint is not a shared proof.

## 0. Unifying statements

- **One split [L].** RH ⇔ ZAL ∧ AAL. ZAL ⇒ qRH. Under AAL, eight RH-level statements collapse into one.
- **One rigid alternative [L/D].** ¬AAL ⇔ finite top and bottom layers above zero-free vertical strips ⇔ `ψ(x)−x` is a finite oscillation at leading power order.
- **One inner factor [S].** On `Re s>½`, `(s−1)ζ(s)/s` has inner factor the Blaschke product of right zeros, with no singular part. RH ⇔ `I(w)=0` at one point. BSY reads its mass at 1. `N(ρ)` reads it at a zero. Krein–Langer index reads its degree. Schur parameters and `r(a)` peel it [D]. Carleson separation is its regularity [D].
- **One second expression [S].** `exp(2I(1))=inf_Q∫|ζ exp Q(φ₁)|²dP₁`. Over `𝔽_q` the opposite sign is Castelnuovo; budgets reach 1 ⇔ unitary.
- **One scalar flow [L].** `L′=q−sinh 2L`, `(log K)′=2 cosh 2L`. Lattice form: `artanh r_{n+1}=artanh(s r_n)−artanh γ_n`. Contact is the only way the tower can fail, and it is local [S]. Kicks of arithmetic size cannot cause it by size [S].
- **One certificate [S].** Causal: outer predictor, Schur band, sum of squares with margins as weights. Allegretto–Piepenbrink is its sign-definite face. Reflection data are free coordinates.
- **One threshold [S].** Slack `s>0` Szegő, `s<0` negative, `s=0` RH. Zero slack is singular spectrum.
- **One passive medium [D from L/S].** Reflectors at `½log n`, first reflector reading `Λ(n)/√n`, archimedean base. Window sign says the echo train is passive. RW, PA, PTR, CHMD and SC read the same requirement.
- **One column law [S].** On independent reflectors, infima add and size is exact; on commensurable reflectors the Fejér train has unbounded room. Positivity lives inside one prime at a time. Over `𝔽_q` there is one column.
- **One base against columns [D from L/S].** `current=2|Ξ|²Re ξ′/ξ`, `Re ξ′/ξ=½log(b/2π)+Re ζ′/ζ+O(1/b)`. TH's torus wall, ZCG's carrier horizon, FFP's forced drift and eventual Hadamard positivity read the Gamma base against Euler columns.
- **One Laguerre form [D].** `Ξ′²−ΞΞ″` and its depth-`a` version: TH current as `a→0`, PTR at `h`, heat collision exclusion on `H_t`, `J`-level Turán for LA. Each route's source is different, and only the limit form is common.
- **One Hermite–Biehler shift axis [D from L].** `ξ(σ+w)e^{cw}` is stable iff zero-free right of `σ` and `c≥0`. At `σ=1` this is FFP's unconditional stability, PTR at `h=½` and the Lagarias–Suzuki line law `c_Y`, `Y>1`.
- **One Eisenstein carrier [L].** TH's spectrum uses the Fourier coefficients of `E*(z,½+ib)`. PM's Mayer carrier is the same family. Edge positivity by Maass–Selberg is shared; off-axis positivity is open on both.
- **One Lax–Phillips model [D].** `φ(s)(s−1)/s` is a Blaschke product over `(1+ρ)/2`. Resonant states are model-space kernels, the Gram law is the Szegő kernel, Hecke acts by the Toeplitz symbol `p^{u}+p^{−u}`, and `V_p` is a kernel norm.
- **One width axis [L/D].** Floor rate `2σ`, damping rate, abscissa `2Θ`, gauge exponent, stability line `σ`, long-moment slope `2w`, Möbius zero abscissa, integrality exponent, PTR `h`, TH `a`, Hecke level `β`, stencil rate. Interior values are zero-free strips. All unconditional savings sit at VK [L].
- **One finite-rung rule [L].** Each fixed window, rank, degree, row and entry follows from verified zeros, with explicit transfers. Limit pencils at a fixed critical ratio are rungs too [D]. Rungs measure verified height.
- **One budget [L].** A floor `−C_σe^{2σr}∫F²` for every `σ>0`, or one constant at all apertures, implies RH.
- **One blind form [L].** RH is prime-blind positivity. Blind energy is `(1/π)∫|𝓜f|²(θ′+1−Re ζ(½+it))`. An exact null blind test exists.
- **One cone [L].** `𝒜(c)` pins every weight to `Λ(n)` within `Ce^{Kn−c/1104}`. RH ⇔ `λ*→0`. The datum of ζ is the critical point of the family.
- **One format [L].** On every window both sectors are represented exactly: neutral signed theta gauge (even), shifted ground state (odd).
- **One head [L].** Dirichlet-shift companions cancel every tail; what remains of a long window is its head of length `log d`.
- **One frustration [L].** Even sector past `log ρ`, in every gauge. Actual odd source whenever a negative prime reflection acts.
- **One end of size [L].** `H<0` by half-width `21/40`; edge law crosses one in `(½log 5,½log 6]`; templates end at spread `27/5`.
- **Positive mimic = window sign [L].** Below contact, sampling atoms are a positive on-line mimic of ζ's image.
- **One-sided signs [L/S].** BSY `I≥0`, PM `D_s≤0`, TT `D+Q/2≥0`, budgets `≥1`: each proved sign has RH as its opposite.
- **Sign → location [L].** Level `a` gives an exponential corridor; `λ·½log T`, `λ>1`, gives `e^{−c log³T}`. Both are receivers.
- **One log-mean [L].** `100%` critical-scale clustering, Euler-mollified log-mean, outer law, horizontal moment and three defect readings are one statement.
- **Two cluster walls [D].** MZF's obstruction is a local fraction `≳1/8` of comparably deep zeros; NGF's quadratic depth law is `≍log X` zeros at distance `≍d`. Different thresholds, same local-excess shape.
- **Bottom at translation infinity [S].** `c_φ↛0`; far bubbles interfere and never separate; the space at infinity is Bohr.
- **Repulsion is Diophantine and sign-free [L/D].** Finite carriers repel by Baker; a.e. value repels; `0∉E` bears on no real part.
- **Stepanov order [L/D].** Over `𝔽_q` producer → count → unitarity. Over ℤ, Nair integrals ⇔ count, with no rate.

## 1. Faces of the one object

| Reading | Statement | Anchor |
|---|---|---|
| Index | `κ` counts distinct right zeros; RH ⇔ `κ=0`; counts critical lengths | HKT, AKLT, CWS [L] |
| Onset aperture | nonnegative half-widths are `[0,a*]`; contact attained off RH | WVL, AHD [L] |
| Hardy interval | `ℋ(c)` closed, antitone; `⋂ℋ(c)={1}` ⇔ RH | FADF [L] |
| Cone and margin | `λ*(c)→0` ⇔ RH | CHT [L] |
| Two sites | RH ⇔ two-site PD | GWZ, SRT [L] |
| Reflection pair | `W−\|𝒞_m\|=½min(W(G₊),W(G₋))` | SWC [L] |
| Kernel | contact ⇔ kernel blow-up | CSTW [L] |
| Anchor flow | `∫dx/(1−r²)<∞`; `q∈L¹` up to contact | CSTW [L] |
| Sampling | positive on-line mimic at every precontact aperture | CSTW [L] |
| Lattice | Schur parameters in `(−1,1)` | GWZ [L] |
| Causal | outer predictor; every echo in its Schur band; every lattice at the threshold | AIF [S] |
| Moments | even Hamburger, odd shifted Hamburger, window Stieltjes | SWC [L] |
| Li / Cayley | ladder entries `2λ_n`; NSD on primitives | ALG [L] |
| Suzuki | first variation = Weil energy; `A_N` bounded | RHTower [L] |
| Single prime | one Euler factor suffices; transport ⇔ RH | RHTower, AHD [L] |
| Heads | `windowThreshold(log d)` for all `d` | AHD [L] |
| Heat | no positive-time collisions | RHTower, ZCG [L] |
| Cosine | `(Im ξ′)²+Re ξ Re ξ″>0` on the open strip | PTR [L] |
| Jensen | infinitely many degrees real; sublinear upper height | FFP [L] |
| Hausdorff | every row below the quadratic boundary | S [L] |
| Heat grids | every degree on two fixed grids; chirp bounded; chirp mean →0 | RHTower [L] |
| Theta ranks | signed Hankel at every rank | RHTower [L] |
| Krein | coefficient-space positivity; `D_s≥0` | RIT [L] |
| Hecke dispersion | `V_p≤2(1−p^{−½})` at every zero, one `p,Y` | ACP [L] |
| Long moments | cofinal `θ` at any `K`; one window `∫₀¹\|ζM_X\|²≪X^{2ε}` | CDG, MZF [L] |
| Positive proportion | every length-2 window has a positive proportion with `\|E_X\|≤X^ε` | MZF [L] |
| Baez-Duarte / BSY | rows; `I≤0` | RHTower [L] |
| Budgets | `inf_Q budget=1` | AIF [S] |
| Count | `ψ(x)−x≪√x log²x`; integer lag `≤(2+γ−log 4π)√n` | RHTower [L] |
| Integrality | Siegel or Liouville half at square-root scale | ASRP [L] |
| Möbius | subpower Hilbert form; one point `M_X(½+it₀)≪X^ε`; zero-freeness of `M_X` | RHTower, MZF [L] |
| Redheffer | `det=M(N)` = reduced Euler characteristic of the prime complex | HWV, ADT [L] |
| Recurrence | strong self-return; uniform target mass | RHTower [L] |
| Split | ZAL ∧ AAL; ZAL ∧ zero-disc recurrence; decay ∧ recurrence | RHTower [L]; AIF [S] |
| Source criteria | Fock bound, repair equality, co-shift class | RHTower [L] |
| Bezout | source-energy sign | ACS [L] |
| Characters | complex Gram positivity of central class functions | Representation [L] |

## 2. Axes

### 2.1 Window axis
| Coordinate | Reading at half-width `c` | Anchor |
|---|---|---|
| Markov death | support `e^{−3/4}` | SWC [L] |
| Perron threshold | `c=log ρ≈0.2812` | SWC, FADF [L] |
| Actual odd prime entry | `c=½log 2≈0.3466` | FADF [L] |
| Known sign, Lean | floor tower `<0.3621`, base `a₀>181/500`; primitive `h¹` coercive for `a≤181/500` | AIP, LST [L] |
| Known sign, external numerics | `≈1.9` by the window rung with `T₀=3×10¹²` | [D] |
| Even blind minimum | `≥1/20` for `a≤(log 2+1/50)/2` | EWU [L] |
| Odd unit window | `c=½`, margin `≈2×10⁻⁴` | SWC [L/N] |
| First prime stage | `2c=21/20`: stage loan fails; closed-form Schur complement | WTZ, GWZ [L] |
| Prime-three entry | `2c=log 3` | SWC, AHD [L] |
| Prime 3 as collar mass / deleted | fail for `c≥287/500` / `c≥3/5` | SWC [L] |
| Variance-free certificates | fail for `c>273/400` | SWC [K] |
| `{2,3,4}` frontier | `2c<log 5` | SWC [L] |
| Edge-law crossing | `c*∈(½log 5,½log 6]` | FADF [L] |
| End of finite templates | spread `27/5` | WTZ [L] |
| Zero information | from `c≥4`; `≈20` with present constants | WVL [L]; [D] |
| Local crystal scale | `λ·½log T` with `λ<1`: depth `≲λ^{−3/2}/L` invisible | [D] |
| Cut crystal | any fixed depth hidden from aperture `(log T)/36` | WVL [L] |
| Camera threshold | isolated zeros at `λ>½`; configurations and sharp location at `λ>1` | ZCG [L] |
| Height non-locality | zeros below `exp((e^{2δa}−2)/(4δ)−a)` do not decide | WVL [L] |

### 2.2 Width axis
| Route | Parameter | Interior value means | Known | Anchor |
|---|---|---|---|---|
| RW, AIP, OWU | floor rate `2σ` | zero width `≤σ` | VK below rate 1 | S, I [L] |
| SC | Gaussian coupling rate | zero width `≤σ` | bounded ⇔ RH | ACPL [L] |
| WL, MC | abscissa `2Θ`, gauge exponent | `Θ` | VK | CAF, AGT [L] |
| WD | long-moment slope `2wθ` | `w` | exact, strict saving ⇒ RH | CDG [L] |
| MC | zero abscissa of `M_X` | `Θ` | exact | MZF [L] |
| LA | stability line `σ` | zero-free `Re s>σ` | `σ≥1` | FFP [L] |
| PTR | depth `h` | real-rootedness at `h` expected ⇔ width `≤h` | `h>½−vkWidth` | PTR, ZCG [L]; [D] |
| TH | aperture `a` | all ranks at `a` expected ⇔ width `≤a` | VK collar per rank | TCS [L]; [D] |
| TT | endpoint exponent `t` | `C_t` | `t≤κ·vkScale/(96 log)` | C [L] |
| ZCG | `Λ_X log X` | below a fixed `κ₀` gives a strip | `≤6600/9991+ε`; method floor `>½` | RHTower, ZCG [L] |
| PM | Hecke bound `2(1−p^{−½−β})` | half-plane `β` | `β<½` only at the edge | ACP [L] |
| AE | integrality exponent; stencil rate | `Θ` | linear plus `ε`, no rate | ASRP, AKLT [L]; [D] |
| Recurrence | return exponent `e(ρ)` | above the density bound gives RH | none | [D] |

### 2.3 Finite rungs
| Ladder | Rung | Verified height | Anchor |
|---|---|---|---|
| RW, OWU, EWU, ACT | window `a` | `windowHeight a` | VHR [L] |
| HF, SRT | ratio `R`, limit pencil only | window `≈(1/8)log R` | [D] |
| TH | rank `N`, `0<a≤½` | `41+6(N+2)log(N+2)`; rank 10 from 67 | TCS [L] |
| TH | rank `N`, `0<a≤¾` | `D(N+1)³+1` | VHR [L] |
| LA | degree `d` | `2·10⁷d⁴≤T log T` | VHR [L] |
| LI | entry `n` | `n≤4.7T`; `n≤314` from 67 | VHR [L] |
| PA | row `k`, `r` | `k+1≤1.5(T−1)`, `r≤RT³` | VHR [L] |
| HCF | degree | `deg+1≤T/4800` | VHR [L] |
| Centre PF | order `k` | `k+1≤3T`; `k=200` from 67 | VHR [L] |
| Endpoint Toeplitz | order `≤200` | 67 | Representation [L] |

### 2.4 Abscissa split
| Half | Statement | Receivers | Strength |
|---|---|---|---|
| ZAL | finitely many zeros beyond each positive depth | inner-field decay [S], `Φ_S≤Me^{au}`, `Λ_Xlog X→0`, eventual Hadamard, cosine levels [L] | ≥qRH |
| AAL | finite right of `½+h` forces none | single-base lags, log-dense lags, twisted plateau, JAS, off-line chain, bounded towers, bounded cone, shell positivity, weak recurrence [L] | sub |

## 3. Equivalence classes and shared observables

| Class | Observable / endpoint | Routes | Identity or scoped receiver |
|---|---|---|---|
| C1 Window form | `Q≥0` on every window | HF, SRT, AIP, ACT, ACS, RW, EWU, OWU; AHD, CACT | window ⇔ threshold ⇔ Hardy admissibility [L]; MSC landing not established |
| C2 Glued state | `κ(φ_c)−1` | SC, AKG | Grams are compressions [L] |
| C3 Window integer | collision charge, glued index, enclosed multiplicity | WD-charge, SC, TG, HEF | index and count receivers [L]; integrality supplies no subunit norm |
| C4 Sectors | odd, even sign; signed gauges | CHMD, TT-odd, OWU, EWU, ACT | exact format [L]; TT endpoint branch needs upper bounds |
| C5 Laguerre / continuation | Laguerre form on horizontal lines | TH, PTR, ZCG, LA, GTA, XN, HCF, PA | distinct receivers [L]; common limit form only [D] |
| C6 Scheduled prime sums | history floor or sampled bound | FU, CFC, RP, LI | receivers retain their schedules [L] |
| C7 One-point precision | `ψ−x`, `M`, cyclotomic mode, coupling | WL, MC, PBM, RB, JAS, CTF | band ⇔ classical criteria [L] |
| C8 Selection / recurrence | trivial gauge; self-return | MC-typicality, BAG | transfer closed; target mass open [L] |
| C9 Realization | Krein defect, renewal nodes, Lee–Yang limit, cosine | RN, PM, PTR; W1C | RH receivers [L]; producers missing |
| C10 Source completion | factorial energy, repair equality, reflection-odd class | SEC, CDC, PCS; APF, EWJ, RFHM, WBF | sources closed; zero-parameter bounds open [L] |
| C11 Local zero location | depth, near-line density, inner caps | WD, census, HEF, SRT-local, MZF | eight forms; `D_win` not a proportion statement [L] |
| C12 Hodge–Lefschetz | HL, zero modes, top gcd stratum | HF, ACS, RIT, EHT, TG, DZG, GWZ, HWV | zero modes radical [L] |
| C13 Sections and counts | source cone, RR, domination | ACS, HF; IRK; WTZ, LST, KPA | source and RR closed; Bézout ⇔ RH [L] |
| C14 Reflection | Rosati, Lewis, Krein, Hecke dispersion | PM, HF; W1C | coefficient identity, weighted defect, `V_p` [L] |
| C15 Canonical flow | stages, lattices, kernels, `r,q` | CWS, WTZ, DZG, GWZ, CSTW, SWC, CHT, RW, SZ | canonical system to contact [L]; contact-uniform control open |
| C16 Blind cone | `𝒜(c)`, `λ*`, blind tests | PBAP, FADF, CHT | pinning, margin law, exact null test [L] |
| C17 Dimension zero | domination of point counts | ATD, DZG | bare domination ⇔ `Q≥0` [L] |
| C18 Angle dictionary | Hurwitz forms | AHD, ACS, LST, GWZ | `𝔽_q` angle = frequency [L] |
| C19 Two-site band | `\|𝒞_m(f)\|≤W(f)` | GWZ, AOG, SWC, SRT; every route of C1, C4, C7, C14, C15 | RH ⇔ two-parameter family [L] |
| C20 Selberg rigidity | Euler discrepancy; degree; FE twins | SEL; ACS, HF | Gamma-independent rigidity [K] |
| C21 Camera | Weil-image readout; sharp location | ZCG, SRT, MZF | readout conditional on isolation [L] |
| C22 Jet moments | Hankel, Toeplitz, jets | SWC, TH, LA, GWZ, PA, HCF | distinct sequences need their own sign [L] |
| C23 Density apertures | completeness radius | ZCG | face of C21 [L] |
| C24 Hermite–Biehler phase | dominant `A` | ZCG carriers, FFP Euler carriers, PTR, PM line law | real above horizon; drift `θ_S/2`; one shift axis [L/D] |
| C25 Onset aperture | `a*(ζ)` | WVL, SRT, HF, every window route | closed interval [L] |
| C26 Hardy interval | `1∈ℋ(c)` | FADF; C1, C4 | uniqueness and criticality unconditional [L] |
| C27 Contact | `K` bounded up to every length | CSTW, CHT, RW, SZ | blow-up at contact; scaling law [L]; local [S] |
| C28 Finite free | stability of `R_d`; `N_d` | FFP, LA, TH | `sup_dN_d` off-line multiplicity [L] |
| C29 Hecke graphs | finite rational graphs | WTZ, CWS | templates below `27/5` [L] |
| C30 Li ladders | `λ_n≥0` | LI, ACS, HF | Toeplitz ladder [L] |
| C31 Repulsion | separation of zeros | ADO, ZCG, LA | Baker, a.e. values, `0∉E` open [L]; amplifier |
| C32 Long moments | `∫\|ζM\|²` | APR, CDG, WD, MZF; MC, CTF, WL | slope rigid; necessary length; one window [L] |
| C33 Finite-degree detectors | Hausdorff, heat grid, slice, Jensen | PA, HCF, LA, FFP | explicit detection; no fixed family decides [L] |
| C34 Width axis | zero-free parameter | §2.2 | interior is quasi-RH |
| C35 Finite rungs | fixed window, rank, degree | §2.3 | verification decides each rung [L] |
| C36 Prime-blind duality | Gamma, pole, `log n` | PBAP, EWU, OWU, CHT | RH ⇔ blind positivity [L] |
| C37 Inner factor | Blaschke product of right zeros | CTF-BSY, MZF, AKLT, GWZ, CSTW, AIF | identity and box budgets [S]; `N(ρ)≤Πϱ` [L] |
| C38 Eisenstein carrier | `E*(z,½+ib)`, Hecke periods, resonances | TH, PM; W1C support | coefficient identification [L]; edge positivity shared |
| C39 Passive medium | echo train of `Λ(n)/√n` | RW, PA, PTR, CHMD, SC | Schur band, first-reflector dictionary [S]; lossless stack unconstructed |
| C40 Near-line clusters | comparably deep zeros; crowds | MZF, NGF, WVL | isolated rate 2 [L]; shielding, crowds [L]; cluster wall open |
| C41 Parabolic flow | frequency, gap laws, maximum principle | NGF, ZCG | all laws blind to `t=0` [L] |
| C42 Log-mean | `T⁻¹∫log\|ζ\|` | WD, CTF, RW, ZCG, MC, census | 8-way equivalence [L]; Jensen blind |
| C43 Abscissa split | `Θ∞`, attained top | BAG, JAS, SC, WL sparse, all count routes | split and collapse [L]; AAL open |
| C44 Torus and columns | phases, insertion cone, column minima | TH, ZCG carriers, FFP drift | Bernstein, locking, columns add [S] |
| C45 Production | Nair lattice, stencils, gauge multiplicity | WL, MC; AE, AKLT, AHA, AGT | exact integrality; slope `1+ε` [L]; no rate |
| C46 Characters and weights | Young projections, tensor growth, global trace | ACS, HF; W2, W4 | RH-level criteria; finite-order and column positivity [L]; Golden blocks shortcuts |
| C47 Bohr space | far dipoles, recurrence of cosine series, pair returns | RW, HF, BAG | far bubbles [S]; pair recurrence [L] |

C1, C4, C16, C19, C25 and C26 are exact window-form dictionaries. C5, C28, C33 require all-root or all-degree control. C11, C32, C40, C42 clustering and occupancy statements are weaker than RH; RH receivers need finite and shallow exceptions controlled, which is C43. C13 closes source supply, not effectivity. C8–C10 and C21 retain source-specific bounds. C23, C24, C31 supply calibration or amplification.

### 3.1 Constructive transfers and their limits

| Sources / routes | Established transfer | Input not transported |
|---|---|---|
| RW/HF/SRT/AIP/ACS | complete form, band and source-energy sign have exact receivers [L] | all-aperture sign; complement at each ratio |
| AHD→VHR | limit pencil at ratio `R` from a window of half-width `≈(1/8)log R` [D] | compactness modulo Bohr |
| RW→flow | canonical system, anchor identity, flux, Riccati form, contact scaling [L] | variation bound; `q∈L¹` up to contact |
| Primes→reflectors | first reflector reads `Λ(n₀)`; forward map causal, injective [S] | forward map at large `n` |
| Verified heights→rungs | window, Li, Hausdorff, heat, Jensen, PF, theta [L] | certified verification past 67 |
| NGF↔MZF | typical-height input shared: zero keeping, local count | exceptional heights |
| ZCG↔WD | depth law reads critical-scale clustering [D] | crowds |
| CDG/MZF→CTF | sharp defect → cofinal moment with `K=3`; one-window and positive-proportion forms [L] | arithmetic upper bound |
| LA/ZCG/PTR/TH | separate criteria [L] | no implication between unresolved source estimates |
| TH↔ZCG | current is `2\|Ξ\|²Re ξ′/ξ`; columns against Gamma base [L/S/D] | prime cancellation above `S*` |
| PM↔TH | common Eisenstein coefficients [L] | off-axis positivity |
| PM | coefficient Krein identity, weighted defect, boundary norm, `V_p` [L] | physical descent, `D_s≥0` |
| RN→RW | two-ended formula, energy comparison [L] | joint-node exclusion |
| SZ→Weil | first variation, Abel source, VK saving [L] | bounded residual |
| SEC, CDC, PCS | actual sources and criteria [L] | zero-parameter bound, equality, vanishing |
| BAG | flow/head-target transfer; pair recurrence at typical base [L] | uniform mass; returns on off-line discs |
| TG, GTA | trace norm bounds multiplicity; charge receiver [L] | subunit norm; small charge |
| CTF, FEL, AIF | BSY integral, budgets, mollifier infimum [L/S] | calibrated history; near-extremal mollifier |
| AAL producers | sparse bounds ⇒ AAL [L] | each source bound |
| AE→WL | stencil slope ⇒ one-sided prime count [L] | rate past VK |

## 4. U-Σ — the sign

Core problem: `1∈ℋ(c)` for every `c`. In cone form, `λ*(c)≥0` for every `c`. In format form, the two signed certificates on every window. In causal form, an outer predictor at every window. In flow form, `q∈L¹` up to contact. In Laguerre form, horizontal-line positivity of Ξ.

| Face | Routes / programmes | Reduction |
|---|---|---|
| Complete atomic matrix | HF, SRT, AIP, ACT, CACT, CSAR, ACPL, RAPT, TM, ADT, AHD | limit pencil is a rung; complement is compactness modulo Bohr; all `K` is `a*=⊤` |
| Ground energy, chain, cone | RW, EWU, OWU, CSTW, CHT | `a*(ζ)` by stages; `L,q`; `λ*≥0` |
| Causal chain | RW, GWZ, AIF | outer predictors; Schur bands; free coordinates; forward map |
| Sectors, ground states | CHMD, ACT, OWU, EWU, SWC, FADF | two-sector format |
| Hardy, calibration | FADF, PBAP, CHT | arithmetic point in `𝒜(c)` |
| Moment problems | SWC, TH, LA, PA, HCF | Stieltjes, Hamburger; rows, degrees |
| Theta spectrum | TH, CAF, TCS, AIF | Euler operators on Eisenstein coefficients; columns against Gamma base |
| Heat, cosine, Jensen | ZCG, PTR, LA, NGF, FFP | crystal on typical heights; small time at all heights |
| Glued state | SC, AKG | Beurling-schedule sign |
| Window tower | CWS, WTZ, DZG, GWZ, SWC | kick admission; two sites |
| Hecke graphs | WTZ | finite matrices below `27/5` |
| Visibility | WVL, SRT, DCI, ZCG | output of every window theorem |
| Edge, zero modes | EHT, HWV, DZG, GWZ | no zero mode |
| Effectivity, RR | ACS, LST, RIT, HF, KPA | source and RR closed; Bézout is sign |
| Li, Cayley | LI, ALG | `λ_n≥0` |
| Suzuki | SZ | first variation = Weil energy |
| Scheduled sums | FU, CFC, RP, LI | history floors |
| Charge | GTA, TG | cofinally small charge; subunit norm |
| Renewal | RN | joint nodes |

## 5. U-Π — precision and production

Core problem: square-root precision of one smoothed short-window prime count, and an exact mechanism producing it.

| Face | Routes / programmes | Reduction |
|---|---|---|
| Reflection-pair coupling | SWC, GWZ, CSTW, AOG | collar Hankel − smoothed count; truncates to `n≤e^{2c}` |
| Classical one-sided counts | WL, PBM, RB, JAS, CTF | RH-level equivalence with the band; integer lag form |
| Collective kicks | SWC, FADF | beyond size, by sign |
| Cyclotomic mode, gauge torus | MC, CAF, AGT | exponent `½` at the trivial point |
| Integer producers | WL, AKLT, ASRP, AE | exact integrality; stencils; rate of `C_ε` is a width axis [D] |
| Möbius, nerve | MC, HWV, ADT | half-power cancellation; one-point form; zeros of `M_X` |
| Inner caps | WD, CDG | off-line generating function |
| Near-line density | WD, CDG, census, MZF | log-mean; isolated rate 2, clusters `2θ`; barrier blind; last scale |
| Long moments | APR, CDG, WD, MZF; CTF | slope rigid; one-window; pronic tail |
| Budgets | CTF, AIF | second expression; near-extremal mollifiers |
| Negative moments | MZF, MC, ADO | exponential moments of the Green potential; long polynomial pays residues |
| Deciding-input filters | ASRP, APR | parity, purity, precision, aperture, stabilizer |
| Census | SRT, Zeta23, CDG | signed pair data past bandwidth one; runs |
| Sections, heights | ACS, LST, WTZ, DZG, KPA | independent count or height sign not constructed |

## 6. U-Γ — selection and reflection

Core problem: source-defined arithmetic control of `ρ↦1−ρ̄`.

| Face | Routes / programmes | Status |
|---|---|---|
| Recurrence, gauge | MC, AGT, BAG | transfer closed; pair returns at typical base; target mass and trivial gauge open |
| Abscissa split | BAG, JAS, SC, WL sparse, AKLT, ZCG | split and collapse proved; ¬AAL rigid; AAL open |
| Zero–one law | whole programme | escape carriers `κ∈{0,∞}`; recurrent data degree `0` or `∞` [L/S]; actual ζ open |
| One-off fakes | APD, RHTower, AIF | continuous Beurling and non-arithmetic data have them; exact FE forbids them; defect trade-off open |
| Time-zero selection | ZCG, NGF | parabolic tools blind; arithmetic input needed |
| Pole gluing | SC, AKG, RIT | classified |
| Weil cone, lattices | RHTower, GWZ, FADF, CHT | at most `{Λ}`; nonempty iff RH |
| Selberg class | SEL | rigidity |
| Camera identification | ZCG, SRT, MZF | conditional readout; no isolation for ζ |
| Reality at near-coincidences | ZCG, ADO | pair discriminant; FE pair forces `\|ζ(½+iγ)\|≪\|γ\|^{33/200+ε}δ²` |
| Sharp location | SRT, ZCG | proved receiver |
| Diophantine repulsion | ADO, ZCG | `0∉E` open |
| Euler columns, carriers | ZCG, FFP, AIF | domination non-selective; drift `θ_S/2`; column inner field explicit |
| Mayer reflection | PM; W1C, ACP | `D_s≤0`; boundary norm; `V_p`; Poisson and Schur blindness; `D_s≥0` open |
| Rosati, Frobenius at infinity | CWS, WTZ, GWZ, AOG | sharpened |
| Li, Cayley | ALG, LI | Metzler sign = Hodge index |
| Displacement | RHTower, CDC, SEC | holomorphic data carry no weighting by displacement |
| Source completions | CDC, SEC, PCS; RFHM, EWJ, APF, WBF | source versus missing forcing |
| Characters, weights | ACS, Representation, AK | column and finite-order positivity; Golden blocks shortcuts |
| Function-field calibration | many | one window decides purity; `ℋ(n)={1}` for large `n`; curve chain |

## 7. Cross-family seams

| Seam | Statement | Routes |
|---|---|---|
| Σ ∩ Π: reflection pairs | `W(f±f∘R)=2W(f)±2𝒞_m(f)` | SWC, GWZ, CSTW, AOG, WL [L] |
| Σ ∩ Π: Hardy form | `W=H−P`; unique multiple | FADF [L] |
| Σ ∩ Π: cone | pinning; `λ*` ceiling | CHT [L] |
| Σ ∩ Π: size versus sign | edge law; `H<0` by `21/40`; size exact across columns | FADF, SWC [L]; AIF [S] |
| Σ ∩ Π: untwisted–twisted | orthogonal twists `O(1/K)`; Dirichlet shifts cancel tails | AHD [L] |
| Σ ∩ Π: exponential weight | prime shifts infinitesimal against `e^{−8y}` | CACT [L] |
| Σ ∩ Π: reflectors | first reflector reads the prime; Schur parameter over `𝔽_q` reads the point count | AIF [S]; GWZ [L] |
| Σ ∩ archimedean | logarithmic Poisson factor; positive renewal kernel; edge law | CSTW, CHT [L] |
| Σ ∩ Γ: chain and mimic | sampling atoms are positive mimics | CSTW, ZCG [L] |
| Σ ∩ Γ: flow and inner factor | `r` peels the inner factor [D] | CSTW, GWZ, MZF, AIF |
| Σ ∩ Γ: exact completion | coefficient Weil energy = Krein form | RIT [L] |
| Σ ∩ Γ: visibility | window sign reads depth; universal threshold; two-lobe bound | WVL, ZCG [L] |
| Σ ∩ Γ: theta and Eisenstein | same coefficients; unitary axis versus period variable | CAF, RIT [L] |
| Σ ∩ Γ: Bohr | far dipoles, recurrence replaces decoupling | AIF [S]; BAG [L] |
| Σ ∩ Π ∩ Γ: local onset | sign at `λ·½log X` reads clustering at fixed constant [D] | RW, ZCG, WD |
| Π ∩ continuation: heat size floor | `6600/9991`; saddle; pair models collide | ZCG [L] |
| Π ∩ Γ: density aperture | blindness `πD`; Ingham scales; weighted count | ZCG, WVL [L] |
| Π ∩ Γ: negative moments | `N(ρ)=exp(−ΣG)`; Möbius log energy pays `Σ\|ρζ′(ρ)\|⁻²` | MZF [L]; AIF [S] |
| Π ∩ Γ: exponent rigidity | Poisson floor against cap | MZF [L] |
| Π ∩ Γ: prime-side AAL | ¬AAL is a finite oscillation of `ψ(x)−x` [D] | WL, BAG |
| C5 ∩ C28: finite free | heat = `⊞_d` with Hermite; `N_d` counts off-line zeros | FFP [L] |
| C5 ∩ C31: repulsion and reality | uniform separation transports reality along real paths | ADO [L] |
| Σ ∩ Π: gluing | Redheffer = reduced Euler characteristic | HWV, ADT [L] |
| Σ ∩ Γ: Li and Hodge | Hodge index = Metzler sign = Li | ALG [L] |

## 8. Route → core map

| Route | Core | Halves | Classes | Face |
|---|---|---|---|---|
| WL | Π | both | C7, C19, C32, C43 | bounded endpoint energy; integer lag; sparse samples read AAL |
| RW, EWU, OWU | Σ | both | C1, C4, C15, C16, C19, C22, C25–C27, C39, C47 | `a*(ζ)`; `L,q`; causal; two-sector format |
| FU, CFC, RP | Σ | both | C6 | full-history bounds |
| SZ | Σ | both | C15, C27 | completed Abel residual |
| LI | Σ (Π) | both | C30, C6 | Cayley–Li sign |
| PA (HJ) | Σ (Π) | both | C5, C22, C33, C39 | rows below the quadratic boundary; exterior diagonal |
| TH | Σ (Γ) | both | C5, C22, C33–C35, C38, C44 | Eisenstein coefficients; rank; columns against Gamma base |
| HCF | Σ | both | C5, C22, C33 | all degrees on two grids |
| LA | Σ | ZAL side | C5, C22, C28, C33 | outer roots |
| GTA | Σ | both | C5 | cofinally small charge |
| XN | Σ | both | C5 | covering discs |
| MC | Π (Γ) | both | C7, C8, C12, C32 | trivial gauge; one-point form; `M_X` zeros |
| TT | Π (Σ) | both | C4 | endpoint upper bound |
| TG | Π, Σ | both | C3, C12 | subunit trace norm |
| HF | Σ (Π, Γ) | both | C1, C12–C15, C18, C25, C47 | compactness modulo Bohr then sign; head windows |
| SRT, AIP, ACT | Σ (Π) | both | C1, C4, C11, C19, C21, C25 | complete atomic matrix; sharp location |
| SC | Σ, Π (Γ) | AAL branch; both | C2, C3, C7, C39, C43 | glued state; heat-average coupling; undamped cone ⇒ AAL |
| CHMD | Σ | both | C4, C1, C39 | odd sector |
| RN | Σ | both | C9, C1 | joint nodes |
| WD | Π (Σ) | ZAL side | C3, C11, C32, C40, C42 | long moments; log-mean; near-line density |
| PM | Γ (Σ) | both | C9, C14, C38 | Krein; boundary norm; `D_s`; Hecke dispersion |
| JAS | Π | AAL branch; both | C7, C19, C43 | moving power; shell positivity ⇒ AAL |
| CTF | Π | both | C7, C19, C32, C37, C42 | BSY, budgets |
| PBM, RB | Π | both | C7, C19 | abscissa, extremal |
| BAG | Γ | AAL | C8, C43, C47 | target mass; returns |
| ACS | Π (Σ, Γ) | both | C13, C1, C12, C18, C20, C30, C46 | source sign; global trace |
| SEC | Γ | both | C10 | factorial bound |
| CDC (BSH) | Γ | both | C10 | repair equality |
| PCS | Γ | both | C10 | singular class |
| PTR | Σ (Γ) | both | C9, C5, C24, C39 | Laguerre below VK |
| ZCG | Γ (Σ) | ZAL side | C5, C21, C23, C24, C31, C40, C41 | collisions; frequency; time-0 selection |
| APF, EWJ, RFHM, WBF (candidates) | Γ (Π) | — | C10 | missing landing |
| IRK (candidate) | Γ (Π) | — | C13 | analytic trace with Chern charge |
| EGC, FEL, MSC (candidates) | Σ (Π) | — | C6, C1 | landing; history; Sonin sign |
| W1C (candidate) | Σ (Γ) | — | C9, C5, C38 | independent positive realization |
| FFP (support) | Σ (Π) | — | C28, C22, C24, C5, C33 | stability; count |
| ADO (support) | Γ | — | C31, C5 | amplifier |
| NGF (support) | Σ (Γ) | — | C41, C40, C5 | parabolic laws |
| MZF (support) | Π (Γ) | — | C11, C21, C32, C37, C40, C42 | cameras; rigidity |
| AIF (programme) | Σ, Π, Γ | both | C37, C39, C42–C44, C47 | inner field; causal; columns; recurrence |
| VHR (support) | — | — | C35 | rungs |
| CSTW, CHT (programmes) | Σ | — | C15, C16, C27, C37 | flow; cone |
| FADF, SWC, WVL, WTZ | Σ | — | C26, C4, C25, C29 | Hardy; format; visibility; graphs |
| APR, AE, AKLT | Π | — | C32, C7, C45 | length; filters; production; AAL producers |
| PBAP, W3 | Σ (Γ) | — | C16, C36 | blind positivity; exact null test |
| Representation, AK (W2, W4) | Γ (Σ) | — | C46 | characters; weights |

## 9. What a closing argument must supply

| Needed | Present over ℤ | Missing |
|---|---|---|
| Both halves of the split | split, collapse under AAL, rigid ¬AAL [L] | one ZAL input; one AAL input |
| Budget, not exact sign | bounded or subexponential floor ⇒ RH [L] | any such floor |
| Sign of the minimal object | band ⇔ `1∈ℋ(c)` ⇔ `λ*→0` [L] | the band at every step |
| Mechanism for the sign | exact format; causal certificate; Schur bands; floors to `a_k`; cone pinned [L/S] | every actual echo in its band; a signed mechanism past `log ρ` |
| Uniformity in length | each length a rung; transport ⇔ RH; head reduction [L] | every length |
| Flow | canonical system, Riccati, contact scaling, soft kick [L]; local a priori estimates [S] | `q∈L¹` up to contact; a bound free of `1/μ` |
| Full-space structure | subcritical and small-K PD; low packets; aliasing limits and dual floors; far reserve; tails [L] | profile decomposition with Bohr space at infinity above `R₀` |
| Across primes | columns add; Gamma base grows with height [S/D] | prime cancellation above `S*` |
| Theta | rank ten; two atoms; single chains; Euler product [L] | cross-chain positivity with height-dependent amplitude |
| Time selection | parabolic laws [L] | an arithmetic input separating `Φ` from heated kernels |
| Precision, occupancy | rate 2 for isolated; log-mean equivalence; long-moment rigidity [L] | sharp log-mean; cluster bound; detector past last scale |
| Opposite sign | second expression; Castelnuovo over `𝔽_q` [S] | near-extremal mollifiers |
| Count from geometry | exact source cone and RR [L] | source sign; independent count or Rosati producer |
| Canonical selector | cone pinned; unique multiple; camera conditional [L] | all-aperture sign; isolation |
| Reflection | coefficient completion, weighted defect, boundary norm, Hecke dispersion [L] | a lower bound for dispersion; `D_s≥0`; physical carrier |
| Sparse exceptions | density theorems, corridors, sharp location, pair recurrence at typical base [L] | AAL: returns at a zero or a contradiction in ¬AAL |
| Production | exact integrality; slope `1+ε`; filters; criteria [L] | a rate past VK; an independent arithmetic bound in a live route, or a landing for one candidate |
