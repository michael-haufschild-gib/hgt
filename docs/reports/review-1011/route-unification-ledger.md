# Route unification ledger — status quo

The 38 live formulations and 12 candidates are faces of three core problems: **U-Σ** (sign), **U-Π** (precision and production) and **U-Γ** (selection, reflection and position). Their RH-level endpoints meet at one object: **one inequality per prime, on the primes of sparse logarithmic windows, off power-thin exceptions**. For a prime `p` the smoothed prime count in the window of `p` exceeds its archimedean-plus-pole prediction by at most a constant, `P(p)≤A(p)+K`; equivalently `2c_p≥−K`; equivalently Weil's form is nonnegative on the two-bump `B+τ_{log p}B`; equivalently the class `Γ_1+Γ_p` carries a count with Tate limit `δ_p(1,1)`; and, with no sign, `|2c_p|≤K` [L*]. U-Σ reads the object as the sign of one test per prime, U-Π as a crude prime count, U-Γ as the count half of a Born rule.

Transversal to the three cores, a failure of RH lies in one of **two worlds**: world I (¬AAL), a finite isolated top layer with a zero-free strip, or world II (AAL ∧ ¬ZAL), a tail approaching `Re s=Θ∞>½` [L*]/[D]. RH has three atoms, ZAL ∧ B13 ∧ Landing [L*]. Every atom needs the functional equation and the Euler product together, and ζ is rigid: no model keeps both structures and moves a zero [L*]/[D].

Three structural gaps lie under all three cores: the **dark range** (Dirichlet polynomials longer than the height); the **diagonal** (a comb finite part with no positive presentation; not one glued carrier object) [L*]; and the **joint FE–Euler input** (an inequality that the explicit formula does not imply). The family step is not among them: the zero motive of ζ is the fixed part of every arithmetic family, so no family is a producer [L*].

**Why there are three cores [D].** No test is compact on both sides of the explicit formula. A compact prime side (U-Σ) leaves infinitely many zero modes and only an exact sign decides. A localized zero side (U-Π) lets a crude bound decide and leaves the prime side at square-root precision. U-Γ is the involution `ρ↦1−ρ̄`, the selection of ζ and the position of its zeros in height. The curve proof uses two freebies that ζ lacks: finite rank, and zeros periodic in height.

Corpus checkpoint: commit `68b0e1200f` with its working tree (2026-11-10); working log `logs/review-1011-statusquo-research.md`. Evidence: `[L*]` Lean statement read for this ledger; `[L]` recorded as integrated Lean in the frontier map, the scoped-obstruction ledger or a programme table of `formal/` returned by the corpus search tool; `[S]` source present in the working tree, not committed at the checkpoint, statement read; `[K]` with transitive axiom audit as recorded; `[D]` deduction; `[C]` classical. Locators: [frontier map](../rh-current-frontier-map.md), [scoped obstructions](../rh-killed-routes.md), [walls](walls-ledger.md), [routes](route-obstacles.md), [summary](obstacles-summary.md).

**Equivalence through RH transfers truth, not mechanism.** Only an explicit source identity or a proved transport moves an estimate between routes. Section 3 separates the two.

## 0. Unifying statements

- **One inequality per prime [L*].** RH ⇔ `2c_p≥−K` ⇔ `P(p)≤A(p)+K` ⇔ `Re W(B+τ_{log p}B)≥0` at every prime; width `≤α` ⇔ the same with `Kp^α`.
- **One local decision with exceptions [L*].** The bound on the primes of arbitrarily late logarithmic windows, outside `Ce^{δT}` primes per window, is RH; under ¬RH every late window keeps a violator outside every such set.
- **One sign-free decision [L*].** RH ⇔ `|2c_p|≤K` on such windows, by complex deletion filters; RH ⇔ the ordinate is injective on the zeros.
- **One sample principle [L*]/[L].** `√T` windows decide every tempered configuration; no fixed length does; separated deep ordinates are decided by bounded windows; Bohr-dense sets decide attained tops; density-zero exceptions and finitely many Frobenii admit unattained tops.
- **Two worlds [L*]/[D].** `Θ<1⇔Θ∞<1`; ¬AAL ⇒ `Θ<1`; a failure of RH is a finite isolated top with a free strip, or a tail.
- **Three atoms [L*].** RH ⇔ ZAL ∧ B13 ∧ Landing; AAL ⇔ B13 ∧ Landing ∧ DH; a failure of AAL fails exactly one.
- **One complete receiver in world I [L*].** Filters read every top residue at every damping speed; the VK bound and the growth range are separated by `a(1−β)/2`.
- **One rigidity [L*]/[L].** Hamburger; FE-defect isolation; count distance; isozeric gauge deformations; the fixed part of every family.
- **One price for exactness [L*].** A power map is a Frobenius at one prime; simultaneous vanishing costs `m·θ(S)`; the exact Stepanov count is Chebyshev's; orbit symmetries are Adams maps.
- **One square [L*].** `𝒢=W(ℤ)`: contacts plus jets are Weil's off-diagonal; the diagonal has torsion conormal classes; no finite-type carrier; the diagonal of Weil's form is a comb finite part.
- **One count [L*].** A section count with Riemann–Roch and Bézout ⇔ Hodge index ⇔ RH; the count is needed on one ray per prime of sparse windows.
- **One index law [L*].** A defect of degree `κ` has at most `κ` exceptional points; the bound passes to limits; RH ⇔ ξ is a limit of index-one functions.
- **One scalar for the windows [L*].** RH ⇔ `Ψ` locally bounded; a window at aperture `a` is a finite-height statement.
- **One critical curve [L*].** `R_c=R_polar=R_halfline≤W₀`, with a three-way classification.
- **One horizon [L*].** Ringdown, horocycle, cavity energy and reflection Krein index read the same resonances; one cavity function is a complete and sharp receiver.
- **One scale of the prime orbit [L*].** Heavy returns are excluded to the VK height and, in a strip, to `exp(c·y^{1−Θ∞})`.
- **One width axis [L]/[D].** Every interior value of every growth, decay or deformation parameter is a zero-free strip; unconditional pointwise savings are VK; purity thresholds of the natural deformations are the width.
- **One Mertens level [L*]/[L].** Producer rate, Farey discrepancy, nerve, orientation cover.
- **Law and point [D].** Past VK every unconditional theorem is in law; on the prime side a zero is visible at every scale, on the height side it is one point.

## 1. Faces of the one object

| Reading | Statement | Anchor |
|---|---|---|
| Prime two-bumps | `Re W(B+τ_{log p}B)≥0` at every prime | SOSZ [L*] |
| Stepanov prime count | `P(p)≤A(p)+K` | SOSZ [L*] |
| Local prime count with exceptions | the same on logarithmic windows off `Ce^{δT}` primes | SOSZ ScaleLocality [L*] |
| Two-prime local windows | a lower bound on the difference lags of two primes in late `√T` windows | SOSZ ScaleLocality [L*] |
| Two-sided, sign-free | `\|c_p\|≤K` | SOSZ, SignFreePurityMechanisms [L*] |
| Height separation | the ordinate is injective on the zeros | SignFreePurityMechanisms [L*] |
| Count door | an `ℕ`-count with Tate limit `δ_p(1,1)` on every prime ray | SOSZ, CTH [L*] |
| Section count | Riemann–Roch and Bézout for one count | ArithmeticCorrespondencePositivity [L*] |
| Three atoms | ZAL ∧ B13 ∧ Landing | ELT, ZCG [L*] |
| Attained top + thick count | attained abscissa ∧ thick `O(√X)` prime deviation | IRP [L*] |
| Windows | `W≥0` on every window; `Ψ` locally bounded | AHD, AIF [L*] |
| Sectors | odd form `≥0`; even blind minimum `≥0`; one-shift variation inequality | RHTower, ArithmeticCriticalityTheory [L*] |
| Critical thresholds | all `=⊤` | AHD [L*] |
| Clock | `E_r(f)≥−ε` near `r=1` on every packet | HAT [L*]/[D] |
| Li / Cayley | ladders NSD on primitives | ALG [L*] |
| Heat | no positive-time collision | RHTower [L*] |
| Cosine | strict Laguerre on the open strip | RHTower [L*] |
| Jensen | infinitely many degrees real-rooted; equivalently no finite nonempty stratum of exceptional shifts at any degree | FFP, ZCG [L*] |
| Index | ξ a limit of index-one functions | IRP [L*] |
| Hausdorff, heat grids, theta jets, renewal, quartic charge, cubic gate | the receivers of PA, HCF, TH, RN, GTA, TG | [L*] |
| Ringdown | every pulse at `e^{−(¼−ε)τ}` | BHR [L*] |
| Cavity energy | rate `y^{¾−ε}` for one cavity function | AHMH [L*] |
| Reflection Krein form | negative index `0` | AHMH [L*] |
| One eigenform | sharp rate ∧ no nonhalving Shimura zero | AHMH [L*] |
| Long moments | cofinal polynomial boundedness | CDG [L*] |
| BSY / chronological rows | vanishing log-integral; unit rows reach every tolerance | RHTower [L*] |
| Classical counts | integer lag one-sided; regularized abscissa; squarefree quarter law; Robin at `lcm` | RHTower [L*] |
| Producer rate | rates `K^{−a}` for all `a<½` | AAD [L*] |
| Fixed-point auxiliary | `log N(A_N)≤N+C√N log²N` | ALST [L*] |
| Orientation cover | weight `½` | HAT [L*] |
| Tensor powers | sublinear tensor exponents with the trace of ζ retained | AWT [L*] |
| Cone coupling | bounded Gaussian-damped coupling on one two-prime cone | ACPL [L*] |
| Source cone | all-aperture Bézout | ACS [L*] |
| Recurrence | uniform head-target density; `T^c` one-separated returns to small discs, `c>(30/13)(1−σ)`, exclude a zero right of `σ` | RHTower, ZCG [L*] |

## 2. Axes

### 2.1 Scale axis of the minimal face
| Window radius in `u=log p` at a late `T` | Decides | Anchor |
|---|---|---|
| all primes; power-saving gap sets | RH | SOSZ [L*] |
| `r√T` | RH, every tempered configuration | SOSZ [L*] |
| `C log²T` | RH; signed-deletion proof of the absolute form | SOSZ [L*] |
| `32 log(T+2)`, off `Ce^{δT}` primes | RH, width, Stepanov form | SOSZ [L*] |
| unbounded | attained tops (world I): AAL | SOSZ [L*] |
| unbounded, `o(log T)`; bounded with a lowest ordinate | open (B143) | — |
| `80/δ+1` | configurations with `δ`-separated deep ordinates, from either side | SOSZ [L*] |
| any fixed length, no constraint | nothing uniformly | SOSZ [L*] |
| one prime's powers | nothing (aliasing) | SOSZ [L] |

### 2.2 The exceptional coordinate
| Level | Statement | Status |
|---|---|---|
| quasi-RH | `Θ<1` ⇔ `Θ∞<1` | tail law [L*] |
| ZAL | `Θ∞=½` | ≥qRH, open |
| Landing | ZAL ⇒ finitely many off-line zeros | sub; open for ζ; settled as a method question [L*] |
| B13 | finitely many off-line zeros ⇒ none | sub, open |
| DH | ¬AAL ⇒ ZAL | sub, open; classified on models [L*] |
| AAL | no isolated top | sub, open; implied by B56 [D] |
| B56 | `Θ<1⇒Θ=½` | sub, open; implied by the transfer of S3 [D] |
| World I | finite top, free strip, Mertens power saving, late heavy returns, complete receiver | instrumented [L*] |
| World II | tail | receivers only |

### 2.3 Window axis and height
| Coordinate | Value | Anchor |
|---|---|---|
| Markov death; Perron threshold | `e^{−3/4}`; `log ρ` (plastic) | SWC, FADF [L] |
| Known sign in Lean | half-width `<0.3621`; windows `A≤181/250` | AIP, HAT [L] |
| Verified height | RH through 67; sign at `a` from `windowHeight(a)` | VHR [L*] |
| Visibility | positivity at `a` forces near-line zeros to height of scale `e^{a}`; models hide to aperture `(log T)/36` | WVL, SRT [L] |
| End of finite templates | spread `27/5` | WTZ [L] |

### 2.4 Width axis
| Route | Parameter | Interior value means | Known |
|---|---|---|---|
| ACS, SRT, WL | growth exponent of either side at the primes, on logarithmic windows, off exceptions | width | VK saving |
| WL, IWT | continuous-level lag exponent | zero-free half-plane | VK |
| MC, AAD, RAC | Mertens level; stencil rate; Liouville exponent | strip | VK |
| PM | ringdown, horocycle, cavity exponents; Narain exponent | strip | stretched-exponential saving |
| TH, PTR, ZCG, LA | aperture, depth, heat time, stability line | width | VK collars; heat time = width squared |
| AWT | tensor-moment exponents | width | none sublinear |
| TTPO | heavy-return exponent | Littlewood-type bound | `(log y)^{3/2−ε}`; `y^{1−Θ∞}` in a strip |
| IRP | defect degree along natural deformations | width | pure from `a=½` |

### 2.5 Scale axis of the prime orbit
| Range of primes at height `t` | What holds | Anchor |
|---|---|---|
| `p≲c log t` | prescribable | PTT [L] |
| `≈(log t)²` | Euler mollifier length for near-unit moments | APR [L] |
| `(log t)^A` | saving `t^{−δ}` | PTT [L] |
| `exp((log t)^{2/3+ε})` | no heavy return | TTPO [L*] |
| `y` with `log t<c·y^{1−Θ∞−ε}` | no heavy return, in a strip | TTPO [L*] |
| beyond the collective depth floor | return counts | CDGeo [L] |

### 2.6 Conversions from law to point
| Conversion | Where it proves a Riemann hypothesis | Over ℤ |
|---|---|---|
| sign of a form | Weil for curves; Lagarias–Suzuki | U-Σ; no producer; the square is a curve |
| integrality gap with cheap vanishing | Stepanov–Bombieri | cost `m·θ(S)`: the count itself [L*] |
| exact recurrence in height | curves | the dark range; the transfer has strength ≥B56 [D] |
| separation by an invariant | Newton polygons | a receiver; coefficient gaps excluded [L*] |
| a family with monodromy | Deligne | fixed part [L*] |
| limits of pure objects, then identification | — | identification free (rigidity); natural families follow the width axis [L*]/[D] |

### 2.7 The curve proof and its ℤ-counterparts
| Ingredient on a curve over `𝔽_q` | ℤ-counterpart | Status over ℤ |
|---|---|---|
| Finite rank | ZAL = well-foundedness; or an attained top | open |
| Periodicity of the zeros ⇒ AAL | absent: no vertical progression of zeros and no `ℓ²` perturbation of one, at any real part [L*]; the counterpart is zero transport, and only dilations are exact | open |
| Stepanov's bound | `P(p)≤A(p)+K` on logarithmic windows off exceptions | open (B130) |
| Frobenius with zero derivative | a power map is a Frobenius at one prime | priced [L*] |
| The surface `C×C` | `Spec W(ℤ)`: a curve with contacts; tower of lines of infinite type | no finite-type object [L*] |
| The diagonal and its self-intersection | a comb finite part | no glued object [L*] |
| Riemann–Roch and ampleness | exact section counts; Bézout is the Hodge index | Bézout open (B149) |
| Tensor-power trick and family | Tate-twist constituents; fixed part | no producer [L*] |
| Archimedean and finite fibres | weight lines of the shift; `ℍ³` and trees | off-diagonal only [L*] |
| No carries in `𝔽_q[T]` | carry term `(2 log 2−1)N` | defect of the window count [L*] |
| Middle cohomology of the orientation cover vanishes | weight `≥½`, `=½` ⇔ RH | open |

## 3. Which routes are the same problem

### 3.1 Same problem by source identity or proved transport
| Family | Routes | Identity | Anchor |
|---|---|---|---|
| **Prime-degree inequality** | ACS, SRT, WL (prime-window form), HF and RW through the two-bumps, ZCG (sampling), HAT-C, candidate S3 (as receiver) | `c_B(log p)=A(p)−P(p)`, `Re W(B+τ_{log p}B)=2c_B(0)+2c_p`: one number per prime, localized to logarithmic windows with exceptions | SOSZ [L*] |
| **Window scalar** | RW, EWU, OWU, ACT, CHMD (odd), TT (odd), SZ, RN, LI, AIP, HAT-C | one form on one window; sectors exact; the clock is an ordered approximation of the same form | SWC, HAT, AIF [L*] |
| **Critical curve** | HF, SRT, AIP, ACS (atomic), SC | `R_c=R_polar=R_halfline≤W₀` | AHD [L*] |
| **Exceptional coordinate** | ZCG (abscissa laws), BAG, JAS (shell), SC (undamped), WL (thick runs), LA (finite support) | two worlds; atoms; finite-stratum receivers are B13 faces | ELT, ZCG, IRP [L*] |
| **Mertens level** | MC, SQF, WL (integer lag), PBM, RB, CTF (defect) | rate ⇔ level; centred cover count | AAD, RIAC [L*]/[L] |
| **Horizon** | PM with BHR, ASH, CTH, AHMH | one scattering matrix; one cavity receiver | AHMH [L*] |
| **Count and diagonal** | ACS, HF, PM (probes), HAT-C | count ⇔ Hodge index; contacts + jets; comb finite part | AGZ, HAT, CTH [L*] |
| **Laguerre / continuation** | ZCG (heat), PTR, LA, HCF | collision-free flow; purity thresholds are the width | RHTower, FFP [L*] |
| **Tensor and family** | ECP, ACS (tensor branch) | positivity at every rank; fixed part | AWT [L*] |
| Aliases | HJ→PA; BSY criterion of FEL→CTF | definitions | frontier |

### 3.2 Same endpoint, distinct mechanism
| Group | Routes | Common form only |
|---|---|---|
| Scheduled sums | FU, CFC, RP, LI | one-sided history floors |
| Finite-degree detectors | PA, HCF, TH, LA, GTA, XN, TG | a sign or a bound at every degree, rank or disc |
| Source completions | candidates SEC, CDC/BSH, APF, EWJ, RFHM, WBF | a source plus one condition at each zero |
| Dark-range inputs | B46, B57, B96, B97, B121, B137 | Dirichlet polynomials longer than the height |
| World-I inputs | B13, B138, B141, B145, B128 | an inequality beyond the explicit formula, using both structures |
| Producers of RH strength | B87, B146, B149, B114, B117 | a positive or index-one object built without the zeros |

### 3.3 Classes

**Σ-classes.**
| Class | Observable | Routes | Identity or scoped receiver |
|---|---|---|---|
| C1 Window form | `W≥0` on every window | RW, EWU, OWU, ACT, AIP, HF, SRT, ACS | window ⇔ threshold ⇔ sector criteria [L*] |
| C2 Canonical flow | `r, q, Ψ` | RW, SZ | `Ψ` locally bounded ⇔ RH [L*] |
| C3 Critical compactness | thresholds, ground states | HF, SRT, AIP, SC | classification [L*] |
| C4 Laguerre / continuation | Laguerre forms, collisions, Jensen roots | PTR, ZCG, LA, HCF, PA | distinct receivers [L*] |
| C5 Scheduled sums | history floors | FU, CFC, RP, LI | receivers retain their schedules [L*] |
| C6 Theta moments | Hankel ranks, adaptive head | TH | head = ζ on the line [L*] |
| C7 Ordered Green approximation | `E_r` | HAT-C | `E_r↑W` [L*] |
| C8 Verified-height rungs | fixed window, rank, degree | RW, TH, LA, LI, PA, HCF | each rung from verified height [L*] |

**Π-classes.**
| Class | Observable | Routes | Identity or scoped receiver |
|---|---|---|---|
| C9 Prime-degree sampling | bounds at decisive samples | ACS, SRT, WL, ZCG | logarithmic windows with exceptions [L*] |
| C10 One-point precision | `ψ`, `M`, squarefree count, regularized series | WL, MC, SQF, PBM, RB, JAS, CTF | classical criteria [L*] |
| C11 Production | stencils, auxiliaries | WL, MC | rate = Mertens level; exact count = Chebyshev [L*] |
| C12 Long moments and census | `∫\|ζM\|²`; covariance; form factor | WD, CTF | exact receivers; estimates in law [L*] |
| C13 Returns | heavy returns, depth, counts | BAG, TH, SRT; S3 | VK height; strip [L*] |
| C14 Exactness | Frobenius at one prime, `m·θ(S)`, Adams maps | ACS, BAG | priced [L*] |
| C15 Families | tensor powers, gauge torus | ECP, ACS | fixed part [L*] |
| C16 Topology of the prime complex | nerve, orientation cover | MC | weight `½` ⇔ RH [L*] |

**Γ-classes.**
| Class | Observable | Routes | Identity or scoped receiver |
|---|---|---|---|
| C17 Two worlds and atoms | `Θ`, `Θ∞`, sectors | ZCG, BAG, JAS, SC, WL, LA | RH = ZAL ∧ B13 ∧ Landing [L*] |
| C18 Finite-layer receiver | filters, currents | ZCG, BAG | complete; gap `a(1−β)/2` [L*] |
| C19 Rigidity | FE defects, gauge deformations | ZCG, BAG, MC | identifies ζ [L*] |
| C20 Horizon | ringdown, cavity, Krein index | PM | sharp receivers [L*] |
| C21 Count | Tate limits, section counts | ACS, HF, PM | count ⇔ Hodge index [L*] |
| C22 Diagonal | comb finite parts, tower, clock | HF, ACS, HAT-C | no glued object [L*] |
| C23 Absolute geometry | contacts, carries, gluing index, tower of lines | ACS, HF | square is a curve [L*] |
| C24 Index and limits | defects, index-one limits | PTR, W1C (candidate) | semicontinuity [L*] |
| C25 Separation | ordinate injectivity | ZCG | receiver [L*] |
| C26 Recurrence and transport | self-return, tail transport | BAG | target mass open [L*] |
| C27 Source completion | zero-parameter conditions | candidates | landings missing [L] |

C1, C2, C7, C9 are exact dictionaries of one form; C9 is the minimal one. C4, C6 and C8 require all-degree or all-height control. C12 is in law and can bear only on tail statements. C10, C11 and C16 are one axis (the Mertens level). C13 and C14 are one programme on the dark range and on exactness. C17–C19 are one programme on the exceptional coordinate. C21–C23 are one programme on the count and the diagonal. C15 is support.

### 3.4 Constructive transfers and their limits
| Sources / routes | Established transfer | Input not transported |
|---|---|---|
| SOSZ → ACS, SRT, WL, HF, ZCG | RH from logarithmic prime windows off exceptions; width; absolute form [L*] | the bound on those windows |
| SOSZ → count door | counts on bounded windows under separation [L*]; on logarithmic windows by assembly (A72) | a count |
| VHR → window routes | verified height ⇒ window sign [L*] | verification at every height |
| AHD / CACT → HF, SRT, AIP | threshold identities and classification [L*] | polar payment; the orthogonal case |
| HAT clock → window routes | `E_r↑W` with Sobolev error [L*] | the sign |
| ELT → ZCG, BAG | world I: filters, VK bounds, Mertens saving, late returns, dominant-ordinate divergence, graded return counts [L*] | a bound in the growth range |
| ZCG / ELT atoms → LA, HF, SC, PTR | finite-stratum receivers = B13 faces; the Jensen law is RH, the cosine law is RH given ZAL [L*] | ZAL, B13, landing |
| IRP → WL | attained top replaces ZAL on thick sets [L*] | attainment; the thick estimate |
| IRP → PM, W1C, PTR | index-one limits give RH [L*] | an independent family |
| AWT → ECP, ACS | tensor criterion with the trace of ζ; fixed part [L*] | nothing: no producer inside families |
| AGZ → ACS, HF | contacts + jets; comb finite parts; section count ⇔ Hodge index [L*] | Bézout |
| TTPO → BAG, S3 | heavy returns in a strip [L*] | breadth past VK; the transfer (≥B56) |
| AHMH → PM | cavity rate ⇔ strip; one-eigenform reduction [L*] | the rate; Shimura nonvanishing |
| SignFreePurityMechanisms → ZCG, ACS | height separation ⇔ bounded traces; prices of Frobenius lifts [L*] | a two-sided bound |
| Census → WD | covariance ⇔ line density; exchange rate [L*] | a bounded form factor |

## 4. U-Σ — the sign

Core problem: `W≥0` on every window. In flow form, `Ψ` locally bounded; in minimal form, one Weil test per prime on logarithmic windows; in matrix form, every critical threshold `=⊤`, which is the window threshold plus polar payment plus the exclusion of a polar-orthogonal ground state; in clock form, `E_r≥−ε` near `r=1`; in Laguerre form, collision-free heat flow; in theta form, the sign of a head whose leading term is `|ζ(½+ib)|²`. Each window is a finite-height statement.

| Face | Routes / programmes | Reduction |
|---|---|---|
| Complete atomic matrix | HF, SRT, AIP, SC; CACT, AHD | classification; B104 |
| Ground energy, chain, cone | RW, EWU, OWU, ACT; CSTW, CHT, AIF | `a*(ζ)`; `Ψ` |
| Prime two-bumps | SRT, ACS; SOSZ | logarithmic windows with exceptions |
| Ordered Green approximation | HAT-C | the sign of `W` |
| Moments and ladders | TH, LI, PA, HCF | all ranks, entries, degrees |
| Heat, cosine, Jensen | ZCG, PTR, LA | small time at all heights |
| Scheduled sums, charge, gate, renewal | FU, CFC, RP, GTA, TG, RN, SZ, CHMD | one-sided floors and gates |

## 5. U-Π — precision and production

Core problem: square-root precision of one smoothed prime count; in minimal form the Stepanov bound on logarithmic windows off power-thin exceptions; in tower form an attained top with a thick `O(√X)` deviation; in production form a stencil rate through `a↑½`. Every exact method has an exact price, and every family sees only its variable part.

| Face | Routes / programmes | Reduction |
|---|---|---|
| Prime-degree crude bounds | ACS, SRT, WL; SOSZ, CDGeo | B130; VK saving |
| Classical one-sided counts | WL, MC, SQF, PBM, RB, JAS, CTF | RH-level equivalences |
| Producers and auxiliaries | WL, MC; AAD, ALST, RAC | rate = Mertens level; Chebyshev |
| Long moments and census | WD, CTF; CDG, APR, IGP | exact receivers; inputs in law |
| Returns and the dark range | BAG, TH; S3; TTPO, CDGeo, PTT, TAPO | VK height; strip; transfer ≥B56 |
| Families | ECP, ACS; AWT, AK | fixed part |
| Topology of the prime complex | MC; RIAC, HAT | cover weight |

## 6. U-Γ — selection, reflection, position

Core problem: source-defined control of `ρ↦1−ρ̄` and of the position of the zeros in height; in world form, the exclusion of world I (B13, Landing, DH) and of world II (ZAL); in count form, a count on one ray per prime or Bézout on the tower; in diagonal form, the sign of a comb finite part; in horizon form, one rate or one reflection sign; in index form, an independent index-one family converging to ξ.

| Face | Routes / programmes | Status |
|---|---|---|
| Two worlds and atoms | ZCG, BAG, JAS, SC, WL, LA; ELT, IRP | sector theorem; world I instrumented |
| Rigidity | ZCG, BAG; EFT, AWT, APD, SEL | ζ identified; no moduli |
| Horizon and count | PM; BHR, ASH, AHMH, CTH | sharp receivers; count at bounded distance |
| Square, diagonal, carrier | HF, ACS, HAT-C; AGZ, HAT, SOSZ | contacts + jets; comb finite part; glued object refuted |
| Index and limits | PTR, W1C; IRP | semicontinuity; line law blind to the fixed part |
| Recurrence | BAG; TAPO, AAD | target mass and transport open |

## 7. Cross-family seams

| Seam | Statement | Anchor |
|---|---|---|
| Σ ∩ Π ∩ Γ: one test per prime | `Re W(B+τ_{log p}B)=2c_B(0)+2c_p`, `c_p=A(p)−P(p)`, the defect of `Γ_1+Γ_p` | SOSZ [L*] |
| Σ ∩ Π: verification | window sign at `a` ⇐ verified height; ⇒ near-line zeros to a height | VHR, WVL [L*]/[L] |
| Σ ∩ Π: theta head | adaptive head = `ζ(½+ib)` up to `O(\|b\|^{−½})` | AHD [L*] |
| Σ ∩ Γ: clock and tower | `E_r↑W`; Weil's functional = limit of Maass–Selberg diagonals | HAT [L*] |
| Σ ∩ Γ: section count | Riemann–Roch and Bézout ⇔ Hodge index | ArithmeticCorrespondencePositivity [L*] |
| Σ ∩ Γ: index | finite Krein–Langer index ⇔ finitely many off-line zeros; index-one limits | AKLT, IRP [L*] |
| Π ∩ Γ: worlds on the prime side | world I ⇒ Mertens power saving and violators in every late bounded window | ELT [L*]/[D] |
| Π ∩ Γ: returns | a heavy return is a zero configuration imitating the pole; strip ⇒ late returns | TTPO [L*] |
| Π ∩ Γ: exactness and absolute geometry | contacts = prime part of the off-diagonal; cost `m·θ(S)`; carries | AGZ, SignFreePurityMechanisms [L*] |
| Π ∩ Γ: families | fixed part; isozeric deformations | AWT [L*] |
| Π ∩ Γ: cavity | energy rate ⇔ zero-free region | AHMH [L*] |
| Π ∩ Γ: gluing index | `log N!` against the zero count | AGZ [L*] |

## 8. Route → core map

| Route | Core | Worlds / atoms | Classes | Face |
|---|---|---|---|---|
| WL | Π (Σ) | both; attained top on thick sets | C9, C10, C11, C17 | integer lag; prime-window count; thick deviation |
| RW, EWU, OWU, ACT | Σ | both | C1, C2, C8 | `a*(ζ)`; `Ψ`; sector signs |
| FU, CFC, RP | Σ | both | C5 | history floors |
| SZ | Σ | both | C1, C2 | completed Abel residual |
| LI | Σ (Π) | both | C5, C8 | Cayley–Li sign |
| PA (HJ) | Σ (Π) | both | C4, C8 | Hausdorff rows |
| TH | Σ (Γ) | both | C6, C8, C13 | head = ζ on the line |
| HCF | Σ (Π) | both | C4, C8 | two grids |
| LA | Σ | world II side; B13 and landing for finite support | C4, C8, C17 | outer roots |
| GTA, XN, TG | Σ (Π) | both | C4 | charge, discs, gate |
| MC, SQF | Π (Γ) | both | C10, C11, C16 | half-power cancellation |
| TT | Π (Σ) | both | C1, C10 | endpoint energy |
| HF | Σ (Π, Γ) | both | C1, C3, C21, C22, C23 | polar payment; count; diagonal |
| HAT-C | Σ (Γ) | both | C1, C7, C22 | ordered Green approximation |
| SRT, AIP | Σ (Π) | both | C1, C3, C9 | prime two-bumps; critical curve |
| SC | Σ, Π (Γ) | AAL branch; ZAL | C3, C17 | damped cone coupling |
| CHMD | Σ | both | C1 | prime wave; odd sector |
| RN | Σ | both | C1 | energy comparison |
| WD | Π (Σ) | world II side | C12 | long moments; census |
| PM | Γ (Σ) | both | C20, C21 | rate; reflection sign; count |
| JAS | Π | AAL branch | C10, C17 | finite power windows |
| CTF | Π | both | C10, C12 | rows; BSY |
| PBM, RB | Π | both | C10 | abscissa; extremal inequality |
| BAG | Γ | AAL; DH | C13, C17, C18, C26 | target mass; transport; returns |
| ACS | Π (Σ, Γ) | both | C1, C9, C14, C15, C21, C22, C23 | Stepanov bound on windows; count; Bézout |
| ECP | Γ (Π) | both | C15 | character positivity at every rank |
| PTR | Σ (Γ) | both | C4, C24 | Laguerre below VK |
| ZCG | Γ (Σ) | all | C4, C9, C17, C18, C19, C25 | collisions; atoms; world I |
| Candidate S3 | Π | — | C13, C9 | transfer ≥B56 |
| Candidates SEC, CDC/BSH, APF, EWJ, RFHM, WBF | Γ (Π) | — | C27 | missing landing |
| Candidates EGC, FEL, MSC | Σ (Π) | — | C5, C1 | landing; history; Sonin sign |
| Candidate IRK | Γ (Π) | — | C21 | trace with Chern charge |
| Candidate W1C | Σ (Γ) | — | C24 | finite positive producer or index-one family |

## 9. What a closing argument must supply

| Needed | Present over ℤ | Missing |
|---|---|---|
| A crude count | the Stepanov bound as one inequality per prime, on logarithmic windows, off power-thin exceptions, one-sided or sign-free; VK saving [L*] | the bound itself (B130) |
| An elimination step | positive and signed deletion, gap iteration, window theorems, infinite Turán, resolvent of a tower [L*]/[L] | none |
| The two worlds | sector theorem; world I instrumented with a free strip; unbounded windows exclude world I [L*] | an inequality beyond the explicit formula in world I (B13, Landing, DH); ZAL for world II |
| A uniformity source | tensor criterion [L*] | none exists inside families (fixed part) |
| A Frobenius substitute | Frobenius at one prime; Adams maps; contacts [L*] | none at a lower price than the count |
| A surface | the arithmetic square, a curve; the tower of lines with exact counts; comb finite parts [L*] | Bézout for effective classes (B149); the sign of the comb finite part (B88) |
| Sign of the minimal object | one Weil test per prime [L*] | the bound at every prime of the sample |
| Uniformity in length | each window from verified height; threshold classification [L*] | every height; B104 |
| The critical line | theta head = `ζ(½+ib)` [L*] | the signed head at the critical zeros |
| Reflection | sharp cavity receivers; reflection Krein index; one-eigenform reduction [L*] | a rate past `½`, or the reflection sign; Shimura nonvanishing |
| A limit of pure objects | index semicontinuity; rigidity for the identification [L*] | an independent family of bounded index (B146) |
| Breadth of returns | VK height; strip breadth; collective counts [L*] | a depth floor uniform in `π(y)` (B97, B137) |
| Resolution of the face | logarithmic radius [L*] | the decisive radius below it (B143) |
| Production | exact integrality; VK rate; parity identity [L*]/[L] | a level past VK |
