# Route unification ledger — status quo

The 38 live formulations and 12 candidates are faces of three core problems: **U-Σ** (sign), **U-Π** (precision and production) and **U-Γ** (selection, reflection and position). Their RH-level endpoints meet at one object, in two exact forms.

- **One inequality per prime, on the primes of sparse logarithmic windows, off power-thin exceptions.** For a prime `p` the smoothed prime count in the window of `p` exceeds its archimedean-plus-pole prediction by at most a constant, `P(p)≤A(p)+K`; equivalently `2c_p≥−K`; equivalently Weil's form is nonnegative on the two-bump `B+τ_{log p}B`; and, with no sign, `|2c_p|≤K` [L*].
- **One matrix on the integers.** The comb pairing of the degree points — off the diagonal `½(1/|m−n|+1/(m+n))+Λ(n/m)`, on the diagonal `−log(n/2π)`, with the degrees `d₁=Σc_n/n`, `d₂=Σc_n` — has the limit `2d₁d₂−Z(f)` on packets; RH ⇔ `D·D≤2d₁d₂` on every packet ⇔ exactly one positive square on the two rulings and every finite family of packets [L*]/[S]. On two short blocks at ratio `p` the inequality is the first form [D].

U-Σ reads the object as the sign of a form, U-Π as a crude prime count, U-Γ as the Hodge index of a pairing.

Transversal to the three cores, a failure of RH lies in one of **two worlds**: world I (¬AAL), a finite isolated top layer with a zero-free strip, or world II (AAL ∧ ¬ZAL), a tail approaching `Re s=Θ∞>½` [L*]/[D]. RH has three atoms, ZAL ∧ B13 ∧ Landing [L*]. Every atom needs the functional equation and the Euler product together, and ζ is rigid: no model keeps both structures and moves a zero, and no bounded Dirichlet series has its zeros among the off-line zeros [L*]/[D].

Three structural gaps lie under all three cores: the **dark range** (Dirichlet polynomials longer than the height); the **diagonal** (the density of a comb, with no positive presentation; not one glued carrier object) [L*]; and the **joint FE–Euler input** (an inequality that the explicit formula does not imply). The family step is not among them: the zero motive of ζ is the fixed part of the canonical arithmetic families [L*].

**Why there are three cores [D].** No test is compact on both sides of the explicit formula. A compact prime side (U-Σ) leaves infinitely many zero modes and only an exact sign decides. A localized zero side (U-Π) lets a crude bound decide and leaves the prime side at square-root precision. U-Γ is the involution `ρ↦1−ρ̄`, the selection of ζ and the position of its zeros in height. The curve proof uses two freebies that ζ lacks: finite rank, and zeros periodic in height.

Corpus checkpoint: commit `804e55e894` with its working tree (2026-11-10); working log `logs/review-1011-frontier-facts.md`. Evidence: `[L*]` Lean statement read for this ledger; `[L]` recorded as integrated Lean in the frontier map, the scoped-obstruction ledger or a programme table of `formal/`; `[S]` source present, graded unfinished or unintegrated or untracked, statement read; `[K]` with transitive axiom audit as recorded; `[D]` deduction; `[C]` classical; `[A]` assessment. Locators: [frontier map](../rh-current-frontier-map.md), [scoped obstructions](../rh-killed-routes.md), [walls](walls-ledger.md), [routes](route-obstacles.md), [summary](obstacles-summary.md).

**Equivalence through RH transfers truth, not mechanism.** Only an explicit source identity or a proved transport moves an estimate between routes. Section 3 separates the two.

## 0. Unifying statements

- **One inequality per prime [L*].** RH ⇔ `2c_p≥−K` ⇔ `P(p)≤A(p)+K` ⇔ `Re W(B+τ_{log p}B)≥0` at every prime; width `≤α` ⇔ the same with `Kp^α`.
- **One local decision with exceptions [L*].** The bound on the primes of arbitrarily late logarithmic windows, outside `Ce^{δT}` primes per window, is RH; a power saving there is quasi-RH; under ¬RH every late window keeps a violator outside every such set.
- **One resolution [L*]/[D].** In the class `𝒵` of tempered configurations with a lowest ordinate and logarithmic local counts, no bounded window length and not every unbounded radius decides; the refuting configuration has deep zeros of positive density. On the aperture side positivity at `a` resolves a zero of depth `δ` with `n_δ` deep neighbours once `δa` exceeds a multiple of `n_δ log(1/δ)+log log γ`, and a configuration with ζ's local counts hides a deep zero at `T` to aperture `(log T)/36`. The transport of this law to the prime side is open (B151).
- **One sign-free decision [L*].** RH ⇔ `|2c_p|≤K` on log-square windows, by complex deletion filters; RH ⇔ the ordinate is injective on the zeros.
- **One matrix [L*]/[S].** The comb pairing is defined on every real vector at every finite scale; on windows of ratio `≤19/18` its form is coercive; on windows of ratio `≤2` it does not depend on the contact weights; on windows of ratio `≤Q` it is nonnegative off fewer than `2QR(Q)` block sums; on packets its defect has at most as many negative squares as ζ has zeros right of the line, and at most the defect of a Hermite–Biehler splitting that covers them. The same matrix without jets and counterterm is the Toeplitz form of a curve; with the conductor as a density it is the square of a quadratic ring, whose twisted part has no pole plane.
- **One selection [L*]/[S].** With the jets and the counterterm of the comb, Bézout holds for contact weights `w` ⇔ RH ∧ `w=Λ`; unit masses on the integers force `w=Λ`; a uniformly separated comb stable under the Frobenius monoid is one orbit `δℕ`; with the counterterm `log(n/2π)−c` the inequality holds ⇔ `c≤0` ∧ RH. RH ⇔ at every aperture some weight system is Weil-positive [D].
- **One slack [L*]/[S]/[D].** The sign over all tests has no positive margin (best margin of a window `≤K exp(11c/2−πe^{2(c−2)})`) and, downward, any uniform floor `−C∫f²` over all packets is RH. A floor at the primes for one fixed bump has `p^{o(1)}`: any floor `−Kp^α` on logarithmic windows gives width `α`. The index has one unit; returns a power.
- **Two worlds [L*]/[D].** `Θ<1⇔Θ∞<1`; ¬AAL ⇒ `Θ<1`; a failure of RH is a finite isolated top with a free strip, or a tail. A floor on windows of any unbounded radius excludes the first.
- **Three atoms [L*].** RH ⇔ ZAL ∧ B13 ∧ Landing; AAL ⇔ B13 ∧ Landing ∧ DH; a failure of AAL fails exactly one.
- **One complete receiver in world I [L*].** Filters read every top residue at every damping speed; centred Vaughan currents at every moment order; the VK bound and the growth range are separated by `a(1−β)/2`.
- **One rigidity [L*]/[L].** Hamburger; FE-defect isolation; count distance; isozeric gauge deformations and analytic smoothings; the fixed part of the canonical families; bounded Dirichlet-series factors are pure; no Dirichlet polynomial is a factor.
- **One price for exactness [L*].** A power map is a Frobenius at one prime; simultaneous vanishing costs `m·θ(S)`; the exact Stepanov count is Chebyshev's; Riemann–Roch with Bézout on the tower is the product formula; a section of the square pays one contact per prime above; the carry is a nonzero class complementary to the window count.
- **Receivers and producers [L*]/[D].** Every mechanism that proves a statement of the type of RH elsewhere has a Lean statement fixing its price over ℤ (§2.7); every route of the corpus is a receiver.
- **One square [L*].** `𝒢=W(ℤ)`: contacts plus jets are Weil's off-diagonal; no finite-type carrier; the diagonal is the density of a comb; one ring of sequences carries the tower, the pole plane and the jets.
- **One index law [L*].** A defect of degree `κ` has at most `κ` exceptional points; the bound passes to limits; RH ⇔ ξ is a limit of index-one functions.
- **One flow [L*]/[D].** A locally finite module is determined by its trace; Castelnuovo–Severi on the flow ⇔ pure and effective; RH ⇔ the lag function is positive definite on `ℝ`.
- **One count of the zeros [L*].** Gluing conditions are the smooth count; the contacts at a height are the remainder `S`.
- **One scalar for the windows [L*].** RH ⇔ `Ψ` locally bounded; a window at aperture `a` is a finite-height statement.
- **One critical curve [L*].** `R_c=R_polar=R_halfline≤W₀`; complete matrix = primitive hyperplane + pole channel; a three-way classification.
- **One horizon [L*].** Ringdown, horocycle, cavity energy and reflection Krein index read the same resonances.
- **One scale of the prime orbit [L*]/[L].** Heavy returns are excluded to the VK height and, in a strip, to `exp(c·y^{1−Θ∞})`.
- **One width axis [L]/[D].** Every interior value of every growth, decay or deformation parameter is a zero-free strip; unconditional pointwise savings are VK.
- **One Mertens level [L*]/[L].** Producer rate, Farey discrepancy, nerve, orientation cover.
- **Law and point [D].** Past VK every unconditional theorem about the zeros is in law; one law — the density zero of the deep zeros — enters a pointwise theorem (pure factors); a second pointwise theorem (no Dirichlet polynomial is a factor) uses the jump of the fractional part. Both concern constituents of ξ.

## 1. Faces of the one object

| Reading | Statement | Anchor |
|---|---|---|
| Prime two-bumps | `Re W(B±τ_{log p}B)≥0` at every prime | SOSZ [L*] |
| Stepanov prime count | `P(p)≤A(p)+K` | SOSZ [L*] |
| Local prime count with exceptions | the same on logarithmic windows off `Ce^{δT}` primes | SOSZ ScaleLocality [L*] |
| Two-prime local windows | a lower bound on the difference lags of two primes in late `√T` windows | SOSZ ScaleLocality [L*] |
| Two-sided, sign-free | `\|c_p\|≤K` | SOSZ, SignFreePurityMechanisms [L*] |
| Height separation | the ordinate is injective on the zeros | SignFreePurityMechanisms [L*] |
| Comb pairing on packets | `D·D≤2d₁d₂`; `CombBezout Λ` | AGZ [L*] |
| Hodge index on packets | exactly one positive square on `H,V` and every finite family; index ≤ defect of a splitting | AGZ, HTFP [L*] |
| Feasible weights | some weight system Weil-positive at every aperture | RHTower, FADF [L*]/[D] |
| Regulated energies | the clock and the scattering tower: energy ≥ minus the jump-tail defect | HAT [L*]/[K]/[D] |
| Count door | an `ℕ`-count with Tate limit the integer probes; `δ_p(1,1)` on every prime ray | CTH [L*]; SOSZ [L] |
| Flow | Castelnuovo–Severi on every divisor of Frobenius graphs; positive definite lag function | IRP [L*]/[D] |
| Three atoms | ZAL ∧ B13 ∧ Landing | ELT, ZCG [L*] |
| Attained top + thick count | attained abscissa ∧ thick `O(√X)` prime deviation | IRP [L*] |
| Windows | `W≥0` on every window; `Ψ` locally bounded | AHD, AIF [L*] |
| Sectors | pole-free functional `≥0` on odd tests; even blind minimum `≥0`; one-shift variation inequality | RHTower, ArithmeticCriticalityTheory [L*] |
| Critical thresholds | all `=⊤` | AHD [L*] |
| Clock | `E_r(f)≥−(1−r²)‖f′‖²/2` near `r=1` on every packet | HAT [L*]/[D] |
| Li / Cayley | ladders NSD on primitives; the flat tail of the comb form is `2λ₁` | ALG [L]; HTFP [L*]/[D] |
| Heat | no positive-time collision | RHTower [L*] |
| Cosine | no exceptional point on the open depth band | RHTower [L*] |
| Jensen | infinitely many degrees real-rooted; no finite nonempty stratum of exceptional shifts | FFP [L]; ZCG [L*] |
| Index | ξ a limit of index-one functions | IRP [L*] |
| Hausdorff, heat grids, theta jets, renewal, quartic charge, cubic gate, Newton discs | the receivers of PA, HCF, TH, RN, GTA, TG, XN | [L*]/[L] |
| Ringdown | every pulse at `e^{−(¼−ε)τ}` | BHR [L*] |
| Cavity energy | rate `y^{¾−ε}` for one cavity function | AHMH [L*] |
| Reflection Krein form | negative index `0` | AHMH [L*] |
| One eigenform | sharp rate ∧ no nonhalving Shimura zero | AHMH [L*] |
| Long moments | cofinal polynomial boundedness | CDG [L] |
| BSY / chronological rows | vanishing log-integral; unit rows reach every tolerance | RHTower [L*] |
| Classical counts | integer lag one-sided; regularized abscissa; squarefree quarter law; Robin at `lcm`; Möbius Hilbert form subpower | RHTower [L*] |
| Producer rate | rates `K^{−a}` for all `a<½` | AAD [L*] |
| Fixed-point auxiliary | `log N(A_N)≤N+C√N log²N` | ALST [L*] |
| Orientation cover | weight `½` | HAT [L*] |
| Tensor powers | sublinear tensor exponents with the trace of ζ retained | AWT [L*] |
| Cone coupling | bounded Gaussian-damped coupling on one two-prime cone | ACPL [L] |
| Recurrence | uniform head-target density; `T^c` one-separated returns exclude a zero right of `σ` | RHTower, ZCG [L*] |

## 2. Axes

### 2.1 Scale axis of the minimal face
| Window radius in `u=log p` at a late `T` | Decides | Anchor |
|---|---|---|
| all primes; power-saving gap sets | RH | SOSZ [L*]/[L] |
| `r√T` | RH, every tempered configuration without real zeros | SOSZ [L*] |
| `C log²T` | RH; signed-deletion proof of the absolute form | SOSZ [L*] |
| `32 log(T+2)`, off `Ce^{δT}` primes | RH, width, Stepanov form, quasi-RH at a power saving | SOSZ [L*] |
| unbounded | attained tops (world I): AAL | SOSZ [L*]/[L] |
| unbounded, `o(log T)`; any fixed length | nothing in the class `𝒵`: block tower with unattained top | SOSZ [L*] |
| the same, with the count of deep neighbours of ζ | open (B151); a sum of `n` modes of frequency `≥Γ` with nonnegative real part on a length `L` has `ΓL≤(2n+1)π` | [D] |
| `80/δ+1` | configurations with `δ`-separated deep ordinates, from either side | SOSZ [L*] |
| any fixed length, no constraint | nothing uniformly: low off-line pair | SOSZ [L*] |
| one prime's powers | nothing (aliasing) | SOSZ [L] |

### 2.2 Ratio axis of the comb pairing
| Window of degree points | What holds at finite scale | Anchor |
|---|---|---|
| one degree point | `c²(2/n+log(n/2π))`; negative at `n=2` | HTFP [L*] |
| ratio `≤19/18` | `D·D≤−(1/40)Σc_n²`; comb form `≥(1/50)Σc_n²`, every real divisor, every scale, every system of contact weights | HTFP [L*] |
| ratio `≤2` | no contact inside the window: the form is independent of the weights | HTFP [L*] |
| ratio in `(2,3)` | one contact, the prime `2`: the first selective window (A96) | — |
| ratio `≤Q` | comb form `≥0` on vanishing block sums; fewer than `2QR(Q)` blocks; `N≥R(Q)` | HTFP [L*] |
| every ratio, arbitrarily large scales | comb form `≥−ηΣc_n²` for every `η>0` ⇒ RH; under ¬RH a divisor with `Σc_n²≤C` and comb form `≤−ε` at every large scale | HTFP [L*] |
| packets of width `≤181/250` in `log n` | limit `≤2d₁d₂−∫f²/5000`, any sign | AGZ [L*] |
| packets of any width | limit `2d₁d₂−Z(f)`; `≤2d₁d₂` ⇔ RH; negative squares `≤#{ρ: Re ρ>½}` | AGZ [L*] |
| two-bump packets at ratio `p` | the Stepanov bound at `p`: one inequality per prime on logarithmic windows off exceptions | HTFP [L*] |
| the flat tail `[1,N]` | per degree point `→2+γ−log 4π`; negative at every large scale with a doubled weight at `2` | HTFP [L*] |

### 2.3 The exceptional coordinate
| Level | Statement | Status |
|---|---|---|
| quasi-RH | `Θ<1` ⇔ `Θ∞<1` | tail law [L*] |
| ZAL | `Θ∞=½` | ≥qRH, open |
| Landing | ZAL ⇒ finitely many off-line zeros | sub; open for ζ; settled as a method question [L*] |
| B13 | finitely many off-line zeros ⇒ none | sub, open |
| DH | ¬AAL ⇒ ZAL | sub, open; classified on models [L*] |
| AAL | no isolated top | sub, open; implied by B56 [D] |
| B56 | `Θ<1⇒Θ=½` | sub, open; implied by the transfer of S3 [D] |
| World I | finite top, free strip, Mertens power saving, late heavy returns, complete receiver, no floor on unbounded windows | instrumented [L*] |
| World II | tail; deep zeros of density zero | receivers only; hides below the logarithmic radius at the level of `𝒵` [L*] |

### 2.4 Window axis and height
| Coordinate | Value | Anchor |
|---|---|---|
| Markov death; Perron threshold | `e^{−3/4}`; `log ρ` (plastic) | SWC, FADF [L] |
| Known sign in Lean | half-width `181/500` with margin `1/5000`; an enlarged aperture `<½` with margin `1/8000` | AIP, AGZ [L]/[L*] |
| Verified height | RH through 67; sign at `a` from `windowHeight(a)` | VHR [L*] |
| Visibility | positivity at `a` bounds the pair energy of an off-line site by the cell count; for ζ, `δa<12((4n_δ+2)log(10⁶/δ)+log(A₀log(\|γ\|+3))+18)`; positivity at `λ·½log(T/2π)`, `λ>1`, bounds the depth at `T` by `exp(−c log³)`; models hide to aperture `(log T)/36` | WVL, RHTower, ZCG [L*]/[L] |
| Blindness | a window blind to a set of lower density `D` has aperture `≥πD`; a cancelling cluster has density `≥2a/π` | ZCG [L*]/[L] |
| Margin | best margin of `[−c,c]` `≤K exp(11c/2−πe^{2(c−2)})` | CHT [L*] |
| End of finite templates | spread `27/5` | WTZ [L] |

### 2.5 Width axis
| Route | Parameter | Interior value means | Known |
|---|---|---|---|
| ACS, SRT, WL | growth exponent of either side at the primes, on logarithmic windows, off exceptions | width | VK saving |
| WL, IWT | continuous-level lag exponent | zero-free half-plane | VK |
| MC, AAD, RAC | Mertens level; stencil rate; Liouville exponent | strip | VK |
| PM | ringdown, horocycle, cavity exponents; Narain exponent | strip | stretched-exponential saving |
| TH, PTR, ZCG, LA | aperture, depth, heat time, stability line | width | VK collars; heat time = width squared |
| AWT | tensor-moment exponents; the branch `1−mt` of an analytic smoothing | width | none sublinear |
| TTPO | heavy-return exponent | Littlewood-type bound | `(log y)^{3/2−ε}`; `y^{1−Θ∞}` in a strip |
| IRP | defect degree along natural deformations | width | pure from `a=½` |

### 2.6 Scale axis of the prime orbit
| Range of primes at height `t` | What holds | Anchor |
|---|---|---|
| `p≲c log t` | prescribable | PTT [L] |
| `≈(log t)²` | Euler mollifier length for near-unit moments | APR [L] |
| `(log t)^A` | saving `t^{−δ}` | PTT [L] |
| `exp((log t)^{2/3+ε})` | no heavy return | TTPO [L*] |
| `y` with `log t<c·y^{1−Θ∞−ε}` | no heavy return, in a strip | TTPO [L] |
| `e^{at}` | centred type-II current on `≤⌈2t^{J+3}⌉` cofactors with error `O(e^{−at/4})`; separated cofactor pairs `≤2/t^b`; near-diagonal pairs and the signed current open | ELT [K]/[S] |

### 2.7 Conversions from law to point
| Conversion | Where it proves a Riemann hypothesis | Over ℤ |
|---|---|---|
| sign of a form | Weil for curves; Lagarias–Suzuki | U-Σ; no producer; the square is a curve; the Hodge index of the comb pairing is RH |
| integrality gap with cheap vanishing | Stepanov–Bombieri | cost `m·θ(S)`: the count itself; at one prime: Heilbronn sums [L*] |
| exact recurrence in height | curves | the dark range; no progression or half progression of zeros [L*] |
| recurrence against density | bounded Dirichlet-series factors of ξ [L*] | ζ is not uniformly almost periodic in the strip; RH ⇔ strong recurrence [L*] |
| two-sided constant terms (the jump of the fractional part) | no Dirichlet polynomial is a factor of ξ [L*] | acts on constituents, not on ξ |
| ferromagnetic stability | Lee–Yang | stable prime polynomials have linear zero counts and their zeros are not zeros of ζ [L]/[L*] |
| a bounded-below naive height | Néron–Tate | RH ⇔ such a height exists on every window [L*] |
| a positive ground state | Perron–Frobenius | the pole moments are not of jump type [D] |
| sections and Bézout | Weil | one contact per prime above; the product formula on the tower [L*] |
| separation by an invariant | Newton polygons; Carlitz–Goss [C] | a receiver; coefficient gaps excluded; the carry is a nonzero class [L*] |
| a family with monodromy | Deligne | fixed part [L*] |
| limits of pure objects, then identification | — | identification free (rigidity); natural families follow the width axis; the index of the pairing ≤ the defect of a splitting [L*]/[D] |

### 2.8 The curve proof and its ℤ-counterparts
| Ingredient on a curve over `𝔽_q` | ℤ-counterpart | Status over ℤ |
|---|---|---|
| Finite rank | ZAL = well-foundedness; or an attained top | open |
| Periodicity of the zeros ⇒ AAL | absent: no vertical progression, no half progression, no `ℓ²` perturbation of one [L*] | open |
| Stepanov's bound | `P(p)≤A(p)+K` on logarithmic windows off exceptions | open (B130) |
| Frobenius with zero derivative | a power map is a Frobenius at one prime | priced [L*] |
| The surface `C×C` | `Spec W(ℤ)`: a curve with contacts; one ring of sequences of infinite type | no finite-type object [L*] |
| The diagonal and its self-intersection | the density of a comb | no glued object [L*] |
| The Néron–Severi lattice and its Hodge index | the comb lattice of a window: negative definite on short windows, finite index on every window | one positive square open (B152) [L*] |
| Riemann–Roch and ampleness | exact section counts with the gluing index; Bézout on the tower is the product formula; sections pay one contact per prime above | Bézout for the comb pairing open (B149) [L*] |
| The form on the comb `q^ℤ`: Toeplitz in the Frobenius eigenvalues, no jets, no counterterm, decided on `2g+1` points | one matrix with jets and the counterterm `log(n/2π)`; no finite determinacy | [S]/[L*] |
| Covers: the twisted parts are negative definite by the index of the covering surface | the twisted part of the square of a quadratic ring: no pole plane, conductor as density; negative semidefinite to aperture `log log q−log 4` | one square open beyond (B154) [S]/[D] |
| Tensor-power trick and family | Tate-twist constituents; fixed part | no producer [L*] |
| Archimedean and finite fibres | weight lines of the shift; `ℍ³` and trees | off-diagonal only [L*] |
| No carries in `𝔽_q[T]` | the carry is a cocycle that is not a coboundary, complementary to the window count | bounds nothing [L*] |
| Middle cohomology of the orientation cover vanishes | weight `≥½`, `=½` ⇔ RH | open |

### 2.9 Conductor axis
| Object | Counterterm | Trivial aperture | Open beyond | Anchor |
|---|---|---|---|---|
| a curve of genus `g` over `𝔽_q` | none; `2−2g` at lag `0` | — | nothing: the sign is purity, decided on `2g+1` degree points | HTFP [S]; ACS [L*] |
| ℤ | `log(n/2π)` | apertures below `½` with a margin | every aperture (RH) | AGZ, AIP [L*]/[L] |
| the twisted part of a quadratic ring of conductor `q` | `log(qn/2π)`, no pole plane | packets shorter than `log 2` for `q≥128π` [S]; `log log q−log 4`: the conductor dominates the contacts [D] | one square at aperture about `log log q` (B154) [A] | AGZ [S] |

In the normalization of a curve the form on the degree point `n` of ℤ is `e²(2+n log(n/2π))`: the genus at `n` is `1+(n/2)log(n/2π)`; the counterterm of a quadratic ring is twice that of ℤ plus `log q` [D].

### 2.10 Slack
| Form of the statement | Slack | Anchor |
|---|---|---|
| the sign over all tests | no positive margin; downward any uniform floor `−C∫f²` | CHT, AGZ [L*]/[S] |
| a floor at the primes, one fixed bump | `p^{o(1)}` | SOSZ [L*] |
| the index of an approximant | one unit | IRP [L*] |
| returns of ζ to its own target | a power `T^c`, `c>(30/13)(1−σ)` | ZCG [L*] |
| the heat flow at time zero | none | RHTower [L] |

## 3. Which routes are the same problem

### 3.1 Same problem by source identity or proved transport
| Family | Routes | Identity | Anchor |
|---|---|---|---|
| **Prime-degree inequality** | ACS (two-block form), SRT, WL (prime-window form), HF and RW through the two-bumps, ZCG (sampling), HAT-C, candidate S3 (as receiver) | `c_B(log p)=A(p)−P(p)`, `Re W(B+τ_{log p}B)=2c_B(0)+2c_p`: one number per prime, localized to logarithmic windows with exceptions | SOSZ [L*] |
| **Comb lattice** | ACS, HF, HAT-C, LI (flat tail), PM (count branch) | Weil's form on packets = limit of the comb form; Hodge index ⇔ RH; the comb selects `Λ` and the constant `2π` | AGZ, HTFP [L*]/[S] |
| **Combs of other objects** | ACS, HF on curves and on quadratic rings | the same normal form: Toeplitz for a curve; contacts `Λ(1+χ)` and counterterm `log(qn²/(2π)²)` for a quadratic ring | HTFP, AGZ [S] |
| **Regulators** | HAT-C, PM | the clock and the scattering tower converge to Weil's form from below by a positive jump tail; the tower of height `N` is the explicit formula of `Λ(s)/Λ(s+N)` | HAT [L*]/[K]/[D] |
| **Window scalar** | RW, EWU, OWU, ACT, CHMD (odd), TT (odd), SZ, RN, LI, AIP, HAT-C | one form on one window; sectors exact; the clock is an ordered approximation of the same form with the same domain | SWC, HAT, AIF [L*] |
| **Critical curve** | HF, SRT, AIP, ACS (atomic), SC | `R_c=R_polar=R_halfline≤W₀`; pole channel | AHD [L*] |
| **Exceptional coordinate** | ZCG (abscissa laws), BAG, JAS (shell), SC (undamped), WL (thick runs), LA (finite support) | two worlds; atoms; finite-stratum receivers are B13 faces | ELT, ZCG, IRP [L*] |
| **Lag and flow** | WL, ACS (flow form), SC | the lag function is the central trace of the zero motive; Castelnuovo–Severi on the flow is its positive definiteness | IRP [L*]/[D] |
| **Mertens level** | MC, SQF, WL (integer lag), PBM, RB, CTF (defect) | rate ⇔ level; centred cover count | AAD, RIAC [L*]/[L] |
| **Horizon** | PM with BHR, ASH, CTH, AHMH | one scattering matrix; one cavity receiver | AHMH [L*] |
| **Zero count** | WD (window prime polynomial), ACS (gluing), TG | gluing index = smooth count; the prime polynomial of a window at a height = contacts at that height = smoothed increments of `S` up to the off-line correction | AGZ, SquareRootThreshold [L*] |
| **Laguerre / continuation** | ZCG (heat), PTR, LA, HCF | collision-free flow; purity thresholds are the width | RHTower, FFP [L*] |
| **Tensor and family** | ECP, ACS (tensor branch) | positivity at every rank; fixed part | AWT [L*] |
| Aliases | HJ→PA; BSY criterion of FEL→CTF | definitions | frontier |

### 3.2 Same endpoint, distinct mechanism
| Group | Routes | Common form only |
|---|---|---|
| Scheduled sums | FU, CFC, RP, LI | one-sided history floors |
| Finite-degree detectors | PA, HCF, TH, LA, GTA, XN, TG | a sign or a bound at every degree, rank or disc |
| Source completions | candidates SEC, CDC/BSH, APF, EWJ, RFHM, WBF | a source plus one condition at each zero |
| Dark-range inputs | B46, B57, B96, B97, B121, B137, B145 | Dirichlet polynomials longer than the height |
| World-I inputs | B13, B138, B141, B145, B128 | an inequality beyond the explicit formula, using both structures |
| Producers of RH strength | B87, B146, B149, B114, B117 | a positive or index-one object built without the zeros |
| Regulators of Weil's form | cusp cutoff, scattering tower, arithmetic clock | purity at finite cutoff and the right limit are split between them |

### 3.3 Classes

**Σ-classes.**
| Class | Observable | Routes | Identity or scoped receiver |
|---|---|---|---|
| C1 Window form | `W≥0` on every window | RW, EWU, OWU, ACT, AIP, HF, SRT, ACS | window ⇔ threshold ⇔ sector criteria [L*] |
| C2 Canonical flow | `r, q, Ψ` | RW, SZ | `Ψ` locally bounded ⇔ RH [L*] |
| C3 Critical compactness | thresholds, pole channel, ground states | HF, SRT, AIP, SC | classification [L*] |
| C4 Laguerre / continuation | Laguerre forms, collisions, Jensen roots | PTR, ZCG, LA, HCF, PA | distinct receivers [L*] |
| C5 Scheduled sums | history floors | FU, CFC, RP, LI | receivers retain their schedules [L*] |
| C6 Theta moments | Hankel ranks, adaptive head | TH | head = ζ on the line [L] |
| C7 Ordered Green approximation | `E_r` | HAT-C | `E_r↑W` on the Weil form domain [L*] |
| C8 Verified-height rungs | fixed window, rank, degree | RW, TH, LA, LI, PA, HCF | each rung from verified height [L*] |
| C28 Comb lattice at finite scale | signature of the comb pairing on windows | ACS, HF, LI | short windows coercive and blind to the contacts; finite index; one positive square ⇔ RH; no positive margin; any uniform floor is RH [L*]/[S] |
| C29 Conductor ladder | signature of the twisted part of the square of a quadratic ring | ACS, HF, HAT-C, PM, SRT (twisted) | trivial aperture `log log q−log 4` [D]; one square open (B154) |

**Π-classes.**
| Class | Observable | Routes | Identity or scoped receiver |
|---|---|---|---|
| C9 Prime-degree sampling | bounds at decisive samples | ACS, SRT, WL, ZCG | logarithmic windows with exceptions; no shorter window in `𝒵`; slack `p^{o(1)}` [L*] |
| C10 One-point precision | `ψ`, `M`, squarefree count, regularized series | WL, MC, SQF, PBM, RB, JAS, CTF | classical criteria [L*] |
| C11 Production | stencils, auxiliaries | WL, MC | rate = Mertens level; exact count = Chebyshev [L*] |
| C12 Long moments and census | `∫\|ζM\|²`; covariance; form factor; deep-zero counts | WD, CTF | exact receivers; estimates in law [L*]/[L] |
| C13 Returns | heavy returns, depth, counts | BAG, TH, SRT; S3 | VK height; strip [L*]/[L] |
| C14 Exactness | Frobenius at one prime, `m·θ(S)`, Adams maps, tower Riemann–Roch, carry class | ACS, BAG | priced [L*] |
| C15 Families | tensor powers, gauge torus, analytic smoothings | ECP, ACS | fixed part; isozeric [L*] |
| C16 Topology of the prime complex | nerve, orientation cover | MC | weight `½` ⇔ RH [L*] |

**Γ-classes.**
| Class | Observable | Routes | Identity or scoped receiver |
|---|---|---|---|
| C17 Two worlds and atoms | `Θ`, `Θ∞`, sectors | ZCG, BAG, JAS, SC, WL, LA | RH = ZAL ∧ B13 ∧ Landing [L*] |
| C18 Finite-layer receiver | filters, currents | ZCG, BAG | complete; gap `a(1−β)/2` [L*] |
| C19 Rigidity | FE defects, gauge deformations, factors | ZCG, BAG, MC, W1C | identifies ζ; factors are pure [L*] |
| C20 Horizon | ringdown, cavity, Krein index | PM | sharp receivers [L*] |
| C21 Count | Tate limits, section counts | ACS, HF, PM | count ⇔ Hodge index [L*]/[L] |
| C22 Diagonal | density of the comb, tower, clock, Robin diagonal | HF, ACS, HAT-C | no glued object [L*] |
| C23 Absolute geometry | contacts, carries, gluing index, one ring of sequences, Dedekind squares | ACS, HF | square is a curve [L*] |
| C24 Index, limits and flow | defects, index-one limits, central trace | PTR, WL, W1C (candidate) | semicontinuity; flow criterion [L*] |
| C25 Separation | ordinate injectivity | ZCG | receiver [L*] |
| C26 Recurrence and transport | self-return, tail transport, recurrence against density | BAG | target mass open; factor purity proved [L*] |
| C30 Constituents | objects sharing zeros with ξ | W1C, PTR, PM | bounded factors pure; no polynomial factor; bounded series on the line open (B153) [L*] |
| C27 Source completion | zero-parameter conditions | candidates | landings missing [L] |

C1, C2, C7, C9, C28 are exact dictionaries of one form; C9 is the minimal one on packets, C28 the one on real vectors; C29 is the same form for a real character, without the pole plane. C4, C6 and C8 require all-degree or all-height control. C12 is in law; its density-zero statement bears on C19 and on C30. C10, C11 and C16 are one axis (the Mertens level). C13 and C14 are one programme on the dark range and on exactness. C17–C19 are one programme on the exceptional coordinate. C21–C23 and C28 are one programme on the count and the diagonal. C15 is support.

### 3.4 Constructive transfers and their limits
| Sources / routes | Established transfer | Input not transported |
|---|---|---|
| SOSZ → ACS, SRT, WL, HF, ZCG | RH from logarithmic prime windows off exceptions; width; absolute form [L*] | the bound on those windows |
| SOSZ → every window receiver | no receiver below the logarithmic radius at the level of `𝒵` [L*] | the count of deep neighbours on the prime side (B151) |
| VHR → window routes | verified height ⇒ window sign [L*] | verification at every height |
| AGZ → ACS, HF, LI | Weil positivity certificates transport to packets of the pairing; Hodge index ⇔ RH; the comb selects `Λ` and `2π` [L*]/[S] | the sign beyond the certified apertures |
| HTFP → ACS, HF | the pairing at finite scale; short windows; finite index; one inequality per prime on the comb; the comb of a curve [L*]/[S] | the block-sum part of a full window (B152) |
| AGZ → BAG, HF (twisted) | the square of a quadratic ring with its twisted part [S] | the exceptional square (B154) |
| IRP → W1C, PTR | no Dirichlet polynomial is a constituent; index ≤ defect [L*] | bounded series (B153); a splitting certified without the zeros (B146) |
| AHD / CACT → HF, SRT, AIP | threshold identities, pole channel, classification [L*] | pole-channel positivity; the orthogonal case |
| HAT clock → window routes | `E_r↑W` with Sobolev error on the exact form domain [L*] | the sign |
| ELT → ZCG, BAG | world I: filters, VK bounds, Mertens saving, late returns, top-ordinate dichotomy, centred Vaughan reductions at growing order; separated cofactor pairs [L*]/[K]/[S] | the near-diagonal pairs and the signed current at a growing mode |
| ZCG / ELT atoms → LA, HF, SC, PTR | finite-stratum receivers = B13 faces; the Jensen law is RH, the cosine law is RH given ZAL [L*]/[L] | ZAL, B13, landing |
| IRP → WL | attained top replaces ZAL on thick sets; the flow criterion [L*] | attainment; the thick estimate; the sign |
| IRP → PM, W1C, PTR | index-one limits give RH; exact polynomial factors are excluded [L*] | an independent family |
| AWT → ECP, ACS | tensor criterion with the trace of ζ; fixed part [L*] | nothing: no producer inside these families |
| TTPO → BAG, S3 | heavy returns in a strip [L] | breadth past VK; the transfer (≥B56) |
| AHMH → PM | cavity rate ⇔ strip; one-eigenform reduction [L*] | the rate; Shimura nonvanishing |
| SignFreePurityMechanisms → ZCG, ACS | height separation ⇔ bounded traces; prices of Frobenius lifts [L*] | a two-sided bound |
| Census → WD, IRP | covariance ⇔ line density; deep zeros `o(V)` ⇒ pure factors [L*] | a bounded form factor |

## 4. U-Σ — the sign

Core problem: `W≥0` on every window. In flow form, `Ψ` locally bounded; in minimal form, one Weil test per prime on logarithmic windows; in lattice form, exactly one positive square of the comb pairing; in matrix form, every critical threshold `=⊤`, which is the window threshold plus pole-channel positivity; in clock form, `E_r≥−(1−r²)‖f′‖²/2` near `r=1`; in Laguerre form, collision-free heat flow; in theta form, the sign of a head whose leading term is `|ζ(½+ib)|²`. Each window is a finite-height statement.

| Face | Routes / programmes | Reduction |
|---|---|---|
| Complete atomic matrix | HF, SRT, AIP, SC; CACT, AHD | classification; B104 |
| Ground energy, chain, cone | RW, EWU, OWU, ACT; CSTW, CHT, AIF | `a*(ζ)`; `Ψ` |
| Prime two-bumps | SRT, ACS; SOSZ | logarithmic windows with exceptions |
| Comb lattice | ACS, HF; AGZ, HTFP | short windows; finite index; B152 |
| Conductor ladder | the twisted part of every sign route | trivial aperture; B154 |
| Ordered Green approximation | HAT-C | the sign of `W` |
| Moments and ladders | TH, LI, PA, HCF | all ranks, entries, degrees |
| Heat, cosine, Jensen | ZCG, PTR, LA | small time at all heights |
| Scheduled sums, charge, gate, renewal | FU, CFC, RP, GTA, TG, RN, SZ, CHMD | one-sided floors and gates |

## 5. U-Π — precision and production

Core problem: square-root precision of one smoothed prime count; in minimal form the Stepanov bound on logarithmic windows off power-thin exceptions; in tower form an attained top with a thick `O(√X)` deviation; in production form a stencil rate through `a↑½`; in lattice form the potential of the flat-tail gauge, the remainder `N/n−ψ(N/n)`. Every exact method has an exact price, and every canonical family sees only its variable part.

| Face | Routes / programmes | Reduction |
|---|---|---|
| Prime-degree crude bounds | ACS, SRT, WL; SOSZ, CDGeo | B130; VK saving |
| Classical one-sided counts | WL, MC, SQF, PBM, RB, JAS, CTF | RH-level equivalences |
| Producers and auxiliaries | WL, MC; AAD, ALST, RAC | rate = Mertens level; Chebyshev; one prime |
| Long moments and census | WD, CTF; CDG, APR, IGP | exact receivers; inputs in law |
| Returns and the dark range | BAG, TH; S3; TTPO, CDGeo, PTT, TAPO, ELT | VK height; strip; transfer ≥B56; signed current open |
| Families | ECP, ACS; AWT, AK | fixed part |
| Topology of the prime complex | MC; RIAC, HAT | cover weight |

## 6. U-Γ — selection, reflection, position

Core problem: source-defined control of `ρ↦1−ρ̄` and of the position of the zeros in height; in world form, the exclusion of world I (B13, Landing, DH) and of world II (ZAL); in count form, Bézout for the comb pairing; in diagonal form, the sign of a comb finite part; in horizon form, one rate or one reflection sign; in index form, an independent index-one family converging to ξ; in flow form, the positive definiteness of the lag function.

| Face | Routes / programmes | Status |
|---|---|---|
| Two worlds and atoms | ZCG, BAG, JAS, SC, WL, LA; ELT, IRP | sector theorem; world I instrumented |
| Rigidity and factors | ZCG, BAG, W1C; EFT, AWT, APD, SEL, IRP | ζ identified; no moduli; factors pure |
| Horizon and count | PM; BHR, ASH, AHMH, CTH | sharp receivers; count door |
| Square, diagonal, carrier, lattice | HF, ACS, HAT-C; AGZ, HTFP, HAT, SOSZ | contacts + jets; density of a comb; glued object refuted; Hodge index ⇔ RH |
| Index, limits, flow | PTR, WL, W1C; IRP | semicontinuity; line law blind to the fixed part; flow criterion |
| Recurrence | BAG; TAPO, AAD, IRP | target mass and transport open; recurrence against density proves factor purity |

## 7. Cross-family seams

| Seam | Statement | Anchor |
|---|---|---|
| Σ ∩ Π ∩ Γ: one test per prime | `Re W(B+τ_{log p}B)=2c_B(0)+2c_p`, `c_p=A(p)−P(p)`, the defect of `Γ_1+Γ_p` | SOSZ [L*] |
| Σ ∩ Π ∩ Γ: one matrix | comb form = Weil's form on packets = `2d₁d₂−D·D`; its potential in the flat-tail gauge = the remainder of the prime number theorem; its index ≤ the number of right zeros and ≤ the defect of a splitting | AGZ, HTFP [L*] |
| Σ ∩ Π: verification | window sign at `a` ⇐ verified height; ⇒ near-line zeros to a height | VHR, WVL [L*]/[L] |
| Σ ∩ Π: theta head | adaptive head = `ζ(½+ib)` up to `O(\|b\|^{−½})` | AHD [L] |
| Σ ∩ Γ: clock and tower | `E_r↑W`; Weil's functional = limit of Maass–Selberg diagonals | HAT [L*] |
| Σ ∩ Γ: index | finite Krein–Langer index ⇔ finitely many off-line zeros; index-one limits | AKLT, IRP [L]/[L*] |
| Π ∩ Γ: worlds on the prime side | world I ⇒ Mertens power saving; every floor fails on unbounded windows; world II can hide below the logarithmic radius at the level of `𝒵` | ELT, SOSZ [L*] |
| Π ∩ Γ: density and resolution | deep zeros of density zero: pure factors; the count of deep neighbours sets the aperture at which a zero is resolved | IRP, SquareRootThreshold, RHTower [L*]; B151 |
| Σ ∩ Γ: the exceptional world | a real zero of a quadratic `L`-function is one negative square of the twisted comb and an isolated real top layer; classical repulsion is its theory | AGZ, ELT [S]/[L*]/[D]; B154 |
| Π ∩ Γ: returns | a heavy return is a zero configuration imitating the pole; strip ⇒ late returns | TTPO [L] |
| Π ∩ Γ: exactness and absolute geometry | contacts = prime part of the off-diagonal; cost `m·θ(S)`; carries complementary to the window count | AGZ, SignFreePurityMechanisms [L*] |
| Π ∩ Γ: families | fixed part; isozeric deformations | AWT [L*] |
| Π ∩ Γ: cavity | energy rate ⇔ zero-free region | AHMH [L*] |
| Π ∩ Γ: zero count | `log N!` against the smooth count; contacts at a height against `S` | AGZ [L*] |

## 8. Route → core map

| Route | Core | Worlds / atoms | Classes | Face |
|---|---|---|---|---|
| WL | Π (Σ, Γ) | both; attained top on thick sets | C9, C10, C11, C17, C24 | integer lag; prime-window count; thick deviation; positive definite lag function |
| RW, EWU, OWU, ACT | Σ | both | C1, C2, C8 | `a*(ζ)`; `Ψ`; sector signs |
| FU, CFC, RP | Σ | both | C5 | history floors |
| SZ | Σ | both | C1, C2 | completed Abel residual |
| LI | Σ (Π) | both | C5, C8, C28 | Cayley–Li sign; flat tail of the comb form |
| PA (HJ) | Σ (Π) | both | C4, C8 | Hausdorff rows |
| TH | Σ (Γ) | both | C6, C8, C13 | head = ζ on the line |
| HCF | Σ (Π) | both | C4, C8 | two grids |
| LA | Σ | world II side; B13 and landing for finite support | C4, C8, C17 | outer roots; finite strata of shifts |
| GTA, XN, TG | Σ (Π) | both | C4 | charge, discs, gate |
| MC, SQF | Π (Γ) | both | C10, C11, C16 | half-power cancellation |
| TT | Π (Σ) | both | C1, C10 | endpoint energy |
| HF | Σ (Π, Γ) | both | C1, C3, C21, C22, C23, C28, C29 | pole channel; count; diagonal; Hodge index; the exceptional square on the twisted part |
| HAT-C | Σ (Γ) | both | C1, C7, C22 | ordered Green approximation |
| SRT, AIP | Σ (Π) | both | C1, C3, C9 | prime two-bumps; critical curve; resolution of the face |
| SC | Σ, Π (Γ) | AAL branch; ZAL | C3, C17 | damped cone coupling |
| CHMD | Σ | both | C1 | prime wave; odd sector |
| RN | Σ | both | C1 | energy comparison |
| WD | Π (Σ, Γ) | world II side | C12 | long moments; census; contacts at a height |
| PM | Γ (Σ) | both | C20, C21 | rate; reflection sign; count; regulator |
| JAS | Π | AAL branch | C10, C17 | finite power windows |
| CTF | Π | both | C10, C12 | rows; BSY |
| PBM, RB | Π | both | C10 | abscissa; extremal inequality |
| BAG | Γ | AAL; DH | C13, C17, C18, C26 | target mass; transport; returns |
| ACS | Γ (Σ, Π) | both | C1, C9, C14, C15, C21, C22, C23, C28, C29 | Hodge index of the comb pairing; Stepanov bound on windows; Bézout; the exceptional square on the twisted part |
| ECP | Γ (Π) | both | C15 | character positivity at every rank |
| PTR | Σ (Γ) | both | C4, C24, C30 | no exceptional point below VK; constituents |
| ZCG | Γ (Σ) | all | C4, C9, C17, C18, C19, C25 | collisions; atoms; world I |
| Candidate S3 | Π | — | C13, C9 | transfer ≥B56 |
| Candidates SEC, CDC/BSH, APF, EWJ, RFHM, WBF | Γ (Π) | — | C27 | missing landing |
| Candidates EGC, FEL, MSC | Σ (Π) | — | C5, C1 | landing; history; Sonin sign |
| Candidate IRK | Γ (Π) | — | C21 | trace with Chern charge |
| Candidate W1C | Σ (Γ) | — | C24, C19 | finite positive producer or index-one family; no exact polynomial factor |

## 9. What a closing argument must supply

| Needed | Present over ℤ | Missing |
|---|---|---|
| A crude count | the Stepanov bound as one inequality per prime, on logarithmic windows, off power-thin exceptions, one-sided or sign-free; VK saving [L*] | the bound itself (B130) |
| The resolution of the count | logarithmic radius for ζ; no shorter window at the level of `𝒵`; the aperture-side law with the count of deep neighbours [L*] | its transport to the prime side (B151) |
| An elimination step | positive and signed deletion, gap iteration, window theorems, infinite Turán, resolvent of a tower [L*]/[L] | none |
| The two worlds | sector theorem; world I instrumented with a free strip; unbounded windows exclude world I [L*] | an inequality beyond the explicit formula in world I (B13, Landing, DH); ZAL for world II |
| A uniformity source | tensor criterion [L*] | none exists inside the canonical families (fixed part) |
| A Frobenius substitute | Frobenius at one prime; Adams maps; contacts; Stepanov at one prime [L*] | none at a lower price than the count |
| A surface | the arithmetic square, a curve; one ring of sequences with exact counts; the comb pairing with limit `2d₁d₂−Z(f)`; margins to width `181/250`; coercivity on short windows and finite index at every scale; the combs of a curve and of a quadratic ring [L*]/[S] | one positive square on full windows (B152); Bézout from a property of the object (B149) |
| A producer | none: every mechanism has a price (§2.7) | one selective inequality at unbounded scale that is not a transport of the classical region; its smallest instance is the exceptional square (B154) |
| Sign of the minimal object | one Weil test per prime [L*] | the bound at every prime of the sample |
| Uniformity in length | each window from verified height; threshold classification; pole channel [L*] | every height; B104 |
| The critical line | theta head = `ζ(½+ib)` [L] | the signed head at the critical zeros |
| Reflection | sharp cavity receivers; reflection Krein index; one-eigenform reduction [L*] | a rate past `½`, or the reflection sign; Shimura nonvanishing |
| A limit of pure objects | index semicontinuity; rigidity for the identification; three regulators [L*] | an independent family of bounded index (B146); a regulator pure at every cutoff with the right limit (B117) |
| Breadth of returns | VK height; strip breadth; collective counts; reductions at exponential scales [L*]/[K] | a depth floor uniform in `π(y)` (B97, B137); the signed current (B145) |
| Production | exact integrality; VK rate; parity identity [L*]/[L] | a level past VK |
