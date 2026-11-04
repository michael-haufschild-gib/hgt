# Route unification ledger — status quo

The 32 live routes and 17 candidates are faces of three core problems — **U-Σ** (sign), **U-Π**
(precision and production), **U-Γ** (selection and reflection) — and the three are one statement read
three ways: the **band** `|𝒞_m(f)| ≤ W(f)` of a test `f` and its mirror image `f∘R`, `R(v) = 2m − v`,
with `𝒞_m(f) = 𝓗_m(f) − Σ_nΛ(n)n^{−1/2}(f⋆f)(2m − log n)`. All read one even integer
`κ = κ(K_ζ) = #` distinct zeros right of the critical line, on one object, the window tower `A ↦ W_A`,
and all are decided on its smallest piece, the reflection pair.

- **One criterion, one minimal object.** Every sign face is Weil's form on windows of every length [L];
  windows are decided on two sites: RH ⇔ every two-site lattice window is PD ⇔ strict orbit
  Cauchy–Schwarz [L]; the parity sectors of a window are the band at its centre [L].
- **Sign = precision.** `W(f ± f∘R) = 2W(f) ± 2𝒞_m(f)` and `𝒞_m` is the collar Hankel form (the pole
  square `e^mμ_{1/2}(f)²` minus trivial-zero squares) minus the smoothed prime count of `f⋆f` [L]: U-Σ on a
  reflection pair is U-Π at one scale.
- **Reflection = zero side.** `Q(H) = 2Re[𝓦H, 𝓦H]` on `ℓ²(zeros)` with reflection `ρ ↦ 1 − ρ̄`; Hecke is
  translation; the window involution is the twisted conjugate Krein reflection [L]: U-Γ's positivity is
  U-Σ in zero coordinates.
- **One canonical system.** Lattices: Szegő–Levinson theory of Weil sequences, one prime kick moves one
  Schur parameter, Szegő singular under RH [L]. Local continuum limit at a bump: the jet Hankel system
  `[W(φ^{(i)}, φ^{(j)})]` [L]. The global Hamiltonian is not constructed.
- **One location.** A new fold couples the two collars only; the kick is the collar Rosati pairing, a
  positive source minus an anti-diagonal conductance [L]; first failures of lattices are two-site [L], and
  window minimizers are non-smooth at the edge [W].
- **One gauge calculus.** In a gauge `F = Φωu` the window form is a signed Dirichlet form plus pole
  charges; theta gauges are critical on the line; a window reads their outside charges with the pole's
  signs [L].
- **One locality law.** The collar light cone pays the kick of `n` at ratio `2Λ(n)n^{−1/2}e^h`, sharp [L];
  it certifies no kick of the primes `3 ≤ p ≤ 73` and no kick once `h > log(1/(2w_n))`; summed over a
  reflection pair the kicks are the smoothed prime count of U-Π [L/D].
- **One algebra, one graph, one family.** The window algebra is a truncated Dirichlet λ-ring with no
  internal Frobenius; finite configurations are rational Hecke graphs; the Tate family is classified at
  dimension zero [L].
- **One decomposition, one pole, one threshold.** At the critical curve the complete family is Weil's
  form at the pole `u = 0` of the frequency counts plus positive counts on every twisted direction; its
  window threshold `R₁(A)` is `⊤` for every `A` iff RH [L].
- **One growth exponent.** The ground-energy growth exponent of windows is the zero width; an
  aperture-independent floor with exponent `p` gives zero width `≤ p`, and the proved size-only range
  `p > 1` carries no zero information [L/D].
- **One Frobenius.** Frobenius at scale `t` is translation by `t` (`T_p − Id = √pH(· + log p)`; PM multiplier
  `p^{1−2s}`, similitude factor `p`) [L].
- **One point and one cone.** The Weil cone is `{Λ}` or empty; only `Λ` keeps every lattice positive [L].
- **One camera.** The explicit formula is injective on finite modifications of the zeros at every
  aperture, sign-free; mimics need near-collisions; reality of a near-collision is the sign of a
  second-order coefficient read through the `(log n)²`-weighted primes [L].
- **One threshold of identification.** Columns of RvM density hide from cameras of exponent `λ ≤ ½` and
  only those [L]; `λ = ½` is the Riemann–Siegel length [D].
- **One deformation.** Reality of a fixed-degree real family is lost only through collision; the heat
  path of `Ξ` is real for `t ≥ 1/8`, has finitely many non-real zeros for every `t > 0` and infinitely many
  for every `t < 0` [L]; so RH ⇔ no collision on `(0, 1/8]` [D].
- **One criticality.** Every exact reading sits on a zero-slack boundary [L/D].
- **One missing mechanism.** Over `𝔽_q` the 2×2 Gram of the diagonal and the graph of Frobenius is
  positive on primitive classes by the Hodge index, proved from Riemann–Roch counts. Over ℤ the same Gram,
  of `f` and `f∘R`, is RH, and the count mechanism is closed [L/D]. Missing: an exact signed payment of
  the collective kicks against the pole square on every reflection pair (P1 = P4 beyond the first
  stages), or archimedean positivity on signed prime-blind combinations (P2), or the reverse co-isometry
  inequality on resonances (P3), or collision exclusion along a source-faithful path (P5).

Evidence: `[L]` Lean; `[W]` working tree or draft module; `[D]` derived here; `[M]` model statement;
`[P]` paper.

## 0. The one object

| Reading | Statement | Anchor |
|---|---|---|
| Index | `κ = #{ρ : Re ρ > ½}` (distinct), even; RH ⇔ `κ < 2` | HKT, AKLT, AOG, ACS [L] |
| Window index | `ι(A)` monotone, `0` for `A ≤ 3/5`, `sup_A ι(A) = κ` | CWS, AHD [L] |
| Two sites | RH ⇔ `[[Q(ψ), c_ψ(t)],[c_ψ(t), Q(ψ)]] ≻ 0` ∀ψ, t; first failure two-site | GWZ [L] |
| Reflection pair | `W(f ± f∘R) = 2W(f) ± 2𝒞_m(f)`; band ⇔ positivity on the pair | SWC [L] |
| Parity sectors | odd ⇔ `𝒞₀(f) ≤ W(f)`, even ⇔ `−𝒞₀(f) ≤ W(f)` on half-window tests | SWC [L] |
| Orbit | RH ⇔ the orbit correlation of one generic bump is eventually bounded; rate = zero width | AOG [L] |
| Coupling | `𝒞_m(f) = 𝓗_m(f) − Σ_nw_n(f⋆f)(2m − log n)`; `𝓗_m` inertia `(1, ∞)` | SWC, CSTW [L] |
| Lattice | Weil sequences Toeplitz; RH ⇔ Schur parameters in `(−1,1)` ⇔ positive with `Σγ² = ∞` | GWZ [L] |
| Continuum (local) | `h^{−n(n−1)}det T_n → det J_n`, `J_n = [W(φ^{(i)},φ^{(j)})]` Hankel; `h^{−2n}E_n → det J_{n+1}/det J_n` | SWC [L] |
| Curve | degenerate window = finite curve; Spec ℤ under RH = infinite-angle curve `e^{iγ_ρh}` | GWZ [L] |
| Window algebra | truncated Dirichlet λ-ring; `ρ_A(Λ) = [M, log Z]`; Hilbert function `π_k(N)` | WTZ [L] |
| Window form | `Q = M + ½⟨c,·⟩² − ½⟨s,·⟩²`, `M` Markov with arithmetic jump rates; `M` dies at `e^{−3/4}` | RHTower, SWC [L] |
| Gauge form | `Ẑ(Φωu) = J_{Φω}(u) + ∫u²ω𝒢_S(ω) + 2V_s − 2V_c`; theta gauges critical on the line | SWC [L] |
| Kick | positive source `2w∫hh∘τu²` − anti-diagonal conductance `w∫hh∘τ(u − u∘τ)²`; local ratio `2we^h` | SWC [L] |
| Tate jet | `Q` = 1-jet at `k = 0` of the counts of `𝔸^k∖0`; positive dimension classified | WTZ, DZG, ATD [L] |
| Stage | `Q = Q_N − 2wc_H(ℓ)`; stage criterion on collar classes; kick = collar Rosati pairing | WTZ, GWZ [L] |
| Frozen form | closed form: moments at the trivial divisor + earlier-fold transports | CSTW [L] |
| Base | all real `C²` tests positive to length `≈ 0.7240`; odd unit window = one prime-two weight in a convex set | SPATL, GWZ, WTZ, SWC [L] |
| Floor | `Q ≥ −(deg K_A + 2sinh(A/2) − A)‖H‖²`; `Q ≥ −C(p)∫e^{−pu}H²`, `p > 1`; a floor with exponent `p` gives zero width `≤ p` | WTZ, SquareRootThreshold [L] |
| Complete family | PD below `(log N)^{1/8}`; whole space at one critical multiple; Weil at the frequency pole + counts; threshold `R₁(A)` | CACT, AHD [L] |
| Bulk | zeros below the grid read only the pole; growing overlap linear and polar | AHD [L] |
| Reflection | `Q = 2Re[𝓦H, 𝓦H]` on `ℓ²(zeros)`; window involution = twisted Krein reflection | RIT [L] |
| Lewis periods | co-isometry defect `≤ 0`, `= 0` iff `Re s = ¼`; retained `T₂` channel sign `¼ − Re s` | RIT [L] |
| Hecke | `T_p − Id` = Mellin translation for every prime; Hecke cones tile | RIT [L] |
| Camera | `W_Z(f,g) = Σm_ρf̂(γ_ρ)conj ĝ(conj γ_ρ)`; depth = tilt; finite modifications identified | ZCG [L] |
| Heat path | `H_t` real for `t ≥ 1/8`; RH ⇔ `H_0` real; non-real zeros for `t < 0` | RHTower DeBruijn [L] |
| Glued state | `κ(φ_c) = κ + 1` at every place | AKG [L] |
| Gluing determinant | Redheffer `det = M(N)` = nerve `χ̃` | ADT, HWV [L] |
| Kähler package | RH ⇔ HL on the PSD locus; zero modes = radical, parity, two-site at first failure | HWV, DZG, GWZ [L] |
| Weil cone | `⊆ {Λ}`; lattice selection; PBAP | RHTower, GWZ [L] |
| Window energy | abscissa = 2·maximal depth; ports; caps to `σ_m`; polynomial stage ⇔ RH | CDG [L] |
| Near-line density | eight forms; `D_win` ⇔ thin Planck shadows | CDG [L] |
| Gauge torus | pole-subtracted exponent range `[Θ, 1]`; first cyclotomic band abscissa `2Θ` | AGT, CAF [L] |
| Angles | `𝔽_q` angle ≡ ℤ frequency; pure curves sums of squares; monodromy rate = zero width | AHD [L] |
| Selberg class | Euler rigidity at `σ = ½`; degree gap `(0,1)`; degree one: conductor `≥ 2m₀` or a pole | SEL [L] |

## 0.1 The window axis

| Coordinate | Reading at window length `A` | Anchor |
|---|---|---|
| Window test | `H` on `[−A, 0]`; folds `T_n`, `n ≤ e^A` | CWS [L] |
| Reflection pair | `f` on `[m − A/2, m]`, mirror `f∘R`; primes `n` with `log n ≤ A` read through `(f⋆f)(2m − log n)` | SWC [L] |
| Two-site step | `t = A − r` for a bump of support `r`; primes `n` with `|log n − t| ≤ 2r` | GWZ, CSTW [L/D] |
| Lattice | total length `nh + r ≤ A`; margins `E_k(φ,h)`; local limit = jet Hankel | GWZ, SWC [L] |
| Stage | `log n ≤ A < log(n+1)`; collars of half-width `h = A/2 − (log n)/2` | WTZ, GWZ [L] |
| Collar locality | kick of `n` paid by its collar while `2Λ(n)n^{−1/2}e^h ≤ 1` | SWC [L]; [D] |
| Known sign | all tests `A ≤ 0.7240`; odd unit window reduced to one prime-two weight in a convex set (open) | SPATL, GWZ, WTZ, SWC [L] |
| Markov death | `A = e^{−3/4}` | SWC [L] |
| Tate horizon | `log₂(1+2√2)` (stage 1), `1.19966…` (stage 2), `≍ e^{−A/2}` | WTZ [L/N] |
| Critical multiple | a multiple `K` synthesizes tests of radius `½log K − O(1)`; `K ≤ K₀` pays every window (size-only) | AHD, WTZ [L] |
| Window threshold | `R₁(A) ≥ R₀`; `= ⊤` for `A ≤ 2·enlargedWeilFloorAperture`; RH ⇔ `⊤` for all `A` | AHD [L] |
| Ground energy | `μ(a) ≤ K exp((11/2)a − πe^{2(a−2)})`; floor `−Ce^{2σA}` ⇔ width `≤ σ` | M, SquareRootThreshold [L] |
| Contact aperture | `≥ 3/10`; `μ = 0` there off RH; bounded above by near-top zeros | SquareRootThreshold [L] |
| Height | paired lattice indistinguishable iff `X = e^{2a}` has `X² ≤ T` | SquareRootThreshold [M] |
| Camera exponent | columns of RvM density hide iff `a ≤ ½·½log(T/2π)` (`λ ≤ ½`) | ZCG [L] |
| Mayer coordinate | window map `𝓦_A`, `‖𝓦_A H‖² ≤ 20e^AT‖H‖²_{W^{2,1}}` | RIT [L] |
| Hecke translation | `T_p − Id`: window `A` → `A + log p`, similitude `p` | RIT [L] |
| Over `𝔽_q` | a curve with `2g` angles fails at lattice index `2g`; camera identifies above `g log q/2` | CWS, GWZ, AHD, ZCG [L] |

Each fixed window length is a sub-RH finite problem; all lengths together are RH; all steps of one
two-site lattice are RH.

## 0.2 The degeneration, angle and camera dictionary

| Object | Over ℤ | Over `𝔽_q` | Classes |
|---|---|---|---|
| Resolution axis | overlap `c`, `c⁸ ≍ K log N` | atom width `w` | C1 |
| First order | `J(1)#ℙ⁷(ℤ/m)` | narrow-width span Gram | C1, C13 |
| Twisted direction | frequency `u`: `½(ζ(β+1,u) + ζ(β+1,1−u))`, positive | angle `θ_i`: positive Hurwitz weight | C1, C18 |
| Trivial direction | pole of the frequency counts at `u = 0`; Weil's form at the pole | main term | C1, C18 |
| Lattice angles | `e^{iγ_ρh}` with weights `m_ρ|φ̂(γ_ρ)|²` (under RH); pole = hyperbolic pair `e^{±h/2}` | Frobenius eigenvalues; trivial `1, q` | C15, C18 |
| First failure | two-site, single angle `±1`; window minimizers edge-singular [W] | at index `2g` | C15, C19 |
| Monodromy | complete degeneration selects `Λ` | rate = zero width, both signs | C8, C18 |
| Camera threshold | `λ = ½` for columns of RvM density | aperture `g log q/2`, sharp (pure vs golden) | C21 |
| Reality | sign of `w²` at second order (prime channel curvature) | trace points `β + β⁻¹ ∈ [−2, 2]` | C5, C21 |
| Euler column | `A² ≤ 4p` ⇔ on the line | `p = 1` case: unit circle | C21, C20 |

## 1. Equivalence classes of routes

Routes in one class compute the same quantity; a theorem in one class transfers through the listed
identity.

| Class | Common quantity | Routes | Identity joining them |
|---|---|---|---|
| C1 Weil's window form | `Q ≥ 0` on windows of every length | HF, SRT, AIP, ACT, ACS-atomic; RW, EWU, OWU, MSC, FEL; ADT/AHD, CACT, CSAR | window ⇔ horizon ⇔ every `K·c*` ⇔ threshold `R₁ ≡ ⊤` ⇔ Beurling ⇔ `ι = 0` ⇔ fold capacity [L] — face of C19 |
| C2 Glued state | `κ(φ_c) − 1` | SC, AKG, RIT-Künneth | Grams are compressions on the Beurling schedule [L] — face of C1 |
| C3 Window integer | collision charge, heat count, window index | WD-charge, SC-heat, LA-heat, TG, HEF | index = Wiener–Hopf index = growth of `|𝒵(t)|²` [L] — face of C11 |
| C4 Sectors and ground states | odd/even sector sign; pole-charged gauges; folded jump process | CHMD, TT, AID, SAHT, OWU, EWU, ACT, SWC | parity sectors = band at the centre; odd-sector positivity ⇔ RH; gauge form [L] — face of C1 |
| C5 Rank / degree / continuation | Laguerre–Pólya; collision exclusion | TH, HCF, PA, GTA, LA, XN; ART; ZCG-deformation | inertia counts off-line pairs; reality lost only through collision; heat path critical at `0` [L/D] |
| C6 Scheduled prime sums | lower bound of a scheduled energy | FU, CFC, RP, SZ, LI, FEL, EGC | explicit-formula functionals bounded below ⇔ RH [L] |
| C7 One-point precision | `ψ − x`, `M(x)`, one cyclotomic mode, coupling, Redheffer, gauge exponent | WL, MC, PBM, RB, JAS, CTF, SC-coupling, AGT | one-sided count ⇔ RH; one mode carries `2Θ`; gauge spectrum `[Θ, 1]` [L] — face of C19 |
| C8 Selection / typicality | trivial gauge point; degeneration type | MC-typicality, BAG, XN; ADT, AHD | RH ⇔ trivial point typical [L] |
| C9 Realization | spectral reality of a constructed operator | RN, PTR, W1C, PM-Mayer | Mayer Krein positivity ⇔ RH; exact zero-coordinate realization [L] |
| C10 Pre-divisor | a section defined before the divisor | APF, BSH, CDC, EWJ, HJ, PCS, RFHM, SEC, WBF | zero-independent forcing (Γ5) |
| C11 Local zero location | window energy, Hecke defect, near-line density, census, clusters | WD-energy, WD-Hecke, census, HEF, SRT-local, IGP, TTPC | abscissa = 2·depth; eight-form density; thin Planck shadows [L] |
| C12 Hodge–Lefschetz / gluing | HL on the positive locus; zero modes; top gcd stratum | HF-Hodge, ACS-Hodge, RIT, EHT, TG, DZG, GWZ | zero modes = radical; first failure two-site [L] |
| C13 Sections, counts, Tate family | count-valued primitive `h¹`; naive height; Tate jet | ACS-effectivity, HF-RR, IRK, AE, WTZ, LST | Künneth `h¹ = ½Q`; Weil = Tate jet = signed count [L]; closed as a sign mechanism [D] |
| C14 Reflection | Rosati involution; Lewis defect; Krein form | PM-scattering, HF band poles, W1C, CWS Frobenius | exact completion; kick = collar Rosati pairing; co-isometry defect [L] — face of C1 |
| C15 Window tower and canonical system | `W_A`; stages; collars; lattices; Schur parameters; jet Hankel | CWS, WTZ, DZG, GWZ, CSTW, SWC; SZ | stage criterion; Levinson; jet Hankel limit; translation contraction [L] — meets C1, C4, C13, C14, C19 |
| C16 Prime-blind cone | archimedean + pole part on blind tests | PBAP | Weil cone `⊆ {Λ}`; zero-side identity [L] — face of C1 |
| C17 Dimension zero | domination of point counts | ATD, DZG (classified) | bare domination ⇔ `Q ≥ 0` [L] |
| C18 Angle dictionary | Hurwitz forms of angles / frequencies | AHD, ACS, LST, GWZ | angle `u` over `𝔽_q` ≡ frequency `u`; trivial angle = pole [L] |
| C19 Two-site band | `|𝒞_m(f)| ≤ W(f)` | GWZ, AOG, SWC; every route of C1, C4, C7, C14, C15 | RH ⇔ two-site PD; coupling = Hankel − smoothed count [L]: a reformulation, no mechanism |
| C20 Selberg-class rigidity | Euler-log discrepancy at `σ = ½`; degree; FE twins | SEL; ACS, HF fakes | Gamma-independent rigidity; degree gap [L] — selection calibration |
| C21 Configuration camera | identification of zero configurations by their Weil image | ZCG, SRT-identification, SquareRootThreshold | finite modifications identified; mimics need near-collisions; column threshold `λ = ½` [L] — selection without sign |

C1, C2, C4, C7, C14, C15, C16 and C17 are one quantity, read at its minimal size in C19. C3 is a face of
C11, and C11 is the growth of window negativity in `A`. C5 and C6 are sign problems on test families
that become RH-complete only in the limit of rank, degree, schedule or deformation time. C13 is the
production face of C19; C8–C10, C18, C20 and C21 are selection and calibration faces.

## U-Σ — the sign

Core problem: the band on every reflection pair; in tower form every prime kick lands in its prediction
interval (`2wc_H(ℓ) ≤ S^N_A(H)`; lattice `|β_n − kick| < E_n`), with frozen forms indefinite; in gauge form
a gauge in which the crossing prime conductances are dominated.

| Layer | Status | Anchor |
|---|---|---|
| Receivers | window, two-site, reflection pair, parity sectors, lattice, translation contraction, horizon, threshold, schedule, `K·c*`, index, fold capacity, Krein, PBAP, domination | CWS, GWZ, CSTW, AHD, SWC, RIT, TM, CHMD, RHTower, DZG [L] |
| Minimal object | reflection pair; first failure two-site; window minimizers edge-singular | GWZ, SWC [L/W] |
| Canonical system | Levinson recursion; Schur parameters; outer predictors; Carathéodory–Fejér; jet Hankel limit | GWZ, SWC [L] |
| Stage | two-collar form; kick law; collar Rosati sectors; frozen form in closed form | GWZ, CSTW [L] |
| Gauge calculus | pole-charged representation; theta gauges critical on the line; outside charges | SWC [L] |
| Locality | collar ratio `2we^h`, sharp; prime `3` unpaid; odd light cone `≥ 0` | SWC [L] |
| Archimedean transmission | trivial divisor: pole `+`, trivial zeros `−`; collar Hankel inertia `(1, ∞)` | CSTW, SWC [L] |
| Entrance and base | exit charge; composite stages free; base to `≈ 0.7240`; Markov death at `e^{−3/4}` | WTZ, SPATL, GWZ, SWC [L] |
| First prime stage | frozen form indefinite; flip rejected; odd unit window one number | WTZ, SWC [L] |
| Budget | sharp floor; aperture-independent floor (size-only); growth exponent = width; canonical-degree horizons | WTZ, AHD, SquareRootThreshold [L] |
| Complete family | subcritical PD; whole space at one critical multiple; threshold law | CACT, AHD [L] |
| Zero modes | radical; parity; gap law; end-collar injectivity; tight band ⇒ reflection-pair zero mode | DZG, GWZ, SWC [L] |
| No slack | Weil cone a point; doubly-exponential margins; Szegő singular; theta gauges critical | RHTower, M, GWZ, SWC [L] |
| Continuation | heat path real for `t ≥ 1/8`, non-real for `t < 0`; collision exit | RHTower DeBruijn, ZCG [L] |
| Dimension zero | classified | DZG, ATD [L] |

| Face | Routes / programmes | Reduction |
|---|---|---|
| Complete atomic matrix | HF, SRT, AIP, ACT, ACS-atomic, CACT, CAF, CSAR, ACPL, RAPT, SSH, SSHA, TM, ADT, AHD | size-only layers closed; threshold `R₁ ≡ ⊤` = untwisted windows at every ratio |
| Aperture ground minimum | RW, EWU, OWU, MSC, CFC, SP | window sign by stages; reflection pairs |
| Sectors / ground states | CHMD, AID, SAHT, TT, ACT, OWU, EWU, SWC | frustration domination in a gauge |
| Glued state | SC, AKG | Beurling-schedule sign |
| Window tower / canonical system | CWS, WTZ, DZG, GWZ, CSTW, SWC | kick admission; two sites |
| Dimension zero | ATD, DZG | equivalent to the window sign |
| Edge / zero modes / Kähler | EHT, HWV, RW, DZG, GWZ | no zero mode; first failure two-site |
| Stars / gluing | HWV, CSAR, ADT | top gcd stratum |
| Effectivity / RR | ACS, LST, RIT, HF, AE | count-valued Hodge index; closed as a mechanism [D] |
| Rank / degree / continuation | TH, LA, HCF, PA, GTA, XN, ART, ZCG | Laguerre–Pólya; collision exclusion |
| Scheduled prime sums | FU, CFC, RP, SZ, LI, FEL, EGC | scheduled energy lower bound |
| Screw / Krein–Schur | SZ | the canonical system of GWZ/CSTW |
| Paths | TG, SC, EHT, ACPL, HWV | source-defined HL along a flow |
| Realization | RN, PTR, W1C, PM | Krein positivity of zero coordinates |
| Prime-blind | PBAP | signed blind combinations |

## U-Π — precision and production

Core problem: square-root precision of one smoothed short-window prime count — the band read on the
prime side, `|Σ_nw_n(f⋆f)(2m − log n) − 𝓗_m(f)| ≤ W(f)` — and its production by an exact mechanism.

| Face | Routes / programmes | Reduction |
|---|---|---|
| Reflection-pair coupling | SWC, GWZ, CSTW, AOG | collar Hankel − smoothed count within `W(f)` (Π4) |
| Collective kicks | SWC, OWU, RW | kicks beyond collar locality = the smoothed count (Π30) |
| One-sided prime count | WL, PBM, RB, JAS, CTF, ACP, ASRP | `ψ(x) − x ≤ C√x log²x` (Π1) |
| One cyclotomic mode | MC, CAF | first-band energy `O(N^{1+ε})` (Π10) |
| Gauge torus | WL, MC, AGT | exponent `½` at the trivial point (Π28) |
| Windowed kernel / coupling | SC, ACPL, AKG, HKT | bounded `K_ζ` ⇔ bounded dense coupling (Π4, Σ17) |
| Integer producers | WL, AKLT, AHA | `ε`-uniform producer (Π3) |
| Möbius / nerve | MC, BVI, CAF, HWV, ADT | half-power cancellation; `χ̃ = −M(N)` |
| Window budget | CWS, WTZ, SRT, AHD | growth exponent = width (Σ28); size-only floor (Σ1o) |
| Window energy | WD, TG, CDG | inner caps (Π17, Π23) |
| Near-line density | WD, CDG, RBG, HEF, census | eight forms; thin Planck shadows (Π5, Π22) |
| Census / clusters | SRT, IGP, Zeta23, CDG, TTPC | signed pair data beyond bandwidth one; cluster detection (Π7) |
| Square-root threshold | ZCG, SquareRootThreshold | `λ = ½` for columns; Riemann–Siegel length (Π29) |
| Tate jet / parity | WTZ, DZG, ATD, AHD | classified (Π24, Π25) |
| Sections / heights | ACS, LST, AOG, AET, AE, RIT, SPTL, CWS | closed as a mechanism (Π11h, Σ31) [D] |
| Bulk second order | AHD, ArtinMertens | Stieltjes constants, `L'/L(1,χ)`, polar growth (Π26) |
| Finite realizations | RIT, CWS | no-go (Π18) |
| Genus | ACS, RHTower, LST, CWS, WTZ | upper law open (Π16) |
| Averages vs heights | WD, LA, SRT | density-zero exceptions; double-log stage (Π6) |
| Candidates | APF, EWJ, FEL, WBF, IRK | integral counts from a source lift |

Identities [L]: one-sided count ⇔ `κ = 0`; reflection-pair coupling = collar Hankel − smoothed count;
coupling rate = orbit-correlation rate = zero width; window-energy abscissa = twice the maximal depth;
first cyclotomic band abscissa `2Θ`; gauge-torus exponent range `[Θ, 1]`; Weil's window form = Tate jet =
signed count; Künneth `h¹` = counts + `½Q`; first-order degeneration term = point count over every
finite ring.

## U-Γ — selection and reflection

Core problem: a source-defined mechanism making the reflection `ρ ↦ 1 − ρ̄` act as a positivity. The
distinguishing half is closed: flips separated at every density, Weil cone a point, lattice selection of
`Λ`, Selberg-class rigidity, identification of finite modifications by the primes. The reflection is
constructed exactly on both sides and identified: completed PM space `ℓ²(zeros)`, Hecke = translation,
window involution = twisted Krein reflection, kick = collar Rosati pairing; the resonant co-isometry
defect is `≤ 0`. Positivity of the reflection is RH.

| Face | Routes / programmes | Status / reduction |
|---|---|---|
| Typicality of the trivial point | MC, AGT, BAG, XN | Γ1; explicit `½` point off the special locus |
| Gluing of the global pole | SC, AKG, RIT | classified (Σ11, Γ11) |
| Margin, index, edge, degeneration selection | RIT, ACP, HKT, EHT, ACPL, RAPT, ADT, BGG | flips separated; only `Λ` degenerates completely (Γ2, Γ12, Γ18) |
| Weil cone / certificates / lattices | RHTower, BSU, GWZ | `{Λ}`; lattice selection (Γ23) |
| Selberg class | SEL | Euler rigidity; degree gap; degree-one conductor or pole (Γ15, Γ33) |
| Camera identification | ZCG, SRT | finite modifications and separated configurations identified; mimics need near-collisions (Γ36) |
| Euler columns | ZCG | Ramanujan = reality; hide below `log p/2` (Γ37) |
| Window selection | CWS | bounded windows blind (Γ20) |
| Density selection | ACPL | RvM-count countermodels (Γ21) |
| Tate counts | WTZ, DZG | do not descend (Γ27) |
| Window Frobenius | DZG, WTZ, RIT | similitudes scalar; Frobenius = translation (Γ28) |
| Intertwining coefficient | PM, RIT, RHTower | band poles = Hodge defect (Σ19, Γ22) |
| Frobenius at infinity | PL, CDG, RBG, EHT, AOG, AET, CWS, WTZ, GWZ | Rosati involution; collar Rosati pairing (Γ4, Γ19) |
| Mayer reflection | PM, W1C | defect `≤ 0`, zero on the quarter line; reverse inequality open (Γ24, Γ29, Γ32) |
| Retained channel | PM | side detector (Γ38) |
| Hecke structure | PM | cones tile; periods eigenfunctions for every prime (Γ34) |
| Resonant-state statistics | PM | retain the rate (Γ26) |
| Physical / native source | PM; PW-B retired | (Γ13, Γ17) |
| Pre-divisor constructions | BSH, CDC, HJ, SEC, PCS, RFHM, EWJ, APF, WBF | zero-independent forcing (Γ5) |
| Function-field calibration | ACS, AKG, RIT, EHT, ACPL, LST, HWV, AET, AHD, CWS, WTZ, GWZ, ZCG | angle dictionary; curves fail at their number of angles; camera certifies purity above `g log q/2` (Γ10, Γ31) |
| Selection → sign | all selectors | no selector gives positivity (Γ16) |

## 2. Cross-family seams

| Seam | Statement | Routes on the seam |
|---|---|---|
| Σ ∩ Π: reflection pairs | `W(f ± f∘R) = 2W(f) ± 2𝒞_m(f)`, `𝒞_m` = collar Hankel − smoothed count | SWC, GWZ, CSTW, AOG, WL [L] |
| Σ ∩ Π: collective kicks | kicks outside the collar-certified range need resources beyond their collar; summed over a reflection pair all kicks are the smoothed count | SWC [L]; [D] |
| Σ ∩ Γ: exact completion | Weil energy = Krein form of zero coordinates; reflection = window involution | RIT, WTZ [L] |
| Σ: one canonical system | Levinson recursion; Szegő singular under RH; jet Hankel limit | GWZ, SWC [L] |
| Σ: one location | each fold = one collar-to-collar correlation; kick = source − anti-diagonal conductance | WTZ, GWZ, CSTW, SWC [L] |
| Σ: one gauge calculus | pole-charged representation; theta gauges critical on the line | SWC, ACT [L] |
| Σ ∩ Π: trivial divisor | the archimedean place transmits only moments at `s = 1, −2k`; collar Hankel inertia `(1, ∞)` | CSTW, SWC [L] |
| Σ ∩ Π ∩ Γ: dimension zero | positive dimension classified | WTZ, DZG, ATD, AHD [L] |
| Σ: one decomposition | counts on every twisted direction + Weil at the frequency pole; threshold law | ADT, AHD [L] |
| Σ ∩ Π: growth exponent | ground-energy growth exponent = zero width; a floor with exponent `p` gives width `≤ p`; the size-only `p > 1` carries none | WTZ, AHD, SquareRootThreshold [L]; [D] |
| Σ: frozen indefiniteness | the new fold is a positive source; cost-only payments refuted | WTZ, SWC [L] |
| Σ ∩ Γ: zero modes | radical, parity, two-site at first failure; edge-singular window minimizers | DZG, GWZ, SWC [L/W] |
| Σ: curves | degenerate windows are finite curves; curves fail at their number of angles | GWZ [L] |
| Σ: one axis | window length = total lattice length = two-site step + support = radius `½log K` = log of the matched height (model) | AHD, GWZ, SquareRootThreshold [L/M] |
| Σ ∩ Π: no slack | Weil cone a point; doubly-exponential margins; Szegő singular; heat path critical | RHTower, M, GWZ, DeBruijn [L] |
| Σ ∩ Π: one gluing | Redheffer, nerve `χ̃`, glued index | ADT, HWV, AKG, MC [L] |
| Σ ∩ Π ∩ Γ: counts | Künneth counts pay all but `½Q`; no count produces the sign | CWS, WTZ, LST, AE, ACS, RIT, ATD, DZG [L]; [D] |
| Σ ∩ Γ: angle dictionary | angle over `𝔽_q` ≡ frequency over ℤ; trivial angle = pole | AHD [L] |
| Σ ∩ Γ: one Frobenius | Frobenius at scale `t` = translation; Hecke = Mellin translation | DZG, RIT [L] |
| Σ ∩ Γ: camera and reality | identification is sign-free; reality at a near-collision is a second-order sign read through `(log n)²`-weighted primes | ZCG [L] |
| Π ∩ Γ: square-root threshold | column threshold `λ = ½` = paired-lattice boundary = Riemann–Siegel length | ZCG, SquareRootThreshold [L/M]; [D] |
| Σ: continuation | reality lost only through collision; heat steps keep mesh and depth (model) | ZCG, LA, DeBruijn [L] |
| Π: window integer = window power sum | collision charge = Wiener–Hopf index | WD, TG, SC-heat [L] |
| Π: one density statement | eight forms; thin Planck shadows | WD, CDG, census, MC, HEF [L] |
| Π: one mode, one torus | first cyclotomic band carries `2Θ`; gauge exponent range `[Θ, 1]` | MC, CAF, AGT [L] |
| Π: bulk | Stieltjes constants; `L'/L(1,χ)`; polar growth along growing overlap | AHD, ArtinMertens [L] |
| Σ ∩ Π: length–height | contact aperture; paired-lattice boundary `X² ≤ T`; cluster detector | SquareRootThreshold, SRT [L/M] |
| Γ: one point, one cone | Weil cone `{Λ}`; lattice selection; prime-blind nonemptiness | RHTower, GWZ [L] |
| Γ: blind selectors | bounded windows, densities, contractions, local twists, Tate counts, resonant statistics, retained channel | CWS, ACPL, RIT, AKLT, WTZ [L] |
| Σ: approximation | RH-true approximants close into Laguerre–Pólya | ART, W1C, PTR, LA, TH |
| Archimedean channel | Lévy jumps, exit charge, end profile, trivial-divisor transmission, collar light cone, archimedean Tate family | AKG, ALG, CHMD, RIT, ACPL, HWV, ACS, LST, ADT, CWS, WTZ, DZG, ATD, CSTW, SWC |

## 3. Route → core map

| Route | Core | Class | Face |
|---|---|---|---|
| WL | Π | C7, C19 | one-sided count; reflection-pair coupling |
| RW, EWU, OWU | Σ | C1, C4, C15, C19 | window sign by stages; parity sectors; reflection pairs |
| FU, CFC, RP, SZ, LI | Σ | C6 | scheduled prime sums; SZ also the Krein–Schur carrier of C15 |
| PA, TH, LA, HCF, GTA, XN | Σ | C5 | Laguerre–Pólya; continuation |
| MC | Π (Γ) | C7, C8 | Möbius cancellation; one mode; gauge torus; Redheffer; typicality |
| TT | Σ | C4 | odd sector / directed covariance |
| TG | Π, Σ | C3, C12 | window integer; HL along paths |
| HF | Σ (Π, Γ) | C1, C12, C13, C14, C15, C18 | complete family; threshold `R₁ ≡ ⊤`; correspondences; Frobenius = translation |
| SRT, AIP, ACT | Σ (Π) | C1, C4, C11, C21 | complete atomic matrix; pencil index; cluster detection; identification |
| SC | Σ, Π (Γ) | C2, C7, C3 | glued state; damped coupling; heat |
| CHMD | Σ | C4, C1 | odd sector |
| RN | Σ | C9 | realization |
| WD | Π (Σ) | C3, C11 | window energy; inner caps; near-line density |
| PM | Γ (Σ) | C9, C14 | exact zero-coordinate Krein space; co-isometry defect; Hecke = translation |
| JAS, CTF, PBM, RB | Π | C7, C19 | one-sided count |
| BAG | Γ | C8 | typicality / recurrence |
| ACS | Π (Σ, Γ) | C13, C1, C12, C15, C18, C20 | count face closed; sign content = Weil's window form; fakes; Selberg rigidity |
| APF, EWJ, WBF, IRK | Γ (Π) | C10, C13 | source lift with integral count |
| BSH, CDC, HJ, SEC, PCS, RFHM | Γ | C10 | pre-divisor constructions |
| EGC, FEL, MSC | Σ | C6, C1 | contour / likelihood / Sonin |
| PTR, W1C | Σ (Γ) | C9, C5, C14 | realization; Krein form of zero coordinates |
| ZCG | Γ (Σ) | C21, C5 | camera identification; reality at near-collisions; continuation |
| PW-B (retired) | Γ | C14 | survivor = scattering receiver |
| PBAP (support) | Γ (Σ) | C16 | prime-blind positivity |

## 4. What a closing argument must supply

| Needed | Present over ℤ | Missing |
|---|---|---|
| Sign of the minimal object | RH ⇔ the band on reflection pairs; explicit coupling; every prime power necessary | the band at every step (B1) |
| Mechanism for the sign | pole-charged gauge calculus; theta gauges critical on the line; kick = source − conductance; collar ratio sharp; Levinson admission; base to `0.7240` | an exact signed payment of the collective kicks against the pole square (B3), first for the odd unit window (B4) and the prime `3` (B5); cost-only, sign-blind, Markov and finite certificates excluded |
| Full-space structure | subcritical PD; whole space at one critical multiple; threshold law | `R₁(A) = ⊤` for every `A` (B7); twisted sector at every multiple (B6) |
| Uniformity in `A` | each length finite; growth exponent = width; contact aperture defined | the contact law (B18); window negativity exponent `< ½` (B16) |
| Nondegeneracy | zero modes = radical, parity, two-site at first failure; edge-singular minimizers [W] | no degenerate two-site lattice (B10) |
| Precision | one-sided count ⇔ RH; one mode carries `2Θ`; gauge spectrum `[Θ,1]`; eight-form density; caps to `σ_m` | square-root size of one smoothed count; inner caps (B19); `D_win` (B21) |
| Count from geometry | Künneth `h¹ = ½Q`; Weil's form a signed count; finite-field Stepanov | — (closed: no count produces the sign [D]) |
| Canonical selector | Weil cone `{Λ}`; lattice selection; Selberg rigidity; identification by the primes | — (automatic after positivity) |
| Reflection | exact zero-coordinate Krein space; defect `≤ 0` with equality on the quarter line; side detector | the reverse inequality on resonances (B38) |
| Reality by continuation | heat path real for `t ≥ 1/8`; collision exit theorem; mesh and depth monotone (model) | collision exclusion on `(0, 1/8]` (B14) |
| Integrality with homotopy invariance | window index; `{0, ∞}` laws | a zero–one law for `κ` (B13); a structural bound on the window index (B12) |
