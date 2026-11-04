# Route unification ledger — status quo

The 32 live routes and 17 candidates are faces of three core problems — **U-Σ** (sign), **U-Π**
(precision and production), **U-Γ** (selection and reflection) — and the three are one statement read
three ways: the **band** `|𝒞_m(f)| ≤ W(f)` of a test `f` and its mirror image `f∘R`, `R(v) = 2m − v`,
with `𝒞_m(f) = 𝓗_m(f) − Σ_nΛ(n)n^{−1/2}(f⋆f)(2m − log n)`. All read one even integer
`κ = κ(K_ζ) = #` distinct zeros right of the critical line, on one object, the window tower `A ↦ W_A`,
and all are decided on its smallest piece, the reflection pair.

- **One criterion, one minimal object.** Every sign face is Weil's form on windows of every length [L];
  windows are decided on two sites [L]; the parity sectors of a window are the band at its centre [L].
- **Sign = precision.** `W(f ± f∘R) = 2W(f) ± 2𝒞_m(f)`; `𝒞_m` = collar Hankel form minus smoothed prime
  count [L]: U-Σ on a reflection pair is U-Π at one scale. Below window length `log 4` this is a two-term
  prime count `w₂(f⋆f)(−log 2) + w₃(f⋆f)(−log 3)` matching `𝓗₀(f)` within the purely archimedean–polar
  `W(f)`, and the whole sign is the membership of `(Λ(2)/√2, Λ(3)/√3)` in an explicit compact convex set [L].
- **Reflection = zero side.** `Q(H) = 2Re[𝓦H, 𝓦H]` on `ℓ²(zeros)`; Hecke is translation; the window
  involution is the twisted Krein reflection [L]; the co-isometry defect of a fixed period is
  `−∫2cosh(δu)4sinh²(δu)|F(u)F(−u)|`, `δ = 2Re s − ½` [L]: U-Γ's positivity is U-Σ in zero coordinates,
  and at a resonance it is the identity `δ = 0` [D].
- **One moment problem.** Even sector ⇔ Hamburger, odd sector ⇔ shifted Hamburger, window ⇔ Stieltjes
  for the jet energies `s_k = W(φ^{(k)})` of every even bump [L]; the theta Hankel tower at one centre is
  the same kind of moment problem for the theta source [L]; Jensen polynomials are its Pólya–Schur form.
- **One canonical system.** Lattices: Szegő–Levinson theory, Szegő singular under RH [L]. Continuum:
  margins `h^{−2n}E_n → det J_{n+1}/det J_n`, reflection coefficients freezing at `(−1)^n` with normal
  velocity `e_{n+1}/e_n`, parity split `det J_n = det E·det O` [L]. The global Hamiltonian is not
  constructed.
- **One location.** The fold of an entering prime couples the two collars; its reflection term is the signature of the
  sliver reflection, `(f⋆f)(−ℓ) = ∫_I(f₊² − f₋²)` [L]; first failures are two-site; window extremals are
  never smooth and live at the edge [L].
- **One gauge calculus and one certificate format.** In a gauge the window form is a signed Dirichlet form
  plus pole charges; theta gauges are critical on the line [L]; below `log 4` retained-variance theta
  gauges (even) and shifted ground states (odd) are exact certificates, and dropping the variance fails
  [L].
- **One locality law and one payment law.** Collar-internal jumps pay the kick of `n` at ratio
  `2w_ne^h`, sharp; outward jumps carry the newest prime power at `w_ne^h/2` [L]; the edge-law bound on the
  summed reflection terms stays below the Lévy energy on windows shorter than `log 5` [D], and still the primes must pay the prime-free
  deficit by sign [L].
- **One decomposition, one pole, one threshold.** At the critical curve the complete family is Weil's form
  at the pole `u = 0` of the frequency counts plus positive counts; `R₁(A) = ⊤` ∀A ⇔ RH; every terminal
  source is polar [L].
- **One growth exponent and one depth law.** The fall rate of the window ground energy is the zero width,
  two-sided for finitely many off-line zeros; window positivity at `R` excludes depth `≥ 1/R` up to height
  `e^{R/polylog R}` [L]; an isolated zero of depth `δ` at height `T` is seen at half-width
  `≈ (1/2δ)log log T`, spread lattice-like sets hide up to `¼log T` [D]: windows read depth, the camera reads
  density.
- **One Frobenius.** Frobenius at scale `t` is translation by `t` [L].
- **One point and one cone.** The Weil cone is `{Λ}` or empty [L].
- **One camera and one density aperture.** The explicit formula identifies configurations exactly up to
  the density `2a/π` of cancelling clusters; blindness costs exactly `πD`; positivity at one aperture
  certifies thin configurations above `πD` [L]; for `ζ` at height `T` the threshold is `a = ¼log(T/2π)`,
  camera exponent `λ = ½`, the Riemann–Siegel length [D].
- **One deformation and one phase.** Reality is lost only through collision [L]; RH ⇔ every zero of
  `H_t` simple ∀t > 0 ⇔ `Λ_X = 0` ∀X [L]; Euler stages `A_X(s) + A_X(1−s)` have a monotone phase and
  simple line zeros above their horizon [L] — a Hermite–Biehler phase, the structure that Levinson–Conrey
  counting and de Branges canonical systems read [D].
- **One criticality.** Every exact reading sits on a zero-slack boundary [L/D].
- **One missing mechanism.** Over `𝔽_q` the Gram of the diagonal and the graph of Frobenius is positive on
  primitive classes by the Hodge index (proved from Riemann–Roch counts), and integrality of the image
  forces collide-or-repel [L]. Over ℤ the same Gram, of `f` and `f∘R`, is RH, the count mechanism is closed,
  and the image is a `log p`-weighted sum without discreteness [L/D]. Missing: a signed payment of the
  collective kicks against the pole square on every reflection pair (P1 = P4), or archimedean positivity on
  signed prime-blind combinations (P2), or an arithmetic expression of the PM defect with manifest sign
  (P3), or collision exclusion along a source-faithful path (P5).

Evidence: `[L]` committed Lean; `[W]` working-tree Lean; `[D]` derived here; `[M]` model; `[P]` paper.

## 0. The one object

| Reading | Statement | Anchor |
|---|---|---|
| Index | `κ = #{ρ : Re ρ > ½}` (distinct), even; RH ⇔ `κ < 2` | HKT, AKLT, AOG, ACS [L] |
| Window index | `ι(A)` monotone, `0` for `A ≤ 3/5`, `sup_A ι(A) = κ` | CWS, AHD [L] |
| Two sites | RH ⇔ `[[Q(ψ), c_ψ(t)],[c_ψ(t), Q(ψ)]] ≻ 0` ∀ψ, t | GWZ [L] |
| Reflection pair | `W(f ± f∘R) = 2W(f) ± 2𝒞_m(f)` | SWC [L] |
| Parity sectors | odd ⇔ `𝒞₀(f) ≤ W(f)`, even ⇔ `−𝒞₀(f) ≤ W(f)` | SWC [L] |
| Below `log 4` | positivity ⇔ `(w₂, w₃) ∈ oddBandWeights c ∩ evenBandWeights c`; prime-free half-window iff `c ≤ log 2` | SWC [L] |
| Sliver | `(f⋆f)(−ℓ) = ∫_I(f₊² − f₋²)`, `I = [−c, c − ℓ]`; `w_n|(f⋆f)(−log n)| ≤ (Λ(n)e^c/(2n))·levyEnergy` | SWC [L] |
| Moments | even ⇔ Hamburger, odd ⇔ shifted Hamburger, window ⇔ Stieltjes for `s_k = W(φ^{(k)})` | SWC [L] |
| Orbit | RH ⇔ the orbit correlation of one generic bump eventually bounded; rate = zero width | AOG [L] |
| Coupling | `𝒞_m(f) = 𝓗_m(f) − Σ_nw_n(f⋆f)(2m − log n)`; `𝓗_m` inertia `(1, ∞)` | SWC, CSTW [L] |
| Lattice | RH ⇔ Schur parameters in `(−1,1)` | GWZ [L] |
| Continuum | `h^{−2n}E_n → det J_{n+1}/det J_n`; `γ_n → (−1)^n`; `det J_n = det E·det O` | SWC [L] |
| Edge | no smooth eigenfunction, constrained ground state or capacity maximizer | SWC [L] |
| Curve | degenerate window = finite curve; Spec ℤ under RH = infinite-angle curve | GWZ [L] |
| Window algebra | truncated Dirichlet λ-ring; `ρ_A(Λ) = [M, log Z]` | WTZ [L] |
| Window form | `Q = M + ½⟨c,·⟩² − ½⟨s,·⟩²`, `M` Markov, dies at `e^{−3/4}` | RHTower, SWC [L] |
| Gauge form | `Ẑ(Φωu) = J_{Φω}(u) + ∫u²ω𝒢_S(ω) + 2V_s − 2V_c`; variance = all-pairs jump form | SWC [L] |
| Gamma ladder | `A(g)‖g'‖² ≤ A(g')‖g‖²`; pole `+` to even, `−` to odd | SWC [L] |
| Tate jet | `Q` = 1-jet at `k = 0` of the counts of `𝔸^k∖0` | WTZ, DZG, ATD [L] |
| Stage | `Q = Q_N − 2wc_H(ℓ)`; soft entry `ηΩ(2c − log p)` | WTZ, GWZ, SWC [L] |
| Base | all real `C²` tests positive to length `≈ 0.7240` | SPATL, GWZ, AIP [L] |
| Floor | `Q ≥ −C(p)∫e^{−pu}H²`, `p > 1`; exponent `p` ⇒ width `≤ p` | WTZ, SquareRootThreshold [L] |
| Complete family | PD below `(log N)^{1/8}` and at one critical multiple; threshold `R₁(A)`; terminal source polar | CACT, AHD [L] |
| Reflection | `Q = 2Re[𝓦H, 𝓦H]`; window involution = twisted Krein reflection | RIT [L] |
| Lewis periods | `D_s ≤ 0`, `= 0` iff `Re s = ¼`; `D_s = −∫2cosh(δu)4sinh²(δu)|F(u)F(−u)|`; retained `T₂` sign `¼ − Re s` | RIT [L] |
| Camera | `W_Z(f,g) = Σm_ρf̂(γ_ρ)conj ĝ(conj γ_ρ)`; cancelling clusters density `≥ 2a/π` | ZCG [L] |
| Blindness | aperture `πD` exact; ⇔ entire functions of exponential type vanishing on the set | ZCG [L] |
| Heat path | real for `t ≥ 1/8`; RH ⇔ all positive-time zeros simple ⇔ `Λ_X = 0` ∀X | RHTower DeBruijn [L] |
| Euler stage | `Λ_X = A_X(s) + A_X(1−s)`: monotone phase, simple line zeros above `2πe^{W(X)}` | ZCG [L] |
| Glued state | `κ(φ_c) = κ + 1` | AKG [L] |
| Gluing determinant | Redheffer `det = M(N)` = nerve `χ̃` | ADT, HWV [L] |
| Kähler package | RH ⇔ HL on the PSD locus | HWV, DZG, GWZ [L] |
| Weil cone | `⊆ {Λ}`; lattice selection; PBAP | RHTower, GWZ [L] |
| Window energy | abscissa = 2·maximal depth; caps to `σ_m`; polynomial stage ⇔ RH | CDG [L] |
| Near-line density | eight forms; `D_win` ⇔ thin Planck shadows | CDG [L] |
| Gauge torus | exponent range `[Θ, 1]`; first cyclotomic band abscissa `2Θ` | AGT, CAF [L] |
| Angles | `𝔽_q` angle ≡ ℤ frequency; curve camera identifies at the genus | AHD, ZCG [L] |
| Selberg class | Euler rigidity at `σ = ½`; degree gap; degree one: conductor `≥ 2` or a pole | SEL [L] |
| Legendre invariant | RH ⇔ `J(ρ) ∈ ℝ` at every zero | KPA [L] |

## 0.1 The window axis

| Coordinate | Reading at half-width `c` (length `2c`) | Anchor |
|---|---|---|
| Window test | `H` on `[−A, 0]` or `[−c, c]`; folds `T_n`, `n ≤ e^{2c}` | CWS [L] |
| Reflection pair | `f` on `[m − c, m]`; primes with `log n ≤ 2c` read through `(f⋆f)(2m − log n)` | SWC [L] |
| Sliver of `n` | `[−c, c − log n]`, width `δ = 2c − log n` | SWC [L] |
| Known sign | all tests `2c ≤ 0.7240`; floor up to `c = enlargedWeilFloorAperture` | SPATL, AIP [L] |
| Markov death | length `e^{−3/4}` | SWC [L] |
| First prime stage | `2c = 21/20`: prime-two weights exclude `0` and `−w₂`; `c ≥ 21/40`: `w₂ ≤ 0` excluded | WTZ, SWC [L] |
| Odd unit window | `c = ½`: one weight `w₂` in a convex set (open) | SWC [L] |
| Prime-three entry | `2c = log 3`: sector sets cylinders in `w₃` before; compact after; soft entry `ηΩ(δ)` | SWC [L] |
| Sliver potential | fails for `c ≥ 287/500` | SWC [W] |
| Variance-free certificates | fail for `c > 273/400` | SWC [L] |
| Prime-free half-window | sharp at `c = log 2` (`2c = log 4`) | SWC [L] |
| Reflection-term bound below Lévy | windows `2c < log 5` | SWC [L/D] |
| Tate horizon | `log₂(1+2√2)` (stage 1), `1.19966…` (stage 2) | WTZ [L/N] |
| Critical multiple | `K` synthesizes tests of radius `½log K − O(1)` | AHD, WTZ [L] |
| Window threshold | `R₁(A) ≥ R₀`; `= ⊤` up to `2·enlargedWeilFloorAperture` | AHD [L] |
| Ground energy | `μ(a) ≤ K exp((11/2)a − πe^{2(a−2)})` | M [L] |
| Excluded depth | positivity at `R` ⇒ no zero of depth `≥ 1/R` up to height `e^{R/polylog R}`; isolated depth `δ` seen at `≈ (1/2δ)log log T` | SquareRootThreshold [L]; [D] |
| Height | paired lattice indistinguishable iff `X = e^{2a}` has `X² ≤ T` | SquareRootThreshold [M] |
| Camera exponent | clusters of `ζ` at height `T` isolable iff `a > ¼log(T/2π)` (`λ > ½`) | ZCG [L/D] |
| Mayer coordinate | window map `𝓦_A`; window tests lift to `+1` fixed periods | RIT [L] |
| Hecke translation | `T_p − Id`: window `A` → `A + log p`, similitude `p` | RIT [L] |
| Over `𝔽_q` | a curve with `2g` angles fails at lattice index `2g`; camera identifies at order `g` | CWS, GWZ, ZCG [L] |

Each fixed window length is a sub-RH finite problem; all lengths together are RH; all steps of one
two-site lattice are RH.

## 0.2 The degeneration, angle and camera dictionary

| Object | Over ℤ | Over `𝔽_q` | Classes |
|---|---|---|---|
| Resolution axis | overlap `c`, `c⁸ ≍ K log N` | atom width `w` | C1 |
| Twisted direction | frequency `u`: positive Hurwitz count | angle `θ_i`: positive Hurwitz weight | C1, C18 |
| Trivial direction | pole of the frequency counts at `u = 0` | main term | C1, C18 |
| Lattice angles | `e^{iγ_ρh}` with weights `m_ρ|φ̂(γ_ρ)|²`; pole = hyperbolic pair | Frobenius eigenvalues | C15, C18 |
| First failure | two-site, single angle `±1`; extremals edge-singular | at index `2g` | C15, C19 |
| Camera threshold | `λ = ½`: pair-isolation aperture of RvM density | order `g`: camera identifies at the genus | C21, C23 |
| Certification by size | none (unbounded density) | bounded image at all orders ⇔ purity | C21 |
| Certification by sign | positivity at one aperture above `πD` for thin configurations | positivity at `a > g log q` | C21, C23 |
| Repulsion | archimedean phase speed above the Euler-stage horizon; none at `ζ`'s scale | integrality: collide or repel | C5, C24 |
| Reality | sign of `w²` at second order (prime channel curvature) | trace points `β + β⁻¹ ∈ [−2, 2]` | C5, C21 |
| Euler column | `A² ≤ 4p` ⇔ on the line | unit circle | C21, C20 |

## 1. Equivalence classes of routes

Routes in one class compute the same quantity; a theorem in one class transfers through the listed
identity.

| Class | Common quantity | Routes | Identity joining them |
|---|---|---|---|
| C1 Weil's window form | `Q ≥ 0` on windows of every length | HF, SRT, AIP, ACT, ACS-atomic; RW, EWU, OWU, MSC, FEL; ADT/AHD, CACT, CSAR | window ⇔ horizon ⇔ threshold `R₁ ≡ ⊤` ⇔ Beurling ⇔ `ι = 0` ⇔ fold capacity [L] — face of C19 |
| C2 Glued state | `κ(φ_c) − 1` | SC, AKG, RIT-Künneth | Grams are compressions on the Beurling schedule [L] — face of C1 |
| C3 Window integer | collision charge, heat count, window index | WD-charge, SC-heat, LA-heat, TG, HEF | index = Wiener–Hopf index [L] — face of C11 |
| C4 Sectors and ground states | odd/even sector sign; pole-charged gauges | CHMD, TT, AID, SAHT, OWU, EWU, ACT, SWC | sectors = band at the centre; below `log 4` sector sets `oddBandWeights`, `evenBandWeights`; retained-variance certificates exact [L] — face of C1 |
| C5 Rank / degree / continuation | Laguerre–Pólya; collision exclusion | TH, HCF, PA, GTA, LA, XN; ART; ZCG-deformation | reality lost only through collision; RH ⇔ simple zeros of `H_t` ∀t > 0 [L] |
| C6 Scheduled prime sums | lower bound of a scheduled energy | FU, CFC, RP, SZ, LI, FEL, EGC | explicit-formula functionals bounded below ⇔ RH [L] |
| C7 One-point precision | `ψ − x`, `M(x)`, one cyclotomic mode, coupling, Redheffer, gauge exponent | WL, MC, PBM, RB, JAS, CTF, SC-coupling, AGT | one-sided count ⇔ RH; gauge spectrum `[Θ, 1]` [L] — face of C19 |
| C8 Selection / typicality | trivial gauge point; degeneration type | MC-typicality, BAG, XN; ADT, AHD | RH ⇔ trivial point typical [L] |
| C9 Realization | spectral reality of a constructed operator | RN, PTR, W1C, PM-Mayer | Mayer Krein positivity ⇔ RH [L] |
| C10 Pre-divisor | a section defined before the divisor | APF, BSH, CDC, EWJ, HJ, PCS, RFHM, SEC, WBF | zero-independent forcing (Γ5) |
| C11 Local zero location | window energy, Hecke defect, near-line density, census, clusters | WD-energy, WD-Hecke, census, HEF, SRT-local, IGP, TTPC | abscissa = 2·depth; eight-form density [L] |
| C12 Hodge–Lefschetz / gluing | HL on the positive locus; zero modes; top gcd stratum | HF-Hodge, ACS-Hodge, RIT, EHT, TG, DZG, GWZ | zero modes = radical [L] |
| C13 Sections, counts, Tate family | count-valued primitive `h¹`; naive height; Tate jet | ACS-effectivity, HF-RR, IRK, AE, WTZ, LST, KPA | Künneth `h¹ = ½Q`; below `log 4` Künneth effectivity ⇔ window sign; closed as a sign mechanism [L/D] |
| C14 Reflection | Rosati involution; Lewis defect; Krein form | PM-scattering, HF band poles, W1C, CWS Frobenius | exact completion; kick = collar Rosati pairing; defect formula; PM lift of window tests [L] — face of C1 |
| C15 Window tower and canonical system | `W_A`; stages; collars; lattices; Schur parameters; jet Hankel | CWS, WTZ, DZG, GWZ, CSTW, SWC; SZ | stage criterion; Levinson; continuum limit with alternating reflection coefficients [L] |
| C16 Prime-blind cone | archimedean + pole part on blind tests | PBAP | Weil cone `⊆ {Λ}` [L] — face of C1 |
| C17 Dimension zero | domination of point counts | ATD, DZG (classified) | bare domination ⇔ `Q ≥ 0` [L] |
| C18 Angle dictionary | Hurwitz forms of angles / frequencies | AHD, ACS, LST, GWZ | angle `u` over `𝔽_q` ≡ frequency `u` [L] |
| C19 Two-site band | `|𝒞_m(f)| ≤ W(f)` | GWZ, AOG, SWC; every route of C1, C4, C7, C14, C15 | RH ⇔ two-site PD; coupling = Hankel − smoothed count [L] |
| C20 Selberg-class rigidity | Euler-log discrepancy; degree; FE twins | SEL; ACS, HF fakes | Gamma-independent rigidity; degree gap [L] |
| C21 Configuration camera | identification by the Weil image | ZCG, SRT-identification, SquareRootThreshold | cancelling clusters density `≥ 2a/π`; fakes caught at their first prime [L] |
| C22 Jet moment problems | Hankel/Toeplitz positivity of one jet sequence | SWC-sectors, TH, LA-Jensen, GWZ-lattice | sectors ⇔ Hamburger/Stieltjes; theta Hankel PSD ⇔ native moment tails; Jensen ⇔ Pólya–Schur [L]; lattice Toeplitz ⇔ Schur [L] — meets C4, C5, C15 |
| C23 Density apertures | completeness radius of exponentials on a configuration | ZCG-blindness, SquareRootThreshold-certification, Π29 | blindness `πD` exact; positivity certifies above `πD`; pair isolation `2a/π`; `λ = ½` [L/D] — face of C21 |
| C24 Hermite–Biehler phase | `ξ = A(s) + A(1−s)` with `|A(1−s)| < |A(s)|` right of the line | ZCG-Euler stages, census (Levinson–Conrey), GWZ/CSTW (de Branges) | Euler stages: monotone phase, simple line zeros above the horizon [L]; HB decomposition of `ξ` ⇔ RH [D] — meets C5, C11, C15 |

C1, C2, C4, C7, C14, C15, C16, C17 and C22 are one quantity, read at its minimal size in C19. C3 is a face
of C11. C5 and C6 are sign problems that become RH-complete only in the limit of rank, degree, schedule or
deformation time; C22 shows C5's rank towers and C4's sectors are the same moment problem. C13 is the
production face of C19; C8–C10, C18, C20, C21 and C23 are selection and calibration faces; C24 is the
phase face of C5 and C11.

## U-Σ — the sign

Core problem: the band on every reflection pair; in tower form every prime kick lands in its prediction
interval; in gauge form a gauge with retained pole variance in which the signed sliver reflections pay
the collar Hankel form; in moment form a Stieltjes measure for every even bump.

| Layer | Status | Anchor |
|---|---|---|
| Receivers | window, two-site, reflection pair, sectors, moment problems, lattice, horizon, threshold, schedule, index, Krein, PBAP, domination | CWS, GWZ, CSTW, AHD, SWC, RIT, TM, CHMD, RHTower, DZG [L] |
| Minimal object | reflection pair; first failure two-site; extremals edge-singular | GWZ, SWC [L] |
| First stages | below `log 4`: two-weight convex membership; certificate format exact; sharp prime-free boundary | SWC [L] |
| Canonical system | Levinson; Schur parameters; continuum margins; alternating reflection coefficients; parity split | GWZ, SWC [L] |
| Gauge calculus | pole-charged representation; theta gauges critical; variance retained | SWC [L] |
| Locality | collar ratio `2we^h` sharp; outward edge `we^h/2`; reflection-term bound below Lévy on windows `< log 5` | SWC [L/D] |
| Archimedean transmission | collar Hankel inertia `(1, ∞)`; Gamma ladder; pole `±` by sector | CSTW, SWC [L] |
| Complete family | subcritical PD; one critical multiple; threshold law; terminal source polar | CACT, AHD [L] |
| Zero modes | radical; parity; tight band ⇒ reflection-pair zero mode; never smooth | DZG, GWZ, SWC [L] |
| No slack | Weil cone a point; doubly-exponential margins; Szegő singular; reflection coefficients at `±1` | RHTower, M, GWZ, SWC [L] |
| Continuation | heat path real for `t ≥ 1/8`, non-real for `t < 0`; `Λ_X` pincer | RHTower DeBruijn, ZCG [L] |
| Dimension zero | classified | DZG, ATD [L] |

| Face | Routes / programmes | Reduction |
|---|---|---|
| Complete atomic matrix | HF, SRT, AIP, ACT, ACS-atomic, CACT, CAF, CSAR, ACPL, RAPT, SSH, SSHA, TM, ADT, AHD | size-only layers closed; threshold `R₁ ≡ ⊤` |
| Aperture ground minimum | RW, EWU, OWU, MSC, CFC, SP | window sign by stages; below `log 4` two numbers |
| Sectors / ground states | CHMD, AID, SAHT, TT, ACT, OWU, EWU, SWC | frustration domination with retained variance |
| Moment problems | SWC, TH, LA | Stieltjes/Hamburger positivity of jet sequences |
| Glued state | SC, AKG | Beurling-schedule sign |
| Window tower / canonical system | CWS, WTZ, DZG, GWZ, CSTW, SWC | kick admission; margin transport; two sites |
| Dimension zero | ATD, DZG | equivalent to the window sign |
| Edge / zero modes / Kähler | EHT, HWV, RW, DZG, GWZ, SWC | no zero mode; extremals edge-singular |
| Stars / gluing | HWV, CSAR, ADT | top gcd stratum |
| Effectivity / RR | ACS, LST, RIT, HF, AE, KPA | count-valued Hodge index; closed as a mechanism [D] |
| Rank / degree / continuation | TH, LA, HCF, PA, GTA, XN, ART, ZCG | Laguerre–Pólya; collision exclusion |
| Scheduled prime sums | FU, CFC, RP, SZ, LI, FEL, EGC | scheduled energy lower bound |
| Screw / Krein–Schur | SZ | the canonical system of GWZ/CSTW |
| Paths | TG, SC, EHT, ACPL, HWV | source-defined HL along a flow |
| Realization | RN, PTR, W1C, PM | Krein positivity of zero coordinates |
| Prime-blind | PBAP | signed blind combinations |

## U-Π — precision and production

Core problem: square-root precision of one smoothed short-window prime count — the band on the prime
side, `|Σ_nw_n(f⋆f)(2m − log n) − 𝓗_m(f)| ≤ W(f)` — and its production by an exact mechanism.

| Face | Routes / programmes | Reduction |
|---|---|---|
| Reflection-pair coupling | SWC, GWZ, CSTW, AOG | collar Hankel − smoothed count within `W(f)` (Π4) |
| Two-term count below `log 4` | SWC, RW, OWU, EWU, ACT | `w₂A₂ + w₃A₃` against `𝓗₀` within archimedean–polar `W` (Π4, Σ50) |
| Collective kicks | SWC, OWU, RW | kicks beyond collar locality = the smoothed count (Π30) |
| One-sided prime count | WL, PBM, RB, JAS, CTF, ACP, ASRP | `ψ(x) − x ≤ C√x log²x` (Π1) |
| One cyclotomic mode | MC, CAF | first-band energy `O(N^{1+ε})` (Π10) |
| Gauge torus | WL, MC, AGT | exponent `½` at the trivial point (Π28) |
| Windowed kernel / coupling | SC, ACPL, AKG, HKT | bounded `K_ζ` ⇔ bounded dense coupling (Π4, Σ17) |
| Integer producers | WL, AKLT, AHA | `ε`-uniform producer (Π3) |
| Möbius / nerve | MC, BVI, CAF, HWV, ADT | half-power cancellation; `χ̃ = −M(N)` |
| Window budget | CWS, WTZ, SRT, AHD | growth exponent = width (Σ28); size-only floor (Σ1o) |
| Terminal and sieve channels | AHD, CACT, V | finite prime boundary mass; Brun–Titchmarsh-type bounds (Π31, Π32) |
| Window energy | WD, TG, CDG | inner caps (Π17, Π23) |
| Near-line density | WD, CDG, RBG, HEF, census | eight forms; thin Planck shadows (Π5, Π22) |
| Census / clusters | SRT, IGP, Zeta23, CDG, TTPC | signed pair data beyond bandwidth one (Π7) |
| Square-root threshold | ZCG, SquareRootThreshold | `λ = ½` = pair-isolation aperture (Π29) |
| Tate jet / parity | WTZ, DZG, ATD, AHD | classified (Π24, Π25) |
| Sections / heights | ACS, LST, AOG, AET, AE, RIT, SPTL, CWS, KPA | closed as a mechanism (Π11h, Σ31) [D] |
| Bulk second order | AHD, ArtinMertens | Stieltjes constants, `L'/L(1,χ)`, polar growth (Π26) |
| Finite realizations | RIT, CWS | no-go (Π18) |
| Genus | ACS, RHTower, LST, CWS, WTZ | upper law open (Π16) |
| Averages vs heights | WD, LA, SRT | density-zero exceptions; double-log stage (Π6) |
| Candidates | APF, EWJ, FEL, WBF, IRK | integral counts from a source lift |

Identities [L]: one-sided count ⇔ `κ = 0`; reflection-pair coupling = collar Hankel − smoothed count;
coupling rate = orbit-correlation rate = zero width; window-energy abscissa = twice the maximal depth;
first cyclotomic band abscissa `2Θ`; gauge-torus exponent range `[Θ, 1]`; Weil's window form = Tate jet =
signed count; Künneth `h¹` = counts + `½Q`.

## U-Γ — selection and reflection

Core problem: a source-defined mechanism making the reflection `ρ ↦ 1 − ρ̄` act as a positivity. The
distinguishing half is closed: flips separated at every density, fakes caught at their first prime, Weil
cone a point, lattice selection of `Λ`, Selberg-class rigidity, identification up to the density aperture.
The reflection is constructed exactly on both sides and identified; at a resonance its defect is
`−∫2cosh(δu)4sinh²(δu)|F(u)F(−u)|`. Positivity of the reflection is RH.

| Face | Routes / programmes | Status / reduction |
|---|---|---|
| Typicality of the trivial point | MC, AGT, BAG, XN | Γ1; explicit `½` point off the special locus |
| Gluing of the global pole | SC, AKG, RIT | classified (Σ11, Γ11) |
| Margin, index, edge, degeneration selection | RIT, ACP, HKT, EHT, ACPL, RAPT, ADT, BGG | flips separated; only `Λ` degenerates completely (Γ2, Γ12, Γ18) |
| Weil cone / lattices | RHTower, BSU, GWZ | `{Λ}` (Γ23) |
| Selberg class | SEL | Euler rigidity; degree gap; degree one (Γ15, Γ33) |
| Camera identification | ZCG, SRT | density criterion `2a/π`; Ingham scale; local camera [W] (Γ36) |
| Blindness | ZCG | aperture `πD` exact; Paley–Wiener equivalence (Γ39) |
| Positivity certification | SquareRootThreshold | thin configurations above `πD`; one column pair `πD/2` (Γ40) |
| Fakes | ZCG | caught at their first prime (Γ41) |
| Euler columns | ZCG | Ramanujan = reality (Γ37) |
| Window selection | CWS | bounded windows blind (Γ20) |
| Density selection | ACPL | RvM-count countermodels (Γ21) |
| Tate counts | WTZ, DZG | do not descend (Γ27) |
| Window Frobenius | DZG, WTZ, RIT | similitudes scalar; Frobenius = translation (Γ28) |
| Intertwining coefficient | PM, RIT, RHTower | band poles = Hodge defect (Σ19, Γ22) |
| Frobenius at infinity | PL, CDG, RBG, EHT, AOG, AET, CWS, WTZ, GWZ | Rosati involution; collar Rosati pairing (Γ4, Γ19) |
| Degree-zero principles | KPA, ACS | bounded above ⇒ `≤ 0`; sublinear-error comparisons exact (Γ19) |
| Legendre invariant | KPA | RH ⇔ `J(ρ)` real (Γ42) |
| Mayer reflection | PM, W1C | defect formula; sign = `δ = 0` (Γ24, Γ29, Γ32) |
| Retained channel | PM | side detector (Γ38) |
| Hecke structure | PM | cones tile; periods eigenfunctions (Γ34) |
| Resonant-state statistics | PM | retain the rate (Γ26) |
| Physical / native source | PM; PW-B retired | (Γ13, Γ17) |
| Pre-divisor constructions | BSH, CDC, HJ, SEC, PCS, RFHM, EWJ, APF, WBF | zero-independent forcing (Γ5) |
| Function-field calibration | ACS, AKG, RIT, EHT, ACPL, LST, HWV, AET, AHD, CWS, WTZ, GWZ, ZCG | camera at the genus; bounded images certify purity; collide or repel (Γ10, Γ31, Γ43) |
| Selection → sign | all selectors | no selector gives positivity (Γ16) |

## 2. Cross-family seams

| Seam | Statement | Routes on the seam |
|---|---|---|
| Σ ∩ Π: reflection pairs | `W(f ± f∘R) = 2W(f) ± 2𝒞_m(f)`, `𝒞_m` = collar Hankel − smoothed count | SWC, GWZ, CSTW, AOG, WL [L] |
| Σ ∩ Π: first stages | below `log 4` window sign = two-term count against `𝓗₀` within archimedean–polar `W` | SWC [L] |
| Σ ∩ Π: size versus sign | reflection-term bound below Lévy on windows `< log 5`, yet the primes are needed as signed payers | SWC [L/D] |
| Σ ∩ Π: collective kicks | kicks beyond collar locality are the smoothed count | SWC [L]; [D] |
| Σ ∩ Γ: exact completion | Weil energy = Krein form of zero coordinates; window tests lift to Mayer fixed periods; defect dominates fold functionals | RIT, WTZ [L] |
| Σ: one canonical system | Levinson recursion; continuum margins; reflection coefficients freeze at `(−1)^n` | GWZ, SWC [L] |
| Σ ∩ C5: one moment problem | sectors ⇔ Hamburger/Stieltjes; theta Hankel PSD ⇔ native moment tails | SWC, TH, LA [L] |
| Σ: one location | each fold = sliver signature of one collar-to-collar correlation | WTZ, GWZ, CSTW, SWC [L] |
| Σ: one gauge calculus | pole-charged representation; retained variance mandatory | SWC, ACT [L] |
| Σ ∩ Π: trivial divisor | collar Hankel inertia `(1, ∞)`; Gamma ladder and pole signs by sector | CSTW, SWC [L] |
| Σ ∩ Π ∩ Γ: dimension zero | classified | WTZ, DZG, ATD, AHD [L] |
| Σ: one decomposition | counts on every twisted direction + Weil at the frequency pole; terminal source polar | ADT, AHD, CACT [L] |
| Σ ∩ Π: growth exponent | ground-energy fall rate = zero width; excluded-depth law; doubly exponential reach | WTZ, AHD, SquareRootThreshold, DCI [L] |
| Σ ∩ Π: shallow zeros | windows of half-width `a` are blind exactly to depth `≲ (log log T)/a`, WD's near-line scale | SWC, SquareRootThreshold, CDG [D] |
| Σ ∩ Γ: zero modes | radical, parity, two-site; never smooth | DZG, GWZ, SWC [L] |
| Σ: curves | degenerate windows are finite curves | GWZ [L] |
| Σ: one axis | window length = lattice length = two-site step + support = radius `½log K` = log of the matched height (model) | AHD, GWZ, SquareRootThreshold [L/M] |
| Σ ∩ Π: no slack | Weil cone a point; doubly-exponential margins; Szegő singular; heat path critical; PM defect zero only at `δ = 0` | RHTower, M, GWZ, DeBruijn, RIT [L] |
| Σ ∩ Π: one gluing | Redheffer, nerve `χ̃`, glued index | ADT, HWV, AKG, MC [L] |
| Σ ∩ Π ∩ Γ: counts | Künneth counts pay all but `½Q`; no count produces the sign | CWS, WTZ, LST, AE, ACS, RIT, ATD, DZG [L]; [D] |
| Σ ∩ Γ: angle dictionary | angle over `𝔽_q` ≡ frequency over ℤ | AHD [L] |
| Σ ∩ Γ: one Frobenius | Frobenius at scale `t` = translation | DZG, RIT [L] |
| Σ ∩ Γ: camera and reality | identification sign-free; reality at a near-collision is a second-order sign | ZCG [L] |
| Σ ∩ Γ: sign-based visibility | positivity at one aperture certifies thin configurations above `πD` | SquareRootThreshold [L] |
| Π ∩ Γ: density aperture | blindness `πD`; cancelling clusters `2a/π`; `λ = ½`; Riemann–Siegel length | ZCG, SquareRootThreshold [L/M]; [D] |
| Σ: continuation | reality lost only through collision; `Λ = sup_X Λ_X` | ZCG, LA, DeBruijn [L] |
| Σ ∩ Π: Hermite–Biehler phase | Euler stages with monotone phase above their horizon [L]; Levinson–Conrey counting; de Branges systems [D] | ZCG, IGP, GWZ |
| Π: window integer | collision charge = Wiener–Hopf index | WD, TG, SC-heat [L] |
| Π: one density statement | eight forms; thin Planck shadows | WD, CDG, census, MC, HEF [L] |
| Π: one mode, one torus | first cyclotomic band carries `2Θ`; gauge exponent range `[Θ, 1]` | MC, CAF, AGT [L] |
| Π: bulk and terminal | Stieltjes constants; polar growth; terminal prime means finite Riemann sums | AHD, ArtinMertens [L] |
| Γ: one point, one cone | Weil cone `{Λ}`; lattice selection | RHTower, GWZ [L] |
| Γ: blind selectors | bounded windows, densities, contractions, local twists, Tate counts, resonant statistics, retained channel | CWS, ACPL, RIT, AKLT, WTZ [L] |
| Γ: exactness by homogeneity | degree-zero Rosati and Tate principles: sublinear-error comparisons are identities | KPA, AE [L] |
| Σ: approximation | RH-true approximants close into Laguerre–Pólya | ART, W1C, PTR, LA, TH |
| Archimedean channel | Lévy jumps, exit charge, collar light cone, outward edge, trivial-divisor transmission, Gamma ladder | AKG, ALG, CHMD, RIT, ACPL, HWV, ACS, LST, ADT, CWS, WTZ, DZG, ATD, CSTW, SWC |

## 3. Route → core map

| Route | Core | Class | Face |
|---|---|---|---|
| WL | Π | C7, C19 | one-sided count; reflection-pair coupling |
| RW, EWU, OWU | Σ | C1, C4, C15, C19, C22 | window sign by stages; below `log 4` two weights; sectors as moment problems |
| FU, CFC, RP, SZ, LI | Σ | C6 | scheduled prime sums; SZ also the Krein–Schur carrier of C15 |
| PA, TH, LA, HCF, GTA, XN | Σ | C5, C22 | Laguerre–Pólya; moment towers; continuation |
| MC | Π (Γ) | C7, C8 | Möbius cancellation; gauge torus; typicality |
| TT | Σ | C4 | odd sector |
| TG | Π, Σ | C3, C12 | window integer; HL along paths |
| HF | Σ (Π, Γ) | C1, C12, C13, C14, C15, C18 | complete family; threshold `R₁ ≡ ⊤`; terminal source polar |
| SRT, AIP, ACT | Σ (Π) | C1, C4, C11, C21, C23 | complete atomic matrix; certification of thin configurations; retained-variance shifts |
| SC | Σ, Π (Γ) | C2, C7, C3 | glued state; damped coupling; heat |
| CHMD | Σ | C4, C1 | odd sector |
| RN | Σ | C9 | realization |
| WD | Π (Σ) | C3, C11 | window energy; inner caps; near-line density |
| PM | Γ (Σ) | C9, C14 | Krein space of zero coordinates; defect formula; window lift |
| JAS, CTF, PBM, RB | Π | C7, C19 | one-sided count |
| BAG | Γ | C8 | typicality / recurrence |
| ACS | Π (Σ, Γ) | C13, C1, C12, C15, C18, C20 | count face closed; Künneth effectivity = window sign; Legendre reality; degree-zero principles |
| APF, EWJ, WBF, IRK | Γ (Π) | C10, C13 | source lift with integral count |
| BSH, CDC, HJ, SEC, PCS, RFHM | Γ | C10 | pre-divisor constructions |
| EGC, FEL, MSC | Σ | C6, C1 | contour / likelihood / Sonin |
| PTR, W1C | Σ (Γ) | C9, C5, C14 | realization; Krein form of zero coordinates |
| ZCG | Γ (Σ) | C21, C23, C24, C5 | camera; density aperture; Euler-stage phase; continuation |
| PW-B (retired) | Γ | C14 | survivor = scattering receiver |
| PBAP (support) | Γ (Σ) | C16 | prime-blind positivity |

## 4. What a closing argument must supply

| Needed | Present over ℤ | Missing |
|---|---|---|
| Sign of the minimal object | RH ⇔ the band on reflection pairs; explicit coupling | the band at every step (B1) |
| Mechanism for the sign | pole-charged gauge calculus; exact certificate format below `log 4`; sliver signature; outward edge; soft entry; base to `0.7240` | a signed payment of the collective kicks against the pole square with retained variance (B3), first below `log 4` (B4, B5); cost-only, sign-blind, variance-free, Markov and finite certificates excluded |
| Full-space structure | subcritical PD; whole space at one critical multiple; threshold law; terminal source polar | `R₁(A) = ⊤` for every `A` (B7); twisted sector at every multiple (B6) |
| Uniformity in `A` | each length finite; fall rate = width; excluded-depth law | the sharp visibility law (B47); window negativity exponent `< ½` (B16); the contact law (B18) is a zero-location statement [D] |
| Nondegeneracy | zero modes radical, parity, two-site, never smooth | no degenerate two-site lattice (B10) |
| Precision | one-sided count ⇔ RH; gauge spectrum `[Θ,1]`; eight-form density; caps to `σ_m` | square-root size of one smoothed count; inner caps (B19); `D_win` (B21) |
| Count from geometry | Künneth `h¹ = ½Q`; Weil's form a signed count; finite-field Stepanov | — (closed [D]) |
| Canonical selector | Weil cone `{Λ}`; Selberg rigidity; identification up to the density aperture; fakes caught at their first prime | — (automatic after positivity) |
| Reflection | exact zero-coordinate Krein space; defect formula manifestly `≤ 0`, zero only at `δ = 0` | an arithmetic expression of the defect at resonances with manifest sign `≥ 0` (B38) |
| Reality by continuation | heat path real for `t ≥ 1/8`; collision exit; `Λ_X` pincer; Euler stages HB above their horizon; integrality repulsion over `𝔽_q` | collision exclusion on `(0, 1/8]` at every height (B14) |
| Integrality with homotopy invariance | window index; `{0, ∞}` laws | a zero–one law for `κ` (B13); a structural bound on the window index (B12) |
