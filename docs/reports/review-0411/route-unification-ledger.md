# Route unification ledger — status quo

The 32 live routes and 17 candidates are faces of three core problems — **U-Σ** (sign), **U-Π**
(precision and production), **U-Γ** (selection and reflection) — and the three are one statement read
three ways: the **band** `|𝒞_m(f)| ≤ W(f)` of a test `f` and its mirror image `f∘R`, `R(v) = 2m − v`, with
`𝒞_m(f) = 𝓗_m(f) − Σ_nΛ(n)n^{−1/2}(f⋆f)(2m − log n)`. U-Σ reads it as a form, U-Π on the prime side, U-Γ on
the zero side. All routes measure one even integer `κ = κ(K_ζ) = #` distinct zeros right of the line and one
number, the onset aperture `a*(ζ)`; RH ⇔ `κ = 0` ⇔ `a*(ζ) = ⊤`. All are decided on the smallest piece of the
window tower `A ↦ W_A`, the reflection pair.

- **One criterion, one number, one minimal object.** Every sign face is Weil's form on windows of every
  length [L]; the positive half-widths form the closed interval `[0, a*(Z)]`, `a*(Z) = ⊤` iff every zero is on
  the line [L]; HF's threshold is `R₁(A) = ⊤ ⇔ A/2 ≤ a*(ζ)` [L]; windows are decided on two sites [L]; the
  parity sectors are the band at the centre [L].
- **Sign = precision.** `W(f ± f∘R) = 2W(f) ± 2𝒞_m(f)`; `𝒞_m` = collar Hankel form minus smoothed prime count
  [L]: U-Σ on a reflection pair is U-Π at one scale. Below window length `log 4` this is a two-term prime count
  matching `𝓗₀(f)` within the archimedean–polar `W(f)`, and the whole sign is the membership of
  `(Λ(2)/√2, Λ(3)/√3)` in an explicit compact convex set [L].
- **Sign → location.** The visibility law turns every window theorem into zero location:
  `k·pairEnergy(δ, a) ≤ L` in lattice backgrounds, an `e^{2(δ−σ)a}/δ` law for unshielded clusters in every
  RvM configuration, a sharp shielding barrier at single-exponential height [L]. Windows read depth and
  coherence; zero information starts at half-width `4` [D].
- **Reflection = zero side.** `Q(H) = 2Re[𝓦H, 𝓦H]` on `ℓ²(zeros)`; canonical Krein–Lax–Phillips space with
  off-line antisymmetric Krein square `−2` [L]; the co-isometry defect of a resonance is
  `−∫2cosh(δu)4sinh²(δu)|F(u)F(−u)|` [L]: U-Γ's positivity is U-Σ in zero coordinates, at a resonance the
  identity `δ = 0` [D].
- **Identification is complete; its residue is a sign.** At aperture `λ·½log(T/2π)` the explicit formula
  fixes RvM configurations for `λ > 1` outside near-collisions `< δ/log T`, and ζ's isolated zeros with their
  multiplicities for `λ > ½` [L]; inside near-coincidences it reads the squared gap `w²` to second order [L].
  What is left of U-Γ is the sign of `w²` — the same as the sign of the reflection.
- **One continuation, one floor.** Reality is lost only through collision; RH ⇔ every zero of `H_t` simple
  ∀t > 0 [L]; collisions are near-coincidences; size information reaches heat time `½/log X` (Gaussian saddle)
  and no further, while pair models collide below every positive time scale [L]. P5's residual is U-Γ's sign.
- **One moment problem.** Even sector ⇔ Hamburger, odd ⇔ shifted Hamburger, window ⇔ Stieltjes for
  `s_k = W(φ^{(k)})` [L]; theta Hankel towers are the same kind of moment problem at one centre [L].
- **One canonical system.** Lattices: Szegő–Levinson theory, Szegő singular under RH [L]. Continuum: margins
  `h^{−2n}E_n → det J_{n+1}/det J_n`, reflection coefficients freezing at `(−1)^n`, parity split
  `det J_n = det E·det O` [L]. The global Hamiltonian is not constructed.
- **One location of frustration.** Odd sector: the kicks (`kick = source − conductance`); even sector: the pole
  alone, `E(f) − E(|f|) = ∬D[ω(|u−v|) + ω(−u−v) − 4cosh(u/2)cosh(v/2)]` [L]. Perron/Markov structure holds
  exactly to `c = log ρ` [L]; beyond, every certificate is signed; the fold of an entering prime couples the
  two collars through the signature of its sliver reflection [L].
- **One gauge calculus and one certificate format.** Pole-charged Dirichlet forms; theta gauges critical on the
  line; below `log 4` retained-variance certificates are exact and dropping the variance fails [L].
- **One locality law and one payment law.** Collar-internal jumps pay the kick of `n` at ratio `2w_ne^h`,
  sharp; outward jumps carry the newest prime power at `w_ne^h/2`; the summed edge-law bound stays below the
  Lévy energy on windows shorter than `log 5` [L/D]; the primes pay the prime-free deficit by sign [L].
- **One decomposition, one pole.** At the critical curve the complete family is Weil's form at the pole
  `u = 0` of the frequency counts plus positive counts; every terminal source is polar [L].
- **One Frobenius, one point, one cone.** Frobenius at scale `t` is translation by `t`; the Weil cone is `{Λ}`
  or empty [L].
- **One criticality.** Every exact reading sits on a zero-slack boundary [L/D].
- **One missing mechanism.** Over `𝔽_q` the Gram of the diagonal and the graph of Frobenius is positive on
  primitive classes by the Hodge index, and integrality of the image forces collide-or-repel [L]. Over ℤ the
  same Gram, of `f` and `f∘R`, is RH; the count mechanism is closed; the image is a `log p`-weighted sum without
  discreteness; domination is shared by every finite real carrier [L/D]. Missing: a signed payment of the
  collective kicks against the pole square on every reflection pair (P1 = P4), or archimedean positivity on
  signed prime-blind combinations (P2), or an arithmetic expression of the PM defect with manifest sign (P3),
  or a repulsion law at near-coincidences driven by the Euler product inside the strip (P5 = the U-Γ sign).

Evidence: `[L]` committed Lean; `[W]` working-tree Lean; `[P]` pipeline-card paper proof; `[D]` derived
here; `[M]` model.

## 0. The one object

| Reading | Statement | Anchor |
|---|---|---|
| Index | `κ = #{ρ : Re ρ > ½}` (distinct), even; RH ⇔ `κ < 2` | HKT, AKLT, AOG, ACS [L] |
| Onset aperture | `WindowPositiveAt Z a ⇔ a ≤ a*(Z)`; `a*(Z) = ⊤` ⇔ on-line; RH ⇔ `a*(ζ) = ⊤`; off RH `a*(ζ)` = contact, attained; `a*(ζ) ≥ 0.362` | WVL [L] |
| Window index | `ι(A)` monotone, `0` for `A ≤ 3/5`, `sup_A ι(A) = κ` | CWS, AHD [L] |
| Threshold | `R₁(A) = ⊤ ⇔ A/2 ≤ a*(ζ)` | AHD, WVL [L] |
| Two sites | RH ⇔ `[[Q(ψ), c_ψ(t)],[c_ψ(t), Q(ψ)]] ≻ 0` ∀ψ, t | GWZ [L] |
| Reflection pair | `W(f ± f∘R) = 2W(f) ± 2𝒞_m(f)` | SWC [L] |
| Parity sectors | odd ⇔ `𝒞₀(f) ≤ W(f)`, even ⇔ `−𝒞₀(f) ≤ W(f)` | SWC [L] |
| Below `log 4` | positivity ⇔ `(w₂, w₃) ∈ oddBandWeights c ∩ evenBandWeights c`; prime-free half-window iff `c ≤ log 2` | SWC [L] |
| Perron | even band Markov iff `c ≤ log ρ`; past it at no pole strength | SWC [L] |
| Sliver | `(f⋆f)(−ℓ) = ∫_I(f₊² − f₋²)`; `w_n|(f⋆f)(−log n)| ≤ (Λ(n)e^c/(2n))·levyEnergy` | SWC [L] |
| Moments | even ⇔ Hamburger, odd ⇔ shifted Hamburger, window ⇔ Stieltjes | SWC [L] |
| Orbit | RH ⇔ the orbit correlation of one generic bump eventually bounded; rate = zero width | AOG [L] |
| Coupling | `𝒞_m(f) = 𝓗_m(f) − Σ_nw_n(f⋆f)(2m − log n)`; `𝓗_m` inertia `(1, ∞)` | SWC, CSTW [L] |
| Lattice | RH ⇔ Schur parameters in `(−1,1)` | GWZ [L] |
| Continuum | `h^{−2n}E_n → det J_{n+1}/det J_n`; `γ_n → (−1)^n`; `det J_n = det E·det O` | SWC [L] |
| Edge | no smooth eigenfunction, constrained ground state or capacity maximizer | SWC [L] |
| Curve | degenerate window = finite curve; Spec ℤ under RH = infinite-angle curve | GWZ [L] |
| Window algebra | truncated Dirichlet λ-ring | WTZ [L] |
| Gauge form | `Ẑ(Φωu) = J_{Φω}(u) + ∫u²ω𝒢_S(ω) + 2V_s − 2V_c`; variance = all-pairs jump form | SWC [L] |
| Gamma ladder | `A(g)‖g'‖² ≤ A(g')‖g‖²`; pole `+` to even, `−` to odd | SWC [L] |
| Tate jet | `Q` = 1-jet at `k = 0` of the counts of `𝔸^k∖0` | WTZ, DZG, ATD [L] |
| Stage | `Q = Q_N − 2wc_H(ℓ)`; soft entry `ηΩ(2c − log p)` | WTZ, GWZ, SWC [L] |
| Base | all real `C²` tests positive to half-width `0.362…` | SPATL, GWZ, AIP [L] |
| Floor | `Q ≥ −C(p)∫e^{−pu}H²`, `p > 1`; exponent `p` ⇒ width `≤ p` | WTZ, SquareRootThreshold [L] |
| Complete family | PD below `(log N)^{1/8}` and at one critical multiple; terminal source polar; simultaneous receiving | CACT, AHD, CSAR [L] |
| Visibility | `k·pairEnergy(δ,a) ≤ L`; `e^{2(δ−σ)a}/δ` in RvM; shielding barrier; non-locality | WVL [L] |
| Reflection | `Q = 2Re[𝓦H, 𝓦H]`; Krein–Lax–Phillips space; window involution = twisted Krein reflection | RIT [L] |
| Lewis periods | `D_s ≤ 0`, `= 0` iff `Re s = ¼`; `D_s = −∫2cosh(δu)4sinh²(δu)|F(u)F(−u)|` | RIT [L] |
| Camera | `W_Z(f,g) = Σm_ρf̂(γ_ρ)conj ĝ(conj γ_ρ)`; inversion at `λ > 1`; ζ readout at `λ > ½`; `w²` to `O(r³)` | ZCG [L] |
| Blindness | aperture `πD` exact; ⇔ entire functions of exponential type vanishing on the set | ZCG [L] |
| Heat path | real for `t ≥ 1/8`; RH ⇔ all positive-time zeros simple; size reaches `½/log X` | RHTower, ZCG [L] |
| Euler stage / carrier | `A(s) + A(1−s)`: phase lattice, simple line zeros above `2πe^{W_a}`, any real coefficients | ZCG [L] |
| Glued state | `κ(φ_c) = κ + 1` | AKG [L] |
| Gluing determinant | Redheffer `det = M(N)` = nerve `χ̃` | ADT, HWV [L] |
| Kähler package | RH ⇔ HL on the PSD locus | HWV, DZG, GWZ [L] |
| Weil cone | `⊆ {Λ}`; lattice selection; PBAP | RHTower, GWZ [L] |
| Window energy | abscissa = 2·maximal depth; caps to `σ_m`; polynomial stage ⇔ RH | CDG [L] |
| Near-line density | eight forms; `D_win` ⇔ thin Planck shadows | CDG [L] |
| Gauge torus | exponent range `[Θ, 1]`; first cyclotomic band abscissa `2Θ` | AGT, CAF [L] |
| Angles | `𝔽_q` angle ≡ ℤ frequency; curve camera identifies at the genus | AHD, ZCG [L] |
| Selberg class | Euler rigidity at `σ = ½`; degree gap; degree one | SEL [L] |
| Legendre invariant | RH ⇔ `J(ρ) ∈ ℝ` at every zero | KPA [L] |

## 0.1 The window axis

| Coordinate | Reading at half-width `c` | Anchor |
|---|---|---|
| Markov death | support `e^{−3/4}` | SWC [L] |
| Perron threshold | `c = log ρ ≈ 0.2812` (even band) | SWC [L] |
| Known sign | all tests to half-width `0.362…`; floor up to `enlargedWeilFloorAperture` | SPATL, AIP [L] |
| Odd unit window | `c = ½`: one weight `w₂` in a convex set (open) | SWC [L] |
| First prime stage | `2c = 21/20`: `w₂ ≤ 0` excluded for `c ≥ 21/40` | WTZ, SWC [L] |
| Prime-three entry | `2c = log 3`: cylinders in `w₃` before; compact after; soft entry `ηΩ(δ)` | SWC [L] |
| Sliver potential / prime 3 deleted | fail for `c ≥ 287/500` / `c ≥ 3/5` | SWC [L] |
| Variance-free certificates | fail for `c > 273/400` | SWC [L] |
| Prime-free half-window | sharp at `c = log 2` (`2c = log 4`) | SWC [L] |
| Reflection-term bound below Lévy | windows `2c < log 5` | SWC [L/D] |
| Zero information | from `c ≥ 4` (`δc ≥ 2`, `δ < ½`); `c ≳ 20` with present constants | WVL [L]; [D] |
| Ground energy | `μ(a) ≤ K exp((11/2)a − πe^{2(a−2)})` | M [L] |
| Excluded depth | positivity at `R` ⇒ no zero of depth `≥ 1/R` to `e^{R/polylog R}`; unshielded clusters to doubly-exponential height | SquareRootThreshold, WVL [L] |
| Height non-locality | zeros below `exp((e^{2δa}−2)/(4δ) − a)` do not decide the window | WVL [L] |
| Contact scale | `c log T`: positivity there is a power-saving zero-location bound | WVL [L] |
| Camera aperture | `λ·½log(T/2π)`: isolated zeros of ζ read at `λ > ½`; configurations at `λ > 1` | ZCG [L] |
| Over `𝔽_q` | a curve with `2g` angles fails at lattice index `2g`; camera at order `g`; columns certified at `(g − ½)log q` | CWS, GWZ, ZCG, WVL [L] |

Each fixed window length is a sub-RH finite problem; all lengths together are RH; all steps of one two-site
lattice are RH.

## 0.2 The degeneration, angle and camera dictionary

| Object | Over ℤ | Over `𝔽_q` | Classes |
|---|---|---|---|
| Resolution axis | overlap `c`, `c⁸ ≍ K log N` | atom width `w` | C1 |
| Twisted direction | frequency `u`: positive Hurwitz count | angle `θ_i`: positive Hurwitz weight | C1, C18 |
| Trivial direction | pole of the frequency counts at `u = 0` | main term | C1, C18 |
| First failure | two-site; extremals edge-singular | at index `2g` | C15, C19 |
| Camera threshold | `λ = ½`: isolated zeros read; `λ > 1`: configurations identified | order `g` | C21, C23 |
| Certification by size | none (unbounded density) | bounded image at all orders ⇔ purity | C21 |
| Certification by sign | split columns at `πD_on + (π/2)D_off`; mixed `2g` columns exactly `(g − ½)ℓ` | positivity at `a > (g − ½)log q`, sharp | C21, C23, C25 |
| Repulsion | phase speed above the carrier horizon (any real coefficients); size reaches `½/log X` on the heat path | integrality: collide or repel | C5, C24 |
| Reality | sign of `w²` at a near-coincidence | trace points `β + β⁻¹ ∈ [−2, 2]` | C5, C21 |
| Euler column | `A² ≤ 4p` ⇔ on the line; twins tilted at every height | unit circle | C21, C20 |

## 1. Equivalence classes of routes

Routes in one class compute the same quantity; a theorem in one class transfers through the listed identity.

| Class | Common quantity | Routes | Identity joining them |
|---|---|---|---|
| C1 Weil's window form | `Q ≥ 0` on windows of every length | HF, SRT, AIP, ACT, ACS-atomic; RW, EWU, OWU, MSC, FEL; ADT/AHD, CACT, CSAR | window ⇔ horizon ⇔ `R₁ ≡ ⊤` ⇔ Beurling ⇔ `ι = 0` ⇔ fold capacity [L] — face of C25 |
| C2 Glued state | `κ(φ_c) − 1` | SC, AKG, RIT-Künneth | Grams are compressions on the Beurling schedule [L] — face of C1 |
| C3 Window integer | collision charge, heat count, window index | WD-charge, SC-heat, LA-heat, TG, HEF | index = Wiener–Hopf index [L] — face of C11 |
| C4 Sectors and ground states | odd/even sector sign; pole-charged gauges; Perron range | CHMD, TT, AID, SAHT, OWU, EWU, ACT, SWC | sectors = band at the centre; below `log 4` sector weight sets; retained-variance certificates exact; Markov to `log ρ` [L] — face of C1 |
| C5 Rank / degree / continuation | Laguerre–Pólya; collision exclusion below `½/log X` | TH, HCF, PA, GTA, LA, XN; ART; ZCG-deformation | reality lost only through collision; RH ⇔ simple zeros of `H_t` ∀t > 0; size floor at the saddle [L] — meets C21 at near-coincidences |
| C6 Scheduled prime sums | lower bound of a scheduled energy | FU, CFC, RP, SZ, LI, FEL, EGC | explicit-formula functionals bounded below ⇔ RH [L] |
| C7 One-point precision | `ψ − x`, `M(x)`, one cyclotomic mode, coupling, Redheffer, gauge exponent | WL, MC, PBM, RB, JAS, CTF, SC-coupling, AGT | one-sided count ⇔ RH; gauge spectrum `[Θ, 1]` [L] — face of C19 |
| C8 Selection / typicality | trivial gauge point; degeneration type | MC-typicality, BAG, XN; ADT, AHD | RH ⇔ trivial point typical [L] |
| C9 Realization | spectral reality of a constructed operator | RN, PTR, W1C, PM-Mayer | Mayer Krein positivity ⇔ RH [L] |
| C10 Pre-divisor | a section defined before the divisor | APF, BSH, CDC, EWJ, HJ, PCS, RFHM, SEC, WBF | zero-independent forcing (Γ5) |
| C11 Local zero location | window energy, Hecke defect, near-line density, census, clusters | WD-energy, WD-Hecke, census, HEF, SRT-local, IGP, TTPC | abscissa = 2·depth; eight-form density [L] — meets C25 at shallow depth |
| C12 Hodge–Lefschetz / gluing | HL on the positive locus; zero modes; top gcd stratum | HF-Hodge, ACS-Hodge, RIT, EHT, TG, DZG, GWZ | zero modes = radical [L] |
| C13 Sections, counts, Tate family | count-valued primitive `h¹`; naive height; Tate jet | ACS-effectivity, HF-RR, IRK, AE, WTZ, LST, KPA | Künneth `h¹ = ½Q`; closed as a sign mechanism [L/D] |
| C14 Reflection | Rosati involution; Lewis defect; Krein form | PM-scattering, HF band poles, W1C, CWS Frobenius | exact completion; Krein–Lax–Phillips space; defect formula [L] — face of C1 |
| C15 Window tower and canonical system | `W_A`; stages; collars; lattices; Schur parameters; jet Hankel | CWS, WTZ, DZG, GWZ, CSTW, SWC; SZ | stage criterion; Levinson; continuum limit [L] |
| C16 Prime-blind cone | archimedean + pole part on blind tests | PBAP | Weil cone `⊆ {Λ}` [L] — face of C1 |
| C17 Dimension zero | domination of point counts | ATD, DZG (classified) | bare domination ⇔ `Q ≥ 0` [L] |
| C18 Angle dictionary | Hurwitz forms of angles / frequencies | AHD, ACS, LST, GWZ | angle `u` over `𝔽_q` ≡ frequency `u` [L] |
| C19 Two-site band | `|𝒞_m(f)| ≤ W(f)` | GWZ, AOG, SWC; every route of C1, C4, C7, C14, C15 | RH ⇔ two-site PD; coupling = Hankel − smoothed count [L] |
| C20 Selberg-class rigidity | Euler-log discrepancy; degree; FE twins | SEL; ACS, HF fakes | Gamma-independent rigidity; degree gap [L] |
| C21 Configuration camera | identification by the Weil image | ZCG, SRT-identification, SquareRootThreshold | local inversion at `λ > 1`; ζ readout at `λ > ½`; second-order moments; fakes at their first prime [L] — complete; residue = sign of `w²` |
| C22 Jet moment problems | Hankel/Toeplitz positivity of one jet sequence | SWC-sectors, TH, LA-Jensen, GWZ-lattice | sectors ⇔ Hamburger/Stieltjes; theta Hankel PSD ⇔ native tails; Jensen ⇔ Pólya–Schur; lattice Toeplitz ⇔ Schur [L] |
| C23 Density apertures | completeness radius of exponentials on a configuration | ZCG-blindness, SquareRootThreshold, Π29 | blindness `πD`; sparse clusters `2a/π`; `λ = ½` [L] — face of C21 |
| C24 Hermite–Biehler phase | `A(s) + A(1−s)` with dominant `A` right of the line | ZCG-Euler stages and carriers, census, GWZ/CSTW | every symmetric half: phase lattice above its horizon [L]; HB decomposition of `ξ` ⇔ RH [D] |
| C25 Onset aperture | `a*(ζ)`: the supremum of positive window half-widths | WVL, SRT, HF (threshold), every window route | closed-interval law; `a* = ⊤` ⇔ on-line; `R₁ = ⊤ ⇔ A/2 ≤ a*`; master visibility law [L] |

C1, C2, C4, C7, C14, C15, C16, C17 and C22 are one quantity, `a*(ζ)` (C25), read at its minimal size in C19.
C3 is a face of C11. C5 and C21 meet at near-coincidences: collision exclusion and the sign of `w²` are one
problem. C6 is a sign problem RH-complete only in the limit of the schedule. C13 is the production face of C19;
C8–C10, C18, C20, C21 and C23 are selection and calibration faces, of which C21 and C23 are complete
identifications; C24 is the phase face of C5 and C11; C25 converts every C19 statement into zero location.

## U-Σ — the sign

Core problem: the band on every reflection pair (`a*(ζ) = ⊤`); in tower form every prime kick lands in its
prediction interval; in gauge form a signed gauge with retained pole variance in which the sliver reflections
pay the collar Hankel form; in moment form a Stieltjes measure for every even bump.

| Layer | Status | Anchor |
|---|---|---|
| Receivers | window, onset aperture, two-site, reflection pair, sectors, moment problems, lattice, horizon, threshold, schedule, index, Krein, PBAP, domination | WVL, CWS, GWZ, CSTW, AHD, SWC, RIT, TM, CHMD, RHTower, DZG [L] |
| Minimal object | reflection pair; first failure two-site; extremals edge-singular | GWZ, SWC [L] |
| First stages | below `log 4`: two-weight convex membership; certificate format exact; sharp prime-free boundary | SWC [L] |
| Positivity-preserving range | Markov to support `e^{−3/4}`; even-band Perron to `log ρ`; robust Perron costs height | SWC [L] |
| Canonical system | Levinson; Schur parameters; continuum margins; alternating reflection coefficients; parity split | GWZ, SWC [L] |
| Gauge calculus | pole-charged representation; theta gauges critical; variance retained | SWC [L] |
| Locality | collar ratio `2we^h` sharp; outward edge `we^h/2`; reflection-term bound below Lévy on windows `< log 5` | SWC [L/D] |
| Complete family | subcritical PD; one critical multiple; threshold law = onset aperture; terminal source polar; simultaneous receiving | CACT, AHD, CSAR, WVL [L] |
| Zero modes | radical; parity; tight band ⇒ reflection-pair zero mode; never smooth | DZG, GWZ, SWC [L] |
| Visibility | window sign → zero location; shielding barrier; non-locality | WVL [L] |
| No slack | Weil cone a point; doubly-exponential margins; Szegő singular; reflection coefficients at `±1` | RHTower, M, GWZ, SWC [L] |
| Dimension zero | classified | DZG, ATD [L] |

| Face | Routes / programmes | Reduction |
|---|---|---|
| Complete atomic matrix | HF, SRT, AIP, ACT, ACS-atomic, CACT, CAF, CSAR, ACPL, RAPT, SSH, SSHA, TM, ADT, AHD | size-only layers closed; `R₁ ≡ ⊤` ≡ `a*(ζ) = ⊤` |
| Aperture ground minimum | RW, EWU, OWU, MSC, CFC, SP | `a*(ζ)` by stages; below `log 4` two numbers |
| Sectors / ground states | CHMD, AID, SAHT, TT, ACT, OWU, EWU, SWC | signed frustration domination with retained variance past `log ρ` |
| Moment problems | SWC, TH, LA | Stieltjes/Hamburger positivity of jet sequences |
| Glued state | SC, AKG | Beurling-schedule sign |
| Window tower / canonical system | CWS, WTZ, DZG, GWZ, CSTW, SWC | kick admission; margin transport; two sites |
| Visibility | WVL, SRT, SquareRootThreshold, DCI | classified in models; output of every window theorem |
| Dimension zero | ATD, DZG | equivalent to the window sign |
| Edge / zero modes / Kähler | EHT, HWV, RW, DZG, GWZ, SWC | no zero mode; extremals edge-singular |
| Stars / gluing | HWV, CSAR, ADT | top gcd stratum |
| Effectivity / RR | ACS, LST, RIT, HF, AE, KPA | count-valued Hodge index; closed as a mechanism [D] |
| Rank / degree / continuation | TH, LA, HCF, PA, GTA, XN, ART, ZCG | Laguerre–Pólya; collision exclusion below the saddle |
| Scheduled prime sums | FU, CFC, RP, SZ, LI, FEL, EGC | scheduled energy lower bound |
| Screw / Krein–Schur | SZ | the canonical system of GWZ/CSTW |
| Paths | TG, SC, EHT, ACPL, HWV | source-defined HL along a flow |
| Realization | RN, PTR, W1C, PM | Krein positivity of zero coordinates |
| Prime-blind | PBAP | signed blind combinations |

## U-Π — precision and production

Core problem: square-root precision of one smoothed short-window prime count — the band on the prime side,
`|Σ_nw_n(f⋆f)(2m − log n) − 𝓗_m(f)| ≤ W(f)` — and its production by an exact mechanism.

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
| Terminal, receiving and sieve channels | AHD, CACT, CSAR, ACPL, V | finite prime boundary mass; simultaneous receiving; Brun–Titchmarsh-type bounds (Π31, Π32, Σ1q) |
| Window energy | WD, TG, CDG | inner caps (Π17, Π23) |
| Near-line density | WD, CDG, RBG, HEF, census, WVL | eight forms; thin Planck shadows; shallow visibility (Π5, Π22) |
| Census / clusters | SRT, IGP, Zeta23, CDG, TTPC, RIT-MayerZ | signed pair data beyond bandwidth one (Π7) |
| Square-root threshold | ZCG, SquareRootThreshold, WVL | camera readout aperture; sign-hiding ridge (Π29) |
| Heat size floor | LA, ZCG | sub-Weyl profile; saddle at `½/log X` (Π12, Σ49) |
| Tate jet / parity | WTZ, DZG, ATD, AHD | classified (Π24, Π25) |
| Sections / heights | ACS, LST, AOG, AET, AE, RIT, SPTL, CWS, KPA | closed as a mechanism (Π11h, Σ31) [D] |
| Bulk second order | AHD, ArtinMertens | Stieltjes constants, polar growth (Π26) |
| Finite realizations | RIT, CWS | no-go (Π18) |
| Genus | ACS, RHTower, LST, CWS, WTZ | upper law open (Π16) |
| Averages vs heights | WD, LA, SRT | density-zero exceptions; double-log stage (Π6) |
| Candidates | APF, EWJ, FEL, WBF, IRK | integral counts from a source lift |

Identities [L]: one-sided count ⇔ `κ = 0`; reflection-pair coupling = collar Hankel − smoothed count; coupling
rate = orbit-correlation rate = zero width; window-energy abscissa = twice the maximal depth; first
cyclotomic band abscissa `2Θ`; gauge-torus exponent range `[Θ, 1]`; Weil's window form = Tate jet = signed
count; Künneth `h¹` = counts + `½Q`.

## U-Γ — selection and reflection

Core problem: a source-defined mechanism making the reflection `ρ ↦ 1 − ρ̄` act as a positivity. The
distinguishing half is closed: flips separated at every density, fakes caught at their first prime, Weil cone
a point, lattice selection of `Λ`, Selberg-class rigidity, local identification at the square-root aperture
up to near-coincidences, second-order reading inside them. The reflection is constructed exactly on both
sides and identified; at a resonance its defect is `−∫2cosh(δu)4sinh²(δu)|F(u)F(−u)|`; at a near-coincidence
its sign is the sign of `w²`. Positivity of the reflection is RH.

| Face | Routes / programmes | Status / reduction |
|---|---|---|
| Typicality of the trivial point | MC, AGT, BAG, XN | Γ1; explicit `½` point off the special locus |
| Gluing of the global pole | SC, AKG, RIT | classified (Σ11, Γ11) |
| Margin, index, edge, degeneration selection | RIT, ACP, HKT, EHT, ACPL, RAPT, ADT, BGG | flips separated; only `Λ` degenerates completely (Γ2, Γ12, Γ18) |
| Weil cone / lattices | RHTower, BSU, GWZ | `{Λ}` (Γ23) |
| Selberg class | SEL | Euler rigidity; degree gap; degree one (Γ15, Γ33) |
| Camera identification | ZCG, SRT | local inversion at `λ > 1`; ζ readout at `λ > ½` (Γ36) |
| Second-order coalescence | ZCG | `w²` to `O(r³)` with loss `e^{C log²X}` (Γ44); polynomial scale open |
| Blindness | ZCG | aperture `πD` exact (Γ39) |
| Positivity certification | WVL, SquareRootThreshold | split columns; mixed counterexample (Γ40) |
| Fakes | ZCG | caught at their first prime (Γ41) |
| Euler columns and carriers | ZCG | Ramanujan = reality; domination non-selective; twins tilted (Γ37, Γ45) |
| Window selection | CWS | bounded windows blind (Γ20) |
| Density selection | ACPL | RvM-count countermodels (Γ21) |
| Tate counts | WTZ, DZG | do not descend (Γ27) |
| Window Frobenius | DZG, WTZ, RIT | similitudes scalar; Frobenius = translation (Γ28) |
| Intertwining coefficient | PM, RIT, RHTower | band poles = Hodge defect (Σ19, Γ22) |
| Frobenius at infinity | PL, CDG, RBG, EHT, AOG, AET, CWS, WTZ, GWZ | Rosati involution; collar Rosati pairing (Γ4, Γ19) |
| Degree-zero principles | KPA, ACS | bounded above ⇒ `≤ 0`; sublinear-error comparisons exact (Γ19) |
| Legendre invariant | KPA | RH ⇔ `J(ρ)` real (Γ42) |
| Mayer reflection | PM, W1C | defect formula; Krein–Lax–Phillips; sign = `δ = 0` (Γ24, Γ29, Γ32) |
| Retained channel | PM | side detector (Γ38) |
| Reality at near-coincidences | ZCG, LA | sign of `w²` ⇔ no heat collision (Γ46, Σ49) |
| Hecke structure | PM | cones tile; periods eigenfunctions (Γ34) |
| Resonant-state statistics | PM | retain the rate (Γ26) |
| Pre-divisor constructions | BSH, CDC, HJ, SEC, PCS, RFHM, EWJ, APF, WBF | zero-independent forcing (Γ5) |
| Function-field calibration | ACS, AKG, RIT, EHT, ACPL, LST, HWV, AET, AHD, CWS, WTZ, GWZ, ZCG, WVL | camera at the genus; collide or repel; columns at `(g − ½)log q` (Γ10, Γ31, Γ43) |
| Selection → sign | all selectors | no selector gives positivity (Γ16) |

## 2. Cross-family seams

| Seam | Statement | Routes on the seam |
|---|---|---|
| Σ ∩ Π: reflection pairs | `W(f ± f∘R) = 2W(f) ± 2𝒞_m(f)`, `𝒞_m` = collar Hankel − smoothed count | SWC, GWZ, CSTW, AOG, WL [L] |
| Σ ∩ Π: first stages | below `log 4` window sign = two-term count against `𝓗₀` within archimedean–polar `W` | SWC [L] |
| Σ ∩ Π: size versus sign | reflection-term bound below Lévy on windows `< log 5`, yet the primes are needed as signed payers | SWC [L/D] |
| Σ ∩ Π: collective kicks | kicks beyond collar locality are the smoothed count | SWC [L]; [D] |
| Σ: one number | every window statement is a lower bound for `a*(ζ)`; HF threshold = `a*(ζ)` | WVL, AHD, SWC, GWZ [L] |
| Σ: Perron range | positivity-preserving certificates exactly to `log ρ`; frustration by the pole (even) and the kicks (odd) | SWC [L] |
| Σ ∩ Γ: exact completion | Weil energy = Krein form of zero coordinates; window tests lift to Mayer fixed periods | RIT, WTZ [L] |
| Σ ∩ Γ: visibility | window sign reads depth and coherence (`k·pairEnergy ≤ L`); the camera reads density; unshielded vs shielded | WVL, ZCG, SquareRootThreshold [L] |
| Σ ∩ Π: shallow zeros | coherent shallow clusters visible at `δ²a³ > 3/2`; spread ones hide while `a³W ≲ L`; WD's near-line scale | WVL, CDG, DCI [L] |
| Σ: one canonical system | Levinson recursion; continuum margins; reflection coefficients freeze at `(−1)^n` | GWZ, SWC [L] |
| Σ ∩ C5: one moment problem | sectors ⇔ Hamburger/Stieltjes; theta Hankel PSD ⇔ native moment tails | SWC, TH, LA [L] |
| Σ: one gauge calculus | pole-charged representation; retained variance mandatory | SWC, ACT [L] |
| Σ ∩ Π: trivial divisor | collar Hankel inertia `(1, ∞)`; Gamma ladder and pole signs by sector | CSTW, SWC [L] |
| Σ ∩ Π ∩ Γ: dimension zero | classified | WTZ, DZG, ATD, AHD [L] |
| Σ: one decomposition | counts on every twisted direction + Weil at the frequency pole; terminal source polar | ADT, AHD, CACT [L] |
| Σ ∩ Π: growth exponent | ground-energy fall rate = zero width; excluded-depth law; height non-locality | WTZ, AHD, SquareRootThreshold, DCI, WVL [L] |
| Σ ∩ Γ: zero modes | radical, parity, two-site; never smooth | DZG, GWZ, SWC [L] |
| Σ ∩ Π: no slack | Weil cone a point; doubly-exponential margins; Szegő singular; heat size floor at the saddle; PM defect zero only at `δ = 0` | RHTower, M, GWZ, ZCG, RIT [L] |
| Σ ∩ Π: one gluing | Redheffer, nerve `χ̃`, glued index | ADT, HWV, AKG, MC [L] |
| Σ ∩ Π ∩ Γ: counts | Künneth counts pay all but `½Q`; no count produces the sign | CWS, WTZ, LST, AE, ACS, RIT, ATD, DZG [L]; [D] |
| Σ ∩ Γ: angle dictionary | angle over `𝔽_q` ≡ frequency over ℤ | AHD [L] |
| Σ ∩ Γ: one Frobenius | Frobenius at scale `t` = translation | DZG, RIT [L] |
| Γ ∩ P5: near-coincidences | collisions are near-coincidences; reality = sign of `w²`; camera reads `w²` to `O(r³)` | ZCG, LA, RHTower [L] |
| Π ∩ P5: heat size floor | sub-Weyl profile `6600/9991`; saddle `½/log X`; pair models collide below every scale | ZCG [L] |
| Π ∩ Γ: density aperture | blindness `πD`; sparse clusters `2a/π`; `λ = ½` readout; sign-hiding ridge | ZCG, WVL, SquareRootThreshold [L] |
| Σ: continuation | reality lost only through collision; `Λ = sup_X Λ_X` | ZCG, LA, DeBruijn [L] |
| Σ ∩ Π: Hermite–Biehler phase | every real finite carrier and symmetric half is a phase lattice above its horizon | ZCG, IGP, GWZ [L] |
| Π: window integer | collision charge = Wiener–Hopf index | WD, TG, SC-heat [L] |
| Π: one density statement | eight forms; thin Planck shadows | WD, CDG, census, MC, HEF [L] |
| Π: one mode, one torus | first cyclotomic band carries `2Θ`; gauge exponent range `[Θ, 1]` | MC, CAF, AGT [L] |
| Π: bulk, terminal, receiving | Stieltjes constants; terminal prime means finite Riemann sums; simultaneous receiving | AHD, ArtinMertens, CSAR [L] |
| Γ: one point, one cone | Weil cone `{Λ}`; lattice selection | RHTower, GWZ [L] |
| Γ: blind selectors | bounded windows, densities, contractions, local twists, Tate counts, resonant statistics, retained channel, finite carriers | CWS, ACPL, RIT, AKLT, WTZ, ZCG [L] |
| Γ: exactness by homogeneity | degree-zero Rosati and Tate principles | KPA, AE [L] |
| Σ: approximation | RH-true approximants close into Laguerre–Pólya | ART, W1C, PTR, LA, TH |
| Archimedean channel | Lévy jumps, exit charge, collar light cone, outward edge, trivial-divisor transmission, Gamma ladder | AKG, ALG, CHMD, RIT, ACPL, HWV, ACS, LST, ADT, CWS, WTZ, DZG, ATD, CSTW, SWC |

## 3. Route → core map

| Route | Core | Class | Face |
|---|---|---|---|
| WL | Π | C7, C19 | one-sided count; reflection-pair coupling |
| RW, EWU, OWU | Σ | C1, C4, C15, C19, C22, C25 | `a*(ζ)` by stages; below `log 4` two weights; sectors; Perron range |
| FU, CFC, RP, SZ, LI | Σ | C6 | scheduled prime sums; SZ also the Krein–Schur carrier of C15 |
| PA, TH, LA, HCF, GTA, XN | Σ | C5, C22 | Laguerre–Pólya; moment towers; continuation below the saddle |
| MC | Π (Γ) | C7, C8 | Möbius cancellation; gauge torus; typicality |
| TT | Σ | C4 | odd sector |
| TG | Π, Σ | C3, C12 | window integer; HL along paths |
| HF | Σ (Π, Γ) | C1, C12, C13, C14, C15, C18, C25 | complete family; threshold = `a*(ζ)`; terminal source polar |
| SRT, AIP, ACT | Σ (Π) | C1, C4, C11, C21, C23, C25 | complete atomic matrix; split-column certification; retained-variance shifts |
| SC | Σ, Π (Γ) | C2, C7, C3 | glued state; damped coupling; heat |
| CHMD | Σ | C4, C1 | odd sector |
| RN | Σ | C9 | realization |
| WD | Π (Σ) | C3, C11 | window energy; inner caps; near-line density |
| PM | Γ (Σ) | C9, C14 | Krein–Lax–Phillips space of zero coordinates; defect formula |
| JAS, CTF, PBM, RB | Π | C7, C19 | one-sided count |
| BAG | Γ | C8 | typicality / recurrence |
| ACS | Π (Σ, Γ) | C13, C1, C12, C15, C18, C20 | count face closed; Künneth effectivity = window sign; Legendre reality |
| APF, EWJ, WBF, IRK | Γ (Π) | C10, C13 | source lift with integral count |
| BSH, CDC, HJ, SEC, PCS, RFHM | Γ | C10 | pre-divisor constructions |
| EGC, FEL, MSC | Σ | C6, C1 | contour / likelihood / Sonin |
| PTR, W1C | Σ (Γ) | C9, C5, C14 | realization; Krein form of zero coordinates |
| ZCG | Γ (Σ) | C21, C23, C24, C5 | camera (complete); near-coincidence sign; continuation |
| WVL (programme) | Σ (Γ) | C25, C11, C23 | onset aperture; visibility laws |
| PBAP (support) | Γ (Σ) | C16 | prime-blind positivity |

## 4. What a closing argument must supply

| Needed | Present over ℤ | Missing |
|---|---|---|
| Sign of the minimal object | RH ⇔ the band on reflection pairs ⇔ `a*(ζ) = ⊤`; explicit coupling | the band at every step (B1) |
| Mechanism for the sign | pole-charged gauge calculus; exact certificate format below `log 4`; sliver signature; outward edge; soft entry; base to `0.362`; Perron to `log ρ` | a signed payment of the collective kicks against the pole square with retained variance (B3), first below `log 4` (B4, B5), past the Perron range (B49) |
| Full-space structure | subcritical PD; one critical multiple; threshold = onset aperture; terminal source polar; simultaneous receiving | `R₁(A) = ⊤` for one `A` past the base from the complete family (B33), then every `A` |
| Uniformity in `A` | each length finite; fall rate = width; visibility law; non-locality | window negativity exponent `< ½` (B16); transport across prime entries (B2) |
| Nondegeneracy | zero modes radical, parity, two-site, never smooth | no degenerate two-site lattice (B10) |
| Precision | one-sided count ⇔ RH; gauge spectrum `[Θ,1]`; eight-form density; caps to `σ_m` | square-root size of one smoothed count; inner caps (B19); `D_win` (B21) |
| Count from geometry | Künneth `h¹ = ½Q`; Weil's form a signed count; finite-field Stepanov | — (closed [D]) |
| Canonical selector | Weil cone `{Λ}`; Selberg rigidity; local identification at `λ > ½`; fakes at their first prime | — (automatic after positivity) |
| Reflection | exact zero-coordinate Krein space; defect formula `≤ 0`, zero only at `δ = 0`; `w²` read at second order | an arithmetic expression of the defect with manifest sign (B38); the sign of `w²` at every near-coincidence (B44) |
| Reality by continuation | heat path real for `t ≥ 1/8`; collision exit; size reaches `½/log X`; carriers HB above their horizon; integrality repulsion over `𝔽_q` | collision exclusion on `(0, ½/log X]` with Euler-product input inside the strip (B14) |
| Integrality with homotopy invariance | window index; `{0, ∞}` laws | a zero–one law for `κ` (B13); a structural bound on the window index (B12) |
