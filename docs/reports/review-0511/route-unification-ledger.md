# Route unification ledger — status quo

The 32 live routes and 18 candidates are faces of three core problems — **U-Σ** (sign), **U-Π** (precision and
production), **U-Γ** (selection and reflection) — and the three are one statement read in three coordinate
systems: the **arithmetic Hardy inequality** `P ≤ H` on every window, equivalently the **band**
`|𝒞_m(f)| ≤ W(f)` of a test `f` and its mirror `f∘R`, `R(v) = 2m − v`,
`𝒞_m(f) = 𝓗_m(f) − Σ_nΛ(n)n^{−1/2}(f⋆f)(2m − log n)`. U-Σ reads it as a form on the window, U-Π on the prime
side, U-Γ on the zero side. All routes measure one even integer `κ = #` distinct zeros right of the line and one
number, the onset aperture `a*(ζ)`; RH ⇔ `κ = 0` ⇔ `a*(ζ) = ⊤` ⇔ `1 ∈ ℋ(c)` ∀c. All are decided on the smallest
piece of the window tower, the reflection pair.

- **One criterion, one number, one inequality.** Every sign face is Weil's form on windows [L]; the positive
  half-widths form `[0, a*(Z)]` [L]; `R₁(A) = ⊤ ⇔ A/2 ≤ a*(ζ)` [L]; the arithmetic part is the unique multiple
  admissible on every window and no Hardy weight survives on odd tests [L]: Weil positivity is a critical Hardy
  inequality whose only open half is admissibility.
- **One format.** On every window both sectors are represented exactly: a neutral line-exact signed theta gauge
  (even), a shifted ground state (odd); nonnegativity of both on every window ⇔ RH [L].
- **One frustration.** Even sector: the pole, past `log ρ`, in every sign gauge; odd sector: the acting prime
  powers' anti-diagonals, from `½log 2`, in every sign gauge; the trivial zeros are paid at the centre [L].
- **One end of size.** `H < 0` by half-width `21/40`; the edge law crosses one at `c* ∈ (½log 5, ½log 6]`; finite
  rational Hecke templates end at spread 6 [L]. Beyond, the primes pay collectively and by sign.
- **One chain.** Before contact the window tower is a de Branges chain with explicit Hermite–Biehler functions;
  contact is a kernel blow-up [L]. RH ⇔ the chain is regular at every length [D].
- **Sign = precision.** `W(f ± f∘R) = 2W(f) ± 2𝒞_m(f)`; the band in prime form is identified with the Weil-lag,
  JAS, CTF, PBM and Robin criteria [L]; Suzuki's first variation is Weil's energy [L]; the Cayley ladder is the
  Toeplitz ladder of Li coefficients [W]; WD's inner caps are the off-line generating function [L].
- **Sign → location.** The visibility law turns window theorems into zero location [L]; the Krein–camera
  assembly would turn positivity at aperture `a` into location of every non-super-shallow off-line zero below
  height `≈ 2πe^{2a}` [D].
- **Reflection = zero side.** Krein form of zero coordinates; Mayer defect `−D_s = ∫K_σ|·|²` with
  `K_σ ∝ (b^{2σ−½} − b^{−(2σ−½)})²` in two coordinate systems [L]: U-Γ's positivity is U-Σ at a resonance, the
  identity `σ = ¼`.
- **Identification is complete; its residue is a sign.** Configurations fixed up to clusters of diameter
  `e^{−c log³T}`; squared gaps of polynomially small isolated clusters read from three prime-side images [L];
  reality is the sign of `𝓗 = 4(W₁² − W₀W₂)/W₀²` [L].
- **One continuation, one floor, one finite free law.** Reality lost only through collision; size reaches the
  saddle `½/log X` and no further [L]; Gaussian finite free capacity `o(d⁻²)`, Euler side stable with forced drift
  `θ_S/2`, ζ/Gamma/pole sides unstable [L]. P5's residual is U-Γ's sign.
- **One missing mechanism.** Over `𝔽_q`: Hodge index on primitive classes, or integrality forcing
  collide-or-repel along a deformation from a pure member [L]. Over ℤ: the same Gram is RH; counts are closed;
  the image is a `log p`-weighted sum without discreteness; domination is shared by every finite carrier [L/D].
  Missing: a signed payment of the collective kicks against the pole square on every reflection pair, in a frame
  where frustration persists (P1 = P4); or a sign-free nonnegative expression of the Mayer defect (P3); or a
  discreteness law at near-coincidences driving collide-or-repel for ζ (P5 = the U-Γ sign).

Evidence: `[L]` committed Lean; `[W]` working-tree Lean; `[P]` pipeline-card paper proof; `[D]` derived here.

## 0. The one object

| Reading | Statement | Anchor |
|---|---|---|
| Index | `κ = #{ρ : Re ρ > ½}` (distinct), even; RH ⇔ `κ < 2`; number of finite critical lengths | HKT, AKLT, CWS [L] |
| Onset aperture | `WindowPositiveAt Z a ⇔ a ≤ a*(Z)`; `a*(Z) = ⊤` ⇔ on-line; off RH `a*(ζ)` = contact; `a*(ζ) ≥ a₁` | WVL, AIP [L] |
| Hardy interval | `ℋ(c)` closed, antitone, `= ℝ` before `½log 2`, bounded after; `⋂ℋ(c) = {1}` ⇔ RH | FADF [L] |
| Calibration space | `𝒜(c)` convex cylinder; entering weights bounded; stage fibre compact; `⋂𝒜(c) = {Λ}` under RH | FADF, RHTower [L] |
| Threshold | `R₁(A) = ⊤ ⇔ A/2 ≤ a*(ζ)`; single-prime transport ⇔ RH | AHD, WVL [L] |
| Two sites | RH ⇔ `[[Q(ψ), c_ψ(t)],[c_ψ(t), Q(ψ)]] ≻ 0`; two real parameters `(γ, v)` decide | GWZ, SRT [L] |
| Reflection pair | `W(f) − |𝒞_m(f)| = ½min(W(G₊), W(G₋))`; coupling truncates to `n ≤ e^{2c}`; `𝒞_m(φ) = c_φ(2m)` | SWC, FADF [L] |
| Signed format | neutral signed even theta gauge `2V ≤ J_{M⁺}`; odd shifted ground state; both ⇔ window | SWC [L] |
| Frustration | even Markov iff `c ≤ log ρ`; unbalanced in every sign gauge past it; odd from `½log 2` | SWC, FADF [L] |
| Trivial zeros | mirror mass − reflected / antireflected energy; paid by centre killing | FADF [L] |
| Trace | `𝒥 = 𝒥_reg + 𝒦`; no point values | FADF [L] |
| Entry | outer `√n₀(log(1/δ) + B)`, inner `√n₀η(½log(1/δ) − ¼)` | FADF [L] |
| Size | edge law crosses one at `c* ∈ (½log5, ½log6]`; `H < 0` by `21/40` | FADF, SWC [L] |
| Moments | even ⇔ Hamburger, odd ⇔ shifted Hamburger, window ⇔ Stieltjes | SWC [L] |
| Lattice | Schur parameters in `(−1,1)` ⇔ RH | GWZ [L] |
| De Branges chain | complete Weil spaces, HB function `(z + i)K(i, z)`, unitary zero-moving, isometric inclusions; contact kernel blow-up | CSTW [L] |
| Symbol | `1 + ½log(1 + ξ²)` − bounded convolution; Riesz vectors bounded | CSTW [L] |
| Hecke graphs | correlation-form windows ⇔ finite rational Hecke graphs; no finite template at spread 6 | WTZ [L] |
| Tate | positive Tate dimensions `[0, κ(A)]`, `κ(A) → 0` | WTZ [L] |
| Complete family | PD below `(log N)^{1/8}`, one multiple across all entries; terminal source polar; twisted sectors cannot repair untwisted modes | CACT, AHD [L] |
| Visibility | `k·pairEnergy(δ,a) ≤ L`; `e^{2(δ−σ)a}/δ`; shielding barrier; non-locality | WVL [L] |
| Camera | inversion `λ > 1`; ζ readout `λ > ½`; moments of isolated polynomially small clusters; `𝓗` reads `w²` | ZCG [L] |
| Heat path | real for `t ≥ 1/8`; `Λ_X ≤ (6600/9991+ε)/log X`; saddle `½/log X`; FE-pair `w² ≥ 0` ⇔ RH | RHTower, ZCG [L] |
| Finite free | `R_d(fg) = R_d(f) ⊞_d R_d(g)`; Gaussian capacity `o(d⁻²)`; Euler drift `θ_S/2`; mollified stability ⇔ RH | FFP [L] |
| Reflection | `Q = 2Re[𝓦H, 𝓦H]`; `−D_s = ∫K_σ|T_{p,s}ψ_s|² = ∫K_σ|three-term|²` | RIT [L] |
| Li / Cayley | ladder entries `2λ_n`; RH ⇔ NSD on primitive ⇔ entrywise `≥ 0`; `𝔽_q`: sharp Weil bound | ALG [W] |
| Inner caps | inner-cap flux = `Σ_{off-line}m_ρe^{(ρ−½)t}` + bounded + `L²` | CDG [L] |
| Suzuki | first variation = complete Weil energy | RHTower [L] |
| Gluing | `κ(φ_c) = κ + 1`; Redheffer `det = M(N)` = reduced Euler characteristic of the wedge of spheres | AKG, HWV [L] |
| Weil cone | `{Λ}` | RHTower [L] |

## 0.1 The window axis

| Coordinate | Reading at half-width `c` | Anchor |
|---|---|---|
| Markov death | support `e^{−3/4}` | SWC [L] |
| Perron threshold | `c = log ρ ≈ 0.2812` (even band; switching fails beyond) | SWC, FADF [L] |
| Odd frustration onset | `c = ½log 2 ≈ 0.3466` (every sign gauge) | FADF [L] |
| Known sign | all tests to `a₁` (`181/500 < a₁ < 181/500 + 5×10⁻⁷`), floor `1/20000`; reflection pairs floor `1/8000` to `enlarged` | AIP, SWC [L] |
| Odd unit window | `c = ½`: one weight in an interval; margin `≈ 2×10⁻⁴` (open) | SWC [L/N] |
| First prime stage | `2c = 21/20`: `w₂ ≤ 0` excluded (`H < 0`); stage loan fails | WTZ, SWC, AHD [L] |
| Prime-three entry | `2c = log 3`: compact two-weight set; soft entry sharp | SWC, FADF [L] |
| Prime 3 as collar mass / deleted | fail for `c ≥ 287/500` / `c ≥ 3/5` | SWC [L] |
| Variance-free certificates | fail for `c > 273/400` | SWC [L] |
| Prime-free half-window | sharp at `c = log 2` | SWC [L] |
| Tate horizons exact | through `2c = log(81/16)` | WTZ [L] |
| Edge-law crossing | `c* ∈ (½log 5, ½log 6]` | FADF [L] |
| End of finite templates | spread 6 (`2c = log 6`) | WTZ [L] |
| Zero information | from `c ≥ 4`; `≈ 20` with present constants | WVL [L]; [D] |
| Ground energy | `μ(a) ≤ K exp((11/2)a − πe^{2(a−2)})` | M [L] |
| Camera aperture | `λ·½log(T/2π)`: isolated zeros at `λ > ½`; configurations at `λ > 1`; Krein–camera height `≈ 2πe^{2a}` | ZCG [L]; [D] |
| Height non-locality | zeros below `exp((e^{2δa}−2)/(4δ) − a)` do not decide the window | WVL [L] |
| Contact | kernel blow-up at `a*` off RH | CSTW [L] |

Each fixed window length is a sub-RH finite problem; all lengths together are RH; one prime step at every length
is RH.

## 0.2 The degeneration, angle and camera dictionary

| Object | Over ℤ | Over `𝔽_q` | Classes |
|---|---|---|---|
| Resolution axis | overlap `c`, `c⁸ ≍ K log N` | atom width `w` | C1 |
| Twisted direction | frequency `u`: positive Hurwitz count | angle `θ_i` | C1, C18 |
| Trivial direction | pole of the frequency counts at `u = 0` | main term | C1, C18 |
| Li / Cayley ladder | `2λ_n`; positivity ⇔ RH | `2(2g − Σβ_i^n)` = sharp Weil lower bound | C30 |
| First failure | two-site; extremals edge-singular | at index `2g` | C15, C19 |
| Camera threshold | `λ = ½` isolated zeros; `λ > 1` configurations; clusters to `e^{−c log³T}` | order `g` | C21, C23 |
| Certification by sign | split columns; mixed `(g − ½)ℓ` | positivity at `a > (g − ½)log q` | C21, C25 |
| Repulsion | phase speed above the carrier horizon; size to `½/log X`; Euler drift `θ_S/2` | integrality: collide or repel | C5, C24, C28 |
| Reality | sign of `𝓗` at a near-coincidence | trace points `β + β⁻¹ ∈ [−2, 2]` | C5, C21 |
| Purity by deformation | heat path pure at `t ≥ 1/8`, collision exit; no discreteness | pure member + integrality + continuity | C5 |

## 1. Equivalence classes of routes

Routes in one class compute the same quantity; a theorem in one class transfers through the listed identity.

| Class | Common quantity | Routes | Identity joining them |
|---|---|---|---|
| C1 Weil's window form | `Q ≥ 0` on windows of every length | HF, SRT, AIP, ACT, ACS-atomic; RW, EWU, OWU, MSC, FEL; AHD, CACT, CSAR | window ⇔ `R₁ ≡ ⊤` ⇔ `ι = 0` ⇔ Hardy admissibility [L] — face of C25 |
| C2 Glued state | `κ(φ_c) − 1` | SC, AKG | Grams are compressions [L] — face of C1 |
| C3 Window integer | collision charge, heat count, window index | WD-charge, SC-heat, LA-heat, TG, HEF | index = Wiener–Hopf index [L] — face of C11 |
| C4 Sectors and ground states | odd/even sector sign; signed gauges | CHMD, TT, OWU, EWU, ACT, SWC | sectors = band at the centre; exact two-sector format; frustration unswitchable [L] — face of C1 |
| C5 Rank / degree / continuation | Laguerre–Pólya; collision exclusion below `½/log X` | TH, HCF, PA, GTA, LA, XN; ZCG | reality lost only through collision; RH ⇔ simple zeros of `H_t` [L] — meets C21 at near-coincidences |
| C6 Scheduled prime sums | lower bound of a scheduled energy | FU, CFC, RP, EGC, FEL | explicit-formula functionals bounded below ⇔ RH [L] |
| C7 One-point precision | `ψ − x`, `M(x)`, cyclotomic mode, coupling, Redheffer, gauge exponent | WL, MC, PBM, RB, JAS, CTF, SC-coupling | reflection-pair count band ⇔ every classical criterion [L] — face of C19 |
| C8 Selection / typicality | trivial gauge point | MC-typicality, BAG, XN | RH ⇔ trivial point typical [L] |
| C9 Realization | spectral reality of a constructed operator | RN, PTR, W1C, PM-Mayer | Mayer Krein positivity ⇔ RH [L] |
| C10 Pre-divisor | a section defined before the divisor | APF, BSH, CDC, EWJ, HJ, PCS, RFHM, SEC, WBF | zero-independent forcing (Γ5) |
| C11 Local zero location | window energy, inner caps, Hecke defect, near-line density | WD, census, HEF, SRT-local | inner caps = off-line generating function; eight-form density [L] |
| C12 Hodge–Lefschetz / gluing | HL on the positive locus; zero modes; top gcd stratum | HF-Hodge, ACS-Hodge, RIT, EHT, TG, DZG, GWZ, HWV | zero modes = radical; prime complex = wedge of spheres [L] |
| C13 Sections, counts, Tate | count-valued primitive `h¹`; Tate jet | ACS-effectivity, HF-RR, IRK, WTZ, LST, KPA | closed as a sign mechanism [L/D] |
| C14 Reflection | Rosati involution; Lewis defect; Krein form | PM, HF band poles, W1C | defect in two coordinate systems [L] — face of C1 |
| C15 Window tower and canonical system | stages; lattices; de Branges chain | CWS, WTZ, DZG, GWZ, CSTW, SWC; SZ | stage criterion; Levinson; de Branges chain to contact [L] |
| C16 Prime-blind cone / calibration | `𝒜(c)`; blind tests | PBAP, FADF | Weil cone `{Λ}`; entry confinement [L] — face of C1 |
| C17 Dimension zero | domination of point counts | ATD, DZG | bare domination ⇔ `Q ≥ 0` [L] |
| C18 Angle dictionary | Hurwitz forms of angles / frequencies | AHD, ACS, LST, GWZ | angle `u` over `𝔽_q` ≡ frequency `u` [L] |
| C19 Two-site band | `|𝒞_m(f)| ≤ W(f)` | GWZ, AOG, SWC, SRT; every route of C1, C4, C7, C14, C15, C26 | RH ⇔ two-site PD ⇔ two-parameter family [L] |
| C20 Selberg-class rigidity | Euler-log discrepancy; degree; FE twins | SEL; ACS, HF fakes | Gamma-independent rigidity [L] |
| C21 Configuration camera | identification by the Weil image | ZCG, SRT-identification, SquareRootThreshold | inversion and polynomial-scale second order [L] — complete to `e^{−c log³T}`; residue = sign of `𝓗` |
| C22 Jet moment problems | Hankel/Toeplitz positivity of one jet sequence | SWC-sectors, TH, LA-Jensen, GWZ-lattice | sectors ⇔ Hamburger/Stieltjes; Jensen ⇔ Pólya–Schur [L] |
| C23 Density apertures | completeness radius on a configuration | ZCG-blindness, Π29 | blindness `πD`; Ingham scales `π/(2a)` (one depth), `π/a` (any depth) [L] — face of C21 |
| C24 Hermite–Biehler phase | `A(s) + A(1−s)` with dominant `A` | ZCG carriers, FFP Euler carriers, census | phase lattice above the horizon; finite free drift `θ_S/2` [L] |
| C25 Onset aperture | `a*(ζ)` | WVL, SRT, HF, every window route | closed-interval law; visibility law [L] |
| C26 Hardy interval | `1 ∈ ℋ(c)` ∀c | FADF; every route of C1 and C4 | optimal Hardy term ⇔ RH; uniqueness and criticality unconditional [L] — face of C25 |
| C27 Weil kernel / contact | `K_a(z,z)` bounded up to every length | CSTW, RW, SZ | de Branges chain; contact blow-up [L] — face of C15 and C25 |
| C28 Finite free stability | stability of `R_d(Ξ)`, `R_d(Ξ·M_S)` at infinitely many degrees | FFP, LA, TH | Jensen dictionary; de Bruijn–Newman in finite form [L] — face of C5 and C22 |
| C29 Rational Hecke graphs | positivity of finite rational graphs of bounded spread | WTZ, CWS | Følner averaging; templates below spread 6 [L] — face of C15 and C17 |
| C30 Li / Cayley ladders | `λ_n ≥ 0` ∀n | LI, ACS, HF | Cayley ladder = Toeplitz ladder of `2λ_n`; Hodge index = Metzler sign [W] — face of C12 and C19 |

C1, C2, C4, C7, C14, C15, C16, C17, C22, C26, C27, C29 and C30 are one quantity, `a*(ζ)` (C25), read at its
minimal size in C19. C3 is a face of C11, and C11's open estimates are zero-free statements verbatim. C5, C21
and C28 meet at near-coincidences: collision exclusion, the sign of `𝓗` and finite free stability at infinitely
many degrees are one problem. C6 is RH-complete only in the limit of its schedule. C13 is the production face of
C19 and is closed. C8–C10, C18, C20, C21 and C23 are selection and calibration faces, C21 and C23 complete
identifications; C24 is the phase face of C5, C11 and C28.

## U-Σ — the sign

Core problem: `1 ∈ ℋ(c)` for every `c` — in format form, the neutral signed theta-gauge inequality and the
shifted-ground-state inequality on every window; in tower form, every prime kick paid by its signed fold at zero
slack; in canonical-system form, a regular Hamiltonian at every length.

| Layer | Status | Anchor |
|---|---|---|
| Receivers | window, onset aperture, Hardy interval, two-site, two-parameter family, reflection pair, sectors, moments, lattice, threshold, single-prime transport, index, Krein, PBAP, Suzuki, Li ladder, mollified Jensen | WVL, FADF, GWZ, SRT, SWC, AHD, CWS, RIT, RHTower, ALG, FFP [L/W] |
| Minimal object | reflection pair; first failure two-site; extremals edge-singular | GWZ, SWC [L] |
| Format | exact two-sector signed certificate on every window | SWC [L] |
| Frustration | unswitchable: even past `log ρ`, odd from `½log 2` | FADF [L] |
| Size | ends before `21/40`; edge law `c* ∈ (½log5, ½log6]` | FADF [L] |
| Entry | calibration space; sharp logarithmic entry law | FADF [L] |
| Canonical system | lattice Levinson; continuum margins; de Branges chain to contact | GWZ, SWC, CSTW [L] |
| Finite reduction | rational Hecke graphs; templates below spread 6 | WTZ [L] |
| Complete family | size-only; twisted sectors cannot repair untwisted modes | CACT, AHD [L] |
| Visibility | sign → location; shielding; non-locality | WVL [L] |
| No slack | unique admissible multiple; no Hardy weight; Szegő singular; contact blow-up | FADF, GWZ, CSTW [L] |
| Dimension zero | classified | DZG, ATD [L] |

| Face | Routes / programmes | Reduction |
|---|---|---|
| Complete atomic matrix | HF, SRT, AIP, ACT, CACT, CSAR, ACPL, RAPT, TM, ADT, AHD | size-only layers closed; `R₁ ≡ ⊤` ≡ `a*(ζ) = ⊤`; single-prime transport |
| Aperture ground minimum / chain | RW, EWU, OWU, MSC, CFC, SP, CSTW | `a*(ζ)` by stages; de Branges chain regular |
| Sectors / ground states | CHMD, TT, ACT, OWU, EWU, SWC, FADF | the two-sector format inequalities |
| Hardy / calibration | FADF, PBAP | `1 ∈ ℋ(c)`; arithmetic point in `𝒜(c)` |
| Moment problems | SWC, TH, LA | Stieltjes/Hamburger positivity |
| Glued state | SC, AKG | Beurling-schedule sign |
| Window tower | CWS, WTZ, DZG, GWZ, CSTW, SWC | kick admission; two sites |
| Hecke graphs | WTZ | finite matrices below spread 6 |
| Visibility | WVL, SRT, DCI | output of every window theorem |
| Edge / zero modes / Kähler | EHT, HWV, DZG, GWZ, SWC | no zero mode |
| Effectivity / RR | ACS, LST, RIT, HF, KPA | closed as a mechanism [D] |
| Li / Cayley | LI, ALG | `λ_n ≥ 0` |
| Suzuki | SZ | first variation = Weil energy |
| Rank / continuation / finite free | TH, LA, HCF, PA, GTA, XN, ZCG, FFP | collision exclusion; stability at infinitely many degrees |
| Scheduled prime sums | FU, CFC, RP, EGC, FEL | scheduled energy lower bound |
| Realization | RN, PTR, W1C, PM | Krein positivity |

## U-Π — precision and production

Core problem: square-root precision of one smoothed short-window prime count — the band on the prime side — and
its production by an exact mechanism.

| Face | Routes / programmes | Reduction |
|---|---|---|
| Reflection-pair coupling | SWC, GWZ, CSTW, AOG | collar Hankel − smoothed count within `W(f)`; truncates to `n ≤ e^{2c}` |
| Classical one-sided counts | WL, PBM, RB, JAS, CTF | identified with the band [L] |
| Two-term count below `log 4` | SWC, RW, OWU, EWU, ACT | `w₂A₂ + w₃A₃` against `𝓗₀` within `W` |
| Collective kicks | SWC, FADF | beyond size: by sign, collectively |
| One cyclotomic mode / gauge torus | MC, CAF, AGT | first-band energy; exponent `½` at the trivial point |
| Integer producers | WL, AKLT | `ε`-uniform producer |
| Möbius / nerve | MC, HWV, ADT | half-power cancellation; wedge of spheres |
| Window energy / inner caps | WD, TG, CDG | off-line generating function |
| Near-line density | WD, CDG, census, WVL | eight forms; thin Planck shadows |
| Census / clusters | SRT, Zeta23, CDG | signed pair data beyond bandwidth one |
| Heat size floor | LA, ZCG | sub-Weyl profile; saddle |
| Finite free capacity | FFP | Gaussian `o(d⁻²)`; shift regime semicircular |
| Euler phase drift | FFP, ZCG | `θ_S/2`; carrier horizon |
| Receiving / terminal / sieve channels | AHD, CACT, CSAR, ACPL, BVI | size-only bookkeeping |
| Sections / heights / Tate | ACS, LST, WTZ, DZG, KPA | closed as a mechanism [D] |

Identities [L]: one-sided count ⇔ `κ = 0`; reflection-pair coupling = collar Hankel − smoothed count = orbit
correlation; window-energy abscissa = twice the maximal depth; inner-cap flux = off-line generating function;
gauge-torus range `[Θ, 1]`; Weil's window form = Tate jet; Suzuki first variation = Weil energy; Cayley ladder =
Li coefficients.

## U-Γ — selection and reflection

Core problem: a source-defined mechanism making the reflection `ρ ↦ 1 − ρ̄` act as a positivity. The
distinguishing half is complete: flips separated, fakes caught at their first prime, Weil cone a point,
Selberg-class rigidity, identification to `e^{−c log³T}` with second-order reading at polynomial scale. The
reflection is constructed exactly on both sides; at a resonance its defect is `−∫K_σ|·|²` in two coordinate
systems; at a near-coincidence its sign is the sign of `𝓗`. Positivity of the reflection is RH.

| Face | Routes / programmes | Status / reduction |
|---|---|---|
| Typicality of the trivial point | MC, AGT, BAG, XN | Γ1 |
| Gluing of the global pole | SC, AKG, RIT | classified |
| Weil cone / lattices / calibration | RHTower, GWZ, FADF | `{Λ}`; unique admissible multiple |
| Selberg class | SEL | rigidity |
| Camera identification | ZCG, SRT | complete to `e^{−c log³T}` (Γ36, Γ44) |
| Reality at near-coincidences | ZCG, LA | sign of `𝓗` ⇔ no heat collision (Γ46) |
| Krein–camera | CSTW, ZCG | positivity ⇒ on-line mimic ⇒ location (Γ47, assembly) |
| Euler columns and carriers | ZCG, FFP | domination non-selective; Euler drift `θ_S/2` |
| Mayer reflection | PM, W1C | defect `−∫K_σ|·|²`; nonnegative representation ⇔ RH (Γ24) |
| Frobenius at infinity / Rosati | CWS, WTZ, GWZ, AOG | Γ4, Γ19 |
| Li / Cayley ladders | ALG, LI | Metzler sign = Hodge index; `𝔽_q` calibration (Γ10) |
| Pre-divisor constructions | BSH, CDC, HJ, SEC, PCS, RFHM, EWJ, APF, WBF | Γ5 |
| Function-field calibration | many | camera at the genus; collide or repel; ladders |
| Selection → sign | all selectors | no selector gives positivity (Γ16) |

## 2. Cross-family seams

| Seam | Statement | Routes on the seam |
|---|---|---|
| Σ ∩ Π: reflection pairs | `W(f ± f∘R) = 2W(f) ± 2𝒞_m(f)`; `W − |𝒞| = ½min(W(G₊), W(G₋))` | SWC, GWZ, CSTW, AOG, WL [L] |
| Σ ∩ Π: Hardy form | `W = H − P`; `1 ∈ ℋ(c)`; unique admissible multiple | FADF [L] |
| Σ ∩ Π: size versus sign | edge law to `c*`; `H < 0` by `21/40`; primes pay by sign beyond | FADF, SWC [L] |
| Σ ∩ Π: classical receivers | reflection-pair band ⇔ Weil-lag, JAS, CTF, PBM, Robin | SWC [L] |
| Σ: one format | neutral signed even gauge + shifted ground state on every window | SWC [L] |
| Σ: frustration | unswitchable in both sectors | FADF [L] |
| Σ: one chain | de Branges chain before contact; contact blow-up | CSTW [L] |
| Σ ∩ C29: finite reduction | rational Hecke graphs; templates end at spread 6 | WTZ [L] |
| Σ ∩ Γ: exact completion | Weil energy = Krein form; Mayer defect in two coordinates | RIT [L] |
| Σ ∩ Γ: visibility and camera | window sign reads depth and coherence; camera reads configurations; Krein–camera links them | WVL, ZCG [L]; [D] |
| Σ ∩ Π: one canonical system | Levinson; continuum margins; reflection coefficients at `(−1)^n` | GWZ, SWC [L] |
| Σ ∩ C5: one moment problem | sectors ⇔ Hamburger/Stieltjes; theta Hankel; Jensen | SWC, TH, LA [L] |
| C5 ∩ C28: finite free | heat = `⊞_d` with Hermite; Gaussian capacity `o(d⁻²)` ⇔ de Bruijn–Newman criticality | FFP [L] |
| Σ ∩ Π: trivial divisor | collar Hankel inertia `(1, ∞)`; centre pays the trivial zeros | CSTW, FADF [L] |
| Σ: one decomposition | counts on twisted directions + Weil at the frequency pole | AHD, CACT [L] |
| Σ ∩ Π: no slack | unique multiple; no Hardy weight; Szegő singular; saddle; PM defect zero only at `σ = ¼` | FADF, GWZ, ZCG, RIT [L] |
| Σ ∩ Π: gluing | Redheffer = reduced Euler characteristic of the wedge of spheres | HWV, ADT [L] |
| Σ ∩ Π ∩ Γ: counts | closed as a sign mechanism | CWS, WTZ, LST, ACS, RIT, DZG [L/D] |
| Σ ∩ Γ: Li / Hodge | Cayley ladder: Hodge index = Metzler sign = Li | ALG [W] |
| Γ ∩ P5: near-coincidences | collisions are near-coincidences; reality = sign of `𝓗` | ZCG, LA, RHTower [L] |
| Π ∩ P5: heat size floor | `6600/9991`; saddle `½/log X`; pair models collide | ZCG [L] |
| Π ∩ Γ: density aperture | blindness `πD`; Ingham scales; `λ = ½` readout | ZCG, WVL [L] |
| Σ ∩ Π: Hermite–Biehler phase | finite carriers and symmetric Euler products real above their horizon; drift `θ_S/2` | ZCG, FFP [L] |
| Π: inner caps | off-line generating function | WD, CDG [L] |
| Γ: blind selectors | bounded windows, densities, contractions, twists, Tate counts, resonant statistics, retained channel, finite carriers | CWS, ACPL, RIT, AKLT, WTZ, ZCG [L] |
| Archimedean channel | Lévy jumps, edge killing, centre killing, logarithmic symbol, Gamma ladder | SWC, FADF, CSTW, ATD [L] |

## 3. Route → core map

| Route | Core | Class | Face |
|---|---|---|---|
| WL | Π | C7, C19 | one-sided count; reflection-pair band |
| RW, EWU, OWU | Σ | C1, C4, C15, C19, C22, C25, C26, C27 | `a*(ζ)` by stages; two-sector format; de Branges chain |
| FU, CFC, RP | Σ | C6 | scheduled prime sums |
| SZ | Σ | C15, C27 | Suzuki first variation = Weil energy |
| LI | Σ (Π) | C30, C6 | Cayley ladder = Li coefficients |
| PA, TH, LA, HCF, GTA, XN | Σ | C5, C22, C28 | Laguerre–Pólya; moments; continuation; finite free |
| MC | Π (Γ) | C7, C8, C12 | Möbius cancellation; gauge torus; wedge of spheres |
| TT | Σ | C4 | odd sector |
| TG | Π, Σ | C3, C12 | window integer; inner caps |
| HF | Σ (Π, Γ) | C1, C12, C13, C14, C15, C18, C25 | threshold = `a*(ζ)`; single-prime transport |
| SRT, AIP, ACT | Σ (Π) | C1, C4, C11, C19, C21, C25 | complete atomic matrix; two-parameter family; anti-diagonal classification |
| SC | Σ, Π (Γ) | C2, C7, C3 | glued state; damped coupling as heat average |
| CHMD | Σ | C4, C1 | odd sector |
| RN | Σ | C9 | realization |
| WD | Π (Σ) | C3, C11 | inner caps = off-line generating function; near-line density |
| PM | Γ (Σ) | C9, C14 | Krein–Lax–Phillips; defect in two coordinates |
| JAS, CTF, PBM, RB | Π | C7, C19 | identified with the band |
| BAG | Γ | C8 | typicality / recurrence |
| ACS | Π (Σ, Γ) | C13, C1, C12, C18, C20, C30 | count face closed; Künneth effectivity = window sign |
| APF, EWJ, WBF, IRK | Γ (Π) | C10, C13 | source lift with integral count |
| BSH, CDC, HJ, SEC, PCS, RFHM | Γ | C10 | pre-divisor constructions |
| EGC, FEL, MSC | Σ | C6, C1 | contour / likelihood / Sonin |
| PTR, W1C | Σ (Γ) | C9, C5, C14 | realization |
| ZCG | Γ (Σ) | C21, C23, C24, C5 | camera (complete to `e^{−c log³T}`); sign of `𝓗` |
| FFP | Σ (Π) | C28, C22, C24, C5 | finite free stability; Euler drift |
| FADF (programme) | Σ | C26, C4, C16 | Hardy interval; frustration; entry |
| CSTW (programme) | Σ | C27, C15 | de Branges chain; contact |
| WVL (programme) | Σ (Γ) | C25, C11, C23 | onset aperture; visibility |
| WTZ (programme) | Σ | C29, C15, C13 | rational Hecke graphs; Tate |
| PBAP (support) | Γ (Σ) | C16 | prime-blind positivity |

## 4. What a closing argument must supply

| Needed | Present over ℤ | Missing |
|---|---|---|
| Sign of the minimal object | RH ⇔ the band on reflection pairs ⇔ `1 ∈ ℋ(c)` ∀c; explicit coupling | the band at every step (B1) |
| Mechanism for the sign | exact two-sector format on every window; centre pays trivial zeros; sharp entry law; base to `a₁`; Perron to `log ρ` | the format inequalities on every window (B3), first below `log 4` (B4, B5), in a frame where frustration persists (B49) |
| Full-space structure | subcritical PD; one multiple across all entries; threshold = onset aperture | an HF-native window beyond the base (B33), then every `A` |
| Uniformity in length | each length finite; single-prime transport ⇔ RH; de Branges chain | transport across one prime at every length (B2); regularity of the chain (B51) |
| Nondegeneracy | zero modes radical, two-site, never smooth; contact blow-up | no degenerate two-site lattice (B10); no contact |
| Precision | one-sided count ⇔ RH; inner caps = off-line generating function | square-root size of one smoothed count; inner caps at every stage (B19); `D_win` (B21) |
| Count from geometry | Künneth `h¹ = ½Q`; finite-field Stepanov; ladders over `𝔽_q` | — (closed [D]) |
| Canonical selector | Weil cone `{Λ}`; unique admissible multiple; identification to `e^{−c log³T}` | — (automatic after positivity) |
| Reflection | Krein space of zero coordinates; defect `−∫K_σ|·|²` in two coordinates; `𝓗` reads `w²` | a sign-free nonnegative defect identity (B38); `𝓗 ≥ 0` on every near-coincidence (B44) |
| Reality by continuation | heat path real for `t ≥ 1/8`; collision exit; size to `½/log X`; finite free criticality | collision exclusion below `½/log X` (B14); mollified stability (B52) |
| Discreteness | camera at polynomial scale | collide or repel for ζ (B54); an integral structure along a deformation (2.4) |
