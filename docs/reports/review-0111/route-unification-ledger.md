# Route unification ledger — status quo

The 33 live routes and 16 candidates are faces of three core problems. The three core problems are
three readings of one even integer, `κ = κ(K_ζ)`: the negative index of Weil's correlation on the
dilations of `ℚ`, read on the pole-orthogonal hyperplane `v₁^⊥`. Four formal frames make `κ` an
invariant of the complete Weil family:
- **HWV** (Kähler package): `v₁^⊥` is the primitive part. Transport along the overlap flow is free.
  RH ⇔ hard Lefschetz on the positive locus.
- **EHT** (edge): RH ⇔ no edge; a finite edge is a zero mode.
- **ACPL** (coupling): RH ⇔ bounded inter-tower coupling; the coupling is as large as the kernel.
- **AKG** (gluing): `κ(φ_c) = κ + 1` at every place.

The receiver theory of the atomic families adds a fifth frame. The overlap axis is the aperture
axis. A multiple `K` of the critical overlap `c*_φ(N)` synthesizes every smooth test of radius
`½ log K + O(1)`.

Evidence tags as in `walls-ledger.md`.

## 0. The one object

| Reading | Statement | Anchor |
|---|---|---|
| Index | `κ(K_ζ) = #{ρ : Re ρ > ½}` (distinct), even, carried by one two-prime lattice | HKT, AKLT [M] |
| Bounded kernel | RH ⇔ `‖K_ζ(u)‖ ≤ Re K_ζ(1)` ∀u (Castelnuovo–Severi at rational scales) | RIT `riemannHypothesis_iff_castelnuovoSeveri` [L] |
| Coupling | RH ⇔ bounded `K(uv) − K(u) − K(v) + K(1)` on one `⟨p⟩×⟨q⟩`; rate = width; coupling ≍ kernel | ACPL [L] |
| Window prime error | `K_ζ(u)` = smoothed prime error in a fixed-length multiplicative window at `u`, normalized by `√u` | HKT [M]; reading [D] |
| Glued state | `κ(φ_c) = κ + 1` at `∞` and every prime | AKG `negIndex_weilArchState_eq_add_one` [L] |
| Primitive part | boost hyperplane = `v₁^⊥` = Markov = harmonic hyperplane; `v₁` = ground state = Kähler class | RIT [M]; HWV [L] |
| Kähler package | HR ∧ HL ⇔ strict HR; HR transports wherever HL holds on the HR locus; RH ⇔ HL on the PSD locus along `1 ≤ c ≤ 2(log N)^β`, `β > ½`; Liouville = HL | HWV `TheKahlerPackage` [L]; `TheLiouvilleProperty` [U] |
| Edge | RH ⇔ `e_φ ≡ ∞`; a finite edge is PSD with a zero mode; no edge ⇔ bounded coupling | EHT, ACPL [L] |
| Overlap = aperture | at `c*_φ` margin = synthesis error = `1/log N`; RH ⇔ positivity at every `K·c*_φ`; `K` sees radius `½ log K + O(1)` | TM `ReceiverRate` [L] |
| Aperture floor | `μ(A) ≤ K exp((11/2)A − πe^{2(A−2)})` unconditionally; every positive aperture transport loses doubly exponentially | ArithmeticCompensationTheory `TheApertureFloorMustDecayDoublyExponentially` [L] |
| Visibility (RVM model) | an isolated pair of depth `δ`, height `ξ` is seen at aperture `a` iff `S_δ(a) > (1/2π)log(ξ/2π)` | ACS visibility law [L] |
| Scaling surface / effectivity | cycles `aH + bV + f`; Castelnuovo–Severi defect = Weil's form; RH ⇔ an effectivity with RR and ample axioms; quadratic RR ⇔ renormalized Hodge index; theta `h⁰` gives RR on `Spec ℤ` and the pole plane | ArithmeticCastelnuovoSeveri `TheScalingSurface`, RIT, ArithmeticOrientationGeometry `TheThetaH0OfSpecZ` [L] |
| First rung | finite Hodge defect ⇔ bounded heat counts ⇔ bounded collision charges ⇒ `Θ < 1`; RH = defect `< 2` | ArithmeticOrientationGeometry `TheIndexExit` [L] |
| Stars | star of `d` ≅ family at `(c⌊N/d⌋/N, ⌊N/d⌋)`; positivity descends; flux `log d` ⇔ `Λ ∗ 1 = log` | HWV [L] |
| Packet identity | complete form on packets = `J_N + ½A_N` + bounded diagonal − shell degree + boundary terms | ACPL [M] |
| Heat | `κ(φ_c^{(t)}) − 1 = N(t)/2` = future collision pairs | AKG, RIT [M] |
| Quantum | collision charge = Fredholm index; `κ ≤ sup O`; RH ⇔ `O < 2` per window | CDG [M]; EHT [L] |
| Hecke defect | mean `O(log U)`; `o(log U)` ⇔ critical-scale clustering; fixed scale ⇔ corridor; one constant over dyadic scales ⇔ RH | CDG `LogScaleHeckeDefect` [L] |
| Frobenius at infinity | `σ(ρ) = 1 − ρ̄`; RH ⇔ `σ` trivial ⇔ Hecke similitude of the collided form; `κ = #` moved zeros | EHT `FrobeniusAtInfinity` [L] |
| Partner angle | resonant states `E*(·,ρ/2)`, `E*(·,(1−ρ̄)/2)`: `cos² = 4Reρ(1 − Reρ)`, saturated iff `Re ρ = ½` | RHTower `EisensteinResonantPartnerAngle` [L] |
| Mayer determinant | `D(w,λ) = A + ζ(w)B` for the regularized Gauss–Mayer operator; `B(w,−1) = 0` | RIT `GaussMayer*` [L] |
| Künneth | `κ(K_ζ⊠K_ζ) ∈ {0, ∞}`; no softening at any horizon | RIT [M]; EHT [L] |
| Finite-index constraints | `κ ≤ r` ⇔ translation-stable positive constraints of dimension `≤ r` | HKT `Index` [L] |
| Selection | every prime-set flip separated; self-similar counterterm only for generalized von Mangoldt weights | RIT [M]; HWV `TheDivisorIdentitySelects` [L] |

The three walls are the three ways a reading of `κ` fails:
- **Σ**: the sign of the complete form is not decided by estimates beyond the critical overlap.
  There an aperture of positive radius enters, and the aperture floor dies doubly exponentially,
  so only an exact (effectivity / Riemann–Roch), quantized or structural producer can decide it.
- **Π**: the prime statistics are not precise enough. This concerns the windowed one-point error
  (the kernel) and the conjugate-diagonal depth functional (the Hecke defect).
- **Γ**: selection of ζ does not produce positivity. Every selector is a margin or a counterterm
  identity.

## 1. Equivalence classes of routes

Routes in one class compute the same quantity; a theorem in one class transfers to the others
through the listed identity.

| Class | Common quantity | Routes | Identity joining them |
|---|---|---|---|
| C1 Overlap / aperture axis | positivity of the complete Weil family at overlap `K·c*_φ(N)`, equivalently Weil positivity at radius `½ log K` | HF, SRT, AIP, ACT, ACS-atomic; RW, EWU, OWU, MSC | `W_{φ,c,N}` PSD ⇔ `N < h(atom_{c/N})` [M]; `K ↔ ½ log K` [L]; visibility law [L] |
| C2 Glued state | `κ(φ_c) − 1` on the boost hyperplane | SC, AKG-gluing, RIT-Künneth | `κ(φ_c) = 1 + κ_boost`; boost mass `= √(log N)⟨x, v₁⟩` [M]; at `K·c*_φ` smooth-bump packets realize ratCorr Grams of a radius-`½ log K` test [D] — joins C1 |
| C3 Heat / collision integer | `N(t)/2`, `O(T)`, `ΔO` | WD-charge, SC-heat, LA-heat, TG, HEF | heat index = future collisions; bounded `N` ⇔ bounded `O`; horizon defect `≤ sup O` [L/M] — joins C1 |
| C4 Odd / Markov sector | odd-sector Doob energy `R ≤ ½` | CHMD, TT, AID, SAHT | Markov hyperplane = `v₁^⊥`; on atomic tests Weil form = Markov form [M] — joins C1 |
| C5 Rank / degree uniformity | all-rank Hankel, all-degree Jensen, PF signs | TH, HCF, PA, GTA, LA-Jensen | heated Hankel inertia counts off-line pairs at matched rank [M]; rank and degree play the role of aperture [D] |
| C6 Scheduled prime sums | lower bound of a prime-scheduled energy | FU, CFC, RP, SZ, LI, FEL, EGC | explicit-formula functionals bounded below ⇔ RH [M] |
| C7 Window precision | `ψ(x) − x`, `M(x)`, windowed prime error, Serre-dual `h⁰`, inter-tower coupling | WL, MC, PBM, RB, JAS, CTF, ACS-effectivity, SC-coupling | `Count(a)` iff `a − 1 ∈ 𝒬`; quadratic RR ⇔ Hodge index; coupling ≍ kernel = window error [L/M/D] |
| C8 Selection / typicality | the trivial gauge point among twins | MC-typicality, BAG, XN, PM-selection | RH ⇔ trivial point typical [M] |
| C9 Realization | spectral reality of a constructed operator | RN, PTR, W1C, PM-Mayer | Vitali: normal real-zero approximants force RH [M]; Mayer determinant `D = A + ζB` [L] |
| C10 Pre-divisor | a section or potential defined before the divisor | APF, BSH, CDC, DR, EWJ, HJ, IRK, PCS, RFHM, SEC, WBF | each needs a zero-independent forcing (Γ5) |
| C11 Conjugate diagonal | non-holomorphic depth functionals: Hecke defect, fibre multiplicity, same-point quantum, local counts | WD-Hecke, census, HEF, SRT-local count, IGP | `H(γ) ≤` prime polynomial `+ 4E_γ(L)`; `O ∈ 2ℕ`; counts + linear explicit formula insufficient [L/M] |
| C12 Hodge–Lefschetz / renormalization | HL of the Kähler package on the positive locus; star descent | HF-Hodge, ACS-Hodge, RIT renormalized index, EHT zero modes, TG paths | Liouville = HL; transport free; star isometry; scaling-surface effectivity [L/U] |

C1, C2, C3, C4 and C12 compute one sign on one hyperplane. C1 reads it along the aperture axis, C2
on the glued state, C3 along the heat parameter, C4 on the odd sector. C12 is the deformation form:
the sign is HR, and its content is HL on the positive locus. C5 and C6 are sign problems on test
families that become RH-complete only in the limit of rank, degree or schedule. In C5 rank and
degree play the role of aperture. C7 and C11 are the two precision faces: the one-point windowed
prime error, and the depth seen through the conjugation pairing. C8–C10 are the selection faces.

## U-Σ — positivity on the primitive part across the critical overlap

Core problem: the complete Weil form (primes, prime powers, both poles, Gamma) is nonnegative on
`v₁^⊥` at every multiple `K·c*_φ(N)` of a profile's critical overlap. Equivalent forms:
- Weil positivity at every aperture;
- hard Lefschetz on the positive locus of the overlap flow;
- no zero mode on `v₁^⊥` [L].

| Layer | Status | Anchor |
|---|---|---|
| Rough regime, tilted spline | all vectors `c ≤ (log N)^{1/16}`; complement `1/9`; confinement `log R' ≤ Cc¹¹`; packets `1/8` in progress | CACT [L/U] |
| Binding term of the rough regime | quadratic single-conductor residual against floor²: `c¹⁶/log N` | CACT [L] |
| Rough regime, smooth profiles | edge `→ ∞` for every profile without real Fourier zeros; no rate | EHT [L] |
| Critical overlap | Denjoy–Carleman and sinc: `c*_N ≍ L(log L)²` (margin = synthesis error = `1/log N`); tilted spline: receivers at `α > ¼` (second order), expected `1/8` (fourth order) | TM [L]; [D] |
| Aperture regime | `K·c*` sees radius `½ log K`; Weil floors through `181/500` and `A₊`; doubly exponential ceiling on the floor; visibility law (model) | TM, RW, ArithmeticCompensationTheory, ACS [L/M] |
| Effectivity | RH ⇔ effectivity with RR and ample axioms; base and pole-plane RR by Poisson; test classes missing | ArithmeticCastelnuovoSeveri, RIT, ArithmeticOrientationGeometry [L] |
| Kähler package | transport free; HL on the PSD locus is RH | HWV [L/U] |
| Stars | descent proved; deep stars positive; ascent open; coprime coupling outside every star | HWV [L]; [D] |
| Packet arithmetic | jump and affine incidence squares, exact Mertens diagonal, shell degree as the only growing term | ACPL [M] |
| High conductors | single modes coercive on `[(log N)^A, N^θ]`; spans and `m > √N` open | CAF [L] |
| Edge | crossing with zero mode; tilted window `[(log N)^{1/16}, 2(log N)^{¼+}]` under ¬RH | EHT [L]; [D] |

| Face | Routes / programmes | Reduction |
|---|---|---|
| Complete atomic matrix | HF, SRT, AIP, ACT, ACS-atomic, CACT, CAF, RAPT, SSH, SSHA, CSAR, ACPL, TM | positivity at every `K·c*_φ`; below `c*_φ` sub (rough regime) |
| Aperture ground minimum | RW, EWU, OWU, MSC, CFC | `μ(A) ≥ 0` ∀A |
| Edge / zero modes / Kähler package | EHT, HWV, RW | HL on the PSD locus |
| Stars / renormalization | HWV | ascent from stars to the top (no arithmetic mechanism known) |
| Effectivity / Riemann–Roch | ACS, RIT, HF | an effectivity of the scaling surface for cycles with a test component |
| Glued state | SC, AKG | `κ(φ_c) < 3` ⇔ positivity on `v₁^⊥` of the ratCorr Grams |
| Renormalized Hodge index | RIT | definiteness on the primitive part |
| Haar / Doob / odd sector | CHMD, AID, SAHT, TT | `R ≤ ½` on odd vectors; uniform coarse index |
| Rank / degree | TH, LA, HCF, PA, GTA | all-rank / all-degree sign |
| Scheduled prime sums | FU, CFC, RP, SZ, LI, FEL, EGC | lower bound on a prime-scheduled energy |
| Heat flow | WD, LA, HEF, SC-heat | no index jump on `(0, 1/8]` |
| Quantum / trace | TG, WD, AID | an integer `< 2` |
| Paths | TG, SC, EHT, ACPL, HWV | source-defined HL along a flow (transport itself is free) |
| Realization | RN, PTR, W1C, PM | spectral reality of a constructed operator |
| Künneth / powers | RIT, EHT | closed: RH-equivalent at every degree and every horizon |

## U-Π — precision of the prime statistics

Core problem: an unconditional square-root-precise statement about primes. It takes two forms:
- the one-point windowed error, which is the kernel, the coupling and the one-sided count;
- the conjugate-diagonal depth functional, which is the Hecke defect.

At the critical overlap the Σ problem meets Π: the margin equals the overlap residual, so only a
signed cancellation statement decides the sign (Π15).

| Face | Routes / programmes | Reduction |
|---|---|---|
| One-sided prime count | WL, PBM, RB, JAS, CTF, ACP, ASRP | `ψ(x) − x ≤ C√x log²x` (Π1) |
| Windowed kernel / coupling | SC, ACPL, AKG, HKT | bounded `K_ζ` ⇔ bounded coupling ⇔ window PNT at `√` precision (Π4) |
| Integer producers | WL, AKLT, AHA | `ε`-uniform producer (Π3) |
| Möbius cancellation | MC, BVI, CAF | moving-scale half-power cancellation; band localization retains `2Θ` (Π2, Π10) |
| Effectivity / sections | ACS, SPTL, AET, RIT | Serre-dual `h⁰` with quadratic RR (Π11) |
| Exceptional moduli | MC, CACT, CAF | individual control beyond `(log x)^A` (Π9 = Σ1d) |
| Conjugate diagonal | WD, CDG, RBG, HEF | mean `o(log U)` (sub); fixed scale (≥qRH); dyadic one constant (RH) (Π5) |
| Census / local counts | SRT, IGP, Zeta23, CDG, TTPC | 100% critical; pointwise local count; signed prime surplus `≤ N/18` (Π7) |
| Averages vs heights | WD, LA, SRT | density-zero exceptions invisible to means (Π6) |
| Critical-scale residual | HF, SRT, AIP, ACS, TM | signed cancellation of the overlap residual at `K·c*_φ` (Π15) |
| Subconvexity | LA, WD, AHA | heat floor `4μ(½)` (Π12) |
| Candidates | APF, EWJ, FEL, WBF, IRK | integral counts from a source lift |

Identities [L/M]:
- one-sided count ⇔ `κ = 0`;
- coupling rate = zero width;
- prime-error budget `≥ 2 + γ − log 4π`;
- Farkas duality between producers and Möbius log-harmonic measures;
- the prime polynomial is self-absorbed by the Hecke defect at log scale;
- counts + linear explicit formula cannot bound the Hecke defect;
- mean `o(log U)` ⇔ critical-scale clustering;
- quadratic RR ⇔ renormalized Hodge index.

## U-Γ — selection of ζ

Core problem: a source-defined mechanism that both distinguishes ζ from its twins and produces
positivity. The distinguishing half is closed for prime-set flips. The producing half is Frobenius
at infinity, which has four proved RH-equivalent readings.

| Face | Routes / programmes | Status / reduction |
|---|---|---|
| Typicality of the trivial point | MC, AGT, BAG, XN | RH ⇔ trivial point typical (Γ1) |
| Gluing of the global pole | SC, AKG, RIT | classified: only the extremal weight has one square; glue pole-blind (Σ11, Γ11) |
| Margin, index and edge selection | RIT, ACP, HKT, EHT, ACPL | every prime-set flip separated; Wirsing constants of flip twins positive (Γ2) |
| Counterterm selection | HWV | self-similar star flux ⇔ generalized von Mangoldt weight; only `ω ≡ 1` among twists (Γ18) |
| Gauge fixing | ALG, AES | entrywise-nonnegative gauges only on archimedean characters; twisted source sign forces `ω(p) = 1` (Γ12) |
| Local renormalization | AKG | counterterms make `Λ` and a twin both index `1` (Γ14) |
| Frobenius at infinity | PL, CDG, RBG, EHT, PM | defect involution; Hecke similitude; dyadic Hecke constant; partner saturation (Γ4) |
| Physical / native source | PM; PW-B retired | source-uniform extinction is a no-go; algebraic recentering of the critical parabola impossible (Γ13, Γ17) |
| Pre-divisor constructions | BSH, CDC, HJ, SEC, PCS, RFHM, DR, EWJ, APF, WBF | a section / potential defined before the divisor (Γ5) |
| Function-field calibration | ACS (`𝔽₃`), AKG (`𝔽_q(X)`), RIT, EHT, ACPL | local walls identical; ℤ differs by unbounded edge and incommensurable towers (Γ10) |
| Selection → sign | all selectors | no selector produces complete-form positivity (Γ16) |

## 2. Cross-family seams

| Seam | Statement | Routes on the seam |
|---|---|---|
| Σ: one hyperplane | glued index, complete-Weil sign, Markov criterion, renormalized Hodge index and HR of the Kähler package are positivity on `v₁^⊥` | SC, HF, SRT, AIP, ACS, CHMD, RIT, HWV |
| Σ: overlap = aperture | the complete family at `K·c*_φ` sees radius `½ log K`; the edge of a fixed off-line pair sits at `≲ C e^{2a(ρ)} c*_φ`, `a(ρ)` its visibility aperture | HF, SRT, AIP, RW, EHT, TM [L/D] |
| Σ: rough versus aperture | no corpus receiver turns positivity below the receiver threshold into a statement about zeros; the tilted-spline exponents `1/16, 1/11, 1/9, 1/8` belong to the profile | CACT, SSH, ACPL, TM [L/D] |
| Σ: zero modes | a finite edge is a zero mode of a PSD form; successor + dyadic rigidity confines incidence kernels to constants; Liouville = HL | EHT, CSAR, ACPL, HWV |
| Σ ∩ Π: aperture floor | the restricted Weil floor dies doubly exponentially in the aperture; in the RVM model positivity at aperture `a` excludes isolated pairs below `2π exp(2π S_δ(a))` | RW, ACS, ArithmeticCompensationTheory [L]; model [D] |
| Σ ∩ Π ∩ Γ: effectivity | an effectivity of the scaling surface would give sign (Hodge index), precision (Castelnuovo–Severi) and selection (graph classes) at once, as over `𝔽_q` | ACS, RIT, HF, SC [L/D] |
| Σ ∩ Π: unattained width | cone, tower and escape receivers leave the case "`Θ` not attained"; attainment implies `Θ < 1` | ACPL, AKLT, PM [L/M/D] |
| Σ ∩ Π: quantization | RH = an even integer `< 2`; integer-theta readings are exact but stabilize at prefixes tied to divisor separation | WD, TG, SC, HKT [L] |
| Σ ∩ Π: critical-scale residual | at `c*_φ` the margin equals the overlap residual; the sign needs signed cancellation | HF, SRT, AIP, TM, CSAR [D] |
| Σ ∩ Π: kernel = coupling = window error | bounded kernel, bounded coupling, no edge, window PNT at `√` precision are one statement | SC, ACPL, EHT, WL, HKT |
| Σ ∩ Π: conductor levels | residual control uses the Siegel–Walfisz range; single modes to `N^θ`, `θ < ½`; above `√N` needs Elliott–Halberstam type | CACT, CAF, MC |
| Σ ∩ Π ∩ C11: collisions | `H(γ)` bounded by prime polynomial + Hecke defect; `ΔO ≤ 2·max H·n_off`; bounded `ΔO` ⇒ density one | WD, CDG, SRT, census |
| Π: averages vs heights | means and density statements cannot exclude density-zero clusters; the Hecke-defect hierarchy separates mean, clustering, corridor and all scales | WD, LA, SRT, census |
| Σ ∩ Γ: gluing | the archimedean place supplies the one square; the glue is pole-blind | AKG, SC, RIT |
| Σ ∩ Γ: Frobenius at infinity | reflection pairing (Weil form) vs conjugation pairing (collided form, resonant partner states); their identity is RH | EHT, PL, CDG, HF, PM |
| Σ ∩ Γ: counterterm self-similarity | stars carry the same form for every weight; only the counterterm selects, through `Λ ∗ 1 = log` | HWV, HF, SC |
| Γ: selection without sign | every selector is a margin, index or counterterm identity on a partial form | RIT, ACP, ACPL, ALG, AES, EHT, HWV |
| Σ: paths | crossing-free deformation ⇔ positivity; Kähler transport free; content = HL | TG, SC, WD, EHT, ACPL, HWV |
| Archimedean channel | the archimedean place glues `+` and `×`; coprime atoms are coupled only through it (Gamma, poles, successor shells) | AKG, ALG, CHMD, RIT, ACPL, HWV [D] |

## 3. Route → core map

| Route | Core | Class | Face |
|---|---|---|---|
| WL | Π | C7 | one-sided count, producers |
| RW, EWU, OWU | Σ (Γ) | C1 | the aperture axis itself; selectivity |
| FU, CFC, RP, SZ, LI | Σ | C6 | scheduled prime sums |
| PA, TH, LA, HCF, GTA | Σ | C5 | rank / degree sign |
| MC | Π (Γ) | C7, C8 | Möbius cancellation; band localization; typicality |
| TT | Σ | C4 | odd / directed covariance |
| TG | Σ | C3, C12 | quantum; source-defined HL along paths |
| HF | Σ (Π, Γ) | C1, C12 | complete family at the critical overlap; Kähler package; stars; Frobenius at infinity |
| SRT, AIP, ACT | Σ (Π) | C1 | complete atomic matrix; edge; zero modes |
| SC | Σ, Π (Γ) | C2, C7, C3 | glued state; coupling = window error; heat homotopy |
| CHMD | Σ | C4, C1 | Haar / Doob / odd sector |
| RN | Σ | C9 | realization |
| WD | Σ, Π | C3, C11 | collision charge; Hecke-defect hierarchy |
| PM | Γ (Σ) | C8, C9 | Mayer determinant; resonant states; partner saturation |
| JAS, CTF, PBM, RB | Π | C7 | one-sided count |
| XN, BAG | Γ | C8 | typicality / recurrence |
| ACS | Π (Σ, Γ) | C7, C1, C12 | effectivity / quadratic RR; atomic; curve calibration |
| APF, EWJ, WBF, IRK | Γ (Π) | C10 | source lift with integral count |
| BSH, CDC, HJ, SEC, PCS, RFHM, DR | Γ | C10 | pre-divisor constructions |
| EGC, FEL, MSC | Σ | C6, C1 | contour / likelihood / Sonin |
| PTR, W1C | Σ | C9 | realization |
| PW-B (retired) | Γ | — | source-uniform extinction refuted |

## 4. What a closing argument must supply

Over `𝔽_q` one object, the Frobenius graph on `C × C`, supplies all three readings. The Hodge index
gives the sign, Riemann–Roch gives the count, and the graph is canonical. A curve's edge is
`≤ 2g`: a bounded aperture decides. Its prime towers are commensurable, and Frobenius is conformal
with factor `q`. Over ℤ the corpus has each ingredient separately:

| Needed | Present over ℤ | Missing |
|---|---|---|
| Positivity by identity | packet identity (jump + affine incidence squares + bounded diagonal); local pole–successor forms; archimedean form on `ℓ = 0` = dilation form + shell squares; matched prime form with one positive direction on every finite sieve; star isometry | an identity for the shell degree jointly with the pole; an SOS identity for the dilation form on one two-prime lattice |
| Positivity uniform in aperture | rough regime to the profile's critical overlap (tilted spline `1/16`); Weil floors through radius `181/500`; receivers at every `K·c*` | a mechanism whose constants do not grow with the aperture; the floor must die doubly exponentially [L], so estimates cannot supply it |
| Nondegeneracy (HL) | Kähler-package transport; Liouville = HL; star descent; deep stars positive | HL on the positive locus; ascent from stars to the top |
| Precision | one-sided count ⇔ RH; kernel = coupling = window error; producers to the main term; prime polynomial self-absorbed; Hecke-defect means `O(log U)` | square-root input for one-point windows; arithmetic access to the conjugate diagonal |
| Count from geometry | theta `h⁰` with RR on `Spec ℤ` and on the pole plane; scaling surface with RH ⇔ effectivity; quadratic RR ⇔ Hodge index; arithmetic Bézout | an effectivity (`h⁰`) for cycles with a test component, whose Euler characteristic contains the prime comb without breaking the Riemann inequality |
| Canonical selector | every prime-set flip separated; coupling diagonal; gauge fixing; self-similar counterterm | Frobenius at infinity as an operator (a conformal correspondence of factor `≠ 1`, or a Hecke similitude of the collided form, or partner saturation of resonant states) |
| Integrality with homotopy invariance | collision charge as Fredholm index; heat index as Pontryagin homotopy; index constant on nondegenerate paths | a source-defined noncrossing mechanism along the overlap or heat flow |
