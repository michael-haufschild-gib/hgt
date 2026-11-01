# Route unification ledger — status quo

The 33 live routes and 16 candidates are faces of three core problems. The three core problems are
three readings of one even integer, `κ = κ(K_ζ)`: the negative index of Weil's correlation on the
dilations of `ℚ`, read on the pole-orthogonal hyperplane `v₁^⊥`. Gluing at any place turns it into
the index `κ(φ_c) = κ + 1` of one affine state. EHT makes it a resolution invariant: RH ⇔ the
complete Weil family has no edge, and a finite edge is a zero mode. ACPL makes it a coupling
invariant: RH ⇔ the inter-tower coupling is bounded, and the coupling is as large as the kernel.
Evidence tags as in `walls-ledger.md`.

## 0. The one object

| Reading | Statement | Anchor |
|---|---|---|
| Index | `κ(K_ζ) = #{ρ : Re ρ > ½}` (distinct), even, carried by one two-prime lattice | HKT, AKLT [M] |
| Bounded kernel | RH ⇔ `‖K_ζ(u)‖ ≤ Re K_ζ(1)` ∀u (Castelnuovo–Severi at rational scales) | RIT `riemannHypothesis_iff_castelnuovoSeveri` [L] |
| Coupling | RH ⇔ bounded `K(uv) − K(u) − K(v) + K(1)` on one `⟨p⟩×⟨q⟩`; rate = zero width; coupling ≍ kernel; `κ(L_aL_bK_ζ) = κ` | ACPL [L] |
| Window prime error | `K_ζ(u)` = smoothed prime error in a fixed-length multiplicative window at `u`, normalized by `√u` | HKT spline-kernel identity [M]; reading [D] |
| Glued state | `κ(φ_c) = κ + 1` at `∞` and every prime; translation reading `1` | AKG [L/M] |
| Hyperplane | boost = `v₁^⊥` = Markov = harmonic; `v₁` = ground state | RIT [M] |
| Hodge index | RH ⇔ renormalized Hodge index ⇔ quadratic RR on the scaling surface | RIT [M] |
| Edge | RH ⇔ `e_φ ≡ ∞`; `W_{φ,c,N}` PSD ⇔ `N < h(atom_{c/N})`; finite edge = PSD with a zero mode; no edge ⇔ bounded coupling | EHT, ACPL [L] |
| Packet identity | complete form on packets = `J_N + ½A_N` + bounded diagonal − shell degree + boundary terms; Mertens and Euler constants cancel | ACPL [L] |
| Heat | `κ(φ_c^{(t)}) − 1 = N(t)/2` = future collision pairs | AKG, RIT [M] |
| Quantum | collision charge = Fredholm index; `κ ≤ sup O`; RH ⇔ `O < 2` per window | CDG [M]; EHT [L] |
| Hecke defect | RH ⇔ one constant bounds the dyadic Hecke defects; fixed scale ⇔ corridor | CDG [L] |
| Frobenius at infinity | `σ(ρ) = 1 − ρ̄`; RH ⇔ `σ` trivial on the zeros ⇔ Hecke similitude of the collided form; `κ = #` moved zeros | EHT [L] |
| Künneth | `κ(K_ζ⊠K_ζ) ∈ {0, ∞}`; no softening at any horizon | RIT [M]; EHT [L] |
| Selection | glued test index `κ + 1` for `Λ`, `∞` for finite flips; every prime-set flip separated by an atomic margin | AKG [M]; RIT [L] |

The three walls are the three ways a reading of `κ` fails. The sign of the complete form is not
determined by estimates across the edge (Σ). The prime statistics are not precise enough: windowed
one-point errors, and the conjugate-diagonal depth functional (Π). Selection of ζ does not produce
positivity (Γ).

## 1. Equivalence classes of routes

Routes in one class compute the same quantity; a theorem in one class transfers to the others
through the listed identity.

| Class | Common quantity | Routes | Identity joining them |
|---|---|---|---|
| C1 Threshold curve | detection horizon `h(w)` of the width-`w` atom, read along `w = c/N` (complete Weil matrix), fixed `w` (fixed test), fixed support (aperture) | HF, SRT, AIP, ACS-atomic, ACT; RW, EWU, OWU, MSC; SC-index | `W_{φ,c,N}` PSD ⇔ `N < h(atom_{c/N})`; `sup_N d_f(N)` = seen zeros; isolated-pair aperture law `S_δ(a) > L` [L] |
| C2 Glued state | `κ(φ_c) − 1` on the boost hyperplane | SC, AKG-gluing, RIT-Künneth | `κ(φ_c) = 1 + κ_boost`; boost mass `= √(log N)⟨x, v₁⟩` on integer slopes [M] — joins C1 |
| C3 Heat / collision integer | `N(t)/2`, `O(T)`, `ΔO` | WD-charge, SC-heat, LA-local heat, TG, HEF | heat index = future collisions; bounded `N` ⇔ bounded `O`; every horizon defect `≤ sup O` [L/M] — joins C1 |
| C4 Odd / Markov sector | odd-sector Doob energy `R ≤ ½` | CHMD, TT, AID, SAHT | Markov hyperplane = `v₁^⊥`; on atomic tests Weil form = Markov form [M] — joins C1 |
| C5 Rank / degree uniformity | all-rank Hankel, all-degree Jensen, PF signs | TH, HCF, PA, GTA, LA-Jensen | heated Hankel inertia counts off-line pairs at matched rank [M] |
| C6 Scheduled prime sums | lower bound of a prime-scheduled energy | FU, CFC, RP, SZ, LI, FEL, EGC | explicit-formula functionals bounded below ⇔ RH [M] |
| C7 Window precision | `ψ(x) − x`, `M(x)`, windowed prime error, Serre-dual `h⁰`, inter-tower coupling | WL, MC, PBM, RB, JAS, CTF, ACS-effectivity, SC-coupling | `Count(a)` iff `a − 1 ∈ 𝒬`; quadratic RR ⇔ Hodge index; coupling ≍ kernel = window error [L/M/D] |
| C8 Selection / typicality | the trivial gauge point among twins | MC-typicality, BAG, XN, PM | RH ⇔ trivial point typical [M] |
| C9 Realization | spectral reality of a constructed operator | RN, PTR, W1C, PM | Vitali: normal real-zero approximants force RH [M] |
| C10 Pre-divisor | a section or potential defined before the divisor | APF, BSH, CDC, DR, EWJ, HJ, IRK, PCS, RFHM, SEC, WBF | each needs a zero-independent forcing (Γ5) |
| C11 Conjugate diagonal | non-holomorphic depth functionals of the divisor: Hecke defect, fibre multiplicity, same-point quantum, local counts | WD-Hecke, census, HEF, SRT-local count, IGP | `H(γ) ≤` prime polynomial + `4E_γ(L)`; same-point quantum `O ∈ 2ℕ`; explicit formula + counts insufficient [L] |

C1, C2, C3 and C4 compute one sign on one hyperplane, read along different sections of the
threshold curve or along the heat parameter. C5 and C6 are sign problems on test families that
become RH-complete only in the limit of rank or schedule. C7 and C11 are the two precision faces:
C7 the one-point windowed prime error, C11 the depth seen through the conjugation pairing. C8–C10
are the selection faces.

## U-Σ — positivity on the pole-orthogonal hyperplane across the detection edge

Core problem: the complete Weil form (primes, prime powers, both poles, Gamma) is nonnegative on
`v₁^⊥` along an RH-complete schedule. Equivalently, the overlap flow `c ↦ W_{c,N}` has no zero mode
on `v₁^⊥` [D from L].

| Layer | Status | Anchor |
|---|---|---|
| Universal regime (no zero information) | tilted spline, all vectors, `c ≤ (log N)^{1/19}` | CACT [L] |
| Residual ceiling `19` | residual `c⁵/log N` against floor² `c⁻¹⁴`; binding for the norm-quasimode method | CACT [L] |
| Confinement ceiling `16` | `D_N ≤ Cc¹⁶` for nonpositive vectors; sector `exp(c¹⁶/η)`; intrinsic to separate shell payment | ACPL, SSH [L] |
| Synthesis threshold `4` | positivity at `c⁴/log N → ∞` is RH (every `C²` profile) | EHT [L] |
| RH regime | tilted full `α > ¼`, hyperplane `α > ½`; `C^∞` hyperplane every `α > 0`; sinc at `τ(c) log N ≈ 1` | RAPT, RIT, TM [L/M] |
| Packet arithmetic | jump and affine incidence squares, exact Mertens diagonal, shell degree as the only growing term | ACPL [L] |
| Shells | separate payment `c²/ε` sharp; joint top-band `O(G(c + log N))` | SSH [L] |
| High conductors | single modes coercive on `[(log N)^A, N^θ]`; spans and `m > √N` open | CAF [L]; Σ1g, Σ1h |
| Edge | crossing with zero mode; window `[(log N)^{1/19}, 2(log N)^{¼+}]` under ¬RH | EHT [L]; [D] |

| Face | Routes / programmes | Reduction |
|---|---|---|
| Complete atomic matrix | HF, SRT, AIP, ACT, ACS-atomic, CACT, CAF, RAPT, SSH, SSHA, CSAR, ACPL | positivity on `v₁^⊥` at the RH-complete rate of a matched profile |
| Edge / zero modes | EHT, ACPL interfaces, RW | no zero mode along the overlap flow |
| Glued state | SC, AKG | `κ(φ_c) < 3` ⇔ positivity on `v₁^⊥` of the ratCorr Grams |
| Renormalized Hodge index | RIT | definiteness on the primitive part `v₁^⊥` |
| Aperture ground minimum | RW, EWU, OWU, MSC, CFC | `μ(A) ≥ 0` ∀A |
| Haar / Doob / odd sector | CHMD, AID, SAHT, TT | `R ≤ ½` on odd vectors; uniform coarse index |
| Rank / degree | TH, LA, HCF, PA, GTA | all-rank / all-degree sign |
| Scheduled prime sums | FU, CFC, RP, SZ, LI, FEL, EGC | lower bound on a prime-scheduled energy |
| Heat flow | WD, LA, HEF, SC-heat | no index jump on `(0, 1/8]` |
| Quantum / trace | TG, WD, AID | an integer `< 2` |
| Paths | TG, SC, EHT, ACPL | a source-defined noncrossing path (finite level: equivalent to the sign) |
| Realization | RN, PTR, W1C, PM | spectral reality of a constructed operator |
| Künneth / powers | RIT, EHT | closed: RH-equivalent at every degree and every horizon |

## U-Π — precision of the prime statistics

Core problem: an unconditional square-root-precise statement about primes. It takes two forms:
the one-point windowed error, which is the kernel, the coupling and the one-sided count; and the
conjugate-diagonal depth functional, which is the Hecke defect.

| Face | Routes / programmes | Reduction |
|---|---|---|
| One-sided prime count | WL, PBM, RB, JAS, CTF, ACP, ASRP | `ψ(x) − x ≤ C√x log²x` (Π1) |
| Windowed kernel / coupling | SC, ACPL, AKG, HKT | bounded `K_ζ` ⇔ bounded coupling ⇔ window PNT at `√` precision (Π14) |
| Integer producers | WL, AKLT, AHA | `ε`-uniform producer (Π3) |
| Möbius cancellation | MC, BVI, CAF | moving-scale half-power cancellation; band localization retains `2Θ` (Π2, Π16) |
| Effectivity / sections | ACS, SPTL, AET, RIT | Serre-dual `h⁰` with quadratic RR (Π11) |
| Exceptional moduli | MC, CACT, CAF | individual control beyond `(log x)^A` (Π9 = Σ1g) |
| Conjugate diagonal | WD, CDG, RBG, HEF, census | Hecke defect at all dyadic scales with one constant (Π15) |
| Census / local counts | SRT, IGP, Zeta23, CDG | 100% critical; pointwise local count (Π8, Π12) |
| Collision readings | WD, CDG | detection scale = zero gap (Π13) |
| Candidates | APF, EWJ, FEL, WBF, IRK | integral counts from a source lift |

Identities [L/M]: one-sided count ⇔ `κ = 0`; coupling rate = zero width; prime-error budget
`≥ 2 + γ − log 4π`; Farkas duality between producers and Möbius log-harmonic measures; prime
polynomial self-absorbed by the Hecke defect at log scale; counts + linear explicit formula cannot
bound the Hecke defect; quadratic RR ⇔ renormalized Hodge index.

## U-Γ — selection of ζ

Core problem: a source-defined mechanism that both distinguishes ζ from its twins and produces
positivity. The distinguishing half is closed for prime-set flips. The producing half is Frobenius
at infinity.

| Face | Routes / programmes | Status / reduction |
|---|---|---|
| Typicality of the trivial point | MC, AGT, BAG, XN | RH ⇔ trivial point typical (Γ1) |
| Gluing of the global pole | SC, AKG, RIT | classified: only the extremal weight has one square; glue pole-blind (Σ11, Γ11) |
| Margin, index and edge selection | RIT, ACP, HKT, EHT, ACPL | every prime-set flip separated; diagonal coupling recovers flip sets; single-flip edges bounded (Γ2) |
| Gauge fixing | ALG, AES | entrywise-nonnegative gauges only on archimedean characters; twisted source sign forces `ω(p) = 1` (Γ12) |
| Local renormalization | AKG | counterterms make `Λ` and a twin both index `1` (Γ14) |
| Polarization / Frobenius at infinity | PL, CDG, RBG, EHT | Hecke similitude of the collided form ⇔ RH (Γ4) |
| Physical / native source | PM; PW-B retired | source-uniform extinction is a no-go; half-parameter cusp selection is RH (Γ13) |
| Pre-divisor constructions | BSH, CDC, HJ, SEC, PCS, RFHM, DR, EWJ, APF, WBF | a section / potential defined before the divisor (Γ5) |
| Function-field calibration | ACS (`𝔽₃`), AKG (`𝔽_q(X)`), RIT, EHT, ACPL | local walls identical; ℤ differs by unbounded edge and incommensurable towers (Γ10) |
| Selection → sign | all selectors | no selector produces complete-form positivity (Γ16) |

## 2. Cross-family seams

| Seam | Statement | Routes on the seam |
|---|---|---|
| Σ: one hyperplane | SC's index problem, the complete-Weil sign problem, the Markov criterion and the renormalized Hodge index are positivity on `v₁^⊥` | SC, HF, SRT, AIP, ACS-atomic, CHMD, RIT |
| Σ: one threshold curve | complete Weil matrix, fixed-test horizon index and aperture minimum are sections of `h(w)` | HF, SRT, AIP, RW, SC, EHT |
| Σ: three exponents | `1/19` residual ceiling, `1/16` confinement ceiling, `¼` synthesis threshold | CACT, SSH, ACPL, EHT |
| Σ: zero modes | a finite edge is a zero mode of a PSD form; successor + dyadic rigidity confines incidence kernels to constants | EHT, CSAR, ACPL |
| Σ ∩ Π: kernel = coupling = window error | bounded kernel, bounded coupling, no edge, window PNT at `√` precision are one statement | SC, ACPL, EHT, WL, HKT |
| Σ ∩ Π: conductor levels | residual control uses Siegel–Walfisz range; single modes to `N^θ`, `θ < ½`; above `√N` needs Elliott–Halberstam type | CACT, CAF, MC |
| Σ ∩ Π: coherent prime sector | jumps are incidence events; pole cost `log Q` sharp; Mertens and Euler constants cancel exactly | CSAR, ACPL, RAPT |
| Σ ∩ Π ∩ C11: collisions | `H(γ)` bounded by prime polynomial + Hecke defect; `ΔO ≤ 2·max H·n_off`; bounded `ΔO` ⇒ density one | WD, CDG, SRT, census |
| Π: conjugate diagonal | Hecke defect is non-holomorphic in `ρ`; linear explicit formula + counts insufficient; dyadic-uniform bound ⇔ RH | WD, CDG, HEF, census |
| Σ ∩ Γ: gluing | the archimedean place supplies the one square; the glue is pole-blind | AKG, SC, RIT |
| Σ ∩ Γ: Frobenius at infinity | reflection pairing (Weil form) vs conjugation pairing (collided form); their identity is RH | EHT, PL, CDG, HF |
| Γ: selection without sign | every selector is a margin or index on a partial form | RIT, ACP, ACPL, ALG, AES, EHT |
| Σ: paths | crossing-free deformation ⇔ positivity; axial→coupled homotopy degenerate at `t = 0` | TG, SC, WD, EHT, ACPL |
| Archimedean channel | the archimedean place glues `+` and `×`; two-prime exponents dense; curves commensurable, ℤ incommensurable | AKG, ALG, CHMD, RIT, ACPL |

## 3. Route → core problem map

| Route | Core | Class | Face |
|---|---|---|---|
| WL | Π | C7 | one-sided count, producers |
| RW, EWU, OWU | Σ (Γ) | C1 | aperture section of the threshold curve; selectivity |
| FU, CFC, RP, SZ, LI | Σ | C6 | scheduled prime sums |
| PA, TH, LA, HCF, GTA | Σ | C5 | rank / degree sign |
| MC | Π (Γ) | C7, C8 | Möbius cancellation; band localization; typicality |
| TT | Σ | C4 | odd / directed covariance |
| TG | Σ | C3 | quantum; noncrossing paths |
| HF, SRT, AIP, ACT | Σ (Π) | C1 | complete atomic matrix; edge; zero modes |
| SC | Σ, Π (Γ) | C2, C7, C3 | glued state; coupling = window error; heat homotopy |
| CHMD | Σ | C4, C1 | Haar / Doob / odd sector |
| RN | Σ | C9 | realization |
| WD | Σ, Π | C3, C11 | collision charge; conjugate-diagonal Hecke defect |
| PM | Γ (Σ) | C8, C9 | native source; Gauss–Mayer determinant |
| JAS, CTF, PBM, RB | Π | C7 | one-sided count |
| XN, BAG | Γ | C8 | typicality / recurrence |
| ACS | Π (Σ, Γ) | C7, C1 | effectivity / quadratic RR; atomic; curve calibration |
| APF, EWJ, WBF, IRK | Γ (Π) | C10 | source lift with integral count |
| BSH, CDC, HJ, SEC, PCS, RFHM, DR | Γ | C10 | pre-divisor constructions |
| EGC, FEL, MSC | Σ | C6, C1 | contour / likelihood / Sonin |
| PTR, W1C | Σ | C9 | realization |
| PW-B (retired) | Γ | — | source-uniform extinction refuted |

## 4. What a closing argument must supply

Over `𝔽_q` one object, the Frobenius graph on `C × C`, supplies all three readings. The Hodge index
gives the sign, Riemann–Roch gives the count, and the graph is canonical. A curve's edge is
`≤ 2g`, and its prime towers are commensurable. Over ℤ the corpus has each ingredient separately:

| Needed | Present over ℤ | Missing |
|---|---|---|
| Positivity by identity | packet identity: jump squares + affine incidence squares + bounded diagonal; local pole–successor forms = hyperbolic pair + shell squares; archimedean form on `ℓ = 0` = dilation form + shell squares; matched prime form has one positive direction on every finite sieve | an identity for the shell degree jointly with the pole; an identity for Weil's dilation form on one two-prime lattice |
| Positivity across the edge | universal regime to `(log N)^{1/19}`; edge = zero mode; conductor averages at RH-complete overlap; single modes coercive above polylog | a mechanism that is not an estimate; nondegeneracy of the overlap flow on `v₁^⊥` |
| Precision | one-sided count ⇔ RH; kernel = coupling = window error; producers to the main term; prime polynomial self-absorbed | square-root input for one-point windows; arithmetic access to the conjugate diagonal |
| Count from geometry | linear theta RR; arithmetic Bézout; quadratic RR ⇔ Hodge index | an unconditional Serre-dual `h⁰` |
| Canonical selector | every prime-set flip separated; coupling diagonal; gauge fixing; twisted source sign | Frobenius at infinity; a selector that is also a positivity producer |
| Integrality with homotopy invariance | collision charge as Fredholm index; heat index as Pontryagin homotopy; index constant on nondegenerate paths | a source-defined noncrossing mechanism along the overlap or heat flow |
