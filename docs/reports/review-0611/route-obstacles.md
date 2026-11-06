# Route obstacles — status quo

Scope: 38 live route formulations, 9 candidates and their supporting programmes. For each: path, what is established, obstacles that are **(a) just work**, obstacles that are **(b) open mathematics nobody has a solution to**.

Corpus checkpoint: commit `8c88f0f9a6` plus the working tree of 2026-11-06.

**Live** means source observable, proved RH-sufficient receiver and explicit open estimate. **Candidate** means an independent source mechanism or landing is missing. Formulations are not independent mechanisms: HJ is PA, BSH is CDC, FEL's BSY criterion belongs to CTF. A criterion, a source construction, a quotient equality or a scalar grade does not discharge an arithmetic sign or vanishing.

**Evidence.** `[L]` Lean source. `[S]` Lean source still unfinished or uncommitted. `[D]` mathematical deduction, not a Lean theorem. `[N]` numerical, uncertified. `[C]` classical literature, not formalized.

**Strength.** RH; ≥qRH (zero-free half-plane or Lindelöf); sub (strictly below quasi-RH); method; indep. (independent of RH).

**Labels.** `A*` just-work items and `B*` open problems are listed in full in [obstacles-summary.md](obstacles-summary.md). An A item is known mathematics, finite computation, effectivization or assembly of proved pieces; `(unverified)` marks A items whose difficulty is not established.

**Notation.** Windows `[−a,a]`. `W` Weil's form, `w_n=Λ(n)n^{−1/2}`, `H` the archimedean–polar form, `P` the arithmetic part, `W=H−P`. `μ(a)` ground energy. `a*(ζ)` onset aperture. `ℋ(c)` Hardy interval, `𝒜(c)` window cone, `λ*(c)` its best margin. `K_a(z,z)` Weil reproducing kernel. `τ_L,τ_R` endpoint traces. `r(a)=τ_R(i)/τ_L(i)` anchor reflection, `m(a)=(1+r²)/(1−r²)`. `q(a)=Ψ′(a)` where `H₁=e^{2Ψ}`, `H₂=e^{−2Ψ}` is the canonical Hamiltonian. `L=log T`, `L_T=½log(T/2π)`. `H_t` the de Bruijn–Newman flow, `Λ_X` its local constant, `τ=t log²X` normalized heat time. `N_d` non-real root count of `R_d(Ξ)`. `w=zetaZeroWidth`, `Θ=½+w`. `M_X` truncated Möbius polynomial, `E_X=ζM_X−1`. `ϱ(ρ,ρ′)=|ρ−ρ′|/|ρ+ρ̄′−1|` pseudo-hyperbolic ratio on `Re s>½`. `vkScale(T)=(log T)^{3/5}(log log T)^{−5/3}`.

## 0. The picture

| Fact | Evidence | Consequence |
|---|---|---|
| RH ⇔ `a*(ζ)=⊤` ⇔ `1∈ℋ(c)` ∀c ⇔ `λ*(c)→0` ⇔ two-site PD ⇔ no finite contact | [L] | every window route measures one number |
| Canonical system to contact: `H₁H₂=1`, every Gram is the integral of its endpoint-trace energy from aperture 0, no initial atom | [L] | the chain has no singular part before contact |
| `(log K(i,i))′=2m=2(1+r²)/(1−r²)` and `r′=(1−r²)q−2r` | [D from L] | contact is a blow-up of one scalar flow |
| Every proved upper bound on the chain divides by `μ` (`groundEnergy_mul_evalGram_le_aperture`) | [L] | the gap between chain and contact is a `1/μ` factor |
| `windowPositiveAt_of_rhVerifiedThrough` with explicit height, plus Li, Hausdorff, heat-grid, Jensen, PF, theta rungs | [L] | each finite rung is verification. Lean's own verified height is `H²<431/2` |
| Floor tower: `a_k−a₀<10^(−7800000)`, `a_k<0.3621` | [L] | that tower produces no aperture |
| Every route with a saving has the same Vinogradov–Korobov saving and stops there: AIP cost, SZ source, TT band, MC Hilbert form, PTR depth, TH collar, WL energy | [L] | one width axis; interior values are zero-free strips |
| Density-one heights: `Λ_X log X→0`; central gaps at every `κ≤t log(x/2π)≤1`; at critical scale, gaps `≥c·min(t,log⁻²)` and all zeros real for `τ≳κ(δ)` outside `δT` heights | [L/S] | ZCG's crystal exists on almost all heights down to bounded `τ` |
| Central inequality at all heights ⇒ RH and uniformly bounded multiplicity | [L] | it is strictly stronger than RH |
| `Φe^{−τx²}` has the same Fock, frequency and doubling laws and non-real zeros below `τ` | [L] | parabolic structure cannot select time 0 |
| Hyperbolic density: depth `∈[α/L,(α+1)/L]`, `Πϱ≥B₀≥e^{−x/8}` over zeros deeper than `x/2L`, gives `≪(α+1)TLe^{−2x}/B₀²` | [L/S] | Density Hypothesis rate for all but clustered deep zeros |
| `N(ρ)≤Πϱ`, where `N(ρ)` is the normalized derivative at a zero | [S] | negative moments of `ζ′` at zeros are the remaining input |
| Barrier events cannot decide occupancy: one Euler factor puts a depth `A/L` zero in every unit window, prime walk moved by `≤8` | [L] | `D_win` needs a zero-specific input |
| Last scale: any normalized mollifier of length `V^θ`, `θ<½`, has shifted defect `≥c(e^{−2θa}/a)V`; short Dirichlet weights do not lower it | [L] | polynomial detectors stop at depth `≍log log V/θ` |
| Long-moment slope is exactly `2wθ`; cofinal bound at any fixed `K` self-improves to `K=6`; `RH⇔∫₀¹|ζM_X|²≪X^{2ε}` | [L] | WD's RH branch lives in one bounded window |
| TH spectrum: `S(a,b)=Σ_Nτ_b(N)A(N;a,b)`, `τ_b(p^k)=U_k(cos(b log p))` | [D from L] | theta positivity is Eisenstein-coefficient positivity |
| Positive at actual phases; negative at some torus point once primes `≲19–47` are free | [N] | TH needs actual phase locking |
| PM: `ζ(2s)≠0` on `Re 2s=1` from the Mayer carrier by Maass–Selberg; resonant `D_s≤0` | [L] | PM carries edge information; positivity off the unitary axis stays open |

## 1. Mechanism classes

| Class | Mechanism | Status |
|---|---|---|
| M1 Signed criticality | Primes pay the archimedean–polar deficit by sign in a frustrated critical form | format exact on every window; frustration unswitchable; size payment ends before half-width `21/40` |
| M2 Calibration | Window cones, blind positivity, margin | cone pinned at rate `e^{−c/1104}`; margin ceiling doubly exponential; sign open |
| M3 Canonical flow | `r,q` of the Weil chain | exact to contact; contact-uniform control open |
| M4 Reflection | Krein/Lewis positivity, Eisenstein carrier | coefficient completion closed; `D_s≥0` open |
| M5 Square-root cancellation | One smoothed prime count, long moments | receivers closed; arithmetic estimates open |
| M6 Continuation | Heat, cosine, Jensen | high-time and typical-height regions closed; small time at all heights open |
| M7 Zero geometry | Cameras, Blaschke factors, Carleson separation | isolated zeros at rate 2; clusters open |
| Amplifiers | Diophantine repulsion, integrality | amplify a certificate, produce none |

## 2. Shared obstacle blocks

### S1. Complete Weil family at the critical curve

Routes: HF, SRT, AIP, ACT, ACS (atomic), SC, CHMD (index). Programmes: CACT, AHD, CSAR, ACPL, ADT, RAPT, TM, SSHA, CAF.

Established [L]:
- Full tilted-spline matrix PD for `1≤c≤(log N)^α`, `α<1/8`, and through one small multiple `c≤2K₀(log N)^{1/8}`.
- Every fixed critical ratio `R=c⁸/log N`: critical pencil `κQ+(7J/R)∫e^{−8y}H²`, exact aliasing limit, fixed-family eventual inertia, positive low packet through `⌊(log N)^{13/32}⌋`, polar capacity `S_A²/(J₁/R+κg)`.
- Weighted floor `Q(H)≥−F(p)∫e^{−pu}H²`, `p>1`, `F(p)` explicit, independent of aperture.
- Atomic synthesis: adjoint error `O(c/N)`, mixed mass and high-Fourier dual floors along strong physical `L¹` limits; prime shifts infinitesimal in the terminal weight, bounded weighted collar mass and exponential control of physical `L¹` tails [S]; receiving modes with bounded charge, vanishing physical energy, capacity `log log N+O(1)`.
- Dirichlet-shift companions reduce long windows to head windows; `d=2` unconditional; all `d` ⇔ RH.

Structure [D]: the limit pencil at a fixed ratio is a finite rung. Far windows are paid by the exponential weight, so positivity on smooth families at ratio `R` follows from `a*(ζ)≥(1/8)log R+O(1)`. What is left at a fixed ratio is compactness of bounded-energy sequences, i.e. the full complement: growing conductors, far band and receiving-charge bubbles.

| | Obstacle | Strength |
|---|---|---|
| A10–A14, A35 | Constants, profiles, ratio interval, channel norms, Schur debit, aliasing bookkeeping | — |
| B6 | Concentration-compactness at one ratio above the size-only optimum | sub |
| B7 | Full-space sign eventually at every `K` | RH |
| B8 | Growing families, moving and coalescing frequencies, conductors beyond `(log N)^{13/32}` | sub |
| B9 | Head thresholds for every `d` | RH |

### S2. Window tower and canonical flow

Routes: RW, EWU, OWU, ACT, AIP, CHMD, TT (odd), HF, ACS, SRT, SZ, MSC. Programmes: CWS, WTZ, DZG, GWZ, CSTW, SWC, FADF, CHT.

Established [L]:
- Precontact de Branges chain: Hermite–Biehler function, isometric inclusions, orthogonal increments, translation isometries.
- Canonical system with literal kernel; `H₁H₂=1`; anchor identity `τ_L²−τ_R²=2K`; endpoint flux `τ̄_L(z)τ_L(w)−τ̄_R(z)τ_R(w)=i(w̄−z)K(w,z)`.
- Gram AC with no atom; sampling bases at every non-exceptional phase; positive on-line mimic at every precontact aperture, and a positive mimic forces positivity; sampling atoms obey the local weighted count, uniform in phase.
- Window solutions with forcing dominated by constants and translates are bounded, with edge law `u(±(a−t))√log(1/t)→∫Kf`.
- Cone: effective pinning, margin ceiling, bands, datum classification. First-stage Schur complement in closed form. Exact two-sector format; `{2,3,4}` sliver band below `log 5`.

Structure [D]: `(log(1−r²))′≥−2|q|`, so `q∈L¹` on an interval excludes contact there. At finite-order contact `|q|≈2m`. The scale-invariant bound is `|q|≲C(a)m`, equivalently a uniform local variation bound on `r`.

| | Obstacle | Strength |
|---|---|---|
| A1–A3, A7, A8 | Certified verification, numeric heights, first-window membership, cone widths, Tate horizons | — |
| A19–A22 | Lean Riccati form, Gelfand–Levitan formula for `q`, numerical `r,m,q`, curve calibration | — |
| B1 | Sign on every window | RH |
| B2 | Contact exclusion: `∫dx/(1−r²)<∞` on bounded intervals, `q∈L¹_loc` | RH |
| B3 | Scale-invariant variation bound on `r`, free of `1/μ` | sub |
| B4 | Two-sector certificate inequalities | RH |
| B5 | Kick admission at every stage | RH |
| B17 | Decay law of `λ*(c)` | sub (rate) |
| B18 | Signed ground-state structure past `log ρ` | method |

### S3. Continuation and nodal geometry

Routes: ZCG, LA, PTR, HCF, PA, GTA, XN. Programmes: NGF, FFP, ADO, RHTower heat.

Established [L]:
- Collision criterion; high-time horizon `(6600/9991+ε)/log X`; `c d²/log X≤Λ_X`; a heat coefficient below `c/4` gives a zero-free strip.
- Fock identity, monotone frequency, order law, doubling; Hermite blow-up; Sturm drop law with buffered curves; gap law `d(g²)/dt=8−g²S+O(g²log X)`; mesh pair rate `≥16/n−4Kg²`; maximum principle in real simple cylinders; uniform mesh above any real time; cluster spread rate `2n²(n−1)`; crystal symbol `ξ(2π−ξ)/g²`; depth moments dissipated.
- Multiplicity `≤(3300/9991+ε)log X`.
- Density-one and critical-scale crystal; zeros real at critical scale [S]; depth law linear unless crowded.
- `N_d` nondecreasing, supremum is off-line multiplicity, `N_d≤300√(d log d)`, roots with `|Re z|≤√(d log d)/100` real, off-line zero at height `γ` counted only for `d≳γ²log γ`.
- Cosine strict Laguerre sign above `½−vkHadamardWidth`.

| | Obstacle | Strength |
|---|---|---|
| A23–A26, A34 | Horizon to `4μ(½)`, power-saving exceptional set, lower depth law, module integration, Jensen rung | — |
| B26 | Exclude collisions at arbitrarily small time, all heights | RH |
| B27 | Frequency `<1` at every putative collision | RH |
| B28 | An arithmetic input distinguishing `Φ` among `Φe^{−τx²}` | method |
| B29 | Runs of `k` consecutive simple critical zeros on a positive proportion of windows, every `k` | sub |
| B24 | Outer-root control of `R_d(Ξ)` | RH |
| B25 | `N_d` bounded | ≥qRH |

### S4. Near-line geometry and long moments

Routes: WD, CTF, MC, TG; census. Programmes: CDG, APR, MZF.

Established [L]:
- Selberg CLT; off-line `log|ζ|` is the prime field up to a bounded error; Steinhaus transfer; barrier law; Lorentz mass exponential tail.
- Prime camera rate 2 for dominant zeros; Turán camera for bounded clusters; hyperbolic density theorem; `N(ρ)≤Πϱ` [S]; separation removed [S].
- Eight forms of `100%` clustering; root model separates clustering from `D_win`; last-scale floor; occupied windows lose one log; corridor `b log log T/log T` with exceptions `O(T/log^ηT)` [S].
- Long-moment slope `2wθ`, quantifier collapse, one-window and positive-proportion RH forms, exponent rigidity; collar factorization; zero-damping head `1−1/(D+1)`.

Structure [D]: isolated means Carleson uniformly separated in `H²(Re s>½)`. For equal-depth zeros spaced `s`, `Πϱ≈exp(−2πb/s)`, so `B₀≥e^{−x/8}` means a local fraction `≲1/8` of comparably deep zeros. Non-isolated zeros are bounded only through the mollifier defect, at rate `2θ`.

| | Obstacle | Strength |
|---|---|---|
| A26, A28–A30 | Module integration, moments past `21/50`, Chowla, census items | — |
| B57 | `100%` critical-scale clustering | sub |
| B58 | `D_win` | sub |
| B59 | Cluster wall: Density Hypothesis rate for all near-line zeros | sub |
| B60 | Negative moments of the normalized derivative at deep zeros | sub |
| B61 | A detector past the last scale | sub |
| B62 | Cofinal long moment bound | RH |

### S5. Production and precision

Routes: WL, MC, PBM, RB, JAS, CTF, FU, CFC, RP, LI, AIP. Programmes: ASRP, APR, AGT, AKLT.

Established [L]: reflection-pair prime count band ⇔ every classical one-sided criterion; entry filters (parity, purity, precision, unbounded aperture and length, stabilizer); necessary length of mollifiers; length–precision law; gauge torus exponents `[Θ,1]`; multivariate parity producers reach `(1+ε)x+C_εlog²x`.

| | Obstacle | Strength |
|---|---|---|
| A29, A31 | Chowla, Selberg degree-one | — |
| B48 | A deciding input at square-root precision | RH |
| B55 | `ε`-uniform producer (`C_ε` polynomial gives a strip) | sub to ≥qRH |
| B56 | `Θ<1⇒Θ=½` | sub |

### S6. Reflection and carriers

Routes: PM; W1C (candidate); RN and PTR in part. Programmes: RIT, ART, AOT.

Established [L]: resonance ⇔ `ζ(2s)=0`; `Q=2Re[WH,WH]`; `D_s≤0`, zero iff `Re s=¼`; boundary norm and first Whittaker mode give `ζ≠0` on `Re w=1`; boundary scattering modulus 1; full determinant has no arithmetic reflection even with `λ`-independent scalar; renewal `det₂` gives denominator, not Ξ.

| | Obstacle | Strength |
|---|---|---|
| A32, A33 | Physical mixed-parameter identifications (unverified), effective boundary lower bound | — |
| B66 | Independent `D_s≥0` or full Krein positivity | RH |
| B67 | Positive physical carrier | method |
| B68 | PM-native zero-free curve inside the strip | sub |

### S7. Index and support

Routes: HKT, AKLT, SC, RIT, CWS through HF, ACS; LA. Established [L]: `κ(φ_c)=κ+1`; finite index ⇒ Lindelöf; `κ∈{0,∞}` under escape, mixing or height decay; `sup_dN_d` is off-line multiplicity; `K_ζ^n` PD ⇔ RH.

| | Obstacle | Strength |
|---|---|---|
| B13 | Index ceiling uniform in resolution | ≥qRH |
| B14 | Exclude finite nonzero off-line support for ζ | sub |
| B25 | `N_d` bounded | ≥qRH |

## 3. Live routes

### WL — Weil lag
- **Path:** bounded prime-deficit critical energy → RH.
- **Established:** bounded endpoint energy ⇔ RH; first-band abscissa `2Θ`; `E(T)≤Ce^{T−κT^{ex}}`, `ex<3/5`; gauge exponents `[Θ,1]` [L].
- **(a)** Künneth and mixed jet calibration (A17).
- **(b)** `∃C∀T, E(T)≤C`, or first-band square-root bound (B49); half-power at the trivial gauge point (B50); parity-breaking producer (B48, B55).

### RW — Restricted Weil ground energy
- **Path:** `μ(a)≥0` at every radius → RH.
- **Established:** block S2. Canonical system to contact, `H₁H₂=1`, sampling, positive mimics, explicit verified-height window rung, floor tower frozen below `0.3621` [L].
- **(a)** A1–A3, A19–A22: certified verification, numeric window heights, first-window membership, Lean Riccati form, formula for `q`, numerical `r,m,q`, curve calibration.
- **(b)** All-aperture sign or subexponential floor (B1, B15); contact-excluding bound free of `1/μ` (B2); scale-invariant variation of `r` (B3); structural sign past `log ρ` (B18); margin law (B17).

### FU — Signed prime scheduling
- **Path:** signed Möbius history → one-sided sampled Abel bound → RH.
- **Established:** one-sided criterion at fixed `m`; one controlled sample per backward window `N^{1−δ}`; exhaustive bounded-block payment at fixed horizons [L].
- **(a)** None that moves the route.
- **(b)** Complete-history cross-clock bound retaining seed, drift, covariance, endpoints (B44).

### CFC — First-clock lower bound
- **Path:** first-clock sine coefficient bounded below on a tail → RH.
- **Established:** exact tail criterion; phase-natural transport is identity [L].
- **(a)** None.
- **(b)** Lower bound retaining prime, archimedean and endpoint terms (B44).

### RP — History floor
- **Path:** matched-quantile history → eventual linear floor → RH.
- **Established:** exact linear-floor criterion; low-LCM payment; sublinear floor impossible [L].
- **(a)** None.
- **(b)** High-LCM pairs, moving core, singular-domain terms in one floor (B44).

### PA — Prime–archimedean passivity (HJ alias)
- **Path:** prime−Gamma source sign → RH.
- **Established:** Hausdorff rows nonnegative for `r≥H(k)` with `H(k)` explicit; RH ⇔ initial segments; exterior diagonal criterion at `218/25`; row `k+1≤(3/2)(T−1)`, `r≤RT³` from verified height [L]. Saddle of a Hausdorff atom [S].
- **(a)** Row saddle estimates and horizons (A18); verified rows (A1).
- **(b)** Initial-segment signs uniformly in `k`, or `K(z,z)≥0` on the exterior sector, or `TV(n)/qⁿ→0` for every `q>1` (B33).

### MC — Möbius cancellation
- **Path:** half-power Möbius or Liouville cancellation → RH.
- **Established:** arbitrarily small `ε` with `sup_TE_ε(T)<∞` ⇔ RH; fixed `t₀`: `M_N(½+it₀)≪N^ε` ⇔ RH; undamped Hilbert energy `≤CTe^{−c·vkScale(T)}`; Haar-a.e. exponent `½`, Baire-generic `1`; flip exponent `max(θ,Θ)` [L].
- **(a)** Logarithmic two-point Chowla (A29).
- **(b)** Trivial-gauge cancellation (B50); signed long-modulus tail including the harmonic tail (B50); parity-breaking producer (B48).

### TT — Theta tail / Wold
- **Path:** weighted endpoint energy bounded for each `0<t<½` → RH.
- **Established:** Wold residual `O(e^{−c·vkScale(N)})`; `D_t+Q_t/2≥0`; boundedness ⇔ RH; uniform bound for `t≤κ·vkScale(N+2)/(96 log(N+2))` [L].
- **(a)** None that moves the route.
- **(b)** `C_t` for every fixed `0<t<½`, literal weights `(n+1)^{2t}`; endpoint `t=½` fails (B36). Odd branch: B4.

### LA — Jensen line anchor
- **Path:** Jensen polynomials real-rooted or sublinear root height → RH.
- **Established:** block S3. RH ⇔ infinitely many unshifted degrees real; RH ⇔ sublinear upper-root height for mollified, shifted families; reality from verified `2·10⁷d⁴≤T log T` [L].
- **(a)** Jensen rung toward saddle scale, constants in `300√(d log d)` (A34, unverified); A1.
- **(b)** Outer-root control (B24); bounded `N_d` gives finite support only (B25, B14).

### ZCG — Zero-configuration geometry / heat descent
- **Path:** half-Gaussian source → no positive-time collision → RH.
- **Established:** blocks S3, S4. Collision criterion; `c d²/log X≤Λ_X≤(6600/9991+ε)/log X`; density-one reality, central inequality at every fixed `κ` and at critical scale; cameras; sharp location `e^{−c log³T}` under positivity at `λL_T`, `λ>1` [L/S].
- **(a)** A15, A23–A26: camera constants, horizon `≈0.619`, power-saving exceptional set, lower depth law, module integration.
- **(b)** Collisions at small time, all heights (B26); frequency `<1` at every putative collision (B27); arithmetic time-0 selector (B28); `k`-runs (B29); FE-pair reality with coverage (B73). Global central inequality is stronger than RH, so it is not the right target. `0∉E` (B74) is separate and decides no real part.

### TG — Topological sub-unit gate
- **Path:** cubic defect trace norm `<1` → integer zero count vanishes → RH.
- **Established:** defect constructed, trace class; multiplicity `≤` trace norm; RH ⇔ every rectangle has some `x>0` with norm `<1`; Gaussian passage alternative [L].
- **(a)** None that moves the route.
- **(b)** Trace norm `<1` on every rectangle, or bounded centered Gaussian oscillation (B40).

### HF — Hodge / Hecke / complete cells
- **Path:** complete arithmetic form `≥0` → Hodge index → RH.
- **Established:** block S1; `xiDampedSourceWork` ceiling `≤2` cofinally ⇔ RH; logarithmic ceiling proved; `P_N≤(log N−γ+ε)|x|²` and depth law with explicit horizons; sharp Schur bound `½log N` [L].
- **(a)** A10–A14, A17, A22, A35.
- **(b)** Concentration-compactness at one ratio (B6); full-space sign at every `K` (B7); growing twists and conductors (B8); head windows (B9); source-work ceiling (B43); top coprime stratum (B11); zero modes (B10); exact SOS on a two-prime lattice (B12); Rosati and band poles (B75, B76).

### CHMD — Causal hyperbolic–modular duality
- **Path:** one-sided bounded prime wave or odd Doob half-threshold bound → RH.
- **Established:** wave and Doob receivers; normalized prime−pole decay `O(e^{−√log Y/92160000})`; nonfirst source retains fraction `1−ε` of Gamma energy [L].
- **(a)** Mixed Schur debit (A14).
- **(b)** Either side of the unnormalized wave bound, or complete odd sign paying first-prime, potential and polar terms (B37, B4).

### TH — Theta moment positivity
- **Path:** signed center-mixed jets → all-rank Hankel → RH.
- **Established:** ranks `≤9` at all `0<a<½`; all ranks in a VK collar; two-atom sections at every rank; every geometric chain `q^n` positive; rank-uniform Gaussian remainder; no fixed head pays it; pointwise iteration fails at `log 6`; rank `N` from current on `|b|≤D(N+1)³`; Bessel cosh averages explicit [L/S].
- **Structure:** `S=Σ_Nτ_b(N)A(N)`; Euler operators `T_p=(1−2cos(b log p)σ_p+σ_p²)^{−1}` with `σ_p` the shift by `log p` multiply Laplace mixtures in `log N` by `|1−p^{−s+ib}|^{−2}>0`; `A` has a log-concave tail outside that cone; `current/a→Ξ′²−ΞΞ″` as `a→0` [D].
- **Numerics:** positive at actual phases, `b≤775`; torus-uniform positivity fails once primes `≲19–47` are free [N].
- **(a)** Rank 10 (A4); tail-failure certificate (A6); operator form and scans (A36); verified ranks (A1).
- **(b)** `S`-smooth spectra on small `S`, first `{2,3}` (B21); Euler-invariant cone containing `A` (B22); full-source rank `≥10` at every `a`, all ranks (B23).

### RN — Theta renewal
- **Path:** two-ended renewal → no joint nodes → RH.
- **Established:** `det₂` gives `D`, not Ξ; `Ξ=0` ⇔ joint node for `|x|<¼,y>0`; energy comparison ⇔ RH; `D` has nonreal zeros [L].
- **(a)** None.
- **(b)** Joint-node exclusion or the energy comparison (B38).

### WD — Ward / collision / long moments
- **Path:** source current, window energy or long moments → RH.
- **Established:** block S4. Attained extrema and collision receivers; one-window RH form; slope rigidity [L].
- **(a)** A26, A28; constants.
- **(b)** Cofinal long moment (B62); `D_win` (B58); clustering (B57); cluster wall (B59); negative moments (B60); detector past the last scale (B61); collision charge (B63). Finite and shallow exceptions remain outside density statements.

### LI — Paired Li / Cayley ladders
- **Path:** primitive lower bound or Li sign → RH.
- **Established:** guarded zero set finite, RH iff empty; ladder = Li coefficients; RH ⇔ NSD on primitives; subexponential response criterion; Li `n≤4.7T` from verified height [L].
- **(a)** Verified entries (A1).
- **(b)** Budget at every guarded zero, primitive lower bound or response floor (B45).

### SZ — Suzuki screw
- **Path:** completed Abel residual bounded → RH.
- **Established:** first variation = Weil energy; `|A_N|≤C√N e^{−c·vkScale(N)}`; bounded ⇔ RH [L].
- **(a)** None that moves the route.
- **(b)** `sup|A_N|<∞`, complete first-variation sign, or rectangular Ward lower bound (B39, B1).

### PM — Gauss–Mayer physical model
- **Path:** scattering source → Krein/Lewis positivity → RH.
- **Established:** block S6 [L].
- **(a)** Physical identifications (A32, unverified); effective boundary lower bound (A33).
- **(b)** Independent `D_s≥0` or renormalized Krein positivity (B66); positive physical carrier (B67); interior zero-free curve (B68).

### PTR — Cosine source / photonic
- **Path:** `A_h` collision-free descent → RH.
- **Established:** sech handoff; strict Laguerre for `h≥½` and for large `|x|`, `h>½−vkHadamardWidth(|x|+1)`; sign at every `0<h<½` ⇔ RH [L].
- **(a)** None.
- **(b)** Strict sign below the VK boundary (B31); independent lossless prime-faithful stack (B67).

### JAS — Joint ancestry
- **Path:** subpower control on moving finite power windows → RH.
- **Established:** `RH⇔∀ε, frequently, |Riesz(m²,k)|≤m^{εk}` on `m<k≤m+m/log(m+1)`; finite admission [L].
- **(a)** None.
- **(b)** Uniform arithmetic control on that window (B51).

### CTF — Chronological tail / Báez–Duarte
- **Path:** approximation, defect or BSY sign → RH.
- **Established:** real unit-bounded rows ⇔ RH; sharp defect `D_y≥c_ρy^{2Re ρ−1}`, sparse subpolynomial ⇒ RH; BSY `I≤0⇔RH`; positive-proportion form on every window ⇔ RH; good-set restriction cannot lower the exponent [L].
- **(a)** None that moves the route.
- **(b)** Vanishing-error rows, sparse subpolynomial defect, BSY sign or uniform positive proportion (B52).

### HCF — Heat trace
- **Path:** both prime-log grids positive at every degree → RH.
- **Established:** two-grid criterion at fixed offsets; explicit detector degree; bounded prime chirp on a vertical line ⇔ RH; vertical Cesàro mean of the chirp `→0` ⇔ RH; degree `+1≤T/4800` from verified height [L].
- **(a)** Verified degrees (A1).
- **(b)** Nonnegativity at every degree, or chirp bound or mean (B32).

### XN — Newton discs
- **Path:** line-centered self-map discs covering every zero → RH.
- **Established:** coverage and closed-margin criteria; `ΔM=4(r²−|z−c|²)|ξ″|²`; local damping preserves first jets [L].
- **(a)** None.
- **(b)** Cover every zero with `M≥0` throughout (B34).

### BAG — Self-return
- **Path:** strong self-return / head-target mass → RH.
- **Established:** flow/head-target transfer; cutoff-uniform positive mass ⇔ RH; weak recurrence ladder [L].
- **(a)** None.
- **(b)** Cutoff-uniform positive mass (B69).

### EWU — Even sector
- **Path:** even blind minimum `≥0` → RH.
- **Established:** Hamburger form; neutral gauge; Markov to `log ρ`; blind minimum `≥1/20` for `a≤(log 2+1/50)/2` [L].
- **(a)** Verified windows (A1–A3).
- **(b)** Blind minimum `≥0` at every aperture; `2V≤J_{M⁺}` (B4, B18, B46).

### GTA — Schur charge
- **Path:** cofinally small quartic charge or compact full mode → RH.
- **Established:** charge family; compactness ⇔ RH; late charge `≤HS/400`; small-spectrum charge `≤(150δ²+425δ³/4+ε)·HS²`; skew energy has positive limit [L].
- **(a)** None that moves the route.
- **(b)** Charge `<ε` at arbitrarily late stages; large spectral nodes uncontrolled (B35).

### OWU — Odd sector
- **Path:** odd polar-hyperplane positivity → RH.
- **Established:** shifted Hamburger; unit window reads `w₂`; frustration; variance retention necessary above `273/400` [L].
- **(a)** A1–A3, A7.
- **(b)** Sign at every aperture on compact C² odd `F` with `∫F sinh(x/2)=0`; retained-variance payment (B4, B18, B46).

### PBM — Regularized abscissa
- **Path:** pole-regularized prime series converges for every `σ>½` → RH.
- **Established:** exact equivalence [L].
- **(a)** None.
- **(b)** `|Σ_{n<N}(Λ(n+1)−1)/log(n+1)|≤C_εN^{½+ε}` (B53).

### RB — Robin/Nicolas
- **Path:** eventual extremal divisor inequality → RH.
- **Established:** colossally abundant and lcm reductions without `Θ<1` [L].
- **(a)** None.
- **(b)** Eventual inequality on colossally abundant `n`, or lcm defect bound (B54).

### SRT — Lag localization
- **Path:** complete two-bump sign or horizon-layer sign → RH.
- **Established:** full-family receivers; explicit horizons; sharp location; split-column receiver; depth mass bound under positivity [L/S].
- **(a)** A10, A15, A16.
- **(b)** Complementary-window sign, tails and source kernel at every ratio (B7, B8, B13).

### ACT — Single shift
- **Path:** one shift pays every even compact profile → odd positivity → RH.
- **Established:** single-shift receiver; `{2,3,4}` band with kicks `<0.991` of Lévy energy; floors through `a_k` [L].
- **(a)** Anti-diagonals (A9).
- **(b)** One shift uniform in profile paying `D_a` (B46, B4).

### AIP — Incidence
- **Path:** complete reflected-prime/pole allocation → subexponential cost → RH.
- **Established:** allocation; `|cost|≤Ke^{r−c(2r)^{3/5}(log 2r)^{−5/3}}·Sobolev` [L]; capacity `log log N+O(1)`.
- **(a)** A10–A14.
- **(b)** `C_σe^{2σr}` cost bound for every `σ>0` (B47); packet-branch complement (B6–B8).

### SC — Stokes / Witt–Krein
- **Path:** glued index `≤1`, or bounded damped two-prime coupling → RH.
- **Established:** `κ(φ_c)=κ+1`; bounded coupling ⇔ RH; heat-average representation with full source [L].
- **(a)** Curve calibration (A22).
- **(b)** Arithmetic coupling bound; sublinear tensor loss (B41); B10, B12, B14.

### ACS — Castelnuovo–Severi
- **Path:** source energy → all-aperture Bézout → RH.
- **Established:** exact source cone; all-aperture Riemann–Roch; Bézout ⇔ RH; primitive `h¹` coercive for `a≤181/500`; curve windows characterize unitary spectra [L].
- **(a)** A17, A31.
- **(b)** Source-energy sign at every radius (B42, B1); independent count or Rosati producer (B75); genus, Serre duality, Epstein (B65).

### SEC — Seam / Fock
- **Path:** factorial jet energy at ξ zeros → RH.
- **Established:** seam admitted; `F_ρ` identified; Fock bound ⇔ RH; constant may depend on `ρ` [L].
- **(a)** None.
- **(b)** Bound at actual zero parameters (B70).

### CDC — Dagger (BSH alias)
- **Path:** marked-repair equality at ξ zeros → RH.
- **Established:** canonical potential, Euler-face metric, calibration; `N=1,n=2` equality suffices [L].
- **(a)** None.
- **(b)** Proof-erasure equality at every zero (B71).

### PCS — Co-shift
- **Path:** reflection-odd class vanishes at ξ zeros → RH.
- **Established:** quotient vanishing ⇔ `n^{−ρ}−n^{−(1−ρ̄)}∈ℓ²` ⇔ RH; cutoffs converge strongly with a persistent gap [L].
- **(a)** None.
- **(b)** Vanishing at every zero; independent differential lift retaining the shift defect (B72).

## 4. Candidates

Each needs its independent mechanism first (B78).

| Candidate | Established [L] | (a) Just work | (b) Open mathematics |
|---|---|---|---|
| APF | prime/grade trace reconstruction on real labels | none | full-divisor exhaustion and RH landing |
| EGC | double-Gaussian zero-pair contour; inner remainder vanishes | contour constants (A37) | height-fibre isolation; outer landing |
| EWJ | all-depth reporter; norm exhaustion only on blind plane | none | faithful endpoint admission |
| FEL | KL accounting; BSY criterion belongs to CTF | none | calibrated predeclared history forcing BSY sign |
| IRK | finite idempotent traces; Meyer–Ξ free resolution | none | projective lift identifying trace with Chern charge |
| MSC | unweighted `L²` discrepancy; conormal transport | none | Sonin/Weil sign landing |
| RFHM | support source; creation; strong exhaustion | none | RH-sufficient orientation law |
| W1C | Lee–Yang receiver; one-interval convergence suffices | none | finite ferromagnetic producer converging to Ξ |
| WBF | Gram recovers magnitudes and phase class | none | arithmetic stream and Ξ landing |

## 5. Supporting programmes

| Programme | Established [L/S] | (a) Just work | (b) Open mathematics |
|---|---|---|---|
| CSTW | canonical system, `H₁H₂=1`, sampling, mimics | A19–A21 | B2, B3 |
| CHT | margin law, pinning, datum, bands, edge law | A7 | B17 |
| VHR | rungs: window, Li, Hausdorff, heat, Jensen, PF, theta | A1, A2 | none; decides no all-aperture statement |
| NGF | frequency, blow-up, gap laws, maximum principle, critical-scale crystal, order bound | A24–A26 | B26–B29 |
| MZF | Selberg CLT, cameras, hyperbolic density, derivative bound, rigidity, last scale | A26, A28 | B57–B61 |
| FFP | `N_d` law, saddle region, stability dictionary, bulk blindness | A34 | B24, B25 |
| ADO | carrier repulsion; a.e. value; exceptional set dimension `≤1`; FE-pair flatness `|γ|^{33/200+ε}δ²` | none | B74 |
| APR | necessary length, filters, prefix amplification, collar laws | A28 | B48 |
| PBAP | blind positivity, blind ζ dictionary, Carlson threshold, capacity bound | none | B19, B20 |
| WVL | master law `k·pairEnergy(δ,a)≤L`, shallow depth-mass bound [S], explicit detector | A16 | none beyond B1 |
| AHD/CACT | aliasing limits, dual floors, head reduction, polar capacity | A10–A13, A35 | B6–B9 |
| CAF | two-atom, geometric chains, Gaussian boundary, cosh averages | A36 | B21–B23 |

## 6. Decisive wall per route

| Wall | Routes |
|---|---|
| Σ sign or budget | RW, EWU, OWU, ACT, CHMD, SZ, RN, ACS, AIP, SRT, SC, LI, TT (odd) |
| Σ full-space compactness, then sign | HF, SRT and AIP packet branches |
| Σ continuation at small time | ZCG, PTR, LA, GTA, XN, HCF, PA, TH |
| Π square-root precision and long moments | WL, MC, PBM, RB, JAS, CTF, FU, CFC, RP, TT (endpoint), WD, TG |
| Γ reflection and selection | PM, BAG, SEC, CDC, PCS |
| Missing source landing | APF, EGC, EWJ, FEL, IRK, MSC, RFHM, W1C, WBF |
