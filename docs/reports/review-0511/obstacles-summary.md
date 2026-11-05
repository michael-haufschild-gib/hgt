# Obstacles summary — status quo

Companion to `route-obstacles.md` (per route; labels `A*`, `B*`, `S*`, mechanism classes P1–P5),
`walls-ledger.md` (Σ/Π/Γ) and `route-unification-ledger.md` (mechanism classes). Corpus checkpoint: `9c877bf0377b015a3d009764764926a61c7b657e`.
Evidence: `[L]` integrated, source-reviewed Lean; `[S]` unfinished/unintegrated; `[D]` inference, not a Lean theorem; `[N]` unverified numerical observation. Windows `[−c, c]` or
half-windows `[−c, 0]`; `w_n = Λ(n)n^{−1/2}`; `H` the archimedean–polar form (prime weights `0`), `P` the arithmetic
part, `W = H − P`; `𝒥` the Lévy energy; `𝒞_m(f) = 𝓗_m(f) − Σ_n w_n(f⋆f)(2m − log n)`; `a*(ζ)` the onset aperture;
`ℋ(c) = {t : H − tP ≥ 0 on [−c, c]}` the arithmetic Hardy interval; `𝒜(c)` the window cone of weights `λ` with
`W_λ ≥ 0` on `[−c, c]`; `λ*(c)` its best margin; `L_T = ½log(T/2π)`; `a_k = weilFloorApertureTower k`,
`a₀ ∈ (181/500, 181/500 + 5×10⁻⁷)`, `a_∞ = lim a_k` (not identified); `log ρ ≈ 0.2812` (plastic number);
`Θ = sup Re ρ`; `N_d` the number of non-real roots of the degree-`d` reversed Jensen polynomial of `Ξ`; `E` the
exceptional values of ζ (a dense `G_δ` null set).

**38 live formulations; 9 candidates.** Live means a concrete source, RH-sufficient receiver and explicit open estimate—not a discharged RH proof or an independent mechanism. ZCG, PTR, SEC, ACS, CDC and PCS satisfy this definition. HJ→PA; BSH→CDC; FEL's BSY criterion→CTF. Candidates: APF, EGC, EWJ, FEL, IRK, MSC, RFHM, W1C, WBF. Authoritative classifications: [frontier](../rh-current-frontier-map.md), [killed/retired mechanisms](../rh-killed-routes.md).

## 1. The big picture

### 1.1 One sign, one number, one inequality
RH ⇔ `a*(ζ) = ⊤` ⇔ `1 ∈ ℋ(c)` for every `c` ⇔ `λ*(c) → 0` [L: WVL, FADF, CHT]. Weil positivity is a **critical Hardy
inequality**: the arithmetic part `P` must be a Hardy term for the archimedean logarithmic jump operator with the pole
kept, `H ≥ P` on every window. Two necessary properties hold unconditionally: the multiple `1` is the only
multiple admissible on every window, and no Hardy weight survives on odd tests [L]. Admissibility on
every window is RH. Known: `a*(ζ) ≥ a_∞`: `windowThreshold A = ⊤` for `A ≤ 2a_k` on an infinite strictly increasing
tower from `a₀` with floors `(1/20000)/2^k`; the tower has no proved upper bound and its limit is not identified [L/D].

### 1.2 The cone is pinned and its margin collapses
On `𝒜(c)` every weight is pinned: `|λ(n) − Λ(n)| ≤ C exp(Kn − c/1104)` for `c ≥ 2`, `2 ≤ n ≤ e^{2c−1/6}`, so every
integer up to a fixed multiple of the aperture is forced to `Λ(n)` within `Ce^{−c/2208}`; the bands of `λ(n)` are
intervals of width `≥ λ*(c)√n`, hence `λ*(c)√n ≤ Ce^{Kn−c/1104}` [L: CHT]. Over all weights the best margin obeys
`λ*(c) ≤ K exp(3c − (π/6)e^{2(c−13/12)})` and the Gaussian ceiling; at the tower apertures `λ*(a_k) ≥ (1/20000)/2^k`
[L]. The datum of ζ is the critical point of the cone family: at pole weight `1` every negative log-conductor has
eventually empty cones, at log-conductor `0` nonempty cones force pole weight `≥ 1 − K exp(3c − (π/6)e^{2(c−13/12)})`,
and the critical log-conductor equals `−λ*(c)` [L]. Finite-window weights remain variable; their global intersection
is `{Λ}` under RH and empty otherwise. The open target is nonnegativity at every aperture; `a_∞` is not known finite.

### 1.3 The certificate format is exact on every window
On every reflection pair `W(f) − |𝒞_m(f)| = ½min(W(G₊), W(G₋))`, the coupling truncating to `2 ≤ n ≤ e^{2c}` [L: SWC].
The even sector is represented exactly by a window-adapted, line-exact signed theta gauge with zero pole charge
(`2V ≤ J_{M⁺}`), the odd sector by a shifted ground state; nonnegativity of both on every window ⇔ RH [L]. The gauge
freedom acts only in the pole direction: on the pole-neutral hyperplane every neutral gauge reads `archForm − primeSum`,
and receding pockets conserve the outside deficit [L]. At `2c < log 5` the window is an exact three-power problem: the
`{2,3,4}` sliver band, with only `n = 2` acting in the half-window diagonal [L]. What is open is the inequality the
format states, not the format.

### 1.4 Frustration cannot be switched away
The even kernel is Markov exactly for `c ≤ log ρ`; past it the even band fails Beurling–Deny at every pole strength
and all weights, and is frustrated in every sign gauge [L: SWC, FADF]. The odd light cone is positive, and each acting
prime power adds an anti-diagonal frustrated in every sign gauge when it acts [L]. For every admitted global positive
weight sequence, odd frustration occurs at sufficiently large apertures; this is not a common onset at `½log 2`
for every finite-window cone point [L: CHT]. The even obstruction past `log ρ` is weight-independent. Trivial zeros are paid by
centre killing [L]. What remains to pay: the constant potential, the pole square (odd), the prime reflections (both).

### 1.5 Limits of the specified size-payment certificates
The summed edge law `|P_μ(f)| ≤ E_c(μ)𝒥(f)` certifies by size until `E_c = 1`; for ζ the unique crossing is
`c* ∈ (½log 5, ½log 6]` [L]. Size dies before that: `H` itself is negative on a window of half-width `≤ 21/40`, and
beyond a finite window one real test makes the prime part strictly negative for the whole calibration space [L]. Below
`log 5` the reflected kicks of `2, 3, 4` together use less than `0.991` of the Lévy energy [L]. Each entering weight is
confined two-sidedly with sharp logarithmic constants [L]. The primes pay by sign.

### 1.6 Finite matrices end before `log 6`
Positivity of any correlation form on a window is positivity of all finite rational Hecke graphs of smaller
log-spread [L: WTZ]; at spread `6` the ×2/÷3 orbit in `[1,6)` is infinite, so no finite template exists there [L].
Exact Tate horizons are computed through `log(81/16)` [L].

### 1.7 The window tower is a de Branges chain until contact, and the chain has a Hamiltonian density
Before contact every window carries a complete Weil Hilbert space realized by entire functions, a de Branges space with
an explicit Hermite–Biehler function, unitary zero-moving, antiunitary conjugation and isometric inclusions; growing the
window adds an orthogonal kernel increment; the exterior crossings are bounded by `C_b‖u‖‖v‖` independently of the
collar width; the normalized exterior response tends to minus the endpoint trace with the factor `√log(1/t)`; the prime
and polar responses are continuous [L: CSTW]. The Weil symbol is `1 + ½log(1 + ξ²)` minus a bounded convolution and
factors through a logarithmic Poisson factor with a positive causal kernel; the half-line Green operator is explicit
[L]. The evaluation Gram `G(a)` of the Riesz vectors is monotone with `0 ≤ ∫_a^b G′ ≤ G(b) − G(a)`: the chain has a
Hamiltonian density, and the gap is its singular part [L: CHT]. Either RH, or some diagonal kernel diverges at `a*`,
the first singular length [L]. Actual Riesz endpoint traces and full-collar pointwise/scaled-`L²` limits at fixed
apertures are established. Complete collar energy per mass lies above `log(1/h)−C_a`; constant collars attain
`log(1/h)+3+C_a`, with `C_a = ‖weilLogarithmicCorrection a‖` [L]. Open: absolute continuity, boundary-flux/support
variation, moving-endpoint estimates and contact-uniform arithmetic kernel control. The density inequality alone
does not identify increments with its integral or exclude contact.

### 1.8 Identification is complete, effective, and locates
At aperture `λL_T`: `λ > 1` fixes RvM configurations up to near-collisions, `λ > ½` reads every isolated zero of ζ with
its multiplicity, at explicit heights [L: ZCG]. Inside isolated clusters of radius `r ≤ T^{−(M'+κ_λ+1)}` the camera reads
centres, squared gaps, discriminants and point locations from finitely many window images [L]. For a two-point cluster
`𝓗 = 4(W₁² − W₀W₂)/W₀²` is the squared gap; FE-pair squared gaps `≥ 0` at every zero ⇔ RH [L]. The camera reads weighted
mass, never cardinality: positive on-line mimics of ζ's image at fixed aperture have `Σw ≤ [θ(y−x)/(2π) + A]log(T/2π)`,
while one flat image carries arbitrarily many atoms [L]. **Sharp location is a theorem:** positivity of Weil's form at
aperture `λ·log(T/2π)/2`, `λ > 1`, at heights `T ≥ zetaNegativeCameraHeight`, confines every zero of ζ at height `T` to
depth `< exp(−c log³(T/2π))`, by two normalized convolution cameras at the cluster and its reflection, without any
on-line mimic or separation premise [L]. It is a receiver: the floor tower does not establish positivity at these
height-dependent apertures. Isolated-cluster readout assumes isolation; the weighted-mass theorem does not construct a positive mimic.

### 1.9 ZCG continuation and LA finite-free stability
ZCG's actual half-Gauss source `Q(t,xiLine X)` has a collision exactly when `Re Q(0) = Im Q′(0) = 0`; excluding
all positive-time collisions is equivalent to RH. Large-height collisions are excluded for
`t ≥ (6600/9991 + ε)/log X`; the saddle crosses `Re s = 1` at `½/log(X/2π)` [L]. The smaller-time region and
low-height compact box remain open. Size-only pair models do not decide the actual source.

LA's `N_d` is nondecreasing; `Ξ` has at most `m` off-line zeros iff
`N_d ≤ m` for all (equivalently infinitely many) `d`, `sup_d N_d` is the off-line zero count, `N_d` is bounded iff the
off-line support is finite, and eventually `N_d ≤ 300√(d log d)` [L: FFP]. The bulk is blind: at scale `½log d` the
real roots of `R_d(ξ(σ+i·))` follow the Cauchy law `1/(w+i)` for every `σ ≥ ½`, and the same law holds for every
backward heat flow `H_{−τ}`, which has non-real zeros [L]. Every zero-free half-plane `Re s > σ` is equivalent to
stability of the Jensen polynomials of `ξ(σ + i·)`; `ξ` has no stability margin on any line; the phase `c = 0` is
exactly critical; the genus-one class is classified by its drift [L]. The specified source-faithful split fails; the
Euler side is stable with forced drift `θ_S/2`, the ζ, Gamma and pole sides are unstable [L]. The off-line zero count is
the supremum of finite polynomial counts. The sublinear upper bound does not imply finitely many off-line zeros.
For actual finite Möbius mollifiers, sublinear maximal imaginary root height along cofinal degrees is another
RH criterion; failure of RH forces eventual linear root height [L].

### 1.10 RH equivalences are not mechanism identities
Exact identifications [L]: the reflection-pair prime-count band ⇔ Weil-lag ⇔ JAS ⇔ CTF ⇔ PBM ⇔ eventual Robin (SWC);
Suzuki first variation = complete Weil energy (SZ); the Cayley ladder = Toeplitz ladder of paired Li coefficients, RH ⇔
every ladder NSD on primitive vectors (ALG); inner-cap flux = off-line generating function (WD); single-prime stage
transport ⇔ RH and Dirichlet-shift head stabilization for every `d` ⇔ RH (HF); two real parameters `(γ, v)` decide the
line (SRT); any nonnegative representation of the Mayer defect ⇔ RH (PM); RH ⇔ `λ*(c) → 0` (CHT); RH ⇔ `N_d = 0` for
infinitely many `d` (FFP); RH ⇔ every Hausdorff row nonnegative on its finite initial segment `r < H(k)` (PA); RH ⇔
every finite-degree two-grid heat functional nonnegative (HCF); RH ⇔ the odd Biane–Pitman–Yor Poincaré inequality (TT).
These equivalences identify global truth values. They do not turn one unproved estimate into a constructive input
for every other route; candidates lacking a source or landing remain candidates.

### 1.11 PM's second expression has the same sign
`−D_s(ψ_s) = |1 + p^{1−2s}|^{−2}∫_1^∞K_σ|T_{p,s}ψ_s|² = ∫_0^∞K_σ(x+1)|ψ_s(x) − (x+1)^{−2s}ψ_s(x/(x+1))|²`,
`K_σ ∝ (b^{2σ−½} − b^{−(2σ−½)})²`, `K_{1/4} ≡ 0` [L: RIT]. Infinitely many resonances lie on `Re s = ¼`, where `D = 0`
while every norm is positive. The coefficient-space Krein completion and its exact quadratic-form identification
are established. Open: physical mixed-parameter realization/descent and independent nonnegativity of this weighted
defect at upper resonances (or full Krein positivity). An unweighted norm is not the defect.

### 1.12 Visibility and the vacuity of short windows
`k·pairEnergy(δ,a) ≤ L` in lattice backgrounds; unshielded clusters excluded to doubly-exponential height; tapered
crystals hide depth `1/a` above `e^{ca}`; doubly-exponential non-locality [L: WVL]. Effective forms: positivity at level
`a` confines every zero with `|γ| ≥ 102` to `|β − ½| < 10⁶exp(−a/(480000 log(|γ|+3)))`, and positivity at `λL_T` to
depth `< e^{−c log³T}` [L]. These are conditional location receivers. The tower starts at `a₀ ≈ 0.362`; its limit
`a_∞` is unknown. No proved cofinal aperture coverage supplies the required height-dependent positivity.

### 1.13 Arithmetic production and necessary mollifier length
A property of weights implying the count `ψ(x) − x = O(√x log²x)` must be parity-breaking, locally pure,
precision-faithful against `εn^{−η}`, `0 ≤ η < ½`, of unbounded aperture and length, with stabilizer in the square-root
class [L: ASRP, APR]. Specified producer classes fail these tests: PNT and error laws weaker than
square root; Type I information at level `N^{1−δ}` and Type II norms (parity-blind); finite systems of linear laws, Mertens
included (common perturbation outside the square-root class); every upper bound on `Re s ≥ ½` that survives the impure
factor `ζ(s)(1 − cp^{−s})`, `c > √p`; the Liouville twin `λΛ + 2` shares every error law above `√x` [L]. A proved
landing for mollified second moments is: moment `→ 1` at length `exp(o(T))` gives the log-mean
`→ 0` and `100%` critical-scale clustering; excess `K₀/log T` at length `exp(T/log T)` gives `D_zero` and `D_win`; a
dyadic bound `≤ CT` with the prescribed prefix cancellation and `θ > ½` gives finitely many zeros of depth
`≥ 1/(2θ)+ε` for each `ε > 0`, not finiteness of every off-line zero. A cofinal bound
`≤ C_θT^K`, fixed `K`, for arbitrarily large `θ` gives RH [L: APR, CDG]. Necessary-length laws: every
normalized unit-bounded Dirichlet polynomial of length `T^θ` has second moment `≥ (1 + 1/(8+6θ))T` (real coefficients to
`θ ≤ log T/24`, complex to `log N ≤ T^{1/60}`); excess `K₀/log T` forces `log N ≥ log²T/(6K₀) − (4/3)log T`; moment
`→ 1` forces `log N/log T → ∞` [L]. These lower bounds do not prove attainability. Complex-mollifier/window-spike
receivers are integrated [L]; actual moment bounds remain open. They bound off-line occupied windows, not a
critical-line zero proportion. The second moment at length `T^θ` sees `εn^{−η}` exactly for `η < ½ − 1/(2θ)` [L].

### 1.14 The near-line ladder is sharp
Eight equivalent forms of `100%` critical-scale clustering [L]. The critical-line proportion `N₀(V)/N(V) → 1` implies
all of them [L]. `D_win` is not a proportion statement: a reflection-symmetric unit-window model with local RvM, simple
critical proportion `→ 1` in every window, depth tails `≪_r e^{−ra}V` for every rate `r`, (L) and clustering still
violates `D_win` and `D_zero`; `D_win` needs depth decay at rate `≍ log log V` [L: CDG]. `D_win` follows from any
holomorphic actual-zero detector with shifted `L²` defect `≤ Ce^{−r(σ−½)log V}·V/log V`; the `V/log V` scale is sharp,
since the Fejér–Dirichlet detector vanishes in `≥ V/12` windows with every `L^p` and `log⁺` defect `≪ V/log V`; every
subcritical polynomial mollifier has shifted defect `≥ c_{θ,A}V` and disc-corridor bound `≫ V log V` [L].

### 1.15 Repulsion is Diophantine and sign-free
Distinct zeros of finite Euler carriers, of integral pure carriers, of degree-two integral factors and of the two-prime
cusp carrier at height `≤ T` are `≥ cT^{−C}` apart (Baker–Matveev); a Liouville Satake angle defeats every polynomial law
and a.e. angle obeys one; `(1−2^{−s})(1−3^{−s})` has distinct zeros at every positive distance [L: ADO]. For a.e. value
`a ∈ ℂ` the `a`-points of ζ repel polynomially; the exceptional set `E` is a dense `G_δ` null set [L]. Polynomial
repulsion of ζ's zeros is the statement `0 ∉ E`; it is open under RH and has no implication for real parts, since an FE
pair at depth `δ` is separated by `2δ` [D]. Near-coincident zeros force joint small values of ζ and ζ′ under the
stated local bounds; small values alone do not prove an off-line pair. An FE pair at depth `δ` makes
`|ζ(½+iγ)| ≤ 480e²(|γ|+2)(|γ|+5)δ²` [L]. Over `𝔽_q`, integrality
quantizes impurity and does not exclude it; finitely many power sums certify integral purity; a continuous integer
family is constant [L]. Integrality amplifies a certificate and produces none.

### 1.16 Criticality everywhere
Several receivers have critical boundaries: global Weil cone at most one point, finite-window coordinates pinned at rate `e^{−c/1104}`; margin ceiling
doubly exponential; only the multiple `1` admissible; no Hardy weight; the datum of ζ critical among `(β, s)`; lattices
Szegő singular; reflection coefficients at `±1`; Perron exactly to `log ρ`; kernel blow-up at contact; heat size horizon
at the saddle; Gaussian finite free capacity `o(d⁻²)`; `ξ` on the exact stability boundary; Euler drift exactly `θ_S/2`;
PM defect zero only at `σ = ¼`; mollified second moment floor `1 + 1/(8+6θ)` and necessary superpolynomial length;
numerical margins `10⁻⁴`–`10⁻¹²` [L/N]. None of these statements proves that every successful argument must be an identity.

### 1.17 What is ruled out
| Mechanism | Verdict | Anchor |
|---|---|---|
| Markov / Perron certificates past `e^{−3/4}` / `log ρ` | refuted at every pole strength and weight | SWC [L] |
| Balancing by sign gauges (switching) | even obstruction past `log ρ`; odd obstruction for acting prime reflections and eventually for every globally admitted weight | FADF, CHT [L] |
| Size-only payment of the primes | dies before `21/40` (`H < 0`); edge law at `c* ∈ (½log5, ½log6]` | FADF, SWC [L] |
| Certificates without pole variance; window-independent even gauges | refuted | SWC [L] |
| Point-value certificates | Weil's form reads no point values | FADF [L] |
| Uncoupled stage loans; orthogonal twisted repair of untwisted modes | refuted at `21/20`; `O(1/K)` | AHD [L] |
| Non-orthogonal (Dirichlet-shift) repair of long windows | cancels every tail; leaves the head window `windowThreshold(log d)` | AHD [L] |
| Gauge optimization off the pole direction | gauge-independent on the pole-neutral hyperplane | SWC [L] |
| Other globally admissible weights | global intersection `{Λ}` or empty; finite-window coordinates pinned within `Ce^{Kn−c/1104}` | CHT [L] |
| Other data (pole weight, conductor) | cones empty below the critical log-conductor; the datum of ζ is the critical point | CHT [L] |
| Finite-template reduction at spread 6 | infinite Hecke orbit | WTZ [L] |
| Source-faithful finite free split; Dirichlet, ζ-side, Gamma, pole pieces | never real-rooted / unstable | FFP [L] |
| Bulk statistics of Jensen roots (density-one reality, Cauchy law) | shared with every backward heat flow; carry no arithmetic | FFP [L] |
| Degree-3 semicircle-free test | every real-rooted cubic passes | FFP [L] |
| Nonnegative multiple of PM norms as the defect | refuted on critical resonances | RIT [L] |
| Global arithmetic majorants as exact ACS source cones | Bezout/ampleness hold, Riemann–Roch fails; exact source effectivity is constructed separately | ACS [L] |
| Height-local decision; universal density thresholds; domination as selector; size-only heat repair | refuted | WVL, ZCG [L] |
| Fixed / coherent / quartic / truncated quartic theta cross-loads | fail at exact scales with capacities `< 1` | TCS [L] |
| Finite-aperture positivity alone as a universal width selector | off-line configurations of every width can share that positivity | SRT, ASRP [L] |
| Hadamard and tensor amplification | every power `K_ζ^n` carries RH | RIT [L] |
| Integrality as a source of purity | `collide_or_repel` assumes the disc bound; impurity quantized, not excluded | ZCG, ADO [L] |
| Polynomial-length mollifiers for clustering | second moment `≥ (1 + 1/(8+6θ))T` | APR, CDG [L] |
| Mollifiers violating `log N ≥ log²T/(6K₀) − (4/3)log T` for the stated excess | excluded within the theorem's coefficient/length regime; no attainability theorem | CDG [L] |
| Critical-line proportion or any fixed exponential depth-tail rate as a route to `D_win` | the root model satisfies both and fails `D_win` | CDG [L] |
| `L^p` or `log⁺` detectors at scale `V/log V` for `D_win` | the Fejér–Dirichlet detector occupies `≥ V/12` windows | CDG [L] |
| PNT, Guth–Maynard, Type I at level `N^{1−δ}`, Type II norms, finite linear laws, impure-factor-stable upper bounds | precision-blind, parity-blind or purity-blind | ASRP, APR [L] |
| Fixed-aperture images as counts of atoms | weighted mass only; flat lattice with arbitrarily many atoms | ZCG [L] |
| A.e. repulsion or the exceptional set as a decision of `a = 0` | `E` is residual and null; `0 ∈ E` undecided | ADO [L] |
| Polynomial repulsion of ζ's zeros as a statement about real parts | FE pairs are separated by `2δ` | [D] |

### 1.18 The live mechanism classes
| Class | Statement | First open test | Status |
|---|---|---|---|
| P1 signed criticality | `H ≥ P` on every window in the exact two-sector format, frustration unswitchable | `a*(ζ) ≥ ½` (odd unit window, margin `≈ 2×10⁻⁴`); `a*(ζ) ≥ log 2` (two weights); `a*(ζ) ≥ ½log 3 + ε` (prime-3 head window) | live |
| P2 calibration | `λ*(c) ≥ 0` for every `c`; arithmetic point in every `𝒜(c)` | positivity beyond proved tower stages; cofinality or contact-excluding bound | live; tower limit unknown |
| P3 PM reflection | weighted defect nonnegative at upper resonances, or full Krein positivity | physical mixed-parameter descent and arithmetic sign | live criterion; coefficient completion closed |
| P4 square-root cancellation | prime-count bands, Li positivity, inner caps, long-mollifier moments | actual moment estimates; B64 is a sufficient target, not an attained length optimum | live |
| P5 continuation / stability | ZCG collision exclusion; LA cofinal Jensen hyperbolicity/root-height bound; PTR strict Laguerre sign | small-time collisions, actual Jensen outliers, `0<h<½` cosine-shift sign | live criteria; independent producers open |

### 1.19 What a finite window can and cannot decide
- **RH is an existence statement at finite levels.** RH ⇔ for every aperture `A` some real weights make `H − P_λ ≥ 0`
  on `[−A, A]`; only `Γ`, the pole and the positions `log n` enter. The global intersection is `{Λ}` under RH and empty otherwise
  [L: RHTower]; on each `𝒜(c)` the coordinates are pinned at rate `e^{−c/1104}` [L: CHT].
- **Every bounded aperture is blind to every width.** For every `a` and `δ ∈ (0, ½]` the off-line lattice
  `{½ ± δ + πik/a}` has width `δ` and a nonnegative form at aperture `a` [L: SRT].
- **Deciding inputs** must pass the four filters of 1.13 and be locally pure [L: ASRP, APR].
- **The cone pins its coordinates while its margin collapses [N].**

| `c` | weights seen | margin of `Λ` | best margin over all weights | band width of `λ(2)` | band width of `λ(3)` |
|---|---|---|---|---|---|
| `0.40` | `2` | `1.8×10⁻⁴` | `6.1×10⁻⁴` | `0.19` | — |
| `0.45` | `2` | `1.6×10⁻⁵` | `1.4×10⁻⁴` | `1.5×10⁻²` | — |
| `0.50` | `2` | `9.4×10⁻⁷` | `1.4×10⁻⁵` | `8.9×10⁻⁴` | — |
| `½log 3` | `2` | `5.6×10⁻⁸` | `1.3×10⁻⁶` | `5.8×10⁻⁵` | — |
| `0.58` | `2, 3` | `6.9×10⁻⁹` | `5.0×10⁻⁷` | `2.4×10⁻⁵` | `0.17` |
| `0.62` | `2, 3` | `4.0×10⁻¹⁰` | `6.7×10⁻⁸` | `3.0×10⁻⁶` | `4.2×10⁻³` |
| `0.66` | `2, 3` | `1.6×10⁻¹¹` | `7.7×10⁻⁹` | `5.4×10⁻⁷` | `2.4×10⁻⁴` |

  Finite Galerkin observations on Legendre polynomials of degree `<36`, double precision; bands are outer
  approximations. Neither roundoff nor the omitted infinite-dimensional complement is certified. Positive
  Galerkin margins do not establish full-space positivity. Formal facts are the pinning and margin bounds above.

### 1.20 Constructed criteria and remaining source gaps

| Route | Established source/receiver [L] | Exact open input |
|---|---|---|
| ZCG | Actual half-Gauss collision criterion ⇔ RH; large-height sub-Weyl horizon | Smaller positive times and low-height compact region |
| PTR | Actual cosine-shift source and sech handoff; strict Laguerre sign for `h≥½` | `A_h′²−A_hA_h″>0` for every `0<h<½`, real `x`; independent photonic realization is a separate producer |
| SEC | Actual time-one seam admitted and transform identified | For fixed `x₀>1`, each ξ-zero `ρ` has a bound `C_ρ` for all partial Fock jet sums; no uniformity in `ρ` required |
| ACS | Exact source cone, all-aperture RR and literal critical-deficit energy | Nonnegative energy for all real compact tests at every radius; independent count/Rosati producer still missing |
| CDC/BSH | Actual potential, Euler metric, curvature identification and calibration | Proof-erasure equality at ξ-zeros already suffices; full semantic descent is stronger |
| PCS | Actual co-shift, ground profile, reflection-odd quotient; vanishing ⇔ RH | `n ↦ n^(−ρ)−n^(−(1−conj ρ))` in `ℓ²` for every ξ-zero; independent differential lift missing |
| PA/HJ | Continued prime−Gamma paired source; exterior scalar-diagonal receiver | Diagonal nonnegativity on the specified regular-point exterior sector |
| RN | Positive cone-preserving operator gives determinant `D`, not Ξ; exact two-ended combination | Exclude joint energy/cross-flux nodes in `0<x<¼,y>0`; `D` itself has infinitely many nonreal zeros |
| SZ | Coefficient-faithful Abel source and signed compensation assembled | Bound the actual residual; assembly is not the remaining gap |
| BAG | Actual flow/torus target transfer | Cutoff-uniform positive lower bound for head-target Haar mass |
| GTA | Actual quartic charge and strong finite-stage convergence | Compact full-mode/operator-norm convergence; ordinary skew-adjoint positive-energy producer is refuted |
| APF | Real-Ξ spectral labels reconstructed | Full-divisor exhaustion and RH landing |
| EGC | Fixed-rectangle double-Gaussian pair sum and inner contour limit | Global height-fibre isolation and outer RH landing |
| EWJ | All-depth reporter and norm-exhaustion criterion | Faithful producer bypassing the identified transverse/endpoint essential gaps |
| FEL | BSY sign criterion already belongs to live CTF | Independent theta-history producer |
| IRK | Finite free resolution, not projective realization | Analytic trace/Chern source identifications |
| MSC | Critical unweighted discrepancy admitted in `L²` | Signed Sonin/Weil landing |
| RFHM | Source admission and strong creation exhaustion | Specified arithmetic orientation law and landing |
| W1C | Abstract Lee–Yang receiver | Source-faithful centered graph producer; convergence on one real interval suffices |
| WBF | Generic Gram magnitude/phase-gauge reconstruction | Arithmetic certificate and Ξ landing |

## 2.1 Auxiliary tasks; difficulty not certified

| # | Task | Routes served | Available basis / limitation |
|---|---|---|---|
| A1 | Explicit constants and horizons (`K₀`, eighth-root theorem, `1/9`, logarithmic profile, Beurling schedule, `M(N) = o(c_N)`) | HF, SRT, AIP, ACS, SC | effectivization of proved limits |
| A2 | General profiles past `θ = 1/1080` | HF, SRT, SC | tilted-spline template |
| A4 | Certified ratio interval at its size-only optimum; receiving complement inside it | HF, AIP, SRT, CSAR | assembly of proved estimates (difficulty unverified) |
| A5 | Rigorous two-weight membership beyond proved tower stages, odd unit window first | RW, OWU, EWU, ACT, SWC, HF | explicit operator inequality; numerical margins are not certificates; finite-window gain supplies no automatic all-aperture propagation |
| A6 | Exact Tate horizons of the remaining stages below spread `6` | WTZ, CWS | finite templates exist there |
| A7 | Closed form of the first-stage complement `Φ_ε` | GWZ, CSTW, WTZ, RW | explicit Schur complement |
| A9 | Literal channel norms critically small with growing periods, offsets, prime bands | AIP | proved sieve inputs (difficulty unverified) |
| A11 | Function-field calibration of the remaining receivers (ladders, Hardy intervals, de Branges chains of curves, finite purity certificates) | AHD, ACS, SC, HF | the sign is known there |
| A13 | Widths of the finite-level cones `𝒜(c)` beyond `c = 0.66` | PBAP, ACS, RW, FADF, CHT | convex finite programs; entry bounds and the pinning rate proved |
| A14 | PM physical mixed-parameter realization/descent; Mayer compatibility and boundary carrier | PM, W1C | coefficient-space Krein completion closed; physical identification is not routine by theorem |
| A15 | Operator-native nonvanishing on `Re w = 1` | PM | Eisenstein template (risk: reduces to the Euler product) |
| A17 | Tenth signed centre-mixed full-theta Hankel section at every `0 < a < ½` | TH | rank 9 closed; first-atom/all-rank paper or partial Bessel modules do not prove the full-theta tail allocation |
| A18 | Jensen horizons, two-grid degrees, PF beyond 45 at the centre, the slice band beyond `\|t\| ≤ 709/50` | PA, LA, HCF | effectivization and finite computation |
| A19 | Certificates on the nine anti-diagonals `{2,3,4,5,7,8,9,11,13}` where the pole pays nowhere | ACT | finite case analysis |
| A20 | Mixed Schur debit; first-prime/coarse/polar costs | AIP, CHMD | fixed-dimensional estimates |
| A21 | Logarithmic two-point Chowla | MC | Tao's theorem |
| A23 | Depth law, star horizons, gcd strata | HF, ACS | effectivization |
| A24 | Census items; Voronoi; Zwegers | census, ACS, HF | classical |
| A25 | Künneth primitive `h¹` at small degree; mixed jets | ACS, WL | calibration |
| A28 | Atomic-lattice bound `λ_max ≤ ½log N` | WTZ, HF | classical |
| A31 | Selberg-class degree-one classification | ACS, SEL | known theorem |
| A33 | Lévy sector margins at `c = ½log 3` | RW, OWU, EWU, SWC | numerical |
| A35 | Sharpen the explicit constants (`2²⁶·960`; detector `480000`, `10⁶`, count `240`) toward `4δL/k` | WVL, every P1 route | explicit test functions and counts in place |
| A36 | Remaining onset-law items (general shallow depth-mass bound under positivity; tapered crystal to `a ≍ log T`; interferometer) | WVL | paper items |
| A38 | Sub-Weyl strip profile from the best exponent pairs (horizon toward `½`) | LA, ZCG | known subconvexity; decides nothing about zeros |
| A43 | Identify the tower limit `a_∞` (closed form or bounds for the series of dilation steps); decide whether a finite stage passes `½log 3` | RW, AIP, HF | explicit recursion in place |
| A44 | Height law of `N_d`: which off-line zeros are counted at degree `d` (outlier positions `x ≈ d/γ` in the saddle identity); explicit constants in `N_d ≤ 300√(d log d)` and in the Cauchy limit | LA, FFP | reading of a proved saddle identity |
| A45 | Constants of the sharp-location theorem (`zetaNegativeCameraHeight`, the exponent in `e^{−c log³T}`) | ZCG, SRT | explicit cameras in place |

## 2.2 Open mathematical obstacles

### Σ — critical sign
| # | Problem | Strength | Routes |
|---|---|---|---|
| B1 | Weil's sign on every window (≡ `1 ∈ ℋ(c)` ∀c ≡ `λ*(c) → 0` ≡ band on reflection pairs ≡ growth steps contractions ≡ Li positivity ≡ Suzuki first variation ≡ two-parameter two-bump family) | RH; fixed length sub | all sign routes |
| B2 | Kick admission at every stage (≡ single-prime stage transport) | RH as induction; each stage sub | RW, GWZ, CSTW, WTZ, HF |
| B3 | The two-sector signed certificate inequalities on every window (`2V ≤ J_{M⁺}`; odd shifted-ground-state form) | RH; fixed length sub | P1 routes |
| B4 | Odd unit window (`w₂ ∈ unitBandWeights`) by a structural certificate | sub; finite window | OWU, RW, TT, SWC |
| B5 | Below `log 4` (`a*(ζ) ≥ log 2`), the prime `3` paid by sign | sub; finite window, no door (2.8) | RW, OWU, EWU, ACT, TT, SWC, HF, ACS |
| B56 | Below `log 5` (`a*(ζ) ≥ ½log 5`): the `{2,3,4}` sliver band | sub; finite window | same as B5 |
| B6 | Twisted-sector positivity through all conductors and frequencies | sub | HF, SRT, AIP, AHD |
| B7 | Full-space sign at critical ratios beyond the size-only threshold | sub per ratio; RH all | HF, SRT, AIP, CSAR |
| B8 | General profiles past `log log N` on the full space | sub | HF, SRT, AIP, SC |
| B9 | Exact SOS on the complete prescribed two-prime lattice test family | RH | HF, SC, ACS |
| B10 | No zero mode at any length | RH | HF, TG, SC, EHT, GWZ |
| B11 | Top coprime stratum | RH | HF, ACS, ADT |
| B12 | Index ceiling uniform in resolution | ≥qRH; RH (tensor) | CHMD, SRT, WD, SC |
| B13 | Exclude finite nonzero off-line support (`κ ∈ {0, ∞}`); separate from proving `N_d` bounded | proposed rigidity input | SC, HF, ACS, CWS, SRT, LA |
| B14 | Exclude every positive-time collision of the actual half-Gauss source; both small-time and compact-height regions remain | RH | ZCG; related TH, LA, HCF, PA, GTA, XN criteria |
| B15 | Complete scheduled prime energies bounded below | RH for constructed receivers | FU, CFC, RP; EGC/FEL still lack independent landing/producer |
| B16 | Window negativity exponent `< ½` | ≥qRH | window routes, HF, WD |
| B33 | HF-native sign: a window beyond the base certified by the complete family itself | sub; finite window | HF |
| B55 | Head-window thresholds `windowThreshold(log d) = ⊤` for every `d` (`d = 3` needs `a*(ζ) ≥ ½log 3 + ε`) | RH | HF, AHD |
| B49 | Signed ground-state structure past `log ρ` compatible with unswitchable frustration | method | EWU, OWU, RW, ACT, SWC, FADF |
| B51 | Contact-excluding arithmetic kernel bound; kernel absolute continuity and boundary-flux/support variation are intermediate problems | no contact ⇔ RH; density inequality alone insufficient | RW, CSTW, CHT, SZ |
| B59 | Decay law of `λ*(c)` between the pinning rate `e^{−c/1104}` and the doubly exponential ceiling | sub | PBAP, FADF, CHT, RW |
| B66 | All ranks `≥ 10` of the signed centre-mixed theta Hankel sections at every `0 < a < ½` | sub per rank; RH all | TH |
| B67 | Hausdorff rows nonnegative on `r < H(k)` for every `k` | RH (all rows) | PA |
| B68 | Every finite-degree pole-annihilating two-grid heat functional nonnegative for fixed admissible offsets | RH (all degrees) | HCF |

### Π — precision and production
| # | Problem | Strength | Routes |
|---|---|---|---|
| B19 | Inner caps at every polynomial stage (≡ the off-line generating function is `L²(e^{−xt})` at every stage) | RH; fixed degree ≥qRH | WD, TG |
| B20 | `100%` critical-scale clustering (≡ log-mean `→ 0` ≡ moment `→ 1` at length `exp(o(T))`, which forces `log N/log T → ∞`) | sub | WD, census, MC, HEF |
| B21 | `D_win` ≡ thin Planck shadows; `D_zero`; needs depth decay at rate `≍ log log V`; sufficient: an actual-zero detector with shifted defect `≤ Ce^{−r(σ−½)log V}V/log V` | sub | WD, census |
| B64 | A complex mollifier family with excess `≤ K₀/log T` at length `exp(c log²T)`, `c ≥ 1/(6K₀)` (⇒ `D_zero ∧ D_win`) | sub | WD, MC, CTF |
| B65 | Cofinal boundedness `∫_1^T\|ζM\|² ≤ C_θT^K` with prefix cancellation `X₁ ≥ T^{3θ/4}` for arbitrarily large `θ` (⇒ RH) | RH | WD |
| B22 | Hecke defect pointwise / dyadic | ≥qRH / RH | WD |
| B23 | Distributional input beyond counts and moments | method | WD, HEF |
| B24 | Genus upper law | indep. | ACS |
| B25 | Logarithmic Serre duality, primitive part | sub | ACS, HF |
| B26 | `ε`-uniform producer; square-root source input (locally pure, parity-breaking, unbounded length) | sub / RH | WL, MC, PBM, RB, JAS, CTF |
| B27 | First cyclotomic mode at square-root precision | RH | MC, WL |
| B28 | Signed pair information beyond bandwidth one | sub | census, ACS |
| B29 | First Epstein real zero on the boost line | sub | ACS |
| B30 | Bounded damped cone coupling; unattained width | RH | SC, ACS |
| B31 | Finite-sieve Hodge positivity → global | RH | SC |
| B32 | Half-power law at the trivial gauge point | RH | MC, WL |
| B52 | Möbius-mollified Jensen stability at infinitely many degrees (≡ `N_d = 0` for infinitely many `d`) | RH | LA, FFP |
| B53 | A source-faithful stable finite free factorization of `J^{d,n}` other than Γ ⊠ Θ | method | FFP, TH |
| B62 | `N_d` bounded (≡ finite off-line support) | ≥qRH | LA, FFP |
| B57 | Self-improvement of a strip: `Θ < 1 ⇒ Θ = ½` (no mechanism; false for shifted products; Hadamard and tensor powers carry RH) | sub | whole programme |

### Γ — selection and reflection
| # | Problem | Strength | Routes |
|---|---|---|---|
| B34 | Rosati positivity of the window reflection | RH | HF, ACS, CWS, GWZ, PM |
| B35 | Band holomorphy of `Λ(s)/Λ(s+1)` | RH | HF, ACS, SC, PM |
| B36 | Selection at the trivial gauge point | RH | MC, BAG |
| B37 | FE twins inside the full class with off-line zeros | sub | HF, ACS, SC, SEL |
| B38 | Independent nonnegativity of weighted `D_s(ψ_s)` at upper resonances, or full Krein positivity | RH receiver | PM; W1C needs its own producer |
| B39 | Resonant-state statistic selecting the decay rate | method | PM |
| B40 | Independent positive physical/graph realization of the specified source | producer problem | PM, W1C; RN/PTR already have analytic receivers |
| B41 | Actual source sign/vanishing, versus missing source landing | RH for live criteria; missing landing for candidates | live CDC/BSH, PA/HJ, PCS, SEC; candidates APF, EWJ, RFHM, WBF |
| B42 | Prime-blind positivity on signed blind combinations | RH | PBAP |
| B44 | Nonnegative squared gap for every actual FE pair; camera realization retains isolation/readout hypotheses | RH when every pair is covered; small-value converse not supplied | ZCG, ADO |
| B45 | Cross-tower gap through the archimedean channel | method | HF, AIP |
| B46 | PM-native zero-free region for `ζ(2s)` (route test) | sub | PM |
| B54 | `0 ∉ E`: polynomial repulsion of distinct zeros of ζ (open under RH; a.e. value has it; no implication for real parts; no route depends on it) | indep. | ADO, ZCG |

### Settled questions (status-quo answers)
| Question | Answer | Anchor |
|---|---|---|
| Is Weil positivity a Hardy inequality? | yes: `H ≥ P` on every window; only the multiple `1` admissible; critical; optimal ⇔ RH | FADF [L] |
| Is the Weil cone effectively unique? | yes: `\|λ(n) − Λ(n)\| ≤ Ce^{Kn−c/1104}` on `𝒜(c)` | CHT [L] |
| Does the best margin decay? | yes, doubly exponentially, over all weights; RH ⇔ `λ*(c) → 0`; the exact rate is open | CHT [L] |
| Is the datum of ζ special? | yes: the critical point of the `(β, s)` family; critical log-conductor `= −λ*(c)` | CHT [L] |
| Can the specified frustration be switched away? | no for even kernels past `log ρ` or acting odd prime reflections; global admitted weights eventually have odd frustration | FADF, CHT [L] |
| Where does size payment end? | before half-width `21/40`; edge law at `c* ∈ (½log5, ½log6]` | FADF, SWC [L] |
| Is the certificate format exact on every window? | yes: neutral signed theta gauge (even), shifted ground state (odd) | SWC [L] |
| What do the trivial zeros cost? | nothing: centre killing pays them | FADF [L] |
| Is the window tower a canonical system? | a de Branges chain before contact with a Hamiltonian density; contact is the first singular length | CSTW, CHT [L] |
| Does window positivity reduce to finite matrices? | for correlation forms yes, via rational Hecke graphs; finite templates end at spread 6 | WTZ [L] |
| Can the camera read squared gaps at polynomial scale? | yes, from three prime-side images | ZCG [L] |
| Does positivity at the camera aperture locate the zeros? | yes: depth `< e^{−c log³T}` at aperture `λL_T`, `λ > 1` (a receiver) | ZCG [L] |
| Does the camera count atoms? | no: it bounds weighted mass; one flat image carries arbitrarily many atoms | ZCG [L] |
| What does pair reality detect? | All actual FE-pair squared gaps nonnegative ⇔ RH; off-line pairs force small line values, not conversely | ZCG, ADO [L] |
| What does the Jensen count establish? | `sup_d N_d` equals total off-line multiplicity; eventually `N_d ≤ 300√(d log d)`; neither bound proves finite support | FFP [L] |
| Is `ξ` stable on any line? | no margin on any line; zero-free `Re s > σ` ⇔ stability of `ξ(σ + i·)`; `c = 0` critical | FFP [L] |
| Does PM's second expression change the sign? | no: same `(b^{2σ−½} − b^{−(2σ−½)})²` factor | RIT [L] |
| What is WD's inner cap? | the generating function of the off-line zeros | CDG [L] |
| Are SZ and LI independent of Weil positivity? | no | RHTower, ALG [L] |
| Does HF transport one prime? | single-prime transport for all `A` ⇔ RH; unconditional across `p = 2` | AHD [L] |
| Can non-orthogonal twists repair untwisted negativity? | Dirichlet shifts cancel tails, leave the head `windowThreshold(log d)`; `d = 2` done | AHD [L] |
| Do joint twist families inherit positivity? | eventually PD at every critical multiple iff jointly independent | AHD [L] |
| How far is the three-power reduction exact? | Full window width `2c<log 5`: the `{2,3,4}` sliver band, still an operator inequality | SWC [L] |
| Is the excluded-depth law effective? | yes: `10⁶exp(−a/(480000 log(\|γ\|+3)))` at level `a`; `e^{−c log³T}` at `λL_T` | SquareRootThreshold, ZCG [L] |
| Does finite-window positivity alone determine width in the configuration class? | no: every width has finite-window positive mimics | SRT [L] |
| Do polynomial mollifiers reach clustering? | no: second moment `≥ (1 + 1/(8+6θ))T`; moment `→ 1` forces `log N/log T → ∞` | APR, CDG [L] |
| What length does the stated excess need? | `log N ≥ log²T/(6K₀) − (4/3)log T` in the theorem's regime; attainability unproved | CDG [L] |
| Does the critical-line proportion decide the ladder? | proportion `→ 1` ⇒ clustering; neither proportion nor any exponential depth rate ⇒ `D_win` | CDG [L] |
| What detector gives `D_win`? | shifted `L²` defect `≤ Ce^{−r(σ−½)log V}V/log V`; the scale is sharp | CDG [L] |
| Which inputs can decide the count? | parity-breaking, locally pure, precision-faithful, unbounded aperture and length; Type I/II, Mertens, PNT, impure-stable bounds cannot | ASRP, APR [L] |
| Is purity over `𝔽_q` a deformation argument? | no: `collide_or_repel` assumes the disc bound; integer families are constant; impurity is quantized and certified by finitely many power sums | ZCG, ADO [L] |
| Do ζ's zeros repel? | a.e. value of ζ repels polynomially; `0 ∈ E` undecided; finite Euler and integral pure carriers repel by Baker | ADO [L] |
| Is the theta cusp positive at rank 9? | yes, at every `0 < a < ½`; the complete fifth even tail is PD at every cutoff | TCS [L] |
| Is every fixed Jensen degree eventually real-rooted? | yes, beyond an explicit shift horizon | RHTower [L] |
| Are the centre jets positive? | PF₄₅ at the centre; all slice coefficients nonnegative for `\|t\| ≤ 709/50` | RHTower [L] |

## 2.3 Frankenstein routes

**No assembled RH proof.** F6 is a proved conditional receiver. F7 has a Hamiltonian density and fixed-aperture
boundary limits, but still needs variation estimates and contact-excluding arithmetic control. F11–F13 retain their
stated source estimates. Global RH equivalence does not establish a constructive identification between mechanisms.

### F1. The gauge–tower assembly (P1)
| Segment | Supplied by | Status |
|---|---|---|
| RH ⇔ `1 ∈ ℋ(c)` ∀c ⇔ reflection pairs ⇔ two sectors ⇔ `λ*(c) → 0` | WVL, FADF, SWC, CHT | [L] |
| Exact two-sector format on every window; gauge freedom only in the pole direction | SWC | [L] |
| Floors to `a_∞` on windows and reflection pairs; exact `{2,3,4}` problem below `log 5` | AIP, SWC | [L] |
| Perron to `log ρ`; trivial zeros at the centre; entry law; cone pinned | SWC, FADF, CHT | [L] |
| Core: `2V ≤ J_{M⁺}` and the odd ground-state inequality on every window | — | B3; first instances B4, B5 |

### F2. Hardy induction (FADF ⊕ AHD ⊕ CSTW)
`1 ∈ ℋ(c)` is antitone; composite stages carry no fold; each prime-power entry is a compact interval in the newest
weight with sharp logarithmic softness; single-prime transport for all `A` ⇔ RH [L]. Residual: a margin at every
entry. Criticality forbids uniform margins (no Hardy weight; `λ*` doubly exponentially small), and the first-fold stage
loan fails at `21/20` [L]. This excludes that loan mechanism, not every aperture-dependent signed estimate. B2.

### F3. The complete-family assembly = the onset aperture
Subcritical PD + one critical multiple across all entries + threshold law + terminal polar source + receiving charges
[L]; orthogonal twists cannot repair untwisted modes [L]; Dirichlet-shift companions cancel every tail and reduce each
long window to its head `windowThreshold(log d)`, unconditional for `d = 2` [L]; joint periodic windows PD iff
independent [L]. Certifies exactly what the base certifies. Residual: B55 (the head for `d = 3` is the window
`a*(ζ) ≥ ½log 3 + ε`; `a₀ ≈ 0.362`, tower limit unknown), B33, B1.

### F4. The reflection assembly (P3)
Coefficient-space Krein completion + window lift + weighted defect formula in two coordinate systems [L]. Residual:
physical mixed-parameter realization/descent and B38; both defect expressions retain the nonnegative squared factor.

### F5. The camera–continuation assembly (ZCG ⊕ heat ⊕ ADO)
| Segment | Supplied by | Status |
|---|---|---|
| Heat path real for `t ≥ 1/8`; RH ⇔ no collision at any positive time (`t=0` simplicity not asserted) | RHTower, ZCG | [L] |
| No collision above `(6600/9991 + ε)/log X`; saddle `½/log X` | ZCG | [L] |
| Collisions are near-coincidences; identification to `e^{−c log³T}`; `𝓗` reads `w²` at polynomial scale | ZCG | [L] |
| Near-coincidence ⇒ joint small values under local bounds; uniform separation transports reality with its real-path hypotheses | ADO | [L] |
| Core: exclude `Re Q(0)=Im Q′(0)=0` at all remaining positive times and heights. Uniform heat-path repulsion is a possible sufficient input; repulsion of ζ's zeros alone is not | — | B14; B44 requires its cluster hypotheses; B54 is not the missing collision estimate |

### F6. The sharp location assembly (SRT ⊕ RHTower ⊕ ZCG) — a theorem
Positivity at aperture `λ·log(T/2π)/2`, `λ > 1`, at heights `T ≥ zetaNegativeCameraHeight` ⇒ every zero of ζ at height
`T` has depth `< exp(−c log³(T/2π))` [L: ZCG SharpLocation]. The assembly is closed: two normalized convolution cameras
at the cluster and its reflection make `Re W(f−g, f−g) < 0` without any on-line mimic or separation premise. Output: a
receiver that produces no sign and is vacuous at known apertures. The converse (RH below `T` ⇒ positivity at `½log T`)
is blocked by doubly-exponential non-locality, so height induction stays closed.

### F7. The canonical-system assembly (CSTW ⊕ CHT ⊕ GWZ ⊕ SWC)
De Branges chain before contact + lattice Levinson recursion + continuum jet limits + parity split + Hamiltonian density
`0 ≤ ∫G′ ≤ ΔG` of the evaluation Gram [L]. Actual fixed-aperture endpoint traces and complete collar limits are
closed; finite contact forces diagonal kernel blow-up. Residual: B51—contact-excluding arithmetic kernel bounds,
absolute continuity and support variation. No identification `ΔG=∫G′` follows from the density inequality alone.

### F8. Finite free ⊕ Euler carriers ⊕ Baker (FFP ⊕ ZCG ⊕ ADO)
Normalized Euler products HB-stable with drift `θ_S/2` ≡ the carrier horizon `2πe^{θ_S}`; finite Euler carriers and
integral pure carriers repel polynomially by Baker; the Euler product's only consistent Bohr tangency is `(1,1)` at
`σ = 0` [L]. Residual: the same domination is shared by every finite real carrier and twins are tilted at every height
[L]; the Euler product diverges in the strip, so no finite carrier converges to `Ξ`; the mollified criterion is a
receiver (B52).

### F9. Finite Hecke graphs ⊕ numerics (WTZ ⊕ A5)
Correlation-form windows are finite matrices below spread 6 [L]; certify `a*` numerically there. Residual: Weil's form
carries the archimedean Lévy part, not a correlation form; margins `10⁻⁵`–`10⁻⁸`; windows below half-width 4 carry no
zero information.

### F10. Visibility–density (WVL ⊕ WD ⊕ DCI)
Unshielded clusters excluded to doubly-exponential height; shallow depth mass bounded; inner caps = off-line generating
function [L]. Residual: B1 at growing aperture and B21 (log-free occupancy).

### F11. Count ⊕ camera (FFP ⊕ ZCG)
`sup_d N_d` equals total off-line multiplicity, with eventual `N_d ≤ 300√(d log d)`; the camera bounds depth by
`e^{−c log³T}` under positivity at `λL_T` [L]. Arbitrarily shallow off-line zeros are not thereby excluded, and a
height-local depth bound is not a zero value of `N_d`. Residual: B52; B62 yields only finite off-line support.

### F12. Heads ⊕ tower (AHD ⊕ AIP ⊕ SWC)
Dirichlet-shift stabilization for `d = 2` is unconditional because `log 2 < 2a₀` [L]; for `d = 3` it needs
`windowThreshold(log 3 + ε) = ⊤`, i.e. half-width `(log 3 + ε)/2`, above the tower start `a₀ ≈ 0.362`;
below `log 5` that window is the `{2,3,4}` sliver band [L]. Residual: a finite window (A5 numerics or B5/B56
structure), which decides the prime-3 head and nothing beyond it.

### F13. Mollifier ⊕ detector (APR ⊕ CDG ⊕ WD)
Any complex normalized mollifier family with excess `≤ K₀/log T` at length `exp(c log²T)` gives `D_zero` and `D_win`;
any holomorphic actual-zero detector with shifted defect `≤ Ce^{−r(σ−½)log V}V/log V` gives `D_win`; the length and
detector-scale obstruction and necessary length law are proved [L]. Residual: B64—the actual moment bound;
fixed polynomial length cannot yield moment `→1` in the stated coefficient class. The lower length bound does not
prove an attainable optimum.

## 2.4 A wildly different route

Σ/Π/Γ organize current obstacles; they are not a theorem classifying every possible RH proof. The corpus has live
analytic routes outside the window-sign presentation, including ZCG, PTR, SEC, CDC and PCS. Their concrete receivers
are established; none has its decisive arithmetic input discharged. A distinct producer must be assessed on its
actual source and landing, not rejected merely because its conclusion is equivalent to RH.

**Integrality alone does not force purity.** Over `𝔽_q` purity mechanisms include Weil's Hodge index,
Stepanov–Bombieri's point count, Deligne's positivity on tensor powers. `collide_or_repel` [L] takes the disc bound as a
hypothesis; integer polynomials do not deform continuously (a continuous integer family is constant [L]); integrality
quantizes impurity and does not exclude it (`X^{g−1}(X − m)` is monic, integral, impure [L]); given integrality,
finitely many power sums certify purity, at orders growing like `(q/9)^{1/4}` [L]. These examples exclude integrality
alone, not an additional arithmetic sign or count law.

**Tensor amplification is closed.** Every Hadamard power `K_ζ^n` is positive definite iff RH [L].

**Possible input to ZCG: a small-value inequality along the heat path.** The small-value dictionary
turns reality into a small-value statement: an FE pair at depth `δ` forces `|ζ(½+iγ)| ≤ 480e²(|γ|+2)(|γ|+5)δ²` and a
near-coincidence forces joint small values of ζ and ζ′ under local bounds [L: ADO]. An independent lower bound
could therefore help exclude such pairs; an exact converse or a sufficient bound is not supplied here. In the same
spirit, polynomial repulsion of ζ's zeros is `0 ∉ E` [L/D]. The corpus's Baker–Matveev inputs concern algebraic data
and finite-rank frequency modules; they do not supply the required actual heat-path estimate. Two further
facts bound this direction: `0 ∉ E` has no implication for real parts (FE pairs are separated by `2δ`), so a
small-value route must address the heat path (`H_t`, `t ∈ (0, ½/log X]`), where uniform polynomial repulsion would
transport reality [L: ADO `splits_of_uniform_repulsion`] and give RH; and the only proved repulsion for ζ is in the
value `a`, not along the flow. This is an unconstructed producer for live ZCG, not grounds to demote its collision criterion.

## 2.5 Breakthrough questions below RH and quasi-RH

### Validity tests

A question stands in 2.5, 2.6 or 2.8 only if it passes these tests.

| Test | Requirement | Anchor |
|---|---|---|
| T1 Not RH | Not equivalent to RH. In 2.5 also: implied by RH, and not implying quasi-RH | equivalence web |
| T2 Decision | Answered only by a proof or a refutation of the stated inequality. Identity + obstruction + equivalence with RH is no answer | — |
| T3 Written consequence | YES ⇒ a named statement, by an argument that can be written down | — |
| T4 Aperture | Anything claimed to lead to RH is not determined by a finite window | `not_of_finite_window`, `exists_configWidth_eq_and_weil_nonneg_on_aperture` [L] |
| T5 Mimics | False on at least one corpus fake: off-line lattices, Liouville twin, `Λ + εn^{−η}`, Davenport–Heilbronn, `ζ(s)ζ(s−ε)`, `ξ(s+a)ξ(s−a)`, `ζ(s)(1 − cp^{−s})` | `deciding_input_necessary_properties`, APR filters [L] |
| T6 Mechanism | Names an input not refuted by a Lean no-go | — |
| T7 Shape | Not a shape answered in Lean without moving a wall (table below) | — |

| Shape | Lean output | Walls moved |
|---|---|---|
| Construct the object whose regularity is RH | de Branges chain, Hamiltonian density, contact blow-up (CSTW, CHT) | none: B51 is RH |
| Express the sign in another coordinate | two weighted defect expressions (RIT); gauges (SWC); inner cap (CDG); pair discriminant (ZCG); `λ*(c) → 0` (CHT); cofinal `N_d = 0` (FFP) | source criterion closed; independent estimate still needed |
| Read a quantity at a finer scale | polynomial-scale readout; sharp location at `λL_T` (ZCG) | none: B44 is RH; location needs positivity |
| Pin the weights or the datum | pinning rate `e^{−c/1104}`; margin ceiling; datum critical (CHT) | none: the sign of `λ*` is B1 |
| Count the failures | `sup_d N_d` = off-line count; `N_d ≤ 300√(d log d)` (FFP) | none: `N_d = 0` is RH |
| Transport across one step | single-prime transport ⇔ RH; heads for every `d` ⇔ RH (AHD) | none |
| First window beyond a base | increasing floor tower (AIP) | no automatic all-aperture propagation; limit unknown |
| Second expression + "any nonnegative one is RH" | `mayerDefect_nonneg_representation_iff` (RIT) | none |
| Necessary conditions on a producer | entry filters; necessary-length laws (ASRP, APR, CDG) | none: they exclude, they do not construct |

The proved receivers do not discharge `D_win`, all-aperture positivity or the proposed long-mollifier moment bound.
Sub-RH research targets below use separate selection tests; failing those tests does not invalidate a live RH route.

**Audit of the question forms that fail.**

| Question form | Fails | Reason |
|---|---|---|
| Sign ⇒ location at `a = λL_T` | T3 as a breakthrough | A theorem (F6) and a receiver; no sign is produced; vacuous at known apertures |
| Mayer defect size law with corridor `\|σ − ¼\| < c/log\|Im s\|` | T1, T6 | Above quasi-RH; the relations are `K_σ`-weighted equalities |
| `windowThreshold = ⊤` through stage 2 and `log 3` "from the complete family" | T4, T6 | `windowThreshold A = ⊤ ⇔ A/2 ≤ a*`; a finite window seeing one or two numbers |
| Collide or repel for ζ (`0 ∉ E`) as a step to RH | T1, T3 | Not implied by RH; FE pairs may be well separated; its model theorems assume the disc bound or a finite frequency module |
| Contact-excluding kernel bound | T1 | RH-strength target; absolute continuity alone is not identified with contact exclusion |
| Nonnegative expression of `D_s(ψ_s)` | T1, T2, T7 | `D_s ≤ 0` always, so such an expression is `D_s = 0` |
| Off-line generating function in `L²(e^{−xt})` | T1, T2 | Integrability at every `x` says the off-line set is empty |
| Single-prime transport; head thresholds for every `d`; head recursion over divisors | T1, T7 | Induction on an antitone threshold; base case RH |
| `𝓗 ≥ −B` on isolated clusters | T1, T6 | `𝓗` is the squared gap by theorem |
| `a*(ζ) ≥ log 2` or `≥ ½log 3 + ε` as a door | T4, T5, T6 | 2.8 |
| Effective uniqueness of the cone; margin law | T7 | Answered in Lean (CHT); the sign of `λ*` is untouched |
| `N_d` bounded as a 2.5 question | T1 | Finite off-line support implies Lindelöf and a zero-free half-plane (above quasi-RH) |
| A sublinear bound on `N_d` alone | T3 for zero extinction | Existing `O(√(d log d))` allows infinitely many off-line zeros; uniform boundedness gives finite support, eventual zero gives RH |
| Replacement for Allegretto–Piepenbrink; SOS on the pole-neutral hyperplane; balanced signed ground state | T2, T6 | A positive form has an exact certificate by definition |
| Stability preserver containing Euler factors and the Gamma phase | T3, T6 | No finite carrier converges to `Ξ`; ζ, Gamma and pole pieces are unstable |
| Deformation from a pure object with integral structure | T3, T6 | 2.4 |
| Polynomial-length mollifier with moment `→ 1` or excess `o(1/log T)` | T6 | Excluded by the necessary-length laws |
| Proportion one or a depth-tail rate as a route to `D_win` | T6 | The root model satisfies both and fails `D_win` |

The sections below keep only what passes.

### 2.5.1 Whole programme — `100%` critical-scale clustering
**Question.** Prove `T⁻¹∫_T^{2T} log|ζ(½ + it)| dt → 0`; equivalently, for every `κ > 0`, all but `o(T log T)` zeros in
`(T, 2T]` lie within `κ/log T` of the line. Eight forms are equivalent, among them the truncated Euler-mollified log
mean, the linear-mollifier law and the dyadic horizontal moment `o(T)` [L: `criticalClustering_logMean_mollifier_hecke_tfae`]
(B20).
- **T1.** Implied by RH; implied by the critical-line proportion `N₀(T)/N(T) → 1` [L]; allows sparse off-line zeros at
  every depth, so it implies neither RH nor quasi-RH.
- **T2.** Selberg's tail moment gives `Σ(β − ½) ≪ T` [L]; the question is `o(T)`, and no identity delivers it.
- **T3.** `Σ_{T<γ≤2T}(β − ½) = o(T)`: RH on average at the mean-spacing scale.
- **T5.** False for Davenport–Heilbronn, off-line lattices of bounded spacing, `ζ(s)ζ(s−ε)` and `ζ(s)(1 − cp^{−s})`
  (log-mean `→ log(c/√p) > 0` [L]): a proof must use the Euler product inside the strip and local purity.
- **T6.** By Jensen and Littlewood it follows from a mollifier with second moment `→ 1`, which forces
  `log N/log T → ∞` [L]; the required actual long-moment bounds are not supplied.
- **Limit.** No door to RH: the sparse exceptions survive it. The stronger classical target, proportion `→ 1`, is also
  valid (T1–T5, T7) and has the same mechanism and the same limit.

### 2.5.2 Route PM — none
No breakthrough question passes. The defect relations are equalities with the same `K_σ`; a corridor at scale
`1/log|Im s|` is above quasi-RH. The valid item is a route test, not a breakthrough: B46, a zero-free region
`β < 1 − c/log|γ|` from the Lewis–Hecke carrier alone. Risk: its positivity is the Euler product (A15).

### 2.5.3 Route WD — log-free window occupancy
**Question.** `D_win`: for every `A`, at most `ε(A)V` unit windows of `[V, 2V]` contain a zero of depth `≥ A/log V`,
`ε(A) → 0` [L: CDG] (B21).
- **T1.** Implied by RH; sparse windows stay free, so no quasi-RH.
- **T2, T5.** A decision, false for Davenport–Heilbronn, `ζ(s)ζ(s−ε)` and impure factors (window occupancy fails on
  their zero lattices [L]).
- **T3.** `D_zero ⇔ D_win` + vanishing giant-cluster tails; `D_zero ⇒ D_win ∧` (2.5.1); `D_win ⇔` thin Planck shadows
  are rare [L].
- **Known obstructions.** The root model shows that critical-line proportion and fixed exponential
  depth-tail rate suffices; depth must decay at rate `≍ log log V` [L]. The sufficient detector shape is known and sharp
  (shifted `L²` defect `≤ Ce^{−r(σ−½)log V}V/log V`); the specified polynomial mollifier class cannot supply the required excess, Barban–Vehov reaches scale
  `V` and not `V/log V` [L]. The complex-coefficient rate `K₀/log T` at length `exp(c log²T)` would suffice (B64). No
  input is named.
- **Limit.** Valid open estimate; no off-line extinction follows from occupancy alone.

### 2.5.4 Route HF — none
`windowThreshold A = ⊤ ⇔ A/2 ≤ a*`, so an HF statement about a window is a window statement (B33). The prime-3 head
window is a finite window (A5). Joint periodic positivity is settled (PD ⇔ independence [L]).

### 2.5.5 Route TH — finite-rank frontier
Rank 9 is a theorem; rank 10 needs a uniform full-theta proof, not only a finite computation (A17); all ranks is RH (B66). No
statement strictly between a finite rank and RH is formulated by the corpus.

### 2.5.6 Route ZCG — the repulsion decision, not a step to RH
**Question.** `0 ∉ E`: distinct zeros of ζ at height `T` are `≥ T^{−C}` apart (B54).
- **T2, T3, T4, T5, T7 pass:** a decision; consequence: the value `0` is not exceptional, the zeros of ζ obey the law
  obeyed by a.e. value and by every integral pure carrier [L]; an unbounded-aperture statement; false for carriers with
  Liouville Satake angles and for `(1−2^{−s})(1−3^{−s})` [L].
- **T1 fails in one clause:** it is not implied by RH (open under RH), and it does not imply quasi-RH.
- **T6:** the only mechanism reaching ζ is the Diophantine one for finite frequency modules (Baker), which does not
  reach the infinite rank of `⊕ℤ log p`.
- **Bearing.** None on real parts; the repulsion needed by P5 is along the heat path, not at `t = 0` (F5). A real advance
  for the repulsion programme and for the understanding of `E`, not a step toward RH.
ZCG also has its live actual-source collision criterion (1.9); the remaining small-time and low-height estimates are
RH-level obstacles, distinct from this sub-RH repulsion question.

## 2.6 Breakthrough questions that open the path to RH

No verified factorization with a supplied new producer is recorded here. This section asks for `RH ⇔ Q ∧ R` with `Q`, `R` both strictly weaker
than RH and at least one of them reachable. Splitting counterexamples by depth or density always gives such a
factorization, so the content lies in a mechanism for one factor. The joint input must be parity-breaking, locally pure,
precision-faithful and of unbounded aperture and length [L]; PNT, Guth–Maynard, every error law weaker than square
root, Type I/II information, finite linear laws and every impure-stable upper bound are inherited by weights failing the
count [L]. So a door has to name an unconditional input at square-root precision or a long mollified second moment. The
corpus has none, and no question below names one.

### 2.6.1 Whole programme — none; the door-shaped statements have no mechanism
**B57, self-improvement.** `Θ < 1 ⇒ Θ = ½`; then `RH ⇔ (Θ < 1) ∧` B57 [D]. Passes T1–T5 (false for off-line lattices
and for `ξ(s+a)ξ(s−a)`, where `Θ_a = Θ + a` [L], so a proof must use degree one or the Ramanujan bound). Fails T6: the only
known self-improvement is Deligne's tensor-power step, closed on Weil's kernel [L].
**B62, finite off-line support (`N_d` bounded).** Then `RH ⇔ (N_d bounded) ∧ (no off-line zero given finitely many)`;
the second factor is RH-strength in every known form (one positive non-blind prime tower ⇔ RH [L]) and the first is
above quasi-RH. Not a door.
**B65, cofinal long-mollifier boundedness.** Implies RH outright [L]; it is RH-hard, not a door.

### 2.6.2 Route PM — none
`D_s ≤ 0` always, so a nonnegative expression is `D_s = 0`, which is RH [L].

### 2.6.3 Route WD — none
The RH-level statements (inner caps at every stage; cofinal long-mollifier bound) are emptiness of the off-line set or
RH in another form [L]. WD's valid content is below RH (2.5.1, 2.5.3) and its door-shaped item B64 lands on `D_win`, not
on RH.

### 2.6.4 Route HF — none
Transport across one prime is induction on an antitone threshold [L]. Dirichlet-shift companions reduce long windows to
head windows, and a head window is again a window (B55).

### 2.6.5 Route TH — none
All ranks is RH; no finite rank moves the wall.

### 2.6.6 Route ZCG — none
The actual positive-time half-Gauss collision criterion is live. Large-height times above the sub-Weyl horizon are
closed; smaller times and the compact low-height region remain. Camera discriminants and conditional sharp location
are supporting receivers, not the missing collision estimate.

## 2.7 Does closing RH need a new field?

No theorem here establishes that a new field is necessary. Two useful groupings organize part of the research;
they do not exhaust the live route mechanisms or prove one grouping cannot supply the decisive estimate.

### 2.7.1 Programme A — Critical Hardy theory of the window cone

| Established [L] | Open |
|---|---|
| Signed forms `W_λ=H−P_λ`; nested cones; global intersection `{Λ}` under RH, empty otherwise | Actual all-aperture sign |
| Coordinate pinning, doubly-exponential margin ceiling, critical datum | Margin law and certified aperture extension: B59, B3–B5, B56 |
| Precontact Hilbert/de Branges spaces, orthogonal increments, density inequality | Absolute continuity, boundary-flux/support variation, contact-excluding arithmetic bounds: B51 |
| Actual endpoint traces and fixed-aperture full-collar limits; logarithmic collar energy | Quantitative moving-endpoint/increment control and contact-uniform constants |
| Increasing floor tower from `a₀≈0.362` | Identify `a_∞` or prove aperture exhaustion: A43 |

Finite-aperture positivity alone does not select width in the general configuration class. This does not rule out
a new arithmetic argument proving all-aperture positivity. Numerical bands in 1.19 remain observations, not certificates.

### 2.7.2 Programme B — Arithmetic production at square-root precision

| Proven restriction / receiver [L] | Remaining input |
|---|---|
| Specified precision-blind, parity-blind and impure-factor-stable classes fail to force the count | Arithmetic estimate outside those classes |
| Fixed polynomial mollifier length has moment floor `1+1/(8+6θ)` in the stated coefficient regime | A moment tending to one requires superpolynomial length |
| Excess `K₀/log T` requires `log N≥log²T/(6K₀)−(4/3)log T` | Attainability is not proved |
| Actual moment `→1`, `log N=o(T)` ⇒ critical-scale clustering | B20: construct such bounds, or prove clustering by another mechanism |
| Actual excess `O(1/log T)`, `log N≤T/log T` ⇒ log-free occupancy/density | B64: construct the moment bound; B21 is the output target |
| Cofinal prefix `O_θ(T^K)`, fixed K and unbounded θ ⇒ RH | B65: actual prefix-controlled bounds |
| Finite-carrier and almost-every-value repulsion | Does not supply ZCG's actual heat-path collision exclusion |

These are scoped restrictions and conditional receivers, not a no-go for all classical methods.

### 2.7.3 How the programmes fit

- A and B have proved global RH equivalences; shared truth values do not construct source-level transport.
- ZCG, PTR and LA have distinct actual heat/cosine/Jensen criteria. Their missing estimates are not replaced by a
  generic requirement to first build another source.
- PM's coefficient completion, ACS's source cone/RR, SEC's seam admission and CDC/PCS's source criteria are done.
  Their sign, zero-selected bound or equality remains open.
- Candidate status requires a missing source mechanism/landing; an unproved final RH-level estimate alone does not
  demote a live route.
- KR-TOR/UCF/R1 are retired labels, not proved kills. BAG's actual flow transfer, PA's contour-sign receiver and TG's
  bounded-Gaussian-passage receiver survive. Other no-gos retain the scope in the killed-routes ledger.

## 2.8 Which sub-RH target advances the search?

No ranking of intrinsic difficulty is proved. Distinguish useful partial targets from a complete RH receiver.

| Target | Consequence | Limit |
|---|---|---|
| Extend a certified finite aperture, including the prime-3 head | A larger positivity interval and the corresponding head theorem | No automatic propagation to all apertures |
| `100%` critical-scale clustering (B20) | Horizontal first moment `o(T)`; almost all zeros within each fixed `κ/log T` corridor | Sparse off-line zeros remain; not a critical-line proportion theorem |
| Log-free window occupancy `D_win` (B21) | Few occupied depth windows; connection to `D_zero` retains giant-cluster-tail conditions | No off-line extinction |
| Uniform bound on Jensen counts `N_d` (B62) | Finite off-line support | Excluding the finite remainder remains necessary |
| Actual heat-path small-time exclusion (B14) | Removes the principal unresolved ZCG collision region | Low-height compact region must also be controlled |
| Actual long-mollifier excess `O(1/log T)` (B64) | Sufficient for clustering and occupancy under the stated length hypotheses | Necessary length law is not a construction or an RH proof |

Clustering follows from a suitable second-moment bound; the reports do not establish the converse existence of
such a mollifier. Finite-window mimic theorems exclude positivity-only selectors, not every arithmetic use of a
finite-window theorem. New estimates must be evaluated with their precise quantifiers and source hypotheses.
