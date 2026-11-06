# Obstacles summary — status quo

Companion to `route-obstacles.md` (per route; labels `A*`, `B*`, `S*`, mechanism classes P1–P5),
`walls-ledger.md` (Σ/Π/Γ) and `route-unification-ledger.md` (mechanism classes). Corpus checkpoint: `9ebb2bd387`.
Evidence: `[L]` integrated, source-reviewed Lean; `[S]` unfinished/unintegrated; `[D]` inference, not a Lean theorem; `[N]` unverified numerical observation; `[C]` classical literature, not formalized. Windows `[−c, c]` or
half-windows `[−c, 0]`; `w_n = Λ(n)n^{−1/2}`; `H` the archimedean–polar form (prime weights `0`), `P` the arithmetic
part, `W = H − P`; `𝒥` the Lévy energy; `𝒞_m(f) = 𝓗_m(f) − Σ_n w_n(f⋆f)(2m − log n)`; `a*(ζ)` the onset aperture;
`ℋ(c) = {t : H − tP ≥ 0 on [−c, c]}` the arithmetic Hardy interval; `𝒜(c)` the window cone of weights `λ` with
`W_λ ≥ 0` on `[−c, c]`; `λ*(c)` its best margin; `L_T = ½log(T/2π)`; `a_k = weilFloorApertureTower k`,
`a₀ ∈ (181/500, 181/500 + 5×10⁻⁷)`, `a_∞ = lim a_k`, `a_∞−a₀<10^(−7,800,000)` [D]; `log ρ ≈ 0.2812` (plastic number);
`Θ = sup Re ρ`; `N_d` the number of non-real roots of the degree-`d` reversed Jensen polynomial of `Ξ`; `E` the
exceptional values of ζ (a dense `G_δ` null set).

**38 live formulations; 9 candidates.** Live means a concrete source, RH-sufficient receiver and explicit open estimate—not a discharged RH proof or an independent mechanism. ZCG, PTR, SEC, ACS, CDC and PCS satisfy this definition. HJ→PA; BSH→CDC; FEL's BSY criterion→CTF. Candidates: APF, EGC, EWJ, FEL, IRK, MSC, RFHM, W1C, WBF. Authoritative classifications: [frontier](../rh-current-frontier-map.md), [killed/retired mechanisms](../rh-killed-routes.md).

## 1.0 Main facts

1. **Finite rungs are verification tasks [D].** Each window or rank follows from RH verified to a finite height. Window `a` needs `log(T₀/2π)≳2Σ_{n≤e^{2a+s}}Λ(n)/√n`, matching the proved non-locality lower bound. No finite rung decides RH.
2. **Budget suffices [L].** A floor `−C_σe^{2σr}∫F²` for every `σ>0`, or one constant at all apertures, implies RH.
3. **A width axis runs through the routes [L/D].** Interior values are zero-free strips. All routes stop at the Euler edge.
4. **The problem has a prime-free form [L].** RH ⇔ blind positivity; blind energy is `(1/π)∫|𝓜f|²(θ′+1−Re ζ(½+it))`.
5. **Kernel regularity is closed in substance [L/D].** The increment bound and residual limits give absolute continuity. Every bound carries `2C²/μ(a)`, which is the whole remaining gap in the chain.
6. **TH splits [L/N].** First atoms are PD at every rank, every cutoff. Integrated pair spectra have a positive radial factor times the log-ratio cosine: diagonal pairs positive, each unequal pair negative at some frequency [L]. With the aperture weight retained, `Θ₁+Θ₂` has PD signed sections at every rank and every `0<a<½` [L]. Full tails fail at `b=2γ₄` for small `r`, so fibrewise allocation is dead and the aperture weight must stay.
7. **The heat horizon is strip-strength near its floor [L/D].** `c d²/log X≤Λ_X≤(6600/9991+ε)/log X`.
8. **Positive mimic = window sign [D].**

## 1. The big picture

### 1.1 One sign, one number, one inequality
RH ⇔ `a*(ζ) = ⊤` ⇔ `1 ∈ ℋ(c)` for every `c` ⇔ `λ*(c) → 0` [L: WVL, FADF, CHT]. Weil positivity is a **critical Hardy
inequality**: the arithmetic part `P` must be a Hardy term for the archimedean logarithmic jump operator with the pole
kept, `H ≥ P` on every window. Two necessary properties hold unconditionally: the multiple `1` is the only
multiple admissible on every window, and no Hardy weight survives on odd tests [L]. Admissibility on
every window is RH. Known in Lean: `a*(ζ) ≥ a_∞`: `windowThreshold A = ⊤` for `A ≤ 2a_k` on a strictly increasing tower from `a₀` with
floors `(1/20000)/2^k` [L]. The tower is frozen: `a_∞−a₀<10^(−7,800,000)` [D]. RH verified to `3×10¹²` gives `a*(ζ)≥≈1.9` [D].

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
depth `< e^{−c log³T}` [L]. These are conditional location receivers. The tower stays at `a₀ ≈ 0.362`. No proved aperture coverage supplies the required height-dependent positivity.

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
| Fibrewise full-theta tail allocation at all ranks | negative density at `b=2γ₄`, small `r` | [N/D] |
| Floor tower as an aperture producer | frozen at `a₀` | [D] |
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
| P1 signed criticality | `H ≥ P` on every window in the exact two-sector format, frustration unswitchable | sign at unbounded aperture (B7); first windows are verification (A46) | live |
| P2 calibration / blind | `λ*(c) ≥ 0` for every `c`; blind positivity | a floor or sign at unbounded aperture; exact extremal test | live; tower frozen at `a₀` |
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
| A5 | Two-weight membership past `a₀`, odd unit window first | RW, OWU, EWU, ACT, SWC, HF | by A46–A47 or Galerkin; no all-aperture propagation |
| A6 | Exact Tate horizons of the remaining stages below spread `6` | WTZ, CWS | finite templates exist there |
| A7 | Closed form of the first-stage complement `Φ_ε` | GWZ, CSTW, WTZ, RW | explicit Schur complement |
| A9 | Literal channel norms critically small with growing periods, offsets, prime bands | AIP | proved sieve inputs (difficulty unverified) |
| A11 | Function-field calibration of the remaining receivers (ladders, Hardy intervals, de Branges chains of curves, finite purity certificates) | AHD, ACS, SC, HF | the sign is known there |
| A13 | Widths of the finite-level cones `𝒜(c)` beyond `c = 0.66` | PBAP, ACS, RW, FADF, CHT | convex finite programs; entry bounds and the pinning rate proved |
| A14 | PM physical mixed-parameter realization/descent; Mayer compatibility and boundary carrier | PM, W1C | coefficient-space Krein completion closed; physical identification is not routine by theorem |
| A15 | Operator-native nonvanishing on `Re w = 1` | PM | Eisenstein template (risk: reduces to the Euler product) |
| A17 | Tenth signed centre-mixed full-theta section at every `0<a<½` | TH | gamma reserve or A48 |
| A46 | Verified-height window theorem | RW, OWU, EWU, ACT, HF | paper proof [D]; Lean as an implication |
| A47 | Lean-certified `RHVerifiedThrough T`, `T≈10²–10³` | window routes, TH | `hardySEM` brackets exist [L]; Turing count missing; computation heavy |
| A48 | TH finite ranks from verified zeros; Vinogradov–Korobov collar | TH | `current_nonneg_on_frequency_window` and `VinogradovKorobovZeroFree` [L] |
| A49 | De Branges sampling; mimic hypothesis discharged | RW, ZCG | standard theory on the chain [L] |
| A50 | Kernel absolute continuity, density identity, Krein-type system | RW, SZ | increment bound and residual limits [L]; left continuity needed |
| A51 | Heat horizon `(½+ε)/log X` on almost all heights | ZCG | mean values + strip-profile law [L] |
| A52 | Explicit strip from a heat coefficient | ZCG | `exists_le_localNewmanConstant_of_offLine_zero` [L] |
| A53 | Lean certificate of the center-tail failure | TH | [N] |
| A54 | Verified-height bounds for PA, HCF, Jensen, Li rungs | PA, HCF, LA, LI | needs A44 for Jensen |
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
| A43 | Lean bound `weilFloorApertureTower k<0.3621` | RW, AIP, HF | direct from the step formula [D]; no stage passes `½log 3` |
| A44 | Height law of `N_d`: which off-line zeros are counted at degree `d` (outlier positions `x ≈ d/γ` in the saddle identity); explicit constants in `N_d ≤ 300√(d log d)` and in the Cauchy limit | LA, FFP | reading of a proved saddle identity |
| A45 | Constants of the sharp-location theorem (`zetaNegativeCameraHeight`, the exponent in `e^{−c log³T}`) | ZCG, SRT | explicit cameras in place |

## 2.2 Open mathematical obstacles

### Σ — critical sign
| # | Problem | Strength | Routes |
|---|---|---|---|
| B1 | Weil's sign on every window (≡ `1 ∈ ℋ(c)` ∀c ≡ `λ*(c) → 0` ≡ band on reflection pairs ≡ growth steps contractions ≡ Li positivity ≡ Suzuki first variation ≡ two-parameter two-bump family) | RH; fixed length sub | all sign routes |
| B2 | Kick admission at every stage (≡ single-prime stage transport) | RH as induction; each stage sub | RW, GWZ, CSTW, WTZ, HF |
| B3 | The two-sector signed certificate inequalities on every window (`2V ≤ J_{M⁺}`; odd shifted-ground-state form) | RH; fixed length sub | P1 routes |
| B4 | Structural certificate of the odd unit window (the numerical statement is A46–A47) | method | OWU, RW, TT, SWC |
| B5 | Structural certificate below `log 4`, prime `3` paid by sign (numerical statement A46–A47) | method | RW, OWU, EWU, ACT, TT, SWC, HF, ACS |
| B56 | Structural certificate of the `{2,3,4}` sliver band (numerical statement A46–A47) | method | same as B5 |
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
| B51 | Contact-excluding arithmetic kernel bound, free of `1/μ(a)` | RH | RW, CSTW, CHT, SZ |
| B59 | Decay law of `λ*(c)` between the pinning rate `e^{−c/1104}` and the doubly exponential ceiling | sub | PBAP, FADF, CHT, RW |
| B66 | All ranks of the signed centre-mixed sections at every `0<a<½` | RH | TH |
| B69 | Unequal-atom payment with aperture weight retained | RH | TH |
| B70 | Any interior width value: a fixed zero-free strip by any route | ≥qRH | every route on the width axis |
| B71 | Exact extremal blind test `Φ=Ξ·g` | indep. | PBAP |
| B72 | Floor `−Cexp(r−cr^α)`, `α>3/5` (beyond Vinogradov–Korobov) | sub | window routes |
| B73 | `Λ_X log X→0` on density-one heights | sub | ZCG |
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
| Is the window tower a canonical system? | a de Branges chain before contact with exact collar equation; absolutely continuous [D]; contact is the first singular length | CSTW, CHT [L] |
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
| Are first-atom tails positive at all ranks? | yes, every rank, every `r≥0` | CAF [L] |
| Are full-theta tails positive at all ranks and cutoffs? | no, numerically: negative density at `b=2γ₄` for small `r` | [N/D] |
| Is the floor tower cofinal? | no: `a_∞−a₀<10^(−7,800,000)` | [D] |
| Do first windows need new mathematics? | no for the numerical statement: verified zeros decide them | [D] |
| Is an exact sign necessary? | no: a bounded or subexponential floor implies RH | SquareRootThreshold [L] |
| Is every fixed Jensen degree eventually real-rooted? | yes, beyond an explicit shift horizon | RHTower [L] |
| Are the centre jets positive? | PF₄₅ at the centre; all slice coefficients nonnegative for `\|t\| ≤ 709/50` | RHTower [L] |

## 2.3 Frankenstein routes

**No assembly closes RH.** Each row names what the parts jointly prove and the single estimate still missing. A shared RH endpoint does not transfer an estimate between routes.

| # | Parts | What the assembly gives | Status | What is still missing |
|---|---|---|---|---|
| F1 | WVL, FADF, SWC, CHT | exact two-sector format on every window; cone pinned | [L] | the format inequalities (B3) |
| F2 | FADF, AHD, CSTW | Hardy induction by prime entries; single-prime transport ⇔ RH | [L] | a margin at every entry (B2) |
| F3 | CACT, AHD | complete family reduces long windows to heads | [L] | heads for all `d` (B55) |
| F4 | RIT | coefficient completion and weighted defect | [L] | `D_s≥0` (B38) |
| F5 | RHTower, ZCG, ADO | heat path, horizon, near-coincidence dictionary | [L] | collisions at small time (B14) |
| F6 | SRT, RHTower, ZCG | positivity at `λL_T` ⇒ depth `<e^{−c log³T}` | closed receiver [L] | the positivity |
| F7 | CSTW, CHT, GWZ, SWC | canonical system with explicit collar equation | [L]; AC [D] | contact-uniform bound (B51) |
| F8 | FFP, ZCG, ADO | Euler carriers stable and repelling | [L] | no finite carrier converges to Ξ |
| F9 | WTZ, A5 | finite Hecke matrices below spread 6 | [L] | Weil's form is not a correlation form |
| F10 | WVL, WD, DCI | visibility plus shallow mass bounds | [L] | B1, B21 |
| F11 | FFP, ZCG | `N_d` and camera depth | [L] | B52 |
| F12 | AHD, SWC, A46 | Dirichlet-shift heads for small `d` | [L]/[D] | large `d` (B55) |
| F13 | APR, CDG, WD | moment and detector receivers | [L] | actual moments (B64) |
| F14 | Verified zeros, SWC, AHD, TCS | windows to `a≈1.9`, heads to `d≈50`, TH ranks far past 9 | [D], external numerics | nothing finite; decides no all-aperture statement |
| F15 | CSTW, ZCG RealWeights | sampling atoms are positive mimics; weighted count applies | [D] | sign past `a*` (same as B1) |
| F16 | Floor receivers, CSTW, CHT | RH from any subexponential floor; kernel flow gives the budget's natural form | [L]/[D] | a floor independent of `μ(a)` |
| F17 | Heat depth, horizon, floor | three-way width dictionary | [L]/[D] | any interior width value |
| F18 | TH current, first atoms, verified zeros | current positive on a frequency window; first atoms positive everywhere | [L] | unequal atoms at high frequency (B69) |

**Closest to the open core: F16.** It replaces exact sign with a budget, and the chain supplies an evolution equation. Every proved bound divides by `μ(a)`. A bound without that factor closes RH; none is known.

## 2.4 A wildly different route

Three mechanisms lie outside the current routes. Only the N1 receiver is in Lean. All three are speculative: none has a theorem behind it beyond the classical or Lean statements cited. They share the endpoint RH and differ in mechanism.

### W1. Exact extremal function (sphere-packing method)
- **Idea.** Prove the blind inequality by constructing its exact extremal object, as Viazovska's functions do for a zero-slack linear program. Criticality kills margin arguments; it does not kill exact identities.
- **Precise target.** `Φ=Ξ·g` with `|Φ|²` blind at every `log n` (N1) [L receiver]. It would be an exact null ray of the blind program.
- **Why the walls differ.** No primes appear (Π filters do not apply), no gauge or margin is used (Σ no-gos do not apply).
- **First test.** Carlson forces `|g|` to grow near `e^{π|t|/4}`; compact solutions do not exist [L]. Decide existence in the Carlson-admissible class.
- **Risk.** Modular forms have finitely many zeros in a fundamental domain, so zeros at all `i·n` do not come directly from a modular form [D].

### W2. Representation-theoretic construction (Thoma, Schur–Weyl)
- **Idea.** With `α_ρ=1/(ρ(1−ρ))`, RH is Schur positivity of the `α_ρ`, which is PF_∞ at the centre [L] and, by Thoma's theorem, says `σ↦∏_{cycles}p_k(α)/p_1^k` is a character of `S_∞` [D]. Build the representation instead of checking inequalities.
- **Why the walls differ.** A representation has positivity built in. Over `𝔽_q` the same function is the trace of `σ·F^{⊗k}` on `H^{⊗k}`, which links it to Deligne's tensor powers [D].
- **First test.** Compute the Kingman/Thoma data for curves and for known fakes, and look for a natural exchangeable partition with frequencies `α_ρ/p₁`.
- **Risk.** Building it is a Hilbert–Pólya realization in other language. Direct tensor amplification is closed (Σ13).

### W3. Homogeneous dynamics
- **Idea.** Zagier's classical criterion says RH is the rate `y^{3/4−ε}` for equidistribution of long closed horocycles on the modular surface [C]. A dynamical proof of that rate would bypass Euler-product positivity.
- **Why the walls differ.** The input would be rigidity, not an inequality on primes.
- **First test.** Formalize the criterion, then ask whether Hecke recurrence plus entropy (Lindenstrauss type) constrains limit measures.
- **Risk.** The rate is read from the same scattering poles as PM, and horocycle flow has zero entropy.

## 2.5 Breakthrough questions below RH and quasi-RH

Tests as listed below. T1 is read as: implied by RH and not implying quasi-RH. T4 applies only to claims of reaching RH.

| Test | Requirement |
|---|---|
| T1 | Not equivalent to RH; below quasi-RH |
| T2 | Answered by proving or refuting a stated inequality |
| T3 | A named consequence can be written down |
| T4 | Not decided by a finite window (nor a finite rung) |
| T5 | False on a corpus fake |
| T6 | Names an input not refuted in Lean |
| T7 | Not a shape already answered without moving a wall |

### 2.5.1 Whole programme — `100%` critical-scale clustering (B20)
**Question.** Does `T⁻¹∫_T^{2T}log|ζ(½+it)|dt → 0`? Equivalently, do all but `o(T log T)` zeros lie within `κ/log T` of the line for each `κ`?
- **Tests.** T1–T5, T7 pass. False for Davenport–Heilbronn, `ζ(s)ζ(s−ε)` and impure factors [L]. T6 weak: long moments are the only named input.
- **Gives.** RH on average at the spacing scale.
- **Limit.** Sparse off-line zeros survive; no path from it to RH is known.

### 2.5.2 Route PM — a PM-native zero-free line (B46)
**Question.** Can the Mayer/Lewis–Hecke carrier alone prove `ζ(2s)≠0` on `Re 2s=1`, without the Euler-product inequality?
- **Answer: yes, formalized.** The actual Eisenstein lift, its Maass–Selberg norm and nonzero first Whittaker mode prove `MayerBoundaryNorm.mayer_boundary_denominator_ne_zero`. The completed scattering quotient has unit modulus; the actual Mayer determinant and pole cofactor have the same zeros on the nonreal upper boundary. Direct checks and transitive standard-axiom audits passed. [Proof, independence audit and Lean declarations](../../drafts/pipeline/3-formalized/mayer-boundary-maass-selberg-norm.md).
- **Tests.** All pass. Blaschke insertion (Γ22) is the fake it must exclude.
- **Gives.** Boundary zero information from the actual geometric Mayer carrier.
- **Limit.** The absolute-convergence chamber uses the convergent Möbius convolution identity; the boundary proof uses no Euler-product inequality. Interior resonance exclusion remains open.

### 2.5.3 Route WD — log-free window occupancy (B21)
**Question.** For every `A`, do at most `ε(A)V` unit windows of `[V,2V]` hold a zero of depth `≥A/log V`, with `ε(A)→0`?
- **Tests.** T1–T5, T7 pass. T6: the sufficient detector shape is known and sharp, no producer is.
- **Gives.** `D_win`; with cluster tails, `D_zero`.
- **Limit.** Requires depth decay at rate `≍ log log V`, so proportion results do not reach it.
- **Programme.** 2.7.2.

### 2.5.4 Route HF — one critical multiple past the size optimum (B7)
**Question.** For one `K` above the size-only optimum, is the full tilted-spline matrix eventually PD at `c=2K(log N)^{1/8}`?
- **Tests.** All pass. Unbounded aperture, and the Liouville twin fails at fixed overlap [K].
- **Gives.** The first full-space sign payment beyond size; requires beating `O(c)` against `O(log N/c⁷)`.
- **Limit.** Each `K` is separate; all `K` is the RH receiver.

### 2.5.5 Route TH — the first unequal atom pair
**Question.** Does the two-atom source `Θ₁+Θ₂`, with aperture weight retained, have positive signed sections at every rank and every `a`?
- **Answer: yes, formalized for every `0<a<½`.** Convex aperture weights let the two diagonal terms pay the cross pair at every frequency. The exact literal jet and Fourier identities give `CompletedArithmeticForms.twoAtomApertureMatrix_posDef`, positive determinants, and positive successor Schur coordinates at every rank. All eight modules passed direct checks and transitive standard-axiom audits. [Proof and Lean declarations](../../drafts/pipeline/3-formalized/two-atom-aperture-convexity.md).
- **Tests.** T2, T3, T4 pass. T1 and T5 do not apply as stated: this is a statement about a model source, and only prime 2 enters.
- **Gives.** The first rank-uniform statement with a cross pair, and the correct form of allocation after fibrewise tails fail [N/D].
- **Limit.** Decides nothing about ζ alone; the full theta source still requires allocation of all unequal pairs.

### 2.5.6 Route ZCG — the saddle on almost all heights (B73)
**Question.** Does `Λ_X log X → 0` on a density-one set of heights?
- **Answer: yes, formalized.** One measurable density-one set satisfies the exact limit for `localNewmanConstant`. On the same set, every `κ>0` eventually gives real zeros throughout `|Re z−X|≤1` simultaneously for all `τ≥κ/log X`. Theorems: `ZeroConfigurationGeometry.exists_densityOne_localNewman_scaled_tendsto_zero` and `exists_densityOne_eventual_local_heat_reality`; direct checks and transitive standard-axiom audits passed. [Proof and Lean declarations](../../drafts/pipeline/3-formalized/local-newman-density-one.md).
- **Tests.** T1–T5, T7 pass. Density-one `(½+ε)/log X` is reachable from mean values (A51); crossing `½` is the content.
- **Gives.** The heat-flow form of clustering.
- **Limit.** Exceptional heights remain. The relation to B20 is expected, not proved.
- **Programme.** 2.7.1.

## 2.6 Questions that would open the path to RH

Every statement below is RH-strength or stronger. **None passes the door test of a reachable factor.** Each entry gives the weakest door-shaped form known.

| Route | Question | Why it would open the path | Verdict |
|---|---|---|---|
| 2.6.1 Whole | Self-improvement of a floor: does rate `2σ` imply rate `σ`? (B57) | With `Θ<1` it gives RH; floors need no exact sign [L] | No mechanism; false for shifted products, so degree one or Ramanujan must enter |
| 2.6.2 PM | An independent expression forcing `D_s≥0` | Equivalent to RH since `D_s≤0` always | RH itself; it needs a positive physical carrier (B40) |
| 2.6.3 WD | Cofinal `∫_1^T|ζM|²≤C_θT^K` with prefix cancellation (B65) | Implies RH [L] | Possibly stronger than RH; length far beyond present mollifiers |
| 2.6.4 HF | Cofinal `xiDampedSourceWork≤2` | Coarse bound; the threshold is quantized, so `≤2` forces `0` [L] | RH; attractive because it is an upper bound, not a sign |
| 2.6.5 TH | Unequal-atom allocation with aperture weight (B69) | Closes all ranks | RH; fibrewise form is false [N/D] |
| 2.6.6 ZCG | Exclude collisions below the saddle by a route not using size | Size stops at `½/log X` | Fixed coefficient below a constant is already strip strength [D] |

## 2.7 Does closing RH need a new field?

No theorem says so. The evidence is structural: every known tool fails for a proved reason.

| Known tool | Why it stops |
|---|---|
| Size estimates | die before half-width `21/40` |
| Positivity-preserving (Markov, Perron) | frustration past `log ρ` |
| Type I/II sieve data | parity blind |
| Finite computation | finite rungs decide nothing |
| Tensor amplification | carries RH unchanged |
| Integrality | amplifies, produces nothing |

**What the field would be about.** Critical signed forms whose off-diagonal data live on a sparse arithmetic set of positions: how such a form can be nonnegative with zero slack and no sign gauge.

| Aspect | Requirement |
|---|---|
| Objects | window cones over `log ℕ`; blind states; canonical systems with atomic kicks; datum plane (pole, conductor) |
| Language | budget (floor rate) in place of exact sign; width axis; duality between weights and blind states |
| Criteria it must meet | false on every corpus fake; parity-breaking; locally pure; unbounded aperture; recovers Weil's proof over `𝔽_q` |
| Questions | When is a frustrated form nonnegative? What replaces Allegretto–Piepenbrink? What makes `{log n}` special among node sets? Why is `(β,s)=(1,0)` critical? |
| Tools to build | exact certificates for frustrated forms; a priori estimates for Krein systems with atomic forcing, free of `1/μ(a)`; a self-improvement step for floors |
| Test case | a proof of `H≥P` on one unbounded test family (B7), then its `𝔽_q` analogue |

The closest existing programme is critical Hardy theory of the window cone. The arithmetic-production side (square-root precision) is not obviously part of the same field, and the corpus proves no bridge between them beyond shared RH endpoints.

### 2.7.1 A programme for route ZCG: nodal geometry of the de Bruijn flow

**A research programme, not a new field.** It supplies ZCG's first tool below the saddle that does not rest on size. It does not exclude a collision by itself. The PDE inputs are [C]; none is in Lean.

**Why ZCG needs it.** Uniform bounds from unconditioned source sizes stop at the saddle `½/log X` [L]. Lowering the coefficient uniformly by size needs Lindelöf-strength input, and a small enough uniform coefficient forces a zero-free strip [D]. Exceptional heights still require a different input.

**B73 is settled on a density-one set [L].** Typical-height zero-free boxes give a small relative source derivative. The half-Gaussian argument then proves `Λ_X log X → 0` on one measurable density-one set, with reality throughout each unit window at every later time above `κ/log X`. This does not establish the local repulsion law below or an implication to B20. [Exact theorem and proof](../../drafts/pipeline/3-formalized/local-newman-density-one.md).

**The change of viewpoint.** `u(X,t)=H_t(X)` solves `∂_t u=−∂_X²u`, so decreasing `t` is forward parabolic flow. RH says the nodal curves of `u` in the half-plane `t>0` have no turning points. A collision is a point where `u` vanishes to parabolic order two, with local model `x²−2(t−t₀)`.

| Tool | What it gives ZCG | Status |
|---|---|---|
| Zero number (Sturm, Angenent) | real-zero count falls only at collisions as `t` decreases, by the collision's order | needs buffered windows: the unbuffered law fails [L] |
| Parabolic frequency (Almgren, Poon) | monotone quantity: vanishing order at a point is bounded by Gaussian-weighted frequency at any larger scale | exact for every caloric function, no size input |
| Blow-up classification | each collision is a Hermite profile of its order | model case proved (`pairModelHeat_orderTwo_collision`) [L] |
| Zero dynamics (Dyson flow, Rodgers–Tao) | `d(g²)/dt=8−g²S`, where `S≥0` sums neighbour forces [D] | averaged law `spread_roots_heatFlow` proved for polynomials [L]; localization open |
| Relaxation at normalized time `τ=tlog²X` | connects GUE-type gaps at `τ≲1` to crystal gaps at `τ≫1` | `τ` runs up to `≈0.66 log X` in the open region [D] |

**The central question.** Is there `c>0` with `g_t²≥c·min(t, log⁻²X)` for every adjacent pair of real zeros near height `X` and every `t>0`?
- It implies no positive-time collision, hence RH.
- The converse is expected away from clusters but unproved.
- The density-one version would give another mechanism for the now-proved B73 conclusion.

**(a) Just work**
1. Sturm drop law for `H_t` in buffered windows.
2. Local zero ODE for the actual source, with a regularized sum.
3. Hermite blow-up at actual collisions.
4. Frequency monotonicity for `u`, and an explicit collision-order bound, about `0.33 log X` from the horizon scale [D].

**(b) Open mathematics**
1. The local repulsion law above.
2. A depth law linear in `d`: the model gives `t*≈d/log X` when `d log X≫1`, while Lean has `c d²/log X`.
3. Control of neighbour compression `S` on clusters.

**What limits it.**
- Every monotone identity here also holds for `H_{−τ}`, which does collide at positive time. The arithmetic must enter through data: the proved region above the horizon, RvM counts, pair correlation and the Euler product in `Q`.
- Collisions do occur below `t=0` [L: `newmanConstant_nonneg` with `Λ=0` under RH], so any inequality must degenerate exactly at `t=0`.
- A dimension count makes collisions in the `(X,t)` plane generic, so Diophantine repulsion alone cannot exclude them [D].

### 2.7.2 A programme for route WD: multiscale analysis of the mollified zeta field

**Serves WD's density branch (B20, B21), not its RH branch (B19, B64, B65).** It is an existing area of probabilistic number theory. Its inputs are [C]; a Selberg central limit theorem, branching barriers and multiplicative chaos at this scale are not in Lean.

**Why WD needs it.** WD's obstacles come from one method, second moment plus Jensen:
- polynomial length has moment floor `1+1/(8+6θ)` [L];
- moments alone do not determine the log-mean (Π19) [L];
- occupied-window bounds lose a factor `log V` [L].

B23 already asks for a distributional input beyond counts and moments. This programme is a candidate for it.

**The change of viewpoint.** `log|ζ(½+it)|` behaves as a log-correlated field, with primes in dyadic scales as branching steps. A unit window contains about `log V` zeros, so the `log V` loss is a union bound over them [D]. Barrier arguments are the known way to beat such a union bound (Fyodorov–Hiary–Keating maxima, Arguin–Bourgade–Radziwiłł; Harper for random multiplicative functions).

| Target | Fit | Why |
|---|---|---|
| `D_win` (B21) | best first target | only `A→∞` is needed, where second-moment excess is small; the obstruction is the log loss [D] |
| Clustering (B20) | harder | small `κ` needs primes near `T^{Θ(1)}`, where products exceed `T`; this is signed pair data past bandwidth one (B28) |
| Long-moment bounds (B64, B65) | no help | a long mollifier is truncated `1/ζ`, so residues `N^{ρ−s}/(ρζ′(ρ))` bring in negative moments of `ζ′` and every off-line zero [D] |

**The central question.** Does a barrier on partial prime sums give `P(unit window of [V,2V] holds a zero of depth ≥A/log V)≤ε(A)`, with `ε(A)→0` independent of `V`?

**(a) Just work**
1. Selberg's central limit theorem for `ζ` and the dyadic prime decomposition, in Lean.
2. Twisted second moments against products of short Euler pieces, within known length.
3. Barrier probability estimates for the prime-sum random walk.

**(b) Open mathematics**
1. Turning a barrier event into the detector shape: `D_win` needs shifted defect `≤Ce^{−r(σ−½)log V}V/log V` [L], and size-only detectors at that scale fail (Fejér–Dirichlet) [L].
2. The last scale, where mean-value theorems stop (B28).
3. Negative moments `Σ|ζ′(ρ)|^{−2}`, which link WD to the small-value questions of ADO.

**What limits it.**
- Sparse off-line zeros survive, so this reaches no RH statement.
- The barrier method's success on maxima is an analogy here, not a theorem about zeros.

**Why it could work where the fakes fail.** It uses independence of primes, which the root model, Davenport–Heilbronn and impure factors lack.

## 2.8 The one question

**B7, the HF question of 2.5.4.** For one `K` above the size-only optimum, is the full tilted-spline matrix eventually positive definite at `c=2K(log N)^{1/8}`?

**Why this question.** It alone has all four properties:
1. **Not a finite rung.** The aperture is unbounded, so verified zeros cannot decide it.
2. **Selective.** The Liouville twin fails at fixed overlap [K], so a proof must use prime signs.
3. **Past size.** It forces the first payment of the far complement by sign, which is the step every sign route lacks.
4. **Below RH.** Each single `K` is a sub-RH target.

**Consequence.** The first mechanism paying primes by sign on unbounded windows. Every sign route needs one, and none has one.

**Limits.**
- It does not pass the strict door test: no theorem propagates one `K` to all `K`.
- The size-only optimum must be certified first (A4). Otherwise a positive answer could be size in disguise.
- Its difficulty relative to RH is unproved.

**Next strongest:** B20 clustering. It is the stronger classical result, but it has no route to RH and its only named input is long mollifiers, far beyond present lengths.

**Not doors:**
- first windows (`½`, `log 2`, `½log 5`), which are finite verification;
- the tower limit, which is frozen at `a₀`;
- fibrewise TH tails, which fail numerically.
