# Obstacles summary — status quo

Companion to `route-obstacles.md` (per route; labels `A*`, `B*`, `S*`, mechanism classes P1–P5),
`walls-ledger.md` (Σ/Π/Γ) and `route-unification-ledger.md` (classes C1–C24). Evidence: `[L]` committed
Lean declaration; `[W]` working-tree Lean module; `[D]` derived here from Lean statements; `[M]` exact
model statement; `[N]` numerical; `[P]` paper. Killed mechanisms are cited by their anchor in
`rh-killed-routes.md`. Windows `[−c, c]` (half-width `c`, length `2c`) or half-windows `[−c, 0]`;
`w_n = Λ(n)n^{−1/2}`; for `f` left of `m` and its mirror `f∘R`, `𝒞_m(f) = 𝓗_m(f) − Σ_nw_n(f⋆f)(2m − log n)`
with the collar Hankel form `𝓗_m(f) = e^mμ_{1/2}(f)² − Σ_ke^{2mσ_k}μ_{σ_k}(f)²`. The lag `log n` sees a
half-window test only on its **sliver** `I = [−c, c − log n]` of width `δ = 2c − log n`. Paper results `[P]`
of the cards `zcg-square-root-local-inversion`, `zcg-heat-scale-source-repulsion` and
`window-visibility-onset-law` (`docs/drafts/pipeline/2-fully-proven/`) are cited by card name;
`L_T = ½log(T/2π)`.

## 1. The big picture

### 1.1 RH is the band on reflection pairs
RH ⇔ every two-site lattice window is PD ⇔ `|c_φ(t)| < Q(φ)` for every bump and `t ≠ 0` [L: GWZ]. For a
test and its mirror, `W(f ± f∘R) = 2W(f) ± 2𝒞_m(f)`; the odd and even sectors of `[−c, c]` are the band at
the centre [L: SWC]. The minimal decisive object is the smoothed prime number theorem at square-root
precision, constant `W(f)`, in a fixed multiplicative window.

### 1.2 The first stages are two numbers
A half-window test on `[−c, 0]` meets no prime lag iff `c ≤ log 2` [L]. For every `0 < c < log 2` the
window is positive iff `(Λ(2)/√2, Λ(3)/√3) ∈ belowLogFourBandWeights c`, the set of weight pairs for which
`|𝓗₀(f) − w₂(f⋆f)(−log 2) − w₃(f⋆f)(−log 3)| ≤ W(f)` on `[−c, 0]`, with `W(f)` purely archimedean–polar;
the set is the intersection of the odd and the even sector sets, convex, compact once `c > ½log 3`, a
cylinder in `w₃` before `3` enters, and it excludes every `w₂ ≤ 0` for `c ≥ 21/40` [L: SWC]. So below
`log 4` the sign is the membership of one explicit point in one explicit compact convex set: a two-term
prime count must reproduce the collar Hankel form within the archimedean energy. The odd unit window
(`c = ½`) is its one-number shadow (`w₂ ∈ unitBandWeights`). The base theorem reaches length `≈ 0.7240`;
nothing between `enlargedWeilFloorAperture` and `log 2` is proved [L].

### 1.3 The primes pay by sign, not by size
For `f` on `[−c, 0]`, `(f⋆f)(−ℓ) = ∫_I(f₊² − f₋²)` (the signature of the sliver reflection), outward jumps
give `Ω(δ)∫_If² ≤ levyEnergy f`, and every prime power costs at most `w_n|(f⋆f)(−log n)| ≤
(Λ(n)e^c/(2n))·levyEnergy f`; `{2,3}` together use `< ¾` of the Lévy energy below `log 4` [L: SWC]. Summing
the bound over the acting prime powers, `(e^c/2)Σ_{n ≤ e^{2c}}Λ(n)/n` is below `1` exactly on windows
shorter than `log 5` (`0.991` just below, `1.35` just above) [D]. Yet the primes are indispensable: the
Markov part is negative beyond length `e^{−3/4}`, `w₂ = 0` and the flip are inadmissible [L]. Below
`log 5` the reflection terms stay below the Lévy energy and still must pay the prime-free archimedean–polar
deficit; they pay through the sign of their sliver reflections — helping on reflection-symmetric profiles,
costing on antisymmetric ones. The prime `3` cannot be carried by its size: the worst-case collar
potential fails for `c ≥ 287/500` [W].

### 1.4 Certificates must keep the pole variance
In a gauge `F = Φωu` the window form is a signed Dirichlet form plus pole charges [L]. Dropping the pole
variance fails for `c > 273/400` (explicit two-profile witness; refutes compact sinh-charged
supersolutions, odd theta-gauge outside-charge certificates and shifted-ground-state lower bounds) [L];
nonnegative even theta gauges have a strictly negative cosh-charged defect [L]. Retaining the variance —
the all-pairs jump form `∫∫m(x)m(y)(u(x) − u(y))²` — makes every positive even theta gauge (even sector)
and every shifted ground state (odd sector) an exact certificate equivalent to positivity below `log 4`,
to the Hodge index of the scaling subsurface and to Künneth effectivity [L]. The certificate format is
settled; only the arithmetic membership is open.

### 1.5 Sectors are moment problems; extremals live at the edge
For an even bump with `s_k = W(φ^{(k)})`: the even sector is the Hamburger condition, the odd sector the
shifted Hamburger condition, the window the Stieltjes condition [L]. A nonnegative window therefore gives
every even bump a spectral measure on `x = ξ² ∈ [0, ∞)`; the pole sits at `x = −¼`. No window
eigenfunction, constrained ground state or capacity maximizer is smooth; nonnegative windows are PD on
smooth tests and the band is strict there [L]. The lattice canonical system freezes onto the boundary of the
Schur disk: reflection coefficients `γ_n → (−1)^n` with normal velocities `e_{n+1}/e_n`, margins
`h^{−2n}E_n → det J_{n+1}/det J_n > 0` on every nonnegative window, parity split `det J_n = det E·det O`
[L]. The Gamma form rises along the derivative ladder and prefers the even sector; the pole adds its
positive square to the even sector and its negative square to the odd one [L].

### 1.6 Local resources certify few kicks; soft entry is margin transport
Collar-internal jumps pay the kick of `n` at ratio `2w_ne^h`, sharp, never for the primes `3 ≤ p ≤ 73`
[L/D]; outward jumps carry the newest prime power at ratio `w_ne^h/2` near its entry [L]. Soft entry: a
sector band with Lévy margin `η` admits every newest weight within `ηΩ(2c − log p)`,
`Ω(δ) ≥ (e^{−1/2}/2)log(1/δ)` [L]. Carrying `w₃ = 0.634` needs `η·0.303·log(1/δ) ≥ 0.634`, so even a margin
`η = 1` covers only `δ ≤ 0.12`, i.e. `c ≤ 0.61 < log 2` [D]: soft entry is a sliver mechanism, and on most
of `(½log 3, log 2)` the prime `3` is paid by the sign of its reflection. Summed over a reflection pair the
anti-diagonals of all kicks are the smoothed prime count in `𝒞_m`: P1 and P4 are one problem beyond the
first stages, and already below `log 4` as a two-term count.

### 1.7 The complete family: size-only layers complete; the sign is a threshold
The complete Weil matrix is PD below `(log N)^{1/8}` and on the whole prime-horizon space at one critical
multiple with every window corollary [L]. Every window has a threshold `R₁(A)` and RH ⇔ `R₁(A) = ⊤` ∀A [L].
Every compact terminal window has an exact complete mixed limit at all positive ratios, and its source is
polar (nonpolar centre and divisor jet cancel); correctors cannot improve zero-source windows; the polar
capacity is attained by one pole coefficient [L]. Receiving charges, mixed channels and sieve inputs are
classified [L]. The floor that pays the small multiple carries no zero information: its exponent `p > 1` is
forced by Cauchy–Schwarz on the pole moment, and exponent `p` gives only zero width `≤ p` [L/D].

### 1.8 PM is the zero side, and its sign is the identity `δ = 0`
`Q(H) = 2Re[𝓦_AH, 𝓦_AH]` exactly on `ℓ²(upper Mayer resonances)` [L]. For a `+1` fixed period the
co-isometry defect is `D_s(ψ) = −∫_0^∞(e^{δu}+e^{−δu})(e^{δu}−e^{−δu})²|F(u)F(−u)|du`, `δ = 2Re s − ½`
[L]; for a resonance `ρ = 2s`, `δ = Re ρ − ½` and `D_s ≈ −8δ²∫u²|F(u)F(−u)|` [D]. So `D_s ≥ 0` at a
resonance is the statement `Re ρ = ½` itself, not an inequality with room. The resonant basis is
Krein-isotropic off `Re s = ¼` [L]; the retained `T₂` channel has defect of the sign of `¼ − Re s` and reads
the side [L]; window tests lift to fixed periods whose defect dominates the fold functionals [L]. A PM proof
needs a second expression of the defect at resonances, arithmetic and manifestly `≥ 0`.

### 1.9 The camera identifies at the density threshold, without sign
Blind windows exist at every aperture above `π` times the upper density and at none below the lower
density (Jensen); blind windows ⇔ entire functions of exponential type vanishing on the set; no nonzero
window is blind to the real zeros of `Ξ` [L: ZCG]. Mimics at aperture `a` cancel only along clusters of
upper uniform density `≥ 2a/π`, sharp by the on-line lattice pair; shallow separated configurations are
resolved at the Ingham scale, globally and around one height with an explicit far error; every fake with
`ζ`'s archimedean data is caught exactly above aperture `½log n₀` of its first differing integer [L]. With
`L_T = ½log(T/2π)` the camera is quantitative and uniform in height: if the cancelling cluster of two
tempered configurations has distinct-point density `θ·(1/2π)log(T/2π) + O(log T)` near `T` and their images
agree at aperture `λL_T`, `λ > θ/2`, they have equal multiplicities at every point of `|Im z − T| ≤ T/4`
that is `T^{−M}`-isolated in the cluster [P: `zcg-square-root-local-inversion`; W]. For `ζ` against a
mimic of local density `μ log X` the aperture `λ log X`, `λ > ¼ + πμ/2`, suffices at every
`exp(−κ log X/(1 + log log X))`-isolated point, and cancelling clusters of `ζ`-mimics consist of
near-coincident points [L: `multDiff_zeta_eq_zero_of_isolated`]. The threshold is sharp: the on-line
lattice of `ζ`'s density and its half-shift have disjoint carriers, local counts within `1`, separation
`π/log(T/2π)` and equal images up to aperture `L_T` [L: `exists_rvm_pair_mimic_disjoint_up_to_one`]. So
against an arbitrary competitor of `ζ`'s density the image must read the primes up to `T` (`λ = 1`); the
primes up to `√T` (`λ > ½`, the Riemann–Siegel length) suffice only against competitors that differ from
`ζ` on a set of density `< (2λ − 1)(1/2π)log(T/2π)`. Positivity at one aperture puts thin configurations
on the line above `πD` and split columns above `πD_on + (π/2)D_off` [L; P]. An on-line competitor with the
image of `ζ` would already be Weil positivity, so identification decides nothing alone [D].

### 1.10 Reality by continuation is a zero-free region in heat coordinates
`H_t` is real for `t ≥ 1/8` (corpus normalization) and non-real for every `t < 0`; RH ⇔ every zero of `H_t`
is simple for every `t > 0` ⇔ the collision mass vanishes ⇔ the local constant `Λ_X` vanishes at every
height, and a zero of depth `d` near `X` forces `Λ_X ≥ c·d²/log X` [L: RHTower]. With the symmetric half
`Q_t(X, y) = ∫_0^∞ g_t(w − y)ξ(½ + w + iX)dw`, `H_t(X) = 2Re Q_t(X, 0)` and at a real zero
`|H_t'(X)| = 2|Re(D₀ conj Q_t)|/|Q_t|`, `D₀ = ∂_yQ_t|_{y=0}` [P: `zcg-heat-scale-source-repulsion`]:
simplicity is the phase speed of the half, the law of Euler stages (`SymmetricHalvesArePhaseLattices` [L])
for the heat source. Domination `|Q_t(X, −y)| < |Q_t(X, y)|` from four sub-Weyl profiles gives
`Λ_X ≤ (6600/9991 + ε)/log X`, sharp for that profile at `w* = 198/9991` [P] (`(2/3 + ε)/log X` [L]).
Size-only domination ends at `½/log X`: below it the Gaussian saddle `σ* = ½ + t log(X/2π)` lies in the
strip, and the pair model (one off-line pair of depth `δ` in an on-line lattice of `ζ`'s density,
`L ≍ log X`) collides at `t* = (√(1 + L²δ²) − 1)/L² < δ/L ≤ 1/(2L)` [P]. So every off-line pair of the
model has collided by `½/log X`, and no horizon `c/log X` with `c ≥ ½` excludes a zero; in the model
`Λ_X log X` is the depth of the deepest zero near `X` (`t* ≈ δ/L` for `Lδ ≫ 1`, `≈ δ²/2` for `Lδ ≪ 1`) [D].
Below `½/log X` domination needs a lower bound for `ξ` on a horizontal segment inside the strip:
zero-free-region information [D]. Repulsion is proved where `ζ` is not: integrality of the image over `𝔽_q`
(collide or repel, purity lost only at Frobenius collisions) and phase speed above the horizon `2πe^{W(X)}`
of finite Euler stages [L: ZCG].

### 1.11 What a window sees: the onset law
Every tempered configuration `Z` has an onset aperture `a*(Z) ∈ [0, ⊤]`: window positivity at `a` ⇔
`a ≤ a*(Z)`; `a*(Z) = ⊤` ⇔ `Z` is on the line; RH ⇔ `a*(ζ) = ⊤`; off RH `a*(ζ)` is the contact aperture;
`AHD.windowThreshold A = ⊤` ⇔ `A/2 ≤ a*(ζ)` [L: `OnsetApertureAndPositivityDictionary`]. On model classes
the onset is exact [P: `window-visibility-onset-law`]:
- **Deep coherent clusters.** `k` aligned pairs of depth `δ` in an on-line lattice of density `L/2π`:
  positivity at `a ≤ L/2` ⇔ `k(sinh(2δa)/(2δ) − a) ≤ L`, so `a* ≍ (1/2δ)log(CδL/k)` for `k ≲ δL`. In RvM
  backgrounds positivity at `a` excludes every zero with `e^{2(δ − σ)a} ≥ CδaA₀log(|γ| + R)/k`, unless a zero
  deeper than `σ` shields its collar (the tilt-amplification law, unconditional).
- **Shallow coherent clusters.** `a* ≍ (L/(kδ²))^{1/3}` for `k ≳ δL`; positivity at `a` bounds the sub-depth
  mass of shallow clusters, `Σmδ² ≤ CA₀log T/a²` per unit window (DCI: `40σ²log(180|T|)`).
- **Columns.** Positivity above `πD_on + (π/2)D_off` puts split columns on the line, sharp for mixed columns
  of genus `g ≥ 2`. Half-carrier law: if `ρ₀` can be isolated from the right half of the carrier at aperture
  `a − ε`, some window of half-width `a` is negative.
- **Crystals.** Off-line lattices hide up to `L/2`; one defect lowers the onset to `(1/2δ)log(CδL/ε²)`, and
  `ℓ¹` perturbations below `c/(L²cosh δL)` keep it at `L/2`: hiding at the density aperture is a ridge of
  width `e^{−δL}`. Smoothly tapered packets of peak depth `¼` with RvM counts hide up to `a ≍ log T`.
- **Height.** Configurations equal below `T ≍ exp(e^{2δa}/(Cδ))` have opposite window signs at `a`.

So windows read depth, coherence and crystallinity; the camera reads density. Isolated deep zeros are seen at
log-log apertures and doubly exponentially high; the height reach free of shielding hypotheses is single
exponential, sharp by tapered crystals. A contact law at scale `c log T` is a zero-location statement: it
forces every unshielded lowest off-line zero to depth `≲ log log T/(c log T)`. Combined with the local camera,
the half-carrier law would make every `T^{−M}`-isolated off-line zero of `ζ` near `T` visible at half-width
`(1 + ε)L_T` at any depth (B48); what stays hidden is near-coincident clusters below the camera's isolation
scale and smooth off-line sheets [D].

### 1.12 Criticality: no slack anywhere
Weil cone `{Λ}`; lattices Szegő singular under RH; reflection coefficients freezing at `±1`; aperture floor
doubly-exponentially small; theta gauges critical on the line; extremals never smooth; heat path real at
`t ≥ 1/8`, non-real at every `t < 0`; PM defect vanishing only at `δ = 0`; hiding of off-line lattices on a
ridge of width `e^{−δL}` [P]; size-only heat domination ending at `½/log X`, where heat times begin to carry
zero information [P; D]; numerical margins `1.5×10⁻⁵` (odd) and `5.6×10⁻⁸` (even) at `c = ½log 3` [N]. Every
exact reading of RH sits on a zero-slack boundary: a proof must be an identity at the boundary, not an
inequality with room [D]. Real-rootedness is a closed condition (Hurwitz): a locally uniform limit of strictly
stable approximants reaches the boundary without slack (2.7) [D].

### 1.13 Counts, Hodge index and degeneration are closed as an RH mechanism
Bare domination ⇔ `Q ≥ 0`; no Gamma–pole family dominates the Tate counts; every concrete count type is
excluded; below `log 4` Künneth effectivity is the window sign itself [L]. The degree-zero height principles
(bounded-above Rosati forms are `≤ 0`, sublinear-error comparisons are exact) are exactness tools, not
producers [L: KPA]. Conclusion [D]: counts cannot close RH.

### 1.14 Selection and minimal input
Selection after positivity is automatic (Weil cone `{Λ}`; lattice selection; fakes caught at their first
prime) [L]. A positive measure with Riemann's FE is the counting measure of `ℕ`; positive primes with
regular integers allow off-line zeros; Selberg-class Euler rigidity at `σ = ½`, degree gap, degree one with
conductor `≥ 2` or a pole [L]. RH ⇔ the Legendre invariant is real at every zero — a reformulation [L]. A
proof uses the functional equation and the Euler product together.

### 1.15 Precision and density
Near-line density is one statement in eight forms; `D_win` ⇔ thin Planck shadows; `D_zero` ⇔ `D_win` +
vanishing cluster tail [L: CDG]. The WD cap `σ_m = 1 − 1/(116log(m+5))` is the classical zero-free region
[L]. The gauge torus has pole-subtracted exponent range exactly `[Θ, 1]` [L]. Simple-critical proportion
`≥ 0.67250071` (imported Zeta23 inputs) [L].

### 1.16 What is ruled out
| Mechanism | Verdict | Anchor |
|---|---|---|
| Fold paid as a cost | refuted at the first prime | `#frozen-gamma-cubic` |
| Lossless lower forms of the odd unit window | refuted | `#retained-gamma-lower-form`, `#first-fold-linear-chord` |
| Markov ground states; folded supersolutions | dead beyond `e^{−3/4}`; void on the unit odd window | `#prime-free-markov`, `KR-BD`, `#folded-markov`, `#folded-origin-charge` |
| Certificates without the pole variance | refuted for `c > 273/400` | `#variance-dropped-theta-gauge` |
| Nonnegative even theta-gauge cosh certificates | refuted | `#theta-gauge-cosh-defect` |
| The prime `3` carried by its collar size | refuted for `c ≥ 287/500` [W] | `#prime-three-sliver-potential` |
| Collar-local payment of every kick | fails at the prime `3` | `#collar-local-payment`, `#collar-positivity-induction` |
| Smooth extremals / smooth zero modes | none exist | `#smooth-window-attainment` |
| Lossless local allocation | refuted | `KR-LGP` |
| Finite-square / finite-rank identities and realizations | refuted | `#fold-count-identity`, `#finite-window-realization`, `KR-FPR` |
| Slack (uniform floors, lattice slack, Gram floors, full-horizon reference floors) | refuted | `KR-PAF`, `#lattice-positive-slack`, `#growing-overlap-floor`, `#full-conductor-diagonal` |
| Counts / Tate domination / Hodge index from counts | closed [D] | 1.13 |
| Size-only layers as Weil information | blind | `#fixed-packet-bulk`, `#twisted-horizon-blindness` |
| Low-conductor deletion, raw-cost charge control, vanishing complement coupling, absolute pole-collar budget | refuted | `#low-conductor-deletion`, `#prime-pole-cost`, `#charge-complement-vanishing`, `#critical-pole-collar-budget` |
| PM line selectors | refuted or side-only | `#lewis-inversion`, `#farey-three-term`, `#mayer-krein-sign`, `#resonant-cutoff-gram`, `#scattering-schur`, `#scattering-recentering` |
| Bounded operator symmetry for the PM reflection off `Re s = ¼` | refuted | `#cauchy-reflection-order` |
| Selectors without positivity; bounded apertures against Euler columns | blind | Γ16; ZCG [L] |
| Pole matching as half-power input | refuted | `#pole-matching-half-power` |
| First Laguerre inequality as a reality certificate | refuted | HTGeometry [L] |
| Fixed cross-load for theta rank 9 | refuted at `q = 8` [W] | `#theta-fixed-cross-load` |
| Fixed-aperture / finite-horizon positivity as a decision | refuted | `KR-CRT`, `#finite-readings` |
| Two-configuration local inversion below aperture `L_T` (`½ < λ ≤ 1`) | refuted: the on-line lattice of `ζ`'s density and its half-shift | `zcg-square-root-local-inversion`; ZCG [L] |
| Size-only heat domination as zero information (sub-Weyl, Bourgain, Lindelöf) | blind on `[½, 2/3]/log X`, impossible below `½/log X` | `zcg-heat-scale-source-repulsion` [P]; [D] |
| Height induction; a contact law at scale `c log T` as a proof step; deciding a window from the zeros below a height | refuted (height non-locality) | `window-visibility-onset-law` [P] |
| Spread hiding at the density aperture as a general law (Π29) | refuted off an `e^{−δL}` crystalline ridge | `window-visibility-onset-law` [P] |
| `πD/2` certification for mixed columns | refuted for genus `g ≥ 2` | `window-visibility-onset-law` [P] |
| Doubly exponential height reach without shielding hypotheses | refuted (tapered crystals) | `window-visibility-onset-law` [P] |
| The camera as a producer | identification complete and sign-free; decides nothing alone | 1.9 [L; P; D] |

### 1.17 The live mechanism classes
| Class | Statement | First open test | Status |
|---|---|---|---|
| P1 signed criticality | primes pay the prime-free deficit by the signs of their sliver reflections, pole variance retained | below `log 4` (two weights); the odd unit window (one weight); below `log 5` (the size-subordinate regime) | live; certificate format exact; cost-only, Markov, variance-free, size-only certificates excluded |
| P2 prime-blind positivity | archimedean + pole part `≥ 0` on signed blind combinations | finite-level cones `C_A`, `A ≤ log 6` | live; solved on nonnegative and separated cones |
| P3 PM reflection | an arithmetic expression of `D_s(ψ_s)` with manifest sign | a PM-native zero-free region for `ζ(2s)` | reduced to the identity `δ = 0` |
| P4 square-root cancellation | the band in prime form for one smoothed count | — | live; classical; parity barrier |
| P5 reality by continuation | no collision along a source-faithful path | heat path on `(0, ½/log X]` near height `X` | receiver: a zero-free region in heat coordinates; size-only domination closed (blind above `½/log X`, impossible below) |
| P6 arithmetic stability | real-rootedness of `ξ` as a limit of stable objects from Euler and Gamma data, by stability preservers | `J^{3,n}` without a semicircle factor; a half one-sided below `½/log X` | undeveloped producer; Hermite–Biehler instances above size horizons [L; P] |

### 1.18 The receivers are complete; the producers are open
Three receivers turn statements about the image into statements about zeros, uniformly in height: the
camera (identification at cluster density `2a/π`, local, `T^{−M}`-precise, sharp at `λ = 1` for two
carriers) [L; P; W]; the onset law (window sign ↔ depth, coherence, crystallinity) [L; P]; the heat path
(collision ↔ zero depth, simplicity ↔ phase speed of a half) [L; P]. None produces: the camera is sign-free,
the onset law is a dictionary, and size domination is blind on its whole reachable range. They leave the same
three residues in every family: near-coincident clusters below the isolation scale (B44), smooth off-line
sheets (B50), and zero depth near the line at the level of a zero-free region (B49). A closing argument needs
one producer: Weil's sign on windows of length `≍ log T` (P1, P4), an arithmetic second expression of the PM
defect (P3), a Hermite–Biehler half below `½/log X` (P5 as receiver of P4 or P6), or a stability limit (P6)
[D].

## 2.1 Obstacles that are just work

| # | Task | Routes served | Why it is work |
|---|---|---|---|
| A1 | Explicit constants and horizons: `K₀`, eighth-root theorem, `1/9`, logarithmic profile, Beurling schedule, horizon criterion, conductor range `M(N) = o(c_N)` | HF, SRT, AIP, ACS, SC | effectivization of proved limits |
| A2 | General profiles past `θ = 1/1080` | HF, SRT, SC | tilted-spline template |
| A3 | Joint twist families; equal-parity characters; different moduli | HF, SRT, AHD | single-family proofs are templates |
| A4 | Certified ratio interval at its size-only optimum; receiving-charge complement inside it | HF, AIP, SRT, CSAR | assembly of proved estimates (difficulty unverified) |
| A5 | Rigorous computer-assisted certificate of `(w₂, w₃) ∈ belowLogFourBandWeights c` on `(enlargedWeilFloorAperture, log 2)`; the odd unit window as its first case | RW, OWU, EWU, ACT, GWZ, SWC | an operator inequality on `L²[−c, 0]` with explicit kernels; decides cases, not the mechanism; margins `~10⁻⁵–10⁻⁸` [N] |
| A6 | Rational Hecke graphs and Tate horizons of stages 3, 4, 5, 7, … | WTZ, CWS | finite graphs |
| A7 | Closed form of the first-stage complement `Φ_ε` | GWZ, CSTW, WTZ, RW | explicit archimedean Schur complement |
| A8 | Even-sector cosh-credit supersolutions with retained variance | EWU, RW, SWC | mirror of the odd retained-variance identities (difficulty unverified) |
| A9 | AIP channel norms: literal prime bands, small multipliers, offset-dividing primes, offset cardinality, periodic errors | AIP | size estimates with the proved sieve bounds (difficulty unverified) |
| A10 | Window index as a function of the length | AHD, SRT, CWS | conditional calculus |
| A11 | Function-field calibration | AHD, ACS, SC, HF | the sign is known there |
| A12 | Gaussian-damped coupling identity | SC, ACS | explicit formula |
| A13 | Finite-level Weil cones `C_A` and their widths | PBAP, ACS, RW | finite convex programs, Farkas duality in place |
| A14 | PM classical identifications; mixed-parameter completion; Mayer transfer compatibility; boundary carrier; rational Weyl identification | PM, W1C | known theories |
| A15 | Operator-native nonvanishing on `Re w = 1` | PM | Eisenstein template (risk: reduces to the Euler product) |
| A16 | Formalize the camera–visibility–heat package: sub-spacing inversion at `T^{−M}`, the symmetric-half collision law and the four-piece horizon, the onset laws (coherent, cubic, split columns, crystals, tapered packets, height non-locality) | ZCG, WindowVisibilityLaw, SRT | paper proofs complete [P]; modules in progress [W] |
| A17 | Theta rank 9: a variable cross-load or other repair on the compact source gap; ranks `≥ 10` at fixed apertures | TH | finite-dimensional sign on a compact parameter set (difficulty unverified) |
| A18 | Hausdorff shifts, Jensen horizons, two-grid degrees, PF beyond 37 | PA, LA, HCF | effectivization |
| A19 | Nine atom-dominated collar moduli | ACT | finite case analysis |
| A20 | Mixed Schur debit; first-prime/coarse/polar costs | AIP, CHMD | fixed-dimensional estimates |
| A21 | Logarithmic two-point Chowla | MC | Tao's theorem |
| A22 | Björner wedge decomposition | MC, HF | classical topology |
| A23 | Depth law, star horizons, gcd strata | HF, ACS | effectivization |
| A24 | Census items; Voronoi; Zwegers | census, ACS, HF | classical |
| A25 | Künneth primitive `h¹` at small degree; mixed jets | ACS, WL | calibration |
| A26 | WD composition; Vinogradov–Korobov cap in place of `σ_m` | WD, LA, TG | classical zero-free region |
| A27 | Cluster-detector constant | SRT, WD | constants |
| A28 | Atomic-lattice bound `λ_max ≤ ½log N` | WTZ, HF | classical |
| A29 | Bridge: reflection-pair coupling = smoothed count → WL/JAS/CTF/PBM/RB receivers | WL, JAS, CTF, PBM, RB, GWZ | composition of proved identities |
| A30 | Two-site band on a bounded step range from numerical zeros | GWZ, WL | computation; decides nothing |
| A31 | Selberg-class degree-one classification | ACS, SEL | known theorem |
| A32 | Receivers marked unfinished: Cayley–Li primitive sign, SZ first-variation transfer | LI, SZ | statements in place |
| A33 | Lévy sector margins at `c = ½log 3` in both sectors | RW, OWU, EWU, SWC | numerical; feeds soft entry |
| A34 | Camera isolation below `T^{−M}`: the window floor costs `D(1 + log D)log(1/η)` against `(1 + R)^{2k}`, with `k` limited by the bump constant `(4(1 + m/ε))^m` | ZCG | effectivization (difficulty unverified) |
| A35 | Four-piece heat horizon with sharper sub-Weyl exponents (`μ(½) ≤ 13/84` and successors) | P5, ZCG, RHTower | effectivization; carries no zero information above `½/log X` [D] |

## 2.2 Open mathematical obstacles

### Σ — critical sign
| # | Problem | Strength | Routes |
|---|---|---|---|
| B1 | Weil's sign on windows of every length (≡ band on every reflection pair ≡ Stieltjes moments of jet energies ≡ `R₁ ≡ ⊤` ≡ `ι = 0` ≡ Krein positivity ≡ PBAP) | RH; fixed length sub | all sign routes |
| B2 | Kick admission at every stage | RH as induction; each stage sub | RW, GWZ, CSTW, WTZ, HF, SZ |
| B3 | Frustration domination: a gauge with retained pole variance in which the signed sliver reflections of all acting prime powers pay the collar Hankel form, odd and even | RH; fixed length sub | P1 routes |
| B4 | Structural certificate of the odd unit window (`w₂ ∈ unitBandWeights`) | sub | OWU, RW, TT, SWC |
| B5 | Structural certificate below `log 4`: the arithmetic point in `belowLogFourBandWeights c`, the prime `3` paid by sign | sub | RW, OWU, EWU, ACT, TT, SWC |
| B6 | Twisted-sector positivity through all conductors and frequencies at every multiple | sub | HF, SRT, AIP, AHD |
| B7 | Full-space sign at critical ratios beyond the size-only threshold | sub per ratio; RH for all | HF, SRT, AIP, CSAR |
| B8 | Full-space positivity of general profiles past `log log N` | sub | HF, SRT, AIP, SC |
| B9 | Exact SOS on one two-prime lattice | RH | HF, SC, ACS |
| B10 | No zero mode at any length | RH | HF, TG, SC, EHT, GWZ |
| B11 | Top coprime stratum | RH | HF, ACS, ADT |
| B12 | Index ceiling uniform in resolution | ≥qRH; RH (tensor) | CHMD, SRT, WD, SC |
| B13 | Zero–one law `κ ∈ {0, ∞}` | sub | SC, HF, ACS, CWS, SRT |
| B14 | Laguerre–Pólya at all ranks/degrees; collision exclusion along a source-faithful path (heat path: on `(0, ½/log X]`, the range that carries zero information) | RH | TH, LA, HCF, PA, GTA, XN, ZCG |
| B15 | Scheduled prime energies bounded below | RH | FU, CFC, RP, SZ, LI, FEL, EGC |
| B16 | Window negativity exponent `< ½` (≡ zero width `< ½`) | ≥qRH | window routes, HF, WD |
| B17 | Global continuum canonical system of the tower | identity | GWZ, CSTW, SZ, SWC |
| B18 | Contact law (RH to height `T` ⇒ windows of length `c log T` positive) | a zero-location statement [P]: unshielded lowest off-line zeros of depth `≲ log log T/(c log T)` | window routes |
| B48 | Local half-carrier visibility: every `T^{−M}`-isolated off-line zero of `ζ` near `T` makes a window of half-width `(1 + ε)L_T` negative (2.9) | sub | window routes, ZCG, SRT, WD |
| B50 | Smooth off-line sheets: `ζ` has no smoothly tapered or near-crystalline off-line packet (the hiding mode at the density aperture) | sub | window routes, ZCG, census |

### Π — precision and production
| # | Problem | Strength | Routes |
|---|---|---|---|
| B19 | Inner caps `[½, σ_m]` at every polynomial stage | RH; fixed degree ≥qRH | WD, TG |
| B20 | `100%` critical-scale clustering | sub | WD, census, MC, HEF |
| B21 | `D_win` ≡ thin Planck shadows; `D_zero` | sub | WD, census |
| B22 | Hecke defect pointwise / dyadic | ≥qRH / RH | WD |
| B23 | Distributional input beyond counts and moments | method | WD, HEF |
| B24 | Genus upper law | indep. | ACS |
| B25 | Logarithmic Serre duality, primitive part | sub | ACS, HF |
| B26 | `ε`-uniform producer; square-root source input | sub / RH | WL, MC, PBM, RB, JAS, CTF |
| B27 | First cyclotomic mode at square-root precision | RH | MC, WL, CAF |
| B28 | Signed pair information beyond bandwidth one | sub | census, ACS |
| B29 | First Epstein real zero on the boost line | sub | ACS |
| B30 | Bounded damped cone coupling; unattained width | RH | SC, ACS |
| B31 | Finite-sieve Hodge positivity → global | RH | SC |
| B32 | Half-power law at the trivial gauge point | RH | MC, WL |
| B33 | HF-native arithmetic sign: the pencil beyond the size-only interval or the floor at `p = 1`, from primes | sub | HF |
| B49 | A Hermite–Biehler half below the size floor: `Q` from Euler and Gamma data with `H_t = Q + Q^#` and `|Q^#| < |Q|` off the line near height `X` for `t ∈ (0, ½/log X]` (2.6.5) | RH; one `τ = t log X < ½`: a zero-free region of depth `≈ τ` (pair model) | ZCG, P6, LA, census, WD |

### Γ — selection and reflection
| # | Problem | Strength | Routes |
|---|---|---|---|
| B34 | Rosati positivity of the window reflection | RH | HF, ACS, CWS, GWZ, PM |
| B35 | Band holomorphy of `Λ(s)/Λ(s+1)` | RH | HF, ACS, SC, PM |
| B36 | Selection at the trivial gauge point | RH | MC, BAG |
| B37 | FE twins inside the full class with off-line zeros | sub | HF, ACS, SC, SEL |
| B38 | An arithmetic expression of `D_s(ψ_s)` at resonances with manifest sign `≥ 0` | RH | PM, W1C |
| B39 | Resonant-state statistic selecting the decay rate | method | PM |
| B40 | Source-faithful realization of unbounded rank | RH | RN, PTR, W1C, PM |
| B41 | Pre-divisor forcing | RH | APF, BSH, CDC, EWJ, HJ, PCS, RFHM, SEC, WBF |
| B42 | Prime-blind positivity on signed blind combinations | RH | PBAP |
| B51 | Second-order local inversion uniform in height: equal images at aperture `(1 + ε)L_T` fix centre and squared gap of every near-coincident pair near `T` (2.5.5) | sub | ZCG, SRT |
| B44 | Reality at near-coincident clusters below the camera's isolation scale, at all orders | RH | ZCG, LA |
| B45 | Cross-tower gap through the archimedean channel | method | HF, AIP |
| B46 | PM-native zero-free region for `ζ(2s)` | sub | PM |

### P6 — stability
| # | Problem | Strength | Routes |
|---|---|---|---|
| B52 | A finite free factorization `J^{3,n} = p_n ⊞_3 q_n` without a semicircle factor, with real-rooted pieces from Gamma and prime data for every `n` — or its impossibility | method | P6, LA, TH |
| B53 | A stability-preserving limit of Euler stages: stable halves of `ξ` whose horizon does not recede with the height | RH | P6, ZCG, census |

### Settled questions (classified; not obstacles)
| Question | Answer | Anchor |
|---|---|---|
| What is the sign below `log 4`? | membership of `(Λ(2)/√2, Λ(3)/√3)` in an explicit compact convex set | SWC [L] |
| Where does the half-window first meet a prime lag? | at `c = log 2`, sharp | SWC [L] |
| Must certificates keep the pole variance? | yes; variance-free certificates fail for `c > 273/400`; retained ones are exact below `log 4` | SWC [L] |
| Can the prime `3` be paid by its size? | no: collar potential fails for `c ≥ 287/500`; soft entry reaches `δ ≤ 0.12` only | SWC [W]; [D] |
| How large are the kicks? | `{2,3}` `< ¾` Lévy; all kicks `< ` Lévy on windows `< log 5` | SWC [L]; [D] |
| What is a sector? | a Hamburger (even), shifted Hamburger (odd) moment problem; the window a Stieltjes problem | SWC [L] |
| Are window extremals smooth? | never | SWC [L] |
| Where does the lattice canonical system live in the continuum limit? | on the boundary `(−1)^n` of the Schur disk, normal velocities `e_{n+1}/e_n` | SWC [L] |
| Can a Markov supersolution certify a window longer than `e^{−3/4}`? | no | SWC [L] |
| Is the complete family positive on the whole space at one critical multiple? | yes; size-only | CACT, AHD [L] |
| What is the terminal source? | polar; nonpolar parts cancel; correctors cannot improve zero-source windows | AHD, CACT [L] |
| What decides HF? | `R₁(A) = ⊤` for every `A` | AHD [L] |
| What does the aperture-independent floor say about zeros? | nothing beyond width `≤ p` | WTZ, SquareRootThreshold [L]; [D] |
| What is the PM defect? | `−∫2cosh(δu)4sinh²(δu)|F(u)F(−u)|`: its sign is `δ = 0` | RIT [L] |
| Does the retained Hecke channel select the line? | no; it reads the side | RIT [L]; [D] |
| What does blindness cost? | exactly `π` times the density | ZCG [L] |
| When do clusters cancel? | only at upper uniform density `≥ 2a/π` | ZCG [L] |
| When is a fake caught? | exactly above aperture `½log n₀` of its first differing integer | ZCG [L] |
| Does positivity at one aperture certify? | thin configurations above `πD`; split columns above `πD_on + (π/2)D_off`, sharp for mixed columns | SquareRootThreshold [L]; `window-visibility-onset-law` [P] |
| What is the square-root threshold? | `λ = ½` (units `L_T`) for clusters of `ζ`'s density; `λ = 1` for two carriers of that density, sharp | ZCG [L; P] |
| Where must heat collisions be excluded? | `t ∈ (0, (6600/9991+ε)/log X]` near height `X`; zero information only in `(0, ½/log X]` | RHTower [L]; `zcg-heat-scale-source-repulsion` [P]; [D] |
| How does purity survive over `𝔽_q`? | closed, lost only at Frobenius collisions; integral configurations collide or repel | ZCG [L] |
| Do Euler stages have real line zeros? | above their horizon `2πe^{W(X)}`, all simple | ZCG [L] |
| Is the window algebra Frobenius-bearing? | no; Frobenius at scale `t` is translation | DZG, RIT [L] |
| Does positive dimension supply positivity? | no | ATD, DZG [L] |
| What does the fall rate of the window ground energy read? | the zero width (bounded clustering); two-sided for finitely many off-line zeros | SquareRootThreshold [L] |
| How high do windows see? | isolated deep zeros: doubly exponentially high, depth `δ` at half-width `≈ (1/2δ)log log T`; general configurations: single exponential `e^{Ca}`, sharp by tapered crystals | DCI [L]; `window-visibility-onset-law` [P] |
| Does the pole decide the half-power law? | no | AGT [L] |
| Where does local inversion hold? | for clusters of `θ` times `ζ`'s density at aperture `λL_T`, `λ > θ/2`, at every `T^{−M}`-isolated point, uniformly in `T` | ZCG [P; W] |
| Do the zeros of `ζ` fix their mimics? | at aperture `λ log X`, `λ > ¼ + πμ/2`, for mimics of density `μ log X`, at every `exp(−κ log X/(1 + log log X))`-isolated point | ZCG [L] |
| What is the onset law of window negativity? | deep `(1/2δ)log(CδL/k)`; shallow `(L/(kδ²))^{1/3}`; split columns `πD_on + (π/2)D_off`; crystals `L/2` on a ridge of width `e^{−δL}` | WindowVisibilityLaw [L; P] |
| Does window positivity control shallow clusters? | yes: `Σmδ² ≤ CA₀log T/a²` per unit window | `window-visibility-onset-law` [P] |
| Is hiding at the density aperture a general sign law? | no: an `e^{−δL}` crystalline ridge; smoothly tapered packets hide up to `≍ log T` | `window-visibility-onset-law` [P] |
| Can a window be decided from the zeros below a height? | no: configurations equal below `T` have opposite window signs | `window-visibility-onset-law` [P] |
| What is simplicity of a zero of `H_t`? | nonzero phase speed `Re(D₀ conj Q_t)` of the symmetric half | `zcg-heat-scale-source-repulsion` [P] |
| Where does size-only heat domination stop? | at `½/log X`: the Gaussian saddle enters the strip; the pair model collides at `t* < δ/L` | `zcg-heat-scale-source-repulsion` [P] |
| What does `Λ_X` measure? | in the pair model `Λ_X log X` is the depth of the deepest zero near `X` | [D] |

## 2.3 Frankenstein routes

**Verdict: no assembly closes RH.** Every assembly ends at one named residual, and the residuals are the
three core walls in exact form. Three assemblies sharpen what a closing piece must be (F2, F7, F10).

### F1. The gauge–tower assembly (P1)
| Segment | Supplied by | Status |
|---|---|---|
| RH ⇔ windows ⇔ reflection pairs ⇔ sectors ⇔ moment problems | CWS, GWZ, SWC | [L] |
| Base through length `0.7240`; first stage rejects `0` and the flip | SPATL, GWZ, SWC | [L] |
| Pole kept; variance retained; exact certificate format below `log 4` | SWC | [L] |
| Sliver signature, outward edge, soft entry, weight confinement | SWC | [L] |
| Stage criterion; Levinson admission; continuum limit at the Schur boundary | GWZ, CSTW, SWC | [L] |
| Core: the signed reflections pay the collar Hankel form in every stage | — | B3 (RH); first instances B4, B5 |

It bypasses conductors, dimension zero, counts, density and PM. It does not bypass exactness.

### F2. The multiscale assembly with margin transport (P1 ⊕ P4)
Idea: pay the kicks inside their collar-certified range locally, carry each newest prime across its entry
by soft entry, and pay the older primes by window positivity at a smaller scale.

| Segment | Supplied by | Status |
|---|---|---|
| Local payment at ratio `2w_ne^h` (collar) or `w_ne^h/2` (outward edge) | SWC | [L] |
| Soft entry with tolerance `ηΩ(δ)` | SWC | [L] |
| All kicks on a reflection pair = smoothed prime count in `𝒞_m` | SWC | [L] |
| Window positivity at half-width `a` bounds prime sums with autocorrelation kernels at scale `a` | CWS | [L] |
| Bridge to cross-correlation kernels `(f⋆f)(2m − ·)` at scale `2a` | — | missing: by polarization it is the band at scale `2a` [D] |

Residuals: margins decay doubly exponentially in the length, and soft entry covers slivers `δ ≤ 0.12`
even at margin `η = 1` [D], so margin transport cannot replace the sign; the doubling step breaks at
polarization. The missing bridge is the band itself (B1).

### F3. The complete-family assembly (blind)
Subcritical PD + whole space at one critical multiple + threshold law + joint pole + terminal source polar
[L]. Complete at small ratios, without Weil information there; beyond the size-only threshold it lands
on B7, at every ratio on `R₁ ≡ ⊤` = B1.

### F4. The reflection assembly (P3)
PM exact completion + window involution + window lift of tests + defect formula + retained channel [L].
Residual: the defect at resonances is `−(positive)·sinh²(δu)`-weighted; its vanishing is `δ = 0`. The
assembly needs a second expression of the same defect with manifest sign (B38); the retained channel,
antisymmetric under reflection, cannot supply it.

### F5. The camera–continuation assembly (Γ ⊕ P5)
| Segment | Supplied by | Status |
|---|---|---|
| Heat path real for `t ≥ 1/8`; RH ⇔ `Λ_X = 0` ∀X; collisions near `X` lie in `(0, (6600/9991+ε)/log X]` | RHTower, ZCG | [L; P] |
| Reality lost only through collision; heat steps keep mesh and depth (model) | ZCG | [L] |
| Simplicity = phase speed of the symmetric half `Q_t` | ZCG | [P] |
| Local camera uniform in height, `T^{−M}`-precise, sharp at `λ = 1` for two carriers | ZCG | [L; P; W] |
| Reality at a near-collision = sign of the second-order coefficient read through `(log n)²`-weighted primes | ZCG | [L] |
| Repulsion: integrality (`𝔽_q`), phase speed above the Euler-stage horizon | ZCG | [L] |
| Core: a Hermite–Biehler half below `½/log X` | — | B49 (RH) |

It bypasses positivity of Weil's form and counts. Residual: in heat coordinates the core is a zero-free
region — in the pair model `Λ_X log X` is the depth of the deepest zero near `X` — and size-only domination
is blind on `[½, 6600/9991]/log X` and impossible below `½/log X` [P; D]. The camera supplies identification
only; the producer must be a cancellation of the Euler product inside the strip (P4) or a stability limit
(P6).

### F6. Density–index–cluster (WD ⊕ AHD ⊕ CWS ⊕ AKLT ⊕ SRT)
Off-line zeros live in density-zero window sets, are seen at aperture `≍ log|γ|log log|γ| + 1/δ`, each
raising the window index [L]. Residual: index ceiling and zero–one law (B12, B13): ≥qRH.

### F7. The aperture–depth assembly (Σ ⊕ Π, windows ⊕ near-line density)
| Segment | Supplied by | Status |
|---|---|---|
| Fall rate of the window ground energy = zero width; doubly exponential height reach for isolated zeros | SquareRootThreshold, DCI | [L] |
| Window positivity at half-width `R` ⇒ no zero of depth `≥ 1/R` below `exp(R/polylog R)` | SquareRootThreshold | [L] |
| Onset law: deep `(1/2δ)log(CδL/k)`, shallow `(L/(kδ²))^{1/3}`, depth mass `Σmδ² ≤ CA₀log T/a²`, crystals | WindowVisibilityLaw | [L; P] |
| Shallow zeros: near-line density at depth `A/log V` | CDG | B21, B22 |
| Verified zeros to a finite height | numerical | [P] |

Idea: let the windows exclude the deep zeros (cheap: length `≈ (1/δ)log log T`) and let near-line density
control the shallow ones. Residual: below length `log T` windows are blind to isolated zeros of depth
`≲ (log log T)/a` and see shallow coherent clusters only through their depth mass; controlling the shallow
ones at every height with no exceptional windows is WD's pointwise Hecke-defect problem (B22: pointwise ≥qRH,
dyadic RH). At length `≍ log T` the residual is B48 and the two hiding structures (B44, B50). Height
induction fails at its first step: configurations equal below `T` have opposite window signs [P].

### F8. The moment-problem assembly (SWC ⊕ TH ⊕ LA)
| Segment | Supplied by | Status |
|---|---|---|
| Window ⇔ Stieltjes moments of `s_k = W(φ^{(k)})` for every even bump | SWC | [L] |
| Theta Hankel towers PD through rank 8 at every centre; PSD reduced to native moment tails | TH | [L] |
| Fixed-degree Jensen polynomials eventually hyperbolic | LA | [L] |
| Core: a representing measure built from prime data | — | B1 (the measure is the zero-side measure: Γ8) |

It shows what the output of a proof is: a positive measure on `[0, ∞)` for every even bump. The finite
unconditional ranks (TH) concern the theta source at one centre, not window bumps, and do not transfer.
Residual: zero-side positivity (Γ8).

### F9. The Hermite–Biehler assembly (ZCG ⊕ census ⊕ canonical systems)
| Segment | Supplied by | Status |
|---|---|---|
| Euler stages `A_X(s) + A_X(1−s)`: simple line zeros, phase lattice above the horizon | ZCG | [L] |
| Heat source `H_t = Q_t + Q_t^#`: Hermite–Biehler above `(6600/9991)/log X`; simplicity = phase speed | ZCG | [P] |
| A decomposition `ξ = A(s) + A(1−s)` with `|A(1−s)| < |A(s)|` right of the line ⇔ RH | classical | [D] |
| Levinson–Conrey counting of zeros of such an `A` of Riemann–Siegel length (`λ = ½`) | census, IGP | [L] |
| de Branges / canonical-system organization | GWZ, CSTW | [L] |
| Core: a Hermite–Biehler half at `ζ`'s scale without a size horizon | — | B49, B53 |

Residual: every half in the corpus is one-sided above a size horizon (Euler stages: `2πe^{W(X)}`, receding;
heat source: `0.6606/log X`, floor `½/log X`) or on a proportion of the zeros only (Levinson–Conrey,
`≥ 0.6725` simple critical). The assembly is the one-variable form of P6.

### F10. The camera–visibility assembly (Γ ⊕ Σ)
| Segment | Supplied by | Status |
|---|---|---|
| Local camera: isolating window pairs with explicit far tail, `T^{−M}`-precise, uniform in `T` | ZCG | [L; P; W] |
| Half-carrier law: isolation from the right half of the carrier ⇒ a negative window | WindowVisibilityLaw | [P] |
| Onset dictionary `a*(Z)`; RH ⇔ `a*(ζ) = ⊤` | WindowVisibilityLaw | [L] |
| Local half-carrier visibility for `ζ` at half-width `(1 + ε)L_T` | — | B48 (sub) |
| Core: window positivity at lengths `≍ log T` | — | B1 at those lengths |

Residual: B1. The assembly shows that windows of length `≍ log T` and the camera see the same zeros, and that
what neither sees is B44 and B50.

## 2.4 A wildly different route

**Verdict: no route that avoids all three walls is visible.** Every route reads the zeros through the
explicit formula or through a function whose divisor is that of `ζ`; the three walls are the three
components of that formula — sign of the zero side, size of the prime side, identification between them.
The corpus covers positivity, precision, realization, deformation, recurrence, counts, function-field
transfer, quasicrystals, Lee–Yang, moment problems and Hermite–Biehler phases.

The farthest mechanism not developed in the corpus (the search tool returns nothing for it) is the producer
of the field proposed in 2.7:

**Real-rootedness from finite free probability (interlacing families).** Marcus–Spielman–Srivastava: the
expected characteristic polynomial of a sum of independent random rank-one PSD matrices (a mixed
characteristic polynomial) is real-rooted, by real stability and barrier arguments; finite free
convolutions preserve real-rootedness (`⊞_d` always, `⊠_d` with one factor of nonnegative roots); `E det(x − GUE_d)` is the Hermite polynomial. The Jensen
polynomials `J^{d,n}` of `Ξ` are real-rooted for all `d, n` iff RH (Pólya), each fixed degree is eventually
real-rooted [L: LA], and they converge to Hermite polynomials as `n → ∞` [P: Griffin–Ono–Rolen–Zagier]. A
route would realize every `J^{d,n}` as a finite free convolution or mixed characteristic polynomial of
real-rooted pieces built from Gamma and Euler data.
- What is far: no quadratic form sign (Σ), no square-root count (Π), no reflection or Krein positivity
  (PM). Real zeros come from real stability. An expectation over a family is not a single finite object,
  so the finite-realization no-gos (`KR-FPR`, finite graph and virtual-graph realizations) do not apply.
- Where it meets the walls: (i) criticality — the entire-function limit of `⊞` with a semicircle is the
  heat flow, and `H_t` is non-real for every `t < 0` [L], so `Ξ` is not a positive-time heat flow of a
  real-rooted function: a factorization may carry no Gaussian component in the limit [D]; (ii) source faithfulness — the pieces must come from primes and
  Gamma, not zeros (Γ5); (iii) the coefficients of `J^{d,n}` are moments of `Ξ`'s Fourier kernel, so a
  `⊞`-factorization is a nonlinear identity among the moments of C22.
- First test: degree `d = 3`: real-rooted `p, q` of degree `3`, built from explicit Gamma/prime data, with
  `J^{3,n} = p ⊞_3 q` for every `n` — or a proof that no semicircle-free factorization exists, which would
  close the mechanism.
- Where it meets the corpus: a Hermite–Biehler half is one-variable real stability; Euler stages [L] and the
  heat source [P] are such halves above size horizons, and Levinson–Conrey halves on a proportion [L].

The multivariate stability direction (self-reciprocal stable Dirichlet polynomials on the prime torus) is
in the corpus: the two-prime Lee–Yang family has all zeros on the line and zeros that are not zeros of `ζ`
[L], and the archimedean factor is not multiplicative in the primes.

## 2.5 Breakthrough questions below RH and quasi-RH

### 2.5.1 Whole programme — the global canonical system of the tower
**Question.** Construct, from the explicit formula, the continuum canonical system of the window tower:
Krein's reflection function `A(L)` (the continuous analogue of the lattice Schur parameters) of Weil's
translation-invariant kernel on `[0, L]`, with its singular structure at the prime-power lengths
`L = log n`, such that the window of length `L` is positive iff the system has no blow-up on `[0, L]`.
- **Below RH.** An identity: it constructs the object whose regularity is RH; it decides no sign.
- **Why it is not settled.** The lattice system (Levinson, Schur parameters) and the local continuum limit
  (jet Hankel system, reflection coefficients freezing at `(−1)^n`) are proved [L]; the global system with
  the prime kicks is not constructed (B17); Krein's theory needs nondegenerate truncations, which hold up
  to the first failure.
- **Advance.** One object carrying the lattices, the jets, the sectors (as the two parity blocks), the Krein
  structure of PM and the Krein–Schur carrier of SZ; every stage step becomes a local statement about
  `A(L)` across `L = log n`; the onset law (1.11) becomes the blow-up time of the system as a function of
  the zeros.

### 2.5.2 Route PM — a zero-free region owned by the Lewis–Hecke carrier
**Question.** From the three-term equation, modular inversion, the Hecke eigenrelations
`T_pψ_s = (1 + p^{1−2s})ψ_s` and the defect formula, prove an upper bound on `|D_s(ψ_s)|` relative to its
cross mass `∫u²|F(u)F(−u)|` that excludes resonances with `Re s > ½ − c/log|Im s|` (zeros `ρ = 2s` with
`Re ρ > 1 − 2c/log|γ|`).
- **Below RH.** de la Vallée Poussin strength.
- **Not ruled out because.** Every killed PM mechanism is a line selector; none concerns the size of the
  defect. The defect is `≈ −8δ²·(cross mass)` [D], so a size bound is a depth bound. Risk: the cone counting
  behind `1 + p` is the Euler product (A15).
- **Advance.** The first sign-bearing statement PM owns.

### 2.5.3 Route WD — log-free window occupancy
**Question.** Prove `D_win`: for every `A > 0` at most `ε(A)V` unit windows of `[V, 2V]` contain a zero of
depth `≥ A/log V`, `ε(A) → 0`; equivalently, thin Planck shadows occupy `o_A(V)` windows [L: CDG].
- **Below RH.** A density statement.
- **Why it is not settled.** Selberg-type density counts `≍ e^{−cA}V log V` such zeros, more than the `V`
  windows; `D_win` is a clustering statement which counts and moments cannot give
  (`#window-density-separation`).
- **Window input.** Positivity at half-width `a` bounds the sub-depth mass of shallow coherent clusters by
  `CA₀log T/a²` per unit window [P: `window-visibility-onset-law`]; it gives no occupancy bound.
- **Advance.** WD's analytic input at the log stage on almost all windows.

### 2.5.4 Route HF — beat the size-only threshold with the primes
**Question.** Prove the critical pencil `a_φQ(H) + (7J(1)/R)M₈(H)` positive on every window at one explicit
ratio `R > jointPoleCriticalRatio`, using prime input in the receiving-charge complement (growing fibres,
literal prime bands). Floor form: `Q(H) ≥ −C∫e^{−pu}H²` at the edge exponent `p = 1`.
- **Below RH.** A fixed ratio is a finite statement; exponent `p = 1` gives only zero width `≤ 1`.
- **Why it matters.** Every HF layer proved is size-only; the terminal layer is polar and correctors cannot
  improve zero-source windows [L], so the only place left for arithmetic sign is the complement.
- **Not to be pursued.** Uniform floors along growing overlaps, bare counts through all conductors,
  low-block deletion, terminal correctors.

### 2.5.5 Route ZCG — second-order local inversion, uniform in height
**Question.** Two tempered configurations with Riemann–von Mangoldt local counts and equal images at aperture
`(1 + ε)L_T` have, on every pair of points closer than `T^{−M}` that is `T^{−M'}`-isolated from the rest of
the cluster (`M' < M`), the same centre and the same squared gap `w²`, uniformly in `T` (B51).
- **Below RH.** Sign-free.
- **Not ruled out because.** The squared gap is read linearly at second order at fixed aperture
  (`norm_pairSignal_add_sq_mul_secondMoment_le` [L]); the zero-order inversion is uniform in `T` with explicit
  windows (1.9); the second-order windows need the second moment `(u²f)^` at the pair, which the explicit
  spline bumps control (`exists_explicit_bump` [L]).
- **Advance.** `w² = −4δ²` for an FE pair of depth `δ` and `w² = g² > 0` for a real pair. The explicit formula
  at length `2(1 + ε)L_T` then expresses the reality of every near-coincident pair near `T` as the sign of an
  explicit prime-side quantity at the pair's scale — the `(log n)²`-weighted coalescent channel
  (`deriv_deriv_primeChannel_modulate` [L]) — uniformly in `T`: B44 in prime form.

## 2.6 Breakthrough questions that open the path to RH

### 2.6.1 Whole programme — exact collective payment
**Question.** On every reflection pair, write `W(f) − |𝒞_m(f)|` as a nonnegative signed Dirichlet form in a
gauge with retained pole variance plus nonnegative pole charges: a gauge family, exact on the line like the
theta gauges, whose restriction to every window pays the collar Hankel form by the signed sliver
reflections of all acting prime powers, in both sectors.
- **Why it opens the path.** It is B3, hence B1 and RH; the gauge calculus and the certificate format are
  exact [L], so only the domination is missing.
- **Constraints.** Variance mandatory; Markov dead past `e^{−3/4}`; collar locality sharp; soft entry a
  sliver mechanism; beyond `log 5` even the edge-law bound on the summed reflection terms exceeds the Lévy energy, so the payment becomes
  collective (P4); extremals edge-singular; margins `~10⁻⁸`; FE and Euler product both enter.

### 2.6.2 Route PM — a second expression of the defect
**Question.** At every resonance, express `D_s(ψ_s)` arithmetically — through finite cusp energy, Hecke
norms or a resonance identity — as a manifestly nonnegative quantity.
- **Why it opens the path.** The analytic expression `−∫2cosh(δu)4sinh²(δu)|F(u)F(−u)|` is `≤ 0` with equality
  only at `δ = 0` [L]; any second expression `≥ 0` forces `Re ρ = ½` for every zero. The retained channel shows
  arithmetic enters through `core_s(2) ≠ 0`; a second channel with a reflection-symmetric sign law would be
  the needed input.

### 2.6.3 Route WD — inner-cap cancellation
**Question.** On every Burnol unit window, at every polynomial stage, cancel the right-port flux through the
inner caps `[½, σ_m]` by a source identity.
- **Why it opens the path.** Across all degrees it is RH; at fixed degree the corridor `|β − ½| ≤ C/|γ|^k`
  [L]. It is the zero-free region pushed to the line by a window identity.

### 2.6.4 Route HF — the threshold stays infinite
**Question.** Prove `R₁(A) = ⊤` for every window length `A`.
- **Why it opens the path.** It is RH [L]. HF's content is P1 on untwisted windows at every multiple; the
  complement must be paid with sign at every ratio.

### 2.6.5 Route ZCG — a Hermite–Biehler half below the size floor
**Question.** Construct a half `Q` from Euler and Gamma data — the heat source `Q_t` mollified by a Dirichlet
polynomial, or a renormalized Euler stage — with `H_t = Q + Q^#` near height `X` and `|Q^#| < |Q|` off the
line for every `t ∈ (0, ½/log X]`, uniformly in `X` (B49).
- **Why it opens the path.** At every height and every `t > 0` it is RH (`Λ_X = 0`) [L]; the collision law
  makes reality automatic under domination [P]. At one fixed `τ = t log X < ½` it is a zero-free region of
  depth `≈ τ` in the pair model [D].
- **Constraints.** Size-only domination is blind on `[½, 6600/9991]/log X` and impossible below `½/log X`
  [P]; the twins are dominated above their horizon and tilted at every height, so `Q` must use cancellation of
  the Euler product, not its size (`twin_tilt_costs_weight` [L]); Davenport–Heilbronn must fail;
  Levinson–Conrey halves are one-sided on a proportion only.
- **First test.** One `τ < ½` on almost all unit windows near `X` (density form), compared with Selberg-type
  near-line density (difficulty unverified).

## 2.7 Does closing RH need a new field?

**Assessment: yes — an arithmetic stability theory: real-rootedness of `ξ` produced as a locally uniform
limit of stable objects built from Euler and Gamma data by stability-preserving operations, instead of by
size domination or by a sign.**

*Why this field.*
1. The receivers are complete (1.18). Identification is a density law, sharp and uniform in height (1.9);
   the onset law gives every window statement a zero meaning (1.11); the heat path ties collisions to zero
   depth (1.10). None of them produces, and size domination is blind on its whole reachable range.
2. Every producer the corpus has tried must hold with room at a boundary that has none (1.12): Weil's sign on
   windows, the PM defect, Hermite–Biehler domination as `t → 0`. Real-rootedness is closed under locally
   uniform limits (Hurwitz; the Laguerre–Pólya class), so a stability proof is a limit of strictly stable
   approximants whose slack tends to zero: it is compatible with exact criticality by construction.
3. The corpus holds stable approximants that fail only through size: Euler stages are Hermite–Biehler above
   `2πe^{W(X)}` [L]; the heat source is Hermite–Biehler above `(6600/9991)/log X` [P]; Levinson–Conrey halves
   are one-sided on a proportion [L]; the two-prime Lee–Yang family is stable on the prime torus with all
   zeros on the line [L]; fixed-degree Jensen polynomials are eventually hyperbolic [L]. By the
   Hermite–Biehler theorem a half `Q` with `F = Q + Q^#` and no zeros on one side is one-variable real
   stability. What is missing is an operation that carries the Euler product to the boundary without size.
4. It is the producer class compatible with ZCG's premise: no Weil positivity, no spectral input, no count.

*What it is about.* Halves `Q` with `F = Q + Q^#` (`F = H_t`, Euler stages, mollified `ξ`, Jensen polynomials
`J^{d,n}`) and the operations that keep their zeros on one side: multiplier sequences and Pólya–Schur
operators; Borcea–Brändén preservers in several variables, one variable per prime; finite free convolutions
`⊞_d`, `⊠_d` and mixed characteristic polynomials; locally uniform limits. Arithmetic enters through the
Euler product as a product of stable factors on the prime torus, the archimedean part through `Γ_ℝ`.

*Objects and language.* Hermite–Biehler halves and their phase speeds `Re(D conj Q)`; horizons of stages;
stability preservers and multiplier sequences; finite free convolutions, interlacing families and barrier
functions; stable Dirichlet polynomials on the prime torus; Jensen polynomials and their Hermite limits; the
Laguerre–Pólya class.

*Mechanisms it aims to discover.*
- A preserver carrying Euler stages of growing length to stable halves of `ξ` with a horizon that does not
  recede (B53).
- A finite free factorization of `J^{d,n}` without a semicircle factor, or an interlacing family with expected
  polynomial `J^{d,n}`, with pieces from Gamma and prime data (B52).
- A stable lift: a stable function on the prime torus × the archimedean line whose diagonal restriction is
  `ξ`.
- A mollified Euler–Gamma half that is one-sided below the size floor `½/log X` of the heat source (B49).

*Traps (settled in the corpus).*
- Size domination: blind above `½/log X`, impossible below it; the Euler-stage horizon recedes (1.10).
- Twins: dominated above their horizon, tilted at every height; a weight that grows like `log` of the height
  reaches their tilts (`exists_twin_tilt_beyond_every_weight` [L]). The mechanism must use cancellation of the
  Euler product, not its size, and must fail for the twins.
- Davenport–Heilbronn: functional equation, no Euler product, off-line zeros.
- Gaussian components: `H_t` is non-real for every `t < 0` [L], so a factorization of `Ξ` carries no
  semicircle factor in the limit.
- Lee–Yang restrictions: stability on the prime torus restricts to on-line zeros that are not `ζ`'s [L].
- Proportions: Levinson–Conrey one-sidedness holds on a proportion; counts cannot close RH (1.13).
- The first Laguerre inequality is no reality certificate; fixed-degree hyperbolicity is eventual only [L].

*Questions it must answer.*
- Does `ξ` lie in the closure of an explicitly arithmetic stable family, and which operation carries the
  Euler product into it?
- Is there a half of `ξ` from primes and Gamma, one-sided near every large height below `½/log X`?
- At which degree does a factorization of `J^{d,n}` without a semicircle factor exist, starting at `d = 3`?
- What replaces the receding horizon `2πe^{W(X)}`: a renormalized stage with a horizon uniform in `X`?
- How does a stability proof fail for the twins' tilts and for Davenport–Heilbronn's off-line zeros?

*Tools.* Hermite–Biehler and Hermite–Kakeya–Obreschkoff theorems; Pólya–Schur and Borcea–Brändén
classifications of stability preservers; Laguerre–Pólya class, multiplier sequences, Jensen polynomials and
their Hermite limits (Griffin–Ono–Rolen–Zagier); finite free probability (Marcus–Spielman–Srivastava: `⊞_d`,
`⊠_d`, interlacing families, barrier method); the de Bruijn heat semigroup; Levinson–Conrey mollifiers; the
corpus's symmetric halves, Euler stages and collision law; the camera and the onset law as dictionaries.

*Criteria a contribution must meet.*
1. Produce one-sidedness of a half, or real-rootedness of an approximant, without a horizon that recedes with
   the height.
2. Use the functional equation and the Euler product together; fail for twins, Davenport–Heilbronn, flips,
   Beurling systems and `ζ(s)ζ(s − ε)`.
3. Meet the boundary as a limit: every approximant strict, the limit exact.
4. Carry no Gaussian component in the limit.
5. Be testable on finite objects first: degree-`d` Jensen polynomials, finite Euler stages, finite free
   convolutions.
6. No Weil positivity, no spectral realization, no counts.

*Explicitly outside the field.* Weil positivity and window signs (P1, HF), the PM defect sign, counts and
Hodge index, size-only domination, spectral realizations.

*The sign field.* Arithmetic criticality theory — positivity, at exact criticality, of frustrated nonlocal
Dirichlet forms with arithmetic jumps on intervals, read as moment problems and settled at the boundary — is
the field of the window routes and of 2.8. Its dictionary is SWC, ACT, GWZ, CSTW, WTZ, DZG; its core (B3) is
open; the onset law (1.11) gives its outputs a zero meaning. Its criteria: reproduce the base `0.7240` and the
first-stage margins `~10⁻⁵–10⁻⁸`; pay the pole's negative square in the odd sector and the cosh deficit in the
even sector with the variance retained; freeze reflection coefficients at `±1`; deliver the band on every
reflection pair; pay the primes `3 ≤ p ≤ 73` by sign from their entry; cross `log 5`; force `Λ` and fail for
flips, Euler twins, Beurling systems, `ζ(s)ζ(s−ε)`, Davenport–Heilbronn, Epstein and golden data; use the
functional equation and the Euler product together. The camera threshold it meets is `λ = 1` against arbitrary
competitors and `λ = ½` against sparse modifications (1.9).

## 2.8 The one question

**Is every window of length `< log 5` positive, by one exact mechanism in which each prime power is paid by
the sign of its sliver reflection and the pole variance is retained?**

On these windows the primes `2`, `3` and the prime power `4` act; the Markov part is dead; `w₂ ≤ 0` and the
flip are inadmissible; the prime `3` is uncertified by its collar and cannot be carried by its size
(`287/500`) nor by soft entry beyond `δ ≈ 0.12`; `4` is collar-certified; both parity sectors must be paid;
below `log 4` the problem is exactly a two-point convex membership with exact retained-variance certificates
[L]; numerical margins near `log 3` are `1.5×10⁻⁵` (odd) and `5.6×10⁻⁸` (even) [N].

*Why it is less hard than RH or quasi-RH.* A finite window, three prime powers, an exact certificate format;
it implies no statement about zeros at large height.

*Why it pushes the door open.* `log 5` is the exact end of the size-subordinate regime: below it the edge-law bound
on the summed reflection terms stays below the Lévy energy (`0.991`), above it the bound exceeds it for every
longer window (`1.35` at the entry of `5`) [D]. So windows below `log 5` isolate the sign mechanism of P1 in pure form — the primes are small and still
indispensable — from the collective cancellation of P4. A structural answer gives the template of the stage
step (B2, B3) with the variance, sliver and edge structure that every later stage must carry; its failure
mode at `log 5` names precisely what the collective payment must supply. A proof that no mechanism of this
class exists identifies the term the next certificate must retain.

*Precise boundary.* Excluded: Markov supersolutions, folded supersolutions, variance-free gauges, collar-local payment, size-only payment of the prime `3`, soft entry alone, lossless lower forms, finite-square identities, cost-only payments, smooth extremals. Not excluded: retained-variance theta gauges and shifted ground states (exact below `log 4`), pole-charged supersolutions with non-compact gauges, variable-hub Schur elimination, packed nonlocal paths, and any exact identity that uses the trivial-zero Hankel squares and the sliver signatures.

## 2.9 The big impact question

**Which off-line zeros of `ζ` can hide from the windows?** Prove local half-carrier visibility (B48): if `ζ` has an off-line zero `ρ₀` at height `T₀` that is `T₀^{−M}`-isolated from the other zeros, some window of half-width `(1 + ε)L_{T₀}` is negative, `a*(ζ) ≤ (1 + ε)L_{T₀}`.

Expected shape [D]: the half-carrier law (1.11) needs a window of aperture `a − ε` vanishing on the right half of the carrier except at `ρ₀`. For `ζ` the right half has density `(1/2π)log(T/2π)`, so the aperture is `πD = L_T`; the local camera supplies the vanishing near `T₀` with an explicit far tail at `T₀^{−M}` precision (1.9). Deep zeros are seen much earlier, at `(1/2δ)log(Cδ log T₀)`.

*Why it is less hard than RH.* It is a zero-side statement, conditional on an off-line zero, and assumes no sign of `ζ`'s Weil form; it combines two proved mechanisms — the half-carrier law and the local camera with its far tail — at the density aperture.

*What it decides across the programme.*

| Effect | Routes and walls | How |
|---|---|---|
| The correct contact law | window routes, B18 | window positivity at half-width `a` excludes every isolated off-line zero below height `≈ 2πe^{2a/(1+ε)}` at every depth; single exponential, sharp by tapered crystals |
| One residual for windows and camera | P1 routes, ZCG, SRT | windows of length `≍ log T` and the camera see the same zeros: everything except near-coincident clusters (B44) and smooth off-line sheets (B50) |
| Pointwise control of isolated near-line zeros | WD, CDG | every isolated zero near `T` of depth `≥ T^{−M}` is visible at length `≍ log T`; exceptional windows are near-coincident or crystalline |
| Names the hiding structures | all window routes, P5 | off RH, the lowest invisible off-line structure is a near-coincident cluster or a sheet |

*How each answer moves the map.*
- **B48 holds:** the zero-side theory of windows is complete for `ζ`; the open core of every window route is B1 at lengths `≍ log T` plus B44 and B50.
- **B48 fails** (an isolated off-line zero of `ζ` hides beyond `L_T`): the far tail of `ζ`'s camera cancels coherently at the density aperture — a structural statement about `ζ`'s zeros at scale `1/log T` and a hiding mode outside the model classes of 1.11.

*First tests.* (1) An on-line lattice of `ζ`'s density with one off-line pair of any depth `δ`:`a* ≤ L/2 + ε` uniformly in `δ` (half-carrier law with a window blind to the lattice). (2) Perturbed RvM backgrounds with the far tail of `FarZerosAreFaintInTheLocalCamera`. (3) `ζ` itself.

*Why this question and not another.* The one question (2.8) decides whether P1 has a sign mechanism, but only for P1. B51 is sign-free and serves ZCG; B49 and B53 are RH-strength; B52 opens one new route. B48 is sub-RH, uses the corpus's own harmonic analysis, and fixes the zero-side meaning of every window route (C1, C4, C15, C19), of the camera (C21, C23) and of near-line density (C11) at once.
