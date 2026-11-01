# Walls ledger — status quo

Three wall families block every route: **Σ** the critical sign, **Π** square-root precision, **Γ**
selection of ζ. All three read one even integer, `κ = κ(K_ζ) = #` distinct zeros right of the
critical line, on one hyperplane, the pole-orthogonal hyperplane `v₁^⊥`. In the formal Kähler
package `(W_{c,N}, v₁)` of HWV, `v₁^⊥` is the primitive part. Hodge–Riemann (HR) is the sign there,
hard Lefschetz (HL) is nondegeneracy there. Transport of HR along the overlap flow is free, so the
whole content is HL on the positive locus.

- **Σ** is the sign of the complete Weil form on `v₁^⊥`. Along the overlap axis it splits at the
  critical overlap `c*_φ(N)` of the profile `φ`. At `c*_φ` the profile tail energy, which is both
  the margin of the complete form and its synthesis error, equals the Weil weight `1/log N`.
  - Below `c*_φ` lies the **rough regime**. The synthesizable radius `½ log K + O(1)` is negative
    there, so no fixed test is synthesized [D from L]. Positivity there uses only classical prime
    distribution (moduli `q ≤ (log x)^A`). No corpus receiver turns it into a statement about
    zeros; whether `N`-dependent vectors can see zeros there is open.
  - At `K·c*_φ` the family synthesizes every smooth test of radius `½ log K + O(1)`. RH is
    positivity at every `K`, i.e. Weil positivity at every aperture.
  - The aperture floor dies doubly exponentially: `μ(A) ≤ K exp((11/2)A − πe^{2(A−2)})`,
    unconditionally, and every positive aperture transport must lose at a doubly exponential rate
    [L]. No estimate with polynomial or exponential loss reaches all apertures.
  - In the RVM model an isolated off-line pair of depth `δ` at height `ξ` is seen at aperture `a`
    iff `S_δ(a) = sinh(2δa)/(2δ) − a > (1/2π)log(ξ/2π)` [L].
  - The scaling surface turns Σ into geometry: RH ⇔ an effectivity with the Riemann–Roch and ample
    axioms exists; positivity-defined cones fail the Riemann–Roch axiom [L].
- **Π** is the precision of two prime statistics.
  - The one-point statistic is the smoothed prime error in multiplicative windows. It equals Weil's
    kernel and the inter-tower coupling.
  - The conjugate-diagonal statistic is the Hecke defect. Its control has an exact hierarchy:
    dyadic mean `O(log U)` (proved); mean `o(log U)` ⇔ 100% critical-scale clustering; one fixed
    scale ⇔ log corridor (≥qRH); one constant over all dyadic scales ⇔ RH.
- **Γ** is closed for every prime-set flip. What remains is Frobenius at infinity, the identity of
  the reflection pairing `ρ ↔ 1 − ρ` with the conjugation pairing `ρ ↔ ρ̄`. It has four proved
  readings, all RH: the defect involution, a Hecke similitude of the collided form, one constant
  for the dyadic Hecke defects, and saturation of the partner angle of resonant Eisenstein states.
  Every selector in the corpus is a margin, index or counterterm statement on a partial form.

Status: **Solved** (the face is a theorem), **Partially solved**, **Sharpened** (open, with its exact
form a theorem), **Open**, **No-go** (the mechanism is refuted), **Classified** (answered by a
classification theorem). Strength: **RH**, **≥qRH** (implies a zero-free half-plane and Lindelöf),
**LH** (implies Lindelöf), **sub**. Evidence: `[L]` Lean statement or module docstring read;
`[U]` Lean file unfinished or not yet integrated; `[M]` frontier-map or killed-routes entry, Lean not
re-read; `[D]` derived here from `[L]` statements, not formalized.

## Σ — critical sign

| Wall | Status | Strength | Content |
|---|---|---|---|
| Σ1 All-aperture positivity | Sharpened | RH | Denjoy–Carleman and sinc profiles: RH ⇔ eventual positivity at every bounded multiple `K·c*_N`; every divergent multiple is a receiver; one `K` sees every `C²` test of radius `R` with `24eB⌈1+e^{2(R+1)}⌉ < K/(32e)` [L]. Restricted Weil ground minimum: `μ(A) ≥ 0 ∀A` ⇔ RH; floors through radius `181/500` and at an explicit `A₊ > 181/500` [M/L]. Unconditional ceiling `μ(A) ≤ K exp((11/2)A − πe^{2(A−2)})` for `A ≥ 3`; no positive floor along any unbounded aperture sequence; any positive transport loses doubly exponentially [L]. The isolated-pair visibility law `S_δ(a) > (1/2π)log(ξ/2π)` holds in the RVM model [L]. |
| Σ1a Critical overlap | Sharpened | — | Denjoy–Carleman: `c*_N ≍ L(log L)²`, `L = loglog N`, where `μ_B(c)² log N = 1` [L]. Sinc: `τ(c*) log N = 1`, same order [L]. Quasi-analytic boundary: no nonzero compact Gevrey-≤1 profile exists, so receivers stop at `(loglog N)^{1+ε}` [L]. Tilted spline: receiver proved for `α > ¼` by second-order synthesis [L]. With `|φ̂(ξ)| ≍ ξ⁻⁴`, fourth-order synthesis would place its critical overlap at `(log N)^{1/8}` [D]. |
| Σ1b Rough regime, tilted spline | Partially solved | sub | All vectors, `1 ≤ c ≤ (log N)^α`, every `α < 1/16`: matrix `≥ κ/(2c⁷)`, literal `weilQuad ≥ 0`, pole-defect reserve [L]. Complement of conductors `≤ N^θ` coercive for `α < 1/9`; global negative index `≤ N^θ` [L]. Bounded-energy vectors confined to `log R' ≤ C c¹¹ + log Q₁` [L]. Fixed finite and polylogarithmic conductor packets for `α < 1/8` via linear-in-`c` bilinear residuals [U]. Binding term: quadratic single-conductor residual `c²(1+log c)³/log N` against floor² `c⁻¹⁴`. |
| Σ1c Joint shell–pole payment | Open | sub | Separate shell payment is sharp at `c²/ε`, i.e. `c⁹` at `ε = c⁻⁷` [L]. Joint top-band coefficient `O_φ(G(c + log N))` [L]. All-vector positivity at the spline's critical overlap needs confinement exponent `≤ 8` [D]; the current exponent `11` comes from separate payment. |
| Σ1d Low-conductor spans | Partially solved | sub | Single modes `(log N)^A ≤ m ≤ N^θ` coercive, exceptional set empty, every `C²` profile [L]. Spans below `(log N)^A` open; sublinear nonpositive dimension does not bound the index. |
| Σ1e Square-root conductor barrier | Open | sub | Frames and residual averages need `m² ≤ N` [M]. Above `√N`: Elliott–Halberstam-type input. |
| Σ1f Defect-only confinement | No-go | — | `Q < 2^k` witnesses [M]. |
| Σ1g Haar / Gamma graph | Partially solved | sub | Growing-packet prime–pole cancellation to `exp(√log Y/23040000)` [M]. Index `≤ R + A` for `R` coarse cells [M]. Growing Euler head alone unbounded [M]. Open: joint non-arithmetic Gamma graph + signed diagonal + roots + poles. |
| Σ1h Rough regime, smooth profiles | Partially solved | sub | Every `C²` profile without real Fourier zeros has edge `→ ∞` [L]. One `C^∞` profile carries the unconditional edge divergence and the every-power hyperplane receiver; no rate [L]. Expected reach `ε·c*_N` with profile constants [D]. |
| Σ2 Edge, zero modes, hard Lefschetz | Sharpened | RH | HR ∧ HL ⇔ strict HR; transport needs HL only on the HR locus; losing HR forces a primitive zero mode [L]. Liouville ⇔ HL; RH ⇔ HL on the PSD locus along `1 ≤ c ≤ 2(log N)^β`, `β > ½` [U]. A finite first edge is PSD with a zero mode [L]. Under ¬RH, tilted crossings occur i.o. in `[(log N)^α, 2(log N)^{¼+}]` [L, Lean `α < 1/59`; `1/16` available]. |
| Σ3 Star renormalization | Partially solved | — (descent); RH (ascent) | The star of `d` is the family at `(c⌊N/d⌋/N, ⌊N/d⌋)`; star embedding is an isometry for every weight [L]. Positivity descends to every star; negative directions first appear at the top of the divisor lattice [L]. Deep stars are positive [L]. The counterterm is self-similar on stars exactly for generalized von Mangoldt weights [L]. Ascent (stars ⇒ HL at the top) has no arithmetic mechanism: the gcd/Möbius decomposition of a form into star pieces holds for every symmetric matrix on ℕ [D]. |
| Σ4 Finite index / heat count | Sharpened | ≥qRH (`K_ζ`); RH (`K_ζ⊠K_ζ`) | `κ < ∞` ⇔ bounded `N(t)` ⇔ bounded `O(T)` ⇒ Lindelöf + half-plane [L/M]. No softening at any resolution [L]. |
| Σ5 Collision quantum / heat homotopy | Sharpened | RH | `O ∈ 2ℕ`; RH ⇔ `O < 2` per window; horizon defect `≤ κ ≤ sup O`; all `O ≤ 1` ⇒ RH [L]. Heat state `κ(φ_c^{(t)}) = N(t)/2 + 1`, RH ⇔ constant [M]. |
| Σ6 Rank / degree uniformity | Partially solved | RH | Rank 7 strict, rank 8 PSD [M]; fixed Jensen degree eventually hyperbolic [M]; PF₃₇ at the centre [L]; RH ⇒ simple roots of reversed Xi Jensen sections [M]. |
| Σ7 Odd / Markov sector | Open | RH | RH ⇔ `R ≤ ½` on odd vectors [M]. |
| Σ8 Realization | Open | RH | Lossless realization needs infinitely many resonances; normal real-zero approximants force RH (Vitali) [M]. Gauss–Mayer Fredholm determinant `D = A + ζ(w)B` constructed [L]; resonance exclusion is RH. |
| Σ9 Explicit image / resolvent | Partially solved | RH in strip | Depth identity for `σ > 1`; theta–prime expression at `s = 4` [M]. |
| Σ10 Local signatures and gluing | Solved | — | `κ(φ_c) = κ + 1` at `∞` and every prime; readings add; dilation form + shell squares on boost mass zero [L/M]. |
| Σ11 Product-formula gluing of the global pole | Classified | — | Sum of local poles `|S|` squares; tensor `2^{|S|−1}`; renormalized infinite product `∞`; extremal weight = archimedean pole on `S`-units [M]. |
| Σ12 Running counterterm / star flux | Solved | — | `log N − γ` cancels the prime diagonal through `Λ ∗ 1 = log` [M]. On every star the counterterm pays exactly the boundary flux `log d` [L]. |
| Σ13 Tensor amplification | No-go | — | `K_ζ^n` PD ⇔ RH; `n₋(G⊗G) = 2n₊n₋` at every horizon [L/M]. |
| Σ14 Deformation to a positive model | No-go as free input | — | Crossing-free path `A → I` ⇔ `A` PD [M]; Kähler-package transport is exact and free [L]. The content is HL. |
| Σ15 Separable assemblies | Classified (no-go) | — | Blind to coupling when truncated, overcount when untruncated [M]. |
| Σ16 Prime–pole coherence / packet identity | Solved (as identity) | — | `B_Q² ≤ S_Q L_Q` sharp [M]. Complete form on packets = jump squares + affine incidence squares + bounded diagonal − shell degree + boundary terms [M]. Shell degree is the only overlap-growing non-square term. |
| Σ17 Inter-tower coupling | Solved (as equivalence) | RH | Coupling ≍ kernel; RH ⇔ bounded coupling on one `⟨p⟩×⟨q⟩` [L]; rate = width [M]; cone ⇒ RH or unattained width [L]. Attainment of `Θ` implies `Θ < 1` (no zeros on `Re s = 1`), so excluding the unattained alternative outright is ≥qRH; "bounded cone coupling ⇒ RH" as a pure implication is sub [D]. The same alternative appears in tower detection [L] and PM escape tightness [M]. |
| Σ18 Exact SOS on a two-prime lattice | Open | RH | Weil's dilation form on boost-mass-zero vectors of one two-prime lattice as a sum of squares of coupling differences. |
| Σ19 Loop-Eisenstein band poles | Open | RH | `κ_Hodge = #` band poles of `Λ(s)/Λ(s+1)` [M]; noncancellation mechanism missing. |
| Σ20 Scheduled prime sums | Open | RH | Lower bounds for prime-scheduled energies (FU, CFC, RP, SZ, LI, FEL, EGC) [M]. |
| Σ21 Extension / carrier | Classified | — | Escape, mixing, height decay ⇒ `κ ∈ {0, ∞}` [M]. Continuous-dilation carriers reading `1_H` exist iff `H ∈ {{0}, ℚ}` [M]. Every nonzero proper subgroup successor splits uniquely `p + ψ∘slope + q`, `κ = κ(ψ∘slope + q)` [L]. |

## Π — square-root precision

| Wall | Status | Strength | Content |
|---|---|---|---|
| Π1 Global law | Solved (as equivalence) | RH | `ψ(x) − x ≤ C√x log²x` ⇔ RH ⇔ `κ = 0` [M]. |
| Π2 Deciding input | Open | RH | No unconditional source input at square-root precision. |
| Π3 Producer cost | Partially solved | sub / RH | Growing-alphabet producers reach `ψ, θ ≤ (1+ε)x + C_ε log²x`; every individual producer has slope `> 1` [M]. Open: `ε`-uniform error. |
| Π4 Window precision (kernel = coupling) | Sharpened | RH | Weil's kernel is the smoothed prime error in fixed-length multiplicative windows; coupling ≍ kernel [L/M]. Square-root control at every height is RH. |
| Π5 Conjugate diagonal (Hecke defect) | Sharpened | sub → ≥qRH → RH | Prime polynomial carries `O(1/log T)` of the defect; counts + linear explicit formula cannot bound it [L]. Dyadic means `O_c(log U)` for `c < 22/51`, `O(U^η)` for `c < 2/3` [L]. Mean `o(log U)` ⇔ 100% critical-scale clustering [L]. Fixed-scale `O(1)` ⇔ corridor (≥qRH) [L]. One constant over dyadic scales ⇔ RH, also as a zero-coordinate-free finite-theta statement [L]. Bare prime polynomial grows like `e^L/L²` at anti-nodal ordinates even under RH [L]. |
| Π6 Averages versus all heights | Sharpened | — | Almost all unit windows are free of zeros at depth `≥ (6/5)loglog T/log T` [L]. Local count holds for density-one heights; right-half depth moment `o(V)` [M]. A density envelope admits a singleton count, so density never excludes one zero [M]. |
| Π7 Census / local count | Partially solved | sub / LH | Simple critical `≥ 0.67250071` [L]; dichotomy: `N₀ ≥ 7N/10` or many simple off-line zeros within `A/log T` [M]; prime surplus `≤ N/18` would give 75% [M]. |
| Π8 Depth visibility | Sharpened | — | Isolated pair visible at aperture `a` iff `S_δ(a) > (1/2π)log(ξ/2π)`; archimedean domination blind at every depth [L]; clusters hide depth from heat [M]. In the model, positivity at aperture `a` excludes isolated pairs below `2π exp(2π S_δ(a))` [D]; clusters are not covered. |
| Π9 Exceptional moduli | Partially solved | sub | Uniform zero-free region and Siegel for `q ≤ (log x)^A`; every inverse-log rate at one horizon [M]. |
| Π10 Frequency localization | Sharpened | ≥qRH (¾ strip); RH | Every band `K = ⌈N^δ⌉` retains the infimal exponent `2Θ`; far energy `≤ N^{2Θ+ε}/K` [L]. |
| Π11 Quadratic RR / effectivity | Solved (as equivalence) | RH | Renormalized Hodge index ⇔ Serre-dual `h⁰` with quadratic RR along rays and subquadratic degree-zero growth [L]. Scaling surface: RH ⇔ an effectivity with RR and ample axioms; positivity cones fail RR [L]. Theta `h⁰` gives RR on `Spec ℤ` and on the pole plane by Poisson summation [L]. Missing: RR for classes with a test component. Refuted: finite readings + mass, positive counts, determinant data, Boolean sections, majorants, polar box minus `ψ`, finitely many degrees [L/M]. |
| Π12 Subconvexity / heat floor | Partially solved | sub | `ζ(5/6+it) ≪ t^{2/53} log t` [L]; `μ(½) ≤ 33/200` [U]. Heat floor `2/3` from three pieces of the Ki–Kim–Lee strip profile; the `w ≥ 3/14` piece (via `μ(5/7) ≤ 1/14`) is certified only for `c > 2/3` [L]. A lower floor needs every piece to improve. |
| Π13 Gap-dependent detection scale | Sharpened | sub | Stopping certificate sound, eventually complete; admissible stage depends on divisor separation [M]. |
| Π14 Amplifier rank | No-go (finite support) | — | Growing losses `e^{2kλ}` keep radius `Be^λ` [M]. |
| Π15 Critical-scale residual sign | Sharpened | RH (all `K`) | At `c*_φ` margin = synthesis error = `1/log N` [L]. The sharp literal prime residual scale is `(log Q)²/log N` [M]. No absolute residual bound decides the sign at `K·c*_φ`; only signed cancellation can [D]. |

## Γ — selection

| Wall | Status | Strength | Content |
|---|---|---|---|
| Γ1 Trivial gauge point | Open | RH | `Θ ≥ ½`, Haar-a.e. `½`; RH ⇔ trivial point typical [M]. |
| Γ2 Prime-set flips | Solved | — | Ordinary or two-adic atomic margin separates every nontrivial prime pattern, no density assumption [M]. Coupling diagonal recovers flip sets; `ζ` and a `p`-flip never both have finite coupling index [M]. Flip twins with relative density `κ < ½` have harmonic correlation `≍ (log N)^{−2κ}` with positive constant; multiscale dual bound for `κ < ¼` [L]. |
| Γ3 Twin-blindness of soft structure | No-go (complete) | — | Krein index invariant under unitary twists; pointwise-closed classes contain every unitary twist [M]. |
| Γ4 Frobenius at infinity | Open | RH | `σ(ρ) = 1 − ρ̄` fixes exactly the line; `κ = #` moved right zeros; RH ⇔ `σ` trivial ⇔ every Hecke translation is a similitude of the collided form [L]. RH ⇔ one constant for the dyadic Hecke defects [L]. Resonant states of `ρ` and `1 − ρ̄`: `cos²` of their angle is `4Reρ(1 − Reρ)`; saturation iff `Re ρ = ½` [L]. A conformal correspondence with factor `≠ 1` over ℤ is missing [M]. |
| Γ5 Source identification / pre-divisor construction | Partially solved | RH | Integer counting + full-cone positivity ⇒ `λ = Λ` and RH [M]. Pre-divisor sections and potentials need zero-independent forcing. |
| Γ6 Boundary sign / coherence | Solved | — | Pole boundary sign separates ζ from size-equivalent twins [M]. |
| Γ7 Affine carrier with Weil dilation | Solved | — | Via gluing at a place [M]; subgroup classification (Σ21) [L]. |
| Γ8 Poisson rigidity | Sharpened | RH | Positive tent-self-dual measures with gap are Dirac combs; zero-side positivity = RH [M]. |
| Γ9 Archimedean continuity vs height decay | No-go | — | Continuous dilation against a decaying finite-adelic reading ⇒ `κ = ∞` [M]. |
| Γ10 Function-field indistinguishability | Sharpened | — | Local index walls identical over `𝔽_q(X)` [M]. Curve edge `≤ 2g`, defect from window `2g` = eigenvalues moved by the circle reflection [L]. Curve towers commensurable, two-prime log-lattices dense [M]. Frobenius conformal with factor `q`; Hecke dilations are boosts [M]. |
| Γ11 Pole-blindness of the glue | No-go | — | Simple pole absorbed, double pole costs a square [M]. |
| Γ12 General gauges | Partially solved | sub | Entrywise-nonnegative gauges only on archimedean characters [M]; twisted Selberg source forces `ω(p) = 1` [M]. Open: unimodular gauges with `S_N/H_N → 1`; zero-density twins at `κ = 0`. |
| Γ13 Source-uniform extinction | No-go | — | Fails at `3/4 + i` [M]. |
| Γ14 Local counterterm selection | No-go | — | Diagonal counterterms give `Λ` and a flip twin glued index `1` [M]. |
| Γ15 Functional-equation twins without Euler product | Open | sub | No Lean statement. |
| Γ16 Selection–sign gap | Sharpened | RH | Selectors: atomic pole index, two-adic probe, Metzler gauge, twisted Selberg source, coupling diagonal, finite-flip edges, self-similar star flux [L/M]. All are margins, indices or counterterm identities on partial forms; none yields complete-form positivity. |
| Γ17 Scattering recentering | Classified (no-go) | — | A rational map real at infinitely many points of the critical parabola `3/16 + t²/4 + it/4` is constant; an algebraic relation real infinitely often on the parabola and on `(¼, ∞)` is a horizontal line [M/L]. |
| Γ18 Divisor-identity selection | Solved (selection) | — | A weight has self-similar star flux iff it is a generalized von Mangoldt function; among completely multiplicative twists `Λω` only `ω ≡ 1` [L]. |

## Bridges

| Bridge | Anchor |
|---|---|
| `κ(K_ζ)` = right zeros = Hodge defect = band poles of `Λ(s)/Λ(s+1)` = zeros moved by `σ` | HKT, RIT [M]; EHT `FrobeniusAtInfinity` [L] |
| `κ(φ_c) = κ + 1` at every place | AKG [L] |
| boost hyperplane = `v₁^⊥` = Markov = harmonic hyperplane = primitive part of the Kähler package | RIT [M]; HWV [L] |
| bounded `K_ζ` ⇔ bounded coupling ⇔ no edge ⇔ RH | RIT, ACPL [L] |
| RH ⇔ HL on the PSD locus along the overlap flow; Liouville = HL | HWV `TheLiouvilleProperty` [U] (transport: `TheKahlerPackage` [L]) |
| overlap multiple `K·c*` ↔ test radius `½ log K + O(1)` | TM `ReceiverRate` [L] |
| aperture floor `μ(A) ≤ K exp((11/2)A − πe^{2(A−2)})`; positive transport loses doubly exponentially | ArithmeticCompensationTheory `TheApertureFloorMustDecayDoublyExponentially` [L] |
| isolated pair visible at aperture `a` iff `S_δ(a) > (1/2π)log(ξ/2π)` (RVM model) | ACS visibility law [L] |
| RH ⇔ an effectivity of the scaling surface with RR and ample axioms; Castelnuovo–Severi defect = Weil's form | ArithmeticCastelnuovoSeveri `TheScalingSurface` [L] |
| theta `h⁰`: RR on `Spec ℤ` and on the pole plane by Poisson summation; `Λ(s)` = Mellin generating function of `h⁰` | ArithmeticOrientationGeometry `TheThetaH0OfSpecZ` [L] |
| star of `d` ↔ lower horizon `(c⌊N/d⌋/N, ⌊N/d⌋)`; counterterm flux `log d` ↔ `Λ ∗ 1 = log` | HWV [L] |
| first rung: finite Hodge defect ⇔ bounded heat counts ⇔ bounded collision charges; ⇒ `Θ < 1`; RH = defect `< 2` | ArithmeticOrientationGeometry `TheIndexExit` [L] |
| complete form on packets = jump squares + affine incidence squares + bounded diagonal − shell degree + boundary | ACPL [M] |
| `κ(φ_c^{(t)}) − 1 = N(t)/2` = future collision pairs | AKG, RIT [M] |
| collision charge = Fredholm index; horizon defect `≤ sup O` | CDG [M]; EHT [L] |
| Hecke defect: mean `O(log U)`; `o(log U)` ⇔ critical-scale clustering; fixed scale ⇔ corridor; dyadic-uniform ⇔ RH | CDG [L] |
| partner saturation of resonant states ⇔ `Re ρ = ½` | RHTower `EisensteinResonantPartnerAngle` [L] |
| Mayer determinant `D(w,λ) = A + ζ(w)B`, `B(w,−1) = 0` | RIT `GaussMayer*` [L] |
| renormalized Hodge index ⇔ quadratic RR on the scaling surface | RIT [M] |
| curve: bounded tower coupling ⇔ unitary ⇔ Castelnuovo–Severi on the Frobenius span; edge `≤ 2g` | ACPL, EHT [L] |
| finite index `≤ r` ⇔ translation-stable positive constraints of dimension `≤ r` | HKT `Index` [L] |

## Status counts

| Family | Solved | Partially solved | Sharpened | Open | No-go | Classified |
|---|---|---|---|---|---|---|
| Σ (29) | 4 (Σ10, Σ12, Σ16, Σ17) | 7 (Σ1b, Σ1d, Σ1g, Σ1h, Σ3, Σ6, Σ9) | 5 (Σ1, Σ1a, Σ2, Σ4, Σ5) | 7 (Σ1c, Σ1e, Σ7, Σ8, Σ18, Σ19, Σ20) | 3 (Σ1f, Σ13, Σ14) | 3 (Σ11, Σ15, Σ21) |
| Π (15) | 2 (Π1, Π11) | 4 (Π3, Π7, Π9, Π12) | 7 (Π4, Π5, Π6, Π8, Π10, Π13, Π15) | 1 (Π2) | 1 (Π14) | — |
| Γ (18) | 4 (Γ2, Γ6, Γ7, Γ18) | 2 (Γ5, Γ12) | 3 (Γ8, Γ10, Γ16) | 3 (Γ1, Γ4, Γ15) | 5 (Γ3, Γ9, Γ11, Γ13, Γ14) | 1 (Γ17) |

Strength of the open walls: RH — Σ1, Σ2, Σ3 (ascent), Σ5, Σ7, Σ8, Σ18, Σ19, Σ20, Π2, Π4, Π11 (construction), Π15, Γ1, Γ4, Γ5, Γ8,
Γ16; ≥qRH — Σ4 (`K_ζ`), Π5 (fixed scale), Π10 (¾ strip); sub — Σ1b–Σ1h, Π3,
Π5 (mean `o(log U)`), Π7, Π9, Π12, Π13, Γ12, Γ15.
