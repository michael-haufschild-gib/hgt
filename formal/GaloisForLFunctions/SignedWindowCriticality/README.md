# Signed Window Criticality (SWC)

Namespace `GaloisForLFunctions.SignedWindowCriticality`; umbrella `SignedWindowCriticality.lean`.
Every theorem is unconditional; equivalences with RH are labelled as such.

## 1. Motivation

RH is the statement that Weil's form `W` is nonnegative on every window. The corpus has fixed the
shape of any proof of this sign (review-0311 §1.9–1.10): two sites decide; the stage step is exact
and carries no sign; counts, Hodge index and degeneration are closed; slack, finite identities,
sign-blind ground states and Markov passage are refuted. The one surviving proof mechanism of the
window tower is *signed criticality*: a positive function on the window satisfying a pointwise
inequality, through which `W` becomes an exact sum of squares of differences plus a nonnegative
remainder — an identity of unbounded rank, the only kind the no-slack facts allow — in which every
sign of the form is used.

ACT built this theory for the Markov part of the Weil form on the whole line, in the Doob gauge of
Riemann's kernel `Φ`, and found that no positive folded supersolution exists there (two-moment law).
SWC is the window version with every sign kept. Its subject is the quadratic form of Weil on a
symmetric window `[−a, a]`, read as a nonlocal Schrödinger form: positive archimedean jump rates,
arithmetic jumps of length `log n`, a constant creation potential, and the pole's hyperbolic pair.
The questions are which parts of this form are Markov and which are frustrated, what a positive
supersolution must carry to certify it, how such a supersolution passes a prime-power stage, and
what the ground state becomes when the window is critical.

Three facts organize the field.

1. **Parity splits the pole.** On a symmetric window `W = W₊ ⊕ W₋` (even and odd tests are
   `W`-orthogonal). The pole's hyperbolic pair `½⟨c, F⟩² − ½⟨s, F⟩²`, `c = 2cosh(x/2)`,
   `s = 2sinh(x/2)`, puts its positive square on even tests and its negative square on odd tests:
   `W₊ = M + ½⟨c, ·⟩²` and `W₋ = M − ½⟨s, ·⟩²`, where `M = W − pole` is the Markov part.
2. **Frustration sits in opposite sectors.** Folding the jump measure by parity gives the sector
   conductances `c_±(x, y) = κ(|x − y|) ± κ(x + y) + Σ_n w_n[δ(|x − y| − log n) ± δ(x + y − log n)]`,
   `κ = ω − 2cosh(·/2)`. In the odd sector the archimedean place and the pole are a positive
   light cone and the only negative conductances are the prime anti-diagonals `x + y = log n`; in
   the even sector the primes are positive and the only negative conductance is the pole at long
   range. The pole frustrates the even sector, the primes frustrate the odd sector.
3. **The Markov ground state dies before the first prime.** `M` is a translation-invariant Z-type
   form; a smooth plateau of width `e^{−3/4} < ½ < log 2` has `M ≤ −‖F‖²/40` (numerically `M` is
   indefinite from length `≈ 0.22`). By the easy half of Allegretto–Piepenbrink no positive
   supersolution of the Markov generator — two-sided, or folded in ACT's sense — exists on any
   interval longer than `e^{−3/4}`, in particular not on the unit odd window. A certificate on the
   first prime stage must keep the pole.

So the object of the field is not a Markov ground state but a signed one: a positive gauge whose
Doob-transformed form has negative conductances exactly on the frustration loci, and whose negative
edges are paid by the positive network.

The same form has two further axes on which the sign must pass. Along the window axis the stage is
exact: `W ≥ 0` on a window of length `ℓ + ε` iff `W ≥ 0` on the window of length `ℓ` and translation
by `ε` is a contraction, `W(τ_εu, v)² ≤ W(u)W(v)` for all tests `u, v` of the shorter window
(CSTW), so a signed certificate must pay one *mixed pairing* per growth step with premises on the
shorter window only. Along the conductor and overlap axes the same form is the complete family
`W_{φ,c,N}` on atoms at `log n`, `n ≤ N`, of width `c/N`: positive definite below the eighth root
`c ≤ (log N)^α`, `α < 1/8` (CACT), with RH the positivity of the conductor Gram at every multiple of
the critical curve `c = 2K(log N)^{1/8}` (HWV). On that axis the sign has to survive a passage to a
limit, and the corpus has proved that energy limits erase arithmetic charges that the complete form
must still pay (CSAR). A signed certificate on a window and a charge-retaining identity on the
complete family are the two faces of the same positivity.

Two landings accept a certificate. The window and lattice forms accept none but the sharp one:
under RH every lattice margin tends to `0` and the Weil cone is the point `{Λ}` (GWZ), so a window
certificate may not lose a multiplicative factor. The orbit of one fixed bump accepts constants:
for the cubic spline `B`, RH holds iff `|c_B(t)| ≤ K_ε e^{εt}` for every `ε > 0` (AOG), and already
if `|c_B(t)|^k ≤ C_k e^{L_k t}` with `L_k/k → 0` (ACP). What no landing accepts is a positive
exponential rate, which is the zero width. A certificate that cannot keep a sharp window margin is
to be judged by the rate it controls.

## 2. Objects

| Object | Meaning |
|---|---|
| Window | `[−a, a]`, half-width `a`, length `2a`; its stage is `N = ⌊e^{2a}⌋`, the prime powers `n ≤ N` act |
| Weil form | `W(F) = Γ‖F‖² + ∫_0^∞ ω(x)‖F − F(· + x)‖²dx − 2Σ_n w_n c_F(log n) + ½⟨c, F⟩² − ½⟨s, F⟩²`; `ω(x) = e^{−x/2}/(1 − e^{−2x})`, `w_n = Λ(n)/√n`, `c_F(t) = ∫F(y)F(y + t)dy`, `Γ = −γ − log π − π/2 − 3log 2` |
| Markov part | `M = W − pole = V_N‖F‖² + J_N(F)`, `V_N = Γ − 2Σ_{n≤N} w_n`, `J_N` the archimedean and prime jump energies (RHTower `markovForm`) |
| Sector forms | `W₊` on even tests, `W₋` on odd tests; ground energies `μ₊(a)`, `μ₋(a)` |
| Frozen form | `W` with the kick of the newest prime power removed (stage form of WTZ/DZG) |
| Weil jump density | `κ = ω − 2cosh(·/2)`: strictly decreasing, positive exactly below `log ρ ≈ 0.2812` (ACT) |
| Sector conductances | `c_±(x, y)` above, on the half-window `(0, a]` |
| Frustration locus | the pairs with `c_± < 0`: prime anti-diagonals (odd), long-range pole pairs (even) |
| Gauge | a function `h` on the half-window; `F = hu` |
| Doob form | `D_h(u) = ½∫∫ c_±(x, y)h(x)h(y)(u(x) − u(y))²`, a signed Dirichlet form |
| Signed potential | `g_h = (W_±h)/h`, the pointwise defect of the gauge |
| Signed supersolution | `h > 0` on `(0, a)` with `g_h ≥ 0` and `D_h ≥ 0` |
| Pole charges | of a gauge `ω` on a window `S`: the sinh charge `∫_S Φω sinh(x/2)` and the cosh charge `∫_S Φω cosh(x/2)`; charge variances `V^S(u) = (∫_S m)(∫u²m) − (∫um)²` for `m = Φω sinh(x/2)`, `Φω cosh(x/2)` |
| Weil source | `𝒮(a) = (𝓛_D a − Φcosh(x/2)a) − 2B(Φa)Φ sinh(x/2) + 2A(Φa)Φ cosh(x/2)`, the operator through which `W` polarizes in the Doob gauge |
| Theta gauge, outside charges | `ω = Σ_j α_jτ_{b_j}`, `τ_b = Φ(· − b)/Φ`, with total charges `A/2`, `B/2` (`A = Σα_j cosh(b_j/2)`, `B = Σα_j sinh(b_j/2)`); outside charges: total charge minus the charge on `S` |
| Collar regional energy, collar light cone | on a collar `C = [c − h, c + h]`: `E_C(f) = ∫_C∫_C (f(u) − f(v))²/(2|u − v|)` and `A_C(f) = ½∫_C∫_C ω(|u − v|)(f(u) − f(v))²` |
| Pole capacities | `cap₋(a) = sup ⟨s, F⟩²/(2M(F))` over odd tests (sinh capacity); the cosh charge of the even Perron state |
| Collar, collar reflection | at stage `n`: `I = [log n − a, a]`, `τx = log n − x`; the kick on odd tests is `2w_n⟨U, τU⟩_I` |
| Kron reduction | Schur complement of a form onto a set of terminals; preserves Z-type |
| Markov threshold | `L_M`: the infimum of lengths on which `M` is indefinite |
| Ordered coupling | for tests `f` left and `g` right of a cut, `W(f + g) = W(f) + W(g) + 2(−∫_0^∞ κ(x)c_{fg}(x)dx − Σ_n w_n c_{fg}(log n))`, `c_{fg}(x) = ∫f(u)g(u + x)du`; the collar kernel `−κ = 2cosh(·/2) − ω = e^{x/2} − Σ_{k≥1}e^{−(2k+½)x}` is the trivial divisor of `ζ` (CSTW) |
| Trivial-divisor moments | `μ_s(f) = ∫f(u)e^{(½−s)u}du` (left), `ν_s(g) = ∫g(v)e^{(s−½)v}dv` (right); across a cut the archimedean place and the pole couple only through `⟨μ(f), ν(g)⟩ = μ_1ν_1 − Σ_{k≥1}μ_{−2k}ν_{−2k}` (CSTW) |
| Frozen two-collar form, stage disk | on a stage test `x_L + y + x_R`: `W = F(x_L, y, x_R) − 2w⟨x_L, Jx_R⟩`, `F = W(x_L + y) + W(y + x_R) − W(y) + 2⟨μ(x_L), ν(x_R)⟩`; the stage is positive iff the fold lies in the Carathéodory disk centred at the frozen pairing with radius `√(W(u)W(v))` (CSTW) |
| Mixed pairing | `W(τ_εu, v)` for tests `u, v` of the shorter window; the contraction `W(τ_εu, v)² ≤ W(u)W(v)` is the growth step |
| Collar Hankel form | on reflection-paired collar data `x_R = ±x_L∘R`, the collar coupling `2⟨μ(x_L), ν(x_R)⟩ = ±2(e^{−(A+ℓ)/2}μ_1(x_L)² − Σ_k e^{(2k+½)(A+ℓ)}μ_{−2k}(x_L)²)`: one pole square against the trivial-zero squares |
| Complete family | `W_{φ,c,N}`, atoms `φ(·N/c)` at `log n`, `n ≤ N`; conductor packets `r_e = c_e(n)/√(φ(e)n log N)`; the pole packet `e = 1` |
| Prime generator, receiving charge | `GF(n) = Σ_k (Λ(k)/k)[F(kn) − F(n)]` on packets `F = Σ_m a_m e_m`; adjunction energy `L_M(a) = Σ(log m + τ(m))a_m²`; the coherent constant output `P_M(a) = Σ_p (log p/√(p−1))a_p` is a receiving charge (CSAR) |
| Complete-form decomposition | `W(packet F) = jump energy + ½ affine Dirichlet energy + Mertens–Euler diagonal − shell degree + centre + cross + pole-error + overlap` (ACoT) |
| Conductor Schur form | `A − BD⁻¹B*` of the conductor block `A` against the coercive complement `D` at the critical curve; its positivity for every coefficient vector and every `K` is RH (HWV) |
| Pencil, critical multiple | on a horizon window `H = e^{y/2}h` along `c⁸/log N → R`: `c⁻¹⟨Wx, x⟩ → a_φW(H) + (7J(1)/R)‖H‖²_{−8}`, `a_φ = (∫φ)²/∫φ²`; a window with `W(H) < 0` turns negative past `R*(H) = 7J(1)‖H‖²_{−8}/(a_φ|W(H)|)` (AHD) |
| Spline orbit | `c_B(t) = W(B, B(· − t))` for the cubic spline; its growth rate is the zero width (AOG) |

## 3. Language

- **Z-type / Markov**: all conductances nonnegative; `|F|` does not raise the energy.
  **Frustrated**: some conductance negative and no sign gauge `F ↦ σF` removes all negative ones.
- **Gauge** vs **sign gauge**: a positive rescaling `F = hu` changes potentials, never the sign of a
  conductance; a sign gauge flips signs of conductances along a cut.
- **Signed ground-state representation**: `W(hu) = D_h(u) + ∫g_h h²u²`. **Neumann** and
  **Dirichlet** forms of a reflected edge are the two ways of writing `(aα + bβ)²`; only the Neumann
  form has a nonnegative remainder, only the Dirichlet form has the odd generator as potential.
- **Kron domination**: the negative network is dominated by the Kron reduction of the positive
  network onto the frustration locus. **Packed path**: a payment of negative conductances by
  positive ones that uses no positive conductance beyond its capacity; on a collar, the payment of
  the reflection by the collar's light cone at the first Legendre gap.
- **Pole-charged supersolution**: a gauge whose Markov defect carries its own sinh charge
  (`≥ 2σ_sΦ sinh`); **pole-charged harmonic**: a gauge whose Weil source vanishes on the window.
- **Critical**: the sector ground energy tends to `0` along the tower. **Agmon ground state**: the
  minimizer of `W_±` on a window, normalized; **edge value**: its value at `x = a`.
- **Perron property**: the sector ground state has no node in `(0, a)`. **Oscillation property**: the
  `k`-th sector eigenfunction has `k` nodes in `(0, a)`, and even and odd eigenvalues interlace.
- **Growth step / contraction**: the passage from the window of length `ℓ` to `ℓ + ε`; **mixed
  pairing**: the cross term `W(τ_εu, v)` it must pay; **premises on the shorter window**: a
  certificate of the step may assume `W ≥ 0` on `W_ℓ`, never on `W_{ℓ+ε}`.
- **Landing**: an RH-equivalent receiver; **sharp** (window, lattice: no multiplicative slack) or
  **rate** (spline orbit, tensor loss: constants free, exponential rate zero).
- **Receiving charge**: a constant or nonconstant output of the prime generator that survives
  vanishing adjunction and physical energy; **charge retention**: a limit argument that keeps it or
  proves its cancellation inside the complete form.
- **Critical curve, multiple**: `c⁸ ≍ R log N` (equivalently `c = 2K(log N)^{1/8}`, `R = (2K)^8`);
  **window index**: the negative index of the pencil on a family of windows; **equality face**: the
  windows with vanishing leading pencil, where the canonical clock gives eventually negative energy.
- **Additive–multiplicative coupling**: the pole and the successor `n ↦ n + 1` against the Hecke
  action; the successor pairs lie in the top coprime stratum, and the prime successor edges
  `(n, pn + 1)` carry the affine energy.

## 4. Mechanisms

1. **Parity split of the hyperbolic pair.** `W` commutes with `x ↦ −x`, `⟨c, F⟩ = 0` on odd and
   `⟨s, F⟩ = 0` on even tests. Each sector carries one square of the pole with a fixed sign.
2. **Sector conductances and frustration.** The odd light cone `κ(|x − y|) − κ(x + y) > 0` (ACT) is
   the archimedean place and the pole together; in the odd sector every failure of positivity sits
   on a prime anti-diagonal. As a Beurling–Deny statement: for `F̃ = sign(x)|F|`, the archimedean
   energy and the pole's negative square do not increase (AIP's exact fold
   `J_P = 2S_P + 4∫F²Π_P`, whose surplus weights `ω(s) − ω(s + 2x)` are nonnegative), so the frozen
   odd form is Markov, while the kick `−2wc_F(ℓ) = 2w∫F(s)F(ℓ − s)ds` of the first prime does not
   decrease. In the even sector the primes are inside the Markov part and the pole's positive
   square is the only anti-Markov term (RHTower `markovForm_abs_le`, `pole_le_pole_abs`).
3. **Markov death.** `M` is translation invariant and Z-type. A smooth plateau of width
   `w = e^{−3/4}` has self-energy `(log(1/w) + 2c_∞ + β/‖φ‖²)‖F‖² + O(w)‖F‖²` with
   `2c_∞ = 2log 2 + π/2` (SSHA); the `π/2` cancels against `Γ`, leaving
   `−γ − log 2 − log π + 3/4 + 1 + e^{−1/4}/2 + o(1) < −1/40`. In ACT's ground-state representation
   `M(Φωu) = J_{Φω}(u) + ∫u²ω(𝓛_Dω − Φcosh ω)` a nonnegative `C²_c` supersolution on an interval
   makes both terms nonnegative for every `u` vanishing off the interval, so a translate of the
   plateau excludes it. The folded generator is the two-sided generator of `ω∘|·|` on `[0, ∞)`, and
   lowering a gauge away from a point raises its generator there; a cut-off reduces ACT's folded
   criterion on `(0, a)` to the two-sided one.
4. **Pole charges.** On a window `S` with gauge `ω`, `M = Φω`, put `m_s = M sinh(x/2)`,
   `m_c = M cosh(x/2)`, `σ_s = ∫_S m_s`, `σ_c = ∫_S m_c`. Then exactly
   `Ẑ(Φωu) = J_{Φω}(u) + ∫u²ω𝒢_S(ω) + 2V_s(u) − 2V_c(u)` with the pole-charged defect
   `𝒢_S = (𝓛_Dω − Φcosh ω) − 2σ_sΦ sinh + 2σ_cΦ cosh` and charge variances
   `V = (∫_S m)(∫u²m) − (∫um)²`; `2V_s − 2V_c = −∫∫_{S²}M(x)M(y)cosh((x−y)/2)(u(x)−u(y))²` is the pole as
   a long-range negative conductance. The negative square is a **sinh charge**: if `m_s ≥ 0` and the
   defect carries `2σ_sΦ sinh`, then `Ẑ ≥ J + 2A²`. The positive square is a **cosh credit**: if
   `ω ≥ 0` and the defect is at least `−2σ_cΦ cosh`, then `Ẑ ≥ J − 2V_c − 2B²`. Globally, the odd
   capacity form of RHTower/ACT and the cosh capacity criterion of CWS are the two sector shadows.
   Explicit pole-charged gauges exist on every window: ACT's shifted ground state `ω_a` carries the
   whole charge `sinh(a/2)/2` of the half-line in its source, the window reads only the part
   inside, and `Ẑ(Φω_au) = 2S_a − D_a + 8V_c + 8τ_c(a)∫_{x>0}u²m_a sinh` exactly, with outside charge
   `τ_c(a) = ∫_{x≥c}m_a sinh > 0`. More generally, every theta gauge `ω = Σα_jτ_{b_j}` has source
   `−Φ(A cosh − B sinh)` with total charges `A/2`, `B/2`, and for every set `S`
   `Ẑ(Φωu) = J_M + 2V_s^S − 2V_c^S + 2τ_s^S∫u²M sinh − 2τ_c^S∫u²M cosh`: theta gauges are critical on
   the line, and a window reads the charges outside it with the pole's signs — slack in the odd
   sector, deficit in the even sector. In an even theta gauge with `M ≥ 0` the even window form is
   at most its Markov Dirichlet form minus the outside cosh deficit. Windows are subcritical in odd
   theta gauges and supercritical in even ones, matching the numerical order `μ₊ < μ₋`.
5. **Signed ground-state representation.** For every gauge, `W(hu) = D_h(u) + ∫g_hh²u²`, with the
   sign of each Doob conductance equal to `sign(c_±)·sign(h(x)h(y))`. With `h` the sector ground
   state, `g_h = μ_±` and `D_h ≥ 0`: a positive ground state is a signed supersolution.
6. **Kron reduction of negative edges.** A signed Dirichlet form `D = D⁺ − D⁻` with `D⁻` carried by a
   terminal set is nonnegative iff the Kron reduction of `D⁺` onto the terminals dominates `D⁻`; Kron
   reduction never creates frustration, and pairwise healing decides positivity on the terminals
   (SAEI, finite forms). For one negative edge this is effective conductance; at a stage it is the
   two-collar form of GWZ. In the continuum the prime anti-diagonal is the reflection of its
   collar, and the regional logarithmic light cone conducts that reflection at its first Legendre
   gap: `∫_C f(u)f(2c − u) ≥ −½E_C(f)`, sharp on the linear profile, so the collar's own light cone
   carries the kick of `n` at the ratio `2Λ(n)n^{−1/2}e^{h}`, and this is sharp: on admissible odd
   tests no constant below `2Λ(n)n^{−1/2}/(1 + 4h)` works. For small `h` the ratio is below `1` at
   the first prime, at proper prime powers and at primes `p ≥ 79`, and above `1` for
   `3 ≤ p ≤ 73`, whose collars cannot pay their own frustration.
7. **Stage passage.** For odd `F` the lag-`ℓ` correlation is anti-diagonal,
   `c_F(ℓ) = −∫F(s)F(ℓ − s)ds`. In any gauge `F = hu` the kick is
   `−2wc_F(ℓ) = 2w∫h h∘τ u² − w∫h h∘τ(u − u∘τ)²`, `τs = ℓ − s`: a positive source plus a negative
   anti-diagonal conductance. On `τ`-symmetric profiles it is the pure source, on `τ`-antisymmetric
   ones minus it (GWZ: the collar Rosati form). On odd tests supported in `[−a, a]`, `a ≤ ℓ`, that are
   nonnegative on `[0, ∞)`, the kick is nonnegative: it lifts every positive odd profile, in
   particular the Perron state of the Z-type frozen odd form.
8. **Criticality.** The Weil form polarizes through the Weil source
   `𝒮(a) = (𝓛_Da − Φcosh a) − 2B(Φa)Φ sinh + 2A(Φa)Φ cosh`: `Ẑ(Φ(a + b)) = Ẑ(Φa) + Ẑ(Φb) + 2∫b𝒮(a)`.
   A gauge vanishing off `S` that attains the Rayleigh bound `μ` of the window solves `𝒮(a) = μΦ²a`
   on `S`; in its own gauge `Ẑ(Φau) = J_{Φa}(u) + μ∫u²(Φa)² + 2V_s − 2V_c`. A zero mode of a
   nonnegative window is a pole-charged harmonic gauge, and in its gauge the window form is the
   signed Dirichlet form `J + 2V_s − 2V_c` with no potential. Under RH the sector ground energies tend
   to `0` doubly exponentially (ACT, GWZ) and margins have no slack (GWZ). Numerically the critical
   ground state is positive, the `k`-th sector eigenfunction has `k` nodes, even and odd eigenvalues
   interlace, and the edge value of the ground state tends to `0`.
9. **Reflection pairs and the smoothed prime count.** For `f` left of `m` and `R(v) = 2m − v`, the
   cross-correlation of `f` and `f∘R` is the self-convolution `(f⋆f)(2m − ·)`, and the ordered
   coupling is `𝒞_m(f) = 𝓗_m(f) − Σ_nΛ(n)n^{−1/2}(f⋆f)(2m − log n)`: the pole square of the collar
   Hankel form is the main term of the smoothed prime count, the trivial-zero squares its
   exponentially small corrections. `W(f ± f∘R) = 2W(f) ± 2𝒞_m(f)`, so `|𝒞_m(f)| ≤ W(f)` exactly
   when the pair is nonnegative; across all scales this is the square-root form of §1.1 of the
   review. On each reflection sector the growth
   step is exact: `W(x_L + y ± x_L∘R) = 2W(x_L + y) − W(y) ± 2𝒞_m(x_L)` for an interior piece
   `y∘R = ±y`; the only arithmetic of the step is the prime-count error of the collar piece. At
   the centre of a symmetric window the reflection is the parity, and a cut-off at the centre with
   bounded height and shrinking width moves Weil's form by a vanishing amount; so each parity
   sector of `[−a, a]` is exactly the band `±𝒞₀(f) ≤ W(f)` on the half-window `[−a, 0]`, and a
   window certificate is a statement about one half-window, one Hankel form and the prime values
   `(f⋆f)(−log n)`, `log n ≤ 2a`.
10. **The growth step is one mixed pairing.** `W ≥ 0` on `W_{ℓ+ε}` iff `W ≥ 0` on `W_ℓ` and
   `W(τ_εu, v)² ≤ W(u)W(v)` for all `u, v` on `W_ℓ`; at a stage `ℓ = log(N+1)` the pairing is the
   frozen pairing minus the new fold at lag `ℓ − ε`, and the step is a Carathéodory disk (CSTW).
   The collar inequalities of GWZ — on a window already nonnegative, a frozen-negative even test has
   more antisymmetric than symmetric collar mass, an odd one the reverse — assume positivity on the
   enlarged window and describe where a failure cannot sit; they are consequences of the step, not
   a mechanism for it. On reflection-paired collar data the frozen coupling is the collar Hankel
   form, one pole square against the trivial-zero squares (the Gamma symbol's indefiniteness), and
   the pieces' own forms, nonnegative by the premise on the shorter window, are what must pay it
   together with the earlier-fold transports and the new fold.
11. **Charges survive energy limits.** On prime-supported input the generator splits as one
    coherent constant minus diagonal prime rows, `GF_a = P_M(a) − Σ_p τ(p)a_pe_p`, with the
    cutoff-independent bound `mean|GF_a − P_M(a)|² ≤ (log 2/2)L_M(a)`; the coefficients
    `a_p = (t/B_M)√(p−1)/p` carry charge `t` with energy `t²/B_M → 0`, harmonic-pole-neutral, with
    vanishing physical input uniformly over horizons; `G` is a derivation across coprime conductors,
    `G(e_{ab}) = e_bG(e_a) + e_aG(e_b)`, so the same coefficients on `e_{mp}` carry the nonconstant
    output `t·e_m` with vanishing energy; prime residuals carry a quadratic logarithmic conductor
    cost attained on explicit packets (CSAR). A certificate that passes to a limit in energy or
    physical norm has lost a charge the complete form still carries; norms are not signed forms.
12. **The complete form is a signed network with retained boundary terms.** On a packet the
    complete energy is prime jump energy, half the affine Dirichlet energy, the Mertens–Euler
    diagonal, minus the shell degree, plus centre, cross, pole-error and overlap terms; the prime
    successor edges `(n, pn + 1)` bound nonconstant packet mass by the affine energy with factor
    `(B_{⌊N/16Q²⌋} − B_Q)/64` (ACoT); the divisor jet completes to the exact squares
    `Σ_{m∣D}Σ_{k∣m}Λ(m/k)φ(k)(f(m) − f(k))²`, zero only on constant profiles; bounded base profiles
    with mean-zero periodic top-band perturbations have joint shell–pole cancellation uniform in the
    overlap (SSh). These are the identities in which a charge can be seen to be paid.
13. **Two landings; the Liouville reading.** The spline orbit accepts constants and rejects rate
    (AOG, ACP; mechanism statement in §1). Along translation the collided form has second
    difference `Σ_ρ m_ρ(2cosh(2(Re ρ − ½)L) − 2)|tr f(ρ)|² ≥ 0` (APol), so RH is the statement that an
    explicit convex functional of the translation parameter is bounded, hence constant: a proof of
    this field is a Liouville theorem for a critical form, not a spectral gap.
14. **The critical curve of the complete family.** Below the eighth root the complete matrix is
    positive definite on the whole space (CACT); along `c⁸/log N → R` a horizon window converges to
    the pencil `a_φW(H) + (7J(1)/R)‖H‖²_{−8}`, is eventually positive below `R*(H)` and negative above
    it, and on the equality face the canonical clock `c_N = max(1, (R log N)^{1/8})` gives eventually
    negative energy; twisted sectors are zero-blind counts; the count form ends at the resolution
    `m ≍ c` (AHD). RH is the positivity of the conductor Gram at every `R`, for every coefficient
    vector over all conductors `e ≤ N` (HWV). One small multiple with all vectors is a capstone in
    source, not yet dependency-closed (CACT). The sign therefore lives in the Schur form of the
    conductor block against the complement as the cutoff grows, and in the charges of mechanism 11.

## 5. Questions

| Question (review-0311 §2.7, §2.8) | Status |
|---|---|
| Does the first prime stage admit a signed supersolution (2.8)? | Literal form: **no.** No `C²_c` function nonnegative on `[0, ∞)` and positive on `(0, a)` satisfies ACT's folded supersolution inequality on `(0, a)` for any `a > e^{−3/4}`, in particular on the unit odd window (`not_exists_foldedWindowSupersolution_half`); no nonnegative `C²_c` gauge is a two-sided Markov supersolution on an interval longer than `e^{−3/4}` (`not_exists_markovWindowSupersolution`). Survivor: the pole-charged supersolution of mechanism 4 in the odd sector — an odd gauge whose Markov defect carries the sinh charge — gives `Ẑ ≥ J_{Φω}` (`signedJumpEnergy_add_le_fullZeroForm_of_sinhCharged`), and the remaining condition is the nonnegativity of the signed Dirichlet form, whose only negative conductances are the prime-2 anti-diagonal. Explicit survivors exist: every shifted ground state is a strict pole-charged supersolution on the unit window, `Ẑ(Φω_au) ≥ 2S_a(u) − D_a(u) + 8τ_{1/2}(a)∫_{x>0}u²m_a sinh` with `τ_{1/2}(a) > 0` (`fullZeroForm_shiftedGroundState_ge`, `outsideCharge_pos`); on the line the slack vanishes and the inequality at one shift is RH (ACT). Numerically the odd ground state is positive on `(0, ½]` with energy `≈ 1.95·10⁻⁴`; it is a signed supersolution in this sense. **Exact content:** the complete odd unit window is equivalent to the half-window Markov–Hankel inequality `4S(f)² ≤ M(f) + Σ_{j≥0}m_j(f)² + w₂(f⋆f)(−log 2)` on `[−½, 0]` (`odd_unit_nonneg_iff_markov_hankel`), which reads the arithmetic only through `w₂` and is convex in it (`convex_unitBandWeights`). Its truth is a quantitative statement with margin `≈ 2·10⁻⁴`; its certificate is open |
| How does a supersolution pass a stage? | In any gauge the kick is a positive source plus a negative anti-diagonal conductance on the collar (`kick_eq_source_sub_collarConductance`); on `τ`-symmetric profiles it is the pure source, on `τ`-antisymmetric ones minus it; it is nonnegative on every positive odd profile (`kick_nonneg_of_nonneg_of_support`). A supersolution passes the stage by absorbing the source into its potential and dominating the new negative conductance by the light cone; the `τ`-antisymmetric collar data carry the whole cost. The collar correction that absorbs the kick is the collar's own light cone: on odd tests the anti-diagonal of `n` is carried at the ratio `2Λ(n)n^{−1/2}e^{h}` (`kick_add_collarLevyEnergy_nonneg`), below `1` for thin collars of the first prime (`√2 log 2 < 1`), above `1` for `3 ≤ p ≤ 73`, where jumps leaving the collar, the source or the pole must pay |
| What replaces Allegretto–Piepenbrink when the full form carries a rank-two indefinite pole term? | The pole-charged representation (`fullZeroForm_phiDoob_mul_eq`): each square becomes a charge of the gauge — the negative square must be carried by the defect as `2σ_sΦ sinh`, the positive square allows a deficit `2σ_cΦ cosh` at the price of a rank-one negative conductance — and positivity reduces to a pointwise charged inequality plus nonnegativity of a signed Dirichlet form. For the Markov part alone the easy half holds on windows (`markovEnergy_phiDoob_mul_nonneg_of_windowSupersolution`) and is void past `e^{−3/4}` |
| What is the Agmon ground state of a critical window, and how does it relate to the zero modes of a first failure? | A Rayleigh-critical gauge solves the pole-charged source equation `𝒮(a) = μΦ²a` on the window (`weilSource_eq_of_rayleighCritical`) and represents the window form in its own gauge as a signed Dirichlet form plus `μ` times mass (`fullZeroForm_phiDoob_mul_eq_of_rayleighCritical`). A zero mode of a first failure is a pole-charged harmonic gauge, its Markov defect exactly `2BΦ sinh − 2AΦ cosh`, and in its gauge the window form has no potential (`weilSource_eq_zero_of_zeroMode`, `fullZeroForm_phiDoob_mul_eq_of_zeroMode`). On a nonnegative window symmetric about `m` the two-site band holds for every collar test (`abs_coupling_le_weilQuad_of_window`), and a first failure of it is a reflection pair: if `|𝒞_m(f)| = W(f)`, then `F₀ = f + εf∘R` (`ε = ±1`, two sites and one sign) is a zero of the window form with `F₀∘R = εF₀`, and its gauge `F₀/Φ` is pole-charged harmonic on the window (`zeroMode_of_tight_band`); its collar shape is the mirror image of the collar piece. Perron, oscillation and edge behaviour of the critical ground state are numerical (mechanism 8) and open |
| What exactly remains on the odd unit window? | **In half-window form:** the odd unit window is nonnegative iff `W(f) ≥ 𝓗₀(f) − (log 2/√2)(f⋆f)(−log 2)` for every `C²` test `f` supported in `[−½, 0]` (`odd_unit_nonneg_iff`): Weil's form on a half-window of length `½` (archimedean there), the collar Hankel form at the centre, and one prime value. The condition is linear in the prime-two weight: the odd unit window holds iff `w₂ = log 2/√2` lies in an interval of admissible weights (`odd_unit_nonneg_iff_mem_unitBandWeights`, `convex_unitBandWeights`), so it reads exactly one arithmetic number. **In Markov–Hankel form:** since `ω(t) = Σ_j e^{−(2j+½)t}`, the archimedean coupling of a half-window test with its mirror is the positive Hankel form `Σ_j m_j(f)²`, `m_j(f) = ∫f(u)e^{(2j+½)u}du`, and the odd unit window holds iff `4S(f)² ≤ M(f) + Σ_{j≥0}m_j(f)² + w₂(f⋆f)(−log 2)` (`odd_unit_nonneg_iff_markov_hankel`): the pole debt of the pair is paid by the Markov part of the half — which alone dies at width `e^{−3/4} < ½` — the reflection squares and the prime value. On every symmetric window the odd sector is `4S² ≤ M + Σ_jm_j² + P` and the even sector `Σ_jm_j² + P ≤ M + 4C²`, `P(f) = Σ_nw_n(f⋆f)(−log n)` (`odd_nonneg_iff_markov_hankel`, `even_nonneg_iff_markov_hankel`): across the centre the archimedean place pays the odd sinh debt and charges the even cosh credit. More generally each parity sector of `[−a, a]` is the band at the centre, `±𝒞₀(f) ≤ W(f)` for every half-window test (`odd_nonneg_iff_centreCoupling_le`, `even_nonneg_iff_neg_centreCoupling_le`). In moment form: with `L(F) = ∫xF`, `b = 3203/320` and `R(F) = W(F) + bL(F)²` on odd `C²` tests supported in `[−½, ½]`: `R(F) ≥ ‖F‖²/1000` (WTZ), so the open statement is the capacity bound `b·sup_{F≠0} L(F)²/R(F) ≤ 1`; the exact Gamma remainder and the signed prime-2 correlation must be kept (the retained Gamma lower form has a negative direction, and the exterior Gamma reserve alone cannot restore its sign, WTZ). A certificate of it is a bounded-window advance and the template for the first mixed pairing; no induction law follows from it |
| Which identity pays the mixed pairing of a growth step with premises on the shorter window? | On each reflection sector the step is the exact identity `W(x_L + y ± x_L∘R) = 2W(x_L + y) − W(y) ± 2𝒞_m(x_L)` (`weilQuad_stage_even`, `weilQuad_stage_odd`), with `𝒞_m(x_L)` the collar Hankel form minus the smoothed prime count of the collar piece (`orderedCoupling_collarReflect`); the premises `W(x_L + y), W(y)` live on the shorter window. The inequality `2W(x_L + y) − W(y) ± 2𝒞_m(x_L) ≥ 0` is open at every stage past the proved lengths. Without reflection pairing, stage one is the inequality `W(x_L) + W(x_R) + 2⟨μ(x_L), ν(x_R)⟩ + Φ_ε(μ(x_L), ν(x_R)) ≥ 2w₂∫x_L(u)x_R(u + log 2)du` of the trivial-divisor moment sequences against one lag overlap (CSTW closed form), equivalently the contraction `W(τ_εu, v)² ≤ W(u)W(v)` on `W_{log 2}`; stage two adds only the `T₂` transports |
| Which term of the complete form pays a receiving charge that energy limits erase? | Open; the first test is the complete energy on the harmonic-pole-neutral prime-charge families and their coprime fibre products at `c ≍ (log N)^{1/8}`, with every term of the decomposition retained: paid by the affine successor energy, cancelled by shell–pole terms, or a signed residual against the complement |
| What is the Schur form of the conductor block against the coercive complement at the critical curve, as the cutoff grows? | Open; separate positive blocks do not suffice; the all-`R`, all-vector conductor Gram is the landing |
| What is the spectral theory of the collar Hankel form `|μ_1|² − Σ_k|μ_{−2k}|²` on collar classes? | On reflection-paired data `g = f∘R`, `R(v) = 2m − v`, CSTW's moment pairing is `𝓗_m(f) = e^mμ_{1/2}(f)² − Σ_k e^{2mσ_k}μ_{σ_k}(f)²` (`momentPairing_collarReflect`). For collar tests in `[p, q]`, `q < m`: the trivial zeros see every test (`eq_zero_of_trivialMoments_eq_zero`); `𝓗_m` is negative definite on the pole hyperplane (`collarHankel_neg_of_poleMoment_zero`) and has at most one positive square (`exists_collarHankel_nonpos`); its trivial-zero squares decay like `e^{−(4k+5)(m−q)}`, so it is a rank-`(1, K)` form up to `‖f‖₁²e^{−(4K+5)(m−q)}/(1 − e^{−4(m−q)})` (`abs_collarHankel_sub_truncation_le`). On nonnegative collar data the sign flips at the plastic distance: `𝓗_m(f) ≥ (∫f)²(e^d − e^{−5d}/(1 − e^{−4d}))`, `d = m − q`, so `𝓗_m > 0` once `e^{6d} − e^{2d} > 1` (`2d > log ρ`, `ρ³ = ρ + 1`) and the positive index is exactly one (`collarHankel_pos_of_nonneg`); within the plastic distance `𝓗_m < 0` on nonnegative data (`collarHankel_neg_of_nonneg`). **Spectral decay:** on the collar tests annihilating the pole moment and the first `K` trivial-zero moments, `−(q − p)ε_K‖f‖₂² ≤ 𝓗_m(f) ≤ 0` with `ε_K = e^{−(4K+5)d}/(1 − e^{−4d})` (`abs_collarHankel_le_sq_of_moments_zero`), so by min–max at most `K + 1` eigenvalues have modulus above `(q − p)ε_K`: the spectrum decays at least geometrically with ratio `e^{−4d}`. Its negative index is infinite: for every `n` there are `n` collar tests on whose span it is negative definite (`exists_collarHankel_negDefinite`), so beyond the plastic distance its inertia is `(1, ∞)`. Open: the matching lower bound (exact asymptotics) and its domination by the pieces' forms; its continuum shadow is the Gamma symbol `Re ψ(¼ + iξ/2) − log π` with Weyl law `≈ 2A` negative directions and the zero-free band `|ξ| < γ_1` of Weil's spectral measure |

## 6. Tools

**Developed.**
- Markov-negative plateaus: exact self-energy of a smooth plateau atom against the creation
  potential; translation invariance of the Markov form; the death width `e^{−3/4}`.
- Ground-state representation of every `C²_c` gauge in the Doob gauge, continuity of the two-sided
  generator (dominated convergence, locally uniform prime summability), window
  Allegretto–Piepenbrink, quotients `G/(Φω)` through gauges positive on an interval.
- Folded-to-two-sided reduction and the comparison principle for lowered gauges.
- Pole charges: sinh and cosh charges of a gauge on a window, the pole-charged defect, charge
  variances with Cauchy–Schwarz, the exact pole-charged representation.
- Polarization of the Weil form through the Weil source; variational source law on a window via the
  fundamental lemma; own-gauge representation of critical gauges.
- Collar reflection calculus: anti-diagonal form of odd correlations, source/conductance split of
  the kick, sector values.
- Collar Hankel calculus: reflected moments, trivial-zero completeness by polynomial moments in
  `e^{2u}`, inertia, geometric truncation.
- Reflection-pair calculus: self-convolution reading of ordered couplings, two-site identities,
  sector form of the three-piece chain law.
- Beurling–Deny calculus on odd tests: the positive odd profile `sign(x)|F|`, Lipschitz and
  support transfer, comparison of AIP surplus energies on the quadrant, anti-diagonal kick
  comparison.

- Packed nonlocal paths on collars: the reflection inequality `∫(F − F∘R)² + ½E(F + F∘R) ≤ 2E(F)`
  from the first regional Legendre gap (sharp on the linear profile), its physical rescaling, the
  comparison `e^{−h}E_C ≤ 2A_C` with the collar's light cone, and the bound of every prime
  anti-diagonal on odd tests by its collar's light cone at the ratio `2Λ(n)n^{−1/2}e^{h}`.

- Sharpness of the packed path: the Legendre gap `2` is the infimum of the regional Rayleigh
  quotient on admissible odd profiles (edge layers cost `O(δ^{1/2})`), `2A_C ≤ (1 + 4h)E_C`, and
  for `λ(1 + 4h) < 2w` an admissible odd test defeats `λ` times the collar light cone; the best
  constant lies in `[2w/(1 + 4h), 2we^{h}]`. The ratio `2Λ(n)/√n` is below `1` for `n = 2` (as
  `log 2 < 1/√2`) and every proper prime power, above `1` exactly for the primes `3 ≤ p ≤ 73`, for
  which the frustration must be paid by jumps leaving the collar, by the source or by the pole. The
  first-fold strip version with the Gamma floor is WTZ's, the finite Kron theory SAEI's.

- The odd light cone in the Doob gauge: for every odd gauge positive on the half-line and every
  even profile, each shift splits as twice the same-side jumps minus the anti-diagonal jumps, and
  the archimedean part of `J_{Φω}` folds to `2∫∫(ω(s) − ω(s + 2x))J_s(x) ≥ 0`.

**To be developed here.**
- Mixed-pairing calculus: bounds on `W(τ_εu, v)` whose premises are positivity on the shorter
  window and arithmetic; the collar Hankel form on reflection-paired data.
- Charge-retaining limits: passages to the critical curve that keep receiving charges or prove
  their cancellation in the complete form.
- Schur forms of conductor blocks against coercive complements.

**Used from the corpus.** WTZ (the first regional Legendre gap pays the variation on the prime-two
strip, `firstFold_strip_coercive`: the packed path of the first fold); ACT (ground-state identities, folded generator, light cone, two-moment
law, Allegretto–Piepenbrink for finite jump forms, hub/Schur steps); RHTower (`markovForm`,
`weil_eq_markovForm_add_pole`, sinh capacity, CCM ground energy); GWZ (two-collar form, kick as collar
Rosati form, two sites decide, zero modes); CSTW (frozen form in closed form); CWS (window form,
cosh capacity criterion, one negative square on short windows); WTZ/F1 (first-fold payments on the
odd unit window); LST (regional logarithmic spectrum).
Also: CSTW (ordered coupling, transmission through the trivial divisor, frozen forms in closed
form, growth law, stage disk); AOG and ACP (spline-orbit growth and tensor-loss receivers); CSAR
(receiving charges, generator decomposition, derivation law across coprime conductors, residual
scales); ACoT (complete-form decomposition, prime successor edges); SSh (divisor-jet squares,
top-band joint cancellation); AHD (pencil, critical multiple, equality face, window index); HWV
(conductor Gram receiver); CACT (whole-space positivity below the eighth root; the critical-multiple
capstone in source); WTZ (the uniform Gamma reserve cannot pay the first fold; the two-moment
first-fold form is negative on a smooth test); APol (second difference of the collided form).

## 7. Open research topics

The topics are of three kinds. Topics 6, 8, 9 and 11 are RH-strength: taken at every stage, for every
coefficient vector or with zero rate, each is equivalent to RH. Topics 1 and 2 are bounded
inequalities with explicit small margins, whose certificates are quantitative. Topics 3, 4, 5, 7
and 10 are structural.

1. Certify the odd unit window: the half-window Markov–Hankel inequality
   `4S² ≤ M + Σ_jm_j² + w₂(f⋆f)(−log 2)` on `[−½, 0]`, or the signed Dirichlet form
   `2S_a − D_a + 8τ_{1/2}(a)∫u²m_a sinh` of one shifted gauge; margin `≈ 2·10⁻⁴`.
2. The even sector of the first prime stage: `Σ_jm_j² + P ≤ M + 4C²` on the half-window, the
   Perron state of `M` and its cosh charge.
3. Perron and oscillation properties of `W` on windows.
4. The critical ground state: edge value, shape at the collars, limit along the tower.
5. Calibration across the tower: a single window reads finitely many weights, convexly; the first
   stage rejects the frozen and flipped weights and forces the sign of `Λ(2)`. Euler twins,
   `ζ(s)ζ(s − ε)`, Epstein and golden data must fail on some window of the tower.
6. The mixed-pairing bound of the growth step at every stage, with premises on the shorter window;
   stage one in CSTW's moment form, stage two with the `T₂` transports, stage three on the weighted
   path `2, 3, 2` and the rational Hecke graphs of WTZ.
7. The collar Hankel form: the lower bound matching its geometric spectral decay `e^{−4d}`, and
   its coupling to the archimedean jumps.
8. Charge accounting on the complete family: the complete energy of the prime-charge families and
   their coprime fibres at the critical overlap, term by term; classification of which modes'
   charges survive vanishing energy; the term that pays.
9. The Schur form of the conductor block against the complement at the critical curve as the
   cutoff grows; dependency closure of the critical-multiple capstone.
10. The continuum canonical system of a bump: the Hankel system of the zero measure, of which the
    lattice jet system gives the first terms.
11. Rate certificates: estimates landing on the spline-orbit or tensor-loss receivers, where
    constants are free.

## 8. Pillar theorems

| Theorem | Lean | Status |
|---|---|---|
| The Markov part is negative on a plateau of width `e^{−3/4}` | `exists_markovEnergy_neg_of_support_le`, `exists_markovEnergy_neg_of_support_Icc` | unconditional |
| Window Allegretto–Piepenbrink for the Markov part | `markovEnergy_phiDoob_mul_eq_signedJump_add_defect`, `markovEnergy_phiDoob_mul_nonneg_of_windowSupersolution` | unconditional |
| No Markov ground state on an interval longer than `e^{−3/4}` | `not_exists_markovWindowSupersolution` | unconditional |
| The folded criterion is void on the unit odd window | `foldedGenerator_eq_twoSidedGenerator_abs`, `twoSidedGenerator_le_of_le_of_eqOn`, `not_exists_foldedWindowSupersolution`, `not_exists_foldedWindowSupersolution_half` | unconditional |
| Pole-charged representation; sinh charge; cosh credit | `fullZeroForm_phiDoob_mul_eq`, `signedJumpEnergy_add_le_fullZeroForm_of_sinhCharged`, `signedJumpEnergy_sub_le_fullZeroForm_of_coshCharged`, `chargeVariance_nonneg` | unconditional |
| Polarization through the Weil source; source law of critical gauges; own-gauge representation | `fullZeroForm_phiDoob_add`, `weilSource_eq_of_rayleighCritical`, `fullZeroForm_phiDoob_mul_eq_of_rayleighCritical` | unconditional |
| Zero modes are pole-charged harmonic gauges | `weilSource_eq_zero_of_zeroMode`, `fullZeroForm_phiDoob_mul_eq_of_zeroMode` | unconditional (zero modes exist only off RH) |
| The kick is a positive source and a negative collar conductance | `integral_mul_shift_eq_neg_antidiagonal`, `kick_eq_source_sub_collarConductance`, `kick_eq_source_of_symmetric`, `kick_eq_neg_source_of_antisymmetric`, `kick_nonneg_of_nonneg_of_support` | unconditional |
| The spectrum of the collar Hankel form decays geometrically on the annihilators of its moments; its negative index is infinite | `abs_collarHankel_le_of_moments_zero`, `sq_integral_abs_le`, `abs_collarHankel_le_sq_of_moments_zero`, `exists_collarHankel_negDefinite` | unconditional |
| The collar Hankel form: reflection pairing, completeness, inertia, truncation, plastic distance | `momentPairing_collarReflect`, `momentPairing_neg_collarReflect`, `eq_zero_of_trivialMoments_eq_zero`, `collarHankel_neg_of_poleMoment_zero`, `exists_collarHankel_nonpos`, `abs_collarHankel_sub_truncation_le`, `collarHankel_ge_of_nonneg`, `collarHankel_pos_of_nonneg`, `collarHankel_neg_of_nonneg` | unconditional |
| Theta gauges: total charges, outside-charge identity, criticality on the line, even-sector deficit | `integral_thetaGauge_mul_cosh`, `integral_thetaGauge_mul_sinh`, `fullZeroForm_thetaGauge_eq`, `fullZeroForm_thetaGauge_eq_univ`, `fullZeroForm_evenThetaGauge_window`, `fullZeroForm_evenThetaGauge_le` | unconditional |
| Shifted ground states are strict pole-charged supersolutions on every window | `fullZeroForm_shiftedGroundState_window`, `fullZeroForm_shiftedGroundState_ge`, `outsideCharge_pos`, `sq_setIntegral_mul_le` | unconditional |
| The frozen odd form is Markov and the kick is not | `levyEnergy_oddAbs_le`, `sq_sinhPairing_le_oddAbs`, `frozenOddForm_oddAbs_le`, `kick_le_kick_oddAbs`, `markovForm_two_sub_one`, `firstStage_frustration` | unconditional |
| On reflection pairs the coupling is the smoothed prime count; the growth step on a reflection sector | `crossCorr_collarReflect`, `orderedCoupling_collarReflect`, `weilQuad_add_collarReflect`, `weilQuad_sub_collarReflect`, `weilQuad_stage_even`, `weilQuad_stage_odd` | unconditional |
| The band is positivity on the reflection pair; the first prime stage opens positive on reflection pairs of total length `≤ 181/250` | `abs_coupling_le_weilQuad_iff`, `abs_coupling_le_weilQuad_of_short` | unconditional |
| The light cone of a collar carries its reflection; prime anti-diagonals on odd tests are carried at the ratio `2Λ(n)n^{−1/2}e^{h}`; the ratio is below `1` for prime `2`, above for `3` | `integral_sub_reflect_sq_add_le`, `integral_sub_reflect_sq_id`, `neg_half_regionalLogEnergy_le_integral_mul_reflect`, `collarLogEnergy_eq`, `neg_half_collarLogEnergy_le`, `exp_neg_mul_collarLogEnergy_le`, `neg_collarLogEnergy_le_kick`, `kick_add_collarLevyEnergy_nonneg`, `two_mul_log_two_div_sqrt_two_lt_one`, `one_lt_two_mul_log_three_div_sqrt_three` | unconditional |
| The parity sectors of a symmetric window are the band at its centre; the odd unit window in half-window form reads one prime weight, convexly | `le_weilQuad_of_centreCutoff`, `odd_nonneg_iff_centreCoupling_le`, `even_nonneg_iff_neg_centreCoupling_le`, `centreCoupling_eq_of_half`, `odd_unit_nonneg_iff`, `odd_unit_nonneg_iff_mem_unitBandWeights`, `convex_unitBandWeights`, `odd_unit_nonneg_iff_markov_hankel`, `centreCoupling_eq_moments`, `odd_nonneg_iff_markov_hankel`, `even_nonneg_iff_markov_hankel` | unconditional |
| The first stage rejects the frozen and the flipped divisor; the sign of `Λ(2)` is forced | `firstStageForm_zeta`, `convex_firstStageWeights`, `zero_notMem_firstStageWeights`, `neg_notMem_firstStageWeights`, `pos_of_mem_firstStageWeights` | unconditional |
| The odd light cone in the Doob gauge: per-shift split into same-side and anti-diagonal jumps; the archimedean part is a nonnegative folded form | `integral_signedShiftJump_eq_split_of_odd`, `integral_arch_mul_gaugeJumpProfile_eq_fold_of_odd`, `integral_arch_mul_gaugeJumpProfile_nonneg_of_odd` | unconditional |
| The collar ratio is sharp: the Legendre gap is the infimum on admissible odd profiles; the collar of prime `3` does not pay its own frustration | `regionalLogEnergy_le_of_layer`, `abs_regionalLogPair_le`, `exists_odd_profile_ratio_lt`, `two_mul_collarLevyEnergy_le`, `exists_kick_add_collarLevyEnergy_neg`, `exists_prime_three_collar_unpaid` | unconditional |
| Weil's form is ACT's full zero form; on a nonnegative symmetric window the band holds, and a tight band has a reflection-pair zero mode with pole-charged harmonic gauge | `fullZeroForm_eq_weilQuad`, `abs_coupling_le_weilQuad_of_window`, `zeroMode_of_tight_band_even`, `zeroMode_of_tight_band_odd`, `zeroMode_of_tight_band` | unconditional |

## 9. Traps

| Trap | Truth |
|---|---|
| A positive folded supersolution certifies the odd sector | It certifies the Markov part only, and forces `M ≥ 0` on every test supported in the half-window; `M` is negative on a plateau of width `e^{−3/4} < ½` |
| The window must be prime-free for a Markov certificate to fail | The Markov part dies at width `e^{−3/4} < log 2`, before the first prime acts; the base `181/250` is already out of reach of Markov certificates |
| A supersolution has to be positive up to the window edge | A `C²_c` gauge vanishing at an endpoint fails the inequality next to it; window gauges are positive on a neighbourhood of the closed interval and arbitrary outside |
| The archimedean jumps across the centre are neutral between the sectors | They are the positive Hankel form `Σ_j m_j(f)²` of the half-window test: a gain in the odd sector, a cost in the even sector |
| Both sectors gain from cutting the window | Only the odd sector: an odd theta gauge keeps its outside sinh charge as slack, an even theta gauge loses its outside cosh charge as deficit |
| The window slack of a shifted ground state is a free gain | The identity is exact: a large outside charge `τ_c(a)` comes with a large reflected energy `D_a`; the slack measures how far the window is from the critical (whole-line) case |
| The zero mode of a first failure is an arbitrary test | It is a pole-charged harmonic gauge on the window, and in its gauge the window form has no potential |
| The trivial-zero squares of the collar coupling are a small correction | They are an injective positive Hankel form: on the pole hyperplane the collar coupling is negative definite |
| The sign of the collar coupling on positive data is fixed | It flips at the plastic distance `log ρ`: positive for reflection pairs farther apart, negative closer in — the same threshold at which `2cosh(x/2) − ω(x)` changes sign |
| `|F|` is the worst odd test | On the first odd stage `sign(x)|F|` lowers the frozen form and raises the kick; neither `F` nor `F̃` dominates |
| The growth step needs the whole window | On a reflection sector it reads two forms on the shorter window and one number of the collar piece, `𝒞_m(x_L)` |
| The pole is a perturbation of a Markov form | It is a square of fixed sign in each sector; in the even sector it pays the Markov Perron state, in the odd sector it is the debt |
| Frustration comes from the primes | Only in the odd sector; in the even sector the primes are positive and the pole frustrates |
| A gauge can remove a negative conductance | Positive gauges never change the sign of a conductance |
| Kato's inequality handles frustrated edges | It compares with the form whose kick has the wrong sign, which is more negative than the frozen form |
| The kick is a cost | It is positive on every positive function; it lifts the frozen Perron state |
| Every prime's frustration can be paid inside its collar | The collar's light cone carries a prime anti-diagonal at the ratio `2Λ(n)n^{−1/2}e^{h}`, and no better than `2Λ(n)n^{−1/2}/(1 + 4h)` on admissible odd tests: below `1` for `2` (as `log 2 < 1/√2`), above `1` for `3` through `73`, whose collars provably do not pay (`exists_prime_three_collar_unpaid`) |
| The collar inequalities of GWZ give an induction across stages | They assume `W ≥ 0` on the enlarged window and conclude a strict inequality of collar masses, not sector membership; the growth step is the contraction law, whose mixed pairing must be bounded with premises on the shorter window |
| A proof must keep sharp constants everywhere | Only the window and lattice forms have no slack; the spline-orbit and tensor-loss receivers accept constant losses and reject only a positive rate |
| Convergence of inputs in energy controls the output | A constant charge `t` survives adjunction energy `t²/B_M → 0` and vanishing physical input; every nonconstant mode's charge is carried the same way through the derivation law |
| A large generator norm is a negative Weil direction | The centred output is bounded by `(log 2/2)` times the adjunction energy; norms and signed forms must be distinguished |
| The infimum of critical multiples over negative windows is a sub-RH invariant | `R₁(A) = inf R*(H)` over negative tests on `[−A, 0]` is nonincreasing in `A`; a lower bound tending to infinity is RH; `R₁(A) = ∞` is window positivity at length `A` |
| Positivity at one multiple of the critical curve continues to all multiples by continuity | On the equality face of the pencil the canonical clock is eventually negative; passing a zero margin needs new input |
| Bounded two-prime coupling with exact zero counts forces zero width | An abstract sign- and conjugation-symmetric divisor with exact spline weights, the full Riemann–von Mangoldt count and bounded coupling has positive unattained width (ACoT) |
| A certificate of the odd unit window would select `ζ` | It reads only `w₂ = log 2/√2`, convexly; fakes with the same archimedean place, pole and weight at `2` share it |
| The positive Euler twins show that only the strict Euler bound can select | Among positivity, the functional equation, an Euler product and Ramanujan bounds, the strict bound `θ < ½` is what excludes them; their conductor is `p²`, so exact source data also distinguish them |

## 10. Place in the research and relation to other programmes

| Programme | Relation |
|---|---|
| ACT | whole-line ground states of the Markov part in the Doob gauge; SWC works on windows, with the pole kept and every sign used |
| GWZ, CSTW | two-collar form, kick as collar Rosati form, Levinson recursion, frozen form in closed form; SWC supplies the ground-state side of the same stage step |
| WTZ, DZG | window algebra, stage form, stage identity in every gauge, zero modes as radical |
| CWS | window form, one negative square on short windows, cosh capacity criterion |
| RHTower | Markov–pole split, sinh capacity, CCM restricted ground energy |
| F1 cards | numerical payments on the odd unit window; SWC asks for the mechanism |
| AOG, ACP | spline-orbit growth and tensor-loss receivers: the rate landing for certificates that lose constants |
| CSAR | receiving charges, generator decomposition, derivation law; the obstruction to energy limits on the complete family |
| ACoT, SSh | complete-form decomposition, prime successor edges, divisor-jet squares, top-band joint cancellation: the signed network of the complete family |
| AHD, CACT, HWV | pencil at the critical curve, critical multiples, equality face; whole-space positivity below the eighth root; the all-`R` conductor Gram receiver |
| ATD | archimedean Tate domination closed; descent at dimension zero is Weil positivity |
| TH (theta sections) | the signed centre-mixed source-jet hierarchy, positive throughout the critical aperture iff RH, strict through rank eight: a source positivity with inputs disjoint from prime sums |

## 11. Success criteria and criteria for contributions

The criteria review-0311 §2.7 sets for the field: reproduce the base `181/250` and the first prime
stage; pay the pole's negative square; be critical; deliver the two-site band; force `Λ` and fail
for flips, twins, `ζ(s)ζ(s − ε)`, Epstein and golden data; use the functional equation and the Euler
product together.

| Criterion | Status in SWC |
|---|---|
| Base `181/250` and first prime stage | The two-site band with the prime `2` inside holds on every reflection pair of total length `≤ 181/250` (`abs_coupling_le_weilQuad_of_short`, from the SPATL base); a signed-supersolution proof of the base itself is open (a Markov one cannot exist past `e^{−3/4}`) |
| The pole's negative square | Paid by a sinh charge of the gauge (`signedJumpEnergy_add_le_fullZeroForm_of_sinhCharged`); shifted ground states carry it with window slack (`fullZeroForm_shiftedGroundState_ge`) |
| Criticality | Critical gauges solve the pole-charged source equation and represent the window form without slack in their own gauge (`weilSource_eq_of_rayleighCritical`, `fullZeroForm_phiDoob_mul_eq_of_zeroMode`); on the line the shifted-gauge slack vanishes |
| Two-site band | Exact form `|𝓗_m(f) − Σ_nΛ(n)n^{−1/2}(f⋆f)(2m − log n)| ≤ W(f)` ⇔ positivity of the reflection pair (`abs_coupling_le_weilQuad_iff`) |
| Force `Λ`; fail for fakes | At the first prime stage (window length `21/20`) the admissible prime-two weights form an interval that excludes the frozen weight `0` and the flipped weight `−w₂` (`convex_firstStageWeights`, `zero_notMem_firstStageWeights`, `neg_notMem_firstStageWeights`); if the first stage of `ζ` is nonnegative, every admissible weight is positive, so the sign of `Λ(2)` is forced (`pos_of_mem_firstStageWeights`). A single window cannot force `Λ` beyond such intervals: the odd unit window reads exactly the weight `w₂` and is a convex condition on it (`convex_unitBandWeights`), so every divisor with the archimedean place, pole and weight at `2` of `ζ` passes or fails it with `ζ`. Selection is a property of the tower (GWZ lattice selection, ACT selectivity), read by SWC certificates only through the kicks |
| Functional equation and Euler product | The pole's hyperbolic pair and the trivial divisor (functional equation) meet the prime anti-diagonals (Euler product) in the same signed form; no SWC statement uses one without the other |

A contribution must be exact (an identity, an equivalence, a classification, or a no-go with its
strongest positive survivor), keep every sign of the form, say which primes and which lengths it
reads, and be unconditional.

Further criteria. Deliver the all-`R`, all-vector conductor Gram of the complete family, or an
exact Schur form of the conductor block that lands on it. Retain receiving charges through every
limit, or prove their cancellation in the complete form. Lose constants only where a receiver
accepts them (spline orbit, tensor loss), never a rate. Bound each mixed pairing with premises on
the shorter window. Fail for the positive multiplicative twins of conductor `p²` with zeros at any
`Re s ∈ (½, 1)`.

## 12. Big picture

Weil's form on a window is a nonlocal Schrödinger form whose archimedean jumps are positive, whose
prime jumps carry signs, and whose pole is one hyperbolic pair split by parity into a positive even
square and a negative odd square. Its Markov part dies before the first prime; from there on every
certificate is signed: a positive gauge whose Doob form has negative conductances exactly on the
frustration loci and whose negative edges are paid by the positive network. Positivity passes
along three axes. Along the length it is one mixed pairing per growth step, `W(τ_εu, v)² ≤ W(u)W(v)`
with premises on the shorter window, whose arithmetic content is the trivial-divisor moment pairing
against one lag overlap, and whose cost sectors are the collar Hankel form of one pole square
against the trivial-zero squares. Along the conductor and the overlap it is the complete family at
the critical curve `c⁸ ≍ R log N`, where every twisted direction is a count, the untwisted window is
Weil's form at the pole of the frequency counts, and RH is the conductor Gram at every `R`; there
the certificate is an exact identity on the complete form that pays the receiving charges which
energy limits erase, in the Schur form of the conductor block against its complement. In every
exact decomposition the sign sits in one trivial direction, and the mixed pairing between that
direction and its complement is the whole problem. Under RH the critical objects have no margin:
lattice margins collapse, the Weil cone is a point, the equality face of the pencil is negative;
the certificate of this field is therefore a Liouville theorem for a critical signed form — bounded
along the dilation flow, hence constant — and not a spectral gap. Constants may be lost only on the
rate landings; a positive exponential rate may never be lost, since it is the zero width.

On a single window the theorems of this field fix where the sign sits. The Markov part dies at
width `e^{−3/4}`, before the first prime, so every certificate past it is pole-charged: the odd
square is carried by the sinh charge of the gauge, and the even square is a cosh credit paid for by
a rank-one negative conductance. Theta gauges are critical on the line, and a window reads the
charges outside it with the pole's signs: slack in the odd sector, deficit in the even sector. On
a reflection sector the growth step is a single identity whose only unknown is one number of the
collar piece, the collar Hankel form minus the smoothed prime count. The collar Hankel form has one
positive square, sees every test through the trivial zeros, and changes sign on positive data at
the plastic distance. A first failure of the band is a reflection pair whose gauge is pole-charged
harmonic. What remains is one inequality per stage, with no slack to lose: the certificate of the
odd unit window, and the growth-step inequality past `181/250`.
