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
   form; its ground energy on windows of length `L` is negative already for `L ≳ 0.22`, far below
   the first prime stage `L = log 2`. By Allegretto–Piepenbrink no positive supersolution of the
   Markov generator — two-sided or folded, in any gauge — exists on any window longer than that.
   A certificate on the first prime stage must keep the pole.

So the object of the field is not a Markov ground state but a signed one: a positive gauge whose
Doob-transformed form has negative conductances exactly on the frustration loci, and whose negative
edges are paid by the positive network.

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
| Pole capacities | `cap₋(a) = sup ⟨s, F⟩²/(2M(F))` over odd tests (sinh capacity); the cosh charge of the even Perron state |
| Collar, collar reflection | at stage `n`: `I = [log n − a, a]`, `τx = log n − x`; the kick on odd tests is `2w_n⟨U, τU⟩_I` |
| Kron reduction | Schur complement of a form onto a set of terminals; preserves Z-type |
| Markov threshold | `L_M`: the infimum of lengths on which `M` is indefinite |

## 3. Language

- **Z-type / Markov**: all conductances nonnegative; `|F|` does not raise the energy.
  **Frustrated**: some conductance negative and no sign gauge `F ↦ σF` removes all negative ones.
- **Gauge** vs **sign gauge**: a positive rescaling `F = hu` changes potentials, never the sign of a
  conductance; a sign gauge flips signs of conductances along a cut.
- **Signed ground-state representation**: `W(hu) = D_h(u) + ∫g_h h²u²`. **Neumann** and
  **Dirichlet** forms of a reflected edge are the two ways of writing `(aα + bβ)²`; only the Neumann
  form has a nonnegative remainder, only the Dirichlet form has the odd generator as potential.
- **Kron domination**: the negative network is dominated by the Kron reduction of the positive
  network onto the frustration locus.
- **Critical**: the sector ground energy tends to `0` along the tower. **Agmon ground state**: the
  minimizer of `W_±` on a window, normalized; **edge value**: its value at `x = a`.
- **Perron property**: the sector ground state has no node in `(0, a)`. **Oscillation property**: the
  `k`-th sector eigenfunction has `k` nodes in `(0, a)`, and even and odd eigenvalues interlace.

## 4. Mechanisms

1. **Parity split of the hyperbolic pair.** `W` commutes with `x ↦ −x`, `⟨c, F⟩ = 0` on odd and
   `⟨s, F⟩ = 0` on even tests. Each sector carries one square of the pole with a fixed sign.
2. **Sector conductances.** The odd light cone `κ(|x − y|) − κ(x + y) > 0` (ACT) is the archimedean
   place and the pole together; in the odd sector every failure of positivity sits on a prime
   anti-diagonal. The even fold `κ(|x − y|) + κ(x + y)` is negative at long range; the pole's
   positive square is the only anti-Markov term (RHTower).
3. **Markov death.** `M` is translation invariant and Z-type, so its ground energy on windows of
   length `L` is nonincreasing in `L`, attained by an even positive (Perron) state; an explicit test
   makes it negative at an explicit length. A positive supersolution of the Markov generator on a
   half-window forces `M ≥ 0` on every test supported there; hence none exists past `L_M`.
4. **Pole capacities by sector.** Odd: `W₋ ≥ 0` iff `M ≥ 0` on odd tests and the sinh capacity is at
   most `1`; the negative pole square is paid by the odd Markov energy. Even: `W₊ ≥ 0` iff `M` has at
   most one negative even square and the cosh square pays it (Sherman–Morrison); the positive pole
   square pays the Markov Perron state.
5. **Signed ground-state representation.** For every gauge, `W(hu) = D_h(u) + ∫g_hh²u²`, with the
   sign of each Doob conductance equal to `sign(c_±)·sign(h(x)h(y))`. With `h` the sector ground
   state, `g_h = μ_±` and `D_h ≥ 0`: a positive ground state is a signed supersolution.
6. **Kron reduction of negative edges.** A signed Dirichlet form `D = D⁺ − D⁻` with `D⁻` carried by a
   terminal set is nonnegative iff the Kron reduction of `D⁺` onto the terminals dominates `D⁻`. For
   one negative edge this is effective conductance; at a stage it is the two-collar form of GWZ.
7. **Stage passage.** At stage `n` the kick on odd tests is `2w_n⟨U, τU⟩` on the collar: `+2w_n` on
   `τ`-symmetric and `−2w_n` on `τ`-antisymmetric collar data (GWZ: the collar Rosati form). It is
   positive on every positive function, in particular on the Perron state of the frozen form; the
   frozen-negative direction is lifted by the kick.
8. **Criticality.** Under RH the sector ground energies tend to `0` doubly exponentially (ACT, GWZ),
   and margins have no slack (GWZ). Numerically the critical ground state is positive and its edge
   value tends to `0`.

## 5. Questions

| Question (review-0311 §2.7, §2.8) | Status |
|---|---|
| Does the first prime stage admit a signed supersolution (2.8)? | Literal form (positive supersolution of the folded Markov generator): **no**, on every window past `L_M` (mechanism 3). Survivor: the odd sector form `W₋` with the prime-2 anti-diagonal retained; numerically its ground state is positive on `(0, ½]` with energy `≈ 1.95·10⁻⁴`, i.e. a signed supersolution exists; a certificate of it is open |
| How does a supersolution pass a stage? | Through the collar reflection: the kick is `2w⟨U, τU⟩`; the frozen Perron state is `τ`-positive and is lifted; the `τ`-antisymmetric collar data must be paid by the Kron-reduced frozen form |
| What replaces Allegretto–Piepenbrink when the full form carries a rank-two indefinite pole term? | Allegretto–Piepenbrink for the Markov part plus one capacity per sector (mechanism 4); with frustration, the signed supersolution with Kron domination (mechanisms 5–6) |
| What is the Agmon ground state of a critical window, and how does it relate to the zero modes of a first failure? | Target: Perron and oscillation properties, edge behaviour, the zero mode at a first failure as the critical ground state |

## 6. Tools

**To be developed here.**
- Sector calculus on symmetric windows: parity projections, `W`-orthogonality, sector pole squares.
- Explicit Markov-negative tests and the Markov threshold.
- Signed ground-state representations in any gauge, finite and continuum.
- Kron reduction of signed Dirichlet forms; effective conductance; packed paths.
- Sherman–Morrison capacities in each sector.
- Collar reflection calculus at a stage.

**Used from the corpus.** ACT (ground-state identities, folded generator, light cone, two-moment
law, Allegretto–Piepenbrink for finite jump forms, hub/Schur steps); RHTower (`markovForm`,
`weil_eq_markovForm_add_pole`, sinh capacity, CCM ground energy); GWZ (two-collar form, kick as collar
Rosati form, two sites decide, zero modes); CSTW (frozen form in closed form); CWS (window form,
cosh capacity criterion, one negative square on short windows); WTZ/F1 (first-fold payments on the
odd unit window); LST (regional logarithmic spectrum).

## 7. Open research topics

1. Certify the signed supersolution of the odd unit window: an explicit positive gauge with
   `g_h ≥ 0` and Kron domination of the prime-2 anti-diagonal.
2. The even sector of the first prime stage: Perron state of `M`, cosh charge, and its passage.
3. Perron and oscillation properties of `W` on windows.
4. The critical ground state: edge value, shape at the collars, limit along the tower.
5. Calibration: flips, Euler twins, `ζ(s)ζ(s − ε)`, Epstein and golden data must fail.

## 8. Pillar theorems

To be filled as they are proved.

## 9. Traps

| Trap | Truth |
|---|---|
| A positive folded supersolution certifies the odd sector | It certifies the Markov part only, and forces `M ≥ 0` on every test supported in the half-window; `M` is indefinite past `L_M ≈ 0.22` |
| The pole is a perturbation of a Markov form | It is a square of fixed sign in each sector; in the even sector it pays the Markov Perron state, in the odd sector it is the debt |
| Frustration comes from the primes | Only in the odd sector; in the even sector the primes are positive and the pole frustrates |
| A gauge can remove a negative conductance | Positive gauges never change the sign of a conductance |
| Kato's inequality handles frustrated edges | It compares with the form whose kick has the wrong sign, which is more negative than the frozen form |
| The kick is a cost | It is positive on every positive function; it lifts the frozen Perron state |

## 10. Place in the research and relation to other programmes

| Programme | Relation |
|---|---|
| ACT | whole-line ground states of the Markov part in the Doob gauge; SWC works on windows, with the pole kept and every sign used |
| GWZ, CSTW | two-collar form, kick as collar Rosati form, Levinson recursion, frozen form in closed form; SWC supplies the ground-state side of the same stage step |
| WTZ, DZG | window algebra, stage form, stage identity in every gauge, zero modes as radical |
| CWS | window form, one negative square on short windows, cosh capacity criterion |
| RHTower | Markov–pole split, sinh capacity, CCM restricted ground energy |
| F1 cards | numerical payments on the odd unit window; SWC asks for the mechanism |

## 11. Success criteria and criteria for contributions

The criteria review-0311 §2.7 sets for the field: reproduce the base `181/250` and the first prime
stage; pay the pole's negative square; be critical; deliver the two-site band; force `Λ` and fail
for flips, twins, `ζ(s)ζ(s − ε)`, Epstein and golden data; use the functional equation and the Euler
product together.

A contribution must be exact (an identity, an equivalence, a classification, or a no-go with its
strongest positive survivor), keep every sign of the form, say which primes and which lengths it
reads, and be unconditional.

## 12. Big picture

To be written.
