# Dimension-Zero Geometry of Spec ℤ (DZG)

Namespace `GaloisForLFunctions.DimensionZeroGeometryOfSpecZ`; umbrella `DimensionZeroGeometryOfSpecZ.lean`.
Every theorem is unconditional; equivalences with RH are labelled as such.

## 1. Motivation

On a window `W_A` (tests supported in `[−A, 0]`) the arithmetic acting on Weil's form is the Dirichlet
ring truncated at `⌊e^A⌋`, and Weil's arithmetic term is the derivative at dimension zero of a family
whose values in positive dimension are point counts (WTZ):

`Q(H) = Ω(0)τ_H(0) − 2τ_H′(0) + J_∞(H) + pole(H)`, `τ_H(k) = ⟨ρ_A(J_k)H, H⟩`,

with `J_k(m) = φ(m)#ℙ^{k−1}(ℤ/m)` Jordan's totient. RH is the sign of this jet on every window. Three
facts fix what kind of theory can produce that sign:

- **No slack.** The Weil cone is a point (every Weil-positive real weight is `Λ`); window margins are
  doubly exponentially small; no finite identity, finite carrier or lossy estimate survives.
- **Positivity in positive dimension is soft.** The counts are nonnegative in every positive dimension
  for `ζ` and for fakes alike (`ζ(s)ζ(s−ε)`); at a prime only the sign of the weight survives `∂_k|₀`.
- **Every route's last wall is one statement**: on the odd sector of every window, the folded arithmetic
  jump process has a positive ground state and sinh capacity at most one.

Over `𝔽_q` the passage from counts to positivity is made by the geometry of `C × C` (Castelnuovo–Severi,
Rosati positivity of Frobenius). Over `ℤ` there is no surface; what is there is a tower of windows, a
jump process on each, a reflection `σ_A`, and a family of counts in a continuous dimension `k` whose
derivative at `k = 0` is the arithmetic. DZG is the geometry of that dimension-zero point: what
positivity a family in positive dimension can carry to `k = 0`, what the archimedean place contributes
in dimension `k`, which operators can play Frobenius, and what the archimedean place alone must satisfy.

## 2. Objects

| Object | Meaning |
|---|---|
| Window, level, stage | `W_A`, `N = ⌊e^A⌋`; stage `n`: `log n ≤ A < log(n+1)` (CWS, WTZ) |
| Unified jump measure | `m = ω(t)dt + Σ_{n≥2} Λ(n)n^{−1/2}δ_{log n}` on `(0, ∞)`, `ω(t) = e^{−t/2}/(1 − e^{−2t})`: archimedean and arithmetic jumps on one footing |
| Autocorrelation | `c_H(t) = ∫H(u)H(u + t)du`; Weil's form depends on `H` only through `c_H` |
| Weil functional | `W(g) = pole(g) + arch(g) − Σ_n Λ(n)n^{−1/2}(g(log n) + g(−log n))` on even tests; `Q(H) = W(c_H)` |
| Archimedean–polar functional | `D(g) = pole(g) + arch(g)`; `D(c_H) = Ω(0)‖H‖² + J_∞(H) + pole(H)` |
| Jordan (residue-ring) Tate family | `J_k = twist_{−k}ζ * μ`, `Σ J_k(n)n^{−s} = ζ(s−k)/ζ(s)`; counts of `𝔸^k∖0` over `ℤ/m` |
| Logarithmic (finite-field) Tate family | `L_k(n) = Λ(n)(n^k − 1)/log n`, `L_k(p^a) = #(𝔸^k∖0)(𝔽_{p^a})/a`; `J_k = exp L_k` (WTZ) |
| Tate tilt | `g ↦ g·e^{kt}`: the Tate twist `f ↦ f·n^k` read on the jump measure; on windows, conjugation by `e^{kM}` |
| Twisted Weil pairing | `Q^{(k)}(H) = B(e^{kM}H, e^{−kM}H)`, `B` the bilinear Weil form |
| Archimedean Tate family | a form `A_k` built from the Gamma factor and the pole with `A_0 = 0`, `∂_kA_k|₀ = D(c_H)` |
| Dimension-`k` defect | `P_k(H) = A_k(H) − 2(τ_H(k) − ‖H‖²)`; `P_0 = 0`, `∂_kP_k|₀ = Q(H)` |
| Window algebra, Rosati involution | `ρ_A(𝒜)`, `σ_A` (WTZ); Hecke similitude: `S` with `Q(SH) = λQ(H)` |
| Finite-level Weil cone | `C_A`: weights on `{2, …, N}` making Weil's form (ζ's Gamma factor and pole) nonnegative on `W_A` |
| Prime-blind cone | `𝒦`: positive combinations of autocorrelations vanishing at every `±log n`, `n ≥ 2` |

## 3. Language

- **Dimension**: the parameter `k` of a Tate family; **dimension zero**: the jet at `k = 0`.
- **Tate piece**: value at a positive integer dimension; **non-Tate piece**: the derivative at `0`.
- **Normalizations of dimension**: *Jordan* (residue-ring counts, one-sided, multiplicative),
  *logarithmic* (finite-field counts, one-sided, additive), *symmetric* (twisted pairing, even in `k`).
  Weil's form is the derivative at `0` of the first two and the value at `0` of the third.
- **Domination at dimension `k`**: `P_k ≥ 0`. **Descent**: domination near `0` gives `Q ≥ 0`.
- **Structured** archimedean family: one that is a Tate family in its own right (a tilt or cocycle of
  the Gamma factor), not an arbitrary form with the right 1-jet.
- **Soft / selective**: true for fakes with off-line zeros / fails on them (as in WTZ, CWS).
- **Exact**: an identity, an integer, or a structural law losing nothing (the only kind no slack allows).

## 4. Mechanisms

**A. Criticality (ground states).** Positivity of a Z-type jump form is the existence of a positive
supersolution (Allegretto–Piepenbrink); the ground-state representation writes the form as a sum of
squares of jump differences of `H/φ` plus a potential: an exact identity of unbounded rank. On the
whole line no positive folded supersolution exists (ACT); on windows the question is open (2.6.1).

**B. Dimension zero (descent).** If `P_k ≥ 0` for `0 < k ≤ k₀`, dividing by `k` gives `Q ≥ 0`. The
mechanism only uses the 1-jet of `A_k`; its content lies in what structure `A_k` carries.

**C. Reflection (Weil's argument).** Rosati positivity plus a Frobenius similitude gives `|α|² = q`. On
windows the reflection `σ_A` is the Rosati involution of the window algebra and an isometry of `Q`.

**D. Prime-blind existence.** RH holds iff every finite-level Weil cone `C_A` is nonempty (compactness
plus uniqueness of the Weil cone, RHTower). The witness at each level may be any weight.

**E. Tilting (the unifying mechanism).** The Tate twist acts on the unified jump measure by exponential
tilting, `m(dt) ↦ e^{kt}m(dt)`, simultaneously on the archimedean density `ω` and on the prime atoms
`Λ(n)n^{−1/2}δ_{log n}`: it is the Esscher transform of the arithmetic jump process. On a window it is
conjugation by `e^{kM}`, the exponential Doob gauge, so dimension (B) and gauge (A) are one parameter.
The twisted pairing `B(e^{kM}H, e^{−kM}H)` is Weil's functional at `c_H·cosh(kt)`: the zero form of the
shifted pair `Λ(s−k)Λ(s+k)`, whose zeros `ρ ± k` leave the line. The archimedean place in dimension
`k` is the tilted Lévy density `ω(t)e^{kt}`, the Lévy density of `Γ_ℝ(s − k)`.

## 5. Questions the programme answers

| Question (obstacles §2.7, §2.8) | Status |
|---|---|
| Is there an archimedean Tate family dominating the counts near `k = 0`? | open; first: whether the bare existence question is already RH-complete |
| What positivity survives `∂_k` at `k = 0`; which normalization uses the archimedean data? | open |
| What is the archimedean place in dimension `k`; does it dominate near `k = 0`? | open |
| Is there a Hecke operator on windows commuting with `σ_A` and acting as a similitude of `Q`? | open |
| Does the window jump process have an Agmon ground state; its shape; how does it pass a stage? | open |
| Is there a unique-continuation principle for the window Euler–Lagrange equation? | open |
| Is the archimedean place positive on the annihilator of `log ℕ`? | open (RH, Mechanism D) |
| Over `𝔽_q(C)`, which structure supplies each answer; which has an analogue over `ℤ`? | open |

## 6. Tools

**To develop.** Jet calculus of families of quadratic forms at `k = 0` (descent, jet constraints on null
tests); tilting of jump measures and exponential Doob gauges on windows; the archimedean Tate family
from the Gamma factor (Lévy–Khintchine in dimension `k`, Gamma ratios at even dimension); similitude
calculus in the window algebra (stage valuation, short right-end tests); compactness of finite-level
cones and truncated Krein extension; ground-state representations of censored jump forms on intervals;
the function-field dictionary (Tate twist as a scalar on each Frobenius degree).

**Used from the corpus.** WTZ (window algebra, Tate function, Jordan and logarithmic families, jets,
Rosati involution); CWS (window tests, folds, canonical class, index); ACT (ground-state
representations, shifted-pair zero form, Allegretto–Piepenbrink for finite jump forms); RHTower (Weil
functional, cone uniqueness, finite-level existence, Markov form); SpacingScaleHarmonicAnalysis
(`weilQuad`, Lévy form, translation invariance).

## 7. Open research topics

1. A structured archimedean Tate family and its domination of the counts at the first-fold stage.
2. Jet constraints: what the 2-jet of any dominating family must do on near-null tests (Selberg's `Λ₂`).
3. The Frobenius problem: similitudes of `Q` outside the window algebra (dilations, reflections).
4. Ground states of the censored window process; their passage across a stage.
5. The prime-blind cone at the first levels: the archimedean–polar kernel on `(−A, A)` plus point masses
   at `±log n`, `n ≤ e^A`.
6. The function-field dictionary for each mechanism.

## 8. Pillar theorems

To be filled as theorems are formalized.

## 9. Traps

| Trap | Truth |
|---|---|
| Counts in positive dimension select `ζ` | `ζ(s)ζ(s−ε)` has nonnegative counts in every positive dimension (WTZ) |
| Positive dimension moves away from RH harmlessly | In the symmetric normalization, dimension `k` moves the zeros to `ρ ± k` (shifted pair, ACT: not positive on any window for large `k`) |
| A dominating archimedean family is a reduction of RH | Only if it carries structure; bare existence with the right 1-jet is a reformulation |
| Finite identities can produce the sign | Refuted at the first prime (CWS); no slack anywhere |

## 10. Place in the research and relation to other programmes

| Programme | Relation |
|---|---|
| WTZ (`WindowTowerOfSpecZ`) | supplies the window algebra and the Tate families; DZG studies positivity at their dimension-zero point |
| CWS (`CohomologyOfWindowsOfSpecZ`) | one window at a time: folds, canonical class, index; DZG's windows |
| AHD / ADT | the degeneration produces the Tate pieces as conductor counts; DZG asks what carries their positivity to `k = 0` |
| ACT (`ArithmeticCriticalityTheory`) | whole-line ground states, two-moment no-go, shifted pairs; DZG's Mechanism A on windows and the tilt |
| PM (Mayer / renormalized intersection) | the reflection as a Krein structure; Mechanism C |
| RHTower Weil-cone modules | uniqueness and finite-level existence; Mechanism D |

## 11. Success criteria and criteria for contributions

The programme succeeds when each question of §5 has a theorem as answer — an identity, an equivalence
labelled as such, a classification, or a no-go with its strongest positive survivor — and when the
positivity at dimension zero is either produced by a structured mechanism or shown to be out of reach
of every mechanism of a named class.

A contribution must:
1. be about the passage to dimension zero, the archimedean place in dimension `k`, the reflection, the
   ground state, or the prime-blind cone — not a re-proof of window algebra facts;
2. be exact (identity, equivalence, classification, structural inequality), not an estimate losing a
   factor growing with `A`;
3. say what it does on fakes (shifted products, flip twins, Epstein data);
4. be unconditional; RH-equivalent statements are labelled as such and count only if they move the
   problem to an object with new structure.
