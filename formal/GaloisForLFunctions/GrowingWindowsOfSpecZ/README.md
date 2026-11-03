# Growing Windows of Spec ℤ (GWZ)

Namespace `GaloisForLFunctions.GrowingWindowsOfSpecZ`; umbrella `GrowingWindowsOfSpecZ.lean`.
Every theorem is unconditional; equivalences with RH are labelled as such.

## 1. Motivation

RH is the statement that Weil's form `Q` is nonnegative on every window `W_A` (real `C²` tests
supported in `[−A, 0]`), for every length `A` (CWS `riemannHypothesis_iff_windowForm_nonneg`). The
corpus has classified what does not produce this sign:

- **No slack.** The Weil cone is a point, window margins collapse doubly exponentially, no finite
  identity, finite carrier or lossy estimate survives (RHTower, CWS, ACT).
- **No positive dimension.** Positivity of the counts in Tate dimension `k ≠ 0` does not descend to
  `k = 0`, and bare domination is Weil positivity itself (DZG).
- **No Frobenius inside a window.** The similitudes of `Q` in the window algebra are scalars (DZG);
  the reflection `σ_A` is the Rosati involution but carries no sign by itself (WTZ, CWS).
- **The new fold is a positive source.** The frozen form `Q_N` is indefinite past the first prime and
  the prime `2` repairs a negative frozen direction (WTZ
  `exists_first_stage_positive_exit_loan_failure`); every payment that treats the new fold as a
  cost fails.

What is left is a statement about **growth**: as the window length `A` increases, the form changes
only by one collar-to-collar correlation per prime power (`Q = Q_N − 2w c_H(log(N+1))`, DZG
`weilQuad_eq_stageForm_sub_corr`), and positivity must survive each of these kicks exactly. GWZ is
the exact theory of this growth: the window length is a time, each prime power is an impulse
`w_n = Λ(n)/√n` at time `log n`, the archimedean place and the pole are the free evolution, and RH is
the statement that the evolution never leaves the positive cone.

Krein–Gelfand–Levitan theory says that for a translation-invariant kernel positivity on every
interval is the global existence of a causal evolution in the interval length (a canonical system,
a continuous Schur algorithm). GWZ builds the arithmetic version of this theory in exact form:
two-collar forms instead of resolvents, prediction intervals instead of estimates, ground states and
zero modes instead of lower bounds.

## 2. Objects

| Object | Lean | Meaning |
|---|---|---|
| Window, level, stage | CWS `IsWindowTest`, `windowLevel` | tests in `[−A, 0]`; `N = ⌊e^A⌋`; stage `n`: `log n ≤ A < log(n+1)` |
| Frozen form | WTZ `stageForm N` | Weil's form with the folds `n ≤ N` only: the datum before the kick |
| Kick | `primeJumpWeight (N+1)`, `corr H ℓ` | `w = Λ(N+1)/√(N+1)` times the correlation at `ℓ = log(N+1)` |
| Collars, interior | `IsInteriorTest A ℓ h` | left collar `[−A, −ℓ]`, right collar `[ℓ − A, 0]`, interior `[−ℓ, ℓ − A]` |
| Two-collar form | `twoCollarForm N A H` | `S^N_A(H) = inf_{h interior} Q_N(H + h) ∈ [−∞, ∞)`: the frozen form seen from the collars |
| Collar reflection | `collarReflection A ℓ` | `R u = −A − ℓ − u`, the reflection of the left collar about its midpoint |
| Window involution | CWS `windowInvolution A` | `σ_A H(u) = H(−A − u)`; swaps the collars |
| Lattice tests | `latticeTest φ h y` | `Σ_k y_k φ(· + kh)`: amplitudes on the lattice `hℤ` of translates of a bump `φ` |
| Weil sequence | `weilSeq φ h m` | `κ(m) = W(φ, φ(· + mh))`: the orbit correlation of `φ` sampled on `hℤ` (AOG) |
| Toeplitz form | `toeplitzForm κ y` | `Σ_{j,k} κ(j − k)y_jy_k`, the Weil form of a lattice test |
| Prediction error, predictors | `predError κ m`, `forwardPredictor`, `backwardPredictor` | `E_m = min Q(e_0 + Σ_{1≤k≤m} y_ke_k)`; its minimizer and its mirror image |
| Schur parameter | `schurParam κ m` | `β_m = ⟨f_{m−1}, e_m⟩_Q`, `γ_m = β_m/E_{m−1}`: the corner coupling of the next lattice window |
| Zero mode | DZG `weilPair_eq_zero_of_zeroMode` | `Q(H) = 0` on a nonnegative window: a radical vector, an edge of the positive cone |

## 3. Language

- **Time** is the window length `A`; **free evolution** is the archimedean place with the pole;
  **kicks** are the prime powers, of strength `w_n` at time `log n`. Composite stages carry no kick.
- **Collar data** of a window test: its class modulo interior tests. The fold of the newest stage
  reads collar data only.
- **Frozen**: before the kick (`Q_N`); **complete**: after it (`Q`).
- **Positive source / cost**: collar data on which the kick raises / lowers `Q`.
- **Sector**: an eigenspace of `σ_A` (even, odd) intersected with an eigenspace of the collar
  reflection `R` (symmetric, antisymmetric).
- **Prediction interval** of a lattice window: the interval `[π_m − E_{m−1}, π_m + E_{m−1}]` in which
  the newest Weil datum `κ(m)` must land for the next lattice window to stay positive; `π_m` is the
  frozen prediction of `κ(m)` from `κ(0), …, κ(m−1)`.
- **Margin**: a prediction error `E_m`, or the ground energy of a window. **Soft** horizons are the
  lengths up to which a lossy bound pays the window (`≍ e^{−A/2}` after the stage); **exact**
  margins are the true ones (`≍ exp(−e^A)`).
- **First critical length**: the infimum of lengths with a nonzero test of nonpositive energy; a
  **zero mode** lives there if the window is still nonnegative.
- **Soft / selective**: true for data with off-line zeros (flip twins, `ζ(s)ζ(s−ε)`, Epstein,
  golden curve) / false on them.

## 4. Mechanisms

**A. Criticality.** A positive supersolution of the window jump operator gives Weil positivity by
the ground-state representation (Allegretto–Piepenbrink), an exact sum of squares of unbounded rank.
Crossing a stage changes the representation by a correction on the two collars only (DZG
`weilQuad_eq_groundState`). Mechanism A asks for a ground state at every length that passes every
stage by collar corrections.

**B. Causal evolution.** The window form at length `A` is determined by the form just before `A`
and the kick at `A`. On collar data this is the **kick law**: the infimum over interior
perturbations commutes with the kick, because the kick reads only collar data, so
`inf_h Q(H + h) = S^N_A(H) − 2w c_H(log(N+1))`. Positivity of the window is the **stage criterion**
`2w c_H ≤ S^N_A(H)` on every collar class. On the lattice `hℤ` the two-collar form is a `2×2` matrix
`[[E, β], [β, E]]` (equal diagonal by the reflection), the stage criterion is `|β| ≤ E`, and the
evolution is the Schur–Levinson recursion `E_m = E_{m−1} − β_m²/E_{m−1}`: an exact discrete
canonical system whose parameters are kicked by the primes.

**C. Reflection.** `σ_A` is an isometry of the window form that commutes with the interior, the
frozen form and the kick. It splits the stage criterion into an even and an odd one-collar problem.
On even tests the kick is the collar reflection form, `c_H(ℓ) = ⟨h, Rh⟩_{L²(L)}`; on odd tests it is
its negative. The kick is a positive source exactly on the even-antisymmetric and the
odd-symmetric sectors.

**D. Prime-blind existence.** The frozen form at a stage is prime-blind beyond `N`; the stage
criterion is a Farkas-type statement for the newest weight alone (RHTower finite-level cones).

**E. Angles.** The lattice `hℤ` folds frequencies modulo `2π/h`. A degenerate lattice window has a
one-dimensional, palindromic radical whose symbol vanishes on finitely many angles: a degenerate
window looks like the window of a curve over a finite field (CWS curve windows).

## 5. Questions the programme answers

| Question (review-0311 §2.7) | Form of the answer |
|---|---|
| What is the two-collar form of a stage, and what law carries it across a prime kick (2.5.1)? | The infimum of the frozen form over interior perturbations; the kick subtracts `2w c_H(ℓ)` from it exactly; positivity of the window is the stage criterion on collar classes; on the lattice, a `2×2` matrix with the Schur–Levinson law |
| Does the window jump process have a positive ground state at every length, and how does it pass a stage (2.6.1)? | Lattice: the predictors are the ground states of the corner problem and pass each stage by the Levinson step. Continuum: by collar corrections in any gauge (DZG); existence at every length is RH |
| Is there a unique-continuation principle that forbids a zero mode with full mass on both collars? | Structure of zero modes at a first critical length: reflection parity, one-dimensionality and both-corner support on the lattice; the continuum UCP is open |
| Which positive involution on two-collar data makes `σ_A` a Rosati positivity? | The collar reflection `R`: the kick is `∓⟨h, Rh⟩` on the two `σ_A`-sectors |
| What is the `ℤ`-analogue of the trivial Frobenius angle (2.6.4)? | Lattice reading: angles are frequencies modulo `2π/h`; degenerate windows are curve windows |
| How do the soft horizons `≍ e^{−A/2}` become the exact doubly exponential margins? | Margins are products `E_m = E_0∏(1 − γ_k²)`: exact collapse is the accumulation of the Schur parameters at `±1` |

## 6. Tools

**To develop.**
- Two-collar calculus on Weil's form: interior tests, collar locality of the kick, two-collar form,
  kick law, stage criterion, reflection splitting, collar reflection.
- Schur complements without inverses: the variational corner reduction for a symmetric bilinear
  form that is positive definite on an interior subspace, with an involution swapping two corners.
- Lattice canonical systems: Toeplitz forms of translates, predictors, prediction errors, Schur
  parameters, the Levinson recursion, kick law, locality in the primes.
- Degeneration calculus: kernels at a first critical lattice length, parity of zero modes.

**Used from the corpus.** CWS (window tests, level, window criterion, window involution); WTZ
(stage form, transfer across a stage, first-fold failure of the collar loan); DZG (stage identity,
correlation on the left collar, gauge representation, zero modes); ACS (Weil pairing, bilinearity,
`realTests`); AOG (orbit correlations, orbit Hodge index); HKT (negative index on groups); HWV
(`weilQuad_pos_of_riemannHypothesis`).

## 7. Open research topics

1. **The continuum two-collar form at the first prime** (A8): the infimum of the prime-free
   archimedean form over interior perturbations, as an operator on `L²(L) ⊕ L²(R)`.
2. **Ground states at every length** (2.6.1), stage-uniform.
3. **Unique continuation** for the window Euler–Lagrange equation.
4. **The continuum limit** `h → 0` of the lattice canonical system (Krein's continuous Schur
   algorithm with atoms at `log n`).
5. **Exact margins**: the rate at which the Schur parameters of Spec ℤ accumulate at `±1`.

## 8. Pillar theorems

To be filled as the theory is formalized.

## 9. Traps

| Trap | Truth |
|---|---|
| The new fold is a cost to be paid by the frozen form | It is a positive source on two of the four sectors; the frozen form is negative on tests the complete form keeps positive (WTZ) |
| The two-collar form needs resolvents | It is an infimum over interior perturbations; the kick commutes with the infimum |
| A finite lattice can decide RH | Each lattice window is one slice; RH is every lattice window of every bump at every step |
| A canonical-system formulation removes the wall | It changes the toolset, not the wall: the evolution passes doubly exponentially close to the boundary of the cone |

## 10. Place in the research and relation to other programmes

| Programme | Relation |
|---|---|
| WTZ (`WindowTowerOfSpecZ`) | window algebra, stages, transfer across a stage; GWZ studies how positivity passes the stages |
| DZG (`DimensionZeroGeometryOfSpecZ`) | the dimension-zero chapter of the same theory (negative); stage identity in every gauge; zero modes |
| CWS (`CohomologyOfWindowsOfSpecZ`) | one window at a time; window criterion; curve windows |
| ACT (`ArithmeticCriticalityTheory`) | whole-line ground states and Doob transforms; GWZ works on windows and stages |
| AOG, HKT | orbit correlations and their Toeplitz/Krein–Langer index theory; GWZ adds the causal (Schur) evolution |
| SZ (RHTower `Suzuki`) | screw functions and Krein–Schur blocks; the nearest carrier of the continuum canonical system |

## 11. Success criteria and criteria for contributions

The programme succeeds when each question of §5 has a theorem as answer — an identity, a labelled
equivalence, a classification, or a no-go with its strongest positive survivor — and the stage step
is reduced to an exact statement about collar data alone.

A contribution must:
1. concern the passage of positivity through the growth of the window (two-collar forms, kicks,
   canonical systems, ground states, zero modes, margins), not re-prove single-window facts;
2. be exact: an identity, an equivalence, a classification, a rigidity law, never an estimate that
   loses a factor;
3. be local and causal: state which primes and which lengths it reads;
4. say what it does on fakes and on curves over `𝔽_q`;
5. be unconditional; RH-equivalent statements are labelled and count only when they move the
   problem to an object with new structure.

## 12. Big picture

To be written once the pillars are in place.
