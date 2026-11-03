# Review 0311 — consolidated report and big-picture interpretation

Companion to `obstacles-summary.md` (§2.4–2.8 answer the same seven questions from the P1 side),
`route-obstacles.md` (labels `A*`, `B*`, classes P1–P4), `walls-ledger.md` (Σ/Π/Γ),
`route-unification-ledger.md`, `rh-current-frontier-map.md`, `rh-killed-routes.md`, and the
programme READMEs under `formal/GaloisForLFunctions/*/README.md`. Evidence tags: `[L]` a Lean
theorem whose statement was read in source or returned by the corpus search; `[D]` derived here from
`[L]` statements; `[C]` a proposal or conjecture of this report; `[N]` numerical. Windows of length
`A` are real `C²` tests supported in `[−A, 0]`; `Q` is Weil's form; `c_φ(t) = W(φ, φ(· − t))` is the
orbit correlation; `κ` is the number of distinct zeros right of the line.

---

## 1. The programme in one picture

### 1.1 One invariant, one equation

Everything the corpus has proved about RH is a reading of one even integer `κ = κ(K_ζ)` and one
inequality.

The integer. `κ` is read, exactly, as: the negative index of Weil's form on windows (`ι(A)`,
CWS: RH ⇔ `ι(A) < 2` ⇔ `ι(A) = 0` ∀A) `[L]`; the negative index of the orbit kernel `K_ζ` on
`ℚ_{>0}^×` (HKT; finite ⇔ Lindelöf-deep, decided on any two-prime lattice) `[L]`; the index of the
glued archimedean and `p`-adic states, `κ + 1` at every place (AKG) `[L]`; the window index of the
pencil of the complete family at the critical curve (AHD: some family has index `≥ n` iff `ζ` has
`≥ n` right zeros) `[L]`; the collision charge of the reflection configuration (HEF: RH ⇔ `O < 2`)
`[L]`; the Fredholm index of the Wiener–Hopf lift (WD) `[L]`.

The inequality. RH ⇔ for every nonzero bump `φ` and every `t ≠ 0`,
`|c_φ(t)| < Q(φ)` (GWZ `riemannHypothesis_iff_abs_weilOrbitCorr_lt`) `[L]`, and with CSTW's ordered
coupling the orbit correlation is explicit `[L/D]`:

`c_ψ(t) = A(ψ)B(ψ) e^{t/2} − Σ_{k≥1} μ_{−2k}(ψ) ν_{−2k}(ψ) e^{−(2k+½)t} − Σ_n Λ(n) n^{−1/2} (ψ⋆ψ)(t − log n)`.

The first two terms are the trivial divisor of `ζ` (pole `+`, trivial zeros `−`) read through the
exponential moments of `ψ`; the last is the `ψ⋆ψ`-smoothed Chebyshev count near `e^t`. So the
inequality says: the smoothed prime count matches its main term `AB e^{t/2}` to within the fixed
constant `Q(ψ)`, for every `t`. This is the classical statement `ψ(x) − x = O(√x · polylog)` in its
sharp-constant form. In the ledger's words: Σ on two sites is Π at one point.

### 1.2 What is established, by what it says about a mechanism

| Theme | Status quo `[L]` unless marked | Consequence for a proof |
|---|---|---|
| Two sites decide | RH ⇔ every two-site lattice window PD; off RH a short generic bump has an exactly degenerate two-site lattice (GWZ) | Interiors, stages, collars are proof *mechanisms*, not needed to *decide* |
| Growth of a window | `Q = Q_N − 2w c_H(ℓ)` per prime power; the kick reads collar data only; kick = collar Rosati form `∫_L H·(σ_AH)∘R`, a positive source on even–`R`-antisymmetric and odd–`R`-symmetric data; frozen-negative tests are forced into those sectors (GWZ) | The sign of the stage step lives on two of four sectors; the frozen form must pay on the other two |
| Transmission | Across a cut the archimedean place and pole couple ordered tests only through moments at the trivial divisor, kernel `κ(x) = e^{x/2} − Σ_k e^{−(2k+½)x}`; frozen two-collar form in closed form at stages 1, 2; window growth ⇔ translation contraction; RH ⇔ every growth step contracts (CSTW) | The first-stage problem is a problem about two moment sequences at the trivial divisor and one `L²` overlap at lag `log 2` |
| Lattice canonical system | Weil sequences are Toeplitz; Schur–Levinson evolution exact and causal in the primes; one prime kick moves one Schur parameter; only `Λ` survives all lattices; degenerate window = finite curve (Carathéodory–Fejér); under RH Szegő-singular (margins → 0, `Σγ_k² = ∞`); continuum limit is a jet system, no unnormalized continuum canonical system (GWZ) | No slack anywhere; the extremal object is critical, not subcritical; the prime kicks must land in prediction intervals that collapse |
| Dimension zero | Weil's window form = `d/dk|₀` of the Tate function `τ_H(k) = ⟨ρ_A(J_k)H,H⟩` whose integer values are counts `φ(m)#ℙ^{k−1}(ℤ/m)`; jets at `0` are Bombieri's `Λ_j`; `k ↦ −k` is Dirichlet inversion carrying the parity `(−1)^{ω(n)}`; Tate positivity in every real dimension holds for the fake `ζ(s)ζ(s−ε)` and does not descend (WTZ, DZG); no archimedean family dominates the counts across the tower, every pole weight is pinched to `1/ζ(1+k) < k`, window-local domination is Weil positivity itself (ATD) | Counts in positive dimension are blind; the sign is a first-order jet, hence parity-sensitive; the count/Hodge/domination mechanism is closed |
| Complete family at the critical curve | First order = count `J(1)·#ℙ⁷(ℤ/m)`; second order on horizon windows = pencil `κQ(H) + (7J(1)/K)‖H‖²_{−8}` exactly; twisted sectors (conductors, characters, frequencies) are zero-blind counts/Hurwitz forms; conductor decomposition block-diagonal; zeros enter fixed packets only through the pole with positive weight; count form ends at the resolution `m ≍ c`; window index resolves the right zeros of its length and is capped by the Shannon number (AHD) | Everything below the sign is size-only; `Q(H)` stands exactly at the pole `u = 0` of the frequency count; positivity at one multiple is sub-RH, at every multiple is RH |
| Base positivity | All `C²` tests of support length `≤ 181/250`; strict floor `1/8000` on windows up to `2·enlargedWeilFloorAperture`, an explicit length in `(181/250, 1)` past `log 2` (ATD); windows `≤ 1/7` by exit charge alone; odd unit window: `Q + (3203/320)(∫xF)² ≥ ‖F‖²/1000`, i.e. positive off one first-moment direction; the retained Gamma lower form has a negative direction while the complete form is positive (WTZ) | The first prime acts as a positive source; the Gamma remainder cannot be discarded; the open base case is one scalar charge |
| Whole space | `completeWeilMatrix tiltedUnitSpline c N` PD for `1 ≤ c ≤ (log N)^α`, `α < 1/8`; at the critical curve `c ≤ 2K(log N)^{1/8}` the far complement of the conductor subspace (conductors `≤ N^θ`, `θ ≥ (1 + log log N)^{−5}`) is coercive with its weighted collar (CACT); conductor Gram PSD at every `2K(log N)^{1/8}` is RH (HWV) | The eighth-root endpoint at one small multiple is an assembly away (card in progress, §B); the growing-conductor block at the critical curve is where RH sits |
| PM | `Q(H) = 2 Re[𝓦H, 𝓦H]` exactly on `ℓ²(upper Mayer resonances)`; `T_p − Id` is the Mellin translation for every prime; `D_p` a Krein similitude of factor `p`; Lewis co-isometry defect `≤ 0`, `= 0` iff `Re s = ¼`; bounded Cauchy reflection only for `Re s ≥ ¼`; physical cusp energy has Krein form as its linear term, counterterms carry no sign; window Serre duality is *not* the linear Krein reflection (the identification is antiunitary with an exponential twist) (RIT) | PM is the zero side in Krein coordinates; the reflection carries no sign of its own |
| Selection | Weil cone `{Λ}`; lattice selection; FE + positive measure ⇒ counting measure of `ℕ` (APD); degree gap `(0,1)` empty, strong multiplicity one at the critical Euler abscissa for arbitrary Gamma data, finite-prime rigidity (SEL); positive multiplicative twins `ζ(s)(1 + Ap^{−s} + p^{1−2s})` with FE, Euler product, Ramanujan bounds and a zero at any `Re s ∈ (½, 1)` — excluded only by the strict square-root Euler bound (SEL) | Selection is automatic after positivity; a proof must use the FE and the Euler product with the Selberg Euler bound `θ < ½`, nothing weaker |
| Gauge | Möbius exponent `½` Haar-a.e., `1` Baire-generically; RH ⇔ the trivial point is typical; the prime source is atypical exactly by the pole (AGT, ACG) | Neither measure nor category reaches the trivial point; only the pole distinguishes it |
| Density (WD) | 8-way unconditional equivalence of critical-line log-mean, mollifiers, off-line moments, 100% critical-scale clustering, dyadic Hecke defect; `D_win` ⇔ thin Planck shadows; almost-all Bessel–Szegő certificates at the double-log stage; countermodels exclude volume and moment inputs (CDG) | WD's single analytic input is one double-logarithm short; it is a density statement, sub-RH |

### 1.3 The three walls are one wall: where the sign hides

Σ (sign), Π (precision) and Γ (selection/reflection) are the same obstruction in three coordinate
systems. The sign of RH is confined, in every programme, to the *trivial direction* of a structure
whose non-trivial directions are manifestly positive:

- the derivative at Tate dimension `k = 0` (positive counts at `k > 0`) `[L]`;
- the pole `u = 0` of the frequency count (Hurwitz forms at `u ≠ 0`) `[L]`;
- conductor one in the block-diagonal second order (counts at `m ≥ 2`) `[L]`;
- the pole coordinate of the bulk (pole-free packets are blind) `[L]`;
- the trivial gauge point (Haar-a.e. exponent `½`) `[L]`;
- the one scattering channel surviving at each Mayer resonance (the zeta-axis channel vanishes) `[L]`;
- the one negative square of the glued state, the hyperbolic pair `e^{±h/2}` on lattices `[L]`;
- the first-moment direction of the odd unit window `[L]`.

The reason is structural and is itself a theorem of the corpus in several forms: the Euler product
enters the zero side only through the pole (LST: "the Euler product returns only through boost
equivariance"; AHD: twisted windows see no point of the strip; ACoT: the jump energy equals the pole
defect) `[L]`. All non-trivial twists are Hurwitz–Lerch objects without Euler product. Hence any
mechanism must couple the functional equation (which fixes the trivial divisor and the reflection)
with the Euler product (which fixes the folds) at the pole, and the corpus has proved that neither
alone selects `ζ` (APD, SEL) `[L]`.

A second structural fact is that the obstruction is additive–multiplicative. The window algebra is
purely multiplicative (the Dirichlet ring truncated at `e^A`; Hecke similitudes are scalars; the
reflection lies outside it) `[L]`; the pole and the successor `n ↦ n + 1` are additive; every
successor pair lies in the top coprime stratum, which is the open core of the Kähler package
(HWV, ADT) `[L]`; and a positive-definite kernel on the affine group with an integer successor and a
continuous dilation has infinite index (AKG) `[L]`. The sign is the coupling of the multiplicative
structure to the additive one through the archimedean place — a sum–product phenomenon.

### 1.4 The four live classes

| Class | Content | State |
|---|---|---|
| P1 signed criticality | a signed certificate of unbounded rank at every stage, using the sign of each fold | the raw folded supersolution is excluded for every nonnegative compact profile by the origin charge (ACT `compact_positive_profile_origin_failure`) `[L]`; the odd unit window is one first-moment charge from closed `[L]`; strict base floor past `log 2` `[L]` |
| P2 prime-blind positivity | archimedean + pole `≥ 0` on nonnegative combinations of autocorrelations vanishing on `±log ℕ_{≥2}` | unchanged: RH ⇔ `PrimeBlindPositive` `[L]`; on blind tests it is the zero sum `[D]` |
| P3 PM reflection | Krein positivity on the completed resonant space | exact identity, Hecke for every prime, antiunitary reflection; reduced to the zero side `[L]` |
| P4 square-root cancellation | one smoothed prime sum at sharp constant | first cyclotomic band ⇔ RH exactly (CAF) `[L]`; parity barrier at damping `½` `[L]` |

### 1.5 A unification: the gauge torus is the dual of the orbit group

The orbit kernel `K_ζ(n/m) = W(φ(· − log n), φ(· − log m))` is a Hermitian function on the discrete
group `ℚ_{>0}^×` (HKT) `[L]`. Its dual group is the compact torus `∏_p S¹` of unimodular completely
multiplicative functions, which is AGT's gauge torus `[D]`. Under RH the kernel is positive definite
and, by Bochner, its spectral measure on the torus is `Σ_ρ m_ρ|φ̂(γ_ρ)|² δ_{χ_ρ}` with
`χ_ρ(n) = n^{iγ_ρ}`: it is supported on the Tate line `{n ↦ n^{it}}`, the orbit of the trivial point
under the Tate flow, at the zero ordinates `[D]`. Off RH, `κ` characters leave the torus
(Krein–Langer). The Tate line is dense in the torus (Kronecker, since the `log p` are
`ℚ`-independent), and the Tate flow is uniquely ergodic on it; therefore every *continuous*
functional of a gauge point has its Haar-typical value on average along the Tate line. This is
exactly the mean-value theorem for Dirichlet polynomials (the Tate-line average of
`|Σ_{n≤N} μ(n)n^{it}|²` is the Haar integral `Σ μ(n)² ≍ N`), and it is why "random multiplicative
functions" and "Montgomery–Vaughan mean values" are one theorem. The exponent is a `limsup`, not a
continuous functional, and the Baire-generic value is `1` `[L]`; RH is the value `½` at the one
point `0` whose only distinguishing feature on the torus is the pole `[L: AGT]`. So MC, AGT, HKT,
AKG are one object seen from the group, its dual, and its spectral measure; none of them has a tool
for the single point.

### 1.6 Route states

- **PM.** Everything structural is exact: completed Krein space, Hecke multipliers `p^{1−2s}` for
  every prime, Eisenstein and Barnes periods as Hecke eigenfunctions, Hecke cones tiling the quadrant,
  closed Cauchy reflection with cores on any source interval, physical admission detecting
  resonances, Gaussian synthesis recovering the complete Weil form `[L]`. Negative structural facts:
  Serre duality is not the linear Krein reflection; the finite-energy core is not a Hecke
  eigenvector with the completed eigenvalue (one boundary channel is essential); no bounded
  reflection across the strip; counterterms carry no sign `[L]`. PM owns no sign.
- **MC.** Half-power and Redheffer criteria, gauge exponents, near-frequency bands retain `2Θ` `[L]`;
  the open item is actual cancellation at the trivial point. Class P4 with the gauge-torus wall of
  §1.5.
- **WD.** Eight equivalent readings of critical-scale clustering; `D_win ⇔ D_zero` up to a cluster
  tail; certificates at the double-log stage; inner caps `σ_m = 1 − 1/(116 log(m+5))`; right
  half-port rigidity on Burnol windows `[L]`. Open: `D_win` at fixed depth (one double-log short) and
  inner-cap cancellation (RH at all degrees).
- **HF.** Subcritical PD below `1/8`; critical-curve far complement coercive with its weighted
  collar; twisted sectors inherit; short windows and the cosh hyperplane inherit; count form ends at
  the resolution `[L]`. Open: the conductor block at the critical curve for one small multiple
  (card in progress) and, for RH, the continuation in `K`.

### 1.7 The shape any proof must have `[D]`

1. It is an inequality `2w_n c_H(log n) ≤ S^{n−1}_A(H)` holding at every prime-power stage, or an
   equivalent statement about all stages at once; stages are not independent (margins collapse).
2. Its input is the functional equation (trivial divisor, reflection) and the Euler product with the
   strict Euler bound; its output must fail for the positive Euler twins, flip twins, shifted
   products, Epstein data and the golden fake.
3. It is not a count, not a Markov or sign-blind ground state, not a fixed-rank identity, not a
   twisted-sector statement, not a bounded operator identity on the PM side.
4. It is critical: under RH the extremal objects (lattice margins, the window index at the critical
   curve) sit at zero with no slack. A proof is a Liouville theorem: bounded ⇒ constant, for an
   explicit convex functional along the dilation flow (the collided form `D` of APol has second
   difference `Σ m_ρ(2cosh(2(Re ρ − ½)L) − 2)|tr f(ρ)|² ≥ 0` along translation `[L]`, so RH ⇔ `D`
   bounded along the flow ⇔ `D` constant ⇔ Hecke invariance).

---

## 2. Q1 — A new proof mechanism

### 2.1 What a mechanism may still be

By §1.2–1.4 a new mechanism must produce the stage inequality on the two collar sectors where the
kick is a cost (even–`R`-symmetric and odd–`R`-antisymmetric data), using the sign structure of the
folds, without an estimate that loses a factor. Two proposals follow; the first refines P1 into a
form that uses only theorems the corpus already has, the second is a different object.

### 2.2 Proposal A — Rosati forcing by induction on stages `[C]`

Induction hypothesis: `Q ≥ 0` on `W_A` for `A < log(N+1)` (true at the base `[L]`). Stage `N+1`:
by GWZ, on a nonnegative window every frozen-negative even test is forced `R`-antisymmetric on the
collars and every frozen-negative odd test is forced `R`-symmetric `[L]`, and on exactly those
sectors the kick is a positive source `[L]`. So the only data that can fail the stage are
frozen-*nonnegative* tests on the cost sectors. On the cost sectors the collars are reflections of
each other, `x_R = ±(x_L∘R)`, and the frozen two-collar form of CSTW specializes `[D]`:

`F = Q(x_L) + Q(x_R) + Q(y) + 2⟨μ(x_L), ν(y)⟩ + 2⟨μ(y), ν(x_R)⟩ ± 2( e^{−(A+ℓ)/2} μ_1(x_L)² − Σ_{k≥1} e^{(2k+½)(A+ℓ)} μ_{−2k}(x_L)² ) − 2Σ_{m<N+1} w_m(⟨x_L, τ_m y⟩ + ⟨y, τ_m x_R⟩)`,

where the collar–collar coupling has become a weighted Hankel form on the moment sequence of one collar (`ν_s(x_L∘R) = e^{−(s−½)(A+ℓ)} μ_s(x_L)` `[D]`):
one positive square at the pole, infinitely many negative squares at the trivial zeros (this is the
Gamma symbol's indefiniteness, Weyl law `ι_Γ(A) ≈ 2A` `[N]`). The mechanism is therefore: on the
cost sectors, *the pieces' own forms `Q(x_L) + Q(x_R) + Q(y)` (nonnegative by induction) plus the pole
square pay the trivial-zero squares, the earlier-fold transports and the new fold* — a coercivity of
the frozen form restricted to a sector, not a global signed supersolution.

Why it is not excluded. It is not Markov (the sector restriction uses the sign of `σ_A` and `R`);
not a count; not finite rank (the moment sequence is infinite); the induction supplies positivity of
the pieces rather than requiring a global profile `ω`, so the origin-charge no-go for folded
supersolutions does not apply. What it must prove at stage one is exactly the odd unit window
(§7), where the cost sector is odd–antisymmetric and the single charge is the first moment `[L]`.

Risk. Sector coercivity at stage `n` must hold with margin `≥ 2w_n` on collar `L²` mass; under RH
all margins collapse along lattices `[L]`, so the induction cannot carry a uniform margin — it must
carry an exact identity per stage (the Carathéodory disk `[L]`) with the kick landing inside.

### 2.3 Proposal B — the Nevanlinna reading of the tower `[C]`

RH ⇔ `Re(ξ'/ξ)(s) > 0` for `Re s > ½` (Lagarias). This is Weil positivity on the two-parameter
family of one-sided exponential tests, and it collapses the whole tower into one Herglotz function
`F = ξ'/ξ`. The window theory is the moment problem of `F`; the lattice Schur–Levinson evolution is
its Schur algorithm `[L]`; the two-site criterion is the `2×2` Pick matrix of `F` at two points. The
new element is to use the Herglotz class, not the forms: a Herglotz function on a half-plane has a
Riesz–Herglotz measure, and `F` has an explicit Hadamard factorization. The mechanism would show
that the measure of `F` restricted to the *prime side* (the Dirichlet series `−ζ'/ζ`, convergent
only for `Re s > 1`) continues as a positive measure by a *subordination* argument: `−ζ'/ζ` is
Herglotz on `Re s > 1` (positive Dirichlet coefficients), and the question is whether composition
with the functional equation keeps the Herglotz property down to `Re s > ½`. This is the Γ wall
(band holomorphy `B31`) in function-theoretic form, and it is where the Laguerre–Pólya no-go
(`B12`) lives; it is listed here because it is the only formulation where the entire tower is one
object and classical operator theory (de Branges, Krein strings) applies, and because the corpus's
B41 (continuum canonical system) is its unsolved piece.

### 2.4 Assessment

Proposal A is the recommended mechanism: it is P1 with the sector structure made the inductive
invariant, it has its base case stated, and its first obstruction is the odd unit window. Proposal B
is a change of object rather than of mechanism; it should be used to import de Branges/Krein string
theory into B41, not as a route by itself.

---

## 3. Q2 — A wildly different approach

The corpus has *proved* that the space of approaches is small: every reformulation reads `κ`;
two sites decide; selection is automatic after positivity; FE and Euler product are both needed and
the Euler bound `θ < ½` is the selecting axiom; positive dimension, counts, Markov, finite rank,
twisted sectors and PM reflection carry no sign `[L]`. "Wildly different" therefore cannot mean
"avoiding Σ"; it can only mean meeting Σ in a form with different inputs.

Two such forms exist.

1. **Prime-blind existence (P2).** RH ⇔ the Gamma factor and the pole are nonnegative on the cone
   of nonnegative combinations of autocorrelations vanishing on `±log ℕ_{≥2}` `[L]`. No von Mangoldt
   value is estimated; the integers enter only as a zero set. On blind tests the functional is the
   zero sum `[D]`, so the problem is zero-side positivity on the blind cone, and finite levels have
   near-null spaces of dimension `≍ e^{2A}` against `≍ e^A` constraints `[D]`. This is the route
   named in `obstacles-summary.md §2.4`, and it remains the one route far from the others.

2. **Spectral measure on the gauge torus (§1.5).** RH ⇔ the spectral measure of the orbit kernel
   `K_ζ` on the gauge torus has no mass off the torus `[D]`. The inputs are harmonic analysis on the
   compact group `∏_p S¹`, the unique ergodicity of the Tate flow, and the pole as the only
   non-invariant datum. What is provable (Haar-a.e. half-power law, mean values along the Tate
   line) is exactly what is classical; the trivial point is reached only through the pole. This
   approach does not touch Σ in its window form, but it meets Γ at the trivial gauge point (`B32`).

A third, honestly assessed: the function-theoretic approach of §2.3 (Herglotz class, de Branges
spaces). It avoids windows and lattices entirely, but its wall is `B12`/`B31`, i.e. Γ.

Verdict: P2 remains the wildly different route; the gauge-torus reading is the right place to
understand why probabilistic and mean-value methods cannot cross, and should be recorded as a
unification rather than pursued as a route.

---

## 4. Q3 — Breakthrough questions less hard than RH or quasi-RH

### 4.1 Whole programme — the first prime stage as a moment inequality

Question. For `A ∈ [2·enlargedWeilFloorAperture, log 3)`, prove the stage-one criterion
`2w₂ c_H(log 2) ≤ S^1_A(H)` on every collar class, using CSTW's closed form: with the two-collar
complement `Φ_ε(μ(x_L), ν(x_R))` a function of the two moment sequences at the trivial divisor, prove

`Q(x_L) + Q(x_R) + 2⟨μ(x_L), ν(x_R)⟩ + Φ_ε(μ(x_L), ν(x_R)) ≥ 2w₂ ∫ x_L(u) x_R(u + log 2) du`.

Why it is below RH. One window, one prime, explicit kernel; the inequality compares an `L²` overlap
at one lag with a Hankel pairing of Laplace moments at `s = 1, −2, −4, …` plus the coercive forms
of two short pieces (`Q ≥ (1/8000)‖·‖²` on the pieces `[L]`).

Why it is a real advance. It is the first positivity in which a prime enters with its sign and the
trivial zeros enter as an infinite moment system; it is the template of every later stage (CSTW
stage two adds only the `T₂` transports `[L]`); and its odd sector is the one scalar charge of the
odd unit window (§7).

Status quo. Proved for `A ≤ 181/250` by the frozen form alone `[L]`; strict floor on windows up to
`2·enlargedWeilFloorAperture` `[L]`; above that the frozen form is indefinite and the kick is needed
`[L]`; no finite count identity exists at this stage `[L]`.

### 4.2 Route PM — the sign of one boundary channel

Question. At every upper Mayer resonance the raw Hecke image of the core leaves whole-Haar `L²`
and exactly one boundary coefficient restores it; the corrected transport has the completed
eigenvalue and the zeta-axis channel vanishes, leaving one scattering correction per prime `[L]`.
Prove that the *sign* of this scattering coefficient, as a function of the resonance, is
determined by `Re s − ¼` — i.e. that the co-isometry defect `D_s ≤ 0` (`= 0` iff `Re s = ¼` `[L]`)
is read off the retained boundary channel of `T_2` alone.

Why below RH. It is a statement about one explicit coefficient of one explicit function at each
resonance, not about all resonances at once; it is PNT-strength in content (the previous
reviewer's zero-free-region question is its consequence for resonances near `Re s = ½`).

Why an advance. It would be the first sign statement PM owns; every other PM item is an identity
or a blind positivity `[L]`. Risk: the eigenvalue `1 + p^{1−2s}` is the Euler factor, so the sign
may reduce to the classical argument.

### 4.3 Route MC — square-root cancellation at one non-trivial, non-arithmetic gauge point

Question. Exhibit one explicit gauge point `x ≠ 0` (a completely multiplicative unimodular function
with explicitly described values), not a Dirichlet character and not a Tate translate `n^{it}`, at
which the Möbius gauge sum has exponent `½` unconditionally.

Why below RH. The Haar-a.e. statement is proved `[L]`; the question asks to replace "almost every"
by "this one", for a point with no pole and no functional equation.

Why an advance. The corpus's only explicit points fail the half-power law (the Liouville twist `[L]`, whose
sum is the squarefree count `[D]`) or are RH-equivalent (the trivial point). A single explicit point with
exponent `½` would show that the half-power law can be reached deterministically without the pole;
the mechanism for it (a structured point whose Euler product has no continuation but whose
partial sums cancel) is what MC lacks. If no such point exists, that is a theorem about the torus
worth having.

### 4.4 Route WD — `D_win` at fixed depth

Question. For every `A > 0`, the number of unit windows `[t, t+1] ⊂ [V, 2V]` containing a zero of
depth `≥ A/log V` is `≤ ε(A) V` with `ε(A) → 0`; equivalently thin Planck shadows occupy `o_A(V)`
unit windows `[L: equivalence]`.

Status quo. Proved at depth `(2/r) log log V + u` (almost-all Bessel–Szegő certificates at the
double-logarithmic stage) `[L]`; the clustered and sparse-uniform countermodels show volume and
moment bounds cannot supply it `[L]`.

Why an advance. It is WD's one analytic input at the log stage; it is a density statement
(sub-RH), exactly one double logarithm short.

### 4.5 Route HF — positivity at one small critical multiple, then the first jump multiple

Question (a). Close the card "the complete Weil family is positive at a critical multiple":
`completeWeilMatrix tiltedUnitSpline c N` PD for `1 ≤ c ≤ 2K₁(log N)^{1/8}` for one `K₁ > 0`.

Status quo. The far complement of the conductor subspace is coercive at the critical curve with
its weighted collar, the low packet through `Q₁ = (log N)^{13/32}` is coercive, the Schur payment
and the deep-row pairing are in Lean `[L]`; the assembly (conductor block against complement,
terminal prefix leakage) is the open gate.

Question (b), the structural one. On a window family with `Q(H) < 0` for some `H`, the pencil
index jumps at `K*(H) = 7J(1)‖H‖²_{−8}/(κ|Q(H)|)` `[L]`. Compute the first jump multiple
`K_1 = inf_H K*(H)` over all horizon windows of a given length `A` as a function of `A`, and prove
it is attained on a two-site window (by GWZ two sites decide). Under RH `K_1 = ∞`; unconditionally
`K_1 ≥ K₀ = βJ/(κC(β+1))` `[L]`. A lower bound `K_1(A) ≥ K₀(A)` growing with `A` is sub-RH and would
be the first HF statement with sign content beyond the size-only floor.

---

## 5. Q4 — Breakthrough questions that open the path to RH

### 5.1 Whole programme — the sector-coercive stage theorem

For every prime power `n` and every collar width `ε < log((n+1)/n)`, prove: on the two cost
sectors, the frozen two-collar form `S^{n−1}_{log n + ε}` dominates `2w_n c_H(log n)`, with the
pieces' forms taken from the previous window. By GWZ's sector theorem this is Weil positivity at
stage `n` given positivity below it `[L]`, hence RH by induction. It opens the path because it is
local in the stage, exact (an identity plus one inequality on an explicit Hankel form), and has
its base case at the first prime (§4.1). Its risk is §2.2's: margins collapse, so the inequality
must be proved as an exact disk condition (`stage_nonneg_iff_disk` `[L]`), not with a uniform
constant.

### 5.2 Route PM — finite cusp energy forces zero defect

`∫_1^∞ |ψ(2a) − 2^{1−2s}ψ(a)|² da/a < ∞ ⇒ D_s(ψ) = 0` for Lewis periods. Finite cusp energy ⇔
resonance and `D_s = 0` ⇔ `Re s = ¼` `[L]`, so this is RH as an implication between two explicit
quadratic functionals of one function. As in `obstacles-summary.md §2.6.2`. The physical cusp energy's linear term *is* the Krein
form and the counterterms carry no sign `[L]`, so the implication cannot come from the energy's
own structure.

### 5.3 Route WD — inner-cap cancellation at every polynomial stage

On every Burnol unit window cancel the right-port flux through the inner caps `[½, σ_m]` by a
source identity; across all degrees it is RH, at fixed degree a Lindelöf corridor `[L]`. The right
half-port rigidity (six-way equivalence; sub-`e^{t/2}/(t+1)` decay unconditionally on every Burnol
window) `[L]` fixes the exact shape of the required cancellation.

### 5.4 Route MC — selection at the trivial gauge point

Prove the half-power law at `x = 0` from a property of the pole alone: the prime source is
atypical exactly by the pole `[L]`, so the statement is that the pole's contribution to the
Möbius source is of the same size as the typical fluctuation. By §1.5 it is the claim that the
Bochner measure of the orbit kernel has no mass off the torus. Opening the path here means finding
one non-generic (neither measure nor category) property of the Tate line that distinguishes
`t = γ_ρ` from complex `t`.

### 5.5 Route HF — the pencil index stays zero at every multiple

The index is monotone in `K`, zero below `K₀`, and jumps exactly at the critical multiples of the
relative eigen-windows `[L]`; its vanishing at every `K` is RH. HF supplies no mechanism of its own
for the continuation in `K`; §4.5(b) is the sub-RH form.

---

## 6. Q5 — The three open questions to focus on

1. **The odd unit window with its one first-moment charge (A6), by a mechanism that retains the
   Gamma remainder.** It is the base case of P1, the odd cost sector of stage one, a finite explicit
   problem, and its numbers are already within one square of closing `[L]`.

2. **The stage-one criterion on `[2·enlargedWeilFloorAperture, log 3)` as a moment inequality
   (A5/A8, §4.1).** It is the first instance of the sector-coercive stage theorem and fixes the
   shape of the induction: Hankel form at the trivial divisor against one lag overlap.

3. **The critical-curve conductor block at one small multiple (the card in progress), followed by
   the first jump multiple `K_1(A)` (§4.5).** It closes the eighth-root endpoint, starts the pencil
   index at zero, and turns HF's remaining problem into one explicit function `K_1(A)` whose
   finiteness is the negation of RH.

Why these three. They are the three places where the sign is a single explicit scalar (a first
moment, one lag value, one multiple), each on a two-site-decidable object, each with base
positivity already in Lean.

---

## 7. Q6 — The one question

**Can the complete odd unit-window form be proved nonnegative by a certificate that retains the
signed prime-two correlation, the exact Gamma remainder and the pole?**

Status quo `[L]`: for odd `C²` tests `F` supported in `[−½, ½]`,
`Q(F) + (3203/320)(∫xF)² ≥ ‖F‖²/1000`; `Q(F) ≥ ‖F‖²/100` when `∫xF = ∫x³F = 0`; the frozen form is
indefinite (odd cubic: frozen `< −29‖f‖²/2100`, complete `> ‖f‖²/100`); the fixed linear chord
cannot pay the first charge; the exact logarithmic first-moment inverse is positive and the prime
reflection lowers it on its strip; the retained Gamma lower form has a negative direction on the
quintic while the complete form is positive, so the Gamma remainder must be kept; the regional
logarithmic kernel is diagonalized by Legendre polynomials with eigenvalues `2H_n`, and two
vanishing odd moments raise the gap to `H_5 + log 2`.

Why it is less hard than RH or quasi-RH. One window, one prime, one sector, one scalar charge.

Why the answer tells where the proof must be. If the first moment is paid by the signed prime
term together with the Gamma remainder (and not by either alone), the sector-coercive stage theorem
(§5.1) has its base case and its template: the pole square and the self-energies pay the
trivial-zero squares and the fold. If the first moment cannot be paid on the unit window, the odd
cost sector of stage one carries a genuine negative direction, Weil positivity fails on a window
of length one, and RH is false; the corpus's numerics (`[N]`: margins `1.5·10⁻⁵` odd at half-width
`½ log 3`) say this will not happen, so the question is the mechanism, not the number.

This agrees with `obstacles-summary.md §2.8`, with a sharper boundary: Gamma remainder retained,
linear chord excluded, Legendre spectrum available `[L]`.

---

## 8. Q7 — The walls as questions without tools: the new field

### 8.1 Assessment

The walls are not three missing estimates; they are one missing structure: a positivity that is
critical (no slack), signed (uses each fold's sign), additive–multiplicative (couples the successor
and the pole to the Hecke action through the archimedean place), and selective (fails for every
Euler datum with a weaker Euler bound). Nothing in current mathematics produces such a positivity:
Hodge index needs counts (closed over `ℤ`), criticality theory needs Markov forms (closed),
canonical systems need a Hamiltonian (not constructed), Krein spaces need a reflection with a sign
(not available), sum–product theory loses constants. The field that would supply it is the one the
previous reviewer named, with a different emphasis on what its first theorem must be.

### 8.2 Name and objects

**Signed arithmetic criticality on the window tower** — the theory of nonnegative quadratic forms
`Q_A` on growing intervals `[−A, 0]` that are (i) Lévy–Khintchine in the archimedean part (positive
jump rates `ω`), (ii) perturbed by signed folds of lengths `log n` with weights `Λ(n)/√n`, (iii)
carrying one rank-two indefinite pole term, (iv) critical in the limit (ground energy zero, margins
collapsing), and of the inductive passage of their positivity from `A` to `A + ε`.

Objects: window modules `F_A` over the truncated Dirichlet ring; collar classes modulo interior
tests; the two involutions `σ_A` (Serre/Rosati) and `R` (collar reflection) and their four
sectors; the trivial-divisor moment sequences `μ_s`, `ν_s` at `s = 1, −2, −4, …` and the Hankel form
`|μ_1|² − Σ|μ_{−2k}|²`; frozen two-collar forms and Carathéodory disks; lattice Weil sequences,
Schur parameters, outer ground states, zero modes with unimodular angles; the pole as the
hyperbolic pair `e^{±h/2}`; Tate functions `τ_H(k)` and their jets `Λ_j`.

### 8.3 Questions it must answer

1. Does the frozen two-collar form dominate the kick on the cost sectors at every stage, given
   positivity below the stage (the sector-coercive stage theorem)?
2. What is the exact passage law of a critical (Szegő-singular) ground state across a stage, in
   the continuum: the analogue of `E_{n+1} = E_n(1 − γ_n²)` for collar classes, and its
   Hamiltonian (B41)?
3. Which Poincaré inequality for the censored jump process pays the interior where the end profile
   `V_A` is negative, uniformly in `A`, with the pole included?
4. Why do the prime kicks land in their prediction intervals: what arithmetic statement about all
   kicks at once (the Euler product as a product of commuting unipotents on the window) is
   equivalent to the stage inequality?
5. What is the Agmon ground state of a critical window and how does its collar shape relate to the
   palindromic zero mode of a hypothetical first failure?

### 8.4 Point of view and language

Positivity is an evolution, not a property: the window length is time, prime powers are impulses,
the archimedean place and the pole are the free evolution, and RH is the statement that the
evolution never leaves the positive cone and does so without slack. The language is that of
canonical systems and Schur algorithms (Krein, Gelfand–Levitan, de Branges) made arithmetic:
causal in the primes, local in the stage, exact in rank.

### 8.5 Foundational principles

- Exactness: identities and equivalences of unbounded rank; never an estimate losing a factor.
- Signed: every fold enters with its sign; nothing Markov, nothing sign-blind.
- Criticality: the extremal objects have zero margin; proofs are Liouville theorems, not spectral
  gaps.
- Locality and causality: a statement says which primes and which lengths it reads.
- Selection by positivity: the only weight surviving every stage is `Λ`; the theory must reproduce
  the degree gap and the strict Euler bound as consequences.

### 8.6 Criteria it must fulfil

1. Reproduce base positivity through `2·enlargedWeilFloorAperture` and the first prime stage.
2. Pay the pole's one negative square on every lattice and every window.
3. Be critical: margins tend to zero along every lattice; the ground state degenerates in the limit.
4. Deliver the two-site band at every scale.
5. Force `Λ` and fail for flips, Euler twins (including the positive multiplicative twins with
   zeros at `3/4`), `ζ(s)ζ(s − ε)`, Epstein and golden data.
6. Use the functional equation and the Euler product together, with the strict Euler bound.
7. Calibrate over `𝔽_q`: degenerate windows are curve windows; a curve degenerates at its number of
   angles.

### 8.7 Research topics

- The odd unit window and the stage-one moment inequality (§6, §7).
- Sector-coercive stage theorems at stages two and three (the weighted path `2, 3, 2` and the
  rational Hecke graphs of WTZ supply the arithmetic side).
- The continuum canonical system of a bump (B41): Hankel/Jacobi system of the zero measure; the
  jet system of GWZ as its first terms.
- The Agmon ground state of a critical window and unique continuation from the collars.
- The first jump multiple `K_1(A)` of the complete family (§4.5) and its two-site attainment.
- Hankel forms at the trivial divisor: spectral theory of `|μ_1|² − Σ|μ_{−2k}|²` on collar classes
  (the Gamma symbol's Weyl law `ι_Γ(A) ≈ 2A` and the zero-free band `|ξ| < γ_1`).
- The additive–multiplicative coupling of the top coprime stratum (B9) in the language of stages:
  the successor as the pole's partner.
- Explicitly outside: counts and Hodge index over `ℤ`, Tate domination, Markov ground states,
  measure rigidity on the PM side, bounded PM reflections off `Re s = ¼`.

---

## Appendix A — Facts used, with Lean anchors

| Fact | Anchor |
|---|---|
| RH ⇔ `|c_φ(t)| < Q(φ)`; RH ⇔ two-site PD; off RH an exactly degenerate two-site lattice | GWZ `riemannHypothesis_iff_abs_weilOrbitCorr_lt`, `riemannHypothesis_iff_two_site_posDef`, `exists_degenerate_lattice_of_not_riemannHypothesis` |
| RH ⇔ every lattice margin positive; ⇔ no degenerate lattice; ⇔ positive and singular; ⇔ Schur parameters in `(−1,1)` | GWZ `riemannHypothesis_iff_levinsonErr_pos`, `_no_degenerate_lattice`, `_singular_lattices`, `_abs_reflCoeff_lt_one` |
| Kick = collar Rosati form; sector forcing | GWZ `corr_eq_collar_windowInvolution`, `collar_antisymmetric_of_frozen_negative_even`, `collar_symmetric_of_frozen_negative_odd` |
| Transmission through the trivial divisor; closed frozen forms; translation contraction | CSTW `OrderedAt.integral_collarKernel_mul_eq_moments`, `frozenTwoCollar_eq_transmitted`, `firstStage_frozen_congr`, `riemannHypothesis_iff_translation_contraction` |
| No count identity at the first prime | CWS `not_exists_countIdentity` |
| Window index: RH ⇔ `ι(A) < 2` ⇔ `= 0` | CWS `riemannHypothesis_iff_forall_windowIndex_lt_two`, `_eq_zero` |
| Weil's form = dimension-zero jet of counts; Tate positivity does not descend; Hecke similitudes are scalars | WTZ `weilQuad_eq_tateJet`; DZG `tatePositivity_does_not_descend`, `windowRep_similitude` |
| Archimedean Tate domination closed; descent = Weil positivity | ATD `archimedean_tate_domination_complete_solution`, `riemannHypothesis_of_local_archimedeanTateDomination`, `not_exists_shiftedPole_weight_domination_linear` |
| Strict floor past `log 2` | ATD `weilQuad_ge_one_div_eightThousand_of_le_two_mul_enlargedAperture`; AIP `enlargedWeilFloorAperture_bounds` |
| Odd unit window off one moment; two moments suffice; Gamma remainder retained | WTZ `weilQuad_add_first_moment_ge_mass`, `weilQuad_ge_of_odd_two_moments_zero`, `exists_odd_unit_retainedGamma_neg_weil_pos`, `firstFold_linear_chord_exceeds_first_capacity` |
| Folded supersolution criterion and its origin-charge no-go | ACT `riemannHypothesis_of_foldedSupersolution`, `compact_positive_profile_origin_failure` |
| Second order at the critical curve; critical multiple; index resolves zeros; count ends at resolution | AHD `horizon_layer_criticalCurve_exact`, `criticalMultiple_exact`, `exists_windows_resolving_rightZeros`, `exists_countRatio_le_half` |
| Whole space PD below `1/8`; critical-curve far complement | CACT `eventually_tiltedUnitSpline_completeWeilMatrix_posDef_below_one_eighth`, `exists_critical_multiple_weighted_far_complement`, `exists_critical_multiple_low_packet_and_collar_budget` |
| Conductor Gram at every `2K(log N)^{1/8}` is RH; RH ⇔ Liouville along the overlap flow | HWV `riemannHypothesis_iff_conductorGram_nonneg_eighthRoot`, `riemannHypothesis_iff_liouville_along_the_overlap_flow` |
| Prime-blind positivity ⇔ Weil cone nonempty | RHTower `exists_weilPositiveFull_iff_primeBlindPositive` |
| Finite index ⇔ Lindelöf-deep; glued index `κ + 1`; successor + dilation ⇒ infinite index | HKT `zetaKernel_finiteIndex_tfae`; AKG `negIndex_weilArchState_eq_rightZeros`, `negIndex_add_slope_eq_top_of_continuous_dilation` |
| Bounded cone coupling ⇒ RH or no deepest zero | ACoT `riemannHypothesis_or_no_deepest_zero_of_bounded_coneCoupling` |
| Gauge exponents; RH ⇔ trivial point typical | AGT `ae_gaugeExponent_moebius_eq_half`, `moebius_exponent_one_residual_and_null`, `riemannHypothesis_iff_trivialPoint_typical` |
| Transverse energy `< 1` ⇔ RH; collided form second difference | AES `riemannHypothesis_iff_divisorTransverseEnergy_lt_one`; APol `collidedForm_second_difference` |
| PM exact Krein identity; Hecke = Mellin translation for every prime; Serre ≠ Krein reflection; defect `= 0` iff `Re s = ¼` | RIT `weilQuad_eq_completedKreinForm`, `lewisHeckeOperator_windowMellinPeriod`, `no_weil_isometric_krein_reflection_intertwiner`, `resonantLewisPeriod_coIsometryDefect_eq_zero_iff` |
| Degree gap; strong multiplicity one; positive Euler twins at `3/4` | SEL `degree_eq_zero_or_one_le`, `coeff_eq_of_critical_discrepancy`, `exists_positive_multiplicative_twin`, `not_fullClass` |
| `D_win` ⇔ thin Planck shadows; double-log certificates; 8-way equivalence | CDG `logFreeNearLineWindowOccupancy_iff_thinPlanckShadow`, `almostAll_doubleLogStage_besselSzegoCertificate`, `criticalClustering_logMean_mollifier_hecke_tfae` |
| First cyclotomic band ⇔ RH | CAF `riemannHypothesis_iff_chebyshevFirstCyclotomicBand` |
| Theta sections: rank 8 strict | TCS `thetaCuspCenterMixedSignedHankel_eight_posDef` |

## Appendix B — Work in progress relevant to this report

`docs/drafts/pipeline/1-in-progress/the-complete-weil-family-is-positive-at-a-critical-multiple.md`
(A30): whole-space positive definiteness of the complete family for `1 ≤ c ≤ 2K₁(log N)^{1/8}` at one
`K₁ > 0`. In Lean: the below-`1/8` theorem, the dyadic seventh-power top-collar reserve, the
log-free conductor residuals at `Q₁ = (log N)^{13/32}`, the deep-row pairing, the critical-multiple
Schur payment and the weighted far complement on the conductor orthocomplement `[L]`. Open gate: the
assembly of the conductor block with the complement. Reading: it closes the eighth-root endpoint at
small multiples and starts the pencil index at zero; it is size-only (positivity at one multiple is
sub-RH), and its value for RH is to make the continuation in `K`, i.e. the first jump multiple
`K_1(A)` of §4.5, the whole of HF's remaining problem.
