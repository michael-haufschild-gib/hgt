# Review 0311 — consolidated report and big-picture interpretation

Companion to `obstacles-summary.md` (§2.4–2.8 answer the same seven questions from the P1 side),
`route-obstacles.md` (labels `A*`, `B*`, classes P1–P4), `walls-ledger.md` (Σ/Π/Γ),
`route-unification-ledger.md`, `rh-current-frontier-map.md`, `rh-killed-routes.md`, the programme
READMEs under `formal/GaloisForLFunctions/*/README.md`, and `astra.md` (review of an earlier draft;
its validated corrections are incorporated, see §9). Evidence tags: `[L]` a Lean theorem whose
statement was returned by the corpus search; `[S]` in source, not in its umbrella or not
dependency-closed; `[D]` derived here from `[L]` statements; `[C]` a proposal of this report; `[N]`
numerical. Windows of length `A` are real `C²` tests supported in `[−A, 0]`; `Q` is Weil's form;
`c_φ(t) = W(φ, φ(· − t))` is the orbit correlation; `κ ∈ ℕ∞` is the number of distinct zeros right of
the line; `a_φ = (∫φ)²/∫φ²` is the atom normalization (written `κ` in the AHD README).

---

## 1. The programme in one picture

### 1.1 One invariant, one inequality, two landings

The invariant. `κ` is read exactly as: the negative index of the orbit kernel of the cubic spline
on `ℚ_{>0}^×`, `negIndex zetaKernel = (rightZeros).encard` (HKT) `[L]`; the supremum of the window
indices, `⨆_A ι(A) = (rightZeros).encard`, each `ι(A)` finite (CWS) `[L]`; the index of the glued
archimedean and `p`-adic states, `κ + 1` at every place (AKG) `[L]`; the supremum over families of
the window index of the pencil of the complete family (AHD) `[L]`; the collision charge of the
reflection configuration (HEF: RH ⇔ `O < 2`) `[L]`. `κ` takes values in `ℕ∞`; when finite it is
even (right zeros pair by conjugation) and then all zeros above some height lie on the line
(HKT `zetaKernel_finiteIndex_tfae`), which implies Lindelöf and a zero-free half-plane `Re s > ½ + α`,
`α < ½` (`lindelof_of_negIndex_zetaKernel_lt_top`, `quasiRH_of_negIndex_zetaKernel_lt_top`) `[L]`. No window carries the global invariant; the windows exhaust it by supremum.

The inequality. RH ⇔ `|c_φ(t)| < Q(φ)` for every nonzero bump `φ` and every `t ≠ 0`
(GWZ `riemannHypothesis_iff_abs_weilOrbitCorr_lt`) `[L]`, and with CSTW's ordered coupling `[L/D]`

`c_ψ(t) = A(ψ)B(ψ) e^{t/2} − Σ_{k≥1} μ_{−2k}(ψ) ν_{−2k}(ψ) e^{−(2k+½)t} − Σ_n Λ(n) n^{−1/2} (ψ⋆ψ)(t − log n)`:

the first two terms are the trivial divisor of `ζ` (pole `+`, trivial zeros `−`) through the
exponential moments of `ψ`, the last is the `ψ⋆ψ`-smoothed Chebyshev count near `e^t`. So the
inequality says the smoothed prime count matches `AB e^{t/2}` within the constant `Q(ψ)` at every
scale. In the ledger's words: Σ on two sites is Π at one point.

The two landings. The sharp constant is not the only landing. For the fixed cubic spline `B`
(which sees every right zero): RH ⇔ `∀ε > 0 ∃K ∀t ≥ 0: |c_B(t)| ≤ K e^{εt}`
(AOG `riemannHypothesis_iff_splineOrbit_subexponential`) `[L]`; RH follows from
`|c_B(t)|^k ≤ C_k e^{L_k t}` with `L_k/k → 0`, and RH ⇔ one fixed exponent `L` bounds every tensor
power (ACP `riemannHypothesis_of_sublinear_tensor_loss`, `riemannHypothesis_iff_fixed_tensor_loss`)
`[L]`; linear loss `L_k = kσ` is exactly zero width `≤ σ` `[L]`. Consequence `[D]`: an argument may
lose multiplicative constants, even order-dependent ones; what it may not lose is a positive
exponential rate. "No slack" (collapsing lattice margins, Weil cone a point) constrains the
window and lattice forms, not every receiver.

### 1.2 What is established, by what it says about a mechanism

| Theme | Status quo `[L]` unless marked | Consequence for a proof |
|---|---|---|
| Two sites decide | RH ⇔ every two-site lattice window PD; off RH some short generic bump has an exactly degenerate two-site lattice at some step (GWZ) | Interiors, stages, collars are proof *mechanisms*, not needed to *decide*; the theorem supplies no minimizer at a prescribed aperture |
| Growth of a window | `Q = Q_N − 2w c_H(ℓ)` per prime power; the kick reads collar data only; it is the collar Rosati form `∫_L H·(σ_AH)∘R`, `= ±¼(∫(H+H∘R)² − ∫(H−H∘R)²)` on `σ_A`-even/odd tests; growth law `Q ≥ 0` on `W_{ℓ+ε}` ⇔ `Q ≥ 0` on `W_ℓ` and `W(τ_εu, v)² ≤ Q(u)Q(v)` ∀`u, v` on `W_ℓ` (CSTW `window_nonneg_iff_contraction`); RH ⇔ every growth step contracts | The open step of any window induction is an independent bound on the mixed pairing `W(τ_εu, v)` of shorter-window tests; the collar-sector theorems of GWZ assume positivity on the enlarged window and cannot replace it (§9) |
| Transmission | Across a cut the archimedean place and pole couple ordered tests only through moments at the trivial divisor, kernel `κ(x) = e^{x/2} − Σ_k e^{−(2k+½)x}`; frozen two-collar forms in closed form at stages 1, 2 (CSTW) | The first-stage problem is a problem about two moment sequences at the trivial divisor and one `L²` overlap at lag `log 2` |
| Lattice canonical system | Weil sequences are Toeplitz; Schur–Levinson evolution exact and causal; one prime kick moves one Schur parameter; only `Λ` survives all lattices; degenerate window = finite curve; under RH Szegő-singular; continuum limit is a jet system (GWZ) | Margins collapse in the lattice form; the kicks must land in prediction intervals that shrink |
| Dimension zero | Weil's window form = `d/dk|₀` of the Tate function with integer values `φ(m)#ℙ^{k−1}(ℤ/m)`; jets are Bombieri's `Λ_j`; `k ↦ −k` is Dirichlet inversion with parity `(−1)^{ω(n)}`; Tate positivity holds for `ζ(s)ζ(s−ε)` and does not descend (WTZ, DZG); no archimedean family dominates the counts across the tower, pole weights pinched to `1/ζ(1+k) < k`, window-local domination is Weil positivity (ATD) | The sign is a first-order jet; count/domination mechanisms are closed |
| Complete family at the critical curve | First order = count `J(1)#ℙ⁷(ℤ/m)`; on horizon windows along `c⁸/log N → R`: `c⁻¹⟨Wx,x⟩ → a_φ Q(H) + (7J(1)/R)‖H‖²_{−8}` exactly; a window with `Q(H) < 0` is eventually negative iff `R > R*(H) = 7J(1)‖H‖²_{−8}/(a_φ|Q(H)|)`; on the equality face of the pencil the canonical clock gives eventually *negative* energy (`canonicalCriticalClock_energy_negative`); twisted sectors are zero-blind counts; count form ends at the resolution `m ≍ c`; window index resolves the right zeros of its length and is capped by the Shannon number (AHD) | Everything below the sign is size-only; positivity at one multiple is sub-RH, at every multiple is RH; passing through a zero margin needs new input |
| Base positivity | All `C²` tests of support length `≤ 181/250`; strict floor `1/8000` on windows up to `2·enlargedWeilFloorAperture ∈ (181/250, 1)` (ATD); windows `≤ 1/7` by exit charge; odd unit window: `Q(F) + (3203/320)(∫xF)² ≥ ‖F‖²/1000` (`weilQuad_add_reduced_first_moment_ge_mass`; `5123/320` in the unreduced form); `Q(F) ≥ ‖F‖²/100` when the first and third moments vanish; the retained Gamma lower form has a negative direction while the complete form is positive (WTZ) | The first prime acts as a positive source; the Gamma remainder cannot be discarded; the open base case is one quadratic charge |
| Whole space | `completeWeilMatrix tiltedUnitSpline c N` PD for `1 ≤ c ≤ (log N)^α`, `α < 1/8` `[L]`; at the critical curve the far complement, the low packet through `(log N)^{13/32}`, the Schur payment and the weighted collar are in Lean `[L]`, and a capstone `exists_critical_multiple_completeWeilMatrix_posDef` (PD for `1 ≤ c ≤ 2K(log N)^{1/8}` at one `K ∈ (0, ½]`) is in source `[S]`, not umbrella-wired; RH ⇔ for every `K > 0`, eventually, the conductor Gram at `2K(log N)^{1/8}` over all conductors `e ≤ N` is PSD for every coefficient vector (HWV) | One small `K` and fixed families are size-only; the receiver needs all `K` and all vectors |
| Arithmetic charges (CSAR) | The prime generator `G` on prime-supported input splits as one coherent constant minus diagonal prime rows; the centred output has the cutoff-independent bound `mean|GF − P_M(a)|² ≤ (log 2/2) L_M(a)`; a prescribed constant charge `t` survives adjunction energy `t²/B_M → 0` and vanishing physical input, harmonic-pole-neutral, uniformly over horizons (`exists_harmonic_neutral_physical_vanishing_charge`); `G` is a derivation across coprime conductors (`normalizedPrimeModeSource_mul_of_coprime`); prime residuals carry a quadratic logarithmic conductor cost attained on explicit coherent packets `[L]` | Energy and physical-input norms can erase a nonzero receiving charge; a limit argument must retain it or prove its cancellation in the complete form; norms are not signed forms |
| Complete-form identities | `completeWeilEnergy_packetVector_at_every_overlap`: prime jump energy + ½ affine Dirichlet energy + Mertens–Euler diagonal − shell degree + centre, cross, pole-error and overlap terms (ACoT); prime successor edges `(n, pn+1)` bound nonconstant packet mass by affine energy with factor `(B_{⌊N/16Q²⌋} − B_Q)/64` (ACoT); divisor jet completes to exact squares `Σ_{m∣D}Σ_{k∣m}Λ(m/k)φ(k)(f(m) − f(k))²` (SSh); joint shell–pole cancellation for bounded base profiles with mean-zero periodic top-band perturbations, uniform in overlap (SSh) `[L]` | Exact signed structure exists for a joint comparison of growing packets against their complement with boundary terms |
| PM | `Q(H) = 2 Re[𝓦H, 𝓦H]` exactly on `ℓ²(upper Mayer resonances)`; `T_p − Id` is the Mellin translation for every prime; `D_p` a Krein similitude of factor `p`; Lewis defect `≤ 0`, `= 0` iff `Re s = ¼`; bounded Cauchy reflection only for `Re s ≥ ¼`; window Serre duality is *not* the linear Krein reflection; physical cusp energy has the Krein form as linear term, counterterms carry no sign (RIT) | PM is the zero side in Krein coordinates; the reflection carries no sign of its own |
| Selection | Weil cone `{Λ}`; lattice selection; FE + positive measure ⇒ counting measure of `ℕ` (APD); degree gap `(0,1)` empty; strong multiplicity one at the critical Euler abscissa for arbitrary Gamma data; positive multiplicative twins `ζ(s)(1 + Ap^{−s} + p^{1−2s})` (degree one, conductor `p²`, root number one) with zeros at any `Re s ∈ (½,1)`, excluded from the full class only by the strict Euler bound `θ < ½` (SEL) | Selection is automatic after positivity; a proof must use FE and Euler product together; among the tested axioms only the strict Euler bound separates `ζ` from these twins (their conductor also differs) |
| Gauge | Möbius exponent `½` Haar-a.e., `1` Baire-generically; RH ⇔ the trivial point typical; prime source atypical exactly by the pole (AGT, ACG) | Neither measure nor category reaches the trivial point |
| Theta source | The complete signed centre-mixed source-jet hierarchy is positive throughout the critical aperture iff RH (`ThetaCuspCenterMixedSignedJetCompleteness`, with smoothness, decay and moment determinacy as source theorems); the signed Hankel section of size eight is strictly positive for every `0 < a < ½` (TCS) | An RH-equivalent *source* positivity with its own lane; a generic positive moment extension is insufficient (the next moment is prescribed) |
| Density (WD) | 8-way unconditional equivalence of critical-line log-mean, mollifiers, off-line moments, 100% clustering, dyadic Hecke defect; `D_win` ⇔ thin Planck shadows; almost-all Bessel–Szegő certificates at the double-log stage; countermodels exclude volume and moment inputs (CDG) | WD's single analytic input is one double-logarithm short |
| Coupling | Bounded two-prime cone coupling ⇒ RH or no deepest zero; RH on the finite stratum (ACoT) `[L]`; an abstract sign- and conjugation-symmetric divisor with exact spline weights, the full Riemann–von Mangoldt count with `O(log T)` remainder, bounded two-prime coupling and positive *unattained* width exists (`exists_two_prime_rvm_prescribed_spline_divisor`) `[L]` | Zero counts and bounded coupling cannot replace source arithmetic; the finite-stratum hypothesis is essential |

### 1.3 The three walls are one wall; where the sign hides, and what hides with it

Σ, Π and Γ are the same obstruction in three coordinate systems. In every exact decomposition the
corpus has, the sign of RH sits in a *trivial direction* whose complement is positive by a theorem:

- Tate dimension `k = 0` (counts at `k > 0`) `[L]`;
- the pole `u = 0` of the frequency count (Hurwitz forms at `u ≠ 0`) `[L]`;
- conductor one in the block-diagonal second order (counts at `m ≥ 2`) `[L]`;
- the pole coordinate of the bulk (pole-free packets are blind) `[L]`;
- the trivial gauge point (Haar-a.e. exponent `½`) `[L]`;
- the one scattering channel surviving at each Mayer resonance `[L]`;
- the one negative square of the glued state, the hyperbolic pair `e^{±h/2}` on lattices `[L]`;
- the first-moment direction of the odd unit window `[L]`.

What these decompositions do not supply is the *mixed pairing* between the trivial direction and
its complement, and that pairing is the open problem in each case: the contraction term
`W(τ_εu, v)` of the growth law, the Schur form `A − BD⁻¹B*` of the conductor block against the
complement, the receiving charges that vanishing-energy inputs retain. The reduction is exact; it
is not a localization of the difficulty to a scalar. (A global index bound `≤ 1` for the cubic
spline would already be RH, since the index is even `[D]`.)

The reason the trivial direction carries the sign is a theorem in several forms: the Euler product
enters the zero side only through the pole (LST, AHD, ACoT) `[L]`; all non-trivial twists are
Hurwitz–Lerch objects without Euler product. Neither the functional equation nor the Euler product
alone selects `ζ` (APD, SEL) `[L]`.

A second structural fact: the obstruction is additive–multiplicative. The window algebra is purely
multiplicative (the Dirichlet ring truncated at `e^A`; Hecke similitudes are scalars; the reflection
lies outside it) `[L]`; the pole and the successor are additive; every successor pair lies in the
top coprime stratum (HWV) `[L]`; a positive-definite kernel on the affine group with an integer
successor and a continuous dilation has infinite index (AKG) `[L]`; and the prime successor edges
`(n, pn+1)` are exactly what pays nonconstant packet mass in the affine energy (ACoT) `[L]`.

### 1.4 The four live classes

| Class | Content | State |
|---|---|---|
| P1 signed criticality | a signed certificate of unbounded rank at every stage, using the sign of each fold | the raw folded supersolution is excluded for every nonnegative compact profile by the origin charge (ACT) `[L]`; the odd unit window is one quadratic charge from closed `[L]`; strict base floor past `log 2` `[L]`; the exact growth statement is the contraction law `[L]`; no induction law across stages exists (§9) |
| P2 prime-blind positivity | archimedean + pole part `≥ 0` on finite nonnegative combinations of autocorrelations of complex `C²` tests whose *combined* symmetric samples vanish at every `log n`, `n ≥ 2` (individual tests need not be blind or nonnegative) | RH ⇔ `PrimeBlindPositive` (`riemannHypothesis_iff_primeBlindPositive_unconditional`) `[L]`; the nonnegative, individually blind reduction is conditional on a short-window inequality (`weilArchRe_nonneg_of_primeBlind` assumes `WindowPositive`) `[L]`; the signed aggregate cone is open |
| P3 PM reflection | Krein positivity on the completed resonant space | exact identity, Hecke for every prime, antiunitary reflection; reduced to the zero side `[L]` |
| P4 square-root cancellation | one smoothed prime sum, or subexponential orbit growth, or sublinear tensor loss | first cyclotomic band ⇔ RH exactly (CAF) `[L]`; parity barrier at damping `½` `[L]`; fixed-spline receivers accept constant losses `[L]` |

### 1.5 A unification: the gauge torus is the dual of the orbit group

The orbit kernel `K_ζ(n/m) = W(φ(· − log n), φ(· − log m))` is a Hermitian function on the discrete
group `ℚ_{>0}^×` (HKT) `[L]`; its dual group is the compact torus `∏_p S¹` of unimodular completely
multiplicative functions, AGT's gauge torus `[D]`. Under RH the kernel is positive definite and its
Bochner measure on the torus is `Σ_ρ m_ρ|φ̂(γ_ρ)|² δ_{χ_ρ}`, `χ_ρ(n) = n^{iγ_ρ}`: supported on the Tate
line `{n ↦ n^{it}}` at the zero ordinates `[D]`. Off RH the kernel is not positive definite and has
no Bochner measure; if its index is finite, Krein–Langer theory (`isKreinLanger_zetaKernel_iff_negIndex_lt_top`
`[L]`) represents it with finitely many non-unitary exceptional characters `n ↦ n^{ρ−½}`; if the
index is infinite there is no such representation. The Tate line is dense in the torus (Kronecker)
and the Tate flow is uniquely ergodic on it, so every *continuous* functional of a gauge point has
its Haar-typical value on average along the Tate line: this is the mean-value theorem for Dirichlet
polynomials, and it is why random multiplicative functions and Montgomery–Vaughan mean values are
one theorem. The exponent is a `limsup`, not a continuous functional, and the Baire-generic value is
`1` `[L]`; RH is the value `½` at the one point `0` whose only distinguishing feature is the pole
`[L: AGT]`. MC, AGT, HKT, AKG are one object seen from the group, its dual and its spectral measure;
none has a tool for the single point.

### 1.6 Route states

- **PM.** Everything structural is exact (completed Krein space, Hecke multipliers for every prime,
  Eisenstein and Barnes periods as Hecke eigenfunctions, Hecke cones tiling the quadrant, closed
  Cauchy reflection, physical admission detecting resonances, Gaussian synthesis recovering the
  complete Weil form) `[L]`. Negative facts: Serre duality is not the linear Krein reflection; the
  finite-energy core is not a Hecke eigenvector with the completed eigenvalue; no bounded reflection
  across the strip; counterterms carry no sign `[L]`. PM owns no sign.
- **MC.** Half-power and Redheffer criteria, gauge exponents, bands retain `2Θ` `[L]`; open item:
  cancellation at the trivial point.
- **WD.** Eight equivalent readings of critical-scale clustering; `D_win ⇔ D_zero` up to a cluster
  tail; double-log certificates; inner caps `σ_m = 1 − 1/(116 log(m+5))`; right half-port rigidity
  `[L]`. Open: `D_win` at fixed depth; inner-cap cancellation (RH at all degrees).
- **HF.** Subcritical PD below `1/8`; critical-curve far complement, low packet and Schur payment
  `[L]`; capstone at one small multiple `[S]`; twisted sectors, short windows and the cosh hyperplane
  inherit `[L]`; count form ends at the resolution `[L]`. Open: the all-`K`, all-vector conductor
  Gram; the Schur form of the conductor block against the complement at growing scales; the
  receiving charges (§1.2).
- **TH.** Signed-jet completeness ⇔ RH `[L]`; rank eight strict `[L]`; all ranks open.

### 1.7 The shape any proof must have `[D]`

1. It is a statement about all stages at once (stages are not independent: margins collapse), or a
   growth-rate statement for one fixed spline orbit, or a positivity of one RH-equivalent source
   hierarchy at every rank.
2. Its input is the functional equation and the Euler product with the strict Euler bound; its
   output must fail for the positive twins, flip twins, shifted products, Epstein data and the
   golden fake.
3. It is not a count, not a Markov or sign-blind ground state, not a fixed-rank identity, not a
   twisted-sector statement, not a bounded operator identity on the PM side.
4. It may lose constants but not rate: the forbidden loss is a positive exponential rate in the
   orbit variable (that is the zero width) or a multiplicative slack in the window/lattice forms
   (which have none under RH). A proof is a Liouville theorem — bounded ⇒ constant — for an explicit
   convex functional along the dilation flow (the collided form has second difference
   `Σ m_ρ(2cosh(2(Re ρ − ½)L) − 2)|tr f(ρ)|² ≥ 0` `[L]`).
5. It retains the arithmetic charges that energy limits erase (§1.2, CSAR), or proves their
   cancellation inside the complete form.

---

## 2. Q1 — A new proof mechanism

### 2.1 What a mechanism may still be

By §1.2–1.4 a mechanism must produce one of: the mixed-pairing bound `W(τ_εu, v)² ≤ Q(u)Q(v)` for
shorter-window tests at every stage; the all-`K` conductor Gram; the rank-uniform theta source law;
the signed aggregate prime-blind cone; or a zero growth rate for the spline orbit. The two
proposals below are the ones not excluded by the ledgers.

### 2.2 Proposal A — joint arithmetic cancellation with retained charges `[C]`

Object: the complete form on growing packets at the critical overlap, with the exact
decomposition `completeWeilEnergy_packetVector_at_every_overlap` `[L]` (prime jump energy, affine
Dirichlet energy, Mertens–Euler diagonal, shell degree, centre, cross, pole-error, overlap).

Mechanism: on the normalized prime-charge families `a_p = (t/B_M)√(p−1)/p` and their coprime fibre
products (the derivation law `G(e_{ab}) = e_bG(e_a) + e_aG(e_b)` `[L]`), compute the complete form
and its polarized pairing with the complement *exactly*, retaining shell, Gamma, pole and horizon
boundary terms, and identify which term pays or cancels the receiving charge `t` that adjunction
and physical energies lose. Candidates in Lean for the paying term: the affine successor energy
(`prime_successor_edges_control_nonconstant_packets` `[L]`), the divisor-jet squares `[L]`, the
top-band joint shell–pole cancellation `[L]`.

Why it is not excluded: it is neither a count, nor Markov, nor a finite identity, nor a twisted
sector; it uses the signed structure of the complete form and confronts a proved obstruction (the
charge that energy limits erase). Where complement coercivity is available, the quantity to control
is the Schur form `A − BD⁻¹B*`, not separate positive blocks; extending coercivity to the required
scales is part of the task.

Landing: the all-`K`, all-vector conductor Gram (`riemannHypothesis_iff_conductorGram_nonneg_eighthRoot`)
`[L]`, or, with constants free, the subexponential spline-orbit receiver `[L]`.

Risk: the explicit families may show that *every* nonconstant mode's charge can be retained by
vanishing-energy inputs (§7); then only exact identities, not limits, can carry the argument.

### 2.3 Proposal B — the growth-rate landing for one orbit `[C]`

Object: `c_B(t)` for the cubic spline, an explicit function of `t` by the ordered-coupling identity
of §1.1 `[L/D]`.

Mechanism: prove `|c_B(t)| ≤ K_ε e^{εt}` for every `ε > 0` directly from the prime sum with the
trivial-divisor moments as main term, i.e. a smoothed prime number theorem with square-root error
for one fixed smoothing, with constants free; or the tensor form `|c_B(t)|^k ≤ C_k e^{L_k t}`,
`L_k/k → 0`, where the loss may grow sublinearly in the tensor order `[L]`.

Why it is listed: it is the only landing in which multiplicative constants are free, so estimates
that cannot keep a sharp window margin are not disqualified; the function-theoretic statement
`Re ξ'/ξ(s) > 0` on `Re s > ½` (Lagarias) is its half-plane form. (`−ζ'/ζ` is not Herglotz on
`Re s > 1`: at `t = π/log 2` its real part is negative for large `σ` `[D]`; positive Dirichlet
coefficients give boundedness, not a positive real part.) The Schur algorithm of GWZ and a Pick
problem for `ξ'/ξ` are analogues, not an identification.

Risk: Π in its classical form; the corpus's parity barrier and precision class apply.

### 2.4 Assessment

Proposal A is recommended: it uses the corpus's deepest exact structure, has explicit test families
and a proved obstruction to confront, and lands on an exact receiver. Proposal B fixes the
landing criterion for any estimate produced along the way. The sector-coercive induction proposed in
an earlier draft is withdrawn (§9).

---

## 3. Q2 — A wildly different approach

The corpus has *proved* that the space of approaches is small: every reformulation reads `κ`; two
sites decide; selection is automatic after positivity; FE and Euler product are both needed; counts,
positive dimension, Markov, finite rank, twisted sectors and PM reflection carry no sign `[L]`.
"Wildly different" can only mean meeting Σ with different inputs.

1. **Prime-blind existence (P2).** RH ⇔ `PrimeBlindPositive` `[L]`: the archimedean and pole part
   is nonnegative on every finite nonnegative combination of autocorrelations of complex `C²` tests
   whose combined symmetric samples vanish at every `log n`, `n ≥ 2`. No von Mangoldt value is
   estimated; the integers enter as a zero set of combined samples. The nonnegative, individually
   blind reduction is proved only under a short-window inequality `[L]`; the signed aggregate cone is
   the open object. This remains the route far from the others (`obstacles-summary.md §2.4`).

2. **The theta source hierarchy (TH).** RH ⇔ positivity of the complete signed centre-mixed
   source-jet hierarchy throughout the critical aperture `[L]`, with rank eight strict `[L]`. Its
   inputs are the theta function's own jets, not prime sums; its missing step is a rank-uniform law
   for the next Schur complement, and a generic positive moment extension is insufficient because the
   next moment is prescribed by the source.

3. **Spectral measure on the gauge torus (§1.5).** A reading rather than a route: it explains why
   probabilistic and mean-value methods cannot reach the trivial point.

Verdict: P2 and TH are the two lanes with different immediate inputs; both receivers are
RH-equivalent positivities.

---

## 4. Q3 — Breakthrough questions less hard than RH or quasi-RH

### 4.1 Whole programme — the first prime stage as a moment inequality

Question. For `A ∈ [2·enlargedWeilFloorAperture, log 3)`, prove the stage-one criterion
`2w₂ c_H(log 2) ≤ S^1_A(H)` on every collar class, in CSTW's closed form: with the two-collar
complement `Φ_ε(μ(x_L), ν(x_R))` a function of the two moment sequences at the trivial divisor,
`Q(x_L) + Q(x_R) + 2⟨μ(x_L), ν(x_R)⟩ + Φ_ε ≥ 2w₂∫x_L(u)x_R(u + log 2)du`. Equivalently (contraction
law `[L]`): `W(τ_εu, v)² ≤ Q(u)Q(v)` for all tests `u, v` on `W_{log 2}`, `ε < log(3/2)`.

Why below RH. One window, one prime, explicit kernel; the pieces are coercive (`Q ≥ (1/8000)‖·‖²`
`[L]`).

Why an advance. The first positivity in which a prime enters with its sign and the trivial zeros as
an infinite moment system; the first mixed-pairing bound of the growth law beyond the proved lengths.
It does not by itself give an induction law for later stages (§9).

Status quo. Proved for `A ≤ 181/250` by the frozen form alone `[L]`; strict floor up to
`2·enlargedWeilFloorAperture` `[L]`; no finite count identity at this stage `[L]`.

### 4.2 Route PM — the sign of one boundary channel

Question. At every upper Mayer resonance the raw Hecke image of the core leaves whole-Haar `L²`
and exactly one boundary coefficient restores it; the zeta-axis channel vanishes, leaving one
scattering correction per prime `[L]`. Prove that the sign of this coefficient is read off
`Re s − ¼` from the retained boundary channel of `T_2` alone.

Why below RH / why an advance. One explicit coefficient at each resonance; the first sign statement
PM would own. Risk: the eigenvalue `1 + p^{1−2s}` is the Euler factor, so it may reduce to the
classical argument.

### 4.3 Route MC — square-root cancellation at one explicit non-arithmetic gauge point

Question. Exhibit one explicit gauge point `x ≠ 0`, not a Dirichlet character and not a Tate
translate, with proved Möbius exponent `½`.

Why below RH / why an advance. The Haar-a.e. statement is proved `[L]`; the explicit points known
fail the half-power law (the Liouville twist `[L]`, whose sum is the squarefree count `[D]`) or are
RH-equivalent. One deterministic point with exponent `½` would show the law is reachable without the
pole.

### 4.4 Route WD — `D_win` at fixed depth

Question. For every `A > 0`, the unit windows in `[V, 2V]` containing a zero of depth `≥ A/log V`
number `≤ ε(A)V`, `ε(A) → 0`; equivalently thin Planck shadows occupy `o_A(V)` windows `[L]`.
Status quo: proved at depth `(2/r)log log V + u` `[L]`; countermodels exclude volume and moment
inputs `[L]`. One double logarithm short.

### 4.5 Route HF — exact charge accounting on explicit families, then the capstone

Question (a). On the normalized prime-charge families and their coprime fibre products, compute the
complete form at the critical overlap exactly with every term of
`completeWeilEnergy_packetVector_at_every_overlap`, and determine which term pays or cancels the
receiving charge `t` (§1.2). First classification test: whether inputs supported on `mp`, `m`
fixed, `p ∤ m` growing, retain the nonconstant output `e_m` while adjunction and physical energies
vanish. Heuristic `[D]`: by the derivation law, `G(Σ_p a_p e_{mp}) = (Σ_p a_p c_p)e_m + Σ_p a_p e_p(G(e_m) − τ(p)e_m)`
with `c_p = log p/√(p−1)`, so the scalar-case coefficients give output `t·e_m` with energy
`≍ t²/B_M → 0`; the test is expected to answer *yes*, in which case every mode's charge can hide in
vanishing-energy inputs and only exact identities, not energy limits, can carry the conductor-Gram
receiver.

Question (b). Close the capstone `exists_critical_multiple_completeWeilMatrix_posDef` `[S]` into its
umbrella with dependency closure; then, on the critical curve, the quantity of interest is the Schur
form of the conductor block against the coercive complement as the conductor cutoff grows.

Question (c), the quantitative window form. For a length `A`, let `R₁(A)` be the infimum of
`R*(H) = 7J(1)‖H‖²_{−8}/(a_φ|Q(H)|)` over tests on `[−A, 0]` with `Q(H) < 0` (`∞` if none). `R₁` is
nonincreasing in `A` `[D]`; `R₁(A) = ∞` iff `Q ≥ 0` on `W_A`; `R₁(A) ≥ R₀ = 7J(1)/(a_φC(8))` for every
`A`, with `C(p) = |Ω(0)| + 2ΣΛ(n)n^{−(p+1)/2} + 1/(p+1) + 1/(p−1)` aperture-independent `[L]`. A lower
bound `R₁(A) → ∞` is RH; the sub-RH content is a lower bound at one fixed `A` beyond the proved
lengths, which is window positivity at that length in quantitative form. Whether an infimum is
attained on a two-site window is not proved (two-site detection gives no minimizer `[L/D]`), and on
the equality face the canonical clock is eventually negative `[L]`, so continuation through a zero
margin needs new input.

(In the overlap convention `c = 2K(log N)^{1/8}` of CACT and HWV, `R = (2K)^8`.)

---

## 5. Q4 — Breakthrough questions that open the path to RH

### 5.1 Whole programme — the mixed-pairing bound of the growth law at every stage

For every `0 < ε < ℓ`, prove `W(τ_εu, v)² ≤ Q(u)Q(v)` for all tests `u, v` on `W_ℓ` by an argument
whose premises are positivity on `W_ℓ` and arithmetic, not positivity on `W_{ℓ+ε}`. By
`riemannHypothesis_iff_translation_contraction` `[L]` this is RH. What opens the path is a bound on
the mixed pairing that is *uniform in the stage*: the sector theorems of GWZ describe where failures
would sit on a window already known positive and cannot supply it (§9). The CSTW closed forms give
the stage-one and stage-two shapes of the pairing (trivial-divisor moments plus earlier-fold
transports) `[L]`.

### 5.2 Route PM — finite cusp energy forces zero defect

`∫_1^∞|ψ(2a) − 2^{1−2s}ψ(a)|²da/a < ∞ ⇒ D_s(ψ) = 0` for Lewis periods: finite cusp energy ⇔
resonance and `D_s = 0` ⇔ `Re s = ¼` `[L]`. As in `obstacles-summary.md §2.6.2`; the physical cusp
energy's linear term *is* the Krein form and the counterterms carry no sign `[L]`.

### 5.3 Route WD — inner-cap cancellation at every polynomial stage

Cancel the right-port flux through `[½, σ_m]` on every Burnol unit window by a source identity;
across all degrees it is RH `[L]`; the six-way right-half-port rigidity fixes its shape `[L]`.

### 5.4 Route MC — selection at the trivial gauge point

Prove the half-power law at `x = 0` from a property of the pole alone (the prime source is
atypical exactly by the pole `[L]`); by §1.5 it is the claim that the orbit kernel is positive
definite with Bochner measure on the Tate line.

### 5.5 Route HF — the all-`K`, all-vector conductor Gram

For every `K > 0`, eventually in `N`, for every coefficient vector over all conductors `e ≤ N`, the
conductor Gram at `2K(log N)^{1/8}` is PSD `[L: equivalence]`. Fixed-conductor diagonals, one small
`K`, and non-effectively growing packets do not supply these quantifiers; what would is an exact
Schur-form identity of the conductor block against the complement that retains the receiving
charges (§2.2).

### 5.6 Route TH — a rank-uniform theta source law

From the strict low-rank signed-flux payments extract a recurrence, factorization or comparison for
the next Schur complement at every rank and every `0 < a < ½`; positivity at all ranks is RH `[L]`.

---

## 6. Q5 — The three open questions to focus on

1. **Exact charge accounting on the explicit prime-charge families at the critical overlap
   (§4.5(a)).** It uses the deepest exact structure in Lean (complete-form decomposition, derivation
   law, successor reserve, divisor-jet squares), confronts a proved obstruction, and its answer
   decides whether energy limits or only identities can carry the conductor-Gram receiver.

2. **The first-prime-stage mixed-pairing bound (§4.1) with the odd unit window as its diagnostic
   (§7).** The only place where a prime acts as a positive source with the trivial zeros as an
   infinite moment system and the pieces already coercive.

3. **A rank-uniform theta source law (§5.6).** An RH-equivalent source positivity with strict rank
   eight and a prescribed next moment; the lane with inputs disjoint from prime sums.

Why these three. Each is an exact statement on an explicit object with its base already in Lean,
each confronts a named obstruction (charges erased by energy, mixed pairing not supplied by sector
theorems, prescribed next moment), and together they cover the three live shapes: identity on the
complete form, growth of a window, positivity of a source hierarchy.

---

## 7. Q6 — The one question

**Does the complete form at the critical overlap pay the receiving charge that energy limits erase?**

Precisely: on the harmonic-pole-neutral families with `packetMean(GF) = t`, adjunction energy
`< ε` and physical input `< ε` (`exists_harmonic_neutral_physical_vanishing_charge` `[L]`), and on
their coprime fibre products, evaluate `completeWeilEnergy` at `c ≍ (log N)^{1/8}` with every term of
the exact decomposition `[L]` retained, and determine whether the charge `t` is paid by the affine
successor energy, cancelled by the shell–pole terms, or survives as a signed residual against the
complement.

Why it is less hard than RH or quasi-RH. Explicit families, one overlap scale, an identity to
evaluate; the first result is a sharp residual classification, not a sign for all vectors.

Why the answer tells where the proof must be. If the charge is paid by an identifiable term, the
conductor-Gram receiver can be approached by retaining finitely many such terms in the Schur form
of the conductor block, and the critical-curve programme has its mechanism. If every mode's charge
survives with vanishing energy (the expected answer of the classification test, §4.5(a)) and no term
of the complete form pays it, then energy and norm arguments at the critical curve are excluded as
a class and the programme must proceed by exact signed identities only — a wall as sharp as the
parity barrier, and worth having in Lean.

**The one finite question kept as a diagnostic (odd unit window).** With `L(F) = ∫xF`,
`b = 3203/320` and `R(F) = Q(F) + bL(F)²` on odd `C²` tests supported in `[−½, ½]`, the proved floor
`R(F) ≥ ‖F‖²/1000` `[L]` makes the remaining question exactly `b · sup_{F≠0} L(F)²/R(F) ≤ 1`, with the
exact Gamma remainder and the signed prime-two term retained in any certificate (the retained Gamma
lower form has a negative direction `[L]`). Solving it is a bounded-window advance and the template
for §4.1; it is not established as the privileged entrance to RH, since no induction law follows
from it (§9).

---

## 8. Q7 — The walls as questions without tools: the new field

### 8.1 Assessment

The walls are one missing structure: a positivity that is critical (no slack in the window and
lattice forms), signed (uses each fold's sign), additive–multiplicative (couples successor and pole
to the Hecke action through the archimedean place), charge-retaining (keeps what energy limits
erase), and selective (fails for every Euler datum with a weaker Euler bound). No present field
produces it: Hodge index needs counts (closed over `ℤ`), criticality theory needs Markov forms
(closed), canonical systems need a Hamiltonian (not constructed), Krein spaces need a reflection
with a sign (not available), sum–product theory loses rate-free constants but not rate.

### 8.2 Name and objects

**Signed arithmetic criticality on the window tower and the complete family** — the theory of
nonnegative quadratic forms on growing intervals (archimedean Lévy–Khintchine part, signed folds of
lengths `log n` with weights `Λ(n)/√n`, one rank-two indefinite pole term, critical in the limit)
together with the complete family on `[1, N]` at overlap `c` (atoms, conductors, packets, charges),
and of the passage of positivity along length, conductor and overlap.

Objects: window modules over the truncated Dirichlet ring; collar classes; the involutions `σ_A`
and `R`; trivial-divisor moment sequences and the kernel `κ(x)`; frozen two-collar forms and the
Carathéodory disk; lattice Weil sequences, Schur parameters, zero modes with unimodular angles; the
pole as the hyperbolic pair `e^{±h/2}`; Tate functions and their jets; conductor packets, the prime
generator `G` and its derivation law, receiving charges, successor edges, divisor-jet squares; the
pencil `a_φQ(H) + (7J(1)/R)‖H‖²_{−8}` and its critical multiples; the signed theta source jets.

### 8.3 Questions it must answer

1. Which exact identity pays the mixed pairing `W(τ_εu, v)` of the growth law at every stage, with
   premises only on the shorter window?
2. Which term of the complete form pays the receiving charges that adjunction and physical energies
   erase, uniformly in conductor and overlap?
3. What is the Schur form of the conductor block against the coercive complement at the critical
   curve, as the cutoff grows?
4. What is the continuum canonical system of a bump (B41), and what replaces Allegretto–Piepenbrink
   for forms with a rank-two indefinite pole term?
5. What rank-uniform law governs the signed theta source jets?

### 8.4 Point of view and language

Positivity is an evolution along three axes (length, conductor, overlap), not a property: prime
powers are impulses, the archimedean place and the pole are the free evolution, charges are what
the evolution must carry. The language is that of canonical systems and Schur algorithms made
arithmetic, and of exact decompositions of the complete form with every boundary term retained.

### 8.5 Foundational principles

- Exactness where there is no slack: identities and equivalences of unbounded rank in the window
  and lattice forms; constants may be lost only where a receiver accepts them (fixed-spline
  growth, tensor loss).
- Signed: every fold enters with its sign; nothing Markov, nothing sign-blind.
- Charge retention: no passage to a limit that loses a receiving charge without accounting for it.
- Criticality: the extremal objects have zero margin; proofs are Liouville theorems, not spectral
  gaps.
- Locality and causality: a statement says which primes, lengths, conductors and overlaps it reads.
- Selection by positivity: the only weight surviving every stage is `Λ`; the theory must reproduce
  the degree gap and the strict Euler bound as consequences.

### 8.6 Criteria it must fulfil

1. Reproduce base positivity through `2·enlargedWeilFloorAperture`, the first prime stage, and
   subcritical PD below `1/8`.
2. Pay the pole's one negative square on every lattice and every window.
3. Be critical: margins tend to zero along every lattice; the ground state degenerates in the limit.
4. Deliver the two-site band at every scale, and the all-`K` conductor Gram.
5. Force `Λ` and fail for flips, Euler twins (including the positive twins of conductor `p²` with
   zeros at `3/4`), `ζ(s)ζ(s − ε)`, Epstein and golden data.
6. Use the functional equation and the Euler product together, with the strict Euler bound.
7. Calibrate over `𝔽_q`: degenerate windows are curve windows; a curve degenerates at its number of
   angles.

### 8.7 Research topics

- Exact charge accounting on the prime-charge families and their coprime fibres (§7).
- The Schur form of the conductor block at the critical curve; the capstone's dependency closure.
- The first-stage mixed-pairing bound and the odd unit window capacity bound (§4.1, §7).
- Mixed-pairing bounds at stages two and three (the weighted path `2, 3, 2` and the rational Hecke
  graphs of WTZ supply the arithmetic side).
- The rank-uniform theta source law (§5.6).
- The continuum canonical system of a bump (B41).
- The signed aggregate prime-blind cone (§3).
- Hankel forms at the trivial divisor: `|μ_1|² − Σ|μ_{−2k}|²` on collar classes (the Gamma symbol's
  Weyl law and the zero-free band `|ξ| < γ_1`).
- Explicitly outside: counts and Hodge index over `ℤ` as sign producers, Tate domination, Markov
  ground states, measure rigidity on the PM side, bounded PM reflections off `Re s = ¼`.

---

## 9. Response to the review in `astra.md`

Each claim was checked against the Lean statement returned by the corpus search.

| Review claim | Verdict | Action taken |
|---|---|---|
| The sector-forcing induction assumes its conclusion: `collar_antisymmetric_of_frozen_negative_even` / `_odd` take `hpos : ∀ G, IsWindowTest A G → 0 ≤ weilQuad G` with `windowLevel A = N + 1`, and conclude a strict inequality `∫_L(H+H∘R)² < ∫_L(H−H∘R)²`, not sector membership | Confirmed `[L]`: the proof begins `have hQ := hpos H hH` | The "Rosati forcing by induction" proposal and §5.1 are withdrawn; the exact growth law `window_nonneg_iff_contraction` is the statement of record, and the open step is the mixed-pairing bound with premises on the shorter window |
| Sharp constants are not compulsory: `riemannHypothesis_iff_splineOrbit_subexponential`, `riemannHypothesis_of_sublinear_tensor_loss`, `riemannHypothesis_iff_fixed_tensor_loss` | Confirmed `[L]` | §1.1 "two landings", §1.7(4), §2.3, §8.5 corrected: constants may be lost, rate may not |
| Two-site detection gives no minimizer at a prescribed aperture; the first-jump function was mislabelled sub-RH and mixed the conventions `R = lim c⁸/log N` versus `c = 2K(log N)^{1/8}` and `κ` (zero count) versus `a_φ` | Confirmed `[L/D]`; `criticalMultiple_exact` is stated with `c⁸/log N → K` and `a_φ = (∫φ)²/∫φ²`; `R₁(A)` is nonincreasing; `K₀` is aperture-independent | §4.5 rewritten; notation `a_φ`, `R`, `R*(H)` fixed throughout |
| `canonicalCriticalClock_energy_negative`: the equality face is eventually negative | Confirmed `[L]` | Added to §1.2 and §4.5(c) |
| `κ` is an element of `ℕ∞`; windows exhaust it by supremum; finite index means finitely many off-line zeros and *implies* Lindelöf | Confirmed `[L]`: `negIndex_zetaKernel = (rightZeros).encard`, `iSup_windowIndex`, `lindelof_of_negIndex_zetaKernel_lt_top` | §1.1 corrected |
| "One trivial direction, all others positive" suppresses the mixed pairings | Accepted `[D]` | §1.3 rewritten; the index-`≤ 1` remark added |
| The positive Euler twins have conductor `p²` and rule out the tested package, not every input | Confirmed `[L]`: `gammaData_conductor = p²` | §1.2, §1.7(2), §8.5–8.6 softened |
| A Bochner measure cannot have mass off the torus; the generalized representation needs finite index | Accepted `[D]` | §1.5 rewritten with `isKreinLanger_zetaKernel_iff_negIndex_lt_top` |
| `−ζ'/ζ` is not Herglotz on `Re s > 1` (counterexample at `t = π/log 2`) | Confirmed `[D]` | The Nevanlinna proposal is replaced by the growth-rate landing (§2.3) |
| The arithmetic frontier is charge retention: `exists_harmonic_neutral_physical_vanishing_charge`, `arithmeticPrimeGenerator_primeOnly_decomposition`, `primeCenteredGenerator_period_sq_le`, `normalizedPrimeModeSource_mul_of_coprime`, residual scale theorems, `divisorJetEnergy_eq`, `completeWeilEnergy_packetVector_at_every_overlap`, `prime_successor_edges_control_nonconstant_packets`, top-band joint cancellation | Confirmed `[L]` | New rows in §1.2; Proposal A (§2.2); §4.5(a); the one question (§7) |
| The capstone `exists_critical_multiple_completeWeilMatrix_posDef` exists in source, not dependency-closed | Confirmed `[S]`: present in `TheCompleteWeilMatrixIsPositiveAtACriticalMultiple.lean`, not imported by the umbrella | §1.2, §4.5(b), Appendix B corrected |
| `PrimeBlindPositive` quantifies over complex tests with a combined blind condition; the nonnegative reduction is conditional on `WindowPositive` | Confirmed `[L]`: `WeilTestFn` is `{f : ℝ → ℂ // C² ∧ compact support}`; `weilArchRe_nonneg_of_primeBlind (hW : WindowPositive)` | §1.4, §3 corrected |
| The theta signed-jet hierarchy is RH-equivalent and deserves a lane | Confirmed `[L]` (`ThetaCuspCenterMixedSignedJetCompleteness`, rank eight strict) | Added to §1.2, §3, §5.6, §6 |
| `exists_two_prime_rvm_prescribed_spline_divisor`: bounded two-prime coupling with exact counts and unattained width does not force zero width | Confirmed `[L]` | Added to §1.2 (coupling row) |
| The odd-window constant `3203/320` belongs to the reduced theorem; the unreduced one has `5123/320` | Confirmed `[L]` | §1.2, §7, Appendix A corrected; the capacity formulation `b·sup L²/R ≤ 1` adopted |
| The odd unit window is not established as the privileged entrance | Accepted | §6–7 reorganized: charge accounting first; the odd window kept as diagnostic |

Not adopted: nothing in the review was found to be wrong. One qualification: the review's priority
"joint arithmetic cancellation" is adopted as Proposal A and as the one question, but its landing
remains an RH-equivalent receiver; the sub-RH content is the residual classification on the explicit
families, which is what §7 asks.

---

## Appendix A — Facts used, with Lean anchors

| Fact | Anchor |
|---|---|
| RH ⇔ `|c_φ(t)| < Q(φ)`; RH ⇔ two-site PD; off RH an exactly degenerate two-site lattice | GWZ `riemannHypothesis_iff_abs_weilOrbitCorr_lt`, `riemannHypothesis_iff_two_site_posDef`, `exists_degenerate_lattice_of_not_riemannHypothesis` |
| RH ⇔ subexponential spline orbit; sublinear tensor loss ⇒ RH; RH ⇔ fixed tensor loss; linear loss = zero width | AOG `riemannHypothesis_iff_splineOrbit_subexponential`, `zeta_splineOrbit_rate_iff_zetaZeroWidth_le`; ACP `riemannHypothesis_of_sublinear_tensor_loss`, `riemannHypothesis_iff_fixed_tensor_loss`, `zetaZeroWidth_le_iff_linear_tensor_loss` |
| Growth law and stage disk; RH ⇔ every growth step contracts | CSTW `window_nonneg_iff_contraction`, `stage_nonneg_iff_disk`, `riemannHypothesis_iff_translation_contraction` |
| Kick = collar Rosati form; parity splitting; collar inequalities on a window already positive | GWZ `corr_eq_collar_windowInvolution`, `window_nonneg_iff_sectors`, `collar_antisymmetric_of_frozen_negative_even`, `collar_symmetric_of_frozen_negative_odd` |
| Transmission through the trivial divisor; closed frozen forms | CSTW `OrderedAt.integral_collarKernel_mul_eq_moments`, `frozenTwoCollar_eq_transmitted`, `firstStage_frozen_congr` |
| No count identity at the first prime | CWS `not_exists_countIdentity` |
| Index: orbit kernel, windows, finiteness | HKT `negIndex_zetaKernel`, `zetaKernel_finiteIndex_tfae`, `lindelof_of_negIndex_zetaKernel_lt_top`, `isKreinLanger_zetaKernel_iff_negIndex_lt_top`; CWS `iSup_windowIndex`, `windowIndex_lt_top`, `riemannHypothesis_iff_forall_windowIndex_eq_zero` |
| Weil's form = dimension-zero jet of counts; Tate positivity does not descend; Hecke similitudes scalar | WTZ `weilQuad_eq_tateJet`; DZG `tatePositivity_does_not_descend`, `windowRep_similitude` |
| Archimedean Tate domination closed | ATD `archimedean_tate_domination_complete_solution`, `riemannHypothesis_of_local_archimedeanTateDomination`, `not_exists_shiftedPole_weight_domination_linear` |
| Strict floor past `log 2` | ATD `weilQuad_ge_one_div_eightThousand_of_le_two_mul_enlargedAperture`; AIP `enlargedWeilFloorAperture_bounds` |
| Odd unit window | WTZ `weilQuad_add_reduced_first_moment_ge_mass` (`3203/320`), `weilQuad_add_first_moment_ge_mass` (`5123/320`), `weilQuad_ge_of_odd_two_moments_zero`, `exists_odd_unit_retainedGamma_neg_weil_pos`, `firstFold_linear_chord_exceeds_first_capacity` |
| Folded supersolution criterion and its origin-charge no-go | ACT `riemannHypothesis_of_foldedSupersolution`, `compact_positive_profile_origin_failure` |
| Second order at the critical curve; critical multiple; equality face; index resolves zeros; count ends at resolution | AHD `horizon_layer_criticalCurve_exact`, `criticalMultiple_exact`, `canonicalCriticalClock_energy_negative`, `canonicalCriticalClock_phase_diagram`, `exists_windows_resolving_rightZeros`, `exists_countRatio_le_half` |
| Whole space PD below `1/8`; critical-curve pieces; capstone | CACT `eventually_tiltedUnitSpline_completeWeilMatrix_posDef_below_one_eighth`, `exists_critical_multiple_weighted_far_complement`, `exists_critical_multiple_low_packet_and_collar_budget`, `exists_critical_multiple_schur_payment`; `exists_critical_multiple_completeWeilMatrix_posDef` `[S]` |
| Conductor Gram at every `2K(log N)^{1/8}` is RH; RH ⇔ Liouville along the overlap flow | HWV `riemannHypothesis_iff_conductorGram_nonneg_eighthRoot`, `riemannHypothesis_iff_liouville_along_the_overlap_flow` |
| Receiving charges, generator decomposition, derivation law, residual scales | CSAR `exists_harmonic_neutral_physical_vanishing_charge`, `exists_harmonic_neutral_arbitrarily_small_energy_charge`, `arithmeticPrimeGenerator_primeOnly_decomposition`, `primeCenteredGenerator_period_sq_le`, `normalizedPrimeModeSource_mul_of_coprime`, `exists_primeResidual_packet_relative_log_sq_le`, `eventually_coherentPrimeResidual_logarithmic_lower` |
| Complete-form decomposition; successor edges; divisor jet; top-band joint cancellation | ACoT `completeWeilEnergy_packetVector_at_every_overlap`, `prime_successor_edges_control_nonconstant_packets`; SSh `divisorJetEnergy_eq`, `exists_abs_jointTopCoefficient_le_uniform_overlap` |
| Prime-blind positivity ⇔ RH; conditional nonnegative reduction | RHTower `riemannHypothesis_iff_primeBlindPositive_unconditional`, `exists_weilPositiveFull_iff_primeBlindPositive`, `weilArchRe_nonneg_of_primeBlind` |
| Glued index `κ + 1`; successor + dilation ⇒ infinite index | AKG `negIndex_weilArchState_eq_rightZeros`, `negIndex_add_slope_eq_top_of_continuous_dilation` |
| Bounded cone coupling ⇒ RH or no deepest zero; abstract RVM divisor with unattained width | ACoT `riemannHypothesis_or_no_deepest_zero_of_bounded_coneCoupling`, `exists_two_prime_rvm_prescribed_spline_divisor` |
| Gauge exponents; RH ⇔ trivial point typical | AGT `ae_gaugeExponent_moebius_eq_half`, `moebius_exponent_one_residual_and_null`, `riemannHypothesis_iff_trivialPoint_typical` |
| Transverse energy `< 1` ⇔ RH; collided form second difference | AES `riemannHypothesis_iff_divisorTransverseEnergy_lt_one`; APol `collidedForm_second_difference` |
| PM exact Krein identity; Hecke = Mellin translation; Serre ≠ Krein reflection; defect `= 0` iff `Re s = ¼` | RIT `weilQuad_eq_completedKreinForm`, `lewisHeckeOperator_windowMellinPeriod`, `no_weil_isometric_krein_reflection_intertwiner`, `resonantLewisPeriod_coIsometryDefect_eq_zero_iff` |
| Degree gap; strong multiplicity one; positive Euler twins of conductor `p²` | SEL `degree_eq_zero_or_one_le`, `coeff_eq_of_critical_discrepancy`, `exists_positive_multiplicative_twin`, `not_fullClass`, `gammaData_conductor` |
| `D_win` ⇔ thin Planck shadows; double-log certificates; 8-way equivalence | CDG `logFreeNearLineWindowOccupancy_iff_thinPlanckShadow`, `almostAll_doubleLogStage_besselSzegoCertificate`, `criticalClustering_logMean_mollifier_hecke_tfae` |
| First cyclotomic band ⇔ RH | CAF `riemannHypothesis_iff_chebyshevFirstCyclotomicBand` |
| Theta: signed-jet completeness ⇔ RH; rank eight strict | RHTower `ThetaCuspCenterMixedSignedJetCompleteness`; TCS `thetaCuspCenterMixedSignedHankel_eight_posDef` |

## Appendix B — Work in progress relevant to this report

`docs/drafts/pipeline/1-in-progress/the-complete-weil-family-is-positive-at-a-critical-multiple.md`
(A30): whole-space positive definiteness of the complete family for `1 ≤ c ≤ 2K₁(log N)^{1/8}` at
one `K₁ > 0`. In Lean: the below-`1/8` theorem, the dyadic seventh-power top-collar reserve, the
log-free conductor residuals at `(log N)^{13/32}`, the deep-row pairing, the critical-multiple Schur
payment and the weighted far complement `[L]`, and the capstone
`exists_critical_multiple_completeWeilMatrix_posDef` assembling them `[S]` (in source, not imported by
the umbrella; the frontier map tags it `[S]`). Reading: it closes the eighth-root endpoint at small
multiples and starts the pencil index at zero; it is size-only (positivity at one multiple is
sub-RH); what it leaves is the all-`K`, all-vector conductor Gram, whose attack is §2.2 and §7.
