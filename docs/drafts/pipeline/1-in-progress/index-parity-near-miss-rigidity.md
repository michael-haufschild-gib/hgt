# Index and parity rigidity: the near-miss programme

- **ID:** `index-parity-near-miss-rigidity`
- **Stage:** 1-in-progress
- **Parent programme:** `source-contraction-two-volterra-domination` (Class-C exploration)
- **Type:** OWN CONJECTURE PROGRAMME / rigidity between zero-density and RH
- **RH status:** the headline conjecture C8 is strictly weaker than RH and strictly beyond all
  refereed literature; nothing on this card restates RH.

## The index dictionary (exact)

Let κ_T := the maximal number of negative eigenvalues of a finite section
`[B(w_j, w̄_k)]` of the theta-tail Bezoutian with `|Im w_j| ≤ T`, and κ := sup_T κ_T.
Through the spectral expansion (each on-line zero contributes a rank-one PSD Cauchy square
`1/((w−iγ)(v̄+iγ))`; each off-line quadruple contributes two negative squares, one per
right-half centered zero):

**κ_T = N_off(T)**, where N_off(T) counts off-line zeros with ordinate in (0,T) individually
(each same-height off-line pair {β, 1−β} yields two right-half centered zeros ρc, ρ̄c, hence two
negative squares — checked on the model quartic (w²−ρ²)(w²−ρ̄²), whose logarithmic derivative
has Pick index 2 = its right-half zero count; Hurwitz-stable P give P′/P positive-real, index
0), and κ = N_off.

The ladder, with owners:
- κ_T ≤ 0.583·N(T): known — Levinson–Conrey–Pratt et al. proportion bounds `[LITERATURE]`.
- κ_T = o(N(T)) ("almost all zeros ON the line"): open. (Bohr–Landau gives almost-all only in
  every strip |β−1/2| < δ, not on the line.)
- κ < ∞ ("all but finitely many on the line"): open, beyond all literature.
- κ = 0: RH (the corpus receiver).
- Stability: κ_T is invariant along the tilt family `(e^{cw}ξc)′` up to the Levinson–Montgomery
  `O(log T)` bookkeeping; the finite-section index is exactly c-independent (the Bezoutian is
  c-free; Lean congruence in `ThetaTailKreinXiCentTiltCollapse`). Nested sections have
  nondecreasing negative index (corpus: finite generalized-Schur inertia layer).
- Corpus ownership of the finite dictionary: multiplicity-aware finite Krein–Langer
  (`finiteBlaschkeGeneralizedSchurKernel_exactNegativeSquares` and companions),
  `xiShiftFiniteGeneralizedSchur_exactNegativeSquares`, SV2's finite-or-infinite leakage rank.
  Structure theory for the infinite finite-index case: Pontryagin de Branges spaces
  (Kaltenbäck–Woracek Π_κ theory) `[LITERATURE, structure only]` — no zeta application asserting
  rigidity located in refereed sources (searched 2026-08; one unrefereed 2026-era Academia.edu
  document claims the statement — treat as unverified, see audit note below).

## C8 [CONJECTURE] — near-miss rigidity

**Either κ = 0 or κ = ∞: RH cannot fail finitely often.** Four equivalent forms (derived, exact):

1. `N_off ∈ {0, ∞}`.
2. `h = ξc′/ξc` does not belong to the generalized Nevanlinna class `N_κ(ℂ₊)` for any
   `0 < κ < ∞` (Krein–Langer).
3. No factorization `Ξ = Q·Ξ̃` with `Q` a nonempty finite product of real quartics positive on
   `ℝ` (one per off-line quadruple: `Q_ρ(τ) = (τ²−ρ²)(τ²−ρ̄²)`) and `Ξ̃` real-rooted entire.
4. No identity `Φ = Q(−i∂)·Φ̃` with `Φ̃` the density of a real-rooted transform: the theta
   density satisfies no nontrivial finite-order ODE-relation onto the Laguerre–Pólya cone.

**Consequence mining under ¬C8 (the compactness resource):** if `0 < κ < ∞` then all
almost-all zero machinery upgrades to all-but-finitely-many; Lindelöf-type consequences follow
as in the RH ⟹ LH argument (finitely many exceptions are height-harmless); and every corpus
schedule receiver (FCRJ, RBH channels) acquires an anomaly that is EXACTLY a nonzero Bohr
almost-periodic polynomial with κ frequencies and explicitly computable amplitudes — a finitely
parametrized object. Refuting C8's negation = refuting one finite-frequency trig polynomial
against source-side facts.

## The counterfeit boundary (what a proof MUST use)

`[FALSIFIED for the bare analytic class]`: take two real zeros `±γ₁, ±γ₂` of `Ξ` (Hardy) and any
non-real `ρ` off the axis; then

`Ξ_fake(τ) := Ξ(τ)·(τ²−ρ²)(τ²−ρ̄²)/((τ²−γ₁²)(τ²−γ₂²))`

is entire, even, real, order one, satisfies every FE/reality/passport constraint, and has
exactly one off-line quadruple, hence **κ = 2 exactly**. So C8 is FALSE in the class {even real order-one entire,
FE-real, Hadamard-genus-one}: any proof must use the arithmetic (Euler orbit / Dirichlet
coefficients), which the relocation does not preserve — the fake's "zeta" has no Euler product.
This also calibrates any claimed short proof (including the unrefereed 2026 document): if it
never uses arithmetic beyond the functional equation, it proves the false statement above.
Corpus parallel: the window-jet relocation machinery already builds positive-density off-line
counterfeits with identical passports; this is its κ = 1 specialization.

## Attack surface A [live]: Bohr recurrence against positive-density one-sided bounds

Finite spectra are rigid in a way infinite spectra are not: a nonzero Bohr polynomial with κ
frequencies has syndetic sublevel sets whose densities are exact torus measures (Weyl on `𝕋^κ`),
it recurs to its sup/inf with bounded gaps, and it cannot tend to zero or hold an eventual sign.
So C8 follows from any ONE unconditional source-side inequality of the shape

  "carrier ≥ −ε on a set of log-scales of density > 1 − η(κ, amplitudes)"

paired with the exact finite-κ anomaly formula forcing "carrier ≤ −δ on a torus-measured
positive-density set". For κ = 1 the bad set has density exactly 1/2 — one-sided bounds past
half density are the crux, and this is verbatim the T2 lane's open frontier ("signed subhalf
continuation"; "exponential overregularization past half density is impossible"): T2's subhalf
receiver is exactly where single-frequency witnesses die. The RBH terminal analysis
(separated-sign geometry complete through continuum cardinality; odd Bohr channels have cofinal
zeros and both signs) is the corpus's finite-vs-infinite frequency classifier and should be the
first machinery consulted. First concrete question: which corpus carrier has BOTH an
unconditional positive-density one-sided bound AND sensitivity to a single off-line quadruple's
Bohr term at matching normalization? (The CCM-FU PNT carrier tends to zero unconditionally but
is exceptional-insensitive at that normalization; the FCRJ zero-floor is exceptional-sensitive
but has no unconditional one-sided bound. The gap between these two is the exact target.)

## Attack surface B [live]: the function-field/Perron–Frobenius template (C9)

The FF proof of RH is an index theorem: the intersection form is Lorentzian (positive index 1 —
Hodge index) and Frobenius preserves the ample cone; Perron–Frobenius-in-Lorentz-space then
pins the eigenvalues. The number-field slots, all corpus-present but unwelded:

- Lorentz structure: SC's source-built all-prime Krein form has EXACTLY one negative square per
  left fibre modulo its radical (corpus, map §SC) — a source index-one object.
- Cone-preserving arithmetic operator: `Z = Σ n^{−1/2} S_{log n}` is manifestly
  positivity-preserving on the half-line (positive coefficients, forward shifts) — the
  "Frobenius" slot; Lean-adjacent via the orbit factorization module.
- Missing weld `[OPEN CORE of C9]`: an exact identity presenting the Weil/Bezoutian form as the
  Perron–Frobenius complement of `Z`'s action on an SC-type Lorentz fibre — so that
  cone-preservation + index-one forces the spectral confinement, instead of assuming it.
  This is a construction target, not a receiver: PF simplicity of a positive operator's leading
  eigenvector is an unconditional index-one rigidity, the exact mechanism class the FF proof
  uses. Risk to retire early: if the weld exists only with target-fed data, it collapses into
  the known receiver web — test on the two-atom truncation first, where everything is explicit
  and the off-axis zero (Lean witness `xiCentTwoAtomTruncation_witness_zero`) must appear as a
  cone-boundary phenomenon for the finite operator `1 + 2^{−1/2}S_{log 2}`.

## Killed in this exploration (with reasons)

- Shift-orbit amplification of one negative direction to infinitely many (would prove the 0/∞
  dichotomy abstractly): FALSE route — the half-line truncation adds the window term
  `∫_{−a}^0(|K₊|²−|K₋|²)` with no fixed sign; packets are not shift-stable.
- Abstract Toeplitz/Smirnov dichotomy ("meromorphic frame multiplier ⟹ index 0 or ∞"):
  FALSE — Krein–Langer classes S_κ realize every finite κ. Surviving structure (not proof):
  the closed two-Volterra graph is single-valued iff no strip poles; with poles the closure's
  multivalued part is a Beurling shift-invariant (hence infinite-dimensional) subspace.
- Pontryagin symmetry-compression ("finite negative subspace must carry an infinite symmetry"):
  the honest symmetry group of the form is only (ℤ/2)² (evenness, conjugation) — admits finite
  representations; the c-flow permutes realizations, not the form. No leverage as stated.
- Determinant-sign mod 2 of sections: equals off-line counting mod 2 — receiver.

## Queued exact bricks (Lean-able, unconditional)

1. Finite-section index is c-independent and nondecreasing under node nesting (assemble from
   the existing congruence + corpus inertia layer; near-trivial, worth stating once).
2. The κ = 1 counterfeit as a formal object (order/FE/reality preserved, one quadruple):
   fixes the counterfeit boundary in Lean; the corpus relocation machinery likely makes this
   short.
3. For C9: the two-atom PF test case — spectrum/cone analysis of `1 + 2^{−1/2}S_{log 2}` on
   the half-line against the Lean witness.

## Loop log

- 2026-08-28: card opened after full exploration; C8 frozen with four forms + counterfeit
  boundary; attack surfaces A (Bohr-vs-subhalf) and B (PF/Lorentz weld, C9) named with their
  first tests; kill-list recorded. External audit: refereed literature empty on C8; one
  unrefereed claim flagged unverified; Π_κ-dB structure theory available (Kaltenbäck–Woracek).

## Two-atom PF cone test — executed 2026-08-28 (verdict: weld retired, index residue extracted)

Exact analysis + finite-section numerics (`computations/2026-08-28-two-volterra-domination-loop/
pf_test.py`, `pf_check.py`). Setup: `Z₂ = I + q·S_{log 2}`, `q = 2^{−1/2}`, on `L²(e^{2βs}ds)`;
`‖S_a‖_β = 2^β`; co-shift Laplace-frame-diagonal with symbol `1 + 2^{−1/2−w}`.

**Qualitative PASS — the Lean witness is exactly a cone/index boundary phenomenon:**
- Zeros of the symbol = (critical weight `β = 1/2`, where the cone radius `q·2^β` reaches 1) ×
  (anti-Perron peripheral direction `e^{−aw} = −1`), giving `Re w = −1/2`, ordinate lattice
  `π(2k+1)/log 2` — the witness `w₀ = −1/2 + iπ/log 2` is the anti-Perron point at critical
  weight, diametrically opposite the Perron eigenvalue `1+q` (positive constant direction).
- The weight transition is a Fredholm/winding index jump. Finite sections show the three
  predicted regimes exactly: `β < 1/2`: smin → `1 − q·2^β` (measured 0.13124 → limit 0.1294);
  `β = 1/2`: smin ∝ 1/N (measured halving per doubling), soft space m-fold degenerate
  (0.04832749… with multiplicity — one soft mode per stride class = the discretized zero
  lattice), carrier = stride-2m alternation (block-mean sign pattern −1,+1,… with slow
  envelope) = continuum frequency `π/log 2`; `β > 1/2`: exponential collapse with
  m-dimensional approximate kernel (index-jump regime).

**Mechanism-power FAIL — C9's weld retired as a producer, three exact reasons:**
1. For the full `Z = Σ n^{−1/2}S_{log n}` the cone/Neumann disc gives only the trivial region
   `Σ_{n≥2} n^{−σ} < 1 ⟺ σ > s*`, `ζ(s*) = 2` (`s* ≈ 1.7286`) — weaker than elementary
   zero-free regions. The two-atom exactness is a single-shift accident: there the spectrum IS
   the full disc, so the disc bound is sharp only there, and the cone constrains no peripheral
   direction (vacuous PF periphery).
2. The operative cone positivity of zeta lives one level up — `Λ(n) ≥ 0` at the log-derivative
   plus 3-4-1 — which IS the classical zero-free region; the PF frame adds nothing to it.
3. **Bohr-denseness no-go (structural, decisive):** on every vertical line of the strip
   `inf|ζ| = 0` (Bohr almost-zeros), so `0 ∈ σ` of every fixed-weight Wiener–Hopf realization
   unconditionally — no spectral-membership/invertibility criterion at fixed weight can express
   RH. Spectral-set frames are structurally incapable; only jump/index/eigen-defect data
   (responding to actual zeros, not almost-zeros) can carry RH content.

**Positive salvage:**
- The weight-indexed Fredholm index `β ↦ ind(WH(ζ-symbol, weight β))` jumps exactly at off-line
  zero abscissas: RH ⟺ the index function is constant on `(0, 1/2)`; finite total jump budget
  ⟺ C8's finite κ. Attack surface B folds back into the index programme — its correct residue
  is the index-jump locus, not PF invertibility.
- Bohr-robustness of the index/section frame is now demonstrated concretely — validating the
  Class-C representation against the operator-spectrum alternative.
- Lean-able bricks queued: the two-atom winding/index-jump statement (winding of
  `1 + q·2^β·e^{−iθ}` jumps at `q·2^β = 1`; elementary) alongside the existing witness theorem.

## Attack surface A — first assault (2026-08-28): two halves closed, the third specified exactly

**Formalized survivors (unconditional, axioms standard):**
- `HTGeometry/HerglotzPoleIndexAnchor.lean` — the generic index dictionary anchors:
  `re_one_div_sub` (Cauchy-atom real part = abscissa gap over squared distance),
  `re_one_div_sub_neg_iff` (each right-half pole is detected by a strictly negative rank-one
  Carathéodory diagonal at every node left of its abscissa), `re_lhpPoleSum_nonneg`, and
  `isPSDKernel_lhpPoleSum` (stable pole configurations carry no negative squares — the
  index-zero half of κ = N_off), assembled on the corpus's
  `isPSDKernel_halfPlaneCaratheodory`.
- `RHTower/ThetaTailKreinTiltSectionAnchor.lean` — the sesquilinear section identity
  `2c(w+conj v)·B = tilt₊·conj tilt₊ − tilt₋·conj tilt₋` and `tiltGram_param_uniform`
  (Gram differences at two tilt parameters are exact mutual rescalings: section inertia is
  parameter-free).
- `HTGeometry/CosineSublevelPeriodMeasure.lean` — the Bohr-negativity measure core:
  `cos_sublevel_period_eq` ({cos ≤ −1/2} within a period is exactly the middle third) and
  `volume_cos_sublevel_period` (= 2π/3): a single-frequency mean-zero anomaly spends exactly
  one third of every period at depth half its amplitude. Queued bookkeeping: periodization to
  the density statement on [0,U]; the general-κ L²/L∞ negative-density lemma
  (density ≥ 1/(8κ) at depth ‖A‖₂/(4√(2κ)) — proof recorded here: mean-zero + Parseval +
  ‖A‖∞ ≤ √(2κ)‖A‖₂ + Markov).

**The anomaly law (paper-exact, unconditional inputs only):** under finite κ with top abscissa
β, `(ψ(e^u) − e^u)·e^{−βu} = A(u) + E(u)` where `A` is the exact κ-frequency Bohr polynomial of
the exceptional zeros and `density{|E| > δ} → 0` — using only the explicit formula and
`Σ 1/|ρ|² < ∞` (windowed Chebyshev on the Besicovitch mean square; the on-line background dies
in density under the `e^{−(β−1/2)u}` normalization). So finite-κ ⟺ the normalized prime
fluctuation converges in density to a nonzero finite Bohr polynomial — **C10**, the distilled
minimal target: refute that convergence for every β > 1/2. C10 ⟸ any unconditional one-sided
carrier bound at density > 2/3 (κ=1; > 1 − 1/(8κ) generally); C10 ⟹ C8.

**Audited carrier failure map (why each natural candidate misses):**
ψ-direct one-sided at scale x^β — RH-strength (no unconditional second moments); quadratic /
energy carriers — anomaly enters squared, blind; manifest Λ ≥ 0 monotonicity — main-term
dominated, kills only β = 1 (attack A at β → 1 IS the classical zero-free-line mechanism);
S(T) — exceptional-insensitive (O(1) jumps per zero); Littlewood/log|ζ| line-means —
non-discriminating (both κ = 0 and finite κ give bounded integrals; keep the clean receiver:
`∫₀^T log|ζ(σ₀+it)|dt = O(1) ⟺ finitely many zeros right of σ₀`); Odlyzko-style positive-test
explicit-formula budgets — spent by on-line zeros, no finite-κ gain.

**Landing.** The missing third piece — an unconditional positive-density one-sided prime-side
bound at sub-main scale against a fixed known frequency — is exactly the corpus's
signed-incidence frontier (T2 "signed subhalf continuation", E-lane sign supply, D2 windows),
with a new consumer relation: those lanes' PARTIAL goals suffice for near-miss rigidity before
their full goals are reached, and the target frequency being fixed/known permits Diophantine
window tuning unavailable to the full lanes. Next cycle: mine the proved T2/E layers for any
statement meeting the spec (one-sided, density > 2/3, sub-power scale, fixed frequency).
