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
