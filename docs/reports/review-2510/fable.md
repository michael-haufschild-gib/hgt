# Fable review (2026-10-25): walls, mechanisms, focus questions, and the field that would be needed

Status: written against the working tree of 2026-10-25 (committed snapshot `93e83b0bb` plus uncommitted
work). Evidence: the six ledgers and twenty programme READMEs named in the brief, read in full, and about
twenty-five queries with `scripts/formal_tools.py research`, recorded in
`logs/fable-review-2510-research-log.md`. No compilation, no axiom audit, no web.

Labels follow the frontier map: [L] reachable from a package umbrella, [S] source not reached by an
umbrella, [U] uncommitted source present in the working tree. A receiver is an RH-equivalent reformulation
and is never a producer of its input. Statements marked *(proposal)* are mine and are not theorems.

Companions: [frontier map](../rh-current-frontier-map.md), [killed routes](../rh-killed-routes.md),
[route unification](route-unification-ledger.md), [hard obstacles](hard-obstacles.md),
[walls ledger](walls-ledger.md), [what forces blindness](what-forces-blindness.md).

---

## 0. Where the frontier is, in one paragraph

Every unconditional positivity theorem in the corpus is positivity on a carrier blind to off-line zeros,
and for the single-channel class this is now a theorem [L]: every sharp-stable right convolution ideal of
the Meyer source with nonnegative trace lies in the maximal blind ideal
(`isGreatest_meyerSharpPositiveIdeal`), and every scale-shift-invariant Weil-nonnegative test space is
blind (`zeta_blindOffLine_of_scaleShift_subspace_weil_nonneg`). The maximal blind ideal equals the whole
source iff RH, with no simplicity condition. The only proved *forcing* law is multiplicative: coupling the
dilated channels `n^{-ikt} = (n^{-it})^k` with `Λ ≥ 0`, a simple pole, no harmonic poles and integer zero
orders forces `ζ(1+it) ≠ 0` (`harmonic_quantized_zero_vanishing`) [L]; with growth input it reproduces the
de la Vallée Poussin, Littlewood and Vinogradov–Korobov regions, and its next rung is a fixed zero-free
strip, which is also the first rung of every graded cancellation receiver (face 1.0). The three walls are
the rate reading (W1), the transfer reading (W3) and the carrier reading (W14) of one sentence: *what
forces the actual arithmetic source to be blind to off-line zeros?*

I take this picture as established and do not re-derive it. What follows is what I can add.

---

## 1. A wall face that appears to have fallen: 14.12 (completeness of invariants)

The walls ledger lists face 14.12 as *New/Open*: "uniqueness for FE + Beurling Euler positivity + simple
pole, or a countermodel with an off-line zero (Q2)". The route-unification ledger makes this its U3 bridge.

The working tree contains an untracked module [U, S]
`formal/GaloisForLFunctions/HTGeometry/BeurlingRiemannFunctionalEquationRigidity.lean` (no importer, no
`sorry`/`axiom` found by text search, not compiled by me). Its final theorem,
`beurlingSystem_rigidity_of_completed_functional_equation`, states: for a countable Beurling system `B`
(free commutative monoid on prime labels of norm `> 1`) whose generalized zeta satisfies Riemann's
degree-one completed functional equation in Hamburger's form (reflection with `Γ_ℝ`, correction terms
`α Γ_ℝ(s) + β Γ_ℝ(s−1)`, remainder `E` holomorphic on the strip `(−1/2, 3/2)` with `1/(1+t²)` decay),

- `α = −1/2`, `β = 1/2` (the simple pole is forced, not assumed; no entire degree-one Beurling Euler
  product exists);
- every generalized integer has a positive-integer norm and every positive integer occurs exactly once;
- `beurlingZeta B = riemannZeta` on `Re s > 1`;
- the labels are in norm-preserving bijection with the rational primes.

The mechanism is a **Fejér-tent spectral gap identity**: the theta relation with arbitrary complex
coefficients `a_n` on frequencies `λ_n ≥ 1` forces `Σ a_n (sin πλ_n / πλ_n)² = −(α+β) = 0`; with
`a_n ≥ 0` every active frequency is an integer, and the ordinary Hamburger theorem (already [L],
`HamburgerFunctionalEquation`, `HamburgerGeneralFrequencies`) finishes.

**Consequences, if the module audits.**

1. Q2 is answered positively and more strongly than asked: the functional equation alone, on a Beurling
   system, forces `ζ`. Euler positivity enters only through the nonnegativity of integer counts; the simple
   pole is a conclusion.
2. The countermodel battery can never refute a forcing proposal that uses Riemann's full functional
   equation together with the Beurling (free-monoid) structure. Every surviving countermodel in the corpus
   (golden datum, double-pole and periodic-pole Beurling models, over-regular systems, shifted pairs,
   `Γ_ℝ^d` abundance for `d ≥ 3`) fails this combination, and now provably must.
3. The "axiomatic Weil" strategy — prove an RH-type theorem for a *class* of systems satisfying axioms —
   has no room at degree one: the class defined by {degree-one FE, Beurling structure} is `{ζ}`. A general
   class exists only with a weaker FE (the `Γ_ℝ^d` families with their proved abundance) or without the
   free-monoid structure (Selberg-class-type coefficient axioms). Any proof must therefore use features
   specific to `ζ`, exactly as the maximality theorem already said for positivity.
4. Methodologically, this is a *rigidity* theorem of the shape positivity + exact self-dual identity ⇒
   lattice quantization. It is the same shape as the Re s = 1 forcing law (positive-definiteness + integer
   values ⇒ character on a subgroup). I return to this shape in §4.

**Caveats.** [U, S]; I did not compile it; the Hamburger hypothesis on `E` (holomorphy on the strip with
quadratic decay) is part of the statement and must stay visible when the result is cited as "FE".

---

## 2. Question 1 — a new mechanism that circumvents the walls?

### 2.1 Verdict

No. I found no mechanism that reaches RH strength, a fixed zero-free strip, or any statement between
Vinogradov–Korobov and a strip, and I found no selection, transfer or realization theorem that the corpus
lacks and that current mathematics supplies. What I can offer is sharper than "no": a precise statement of
which structural classes the exhaustion theorems cover, three directions that lie *outside* those classes
and are not contradicted by any no-go in the catalogue, and two directions I tested and closed myself.

### 2.2 What is exhausted, stated as classes

| Class of mechanism | Exhausting theorem | Face |
|---|---|---|
| Quadratic positivity on a sharp-stable convolution ideal along the scaling flow (single channel) | lies in the maximal blind ideal [L] | 14.10 |
| Quadratic positivity on a scale-shift-invariant test space | blind [L] | 14.10 |
| Finite-degree harmonic (multiplicative) coupling by a nonnegative cosine polynomial | Fejér barrier `a₁ < 2a₀`; interior needs growth input; next rung is a strip [L] | 14.11, 1.0 |
| Finitely many linear readings, with or without mass | cannot supply Bézout [L] | 3.1, 14.4 |
| Positive exponential aperture floors; permanently frozen prime families | impossible / eventually negative [L] | 1.13 |
| Eventual all-height phase saving | refuted; bad phases recur syndetically [L] | 3.14 |
| PSD + dilation + antipodality as escape exclusion | white noise satisfies them [L] | 3.2 |
| Finite-dimensional affine-unitary (successor + dilation) carriers | trivial [L] | 14.1 |
| Counting-based heat repair | configuration-blind (order `R/N`, detector needs `δ²/log t`) [L] | 1.14 |
| Beurling countermodels against FE-complete methods | none exist [U, §1] | 14.12 |

Everything a route can still do must leave at least one of these classes. The three openings below do.

### 2.3 Openings outside the exhausted classes

#### Opening A — rank-two multiplicative positivity (the two-prime Bochner problem) *(proposal)*

**Facts [L].** RH holds iff, for two distinct primes `p, q`, the prime-side Weil Gram of the translates of
the cubic spline `B` by every finite set of shifts `k log p + l log q` has no negative square
(`riemannHypothesis_iff_splineTwoPrime_negIndex_eq_zero`). A single tower can be Toeplitz-blind to an
off-line configuration (`exists_symmetric_wolff_toeplitz_blind_configuration`); two primes recover the
full defect. On the boundary line the only proved forcing is a *rank-one* positive-definiteness statement:
the boundary divisor `D(u)` is an even positive-definite function on `ℝ`, integer-valued with `D(0) = 1`,
hence a `±1` character on a subgroup, hence `δ₀` for `ζ` (MPG, [S]). MPG lists "multi-frequency profiles:
joint positive definiteness on subgroups of rank `≥ 2`" as open and notes it adds nothing *on the
boundary* for `ζ`.

**Reading.** Set `c(k,l) = Re W(B, B(· − k log p − l log q))`. The two-prime theorem says RH iff `c` is a
positive-definite function on the group `ℤ log p + ℤ log q ≅ ℤ²`. By Bochner on `ℤ²`, that is iff `c` is
the Fourier transform of a positive measure on the two-torus `T²`. The zero side computes that measure:
each critical zero contributes a point mass at `(γ log p, γ log q) mod 2π` on the Kronecker line of `T²`;
an off-line zero contributes an exponential, not a character, so positivity fails. The prime side computes
`c(k,l)` as the archimedean term minus a *finite* von Mangoldt sum over the window
`|log n − |k log p + l log q|| ≤ 2a`: `c` reads the primes near the `{p,q}`-units `p^k q^l`. So RH is a
positive-definiteness property of the prime distribution around the `S`-units of a two-element `S`, and
rank one (one prime) is provably insufficient while rank two is sufficient.

**Why this is outside the exhausted classes.** It is a Bochner statement on a rank-two group, not a
quadratic form on a convolution ideal of the one-parameter scaling flow (the translates by `ℤ log p +
ℤ log q` form a dense but non-closed sub-semigroup; the maximality theorem is about `♯`-stable ideals
under the full flow). It is also not finite-degree harmonic coupling (which is rank one in the height
variable). The two positive-definiteness structures of the corpus — MPG's in height, AOG's in scale — are
Fourier dual to each other through the explicit formula.

**What it does not do.** Positivity on a finite box of `ℤ²` is a finite Toeplitz-block condition at a
bounded aperture and has width resolution `1/2` (SSIC). The hope is not an estimate but a rigidity law:
what does joint positive-definiteness on `ℤ²`, together with the integrality of zero orders, force that
rank one does not? On the boundary line the answer is "nothing" (`D_ζ = δ₀` already); the interior analogue
is the open question. The rank-two Fejér barrier (the maximal value of a fixed Fourier coefficient of a
positive measure on `T²` with prescribed others) is computable and has never been computed in the corpus.

#### Opening B — an integer-quantized interior budget *(proposal)*

**Facts.** Both working mechanisms in mathematics rest on the same shape: a positive source (point counts
over `𝔽_q`; `Λ ≥ 0`), an integer-valued controlled quantity (`h⁰`; the zero order `m`), and a rigid
normalization fixing the scale (degree and genus through RR; pole residue `1`). The step that produces
information is "an integer strictly below `1`, or strictly between the budget and twice the budget, is
`0`" (`a₁ m ≤ a₀ < a₁ ⇒ m = 0`; RR gives `h⁰ ≥ 1` once `deg > 2g − 2`). Over `ℤ` the corpus has proved
that the natural Euler characteristic is **not** integral: the box defect `E(s) = e^s + s − 1 − ψ(e^s)`
equals degree minus log torsion, `E(log N) = (N−1) − log #(ℤ/Q_N ℤ)`, and takes the value `½ + log(3/2)`
(`no_dimension_model_for_boxDefect`, BG) [L]. The corpus has many integer invariants of the zero set
(multiplicities; `D` even; collision mass even; sign-change index even; cofactor index finite or continuum,
never countable; Hecke-cycle lattice of infinite rank with no numerical relations) but no inequality in the
strip in which one of them enters linearly against a budget it could exceed.

**The opening.** Find the quantized budget at the critical line. Candidates that are integers or logs of
integers and are tied to the source rather than to the zeros: the torsion orders `#(ℤ/Q_N ℤ) =
lcm(1..N)/N`; the finite-horizon affine quotient (`1 + (N+1)(N+2)/2` operators, BG); the orders of
Kronecker characters in the Bohr polydisk (the rank-one escape classification already forces magnitudes
`p^{-s}`, `s ≥ ½`, and multiplicative signs, ADR). The target statement has the shape "the negative index
of the Weil form at aperture `a` is at most `(continuous quantity) < 1`", using the parity `D ∈ 2ℕ` so that
`D ≤ 1` suffices. I have no candidate inequality; I record the shape because it is the one shape that has
ever forced anything, and because the corpus has never tried to write the strip analogue of
`a₁ μ_zero(t) ≤ a₀`.

**Why outside the exhausted classes.** Quantization is not a quadratic-form estimate and not a finite
cosine coupling; the no-gos of the catalogue (KR-WIP: Witt integrality is not purity; KR-INT: finite-rank
integral Frobenius lattices fail) exclude integrality *of counts* as a selector but do not exclude an
integer-valued inequality whose integer is a *zero order*. The boundary-line law is exactly such an
inequality.

#### Opening C — non-commutative carriers (successor and dilation jointly) *(proposal)*

**Facts [L].** The maximality theorem concerns ideals of the *commutative* scaling flow. The successor is
the one structure of `ℤ` that Beurling systems lack (BVI, SSA), and only Bézout-selective (Class III) laws
can carry new information (THIM). BG proves the finite-horizon affine semigroup (`D_a U = U^a D_a`) has
scalar joint commutant, indecomposable invariant subspaces, and that continuous finite-dimensional
affine-unitary carriers are trivial (`finite_affine_unitary_rigidity`). SSA proves the successor gives exact
density-scale laws (one-third floor, quantized deficits), not square-root ones.

**The opening.** A positivity principle for the Weil form read as a positive functional on a *-algebra
generated by both ring operations — an infinite-dimensional, non-unitary or non-finite representation of
the affine semigroup `ax + b` over the integers, with the von Mangoldt source as a state. The classical
object with these symmetries is the Bost–Connes system (the Hecke C*-algebra of the `ax+b` semigroup over
`ℚ`), whose phase transition sits at `Re s = 1` — the same line where multiplicative forcing works — and
whose symmetries are quantized by roots of unity. The corpus has no Bost–Connes material (searched: only
abelian zeta-gas KMS states and finite KMS normalizations). I cannot say this carries the sign; I can say
it is the only class of positivity principle for which no corpus no-go applies and which uses the
successor non-trivially.

**Test it must pass first.** Produce, in the finite affine quotient of BG, a positive functional that is
*not* a quadratic form in the test and whose restriction to the dilation subsemigroup is the Weil form on
a finite set of translates; then show it fails on the golden datum. If no such functional exists at finite
horizon, the opening closes.

### 2.4 Openings I checked and closed

- **Complex damping and the three-lines theorem.** The receiver energy `E_T(ε)` is a sum of
  `|analytic in ε|²`, hence log-subharmonic in complex `ε`; the corpus has a three-lines mean-square
  convexity theorem (`integral_normSq_le_of_three_lines`). "Both ends paid" (`E_T → Σ 1/(n(n+1)) ≤ 1` as
  `ε ↓ 0`, bounded at `½`) tempts a maximum-principle argument on the strip `0 < Re ε < ½`. It fails for
  a reason worth recording: the exact identity `A_0 ≡ 1` holds only at the single real point `ε = 0`; at
  `ε = iτ`, `τ ≠ 0`, the receiver reads `Σ_j ∏_{p|j}(1 − p^{-iτ}) − n/ζ(1+iτ)`, whose growth exponent is
  `Θ`. The left boundary of the strip carries the whole width problem, and interpolation reproduces the
  trivial exponent. The corpus already proves the sharp form on the imaginary axis
  (`exists_pmComplexDampedFermiSource_imaginary_memLp_iff_zero`: zero is the only admitted imaginary
  damping near the origin). Closed.
- **Total positivity grading.** Log-concavity of Riemann's `Φ` is `PF₂`; real-rootedness of `Ξ` is the
  `PF_∞`/Laguerre–Pólya endpoint. The corpus kills log-concavity as an exclusion tool and already carries
  the grading by Jensen degree and heat time, with the same residual region (bounded height × small heat).
  Intermediate `PF_k` conditions are the Jensen/Turán hierarchy, already present. Nothing new.
- **Selection by self-reference.** At the ordinate `γ₀` of a hypothetical off-line zero the prime phases
  are not generic: the partial sums `Σ_{n≤X} Λ(n) n^{-ρ₀}` carry a `−m log X` drift. Using this to show
  `γ₀` is not a bad frequency for the averaged positivity theorem collapses to the explicit formula (the
  drift *is* the zero's contribution). Closed, unless an independent prime-side estimate at `γ₀` exists,
  which is W1 again.

---

## 3. Question 2 — the three questions to focus on

Criteria: not RH-equivalent as stated; graded deliverables that are theorems about the source, not about
the zeros; uses structure outside the exhausted classes or at the one place where quantitative unconditional
progress has a scoreboard; feeds several routes.

### Focus 1 — Rank-two multiplicative positivity with quantization

**Question.** What does joint positive-definiteness of a function on `ℤ²` (two incommensurable prime
scales), together with integer-valued zero orders and the simple pole, force on the divisor of `ζ` — on the
boundary line, in the interior with growth input, and in the limit of growing boxes?

**Why.** It is the minimal structure outside both proved mechanisms: rank one is provably blind (Wolff),
rank two provably decides RH (two-prime spline orbit), and the forcing law that works is rank-one
positive-definiteness plus integrality. MPG lists exactly this as open; AOG and ACS own the two-prime side;
BVI owns the two-prime Kloosterman/CRT block structure of the prime Gram.

**Deliverables, graded.**
1. The exact rank-two Fejér barrier: the maximal ratio of a prescribed Fourier coefficient to the mass for
   positive measures on `T²` under the corpus's harmonic-isolation hypotheses; its restriction to the
   Kronecker line `(u log p, u log q)`.
2. The boundary-line rank-two forcing law and its sharpness models (which Beurling-type systems with two
   coupled channels keep a boundary zero). Expected: nothing beyond rank one for `ζ`; the value is the
   classification.
3. The interior law with growth input `M`: the rank-two analogue of MPG's planned `(√κ − 1)²/M`.
4. The prime-side computation of `c(k,l)` as a finite von Mangoldt window around `p^k q^l` and its
   calibration on the golden datum (must fail PD) and on a curve (must be PD by Weil).

**Battery.** Golden datum; curve data; shifted pair; the Wolff Toeplitz-blind configuration (must be
visible at rank two).

**Routes fed.** ACS (open problem 8: multi-channel positivity past the Fejér barrier), AOG (single-tower vs
two-prime), MPG, HF/SRT (index on two-prime orbits).

### Focus 2 — Classification of escape states of the actual Möbius receiver

**Question.** Which cyclic critical-Wiener modules occur as common cofactor-Gram limits of the *actual*
damped Möbius receiver on escape, and which Class III (Bézout/successor) law of the source excludes them?

**Why.** This is the only non-graded handle in the cancellation family (the admission/escape alternative),
it has the richest machinery in the corpus (ADR: paid ideal ⊆ annihilator, zero-cofactor dichotomy,
rank-one classification, horizon-ratio law, unit transport; BG: paid ideal is not closed, continuum
defects), and its intermediate deliverables are statements about `μ`, not about zeros.

**Deliverables, graded.**
1. Exclude rank-one escape for the actual source: show that neither the augmentation character nor any
   `χ(p) = η(p) p^{-s}`, `s ≥ ½`, is a common limit of the actual cofactor Grams. The magnitudes are
   already forced; the open part is that the sign character `η` and the exponent are not realized by `μ`.
2. Exclude finite-dimensional escape by a source law (finite dimension forces escape; the converse
   exclusion is open).
3. Decide `hull = obstructionHull(μ_ε)` (ideal equality) at one fixed `ε < ½`.
4. The endpoint, a fixed zero-free strip (quasi-RH), is the first rung of every U1 route and is where
   this question meets Focus 3.

**What success/failure means.** Any of 1–3 is a new theorem about Möbius signs at a scale below half
damping, obtained without a zero-free strip; failure (an actual rank-one or finite-dimensional escape
module) would be a counterexample to the receiver's bounded-energy form and hence to RH — so the
classification is informative in both directions.

**Routes fed.** PM, MC, CTF, BVI, THIM, SSA, BG.

### Focus 3 — The signed close-prime-pair surplus beyond the square-root threshold

**Question.** Bound the coalescent surplus of odd primes at even shifts within `T^{−1+η}` at bandwidth
`λ = 4/3`: `oddEvenShiftPrimeCoalescentSurplus ≤ (β + o(1)) N(T,2T)` with `β ≤ 1/18`.

**Why.** This is the square-root threshold wall (U1 meets U2 at aperture `½ log T`) in its most finite
form: a single signed additive prime-pair statement with a known truth value (Hardy–Littlewood/GUE gives
`−1/144`), an explicit budget (`1/18`), a proved reduction (prime powers eliminated, parity reduction, the
Jackson/smooth-window certificate `N₀* ≥ (29/36 − ε)N − surplus` [L]), and a scoreboard: every
intermediate `β` is a theorem (`β < 5/36` beats `2/3`; `β ≤ 577/4500` beats `HD(1)`; `β ≤ 1/18` gives
`3/4`). It is the one wall face where unconditional quantitative progress is measurable without first
proving a strip. It is also the mean-square counterpart of APT's single-height prime saving (open problem
3 there), so progress transfers to the aperture face.

**Deliverables, graded.** Narrow-strip quadratic bound `β(δ) ≤ Bδ²/(1+δ)²` near `λ = 1`; the signed sieve
transfer of trapezoidal lobe cancellation to `1_ℙ(m)1_ℙ(m+2r)`; singular-series error control against the
signed coalescent kernel; the finite-sum-to-form-factor transfer on `(1, 1+δ]`.

**Battery.** Poisson-without-repulsion model must fail (`+1/16`); spectral-sieve model meets the budget
iff `Υ ≤ 2`; sign-blind sieves lose a factor two (parity).

**Routes fed.** ACS/TTPC (proportions), SRT (beyond `X = T`), BVI (balanced statistics at `Q ≍ P`), SAEI.

### Why not the others

- **Selection (3.14, corpus Q1).** Important, but even a perfect selection theorem at the proved aperture
  `κ₀ log Γ` does not reach the detector: the smooth negative witness of a depth-`δ` zero at ordinate `γ`
  needs aperture `C δ^{-2}(4+|γ|)²`, and the near-top modulated lag is `(log γ)² log log γ / δ`. Selection
  without aperture growth produces no contradiction. Keep it as the graded short-window programme; do not
  make it a focus.
- **`polarRate = Δ` (1.11).** The only missing entry of the rate dictionary, but it is a statement about
  hypothetical off-line zeros (no collapsed clusters at doubly exponential height); it never helps prove RH
  and is vacuous if RH holds. Record, do not focus.
- **Invariant completeness (14.12, corpus Q2).** Apparently closed (§1). Convert into an audit task and a
  reference theorem; remove from the open list once integrated.
- **The de Bruijn–Newman core (1.14).** Honest status: counting repairs every high head at every positive
  heat; the residual is bounded height × small heat; the corpus itself shows counting is
  configuration-blind. Progress needs a sign input, which is W1.

---

## 4. Question 3 — the field that would supply the missing tools

### 4.1 Reading the walls as questions

- **W1.** Why do the signs of `μ`, or the fluctuations of `Λ`, cancel to square-root precision at a single
  scale, with every counterterm paid? Over `𝔽_q` the answer is a *count* (Weil, Stepanov): square-root
  cancellation is the shadow of an integer. Over `ℤ` the only additive input (successor) gives density
  scale.
- **W3.** How does a *sign* survive a limit, a completion, a reading or an average? Over `𝔽_q` the
  Néron–Severi lattice is of finite rank, so signature is a finite computation; over `ℤ` the scaling
  surface has infinite rank and no numerical relations.
- **W14.** What arithmetic object carries the source and forces it into the blind carrier? Over `𝔽_q` it
  is `C × C` with effectivity (sections); over `ℤ` there is no surface and the Euler characteristic is real.

The three answers over `𝔽_q` are one object: an intersection theory with integer-valued pairing, finite
rank up to numerical equivalence, and a positivity (ampleness) that comes from counting sections. Over `ℤ`
the corpus has built the pairing (exact), the Lefschetz and adjunction identities (exact), the signature
law, the maximal blind carrier, the function-field calibration and the fake data — and has proved that the
missing ingredient is not an estimate but a structure: an effectivity defined without the sign, with RR.

### 4.2 The field: Arithmetic Positive Duality *(proposal)*

**Name.** Arithmetic Positive Duality: the rigidity theory of positive-definite arithmetic distributions
under Poisson-type self-duality and integer quantization. Working subtitle: *positivity on both sides of
the explicit formula*.

**Point of view.** The explicit formula is a Poisson summation formula between two measures on the line:
the prime measure `μ_P = Σ Λ(n) n^{-1/2} (δ_{log n} + δ_{−log n})` (with its archimedean density and pole
corrections) and the zero measure `μ_Z = Σ m_ρ δ_{γ_ρ}` with `γ_ρ = (ρ − ½)/i`. The prime measure is
positive by arithmetic (`Λ ≥ 0`); RH says the zero measure is a genuine positive measure on `ℝ`. By
Bochner–Schwartz this is Weil's criterion: the Weil distribution is positive definite. So RH is the
statement that a specific Poisson pair is *positive on both sides*. The corpus's two proved mechanisms are
the two first theorems of this field:

- MPG's boundary forcing: positive-definiteness of the prime side in the height variable, with integer
  values and a rigid pole, forces the zero side to vanish on `Re s = 1`;
- the Beurling functional-equation rigidity (§1): a positive self-dual theta pair is forced onto the lattice
  `ℤ` by a Fejér-tent identity.

Weil's theorem for curves is its calibration: positivity of the Fourier transform of the (shifted)
point-count measure on `ℤ`, proved by counting.

**Objects.**
- Poisson pairs `(μ, μ̂)` of tempered measures/distributions on `ℝ` (and on `ℝ × T^r`, on `ℤ^r`, on the
  adeles) with prescribed arithmetic support on one side: `{± log n}` with multiplicative weights; lattices;
  `S`-unit groups `ℤ log p₁ + … + ℤ log p_r`.
- Positive-definite functions on discrete groups of finite rank (`ℤ`, `ℤ²`, `ℤ^r`), integer-valued or
  integer-quantized, and their Fourier measures on tori; Kronecker lines as supports.
- Integer-valued and log-integer-valued invariants: zero orders, distinct right zeros `D`, collision
  masses, torsion orders `#(ℤ/Q_N ℤ)`, Hecke-cycle lattices; the two budgets that have forced anything
  (pole residue `1`, degree/genus).
- Carriers on which the Weil form is a *trace* of a non-commutative action (affine semigroup; Bost–Connes
  type), with the maximal blind ideal as the known commutative sub-carrier.
- Crystals and quasicrystals: measures with discrete support and discrete spectrum (the corpus's lag
  lattices, off-line crystals, Nyquist thresholds), positive crystalline measures and their lattice
  rigidity.

**Language.** Positive-definiteness (Bochner on groups, Bochner–Schwartz on distributions), self-duality
(Poisson), quantization (integer values, parity, character subgroups), spectral gap identities (Fejér tents,
exact sums of squares equal to a computable constant), blindness and visibility (SSIC readings), rank of
the coupling group, barriers (the maximal Fourier coefficient of a positive measure given others), and the
corpus's width units.

**Foundational principles.**
1. *Positivity on one side is known; positivity on the other is the theorem.* Never assume the zero side.
2. *Rigidity before estimates.* The two theorems that exist are rigidity theorems (character on a subgroup;
   lattice support), not inequalities with constants. Seek exact identities whose two sides have different
   regularity (a sum of squares versus a computable constant), then quantize.
3. *Quantization is the lever.* An integer below one is zero; an integer-valued positive-definite function
   with unit mass is a character. Every forcing step must name its integer and its budget.
4. *Rank matters.* Rank one in the height variable forces only the boundary; rank one in the scale variable
   is Toeplitz-blind; rank two in scale decides RH. The theory is a theory of finite-rank sub-couplings
   exhausting an infinite-rank object.
5. *Both ring operations.* Any positive functional that is additive-only or multiplicative-only is either
   blind (quadratic, single-channel) or stops at the boundary (multiplicative). The successor must enter
   through the carrier, not through a density-scale correction.
6. *Calibration over `𝔽_q` and on the battery.* Every statement is tested on curves (must reproduce Weil),
   on the golden datum (must fail), on shifted pairs, parity twins, over-regular Beurling systems, and on
   the FE-complete class (now `{ζ}`).

**Criteria the field must satisfy (what would count as having it).**
- A rank-two forcing law on the boundary line with sharpness models, and an interior law with explicit
  growth input and barrier (Focus 1).
- A quantized inequality in the strip: an integer invariant of the divisor bounded by a computable budget
  strictly below its first nonzero value, on a stated carrier.
- A topology on the Meyer source in which the maximal blind ideal is closed and exhaustion is a limit
  statement (face B3.4), or a proof that no such topology exists.
- Reproduction of the known analytic output in its own coordinates: PNT, the Vinogradov–Korobov region,
  the Guth–Maynard density exponent, Montgomery pair correlation for `α < 1`.
- Reduction over `𝔽_q` to Weil's proof, step by step, with the integer budget identified as degree/genus.
- Formalization with no RH-equivalent hypothesis; every rigidity theorem states which invariant it uses and
  which battery model it excludes.

**Central questions.**
1. (Rank-two boundary law) Classify even positive-definite integer-valued functions on `ℤ²` with
   `D(0) = 1` and the harmonic-isolation hypotheses; find the sharpness models.
2. (Interior continuation) Which positive-definiteness constraints on `Re(−ζ'/ζ)(σ + iu)`, `σ > 1`,
   survive analytic continuation to `½ < σ < 1` when coupled across two incommensurable primes and
   combined with growth input?
3. (Prime-side Bochner) Characterize the positive measures on `T²` whose Fourier coefficients are the
   finite von Mangoldt windows `c(k,l)` around `p^k q^l`; relate the Kronecker-line support to prime
   distribution in short multiplicative windows.
4. (Quantized budget) Identify the integer or log-integer that plays the pole's role at the critical line;
   prove or refute an inequality of the form `(integer invariant) × (coefficient) ≤ (budget)` on a finite
   sub-coupling.
5. (Crystalline rigidity for Poisson pairs) Extend the Fejér-tent spectral gap identity from theta pairs to
   the Weil pair: which exact sums of nonnegative terms equal a computable constant on the Weil pair, and
   what do they force?
6. (Non-commutative carrier) Does the Weil form extend to a positive functional on the affine semigroup
   algebra of the integers that is not a quadratic form in the test? What is its restriction to the finite
   affine quotient?
7. (Topology) Which completion of the Meyer source retains every critical jet and makes the trace-bounded
   ideal closed?

**Research topics (programme outline).**
- Positive-definite functions on `ℤ^r` with arithmetic Fourier supports: barriers, extremal measures,
  quantized classification; the `ℤ²` Fejér problem.
- Fourier duality of the two corpus positivities (MPG height / AOG scale) made explicit as one theorem.
- Spectral gap identities of Fejér type for the Weil distribution against lattices and `S`-unit groups.
- Integer budgets: torsion orders, finite affine quotients, Hecke-cycle lattices; which admit a
  theorem-of-the-square substitute (the naive one fails, `heckeCorrespondence_no_square_relation`).
- Positive crystalline measures with Gaussian/theta self-duality: the Beurling rigidity as the first case;
  degree-`d` abundance as the control group.
- Non-commutative positivity on the affine semigroup: finite-horizon functionals, infinite-dimensional
  carriers, Bost–Connes-type symmetries and their quantization; what the Weil form's restriction is.
- Signed additive prime correlations at the square-root threshold (Focus 3) as the analytic face of the
  same duality: the coalescent surplus is the prime-side Fourier coefficient the zero side cannot see.
- Formal infrastructure: Bochner on `ℤ^r` and `T^r` (the corpus has Bochner on `ℝ`), Bochner–Schwartz for
  tempered distributions, Fourier analysis on `S`-unit groups.

**Relation to existing programmes.** MPG is the rank-one height side; AOG/ACS own the scale side and the
calibration; BG and SSA own the successor and the finite affine quotient; SSIC prices every reading; BSU
owns the bi-scale uncertainty and node criticality; TTPC owns the threshold face. The field is not a new
programme beside these; it is the statement that their positivity structures are Fourier dual and that
their two proved forcing theorems share one shape, with the research task of producing the third instance
of that shape in the strip.

**What it is not.** It is not a claim that such a field exists or must exist; the summary's statement that
no reviewed theorem proves a new field is needed stands. It is the smallest field in which the two things
that have ever forced anything about `ζ`'s zeros — integer quantization against a rigid budget, and
positivity + exact self-duality — are the axioms rather than accidents, and in which the corpus's
exhaustion theorems are theorems about what the axioms do *not* yet contain.

---

## 5. Evidence

**Read in full.** `docs/reports/rh-current-frontier-map.md`; `docs/reports/rh-killed-routes.md`
(sections: wall families, 44 mechanisms, retired labels, route-class obstructions, ULF obstructions,
endpoint and scoped catalogues skimmed by header and first lines); `review-2510/route-unification-ledger.md`;
`review-2510/hard-obstacles.md`; `review-2510/walls-ledger.md`; `review-2510/what-forces-blindness.md`;
the READMEs of arithmetic-positivity-theory, BiScaleUncertainty, TransHorizonIncidenceMechanics,
BezoutValuationIncidence, ArithmeticCriticalityTheory, SquareRootThreshold, ArithmeticIncidencePositivity,
ArithmeticContinuationAndCriticalEnergy, ScaleSignedIncidenceCriticality, ArithmeticCompensationTheory,
ArithmeticCastelnuovoSeveri, SignedArithmeticEnergyIncidence, TransThresholdPairCorrelation,
ArithmeticOrientationTheory, ArithmeticOrientationGeometry, ArithmeticLocalDivisorGeometry,
SignedSuccessorArithmetic, ArithmeticDefectRigidity, BiarithmeticGeometry, MultiplicativePositivityGeometry.
No other Markdown was read.

**Corpus searches** (`scripts/formal_tools.py research`, default hybrid mode unless noted): complex
damping/three lines; Bost–Connes/KMS/`ax+b`; interior quantized forcing; Hamburger/Beurling uniqueness;
Pólya frequency/Laguerre–Pólya; Hilbert–Pólya operators; Chowla/Sarnak correlations; Lindelöf; off-line
clustering and `polarRate`; single-height phase selection; zero-density exponents; Selberg class; de
Bruijn–Newman; Montgomery pair correlation; escape-state classification; crystalline/Poisson lattice
support; function-field Hodge index; Li coefficients; Nyman–Beurling; theorem of the square; affine
infinite-dimensional carriers; adelic/Connes trace; uniqueness/rigidity; integer parity invariants;
tensor-power self-improvement; Hadamard three-lines convexity; Fourier interpolation at zeta zeros; sign
uncertainty principles; Bochner–Schwartz framing; `splineTwoPrime` (lexical); Wolff obstruction; rank-two
positive definiteness; Stepanov. Source files opened for exact statements:
`HTGeometry/BeurlingRiemannFunctionalEquationRigidity.lean`, `RHTower/PMPowerDampedMobiusComplexBoundary.lean`,
`RHTower/BeurlingSystemGibbsGauge.lean`, `ArithmeticOrientationGeometry/TheSplineOrbitDecidesTheCriticalLine.lean`.

**Not found in the corpus** (relevant absences): Bost–Connes or Cuntz `ax+b` algebras; crystalline-measure
or Fourier-interpolation results; sign-uncertainty principles; a rank-two positive-definiteness theory
(only Bochner on `ℝ` and the two-prime receiver); Chowla/Sarnak-type correlation results; an explicit
Bochner–Schwartz statement for the Weil distribution.

Working log: `logs/fable-review-2510-research-log.md`.
