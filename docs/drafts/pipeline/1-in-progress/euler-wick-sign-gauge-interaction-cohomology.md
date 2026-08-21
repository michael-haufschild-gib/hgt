# Euler--Wick sign-gauge interaction cohomology

- **ID:** euler-wick-sign-gauge-interaction-cohomology
- **Stage:** 1-in-progress
- **Type:** ACTIVE REGULAR-ORBIT / OPPOSITE-CROSSING ROUTE; DIRECT SCALAR LANDING KILLED
- **Source:** `rh-current-frontier-map.md` question 28; corpus bridge from raw Euler Wick defect to finite-quotient interaction cohomology
- **Statement:** The two-leg sign-gauge orbit of the raw four-factor Euler Wick defect canonically generates the full `Fin 2 × Fin 2` joint-observable quotient modulo row and column marginals.  Its full regular representation admits an exact completed logarithmic-flux landing whose augmentation is Xi, and source reflection combined with double-negative residue translation gives the strictly positive local crossing `4 log(p) z²`.  Genuine meromorphic cell carriers and transport of this crossing to divisor exclusion remain open.

## Goal

Answer frontier question 28 with a coefficient-faithful source invariant that survives the collapse of nonlinear and tangent higher grades to grade one.  The target is not a renamed scalar obstruction: the raw Euler coefficient packet itself must induce the quotient class, and the class must exhaust the unique mixed direction without any Xi-divisor, RH, zero-location, positivity, or source-order premise.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: exact EWQ, Artin no-go, regular-orbit, and opposite-crossing leaf builds green; axiom audit PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Exact conjecture `[EWIC-1]`

Let `D(a)` be the raw squarefree Euler four-point Wick defect, so the existing corpus proves

`D(a) = -2 a₀ a₁ a₂ a₃`.

Let `ε : Fin 2 → ℂ` equal `1` at the distinguished anchor `1` and `-1` at `0`.  Define the actual two-leg gauge orbit

`G_a(x,y) = D(a) ε(x) ε(y)`

and take its canonical anchored mixed part

`I_a(x,y) = G_a(x,y) - G_a(x,1) - G_a(1,y) + G_a(1,1)`.

Conjecture:

1. `I_a(x,y) = D(a)(ε(x)-1)(ε(y)-1)`.
2. `I_a` lies in the anchored interaction complement and its quotient class is unchanged after adding any row-plus-column observable.
3. `[I_a] = 0 ↔ D(a)=0 ↔ a₀a₁a₂a₃=0`.
4. If all four Euler coefficients are nonzero, `[I_a]` spans the entire `Fin 2 × Fin 2` interaction cohomology, whose complex dimension is exactly one.

## Why this attacks a frontier obstruction

AGC collapse says scalarization through grade-one or marginal data erases nonlinear/tangent higher grades.  The joint-observable quotient is designed to erase exactly the two marginal spaces while retaining their mixed incidence.  `[EWIC-1]` would identify a natural raw Euler observable—not an arbitrary complement vector—whose surviving class is both coefficient-faithful and complete in the first nontrivial quotient.  This supplies an exact detector class for the mixed-incidence and higher-grade-survival obligations shared by AGC, Q, HC, PLAC, and EPC.  It does not yet prove the global order or receiver-landing theorem.

## Anti-theatre / kill criteria

Kill this bridge if any of the following occurs:

- the class is defined by inserting `D(a)` into a preselected basis rather than by the gauge orbit and canonical mixed-part operation;
- nonvanishing needs any hypothesis beyond the already classified local degeneracy locus;
- marginal neutrality is merely asserted for one chosen counterterm instead of the full marginal submodule;
- the spanning result does not identify the whole one-dimensional quotient;
- the construction factors through either single gauge leg, in which case it is grade-one data in disguise.

## Approach

Use `EulerSquarefreeWickDefect` for the literal source scalar and `CoprimePrimeResidueInteraction` for the canonical row/column/anchored decomposition.  Package the anchored observable inside `ClassInvariantRestricted (productFstSetoid ⊓ productSndSetoid)`, map it to `FiniteQuotientInteractionCohomology`, prove its exact kernel by the marginal/anchored disjointness theorem, then combine nonvanishing with the existing dimension-one formula to prove generation.

## Conjecture loop

- **C1:** Hall visible-kernel recovery solves Route E neighbor expansion. **FAIL/PIVOT.** Generic quotient injectivity is Hall's missing condition in another form; no automatic graph expansion follows from the QEC theorem.
- **C2:** Chern--Simons/Wilson secondary holonomy solves PCS zero-index blindness. **FAIL/PIVOT.** Wilson holonomy supplies a homological detector, but no corpus theorem forces its completed Euler-source class to vanish precisely in the right strip.
- **C3:** Rainich square reconstruction linearizes Route O determinant positivity. **FAIL/PIVOT.** Corpus has forward Rainich identities but no inverse source reconstruction; Route O is also inside the excluded classical operator family.
- **C4:** Raw Euler Wick defect becomes a canonical sign-gauge interaction class solving AGC's detector problem. **PROVED.** `EulerSquarefreeWickInteractionCohomology.lean` proves the exact anchored law, marginal-counterterm invariance, kernel, dimension-one quotient, and generation.
- **C5:** Pauli character projection turns the EWQ class into a ZGC orientation producer. **FAIL/PIVOT.** The Pauli projector preserves/extracts a character sector but supplies no source law annihilating the selected Xi endpoint.
- **C6:** Actual mod-3/mod-4 prime recurrence upgrades EWQ to an analytic source channel. **PROVED SURVIVOR.** `EulerSquarefreeWickPrimeResidueHT.lean` and `EulerSquarefreeWickQuadraticCharacterBridge.lean` identify the carrier with the canonical modulo-twelve quadratic character and prove relative differential independence over every separate marginal field; no analytic marginal counterterm cancels it.
- **C7:** Pauli/Clifford/Wick zero-mode cancellation closes HC/CGL. **FAIL/PIVOT.** Equal-character off-diagonal triples survive the zero mode; a Clifford twirl would require a complete invariant orbit, while Wick pairings are nonzero.
- **C8:** Deninger's prime--Gamma mixed secant carries the modulo-twelve interaction. **FAIL/PIVOT.** The literal source trace has no residue coordinate and sums residue labels away. Twisting it changes the Xi resolvent and destroys the divisor-side polarization identity.
- **C9:** Exterior/Fock or Rainich reconstruction orients Route O. **FAIL/PIVOT.** Route O already linearly recovers both coordinates through two fixed shears; determinant polarization still lacks order. The corpus contains only forward Rainich algebraic identities, not a source inverse/dynamics theorem.
- **C10:** ZGC class-law chirality plus valuation-depth renewal supplies a completed involution. **FAIL/PIVOT.** Exact two-class conditionals exist, but their actual aperture mass evacuates. Relative HT creates new algebraic directions, not probability mass, and the non-atomic theta/Hasse packet cannot be KL-isometrically identified with a countably atomic class law.
- **C11:** Constitutive prime-interaction formation phase or Route-N vacuum fusion orients EWQ. **FAIL/PIVOT.** Formation work squares away the quadratic sign, so attaching EWQ labels is theatre. Vacuum fusion requires a uniform positive admission; the actual moving abelian apertures tend to zero, and character recurrence does not replenish mass.
- **C12:** The algebraic EWQ phase closes the quadratic Gelfond--Schneider endpoint. **FAIL/PIVOT.** Equality of the EWQ value with the Xi multiplicity phase is exactly the missing divisor-to-source monodromy; by the endpoint theorem that equality already forces zero multiplicity.
- **C13:** Complete EWQ through all prime-power depths and test a gauge-equivariant Xi landing. **PROVED NO-GO / POSITIVE SURVIVOR.** `EulerSquarefreeWickArtinInteractionNoGo.lean` proves the four-sector virtual coefficient
  `1 + (χ₃χ₄)^k - χ₃^k - χ₄^k = (1-χ₃^k)(1-χ₄^k)`. Every even depth is zero and every odd depth is the original anchored EWQ class. This is the local logarithmic coefficient of `ζ L(χ₁₂)/(L(χ₃)L(χ₄))`. The same module proves every residue-translation-invariant scalar linear reader annihilates the joint character, so no scalar Xi landing is both gauge equivariant and coefficient faithful.
- **C14:** Retain the entire regular residue orbit rather than apply a scalar reader. **PROVED SURVIVOR.** `EulerSquarefreeWickRegularOrbitFlux.lean` proves Fourier inversion onto four literal residue cells, exact recovery of all four sectors, and a completed logarithmic-flux landing with vacuum coordinate `-d log Xi`, three Dirichlet-L coordinates, Xi as cell augmentation, and the virtual Artin interaction as anchored reader.  The canonical split form has signature `(+,-,-,+)`; literal prime packets are null, the joint axis is positive, marginal axes are negative, and real nonnegative cell weights have exact norm `8(ad+bc) ≥ 0`.  Hostile audit: this is initially a direct sum of Fourier sectors, so it does not yet couple an EWQ class to a Xi divisor.
- **C15:** Use the unique double-negative residue translation as the null-cone crossing operator and pair it with functional-equation group completion. **PROVED SURVIVOR.** `EulerSquarefreeWickOppositeResidueCrossing.lean` proves that `(-1,-1)` fixes vacuum and joint sectors, negates both marginals, sends every odd-depth actual gauge packet to the opposite residue cell, and converts the split form to the positive sum of four coordinate squares.  Tensoring this crossing with the exact Euler residue seam between `p` and `p⁻¹` gives `4 log(p) z² > 0` for every nonzero actual prime packet; every finite nonzero packet family has strictly positive total energy.  This is the first canonical non-block-diagonal source orientation in EWQ.
- **C16:** Exponentiate each inverse-Fourier cell flux to a genuine completed meromorphic carrier. **FAIL AS AUTOMATIC STEP / DIVISOR-QUANTIZATION PIVOT.** The inverse transform divides logarithmic residues by four.  Therefore a cell carrier exists only if the Walsh--Hadamard combinations of the Xi/Dirichlet-L divisor orders are divisible by four.  With `r` independent quadratic gauges the denominator becomes `2^r`; a pure Xi divisor would need multiplicity divisible by `2^r`.  Unbounded gauge rank would annihilate every finite Xi order, but only after proving either an unbounded family of genuine cell-root landings or enough pointwise nonvanishing of all auxiliary product-character L-functions.  Corpus finite quadratic moments do not currently provide this common-zero avoidance.  Treating the flux direct sum as already exponentiated is theatre.

## No-go closure (mandatory when falsified)

- **Exact killing theorem/mechanism:** `no_quadraticResidueGaugeInvariantScalarReader_product_one`. A scalar Xi target carries the trivial residue action; equivariance annihilates the nontrivial `χ₃ ⊗ χ₄` isotypic class. Independently, `primeResidueValuationInteractionGridCarrier_vacuum_eq_zetaGhost` identifies the untwisted zeta tower with the unique empty-support sector, while EWQ lies in the full two-coordinate sector. A non-equivariant map would discard the route's defining gauge/marginal quotient and is not coefficient faithful.
- **Strongest positive survivor:** the all-depth virtual Artin interaction. Odd valuation layers retain EWQ, even layers cancel, and its natural completed target is the four-function cross-ratio `ζ L(χ₁₂)/(L(χ₃)L(χ₄))`, not Xi. This vector/twisted system has its own three nonprincipal Dirichlet-L divisors; existing Stark, Artin, functional-equation, and zero-count laws do not isolate the zeta divisor or orient its zeros.
- **New insight:** interaction cohomology is a superselection label, not a scalar correction. Completion preserving the label necessarily leaves the trivial zeta representation; completion forgetting the label kills the invariant. This explains why marginal cancellation is strong yet cannot become an Xi producer. The obstruction is representation-theoretic, not missing analytic estimates.
- **Status:** direct scalar EWQ-to-Xi route killed.  Full regular-orbit route is live: completed flux landing and canonical positive opposite crossing are formalized.  Open core is now sharp—integral/meromorphic cell descent plus transport of positive source crossing to negative-square exclusion of off-line Xi divisors.

## Log

- 2026-08-21 — Created directly in stage 1 after whole-corpus search and three explicit bridge kill tests. Scratch formalization started; frontier map remains read-only.
- 2026-08-21 — Closed `[EWIC-1]` in Lean; realized actual prime residue carrier and canonical `χ₁₂`; proved relative HT and analytic marginal no-cancellation.
- 2026-08-21 — Ran formation, vacuum-fusion, ZGC, Gelfond--Schneider, Artin/Stark, hyperbolic-quartic, Deninger mixed-secant, Route O, Pauli/QEC, Rainich, and valuation-superselection attacks. Each failed at an exact source/receiver handoff rather than by analogy.
- 2026-08-21 — Proved the all-depth virtual Artin coefficient law and scalar gauge-equivariant Xi-landing no-go in `EulerSquarefreeWickArtinInteractionNoGo.lean`. `rh-current-frontier-map.md` remained read-only.
- 2026-08-21 — Reopened route after scalar no-go.  Proved a coefficient-faithful four-sector completed logarithmic-flux landing, its `(2,2)` Krein/null-cone law, and exact nonnegative source cone `8(ad+bc)` in `EulerSquarefreeWickRegularOrbitFlux.lean`.
- 2026-08-21 — Combined EWQ with the corpus Euler character group completion and finite-Hankel null-crossing principle.  Proved the canonical opposite-residue reflected crossing `4 log(p) z²`, strict finite source energy, and odd-depth compatibility with actual `(-1,-1)` residue translation in `EulerSquarefreeWickOppositeResidueCrossing.lean`.
- 2026-08-21 — Hostile divisor audit exposed the next obstruction: inverse Fourier fluxes have quarter-integral residues unless a Walsh divisor congruence holds.  General `2^r` gauge cubes turn completed carrier landing into an unbounded root/divisor-annihilation mechanism, conditional only on constructing genuine cell roots or avoiding common auxiliary L-zeros.  Frontier map remained read-only.
