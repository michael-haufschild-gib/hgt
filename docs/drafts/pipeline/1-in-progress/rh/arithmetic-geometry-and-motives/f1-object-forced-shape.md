# The F₁ object for Spec ℤ: its shape as forced by theorem

- **ID:** ULF-F1-003
- **Stage:** 1-in-progress (constraints proved; the object itself open)
- **Type:** STRUCTURAL PROGRAMME with certified constraints
- **Source (literature, August 2026):** Connes–Consani, *On the absolute geometry of Spec ℤ*
  (arXiv 2606.06604: the absolute `𝔽₁`-curve as pullback of the `𝔽₁`-structure sheaf, discrete
  Frobenius symmetries, Tate curve with modulus `p⁻¹`, real Fargues–Fontaine analogue; no RH
  statement); Connes–Consani, *On the Jacobian of Spec ℤ* (arXiv 2602.15941: the Riemann sector
  of the adele class space as the monoidal extension of the Picard group, torsion-free rank-one
  groups with norms; no RH statement); Deninger, *Rational Witt vectors and associated sheaves*
  (arXiv 2508.05329) and the foliated dynamical systems for arithmetic schemes; Meyer's spectral
  realization.
- **Source (corpus):** the Deninger source-native programme (`deninger-arithmetic-cohomology-construction.md`,
  roadmap: H¹ = Meyer's quotient `M_ζ`, three-term complex in Lean, Frobenius-compatible Hodge
  star `⟺` RH, open Hodge gate), `XiArakelovKroneckerChamber`, and the 2026-09-02 theorems
  (`FrobeniusTorsionLaw`, `SixExponentials`, `LiSignOscillation`, `GlobalParityWall`,
  `MoebiusConvergenceZeroFree`, Baker's theorem in Lean).
- **Statement:** any cohomology of the arithmetic curve over `𝔽₁` whose Frobenius has the
  zeros of ξ as eigen-characters must have the shape §2; the constraints there are theorems, the
  object is not constructed.

## 1. What is new relative to the August 2026 literature

The 2026 constructions supply geometry (an absolute curve with discrete Frobenius symmetries, a
Jacobian) but no bridge to the zeros. The corpus's Deninger programme supplies the candidate H¹
(Meyer's quotient) and reduces RH to one gate. The theorems of 2026-09-02 add *constraints that
any such object must satisfy*, none of which appears in the literature:

| constraint | theorem | what it forbids |
|---|---|---|
| C1 no finite integral lattice | `not_exists_joint_eigenfunctional_three_primes` | a finite free ℤ-module with three Frobenii `F_p, F_q, F_r` and a nonzero functional intertwining them with `p^ρ, q^ρ, r^ρ` |
| C2 unitary lattices are torsion | `exists_pow_eq_one_of_eigenfunctional_of_unimodular_charpoly` | a finite free ℤ-lattice Frobenius with unimodular spectrum has every eigen-character a root of unity |
| C3 normalised integrality contradicts RH | `not_riemannHypothesis_of_xiArakelovIntegral_faithful` | Galois-closed algebraic-integer Arakelov coordinates |
| C4 per-prime integrality at ≤ 2 primes | `not_all_three_prime_cpow_isAlgebraic` | `p^ρ` algebraic at three primes |
| C5 no global multiplicity doubling | `not_forall_even_order_xi` | any antiunitary or Kramers structure on all of H¹ |
| C6 Lefschetz numbers oscillate | `not_eventually_re_xiLiPaired_neg` | any one-signed universal Lefschetz positivity below RH |
| C7 Möbius convergence is the conclusion | `riemannZeta_ne_zero_of_moebius_convergesAt` | a cohomology on which `μ` acts convergently in the strip |

## 2. The forced shape

(a) **Coefficient ring.** The Frobenii form the dilation monoid `ℕ^×`; the natural coefficient
ring is its completed monoid ring, mathlib's `ArithmeticFunction ℤ` under Dirichlet convolution,
with the zeta element `ζ = Σ_n [n] = ∏_p (1 − [p])⁻¹` (all coefficients `1`) and its inverse
`μ`. Integrality lives here, on the coefficient side (MUST-129), not on eigenvalues (C1–C4).

(b) **H¹ as a cokernel of the zeta element.** Meyer's `M_ζ = H_−/{x ↦ Σ_n f(nx)}` is
`H_−/ζ·H_∩` for the dilation action `([n]·f)(x) = f(nx)`: the middle cohomology is the cokernel
of multiplication by the zeta element on the Poisson-admissible subspace. The zeros are the
characters `χ_s : [n] ↦ n^{−s}` at which `ζ` fails to be a `χ_s`-unit; since `ζμ = 1` in the
ring, this is exactly where `μ` does not act (C7): RH is the statement that `μ` acts on the
`Re s > ½` sector.

(c) **Infinite rank, flow not discrete.** By C1–C2 no finitely generated ℤ-submodule carries a
zero as a joint eigen-character; the Frobenius is the scaling flow `e^{tΘ}` and the discrete
Frobenii `F_p = e^{(log p)Θ}` have transcendental eigenvalues at all but at most two primes
(C4). In the absolute curve of Connes–Consani, the discrete Frobenius symmetries of the Tate
curve pieces (modulus `p⁻¹`) therefore cannot see the zeros in any finitely generated integral
piece; the zeros must live in the archimedean (real Fargues–Fontaine) part.

(d) **Why the archimedean line.** The characters of `ℤ[ℕ^×]` form the torus `(ℂ^×)^{primes}`;
the Euler product `∏(1 − z_p)⁻¹` has no zeros on it. The zeros arise only along the line
`z_p = p^{−s}`, whose unitary part `(p^{−it})_p` is dense in every finite unitary sub-torus
because the `log p` are ℚ-independent (Baker, in Lean). The zeros are a phenomenon of the
archimedean embedding of the monoid, invisible to every finite algebraic specialization.

(e) **The single missing datum.** A Hermitian form on `coker(ζ)` must vanish on `ζ·H_∩`, hence
is a Weil-type form supported on the zeros; its positivity is RH (corpus: Frobenius-compatible
Hodge star `⟺` RH; producer positivity is RH-or-blind). The only non-receiver route is a
positivity *produced by geometry* (Deninger–Singhof: Kähler leaves with the flow scaling the
Kähler class), which needs the archimedean compactification of the roadmap's open trace gate.

## 3. Predictions on the 2026 literature (falsifiable)

- P1. No finitely generated integral piece of Connes–Consani's absolute curve cohomology has a
  zero of ξ as a joint Frobenius eigen-character at three primes (C1).
- P2. Any "Jacobian of Spec ℤ" endomorphism ring containing three integral Frobenii with a Rosati
  positive involution on a finite-dimensional ℚ-piece is impossible; Rosati positivity must be a
  trace (type II) positivity, i.e. Weil positivity, a receiver.
- P3. Deninger's rational-Witt dynamical system cannot have a finite-rank ℤ-structure on the
  leafwise H¹ compatible with three prime Frobenii; its ℤ-structure must be on the coefficient
  sheaf (rational Witt vectors act as the Dirichlet ring), consistent with (a).

## Open core
`[OPEN CORE]` a geometric production of the positive Hodge form on `coker(ζ)` (the Kähler
foliation with transverse flow, extended through the arithmetic compactification). Nothing in the
August 2026 literature closes it; the corpus's roadmap names it as
`DAC_ARITHMETIC_CALDERON_GREEN_INTERMEDIATE_EXTENSION`.

## Gates
- [x] 0 → 1: constraints C1–C7 proved in Lean; shape (a)–(e) stated with sources.
- [ ] 1 → 2: the positive Hodge form produced by geometry.

## Log
- 2026-09-03 — created; C1–C2 new in `RHTower.FrobeniusLatticeRigidity`.

## Addendum 2026-09-03 — the constraint on the corpus's own carrier, and the audit of the Hodge gate

**C1 on the graded carrier (Lean, `RHTower.DeningerCarrierNoIntegralLattice`).** With the
Frobenius at `p` acting on `XiZeroCopy →₀ ℂ` by `p^ρ` on the `ρ`-mode
(`deningerPrimeFrobenius`), every finitely generated `ℤ`-submodule stable under the Frobenii at
three distinct primes is zero (`deningerDivisorH1_no_finite_frobenius_lattice`). Every
coordinate functional is a joint eigen-functional, and a finitely generated torsion-free
`ℤ`-module is free, so `FrobeniusLatticeRigidity` applies. The corpus's carrier therefore has no
integral lattice in the modes at all; any `ℤ`-structure lives on the coefficient side, as (a)
predicts.

**Audit of the open Hodge gate** (`deninger-arithmetic-calderon-green-intermediate-extension`,
`deninger-hodge-schwartz-resolvent-core`) against the terminal classification:

| open item of the gate | kind | verdict |
|---|---|---|
| radical identity `H_− ∩ \overline{Z(H_∩)}^{L¹(e^{t/2}dt)} = Z(H_∩)` | closure inside the strip | the critical-line norm controls the Mellin transform only on `Re s = ½`, so the closure is annihilated at on-line zeros and blind to off-line ones (kind ii); expected RH-equivalent or false, not an independent producer |
| Green supertrace / cup identity `(5)` | identity | admissible; carries no positivity by itself |
| global Green-energy radical (`zero energy ⟺ closed boundary subspace`) | faithfulness of a completion | receiver: faithfulness of any flow-compatible energy on `coker(ζ)` is the Hodge purity, i.e. RH (corpus: Frobenius-compatible Hodge star ⟺ RH) |
| Hodge–Schwartz core density + off-axis resolvent preservation | resolvent stability | RH-strength by the corpus's own `DAC_DENSE_RESOLVENT_TRANSPOSE_PURITY` (the card labels it RH-bearing) |
| geometric production (Kähler leaves, transverse flow, archimedean compactification) | producer | the only non-receiver item; open |

So the gate's proof programme is correct in shape: every analytic clause is a receiver, and the
theorem it needs is the geometric one (Deninger–Singhof positivity on an arithmetic foliated
space). MUST-134: work on the gate should go to the archimedean compactification producing the
Kähler class, not to closure or faithfulness clauses, which cannot be proved below RH.

## Addendum 2026-09-03 (ii) — all places are cusps (Lean, `RHTower.ArchimedeanTransverseMassLaw`)

The Deninger–Singhof positivity integrates leafwise `L²`-norms against a flow-invariant transverse
measure. At the real apex of the corpus's stationary germ the flow contracts the invariant
transverse coordinate `x = r²` by `e^{−2t}` (`deningerGermTransverse_flow`), i.e. translates
`log x` by `−2t` (`log_deningerGermTransverse_flow`). A nonzero transverse measure invariant under
this flow and finite on compacts is, by uniqueness of Haar measure on the line, a multiple of
Lebesgue measure in `log x`, hence gives infinite mass to every neighbourhood of the apex
(`apex_transverse_mass_eq_top`). So in the invariant-measure geometry the archimedean place is a
complete cusp end of infinite transverse mass, exactly as the finite primes are cusp ends of
infinite length (`deningerCusp_length_not_integrable`). No smooth stationary-point model of the
real place carries a finite invariant transverse measure.

MUST-135: the archimedean compactification of the open Hodge gate must be cuspidal — the global
scalar product must be built with the measure `d(log x)` near the apex, and the leafwise forms
must decay along the cusp. Forms with finite global norm near the apex are exactly those whose
transverse profile is `L²` for `d(log x)`, i.e. `L²((0, ε), dx/x)`: the archimedean weight is the
Mellin-critical weight `x^{−1}dx` on the transverse coordinate. This is the invariant-measure
origin of the `1/2` in `Θ − ½`: leafwise Kähler weight `e^{t}` against the invariant transverse
measure gives global weight `e^{t}`, and `e^{−t/2}φ^{t*}` is unitary (corpus:
`deningerTwistedFlow_centered`).

## Addendum 2026-09-03 (iii) — census of the global space in the corpus, and the transverse-measure atlas

**What the corpus holds for the global foliated space** (deep inspection 2026-09-03):

| stratum / structure | module | proved |
|---|---|---|
| fine generic source: points `(χ, h, u)` (unitary character, Kummer vector, suspension height); modulus flow and Kummer–Kronecker phase flow generate an affine-group action whose orbits are the leaves; the flow moves only the height and is transverse to the leaves | `DeningerAffineLeafFlow` | yes |
| deck relation `(a, u) ∼ (q a, u/q)` trivialised by the weight-one radius; suspension flow = dilation of the radial line; ray augmentation resolution | `DeningerKummerRayResolution`, `DeningerArithmeticHilbertKummerRadius` | yes |
| leaf cylinder modes: Haar-orthogonal characters, norm `1/|μ|`, cup pairing; Kronecker density ⟺ trivial annihilator | `DeningerCylinderModes` | yes |
| prime cusp: metric `(u/L)(dL²+dθ²)`, weight-one Kähler form, deck invariance, infinite length, quarter-turn star | `DeningerProLogCuspHodge` | yes |
| real apex germ: involution, flow weights `+½` (leaf), `−2` (transverse), stationary apex, orientation-sign descent | `DeningerStationaryKahlerGerm`, `DeningerReesJetTower` | yes |
| generic/prime overlap: conformal metrics, agreeing stars | `DeningerAffinePrimeOverlap` | yes |
| abstract flow purity: weight law, unitary group, `Re λ = n/2`, odd `J` with `J² = −1`, positive cup | `DeningerKahlerRiemannFlowPurity` | yes |
| rational Witt space (Deninger Def. 2.3) | `DeningerDynSysRationalWittPresheaf` | yes |
| transverse measure: canonical, both ends cusps, apex gluing `log x = −2 log u` | `ArchimedeanTransverseMassLaw` | yes (this cycle) |
| **global gluing of the strata into one foliated space with holonomy-invariant transverse measure and leafwise complete Kähler metric** | — | **missing** |
| leafwise `L²`-Hodge theory on the cusped leaves (fibred-cusp / extended Hodge) and its comparison with `M_ζ` | — | **missing (the gate)** |

**Transverse-measure atlas (Lean).** On the generic stratum the flow translates the logarithmic
height by `t` (`log_deningerSuspFlow_susp`); a nonzero flow-invariant transverse measure, finite
on compacts, is a multiple of `d(log u)` and infinite at both ends (`suspension_transverse_mass_eq_top`).
The real-apex chart's coordinate glues by `log x = −2 log u`, the only power law compatible with
the flow weights `+1` and `−2` (`apexGluing_exponent_unique`); the gluing intertwines the two
flows (`apexGluing_intertwines`), carries invariant measures to invariant measures
(`map_apexGluing_invariant`), and sends `d(log u)` to `½ d(log x)` (`map_apexGluing_volume`).
Hence the flow-invariant transverse measure of the whole transversal is canonical up to one
global constant, with the real apex at the `u → ∞` end.

**Consequence (MUST-136).** The Riemannian-foliation hypothesis of Deninger–Singhof (existence of
a holonomy-invariant transverse measure) is not the obstacle: leaves fix the height, holonomy is
trivial on the transversal, and the measure is forced. The whole difficulty of the positive Hodge
gate is leafwise: a complete Kähler metric on the cusped leaves with `L²`-Hodge decomposition in
the extended (fibred-cusp) sense, glued across the prime and real strata, whose reduced `H¹`
compares with `M_ζ`. The next construction step is the leafwise metric on the generic leaf
(affine-group orbit) that restricts to the prime cusp metric and the apex germ on the overlaps,
with the flow scaling its Kähler class by `e^{t}`.

## Addendum 2026-09-03 (iv) — correction: the polarization density has weight one, not zero

The weight bookkeeping of the Deninger–Singhof polarization is: `H² = ℂ(−1)`, i.e. the flow acts
on the Kähler class by `e^{t}`; the cup pairing `H¹ × H¹ → H²` is flow-equivariant, so paired
eigenvalues satisfy `λ + λ' = 1`; positivity of `h(x, y) = tr(x ∪ ⋆y)` with `h(φx, φy) = e^{t}h(x, y)`
makes `e^{−t/2}φ` unitary and forces `Re λ = ½`. A trace on `H²` *invariant* under the flow is
impossible (`no_invariant_trace_of_weight_one`: `T(ω) = T(φ^{t*}ω) = e^{t}T(ω)`), and in real
leaf dimension two the leafwise `L²` product of one-forms is conformally invariant, so a
flow-invariant transverse measure would make the flow unitary on `H¹` with `Re λ = 0`, not `½`.
Hence the transverse density of the polarization is the **weight-one density `du`** on the height
line, whose pushforward under `u ↦ e^{t}u` is `e^{−t}du` (`heightDensity_map_heightFlow`), not
the invariant `du/u` of addenda (ii)–(iii). With `du` the `u → 0` end has finite mass
(`heightDensity_Ioo_zero_one`) and the real apex `u → ∞` has infinite mass
(`heightDensity_Ioi_one`); in the apex coordinate `x = u^{−2}` the density is `½ x^{−3/2}dx`, so
the real place is the *only* transverse cusp. Uniqueness of the weight-one density is the Haar
argument applied to `e^{−y}ν` in the logarithmic coordinate (paper).

**Corrected laws.** MUST-135 and MUST-136 are replaced by MUST-137: the transverse density of the
F₁ object is `du` (weight one, canonical up to a constant), invariant transverse measures are
excluded by `H² = ℂ(−1)`, the `u → 0` end is a finite boundary and the real apex is the single
transverse cusp; the difficulty of the gate remains leafwise. The results of (ii)–(iii) stay
true as statements about invariant measures and record why that hypothesis cannot be the one
used.

## Addendum 2026-09-03 (v) — the weight-one density is the corpus's half-density, and the completion dichotomy

**Identification (Lean, `RHTower.WeightOneFlowIsometry`).** The corpus completes the literal Meyer
cohomology with the `L¹` seminorm of weight `exp(t/2)` in the logarithmic radius
(`deningerMeyerHalfDensityWeight`), on which the centered dilation `g ↦ e^{−c/2} g(· − c)` is an
isometry. The square of that weight is `exp t = du/dt` (`deningerMeyerHalfDensityWeight_sq`); the
centered flow is an `L²` isometry for the weight `exp t` (`integral_exp_mul_normSq_centeredFlow`);
and any continuous weight for which the centered flow preserves interval masses is a constant
multiple of `exp t` (`weight_eq_exp_of_flow_isometry`). So the Deninger–Singhof polarization density
of addendum (iv) and the corpus's half-density completion are one weight, seen in `L²` and in `L¹`.
Its Mellin dual is the critical line: `L²((0,∞), du)` is carried by the Mellin transform onto
`L²(Re s = ½)`, which is the classical reason the unitary spectrum of dilations is the line.

**Completion dichotomy (synthesis of corpus theorems).** Let `H` be a completion of the literal
Meyer cohomology on which the centered flow acts by bounded operators.
1. If `H` is a Hilbert space with unitary flow diagonalised by Mellin against an absolutely
   continuous spectral measure (the `L²(du)` completion, or any weighted `L²` on the line such as
   the Calderón trace norm `∫|F(½+iτ)|²/|τ| dτ` of the leaf modes), the flow has no eigenvectors
   (`HTGeometry.DilationSpectralType`) and no zero evaluation is continuous: the zeros are
   resonances, not eigenvalues, and no Hodge structure with the zeros as `Θ`-eigenvalues exists on
   `H`.
2. If `H` is a Hilbert space on which some zero evaluation is a continuous transpose
   eigenfunctional of the unitary flow, that zero is on the line
   (`re_eq_half_of_unitary_transposeEigenfunctional`); a Hilbert completion carrying all zeros as
   eigen-characters is the Weil `ℓ²` over the divisor (`XiWeilLineConjHilbert`) and exists as a
   polarised structure exactly under RH.
3. If `H` is the `L¹` half-density completion, the on-line evaluations are continuous and the
   off-line ones are unbounded (`riemannHypothesis_iff_deningerMeyerHalfDensityXiEvaluationsBounded`),
   but `H` has no inner product, so no polarisation positivity can be stated on it; the Hodge star
   of the leaf modes is the Hilbert transform `i·sgn μ`, which is not bounded on `L¹`.

Hence no completion of the arithmetic Meyer cohomology carries simultaneously a positive
polarisation and the zeros as continuous spectrum, unless RH holds already. The Deninger–Singhof
polarised Hodge structure, if it exists for `Spec ℤ`, lives on the literal (uncompleted)
cohomology, and its positivity is the Weil form on the divisor. This is MUST-138; it closes the
"extended `L²`-Hodge" reading of the gate `DAC_ARITHMETIC_CALDERON_GREEN_INTERMEDIATE_EXTENSION`
as a receiver and confirms the corpus's earlier verdict ("Deninger weight-one polarisation: axioms
⟺ Re = ½", five-lanes-one-wall) from the completion side.

**Verdict on the F₁ lane.** Its transverse data (`du`), leafwise complex structure (Hilbert
transform in the Kronecker direction, invariant under the positive dilations of the deck group and
the flow, `deningerFreqSign_pos_mul`), local positivity (`deningerMode_cupStar_pos`) and trace
weight are all canonical; the lane produces no positivity beyond the local modes. Further work on
completions or leafwise metrics is theatre. The producer question is the one the corpus already
names: a positivity-preserving regularisation of the prime-side Gram forms.
