# Multiplicity-parity ladder RH_{2^k}: the route map and the Kramers reading of the base rung

- **ID:** multiplicity-parity-ladder-route
- **Stage:** 1-in-progress
- **Type:** RESEARCH MAP + THEOREM (Lean, bricks) + CONJECTURE (mechanism program)
- **Source:** `formal/GaloisForLFunctions/RHTower/` ladder stack (`RiemannTower`, `RHLadderTheory`,
  `RHCharacterizations`, `GermExtension`, `EMAnnulusSupply`, `EquivariantRootDissolution`) ·
  new bricks `LadderLattice.lean`, `SymplecticMultiplicity.lean`
- **Statement:** RH filtered by order-divisibility — rung `k` = "every off-line ξ-zero has order
  divisible by `2^k`" — is governed by a single natural invariant (the off-line order gcd), breaks
  at one sharp finite level if it breaks at all, and its base rung is equivalent to a quaternionic
  (symplectic Kramers) symmetry on finite-dimensional models of the local divisor.

## Goal

Determine what a proof of any rung `k ≥ 1` must look like, bank every structural theorem the rung
already forces, and isolate the open core as a construction problem rather than an estimate. The
literature's multiplicity program runs in the opposite direction (simplicity of on-line zeros:
Levinson, Conrey, Montgomery pair correlation); an order-divisibility filtration of RH with a
cofinal sufficiency criterion is not a posed program there, so the route is native ground.

## The object

`RHLadder k : ∀ ρ, Re ρ > ½ → ξ(ρ) = 0 → 2^k ∣ ord_ρ(ξ)`. Banked equivalences (all Lean,
axiom-clean): rung `k` ⟺ analytic `2^k`-th root of ξ on `Re s > ½` (`rhLadder_iff_root`) ⟺
extension of the Euler-side root germ from `Re s > 1` (`rhLadder_iff_germ_extends`) ⟺ deck-charge
triviality ⟺ line holography ⟺ window certificates (`rhLadder_tfae`); RH ⟺ all rungs
(`rh_iff_forall_ladder`) ⟺ cofinally many (`rh_of_rhLadder_cofinal`). RH₂ = rung 1 = "ξ is a
square on `Re s > ½`" (`rhLadder_one_iff_sqrt_rightHalf`, `rh2_tfae`).

## The governing invariant [PROVED HERE, paper; Lean encodes it without naming it]

Let `D := gcd { ord_ρ(ξ) : ρ off-line zero } ∈ ℕ`, with `gcd ∅ = 0`. Then the whole route is the
divisibility profile of this one natural number: rung `k` ⟺ `2^k ∣ D`; the divisor-lattice ladder
(below) at modulus `n` ⟺ `n ∣ D`; RH ⟺ `D = 0`; the sharp level is `v₂(D)`. A proof of rung 1 is
exactly a proof that `D` is even; RH is the statement that the constraint kills `D` outright.

## New Lean structure banked by this card (all axiom-clean, in the umbrella)

`LadderLattice.lean` — the order-theoretic completion of the route:

- `OrderLadder n` — the ladder over the full divisor lattice `(ℕ, ∣)`; antitone
  (`orderLadder_of_dvd`); the dyadic ladder is its cofinal chain (`orderLadder_pow_two`).
- `orderLadder_zero_iff_rh` — **the lattice top `n = 0` IS RH**: `0 ∣ ord` forces `ord = 0`,
  i.e. no off-line zero. RH sits inside its own filtration as the terminal modulus.
- `rh_of_orderLadder_unbounded` — moduli of unbounded size suffice, no divisibility relations
  among them required.
- `sharpLevel` = least 2-adic valuation of an off-line order; `forall_rhLadder_or_sharp` — **the
  sharp dichotomy**: the truth set of the dyadic ladder is `ℕ` (RH) or exactly the initial
  segment `{k ≤ sharpLevel}`, first failure at `sharpLevel + 1` (`not_rhLadder_succ_sharpLevel`);
  `not_rh_iff_exists_sharp`; `rh_iff_rhLadder_unbounded`; `rh_iff_setOf_rhLadder_infinite` — the
  cofinal criterion upgraded to pure cardinality.

`SymplecticMultiplicity.lean` — the Kramers reading of the base rung:

- `even_finrank_maxGenEigenspace` — **even multiplicity from symplectic self-adjointness**: a
  finite-dimensional complex endomorphism self-adjoint for a nondegenerate alternating form has
  every algebraic multiplicity even, at real and non-real eigenvalues alike (generalized
  eigenspaces are pairwise orthogonal for the form; the restricted form is alternating
  nondegenerate; odd skew determinants vanish). As linear algebra this is classical (skew-pencil
  normal form; in non-Hermitian physics: Kramers pairs of class AII†) — `[SEARCH]` as mechanism,
  machine-checked here as a brick.
- `rhLadder_one_iff_symplecticRealization` — **RH₂ ⟺ at every off-line zero the vanishing order
  is the algebraic multiplicity of a symplectically self-adjoint endomorphism**. Parity of a
  vanishing order = existence of a quaternionic symmetry on a finite-dimensional model of the
  local divisor. The minimal counterexample to RH₂ is a 1-dimensional off-line root space, and
  1-dimensional spaces carry no symplectic form — the mechanism excludes exactly the minimal
  violation.

## Reframes of the rung, with registers

1. **Continuation** `[PROVED, banked]`: rung `k` ⟺ the arithmetically given germ (the
   `ζ^{1/2^k}`-dressing Dirichlet series, convergent on `Re s > 1`) continues analytically across
   the zero field to `Re s > ½` (`rhLadder_iff_germ_extends`). The constraint is continuability,
   not any estimate.
2. **Closure** `[BRIDGE, paper]`: even-order divisors are stable under locally uniform limits
   (zero-counting on small circles passes to the limit and even integers are closed), so the
   square class in `𝒪(Re s > ½)` is closed; hence RH₂ ⟺ ξ lies in the closed set of analytic
   squares. Voronin universality cannot decide this: it approximates targets on zero-free
   compacta only, and the obstruction sits exactly at the zeros. The approximation reframe is
   exact; the classical approximation tool is blind to it.
3. **Quantitative** `[KNOWN ingredient + banked ladder, paper]`: `ord_ρ ≪ log(2 + |Im ρ|)`
   (Jensen), so rung `k` forbids off-line zeros below height `exp(c·2^k)` — each rung is a
   doubly-exponential-height off-line-free certificate, and the cofinal criterion recovers RH
   quantitatively. Conversely no finite-height verification yields any rung: the two filtrations
   (height-truncated RH, divisibility rungs) are transverse.
4. **Kramers/operator** `[PROVED HERE, Lean]`: reframe 4 = `rhLadder_one_iff_symplecticRealization`.
   Hilbert–Pólya asks for a real structure forcing spectrum location; the parity ladder asks for
   a quaternionic structure forcing multiplicity parity — a different operator-theoretic axis,
   strictly weaker per rung, exhausting RH in the limit.

## The walls (banked; a rung proof must respect all four)

- **Class no-go** `[PROVED, banked]`: the shape class {FE + Schwarz + growth} contains members
  with simple off-line zeros (orbit-quartic planting: `TailBlindness`,
  `FiniteDivisorPrefixNonselection`). Any rung proof must consume the Euler product/arithmetic
  beyond the shape class.
- **Reader no-go** `[PROVED, banked]`: every reflection-invariant parity reader sees only paired
  totals — the symmetry quadruple carries total weight `4·ord`, mod-2 trivial
  (`quadruple_weight_parity_refuted`, `LandauShadowNoGo`, `DeciderBarrier`). The proof must read
  a single quadruple member, i.e. break the Schwarz pairing locally.
- **Equivariant dissolution** `[PROVED, banked]`: the Real (σ-equivariant) tower off the line is
  the plain ladder verbatim (`rhLadder_iff_equivariant_offline_root`); the seam sign adds only
  boundary/annular data. No refinement of the rung hides in equivariance.
- **Antiunitary catalogue** `[PROVED HERE, paper]`: an antilinear `J` commuting with an operator
  pairs the eigenvalue `λ` with `λ̄` and cannot fix a non-real eigenvalue; the transpose-type
  intertwining `J K J⁻¹ = K^†`-adjoint (class AII†) is the unique (anti)unitary shape whose
  induced pairing fixes `λ` — it sends right root vectors to left root vectors at the same
  eigenvalue, and `J² = −1` makes the Keldysh right–left pairing symplectic. AII† is therefore
  THE symmetry class of this route; commuting-type symmetries are structurally blind (they are
  the reader no-go in operator clothing).

## The program (conjecture stack)

- `[CONJECTURE]` **Seam-anomalous quaternionic realization.** There is an operator model of ξ's
  divisor built from arithmetic data (the HS/Schatten substrate is in-tree) carrying an
  antiunitary `J`, `J² = −1`, intertwining the operator with its transpose up to a defect
  supported on the critical line. Off the line the Keldysh–symplectic mechanism then forces even
  multiplicity — rung 1. On-line odd zeros are exactly the `J`-anomaly, localized on the seam:
  the operator restatement of "escapes happen in pairs" (seam-sign shadow).
- `[PROVED HERE, Lean]` **Clifford filtration of the ladder** (upgraded from conjecture;
  `CliffordMultiplicity.lean`, axiom-clean). Rung `k` ⟺ at every off-line zero the vanishing
  order is the algebraic multiplicity of an endomorphism commuting with `2k` anticommuting
  complex structures (`rhLadder_iff_cliffordModel`). Mechanism: `2k` anticommuting complex
  structures force `2^k ∣ dim` (`pow_dvd_finrank_of_anticomm`, the halving induction on the
  `i`-eigenspace of `J₁` with the residual family `J₂Jⱼ`), and commuting structures preserve
  generalized eigenspaces (`pow_dvd_finrank_maxGenEigenspace_of_anticomm`). Converse: scalar
  model on the doubled `Cl`-module (`AnticommSpace.base`/`double` — the module face of
  `Cl_{n+2} ≅ Cl_n ⊗ M₂`, matching the Kummer squaring law). Tower coherence: forgetting
  generators restricts level `k` to every lower level (`CliffordModel.restrictLevel`,
  `cliffordModel_mono`), mirroring `rhLadder_of_succ`. Capstones: `rh_iff_forall_cliffordModel`
  — **RH ⟺ Clifford models at every level** — and `rh_of_cliffordModel_cofinal` (unboundedly
  many levels suffice). The cofinal criterion is now literally: an unbounded emergent Clifford
  tower on finite-dimensional root spaces forces the off-line spectrum empty. Constraint-side
  throughout: symmetry-algebra size against finiteness; no flow, no deformation parameter.
- `[CONJECTURE, moonshot — gear-train/plumbing collision]` **Wu-characteristic reading.** Equip
  the weld surface's divisor lattice with the arithmetic linking form (prime-braid/tropical
  linking, in-tree) and conjecture the critical line is its characteristic element: a Wu-type
  identity `x·x ≡ x·(line) (mod 2)` would force every off-line divisor component even while
  permitting odd orders only on the line. Gear image: a closed train of meshing gears needs an
  even cycle or it jams; the line is the unique rack allowed odd teeth.

## Attack record (killed this pass)

- Divisible-character rigidity (extend the mod-2 monodromy character to a 2-divisible arithmetic
  group, forcing triviality): the only extension datum available is the Euler-side germ, whose
  continuation IS the rung — circular. Kept only as the localization "the obstruction is
  emergent/non-factorwise" (each completed Euler factor has a full Kummer tower,
  `WeldTowerFree`).
- Jet/discriminant hyperbolicity (orders even because ξ is a discriminant of a hyperbolic
  family): dies at non-real points exactly as `SpurNoGo` records for one-pair preservation.
- Quadratic-twist arithmetic squares: `ord_ρ(ζ_K) = ord_ρ(ζ) + ord_ρ(L)` is additive; no parity
  coupling at a shared point is forced by any known factorization.

## Gates

- [x] 0 → 1  in-progress: route map complete; invariant named; walls banked; mechanism bricks
      formalized (`LadderLattice.lean`, `SymplecticMultiplicity.lean`, lint green, axiom-clean)
- [x] Stage-1 bricks 1→2→3 (mechanism/bridge/coherence): Clifford rung-`k` mechanism, rung-`k`
      bridge `rhLadder_iff_cliffordModel`, and level restriction all proven and formalized in
      `CliffordMultiplicity.lean` (lint green, axiom-clean); the k = 1 symplectic and Clifford
      readings coexist as independent operator faces of the same rung
- [ ] 1 → 2  fully-proven (route level): the closure reading's limit-parity lemma written; any
      construction progress on the seam-anomalous `J` (Stage 2, the open core)
- [ ] 2 → 3  formalized (route level): whatever Stage-2 structure survives on paper
- [ ] 3 → 4  publication-ready

## Open core

`[OPEN CORE]` Any rung `k ≥ 1`. Localized by this card: construct, from Euler data, a symplectic
structure on an operator model of the off-line divisor whose anomaly is line-supported — the
parity-weakening of Hilbert–Pólya. Every ingredient except the arithmetic construction is now a
theorem.

## Stage 2 — gate analysis (divisor model, symmetry, anomaly, non-circularity)

**Gate 4 (divisor model): PASSED, in two forms.**

- Canonical analytic model `[BRIDGE]`: the banked window factorization (`xi_ball_factorization`)
  gives `𝒪(B)/(ξ) ≅ ⊕_w ℂ[z]/((z−w)^{m_w})` with multiplication-by-`s` as the operator —
  eigenvalues the window zeros, algebraic multiplicities the orders. The single-zero local piece
  is the in-tree `LocalDivisorJet` (`SigmaDivisorJet.lean`). Standard commutative algebra.
- Arithmetic-member model `[PROVED, banked]`: `EMSplitData` (`EMAnnulusSupply.lean`) supplies at
  every strip point a finite hole space of the explicit completed Euler–Maclaurin member with
  hole count = the central vanishing order (`emSplitData_count_eq`), and
  `rhLadder_of_em_split_multiplicity` already transports every rung to this model. The window
  dimension is arithmetic data; no divisor is read.

**Gate 5 (symmetry): two walls now stand, one of them new and machine-checked.**

- `[PROVED HERE, Lean]` **The cyclic no-go** (`SymplecticCyclicObstruction.lean`): every
  `K`-invariant bilinear form on a module with a cyclic vector is symmetric
  (`invariant_bilin_symm_of_cyclicVector` — on iterates the form reads only `i + j`); hence an
  alternating invariant form vanishes and a symplectic structure forces ≥ 2 channels
  (`not_cyclicVector_of_symplectic`). Sharpened to root spaces: for symplectically self-adjoint
  `K` **no nontrivial generalized eigenspace admits a cyclic vector**
  (`restrictMaxGen_no_cyclicVector_of_symplectic`) — beyond even multiplicity, single Jordan
  blocks are excluded at every eigenvalue. Consequence: the canonical local divisor model is
  cyclic, so **the J can never live on the analytic local model**; the second channel must come
  from elsewhere. (Commutative-algebra face `[SEARCH]`: on a Gorenstein quotient all invariant
  forms are residue forms `φ(fg)`, automatically symmetric.)
- `[PROVED-shape, paper]` **FE-doubling blindness.** The one unconditional arithmetic doubling —
  carrier `𝒪(B_ρ)/(ξ) ⊕ 𝒪(B_{1−ρ})/(ξ)` over a window and its functional-equation mirror,
  `K = (mult s) ⊕ (mult (1−s))`, `ω` the residue pairing crossed with the FE pullback — is
  symplectic with `K` self-adjoint and eigenvalue `ρ` of multiplicity `2m`. It models the
  *paired* divisor, even unconditionally: the reader no-go in operator clothing. (The Lean
  converse constructions already certify that doubled-multiplicity realizations are free.) Any
  J built by mirror pairing proves nothing; the J must fix a single quadruple member.

**Gate 6 (anomaly localization): collapse on analytic carriers; automatic on balanced ones.**

`[PROVED-shape, paper]` **The Smith-balance reduction.** For any 2×2 holomorphic presentation
`ξ = det M` on a window, the cokernel model splits by the local Smith form:
`coker M ≅ 𝒪/(d₁) ⊕ 𝒪/(d₂)` with `d₁ = gcd(entries of M)`, `d₁d₂ = ξ`. Define the **balance
defect** `β_M(ρ) := v_ρ(d₂) − v_ρ(d₁) ≥ 0`; then `β_M(ρ) ≡ ord_ρ(ξ) (mod 2)`, and a symplectic
self-adjoint structure exists on the cokernel model at `ρ` iff `β_M(ρ) = 0`. Consequences:

- at an odd-order zero balance is impossible — **the anomaly is canonically supported on
  odd-order zeros; it cannot leak**: gate 6 is automatic in this frame;
- rung 1 ⟺ some window-wise presentation has `β_M = 0` at every off-line zero (forward: balance
  forces even order; converse: a local square root yields a balanced diagonal presentation);
- if `M` is built from ξ's own analytic germ, balance at `ρ` ⟺ the Weierstrass factor is a
  square ⟺ the rung locally — circularity located exactly. The route lives or dies on
  presentations whose entries have independent arithmetic identity.

**Gate 7 (non-circularity): sharpened.** The demand is now precise: exhibit an arithmetic 2×2
presentation `ξ = det M` — entries from the Eisenstein/theta/Hecke side, not from any square
root of ξ — and prove off-line balance of the entry gcd from the entries' own relations (their
functional equations, multiplicativity), never from ξ's divisor. The rung becomes a statement
about the **common vanishing divisor of four explicit arithmetic functions** rather than the
parity of one function's divisor — the meander cut: re-presenting the single channel as a
determinant exposes an inner gcd channel that analysis of ξ alone does not see.

**Surviving candidates for the presentation** (all `[CONJECTURE]`, novelty-gated):

- (C1) **Metaplectic/theta carrier.** The two channels = the even/odd components of the Weil
  representation; the metaplectic deck element acts by −1 on the genuine part — an arithmetic
  germ of `J² = −1` — and ξ is the Mellin transform of θ. Structural rhyme: Waldspurger converts
  "central L-value is a square" through the metaplectic correspondence; the rung asks for the
  function-level analogue on the right half-plane. Euler input: half-integral Hecke theory acts
  through `T(p²)` — the square-index substructure the germ `ζ^{1/2}` already displays.
- (C2) **Eisenstein/Maass–Selberg Gram presentation.** Truncated Eisenstein inner products give
  2×2 Gram matrices with ξ-combinations as determinants and the scattering unitarity axis on
  the critical line. The location program through scattering is classical and closed
  (Lax–Phillips, `[SEARCH]` — do not re-run); the balance question about local Smith forms of
  these Grams at off-line points is not posed there.
- Falsification branch: a **channel-rigidity theorem** — every arithmetic functor of window data
  factors through cyclic-or-mirror-doubled carriers — would convert the route into a no-go
  (multiplicity parity inaccessible to operator symmetry), itself promotable.

**The half-bound and the shape classification** `[PROVED-shape, paper]`. For a 2×2 presentation
over the local ring at `ρ`, `v(d₁) = min entry order` and `v(det) ≥ 2·(min entry order)`, so
**the entry gcd can never exceed half the determinant order**; balance is exactly achievement of
the half bound, and then some determinant-achieving diagonal has entry orders exactly
`(m/2, m/2)`.  Consequently every balanced presentation contains, on its achieving diagonal, a
local factorization of ξ into two factors of equal order — and conversely such a factorization
gives the diagonal presentation.  Balanced 2×2 presentations and equal-order factorizations are
the same object.

**Wronskian kill** `[PROVED-shape, paper]`.  Presentations `M = [[u, v], [u', v']]` (so
`ξ = W(u,v)`) can never balance at a zero: the derivative drop `v(u') = v(u) − 1` (whenever
`v(u) ≥ 1`) is incompatible with all four entries reaching the half bound `m/2 ≥ 1`.  Derivative
and Wronskian shapes are excluded as rung certificates.

**The twin theorem** `[PROVED HERE, Lean]` (`TwinFactorization.lean`, axiom-clean):

> `rhLadder_one_iff_twinFactorization` — **RH₂ ⟺ ξ admits a twin factorization on
> `Re s > ½`**: analytic `a, d` with `a·d = ξ` pointwise and `ord_ρ(a) = ord_ρ(d)` at every
> right-half point.

The square root is the diagonal twin `a = d`; the format's gain is that the twins may differ —
as functions and in their divisors — on the critical line, so the line anomaly (gate 6) is
built into the format rather than demanded of a symmetry.  Consistency against the class wall:
for orbit-quartic counterexamples twins simply fail to exist; the format proves nothing
vacuously.  The mirror twin `(f(s), f(1−s))` is not automatically equal-order (it demands
`v_f(ρ) = v_f(1−ρ)` — the reflection reader again): no gain from reflection, as the walls
require.

**Stage-2 verdict, gate by gate.**

- Gate 4 (divisor model): **CLOSED — constructed/found** (canonical window model banked;
  EM-member arithmetic model banked with rung transport).
- Gate 5 (symmetry): **CLOSED productively — impossibility plus equivalent reformat, both
  machine-checked.**  A J on ξ-derived analytic carriers is impossible (cyclic no-go, Lean;
  mirror blindness, paper); on 2×2 carriers the symmetry demand is equivalent to balance, and
  balance to twins; the Lean twin theorem replaces "construct J" by "construct twins" with no
  loss.
- Gate 6 (anomaly localization): **CLOSED structurally** — in the twin/balance format the odd
  anomaly is automatic (`β ≡ ord mod 2`; twins constrained only off the line); leakage is
  impossible by format, not by engineering.
- Gate 7 (non-circularity): **OPEN — this is the route's entire remaining content, now in
  sharpest form.**  Construct arithmetic twins not built from `√ξ`.  Equivalent
  Dirichlet-series form: a convolution splitting `𝟙 = α ∗ δ` with `α ≠ δ` allowed, whose two
  L-series continue to `Re s > ½` with equal divisors (the square-root germ is the diagonal
  splitting `α = δ = d_{1/2}`; the twin format opens the full unit group of Dirichlet series).
  Kill-list so far: Wronskian/derivative shapes, mirror twins, `√ξ`-diagonal.  Live candidates:
  metaplectic/theta even–odd channels (exact ingredient needed: the entries of the metaplectic
  Eisenstein scattering data on the double cover — a formula-level literature verification,
  recorded, not yet performed), Eisenstein/Maass–Selberg Grams (balance question new there),
  and non-diagonal convolution splittings with forced divisor equality.

## Log

- 2026-07-11 — created in 1-in-progress; divisor-lattice + sharp-level + Kramers bricks banked in
  Lean; walls consolidated from banked no-gos; program stack stated.
- 2026-07-11 — Stage-1 bricks closed: `CliffordMultiplicity.lean` proves the rung-`k` mechanism
  (halving induction), the bridge `rhLadder_iff_cliffordModel`, the doubling existence
  construction, level coherence, and the capstones `rh_iff_forall_cliffordModel` /
  `rh_of_cliffordModel_cofinal`. Every rung of the ladder now has an operator-symmetry
  characterization; the route's remaining content is entirely Stage 2 (the arithmetic
  construction) and Stage 3 (escalation).
- 2026-07-11 — Stage-2 gate analysis complete: gate 4 passed (canonical + EM-member models);
  cyclic no-go proven and formalized (`SymplecticCyclicObstruction.lean` — invariant forms on
  cyclic modules are symmetric; no lone Jordan channel for symplectic self-adjoint operators);
  FE-doubling blindness and Smith-balance reduction on paper; the open core relocated to the
  balance defect `β_M` of arithmetic 2×2 presentations. Sonin/HS carriers assessed: they are
  analytic window functors, hence subject to the cyclic/mirror walls — a J there must import an
  arithmetic second channel first.
- 2026-07-11 — Stage-2 constructions executed: half-bound/shape classification and Wronskian
  kill on paper; the twin theorem formalized (`TwinFactorization.lean`,
  `rhLadder_one_iff_twinFactorization`, axiom-clean, lint green).  Gates 4–6 closed
  (constructed / impossibility-plus-reformat / structural); gate 7 is the open core in final
  form: arithmetic twins ⟺ non-diagonal convolution splitting `𝟙 = α ∗ δ` with equal continued
  divisors.

## Next move

Attack gate 7 through the convolution-splitting form: characterize which unit-group splittings
`𝟙 = α ∗ δ` can have BOTH L-series continue past `Re s = 1` (the Euler-side constraint on
`(α, δ)` — multiplicativity forces local splittings `(1 − p^{-s})^{-1} = a_p(s)·d_p(s)` and the
continuation demand couples them across `p`); the first structural theorem to try is a rigidity
statement — either every admissible splitting is diagonal-up-to-units (route converts to a
no-go with the rigidity theorem as the promotable residue) or the admissible space is a torsor
whose parametrization names the Stage-2 object.  In parallel: the metaplectic scattering-entry
lookup, and in Lean the `2^k`-fold equidivisor factorization generalization of the twin theorem.

## 2026-09-02 — Gate 7 rigidity (paper + Lean): the non-diagonal freedom is empty

**Twin rigidity theorem** `[PROVED HERE, Lean: TwinRigidity.lean, axiom-clean]`. Let `(a, d)` be
any twin factorization of ξ on `Re s > ½`. Equal orders make `q := a/d` an analytic nonvanishing
function on the half-plane (`localQuotientOn_analytic_nonvanishing_factorization`); the
half-plane is simply connected, so `q` has an analytic square root `v`; then `g := d·v`
satisfies `g² = d² q = d·a = ξ`, with `a = g·v` and `g = d·v` (`twin_eq_sqrt_mul_unit`).
Conversely `(g v, g/v)` is a twin for every root `g` and every analytic unit `v`
(`twinFactorization_of_sqrt_mul_unit`). Hence the twin set is empty or a torsor under the
analytic units of the half-plane over the diagonal twin (`twinFactorization_iff_exists_sqrt`).

**Consequence for the "Next move".** The dichotomy posed there is settled on the first branch:
every admissible splitting `𝟙 = α ∗ δ` with both L-series continuing to `Re s > ½` with equal
divisors is diagonal up to units — the L-series of `α` is a square root of ξ (up to the Γ- and
polar factors) times a unit. Non-diagonal twins therefore carry no information beyond the
existence of the root; the "meander cut" exposes no inner channel that the root does not
already contain. Gate 7 reduces, without loss, to: **construct an analytic function on
`Re s > ½` whose divisor is half of ξ's, from arithmetic.**

**Why no known arithmetic object can be that function.** L-functions are multiplicative under
direct sums of motives, `L(M ⊕ N) = L(M)·L(N)`, and the trivial motive `𝟙` is simple, so no
motivic `(M, N)` has `L(M)L(N) = ζ` except `{𝟙, 0}`; a half-divisor object is not the L-function
of any motive. The half-integral-weight (metaplectic) objects of candidate (C1) square to
integral weight, so they can present ξ as a product of *two different* factors only in the
form `g v · g/v` above, i.e. only after a square root of ξ already exists; Waldspurger's squares
are squares of *values*, not of functions. The Maass–Selberg Grams of candidate (C2) have
determinants built from `ξ(2s), ξ(2s−1)` and their balance at an off-line point is, by the
twin theorem, again a square root of the same local factor. The only remaining arithmetic
candidates are the Selberg–Delange powers `ζ^{θ}`, whose continuation past the zero field is
the rung itself (reframe 1). The open core is therefore irreducible in the present corpus:
no linear, family, motivic, metaplectic, or Gram construction produces a half-divisor.

**Status of the open core.** Not solved. It is now known to be exactly the statement "ξ has
an analytic square root on `Re s > ½`" with every proposed reformulation proved equivalent
(root ⟺ germ extension ⟺ twins ⟺ Clifford models ⟺ symplectic realizations), and every
proposed producer (cyclic carriers, mirror/family doubling, quadratic symbols, non-diagonal
twins, motivic halves) proved either impossible or equivalent to the root. A proof must supply
a non-linear arithmetic construction of a half-divisor object; MUST-125/126 record the
constraint. Related Lean this pass: `HTGeometry.SymplecticDoublingFree` (doubling is free;
`{±1}` skew pairings are symmetric), complementing `SymplecticCyclicObstruction`.

## 2026-09-02 — Fixed theta determinant carrier: one-chain no-go and surviving parity character

The fixed Hedenmalm theta source is a genuine arithmetic carrier, not an abstract model:
`thetaSourceEntireDet2_eq_XiC_normalized` identifies its regularized determinant with normalized
`XiC`, and `finrank_thetaRootBlock_at_XiSupport` identifies each complete generalized root-block
dimension with exact Xi multiplicity. It therefore gives the strongest available test of the
report's proposed “2×2 arithmetic presentation”.

The test is negative in the proposed Kramers form. Source ODE uniqueness already gives
`finrank (ker N_mu) = 1` for the nilpotent part of every nonzero root block. New theorem
`exists_cyclicVector_thetaRootNilpotentPart` upgrades the coordinate-free nilpotency-index law to
a literal cyclic vector: every actual theta root block is one complete Jordan chain. Combining
this with `SymplecticCyclicObstruction` yields
`thetaRootBlockOperator_not_symplectically_selfAdjoint`: no nondegenerate alternating bilinear
form can make the actual restricted theta operator self-adjoint. Functional-equation reflection
pairs distinct `mu` and `-mu` blocks; it does not create a second channel at one spectral point.

**Positive survivor.** Xi multiplicity is exactly the length of this single arithmetic Jordan
chain. Reflection acts on its nonzero terminal conormal current through the computable scalar
`thetaDepthCharacter(mu) = (-1)^(dim ThetaRootBlock(mu)-1)`. At an Xi support point this is
`(-1)^(ord_rho(Xi)-1)`. Hence base rung is now equivalent, on this concrete carrier, to the
source-native sign law `thetaDepthCharacter = -1` at every right-half support point. Any viable
theta-source proof must force that sign from prime/source data; adding a formal symplectic double
cannot do it. If no such source law exists, fixed determinant carrier is retired with the
single-chain classification as its positive salvage.

Lean: `HedenmalmThetaRootBlockCyclicNoGo.lean`; targeted `lake build` succeeds; theorem axiom
audit contains only `propext`, `Classical.choice`, and `Quot.sound`. Full formal lint is blocked
only by pre-existing unrelated unreachable modules in the dirty worktree; this module is wired
into `RHTower.lean`.

The surviving sign interface is now formalized exactly in
`HedenmalmThetaDepthCharacterLadder.lean`:
`thetaDepthCharacter_eq_neg_one_iff_even_multiplicity` and
`rhLadder_one_iff_thetaDepthCharacter_eq_neg_one_rightHalf`. Targeted build succeeds and axiom
audit is clean modulo Lean foundations. Corpus audit of `HedenmalmThetaSourcePrimeModularCurrentField`
shows prime-modular dilations commute with the conormal current for both character values; dense
off-wall dilation spectrum therefore does not select `-1`. This closes prime-dilation covariance
as a parity producer while preserving the depth character as exact open source invariant.

## 2026-09-02 — Report audit: reflected-pair and Clifford-successor type mismatches

The report's proposed 2×2 Kramers step fails on the actual theta carrier for a second, independent
reason. `thetaSpectrumNeg_ne` proves functional-equation reflection fixes no nonzero source
spectral point. On the direct sum of the `mu` and `-mu` blocks, the canonical quarter-turn squares
to `-1`, but `thetaReflectedRootPairQuarterTurn_anticommutes` proves it anticommutes with the
block-diagonal theta operator. It exchanges distinct spectral sectors rather than preserving the
generalized eigenspace at `mu`. The paired dimension is always `2 * ord_rho(Xi)` and hence even
for every possible local order (`finrank_thetaReflectedRootPair_at_XiSupport_even`). This evenness
is tautological inter-block doubling and supplies no parity information about `ord_rho(Xi)`.

The claimed Clifford induction has a separate exact dimension mismatch. The corpus only proves
the downward map `CliffordModel (k+1) rho -> CliffordModel k rho`. The public construction
`AnticommSpace.double` replaces `V` by `V × V`; new theorem
`finrank_anticommSpace_double_ne_xi_order` shows that, at every Xi zero, doubling an exact
multiplicity space cannot retain the same fixed analytic order. Thus the named doubling functor
does not upgrade rung `k` to rung `k+1`; it doubles the object being measured. A genuine upward
step would need two new commuting Clifford generators on the unchanged root block, which is
exactly the additional `2^(k+1)`-divisibility claim.

Lean: `HedenmalmThetaReflectedPairParityBlindness.lean` and
`CliffordSuccessorDoublingMismatch.lean`; direct checks and targeted builds succeed. Axiom audits
contain only `propext`, `Classical.choice`, and `Quot.sound`.

The report's differential-Galois veto is also contradicted by existing axiom-clean corpus
theorems. `hypertranscendental_finiteQuartetWardIndex_law` constructs hypertranscendental entire
functions with functional-equation and Schwarz symmetries and arbitrary finite off-critical
quartet packets. More concretely, `reflectedGammaQuartetCarrier_hypertranscendental` coexists with
`reflectedGammaQuartetCarrier_offCentral_cosh_zero`. Hypertranscendence therefore cannot by itself
forbid off-line quartets. The cited
`isomonodromy_of_no_riccati_of_differentialSolution` additionally requires a full difference
system, algebraic-extension basis, separating Galois specializations, sigma-simplicity, no base
Riccati solution, fundamental matrix and scalar differential-jet constraint; no Xi-quartet-to-
those-hypotheses bridge appears in the corpus.

## 2026-09-02 — Leading-Xi-jet orientation cancels terminal-depth parity

The next source-orientation candidate is also closed. The actual on-shell Xi Wronskian is
reflection-odd, while the terminal theta current transforms by
`thetaDepthCharacter = (-1)^(m-1)`. This looks capable of forcing the desired value `-1` until
the coefficient retained by any coefficient-faithful comparison is included: the first nonzero
Xi jet transforms by `(-1)^m`. For every positive multiplicity,

`(-1)^m * (-1)^(m-1) = -1`.

Thus leading-coefficient-weighted terminal current is reflection-odd for every multiplicity,
including odd multiplicity. Its oddness is an identity forced by functional equation, not a parity
selector. Dividing out leading coefficient recovers bare depth character but discards source
orientation whose oddness was meant to prove it. This closes equation-Wronskian, first-nonzero-jet,
and coefficient-normalized determinant-line orientation as base-rung producers.

Lean: `HedenmalmThetaXiJetParityCancellation.lean` proves
`xiJetParity_mul_thetaDepthCharacter_eq_neg_one` and
`ccmRationalAdelicPrimeXiCartierCoefficient_reflection_mul_thetaDepthCharacter`. Both are
unconditional actual-Xi statements. Direct Lean check and targeted build succeed; axiom audit
contains only Lean foundations.

Novelty audit: corpus search found no prior theorem composing the two exact parity laws. External
literature remains orthogonal: Alpöge--Furman (arXiv:2608.13637) proves unconditional density of
simple on-line zeros, while Ivić (arXiv:math/0501434) bounds possible multiplicities. Neither
constructs a half-divisor nor constrains parity of hypothetical right-half zeros.

## 2026-09-02 — Exact half-divisor must be intrinsically half-plane-local

Squarefree Fisher conormal data does not supply the missing parity. Its quotient is exactly a
pointed logarithmic derivative `2 B'/B` plus a regular connection term, so its residue is `2m`.
The reflection-charge construction subsequently squares `m`. Both operations retain multiplicity
magnitude but erase its class modulo two. Burnol doubled-window conormal tomography likewise
divides out the common leading jet and recovers horizontal spectral position, not multiplicity
parity. These are receivers, not an arithmetic half-divisor producer.

Hardy's already-formalized sign flips give a sharper restriction on the exact target. There are
critical-line Xi zeros of odd analytic order above every height. At such a point no analytic germ
can square to Xi, since squaring doubles local analytic order. Therefore Xi has no globally entire
square root. More strongly, every hypothetical square root on `Re s > 1/2` is necessarily
non-entire and cannot arise by restricting any entire arithmetic determinant or Pfaffian.

**Closed search class.** Global entire determinant/Pfaffian candidates for the requested `g` are
impossible. Doubling a carrier produces a square of Xi and is parity-blind; retaining one copy of
Xi meets unavoidable odd-order seam zeros. A viable construction must be single-valued on the
strict right half-plane yet carry boundary branching at arbitrarily high critical-line points.

**Positive survivor.** The boundary singularity is now an exact specification, not a heuristic:
`RHLadder 1` is equivalent to existence of a right-half square root that is provably non-entire.
This leaves unchanged the sole open edge: construct that intrinsically half-plane-local arithmetic
root, equivalently force `thetaDepthCharacter = -1` at every strict-right Xi divisor point.

Lean: `XiRightHalfSquareRootBoundaryNoExtension.lean` proves
`no_local_analytic_sqrt_xi_of_odd_order`,
`exists_odd_order_line_zero_no_local_analytic_sqrt_gt`, `not_exists_entire_sqrt_xi`,
`rightHalf_sqrt_not_entire`, and `rhLadder_one_iff_exists_rightHalf_sqrt_not_entire`. Direct Lean
check and targeted build succeed. Axiom audit contains only `propext`, `Classical.choice`, and
`Quot.sound`. Global formal lint remains blocked by pre-existing unrelated unreachable modules;
new module is wired into `RHTower.lean` and is not among failures.

Novelty audit: corpus search found no existing theorem deriving this boundary non-extension from
`GlobalParityWall`. External literature on zeta multiplicity continues to support simplicity as
the expected generic behavior; the 2026 Alpöge--Furman result proves a large unconditional
proportion of simple on-line zeros and supplies no off-line evenness or half-divisor construction.

## 2026-09-02 — Exact pole-cleared squarefree arithmetic reduction

The first-prime-trace exponential cannot be halved before removing its Euler-pole monodromy.
The correct coefficient-faithful arithmetic carrier is the analytic pole-cleared squarefree unit

`P_sf(s) = zetaResidueUnit(s) / zeta(2s) = ((s-1) zeta(s)) / zeta(2s)`

away from the removable point `s=1`. On the full strict right half-plane,

`xi(s) = C(s) P_sf(s)`,  where `C(s) = (s/2) Gamma_R(s) zeta(2s)`.

The complement `C` is analytic and nowhere zero there: `s` is nonzero, `Gamma_R` is analytic and
nonzero for positive real part, and `zeta(2s)` is analytic and nonzero because `Re(2s)>1`.
Simple connectedness therefore supplies an unconditional analytic square root of `C`. It follows
that `P_sf` has exactly the complete Xi divisor at every right-half point and

`RHLadder 1 <-> P_sf admits an analytic square root on Re(s)>1/2`.

This is an exact arithmetic localization, not a construction of the missing root. It closes the
naive `exp(primeZeta/2)` route: classical prime-zeta continuation acquires logarithmic branch
points at zeta zeros, and selecting its half-exponential single-valuedly is exactly the parity
obligation above. The surviving open edge is now sharper: construct a single-valued analytic
square root of `P_sf` from arithmetic source data, not from post hoc divisor selection.

Lean: `XiSquarefreePoleUnitRootReduction.lean` proves analyticity and nonvanishing of `C`, exact
factorization, exact analytic-order equality, existence of a root of `C`, equivalence of Xi and
`P_sf` square roots, and the final `RHLadder 1` equivalence. Direct Lean check and sole targeted
build succeed. Axiom audit contains only `propext`, `Classical.choice`, and `Quot.sound`. Formal
lint remains blocked only by pre-existing unrelated unreachable modules; new module is wired into
`RHTower.lean` and is not among failures.

Novelty audit: corpus search found no prior square-root equivalence for `zetaResidueUnit` or
`squarefreeMobiusCriticalPoleUnit`. Fröberg's classical prime-zeta continuation and current
expositions identify the same logarithmic singularities at scaled zeta zeros; no source found
constructs a single-valued half-divisor across the strict right half-plane.

## 2026-09-02 — All higher prime valuations removed; exact first-trace continuation target

The pole-cleared squarefree unit still contains the Hilbert--Carleman determinant

`D2(s) = exp(squarefreeCarlemanLogDet(s))`.

This factor encodes all valuation-at-least-two prime-power terms and has the explicit analytic
half

`D2_half(s) = exp(squarefreeCarlemanLogDet(s)/2)`

throughout `Re(s)>1/2`. Dividing it out leaves

`E1(s) = squarefreeMobiusCriticalPoleUnit(s) / D2(s)`.

The complete Xi divisor is exactly the divisor of `E1`. On `Re(s)>1`,

`E1(s) = (s-1) exp(P(s))`,

and its fixed arithmetic square-root branch is

`e_Euler(s) = exp((log(s-1) + P(s))/2)`.

**Exact surviving obligation.** `RHLadder 1` holds iff this fixed Euler branch extends to an
analytic function `e` on `Re(s)>1/2` satisfying `e(s)^2=E1(s)`. Agreement is literal on the whole
Euler half-plane, not merely up to sign: the extension is oriented at `s=2`, then connected
square-root uniqueness fixes it everywhere on `Re(s)>1`.

This constructively removes archimedean completion, doubled zeta, and every higher-valuation
Carleman term. No higher prime power can supply missing parity. The open core is only monodromy of
the pole-cleared valuation-one prime trace. Any proposed arithmetic `g` must construct this exact
continuation; writing `exp(P/2)` without proving single-valued continuation is circular.

Lean: `XiPoleClearedFirstTraceRootReduction.lean` proves the explicit Carleman half, exact divisor
preservation, Euler-chamber identity, fixed Euler half-germ, square-root equivalence, and literal
extension criterion. Direct Lean check and targeted build succeed. Axiom audit contains only
`propext`, `Classical.choice`, and `Quot.sound`. Module is wired into `RHTower.lean`.

## 2026-09-02 — Paper proof: singular first-trace half ODE

Write `E = E1` for the pole-cleared valuation-one field. The square-root equation can be replaced
by one source-facing first-order equation which never mentions a zero or divisor:

`2 E(s) e'(s) = E'(s) e(s)`, with `e(2) = e_Euler(2)`.

If `e^2 = E`, differentiation and multiplication by `e` give this equation. Conversely suppose
`e` is analytic on `Re(s)>1/2`, obeys the equation there, and has the stated anchor. Since `E(2)`
is nonzero, on a small ball around `2` the quotient `q=e^2/E` is analytic. Its derivative is

`q' = (2 e e' E - e^2 E') / E^2 = e(2 E e' - E'e)/E^2 = 0`.

The anchor and `e_Euler(2)^2=E(2)` give `q(2)=1`, hence `q=1` on that ball. Therefore `e^2=E`
there. Both sides are analytic on the connected right half-plane, so the identity theorem gives
`e^2=E` everywhere. Thus existence of an anchored analytic solution of the singular linear ODE is
equivalent to the fixed Euler half-germ extension, and hence exactly to `RHLadder 1`.

At a zero of `E` of order `m`, the equation has local indicial exponent `m/2`; an analytic anchored
solution can cross the zero exactly when that exponent is integral. This does not solve the rung,
but it removes explicit divisor selection from the target: surviving arithmetic task is now to
construct one global analytic solution of the displayed coefficient-explicit ODE. No local
existence theorem can cross an odd-order singular point without proving the parity claim itself.

Lean: `XiPoleClearedFirstTraceHalfODE.lean` defines anchored global half-ODE solvability and proves
both directions between its solutions and analytic square roots of `E1`, then proves the exact
equivalence with `RHLadder 1`. Direct Lean check and sole targeted build succeed. Axiom audit for
all three exported theorems contains only `propext`, `Classical.choice`, and `Quot.sound`. Module is
wired into `RHTower.lean`.

## 2026-09-02 — Entire finite-prime/continuum-tail square approximants

There is one canonical way to make every finite Euler approximation a literal entire square while
retaining the fixed Euler half-germ. For a real cutoff `X > 1`, put `L = log X`,

`P_X(s) = sum_{p <= X} p^(-s)`

and, initially on `Re(s) > 1`,

`T_X(s) = integral_X^infinity t^(-s) / log(t) dt = E1((s-1)L)`.

Let

`Ein(z) = sum_{n>=1} (-1)^(n+1) z^n / (n n!)`.

This power series is entire, and the classical pole-cancellation identity on the right half-plane
is

`log(s-1) + T_X(s) = -gamma - log L + Ein((s-1)L)`.

Consequently

`Phi_X(s) = P_X(s) - gamma - log L + Ein((s-1)L)`

is entire. Define

`h_X(s) = exp(Phi_X(s)/2)` and `F_X(s) = exp(Phi_X(s))`.

Every `h_X` is entire and zero-free, with the unconditional identity `h_X^2 = F_X`. On
`Re(s) > 1`, the cancellation formula gives the coefficient-faithful source identity

`F_X(s) = (s-1) exp(P_X(s) + T_X(s))`.

As `X -> infinity`, finite prime sums converge locally uniformly to prime zeta and `T_X -> 0`
locally uniformly on `Re(s) > 1`. Hence

`h_X -> exp((log(s-1) + P(s))/2) = e_Euler`

locally uniformly on that chamber. No choice of zeros, divisor, logarithm continuation, or sign is
present in the construction.

**Normal-family producer.** Choose any cofinal cutoff sequence `X_n`. If `{h_{X_n}}` is locally
bounded on `Re(s) > 1/2`, Vitali's theorem applies because the family is entire and already
converges pointwise on the open uniqueness set `Re(s) > 1`. It produces an analytic limit `h` on
the full strict right half-plane, agreeing there with `e_Euler`. Thus `h^2 = E1` on the Euler
chamber; the identity theorem extends this equality throughout `Re(s) > 1/2`. This constructs the
required arithmetic half-divisor and proves `RHLadder 1`.

There is a stronger consequence which prevents treating this as a parity-specific mechanism.
Every `h_X` is zero-free. Hurwitz therefore makes the nonzero Vitali limit `h` zero-free on the
whole connected right half-plane. Hence `E1 = h^2` is zero-free there. Because `E1` has exactly
the strict-right Xi divisor, the same local boundedness estimate proves the full Riemann
hypothesis, not merely even multiplicity of possible off-line zeros. In particular, if RH were
false but every off-line zero had even order, the desired square root would exist yet this
zero-free approximation family would still have to lose local boundedness.

**Open core and failure audit.** Local boundedness has not been proved. It is not a routine
consequence of the prime number theorem: to the left of `Re(s)=1`, explicit-formula contributions
from a zeta zero `rho` have size on the scale `X^(Re(rho)-Re(s))/log X`, while the continuum tail
cancels only the pole at `1`. An off-line zero with `Re(rho)>Re(s)` therefore supplies precisely
the prospective normal-family blow-up. Contrapositively, failure of RH forces this canonical
entire-square family to lose local boundedness somewhere in the strict right half-plane. The
proposed estimate is therefore a concrete source-side RH-strength obligation, not yet an
unconditional proof and not a disguised divisor hypothesis. Its positive survivor is a canonical
finite-prime normal-family criterion for RH plus a forced local-amplitude blow-up alternative; it
does not isolate the weaker multiplicity-parity rung.

Corpus audit found no prior version of this family. `CriticalCenteredPrimeTailEntireCarrier.lean`
and `CriticalCenteredPrimeTailEulerPrimitive.lean` instead center the von Mangoldt current by its
continuous mean and multiply the existing zeta carrier by a zero-free entire gauge; they preserve
the original divisor and cannot manufacture a half-divisor. Existing `VitaliConvergence.lean` is
already sufficient for the compactness-to-root step. External search found classical prime-zeta
continuation and general zeta/Fredholm determinant literature, but no construction establishing
the required local boundedness of these finite-prime/continuum-tail square approximants.

## 2026-09-03 — Nonlinear coefficient half exists uniquely and carries no parity choice

The report's proposed nonlinear arithmetic step must distinguish two meanings of "square root."
At the coefficient level there is no obstruction at all. Let `f` be any complex arithmetic
function with `f(1)=1`. There is a unique normalized arithmetic function `g`, `g(1)=1`, satisfying
the Dirichlet-convolution identity

`g * g = f`.

Indeed set `g(0)=0`, `g(1)=1`, and for `n>1` recursively define

`g(n) = (f(n) - sum_{d|n, 1<d<n} g(d)g(n/d))/2`.

Every value on the right has smaller index. Splitting the convolution sum into the two endpoint
terms `(1,n)` and `(n,1)` plus proper interior divisors proves existence; the same split and strong
induction prove uniqueness.

For the squarefree indicator `f=mu^2`, this produces the formal local Euler factor
`(1+z)^(1/2)`: at every prime `p`, `g(p)=1/2` and `g(p^2)=-1/8`. Thus the nonlinear arithmetic
half requested in Step 1 already exists canonically before any RH information enters. Its
uniqueness rules out hidden coefficient-level design freedom.

This does not construct the requested analytic `g` on `Re(s)>1/2`. Turning convolution into
multiplication of Dirichlet series requires convergence. In the Euler chamber it recovers the
already-known branch of the squarefree Euler product; continuation across `Re(s)=1` encounters
exactly the logarithmic monodromy of zeta zeros isolated by the first-trace root reduction. Hence
the report's Step 1 is either trivial if interpreted formally, or exactly `RHLadder 1` if interpreted
as an analytic half-divisor. No intermediate nonlinear coefficient theorem supplies parity.

Lean: `SquarefreeConvolutionHalfRigidity.lean` constructs `convolutionHalf`, proves
`convolutionHalf_mul_self`, proves normalized uniqueness and the packaged unique-existence theorem,
then specializes to the complex squarefree indicator and verifies the prime and prime-square
coefficients. Direct Lean check succeeds with no `sorry` or added axiom.

## 2026-09-03 — Holomorphic fixed-fiber Kramers rigidity

The report's proposed two-by-two Kramers step has two inequivalent symmetry interpretations. A
fixed antiunitary `J` acting inside every parameter fiber imposes standard quaternionic form

`A(s) = [[a(s), b(s)], [-conj(b(s)), conj(a(s))]]`.

If all four entries are holomorphic in the same complex parameter `s`, then both `a` and `conj(a)`
are holomorphic, as are `b` and `conj(b)`. On a connected open domain, a holomorphic function whose
pointwise conjugate is also holomorphic is constant: the holomorphic sum `f+conj(f)` is real-valued,
so the open mapping theorem makes it constant; this fixes `Re(f)`, and a second use of the same
theorem makes `f` constant. Therefore `a`, `b`, the full matrix family, and its determinant are all
constant. Such a family cannot realize the nonconstant first-trace carrier or Xi.

The only nonconstant antiunitary alternative is parameter-reversing covariance,
`J A(s) J^-1 = A(conj(s))`. At an off-real spectral parameter this transports a kernel to the
distinct conjugate fiber. It explains conjugate pairing but does not double analytic multiplicity
at either point. Kramers degeneracy is local only on the fixed parameter locus, corresponding here
to the already-understood critical line. Thus Step 2 either forces a constant determinant or
recovers reflection pairing; neither yields `RHLadder 1`.

This second branch has an exact two-by-two countermodel. For any nonreal `rho`,

`A_rho(s)=diag(s-rho,s-conj(rho))`

obeys standard parameter-reversing Kramers covariance, but
`det A_rho(s)=(s-rho)(s-conj(rho))` has analytic order exactly one at `rho`. Thus even the literal
holomorphic two-by-two reflection model asserted by the report permits simple off-real zeros.

This is compatible with `SymplecticMultiplicity.lean`: that module uses the much stronger
complex-bilinear symplectic self-adjointness which preserves each generalized eigenspace and really
does force even multiplicity. Its existence for the Xi divisor is already equivalent to the first
ladder rung. It is not supplied by ordinary antiunitary Kramers covariance.

Lean: `HolomorphicKramersFiberRigidity.lean` proves conjugate-pair constancy, constancy of a
holomorphic standard Kramers two-by-two family, and constancy of its determinant. Direct Lean check
succeeds with no `sorry` or added axiom. `ParameterReversingKramersSimpleZero.lean` constructs the
nonconstant covariant diagonal family, proves its determinant formula, and proves order one at
every nonreal chosen parameter; direct Lean check and targeted build succeed with no added axiom.

## 2026-09-03 — Differential-Galois and NFD/RLM report claims do not supply a producer

For the exact half ODE `e'/e = E1'/(2E1)`, a loop around a zero of `E1` of order `m` has scalar
monodromy

`exp(2 pi i (m/2)) = (-1)^m`.

Triviality of this rank-one monodromy is therefore exactly evenness of `m`. A differential-Galois
argument can prove the base rung only by deriving this sign from independent arithmetic input.
The report cites `isomonodromy_of_no_riccati_of_differentialSolution`, but that theorem concerns a
second-order difference system and requires a full list of hypotheses: a chosen difference system,
fundamental matrix, sigma-simple Picard--Vessiot setting, separating Galois specializations, absence
of a base Riccati solution, and a differential constraint on a scalar stabilizer. The report
constructs none of these for `E1` or Xi. More decisively, existing corpus examples attach arbitrary
off-line quartet packets to hypertranscendental functional-equation carriers. Hypertranscendence is
compatible with the forbidden divisor and cannot determine the monodromy sign.

The final NFD/RLM claim is a programme, not a theorem or bridge. The cited NFD charter labels itself
`[FIELD HYPOTHESIS] [CORPUS REALIZATION OPEN] [NOT RH] [NO LEAN]`, states that its current status is
below Gate 1, and says its word model is only a calibration rather than an HGT producer. Its hostile
audit explicitly warns that without literal source-normal producer constructions NFD is another
container and must be rejected. The RLM constitution likewise labels universal dynamics open and
`[NOT RH]`; it excludes RH routes from its foundations. No `working_log.md` named by the report
exists in the repository.

One premise of Step 4 is false before reaching any Picard--Vessiot machinery: differentially
algebraic functions do not have periodic zero sets. The linear polynomial `z-a` is
differentially algebraic (an order-zero algebraic differential relation), has singleton zero set
`{a}`, and that set is invariant under no nonzero translation. Conversely, corpus theorem
`hypertranscendental_finiteQuartetWardIndex_law` and the reflected-Gamma quartet constructions
show that hypertranscendence tolerates arbitrary finite off-critical divisor packets. Thus the
claimed differential-algebraic/periodic versus hypertranscendental/critical divisor dichotomy is
reversed neither by definitions nor by the formal results.

Hypertranscendence also cannot veto a square-root carrier. For every entire function `g`, the
function `g` is hypertranscendental if and only if its square `g^2` is hypertranscendental. One
direction is closure of differential algebraicity under multiplication. The other passes to the
global meromorphic differential field, uses that every positive power of a hypertranscendental
element remains hypertranscendental, and returns through the exact analytic-jet bridge. Therefore
even a future proof that Xi is hypertranscendental would be fully compatible with a
hypertranscendental square root; it supplies no multiplicity parity and no monodromy trivialization.
The domain-local version is exact as well: on every nonempty connected open domain, and in
particular on `rightHalf`, an analytic function satisfies no algebraic differential equation if
and only if its square satisfies none. Thus the objection cannot be restored by noting that the
required root is only half-plane analytic rather than entire.

Lean: `DifferentialAlgebraicZeroPeriodicityNoGo.lean` gives the exact linear-polynomial
counterexample and proves nonperiodicity of its zero set for every nonzero translation. Direct
Lean check and targeted build succeed with no added axiom.
`HypertranscendentalSquareCompatibility.lean` proves both the exact entire-function equivalence and
the arbitrary-domain/right-half equivalence under squaring. Direct Lean check, targeted build, and
axiom audit succeed; only standard foundational axioms `propext`, `Classical.choice`, and
`Quot.sound` occur.

The report's broader "continuous class wall" language also needs a qualification. Pointwise zero
multiplicity parity is not invariant under a continuous analytic deformation. The jointly
polynomial family `F(t,z)=z^2-t^2` has a double zero at `z=0` when `t=0`, but for every nonzero
`t` it has a simple zero at `z=t` (and another at `z=-t`). What is deformation-invariant is total
multiplicity inside a fixed contour while no zero crosses that contour. This does not supply the
missing local parity law. `ContinuousAnalyticMultiplicityParityNoGo.lean` formalizes joint
continuity, entire parameter slices, order two at the collision, and order one after every
nonzero split. Direct Lean check, targeted build, and axiom audit succeed; only `propext`,
`Classical.choice`, and `Quot.sound` occur.

There is one exact closedness survivor. If holomorphic squares on any open domain converge locally
uniformly there, their normalized argument-principle counts are eventually equal to the limit count
on every compactly contained zero-free circle. Each approximant count is twice a natural number, so
the limit count is even; on an isolating disc, the limit zero therefore has even analytic order.
This applies directly with the domain `rightHalf`, not only to entire approximants. It is
substantially stronger than mere continuity in a parameter and exactly states what a
square-approximation proof would need. It remains a receiver: no arithmetic square approximants to
Xi are constructed, and supplying them would already force rung one.
`LocallyUniformSquareMultiplicityClosure.lean` proves global and domain-local power/count transfer,
even contour-count closure, isolated-zero parity, and the automatic local isolation/radius reduction
from any specified finite analytic order. The capstone
`XiPoleClearedFirstTraceSquareApproximation.lean` proves the exact equivalence: `RHLadder 1` iff the
pole-cleared valuation-one field is a compact-open limit on `rightHalf` of holomorphic squares.
Forward direction uses a constant sequence from a root; reverse direction transfers local order
parity by the argument principle. Thus proving convergence of the proposed finite-prime squares is
not a weaker route to parity—it is precisely a rung-one proof obligation. Direct Lean checks,
targeted builds, and axiom audits succeed; only `propext`, `Classical.choice`, and `Quot.sound`
occur.

Random or deterministic prime splitting does not evade this obstruction. A centered signed-prime
Euler factor that converges on `Re(s)>1/2` is a nonvanishing analytic unit. On `Re(s)>1`, either
split factor is the fixed half-Euler germ multiplied by such a unit; extending the split factor and
dividing by the unit therefore extends the fixed germ itself. The randomness changes only gauge,
not its `ZMod 2` monodromy. The report's displayed convolution identity is even more restrictive:
if `alpha * delta = 1`, then wherever the two Dirichlet series represent convolution their product
is identically one, so both are zero-free there and cannot have Xi's nonempty divisor. A viable twin
must instead multiply to Xi, and `TwinRigidity.lean` proves that such equal-divisor twins exist iff
the desired analytic square root already exists.

**Report verdict.** Multiplicity parity remains a logically valid exact target, but the proposed
four-step proof is not a proof architecture. Step 1 either gives the automatic formal coefficient
half or assumes the desired analytic half-divisor. Step 2 is constant-or-reflection-only. Step 3
has no upward Clifford construction and naive doubling changes multiplicity. Step 4 has neither a
Xi-to-Galois bridge nor a valid hypertranscendence veto. NFD/RLM supplies no marked HGT endofunctor,
comparison theorem, or divisor consequence. Exact surviving edge remains unchanged: construct the
fixed Euler half-germ continuation, equivalently an anchored analytic solution of the singular
first-trace half ODE, from source data without assuming trivial monodromy.

Quadratic-refinement salvage is already closed in the corpus. `SeamArfCollapse.lean` proves that a
reflection-invariant `ZMod 2` quadratic density on each reflected pair collapses pointwise to the
linear deck parity and that its whole-pair sum vanishes. Breaking reflection invariance amounts to
choosing the missing square-root sheet. Independently, the canonical reflected-pair quarter-turn
from `HedenmalmThetaReflectedPairParityBlindness.lean` exists for every multiplicity and hence sees
only the tautological dimension `2m`; on one actual theta root block,
`SymplecticCyclicObstruction.lean` rules out a nondegenerate invariant alternating form because the
block is cyclic. Thus Arf, Maslov, and local residue-polarization variants provide no source-side
parity theorem beyond the same open monodromy edge.

## 2026-09-03 — Canonical local Euler--residue Kramers detector

The multiplicity-`m` local divisor algebra does carry a canonical alternating form without any
choice of square-root sheet. In the monomial coordinates of `C[t]/(t^m)`, let the Frobenius
residue pair coordinate `i` with `m - 1 - i`, and antisymmetrise against the Euler grading. The
result is

`omega_m(t^i,t^j) = j - i` when `i + j = m - 1`, and zero otherwise.

Its matrix is anti-diagonal with coefficient `m - 1 - 2i` in row `i`. If `m` is even every
coefficient is nonzero, and testing against the reversed coordinate basis proves nondegeneracy.
Conversely any nondegenerate alternating form on a complex `m`-space forces `m` even. For odd
`m = 2r + 1`, the radical is exactly the line spanned by the middle monomial `t^r`, because its
coefficient is zero and every other anti-diagonal coefficient is nonzero. Hence

`omega_m nondegenerate <-> Even m`.

This is the strongest intrinsic local Kramers salvage found. It eliminates the need to postulate
an unspecified symplectic form, but it does not produce parity: for the Xi local divisor jet,
nondegeneracy of this exact canonical form is equivalent to `RHLadder 1`. Existing arithmetic
jet constructions (`DeningerArithmeticJetDuality`) supply every multiplicity-bounded derivative
coordinate unconditionally; their multiplicity is indexed by the already-known Xi divisor.
Existing ordinary/compact-support Poincare pairings are nondegenerate only between distinct dual
spaces, while quaternionic rectangular atoms double a divisor-free two-dimensional carrier.
Neither removes the odd middle radical inside a single Xi jet block.

Lean: `LocalDivisorJetEulerResidueParity.lean` constructs the coefficient, anti-diagonal matrix,
and bilinear form; proves alternation, constructive nondegeneracy for even length, exact
nondegeneracy iff even length, exact classification of the odd middle radical, and the equivalence between local
nondegeneracy at every right-half Xi zero and `RHLadder 1`. Direct Lean check succeeds with no
`sorry` or added axiom.

## 2026-09-03 — Dyadic convolution escalation is automatic coefficient algebra

Iterating the unique normalized convolution half gives a canonical tower `T_0=f`,
`T_(n+1)*T_(n+1)=T_n` for every normalized complex arithmetic function `f`. It is the unique
normalized coherent tower, and

`T_n^(2^n)=f`

under Dirichlet convolution. At a prime `p`, `T_n(p)=f(p)/2^n`; for the squarefree indicator this
is exactly `2^(-n)`. Thus the report's proposed all-rung escalation exists unconditionally at the
coefficient level, just as its base half does. Clifford machinery is unnecessary there.

This does not advance any analytic ladder rung. Dirichlet-series multiplication follows from the
coefficient identity only inside a common convergence chamber. To obtain `RHLadder n`, the
depth-`n` coefficient root must be continued as a single-valued analytic function through the
strict right half-plane; that continuation is exactly the `2^n`-divisibility statement. In
particular, analytic continuation of `T_1` supplies no inheritance theorem for `T_2`. The report's
Step 3 silently replaces automatic coefficient recursion by the missing analytic continuation at
every depth.

Lean: `SquarefreeConvolutionDyadicTower.lean` constructs the tower and recursive dyadic power,
proves the successor square law, `2^n`-power law, normalized uniqueness, general prime coefficient
formula, and squarefree specialization. Direct Lean check succeeds with no `sorry` or added axiom.

## 2026-09-03 — Absolute-convergence wall for every finite dyadic root

The canonical coefficient tower has an unavoidable analytic boundary. If the norm Dirichlet series
of its depth-`n` stage were summable at `s`, restriction to prime indices would remain summable.
On primes the coefficient is exactly `2^(-n)`, so multiplication by `2^n` would make

`sum_p norm(p^(-s))`

summable. The exact prime-power abscissa theorem rules this out whenever `Re(s) <= 1`. Hence every
finite dyadic coefficient root, including the proposed convolution half, fails absolute Dirichlet
summability throughout the target substrip `1/2 < Re(s) <= 1`.

This retires direct absolutely convergent coefficient realization as a producer. It does not rule
out the requested `g`: a viable arithmetic construction must instead provide genuine analytic
continuation or renormalization of the fixed Euler half-germ, while proving its `ZMod 2` monodromy
vanishes. That monodromy cancellation remains exactly `RHLadder 1`.

Lean: `SquarefreeConvolutionDyadicAbsoluteConvergenceWall.lean` proves the all-depth obstruction
and its explicit convolution-half corollary. Direct Lean check succeeds with no `sorry` or added
axiom.

## 2026-09-03 — Convolution-inverse analytic twins are zero-free

The report also asks for coefficient streams `a,d` satisfying `a*d=1` whose Mellin transforms
continue holomorphically to `Re(s)>1/2` and vanish on the Xi divisor. This class is empty as soon
as either continuation has any right-half zero.

Indeed, in the common Euler chamber, absolute convergence and the Dirichlet-convolution product
law give

`L(a,s)L(d,s)=L(a*d,s)=L(1,s)=1`.

If holomorphic continuations `A,D` exist on the connected strict right half-plane and agree with
these series in the Euler chamber, the identity theorem forces `A(s)D(s)=1` throughout the domain.
Both factors are therefore zero-free. Continuing an inverse pair cannot turn its coefficient
identity into a divisor split; a zero in one factor would require a pole in the other and leave
the requested holomorphic class.

This closes the report's `a*d=1` twin mechanism. The only nontrivial analytic twins remain those
whose product is Xi itself; `TwinRigidity.lean` already shows those are a genuine square root
dressed by a zero-free unit and hence exactly `RHLadder 1`.

Lean: `ConvolutionInverseAnalyticZeroNoGo.lean` packages the proposal as a closed existential and
proves its negation using the `L`-series convolution law and analytic identity theorem. Direct Lean
check succeeds with no `sorry` or added axiom.

## 2026-09-03 — Same-fibre Kramers rigidity is dimension-free for bounded operators

The finite two-by-two constancy obstruction is not a low-dimensional accident. Let `A(z)` be a
bounded complex-linear operator family on any complex inner-product space, with every weak matrix
coefficient holomorphic on a connected open parameter domain. Let one fixed antiunitary `J`
commute with `A(z)` in each fibre. Then

`inner(Jx, A(z) Jy) = conjugate(inner(x, A(z)y))`.

The left side is holomorphic by weak holomorphy, while the right side is the pointwise conjugate of
another holomorphic coefficient. Open-mapping rigidity makes every coefficient constant.
Inner-product separation then makes `A(z)` itself constant. The proof does not need finite
dimension, compactness, trace class, or even the additional Kramers relation `J^2=-1`.

The same proof does not use boundedness once one fixes a common operator domain: weak matrix
coefficients on that domain are still constant. This closes all bounded same-fibre holomorphic
Kramers/Fredholm models and all fixed-domain unbounded variants as producers of a nonconstant Xi
divisor. Parameter-reversing covariance still pairs distinct conjugate fibres and permits simple
off-real zeros. Remaining operator route must therefore use genuinely parameter-dependent
domains or a source law outside pointwise same-fibre commutation; none currently supplies parity.

Lean: `HolomorphicKramersOperatorRigidity.lean` proves both arbitrary-Hilbert-space bounded and
arbitrary fixed-domain theorems from the scalar conjugate-pair constancy lemma. Direct Lean check
succeeds with no `sorry` or added axiom.

## 2026-09-03 — Exact Euler-chamber realization of the convolution half

The report's canonical coefficient half has a complete source-defined Euler realization. Define

`a(n) = product_(p^k || n) binom(1/2,k)`.

This is multiplicative, its local generating series is `(1+X)^(1/2)`, and the formal identity
`(1+X)^(1/2) (1+X)^(1/2) = 1+X` proves `a*a` is the squarefree indicator. Uniqueness of the
normalized convolution half therefore identifies `a` with `squarefreeConvolutionHalf`. In
particular, at every prime power,

`squarefreeConvolutionHalf(p^k) = binom(1/2,k)`.

The recurrence

`(k+1) binom(1/2,k+1) = (1/2-k) binom(1/2,k)`

gives `|binom(1/2,k)| <= 1`. Multiplicativity upgrades this to the global divisor bound
`|a(n)| <= d(n)`, so its ordinary Dirichlet series converges absolutely and is holomorphic for
`Re(s)>1`. Dirichlet-convolution multiplication is therefore legitimate there and gives the exact
identity

`L(a,s)^2 = zeta(s)/zeta(2s)`.

This validates the coefficient half and its Euler germ, but not the report's claimed right-half
analytic object. Together with `SquarefreeConvolutionDyadicAbsoluteConvergenceWall.lean`, the
abscissa is sharp for the proposed method: convergence holds on `Re(s)>1` and fails on
`Re(s)<=1`. Any solution on `Re(s)>1/2` must analytically continue or renormalize this fixed germ;
single-valued continuation is still exactly the missing parity/monodromy theorem.

Lean: `SquarefreeConvolutionHalfEulerSummability.lean` proves multiplicativity, all prime-power
coefficients, the binomial norm bound, global divisor domination, absolute convergence,
holomorphy, and the exact zeta-quotient square identity. Direct Lean check succeeds with no
`sorry` or added axiom.

## 2026-09-03 — Source-defined Cayley–Dirichlet Vitali bridge

The fixed pole factor admits an explicit full-domain approximation without choosing a square-root
branch on the target half-plane. Put

`w(s) = (s-2)/s`

and let `B_(alpha,N)` be the degree-`N-1` binomial partial sum for `(1+z)^alpha`. Then

`r_N(s) = B_(1/2,N)(w(s)) B_(-1/2,N)(-w(s))`

is rational with its only possible pole at `s=0`, hence holomorphic on `Re(s)>1/2`. On
`Re(s)>1`, these functions converge compact-open to

`r(s) = (1+w(s))^(1/2) (1-w(s))^(-1/2)`,

and the Cayley inverse identity gives `r(s)^2=s-1` exactly.

Synchronize this with the canonical convolution-half Dirichlet polynomials

`D_N(s) = sum_(n<N) a(n)n^(-s)`

and the explicit zero-free Carleman half-determinant `C_(1/2)`:

`G_N(s) = r_N(s) D_N(s) / C_(1/2)(s)`.

Every `G_N` is holomorphic on `Re(s)>1/2`. On `Re(s)>1`, `G_N` converges compact-open to a
source-defined limit whose square is the pole-cleared first-trace continuation `E1`. Therefore,
if this one explicit sequence is locally bounded on `Re(s)>1/2`, arbitrary-domain Vitali produces
a holomorphic limit there; the identity theorem forces its square to equal `E1` everywhere, and
`RHLadder 1` follows.

Status: `[BRIDGE] [NOT RH]`. Local boundedness is the exact surviving source estimate, not proved.
Hostile check matters: the Cayley factors alone cannot be locally bounded across `s=1`, since such
normality would manufacture a holomorphic square root of the simple-zero function `s-1`. For real
`1/2<s<1`, `|w(s)|>1`, so raw binomial truncations also exhibit an exterior-disk growth hazard.
Only synchronized cancellation with `D_N` could make the combined family normal. This makes the
criterion substantially more concrete than existential continuation, but it remains a receiver
until an arithmetic cancellation estimate is proved.

Lean: `PoleFactorCayleySqrtApproximation.lean` proves full-domain holomorphy, Euler-chamber
compact-open convergence, and the exact square identity. `SquarefreeConvolutionHalfVitaliCriterion.lean`
proves every `G_N` holomorphic, its Euler-chamber limit and square identity, and the local-boundedness
implication to `RHLadder 1`. Both direct checks and targeted builds pass. Axiom audits report only
`propext`, `Classical.choice`, and `Quot.sound`; no `sorry`, new axiom, or unsafe declaration.

## 2026-09-03 — Standalone Cayley normality is impossible

The growth warning above is now a theorem, without estimating any binomial coefficient. Assume the
rational pole-factor approximants `r_N` were locally bounded on `Re(s)>1/2`. They are holomorphic
there and converge pointwise on the open Euler chamber to `r`. Vitali would produce a holomorphic
full-half-plane limit `R`; uniqueness on the Euler chamber and the identity theorem would force

`R(s)^2 = s-1`

throughout `Re(s)>1/2`. At the interior point `s=1`, the right side has analytic order one, while a
square has order divisible by two. Contradiction.

This retires any proof that bounds the pole-factor approximation separately and then combines it
with a separately bounded Dirichlet half. The only surviving normal-family mechanism is joint
cancellation inside the product `r_N D_N`; no factorwise majorant can establish it.

Lean: `PoleFactorCayleySqrtNormalityNoGo.lean` proves the contradiction using arbitrary-domain
Vitali, analytic identity, and order divisibility. Direct Lean check and targeted build pass; axiom
audit reports only `propext`, `Classical.choice`, and `Quot.sound`.

## 2026-09-03 — Same-index Cayley–Dirichlet normality is impossible

The remaining synchronized-cancellation premise for the explicit sequence is false. Test at the
fixed interior point `s=4/7`, where the Cayley coordinate is `-5/2`. The positive-half binomial
partial sum has norm at least `1/4` from its second term onward. The negative-half alternating
partial sums have central-binomial weights whose successive growth is at least `5/4`; parity-wise
alternating-sum bounds therefore give

`(5/4)^(N-1) / 20 <= |r_N(4/7)|`.

If `G_N = r_N D_N / C_(1/2)` were locally bounded, the zero-free fixed denominator would force
`(5/4)^(N-1)|D_N(4/7)|` to remain bounded. Applying this to adjacent odd/even truncations makes
their difference decay geometrically. At an odd prime `p`, however,

`D_(p+1)(4/7) - D_p(4/7) = (1/2) p^(-4/7)`,

whose norm is at least `1/(2p)`. Infinitely many arbitrarily large primes and exponential-over-
linear growth give a contradiction.

Status: `[FAILED/RETIRED EXACT SEQUENCE] [LEAN-PROVED]`. The prior Vitali implication remains a
correct receiver, but its local-boundedness premise is provably unavailable for same-index raw
truncations. Positive survivor: any source-defined normal-family successor must change the relative
scales, smoothing, or regularization of the Cayley and Dirichlet approximants. It must preserve the
fixed Euler half-germ while avoiding both the simple-zero pole-factor obstruction and prime-jump
geometric-decay obstruction. No such construction is presently known.

Lean: `SquarefreeConvolutionHalfVitaliNormalityNoGo.lean` proves explicit exterior-point growth,
the prime-term polynomial lower bound, and negation of
`PoleClearedFirstTraceSourceLocallyBounded`. Direct Lean check and targeted build pass. Axiom audit
reports only `propext`, `Classical.choice`, and `Quot.sound`; no `sorry`, new axiom, opaque, or
unsafe declaration.

## 2026-09-03 — Sharp prime-scale ceiling for resynchronized truncations

Let `kappa(N)` be the Cayley degree paired with Dirichlet cutoff `N`. The exterior-point argument
extends beyond same-index truncation. If all `kappa(N)>=3` and the scheduled products are bounded
at `s=4/7`, then some constant `B>=0` satisfies, for every prime `p`,

`(5/4)^min(kappa(p)-1,kappa(p+1)-1) <= B p`.

Proof: boundedness controls both adjacent partial sums after multiplication by their respective
Cayley growth factors. Rescale both by the smaller exponent, subtract, and use the exact prime
jump `(1/2)p^(-4/7)`, bounded below by `1/(2p)`. Consequently any schedule for which the left-hand
exponential divided by `p` tends to infinity is also impossible.

Status: `[LEAN-PROVED POSITIVE SURVIVOR] [CONSTRAINT, NOT RH]`. Raw resynchronization can remain
viable only if at least one of the adjacent Cayley degrees along every large prime is logarithmic
in the prime. Linear, polynomial, or other superlogarithmic adjacent schedules cannot work. This
does not prove a logarithmic schedule is bounded; it identifies the maximum growth regime in which
arithmetic cancellation has not already been ruled out.

Lean: `SquarefreeConvolutionHalfCayleyScheduleCeiling.lean` proves the prime-scale ceiling and the
general superlogarithmic-schedule no-go. Direct Lean check and targeted build pass. Axiom audit
reports only `propext`, `Classical.choice`, and `Quot.sound`.

## 2026-09-03 — Explicit logarithmic schedule survives known normality obstructions

For any Cayley-degree schedule `kappa(N)` tending to infinity, the scheduled products

`G_N^kappa(s) = r_(kappa(N))(s) D_N(s) / C_(1/2)(s)`

retain compact-open convergence to the fixed Euler half-germ on `Re(s)>1`. Thus local boundedness
on `Re(s)>1/2` still implies `RHLadder 1` by Vitali and analytic identity.

The explicit choice

`kappa(N) = log_2(N+1) + 3`

tends to infinity and keeps every Cayley degree at least three. It also avoids the prime-scale
divergence obstruction: the normalized exterior growth

`(5/4)^min(kappa(N)-1,kappa(N+1)-1) / N`

is uniformly at most eight for `N>=1`. This does not prove local boundedness, but it is the first
fully specified raw truncation sequence satisfying both necessary structural requirements: enough
Cayley depth for Euler-chamber convergence and sufficiently slow depth to escape the prime-jump
no-go.

Status: `[LIVE BRIDGE] [NOT RH]`. Exact open core is local boundedness of the logarithmically
rescheduled products on `rightHalf`. Hostile attack must next determine whether raw Dirichlet
partial sums grow too quickly even for this sublinear exterior factor, or whether a smoothed
variant is required.

Lean: `SquarefreeConvolutionHalfLogScheduleCriterion.lean` proves scheduled compact-open
convergence, scheduled Vitali implication, logarithmic-schedule divergence to infinity, uniform
prime-scale bound, and compatibility with the prior no-go. Direct Lean check and targeted build
pass. Axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`.

## 2026-09-03 — Base-two logarithmic schedule fails near the half-plane boundary

Passing the `s=4/7` prime-scale test was not enough. At the closer boundary point `s=6/11`, the
Cayley coordinate is `-8/3`. The negative-half central-binomial weights grow by at least factor two
after their first step. Parity-controlled alternating sums and the nonvanishing positive-half
factor yield

`(N+1)/20 <= |r_(log_2(N+1)+3)(6/11)|`.

Local boundedness of the scheduled products would therefore force

`(N+1) |D_N(6/11)| = O(1)`.

At every prime `p`, the adjacent jump is exactly `(1/2)p^(-6/11)`, so multiplying by `p` gives
`(1/2)p^(5/11)`, unbounded along arbitrarily large primes. Contradiction.

Status: `[FAILED/RETIRED LOG-BASE-2 SEQUENCE] [LEAN-PROVED]`. Positive survivor is stronger than
the earlier fixed-point ceiling: a viable schedule must be slow enough uniformly over compacta
approaching `Re(s)=1/2`, not merely at one exterior point. Since both binomial factors have
exterior exponential growth, the eventual critical logarithmic base is expected to be governed by
the square of the boundary Cayley modulus, not the one-factor lower bound used here. Exact sharp
base remains under attack.

Lean: `SquarefreeConvolutionHalfLogScheduleBoundaryNoGo.lean` proves factor-two weight growth,
linear scheduled pole-factor growth, the exact prime-term power law, and negation of local
boundedness for `logarithmicCayleySchedule`. Direct Lean check and targeted build pass. Axiom audit
reports only `propext`, `Classical.choice`, and `Quot.sound`.

## 2026-09-03 — Two-factor boundary ceiling

The preceding base-two no-go was not sharp because it discarded exponential growth of the
positive-half binomial factor. At `s=6/11`, its negative terms grow by at least factor two after a
finite head, while the negative-half alternating factor already has the same lower rate. Hence,
for every degree `M>=6`,

`4^(M-6) / 5 <= |r_M(6/11)|`.

For a general schedule with `kappa(N)>=6`, boundedness at this one point therefore forces some
`B>=0` such that every prime satisfies

`4^min(kappa(p)-6,kappa(p+1)-6) <= B p^(6/11)`.

Any schedule whose left side divided by `p^(6/11)` tends to infinity is impossible. This is the
correct two-factor obstruction at this test point. In particular, merely choosing a generic
logarithmic schedule is insufficient; its base must be large enough relative to both exterior
binomial growth and the local Dirichlet exponent.

Status: `[LEAN-PROVED POSITIVE SURVIVOR] [CONSTRAINT, NOT RH]`. Expected boundary-uniform scale is
stricter still: as `Re(s)` approaches `1/2`, Cayley modulus approaches three and two-factor growth
approaches base nine per degree. Determining and formalizing the sharp uniform logarithmic
threshold is next; an even slower log-log schedule remains structurally compatible.

Lean: `SquarefreeConvolutionHalfBoundaryTwoFactorCeiling.lean` proves both factor growth laws, the
`4^M` pole-factor bound, scheduled prime ceiling, and scale-divergence no-go. Direct Lean check and
targeted build pass. Axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`.

## 2026-09-03 — Square-root logarithmic schedule survives both proved ceilings

The explicit slower schedule

`kappa(N) = log_4(sqrt(N)+1) + 6`

tends to infinity and keeps every degree at least six. It therefore preserves Euler-chamber
compact-open convergence and the Vitali implication: local boundedness of its scheduled products
on `rightHalf` would prove `RHLadder 1`.

Unlike the retired base-two logarithmic schedule, this choice satisfies the sharp two-factor
boundary scale law pointwise for every `N>=1`:

`4^min(kappa(N)-6,kappa(N+1)-6) <= 2 N^(6/11)`.

It also satisfies the earlier one-factor test with uniform normalized bound `2048`. Consequently
neither current prime-jump divergence theorem can retire it. The real-axis sign attack also fails:
on `1/2<sigma<1`, both `sigma-1` and `zeta(sigma)` are negative while `zeta(2 sigma)` is positive,
so the squarefree pole unit has positive rather than negative sign. Real-valued square approximants
are therefore sign-compatible there.

Status: `[LIVE BRIDGE] [NOT RH]`. Exact open core is now local boundedness of this concrete
square-root logarithmic schedule, or a proof that some other boundary point forces a still slower
degree law. Passing necessary pointwise prime-jump ceilings supplies no upper bound on Dirichlet
partial sums and no normal-family theorem by itself.

Lean: `SquarefreeConvolutionHalfSqrtLogSchedule.lean` proves divergence of the schedule to infinity,
both explicit scale bounds, negation of both known scale-divergence predicates, and the conditional
`RHLadder 1` endpoint. Direct Lean check and targeted build pass. Axiom audit reports only
`propext`, `Classical.choice`, and `Quot.sound`.

## 2026-09-03 — Square-root logarithmic schedule fails under sharper boundary growth

The prior base-four boundary estimate was not asymptotically sharp. At `s=6/11`, the
positive-half exterior binomial term ratio is at least `5/2` from degree 23 onward. Combining this
with the already certified factor-two growth of the negative-half factor gives, for `M>=24`,

`5^(M-24) <= |r_M(6/11)|`.

Any cofinal schedule bounded at this point must therefore obey an eventual prime ceiling

`5^min(kappa(p)-24,kappa(p+1)-24) <= B p^(6/11)`.

For `kappa(N)=log_4(sqrt(N)+1)+6`, choose a Bertrand prime
`16^m < p <= 2*16^m`. Both adjacent scheduled degrees are at least `m+6`, while raising the
ceiling to the eleventh power exposes the strict integer inequality

`2*16^6 < 5^11`.

The exponential gap eventually beats every fixed `B`, contradiction.

Status: `[FAILED/RETIRED SQUARE-ROOT-LOG SEQUENCE] [LEAN-PROVED]`. Positive survivor: passing one
coarse exterior lower bound is not meaningful evidence of normality. A raw cofinal schedule must
grow strictly slower than `log_4(sqrt N)`; iterated logarithmic depth remains compatible with all
proved prime-jump ceilings. Local boundedness for such a slower schedule remains unproved.

Lean: `SquarefreeConvolutionHalfSqrtLogScheduleBoundaryNoGo.lean` proves factor-`5/2` growth, the
base-five pole-factor bound, the eventual cofinal-schedule prime ceiling, its Bertrand-prime
violation for the square-root-log schedule, and negation of local boundedness. Direct Lean check
and targeted build pass. Axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`.

## 2026-09-03 — Iterated-log schedule survives sharpened fixed-point ceiling

Set

`kappa(N) = log_2(log_2(N+1)+1) + 24`.

This schedule tends to infinity and is everywhere at least 24, so the general scheduled Vitali
bridge applies. At the sharpened `s=6/11` test, its base-five exterior scale is eventually bounded
by the allowed prime power:

`5^min(kappa(N)-24,kappa(N+1)-24) <= N^(6/11)`.

The proof is symbolic. Since `5<=8`, the left side is bounded by a cubic power of
`log_2(N+1)+1`. The natural logarithm comparison converts this to a fixed multiple of
`(1+log N)^3`, and the corpus log-versus-power theorem absorbs it into `N^(6/11)`.

Status: `[LIVE BRIDGE] [NOT RH]`. This is the first explicit cofinal schedule surviving the
sharpened base-five obstruction. Its local boundedness remains wholly open; the scale estimate is
only a necessary-condition check. Fixed interior test points cannot by themselves distinguish
iterated-log growth from subpower prime decay. Next hostile attack must either control actual
Dirichlet partial sums, find a qualitatively different obstruction, or replace raw truncation by
smoothing.

Lean: `SquarefreeConvolutionHalfIteratedLogSchedule.lean` proves cofinality, the eventual
base-five scale bound, an explicit eventual prime ceiling, and the conditional `RHLadder 1`
endpoint. Direct Lean check and targeted build pass. Axiom audit reports only `propext`,
`Classical.choice`, and `Quot.sound`.

## 2026-09-03 — Iterated-log schedule defeats every fixed-base exponential ceiling

The preceding base-five estimate is not special to `s=6/11`. For every fixed natural base
`q>=1` and every real exponent `delta>0`, Lean now proves

`q^min(kappa(N)-24,kappa(N+1)-24) <= N^delta`

eventually for the same iterated-log schedule. The proof bounds `q` by `2^q`, converts the outer
binary logarithm into a fixed `q`-th power of `log_2(N+1)+1`, and absorbs that polylogarithm into
the arbitrary positive power `N^delta`.

Status: `[LEAN-PROVED POSITIVE SURVIVOR] [SEARCH-CLASS CLOSURE, NOT RH]`. Any fixed interior
point whose Cayley approximants have at most exponential-in-degree growth yields only this kind of
subpower ceiling. Such a point cannot retire the iterated-log schedule through a prime-jump
argument. A successful hostile attack must be boundary-uniform, use actual multi-term arithmetic
cancellation/growth, or change the regularization.

Lean: `SquarefreeConvolutionHalfIteratedLogSchedule.lean` now also proves
`eventually_iteratedLogarithmicCayleySchedule_fixedBaseScale_le`. Direct Lean check and targeted
module build pass. Axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`.

## 2026-09-03 — Every cofinal raw schedule fails by Abel continuation

The fixed-point ceiling search was too weak because degree growth is not the decisive obstruction.
The canonical convolution-half Dirichlet partial sums themselves cannot be eventually bounded at
`s=6/11`. If they were, shifting their coefficients into the zero-indexed Dirichlet API and
applying Abel summation would give convergence at `s=2/3`. Uniform Abel continuation would then
produce a holomorphic sum `F` on `Re(s)>2/3`. On `Re(s)>1`, the Euler identity gives

`F(s)^2 = zeta(s) / zeta(2s)`.

Analytic uniqueness applied to

`(s-1) F(s)^2 zeta(2s) - (s-1) zeta(s)`

extends the pole-cleared identity across `s=1`. Its left product vanishes there, while the zeta
residue unit has value one, contradiction.

This kills every cofinal Cayley schedule at once. Cofinality eventually gives `kappa(N)>=24`, and
the certified exterior bound

`1 <= 5^(kappa(N)-24) <= |r_(kappa(N))(6/11)|`

turns local boundedness of the scheduled products into forbidden eventual boundedness of the raw
Dirichlet partial sums. Same-index, logarithmic, square-root-logarithmic, iterated-logarithmic, and
all still slower cofinal raw schedules are therefore covered.

Status: `[FAILED/RETIRED RAW SCHEDULED TRUNCATION CLASS] [LEAN-PROVED]`. Positive survivor:
failure is not a rate problem. Any viable continuation scheme must change the arithmetic
approximants before multiplication by the Cayley factor—through genuine smoothing, a counterterm,
or another renormalization—and must still preserve source-faithful compact-open convergence to the
Euler half-germ. Merely slowing the degree schedule cannot work. No Selberg--Delange asymptotic is
needed for this closure.

Lean: `SquarefreeConvolutionHalfCofinalScheduleNoGo.lean` proves raw partial sums are not
eventually bounded at `boundaryExteriorPoint`, proves no cofinal scheduled product is locally
bounded, and specializes this to the formerly surviving iterated-log schedule. Direct Lean check
and targeted module build pass. Axiom audits report only `propext`, `Classical.choice`, and
`Quot.sound`; no `sorry`, new axiom, opaque declaration, or unsafe declaration is used.

## 2026-09-03 — Counterterm classification isolates singular renormalization

Let `c_N(s)` correct the raw convolution-half Dirichlet polynomial before multiplication by the
Cayley pole factor. Source fidelity has two exact requirements: every `c_N` is analytic on
`rightHalf`, and `c_N -> 0` compact-open on `farHalf`. These conditions preserve both holomorphy of
the corrected approximants and compact-open convergence to the fixed Euler half-germ. Consequently
local boundedness of any cofinal corrected family still implies `RHLadder 1` by Vitali and analytic
identity.

The Abel obstruction forces a sharp price. If the corrected arithmetic values have a bounded tail
at `s=6/11`, then `c_N(6/11)` cannot also have a bounded tail, since subtracting two bounded tails
would bound the raw partial sums. Local boundedness of a cofinal corrected product gives precisely
such a bounded corrected tail through the base-five Cayley lower bound. Therefore every successful
counterterm is unbounded at `6/11`. In particular, uniformly bounded perturbations and corrections
tending pointwise to zero there cannot work.

Status: `[LEAN-PROVED POSITIVE SURVIVOR] [EXACT OPEN BRIDGE, NOT RH]`. Required object is now a
singular separating family: analytic on `rightHalf`, compact-open zero on `farHalf`, unbounded in
the inner strip strongly enough to cancel the raw pole-root divergence, yet locally bounded after
the corrected arithmetic term is paired with the cofinal Cayley factor. Ordinary small smoothing
is excluded. Next hostile test should construct an explicit separating counterterm and determine
whether its transition layer near `Re(s)=1` remains locally bounded or merely moves the blow-up.

Lean: `SquarefreeConvolutionHalfCountertermNecessity.lean` defines admissible counterterms and
corrected scheduled products, proves preservation of analyticity and the Euler-chamber source
limit, gives the conditional `RHLadder 1` endpoint, and proves the unbounded-counterterm necessity
plus bounded/pointwise-vanishing no-go corollaries. Direct Lean check and targeted module build
pass. Axiom audits report only `propext`, `Classical.choice`, and `Quot.sound`.

## 2026-09-03 — Explicit anchored separator repairs the Abel witness

The first singular counterterm satisfying the classification is explicit:

`c_N(s) = -D_N(6/11) exp(N(6/11-s))`.

Each `c_N` is entire. At `s=6/11` its exponential factor is one, so
`D_N(6/11)+c_N(6/11)=0`; every pole-cleared scheduled approximant therefore vanishes exactly at
the point which retired all raw schedules. On every compact subset of `Re(s)>1`, the exponential
decay beats the certified crude bound `|D_N(6/11)|<=N^2`, so `c_N->0` compact-open. The family is
therefore a source-faithful admissible counterterm for the general Vitali bridge.

Its singularity is genuine, not hidden: `c_N(6/11)=-D_N(6/11)` has no bounded tail, and the
counterterm family is not locally bounded on any ball centered at `6/11`. This is required by the
counterterm classification. The cancellation shows that unbounded correction amplitude alone does
not obstruct bounded corrected products.

Status: `[LIVE EXPLICIT CANDIDATE] [NOT RH]`. The old Abel witness is closed for this family, but
no local-boundedness theorem is claimed. Exact open core is transition-layer control of

`r_(kappa(N))(s) (D_N(s)+c_N(s)) / C_(1/2)(s)`

on all compact subsets of `rightHalf` for a cofinal `kappa`. Next hostile attack must test points
and derivatives immediately left of the anchor; a fixed-point cancellation which merely moves
exponential blow-up is terminal.

Lean: `SquarefreeConvolutionHalfAnchoredCounterterm.lean` proves the polynomial amplitude bound,
entireness, compact-open Euler-chamber decay, admissibility, exact anchor cancellation, required
unbounded amplitude, and failure of local boundedness for the counterterm by itself. Direct Lean
check and targeted module build pass. Axiom audits report only `propext`, `Classical.choice`, and
`Quot.sound`.

## 2026-09-03 — Rank-one boundary anchor fails at first jet

The explicit anchor is terminal. On the radius-`1/22` disc about `b=6/11`, coefficient bounds give
`|D_N(s)|<=N`; Cauchy's estimate therefore gives `|D_N'(b)|<=22N`. But the separator derivative is
`-N`, so

`(D_N+c_N)'(b)=D_N'(b)+N D_N(b)`.

The already-certified absence of any bounded tail for `|D_N(b)|` forces these corrected first jets
to escape every fixed bound. For every cofinal degree schedule, the Cayley factor is eventually
bounded below at `b`, while the determinant is fixed and nonzero. If the full corrected quotients
were locally bounded, Cauchy's derivative estimate on a smaller disc would give one uniform first-
derivative bound, contradicting this escape.

Status: `[RETIRED — FIRST-JET OBSTRUCTION] [NOT RH]`. Exact anchor interpolation only moves the
Abel obstruction from value order zero to derivative order one. Positive survivor: a viable
singular renormalization must cancel or distribute a transition jet; no rank-one value anchor of
this form can suffice.

Lean: `SquarefreeConvolutionHalfAnchoredCountertermNoGo.lean` proves the coefficient bound, linear
Cauchy derivative estimate, exact counterterm and quotient derivative formulas, and the universal
cofinal local-boundedness no-go. Direct Lean check passes.

## 2026-09-03 — First-jet Hermite repair fails at second jet

The next counterterm matches the degree-one Taylor jet of `exp(N(s-b))D_N(s)` at `b=6/11`, then
multiplies it by `-exp(N(b-s))`. It is entire, converges compact-open to zero on `Re(s)>1`, and
cancels both the corrected value and first derivative exactly at `b`. Thus it passes the previous
first-jet obstruction rather than merely repeating the rank-one anchor.

Its first uncancelled jet is exact:

`(D_N+c_N)''(b)=D_N''(b)+2N D_N'(b)+N^2 D_N(b)`.

Cauchy on the radius-`1/22` disc gives `|D_N'(b)|<=22N` and `|D_N''(b)|<=968N`. Since
`|D_N(b)|` has no bounded tail, the `N^2D_N(b)` term forces the corrected second jets beyond every
fixed bound. For a cofinal Cayley schedule the pole factor is eventually bounded below and the
determinant is fixed nonzero. Local boundedness would give a uniform second-derivative Cauchy
bound, contradiction.

Status: `[RETIRED — SECOND-JET OBSTRUCTION] [NOT RH]`. Finite Hermite matching through first order
only moves the obstruction one derivative higher. Positive survivor is now increasing-order or
genuinely distributed transition-jet renormalization; fixed value/first-jet interpolation is
closed.

Lean: `SquarefreeConvolutionHalfFirstJetCountertermNoGo.lean` constructs the admissible correction,
proves exact zero- and first-jet cancellation, all-order Cauchy bounds for raw jets, the exact
second-jet quotient formula, and the cofinal local-boundedness no-go. Direct Lean check passes.

## 2026-09-03 — Every fixed dressed arithmetic jet escapes

The first- and second-jet calculations extend arithmetically to every fixed order. For

`H_N(s)=exp(N(s-b))D_N(s)`, `b=6/11`,

Leibniz gives

`H_N^(k)(b)=sum_(i=0)^k binom(k,i) N^i D_N^(k-i)(b)`.

The top term is `N^kD_N(b)`. Cauchy gives the explicit general bound
`|D_N^(j)(b)|<=j! N 22^j`. Hence the sum of all terms with `i<k` is at most `C_k N^k`, where

`C_k=sum_(i<k) binom(k,i)(k-i)!22^(k-i)`.

Because `|D_N(b)|` has no bounded tail, `|H_N^(k)(b)|` has no bounded tail for every fixed `k`
(including `k=0`). This is unconditional and schedule-independent.

Status: `[FIXED-JET ARITHMETIC CLASS CLOSED] [NOT RH]`. Any fixed-depth Hermite anchor leaves its
first uncancelled jet equal to one of these dressed jets, so the only interpolation survivor has
depth tending to infinity with cutoff. Distributed/nonlocal transition control remains separate.

Lean: `SquarefreeConvolutionHalfFixedJetEscape.lean` proves the exact dressed Leibniz expansion,
explicit remainder constant and bound, and absence of an eventual bound at every fixed jet order.
Direct Lean check passes.

## 2026-09-03 — Abel obstruction fills the entire interior real interval

The raw obstruction is not confined to the original witness `b=6/11`. For every real
`sigma` with `1/2<sigma<1`, bounded convolution-half Dirichlet partial sums at `sigma` would, by
Abel summation, define a holomorphic Dirichlet sum on a half-plane still containing `s=1`.
Squaring on the Euler chamber and applying analytic uniqueness would force the zeta residue unit
to vanish at one. Hence the raw partial sums have no bounded tail at every such `sigma`.

Combining the new theorem at `sigma=4/7` with the existing Cayley lower bound gives a second
counterterm necessity law: every cofinal locally bounded corrected family has an unbounded
counterterm tail at `4/7`, as well as at `6/11`. In particular, any correction tending to zero at
`4/7` is terminal for every cofinal Cayley schedule.

Status: `[LEAN-PROVED MULTI-ANCHOR OBSTRUCTION] [NOT RH]`. Point-jet cancellation must stay active
throughout the whole real interval `(1/2,1)`, not merely at one selected anchor. This sharply
constrains the moving-depth Hermite survivor: a schedule whose transition collapses back to
`6/11` is already excluded at `4/7`. The remaining hostile audit is whether a linearly moving
transition can preserve compact-open source fidelity on the full vertically unbounded Euler
half-plane; vertical Taylor growth is the suspected obstruction, but that dichotomy is not yet a
Lean theorem.

Lean: `SquarefreeConvolutionHalfInteriorUnbounded.lean` proves pointwise and eventual
unboundedness for every real `sigma in (1/2,1)`, specializes it at `4/7`, and proves the second
counterterm necessity and pointwise-vanishing no-go. Direct Lean check passes.

## 2026-09-03 — Exact Cayley seam formulation

Set `w=(s-2)/s`. The strict target half-plane `Re(s)>1/2` is biholomorphic to the disk
`|w+1|<2`, with inverse `s=2/(1-w)`, while the arithmetic Euler chamber `Re(s)>1` is exactly the
unit subdisk `|w|<1`. The fixed prime-zeta half-germ therefore lives on an internal unit disk, and
the missing scalar is precisely its analytic square-root continuation across that circle to the
larger tangent disk.

This change of coordinates does not weaken the endpoint: existence of a square root on the larger
disk is equivalent to `RHLadder 1`, and the stronger condition that it agree with the transported
fixed arithmetic half-germ on the unit disk is equivalent as well. The seam is therefore a clean
Hardy/Riemann--Hilbert formulation of the surviving problem, not a new producer and not an RH
proof.

Status: `[EXACT CAYLEY-SEAM REDUCTION] [OPEN PRODUCER] [NOT RH]`. The useful search target is now a
coefficient-faithful continuation theorem across the internal unit circle. Pure root existence,
locally uniform square approximation, and the first-order half-ODE remain exact receivers and are
circular if asserted without such a producer.

Lean: `XiPoleClearedFirstTraceCayleySeam.lean` proves both domain maps and inverses, exact Euler
unit-subdisk membership, analyticity of the transported field and arithmetic germ, root-existence
equivalence, and fixed-germ extension equivalence. Direct Lean check passes.

The internal unit circle is not a local analytic barrier. Classical zero-freeness on
`Re(s)>=1` makes the transported field nonzero on the closed unit disk (inside the larger open
disk). Every finite seam point therefore has a nonvanishing local analytic square root. The
remaining obstruction is global: continuation through the outer annulus must avoid or acquire
even winding around every off-line zero. Arithmetic loss of the Euler series at `Re(s)=1` is a
source-representation seam, not a local singularity of the continued field.

## 2026-09-03 — Unconditional high-band continuation beyond the Euler chamber

The de la Vallee Poussin zero-free region yields a genuine positive continuation result. There is
an absolute height `T` such that for every `Y>=T`, the convex height-one band

`Y<Im(s)<Y+1`, `Re(s)>1-1/(10000 log(Y+1))`

is zero-free. On each band the pole-cleared first-trace field therefore has an analytic square
root. Normalizing its sign at the canonical Euler-side point `2+i(Y+1/2)` and applying analytic
uniqueness makes it agree with the fixed prime-zeta half-germ throughout the band overlap with
`Re(s)>1`.

Status: `[UNCONDITIONAL ARITHMETIC CONTINUATION] [SHRINKING WIDTH] [NOT RH]`. This is stronger than
pointwise local seam passage: one coherent branch crosses the full height-one band. Its leftward
gain is only `1/(10000 log Y)` and tends to zero, whereas the target requires fixed width `1/2`.
Classical zero-free regions therefore produce a cusp collar, not the required half-plane root.

Lean: `XiPoleClearedFirstTraceZeroFreeBand.lean` proves band openness, convexity, containment in
`rightHalf`, zero-freeness from the formal de la Vallee Poussin theorem, analytic root existence,
and exact agreement with the fixed Euler half-germ. Direct Lean check passes.

## 2026-09-03 — One coherent branch on the full upper zero-free cusp

The separate high-band roots assemble more strongly into one global arithmetic branch. For a
sufficiently large absolute `T`, define

`C_T={s: Im(s)>T, Re(s)>1-1/(10000 log(Im(s)))}`.

A globally continuous real-coordinate shear maps the convex quadrant
`{Re(z)>0, Im(z)>T}` homeomorphically onto `C_T`; hence the cusp is open and simply connected. The
formal de la Vallee Poussin theorem makes the pole-cleared first-trace field nonzero throughout
`C_T`. It therefore has one analytic square root there. Sign normalization at an Euler-side point
and analytic uniqueness force equality with the fixed prime-zeta half-germ on all of
`C_T intersect {Re(s)>1}`.

Status: `[COHERENT ZERO-FREE CUSP ROOT] [UNCONDITIONAL] [NOT RH]`. This is no longer a collection of
unrelated local branches. It is one source-faithful analytic object on an unbounded domain crossing
the Euler line at every high ordinate. Its boundary nevertheless tends to `Re(s)=1`; it reaches no
fixed line `Re(s)=sigma<1`. The remaining leap from shrinking cusp width to the fixed half-plane is
exactly where possible off-line zeros and `ZMod 2` monodromy enter.

Lean: `XiPoleClearedFirstTraceZeroFreeCusp.lean` proves continuity of the protected cusp boundary,
constructs the shear homeomorphism, proves openness and simple connectedness, establishes
zero-freeness, and constructs the normalized arithmetic square root. Direct Lean check passes.

## 2026-09-03 — One arithmetic branch on the symmetric two-ended cusp

Reflecting the upper cusp through complex conjugation gives a lower cusp with the same unconditional
zero-free bound. Each cusp is open and simply connected and meets the Euler chamber `Re(s)>1` in a
convex set. Orienting both square roots by the fixed prime-zeta half-germ makes their overlap values
identical. Two successive analytic gluing steps therefore produce one function on

`{Re(s)>1} union C_T^+ union C_T^-`

which is analytic, squares to the pole-cleared first-trace field, and equals the fixed arithmetic
half-germ everywhere in the Euler chamber.

Status: `[SYMMETRIC TWO-ENDED CUSP ROOT] [UNCONDITIONAL] [NOT RH]`. Conjugation symmetry introduces
no sign or monodromy obstruction once both ends are attached through the Euler chamber. It also adds
no fixed-width gain: both boundaries retreat to `Re(s)=1`. The surviving obstruction remains
leftward domain enlargement through the zero-bearing strip, not normalization or compatibility of
the upper and lower arithmetic branches.

Lean: `XiPoleClearedFirstTraceSymmetricZeroFreeCusp.lean` proves lower-cusp topology, reflected
zero-freeness, arithmetic orientation, cusp disjointness, height restriction, and exact two-stage
gluing on the connected symmetric domain. Direct Lean check passes.

## 2026-09-03 — Growing Hermite depth below slope `1/54` is terminal

Let `D_N` be the convolution-half Dirichlet polynomial and let `H_{N,K}` be the degree-`K` Taylor
polynomial at `b=6/11` of `exp(N(s-b))D_N(s)`. The canonical moving-depth Hermite counterterm is

`c_{N,K}(s)=-exp(N(b-s))H_{N,K}(s)`.

It cancels the raw value at `b` for every depth. On the Cauchy circle of radius `1/77`, the dressed
source has norm at most `N exp(N/77)`. Evaluating its Taylor polynomial at the independent witness
`a=4/7`, whose distance from `b` is `2/77`, costs at most `2^(K+1)`. After the separating
exponential is restored,

`|c_{N,K}(4/7)| <= N 2^(K+1) exp(-N/77)`.

Using the fourth Taylor lower bound for `exp(7/10)` gives `2^K<=exp(7K/10)`, while
`1/77-7/(10*54)=1/41580>0`. Consequently every depth schedule with `K(N)<=N/54` makes this
counterterm tend to zero at `4/7`. The interior
multi-anchor theorem says any locally bounded cofinal corrected family requires an unbounded
counterterm there, yielding a contradiction. The earlier `1/154` estimate remains as a compatibility
corollary.

Status: `[LINEAR-DEPTH HERMITE CLASS CLOSED] [NOT RH]`. This strictly extends the fixed-depth
closure to a growing linear class. A surviving point-Hermite schedule must exceed this slope (the
constant is conservative, not claimed sharp), or replace point Taylor interpolation with a
distributed/nonlocal transition. Lean:
`SquarefreeConvolutionHalfMovingHermiteNoGo.lean`; direct Lean check passes.

## 2026-09-03 — Far witness closes point-Hermite depths through slope `1/15`

The same moving Taylor/Hermite correction admits a stronger independent test at `s=2/3`, whose
Cayley coordinate is exactly `-2`. Explicit alternating-binomial estimates show that the Cayley
square-root factor has norm at least one for every cutoff `N>=8`; hence a locally bounded corrected
family still requires its counterterm to be unbounded at this point.

A radius-`1/22` Cauchy estimate about `b=6/11` and the gap `2/3-6/11=4/33` give

`|c_{N,K}(2/3)| <= N 3^(K+1) exp(-5N/66)`.

The elementary bound `3<=exp(11/10)` then makes the right side tend to zero for every schedule
eventually satisfying `K(N)<=N/15`; the remaining exponential rate is `2/825`. This contradicts
the exact counterterm-unboundedness necessity at `2/3`.

Status: `[FAR-WITNESS LINEAR-DEPTH CLASS CLOSED] [NOT RH]`. Every surviving point-Hermite schedule
must exceed `N/15` infinitely often. This constant is sufficient, not sharp. Distributed or
nonlocal transitions remain open, as do high-slope point-Hermite schedules whose Euler-chamber
compact-open behavior has not yet been controlled. Lean:
`SquarefreeConvolutionHalfMovingHermiteFarWitnessNoGo.lean`; direct Lean check passes.

## 2026-09-03 — Superdiagonal Hermite depth destroys Euler source fidelity

Large Taylor depth fails for a different reason. At the Euler point `s=1101/1100`, use the full
radius-`6/11` circle about `b=6/11`; this circle remains in `Re(s)>=0`, where the finite Dirichlet
source has norm at most `N`. A centered Cauchy remainder theorem gives

`|H_{N,K}(1101/1100)-exp(501N/1100)D_N(1101/1100)|
  <= (200/33) N exp(6N/11) (167/200)^(K+1)`.

After undoing the exponential dress, the corrected source obeys

`|D_N(1101/1100)+c_{N,K}(1101/1100)|
  <= (200/33) N exp(9N/100) (167/200)^(K+1)`.

A fourth-order Taylor remainder proves `exp(1801/10000)<=200/167`, hence
`167/200<=exp(-1801/10000)`. Every schedule eventually satisfying `K(N)>=N/2` therefore makes this
tend to zero with residual exponential rate `1/20000`. But source admissibility would make the
counterterm tend to zero while `D_N(1101/1100)` tends to its nonzero Euler product. Hence every
schedule eventually above slope `1/2` is source-unfaithful.

Status: `[HIGH-DEPTH SOURCE-FIDELITY CLASS CLOSED] [NOT RH]`. Combined exact survivor for the
canonical point-Hermite construction: a viable schedule can be neither eventually at most `N/15`
nor eventually at least `N/2`. Intermediate slopes and schedules oscillating between regimes
remain open; distributed/nonlocal transitions remain separate. Lean:
`SquarefreeConvolutionHalfMovingHermiteHighDepthNoGo.lean`; direct Lean check passes.

## 2026-09-03 — Arithmetic mode tails sharpen high-depth failure to `37/80`

The preceding Cauchy estimate discards finite Dirichlet structure. Expanding the positive dress
mode by mode gives frequencies `N-log n`. At `s=1101/1100`, undoing the dress identifies each
corrected mode exactly with a Poisson upper tail of action

`x_{N,n}=((N:real)-log n) * 501/1100`, with `0<=x_{N,n}<=(501/1100)N`.

An exponential Chernoff tilt proves

`exp(-x) (exp(x)-sum_{j<K+1} x^j/j!)
  <= exp(-(K+1)t+x(exp(t)-1))`.

Taking `t=1/75`, the first-order factorial remainder gives `exp(1/75)<=75/74`. Therefore, if
`K>=37N/80`, the entire corrected source satisfies

`|D_N(1101/1100)+c_{N,K}(1101/1100)|
  <= N exp(-29N/2442000)`.

It tends to zero, contradicting source fidelity to the nonzero Euler product. This strictly
improves the generic Cauchy threshold `N/2` without changing the Hermite construction.

Status: `[ARITHMETIC HIGH-DEPTH SOURCE-FIDELITY CLASS CLOSED] [NOT RH]`. Combined exact survivor
for the canonical point-Hermite construction: a viable schedule can be neither eventually at most
`N/15` nor eventually at least `37N/80`. Intermediate slopes and schedules oscillating between
regimes remain open; distributed/nonlocal transitions remain separate. Lean:
`SquarefreeConvolutionHalfMovingHermiteArithmeticHighDepthNoGo.lean`; direct Lean check passes.

## 2026-09-03 — Near-one witness closes point-Hermite depths through `N/3`

Move the independent interior test to `s=10/11`, where the shifted pole Cayley coordinate is
`-6/5`. The `(-1/2)` binomial weights eventually grow by at least `21/20`; explicit parity bounds,
together with a nonzero lower bound for the `(1/2)` factor, prove that the finite Cayley square-root
factor has norm at least one for every cutoff at least `264`.

For the moving Hermite correction, the radius-`1/3` Cauchy circle about `b=6/11` remains in
`Re(s)>=0`. Since the witness gap is `4/11`, the Taylor ratio is `12/11`, and

`|c_{N,K}(10/11)| <= 11 N (12/11)^(K+1) exp(-N/33)`.

The third Taylor lower bound gives `12/11<=exp(9/100)`. Every schedule eventually satisfying
`K(N)<=N/3` therefore makes the counterterm tend to zero, with residual exponential rate `1/3300`.
This contradicts the exact interior unboundedness forced by local boundedness of the corrected
family.

Status: `[NEAR-ONE LINEAR-DEPTH HERMITE CLASS CLOSED] [NOT RH]`. Combined exact survivor for the
canonical point-Hermite construction: a viable schedule can be neither eventually at most `N/3`
nor eventually at least `37N/80`. Intermediate slopes and oscillatory schedules remain open;
distributed/nonlocal transitions remain separate. Lean:
`SquarefreeConvolutionHalfMovingHermiteNearOneWitnessNoGo.lean`; direct Lean check passes.

## 2026-09-03 — Very-near-one witness closes point-Hermite depths through `3N/8`

Move the independent interior test to `s=20/21`, where the shifted pole Cayley coordinate is
`-11/10`. The `(-1/2)` binomial weights eventually grow by at least `21/20`; exact parity bounds,
together with a `1/100` lower bound for the `(1/2)` factor, prove that the finite Cayley
square-root factor has norm at least one for every cutoff at least `271`.

For the moving Hermite correction, the radius-`3/8` Cauchy circle about `b=6/11` remains in
`Re(s)>=0`. The witness gap is `94/231`, the Taylor ratio is `752/693`, and

`|c_{N,K}(20/21)| <= 12 N (752/693)^(K+1) exp(-59N/1848)`.

The Taylor lower bound gives `752/693<=exp(1/12)`. Every schedule eventually satisfying
`K(N)<=3N/8` therefore makes the counterterm tend to zero, with residual exponential rate
`5/7392`. This contradicts the exact interior unboundedness forced by local boundedness of the
corrected family.

Status: `[VERY-NEAR-ONE LINEAR-DEPTH HERMITE CLASS CLOSED] [NOT RH]`. Combined exact survivor for
the canonical point-Hermite construction: a viable schedule can be neither eventually at most
`3N/8` nor eventually at least `37N/80`. The remaining monotone band is
`3/8 < K(N)/N < 37/80`; oscillatory schedules and distributed/nonlocal transitions remain open.
Lean: `SquarefreeConvolutionHalfMovingHermiteVeryNearOneWitnessNoGo.lean`; direct Lean check
passes.

## 2026-09-03 — Same witness closes point-Hermite depths through `2N/5`

Keep the arithmetic witness `s=20/21` and enlarge the Cauchy circle about `b=6/11` to radius
`2/5`, still wholly inside `Re(s)>=0`. The witness gap remains `94/231`, so the Taylor ratio is
now `235/231`, and

`|c_{N,K}(20/21)| <= 58 N (235/231)^(K+1) exp(-8N/1155)`.

The Taylor lower bound gives `235/231<=exp(1/58)`. Every schedule eventually satisfying
`K(N)<=2N/5` therefore makes the counterterm tend to zero, with residual exponential rate
`1/33495`. The existing exact pole-factor lower bound at `20/21` then contradicts local
boundedness of the corrected family.

Status: `[TWO-FIFTHS LINEAR-DEPTH HERMITE CLASS CLOSED] [NOT RH]`. Combined exact survivor for
the canonical point-Hermite construction: a viable schedule can be neither eventually at most
`2N/5` nor eventually at least `37N/80`. The remaining monotone band is
`2/5 < K(N)/N < 37/80`; oscillatory schedules and distributed/nonlocal transitions remain open.
Lean: `SquarefreeConvolutionHalfMovingHermiteTwoFifthsNoGo.lean`; direct Lean check passes.

## 2026-09-03 — Pole-factor growth is uniform over all fixed interior witnesses

The fixed rational cutoff calculations are no longer needed. For every real exterior modulus
`x>1`, the successive ratios of both relevant binomial coefficient magnitudes tend to `x`. The
`(1/2)` partial sums therefore tend to `-infinity`; the odd and even parity subsequences of the
alternating `(-1/2)` partial sums tend to `+infinity` and `-infinity`, respectively. Their product
has norm at least one on every sufficiently large cutoff.

For every real `sigma` with `1/2<sigma<1`, the shifted Cayley coordinate is
`-(2/sigma-1)` and `2/sigma-1>1`. Consequently every cofinal locally bounded corrected family
forces its counterterm to have no bounded tail at every fixed real point of the open critical
strip, not only at selected rational witnesses.

Status: `[GENERAL INTERIOR POLE-FACTOR GROWTH CLOSED] [NOT RH]`. Positive survivor: low-depth
Hermite obstructions may now choose the witness continuously. This is the missing reusable input
for closing every eventual linear slope strictly below the geometric threshold `5/11`. Lean:
`SquarefreeConvolutionHalfInteriorPoleFactorGeneral.lean`; direct Lean check passes.
