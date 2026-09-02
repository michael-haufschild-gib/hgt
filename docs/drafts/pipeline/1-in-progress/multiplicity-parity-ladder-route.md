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
