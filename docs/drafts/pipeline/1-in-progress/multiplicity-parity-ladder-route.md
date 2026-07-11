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
- `[CONJECTURE]` **Clifford filtration of the ladder.** Rung `k` ⟺ realization carrying a
  `Cl_{2k}(ℂ) ≅ M_{2^k}(ℂ)`-module structure on off-line root spaces (the unique irreducible
  representation has dimension `2^k`, forcing `2^k ∣ mult`). The dyadic tower of rungs is the
  Clifford/Bott periodicity tower: rung-raising = adjoining two anticommuting odd generators,
  matching the Kummer squaring law. The cofinal criterion becomes: **an unbounded emergent
  Clifford tower on finite-dimensional root spaces is impossible unless the off-line spectrum is
  empty** — RH as "the off-line spectrum is forced to carry more symmetry than any finite
  multiplicity can hold". Constraint-side throughout: symmetry-algebra size against finiteness;
  no flow, no deformation parameter.
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
- [ ] 1 → 2  fully-proven: the Clifford rung-`k` mechanism on paper; the closure reading's
      limit-parity lemma written; any construction progress on the seam-anomalous `J`
- [ ] 2 → 3  formalized: Clifford mechanism (`M_{2^k}`-module ⟹ divisibility of every root-space
      dimension) in Lean; rung-`k` analogue of `rhLadder_one_iff_symplecticRealization`
- [ ] 3 → 4  publication-ready

## Open core

`[OPEN CORE]` Any rung `k ≥ 1`. Localized by this card: construct, from Euler data, a symplectic
structure on an operator model of the off-line divisor whose anomaly is line-supported — the
parity-weakening of Hilbert–Pólya. Every ingredient except the arithmetic construction is now a
theorem.

## Log

- 2026-07-11 — created in 1-in-progress; divisor-lattice + sharp-level + Kramers bricks banked in
  Lean; walls consolidated from banked no-gos; program stack stated.

## Next move

Formalize the Clifford rung-`k` mechanism (a module over a matrix algebra `M_d` has every
submodule dimension divisible by `d`; apply to root spaces) and instantiate the first candidate
`J` on the Sonin/HS window substrate: the two shortest paths from this card into new theorem
ground.
