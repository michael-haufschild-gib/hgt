# The weld as an infinite origami: flat geometry of d log ξ

- **ID:** weld-origami
- **Stage:** 1-in-progress
- **Type:** CONJECTURE (program) + THEOREM (dictionary bricks)
- **Source:** novelty-gate challenge (reframe demand); rng draw: tropical-berkovich × origami ×
  knot-tying; successor frame for defect-protection + seam-sign-pinning
- **Statement:** The completed object carries a canonical square-tiled (origami) flat structure —
  the |d log ξ| metric with integral absolute periods — in which zeros are half-infinite cylinders
  of integer circumference, critical points are cone points, the critical line is a crease
  developing onto lattice lines, and RH is the flat-foldability statement: every singularity of
  the origami lies on the crease.

## The reframe

Take ω := d log ξ = (ξ′/ξ) ds. It is meromorphic on ℂ with ONLY simple poles, exactly at the
zeros of ξ, with residue = the vanishing order m ∈ ℕ; its zeros are the critical points of ξ.
Consequences, all structural (no height, no flow, no carrier):

1. **Integral periods.** Every absolute period ∮ω lies in 2πi·ℤ (the argument principle read as
   integrality). The developing map F = log ξ therefore presents the zero-complement as a cover
   of the standard cylinder, and the |ω|-flat metric tiles the weld by unit squares (pullbacks of
   the modulus–phase grid): **the weld is canonically an infinite square-tiled surface — an
   origami in the flat-geometry sense.**
2. **Defect dictionary.** A zero of order m = a half-infinite flat cylinder end of circumference
   2πm (cycle of m squares). A critical point of order k = a cone point of angle 2π(k+1). The
   deck charge of the defect-protection program = the flat holonomy; the cylinder circumference
   IS the banked winding.
3. **Two flat symmetries.** σ : s ↦ 1 − conj s is an anti-flat isometry whose fixed geodesic (the
   critical line) develops into the horizontal lattice lines Im F ∈ πℤ — **the seam-sign bit of
   SeamSignBit.lean is the lattice height mod 2 of the crease** (sign + ⟺ Im F ∈ 2πℤ, sign − ⟺
   Im F ∈ π + 2πℤ); the FE s ↦ 1−s is a flat half-turn about the centre. The entire seam-sign /
   equivariant-twist session is the local theory of this crease.
4. **Boundary models.** Beyond the wall the origami is defect-free (banked:
   `xi_chargeFree_beyond_wall`) — asymptotically the standard grid of the Euler product; the
   archimedean end is the Γ-log end. The strip is the interpolation region; all defects live
   there, and the tiling widens logarithmically with height.
5. **Combinatorial encoding.** A square-tiled surface is a pair of permutations (horizontal,
   vertical) of its squares; cylinders are h-cycles, cone points are commutator defects. **The
   divisor of ξ = the cycle type of an explicitly constrained infinite permutation pair**, with σ
   and the FE acting as symmetries. RH ⟺ no σ-swapped pair of h-cycles ⟺ every cycle is
   σ-symmetric. (Knot-strand reading: cylinders are strands braided through the widening strip;
   the permutation pair is the braid datum.)

## RH restated (the flat-foldability form)

> `[CONJECTURE — the program]` RH ⟺ the weld origami folds flat along its crease: every
> singularity (cylinder end AND cone point) lies on the fixed geodesic. The zero half is the
> classical statement; the cone-point half is Speiser's theorem `[KNOWN]` — the flat structure
> unifies the two as one foldability condition.

The native (non-corpus) questions this opens — the actual research program:

- **Realizability/obstruction:** which infinite, logarithmically-widening, σ-real origamis with a
  standard grid end and a Γ-log end are developable (arise from a globally univalent flat
  immersion of the strip)? Flatness + the two boundary models + the crease reality are strong
  local rules; the moonshot `[CONJECTURE]` is a boundary-forced foldability theorem: the boundary
  data leaves no room for interior defects — holography of tilings, "the constraint fixes the
  bulk tiling".
- **Equivariant cylinder combinatorics:** Smith-type constraints on σ-actions on the permutation
  pair; which cycle types admit free σ-pairs compatibly with the FE half-turn and the widening
  profile.
- **Saddle-connection ledger:** flat geodesics between cone points and cylinder ends as a new
  finite local datum per window (replacing analytic estimates by flat lengths — lengths are
  periods, hence exact, not estimated).

## Firewalls (what is corpus, and must not be re-derived)

- Speiser's theorem (cone-point half) — [KNOWN]; use as dictionary only.
- Bohr–Landau clustering = the degenerate naive tropical limit of the tiling — [KNOWN]; the
  reframe must never argue through zero-density/value-distribution (that is height-measuring,
  banned).
- Argument principle / residue = the integrality of periods — banked in-tree as winding calculus.

## First bricks

- (B1) Dictionary at the level already formalized: circumference := flat holonomy = 2π·winding —
  the banked `boxCharge`/`windingNumber` calculus IS the cylinder ledger; nothing to rebuild.
- (B2) The crease develops onto lattice lines = `fESchwarz_real_on_line` (banked today).
- (B3) `[NEXT Lean]` the wall-side standard grid: defect-freeness banked
  (`xi_chargeFree_beyond_wall`); add the seam-height statement there via
  `XiRealAnchorPositive` (in flight): at the real anchor the crease sits on the EVEN lattice line
  (sign +), fixing the global lattice offset of the whole origami.
- (B4) `[NEXT Lean]` the σ-action on cylinders: an on-line zero's cylinder is σ-invariant with
  two fixed rays; an off-line pair's cylinders are swapped — the equivariant-twist module
  (`RealRootTower.lean`, `equivariant_pow_root_iff`) is exactly the σ-invariant-cylinder root
  theory; state the cylinder-language corollary.

## Gates
- [x] 0 → 1  in-progress: objects precise, dictionary mapped, firewalls named, bricks listed
- [~] 1 → 2  fully-proven: packing stratification COMPLETE (layers 1–5 settled; layer 6 = the
      moonshot, open); B1–B4 bricks done
- [~] 2 → 3  formalized, all axiom-clean, in umbrella: `SymmetricDivisorRealization.lean`
      (`no_local_packing_obstruction`, `symmetric_divisor_realizable`, FESchwarz closure algebra,
      `linePair`/`realPair` blocks); `RealRootTower.lean` (`equivariant_pow_root_iff`,
      `equivariant_full_tower_iff`, `xi_circleLoop_equivariant`,
      `xi_window_equivariant_root_iff`); `XiRealAnchorPositive.lean` (`xi_real_on_real_anchor`,
      `xi_pos_on_real_anchor` — ζ < 0 on (0,1) built from scratch, absent from mathlib)
- [ ] 3 → 4  publication-ready (waits on layer-6 progress)

## Log
- 2026-07-09 — created from the novelty-gate challenge; rng axis tropical-berkovich; origami
  collision identified the integral-period structure; knot collision gave the braid reading of
  the permutation pair.

## §Packing: the equivariant cylinder-packing obstruction, located exactly

The obstruction question is stratified by constraint layer; every layer below arithmetic is now
settled EMPTY, so the obstruction is located, not merely conjectured:

1. **Local layer — EMPTY [PROVED, Lean, axiom-clean].** `symmetric_divisor_realizable` +
   `no_local_packing_obstruction` (SymmetricDivisorRealization.lean): products of orbit quartics, crease pairs
   `(s−(½+τi))(s−(½−τi))` and real pairs `(s−r)(s−(1−r))` realize EVERY finite symmetric divisor
   exactly, inside FE+Schwarz. No local flat/symmetry rule constrains cylinder packing at all —
   the full-divisor strengthening of the softness metatheorem.
2. **Quantitative-soft layer — EMPTY [corollary of 1].** Any true packing inequality (bounding
   σ-swapped cylinder pairs per window by width/crease/symmetry data) would be violated by a
   realization from layer 1; hence every true packing bound must carry hypotheses beyond flat
   symmetry. There is no soft quantitative obstruction to prove — and this emptiness is itself
   the theorem.
3. **Growth layer — CORPUS [firewalled].** Adding order-1 growth yields only Jensen-type count
   bounds = classical zero-counting (height-measuring, banned as a route and known regardless).
   The growth layer adds no packing information beyond the corpus.
4. **Crease-data layer — EXACTLY the proven sign calculus.** The crease word (lattice heights,
   parities between anchors) determines crease-order parities (`line_sign_flip_iff_odd_total_order`)
   and pins odd clusters (`online_odd_cluster_pinned`); σ-swapped pairs are PROVABLY invisible to
   all of it (sign-blindness). The crease can never see the packing.
5. **Abstract-flat layer — unobstructed by construction.** Any symmetric permutation pair glues
   to a real square-tiled surface; abstract realizability is definitional. All content lies in
   DEVELOPABILITY to `d log f` for f in a constraint class — and layers 1–2 show developability
   over FE+Schwarz is unobstructed too.
6. **Arithmetic layer — the residual home of the obstruction [OPEN, the moonshot].** On `re > 1`
   the Euler product writes the tiling explicitly: each prime contributes a periodic shear of
   period `2π/log p`; the superposition is the **arithmetic origami**, defect-free (proven:
   `xi_chargeFree_beyond_wall`). The packing obstruction, if it exists anywhere, is the
   **continuation rigidity of the arithmetic origami**: which extensions of that explicit tiling
   across the log-widening strip to the Γ-end exist, and do all of them fold flat along the
   crease? This is the origami form of the germ-continuation frontier (GermExtension /
   WeldTowerLimit): every frame of this program relocates RH onto the same reach-across-the-strip
   question, and the origami frame contributes the new toolset — period coordinates (critical
   values as relative periods), cylinder surgery, equivariant flat geometry.

**Verdict:** the equivariant cylinder-packing obstruction does not exist below arithmetic
coupling — proven, not suspected — and at arithmetic coupling it IS the strip-continuation
rigidity. Next constructive step of the program: compute the arithmetic origami's permutation
pair explicitly for the first primes (a finite combinatorial object, exact — periods, not
estimates) and pose the continuation problem for it as a standalone combinatorial question.

## §The arithmetic origami is a pants decomposition [SEARCH register, exact dictionary]

In the chart u = p^{-s} a single Euler factor contributes ω_p = d log (1−u)^{-1} = du/(1−u): the
single-prime origami is a flat PAIR OF PANTS (three ends; the u = 1 end a cylinder of integer
circumference; vertical period 2π/log p in the s-plane). The Euler product presents the weld's
beyond-wall tail as an infinite superposition of prime pants — **multiplicativity = a pants
decomposition of the tail**, with Fenchel–Nielsen-type data: lengths from the periods 2π/log p,
twists from the prime phases. The strip is precisely where the decomposition ends and the surface
must be continued to the Γ-end across the crease. The moonshot of §Packing in these terms: the
continuation of a pants-decomposed real origami across a log-widening strip is rigid — no
interior defects survive. (Surface-theory toolboxes this imports: Fenchel–Nielsen coordinates,
pants-graph combinatorics, TQFT-style gluing — none of them RH-corpus instruments.)

## §Layer-6 toy case: attacked and exhausted

**(a) Asymptotic tails are blind [PROVED, Lean, axiom-clean — TailBlindness.lean, `not_forcesRHParity_of_dlogTail`, `dlog_orbitQuartic_vanishes`].** The
logarithmic derivative of an orbit quartic vanishes toward the arithmetic end, so any tail
condition constraining only the asymptotic tiling (dlog shape as re → ∞) is stable under quartic
surgery; by the banked cut theorem such classes carry off-line charge and can never force parity.
Single-prime (indeed any-tail) TOY RIGIDITY IS FALSE for tiling-asymptotic hypotheses.

**(b) Exact finite-prime completions are unique and unfoldable [PROVED, Lean — `toyCompletion_offline_defect`].** An
exact identity `g = archFactor·∏_{p ∈ P}(1−p^{−s})^{−1}` on a half-plane determines g outright
(identity theorem) — rigidity trivializes to uniqueness — and the resulting member is UNFOLDABLE:
`archFactor` has an uncancelled simple zero at s = 1 (off-crease), removed in the true weld only
by the pole of ζ, i.e. by the divergence of the full prime ensemble. **The first foldability
event of the weld (no defect at s = 1) IS the divergence of the prime harmonic series** — the
Mertens shadow of foldability. No finite sub-product can fold.

**(c) Verdict — the moonshot is now hypothesis-minimal.** Layer-6 rigidity requires BOTH the
exact identity (asymptotics refuted by (a)) AND the infinite ensemble (finite exactness refuted
by (b)): the minimal viable object is precisely the infinite-prime germ on the half-plane — the
germ of GermExtension. Every weakening of the moonshot's hypotheses is now refuted by theorem;
the open core is named, minimal, and shared with the tower frontier.

## §The period map's origin [PROVED, Lean, axiom-clean]

`xi_central_window_realTower` (RealRootTower.lean §4): the equivariant period map of the weld —
window ↦ (winding, anchor sign), the complete deformation invariant by the equivariant
h-principle — takes the value **(0, +) at the central window, forced by the coefficient side**
(the η-positivity chain gives ξ(½) > 0; continuity gives a vacuum radius with positive anchor).
By the per-window criterion the central window therefore carries an equivariant `2^k`-th root of
the ξ-boundary loop at every positive level: **the Real root tower of ξ exists unconditionally at
the centre of the weld.** The programme's open core is thereby upgraded from the existence of a
conjectured object to the REACH of an existing one — how far the central Real-tower germ extends
along the crease and into the strip, with the exact infinite-prime identity (proven minimal by
the toy theorems) as its only possible engine.

## §Crease reach [PROVED, Lean, axiom-clean]

`xi_crease_reach_realTower` (with `xi_fESchwarz`): the period map's origin value propagates — for
any window `closedBall (linePt τ) r` on which ξ is nonvanishing, with ξ also nonvanishing on the
crease segment `[0, τ+r]`, the transported sign is positive (IVT on the real restriction from the
arithmetically pinned centre) and the window carries the equivariant `2^k`-root at every positive
level. **The Real tower's reach is bounded below by every zero-free crease stretch, as a
theorem.** The remaining reach questions are exactly the two faces of the minimal engine: past a
crease zero the sign law is the banked parity reading (odd flips, even survives — per-level
divisibility takes over), and into the strip is the exact infinite-prime germ. Nothing below that
engine remains open in this thread.

## §Ledger evaluation: windings and signs beyond zero-free stretches [PROVED, Lean, axiom-clean]

`CreaseHolonomy.lean` — the complete theory-level evaluation of the per-window obstruction pair:

* `xi_line_zeros_finite` — crease zeros of ξ in a compact parameter interval are finite.
* `xi_line_multi_peel` — global multi-zero peel of ξ along a crease segment (interior on-line
  zeros peeled, cofactor analytic on ℂ and nonvanishing on the segment).
* `xi_line_sign_iff_even_cumulative_order` — **crease holonomy**: for `τ > 0` with
  `ξ(linePt τ) ≠ 0`, the crease sign at `τ` is `+` ⟺ the cumulative crease order in `(0,τ)` is
  even, transported from the arithmetically pinned `ξ(½) > 0`.
* `xi_window_tower_iff_ledger` — **the full evaluation**: the equivariant `2^k`-root of the
  boundary loop of the window `(linePt τ₀, r)` exists ⟺ `2^k ∣ D(W)` (total enclosed order) ∧
  the cumulative crease order in `(0, τ₀+r)` is even. Both coordinates of the `π₀ ≅ ℤ × ℤ/2`
  classification are now exact ledger reads — no analytic data beyond the divisor enters.

The directive "the actual windings and signs of ξ beyond zero-free crease stretches" is closed at
theory level: winding = `D(W)` (argument principle, banked), sign = crease-ledger parity (holonomy,
new). What remains about actual VALUES is the divisor itself — the exact infinite-prime germ,
proven the minimal engine (TailBlindness). See the dissolution section of `seam-sign-pinning.md`
for where each ledger coordinate can and cannot obstruct (region/boundary/off-line stratification).

## §Germ blindness, completed: the carrier is exact-infinite-non-tail [PROVED, Lean, axiom-clean]

`FiniteEulerInert.lean` — the second germ no-go, closing the pants/FN question from below:

* `fePants p = (1 − p^{−s})(1 − p^{−(1−s)})` — the FE-completed local factor: entire, FESchwarz,
  and **nonvanishing on the open strip** (its zeros are the clock lattices `(2πi/log p)ℤ` on the
  walls `Re ∈ {0,1}` — finite pants data lives on the walls, never in the strip).
* `feBundle_divisor_inert` — multiplying any member by the finite bundle changes NO vanishing
  order at any strip point.
* `finiteEulerClass_isSoft`, `finiteEulerClass_not_forcesRHParity` — the class of members carrying
  the exact P-pants remains fully soft (plants arbitrary off-line charge; parity toggle absorbs
  wall-lattice orders): **finite exact Euler data imposes no divisor constraint whatsoever.**

Synthesis of the two no-gos: TailBlindness kills all ASYMPTOTIC germ data; FiniteEulerInert kills
all FINITE EXACT germ data (FE-completed, any prime set). The divisor-constraining content of the
Euler germ is therefore carried only by the **exact infinite product as a whole** — consistent
with, and sharpening, `GermExtension.rhLadder_iff_germ_extends`: the rung is a continuation
statement about one infinite arithmetic object, and no finite or asymptotic shadow of it retains
any of the constraint.

Firewalls recorded (attack-as-false on the successor lane): (i) the FE-completion of the FULL germ
is ξ(s)ξ(1−s) = ξ² — the function-level weld defect is zero BY the FE, so the mirror divisor N is
NOT a weld defect of that object; (ii) stratifying weldability over infinite sub-products
Q ⊆ primes (which ζ_Q continue) is Langlands/Beurling corpus — banned as search. (iii) rng draw
queueing-at-borders × auction-theory collided with the residue: lands on extremal/marginal
statistics of the prime stream = resonance/large-values corpus [KNOWN] and the banned height
frame; the tropical/max-plus reading is the already-firewalled degenerate limit. No new object
survived the gate — the negative results are recorded to prevent re-derivation.

## §The open core, bounded on every side [synthesis; certificates named]

The standing open core — the continuation of the exact infinite product as a single object — is
now bounded on every side the program possesses, each side with its certificate:

1. **Germ-shadow side — CLOSED BY PRINCIPLE.** Shadows of the germ act on the strip through
   nonvanishing objects (tail: TailBlindness; finite exact: FiniteEulerInert, wall-supported;
   thin-infinite exact: VACUOUS — on its convergence sub-strip `σ_Q < Re < 1−σ_Q` a thin bundle
   `B_Q` is nonvanishing, so EVERY entire FESchwarz member factors through it and the decoration
   constrains nothing). General principle: a decoration nonvanishing at a point is divisor-inert
   there (the `feBundle_divisor_inert` mechanism, generic). Constraint requires vanishing; the
   only germ object whose strip continuation vanishes is the full product, and its vanishing IS
   the divisor. No further sub-germ no-go exists to prove — they are all instances. [Do NOT build
   the thin-infinite tprod module; it formalizes a vacuity.]
2. **Class-level side — CLOSED AT SATURATION.** FESchwarz soft; + Dirichlet shape soft; + finite
   exact Euler soft; + full multiplicativity = two-sided-hard (forcing parity would be RH-grade;
   refuting needs an FE+Euler off-line member, equally open). The trichotomy ladder ends at the
   wall on both sides.
3. **Equivariant/topological side — CLOSED BY THEOREM.** Complete obstruction map (dissolution,
   holonomy, ledger evaluation); all RH content = the off-line equivariant coherent ℤ₂-tower,
   obstruction = pure divisor data.
4. **Spectral side — CLOSED AS NO-GO.** `seam_spectral_iff_rh`: the missing spectral ingredient
   is not a bridge lemma, it IS RH (and Hilbert–Pólya is banned as route regardless).
5. **Realization side — CLOSED.** No local packing obstruction; every finite symmetric divisor
   realizable in the bare class.
6. **Dead angles this round (pre-build kills, do not re-derive):** (a) deck-dyadicity =
   coefficient-dyadicity of the root germ — numerology, the ladder base is conventional; (b) the
   global monodromy representation `π₁(ℂ∖Z(ξ)) → ℤ₂` — unconditional but a repackaging of banked
   deck classes, no new constraint content; (c) almost-periodic/spectral-leakage re-cut — Bohr
   corpus; (d) extremal-prime-statistics carrier — resonance/height corpus, banned frame.

Reading: the core is irreducible from below for a stated structural reason — germ data reaches
the divisor only by already containing it (continuation values), never through a structural
shadow. Every attack on the core must therefore engage the exact infinite object whole; partial
handles are certified dead. The instrumented target remains the off-line coherent tower, whose
obstruction the ledger theorems read exactly.
