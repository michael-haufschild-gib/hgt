# Seam-sign pinning: what distinguishes off-line zeros

- **ID:** seam-sign-pinning
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean, bricks) + CONJECTURE (pinning dichotomy)
- **Source:** successor of defect-protection (π₀ classification); question: what property do
  off-line zeros have that on-line zeros cannot meet, and what constraint lets them off the line?
- **Statement:** Off-line zeros are exactly the seam-sign-invisible defects; odd on-line defects
  are pinned to the line by a second conserved quantity (the endpoint sign bit of the real
  restriction), and escape from the line is only possible by pair creation at an even-order
  on-line collision.

## The three dichotomies

**D1 [PROVED, banked substrate] Orbit dichotomy.** The FE and Schwarz involutions compose to the
critical-line reflection `s ↦ 1 − conj s`. On-line zeros are its fixed points; off-line zeros are
free orbits with a distinct equal-order mirror partner. Ledger form: `D = L + 2N`
(WindowRelation); consequence: off-line charge is paired, hence invisible to every
reflection-invariant parity reader (DeciderBarrier).

**D2 [BRICKS PROVED / DICHOTOMY OPEN] Seam-sign dichotomy.** Every FE+Schwarz member is
real-valued on the critical line, so the line carries a second invariant beyond the deck charge:
the sign bit of the real restriction at any nonvanishing line point, conserved along every
deformation keeping that point nonvanishing (`SeamSignBit.lean`: reality lemma + sign
conservation + the two-invariant package with the moving-window charge).
`[CONJECTURE]` **Pinning dichotomy:** in a line-symmetric window under FE+Schwarz-preserving
deformation with nonvanishing boundary and line-endpoints, an odd on-line cluster can never fully
leave the line (its window sign flip is conserved while `D` is conserved and off-line
contributions to `D − L` are even); off-line defects are exactly the charge carriers invisible to
the sign bit. `[OPEN CORE]` the real-zero parity reading: sign flip across the window ⟺ odd `L`
(needs a real-restriction zero-parity count for continuous members; for analytic members via the
peel this is the Hardy mechanism, cf. HardySignChange for the carrier-specific version).

**D3 [PROVED, banked] Interior/boundary dichotomy.** `rightHalf` is open: line zeros are never
enclosed by the right-half root tower and obstruct nothing; off-line zeros are interior
obstructions (nonzero two-circle modulus slope, nontrivial deck class). RH = all obstructions are
boundary.

## The answer to the source question

The property off-line zeros have that on-line zeros cannot meet: **a free mirror partner** (D1) —
equivalently, charge decoupled from the seam sign (D2). The property on-line (odd) zeros have
that off-line zeros cannot: **seam-sign coupling** — their existence is readable from two real
numbers at the window's line-endpoints. The constraint that "allows" a zero off the line: escape
preserves the sign data only via pair creation at an even-order on-line collision — off-line
zeros are born in pairs from on-line collisions or imported through window boundaries; they never
leave alone. RH restated: the seam-sign coupling never breaks — every defect of ξ is
sign-visible.

## Gates
- [x] 0 → 1  in-progress: dichotomies stated, bricks specified
- [x] 1 → 2  fully-proven: bracket pinning, parity reading, full pinning dichotomy, equivariant
      h-principle — all proved (residual [KNOWN, unformalized]: real-anchor positivity ξ > 0 on
      (0,1) via η-positivity)
- [x] 2 → 3  formalized, all axiom-clean, in the umbrella:
      `SeamSignBit.lean` (`fESchwarz_real_on_line`, `line_sign_conserved`,
      `seam_two_invariants_conserved`, `online_zero_pinned_of_sign_bracket`);
      `SeamSignParity.lean` (`line_sign_flip_iff_odd_total_order`, `online_odd_cluster_pinned` —
      the full pinning dichotomy);
      `SeamEquivariantTwist.lean` (`equivariant_log_twist`, `twist_parity_eq_sign`,
      `equivariant_joined_of_winding_sign_eq`, `equivariant_joined_iff` — π₀ ≅ ℤ × ℤ/2);
      `ConnectedSymmetryBarrier.rh_iff_seam_blind_windows_chargeless` (the RH re-cut: charge only
      where the seam can see it); `DirichletShapeCharge.xi_chargeFree_beyond_wall` (Euler
      contrast)
- [ ] 3 → 4  publication-ready

## Approach
Bricks: reality on the line for FESchwarz; endpoint sign conservation along families; the
two-invariant conservation package (deck charge at all levels + sign bit). Then the parity
reading: for members analytic near the line-segment, `L mod 2` = sign flip, via the peel and the
real restriction; assemble the pinning dichotomy. Wild-analogy anchor: defect pinning on the
fixed locus of an anti-unitary symmetry (topological insulators' particle–hole symmetry — zeros
pinned at symmetric points unless they split in pairs).

## Log
- 2026-07-08 — created; D1/D3 identified as banked; D2 bricks delegated (`SeamSignBit.lean`);
  pinning dichotomy labeled with its open core.

## §Deeper: the equivariant classification behind the dichotomy

`[CONJECTURE]` **Equivariant π₀ (the KR-shadow).** The critical line is the fixed locus of the
anti-holomorphic involution `σ : s ↦ 1 − conj s`, and an FE+Schwarz member is a σ-equivariant map
into `ℂ*` (real on the fixed locus). The symmetric pair space should classify by the pair
(winding `n` ∈ ℤ, endpoint sign data ∈ ℤ/2) subject to the compatibility `n ≡ sign-flip (mod 2)`
— the topological-defect analogue of the classification of Real (Atiyah) line bundles: bulk
charge ℤ, fixed-locus sign ℤ/2, welded by a mod-2 constraint. The non-equivariant classification
π₀ = ℤ is PROVED (`windingNumber_eq_iff_joined`); the equivariant refinement is the successor
theorem, and its proof should be the equivariant version of the log-interpolation (interpolating
two σ-equivariant logarithms stays σ-equivariant; the open piece is the existence of an
equivariant continuous log, which is exactly where the ℤ/2 sign obstruction lives).

**The escape unit is two.** At the invariant level the full story of "getting off the line":
a simple on-line zero has sign flip −1 and is pinned; two on-line zeros (flip +1 net) may collide
and re-emit as an off-line mirror pair, conserving both charge (2 = 2) and flip (+1 = +1); an
off-line pair may land back as an even on-line cluster. So sign-invisible defects — even on-line
clusters and off-line mirror pairs — are `[CONJECTURE]` mutually deformation-equivalent (the
escape move), while odd on-line zeros are the pinned residue. **RH₂, the base rung, is exactly
the seam-sign shadow: "escapes happen in pairs" is the parity law, which explains structurally
why parity is the sharp first rung of the ladder.**

## §Deeper resolved [PROVED HERE, paper] — the equivariant h-principle

The KR-shadow conjecture above is settled affirmatively, by elementary obstruction theory on
logarithms. For a σ-symmetric boundary circle (center on the line, σ acting by θ ↦ π − θ with
fixed angles ±π/2 = the line crossings) and an equivariant nonvanishing loop γ (γ(π−θ) = conj γ(θ)):

1. **Twist.** Any continuous log L₀ of γ satisfies conj L₀(π−·) = L₀ − 2πik for a constant k ∈ ℤ
   (two logs of one loop differ by a constant integer multiple of 2πi). Re-choosing L₀ shifts k by
   EVEN integers only (admissible adjustments lie in 2πiℤ). So **k mod 2 is an invariant of γ —
   and it equals the anchor sign bit**: an equivariant log (k even, normalizable to 0) forces
   L(π/2) real, i.e. γ(π/2) = exp(real) > 0; γ(π/2) < 0 forces k odd.
2. **Interpolation preserves twist.** If γ₀, γ₁ have equal winding and equal twist parity,
   normalize to equal twist k; then L_t := (1−t)L₀ + tL₁ satisfies conj L_t(π−·) = L_t − 2πik,
   and exp L_t is a σ-equivariant nonvanishing homotopy (exp(−2πik) = 1), a loop at every t by
   the equal-winding increment as in the non-equivariant proof.
3. **Necessity.** Winding is conserved (formal: `windingNumber_of_homotopic`); the anchor sign is
   conserved (formal: `line_sign_conserved` brick).

> **Equivariant classification:** symmetric pairs are symmetrically joined ⟺ winding and
> top-anchor sign agree; π₀(symmetric pair space) ≅ ℤ × ℤ/2, bottom sign determined by
> ε₋ = ε₊·(−1)ⁿ. Model check: γ(θ) = i·r·e^{iθ} (simple on-line zero at the center) has
> (n, ε₊, ε₋) = (1, −1, +1) ✓.

Consequences now THEOREM-level (paper): the escape move is real — sign-invisible defects of equal
charge (even on-line clusters, off-line mirror pairs) are symmetrically deformation-equivalent;
odd on-line defects are pinned (twist −1 sector). RH₂ = "ξ's right-half symmetric windows all sit
in the (0,+) component". Next: formalize equivariant logs + twist (builds on contLog); then the
only remaining open core of this card is the real-zero parity reading (sign flip ⟺ odd L).

## §Euler coupling and the synthesis object

**First bite [PROVED HERE, Lean]:** `xi_chargeFree_beyond_wall` (DirichletShapeCharge.lean) — the
Euler member ξ carries NO deck charge at any level in windows beyond the wall (`re ≥ 1`), while
the η-completion (same shape class, non-multiplicative coefficients) carries charge `−1` at a
point ON the wall. Multiplicativity's first seam coupling: it kills charge wherever it applies.

**Real-anchor pinning [KNOWN, to formalize]:** coefficient positivity of the alternating series
forces `η > 0` on `σ > 0`, hence `ζ < 0` and `archFactor < 0` on the real segment `(0,1)`, hence
`ξ > 0` there: the arithmetic side pins the seam sign bit at the real anchor — the base point of
all sign bookkeeping is `+`, by the Euler/coefficient structure, not by symmetry.

**The synthesis object [CONJECTURE / next construction]: the Real root tower.** Inside the strip
the Euler product acts only through germ continuation (GermExtension / WeldTowerLimit), and the
seam now carries a second invariant, so the tower and the sign data must be transported together:
define the **σ-equivariant (Real) `2^k`-root tower** — roots `g` with `g(1 − conj s) = conj g(s)`
— whose per-window obstruction is exactly the pair (winding mod `2^k`, anchor sign bit) classified
by the equivariant h-principle. `[CONJECTURE]` RH ⟺ the Real tower of ξ extends across the strip;
the equivariant refinement is strictly stronger per window than the plain tower (it also carries
the pinning of odd on-line clusters), and its local obstruction theory is now fully machine-checked
substrate (SeamSignBit, SeamEquivariantTwist, ConnectedSymmetryBarrier). This merges the two
surviving constraint routes of the program — the Kummer tower and the seam sign — into one object.

## §Real tower: local obstruction theory (formalization in flight)

`RealRootTower.lean` (delegated): **the seam obstruction saturates at one bit.** An equivariant
`2^k`-th root of a symmetric boundary loop exists ⟺ `2^k ∣ winding` ∧ anchor sign positive — at
EVERY level the Real tower carries exactly one bit beyond the deck data, because log-branch
adjustments move the reflection twist by even integers only (`2^k·t − 2m = k₀` solvable ⟺ `k₀`
even). Full equivariant tower on the boundary ⟺ winding 0 ∧ sign +. [Found by attack-as-false:
the naive guess "twist mod 2^k is a level-k invariant" is FALSE — only its parity survives branch
adjustment.]

Region-level remark [PROVED-shape, to formalize later]: a σ-invariant region that misses the line
is a mirror pair of components, where equivariant structure is free (define on one component,
reflect to the other); the Real tower is obstructed only where the region meets the seam — the
region-level echo of `rh_iff_seam_blind_windows_chargeless`.

`XiRealAnchorPositive.lean` (delegated): the coefficient side pins the anchor: paired alternating
series positive for σ > 0, eta factor negative on (0,1) ⟹ ζ < 0 there; archFactor negative ⟹
ξ > 0 on the real segment — the base point of seam-sign bookkeeping is +, forced by arithmetic.

## §Dissolution: the sign bit is a hole invariant [PROVED HERE, Lean, axiom-clean]

The §Deeper/§Real-tower claim "the equivariant refinement is strictly stronger per window than
the plain tower" is now CORRECTED and located exactly (attack-as-false on our own program).
`EquivariantRootDissolution.lean`:

* `mirrorRoot_ratio` — on a line-symmetric preconnected open set, a plain `n`-root `g` and its
  Schwarz mirror differ by the constant `ζ = conj(g a)/g a ∈ μ_n`, read at any line anchor.
* `exists_equivariant_root_of_anchor_pos` / `anchor_pos_of_equivariant_root` /
  `exists_equivariant_root_iff_anchor_pos` — equivariant root (`n` even, plain root given) ⟺
  `f(a) > 0`: the obstruction is the square class of `ζ` in `μ_n/μ_n² ≅ ℤ/2`, and the anchor
  sign computes it (the explicit scale is `c = conj(g a)/‖g a‖`, an `n`-th root of unity because
  `‖g a‖ⁿ = f(a)`).
* `exists_equivariant_root_of_odd` — odd `n`: no sign condition; the bit is 2-adic.
* `exists_equivariant_root_iff_orders_dvd` — regional dichotomy on symmetric convex windows:
  equivariant root ⟺ per-zero divisibility ∧ anchor positivity.
* `xi_equivariant_root_iff_orders_dvd`, `xi_equivariant_root_iff_root` — for ξ at the central
  anchor (`ξ(½) > 0`, banked) the sign clause is a THEOREM: **regionally the Real tower of ξ IS
  the plain tower**. The extra bit is a hole-detecting (boundary/annulus) invariant — a region
  sees the divisor, which already forces the line-sign bookkeeping a boundary loop can only sample.
* `rhLadder_xi_equivariant_window_root` — germ coupling, forward: `RH_{2^k}` propagates the far
  germ equivariantly into every admissible symmetric convex window; the only surcharge over the
  plain rung is the UNCONDITIONAL line ledger. The converse is `root_orders_dvd` (window-local
  only): the line ledger is exactly what blocks regional equivariant data from returning the rung.
* `rhLadder_iff_equivariant_offline_root` — **the rung is an off-line equivariant statement**:
  `RH_{2^k}` ⟺ ξ has a Schwarz-equivariant `2^k`-root on `{Re s ≠ ½}` (mirror gluing is free off
  the line; right-half restriction returns the rung).
* Pro level: `exists_equivariant_coherentTower_of_anchor_pos` — the canonical scales satisfy
  `c_{k+1}² = c_k` (forced by the tower's squaring law at the anchor) and `c_0 = 1` at a positive
  anchor, so the sign obstruction does NOT accumulate in the inverse limit on regions;
  `rh_iff_xi_equivariant_coherentTower_offline` — **RH ⟺ ξ carries a Schwarz-equivariant coherent
  ℤ₂-tower off the critical line** (mirror gluing intertwines squaring, `mirrorGlue_sq`).

Complete obstruction map of the Real tower: OFF-LINE = exactly the rung (and, pro-level, exactly
RH); SYMMETRIC REGIONS = plain divisibility + the unconditional line ledger; SYMMETRIC BOUNDARIES
= one extra sign bit, evaluated by the crease ledger (CreaseHolonomy). Consequence: the region
form of "RH ⟺ the Real tower extends across the strip" is dead (on-line zeros obstruct
unconditionally), and its off-line form is the plain ladder verbatim — the Real tower's genuinely
new content relative to the plain ladder lives ONLY in boundary/annular data, where it equals the
unconditional on-line parity ledger.
