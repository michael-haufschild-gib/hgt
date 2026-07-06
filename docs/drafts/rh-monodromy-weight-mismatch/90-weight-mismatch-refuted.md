# 90 — Attack-as-false: the weight-mismatch parity invariant is REFUTED

Doc 89 named the moonshot (route b): a ℤ₂ **parity** of the zero-quadruple
`Q(ρ) = {ρ, 1−ρ, ρ̄, 1−ρ̄}` that is even iff `Re ρ = ½`, with the two symmetries acting as a 4-cycle
(odd) off-line vs a 2-cycle (even) on-line. Per the mandate — attack your best conjecture as false
first — I did. **It is false.** The refutation is now a Lean theorem
(`WeightMismatchRefutation.lean`, axiom-clean).

## What actually happens (the computation)

The two involutions on `Q`:
- functional equation `σ_FE : s ↦ 1−s` acts as `(ρ, 1−ρ)(ρ̄, 1−ρ̄)` — **two transpositions, EVEN**;
- Schwarz `σ_S : s ↦ s̄` acts as `(ρ, ρ̄)(1−ρ, 1−ρ̄)` — **two transpositions, EVEN**;
- their composite `σ_FE∘σ_S = (ρ, 1−ρ̄)(1−ρ, ρ̄)` — **EVEN**.

They generate the **Klein four-group `V₄ ⊂ A₄`** — every element even. There is **no 4-cycle**, on the
line or off it. The doc-89 mechanism was simply wrong about the permutation type.

The weight version is equally dead. By the functional equation and Schwarz reflection all four points
carry **equal** ξ-order (`xi_orderAt_quadruple_eq`: `ord(1−ρ)=ord(ρ̄)=ord(1−ρ̄)=ord(ρ)`), so the total
tower weight over the quadruple is `4·ord(ρ)` — **ℤ₂-trivial (even) for every `ρ`**, whether on or off
the critical line (`quadruple_weight_parity_refuted`). The conjectured biconditional fails in the
off-line direction: off-line zeros give parity `0` too. **A constant invariant carries no information.**

## Why the parity route was doomed, structurally

The real on-line/off-line distinction is not a parity but **τ-fixedness**: the antiholomorphic
involution `τ = lineReflect : s ↦ 1 − s̄` (= `σ_FE∘σ_S`) has fixed locus exactly the critical line
(`lineReflect_fixed_iff`: `τ(ρ)=ρ ↔ Re ρ = ½`). RH ⟺ every ξ-zero is τ-fixed. But "τ-fixed" is a
property of a *single point*, not a mod-2 invariant of its *orbit* — the orbit is `V₄`-even in both
cases; only its **size** changes (4 distinct off-line, 2 on-line, both even). No orbit-level ℤ₂
functional can separate size-2 from size-4 orbits by parity. The parity idea was structurally
incapable of the job.

## The redirect (forward, not a tombstone)

The refutation kills the *parity* framing and sharpens what a real mechanism must look like:

1. **The object is right, the invariant was wrong.** The τ-invariant ξ-divisor decomposes as
   (real part on the fixed locus) + (off-line `V₄`-quadruples). RH = *no off-line quadruples*. This is
   a genuine, clean reformulation (τ-invariant divisor, real iff RH) — but it does **not self-force**:
   nothing internal to the quadruple forbids it. The force must be **external**.

2. **Reconnect to the ladder as the forcing mechanism, dropping parity.** The lane's `RH_{2^k}` ladder +
   defect-recurrence was always the intended *force*; doc 89 mistakenly tried to route it through orbit
   parity. The correct target: does the ladder's recurrence bound the **count** of off-line quadruples
   below the height `T` (a *quantitative* obstruction, e.g. `#{off-line quadruples ≤ T} = o(#zeros ≤ T)`
   forced by a defect-decay), rather than a *parity* of a single one? That is a density/counting force,
   not a mod-2 one — and it composes with the step-4 proportion lane (`|D|` large a.e.-height →
   zero-density) rather than the dead parity.

3. **If a discrete invariant is wanted, it must be an equivariant *index*, not a parity.** `τ` is
   orientation-reversing; the right discrete gadget is a *signed* fixed-point/index quantity of `τ`
   acting on the divisor, whose vanishing would force all zeros onto the fixed curve. Whether such an
   index is forced (rather than merely equal to the off-line count, which is RH) is the honest open
   question — and the only version of "route b" not yet refuted.

**Net:** route (b)-as-parity is closed (Lean-refuted). Route (b) survives only as (2) the ladder-as-
counting-force or (3) a genuine equivariant index — both of which drop the mod-2 framing entirely. The
next construction is (2): make the defect-recurrence bound the off-line quadruple count, and collide it
with the step-4 density lane.

## Postscript — the refutation's shadow IS the real open core (RHLadder)

Chasing where the parity idea came from led to the actual frontier. The tree already reduces RH to a
**mod-`2^{k+1}` tower** — `RHLadder k`: *every right-half ξ-zero has vanishing order divisible by `2^k`*
(`RiemannTower.RHLadder`, `rh_iff_forall_ladder : RH ↔ ∀ k, RHLadder k`). My mod-2 "parity" was exactly
its trivial `k ≤ 1` shadow — the level where `2m` is automatically divisible. The non-trivial content is
the whole tower.

Now formalized (`WeightMismatchRefutation.lean`, axiom-clean):
- `not_rhLadder_of_rightHalf_zero` — a right-half ξ-zero of order `m ≥ 1` **breaks** `RHLadder k` for
  every `k` with `2^k > m` (the ladder demands `2^k ∣ m`, impossible for `0 < m < 2^k`).
- `not_forall_rhLadder_of_rightHalf_zero` — hence a single off-line zero collapses the whole tower
  `∀ k, RHLadder k`.

So the honest "weight" is not a parity but the **2-adic valuation `v₂(ord ρ)`** of the zero order: RH ⟺
`v₂` is forced to `∞` (order `0`) at every right-half point ⟺ `RHLadder k` for all `k`. The parity
refutation is not a dead end — it correctly located the open core: **prove `RHLadder k`** (equivalently:
ξ admits an analytic `2^k`-th root on `Re s > ½`, `rhLadder_iff_root`). That is the exact target of the
whole Spur/ladder apparatus, and it is where the real research sits — not in any mod-2 invariant.
