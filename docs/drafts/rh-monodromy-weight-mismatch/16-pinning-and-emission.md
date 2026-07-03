# 16 — Pinning, Emission Ports, and the Two-Coloring Theorem

**Register: SEARCH**, with two paper-proved statements (§1, §3–4) awaiting promotion
checks, and OC1-proper located in §5. This document re-cuts OC1 of
`15-conservation-program.md` §4: what was a conjecture about crossing-pairing becomes,
on the model family, a theorem — and the two measured anomalies of R3c (disjoint
populations, the box-84 exception) are DERIVED, not just observed.

Throughout: "the line" = Re s = 1/2; FE = self-functional-equation f(1−s) = f(s) (up
to a nonvanishing scalar — zeros are all that matter); reality = f(s̄) = conj f(s).

---

## 1. The pinning lemma `[PROVED HERE — paper]`

**Lemma (pinning).** Let (f_c) be a family, analytic in s, continuous in c, with each
member satisfying FE ∧ reality. Suppose f_{c₀} has a SIMPLE zero at ρ₀ = 1/2 + iγ₀ on
the line. Then for c near c₀ the unique nearby zero ρ(c) stays ON the line.

*Proof.* Simplicity gives ε > 0 with ρ₀ the unique zero in the closed ball B̄(ρ₀, ε)
and, for c near c₀, a unique simple zero ρ(c) ∈ B(ρ₀, ε) depending continuously on c
(standard local zero theory / Hurwitz). FE ∧ reality compose to the anti-holomorphic
reflection across the line: f_c(1 − s̄) = conj f_c(s), so 1 − conj ρ(c) is also a zero
of f_c; it lies in B(ρ₀, ε) because ρ₀ is fixed by the reflection and the reflection
is an isometry. Uniqueness forces ρ(c) = 1 − conj ρ(c), i.e. Re ρ(c) = 1/2. ∎

**Reading.** FE ∧ reality PIN simple on-line zeros. The constraint pair does not
merely place zeros symmetrically — it freezes the simple on-line population against
any FE-preserving deformation. (For odd multiplicity ≥ 3 the argument gives only that
the multiset of emerging zeros is reflection-symmetric; a symmetric splitting can
leave one zero on the line and push pairs off.)

## 2. Emission ports (the ledger consequence)

**Corollary.** Along an FE ∧ real family, off-line charge in a region away from the
region's boundary can be CREATED only at parameters where some on-line zero has
multiplicity ≥ 2 (an "emission port"). A simple on-line zero is pinned (§1); an
off-line zero moves continuously (no creation); reality forbids a single zero leaving
the line alone (its conjugate must follow), and FE ∧ reality forbid even a pair
leaving from a simple point.

For the conservation ledger of doc 15 this closes the classification of mod-2 charge
events for FE-compatible paths:

> interior collisions — free (mod 2);  boundary flux — `deckClass_jump`;
> seam events — ONLY at on-line multiple points, quantized by the seam cocycle
> (`SeamCocycle.lean`: a port of multiplicity m jumps the seam class by e(m/n)).

So **(P-flux) for FE ∧ real families = parity control of emission-port events plus
lateral flux.** The k = 1 rung along such a family is exactly: no odd number of
emission events per upper-quadrant box.

## 3. The mirror identity of the two-character family `[PROVED HERE — paper]`

Let χ be the D–H character mod 5, Λ(s,χ) the completed L-function,
Λ(s,χ) = ε·Λ(1−s,χ̄) with |ε| = 1 the classical FE. Consider the two-parameter family

  G_{c,d}(s) := c·Λ(s,χ) + d·Λ(s,χ̄).

Substituting the FE of both characters:

  G_{c,d}(1−s) = (d·ε)·Λ(s,χ) + (c·ε̄)·Λ(s,χ̄) = G_{dε, cε̄}(s).

**Identity (mirror).** The reflection s ↦ 1−s maps the zero set of G_{c,d} to the zero
set of G_{dε, cε̄}: reflection across the line is the parameter involution
(c,d) ↦ (dε, cε̄). On the ratio coordinate r = c/d (zeros depend only on r), the
involution is the holomorphic map r ↦ ε²/r, whose fixed points are r = ±ε.

The R3 k-pencil is the unit circle r(k) = (1−ik)/(1+ik); D–H sits at the fixed point
r(κ) = ε. The involution restricted to the circle is the reflection of the circle
fixing ±ε; in the k-coordinate:

  k' = tan(2·arctan κ − arctan k)   (a real Möbius involution fixing κ; k' ≈ 2κ − k).

Composing with reality (zeros of each member are conjugation-symmetric), for a zero
trajectory ρ_j(k) passing through an on-line SIMPLE point at k = κ (local uniqueness
at κ identifies the trajectory with its mirror — see §7 for why this hypothesis is
necessary):

  **ρ_j(k') = 1 − conj ρ_j(k),  i.e.  β_j(k') − 1/2 = −(β_j(k) − 1/2) exactly.**

The displacement of every unpinned zero from the critical line is exactly ODD across
the FE fiber (in the Möbius coordinate). `[VERIFIED to 30 digits — §7 / R9-RESULTS;
the ε-algebra and FE normalization are measurement-backed.]`

## 4. The two-coloring theorem, and box 84 explained

**Theorem (two-coloring of unpinning).** Let ρ_j(k) be the trajectory of a simple
on-line zero of the k-pencil at κ, with unpinning velocity v_j := d(Re ρ_j)/dk|_{κ}
(defined by local zero theory; finite). If v_j ≠ 0, then for small detuning the zero
is right-defective (β > σ₀ > 1/2) on exactly ONE side of κ — the side where
v_j·(k − κ) > 0 — and by §3 its displacement on the other side is the exact mirror
(left of the line, invisible to right-band boxes).

*Proof.* Immediate from §3's odd displacement plus continuity: β_j(k) − 1/2 changes
sign at κ along the Möbius-symmetrized coordinate; a right-band box (σ > σ₀) sees the
zero only where the displacement is positive and exceeds σ₀ − 1/2. ∎

**Consequences, against the R3/R3c measurements:**
- **Disjoint populations DERIVED.** The two defect populations on the two sides of the
  FE fiber (measured disjoint in R3c) are the sign classes {v_j > 0}, {v_j < 0}. The
  measured "defect velocity dσ/dk ≈ 0.2–0.35" is |v_j|.
- **Box 84 DERIVED.** The single both-sided box is the box containing the CERTIFIED
  pre-existing off-line zero (t ≈ 85.699, banked to 18 digits): an already-off-line
  zero is not subject to pinning or to the sign dichotomy — it moves smoothly and
  stays deep in the band for small detuning, so its box defects on BOTH sides. The
  "designated counterexample" of doc 15 §6 is thereby resolved: box 84 does not
  refute the two-coloring; it is the unique box whose defect is not an unpinning
  event at all.
- **Plateau centering.** The exact mirror symmetry is between right-defects at k and
  LEFT-defects at k'; it does not by itself force n(k) = n(k'). The measured
  approximate centering of the plateau at κ is the statistical statement that the two
  sign classes have comparable sizes (16 vs 11 boxes in R3c — comparable, not equal).

No computation was run for this section: the two R3c anomalies are retro-dicted by
the theorems above, and running the pod to re-confirm them would be theatre. The one
genuinely open measurable is the v_j = 0 degenerate class (second-order unpinning);
nothing in the current data requires it to be nonempty.

## 5. OC1 proper, relocated

What remains open for the conservation program is exactly this, now sharply bounded:

> **(OC1′) Emission parity at Euler-type endpoints.** For families FE ∧ real along the
> whole path with the target member carrying the exact Euler structure, emission
> ports (on-line multiple points) either do not occur or occur with even multiplicity
> per upper-quadrant box.

Honesty clauses. (i) This is the de Bruijn–Newman SHAPE (zeros leaving the line under
deformation), and at ζ-strength it is RH-grade — Bagchi-consistency is not evaded,
only reshaped: the burden is now the parity of a discrete event count, guarded by two
proved structures (pinning; quantized seam jumps) instead of magnitude estimates.
(ii) The pinning lemma protects only SIMPLE on-line zeros: (OC1′) interacts with the
simplicity of on-line zeros (GSH-flavored), and any proof must either control
multiple on-line points directly or show the family avoids them — attack both as
false first. (iii) The D–H pencil does NOT satisfy (OC1′)'s hypotheses (FE fails off
the fiber) — consistently, since detuning is exactly how its off-line population is
excited (§4): the model family shows the MECHANISM (unpinning by FE-breaking), and
(OC1′) asks whether the FE-preserving directions are emission-free at Euler points.

## 6. Formalization targets

1. **Mirror identity** — algebraic; needs mathlib's completed Dirichlet L functional
   equation for χ mod 5 (probe `DirichletCharacter` completed-FE names) plus the
   two-line parameter computation. Cheap once the FE name is pinned.
2. **Pinning lemma** — needs local zero UNIQUENESS under perturbation, i.e. a counting
   statement mathlib lacks (no Rouché). Two Rouché-free routes: (a) the tree's
   `PerturbationZero` (existence) plus an order argument; (b) `[CONJECTURE — route]`
   the LARGE-n DECK-CLASS COUNTING TRICK: the ledger (L) at level n exceeding any a
   priori bound on the enclosed count pins the exact count, because a count `< n` is
   determined by its residue mod n — `deckClass_multi_zero` + `deckClass_jump` as a
   full Rouché substitute. If (b) works it removes the shared mathlib gap for ALL
   counting arguments in this lane and the q62 lane.
3. **Emission-port corollary** — follows formally from 1–2 plus the banked seam
   cocycle; no new analysis expected.

---

## 7. Verification record (R9, 2026-07-03) — §3 CONFIRMED, §4 sharpened

The mirror identity was put to a pre-registered numerical test (R9-RESULTS.md in
`computations/`; scripts archived in `computations/mwm/`). Outcome:

- **§3 CONFIRMED to 30 digits.** The pencil is LINEAR in (c,d), so the unique member
  vanishing at any point is exact algebra: the INCIDENCE MAP r(s₀) = −L(s₀,χ̄)/L(s₀,χ).
  At the reflected points 1−ρ(k₁), 1−conj ρ(k₁) of the certified box-84 zero continued
  to k₁ = κ + 0.03, the required member is |r| = 1 (to 3e-29) with k equal to the
  Möbius prediction k' = tan(2·arctan κ − arctan k₁) to 8.5e-30. The κ closed form
  (√(10−2√5) − 2)/(√5 − 1) is verified against the certified zero (residual 3.5e-17).
- **§4 proof sharpened.** The trajectory identity ρ_j(k') = 1 − conj ρ_j(k) holds for
  zeros passing through an on-line SIMPLE point at κ (where local uniqueness applies)
  — exactly the two-coloring's population. Pre-existing off-line zeros are NOT subject
  to it: their mirror images are SEPARATE zeros in the left half-strip (measured:
  f_{k'} carries both the continued trajectory zero at β = 0.794 and the mirror
  partner at β = 0.176 near t ≈ 85.7). Box 84's measured velocity: dβ/dk ≈ 0.50.
- **Method note.** The initial Muller run from the correct seed converged to the wrong
  zero — a reminder that root-finder failure is not refutation; the exact linear-pencil
  incidence solve is the robust instrument.

**Opened (the next object):** the incidence map r(s) = −L(s,χ̄)/L(s,χ) packages the
ENTIRE family dynamics as the level-set geometry of one meromorphic function — zeros
of f_k are the level curve r = r(k); the FE fiber and the mirror involution are its
symmetries; unpinning velocities v_j are its boundary derivatives on the critical
line; the Euler moat is the geometry of its exceptional level r = 0/∞. The measured
R3/R5/R5b laws are value-distribution statements about r. This is the natural carrier
for (OC1′)'s two-coloring beyond the model family, and a candidate meeting point with
the u-plane calculus (compose r with the descent).
