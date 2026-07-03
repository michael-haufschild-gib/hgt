# 15 — The Conservation Program: Global Charge Bookkeeping

**Register: SEARCH** (conjectures labelled; the spine is banked Lean, cited by name).
Companion of `14-parity-stratum.md` (the two docs are the two fronts of 00-approach §12).

**Aim.** Convert a rung RH_{2^k} — deck-class triviality at every off-line zero
(`xi_deckClass_eq_one_iff_ladder_dvd`) — into a LEDGER statement: charges are created
nowhere, drained at known anchors, and change only by boundary flux along a measured
family deformation. State the ledger exactly, prove what is provable today, and locate
the residual open core to the line item.

---

## 1. The pencil, pinned (measured input; raw in `computations/`)

With L = L(s, χ), χ the character mod 5 underlying D–H, and c ∈ ℂ:

  f_c := c·L(s, χ) + (1−c)·L(s, χ̄).

- **s-pencil (R3/R3b/R3c):** the real slice c = (1−ik)/2; the FE holds exactly at
  k = κ ≈ 0.28408 (f_{(1−iκ)/2} = f_DH). Measured: the FE fiber is a transversal defect
  MINIMIZER with floor > 0 (floor 2 in window 2; floor 1 at band σ₀ = 0.5025), linear
  plateau width ≈ 4·(σ₀ − 1/2), replicated in two windows and at three bands; the two
  defect populations on the two sides of the fiber are DISJOINT except the banked box 84
  (t ≈ 85.7) — detuning the FE in opposite directions excites different zero families.
- **c-path (R5/R5b/R5c):** c(u) = (1−u)·c_DH + u from D–H (u = 0: FE, no Euler product)
  to pure L(s,χ) (u = 1: Euler product). Measured: two-minimizer geometry (FE = thin
  fiber with floor, Euler = OPEN BASIN with floor 0 — "the moat", width ≈ 0.025 at
  T = 200, shrinking faster than 1/log T at T = 1000); linear flux n ≈ 120(1−u) down to
  u ≈ 0.955, then clustered wall-crossings, then silence; per-zero crossing parameters
  u* banked (Euler-resistance ranking, anti-correlated with FE-pinning).

The program treats these as the *shape* of the dynamics the ledger must account for;
no measured number is consumed as a hypothesis.

## 2. The formal spine (banked, axiom-clean)

- **Conservation.** `deckClass_step` / `deckClass_chain` /
  `deckClass_deformation_invariant` (DeckHomotopy.lean): along any deformation in which
  the two annulus charts of a box stay zero-free (dominated steps ‖f' − f‖ < ‖f‖ on the
  charts), the box charge mod n is CONSTANT — any roots at either end, no argument
  principle. Charge moves only when a zero touches the chart annulus.
- **Additivity.** `deckClass_multi_zero` (DeckMultiZero.lean): the box charge is the sum
  of enclosed multiplicities mod n.
- **Anchors.** `xi_deckClass_far_field` (FarFieldAnchor.lean): boxes right of Re s = 1
  carry zero charge at every rung — the drain every ledger empties into.
  `analyticOrderAt_even_of_reflection` (ReflectionParity.lean): on the FE fiber of any
  family, the fixed point s = 1/2 carries even order at all times — a pinned interior
  datum (holds for every FE-symmetric member; off the fiber it is vacuous).
- **Blindness constraint.** The symmetry discount (14 §2): symmetric-region ledgers are
  ≡ 0 mod 4 identically; all books below are kept per upper-quadrant box.

## 3. The ledger identity

For a box B (upper quadrant, annulus charts on ∂B) and a path (f_u) in the family:

> (L)  charge_k(B, f_1) − charge_k(B, f_0) ≡ [signed multiplicity flux of zeros
>       through the chart annulus along the path]  (mod 2^k).

**Status.** The no-flux case of (L) is `deckClass_deformation_invariant` — banked. The
jump case is a concrete near-term Lean target [carded below as `deckClass_jump`]: when
the enclosed configuration changes by one zero of multiplicity m, the two classes differ
by exp(2πi·m/2^k) — provable by evaluating `deckClass_multi_zero` at both ends and
taking the ratio; no new analysis. With both, (L) is a theorem for piecewise-generic
paths (finitely many transversal crossings), which is the only regime the program uses.

**Interior events are free.** A collision/annihilation of two zeros inside B (the R3
measured events) changes the enclosed count by ±2m', leaving the mod-2 ledger unchanged
— and annihilation REQUIRES matching charges, which is precisely the parity front's
input (14 §4.4). Consequence: **at k = 1 the entire burden of (L) is boundary flux.**
Nothing that happens inside a box can ever change its mod-2 books.

## 4. The program (coupled reduction) `[CONJECTURE → proof-sketch]`

Fix k = 1 (the base stratum; higher rungs iterate). Suppose ζ (or an FE member under
study) has a simple off-line zero in an upper-quadrant box B. Run the family from an
anchored end (charge 0) to the target member. By (L):

  1 ≡ charge₁(B, target) ≡ [mod-2 flux through ∂B along the path].

So the rung follows from: **(P-flux) the total mod-2 flux through every upper-quadrant
box boundary, along an FE-compatible path from an anchored end, is even.** The program's
central object is this crossing-parity functional, and the residual open core is its
control, itemized:

- **(OC1) Band-edge crossings (σ = σ₀ wall).** The measured dominant channel (linear
  flux law). What is needed is not a count but a PAIRING: an exact mechanism matching
  wall-crossings in pairs. [CONJECTURE] the R3c two-population asymmetry (disjoint
  defect families on the two sides of the FE fiber) is the shadow of an orientation /
  two-coloring of crossings — a transversality structure on the FE-constrained family
  that pairs entries with exits. This is the program's principal open mathematics.
- **(OC2) Seam crossings (critical line).** Zeros crossing into the line absorb charge
  into the RH-invisible locus. The accounting instrument is the seam cocycle (#122):
  reflection gluing at the slit boundary in the u-plane, where the positivity
  instruments retargeted by 14 §4.3 natively live.
- **(OC3) The anchor below σ = 1.** Conservation cannot manufacture nonvanishing: the
  anchored end is provably clean only in the far field (Re s > 1, banked). Three
  honest options: (a) tall boxes reaching into the far field — anchor free, burden
  moved entirely to lateral/seam flux (OC1/OC2); (b) numerically certified endpoint
  windows (winding certificates at the Euler end — legitimate for finite-height,
  per-window rungs; this is what the measured moat licenses); (c) the u-plane form
  (UPlaneDescent): regions on the slit plane with the far-field anchor on the positive
  real end.

**Honesty clause.** (P-flux) at full strength is RH-grade by Bagchi-consistency — the
program does not shrink the burden, it RESHAPES it: from a magnitude estimate at a
hypothetical zero to the parity of a crossing count along a family, with conservation,
additivity, anchors, and interior dynamics all discharged by machine-checked lemmas.
The wager (00-approach §12) is that parity-of-flux is differently-shaped hard: it has
discrete structure (pairing, orientation, two-coloring) that magnitude bounds lack.

## 5. Relation to the index-formula arc (07)

07's (H_k) ⟹ (R_k) Rouché transfer is the t-translation instance of (L): translation in
t is a deformation, box charges transport, and defect recurrence is charge recurrence.
The family ledger strictly generalizes it: 07 moved boxes at fixed member; (L) moves the
member at fixed box. The R6 negative (data non-recurrence at 24× margin while defects
recur) is consistent: (L) never claims boundary DATA recurs — only the ℤ/2^k class.

## 6. Next moves (carded)

1. **`deckClass_jump`** (Lean, cheap): one-zero boundary crossing jumps the class by
   exp(2πi·m/n) — ratio of two `deckClass_multi_zero` evaluations. Completes (L).
2. **(OC1) attack:** formulate the two-coloring conjecture precisely on the pencil
   (crossing orientation = side of the FE fiber exciting the zero's population, per
   R3c); attack-as-false with the banked box-84 exception (the one two-sided zero) as
   the designated counterexample candidate.
3. **#122 seam cocycle** for (OC2) — u-plane slit ledger.
4. **u-plane ladder** (root existence on the star-convex slit plane) — makes (b)/(c)
   anchoring statements global instead of per-box.
