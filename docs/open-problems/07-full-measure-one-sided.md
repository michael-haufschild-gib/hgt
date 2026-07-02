# Open Problem 7: Do strictly one-sided points carry full harmonic measure on a quadratic Julia set?

**Field:** complex dynamics / geometric function theory (harmonic measure).
**Self-contained:** everything needed is defined below; classical results from the
literature may be used freely with citation. **The request:** prove or refute the Problem
as stated and provide a complete rigorous proof.

## Setting

For a parameter `c ∈ ℂ` let

- `f_c(z) = z² + c`,
- `K_c = { z ∈ ℂ : the orbit z, f_c(z), f_c(f_c(z)), … stays bounded }` — the **filled
  Julia set**, compact with connected complement (a *full* compact set),
- `J_c = ∂K_c` — the **Julia set**.

Take `c` in the Mandelbrot set `M`, so `K_c` is connected. Let `μ_c` denote the
**harmonic measure** of the domain `ℂ̂ ∖ K_c` evaluated at `∞` — equivalently the
equilibrium measure of `K_c` (which has logarithmic capacity `1`), equivalently the
Brolin measure of maximal entropy of `f_c`. It is a Borel probability measure with
support exactly `J_c`, non-atomic, ergodic and invariant under `f_c`.

**Strictly one-sided points.** Call `p ∈ J_c` **strictly one-sided** if

> there is `ρ₀ > 0` such that for every `0 < ρ ≤ ρ₀` the set `B(p, ρ) ∖ K_c` is
> connected

— a single local access to the exterior, in the strong ball-connectivity sense. Write

- `S_c = { p ∈ J_c : p is strictly one-sided }`.

## The Problem

> **Prove or refute: for every `c ∈ M ∖ {0, −2}`,**
>
> `μ_c(S_c) = 1`.
>
> (If `S_c` fails to be `μ_c`-measurable, read the statement as: the complement
> `J_c ∖ S_c` is contained in a Borel set of `μ_c`-measure zero.)

An equivalent form (immediate pigeonhole): **every Borel `E ⊆ J_c` with `μ_c(E) > 0`
contains a strictly one-sided point.**

### Acceptable weakenings (any one is a complete solution)

- **(W1) The special-set form.** Fix `c₁ ≠ c₂ ∈ M ∖ {0, −2}`, set `X = K_{c₁} ∪ K_{c₂}`,
  let `W` be the unbounded component of `ℂ ∖ X`, and (after exchanging indices if
  necessary) consider the exposed set `E = ∂W ∖ K_{c₂}`, a nonempty subset of `J_{c₁}`.
  The following may be used without proof (it is established): `μ_{c₁}(E) > 0`. Show
  `E ∩ S_{c₁} ≠ ∅` — i.e. the specific exposed set, not an arbitrary positive-measure
  set, contains a strictly one-sided point.
- **(W2)** The full-measure statement for all `c` in an explicitly described subclass of
  `M ∖ {0, −2}` (e.g. real parameters, or parameters with locally connected `J_c`,
  together with the statement of what is used about the subclass).
- **(W3)** A refutation: a parameter `c ∈ M ∖ {0, −2}` with `μ_c(S_c) < 1`, ideally with
  a characterization of `μ_c(S_c)` — noting whether the failure can also occur for the
  special sets in (W1).

## Known facts that may be used without proof

1. Each `K_c` (`c ∈ M`) is compact, full, connected, contained in the closed ball of
   radius `2`, of capacity `1`, with Green's function `G_c` continuous on `ℂ`, vanishing
   exactly on `K_c`, and `G_c(f_c(z)) = 2·G_c(z)`.
2. `μ_c` is non-atomic with support `J_c`; `f_c`-invariant, ergodic, entropy `log 2`.
3. **Density is known and insufficient.** The β-fixed point of `f_c` (landing point of
   the external ray of angle `0`) is strictly one-sided for `c ∈ M ∖ {0, −2}`, and so is
   every iterated `f_c`-preimage of it along orbits avoiding the critical point; these
   points are dense in `J_c`. But this set is countable (at most `2ⁿ` preimages at level
   `n`), so by non-atomicity it has `μ_c`-measure `0`. Density therefore cannot meet a
   general positive-measure set — nor the special set in (W1), which need not be
   relatively open in `J_{c₁}`.
4. **A.e. uniaccessibility is known and insufficient.** For `μ_c`-a.e. `p ∈ J_c` exactly
   one external ray lands at `p` (Fatou–Lindelöf-type accessibility refined by
   Zdunik-type a.e. theorems; cite the version used). CAUTION: uniaccessibility does
   NOT imply strict one-sidedness. A topologist's comb has a uniquely accessible tip
   `p` for which `B(p,ρ) ∖ K` has infinitely many components at every scale `ρ` —
   accumulation without access. Conflating the two notions is the known-invalid step
   this problem replaces; a valid proof must control complementary components of small
   balls, not merely count landing rays.
5. No Jordan arc separates the plane. Consequently a *single* spiraling access does not
   by itself destroy ball-connectivity; only comb-like accumulation of complementary
   components can. (So a refutation needs positive measure of comb-type points, and a
   proof needs to exclude them a.e.)
6. Harmonic-measure boundary theory for simply connected domains (McMillan's twist/cone
   dichotomy, Makarov's theory) and its Julia-set refinements
   (Przytycki–Urbański–Zdunik; Zdunik's dichotomy: `μ_c` is singular with respect to
   Hausdorff-1 measure unless `J_c` is a circle or segment), with citation.
7. Anything from the standard literature on polynomial dynamics, plane topology, and
   potential theory (Douady–Hubbard, Milnor, prime ends, extremal length,
   Janiszewski-type separation), with citation.

## Calibration: the excluded parameters show the statement has real content

- `c = −2` (`K_c = [−2,2]`): every interior point of the segment is two-sided (a small
  ball is cut into two half-disks), and only the endpoints `±2` are strictly one-sided,
  so `μ_{−2}(S_{−2}) = 0`. The full-measure statement is FALSE for a segment — so no
  soft/general argument can prove the Problem; the non-smoothness of `J_c` for
  `c ∉ {0, −2}` must be used.
- `c = 0` (`K_c` = closed unit disk): here `B(p,ρ) ∖ K_c` is a single lune for every
  boundary point, so `S_0 = J_0` and the statement holds trivially — but `c = 0` is
  excluded upstream for unrelated reasons.
- These two are exactly the parameters with smooth Julia sets, i.e. exactly the
  exceptions in Zdunik's dichotomy (fact 6). Whether the same dichotomy governs
  `μ_c(S_c) = 1` is the heart of the Problem.

## What it unlocks

The companion two-parameter analysis (Problem 6 of this series) already established the
potential-theoretic half: for distinct `c₁ ≠ c₂ ∈ M ∖ {0, −2}`, after a swap the exposed
set `E = ∂W ∖ K_{c₂}` is nonempty with `μ_{c₁}(E) > 0`. A positive answer here (full form
or (W1)) then yields by pigeonhole a strictly one-sided point of `J_{c₁}`, off `K_{c₂}`,
on `∂W` — the final open analytic input of the both-connected case of a machine-checked
algebraic-independence theorem for Böttcher coordinates (every downstream reduction is
already formalized in Lean 4, axiom-clean). A refutation (W3) that also kills (W1) would
redirect the programme to its measure-quantified variant, so the answer is decisive
either way.

## Deliverable

A rigorous, self-contained proof or refutation (modulo cited literature), written so
that each step can be checked and, eventually, formalized.
