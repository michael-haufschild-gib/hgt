# No finite Müntz system inverts ζ, so no finite section is dense

Status: formalized (Lean, unconditional)
Date: 2026-08-09

## The result

`RHTower/MuentzZetaRelationImpossible.lean`:

> **`bdDist_pos_of_injective_of_lt_one` — every finite family of distinct dilations `θᵢ ∈ (0,1)` has strictly
> positive Báez-Duarte distance.**

Unconditional, and with no arithmetic input at all. The corpus previously knew this only for special
families: `bdDistDiscrete_pos` (factorial floor, for `θ = 1/(n+1)`) and `bdDist_single_ge` (one generator).
This is the structural reason behind both, and it holds for arbitrary finite families.

## The reusable interface

The route is now factored so that a family other than Báez-Duarte's inherits it by proving one hypothesis:

* **`exists_detectorCombination_floor_of_linearIndependent_pairings`** (in `BorderDeterminantVanishing`) —
  the law for an *arbitrary* family in the carrier: if the Mellin detectors pair with a finite family `G` and a
  target `x` through linearly independent functions on the strip, then there are sample points `y` in the strip
  and coefficients `a` whose detector combination annihilates `G`, pairs with `x` at exactly `1`, and certifies
  two floors for `dist(x, span G)` — the sharp `1/‖w‖` and the elementary
  `1 / ∑ⱼ ‖aⱼ‖/√(2 Re yⱼ − 1)`, which mentions only the coefficients and the real parts of the sample points.
  `exists_detector_floor_of_linearIndependent_pairings` and `infDist_pos_of_linearIndependent_pairings` are the
  weaker forms;
* `bdDist_pos_of_linearIndependent_borderRowFun` — the Báez-Duarte instance, supplying the two pairing
  identities `inner_bdDetector_bdGen` and `inner_bdDetector_bdTarget`;
* `muentz_relation_of_not_linearIndependent` — the converse computation, isolated from the determinant
  hypothesis: a dependence among the pairing functions *is* a Müntz relation inverting `ζ` on the strip;
* `linearIndependent_borderRowFun_of_injective` — the Báez-Duarte instance of that hypothesis, proved by the
  refutation below, so `bdDist_pos_of_injective_of_lt_one` is now a two-line consequence.

So the analytic content lives entirely in the independence of the pairing functions; everything above it is
linear algebra, and it no longer mentions the Báez-Duarte generators at all — only the carrier and its Mellin
detectors. A new family supplies its own pairing functions plus one independence proof.

## The chain

Four cards assemble into it, each supplying one link:

1. `detector-duality-is-exact.md` — the distance *is* the best annihilator pairing, so a floor means
   exhibiting a detector;
2. `finite-section-zeta-interpolation-dichotomy.md` — with more sample points than generators, annihilating
   the section is free (rank), so the only escape is interpolating `ζ` at the sample points; a nonvanishing
   bordered determinant of sampled `ζ` values certifies a floor;
3. `sampling-detects-independence.md` — a determinant vanishing at *every* sample makes the row functions
   linearly dependent, which collapses "for each sample there are coefficients" to one fixed relation
   `(∑ᵢ cᵢ(θᵢ^s − θᵢ))·ζ(s) = c_N` on the whole strip;
4. this card — that relation is impossible.

## Why the last step is elementary

* `eq_zero_of_forall_sum_cpow_eq` — the concrete form of Dedekind's independence of characters: if
  `∑ᵢ bᵢ·θᵢ^s = K` for **all** `s` with the `θᵢ` distinct, positive and `≠ 1`, then every `bᵢ` and `K`
  vanish. Built from `linearIndependent_monoidHom` through the corpus's own `logCpowChar`, with the constant
  term carried by the extra character `θ = 1` in an `Option` index — the pattern already used inside
  `BurnolCoPoissonSubWindowIndependence`, here extracted as a standalone law;
* `muentzSum`, `muentzSum_eq_cpow`, `differentiable_muentzSum` — the combination written with `exp` so that
  entirety is automatic, and identified with the `cpow` form;
* **`eq_zero_of_muentz_zeta_relation`** — the refutation:
  1. `P·ζ − c_N` is analytic on the **convex** half-plane `Re s < 1` (no pole there) and vanishes near
     `3/4`, hence on the whole half-plane (identity theorem, `convex_halfSpace_re_lt`);
  2. the trivial zero `ζ(−2) = 0` (`riemannZeta_neg_two_mul_nat_add_one`) forces `c_N = 0`;
  3. `ζ(3/4) ≠ 0` (the corpus's `riemannZeta_ne_zero_of_ofReal_mem_Ioo`) makes `ζ` nonvanishing near `3/4`,
     so `P ≡ 0` there and — `P` being entire — everywhere;
  4. character independence gives `c = 0`.

Note what the proof avoids: no zero of `ζ` in the critical strip is needed, no zero-free region, no
information about RH. The only value of `ζ` used off the real segment is a *trivial* zero, and the only
nonvanishing used is on `(0,1)` where it is classical. Staying inside the convex half-plane `Re s < 1` avoids
the pole at `1` entirely, so the identity theorem needs only convexity.

All six declarations are `#print axioms`-clean.

## What it does and does not say

It says: for a *fixed* finite section the distance is positive, so `d_N → 0` can only happen in the limit —
consistent with, and required by, the Nyman–Beurling criterion. It gives no rate: the constant it produces is
not explicit, since it comes from a determinant obtained by contradiction rather than from a chosen sample.

The quantitative side is now packaged rather than open-coded: the obstruction law itself hands back sample
points `y`, coefficients `a` solving the sampled system, and the floor
`1 / ∑ⱼ ‖aⱼ‖/√(2 Re yⱼ − 1)`. Every ingredient of that expression is elementary; what remains is choosing the
sample so the bound is large, which is an estimate of a quantity already known to be positive.

## Both restrictions removed

`RHTower/FiniteFamilyObstruction.lean` drops the distinctness and the `θ < 1` hypotheses, which were
cosmetic — repetitions give the same generator and `θ = 1` gives the zero vector:

* `bdGenFun_one`, `bdGen_one` — `{u} − 1·{u} = 0`, so `bdGen 1 = 0` in the carrier;
* `bdDist_mono_span` — the span form of `bdDist_mono`, which is what a comparison of *spans* (rather than of
  generator sets) needs;
* **`bdDist_pos_of_finite` — every finite family of dilations in `(0,1]` has positive Báez-Duarte
  distance**, with no injectivity hypothesis and no exclusion of `1`. Passing to the distinct values below
  `1` (`Finset.image θ univ |>.erase 1`, enumerated by `Finset.equivFin`) leaves the span unchanged;
* `bdDistFinset_pos` — hence every finite section of an arbitrary family is obstructed.

This subsumes `bdDistDiscrete_pos`: the discrete family `bdDiscrete n = 1/(n+1)` starts at `θ = 1`, which the
structural theorem excludes but `bdDist_pos_of_finite` handles, so the factorial floor of
`DistancePositivity` is no longer the only route to positivity — and the general statement holds for families
the factorial argument says nothing about.
