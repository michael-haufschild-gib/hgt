# Lindelöf campaign — successor summary

The working log (`lindelof-hypothesis-campaign.md`) is ~97 cycles and 160+ numbered findings. This
file is the short version: what stands, what was withdrawn, and where the frontier is.

**Bottom line: LH is neither proved nor disproved. `μ(1/2) ≤ 13/84` (Bourgain 2017) stands.**

---

## 1. Read this first

**Twenty-three errata (E1–E23) and fifty-one dead routes (D1–D51) are recorded in the log.** They are
the most reusable output: each marks a route that looks promising and is not, with the check that
killed it. **Do not re-attempt anything here without reading them.**

Four of the campaign's own headline results were withdrawn after checks they failed:

| withdrawn | why |
|---|---|
| Theorems 1–2 and Theorem 3 `(⟹)` of the factorisation card | E19: the proof interchanges the `Δ_k` Voronoi series with a second summation; a legitimate version proves the sharp Dirichlet divisor conjecture |
| the general-`k` equivalence | E17: the two directions coincide only at `k = 3` |
| `G₃ ≪ y^{2/3}` and `A(h) ≪ y/h` | E20: derived from the Voronoi *diagonal*, which reproduces the conjectural value; the off-diagonal is the whole difficulty |
| "moments beat exponent pairs, increasingly in `k`" | E22: compared against one-dimensional exponent pairs, not against the multi-dimensional methods the subject uses |

**The standing methodological rule** (learned three times over): *when a Voronoi diagonal reproduces a
conjectured value, that is evidence the off-diagonal carries the entire difficulty — never evidence
the computation is complete.* And: *any argument expanding `Δ_k` in its Voronoi series inside a second
summation or integral must be checked at `k = 2` against the Dirichlet divisor conjecture before its
output is believed.*

---

## 2. The frontier, in one line

From the approximate functional equation, `μ(1/2) = b(1/2) − 1/4` where `t^{b(α)}` bounds
`|Σ_{n∼t^α}n^{−it}|`. Hence

> **LH ⟺ `|Σ_{n∼√t} n^{−it}| ≪ t^{1/4+ε}` — square-root cancellation for one explicit exponential sum
> at one explicit length.**

In the block variable `N = √t`: the record is `N^{17/21} = N^{0.8095…}`; square-root is `N^{1/2}`; the
shortfall is `2μ = 13/42`.

**Where the remaining loss sits (cycle 97):** `13/84` comes from
`decoupling → sharp mean value theorem → Bombieri–Iwaniec conversion`. Bourgain's mean-value input is
essentially sharp, so the loss is in the **BI conversion at the self-dual block** — specifically its
first and second spacing problems (counting rational resonance points near a curve). That is geometry
of numbers, and structural reasoning does not reach it.

---

## 3. What stands

All Lean-certified as exponent arithmetic in `formal/GaloisForLFunctions/HTGeometry/`, axioms
`[propext, Classical.choice, Quot.sound]`; umbrella builds green.

**Nineteen barrier theorems**, in five proved mechanisms:

1. **Inertness** — output equals input; stationary at the self-dual parameter. *Mean-value family,
   Halász–Montgomery, Guth–Maynard, short-interval mean square at its optimum, the Jensen–Backlund
   zero geometry.* Mechanism: **self-dual stationarity** — at the convexity bound the large-value
   optimisation is exactly tied across the strip, and every subconvexity input breaks the tie back to
   the critical line and the fourth moment.
2. **Circularity** — input strictly stronger than output; a moment exponent re-enters. *Backlund's
   criterion, the `S(t)` route, the double-Voronoi chain at every abscissa, the reduction loop.*
3. **Spectral thinness** — the target sits on the Eisenstein spectrum, suppressed by the rank gap
   `n(n−1)/2` (the number of positive roots of `GL(n)`), which **grows with the rank**. Kills
   Motohashi's continuous term and every higher-rank analogue.
4. **Ω-driven ceilings** — a method factoring through an error term inherits that term's Ω-floor.
   Kills Heath-Brown's twelfth moment at its input's limit, resonance (Gál sums are subpolynomial), and
   the Motohashi continuous term.
5. **The Voronoi-interchange barrier** — interchanging the `Δ_k` Voronoi series with a second
   summation is worth the divisor problem itself.

Plus **one barrier into the sum**: the **Weyl-degree trade-off** — the Taylor/Weyl route pays
`N^{2/(d+1)}` per subdivision and gains only `2^{−(d−1)}`, so raising the degree always loses; the
optimum `d = 3` gives `N^{7/8}`, worse than van der Corput.

**Structural results:**

* **one invariant**, the phase boundary `n ≲ y^{1/(k−1)}`, with which four separate obstructions
  coincide, and which separates `k = 2` from `k ≥ 3`;
* **`k = 4` is a fivefold criticality**: first non-neutral index (the neutrality law: a perfect `2j`-th
  moment beats `θ` iff `j > 1/(2θ)`, so `k = 3` is *worthless* against `13/84`); last index the
  pointwise transfer branch can reach; first index where the two conjectured correlation sizes differ
  in consequence; where the independent-signs model's error crosses the main term; and where the
  factorisation chain is exactly borderline;
* **the reformulation** `m(k) = 1 ⟺ s(k) ≤ 1/2 + 1/k`, i.e. **LH ⟺ the `k`-fold additive-divisor
  error is of square-root size asymptotically in `k`**;
* **RH refutes the independent-signs model at `k = 5`** — the model is compatible with RH exactly on
  `k ≤ 4` — and RH decides the Conrey–Gonek/Ivić dichotomy in Conrey–Gonek's favour for `k ≥ 5`;
* **the Conrey–Gonek/Ivić dichotomy is invisible at the sixth moment**: both sizes give `m(3) = 1`, so
  no result at `k = 3` can distinguish them. Evidence must be sought at `k = 4` or beyond.

---

## 4. What a successor should not do

* re-run the additive-divisor programme through Voronoi expansions (E19, E20, D31–D45);
* look for a higher-rank spectral identity (the rank gap grows as `n(n−1)/2`);
* target the **sixth** moment — it is subconvexity-neutral against `13/84` by the campaign's own
  neutrality law. **The cheapest non-neutral target is the eighth moment (`k = 4`)**, requiring
  `Δ₄(x,h) ≪ x^{1/2+ε}` with no shift cancellation, or `Σ_{h≤H}Δ₄ ≪ H^{1/2}x^{3/4+ε}` with it;
* attempt a disproof via moment lower bounds — it implies `¬RH`, hence is strictly harder.

## 5. What is genuinely open and worth attacking

1. **The BI conversion at the self-dual block** — the spacing problems. This is where `13/84` is lost.
2. **`Δ₄(x,h) ≪ x^{1/2+ε}`** — the Conrey–Gonek size at the single index `k = 4`. Yields `μ ≤ 1/8`.
3. **`s(k) ≤ 1/2 + 1/k` for all `k`** — equivalent to LH itself.
