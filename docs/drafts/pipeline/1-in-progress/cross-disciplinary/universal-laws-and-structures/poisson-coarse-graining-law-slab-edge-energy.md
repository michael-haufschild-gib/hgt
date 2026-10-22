# The Poisson coarse-graining law for the slab edge energy

- **ID:** poisson-coarse-graining-law-slab-edge-energy
- **Stage:** 1-in-progress (paper proof complete; Lean core in flight)
- **Type:** THEOREM (exact identity + monotone flow) with a certificate corollary
- **Label:** `[PAPER-PROVED]` `[BRIDGE — exact new identity; graded honestly, see novelty audit]`
- **Lane:** Fable, positive-inversion sweep
- **Inverts (positively):** NG35 (form-factor Q-extraction kill), and reorganizes the `Q`-face and
  `F_0`-face of `prime-covering-descent-index-divisibility-rh.md` cont. 50-51 into one formula.

## The identity

Work in the centered `u`-frame at height `gamma`; the height fiber is `u_j = gamma + i d_j` with
masses `m_j > 0`, and `tr = Xi'/Xi = sum_j m_j/(u - u_j) + (regular)`. Let
`F(h) := ∮_vert |tr|^2` be the energy on the two slab edges at `Re(u - gamma) = ±h`.

Write `mu := sum_j m_j delta_{d_j}` for the fiber's **displacement measure** and

> `E_a(mu) := sum_{j,k} m_j m_k * a^2 / (a^2 + (d_j - d_k)^2)`.

**Theorem A (exact evaluation).** For the fiber part of the trace,
`h * F(h) = 2*pi * E_{2h}(mu)`.

*Proof.* On the edge `u = gamma + h + i eta`, `tr(u) = sum_j m_j/(h + i(eta - d_j))` and, masses
being real, `conj(tr(u)) = sum_k m_k/(h - i(eta - d_k))`. For each ordered pair substitute
`a = eta - d_j`, `Delta = d_j - d_k`, so the integrand term is
`1/((h + i a)(h - i(a + Delta)))`. Its poles are `a = i h` (upper half-plane) and
`a = -Delta - i h` (lower). Closing upward and taking the residue at `a = i h` gives
`2*pi*i * (1/i) * 1/(2h - i*Delta) = 2*pi/(2h - i*Delta)`. Summing,
`∫_R |tr|^2 d eta = 2*pi * sum_{j,k} m_j m_k/(2h - i Delta_{jk})`. Pairing `(j,k)` with `(k,j)`
gives `1/(2h - i Delta) + 1/(2h + i Delta) = 4h/(4h^2 + Delta^2)`; multiplying by `h` and adding
the second edge yields `2*pi * sum_{j,k} m_j m_k (2h)^2/((2h)^2 + Delta^2)`. ∎

**Theorem B (spectral form).** `E_a(mu) = (a/2) * ∫_R |mu-hat(xi)|^2 e^{-a|xi|} d xi`.

*Proof.* `a^2/(a^2 + x^2) = pi*a*P_a(x)` with `P_a` the Poisson kernel, whose Fourier transform is
`e^{-a|xi|}`; the double sum is the energy `∫∫ P_a(x-y) d mu d mu`, which by Plancherel equals
`(1/2pi)∫|mu-hat|^2 e^{-a|xi|}`. ∎

**Theorem C (monotone flow with two arithmetic endpoints).** With `Q := sum_j m_j^2` (the
multiplicity second moment) and `M := sum_j m_j` (the fiber mass), `a ↦ E_a(mu)` is strictly
increasing on `(0, ∞)` unless all `d_j` coincide, and

> `lim_{a -> 0+} E_a = Q`,  `lim_{a -> ∞} E_a = M^2`.

*Proof.* Each `a^2/(a^2 + Delta^2)` has `a`-derivative `2 a Delta^2/(a^2+Delta^2)^2 >= 0`, strict
when `Delta != 0`; masses are positive. Endpoints are termwise. ∎

The `a -> 0` endpoint has a second reading via Theorem B: `(a/2)∫ f e^{-a|xi|}` is an **Abel mean**,
and the Abel mean of the almost-periodic `|mu-hat|^2` is its Bohr mean value, which is `Q` by
Parseval for almost-periodic functions.

## What this reorganizes (the positive inversion of NG35)

1. **The whole Laurent structure in one formula.** `h F(h) = 2 pi E_{2h}` expands as
   `F(h) = 2 pi Q/h + O(h)` with **no constant term from the fiber**. Hence the entire `F_0`-face
   of cont. 50 is a *truncation/regular-part* effect (finite edge length `c`, non-fiber zeros,
   archimedean block) — consistent with its recorded closed form `-4c sum m_j^2/(c^2 - d_j^2)`,
   whose `c`-dependence now has a cause rather than being an observed coincidence.
2. **The germ is a coarse-graining flow.** `E_a` merges fiber points at resolution `a` and replaces
   each cluster by its total mass squared. `E_a` therefore interpolates *monotonically* between two
   distinct zero-statistics: the multiplicity second moment `Q` (`a -> 0`, resolved) and the
   squared fiber mass `M^2` (`a -> ∞`, fully merged). RH at `gamma` says the flow is stationary.
   This is the exact content of the cont.-51 "scale crossover": the `1/h` coefficient is
   scale-dependent because `E_a` is a *flow*, not a number.

**Corollary (limit-free certificate).** Since `a^2/(a^2 + Delta^2) <= 1` with equality iff
`Delta = 0`,

> `E_a(mu) <= M^2` for every `a > 0`, with equality **iff** all `d_j` coincide.

Combined with the functional-equation mirror symmetry (`d ↦ -d`, mass-preserving), "all `d_j`
coincide" forces `d_j = 0`. Hence

> **RH at `gamma` ⟺ `h * F(h) = 2 pi M^2` at ONE (equivalently every) `h > 0`.**

This strictly improves certificate C1 of cont. 50, which required the germ `lim_{h->0} h F(h)`:
**the limit is eliminated**, and one fixed slab suffices. (Scope: stated for the fiber part; the
truncation and regular-part corrections are exactly the `F_0` terms of item 1 and must be carried
explicitly in any source-side use — they do not vanish, and pretending otherwise would repeat the
error the germ quantifier was introduced to avoid.)

## Novelty audit (honest grade)

- **The identity itself is routine.** Theorem A is a residue computation any competent analyst
  produces in an hour; Theorem B is Plancherel for the Poisson kernel; Theorem C is termwise
  monotonicity. As *mathematics* this is `[BRIDGE]`, not a discovery, and it is graded so.
- **What is new here** is the organizing statement: that the slab edge energy of the trace *is* a
  Lorentzian coarse-graining of the fiber's displacement measure, so that the `Q`-face and the
  `F_0`-face are one object, the crossover is a flow, and the certificate loses its limit. That is
  a structural clarification of this corpus's own objects, not a new fact about zeta.
- **No claim of novelty against the literature is made.** Poisson-kernel energies of zero measures
  are standard; the corpus-level reorganization is the contribution.

## Lean plan

`RHTower/PoissonCoarseGrainingEnergy.lean`: `poissonEnergy`, monotonicity in `a`, the two
endpoints, `poissonEnergy_le_sq_sum` with the equality characterization (the limit-free
certificate's algebra), and the mirror-symmetry step to `d_j = 0`.

## Log

- 2026-07-18 (Fable): derived, proved, audited, graded `[BRIDGE]`. Companion to
  `detector-order-classification-rh-readers.md` in the kill-list positive-inversion sweep.

## THE RESOLUTION THRESHOLD (added 2026-07-18) — the wall made quantitative

Combining the two results of this sweep gives an exact rate where the corpus previously had a
qualitative verdict.

**Input 1 (Detector Order Classification).** Within a height-localized family the certificate is
forced to be the centered second moment of the fiber.

**Input 2 (Theorem A above).** A reader with prime support bounded by `L` resolves the fiber only
at scale `a ≈ 1/L`: what it computes is the coarse-grained energy `E_a`, never the fiber's own
second moment, because `E_a` is exactly the fiber convolved with a Poisson kernel of width `a`.

**Theorem D (exact detection gap).** For two equal masses `m` at `±d` versus the merged mass `2m`
at the origin,

> `E_a(merged) - E_a(pair) = 2 m^2 (1 - lorentz a (2d)) = 8 m^2 d^2 / (a^2 + 4 d^2)`,

and this gap is at least `m^2` **iff** `a^2 <= 4 d^2`.

*Proof.* `E_a(pair) = 2m^2(1 + lorentz a (2d))` and `E_a(merged) = 4m^2` by direct evaluation
(`lorentz a 0 = 1`, kernel even); the gap is `2m^2(1 - lorentz a (2d))` which is
`2m^2 (2d)^2/(a^2 + (2d)^2)`. The threshold is `8 d^2 >= a^2 + 4 d^2`. ∎
(Formalized: `poissonEnergy_mirror_pair`, `poissonEnergy_merged`, `poissonEnergy_mirror_pair_gap`,
`poissonEnergy_gap_ge_iff`.)

**The consequence.** Relative to the total energy `4 m^2`, the signal from a splitting of size `d`
is `2 d^2/(a^2 + 4 d^2)`, which is `O(d^2/a^2)` for `d << a`. **Detecting displacement `d`
requires resolution `a <~ d`, hence prime support `L >~ 1/d`.** Since RH violations may be
arbitrarily mild (no uniform margin — NG14), no finite prime support suffices, and the required
support diverges like `1/d`.

**What this replaces.** Cont. 51 concluded "`Q` is not source-computable; extracting it needs `h`
below the fiber isolation scale, which is divisor data." That is now a rate rather than a verdict:
the obstruction is a *resolution deficit* with the exact exchange law `a <~ d`, and the deficit is
quadratic in `d/a`. It is the same phenomenon as the `alpha >= 1` barrier of the pair-correlation
literature, here in a form localized to a single height and with an explicit constant.

**Honest scope.** The identification `a ≈ 1/L` between resolution and prime support is the standard
uncertainty heuristic and is *not* proved here; Theorem D and the threshold are exact and formal,
the translation to prime support is the classical dictionary. Stated separately so the proved part
and the heuristic part are not confused. Grade of Theorem D: `[BRIDGE]` as mathematics (two-line
kernel algebra), `[useful]` as a statement, because it converts a wall into a rate.
