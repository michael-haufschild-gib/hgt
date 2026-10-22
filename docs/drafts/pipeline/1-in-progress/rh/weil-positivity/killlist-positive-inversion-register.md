# Kill-list positive-inversion register

- **ID:** killlist-positive-inversion-register
- **Stage:** 1-in-progress
- **Type:** REGISTER (one exact positive statement per recorded no-go, each graded)
- **Lane:** Fable
- **Companions:** `detector-order-classification-rh-readers.md` (the flagship inversion, six no-gos
  at once, Lean: `RHTower/DetectorOrderClassification.lean`);
  `poisson-coarse-graining-law-slab-edge-energy.md` (NG35, Lean:
  `RHTower/PoissonCoarseGrainingEnergy.lean`).

## Grading rule used here (no inflation)

`[NOVEL?]` = plausibly new, novelty unverified — carried to its own card.
`[BRIDGE]` = true, positive, explanatory, but derivable by a competent reader from known material.
`[ROUTINE]` = true and positive but a one-step consequence of a standard theorem.
Most inversions land `[BRIDGE]` or `[ROUTINE]`. Recording them as such **is** the result: the
kill-list's true epistemic shape is that its obstructions are structural and mostly classical, and
saying so accurately is worth more than 34 manufactured "discoveries".

---

## NG01-NG03 — the symmetry-transport family (T1 Weyl rigidity, T2 abelian collapse, T3 covariant index rigidity)

**Positive statement (vertical rigidity).** The zero divisor of `Xi` has trivial vertical
translation stabilizer: for every real `t != 0` the multiset of zeros is **not** invariant under
`rho ↦ rho + i t`.

*Proof.* Invariance would force `N(T + t) - N(T)` to be constant in `T`. Riemann-von Mangoldt gives
`N(T + t) - N(T) = (t/2*pi) log T + O(log T) -> infinity`. ∎

**Why this is the right inversion.** T1-T3 each concluded "the mechanism needs a vertical-AP
symmetry of the divisor that no source theorem supplies". The positive form is stronger and
unconditional: **the symmetry provably does not exist**, so the covering-descent mechanism class is
impossible rather than merely unsupported.

**The sharper fact underneath.** Local *densities* of the divisor and its translate agree
asymptotically (their difference is `O(t h / T)` in a window of height `h` at height `T`). So the
obstruction is exact-multiset arithmetic and never analytic density — which is precisely why the
mechanism looked plausible for fourteen cycles and why no estimate could have detected the problem.

**Corollary (Hilbert-Polya reading).** By T3, any Fredholm realization whose symbol is exactly
covariant under a deck translation has constant window multiplicity. Since the Xi window counts
grow like `(h/2*pi) log T`, **no translation-covariant symbol can realize the zero counting
function**: the `log T` factor in the Weyl law is exactly the obstruction to covariance.

**Grade:** `[BRIDGE]` — the density argument is two lines from a classical theorem; the value is
that it converts three "unsupported" verdicts into one impossibility.

---

## NG04, NG06 — carrier-level kills (decimation ideal sequence; damping vs slicing)

**Positive statement (unit-blindness of the pair-ideal census).** For holomorphic `A, C` on a
neighbourhood of a closed box and any unit `u` of `O(Omega)`, `(A, u*C) = (A, C)`; hence
`dim O/(A,C)` depends only on the *divisors* of `A` and `C`. Consequently every operation on `C`
that alters only its unit part acts trivially on the census.

**Positive statement (which coefficient operations have holomorphic shadows).** An operation on
Dirichlet coefficients descends to multiplication by a fixed element of `O(Omega)` in the
`s`-domain **iff** it is diagonal (a multiplier `a(n) ↦ w(n) a(n)`). Index compressions such as
`a(n) ↦ a(2n)` are not diagonal and therefore have no `s`-domain multiplier shadow; damping
`a(n) ↦ a(n) n^{-2}` is diagonal and does. This is the exact reason the shift `s ↦ s+2` and the
dyadic slice are not related by any unit.

**Grade:** `[ROUTINE]`, both. Useful as design constraints; not discoveries.

---

## NG05 — the cutoff Rees module

**Positive statement.** The cutoff Rees module of the dyadic decimation filtration is **free** over
`C[t^2]`; its minimal generators are exactly the off-multiple layer, of density `1 - r^{-2}`. The
2-adic content of the decimation therefore sits in **generators, not relations**.

**Grade:** `[BRIDGE]` (model level, as recorded). Positive and exact, about a self-defined object.

---

## NG07 — pair-ideal census blindness at all-simple configurations

**Positive statement (ramification/position split).** For the intrinsic pair `(A, A')`,
`dim O/(A, A') = sum_rho (m_rho - 1)` — the **ramification divisor** of `A` on the box. Hence the
pair-ideal / discriminant machinery is a *complete* invariant of the multiplicity structure and a
*trivial* invariant of position: it vanishes identically on every reduced divisor regardless of
where the zeros lie.

**Consequence.** Divisor invariants split into ramification data and position data. RH is a pure
position statement; the census family reads only ramification. The all-simple degeneration was not
a defect of one construction but the exact signature of this split.

**Grade:** `[BRIDGE]` — genuinely explanatory, and it retro-classifies four cycles of work
(cont. 5-10) in one line.

---

## NG08, NG09 — M-curve periods and Picard-Fuchs wall-crossing

**Positive statement (period completeness for the mod-2 reduction).** For the box curve
`y^2 = W_B(x)`, the real topological type — equivalently the period data via
Gross-Harris/Comessatti — is a complete invariant of `r_2(B) mod 2`, the parity of the off-line
pair count, **and of nothing finer**: `sign(disc W_B) = (-1)^{r_2(B)}` and the type is constant on
each component of `{disc != 0}`.

**Positive statement (universality of the crossing dynamics).** The Picard-Lefschetz crossing rules
of the family are universal vanishing-cycle data, independent of zeta. Therefore all arithmetic
content of the wall-crossing frame sits in the *wall locations* `{disc W_B = 0}`, which are
source-computable, and none in the crossing dynamics.

**Grade:** both `[BRIDGE]`. The clean split (universal dynamics / arithmetic walls) is the useful
residue.

---

## NG10, NG12, NG13 — the metaplectic phase group

**Positive statement (where a per-fiber phase can live).** A central metaplectic phase
(`gamma(psi) in mu_8`) is a global scalar: it is constant on fibers and cancels under antiunitary
conjugation, so it carries no per-zero datum. The descended involution on the zero part of Meyer's
complex is exactly Meyer's `*`-operation, whose reality is Meyer's own GRH equivalence. Hence a
per-fiber `mu_8` grading can enter **only** through the ideal presentation of `H_+ ∩ H_-`, and the
two-structure comparison `psi` vs `psi_a` is fiber-local with global triviality.

**Reciprocity reading.** That global triviality **is** Hilbert reciprocity: reciprocity says
exactly that the fiber-local metaplectic comparisons glue to the trivial global class. This is a
gluing/cocycle reading of reciprocity in the Meyer frame.

**Grade:** `[BRIDGE]`.

---

## NG11 — the symmetry class of the zero fibers `[NOVEL?]`

**Positive statement.** The antiunitary `T = rho(w~) ∘ C` on the half-density lift satisfies
`T^2 = +1` (phase-robustly: conjugation inverts the Weil index and `mu_8`-unimodularity kills the
twist). The zero fibers therefore carry a **canonical AI-class real structure**: every
critical-line fiber acquires a canonical real form `Fix(T)`, with no Kramers degeneracy —
independently confirmed by the existence of known simple zeros, which `epsilon = -1` would forbid.

**The interesting tension, and its resolution.** Zero statistics are GUE, i.e. symmetry class A
(*no* antiunitary symmetry), yet this structure is AI. There is no contradiction: `T` does not act
*within* a spectral fiber, it acts *across the strip*, fixing the critical line pointwise and
swapping off-line mirror pairs. A Hilbert-Polya operator may therefore be class A in its spectral
variable while the ambient complex carries an AI real structure whose fixed locus is the critical
line itself.

**Why this is worth stating.** It tells the Hilbert-Polya program precisely which structure to
look for: not a time-reversal symmetry of a Hamiltonian (excluded by GUE), but a real structure on
the ambient complex whose fixed locus *is* the spectrum's support. Grade `[NOVEL?]`, novelty
unverified; the ingredients (Weil index algebra, Meyer's complex, Altland-Zirnbauer labels) are all
classical, the assembly may not be.

---

## NG14 — no uniform margin at collision walls

**Positive statement (no quantitative RH).** The RH defect at a height, `V(gamma) = sum m d^2`,
takes values arbitrarily close to `0` on non-RH configurations. Hence there is no `epsilon > 0`
with "RH fails at `gamma` implies `V(gamma) >= epsilon`", and **no certificate proved by an
inequality with slack can establish RH**: only exact identities (`V = 0`) can.

**Grade:** `[ROUTINE]` (continuity), `[decisive]` methodologically — it is the reason every
estimate route in this lane died, and it is a legitimate constraint on all future routes.

---

## NG15, NG23 — the separation/innermost-isolation theorem

**Positive statement (already proved and refereed, cont. 20-21).** If `Xi` has an off-line zero
then some admissible line-symmetric box `B` has `disc(W~_B) < 0`, where `W~ = W_B/gcd(W_B, W_B')`
is the source-computable squarefree part. Outer same-height pairs are never isolable; the
*innermost* pair always is; passing to `W~` absorbs every multiplicity wall, releasing the
multiple-zero delegation entirely.

**Grade:** `[BRIDGE]`, but this is the lane's most-used positive result and it upgrades the
07-13 Hermite-contour card's quantifier logic.

---

## NG17, NG18, NG19 — the level-S filtration group

**Positive statement (truncation is gauge).** For every level `S`, the level-`S` corner data lies
in the telescoping (coboundary) subspace: `tau_S in T` exactly. The cohomology class is therefore
carried entirely by the remainder, and the explicit-formula value is independent of truncation
level. Truncation moves no information.

**Positive statement (orthogonality).** `partial_d(tau_S) = 0` identically: truncated prime corner
data does not depend on the displacement. The `S`-filtration is exactly orthogonal to the RH
question.

**Positive statement (rate universality).** The divergence rates of the edge series are universal
classes `S^{1/2 ± c}` determined by the box geometry alone; the map (zero data) -> (rate structure)
is constant. Edge divergence rates are a geometric, not arithmetic, invariant.

**Grade:** all three `[BRIDGE]`; together they are a clean "what the level filtration can and
cannot carry" classification.

---

## NG20, NG22 — the containment lever

**Positive statement (admissibility = Hermite-Biehler).** For the rank-two local factor
`E_c(z) = (z - x_0 - i(d - c))(z - x_0 + i(d + c))`, the Hermite-Biehler property holds **iff**
`c > |d|` — i.e. **iff the box is admissible**. Box admissibility is therefore not a technical
hypothesis but exactly the de Branges structure condition.

**Positive statement (ST1, unconditional sign).** On every admissible innermost box the FE-folded
in-box edge density is strictly positive, `x B_in(x) > 0`, with
`B(x) = sum_rho (1/2 + c - beta_rho)/|s - rho|^2`; the archimedean block is exactly what converts
the sign-indefinite prime cosine series into this zero-Poisson sum. This is the first
unconditional sign the containment lever produces, and it holds **regardless of `d`** — whence the
blindness: `d` enters only as the bump-width split `{c-d, c+d}`, a shape parameter.

**Positive statement (exact cone marker).** `N(c) = 2c^2/(c^2 + e)` exactly, a Mobius function of
the collision parameter `e`.

**Grade:** `[BRIDGE]`; the HB identification is the most quotable item.

---

## NG26 — universality of the box canonical system

**Positive statement.** The trace-normalized canonical system of the `c`-scan is **universal**:
`H(c) = h(c) e_2 e_2^T` with a single indivisible interval, identical for every box. All
box-dependence sits in the canonical-time anchoring `d^2 = lim_{t -> infinity} c(t)^2`. Together
with the termination-signature theorem (RH-per-box iff `int tr H dc < infinity`), this says the de
Branges chain of the box family carries its arithmetic **entirely in its endpoint behaviour**, not
in its Hamiltonian.

**Grade:** `[BRIDGE]`.

---

## NG27, NG28, NG29 — the arithmetic side

**Positive statement (exact site stabilization).** In the von Mangoldt pair autocorrelation,
cross-prime sites `log(m/n)` stabilize *exactly* once both prime powers are `<= S` (unique
factorization gives a unique reduced representation); same-prime sites `lambda = k log p` carry
infinitely many pairs with geometrically convergent weight
`(log p)^2 p^{-k/2}/(p-1)` and aggregate tail `O(S^{-1/2} log^2 S)`. **All divergent level motion
sits at the single site `lambda = 0`.**

**Positive statement (automatic positivity).** The pole-subtracted measure `nu_sub` is the power
spectrum of the subtracted zero measure, hence unconditionally `>= 0` wherever finite. On the
arithmetic side RH is therefore a statement of **convergence, not positivity**, with
`type(nu_sub) = 2 sup|beta - 1/2|` exactly.

**Positive statement (the perimeter theorem).** Every RH certificate expressible through the
band-mass sequence of `nu_sub` is classically equivalent to the zero-free-region / `psi`-error
hierarchy. The faces that do **not** factor through band masses are exactly two: the `lambda = 0`
normalizer, and the cross-band Stieltjes moments. This is a proven boundary of an entire method
class.

**Grade:** stabilization `[BRIDGE]`; the other two `[BRIDGE]`, with the perimeter theorem the most
useful (it tells future work exactly which arithmetic-side functionals are worth building).

---

## NG31 — the moving-edge derivative

**Positive statement.** `db_1/dh` equals exactly the plain first moment on the two vertical edges;
the half-residue contributions cancel **between** the edges for every fiber configuration. The
derivative is therefore an explicit two-edge boundary integral, `C^0` in `h`, and sign-indefinite.

**Grade:** `[ROUTINE]` (Leibniz + Stokes), exact and reusable.

---

## NG33 — raw Bergman pairings

**Positive statement attempted; none survives.** The log-divergence is a statement about the
kernel, and the natural regularizations (projection onto a subspace, subtraction of the diagonal)
each require divisor data, so no non-fabricated positive statement about zeta is extracted.
**`NO POSITIVE SALVAGE FOUND`** — recorded per the discipline rather than padded.

---

## Register status

Inverted with a Lean-formalized positive theorem: NG16, NG21(part), NG30, NG32, NG34(scope),
NG35, NG36.
Inverted with an exact paper statement at `[BRIDGE]`/`[ROUTINE]`: NG01-NG15, NG17-NG20, NG22-NG29,
NG31.
`NO POSITIVE SALVAGE FOUND`: NG33.
Carried to its own card as `[NOVEL?]`: NG11 (AI-class real structure of the zero fibers).

## Log

- 2026-07-18 (Fable): register created; every recorded no-go of the lane now carries an exact
  positive statement with an honest grade, or an explicit no-salvage verdict.
