# Weil positivity ladder on outside-strip base points

**Stage 1 (live conjecture + paper-proof work). One claim per card; this is the programme's rung 0.**

## Why this card exists

The xi-ward campaign (`xi-ward-moire-prime-pair-attack.md`, steps 9bd–9bn) terminated in a
structural obstruction, established with sources at step 9bn:

> Every criterion produced there is an EQUIVALENCE. Equivalences transport difficulty; they add no
> input. The total arithmetic input of that chain is (i) `ζ ≠ 0` on `Re s > 1` (strip confinement)
> and (ii) explicit theta/Γ values. **Davenport–Heilbronn** exhibits Dirichlet series with a
> functional equation of the same shape and off-line zeros, so (i)+(ii) cannot imply RH in ANY
> representation.

Representation lesson: a closing route must make **`Λ(n) ≥ 0` a primitive**, not a derived scalar.
The corpus's `ZetaThreeFourOne.lean` (3-4-1 inequality) and `exists_low_height_zeta_zero_free` were
audited: that reach does NOT extend the certified Herglotz region into the strip — far copies
dominate the balance and no low-height copy is known to exist without computation.

## The one structural opening that survived

**[LOCAL-RESEARCH]** step 9bj: off-critical zeros are detected by Weil Gram families whose base
points lie entirely OUTSIDE the strip. Numerically decisive and, crucially, **local** (N=30 vs N=100
agree to 3 digits, so the signal does not depend on the global zero configuration) and sensitive to
arbitrarily small displacements given enough base points (4 points catch `v = 0.001`).

Why that matters: outside the strip the prime side CONVERGES. `Im z < −½` gives `Re s > 1`
(Dirichlet directly); `Im z > ½` gives `Re s < 0` (Dirichlet after the functional equation). Inside
the strip no series converges — which is exactly why the campaign's arithmetic never reached its
detection region. Outside-strip detection removes that mismatch.

## Rung 0 — the exact claim to prove on paper first

**[CONJECTURE]** *(outside-strip detection)* Let `pt₀` be a divisor copy with `Im pt₀ = v ≠ 0`. Then
for every `h > ½` there exist finitely many base points `z₁,…,z_n` with `|Im z_k| = h` and
coefficients `c ∈ ℂⁿ` such that the Weil Gram form `Q(c) = Σ_{i,j} c_i conj(c_j) M(z_i, conj z_j)`
is strictly negative.

### Paper-proof route (mechanism checked on paper; NOT closed)

1. **[CORPUS]** rank-one blow-up: `exists_neg_weilDiagonal_of_offAxis_zero` gives, for the INSIDE
   point `z = pt₀ + δ`, a diagonal value `Q ≤ −C/|δ|` (9bh).
2. **Taylor transport.** `z ↦ K z (pt)` is analytic with a single pole at `z = pt`. Expanded about an
   outside base point `z₀` (`|Im z₀| = h`), its series converges for `|z − z₀| < |pt − z₀|`, and an
   `n`-point family based at `z₀` realizes the partial sums. So the inside kernel `K_{pt₀+δ}` is a
   limit of outside-based combinations.
3. **Continuity of the form.** `|Q(F) − Q(F')| ≤ ‖F − F'‖·(‖F‖+‖F'‖)` in `ℓ²` of the divisor, which
   converges by the genus-one bound (corpus `xiSpectralPoint_inv_sq_summable`).
4. Choose `δ` so that (1) beats the (2)-error measured in (3).

### [OPEN CORE] — the exact unproved step

Step 2's radius about `z₀` is exactly `|pt₀ − z₀|`, and the target `pt₀ + δ` sits essentially ON that
circle, so the Taylor remainder is only marginally controlled and the required `n` grows as `δ → 0`.
**Missing lemma: a quantitative `ℓ²(divisor)` bound on the Taylor remainder, uniform over the
divisor** — control of `Σ_q |R_n(pt_q)|²` where the radius `|pt_q − z₀|` varies with `q`; binding for
copies nearest `z₀`, harmless for far ones. Ordinary complex analysis, not yet written.

## Discipline for this card

- Stage 1 until the rung-0 paper proof CLOSES. **No Lean infrastructure before then** (Gate 4).
- The 9bj numerics are an engineering sanity check, NOT evidence; they may not enter the proof.
- On closing rung 0 the criterion becomes: RH ⟺ PSD of a Gram family whose every entry is an
  absolutely convergent prime expression. Rung 1 is then the first arithmetic positivity statement:
  identify coefficient families whose prime-side weight has a definite sign (the analogue of
  small-support band-limiting, where the 3-4-1 primitive enters), and prove positivity there.
- Ladder shape: rung `k` extends the admissible base-point family; RH is the limit. The 2026
  literature reports explicit failures of candidate positivity statements at large support, so rung 1
  must be attacked with that failure as a design constraint, not ignored.

## Status

`[CONJECTURE]` rung 0 stated exactly; `[OPEN CORE]` named; paper proof NOT closed; no Lean written.

---

## Rung 0 — PAPER PROOF CLOSED (Gate 4)

The Taylor route above is **dead**, and the reason is sharp and worth recording.

**[FALSIFIED — the Taylor transport]** Expanding `z ↦ K z (p)` about an outside base point `z₀` has
radius exactly `|p − z₀|`, which DEPENDS ON THE COPY. Approaching `pt₀` from below (the only
direction where the rank-one form goes to `−∞`: the direction is forced to be `δ ∝ A(pt₀)·m ≈ −i`,
since `cos 2·arg pt₀ ≈ 1` makes the from-above approach send `Q → +∞`) puts the target inside the
disc for `pt₀` when `z₀` is BELOW the strip — but then the conjugate copy `conj pt₀` has the SMALLER
radius `h − v₀`, and the target lies outside ITS disc, so the partial sums blow up there like
`((h+v₀−ε)/(h−v₀))ⁿ`. No single expansion centre serves both members of a conjugate pair.

**Representation lesson:** approximation of the inside kernel is not a Taylor problem at all. It is a
DENSITY problem, and density is decided by the identity theorem, not by radii.

### The proof

Work in `ℓ²(divisor)`; a test function enters the Weil form only through its restriction to the
divisor.

1. **The form is bounded.** `Q(F) = Σ'_q F(pt_q)·F^#(pt_q)` with `F^#(w) = conj F(conj w)`. The
   divisor is conjugation-stable, so `‖F^#|_div‖ = ‖F|_div‖` and `|Q(F)| ≤ ‖F|_div‖²`. Moreover
   `|Q(F) − Q(G)| ≤ ‖F−G‖(‖F‖+‖G‖)`: **`Q` is continuous on `ℓ²(divisor)`.**
2. **Kernels are in `ℓ²`.** `K z (p) = −z/(p(p−z))`, so `|K z (p)| ≤ C_z/|p|²` for all but finitely
   many copies, and `Σ 1/‖pt‖² < ∞` (corpus `xiSpectralPoint_inv_sq_summable`). Hence
   `K z|_div ∈ ℓ²(divisor)`.
3. **Density by the identity theorem.** Let `a ∈ ℓ²(divisor)` annihilate every `K z|_div` for `z` in
   the open outside-strip region `Ω`. Put `φ(z) := Σ_q conj(a_q)·K z (pt_q)`. The bound in (2) is
   locally uniform in `z`, so by Cauchy–Schwarz the series converges locally uniformly on
   `ℂ ∖ divisor`; hence **`φ` is analytic there**. `ℂ` minus a discrete set is connected, and `φ ≡ 0`
   on the open set `Ω`, so `φ ≡ 0` — in particular `φ(w) = 0` for the inside point `w`. So `a ⊥ K w`.
   By Hahn–Banach, **`K w` lies in the closed span of the outside-strip kernels.**
4. **Transfer.** Choose `w = pt₀ + δ` as in the rank-one theorem, so `Q(K w) < 0` (corpus
   `exists_neg_weilDiagonal_of_offAxis_zero`, 9bh). Take finite combinations `F_n → K w` in
   `ℓ²(divisor)` from (3). By (1), `Q(F_n) → Q(K w) < 0`, so `Q(F_n) < 0` for large `n`. ∎

**[PAPER-PROVED] rung 0.** Combined with `weilGram_form_re_nonneg_of_all_real` (9bk: on-line copies
contribute only PSD rank-ones, base points unrestricted), this yields the target criterion:

> **RH ⟺ the Weil Gram family with base points confined OUTSIDE the strip is positive semidefinite.**

Every entry of that family is an absolutely convergent prime expression (`Im z < −½` gives `Re s > 1`
directly; `Im z > ½` gives `Re s < 0`, hence `Re(1−s) > 1`, after the functional equation). **The
critical strip, where no Dirichlet series converges, is bypassed entirely** — which is exactly the
mismatch that defeated the previous campaign.

Note the proof consumes NO estimate: boundedness, analyticity, the identity theorem, Hahn–Banach.
The numerics of 9bj played no role and remain a sanity check only.

## Next

- **Gate 5 for rung 0:** formalize. Needed: `ℓ²(divisor)` as an inner-product space, continuity of
  `Q`, local-uniform analyticity of `φ`, the identity theorem (mathlib has
  `AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero`, already used in the corpus), and
  Hahn–Banach (mathlib). No new mathematics required.
- **Rung 1 (the first arithmetic rung, where `Λ ≥ 0` finally enters as a primitive):** with the
  criterion now stated on convergent prime data, find coefficient families whose prime-side weight
  `Σ_n Λ(n) n^{−1/2}·W_n(c)` has a definite sign, and prove positivity there. Design constraint from
  the 2026 literature: candidate positivity statements at large support have been explicitly
  disproved, so rung 1 must identify WHICH support ranges survive, not assume all do.

## Gate 5 progress — rung 0 foundation LANDED

`XiWeilDivisorHilbert.lean`, clean, sorry-free, axioms standard. This is step (1)–(2) of the rung-0
paper proof, formalized:

- **`XiDivisorL2 := lp (fun _ : XiZeroCopy => ℂ) 2`** — the divisor Hilbert space, the carrier the
  paper proof needs. mathlib supplies `InnerProductSpace`, `CompleteSpace`, and the orthogonal
  machinery (`Submodule.orthogonal_orthogonal`) on it.
- **`memℓp_kernel_restriction`** — every regularized Cauchy kernel restricts into `ℓ²(divisor)`.
  Proof route (no estimate): the relative resolvent trace is absolutely summable (genus-one), an
  absolutely summable family is bounded by its own total, and `‖f q‖² ≤ M‖f q‖` then transfers
  summability from the first power to the square (`summable_sq_of_summable_norm`).
- **`xiKernelVec`** — the kernel as a vector of that space.
- **`summable_weilL2Summand`** — the Weil summand `a q · conj(a (lineConj q))` is absolutely summable
  for EVERY `ℓ²` sequence, by `|xy| ≤ ½(x²+y²)` against the two square-summable families (the second
  obtained by reindexing along the conjugation involution, `summable_sq_lineConj`).
- **`xiWeilL2Form`** and **`xiWeilL2Form_kernelVec`** — the intrinsic form on the Hilbert space, and
  the identification that on a kernel vector it computes the Weil polarization of that kernel. This
  is the bridge that lets the rank-one detection theorem (9bh) be read as a statement about a vector
  of `XiDivisorL2`.

**Remaining for rung 0's Gate 5:** (a) continuity of `xiWeilL2Form` (the `‖a−b‖(‖a‖+‖b‖)` bound —
same AM–GM ingredient, already present); (b) analyticity of `φ(z) = Σ_q conj(a_q)·K z (pt_q)` in `z`
off the divisor (locally uniform convergence via Cauchy–Schwarz against the `O(1/‖pt‖²)` bound);
(c) the identity-theorem step (mathlib
`AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero`, already used elsewhere in the
corpus); (d) `Sᗮᗮ = S` to conclude membership in the closed span. No new mathematics in any of them.

### Gate 5 progress — step (a) continuity LANDED

**`xiWeilL2Form_sub_norm_le`**: `‖Q a − Q b‖ ≤ ‖a−b‖·‖a‖ + ‖b‖·‖a−b‖` on `XiDivisorL2`.
Ingredients, all now certified: the reindexing isometry `xiLineConjVec` along the divisor's
conjugation involution (`xiLineConjVec_norm` — a bijection preserves the `lp` norm, via
`lp.norm_eq_tsum_rpow` and `Equiv.tsum_eq`), Hölder on `ℓ²` (`tsum_norm_mul_le`, from mathlib's
`lp.tsum_mul_le_mul_norm` at the conjugate pair `(2,2)`), and the pointwise split
`a·conj(a∘σ) − b·conj(b∘σ) = (a−b)·conj(a∘σ) + b·conj((a−b)∘σ)`.

This is the transport mechanism of the rung-0 proof: a value of the Weil form at ONE test function
now provably controls its value at any test function approximating it in `ℓ²(divisor)`. With
`xiWeilL2Form_kernelVec` (the form on a kernel vector IS the Weil polarization), the rank-one
detection theorem 9bh is now a statement about a vector of `XiDivisorL2` that transports.

**Remaining for rung 0's Gate 5:** (b) analyticity of `φ(z) = Σ_q conj(a_q)·K z (pt_q)` off the
divisor — locally uniform convergence by Cauchy–Schwarz against the `O(1/‖pt‖²)` bound, the same
two ingredients already certified here; (c) the identity theorem (mathlib, already used in the
corpus); (d) `Sᗮᗮ = S`. Then rung 0 is `[LEAN-PROVED]` and the criterion is stated on convergent
prime data.

### Gate 5 progress — step (b) domination LANDED

The analyticity of the annihilator `φ(z) = Σ_q conj(a_q)·K z (pt_q)` needs a summable majorant
uniform on a ball. Both halves are now certified:

- **`xiInvVec`** — the reciprocals `q ↦ pt_q⁻¹` form an `ℓ²` vector on the divisor. Immediate from
  the genus-one bound `xiSpectralPoint_inv_sq_summable`; no floor or estimate required.
- **`norm_kernel_le_of_ball`** — if `XiC` does not vanish on `ball s r₀`, then for every base point
  `z` in the HALF ball and every copy,
  `‖K z (pt_q)‖ ≤ (2(‖s‖+r₀)/r₀)·‖pt_q⁻¹‖`.
  The mechanism is that non-vanishing on the ball forces `‖pt_q − z‖ ≥ r₀/2` for EVERY copy — a
  uniform separation obtained from continuity alone, with no appeal to local finiteness of the
  divisor. Combined with `‖z‖ ≤ ‖s‖ + r₀` the kernel bound follows by one division.

Consequence: on the half ball, `‖conj(a_q)·K z (pt_q)‖ ≤ ‖a_q‖·C·‖xiInvVec q‖`, whose summability is
`summable_norm_mul a xiInvVec` (Hölder, already certified in §3). That is exactly the hypothesis of
the corpus's locally-normal-convergence template (`SummableLocallyUniformlyOn`, as used in
`ArcsineZetaAnalyticFamily.lean`) and of mathlib's `differentiableOn_tsum_of_summable_norm`.

**Remaining for rung 0:** assemble those two into `DifferentiableOn ℂ φ {z | XiC z ≠ 0}`; then the
identity theorem on that connected open set; then `Sᗮᗮ = S`. No new mathematics.

### Gate 5 progress — step (c) ANALYTICITY LANDED

**`differentiableAt_annihilator`**: for every `a ∈ ℓ²(divisor)`, the annihilator function
  `φ_a(z) = Σ'_q conj(a q) · K z (pt_q)`
is differentiable at every `z` with `XiC z ≠ 0`.

Assembly, all pieces certified here: continuity of `XiC` gives a ball on which it does not vanish;
`half_le_norm_sub_of_ball` turns that into a UNIFORM separation `‖pt_q − z‖ ≥ r₀/2` over the whole
divisor on the half ball (continuity only — no local finiteness); `norm_kernel_le_of_ball` converts
the separation into the domination `‖conj(a q)·K z (pt_q)‖ ≤ C·‖a q‖·‖xiInvVec q‖`; Hölder
(`summable_norm_mul`) makes that majorant summable; each term is differentiable because the pole
`pt_q` is outside the half ball. Then locally normal convergence gives differentiability of the sum.

So `φ_a` is analytic on the connected open set `{z | XiC z ≠ 0}` — exactly the hypothesis the
identity theorem consumes.

**Remaining for rung 0:** (d) the identity theorem — `φ_a ≡ 0` on the outside-strip region forces
`φ_a(w) = 0` at the inside detection point (mathlib
`AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero`, used elsewhere in the corpus; the
domain is `ℂ` minus a discrete set, hence preconnected); (e) `Sᗮᗮ = S` to convert the annihilator
statement into membership in the closed span; then the transport by `xiWeilL2Form_sub_norm_le`
closes rung 0.

### Gate 5 progress — the identity-theorem domain LANDED

The identity theorem needs its domain open and preconnected. Both are now certified for the divisor
complement, reusing the corpus rather than rebuilding:

- **`XiC_zeroSet_countable`** — the zero set of `XiC` is countable: it is the RANGE of
  `xiSpectralPoint` over `XiZeroCopy` (`XiC_eq_zero_iff_exists_xiZeroCopy`), and `XiZeroCopy` is
  countable via the corpus's `xiDivisorSupport_univ_countable` (extracted there from mathlib's
  locally finite divisor plus σ-compactness of the plane). Reusing the corpus theorem avoided
  redoing the local-finiteness argument entirely.
- **`isPreconnected_XiC_ne_zero`** — removing a countable set from the plane leaves a path-connected
  set (`Set.Countable.isPathConnected_compl_of_one_lt_rank`, `rank ℝ ℂ = 2`).
- **`isOpen_XiC_ne_zero`** — continuity of `XiC`.

With `differentiableAt_annihilator`, the annihilator `φ_a` is analytic on an OPEN PRECONNECTED set,
so vanishing on any nonempty open subset forces `φ_a ≡ 0`. That is the mathematical content of rung
0's step (d). What remains: invoke the identity theorem on these hypotheses, then convert
`a ⊥ every outside kernel ⟹ a ⊥ K_w` into membership in the closed span via `Sᗮᗮ = S`, after which
`xiWeilL2Form_sub_norm_le` transports the rank-one negativity and rung 0 closes.

### Gate 5 progress — step (d) IDENTITY THEOREM LANDED

**`inner_kernelVec_eq`** — the annihilator function IS the inner product against the kernel vector:
`⟪a, K z⟫ = Σ'_q conj(a q)·K z (pt q)`. This bridges the Hilbert-space statement (orthogonality) and
the analytic statement (a function of the base point).

**`annihilator_eq_zero_of_vanishing_open`** — if the annihilator vanishes on ANY nonempty open set of
admissible base points, it vanishes at EVERY point off the divisor. Proof: `differentiableAt_annihilator`
gives `DifferentiableOn` on `{XiC ≠ 0}`, hence `AnalyticOnNhd`; vanishing on an open subset gives
eventual vanishing at an interior point; and
`AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero` applies because
`isPreconnected_XiC_ne_zero` and `isOpen_XiC_ne_zero` are certified.

**This is the mathematical core of rung 0.** In Hilbert-space terms: a vector orthogonal to every
outside-strip kernel is orthogonal to EVERY kernel, including the inside ones where detection
happens. The Taylor route died because radii vary per copy (FALSIFIED entry above); the identity
theorem does not care about radii at all.

**Remaining for rung 0:** assembly only — `Sᗮ ⊆ {K_w}ᗮ` (immediate from the two theorems above),
hence `K_w ∈ Sᗮᗮ = S̄` (mathlib `Submodule.orthogonal_orthogonal`), then transport the rank-one
negativity along `xiWeilL2Form_sub_norm_le`. No further analysis.

## RUNG 0 CLOSED — [LEAN-PROVED]

**`riemannHypothesis_iff_outsideStrip_nonneg`** (axioms standard, sorry-free, lint clean):

> `RiemannHypothesis ↔ ∀ F ∈ Submodule.span ℂ outsideKernelSet, 0 ≤ (xiWeilL2Form F).re`

where `outsideKernelSet` is the set of regularized Cauchy kernels whose base point satisfies
`1/2 < |Im z|` — entirely off the critical strip.

Both directions:
- **(⟸)** `exists_neg_weilL2Form_outsideStrip`: an off-critical zero yields a FINITE outside-strip
  combination with negative form. Chain: rank-one detection at an inside point (9bh) →
  `kernelVec_mem_closure_span` (a vector orthogonal to all outside kernels is orthogonal to every
  kernel, by analyticity + the identity theorem on the preconnected divisor complement, then
  `Sᗮᗮ = S`) → transport by the Lipschitz bound `xiWeilL2Form_sub_norm_le` with an explicit ε.
- **(⟹)** `xiWeilL2Form_re_nonneg_of_rh`: under RH every spectral point is real, so conjugation
  fixes it; vectors in the span factor through the spectral point
  (`factorsThroughSpectral_of_mem_span`), hence the form collapses to `Σ normSq`, manifestly ≥ 0.

**Why this is the right carrier.** The strip is where detection must happen (a displaced zero is
inside it) but where no Dirichlet series converges; outside the strip every Gram entry is absolutely
convergent (`Im z < −½` gives `Re s > 1`; `Im z > ½` gives `Re(1−s) > 1` via the functional
equation). Rung 0 removes that mismatch: detection is now performed by base points that never enter
the strip.

**Rung 1** is now the live claim: with the criterion on convergent prime data, find coefficient
families whose prime-side weight `Σ_n Λ(n) n^{−1/2} W_n(c)` has a definite sign — the point where
`Λ(n) ≥ 0` enters as a primitive rather than as a derived scalar. Design constraint (9bn): the 2026
literature reports candidate positivity statements at large support explicitly DISPROVED, so rung 1
must determine which support ranges survive rather than assume all do.

## Rung 1 — the arithmetic Gram entry [LEAN-PROVED, first brick]

`XiWeilArithmeticGram.lean`, clean, sorry-free, axioms standard.

**`xiWeilGramEntry_arithmetic`** — for base points BELOW the strip (`Im z < −1/2`, hence
`Re(1/2 + zi) > 1`), every Gram entry of the rung-0 criterion equals

  `M₁ − (z'/(z(z−z')))·[s⁻¹ + (s−1)⁻¹ + logDeriv Γ_ℝ(s) − L(Λ,s)]·I`
      `+ (z/(z'(z−z')))·[same at s']·I`,  `s = 1/2 + zi`,

with `L(Λ,s) = Σ Λ(n) n^{−s}` absolutely convergent
(`lseries_vonMangoldt_summable_of_im_lt_neg_half`). Supporting:
`one_lt_re_of_im_lt_neg_half`, `XiC_ne_zero_of_im_lt_neg_half`, and
`logDeriv_XiC_eq_arithmetic_of_im_lt_neg_half` (the centered logarithmic derivative is `I` times the
prime–archimedean expression, via the corpus's `logDeriv_xi_eq_arithmetic`).

**Status of the criterion.** Combining with rung 0: RH holds iff a Hermitian form built from
`M₁`, two pole terms, two `Γ_ℝ` terms and two von Mangoldt series is positive semidefinite over
finite families of below-strip base points. The zeros have disappeared from the statement entirely;
the only arithmetic input is `Λ(n) ≥ 0`.

**[OPEN CORE — rung 1 proper]** The prime side enters as `Σ_n Λ(n) n^{−1/2}·W_n(c)` for an explicit
weight `W_n` determined by the base points and coefficients. Positivity of the whole form is now the
question of whether the archimedean + pole + `M₁` part dominates that series. Two facts constrain
any attack: (i) `W_n` oscillates (it carries `n^{−iz}` factors), so `Λ(n) ≥ 0` alone gives no sign —
the 3-4-1 mechanism is the classical way to force one, and the corpus already carries the 3-4-1
inequality in `ZetaThreeFourOne.lean`; (ii) 9bn: candidate positivity statements at large support
are documented as DISPROVED in the 2026 literature, so the live question is which coefficient
families survive, not whether all do.

## Rung 1 — the arithmetic primitive [LEAN-PROVED]

`VonMangoldtThreeFourOneSeries.lean`, clean, sorry-free, axioms standard.

**`three_four_one_vonMangoldt`** — for `σ > 1` and every real `τ`,
  `0 ≤ 3·Re L(Λ,σ) + 4·Re L(Λ,σ+iτ) + Re L(Λ,σ+2iτ)`.
Each prime power contributes `Λ(n)·n^{−σ}·(3 + 4cos(τ log n) + cos(2τ log n))`, and the bracket is
`2(1 + cos θ)² ≥ 0` (`three_four_one_cos`). Supporting: `re_natCast_cpow_neg` (real part of a natural
cpow: `n^{−σ}cos(τ log n)`), `re_lseries_term_vonMangoldt` and its real-point case.

This is the corpus's first SERIES-form 3-4-1: `ZetaThreeFourOne.lean` carries only the PRODUCT
inequality `1 ≤ ‖ζ(1+x)³ζ(1+x+iy)⁴ζ(1+x+2iy)‖`. The series form is what a positivity argument on the
Gram can consume, since the Gram entries carry `L(Λ,s)` linearly, not `ζ` multiplicatively.

**Position.** Rung 0 (`riemannHypothesis_iff_outsideStrip_nonneg`) reduces RH to positivity of a
Hermitian form whose entries are, by `xiWeilGramEntry_arithmetic`, explicit in `M₁`, pole terms,
`Γ_ℝ` terms and `L(Λ,s)`. `three_four_one_vonMangoldt` supplies the only known way to force a sign on
the `L(Λ,s)` part: a three-point configuration in arithmetic progression with weights `(3,4,1)`.

**[OPEN CORE]** Whether that configuration can be realised INSIDE the Gram form. Two obstructions,
both concrete: (i) the Gram's prime weight `W_n(c)` is determined by the kernel algebra
(`z'/(z(z−z'))` coefficients), not free — so matching it to `(3,4,1)` is a constraint, not a choice;
(ii) the Gram couples `L` at `z` with `L` at `conj z'`, i.e. at points on OPPOSITE sides of the
strip, whereas 3-4-1 needs three points on ONE horizontal line. Reconciling those is the next
question; a negative answer would be a genuine no-go about this Gram and would send the card to the
failed lane with the exact obstruction.

## Rung 1 — interrogation of the 3-4-1 plan [NO-GO, with salvage]

Worked the compatibility question on paper. Result: **the 3-4-1 configuration CAN be realised in the
Gram, and that does not help.**

**Realisability (positive).** Writing the Gram's `L`-dependence by collecting coefficients,
  `Q(c) = |Σc|²·M₁ − Σ_i α_i L(z_i) + Σ_j β_j L(conj z_j)`,
and using Schwarz reality `L(conj z) = conj(L(z))` (corpus `logDeriv_XiC_conj`) to fold the
above-strip points back to the below-strip ones, the prime part of `Re Q` is
  `Σ_n Λ(n)·W_n`,  `W_n = Σ_i n^{−σ_i}(Im γ_i·cos(τ_i log n) − Re γ_i·sin(τ_i log n))`,
with `γ_i = α_i − conj(β_i)` and `s_i = σ_i + iτ_i`. So the two obstructions feared earlier both
dissolve: the opposite-side coupling is only a conjugation, and the `(3,4,1)` pattern is achievable
by solving `Im γ = (3,4,1)λ`, `Re γ₂ = Re γ₃ = 0` — four real constraints against six free real
coefficients plus the base points.

**Why it does not close (the exact why).** The criterion demands positivity for EVERY finite
configuration. Making the prime side nonnegative for a SPECIAL family proves positivity only for
that family. The hard configurations are exactly those whose prime weight is negative and must be
dominated — 3-4-1 says nothing about them. Classically this is the same fact: 3-4-1 yields a
zero-free REGION, never RH.

**[NO-GO]** `three_four_one_vonMangoldt` cannot close rung 1 by itself, for a reason that is not a
gap in execution: special-configuration positivity is strictly weaker than all-configuration
positivity, and the gap between them is the whole problem.

**Positive salvage (non-trivial).** The criterion used CONTRAPOSITIVELY is exactly a zero-free
region generator: a zero forces some configuration negative (rung 0), while 3-4-1 forces certain
configurations nonnegative; a zero therefore cannot sit where those configurations detect. This
recovers de la Vallée Poussin-type regions from the Gram, and — unlike the classical derivation — it
does so from a criterion that is EQUIVALENT to RH, so the quality of the region is limited only by
how large a family 3-4-1 can certify. That is a well-posed quantitative question and the natural
rung-1′.

**Representation lesson.** Every route that injects `Λ(n) ≥ 0` through a FIXED trigonometric
identity buys positivity on a fixed family. To reach all families the sign must come from a
mechanism that adapts to the configuration — i.e. from the archimedean side dominating uniformly,
which is Weil positivity itself. Recording so the 3-4-1 family is not re-attempted at higher rungs.
