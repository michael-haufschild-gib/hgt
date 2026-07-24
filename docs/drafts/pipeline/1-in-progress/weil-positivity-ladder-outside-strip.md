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
