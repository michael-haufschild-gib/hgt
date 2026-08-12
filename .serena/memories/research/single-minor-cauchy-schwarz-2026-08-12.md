# Step 37: quantifier collapse — RH as one Cauchy–Schwarz inequality per polynomial

Card: `docs/drafts/pipeline/1-in-progress/xic-order-one-growth-organ.md` (step 37).

## Theorems (all [LEAN-PROVED], RHTower namespace)

- `forall_level_criticalLine_of_weighted_turanMinors_even`
  (`RHTower/XiResolventEvenTuranMachine.lean`): the level-cleansing machine runs on the
  even-index weighted Turán minors alone. Parity-robustness: `Re u > 0` for every resolvent
  point kills `V = -1` on the level, so `V² = 1 ∧ V ≠ 1` is impossible; odd-power Cesàro sums
  `Σ V^(2n+1) = V·Σ(V²)^n` are bounded by `2/‖V²−1‖`; sub-level tail geometric with ratio
  `(ρ₂/ℓ)²`.
- `xiPolyMoment_X_pow_mul` (`RHTower/XiResolventSingleMinorCriterion.lean`):
  `M_{X^m·p}(k) = M_p(k+2m)` — the polynomial quantifier regenerates the even minor ladder
  from the single index-0 minor.
- `riemannHypothesis_iff_forall_polyTuranMinor_zero_re_nonneg` (same file): at one shift
  `X ≥ 0`, RH ⟺ ∀ p : Polynomial ℝ, 0 ≤ Re(M_p(0)·M_p(2) − M_p(1)²). One inequality per
  polynomial; the ∀n of step 36 is gone.
- `riemannHypothesis_iff_forall_polyCauchySchwarz`
  (`RHTower/XiResolventTraceCauchySchwarz.lean`): RH ⟺ ∀ f g,
  0 ≤ Re(L(f·f)·L(g·g) − L(f·g)²) with `L p = Σ'_q u_q·p(u_q)` (`xiPolyFunctional`).
  Lagrange pair identity `2(L(f²)L(g²) − L(fg)²) = Σ' u₁u₂(f₁g₂ − f₂g₁)²`; backward via
  `g := X·f` recovering `(M_p(0), M_p(1), M_p(2))`.

## Significance

Sign-blind criterion: negating L preserves all minors, so detection is descent oscillation,
not measure positivity — structurally outside the Hamburger/Weil positivity-on-squares genre.
Literature has Turán inequalities for ξ only as necessary conditions; Li/Sekatskii one-point
criteria are linear. [CANDIDATE NEW SCIENTIFIC KNOWLEDGE] provisional.

## Lean traps (new this step)

- `field_simp` cannot reconcile `ℓ^(n*4)` with `ℓ⁻¹^(n*2)` (symbolic exponents): pre-split
  powers to matching atoms via `← pow_mul`/`← pow_add` first; then `field_simp` closes fully
  (drop trailing `ring`).
- `norm_num at h` expands `Complex.mul_re`; to normalize only Nat indices use
  `simpa only [Nat.zero_add] using h`.

## Next frontier

(a) supply the inequality for concrete p (p = 1 first: `Re(R₀R₂ − R₁²) ≥ 0`);
(b) quantitative descent via Turán power-sum bounds → finite jet certificates for partial RH;
(c) Lean counterexample that plain minors cannot detect below the geometric mean of two
higher real atoms (sharpness of the polynomial quantifier).
