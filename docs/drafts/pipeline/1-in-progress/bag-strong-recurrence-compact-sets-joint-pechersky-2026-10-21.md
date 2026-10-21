# BAG — Bagchi's strong recurrence on compact sets: joint Pechersky approximation on disc unions

- **ID:** BAG-strong-recurrence-compact-sets-2026-10-21
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean, in progress)
- **Source:** Receiver `ZetaStronglyRecurrent` (`RHTower/ZetaStrongRecurrenceReceiver`), the disc chain (Pechersky → phased Euler products → Kronecker–Weyl → cutoff uniformity → Carlson tail laws), today's all-disc theorem `riemannHypothesis_iff_zetaDiscRecurrent`.
- **Statement (target):** `RiemannHypothesis ↔ ZetaStronglyRecurrent`: RH holds iff for every compact `K ⊂ {1/2 < Re s < 1}` and every `ε > 0` the shifts `τ` with `sup_K |ζ(s+iτ) − ζ(s)| < ε` have positive lower density.

## Goal

The direction RH ⟸ is in the corpus (`riemannHypothesis_of_zetaStronglyRecurrent`). The direction
RH ⟹ needs a *non-disc universality argument*: every proved universality statement lives in the
Hardy space of one disc, because the Pechersky density lemma is a Hilbert-space statement and the
prime vectors `p^{−s}` are square-summable only on discs inside `Re s > 1/2`. A compact `K` of
the strip need not lie in one such disc (tall compacta). The corpus search (Runge module
`HTGeometry/RungeDensity` approximates by differentially algebraic functions, not polynomials;
analytic logs on balls; `tendstoUniformlyOn_taylorPoly`; `hardyDiskOfAnalytic`) fixes the route.

## Route (joint phases on a finite union of discs)

Cover `K` by finitely many closed discs `D_i = closedBall z_i (ρ_i r₁)` whose doubled discs lie in
the strip (`2ρ_i < min(Re z_i − 1/2, 1 − Re z_i)`), indexed by a finite type `ι`.

1. **Horizontal-extent divergence lemma** (`PrimeSumDivergenceOfHorizontalExtent`). For `Φ ≢ 0`
   entire of any exponential type with `‖Φ(−x)‖ ≤ A e^{bx}` on the negative ray, `b < 1 − σ`, the
   sums `Σ_{p<N} p^{−σ}‖Φ(log p)‖` are unbounded. Mechanism: the sibling cap-free module's ray
   exponent `a` and Phragmén–Lindelöf thin-strip bound are kept; only the floor `a ≥ −ρ` (which used
   the full type) is replaced by `a ≥ −b` from the two-ray theorem applied to `Φ(w)e^{κw}`,
   `κ = (b − a)/2`. The vertical extent of a region then only enters as a constant.
2. **Direct sum of disc Hardy spaces** (`HardyDiscTuplesAndJointPechersky`). `DiscTuple ι :=
   PiLp 2 (fun _ : ι => HardyDisk)`; prime tuples `u_p = (primeTerm z_i ρ_i p)_i`;
   `Σ‖u_p‖² < ∞`; pairing `⟪u_p, e⟫ = F_e(log p)` with `F_e(ξ) = Σ_i exp(−conj(z_i) ξ)·Φ_{e_i}(ξ)`
   entire, negative-ray rate `b = max_i (Re z_i + ρ_i) < 1`. The closed span `H'` of the prime
   tuples is a Hilbert space in which Pechersky's hypotheses hold (if the pairings with `e ∈ H'`
   are summable then `F_e ≡ 0` by 1, so `e ⊥ H'`, so `e = 0`): every `h ∈ H'` is a limit of
   unimodular prime sums, with prescribed initial phases (`exists_unimodular_finite_approx_extend`).
3. **Which tuples lie in `H'`** (`ExponentialTuplesAndPolynomialMembership`). For real `ξ` the
   tuple `E_ξ` of `s ↦ e^{−sξ}` pairs with `e` to `F_e(ξ)`; so `e ⊥ H' ⟹ F_e ≡ 0 ⟹ e ⊥ E_ξ`, hence
   `W := closure span{E_ξ : ξ ∈ ℝ} ⊆ H'`. Finite differences `((e^{−sh} − 1)/h)^k → (−s)^k`
   uniformly on compacts put every polynomial tuple in `W`; Taylor expansion on a large disc puts
   the tuple of every function analytic on a large disc containing the doubled discs in `W`.
4. **`log ζ` lies in `H'`** (`LogZetaTupleLiesInPrimeSpan`). Under RH, `(s−1)ζ(s)`
   (`zetaPoleFilled`, entire) has no zero on `Re s > 1/2`, so it has an analytic log `ℓ` on a disc
   `D(c₁, R₁) ⊂ {Re > 1/2}` containing the doubled discs (centre far to the right); `log(1−s)` is
   analytic on `{Re < 1}`, hence on a disc `D(c₂, R₂)` containing them (centre far to the left).
   `L := ℓ − log(1−s) − iπ` satisfies `exp L = ζ` near the discs and its tuple is in `W ⊆ H'`.
   This is where Runge is avoided: the target is a sum of two functions each analytic on a
   half-plane, and a compact of a half-plane lies in a disc of that half-plane.
5. **Bridge, Kronecker–Weyl, uniformity, tail law on the union**
   (`EulerProductsApproximateZetaOnDiscUnions`, `UniformEulerTargetDensityOnDiscUnions`,
   `ZetaStrongRecurrenceOnCompactSets`): the disc proofs run componentwise with the joint phases;
   the random block sum is controlled on every disc at once by a union bound (Chebyshev with
   `Σ_i E‖S_i‖² ≤ δ²/2`); the tail law on the union is the finite-cover law
   `eventually_eventually_volume_eulerDiscTailBadSet_le_of_lt` per disc; `zetaReturnSet K ε ⊇
   zetaReturnSet (⋃ D_i) ε`.

## Gates
- [x] 0 → 1  in-progress: well-posed, route fixed by corpus search
- [ ] 1 → 2  paper proof complete (the route above; details in the module docstrings)
- [ ] 2 → 3  Lean: modules 1–7 compiled, wired, axioms standard
- [ ] 3 → 4  not pursued (user rule)

## Log
- 2026-10-21 — created after the all-disc theorem; corpus searched (no polynomial Runge, no
  direct-sum Pechersky, no compact-set universality); route fixed.
