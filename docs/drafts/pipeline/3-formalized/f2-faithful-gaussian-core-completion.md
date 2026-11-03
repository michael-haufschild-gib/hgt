# F2 — faithful Gaussian core completion

- **Stage:** 3-formalized
- **Result:** For every `ε>0` and existing zero-space vector `x∈ℓ²`, the actual Gaussian core sum vanishes Haar-almost everywhere iff every upper-resonance coefficient `x_(2s)` vanishes. The same equivalence holds for its whole-axis Haar `L²` sum and for pointwise vanishing on `a>0`.
- **Scope:** Lower-half-plane coordinates do not enter the sum. Faithfulness supplies neither a bounded inverse nor positivity of the signed reflection form.

## Proof

Write `w=2s`, `r=Re w∈(0,1)`, `y=Im s`. The [two-endpoint estimate](f2-resonant-core-two-endpoint-bound.md) is

`|core_s(a)|≤C(1+y)^N exp(πy/2) min(a⁻¹,a^(1−r))`.

[Whole-axis synthesis](f2-whole-axis-gaussian-mellin-synthesis.md) gives convergence in `L²((0,∞),da/a)` and exact interchange of the actual series with its Mellin integral on `0<Re u<1`. Individual transforms are holomorphic on `r−1<Re u<1`.

Mellin convolution first gives the individual transform on `0<Re u<r`. Clearing the pole factors and applying the identity theorem extends the identity to the common strip:

`Γℝ(w)u(u−1)(w−u)(w−u−1) M(core_s)(u) = 4 symbol(w,u) ξ(u)ξ(w−u)`.

Use the quotient on the right as the continued kernel `K_s(u)`. The point `u=w` is removable; the raw total Gamma expression at that point is not the analytic extension.

On any closed real substrip of `−1<Re u<1`, the numerator after division by `Γℝ(w)` is bounded by `C exp(2πy)`, uniformly in `Im u`. The ingredients are the existing bound of `|ξ(u)|` by its real-axis value, Euler's integral bound for numerator Gamma factors, and reciprocal Gamma strip bounds. On a small ball avoiding all four pole factors, denominator distances have a common positive lower bound. Gaussian damping therefore gives local normal convergence.

Let `U={−1<Re u<1, Im u>0, ξ(u)≠0, ξ(u+1)≠0}`. Removing the two countable zero sets from the open convex upper strip leaves it connected. The Gaussian kernel sum agrees with the literal physical Mellin transform on `U∩{Re u>0}`. Hence vanishing of that transform on the common strip forces vanishing of the continuation throughout `U`.

For a selected resonance `k`, put `q=2k−1`. Then `−1<Re q<0`, and `ξ(q)≠0` by the functional equation and zero-freeness to the right of one. Isolated xi zeros make `U∪{q}` open. After deleting the `k`th term, the same normal-convergence proof applies on this larger domain, so the remaining sum is continuous at `q`. The selected kernel has nonzero residue

`R_k = −2 symbol(2k,q) ξ(q) / (Γℝ(2k) q(q−1))`.

Indeed `2k−q=1`, `ξ(1)=1/2`, and every displayed factor is nonzero. Multiplying the full sum by `u−q` and taking the punctured limit therefore recovers `exp(−ε(Im k)²)x_(2k)R_k`. A zero continuation forces `x_(2k)=0`.

Haar-almost-everywhere vanishing makes every common-strip Mellin integral zero. The existing `L²` representative identity transfers this conclusion to the whole-axis synthesis. The reverse implications follow by termwise vanishing.

## Lean

`RenormalizedIntersectionTheory/MayerScattering/GaussianMellinPoleSeparation.lean`:

- `upperMayerCore_mellin_cleared`, `upperMayerCore_mellin_eq_kernel`.
- `gaussianMellinContinuation_normal`, `gaussianMellinContinuation_differentiableOn`.
- `gaussianPhysicalCore_ae_eq_zero_iff`.
- `gaussianWholePhysicalColumn_tsum_eq_zero_iff`.
- `gaussianPhysicalCore_eq_zero_iff`.

Final individual `lake --old env lean` audit passed without warnings. All seven public theorem audits report only `propext`, `Classical.choice`, `Quot.sound`. Module wired into the RIT umbrella; no umbrella build.
