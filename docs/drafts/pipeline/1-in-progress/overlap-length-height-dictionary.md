# Overlap, polynomial length, height, and the complete Weil form

- **ID:** overlap-length-height-dictionary
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** `docs/reports/review-2910/fable2.md`, §1.3.
- **Scope:** Exact dictionary, threshold qualifications, and consequences for the actual complete form.
- **Closeout:** All started drafts and associated paper arguments are formalized and audited. Further conjecture work is paused.

## Formalized results

Each linked card states the exact theorem, paper argument, Lean declarations, and audit status.

| Result | Formalized card |
|---|---|
| `T=X/c`, `c=X/T`, exact bandwidth identities, fixed-overlap bandwidth tending to one | [Coordinates](../3-formalized/overlap-length-height-coordinates.md) |
| Dilation Jacobian, conventional coefficient reweighting, and absence of a hard Fourier cutoff | [Atomic transform](../3-formalized/normalized-atomic-length-height-transform.md) |
| Density-matched paired-lattice agreement exactly at `X²≤T`, with negative-test converse | [Calibrated lattice boundary](../3-formalized/density-matched-length-height-boundary.md) |
| `E_m(c)=E_m(1)-log c` for nonpolar reference conductors; exact crossings and self-error `O(c/N)` | [Ramanujan reference loss](../3-formalized/overlap-forces-new-ramanujan-terms.md) |
| Exact asymmetric logarithmic windows and geometric onset `t_N=N log(1+1/N)→1` | [Successor windows](../3-formalized/exact-successor-shell-windows.md) |
| Census cutoff `(T/(2π))^λ` and physical overlap `(T/(2π))^(λ-1)/(2π)` | [Census coordinates](../3-formalized/census-length-height-coordinates.md) |
| Positive logarithmic weighted successor-fiber growth at every fixed `c>1` | [Divisor fiber](../3-formalized/fixed-overlap-logarithmic-divisor-fiber.md) |
| Actual complete matrix at height `N/c`, with the fixed-reserve positivity range transported exactly | [Complete-form coordinates](../3-formalized/complete-weil-length-height-positivity.md) |
| Super-Gevrey overlap diverges, bandwidth tends to one, and `N~T_N c(T_N)` | [Steklov height substitution](../3-formalized/super-gevrey-length-height-dictionary.md) |
| Positive actual prefix at `cM/N≤1`, exact Schur equivalence, and positive elimination cost | [Paid-prefix Schur reduction](../3-formalized/a-positive-prefix-gives-the-exact-schur-reduction.md) |
| Gap at least `k≥1` enters at `N log(1+k/N)→k` | [Higher-shell thresholds](../3-formalized/exact-higher-successor-shell-thresholds.md) |
| Actual enclosing aperture `(log N+(b-a)w)/2`, with cutoff `N exp((b-a)w)` | [Profile-width aperture](../3-formalized/atomic-aperture-retains-profile-width.md) |
| Every finite plateau overlap Gram is strictly positive at every positive width | [Finite Gram positivity](../3-formalized/plateau-overlap-gram-is-nondegenerate.md) |
| Growing overlap destroys every uniform coefficient-mass floor; adjacent-vector ratio is `O(c⁻²)` | [Gram degeneration across horizons](../3-formalized/growing-overlap-has-no-uniform-gram-floor.md) |
| Actual successor-fiber positivity iff `t_N<c`; at touching it is positive but `O(log N/N²)→0` | [Open threshold and touching decay](../3-formalized/successor-fiber-open-threshold-and-touching-decay.md) |
| Support normalization multiplies overlap by `b-a` and preserves the complete form and masses | [Profile normalization](../3-formalized/profile-normalization-preserves-complete-form.md) |
| Actual prime-correction action is eventually bounded iff `0<c≤1`; factorial successors force divergence for `c>1` | [Sharp Euclidean boundary](../3-formalized/factorial-successors-force-unbounded-prime-corrections.md) |

All seventeen leaves passed final direct `lake --old env lean` checks with default limits.
Transitive axiom audits contain only `propext`,
`Classical.choice`, and `Quot.sound`. All programme umbrella imports are wired; no placeholders
or raised Lean limits were introduced.

The [Steklov dependency repair](../3-formalized/steklov-fixed-profile-super-gevrey-receiver.md)
also passed its final direct check and six transitive axiom audits. Its synthesis remainder
retains `dcLogWeight 1=(log 4)^2`; this corrects a fixed mollification constant and preserves
the `β>2` receiver.

## Qualifications on §1.3

The corpus uses the positive Fourier convention. Unnormalized dilation contributes `w`;
the conventional polynomial uses coefficients `√n x_n` at `1/2-iz`. The Fourier window
specifies a decay scale. A nonzero-mass compact profile cannot have a hard frequency cutoff.

Profile support matters: `[a,b]` contributes width `(b-a)w` to the atomic support enclosure.
Normalizing to `[0,1]` changes overlap to `(b-a)c` and height to `T/(b-a)`; symmetric
support `[-1,1]` therefore gives overlap `2c`. This reparametrizes one profile and supplies
no transfer between the distinct plateau and Steklov profiles.

At paired-lattice density `log T/(2π)`, the calibrated model boundary is `X²=T`.
SRT quantifies over all tests in an aperture; the atomic criterion quantifies over a fixed-profile
finite-dimensional family. Its negative witness is not thereby an atomic witness.
Census length also retains its `2π` normalization and its proportion quantifier.

The continued separated reference loses `log c` in each nonpolar conductor. Its identification
with actual quasimode energies beyond separation is not supplied by the scalar identity.
The self-error bound concerns normalized archimedean self-energy, not the entire matrix diagonal.
The transported positivity certificate uses `δ_*=1/107520002048050000`; it is a range of one
fixed-reserve estimate, not a classification or claimed optimum of the actual matrix sign.

The weighted divisor-fiber law and Euclidean prime-correction obstruction are distinct results.
The latter uses the finite-column inequality
`‖A e_(N_Y)‖² ≥ [Cφ(t_(N_Y)/c)/∫φ²]² Σ_(p≤Y)(log p)²/p`, with `N_Y=2Y!-1`.
Neither result determines the complete matrix sign. The paid prefix is a genuine coordinate
block, with every mixed entry retained; additive-edge supports alone do not define such a block.

## Closed no-go routes

Each obstruction has a kernel-checked positive survivor:

- [Identifying atomic touching with the calibrated lattice boundary](../5-failed/identifying-atomic-touching-with-the-density-matched-nyquist-boundary.md): exact agreement and negative-witness classification.
- [An unchanged positive separated reference](../5-failed/an-unchanged-positive-separated-reference-at-growing-overlap.md): exact energy decomposition, crossing law, and actual self-error bound.
- [A uniform coefficient-mass floor at growing overlap](../5-failed/a-uniform-coefficient-mass-floor-at-growing-overlap.md): finite Gram positivity, exact autocorrelation deficit, and quantitative degeneration.
- [Uniform absolute prime-correction payment above touching](../5-failed/uniform-absolute-prime-correction-payment-above-touching.md): finite-column lower bound and sharp boundedness boundary.

## Extensions not established by these results

- Reindex the entire weighted downward row by products `ℓ`, retaining horizon truncation and
  support conditions, then identify its cancellation with the actual archimedean overlap row.
- Locate the factorial-successor obstruction in a precisely chosen mixed prime block; relate it
  to the complete mixed block and inverse-prefix Schur cost.
- Prove the remaining actual Schur sign along overlap schedules sufficient for the receiver.
  A scalar symbol or an entrywise sign does not prove this residual inequality.
- Supply a compatible positivity/completeness profile or a signed transfer between the plateau
  and Steklov families.

These remain conjectural extensions here, without completed paper proofs awaiting formalization.
