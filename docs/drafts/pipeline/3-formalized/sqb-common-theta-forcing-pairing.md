# SQB: literal common-theta scalar pairing

Status: scratch, canonical source, named leaf build, all eight public axiom checks, and formal lint passed. RH and normalized full-Xi native occurrence remain unproved.

Module: `GaloisForLFunctions.RHTower.SelbergThetaCommonForcingPairing`.
Namespace: `RHTower.SelbergThetaCommonForcingPairing`.

## Exact result

Let `P=nativePositive` be the complete positive theta periodization, `W_q=nativeSource q`, `U_q=centered W_q`, and `F_0=-(1/4) centered P`. Let `h_q=heightProfile q` be the literal reflected-pair half-density, `z_q=xiSpectralPoint q`, `M=sourceMass`, and `V=<constantVector,constantVector>`.

One fixed real weight, independent of the Xi copy, is

    J(y) = integral_[0,1) positiveSource(x+iy) dx.

`horizontalWeight_pos` proves `J(y)>0`. The complete positive source is globally bounded, and the horizontal integral is admitted. Define

    S(q) = integral_(0,infinity) y^-2 h_q(y) J(y) dy.

`scalarResponse_integrable` proves absolute integrability of this displayed expression. The native pairing and its true constant-mode correction are

    <P,W_q> = S(q),
    m(q)=<F_0,U_q> = -1/4 [ S(q) - M^2 / ((1+z_q^2)V) ].

These are `nativePositive_inner_source` and `sourcePairing_eq_scalarResponse`. They use the actual native vectors, their almost-everywhere representatives, and the original modular measure. The weight retains every primitive row of the positive source. It is not replaced by a single cusp row or a different theta dilation profile.

## Dependency-closed analytical proof

1. The existing positive theta source is bounded on the modular fundamental domain. Every point has a modular translate in that domain. Exact invariance therefore extends the same bound to the whole upper half-plane.
2. The actual common-forcing height profile has every power bound. Its quadratic bound near zero and constant bound at infinity admit its integral over the complete hyperbolic strip.
3. Multiplication by the globally bounded positive theta field admits the complete strip product. Integer-translation invariance and the existing absolute half-row integral theorem justify unfolding. The periodized product is exactly `W_q P`, because the positive field is modular invariant. No row is omitted.
4. Strip Fubini separates the actual horizontal weight J from h_q. Product-space integrability also proves that the resulting scalar height integral is absolutely integrable.
5. The native L2 representatives identify the scalar integral with `<P,W_q>`. The original mean laws give `<1,W_q>=M/(1+z_q^2)` and `<1,P>=M`. Orthogonality of `centered W_q` to the true constant vector eliminates the left constant component, while expansion on the right retains exactly the displayed correction.

## Join to the full native Gram

The previously audited common-forcing Gram law is

    (e_r-conj(e_q)) G(q,r) = m(r)-conj(m(q)).

The new theorem identifies its scalar input with an admitted integral of the literal theta profile against one fixed positive weight. Off reflected energy collisions, substitution determines the two-variable native response Gram from these scalar integrals. The previous complete packet formulas then retain every vector/image and forcing cross term. At collisions, the cleared Gram identity remains in force; no confluent Gram value is asserted.

The missing mathematical input is an estimate on these actual complex integrals, including the finite-volume subtraction, that yields native packets with vanishing residual after normalization. Positivity of J does not assert a sign for the complex response S(q). No such packet sequence, centered-vector nonvanishing result, or RH conclusion is claimed here.

## Corpus search contribution

Broad OR searches covered covariance/correlation signs, Herglotz formulas, Sturm/total-positivity mechanisms, spectral measures, and horizontal means. The useful composition is the modular reduction theorem `ModularGroup.exists_smul_mem_fd`, the already closed theta power bounds and modular invariance, and `modularStrip_integral_halfRow_sum` with strip Fubini. It avoids introducing an equal-Gram hypothesis.

The located total-positivity/Laguerre-Polya results did not supply an unconditional sign for this native pairing. The positive raw-theta moment covariance and the real-axis Suzuki Herglotz carrier concern other kernels; their identifications with the present integral were not established. Earlier partial semantic coverage remains a search limitation, not evidence of absence from the corpus.

Reproducible query snapshots: `/tmp/sqb39_scalar_search.json`, `/tmp/sqb39_total_positive.json`, `/tmp/sqb39_spectral_pairing.json`, `/tmp/sqb39_mean_search.json`. Source-text discovery also followed every file directly mentioning `thetaCuspFullSource`, with sign-related hits retained in `/tmp/sqb39_theta_signs.txt`.

## Verification

All eight public declarations were audited.

- `lake env lean /tmp/sqb39_pairing.lean`: passed.
- `lake env lean GaloisForLFunctions/RHTower/SelbergThetaCommonForcingPairing.lean`: passed without diagnostics (`/tmp/sqb39_source_check.log`).
- Named preflight `lake build GaloisForLFunctions.RHTower.SelbergThetaCommonForcingPairing --old --no-build`: only the new leaf was stale (`/tmp/sqb39_preflight.log`).
- `lake build GaloisForLFunctions.RHTower.SelbergThetaCommonForcingPairing --old`: passed; only that leaf built, in 51 seconds (`/tmp/sqb39_leaf_build.log`). Other logged dependencies were cached replays.
- `lake env lean /tmp/sqb39_axioms.lean`: eight outputs, only `propext`, `Classical.choice`, and `Quot.sound` (`/tmp/sqb39_axioms.log`).
- `python3 scripts/formal_tools.py index` and `python3 scripts/formal_tools.py lint`: passed (`/tmp/sqb39_index.log`, `/tmp/sqb39_lint.log`).

No numerical computations, Runpod, added axioms, full builds, or umbrella builds. The finished leaf is wired once into `RHTower.lean`.
