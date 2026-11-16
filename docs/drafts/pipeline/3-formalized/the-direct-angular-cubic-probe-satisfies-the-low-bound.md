# The direct angular cubic probe satisfies the low bound

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Obstacle:** O3; actual low-probe estimate for the angular cubic detector.
- **Lean:** `ProbePhysical.angularCompensatedPhysicalProbe_low` and
  `ProbePhysical.angular_original_ray_compensatedPhysicalProbe_low` in
  `MetaplecticMobiusDescent/Detector/AngularLowProbe.lean`.

## Statement

Fix angular exponent `ℓ : ℕ`, finite Hecke character `η`, admissible excluded primes,
compact annular slot weights of modulus at most one, and smooth compact annular
physical weights. For nonnegative slot lengths with `Σ ellᵢ ≤ 1/6`, every `0<ε<1`
admits `C>0` such that, eventually in `Z`, the actual compensated angular probe at
physical scales `Z^(17/48), Z^(23/48)` satisfies

`|angularCompensatedPhysicalProbe| ≤ C Z^(3/16+256ε)`.

The constant is uniform over supported, pairwise disjoint prime pools outside the
excluded set with norms in `[a Z^ellᵢ, b Z^ellᵢ]`. The ray-pool version follows when
slot lengths are injective. Selected-prime compensation includes the exact phase
`conj(ψ₆(p))^ℓ`. No angular periodicity or conjectural analytic estimate is assumed.

## Proof

1. Higher cusp jets and angular Poisson/Mellin reflection reconstruct the actual
   completed source. Its squared row energy is at most
   `C(1+|θ|)^degree Z^((5/6−2d)+507ε)`. Periodicity is needed only for the finite
   coefficient; the angular factor is handled by reflection.
2. Exact physical-to-ideal identities, finite ray correction and unit-orbit
   normalization give inverse-row mass `C(1+|t|)^degree Z^(507ε/2)`.
3. Mellin separation retains the original radial Gram kernel. Its actual Gram
   inequality yields central compensated tuples bounded by
   `C(1+|t|)^degree Z^(3/16+254ε)`.
4. Gaussian moments sum the central dyads. Arbitrary remote Gaussian decay makes
   the remaining dyads summable with norm sum `O(Z^(-1))`. Total dyad norm is
   `O(Z^(3/16+256ε))`.
5. Exact Gaussian reassembly and the finite compensation-subset sum give the
   stated bound for the direct physical probe. Distinct slot lengths make the
   original ray pools eventually disjoint.

## Scope and verification

This closes the low-range estimate previously blocked by the failure of finite
periodicity under angular twisting. Angular prime-slot estimates, high moment
induction and both common-signal comparisons remain open; no rung seed follows yet.

Every supporting module and the endpoint passed final plain
`lake --old env lean <module>` checks. Modules are umbrella-wired; no umbrella build.
The complete low estimate is one contribution; supporting identities and bounds
carry no separate count. External novelty and axiom checks were skipped as requested.
