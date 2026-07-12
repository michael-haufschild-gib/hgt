# M-free telescope right-half divisor localization

- **ID:** `mfree-telescope-right-half-divisor-localization`
- **Stage:** 3-formalized / not-new
- **Type:** THEOREM (paper + Lean), `[PROVED]`
- **Lean:** `formal/GaloisForLFunctions/RHTower/MFreeTwinNoGo.lean`
- **Sources:** `mfree-telescoping-tower.md`, `../../1-in-progress/multiplicity-parity-ladder-route.md`

## Theorem

For the dyadic scalar telescope define

```text
F_k(s) = zeta(2^k s) / zeta(2^(k+1) s).
```

On `Re s > 1/2`:

1. `F_0(s)=0` exactly when `zeta(s)=0`;
2. `F_k(s) != 0` for every `k>=1`;
3. every finite subproduct avoiding rung zero is zero-free;
4. at a zeta zero, every finite subproduct containing rung zero vanishes.

Therefore every finite partition of the dilation rungs places the entire right-half zeta divisor in
the unique block containing rung zero.  Even/odd depth splitting, mixed-radix regrouping, and scalar
telescope rearrangement cannot produce equal-divisor arithmetic twins or a nontrivial projective
Weyl commutator on the local zero space.

## Proof

If `k>=1` and `Re s>1/2`, then

```text
Re(2^k s) > 1,
Re(2^(k+1) s) > 1.
```

Both zeta values are nonzero in the Euler half-plane, so `F_k(s)` is nonzero.  At `k=0`, the
denominator `zeta(2s)` is nonzero for the same reason, hence the quotient vanishes exactly with its
numerator.  The finite-product statements follow because a product over complex numbers vanishes
exactly when one factor vanishes.

## Positive statement from the no-go

The telescope is not merely unsuccessful; it proves a necessary architecture:

> Every successful twin or projective channel must contain unscaled prime data.  Stratifying Euler
> data by dilation depth is maximally one-channel, because every positive-depth rung is a unit on the
> entire RH half-plane.

Thus the surviving variants must mix primes horizontally at the original spectral scale—through
non-diagonal convolution, character/metaplectic channels, or an all-prime incidence action—rather
than distribute them vertically among scaled zeta copies.

## Formal surface

- `dyadicMFreeZetaRung`
- `dyadicMFreeZetaRung_ne_zero`
- `dyadicMFreeZetaRung_zero_iff_base`
- `dyadicMFreeZetaSubproduct_ne_zero`
- `dyadicMFreeZetaSubproduct_eq_zero`
- `dyadicMFreeZetaTower_divisor_localizes`

## Verification

`lake env lean GaloisForLFunctions/RHTower/MFreeTwinNoGo.lean` passes on the repository toolchain.

## Novelty and significance gate

The proof is elementary and not new scientific knowledge.  Its significance is eliminative and
architectural: it closes a large scalar-telescope detour and forces every surviving arithmetic twin
or Weyl construction to mix unscaled prime data in each channel.

## Gates

- [x] 0 -> 1: exact detour and RH-facing failure stated
- [x] 1 -> 2: zero-free/divisor-localization proof complete
- [x] 2 -> 3: formalized and exact module check passes
- [ ] 3 -> 4: not promoted; not new scientific knowledge

