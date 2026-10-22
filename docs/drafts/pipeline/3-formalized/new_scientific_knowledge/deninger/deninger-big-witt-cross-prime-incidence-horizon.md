# Deninger Big-Witt cross-prime incidence horizon

- **ID:** deninger-big-witt-cross-prime-incidence-horizon
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Route L, canonical big-Witt codiagonal and all-cross-prime Calderón--Witt incidence
- **Statement:** Reciprocal-prime Teichmüller codiagonals canonically generate a square-summable all-prime incidence horizon with coefficient `1/(pq)`; completed Xi Green provenance lies in its exact Koszul kernel, and actual Gamma admission has critical-line radical at every prime-pair coordinate.

## Goal

Remove a synthetic choice from Route L. Existing all-cross-prime incidence exactness used
`2^(-Encodable.encode i)` only to manufacture a full-support `ℓ²` horizon. That construction was
correct but did not explain its coefficients from Euler/Witt source arithmetic. It therefore
could not certify ordinary-prime coefficient provenance or recover the Gamma-six `1/6` atom in
the literal completed comparison.

The present theorem replaces that enumeration-dependent horizon by one forced by canonical
big-Witt multiplication:

```text
η(p,q) = [1/p] ⊙ [1/q] coefficient = 1/(pq),    p≠q.
```

It pushes this exact source through completed Xi incidence, its Koszul differential, and the
existing actual Gamma-admission operator. It does not prove that the physical Gamma boundary is a
source boundary, preserve the complete Gamma-six trace-class remainder, or prove RH.

## Gates

- [x] 0 → 1 in-progress: synthetic-choice defect isolated; reciprocal-prime source proposed
- [x] 1 → 2 fully-proven: complete proof below, `[PROVED HERE]`
- [x] 2 → 3 formalized: `DeningerBigWittCrossPrimeIncidenceHorizon.lean`
- [ ] 3 → 4 publication-ready: external novelty audit and paper integration

## Theorem `[PROVED HERE]`

Let

```text
I = {(p,q) : p,q ordinary primes and p≠q}.
```

For `i=(p,q)`, define in the canonical big-Witt ring over `ℚ`

```text
face(p) = 1/p,
ω_i = [1/p] + [1/q] - [1/p+1/q],
u_i = 1/(pq),
v_i = 1/p+1/q.
```

Then:

1. `gh₁(ω_i)=0`, `ω_i≠0`, and

   ```text
   (1-v_i T)(S(ω_i)-1)=u_i T².
   ```

2. The raw prime-pair field `η⁰_i=u_i`, embedded in `ℂ`, belongs to `ℓ²(I)`, has no
   zero coordinate, and satisfies `η⁰_(2,3)=1/6`. Its unit normalization `η` is also
   full-support.
3. On the completed all-divisor packet

   ```text
   P = ℓ²(Div(Ξ); ℓ²(I)),
   ```

   the raw comparison

   ```text
   (Φ_W x)(r,i)=x(r)/(pq)
   ```

   is continuous, injective, and has the same closed range as the normalized isometric
   comparison.
4. With base pair `i₀=(2,3)`, define

   ```text
   (∂_W z)_i = η(i₀) z_i - z_(i₀) η_i
   ```

   and apply it fibrewise as `Δ_W`. Then

   ```text
   ker ∂_W = ℂη,
   ker Δ_W = range Φ_W,
   Δ_W(Φ_W(Green(ℓ)))=0
   ```

   for every completed arithmetic source primitive `ℓ`.
5. Each completed source coordinate decodes to the actual ordered Calderón--Witt witness:

   ```text
   SourceValue(r,i,Φ_W x) = (x(r)/(pq)) w_(p,q).
   ```

6. For arbitrary completed Green provenance `a`, actual Gamma admission is

   ```text
   A_Γ(Φ_W Green(a))(r,i)
     = κ(r) H(a,r) /(pq),
   ```

   where `κ(r)≥0` is the already proved quadratic Gamma--Green mate curvature and `H` is
   oriented Hodge transport. For the fixed reflected Gaussian, `H≠0` and `1/(pq)≠0`; hence,
   at every individual ordered prime pair,

   ```text
   A_Γ(Φ_W Green_Gauss)(r,i)=0  ↔  Re(r)=1/2.
   ```

Every statement is unconditional. No zero-location, RH, positivity premise, target-selected
weight, or added axiom occurs.

## Proof

### Big-Witt source

The arbitrary-ring codiagonal theorem gives, for all `a,b`,

```text
gh₁(C(a,b))=0,
(1-(a+b)T)(S(C(a,b))-1)=abT²,
C(a,b)=0 ↔ ab=0.
```

Take `a=1/p`, `b=1/q`. Ordinary primes are nonzero in `ℚ`, so `ab=1/(pq)≠0`; all
claims follow. At `(2,3)`, sum and product give `5/6` and `1/6`, and the source is exactly the
Gamma-six Big-Witt Stokes source.

### Square summability

The prime subseries of the convergent `p`-series satisfies

```text
∑_p p^(-2) < ∞.
```

Tonelli/product summability gives

```text
∑_(p,q) p^(-2)q^(-2) < ∞.
```

Restricting to `p≠q` preserves summability. Since
`|η⁰_(p,q)|²=p^(-2)q^(-2)`, the raw field belongs to `ℓ²(I)`. Every coordinate is
nonzero; evaluation at `(2,3)` is `1/6`. Its norm is therefore nonzero, so unit normalization is
defined and retains full support.

### Completed comparison and exact Koszul kernel

Multiplication by the unit vector `η` defines an isometry
`x ↦ (r ↦ x(r)η)`. Multiplying this map by `||η⁰||` gives the raw comparison and
cancels normalization pointwise, leaving exactly `x(r)/(pq)`. Its norm is
`||η⁰|| ||x||`, so it is injective; the nonzero scalar shows raw and normalized ranges
coincide.

If `∂_W z=0`, the `i`-coordinate equation is

```text
η(i₀)z_i=z_(i₀)η_i.
```

Because `η(i₀)≠0`,

```text
z=(z_(i₀)/η(i₀))η.
```

The converse is immediate. Fibrewise application gives the global kernel. Coordinate evaluation
is contractive, so the residual coefficient
`z(r,i₀)/η(i₀)` remains in the outer `ℓ²` space. This proves exactness. Completed Xi
Green descent follows by substituting its coefficient vector into the raw comparison.

### Actual source values and Gamma radical

The existing normalized arithmetic incidence coordinate sends the actual witness `w_i` to one.
The raw comparison formula therefore decodes exactly to `x(r)/(pq) w_i`, preserving every
ordinary-prime label.

Existing Gamma admission acts fibrewise by the normalized actual Gamma boundary coefficient. The
proved Green provenance factorization expresses that coefficient times Green provenance as

```text
κ(r) H(a,r).
```

Multiplying the raw coordinate adds exactly `1/(pq)`. For the reflected Gaussian, `H(a,r)` is
nonzero at every divisor copy, and `1/(pq)` is nonzero at every prime pair. Thus the product
vanishes exactly when `κ(r)=0`; the previously proved curvature radical is exactly
`Re(r)=1/2`.

## Conjecture loop and failures

1. **Use existing all-prime packet unchanged.** Failed source-purity audit: its
   `2^(-Encodable.encode i)` coefficients depend on a countability encoding, not Euler/Witt
   arithmetic.
2. **Normalize reciprocal coefficients first and identify `(2,3)` with `1/6`.** Failed exactness
   audit: normalization rescales the physical coefficient. Retained both carriers and made the
   raw comparison authoritative; only its range is identified with the normalized Hilbert copy.
3. **Claim packet Koszul exactness as new.** Failed corpus novelty audit: exactness already exists
   for the synthetic horizon. New theorem instead proves source-derived coefficients, exact raw
   source values, and Gamma radical.
4. **Reciprocal Big-Witt horizon.** Survived. It is square-summable, full-support, source-derived,
   exact at `(2,3)`, and compatible with completed Green and actual Gamma admission.

## Novelty boundary

Big-Witt rings and Teichmüller multiplication are classical; compare Rabinoff,
[*The Theory of Witt Vectors*](https://arxiv.org/abs/1409.7445), and Cuntz--Deninger,
[*Witt Vector Rings and the Relative de Rham Witt Complex*](https://arxiv.org/abs/1410.5249).
Square summability of reciprocal-prime products and rank-one Koszul kernel algebra are elementary
once the coefficient law is known. No novelty is claimed for those ingredients separately.

Targeted corpus and arXiv searches found no prior construction joining reciprocal-prime
Teichmüller codiagonals, completed Calderón--Witt incidence, and Gamma/co-Poisson mate curvature.
New candidate content is the source-forced replacement of an enumeration-dependent horizon and
the resulting coordinatewise Gamma radical with exact `1/(pq)` provenance. External novelty
verification remains required.

## Hostile audit

- **Not RH.** The Gamma radical theorem says annihilation is equivalent to critical-line support;
  it does not prove annihilation from a source boundary.
- **Not a renamed predecessor.** Predecessor used arbitrary `Encodable.encode` weights. This
  theorem proves literal reciprocal-product coefficients and recovers `1/6` before normalization.
- **No coefficient erasure.** Raw comparison, exact source-value formula, and kernel range retain
  completed Xi coefficients and every ordered prime label.
- **No hidden divergence.** `ℓ²` summability uses the convergent prime-square series; no
  reciprocal-prime `ℓ¹` assertion occurs.
- **Actual frontier movement.** Ordinary-prime and Gamma-six coefficient provenance is now closed
  through incidence and Gamma admission. Remaining hard theorem is source-null-homotopy of this
  exact Gamma-admitted class through the complete trace-ideal-preserving target square.

## Lean certificate

File:
`formal/GaloisForLFunctions/RHTower/Deninger/DeningerBigWittCrossPrimeIncidenceHorizon.lean`

Capstone:
`RHTower.DAC_DENINGER_BIG_WITT_ALL_CROSS_PRIME_INCIDENCE_DESCENT`

Key declarations:

- `deningerBigWittCrossPrimeStokesSource_green`
- `summable_norm_sq_deningerBigWittCrossPrimePacketRawCoefficient`
- `deningerBigWittCrossPrimePacketRawHorizon_two_three`
- `deningerBigWittRawAllCrossPrimeXiIncidenceComparison_apply`
- `deningerBigWittAllCrossPrimeXiIncidenceSourceValue_rawGreen`
- `ker_deningerBigWittGlobalPacketKoszulDifferential_eq_rawRange`
- `deningerCalderonWittAllCrossPrimeGammaAdmissionOperator_bigWittGreen_apply_eq_mateCurvature`
- `deningerCalderonWittAllCrossPrimeGammaAdmissionOperator_bigWittReflectedGaussian_eq_zero_iff`

All are closed theorems over existing concrete source and target objects. No missing mathematical
premise is packaged as a structure field.

Verification:

- `lake env lean GaloisForLFunctions/RHTower/Deninger/DeningerBigWittCrossPrimeIncidenceHorizon.lean`
  passed.
- Targeted
  `lake build GaloisForLFunctions.RHTower.Deninger.DeningerBigWittCrossPrimeIncidenceHorizon` passed;
  no umbrella or full build was run.
- Axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`.
- Repository lint reports no issue in either new Big-Witt module and confirms umbrella
  reachability. It exits nonzero only on unrelated concurrently unwired modules.

## Log

- 2026-08-15 — conjecture loop, paper proof, source-specific novelty audit, and Lean
  formalization completed.
