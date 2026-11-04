# Signed critical Gamma–center remainder

- **ID:** critical-gamma-center-signed-limit
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** [critical-ratio continuation](../1-in-progress/critical-ratio-continuation.md)

## Exact statement

Fix positive conductors m,l and an admissible compact C² profile φ. Write
a=(∫φ)²/∫φ², L=log N, w=c/N, and v_m for the normalized horizon mode.
For c_N≥1, c_N→∞ and c_N⁴(log N)²/N→0, set

    Z_m = Center(ac)v_m − [m=1]ac v_m
          − separatedCrossError v_m
          + (sqrt(φ(m)))⁻¹ normalizedFullNearGammaDownwardVector_m
          + nearCenterVector_m.

The checked limit is

    (L/c_N) ⟨Z_m,v_l⟩ → a(1−log(4π))[m=1][l=1].

Together with the upward-prime limit −a(γ+1)[m=1][l=1], which enters
the complete residual with a minus sign, this gives the checked complete
coefficient a(2+γ−log(4π)). Neither limit controls growing conductors or
the coupling to the horizon complement.

## Existing inputs

- `TheRowsOfANearPairSum.abs_nearPairSum_sub_le`: periodic averaging for
  arbitrary bounded Lipschitz kernels on a fixed scaled-gap interval,
  with error O(1+log c+c²/N). No new general averaging theorem is needed.
- `abs_mixed_levy_sub_robin_le`: the signed common-window Robin expansion.
- `TheArchimedeanKernelOfNearAtoms`: the actual near pairing has an
  explicit `nearKernel`, an O(w) error, bounded Lipschitz constants,
  and an exact integral. These analytic producers already exist.
- `archimedeanFinitePart_eq`: 2θ′(0)+archRobinConstant=−log(2π)−γ.
- `atomCrossErrorKernel_atomDilate_eq`: the far correction as a signed
  autocorrelation integral against a difference of Gamma densities.
- `exists_profile_crossError_uniform`: a reciprocal-square bound
  Cφ w²/s² for every width w>0 and separated gap s>w.
- `tendsto_centerPairing_sub`: the full center finite part. It contains
  diagonal prime-power terms and a conductor-one receiving column.
- The logarithmic horizon mean, conductor lowering of the divisor jet,
  harmonic Ramanujan sums and the exact rational center kernel.

## Signed cancellation

Put A(s)=shellAutocorr φ s/∫φ², so ∫ℝ A=a, and k=−log(2π)−γ.
The existing normalized near kernel F(s)=nearKernel(φ,s)/∫φ² reads,
on 0≤s≤2 and any common window R≥1+s,

    F(s) = (k−log R)A(s)
           + ∫₀ᴿ (2A(s)−A(s+y)−A(s−y))/(2y) dy.

Extend it evenly and use the same expression for larger s. For s>2,

    F(s) = −(1/2)∫₋₁¹ A(t)/(s+t) dt,
    crossSingular(1/s) = −F(s)−a/(2s).

The required joint integral is

    2∫₀² F(s) ds − 2∫₂∞ crossSingular(1/s) ds
      = −a(log(4π)+γ).

**Available near integral.** `integral_nearKernel` already gives

    2∫₀² F = ka − ∫₋₁¹ A(t) log(2+t) dt.

The matching far integral follows by integrating
1/(s+t)−1/s over 2≤s≤T and taking T→∞:

    2∫₂∞ crossSingular(1/s)
      = a log 2 − ∫₋₁¹ A(t) log(2+t) dt.

The profile-dependent logarithmic integrals cancel exactly. Interchanging
the far integrals is justified by |t|≤1 and the integrable O(1/s²) bound
on their difference. The near integral's proof already handles the
cancelled second difference at y=0.

This integral cancellation and the uniform actual-entry estimate
`|crossError−crossSingular(w/s)|≤(5∫|G|/(2M))w` for s>w are now
kernel-verified in `TheNearAndFarGammaProfilesHaveOneFinitePart.lean`.
The finite-part integral has error at most 2/T before T→∞. Transfer to
the actual growing arithmetic pairings is formalized in
`TheGrowingGammaPairMeanIsPolar.lean`: the raw
near remainder minus separated cross pairing, divided by c, tends to
`−a(log(4π)+γ)δₘ₁δₗ₁` under only c>0, c→∞ and c/N→0. The actual center
transfer and complete residual assembly are also formalized.

**Arithmetic pieces.** After scaling by L/c, the limits are:

| Piece | Limit |
|---|---|
| Near archimedean remainder minus far cross correction | −a(log(4π)+γ)δₘ₁δₗ₁ |
| Near logarithmic row | aδₘ₁δₗ₁ |
| Near divisor jet | aδₗ₁ Λ(m)/sqrt(φ(m)) |
| Near center minus log c times near Gram | a(log 2+γ−1)δₘ₁δₗ₁ − a[m=l>1]Λ(m)/φ(m) |
| Full center residual | a centerLimitCoeff(m,l)/sqrt(φ(m)φ(l)) |

The last row is already known. Its nonpolar diagonal and receiving-column
terms cancel the corresponding two rows above. At m=l=1 the constants
sum to a(1−log(4π)).

## Proof mechanism and scope

**Periodic-kernel bridge.** For bounded q-periodic sequences u,v and a
bounded Lipschitz kernel K on [α,β], 0≤α≤β and β>0, let w_N=c_N/N,
c_N>0, c_N→∞ and w_N→0. The existing row estimate gives

    nearPairSum(K,α,β,w_N,N,u,v,1)/c_N
      → 2 mean(u) mean(v) ∫_α^β K.

Indeed, its error divided by c_N is
O(1/c_N + log(2βc_N)/c_N + c_N/N + 1/N), which tends to zero.
Its main term is the product of the periodic Cesàro mean of
u·mean(v)+v·mean(u) and ∫K(s)exp(w_N s/2)ds. The former tends to
2 mean(u)mean(v); uniform convergence of the exponential on [α,β]
gives the latter limit. This is a direct bridge from an existing estimate,
not a new arithmetic cancellation law. The limit is formalized in
`TheGrowingNearPairMeanIsPolar.lean`.

1. Apply the existing near-kernel approximation and periodic pair estimate
   on [0,2] and [2,T]. The far-tail paper bound is
   B² Cφ(16c/T+32c²/N), where |u(n)|,|v(n)|≤B,
   Cφ=152(∫|φ|)²/∫φ², and T≥2. For n<j≤2n, the existing
   cross-entry bound divided by sqrt(nj) is at most
   4Cφw²n/(j−n)². The tail condition forces j−n>Twn, so
   reciprocal-square summation costs at most 8Cφw/T per row.
   For j>2n, the same entry is at most 4Cφw²/sqrt(nj);
   Σ_(n≤N)1/sqrt(n)≤2sqrt(N). Doubling the upper triangle
   gives the stated bound, uniform before T→∞.
   `TheSeparatedGammaTailIsUniformAtGrowingOverlap.lean` formalizes this
   finite bound uniformly in T, c and N.
2. Retain the signed near-center harmonic sum. Its exact logarithmic
   cutoff is H=N(1−exp(−2c/N)), with H/(2c)→1. The ground sum is
   log H+γ−1+o(1); the nonpolar sums tend to −Λ(m).
3. Combine the far integral with the exact vector decomposition.
   The exterior downward row vanishes after division by overlap.

**Exact center reduction.** The existing
`archimedeanCenterKernel_div_sqrt_mul` gives
½(1/|n−j|+1/(n+j)), not merely an approximation. Put d=exp(2w)−1.
For a positive integer gap h, the near pairs are exactly
ceil(h/d)≤n≤N−h; they occur only for h≤H=Nd/(1+d).
Their count differs by at most one from N(1−h/H).
`abs_gapRow_sub_le`, applied to the two endpoints of this interval,
replaces the Ramanujan pair weight by 2[m=l]c_m(h), with an error
independent of h and the endpoints. Thus the difference-kernel part,
divided by N, is

    [m=l] Σ_(1≤h≤floor H) c_m(h)(1/h−1/H)
      + O_m,l((1+log N)/N).

The sum-kernel part is O_m,l(c/N), using the existing near-row
cardinality bound. For m>1, the displayed sum tends to −Λ(m) by
`tendsto_lagHarmonic` and bounded Ramanujan partial sums. For m=1,
subtracting log c leaves log 2+γ−1. This identifies the center constant
without discarding its signed conductor correlations. The exact interval-count estimate,
signed triangular harmonic approximation, and growing-cutoff limit now
are formalized in `TheNearCenterRetainsItsHarmonicFinitePart.lean`.
`TheActualNearCenterHasItsSignedFinitePart.lean` verifies the exact
logarithmic-pair reindexing and the actual center limit.

The `log c` subtraction requires more than convergence of the relative
near-Gram. Its existing shell error is O_m,l(c⁴ log N/N) after division
by c; multiplying by log c is paid by c⁴(log N)²/N since eventually c≤N.
The exact shell remainder is O_m(1+log c), so its contribution is
O_m((log c+(log c)²)/c)→0. This supplies the needed logarithmic accuracy
without interchanging two uncontrolled limits.

**Complete-residual assembly.** The exact seven-channel identity leaves
three replacement terms in addition to the Gamma–center and upward
residues. The ratio-prime bilinear bound becomes O_m,l(1/c). The self
error becomes O_m,l(log N/N). The existing squared pole-error bound
O_m(c¹⁰(log N/N)²), followed by Cauchy–Schwarz against a bounded normalized
conductor vector, becomes O_m,l(c⁴(log N)²/N). Each vanishes under the
stated clock assumptions. The checked Gamma–center limit therefore supplies
the complete fixed-pair coefficient a(2+γ−log(4π)), without an additional
analytic assumption. This assembly now checks with the standard three axioms.

The constant is not inferred from positivity of the low-zero ledger.
Replacing the Gamma finite part by its value at zero frequency would
give the wrong constant. Estimates of the separate absolute values lose
both the finite-part cancellation and the arithmetic receiving column.

`TheGrowingGammaCenterResidueIsSupportedAtThePole.lean` formalizes the
exact vector assembly and the joint limit `a(1−log(4π))δₘ₁δₗ₁`, without
an additional analytic premise.
`TheCompleteCriticalResidueIsSupportedAtThePole.lean` formalizes the
complete seven-channel residual with coefficient
`a(2+γ−log(4π))δₘ₁δₗ₁` on every positive critical ratio. Both endpoints
and all named supporting modules pass their actual-path source audits;
their printed capstones depend only on
`[propext, Classical.choice, Quot.sound]`.

Verdict: `BRIDGE` within the local corpus. The joint limit resolves the
fixed-pair Gamma–center cancellation. The [complete growing low-packet
transfer](critical-low-packet-signed-compactness.md) is
also formalized; complement coupling remains open. No claim of novelty
relative to external literature is made.
