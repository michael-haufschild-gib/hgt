# HB: complete source meromorphy in the original joint L² space

- **Stage:** formalized in Lean 4.
- **RH:** unproved. Original causal outgoing response, physical left pairing, and independent extinction remain open.
- **Result:** the complete continued cusp residual is meromorphic in the norm of the actual joint L² space throughout `Im w ≠ 0`, `|Re w| < 2`. This band contains both fundamental QNMs of every Xi occurrence and overlaps the original Green source chamber.

## Exact theorem

`continuedOriginalSource_allXi_fundamental_meromorphic_germ` proves, for every
Xi copy, either physical source branch, and arbitrary amplitude, at both
fundamental physical QNM frequencies:

```text
continuedCuspResidualL2 is meromorphic with values in the actual joint L² space;
on one punctured frequency neighborhood:
  the complete continued residual is square-integrable;
  originalForcing = fieldWave(continuedExplicitField) + complete residual.
```

No continuation, uniform-bound, endpoint, nonresonance, admission, or RH premise
is supplied to this all-Xi conclusion. The source retains the native squared
remainder, fixed smooth onset, full-square lift, all three original principal
responses, and every cutoff commutator. The source is the residual after the
explicit field is subtracted. Admission of the unrenormalized angular source is
not asserted.

`continuedCuspResidualL2_eq_original` identifies this exact L² class with
`cuspResidualVector` in the original nonreal principal Green chamber.
`continuedCuspResidualL2_original_corridor` constructs a continuous path from
any point of the band to that chamber, with the full source L²-meromorphic at
every point of the path. The explicit path preserves imaginary part and ends
at real part `7/4`. This identifies a source germ; it does not continue the
original causal response operator.

## Dependency-closed proof

Write `s=physicalRate`, `c_i(w)=connection(w,principalFrequency_i)`, and
`S(w)=1+(w-2s) onsetCorrection(2s,w)`. The continued principal difference is
`U_i=continuedTortoiseGreen-radialLift*principalAmplitude_i`.

1. Define the undivided numerator explicitly, before taking any pole value:
   
   ```text
   Uhat_i = (N * restoredHorizonMellin + H * undividedOuterIntegral) * S
            + c_i * radialLift(s,w,a,S) * principalAmplitude_i.
   D_i = -(w-2s)c_i.
   ```
   
   Away from the original denominator zeros, `Uhat_i=D_i U_i`. Its explicit
   first spatial jet equals `D_i U_i'`. Existing actual Gauss-frequency
   holomorphy, first Mellin subtraction, outer-integral holomorphy, and lift
   identities prove both jets frequency-analytic for `Re w>-2`, `Im w≠0`.
   At a pole the analytic numerator's value is given by this formula;
   multiplication of the totalized original quotient at that point is not
   substituted for the analytic value.
2. The same original radial equation gives
   `Uhat_i''=w² Uhat_i+p_i Uhat_i-fhat_i`, with
   `p_i=-horizonCoordinate*m_i(m_i-1)` and
   `fhat_i=-c_i*reducedCoefficient(s,w,a,S)*principalAmplitude_i`.
   The potential is bounded by `A exp(2t)`. The exact native source
   factorization gives `|fhat_i|≤B exp((Re w+2)t)` uniformly on any compact
   nonreal frequency set. Its remaining profile is continuous jointly on that
   set times `[0,1]`, so compactness supplies one `B`.
3. Make the existing horizon energy coefficient explicit as a continuous
   function of `w`, `Uhat_i(-1)`, `Uhat_i'(-1)`, `A`, and `B`, for `w≠0`.
   For `Re w≤0`, the previously proved energy estimate applies directly.
   For `Re w>0`, apply that estimate with free frequency `-w` to the **same**
   solution, potential, and forcing. The ODE is unchanged because `(-w)²=w²`;
   on `t<0` the original source bound is at most
   `B exp((-Re w+2)t)`. The maximum of the two explicit coefficients is
   continuous and proves `|Uhat_i(t)|≤C exp(-|Re w|t)`.
   This changes the estimate only; no opposite-frequency response inverse is
   used.
4. Compact frequency bounds on the actual interior jets bound `C` uniformly.
   At each interior zero of the original denominators, frequency continuity
   extends this same bound from a punctured neighborhood. Multiplication by
   `horizonCoordinate≤4 exp(2t)` gives
   `|horizonCoordinate*Uhat_i|≤4C exp((2-|Re w|)t)`.
   A frequency ball strictly inside `|Re w|<2` has a single positive decay
   margin. Thus one square-integrable exponential dominates the complete
   cleared cutoff family throughout that ball, including its analytic values
   at connection zeros. Actual spatial continuity follows by differentiating
   the undivided endpoint moments; it supplies measurability at those zeros.
5. Prove a complex-parameter dominated theorem in the genuine L² quotient.
   Cauchy's estimate bounds the pointwise derivatives on a smaller ball by
   `(2/R)b`, where `b∈L²` is the common majorant. The complex convex mean-value
   estimate bounds the difference quotients by the same function. Dominated
   convergence applies to the squared difference between each quotient and
   the pointwise derivative. The exact L² norm-square identity therefore
   proves convergence of the actual complex L² slopes. This establishes
   complex differentiability and, locally, analyticity. A restricted-measure
   version requires pointwise holomorphy only on the actual spatial domain
   `t<0`.
6. Apply that theorem to the cleared cutoff and native reduced coefficients.
   Restore `D_i` using meromorphic scalar multiplication in L², with equality
   to the original quotient classes on a punctured neighborhood. The physical
   source pole satisfies `Re(2s)<-2`, so it is outside the band. The actual
   quotient coefficients also belong to L² at their totalized connection-zero
   values: there the original Green moments vanish and the original lift's
   compact radial profile supplies the bound. Hence the defined L² class is
   the actual admitted source throughout the band; its fallback value outside
   admission is never used there.
7. Reuse the corpus's existing continuous bilinear separated-product map.
   Tensor each actual radial class with its original angular L² factor, then
   sum the native remainder and all three cutoff terms. Almost-everywhere
   identities prove equality to the class of the complete original residual.
   Continuous linear maps and finite sums preserve meromorphic germs, giving
   full joint L² meromorphy.
8. The strict Xi strip proves `|Im principalFrequency_i|<3/2` for all three
   principal powers. The path
   `gamma(r)=w+r*(7/4-Re w)`, `0≤r≤1`, remains in the nonreal band and ends in
   every principal chamber. Equality of the continued and original pointwise
   source on the original chamber gives equality of their L² classes.
   Finally the existing unconditional Xi spectral bounds place both
   fundamental QNMs in this band. Intersect its open neighborhood with the
   proved punctured original field-equation germ to obtain the capstone.

## Formal modules

Six leaves under `GaloisForLFunctions/HTGeometry`:

- `HorizonGrowthCoefficient`, `SymmetricHorizonGrowth`
- `L2CauchyHolomorphy`, `L2FamilyCongruence`, `L2RestrictedHolomorphy`, `L2MeromorphicAlgebra`

Twelve leaves under `GaloisForLFunctions/RHTower`, with prefix
`ThetaCuspHawkingBMJointSource`:

- `ClearedPrincipal`, `CompactFrequencyBounds`, `ClearedPrincipalODE`, `ClearedUniformBound`
- `ClearedCutoffMajorant`, `ClearedRadialAdmission`, `ClearedL2Holomorphy`, `ClearedNativeL2`
- `ContinuedBandAdmission`, `RadialL2Meromorphy`, `CompleteL2Meromorphy`, `ContinuationCorridor`

## Validation

Eighteen canonical leaves, 1,284 source lines, and 52 new public theorems passed
individual foreground `lake build <module>` audits in an isolated package
using 4,062 existing dependency oleans. Exactly eighteen new oleans were built.
Every new theorem uses only `propext`, `Classical.choice`, and `Quot.sound`.
All 36 installed olean/ilean artifacts match the audited bytes; all installed
sources also match their audited source bytes. Both area umbrellas are wired,
with no full or umbrella build run.

The generated index was refreshed once. `scripts/formal_tools.py lint
--check-generated` passed, with only existing large-file warnings. No numerical
experiment, computational certificate, new axiom, or admitted proof was used.

## Remaining physical obligation

Construct the continuation of the original causal **joint response**, with its
outgoing radial endpoint and modular cusp prescription retained, and identify
its physical advanced/adjoint left residue against this complete source. The
proved source germ does not construct that inverse, select its continuation
sheet, prove survival of a pole, or determine the physical left-source
projection. An energy inverse chosen independently in the opposite half-plane
still supplies none of those identifications.

The source corridor reaches the original Green convergence chamber. No claim
is made here of a new global L²-holomorphy theorem on the entire unbounded
right half-plane or of a new Bochner-transform identification beyond the
existing causal source theorem's stated domain. The original pointwise source
continuation and existing causal transform identities remain available.

Physical metric and spin-two/AIME reconstruction, independent Hawking-clock
extinction, and RH remain open. Higher overtones require additional endpoint
subtractions. No numerical experiment is indicated by these unresolved
source-domain and physical-pairing obligations.
