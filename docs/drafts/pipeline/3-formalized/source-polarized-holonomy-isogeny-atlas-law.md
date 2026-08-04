# Source-polarized holonomy-isogeny atlas law

- **ID:** `source-polarized-holonomy-isogeny-atlas-law`
- **Stage:** 3-formalized
- **Type:** POSITIVE CROSS-ROUTE CLASSIFICATION / NO-GO
- **Statement:** Route R's prime/depth graded-`det₂` anomaly, Route L's source-dagger mate
  monodromy, and the actual CCM cofinal Bockstein readout are finite-isogenous presentations of
  one positive horizontal character.  They have the same critical-line radical and cannot supply
  independent charts in a parallel source atlas.

## Public sentence

Route count is not atlas rank: R, L, CCM, and the graded correction are four coordinate systems on
one obstruction.

## Theorem

For an ordinary prime `p`, centered rate `a_s=2 Re(s)-1`, and the first three Wold depths, define

```text
A_p(s) = primeDepthBVWoldGradedDet2Anomaly a_s (p,0) (p,1) (p,2),
delta_p(s) = exp(a_s log p).
```

Then, unconditionally,

```text
Area((p,0),(p,1),(p,2)) = -(1-p^(-1))^3 log p,
A_p(s) = exp(a_s (1-p^(-1))^3 log p),
A_p(s)^(p^3) = delta_p(s)^((p-1)^3),
A_p(s)=1 iff delta_p(s)=1 iff Re(s)=1/2.
```

At `p=2`,

```text
A_2(s)^8 = delta_2(s).
```

More generally, if `A_(p,e)` is the correction on consecutive depths
`(p,e),(p,e+1),(p,e+2)`, then

```text
Area_(p,e) = -(1-p^(-1))^3 p^(-e) log p,
A_(p,e+1)^p = A_(p,e),
A_(p,e+k)^(p^k) = A_(p,e),
A_(p,e)^(p^(e+3)) = delta_p(s)^((p-1)^3),
A_(p,e)(s)=1 iff Re(s)=1/2.
```

Thus Route R depth supplies an unconditional coherent prime-Kummer tower of scalar anomalies.
Increasing depth adds roots but no radical.  This separates it sharply from the divisor-bearing
Kummer tower in `RiemannTower.lean`, whose holomorphic Xi roots detect zero multiplicity and are
equivalent to RH.

Let

```text
C_2(s)=1+A_2(s)+...+A_2(s)^7 > 0.
```

The actual rational-adelic CCM cofinal source-homology readout at clock two satisfies

```text
readout(k,m,s,w,x)
  = (A_2(s)-1) C_2(s) (iteratedDeriv k XiC w) trace(x).
```

Thus Route L/CCM's defect and Route R's anomaly defect have exactly the same radical before Xi
quantification or any limiting passage.

## Relation-kernel transition

Let `tau_p` be the actual nonzero source-pointed Calderón--Witt commutator calibrator and let
`D(s)=xiNearbyPoleDualityAdjunctionFracture(s)=2 Re(s)-1`.  Define the positive source scale

```text
c_(p,e)=(1-p^(-1))^3 p^(-e) log p > 0.
```

The new logarithmic transition law is

```text
log A_(p,e)(s) = c_(p,e) D(s),
c_(p,e) * (D(s) tau_p) = (log A_(p,e)(s)) tau_p,
D(s) tau_p=0 iff A_(p,e)(s)=1.
```

Therefore the relation-kernel route contributes a nonzero coefficient-faithful carrier, not a new
vanishing radical.  Its remaining singular relative arithmetic vanishing law would be genuinely
new; the already constructed calibrator alone does not raise atlas rank.

## Proof

Put `q=p`, `b=1-q⁻¹`, `m_e=bq⁻ᵉ`, and `lambda_e=(e+1)log q`.  Direct expansion gives

```text
theta_01 = b log(q)(2-q⁻¹),
theta_12 = b log(q)(3q⁻¹-2q⁻²),
theta_20 = b log(q)(q⁻²-3).
```

Their sum is

```text
b log(q)(-1+2q⁻¹-q⁻²) = -b^3 log(q).
```

The graded-`det₂` anomaly is the exponential of minus centered rate times this area, giving its
closed form.  At depth `e`, the same expansion gains the factor `p⁻ᵉ`; therefore the next anomaly's
`p`-th power is the preceding anomaly.  Raising depth zero to `p³` clears the Wold mass denominator
and yields the stated power of the mate gain.  The real exponential is positive and injective, so
every level has exactly the radical `a_s=0`.  At `p=2`, geometric factorization of `A_2`'s eighth
power gives the positive CCM amplifier.

## Lean realization

Module:
`formal/GaloisForLFunctions/RHTower/PrimeDepthBVWoldSourceDaggerAtlasTransition.lean`

Relation-kernel transition module:
`formal/GaloisForLFunctions/RHTower/PrimeDepthBVWoldRelationKernelAtlasTransition.lean`

Main declarations:

- `primeDepthBVWoldConsecutiveIncrementArea_primeTriangle`
- `primeDepthBVWoldConsecutiveIncrementArea_primeConsecutiveTriangle`
- `primeDepthBVWoldPrimeConsecutiveTriangleAnomaly_succ_pow`
- `primeDepthBVWoldPrimeConsecutiveTriangleAnomaly_add_pow`
- `primeDepthBVWoldPrimeConsecutiveTriangleAnomaly_pow_eq_mateGain_pow`
- `primeDepthBVWoldPrimeConsecutiveTriangleAnomaly_eq_one_iff_re_eq_half`
- `primeDepthBVWoldPrimeTriangleAnomaly_eq`
- `primeDepthBVWoldPrimeTriangleAnomaly_pow_eq_mateGain_pow`
- `primeDepthBVWoldPrimeTriangleAnomaly_eq_one_iff_mateGain`
- `primeDepthBVWoldPrimeTwoTriangleAnomaly_pow_eight`
- `primeDepthBVWoldPrimeTriangleAnomaly_eq_one_iff_re_eq_half`
- `primeDepthBVWoldPrimeTwoCyclotomicAmplifier_pos`
- `primeDepthBVWoldPrimeTwoTriangleAnomaly_pow_sub_one_factor`
- `ccmMobiusThetaCofinalSourceHomologyLanding_readout_eq_anomalyFactor`
- `primeDepthBVWoldPrimeConsecutiveTriangleLogScale_pos`
- `log_primeDepthBVWoldPrimeConsecutiveTriangleAnomaly_eq_greenFracture`
- `primeDepthBVWold_logAnomaly_sourcePointedTau_transition`
- `deningerCalderonWittSourcePointedGreenRay_eq_zero_iff_anomaly_eq_one`

Module is imported by `formal/GaloisForLFunctions/RHTower.lean`.

## Novelty audit

### Internal

Exact identifier and formula search found no prior R/L/CCM transition theorem.  Predecessor modules
separately proved Route R triangle curvature/counterboundary, Route L mate monodromy, and CCM
cofinal readout.  This theorem is their first exact all-prime comparison.

### External

- Ponge's para-`S` modules provide the abstract identity `d²=(1-T)S` and perturbation machinery,
  but no arithmetic Wold/`det₂`/Deninger transition or RH source radical.
- Connes--Consani provide cyclic/sheaf realizations of zeta zeros, not this prime-depth isogeny.
- No exact collision was found in the targeted primary-source search through 2026-08-04.

Classification: `[NEW WITH PRECISE PARENTS]`.

## Significance and anti-theatre verdict

This theorem does not assert RH and does not rename an RH equivalence.  It changes merger design:

1. parallel conservativity must be computed after quotienting observations by exact source
   isogeny;
2. R, L, CCM, and graded-`det₂` supply one primitive radical, not four;
3. a successful Frankenstein route needs a transition to a class not generated from
   `p^(2 Re(s)-1)` by powers, nonzero rescaling, completion, or boundary passage;
4. the retired para-`S` proposal failed because its desired periodicity leg was precisely the
   already constructed graded anomaly, while its non-torsion clause hid RH.
5. deeper Wold charts are coherent scalar Kummer roots of the same anomaly, so depth proliferation
   cannot raise primitive atlas rank.
6. a vector-valued nonzero calibrator can improve coefficient provenance without changing the
   radical; atlas rank counts independent annihilation laws, not target dimension.

The resulting proof-design invariant is **source-vanishing rank**, not route count or detector
dimension.  For the presently merged R/L/CCM/relation-kernel family, obstruction rank is one and
proved source-vanishing rank is zero.  Missing theorem must supply a zero for an independent
arithmetic reason and compare it coefficient-faithfully to the already constructed horizontal
carrier.

Remaining viable transverse data are source orientation phase, singular Cartier provenance, and
noncompact cofinal incidence before scalarization.  This restriction is the theorem's downstream
research value.

The active corpus conjecture `DAC_FROBENIUS_COHERENCE_DEFECT_SPECTRUM` proposes a sharper
transverse carrier: failures of local scalar Frobenius homotopies to glue.  The strict identity
`A_(p,e+k)^(p^k)=A_(p,e)` proves that the BV--Wold scalar anomaly tower has zero same-prime
power-associator at every finite depth.  It therefore lies entirely in the scalar Kummer sector
and cannot instantiate that conjectured non-scalar coherence class.  Any successful use of the
coherence-defect program must retain overlap/homotopy provenance not present in scalar anomaly
values.
