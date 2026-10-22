# Suzuki projective defect free boundary

- **ID:** `suzuki-projective-defect-free-boundary`
- **Stage:** 3-formalized
- **Type:** THEOREM / SUZUKI SCREW ROUTE / POSITIVE NO-GO SURVIVOR
- **Scientific status:** `[PROVED HERE] [LEAN-PROVED ANALYTIC CORE]`
  `[CANDIDATE NEW SOURCE-SPECIFIC SYNTHESIS] [GENERIC COMPONENTS KNOWN]`
  `[PRIORITY UNVERIFIED] [NOT AN RH PROOF] [NO NUMERICAL EVIDENCE]`
- **Primary source:** Masatoshi Suzuki, *Weil's quadratic form via the screw function*,
  arXiv:2606.09096v1 (2026), Theorem 1.5 and the discussion after Corollary 1.6.
- **Statement:** The far-negative end of Suzuki's shift space has a universal projective free
  representative which converges locally uniformly to the zero Schur carrier.  Common source
  scaling is invisible, the normalized two-defect Gram state has exact even/odd eigenweights,
  and source parity uniquely selects the odd and even extension phases.  The arbitrary-shift
  no-go therefore exposes a concrete boundary stratum and a canonical ground-centered chart for
  the next noncollapse problem.

## Formal theorem

The free-interval carrier is

```text
Theta_a^free(z)
  =(exp(-2a)-exp(2iaz))/(1-exp(-2a)exp(2iaz)).             (1)
```

For every `eta>0`, the Lean theorem

```text
suzukiFreeLivsic_tendstoUniformlyOn_upperStrip
```

proves uniform convergence to zero on `Im z>eta` as `a -> infinity`.  Consequently

```text
suzukiFreeLivsic_tendstoLocallyUniformlyOn
```

proves

```text
Theta_a^free -> 0
```

locally uniformly on the whole upper half-plane.  The proof uses the exact bound

```text
|Theta_a^free(z)|
 <= 2(exp(-2a)+exp(-2a eta))                              (2)
```

once the denominator is uniformly at least `1/2`.  This is a compact-open theorem, not only a
pointwise limit.

## Projective defect law

For a characteristic pair `(A,E)` and `c!=0`, Lean proves

```text
(cA)/(cE)=A/E.                                            (3)
```

Thus the Livsic carrier depends on the projective defect ray.  If

```text
N=||v_+||_T^2=||v_-||_T^2,
C=<v_-,v_+>_T,
```

the normalized two-channel Gram state has the exact parity eigenweights

```text
p_even=(N+C)/(2N),
p_odd =(N-C)/(2N),
p_even+p_odd=1,
p_even-p_odd=C/N.                                         (4)
```

The formalization proves projective scale invariance of this state, its even and odd eigenlines,
and positivity of both weights under the sharp Gram condition `|C|<=N`.

## Parity phase selection

For Suzuki's one-transform presentation

```text
A_F(z)=(z-i)F(z),
E_F(z)=(z+i)F(-z),
```

Lean proves

```text
A_F(-z)=-E_F(z),
E_F(-z)=-A_F(z),
W_u(-z)=-u W_(u^-1)(z).                                   (5)
```

Therefore `u=1` is the odd member and `u=-1` is the even member.  Conversely, away from the exact
diagonal degeneracies `A=E` and `A=-E`, these phases are unique.  Since the centered target
`z^2 XiC(z)/XiC'(z)` is odd wherever interpreted meromorphically, `(5)` supplies an exact
symmetry-compatible phase selection for any parity-preserving approximation scheme.  It does not
assert that an arbitrary exponential normalization preserves parity.

## Positive survivor and forward route

The no-go is not closed merely by observing that very negative shifts collapse.  Equations
`(1)`--`(5)` identify the strongest positive structure exposed by the failure:

1. the shift end compactifies the carrier moduli by a universal free boundary point;
2. the first anchored defect angle is the polarization `C/N` of a two-state parity Gram law;
3. exact source parity removes the otherwise arbitrary extension phase;
4. for every `tau>0`, the unconditional ground-centered shift

   ```text
   lambda_a^(tau)=lambda_a-tau
   ```

   lies below the spectral floor with exact gap `tau`.

The initially live ground-edge route is now source-specific and measurable:

```text
ground-centered projective resolvents
  -> keep odd leakage through the parity gap nonvanishing
  -> avoid both universal shift boundaries
  -> identify the resulting non-universal limit with the global Xi/de Branges carrier. (6)
```

Uniform noncollapse or limit independence over **all** admissible shifts is false and must not be
used as a premise.  `SuzukiGroundEdgeCayleyUniversality.lean` now proves that approaching a simple
even floor too rapidly forces the other universal boundary, the Cayley map.  The remaining source
problem is the intermediate-window lower bound for the dimensionless odd leakage.

## Lean realization

The unconditional theorem batch is in

```text
formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiProjectiveDefectBoundary.lean
```

with principal declarations

```text
suzukiLivsicQuotient_common_scale
suzukiCharacteristicPencil_common_scale
suzukiFourier_parityPair
suzukiCharacteristicPencil_neg_of_parity
suzuki_odd_phase_eq_one
suzuki_even_phase_eq_neg_one
suzukiNormalizedDefectGram_common_scale
suzukiDefectGram_weight_and_polarization
suzukiDefectGram_weights_mem_unitInterval
norm_suzukiFreeLivsic_le
suzukiFreeLivsic_tendstoUniformlyOn_upperStrip
suzukiFreeLivsic_tendstoLocallyUniformlyOn
suzukiGroundCenteredShift_lt
suzukiGroundCenteredShift_gap.
```

The concrete restricted Weil operator and its resolvent are not represented here.  Hence the
source-specific diagonal negative-shift selection theorem remains at Stage 2 in
`suzuki-negative-shift-defect-escape.md`; this card formalizes the exact dependency-closed
analytic and projective survivor.

## Gates

- [x] strongest positive survivor extracted from the negative-shift no-go
- [x] projective carrier and normalized Gram laws paper-proved
- [x] parity involution and unique symmetry phases paper-proved
- [x] universal free boundary proved in compact-open topology
- [x] unconditional ground-centered chart isolated
- [x] analytic/projective survivor formalized in Lean
- [ ] concrete Suzuki restricted Weil operator and resolvent formalized
- [x] ground-edge universalization classified and strongest positive leakage invariant formalized
- [ ] cofinal intermediate-window leakage lower bound proved
- [ ] specialist priority review
- [ ] RH

## Log

- 2026-07-21 — promoted directly to Stage 3 after the dependency-closed paper proof and exact Lean
  verification of the positive no-go survivor.
