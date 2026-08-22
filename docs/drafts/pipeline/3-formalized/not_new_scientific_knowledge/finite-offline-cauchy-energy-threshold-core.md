# Finite off-line Cauchy energy exceeds four units per zero

- **ID:** `finite-offline-cauchy-energy-threshold-core`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean), `[BRIDGE]`
- **Scientific status:** `[FORMALIZED] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Lean files:** `formal/GaloisForLFunctions/RHTower/FiniteOfflineCauchyEnergy.lean`;
  `formal/GaloisForLFunctions/RHTower/FiniteOfflineCauchyL2.lean`
- **Paper card:**
  `docs/drafts/pipeline/2-fully-proven/not_new_scientific_knowledge/10-euler-gamma-completion/infinitesimal-euler-leakage-cauchy-energy-threshold.md`
- **Statement:** For every nonempty finite packet with multiplicities at least one and horizontal
  displacements `0<a_j<1/2`, its real Cauchy-resolvent Gram energy is strictly greater than four
  times the packet cardinality; all cross terms are nonnegative and the diagonal already supplies
  the threshold.

## Formalized result

Lean defines

```text
C(a,b,delta)=(a+b)/((a+b)^2+delta^2)
```

and proves the exact complex-resolvent identity

```text
C(a,b,delta)=Re((a+b+i delta)^(-1)).
```

For finite data `a_j`, `gamma_j`, and multiplicities `m_j`, it defines

```text
E_off
 =4 sum_(j,k) m_j m_k
    C(a_j,a_k,gamma_j-gamma_k).
```

If every `a_j>0`, every summand is nonnegative and the self-kernel is

```text
C(a_j,a_j,0)=1/(2a_j).
```

Consequently Lean proves the exposed diagonal bound

```text
E_off >= 2 sum_j m_j^2/a_j.
```

If the packet is nonempty, `m_j>=1`, and `a_j<1/2`, it proves the strict global threshold

```text
E_off > 4 card(J).
```

In particular a single off-line zero mode already has energy strictly greater than four.

The analytic companion module defines the actual finite profile

```text
ell(t)=2 sum_j m_j exp(-(a_j+i gamma_j)t)
```

and its conjugate pair integrands.  It proves their integrability on `(0,infinity)`, the pointwise
Gram expansion

```text
conjugate(ell(t)) ell(t)=sum_(j,k) pair_(j,k)(t),
```

and the exact norm identity

```text
integral_0^infinity |ell(t)|^2 dt = E_off.
```

Thus the formal certificate now includes the finite Paley--Wiener/Laplace exponential integral,
not only the algebraic resolvent sum.

## Main declarations

- `transverseCauchyKernel_eq_resolvent_re`
- `transverseCauchyKernel_pos`
- `transverseCauchyKernel_self`
- `finiteOfflineCauchyEnergy_eq_resolventGram`
- `finiteOfflineCauchyEnergy_ge_selfDiagonal`
- `finiteOfflineCauchyEnergy_ge_two_mul_sum_sq_div`
- `finiteOfflineCauchyEnergy_gt_four_card`
- `finiteOfflinePairIntegrand_eq`
- `integral_finiteOfflinePairIntegrand`
- `finiteOfflineProfile_gramExpansion`
- `finiteOfflineProfile_gramIntegrableOn`
- `integral_norm_sq_finiteOfflineProfile`

## Boundary of the certificate

The modules formalize the finite algebraic Cauchy-Gram identity, the explicit exponential-profile
`L^2` identity, and the sharp strip threshold. They do not derive that profile from the
differentiated shifted Xi quotient or prove the open source-side inequality `C_E(0,0)<=4`. Thus
they certify the unconditional finite exclusion implication, not the missing arithmetic upper
bound.

## Gates

- [x] complex resolvent real-part identity formalized
- [x] positivity of every ordered-pair contribution formalized
- [x] exact diagonal lower bound formalized
- [x] strict four-unit-per-zero threshold formalized
- [x] finite exponential profile, pairwise integral, and exact `L^2` norm identity formalized
- [x] RHTower aggregate import added
- [ ] derive the explicit finite profile from the differentiated shifted Xi quotient
- [ ] unconditional Xi-source upper bound `C_E(0,0)<=4`
