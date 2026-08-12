# Xi horizontal collision charge: quantized endpoint and replication gap

- **ID:** `xi-horizontal-collision-charge-quantized-endpoint`
- **Stage:** 1-in-progress
- **Type:** FRANKENSTEIN BRIDGE / PRODUCER SPECIFICATION
- **Status:** `[PAPER-PROVED ENDPOINT] [LEAN TARGET] [NOT RH]`
- **Target:**
  `formal/GaloisForLFunctions/RHTower/XiHorizontalCollisionChargeEndpoint.lean`

## Conjecture loop

### C1 — a zero-density estimate for horizontal charge proves RH

`[FALSIFIED]` Let `N(T)` be total Xi divisor multiplicity, `N_0(T)` its critical-line part, and
`O(T)` horizontal collision charge.  Even if `O(T)=o(N(T))`, the inequality

```text
N_0(T) >= N(T) - O(T)
```

proves only `N_0(T)/N(T) -> 1`.  A fixed reflected off-line pair contributes a persistent even
charge while still satisfying `O(T)=o(N(T))`.  Monotonicity and integrality do not remove that
finite defect.

### C2 — quantization lowers the required source estimate to a strict two-unit bound

`[PAPER-PROVED]` For the finite positive-height strip divisor `S_T`, put

```text
m_rho = ord_rho(Xi),
H_rho = sum_{z in S_T, Im z = Im rho} m_z,
O(T)  = sum_{rho in S_T} m_rho (H_rho - m_rho).
```

Equivalently, after grouping by ordinates,

```text
O(T) = sum_gamma H_gamma^2 - sum_{rho in S_T} m_rho^2.
```

Every off-line point is accompanied by the distinct point `1-conj(rho)` at the same ordinate and
with the same positive order.  Hence its summand is at least `m_rho`, and

```text
N(T) - N_0(T) <= O(T).
```

The existing strip identity gives

```text
N(T) - N_0(T) = 2 sum_{Re rho > 1/2} m_rho.
```

Thus any off-line zero forces `2 <= O(T)` for every later window.  Conversely RH makes every
height fibre contain its unique critical-line point, so `H_rho=m_rho` and `O(T)=0`.  Therefore

```text
RH <-> forall T, O(T)=0
   <-> forall T, O(T)<2
   <-> forall n : Nat, O(n)<2.
```

The last equivalence is the useful source endpoint: no limiting argument and no simplicity
assumption are needed.

### C3 — positive charge automatically amplifies to positive density

`[OPEN; HOSTILELY UNSUPPORTED]` The alternative route would be a literal Xi-divisor replication
law

```text
O(T0)>0 -> exists c>0, eventually c*N(T) <= O(T).
```

No current corpus theorem supplies it.  Prime-semigroup, Wold, Gamma-six, and moment-neutral
amplifiers replicate source carriers or index blocks, not new Xi divisor points.  Treating those
copies as zeros would be a coefficient-faithfulness error.  Standard zero-density bounds also do
not convert one exceptional zero into positive density.

## Paper proof details

For `rho in S_T`, the exact-height finset contains `rho`; positivity of analytic order gives
`m_rho>0`.  Its critical-line reflection belongs to the same exact-height finset.  If `rho` is
off-line the two points are distinct, reflection preserves order, and therefore
`2*m_rho <= H_rho`.  It follows that `m_rho <= m_rho*(H_rho-m_rho)`.  Summing over off-line points
proves the deficit domination.

For the quadratic identity, `m_rho<=H_rho` gives

```text
m_rho(H_rho-m_rho)+m_rho^2=m_rho H_rho.
```

Summing and grouping the last expression by `gamma=Im rho` yields `sum_gamma H_gamma^2`.

If a right-half box contains a zero, its reflected pair contributes at least two to the off-line
mass, hence to `O(T)`.  This contradicts `O(T)<2`.  Natural cutoffs are cofinal in every finite
height box.  Under RH, the existing horizontal-fibre theorem gives `H_rho=m_rho` pointwise, so all
summands vanish.

## Exact open producer

Prove from a literal prime/Gamma/source identity, without assuming divisor reality, either

```text
forall n : Nat, O(n) < 2
```

or the C3 replication dichotomy.  An estimate `O(T)=o(N(T))` is not enough.

## Gates

- [x] C1 falsified with explicit persistent-even-defect model
- [x] C2 paper proof dependency-closed
- [ ] C2 Lean formalization and axiom audit
- [ ] source-derived strict two-unit estimate or literal divisor replication

