# The critical-Mellin Volterra--Haar filter detects every positive-growth mode

- **ID:** `ccm-critical-mellin-volterra-haar-mode-faithfulness`
- **Stage:** 3-formalized
- **Type:** THEOREM, `[BRIDGE]`, positive filter-faithfulness law
- **Scientific status:** `[PROVED] [FORMALIZED] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Lean module:** `GaloisForLFunctions.RHTower.CCMCriticalMellinVolterraHaarMode`

## Statement

For `w != 0`, the equal-scale adjacent-block integral of the exponential mode `exp(wh)` is

```text
integral_[x-L,x] exp(wh)dh - integral_[x-2L,x-L] exp(wh)dh
 =exp(wx)(1-exp(-Lw))^2/w.                                (1)
```

The error-dependent Volterra response is

```text
V_w(h)=-exp(wh)-(1/2)integral_[0,h]exp(wu)du.              (2)
```

Its adjacent-block response is

```text
integral_[x-L,x] V_w(h)dh - integral_[x-2L,x-L] V_w(h)dh
 =exp(wx) M_L(w),                                         (3)

M_L(w)=-(2w+1)(1-exp(-Lw))^2/(2w^2).                      (4)
```

For every `L>0`,

```text
Re(w)>0  implies  M_L(w)!=0.                              (5)
```

## Lean surface

- `exponentialAdjacentBlock`
- `exponentialAdjacentBlock_eq`
- `criticalMellinVolterraHaarMultiplier`
- `one_sub_exp_neg_mul_ne_zero`
- `criticalMellinVolterraHaarMultiplier_ne_zero`
- `criticalMellinVolterraMode`
- `criticalMellinVolterraMode_eq`
- `criticalMellinVolterraModeAdjacentBlock_eq`

Finite-packet successor:

- `GaloisForLFunctions.HTGeometry.FiniteModalTransfer`
- `GaloisForLFunctions.RHTower.CCMCriticalMellinVolterraHaarFinitePacket`
- `det_criticalMellinVolterraHaarFinitePacket_ne_zero_iff`
- `criticalMellinVolterraHaarFinitePacket_exact_hankel_mode_count`

## Proof

Direct integration gives `(1)` and `(2)`.  Linearity gives `(3)`--`(4)`.  In the open right
half-plane, `w`, `2w+1`, and `1-exp(-Lw)` are all nonzero.  For the last factor, equality
`exp(-Lw)=1` would force equality of norms and hence `-L Re(w)=0`, contradicting `L>0` and
`Re(w)>0`.

## RH relevance

The normalized Chebyshev reduction identifies the remaining rectangular source estimate with this
fixed Volterra--Haar filter.  Equation `(5)` proves that the filter faithfully retains every
positive-growth exponential mode.  Therefore a successful proof must constrain the normalized
Chebyshev source values; it cannot rely on cancellation caused solely by the choice of fixed-width
filter.  The finite-packet successor strengthens this from isolated-mode detection to preservation
of the exact joint Hankel mode count for every finite positive-growth packet with distinct sampled
nodes and nonzero amplitudes.

## Verification

- [x] target module elaborates
- [x] dedicated Lake target builds
- [ ] one-sided subpower lower bound for the actual normalized Chebyshev input proved
