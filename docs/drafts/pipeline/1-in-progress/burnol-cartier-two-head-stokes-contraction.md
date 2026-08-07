# Burnol Cartier two-head Stokes contraction

- **ID:** `burnol-cartier-two-head-stokes-contraction`
- **Stage:** 1 — in progress
- **Route:** R
- **Scientific status:** `[PAPER-PROVED SURVIVOR] [LEAN-PENDING]`
- **Open producer:** pre-divisor Euler--Gamma--Stokes non-amplification of the fixed two-head
  polarization.

## Frontier

The current Route R endpoint asks for separate conservation of the forward aperture-head norm of
the Cartier zero-transfer at every Xi divisor.  Ambient `L²` isometry and extended-Sonin landing do
not imply it: at a hypothetical right-half zero the forward head is strictly amplified.

The new reduction replaces that coordinate equality by a one-sided inequality for a canonical,
fixed, positive source observable.  For aperture `a > 0`, define the head coefficient intrinsically
by

```text
h_a(f) = a⁻¹ ⟨1_(0,a), f⟩.
```

On a constant-head Sonin vector this is its literal head coefficient.  With `C` the cosine
involution, define the fixed two-Gamma-head polarization

```text
E_a(f) = |h_a(f)|² + |h_a(C f)|².
```

No divisor, zero, target metric, or fitted weight occurs in `E_a`.

For the fixed sub-window source atom `f₀`, at `a = 1/2`,

```text
h_a(f₀) = -1,
h_a(C f₀) = -log 2,
E_a(f₀) = 1 + (log 2)².
```

At a right-half Xi divisor `rho`, the already constructed Cartier zero-transfer `U_rho` has

```text
h_a(U_rho f₀)   = -alpha_rho,
h_a(C U_rho f₀) = -(log 2) beta_rho,

alpha_rho = conj(rho)/(1-rho),
beta_rho  = (1-conj(rho))/rho.
```

Writing `x = |alpha_rho|`, `y = |beta_rho|`, the existing exact reciprocal law gives `xy = 1`.
On the open right half of the strip, `x > 1` and `0 < y < 1`.  Hence

```text
E_a(U_rho f₀) - E_a(f₀)
  = x² + (log 2)² y² - 1 - (log 2)²
  = (x-y) (x-(log 2)² y)
  > 0,
```

because `0 < log 2 < 1`.

Therefore the source-native one-sided law

```text
E_a(U_rho f₀) <= E_a(f₀)
```

at every right-half Xi divisor excludes every such divisor.  It implies the existing separate
forward-head norm conservation predicate and hence RH.  Equality is unnecessary; preservation of
one coordinate is unnecessary; a full GNS or same-fibre metric comparison is unnecessary.

## Conjecture / hostile-attack log

1. **Projectively unipotent two-head transfer.** `[FAILED]`  A coefficient-faithful invariant line
   is already classified in the corpus and is equivalent to the hidden coefficient vanishing.
   Rephrasing the transfer as projective unipotence does not produce it.
2. **Ambient isometry intertwines the head projection.** `[FAILED]`  The explicit off-line gain
   disproves this.  Total norm is transferred into tails, so fixed-head commutation cannot follow
   from `L²` isometry or Sonin landing.
3. **Fixed two-head positive contraction.** `[SURVIVES]`  It uses the independent cosine/Gamma
   orientation and asks only for non-amplification of their unweighted positive sum.  Reciprocal
   transfer makes every off-line value strictly expansive.  This is a smaller and more natural
   Stokes producer than separate forward-head conservation.

## Lean target

Create `RHTower/BurnolCartierZeroTransferHeadPolarization.lean` containing:

- canonical forward and cosine head coefficient functions on `soninExtendedSpace a`;
- recovery of literal constant heads;
- exact fixed-atom and zero-transfer polarization values;
- strict right-half two-head amplification;
- a source non-amplification predicate;
- unconditional implication from that predicate to
  `BurnolXiCartierZeroTransferForwardHeadNormConservation` and `RiemannHypothesis`.

The remaining scientific core after formalization is exact and singular: prove this fixed
two-head non-amplification from pre-divisor Euler--Gamma--Stokes structure.  It must not be assumed
from ambient isometry, Sonin membership, critical-line placement, or RH.

