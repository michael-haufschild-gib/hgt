# Finite Euler logarithmic counts force roots into the unit disk

- **Stage:** 0-backlog
- **Type:** CONJECTURE
- **Obstacle:** O11

For a finite multiset of local Euler roots `W`, define `bₖ=(1−Σ_{α∈W} αᵏ)/k`. Conjecture: nonnegative real parts of all `bₖ`, `k≥1`, force every root into the closed unit disk. A nonconstant reciprocal multiplier with root-product modulus greater than one would therefore fail a logarithmic count test, in every degree.

**Scope:** polynomial Euler multipliers. Adding new reciprocal denominators contributes positive pole terms to the logarithmic counts and requires a separate continuation audit; this conjecture does not exclude arbitrary rational Euler modifications.

**Corpus connection:** `ZeroConfigurationGeometry.BoundedImagesCertifyPurity.exists_simultaneous_return` gives arbitrarily large simultaneous returns of any finite unimodular family. Apply it to all nonzero root phases. At a common return every root power has positive real part; a root outside the unit disk forces their sum above one. This avoids identifying a largest-modulus layer.

**Required:** audit overlap with existing power-sum purity and Li recurrence theorems; prove the real-part conclusion for finite multisets, including zero roots; identify the resulting coefficients with the actual finite Euler logarithm. No contribution counted before those steps.
