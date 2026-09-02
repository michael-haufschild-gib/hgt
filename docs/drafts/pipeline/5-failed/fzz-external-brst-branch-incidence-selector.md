# Failed route: FZZ external-BRST branch-incidence selector

- **Route:** Use existence or logarithmic monodromy of the marked cigar area OPE against BRST vertices to produce radial divisor-mode passivity.
- **Status:** RETIRED — unconditional Lean no-go.
- **Exact killing theorem:** `not_exists_physical_fzzCigarExternalBRSTBranchCharge_radialSelector`.

## Why it fails

For quantized cigar charges `m=(p-kν)/2`, `mbar=-(p+kν)/2`, the two signed marked branch charges are exactly `(p,-p)`. They are independent of physical radial momentum, `j`, level `k`, and winding `ν`. Hence no predicate of full branch-charge pair selects zero radial momentum; branch incidence is only `p≠0`.

## Strongest positive survivor

The charge-even log-modulus mean is `-2j/(1-2/k)` and reconstructs `j` for `k>2`; odd half-difference is `kν`. Full modulus/on-shell kernels, support motion, and higher replica order remain live.

## Verification

Module `GaloisForLFunctions.RHTower.FZZCigarParityExternalBRSTBranchChargeNoGo` passes direct Lean and targeted build. Key theorems use only `propext`, `Classical.choice`, `Quot.sound`. Umbrella wired. Frontier map unchanged.
