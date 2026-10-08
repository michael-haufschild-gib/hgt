# Critical PBAP: the finite energy left after residue cancellation

Status: OPEN. This records competing conjectures, not a proved sign theorem.

Use the existing `SmoothTest`, `testGamma`, `testPole`, `testMass`, `logVector`
and `SmoothNullPositive` definitions from `WeilWorkPBAPCriticalDatum`.
For a nonnegative finite smooth mixture `c` satisfying the complete **real**
integer-null equation, put

`M(c) = sum_f c(f)*testMass(f)` and
`E(c) = sum_f c(f)*(testGamma(f)+testPole(f))`.

All normalizations below use the actual physical mass and both signed poles.

## Exact competing statements

**S0 (no positive mass margin):** for every real `epsilon>0`, there is such a
mixture with `M(c)=1` and `E(c)<epsilon`.

**S+ (strict mass margin):** there exists a real `epsilon>0` such that every
such mixture satisfies `epsilon*M(c)<=E(c)`.

These are incompatible and exhaustive. A nonnegative mixture of zero mass is
supported only on zero tests and has zero energy. Every positive-mass mixture
can be rescaled to mass one. Hence failure of S0 gives S+, including the zero
mass case. S0 allows a negative witness and therefore does **not** prove PBAP.
S+ would prove smooth-cone positivity, with the extension to the full test
interface still requiring its established approximation argument.

S0 is precisely failure of `SmoothNullPositive 1 1 (-epsilon)` for every
positive `epsilon`. It is the constant-weight part of the old L401 sharpness
program. Verdict on the statement as a proposed new idea: **REDISCOVERED**.
New terminology or a formal wrapper would not move the frontier.

## Hostile audit of the proposed mechanisms

1. **Leading residues.** The audited critical-boundary modules exclude `b>a`
   even with arbitrary constant mass allowance. At `a=b=1` their two limits
   agree and the mass allowance disappears. They decide neither S0 nor S+.
2. **Near-radical tests.** `zeta_weil_margin_superexponential` prices the actual
   von Mangoldt Weil form. Its tests are polar; their integer samples need not
   vanish. Removing the prime contribution is not justified.
3. **Exposing-ray near-minimizers.** `ExposingRayMass.near_threshold_mass`
   exactly matches the nonzero exposing ray. It is not a null-cone theorem.
4. **Small defect repair.** `abs_energy_nullRepair_sub_le` is an actual bound,
   but using it here requires the complete weighted defect budget to vanish
   relative to mass. That has not been proved for a near-radical family.
5. **Joint modulations.** The ten audited Joint leaves force positive energy
   escape near correction mass one for a fixed profile with two real-active
   nodes. They do not produce critical near-minimizers by taking that limit.
   Varying the profile or prime requires uniform control of the explicit costs.
6. **Minimal conductor.** A negative constant mass shift resembles a change
   in the gamma normalization, but classification of ordinary L-functions is
   unavailable until its analytic continuation, functional equation and
   divisor conditions are proved for the actual completion. General real
   weights do not supply integer zero multiplicities or positive Dirichlet
   coefficients. Do not import a conductor classification as a missing premise.

## Next falsifiable strengthening

**S0-repair:** there exist nonnegative finite smooth mixtures `c_k` with
`M(c_k)=1`, `E(c_k)->0`, and
`repairBudget(-defect(c_k))->0`.

This was proposed as a stronger construction mechanism; the audit below rejects
that distinction unless an independent source family is specified.
The actual positive null-repair theorem would make the repaired energies tend
to zero. Its mass must also be controlled: energy control alone does not prove
that repaired physical mass tends to one. At minimum, positivity of repair
preserves the original unit mass, which is sufficient for an upper near-zero
normalized energy bound when that energy is nonnegative; a negative repaired
energy already settles S0. Every individual repair remains finite and exactly
integer-null.

**[OPEN CORE]** Construct `c_k` with both the critical finite energy and the
complete weighted defect budget tending to zero. The bare Riemann-kernel
truncations have no established vanishing defect budget. Neither a support
count nor moment matching without its energy cost supplies this construction.

The converse S0=>S0-repair is tautological if exact-null mixtures are allowed
as `c_k`; thus S0-repair is not a genuinely stronger statement in that broad
form. To gain content, the next cycle must specify a source family independently
of nullness, prove its energy limit, and then prove the defect estimate.
Verdict on the unrestricted reformulation: **CIRCULAR as a construction plan**.
Do not formalize it as new research.

The next substantive target remains the literal full-energy sign. These audits
identify obligations, not reasons to assume either competing conjecture.
