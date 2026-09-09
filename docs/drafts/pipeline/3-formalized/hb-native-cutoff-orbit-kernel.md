# HB: original cutoff orbit and reverse Mellin kernel

Stage: formalized. Ten new leaves, 681 source lines, 43 new public theorems.
These kernel results alone do not evaluate the complete native source period
or prove RH. Their two-sided Mellin pairing is formalized below.

Chain: literal theta cusp → Xi occurrence → complete native source projection
→ original causal response and physical adjoint pairing → independent
Hawking-clock extinction → RH.

## Exact original orbit sum

For the original window `w(x)=smoothTransition(x+1)-smoothTransition(x)`, set
`seed_h(z)=w(Re z) h(Im z)` and `P_h(z)=sum_gamma seed_h(gamma z)` over
`PSL2Z`. The unchanged window satisfies `sum_n w(x+n)=1` for every real
coordinate. `cuspOrbitEquiv` identifies the actual projective group with
coprime half-rows and integer translations, using the existing representatives
and their proved unique translation decomposition.

If `h(y)=0` for `y<=2`, the full orbit sum has finite support at each fixed
point. Every active image lies in the compact rectangle
`[-1,1] x [2,max(y,1/y)]`; proper discontinuity bounds the active group
elements. No upper compact support on the profile is imposed. Exact
regrouping gives

```text
P_h(z) = sum_(v in gammaSetHalf) h(Im(gamma_v z))
       = h(y) + sum_(v != identityRow) h(Im(gamma_v z)).
```

Every nonidentity half-row has positive lower-left entry and transformed
height at most `1/y`. Its complete sum therefore vanishes for `y>=1/2`.
All contributions below that height remain present.

For the actual Xi source, `h_q(y)=eta(y) A_(q-1/2)(y)^2/2` gives exactly
the existing `squareCutoffSeed`. The global square residual equals the
original local square residual at every horizontal coordinate when
`y>=1/2`. Its horizontal mean there is
`(1-eta) A^2/2 + 4 sum_N amplitude_N^2`.

## Reverse kernel and reflected moment

Nonnegativity and finite translation support of the original window give
`sum_n norm(seed_h(T^n gamma_v z))=norm(h(Im(gamma_v z)))`.
Thus summability of the height rows admits the full projective sum, including
profiles reaching zero. Negating a coprime row preserves its height; the full
row sum has exactly twice the projective half-row multiplicity. Existing
convergence of the actual Eisenstein sum proves, for `Re s>1`,

```text
Lambda(2s) P_(y^s)(z) = scalar(s-1/2)(coordinates z).
```

Set `low_s(y)=y^s` for `y<=1/2` and zero otherwise. Its row and orbit sums
converge by comparison with those same power rows. For `y>=2`, every
nonparabolic row is retained and the parabolic row is absent. Consequently,

```text
Lambda(2s) P_low_s(z)
  = scalar(s-1/2)(coordinates z) - Lambda(2s) y^s,
integral_0^1 Lambda(2s) P_low_s(x+iy) dx
  = Lambda(2s-1) y^(1-s).
```

This mean follows from the original scalar's actual constant term and
periodicity, with no assigned normalization of the reverse kernel.

The proved strict Xi strip supplies positive real parts for both original
Weyl exponents `q` and `1-q`. The actual `h_q` is continuous and satisfies
`norm(h_q(y))<=C y^2` on the entire real line, where
`C=(norm(Lambda(2q-1))+norm(Lambda(2q)))^2/2`. For `Re s>2`, the majorant
`C y^(1-Re s)` admits the original reflected moment
`integral_2^infinity y^(-s-1) h_q(y) dy`. No native source bound is supplied
as a premise.

## Lean leaves and audit

All leaves are under `GaloisForLFunctions.RHTower`, with prefix
`ThetaCuspHawking`:

| Leaf suffix | Closed content |
| --- | --- |
| `BMCuspOrbitIndex` | Original window partition and actual group equivalence |
| `BMCuspHeightOrbitFinite` | Pointwise finite high-support orbit and norm sums |
| `BMCuspHeightRowPeriodization` | Exact translation and half-row regrouping |
| `BMCuspNonparabolicHeight` | Full nonparabolic sum and height cutoff |
| `BMNativeCutoffOrbitSeparation` | Original native source specialization |
| `BMCuspWindowAbsoluteRegrouping` | Norm-preserving translations and row admission |
| `BMCuspPowerPeriodization` | Actual completed Eisenstein normalization |
| `BMLowCuspPower` | Admitted reverse lower-height kernel |
| `BMLowCuspPowerMean` | Actual reflected horizontal mean |
| `BMNativeCutoffMellinAdmission` | Original quadratic bound and reflected moment |

Each new leaf passed `lake env lean <scratch-file>`, then its individual
canonical `lake build <module>` in an isolated workspace using existing
dependency artifacts. All ten final module audits were warning-free.
Scratch-only `#print axioms` checked exactly the 43 new public theorems;
their dependencies are only `propext`, `Classical.choice`, and `Quot.sound`.
Ten sources and twenty olean/ilean artifacts were installed with byte
verification. All ten modules are wired into the umbrella; no umbrella or
full build was run. No numerical computation supplied any proof step.

The repository-wide `lint --check-generated` run did not pass. It reported
the unrelated `HTGeometry.FokasLenellsRawMixedPrimitive` as unreachable and
three stale generated files: `LEAN_API.md`, `LEAN_GAPS.md`, and
`LEAN_OVERVIEW.md`. It reported no error in these ten new leaves. The global
gate did not pass in that audit.

## Subsequent integral pairing and remaining source problem

The [original reflected Mellin value](hb-native-cutoff-orbit-mellin.md)
now proves both strip-product admissions, summability of integral norms,
and both sum/integral interchanges. It evaluates the complete lower-strip
cutoff correction against the admitted reflected native height moment.
Pointwise finite orbit support alone does not supply those estimates.

The [complete native period continuation](hb-native-period-continuation.md)
now has its derived combined value and analytic physical specialization,
with the reflected cutoff correction retained. Its identification with
the actual physical quotient pairing still needs parameter regularity of
that integral. The original outgoing joint inverse, physical left residue,
source nonvanishing, independent extinction, and RH remain open.
