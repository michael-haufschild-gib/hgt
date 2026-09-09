# HB: the original cutoff orbit's reflected Mellin value

Stage: formalized. Ten new leaves, 869 source lines, 50 new public theorems.
RH remains unproved.

Chain: literal theta cusp → Xi occurrence → complete native source projection
→ original causal response and physical adjoint pairing → independent
Hawking-clock extinction → RH.

## Exact theorem

Let `q` be any original Xi copy, `h_q(y)=eta(y) A_(q-1/2)(y)^2/2`, and
`P_h` the full projective periodization with the original translation window.
Let `C_q(y)=squareCutoffStripMean q y` be the actual horizontal mean of
`P_h`. For `Re s>2`, Lean proves

```text
Lambda(2s) integral_(0,1/2] y^(s-2) C_q(y) dy
  = Lambda(2s-1) integral_(2,infinity) y^(-s-1) h_q(y) dy.
```

Both height integrals are absolutely admitted. On the lower interval,
`h_q=0`, so `C_q` is precisely the complete nonparabolic correction. The
identity retains every original orbit image and both Weyl coefficients.
It does not integrate the growing parabolic cutoff separately at infinity.

The capstone is `RHTower.D4BMJointSource.nativeCutoffOrbit_mellin_value`.
Its only restriction on the testing parameter is the displayed convergence
chamber; no source-bound, integral-admission, interchange, or RH premise
is supplied.

## Positive majorants from the original rows

For real `r>1`, let `S_r` be the sum of positive transformed height powers
over the original coprime half-rows. Let `L_r` retain the same rows whose
transformed heights are at most `1/2`. Their complexifications are exactly
the original windowed power periodizations, with the already proved
projective multiplicity.

The original completion is nonzero in its right half-plane. Set
`D(r)=norm(Lambda(2r-1))/norm(Lambda(2r))`. The actual scalar constant term
and reverse-kernel mean give

```text
integral_0^1 S_r(x+iy) dx <= y^r + D(r) y^(1-r),       y>0,
integral_0^1 L_r(x+iy) dx  = D(r) y^(1-r),             y>=2.
```

Nonnegative row sums dominate the norms of the unchanged complex sums:

```text
norm(P_low_s(z)) <= L_(Re s)(z),
norm(P_h_q(z))   <= C S_2(z),
```

where `low_s(y)=y^s` on `y<=1/2`, and zero otherwise. The constant `C`
comes from the proved native estimate `norm(h_q(y))<=C y^2`. Positivity
is used for the majorant, not asserted of the complex source.

## Both original strip products are admitted

The literal products are

```text
F_lower(z) = low_s(Im z) P_h_q(z),
F_upper(z) = h_q(Im z) P_low_s(z).
```

The countable orbit sums and actual chart are measurable. For
`sigma=Re s>2`, their horizontal norm densities in `dx dy/y^2` satisfy

```text
lower: <= C [y^sigma + D(2) y^(sigma-3)]  on 0<y<=1/2,
upper: <= C D(sigma) y^(1-sigma)          on y>2.
```

Each product is zero on its complementary height region. The exponents
`sigma-3>-1` and `1-sigma<-1` give actual absolute strip integrability.
The chart proof uses Fubini's criterion for the integral of the horizontal
norm; pointwise finite orbit support alone is not used as an interchange
argument.

## Exact unfolding in both directions

Strip admission and the existing fundamental-domain decomposition derive
summability of the half-row integral norms. Thus

```text
integral_strip F_lower
  = integral_fd P_low_s P_h_q
  = integral_fd P_h_q P_low_s
  = integral_strip F_upper.
```

All integrals use the original hyperbolic measure, and each half-row occurs
once. Periodicity and the actual modular invariance of each periodization
identify the pointwise sums before either integral interchange.

Fubini reduces the lower product to the displayed `C_q` Mellin integral.
On the support of `h_q`, the completed reverse-kernel mean is
`Lambda(2s-1) y^(1-s)`. The hyperbolic density supplies the remaining
`y^-2`, giving the reflected exponent `-s-1` and the stated identity.

## Lean leaves and verification

All leaves are under `GaloisForLFunctions.RHTower`, with prefix
`ThetaCuspHawking`:

| Leaf suffix | Closed content |
| --- | --- |
| `BMCuspPositiveRows` | Positive row sums and original complex norm bounds |
| `BMCuspOrbitMeasurability` | Original seeds, full sums, and majorant measurability |
| `BMCuspPositiveMean` | Actual completion factors and horizontal mean bounds |
| `BMStripMeanAdmission` | Measurable chart and absolute Fubini admission criterion |
| `BMNativeCutoffPairingSeeds` | Both original products, periodicity, and support |
| `BMNativeCutoffLowerAdmission` | Complete lower-strip absolute integral |
| `BMNativeCutoffUpperAdmission` | Complete reverse-strip absolute integral |
| `BMHalfRowIntegralInterchange` | Integral-norm summability and exact half-row unfolding |
| `BMNativeCutoffPairingUnfolding` | Source-dependent equality in both directions |
| `BMNativeCutoffMellinValue` | Admitted original height integrals and reflected value |

Scratch checks used `lake env lean`. Each final canonical module passed its
individual `lake build <module>` in an isolated workspace using existing
dependency artifacts; all ten audits were warning-free. Exactly 50 new
public theorem axiom checks returned only `propext`, `Classical.choice`,
and `Quot.sound`. Ten sources and twenty olean/ilean artifacts were installed
with byte verification. All ten modules are wired into the umbrella.
No full or umbrella build and no numerical experiment was run.

The repository-wide static `lint --check-generated` gate returned exit 1.
It reported four unrelated `HTGeometry` modules unreachable from their
umbrella: `FokasLenellsRawQuinticKernel`, `FokasLenellsRawSecondPhase`,
`FokasLenellsRawTaylorFifth`, and `FokasLenellsRawTaylorFourth`. It also
reported stale `LEAN_API.md`, `LEAN_GAPS.md`, and `LEAN_OVERVIEW.md` after
concurrent corpus changes. No error named these ten new HB leaves and no
proof-debt violation was reported. That static audit failed; the
individual module and new-theorem audits above did pass.

## Remaining source problem

The [complete native period continuation](hb-native-period-continuation.md)
now assembles this lower orbit correction with the actual principal
remainder and [Fourier diagonal](hb-native-fourier-mellin-value.md).
It agrees with the original quotient integral for right-half Xi sources
and `Re s>2`, is meromorphic, and has an analytic value at `s=q/2` retaining
the reflected cutoff moment.

Identifying that physical value with the original quotient pairing needs
the [actual integral's parameter regularity](../1-in-progress/hb-native-square-residual-mellin-value.md).
The original outgoing joint inverse, physical advanced/adjoint left
resonance, complete source nonvanishing, independent extinction, and RH
remain open.
