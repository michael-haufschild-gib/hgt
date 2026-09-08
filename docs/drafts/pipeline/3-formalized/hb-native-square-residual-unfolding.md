# Native square-residual unfolding and complete Fourier–Mellin mean

## Result

For every original Xi divisor copy `q`, let `E_u` be the full scalar cusp
field, `A_u` its original two-power constant part, and

```text
eta(y) = smoothTransition(y-2),
R_q(z) = E_(q-1/2)(z)^2/2 - eta(y)*A_(q-1/2)(y)^2/2,
J(q,u) = integral_fd E_u(z)*R_q(z) dmu.
```

Here `dmu` is the original hyperbolic measure. The source product is
bilinear; its squares contain no complex conjugation.

The literal residual has a smooth modular extension `R_q^aut` agreeing
with it on the entire closed fundamental domain. Define

```text
w(x) = smoothTransition(x+1)-smoothTransition(x),
f_q(z) = w(x)*eta(y)*A_(q-1/2)(y)^2/2,
P_q(z) = sum_(gamma in PSL2Z) f_q(gamma*z),
C_q(y) = integral_0^1 P_q(x+iy) dx.
```

Every cutoff image is retained. Lean proves on the whole upper half-plane

```text
R_q^aut(z) = E_(q-1/2)(z)^2/2 - P_q(z).
```

For every complex `s` with `Re(s)>1`, the following are equalities of the
original admitted integrals:

```text
J(q,s-1/2)
  = Lambda(2s)*integral_strip y^s*R_q^aut(z) dmu
  = Lambda(2s)*integral_0^infinity y^(s-2)*M_q(y) dy,

M_q(y) = A_(q-1/2)(y)^2/2
         + 4*sum_N amplitude(q-1/2,y,N)^2 - C_q(y).
```

The factor `4` is the paired nonconstant Fourier contribution of the
original **half-square** source. No equality with an assigned four-Lambda
expression is assumed.

## Proof

Integer translations preserve the literal residual. Every nonparabolic
overlap of closed fundamental cells lies below the cutoff in both charts.
There the residual is exactly the full scalar half-square, whose modular
symmetry is already proved. Thus the full residual germs agree across
every overlap. The existing cell-germ extension theorem constructs the
smooth invariant extension and gives exact closed-cell agreement.

The full projective periodization of `f_q` equals the original cutoff
subtraction on the closed cell. Nonparabolic summands vanish there by the
actual transformed-height bound; all translation summands give the proved
partition sum one. Transport by a modular representative then identifies
the extension with the full scalar square minus `P_q` everywhere.

Compactness bounds the residual on the lower fundamental cell. The
complete Fourier square remainder bounds the upper cusp. Modular
invariance transports this to a bound on the entire upper half-plane.
Above height three in the standard strip, translation into the closed
cell identifies the extension with the original residual. Every complex
height weight times that full remainder is bounded there.

Consequently, `y^s*R_q^aut` is integrable in the original strip measure.
At the lower end its norm density is bounded by a constant times
`y^(Re(s)-2)`, which is integrable because `Re(s)>1`. At the upper end the
weighted cusp bound gives a constant times `y^(-2)`.

The actual primitive integer-pair Eisenstein sum is reindexed by the
corpus's coprime-row matrices, preserving its factor `1/2`. Translated
norm-integral summability follows from strip admission. This justifies
the infinite-sum/integral interchange. Coprime-row unfolding contributes
the exact factor two, cancelling the original `1/2` and yielding the
native strip identity with completion factor `Lambda(2s)`.

The actual hyperbolic chart and Fubini theorem give the Mellin density
`y^(s-2)`. Periodicity transfers the existing full scalar-square Fourier
mean to `[0,1)`. The periodized cutoff is continuous on each horizontal
interval because it equals the difference of the full scalar half-square
and the smooth modular residual. Both horizontal integrals are admitted,
so subtracting their means gives the displayed complete integrand.

## Lean implementation and audit

All eight new modules have prefix
`GaloisForLFunctions.RHTower.ThetaCuspHawking`:

- `BMSquareResidualModular`: actual compatible extension and full cutoff identity.
- `BMSquareResidualModularBounds`: global bound and complete high-strip bounds.
- `BMModularStripPowerAdmission`: lower-power and bounded-upper-tail admission.
- `BMSquareResidualMellinAdmission`: actual periodic, integrable Mellin seed.
- `BMEisensteinCoprimeRowSum`: exact primitive-pair/coprime-row identification.
- `BMNativeSquareResidualUnfolding`: admitted native quotient-to-strip equality.
- `BMNativeSquareResidualMellinReduction`: original measure and Mellin reduction.
- [BMNativeSquareResidualFourierMean](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMNativeSquareResidualFourierMean.lean):
  `residualStripMean_eq_fourier` and
  `scalarResidualPeriod_eq_full_fourier_mellin`.

The eight scratch leaves passed `lake env lean`. All eight individual
canonical `lake build <module>` audits passed. The 585 new source lines
contain 22 new public theorems; scratch-only axiom checks for exactly those
22 use only `propext`, `Classical.choice`, and `Quot.sound`. Eight sources
and their 16 `.olean`/`.ilean` artifacts were installed and byte-verified
against the canonical audit. All eight imports are wired into `RHTower`.
No full build, umbrella build, or numerical experiment was run. Initial
audit setup reported missing manifests for the private cache-only package
stubs; the Lean module builds produced no elaboration warnings.

Repository `lint --check-generated` is not green: it reports seven
unreachable modules outside this batch (`SelbergMaassCurrentTests` and
the Fokas–Lenells `RawBounds`, `RawEndpoints`, `RawEvolution`,
`RawInteraction`, `RawScattering`, and `RawZero` leaves). It reports no
proof-debt or generated-freshness errors in that check. The eight new
modules each have one verified umbrella import.

## Remaining hard problem

This derives the complete Mellin integrand of the actual native period.
Its value is not yet evaluated. In particular, the integral of the full
cutoff orbit mean has not been replaced by an arithmetic or boundary
formula. Before splitting the combined Mellin integrand into separate
terms, prove each new term and interchange is admitted in a common chamber.

The existing `actualUnfoldedScalarSource` starts from a defined
Fourier–Bessel/Dirichlet expression and uses a different parameter chamber.
Its four-Lambda evaluation cannot be substituted for `J` without proving
the remaining cutoff contribution, normalization, and parameter transport.
The physical test `s=q/2` lies outside the strip-unfolding chamber; any
continuation must be identified with this same original integral.

Complete source nonvanishing, the original outgoing joint inverse and
physical left residue, independent Hawking-clock extinction, and RH remain
unproved. The frontier map remains read-only.
