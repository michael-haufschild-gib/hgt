# SQB: complete native theta pairing and nonzero unit source

The complete centered theta source is nonzero in the original native
Hilbert space. Lean constructs its unit normalization and proves a strict
two-sided weighted energy bound. Full-Xi occurrence and RH remain unproved.

## Exact source statements

For an actual Xi divisor copy q, let z=b+ic=xiSpectralPoint(q),
Phi=thetaCuspFullSource, u=SelbergThetaSourcePhase.mode(q), x=log(y)/2,
p(y)=sqrt(y)Phi(x), w(y)=sqrt(y)u(x). Let P,W be their complete primitive-row
periodizations, h=z-i, V=W+P/h, and

    m_a=2 integral exp(a x)Phi(x)>0, m=m_{-1}.

The new all-real moment module proves, for every real a and r,

    integral exp(a x)u(x)=-m_a/[2(z+i a)],
    integral_0^infty y^-2 p(y)y^r dy=m_{2r-1},
    integral_0^infty y^-2 w(y)y^r dy=-m_{2r-1}/(z+i(2r-1)),
    m_{-a}=m_a.

The native pairing module uses the actual positive Eisenstein field
E2=positiveCuspRows(2) and k=cuspReflectionNorm(2). It proves

    integral_fd V E2=(2i m_3/h)[2/(z+3i)-k/(z-3i)] !=0.

The complete pairing is integrable. Hence V is not zero almost everywhere.
The actual native vector `centeredVector(q)` is its toLp representative,
has zero integral, and is nonzero. Its reciprocal-norm rescaling
`centeredUnit(q)` has original native Hilbert norm exactly one.

Together with the preceding exact energy decomposition, Lean proves

    0 < integral_fd |V|^2/P < m/|h|^2,
    m/|h|^2 < integral_fd |W|^2/P < 2m/|h|^2.

These are unconditional theorems on each actual divisor copy. No source
admission, normalization, nonvanishing, RH or spectral-occurrence premise
is added.

## Closed analytical mechanism

The source's all-power height bounds imply uniform bounds for every
exp(a x)Phi(x). Applying the bounds at a+1 and a-1 proves decaying
exponential bounds at the two ends for exp(a x)u(x), using bounded u/Phi.
All tilted mode and derivative integrals are absolute. Integration of
the exact first-order ODE gives the moment denominator z+i a, which is
nonzero because b is an actual nonzero zero ordinate. The Jacobian of
y=exp(2x) then yields both all-real seed Mellin identities.

The actual lower Eisenstein row mean at height two identifies the
completed coefficient ratio with the real k. Substitution in the complete
two-Weyl mean proves that E2 has horizontal mean y^2+k/y at every y>0.
No numerical comparison of completion factors enters this identification.

For any of the literal seeds used in the pairing, all-power bounds make
|v(y)|y^r integrable for every real r. The proof uses a bounded majorant
near zero and a y^-2 majorant at infinity, with exponents adjusted to r.
The horizontal norm mean for v(Im(z))E2(z) is

    |v(y)|(y^2+k/y).

Thus the hyperbolic strip norm is bounded by integrable moments at
exponents zero and -3. Translation invariance and modular invariance of
E2 let the actual strip unfold into the complete primitive-row family.
The integrals of the row norms are summable, so the integral and the
entire row sum interchange. This retains every modular row and both
Weyl terms despite E2 itself not belonging to native L2.

At r=2 and r=-1, evenness makes the two theta masses equal to m_3.
The exact paired expression follows. If its bracket vanished, then

    (2-k)z-3i(2+k)=0.

The real part and b!=0 force k=2, while the imaginary part gives -12=0.
This proves the pairing is nonzero. The centered weighted density is
integrable by the bound |V|<=K P supplied by the full native disk.
Its integral cannot be zero without V being zero almost everywhere.
This proves strict positive centered energy and the strict lower bound.

## Lean surface and audit

- `formal/GaloisForLFunctions/RHTower/SelbergThetaNativeMoments.lean`:
  namespace `RHTower.SelbergThetaNativeMoments`, seven public declarations,
  235 lines.
- `formal/GaloisForLFunctions/RHTower/SelbergThetaNativePairing.lean`:
  namespace `RHTower.SelbergThetaNativePairing`, twelve public declarations,
  450 lines.
- Both wired once into `RHTower.lean`.
- Full scratch and canonical source checks passed with `lake env lean FILE`
  without diagnostics. Logs: `/tmp/sqb33_moments_check.log`,
  `/tmp/sqb33_moments_source_check.log`, `/tmp/sqb33_pairing_check.log`,
  `/tmp/sqb33_pairing_source_check.log`.
- NativeMoments final named leaf build passed in 9.5 seconds using
  `lake --old build GaloisForLFunctions.RHTower.SelbergThetaNativeMoments`.
  Its preflight identified only that leaf. Logs:
  `/tmp/sqb33_moments_preflight.log`, `/tmp/sqb33_moments_leaf_build.log`.
- NativePairing final named leaf build passed in 9.6 seconds using
  `lake --old build GaloisForLFunctions.RHTower.SelbergThetaNativePairing`.
  It also rebuilt the required direct dependency
  `ThetaCuspHawkingBMStripMeanAdmission` in 21 seconds, as identified by
  its preflight. These are the only two Built lines in that invocation.
  Logs: `/tmp/sqb33_pairing_preflight.log`, `/tmp/sqb33_pairing_leaf_build.log`.
- All nineteen public declarations passed scratch `#print axioms` in
  `/tmp/sqb33_axioms.lean`; every output contains only `propext`,
  `Classical.choice`, `Quot.sound`. Log: `/tmp/sqb33_axioms.log`.
- Repository formal lint passed. Log: `/tmp/sqb33_lint.log`.
- Declaration indexing passed. Log: `/tmp/sqb33_index.log`.

Dependency artifacts were replayed during the named leaf builds; this is
not a fresh audit of the entire dependency source tree. Scoped whitespace
checks passed. Every owned foreground Lean/Lake process exited and its
terminal result was collected. No numerical
computations, full builds, umbrella builds or frontier-map edits were used.

## Remaining obstacle

This proves recovery and normalization of the actual centered source.
The unchanged full-Xi target still requires a family whose complete
operator residual vanishes after its own native normalization. The paper
forcing remains

    (A-e)V=-periodize[sqrt(y)(D-1)(D-iz)Phi]/(4(z-i)),
    e=5/4+z^2/4.

Full graph admission, rowwise derivative interchange and the required
normalized residual estimate remain unproved. The paired scalar is a
recovery functional; vanishing of a scalar pairing cannot replace the
full vector residual. No new no-go or conditional occurrence receiver was
added.
