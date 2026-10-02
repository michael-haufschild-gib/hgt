# SZ finite exponential source budgets

- ID: sz-truncated-exponential-fourier-budget
- Stage: 3-formalized
- Type: THEOREM (Lean)
- Route: SZ
- RH status: unresolved

## Source representation and exact estimates

For f(x)=z*1_[l,r](x)*exp(s*x), define
  V=norm(z)*exp(max(s*l,s*r)).
Then norm(f(x))<=V. For l<=r and real xi!=0,
  norm(Fourier(f)(xi))<=V/(pi*abs(xi)).
The same bound holds for finite sums with V replaced by the sum of
individual budgets. No additional factor counts the pieces.

Translation x -> x-h replaces the interval by [l+h,r+h] and coefficient
by z*exp(-s*h). This preserves V exactly. Restriction to [u,v] is exactly
the atom on [max(l,u),min(r,v)]; a retained subinterval cannot increase V.
Empty intersections vanish by the indicator definition.

## Paper proof

The supremum is bounded by the larger exponential endpoint. The classical
Fourier integral is z times the interval integral of exp(c*x), where
c=s-2*pi*i*xi. Its exact primitive gives the difference of endpoint
exponentials divided by c. The numerator norm is at most
2*exp(max(s*l,s*r)); norm(c)>=2*pi*abs(xi). Finite summation follows by
integrability and the triangle inequality. Translation invariance follows
by cancelling exp(-s*h) against the endpoint factor exp(s*h).

The construction is based on the corpus antiderivative argument in
HTGeometry/ExponentialPieceFourierDecay and the actual polar Fourier
representation in CCMRestrictedWeilPolarFourierRegularity. It extends the
former's integer-frequency, unit-interval estimate to arbitrary real
frequencies and intervals with the exact endpoint budget required by
moving prime translates.

## Lean audit

Module: CCMTruncatedExponentialFourierBudget.

Nine public theorems, two definitions. Scratch audits23268 and30428 pass.
Final leaf audit4101 used `lake --old env lean <leaf> -o <leaf.olean>`
from formal/ and exited0, no warnings or errors. All nine axiom queries
(session42237) exited0, reporting only propext, Classical.choice,
Quot.sound. The leaf is wired into the root RHTower umbrella. No umbrella
or full build was run.

Final global lint10308 exited1 on thirteen unrelated unreachable modules;
this leaf and CCMPolarPrimeExponentialFrequencyCancellation were not
reported. The exact current errors are retained in the SZ working log.

## Exact outstanding connection

These estimates do not yet prove closure of actual Hilbert remainder
iterates. Assemble the finite representation, identify its scalar, polar,
and prime actions with ccmRestrictedWeilBoundedRemainder, and transfer the
pointwise Fourier tail to L2. Then combine with the certified exponential
frequency-window theorem to prove the one-step source norm estimate and
the growing-iterate Neumann argument. Actual odd-response energy, signed
aperture Wronskian control, shift removal, and RH remain unresolved.
