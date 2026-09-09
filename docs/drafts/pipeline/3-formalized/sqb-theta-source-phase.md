# SQB: positive actual theta mode and global logarithmic equation

Every actual Xi divisor copy has a theta mode whose real part has a strict
fixed sign throughout the real line. A real normalization therefore stays
in the open right half-plane and has a globally differentiable principal
logarithm. These are source results; normalized native occurrence and RH
remain unproved.

## Exact theorem

For an actual multiplicity copy rho=beta+i gamma, let

    z=(rho-1/2)(-i)=b+ic,
    u(x)=hedenmalmCausalVolterra(z,x),
    Phi(x)=thetaCuspFullSource(x), Q(x)=Phi'(x)/Phi(x),
    p(x)=-b u(x), L(x)=-iz-i Phi(x)/u(x).

The actual divisor theorems supply b!=0, |c|<1 and XiC(z)=0. The new
unconditional conclusions, at every real x, are

    b Re(u(x))<0,                 Re(p(x))>0,
    u(x)!=0,                     L(x)=u'(x)/u(x),
    (log(p))'(x)=L(x),
    L'(x)=(Q(x)-L(x))(L(x)+iz),
    b (Im(L(x))+b)=Re(p(x)) Phi(x)/|u(x)|^2>0.

Here log is the principal complex logarithm. Its domain is justified
pointwise by strict positive real part, with no branch choices or spatial
nonvanishing assumptions added to the theorem.

## Dependency-closed analytical proof

1. For a real Schwartz function f with f'<0 beyond x and b>0, integrate
   the derivative of f(t)(1-cos(b(t-x))). Both endpoint contributions
   vanish. The result is

       b integral_x^infinity f(t)sin(b(t-x))dt
         = integral_x^infinity -f'(t)(1-cos(b(t-x)))dt>0.

   Integrability follows from Schwartz decay and bounded sine/cosine.
   The integrand on the right is nonnegative and strictly positive near
   x+pi/b. Complex conjugation gives the corresponding signed result
   for every nonzero b.
2. The actual tilted theta source exp(a t)Phi(t) is Schwartz for |a|<1.
   Its derivative is (a+Q(t))exp(a t)Phi(t). Strict logarithmic concavity
   of Phi makes a+Q strictly decreasing; modular reflection makes Q odd.
3. At each spatial x, either Q(x)-c<=0, so the right tilted tail is
   strictly decreasing, or reflection gives a strictly decreasing left
   tilted tail. The exact causal/anti-causal equality at XiC(z)=0 lets
   either tail determine u. Its factors i and exp(c x) convert the sine
   sign into b Re(u(x))<0 in both cases.
4. The actual source ODE u'=-iz u-i Phi gives the formula for L. The
   proved nonvanishing permits division globally. Differentiate it and
   use Phi'=Q Phi to obtain the displayed Riccati equation.
5. Strict positive real part puts p in the slit plane. The complex
   logarithm chain rule gives (log p)'=p'/p=L. Expanding imaginary parts
   in the formula for L yields the positive phase-current identity.

## Formal audit

Module: `formal/GaloisForLFunctions/RHTower/SelbergThetaSourcePhase.lean`.
Namespace: `RHTower.SelbergThetaSourcePhase`. 13 public declarations,
374 lines, imported once by `RHTower.lean`.

- Scratch and canonical source checks passed using `lake env lean FILE`.
- All 13 public declarations passed `#print axioms` in
  `/tmp/sqb28_axioms.lean`; output `/tmp/sqb28_axioms.log` contains only
  `propext`, `Classical.choice`, `Quot.sound`.
- Final leaf audit passed:
  `lake --old build GaloisForLFunctions.RHTower.SelbergThetaSourcePhase`.
  Preflight showed only this leaf needed rebuilding; the leaf took
  14 seconds. Dependencies were replayed from existing artifacts. This
  is not a fresh build of the whole dependency source tree. Logs:
  `/tmp/sqb28_preflight.log`, `/tmp/sqb28_leaf_build.log`.
- `python3 scripts/formal_tools.py lint` passed; its large-file warnings
  do not fail the gate. Output: `/tmp/sqb28_lint.log`.

No numerical computations, additional axioms, proof holes, full builds
or umbrella builds were used. Frontier map was not modified by this work.

## Remaining source comparison

The full complex parameter remains in the Riccati equation. The strictly
positive phase-current density has not yet supplied control of the weighted
odd-source term in the transformed differential equation, or a normalized
native residual estimate. The precise ongoing comparison is recorded in
[the positive occurrence card](../1-in-progress/sqb-positive-occurrence-conjecturing-loop.md).
