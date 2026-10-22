# SQB: centered horizontal theta weight

Status: the full arithmetic representation and its absolute admissions are formalized. Source check, named-leaf build, all 22 public axiom audits, and formal lint pass. The native centered-weight estimate remains open.

Full chain: theta source -> normalized packets with vanishing full native residual at every Xi target -> occurrence -> critical line -> RH. The hardest remaining input is a source estimate on the native scalar pairing, including its constant-mode subtraction.

## Closed source construction

`formal/GaloisForLFunctions/RHTower/SelbergThetaHorizontalArithmetic.lean` constructs the literal radial projection of `f = positiveProfile`, with `J` the fixed horizontal weight in the native scalar pairing:

    g(u) = integral_R f(1/(u^2+v^2)) dv,
    J(y) = f(y) + sqrt(y) sum_c phi(c)/c g(c sqrt(y)).

The actual projection is uniformly bounded on positive coordinates, has an inverse-cube bound, and is absolutely integrable on the positive half-line. Every full lattice sum converges absolutely. The signed divisor-pair source has a product majorant proportional to `d^-4 k^-3`.

For `a=sqrt(y)`, `B=integral_0^infinity g(u) du`, `Q(t)=t sum_k g(kt)-B`, and `L=sum_d mu(d)/d^2`, complete Möbius inversion gives

    J(y) - L B = f(y) + sum_d mu(d)/d^2 Q(d a).

The entire centered remainder converges absolutely. All positive integers, primitive rows, reduced residues, and translations are retained. This is an identity for the original source, with no assumed arithmetic cancellation.

## Active analytical target

The native scalar pairing uses `M/V`. Identifying `LB=M/V` still needs the radial-mass and native-measure laws. The expected constants are `B=pi M/2`, `L=6/pi^2`, and `V=pi/3`; this module does not assert these identities.

A concrete source-specific variation candidate uses reflection to write the radial field as `G(r)=r^-1 Phi(log r)`. Its derivative satisfies

    G'(r) = r^-2 (Phi'(log r)-Phi(log r)),
    integral_0^infinity r |G'(r)| dr = integral_R |Phi'(x)-Phi(x)| dx.

The right side is finite by the existing Schwartz source and derivative. Integrating the horizontal derivative over the half-plane suggests

    Var_[0,infinity)(g) <= 2 integral_R |Phi'-Phi|.

The source-specific variation admission remains to be formalized. Together with the proved inverse-cube tail it would bound the unsigned quadrature remainder by `O(a(1+|log a|))`, after splitting the divisor sum near `1/a`. Sufficiency of that elementary bound for normalized native residuals is not established. The decisive target is stronger cancellation in the literal signed remainder, then a source-pairing orientation or full native residual estimate.

## Verified corpus joins

Complete row reindexing and translation means: `SelbergThetaDilationRows`. Actual source power bounds: `SelbergThetaNativeSource`. Arithmetic coefficient: `Sieve/TotientMoebiusNormalisation.sum_moebius_div_divisors_eq_totient_div`. Complete divisor-pair reindexing: mathlib's `sigmaAntidiagonalEquivProd`. Their joins are checked in the new source, including absolute convergence.

Further candidates include `CCMBVMuntzSummation.abs_sum_riemann_sub_integral_le`, `HTGeometry/BoundedVariationRiemannSum`, and `thetaCuspSchwartzReal`. Generic compact-support quadrature results still require a source-specific noncompact admission before application here.
