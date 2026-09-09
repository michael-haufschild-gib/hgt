# SQB: centered horizontal theta weight

Status: analytical construction in progress. No centered-weight estimate or new Lean theorem is yet claimed.

Full chain: theta source -> normalized packets with vanishing full native residual at every Xi target -> occurrence -> critical line -> RH. The hardest remaining input is a source estimate on the native scalar pairing, including its constant-mode subtraction.

Let f(y)=sqrt(y) Phi(log(y)/2), P its complete primitive-row periodization, and J(y)=integral_[0,1) P(x+iy) dx. The existing native pairing is an admitted integral against J with the exact subtraction M/V.

The proposed arithmetic coordinate is

    g(u) = integral_R f(1/(u^2+v^2)) dv,
    J(y) = f(y) + sqrt(y) sum_c phi(c)/c g(c sqrt(y)).

All c are positive integers. For a=sqrt(y), B=integral_0^infinity g(u) du, Q(t)=t sum_k g(kt)-B, Möbius inversion suggests the exact centered identity

    J(y) - L B = f(y) + sum_d mu(d)/d^2 Q(d a),
    L = sum_d mu(d)/d^2.

The constant is expected to be LB=M/V: radial integration gives B=pi M/2, and the Euler coefficient L=6/pi^2 matches native volume pi/3. These identities need explicit admission and native measure identification in Lean.

Analytical bound to test: bounded variation of g gives |Q(t)|<=t Var(g). The actual inverse-square profile should supply g(u)<=C/u^3 for u>=1, controlling the large-d part without a divergent harmonic estimate. Split at d approximately 1/a; this gives an elementary O(a(1+|log a|)) remainder. Its sufficiency for the desired normalized native residual is NOT established. Stronger cancellation must act on the signed Möbius remainder itself, not on its absolute row majorant.

A source-specific variation mechanism: away from the origin the underlying radial field is G(r)=r^-1 Phi(log r), using the proved reflection of Phi. Then integral_0^infinity r |G'(r)| dr = integral_R |Phi'(x)-Phi(x)| dx, finite by existing Schwartz source and derivative admission. Projection onto one coordinate should give Var_[0,infinity)(g)<=2 integral |Phi'-Phi|. This is a constructive route to the actual quadrature bound, not an assumed BV premise for the theta source.

Located ingredients: complete row reindexing/translation mean in SelbergThetaDilationRows; actual positive-source power bounds and global modular bound; totient_eq_sum_moebius_mul and sum_moebius_div_divisors_eq_totient_div; abs_sum_riemann_sub_integral_le in CCMBVMuntzSummation; thetaCuspSchwartzReal and its derivative. Their exact carriers and hypotheses must be checked at each join.
