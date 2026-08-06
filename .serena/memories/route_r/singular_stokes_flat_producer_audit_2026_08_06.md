# Route R SingularStokesFlat producer audit (2026-08-06)

Exact endpoint: `RouteRPrimeLogEssentialCapSingularStokesLaw.lean` proves port `P_p(rho)=a_rho(1-p^-1)(2-p^-1)c_rho -> 2 a_rho c_rho`, with `a_rho=2 Re rho-1` and nonzero Xi jet `c_rho`; `SingularStokesFlat rho <-> a_rho=0`, globally iff RH.

Hostile-tested producers:
1. Reflected source entropy is signed `1-2 Re s`, not nonnegative; fails.
2. Rational Cartier pre-divisor potential is constant gain 1; compatibility with physical gain is exact central Bockstein/RH wall.
3. Weak-L1/singular trace fails domain: damped wall `sum p^-eps |beta_t(p)| < infinity <-> t=0 or |t|<eps`; eps=0 membership already forces t=0.
4. Cyclic dagger maps corrected class to distinct Kummer-sign-reversed class; sign cancels Gamma reflection and gives unconditional but blind naturality.
5. Prime-log comparison transports multiplication/trace/derivation/non-erasure only, not all-prime valuation GNS representations. Canonical source Hilbert marking is damped; undamped recovery grows >=sqrt(p) and is unbounded.
6. A fixed bounded Stokes reporter on normalized self-adjoint prime-log eigenvectors would force coefficients ->0 by Bessel and hence flatness, but existing LF/trace-norm/completed-Xi topologies do not produce it. Its bounded assembly is another form of zero-aperture trace-wall removability.

Exact remaining source theorem: construct fixed-tail ideals `H_n(rho)` in both fixed Gamma orientations with `H_n-iota_n H_{n+1}=-beta_{2 Re rho-1}(p_n)e_n`. Tail-Roos classification makes this equivalent to beta in l1 and hence RH. Safe-cone primitive exists uniquely for eps>|t|; missing content is coefficient-faithful continuation to eps=0 (pointwise bounded Gamma-root deconvolution + fixed-ideal landing).

Recorded at EOF of `docs/drafts/pipeline/1-in-progress/cofinal-bockstein-polarized-adelic-stokes.md`. No Lean code added because no dependency-closed paper proof; fabricating `forall rho, SingularStokesFlat rho` would be an RH proof.
