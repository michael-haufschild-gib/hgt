# Radius-polynomial flux cannot flatten the actual theta border

- **ID:** tt-radius-polynomial-border-flattening
- **Stage:** 5-failed
- **Type:** FALSIFIED mechanism; exact positive survivor formalized
- **Route:** TT, complete signed theta-current matrix
- **Parent:** `../1-in-progress/tt-all-rank-center-flux-induction.md`, C45

## Exact proposed mechanism

The last odd-four border contains the complete signed twelfth reflection
jet J_6(x). The existing odd-three head contains J_1 through J_5 and its
zero-integral center-flux correction. One proposed induction would flatten
that border to the head times a fixed vector, using polynomial multiples
of the existing flux in the physical radius r=2x.

This mechanism fails even if arbitrary fixed multiples of all J_0,...,J_5
are allowed. The theorem does not refute matrix-flux positivity in general,
the parent conjecture C45, or RH.

## Exact positive survivor and paper proof

Put q(x)=pi*exp(2x), f(x)=thetaCuspSourceTerm(x,1),
J_k(x)=(-1)^k*thetaCuspNativeReflectionJet(2k,x),
w_a(r)=r*sinh(a*r), and
F_a(r)=r^2*sinh(a*r)*Phi(r/2)^2, with Phi the complete theta source.
For any a>0, real polynomial P, and six real coefficients v_k, define

    B(x)=J_6(x)-sum_(k<6) v_k*J_k(x)
         -(P(r)*F_a(r))'|_(r=2x)/w_a(2x).

The exact invariant is

    B(x)/(f(x)^2*q(x)^6) -> 2724986880.

Consequently B(x)>0 eventually, so B cannot vanish on a cofinal ray.
The constant is the already known sixth Gaussian moment, not a numerical
estimate, optimized bound, or experimentally chosen value.

The corpus already proves J_k/(f^2*q^k) converges through k=6. Every lower
jet therefore vanishes after division by f^2*q^6. It also proves
F'_a/(w_a*f^2*q^5)->0 and Phi/f->1. The product rule gives

    (P*F_a)'/(w_a*f^2*q^6)
      = [(r*P')/q^6]*(Phi/f)^2
        + [P/q]*[F'_a/(w_a*f^2*q^5)].

Both terms tend to zero because polynomial radius growth loses to positive
powers of q. Subtracting these limits proves the invariant, with every
actual Gaussian integer atom retained through the corpus source limits.

## Formal status

`ThetaCuspPolynomialFluxBorderDegree.lean` contains the source-specific
flux derivative limit, exact residual limit, eventual strict positivity,
and impossibility of cofinal vanishing. Targeted
`lake build --old +GaloisForLFunctions.RHTower.ThetaCuspPolynomialFluxBorderDegree`
passed. The leaf is imported by `RHTower.lean`; no umbrella build ran.
Final `lake env lean GaloisForLFunctions/RHTower/ThetaCuspPolynomialFluxBorderDegree.lean`
passed (exit 0). Both checks emitted one informational `ring_nf` suggestion,
not a failed proof or leaf warning. Separate `/tmp` axiom checks for all
four public theorems returned exactly `[propext, Classical.choice, Quot.sound]`:

- `thetaCuspRadiusPolynomialFlux_deriv_scaled_six_tendsto_zero`;
- `thetaCuspPolynomialFluxBorderResidual_scaled_tendsto`;
- `thetaCuspPolynomialFluxBorderResidual_eventually_pos`;
- `thetaCuspPolynomialFluxBorderResidual_not_eventually_zero`.

No added axioms, proof holes, heartbeat changes, or numerical experiments.
Index refresh passed. Global `lint --check-generated` returned 1 on fourteen
unrelated unreachable modules and three stale generated indexes after
concurrent changes; it reported no error in this leaf. The repository-wide
gate is not claimed clean. All owned checking processes exited.

## What survives for the RH proof

The invariant identifies a mismatch of Gaussian degrees. It does not show
that increasing a radius-polynomial degree can help: every finite degree
is covered. C46 in the parent card instead tests a Gaussian-scale flux
with a forced zero at the source center. Its proposed leading cancellation
is not yet a proof of the complete signed remainder or integrated current.
