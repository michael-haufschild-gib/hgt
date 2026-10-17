# Global plastic minimizers in nonzero coherent classes

- **ID:** global-coherent-fiber-plastic-minimizer
- **Stage:** 5-failed, closure audit pending
- **Type:** FALSIFIED (paper); exact positive survivor awaiting Lean audit
- **Source:** ../1-in-progress/hyperbolic-multiplier-lifting-2026-10-17.md
- **Statement tested:** Every actual odd full-fold coherent class has a source
  minimizing the original plastic functional.

## Exact obstruction

Write P for the full folded sinh source and O for its signed hyperbolic moment.
Every member g of its actual compact continuous odd coherent class satisfies
Q(g)=2J(g)-2O², with J(g)>=0 and J(g)=0 iff g=0. The class has exact
infimum -2O², so attainment requires the zero source and hence P=0.
Positive curvature along every nonzero zero-fold line does not imply a
minimizer on the entire coherent class.

## Strongest positive survivor

Let d=log2, R be the canonical annular representative, S(u)=sinh(u/2)R(u),
L_n=(n+4)d, r_n(u)=S(u-L_n)/sinh(u/2), and E_n=odd(r_n).
These are actual compact continuous sources, constructed without analytic
premises. Their support lies in (n+1)d<|u|<(n+7)d. Their full fold, signed
moment and exact coherent price equal those of the input odd source.

With H=integral S² and M=integral_(0,infinity) levyCoshKernel, the explicit
unconditional bounds are

- h_(E_n)(0)<=2H/((n+1)d)²;
- 0<=Q(E_n)+2O²<=8MH/(d²(n+1)²).

Consequently -2O² is the greatest lower bound on every actual coherent class.
It is attained iff P=0. The class contains a source with negative plastic
value iff O is nonzero. M equals half the known plastic origin potential,
so the coefficient is completely source-defined and explicitly evaluated.

## New insight and boundary

The full coherent fold fixes the plastic infimum but cannot prevent loss of
attainment through outward source escape. This gives an actual minimizing
family and the exact sign boundary, beyond the nonattainment obstruction.
No fixed source-energy normalization, prime-grid blindness, smoothness beyond
continuity, or positivity on arbitrary odd sources is imposed or asserted.

## Proof status

- [x] Well-posed source-pure minimization question.
- [x] Dependency-closed paper obstruction and positive survivor.
- [ ] Exact source construction and full variational capstone Lean audit.
- [ ] All public theorem axiom audits and integration checks.

Implementation modules, currently awaiting audit:
`formal/GaloisForLFunctions/BiScaleUncertainty/OutwardCoherentEscape.lean` and
`formal/GaloisForLFunctions/BiScaleUncertainty/CoherentFiberPlasticInfimum.lean`.
No external novelty or repository-wide clean-gate claim.
