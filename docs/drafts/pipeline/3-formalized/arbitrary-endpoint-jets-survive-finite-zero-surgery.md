# Arbitrary endpoint jets survive finite zero surgery

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Obstacles:** B13, B112; arithmetic detection of finite exceptional divisors.
- **Target:** For every finite endpoint jet order and every positive strip width, an entire finite rational modification of actual `xi` preserves that jet at zero and one, reflection, reality, and vertical normalization, while adding off-line zeros inside the prescribed width about the critical line.
- **Contribution count:** One (#14), including donor clustering, polynomial root confinement, sharp degree rigidity, and entire surgery.
- **Novelty boundary:** The two-quartet construction preserves the first jet for arbitrary four donor pairs. Theta-profile surgery preserves arbitrary jets through broader deformations; multi-quartet passport models use a different entire source. Neither supplies this finite rational modification of actual `xi`.

## Proof

For every `ell>0`, every `n`, and every lower height `M`, some interval `[H,H+ell]` with `H>=M` contains `n` distinct simple critical zeros. Otherwise partition positive ordinates by `floor(gamma/ell)`. Bins beyond `M+ell` contain fewer than `n` zeros, while the initial segment is finite. Since at most `floor(T/ell)+1` bins occur below `T`, the simple critical count is bounded linearly in `T`. This contradicts the unconditional bound `T log T/(72 pi)` in `RHTower.eventually_superlinear_xiSimpleCriticalZeroCount`. Taking a subset gives exactly the desired number of donors.

Choose an even number `n>=2` of distinct actual critical-line donor pairs in a short high ordinate interval. Write their endpoint parameters as `a_j` with `|a_j-A|<=w`, `A>7w>0`, and set
`D(q)=product(q+a_j)`, `epsilon=2(2w)^n/(A-w)^(n-1)`,
`N(q)=D(q)-epsilon q^(n-1)`.
Then `N-D` vanishes to order `n-1` at `q=0`, and both polynomials are monic of degree `n`. Substitution `q=s(s-1)` preserves endpoint jets through order `n-2`.

For real negative `q`, outside the interval containing the donor roots, `D(q)>=0`; inside, `|D(q)|<=(2w)^n`. The added term is positive and at least `2(2w)^n`, so `N(q)>0` there. At any complex root, writing `r=|q+A|`, the equality of norms gives `(r-w)^n<=epsilon(r+A)^(n-1)` when `r>w`. If `r>=5w`, then
`(A-w)(r-w)-2w(r+A)=(A-3w)(r-5w)+2w(A-7w)>0`.
Raise this strict inequality to power `n-1`, multiply by `4w`, and use `4w<=r-w`; the result contradicts the root inequality after multiplying by `(A-w)^(n-1)`. Thus every root lies in `|q+A|<5w`, hence has negative real part; the preceding real-axis positivity excludes every real root.

Put `A=H^2+1/4`. For `s=1/2+x+iy`,
`|s(s-1)+A|^2-4H^2 x^2=(x^2+y^2-H^2)^2>=0`.
The root disc therefore gives `|x|<5w/(2H)`. Short ordinate clusters make this width arbitrarily small. Cancelling the distinct donor factors against `xi` gives an entire surgery without any simplicity assumption.

More explicitly, for donor ordinates in `[L,L+ell]`, take `A=(L^2+(L+ell)^2)/2+1/4` and `w=L ell+ell^2/2`. If `L>=16` and `0<ell<=1/8`, then `A>7w`, `w<=3L ell/2`, and `sqrt(A-1/4)>=L`; consequently every new zero has transverse depth below `4ell`. Choosing `ell=min(delta/8,1/8)` places all new zeros within depth `delta` and inside the critical strip.

Write the entire donor quotient as `xi(s)=G(s)D(s(s-1))` and put `F(s)=G(s)N(s(s-1))`. Then `F-xi=-epsilon (s(s-1))^(n-1)G` globally. This proves equality of all endpoint derivatives through order `n-2`. Both functions are real under conjugation and invariant under `s -> 1-s`, by their polynomial factors and the identity theorem off the donor set. The numerator's positive degree supplies a complex root; its nonreal `q`-coordinate yields an off-line quartet. Monicity and equal degrees give vertical ratio limit one. Choosing even `n>=K+2` preserves any prescribed finite jet order `K`.

The endpoint order is sharp for this degree: monic degree-`n` numerators and denominators have difference of degree at most `n-1`. Agreement through order `n-1` at `q=0` forces their equality, whereas the displayed construction achieves agreement through order `n-2`.

Normalization refers to the rational multiplier, including on the critical vertical line; the totalized quotient `F/xi` is not that multiplier at donor zeros. No Dirichlet-series structure is asserted for the modified function. Rational-multiplier rigidity for ordinary Dirichlet series is already covered by `GaloisForLFunctions.lseries_polyWeightFamily_coeff_eq_zero` and is not a new contribution here.

## Lean certificate

Paths are relative to `formal/GaloisForLFunctions/ArithmeticPositiveDuality/`.

| Module | Capstone |
|---|---|
| `ClusteredEndpointPolynomial.lean` | `exists_clusterSurgeryPolynomial_root`, `monic_eq_of_endpoint_jets` |
| `ArbitrarilyLargeCriticalDonorClusters.lean` | `exists_critical_donor_cluster` |
| `ArbitraryEndpointJetsSurviveFiniteSurgery.lean` | `arbitrary_endpoint_jets_survive_finite_xi_surgery` |

For each `K` and `delta>0`, the capstone produces `2K+2` distinct positive actual critical donor pairs and an entire function preserving derivatives through order `2K` at both endpoints. Every replacement zero has nonzero imaginary part, lies off the critical line inside `0<Re s<1`, and has transverse depth below `delta`. The rational multiplier tends to one on every vertical line.

All three modules pass direct `lake --old env lean` audits without warnings. The four listed capstones use only `propext`, `Classical.choice`, and `Quot.sound` transitively. All modules are umbrella-wired. No RH hypothesis or unproved analytic input is present.

Finite endpoint jets cannot detect finite exceptional divisors within this analytic class. RH and the original finite-defect obstacles remain open.
