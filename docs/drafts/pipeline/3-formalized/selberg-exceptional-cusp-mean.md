# Actual exceptional Maass constant term

- **ID:** SELBERG-EXCEPTIONAL-CUSP-MEAN
- **Stage:** 3-formalized
- **Parent:** [Constructive Selberg loop](../1-in-progress/selberg-quarter-conjecturing-loop.md), cycle 12.
- **Scope:** Every positive principal congruence level and the infinity cusp. This establishes constant-term vanishing from the existing Maass decay definition, not the Selberg spectral bound.

## Exact result

Let `L=N+1`, let `0<lambda<1/4`, and let `f` be an actual `MaassCuspEigenform (realImage (Gamma L)) lambda` as defined in `MaassCuspAutomorphicCorrespondence`. At every positive height,

`A(y) = integral_(0,L] f(x+i*y) dx = 0`.

The integral is unnormalized: it is `L` times the usual constant Fourier coefficient. The theorem introduces no extra regularity, periodicity, differential-equation, or decay assumptions on this Maass type. The spectral interval is the domain of this auxiliary theorem; the existence or nonexistence of eigenforms in that interval is not settled.

## Dependency-closed paper proof

1. The matrix `T^L` belongs to the actual principal congruence subgroup. The existing invariance field therefore gives horizontal period `L`.
2. The Maass record supplies real C² chart regularity. On a compact rectangle around any positive height, the vertical derivatives are bounded and horizontal slices are integrable. Dominated differentiation gives `A'` and `A''` as the integrals of the corresponding actual chart derivatives. C² suffices; C-infinity is not assumed.
3. Differentiating periodicity gives periodicity of the first horizontal derivative. The fundamental theorem of calculus therefore makes the integral of the second horizontal derivative zero.
4. Integrating the actual positive hyperbolic eigen-equation yields `-y²*A''(y)=lambda*A(y)`.
5. The identity scaling matrix in the defining cusp predicate gives a bound on `|f(x+i*y)|` that is uniform in `x` at sufficiently large `y`. Integrating this bound over fixed finite width gives `A(y)->0`.
6. Put `H(t)=A(exp(t))`. The actual chain rule gives `H''-H'+lambda*H=0` and `H(t)->0`.
7. For roots `a=1/2+nu`, `b=1/2-nu`, with `nu=sqrt(1/4-lambda)`, one has `0<b<a`, `a+b=1`, and `a*b=lambda`. Direct differentiation makes `(H'-b*H)*exp(-a*t)` constant. Swapping the roots supplies a second constant. Subtracting the recovered identities proves

   `(a-b)*H(t)=C_a*exp(a*t)-C_b*exp(b*t)`.

8. Multiplying by `exp(-a*t)` and taking the decay limit gives `C_a=0`. Multiplying the remaining identity by `exp(-b*t)` gives `C_b=0`. Since `a-b` is nonzero, `H=0`. Every positive height is an exponential, so `A=0`.

## Lean implementation

- `GaloisForLFunctions.RHTower.SelbergMaassFourierMean`: actual congruence periodicity, finite-regularity differentiation, horizontal cancellation, Euler equation, and decay.
- `GaloisForLFunctions.RHTower.SelbergExceptionalCuspMean`: integrating-factor constancy, forced exponential expansion, decay rigidity, and the capstones `maassMean_exceptional_zero` and `maassMean_subquarter_zero`.

The general ODE lemmas have their usual explicit analytic hypotheses. The final Maass capstones discharge those hypotheses from the existing Maass type. They do not package an assumed Selberg conclusion into an interface.

## Verification

- Both complete scratch proofs passed `lake env lean` without warnings.
- Both final source files passed direct `lake env lean` checks without warnings.
- Both are wired into `RHTower.lean`; no umbrella build ran.
- Targeted final `lake build` commands passed, rebuilding one target each (dependency graphs: 3103 and 3118 jobs).
- Eleven scratch `#print axioms` checks report only `propext`, `Classical.choice`, and `Quot.sound`.
- Repository-wide lint and index status are recorded in the parent verification log.

## Next mathematical step

The proved constant-term elimination permits positive horizontal frequencies at infinity. It does not yet assemble the nonzero Fourier modes into the cusp Hardy inequality. Integral-cusp covariance, approximation and energy convergence, and a congruence-uniform compact-core gluing estimate remain separate obligations.
