# SQB exact entire-forcing kernel and source-family obstruction

Status: 29 public declarations formalized, individually built and axiom-audited.
RH remains unproved. The frontier map is read-only.

Full chain: original modular source → entire-transform operator → independent
occurrence at every full Xi parameter → critical-line classifier → RH.

## Exact positive kernel classification

Use the actual original native operator A, covariance B=A^(-1), entire covariance
C=g(B), and entire operator T=C^(-1)−2. For an actual Xi copy rho, put

`e=1+(rho/2)(1−rho/2)`, `mu=F((rho/2)(1−rho/2))`,

`a=1+nativePartner(Im rho)=5/4+(Im rho)^2/4`, `b=a^(-1)`.

The actual bounded nonreal resolvent is R_e=(A−e)^(-1). The previously audited
forcing transport is `K=(I−(2+mu)C)R_e`. For every vector f in the original
native Hilbert space, the new theorem proves

`K f=0  iff  f=0 or (Re rho=1/2 and B f=b f)`.

The full residual before resolvent transport has the same exact kernel:

`v−(2+mu)C v=0  iff  v=0 or (Re rho=1/2 and B v=b v)`.

On the original A-domain, `B v=b v` is equivalent to `A v=a v`. These are
classifications of actual eigenspaces. They do not assert that a nonzero
forcing or source occupies an eigenspace, or that all Xi copies are critical.

## Continuous zero sets determine vector kernels

The general analytic input is a new theorem for a bounded self-adjoint operator
B and real continuous spectral symbols f and g. If every spectral zero of f
is a zero of g, then

`f(B)v=0 implies g(B)v=0`.

For n≥0 use the continuous nonnegative regularizer

`r_n(x)=g(x)^2/(1+n f(x)^2)`.

Its denominator is strictly positive. It decreases pointwise to zero: where
f vanishes, g vanishes; elsewhere the denominator tends to infinity. The
spectrum is compact, so Dini's theorem gives uniform convergence to zero.
The continuous functional calculus norm estimate gives `||r_n(B)||→0`.

The exact scalar factorization

`g(x)^2−r_n(x) = [n g(x)^2 f(x)/(1+n f(x)^2)] f(x)`

has a continuous bracket. Thus f(B)v=0 implies `g(B)^2 v=r_n(B)v→0`, hence
g(B)^2 v=0. Self-adjointness of g(B) gives
`||g(B)v||^2=<g(B)^2 v,v>=0`. This proves actual vector-kernel inclusion.
No bound on g/f near its zeros and no spectral gap is used.

Equal spectral zero sets give equal vector kernels. Applying this result to
`f(x)−c` and `x−b` proves the exact fibre theorem:

`f(B)v=c v iff Bv=bv`,

whenever `f(x)=c iff x=b` on the original real spectrum. The theorem permits
the eigenspace to be zero and assumes no occurrence.

## The actual reciprocal symbol fibre

The inspected entire symbol is

`g(x)=1/(F(x^(-1)−1).re+2)` for x>0, and g(x)=0 otherwise.

For every nonzero real ordinate t, let `b=(1+nativePartner(t))^(-1)>0`.
Then `g(x)=g(b)` with x≥0 forces x>0 because g(b)>0. Taking reciprocals gives
equality of the real parts of `F(x^(-1)−1)` and `F(nativePartner(t))`.
Both values are real. The existing complete real-preimage classifier for F
therefore forces `x^(-1)−1=nativePartner(t)`, hence x=b. The converse is immediate.
This includes the covariance accumulation point zero and retains the entire
symbol, without polynomial replacement or approximation.

Positivity of B puts its spectrum in [0,infinity). The general fibre theorem
therefore identifies the actual C-eigenspace with the original B-eigenspace.
Every actual Xi copy has nonzero ordinate, so every scalar input is discharged.

## Full-Xi classification and resolvent transport

If a nonzero entire-domain vector w satisfies Tw=mu w, self-adjointness forces
Im mu=0. The actual form lower bound `Re<Tw,w>≥−||w||^2` also gives Re mu≥−1.
The existing full open-strip range classifier for F then forces Re rho=1/2.
Reality alone is not used in place of that full range constraint.

On the critical line, the exact symbol identity is `2+mu=g(b)^(-1)`, so
`v−(2+mu)Cv=0` is precisely `Cv=g(b)v`. The fibre theorem gives Bv=bv.
Conversely that B-eigen-equation gives the full entire residual zero when rho
is critical. Zero vectors supply the remaining disjunct.

The native resolvent commutes with B. To prove this directly on the actual
closed domain, put v=R_e f. Applying B to `(A−e)v=f` gives `v−eBv=Bf`.
The vector Bv is in the original A-domain and ABv=v, so it solves
`(A−e)Bv=Bf`. The actual resolvent R_e(Bf) solves the same equation.
Injectivity of the nonreal shift identifies the two responses.

Hence `B R_e f=b R_e f` is equivalent to `R_e Bf=R_e(bf)`, and injectivity
of R_e makes it equivalent to Bf=bf. It also identifies `R_e f=0` with f=0.
Applying the preceding residual classification proves the displayed exact
kernel of K for every forcing.

## Original source does not occupy that kernel

Let V be the complete corrected original source and H its complete cutoff
forcing. The previous graph audit proves `(A−e)V=H` in the original domain,
H≠0, V≠0, and R_e H=V.

The original scalar field has nonzero horizontal mean at every positive height.
Choose a nonzero value on height 3/2 and move it into the closed modular cell.
The full modular height bound keeps the resulting height at most 3/2, strictly
below the cutoff transition at height 2. Modular invariance and the exact
low-cutoff identity preserve the nonzero source value. Thus R has a nonzero
closed-cell value at a point where the original H is zero.

If H=cV in the native Hilbert space, the actual almost-everywhere representatives
and their continuity give the same identity on the whole closed cell. At the
constructed point it reads `0=cR(z)`, so c=0, contradicting H≠0. Consequently
H is not any scalar multiple of V. The forced native equation then excludes
`A V=lambda V` for every complex lambda.

If the original entire residual G were zero, the exact kernel classifier would
put V in the recovered B-eigenspace. Since V is already in the actual A-domain,
it would be a native eigenvector, contradicting the preceding source theorem.
Therefore for every actual Xi copy, including every critical copy,

`G≠0`, `K H≠0`, and `||(T−mu)U||>0`, where `U=CV/||CV||`.

The final strict inequality uses the already proved positive denominator and
exact normalized forcing formula. This fixed-vector theorem alone supplies no
uniform bound across arbitrary source families or all Xi copies. The actual
original cutoff family is settled by the following graph-limit theorem.

## Actual normalized cutoff family

Let V_n be the complete compact modular approximants constructed in the previous
native graph audit. They satisfy V_n→V in native Hilbert norm. Each V_n is nonzero:
the original nonzero point below height 2 lies where every cutoff beta_n equals
one. Equality of a core vector to zero would, by its actual representative and
continuity, force its field to vanish at that retained point.

Injectivity of C gives ||C V_n||>0 for every n. Define actual entire-domain vectors

`W_n=C V_n`, `U_n=W_n/||W_n||`.

Every U_n has norm one. The entire operator's exact inverse action gives

`T W_n=V_n−2 C V_n`,

`||(T−mu)U_n||=||C V_n||^(-1)||V_n−(2+mu)C V_n||`.

Since C is bounded, C V_n→C V. The limit norm is strictly positive, so the
reciprocal normalization factors converge as well. Combining these limits with
the exact action above proves both

`U_n→U` and `T U_n→T U`

in the original native Hilbert norm. Thus these are actual normalized graph
approximants to the fixed source. Continuity of subtraction and norm proves
the exact limiting residual

`||(T−mu)U_n|| → ||(T−mu)U|| > 0`.

Uniqueness of limits excludes convergence of this actual residual sequence to
zero for every Xi copy, including critical copies. The theorem supplies the
complete unit-domain construction and positive graph-limit value; it does not
exclude arbitrary different approximate families. The mere existence of a
compact modular exhaustion therefore does not supply spectral approximation.

## Lean modules and verification

| Module | Public declarations | Sole-target final build |
| --- | ---: | ---: |
| HTGeometry.CfcZeroSetKernel | 3 | 3.3s |
| RHTower.SelbergScatteringEntireEigenvectors | 9 | 6.1s |
| RHTower.SelbergScatteringSourceNonvanishing | 6 | 6.7s |
| RHTower.SelbergScatteringApproximateSourceResidual | 11 | 8.8s |

All module names have prefix `GaloisForLFunctions`. Generic kernel declarations
use namespace `GaloisForLFunctions.HTGeometry`; the three source modules use their
matching namespaces under `RHTower`.

Every complete scratch passed `lake env lean` with no diagnostics. Each final
`lake build MODULE` compiled only its named module, with preflight and every
Built line checked. All 29 public axiom reports contain only the standard
`propext`, `Classical.choice`, and `Quot.sound` dependencies. Each new umbrella
import occurs once; all public declarations are indexed. No proof placeholder,
added axiom, unsafe declaration, numerical experiment, or computed proof input
was used. No full or umbrella build was run.

Audit files: `/tmp/sqb11_{kernel,eigen,source,approx}_build.log`,
`/tmp/sqb11_axioms.log`, `/tmp/sqb11_approx_axioms.log`,
`/tmp/sqb11_index_audit.json`, `/tmp/sqb11_final_lint.log`.

The final full formal lint invocation reports six unrelated missing umbrella
imports: `GaloisForLFunctions.RHTower.FokasLenellsSecondTimeBounds`,
`GaloisForLFunctions.RHTower.FokasLenellsSecondTimeDifferentiability`,
`GaloisForLFunctions.RHTower.FokasLenellsSecondTimeForcing`,
`GaloisForLFunctions.RHTower.FokasLenellsSecondTimeInverse`,
`GaloisForLFunctions.RHTower.FokasLenellsSecondTimeMultiplier`,
`GaloisForLFunctions.RHTower.FokasLenellsSecondTimeSymbols`.
The four new modules have no lint errors. Those other-task modules were left untouched.

## Remaining RH obligation

The [fixed corrected-source and original cutoff-family mechanism](../5-failed/sqb-fixed-corrected-source-exact-occurrence.md)
is closed negatively, with the complete kernel classification and exact positive
normalized graph limit as its audited positive survivors. The original graph and forcing transport remain valid.
SQB still requires an independent full-Xi occurrence producer, potentially
using a different vector or a controlled approximate family. No conclusion
about that broader producer, and no RH proof or falsification, follows here.
