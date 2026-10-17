# Finite divisor families and sharp successor coercivity

Status: **[PROVED HERE]**, Lean-certified as one connected package, **13/100**.

## Actual arithmetic pattern

For d∈ℕ and D⊂ℕ finite, put A={d}∪D and let L=lcm_(e∈A)(e+2).
Define U={n≥1 : some e∈A has e+2 dividing n}. Every spacing is at least
two; A is nonempty; L≥2. Divisibility by every spacing is L-periodic.
Every positive n≡1 (mod L) is outside U: otherwise a spacing divides both
L and n, hence divides 1. Every interval of L consecutive positive integers
contains such a node. Thus there is a least r such that no r+1 consecutive
positive integers all belong to U. Since L∈U, 1≤r<L. Minimality supplies a
run of length r. Periodicity moves its initial node into {1,…,L}, so r is
exactly the maximum active run length in one period, including runs crossing
a period boundary. The definition uses only the actual finite divisor family.

## Infinite physical interpolation

Index nodal data by k≥0, with v_k representing the value at k+1. Let
H_A={v∈ℓ²(ℕ;ℝ):v_k=0 whenever k+1∉U}. It is closed: each forbidden
coordinate is the kernel of a continuous coordinate functional. Thus H_A is
a complete real Hilbert space, with mass M(v)=‖v‖²=Σv_k² and no duplicated
common-grid node. Coordinate masking gives an actual element of H_A for
every ambient ℓ² sequence, by pointwise norm domination.

Let R be the unilateral right shift, (Rv)_0=0 and (Rv)_(k+1)=v_k. It is
an isometry, constructed by orthonormal synthesis of the shifted coordinate
vectors. Let S be orthonormal synthesis of the actual physical L² unit-cell
indicators C_k=1_(k,k+1]. Define E_Av=S(v−Rv). Both maps are bounded, hence
the series Σv_k(C_k−C_(k+1)) converges unconditionally in physical L² to E_Av.
Pairing with 1_(0,n] telescopes to v_(n−1) for n≥1 and zero for n=0.
Every integer trace is therefore prescribed, including all off-union zeros.
For n≥1, logarithmic evaluation at log n gives the same trace. The established
rough primitive and exponential transport theorems apply to this actual L²
velocity, with no extra differentiability or analytic admission premise.

Isometry of S and R gives the exact energy

    ‖E_Av‖² = 2Σ_k v_k² − 2Σ_k v_k v_(k+1).

The adjacent product series is absolutely summable by ℓ² Cauchy–Schwarz.
This is the path Gram form: every active node occurs once, and only consecutive
integer nodes interact, regardless of how many divisor grids contain them.

## Sharp constants from a constructed nilpotent shift

On complex ℓ² let P be the orthogonal coordinate mask of U, and let
T=P R* P. Thus (Tz)_k=z_(k+1) if k+1,k+2∈U, and zero otherwise.
Masking and R* are contractions, so ‖T‖≤1. Iterating the displayed formula
shows that (T^j z)_k can be nonzero only when all j+1 nodes k+1,…,k+j+1
are active. Therefore T^r=0, derived from the actual arithmetic run invariant.
The existing nilpotent-contraction sine theorem gives

    |⟨Tz,z⟩| ≤ c‖z‖²,       c=cos(π/(r+1)).

For the complexification z of real v∈H_A, this pairing is exactly
Σ_k v_k v_(k+1), and ‖z‖²=M(v). Consequently

    (2−2c)M(v) ≤ ‖E_Av‖² ≤ (2+2c)M(v).

There is no assumed spectral gap or admitted block decomposition. The existing
operator theorem follows from the finite scalar sine inequality and its defect
telescoping proof; its contraction and nilpotence hypotheses are proved here.
Since r≥1, 0≤c<1, so the lower coefficient is strictly positive. The resulting
norm lower bound makes E_A an injective antilipschitz continuous linear map.
Completeness of H_A then proves that its physical L² range is closed.

For sharpness choose any longest run a+1,…,a+r and set
v_(a+j−1)=sin(jπ/(r+1)) for 1≤j≤r, with all other coefficients zero.
This is actual finitely supported H_A data and has positive mass because its
first sine coefficient is positive. The boundary sine coefficients at j=0,r+1
vanish, and

    sin((j−1)θ)+sin((j+1)θ)=2 cos θ sin(jθ),  θ=π/(r+1).

Multiply by sin(jθ) and sum j=1,…,r. Each adjacent product occurs twice;
the boundary terms vanish. Thus Σv_kv_(k+1)=cM(v), attaining the lower
constant. Replacing v_k by (−1)^k v_k preserves mass and reverses every
adjacent product, attaining the upper constant. All sums in this argument
are exact finite identities, not numerical experiments.

## Unconditional mismatch and unique minimum

For arbitrary physical L² velocity q put w=q−E_Av and
b_k=2F_w(k+1)−F_w(k)−F_w(k+2), where F_w(t)=∫_0^t w.
Pairing the convergent hat series with w gives a summable scalar series and

    ‖q‖² = ‖E_Av‖² + ‖w‖² + 2Σ_k v_k b_k.

This identity is unconditional on q and actual data v. If q matches every
integer trace of E_Av, then all b_k vanish, so its excess energy is exactly
‖w‖². Equality holds exactly when q=E_Av. All off-union traces are fixed
to zero in this variational corollary; prescribing only union traces defines
a different optimization problem.

## Two-grid recovery and scope

For two spacings m,n≥2 with gcd≥2, every active node is a multiple of their
common gcd; no consecutive active pair exists, and r=1. If gcd=1 and m,n≥3,
Bezout gives adjacent positive multiples. Three consecutive active nodes would
put two at distance at most two in the same divisor grid, impossible for a
spacing at least three; hence r=2. If one spacing is two and the other odd,
an odd multiple and its two even neighbors give a run of length three. Any
four consecutive nodes contain two odd nodes at distance two, which cannot
both be multiples of the other spacing; hence r=3. The factors reduce to
(2,2), (1,3), and (2−√2,2+√2), respectively, recovering package 12.

The finite Dirichlet sine spectrum is classical. Izmestiev's
[A general discrete Wirtinger inequality and spectra of discrete Laplacians](https://arxiv.org/html/1502.03186v1),
§1.3, states the Fan–Taussky–Todd inequality and its sine equality case.
No external novelty claim is made for this parent theory. The package
constructs its sharp arithmetic infinite-trace realization and precise continuum
defect within coprime shear. It makes no unweighted logarithmic H¹, full affine
unitary, or RH assertion.

Corpus audit: the focused finite-grid query returned eight candidate and eight
source entries, all inspected; the deep path query returned twenty candidates,
twenty source entries and one ingredient group, all inspected. Neither supplied
the finite-family theorem. Both searches were partial, with interrupted retrieval
or semantic timeout, unmeasured semantic coverage and incomplete refresh. Exact
source search located the existing generic sine certificate and nilpotent
contraction theorem already used by BiScale's triangular Gram machinery. Those
dependencies are reused; no RH-specific analysis or changes are involved.

## Formal verification

All leaves are under `formal/GaloisForLFunctions/BiScaleUncertainty/`.

| Leaf | Result | Public declarations |
| --- | --- | ---: |
| `FiniteGridRunLength.lean` | Period, maximum run, attainment | 18 |
| `SuccessorSequenceHilbert.lean` | Actual shifts and contractive masks | 12 |
| `IntegerHatTraceExtension.lean` | Infinite interpolation and exact defect | 20 |
| `FiniteGridTraceData.lean` | Closed union data and all traces | 20 |
| `FiniteGridTraceStability.lean` | Nilpotence, sine bounds, closed range | 18 |
| `FinitePathSinePackets.lean` | Exact sine and alternating finite packets | 15 |
| `FiniteGridTraceSharpness.lean` | Nonzero attainers of both constants | 12 |
| `FiniteGridTwoSpacingRuns.lean` | Unconditional two-grid recovery | 9 |

Eight final serial direct `lake --old env lean -o <normal-output> <leaf>` checks
passed with empty diagnostic logs; every output is newer than its source.
The exact 124-declaration axiom audit in `/tmp/finite_grid_axioms.lean` passed:
98 theorems, 23 definitions, two abbreviations and one instance use only
`propext`, `Classical.choice`, `Quot.sound`. Eighteen principal signatures and
35 mathlib API probes were inspected. The masked-input theorem takes arbitrary
ambient ℓ² data, so it exposes the constructed producer without a support premise.

Eight unique umbrella imports and all 123 catalog-supported declarations match
their current source locations. The named instance is separately axiom-audited.
Global `lint --check-generated` exits 1 for fourteen unrelated concurrent
unreachable modules and generated API/overview drift. No package or proof-debt
error was reported. Index refreshed after that check; scoped entries verified.
Exact foreign errors and evidence paths are recorded in the fact ledger.
No full/umbrella build, numerical experiment, added axiom or heartbeat increase.

Trap 10 audit: E_A is a constructed producer with proved exact energy and
competitor error; no Chebyshev estimate or floor-sum admission premise appears.
The field's factorial example needs its smooth term stated explicitly:
T(2N)−2T(N)=2N log 2−(1/2)log N−(1/2)log π+O(1/N), while
T(4N)−4T(2N)+4T(N)=(1/2)log N+(1/2)log(2π)−log 2+O(1/N).
These follow symbolically from [DLMF's log-Gamma expansion](https://dlmf.nist.gov/5.11#E1).
Only the centered first stencil has an O(log N) remainder; the second already
cancels its linear term. This is a scope clarification, not a new formal claim
or a separate counted contribution. The read-only field README is unchanged.
