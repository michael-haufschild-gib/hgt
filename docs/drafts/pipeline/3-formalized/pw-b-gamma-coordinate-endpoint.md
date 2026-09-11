# PW-B signed coordinate endpoint and arithmetic mass separation

- **ID:** PW-B-GAMMA-COORDINATE-ENDPOINT-2026-09-11
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean 4)
- **Statement:** The actual weighted shifted source `x*M_(-1)` and weighted coordinate derivative `x*M'` are globally integrable in positive-ray Lebesgue measure, with zero mass. The full arithmetic current has exact mass defect `Gamma(3/2)` from every constant complex combination of `M` and `x*M'`, and their `L1` distance is at least `Gamma(3/2)>0`.

## Actual source and signed assembly

Keep `Q(x)=sqrt(x)*exp(-x)` for `x>0`,
`M_b(x)=sum_n mu(n)*exp(-b*log(n))*Q(n*x)`, and `M=M_0`.
The [coordinate-generator audit](pw-b-gamma-coordinate-generator.md) proves

`x*partial_x M_b=M_b/2-x*M_(b-1)`.

Its absolute atom-integral admission is exactly `Re(b)>0`; at zero this
estimate fails. The present proof admits the complete signed source there.
It does not assert integrability of the unweighted `M_(-1)`.

Set `R(x)=x*Q(x)` and `S(n)=sum_{j<=n} mu(j)`. Retain every signed Abel atom

`B_R(n,x)=S(n)*(R(n*x)-R((n+1)*x))`.

The original Gamma integral directly proves the admitted second moment
`integral x^2*norm Q(x) dx=Gamma(7/2)`. No analytic continuation supplies
this value. The known first moment is `Gamma(5/2)`.
For positive `r,x`, the exact adjacent difference decomposition and the
previous source estimate give

`norm(R((r+1)*x)-R(r*x))`
`<= x*norm Q((r+1)*x)+x*norm Q(r*x)+r*x^2*norm Q(r*x)`.

All three terms are integrable. Positive dilation of the first and second
moments, followed by `(r+1)^2>=r^2`, gives

`integral norm(R((r+1)*x)-R(r*x)) dx`
`<= (2*Gamma(5/2)+Gamma(7/2))/r^2`.

The zero-index Abel atom vanishes. Multiplying the bound by `abs S(n)`
and using the corpus's unconditional inverse-square Mertens summability
proves summability of all Abel atom norm integrals. Thus their complete
sum is globally admitted, provided it is identified with the literal source.

## Exact finite identity and terminal

The original polynomial Gamma moments also imply
`sum_n n^k*norm R(n*x)<infinity` for every fixed `x>0` and natural `k`.
The bound `abs S(n)<=n+1` then makes the complete terminal sequence
`S(n)*R(n*x)` summable, which is stronger than its required convergence to zero.
The same moment estimates admit both adjacent sequences and hence the
pointwise Abel series.

Finite summation by parts gives exactly

`sum_{n<N} B_R(n,x)`
`=sum_{n<=N} mu(n)*R(n*x)-S(N)*R(N*x)`.

The actual coefficient shift identifies `mu(n)*R(n*x)` with
`x*A_(-1)(n,x)`, including zero index. The full original coefficient series
is summable at every positive `x`. Taking the two justified limits proves

`x*M_(-1)(x)=sum_n B_R(n,x)`.

This is equality with the literal source, not a replacement definition.
It transfers global integrability from the complete signed Abel assembly.

## Exact mass and nontrivial positive survivor

Positive dilation and the Gamma recurrence give, for every index,

`integral B_R(n,x) dx=3/2*integral B_Q(n,x) dx`,

where `B_Q` is the already-admitted Abel atom for `M`.
Both norm-integral series are summable, so integration through both sums
is valid. The existing zero mass of `M` now gives

`integral x*M_(-1)(x) dx=0`.

The actual coordinate equation at zero is
`D(x)=x*M'(x)=M(x)/2-x*M_(-1)(x)`. Both terms are admitted, so
`D in L1(dx)` and `integral D=0`.
The [complete logarithmic-current theorem](pw-b-gamma-logarithmic-current.md)
already proves `E=partial_b M_b|0 in L1(dx)` and `integral E=Gamma(3/2)`.
Consequently, for every pair of complex constants `a,c`,

`integral (a*M+c*D) dx=0`,
`integral (E-a*M-c*D) dx=Gamma(3/2)`,
`integral norm(E-a*M-c*D) dx>=Gamma(3/2)>0`.

The last inequality follows from the norm-of-integral bound on the actual
complete residual. It rules out approximation with arbitrarily small L1
error by these combinations, as well as pointwise equality on the positive ray.
No claim is made that this lower bound is attained within their linear
span. The exact nonzero mass and positive norm gap are the retained positive
survivor of the rejected local identification.

## Route scope and next attack

PW-B remains active; RH remains unproved. The chain is literal PW response
-> FE imbalance -> positive Deninger Ward transmutation -> independently
source-forced fixed-grade balance -> RH. The present result closes signed
admission of the coordinate response and excludes constant rescaling or
mixing with the original source as the missing arithmetic identification.
It does not exclude a nonlocal transmutation, a new compensating source,
or a separately justified physical pairing.

The next candidate is an actual translation representation of the coefficient
current. For positive `x` and nonnegative `h`, define provisionally

`T_h f(x)=sqrt(x)/sqrt(x+h)*f(x+h)`.

The original Gamma atoms suggest `T_h Q(n*x)=exp(-n*h)*Q(n*x)`, with the
notation meaning that T acts on the function `x -> Q(n*x)`. Thus the corpus's
convergent Frullani formula suggests

`E(x)=integral_{h>0} (T_h M(x)-exp(-h)*M(x))/h dh`.

For positive integer n the exponential difference has one sign, so its
absolute Frullani mass is `log(n)`. Existing polynomial Gamma summability
suggests a common summable atom-integral bound for every fixed positive x.
Prove the actual translation identity, full-source interchange and all
admissions before interpreting this expression as a generator. Fixed-x
admission alone does not settle a joint global integral or the spectral
Ward identification. This candidate is not formalized in the present leaf.

## Search and method audit

Four complete deep method results, with candidate lemmas, source arguments,
ingredient groups and freshness metadata, are saved in the
[search artifact](../1-in-progress/pw-b-gamma-coordinate-endpoint-searches.json).
All report partial coverage, respectively 723285, 723285, 723325 and 723325
indexed declarations. The usable methods are exact finite Abel summation,
convergent Gamma moments, polynomial moment bounds and the norm-of-integral
inequality. The next candidate's exact convergent Frullani theorems were
located by corpus text search in `HTGeometry/FrullaniIntegral.lean` and read.

Broad entrainment and elasticity web queries initially returned older or
irrelevant results. Direct arXiv search, ordered by announcement date,
returned September2026 papers. Primary sources read include
[reciprocity and mechanical response](https://arxiv.org/html/2609.04169v2)
(September3, revised September6) and
[ensemble-dependent polymer elasticity](https://arxiv.org/abs/2609.04856)
(September4). The former's Theorem2 and proof turn an inaccessible response
component into a norm lower bound; here the actual integral functional
supplies a related separation argument in L1, proved entirely in Lean.
Its mechanical symmetry and passivity assumptions are not imposed on this
arithmetic source. The second paper's abstract compares responses under
different ensembles and an explicit weak-bending approximation; it supplies
no source-domain or parameter identification here. No external theorem is
a Lean premise, and no numerical experiments were run.

## Lean audit

Module: `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingParikhWilczekGammaMobiusCoordinateEndpoint.lean`.
The leaf has 384 lines, 25 public theorems and two definitions.
Its closed capstone is `pwGammaMobiusCoordinateEndpoint_closed`.
Scratch and direct `lake env lean` checks passed without warnings. The
targeted `lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingParikhWilczekGammaMobiusCoordinateEndpoint`
passed. Scratch `#print axioms` audited all 27 public declarations: only
`propext`, `Classical.choice`, and `Quot.sound` occur. Formal lint, index
regeneration, all-name uniqueness, generated API coverage and task-scoped
file checks passed. Umbrella wired; no full/umbrella build or numerical
experiment ran. All owned Lean and research processes finished. RH remains
unproved; the goal remains active.
