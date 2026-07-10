# Exact order-zero defect of archimedean sampling

- **ID:** archimedean-sampling-total-variation-defect
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Grade:** BRIDGE / quantitative strengthening; not new scientific knowledge
- **Source:** `../../3-formalized/not_new_scientific_knowledge/archimedean-theta-seam-sampling-quotient.md`;
  `../../../../formal/GaloisForLFunctions/RHTower/XiThetaCriticalTrace.lean`;
  `../../../../formal/GaloisForLFunctions/RHTower/XiThetaSourceSeam.lean`;
  Riesz--Markov representation and regularity of finite Radon measures
- **Statement:** In the canonical order-zero completion `T = C_0(R)` with the supremum norm,
  sampling a positive absolutely continuous archimedean measure on a closed null set has exact
  defect equal to the measure's full mass.  Symmetric completion doubles the absolute defect, while
  functional-equation symmetry preserves the normalized defect at its maximal value `1`.

## Scope of the norm choice

The standard smooth compactly supported or Schwartz test space used by an explicit formula is a
locally convex space controlled by a family of derivative seminorms.  It has no distinguished
single Banach norm.  A claim that `H^1`, `W^{1,1}`, or one chosen Schwartz seminorm is *the*
canonical explicit-formula norm would therefore be false without extra operator-theoretic input.

For the present comparison, both channels are order-zero distributions:

- the archimedean channel is integration against a finite Radon measure;
- the sampling channel is evaluation against point masses.

The canonical order-zero norm is consequently

`T = C_0(R)`, `||phi||_T = ||phi||_infinity`.

This choice is characterized by Riesz--Markov: `T*` is the space of finite signed Radon measures
with the total-variation norm.  It is also the supremum-norm completion of the smooth compactly
supported test core.  The theorem below has the same supremum when the witnesses are restricted to
smooth compactly supported tests.

## General theorem

Let `X` be a locally compact normal space, let `mu` be a finite positive Radon measure on `X`, and
let `Lambda` be a closed set with `mu(Lambda)=0`.  Define

`S_Lambda(phi) = phi restricted to Lambda`,

`I_Lambda = ker(S_Lambda) = {phi in C_0(X) : phi|_Lambda = 0}`,

and the order-zero sampling defect

`Delta(mu,Lambda) = sup { |integral phi dmu| : phi in I_Lambda, ||phi||_infinity <= 1 }`.

Then

`Delta(mu,Lambda) = mu(X) = ||mu||_TV`.                                  (1)

Equivalently, among all finite signed measures `nu` supported on `Lambda`,

`inf_nu ||mu-nu||_TV = ||mu||_TV`,                                      (2)

and the infimum is attained by `nu=0`.  Thus the best bounded *linear* reconstruction from samples
is no better than discarding the samples.

The same exact value governs arbitrary nonlinear reconstruction.  If `F` ranges over all maps from
the sample range to `R`, with no regularity or linearity assumption, then

`inf_F sup_{||phi||_infinity <= 1} |integral phi dmu - F(S_Lambda(phi))|
  = mu(X)`.                                                              (3)

## Proof `[PROVED HERE]`

The upper bound in (1) is immediate:

`|integral phi dmu| <= ||phi||_infinity mu(X) <= mu(X)`.

For the reverse inequality, fix `epsilon>0`.  Inner regularity and `mu(Lambda)=0` give a compact
set `K` contained in `X \ Lambda` with

`mu(K) > mu(X)-epsilon`.

Because `Lambda` is closed, Urysohn separation gives `phi in C_c(X)` satisfying

`0 <= phi <= 1`, `phi=1` on `K`, `supp(phi) subset X \ Lambda`.

Hence `phi in I_Lambda`, `||phi||_infinity <= 1`, and

`integral phi dmu >= mu(K) > mu(X)-epsilon`.

Letting `epsilon` tend to zero proves (1).  On `R`, the same separator can be mollified inside the
open set `R \ Lambda`, so the supremum is unchanged on `C_c^infinity(R)`.

For (2), every measure supported on `Lambda` is mutually singular to `mu`.  Therefore

`||mu-nu||_TV = ||mu||_TV + ||nu||_TV >= ||mu||_TV`.

Taking `nu=0` proves equality.

For (3), fix any `F` and put `c=F(0)`.  For every `phi` in the unit ball of `I_Lambda`, both `phi`
and `-phi` have sample vector zero, and

`max(|integral phi dmu-c|, |-integral phi dmu-c|) >= |integral phi dmu|`.

Taking the supremum and applying (1) gives a lower bound `mu(X)` for every `F`.  The reconstruction
`F=0` has error at most `mu(X)`, proving (3).

## Completed-zeta theta specialization

Let

`w_theta(u) = exp(u/4) (evenKernel(0,exp(u))-1)` for `u>0`,

and let `mu_+` be the positive measure with density `w_theta` on `(0,infinity)`.  The Lean theorems
`xiThetaPositiveSource_integrable` and `archimedeanThetaDensity_pos` prove that `mu_+` is finite,
positive, and absolutely continuous.  Put

`M_theta = mu_+(R) = integral_0^infinity w_theta(u) du`.

The critical-trace identity at frequency zero identifies this mass with the central completed
theta trace:

`M_theta = completedRiemannZeta_0(1/2)`.

Let

`Lambda_pp = {log n : n is a prime power}`.

This set is locally finite and hence closed, while absolute continuity gives
`mu_+(Lambda_pp)=0`.  Therefore

`Delta(mu_+,Lambda_pp) = M_theta`.                                      (4)

There is also a completely explicit positive lower bound.  On `0 <= u <= log 2`, the first theta
atom gives

`w_theta(u) >= 2 exp(-2 pi)`.

Consequently

`Delta(mu_+,Lambda_pp) = M_theta >= 2 exp(-2 pi) log 2 > 0`.             (5)

This lower bound uses no numerical approximation.

## Completion and functional-equation symmetry

Let `r(u)=-u`, let `mu_- = r_* mu_+`, and let

`mu_c = mu_+ + mu_-`, `Lambda_c = Lambda_pp union (-Lambda_pp)`.

The completed source theorem `xiThetaLogSource_split` identifies `mu_c` with the full even theta
source.  Reflection preserves the supremum norm and total variation.  The positive and reflected
halves are mutually singular, so

`Delta(mu_c,Lambda_c) = 2 M_theta
                       >= 4 exp(-2 pi) log 2`.                           (6)

The same value holds after restricting the test space to the functional-equation-fixed subspace

`T_even = {phi in C_0(R) : phi(-u)=phi(u)}`.

Indeed, choose the positive-half separators in the proof of (1) with support away from zero and
symmetrize them by `phi_even(u)=phi_+(u)+phi_+(-u)`.  The two supports are disjoint, so
`||phi_even||_infinity <= 1`; the function vanishes on `Lambda_c`, and its completed pairing tends
to `2M_theta`.  Hence functional-equation symmetry loses none of the defect.

In normalized form,

`Delta(mu_+,Lambda_pp)/||mu_+||_TV
 = Delta(mu_c,Lambda_c)/||mu_c||_TV
 = Delta_even(mu_c,Lambda_c)/||mu_c||_TV
 = 1`.                                                                  (7)

Thus completion doubles the absolute amount of invisible archimedean information and preserves
the relative loss at the maximal possible value.

## Interpretation

- `[PROVED]` Prime-power sampling is maximally blind to the positive theta measure in the
  order-zero norm: it loses all of its total-variation mass.
- `[PROVED]` Allowing arbitrary nonlinear reconstruction does not improve the minimax error.
- `[PROVED]` Completion doubles absolute defect; reflection/even symmetry preserves normalized
  defect exactly.
- `[BRIDGE]` The exact-defect theorem is a Riesz--Markov/support-separation consequence and is not
  new scientific knowledge.
- `[SEARCH]` A nonmaximal quantitative geometry can only appear after a stronger topology couples
  nearby points—for example, a Sobolev/RKHS or Hilbert norm canonically selected by the actual Weil
  quadratic form, de Branges space, or Connes trace construction.  Choosing an arbitrary `H^s`
  norm would not clear the canonicality gate.

## Gates

- [x] 0 -> 1 in-progress: defect and norm are well posed; the order-zero duality selects the norm.
- [x] 1 -> 2 fully-proven: exact general proof, nonlinear minimax form, theta specialization,
  explicit lower bound, and completion/even-symmetry law are complete.
- [ ] 2 -> 3 formalized: formalize the Radon-measure ideal-norm theorem and instantiate it with the
  existing theta integrability/reflection API.
- [ ] 3 -> 4 publication-ready: not applicable as a standalone novelty claim.

## Log

- 2026-07-10 -- Created from the quantitative follow-up to the generalized archimedean sampling
  quotient.  Rejected `H^1` and `W^{1,1}` as unearned canonical choices; selected the order-zero
  `C_0` norm through Riesz--Markov and proved the exact maximal defect and symmetry law.
