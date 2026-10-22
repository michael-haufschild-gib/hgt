# Route L: weighted Mellin comparison of the literal original Green primitive

- **ID:** L-C49
- **Date:** 2026-09-12
- **Stage:** 3-formalized; both modules checked at default Lean limits
- **Depends on:** C44 actual weighted source; C46 full Xi packet; C48 local primitive and complete jump
- **RH status:** unproved

Chain: complete original Green/BV source → fixed physical-reader agreement
→ conormal vanishing → RH. C48 constructs the literal local primitive and
classifies its source-forced jump. It does not identify that jump with the
fixed physical reader. The next attack must compare the same primitive's
actual transform, retaining its original prime period and boundary terms.

## Closed weighted comparison

Let L>0 and let `F_s(t)=exp(s*t) f(t)` be integrable with Re(s)>0. For the
literal future primitive `G_L f(t)=sum_(j>=0) f(t+jL)`, the checked theorem proves:

1. `exp(s*t) G_L f(t)` is integrable.
2. `M(G_L f)(s)=M(f)(s)/(1-exp(-sL))`.
3. This is the same almost-everywhere representative as the C48 primitive
   whenever the unweighted L1 hypotheses of that construction hold.

The exact term identity is
`exp(s*t) f(t+jL)=exp(-s*jL) F_s(t+jL)`.
Translation preserves the full integral of the norm. Therefore the term
norm integrals form the geometric series with ratio `exp(-Re(s)*L)<1` and
coefficient `integral ||F_s||`. The countable Bochner-series theorem supplies integrability and interchange
of sum and integral. Translation of each original integral then gives the
geometric resolvent. The application derives every admission bound from
the actual source on `0<Re(s)` and `1-a<Re(s)<a`; no source admission is
inserted as an extra premise for the fixed damping-one application.

At original prime period L=log(p), the denominator is `1-p^(-s)`. It is
nonzero throughout Re(s)>0. Its boundary residues are fixed by C48's full
original periodization; none can be discarded in a continuation or reader
comparison. At damping one, every native Xi point lies in the proved domain. Lean
proves analyticity of the actual integral, equality of every derivative
with the original quotient derivative, preservation of native analytic
order and all lower zero jets, and the exact nonzero leading coefficient
`XiC^(m)(z_rho) * M(f_1)(rho)/(1-p^(-rho))`. No simplicity, bounded
multiplicity, critical-line placement or physical comparison is assumed.

## Hard comparison and domain limits

The main unsolved identity is agreement between the complete original
Green/BV boundary and the fixed physical reader. A geometric resolvent or
source-admission theorem alone does not establish it. The original prime,
Tate depth and multiplicity, Xi leading coefficient, Gamma normalization
and horizontal anchor must remain in that comparison.

C44 supplies unweighted L1 at damping two. At damping one it supplies only
the proved positive-weight strip; C48's unweighted periodization limits
cannot be transferred there without proof. Pointwise Xi resolvent readings
also do not prove a full Xi-packet norm bound for the reciprocal denominator.
The subsequent [full Xi norm theorem](route-l-original-green-full-xi-bound.md)
derives that bound and literal Green-field norm convergence at fixed damping
greater than one. No zero-damping passage is assumed or proved.

The theorem about all derivatives concerns the actual Mellin integral as
a function. Identification with every polynomially weighted Green integral
is not yet proved. C48 already identifies the same literal sum with its
cellwise L1 representatives whenever unweighted source integrability holds.
It is not transferred to damping one. The [original boundary-residue theorem](route-l-original-green-boundary-residues.md)
now identifies the same quotient residues with every original jump coefficient.

## Corpus and method audit

Current report: [weighted Green search](../1-in-progress/route-l-weighted-green-search.json).
All 20 candidate statements, 20 source arguments and the proposed group
were inspected. Query generation 877831; inventory snapshot 877838 has
56986/56986 files, including 47384 Lean files. Text/source retrieval and
three iterative queries are partial; compiler applicability is not checked
for the returned candidates. Inventory completeness is not proof coverage.

The proposed group links a finite translation primitive and adjoint
translation pairing to a Suzuki Fourier Gram identity. The last step
requires a matching Sonin L2 source, which has not been supplied for the
literal primitive. It is not an established transfer. C44's actual weighted
Mellin functional and translation equivalence are relevant. The returned
Volterra primitive lemmas concern continuous half-line integration, not the
original discrete shift sum.

An earlier inspected report, `/tmp/route_l_c49_weighted_green_deep.json`,
was lost with the prior runtime's temporary files. Its proposed spectral
resolvent moment was only a definition, not a convergence result. Its
Möbius Mellin ingredients required Re(s)>1 and actual Mellin convergence.
The finite exponential-packet contact identities in
`PairedTranslationResolventCalculus` retain a squared endpoint value and
assume positive node real parts; neither that representation nor its
positivity premises are transferred to the complete source by analogy.


## Additional corpus and method audits

[Bochner/geometric report](../1-in-progress/route-l-weighted-green-integral-search.json):
query generation 877940, inventory snapshot 877946 with 56992/56992 files
(47389 Lean, 9603 prose). Text and source retrieval are partial; semantic
coverage is not measured; returned declarations are source-only and
applicability unchecked. All 20 candidate statements and 20 method
arguments were inspected. `hasSum_mellin` supplies a relevant use of
`hasSum_integral_of_summable_integral_norm`; its own exponential-packet
representation is not assumed for this source. The proposed Gaussian
integrability group does not identify the actual infinite source. The
finished proof instead applies the actual Bochner interchange theorem to
the original translated source, with its geometric norm sum proved.

[Native-order report](../1-in-progress/route-l-weighted-green-jet-search.json): generation
877958, coverage pending, partial due to deadline and unfinished ranking.
All 20 candidate statements were inspected; no source arguments, proof
ideas, or ingredient groups returned. Nonvanishing-unit and local quotient
results require their analytic/order premises. The proof supplies those
premises from C45 and the actual C49 integral identity, then applies the
existing native Xi derivative theorems in Lean.

## Broad recent-paper audit

Single-word arXiv query `renewal`, newest first, found the unrelated
[Geometric Analysis of Doppler-Based Navigation with Low Earth Orbit
Satellites](https://arxiv.org/html/2609.11296v1), 10 September 2026.
Sections 4.2–5.2 were read, including the exact Schur correction and its
projection formula. Their positivity requires full column rank and the
paper's actual measurement Gram matrix; its irreducible correlation uses
the original sign-definite clock sensitivity. Route L has neither this
measurement identification nor the corresponding source-derived sign law.
Thus adding a boundary coordinate does not acquire a cancelling correction
by analogy. The surviving method is to retain the complete correction and
prove its sign from the actual source. No numerical example was used.

## Lean implementation and optimization

- `DeningerWeightedOriginalGreenMellin`: narrow generic calculus importing
  only the already checked C48 core.
- `DeningerDampedOriginalGreenMellin`: separate actual-source application,
  importing C45 for analyticity and native Xi derivatives.
- Both are wired once into `RHTower.lean`; no umbrella build is run.

The first scratch attempt hit the default 200000-heartbeat limit during
scalar-type inference for the norm geometric series. The repair explicitly
types that series over the reals, names its norm-integral summability once,
and uses the exact translation rewrite. The corrected core passes with no
heartbeat or recursion-limit changes. Recorded core profile: import 16.1s,
elaboration 85.4ms, tactic execution 78.5ms. This is a core-only observation,
not a timing claim for the heavy actual-source imports. The actual-source
scratch also passes after making its function equality and analytic-order
application explicit. No axiom-print audit was run.

`lake build GaloisForLFunctions.RHTower.Deninger.DeningerDampedOriginalGreenMellin`
completed successfully. Only the two new modules built: generic core 2.2s,
actual-source application 58s. Existing dependency messages were replayed.
Index regeneration passed. The two modules expose 18 public declarations.

Global lint failed on two separate HTGeometry modules unreachable from
their umbrella: `SecondEndpointMellinLaurentInterchange` and
`UniformSecondOrderJet`. Neither was edited or compiled for this change.
The new Route L imports are present. This is not a passed global lint gate.

Logs: [core profile](route-l-weighted-green-core-profile.log),
[final leaf audit](route-l-weighted-green-build.log),
[global lint](route-l-weighted-green-lint.log),
[index regeneration](route-l-weighted-green-index.log).
