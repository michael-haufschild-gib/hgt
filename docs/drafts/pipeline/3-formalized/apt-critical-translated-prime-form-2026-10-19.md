# Critical prime form of a translated finite factorial pattern

- **ID:** APT-CRITICAL-TRANSLATED-PRIME-FORM
- **Stage:** 3-formalized
- **Type:** FORMALIZED SUPPORT PACKAGE; not counted toward significant novel results
- **Source:** apt-critical-prime-harmonic-diagonal-2026-10-19.md
- **Statement:** Determine the complete limiting prime quadratic form of every fixed finite coefficient pattern translated to high factorial scale.

## Scope

The singleton limit and its exact divisor-charge classification are established inputs.
This package determines how that arithmetic structure acts on a finite family
of actual factorial sources. A Bohr average at fixed scale is not the physical limit;
the slow collar phase must remain. No premise about positivity or a missing source bound
may be introduced. README remains read-only; no computations, new axioms, heartbeat
increases, full builds, commits, or pushes. One owned foreground Lean invocation at a time.
Accepted significant-result count remains **0/100**.

## Plan

- [x] Derive the actual-source formula and a uniform complete-prime majorant on paper.
- [x] Inspect focused corpus retrieval and exact reusable APIs before new Lean work.
- [x] Independently audit all source-index, convergence, and regrouping steps below.
- [x] Formalize and audit the support-independent harmonic mass bounds and exact zero-mass classification.
- [x] Formalize actual translated correlations and the complete prime-series limit.
- [x] Formalize the native divisor diagonal and classify its harmonic signs.
- [x] Run targeted build, actual-file, axiom, index and global lint checks; record the global lint failure below.
- [x] Record conservative novelty/significance decision; no credit assigned.

## Exact sources and proposed theorem

Fix a finite set `S⊂ℕ` and real coefficients `b_j`. Put `N=n+1` and

`B_n(v)=Σ_(j∈S) b_j Φ_(N+j)(v)`,

`g_n(x)=1_(x≤0) exp(x/2) B_n(exp(-x))`,

`P_b(t)=Σ_(j∈S) b_j exp(2πijt)`.

These are actual sources: in the existing API, use
`criticalFactorialSource (S.image (fun j => n+j)) (fun k => b(k-n))`.
Addition is injective, so the image and subtraction introduce no coefficient collisions.
Define the nonnegative slow-phase quadratic masses

`J_m(b)=∫_(v>1) v⁻²(1-cos(2πmv/12)) |P_b(mv)|² dv`.

The intended unconditional endpoint, for every fixed finite `S,b`, is

`lim_(n→∞) Σ_(r≥2) [Λ(r)/sqrt(r)] autocorr(g_n)(log r)`

`= (4/π⁴) Σ_(r≥2) Σ_(l≥1) [Λ(r)/r] w_(rl) w_l J_(rl)(b)`

`= (4/π⁴) Σ_(m≥1) [A(m)/m⁴] J_m(b)`.

Here `A` is the already verified native harmonic divisor charge. All prime powers and
harmonics remain; all displayed series must be proved absolutely convergent. This yields
a single negative harmonic channel at `m=2`, zero channels at `m=1` and `4|m`, and
nonnegative remaining channels. The mass theorem below establishes `J_m(b)>0` for every
nonzero pattern and positive harmonic, without an assumed trigonometric-polynomial
uniqueness statement. Its use for the actual-source channels awaits the source-limit identity.

## Dependency-closed paper argument to audit

1. Each phase has the existing absolutely convergent harmonic expansion. For two source
   offsets `i,j`, the fast carriers in a harmonic pair are `kN` and `rlN`. Their shifts
   tend to `k(i+1/12)` and `rl(j+1/12)` on the shifted branches, and to `ki` and `rlj`
   on the unshifted branches. The verified cosine-product convergence mechanism applies.
2. For `k≠rl`, every difference frequency escapes and every sum frequency escapes.
   For `k=rl`, expand the four products. Their surviving slow integral is

   `∫_(v>1) v⁻² cos(2πk(i-j)v) (1-cos(2πkv/12)) dv`.

   The same-branch offset difference is `k(i-j)`; the two mixed differences are
   `k(i-j)±k/12`. The identity `cos(a+b)+cos(a-b)=2cos(a)cos(b)` gives the formula.
3. Write `B₁=Σ_(j∈S)|b_j|`. Every cosine difference is bounded by two, so each expanded harmonic
   pair has integrated absolute value at most `4B₁²`. The product majorant
   `4B₁² |w_k||w_l|` is summable. Integrate the complete expansion and pass to the
   limit by dominated convergence. The finite sum over `i,j` is harmless. Its cosine
   factor sums to `|P_b(kv)|²` because `b_j` are real. Thus the limiting physical
   correlation at dilation `r>0` is `(4/π⁴)Σ_l w_(rl)w_l J_(rl)(b)`.
4. Put `B_w=Σ_(j∈S)(j+1)|b_j|`. Existing critical prime admission gives a physical
   correlation bound `P_n(4A_n+L_n)/r`, with

   `P_n=12 Σ|b_j|/(N+j)`, `A_n=2B₁`, `L_n=14 Σ(N+j)|b_j|`.

   Since `N≥1`, `P_n≤12B₁/N`, `8B₁/N≤8B₁`, and
   `Σ(N+j)|b_j|/N≤B_w`. Therefore

   `P_n(4A_n+L_n)≤12B₁(8B₁+14B_w)=K(S,b)`.

   This constant is independent of `n`. The physical/logarithmic bridge contributes
   the additional `r^(-1/2)`, so every actual prime atom is bounded by
   `K(S,b) Λ(r)/r²`. The existing summability theorem permits the full prime limit.
5. `|P_b|≤B₁`, hence `0≤J_m(b)≤2B₁²`. The same absolute double-series comparison
   used in the singleton diagonal now has only an additional factor `B₁²`. Regroup
   by `m=rl`; the coefficient is exactly the established `A(m)`, not a new symbol
   defined to absorb an unknown remainder.

## Uniform mass bounds exposed by the diagonal

Write `E_b=Σ_(j∈S)b_j²`. The verified slow quadratic masses obey the uniform bounds

`E_b/48 ≤ J_m(b) ≤ 4E_b` for every integer `m≥1`.

These bounds would make the limiting complete prime form bounded in coefficient `ℓ²`,
independently of the number of offsets. This improves on the support-sensitive `B₁²`
majorant used only to justify passage to the limit. It is the intended native consequence
to investigate, not an assumption permitted in the formal endpoint.

Paper derivation:

- Exact finite Fourier orthogonality gives `∫_j^(j+1)|P_b(mv)|²dv=E_b` for integer
  `j,m`, `m≥1`. On each such interval with `j≥1`, the physical weight is at most
  `j⁻²`, and the slow factor is at most two. Summing and using the existing
  `Σ_(j≥1)j⁻²≤2` gives `J_m(b)≤4E_b`.
- On `[12,24]`, expand the cosine factor and the finite square. Every off-diagonal
  frequency `m(i-j)` integrates to zero. The mixed frequencies
  `m(i-j±1/12)` are nonzero and make an integer number of periods on this interval,
  so they also integrate to zero. Consequently
  `∫_12^24 (1-cos(2πmv/12))|P_b(mv)|²dv=12E_b`.
  Here `v⁻²≥1/576`; nonnegativity of the integrand gives `J_m(b)≥E_b/48`.

Thus every nonzero pattern has strictly positive `J_m(b)` without assuming a uniqueness
theorem for trigonometric polynomials. Inserting the `l=1` harmonic gives a quantitative
strict sign at every nonzero dyadically admitted dilation. The fourth-power harmonic
tail and `Λ(r)/r³` prime majorant then give a support-independent `ℓ²` bound for the
complete limiting prime form once the source-limit identity is established. The mass
constants, integral decompositions, and exact zero-mass classification have passed the
Lean audit recorded below. The source-limit identity and novelty audit remain open.

## Reuse and audit status

Focused deep corpus query completed in `/tmp/apt-critical-translated-pattern-prior.json`;
all twenty candidate lemmas and twenty source arguments were screened. It recovered the
verified singleton/diagonal package, existing critical admission and affine comparison,
and prior fixed-source tail and ramp bounds. Retrieval was complete but semantic coverage
was unmeasured and refresh deferred to the background indexer; absence is not established.
The parent cards record the broader 241-hit APT audit and prior physical Riesz results.
Existing generic averaging, finite-sum algebra, divisor regrouping, and the dyadic stencil
are baseline and receive no novelty credit.

`FactorialCriticalCorrelationLimit.lean` already contains private
`limit_cos_product_tendsto`: it allows arbitrary convergent shifts of two positive
linear carriers. Its statement was checked at line159. The exact collar-shift convergence
is also already proved. Reuse these proofs through a minimal explicit public interface
if needed; do not duplicate the 531-line singleton argument or introduce a generic
infrastructure project. Two explicit public wrappers were added for reuse:
`factorialCriticalCosineProduct_tendsto` exposes the existing physical integral limit,
and `factorialShiftedFreq_translated_sub_tendsto` exposes the actual translated frequency
shift. Their targeted core build passed (`/tmp/apt_critical_translated_core_build.log`,
status `0`); final actual-file and axiom audits remain due after this source-limit work.
The independently audited mass component is installed as recorded below.

The deep carrier-mechanism search `/tmp/apt-critical-translated-carrier-reuse.json`
returned the existing private core theorem as its first candidate. The hybrid collar
query `/tmp/apt-critical-translated-collar-reuse.json` also recovered the exact private
shift convergence and the public native frequency/shift identity. All returned candidate
lemmas and source arguments were screened; retrieval was complete, with unmeasured
semantic coverage and a stale generation warning. Nearby cosine means concern growing
integration intervals or different spectral sources. The current proof reuses the
verified critical physical-weight theorem directly.

Scratch `/tmp/apt_critical_translated_layers.lean` now develops the offset-pair harmonic
correlation limit. It retains arbitrary offsets `i,j`, applies the existing carrier limit
to the four shifted/unshifted products, and identifies the resonant remainder with
`∫ v⁻² cos(2πk(i-j)v)(1-cos(2πkv/12)) dv`. Scratch validation is in progress.

Two independent mechanism searches completed:
`/tmp/apt-critical-periodic-weight-prior.json` and
`/tmp/apt-critical-integer-orthogonality-prior.json`. Their twenty candidate lemmas
and twenty source arguments per query were screened. Both were retrieval-complete
with unmeasured semantic coverage. The proposed ingredient sets did not supply the
required weighted bound; a measure-uniqueness proposal does not prove Parseval here.
The concrete `RHTower.circleAverage_finiteFrequencyPolynomial_norm_sq` was inspected:
it gives exact polynomial Parseval with repeated frequencies, a usable baseline after
changing from circle averages to real unit intervals. The general Hilbert-basis Parseval
and uniform-weight comparison statements were also checked; they do not themselves
provide the half-line physical estimate.

The refined hybrid query `integral_Ioi tsum` recovered
`RHTower.hasSum_integral_Ico_unit` in `ZetaUnitIntervalIntegrals.lean`, plus the
underlying mathlib set-integral and sum/integral comparison APIs. A mechanism based on
unit-interval decomposition therefore has existing corpus support. Exact trigonometric
API queries completed in `/tmp/apt-critical-trig-integral-api.json` and
`/tmp/apt-critical-trig-period-api.json`. Their available hits were screened; source checks
found the exact public `RHTower.integral_cos_two_pi_int_mul` at
`RHTower/FourierPositiveJumpNetwork.lean:107`, giving the integral on `[0,1]` as
`if m=0 then 1 else 0`. This is the appropriate scalar orthogonality input. The
phase-shifted cosine Parseval package and generic cosine primitive were also inspected.
Use the existing scalar theorem or mathlib integral change of variables, rather than
rebuilding Fourier or polynomial infrastructure.

The unit-interval decomposition proof was inspected at
`RHTower/ZetaUnitIntervalIntegrals.lean:100`. It uses the public ray cover
`iUnion_Ico_unit` and mathlib `hasSum_integral_iUnion`; the existing statement has complex
values, while the mathlib primitive also works for real values. Its later, unrelated
theorem has a scoped historical heartbeat setting; do not copy or raise that setting.

Further hybrid retrieval in `/tmp/apt-critical-periodic-integral-api.json` found the
mathlib periodic interval identities directly, including `intervalIntegral_add_eq` and
`intervalIntegral_add_zsmul_eq`. All twenty candidate lemmas and twenty source arguments
were screened. The refined query `tsum one div nat square le two`, saved in
`/tmp/apt-critical-inverse-square-bound-search.json`, recovered existing inverse-square
estimates. Source inspection found the exact public rational estimate
`HTGeometry.tsum_inv_sq_shift_one_le_two` and its summability input in
`HTGeometry/InverseSquareTailSum.lean` and `VerticalShiftTailEstimate.lean`. Reuse these
instead of rebuilding the elementary series bound. Both retrievals completed, with
semantic coverage unmeasured and a snapshot older than the current index generation.

Scratch validation passed for `/tmp/apt_critical_pattern_mass.lean`, including the
selected `have := @Name` API checks (`/tmp/apt_critical_pattern_mass.log`, empty;
`/tmp/apt_critical_pattern_mass.status`, `0`). The native density is the sum of the
squares of its real cosine and sine sums, with an exact double-cosine expansion.
Verified intermediate identities are unit-cell Parseval and the exact collar mass
on `[12,24]`. They give `E_b/48 ≤ J_m(b) ≤ 4E_b`, and `J_m(b)=0` exactly when
every coefficient on the support vanishes, for every `m>0`.

The proof was installed as
`formal/GaloisForLFunctions/arithmetic-positivity-theory/FactorialCriticalPatternHarmonicMass.lean`
(427 lines, 14 public declarations) with its APT umbrella import. The targeted leaf build
passed (`/tmp/apt_critical_pattern_build.log`, status `0`). Direct compilation of the
actual source passed with an empty log (`/tmp/apt_critical_pattern_actual.log`, status `0`).
The actual-import audit of all fourteen declarations passed
(`/tmp/apt_critical_pattern_actual_axioms.log`, status `0`), using only `propext`,
`Classical.choice`, and `Quot.sound`. Index refresh passed
(`/tmp/apt_critical_pattern_index.log`, status `0`), and every one of the fourteen public
declarations was confirmed in `formal/LEAN_API.md`. Whitespace and forbidden-marker
checks passed; no heartbeat setting was added.

Authoritative `scripts/formal_tools.py lint` returned `1`
(`/tmp/apt_critical_pattern_lint.log`): the two pre-existing unreachable TransHorizon
modules `FermiHomogeneousEnergyAndPronicComparison` and `FermiPrimeExponentGramBounds`,
plus 381 large-file warnings. No error names the new mass leaf. Global lint is not green.

This is the mass component of the proposed translated-source endpoint; the complete
translated prime limit is still open. Novelty/significance decision: no separate credit
for this supporting package. The singleton and diagonal packages retain their completed
actual-file audits, without repeat tests of unchanged proofs.

The focused query `factorialPhaseCombination_hasSum`, saved in
`/tmp/apt-critical-translated-combination-api.json`, recovered the exact existing
finite-combination harmonic expansion and its equivalent `factorialPhaseCombination_eq_tsum`.
All twenty candidates and twenty source arguments were screened. Retrieval completed;
semantic coverage remained unmeasured. In the next source-limit proof, reuse this public
expansion and the existing cosine-carrier convergence mechanism instead of rebuilding
the harmonic expansion. The expansion has normalization `-π²/2` on its phase-combination
side; its equivalent series formula has factor `-2/π²`.

The sign of the entire limiting prime form, any periodized-kernel positivity/negativity,
and any complete Weil consequence remain open. No numerical evidence is used.

## Further exact survivor to audit after the translated endpoint

Changing variables `u=mv` in the proposed masses gives

`J_m(b)=m ∫_(u>m) u⁻²(1-cos(2πu/12)) |P_b(u)|² du` for `m≥1`.

Consequently the proposed complete diagonal has the common-density representation

`(4/π⁴) ∫_(u>1) u⁻²(1-cos(2πu/12)) |P_b(u)|² H(u) du`,

where `H(u)=Σ_(1≤m≤u) A(m)/m³` almost everywhere, with integer endpoints handled
separately. A sufficient uniform majorant for this interchange follows from
`Σ_r Λ(r)/r²<∞` and `Σ_l l⁻³<∞`. Alternatively, exact change of variables and the
absolute weighted diagonal give `Σ_m ∫|f_m|<∞` directly. Cubic summability itself
is not to be inferred merely from a fourth-power coefficient series.

The established charge classification suggests an exact arithmetic sign boundary:
`H=0` on `[1,2)`, `H<0` on `[2,5)`, and `H>0` on `[5,∞)`. Indeed
`H(2)=-log(2)/4`, `H(3)=H(4)=-log(2)/4+log(3)/9<0`, and
`H(5)=-log(2)/4+log(3)/9+log(5)/25>log(2)/150>0`.
The latter bound follows symbolically from `3²>2³` and `5⁴>2⁹`, while every
subsequent charge is nonnegative. These are dependency-closed paper deductions, not
yet corpus-audited or formalized new results. The sign boundary of `H` does not decide
the sign of the entire integral or its periodization against `|P_b|²`.

First overlap search for this deduction completed in
`/tmp/apt-critical-cumulative-charge-prior.json` (deep mode, complete retrieval,
unmeasured semantic coverage). Every returned candidate lemma and source argument was
screened. Source inspection distinguished three nearby constructions: the maximum-index
covariance in `EulerDeletionAveragedDivisorCovariance.lean:333`, the Abel-summed divisor
defect boundary in `DivisorSourceHarmonicBoundary.lean:90`, and the retained finite prime
cutoff in `MobiusDivisorCriticalRetainedPrimeBoundary.lean:24`. None of those inspected
statements is the cumulative native charge above. The proposed search ingredient set
concerned factorial exponential tails and does not supply this argument. Broader priority
and applicability audits are still required; this is not a novelty conclusion.

## Translated harmonic limit implementation

The complete scratch proof `/tmp/apt_critical_translated_layers.lean` passed Lean
with an empty log and status `0`. It proves the offset-pair limit, sums every pair
into the existing pattern mass, and identifies the native translated finite
harmonic layer using the injective image `j ↦ n+j` and coefficient `b(q-n)`.
The resulting theorem includes zero harmonics and arbitrary finite real patterns:
the actual layer correlation tends to `J_k(b)` when `k=r*l`, and to zero otherwise.

Installed as `FactorialCriticalTranslatedHarmonicLimit.lean`, with its APT umbrella
import. Its targeted build passed in 138 seconds
(`/tmp/apt_critical_translated_harmonic_build.log`, status `0`);
actual-file and axiom audits remain due.
The two public carrier wrappers added to `FactorialCriticalCorrelationLimit.lean`
have a successful targeted build; their final actual-file and axiom audits also
remain due. No separate novelty credit is assigned to these support statements.

The query `factorialPhaseCombination correlation translated limit` completed in
`/tmp/apt-critical-translated-correlation-reuse.json`. All twenty candidates and
twenty source arguments were screened. It recovered the exact native phase bounds,
continuity, existing critical physical bound, and singleton harmonic domination
proof. Semantic coverage is unmeasured. The full translated correlation proof
reuses the public full phase expansion, the new harmonic limit, and that complete-series
domination mechanism. Installed as `FactorialCriticalTranslatedCorrelationLimit.lean`,
with its APT umbrella import. Its targeted build passed in 99 seconds
(`/tmp/apt_critical_translated_correlation_build.log`, status `0`). The two remaining
universe checks from the scratch API block passed separately in
`/tmp/apt_critical_translated_correlation_api.lean`; the installed source omits that
test block. Actual-file and axiom audits remain due.

The complete-prime scratch `/tmp/apt_critical_translated_prime_limit.lean` combines
the uniform moment bound with the existing native logarithmic correlation bridge
and complete-prime dominated convergence. It passed Lean with an empty log and status `0`.
Installed as `FactorialCriticalTranslatedPrimeLimit.lean`, with its APT umbrella import;
the targeted build passed in 37 seconds
(`/tmp/apt_critical_translated_prime_limit_build.log`, status `0`). The queries
`criticalFactorialPrimeConstant translate uniform ratio` and the broader deep
`finite factorial source translated scale moments uniform prime correlation bound`
were screened completely (twenty candidates and twenty source arguments each).
The deep results mainly concerned unrelated factorial moments. The lexical query
`criticalFactorialPrimeConstant` returned its single definition; exhaustive `rg`
screened every use in the APT tree. The exact reusable results are critical finite-source
admission and the singleton uniform-bound proof, not a pre-existing translated-pattern
bound in the inspected material. Semantic coverage remains unmeasured.

The query `pattern harmonic prime diagonal`, restricted to APT, recovered the existing
divisor fiber argument, the native charge classification, and the audited pattern mass.
All twenty candidates and twenty source arguments were screened. Its snapshot was older
than the current generation, with unmeasured semantic coverage. Reuse the existing
charge definition and classification; only its physical pattern mass changes.
The complete translated prime-series endpoint is formalized. Its divisor regrouping,
harmonic sign classification, and support-independent bound passed Lean in
`/tmp/apt_critical_translated_diagonal.lean` with an empty log and status `0`.
Installed as `FactorialCriticalTranslatedPrimeHarmonicDiagonal.lean`, with its APT
umbrella import; the targeted build passed in 53 seconds
(`/tmp/apt_critical_translated_diagonal_build.log`, status `0`). The first summability term hit the
default elaboration limit; explicit intermediate types resolved it without any heartbeat
increase. Final audits and conservative significance decision are recorded below.

For the support-independent bound, put
`M₂=Σ_(r≥2) Λ(r)/r²` and `W₁=Σ_(l≥0)|w_l|`, both already summable in the corpus.
The same absolute joint majorant gives the concrete paper consequence
`|P∞(b)| ≤ (16/π⁴) M₂ W₁ E_b`.
Indeed each prime/harmonic term before the factor `4/π⁴` is bounded by
`4E_b·envelopePrimeMajorant(3/2,r)·|w_l|`; sum the product majorant and apply
the integral/series identity. This bound is independent of the number and locations
of offsets. It does not establish a sign for the complete prime form.

The focused query `prime form coefficient square sum uniform`, restricted to APT,
completed in `/tmp/apt-critical-translated-prime-l2-reuse.json`; all twenty candidates
and twenty source arguments were screened. It recovered
`abs_tsum_factorialSpanPrimeAtom_le` and the earlier full-span budget. Exact source
inspection confirms that `factorialSpanTest` uses `exp(3x/2)` and physical weight `v⁻⁴`;
the present critical source uses `exp(x/2)` and `v⁻²`. The existing budget therefore
does not directly supply this critical limit bound. Its norm/absolute-series comparison
argument and `canonicalPrimeMajorantConstant` are reused. Retrieval had a stale coverage
snapshot and unmeasured semantic coverage; no absence or novelty claim follows.

## Final verification and significance decision

Direct compilation of all five changed Lean files passed with empty logs and status `0`:
the carrier-limit core and the four translated harmonic, correlation, prime-limit,
and divisor-diagonal leaves. Logs are
`/tmp/apt_translated_actual_<LeafName>.log` and the corresponding `.status` files.
The actual-import axiom audit of all eighteen new public declarations passed
(`/tmp/apt_critical_translated_actual_axioms.log`, status `0`), using only
`propext`, `Classical.choice`, and `Quot.sound`.

Index refresh passed (`/tmp/apt_critical_translated_index.log`, status `0`), and all
eighteen public declarations were individually confirmed in `formal/LEAN_API.md`.
Scoped whitespace, forbidden-marker, and `git diff --check` checks passed. No heartbeat
setting was added. Completed `/tmp/apt_critical_translated_*.lean` scratch sources and
their two merged fragments were deleted; validation logs and search JSON remain.

The authoritative `scripts/formal_tools.py lint --check-generated` returned `1`
(`/tmp/apt_critical_translated_lint.log`): 381 large-file warnings and three unreachable
TransHorizon umbrella modules outside this change:
`FermiHomogeneousEnergyAndPronicComparison`, `FermiPrimeBoxGramBounds`, and
`FermiPrimeExponentGramBounds`. The first and third were recorded by the earlier mass
audit; the second now also appears. No lint error names these APT leaves. The global
gate is not green; foreign modules were preserved.

The exact actual-source limit, complete divisor diagonal, individual harmonic signs,
and support-independent coefficient `ℓ²` bound are formalized. This is retained as a
supporting package: its proof uses established harmonic averaging, the existing native
divisor charge, and absolute-series arguments. A separate significant novelty claim is
not established. Accepted significant-result count remains **0/100**.

The sign and coercivity of the total quadratic form remain open. They are tracked in
`../1-in-progress/apt-critical-prime-kernel-signature-2026-10-19.md`, including the
sharp cumulative-charge boundary, exact unit-cell reduction, and required real even
kernel. No positivity claim or Weil consequence is inferred from the harmonic signs.

The successor card now also records the continuous real representative and exact
weight identity `∫_(0,∞)γ(u)Q_b(u)du=(π²/12)Σ b_j²`, obtained using the existing
sinc-square Fourier identity. Both supporting leaves compile directly and are wired into
`ArithmeticPositivityTheory.lean`. Their final audit and the user-requested pause
are tracked on that card; the sign classification remains open.
