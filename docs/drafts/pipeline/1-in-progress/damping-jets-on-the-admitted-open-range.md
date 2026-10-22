# Damping jets on the admitted open range

- **ID:** damping-jets-admitted-range
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** ACCE continuation/tangent hierarchy; PM exact admission frontier
- **Statement:** Critical-norm holomorphy and factorial jet bounds hold for the literal
  Möbius source at every complex damping with real part above the zero width.

## Goal

Prove that actual-source pointwise tangent and signed-work budgets on compact damping
intervals follow from the known open admission frontier. This tests the missing converse
for the arithmetic family, which the generic spike counterexample does not answer.
Count at most one contribution for the full jet theorem and its continuation consequence.

## Gates

- [x] 0 → 1: exact source and norm identified; prior-work searches run.
- [ ] 1 → 2: dependency-closed paper proof, including parameter and physical-source passage.
- [ ] 2 → 3: exact Lean result, foreground leaf audit and axiom audit.
- [ ] Significance/novelty audit: substantial positive addition rather than a reformulation.

## Existing inputs

- `RHTower.TheDampedMoebiusMellinQuotientIsHardyRightOfTheZeroAbscissa`:
  reciprocal-zeta vertical bounds, pole-cleared quotient, Hardy majorant.
- `RHTower.AdmissionBelowHalfDampingAboveTheZeroWidth`:
  Paley–Wiener source identification and the exact open admission range.
- `TransHorizonIncidenceMechanics.DampedMoebiusFirstMomentAndChebyshevTangentBridge`:
  logarithmic source derivatives; norm admission of arbitrary log-weighted rows only
  above half damping.
- `ArithmeticContinuationAndCriticalEnergy.TheDampingAverageOfTheRelativeLossSuffices`:
  averaged tangent criterion and finite-horizon regularity.

## Conjecture loop

1. Extend the quotient in complex damping, uniformly on a compact disc in `Re z > Delta`.
2. Establish the derivative Hardy bounds with no unproved uniformity assumption.
3. Identify those derivatives with the literal log-weighted arithmetic source, retaining
   its centring and fractional-part correction.
4. Derive real compact-interval tangent bounds and the actual pointwise-continuation converse.
5. Audit whether the result supplies a new tool of the requested significance. Do not count
   intermediate estimates separately.

## Scope checks pending

Shifted-zeta and Beurling sources should retain their positive critical boundary; the
argument must not manufacture below-boundary admission. A finite Euler polynomial in the
function-field calibration should give finite-dimensional analytic dependence directly.
The Liouville version requires its extra Euler factor, not an unproved identification.

## Log

- 2026-10-22 — created before proof implementation; all mathematical claims above remain
  conjectural until source identification and uniformity are checked.
- 2026-10-22 — user restricted discovery to corpus search and conjecturing; no further
  web research. Quotient Cauchy estimate drafted; initial compiler checks exposed only
  local elaboration issues, not a mathematical obstruction. Source-identification helper
  now retains the Hardy budget instead of merely producing some square-integrable datum.
- 2026-10-22 — `MobiusDampingJetHardyBounds.lean` passes the required foreground leaf
  command. It proves uniform factorial Hardy bounds for every order and every real
  damping in a fixed closed interior range. This supporting result does not increment
  the contribution count. Literal-source and centered-prefix audits remain open.
- 2026-10-22 — verified Hardy leaf wired into `RHTower.lean`, without an umbrella build.
  Plain leaf checks do not emit `.olean` artifacts in this environment. Asked user whether
  dependency-only `-o` is permitted or proof phases should be consolidated; no forbidden
  artifact-generation command has been run.
- 2026-10-22 — `MellinHardySourceIdentification.lean` passes its foreground leaf audit.
  It transfers the explicit source's full positive-ray square mass from one absolutely
  convergent Mellin line, preserving the original Hardy constant. Its input assumptions
  are discharged by the literal jet's strip identity in the pending source leaf.
- 2026-10-22 — importing the verified Hardy leaf fails with the exact missing
  `.lake/build/lib/lean/GaloisForLFunctions/RHTower/MobiusDampingJetHardyBounds.olean`
  diagnostic. Rechecking that exact dependency with the prescribed plain command, as
  formal instructions require. User's build-rule clarification is pending.
- 2026-10-22 — retry after the prescribed dependency check still reports the same
  missing artifact. Consolidated the three new jet proof phases into
  `MobiusDampingJetsOnTheAdmittedRange.lean` for a plain foreground audit without
  forbidden artifact generation. The merged audit rechecks both earlier proof phases;
  the new source phase exposed three local elaboration errors, now corrected.
  Original split drafts were removed only after their full contents were preserved in
  the merged leaf; the umbrella now references that leaf. Its final audit is pending.
- 2026-10-22 — the generic inversion leaf's existing imports report missing old-path
  `RHTower/ThetaCuspFullReflectionSixthModularSeam.olean`. The prescribed source command
  finds no corresponding old-path source. Corpus search locates the source under
  `RHTower/ThetaCusp/`; this is an existing dependency-cache relocation issue, not a
  mathematical failure. No unrelated caches, modules, or imports were changed.
- 2026-10-22 — generic mean/dyadic inversion elaborates in isolation except for one
  natural-number inequality normalization, now corrected. The full pronic transfer is
  drafted. Its isolated audit copies the existing receiver definitions and the exact
  counting-multiples proof into a scratch file, with narrow existing imports. This is
  a mathematics/elaboration check only, not a substitute for the required final leaf
  audit against the actual imported modules. Targeted dependency-artifact permission
  has been requested again with the newly identified stale-import issue explained.

## Paper mechanism under audit

Write `Delta = Theta - 1/2`, fix `a > Delta`, and choose
`0 < r < min(a - Delta, 1)`. The existing reciprocal-zeta estimate on the line
`Re w >= 1/2 + a - r`, followed by Cauchy's circle formula, gives uniformly for
`epsilon >= a`

`|D^k invZeta(s + epsilon)| <= C k! r^(-k) (2 + |Im s|)^(1/8)`.

Multiplication by the already controlled entire Fermi numerator and division by
`s` gives a common vertical majorant
`K k! r^(-k) (1 + |Im s|)^(-9/16)`. Its square is integrable; no bound at
the zero-width boundary is asserted.

For `c[k,epsilon](d) = (-log d)^k mu(d) d^(-epsilon)`, absolute Dirichlet
convergence on `Re s + epsilon > 1` identifies this quotient with the Mellin
transform of the literal, pointwise finite Fermi source. On one vertical line
in `max(1/2,1-epsilon) < Re s < 1`, Fourier uniqueness identifies its logarithmic
head chart with the Paley–Wiener datum. Hence the same factorial bound controls
the physical Fermi norm. This step must not replace the source by an unrelated
inverse transform.

The mean series `m[k,epsilon] = sum_d c[k,epsilon](d)/d` is absolutely convergent.
Thus `D_c(x)/x -> m`, by dominated convergence against `|c(d)|/d`. Put
`C_c(t)=D_c(1/t)-m/t`. Exact Fermi cancellation gives
`F_c(t)=C_c(t)-2 C_c(2t)`. Iteration and the preceding limit give
`C_c(t)=-sum_{j>=1} 2^(-j) F_c(t/2^j)`. The norm sum is geometric:
`||C_c||_2 <= (1+sqrt(2)) ||F_c||_2`. Existing PM dyadic-inversion lemmas supply
this estimate; their arithmetic limit must be generalized to the log-weighted row.

On the reciprocal integer cell, the centered prefix is
`A_c(floor(1/t)) = C_c(t) + m frac(1/t)`. The correction has norm at most `|m|`
on `(0,1)`; it cannot be discarded. A separate mean estimate is unnecessary:
on `t>1` the floor response vanishes, so `C_c(t)=-m/t`. Its tail square mass
is exactly `|m|^2`, already inside the centered-source budget. Thus the correction
and reciprocal source are controlled by the same norm. All pronic jet norms then
inherit locally uniform factorial bounds above `Delta`, with the same Cauchy radius.

Uniform first-jet bounds on `[a,b]` imply finite-horizon Lipschitz bounds by the
fundamental theorem of calculus, then the same bound in the critical norm.
For actual-source continuation, RH makes every `a>0` an interior point. Conversely,
cofinal continuation budgets imply cofinal admission by existing theorems.
This is an interior regularity converse, not an RH proof or a boundary estimate.

Still to audit formally: coefficient derivative identity, generic mean/dyadic
transfer, exact finite-horizon tangent identification, and the claimed Hilbert-valued
holomorphy (which requires complex parameter neighborhoods, not only real jet norms).
