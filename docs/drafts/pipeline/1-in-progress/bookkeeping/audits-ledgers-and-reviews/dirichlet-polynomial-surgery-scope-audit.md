# Polynomial surgery is not divisor rigidity

- **ID:** dirichlet-polynomial-surgery-scope
- **Stage:** Research-audit correction complete; parent RH search remains in progress
- **Type:** SOURCE-SCOPE AUDIT; no new RH architecture
- **Statement:** Correct the inference from exclusion of a polynomial multiplier to exclusion of every finite change of a zero divisor.

## Why this affects the RH search

`RHTower.no_polynomial_surgery` forbids the exact equality `F(s)=P(s)G(s)` for
two somewhere absolutely convergent ordinary Dirichlet series, nonzero `G`, and
a nonconstant polynomial `P`. Its introduction incorrectly broadens this to
finite divisor surgery within the class. `GoldilocksTrichotomy` also describes
the theorem as a mechanism for a class with no off-line charge, which its
statement does not establish.

The broader conclusion does not follow: a change of divisor permits an
additional nonvanishing analytic factor. The current corpus separately proves
`RHTower.exists_continuable_phase_with_prescribed_locallyFinite_divisor`.
That theorem realizes every locally finite signed divisor supported in
`Re(s)<1` by a meromorphic continuation of a unimodular-prime Euler product.
The existing `HelsonCharacterLSeries` identifies that product with an ordinary
Dirichlet series on `Re(s)>1`.

This is a boundary correction, not an attempt to use Helson functions as an RH
route. Their flexible coefficients differ from the literal coefficients of
zeta. Neither a new proof architecture nor new mathematical knowledge is claimed.

## Verification and affected statements

- [x] Instantiate a singleton divisor at `3/4 + i` in Lean scratch, with no open assumptions.
- [x] Audit the instantiated result and original polynomial theorem with `#print axioms` in scratch.
- [x] Correct source comments and all direct downstream citations that broaden the result.
- [x] Record the route-independent distinction in `universal-law-field/STATUS.md`.
- [x] Run targeted source checks and the required final narrow audit if source files change.

Read declarations and proof bodies in `DirichletRigidity`, `GoldilocksTrichotomy`,
`AnderssonTheoremTwo`, `LocallyFiniteDivisorPresentation`, and
`HelsonCharacterLSeries`. Search-tool queries for coefficient surgery and Helson
finite divisors were paired with `rg` of actual statements and citations.

## Primary source

Johan Andersson, [*Mittag-Leffler type theorems for Helson zeta-functions*](https://arxiv.org/abs/2408.15713),
is the published research source for the prescribed-divisor mechanism. The
corpus implementation and its hypotheses must be verified separately; the
paper title alone is not evidence that the Lean conclusion is available.

## Survivor status

The original polynomial-multiplier obstruction remains valid. It is a routine
first-coefficient asymptotic result and is already formalized. The Helson
counterexample is an instance of an existing general theorem, not new positive
salvage and not a new zero-location mechanism. No proposed RH route is retired
by this audit.

## Verified conclusion and exact limits

`SurgeryScopeAudit.ordinary_series_singleton_divisor` constructs a monoid-with-zero
homomorphism `a : ℕ →*₀ ℂ` and a meromorphic function `Z` such that:

- Every positive-integer coefficient has norm one.
- For every `Re(s)>1`, the ordinary series is absolutely summable and equals `Z(s)`.
- The meromorphic order is one at `3/4+i` and zero everywhere else.

The statement concerns the meromorphic divisor. It does not prescribe arbitrary
point values at removable singularities. No functional equation or literal
zeta coefficient identification is claimed. The proof instantiates an existing
general theorem, then uses uniqueness of the Euler-product limit to identify
the ordinary series.

The scratch file `/tmp/hgt-dirichlet-surgery-scope-W2izoY/SingletonDivisor.lean`
passed `lake env lean`, as did the original polynomial theorem's separate
`PolynomialAudit.lean`. The singleton theorem and both polynomial capstones
report only `propext`, `Classical.choice`, and `Quot.sound`. No experimental
computation or additional axiom enters. The combined `Names.lean` audit also
passes after specifying the universe-polymorphic singleton set at `ℂ`.

One missing precompiled dependency in the existing Andersson import chain was
checked individually with `lake env lean -o ...`:
`XiMassCriticalDiagonalPrimeCoronaZeroDensity`. No source in that dependency
was edited or adopted as an architecture; no umbrella build was run.

Source edits are comments only in `DirichletRigidity` and `GoldilocksTrichotomy`;
all non-comment tokens match HEAD. Direct citations were checked in
`rhtower-nogo-positive-content-audit`, `rh-tower-obstruction-language`, and
`defect-protection-connected-symmetry`. The last also incorrectly inferred an
upper boundary for a minimal RH constraint; the corrected text distinguishes
a necessary exclusion of one planting operation from a sufficient class law.
Existing module umbrella imports remain present. No production module was added
for this instance of published mathematics.

Final validation: both edited source files passed `lake env lean`. The final
leaf audits `lake build GaloisForLFunctions.RHTower.DirichletRigidity` and
`lake build GaloisForLFunctions.RHTower.GoldilocksTrichotomy` passed, respectively
4.3 and 3.1 seconds for the rebuilt leaves. `python3 scripts/formal_tools.py lint`
passed with existing size warnings; its log is
`/tmp/hgt-dirichlet-surgery-scope-W2izoY/lint.log`. The stored proof below matches
the checked scratch text apart from the scratch-only axiom query. Local links
and scoped `git diff --check` pass. The research index now returns the corrected
polynomial-multiplier scope. No mathematical experiment was run in this audit.

## Broader search that exposed the correction

The search covered arithmetic surgery, integer substitution, multiplicative
exchange, coefficient surgery, arithmetic associators, integer nonlinear
operations, finite prime twists, and Helson finite divisors. Search hits were
discovery evidence, not a claim to have checked every matching declaration.
Actual statement/proof checks gave these transfer boundaries:

| Corpus mechanism | What its source actually requires or proves | RH consequence available here |
|---|---|---|
| `EulerCompositionPolynomialRigidity.exists_polynomial_of_euler_mero_relation` | A nontrivial polynomial relation holds as a meromorphic-function identity after a nonconstant entire substitution. | A zero at one parameter does not supply that identity. No source realization found. |
| `mahler_homogeneous_eq_zero` | Exact equality of formal series under `X -> X^k` forces the stated scalar rigidity. | No zero-forced formal-series equality was constructed. |
| `PrimeCollisionConvolution` and `PrimeCollisionCoordinateFusionEscapeUniversalityLaw` | Valuation labels retain ordered or symmetrized native convolution coefficients; under the stated residue-density hypothesis, collision projection produces a new differential-field layer. | Field growth is not a zero-location constraint; no transfer to the literal zeta zero was established. |
| `IntegerCarryTransport` | The source obeys a transported multiplicative law; freezing its argument is legal only when all carries vanish. | This was already recorded in STATUS F20g. It is not a fresh architecture. |
| `TopologicallyAdmittedCarryPropernessSelection` | A locally bounded additive character through a compact phase must vanish; the traffic variant assumes the required local bound. | Compact phase alone supplies no bound on the unwrapped source. No arithmetic bound found. |
| `DirichletRigidity` versus prescribed Helson divisors | Exact polynomial multiplication is excluded while general divisor realization remains possible. | A misleading class-level exclusion was corrected and verified; no RH proof follows. |

The exact theorem names above are located in the named modules; the first row
uses the module name as a location, with theorem namespace
`GaloisForLFunctions.HTGeometry`. The Mahler theorem is in
`GaloisForLFunctions.HTGeometry.MahlerHomogeneousRigidity` as a module location and namespace
`GaloisForLFunctions`. Excluded spectral, Gamma, theta, and other classic-route
hits were not adopted as candidate mechanisms.

## Reproducible audit instance

Copy this existing-theorem instance to a scratch file and check with `lake env lean`.
Axiom queries belong in that scratch file only.

```lean
import GaloisForLFunctions.RHTower.LocallyFiniteDivisorPresentation
import GaloisForLFunctions.HTGeometry.HelsonCharacterLSeries

open Complex Filter Set GaloisForLFunctions.HTGeometry

noncomputable section
namespace SurgeryScopeAudit

def rho : ℂ := 3 / 4 + Complex.I

def singleDivisor (z : ℂ) : ℤ := if z = rho then 1 else 0

theorem singleDivisor_locallyFinite : RHTower.LocallyFiniteDivisor singleDivisor := by
  intro R
  apply (Set.finite_singleton rho).subset
  intro z hz
  have h : z = rho := by
    by_contra h
    simpa [singleDivisor, h] using hz.1
  simpa using h

theorem singleDivisor_supported : ∀ z, singleDivisor z ≠ 0 → z.re < 1 := by
  intro z hz
  by_cases h : z = rho
  · subst z
    norm_num [rho]
  · simp [singleDivisor, h] at hz

/-- Existing prescribed-divisor theorem instantiated at one strict-right nonreal point.
This is an audit witness, not new mathematics or a statement about the literal zeta function. -/
theorem ordinary_series_singleton_divisor :
    ∃ (a : ℕ →*₀ ℂ) (Z : ℂ → ℂ),
      (∀ n, n ≠ 0 → ‖a n‖ = 1) ∧
      MeromorphicOn Z Set.univ ∧
      (∀ s : ℂ, 1 < s.re → LSeriesSummable (fun n => a n) s ∧
        Z s = LSeries (fun n => a n) s) ∧
      (∀ z, meromorphicOrderAt Z z = ((singleDivisor z : ℤ) : WithTop ℤ)) := by
  classical
  obtain ⟨χ, _, Z, hmero, hprod, hord⟩ :=
    RHTower.exists_continuable_phase_with_prescribed_locallyFinite_divisor
      singleDivisor_locallyFinite singleDivisor_supported
  let u : ℕ → ℂ := fun n => if h : Nat.Prime n then (χ ⟨n, h⟩ : ℂ) else 1
  have hu : ∀ p, Nat.Prime p → ‖u p‖ = 1 := by
    intro p hp
    simp only [u, dif_pos hp]
    exact (χ ⟨p, hp⟩).2
  have hχ : ∀ p : Nat.Primes, (χ p : ℂ) = u p := by
    intro p
    simp [u, p.2]
  refine ⟨phaseChar u, Z, ?_, hmero, ?_, hord⟩
  · intro n hn
    exact norm_phaseChar_eq_one hu hn
  · intro s hs
    refine ⟨lSeriesSummable_phaseChar hu hs, ?_⟩
    have hp := hasProd_phaseEuler hu hs
    have hp' : HasProd
        (fun p : Nat.Primes => (1 - (χ p : ℂ) * ((p : ℕ) : ℂ) ^ (-s))⁻¹)
        (LSeries (fun n => phaseChar u n) s) := by
      simpa only [hχ] using hp
    exact (hprod s hs).unique hp'


end SurgeryScopeAudit
```
