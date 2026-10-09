# Construct the actual polynomial exterior cycle

- **ID:** POLYNOMIAL-EXTERIOR-CYCLE-20261009
- **Stage:** 3-formalized
- **Type:** BRIDGE; external novelty unverified; corpus only
- **Parent:** `../1-in-progress/finite-planar-polynomial-realization.md`
- **Target:** Construct a large positive target circle whose actual polynomial covering monodromy is a full cycle on its root fiber. Separately certify the regular fiber has degree-many sheets.

## Corpus audit

The documented `power monodromy circle` lexical query returned two declarations in a Jacobi integral module; neither supplies a power-cover circle action. Installed `RingTheory/RootsOfUnity/Complex.lean` supplies `Complex.isPrimitiveRoot_exp`: exp(2πi/d) is a primitive d-th root for d≠0. Inspected `IsPrimitiveRoot.eq_pow_of_pow_eq_one` expresses every d-th root of unity as one of its powers, and `IsPrimitiveRoot.inv` preserves primitivity. Installed `Perm.Cycle.Basic` defines `IsCycleOn` by bijection and repeated-application connectivity. `Polynomial.Reverse` supplies `coeff_zero_reverse` and `eval₂_reverse_mul_pow`, identifying the reciprocal polynomial. The corpus already constructs connected punctured-disk power covers and classifies their quotients, but those statements alone do not calculate this actual exterior loop. No external sources used.

## Cyclic power action — complete paper proof [PROVED HERE]

Let ζ be a primitive d-th root, d>0, and w≠0. Multiplication by ζ permutes {u:u^d=w}; its inverse multiplies by ζ⁻¹. For any two roots u,v, both are nonzero, and (v/u)^d=1. The inspected root-of-unity classification gives k<d with ζ^k=v/u. Hence k iterations send u to v. Thus this permutation is a cycle on the whole fiber. The same argument applies to ζ⁻¹. More generally, if an injective coordinate c on a permutation's sheets has nonzero values, all with the same d-th power, and intertwines the permutation with multiplication by ζ, this argument proves the permutation is a full cycle. This coordinate criterion will avoid unnecessary enumeration or a chosen labeling of roots.

## Reciprocal power coordinate — complete paper proof [PROVED HERE]

Let P be monic of positive degree d and Q=P.reverse. The inspected coefficient identity gives Q(0)=1. Define f(w)=w^d/Q(w). Near zero, Q is nonzero, so f is analytic and has exact order d: it is w^d times the analytic unit 1/Q(w). The already audited analytic power-coordinate theorem supplies an analytic local homeomorphism φ at zero, φ(0)=0, with φ(w)^d=f(w), with its source chosen inside the neighborhood where Q is nonzero. The inspected reverse-evaluation identity gives f(w)=1/P(1/w) whenever w≠0 in that source. Thus ψ(z)=φ(1/z) is an actual power coordinate at infinity, with ψ(z)^d=1/P(z).

## Full exterior monodromy — complete paper proof [PROVED HERE]

For the explicit lift, use q_d(t)=exp(2πit/d). It is continuous, starts at one, has norm one and is never zero. For d>0, the inspected complex exponential power identity gives q_d(t)^d=exp(2πit), and q_d(1)=exp(2πi/d), the inspected primitive root. Its inverse gives the negative local orientation needed below. These exact symbolic path identities are formalized separately before constructing the exterior lift.

Choose ε>0 with ball(0,ε) inside φ's source and choose η>0 with ball(0,η) inside its target. On the compact source disk |z|≤1/ε, |P(z)| is bounded. All actual critical values also form a finite bounded set. Choose M>0 larger than both bounds. Choose ρ>0 with ρ<η and ρ^d<1/M; this follows from continuity of the positive integral power at zero. Put R=1/ρ^d>M. Every root over the positive circle γ(t)=R exp(2πit) lies outside |z|≤1/ε, so ψ is defined there; γ avoids all critical values.

For a root z₀ over R, ψ(z₀)^d=1/R=ρ^d. Taking norms and using injectivity of positive integral powers on nonnegative reals gives |ψ(z₀)|=ρ. The explicit path

z(t)=1/φ⁻¹(ψ(z₀) exp(−2πit/d))

is therefore defined: its argument stays in φ's target disk, and it never equals zero, so φ⁻¹ of it never equals zero. The reciprocal power identity shows P(z(t))=γ(t). This is the unique actual root lift. Its endpoint coordinate is exp(−2πi/d)ψ(z₀). The coordinate ψ is injective on the entire fiber (both inversion and φ are injective there), nonzero, and every coordinate has d-th power 1/R. The cyclic power-action proof above therefore makes the actual root-loop permutation a full cycle. The audited native-covering identification transfers this statement to native `monodromyPerm`, with the positive target orientation explicitly retained.

No argument principle, integral formula, spectral input, numerical root calculation or assumed exterior permutation enters this proof. The estimates only choose neighborhoods for a proper polynomial map.

## Regular fiber sheet count — paper argument pending API audit

At a regular target value, the actual fiber polynomial is monic of degree d, splits over ℂ and has no multiple roots by the proved derivative-avoidance theorem. Its root multiset therefore has d elements and no repetitions. The exact finite-set cardinality adapter still needs a corpus audit before formalization.

## Stronger coordinate rigidity — complete paper proof [PROVED HERE]

The cyclic-coordinate argument gives the sheet count itself, without assuming finiteness. Let a nonempty type A carry a permutation T and an injective nonzero complex coordinate u. Suppose all u(a)^d agree and u(Ta)=ζu(a), where ζ is a primitive d-th root and d>0. Fix a₀∈A. Iteration gives u(T^k a₀)=ζ^k u(a₀). The map k↦T^k a₀ from 0≤k<d is injective: cancel the nonzero u(a₀), then use distinctness of the first d powers of a primitive root. It is surjective: for any a, the quotient u(a)/u(a₀) has d-th power one, hence equals ζ^k for some k<d; injectivity of u gives a=T^k a₀. Thus A is explicitly equivalent to Fin d, and T is a full cycle. Neither a finite-sheet assumption nor algebraic root counting is needed. Applying this stronger theorem to the exterior coordinate should supply both the exterior cycle and exact degree-many sheets at once. The earlier root-multiset argument remains an independently available adapter, not a required premise.

## Remaining geometry

Even after the exterior cycle is proved, the product of a chosen meridian system must be identified with that exterior loop, and adjacent critical-value exchanges must be constructed and shown to induce Hurwitz moves. The exterior theorem will not itself establish either relation or prescribed planar realization.

## Log

- 2026-10-09 — exact cyclic-coordinate and reciprocal-exterior proofs recorded before new Lean code. Native simple-branch monodromy is in final production/axiom/source audit; compiler ownership remains sequential.

- 2026-10-09 — native covering identification and positive-circle transposition are now fully audited, indexed, and pass authoritative global lint. The precise `IsCycleOn IsPrimitiveRoot` corpus query returned no hits. `/tmp/hgt-primitive-coordinate-cycle.lean` contains four statements from the stronger paper proof above and is in its first compiler check: coordinate iteration, an explicit degree-sized orbit bijection, full-cycle action, and exact natural cardinality without a finiteness hypothesis. Exterior reciprocal-coordinate formalization has not yet begun.

- 2026-10-09 — all four primitive-coordinate rigidity statements pass the first scratch Lean check, over an arbitrary field and an arbitrary sheet type. `PrimitiveCoordinateCycle.lean` enters production build, axiom audit and final actual-source check. The explicit orbit bijection derives both full cyclicity and exact sheet count without a finiteness assumption. Next: the reciprocal germ and actual analytic power coordinate at infinity.

- 2026-10-09 — primitive-coordinate rigidity is fully audited: `../3-formalized/primitive-coordinate-cycle-rigidity.md`, four theorems, production build, four standard-only axiom audits and empty final-source check. The completed implementation scratch is removed. `/tmp/hgt-polynomial-reciprocal-power-coordinate.lean` now contains the five paper-derived reciprocal-germ and coordinate statements and is in its first compiler check.

- 2026-10-09 — all five reciprocal-germ and infinity-coordinate statements pass scratch Lean. `PolynomialReciprocalPowerCoordinate.lean` enters production build after the root-phase path check. The exact identity needs only a nonzero inverse coordinate; the analytic germ order equals the monic polynomial's degree. Initial errors were a missing analytic-polynomial import, computability annotation, and confusing evaluation of the zero polynomial with evaluation at zero; all are repaired. Root-phase paths pass except for an endpoint coercion lemma name, now replaced by a direct typed expression and rechecked. Large-circle capture and actual exterior lift are not yet formalized.

- 2026-10-09 — reciprocal-coordinate production build passes. All six root-phase declarations pass scratch: continuous phase, initial value one, constant unit norm, nonvanishing, exact d-th power circle identity, and endpoint multiplier exp(2πi/d). `PowerRootCirclePaths.lean` production build, all eleven reciprocal/phase axiom audits and both actual-source final checks are running sequentially. The large-circle capture theorem is next.

- 2026-10-09 — reciprocal infinity coordinates and root-phase paths are fully audited: `../3-formalized/polynomial-reciprocal-power-coordinate.md`, two modules and eleven declarations, all production builds, standard-only axiom audits and final-source checks pass. Completed implementation scratches removed. `/tmp/hgt-polynomial-exterior-power-chart.lean` now constructs actual infinity-chart data plus a large avoiding circle controlling every root, and derives nonzero, common-radius and injective fiber coordinates. It awaits its first compiler check after index/lint refresh. Full exterior monodromy remains unproved.

- 2026-10-09 — `PolynomialExteriorPowerChart.lean` passes scratch and production leaf build: an actual infinity chart and one large avoiding circle capture every root, with nonzero, common-radius and injective coordinates. No distinct-critical-value assumption is needed. `/tmp/hgt-polynomial-exterior-root-lift.lean` is in its first compiler check; the explicit negative phase in the infinity coordinate lifts the positive target circle. `/tmp/hgt-polynomial-exterior-cycle.lean` and `/tmp/hgt-polynomial-exterior-monodromy.lean` contain the subsequent coordinate-rigidity and native-covering consequences, not yet compiled. Final axiom/source audits remain pending for this four-module batch.

- 2026-10-09 — all four exterior modules now pass scratch Lean checks. `PolynomialExteriorPowerChart`, `PolynomialExteriorRootLift`, and `PolynomialExteriorCycle` also pass production leaf builds. `PolynomialExteriorMonodromy` is building. The checked final theorem constructs a positive exterior circle in the actual regular target, proves its native covering monodromy is a full cycle, and proves its fiber has exactly n+2 sheets, for every parameter including critical-value collisions. Twelve axiom reports (eleven explicit declarations plus the structure constructor) and four final actual-source checks are prepared. Next geometric card: `polynomial-rectangle-meridian-product.md`; its strip-cancellation identity has a complete paper proof, while explicit avoiding homotopies remain under construction.

## Formal certificate — 2026-10-09

Four modules, eleven explicit public declarations: `PolynomialExteriorPowerChart` (structure plus four theorems), `PolynomialExteriorRootLift` (two), `PolynomialExteriorCycle` (three), and `PolynomialExteriorMonodromy` (one). All four production leaf builds pass. All twelve axiom reports, including the structure constructor, contain only `propext`, `Classical.choice`, and `Quot.sound`. All four final actual-source `lake env lean` checks pass with empty logs. Axiom log: `/tmp/hgt-polynomial-exterior-axioms.log`; final logs: `/tmp/hgt-PolynomialExteriorPowerChart-final.log`, `/tmp/hgt-PolynomialExteriorRootLift-final.log`, `/tmp/hgt-PolynomialExteriorCycle-final.log`, `/tmp/hgt-PolynomialExteriorMonodromy-final.log`. All four modules are wired into the HTGeometry umbrella. Index/lint refresh follows.

The native-covering theorem needs only the actual parameter v; distinct critical values are not assumed. It constructs a positive exterior circle, proves its monodromy is a full cycle and its fiber has exactly n+2 sheets. Completed implementation scratches are removed. The next unresolved geometry is `../1-in-progress/polynomial-rectangle-meridian-product.md`, followed by geometric Hurwitz exchanges and controlled realization/collision. No prescribed planar realization, actual Xi embedding, external novelty certificate or RH conclusion follows yet.

Index refresh passed (`/tmp/hgt-polynomial-exterior-index.log`). Authoritative global lint reports only two unrelated unreachable RHTower modules: `LeeYangSplitCountDifference` and `PaperSuzukiCayleySynthesis`; no error concerns the exterior modules (`/tmp/hgt-polynomial-exterior-lint.log`).
