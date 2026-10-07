# Exact toric closure of the simultaneous Xi source

- **ID:** RH-XPTC-20261007
- **Stage:** 1-in-progress
- **Type:** PAPER THEOREM; actual-source quadratic kernel/image and affine-chart algebra formalized
- **Parent route:** `xi-legendre-formal-source-section.md`; simultaneous marked blowup in `xi-legendre-integral-cylinder-comparison.md`
- **Objective:** determine which algebraic geometry the actual prime-marked Xi source permits, before asserting a correspondence between its compact carriers.

## Exact statement

Write `e_n(s)=exp(-s*log(n))` and `d_n(s)=xi(s)*e_n(s)` for every positive integer `n`. All rings of functions below use pointwise operations and constant complex scalars. Let

```
ev : C[X_n | n>=1] -> O(C),   X_n |-> d_n.
J = (X_a*X_b-X_1*X_(a*b) | a,b>=1).
R = C[x_p | p prime].
```

Then:

1. `ker(ev)=J`. Equivalently, a polynomial relation holds precisely when, for each pair `(d,N)`, its coefficients summed over monomials of total degree `d` and integer product `N` vanish.
2. Its image algebra is isomorphic to `A=C+t*R[t]`, via `d_n <-> t*prod_p x_p^(v_p(n))`.
3. For every finite set of distinct primes, the corresponding `d_p` are algebraically independent over `C`. The same is true after restricting to any nonempty open subset of `C`.
4. For distinct primes `p,q`, the elliptic curves `y^2=x*(x-1)*(x-(1+d_p))` and `y^2=x*(x-1)*(x-(1+d_q))` have no nonzero homomorphism over the algebraic closure of the meromorphic function field, or of any field of meromorphic germs. In particular, a finite base change cannot produce a prime-to-prime isogeny.
5. For the vertex ideal `I=t*R[t]` of `A`, the blowup is the single affine chart `Spec R[t]`. Its exceptional fibre is `Spec R`. The actual source lifts to this chart as `(t,x_p)=(xi(s),p^(-s))`, retaining all prime marks at a zero without requiring a simple zero.

The isogeny obstruction also applies to the entire five-channel Humbert Jacobian/Prym carrier: for `p!=q`, the generic Jacobians `J(H_(d_p))` and `J(H_(d_q))` have zero Hom over the algebraic closure of the meromorphic field. Allowing mixing among its five elliptic factors does not repair this obstruction.

The pairwise statement is stronger than the prime-indexed formulation: `d_m,d_n` are algebraically independent whenever `m,n` are distinct positive integers. In a pair of monomials, equal total degree and equal integer product imply `(m/n)^(a-a')=1`, hence equal exponents. More generally, for distinct complex constants `a,b`, the pair `xi(s)*exp(a*s), xi(s)*exp(b*s)` is algebraically independent: equality of the degree and exponential parameter gives `(k-k')*(a-b)=0`. Thus the same generic no-Hom conclusion holds for all distinct positive-integer channels. This is a consequence of the same classical mechanism, not a separate novelty claim.

**Functional-equation consequence [P].** For every integer `n>1`, even a single marked channel cannot acquire a nonzero generic homomorphism to its functional-equation pullback. Indeed,

```
d_n(1-s) = n^(-1) * xi(s) * exp(s*log n).
```

The two exponential parameters `-log n` and `+log n` are distinct, so the preceding pair theorem makes `d_n(s),d_n(1-s)` algebraically independent; multiplying one coordinate by a nonzero constant preserves independence. The same modular-correspondence argument excludes Hom between the Legendre families, and all 25 elliptic-factor comparisons exclude Hom between the Humbert families. This forbids a nonzero algebraic map of these families lifting reflection by fibrewise homomorphisms. It does not forbid the formal act of twisting a scheme by a base automorphism, topological comparison of degenerations, or an action on the marked source algebra itself. The `n=1` channel is the explicit exception: its parameter is Xi, fixed by reflection. No new novelty claim follows: this is a stronger consequence of the same classical parent mechanism. Targeted corpus and arXiv phrase searches returned no exact hits, which is not an exhaustive novelty audit.

## Source input and dependency audit

The source-specific input is the existing unconditional theorem `RHTower.xi_hypertranscendental` in `XiHypertranscendenceUnconditional.lean`. It is reached from the filtered prime-power coefficient source exposed by the exact `+2` shift of `xi'/xi`, not from a hypothetical RH premise. `XiShiftPrimeHypertranscendence.lean` uses the nonzero prime layer and the prime-valuation leading-echelon theorem, followed by the existing faithful finite-abscissa analytic transfer. This argument adds no positivity, spectral construction, numerical experiment, or estimate. Its geometric conclusion concerns exact vanishing ideals and algebraic correspondences.

The elementary differential-algebra fact used below is that a finite differential-algebraic field extension followed by an algebraic extension remains differential-algebraic. The corpus already proves the relevant base-change theorem in `DifferentialAlgebraicBaseChange.lean`. This does not assert that products of arbitrary hypertranscendental functions remain hypertranscendental.

## Dependency-closed paper proof

Fix a finite polynomial `P`. A monomial `prod X_n^(a_n)` evaluates to

```
xi(s)^d * exp(-s*log(N)),
d=sum a_n,  N=prod n^(a_n).
```

Group its terms by `d`. The result is `sum_d F_d(s)*xi(s)^d`, with every `F_d` a finite sum of the entire functions `e_N`. Each such function satisfies the exact first-order equation `e_N'=-log(N)*e_N`, so the meromorphic field generated by the finitely many `e_N` is differential-algebraic over `C(s)`. Hypertranscendence of Xi says that Xi is transcendental over this field: otherwise the differential-algebraic tower law would make Xi differential-algebraic over `C(s)`. Consequently every `F_d` must be identically zero.

For distinct positive integers `N_1,...,N_r`, the functions `e_(N_j)` are linearly independent over `C`. Differentiate an alleged constant linear relation `0,...,r-1` times at zero. The resulting Vandermonde matrix has parameters `-log(N_j)`, which are distinct; its determinant is a product of nonzero differences. Thus every grouped coefficient vanishes. This is an exact derivative and determinant identity, without an asymptotic argument.

The displayed quadrics vanish under `ev`. Conversely, modulo their ideal, every nonconstant degree-`d` monomial with integer product `N` equals `X_1^(d-1)*X_N`: combine two factors using one quadric, and induct on the number of factors. Distinct normal forms have the independent images just proved. This proves (1). Unique prime factorization identifies `e_N` with the monomial of exponent vector `(v_p(N))`; normal forms are exactly `1` and `t^d*prod x_p^(v_p(N))`, `d>=1`. This proves (2).

For prime-indexed variables, equality of integer products forces equality of exponent vectors. Hence no two distinct monomials have the same normal form, proving (3). A relation on a nonempty open subset extends globally by the identity theorem for entire functions.

For (4), the Legendre invariant is the nonconstant rational function

```
j(lambda)=256*(1-lambda+lambda^2)^3/(lambda^2*(1-lambda)^2).
```

Algebraic independence of `d_p,d_q` implies algebraic independence of their two `j`-invariants: adjoining either original variable to its rational image is algebraic, and the product rational map is dominant. An isogeny would put the pair on one of the proper modular correspondences `Phi_N(j_p,j_q)=0`. Every nonzero homomorphism of elliptic curves is an isogeny; factoring its kernel first removes a multiplication map and leaves a cyclic isogeny, hence one such `N`. A relation over any finite extension would already hold in the original field by injectivity. A germ relation extends by the identity theorem. Contradiction. The classical modular-correspondence parent is Elkies, [Modular curves parametrizing isogenies](https://people.math.harvard.edu/~elkies/xisog.pdf), Section 3. This conclusion concerns generic families; it does not forbid isolated isogenous fibres.

For (5), `I^2=t*I`. In the Rees algebra, every degree-one generator `t*m*U` has square `(t*U)*(t*m^2*U)`. Therefore a homogeneous prime not containing the irrelevant ideal cannot contain `t*U`; its distinguished open covers the entire Proj. This chart is

```
A[I/t] = C[t,x_p | p prime] = R[t].
```

On this chart the inverse image of `I` is `(t)`, so its exceptional fibre is `Spec R`. The lift follows from the exact quotient `d_n/xi=e_n`, which extends over each zero. This is an infinite-generator blowup, and is not a proper finite-type blowup: its exceptional fibre is an affine scheme with infinitely many algebraically independent coordinates. No compactness may be inferred from the word "blowup" in this construction.

For the five-channel assertion, use the paper-verified isogeny decomposition of `J(H_delta)` into its five elliptic quotients. Four have Legendre parameters `delta,1+delta,-delta,1-delta`; the fifth has four branch points `0,1,-delta,1-delta`, whose cross-ratio can be taken as `(delta^2-1)/delta^2`. Every resulting `j`-invariant is a nonconstant rational function of `delta`. The algebraic-independence argument therefore excludes Hom between each of the 25 cross-prime pairs of elliptic factors. A homomorphism between the products has these 25 component maps, hence is zero. Composing with the decomposition isogenies gives zero Hom between the Jacobians: a nonzero homomorphism cannot be killed by composition with finite-kernel isogenies because its image is a positive-dimensional connected abelian variety. The same applies to the Prym once the classical Prym/Jacobian identification in the parent card is used. No unproved integral cylinder comparison is a premise of this obstruction.

## Hostile audit

**BRIDGE.** The toric ideal mechanism is classical; see Sturmfels, [Equations Defining Toric Varieties](https://arxiv.org/pdf/alg-geom/9610018), Lemma 1.1. The proof above supplies its particular kernel directly, including infinitely many generators by finite support. No new general theory of toric ideals or differential algebra is claimed. The application closes a concrete proposed transport mechanism: distinct prime-marked Legendre families cannot be joined by an algebraic isogeny, even though their degenerations occur at the same Xi zeros.

The positive survivor is stronger than this obstruction: an exact presentation of the entire source algebra, its canonical affine blowup, and its retained prime-marked exceptional fibre. This is not an RH proof. It remains valid for any hypertranscendental entire function in place of Xi. Its global independence does not imply algebraic independence of the numbers `p^(-rho)` at an individual zero; no Schanuel-type assertion is imported.

Corpus audit: deep search `xi prime exponential algebraic independence Zariski` completed without a partial flag. It found Xi hypertranscendence and prime-source coefficient-independence machinery, but no exact kernel/pinching theorem. This is a search finding, not proof of novelty. Primary-source searches located the classical toric and isogeny parents. Significant novelty is not certified.

## Work checklist

The verified quadratic formalization uses the monoid of normal forms directly. For an additive commutative monoid `M`, its elements are `unit` and `term(k,a)` (`k>=0`, `a in M`), with `term(k,a)*term(l,b)=term(k+l+1,a+b)`. Map `X_a` to the basis element `term(0,a)` of its monoid algebra. In the quadratic quotient, send `term(k,a)` back to `X_0^k*X_a`; the defining quadric proves multiplicativity. These maps are inverse: on generators this is immediate, and `term(k,a)=term(0,0)^k*term(0,a)`. This proves the exact quadratic presentation without cancelling `X_0` before its regularity is known. The faithful polynomial realization sends `unit` to `1` and `term(k,a)` to `T^(k+1)*[a]`; distinct degree/label pairs give distinct basis elements. This is the dependency-closed algebraic proof in `HomogenizedMonoidAlgebra.lean`, still a classical bridge.

The affine-chart proof works in the localization of `B[T]` at `T`, where `B=R[M]`. The polynomial map is injective because every power of `T` is regular. Under the faithful quotient realization, the ratios `qVar(a)/qVar(0)` equal the constant monomials `[a]`. Hence the subalgebra generated by the source and these ratios is precisely the image of `B[T]`: it contains `T`, every `[a]`, and every scalar; conversely both kinds of generators are polynomial. Extension of the vertex ideal is `(T)`, whose quotient is `B`. This avoids introducing a naive quotient by `T*Y_a-qVar(a)`, whose `T`-torsion would otherwise need to be removed. The classical parent is [Stacks, Blow up algebras](https://stacks.math.columbia.edu/tag/052P), Definition 10.70.1 and Lemmas 10.70.2/10.70.6; [Blowing up](https://stacks.math.columbia.edu/tag/01OF) supplies the scheme interpretation. Those definitions allow arbitrary ideals. No finite-generation or properness hypothesis is introduced.

- [x] State exact conjecture and attack its strongest classical parents.
- [x] Complete paper proof, including strongest positive survivor.
- [x] Verify source theorem's current Lean interface and axiom closure.
- [x] Formalize actual Xi evaluation and the complete grouped degree/exponential-parameter relation criterion.
- [x] Formalize algebraic independence of the whole prime family and of any pair with distinct complex parameters.
- [x] Translate the integer-source normal form to integer products and prove the displayed quadratic-ideal presentation in Lean (actual upper-end meromorphic germs).
- [ ] Formalize the generic geometric no-Hom interpretation, including the functional-equation pullback.
- [x] Formalize the affine blowup algebra in a faithful common localization, its vertex-ideal extension, and its exceptional quotient, without finiteness assumptions.
- [x] Connect the actual graded Rees algebra and its full Proj scheme to the verified chart, preserving source and ratio coordinates.
- [x] Identify the arithmetic monoid algebra with prime-variable polynomials, preserving each prime mark.
- [x] Update the route ledger with separate Lean and paper statuses.

Verified scheme proof: `ReesGrading.lean` grades `reesAlgebra I` by monomials `c*U^n` with `c in I^n`, with finite-support decomposition. `HomogenizedMonoidProjCover.lean` identifies its irrelevant ideal with the ideal spanned by `reesGenerator a`, using `I^(n+1)=(t)^n*I`. The Rees-prime criterion makes `D_+(t*U)` all of native Proj. `HomogenizedMonoidProjectiveBlowup.lean` sends a native homogeneous fraction `(c*U^n)/(t*U)^n` to `c/t^n` in the verified common localization. This map is injective by homogenizer regularity, with image exactly `affineChart`. Native Proj's chart isomorphism then gives the full scheme isomorphism with `Spec R[M][T]`. Separate coordinate theorems preserve both the source map and every mark `qVar(a)/qVar(0)`. `HomogenizedIntegerBlowup.lean` supplies the unique-factorization coordinate equivalence and the full prime-coordinate scheme isomorphism. The actual source image is transported to the pinched prime-polynomial range in `XiIntegerSourceToricIdeal.lean`; its direct source-file audit and targeted build both pass.

The follow-up attack "add functional-equation symmetry and then force all exceptional points fixed" was checked against polynomial-multiplier counterexamples. This is **REDISCOVERED**, not a fresh route: `verified-height-amplification.md` already isolates the missing source-to-divisor selection law and observes that free-orbit quartics preserve generic symmetry while changing the full Euler logarithmic derivative. `euler-functional-equation-independence.md` records explicit quartet constructions. The present source-algebra calculation does not escape that boundary merely by retaining infinitely many monoid labels. Deep search completed without a partial flag but had weak relevant hits; direct ledger/card search located these prior obstructions. No duplicate Lean leaf is warranted for that attack.

`[OPEN CORE]` for RH remains a source-derived operation on the marked exceptional geometry that forces the functional-equation partner to lie on the same zero component. Neither the presentation nor the blowup supplies that operation. The failed finite-isogeny producer must not reappear as an assumed naturality map.

## Log

- 2026-10-07 — `HTGeometry/HomogenizedMonoidAlgebra.lean` now proves the quadratic kernel and explicit quotient equivalence for every commutative coefficient ring and additive commutative monoid, without cancellation assumptions. `RHTower/XiIntegerSourceToricIdeal.lean` transports this presentation through the injective logarithmic label map and the actual Xi evaluation. Both direct leaf checks and targeted builds passed; the generic kernel, quotient equivalence, and actual Xi kernel have only `propext`, `Classical.choice`, `Quot.sound`. Both leaves are registered. The actual carrier in Lean is the upper-end meromorphic germ field; the entire-function interpretation uses the paper identity-theorem argument. These remain classical structural bridges, not significant novelty or an RH result. The Rees search returned partial results with a worker-disconnection error; available hits do not justify Noetherian or finite-generation assumptions.

- 2026-10-07 — two-division bridge verified in `LegendreSourceKummer`; actual source-algebra closure and isogeny obstruction derived on paper. Next task is the actual Xi kernel formalization, not another arbitrary carrier identity.
- 2026-10-07 — scratch audit confirmed the current `RHTower.xi_hypertranscendental` statement and axioms exactly `propext`, `Classical.choice`, `Quot.sound`. The scratch API probe also rejected a guessed scalar-field alias; use the actual `xiRotatedUpperEndCarrier_hypertranscendentalOver` over `upperEndRationalCoordinateField` and explicit restriction of scalars.
- 2026-10-07 — formalization now constructs all complex exponential upper-end germs, their constant-coefficient differential equations, and the differential field they generate. The intended faithful algebra is `C[(C,+)][T]`, evaluated by `exp(a*z)` and the actual rotated Xi carrier. The deep coefficient-field search returned partial coverage; its source hits supplied the existing Artin-shortening and first-order DA interfaces. Scratch work remains in `/tmp/hgt_xi_exp_source.lean`; no formal completion claimed yet.
- 2026-10-07 — `RHTower/XiExponentialSourceRelations.lean` passes direct Lean checking without warnings and its targeted `--old` build passes (9157 dependency jobs; no umbrella build). Its actual carrier is `xi(-I*z)*exp(a*z)`. `source_relation_iff_grouped_coefficients` proves the complete finite-polynomial relation criterion for arbitrary parameter families. `prime_source_algebraicIndependent` has no unproved source premises; `source_pair_algebraicIndependent` requires only distinct complex parameters. Axiom audits of these results, the faithful polynomial evaluation, and Xi hypertranscendence over the exponential field report exactly `propext`, `Classical.choice`, `Quot.sound`. Umbrella registration and indexing are complete. Global lint reports 15 unrelated unreachable modules and stale generated API/overview files after concurrent source changes; it is not globally clean. The arithmetic product/quadratic-ideal presentation, Rees chart, and geometric no-Hom theorems remain paper-only. Own obsolete scratch files were removed.

- 2026-10-07 — `HomogenizedMonoidPinching.lean` passes direct checking and its targeted build. It identifies the image as `R+T*R[M][T]`, proves homogenizer regularity, every vertex-ideal power, and the degree-one Rees-prime covering criterion. `HomogenizedMonoidBlowupChart.lean` passes direct checking: the common overring is proved to localize both the source and polynomial algebra; the chart adjoins ratios of all vertex-ideal elements, is equivalent to `R[M][T]`, and has exceptional quotient `R[M]`. Full Proj identification is still separate. `XiIntegerSourceToricIdeal.lean` also passes its updated direct check with explicit source-image algebra equivalences. Targeted builds of both new leaves pass (1575 and 1599 jobs); the updated actual-source leaf build also passes (9159 jobs). The final combined audit of eleven kernel/image/regularity/ideal/chart/exceptional results passes; every result uses exactly `propext`, `Classical.choice`, `Quot.sound`. Global `lint --check-generated` reports 16 unrelated unreachable modules; no own-leaf lint error or generated-file staleness was reported. The lint gate is not globally clean.

- 2026-10-07 — final checkpoint: all owned foreground jobs terminated; source, generic presentation, pinching, and chart leaves pass their direct checks and necessary targeted artifact builds. All four leaves are registered; generated index refreshed; scoped whitespace checks pass. No commit or push. Temporary own scratch files removed after the combined axiom audit. Verdict remains **BRIDGE**; no significant novelty or RH conclusion is certified. The positive survivor is not retired as complete: native Proj, prime-variable coordinates, and generic geometric no-Hom remain explicit work items.

- 2026-10-07 — continuation: previous turn classified progress; active objective reread. Native Rees grading is now the next obligation, represented by finite polynomial coefficients rather than a finiteness assumption on the ideal. Deep corpus query `Rees algebra grading homogeneous decomposition polynomial coefficient` completed with `partial=false`, no errors, 68,055 inventoried files, mostly pending compiler coverage; exact `reesAlgebra` search found only the already verified source leaf. No reusable native grading was found. Scratch construction is underway; no new formal completion claimed.

- 2026-10-07 — `ReesGrading.lean` passes direct checking and targeted build (1582 jobs), constructing the native grading and irrelevant-ideal constant-coefficient criterion for arbitrary ideals. `HomogenizedMonoidProjCover.lean` passes direct checking: the actual native irrelevant ideal equals the marked degree-one ideal, the homogenizer basic open is all of native Proj, and `projIsoHomogeneousChart` gives the full scheme-to-homogeneous-localization isomorphism. The remaining bridge sends homogeneous fractions to the previously verified affine chart; scratch proof is underway. These remain classical structural obligations.

- 2026-10-07 — `HomogenizedMonoidProjectiveBlowup.lean` passes direct checking and its targeted build (2455 jobs), including the full native scheme isomorphism and source/mark coordinate compatibility. `HomogenizedIntegerBlowup.lean` passes direct checking: unique factorization supplies the additive monoid equivalence and the full scheme isomorphism in prime-variable coordinates. The actual Xi image is being transported into these coordinates explicitly; no source premise is added.

- 2026-10-07 — hostile follow-up: adjoining all derivatives is **REDISCOVERED** as a proposed way to create algebraic constraints. The existing `xi_hypertranscendental_expField` already says every Xi derivative is algebraically independent over the exponential differential field. With `e_n=exp(-s log n)`, the triangular identities `D^k(xi*e_n)=e_n*sum_(j<=k) binom(k,j)*(-log n)^(k-j)*D^j(xi)` do not alter that freedom. Infinite differential polynomial rings have finite-support polynomial relations; merely admitting all orders cannot produce a relation absent at every finite order. The classical parent is differential-polynomial freeness ([Tressl, Section 1.2](https://personalpages.manchester.ac.uk/staff/marcus.tressl/papers/ModelTheoryOfDifferentialFields.pdf); [Pong, Section 2](https://math.csudh.edu/~pong/download/rankineq.pdf)). The positive survivor is the already formalized hypertranscendence over the full exponential field. No duplicate jet-algebra leaf is warranted. This does not exclude analytic completion or operations retaining the full Euler source. Deep corpus search completed nonpartially with no errors; semantic hits were broad and do not certify novelty.

- 2026-10-07 — final source checks: all four new geometry leaves and the updated actual Xi source leaf pass `lake env lean`; necessary targeted builds pass (Rees grading 1582 jobs, Proj cover 2454, full scheme 2455, prime coordinates 2456, actual Xi source 9165). A combined audit of sixteen grading, scheme, coordinate, source-image, and hypertranscendence results reports exactly `propext`, `Classical.choice`, `Quot.sound`. All new leaves are wired; scoped whitespace and forbidden-declaration checks pass. After index refresh, final global lint reports only five unrelated unreachable HTGeometry modules: `ApertureConeCalculus`, `ApertureConeWinding`, `ApertureLogTranslation`, `ApertureOpenHistoryIdeal`, and `BoundaryCoronaCStarAlgebra`. No own-leaf lint error or generated-file staleness remains in that check; the global gate is not clean. No full or umbrella build, heartbeat override, numerical experiment, commit, or push was used. The next active attack is recorded in `xi-marked-joint-monodromy.md`; no RH result or significant novelty is certified.
