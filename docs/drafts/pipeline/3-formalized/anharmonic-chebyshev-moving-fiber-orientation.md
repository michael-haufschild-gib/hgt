# Anharmonic Chebyshev moving-fiber orientation sector

- **ID:** anharmonic-chebyshev-moving-fiber-orientation
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Rouyea--Bourgeois (2026), Proposition 6.9 and Remark 6.10; new invariant-coordinate orientation analysis
- **Statement:** Möbius recentering retains an exact finite moving anharmonic fiber. Its actual-Xi q-covariant standard sector satisfies the sharp global separation `E_q(s) > 2T_q(s)²` for every real `s>2`, with ratio tending to `2` cofinally; every scalar holomorphic quadratic alternative is isotropic.

## Goal

Identify information discarded by the scalar `q²` Chebyshev descent and determine whether the
scale-dependent Möbius scan really requires infinite source data, or only changes source anchors.
Result must expose a concrete positive survivor and connect it to actual completed Xi, not merely
restate a representation-theoretic obstruction.

## Gates

- [x] 0 → 1 in-progress: source-pure statement, explicit hostile tests, literature baseline identified
- [x] 1 → 2 fully-proven: exact algebraic proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3 formalized: Lean modules named below; direct compile and axiom audit pass
- [ ] 3 → 4 publication-ready: standalone novelty audit and arithmetic consequences remain open

## Literature baseline

- Zhang, [A Hausdorff moment problem and the Riemann hypothesis](https://arxiv.org/abs/2303.09396),
  proves an RH-equivalent Hausdorff finite-difference criterion. Corpus theorem
  `scaledPrimeArchHausdorffMomentDifferencesNonnegative_iff_riemannHypothesis` already gives an
  endpoint-calibrated form, so no duplicate alias was added.
- Rouyea--Bourgeois,
  [A Chebyshev Trace Criterion for the Riemann Hypothesis](https://www.alphaxiv.org/abs/2608.chebyshev-trace-riemann-hypothesis),
  gives the order-three quotient, `q²` descent, Koebe trace, bounded-trace RH criterion, and the
  scale-dependent Möbius scan. Their Remark 6.10 correctly says recentered coefficients generally
  depend on infinitely many *original trace coefficients* and therefore leave their fixed
  three-point information class.
- The moving-fiber reinterpretation and `q`-normalized Xi orientation energy below are not claimed
  in that paper. They are new to this corpus. External novelty beyond this targeted current-source
  audit remains to be established before publication.

## Conjecture loop

### C1 — scalar holomorphic orientation energy

**Conjecture.** An odd or standard `S₃` sector supplies a scalar holomorphic positive orientation
detector lost by `q²` descent.

**Hostile test.** Classify every cyclic-invariant quadratic on difference coordinates
`p = a-b`, `q = b-c`.

**Failure.** Every such quadratic is a scalar multiple of

`p² + p q + q²`.

Over `ℂ` this Casimir is isotropic on the nonzero vector
`(p,q) = ((-1+i√3)/2,1)`. Scalar holomorphic quadratic positivity is impossible.

### C2 — doubled Hermitian survivor

**Conjecture.** Conjugate doubling repairs isotropy.

**Result `[PROVED HERE]`.** The energy

`‖a-b‖² + ‖b-c‖² + ‖c-a‖²`

is cyclic- and reflection-invariant, nonnegative, and zero exactly when `a=b=c`. Positivity forces
a Hermitian/doubled sector; trivial-sector scalar compression cannot retain orientation.

### C3 — moving locality under Möbius scanning

**Conjecture.** Recentring destroys fixed locality but retains finite moving-orbit locality.

**Hostile test.** A generic statement that order-`n` coefficients depend on an order-`n` jet at the
new center is only chain-rule infrastructure. Require exact source anchors, fiber cardinality,
real-sheet geometry, Koebe center, and actual Xi current.

**Result `[PROVED HERE]`.** For `s,z ∉ {0,1}`,

`q(z)² = q(s)²`

iff `z` belongs to the cyclic orbit of `s` or the cyclic orbit of `1-s`. For real `s>2`, one cyclic
orbit has points in `(2,∞)`, `(1/2,1)`, and `(-1,0)`. An explicit real center `a(q)∈(0,1)` satisfies

`27 a(q)/(1-a(q))² = q²`.

Thus Möbius scanning leaves fixed exceptional-point locality but retains finite moving six-point
locality, folded by Xi's functional equation to a moving three-point orbit.

## Invariant-coordinate split

Define

`D_q log xi(s) = (xi'/xi)(s) / q'(s)`

with

`q'(s) = 1 + 1/s² + 1/(s-1)²`.

The Jacobian satisfies the exact cyclic covariance laws

`q'(w(s)) w'(s) = q'(s)`,

`q'(w²(s)) (w²)'(s) = q'(s)`.

For every real `s>2`, the descended product current splits exactly as

`D_q log (xi(s) xi(w(s)) xi(w²(s)))`

`= D_q log xi(s) + D_q log xi(w(s)) + D_q log xi(w²(s))`.

This sum is the trivial sector. The standard-sector energy

`E_q(s) = Σ_cyclic ‖D_q log xi(s) - D_q log xi(w(s))‖²`

is nonnegative, invariant under the cyclic generator and reflection, and vanishes exactly when all
three `q`-coordinate Xi logarithmic derivatives coincide.

## Higher-principle interpretation

Repeated scalar-positivity failures are shadows of one quotient principle: invariant scalar descent
retains the trivial representation and erases the standard representation. Over `ℂ`, the unique
holomorphic quadratic Casimir on that standard sector is isotropic. Positive orientation data
therefore cannot live in one scalar holomorphic channel; it requires conjugate doubling. The correct
derivatives are taken in invariant quotient coordinate `q`, not source coordinate `s`.

## Formal certificate

- `formal/GaloisForLFunctions/RHTower/AnharmonicChebyshevOrientationCasimir.lean`
  - literature quotient/Koebe algebra
  - invariant quadratic classification and explicit isotropic witness
  - Hermitian positive survivor
- `formal/GaloisForLFunctions/RHTower/AnharmonicChebyshevMovingFiber.lean`
  - exact three-/six-point fiber classification
  - real moving-orbit chambers and explicit Koebe scan center
  - actual Xi moving-three-point logarithmic current
  - `q`-normalized trivial/standard split and full-`S₃` Hermitian energy
- Both modules compile with this toolchain.
- Audited representative theorems depend only on `propext`, `Classical.choice`, and `Quot.sound`.
- No `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` declaration occurs in either module.

## Open core and falsifiers

1. **Arithmetic producer:** derive a completed prime--Gamma formula for the three
   `D_q log xi` components or for `E_q(s)`. Algebra alone supplies no sign or bound.
2. **Non-theatre falsifier:** if the completed source formula is only an identity with an uncontrolled
   cross term, this lane does not advance RH and must pivot.
3. **Useful target:** a source-pure bound or monotonicity law for `E_q(s)` coupled to the Chebyshev
   trace current. Any claimed RH consequence must pass the existing exact-tail audit.
4. **Publication gate:** search current literature specifically for invariant-coordinate orbit
   variance of logarithmic derivatives before claiming external novelty.

## Log

- 2026-08-22 — literature baseline checked; C1 falsified with exact classification and isotropic witness.
- 2026-08-22 — C2 Hermitian survivor proved on paper and in Lean.
- 2026-08-22 — C3 strengthened from generic finite jets to exact moving fibers, explicit scan center,
  and actual Xi invariant-coordinate split; formalized and axiom-audited.

## C4 — Noether/Jacobi fibre current is strictly present

**Cross-corpus mechanism audit.** Wide corpus searches covered Noether currents, covariant
derivatives, Hermitian Casimirs, graph-Laplacian kernel recovery, quantum Fisher variance,
Jacobi/centre-of-mass coordinates, Hodge splitting, Ward identities, causal cone flux, quotient
information loss, and holonomy. Two filters removed theatre:

1. Casimir/QFI nonnegativity alone is a renamed sum of squares and cannot select RH.
2. A transferable mechanism must produce an actual Xi statement stronger than generic positivity.

The surviving synthesis combines three-body Jacobi splitting with the already-formalized strict
real-axis Xi response. For arbitrary `a,b,c : ℂ`, Lean proves

`3 (‖a‖² + ‖b‖² + ‖c‖²) = ‖a+b+c‖² + E(a,b,c)`.

Thus quotient-visible trace and quotient-invisible Casimir are exact orthogonal energy sectors. For
the actual q-covariant Xi orbit and every real `s>2`, the three real parts have signs

`(+,+,-)`.

Reason: two orbit points lie right of `1/2`, one lies left, Xi's centered logarithmic derivative is
strictly positive on the right real ray, the functional equation reverses its sign on the left,
and `q'` is positive on the real axis. Hence

`E_q(s) > 0`.

**Result `[PROVED HERE]`.** Scalar moving quotient descent is nowhere information-complete on its
real scan sheet: it discards a strictly nonzero actual-Xi standard current at every `s>2`. This is
stronger than the prior abstract zero criterion and does not assume RH.

**Formal certificate.**

- `formal/GaloisForLFunctions/RHTower/AnharmonicChebyshevNoetherCasimir.lean`
  - exact Jacobi/Noether trace--Casimir energy decomposition;
  - strict right/left real-axis Xi logarithmic-derivative signs;
  - q-covariant orbit sign pattern `(+,+,-)`;
  - strict moving-fibre orientation energy.

**Boundary.** Strict fibre energy is a no-collapse theorem, not an RH selector. Source evolution or
domination of this nontrivial standard sector remains necessary. Prime--Gamma access is immediate
for two reflected exterior components; the middle point in `(1/2,1)` remains the source bottleneck.

## Log continuation

- 2026-08-22 — wide physics/mathematics corpus search rejected Casimir/QFI positivity as
  insufficient by itself; retained Noether/Jacobi quotient-current split.
- 2026-08-22 — C4 proved on paper and in Lean: actual q-fibre Xi signs are `(+,+,-)` and
  `E_q(s)>0` for every real `s>2`.

## C5 — cofinal one-sheet concentration and universal Casimir ratio

**Conjecture.** The moving three-sheet current has a universal far-sheet energy split, not merely a
pointwise positive fibre term.

**Hostile test.** Prove component limits from existing Xi asymptotics and quotient Jacobians. Reject
any statement depending on numerical fitting or on an assumed monotonicity of `E_q`.

**Result `[PROVED HERE]`.** As `s → +∞`, Lean proves

`D_q log xi(s) → +∞`,

`D_q log xi((s-1)/s) → 0`,

`D_q log xi(1/(1-s)) → 0`.

The proof combines the corpus theorem `xiRayLogDeriv → +∞`, continuity at the return points `1`
and `0`, the exterior law `q'(s)→1`, and exact covariances

`q'(w(s)) = q'(s)s²`,

`q'(w²(s)) = q'(s)(1-s)²`.

Consequently the exterior sheet asymptotically carries all raw component amplitude. Yet the
three-body Parseval law forces the standard-sector energy to retain twice the scalar energy:

`E_q(s) / (D_q log xi(s))² → 2`.

More invariantly, if `T_q(s)` is the real descended trace

`Re(D_q log(xi(s)xi(w(s))xi(w²(s))))`,

then

`E_q(s) / T_q(s)² → 2`.

This exact constant is the dimension-two standard representation showing up as a universal
invisible/visible energy ratio. It is unconditional and does not imply RH.

**Novelty audit `[NOVELTY UNVERIFIED]`.** Targeted current searches for Riemann Xi with anharmonic
orbit logarithmic derivatives, q-coordinate currents, orientation energy, Casimir, and standard
`S₃` sectors found the Rouyea--Bourgeois descent paper but no indexed statement of the moving
q-current sign law, strict standard-sector energy, cofinal one-sheet concentration, or ratio `2`.
Absence from search results is not proof of external novelty; publication label remains unverified.

**Formal additions.** `AnharmonicChebyshevNoetherCasimir.lean` now also proves:

- real quotient-Jacobian covariance and all three component limits;
- exact identification of real visible trace with logarithmic derivative of cyclic Xi product;
- real/complex orientation-energy agreement on the scan sheet;
- exterior-normalized and descended-trace-normalized Casimir limits, both equal to `2`.

## Log continuation II

- 2026-08-22 — C5 proved on paper and in Lean; no monotonicity assumption used.
- 2026-08-22 — targeted web novelty search found source descent paper, no exact collision; novelty
  remains unverified rather than claimed.

## C6 — global theta variance forces sharp Casimir separation

**Conjecture.** The asymptotic ratio `2` is the sharp lower wall of the complete real scan sheet:

`E_q(s) > 2 T_q(s)²` for every `s>2`.

**Numerical pre-certification.** High-precision probes gave `E_q/T_q² ≈ 59.8` at `s=2.1`,
`2.686` at `s=3`, and `2.003` at `s=10`. These supported the lower-wall conjecture but were not
used in its proof.

**Cross-corpus mechanism.** The missing comparison came from the theta-source/Laplace-transform
lane, not from further anharmonic algebra. The abstract `ThetaSource` already supplies
faster-than-every-exponential decay, and the literal theta-cusp source has global bilateral
Laplace transform `xiCent`. The earlier real-tilt variance API was artificially restricted to
`|a|<1`; the all-plane source interface removes that restriction.

For every source moment

`M_m(w) = ∫ x^m k(x)e^{wx} dx`,

dominated differentiation gives `M_m'(w)=M_{m+1}(w)` on all of `ℂ`. At every real tilt `a`,
the positive full-support tilted measure makes the order-two Hankel determinant strict:

`M_0(a)M_2(a)-M_1(a)² > 0`.

Thus its normalized mean `μ(a)=M_1(a)/M_0(a)` has derivative equal to a strictly positive
variance. The global source weld identifies

`μ(a) = xiRealLogDeriv(a)`,

so the centered Xi logarithmic derivative is strictly increasing on all of `ℝ`. This statement
is unconditional and concerns only the zero-free real axis.

For `s>2`, put

`u=(s-2)/(2s)`, `v=(s+1)/(2(s-1))`.

Then `0<u<v`. Strict Xi log-derivative monotonicity orders the return numerators, while exact
anharmonic covariance gives return denominators `q'(s)s²` and `q'(s)(s-1)²`. Since
`(s-1)²<s²`, the negative reflected return current strictly dominates the positive return current:

`0 < b(s) < -c(s)`.

Writing exterior current as `a(s)>0`, elementary three-body algebra gives

`E_q(s)-2T_q(s)² = -6(a b+b c+c a)`.

The inequality `b<-c` implies `ab+bc+ca<0`, hence the conjectured strict lower wall.

**Result `[PROVED HERE]`.** For every real `s>2`,

`2 T_q(s)² < E_q(s)`.

C5 proves `E_q(s)/T_q(s)² → 2`; therefore constant `2` is globally valid and asymptotically
sharp. This strengthens pointwise non-collapse and the cofinal law into a complete-sheet rigidity
theorem.

**Novelty audit `[NOVELTY UNVERIFIED]`.** The positive-kernel implication "log-Laplace curvature
= tilted variance" is standard and is not claimed as new. Sondow--Dumitrescu prove a different
horizontal-half-line monotonicity property of Xi modulus, and Dimitrov--Xu develop general
Wronskian positivity for Laplace transforms. Targeted searches found no indexed statement of the
anharmonic return-current domination or sharp global q-Casimir inequality. That absence is not a
novelty proof; only the synthesis is a candidate new result.

**Formal additions.** New module
`formal/GaloisForLFunctions/RHTower/ThetaSourceGlobalStrictLogConvexity.lean` proves:

- all-order, whole-plane theta-source Laplace moment differentiation;
- global strict Hankel determinants and tilted variance;
- `thetaTiltMean_eq_xiRealLogDeriv`;
- `strictMono_xiRealLogDeriv`.

`formal/GaloisForLFunctions/RHTower/AnharmonicChebyshevNoetherCasimir.lean` proves:

- strict reflected return-current domination;
- the signed three-body energy lemma;
- `two_mul_chebyshevXiQRealTrace_sq_lt_orientationEnergy`.

**RH audit.** C6 does not prove or falsify RH. Positive theta-source variance is unconditional and
blind to nonreal zero location; the resulting Casimir bound measures information loss under scalar
descent but does not constrain the discarded standard sector by an RH-equivalent prime--Gamma
quantity. The exact order-20/order-21 RH tail remains unchanged.

## Log continuation III

- 2026-08-22 — C6 proved on paper and in Lean by welding global theta-source variance to
  anharmonic Jacobian covariance.
- 2026-08-22 — targeted builds and direct Lean checks pass for both C6 modules. Representative
  axiom audits report only `propext`, `Classical.choice`, and `Quot.sound`; scoped proof-debt scan
  and `git diff --check` pass.
- 2026-08-22 — full umbrella build is externally blocked by duplicate
  `RHTower.deningerBigWittRingSeries` declarations in concurrent Deninger modules. Global formal
  lint is externally blocked by four unreachable concurrent `HTGeometry` modules
  (`FidelityPhaseRadius`, `FidelityReturnExponent`, `FidelityReturnTime`,
  `SortedEnsembleSpectrumScaling`). Neither failure names or traverses C6 source as defective.

## C7 — literature cubic-coordinate endpoint

**Literature-first correction.** Rouyea--Bourgeois,
[The Cubic Descent of the Riemann Xi Function](https://www.alphaxiv.org/abs/2608.riemann-xi-hankel-criterion),
Lemma 2.7, already proves the exact reality locus

`q(s) ∈ iℝ  ⇔  Re(s)=1/2 or |s|=1 or |1-s|=1`,

and uses `|Im(s)|>1` to remove the two circle branches. The cubic-coordinate RH reader is therefore
literature, not new research.

**Result `[FORMALIZED FROM LITERATURE]`.** New module
`formal/GaloisForLFunctions/RHTower/AnharmonicChebyshevCubicDescentCriterion.lean` proves:

- `q` commutes with conjugation and is nonzero on every actual Xi-zero copy;
- `q(ρ)²` is strictly negative real iff `Re(ρ)=1/2`;
- `allXiZeroChebyshevQSquaresStrictlyNegative_iff_riemannHypothesis`.

The reverse implication uses exact three-point fibre classification plus the independently
source-derived Xi height gap. It does not assume a zero enumeration or RH.

**Boundary.** This is an exact reader, not a producer. Proving that all descended zero nodes are
negative is RH itself. The companion Chebyshev-trace paper reduces production to its explicit
completed prime--archimedean bound; it states that this final bound remains open.

## C8 — exact future-sheet mass gap and boundary-positivity no-go

**Conjecture.** Reinterpret C6 as a Lorentz-type cone and ask whether strict separation admits an
exact positive mass decomposition rather than only an inequality.

For real `s>2`, write

`a = D_q log xi(s)`, `b = D_q log xi(w(s))`, `c = D_q log xi(w²(s))`,

and `d=-c-b`. The C6 proof gives `a>0`, `b>0`, `d>0`. Direct three-body algebra yields the stronger
identity

`E_q - 2T_q² = 6 (b² + d(a+b))`.                                      `(C8.1)`

Both right-hand channels are strictly positive. A second theta-monotonicity comparison gives the
full chamber

`0 < b < -c < a`,                                                        `(C8.2)`

so `T_q=a+b+c>0`. Thus `(T_q,E_q)` lies strictly on one future-oriented side of the cone
`E=2T²` at every finite exterior scan point, while

`(E_q-2T_q²)/T_q² → 0`.

**Result `[PROVED HERE]`.** `AnharmonicChebyshevNoetherCasimir.lean` now proves `(C8.1)`, `(C8.2)`,
strict positivity of the Lorentz mass gap, strict positivity of the descended trace, and normalized
approach to the null wall.

**Positive no-go survivor.** The invariant-coordinate logarithmic derivative of the cyclic Xi
product has positive real part on the entire exterior real ray, unconditionally. Therefore the
real-axis restriction of the cubic paper's positive-real/Herglotz programme cannot distinguish RH.
Any successful completion must control transverse complex directions, equivalently the full disk or
right-half-plane condition, not more real-ray monotonicity.

**Higher principle.** Symmetry quotient readers create aliases: the fixed locus and compact
same-fibre shells have identical scalar reality data. An independent radial/source gap can prune
the compact aliases, but cannot generate the remaining fixed-locus condition. This
`quotient + fibre classification + radial exclusion` principle explains both why the cubic reader is
exact and why it is not a proof.

**Novelty audit `[NOVELTY UNVERIFIED]`.** Targeted searches found the two 2026 cubic/Chebyshev
papers but no indexed statement of `(C8.1)`, `(C8.2)`, the future-sheet interpretation, or the
unconditional real-ray positive-log-derivative boundary. Search absence is not a novelty proof.

**RH audit.** C7 and C8 do not prove or falsify RH. C7 is an exact restatement on actual Xi zeros.
C8 proves the real boundary of a complex positive-real criterion automatically and therefore
sharpens the remaining obligation: establish transverse complex positivity or the equivalent
completed Chebyshev trace bound.

## Log continuation IV

- 2026-08-23 — corrected novelty attribution: cubic reality locus and negative-ray endpoint are
  Rouyea--Bourgeois literature; formalized the exact Xi-zero/RH equivalence in Lean.
- 2026-08-23 — C8 proved on paper and in Lean: exact positive two-channel mass gap, full strict
  current chamber, future trace positivity, and normalized null-wall approach.
- 2026-08-23 — direct Lean checks pass. Headline axiom audits report only `propext`,
  `Classical.choice`, and `Quot.sound`.
