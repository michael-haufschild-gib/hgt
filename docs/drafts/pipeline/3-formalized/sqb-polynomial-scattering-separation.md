# Polynomial transport of modular scattering energies: reality and separation

- **ID:** SQB-POLYNOMIAL-SCATTERING-SEPARATION
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean); source, build, axiom, index, and lint audits passed
- **Scope:** Fixed complex polynomials of the native modular-scattering Casimir. This is not a proof or falsification of RH or the Selberg quarter conjecture.

## Statements

Define

\[
 s(z)=\tfrac14+\tfrac{i z}{2},\qquad
 k(z)=s(z)(1-s(z))=\tfrac3{16}+\tfrac{z^2}{4}+\tfrac{i z}{4}.
\]

For a complex polynomial P:

1. P(k(t)) is real at infinitely many real parameters t **if and only if** P is a real constant. In particular, every nonconstant P has only finitely many real-valued parameters.
2. If P is nonconstant, |Im P(k(t))| tends to infinity as t tends to positive infinity. Thus, for every real M, there is B such that t≥B implies |P(k(t))−r|>M for every real r.
3. For every nonconstant P and every pair of real bounds H,M, there is t>H with ζ(1/2+it)=0 such that t is a genuine pole of the corpus's normalized modular scattering coefficient and |P(k(t))−r|>M for every real r.
4. P(k(z)) is real at every multiplicity-marked Xi spectral point z **if and only if** P is a real constant. Requiring reality merely at all critical-line zeta zeros already gives the same classification.

All assertions are unconditional. A polynomial can have arbitrary complex coefficients and arbitrary finite degree; it is held fixed as height grows. No estimate is claimed uniformly over a changing polynomial family.

## Proof

Put Q=P∘k, considered as a complex polynomial. Coefficientwise conjugation Q* obeys Q*(t)=conj(Q(t)) on real t. If Q is real at infinitely many such t, Q*=Q by polynomial identity.

The literal quadratic obeys k(−z−i)=k(z), so Q(−z−i)=Q(z). Since Q*=Q, conjugating this identity supplies Q(−z+i)=Q(z). Composing the two reflections gives Q(z+2i)=Q(z).

The corpus's polynomial period theorem forces every nonconstant complex polynomial to have only zero additive period. Its proof chooses one complex root and transports it along the purported nonzero period; the distinct translated roots form an infinite set, forcing the polynomial to vanish identically. Consequently Q is constant. Since deg k=2 and natural degree multiplies under polynomial composition, P is constant. One real-valued sample forces its constant coefficient real. Real constants give the converse.

To strengthen finite exceptional reality to divergent separation, take R=Im(Q) coefficientwise, a real polynomial with R(t)=Im(P(k(t))). If R were constant b, then P−ib would be real on the full parabola. The classification would make P−ib, hence P, constant. For nonconstant P, R therefore has positive degree. The checked real-polynomial growth theorem gives |R(t)|→∞. The elementary inequality |Im w|≤|w−r| for real r gives the uniform separation from the entire real axis.

The corpus's unconditional Hardy theorem supplies a critical-line zeta zero in every sufficiently high dyadic window. Choose the window above H and the separation threshold B. The original Xi zero equivalence supplies a multiplicity-marked Xi copy with centered spectral point t. Its checked normalized scattering coefficient

\[
 S(z)=\frac{\Xi_C(z+i)}{\Xi_C(z)}
\]

has strictly negative meromorphic order there: the denominator vanishes, while the shifted numerator is nonzero. The same t therefore satisfies the actual pole and uniform separation assertions simultaneously. Reality at all Xi copies implies reality at these infinitely many critical-line zeros, forcing the polynomial to be a real constant. This proof uses neither RH nor a hypothetical off-line zero.

## Consequence for a spectral proof

The native scattering parameter at a zeta zero ρ is s=ρ/2. Even known critical-line zeros do not supply real native Casimirs. A fixed nonconstant polynomial change of that scalar energy cannot place all these occurrences in a real Maass spectrum. Allowing any fixed approximation error does not repair this class: the distance from every real value is unbounded on genuine critical-line poles.

This does not rule out a different source construction, a nonpolynomial transform, a family whose degree changes with height, or an independently proved operator-domain comparison. None is supplied here. SQB still needs its source quarter inequality and an independent Xi occurrence mechanism in the appropriate spectral domain.

## Corpus provenance

Broad OR searches used the entire indexed corpus, without a module restriction: spectral transformations, automorphic/Hecke/representation mechanisms, geometric curvature/capacity mechanisms, and polynomial/reflection mechanisms. Their respective metadata coverage was 3543 declarations in 1156 modules; 1412 in 320; 13010 in 1783; and 20536 in 5472. These counts are discovery coverage, not claims to have read every proof.

Inspected mechanisms used in the proof:

- `RHTower.polynomial_eval_periodic_eq_zero` in `CoshPolynomialPeriodClassification`: infinite translated-root proof of polynomial period rigidity.
- `HTGeometry.SymmetricPolynomialJets`: coefficientwise Schwarz conjugation and reflected polynomial identities; the implementation uses the narrow underlying mathlib evaluation identity.
- `GaloisForLFunctions.HTGeometry.ExpZeroBound.imPoly` and `eval_imPoly` in `ExponentialPolynomialZeroBound`: actual imaginary polynomial of a complex polynomial.
- Mathlib `Polynomial.abs_tendsto_atTop`: real-polynomial growth from positive degree.
- `RHTower.exists_riemannZeta_line_zero_dyadic` in `HardyDyadicWindowTheorem`: actual unconditional critical-line zeros in arbitrarily high dyadic windows.
- `RHTower.XiC_eq_zero_iff_exists_xiZeroCopy` in `XiCanonicalProduct`: multiplicity-marked source occurrence.
- `RHTower.thetaCuspHawkingOpticalCusp_xiSpectralPoint_isPole` in `ThetaCuspHawkingOpticalCuspScatteringIncidence`: genuine meromorphic pole incidence.

The broader finite-graph gap and explicit complementary-series sources were inspected as alternative mechanisms. Their respective spectral-gap and global automorphic-lift inputs are not supplied by this argument. No novelty claim is made.

## Verification

All complete scratch proofs and all three direct source checks passed. Each module is wired exactly once into `RHTower.lean`; no full or umbrella build ran.

- `SelbergScatteringPolynomialReality`: final targeted build passed, rebuilding only this target (4.3s).
- `SelbergScatteringPolynomialSeparation`: final targeted build passed, rebuilding only this target (63s).
- `SelbergScatteringPolynomialXiObstruction`: final targeted build passed; the target itself took 32s. Lake first rebuilt six stale required dependencies: `SmoothAFECutoffSum`, `SmoothAFEZetaDualSeriesFreezing`, `HardyFourthMomentSignChange`, `HardyZSmoothAFEReal`, `HardyZDyadicMean`, and `HardyDyadicWindowTheorem`. The first dependency jobs ran in parallel, contrary to the requested single-process discipline; this was reported during the task. Subsequent checks were serialized. `HardyFourthMomentSignChange:171` emitted an existing `push_neg` deprecation. Other dependency output was replayed informational tactic advice. No new module emitted warnings.

A separate `/tmp/sqb_axioms.lean` audit imported the final built endpoint and checked every one of the 19 exported declarations. All depend only on `propext`, `Classical.choice`, and `Quot.sound`. Its output also verifies the two source-capstone types: neither assumes RH, Selberg, source admission, or a conjectural estimate. The only nonconstancy condition in the separation theorem is its stated polynomial class. Log: `/tmp/sqb_axioms.log`.

The refreshed search index contains exactly all 19 declarations (`/tmp/sqb_index_audit.json`, compared with `/tmp/sqb_export_inventory.json`). Repository formal lint passed with existing large-file warnings (`/tmp/sqb_lint.log`). Forbidden-declaration and numerical-proof scans were empty for all three modules. Source whitespace and umbrella import-count checks passed.

No numerical experiments, added axioms, commits, or pushes were used. This task made no edits to `rh-current-frontier-map.md`; concurrent tasks changed that file independently. Future final builds must preflight and serialize stale required dependencies rather than relying on Lake's default scheduling.
