# AdelicKreinGeometry (AKG)

Namespace `GaloisForLFunctions.AdelicKreinGeometry`; umbrella `AdelicKreinGeometry.lean`; 34 modules
(24 root, `Haar/` 10). All results unconditional; RH appears only inside equivalences.

## 1. Motivation

Positive harmonic analysis on the affine group `Aff(ℚ) = {x ↦ ax + b}` cannot carry Weil's correlation together
with a visible integer successor: a positive state with Weil's dilation part has a blind successor (APD). The
indefinite theory of the Weil kernel (HKT, AKL) lives on the multiplicative group alone. AKG studies Hermitian
functions of finite negative index (Pontryagin states) on the dilation–translation system, where both ring
operations act. Questions: which supports and decays allow a finite nonzero index; how a global index is computed
from local constituents glued at the pole; what replaces conformal Frobenius over `ℤ`; and whether Weil's dilation
data can sit on a finite-index state with the integer successor.

## 2. Objects

| Object | Lean | Meaning |
|---|---|---|
| Index, witnesses | `IsWitness` | `κ(φ) = sup` negative squares of Gram matrices; a finite family attaining it |
| Extensions | `blindWeilState`, `regularWeilState`, `slopeAbs`, `slopeUnit` | `ratCorr(|a|)`; zero off the dilations |
| Hecke support | `IsHeckeSupported` | `φ(ax + b) ≠ 0 ⇒ den(a)·b ∈ ℤ` |
| Height decay | `HasHeightDecay`, `slopeHeight`, `doubling` | decay in `|num a|·den a`; escape along `x ↦ 2^j x` |
| Polar index | `polarIndex`, `totalMass` | negative squares on mean-zero vectors (`κ₀ ≤ κ ≤ κ₀ + 1`) |
| Separable assembly | `separable`, `axisFamily`, `negLogHeight` | `K(g) = Σ_p k_p(g_p)` on `Π H_p` |
| Additive kernels | `absRat`, `negAbsRat`, `negAbsKernel`, `negPowKernel`, `negPowRat`, `negAbsInf`, `negUltra` | `±|b|`, `−|m|^s`, `−|·|_∞` on `K[X]`, `−|b|_v` ultrametric |
| Subordination | `subordination`, `subordinand` | `I_s(t) = ∫_0^∞ (1 − e^{−rt}) r^{−1−s} dr` |
| Fourier/Ramanujan data | `fourierCoeff`, `negCoeffs`, `levelKernel`, `ramanujanCoeff`, `IsUnitInvariant`, `IsConductorInvariant`, `IsIntPeriodic` | conductor coefficients of kernels on `ℤ/N` and `ℚ/ℤ` |
| Affine group of a field | `AffineGroupOf`, `slopeOf`, `shiftOf`, `translationOf`, `dilationOf` | `x ↦ ax + b` over any field `K` |
| Conformal data | `IsConformal`, `slopePow`, `conformalInduction`, `poleSuccessor`, `boostMass` | `ψ(ub) = |u|_v^s ψ(b)`; `|a|^{∓s/2}`; `|a|^{−s/2}ψ(b)`; boost pair + induction |
| Pole state | `poleState`, `kreinForm`, `krein2` | `a^{1/2} + a^{−1/2} − i b a^{−1/2}` from `SL(2,ℝ)` on signature `(1,1)` |
| Places | `IsUltra`, `ballSubgroup`, `inftyAbs`, `inftyNorm` | nonarchimedean balls; `|f|_∞ = b^{deg f}` on `F(X)` |
| Shells | `ballOf`, `shellSquares`, `tailSum` | balls of radius `r` at `p`; half-lines `(−∞, t)` at `∞`; squares of class sums |
| Prime lattice kernel | `primeLatticeKernel`, `countertermKernel` | `Λ(u)u^{−1/2}` on prime powers of `ℚ_{>0}`; `D·δ₁ − P` |
| Twists | `slopeChar` | unitary character of the slope |
| Product state | `adelicWeilState` | `ratCorr(|a|)·haarState` |
| Place assembly | `placeAssembly`, `boostChar` | `Σ_j` pole–successor states at places `v_j`; boost character `|u|_v^{s/2}` |
| Archimedean Weil state | `weilArchState` | `ratCorr(|a|) − c|a|^{−1/2}|b|`: blind extension plus conformal induction of `−c|b|` |
| Haar carriers | `haarOneNegativeSquare`, `affineLogTwo`, `mixedQuadraticKernel`, `haarMixedQuadraticState`, `mixedPowerKernel`, `mixedPowerPhase`, `haarMixedPowerState` | Haar ± log-slope or axis-invisible polynomial perturbations |
| Period defects | `translationPeriodDefect`, `translationPeriodSpace`, `affinePeriodSpace` | `col(b + 1) − col(b)` and its affine orbit |

External: `negIndex`, `IsHermKernel`, `IsPosDefKernel`, `gram`, `zetaKernel`, `kernelColumnSpan` (HKT);
`AffineGroupQ`, `affSlope`, `affShift`, `translation`, `dilation`, `heckeState`, `haarState`, `HasIntegerSuccessor`,
`ratCorr`, `splineCorr`, `extendFromSubgroup`, `IsPosDefOnGroup` (APD).

## 3. Language

- **Pontryagin state**: Hermitian function with `κ < ∞`; **type**: `κ ∈ {0, ∞}` or finite nonzero.
- **Escape**: a translate `t` with `φ(x_a⁻¹ t y_b) = 0` for given finite families; **approximate escape** / **mixing**: along a sequence.
- **Blind extension**: pullback along `|slope|`; **regular extension**: zero off a subgroup.
- **Gluing square**: the at most one square the shared constant (pole) direction adds to local polar indices.
- **Conformal successor** of exponent `s`: `ψ(ub) = |u|^s ψ(b)`; **boost pair**: `|u|^{s/2} + |u|^{−s/2}`.
- **Pole–successor state**: boost pair plus conformal induction of a successor; one per place.
- **Axis-invisible kernel**: zero on all translations and all dilations.
- **Agreement shell** of radius `r`: a class of points with `|x − y|_v ≤ r`.
- **Near coincidence**: rationals close to 1 have large denominators.

## 4. Mechanisms

**A. Index calculus on groups**
1. Pullback along surjections keeps `κ`; restriction never increases it; orthogonal translates carry copies of a
   whole negative subspace ⇒ induction formula `κ(ext₀ψ) = [G:H]·κ(ψ)`.
2. Witness complement is positive ⇒ escape forces finite `κ = 0`; block additivity + lower semicontinuity of the
   index ⇒ approximate escape and mixing force `κ ∈ {0, ∞}`.
3. Unitary twists are diagonal Gram congruences ⇒ `κ` is twin-blind.
4. Separable Gram = sum of local Grams; mean-zero blocks on different axes are orthogonal; complement of a maximal
   negative subspace is nonnegative ⇒ signature formula with one gluing square.

**B. Arithmetic escapes and incompatibilities**
5. Translation by `1/P` (prime above all denominators) escapes every Hecke-supported state; translation by `PQ`
   (two new primes) escapes the prime lattice kernel.
6. Height is submultiplicative; doubling dilations escape height-decaying states.
7. `den(q)·|q − 1| ≥ 1`: a state continuous at 1 minus one decaying with the denominator has infinite index;
   spreading over translates `x + j/P` removes Hecke-supported parts (dilution).
8. Averaging over many Haar-orthogonal translates makes any positive integer-successor carrier invisible to the
   index; its dilations obey `|p(D_u)|² ≤ |u − 1|`.

**C. Additive side**
9. Fourier expansion on `ℤ/N`: Gram form `= Σ_ξ a_ξ|Σ c e(yξ/N)|²`; dual characters span negative subspaces.
   Unit invariance makes coefficients constant on conductor classes of size `φ(d)`.
10. Conditional positivity of `−|·|`: min-kernel sum of squares on `ℤ`; integral rescaling to `ℚ`; Poisson
    subordination for `|m|^s`; equivalence kernels (ultrametric layers / balls + layer cake) for `−|·|_v`.

**D. Conformal and pole structure**
11. Endomorphisms fix the identity ⇒ positive states admit no conformal factor `≠ 1`.
12. Point vectors `k_t, k_∞` on `ℙ¹(K)`: dilations act as boosts with eigenvalues `|a|^{∓s/2}`; Gram form of the
    pole–successor state `= 2Re(X̄Y) + ψ`-form with total mass `X`.
13. Borel of `SL(2,ℝ)` preserves a signature `(1,1)` form: Gram `= Wᴴ h W` ⇒ one negative square.
14. Product formula `∏_v |a|_v = 1`: local boosts multiply to 1 on `ℚ^×`; on dilations each boost pair is the
    pair kernel of its boost character, so a unit separating the characters gives one square per place.
14a. Equivalence kernels are sums of squares of class sums; with the layer cake the local pole–successor form is
    a renormalized hyperbolic pair plus shell squares: `2Re(X̄Y) − cR|X|²` at `p` (balls), `2Re(X̄Y_R)` with
    `Y_R = Y − cΣ w_g|a_g|^{−1/2}(R − b_g)` at `∞` (half-lines `(−∞, t)`).

**E. Axis-invisible kernels**
15. Zero set of an index-≤1 kernel is a subgroup; axes generate `Aff(ℚ)`. Translation columns span `≤ κ`
    dimensions with unipotent action ⇒ polynomial fibres of degree `< κ`, Gram rank `≤ κ²`; hyperbolic features
    give `κ ≤ d + 1` for `γ(1 − a^{−d})b^d`; dilation rescaling keeps `κ` under positive additions.

## 5. Pillar theorems

| Theorem | Lean | Status |
|---|---|---|
| Induction formula; blind extension index-minimal; infinite-index regular extension | `negIndex_extendFromSubgroup`, `negIndex_comp_retraction`, `negIndex_extendFromSubgroup_eq_top` | proved |
| Escape / mixing / height decay ⇒ `κ ∈ {0, ∞}` | `negIndex_eq_zero_or_top_of_escape`, `negIndex_eq_zero_or_top_of_mixing`, `negIndex_eq_zero_or_top_of_heightDecay` | proved |
| Hecke support ⇒ `κ ∈ {0, ∞}`; Kakutani wall is an index wall (`0` for `s ≥ ½`, `∞` below) | `negIndex_eq_zero_or_top_of_isHeckeSupported`, `negIndex_heckeState` | proved |
| Weil's correlation: every affine extension has `κ ≥ κ(K_ζ)`; regular extension `0`/`∞` by RH; Hecke-supported + Haar successor ⇒ `κ = ∞` | `negIndex_blindWeilState`, `negIndex_regularWeilState`, `negIndex_eq_top_of_weil_haarSuccessor` | proved |
| Separable signature formula `Σκ₀ ≤ κ ≤ Σκ₀ + 1`; `−Σ a_p|m_p|` has `κ = 1` | `polarIndex_sum_le_negIndex_separable`, `negIndex_separable_le_polarIndex_sum_add_one`, `negIndex_negLogHeight` | proved |
| No fixed counterterm makes the prime kernel Pontryagin: `κ(D·δ₁ − P) = ∞` | `negIndex_counterterm_sub_primeLatticeKernel` | proved |
| Continuous dilation part + Hecke-supported/positive integer-successor carrier ⇒ `κ = ∞` (incl. Weil) | `negIndex_slope_add_eq_top`, `negIndex_add_slope_of_integer_successor`, `negIndex_add_slope_eq_top_of_weil_dilation` | proved |
| Additive index law `κ = #{a_ξ < 0}`; on `ℚ/ℤ` sup over levels; Ramanujan law `κ = Σ_{A_d<0} φ(d)` | `negIndex_zmod_eq_card`, `negIndex_eq_iSup_card_negCoeffs`, `negIndex_zmod_eq_sum_totient`, `negIndex_eq_iSup_sum_totient` | proved |
| Positive states have no conformal symmetry; `κ(c|b|) = 0, 1, ∞`; `κ(−|m|^s) = 1`; `κ(−|·|_∞) = 1` | `eq_zero_of_conformal_of_isPosDefKernel`, `negIndex_mul_absRat`, `negIndex_negPow`, `negIndex_negAbsInf` | proved |
| Index is twin-blind | `negIndex_mul_unitaryChar`, `negIndex_heckeState_mul_slopeChar` | proved |
| Pole state of `Aff(ℚ)` has `κ = 1`; conformal induction keeps `κ` | `negIndex_poleState`, `negIndex_conformalInduction` | proved |
| Pole–successor signature formula `κ = κ₀(ψ) + 1`; index one at the real place, every `p`, and `∞` of `F(X)` | `negIndex_poleSuccessor_eq`, `negIndex_poleSuccessorState`, `negIndex_padicPoleSuccessor`, `negIndex_inftyPoleSuccessor` | proved |
| Local signatures add over distinct places: a place assembly has `κ = k` (separating unit); `∞` and `p` give `κ = 2` | `negIndex_placeAssembly_eq`, `negIndex_real_add_padic` | proved |
| Shell decomposition: local pole–successor form `= 2Re(X̄Y) − cR|X|² + c∫_0^R Σ_B |shell sum|²` at `p`, `= 2Re(X̄Y_R) + 2c∫_L^R |T_t|²` at `∞` | `hermQuad_gram_poleSuccessor_negUltra_eq`, `hermQuad_gram_poleSuccessorState_eq`, `hermQuad_gram_negUltra_eq`, `hermQuad_gram_negAbsRat_eq` | proved |
| Haar carriers: one square off Hecke support (dilation discontinuous); every `κ ≥ 2` with both Haar axis readings; not positive + slope | `negIndex_haarOneNegativeSquare`, `negIndex_haarMixedPowerState`, `haarMixedQuadraticState_not_positive_add_slope` | proved |
| Axis-invisible kernels: zero or `κ ≥ 2`; rank `≤ κ²`; fibres polynomial of degree `< κ` | `two_le_negIndex_of_zero_axes`, `rank_gram_le_square_of_zero_axes`, `exists_polynomial_translation_fibre_lt_index` | proved |
| Integer successor of index `r`: affine period-defect space has dim `≤ r²` | `finite_affinePeriodSpace_of_integerSuccessor` | proved |
| Weil's dilation data with the archimedean successor: `max(1, κ(K_ζ)) ≤ κ ≤ κ(K_ζ) + 1`; finite iff `κ(K_ζ)` is | `negIndex_weilArchState_le`, `le_negIndex_weilArchState`, `one_le_negIndex_weilArchState`, `negIndex_weilArchState_lt_top_iff` | proved |
| Finite-index state with Weil's dilation data and integer successor (indefinite Mautner) | — | open |

## 6. Tools

**Developed**
- Pontryagin index theory on groups: induction, witness complements, exact/approximate escape, block additivity,
  twist invariance, Krein compressions `Wᴴ h W`, conformal induction.
- Local–global signature calculus: polar index, separable formula (shared pole), pole–successor formula `κ₀ + 1`,
  additivity over places with distinct poles.
- Indefinite Howe–Moore: mixing, height decay, near coincidence, dilution, Haar averaging.
- Exact additive index laws on `ℤ/N`, `ℚ/ℤ` and for Ramanujan (unit-invariant) kernels.
- Conditional positivity toolkit: min kernels, Poisson subordination, ultrametric layer cake, shell sums of squares.
- Axis-invisible kernel theory: degree, rank and exact-index laws; period-defect bounds.

**To build**
- Krein–Langer structure on `Aff(ℚ)` beyond finite rank modulo slope data.
- Non-separable gluing with the archimedean operator in place of a scalar counterterm.
- Hecke states and the index wall over `F_q(T)`.
- Additive carrier of the collision charge; shell sum-of-squares for the complete Weil form (solved for the local
  pole–successor forms).

## 7. Open questions

1. Indefinite Mautner: is there a finite-index state with integer successor and a dilation reading continuous at 1,
   whose negative part is not finite rank modulo slope data?
2. Is every Pontryagin state on `Aff(ℚ)` a positive state plus a coefficient of a finite-dimensional or conformally
   induced Pontryagin representation?
3. Signature formula for the Weil kernel itself, which is neither tower-supported nor separable: what replaces the
   scalar gluing square when the glue is the archimedean operator?
4. Glue the prime and archimedean parts of Weil's kernel to successors place by place, as the pole pair is glued to
   `−|b|`, and compute the index.
5. Which additive invariant (count of negative conductor modes) could equal the number of off-line zeros?
6. Exact sum-of-squares decomposition of the complete Weil form indexed by successor-agreement shells (the local
   pole–successor forms have one, with the running counterterm `cR` on the pole coordinate).

## 8. Traps

| Trap | Fact |
|---|---|
| Successor coordinates are free | Only at index zero; the regular extension costs `[G:H]` copies of every square |
| Indefiniteness escapes APD's positive no-gos | A Hecke-supported Pontryagin state is positive |
| The integer successor forbids finite nonzero index | `haarOneNegativeSquare` has index one, outside Hecke support |
| A slope correction can give the Haar state a continuous dilation reading | Then the index is infinite |
| The Kakutani wall is gradual | It is a jump `0 → ∞` |
| Decaying states can carry a few squares | Mixing and height decay kill them |
| Local polar indices add exactly | Up to one gluing square, carried by the pole |
| The successor can absorb the pole's square | Never: `κ = κ₀(ψ) + 1` |
| Conformal Frobenius has a positive analogue | Positive states admit no conformal symmetry |
| Conformal symmetry separates `ℤ` from `F_q` | The index-one conformal successor exists on both |
| Index laws select `ζ` | They are twin-blind |
| Matched local Hodge indices assemble on `ℚ_{>0}` | Every fixed counterterm leaves infinitely many squares |
| The adelic product of the two readings is a new carrier | It is Hecke-supported: `0` or `∞` |
| Finite index = positive + slope data | The Haar mixed quadratic state is not |
| Only the archimedean place carries a square | Every `p`-adic place carries an index-one pole–successor state |
| Poles at different places glue like a shared pole | They add: `κ(Φ_∞ + Φ_p) = 2` |
| Weil's dilation data forbids a nonconstant successor at finite index | Only the integer one: with `−c|b|` the index is `κ(K_ζ) + ε`, `ε ∈ {0, 1}` |

## 9. Context

**Uses** (import counts): HeckeKreinToeplitz 17, ArithmeticPositiveDuality 7, HTGeometry 3, BiarithmeticGeometry 2,
RHTower 1, RenormalizedArithmeticPotentialTheory 1, ArithmeticLorentzianGeometry 1, ArithmeticKreinLangerTheory 1.

**Used by**: none (umbrella only).

| Neighbour | Relation |
|---|---|
| ArithmeticPositiveDuality | Positive states on `Aff(ℚ)`, Hecke/Haar states, Kakutani wall, Mautner rigidity; AKG asks what finite index changes |
| HeckeKreinToeplitz | Index, Gram calculus, column spaces, `K_ζ`; AKG adds induction, escape, mixing and Weil's affine extensions |
| ArithmeticKreinLangerTheory | Axis zero-or-infinity and twin-blind locality; AKG gives the non-commutative escape law and separable signature |
| RenormalizedArithmeticPotentialTheory | Matched local Hodge index with running counterterm; AKG proves no fixed counterterm works |
| ArithmeticLorentzianGeometry | Hecke is a boost, Frobenius conformal; AKG shows boost and conformal successor are one state |
| BiarithmeticGeometry | Affine translation unipotence and polynomial coefficients for period defects and fibres |
| HilbertianExplicitFormulas, ArithmeticPolarization | Explicit formulas read only Weil's form; AKG tests the additive side as an index carrier |

## 10. Big picture

AKG turns the question "what positive object could carry both arithmetic operations" into an index question, and
the answer is sharply constrained. Every natural arithmetic state, whether supported on integers, decaying in
height, mixing, or a product of the two readings, has either no negative squares or infinitely many. A finite
nonzero index needs a carrier that never escapes, and over `ℚ` that carrier is the pole: the hyperbolic pair at
`0, ∞` of the projective line, which appears at every place as a boost on the multiplicative side glued to a
conformal successor on the additive side, at the price of exactly one square. Index calculus is also twin-blind,
so it cannot by itself select `ζ`.

For the RH effort this locates the missing object precisely. Weil's correlation can be extended to the affine
group without extra cost only by making the successor blind; attaching the integer successor while keeping Weil's
continuous dilation data costs infinitely many squares for every carrier built from positive pieces and slope
corrections. The finite-dimensional local pictures (each place, each finite sieve) all work with one gluing square,
but the global assembly fails at any fixed renormalization. What is needed is a genuinely non-separable,
non-escaping carrier that couples slope and shift in infinite rank, and none of the structures built from local
data supplies it.
