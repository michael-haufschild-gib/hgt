# Cohomology of Windows of Spec ℤ (CWS)

Namespace `GaloisForLFunctions.CohomologyOfWindowsOfSpecZ`; umbrella `CohomologyOfWindowsOfSpecZ.lean`;
13 modules. Every theorem is unconditional. Theorems named `riemannHypothesis_iff_*` are proved
equivalences, not proofs of RH.

## 1. Motivation

The corpus has built every layer of an arithmetic Hodge theory of the scaling surface except the one
that produces positivity. The degeneration of the complete Weil family (ADT, AHD) is a complete
dictionary: its first-order structure is a point count, `J(m) = J(1)·#ℙ⁷(ℤ/m)`; its second-order
structure on a horizon window is Weil's form `Q(H)` of the synthesized window test plus a prime-free
positive term. RH is the sign of that one form on windows of every length. A theory of degenerations
says where the sign lives; it does not supply it.

Over `𝔽_q` the sign is never an estimate. Weil reads it from intersection numbers that are counts,
Stepanov from auxiliary sections whose vanishing is counted, Deligne from tensor powers with Euler
products. In each proof a cohomology group is finite, `h¹ ≥ 0` because it is a dimension, and an
identity converts that free inequality into the bound.

CWS attaches to each **window** of `Spec ℤ` — a scale cutoff `e^A`, i.e. the interval `[−A, 0]` of the
scaling line with the prime powers `n ≤ e^A` that act on it — the arithmetic object whose `h¹` is
Weil's window form, determines that object exactly, and decides which structures can make its `h¹`
nonnegative for a structural reason. It answers: what the window object is and what it cannot be;
how the creation potential is paid; what the prime jumps do to a window; how the window integer,
genus and Frobenius at infinity behave; what a count on window correspondences must be; how the
calibration over `𝔽_q` differs; why windows of bounded length cannot select `ζ`.

## 2. Objects

| Object | Lean | Meaning |
|---|---|---|
| Window test | `IsWindowTest A H`, `windowTests A` | real `C²` function supported in `[−A, 0]` |
| Level, canonical degree | `windowLevel`, `canonicalDegree` | `⌊e^A⌋`; `deg K_A = 2ψ_{1/2}(e^A) − Ω(0)` |
| Window Markov form | RHTower `markovForm`, `levyJump`, `primeJump`, `creationPotential` | `V‖H‖² + J_∞(H) + Σ_{n} (Λ(n)/√n)‖H − H(·+log n)‖²` |
| In-window count, fold energy | `inWindowCount`, `foldEnergy` | `m_ℓ = 1_{[−A,−ℓ]} + 1_{[ℓ−A,0]}`; `∫_{[−A,−ℓ]}(H − H(·+ℓ))²` |
| Symmetric fold mass | `foldSym` | `½∫_{[−A,−ℓ]}(H + H(·+ℓ))²` |
| Canonical density, mass | `canonicalDensity`, `canonicalMass` | `k_A = Σ_{n≤e^A}(Λ(n)/√n) m_{log n}`; its integral |
| Half-weighted Chebyshev function | `halfChebyshev` | `ψ_{1/2}(x) = Σ_{n≤x} Λ(n)/√n` |
| Window floor | `windowFloor` | `deg K_A + 2A sinh²(A/2)` |
| Window involution, transform, multiplier | `windowInvolution`, `windowTransform`, `windowMultiplier` | `H(−A − u)`; `Ĥ(s) = ∫H(u)e^{(s−½)u}`; `e^{−(s−½)A}` |
| Window cycle | `windowCycle` | the scaling cycle `(0, 0, H)` of a window test |
| Realization | `IsWindowRealization`, `windowZeroMap` | real linear `r` with `Q = ‖r·‖²`; `H ↦ (√m_ρ Ĥ(γ_ρ))_ρ` |
| Window index | `windowIndex` | negative squares of `Q` on a window of length `A` |
| Fold-free test | `IsFoldFree` | vanishes off the middle `(−log 2, log 2 − A)` |
| Window genus, Shannon surplus | `windowGenus`, `shannonSurplus`, `zeroCountMain` | near-radical dimension; `(2L)(2T)/2π − 2N₀(T)` |
| Window correspondences, Rosati form | `windowCorr`, `corrTest`, `windowRosati` | integral shifts in `[a−A, 0]`; `Q(Σ ξ(s)x(·−s))` |
| Curve window map | `curveWindowMap` | `e ↦ (Σ_{k<n} e_kβ_i^k)_i ∈ ℂ^{2g}` |

## 3. Language

- **Window of length `A`**; **level** `⌊e^A⌋`; **active** prime power `n ≤ e^A`; **departing** jump: longer
  than the window, or the part of an active jump that exits.
- **Stage** `n`: `log n ≤ A < log(n+1)`; a new prime power enters at each `A = log n`. Prime-free stage
  `A < log 2`; first-prime stage `log 2 ≤ A < log 3`.
- **Fold** of `T_n`: the translation of the left end `[−A, −log n]` onto the right end `[log n − A, 0]`.
  **Antisymmetric count** `½(fold energy)`, **symmetric mass** `foldSym`.
- **Canonical class** of a window: the measure `k_A` left by the creation potential after the exits.
- **Window `h¹`**: `½Q_A`, the primitive `h¹` of LST's Künneth Riemann–Roch on window tests.
- **Carrier**: a structure making `h¹ ≥ 0` — a count, a capacity, a placement. **Soft**: holds for every
  weight or datum of a family; **selective**: fails on a fake.

## 4. Mechanisms

**A. The window datum.**
1. *Locality.* `Q = M_{⌊e^A⌋} + ½⟨c,H⟩² − ½⟨s,H⟩²` on window tests; departing jumps pay their own creation;
   weights agreeing on `n ≤ e^A` give the same functional.
2. *Serre duality.* Reflection and the window involution are isometries; windows of equal length are
   isometric.

**B. The canonical class and the folds.**
3. *Fold identity.* For `H` vanishing off the window,
   `∫(H − H(·+ℓ))² − 2∫H² = fold energy − ∫ m_ℓ H²`: the creation of a jump is paid pointwise by its exits;
   the remainder is the in-window count. Hence
   `Q = Ω(0)‖H‖² + J_∞(H) + Σ (Λ(n)/√n)·fold_n − ∫ k_A H² + pole`.
4. *Shape and degree.* `k_A(u) = ψ_{1/2}(e^{−u}) + ψ_{1/2}(e^{A+u})`: a jump stays inside on one side exactly
   when it is shorter than the distance to that end. The canonical class concentrates at the ends
   (`ψ_{1/2}(e^A)`) and is smallest at the centre (`2ψ_{1/2}(e^{A/2})`); its mass is the Riesz mean
   `2∫_0^A ψ_{1/2}(e^t)dt`.
5. *Signed folds.* Each fold contributes `(Λ(n)/√n)(anti_n − sym_n)`. The symmetric fold masses are the only
   negative arithmetic terms of a window; the arithmetic moves `Q` by at most `∫ k_A H²`.
6. *Stages.* Prime-free windows are purely archimedean; the first-prime window has one fold, the graph of
   `T₂`, with disjoint ends; half-folded tests see no prime; fold-symmetric tests pay the full end mass and
   fold-antisymmetric tests gain it.
7. *The archimedean obstruction.* For `log 2 ≤ A < 2 log 2` the middle `(−log 2, log 2 − A)` carries no
   fold end and no canonical density; on fold-free, pole-free tests `Q − J_∞ = Ω(0)‖H‖² < 0`, on an
   infinite-dimensional space. No identity "jump count + fold data + finitely many squares" exists: the
   obstruction at the first prime is archimedean.
8. *One negative square on short windows.* Below `log 2 + 1/50` the form is coercive on the cosh
   hyperplane of smooth tests (LST), so no plane of window tests is negative definite: positivity there is
   the cosh capacity of one even direction.
9. *Semiboundedness.* `Q ≥ −(deg K_A + 2A sinh²(A/2))‖H‖²`: archimedean jumps and fold energies are
   nonnegative, the canonical density is at most `2ψ_{1/2}(e^A)`, the pole costs at most the sinh capacity.

**C. Carriers.**
10. *Realization.* A realization `Q = ‖r·‖²` forces the sign; under RH the zero map realizes every window.
   Short windows are coercive, so every realization has infinite-dimensional target.
11. *Count (Tate).* On window correspondences, a naive height for `q_x` exists iff `q_x ≥ 0`, and every naive
   height recovers `q_x` by `h(mξ)/m² → q_x(ξ)`.
12. *Capacity and the second order.* The prime-free second-order term `c∫e^{−py}H²` dominates `‖H‖²` on
    windows; with semiboundedness, `κQ + c∫e^{−py}H² ≥ 0` once `c ≥ κ·windowFloor`.
13. *Placement.* The window involution acts on transforms by `s ↦ 1 − s` with multiplier `e^{−(s−½)A}`,
    unitary exactly on `Re s = ½`; pair products `Ĥ(s)Ĥ(1−s)` are invariant.

**D. Calibration and selection.**
14. *Curves.* For unitary data the window form is `‖(Σ e_kβ_i^k)_i‖²` in `ℂ^{2g}`; realizations at every
    window ⇔ unitarity; positive definite on window `n` ⇔ `n ≤ #{distinct β}`; the golden fake has none.
15. *Selection.* Windows below `log p` cannot see the Euler factor at `p`; every bounded window length has a
    flip twin with the same window functional and no Weil positivity.

## 5. Questions the programme answers

| Question | Answer |
|---|---|
| What object has Weil's window form as its `h¹`? | The window datum: archimedean jumps, folds of the active prime powers, the canonical class and the pole plane (`weilQuad_eq_fold_sub_canonical`, `weilQuad_eq_signedFolds`). Its `h¹` is the primitive Künneth `h¹` of the window cycle: `h_K(x) + h_K(−x) = χ(x) + h¹_K(x) + ½Q(H)` with `h¹_K > 0` a product of counts (`primitiveH1_windowCycle`, `kunneth_windowCycle`). A realization `Q = ‖r·‖²` exists at every length iff RH, the zero map being one (`riemannHypothesis_iff_forall_windowRealization`); no realization is finite-dimensional on any window of positive length (`not_isWindowRealization_of_finiteDimensional`). Over `𝔽_q` it is the Frobenius orbit in `H¹`, dimension `2g` (`toeplitz_eq_norm_sq_curveWindowMap`). |
| What set does `τ_x(ξ⋆ξ′)` count, up to bounded error? | Any count at bounded distance from the window Rosati form exists iff `q_x ≥ 0` on window correspondences (`exists_window_naiveHeight_iff`) and recovers `q_x` by Tate's limit (`tendsto_naiveHeight_nsmul_div`); it exists on windows `≤ 3/5` (`exists_window_naiveHeight_of_le`); at all lengths it is RH (`riemannHypothesis_iff_forall_window_naiveHeight`). |
| Is `β` the dimension of `ℙ^β`; what is the second order? | First order: `J_{β+1}(m) = φ(m)#ℙ^β(ℤ/m)` for every `β` (AHD `natCard_projPoints_mul_totient`). Second order on a window: the prime-free term (`β` times the count) pays the whole window at bounded dilation constant (`pencil_nonneg`); the zero-carrying term is Weil's window form, and windows of bounded length do not determine whether it is positive (`exists_flip_twin_of_window`). |
| What pays the creation potential; what is the degree of the window's canonical class? | Exits pay the departing and exiting creation exactly (`jump_sub_creation_eq_fold`); the remainder is `k_A(u) = ψ_{1/2}(e^{−u}) + ψ_{1/2}(e^{A+u})` (`canonicalDensity_eq_halfChebyshev`) of degree `2∫_0^A ψ_{1/2}(e^t)dt` (`canonicalMass_eq_integral_halfChebyshev`); it bounds the arithmetic (`abs_weilQuad_sub_arch_le`) and the form from below (`weilQuad_ge_neg_windowFloor`). |
| What are Stepanov's auxiliary sections on a window? | Over `𝔽_q` Stepanov's count pays `h¹` (LST, hyperelliptic curves of every genus); for curves the sections of a window are the multiples of the reduced characteristic polynomial, appearing exactly beyond `#{distinct β}` (`curveWindow_posDef_iff`). Over `ℤ` the conditions that make a window coercive are finitely many — the window index is at most the Shannon count `⌊1 + 2A·T(A/2)/π⌋` (`windowIndex_le_shannon`), zero for `A ≤ 3/5`. |
| What lattice carries the sections of a window, with what metric? | The window genus is at least `(2 − η)e^A` (`exists_windowGenus_ge`); `2e^{2L}` is the Young conjugate of the zero density, attained at the Landau height `2πe^{2L}` (`isGreatest_shannonSurplus`, `shannonSurplus_eq_iff`), and `e^A = exp h⁰_ℤ(A)(1 + o(1))` (`tendsto_exp_arithH0_div_exp`): the integer lattice of degree `A` with the Gaussian theta metric of `Spec ℤ`. |
| Why `ζ` and not a fake: which axiom fails? | Bounded windows never select (`exists_flip_twin_of_window`); the golden curve has every count axiom and no window cohomology (`goldenDatum_not_forall_curveWindowRealization`); Epstein data are definite counts with real zeros in `(½,1)` (LST). Selection needs the `h¹` at every length. |
| Is Weil's window form a count at the first prime (an identity jump count + `T₂` count + squares)? | No: for `log 2 ≤ A < 2 log 2` no identity `Q = J_∞ + Φ(fold data) + Σ_{i<k} ℓ_i²` exists (`not_exists_countIdentity`); on fold-free, pole-free tests `Q − J_∞ = Ω(0)‖H‖² < 0` on an infinite-dimensional space (`exists_foldFree_poleFree`, `weilQuad_sub_levyJump_lt_zero`). The exact obstruction is the archimedean constant; the prime enters only through the symmetric fold mass, and positivity is the fold capacity inequality (`riemannHypothesis_iff_foldCapacity`). |
| Is the window integer an independent invariant? | `ι(A) = 0` iff the window form is nonnegative (`windowIndex_eq_zero_iff`); `ι` is monotone, finite, `0` up to `3/5`, and exhausts the right zeros, an even number (`iSup_windowIndex`, `iSup_windowIndex_even`); RH iff `ι < 2` everywhere (`riemannHypothesis_iff_forall_windowIndex_lt_two`). |

## 6. Tools

**Developed.**
- Window calculus: window tests, levels, stages, locality in the level and in the Euler factors, window
  involution, translation of windows.
- Fold calculus: fold identity, in-window counts, end translation, fold bounds, symmetric/antisymmetric
  splitting, extremal tests.
- Canonical class: density at the end distances, Riesz degree as an integral of `ψ_{1/2}`, symmetry,
  semiboundedness with the pole capacity.
- Window transform and multiplier; the unitary locus of the window involution.
- Realizations: real linear maps into normed spaces, the zero map on `ℓ²(zeros)`, cell bumps and the
  infinite-dimensionality argument from short-window coercivity.
- Homogeneity of Weil's form; integral correspondences acting on window tests; windowed Tate law.
- Young duality for the window genus; curve window maps into `ℂ^{2g}`.

**Used from the corpus.** Markov form and sinh capacity (RHTower `WeilMarkovPoleCapacity`); window
criterion and primes of a window (AHD); jump count of prime-free cycles (LST); scaling surface, Hodge
defect filtration, zero map, genus function, curve data, contact law, golden datum (ACS); Tate's limit law
(AET); theta `h⁰` (AOG); prime flips (ArithmeticCountingPositivity). The archimedean exit (killing)
potential of a window, `−½log(1 − e^{−2(R−x)}) − ½log(1 − e^{−2(R+x)}) − (3/2)R − (γ + log π)`, and the
window-gauge balance `jump energy + ∫F²(killing) + polar forcing` are in ArithmeticOrientationTheory
(`archWindowKilling`, `fullZeroForm_eq_windowGauge_balance`); they are the archimedean counterpart of the
canonical density. The first-prime fold on odd tests is paid by ground-state transforms and micro-folds in
ArithmeticIncidencePositivity (`fullZeroForm_ge_of_odd_support_le_threeHundredFiftyThreeThousandths`).

**To develop.** Poincaré inequalities for arithmetic jump kernels on intervals with the canonical density as
potential; Arakelov `h⁰` on lattices of growing rank; indefinite theta functions of window correspondences;
Krein and Lax–Phillips structures for the scattering channel of `Λ(s)/Λ(s+1)`.

## 7. Open research topics

1. **The first prime as an inequality between counts.** At the first-prime stage
   `Q = Ω(0)‖H‖² + J_∞ + (log 2/√2)(anti₂ − sym₂) + pole`. No identity with finitely many squares exists
   (the archimedean obstruction); what is open is the inequality `|Ω(0)|‖H‖² + (log 2/√2)sym₂ + ½s² ≤
   J_∞ + (log 2/√2)anti₂ + ½c²` on `log 2 ≤ A < log 3`, i.e. a Poincaré inequality for the Lévy count on the
   middle of the window that also pays the symmetric fold mass of `T₂` on its ends.
2. **The whole prime-free window: one even direction.** Positivity of `Ω(0)‖H‖² + J_∞ + pole` on windows
   `< log 2`: from the jump count to `1/32` (LST), for all tests by estimates to `3/5` (ACS), for odd tests
   past the first prime to `0.724` (ACS, AIP), on the cosh hyperplane across the prime-free window and past
   it to `log 2 + 1/50` (LST `WindowJumpCounts`). Hence every window shorter than `log 2 + 1/50` has at
   most one negative direction (`not_negative_plane`); what is open is the cosh capacity of that single
   even direction, and any derivation from the count beyond `1/32`. The window potential `archWindowKilling − k_A` is the natural Schrödinger potential; at the
   centre it is `−log(1 − e^{−2R}) − (3/2)R − (γ + log π)` before the primes act, positive only on short
   windows, so the interior jumps must contribute.
3. **Window capacity.** The fold capacity inequality uniform in `A` (`riemannHypothesis_iff_foldCapacity`,
   RH); the canonical density at the end distances is the potential.
4. **Window naive heights.** A function on window correspondences, nonnegative for an arithmetic reason,
   at bounded distance from `q_x` (RH at every window).
5. **The dilation constant.** The second-order pencil is positive for `K ≤ βJ/(κ·windowFloor)`; how the
   admissible `K` behaves as `A → ∞` is the horizon criterion.
6. **Window Frobenius at infinity.** An operator on the window object whose fixed line is `Re s = ½` and
   which places the poles of `Λ(s)/Λ(s+1)`; the window involution has the right unitary locus but is an
   isometry on every datum.

## 8. Pillar theorems

| Theorem | Lean |
|---|---|
| Locality; Euler-factor locality; window criterion | `weilQuad_eq_markovForm_windowLevel`, `weilFullFunctional_congr_window`, `riemannHypothesis_iff_windowForm_nonneg` |
| Window Serre duality | `weilQuad_comp_neg`, `weilQuad_windowInvolution` |
| Fold identity; Weil's form folded | `jump_sub_creation_eq_fold`, `weilQuad_eq_fold_sub_canonical` |
| Canonical class: shape, degree, symmetry | `canonicalDensity_eq_halfChebyshev`, `integral_canonicalDensity`, `canonicalMass_eq_integral_halfChebyshev`, `canonicalDensity_reflect` |
| Signed folds; arithmetic bounded by the canonical class | `weilQuad_eq_signedFolds`, `abs_weilQuad_sub_arch_le` |
| Stages: prime-free, first prime | `weilQuad_eq_arch_of_primeFree`, `weilQuad_eq_firstPrimeFold`, `weilQuad_eq_firstPrime_signedFold` |
| Fold capacity criterion | `riemannHypothesis_iff_foldCapacity` |
| Archimedean obstruction at the first prime; no count identity | `weilQuad_eq_of_foldFree`, `exists_foldFree_poleFree`, `not_exists_countIdentity` |
| At most one negative square below `log 2 + 1/50` | `weilQuad_ge_of_coshOrthogonal`, `not_negative_plane` |
| Semiboundedness; second-order pencil | `weilQuad_ge_neg_windowFloor`, `pencil_nonneg` |
| Window Frobenius at infinity | `windowTransform_windowInvolution`, `norm_windowMultiplier_eq_one_iff`, `windowTransform_windowInvolution_mul` |
| The window `h¹` is the primitive Künneth `h¹` | `primitiveH1_windowCycle`, `kunneth_windowCycle` |
| Realizations ⇔ RH; no finite-dimensional window cohomology | `riemannHypothesis_iff_forall_windowRealization`, `not_isWindowRealization_of_finiteDimensional` |
| Window index | `windowIndex_eq_zero_iff`, `iSup_windowIndex_even`, `riemannHypothesis_iff_forall_windowIndex_lt_two` |
| Window genus is a Young conjugate | `isGreatest_shannonSurplus`, `exists_windowGenus_ge`, `tendsto_exp_arithH0_div_exp` |
| Windowed Tate law | `exists_window_naiveHeight_iff`, `tendsto_naiveHeight_nsmul_div`, `riemannHypothesis_iff_forall_window_naiveHeight` |
| Curve windows | `toeplitz_eq_norm_sq_curveWindowMap`, `forall_curveWindowRealization_iff_unitary`, `curveWindow_posDef_iff` |
| Selection | `weilFullFunctional_primeFlip_eq`, `exists_flip_twin_of_window` |

## 9. Traps

| Trap | Truth |
|---|---|
| A window is the semilocal object `{∞} ∪ {p ≤ e^A}` | The window is global: archimedean jumps reach every scale and the pole couples everything; only the jumps are finite |
| The creation potential is a cost of all primes | Departing jumps pay their own creation; only `k_A` remains, concentrated at the ends |
| Every prime jump is a cost | Each fold is an antisymmetric gain minus a symmetric mass; only the symmetric mass is negative |
| The first prime is the obstruction to a count identity | The obstruction is `Ω(0)` on fold-free, pole-free tests, infinite-dimensional, before any prime acts |
| A finite-dimensional window cohomology | Short windows are coercive; every realization is infinite-dimensional |
| A realization is progress | Its existence is RH; the zero map is one; the content is a construction without zeros |
| A naive height can be smaller than the form | Tate's limit recovers `q_x` from any naive height |
| Locality or the Markov property selects `ζ` | Bounded windows have flip twins with identical window functionals and no Weil positivity |
| The window involution orients | It is an isometry on every datum; only its multiplier distinguishes the line |
| The second-order bulk term is irrelevant to the sign | It pays every window at bounded dilation constant; RH is the limit `K → ∞` |
| The near-radical rank `2e^{2a}` is time–frequency numerology | It is the Young conjugate of the zero density, the theta count of the integers of degree `2a` |
| A window index `1` is possible in the limit | Right zeros pair; the limit is even |

## 10. Place in the research and relation to other programmes

| Programme | Relation |
|---|---|
| `ArithmeticHodgeTheoryOfDegenerations`, `ArithmeticDegenerationTheory` | the degeneration whose second order is the window form; CWS uses the window criterion and the primes of a window, and answers the second-order pencil on windows |
| `LatticeSectionTheory` (incl. `WindowJumpCounts`) | single-prime window jump counts and the `T₂`-graph identity through `log 3`, coercivity on the cosh hyperplane to `log 2 + 1/50` (used for `not_negative_plane`); Künneth Riemann–Roch, primitive `h¹ = ½δ`, jump count of prime-free cycles (short-window coercivity), Epstein fakes, Stepanov over `𝔽_q` |
| `ArithmeticCastelnuovoSeveri` | scaling surface, Hodge defect filtration (the window index), zero map, genus function (the window genus), curve data, contact law, golden datum |
| `ArithmeticEffectivityTheory`, `ArithmeticOrientationGeometry` | Tate's limit law (windowed here), correspondence algebra, theta `h⁰` of `Spec ℤ` |
| RHTower `WeilMarkovPoleCapacity` | Markov form and sinh capacity; CWS splits it into folds and the canonical class |
| `ArithmeticCountingPositivity` | prime flips, used as the selection twins of bounded windows |
| WD, PM routes | window integers reduce to precision (WD); placement is the PM question for `Λ(s)/Λ(s+1)` |

CWS sits between the degeneration (which says where the sign lives) and the producers (which must supply
it): it is the exact anatomy of the object a producer has to act on, one window at a time.

## 11. Success criteria and criteria for contributions

The programme succeeds when the window `h¹` is realized by a count, a capacity or a placement at every
window length — first at the whole prime-free window, then one prime at a time, starting with the
symmetric fold mass of `T₂` — or when it is proved which of these carriers cannot exist. Every question of
§5 has a theorem as its answer; the open topics of §7 are the remaining ones.

A contribution must:
1. be stated on window tests of a fixed length, or as a law in the length;
2. say which part of the window form it controls: archimedean jumps, antisymmetric fold counts, symmetric
   fold masses, canonical density, pole;
3. say what it does on the fakes (golden curve, prime flips, Epstein lattices), since a law that holds on
   them is soft;
4. be an identity or a structural inequality, not an estimate that loses a factor growing with `A`;
5. be unconditional; implications into RH and equivalences are labelled as such.

## 12. Big picture

Weil's form on a window of length `A` is a finite arithmetic object: an archimedean jump energy; for each
active prime power a fold of the window onto itself, contributing an antisymmetric count minus a symmetric
mass; a canonical class `ψ_{1/2}(e^{−u}) + ψ_{1/2}(e^{A+u})` that the creation potential leaves after the
exits, concentrated at the ends with Riesz-mean degree; and a pole plane with one negative square. The
canonical degree bounds the form from below, so the prime-free second-order term of the degeneration
pays every window at bounded dilation constant. Every one of these laws holds on every weight; bounded
windows have flip twins; a realization of the `h¹` exists exactly under RH and is never
finite-dimensional, while over `𝔽_q` it is the `2g`-dimensional Frobenius orbit and the golden fake has
none. The integer of a window exhausts the right zeros in pairs; its genus is the Young conjugate of the
zero density, the theta count of the integers. At the first prime no identity "jump count + fold
counts + finitely many squares" exists: the obstruction is the archimedean constant on an
infinite-dimensional space of fold-free tests, so the carrier must be an inequality between counts — the
fold capacity inequality, a Poincaré inequality for the Lévy count that also pays the symmetric fold
masses, first the one of `T₂`.
