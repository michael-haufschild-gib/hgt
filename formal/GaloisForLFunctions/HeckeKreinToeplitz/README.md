# Hecke-covariant Krein–Toeplitz Theory (HKT)

**Arithmetic Krein–Langer theory: local-to-global indefinite harmonic analysis of the Weil kernel.**

**One question.** RH is a property of one kernel, not of one function. The explicit-formula pairing of a test with its Hecke translates is a Hermitian kernel on the multiplicative group of positive rationals, and RH says it has no negative squares. Mathematics has a complete theory of Hermitian kernels with finitely many negative squares on `ℤ` and `ℝ` (Krein–Langer, Pontryagin spaces, Toeplitz forms), and almost none on the group that matters here. HKT asks what that theory is on `Γ = ℚ_{>0} ≅ ⊕_p ℤ`, with the primes acting by translation, and on its adelic completion, the idele class group `𝔸^×/ℚ^×`, whose places supply the local constituents of the kernel:

- its structure theorem;
- its index formula;
- its notion of convergence;
- its local-to-global law;
- above all, an **arithmetic Krein–Langer theorem**: the index of the Weil kernel computed from its local constituents (one-prime towers, the archimedean factor, the pole) and one global law, as Castelnuovo–Severi gives index zero over `𝔽_q`;
- which of its theorems see the difference between `Λ` and its twins.

HKT studies **Hecke-covariant Hermitian kernels** on the Hecke lattice `Γ`.

- *Basic object:* a kernel `k : Γ → ℂ` with `k(u⁻¹) = conj k(u)` and its Toeplitz form `T_k(c) = Σ c̄_a c_b k(a⁻¹b)` on finitely supported `c`.
- *Basic invariant:* the **negative index** `κ(k) ∈ ℕ ∪ {∞}`, the supremum of negative squares of `T_k` over finite families.
- *Basic spectral picture:* positive mass on the **prime torus** `Γ̂ = 𝕋^P`, plus reflected pairs of characters off it.
- *Basic arithmetic instance:* the Weil kernel `W = Γ_∞ + poles − P`. The archimedean factor is a kernel on `ℝ_{>0}`; each prime contributes its tower `⟨p⟩ ≅ ℤ`; the pole is the one removable hyperbolic direction.

Everything is unconditional; RH appears only inside equivalences.

Namespace `GaloisForLFunctions.HeckeKreinToeplitz`; umbrella `HeckeKreinToeplitz.lean`.

---

## 1. Place in the research

The frontier has three walls ([walls ledger](../../../docs/reports/review-2810/walls-ledger.md), [field assessment](../../../docs/reports/review-2810/obstacles-summary.md#28-would-the-obstacles-in-22-need-a-new-field-of-mathematics), `docs/reports/review-2810/fable.md`):

- **Wall 1** asks for a positivity theorem that sees multiplicativity (selectivity).
- **Wall 3** asks for a notion of convergence under which indefinite forms of bounded index are closed (transfer).
- **Wall 14** asks for a construction whose output is a positive-definite kernel (carrier).

All three are statements about one Hermitian kernel on a group, with finitely many negative squares and covariant under translations. HKT is the field in which these three are structure theorems about that object, rather than three estimates.

The corpus fixes what any such theorem must survive.

| Requirement | Corpus statement | Consequence for HKT |
|---|---|---|
| **Selectivity** | Positivity at every root selects `Λ` among weights `|λ| ≤ Λ` (SMAP) | Every sufficient hypothesis fails for the Liouville twin. |
| **Beyond the margin** | The pole-hyperplane gap `2 log 2` is attained by single-prime flips `p ≥ 11` that fail complete positivity (ACP) | A spectral gap of the prime form is not an index ceiling; the theory must see every prime's sign. |
| **Precision** | `λ` and `λ + εn^{−η}`, `η < ½`, are never both positive along a nonnegative tower (SMAP) | Statements stable under relative error `o(1)` in prime counts cannot bound the index. The input is structural: the Euler product and functional equation used as identities. |
| **Unbounded aperture** | One-prime tower positivity is RH even for pole-free generators of arbitrarily small support (ACS, SMAP) | Finite-aperture inequalities move continuously and cannot decide; the index lives on the whole tower. |
| **Lindelöf test** | Finite off-line support ⟹ zeros approach the line ⟹ LH ∧ a zero-free strip (RHTower) | Every finite-index theorem for `ζ` proves LH; an argument that bounds the index without LH-strength input is wrong. |

The corpus built most of the objects without naming the field. HKT takes them as its base.

| Programme | Interface |
|---|---|
| [ArithmeticPositiveDuality](../ArithmeticPositiveDuality/README.md) | Herglotz–Bochner on `ℚ_{>0}` and on lattices (`isPosDefOnGroup_posUnits_iff`, `isPosDefOnLattice_iff`); Kronecker decomposition of the spectral measure (`kronecker_decomposition`); the two-prime spline orbit as a Bochner problem on the torus (`riemannHypothesis_iff_exists_torusMeasure`); Weil for curves as positive definiteness on `ℤ` (`curve_rh_tfae`). HKT is the indefinite (finite negative index) extension of APD's positive theory. |
| [ArithmeticOrientationGeometry](../ArithmeticOrientationGeometry/README.md) | Orbit correlations `c_x(g)` are HKT kernels restricted to `ℝ`; the spline orbit counts right zeros on rational Hecke orbits (`zeta_splineOrbit_negIndex_law`, `riemannHypothesis_iff_splineRatHecke_negIndex_eq_zero`); heat-collision index (`TheIndexExit`). HKT supplies the group-theoretic structure (Krein–Langer class, aliasing, closedness) behind these laws. |
| [ArithmeticCastelnuovoSeveri](../ArithmeticCastelnuovoSeveri/README.md) | Pontryagin law for finite configurations (`pontryagin_law_finite`); one prime tower sees the whole defect of `ζ` (`zeta_one_prime_tower_law`, `deepSparse_zeta`); Wolff blindness, resonant primes, fake curves (golden datum). In HKT these are restrictions of a Krein–Langer kernel to cyclic sublattices. |
| [SelectiveMultiscaleArithmeticPositivity](../SelectiveMultiscaleArithmeticPositivity/README.md) | The selection theorem (`atomicPositiveAt_iff`); the margin `2 log 2`; the dyadic multiresolution of the complete source; tower positivity of pole-free generators is RH (`riemannHypothesis_iff_towerPositive_poleFree_small`); precision rigidity (`not_towerPositive_and_perturbed`). HKT's selectivity and precision principles are SMAP's acceptance tests. |
| [ArithmeticCountingPositivity](../ArithmeticCountingPositivity/README.md) | Harmonic correlation pays the gap `(2 log 2)c_N²`; parity fibre counts; sparse and large prime flips keep the gap and fail complete positivity. These are the battery entries that share every soft spectral property of `Λ`. |
| [ArithmeticIndexDescent](../ArithmeticIndexDescent/README.md), [SignedArithmeticHodgeTheory](../SignedArithmeticHodgeTheory/README.md) | Negative index of complete Weil Grams under source presentations; uniform finite index for every prime layer except the first; work and index share the finite stratum. HKT gives the stratum its structure theorem and the first prime layer its index formulation. |
| [ArithmeticLorentzianGeometry](../ArithmeticLorentzianGeometry/README.md) | Signature certificates; RH as reflection positivity of the Cayley ladder; trickle-down on every Frobenius ladder is the one-sided square-root count; the local factor trickles down by Ramanujan. These are the local-to-global law over `𝔽_q` that HKT must reproduce. |
| [ArithmeticCorrespondencePositivity](../ArithmeticCorrespondencePositivity/README.md) | Sparse annihilators and the Stepanov mechanism (`1 − T_p^N` kills exactly critical lattice symbols); prime-error energy and genus laws; the elliptic Mertens budget is the strict Hasse bound. The counting side of the local-to-global law. |
| [RenormalizedArithmeticPotentialTheory](../RenormalizedArithmeticPotentialTheory/README.md), [SpacingScaleHarmonicAnalysis](../SpacingScaleHarmonicAnalysis/README.md) | Atomic Weil forms at the spacing scale; spectral gap `2 log 2` of the prime form; the exact splitting of the complete matrix in the separated regime; the diagonal regularized by atom width. These are the finite sections of HKT's kernel. |
| [TransThresholdPairCorrelation](../TransThresholdPairCorrelation/README.md), `ShallowCauchyPrimeEnergy` | Inertia of explicit-formula Grams beyond bandwidth one: the exact exchange rate, and the signed coalescent prime-pair kernel; shallow Cauchy energy at depth `1/log T`. The census face of the index. |
| [MultiplicativePositivityGeometry](../MultiplicativePositivityGeometry/README.md) | Positive-definite functions and Bochner theory for the boundary divisor; the Fejér barrier. |
| `HTGeometry` | Hermitian inertia (`hermNegIndex`, `negIndex_eq_card_neg_eigenvalues`); Krein–Langer inertia bounds (`sigNeg_le_of_add_sum_sq_nonneg`, `exact_neg_inertia`); lower spectral windows; infinite-torus Fourier theory. |
| `RHTower` | Explicit formula, Weil criterion, de Bruijn–Newman flow, Ki–Kim–Lee finiteness; depth strata (`LindelofCosineFiniteDefectDepth`, `DeBruijnHighCollisionsReadTheDepth`); finite-level existence of Weil-positive weights. |

---

## 2. Why

**Weil over `𝔽_q` is positive definiteness on `ℤ`.**

- For a curve, the trace sequence `m ↦ Σ_i β_i^m` (with `β_i = α_i/√q`) is a Hermitian function on `ℤ`; it is positive definite iff every `|β_i| = 1` (`curve_rh_tfae`).
- If some eigenvalues leave the circle, they come in reflected pairs `β, 1/β̄` (functional equation), and the sequence has exactly one negative square per pair. The Krein–Langer decomposition of the trace sequence is the eigenvalue list; its negative index is the number of outer eigenvalue pairs.
- The golden datum `1 − 5X + 5X²` has every soft structure and index one.
- Weil does not bound this index by estimates. Riemann–Roch on `C × C` produces an effective class, and Castelnuovo–Severi turns it into index zero. Stepanov does it by a count: an auxiliary polynomial vanishing to high order at the rational points gives a one-sided square-root count, and trickle-down on every Frobenius ladder is equivalent to that count. The index is computed from local data (one Frobenius) and one global law (a count or a Hodge index).

**Over `ℤ` the group is `ℚ_{>0}`, and its completion is the idele class group.** Translating a test `g` by `log u`, `u ∈ ℚ_{>0}`, and pairing with `g` gives the **Hecke orbit kernel** `K_g(u) = W(g, τ_{log u} g)`. By the explicit formula, `K_g(u) = Σ_ρ ω_ρ(g) u^{ρ−1/2}`:

- an on-line zero `½ + iγ` contributes the unitary character `u ↦ u^{iγ}`, the point `(p^{iγ})_p` of the prime torus, with weight `|ĝ(γ)|² ≥ 0`;
- an off-line zero `ρ` and its reflection `1 − ρ̄` contribute the reflected pair of non-unitary characters `(p^{ρ−1/2})_p`, `(p^{1/2−ρ̄})_p`.

The on-line part is positive definite (Bochner); each off-line pair is a hyperbolic plane. RH is `κ(K_g) = 0`; finite off-line support is `κ(K_g) < ∞`. On the prime side the same kernel splits by places:

- the archimedean factor, a kernel on `ℝ_{>0}`;
- the pole, one removable hyperbolic direction;
- for each prime `p`, a term carried by the tower `⟨p⟩`.

No constituent is positive by itself; the index is a global invariant of their assembly.

**What changes.** The corpus treats the finite negative index as a defect to bound. HKT treats it as an invariant to compute: a Krein–Langer structure theorem with a price list, assembled from local constituents. Five consequences follow from this point of view, and each is a theorem to prove, not a reformulation:

1. *Finite support becomes a structure.* `κ(K) < ∞` means `K` = positive definite + finitely many hyperbolic pairs. The index is read off the decomposition, and the decomposition is the subtracted-lag receiver.
2. *Transfer becomes topology.* Bounded index is a closed condition for pointwise convergence of kernels. Positivity proved on atomic or truncated families passes to the limit in the kernel topology; it does not in `L²` of tests, on which the Weil form is not continuous.
3. *Local-to-global becomes a lattice law.* A kernel on `Γ` restricts to every sublattice. Pairs whose restrictions coincide merge; pairs that become unitary disappear. One coordinate circle can hide pairs (aliasing); for arithmetic pairs two primes never alias.
4. *Positivity becomes the last step.* The order is index theory first, then a count or Riemann–Roch-type identity that bounds the index, then positivity as a consequence. Analytic estimates verify local inputs; they never cancel signs globally.
5. *Finite index is a Lindelöf-level statement.* Finitely many hyperbolic pairs means the zeros approach the critical line, which gives LH and a zero-free strip. The finite stratum is a target of the same depth as LH, and LH is the diagnostic for every claimed index bound.

---

## 3. Objects and language

| Weil over `𝔽_q` | Krein–Toeplitz object | Over `ℤ` |
|---|---|---|
| Frobenius powers `ℤ` | the group `G` of translations | Hecke lattice `Γ = ℚ_{>0} ≅ ⊕_p ℤ`; completion `𝔸^×/ℚ^×` |
| one Frobenius | a cyclic sublattice `⟨u⟩` | a prime tower `⟨p⟩ ≅ ℤ` |
| unit circle | unitary dual `Ĝ` | prime torus `𝕋^P` (`PrimeTorus`) |
| eigenvalues `β ∈ ℂ^×` | complex characters `χ : G →* ℂ^×` | logarithmic characters `u ↦ u^{ρ−1/2}`, i.e. `(p^{ρ−1/2})_p` |
| functional equation `β ↔ 1/β̄` | reflection `χ ↦ χ^†`, `χ^†(u) = conj(χ(u))⁻¹` | `ρ ↔ 1 − ρ̄` |
| trace sequence | Hermitian kernel `k`, `k(u⁻¹) = conj k(u)` | Hecke orbit kernel `K_g(u) = W(g, τ_{log u}g)` |
| local factor at a point | local constituent | archimedean factor on `ℝ_{>0}`; prime term on `⟨p⟩`; pole |
| `|β| = 1` | unitary character (fixed by `†`) | zero on the line |
| `|β| ≠ 1` pair | **hyperbolic pair** `h_{χ,ω} = ωχ + ω̄χ^†` | off-line quartet (with conjugation) |
| `#{|β| > 1}` | negative index `κ(k)` | Hodge defect = number of right zeros seen |
| point count `N_k ≥ q^k + 1 − Cq^{k/2}` | global law bounding `κ` | one-sided prime count `ψ(x) − x ≤ C√x log²x` |
| Castelnuovo–Severi | `κ(k) = 0` from the global law | RH |

**Words.**

*Structure.*

- *Gram matrix* of a family `x : ι → G`: `(k(x_a⁻¹x_b))_{a,b}`.
- *Negative index* `κ(k)`: the supremum over finite families of the number of negative squares.
- *Krein–Langer class* `KL(G)`: kernels `p + Σ_{j∈J} h_{χ_j,ω_j}` with `p` positive definite, `J` finite and `ω_j ≠ 0`.
- *Spectral data*: the positive part's Bochner measure on `Ĝ` and the finite set of hyperbolic pairs.
- *Separation at `u`*: the values `χ_j(u)` are off the unit circle, and the `2|J|` numbers `χ_j(u), χ_j^†(u)` are distinct.
- *Aliasing on a subgroup `H`*: two pairs with equal restrictions to `H`, or a pair that becomes unitary on `H`.
- *Hecke covariance*: the Gram matrix of a translated family is unchanged.
- *Growth exponent along `u`*: `limsup (1/n) log |k(u^n)|`.

*Arithmetic tests.*

- *Twin orbit*: the kernels obtained by replacing `Λ` with `ωΛ`, `|ω| = 1`; the control family of every selectivity test.
- *Selective* statement: one that fails for some bounded twin.
- *Parity-breaking* input: one that distinguishes `λ`-twisted from untwisted data.
- *Precision-faithful* input: one that distinguishes `Λ` from `Λ + εn^{−η}` for every `η < ½`.
- *Battery*: the Liouville twin; scalings `cΛ` and quadratic mixtures; single-prime flips with the maximal margin; `Λ + εn^{−η}`; the golden curve; over-regular Beurling systems; Davenport–Heilbronn functions.

*Local-to-global.*

- *Index-carrying topology*: a topology on kernels, or a completion of the test space, in which bounded negative index passes to limits.
- *Count*: a one-sided bound at square-root precision.
- *Local-to-global law*: a map from local constituents and one count to a global index.
- *Exhaustion statement*: names source, form, domain, growth parameter and error currency together.

---

## 4. Mechanisms

1. **Hyperbolic planes.** For a character `χ` and weight `ω`, the Toeplitz form of `h_{χ,ω}` is `2 Re(ω A(c) conj B(c))`, with `A(c) = Σ c_a χ(a)` and `B(c) = Σ c_a χ^†(a)`. If `χ` is unitary then `A = B` and the form is `2 Re ω |A|²`. Otherwise `A, B` are independent functionals and the form is a hyperbolic plane: exactly one negative square.
2. **Upper bound by sums of squares.** `2 Re(ωAB̄) ≥ −|ω|(|A|² + |B|²)`, so adding `|J|` squares of linear functionals makes `p + Σ h_j` nonnegative. A form that becomes nonnegative after adding `n` squares has at most `n` negative squares (`negIndex_le_card_of_nonneg_on_ker`). Hence `κ(p + Σ_j h_j) ≤ |J|` for every positive-definite `p`, unconditionally.
3. **Lower bound by growth and interpolation.** On the cyclic subgroup `⟨u⟩` a hyperbolic pair is a two-sided exponential `ω w^n + ω̄ w̄^{−n}` with `|w| ≠ 1`, while a positive-definite part is bounded by `p(1)`. Take test vectors `c = X^N E − F`, with coefficients on two windows `N` apart, where `E, F` interpolate unit data at the `2|J|` nodes. The hyperbolic part is then `−2 Σ_j |ω_j| |w_j|^N |a_j|²` on a `|J|`-dimensional space, while the positive part stays bounded: for large `N` the form is negative definite there. The interpolation constants come from an inverse Vandermonde matrix.
4. **Closedness.** If `k_n → k` pointwise, the Gram matrices converge entrywise on every finite family. Compressed to the negative eigenvectors of the limit Gram matrix, they converge to a negative diagonal and are eventually negative definite, so a negative-definite subspace of dimension `m` persists. Hence `{k : κ(k) ≤ m}` is closed under pointwise convergence.
5. **Restriction and aliasing.** Pulling back along a homomorphism `H → G` does not increase `κ`. On `H`, hyperbolic pairs regroup by their restricted characters. A group of pairs whose restriction is unitary is positive; a group with nonzero total weight and non-unitary restriction carries one negative square.
6. **Arithmetic characters.** For `χ_ρ(u) = u^{ρ−1/2}` the modulus at `p` is `p^{β−1/2}`.
   - Two right zeros alias on `⟨p⟩` iff they have the same real part and ordinates differing by `2πℤ/log p`.
   - On `⟨p, q⟩` they alias iff they are equal (`log p / log q ∉ ℚ`).
   - A right zero never aliases with the reflection of a right zero.
   - Small logarithmic scales separate any finite set of right exponents at one element.
   - A pair of distinct right exponents aliases at most at one prime, so at most `κ(κ−1)/2` primes are blind to a configuration of `κ` right zeros.
7. **Growth reads depth.** In the Krein–Langer class with separation at `u`, `|k(u^n)|` grows at the exponential rate of the deepest pair, and `k` is bounded on `⟨u⟩` iff it has no pair there. The mechanism is non-cancellation at the top modulus: `m` consecutive values of a unimodular exponential sum are a Vandermonde image of coefficients of constant modulus.
8. **A positive part never pays a pair.** Growth beats boundedness: every separated pair survives any positive-definite addition. An index ceiling therefore cannot come from a positive majorant. It must come from a structure: a decomposition, a count or an identity.
9. **Counting bounds the index (`𝔽_q`).** For curve data with nonnegative counts, trickle-down on every Frobenius ladder is equivalent to the one-sided square-root count; Stepanov's auxiliary polynomial supplies it for hyperelliptic curves. The local constituent at one prime contributes local RH (Ramanujan); the global law is the count.
10. **Depth strata.** On `Γ`, finitely many hyperbolic pairs means only finitely many right zeros at every depth, and the zeros approach the line. By Backlund's criterion this is LH; the finitely many deep zeros bound the abscissa below `1`. In the heat flow, high collisions read exactly this depth content, and near-axis collisions carry the rest.
11. **Precision rigidity.** Two weights share the archimedean and pole constituents, so their tower Toeplitz forms differ by the prime pairing of the difference alone. If the difference is one-signed with unbounded mass along the lags, the two weights cannot both be positive. This holds for the Liouville twin and for `n^{−η}` perturbations, whose interval sums agree up to relative error `o(1)`.

---

## 5. Pillar theorems

1. **Index formula.** `κ(p + Σ_{j∈J} h_{χ_j,ω_j}) ≤ |J|` for every positive-definite `p`, with equality under separation at one element (`negIndex_add_sum_pairKernel_le`, `negIndex_add_sum_pairKernel_eq`).
2. **Hyperbolic plane law.** A single pair has index `0` if unitary and `1` otherwise, whatever positive-definite kernel is added (`hermQuad_gram_pairKernel`, `negIndex_pairKernel_of_unitary`, `negIndex_add_pairKernel_eq_one`).
3. **Transfer.** Bounded index is closed under pointwise convergence of Hermitian kernels (`eventually_le_hermNegIndex`, `negIndex_le_of_tendsto`, `isPosDefKernel_of_tendsto`).
4. **Aliasing law.** The index of the restriction to a cyclic subgroup is the number of value classes of nonzero total weight (`negIndex_zpowers_le_card_image`, `negIndex_zpowers_eq_card_classes`). For arithmetic pairs: the one-prime law (`negIndex_prime_eq_card_classes`, `zeroChar_prime_eq_iff`); two primes decide (`negIndex_twoPrime_eq`); at most `κ(κ−1)/2` primes are blind and every other prime sees the whole index (`eq_of_alias_of_alias`, `ncard_blindPrimes_le`, `negIndex_prime_eq_of_not_blind`).
5. **Arithmetic index formula.** On `ℚ_{>0}`, a positive-definite part plus the reflected pairs of `κ` distinct points right of the critical line, with nonzero weights, has index exactly `κ`, whatever the weights and whatever positive mass the on-line zeros carry (`negIndex_hecke_pairs_eq`; on any group with small logarithmic scales `negIndex_logChar_pairs_eq`).
6. **`𝔽_q` calibration.** The trace kernel of a curve datum is a positive-definite part plus one hyperbolic pair per outer eigenvalue (`traceKernel_eq`); its index is the number of distinct outer eigenvalues (`negIndex_traceKernel`); index zero is unitarity, the square-root count and trickle-down on every Frobenius ladder (`negIndex_traceKernel_eq_zero_iff`, `negIndex_traceKernel_eq_zero_iff_count`, `negIndex_traceKernel_eq_zero_iff_trickleDown`); the golden datum has index one (`negIndex_golden_traceKernel`).
7. **Arithmetic instance.** The Hecke orbit kernel `u ↦ W(f, f(· − log u))` of a real test on a tempered zero configuration is Hermitian, its Gram matrices are the Weil Gram matrices of the translates, and its index is the number of right zeros the test sees (`gram_orbitKernel`, `isHermKernel_orbitKernel`, `negIndex_orbitKernel`). On the finite stratum it is the orbit kernel of the on-line zeros (positive definite) plus one hyperbolic pair `u^{ρ̄−1/2}` per right zero (`orbitKernel_eq_onLine_add_pairs`); it is Krein–Langer iff the test sees finitely many right zeros, and for `ζ` iff finitely many zeros lie off the line (`isKreinLanger_orbitKernel_iff`, `isKreinLanger_zetaKernel_iff`). For `ζ` and the cubic spline: index = number of right zeros, even; RH iff the kernel is positive definite iff index `≤ 1` (`negIndex_zetaKernel`, `negIndex_zetaKernel_eq_two_mul`, `riemannHypothesis_tfae_zetaKernel`).
8. **Two-prime finiteness.** The index of the orbit kernel is carried by any sublattice with dense scales, in particular by two primes (`negIndex_orbitKernel_comp`, `negIndex_orbitKernel_twoPrime`, `negIndex_zetaKernel_twoPrime`). Finite index of the Weil kernel of `ζ`, on `ℚ_{>0}` or on two prime towers, is finite off-line support, bounded heat counts, and the critical line above some height (`zetaKernel_finiteIndex_tfae`).
9. **Lindelöf law.** A Weil kernel of finite index on `Γ` has zeros approaching the line; hence LH and a fixed zero-free strip (`lindelof_of_negIndex_zetaKernel_lt_top`, `quasiRH_of_negIndex_zetaKernel_lt_top`).
10. **Self-upgrade and growth.** A Krein–Langer kernel separated at `u` and bounded along `u^n` has no pair and is positive definite; below the largest node modulus no geometric bound holds (`coeff_eq_zero_of_tendsto_zero`, `coeff_eq_zero_of_norm_le`, `isPosDefKernel_of_bounded`, `not_norm_le_of_lt_depth`).
11. **Index-carrying completion.** A completion of the test space on which the Weil kernel is continuous for the index, agreeing with pointwise kernel limits on atomic and truncated families.
12. **Arithmetic Krein–Langer theorem.** The index of the Weil kernel is bounded by a quantity computed from its local constituents and one global law (a square-root count or a Riemann–Roch-type identity). Over `𝔽_q` it reproduces index zero. It fails for every member of the battery that lacks the global law, and when it gives a finite index it implies LH.

---

## 6. Traps

| Trap | Truth |
|---|---|
| Finite index is a smallness condition | It is a structure: positive + finitely many hyperbolic pairs; the size of the weights is irrelevant |
| A pair can be paid by a large positive part | Never: growth beats boundedness, and every pair survives any positive-definite addition |
| Positivity on every coordinate circle gives positivity on `Γ` | False in general (multivariable Fejér–Riesz fails); true for the arithmetic class only because every right zero is non-unitary at every prime |
| One prime always sees every pair | Aliasing: equal real parts, ordinates `2πℤ/log p` apart, cancelling class weights |
| `L²` limits of positive tests are positive | Weil's form is not `L²`-continuous; bounded index is closed only in the kernel topology |
| Index is additive under sums of kernels | Only subadditive; cancellations of weights remove pairs |
| Bochner on the torus decides RH | The Hecke orbit kernel is positive definite iff RH; every unconditional input must still be selective |
| The maximal gap `2 log 2` of the prime form selects `ζ` | Single-prime flips `p ≥ 11` attain it and carry hyperbolic pairs; a gap is not an index ceiling |
| Short-interval prime statistics bound the index | `Λ + εn^{−η}` shares them and fails along every nonnegative tower |
| A narrow generator shortens the tower | Tower positivity is RH at every generator support |
| Finite index is a sub-Lindelöf target | Finite index forces the zeros to approach the line, hence LH |
| One-sided sieve bounds control the trans-threshold inertia | The coalescent prime-pair kernel is signed; its Poisson term cancels only against the exact main term |
| Local constituents are positive | None is: the prime terms enter with a minus sign and the pole is hyperbolic; positivity is a property of the assembly |
| A new equivalence is progress | The receivers are complete; a contribution computes, bounds or structures the index |

---

## 7. Questions the programme answers

1. **Structure.** Which Hermitian kernels on `Γ` and on `𝔸^×/ℚ^×` have finitely many negative squares, and what is their decomposition? How is the index read off the spectral data?
2. **Arithmetic index.** For the Hecke orbit kernel of `ζ`, which bounds on `κ` follow from prime-side information alone (energies, work, collision mass, first prime layer), and how do they price a pair?
3. **Local-to-global.** How many primes certify the index of a kernel? What exactly can one prime hide? When does positivity on finitely many coordinate circles give positivity on the torus? Which global law turns the local constituents into an index ceiling?
4. **Transfer.** In which topology on kernels, or which completion of tests, is bounded index closed, and which atomic and truncated receivers converge in it?
5. **Deformation.** Which flows on kernels (restriction, rotation, damping, heat) are index nonincreasing, and how is the index drop counted (collisions)? What arithmetic quantity governs the near-axis collisions of the heat flow?
6. **Calibration.** Does every theorem reduce over `𝔽_q` to Weil, and fail on the golden datum?
7. **Selectivity.** Which statements of the theory are false for the twins of `Λ`, for the maximal-margin flips and for `Λ + εn^{−η}`?
8. **Parity.** What is the positive form of the parity barrier in index language, and is the margin `2 log 2` its first quantitative trace?
9. **Lindelöf.** Why does finite index imply LH, and is there a direct local-to-global argument for that implication that does not pass through zeros?
10. **Counting over `ℤ`.** What replaces Frobenius's lattice spectrum in a Stepanov-type auxiliary construction on `Γ`?
11. **The prime 2.** Why is `2` both the multiresolution generator of the complete source and the bottleneck of the margin `2 log 2`?

---

## 8. Tools

To build, in order:

1. kernels on groups with Gram matrices and the negative index;
2. hyperbolic pair kernels and the hyperbolic plane law;
3. the index formula (upper and lower bounds);
4. closedness under pointwise limits;
5. restriction, covariance and the aliasing law;
6. logarithmic characters and the arithmetic index formula;
7. curve trace kernels on `ℤ` and the count–index equivalence;
8. the Hecke orbit kernel of a zero configuration on `Γ`;
9. two-prime finiteness and the Lindelöf law;
10. growth exponents and self-upgrade;
11. local constituents (archimedean, pole, prime towers) and their assembly;
12. the selectivity battery (golden datum, twins, maximal-margin flips, `n^{−η}` perturbations, aliasing configurations).

| Tool | Purpose | Test |
|---|---|---|
| Selective transfer to the separated regime | Turn the gap `2 log 2` into positivity of the full form at widths between the Robin–Euler ratio and the spacing | Fails for Liouville; may hold for the maximal-margin flips |
| Arithmetic Krein–Langer theorem | Index of the Weil kernel from local constituents and one global law | Reproduces index zero over `𝔽_q`; fails for Davenport–Heilbronn and over-regular Beurling systems; implies LH when it gives finite index |
| Stepanov over `ℤ` | An auxiliary construction on `Γ` giving one-sided prime counts at square-root precision without a lattice spectrum | Reproduces hyperelliptic RH; parity-breaking |
| Two-sided coalescent pair theory | Inertia of explicit-formula Grams beyond bandwidth one: prime-pair asymptotics on average at bounded constant | Reproduces the Hardy–Littlewood value on model sequences; fails for parity-twisted models |
| Index-carrying completion | A completion of the test space on which the Weil kernel is continuous for the index | Agrees with pointwise kernel limits; reproduces the one-prime tower law |
| Structural precision | Euler product and functional equation entering as identities, so that `n^{−η}` perturbations fail | The precision battery |

---

## 9. Open research topics

1. **The converse Krein–Langer theorem on `Γ`.** A Hermitian kernel on `Γ` with `κ < ∞` negative squares is positive definite plus finitely many hyperbolic pairs. On `ℤ` this is Krein–Langer; on `Γ` the Pontryagin-space proof must commute with all prime translations.
2. **Prime-side index estimates.** `κ(K_g) ≤ F(E_crit)` from the quadratic cost law; an index bound from the dyadic Chebyshev sequence along one prime; the first prime layer as a relative-compactness statement against Gamma.
3. **Multiplicative Poincaré inequalities.** The gap `2 log 2` of the multiplicative walk as a statement about the Toeplitz form of the prime kernel on finite subsets of `Γ`, and why it does not bound the index.
4. **Local-to-global with heights.** How many primes certify positivity of the kernel restricted to zeros of height `≤ T`.
5. **Inertia of explicit-formula Grams.** Higher moments `tr Â^k` as higher inertia; the signed coalescent prime-pair kernel beyond bandwidth one.
6. **Collision calculus.** The heat flow as a deformation of Krein–Langer data; the count of collisions as index drop; effective horizons; the near-axis count.
7. **The arithmetic Stepanov problem.** Auxiliary sections on `Γ` from a source other than a lattice of the spectrum.
8. **The separated regime.** The bottom of the complete Weil spectrum on atomic families between the Robin–Euler ratio and the spacing, as a positivity statement selective against Liouville.
9. **Structural precision.** An index argument in which the Euler product and the functional equation enter as identities, so that it fails for `Λ + εn^{−η}`.
10. **The Lindelöf bridge.** A direct proof that a finite-index Weil kernel forces LH, read from the kernel rather than from zeros.

---

## 10. Success criteria and what a contribution is

**Success.** The field succeeds when the three walls are three structure theorems about the Weil kernel:

1. the finite-support stratum is the Krein–Langer class, with an arithmetic estimate of the index from local constituents and one global law;
2. a transfer theorem in an index-carrying topology carries positivity from atomic families to the limit;
3. a local-to-global law reduces positivity on `Γ` to two primes and a count.

Its first selective theorem must hold for `Λ` and fail for the Liouville twin at a scale beyond the Robin–Euler point.

**First evidence of success** is any of:

- separated-regime positivity that fails visibly for the Liouville twin;
- a two-sided coalescent pair bound from an input that fails for the parity-twisted model;
- an index ceiling for the Weil kernel on two prime towers obtained from local data.

**Criteria.**

1. **Independence.** Built from arithmetic data, never from zero-indexed objects.
2. **Fidelity.** All mixed entries, Gamma, both poles and multiplicities; prime-only, collided and complete forms kept apart.
3. **Selectivity battery.** Every sufficient hypothesis fails for the battery.
4. **Parity and precision.** The theory contains an input that `λ`-twisting changes and that `n^{−η}` perturbations change.
5. **Exhaustion.** Uniformity exactly in the growing parameters, in an index-carrying topology.
6. **Calibration.** Reproduces Weil over `𝔽_q` by counting, the `2/3` census, the narrow positivity regime and the sharp gap. It does not demand the false all-overlap Metzler gauge or a pure-Markov sign, and it implies LH whenever it claims finite index.
7. **A new inequality.** A paid sign, index ceiling, count or energy bound, not another equivalence.
8. **Formal closure.** Unconditional Lean statements with every input discharged.

**A contribution** is an unconditional theorem stated in kernels, Gram matrices, characters and indices on a group. It:

- says what it gives over `𝔽_q` (Weil) and on the golden datum;
- computes, bounds or structures the index rather than restating an equivalence;
- states which hypotheses on spectral data (separation, finiteness, weights) it uses, and proves them in the arithmetic case;
- records the positive survivor of every no-go.

**Principles.**

- Selectivity: a statement that survives all twins is a dictionary, not a theorem.
- Precision: a statement that survives `n^{−η}` perturbations cannot decide the sign.
- Index is energy: every negative square has a price.
- A positive part never pays a pair.
- The pole is the only hyperbolic direction removable by one linear condition.
- Locality fails; two primes decide.
- Finite index is Lindelöf-deep.
- Regularization has a quasi-analytic boundary.
- Positivity is the last step: index, then count, then sign.
