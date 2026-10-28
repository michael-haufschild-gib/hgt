# Hecke-covariant Krein–Toeplitz Theory (HKT)

**One question.** RH is a property of one kernel, not of one function: the explicit-formula pairing
of a test with its Hecke translates is a Hermitian kernel on the multiplicative group of positive
rationals, and RH says it has no negative squares. Mathematics has a complete theory of Hermitian
kernels with finitely many negative squares on `ℤ` and `ℝ` (Krein–Langer, Pontryagin spaces,
Toeplitz forms) and almost none on the group that matters here. What is that theory on
`Γ = ℚ_{>0} ≅ ⊕_p ℤ`, with the primes acting by translation? What is its structure theorem, its
index formula, its local-to-global law and its notion of convergence, and which of its theorems
see the difference between `Λ` and its sign twins?

HKT studies **Hecke-covariant Hermitian kernels** on the Hecke lattice `Γ`. Basic object: a kernel
`k : Γ → ℂ` with `k(u⁻¹) = conj k(u)` and its Toeplitz form `T_k(c) = Σ c̄_a c_b k(a⁻¹b)` on finitely
supported `c`. Basic invariant: the **negative index** `κ(k) ∈ ℕ ∪ {∞}`, the supremum of negative
squares of `T_k` over finite families. Basic spectral picture: positive mass on the **prime torus**
`Γ̂ = 𝕋^P` plus reflected pairs of characters off it. Everything is unconditional; RH appears only
inside equivalences.

Namespace `GaloisForLFunctions.HeckeKreinToeplitz`; umbrella `HeckeKreinToeplitz.lean`.

---

## 1. Place in the research

The frontier has three walls and the corpus has shown they are one (see
`docs/reports/review-2810/fable.md`). Wall 1 asks for a positivity theorem that sees
multiplicativity (selectivity); Wall 3 asks for a notion of convergence under which indefinite forms
of bounded index are closed (transfer); Wall 14 asks for a construction whose output is a
positive-definite kernel (carrier). All three are statements about a Hermitian kernel on a group
with finitely many negative squares, covariant under translations. HKT is the field in which these
three are structure theorems about one object, rather than three estimates.

The corpus built most of the objects without naming the field. HKT takes them as its base.

| Programme | Interface |
|---|---|
| [ArithmeticPositiveDuality](../ArithmeticPositiveDuality/README.md) | Herglotz–Bochner on `ℚ_{>0}` and on lattices (`isPosDefOnGroup_posUnits_iff`, `isPosDefOnLattice_iff`), Kronecker decomposition of the spectral measure (`kronecker_decomposition`), the two-prime spline orbit as a Bochner problem on the torus (`riemannHypothesis_iff_exists_torusMeasure`), Weil for curves as positive definiteness on `ℤ` (`curve_rh_tfae`). HKT is the indefinite (finite negative index) extension of APD's positive theory. |
| [ArithmeticOrientationGeometry](../ArithmeticOrientationGeometry/README.md) | Orbit correlations `c_x(g)` are the kernels of HKT restricted to `ℝ`; the spline orbit counts right zeros on rational Hecke orbits (`zeta_splineOrbit_negIndex_law`, `riemannHypothesis_iff_splineRatHecke_negIndex_eq_zero`); heat-collision index (`TheIndexExit`). HKT supplies the group-theoretic structure (Krein–Langer class, aliasing, closedness) behind these laws. |
| [ArithmeticCastelnuovoSeveri](../ArithmeticCastelnuovoSeveri/README.md) | Pontryagin law for finite configurations (`pontryagin_law_finite`), one prime tower sees the whole defect of `ζ` (`zeta_one_prime_tower_law`, `deepSparse_zeta`), Wolff blindness, resonant primes, fake curves (golden datum). In HKT these are the restriction of a Krein–Langer kernel to cyclic sublattices. |
| [SelectiveMultiscaleArithmeticPositivity](../SelectiveMultiscaleArithmeticPositivity/README.md) | The selection theorem (`atomicPositiveAt_iff`), the selective margin `2 log 2`, the dyadic multiresolution of the complete source. HKT's selectivity principle is SMAP's acceptance test. |
| [ArithmeticIndexDescent](../ArithmeticIndexDescent/README.md), [SignedArithmeticHodgeTheory](../SignedArithmeticHodgeTheory/README.md) | Negative index of complete Weil Grams under source presentations; work and index share the finite stratum. HKT gives the stratum its structure theorem. |
| [ArithmeticLorentzianGeometry](../ArithmeticLorentzianGeometry/README.md) | Signature certificates; RH as reflection positivity of the Cayley ladder. |
| [RenormalizedArithmeticPotentialTheory](../RenormalizedArithmeticPotentialTheory/README.md), [SpacingScaleHarmonicAnalysis](../SpacingScaleHarmonicAnalysis/README.md) | Atomic Weil forms at the spacing scale; spectral gap `2 log 2` of the prime form; the diagonal regularized by atom width. These are the finite sections of HKT's kernel. |
| [MultiplicativePositivityGeometry](../MultiplicativePositivityGeometry/README.md) | Positive-definite functions and Bochner theory for the boundary divisor; the Fejér barrier. |
| `HTGeometry` | Hermitian inertia (`hermNegIndex`, `negIndex_eq_card_neg_eigenvalues`), Krein–Langer inertia bounds (`sigNeg_le_of_add_sum_sq_nonneg`, `exact_neg_inertia`), infinite-torus Fourier theory. |
| `RHTower` | Explicit formula, Weil criterion, de Bruijn–Newman flow, Ki–Kim–Lee finiteness. |

---

## 2. Why

**Weil over `𝔽_q` is positive definiteness on `ℤ`.** For a curve the trace sequence
`m ↦ Σ_i β_i^m` (with `β_i = α_i/√q`) is a Hermitian function on `ℤ`; it is positive definite iff
every `|β_i| = 1` (`curve_rh_tfae`). If some eigenvalues leave the circle they come in reflected
pairs `β, 1/β̄` (functional equation) and the sequence has exactly one negative square per pair: the
Krein–Langer decomposition of the trace sequence is the eigenvalue list, its negative index is the
number of outer eigenvalue pairs. The golden datum `1 − 5X + 5X²` has every soft structure and index
one.

**Over `ℤ` the group is `ℚ_{>0}`.** Translating a test `g` by `log u`, `u ∈ ℚ_{>0}`, and pairing with
`g` gives the **Hecke orbit kernel** `K_g(u) = W(g, τ_{log u} g)`. By the explicit formula
`K_g(u) = Σ_ρ ω_ρ(g) u^{ρ−1/2}`: an on-line zero `½ + iγ` contributes the unitary character
`u ↦ u^{iγ}`, i.e. the point `(p^{iγ})_p` of the prime torus, with weight `|ĝ(γ)|² ≥ 0`; an off-line
zero `ρ` and its reflection `1 − ρ̄` contribute the reflected pair of non-unitary characters
`(p^{ρ−1/2})_p`, `(p^{1/2−ρ̄})_p`. The on-line part is positive definite (Bochner); each off-line pair is
a hyperbolic plane. RH is `κ(K_g) = 0`; finite off-line support is `κ(K_g) < ∞`.

**What changes.** The corpus treats the finite negative index as a defect to bound. HKT treats it
as an invariant to compute: a Krein–Langer structure theorem with a price list. Three consequences
follow from the point of view, and each is a theorem to prove, not a reformulation:

1. *Finite support becomes a structure.* `κ(K) < ∞` means `K` = positive definite + finitely many
   hyperbolic pairs. The index is read off the decomposition, and the decomposition is the
   subtracted-lag receiver.
2. *Transfer becomes topology.* Bounded index is a closed condition for pointwise convergence of
   kernels. Positivity proved on atomic or truncated families passes to the limit in the kernel
   topology, while it does not in `L²` of tests (the Weil form is not `L²`-continuous).
3. *Local-to-global becomes a lattice law.* A kernel on `Γ` restricts to every sublattice; pairs whose
   restrictions coincide merge, pairs that become unitary disappear. One coordinate circle can hide
   pairs (aliasing); for arithmetic pairs two primes never alias.

---

## 3. Objects and language

| Weil over `𝔽_q` | Krein–Toeplitz object | Over `ℤ` |
|---|---|---|
| Frobenius powers `ℤ` | the group `G` of translations | Hecke lattice `Γ = ℚ_{>0} ≅ ⊕_p ℤ` |
| unit circle | unitary dual `Ĝ` | prime torus `𝕋^P` (`PrimeTorus`) |
| eigenvalues `β ∈ ℂ^×` | complex characters `χ : G →* ℂ^×` | `u ↦ u^{ρ−1/2}`, i.e. `(p^{ρ−1/2})_p` |
| functional equation `β ↔ 1/β̄` | reflection `χ ↦ χ^†`, `χ^†(u) = conj(χ(u))⁻¹` | `ρ ↔ 1 − ρ̄` |
| trace sequence | Hermitian kernel `k`, `k(u⁻¹) = conj k(u)` | Hecke orbit kernel `K_g(u) = W(g, τ_{log u}g)` |
| `|β| = 1` | unitary character (fixed by `†`) | zero on the line |
| `|β| ≠ 1` pair | **hyperbolic pair** `h_{χ,ω} = ωχ + ω̄χ^†` | off-line quartet (with conjugation) |
| `#{|β| > 1}` | negative index `κ(k)` | Hodge defect = # right zeros seen |
| Hasse–Weil | `κ(k) = 0` (positive definite) | RH |

**Words.**
*Gram matrix* of a family `x : ι → G`: `(k(x_a⁻¹x_b))_{a,b}`. *Negative index* `κ(k)`: supremum over
finite families of the number of negative squares. *Krein–Langer class* `KL(G)`: kernels
`p + Σ_{j∈J} h_{χ_j,ω_j}` with `p` positive definite, `J` finite, `ω_j ≠ 0`. *Spectral data*: the
positive part's Bochner measure on `Ĝ` and the finite set of hyperbolic pairs. *Separation at `u`*:
the values `χ_j(u)` are off the unit circle and the `2|J|` numbers `χ_j(u), χ_j^†(u)` are distinct.
*Aliasing on a subgroup `H`*: two pairs with equal restrictions to `H`, or a pair that becomes
unitary on `H`. *Hecke covariance*: the Gram matrix of a translated family is unchanged.
*Growth exponent along `u`*: `limsup (1/n) log |k(u^n)|`. *Twin orbit*: the kernels obtained by
replacing `Λ` with `ωΛ`, `|ω| = 1`; the control family of every selectivity test.

---

## 4. Mechanisms

1. **Hyperbolic planes.** For a character `χ` and weight `ω`, the Toeplitz form of `h_{χ,ω}` is
   `2 Re(ω A(c) conj B(c))`, `A(c) = Σ c_a χ(a)`, `B(c) = Σ c_a χ^†(a)`. If `χ` is unitary then `A = B`
   and the form is `2 Re ω |A|²`; otherwise `A, B` are independent functionals and the form is a
   hyperbolic plane: exactly one negative square.
2. **Upper bound by sums of squares.** `2 Re(ωAB̄) ≥ −|ω|(|A|² + |B|²)`, so adding `|J|`-many squares of
   linear functionals makes `p + Σ h_j` nonnegative; a form that becomes nonnegative after adding
   `n` squares has at most `n` negative squares (`negIndex_le_card_of_nonneg_on_ker`). Hence
   `κ(p + Σ_j h_j) ≤ |J|` for every positive-definite `p`, unconditionally.
3. **Lower bound by growth and interpolation.** On the cyclic subgroup `⟨u⟩` a hyperbolic pair is a
   two-sided exponential `ω w^n + ω̄ w̄^{−n}` with `|w| ≠ 1`, while a positive-definite part is bounded
   by `p(1)`. Test vectors `c = X^N E − F` (coefficients on two windows `N` apart) with `E, F`
   interpolating unit data at the `2|J|` nodes make the hyperbolic part `−2 Σ_j |ω_j| |w_j|^N |a_j|²`
   on a `|J|`-dimensional space, while the positive part stays bounded: for large `N` the form is
   negative definite there. The interpolation constants are fixed by an inverse Vandermonde matrix.
4. **Closedness.** If `k_n → k` pointwise, the Gram matrices converge entrywise on every finite family;
   a negative-definite subspace of dimension `m` is stable under small perturbation (compact unit
   sphere). So `{k : κ(k) ≤ m}` is closed in the topology of pointwise convergence.
5. **Restriction and aliasing.** Pulling back along a homomorphism `H → G` does not increase `κ`.
   On `H`, hyperbolic pairs are regrouped by their restricted characters; a group whose restriction is
   unitary is positive, and a group with nonzero total weight and non-unitary restriction carries one
   negative square.
6. **Arithmetic characters.** For `χ_ρ(u) = u^{ρ−1/2}` the modulus on `p` is `p^{β−1/2}`. Two right
   zeros alias on `⟨p⟩` iff they have the same real part and ordinates differing by
   `2πℤ/log p`; on `⟨p, q⟩` they alias iff they are equal (`log p / log q ∉ ℚ`); a right zero never
   aliases with the reflection of a right zero.
7. **Growth reads depth.** In the Krein–Langer class with separation at `u`, `|k(u^n)|` grows at the
   exponential rate of the deepest pair, and `k` is bounded on `⟨u⟩` iff it has no pair there.

---

## 5. Pillar theorems

1. **Index formula.** `κ(p + Σ_{j∈J} h_{χ_j,ω_j}) ≤ |J|` for every positive-definite `p`, with equality
   under separation at one element.
2. **Hyperbolic plane law.** A single pair has index `0` if unitary and `1` otherwise.
3. **Transfer.** Bounded index is closed under pointwise convergence of kernels.
4. **Aliasing law.** The index of the restriction to a subgroup is the number of non-unitary classes
   of nonzero total weight; arithmetic pairs do not alias on two primes.
5. **`𝔽_q` calibration.** The trace kernel of a curve datum lies in the Krein–Langer class of `ℤ`;
   its index is the number of outer eigenvalue pairs; the golden datum has index one.
6. **Arithmetic instance.** The Hecke orbit kernel of a test lies in the Krein–Langer class of `Γ`
   iff it sees finitely many right zeros; its index is that number; RH iff index zero.
7. **Self-upgrade.** A Krein–Langer kernel separated at `u` and bounded on `⟨u⟩` is positive definite
   there.

---

## 6. Traps

| Trap | Truth |
|---|---|
| Finite index is a smallness condition | It is a structure: positive + finitely many hyperbolic pairs; size of weights is irrelevant |
| A pair can be paid by a large positive part | Never: growth beats boundedness, every pair survives any positive-definite addition |
| Positivity on every coordinate circle gives positivity on `Γ` | False in general (multivariable Fejér–Riesz fails); true for the arithmetic class only because every right zero is non-unitary at every prime |
| One prime always sees every pair | Aliasing: equal real parts, ordinates `2πℤ/log p` apart, cancelling class weights |
| `L²` limits of positive tests are positive | Weil's form is not `L²`-continuous; bounded index is closed only in the kernel topology |
| Index is additive under sums of kernels | Only subadditive; cancellations of weights remove pairs |
| Bochner on the torus decides RH | The Hecke orbit kernel is positive definite iff RH; every unconditional input must still be selective |
| A new equivalence is progress | The receivers are complete; a contribution computes, bounds or structures the index |

---

## 7. Questions the programme answers

1. **Structure.** Which Hermitian kernels on `Γ` have finitely many negative squares, and what is
   their decomposition? How is the index read off the spectral data?
2. **Arithmetic index.** For the Hecke orbit kernel of `ζ`, which bounds on `κ` follow from prime-side
   information alone (energies, work, collision mass), and how do they price a pair?
3. **Local-to-global.** How many primes certify the index of a kernel; what exactly can one prime hide;
   when does positivity on finitely many coordinate circles give positivity on the torus?
4. **Transfer.** In which topology on kernels and tests is bounded index closed, and which atomic and
   truncated receivers converge in it?
5. **Deformation.** Which flows on kernels (restriction, rotation, damping, heat) are index
   nonincreasing, and how is the index drop counted (collisions)?
6. **Calibration.** Does every theorem reduce over `𝔽_q` to Weil, and fail on the golden datum?
7. **Selectivity.** Which statements of the theory are false for the sign twins of `Λ`?

---

## 8. Tools

To build, in order: kernels on groups with Gram matrices and the negative index; hyperbolic pair
kernels and the hyperbolic plane law; the index formula (upper and lower bounds); closedness under
pointwise limits; restriction, covariance and the aliasing law; curve trace kernels on `ℤ`; the
Hecke orbit kernel of a zero configuration on `Γ`; growth exponents and self-upgrade; the selectivity
battery (golden datum, twins, aliasing configurations).

---

## 9. Open research topics

1. **The converse Krein–Langer theorem on `Γ`**: a Hermitian kernel on `Γ` with `κ < ∞` negative squares
   is positive definite plus finitely many hyperbolic pairs (on `ℤ` this is Krein–Langer; on `Γ` the
   Pontryagin-space proof must be made to commute with all prime translations).
2. **Prime-side index estimates**: `κ(K_g) ≤ F(E_crit)` from the quadratic cost law; an index bound from
   the dyadic Chebyshev sequence along one prime.
3. **Multiplicative Poincaré inequalities**: the gap `2 log 2` of the multiplicative walk as a
   statement about the Toeplitz form of the prime kernel on finite subsets of `Γ`.
4. **Local-to-global with heights**: how many primes certify positivity of the kernel restricted to
   zeros of height `≤ T`.
5. **Inertia of explicit-formula Grams**: higher moments `tr Â^k` as higher inertia.
6. **Collision calculus**: the heat flow as a deformation of Krein–Langer data; count of collisions as
   index drop; effective horizons.
7. **The arithmetic Stepanov problem**: auxiliary sections on `Γ` from a source other than a lattice of
   the spectrum.

---

## 10. Success criteria and what a contribution is

**Success.** The field succeeds when the three walls are three structure theorems about the Hecke
orbit kernel: (i) the finite-support stratum is the Krein–Langer class with an arithmetic estimate of
the index; (ii) a transfer theorem in the kernel topology carries positivity from atomic families to
the limit; (iii) a local-to-global law reduces positivity on `Γ` to finitely many primes. Its first
selective theorem must hold for `Λ` and fail for the Liouville twin at a scale beyond the
Robin–Euler point.

**A contribution** is an unconditional theorem stated in kernels, Gram matrices, characters and
indices on a group; it says what it gives over `𝔽_q` (Weil) and on the golden datum; it computes,
bounds or structures the index rather than restating an equivalence; it states which hypotheses on
spectral data (separation, finiteness, weights) it uses and proves them in the arithmetic case; and
it records the positive survivor of every no-go.

**Principles.** Selectivity: a statement that survives all twins is a dictionary, not a theorem.
Index is energy: every negative square has a price. The pole is the only hyperbolic direction that
is removable by one linear condition. Locality fails, one prime decides. Regularization has a
quasi-analytic boundary.
