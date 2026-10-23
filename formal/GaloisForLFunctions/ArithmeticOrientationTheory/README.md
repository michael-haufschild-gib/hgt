# Arithmetic Orientation Theory (`GaloisForLFunctions.ArithmeticOrientationTheory`)

**Arithmetic Orientation Theory** (AOT) is the study of the sign-valued and integer-valued
invariants of arithmetic sources that survive passage to unbounded aperture, horizon, damping and
height, and of the counting theorems that compute them. Its objects are oriented: a signed
incidence form carries its switching class, a divisor row carries its companion (parity) class, a
reading of a source carries the question whether it separates a datum from its flip, a space of
tests at a divisor of nodes carries the dimension of its sections. Its theorems are identities,
classifications and counts; estimates are corollaries.

Everything in the theory is unconditional. The Riemann Hypothesis appears only inside exact
equivalences (the width dictionary) or as the conclusion of implications whose premise is one
finite inequality; the theory never asserts such a premise.

---

## Place in the research

The review of the three wall families (`docs/reports/review-2310/fable.md`) found that every
killed mechanism loses the same thing at the same place: the **orientation** of the source, at
the passage to a limit. Sign-blind readings (amplitudes, period moments, Grams of magnitudes)
saturate exactly at half damping; finite apertures, horizons, ranks and moment lists admit
off-line extensions; positivity and self-adjointness supply no upper bound; magnitude readers
erase orientation. The three walls are three faces of this loss: sign in estimates (Wall 1), parity
class in transport (Wall 3), effectivity in realization (Wall 14).

AOT is the programme that makes orientation the primitive object. It supplies

- the **frustration index** of a signed incidence form and its control of the ground energy;
- the **rank-one law** for the frustrating part of the odd Weil prime side, tower by tower;
- the **Nyquist rank bound** on the sections of a node divisor, the rank–nullity skeleton of a
  Riemann–Roch theorem for readings, instantiated on Dirichlet polynomials at separated heights;
- the **orientation of damped weights**, read exactly at the prime `2` by the first pronic moment,
  and the parity floor as a statement about readings;
- the **critical Wiener monoid**, the stability group of the class "paid";
- the **width dictionary** as one theorem.

| Neighbour | Interface |
|---|---|
| [Scale-Signed Incidence Criticality](../ScaleSignedIncidenceCriticality/README.md) | Supplies readings, shadows, resolution and invisibility; AOT adds flips, faithfulness and the closure law of blindness. |
| [Signed Arithmetic Energy Incidence](../SignedArithmeticEnergyIncidence/README.md) | Supplies balance, holonomy and local payment; AOT attaches the frustration index and mass to the switching class and relates them to the ground energy. |
| [Arithmetic Incidence Positivity](../ArithmeticIncidencePositivity/README.md) | Supplies the ratio/product atoms and the `2R − P` form of the odd autocorrelation; AOT proves the per-tower rank-one law of the product part. |
| [Trans-Horizon Incidence Mechanics](../TransHorizonIncidenceMechanics/README.md) | Supplies the even flip, the parity barrier, the first pronic moment and the critical Wiener algebra; AOT reads the flip at `2`, restates the barrier for readings, and proves the monoid structure. |
| [Bézout–Valuation Incidence](../BezoutValuationIncidence/README.md) | Supplies the damping chain and its residue modes; AOT shows the flow transports orientation exactly on residue combinations. |
| [Arithmetic Castelnuovo–Severi](../ArithmeticCastelnuovoSeveri/README.md) | Supplies the scaling surface, the Hodge index and the effectivity axioms; AOT's width dictionary places them beside the other units, and its section counts are the finite-dimensional shadow of the missing Riemann–Roch. |
| [Bi-Scale Uncertainty](../BiScaleUncertainty/README.md) | Supplies the linear-band form of RH and the node criticality laws; AOT's Nyquist bound is the sampling-theoretic reading of the same square-root threshold. |
| [Square-Root Threshold](../SquareRootThreshold/README.md) | The sampling threshold `N ≍ T` of the Nyquist bound is the test-length threshold of that programme. |
| [Arithmetic Criticality Theory](../ArithmeticCriticalityTheory/README.md) | Supplies the ground-energy path `μ(A)` and the non-Z-type obstruction on the prime anti-diagonals; AOT reads that obstruction as frustration and asks whether the frustration index at aperture `A` is `μ(A)`. |
| [Arithmetic Continuation and Critical Energy](../ArithmeticContinuationAndCriticalEnergy/README.md) | Supplies the exact damping derivative (boundary flux, jump energy, forcing) and admission as the damping unit; the aperture analogue of that identity is the oriented-transport problem of §7. |
| [Arithmetic Compensation Theory](../ArithmeticCompensationTheory/README.md) | Supplies the doubly exponential decay that every positive aperture floor must respect, one of the battery tests of §8. |
| [Arithmetic Positivity Theory](../arithmetic-positivity-theory/README.md) | Supplies the temperedness gate, the one proved instance of the shifted-pair test of §8, and the factorial calibration families. |
| [Trans-Threshold Pair Correlation](../TransThresholdPairCorrelation/README.md) | Works beyond the diagonal `N ≍ T` of the Nyquist bound, where section counts would have to beat the large-values estimate. |

**The shared target.** The programmes work on RH as the sign of one critical arithmetic form and
on the critical cancellation of the actual Möbius and prime source. AOT contributes the
orientation-side half: an exact account of which invariants carry the sign across limits, which
readings are faithful to it, and what the frustrating part of the critical form is made of.

Read §2 for the objects, §3 for the pillar theorems, §5 for the traps, §7 for the open problems.

---

## 1. Why

### 1.1 One invariant in many units

Write `Δ = sup |Re ρ − ½|`. Every receiver of the corpus reads `Δ` exactly, each in its own
unit: damping (the infimum of the derived set of admitted dampings is `Θ − ½`), aperture (the
ground energy `μ(A)` stays nonnegative iff RH), growth (the Chebyshev band is linear iff RH), index
(every intersection Gram has exactly one positive square iff RH), effectivity (an effectivity with
the Riemann–Roch and ample axioms exists iff RH). The width dictionary (`widthDictionary_tfae`)
is the change of coordinates. A new unit is not a new proof.

### 1.2 The loss of orientation

In every unit the unconditional estimate sits at the value width `½` would give, improved only by
the Vinogradov–Korobov factor. The mechanisms that would close the gap fail in one of a few ways,
and each failure is a loss of orientation:

- **amplitude readings** are blind: on the damped class the predicate "paid" is a function of the
  Ramanujan amplitudes exactly when `ε > ½` (the parity barrier), and blindness is closed under
  post-processing, pairing and families;
- **finite data** admit off-line extensions: a bounded-aperture certificate has width limit `½`
  in every unit;
- **positivity** of a form says nothing about its upper bound, and the frustrated part of the
  Weil ledger is never locally payable: the pole is a rank-one charge.

Mathematics has two ways of making an orientation survive limits: topological index theory and
algebraic effectivity. Neither exists for a source living on `ℤ × (scale)`. AOT builds the
finite, exact part of both.

### 1.3 What an orientation is

Three structures carry it.

**Switching classes.** A signed incidence form `c` on a finite set has the ℤ/2 class
`{s_i s_j c_ij : s_i = ±1}`. The class is trivial iff the form is balanced iff every closed-walk
holonomy is `+1` (Signed Arithmetic Energy Incidence). AOT attaches to the class an integer, the
frustration index, and a mass, and proves that they control the ground energy of the signed
Dirichlet form.

**Companion classes.** A four-free weight of the damped class has an even flip `c♭`, invisible to
every amplitude reading and to every translated moment, that can break the receiver. AOT proves
that the flip is an involution on the class and that the first pronic moment reads it exactly at
the prime `2`: `M(c♭) − M(c) = 2 log 2 · W_c(2)`.

**Effectivity.** On the scaling surface effectivity is the missing axiom. AOT builds its
finite-dimensional shadow: a reading of a test space at a node set has sections (the tests it
annihilates), and their number obeys a rank–nullity Riemann–Roch and a Nyquist bound.

---

## 2. What: objects and language

### 2.1 The dictionary

| orientation theory | signed forms | damped weights | readings | sections |
|---|---|---|---|---|
| orientation | switching class | companion class (even flip) | flip `κ : D → D` | — |
| orientation index | frustration index `ν(c)` | `W_c(2)` | — | `h⁰(A)` |
| trivial orientation | balanced | `W_c(2) = 0` | fixed by `κ` | — |
| faithful reading | ground energy at a sign vector | first pronic moment | `OrientationFaithful r κ` | rank |
| blind reading | incidence energy of `|c|` | amplitude reading | `Invisible r κ` | — |
| transport | switching covariance | damping flow on residue modes | refinement | frame bound |

### 2.2 Objects

- **Signed Dirichlet form.** `D_c(x) = Σ_{i≠j} |c_ij| (x_i + sgn(c_ij) x_j)²`
  (`signedDirichletForm`), with `sgn` the orientation sign `orientSign`. It equals
  `2 Σ_i deg_i x_i² + 2 Σ_{i≠j} c_ij x_i x_j` (`signedDirichletForm_eq`): the incidence energy with
  the diagonal replaced by the degree. Its **ground energy** is the infimum on the unit sphere
  (`groundEnergy`).
- **Sign vectors, misaligned mass and count.** `IsSignVector s` (`s_i² = 1`); `misalignedMass s c`
  is the absolute coupling of the overlaps left positive after switching by `s`;
  `misalignedCount s c` their number (ordered pairs).
- **Frustration index and mass.** `frustrationIndex c = min_s misalignedCount s c`,
  `frustrationMass c = inf_s misalignedMass s c`.
- **Prime-sum pairs.** `primeSumPairs p`: the ordered pairs of sampled positions whose sum is the
  logarithm of a prime power — the only possible frustrating overlaps of the odd Weil ledger.
- **Lattice correlations.** For a finitely supported profile `q : ℕ → ℝ`: the ratio correlation
  `R_q(m) = Σ_a q(a) q(am)` (`ratioCorr`) and the product correlation
  `P_q(m) = Σ_{ab=m} q(a) q(b)` (`productCorr`); the tower Mellin value
  `S_p(q) = Σ_i q(p^i) p^{−i/2}` (`towerMellin`); the tower product part
  `Σ_k Λ(p^k)(p^k)^{−1/2} P_q(p^k)` (`towerProductPart`); the lattice odd prime side
  `Σ Λ(m) m^{−1/2}(2R_q − P_q)` over a finite set of towers (`latticeOddPrimeSide`).
- **Readings at nodes.** A matrix `A : Matrix m n ℂ` (rows nodes, columns test coordinates); its
  Frobenius mass `Σ ‖A_ij‖²` (`frobeniusMass`), a frame bound `K` (`HasFrameBound`), its sections
  `ker A` and their number `h0 A`. The Dirichlet sampling matrix
  `dirichletSampling N lam R` reads Dirichlet polynomials of length `N` at the heights
  `lam 0, …, lam R`.
- **Oriented data.** `Orientation D` (an involutive flip); `OrientationFaithful r κ`;
  `orientationClass κ d = {d, κ d}`. The four-free damped weights `FourFreeDamped ε` with the
  even flip `evenFlipOrientation`; their amplitude reading `amplitudeReading`.
- **The even flip.** `evenFlip c = c + c_e ⋆ (δ₁ − 2δ₂)`, with the three-face description
  `evenFlip_apply`: add `c(2d)` on odd `d`, negate on `d ≡ 2 (mod 4)`, fix the rest.
- **The critical Wiener monoid.** Kernels with `Σ |g(q)| q^{−1/2} < ∞` (`CriticalWiener` of
  Trans-Horizon Incidence Mechanics), with the unit `unitKernel = δ₁`, the absolute convolution
  `absConv`, and the complex absolute kernel `absWeight`.
- **Residue combinations.** `residueCombination S a = Σ_{d ∈ S} a_d v_d` in `c₀`, with `v_d` the
  normalized residue modes of the damping chain.

### 2.3 Words

- **Oriented**: carrying a flip. **Faithful**: separating every datum from its flip.
  **Blind**: invisible to the flip. **Orientation class**: the orbit of the flip.
- **Frustration**: the positive (misaligned) overlaps of a signed form; **balanced**: zero
  frustration index; **switching**: the gauge action of sign vectors.
- **Tower**: the prime powers of one prime; **tower-local**: supported in one tower;
  **rank-one law**: a tower's product part is one square.
- **Section**: a test annihilated by a reading; **degrees of freedom**: the Frobenius mass;
  **Nyquist bound**: the upper bound on sections by degrees of freedom over the frame bound.
- **Unit**: a coordinate on the width line; **dictionary**: the change of units.

---

## 3. How: the pillar theorems

All unconditional.

### 3.1 The frustration index controls the ground energy (`FrustrationIndexControlsTheGroundEnergy`)

1. **Switching covariance.** `D_{s·c}(s x) = D_c(x)` for every sign vector `s`
   (`signedDirichletForm_switch`), and the frustration index is a switching-class invariant
   (`frustrationIndex_switch`): orientation is a property of the class.
2. **Balance.** `IsBalanced c ↔ frustrationIndex c = 0` (`isBalanced_iff_frustrationIndex_eq_zero`).
3. **Sign vectors read the mass.** `D_c(s) = 4 · misalignedMass s c`
   (`signedDirichletForm_signVector`); hence `groundEnergy c ≤ 4 ν_w(c) / n`
   (`groundEnergy_le_frustrationMass`).
4. **Ground energy zero is balance.** A nowhere-vanishing profile of zero Dirichlet energy
   switches the form into alignment (`isBalanced_of_signedDirichletForm_eq_zero`); a balanced form
   has a sign vector of zero energy
   (`exists_signVector_signedDirichletForm_eq_zero_of_isBalanced`); on a connected pattern every
   nonzero zero-energy profile vanishes nowhere (`ne_zero_of_signedDirichletForm_eq_zero`, by
   propagation of `|x|` along walks), so
   `(∃ x ≠ 0, D_c(x) = 0) ↔ IsBalanced c` (`groundEnergy_eq_zero_iff_isBalanced`).
5. **The odd Weil ledger.** Its frustration index is at most the number of ordered prime-sum
   pairs (`frustrationIndex_oddWeilLedger_le`): frustration lives on prime sums only.

### 3.1′ The frustration index of the prime triangle (`TheFrustrationIndexOfThePrimeTriangle`)

1. **Mirror pairs.** For a symmetric coupling on a linearly ordered set the misaligned count of
   every sign vector is twice the number of misaligned pairs `i < j`
   (`misalignedCount_eq_two_mul`); an unbalanced symmetric form has frustration index at least
   `2` (`two_le_frustrationIndex_of_not_isBalanced`).
2. **Three points.** Any symmetric form on three points has index at most `2`
   (`frustrationIndex_le_two_fin3`): switch the two neighbours of a vertex into alignment.
3. **The prime triangle.** At the positions with pairwise sums `log 2, log 3, log 5` and every
   sufficiently small archimedean–polar weight, the odd Weil ledger has frustration index exactly
   `2` (`frustrationIndex_primeTriangle`): the first arithmetic obstruction carries one misaligned
   overlap, in either order, after every switching, and its index is computed without evaluating
   a coupling. The frustration mass of the general odd ledger is bounded by the positive coupling
   on prime-sum pairs (`frustrationMass_oddWeilLedger_le`).

### 3.1″ The lattice odd ledger is balanced (`TheLatticeOddLedgerIsBalanced`)

1. **Tower comparison.** Within a tower the prime weight at a lattice sum is at most the weight at
   the lattice difference, `Λ(r^{i+j})/√r^{i+j} ≤ Λ(r^{|i−j|})/√r^{|i−j|}` (`primeKernel_tower_le`,
   `primeKernel_log_add_le`): a prime-sum pair of lattice points is also a prime-difference pair,
   and the difference carries the larger weight.
2. **Balance at every aperture.** Sampled at the logarithms of distinct integers `≥ 2`, the odd
   Weil ledger has only aligned overlaps (`oddFold_lattice_nonpos`), is balanced
   (`isBalanced_lattice`), has frustration index `0` (`frustrationIndex_lattice_eq_zero`), and its
   positivity is local payment (`nonneg_iff_locallyPayable_lattice`).
3. **The frustration of the odd ledger is a continuum phenomenon**: zero on the lattice at every
   aperture, `2` on the prime triangle between lattice points.
4. **The prime-sum charge bounds the frustration mass.** Every overlap is at most
   `β · prime(p_x + p_y)` (`oddFold_le_primeKernel`), so the frustration mass of any positive
   configuration is at most `β` times its prime-sum charge (`frustrationMass_le_primeSumCharge`),
   the charge being `Λ(n)/√n` at the integer `n = e^{p_x + p_y}` (`primeKernel_eq_of_exp_eq`).

### 3.2 The frustration of a tower is rank one (`TheFrustrationOfATowerIsRankOne`)

1. **Tower locality.** `P_q(p^k) = Σ_{i≤k} q(p^i) q(p^{k−i})` (`productCorr_prime_pow`).
2. **Cauchy product.** `(Σ_{i≤K} u_i)² = Σ_{k≤2K} Σ_{i≤k} u_i u_{k−i}` for sequences vanishing
   beyond `K` (`sq_sum_eq_sum_cauchy`), read off the square of the generating polynomial.
3. **Rank-one law.** `towerProductPart q p K = log p · (S_p(q)² − q(1)²)`
   (`sum_vonMangoldt_productCorr_prime_pow`): the whole product (sum-pair, frustrating)
   contribution of the tower of `p` is one Mellin square at `s = ½`, minus the pole-like term
   `q(1)²`.
4. **Orientation reading.** The product part of a tower is at least `−log p · q(1)²`
   (`sum_vonMangoldt_productCorr_prime_pow_ge`) and is a square for profiles vanishing at `1`
   (`towerProductPart_nonneg`); over any finite set of towers the odd prime side is at most twice
   its ratio part (`latticeOddPrimeSide_le_of_eq_zero`), and the product parts sum to the sum of
   the squares (`sum_towerProductPart`).

The sign of the odd form is the competition between the difference correlations, which couple
every tower to every other, and a sum of independent rank-one squares, one per prime.

### 3.2′ Prime-power sums regroup by towers (`PrimePowerSumsRegroupByTowers`)

1. **Regrouping.** `Σ_{m ≤ M prime power} F(m) = Σ_{p ≤ M} Σ_{1 ≤ k ≤ log_p M} F(p^k)`
   (`sum_primePow_eq_sum_towers`): the fibre of the least prime factor is the tower; the same for
   von Mangoldt-weighted sums (`sum_vonMangoldt_mul_eq_sum_towers`).
2. **The global product part is the sum of the tower squares.** For a profile supported on
   `[1, X]` and a horizon `M ≥ X²`,
   `Σ_{m ≤ M} Λ(m) m^{−1/2} P_q(m) = Σ_{p ≤ M} log p · (S_p(q)² − q(1)²)`
   (`sum_vonMangoldt_productCorr_eq_sum_towers`): beyond the square of the support the
   frustrating part of the odd prime side is exactly the sum of the rank-one tower squares.

### 3.2″ The ratio part decomposes over cosets (`TheRatioPartDecomposesOverCosets`)

1. **Coset decomposition.** Writing `a = p^i a'` with `a'` prime to `p` (the `p`-free part
   `pfreePart`), the ratio correlation at `p^k` sorts into cosets,
   `R_q(p^k) = Σ_{a' p-free} Σ_i q(p^i a') q(p^{i+k} a')` (`ratioCorr_prime_pow_eq_sum_cosets`).
2. **Toeplitz forms.** The ratio part of the tower of `p` is `log p` times a sum over cosets of
   one-sided Toeplitz forms with kernel `p^{−k/2}` (`cosetToeplitz`, `towerRatioPart_eq_sum_cosets`).
3. **The coset law.** The odd prime side of a tower is
   `log p · (2 Σ_{a'} Toeplitz_p(q|_{a'}) − (S_p(q)² − q(1)²))` (`towerOddPrimeSide_eq`): the
   difference correlations are coset-Toeplitz, the sum correlations one Hankel square on the unit
   coset. This is the orientation-sensitive decomposition of §7.2 in its exact finite form.

### 3.3 The Nyquist rank bound (`TheNyquistRankBound`)

1. **Rank–nullity Riemann–Roch.** `h0 A + rank A = dim` (`h0_add_rank`), sections exist
   beyond the nodes: `h0 A ≥ dim − #nodes` (`card_sub_card_le_h0`), and with the obstruction
   count `h1 A = #nodes − rank A` the Euler characteristic form `h⁰ − h¹ = dim − #nodes` holds
   (`h0_sub_h1`); interpolation at every node is possible iff `h¹ = 0` (`h1_eq_zero_iff`).
2. **Rank–trace law.** For a frame bound `K`, `Σ ‖A_ij‖² ≤ K · rank A`
   (`frobeniusMass_le_rank_mul`): the Gram `AᴴA` is Hermitian positive semidefinite, its trace is
   the Frobenius mass (`re_trace_conjTranspose_mul_self`), each eigenvalue is a Rayleigh quotient
   of the frame (`eigenvalues_le_of_hasFrameBound`), the rank counts the nonzero eigenvalues.
3. **Nyquist bound.** `h0 A ≤ dim − (Frobenius mass)/K` (`h0_le_nyquist`); at full degrees of
   freedom, `K · dim ≤ Frobenius mass`, there are no sections (`h0_eq_zero_of_frobeniusMass_ge`),
   and dually at `K · #nodes ≤ Frobenius mass` every node datum is interpolated
   (`h1_eq_zero_of_frobeniusMass_ge`).
4. **Dirichlet polynomials at separated heights.** The sampling matrix has unit-modulus entries
   (`frobeniusMass_dirichletSampling`: mass `(R+1) N`), the large-values estimate is a frame bound
   (`hasFrameBound_dirichletSampling`: `K = (T + 4N(1 + log N))(δ⁻¹ + 2 log N)`), and so the
   Dirichlet polynomials of length `N ≥ 2` vanishing at `R + 1` heights `δ`-separated in `[0, T]`
   form a space of dimension at most `N − (R+1) N / K` (`h0_dirichletSampling_le`).

Below the diagonal `N ≪ T` the reading is essentially injective; above it, hiding is possible.
This is the square-root threshold of the aperture as a sampling threshold.

### 3.4 The even flip is read at the prime two (`TheEvenFlipIsReadAtThePrimeTwo`)

1. **The flip is an orientation.** Three faces (`evenFlip_apply`), involution
   (`evenFlip_evenFlip`), stays four-free (`evenFlip_fourFree`), stays in the damped class with
   constant `2K` (`dampedClass_evenFlip`).
2. **Reading at `2`.** `M(c♭) − M(c) = 2 log 2 · W_c(2)` (`firstPronicMoment_evenFlip_sub`):
   the von Mangoldt pairing sees even moduli only at powers of two
   (`eq_two_pow_of_even_of_isPrimePow`), and a four-free weight has `W_c(2^a) = 0` for `a ≥ 2`
   (`weightRamanujanCoeff_eq_zero_of_four_dvd`).
3. **Faithfulness and blindness.** The first pronic moment separates `c` from `c♭` iff
   `W_c(2) ≠ 0` (`firstPronicMoment_separates_evenFlip_iff`,
   `orientationFaithful_firstPronicMoment`); the sign of `W_c(2)` is a ℤ/2 invariant of the class
   that the flip reverses (`sign_weightRamanujanCoeff_evenFlip_two`); the amplitude reading is
   blind to the flip (`invisible_amplitude_evenFlip`).
4. **The parity floor for readings.** At every `0 < ε ≤ ½` the amplitude reading does not resolve
   payment on the four-free damped weights (`not_resolves_amplitude_receiverBounded`): the Fermi
   weight and its flip have the same amplitudes, one paid and one not.

### 3.5 Oriented readings (`OrientedReadings`)

1. **Closure law of blindness.** Blind readings stay blind under post-processing
   (`Invisible.comp`), pairing (`Invisible.join`), families of any cardinality (`Invisible.pi`)
   and coarsening (`Invisible.of_refines`).
2. **Blind readings resolve only invariant predicates**
   (`forall_iff_of_resolves_of_invisible`, `not_resolves_of_invisible_of_flips`).
3. **Resolving a flipping predicate forces faithfulness**
   (`orientationFaithful_of_resolves_of_flips`).
4. **Orientation classes.** A blind reading is constant on classes
   (`eq_of_mem_orientationClass_of_invisible`); classes of flipped data coincide
   (`orientationClass_flip`).

### 3.6 The critical Wiener monoid (`TheCriticalWienerMonoid`)

1. **Closure with submultiplicative norm.** `CriticalWiener a → CriticalWiener b →
   CriticalWiener (a ⋆ b)` (`criticalWiener_dirichletConv`) and
   `Σ |a ⋆ b| q^{−1/2} ≤ (Σ |a| q^{−1/2})(Σ |b| q^{−1/2})` (`tsum_abs_dirichletConv_le`), through
   the L-series of the absolute kernels at `½` (`lSeries_absWeight`, `convolution_absWeight`).
2. **Unit and associativity.** `δ₁` is critical Wiener and a unit away from `0`
   (`criticalWiener_unitKernel`, `dirichletConv_unitKernel`); convolution is associative
   (`dirichletConv_assoc`, via `dirichletConv_eq_toArithmeticFunction`).
3. **Orbits.** The paid class is a union of orbits of the monoid (`receiverBounded_orbit`).

### 3.6′ Local factors are the units of the Wiener monoid (`LocalFactorsAreTheUnitsOfTheWienerMonoid`)

1. **Inverse towers.** The local factor `δ₁ − a δ_p` has Dirichlet inverse `Σ_k a^k δ_{p^k}` away
   from `0` (`dirichletConv_localFactor_inverse`), and the tower is critical Wiener iff
   `|a| < √p` (`criticalWiener_localFactorInverse_iff`).
2. **Commutativity and uniqueness.** Convolution is commutative (`dirichletConv_comm`) and inverses
   are unique away from `0` (`inverse_unique`).
3. **The unit law.** `δ₁ − a δ_p` is a unit of the critical Wiener monoid iff `|a| < √p`
   (`isWienerUnit_localFactor_iff`): the local factor law of Trans-Horizon Incidence Mechanics is
   invertibility in the stability monoid, and `√p` is where the inverse tower leaves the class.

### 3.7 The damping flow preserves orientation (`TheDampingFlowPreservesOrientation`)

`C_η (Σ_d a_d v_d) = Σ_d a_d d^{−η} v_d` (`centeredOperator_residueCombination`); the sign of every
coefficient is preserved (`sign_coeff_centeredOperator`), nonvanishing is preserved
(`coeff_centeredOperator_ne_zero_iff`), and the flow composes (`centeredOperator_residueCombination_twice`).

### 3.8 The width dictionary and pole-subtracted forcing (`TheWidthDictionary`, `PoleSubtractionAndTheForcingSignDictionary`)

`widthDictionary_tfae`: RH, the Hodge index of the scaling surface, the existence of an
effectivity, one positive square in every intersection Gram, cofinal admission of the damped
receiver, arbitrarily small pronic prefix energy, the linear Chebyshev band, and the absence of a
finite-radius refutation of full Weil positivity are equivalent. Pairs of units are stated
directly (`one_positive_square_iff_cofinal_budget`, `exists_effectivity_iff_meanSquare_band`).
`castelnuovoSeveriMetrologyAndWidthDictionary_tfae` extends this dictionary with the degree-filtered
Hodge defect (`∀ a, hodgeDefectAt zetaZeroConfig a = 0`), the even and odd reflection-sector Hodge
defects (`∀ a, sectorHodgeDefectAt zetaZeroConfig s a = 0`), and the Castelnuovo–Severi defect-floor
growth rates (`oddDefectFloorRate = 0`, `fullDefectFloorRate = 0`; direct bridges
`oddDefectFloorRate_eq_zero_iff_cofinal_budget`, `oddDefectFloorRate_eq_zero_iff_meanSquare_band`,
`sectorHodgeDefectAt_eq_zero_iff_one_positive_square`). At general width `σ ≥ 0`,
`gradedWidthDictionary_tfae` equates `zetaZeroWidth ≤ σ`, `oddDefectFloorRate ≤ σ`,
`fullDefectFloorRate ≤ σ`, and the `H¹`-normalised exponential Castelnuovo–Severi defect floors on
`scalingSubsurface (oddRealTestsAt r)` and `scalingSubsurface (realTestsAt r)`.

`forcingSignAndWidthDictionary_tfae` (`PoleSubtractionAndTheForcingSignDictionary`): unites the
eight width units with the pole-subtracted forcing units of `WhichArithmeticDataForceTheSign`
(forward light-cone Bézout, open light-cone Bézout, odd-sector Hodge index, coupled odd-cone
Bézout, all-aperture two-pole Chebyshev defect payment, and subexponential odd-defect floor), and
proves that a one-sided pole-subtracted prime window ceiling `windowCeiling L ≤ e^{L/2} + B(1 + L)`
forces every unit in the dictionary (`scalingSurface_hodgeIndex_of_windowCeiling_le`,
`positiveCone_bezout_of_windowCeiling_le`, `cofinal_budget_of_windowCeiling_le`). On curve data,
the unsubtracted reading recording `(q, g)`, trace integrality, and `∀ k ≥ 1, N_k ≥ 0` cannot
resolve `CurveDatum.Unitary` (`not_resolves_unsubtractedCurveReading_unitary`), whereas the lag-1
Frobenius reflection defect reading resolves it on every `CurveDatum ι`
(`resolves_frobReflectionReading_unitary`, `orientationFaithful_frobReflectionReading_of_flips`).

### 3.9 Complete-period quadratic forms are orientation-blind (`CompletePeriodQuadraticFormsAreOrientationBlind`)

The complete-period lag-covariance reading `completePeriodLagReading N c = (finiteHarmonicSum N c, fun h => TwoLagSieve.periodCovariance N c h)` refines all 12 complete-period quadratic forms of the sieve theory (`sieveVariance`, `bezoutCoprimeQuadraticForm`, `sieveSuccessorCovariance`, `sieveSuccessorReserve`, `sievePoincareExcess`, `successorPhaseLoss`, `sievePrimitiveEnergy`, `sieveVarianceAboveParity`, `selbergTotientDiagonalForm`, `franelGcdQuadraticForm`, `tupleVariance N · H`, and `SieveMoments.translatedMoment N · (v : Fin 2 → ℕ)`) (`refines_completePeriodLagReading_*`). Its shadow at `c₁` (`N ≥ 1`) is the exact `(ℤ/2ℤ)^{N-1}` sign-character orbit of `c₁` on `Icc 1 N` (`mem_shadow_completePeriodLagReading_iff_signOrbit`). Consequently, every mean-preserving sign character `ε` (`ε 1 = 1`, `ε(q)² = 1`) — including `evenFlipRow N` and `singleModeSignFlip q₀` (`q₀ ≥ 2`) — is invisible to `completePeriodLagReading N` and to every complete-period quadratic form (`invisible_completePeriodLagReading_scaledSelbergRow`, `invisible_completePeriodLagReading_evenFlipRow`), and for `N ≥ 3` the reading fails to resolve `sieveSeq N c k` at every `k ∈ ℕ`, the sign `0 ≤ vonMangoldtReadout N c`, and the first-cell defect sign `sieveRenormalizedPrefixDefect N 1 c < 0`, witnessed by `primePairPlusWeight N` and `primePairMinusWeight N` (`not_resolves_completePeriodLagReading_sieveSeq`, `not_resolves_completePeriodLagReading_vonMangoldtReadout_nonneg`, `not_resolves_completePeriodLagReading_renormalizedPrefixDefect_neg`).

---

## 4. Mechanisms

- **Switching as gauge.** Every statement about a signed form is first checked for switching
  covariance; invariants of the class (index, mass, ground energy) are the only admissible ones.
- **Sign vectors as trial profiles.** The ground energy is bounded by evaluating the Dirichlet form
  at normalized sign vectors, where it counts misaligned mass exactly.
- **Propagation along walks.** Zero Dirichlet energy forces `|x_i| = |x_j|` across every overlap;
  connectivity turns this into nowhere-vanishing and hence into a switching.
- **Tower locality and generating polynomials.** Product pairs of a prime power lie in one tower;
  the Cauchy product of the tower sequence is the square of a polynomial evaluated at `1`.
- **Gram spectral reading.** Frobenius mass = trace, frame bound ≥ every eigenvalue, rank = number
  of nonzero eigenvalues; three facts give the rank–trace law.
- **Single-point tsums.** The difference of two von Mangoldt pairings across the flip is supported
  at one modulus; the sum is evaluated by `tsum_eq_single`.
- **Absolute kernels as L-series.** Closure of the critical Wiener class is the convolution theorem
  for absolutely convergent L-series at `½`, read back on the real line.
- **Equivalence assembly.** The dictionary is `tfae_finish` over the corpus's exact equivalences.

---

## 5. Traps

| trap | correct statement |
|---|---|
| The frustration index is a property of the coupling. | It is a property of the switching class: `frustrationIndex (s·c) = frustrationIndex c`. |
| Ground energy zero means balance. | Only on connected patterns, or for nowhere-vanishing profiles; an unbalanced component disjoint from the support is invisible. |
| `D_c(s) = 0` for the minimizing switching of an unbalanced form. | `D_c(s) = 4 ν_w(c) > 0`; the ground energy is at most `4 ν_w / n`, not zero. |
| The product correlation at a prime power is a cross-tower quantity. | It is tower-local, and its weighted sum over the tower is one square minus `q(1)²`. |
| The frustrating part of the odd prime side is negative. | For profiles vanishing at `1` it is a sum of squares, subtracted; the odd prime side is at most twice its ratio part. |
| `h⁰` is a count of nodes. | It is the dimension of the annihilated test space; nodes enter through the Frobenius mass and the frame bound. |
| The Nyquist bound is injectivity. | It is a quantitative dimension bound; injectivity is its limit when `(R+1)/K → 1`, which the large-values frame bound reaches only below the diagonal. |
| The even flip changes the amplitudes. | It twists them by `σ₂ = ±1`; every amplitude reading is blind to it. |
| The first pronic moment reads the flip everywhere. | It reads it exactly through `W_c(2)`: on weights with `W_c(2) = 0` it is blind too. |
| Payment is a function of amplitudes. | Not at any `ε ≤ ½` on four-free damped weights (`not_resolves_amplitude_receiverBounded`). |
| The critical Wiener kernels form a group. | They form a monoid; inverses need Wiener's lemma for Dirichlet series, which is not proved here. |
| `δ₁` is a two-sided unit on all of `ℕ`. | Only away from `0`; convolution vanishes at `0`. |
| The damping flow changes signs. | On residue combinations it scales coefficients by `d^{−η} > 0`; the open question is magnitude, not orientation. |
| A new unit is progress. | The dictionary is an equivalence; progress is a bound in a unit, with its input class named. |

**Lean conventions.** Capstones take data only; universal statements over all weights or forms are
`∀`; no RH-equivalent appears as a hypothesis; analytic inputs (the large-values estimate, the
first pronic moment identity, the parity pair of the Fermi weight) are proved corpus theorems.

---

## 6. Questions the programme answers and the tools it builds

### 6.1 Questions

1. **What is the integer behind the sign of a signed form?** The frustration index of its
   switching class; zero iff balanced; its mass bounds the ground energy from above, and on
   connected patterns the ground energy vanishes iff the index does.
2. **What is the frustrating part of the odd Weil prime side made of?** One rank-one square per
   prime tower, `log p · (S_p(q)² − q(1)²)`.
3. **How many tests can a reading annihilate?** At most `dim − (degrees of freedom)/(frame bound)`;
   for Dirichlet polynomials at separated heights the frame bound is the large-values estimate.
4. **Which datum reads the even flip?** `W_c(2)`, through the first pronic moment; no amplitude
   reading does, and no amplitude reading resolves payment at or below half damping.
5. **What is the stability group of "paid"?** The critical Wiener monoid, under which the paid
   class is a union of orbits; among local factors its units are exactly those with `|a| < √p`.
7. **Where is the odd Weil ledger frustrated?** Nowhere on the lattice at any aperture, and at
   the prime triangle between lattice points: frustration is a continuum phenomenon, bounded in
   mass by the prime-sum charge.
8. **How is the ratio part oriented?** Coset by coset: it is a sum of one-sided Toeplitz forms
   over the `p`-free cosets, against one Hankel square on the unit coset.
6. **Is RH the same statement in every unit?** Yes: `widthDictionary_tfae`.

### 6.2 Tools

Built and reusable:

- the *signed Dirichlet form*, the *misaligned mass* and the *frustration index* with their
  switching covariance;
- the *walk propagation lemma* for zero-energy profiles;
- *tower locality* and the *Cauchy-product-by-polynomial* lemma;
- the *rank–trace law* and the *Nyquist bound* for readings;
- the *Dirichlet sampling matrix* with its Frobenius mass and frame bound;
- the *three-face formula* for the even flip and its damped-class bound;
- the *absolute-kernel L-series* bridge for Dirichlet convolutions;
- the *orientation calculus* on readings (flip, faithfulness, closure of blindness);
- the *tower comparison* and the *prime-sum charge bound* for the odd ledger;
- the *coset decomposition* of dilation correlations through the `p`-free part;
- the *inverse tower* and the *uniqueness of inverses* in the Wiener monoid;
- the *Euler characteristic* `h⁰ − h¹` of a reading at nodes.

To be built (§7): a section functor beyond the finite-dimensional skeleton; an orientation-faithful
norm on damped weights; the aperture-derivative identity.

---

## 7. Open problems and research topics

1. **The frustration of the odd Weil ledger off the lattice.** On the lattice the index is `0`
   at every aperture (§3.1″) and the prime triangle has index `2` (§3.1′); the mass is bounded by
   the prime-sum charge. Open: the frustration index and mass of the continuum ledger on dense
   position sets in `[0, A]` as `A → ∞`, and the relation of `4 ν_w / n` to the ground energy
   `μ(A)` and the contact aperture `A* ≥ 3/10`.
2. **Beyond the coset law.** The odd prime side of a tower is `2 Σ_{a'} Toeplitz − Hankel`
   (§3.2″). Open: the class of profiles on which the coset Toeplitz forms dominate the unit-coset
   square once the archimedean odd kernel is added, and the selectivity of that class against the
   shifted pair `ζ(s−a)ζ(s+a)`.
3. **Nyquist–Riemann–Roch beyond rank–nullity.** Replace the finite-dimensional test space by
   band-limited tests on an aperture, the node set by the prime-power nodes, and the frame bound
   by a Landau-type density theorem; identify the `h¹` term and the Chebyshev defect
   `E(s) = e^s + s − 1 − ψ(e^s)` as its correction.
4. **An orientation-faithful norm.** A Banach norm on four-free damped weights in which the
   companion class is continuous and the receiver is bounded; the first pronic moment and the
   logarithmic moments are the candidates for its coordinates.
5. **Inverses in the critical Wiener monoid.** Local factors are units iff `|a| < √p` (§3.6′).
   Open: Wiener's lemma for Dirichlet series on `Re s ≥ ½` (invertibility of a general kernel iff
   its series has no zero on `Re s ≥ ½`), and whether units preserve the unpaid class as well.
6. **Transport in aperture.** An aperture-derivative identity for `μ(A)` with a sign-definite
   jump term, compatible with the doubly exponential ceiling.
7. **The Nyquist bound at the diagonal.** Sharpen the frame bound to `T + O(N)` without the
   logarithm at `1`-separated heights, and read the resulting injectivity threshold against the
   square-root threshold of the aperture.
8. **The effectivity cone from sections.** With `h⁰` from problem 3, define `E = {x : h⁰(x) ≥ 1}`
   and prove or refute the Bézout axiom for it. It must give the curve Hodge index over `𝔽_q`
   and fail on the golden datum; locate the property of the ring `ℤ` that it uses.
9. **The index theorem of the receiver.** The pole law of the receiver reads the order of a pole,
   and the Hodge defect is the number of right zeros. Prove that the order read by the receiver is
   a count of sections, and compute the Euler characteristic of the node divisor from the ledger.
10. **The trichotomy of readings.** Prove that every orientation-faithful reading of the critical
    form crosses the Nyquist aperture, reads a magnitude, or adds data of a third kind (mass,
    dilution), and compute the precision cost of each branch. This is the Scale-Signed Incidence
    Criticality trichotomy stated as a theorem about readings.
11. **The width functor.** Construct a functor from receivers to the width line through which every
    oriented invariant factors. The dictionary would become a theorem about a category of
    receivers, and the battery of §8 a list of its non-objects.

---

## 8. Success criteria and contributions

A contribution to the programme is a Lean theorem, unconditional, about an oriented object, that
does one of the following:

- attaches an integer- or sign-valued invariant to an orientation class and proves its
  covariance under the gauge (switching, flip, refinement);
- proves that a named reading is faithful or blind for a named flip, and if blind, which
  predicates it can still resolve;
- computes a count (sections, frustration, rank) and relates it to an energy or a receiver;
- places a receiver in the width dictionary by an exact equivalence, or proves that two units
  agree.

**The selectivity battery.** A theorem that claims to move the width must pass every applicable
test. Each test is a proved corpus fact about a model that violates RH, or a proved limit of a
class of methods.

| test | content | corpus source |
|---|---|---|
| golden datum | fail for the Beurling system `P = 1 − 5X + 5X²`: integral Witt vector, functional equation, positive prime counts, impure | `witt_integral_not_pure`, `goldenDatum_beurling_not_pure` |
| shifted pair | fail for `ζ(s − a)ζ(s + a)`; the temperedness gate `ε(L) = 1/(2 + log L)` is the one proved instance | `not_summable_shiftedPairVonMangoldt_windowDilationExponent` |
| parity twins | separate `μ` from its positive twin, each real character from its twin, Liouville from `κd^{−½}`, the Fermi row from its even flip | `char_parityPair`, `fermi_evenFlip_parityPair` |
| deformation | not survive one Euler-factor deformation, the theta-power family or the `k + t k^{(4m)}` perturbations | killed-routes ledger |
| nodes | fatal at `log 4`, free at `log 6`; every prime power needed | `zeroPoleBlindPositiveOn_iff` |
| unit | a cofinal bound in a width unit; one interior point only translates zeros | `receiverDampingRate_eq_zetaZeroAbscissa_sub_half` |
| ceiling | every positive aperture floor decays at least like `exp(−πe^{2(A−2)})` | `exists_le_floorLoss_of_floor` |
| Ω-laws | never assert `ψ(x) − x = O(√x)` or `M(x) = O(√x)` | Littlewood |
| finite data | rest on no finite computation; every bounded reading admits off-line extensions | `resolutionLimit_width_aperturePositivity` |
| rate | use the prime rate in full; no Hardy weight exists | `riemannHypothesis_iff_isLeast_primeRate` |
| function field | reproduce the exact cancellation over `𝔽_q[T]` and the curve Hodge index | `curve_hodgeIndex_tfae` |
| integrality | land on exactly one positive square | `riemannHypothesis_iff_one_positive_square` |
| no premise | no RH-equivalent as a hypothesis, no `Prop` stand-in, axioms audited | proof-integrity rules |
| precision | excluding depth `β` at scale `L` costs precision `β²L³`; a cheaper certificate is wrong | `theDeficitBudgetLaw` |

The programme succeeds when one of its invariants yields a bound in a width unit that is not a
reformulation: a frustration-index bound on the odd ledger at unbounded aperture, a section count
beyond the diagonal that is selective, or a faithful reading that is also an estimate.

**What would retire it.** The field is retired if the section count of problem 3 cannot produce,
at the diagonal, a statement strictly stronger than the mean value theorem that passes the golden
and shifted-pair tests: if the only sections it finds are those the large sieve already counts.
The risk is that "section" turns out to relabel "Dirichlet polynomial on a window". Then the
contribution of the field is its dictionary and its battery, not a mechanism.

---

## 9. Principles

- **Counts before estimates.** Invariants are integers or semicontinuous; bounds are corollaries.
- **Gauge first.** Every statement is checked for covariance under the flip before it is proved.
- **Name the reading.** A theorem says which reading it uses and whether that reading is faithful.
- **Global payment.** Rank-one charges are paid globally; local certificates locate frustration.
- **Unit hygiene.** Every result is tagged with its unit; a reformulation that changes only the
  unit is recorded as a dictionary entry, not as progress.
- **Selectivity as a theorem.** A positivity claim is accompanied by its failure on the battery.

---

## Source entry points

- `OrientedReadings` — flips, faithfulness, the closure law of blindness.
- `FrustrationIndexControlsTheGroundEnergy` — switching classes, frustration index and mass,
  signed Dirichlet form, ground energy, the odd Weil ledger.
- `TheFrustrationIndexOfThePrimeTriangle` — mirror pairs, three-point bound, the prime triangle.
- `TheLatticeOddLedgerIsBalanced` — tower comparison, balance on the lattice, the prime-sum charge.
- `TheFrustrationOfATowerIsRankOne` — lattice correlations, tower locality, the rank-one law,
  the odd prime side.
- `PrimePowerSumsRegroupByTowers` — regrouping by least prime factor; the global product part.
- `TheRatioPartDecomposesOverCosets` — the `p`-free part, coset Toeplitz forms, the coset law.
- `TheNyquistRankBound` — sections, rank–trace law, Nyquist bound, Dirichlet sampling.
- `TheEvenFlipIsReadAtThePrimeTwo` — the even flip as an orientation, the reading at `2`, the
  parity floor for readings.
- `TheCriticalWienerMonoid` — closure, submultiplicative norm, unit, associativity, orbits.
- `LocalFactorsAreTheUnitsOfTheWienerMonoid` — inverse towers, uniqueness, the unit law.
- `TheDampingFlowPreservesOrientation` — transport of residue combinations.
- `TheWidthDictionary` — the equivalences in one theorem.
- `PoleSubtractionAndTheForcingSignDictionary` — faithfulness of the Rosati reflection reading vs.
  blindness of unsubtracted positivity (`resolves_frobReflectionReading_unitary`,
  `not_resolves_unsubtractedCurveReading_unitary`), the 14-unit master dictionary
  `forcingSignAndWidthDictionary_tfae`, and one-sided pole-subtracted window ceiling forcing.
