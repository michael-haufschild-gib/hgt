# Renormalized Arithmetic Potential Theory of the Characteristic Circle (RAPT)

**One question.** Over `𝔽_q` Weil's proof of the Riemann hypothesis uses one pairing that is
positive, Frobenius equivariant and finite on the diagonal. Over `ℤ` the corpus has these pieces on
separate carriers: a potential theory of the zero divisor (AES), an intersection theory of the
characteristic circle with an anomalous diagonal (AIT), and a renormalization theory whose survival
cones decide which positivity passes a limit (RBG). Every pairing of the explicit formula is a
regularized self-energy, and the two places of `ℚ` regularize the same diagonal. **Which regulator,
which counterterm and which coupling of the prime place, the archimedean place and the arithmetic
point keep positivity and Hecke equivariance together through the limit, and which provably cannot?**

RAPT is the theory of the **renormalization data** of the explicit formula: regulators, the
counterterms they produce, the rank and survival cone of those counterterms, the anomaly of the
Hecke correspondences, and the coupling of the places that must pay the divergence. Its organizing
sentence:

> *The rank of a counterterm is a property of the regulator, not of the pairing. The Abel radius
> renormalizes the self-energy of every torsion point and leaves nothing. The horizon — the
> regulator of Weil's form — has as counterterm the tensor product of the two places'
> counterterms: the identity on the torsion orbits, weighted by their sizes, times the polar
> projection on log-scale profiles. This counterterm is Hecke covariant: the degree of `[p]`,
> additive anomaly `log p` under the radius, becomes the scaling `1/p` of the orbit densities and
> cancels exactly. Coupling never lowers the prime counterterm's rank, and the archimedean place
> pays exactly one direction, the arithmetic point. Covariance forces a scalar counterterm. The
> scalar the archimedean place must supply at atomic resolution `N` is `log N + O(1)`, with
> constant one: the anomaly of `[N]`. The anomalous torsion renormalization costs at least half a
> logarithm more. What remains after the polar counterterm is the scalar `−2γ`: the constant term
> of `−ζ′/ζ` at its pole, once for each Hecke direction. Polar matching selects the Euler gauge: the
> Liouville twin diverges with the opposite sign.*

Namespace `GaloisForLFunctions.RenormalizedArithmeticPotentialTheory`; umbrella
`RenormalizedArithmeticPotentialTheory.lean`. Everything is unconditional; RH and its partial forms
appear only inside equivalences.

---

## 1. Place in the research

The frontier ([obstacles summary](../../../docs/reports/review-2710/obstacles-summary.md), §4)
locates, ingredient by ingredient, what of Weil's argument over `𝔽_q` exists over `ℤ`. A positive
Hermitian structure with Hecke similitudes exists after regularization. Local Hodge index holds at
every prime. Tensor amplification exists with a non-scaling loss. Missing are a finite
self-intersection of the diagonal, archimedean payment of the local-to-global divergence, and
stability of the computed equilibrium. All three are statements about one object: the
**counterterm** the diagonal requires, and the place that pays it.

RAPT owns that object. Its core is Q2 of the report, coupled renormalization of the two places
(B3.25, B3.26, W11, W12). It also takes up the renormalization faces of Q1 (what bounds the field)
and Q3 (the gauge charge of a positive form). In wall terms it is Wall 14 (the diagonal), face
1.16 (polarization) and face 3.23 (positivity and equivariance in one form).

| Programme | What RAPT takes | What RAPT adds |
|---|---|---|
| [RenormalizedBiarithmeticGeometry](../RenormalizedBiarithmeticGeometry/README.md) | regularized families, survival cones, scheme independence, the torsion germ (identity counterterm), the lattice germ (polar hyperplane), periodic germs and Ramanujan modes, the pole node | the **coupled** survival law; the joint germ of the two places and its matched rank-one coupling |
| [ArithmeticIntersectionTheory](../ArithmeticIntersectionTheory/README.md) | orbit intersections, the different `c(n)`, the Hecke cocycle `β`, the regulator anomaly, the spacing regulator, Hecke invariance of `P` | covariance as a constraint on counterterms; the price of the anomaly; the horizon regulator and its tensor law |
| [ArithmeticElectrostatics](../ArithmeticElectrostatics/README.md) | the torsion pairing and `RenormalizesAt`, the atomic Weil form, the arithmetic point, the stability law at atomic resolution, gauge invisibility and margins, alignment at zero ordinates | the exact constants `log N + O(1)` (covariant) and `≥ (3/2) log N` (torsion); the spectral ends `± log N` |
| [ArithmeticEffectivityTheory](../ArithmeticEffectivityTheory/README.md) | torsion orbits `O_n`, `I(m, n)`, Ramanujan sums, Weil's prime kernel `P` as a renormalized torsion energy | — |
| [ArithmeticPolarization](../ArithmeticPolarization/README.md), [ConjugateDiagonalGeometry](../ConjugateDiagonalGeometry/README.md) | `W`, `D`, `Δ`, the Hecke defect | the place of the prime form among regularized families |
| [ArithmeticCastelnuovoSeveri](../ArithmeticCastelnuovoSeveri/README.md), [ArithmeticOrientationGeometry](../ArithmeticOrientationGeometry/README.md) | the scaling surface, Hodge index, `𝔽_q` calibration, the pole plane | the renormalized reading of `Δ² = 2 − 2g` |
| [BiarithmeticGaugeGeometry](../BiarithmeticGaugeGeometry/README.md) | the gauge torus, square-class blindness, sign twins | gauge behaviour of the matching between places |
| `RHTower` | Mertens' first theorem | — |

RAPT does not re-prove what these programmes own; it imports them and proves the laws that join
them.

---

## 2. Why

**Weil's diagonal over `𝔽_q`.** On `C × C` the diagonal is a curve and adjunction gives
`Δ² = 2 − 2g`, a finite number. The tensor-power argument works because this loss does not grow
with the power, and the Hodge index theorem gives the sign on the primitive part.

**Over `ℤ` the diagonal is a divergence.** Every pairing of the explicit formula is singular on the
diagonal:

* at the **prime place** the charges are torsion orbits `O_n` on the circle, with Green function
  `−log |1 − z w̄|`; the Abel radius `r < 1` makes the self-energy of a point finite,
  `log(1/(1 − r))`;
* at the **archimedean place** the charges are atoms at `log n` on the line; a width `ε` makes the
  self-energy of an atom finite, `log(1/ε) + O(1)`;
* the **arithmetic point** `z = 1`, the orbit `O_1`, is fixed by every power map; the torsion
  divergence and the archimedean divergence meet there (the pole).

Positivity lives before the limit, since Abel energies are Gram matrices. Equivariance lives after
it, since Weil's prime kernel is Hecke invariant. RBG proved that positivity passes the limit
exactly on the null cone of the counterterm, and that the Abel torsion germ has the identity as
counterterm, so nothing survives. AIT proved that the counterterm is not Hecke covariant: the
regulator anomaly `log t` of `[t]`, minus the tame different. The report's central conjecture asks
for an **admissible coupling** of the places: low-rank counterterm, covariant finite part, and a
survival cone containing the degree-zero cycles.

**What a theory of renormalization data has to decide, and what it decides.**

1. *Can coupling the places lower the prime counterterm?* No. A positive coupled family whose prime
   block keeps the torsion germ has counterterm rank at least the number of orders. The torsion
   directions that survive span at most the rank of the partner's counterterm. The archimedean
   germ has rank one and pays exactly one direction, the arithmetic point.
2. *Is the rank of the counterterm intrinsic?* No; it belongs to the regulator. At the
   **horizon** (orders `≤ N`, Weil's own regularization) the prime form has no diagonal. Its
   divergence is the tensor product of the identity on torsion orbits, weighted by their sizes, and
   the polar projection on log-scale profiles. These are exactly the counterterms of the Abel
   torsion germ and of the archimedean lattice germ. The survival cone is nontrivial: the
   class-wise polar hyperplane, the degree-zero part of each class.
3. *Can the anomaly be cancelled?* At the horizon it cancels exactly. `[p]` moves the class `j` to
   `j + 1`, whose orbit density is `1/p` of the previous one, while the polar functional scales by
   `p^{−1/2}`. The tensor counterterm, and with it the renormalized finite part, is invariant.
4. *What does covariance cost?* A Hecke-covariant renormalized prime form has a scalar diagonal. Its
   least positive counterterm on orders `≤ N` is `log N + O(1)`, the anomaly of `[N]` and the
   archimedean self-energy at the atomic spacing, both with constant one. Keeping the
   self-intersection, the anomalous torsion renormalization, costs at least `½ log N` more.
5. *What is the finite part?* On the polar hyperplane of uniform profiles, the renormalized prime
   form is the scalar `−2γ`, up to `o(1)` per unit mass. In Weil's form, where `P` enters with a
   minus sign, the renormalized prime place is positive there.
6. *Is the matching of the places gauge blind?* No. Each place's counterterm is gauge blind, but
   their matching is not: the prime place of `ζ` diverges along the archimedean polar direction
   with coefficient `+1`, the Liouville twin with coefficient `−1`.

These answers replace the report's central conjecture by a statement in which every divergence is
computed and matched, the prime finite part is computed, and only the finite parts of the
archimedean place and the pole are open (§9.1).

---

## 3. Objects and language

### 3.1 Carriers and charges

| Object | Definition | Lean |
|---|---|---|
| characteristic circle | `ℝ/ℤ`, torsion `μ_∞`, orbits `O_n`, the arithmetic point `O_1 = {1}` | `primitiveRoots` (AET) |
| orbit intersection | `I(m, n) = Σ_{ζ∈O_m, η∈O_n} log |ζ − η|`, `= φ(m) Λ(n/m)` for `m ∣ n` | `orbitIntersection` (AET) |
| self-intersection density | `c(n) = I(n, n)/φ(n) = log n − Σ_{p∣n} log p/(p − 1)` | `selfIntersection` (AIT) |
| Weil's prime kernel | `P(m, n) = Λ(n/m)(n/m)^{−1/2}` on `m ∣ n`, `m ≠ n`, symmetric | `weilPrimeKernel` (AET) |
| atomic prime form | `P_N(x) = Σ_{m,n ≤ N} x_m x_n P(m, n)` | `atomicWeilForm` (AES), `primeBilinear` |
| torsion pairing | `Σ y_m y_n I(m, n)` against the self-mass `Σ φ(n) y_n²` | `torsionPairing`, `selfMass`, `RenormalizesAt` (AES) |
| pole vector | `u_n = n^{−1/2}`; truncated `u^{(M)} = u 𝟙_{n ≤ M}` | `poleVector`, `truncPole` |
| polar functional | `ℓ(x) = Σ x_n n^{−1/2}`, one factor of Weil's pole term `(Σ x_n √n)(Σ x_n/√n)` | `polarFunctional` |
| step profile | `Σ_i c_i u^{(M_i)}`: the log-scale profile `g = Σ c_i 𝟙_{[0, a_i]}`, `M_i = N^{a_i}` | `stepProfile` |
| class pole vector | `w_j^{(M)} = u^{(M)} 𝟙_{v_p(n) = j}`: the valuation class `j`, dual to the orbit `O_{p^{J+1−j}}` of `μ_{p^{J+1}}` | `classPole` |
| class density | `δ_j = (1 − 1/p)/p^j = φ(p^{J+1−j})/p^{J+1}` | `classDensity`, `classDensity_eq_orbit` |
| class polar functional | `ℓ_j(x) = Σ_{v_p(n) = j} x_n n^{−1/2}` | `classPolar` |
| class-wise profile | `Σ_{j ≤ J} Σ_i c_{ji} w_j^{(M_i)}` | `classProfile` |
| Hecke shift | `(T_t x)(n) = x(n/t)` on multiples of `t` | `heckeShift` |
| tensor counterterm | `C(x) = Σ_{j ≤ J} δ_j^{−1} ℓ_j(x)²` | `tensorCounterterm` |
| Liouville pole vector | `λ(n) n^{−1/2}`, `λ = (−1)^Ω` | `liouvilleSign`, `liouvilleTrunc` |

### 3.2 Renormalization data

| Object | Definition | Lean |
|---|---|---|
| regularized family, counterterm, survival cone | `Q_s − σ_s B → A`; the null cone of `B` (RBG) | `quad`, `survivalCone` (RBG) |
| coupled counterterm | `[[A, C], [Cᵀ, D]]` on a prime block and a partner block | `coupled` |
| prime survival | projection of the survival space to the prime block | `primeSurvival` |
| matched coupling | `[[1, b vᵀ], [v bᵀ, v vᵀ]]` with `|b| = 1` | `primeSurvival_rankOne` |
| joint germ | torsion orbits with modes `c_n/√φ(n)` and archimedean nodes with the constant mode | `jointGerm`, `jointGram` |
| renormalized prime form | `−P + diag(h)`; **covariant** when invariant under every Hecke transport | `renormalizedPrimeForm` |
| covariant counterterm `κ_cov(N)` | least scalar `κ` with `P_N ≤ κ |x|²` | `covariantCounterterm_sandwich` |
| torsion counterterm `κ_tor(N)` | least `κ` renormalizing the torsion pairing on orders `≤ N` | `torsionCounterterm_ge` |
| horizon counterterm | the divergent part of `P_N` on a fixed profile space as `N → ∞` | `abs_atomicWeilForm_classProfile_sub_le` |

### 3.3 The regulators

| Regulator | Counterterm | Rank | Survival cone | Anomaly of `[t]` | Owner |
|---|---|---|---|---|---|
| Abel radius `r` | `φ(n) δ_{mn}` | number of orders | `{0}` | `log t − (tame different)` | RBG, AIT |
| spacing radius `e^{−ε/n}` | scalar | number of orders | `{0}` | tame different | AIT |
| horizon, uniform profiles | `ℓ(x)²` | `1` | `∫ g = 0` | — | RAPT RP5 |
| horizon, class-wise profiles | `Σ_j δ_j^{−1} ℓ_j(x)²` | number of classes | `ℓ_j(x) = 0` for all `j` | none for `[p]` | RAPT RP7, RP9 |

### 3.4 Words

*Regulator*, *counterterm*, *survival cone* as in RBG. A counterterm is *scalar*, *polar* (rank one,
along the polar functional), *orbital* (diagonal on the torsion orbits) or a *tensor* counterterm
(orbital on the arithmetic factor, polar on the profile factor). A renormalization is *covariant*
when its finite part is Hecke invariant, *anomalous* otherwise. A coupling *pays* a prime direction
when that direction lies in the prime survival. Two divergences are *matched* when their leading
terms agree in rank and constant; *anti-matched* when they agree with opposite sign. *Uniform*
profiles depend on `log n` only; *class-wise* profiles also on the `p`-adic valuation. The *arithmetic
factor* of a profile space is its decomposition by classes; the *profile factor* is its log-scale
shape.

Every theorem states its regulator, its counterterm with rank and survival cone, its anomaly, and
the place that pays.

---

## 4. Mechanisms

### A. Coupling the places

1. **The partner kernel is blind to the coupling** (`coupling_mulVec_eq_zero`, `rank_coupling_le`).
   In a positive coupled counterterm `D w = 0 ⇒ C w = 0`, so `rank C ≤ rank D`.
2. **Coupled survival** (`mem_survivalCone_coupled_iff`, `eq_zero_of_inl_mem_survivalCone`,
   `finrank_survival_le_card`, `card_le_rank_coupled`, `finrank_primeSurvival_le_rank`). Survival
   vectors solve `A u + C w = 0`, `Cᵀ u + D w = 0`. If the prime block is nondegenerate, no pure prime
   vector survives, the counterterm has rank `≥ #prime`, and the prime survival has dimension
   `≤ rank D`.
3. **Rank one pays one matched direction** (`coupling_eq_vecMulVec`, `dotProduct_self_le_one`,
   `primeSurvival_rankOne`). With `A = 1` and `D = v vᵀ`: `C = b vᵀ`, `|b| ≤ 1`, prime survival `ℝ b` if
   `|b| = 1`, `0` otherwise.
4. **The torsion germ** (`primeBlock_eq_smul_one`, `coupled_torsion_survival`,
   `coupled_lattice_primeSurvival_le_one`). In every positive symmetric coupled family whose prime
   block is the torsion germ, the prime block of the counterterm is `c · 1` with `c > 0` (scheme
   independence). Hence rank `≥ #S`, and coupled to the lattice germ at most one torsion direction
   survives.
5. **The archimedean place pays the arithmetic point** (`ramanujanMode_one`, `jointGram_eq`,
   `primeSurvival_jointGram`, `jointGerm_quad_nonneg`, `tendsto_jointGerm`, `jointGerm_survival`).
   Ramanujan orthogonality makes the joint counterterm the matched rank-one coupling with `b = e₁`.
   The mode of `O_n`, `n ≥ 2`, has mean zero, while `c_1 ≡ 1` is the archimedean mode itself.

### B. Covariance and the anomaly

6. **Covariance forces a scalar** (`renormalizedPrimeForm_transport`,
   `renormalizedPrimeForm_covariant_iff`, `heckeCovariant_iff_const`). Transport moves the diagonal
   from `h(n)` to `h(tn)`; covariance holds iff `h` is constant. A scalar counterterm has survival
   cone `{0}`, so covariance and survival exclude each other for diagonal counterterms.
7. **The exact rows** (`sum_up_eq`, `sum_down_eq`, `row_eq`). The Schur-weighted row of `P` at `m` on
   orders `≤ N` is `A(⌊N/m⌋) + log m`, with `A(y) = Σ_{t ≤ y} Λ(t)/t`.
8. **The covariant counterterm is `log N + O(1)`** (`row_le`, `row_ge`, `poleVector_eigen`,
   `atomicWeilForm_le_log`, `atomicWeilForm_poleVector_ge`, `log_sub_le_of_atomicWeilForm_le`,
   `covariantCounterterm_sandwich`). The pole vector is an approximate eigenvector with eigenvalue
   `log N`, coordinatewise.
9. **The anomaly costs half a logarithm** (`totient_mul_le`, `poleVector_mul_kernel_le`,
   `torsionPairing_torsionTest_ge`, `sum_log_div_ge`, `sum_tameDifferent_div_le`,
   `torsionCounterterm_ge`, `anomaly_cost`). By `φ(mt) ≤ t φ(m)` the torsion pairing dominates `P`
   entrywise. Its diagonal adds `Σ c(n)/n ≈ ½ log² N`, and the tame part averages to `O(H_N)`.

### C. The horizon

10. **Polarity on uniform profiles** (`primeBilinear_truncPole_eq`,
    `abs_primeBilinear_truncPole_sub_le`, `abs_atomicWeilForm_stepProfile_sub_le`,
    `abs_atomicWeilForm_stepProfile_le_of_polar`). The pole Gram is `H_M H_{M'} + O(H_{min})`. So
    `P_N = ℓ² + O(|c|-mass)` on step profiles, with no divergence on `ℓ = 0`.
11. **Orbital divergence** (`sum_dvd_vonMangoldt_div_le`, `sum_divisors_dvd_vonMangoldt_le`,
    `offClassRow_le`, `classRow_self_ge`, `primeBilinear_classPole_self_ge`,
    `primeBilinear_classPole_le`, `atomicWeilForm_classCombination_ge`,
    `horizonCounterterm_rank_unbounded`). Leaving a valuation class costs one prime power of `p`.
    Each class is an approximate eigenvector with eigenvalue `log M`, and classes decouple. So no
    counterterm of rank `≤ J` plus a bounded scalar renormalizes the prime place.
12. **The tensor law** (`classDensity_eq_orbit`, `abs_unitHarmonic_sub_le`, `abs_classMass_sub_le`,
    `primeBilinear_classPole_two_eq`, `abs_classGram_self_sub_le`, `classGram_cross_le`,
    `abs_atomicWeilForm_classProfile_sub_le`, `abs_atomicWeilForm_classProfile_le_of_polar`).
    On class-wise profiles the horizon counterterm is `Σ_j δ_j^{−1} ℓ_j²`, the class polar squares
    weighted by inverse orbit densities.

### D. Covariance at the horizon

13. **No anomaly** (`atomicWeilForm_heckeShift`, `heckeShift_classPole`, `classDensity_succ`,
    `classPolar_heckeShift_succ`, `classPolar_heckeShift_zero`, `tensorCounterterm_heckeShift`,
    `finitePart_heckeShift`). `P_{pN}(T_p x) = P_N(x)`; `T_p w_j^{(M)} = √p w_{j+1}^{(pM)}`;
    `ℓ_{j+1}(T_p x) = ℓ_j(x)/√p` and `δ_{j+1} = δ_j/p`. Hence `C(T_p x) = C(x)`, and the finite part
    `P − C` is invariant under `[p]`.

### E. The finite part

14. **Euler's constant** (`tendsto_mertensSum_sub_log`, `tendsto_harmonicSum_sub_log`, `roundoff_le`,
    `exists_abs_primeBilinear_truncPole_finitePart_le`,
    `exists_abs_atomicWeilForm_stepProfile_finitePart_le`,
    `exists_abs_atomicWeilForm_stepProfile_add_le_of_polar`). With `Σ_{t ≤ y} Λ(t)/t = log y − γ + o(1)`
    and `H_M = log M + γ + o(1)`, the pole Gram is `H_M H_{M'} − 2γ H_{min} + o(H_{min})`. Hence
    `P_N = ℓ² − 2γ |x|² + o(|c|-mass)` on step profiles.

### F. Gauge

15. **The twisted Mertens sum** (`sum_one_add_liouville_le`, `liouvilleMertensSum_le`,
    `neg_le_liouvilleMertensSum`). `Σ_{t ≤ y} λ(t)Λ(t)/t = −log y + O(1)`: the even prime powers are
    summable.
16. **Dirichlet's hyperbola identity** (`sum_divisors_div_swap`). The divisor part of a row averages
    to its Mertens part.
17. **The spectral ends** (`abs_atomicWeilForm_le`, `atomicWeilForm_liouvillePole_le`,
    `atomicWeilForm_spectrum_ends`). `|P_N| ≤ log N + O(1)`. The pole vector reaches the top and the
    Liouville pole vector the bottom, `−log N + O(1)`.
18. **The polar divergence flips** (`primeBilinear_liouvilleTrunc_eq`,
    `abs_primeBilinear_liouvilleTrunc_add_le`, `abs_liouvilleForm_stepProfile_add_le`). On uniform
    profiles `P(λx) = −ℓ(x)² + O(|c|-mass)`.

---

## 5. Pillar theorems

| Pillar | Statement | Lean |
|---|---|---|
| **RP1 Coupled survival** | partner-kernel inclusion; survival equations; rank `≥ #prime`; prime survival `≤ rank` of the partner; rank one pays one matched direction; for the torsion germ, coupled to any partner | `coupling_mulVec_eq_zero`, `card_le_rank_coupled`, `finrank_primeSurvival_le_rank`, `primeSurvival_rankOne`, `coupled_torsion_survival`, `coupled_lattice_primeSurvival_le_one` |
| **RP2 The archimedean place pays the arithmetic point** | joint counterterm `= [[1, e₁𝟙ᵀ], [𝟙e₁ᵀ, 𝟙𝟙ᵀ]]`; prime survival `ℝ e₁`; matched survival of the joint germ | `jointGram_eq`, `primeSurvival_jointGram`, `jointGerm_survival` |
| **RP3 The covariant counterterm is the anomaly** | covariance ⇔ constant diagonal; `log N − log 8 − 4 ≤ κ_cov(N) ≤ log N + log 4 + 4`; the pole vector is an approximate eigenvector | `renormalizedPrimeForm_covariant_iff`, `heckeCovariant_iff_const`, `poleVector_eigen`, `covariantCounterterm_sandwich` |
| **RP4 The anomaly costs half a logarithm** | `κ_tor(N) ≥ (3/2) log N − C`; `κ_tor − (log N + log 4 + 4) ≥ ½ log N − C` | `torsionCounterterm_ge`, `anomaly_cost` |
| **RP5 Horizon polarity** | on uniform step profiles `P_N = ℓ² + O(|c|-mass)`; no divergence on `ℓ = 0` | `abs_atomicWeilForm_stepProfile_sub_le`, `abs_atomicWeilForm_stepProfile_le_of_polar` |
| **RP6 Orbital divergence** | every class combination has `P ≥ (log M − C)|x|²`; the horizon counterterm has unbounded rank | `atomicWeilForm_classCombination_ge`, `horizonCounterterm_rank_unbounded` |
| **RP7 The tensor law** | `P_N = Σ_j δ_j^{−1} ℓ_j² + O(H_N |c|²)` on class-wise profiles; `δ_j = φ(p^{J+1−j})/p^{J+1}`; survival on the class-wise polar hyperplane | `abs_atomicWeilForm_classProfile_sub_le`, `classDensity_eq_orbit`, `abs_atomicWeilForm_classProfile_le_of_polar` |
| **RP8 Gauge** | spectral ends `±(log N + O(1))`; the Liouville twin diverges as `−ℓ²` on uniform profiles | `atomicWeilForm_spectrum_ends`, `abs_liouvilleForm_stepProfile_add_le` |
| **RP9 No anomaly at the horizon** | `[p]` shifts the classes and scales the orbit densities by the degree; the tensor counterterm and the finite part are invariant | `tensorCounterterm_heckeShift`, `finitePart_heckeShift`, `heckeShift_classPole` |
| **RP10 The finite part is Euler's constant** | `P_N = ℓ² − 2γ|x|² + o(|c|-mass)` on step profiles; `P_N = −2γ|x|² + o(·)` on the polar hyperplane | `exists_abs_atomicWeilForm_stepProfile_finitePart_le`, `exists_abs_atomicWeilForm_stepProfile_add_le_of_polar` |

---

## 6. The questions and their answers

The twelve questions of the report (§4.4), in RAPT's terms.

1. **What is the admissible metric of the characteristic circle?** Under the Abel radius there is
   none: coupling cannot lower the torsion counterterm's rank, and the archimedean place pays one
   direction, the arithmetic point (RP1, RP2). Under the horizon the prime counterterm is the tensor
   product of the torsion counterterm and the archimedean counterterm, with the class-wise polar
   hyperplane as survival cone (RP5–RP7). Its rank is the number of torsion orbits read, so
   condition (i) of the central conjecture (bounded rank on Hecke orbits) is false for every
   regulator in the corpus (RP1, RP6). What replaces it is the tensor law. Condition (ii) holds:
   the finite part is covariant under `[p]` (RP9). Condition (iii) is the sign of the finite part on
   the degree-zero classes. Its prime component is the positive scalar `+2γ` in Weil's form on
   uniform profiles (RP10); the archimedean and polar components are open (§9.1). *Answer:* the
   admissible regulator is the horizon, and its metric is the tensor counterterm.
2. **Does the anomaly cancel?** Yes, in two ways. Removing the self-intersection, as Weil's prime
   sum does, gives a covariant renormalized form. Covariance then forces a scalar counterterm,
   `log N + O(1)` with constant one (RP3), and keeping the anomaly costs at least `½ log N` (RP4).
   At the horizon the cocycle disappears altogether: the tensor counterterm and the finite part are
   exactly invariant under `[p]` (RP9). The degree of `[p]` scales the orbit densities instead of
   shifting the regulator. *Answer:* the anomaly is an artifact of the radius; at the horizon it
   cancels exactly, and the archimedean place pays the scalar `log N`.
3. **What bounds the field?** The field law is RH-strength (AES `TheFieldLawHasAThreshold`). The
   energy of a zero is `O(log γ)` (AES `TheEnergyOfAZeroIsLogarithmic`). RAPT locates the missing
   inequality as a bound on a *finite part*. Every divergence is computed and matched (RP3, RP7),
   and the prime finite part is the scalar `−2γ` (RP10), so neither a counterterm nor the prime
   place can supply it. *Answer:* located in the archimedean and polar finite parts; open.
4. **What bounds the moment of inertia?** Uniform bounds are strips and height averages are density
   estimates (AES `TheHeckeDefectIsTheMomentOfInertia`). *Answer:* located (AES).
5. **What is the Frobenius at infinity?** On the circle, conjugation is the power map of degree `−1`;
   on the divisor its realization by a correspondence is RH (AES). *Answer:* AES.
6. **What is the arithmetic point?** It is the unique orbit coupled to the archimedean germ (RP2).
   Its pole carries the polar divergence of the horizon: the pole vector is an approximate
   eigenvector at the top of the spectrum, with eigenvalue `log N` (RP3, RP5). In the orbital
   decomposition of `μ_{p^{J+1}}` it is dual to the residue `0`, the one-point orbit (RP7).
   *Answer:* the matched direction of the coupled renormalization.
7. **How does `σ_γ` localize beyond the conductor; are zero ordinates aligned with small primes?**
   The alignment law at zero ordinates and its higher moments are in AES
   (`LargeValuesAtZeroOrdinates`, `HigherMomentsAtZeroOrdinates`). *Answer:* AES.
8. **What is the non-archimedean gauge charge of a positive form?** Counterterms of each place are
   gauge blind (the twin's prime form is `P` in the gauge `x ↦ εx`), but their **matching** is
   charged. `ζ`'s prime divergence is `+ℓ²` along the archimedean polar direction; the Liouville
   twin's is `−ℓ²` (RP8). AES adds the coefficient margin of the source and the stability law for
   every twin. *Answer:* the gauge charge sits in the matching of the two places' counterterms.
9. **How does a quantized statistic reach every window?** By window energies (AES).
10. **Is the coupled class bounded at the centre?** Owned by BGG.
11. **What selects the fibre?** Divergences are soft: the tensor law holds for every sign twin in
    its gauged coordinates. Selection must come from the finite parts and from the gauge-charged
    matching (RP8).
12. **What are the escape states of `ζ` at infinite height?** Infinite transverse energy (AES).

---

## 7. Traps

| Trap | Truth |
|---|---|
| The torsion counterterm is the identity, so the prime place has no survival | That is the Abel radius; at the horizon the survival cone is the class-wise polar hyperplane |
| Coupling with the archimedean place lowers the torsion counterterm's rank | The prime block keeps its rank; a partner pays at most its own rank (`finrank_primeSurvival_le_rank`) |
| Any torsion orbit can be matched to the archimedean place | Ramanujan modes of order `≥ 2` have mean zero; only `O_1` couples |
| A better diagonal makes the renormalized form covariant and positive | Covariance forces a scalar, and a scalar counterterm has no survival |
| `κ ≍ log N` is a soft statement | The covariant constant is exactly one; the torsion constant is at least `3/2` |
| The anomaly is a nuisance to be removed for free | Its potential is the self-intersection; removing it saves at least `½ log N` |
| At the horizon the divergence is rank one | Only on uniform profiles; on class-wise profiles it is the tensor counterterm, of unbounded rank |
| A sign twin has the same divergences, so the same renormalization | The same spectrum, but the opposite polar matching at the Liouville gauge |
| The Hecke anomaly `log t` is intrinsic to the prime place | It belongs to the Abel radius; at the horizon `[p]` scales the orbit densities by `1/p` and the anomaly cancels |
| A matched counterterm proves the sign | It removes the divergence; the sign lives in the finite part |
| The finite part of the prime place hides the zeros | On uniform profiles it is the scalar `−2γ`; the zeros are invisible at log-scale resolution, and the sign is decided by the archimedean place and the pole |

---

## 8. Tools

**Imported.** Survival law, germs, Ramanujan relations, Cesàro Grams (RBG); orbit intersections,
the different, the Hecke cocycle and transport (AIT); torsion pairing, atomic Weil form, Schur
machinery (AES); Mertens' first theorem and Mertens' theorem with Euler's constant (RHTower).

**Built here.** Coupled counterterms and the partner-rank calculus; Hecke shifts and the covariance
of the tensor counterterm; the finite part with Euler's constant; the joint germ of the two
places; covariance of diagonals; the exact Schur rows and sharp two-sided bounds for the atomic
prime form; pole vectors, the polar functional, step profiles and their Gram; `p`-adic class pole
vectors, prime-power sums, class masses and the class Gram; the tensor law; Liouville signs, the
twisted Mertens sum and Dirichlet's hyperbola identity; telescoping bounds for `Σ log n/n`.

**To build.** The archimedean self-energy of an atom with constant one at width `ε ≍ 1/N`; Mertens'
theorem for characters; the class-wise finite part.

---

## 9. Open research topics

1. **The matched stability law.** At width `ε = c/N` the archimedean self-energy `log(1/ε)` and the
   covariant counterterm `log N + O(1)` agree to `O(1)`. Is `arch_ε + pole − P_N ≥ 0` on atomic tests
   for some fixed `c`? This is the sharpened central conjecture. All divergences are now computed;
   the statement concerns `O(1)` finite parts. AES proves the Markov form nonnegative at widths
   `N^{−O(1)}` with an archimedean gain `e^{−1/2} log(1/w)`. Closing the gap needs the constant-one
   self-energy.
2. **The finite part on the class-wise survival cone.** On uniform profiles it is `−2γ` (RP10). On
   class-wise profiles the class Gram should carry the same constant per class, corrected by the
   local Euler factor at `p`: compute it, and identify the finite part as a function on the orbits.
3. **Characters at the horizon.** Profiles twisted by a non-principal character should have bounded
   prime form, with finite part `−L′/L(1, χ)`. This needs Mertens' theorem for characters, and would
   identify the survival cone on residue classes mod `q` with the character space.
4. **The exact torsion constant.** The continuum model predicts `κ_tor(N) ∼ (e/(e − 1)) log N`; the
   Schur test fails on highly composite orders. The proven window is `[3/2, 4]` (with AES's upper
   bound).
5. **Polar matching for general gauges.** For a sign gauge flipping a set of primes of logarithmic
   density `ϑ`, the matching coefficient should be `1 − 2ϑ`. The Euler gauge is the unique gauge
   with coefficient `1` up to density zero.
6. **Several primes at once.** The tensor law and its covariance are proved for the classes of one
   prime `p`. For a finite set of primes `Q` the classes are `{n : n = d k, (k, Q) = 1}`, indexed by
   the `Q`-parts `d`. The expected counterterm is `Σ_d δ_d^{−1} ℓ_d²` with `δ_d = (1/d) Π_{p ∈ Q}(1 − 1/p)`,
   covariant under every `[q]`, `q ∈ Q`. This is the full orbit decomposition of `μ_{Q^∞}`.

---

## 10. Success criteria and contribution standards

RAPT succeeds when every question of §6 has an answer of the form theorem, sharp equivalence, or
sharp no-go with its positive survivor, and when the central conjecture of the report has been
replaced by a statement in which every divergence is computed and only a finite part is open. In
its present state:

* Q1 and Q2 have theorem-level answers: the coupled survival law with the arithmetic point as
  survivor; covariance ⇒ scalar with constant one; the cost of the anomaly; the tensor law and its
  covariance without anomaly. Of the three conditions of the central conjecture, (i) is false for
  every regulator, (ii) holds at the horizon, and (iii) is the open sign of the finite part.
* The prime finite part is computed: `−2γ` on the uniform survival cone (RP10).
* Q8 has a theorem-level answer for the Liouville twin.
* Q6 is answered through RP2, RP3 and RP5.
* The central conjecture is replaced by the matched stability law (§9.1).

A contribution is an unconditional Lean theorem about an object of §3. It names its **regulator**,
its **counterterm** with rank and survival cone, its **anomaly**, and the **place** that pays. It
separates identities and divergences (computed) from signs (open). It states what it gives on the
battery: sign twins, the golden datum, curves over `𝔽_q`. Every no-go records its positive survivor.

Principles: the rank of a counterterm belongs to the regulator; covariance forces scalars; the
divergence lives on the torsion orbits; matched divergences leave the sign in the finite part;
matching is gauge charged; identities first, sign last; a reformulation is not a reduction.

---

## 11. Modules

| Module | Content |
|---|---|
| `TheCoupledSurvivalLaw` | coupled counterterms; partner kernel; survival equations; rank and dimension bounds; rank-one partners; the torsion germ coupled to any partner |
| `TheArchimedeanPlacePaysTheArithmeticPoint` | Ramanujan orthogonality; the joint counterterm; prime survival `ℝ e₁`; the joint germ as a positive regularized family; matched survival |
| `TheCovariantCountertermIsTheAnomaly` | covariance of diagonal renormalizations; exact Schur rows; the pole vector as approximate eigenvector; `κ_cov = log N + O(1)` |
| `TheAnomalyCostsHalfALogarithm` | `φ(mt) ≤ t φ(m)`; torsion pairing on the pole charges; averages of `log n/n` and of the tame different; `κ_tor ≥ (3/2) log N − C` |
| `TheHorizonCountertermIsPolar` | truncated pole vectors and step profiles; the pole Gram; polarity on uniform profiles |
| `TheHorizonDivergenceLivesOnTheTorsionOrbits` | prime-power sums; class pole vectors; class rows; full rank on the arithmetic factor; unbounded rank |
| `TheHorizonCountertermIsATensorProduct` | class densities and orbit sizes; class masses; the class Gram at two horizons; the tensor law |
| `TheHorizonCountertermIsHeckeCovariant` | Hecke shifts; invariance of the prime form; class shift by `[p]`; orbit densities scale by the degree; no anomaly |
| `TheFinitePartIsEulersConstant` | Mertens with Euler's constant; roundoff; the finite part of the pole Gram; `−2γ` on step profiles and on the polar hyperplane |
| `TheLiouvilleGaugeFlipsThePolarDivergence` | Liouville signs; the twisted Mertens sum; Dirichlet's hyperbola; spectral ends; the polar flip |
