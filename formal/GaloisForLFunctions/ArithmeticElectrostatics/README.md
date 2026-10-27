# Arithmetic Electrostatics of the Zero Divisor (AES)

**One question.** The nontrivial zeros of `ζ` are the charges of one logarithmic potential,
`U = log |ξ|`. Arithmetic computes four quantities of that potential: its Laplacian (the collided
form `D`), its regularized gradient at the charges (the field `E`, read off `Λ ⋆ Λ`), its
renormalized self-interaction at the diagonal (torsion log-discriminants, the double pole of
`(ζ′/ζ)²`), and its reflection pairing (Weil's form `W`). RH says that the configuration is in
**transverse equilibrium**: no zero feels a field across the critical line. Equilibrium is
computed; its stability is the sign. Which inequality between the computed quantities makes the
equilibrium stable, which renormalization of the diagonal joins positivity and equivariance, and
which of these inequalities are provably out of reach of the inputs the corpus has?

AES is the potential theory of two charge carriers and of the dictionary between them:

- the **conjugate diagonal**: the zero divisor `Z = Σ_ρ m_ρ δ_ρ` in the critical strip, with the
  reflection `ρ ↦ 1 − ρ` (computed by the explicit formula) and the conjugation `ρ ↦ ρ̄` (computed by
  the potential theory of `log |ξ|`);
- the **characteristic circle** `ℝ/ℤ`: torsion orbits `O_n` (primitive `n`-th roots of unity) as
  charges, `−log |z − w|` as Green function, power maps `z ↦ z^t` as Hecke correspondences, the
  arithmetic point `z = 1` as distinguished fibre.

> *RH is the coincidence on the zero divisor of reflection and conjugation; in electrostatic terms,
> the statement that every zero is in transverse equilibrium. The explicit formula is the
> equilibrium equation; what it does not supply is stability. On the circle both equilibrium and
> stability are theorems, and the torsion realizes them.*

Namespace `GaloisForLFunctions.ArithmeticElectrostatics`; umbrella `ArithmeticElectrostatics.lean`.
Everything is unconditional; RH and its partial forms appear only inside equivalences.

---

## 1. Place in the research

The frontier ([obstacles summary](../../../docs/reports/review-2710/obstacles-summary.md), §4) maps
every forcing mechanism found so far and its sharp limit. What is missing has a precise shape: an
inequality that turns the computed positive form, or the computed field, into a bound; or a
renormalization that keeps a positive equivariant family positive at the diagonal. Over `𝔽_q`
both come from a polarization of `C × C`: Riemann–Roch gives the positive trace, the Frobenius is
a similitude, the self-intersection of the diagonal is the finite number `2 − 2g`. Over `ℤ` the
pieces exist in separate programmes, each with one property and not the other. AES is the language
in which they are quantities of one potential, and the place where the joining inequality — a
Hodge index theorem with adjunction — is stated, tested and reduced to its sharp form.

AES concerns the field form of the sign (B1.14), finite off-line index (B2.2), positivity of the
Rankin–Selberg source (B3.28), positive renormalization of torsion energies (B3.37, W16),
transverse equilibrium on the actual divisor (W7(xvi)), and the selection problem (B1.4); in wall
terms, the diagonal of Wall 14 and the polarization face of Wall 1.

| Programme | What AES takes | What AES adds |
|---|---|---|
| [ArithmeticPolarization](../ArithmeticPolarization/README.md) | `W`, `D`, `Δ`, `Re W = D − Δ`, Hecke law of `D`, log-Sobolev equivalence, `σ_γ`, the first gauge charge as a twist | `D` as the energy of the Riesz measure of `log |ξ|`; blindness of electrostatic quantities to the reflection-commuting affine group |
| [ConjugateDiagonalGeometry](../ConjugateDiagonalGeometry/README.md) | the `ξ` current, theta-prefix metrics, depth distributions, local zero detection | the field and the transverse energy as further quantities of the same current |
| [ArithmeticCorrespondencePositivity](../ArithmeticCorrespondencePositivity/README.md) | quadratic terminals, outward rays, the transverse field `xiTransverseField`, `fieldAt`, the source field at every zero, `L(Λ ⋆ Λ) = (ζ′/ζ)²` | virial laws, the threshold form of the field law, the renormalized square |
| [ArithmeticEffectivityTheory](../ArithmeticEffectivityTheory/README.md) | torsion orbits, `I(m, n)`, the Hecke law `I(m, mt) = φ(m)Λ(t)`, Abel energies, the renormalized torsion limit, the Farey potential, `J(a, b) = gcd log lcm` | self-intersections and adjunction of orbits, conjugation on cycles, counterterm rates, the arithmetic point, Fekete stability |
| `RHTower` (transverse chain) | the transverse force and its marginality identity, the zero network, the maximum principle, the attainment dichotomy, angular energy quantization, Selberg's identity, Mertens' first theorem | the energy of the whole divisor and its finiteness law, work = energy, window selection |
| [BiarithmeticGaugeGeometry](../BiarithmeticGaugeGeometry/README.md), [ArithmeticCorrelationGeometry](../ArithmeticCorrelationGeometry/README.md) | the gauge torus, twins, successor holonomy, quantization of surplus residues | the gauge charge of the renormalized source |
| [ArithmeticCastelnuovoSeveri](../ArithmeticCastelnuovoSeveri/README.md), [ArithmeticOrientationGeometry](../ArithmeticOrientationGeometry/README.md) | the scaling surface, Hodge index, Pontryagin law, `𝔽_q` calibration | the electrostatic reading of adjunction `Γ² = q(2 − 2g)` |

AES does not re-prove what these programmes own; it imports them and builds the laws that relate
them.

---

## 2. Why

**Two involutions.** The zero divisor of `ξ` is invariant under reflection `s ↦ 1 − s` and under
conjugation `s ↦ s̄`. The explicit formula computes sums `Σ_ρ m_ρ h(ρ)` with `h` holomorphic: it
sees the reflection, and its pairing is Weil's form `W`. Potential theory of `log |ξ|` sees the
conjugation: the Riesz measure `(1/2π) Δ log |ξ|` is the zero divisor, and its pairing is the
collided form `D(f) = Σ m |f̂(ρ)|²`. The two agree exactly when `ρ̄ = 1 − ρ` at every zero. `W` is
equivariant and its positivity is RH; `D` is positive and its equivariance is RH.

**Stieltjes.** Zeros of classical orthogonal polynomials are equilibrium positions of charges in an
external field, and the equilibrium equation is the differential equation of the polynomial at its
zeros. For `ξ` the equilibrium equation is the explicit formula and the external field the
Γ-factor with the pole; `ξ` satisfies no linear differential equation, so equilibrium cannot be
derived variationally. What holds on every configuration are the **virial laws**: the work of the
field against a displacement is an energy. The transverse virial turns the field into a nonnegative
Dirichlet energy of the real parts on the complete graph of zeros, positive definite on
reflection-odd displacements. Equilibrium is its vanishing; RH is equilibrium.

**Quantization.** An off-line zero and its partner `1 − ρ̄` share their ordinate. The segment
between them is horizontal and contributes exactly `m_ρ m_{ρ*}` to the transverse energy at every
depth. The energy of a reflection-closed configuration is `0` or at least one quantum; a window
cannot carry a fraction of one. Detection becomes a quantized lower bound, and the missing input is
an upper bound — an arithmetic inequality for the field — of a definite, non-infinitesimal size.

**One diagonal, three appearances.** Weil's self-intersection `Δ·Δ = 2 − 2g`, the torsion
self-energy `log(1/(1 − r))` of a root of unity, and the double pole `m²/(s − ρ)²` of `(ζ′/ζ)²` are
self-terms of one potential; removing each leaves the content (the trace, the prime kernel, the
field). In both arithmetic instances the self-term is renormalized by the **degree** `log n` of the
Hecke correspondence `T_n`: on the zero side the counterterm `(ζ′/ζ)′ = Σ Λ(n) log n · n^{−s}` turns
the square into Selberg's nonnegative source `Λ₂ = μ ⋆ log²`; on the circle the self-intersection
per point of `O_n` is `log n` minus local terms at the primes dividing `n`, and grows by exactly
`log p` along the tower of `p`. This is the arithmetic form of Weil's adjunction.

**Stability on the base.** The circle has what the divisor lacks: its discrete logarithmic energy
is bounded below (Fekete–Hadamard), and the torsion attains the bound. The torsion pairing is
positive before renormalization and Hecke equivariant after it; the obstruction between the two is
a self-energy that diverges logarithmically in the order and is carried by the arithmetic point.

---

## 3. Objects and language

| Electrostatics | Zero divisor of `ξ` | Characteristic circle | Over `𝔽_q` | Lean |
|---|---|---|---|---|
| charges | zeros `ρ`, multiplicities `m_ρ` | torsion orbits `O_n`, charge `y_n` per point | Frobenius eigenvalues | `XiZeroCopy`, `XiDivisorSupport`, `primitiveRoots` |
| finite configuration | reflection-closed models | — | — | `IsReflectionClosed` |
| field at a charge | `E(ρ) = Σ_{q≠ρ} m_q/(ρ − q)`; simple coefficient of `(ζ′/ζ)²` is `2mE` | — | — | `fieldAt`, `xiTransverseField`, `transverseForce` |
| transverse energy | `½ Σ_{ρ≠q} m_ρ m_q (Re ρ − Re q)²/|ρ − q|²` | — | `0` | `transverseEnergy`, `divisorTransverseEnergy` (unit charges), `xiCopyTransverseEnergy` (multiplicities) |
| work | `Σ m_ρ (Re ρ − ½) Re E(ρ)` | — | — | `transverseWork`, `displacement` |
| window energy | `Σ_{|γ−T|≤H} E_ang(ρ)` | — | — | `windowEnergy` |
| self-energy (diagonal) | double pole `m²` of `(ζ′/ζ)²`; renormalized `m(m − 1)` in `ζ″/ζ` | `log(1/(1 − r))` per point; renormalized `I(n, n) = log |disc Φ_n|` | `Δ² = 2 − 2g` | `selfTerm_and_residue_of_analyticOrderAt`, `orbitIntersection` |
| renormalized source | `Λ₂ = Λ log + Λ ⋆ Λ = μ ⋆ log²` | `D = φ ⋆ Λ` (local correction) | — | `selbergSource`, `localCorrection` |
| interaction | Weil's form `W` | `I(m, n) = log |Res(Φ_m, Φ_n)|` | `Γ_m · Δ` | `Z.W`, `orbitIntersection` |
| renormalized pairing | — | `Σ y_m y_n I(m, n)` against `κ Σ φ(n) y_n²` | — | `torsionPairing`, `selfMass`, `RenormalizesAt`, `RenormalizesWith` |
| distinguished fibre | the critical line | the arithmetic point `z = 1` (`O_1`) | the base field | `primitiveRoots_one` |
| symmetries | reflection, conjugation, Hecke translations, affine maps `s ↦ ½ + λ(s − ½) + iκ` | conjugation `z ↦ z^{−1}`, power maps `z ↦ z^t` | Frobenius, Rosati | `supportPartner`, `affineMap` |

**Words.**

- *Equilibrium* (at a charge): vanishing transverse field. *Stability*: positivity of the energy
  whose gradient is the field. *Work*: field times displacement, summed. *Virial law*: work =
  energy.
- *Quantum*: the transverse energy `m_ρ m_{ρ*}` of a reflection pair. *Gap*: no reflection-closed
  configuration has transverse energy in `(0, 1)` (integer multiplicities); no window has energy in
  `(0, 2)`.
- *Self-term*: the coefficient of the diagonal singularity. *Regularized*: the singularity cut off
  (`r < 1`). *Renormalized*: a counterterm subtracted, limit taken. *Counterterm*: a self-energy per
  point; *Hecke compatible*: constant on orders, or commuting with power maps; *positivity
  preserving*: the renormalized energy is nonnegative.
- *Adjunction*: a self-term expressed through the degree of a correspondence. *Cover formula*: the
  self-intersection of a `p`-fold cover is `p` times the base plus `p log p` per base point.
- *Computed*, *bounded*, *posited*; *detected*, *excluded*; *collided* (conjugate) and *Rosati*
  (reflection) pairing; *gauge invariant*, *gauge charged* — as in APol, ACG, ACP.

Parameters: the configuration, multiplicities, depth `δ`, ordinate `γ`, window `(T, H)`, the order
bound `N`, the counterterm `κ` or `c(n)`. Every theorem states which are fixed and which grow.

---

## 4. Mechanisms

### A. Finite configurations

1. **Virial laws** (`TheVirialLawsOfAFiniteConfiguration`). For distinct charges `z_j`,
   multiplicities `m_j`: Newton's third law `Σ m_j E_j = 0` (`sum_mul_fieldAt_eq_zero`); Stieltjes'
   virial `Σ m_j z_j E_j = ½((Σm)² − Σm²)`, a pure count (`sum_mul_mul_fieldAt`); the transverse
   virial `Σ m_j (Re z_j − c) Re E_j = transverseEnergy` for every centre `c`
   (`sum_mul_re_fieldAt_eq_transverseEnergy`); the vertical virial; and the energy count
   `transverse + vertical = ½((Σm)² − Σm²)` (`transverseEnergy_add_verticalEnergy`). A configuration
   is critical exactly when all of its energy is vertical.
2. **Equilibrium is the critical line** (`TransverseEquilibriumIsTheCriticalLine`). On
   reflection-closed configurations: transverse equilibrium ⇔ criticality (`critical_iff_equilibrium`);
   one scalar decides — nonpositive total work is criticality (`critical_iff_work_nonpos`); only
   off-line charges do work (`transverseWork_eq_sum_offLine`); each off-line pair carries the quantum
   `m_j m_{σj}` (`pairTerm_refl`, `pairQuanta_le_transverseEnergy`); with integer multiplicities the
   energy is `0` or `≥ 1` (`critical_iff_transverseEnergy_lt_one`); the deepest charge feels an
   outward and the shallowest an inward field (`exists_outward_and_inward_of_not_critical`).

### B. The divisor

3. **The energy of the divisor** (`TheTransverseEnergyOfTheZeroDivisor`). With unit charges at the
   distinct zeros, `𝓔 ∈ [0, ∞]`: `𝓔 = 0` ⇔ RH (`divisorTransverseEnergy_eq_zero_iff`), `𝓔 < 1` ⇔ RH
   (`riemannHypothesis_iff_divisorTransverseEnergy_lt_one`), every finite set of off-line zeros has
   at most `2𝓔` elements (`card_le_two_mul_divisorTransverseEnergy`), and `𝓔 < ∞` ⇔ finitely many
   off-line zeros (`divisorTransverseEnergy_lt_top_iff`). At finite off-line index the energy is the
   outward work of the off-line zeros (`divisorTransverseEnergy_eq_ofReal_work`), RH is work below one
   (`riemannHypothesis_iff_work_lt_one`), and `#off-line ≤ 2 · work`
   (`card_offLine_le_two_mul_work`).
4. **Global arithmetic work** (`ReflectedTransverseWork`, `TheSelbergWorkExhaustsTheTransverseEnergy`).
   For rational damping `w_R(t) = R⁴/(R² + t²)²`, `R ≥ 4`, compact height tapers of the work of the
   actual Laurent residues of `(ζ′/ζ)²` converge to a finite nonnegative value `xiDampedSourceWork R`
   (`xiTaperedSourceWork_tendsto`); as `R → ∞` these converge in `[0, ∞]` to the
   multiplicity-weighted transverse energy `xiCopyTransverseEnergy`
   (`xiDampedSourceWork_tendsto_energy`). Reflection pairing gives an absolutely summable majorant
   before any interchange; multiplicities, coincident copies and all exterior rows are kept; no
   finite off-line premise is used. The work–energy identity thus holds for the whole divisor as an
   arithmetic limit; the missing upper bound on this work is the sign problem.
5. **Window selection** (`QuantizationTurnsWindowsIntoPoints`). The energy of the window
   `|γ − T| ≤ H` bounds the number of off-line zeros in it (`card_offLine_le_windowEnergy`); a window
   with an off-line zero has energy at least `2` (`two_le_windowEnergy`); a window of energy below `2`
   is critical at any scale (`critical_of_windowEnergy_lt_two`); RH ⇔ every unit window has energy
   below `2` (`riemannHypothesis_iff_windowEnergy_lt_two`).
6. **The energy of a zero is logarithmic** (`TheEnergyOfAZeroIsLogarithmic`). Each pair term is at
    most `2/(1 + (γ − γ′)²)` (`angularEnergyTerm_le_lorentz`), so the Lorentzian zero mass gives
    `E(ρ) ≤ 16(C + log(|γ| + 4))` for every zero (`angularEnergy_le_log`) and a window bound by its
    number of zeros (`windowEnergy_le`): `1 ≤ E(ρ) ≤ 16(C + log(|γ| + 4))` at every off-line zero
    (`one_le_angularEnergy_le_log`). The energy is controlled unconditionally; the field is not
    (a nearly coincident pair contributes `1/|ρ − ρ′|`).
7. **The Hecke defect is the moment of inertia** (`TheHeckeDefectIsTheMomentOfInertia`). On the
    strip `2cosh(2δL) − 2 ≤ 4δ²(2cosh L − 2)` (`depthKernel_le_mul_half`), so the symmetric
    equivariance defect of `D` and the transverse moment of inertia `M_f = Σ m δ²|f̂(ρ)|²` satisfy
    `4L² M_f ≤ E_f(L) ≤ 8(cosh L − 1) M_f` (`moment_le_heckeDefect`, `heckeDefect_le_moment`) and
    `E_f(L)/L² → 4 M_f` (`tendsto_heckeDefect_div_sq`).

### C. The field

8. **The field is computed** (`TheRenormalizedSquareIsSelbergsSource`; ACP `EveryXiZeroHasASourceField`).
   At a zero of order `m` of an analytic `F`, the regular part `R` of `F′/F` is analytic, the
   double-pole coefficient of `(F′/F)²` is `m²` and that of `F″/F` is `m(m − 1)`, and both residues are
   `2m R(ρ)` (`selfTerm_and_residue_of_analyticOrderAt`). For `ξ` the regular part is the field of the
   other zeros at every zero.
9. **The field law has a threshold** (`TheFieldLawHasAThreshold`). RH ⇔ every zero right of the
   line feels a transverse field at most `1` (`riemannHypothesis_iff_forall_transverseField_le_one`);
   for an explicit `c > 0`, RH ⇔ every such zero feels a field below `√(2c log(|γ| + 4))`
   (`exists_riemannHypothesis_iff_transverseField_lt_sqrt_log`). The terminal reserve
   `1/(2δ) + cδ log γ` is minimized at `δ = (2c log γ)^{−1/2}`. The field law that would exclude
   off-line zeros is an upper bound of size `max(1, √(2c log γ))`, not an exact equilibrium.
10. **The external field is a prime sum** (`TheExternalFieldIsAPrimeSum`). For `Re s > 1` the field
    of the divisor is a sum of positive Coulomb terms, `Re ξ′/ξ(s) = Σ_ρ Re 1/(s − ρ)`
    (`re_logDeriv_xi_eq_tsum_of_one_lt_re`, `re_reciprocal_pos_of_one_lt_re`), and the explicit
    formula computes it from the primes: `Re L(Λ, s) + Σ_{ρ∈F} Re 1/(s − ρ) ≤ Re (archFactor′/archFactor)(s)`
    for every finite `F` (`re_LSeries_vonMangoldt_add_sum_le`), with
    `Re L(Λ, σ + it) = Σ Λ(n) n^{−σ} cos(t log n)` (`re_LSeries_vonMangoldt_eq`). At the ordinate `γ`
    of a zero of real part `β` and multiplicity `m`, **anti-alignment**:
    `Σ Λ(n) n^{−σ} cos(γ log n) ≤ Re (archFactor′/archFactor)(σ + iγ) − m/(σ − β)`
    (`re_LSeries_vonMangoldt_le_at_zero_ordinate`). Outside the strip a charge pushes the primes out
    of alignment at its own height by its full Coulomb term; inside the strip the outward reserve is
    the matching lower bound on the other side of the charge.

11. **Large values at zero ordinates** (`LargeValuesAtZeroOrdinates`). For a Dirichlet polynomial
    `F(t) = Σ_{n≤N} a_n n^{it}` and zero copies with ordinates in `(A, A + R]`, `A ≥ T₀`:
    `Σ_γ |F(γ)|² ≤ K log(A + R + 1)(R + 8N(1 + log N))(2 + log² N) Σ|a_n|²`
    (`exists_sum_zeroOrdinates_normSq_le`: Sobolev on unit cells, `O(log)` zeros per cell by the
    local zero ceiling, the mean-value theorem on the window), hence the large-values count
    (`exists_card_largeValues_le`). For the prime polynomial `a_n = w_n Λ(n)/√n` the mass is at most
    `log N (log N + log 4 + 4)` (`coeffMass_primeCoeff_le`), giving the **alignment law**
    (`exists_card_aligned_le`): the zero ordinates in `(T, 2T]` at which the prime polynomial of
    length `X` reaches `(1 − η) log T` number `O(T log⁴ X / log T)`, a vanishing proportion of the
    zeros for `log X = o(√log T)` — every aperture up to the forcing threshold.

### D. Renormalization of the diagonal

12. **The zero side** (`TheRenormalizedSquareIsSelbergsSource`). The counterterm identity
   `F″/F = (F′/F)² + (F′/F)′` (`deriv_deriv_div_eq`); Selberg's source `Λ₂ = Λ log + Λ ⋆ Λ = μ ⋆ log²`
   (`selbergSource_eq`), nonnegative (`selbergSource_nonneg`), `Λ₂(p^k) = (2k − 1) log² p`
   (`selbergSource_prime_pow`), with `L(Λ₂, s) = ζ″(s)/ζ(s)` on `Re s > 1` (`LSeries_selbergSource`).
   The degree counterterm `Λ log` removes the self-term at simple zeros, keeps the source
   nonnegative, and leaves the field as residue.
13. **The circle** (`TheSelfIntersectionOfATorsionOrbit`). `I(n, n) = φ(n) log n − (φ ⋆ Λ)(n)`
   (`orbitIntersection_self_eq`), `0 ≤ I(n, n) ≤ φ(n) log n` (`orbitIntersection_self_le`,
   `orbitIntersection_self_nonneg`); `(φ ⋆ Λ)(p^{a+1}) = p^a log p` (`localCorrection_prime_pow`), so
   per point `ℓ_{p^a} = a log p − log p/(p − 1)`; the Leibniz rule `D(ab) = φ(a)D(b) + φ(b)D(a)` on
   coprime orders (`localCorrection_mul_of_coprime`) makes the self-intersection per point additive
   (`orbitIntersection_self_mul_of_coprime`); the cover formula
   `I(p^{a+2}, p^{a+2}) = p I(p^{a+1}, p^{a+1}) + φ(p^{a+1}) p log p` (`orbitIntersection_self_prime_pow_succ`)
   gives growth by exactly the degree `log p` per point (`selfIntersection_per_point_prime_pow_succ`).
   Conjugation maps every orbit onto itself and is the power map of degree `−1`
   (`conj_mem_primitiveRoots`, `conj_eq_pow_of_mem_primitiveRoots`); the Hermitian and bilinear Abel
   energies agree on torsion cycles (`sum_sum_conj_eq`, `torsionEnergy_eq_bilinear`).
14. **The counterterm rate** (`TheTorsionCountertermIsLogarithmic`). A constant counterterm `κ` per
    point renormalizes the orders `≤ N` (`RenormalizesAt`) for `κ = 4 log N + log 4 + 4`
    (`renormalizesAt_log`: diagonal `I(n, n) ≤ φ(n) log n`, Schur test with weights `1/n`, the Hecke
    law, Mertens, super-multiplicativity of `φ`) and only if `κ ≥ ((p − 2)/(p − 1)) log p` for every
    prime `p ≤ N` (`le_of_renormalizesAt_prime`), hence `κ ≥ ½ log(N/2)` for `N ≥ 4`
    (`half_log_le_of_renormalizesAt`, `torsionCounterterm_rate`). No finite renormalization keeps the
    torsion pairing positive uniformly in the order; the divergence is exactly logarithmic, the
    rate of the archimedean self-energy `log(1/ε)` of an atom of width `ε ≍ 1/N`.
    The prime side has the same rate (`TheWeilPrimeFormOnAtomsIsLogarithmic`): Weil's prime form on
    the atoms `log n`, `n ≤ N`, is at most `(2 log N + log 4 + 4) Σ x_n²` (`atomicWeilForm_le`, Schur
    with weights `n^{−1/2}`), and any bound `κ` satisfies `κ² ≥ Σ_{2≤n≤N} Λ(n)²/n ≥ log 2 (log N − log 4 − 4)`
    (`sqrt_le_of_atomicWeilForm_le`, `log_two_mul_le_sq_of_atomicWeilForm_le`), forced again by the atom
    at the arithmetic point `log 1 = 0`. The counterterm the archimedean place must supply at atomic
    resolution `N` is logarithmic on both carriers.

15. **The stability law at atomic resolution** (`TheStabilityLawAtAtomicResolution`). Put a `C²`
    bump `g` of width `w` at each atom `log n`, `n ≤ N`, with weights `x_n` (`atomicTest`). Below the
    spacing `δ_N = log(1 + 1/N)` the atoms are orthogonal (`integral_atomicTest_sq`), the Lévy
    self-energy of the archimedean place is at least `e^{−1/2} log(δ_N/(2w))` per unit mass
    (`levyEnergy_ge_of_disjoint_shifts`, `levyEnergy_atomicTest_ge`), and the prime sum is exactly
    `(∫ g²) × atomicWeilForm` — only the Hecke relations `m = nk` survive (`primeSum_atomicTest`,
    `sum_vonMangoldtAtom_hecke`). Hence the Weil form without its pole, `M = archForm − primeSum`,
    satisfies `M(f) ≥ (2θ′(0) + e^{−1/2} log(δ_N/(2w)) − 2 log N − log 4 − 4) ∫ f²`
    (`markovEnergy_atomicTest_ge`) and is nonnegative for every width `w ≤ atomicWidth N`, a fixed
    power `N^{−O(1)}` (`markovEnergy_atomicTest_nonneg`). The archimedean self-energy is a counterterm
    constant on the atoms — compatible with every Hecke translation — that preserves positivity
    below a power of the spacing: the adjunction law at atomic resolution. At widths comparable to
    the spacing the gain `log(δ_N/w)` is bounded and the prime counterterm is not (ES11): there the
    matching stops, and the tests begin to see the zeros.

### E. The base and the arithmetic point

16. **Power maps are similitudes** (`PowerMapsAreSimilitudesOfTheAbelEnergy`). The Abel energy of
    the torsion groups `μ_A`, `μ_B` has the closed form `T_r(A, B) = gcd(A, B) log(1/(1 − r^{lcm(A,B)}))`
    (`fullTorsionEnergy_eq`); the matrix is positive semidefinite (`sum_sum_fullTorsionEnergy_nonneg`);
    pulling back by `z ↦ z^t` multiplies it by the degree and rescales the cutoff,
    `T_r(At, Bt) = t · T_{r^t}(A, B)` (`fullTorsionEnergy_mul`); removing the self-energy of the
    `gcd(A, B)` common points leaves `−J(A, B) = −gcd log lcm` as `r → 1` (`tendsto_fullTorsionEnergy_sub_log`);
    and `J(At, Bt) = t (J(A, B) + gcd(A, B) log t)` (`logEnergy_mul`): the adjunction term is the shift
    of the self-energy under the rescaled cutoff. On the base the Hecke correspondences are computed
    similitudes of a positive Hermitian structure.
17. **The torsion is the stable equilibrium of the circle** (`TheTorsionIsTheStableEquilibriumOfTheCircle`).
    `N` distinct points of the unit circle satisfy `Σ_{i≠j} log |z_i − z_j| ≤ N log N`
    (`sum_sum_log_norm_sub_le`: Vandermonde and Hadamard), and the `N`-th roots of unity attain it
    (`logEnergy_self_eq`). Discrete energy on the circle is bounded below; the torsion is a minimizer.
18. **The arithmetic point carries the divergence** (`TheArithmeticPointCarriesTheDivergence`).
    `1` is the only point of the circle fixed by the power maps (`eq_one_of_forall_pow_eq_self`),
    `O_1 = {1}` (`primitiveRoots_one`), `I(1, n) = Λ(n)` (`orbitIntersection_one_left`). Every
    counterterm `c(n)` renormalizing the orders `≤ N` satisfies `c(1) ≥ Σ_{2≤n≤N} Λ(n)²/(c(n)φ(n))`
    (`le_counterterm_one`); a constant one satisfies `κ² ≥ Σ Λ(n)²/φ(n) ≥ log 2 (log N − log 4 − 4)`
    (`sq_le_of_renormalizesAt`, `log_two_mul_le_sq_of_renormalizesAt`). A counterterm bounded on the
    orbits of order `≥ 2` must diverge at `z = 1`, the point at which `ψ(N)` is the potential of the
    Farey torsion and RH is a potential bound (AET `psi_eq_fareySum`, `riemannHypothesis_iff_fareySum`).

### F. Gauge

19. **Blindness to the archimedean place** (`QuantizationTurnsWindowsIntoPoints`). The
    reflection-commuting affine maps `s ↦ ½ + λ(s − ½) + iκ` preserve the transverse energy
    (`transverseEnergy_affine`) and scale the field by `λ⁻¹` (`fieldAt_affine`): dilations and the
    archimedean twist — hence the first gauge charge — are invisible to electrostatic quantities.
20. **Gauge charge of the source**. For a completely multiplicative gauge `ω`, the renormalized
    source of the twin `ωΛ` is `ωΛ₂` (`pmul_mul_pmul`, `selbergSource_twist`); its nonnegativity at a
    prime forces `ω(p) = 1` for sign gauges (`eq_one_of_twisted_selbergSource_nonneg`). The charge
    enters through the arithmetic computation, prime by prime.
21. **The gauge margin law of the source** (`TheGaugeMarginOfTheRenormalizedSource`). For a sign gauge
    flipping a prime `p`, `ωΛ₂(p) = −log² p` against `Λ₂(p) = log² p` (`gaugeMargin_of_flip`); on
    every window `N` containing a flipped prime some coefficient is `≤ −log² 2` while `Λ₂ ≥ 0`
    (`gaugeMargin_window`) — a margin fixed by the first flipped prime, not collapsing as primes
    enter; for real `σ > 1`, `L(Λ₂, σ) − L(ωΛ₂, σ) ≥ 2 log² p · p^{−σ}` (`LSeries_gaugeMargin`, with
    `Σ Λ₂(n) n^{−σ}` convergent by `Λ₂ ≤ 3 log²`, `summable_selbergSource_rpow`).

---

## 5. Pillar theorems

| Pillar | Statement | Lean |
|---|---|---|
| **ES1 Virial laws** | work of the field = energy; transverse + vertical = count | `sum_mul_re_fieldAt_eq_transverseEnergy`, `sum_mul_mul_fieldAt`, `transverseEnergy_add_verticalEnergy` |
| **ES2 Equilibrium is the critical line** | equilibrium ⇔ nonpositive work ⇔ critical; quantum per pair; gap `1`; maximum principle | `critical_iff_equilibrium`, `critical_iff_work_nonpos`, `pairQuanta_le_transverseEnergy`, `critical_iff_transverseEnergy_lt_one`, `exists_outward_and_inward_of_not_critical` |
| **ES3 The energy of the divisor** | `= 0` ⇔ RH ⇔ `< 1`; finite ⇔ finite off-line index; work = energy | `divisorTransverseEnergy_eq_zero_iff`, `riemannHypothesis_iff_divisorTransverseEnergy_lt_one`, `divisorTransverseEnergy_lt_top_iff`, `riemannHypothesis_iff_work_lt_one` |
| **ES4 Global source-work exhaustion** | damped tapered Laurent-residue work exhausts the multiplicity-weighted energy, finite or infinite | `xiTaperedSourceWork_tendsto`, `xiDampedSourceWork_tendsto_energy` |
| **ES5 Window selection** | window energy counts off-line zeros; `< 2` ⇒ critical | `card_offLine_le_windowEnergy`, `critical_of_windowEnergy_lt_two`, `riemannHypothesis_iff_windowEnergy_lt_two` |
| **ES6 Defect = moment of inertia** | `4L² M_f ≤ E_f(L) ≤ 8(cosh L − 1) M_f`; `E_f(L)/L² → 4M_f` | `heckeDefect_le_moment`, `moment_le_heckeDefect`, `tendsto_heckeDefect_div_sq` |
| **ES7 Field threshold** | RH ⇔ field `≤ 1` ⇔ field `< √(2c log γ)` at right zeros | `riemannHypothesis_iff_forall_transverseField_le_one`, `exists_riemannHypothesis_iff_transverseField_lt_sqrt_log` |
| **ES8 External field and alignment** | `Re L(Λ, s) + Σ_F Re 1/(s − ρ) ≤ Re arch′/arch`; anti-alignment `m/(σ − β)` at zero ordinates | `re_LSeries_vonMangoldt_add_sum_le`, `re_LSeries_vonMangoldt_eq`, `re_LSeries_vonMangoldt_le_at_zero_ordinate` |
| **ES9 The renormalized square** | self-term `m² → m(m − 1)`, residue `2mR`; `Λ₂ = μ ⋆ log² ≥ 0`, `L(Λ₂) = ζ″/ζ` | `selfTerm_and_residue_of_analyticOrderAt`, `selbergSource_nonneg`, `selbergSource_prime_pow`, `LSeries_selbergSource` |
| **ES10 Torsion adjunction** | `I(n,n) = φ log n − φ ⋆ Λ`; additivity; cover formula; conjugation on cycles | `orbitIntersection_self_eq`, `orbitIntersection_self_mul_of_coprime`, `orbitIntersection_self_prime_pow_succ`, `torsionEnergy_eq_bilinear` |
| **ES11 Logarithmic counterterm** | minimal constant counterterm on orders `≤ N` in `[½ log(N/2), 4 log N + O(1)]`; the atomic Weil prime form has norm in `[√(log 2 (log N − C)), 2 log N + C]` | `torsionCounterterm_rate`, `atomicWeilForm_le`, `log_two_mul_le_sq_of_atomicWeilForm_le` |
| **ES12 The arithmetic point** | `I(1, n) = Λ(n)`; `c(1) ≥ Σ Λ²/(cφ)` | `orbitIntersection_one_left`, `le_counterterm_one` |
| **ES13 Similitudes on the base** | `T_r(A,B) = gcd log 1/(1 − r^{lcm})`, PSD; `T_r(At, Bt) = t T_{r^t}(A, B)`; renormalized limit `−J` | `fullTorsionEnergy_eq`, `sum_sum_fullTorsionEnergy_nonneg`, `fullTorsionEnergy_mul`, `tendsto_fullTorsionEnergy_sub_log`, `logEnergy_mul` |
| **ES14 Stability of the base** | Fekete bound `N log N`, attained by the torsion | `sum_sum_log_norm_sub_le`, `logEnergy_self_eq` |
| **ES15 Gauge** | affine invariance; `Λ₂^ω = ωΛ₂` | `transverseEnergy_affine`, `selbergSource_twist`, `eq_one_of_twisted_selbergSource_nonneg` |
| **ES16 The energy of a zero** | `1 ≤ E(ρ) ≤ 16(C + log(|γ| + 4))` off the line; window energy `≤` zero count × `O(log)` | `angularEnergy_le_log`, `windowEnergy_le`, `one_le_angularEnergy_le_log` |
| **ES17 Large values at zero ordinates** | `Σ_γ |F(γ)|² ≤ K log(A+R+1)(R + 8N(1+log N))(2 + log²N) Σ|a_n|²`; alignment law for prime polynomials | `exists_sum_zeroOrdinates_normSq_le`, `exists_card_largeValues_le`, `exists_card_aligned_le` |
| **ES18 Stability at atomic resolution** | `M(f) ≥ (2θ′(0) + e^{−1/2} log(δ_N/2w) − 2 log N − C)∫f²`; `M ≥ 0` for `w ≤ atomicWidth N` | `primeSum_atomicTest`, `levyEnergy_atomicTest_ge`, `markovEnergy_atomicTest_ge`, `markovEnergy_atomicTest_nonneg` |
| **ES19 Gauge margin of the source** | margin `2 log² p` at the first flipped prime, `≤ −log² 2` on every window; L-series margin | `gaugeMargin_of_flip`, `gaugeMargin_window`, `LSeries_gaugeMargin` |

Inherited and used throughout: `Re W = D − Δ`, `D` faithful, coercive and log-Sobolev (APol); the
transverse force and its marginality identity, the maximum principle, the attainment dichotomy,
angular energy quantization (RHTower); critical configurations in transverse equilibrium, the deepest
off-line zero with positive field, quadratic terminals with a logarithmic reserve, the source field
at every zero (ACP); the Hecke law of torsion orbits and the renormalized torsion limit of the prime
kernel (AET).

---

## 6. The questions and their answers

1. **What is the Frobenius at infinity as a correspondence?** On the circle it is algebraic:
   conjugation is the power map of degree `−1`, fixes every torsion cycle, and identifies the
   Hermitian (collided) and bilinear (reflection) torsion pairings (ES10); the Hecke correspondences
   are computed similitudes of the regularized Hermitian structure, with the cutoff rescaled by the
   degree (ES13). On the divisor, conjugation composed with reflection is the Hermitian reflection `ρ ↦ 1 − ρ̄`, trivial iff RH
   (`riemannHypothesis_iff_supportPartner_eq_id`); its pairing is `D`, whose Hecke equivariance is
   RH (APol). The disagreement of the two involutions is counted by the transverse energy (ES3).
   *Answer:* algebraic on the base; on the divisor its realization by a correspondence is RH.
2. **What is the self-intersection of the diagonal?** Renormalization by the degree on both sides:
   on the zero side the self-term drops from `m²` to `m(m − 1)`, the source becomes `Λ₂ ≥ 0`, the
   field is the residue (ES9); on the circle `I(n, n) = log |disc Φ_n| = φ(n) log n − (φ ⋆ Λ)(n)`,
   additive over coprime orders and growing by `log p` per point along the tower of `p` (ES10).
   *Answer:* Hecke-compatible renormalizations exist and preserve positivity of coefficients; on the
   circle they preserve positivity of the pairing only with a counterterm of size `Θ(log N)`
   (ES11), concentrated at the arithmetic point (ES12). The archimedean place supplies exactly such
   a counterterm: its Lévy self-energy `e^{−1/2} log(1/w)` pays the prime counterterm, and Weil's
   form without its pole is nonnegative on every atomic test at the points `log n`, `n ≤ N`, of
   width `≤ N^{−O(1)}` (ES18). The matching holds below a power of the spacing and stops at the
   spacing, where the tests see the zeros; there it is the sign problem (§9.2).
3. **What bounds the field?** The energy is bounded unconditionally — `E(ρ) ≤ 16(C + log(|γ| + 4))`
   at every zero, a window by its zero count (ES16) — because each pair term is at most one; the
   field is not, since a nearly coincident pair contributes `1/|ρ − ρ′|`. The bound that would
   exclude off-line zeros is sharp: at right zeros a field `≤ 1`, or `< √(2c log γ)`, is RH (ES7);
   equivalently energy `< 1` per zero or total (ES3), unit-window energy `< 2` (ES5). *Answer:*
   unconditionally `O(log γ)` per zero for the energy; the improvement from `O(log γ)` to below one
   quantum is RH; its weaker-than-RH forms are finite total energy (finite off-line index) and
   window bounds.
4. **What bounds the equivariance defect of `D`?** Hecke translation by `L` reweights the charges by
   `e^{2δL}`, and the defect is the transverse moment of inertia `M_f = Σ m δ² |f̂(ρ)|²` of the
   weighted divisor at every scale: `4L² M_f ≤ E_f(L) ≤ 8(cosh L − 1) M_f`, `E_f(L)/L² → 4M_f`
   (ES6). *Answer:* the defect question is equivalent, with explicit constants, to bounding the
   moment of inertia of the charges seen by the test; an arithmetic bound for it is open (B3.33).
5. **What is the arithmetic point, and what is its period?** The unique common fixed point of the
   power maps, the orbit `O_1`; `Λ(n) = I(1, n)` is the potential of `O_n` there; the divergence of
   every positivity-preserving renormalization sits there (ES12); `ψ(N)` is the Farey potential there
   and RH is its square-root bound (AET). It is fixed, not periodic, under every power map; the
   Frobenius-flat structure that gives Stepanov's method its period over `𝔽_q` has no analogue there
   (AET).
6. **How does `σ_γ` localize beyond the conductor; are zero ordinates aligned with small primes?**
   Right of the strip alignment is controlled pointwise: at the ordinate of a zero of real part `β`
   the prime cosine sum `Σ Λ(n) n^{−σ} cos(γ log n)` is at most the archimedean field minus
   `m/(σ − β)` (ES8). On the critical side alignment is rare: the discrete mean value over zero
   ordinates (ES17) shows that the zeros in `(T, 2T]` at which a prime polynomial of length `X`
   reaches `(1 − η) log T` number `O(T log⁴ X/ log T)`, a vanishing proportion for
   `log X = o(√log T)`, which covers every aperture between the conductor horizon and the forcing
   threshold. *Answer:* zero ordinates are aligned with small primes only on a set of zero density;
   excluding isolated deep zeros needs a power saving, which the same law gives from higher moments
   `F^k` once the coefficient mass of the convolution powers is controlled (§9.6).
7. **What is the non-archimedean gauge charge?** Electrostatic quantities are invariant under the
   reflection-commuting affine group, hence blind to every archimedean twist (ES15), and the circle's
   positivity holds for every charge configuration (ES13); the gauge enters through the arithmetic
   source, `Λ₂^ω = ωΛ₂`, prime by prime, with a margin law: every sign twin differing from the Euler
   vacuum on a window has a source coefficient `≤ −log² 2` there, a margin fixed by the first flipped
   prime and not collapsing as primes enter (ES19). *Answer:* the charge and its non-collapsing margin
   live in the source; the margin of the corresponding Weil forms on signed tests (the report's Q3)
   is not supplied by coefficient positivity and remains a certified-window question.
8. **Is the coupled class bounded at the centre?** Owned by BGG. Electrostatically the central
   order of a member is the charge it places at `½`: contracting an off-critical quartet at
   ordinate `γ` moves four charges — two reflection pairs, two quanta of transverse energy — onto
   the centre (`Δ ord = +4`), while outward critical splitting removes two (`Δ ord = −2`). The ceiling
   `ord_{1/2}(Λ) ≤ ord_{1/2}(Λ_γ)` is thus a bound on central charge; on the positive and rational
   subclasses it is equivalent to the absence of off-critical zeros at `γ` (BGG
   `positiveCentralVanishingCeiling_iff`, `rationalCentralVanishingCeiling_iff`). *Answer:* the full
   class is open (B3.34); AES contributes the quantization of what the ceiling must exclude.
9. **What selects the fibre?** The finite laws (ES1, ES2) hold on every reflection-closed
   configuration, fake ones included, and the circle laws (ES10–ES14) on every torsion cycle:
   electrostatic geometry is soft. *Answer:* selection must come from the arithmetic computation of
   the source or the counterterm, never from the geometry of the charges.
10. **What are the escape states of `ζ` at infinite height?** Infinite transverse energy is exactly
    an infinite off-line set (ES3); finite energy forces attainment of the depth supremum, and then
    the marginality identity gives RH (`riemannHypothesis_of_transverseForce_zero_of_energy_lt_top`).
    The arithmetic work exhausts the energy without any finiteness premise (ES4). *Answer:* escape is the infinite-energy regime; its exclusion is open.
11. **How does an average become a point?** By quantization: the energy of a window of any size
    counts its off-line zeros, and a window of energy below `2` is critical (ES5). *Answer:* for a
    quantized quantity selection below the zero spacing is free; the difficulty moves entirely into
    bounding the quantity.
12. **What is the base?** The characteristic circle with its torsion: discrete energy bounded below
    and attained by the roots of unity (ES14), a positive Hermitian structure on which the power maps
    act as similitudes up to rescaling of the cutoff (ES13), the torsion pairing positive before
    renormalization and Hecke equivariant after (AET, ES10). *Answer:* the base carries stability for
    free; the divisor must inherit it through an adjunction that matches the logarithmic
    counterterm (ES11).

---

## 7. Traps

| Trap | Truth |
|---|---|
| Equilibrium can be derived variationally, as for Stieltjes | Stieltjes needs a linear ODE; `ξ` satisfies none |
| The marginality identity is an inequality waiting for a proof | It is RH-equivalent; its attained case is RH, its non-attained case is escape |
| A positive field at the deepest zero excludes it | It detects; exclusion needs an upper bound of size `max(1, √(2c log γ))` |
| The transverse energy decays as zeros approach the line | It is quantized: each off-line pair carries a full unit at every depth |
| Removing the diagonal from a positive energy keeps it positive | Discrete charges without self-energy need a counterterm of size `Θ(log N)` |
| A bounded counterterm suffices on most orbits | The arithmetic point forces `c(1) ≥ Σ Λ²/(cφ)` |
| `Λ₂ ≥ 0` is positivity beyond isotropy | It is positivity of coefficients; the field enters only through residues |
| The torsion pairing lacks Hecke equivariance | It has the Hecke law exactly; it lacks positivity only at the diagonal |
| Conjugation is the missing correspondence over `ℤ` | On the circle it is a power map; on the divisor its pairing is `D`, not computed by the explicit formula |
| Electrostatic quantities see the first gauge charge | They are invariant under every archimedean twist |
| The field and the energy are equally hard to bound | The energy is `O(log γ)` per zero unconditionally; the field has no unconditional bound |
| The archimedean self-energy cannot pay the prime form | It pays it exactly, below a power of the atomic spacing (ES18); it cannot at the spacing |
| Aligned zero ordinates must be rare by randomness | The second moment proves it (ES17); the needed power saving is a higher-moment statement |
| Energy controls the potential at a point | Logarithmic energy does not bound pointwise potentials (Franel–Landau is a potential at one point) |

---

## 8. Tools

**From sibling programmes:** the two forms and the defect; the `ξ` current; terminals, outward
rays, the source field and `L(Λ ⋆ Λ)`; torsion orbits, resultants, Ramanujan sums, Abel energies;
the transverse force, zero network, maximum principle, angular energy; Mertens' first theorem;
Selberg's identity; Hadamard's inequality (`complex_hadamard_entry_bound`).

**Built here:** the virial calculus of finite configurations and reflection-closed models; the
transverse energy of the divisor in `[0, ∞]` and its work form; damped arithmetic source work
(with the reflected pair kernel); window energies; field thresholds; the counterterm identity and
Laurent self-terms; Selberg's source and its gauge twists; the local correction `φ ⋆ Λ`, its
Leibniz rule and the cover formula; conjugation on torsion cycles; renormalized torsion pairings
and counterterm rates; the arithmetic-point bound; Fekete's bound on the circle; affine invariance.

**Built for the frontier's list (§4.5 of the report):** arithmetic adjunction — the degree
renormalization on both carriers (ES9, ES10), the similitude structure of the circle (ES13), and the
matched archimedean counterterm at atomic resolution (ES18); field and defect inequalities — the
unconditional energy bound (ES16), the sharp field thresholds (ES7), the external field law (ES8),
the defect as moment of inertia (ES6); Diophantine control at zero ordinates — anti-alignment
outside the strip (ES8) and the large-values law on the line (ES17); gauge margin laws at the level
of the source (ES19); Hermitian structures with computed similitudes on the base (ES13); selection at
the zero spacing by quantization (ES5).

**Not yet built anywhere:** an arithmetic upper bound for the field or the energy below one
quantum (RH-strength); the matched renormalization at the spacing scale (the sign itself); power
saving for aligned zero ordinates (needs the mass of convolution powers); margins of Weil forms on
signed tests for growing prime windows; a Hermitian structure with computed Hecke similitudes on
the zero side.

---

## 9. Open research topics

1. **The field law.** An arithmetic upper bound for the transverse field at right zeros below
   `max(1, √(2c log γ))`, or for the energy of unit windows below `2`. RH-strength. The energy is
   `O(log γ)` per zero unconditionally (ES16); partial forms are finite total energy (finite
   off-line index, B2.2) and window energies below the zero count at large height.
2. **The stability law (Hodge index with adjunction) at the spacing.** ES18 proves it at atomic
   resolution `w ≤ N^{−O(1)}`: the archimedean self-energy pays the logarithmic counterterm. The open
   step is the spacing scale `w ≍ 1/N`, where the Lévy gain is bounded and the prime counterterm is
   not (ES11, ES12): positivity there must come from cancellation in the prime form rather than from
   self-energy — the sign problem in its adjunction form.
3. **Matched renormalization of the square.** Compare the torsion counterterm with the zero-side
   counterterm `Λ log` through the explicit formula for `ζ″/ζ`.
4. **Electrostatics of the twins.** Fields and energies of the divisors of sign twins (signed
   configurations, no reflection closure); which electrostatic quantity carries non-archimedean
   charge at the level of forms rather than coefficients.
5. **Attainment.** Exclusion of infinite transverse energy for the actual divisor, or an energy
   criterion for attainment of the depth supremum with infinitely many off-line zeros.
6. **Power saving for alignment.** The second moment over zero ordinates is ES17, the first moment
   is in the corpus (`exists_zeroSum_dirichletPolynomial_le`: zero ordinates anti-align on average).
   Applied to `F^k` the large-values law gives power-saving exceptional sets as soon as the
   coefficient mass of the convolution powers of the prime polynomial is bounded by `k! (½ log² X)^k`
   (the multinomial count over prime factorizations); with that, compare the exceptional set with
   zero density and iterate the forcing half outside it (the report's Q1). The outward reserve as a
   short prime sum at the terminal ordinate (W18) is the second entrance.

---

## 10. Success criteria and what a contribution must be

AES succeeds when it proves a stability law of a type the corpus does not contain — an inequality
between computed quantities of the potential that turns detection into exclusion on a stated class
— or a sharp no-go naming the missing input with its positive survivor, and when every question of
§6 has an answer of that kind. Its present state: every question has an answer of the form
theorem, sharp equivalence, or located gap (§6); the stability law holds at atomic resolution
(ES18) and its form at the spacing scale is the sign problem; the field law has its sharp
threshold (ES7) and its unconditional energy form (ES16).

A contribution must:

1. be an unconditional Lean theorem about an object of §3;
2. name which of the four quantities (energy, field, self-energy, pairing) it concerns and on which
   carrier (divisor or circle);
3. keep identities (equilibrium, virial, adjunction) apart from signs (stability);
4. state whether it is computed, bounded or posited, and whether it detects or excludes;
5. state its behaviour on reflection-closed finite configurations, on the circle, on curves over
   `𝔽_q`, and on the battery (fakes, twins, multi-pair configurations);
6. record the positive survivor of every no-go.

Calibration: transverse equilibrium of critical configurations; the quantum of a reflection pair;
`W = D − Δ`; the Hecke law of torsion orbits; Selberg's identity; Fekete's bound; the Farey
potential of `ψ`; Weil for curves.

Principles: equilibrium is computed, stability is the sign; renormalize by the degree; the
divergence sits at the arithmetic point; a detection is not an exclusion; a quantized quantity
selects for free; identities first, sign last; a reformulation is not a reduction.

---

## 11. Modules

| Module | Content |
|---|---|
| `TheVirialLawsOfAFiniteConfiguration` | Newton, Stieltjes and transverse virial; transverse and vertical energy |
| `TransverseEquilibriumIsTheCriticalLine` | reflection-closed configurations; equilibrium, work, quanta, gap, maximum principle |
| `TheTransverseEnergyOfTheZeroDivisor` | energy of the divisor; vanishing, gap, finiteness, work = energy |
| `ReflectedTransverseWork` | reflected pair kernel, height damping and tapers |
| `TheSelbergWorkExhaustsTheTransverseEnergy` | damped arithmetic source work and its exhaustion of the multiplicity-weighted energy |
| `TheFieldLawHasAThreshold` | field thresholds `1` and `√(2c log γ)` |
| `TheRenormalizedSquareIsSelbergsSource` | counterterm identity, Laurent self-terms, Selberg's source and its L-series |
| `TheSelfIntersectionOfATorsionOrbit` | `I(n, n)`, local correction, Leibniz rule, cover formula, conjugation on cycles |
| `TheTorsionCountertermIsLogarithmic` | renormalized torsion pairing; upper and lower counterterm bounds |
| `TheWeilPrimeFormOnAtomsIsLogarithmic` | Schur bound and arithmetic-point lower bound for Weil's prime form on the first `N` atoms |
| `TheArithmeticPointCarriesTheDivergence` | the arithmetic point; nonnegative self-intersections; the bound at `z = 1` |
| `TheTorsionIsTheStableEquilibriumOfTheCircle` | Fekete's bound on the circle, attained by the torsion |
| `QuantizationTurnsWindowsIntoPoints` | window energies; affine invariance; gauge twists of the source |
| `TheHeckeDefectIsTheMomentOfInertia` | the equivariance defect of `D` against the transverse moment of inertia, at every scale and infinitesimally |
| `TheEnergyOfAZeroIsLogarithmic` | pair bound by the Lorentzian kernel; `E(ρ) = O(log γ)`; window energies by zero counts |
| `LargeValuesAtZeroOrdinates` | Sobolev on cells, window mean value, discrete mean value over zeros, large values, the alignment law for prime polynomials |
| `TheStabilityLawAtAtomicResolution` | Lévy gain of disjoint shifts; atomic tests; exact prime sum; the stability law below a power of the spacing |
| `TheGaugeMarginOfTheRenormalizedSource` | margins of the source against sign twins on every window; L-series margin |
| `TheExternalFieldIsAPrimeSum` | the external field as Coulomb sum and prime sum; anti-alignment at zero ordinates; escape as infinite energy |
| `PowerMapsAreSimilitudesOfTheAbelEnergy` | closed form and positivity of torsion Abel energies; power maps as similitudes; renormalized limit; adjunction for full torsion |
