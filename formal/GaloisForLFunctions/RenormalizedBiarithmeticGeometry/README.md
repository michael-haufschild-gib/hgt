# Renormalized Biarithmetic Geometry (RBG)

**One question.** Over `𝔽_q`, Weil's proof of the Riemann hypothesis for a curve uses one pairing on
`C × C` that is at once *positive* (Hodge index, ample `Θ`), *Frobenius-equivariant* (the graph of
Frobenius is a correspondence), *pinned to the arithmetic point* (Lefschetz counts actual
`𝔽_{q^n}`-points) and *finite on the diagonal* (`Δ·Δ = 2 − 2g`). Over `ℤ` the corpus has proved that
these four properties live on four different objects. Which mechanism glues them back — which
renormalization of the diagonal keeps positivity through the scale limit, which coupling of `+1` and
`×p` pins the arithmetic point, which non-scaling invariant makes amplification lossless, and which
local geometry replaces the global extremum Weil never needed?

RBG is the geometry of the **renormalized coupled triple**

```
( positive 2D trace / torsion orbit ,  1D scale boundary ,  log-cell successor connection )
```

and of the divergences that separate its components. Its organizing sentence:

> *Over `ℤ`, positivity and scale equivariance separate only at divergent self-energies, and
> multiplicative data see the arithmetic point only through the successor. Positivity passes a scale
> limit exactly on the null cone of the counterterm; a theorem of the field must say which cone that
> is, and must carry `(+1, ×p)` holonomy before it claims selectivity.*

Namespace `GaloisForLFunctions.RenormalizedBiarithmeticGeometry`; umbrella
`RenormalizedBiarithmeticGeometry.lean`. Everything is unconditional; RH and its partial forms
appear only inside equivalences.

---

## 1. Place in the research

All routes of the corpus (critical arithmetic cancellation, complete signed positivity, faithful
realization) end at one question: what forces the functional-equation reflection `ρ ↦ 1 − ρ` and
complex conjugation `ρ ↦ ρ̄` to agree on every zero, `δ_ρ = Re ρ − ½ = 0`. The exhaustion laws of the
walls ledger are projections of one **fission** of Weil's pairing:

| Weil over `𝔽_q` | Over `ℤ` (owning programme) | Where the pieces separate |
|---|---|---|
| positivity and equivariance in one form | collided form `D` (positive; Hecke-invariant iff RH) vs reflection form `W` (Hecke-invariant; positive iff RH); `Re W = D − Δ` (APol, CDG) | the symmetric Hecke defect `E_f(L) = D(T_L f) + D(T_{−L} f) − 2D(f)` |
| finite self-intersection `2 − 2g` | positive torsion energy `T_r` (AET) and archimedean crossing forms (BGG) become scale-equivariant only after a divergent counterterm | the counterterm and its null cone |
| Frobenius localizes and commutes | boosts (Hecke), unipotent (successor), elliptic `σ_γ` (APol, ACP) | conductor horizon vs forcing threshold (CDG) |
| pinned arithmetic base | multiplicative forms are blind on the gauge torus `Ω_𝒫` (BGG); global `Aff(ℚ)` states split on the Kakutani wall (APD) | `(+1, ×p)` coupling survives only on finite horizons, cells and escape limits |

RBG takes these as its starting theorems and studies the objects in which the pieces are coupled.

| Programme | What RBG takes | What RBG adds |
|---|---|---|
| [ConjugateDiagonalGeometry](../ConjugateDiagonalGeometry/README.md), [ArithmeticPolarization](../ArithmeticPolarization/README.md) | `D`, `W`, `Δ`, `E_f(L)`, depth kernel, two-scale rigidity, finite integer theta readings, RH ⇔ Hecke invariance of `D` | dyadic amplification with fixed loss, the Hecke moment problem, lossless source-side transfer, RH as a growth rate |
| [ArithmeticEffectivityTheory](../ArithmeticEffectivityTheory/README.md) | torsion orbits, `I(m, n)`, the Abel energy `T_r`, Weil's prime kernel as a renormalized torsion energy | survival law; the torsion counterterm is full rank under every scheme and the renormalized limit is indefinite |
| [BiarithmeticGaugeGeometry](../BiarithmeticGaugeGeometry/README.md) | gauge torus, successor connection, polar-neutral collapse, log-cells, positive deformations, central ceilings | gauge charge = square class; cells fix the gauge (also on finite horizons); positivity is irreversible |
| [ArithmeticCorrespondencePositivity](../ArithmeticCorrespondencePositivity/README.md) | quadratic terminals, outward rays, pair-sum formula for `Re ξ′/ξ` | critical discs, the Carathéodory region, the terminal lens |
| [ArithmeticPositiveDuality](../ArithmeticPositiveDuality/README.md) | Kakutani wall, successor blindness of atomic spectra | the finite-horizon side of the interior–boundary duality |
| [MultiplicativePositivityGeometry](../MultiplicativePositivityGeometry/README.md) | multi-frequency purchase cap `a(γ) ≤ 2a(0)` | calibration of collective packets |
| [SelectivePositivityAndThresholdLaws](../SelectivePositivityAndThresholdLaws/README.md) | selectivity battery on `[−181/500, 181/500]`, parity lobes, escaped pairings | battery targets |
| [ArithmeticCastelnuovoSeveri](../ArithmeticCastelnuovoSeveri/README.md), [ArithmeticOrientationGeometry](../ArithmeticOrientationGeometry/README.md) | scaling surface, Hodge index, short-cycle reduction, orbit rates, `𝔽_q` calibration | the renormalized reading of `Δ² = 2 − 2g` |
| [ArithmeticElectrostatics](../ArithmeticElectrostatics/README.md) | potential of `log|ξ|`, torsion self-energies and counterterm rates | the survival criterion under which counterterms are compared |
| [SignedSuccessorArithmetic](../SignedSuccessorArithmetic/README.md), [ArithmeticCorrelationGeometry](../ArithmeticCorrelationGeometry/README.md) | successor sign calculus, stabilizer decompositions | gauge charge of a coupling |

RBG does not re-prove what these programmes own; it imports them and proves the laws that couple
them.

---

## 2. Why

**One pairing, four properties.** On `C × C` the intersection pairing is positive by Hodge index, the
Frobenius graph is a correspondence, Lefschetz counts actual points, and the diagonal has finite
self-intersection. Hasse–Weil uses all four at once; the fourth is what makes the tensor-power
argument lossless (the loss `2g` does not grow with the power).

**Each word of the name is forced by a theorem.**

* *Biarithmetic.* Purely multiplicative data determine a source only up to its orbit under the prime
  gauge torus `Ω_𝒫 = ∏_p S¹`. At the real gauge `−1` they cannot tell `ζ` from Liouville's
  `ζ(2s)/ζ(s)`, which has poles on the critical line. RBG proves the exact form: a coupling is blind
  iff it is of square class, and a positivity criterion built from square-class couplings holds for
  `Λ` iff it holds for `λΛ`. The successor is always charged, and on log-cells the dilation itself
  fixes the gauge. The arithmetic point lives in the coupling of `+1` and `×p`.
* *Renormalized.* Both places of the explicit formula are Abel-regularized self-energies with the
  same universal divergence `−log(1 − r)`: the torsion energy of the prime place and the lattice
  germ of the archimedean place. Positivity lives before the limit, equivariance after it. RBG proves
  that positivity passes the limit exactly on the null cone of the counterterm, that this cone does
  not depend on the renormalization scheme, and that it is `{0}` for the prime place and a
  hyperplane for the archimedean place.
* *Geometry.* Sign, depth and multiplicity of zeros are read by intersection forms, moment problems,
  connections and holonomy, discs and cones — not by norm inequalities on one vertical line.

**Why existing disciplines do not supply the gluing.** Analytic number theory works with unsigned
norms on vertical lines and stalls at the square-root threshold (SRT, SPTL). Arakelov geometry has no
surface `Spec ℤ × Spec ℤ`, and the base theta count does not extend (AET). Operator algebras on
`Aff(ℚ)` meet the Kakutani wall; Meyer's origin space makes continuous class invariants constant
(ACS). Bochner–Weil and Pólya–Schur positivity are blind to interior zeros and chirally soft (MPG,
BGG).

**What RBG found.**

1. *The counterterm rank dichotomy.* The prime-side torsion germ has counterterm `I`; under every
   renormalization nothing survives and the renormalized limit (Weil's prime kernel with the
   log-discriminant diagonal) is indefinite at every prime power. The archimedean lattice germ has
   counterterm `𝟙𝟙ᵀ`; the polar-neutral hyperplane survives and there the digamma Hankel form is
   positive. Adjoining the pole node — the order-one torsion orbit, the arithmetic point — completes
   the archimedean germ to a positive kernel on all vectors.
2. *Lossless amplification.* The collided mass `D(f)` is a non-scaling invariant: dyadic Hecke
   amplification `E(2^k L) ≥ D(2cosh(2^k θ) − 2)` has loss exactly `D(f)`, independent of `k`. One
   upper bound at a large dyadic scale bounds every smaller scale, finite integer theta prefixes
   supply such readings, and RH is equivalent to sub-doubly-exponential dyadic growth.
3. *Gauge fixing by cells.* Lattice dilation is covariant at every gauge; dyadic cell dilation is
   covariant only at the Euler point, and on the horizon `[1, X]` it pins every prime up to `2X + 1`.
4. *Terminal geometry.* A reflected zero pair pulls `Re ξ′/ξ` negative exactly inside its critical
   disc; terminals are the zeros outside every disc, and each terminal carries a zero-free lens on
   which `Re ξ′/ξ ≥ 0`.
5. *Chirality.* Positive deformations form a monoid without nontrivial units.

---

## 3. Objects and language

### 3.1 Primitive objects

| Object | Definition | Lean |
|---|---|---|
| Split-polarized scaling space | test space with collided trace `D ≥ 0`, reflection trace `W`, `Δ = D − Re W`, translations `T_L`, Hecke defect `E_f(L)` | CDG `heckeDefect`, `depthKernel`; APol `collidedForm` |
| Regularized family, counterterm, survival cone | forms `Q_r` with `Q_r − s_r B → A`, `s_r → ∞`; the cone `{x : B(x, x) = 0}` | `quad`, `survivalCone` |
| Torsion germ (prime place) | gcd-twisted Abel energy of primitive roots of unity | `torsionGerm`, `torsionLimit`, `torsionLimitForm` |
| Lattice germ (archimedean place) | `G_r(z) = Σ_{k≥0} r^k/(k + z)`, Hankel family `G_r(x_i + x_j)` | `latticeGerm`, `latticeHankel`, `latticeCounterterm`, `latticeGermLimit` |
| Pole node | the node `x = 0` of the shifted germ, the order-one torsion orbit | `harmonicFn`, `harmonicKernel_nonneg` |
| Depth moments | `m_j(L) = Σ_ρ w_ρ k_ρ^j`, `k_ρ = 2cosh(2δ_ρ L) − 2` | `depthMoment`, `hankelForm`, `seenLevels` |
| Amplification map | `a_D(e) = 4e + e²/D` | `amplify`, `mass` |
| Integer theta reading | CDG's finite-prefix reading of `m_j(L)` | `reading` |
| Prime-gauge bundle | `Ω_𝒫`, `χ_ω`, `U_ω`, successor connection | BGG `PrimeGauge`, `gaugeTwist`, `succConn` |
| Coupling and its charge | source value `F(n)` coupling modes `a, b`; blind iff `nab` is a square | `sourceKernel`, `sourceForm`, `flipGauge` |
| Cell complex | `I_n = [log n, log(n+1))`; cell dilation `M_m`, lattice dilation `D_m`, successor `S` | `cellDilate`, `latticeDilate`, `succShift`, `SupportedOn` |
| Critical disc | `{s : |s − (½ + iγ_ρ)| < |δ_ρ|}` | `InCriticalDisc` |
| Terminal and lens | right zero outside every critical disc; region right of the two radius-`½` circles through it | `IsTerminal`, `InTerminalLens`, `lensWidth` |
| Positive deformation | `Λ₀′/Λ₀ − Λ′/Λ` is the Laplace transform of a measure on a ray | `PositiveDeformation` |

### 3.2 Twelve distinctions

Conflating any of these is a type error.

| Distinction | Consequence |
|---|---|
| Collided `D` / reflected `W` | `ρ ↔ ρ̄` versus `ρ ↔ 1 − ρ̄`; each property holds without the other |
| Even / odd collision | even couplings are blind to `H¹` determinant signs; odd counts see the complex quartet |
| Inserted pole charge / intrinsic oscillatory charge | pole order under deformation versus zero-sum oscillation |
| Hyperbolic / elliptic / unipotent | boost-invariant positive cones are isotropic; only `σ_γ` localizes; `+1` is a Hardy perturbation |
| Square-class / charged coupling | square class is gauge-blind; successor and cell couplings are charged |
| Lattice / cell dilation | lattice dilation is covariant at every gauge, cell dilation only at the Euler point |
| Atomic / continuous dilation spectrum | atomic spectra blind every successor |
| Soft / fibre-selective polarization | fibre-constant theta metrics versus `thetaBoxH0/H1` |
| Outward / inward surgery | positive deformations are irreversible |
| Scalar / low-rank counterterm | scalar counterterms leave no positivity; rank `k` leaves codimension `k` |
| Pointwise / dyadic-growth bound | a bound at one large dyadic scale controls all smaller scales |
| Parity-blind / parity-sensitive dispersion | parity-blind dispersion diverges above the square-root threshold |

### 3.3 Words

*Regularized family*: forms indexed by a regulator. *Counterterm*: the divergent part `s_r B`.
*Survival cone*: the null cone of the counterterm. *Polar-neutral*: in the null cone of a rank-one
polar counterterm. *Pole node*: the node carrying the polar mode. *Effective angle*: `θ` with
`E(L) = D(2cosh θ − 2)`. *Seen level*: a depth level `k_ρ` with `w_ρ ≠ 0`. *Charged*: not covariant
under some real sign gauge. *Gauge-fixing*: covariant only at `𝟏 ∈ Ω_𝒫`. *Terminal*: a right zero
outside every critical disc. *Lens*: the zero-free sector of a terminal.

---

## 4. Mechanisms

1. **Survival of positivity** (`TheRenormalizationSurvivalLaw`). If `Q_r ⪰ 0` and `Q_r − s_r B → A`,
   then `A ≥ 0` on the survival cone of `B` (`quad_nonneg_of_regularized`), and `B ⪰ 0` when
   `s_r → ∞` (`counterterm_nonneg`). Two renormalizations of one family have proportional
   counterterms (`counterterm_eq_smul`), so the survival cone is scheme independent
   (`survivalCone_eq_of_regularized`). Conversely (Finsler–Debreu, `exists_quad_add_smul_pos`), if
   `B ⪰ 0` and `A` is positive on the nonzero null vectors of `B`, then `A + sB ≻ 0` for large `s`;
   hence `A ≥ 0` on the cone iff `A + sB + εI` is eventually positive for every `ε`
   (`quad_nonneg_on_survivalCone_iff`). The identity has survival cone `{0}` (`survivalCone_one`) and
   realizes every form as a renormalized limit of positive forms (`regularized_one_realizes`); a
   rank-one counterterm `v vᵀ` has the hyperplane `⟪v, x⟫ = 0` (`mem_survivalCone_vecMulVec_iff`).
2. **The archimedean germ** (`TheArchimedeanGermSurvivesOnItsPolarHyperplane`). Each Abel level of
   `G_r(x_i + x_j)` is a Cauchy form, so the Hankel family is positive (`latticeGerm_hankel_nonneg`).
   Splitting off `Σ r^k/(k + 1) = −log(1 − r)/r` and applying Tannery's theorem gives
   `G_r(z) + log(1 − r) → −ψ(z) − γ` (`tendsto_latticeGerm_add_log`, `latticeGermLimit_eq`). The
   counterterm is `𝟙𝟙ᵀ` (`latticeHankel_regularized`), so `Σ c_i c_j (−ψ(x_i + x_j)) ≥ 0` on `Σc = 0`
   (`neg_digamma_hankel_nonneg`); off the hyperplane the limit at `z = 2` is `−1`
   (`not_nonneg_latticeGermLimit`).
3. **The torsion germ and the dichotomy** (`TheCountertermRankDichotomy`). AET's twisted torsion
   energy is a regularized family with the identity as counterterm (`torsionGerm_regularized`); by
   scheme independence every renormalization of it has survival cone `{0}`
   (`torsion_survivalCone_eq`). Its limit couples the orbit of order `1` (zero self-intersection) to
   the orbit of order `q` with weight `Λ(q)/√q > 0`, so it is negative along `(1, t)` for small `t`
   (`torsionLimitForm_neg`). Every renormalization of the lattice germ has the polar-neutral
   hyperplane as survival cone (`lattice_survivalCone_eq`). The conjunction is
   `counterterm_rank_dichotomy`.
4. **The pole node** (`ThePoleNodeCompletesTheArchimedeanGerm`). Spending the hyperplane constraint
   on the node `x = 0` — the order-one torsion orbit, whose self-energy is the archimedean divergence
   — turns conditional positivity into positivity of `H(x) + H(y) − H(x + y)`, `H = ψ(1 + ·) + γ`
   (`harmonicKernel_nonneg`). This is the matched cancellation between the two germs.
5. **Dyadic amplification** (`TheDyadicAmplificationOfTheHeckeDefect`). Two-scale rigidity reads
   `E(2L) ≥ a_D(E(L))` (`amplify_heckeDefect_le`), and `a_D` doubles the angle
   (`amplify_cosh`, `iterate_amplify_cosh`). Hence `E(2^k L) ≥ D(2cosh(2^k θ) − 2)` whenever
   `E(L) ≥ D(2cosh θ − 2)` (`heckeDefect_dyadic_ge`), with the strip bound as ceiling
   (`heckeDefect_dyadic_sandwich`); an upper bound at one dyadic scale transfers to the base scale
   (`heckeDefect_le_of_dyadic_le`); sub-doubly-exponential growth forces `E(L) = 0`
   (`heckeDefect_eq_zero_of_dyadic_subexp`); and RH holds iff every test has sub-doubly-exponential
   dyadic growth (`riemannHypothesis_iff_dyadic_subexp`).
6. **The Hecke moment problem** (`TheHeckeMomentProblem`). `m_0 = D`, `m_1 = E(L)`,
   `m_2 = E(2L) − 4E(L)`. Every shifted Hankel form is a trace `Σ_ρ w_ρ k_ρ^s P_c(k_ρ)²`
   (`hankelForm_eq_tsum`, `hankelForm_nonneg`); its null vectors are the polynomials vanishing on
   the seen levels (`hankelForm_eq_zero_iff`); a null vector of size `n` forces fewer than `n` seen
   levels (`ncard_seenLevels_lt_of_hankel_null`); the moments are log-convex (`depthMoment_sq_le`).
7. **Integer theta prefixes** (`IntegerThetaPrefixesReadTheDefectWithoutLoss`). Finite prefixes read
   the moments, the mass, the defect and every Hankel form (`reading_depthMoment`, `reading_mass`,
   `reading_heckeDefect`, `reading_hankelForm`). One pair of readings at a single dyadic scale bounds
   the defect at the base scale (`heckeDefect_le_of_readings`), and depth is always visible in the
   readings (`reading_ge_of_heckeDefect_ge`).
8. **Gauge charge** (`TheGaugeChargeOfACoupling`). A coupling `(n; a, b)` is blind under every real
   sign gauge iff `nab` is a square (`realSignBlind_iff_isSquare`, via prime-flip gauges and
   `isSquare_iff_even_factorization`); kernels transform by conjugation iff their support is of
   square class (`sourceKernel_twist_iff`); for such kernels the twist is the sign change of the
   modes, so positivity for `Λ` and for `λΛ` coincide (`sourceForm_nonneg_twist_iff`). Diagonal,
   ratio and product couplings are square class; successor couplings never are
   (`successor_coupling_charged`).
9. **Cells fix the gauge** (`LogCellsFixTheGauge`). Cell and lattice dilation both satisfy the
   Baumslag–Solitar relation `M_m S = S^m M_m` (`cellDilate_succShift`, `latticeDilate_succShift`);
   cell dilation is lattice dilation spread over the successor orbit (`cellDilate_eq_sum_succShift`).
   Lattice dilation is covariant at every gauge (`gaugeTwist_latticeDilate`); dyadic cell dilation
   only at the Euler gauge (`cellDilate_two_covariant_iff`), and on the horizon `[1, X]`, `X ≥ 4`,
   exactly when every prime `≤ 2X + 1` has phase `1` (`cellDilate_two_covariant_on_horizon_iff`).
10. **Critical discs and the lens** (`CriticalDiscsAndTheTerminalLens`). The pair contribution has the
    sign of `x(x² + (y − γ)² − b²)` (`xiLinePairRe_nonneg_of_not_inCriticalDisc`,
    `xiLinePairRe_neg_of_inCriticalDisc`); off all discs `Re ξ′/ξ ≥ 0`
    (`re_logDeriv_xi_nonneg_of_outside_discs`); terminals are the zeros outside every disc
    (`isTerminal_iff_outside_discs`); the lens of a terminal lies outside every disc
    (`outside_discs_of_mem_terminalLens`), is zero-free off `p` (`xi_ne_zero_of_mem_terminalLens`),
    carries `Re ξ′/ξ ≥ 0` (`re_logDeriv_xi_nonneg_of_mem_terminalLens`) and contains the outward ray
    (`mem_terminalLens_of_ray`).
11. **Irreversibility** (`PositivityIsIrreversible`). Positive deformations compose
    (`PositiveDeformation.trans`); mutual positive deformations have equal logarithmic derivatives on
    a ray (`PositiveDeformation.antisymm`); a nontrivial one cannot be undone
    (`not_positiveDeformation_of_ne`).

---

## 5. Pillar theorems: the eight laws

| Law | Statement | Lean |
|---|---|---|
| I. Split polarization and lossless amplification | `Re W = D − Δ`; `E(L)² ≤ D(E(2L) − 4E(L))`; dyadic amplification with loss `D`; RH ⇔ sub-doubly-exponential dyadic growth; Hankel positivity and shell rigidity of the depth moments | CDG, APol; `heckeDefect_dyadic_ge`, `heckeDefect_le_of_dyadic_le`, `riemannHypothesis_iff_dyadic_subexp`, `hankelForm_nonneg`, `ncard_seenLevels_lt_of_hankel_null` |
| II. Local trichotomy | reflection-commuting affine actions are boosts, unipotent or elliptic | APol `TheEllipticLocalizers`, ACP |
| III. Gauge blindness = square class | blind ⇔ `nab` square; square-class criteria accept `Λ` iff `λΛ`; successor charged | `realSignBlind_iff_isSquare`, `sourceForm_nonneg_twist_iff`, `successor_coupling_charged` |
| IV. Interior–boundary duality | global states decouple `+1` and `×p` (APD); cells couple them and fix the gauge, with reach `2X + 1` on horizon `X` | APD; `cellDilate_two_covariant_iff`, `cellDilate_two_covariant_on_horizon_iff` |
| V. Self-energy survival | positivity passes a scale limit exactly on the survival cone, independent of scheme; prime place: `{0}`, indefinite limit; archimedean place: polar-neutral hyperplane; pole node completes it | `quad_nonneg_on_survivalCone_iff`, `survivalCone_eq_of_regularized`, `counterterm_rank_dichotomy`, `harmonicKernel_nonneg` |
| VI. Chirality and quantization | positive deformations form a monoid with trivial units; central excess quantized in `2ℕ` | `PositiveDeformation.antisymm`, `not_positiveDeformation_of_ne`; BGG G19 |
| VII. Surface effectivity vs base non-extension | Hodge index ⇔ Serre-dual real effectivity with quadratic growth; the base theta count does not extend | AET |
| VIII. Terminal replacement of extrema | every off-line zero ascends to a terminal; terminals = zeros outside every critical disc; each carries a zero-free lens with `Re ξ′/ξ ≥ 0` | ACP; `isTerminal_iff_outside_discs`, `xi_ne_zero_of_mem_terminalLens`, `re_logDeriv_xi_nonneg_of_mem_terminalLens` |

---

## 6. The seven questions and their answers

1. **Split polarization.** *What bounds `E_f(L)` without a fibred product?* Self-amplification. The
   defect cannot grow slower than `D(2cosh(2^k θ) − 2)` once it is positive, so a bound at one large
   dyadic scale bounds it at every smaller scale with no loss, and finite integer theta prefixes
   supply such a bound as a finite computation (`heckeDefect_le_of_readings`). RH is exactly
   sub-doubly-exponential dyadic growth. The full information is the Hecke moment problem, whose
   Hankel forms are read from integer prefixes. What remains is an arithmetic upper bound for the
   readings at one scale `L ≍ log n`.
2. **Matched self-energy.** *How does one cancel `−log(1 − r)` inside the positive cone?* Exactly on
   the survival cone of the counterterm, a scheme-independent invariant. For the prime place the
   cone is `{0}` and the limit is indefinite: no renormalization of the torsion germ alone keeps
   positivity. For the archimedean place the cone is the polar-neutral hyperplane, and the pole node
   — the order-one torsion orbit — cancels the polar divergence and completes the archimedean germ to
   a positive kernel. Matching higher torsion orbits requires a twin whose counterterm has the same
   Cesàro statistics; none is supplied by the lattice germ.
3. **Finite-horizon holonomy.** *How much `(+1, ×p)` curvature survives?* On lattice profiles none:
   lattice dilation is covariant at every gauge. On cell profiles all of it: dyadic cell dilation is
   covariant only at the Euler point, and on the horizon `[1, X]` it detects every prime up to
   `2X + 1`. Every successor coupling is charged.
4. **Chiral moduli.** *What is the geometry of one-way positive deformations?* A monoid without
   nontrivial units: positivity orders deformations and cannot be undone. With BGG's Landau–Wronskian
   principle a positive deformation can only lower the order at its abscissa, and the central excess
   is quantized.
5. **Zero-cone potential.** *How do `F(p) = 0` and an empty cone constrain the outward ray?* The empty
   cone of a terminal is the statement that `p` lies outside every critical disc. That condition
   extends from the ray to a two-dimensional lens bounded by two circles of radius `½` through `p`;
   the lens is zero-free and `Re ξ′/ξ ≥ 0` on it. Upper bounds on the outward growth (the terminal
   ceiling problem) remain open.
6. **Fibre-selective real effectivity.** *Which functionals can select `ζ` against prime-gauge
   twins?* None built from square-class couplings: such a functional is positive at `Λ` iff at `λΛ`.
   Selectivity requires charged couplings — successor links or cells. Serre duality and quadratic
   growth of `h⁰` are AET's.
7. **Fixed-loss amplification.** *What non-scaling invariant breaks depth homogeneity?* The collided
   mass `D(f)`: dyadic Hecke amplification has loss exactly `D(f)`, independent of the number of
   doublings.

---

## 7. Traps

| Trap | Truth |
|---|---|
| Positivity of `T_r` for `r < 1` bounds Weil's prime form | The torsion counterterm is the identity; every form is a renormalized limit of positive forms with scalar counterterm (`regularized_one_realizes`) |
| A better renormalization scheme for the torsion germ keeps positivity | The survival cone is scheme independent and equal to `{0}` (`torsion_survivalCone_eq`) |
| Subtracting `−log(1 − r) I` leaves something positive | The limit is negative along `(1, t)` on `{1, q}` (`torsionLimitForm_neg`) |
| The archimedean place is positive | Only on the polar-neutral hyperplane; at `z = 2` the limit is `−1` |
| A cleverer multiplicative weight separates `ζ` from Liouville | Square-class criteria accept `Λ` iff `λΛ` (`sourceForm_nonneg_twist_iff`) |
| Discretizing to `log n` loses nothing | Lattice dilation is blind; only cell dilation fixes the gauge |
| Two-scale rigidity is one inequality | It iterates to every dyadic scale with fixed loss |
| Dyadic amplification is selective | It holds on every positive depth configuration; its content is the transfer of a source bound |
| The terminal ray is special | It lies in a two-dimensional zero-free lens |
| Positive deformations can be undone | Units are trivial |
| Collective packets amortize pole cost | A positive multi-frequency certificate purchases at most twice the pole share per frequency (MPG `multiFrequency_purchase_le_two`) |

---

## 8. Tools

**Imported**: collided and reflection forms, Hecke defect and depth kernel, finite integer theta
readings (CDG, APol); torsion orbit intersections and the Abel torsion energy (AET); gauge torus,
successor connection, Landau–Wronskian deformations (BGG); terminals, outward rays and the pair-sum
formula for `Re ξ′/ξ` (ACP, RHTower); Gauss series for digamma and the Cauchy kernel (HTGeometry,
RHTower).

**Built in RBG**: the survival law with scheme independence and the Finsler–Debreu converse; the
lattice germ and its digamma limit; counterterm rank of both places; pole-node completion; dyadic
amplification and the effective angle; the Hecke moment problem; integer-prefix transfer; gauge
charge of couplings and the square-class criterion; cell and lattice dilation with finite-horizon
gauge fixing; critical discs, the Carathéodory region and the terminal lens; the positive
deformation monoid.

**To build**: a twin for higher torsion orbits; arithmetic upper bounds for prefix readings at one
dyadic scale; Harnack and harmonic-measure estimates on the lens; quantitative cell holonomy at the
Liouville gauge; Kronecker dilution of collective packets over independent ordinates; Wiener escape
modules as boundary objects.

---

## 9. Open research topics

1. **Twins for higher torsion orbits.** A positive germ whose Cesàro statistics against the
   Ramanujan modes `c_n` (`n ≥ 2`) match those of the torsion germ, so that the joint counterterm has
   a null cone meeting the short-cycle differences `g − T_{2^m} g`.
2. **One-scale arithmetic bounds.** An upper bound for `R_n(f, 2^k L, 1)` at `2^k L ≍ log n` from
   integer arithmetic; by lossless transfer it bounds `E_f(L)`. Any bound `E ≪ e^{2ϑ L} D` at one
   scale gives zero-density control.
3. **Harmonic measure on the lens.** Harnack inequalities for `Re ξ′/ξ` on the lens, compared with
   the outward floor of ACP, toward the terminal ceiling problem.
4. **Quantitative cell holonomy.** Lower bounds for the gauge defect of cell correlations at the
   Liouville gauge for smooth short-cycle profiles.
5. **Collective packets.** Whether commensurable companion clouds can beat the per-frequency cap
   collectively, and the exact dilution over independent ordinates.
6. **Escape modules.** Contractive `𝒲_{1/2}`-modules of damped limits as the boundary objects where
   `(+1, ×p)` coupling survives.

---

## 10. Success criteria and contribution standards

RBG succeeds when it proves, for a coupled object, a positivity that survives the scale limit and
passes the battery, or proves that no object of a stated class can, together with the strongest
positive survivor. The prime-place no-go (`torsion_survivalCone_eq`) with its survivor (pole-node
completion) and the gauge no-go (`sourceForm_nonneg_twist_iff`) with its survivor (cells fix the
gauge) are the models.

**The ten-point battery.** A candidate invariant must state its behaviour on: (1) curves over `𝔽_q`
with genus cost `2g`; (2) the golden datum `1 − 5X + 5X²`; (3) the complex quartet
`X⁴ + 68X² + 256`; (4) pole-budget-2 refunds; (5) outward splittings `W_β` and Maass cofactors; (6)
the Liouville twin `λΛ`; (7) the shifted pair `ζ(s − a)ζ(s + a)`; (8) prime-power nodes; (9) interior
zeros `ζ(s)/ζ(s + 1 − β)`; (10) trans-threshold parity (`λ > 1`).

**A contribution** is an unconditional Lean theorem about constructed objects, wired into the
umbrella. It names its counterterm and survival cone, its gauge charge (square class or charged),
its local type and its scale range; it separates identities (true on every positive configuration)
from estimates (which select `ζ`); and every negative result records its positive survivor. Comments
state mathematics only.

---

## Module architecture

- [`TheRenormalizationSurvivalLaw.lean`](TheRenormalizationSurvivalLaw.lean) — regularized families, survival cones, scheme independence, Finsler–Debreu, scalar and rank-one counterterms.
- [`TheArchimedeanGermSurvivesOnItsPolarHyperplane.lean`](TheArchimedeanGermSurvivesOnItsPolarHyperplane.lean) — the lattice germ, its digamma limit, survival on `Σc = 0`.
- [`TheCountertermRankDichotomy.lean`](TheCountertermRankDichotomy.lean) — the torsion germ as a regularized family; full rank versus rank one.
- [`ThePoleNodeCompletesTheArchimedeanGerm.lean`](ThePoleNodeCompletesTheArchimedeanGerm.lean) — the harmonic-number kernel.
- [`TheDyadicAmplificationOfTheHeckeDefect.lean`](TheDyadicAmplificationOfTheHeckeDefect.lean) — amplification map, lossless transfer, RH as a growth rate.
- [`TheHeckeMomentProblem.lean`](TheHeckeMomentProblem.lean) — depth moments, Hankel positivity, shell rigidity, log-convexity.
- [`IntegerThetaPrefixesReadTheDefectWithoutLoss.lean`](IntegerThetaPrefixesReadTheDefectWithoutLoss.lean) — finite readings of the moment problem and source-side transfer.
- [`TheGaugeChargeOfACoupling.lean`](TheGaugeChargeOfACoupling.lean) — square-class classification, Liouville blindness of square-class criteria, charged successor.
- [`LogCellsFixTheGauge.lean`](LogCellsFixTheGauge.lean) — cell and lattice dilation, Baumslag–Solitar, gauge fixing, finite horizons.
- [`CriticalDiscsAndTheTerminalLens.lean`](CriticalDiscsAndTheTerminalLens.lean) — pair sign law, Carathéodory region, terminals, the lens.
- [`PositivityIsIrreversible.lean`](PositivityIsIrreversible.lean) — the positive deformation monoid.
