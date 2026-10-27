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

1. *The survival cone is the module of relations.* For a periodic Abel germ — modes `a_α`, nodes
   `x_α` — the counterterm is the Cesàro Gram of the modes, and positivity survives the scale limit
   exactly on the linear relations among the modes. The archimedean germ has all modes equal to `1`:
   its relations are the polar hyperplane, where the digamma Hankel form is positive. The torsion
   germ has the identity as counterterm: under every renormalization nothing survives, and the
   renormalized limit (Weil's prime kernel with the log-discriminant diagonal) is indefinite at
   every prime power.
   Adjoining the pole node — the order-one torsion orbit, the arithmetic point — completes the
   archimedean germ to a positive kernel on all vectors. Ramanujan modes of different orders are
   orthogonal, so a twin that places torsion orbits at several nodes survives exactly on the
   relations summing to zero over each order, and pure torsion keeps nothing. The twin's pole-node
   block is the torsion energy itself, so its renormalized limit carries the primes: the entry at
   pole nodes of orders `m` and `mt` is `−φ(m)Λ(t)`.
2. *Lossless amplification.* The collided mass `D(f)` is a non-scaling invariant: dyadic Hecke
   amplification `E(2^k L) ≥ D(2cosh(2^k θ) − 2)` has loss exactly `D(f)`, independent of `k`. One
   upper bound at a large dyadic scale bounds every smaller scale, finite integer theta prefixes
   supply such readings, and RH is equivalent to sub-doubly-exponential dyadic growth.
3. *Gauge fixing by cells.* Lattice dilation is covariant at every gauge; dyadic cell dilation is
   covariant only at the Euler point, and on the horizon `[1, X]` it pins every prime up to `2X + 1`.
   Quantitatively, the covariance defect counts charged cells: at the Liouville gauge it lies
   between `2N₊` and `4N₊`, `N₊ = #{a ≤ X : λ(a) = λ(2a + 1)}` — a correlation of `λ` along
   `(+1, ×2)`.
4. *Terminal geometry.* A reflected zero pair pulls `Re ξ′/ξ` negative exactly inside its critical
   disc; terminals are the zeros outside every disc, and each terminal carries a zero-free lens on
   which `Re ξ′/ξ ≥ 0`. Harnack's inequality holds for `Re ξ′/ξ` on every disc strictly outside the
   critical discs, so the outward floor of a terminal spreads to two-dimensional discs.
5. *Chirality.* Positive deformations form a monoid without nontrivial units.
6. *Dilution and height.* A positive packet on `ℚ`-independent ordinates buys in total at most its
   pole share; on harmonic progressions of length `≤ M` along independent generators it buys at
   most `M` times the pole share, and one progression attains it. Collective amortization is
   measured by the arithmetic of the cloud, not by its size.
7. *Soft versus selective.* Dyadic amplification holds on every positive depth configuration and is
   soft; cells and the successor are selective (they reject the Liouville twin); square-class
   criteria are blind.

---

## 3. Objects and language

### 3.1 Primitive objects

| Object | Definition | Lean |
|---|---|---|
| Split-polarized scaling space | test space with collided trace `D ≥ 0`, reflection trace `W`, `Δ = D − Re W`, translations `T_L`, Hecke defect `E_f(L)` | CDG `heckeDefect`, `depthKernel`; APol `collidedForm` |
| Regularized family, counterterm, survival cone | forms `Q_r` with `Q_r − s_r B → A`, `s_r → ∞`; the cone `{x : B(x, x) = 0}` | `quad`, `survivalCone` |
| Torsion germ (prime place) | gcd-twisted Abel energy of primitive roots of unity | `torsionGerm`, `torsionLimit`, `torsionLimitForm` |
| Lattice germ (archimedean place) | `G_r(z) = Σ_{k≥0} r^k/(k + z)`, Hankel family `G_r(x_i + x_j)` | `latticeGerm`, `latticeHankel`, `latticeCounterterm`, `latticeGermLimit` |
| Periodic germ | modes `a_α` (common period `q`), nodes `x_α`: `Σ_k r^k a_α(k)a_β(k)/(k + 1 + x_α + x_β)`; Cesàro Gram `mean(a_α a_β)` | `twistedGerm`, `periodicGerm`, `cesaroGram`, `ramanujanMode`, `twinPeriod` |
| Pole node | the node `x = 0` of the shifted germ, the order-one torsion orbit | `harmonicFn`, `harmonicKernel_nonneg` |
| Depth moments | `m_j(L) = Σ_ρ w_ρ k_ρ^j`, `k_ρ = 2cosh(2δ_ρ L) − 2` | `depthMoment`, `hankelForm`, `seenLevels` |
| Amplification map | `a_D(e) = 4e + e²/D` | `amplify`, `mass` |
| Integer theta reading | CDG's finite-prefix reading of `m_j(L)` | `reading` |
| Prime-gauge bundle | `Ω_𝒫`, `χ_ω`, `U_ω`, successor connection | BGG `PrimeGauge`, `gaugeTwist`, `succConn` |
| Coupling and its charge | source value `F(n)` coupling modes `a, b`; blind iff `nab` is a square | `sourceKernel`, `sourceForm`, `flipGauge` |
| Cell complex | `I_n = [log n, log(n+1))`; cell dilation `M_m`, lattice dilation `D_m`, successor `S` | `cellDilate`, `latticeDilate`, `succShift`, `SupportedOn` |
| Cell-holonomy defect | Hilbert–Schmidt defect of `U_ω M_2 − c M_2 U_ω` on `[1, X]`; charged cells `σ(a)σ(2a+1) ≠ σ(2)` | `hsDefect`, `chargedCells`, `liouvilleAgreements` |
| Critical disc | `{s : |s − (½ + iγ_ρ)| < |δ_ρ|}` | `InCriticalDisc` |
| Terminal and lens | right zero outside every critical disc; region right of the two radius-`½` circles through it | `IsTerminal`, `InTerminalLens`, `lensWidth` |
| Carathéodory region, ray discs | points strictly outside every closed critical disc; discs of radius `ρh` about `p + h` | `StrictlyOutsideDiscs`, `rayRadius` |
| Positive deformation | `Λ₀′/Λ₀ − Λ′/Λ` is the Laplace transform of a measure on a ray | `PositiveDeformation` |
| Positive packet | `a_0 + Σ_j a_j cos(ω_j t) ≥ 0`: pole share `a_0`, purchase `a_j` | `sum_abs_le_of_packet_nonneg`, `sum_le_height_mul_of_packet_nonneg`, `exists_harmonic_packet` |
| Depth configuration | finite weights `w_i ≥ 0` and depths `δ_i`, mass and Hecke defect | `configMass`, `configDefect` |

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
4. **Periodic germs** (`TheSurvivalConeOfAPeriodicGermIsItsModuleOfRelations`). Every level of a
   periodic germ is a Cauchy form in `C_α a_α(k)` (`periodicGerm_quad_nonneg`). For periodic `p`
   with mean `μ`, `Σ_k r^k p(k)/(k + w) + μ log(1 − r)` converges: the mean part is the lattice
   germ, the mean-zero part converges by Dirichlet's test and Abel's theorem
   (`tendsto_twistedGerm_add_mean_log`). The Cesàro Gram form is the mean square of `Σ_α C_α a_α`,
   so its null cone is the module of relations (`mem_survivalCone_cesaroGram_iff`); the renormalized
   limit is nonnegative there (`periodicGerm_survival`), and every renormalization has this survival
   cone (`periodicGerm_survivalCone_eq`). Constant modes give the polar hyperplane
   (`relations_const_iff`); Ramanujan modes repeated over nodes survive on coefficients summing to
   zero over each order (`ramanujanTwin_survival`).
5. **Ramanujan twins** (`TheRamanujanTwinsSurviveExactlyOnPerOrderRelations`). Ramanujan sums are
   real (`ramanujanSum_im`) and orthogonal over a common period:
   `Σ_{k<q} c_m(k)c_n(k) = qφ(n)δ_{mn}` (`sum_ramanujanSum_mul`, `sum_ramanujanMode_mul`), because
   `ζη = 1` forces `η = ζ⁻¹`, a primitive root of the order of `ζ`. Hence the relations among
   Ramanujan modes at nodes are exactly the per-order relations (`ramanujanRelations_iff`), every
   renormalization of the twin germ has them as survival cone (`ramanujanTwin_survivalCone_eq`), and
   with one node per order the cone is `{0}` (`ramanujan_survivalCone_eq_zero_of_injective`).
6. **The twins carry the primes** (`TheRamanujanTwinsCarryThePrimes`). With the shifted modes
   `c_n(k + 1)` the pole-node germ is the torsion energy, `T_r(m, n) = r · Σ_k r^k c_m(k+1)c_n(k+1)/(k+1)`
   (`torsionEnergy_eq_mul_twistedGerm`); its limit is `−I(m, n)` (`tendsto_twin_poleNode`). Every
   renormalized limit of the shifted twin is nonnegative on per-order relations and has entries
   `−I(ord α, ord β)` at pole nodes of different orders (`ramanujanTwin_carries_primes`), equal to
   `−φ(m)Λ(t)` at orders `m, mt` (`ramanujanTwin_poleNode_vonMangoldt`).
7. **The pole node** (`ThePoleNodeCompletesTheArchimedeanGerm`). Spending the hyperplane constraint
   on the node `x = 0` — the order-one torsion orbit, whose self-energy is the archimedean divergence
   — turns conditional positivity into positivity of `H(x) + H(y) − H(x + y)`, `H = ψ(1 + ·) + γ`
   (`harmonicKernel_nonneg`). This is the matched cancellation between the two germs.
8. **Dyadic amplification** (`TheDyadicAmplificationOfTheHeckeDefect`). Two-scale rigidity reads
   `E(2L) ≥ a_D(E(L))` (`amplify_heckeDefect_le`), and `a_D` doubles the angle
   (`amplify_cosh`, `iterate_amplify_cosh`). Hence `E(2^k L) ≥ D(2cosh(2^k θ) − 2)` whenever
   `E(L) ≥ D(2cosh θ − 2)` (`heckeDefect_dyadic_ge`), with the strip bound as ceiling
   (`heckeDefect_dyadic_sandwich`); an upper bound at one dyadic scale transfers to the base scale
   (`heckeDefect_le_of_dyadic_le`); sub-doubly-exponential growth forces `E(L) = 0`
   (`heckeDefect_eq_zero_of_dyadic_subexp`); and RH holds iff every test has sub-doubly-exponential
   dyadic growth (`riemannHypothesis_iff_dyadic_subexp`).
9. **The Hecke moment problem** (`TheHeckeMomentProblem`). `m_0 = D`, `m_1 = E(L)`,
   `m_2 = E(2L) − 4E(L)`. Every shifted Hankel form is a trace `Σ_ρ w_ρ k_ρ^s P_c(k_ρ)²`
   (`hankelForm_eq_tsum`, `hankelForm_nonneg`); its null vectors are the polynomials vanishing on
   the seen levels (`hankelForm_eq_zero_iff`); a null vector of size `n` forces fewer than `n` seen
   levels (`ncard_seenLevels_lt_of_hankel_null`); the moments are log-convex (`depthMoment_sq_le`).
10. **Integer theta prefixes** (`IntegerThetaPrefixesReadTheDefectWithoutLoss`). Finite prefixes read
   the moments, the mass, the defect and every Hankel form (`reading_depthMoment`, `reading_mass`,
   `reading_heckeDefect`, `reading_hankelForm`). One pair of readings at a single dyadic scale bounds
   the defect at the base scale (`heckeDefect_le_of_readings`), and depth is always visible in the
   readings (`reading_ge_of_heckeDefect_ge`).
11. **Gauge charge** (`TheGaugeChargeOfACoupling`). A coupling `(n; a, b)` is blind under every real
   sign gauge iff `nab` is a square (`realSignBlind_iff_isSquare`, via prime-flip gauges and
   `isSquare_iff_even_factorization`); kernels transform by conjugation iff their support is of
   square class (`sourceKernel_twist_iff`); for such kernels the twist is the sign change of the
   modes, so positivity for `Λ` and for `λΛ` coincide (`sourceForm_nonneg_twist_iff`). Diagonal,
   ratio and product couplings are square class; successor couplings never are
   (`successor_coupling_charged`).
12. **Cells fix the gauge** (`LogCellsFixTheGauge`). Cell and lattice dilation both satisfy the
   Baumslag–Solitar relation `M_m S = S^m M_m` (`cellDilate_succShift`, `latticeDilate_succShift`);
   cell dilation is lattice dilation spread over the successor orbit (`cellDilate_eq_sum_succShift`).
   Lattice dilation is covariant at every gauge (`gaugeTwist_latticeDilate`); dyadic cell dilation
   only at the Euler gauge (`cellDilate_two_covariant_iff`), and on the horizon `[1, X]`, `X ≥ 4`,
   exactly when every prime `≤ 2X + 1` has phase `1` (`cellDilate_two_covariant_on_horizon_iff`).
13. **Quantitative cell holonomy** (`TheCellHolonomyDefectCountsChargedCells`). The Hilbert–Schmidt
    defect of `U_ω M_2 − c M_2 U_ω` on `[1, X]` is `Σ_a (|χ(2a) − cχ(a)|² + |χ(2a+1) − cχ(a)|²)`
    (`hsDefect_eq`); for a real gauge each cell contributes `(σ(2) − c)² + (σ(a)σ(2a+1) − c)²`
    (`hsDefect_realSign`). Every charged cell costs at least `2` whatever the scalar
    (`hsDefect_ge_charged`), and the defect can vanish iff no cell is charged
    (`exists_hsDefect_eq_zero_iff`). At the Liouville gauge the charged cells are the agreements
    `λ(a) = λ(2a + 1)`, and the minimal defect is between `2N₊` and `4N₊`
    (`hsDefect_liouville_sandwich`), with `N₊ ≥ 1` from `λ(2)λ(5) = 1` (`one_le_liouvilleAgreements`).
14. **Critical discs and the lens** (`CriticalDiscsAndTheTerminalLens`). The pair contribution has the
    sign of `x(x² + (y − γ)² − b²)` (`xiLinePairRe_nonneg_of_not_inCriticalDisc`,
    `xiLinePairRe_neg_of_inCriticalDisc`); off all discs `Re ξ′/ξ ≥ 0`
    (`re_logDeriv_xi_nonneg_of_outside_discs`); terminals are the zeros outside every disc
    (`isTerminal_iff_outside_discs`); the lens of a terminal lies outside every disc
    (`outside_discs_of_mem_terminalLens`), is zero-free off `p` (`xi_ne_zero_of_mem_terminalLens`),
    carries `Re ξ′/ξ ≥ 0` (`re_logDeriv_xi_nonneg_of_mem_terminalLens`) and contains the outward ray
    (`mem_terminalLens_of_ray`).
15. **Harnack on the Carathéodory region** (`HarnackOnTheCaratheodoryRegion`). Strictly outside
    every closed critical disc `ξ` has no zero (`xi_ne_zero_of_strictlyOutsideDiscs`) and `ξ′/ξ` is
    analytic (`analyticAt_logDeriv_xi`), so `Re ξ′/ξ` is a nonnegative harmonic function there and
    satisfies Harnack's inequality on every disc of the region (`harnack_re_logDeriv_xi`). The discs
    of radius `ρh`, `ρ = a/(2(a + T))`, about the outward ray of a terminal lie in the region
    (`terminalRayBall_subset`), so ACP's floor spreads with factor `1/3` to discs of radius `ρh/2`
    (`exists_terminal_floor_spreads`).
16. **Irreversibility** (`PositivityIsIrreversible`). Positive deformations compose
    (`PositiveDeformation.trans`); mutual positive deformations have equal logarithmic derivatives on
    a ray (`PositiveDeformation.antisymm`); a nontrivial one cannot be undone
    (`not_positiveDeformation_of_ne`).
17. **Kronecker dilution** (`CollectivePacketsDiluteOverIndependentOrdinates`). Kronecker's theorem
    puts every `cos(ω_j t)` near `−sign(a_j)` at one time, so a nonnegative packet on independent
    ordinates satisfies `Σ_j |a_j| ≤ a_0` (`sum_abs_le_of_packet_nonneg`), sharply
    (`packet_nonneg_of_sum_abs_le`), and its peak is at most twice its pole share
    (`packet_peak_le_two_mul`). The Fejér packet on `γ, …, Mγ` buys `M` times its pole share
    (`exists_harmonic_packet`, `harmonic_purchase_eq`). For harmonic progressions of length `≤ M`
    along independent generators the packet is nonnegative on the diagonal of the torus
    (`diagonal_nonneg_of_packet_nonneg`), and quadrature over `M + 1` diagonal nodes gives the height
    law `Σ a ≤ M a_0` (`sum_le_height_mul_of_packet_nonneg`). The same holds for any cloud of
    nonnegative integer combinations `Σ_i n_{ji} g_i` with heights `1 ≤ Σ_i n_{ji} ≤ M`
    (`sum_le_height_mul_of_generated_packet`).
18. **The battery** (`TheSelectivityBatteryOfRenormalizedBiarithmeticGeometry`). Two-scale rigidity
    and dyadic amplification hold for every finite positive depth configuration
    (`configDefect_sq_le`, `config_dyadic_ge`): they are soft. Cells reject the Liouville twin
    (`liouville_not_cell_covariant`, `two_le_hsDefect_liouville`) and pass the Euler point
    (`euler_cell_covariant`); square-class criteria cannot reject it (`squareClass_liouville_iff`).
19. **The laws** (`TheLawsOfRenormalizedBiarithmeticGeometry`): one conjunction of the laws above,
    `renormalized_biarithmetic_geometry_laws`.

---

## 5. Pillar theorems: the eight laws

| Law | Statement | Lean |
|---|---|---|
| I. Split polarization and lossless amplification | `Re W = D − Δ`; `E(L)² ≤ D(E(2L) − 4E(L))`; dyadic amplification with loss `D`; RH ⇔ sub-doubly-exponential dyadic growth; Hankel positivity and shell rigidity of the depth moments | CDG, APol; `heckeDefect_dyadic_ge`, `heckeDefect_le_of_dyadic_le`, `riemannHypothesis_iff_dyadic_subexp`, `hankelForm_nonneg`, `ncard_seenLevels_lt_of_hankel_null` |
| II. Local trichotomy | reflection-commuting affine actions are boosts, unipotent or elliptic | APol `TheEllipticLocalizers`, ACP |
| III. Gauge blindness = square class | blind ⇔ `nab` square; square-class criteria accept `Λ` iff `λΛ`; successor charged | `realSignBlind_iff_isSquare`, `sourceForm_nonneg_twist_iff`, `successor_coupling_charged` |
| IV. Interior–boundary duality | global states decouple `+1` and `×p` (APD); cells couple them and fix the gauge, with reach `2X + 1` on horizon `X`; the covariance defect counts charged cells | APD; `cellDilate_two_covariant_iff`, `cellDilate_two_covariant_on_horizon_iff`, `hsDefect_ge_charged`, `hsDefect_liouville_sandwich` |
| V. Self-energy survival | positivity passes a scale limit exactly on the survival cone, independent of scheme; for periodic germs the cone is the module of relations among the modes; prime place: `{0}`, indefinite limit; archimedean place: polar-neutral hyperplane; the pole node completes it; Ramanujan twins survive exactly on per-order relations and carry `−φ(m)Λ(t)` in their pole-node block | `quad_nonneg_on_survivalCone_iff`, `survivalCone_eq_of_regularized`, `periodicGerm_survivalCone_eq`, `counterterm_rank_dichotomy`, `harmonicKernel_nonneg`, `ramanujanTwin_survivalCone_eq`, `ramanujanTwin_carries_primes` |
| VI. Chirality, quantization and dilution | positive deformations form a monoid with trivial units; central excess quantized in `2ℕ`; collective packets buy at most (longest harmonic progression) × (pole share) | `PositiveDeformation.antisymm`, `not_positiveDeformation_of_ne`, `sum_abs_le_of_packet_nonneg`, `sum_le_height_mul_of_packet_nonneg`; BGG G19 |
| VII. Surface effectivity vs base non-extension | Hodge index ⇔ Serre-dual real effectivity with quadratic growth; the base theta count does not extend | AET |
| VIII. Terminal replacement of extrema | every off-line zero ascends to a terminal; terminals = zeros outside every critical disc; each carries a zero-free lens with `Re ξ′/ξ ≥ 0`; Harnack holds there and the outward floor spreads | ACP; `isTerminal_iff_outside_discs`, `xi_ne_zero_of_mem_terminalLens`, `harnack_re_logDeriv_xi`, `exists_terminal_floor_spreads` |

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
   the survival cone of the counterterm, a scheme-independent invariant, which for a periodic germ is
   the module of linear relations among its modes. A twin cancels a divergence iff it shares the
   mode that carries it. For the prime place alone the modes are independent, the cone is `{0}` and
   the limit is indefinite. For the archimedean place the cone is the polar-neutral hyperplane, and
   the pole node — the order-one torsion orbit — cancels the polar divergence and completes the germ
   to a positive kernel. For higher orbits the canonical twin is the Ramanujan-twisted lattice germ:
   placing `c_n` at several nodes makes `Σ_x C_{n,x} = 0` a relation, and by Ramanujan
   orthogonality these per-order relations are exactly the survival cone. The twin's pole-node
   block is the torsion energy, so the surviving positivity is an inequality in which
   `I(m, mt) = φ(m)Λ(t)` enters explicitly, against the twisted entries at the other nodes. What
   remains open is the evaluation of those twisted entries.
3. **Finite-horizon holonomy.** *How much `(+1, ×p)` curvature survives?* On lattice profiles none:
   lattice dilation is covariant at every gauge. On cell profiles all of it: dyadic cell dilation is
   covariant only at the Euler point, and on the horizon `[1, X]` it detects every prime up to
   `2X + 1`. Every successor coupling is charged. Quantitatively the covariance defect counts the
   charged cells; at the Liouville gauge it is pinned between `2N₊` and `4N₊`, so the remaining
   holonomy question is the correlation of `λ` along `a ↦ 2a + 1`.
4. **Chiral moduli.** *What is the geometry of one-way positive deformations?* A monoid without
   nontrivial units: positivity orders deformations and cannot be undone. With BGG's Landau–Wronskian
   principle a positive deformation can only lower the order at its abscissa, and the central excess
   is quantized. Coupling many ordinates does not help unless they are commensurable: over
   independent ordinates a positive packet buys at most its pole share in total, and over harmonic
   progressions of length `≤ M` along independent generators — more generally over any cloud of
   nonnegative integer combinations of heights `≤ M` — at most `M` times it, attained by a single
   Fejér packet.
5. **Zero-cone potential.** *How do `F(p) = 0` and an empty cone constrain the outward ray?* The empty
   cone of a terminal is the statement that `p` lies outside every critical disc. That condition
   extends from the ray to a two-dimensional lens bounded by two circles of radius `½` through `p`;
   the lens is zero-free and `Re ξ′/ξ ≥ 0` on it. On the whole Carathéodory region `Re ξ′/ξ` obeys
   Harnack's inequality, so values along the ray control values on discs about it and conversely;
   in particular the outward floor of ACP spreads to discs of radius `ρh/2`. Upper bounds on the
   outward growth that beat the archimedean drift (the terminal ceiling problem) remain open.
6. **Fibre-selective real effectivity.** *Which functionals can select `ζ` against prime-gauge
   twins?* None built from square-class couplings: such a functional is positive at `Λ` iff at `λΛ`.
   Selectivity requires charged couplings — successor links or cells. Serre duality and quadratic
   growth of `h⁰` are AET's.
7. **Fixed-loss amplification.** *What non-scaling invariant breaks depth homogeneity?* The collided
   mass `D(f)`: dyadic Hecke amplification has loss exactly `D(f)`, independent of the number of
   doublings. The amplification law is soft — it holds on every positive depth configuration — so
   the arithmetic must enter through the bound it transfers.

---

## 7. Traps

| Trap | Truth |
|---|---|
| Positivity of `T_r` for `r < 1` bounds Weil's prime form | The torsion counterterm is the identity; every form is a renormalized limit of positive forms with scalar counterterm (`regularized_one_realizes`) |
| A better renormalization scheme for the torsion germ keeps positivity | The survival cone is scheme independent and equal to `{0}` (`torsion_survivalCone_eq`) |
| Any continuum twin cancels the torsion divergence | Only modes shared with the torsion orbit create relations (`periodicGerm_survivalCone_eq`) |
| Subtracting `−log(1 − r) I` leaves something positive | The limit is negative along `(1, t)` on `{1, q}` (`torsionLimitForm_neg`) |
| The archimedean place is positive | Only on the polar-neutral hyperplane; at `z = 2` the limit is `−1` |
| A cleverer multiplicative weight separates `ζ` from Liouville | Square-class criteria accept `Λ` iff `λΛ` (`sourceForm_nonneg_twist_iff`) |
| Discretizing to `log n` loses nothing | Lattice dilation is blind; only cell dilation fixes the gauge |
| Two-scale rigidity is one inequality | It iterates to every dyadic scale with fixed loss |
| Dyadic amplification is selective | It holds on every finite positive depth configuration (`config_dyadic_ge`); its content is the transfer of a source bound |
| A twin with any continuum modes cancels a torsion divergence | Ramanujan modes are orthogonal; only the same mode creates relations (`ramanujanTwin_survivalCone_eq`) |
| Cell gauge fixing is all-or-nothing | The defect counts charged cells; at Liouville it is a `λ`-correlation along `a ↦ 2a + 1` |
| The terminal ray is special | It lies in a two-dimensional zero-free lens |
| Positive deformations can be undone | Units are trivial |
| Collective packets amortize pole cost | Over `ℚ`-independent ordinates the whole packet buys at most the pole share (`sum_abs_le_of_packet_nonneg`); in general at most the longest harmonic length times it (`sum_le_height_mul_of_packet_nonneg`) |
| The terminal ray is one-dimensional information | Harnack spreads it to discs (`exists_terminal_floor_spreads`) |

---

## 8. Tools

**Imported**: collided and reflection forms, Hecke defect and depth kernel, finite integer theta
readings (CDG, APol); torsion orbit intersections and the Abel torsion energy (AET); gauge torus,
successor connection, Landau–Wronskian deformations (BGG); terminals, outward rays and the pair-sum
formula for `Re ξ′/ξ` (ACP, RHTower); Gauss series for digamma and the Cauchy kernel (HTGeometry,
RHTower).

**Built in RBG**: the survival law with scheme independence and the Finsler–Debreu converse; the
lattice germ and its digamma limit; periodic germs, their Cesàro counterterm and the
relations law; Ramanujan orthogonality and the exact twin law; counterterm rank of both places;
pole-node completion; dyadic
amplification and the effective angle; the Hecke moment problem; integer-prefix transfer; gauge
charge of couplings and the square-class criterion; cell and lattice dilation with finite-horizon
gauge fixing and the cell-holonomy defect; critical discs, the Carathéodory region, the terminal
lens and Harnack estimates on it; the positive deformation monoid; Kronecker dilution, the height
law and harmonic concentration of positive packets; the selectivity battery.

**Frontier** (each a research problem, stated in §9): the twisted Lerch entries of the Ramanujan
twins; arithmetic upper bounds for prefix readings at one dyadic scale; a terminal ceiling beating
the archimedean drift; correlation lower bounds for `λ` along `a ↦ 2a + 1`; Wiener escape modules as
boundary objects.

---

## 9. Open research topics

1. **The twisted entries of the Ramanujan twins.** The twin survives exactly on per-order
   relations and its pole-node block carries `−φ(m)Λ(t)` (`ramanujanTwin_carries_primes`). The
   other entries are renormalized twisted Lerch sums `Σ_k c_m(k+1)c_n(k+1)/(k + 1 + x + y)`.
   Evaluate them, and decide whether the resulting bound on the prime form reaches the short-cycle
   differences `g − T_{2^m} g`.
2. **One-scale arithmetic bounds.** An upper bound for `R_n(f, 2^k L, 1)` at `2^k L ≍ log n` from
   integer arithmetic; by lossless transfer it bounds `E_f(L)`. Any bound `E ≪ e^{2ϑ L} D` at one
   scale gives zero-density control.
3. **The terminal ceiling.** Harnack on the Carathéodory region bounds `Re ξ′/ξ` near the ray by
   its values further out; combine it with mollified Borel–Carathéodory estimates (available in
   Mathlib) for `ζ M_X` to bound the outward growth by `(½ − η(a)) log|γ_p|` with `η(a) > ca`.
4. **Correlations along `(+1, ×2)`.** The Liouville cell defect is `Θ(N₊)`; a lower bound
   `N₊ ≥ cX` is a binary correlation estimate for `λ(a)λ(2a + 1)`. Prove one, or show which
   weaker averaged versions suffice for gauge fixing on smooth short-cycle profiles.
5. **Collective packets with relations of mixed sign.** The height law covers clouds generated with
   nonnegative coefficients. Clouds containing differences such as `g_1 − g_2` have ordinates of
   height `0`, where diagonal quadrature says nothing; determine the purchase bound for general
   integer lattices of relations.
6. **Escape modules.** The contractive `𝒲_{1/2}`-modules `ActualCofactorLimit` of ADR (faithful
   or the receiver escapes) as the boundary objects where `(+1, ×p)` coupling survives.

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
- [`TheSurvivalConeOfAPeriodicGermIsItsModuleOfRelations.lean`](TheSurvivalConeOfAPeriodicGermIsItsModuleOfRelations.lean) — periodic germs, Cesàro counterterm, the relations law, Ramanujan twins.
- [`TheRamanujanTwinsSurviveExactlyOnPerOrderRelations.lean`](TheRamanujanTwinsSurviveExactlyOnPerOrderRelations.lean) — Ramanujan orthogonality and the exact twin law.
- [`TheRamanujanTwinsCarryThePrimes.lean`](TheRamanujanTwinsCarryThePrimes.lean) — the pole-node block is the torsion energy; `−φ(m)Λ(t)` in the twin.
- [`TheDyadicAmplificationOfTheHeckeDefect.lean`](TheDyadicAmplificationOfTheHeckeDefect.lean) — amplification map, lossless transfer, RH as a growth rate.
- [`TheHeckeMomentProblem.lean`](TheHeckeMomentProblem.lean) — depth moments, Hankel positivity, shell rigidity, log-convexity.
- [`IntegerThetaPrefixesReadTheDefectWithoutLoss.lean`](IntegerThetaPrefixesReadTheDefectWithoutLoss.lean) — finite readings of the moment problem and source-side transfer.
- [`TheGaugeChargeOfACoupling.lean`](TheGaugeChargeOfACoupling.lean) — square-class classification, Liouville blindness of square-class criteria, charged successor.
- [`LogCellsFixTheGauge.lean`](LogCellsFixTheGauge.lean) — cell and lattice dilation, Baumslag–Solitar, gauge fixing, finite horizons.
- [`TheCellHolonomyDefectCountsChargedCells.lean`](TheCellHolonomyDefectCountsChargedCells.lean) — the covariance defect, charged cells, the Liouville sandwich.
- [`CriticalDiscsAndTheTerminalLens.lean`](CriticalDiscsAndTheTerminalLens.lean) — pair sign law, Carathéodory region, terminals, the lens.
- [`HarnackOnTheCaratheodoryRegion.lean`](HarnackOnTheCaratheodoryRegion.lean) — Harnack for `Re ξ′/ξ`, ray discs, spreading of the outward floor.
- [`PositivityIsIrreversible.lean`](PositivityIsIrreversible.lean) — the positive deformation monoid.
- [`CollectivePacketsDiluteOverIndependentOrdinates.lean`](CollectivePacketsDiluteOverIndependentOrdinates.lean) — Kronecker dilution, the height law, harmonic concentration.
- [`TheSelectivityBatteryOfRenormalizedBiarithmeticGeometry.lean`](TheSelectivityBatteryOfRenormalizedBiarithmeticGeometry.lean) — soft and selective laws on the battery.
- [`TheLawsOfRenormalizedBiarithmeticGeometry.lean`](TheLawsOfRenormalizedBiarithmeticGeometry.lean) — the laws in one statement.
