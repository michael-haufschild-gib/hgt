# Sonin residual Hilbert--Schmidt escape and moment-curve properness

- **ID:** `sonin-residual-hs-escape-and-moment-curve-properness`
- **Stage:** 1-in-progress
- **Type:** `[SOURCE THEOREM] [CLUSTER-SET CLASSIFICATION] [NOVELTY UNVERIFIED]`
- **Parent:** `sonin-prime-arch-finite-moment-transfer.md`
- **RH status:** not an RH proof; collapses the live finite-block closure core to an exact
  fixed-aperture identity, conditional only on the continuity package isolated below.

## Frontier statement

Let

```text
P_a = physical cutoff on [-a,a],
F_a = Fourier-conjugate cutoff on [-a,a],
Q_a = projection onto K_a = ker(P_a) intersect ker(F_a),
Q0_a = 1-P_a-F_a,
C_a = Q_a-Q0_a,
D_p = U_p+U_p^(-1),
R_(a,p) = (1-Q_a)D_pQ_a-(1-Q0_a)D_pQ0_a.
```

The repository's weighted all-prime residual is the block direct sum of nonzero scalar multiples
of the `R_(a,p^m)` with `m>=2`.  Its positive energy is `T_a=K_a^*K_a`, and

```text
S_r(a)=Tr(T_a^(r+1)).
```

The proposed source theorem has four parts.

1. For every fixed `p>1`, `a |-> R_(a,p)` is continuous in Hilbert--Schmidt norm on
   `(0,infinity)`.
2. `||R_(a,p)||_HS^2 -> infinity` as `a->infinity`.
3. The all-prime zeroth moment satisfies

   ```text
   S_0(a) -> 0        as a->0+,
   S_0(a) -> infinity as a->infinity.
   ```

   Every `a |-> S_r(a)` is continuous on `(0,infinity)`.
4. Consequently any finite limit of Sonin moment blocks with positive zeroth coordinate is an
   actual finite-aperture value.  In particular,

   ```text
   SoninPrimeArchFiniteMomentClosure
     iff
   exists a>0, forall r,
     soninAllPrimeEnergyMoment a r = normalizedPrimeArchMoment r.
   ```

The reverse implication in part 4 is immediate.  The forward implication uses the already
formalized cofinal-section theorem to obtain one aperture sequence converging in every moment.
Parts 1--3 trap that sequence in a compact aperture interval; a convergent subsequence and
continuity give one exact aperture matching all orders.

## Existing inputs

The following are already proved in the corpus.

1. `||C_a||_HS^2=8a^2`.
2. Each `R_(a,p)` is Hilbert--Schmidt and nonzero for `a>0`.
3. Every logarithmic prime-power weight is nonzero and their squared norms are summable.
4. The all-prime block direct sum is Hilbert--Schmidt.
5. `S_0(a)=||K_a||_HS^2`, and the all-prime area estimate gives

   ```text
   S_0(a) <= 128 a^2 sum_(p,k)|w_(p,k)|^2.
   ```

6. `normalizedPrimeArchMoment 0>0`.
7. Finite-block closure is equivalent to one positive aperture sequence converging in every
   moment coordinate.

External input: Burnol, *Two complete and minimal systems associated with the zeros of the
Riemann zeta function*, J. Théorie des Nombres de Bordeaux 16 (2004), Proposition
`denselemma`, proves

```text
closure(union_(b>a) K_b)=K_a.
```

Burnol's proof identifies `K_a^perp=A_a+B_a`, uses closedness of this sum and
`intersection_(b>a)(A_b+B_b)=A_a+B_a`.  This is exactly the one-sided density needed below.

## Paper proof

### 1. Strong continuity of the Sonin projections

The family `K_a` is decreasing.

- If `a_n` increases to `a`, then `intersection_n K_(a_n)=K_a`, since the increasing physical
  and Fourier intervals exhaust `[-a,a]` up to null endpoints.  Monotone convergence of
  orthogonal projections gives `Q_(a_n)->Q_a` strongly.
- If `a_n` decreases to `a`, Burnol's density theorem gives
  `closure(union_n K_(a_n))=K_a`.  The other monotone-projection theorem again gives strong
  convergence.

Every scalar sequence converging to `a` has monotone subsequences on either side.  Hence
`Q_b->Q_a` strongly as `b->a`.  The cutoff projections `P_b,F_b` are strongly continuous by
absolute continuity of the `L2` integral, so `Q0_b` and `C_b` are strongly continuous.

### 2. Hilbert--Schmidt continuity of the correction

Regard Hilbert--Schmidt operators as a Hilbert space.  On a compact positive aperture interval,
the exact identity

```text
||C_b||_HS^2=8b^2
```

gives a uniform Hilbert--Schmidt bound.  Strong operator convergence of `C_b` gives convergence
of all matrix coefficients.  Finite-rank operators are dense in the Hilbert--Schmidt class, so
the uniform bound upgrades matrix-coefficient convergence to weak Hilbert--Schmidt convergence.
As `b->a`, the displayed exact identity also gives
`||C_b||_HS->||C_a||_HS`.  Weak convergence plus convergence of Hilbert-space norms gives

```text
||C_b-C_a||_HS -> 0.
```

### 3. Hilbert--Schmidt continuity of one residual

Use the corpus factorization

```text
R_(a,p)=(1-Q_a)D_p C_a-C_a D_p Q0_a.                  (1)
```

If bounded operators `A_n` and their adjoints converge strongly to `A` and `A^*`, then
left and right multiplication by `A_n` converge on every fixed Hilbert--Schmidt operator in
Hilbert--Schmidt norm.  Apply this standard finite-rank approximation lemma to `(1)`, using
strong continuity and self-adjointness of `Q_a,Q0_a,D_p`, plus Hilbert--Schmidt continuity of
`C_a`.  This proves part 1.

### 4. Large-aperture strong limit

As `a->infinity`, `P_a->1` strongly by monotone convergence of the physical cutoffs, and
`F_a->1` strongly by Fourier conjugacy.  Since `Q_a<=1-P_a`,

```text
Q_a -> 0 strongly,
Q0_a=1-P_a-F_a -> -1 strongly,
C_a=Q_a-Q0_a -> 1 strongly.
```

Substitution in `(1)` gives the exact strong limit

```text
R_(a,p) -> D_p-(-D_p)=2D_p.                            (2)
```

The factor `2` is essential: the true Sonin corner tends strongly to zero, while the formal
complement corner tends to `-2D_p`.

### 5. Hilbert--Schmidt escape

`D_p=U_p+U_p^(-1)` is not Hilbert--Schmidt.  Under logarithmic coordinates, `U_p` is translation
by `log p`.  Choose an infinite orthonormal family of compactly supported translates whose two
`D_p` images remain separated; their image norms are bounded below by one fixed positive
constant.  Hence the Hilbert--Schmidt sum for `D_p` diverges.

Fix `M>0`.  Since `2D_p` is not Hilbert--Schmidt, choose a finite orthonormal family
`e_1,...,e_N` with

```text
sum_i ||2D_p e_i||^2 > 2M.
```

The strong convergence `(2)` makes the corresponding finite sum for `R_(a,p)` exceed `M` for all
large `a`.  Bessel's lower bound for Hilbert--Schmidt norm then gives

```text
||R_(a,p)||_HS^2 >= sum_i ||R_(a,p)e_i||^2 > M.
```

Therefore `||R_(a,p)||_HS^2->infinity`.

### 6. All-prime endpoint coercivity

Fix one retained prime-power block, for example `(2,0)`.  Its logarithmic weight is nonzero.
The all-prime block Hilbert--Schmidt energy dominates this one weighted block, so part 2 gives

```text
S_0(a)=||K_a||_HS^2 -> infinity.
```

At the other endpoint the corpus area bound gives `S_0(a)->0`.

### 7. Continuity of every moment

Each weighted local block is Hilbert--Schmidt continuous.  On a compact aperture interval, the
existing square-summable uniform local bound controls the all-prime tail independently of
aperture.  Finite-block continuity plus uniform tail control gives Hilbert--Schmidt continuity of
`K_a`.

Thus `T_a=K_a^*K_a` is continuous in trace norm.  The local operator-norm ceiling on `K_a` gives
uniform bounds for powers, and the telescoping identity for `T_b^(r+1)-T_a^(r+1)` gives trace-norm
continuity.  Taking traces proves continuity of `S_r`.

### 8. Proper positive-mass cluster classification

Let `a_j>0` and suppose `S_r(a_j)->m_r` for every `r`, with `m_0>0`.  Small-aperture collapse
excludes subsequences tending to zero.  Large-aperture escape excludes unbounded subsequences.
Hence `a_j` is eventually contained in some compact interval `[epsilon,A]`.  A subsequence tends
to `a_*` in that interval, and continuity gives `S_r(a_*)=m_r` for every `r`.

Apply this to the single cofinal aperture sequence already extracted from
`SoninPrimeArchFiniteMomentClosure`, using `normalizedPrimeArchMoment_zero_pos`.

## Hostile audit

1. **Wrong endpoint sign:** direct evaluation of the two corners gives
   `crossBoundary(Q_a,D_p)->0` and `crossBoundary(Q0_a,D_p)->-2D_p`; their difference is
   `2D_p`, not `0` or `D_p`.
2. **Strong limit does not normally force Hilbert--Schmidt norms to diverge:** it does here
   because the limit is non-Hilbert--Schmidt and finite orthonormal lower sums converge
   termwise.  No compactness principle is being used backwards.
3. **A single escaping block suffices:** the all-prime construction is an orthogonal block direct
   sum, so no cancellation can erase one block's Hilbert--Schmidt energy.
4. **Continuity is load-bearing:** strong continuity alone permits trace mass to escape.  The
   exact `8a^2` correction norm is what upgrades the correction to Hilbert--Schmidt continuity.
5. **Right-continuity is not guessed:** it uses Burnol's published density theorem for the
   decreasing Sonine filtration.
6. **No Xi divisor or RH-equivalent measure:** all endpoint and continuity inputs are properties
   of the explicit Sonin/cutoff source.  The target enters only through the positive finite number
   `normalizedPrimeArchMoment 0`.
7. **Scientific boundary:** this does not prove the exact fixed-aperture identity.  It proves that
   no cofinal or boundary schedule can provide it.  Future work must either find one actual
   aperture matching all prime--Gamma moments or retire this block-diagonal closure route.

## Novelty audit

Corpus searches found:

- small-aperture collapse and area bounds;
- exact correction energy `8a^2`;
- finite-aperture residual Hilbert--Schmidt/nonzero theorems;
- the conditional finite-block cluster-to-RH consumer.

They did not find large-aperture strong convergence of the principal-subtracted residual,
Hilbert--Schmidt escape, properness of `S_0`, continuity of the all-prime trace moments, or the
fixed-aperture classification.

Primary-literature searches found Burnol's density theorem and the Connes--Consani Sonin/prolate
trace programme, but no theorem for this logarithmically weighted principal-subtracted
prime-power residual or its trace-moment curve.  External novelty remains provisional until a
broader operator-theory and Sonine/prolate audit is complete.

## Gates

- [x] corpus and failed-route search
- [x] exact source objects and endpoint sign isolated
- [x] paper proof decomposed into named analytic lemmas
- [x] Burnol density input located in primary literature
- [ ] independently hostile-audit every continuity step
- [ ] complete broad literature collision audit
- [ ] promote to 2-fully-proven
- [ ] formalize source theorem and fixed-aperture classification in Lean
- [ ] decide exact fixed-aperture identity or retire block-diagonal Sonin cluster route
## 2026-08-27 — F2-RHSE.1 formal closure: large-aperture ceiling and compactness

New module:

- `formal/GaloisForLFunctions/RHTower/SoninAllPrimeMomentWeldApertureCeiling.lean`
- umbrella import: `formal/GaloisForLFunctions/RHTower.lean`

### New mathematical theorem

For every fixed prime-power block, the principal-subtracted Sonin residual has a
nonzero strong limit on each normalized dilation vector as the aperture tends to
infinity.  More precisely, the physical and Fourier cutoff projections converge
strongly to the identity, the actual Sonin projection converges strongly to zero,
and the formal complement `1 - P_a - F_a` converges strongly to `-1`.  Consequently

`centralSoninDilationCornerResidual a p hp g → 2 • dilationSum p hp g`.

The factor `2` is essential: both the actual Sonin corner and the formal complement
survive with opposite limiting signs.  Applying the residual to arbitrarily large
finite orthonormal shell families and using finite-family Hilbert--Schmidt domination
proves

`hsNormSq (centralSoninWeightedPrimePowerResidual a pk) → +∞`

for every prime-power label `pk`.  A single fixed `(2, 0)` block therefore forces

`(soninAllPrimeEnergyMoment a 0).re → +∞`.

This closes the large-aperture escape and properness half of the source theorem.
Combined with the previously formalized small-aperture floor and exact zeroth weld
coordinate, every exact-weld witness sequence is eventually contained in a compact
positive aperture interval and hence admits a positive finite cluster aperture.

### Lean surface

The module proves:

- `tendsto_hsNormSq_centralSoninWeightedPrimePowerResidual_atTop`
- `hsNormSq_centralSoninWeightedPrimePowerResidual_le_re_energyMoment_zero`
- `tendsto_re_soninAllPrimeEnergyMoment_zero_comp_atTop`
- `tendsto_re_soninAllPrimeEnergyMoment_zero_atTop`
- `soninPrimeArchSingleMomentCoupling_eventually_aperture_boundedAbove`
- `soninPrimeArchSingleMomentCoupling_eventually_aperture_mem_compactWindow`
- `soninPrimeArchSingleMomentCoupling_exists_positive_aperture_cluster`
- `soninAllPrimeExactTraceMomentWeld_has_aperture_compactWindow`

All declarations are closed.  Axiom audit reports only `propext`,
`Classical.choice`, and `Quot.sound`.

### Verification

- direct check:
  `cd formal && lake env lean GaloisForLFunctions/RHTower/SoninAllPrimeMomentWeldApertureCeiling.lean`
  — PASS
- exact final module audit:
  `lake build GaloisForLFunctions.RHTower.SoninAllPrimeMomentWeldApertureCeiling`
  — PASS (`Build completed successfully (9526 jobs).`)
- scratch axiom audit with `lake env lean` — PASS

### Targeted literature collision audit

The closest located sources are Xian-Jin Li's explicit orthogonal-projection formula
for Sonine space (JMAA 389 (2012), 379--393), Connes--Consani's fixed-cutoff
archimedean Sonin compression (arXiv:2006.13771), and
Connes--Consani--Moscovici's semilocal Sonin/prolate stability programme
(arXiv:2310.18423).  None of the searched statements gives the principal-subtracted
weighted residual limit, its factor `2`, single-block Hilbert--Schmidt escape, or the
resulting all-prime moment properness.  Novelty status remains **provisional after a
targeted audit**, not an exhaustive claim.

### Remaining open core

The next indispensable theorem is positive-aperture continuity of
`a ↦ soninAllPrimeEnergyMoment a r` on compact intervals.  The local burden is
strong continuity of `a ↦ centralSoninProjection a` followed by Hilbert--Schmidt
continuity of the principal-subtracted residual.  Once closed, continuity sends the
positive cluster aperture above to an exact fixed-aperture weld and removes the last
moving-aperture escape in this F2 branch.

## Active conjecture F2-RHSC.1 — strong continuity of the actual Sonin projection

**Conjecture.** For every `g : SoninL2`,

`ContinuousOn (fun a : ℝ => centralSoninProjection a g) (Set.Ioi 0)`.

**Corpus basis.** Right continuity is forced by the already formalized Burnol
dense-union theorem
`topologicalClosure_iSup_centralSoninCarrier`.  Left continuity is forced by the
dual closed-intersection statement: the intersection of `K_b` over `b < a` is
`K_a`.  The latter should follow from monotone convergence of central interval
cutoffs and Fourier conjugacy.  Mathlib's
`Submodule.starProjection_tendsto_closure_iSup` and the corpus theorem
`starProjection_tendsto_iInf_of_antitone` then convert the two lattice limits into
strong projection limits.  The order-filter bridges
`tendsto_comp_coe_Ioi_atBot` and `tendsto_comp_coe_Iio_atTop` join them into ordinary
positive-aperture continuity.

**Failure/pivot rule.** If the full left carrier intersection cannot be closed
directly, first formalize the exact physical-band identity
`closure (⨆ b<a, centralPhysicalForbidden b) = centralPhysicalForbidden a`, transfer
it by `fourierUnitary`, and recover the carrier statement through orthogonals.

## 2026-08-27 — F2-RHSC.1 formal closure: Hilbert--Schmidt continuity and exact landing

New modules:

- `formal/GaloisForLFunctions/RHTower/SoninProjectionApertureStrongContinuity.lean`
- `formal/GaloisForLFunctions/RHTower/SoninResidualApertureHilbertSchmidtContinuity.lean`
- `formal/GaloisForLFunctions/RHTower/SoninAllPrimeMomentApertureContinuity.lean`
- umbrella imports: `formal/GaloisForLFunctions/RHTower.lean`

### New mathematical theorem

The actual Sonin projection `P_a` is strongly continuous for every positive aperture.
The proof identifies both one-sided carrier limits exactly: the Burnol dense-union
theorem supplies the increasing side, while closure of the increasing physical and
Fourier forbidden bands supplies the decreasing side through orthogonal complements.

Strong convergence alone does not imply Hilbert--Schmidt convergence.  The missing
mixed-topology bridge is now closed: strong convergence of bounded operators, together
with convergence of their Hilbert--Schmidt norm squares, gives Hilbert--Schmidt
convergence; multiplication by a fixed Hilbert--Schmidt operator sends strong convergence
of a uniformly bounded family to Hilbert--Schmidt convergence.  Applying these lemmas to
the exact correction-energy identity and the four-term residual factorization proves

`centralSoninDilationCornerResidual a p hp g`

is Hilbert--Schmidt continuous in `a > 0`, as is every weighted prime-power residual
block.

On any compact positive aperture window, the existing prime-power square-summable
majorant dominates the block differences.  Dominated convergence therefore passes
through the all-prime block sum and proves Hilbert--Schmidt continuity of the all-prime
residual kernel.  Every trace moment

`a ↦ soninAllPrimeEnergyMoment a r`

is consequently continuous on positive apertures.

Combining this continuity with the previously proved compact positive cluster aperture
turns an asymptotic moving-aperture weld into an exact finite-aperture identity.  Lean now
proves the exact classification

`soninAllPrimeExactTraceMomentWeld ↔`
`  ∃ a > 0, ∀ r, soninAllPrimeEnergyMoment a r = normalizedPrimeArchMoment r`.

Thus the whole compactness/continuity burden of F2 is closed.  The former asymptotic
weld endpoint is neither weaker nor more flexible than one exact positive-aperture
all-moment equality.

### Lean surface

The modules prove, among other declarations:

- `continuousOn_centralSoninProjection_apply`
- `tendsto_hsNormSq_comp_left_zero_of_strong`
- `tendsto_hsNormSq_centralSoninDilationCornerResidual_sub`
- `tendsto_hsNormSq_soninAllPrimeResidualKernel_sub`
- `tendsto_soninAllPrimeEnergyMoment_of_tendsto`
- `soninPrimeArchSingleMomentCoupling_exists_exact_positive_aperture`
- `soninAllPrimeExactTraceMomentWeld_iff_exists_exact_positive_aperture`
- `riemannHypothesis_of_soninAllPrimeExactPositiveApertureMomentWeld`

All declarations are closed.  Axiom audit reports only `propext`,
`Classical.choice`, and `Quot.sound`.

### Verification

- all three direct checks with `lake env lean <file>` — PASS
- exact final module audits:
  - `lake build GaloisForLFunctions.RHTower.SoninProjectionApertureStrongContinuity`
    — PASS (`Build completed successfully (9582 jobs).`)
  - `lake build GaloisForLFunctions.RHTower.SoninResidualApertureHilbertSchmidtContinuity`
    — PASS (`Build completed successfully (9593 jobs).`)
  - `lake build GaloisForLFunctions.RHTower.SoninAllPrimeMomentApertureContinuity`
    — PASS (`Build completed successfully (10015 jobs).`)
- scratch `#print axioms` audit — PASS

### Targeted literature collision audit

The closest located primary sources remain Xian-Jin Li's projection formula for Sonine
space (JMAA 389 (2012), 379--393) and Connes--Consani--Moscovici's semilocal
Sonin/prolate construction (arXiv:2310.18423).  The searched statements do not supply
positive-aperture strong continuity of the Sonin projections, Hilbert--Schmidt continuity
of this principal-subtracted all-prime residual, continuity of all its trace moments, or
the exact cluster-aperture landing classification above.  Novelty remains **provisional
after a targeted audit**, not an exhaustive claim.

### Remaining open core

F2-RHSC.1 is closed.  The irreducible remaining F2 statement is the exact fixed-aperture
identity

`∃ a > 0, ∀ r, soninAllPrimeEnergyMoment a r = normalizedPrimeArchMoment r`.

It is sufficient for RH through the already formalized exact moment-to-Li chain, but it is
not proved here.  The next unconditional attack is the scalar base case: use small-
aperture vanishing, large-aperture escape, and the new continuity theorem to prove that
some positive aperture matches the zeroth normalized prime--archimedean moment exactly.

## 2026-08-27 — F2-RHSZ.1 formal closure: positive zeroth-moment surjectivity

New module:

- `formal/GaloisForLFunctions/RHTower/SoninAllPrimeZerothMomentApertureSurjectivity.lean`
- umbrella import: `formal/GaloisForLFunctions/RHTower.lean`

### New mathematical theorem

Let

`S₀(a) = soninAllPrimeEnergyMoment a 0`.

The previous continuity theorem upgrades from sequential form to ordinary continuity on
`a > 0`.  For an arbitrary target `T > 0`, choose the explicit positive aperture

`a₀ = sqrt (T / (2 * 128 * soninAllPrimeColumnWeightSqMass))`.

The quadratic Shannon-area ceiling gives `S₀(a₀).re ≤ T / 2 < T`.  Large-aperture escape
gives some finite `A > a₀` with `T < S₀(A).re`.  The intermediate value theorem on
`[a₀, A]` therefore gives a finite positive aperture at which `S₀(a) = T` exactly.  Hence
the real zeroth trace map is surjective onto the entire positive half-line:

`∀ T > 0, ∃ a > 0, soninAllPrimeEnergyMoment a 0 = (T : ℂ)`.

Specializing `T` to `normalizedPrimeArchMoment 0`, whose strict positivity is already
closed in the corpus, proves the first exact coordinate of the fixed-aperture F2 weld
unconditionally.

### Lean surface

- `continuousAt_soninAllPrimeEnergyMoment`
- `continuousOn_soninAllPrimeEnergyMoment`
- `continuousOn_re_soninAllPrimeEnergyMoment_zero`
- `exists_positive_aperture_soninAllPrimeEnergyMoment_zero_eq`
- `exists_positive_aperture_soninAllPrimeEnergyMoment_zero_eq_normalizedPrimeArchMoment`

All declarations are closed.  Axiom audit reports only `propext`,
`Classical.choice`, and `Quot.sound`.

### Verification

- scratch check: `lake env lean /tmp/f2_zeroth_aperture.lean` — PASS
- direct check:
  `lake env lean GaloisForLFunctions/RHTower/SoninAllPrimeZerothMomentApertureSurjectivity.lean`
  — PASS
- exact final module audit:
  `lake build GaloisForLFunctions.RHTower.SoninAllPrimeZerothMomentApertureSurjectivity`
  — PASS (`Build completed successfully (10016 jobs).`)
- scratch `#print axioms` audit — PASS

### Targeted literature collision audit

Targeted searches around Sonine projections, cutoff-parameter continuity, Hilbert--Schmidt
trace moments, and aperture intermediate-value statements found Connes--Consani's
fixed-cutoff archimedean compression and the established Sonine/prolate programme, but no
statement matching surjectivity of this logarithmically weighted principal-subtracted
all-prime residual trace.  Novelty remains **provisional after a targeted audit**, not an
exhaustive claim.

### Remaining open core

Zeroth-coordinate existence is closed but does not synchronize higher moments.  The hard
F2 burden is now sharply reduced to proving that at least one aperture in the nonempty
zeroth-level set

`{a > 0 | soninAllPrimeEnergyMoment a 0 = normalizedPrimeArchMoment 0}`

also matches every higher normalized prime--archimedean moment.  The next conjecture loop
must extract rigidity of this level set or derive higher-moment identities from the zeroth
normalization; coordinatewise existence at unrelated apertures is insufficient.

## 2026-08-27 — F2-RHSF.1 formal closure: compact normalization fiber

New module:

- `formal/GaloisForLFunctions/RHTower/SoninAllPrimeZerothMomentApertureFiberCompactness.lean`
- umbrella import: `formal/GaloisForLFunctions/RHTower.lean`

### New mathematical theorem

The exact zeroth-normalization set

`Z₀ = {a > 0 | soninAllPrimeEnergyMoment a 0 = normalizedPrimeArchMoment 0}`

is nonempty by positive-half-line surjectivity.  It is also compact.  Quantitatively, the
Shannon-area ceiling places every member above an explicit positive square-root floor, and
large-aperture escape places every member below one finite ceiling.  Positive-aperture
continuity then makes `Z₀` closed inside that compact window.

For every `r`, the continuous discrepancy

`a ↦ ‖soninAllPrimeEnergyMoment a r - normalizedPrimeArchMoment r‖`

therefore attains a genuine minimum on `Z₀`.  Thus the remaining higher-moment problem has
no loss of compactness, no boundary escape, and no unattained infimum: failure at any fixed
degree is witnessed by an actual positive minimum-aperture obstruction.

### Lean surface

- `soninNormalizedZerothApertureFiber_nonempty`
- `soninNormalizedZerothApertureFiber_exists_compactWindow`
- `soninNormalizedZerothApertureFiber_isCompact`
- `exists_soninNormalizedHigherMomentDefect_isMinOn`

All declarations are closed.  Axiom audit reports only `propext`,
`Classical.choice`, and `Quot.sound`.

### Verification

- scratch check: `lake env lean /tmp/f2_zeroth_fiber.lean` — PASS
- direct check:
  `lake env lean GaloisForLFunctions/RHTower/SoninAllPrimeZerothMomentApertureFiberCompactness.lean`
  — PASS
- exact final module audit:
  `lake build GaloisForLFunctions.RHTower.SoninAllPrimeZerothMomentApertureFiberCompactness`
  — PASS (`Build completed successfully (10110 jobs).`)
- scratch `#print axioms` audit — PASS

### Remaining open core

The next irreducible object is the attained first defect on `Z₀`.  Proving its minimum is
zero produces one aperture matching moments `0` and `1`; proving it strictly positive
retires the literal block-diagonal F2 weld with a quantitative obstruction.  Either result
must come from a new arithmetic--operator comparison, since compactness and positivity alone
cannot select the sign.

### Exact first-defect alternative

The same module additionally closes
`soninNormalizedFirstMoment_exact_or_uniformGap`: unconditionally, either one positive
aperture matches normalized moments `0` and `1` simultaneously, or there is an `ε > 0`
which lower-bounds the first-moment mismatch at every exactly zeroth-normalized aperture.
This is the sharp quantitative success/no-go alternative for the next F2 coordinate.  Its
direct check, exact module build (`10110 jobs`), and axiom audit all pass.
