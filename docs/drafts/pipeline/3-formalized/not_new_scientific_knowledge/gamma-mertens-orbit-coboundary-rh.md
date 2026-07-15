# The reflected Mertens shift-two coboundary criterion is equivalent to RH

- **ID:** `gamma-mertens-orbit-coboundary-rh`
- **Stage:** 3-formalized/not_new_scientific_knowledge
- **Type:** EXACT RH CRITERION / HT-TO-RH CONSUMER / SOURCE PRODUCER OPEN
- **Scientific status:** `[LEAN-FORMALIZED] [RH-EQUIVALENT] [NOT AN RH PROOF]
  [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Lean:** `formal/GaloisForLFunctions/RHTower/GammaMertensOrbitCoboundaryRH.lean`
- **Parents:**
  - `../../1-in-progress/calibrated-gamma-mertens-zero-orbit-comparison-rh.md`
  - `../../1-in-progress/gamma-opposite-variance-weyl-seam.md`
  - `../../2-fully-proven/needs-audit/gamma-dihedral-orbifold-bulk-mirror-anomaly.md`
  - `../not_new_scientific_knowledge/xi-rational-quartet-gauge-countermodel.md`
  - `../../2-fully-proven/not_new_scientific_knowledge/mertens-corona-shift-conormal.md`
  - `../../2-fully-proven/not_new_scientific_knowledge/mertens-logarithmic-corona-differential-tower.md`
  - `formal/GaloisForLFunctions/RHTower/XiShiftPrimeExposure.lean`
  - `formal/GaloisForLFunctions/HTGeometry/PrincipalPartDifferentialOperator.lean`
- **Statement:** A Xi zero lies on the critical line if its reflected Mertens simple-pole doublet,
  or any nonzero constant-coefficient differential image of that doublet, is a finite
  coboundary for translation by two.  Requiring this at every Xi zero is exactly equivalent to RH.

## 1. Formal theorem

For an open-strip point `rho`, put

```text
D_rho = PP[-rho,+1] - PP[conjugate(rho)-1,+1].          (1)
```

The translation step is `q=2`, not a fitted lattice.  It is the exact step already exposed by the
completed-Xi logarithmic-derivative identity

```text
logDeriv Xi(s+2)-logDeriv Xi(s)-R_arch(s)
  = sum_n Lambda(n)(1-n^(-2))n^(-s).                    (2)
```

Let `delta_2 E=T_2 E-E` for finitely supported Laurent principal-part data.  Lean proves, for every
nonzero constant-coefficient differential operator `L`,

```text
0<Re(rho)<1  and  L(D_rho)=delta_2 E
  ==> Re(rho)=1/2.                                      (3)
```

Indeed finite translation coboundaries have zero residue on every orbit in `C/2Z`.  A nonzero
differential operator preserves a nonzero top Laurent coefficient, so the two supports in `(1)`
must define the same orbit.  Hence for some integer `n`,

```text
2n = 1-rho-conjugate(rho) = 1-2Re(rho).                 (4)
```

The right side lies strictly between `-1` and `1`; therefore `n=0` and `Re(rho)=1/2`.

Define the criterion

```text
for every rho, Xi(rho)=0 ==> D_rho=delta_2 E_rho
for some finite E_rho.                                  (5)
```

Lean proves

```text
GammaMertensShiftTwoCoboundaryCriterion
  <-> RiemannHypothesis.                                (6)
```

The reverse implication is exact: RH makes the two supports in `(1)` equal, so `D_rho=0` and one
may take `E_rho=0`.

## 2. What has and has not been proved

The consumer is complete.  It replaces literal equality of two Mertens supports by the weaker and
source-natural statement that their difference is exact in finite Gamma-shift cohomology.  Orbit
residue then promotes exactness to support coincidence because the critical strip is narrower than
one nonzero completed-Gamma shift.

This is not an RH proof.  Statement `(5)` is RH-equivalent, and choosing `E_rho` after inspecting
the zero is circular.  The proof-producing statement is:

```text
[CONJECTURE -- COMPLETED SOURCE COBOUNDARY DESCENT]
```

Construct, on the safe Euler half-plane and before using the Xi divisor, a completed
Euler--Gamma relative principal-part cochain whose continuation to an on-shell point `rho`
satisfies

```text
Xi(rho)=0 ==> D_rho=delta_2 E_rho,                       (7)
```

where `E_rho` is the boundary value of that one source construction.  The construction may use
the local Euler factors, the filtered von Mangoldt source in `(2)`, the archimedean Gamma
recurrence, the functional equation, and the already fixed asymptotic calibration.  It may not
use the location, norm, or right/left orientation of an individual zero to choose a cochain.

Equivalently, one may construct a pre-divisor relative identity

```text
D_s-delta_2 E_s = Xi(s) R_s,                            (8)
```

in a source-selected singular completion, provided `R_s` has a regular on-shell boundary value.
The completion and regularity are substantive requirements: the formal expression
`R_s=(D_s-delta_2 E_s)/Xi(s)` is not accepted.

## 3. Why this sharpens the leading route

The previous calibrated comparison demanded equality of every finite prime-jet observation and
then invoked joint faithfulness.  The new consumer needs only one source-cohomological fact:

```text
reflected Mertens boundary class = 0 in H_0(C/2Z).       (9)
```

This is weaker than equality of the full prime vectors and matches the proved translation by two
of the completed source.  It also survives every nonzero finite differential clock by `(3)`.  The
open work has therefore moved from an unspecified faithful comparison functor to a concrete
relative-coboundary descent for the actual completed shift defect.

## 4. No-go attacks, positive successors, and general HT insight

1. **RH-equivalent redressing.** Postulating `(5)` does not advance RH.
   **Positive successor:** `(3)` is a proved terminal consumer and `(7)` names the exact independent
   source producer that would finish the proof.
   **General HT insight:** cohomological exactness is meaningful only when the primitive is selected
   by the constraint source rather than reconstructed from its exceptional divisor.

2. **Local-principal-part no-go.** Recentring two abstract simple poles erases their affine
   locations and makes every residue line isomorphic.
   **Positive successor:** orbit residue in `C/2Z` preserves the global translation class of each
   singularity.
   **General HT insight:** local singularity shape is not a complete invariant of a constrained HT
   conormal; affine orbit support is additional source data.

3. **Finite-differentiation repair no-go.** Applying a polynomial in the derivation cannot merge
   distinct translation orbits.
   **Positive successor:** every nonzero differential clock retains a nonzero top Laurent
   coefficient, so the same RH selector is stable through the full finite jet tower.
   **General HT insight:** derivative order and translation orbit form independent gradings of the
   boundary obstruction.

4. **Zero-fed primitive no-go.** A telescoping cochain fitted after seeing `rho` is circular.
   **Positive successor:** `(8)` demands one pre-divisor source identity with a regular on-shell
   remainder.
   **General HT insight:** a source primitive should be functorial under source operations and
   regular across the exceptional set; mere pointwise exactness has no generative content.

5. **Safe-half-plane exposure no-go.** Identity `(2)` exposes a canonical positive prime source but
   does not continue it into the orbit coboundary `(7)`.
   **Positive successor:** it fixes the step `q=2`, the coefficient filter `1-n^(-2)`, and the
   nonzero source orientation, leaving no translation-lattice gauge.
   **General HT insight:** exact shift exposure supplies canonical operator coordinates even when it
   does not solve the global continuation problem.

6. **Finite-support family no-go.** A holomorphic family of finite pole configurations cannot
   generally change discrete orbit incidence without a singular boundary event.
   **Positive successor:** the required object is a relative or singular completion whose on-shell
   boundary is finite, not a globally finite-support holomorphic family.
   **General HT insight:** constrained HT geometry naturally separates a regular source family from
   an orbit-graded boundary sheaf where discrete incidence lives.

7. **Hypertranscendence-alone no-go.** HT does not force the class `(9)` to vanish.
   **Positive successor:** HT supplies unbounded differential/source complexity, while the
   Euler--Gamma constraint must separately supply the orbit exactness.
   **General HT insight:** operator-growth complexity and orbit-residue conservation are
   complementary invariants; neither subsumes the other.

8. **Dihedral-symmetry no-go.** Put `x=-rho` and `Jx=-1-conjugate(x)`.  Then
   `Jx=conjugate(rho)-1`, and the signed charge conjugation `C=-J` fixes
   `e_x-e_(Jx)`.  The proved Gamma dihedral decomposition classifies this as a legitimate nonzero
   integer sector on every free mirror pair; reflection symmetry does not contract it.
   **Positive successor:** the coefficient of this free-orbit sector is a canonical bulk charge
   which a new Euler--Gamma coupling must annihilate.
   **General HT insight:** reflection can pair HT charges without localizing them; fixed-locus
   torsion and free-orbit integer content are distinct phases of a constrained HT source.

9. **Unframed shift-cohomology no-go.** For any symmetric nonvanishing rational gauge `Q`,

   ```text
   delta_2 logDeriv(Q Xi)
     =delta_2 logDeriv(Xi)+delta_2 logDeriv(Q).           (11)
   ```

   The correction is itself a shift-two coboundary.  The formalized centered-quartet gauge can
   insert an off-critical zero while preserving FE and Schwarz symmetry, so the unframed class of
   the completed shift defect modulo coboundaries cannot detect the insertion.
   **Positive successor:** the exact logarithmic primitive at a safe anchor does detect the gauge;
   for the formalized concrete quartet its change is `-608/425`.
   **General HT insight:** the primitive torsor or calibrated source framing carries divisor
   information which disappears in ordinary translation cohomology.  A constrained HT theory must
   distinguish a framed cocycle from its unframed cohomology class.

## 5. General conjecture extracted from the failures

```text
[CONJECTURE -- ORBIT-GRADED CORONA CONORMAL]
```

For a source-minimal constrained HT function with canonical translation group `G`, its boundary
conormal admits a source-invariant bigrading by

```text
(differential/source clock, affine orbit in C/G).        (10)
```

Finite source coboundaries have zero orbit sum in every affine grade.  Nonzero differential
operators can move the clock grade but cannot erase an isolated affine grade.  Hypertranscendence
appears as cofinal nontermination in the clock direction, whereas functional equations and exact
source recurrences impose conservation laws in the orbit direction.  The bigrading must be framed
by a calibrated primitive: passing immediately to unframed cohomology is not source-faithful under
rational symmetric orbit insertion.

The conjecture unifies, without identifying, four existing phenomena:

- the Mertens logarithmic corona tower has nontermination in the clock grade;
- Gamma's shift recurrence fixes the affine lattice and its calibrated boundary primitive;
- double-sine and elliptic-Gamma defect matroids record translation cosets;
- accumulating Schwartz constraints force DA carrier complexity to escape every fixed finite
  model.

The conjecture is not promoted as new knowledge.  New content would require a construction
invariant under source equivalence, a minimality theorem, and a nontrivial computation for at least
two inequivalent HT sources.

## 6. Verification and scientific verdict

Targeted Lean checks passed for the new module and its module build.  A scratch `#print axioms`
audit reports only `[propext, Classical.choice, Quot.sound]` for both principal theorems.

Orbit-residue obstruction and the critical-strip lattice argument are established mathematics.
The exact RH criterion is significant only as a consumer and is not independent new scientific
knowledge.  The completed source coboundary descent is significant because it would prove RH; its
novelty remains unverified until a source construction exists.

## Gates

- [x] completed-source translation step fixed to `q=2`
- [x] orbit-residue obstruction applied to the reflected Mertens pair
- [x] differential-clock stability formalized
- [x] critical-line conclusion formalized
- [x] exact RH equivalence formalized
- [x] every no-go supplied a nontrivial positive statement
- [x] every failure interrogated for general HT content
- [x] Gamma dihedral free-orbit sector audited
- [x] unframed shift-cohomology shown rational-quartet blind
- [ ] pre-divisor completed source coboundary constructed
- [ ] on-shell regularity proved without dividing formally by Xi
- [ ] source primitive shown independent of zero-location data
- [ ] orbit-graded corona conormal constructed source-invariantly
- [ ] independent novelty audit of the producer theorem
