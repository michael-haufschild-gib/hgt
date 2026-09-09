# Uniform full-unipotent block comparison for every congruence level

Status: dependency-closed paper proof and Lean formalization audited.
All three modules passed source checks and sole-target builds; formal lint
passed. RH is open.

## Exact result

For each positive congruence level n=N+1, let G be the literal quotient
SL₂(ℤ)/Γ(n), acting on its complete complex Euclidean coordinate space by
right translation. Let P be the full group average and P₊, P₋ the averages
over the complete upper and lower unipotent subgroups. Then

    ||v-Pv||² ≤ 16 (||v-P₊v||² + ||v-P₋v||²).

The coefficient does not depend on n or |G|. Both blocks use all n residue
parameters. This is a statement about complete subgroup averages, not a
constant for two individual generators.

## Dependency-closed paper proof

1. For a commutative ring with finite maximal spectrum, let a,b be coprime.
   At each maximal ideal m choose e_m=1 if a belongs to m and e_m=0 otherwise.
   Distinct maximal ideals are coprime. Chinese remaindering gives t congruent
   to e_m at every m. If a is in m, then b is not and a+tb reduces to b.
   If a is not in m, a+tb reduces to a. Thus a+tb belongs to no maximal ideal;
   it is a unit. This proof includes the zero ring. Every finite commutative
   ring has finite maximal spectrum by injection into its finite power set.

2. Write a determinant-one matrix as M=(a b; c d). Its bottom row is coprime,
   so c+td is a unit for a suitable t. Put M'=M U₋(t). If c'=M'₁₀ is a unit
   with inverse r, direct ring algebra using det(M')=1 gives

       M'=U₊((M'₀₀−1)r) U₋(c') U₊((M'₁₁−1)r).

   Multiply by U₋(−t) to recover M. Therefore four alternating factors cover
   SL₂ over every finite commutative ring. Lifting the four parameters through
   any surjective ring map proves surjectivity of its induced SL₂ map.

3. Integer reduction onto ℤ/nℤ is surjective. Its induced SL₂ kernel is
   exactly Γ(n), hence the actual quotient G is isomorphic to SL₂(ℤ/nℤ).
   Transporting the upper/lower parameter homomorphisms proves the required
   four-factor coverage of G. Every transported parameter j is identified
   with the literal class of the integer elementary matrix at j.val.

4. For a finite unitary subgroup average P_H and h in that subgroup,
   U_h P_Hv=P_Hv. Unitarity and the triangle inequality give
   ||U_hv−v||≤2||v−P_Hv||. Write g as upper/lower/upper/lower factors and
   telescope. With a=||v−P₊v|| and b=||v−P₋v||,

       ||U_gv−v||≤4(a+b),   ||U_gv−v||²≤32(a²+b²).

   The exact Reynolds identity
   ||v−Pv||²=(2|G|)⁻¹ Σ_g ||U_gv−v||² gives the coefficient 16.
   No representation dimension, gap, or mixing hypothesis is supplied.

## Original source and complete normalization

For the original Maass source vector F(z), its invariant mean is m(z).
Its centered components are F_q(z)−m(z). Define E(z) as (2n)⁻¹ times
all original upper and lower elementary pullback displacement energies,
with each parameter j in ℤ/nℤ represented by the integer j.val.
Each component, parameter, and its literal pullback is retained. Exact
block Reynolds energy identifies E with the sum of the two block variances.
The conclusions are

    Σ_q |F_q−m|² ≤ 16 E,
    D ≤ |G||m|² + 16 E.

The original multiplied normalized-chord identity gives E=D C, where C is
the same normalized average of upper/lower source chords. It includes common
zeros. At points with m=0 and D>0, 1≤16C.

## Scope and remaining source comparison

The growing quadratic cost of complete S/T words does not apply to this
four-block construction: its averaging blocks grow with the congruence level.
That changing family must remain visible in the geometric analysis. No
level-independent bound from these complete block motions to original full
Maass currents has been proved here. The invariant mean branch, complete
phase and pair currents, original measure and nodes remain part of the
quarter comparison. Independent full-Xi occurrence also remains open.

## Corpus discovery

Broad OR searches used the full local research index without per-module
caps: mixing/convolution/spectral/Kloosterman (18,741 rows; 4,175 modules),
incidence/determinant/unipotent/reduction/surjective (13,214; 3,519), and
stable-range/semilocal/unimodular-row/elementary-factorization (1,966; 170).
These are discovery counts, not counts of inspected proofs. Actual inspected
sources included Sl2ElementaryFactorization, FiniteProjectivePlaneSpectralGap,
IncidenceDesignBound, finite Reynolds energy, and mathlib's maximal-ideal CRT.
The new mechanism extends the existing field factorization to finite rings;
no external numerical computation or numerical result enters the proof.

## Lean audit

- `HTGeometry/FiniteRingSl2.lean`: 16 public declarations. Finite maximal
  spectrum, unit adjustment, explicit four factors, upper/lower parameter
  homomorphisms, naturality and induced SL₂ surjectivity.
- `HTGeometry/FiniteRegularBlocks.lean`: 9 public declarations. Exact block
  energy, fixed average, displacement bound and the complete coefficient-16
  variance comparison.
- `RHTower/SelbergMaassUnipotentBlocks.lean`: 17 public declarations and one
  local normality instance. Actual modular reduction, deck equivalence and
  four blocks, literal integer representatives, source energy, mean-preserving
  density estimate and multiplied chord reconstruction.

The public APIs are `FiniteRingSl2.exists_four_factors_finite`,
`FiniteRingSl2.map_surjective`, `FiniteRegularBlocks.variance_le_two_blocks`,
and `SelbergMaassUnipotentBlocks.variance_le_blockEnergy`,
`density_le_mean_add_blockEnergy`, `blockEnergy_eq_density_mul_chord`.
The first two namespaces are under `GaloisForLFunctions.HTGeometry`; the
source namespace is under `GaloisForLFunctions.RHTower`.

All complete scratch proofs and all three source files passed `lake env lean`.
Each final `lake build GaloisForLFunctions.<module>` compiled only its named
leaf target, verified from every preflight Building and final Built line.
No umbrella or full build ran. An existing cached informational tactic
message from EvenL2LogUnitary was replayed; no new source warning occurred.

All 42 public declarations are indexed exactly once; each module is wired
once in its umbrella. The complete 43-declaration axiom inventory includes
only `propext`, `Classical.choice`, and `Quot.sound`. There is no added axiom,
proof debt, numerical input, or computational oracle. Repository formal lint
passed with existing large-file warnings. No owned Lean/Lake process remains.
No frontier-map edits were made; concurrent peer work was preserved.

Audit files: `/tmp/sqb15_{ring,blocks,actual}_{preflight,build}.log`,
`/tmp/sqb15_ring_source.log`, `/tmp/sqb15_blocks_source.log`,
`/tmp/sqb15_actual_source.log`, `/tmp/sqb15_source_scratch.log`,
`/tmp/sqb15_axioms.lean`, `/tmp/sqb15_axioms.log`,
`/tmp/sqb15_audit_names.txt`, `/tmp/sqb15_index.log`, `/tmp/sqb15_lint.log`.
Discovery metadata: `/tmp/sqb15_{mixing,incidence,stable}_broad.json`.
These logs supplement the reproducible proof sources.
