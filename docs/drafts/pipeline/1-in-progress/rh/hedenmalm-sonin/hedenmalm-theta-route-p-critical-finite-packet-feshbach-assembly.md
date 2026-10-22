# Route-P critical finite-packet Feshbach assembly

- **ID:** `P-G82`
- **Stage:** `1-in-progress`
- **Type:** exact finite physical block assembly
- **Status:** `[CORPUS-NEW] [PAPER-PROVED] [LEAN EXACT-BUILT] [UMBRELLA-WIRED] [NOT RH]`
- **Parent:** `hedenmalm-theta-route-p-ordered-prime-depth-plucker-chirality.md`
- **Lean target:**
  `formal/GaloisForLFunctions/RHTower/GammaSewnMobiusApertureStokesCriticalFinitePacketFeshbachAssembly.lean`

## Conjecture P-G82.A: physical gain survives arbitrary finite block assembly

Use literal critical harmonic aperture from hostile source cell. P-G81 proves it is admissible for
every prime and depth:

```text
a_crit < (e+1/2)log(p).
```

For any nonempty finite index type `I`, choose source packets

```text
(p_i,e_i),(p_i,e_i+1),(q_i,e_i),(q_i,e_i+1),  p_i<q_i.
```

Let `Z_i` be literal Cauchy--Binet partition mass, `M_i` physical complementary Fisher mean, and
`T_i` total Fisher clock. Define block fraction

```text
Phi_I = (sum_i Z_i M_i)/(sum_i Z_i T_i).
```

**Verdict: true, unconditionally proved.** Every `Z_i,T_i` is positive and P-G81 gives
`T_i/2<M_i<T_i`. Strict finite summation yields

```text
1/2 < Phi_I < 1.
```

No weights are fitted: Lean proves `Z_i M_i` equals literal raw complementary-Fisher sum of block,
and `Z_i T_i` equals literal raw total-Fisher sum.

## Consequence

For every retained label `pk`, assembled residual

```text
(1-Phi_I) informationDepletedWeight(pk)
```

lies strictly between zero and half information-depleted weight. Thus arbitrary finite physical
block assembly preserves positive-carrier sign and strict depletion.

## New knowledge

P-G79--P-G82 now close four progressively stronger gates:

```text
hostile cell -> every ordered prime pair -> every depth -> every nonempty finite block family.
```

Finite compatibility does not require uniform lower gain or fitted convex weights. Literal raw
partition mass is exact assembly measure. Remaining obstruction is specifically infinite/cofinal
and combinatorial: prove pairing/overlap compatibility and summability, then identify limit with
global weak-kernel Gamma/polar Feshbach operator.

## Lean realization

Headline declarations:

- `gammaSewnCriticalFinitePacket_aperture_admissible`;
- `gammaSewnCriticalPrimeDepthPacket_Partition_mul_mean_eq_rawFisherSum`;
- `gammaSewnCriticalPrimeDepthPacket_Partition_mul_total_eq_rawTotalSum`;
- `gammaSewnCriticalFinitePacket_Denominator_pos`;
- `gammaSewnCriticalFinitePacket_Numerator_gt_half_denominator`;
- `gammaSewnCriticalFinitePacket_Numerator_lt_denominator`;
- `gammaSewnCriticalFinitePacket_Fraction_mem`;
- `gammaSewnCriticalFinitePacket_ReducedWeight_mem`.

Exact audit:

```text
lake build GaloisForLFunctions.RHTower.GammaSewnMobiusApertureStokesCriticalFinitePacketFeshbachAssembly
Build completed successfully (12735 jobs).
```

Capstone `#print axioms` audit reports only `propext`, `Classical.choice`, and `Quot.sound`.

## P-G83 outcome and P-G84 survivor

P-G83 disproves complete ordered-prime-pair assembly: fixing prime `2` and depth zero repeats one
positive same-prime minor on every incident edge, forcing a positive cofinite denominator floor.
The failure is incidence multiplicity, not decay. P-G84 formalizes the positive survivor: canonical
adjacent-prime path has bounded incidence, an explicit summable depth/prime majorant, and an exact
cofinal physical Schur fraction in `(1/2,1)`. Remaining gate is identification with P-G78's global
weak Köthe kernel and completed Gamma/polar response.

## Honest boundary

P-G82 proves exact finite physical block assembly. It does not prove infinite summability,
exhaustion independence, equality with P-G78 weak-kernel Feshbach elimination, Gamma/polar moment
matching, completed Julia saturation, or RH.
