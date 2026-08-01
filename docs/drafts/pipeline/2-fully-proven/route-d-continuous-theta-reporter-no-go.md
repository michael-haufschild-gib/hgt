# Route D continuous theta-reporter no-go

- **ID:** `route-d-continuous-theta-reporter-no-go`
- **Status:** fully proven on paper — Stage 2, awaiting Lean formalization
- **Route:** D — prime–archimedean Hankel sign and reconstruction
- **Claim class:** `[BRIDGE]`; Route D specialization of classical topology and measure theory
- **Novelty:** not claimed
- **Opened:** 2026-08-01
- **Computation policy:** no numerical computation; symbolic proof only

## Frozen exact claim

Let

```text
tau = thetaCuspContinuousSourceMeasure
a_j = xiThermalNode (xiThermalEnumeration j).
```

`[THEOREM]` If `node : R -> R` is measurable and continuous on `(0,infinity)`, then

```text
not (IsPrimeArchObservableWitness tau node).
```

The claim assumes neither RH nor a support hypothesis. A hypothetical witness first triggers the
existing unconditional Route D witness implications.

## Internal frontier

- `[CORPUS]` `hasSum_xiThermalEnumeration_positiveMoment 0` proves that `sum_j a_j` converges.
- `[CORPUS]` `xiThermalNode_pos` proves `a_j > 0` for every `j`.
- `[CORPUS]` `thetaCuspFullSource_pos_of_pos` proves the theta density is strictly positive on the
  source domain `(0,infinity)`.
- `[CORPUS]` `IsPrimeArchObservableWitness.pushforward_eq_primeArchXiCompactMomentMeasure` forces
  every complete reporter pushforward to equal the canonical atomic Xi measure.
- `[CORPUS]` `IsPrimeArchObservableWitness.measure_levelSet_xiThermalNode_pos` forces every
  enumerated thermal level set to have positive theta-source mass.
- `[LOCAL-RESEARCH]` the observable-carrier quantization card excludes null and countable fibres,
  and proves positive Lebesgue mass for every forced theta fibre. It does not exclude continuous
  reporters with positive-measure plateaus.

No corpus theorem closes continuity on the connected positive theta domain.

## External frontier

- `[LITERATURE]` Burnol's conductor operator gives a local operator derivation of the explicit
  formula and treats finite and archimedean places uniformly; it does not construct an atomic
  theta-source quotient (`arXiv:math/9902080`).
- `[LITERATURE]` Connes--Consani--Moscovici construct moment measures and Jacobi matrices for a
  finite set of local factors from squared local-factor densities; their measure is not the
  Xi-divisor pushforward of one continuous theta reporter (`arXiv:2403.01247`).
- `[LITERATURE]` Suzuki studies the Weil form through continuous screw functions and conjectural
  strong limits of finite-interval self-adjoint operators. This is continuity of a kernel/form,
  not a continuous deterministic map from theta density to the discrete Xi law
  (`arXiv:2606.09096`).
- Support transport under continuous maps, connected images, countability of convergent sequences,
  and atomless-to-atomic measurable quantizers are classical parent theory. The generic mechanism
  is therefore `[REDISCOVERED]`; no scientific novelty is claimed for the Route D specialization.

## Hostile attack and failure-driven conjecturing

1. **Stronger conjecture: every regular reporter fails.** False. An atomless probability space can
   be partitioned into intervals of prescribed masses, producing a monotone countably-valued step
   reporter for any prescribed countable atomic law. Such a reporter is target-fed but can be
   Baire-one. Thus Baire regularity, bounded variation, and countably many jumps do not by
   themselves obstruct the carrier.
2. **Does pure atomic pushforward force a continuous map to be constant in general?** No. It fails
   if source support is disconnected or target atom closure contains a nontrivial connected set.
3. **Why do those counterexamples not apply here?** The theta density is strictly positive on the
   connected interval `(0,infinity)`. The thermal weights are summable and positive, so `a_j -> 0`
   and `K = {0} union range(a)` is compact and countable. It contains no nontrivial interval.
4. **Could collisions make all thermal nodes equal?** No. A positive constant sequence cannot
   converge to zero.
5. **Does the proof secretly assume RH?** No. A witness derives the canonical pushforward law by
   the already formalized unrestricted carrier theorem, which itself derives RH internally.
6. **Can discontinuity close Route D?** No. Target-fed step quantizers show that discontinuity is
   necessary but carries no source content by itself.

**Verdict:** `BRIDGE`. The generic theorem is classical; the exact Route D consequence survives
hostile attack and removes continuous theta observables from the producer search.

## Dependency-closed paper proof

Put `a_j = xiThermalNode (xiThermalEnumeration j)` and

```text
K = {0} union {a_j : j in N}.
```

1. `hasSum_xiThermalEnumeration_positiveMoment 0` says `sum_j a_j` converges. Therefore the terms
   satisfy `a_j -> 0`. The set `K` is compact: it is the range of a convergent sequence together
   with its limit. It is countable because it is a singleton union a countable range. In particular
   `K` is closed.
2. By definition,

   ```text
   primeArchXiCompactMomentMeasure
     = sum_j ofReal(a_j) * dirac(a_j).
   ```

   Every summand is carried by `K`, hence the entire canonical measure assigns mass zero to
   `K^c`.
3. The theta source is

   ```text
   tau = (volume restricted to (0,infinity))
           with density ofReal(2 * thetaCuspFullSource).
   ```

   Its density is measurable and strictly positive on `(0,infinity)`. Consequently `tau` and
   restricted Lebesgue measure have the same null sets there. Every nonempty open subset of
   `(0,infinity)` therefore has positive `tau`-mass, and `tau` is carried by `(0,infinity)`.
4. Suppose `h : IsPrimeArchObservableWitness tau node`. Existing observable rigidity gives

   ```text
   node_* tau = primeArchXiCompactMomentMeasure.                 (1)
   ```

5. Fix `x > 0`. If `node(x) notin K`, continuity of `node` on `(0,infinity)` and openness of `K^c`
   make

   ```text
   (0,infinity) intersect node^{-1}(K^c)
   ```

   a nonempty open set. Step 3 gives it positive `tau`-mass. But `(1)` and step 2 give
   `tau(node^{-1}(K^c)) = 0`, contradiction. Hence

   ```text
   node((0,infinity)) subset K.                                 (2)
   ```

6. The continuous image `node((0,infinity))` is preconnected and is countable by `(2)`. Every
   countable preconnected subset of `R` is a singleton: if it contained `u < v`, preconnectedness
   would include the whole uncountable interval `[u,v]`. Thus there is `c` such that

   ```text
   node(x) = c for every x > 0.                                 (3)
   ```

7. The sequence `a_j` is not constant: it tends to zero while `a_0 > 0`. Choose `j` with
   `a_j != c`. Observable fibre quantization gives

   ```text
   0 < tau(node^{-1}({a_j})).                                   (4)
   ```

   Since `tau` is carried by `(0,infinity)`, `(4)` supplies `x > 0` with `node(x)=a_j`,
   contradicting `(3)`.

All quantifiers and imported results are discharged. The exact claim is `[PAPER-PROVED]` and has
survived the final hostile reread.

## Positive survivor and representation lesson

Continuity is the sharp generic boundary exposed by this attack:

```text
continuous theta reporter                     impossible;
target-fed countably-valued step reporter     always manufacturable in parent measure theory.
```

Therefore the missing source primitive cannot be a continuous scalar observable. It must be a
genuinely discontinuous measurable quotient or correspondence whose plateau partition is produced
by completed prime--Gamma structure. The mathematical delta is not “use a discontinuous map”; it
is that any proposed continuous spectral coordinate, continuous phase observable, or continuous
theta potential is now categorically excluded as the Route D producer.

## Formal target after Stage 2

```text
GaloisForLFunctions.RHTower.PrimeArchContinuousThetaReporterNoGo
```

Planned public surface:

```text
tendsto_xiThermalNode_enumeration_zero
xiThermalCompactNodeSet
xiThermalCompactNodeSet_countable
xiThermalCompactNodeSet_isCompact
ae_primeArchXiCompactMomentMeasure_mem_xiThermalCompactNodeSet
volume_restrict_Ioi_absolutelyContinuous_thetaCuspContinuousSourceMeasure
ae_thetaCuspContinuousSourceMeasure_mem_Ioi
countable_isPreconnected_subsingleton_real
not_isPrimeArchObservableWitness_thetaCusp_of_continuousOn_Ioi
```

## Gates

- [x] exact claim frozen before proof engineering
- [x] internal Route D collision audit
- [x] external parent and Xi-specific audit
- [x] Baire-one target-fed counterexample attack
- [x] disconnected-source and dense-atom-support attacks
- [x] dependency-closed paper proof
- [x] non-trivial positive survivor recorded
- [x] final hostile reread
- [x] Stage 2 promotion
- [ ] exact Lean formalization
