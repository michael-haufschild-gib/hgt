# Quantum-geometric metric--Berry Gram gap

- **ID:** `quantum-geometric-metric-berry-gram-gap`
- **Stage:** 3-formalized / not-new
- **Type:** THEOREM, `[VALUE RELATION]`, `[PHYSICS BRIDGE]`, `[HYPOTHESIS DISCHARGE]`
- **Scientific status:** `[LEAN-VERIFIED] [STANDARD PARENT THEORY] [NOT AN RH PROOF]`
- **Formal module:**
  `formal/GaloisForLFunctions/HTGeometry/QuantumGeometricTensorGram.lean`

## Result

For two complex Hilbert-space channels `u,v`, define the static quantum-geometric values

```text
metricArea(u,v)=||u||^2 ||v||^2-Re<u,v>^2,
berry(u,v)=-2 Im<u,v>.
```

Lean proves the exact decomposition

```text
metricArea(u,v)
 =projectiveGramEnergy(u,v)+berry(u,v)^2/4,              (1)

projectiveGramEnergy(u,v)
 =||u||^2 ||v||^2-|<u,v>|^2.                            (2)
```

It follows that

```text
berry(u,v)^2/4 <= metricArea(u,v),                       (3)

berry(u,v)^2/4 < metricArea(u,v)
  iff projectiveGramEnergy(u,v)>0
  iff LinearIndependent_C [u,v].                         (4)
```

Thus a strict quantum metric--Berry inequality discharges a complex two-channel linear-
independence hypothesis.  This is stronger for this corpus than recording the usual weak quantum-
geometric inequality alone.

## Moment/Krylov consumer

If `v_n` realizes a real moment sequence `m_n` by

```text
<v_i,v_j>=m_(i+j),
```

then Lean proves the exact value relation

```text
metricArea(v_0,v_1)-berry(v_0,v_1)^2/4
  =m_0 m_2-m_1^2,                                       (5)
```

and therefore

```text
berry(v_0,v_1)^2/4 < metricArea(v_0,v_1)
  iff 0<m_0 m_2-m_1^2.                                  (6)
```

Equation `(6)` directly closes the first strict Hankel-determinant premise from a physics-facing
strict quantum-geometric bound.  It composes with the existing Krylov, reflection-positive Hankel,
and prime--archimedean determinant APIs without adding a new carrier.

## Sharp no-go and positive replacement

Berry curvature alone cannot prove complex independence.  For every nonzero `v`, Lean verifies

```text
berry(i v,v)=2||v||^2 !=0,
metricArea(i v,v)=berry(i v,v)^2/4.                      (7)
```

The pair `[i v,v]` lies on one complex line.  This gives a nontrivial positive classification of
the failed curvature-only route:

```text
metricArea(u,v)=berry(u,v)^2/4
  iff not LinearIndependent_C [u,v].                     (8)
```

The useful source target is therefore strict metric excess over Berry curvature, not nonzero
curvature.

## Clock interpretation

The definitions use only inner-product values of two observed tangent channels.  No Hamiltonian,
state propagation, or external time is introduced.  The result supports the project motif:
hypertranscendental geometry is being probed through the observability structure of a clock, while
the physical quantum-geometric tensor supplies a static rank certificate.

## Cross-field audit

- **Genetics/genomics:** Price's selection-covariance equation is already formalized, including
  the size-bias response and cross-Hankel minor, in
  `HTGeometry/NormalizedMomentQuantumVariance.lean`.  Reintroducing it as a genetics wrapper would
  not strengthen the corpus.
- **ML/AI softmax and natural gradient:** categorical softmax Fisher/Hessian values reduce to the
  finite Gibbs covariance already present in `FiniteGibbsDifferentialBoundary.lean`; no duplicate
  wrapper was added.
- **ML/AI NTK/Fisher Gram identities:** these reduce to existing Gram/Jacobian and singular-value
  parent theory unless a source-defined strictness theorem is supplied.  The strict QGT gap was
  retained because it closes the actual two-channel independence/Hankel premise.

## RH impact

This does not produce the source-specific inequality required for RH.  It changes the live target:
for any completed prime--Gamma pair admitting a quantum-geometric realization, it is enough to
prove the strict metric--Berry gap.  Linear independence and first Hankel positivity then follow
automatically.

The obstruction is now exact.  A Berry/orientation calculation by itself is insufficient because
nonzero Berry curvature occurs at saturation on one complex line.  Any RH route using the QGT must
control the metric surplus, not merely the antisymmetric curvature value.  Higher Hankel
determinants still require higher-rank analogues or a source-produced positivity hierarchy.

## Verification

- the one missing exact module cache was built;
- the touched file passed a direct Lean check;
- `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`;
- the repository formal lint gate passes;
- no numerical computation, full project build, or concurrent Lean process was run.

## Literature

- T. Ozawa and B. Mera, *Relations between topology and the quantum metric for Chern insulators*,
  Phys. Rev. B 104 (2021), 045103.  Positivity of the quantum geometric tensor yields the
  metric--Berry inequality and its saturation analysis:
  <https://journals.aps.org/prb/abstract/10.1103/PhysRevB.104.045103>.
- A. Graf and F. Piechon, *Berry Curvature and Quantum Metric in N-band systems -- an
  Eigenprojector Approach*, for the standard QGT decomposition into metric and curvature:
  <https://arxiv.org/abs/2102.09899>.
- G. R. Price, *Selection and Covariance*, Nature 227 (1970), 520--521, for the genetics identity
  audited against the existing Price formalization: <https://www.nature.com/articles/227520a0>.

## Gates

- [x] exact metric--Berry--Gram decomposition
- [x] weak quantum-geometric inequality
- [x] strict gap iff complex pair independence
- [x] saturation iff complex pair dependence
- [x] explicit nonzero-curvature saturated phase-line witness
- [x] exact first Hankel determinant value relation
- [x] strict gap iff first Hankel positivity
- [ ] source-defined strict metric--Berry gap for a completed prime--Gamma channel pair
- [ ] higher-rank QGT criterion closing the full Hankel hierarchy
- [ ] RH
