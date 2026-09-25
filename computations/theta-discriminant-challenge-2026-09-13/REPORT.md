# Independent challenge of theta collision candidates

**Outcome:** six positive-parameter collision points were recovered by one-dimensional discriminants, refined at 100/160 digits with freshly computed moment coefficients, and checked by direct theta-source integration at 190 digits. Whole-family runtime 55.22 seconds; all remote checksums passed. None of the 18 scan cells returned a solver error.

| Direction | Model | Original gap containing collision | t | lambda |
|---|---|---:|---:|---:|
| (+,-) | additive | 4 | 31.9736224572 | .0498866672893 |
| (+,-) | product | 7 | 41.4910714806 | .0345801653424 |
| (-,+) | additive | 24 | 87.9178554010 | .0109767490713 |
| (-,+) | product | 24 | 87.9797867518 | .0101478418484 |
| (+,+) | additive | 24 | 88.1843376178 | .00589249371103 |
| (+,+) | product | 24 | 88.1725283880 | .00597673903943 |

All six satisfy the sufficient positive-multiplier bound. Maximum scaled collision residual at 160 digits is 1.26e-159. Direct integration of the corpus theta kernel and its Fourier derivative differs from shifted-Xi evaluation by at most 2.46e-170 in the frozen positive envelope units. Integration used 16 theta terms, cutoff 3 and subdivided quadrature. These are numerical checks, without interval bounds on truncation or roundoff.

The independent method recovered the named candidates, including the two different (+,-) locations; it did not reveal a missing positive-parameter root in the complementary sampled gaps. That last statement describes a 33-point sign scan, which can miss roots. It does not establish global first-collision order, exclusion of other collisions, or which original zero pair reaches a collision. Local continuation is required before interpreting pair ancestry or the direction of departure from the real t-axis.

**Consequence for HB/RH:** the source-interaction intervention measurably changes these local collision parameters while preserving the two imposed moment constraints. Its effect has different signs in different directions. Generic insufficiency of symmetry and low moments was already known; it is not the discovery claim. The surviving quantitative question concerns coupling-sensitive collision locations and thresholds. No literal-source deformation law, complete physical pairing, extinction mechanism or RH conclusion follows.

Next discriminating test: distinguish interaction-driven movement of a continued collision branch from changes in which original gap contains it. Use branch continuation and return-to-zero-parameter ancestry checks; failure to track a branch must remain inconclusive. Arithmetic controls require their own independently validated completions.
