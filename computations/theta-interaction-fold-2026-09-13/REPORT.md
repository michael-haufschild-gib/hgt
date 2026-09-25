# Continuation stalls are interaction-coordinate folds

**Validated numerical outcome:** the two (+,-) theta stalls are explained by regular extrema of kappa along the collision locus. They occur where F_lambda is numerically zero while F_tt remains nonzero. Thus the evidence supports ordinary double spectral zeros at parameter folds, not triple spectral zeros. This is a numerical classification, not a Lean theorem or interval certificate.

| t | lambda | kappa | kappa''(t) | F_tt / envelope | Sufficient multiplier bound |
|---:|---:|---:|---:|---:|---:|
| 32.5656765399 | .0787955119300 | .355360840854 | -.4706784990 | -.4952682091 | .112237 |
| 40.6731452656 | .0630124114051 | .347587841752 | +.6152263755 | +.9138600006 | .089616 |

The envelope is exp(-pi*t/4)*(1+t^2)^(7/8). Lambda'(t) is respectively +.0328365543 and -.0289712631, so lambda remains a usable local coordinate where kappa fails. The different t locations do not establish that these two folds belong to one connected global branch.

All five prescribed cells were scanned. Three derivative roots were found; the extra (+,+) control root has kappa≈11.2226 and falls outside the admitted interaction range. The conductor-5 cell returned one refinement failure and no admitted root, so arithmetic specificity is inconclusive. Finite sign scans can miss roots; they establish no absence result.

**Validation:** fresh moment coefficient solves at 70/120/180 digits and fold location/refinement at 50/100/160 digits stabilize both candidates. At 160 digits, maximum scaled |F| or |F_t| is 1.37e-161, |F_lambda| is below 7.69e-159, and |kappa'| is below 1.88e-160. Independent integration of F,F_t,F_tt,F_lambda, both at the folds and at t+1/8 with parameters fixed, agrees within 3.21e-185 in envelope units. Theta summation uses 16 terms, cutoff 4 and 190-digit quadrature. No rigorous truncation bound is claimed. Runtime 230.03 seconds; owned process group cleaned; downloaded checksums passed.

**Conjecture challenged:** a continuation stall or disappearing original-gap candidate indicates loss of a source-compatible collision or a triple-zero event. The explicit parameter map supplies a positive alternative: the local collision locus continues while its projection onto kappa folds. Reparameterization resolves the interpretation of these stalls; it does not determine global first-collision order, initial zero ancestry, or off-axis zero trajectories.

**Consequence for HB/RH:** low-order source constraints permit locally complicated interaction geometry without violating the positive-multiplier bound. Solver failure cannot stand in for a source-selection obstruction. The literal HB action, causal corrections and joint boundary limits are not represented by this deformation family. No conclusion about the truth of RH or viability of the complete HB mechanism follows. Further broad scans of the same folds are not prioritized; the next campaign admission should address the missing original causal-action connection.

Reproduce with the archived code, coefficients, inputs, exact environment and frozen protocol. The algebraic collision parametrization is in the protocol; raw scan failures and excluded candidates are retained.
