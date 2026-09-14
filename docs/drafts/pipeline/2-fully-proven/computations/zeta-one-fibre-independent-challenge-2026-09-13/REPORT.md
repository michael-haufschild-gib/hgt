# Independent access-path validation

All 12 selected repetitions completed at 100 and 160 digits using half the discovery step size. From zero 1, the real target approach reaches Re(s) approximately 48 at target distance 2^−48. From zero 6 it approaches the finite point 1.367688181122+38.419105560643i, where the independently evaluated zeta value is 1. Its three tested approach directions reach the same finite point. Zeros 57 and 60 supply further examples of the two behaviors.

Independent Euler–Maclaurin sums with two truncations checked nine spread path locations. Residuals were also divided by the remaining distance of the target from 1, so an absolute error floor could not masquerade as an accurate near-1 calculation. The maximum relative residual was 1.391e-81 at 100 digits and 6.625e-144 at 160 digits. Finite endpoints were separately refined against zeta(s)=1 and checked with the independent formula.

These checks support the selected finite observations, not an infinite escape theorem or every classification in the larger census. A zero's access type can depend on its path. The positive object to study is therefore a zero together with an access path, rather than a path-independent finite/escape label.

For RH, the findings separate the topology of nearby value fibres from rigidity of the zero fibre itself. Neither an asymptotic expansion valid far to the right nor an intrinsic label inferred from one path supplies that rigidity. Any proof using the access picture must retain its path dependence and cover the full divisor, including possible off-line zeros.

Reproduce with `python guard.py experiment.py`. Literal paths, raw trajectories, independent checks, environment and original checksums are retained. No Lean builds or formal proof claim.
