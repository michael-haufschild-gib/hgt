# Mass-shifted adjacent-trace source absorption (2026-08-12)

Closed the independent-flux burden in the adaptive mixed-amplitude/completed P^sharp producer.

On a positive `(n+2)` shifted-Xi Hankel block, actual inverse-Hankel traces satisfy
`F_n = -2 a_n + alpha_n = -a_n - a_(n+1)`. Hence completed history is
`sum_{j<n} alpha_j^2 + 2 sum_{j<n} beta_j + a_n(a_n+a_(n+1))`; two negative adjacent traces force literal source positivity, while source nonpositivity forces one trace nonnegative.

Differentiating the adjacent identity gives a one-block next-trace theorem:
`a_(n+1)' = D_n - a_n' > 0` already under `H_(n+2)>0`, with gap
`sum alpha_j^2 + alpha_n^2 + 2 sum beta_j + 2 beta_n + 2(n+1) beta_(n+1)`.
Both terminal trace signs propagate backward through one positive component, eliminating terminal flux recession. Future higher-face-gap theorem was reproved via adjacent traces only.

Lean modules: `HTGeometry/DegreeCenteredOrthogonalSourceJacobiHistory.lean`, `RHTower/XiShiftedCanonicalAdmissionDegreeCenteredArithmeticSource.lean`. Direct checks and target build passed; eleven capstones depend only on propext/Classical.choice/Quot.sound. Report equations 9.3.567--572 and stage-3 card updated. Novelty unverified.

Failed routes: generic Toda no-return (indefinite tau zeros), alpha sign from ordinary Hankel positivity (missing shifted localizer), factorial/Gamma fixed carrier (existing opposite-orientation no-go). Remaining exact obstruction: compatibility/properness/closedness of iterated higher-face escalation tower on cofinal parabolic schedule, or exact admission/effectivity restriction.