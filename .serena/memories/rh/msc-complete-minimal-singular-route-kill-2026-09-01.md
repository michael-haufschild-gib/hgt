# MSC complete-minimal singular route kill

- Formal module: `formal/GaloisForLFunctions/RHTower/HedenmalmGammaSewnSquarefreeFisherCompleteMinimalSingularRealization.lean`.
- For every `σ>1`, `Re ρ>0`, exact physical MSC source/overlap columns admit an infinite-dimensional positive Hilbert realization whose normalized modes form a complete minimal system.
- Construction: two head coordinates, private tail per mode; alternating cofinal prime subsequences pin opposite heads; coefficient product `squarefreeMobiusMass ρ.re n / squarefreeMobiusTotal σ ≤ 1` leaves tail energy `≥1/2`.
- Private-tail biorthogonal system proves minimality; cofinal head pinning plus `ℓ²` tail decay proves completeness.
- For `0<Re ρ≤1`, every Bessel bound fails on a finite packet. At a strict-right Xi zero this coexists with the four-unit regular MSC germ.
- Route consequence: positivity, infinite dimension, completeness, minimality do not imply RH. Exact surviving MSC burden is derivation of Bessel/frame stability from source geometry.
- Main theorem: `RHTower.HedenmalmThetaSource.CompleteMinimalSingular.strictRightXiZero_mscCompleteMinimalSingularRouteKill`.
- Audit: targeted build PASS; axioms `[propext, Classical.choice, Quot.sound]`; module wired into `RHTower.lean`; global lint only pre-existing unreachable modules.