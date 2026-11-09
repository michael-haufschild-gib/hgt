# Decisive samples with arbitrarily large gaps

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Obstacle:** B136, necessity of power-saving gaps.

## Target

Construct one set D of positive integer degrees with no power-saving gap bound such that every tempered zero configuration without real zeros whose cubic-spline traces are bounded below on D is pure. This would refute necessity of power-saving gaps; it supplies no bound for ζ itself.

## Proposed mechanism

Exhaust impure configurations by countably many compact families with bounded tempered mass, a uniform gap from real zeros, and a protected off-line zero in a bounded region. Every tail of the integer degrees detects each impure configuration by the existing gap theorem. Continuity of each fixed-degree trace then gives a finite detecting block for each compact family and each lower-bound threshold. Place these blocks successively beyond arbitrarily large prescribed gaps.

## Required analytic step

Prove compactness of the actual configuration families and continuity of their actual spline traces; do not assume a compactness interface. Limits must retain integer multiplicities, strip and reflection conditions, temperedness, absence of real zeros, and the protected off-line zero. A bounded weighted counting mass must give uniform trace tails. Establish that the families cover every configuration in the stated class.

A finite-model or attained-top statement does not answer the target.

## Compact coordinates

Represent each zero occurrence by (σ,t), with 0≤σ≤1 and t=1/Im ρ; t=0 is an absent point. Add its horizontal reflection to obtain a genuine configuration. A positive summable weight w=1/(Im ρ)² has an injective rank r obtained by ordering decreasing weights, breaking ties by a fixed injection into ℕ. Then (r+1)w≤Σw. Filling unused ranks with t=0 represents every tempered configuration without real zeros, with its multiplicities, after doubling by reflection.

For integer K, use the closed coordinate family defined by (n+1)tₙ²≤K, every finite partial sum Σtₙ²≤K, and a protected off-line occurrence among n≤K with |σₙ−½|,|tₙ|≥1/(K+1). These families are compact by the product theorem and cover all impure configurations after reflection doubling. The index bound gives uniform control of finite-height multiplicities. The partial-sum bound retains temperedness in limits.

For each fixed lag, the cubic-spline contribution extends continuously by zero at t=0 and is O(t⁴), uniformly in σ. Thus its series is uniformly bounded termwise by C K²/(n+1)² and is continuous on each compact family. Every tail of the primes detects each impure configuration, so finite prime blocks suffice on these compact families. Blocks may start beyond arbitrarily large prescribed gaps. The target can therefore require D⊆primes.
