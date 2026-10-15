# TG: cubic causality does not imply positive critical contraction

Status: failed proof mechanism; positive survivor formalized. TG remains active.

The rejected conjecture was that the factorial cutoff's cubic causal window supplies a uniform bound on positive critical renewal mass. Precisely, there is no real constant bounding `ccmEulerRenewalCriticalMass (m!) N` for every positive `m,N` with `N<(m+1)^3`, even though surviving-prime work is identically zero there at time `log N`.

The positive survivor gives an explicit moving-scale lower bound. Put

`E=(log(4)+4)+(8+Mertens.mertensTail)`.

For every integer `n>=2` with `log(n)>=4*E`, the proved inequalities are

`ccmEulerCriticalMass ((n^2)!) (n^3) >= n/6`,

`ccmEulerRenewalCriticalMass ((n^2)!) (n^6) >= n^2/36`.

The same parameters satisfy `n^6<(n^2+1)^3`, so `ccmEulerSurvivingWork ((n^2)!) (log(n^6))=0`. Choosing `n` large proves unbounded mass within the causal window.

Paper proof: subtract the prime Mertens estimates at `n^3` and `n^2`. The prime window has logarithmic reciprocal mass at least `log(n)/2`. Every prime in that window is coprime to `(n^2)!`; moreover `n<=sqrt(p)` and `log(p)<=3*log(n)`. Summation gives rough critical mass at least `n/6`. The complete ordered product square lies below `n^6`, giving the renewal lower bound. The existing cubic causality theorem supplies exact vanishing of surviving-prime work. No prime number theorem or RH premise is used.

Lean status: all statements proved in `formal/GaloisForLFunctions/RHTower/CCMPrimeDeficitEulerMovingMass.lean`, imported by `RHTower.lean`. The unconditional closure is `RHTower.exists_ccmEulerMoving_cubic_window_large_mass`.

Validation: targeted `lake build --old +GaloisForLFunctions.RHTower.CCMPrimeDeficitEulerMovingMass`, scratch axiom audit, final direct `lake env lean GaloisForLFunctions/RHTower/CCMPrimeDeficitEulerMovingMass.lean`, and formal lint passed. Axioms: `propext`, `Classical.choice`, `Quot.sound` only.

Scope: this rules out contraction inferred from cubic causality alone. It does not rule out every adaptive cutoff choice, any signed estimate for the actual deficit, or TG. The retained Euler action and deleted-prime work must still be estimated with their actual cancellation. The main source-to-zero quantitative bound remains unproved. No external novelty claim is made.
