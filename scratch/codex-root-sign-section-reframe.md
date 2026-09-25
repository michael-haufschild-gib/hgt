# Route T sign-section reframe — finite theorem, endpoint still open

Own research note; frontier map remains read-only. Novelty audit against indexed corpus found the finite prime-selection energy and half-Bernoulli *selection* average, but not the exact random-*sign* section identity below. Generic Walsh orthogonality is classical; the new claim is its coefficient-faithful application to this literal Möbius--divisor source. External priority is unverified.

For finite source index set `I`, label sets `a_i⊆U`, real coefficients `c_i`, processed coordinates `P⊆U`, and independent signs `ε_q∈{±1}` for `q∈U`, define

`F_P(ε)=Σ_{i∈I} c_i ∏_{q∈a_i\P} ε_q`.

Then the exact retained energy is

`E(P)=2^{-|U|} Σ_{ε∈{±1}^U} F_P(ε)^2`.

Proof: expand the square. The sign mean of two terms is one precisely when their remaining labels coincide, and zero otherwise; regroup by that common label. Equivalently, the retained label fibers are the Walsh coefficients of the sign-section polynomial, so this is finite Parseval. Scratch Lean checks the generic identity and its specialization to `mobiusDivisorSelectionEnergy` with `c_d=mobiusDivisorDilationChannel M d`, `a_d=d.primeFactors`, `U=mobiusDivisorSelectionPrimes M`.

For the *arithmetic* source, the section is

`F_{M,P}(ε)=Σ_{d∈mobiusDivisorSelectionIndices M} mobiusDivisorDilationChannel(M,d) ∏_{p∈d.primeFactors\P} ε_p`.

At `P=∅`, mean-square is the original quadratic diagonal; at `P=U`, every section is the complete signed Abel head squared. Prime processing is therefore **boundary restriction to ε_p=+1 followed by the remaining-sign L² norm**, not a generic positive martingale contraction. This explains why sign-randomization and independent prime-subset averaging are distinct operations.

An equivalent unnormalized Walsh law gives `E(P)=2^{|P|-|U|} Σ_{T⊆U\P} W_T²`, where `W_T=Σ_{A⊆U} c_A(-1)^{|A∩T|}` and `c_A=Σ_{i:a_i=A}c_i`. Thus processing `p∉P` decreases energy exactly when at least half of the surviving Walsh-square mass is on frequencies containing `p`. This turns the hard signed covariance into a weighted hypergraph elimination problem. It does **not** give a favorable prime: the arithmetic distribution of this mass is the unsolved input.

The endpoint and initial diagonal alone cannot bound an insertion path in general. On an `n`-coordinate cube, take `c_A=n-2|A|`, the sum of all singleton Walsh characters. Then for every processed set `P` of size `k`, direct finite orthogonality gives `E(P)=2^{n+k}(n-k)`, while `E(∅)=n2^n` and `E(U)=0`. Every ordering crosses an exponential intermediate barrier `E(P)/E(∅)=2^k(n-k)/n`. This is a generic falsifier, not a claim about the arithmetic source. It proves that a source-blind endpoint-to-path principle cannot close CCM-FU.

Whole-route meaning: the original difficult term is not removed. The representation suggests a genuinely different producer—an arithmetic theorem about the moving Walsh-square spectral measure that supplies an elimination order with uniformly bounded surviving mass. It must be proved for the literal coefficients; generic Parseval, typical random twists, and half-selection averages do not suffice. The reframe is a mathematical dictionary plus a falsified generic shortcut, not an RH proof or an established Einstein-like jump.
