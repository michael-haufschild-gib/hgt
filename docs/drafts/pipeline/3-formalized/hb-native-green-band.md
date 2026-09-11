# HB: actual causal principal and complete-source Green band

Stage: 3-formalized. The literal causal principal transforms and the full retained cusp source are identified inside the original Green band. Full joint causal-response transfer, physical left-QNM action, fixed-clock extinction and RH remain unproved.

Chain: literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH.

For the actual three principal exponents m=2ρ,1,2−2ρ, define

B(q)=max(3/2,Re(m₀),Re(m₁),Re(m₂)).

The proved Xi strip gives 3/2≤B(q)<2. The original circle-average formula identifies the Riemann kernel with the average of a positive real height raised to m. Its modulus is bounded by exp(Re(m)d), independently of Im(m). On the causal cone, arcosh(invariant(h,x,y))≤h, giving the actual kernel bound exp(B(q)h).

The literal source is uniformly bounded. Its original retarded integral therefore has pointwise bound C·t²·exp(B(q)t). Finite propagation confines its spatial support to [−t,t]. Lean derives the actual L² bound C·(t+1)³·exp(B(q)t), then absorbs the cubic into any strictly larger exponential rate. The proved native/physical equality transfers this bound to the existing `principalTimeResponse` without selecting a new evolution.

For every Re(w)>B(q), Lean proves absolute Bochner Laplace convergence and holomorphy of that actual time-family transform. The improved growth estimate supplies the second-time-derivative Laplace law. The original spatial distribution equation gives H² regularity; oddness gives the continuous representative's zero Dirichlet trace. Classical interior regularity and the existing negative-ray Wronskian uniqueness theorem identify this representative with the literal principal Green correction, including the physical onset transform. The actual L² classes agree almost everywhere on the original negative ray.

The explicit nonreal point w=(B(q)+2)/2+i lies in 3/2<Re(w)<2 and works for all three principal channels. Their actual bounded cutoff maps preserve convergence and transform identification. The final theorem `D4BMNativeLaplace.causalCuspSourceVector_laplace_original` identifies the full time-source transform with the original `cuspResidualVector` for every Re(w)>B(q). All three cutoff channels are retained.

The new intermediate convergence parameter depends on q. It does not select or change the Hawking clock. No vanishing current, QNM boundary limit or extinction hypothesis is introduced.

Module: [ThetaCuspHawkingBMNativeGreenBand.lean](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMNativeGreenBand.lean), 954 lines. Namespaces: `RHTower.D4BMNativeCircle`, `RHTower.D4BMNativeResponse`, `RHTower.D4BMJointSource`, `RHTower.D4BMNativeLaplace`. The adapted spatial proof uses the existing actual equation and domains with the newly proved convergence condition; existing modules are unchanged.

Validation: the complete scratch passed `lake env lean`; one harmless tactic-style warning remains. The exact leaf build uses cached dependencies and compiles only the new module. The checked source and five artifacts are installed, and one umbrella import is added. No umbrella/full build, axiom-print check or numerical experiment is used.

Search used broad Legendre and Hardy/Laplace queries and deep ground-state, complex-energy, frequency-coercivity, kernel-domination and L²-support queries. Candidate statements and source methods were inspected; partial and source-only search metadata were treated as discovery information. The decisive circle identity was verified in the current corpus. No external paper is a premise.

The remaining full-response transfer is documented in [the working card](../1-in-progress/hb-principal-growth-energy.md). The generic Hilbert causal datum needs every-positive-damping L² admission; then the full source-resolvent product can be inverted at a shift just above B(q) and identified with the already constructed original joint response by Laplace injectivity.

Final formal lint passed with existing large-file warnings. Module imports and local report links were verified. All owned checks completed; temporary audit and scratch files were removed. No owned Lean process remains.
