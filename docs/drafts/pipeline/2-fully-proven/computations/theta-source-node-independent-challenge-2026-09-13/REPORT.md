# Complex zeros of the literal theta source

The literal theta source has robust numerical zeros inside its holomorphic strip, including approximately0.63883005360059i. This is an obstruction to treating the source through one holomorphic logarithm on the whole strip. It is not an RH counterexample: these are zeros in the source coordinate, not spectral zeros of zeta.

The source is Phi(z)=sum(n>=1)exp(z/2)(4q_n^2−6q_n)exp(−q_n), q_n=pi*n^2*exp(2z). The inspected corpus identifies its real-axis Fourier–Laplace transform integral exp(−iwx)Phi(x)dx withXiC(w) for abs(Im w)<1, and proves source holomorphy/evenness for abs(Im z)<pi/4. These are distinct source and spectral strips. No Lean build or fresh axiom audit was performed.

Of120frozen Newton starts at50digits,25converged and95failed (94iteration limits,1domain escape). The successful runs locate13distinct candidates in the upper source half-plane, listed below. Failure elsewhere does not establish zero-free regions, and13is not a complete count in any rectangle.

| Re z | Im z |
|---:|---:|
| 0.000000000000 | 0.638830053601 |
| 0.168696748273 | 0.746259110771 |
| 0.733839540171 | 0.751196622646 |
| 0.867062160817 | 0.759134694139 |
| 1.018240818353 | 0.765996945999 |
| 0.100493831138 | 0.771388873515 |
| 0.382915970686 | 0.772129868107 |
| 0.499138435325 | 0.775059390741 |
| 1.000811914173 | 0.778026046730 |
| 0.050065261555 | 0.781899698700 |
| 0.100335347719 | 0.783942370644 |
| 0.699250111143 | 0.784498681720 |
| 1.506130787771 | 0.784610604293 |

All13candidates passed100/160digit refinement and an independent Jacobi-theta-derivative formula. Each was checked at its four symmetry images without forcing evenness in the independent evaluator. All26validation jobs succeeded. At160digits the largest independent residual divided by the sum of absolute source terms is below1.9e-159; independent/native formula disagreement is below9.5e-209. Local circular phase samples at32,64and128points all give winding1 at both precisions. These are strong numerical checks, not interval-certified zero enclosures or a Lean theorem.

The independent formula is exp(z/2)[pi^2*exp(4z)*theta3^(4)(0,Q)/8+3*pi*exp(2z)*theta3^(2)(0,Q)/4], Q=exp(−pi*exp(2z)), where derivatives act on the Jacobi argument. This avoids the custom derivative recurrence and source reflection used for the search. Both polynomial terms and the complete convergent series are retained. Exact versions, source hashes, code, seeds and raw outputs accompany the reports.

Landscape/RH implication: positivity of Phi on the real axis is compatible with complex source nodes. A global phase construction based on −log Phi must handle these nodes, for example with local logarithms on a punctured domain. Phi itself remains regular there; a formulation that retains Phi as an amplitude does not acquire physical poles. This narrows the design of a contour-based proof without disproving RH or discarding the literal source. Any complete argument must reconstruct the full integral with all relevant cycles, coefficients and boundary contributions; a node or saddle census is insufficient.

Positive survivor: the source-plane nodal geometry is concrete and reproducible, giving actual punctures around which a saddle/contour method must be formulated. No nearest-node theorem, complete topology, all-height saddle law, action-identification theorem or extinction law follows. HB's full SS/SV/VV physical action and independent selection remain open.

Next discriminating computation: map the finite saddle-access network while explicitly stopping near source nodes, and determine where the complex saddle-coordinate map branches. Generic existence of a fold or a logarithmic pole is already expected from the nodal observation and is not a new discovery target.
