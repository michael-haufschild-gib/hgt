# Projection and composition of endpoint cuts

The height of the dilated lower divisor against the original upper jumps equals the height of the original lower divisor against jumps moved from $j$ to $\lfloor j/d\rfloor$. The two tests have identical positive quotient coefficients because $\lfloor j/(di)\rfloor=\lfloor\lfloor j/d\rfloor/i\rfloor$. The degree products differ by $(\sum_i u_i/i)\sum_j b_j\{j/d\}$. The fractional boundary absorbs this difference in the finite part. In a composition of two contractions, jumps already sent to zero are exactly the correction at zero. All positive quotients compose without any correction.

Lean proves `project_graph_height`, `project_quotient_coefficient`, `project_finite_part`, `project_opposite_degrees` and `contract_composition`. [Proofs](../../../../formal/GaloisForLFunctions/SignedArithmeticCorrespondences/ProjectionOfTheMixedGraphHeightUnderDilation.lean)
