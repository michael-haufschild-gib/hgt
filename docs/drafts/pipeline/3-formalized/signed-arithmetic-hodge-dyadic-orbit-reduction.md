# Whole generator cutoffs split every dyadic correlation exactly

For the actual weighted cell clock W_2, let P_A retain the root and every
generator a<A at all levels. The cutoff commutes with every W_2^k. Its head
and tail are orthogonal, including after every dyadic shift. Consequently,

inner(W_2^k x,x)-inner(W_2^k P_A x,P_A x)
=inner(W_2^k (x-P_A x),x-P_A x).

The absolute real difference is at most norm(x-P_A x)^2, independently of k.
For every finite original cell profile f, its actual cell coordinates satisfy

abs(Re inner(W_2^k x,x)-Re inner(W_2^k P_A x,P_A x))
<=32 Gamma(f)/(1+log A), A>=1.

Exact zero/successor coordinate identities prove commutation. Disjoint
generator-coordinate masks prove orthogonality. Clock isometry bounds the
remaining tail correlation; the original-source all-level Gamma theorem
pays its norm. No projected-source Gamma bound or coarse norm factor enters.

Lean: `SignedArithmeticHodgeTheory/GeneratorOrbitCutoffsReduceTheDyadicClock.lean`.
Capstones: `logCellGeneratorHead_dyadic_pow`,
`inner_logCellGeneratorHead_tail`, `dyadic_correlation_sub_head`,
`abs_re_dyadic_correlation_sub_head_le`,
`abs_re_wholeCell_dyadic_head_error_le`.
Individual no-olean audit passes. Printed capstone dependencies contain only
`propext`, `Classical.choice`, `Quot.sound`.
