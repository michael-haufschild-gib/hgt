# EDQ: exhaustive exact matching of critical zeros by finite cutoffs

- **Status:** FAILED shortcut; EDQ remains open.
- **Exact scope:** replacing the full arithmetic source by its complete finite head and requiring exact agreement at every actual simple critical zero through a growing height. For all sufficiently large heights no positive integer cutoff works, even when selected separately at each height. At a fixed cutoff, exact agreement at all but finitely many simple critical zeros also fails. Controlled approximation and nearby displaced zeros are formalized; a separating retained-tail comparison remains open.

## Obstruction

The pole-cleared finite head G_N is entire, satisfies G_N(1)=1, and has norm at most `3*N*exp((log N+2)*norm(s))`. Jensen limits its matches among actual simple critical zeros up to T to `T*(6*log N+12)/log 2`. The unconditional simple-critical census is superlinear. Therefore a fixed cutoff misses at least `T*log T/(144*pi)` actual simple critical zeros eventually. Actual missed zeros occur above every prescribed height; their complete centered Bernoulli tails are nonzero.

The obstruction is uniform over growing cutoffs as well. The exact normalized complete centered tail has real part at least 3/5 for `N>=2*norm(s+3)`. At any zeta zero it equals `720*N^(s+3)*G_N/[s*(s-1)*(s+1)*(s+2)]`, forcing G_N to be nonzero there. Choose one actual simple critical zero rho. The polynomial growth forced by exhaustive matching eventually puts N above `2*norm(rho+3)`, while rho belongs to the census. This contradicts matching, uniformly over every choice of N.

## Positive survivor

The second pass retains the cutoff in the entire-function estimate and uses its fixed nonzero anchor. This gives the sharper explicit matching count `[log(3*N)+(log N+2)*(2*T+3)]/log 2`, the corresponding lower count of missed zeros, and the necessary scale `N>=T^(log 2/(864*pi))` for exact matching at large heights, uniformly over choices of N.

The residual is exactly the polynomial boundary minus the finite source integral. Its discrepancy from `(s-1)*zeta(s)` equals the complete centered Bernoulli tail times `s*(s-1)*(s+1)`. At a zeta zero and a cutoff N at least the absolute height, the signed Fourier tail estimate gives the explicit norm bound `norm(s*(s-1)*(s+1))*N^(-Re(s)-2)/15`. Thus approximate matching remains meaningful, with the full tail retained.

The complete quartic primitive has positive mean 1/720 and a bounded periodic fifth primitive. Exact integration by parts retains the next tail. Its full signed fourth-Bernoulli Fourier series gives `norm(C_N-1)<=4*norm(s+3)/(5*N)` when `abs(Im s)<=N`, hence `Re(C_N)>=3/5` for `N>=2*norm(s+3)`. This is an independent signed comparison for the complete normalized tail, with explicit joint dependence on height and cutoff. The exact transfer to the finite residual applies at critical and hypothetical off-line zeros alike.

The literal finite approximants also converge uniformly on every bounded positive-half-plane region away from the pole, with error at most `(M+1)^2/(15*N^2)` for `norm(s)<=M<=N`. Every nontrivial zeta zero, including multiple zeros, has arbitrarily small isolating circles on which all sufficiently long finite heads retain exactly its logarithmic-derivative winding. The head is nonzero at the original zero but has a distinct zero inside. This constructive contour and displaced-zero survivor is paper-proved and formalized in `ArithmeticFiniteSourceContour`; see [contour transport certificate](../3-formalized/edq-finite-source-contour-transport.md).

The displaced zeros have a full complex asymptotic law, not just convergence: for every nontrivial zero rho of multiplicity m, `N^(rho+3)*(z_N-rho)^m -> -rho*(rho+1)*(rho+2)/(720*g(rho)) != 0`, where the actual analytic factor satisfies `zeta(z)=(z-rho)^m*g(z)`. Logarithmic exponent drift tends to zero, so this fixed-center normalization retains the correct cutoff phase. Actual cofinal sequences realize the law, and their distance scale is `N^(-(Re(rho)+3)/m)`. Paper proof and Lean certificate: [finite-zero displacement law](../3-formalized/edq-finite-zero-displacement-law.md), `ArithmeticFiniteZeroDisplacement`. This still does not determine the limiting zero's real part.

Dependency-closed paper proofs and these exact statements are formalized in `ArithmeticFiniteCutoffZeroBudget` and `ArithmeticCenteredTailPhase`. See the [zero-count certificate](../3-formalized/edq-finite-cutoff-zero-budget.md) and [phase-cone and uniform-obstruction certificate](../3-formalized/edq-centered-tail-phase-cone.md). Exhaustive exact matching is terminal; controlled approximation retains a complete quantitative tail. Global signed arithmetic separation, and RH, remain unproved.
