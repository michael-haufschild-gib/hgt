Route N C14 completed (not RH).

New exact identity for critical marked Krein charge Q_t(p):
  1 + sign(t) * p * Q_t(p) = p^(-2|t|).
The RHS is a genuine multiplicative positive clock cocycle and equals 1 at any prime iff t=0. For t != 0, p is pointwise the unique real diagonal coefficient recovering this cocycle from Q_t.

The prime multiplier p is singular relative to fixed all-prime ell1 completion: it sends the summable witness p^-2 to nonsummable p^-1. Therefore it does not preserve primeL1Submodule and has no HasPrimeDiagonalQuotientMap.

Under bounded Fisher gauge g(p)=p^2/(p+1)^2 with Route R wall R_t=g Q_t, the unique Route R recovery coefficient is h(p)=p/g(p)=(p+1)^2/p and:
  1 + sign(t) h(p) R_t(p) = p^(-2|t|).
h likewise has no quotient map.

At Xi support with centered grade t=2 Re(rho)-1:
- Route N critical Krein sequence is summable iff Re(rho)=1/2.
- scalar Cartier atom landing is injective iff that Krein sequence is summable.
- scalar Cartier specialization is contractible iff the Krein sequence is not summable.
Thus ordinary scalar derived fibre contracts off line exactly when fixed-trace boundary obstruction survives: exact support exchange/Bockstein shadow.

New Lean module:
formal/GaloisForLFunctions/RHTower/HedenmalmGammaSewnTransverseModularCocycle.lean
Umbrella wired. Direct lake env lean passed. Headline axioms only propext, Classical.choice, Quot.sound. No forbidden declarations.

Docs updated:
- docs/drafts/pipeline/1-in-progress/hedenmalm-prime-normal-jordan-grade-separation.md with C14, N.28-N.29.
- docs/drafts/pipeline/1-in-progress/rh-current-frontier-map.md.

Higher-principle/open core:
"singular base change" is now explicitly the unbounded prime-clock deconvolution, not unspecified topology. Bounded/cofinal Hilbert Ward lift is killed by existing four-unit overspend. Remaining producer: construct invariant transverse half-density on every finite ordinary-prime/exponent-depth Euler-Gamma/co-Poisson boundary packet; prove strict nonzero cofinal passage on source-generated exceptional Cartier object before zero evaluation; identify modular cocycle as p^(-2|t|). Isotropy invariance would force it to 1 and t=0. Need avoid ordinary scalar derived base change, which has complementary support and erases off-line atom.

References: mem:research/route_n_krein_gauge_and_cokernel_nogo_2026-08-10, mem:research/route_n_gamma_sewn_critical_wall_2026-08-10.