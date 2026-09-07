# EDQ centered-tail phase cone

- **ID:** EDQ-CTP
- **Stage:** 3-formalized
- **Type:** independent signed comparison for the complete retained arithmetic tail; paper proof and Lean formalized
- **Sources:** EulerDeletionQuarticRemainder, ArithmeticLogarithmicFourierTail, ArithmeticFiniteCutoffZeroBudget, Mathlib.NumberTheory.ZetaValues.

## Full chain

Euler deletion → exact complex zero balance → signed arithmetic separation → exclusion of off-line zeros → RH. The finite-cutoff zero budget forces retention of the actual nonzero tail. This component derives an independent signed bound for that complete tail, with explicit joint dependence on spectral height and cutoff. Global comparison with the finite head remains necessary.

## Paper proof

Let P(x)=({x}^2-{x})/2+1/12 and Q(x)={x}^2*(1-{x})^2/24. The corpus proves Q''=P across the integer joins and

integral_N^infinity P(x)*x^(-s-2) dx = (s+2)*(s+3)*integral_N^infinity Q(x)*x^(-s-4) dx

for integers N>=1 and Re(s)>-1. Q has mean 1/720. Its mean-zero periodic primitive is

S(x)=r^5/120-r^4/48+r^3/72-r/720
    =r*(r-1)*(2*r-1)*(3*r^2-3*r-1)/720, r={x}.

S is continuous, vanishes at every integer, has derivative Q-1/720, and has absolute value at most 1/720. The bound follows from abs(r*(r-1))<=1/4, abs(2*r-1)<=1, and abs(3*r^2-3*r-1)<=7/4.

Exact integration by parts gives

Qtail_N(s)=N^(-s-3)/(720*(s+3))+(s+4)*Stail_N(s),

Stail_N(s)=integral_N^infinity S(x)*x^(-s-5) dx,
norm(Stail_N(s))<=N^(-Re(s)-4)/(720*(Re(s)+4)).

Therefore the literal normalized centered tail

C_N(s)=720*(s+3)*N^(s+3)*Qtail_N(s)

lies in the disk about 1 of radius norm(s+3)*norm(s+4)/((Re(s)+4)*N). If twice that numerator is at most (Re(s)+4)*N, then Re(C_N(s))>=1/2. In particular the full centered tail is nonzero there, without a zeta-zero premise.

At a zeta zero, the exact finite residual G_N satisfies

720*N^(s+3)*G_N(s)/(s*(s-1)*(s+1)*(s+2))=C_N(s).

This transfers the same positive real-part bound to the full finite head, retaining every endpoint term. The primitive estimate holds at all heights. A stronger signed-frequency argument uses the exact fourth-Bernoulli Fourier expansion

1/720-Q(x)=sum_(k in Z) [1/(16*pi^4*k^4)]*exp(2*pi*i*k*x),

with the zero-frequency coefficient defined as zero and total coefficient mass 1/720. The corpus's complete logarithmic-mode estimate bounds each integral by its coefficient times 4*N^(-Re(s)-4)/5 when abs(Im s)<=N. Hence

norm(Qtail_N(s)-N^(-s-3)/(720*(s+3)))<=N^(-Re(s)-4)/900,
norm(C_N(s)-1)<=4*norm(s+3)/(5*N).

For N>=2*norm(s+3), this gives Re(C_N(s))>=3/5 and nonzero complete centered tail. The condition is linear in height; all signed frequencies remain present.

Global exact-matching consequence: choose one actual positive simple critical zero rho. Its finite residual is nonzero at every N>=2*norm(rho+3). The previously proved uniform cutoff-growth law forces any N matching every simple critical zero below T to exceed this fixed threshold once T is large enough. Since rho is then included in that census, exact matching contradicts its nonzero residual. Thus for all sufficiently large T, no positive integer cutoff N, even chosen separately for each T, matches every actual simple critical zero below T. The survivor is the complete phase cone, exact residual identity, and quantitative approximation error. This does not rule out approximation with nearby displaced zeros, nor provide the missing off-line exclusion.

## Gates

- [x] Actual source and cross-route comparisons inspected; paper mean/primitive and joint bound derived.
- [x] Symbolic primitive and exact integration-by-parts identity.
- [x] Complete normalized-tail disks and positive real-part region, including linear-height signed Fourier control.
- [x] Exact transfer to the finite residual at zeros; uniform impossibility of exhaustive exact matching at any finite cutoff.
- [x] Leaf audit/wiring, new-only axioms, lint/index, ledgers, cleanup.
- [ ] Global signed head/tail separation; RH.

## Formal certificate

- Leaf: `formal/GaloisForLFunctions/RHTower/ArithmeticCenteredTailPhase.lean` (506 lines, 27 theorems, 5 definitions), namespace `RHTower.DeletionMixedRefinement`.
- Complete mean and correction: `quarticPrimitiveTail_eq_mean_add_fifth`, `norm_fifthPrimitiveTail_le`.
- Actual signed-frequency series and mass: `hasSum_quarticModeWeight_fourier`, `hasSum_quarticModeWeight`.
- Complete linear-cutoff error: `norm_quarticPrimitiveTail_sub_mean_le_linear`.
- Normalized source: `centeredTailPhase`; exact original-tail bridge: `centeredTailPhase_mul_eq_centered_tail`.
- All-height and linear-height disks: `norm_centeredTailPhase_sub_one_le`, `norm_centeredTailPhase_sub_one_le_linear`.
- Independent positive real-part bound: `centeredTailPhase_re_ge_three_fifths`; full-tail nonvanishing: `centered_tail_ne_zero_of_linear_cutoff`.
- Exact transfer at a zeta zero: `centeredTailPhase_eq_finiteResidual_at_zero`, `finiteCutoffResidual_ne_zero_at_zero_of_linear_cutoff`.
- Global exhaustive-matching obstruction: `eventually_no_finiteCutoff_exact_critical_matching`. Its statement quantifies over every positive integer cutoff at each sufficiently large height; it has no RH or matching-schedule premise.
- Scratch: `LEAN_NUM_THREADS=1 lake env lean /tmp/edq_tail_cone.lean`, exit 0, no diagnostics.
- Final audit: `LEAN_NUM_THREADS=1 lake build --old GaloisForLFunctions.RHTower.ArithmeticCenteredTailPhase`, exit 0; only this leaf built (5.2 seconds), cached dependencies. Umbrella import appended; no umbrella build.
- New-only axiom audit: `lake env lean /tmp/edq_tail_cone_axioms.lean`, exit 0. All 32 new declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`. No added axioms, admissions, or computational certificates.
- Repository lint: exit 0 (`formal lint passed`); existing file-size warnings only.
- Index: exit 0; refreshed formal/.lean_search-9925dbc05e32a559.db (3 changed, 0 removed). Generated references refreshed once.
- Cleanup: all owned check/build/axiom/lint/index processes reached terminal states; both owned scratch Lean sources removed, logs retained. No owned Lean/lake process remains.
- Logs: `/tmp/edq_tail_cone.check.log`, `.build.log`, `.axioms.log`, `.lint.log`, `.index.log`.

The positive cone applies to the explicit complex normalization C_N, not to the unrotated tail. Its transfer at zeros holds at critical and hypothetical off-line zeros alike. It therefore constrains the complete finite head but does not separate zero locations. Approximation can retain nearby displaced zeros while failing exact matching at the original points; no conclusion about such approximate divisor stability is asserted here. RH remains unproved and unfalsified.
