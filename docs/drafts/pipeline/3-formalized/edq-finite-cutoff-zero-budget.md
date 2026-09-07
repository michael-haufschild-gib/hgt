# EDQ finite-cutoff zero budget

- **ID:** EDQ-FCZ
- **Stage:** 3-formalized
- **Type:** global quantitative cutoff constraint; paper proof and Lean formalized
- **Sources:** ZetaCentredSawtoothContinuation, ArithmeticLogarithmicFourierTail, ExponentialTypeZeroDensity, XiSimpleCriticalExponentialTypeBound, Zeta23SimpleCriticalDensity.

## Full chain

Euler deletion → exact complex zero balance → signed arithmetic separation → exclusion of off-line zeros → RH. Local value/slope exclusion leaves global coverage open. This component tests a global finite-cutoff replacement against the actual simple-critical census. It does not infer RH from sampling or retire EDQ.

## Paper proof

For an integer N>=1, retain the complete finite residual

G_N(s)=(s-1)*sum_{1<=n<=N} n^(-s)+N^(1-s)-(s-1)*N^(-s)/2+s*(s-1)*N^(-s-1)/12.

The existing centered Euler–Maclaurin identity and the exact mean restoration give

G_N(s)=(s-1)*zeta(s)+s*(s-1)*(s+1)*integral_N^infinity (B(x)+1/12)*x^(-s-2) dx,

where B(x)=({x}^2-{x})/2. Equivalently G_N is the pole-cleared residual obtained by cutting the full unit source at N. All endpoint and mean terms remain present. G_N is entire and G_N(1)=1.

Write u=norm(s), L=log N. For 1<=n<=N, norm(n^(-s))<=exp(L*u); norm(N^(1-s))<=N*exp(L*u); norm(N^(-s-1))<=exp(L*u). Since 1+u<=exp u and u<=exp u, summing the four terms yields norm(G_N(s))<=3*N*exp((L+2)*u).

Jensen at anchor 1 with radius T+1 therefore bounds any distinct zeros of G_N among actual simple critical zeros below T by

[log(3*N)+(log N+2)*(2*T+3)]/log 2.

For T>=1 this is at most T*(6*log N+12)/log 2. The unconditional simple-critical count eventually exceeds c*T*log T, c=1/(72*pi). Consequently, if G_N vanishes at every simple critical zero up to T, log N>=(c*log 2/6)*log T-2. In particular a fixed N cannot match those zeros at all sufficiently large heights, and exact matching cutoffs eventually require polynomial growth in T (an explicit positive exponent follows by absorbing 2).

Positive survivor: at every actual zeta zero the mismatch is exactly the retained tail times s*(s-1)*(s+1). Where N>=abs(Im s), the existing signed Fourier tail estimate bounds its norm by norm(s*(s-1)*(s+1))*N^(-Re s-2)/15. Exact matching and controlled approximation are distinct obligations.

## Gates

- [x] Actual corpus inspected; explicit nonzero anchor and parameter-uniform paper estimates derived.
- [x] Scratch entire finite residual, exact tail identity, growth estimate.
- [x] Explicit critical sampling budget and polynomial cutoff consequence.
- [x] Actual arbitrarily high mismatch witnesses and retained-tail estimate.
- [x] Leaf audit/wiring, new-only axioms, lint/index, current ledgers, cleanup.
- [ ] Independent global signed arithmetic separation; RH.

The counting theorem alone imposes a growth cost on exact matching. The [complete-tail phase theorem](edq-centered-tail-phase-cone.md) combines that cost with a nonzero retained tail to exclude exhaustive exact matching at every finite cutoff for all sufficiently large heights. Approximate reconstruction remains available. All stated constants and identities are proved symbolically in Lean.

## Formal certificate

- Leaf: `formal/GaloisForLFunctions/RHTower/ArithmeticFiniteCutoffZeroBudget.lean` (356 lines, 17 theorems, 3 definitions), namespace `RHTower.DeletionMixedRefinement`.
- Exact finite source: `finiteCutoffResidual_eq_boundary_sub_head`; exact retained tail: `finiteCutoffResidual_eq_zeta_add_tail`.
- Entirety and anchor: `differentiable_finiteCutoffResidual`, `finiteCutoffResidual_one`.
- Uniform growth: `norm_finiteCutoffResidual_le`.
- Explicit matching count: `finiteCutoff_matching_count_le`; height/cutoff budget: `finiteCutoff_matching_count_le_linear`.
- Unconditional missed count: `finiteCutoff_missed_count_lower`.
- Moving cutoff cost: `eventually_finiteCutoff_matching_log_lower`, `eventually_finiteCutoff_matching_power_lower`, with exact exponent `log(2)/(864*pi)`.
- Fixed-cutoff missed count: `eventually_finiteCutoff_missed_superlinear`, eventually at least `T*log(T)/(144*pi)`.
- Actual high nonzero-tail witnesses: `exists_high_finiteCutoff_nonzero_tail`.
- Controlled discrepancy when `N>=abs(Im s)`: `norm_finiteCutoffResidual_at_zero_le`.
- Scratch: `LEAN_NUM_THREADS=1 lake env lean /tmp/edq_cutoff.lean`, exit 0, no diagnostics.
- Final audit: `LEAN_NUM_THREADS=1 lake build --old GaloisForLFunctions.RHTower.ArithmeticFiniteCutoffZeroBudget`, exit 0; only this leaf built (4.9 seconds), cached dependencies. Existing dependency diagnostics were replayed. Umbrella import appended; no umbrella build.
- New-only axiom audit: `lake env lean /tmp/edq_cutoff_axioms.lean`, exit 0. All 20 new declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`. No added axioms, admissions, or computational certificates.
- Repository lint: exit 0 (`formal lint passed`); existing file-size warnings only.
- Index: exit 0, 2 changed and 0 removed; generated references refreshed once.
- Cleanup: all owned check/build/axiom/lint/index processes reached terminal states; both owned scratch Lean sources removed. No owned Lean/lake process remains; logs retained.
- Logs: `/tmp/edq_cutoff.check.log`, `.build.log`, `.axioms.log`, `.lint.log`, `.index.log`.

The matching criterion is an explicit premise of the cutoff lower-bound theorem; no existence of a matching cutoff schedule is assumed or proved. The missed-count and high-witness theorems are unconditional for every positive integer cutoff. These results constrain finite-source substitutions but provide no all-height signed comparison excluding off-line zeros. RH remains unproved and unfalsified.
