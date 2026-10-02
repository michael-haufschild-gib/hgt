# Completed prime supports defeat the Ramanujan coefficient-square ceiling

- **ID:** pm-ramanujan-completed-support-budget
- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Source:** ../1-in-progress/pm-paired-cutoff-gram-budget.md; route PM
- **Statement:** For every fixed 0<epsilon<1/2, completed Ramanujan prime-aperture norms diverge although their actual logarithmic coefficient-square mass stays uniformly bounded.

## Goal and exact scope

The rejected conjecture extends the natural-denominator energy candidate to
all supports obtained by completing a finite prime set. Its coefficients are
the actual Mobius-aligned Ramanujan coefficients, not arbitrary test weights.
The natural-denominator cutoff conjecture is not falsified by this result.

## Gates

- [x] Well-posed literal source and precise energy budget.
- [x] Dependency-closed paper proof, [PROVED HERE].
- [x] Positive survivor and failure theorem formalized; all audits passed.
- [ ] Standalone publication audit.

## Exact positive survivor and paper proof

For epsilon>0 put alpha=Re(1/zeta(1+epsilon)), b_p=p^(1+epsilon)-1, and

`kappa(S)=alpha*product_(p in S)(1+1/b_p)`.

For finite prime set S define the literal complete primitive and Mobius
floor sum

`U_S(N)=sum_(T subset S) a(product T)*P_(product T)(N)`,
`V_S(N)=sum_(T subset S) mu(product T)*(product T)^(-epsilon)*floor(N/product T)`.

[PROVED HERE] For every N, `U_S(N)=kappa(S)*V_S(N)`.

The actual weight recursion is a(p*q)=-a(q)/b_p for p not dividing q,
and the primitive recursion is P_(p*q)(N)=p*P_q(N/p)-P_q(N). Split the
powerset into subsets containing p and those not containing p. Then

`U_(insert p S)(N)=(1+1/b_p)*U_S(N)-(p/b_p)*U_S(N/p)`.

Mobius multiplicativity and integer floor division give

`V_(insert p S)(N)=V_S(N)-p^(-epsilon)*V_S(N/p)`.

Since `(1+1/b_p)*p^(-epsilon)=p/b_p`, the normalized V recurrence matches
the U recurrence. At empty S both normalized expressions equal alpha*N.
Induction proves the identity, with no infinite interchange.

Take the dyadic floor difference at positive t. The exact generator formula
`phi_d(t)=2*floor((1/(2*t))/d)-floor((1/t)/d)` gives

`U_S(floor(1/t))-2*U_S(floor(1/(2*t)))
 =kappa(S)*pmFinitePrimePowerDampedFermiSource(S,epsilon,t)`.

The left side is the completed Ramanujan Fermi aperture used in the Lean
statement. It retains the fixed q=1 packet.

The normalizer has an exact probability interpretation:

`kappa(S)=sum_(T subset S)|a(product T)|`, hence `alpha<=kappa(S)<=1`.

Indeed evaluate U_S=kappa(S)V_S at N=1. Here V_S(1)=1, P_q(1)=mu(q),
and a(q)*mu(q)=|a(q)|. Distinct prime subsets have distinct products, and
the corpus proves total absolute Ramanujan mass one. The lower bound also
follows from every local factor being at least one. Thus the normalization
is positive, bounded, and intrinsic to the actual source.

## Killing theorem

For 0<epsilon<1/2, the corpus proves the canonical finite-prime Mobius
Fermi norms tend to infinity. The exact source identity and kappa(S)>=alpha>0
transfer this divergence to completed Ramanujan apertures. Each finite
aperture is admitted to L2; no top-valued norm is concealed by `toReal`.

The coefficient-square mass on a completed aperture is at most

`L_epsilon=sum_q q*log(2*q)*|a(q)|^2<infinity`,

by injectivity of prime-subset products and the audited full-mass theorem.
Therefore, for every real C, eventually along canonical prime apertures,

`C*sum_(T subset S) q_T*log(2*q_T)*|a(q_T)|^2 < norm(aperture)^2`.

This is the exact formal failure statement; no uniform completed-support
coefficient-square ceiling survives.

## No-go closure

- **Exact killing mechanism:** norm divergence with bounded actual coefficient-square mass; `pmCompleteRamanujan_eventually_exceeds_logSquare_budget`.
- **Strongest positive survivor:** exact finite primitive and Fermi normalization, with normalizer equal to retained probability mass in [alpha,1].
- **New insight:** Mobius sign alignment and summable coefficient-square mass do not control arbitrary completed prime supports. A successful natural-cutoff proof must use denominator order and its boundary essentially.
- **Status:** Paper proof dependency-closed; exact survivor and failure theorem audited in Lean. Only the support-independent extension is retired.

## Lean certificate

Module: `formal/GaloisForLFunctions/RHTower/PMRamanujanCompleteAperture.lean`.
Main declarations:

- `pmCompleteRamanujanPrimitive_eq_normalized`
- `pmCompleteRamanujanFermiSource_eq_normalized`
- `pmRamanujanApertureScale_eq_weight_mass`
- `pmRamanujanApertureScale_ge_density`, `pmRamanujanApertureScale_le_one`
- `memLp_pmCompleteRamanujanFermiSource`
- `tendsto_pmCompleteRamanujanFermiSource_norm_atTop`
- `pmCompleteRamanujan_logSquareMass_le`
- `pmCompleteRamanujan_eventually_exceeds_logSquare_budget`

All 21 exports (four definitions, seventeen theorems) passed `#print axioms`
with only `propext`, `Classical.choice`, `Quot.sound`. Targeted
`lake --old build GaloisForLFunctions.RHTower.PMRamanujanCompleteAperture`
built only the new leaf. Final actual-file
`lake env lean GaloisForLFunctions/RHTower/PMRamanujanCompleteAperture.lean`
exited zero without diagnostics. The leaf is wired into `RHTower.lean`.
No full umbrella build, numerical experiment, added axiom, proof hole or
heartbeat increase was used.

## Log

- 2026-10-02 — Corpus search72 completed with snapshot coverage; all results
  inspected. Exact normalization and completed-support budget failure closed.
  Global lint reports twelve unrelated unwired modules; no error names this leaf.
