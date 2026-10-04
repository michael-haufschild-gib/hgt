# Actual theta kernel flattening and degree escape

- **ID:** LI-CLOCK-THETA-KERNEL-FLATTENING
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** [actual ratio correction](li-clock-theta-exact-ratio-band.md)
- **Statement:** Both literal B and K=B' have vanishing logarithmic slopes and uniform unit ratios under every fixed bounded shift, while their clock-weighted logarithmic slopes diverge.

## Gates

- [x] Complete dependency-closed proof with the actual full theta source.
- [x] Independent ALL F1–F9/source audit and precise installed-overlap review.
- [x] Exact positive survivors locally formalized; named/direct/imported axioms pass.
- [ ] Repository-wide lint gate green; currently11 unrelated unreachable modules.

## Scope and overlap

The B degree escape is already formalized in
`LiEvenCrossActualClockBorelGrowth.lean:137`. Reuse that proof. The simultaneous
flattening conclusions and K degree extension are paper-derived here; no
world novelty or corpus-absence claim. Fixed shifts do not control growing
history, and both ordinary resolvent sign masses remain infinite. Actual
signed source comparison and RH remain OPEN. No route retirement.

## Formalization: locally FINAL

- Correction501 is locally FINAL, including exact D/K→0. Current's frozen
 254-line formal plan `/tmp/li_current_theta_kernel_flattening_formal_plan.md`,
 SHA `b3eed160c5d48e7c280370e99456df6d969f621be5fe182a646324ca4a063df7`,
 and Pole's complete154-line independent audit
 `/tmp/li_pole_theta_kernel_flattening_plan_audit.md`, SHA
 `caee23cee7497bf397e377909cbc383974ef4ad109cdf6298d8201d597adfff2`,
 were read completely by root and pass every F1–F9/private admission.
- One-leaf scratch implementation released with the seven exact source limits
 plus the independently approved public `ContDiff ℝ ⊤ B` admission already
 established on paper. This eighth export lets later consumers obtain K's
 continuity without copying the ordinary derivative ladder again. Future
 `LiEvenCrossActualClockBorelFlattening.lean` now contains exact frozen589,
 SHA `ccdf4a14032fbc30aa427f40afe611691639a696fb6d613ab4bb083521eb6445`.
 Whole77013 and ALL8 scratch axioms36575 passed; all reports foundational-only.
 Root and independent Pole exhaustive full-source/API reviews PASS:
 `/tmp/li_root_theta_kernel_flattening_frozen_review.md` and
 `/tmp/li_pole_theta_kernel_flattening_frozen_audit.md` (190 lines).
 All8 public/all40 private declarations covered, with exact preservation of
 previously reviewed first365 lines and all new366–589 read. Named37813,
 direct34608 and importedALL8axes43195 passed, zero own warnings and all
 axiom reports foundational-only. Root wired umbrella import; index48383
 passed and all8 generated API rows were read. Lint13047 remains red solely
 for11 unrelated unreachable modules. Root final certificate:
 `/tmp/li_root_theta_kernel_flattening_final_certificate.md`.
 B's existing degree theorem is reused; no growing-shift/history claim.

## Complete audited paper

Initial125-line paper SHA256
`8e959980f4df50bb2a75d7b138a9a49bb0888961fd86ad1228e616dc2e04cef2`.
Independent148-line certificate `/tmp/li_producer_theta_kernel_flattening_audit.md`,
SHA256 `f208a7dba1d24b7fc943ec9cca558c10cb818df827b951feb58cbebe6dae88b8`,
read completely by root. Final paper below changes only status, installed
overlap and terminal search metadata; F1–F9 proof bytes are unchanged.
Final paper SHA256 `6b1697ed58c713da93065bb45766cb3d8b3ff62f08814242b0464149bd25a327`; complete body follows verbatim.

# Literal theta Borel kernel: fixed-shift flattening with escaping degree

Status: dependency-closed PAPER PASS after complete independent audit. RH OPEN.
No numerical computation, Lean claim, source replacement, or inverse sign.

## Fixed source and dependencies

Use exactly B(t)=sum_(j>=0) nu_j*t^(2j)/((2j)!)²,
K=B', and D=(K+tK')''=3K''+tK'''. All nu_j are strictly positive;
nu0=1. Retain the same normalized actual theta moments nu_j=R_j/R0.
The audited394 ratio-band paper supplies genuine complete derivative series,
positive-clock K,D, and D(t)/K(t)->0. The four new raw-ratio Lean exports
prove its key coefficient limit; full D/K Lean formalization is separate.

Installed LiEvenCrossActualClockBorelSource gives actual coefficients,
positivity, all-real summability/continuity, factorial envelope and genuine
first derivative. The higher derivative admissions follow from the existing
paper: every fixed polynomially weighted factorial envelope is summable on
compact clocks, before any full-series derivative is taken. In particular
K,K',K'',K''' are continuous, K is smooth, and K,K' are positive on t>0,
while K'',K''' are nonnegative there. K(t)>=nu1*t/2, hence K(t)->infinity.
There is no finite-degree truncation, RH premise, or asymptotic saddle claim.

## 1. Actual logarithmic slope vanishes

For t>0, positivity of the complete derivative series gives
  0<=K''(t)/K(t)<=D(t)/(3K(t))->0.                 (F1)
Fix any e>0. Choose T>0 such that K''(t)<=e²*K(t) for all t>=T.
Define the genuine differentiable energy
  E(t)=K'(t)²-e²*K(t)².
Then for t>=T,
  E'(t)=2K'(t)[K''(t)-e²*K(t)]<=0.
Consequently E(t)<=E(T), and, since K(t)>0,
  0<q(t):=K'(t)/K(t),
  q(t)²<=e²+max(E(T),0)/K(t)².                   (F2)
Since K->infinity and e was arbitrary, q(t)->0. For an explicit epsilon
proof choose e=epsilon/2, then make the final term<3epsilon²/4.
This avoids any assumed log-convexity of K. The energy inequality is
admitted by ordinary compact FTC and does not require E to have a limit.

The other direct positive consequence is
  0<=t*K'''(t)/K(t)<=D(t)/K(t)->0.               (F3)
Neither F1 nor F3 alone is used as an unsupported first-derivative claim;
F2 supplies that missing implication.

## 2. Uniform fixed-shift ratio on every compact shift interval

For each FIXED S>=0, take t>S. Since K>0 throughout[t-S,t+S],
the genuine logarithm has derivative q, and for every |s|<=S,
  |log K(t+s)-log K(t)|
    <=S*sup_(u in[t-S,t+S]) q(u).                 (F4)
The supremum exists by continuity on the compact interval. q->0 implies
the right-hand side->0 uniformly in s: every point in that interval is
beyond the same eventual threshold once t>=threshold+S.
Exponentiating gives
  sup_(|s|<=S) |K(t+s)/K(t)-1| ->0.               (F5)
Explicitly the displayed absolute ratio is at most exp(S*epsilon)-1
whenever q<=epsilon on the full interval. S=0 is exact equality.
This is an actual-source additive shift law, with S fixed before t grows.
No claim for growing shifts s=s(t), or for all history0<=s<=t, is made.

## 3. The original Borel kernel also flattens

B(0)=1 and B'=K give B(t)=1+integral_0^t K(u)du for t>=0.
For any fixed L>0 and t>L, positivity gives
  B(t)/K(t)>=integral_0^L K(t-v)/K(t)dv.
By the UNIFORM shift law F5, the right-hand side tends to L. As L is
arbitrary, B(t)/K(t)->infinity: for any M choose L>2max(M,0)+2 and
eventually every ratio in the integral is at least1/2. Therefore
  B'(t)/B(t)=K(t)/B(t)->0.                       (F6)
B>=1 guards division. Applying the same compact logarithmic integral
argument to B gives
  sup_(|s|<=S) |B(t+s)/B(t)-1| ->0                (F7)
for every fixed S>=0.

## 4. Full positive degrees escape despite the flattening

Let C(t)=sum_j c_j*t^(d_j), where either C=B with d_j=2j and c_j=Bcoef_j,
or C=K with d_j=2j+1 and c_j=k_(j+1). Every c_j>0. Both the complete
series and degree-weighted derivative series are genuinely summable at
every positive t, by the admitted factorial envelope.
For any fixed integer J>=0, positivity gives
  C(t)>=c_(J+1)*t^(d_(J+1)).
The complete mass of degrees j<=J is a finite polynomial of smaller
degree. Its ratio to C(t) therefore tends to0. Since the full degree
average has nonnegative terms,
  t*C'(t)/C(t)
    >=d_(J+1)*(1-sum_(j<=J)c_j*t^(d_j)/C(t)).     (F8)
The right-hand side tends to d_(J+1), and these degrees are unbounded.
To prove an arbitrary eventual lower bound M, choose J so d_(J+1)>2max(M,0)+2
and then make the prefix ratio<1/2. Thus
  t*B'(t)/B(t)->infinity,
  t*K'(t)/K(t)->infinity.                         (F9)
F6/F2 and F9 are compatible: the positive logarithmic slopes tend to0
while their clock-weighted values grow without bound. No quantitative
growth rate or monotonicity of those slopes is asserted.

## 5. Exact implication for the unresolved history comparison

The actual signed-history problem integrates over a growing interval0..t.
F5 controls every fixed lag interval uniformly, but does not give an
integrable global bound on the signed resolvent r. The independently
audited same-source resolvent has BOTH ordinary sign-part masses infinite.
Thus replacing K(t-s)/K(t) by1 inside the complete history is inadmissible
without a new tail/cancellation estimate. None is proved here. The exact
positive survivor combines F1–F9, including the already-installed B degree
escape. It is not a proof of r*g<=g or P>=0.

## Prior-corpus evidence and limitations

Direct deep query before writing: actual theta Borel kernel logarithmic
derivative tends zero additive fixed shift ratio tends one degree elasticity
diverges; budget90,no-refresh,JSON. Session53990 terminal0,elapsed77.175269s,
partial=true; decomposition timed out. Retrieval generation1166451,
coverage1166444/current1166462; inventory63614/63614 complete; semantic
coverage unmeasured. ROOT read ALL20 candidate and ALL20 source-argument
statements and the complete one ingredient set. Only the literal Borel
coefficient definition directly anchors this source; local theta action,
mixed finite-partition bounds and spectral-temperature tails do not imply
this clock limit. Those suggested ingredient transfers are rejected.
Targeted lexical follow-ups99358/38744/31379 all terminated0; three pages
contain ALL48 returned names/docs, read completely by root. Candidate, source,
proof and ingredient arrays are empty; coverage/freshness fields unreported.
They locate the already-installed B degree escape in BorelGrowth137, with
prefix42 and weighted121. Root read the exact121–145 bodies; the independent
reviewer read the complete144-line module. Other returned hits provide source
definitions, positivity, factorial admissions, Volterra or spatial-growth
bounds; they do not replace the proofs above. No exhaustive absence or world
novelty claim. Source proof relies on audited same-source D/K and admitted
positive series, not any irrelevant search ingredient.

Lean status: F9's B branch and its positive-prefix mechanism are already
formalized in LiEvenCrossActualClockBorelGrowth. The remaining new conclusions
await exact Lean formalization. Independent ALL125/F1–F9 paper/source audit
PASS: /tmp/li_producer_theta_kernel_flattening_audit.md,148 lines, SHA256
f208a7dba1d24b7fc943ec9cca558c10cb818df827b951feb58cbebe6dae88b8. Root read
the complete certificate. This revision changes only status/overlap and the
completed search ledger; every mathematical proof is unchanged.
No route retirement or RH proof/falsification is claimed.

## Lean certificate

- [x] 2 → 3: Lean `GaloisForLFunctions.RHTower`, `GaloisForLFunctions.RHTower.LiEvenCrossActualClockBorelFlattening`, `GaloisForLFunctions.RHTower.LiEvenCrossActualClockBorelGrowth`, `GaloisForLFunctions.RHTower.LiEvenCrossActualClockBorelCorrection`, `GaloisForLFunctions.RHTower.LiEvenCrossActualClockBorelSource`; `lake env lean` + module build pass; axiom audit `[propext, Classical.choice, Quot.sound]` only

Modules (all `lake env lean` clean, `lake build --old` clean, every public constant audited to `[propext, Classical.choice, Quot.sound]`, wired into `GaloisForLFunctions.RHTower`):
`GaloisForLFunctions.RHTower.LiEvenCrossActualClockBorelFlattening`, `GaloisForLFunctions.RHTower.LiEvenCrossActualClockBorelGrowth`,
`GaloisForLFunctions.RHTower.LiEvenCrossActualClockBorelCorrection` (the audited `D/K → 0` input), `GaloisForLFunctions.RHTower.LiEvenCrossActualClockBorelSource`.

| Claim | Declaration |
|-|-|
| `B` smooth, every fixed derivative admitted | `contDiff_liEvenCrossActualClockBorelKernel` |
| (F1) `0≤K''/K≤D/(3K)→0` | `tendsto_liEvenCrossActualClockBorel_third_div_deriv_zero` |
| (F2) `q=K'/K→0` (energy argument) | `tendsto_liEvenCrossActualClockBorel_second_div_deriv_zero` |
| (F3) `tK'''/K→0` | `tendsto_liEvenCrossActualClockBorel_clock_fourth_div_deriv_zero` |
| (F4)–(F5) uniform fixed-shift ratio for `K` | `tendstoUniformlyOn_liEvenCrossActualClockBorel_deriv_shift_ratio` |
| (F6) `B'/B=K/B→0` | `tendsto_liEvenCrossActualClockBorel_deriv_div_kernel_zero` |
| (F7) uniform fixed-shift ratio for `B` | `tendstoUniformlyOn_liEvenCrossActualClockBorel_kernel_shift_ratio` |
| (F8)–(F9) degree escape `tB'/B→∞`, `tK'/K→∞` | `liEvenCrossActualClockBorel_logarithmicDegree_tendsto_atTop`, `liEvenCrossActualClockBorelWeighted_div_kernel_prefix_lower`, `liEvenCrossActualClockBorelPrefix_div_kernel_tendsto`, `tendsto_liEvenCrossActualClockBorel_deriv_logarithmicDegree_atTop` |

## Log

- 2026-10-04 — Lean certificate audited; every numbered claim mapped to a declaration; moved to 3-formalized.
