# Positive-weight endpoint order and calibrated short-window dissipation

- **ID:** thim-positive-weight-endpoint-order
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean 4)
- **Scope:** Exact short-window nonpositivity classification for nonnegative weights,
  including squarefree support and fixed positive harmonic scalar with bounded coefficients.

## Plan and gates

1. [x] Read current README and corpus frontier; select endpoint-order mechanism.
2. [x] Dependency-closed paper proof and baseline comparison.
3. [x] Verify required dependency leaves; formalize actual source and audit all axioms.
4. [x] Wire umbrella, index/lint, update ledger/memory, audit artifacts, clean scratch.

`update_plan` is unavailable; this card tracks work. README is read-only.

## Classical baseline and corpus audit

Classification label: **New formulation**. Classical objects are finite divisor sums
and r-even functions in Toth--Haukkanen, https://arxiv.org/abs/1009.5281;
shifted convolution is the setting of Coppola--Murty--Saha,
https://arxiv.org/abs/1612.03136. The proof uses elementary positivity of the divisor
incidence transform and discrete Dirichlet polarization, not a new estimate for
classical shifted-convolution asymptotics. No external novelty claim is made.

Corpus hybrid search returned the existing all-weight/squarefree **equality**
classification and unit-shift laws, but no positive-cone **order** classification.
Inventory coverage complete, partial=false; compiler freshness mixed. The new
short-window source had no compiled artifact at inspection, so it must be checked
before use rather than treating README claims as certification.

## Paper proof [PROVED HERE]

Let a=M0+1, b=M0+M+1, and D(c)=D_N(M0+M;c)-D_N(M0;c).
Write sigma_N(k) for the full observation state and R_N(k) for the radical state.

For nonnegative coefficients, sigma_N(b)|sigma_N(a) implies s_c(b)<=s_c(a):
every visible divisor of b is a visible divisor of a. For squarefree-supported
coefficients it suffices that R_N(b)|R_N(a). All responses are nonnegative, so
`2D(c)=-E(c)+s_c(b)^2-s_c(a)^2<=-E(c)<=0`.

Conversely, failure of full-state divisibility exposes a visible q>=2 dividing b
but not a. Failure of radical divisibility exposes such a prime q. Let u=1_{d=q},
so s_u(b)-s_u(a)=1 and H_u=1/q. Fix any H>0. Put
`Q=D(u)-1/q`, `t=H/(|Q|+1)`, and
`c=t*u+(H-t/q)*1_{d=1}`.
Then `0<t<=H`, `0<=H-t/q<=H`, hence every coefficient belongs to [0,H],
and the finite harmonic sum is exactly H. The defect is
`D(c)=t*H+t^2*Q=t^2*(|Q|+1+Q)>0`.
Only coefficients 1 and q are used; when q is prime this is squarefree-supported.
Thus even a fixed positive harmonic scalar and a bounded coefficient box do not
weaken the necessity of reverse endpoint-state divisibility.

## Complete harmonic boundary [PROVED HERE]

For nonnegative c, every term c(d)/d at a visible positive divisor is nonnegative.
Thus H_c>=0. If H_c=0, each term is zero, every visible coefficient is zero, and
every response and short-window defect is zero. A negative prescribed H has no
nonnegative realization. Combining this with the positive-H construction gives
the exact all-H classification: universal nonpositivity on the H-calibrated
nonnegative class holds iff `H<=0` or reverse endpoint-state divisibility. For the
squarefree class use radical states. This boundary is a corollary of positivity
of a finite sum and the main order classification, not an additional analytic premise.

## Intended exact conclusions

- Universal nonpositive short-window defect for nonnegative weights iff
  sigma_N(right) divides sigma_N(left).
- For nonnegative squarefree weights, replace sigma by R.
- The same equivalences hold on every fixed H>0 slice with all coefficients in [0,H].
- Under the order condition, retain the quantitative bound D<=-E/2.
- Order of observation states itself is detected by all nonnegative sieve responses.
- Complete H-calibrated classification including zero and infeasible negative H.

## Boundaries

The coefficient cone is nonnegative, not the signed Mobius/damped family. No new
global sign claim for those weights follows. Fixed H must be positive for the
converse construction; at H=0 a nonnegative visible weight is zero. No computations,
added axioms, heartbeat changes, full builds, or README edits.

## Formal verification and integration

- Source: `formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/NonnegativeWeightEndpointOrderAndCalibratedDefect.lean`.
- Final SHA256: `0fc3ea2455ec3f5f9a792631545ae2e36b3cfda24fc6d8044bd3fc4af0e4df05`.
- Actual source passed `lake --old env lean -o <leaf.olean> <leaf.lean>` with exit 0,
  no warnings. No umbrella or full build. Untouched short-window dependency also
  passed its source build; SHA256
  `e090ac704457c67f228ff7e36e8dee4696f1cfb24516ee44cf93f80ffead6f9c`.
- All 24 public theorems and both private helpers have exactly the standard axiom
  closure `{propext, Classical.choice, Quot.sound}`. Scratch-only audit exited 0.
- Artifact audit passed: final source hash, all 26 closures, all 24 baseline
  docstrings and generated API entries, fresh compiled artifacts, unique umbrella
  import, MainTheorems reachability, whitespace, and forbidden-declaration checks.
- Evidence: `logs/thim-order-{lean,dependency-lean,axioms,index,lint}.txt` and
  `logs/thim-order-audit.json`. First index/lint reports preserved with `-first`.
- One index/lint refresh resolved concurrent generated-file staleness. Final lint
  exits 1 with exactly three unrelated structural errors: unwired BVI modules
  `InteriorMartingaleQuadraticGradientAndRenormalizedDriftBudget` and
  `MultiLagBezoutLayerHierarchyAndFourStepInteriorCalculus`, plus existing root
  registration complaint for `TransHorizonIncidenceMechanics.lean`. No finding
  names the new leaf; no forbidden declarations or stale generated files reported.
- All owned build/audit/index/lint jobs reached terminal status. All five owned
  `/tmp` scratch files removed. Ledger and Serena memory preserve the result.
- Classification: **New formulation**, with Known/Corollary constituents explicitly
  labeled. External novelty is not claimed. Sixth contribution complete; ongoing
  THIM research goal remains active.
