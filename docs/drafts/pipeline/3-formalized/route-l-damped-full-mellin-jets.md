# Route L: full Mellin jets of the same damped source

- **ID:** L-C45
- **Date:** 2026-09-11
- **Stage:** 3-formalized
- **Type:** literal jet admission / native Xi multiplicity and leading coefficient
- **Depends on:** [C44 weighted source and exact circle boundary](route-l-damped-weighted-source-boundary.md)
- **RH status:** unproved

Chain: complete original Green/BV source → fixed physical-reader agreement
→ conormal vanishing → RH. C44 closes weighted L1 admission and actual
zeroth Mellin readings. It also proves that the damping-two source retains
every original prime-circle Fourier mode and has no integrable original
undamped Green primitive. This card closes every finite literal Mellin jet
of that SAME source, its local derivative interpretation, and native Xi
multiplicity with the exact nonzero leading coefficient. The complete
packet and physical comparison remain open in [C46](../1-in-progress/route-l-damped-complete-xi-packet.md).
The module is `formal/GaloisForLFunctions/RHTower/Deninger/DeningerDampedSourceMellinJets.lean`.

## Proved: every finite literal jet passes to the actual limit

Fix a>1/2 and s with `1-a<Re(s)<a`. Choose delta>0 so both
`c_minus=Re(s)-delta` and `c_plus=Re(s)+delta` remain in that interval.
For each nonnegative integer k, the current corpus theorem
`Real.pow_div_factorial_le_exp` yields

`|t|^k <= (k! / delta^k)*exp(delta*|t|)`.

Thus, with `C=k!/delta^k`, for every real t,

`|t|^k*exp(Re(s)*t) <= C*(exp(c_minus*t)+exp(c_plus*t))`.

This is a direct two-case inequality, according to the sign of t. C44's
AE identifications show that, for `h_N=g_N-g_a`, the integrals
`int exp(c_plus*t)*|h_N(t)|` and `int exp(c_minus*t)*|h_N(t)|` are exactly
the two weighted L1 distances, hence tend to zero. Therefore

`int |t|^k*exp(Re(s)*t)*|h_N(t)| -> 0`.

The same majorant with g_a proves integrability of every literal Mellin
jet. The norm of the difference of the two literal jet integrals is bounded
by the displayed integral, so all finite jets pass to the original limit.
This paper mechanism uses the already-constructed source and has no new
source-decay, critical-line, jet-incidence or limit-agreement premise.
This mechanism is now closed in Lean.

## Derivatives and retained multiplicity

A smaller spectral neighbourhood and the two outer admitted weights justify
differentiation under the actual integral. Induction identifies the literal
k-th jet with the k-th complex derivative locally in the strip. The proved
C44 source identity then identifies these integrals with every derivative
of the reciprocal-zeta formula on that same strip.

At a=1, every actual Xi point rho is interior. Put alpha=(rho-1/2)*(-I)
and F(z)=XiC(z)*M(g_1)(1/2+z*I). The exact coordinate identity sends alpha
to rho. Local analyticity and M(g_1)(rho) != 0 imply that F and XiC have
the same analytic order. If m is the native xiSupportMultiplicity(rho),
Leibniz gives all derivatives of F below m equal to zero, and

`F^(m)(alpha)=XiC^(m)(alpha)*M(g_1)(rho) != 0`.

No simplicity or uniform multiplicity bound is assumed. The coordinate
and Xi coefficient are unchanged; the multiplier is the actual source
value, not a chosen normalization. This does not prove convergence of the
complete Xi Hilbert packet or agreement of its graph reader.

## Remaining complete packet and physical comparison

For fixed a>1 and every s in the full closed unit strip, the original local
factors obey

`|A_p(s)| <= (1+p^-a)^2`,
`|A_p(s)-1| <= 3*p^-a`.

The prime majorant is summable. It should supply a uniform product bound
and tail convergence, replacing the finite `4^length(P)` bound in C39.
Apply that bound to the actual Gaussian divisor field, identify its limit
with C44's literal evaluations, and transport the same full field through
the existing Green/provenance/native-Tate/fixed-Sonin maps. Preserve the
original Gamma residue normalization. Identify exactly which jet bounds
are required by each map; do not assume bounded multiplicity.

At a=2, C44's original circle discrepancy is nonzero. The next comparison
must retain it and any completion boundary. No full fixed-reader agreement
or cancellation follows from the scalar product or packet convergence.
No endpoint estimate at a=1, zero-damping continuation or pole exclusion
has been proved here.

## Current corpus method audit

`/tmp/route_l_c45_mellin_jets_deep.json` is terminal. All 20 candidate lemmas
and 20 source arguments were inspected; generated idea and ingredient lists
were empty. Generation 875940; semantic 2355400/2355414; partial deadline,
filter/judge and source refresh. Existing all-weight Meyer and entire-moment
lemmas require stronger source assumptions and cannot simply be applied to
C44's strip-admitted source. The direct exponential/polynomial inequality
was read in mathlib `Analysis/Complex/Exponential.lean` 245–260.

The implementation reads C44's actual weighted representatives and convergence,
mathlib L1 norms and local integral differentiation, the original strong-log
Mellin jet integrand, native Xi multiplicity, and local Leibniz expansion.
The full implementation was checked in scratch with this Lean toolchain.
C39's full-field transport is the next packet obligation, not an assumption
of the jet proof.

## Expanded search and failed transfers, 2026-09-11

All candidate lemmas and source arguments were read in each terminal report:

- `route_l_c45_local_differentiation_deep.json`: 20+20 hits; generation
  876049; semantic 2355571/2355573. Partial deadline, filter/judge and source
  refresh. `pow_abs_mul_exp_neg_le` confirms the polynomial/exponential
  mechanism. The local integral-differentiation method avoids assuming
  the stronger all-weight Meyer domain.
- `route_l_c45_transgression_hybrid.json`: 20+20 hits; generation 876081;
  semantic 2355597/2355597. Source refresh remains partial. The actual
  Green–Stokes descent theorem requires the original Meyer source; the
  strip-admitted limit does not yet meet that domain.
- `route_l_c45_joint_boundary_method_deep.json`: 20+20 hits; generation
  876082; semantic 2355597/2355597. Partial deadline, filter/judge and source
  refresh. No generated proof ideas or ingredient groups in these reports.

**Conjecture: a faithful integral lattice supplies one simultaneous boundary
correction. Fail as a transfer.** The retrieved
`DeningerIntegralCartierSecondSourceLattice` is a literal rank-two lattice
in the second Laurent neighbourhood. Its complexification is injective and
retains both source orientations and their nonzero quadratic sum. Reading
`SourceHorizontalSecondCartierPhysicalOrderModerationNoGo` shows that on
an actual strict-right Xi fibre, a coefficient-faithful additive Hardy
reader cannot make that quadratic class moderate. A reduced multiplicative
reader instead kills the source lattice. The positive survivor is the
exact faithful integral-coordinate realization, already in Lean; neither
statement constructs the needed common physical correction.

**Conjecture: a vanishing finite-stage Green correction removes the full
boundary. Fail.** The retrieved
`HedenmalmThetaActualStageGreenBalance` proves the actual correction tends
to zero in operator norm, while its complete Green boundary tends to the
fixed pinned boundary. The positive survivor is that exact decomposition
and convergence theorem, already in Lean. This does not transfer vanishing
to Route L's complete boundary.

**Pivot.** Admit all literal jets of the actual damped source first; then
retain native multiplicity by the local Leibniz formula, with the same
nonzero Mellin multiplier. Separately obtain a summable bound uniform over
the complete divisor before passing any full packet or reader to a limit.

## Broad recent-paper audit

Broad single-word arXiv searches included `localization`, `intertwining`
and `interpolation`; publication dates were checked on the source pages.

- Li–Sun, [Cusp restrictions and Bunke–Naumann invariants with level
  structure](https://arxiv.org/html/2609.11924v1), 10 September 2026:
  Lemmas 4.2–4.3 and Theorems 4.5–4.6 use one global integral modular-form
  correction at both cusps. Constant terms and the actual integral lattice
  matter. This prompted the simultaneous-boundary corpus query above.
  Its modular lattice and global class have not been constructed for Route L.
- Yamaguchi–Tajima, [Quantifying Symmetry Breaking](https://arxiv.org/abs/2609.11926),
  10 September 2026: abstract inspected; HTML unavailable. The conversion
  result concerns finite-dimensional i.i.d. quantum states and a family of
  information metrics. No physical isometry or symmetry conversion was
  imported into the proof.
- Cora–Fernández Tojo, [Stieltjes polynomial interpolation](https://arxiv.org/html/2608.24884v1),
  25 August 2026: Theorem 11.15 gives finite Hermite interpolation with
  explicit separation conditions. Theorem 9.7 requires integral interchange
  and polynomial annihilation before its remainder formula applies. It
  supplies no complete-source norm bound or automatic boundary cancellation.
- Pal–Shkolnikov, [Intertwining diffusions and wave equations](https://arxiv.org/abs/1306.0857),
  2013, appeared in the broad search; abstract inspected. Its positive
  hyperbolic-PDE intertwining kernel has not been produced for this source.
  This is an older result, not a 2026 paper.

## Lean validation

`lake env lean /tmp/route_l_c45_jets.lean` check7 passed with no diagnostics.
The final `lake build GaloisForLFunctions.RHTower.Deninger.DeningerDampedSourceMellinJets`
audit passed, rebuilding only this leaf (37 seconds; other graph results
were replayed). The module has 20 public theorems, one definition and three
private lemmas and is wired once into `RHTower.lean`. Formal lint passed.
No full/umbrella build, numerical experiment or axiom-print command was used.

Logs: `/tmp/route_l_c45_jets_check7.log`,
`/tmp/route_l_c45_jets_build.log`, `/tmp/route_l_c45_jets_lint.log`.

Principal declarations:

- `deningerDampedLogSource_jet_integrable`, `_jet_error_bound`, `_jet_tendsto`
- `hasDerivAt_deningerDampedLogSource_jet_integral`
- `iteratedDeriv_deningerDampedLogSource_mellin`
- `analyticOnNhd_deningerDampedLogSource_mellin`
- `deningerDampedLogSource_jet_eq_euler_derivative`
- `deningerDampingOne_source_all_xi_jets`
- `deningerDampingOneXiResponse_native_order`, `_lower_jets`, `_leading_jet`, `_leading_jet_ne_zero`

`scripts/formal_tools.py index` completed; all 21 public declarations are
present in the generated API. An exact lexical research query retrieves
`deningerDampingOneXiResponse_leading_jet_ne_zero` from the new module.
The card links and targeted diff check pass. No owned Lean process remains.
