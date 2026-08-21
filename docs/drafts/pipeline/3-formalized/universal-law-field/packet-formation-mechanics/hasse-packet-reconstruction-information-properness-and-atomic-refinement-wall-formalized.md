# ULF-PFM-1 — Lean certification record

**Card:** `hasse-packet-reconstruction-information-properness-and-atomic-refinement-wall.md`
**Status:** every displayed result of the card is Lean-certified, unconditional and axiom-clean.

## Card result → Lean declaration

| Card | Statement | Lean |
|---|---|---|
| (PFM.1) | the finite-difference row | `hasseRow`, `hasseRowReal`, `hasseFiniteDifference_packet` |
| (PFM.2) | the Euler integral for the row | `hasseKernel`, `hasseKernel_eq_sum`, `mellin_hasseKernel`, `gamma_mul_hasseRowReal` |
| (PFM.3) | the geometric depth tower sums to eta | `hasSum_hasseRow_eq_eta` |
| (PFM.4) | the complex row majorant | `norm_gamma_mul_hasseRow_le` |
| (PFM.5)–(PFM.9) | the joint packet law and its exact reconstruction | `hassePacketJointAtom`, `hassePacketJointAtom_factor`, `hasSum_hassePacketJointAtom`, `hassePacketRecovery`, `HasseHistoryProfile.kernel` |
| (PFM.6) | the Fermi–Mellin scale marginal | `fermiMellinDensity`, `fermiMellinNormalizer`, `fermiMellinMeasure`, `fermiMellinMeasure_isProbabilityMeasure` |
| (PFM.10) | the characteristic exponent is the completed eta quotient | `integral_phase_fermiMellinMeasure`, `fermiMellinNormalizer_eq_gamma_mul_eta` |
| (PFM.11) | the source zero relation | `hasSum_hasseRow_eq_zero_of_zetaZero` |
| (PFM.12) | exact phase orthogonality at a zero | `integral_phase_fermiMellinMeasure_eq_zero` |
| (PFM.13) | pure-state quantum Fisher information is four times the variance | `pureStateQuantumFisher_fermiMellin`, `momentNormalizedVariance_fermiLogMoment` |
| (PFM.14) | the Fisher lower bound `4τ⁻²` | `one_le_sq_mul_fermiLogVariance_of_zetaZero` (via `norm_one_sub_exp_mul_I_le`) |
| (PFM.15) | the log partition | `fermiLogPartition` |
| (PFM.16) | `F' = E[log T]`, `F'' = Var(log T) > 0` | `hasDerivAt_fermiLogPartition`, `hasDerivAt_fermiLogMean`, `fermiLogVariance_pos` |
| (PFM.17) | the likelihood ratio depends only on the scale | `llr_fermiMellinMeasure` |
| (PFM.18) | directed and symmetric costs | `toReal_klDiv_fermiMellinMeasure`, `jeffreys_fermiMellinMeasure` |
| (PFM.19) | centre selection | `jeffreys_fermiMellinMeasure_eq_zero_iff_center`, `fermiLogMean_strictMonoOn`; also the pre-existing `reflected_fermiFormationJeffreys_eq_zero_iff_center` |
| (PFM.20)–(PFM.23) | the atomic-refinement wall | `hasseAtomicMass`, `hasSum_hasseAtomicMass_fixedColumn`, `summable_hasseAtomicMass_iff`, `packet_formation_atomic_refinement_wall` |
| (PFM.24) | the conservation identity | `hassePacketJointAtom_factor` + `klDiv_splitFormation` |

## Modules

| Module | Public declarations | Role |
|---|---|---|
| `HTGeometry/ConstitutiveHassePacketFormation.lean` | pre-existing | §2, §4 selector, §5 wall |
| `HTGeometry/ConstitutiveHasseGlobalRenewal.lean` | pre-existing | the recovery kernel as a Markov kernel |
| `RHTower/HasseSondowRowMellin.lean` | 14 (new) | §1: the row, its Mellin representation, majorant, eta summation, zero relation |
| `RHTower/FermiMellinObserver.lean` | 30 (new) | §2–§4: the observer law, its normalizer, the log-moment exponential family, the response chain |
| `RHTower/FermiMellinPhaseProperness.lean` | 17 (new) | §3–§4: the phase identity, orthogonality, the Fisher bound, and reflected properness |

All wired into `GaloisForLFunctions.RHTower` and `GaloisForLFunctions.HTGeometry.UniversalLawField`.

## Proof notes

* (PFM.2) is proved by expanding the kernel `e^{-t}(1−e^{-t})^n` into the alternating exponential sum
  and integrating term by term; each term is `((k+1))^{-s} Γ(s)` by `mellin_comp_mul_left` applied to
  the Gamma integral.  (PFM.4) is then just `‖(t)^{s−1}‖ = t^{σ−1}` under the integral sign.
* (PFM.3) uses dominated convergence for series
  (`hasSum_integral_of_dominated_convergence`) with the majorant `t^{σ−1}(e^t+1)^{-1}`, whose
  integrability is the Mellin convergence of the corpus's Fermi kernel; the limit is the corpus's
  closed form `Γ(s)(1−2^{1−s})ζ(s)`, valid on the whole punctured right half-plane.
* The log-moment integrability that (PFM.13)–(PFM.18) need is obtained without any new
  `|log t|^k` estimate: the observer family is an exponential family with statistic `log t`, its
  `integrableExpSet` contains `(−σ, ∞)`, and mathlib's
  `integrable_pow_of_mem_interior_integrableExpSet` supplies every moment.  The response chain
  `M_n' = M_{n+1}` is `hasDerivAt_iteratedDeriv_mgf` transported through the tilt shift.
* `F'' > 0` is proved directly: the centred square integrates positively because its support
  contains an interval `(e^m, e^m+1)`.
* (PFM.14) combines the corpus chord identity `‖1 − e^{ix}‖² = 4 sin²(x/2)`, `|sin y| ≤ |y|`, and the
  corpus's weighted Cauchy–Schwarz `integral_mul_le_sqrt_mul_sqrt_measure`.

## Verification

* `lake env lean` on all three new modules: 0 errors, 0 warnings.
* `#print axioms` over their 61 public declarations: only `propext`, `Classical.choice`,
  `Quot.sound`.
* No `sorry`, `admit`, `axiom`, `opaque`, `unsafe`, and no added hypotheses beyond the card's own
  `σ > 0` / `s ≠ 1` conditions.

## Not claimed

The card's open core — a pre-zero source relation forcing the conserved symmetric work
`J(Q_σ, Q_{1−σ})` to vanish — is future work.  No RH conclusion is claimed.
