# SZ first-contact multiplier identity

- **ID:** sz-first-contact-multiplier-identity
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** docs/reports/rh-current-frontier-map.md, route SZ
- **Statement:** Extract a source-specific sign obstruction from the actual first-null-ground equation using bounded physical multipliers; a dilation identity is admissible only after its boundary and domain terms are proved.

## Hard target
Prove the literal canonical-head Gamma--prime--polar quadratic sign. First-contact reduction is already in the corpus; another conditional positivity receiver is not progress.

## Corpus baseline
- CCMRestrictedWeilPolarMultiplierCriterion: a hypothetical first pole-vanishing null ground coexists with strict positivity of every smooth interior source and arbitrarily small core Rayleigh quotients.
- CCMRestrictedWeilStrictApertureClosure: inward dilation converges in the logarithmic form norm. It gives no derivative at the endpoint and no sign for that derivative.
- CCMPrimePoleSchurKernel and CCMPrimePoleSchurGammaInterpolation: exact two-prime rigidity and finite-aperture mixed interpolation are proved. Their unknown constant does not pay the full signed source.
- SuzukiScrewDisjointCrossCoupling: the full kernel is not positivity preserving after any scalar shift.
- SuzukiCompletedCurrentSignedWindows: the complete pointwise symbol has both arbitrarily deep signed aperture windows. Supported quadratic pairing must be retained.

## Conjecture loop
1. Dilation-virial positivity at first contact. Open: ground-vector admission, moving-boundary term, and signed prime derivative. No proof and no disproof claimed. Generic virial lemmas returned by deep corpus search do not close any of these.
2. Bounded physical multiplier identities for the actual null equation. Investigate whether exact exponential multipliers cancel the polar sector and force a source-specific sign. Keep all translated prime edges and the full Gamma kernel.

## Validation and status
The full supported modulation comparison is now formalized and audited in `CCMRestrictedWeilModulationPhaseRecovery.lean`; its exact phase-recovery law and failure of eventual frequency monotonicity are recorded in `../../../3-formalized/sz-supported-modulation-phase-recovery.md`. Ground-specific first-contact cancellation and RH remain unresolved. This card remains active; do not retire the dilation route merely because its dependencies are hard.

## Source-grounded third conjecture: finite modulation comparison

For a fixed actual aperture source f, compare the full energies after modulation at t+h and t. Conjectured exact asymptotic: the Gamma difference and both polar contributions tend to zero; the finite prime-phase difference remains. This is a comparison of supported sources, not a pointwise-symbol floor. It supplies a test of monotonicity/virial proposals while retaining the actual arithmetic correlations.

Paper mechanism: the derivative of the Gamma rate is globally bounded and tends to zero at both infinities. Its fixed additive increments therefore vanish pointwise and have a uniform bound independent of the carrier. Dominated convergence against the physical Fourier mass proves the Gamma increment law. Physical modulation sends the two fixed polar charges to zero by Riemann--Lebesgue. Every prime translation intertwines with modulation by its literal logarithmic phase. The needed fixed-aperture form admission must be proved, not assumed.

Corpus search `restricted Weil modulation high frequency translated energy difference prime phase Gamma tends zero` returned partial results (generation 1223798, all files inventoried, compiler freshness mixed). Existing `CCMRestrictedWeilPolarFreeShift` explicitly excludes Gamma energy; `CCMCoherentGammaModulationRecurrence` concerns the different coherent quantile cost. No novelty claim is inferred from a search miss. This comparison alone does not prove canonical-head positivity.

## Paper closure of the modulation comparison

Write M_t f(x)=exp(2*pi*i*t*x) f(x), P_a for the literal finite prime operator, Q_a for the complete restricted Weil source, and u_t for the exact form lift of M_t Ju. The fixed-step law is

    Q_a(u_(t+h)) - Q_a(u_t)
      + Re<P_a M_(t+h) Ju, M_(t+h) Ju>
      - Re<P_a M_t Ju, M_t Ju> -> 0.

The weight increment is bounded uniformly in the carrier by the fixed shift. It proves form-domain admission at the same physical aperture and supplies an integrable majorant. No smoothness or unknown-ground domain premise is added. A simultaneous recurrence clock k_j -> infinity, chosen from all visible logarithmic prime phases once for the aperture, therefore satisfies, for EVERY u and fixed h,

    Q_a(u_(k_j+h)) - Q_a(u_(k_j))
      -> Re<P_a Ju,Ju> - Re<P_a M_h Ju,M_h Ju>.

For the literal positive pole profile w=exp(x/2)+exp(-x/2), Schur row energy is invariant under modulation and the unmodulated edge energy vanishes. The limit is thus exactly the full nonnegative Schur phase energy of M_h w. At h=1/(2*log 2), prime two has phase -1. If log 2 < 2a, its overlap row has positive integral, so the limit is strictly positive. The opposite starting phase, equivalently the comparison at -h, gives negative h-increments cofinally. This rules out eventual monotonicity of the full frequency-modulated energy, while preserving the exact phase-energy law.

This is NOT a negative-energy witness and NOT an obstruction to a ground-specific first-contact identity. The actual canonical-head sign remains the hard open problem. Dilation admission and its boundary contribution remain unproved; this modulation argument does not retire that route. Full scratch and production audits passed.

### Final leaf validation

Production `CCMRestrictedWeilModulationPhaseRecovery.lean` passed its exact foreground `lake --old env lean <module> -o <olean>` audit (73301, exit 0, no diagnostics). All eight public axiom queries passed (69365, exit 0), using only `propext`, `Classical.choice`, and `Quot.sound`. No umbrella build was run. Global lint reports fourteen unrelated unreachable modules; the exact list is in the P3 card.

Important quantifiers: the recovered phase law fixes the aperture and source before the carrier limit. Its common clock works for every such fixed source and shift, but convergence is not asserted uniformly over moving sources or growing apertures. It therefore does not supply the unresolved canonical-head Gamma--prime--polar sign or the moving-aperture Wronskian estimate. Next work must attack that ground-specific arithmetic cancellation, not manufacture further high-frequency variants.

### Post-closure ground attack

Deep corpus search1224119 (`restricted Weil null ground bounded multiplier second variation logarithmic form commutator pole constraints`) was partial, with all65305 files inventoried but predominantly pending/stale compiler evidence. Candidate statements, source arguments, empty proof ideas, and proposed ingredient sets were inspected. The suggested Nevanlinna denominator and conditional floor-carrier combination does not establish any actual ground sign. Direct source inspection confirms full first-contact translation saturation and exact constrained-ground source variance are already proved.

Attempt: derive an absolute sign contradiction using bounded multipliers of the first null ground. Limitation: stationarity and commutators alone retain no absolute scalar normalization; adding cI preserves commutators and minimizing eigenspaces while shifting the ground energy. This is an already-known obstruction, not a new result or a retirement of the multiplier route. A usable identity must keep the uncommuted source and its literal Gamma constant, prime autocorrelations, and polar cross term. No additional Lean receiver was written. The actual ground-specific cancellation remains open.
