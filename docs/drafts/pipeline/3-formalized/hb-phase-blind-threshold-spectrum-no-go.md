# HB phase-blind threshold-spectrum no-go

- **ID:** HB-PHASE-BLIND-THRESHOLD-NOGO
- **Stage:** 3-formalized
- **Type:** THEOREM / route-class no-go
- **Route:** HB completed-continuum threshold/zero-mode realization

## RH proof chain under test

`literal Einstein--Teukolsky source` → `completed finite-variation continuum plus threshold atom`
→ `radiative ++ extinction` → `fixed physical-clock covariance` → `complete HB cokernel extinction`
→ RH.

Conjecture C5: arbitrary strictly damped finite-variation modes and arbitrary `L¹` real-axis
continuum transients may depend on seed phase, but one source-independent threshold atom and one
phase-blind passive stationary term cannot asymptotically cancel the cubic AIME pole numerator at
both physical half-turn seed phases. Therefore this regular peripheral spectral class cannot be the
HB producer.

## Corpus origin

Internal Lean corpus search supplied:

- exact terminal-value law: damped finite-variation spectrum plus `L¹` boundary continuum tends
  precisely to its zero-frequency atom;
- exact zero-mode coefficient forced by late-time AIME cancellation;
- cubic AIME numerator reverses under `A ↦ -A` and is nonzero for every nonzero seed on every Xi
  divisor copy;
- fixed even quadratic Ward response cannot cancel AIME at both half-turn phases;
- complete HB cokernel extinction is exactly fixed physical-clock covariance and globally RH.

The corpus does not combine spectral terminal-value rigidity with half-turn phase tomography and
does not classify a common threshold atom against phase-dependent transient spectra.

## Literature audit through 2026-08-31

Targeted primary-source search covered:

- Sberna--Bosch--East--Green--Lehner, `arXiv:2112.11168`, which identifies AIME as a third-order
  secular effect and studies nonlinear mode projection, but does not classify threshold atoms under
  seed half-turn phase;
- Green--Hollands--Sberna--Toomani--Zimmerman, `arXiv:2210.15935`, which develops the conserved
  Teukolsky bilinear form and explicitly separates QNM transients from the zero-frequency branch-cut
  tail, but gives no phase-blind threshold-cancellation theorem;
- Spiers--Pound--Moxon, `arXiv:2305.19332`, which derives nonlinear second-order Teukolsky sources,
  without the cubic AIME/threshold phase classifier;
- León Vega--Svyatkovskyy Kholyavka--Datta--Jiménez Forteza, `arXiv:2606.02146`, which derives
  source-dependent spectral suppression of branch-cut tails, not a common-zero-mode obstruction.

No located source combines late-time peripheral spectral decomposition, cubic AIME phase parity,
and a threshold-atom uniqueness/no-go statement.

## Candidate sharp conclusion

Even allowing unrelated damped and absolutely continuous continuum data in the two phase sectors,
if both completed pole numerators tend to zero then uniqueness of limits forces the common threshold
atom to equal both `-N(A)` and `-N(-A)=N(A)`. Hence `2N(A)=0`, contradicting the unconditional
nonvanishing of AIME for `A≠0`.

The positive survivor is exact: any successful finite-variation threshold completion must carry the
odd cubic source phase in its zero-mode coefficient. Equivalently its threshold atom must be
source-adapted, not source-independent or half-turn even. Singular non-Rajchman peripheral spectrum
and infinite variation remain distinct branches.

## Paper proof `[PROVED HERE]`

Let `R₊(t)` and `R₋(t)` be arbitrary peripheral responses for seed amplitudes `A` and `-A`. Their
strictly damped finite-variation data, `L¹` boundary densities, and even underlying measure spaces
may differ. Let their threshold atoms be `z₊` and `z₋`; keep one common passive stationary term `M`.

1. Dominated convergence removes every strictly damped finite-variation component. The
   Riemann--Lebesgue theorem removes every `L¹` real-axis component. Hence the two full pole
   numerators converge respectively to

   `N(A) + M + z₊` and `N(-A) + M + z₋`.

2. Cubic AIME phase covariance gives `N(-A)=-N(A)`. Therefore asymptotic cancellation in both
   sectors forces

   `z₊=-(N(A)+M)` and `z₋=-(-N(A)+M)`.

3. Subtraction gives the exact threshold jump law

   `z₋-z₊=2N(A)`.

4. If the threshold atom is phase-blind, `z₋=z₊`; hence `2N(A)=0`. For `A≠0`, the corpus's exact
   Xi-fibre AIME theorem gives `N(A)≠0`, contradiction.

Thus no source-independent threshold atom can complete this regular spectral route.

## Lean certificate

Formalized in
`GaloisForLFunctions.RHTower.ThetaCuspHawkingAIMEPhaseBlindThresholdSpectrumNoGo`.

The module proves:

- exact late-time cancellation classification for arbitrary seed phase;
- threshold jump law `z₋-z₊=2N(A)` with unrelated transient spectra;
- impossibility of common phase-blind threshold cancellation for `A≠0`;
- closed route-kill capstone
  `d4BMPassivePeripheralSpectralPhaseBlindThresholdCancellationRouteKilled`.

Targeted module build passed `11406/11406`. `#print axioms` for the cancellation classifier, jump
law, local no-go, and route capstone reports only `propext`, `Classical.choice`, and `Quot.sound`.

## Hostile audit

- The two phase sectors may use unrelated transient spectra, densities, measures, and carrier types.
- Damping may accumulate at zero; no uniform spectral gap is assumed.
- Boundary continuum need only be `L¹`; no smoothness or compact support is used.
- No RH, zero simplicity, QNM completeness, positivity of transient coefficients, or numerical
  input is used.
- The conclusion does not exclude a threshold atom transforming oddly with cubic source phase,
  singular non-Rajchman peripheral spectrum, or infinite variation. Those are the exact survivors.

## Gates

- [x] exact RH chain and corpus origin
- [x] current-literature audit
- [x] dependency-closed paper proof and hostile audit
- [x] Lean formalization and targeted audit
