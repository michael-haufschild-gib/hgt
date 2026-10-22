# ACCE — contributions of 2026-10-22 (session: damping average, autocorrelation, interior bump)

Folder `formal/GaloisForLFunctions/ArithmeticContinuationAndCriticalEnergy`, umbrella wired.
All modules below compile with fresh oleans and are imported by the umbrella.

## New modules and their headline theorems
1. `TheDampingAverageOfTheRelativeLossSuffices` — `relativeLoss E E' T ε = -(E' T ε)/(1+E ε T)`;
   `AveragedContinuation` (horizon-free bound on `∫_a^c relativeLoss`); `Admits.of_averagedContinuation`;
   `integral_relativeLoss_eq` (= `log((1+E_a)/(1+E_c))`); `AveragedContinuation.of_linearContinuation`
   (via `intervalIntegral.integral_le_sub_of_hasDeriv_right_of_le`, so `β'` need not be integrable);
   thinning-spike family `lossSpikeEnergy` (peak height `T+1`, width `(T+1)^-2`) separates averaged from
   pointwise; `intervalIntegrable_relativeLoss_dampedMobiusEnergy` unconditional (needs
   `continuousOn_dampedChebyshevError`, `continuousOn_signedDampingWork`);
   `riemannHypothesis_of_averagedDampingContinuation`, `riemannHypothesis_of_averaged_tangentNorm`
   (replaces BVI's pointwise integrable majorant of `‖E_ε‖_T` by its damping average).
2. `TheSignedWorkIsTheTangentAutocorrelation` — `tangentCorrelation T η ε = pronicPairing T E_η E_ε`;
   `signedDampingWork_eq_pairing_add_integral`: `W_T(ε) = ⟪A_δ,E_ε⟫ + ∫_δ^ε K_T(η,ε)dη`;
   diagonal = `‖E_ε‖²`; `riemannHypothesis_of_nonneg_tangentCorrelation` (budget = paid scalar
   constant `exists_uniform_scalar_damping_work_bound`), `riemannHypothesis_of_bounded_anticorrelationTotal`.
3. `TheAveragedBudgetIsExactlyAdmission` — `averagedContinuation_iff_admits`,
   `riemannHypothesis_iff_cofinal_averagedDampingContinuation` (first *equivalence* in the layer),
   `exists_admits_everywhere_not_linearContinuation`: a family admitted at EVERY parameter with no
   pointwise budget on any interval ⟹ the pointwise form of open problem (C) is not implied by RH;
   (C) should be stated in averaged form.
4. `TheMaxKernelFormOfTheDampingAutocorrelation` — `pronicPairing_prefix_eq_maxKernel`:
   `Σ_{n≤T}(Σ_{j≤n}a_j)(Σ_{k≤n}b_k)/(n(n+1)) = Σ_{j,k≤T}a_j b_k/max(j,k) − (Σa)(Σb)/(T+1)`;
   `maxKernel_quadForm_eq` (NB kernel psd, exact formula); `tangentCorrelation_eq_maxKernel`;
   `sum_Icc_pronic_tail_mass`; `dampedChebyshevIncrement η j = Λ_η(j) − m(η)`.
5. `ThePolarCalibrationOfTheMaxKernelForm` — `sum_one_div_max_eq_rowWeight` (`1−1/j+Σ_{j≤m≤T}1/m`),
   `sum_sum_one_div_max_eq` (`2T − Σ_{m≤T}1/m`), `maxKernelForm_increment_eq` (four-term split:
   prime-pair form, two row-weighted prime sums, explicit polar term) ⟹ cancellation to relative
   precision 1/T is the real price of the sign criterion.
6. `TheLevelCollapseOfTheMaxKernelForm` — `sum_sum_div_max_eq_level_sum`: the double kernel sum is a
   single scale sum `Σ_M (a_M B_M + A_M b_M − a_M b_M)/M`; `tangentCorrelation_eq_level_sum`;
   `pronicNorm_dampedChebyshevError_sq_eq_level_sum` (discrete `d(E²)=2E dE−(dE)²`).
7. `RelativeStabilityOfTheTangentFamily` — `tangentCorrelation_eq_half_energy_sub_difference`,
   `nonneg_tangentCorrelation_iff` (angle condition), `riemannHypothesis_of_relative_tangent_stability`
   (`‖E_η − E_ε‖_T ≤ ‖E_ε‖_T` ⟹ RH); anti-alignment is the only obstruction.
8. `TheEscapeIsAnInteriorBump` — `tendsto_dampedMobiusEnergy_nhdsGT_zero` (limit = pronic mass ≤ 1):
   BOTH ends of the damping range are paid uniformly in the horizon, so the escape is interior;
   `riemannHypothesis_of_no_interior_bump`, `riemannHypothesis_of_convexOn_dampedMobiusEnergy`,
   `exists_unbounded_interior_bump_of_not_riemannHypothesis`.
9. `TheSignedWorkChangesSignOnce` — `riemannHypothesis_of_signedWork_single_sign_change` (a shape
   hypothesis: no positive→negative sign change), `riemannHypothesis_of_monotoneOn_signedWork`,
   `riemannHypothesis_of_nonneg_signedWork`.

## Build/工具 notes
- `lake --old env lean <file>` to check; olean via `lake --old env lean -j 1 -o <olean> -i <ilean> <file>`
  (needed before a downstream module can import it).
- Do not `open Set` together with `Finset` in these modules (ambiguous `Icc`/`Ioc`/`mem_Icc`).
- `push_neg` is deprecated here: use `push Not at h`.
- `ContinuousOn.max` does not exist: use `ContinuousOn.sup`.
- `simpa using h.neg` breaks on instance paths for `HasDerivAt`/`IntervalIntegrable`; use `exact h.neg`.
