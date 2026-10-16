# EWU fixed-window purification

Status: in progress. Scope: unconditional exact rank removal for actual smooth even pole-free sources, with the original support window retained.

## Corpus frontier

`EvenSectorSmoothSourceScalarization` produces a single smooth compact even pole-free source with the whole mixture autocorrelation. Its inverse-transform construction only proves some compact support: `EvenEntireAxisType.quadratic_strip_bound_of_axes` enlarges the imaginary-axis type by two, and the mixture type is accumulated over rows. `EvenSectorExactMomentRealization` preserves arithmetic trace and energy for general C² mixtures but supplies no window or whole-profile preservation.

This prevents those theorems from removing rank constraints inside a fixed aperture, where changing the domain changes the variational problem.

## Conjecture loop

1. Exact full-profile scalarization of arbitrary C² mixtures into smooth sources: rejected as a target. A smooth source has smooth autocorrelation; the current finite-regularity data does not give that. Even for an output merely C², the available spectral decay does not justify two continuous inverse derivatives. No such inference is used.
2. Fixed-window purification of smooth even pole-free mixtures: current target. The mixture identity controls the factor on the imaginary axis by the common aperture, independently of the number of rows. Dilation removes the additive type loss in the existing contour argument. The inverse factor therefore remains in the original interval.
3. Positive survivor/capstone: the actual fixed-window autocorrelation image is closed under arbitrary finite nonnegative mixtures. Every affine profile constraint, including blind trace, normalization, and archimedean energy, is preserved by a single source in the same window. No assertion of RH or blind positivity.

## Paper proof plan

Let every input source be supported in [-a,a]. Its transform on iy is bounded by its L¹ norm times exp(a y). The exact sum-of-squares identity on both axes gives the same type a for the entire even factor Q. Real-axis rapid decay and subquadratic global growth are already proved for this actual factor.

For any b >= 1, apply the corpus strip theorem to Q(b z). Its recovered type is ab+2. Rescaling the inverse integral gives zero at u whenever a+2/b < |u|. Given |u|>a, choose b sufficiently large. Thus the literal inverse vanishes outside [-a,a], with no enlargement. Fourier inversion identifies this inverse with the smooth source furnished by the existing factor theorem. The complete autocorrelation identity follows from Fourier injectivity as before.

## Audit requirements

Foreground leaf builds only, `lake --old build`; final `lake env lean` for each new module; Mathlib-name and axiom checks in /tmp; umbrella imports without umbrella builds; lint and diff checks. Preserve concurrent foreign changes. No numerical experiments, web search, axioms, proof holes, or heartbeat changes.
