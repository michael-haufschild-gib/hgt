# Canonical semigroup aperture high-pass for the Xi prime source

- **ID:** mass-xi-semigroup-aperture-high-pass
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** ../../../reports/mass-shifted-spectral-trace-route.md · §9.3 Exact open core
- **Statement:** RH is equivalent to boundedness of one factored von-Mangoldt high-pass at fixed mass `1` and depth `3/4`, whose co-moving arm is an additional mass shift of the fixed carrier.

## Goal

Turn the graded aperture-gap classification into one canonical arithmetic integral with a common
Euler line and an exact mass-semigroup interpretation.  This exposes a source kernel suitable for
future cancellation attacks and removes contour-depth mismatch.

## Gates

- [x] 0 → 1  in-progress: exact parameters, common source line, semigroup attack
- [x] 1 → 2  fully-proven: dependency-closed paper proof
- [x] 2 → 3  formalized and audited
- [ ] 3 → 4  publication-ready

## Exact claim C15

Let `A(u)=|u|+2`, `b(u)=sqrt(A(u)^2-1)`, and `tau=sigma+iu`.  Then:

1. the carrier at mass `A(u)` is exactly the mass-`b(u)` deformation of the mass-`1` carrier;
2. the co-moving prime integral remains uniformly bounded when moved from depth `1` to depth
   `3/4`;
3. the aperture gap equals the single literal integral

`∫ [(test_1(3/4,tau,x) - test_A(u)(3/4,tau,x))`

`     * L_vonMangoldt(5/4+ix)] dx`;

4. boundedness of this integral for all real `u` is equivalent to RH.

## Approach

Use `mass_mass_pt_eq_mass_pt` with `A(u)^2=1+b(u)^2`.  Use legal-depth independence to transport
the co-moving bound to `3/4`.  Combine the two integrable prime edges before integration and factor
their common absolutely convergent von-Mangoldt series.  Specialize C14 at fixed mass `1`, depth
`3/4`.

## Hostile audit

- Fixed and moving kernels share one Euler point `5/4+ix`; no contour comparison remains inside
  the high-pass.
- The mass-semigroup statement is pointwise on the actual Xi carrier, not a formal analogy.
- No boundedness is inferred beyond the exact RH equivalence.
- The result is useful only if later arithmetic work exploits the factored kernel; it is not counted
  as full route completion.

## Complete paper proof `[PROVED HERE]`

Since `A(u)≥2`, the number `A(u)^2-1` is nonnegative and
`b(u)=sqrt(A(u)^2-1)≥1/2`.  Its defining square identity gives
`A(u)^2=1^2+b(u)^2`.  The exact mass-composition theorem therefore identifies the mass-`A(u)` Xi
point with the mass-`b(u)` deformation of the mass-one Xi point, copy by copy.

Both depths `3/4` and `1` lie strictly between `1/2` and `A(u)`.  Legal-depth independence equates
the corresponding complete moving prime integrals, so the explicit co-moving bound proved at depth
`1` holds unchanged at depth `3/4`.

At common depth `3/4`, both prime integrands are Bochner integrable.  Linearity of the integral
combines their difference.  Expanding the two integrands factors the common von-Mangoldt series at
Euler point `5/4+ix`, leaving exactly the difference of mass tests displayed in C15.  This single
integral equals C14's aperture gap specialized to fixed mass `1`, depth `3/4`.  C14 then identifies
its uniform boundedness with RH for every `sigma>1/2`. ∎

## Lean certificate

- Module: `GaloisForLFunctions.RHTower.XiMassPrimeSemigroupHighPass`.
- Composition: `xiComovingMassFamily_eq_mass_one_then_additional_pt`.
- Common-depth moving bound: `norm_xiMassBottomPrimeIntegral_comoving_threeQuarter_le`.
- Factored integral identity: `xiMassPrimeSemigroupHighPass_eq_apertureGap`.
- RH capstone: `riemannHypothesis_iff_xiMassPrimeSemigroupHighPassLineBound`.
- Direct Lean check — PASS.
- Targeted build — PASS (`9390/9390`).
- Axiom audit — only `propext`, `Classical.choice`, `Quot.sound`.
- Module wired into `GaloisForLFunctions.RHTower` umbrella.

## Log

- 2026-08-05 — C15 frozen after C14 and the rescaled-charge survivor exposed mass composition as
  the correct transverse coordinate.
- 2026-08-05 — paper proof, factored source identity, mass-semigroup law, targeted build, and axiom
  audit completed.
