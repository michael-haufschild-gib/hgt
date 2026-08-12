# One-dimensional affine reflection--depth selector

- **ID:** ULF-RFCM-FAIL-1
- **Stage:** 5-failed
- **Type:** FALSIFIED FIELD CORE / POSITIVE SURVIVOR EXTRACTED
- **Source:** `../../1-in-progress/universal-law-field/reflection-formation-cocycle-mechanics/field-programme.md`
- **Statement:** The proposal that functional reflection and affine depth formation generate a nontrivial curvature selecting the critical center is false: their defect is always a removable common-center coboundary.

## Failed conjecture

Functional-equation reflection (R(\sigma)=1-\sigma) and raw depth
(D_m(\sigma)=m\sigma) do not commute. It was conjectured that their affine-Weyl commutator might
be the missing selection curvature.

The exact calculation is

\[
 D_mRD_m^{-1}R(\sigma)=\sigma+(m-1).
\]

This translation is independent of (sigma). It does not vanish specifically at
(sigma=1/2), so it cannot select the critical center.

## No-go closure

- **Exact killing theorem/mechanism:** Every strict affine multiplicative formation action has the
  form (F_\lambda(x)=d+\lambda(x-d)) for one common center (d). Its exchange with reflection
  about (c) is translation by (2(\lambda-1)(c-d)). Hence the entire defect is a coboundary and
  vanishes only when the two marked centers coincide.
- **Strongest positive survivor:** Functional reflection uniquely forces the compensated depth
  action
  
  \[
  C_m(\sigma)=\tfrac12+m(\sigma-\tfrac12),
  \]
  
  equivalently the coefficient correction (n^{(m-1)/2}). Any nonzero mismatch exits every
  bounded admission chamber and has unbounded proper work; common recovery preserves that work
  exactly.
- **New insight:** Half-density centering is forced, but it is a compensation law, not an RH
  producer. A viable new field mechanism must carry a genuinely non-coboundary, nonlinear,
  higher-rank, noncommutative, or admission-singular exchange class.
- **Status:** dependency-closed paper theorem in
  `../../2-fully-proven/universal-law-field/reflection-formation-cocycle-mechanics/reflection-depth-center-cocycle-half-density-compensation-and-properness-law.md`; Lean formalization intentionally deferred during current read-only research phase.

## Why common recovery does not save the conjecture

For any parameter-independent Markov recovery kernel (K), split formation satisfies

\[
 D_{\rm KL}(\mu_x\otimes K\Vert\mu_y\otimes K)
 =D_{\rm KL}(\mu_x\Vert\mu_y).
\]

Thus packet lifting transports the translation defect isometrically. Information neutrality does
not turn it into zero work.

## Log

- 2026-08-12 -- conjectured from the newly constructed functional-equation packet lift.
- 2026-08-12 -- falsified by common-center classification; positive half-density/properness
  survivor promoted to Stage 2.
