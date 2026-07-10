# Fitting vanishing vs one-sided and combined fakeness (corrected)

- **ID:** fitting-fake-gap
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) — `[PROVED HERE]`, elementary presentation algebra
- **Novelty grade:** **not dual-gate new knowledge** — standard adjugate/Fitting first-variation algebra on a fixed \(2\times 2\) presentation; useful as a corrected dictionary, not a literature-absent bridge.
- **Statement (delivered):** For `A = standardPres m = [[X^m,1],[0,1]]` and `Δ = [[a,b],[c,d]]` over `ℚ[X]`:
  1. Fitting vanishes ⇔ `X^m ∣ (a−c)`.
  2. Right-fake ⇔ `X^m ∣ (a−c)` and `X^m ∣ (b−d)`.
  3. Left-fake ⇔ `X^m ∣ a` and `X^m ∣ c`.
  4. **Combined-fake** (`Δ = A Hᵣ + Hₗ A + X^m K`) ⇔ Fitting vanishes (`FittingZero_iff_combinedFake`).
  5. Witness `[[1,0],[1,1]]`: Fitting zero, not left-fake, not right-fake, **is** combined-fake (explicit sum of one left and one right term).

## Corrected wording (after external review)

> Fitting vanishing does **not** imply either left-fakeness or right-fakeness **separately**.  
> However, for this presentation it is **equivalent** to lying in the sum of the left and right fake modules modulo `(X^m)`.

Calling the gap “bilateral non-fake” was **misleading**: the standard bilateral/combined tangent sense is left-**plus**-right, under which the witness **is** fake.

## Dual gate
- **NOVEL:** fails (elementary / reduce-to-known presentation algebra).
- **SIGNIFICANT (local):** yes as a **correction** of the program’s fake dictionary (one-sided vs combined); not as a new mathematical branch object.

## Lean
- `RHTower/FittingFakeGap.lean`
- Capstones: `FittingZero_iff_combinedFake`, `fitting_zero_not_imp_one_sided_fake`, `fitting_vs_fake_summary`
- Witness certs: `oneSidedGapWitness_*` (aliases `bilateralWitness_*` retained for driver compatibility)

## Log
- 2026-07-08 — right-only and “bilateral non-fake” overclaims corrected; equivalence to combined fakeness formalized.
