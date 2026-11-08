# Integer support makes integrable FE defects rigid

- **ID:** exact-event-integer-support-fe-rigidity
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** review-0811/obstacles-summary.md §2.5, §2.10; B84, B103
- **Statement:** In the Hamburger strip class, a nonempty countable Beurling system with integer norms and integrable uncompleted Riemann FE defect has exactly the rational primes, with no restriction on defect size or pole residue.

## Mathematical content

Existing rigidity requires either residue at most one or defect norm at most 1/6400.
Integer support removes both restrictions. This is a classification of infinite Euler
products, not an exclusion of zeros of ζ. Noninteger Beurling systems remain outside it.

Let the distinct integer norms be 1 = λ₀ < λ₁ < … with multiplicities Aₙ.
The unit norm has A₀ = 1. Put
C_y(ε) = ε Σₙ Aₙ exp(−2πλₙε) cos(2πλₙy).
Integer support gives C₁ = C₀ identically. The existing defective Mellin–Laplace identity
and vanishing radial residues of an L¹ defect give C₀ → β/π and C₁ → 1/(2π).
Thus β = 1/2, and the existing unit-density rigidity identifies the entire spectrum and
its multiplicative generators. Every analytic regularity assumption is displayed in the
theorem; no FE regularity is claimed for the known one-offs.

## Proof and novelty gates

- [x] Corpus audit: unit-density rigidity, small-defect rigidity, ordered Beurling norms.
- [x] Dependency-closed paper argument above.
- [x] Exact Lean statement and direct module check.
- [x] Transitive axiom audit: only `propext`, `Classical.choice`, `Quot.sound`.
- [x] Nonclassical integer-supported systems cannot satisfy all displayed strip and integrability conditions. No conclusion about zeros of ζ follows.

## Lean

`ExactEventTheory/IntegerSupportForcesExactArithmetic.lean`:

- `integer_support_pins_pole_residue`
- `integer_spectrum_of_integer_support_integrable_defect`
- `beurlingSystem_rigidity_of_integer_support_integrable_defect`

Final audit: `lake --old env lean GaloisForLFunctions/ExactEventTheory/IntegerSupportForcesExactArithmetic.lean`.
Programme umbrella and `MainTheorems.lean` imports added; no umbrella build.

External search found classical Hamburger converse theorems, not this L¹-defect extension;
absence from search is not a literature-priority claim.

## Scope of the defect

The metric in B84 is the L¹ norm of the **uncompleted** defect. Gamma damping of a
subexponentially growing Mellin correction does not establish its finiteness. Prime-power
discrepancy control alone has not resolved that analytic input.
