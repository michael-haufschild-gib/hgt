# The even-product field and the lifting of reflection

- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** `docs/reports/review-1011/fable.md`, §§10.5(1–3), 10.6.

## Objects and target

Let `A={ρ−1/2 : ξ(ρ)=0}`, `L=ℚ(A)` and
`K=ℚ(ab : a,b∈A)`, as actual subfields of ℂ. These use the entire divisor.
Fix any `a₀∈A`; it is nonzero.

Prove `L=K(a₀)` and `[L:K]≤2`. Classify when the functional-equation
permutation `a↦−a` extends to a field automorphism: exactly when `a₀∉K`.
The extension, when it exists, must be unique and have fixed field `K`.

## Mechanism

Every `a∈A` equals `(aa₀)/a₀`, with `aa₀,a₀²∈K`. Hence one quadratic
generator contains all centered zeros. If `a₀∉K`, quadratic conjugation
sends every generator to its negative. Conversely such an automorphism fixes
all even products and moves `a₀`, so `a₀∉K`.

Complex conjugation preserves both fields. Using an unconditionally existing
critical-line zero as anchor, `K⊆ℝ` is equivalent to all centered zeros being
purely imaginary. Thus reality of the even-product field is an arithmetic
target, not an assumption available from the functional equation.

## Required distinction

`K` is defined from zeros, not yet from prime-side data. This construction
classifies the obstruction to lifting a permutation; it does not manufacture
the missing arithmetic ground field or prove RH. An actual prime-side
description, or a relation forcing/refuting `a₀∈K`, remains necessary.

## Obligations

Exact intermediate-field equality; degree and automorphism classification;
conjugation invariance; specialization to all ξ zeros with no unproved
premises; transitive Lean axiom audit.
