# TG C9.11l — source-preserving Fredholm Euler transition system

- **Stage:** 5-failed
- **Status:** stated Fredholm-transition mechanism refuted; route TG remains active
- **Positive survivor:** dependency-closed paper proof and Lean formalization complete

## Refuted mechanism

The finite actual Euler boundary quotient is a Banach-space isomorphism.
Conjecture: its source-preserving transitions could become Fredholm after
discarding finitely many initial prime stages, furnishing the missing cofinal
index carrier.

The original source maps force a unique transition τ_(S,T). Its exact kernel
is boundedly equivalent, through the original source chart, to the Fourier
shell `(max(b,P_S),P_T)`. Every nondegenerate such shell is infinite dimensional.
For every starting S and positive b there is T⊇S with P_T>max(b,P_S), hence a
non-Fredholm transition. A finite initial deletion cannot repair this system.

## Strongest positive survivor

The entire transition system is identified with actual Fourier restriction in
the source-defined charts Φ_S, including surjectivity and composition:
`Φ_S τ_(S,T)=R_(P_S) Φ_T`, `Φ_S(B_S f)=R_(P_S)f`.
The exact kernel equivalence retains the complete lost shell, not only a
dimension obstruction. The original return remains
`J_S f=−A_S* τ_(S,T)(B_T f)` for b≥1. This specifies the missing infinite
boundary grade that any viable relative construction must carry.

Paper proof and Lean proof: complete in
P3:tg-euler-cofinal-boundary-transitions. Four final leaves pass; all 29 public
axiom queries contain only the standard three logical axioms. No cofinal
prime–Gamma class, Hardy cubic identification or sub-unit law follows.

The proper-mode continuation is proved in P3:tg-unsquared-relative-source-assembly; do not replace this
source system by arbitrary annular isometries or erase its current return.
