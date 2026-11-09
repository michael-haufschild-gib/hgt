# Polynomial syzygy width bounds exact order

- **ID:** alst-syzygy-width-bounds-order
- **Stage:** 0-backlog
- **Type:** CONJECTURE
- **Statement:** If `h=Σ_{i<m} f_i ψ_q(g_i)` is nonzero and all global mixed first-factor Euler moments below order `r` vanish, then `r<m`. For `q≥2` and a nonempty variable set, `m=r+1` is attained by the binomial paired polynomial `(V_p−U_p)^r`.

## Mathematical purpose
Price exact Stepanov multiplicity in the number of paired summands, as well
as arithmetic length. A bound independent of polynomial degree would expose
an additional obstruction to producing high order from a short family.

## Route to audit
Translate the syzygies into diagonal multiplicity of the paired polynomial.
Its separated-variable rank is at most `m`. A generalized Wronskian argument
should show that a nonzero tensor of rank `m` cannot vanish to diagonal
order `m`: derivatives below that order must detect a full independent
family over the constant field. Dependent first factors must be reduced
before applying this argument. All Wronskian and constant-field inputs
require proofs; none is an allowed extra premise.

The initial corpus search for diagonal multiplicity and separated-variable
rank found no matching bound. Novelty, the general multivariable statement,
sharpness, and Lean formalization remain open. Nothing is counted.
