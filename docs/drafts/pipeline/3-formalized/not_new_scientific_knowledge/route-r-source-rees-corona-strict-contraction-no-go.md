# Route-R source Rees--corona strict-contraction no-go

- **ID:** `route-r-source-rees-corona-strict-contraction-no-go`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / NON-NOVEL INFRASTRUCTURE
- **Source:** `../../1-in-progress/source-poisson-rees-even-odd-energy.md`
- **Statement:** Every adjacent-depth rational-adelic Rees--corona edge attenuates a centered
  strip grade by a factor in `(0,1)`; nonzero off-critical grades are therefore nonzero strict
  contractions, while annihilation is equivalent to zero grade.

## Theorem

For every prime `p`, set

\[
 \kappa_p=\frac{(1-p^{-1})(2-p^{-1})}{2\log p}.
\]

The exact adjacent-depth corona weight is

\[
 w_p(a)=a\kappa_p,qquad 0<\kappa_p<1.                         \tag{1}
\]

Consequently, for every real `a` with `|a|<=1`,

\[
 |w_p(a)|<1,
\]

and

\[
 w_p(a)=0\iff a=0.                                             \tag{2}
\]

In particular every nonzero strip grade gives a nonzero strict contraction.  Local Schur
contractivity cannot distinguish critical from off-critical centered rates.

## Paper proof

Put `q=p^{-1}`.  The adjacent Wold masses and Gamma clocks are

\[
 m_0=1-q,\quad m_1=(1-q)q,\quad \lambda_0=\log p,\quad
 \lambda_1=2\log p.
\]

Substitution into

\[
 w_p(a)=a\frac{m_0\lambda_1-m_1\lambda_0}{\lambda_0\lambda_1}
\]

gives `(1)`.  Since `p>1`, `0<q<1`, so `kappa_p>0`.  Also
`log p>=1-p^{-1}` and `2-q<2`, hence

\[
 (1-q)(2-q)<2(1-q)\le2\log p.
\]

Division by the positive denominator proves `kappa_p<1`.  The contraction bound follows from
`|w_p(a)|=|a|kappa_p`; positivity of `kappa_p` proves `(2)`.

## Lean certificate

Module:
`GaloisForLFunctions.RHTower.PrimeDepthBVWoldReesCoronaContractionNoGo`.

Declarations:

- `primeDepthBVWoldReesCoronaWeight_adjacent_eq`;
- `primeDepthBVWoldReesCoronaAdjacentAttenuation_pos`;
- `primeDepthBVWoldReesCoronaAdjacentAttenuation_lt_one`;
- `primeDepthBVWoldReesCoronaAdjacentAttenuation_mem_Ioo`;
- `abs_primeDepthBVWoldReesCoronaWeight_adjacent_lt_one`;
- `primeDepthBVWoldReesCoronaWeight_adjacent_eq_zero_iff`;
- `primeDepthBVWoldReesCorona_strictContraction_nonzero_of_strip`.

Verification:

- `lake env lean GaloisForLFunctions/RHTower/PrimeDepthBVWoldReesCoronaContractionNoGo.lean`:
  PASS;
- `lake build GaloisForLFunctions.RHTower.PrimeDepthBVWoldReesCoronaContractionNoGo`: PASS;
- `scripts/formal_tools.py lint`: PASS;
- axiom audit: only `propext`, `Classical.choice`, and `Quot.sound`.

The module is wired into `GaloisForLFunctions.RHTower`.

## Research consequence

This theorem is not the requested even-over-odd energy theorem.  It eliminates a tempting weaker
replacement.  Any successful source theorem must prove global singular annihilation or a positive
pre-completion Hodge identity; local contractivity is automatic throughout the strip.

## Log

- 2026-08-04 -- Paper proof completed, formalized unconditionally, leaf source check and module
  build passed, standard-axiom audit passed, and RHTower umbrella wiring added.
