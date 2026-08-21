# Matched CCM wall-light incidence

## Status

Formalized unconditionally in
`GaloisForLFunctions.RHTower.CCMActualHeadMatchedOrientedWallLightIncidence`.
This closes a source-occurrence theorem inside the actual matched CCM carrier; it does not yet
identify the Robin--Gamma--holonomy rectangular trace or prove RH.

## New knowledge

For a prime-power source `n = p^(e+1)`, Lean proves pointwise at every real frequency `xi`

\[
\|\ell_+(2\pi\xi;p,e)\|^2-\|\ell_-(2\pi\xi;p,e)\|^2
=w_n\sin(2\pi\log(n)\xi),
\]

where `w_n` is the literal critical Mellin/von-Mangoldt mass and `ell_±` are the corpus-forced
Suzuki light amplitudes.  No division by `w_n`, wall amplitude, height, or source coordinate is
used.

Combining this with the oriented matched characteristic cocycle gives the incidence symbol

\[
w_n\cos(2\pi\log(n)\xi)C_n(\xi)
+(\|\ell_+\|^2-\|\ell_-\|^2)S_n(\xi)
=w_n\operatorname{Re}\Phi_n(\xi).
\]

Therefore critical mass times one actual matched prime--polar cell is exactly the spectral
integral of an even rebate channel plus the literal positive-light-minus-negative-light channel.
The theorem also assembles over every finite prime-power packet.

Lean further proves the exact positive survivor

\[
\|\ell_-\|^2=\frac{w_n-(\|\ell_+\|^2-\|\ell_-\|^2)}{2}.
\]

Thus negative light has two irreducible coordinates: half critical mass as center reserve and
minus half oriented imbalance.  At spectral center the matched incidence symbol is zero, while
negative-light energy is strictly positive at every prime-power wall.  Consequently matched
incidence alone cannot pointwise dominate raw negative light; the corpus now contains a closed
no-go theorem for that attempted shortcut.

## Consequence for the frontier

The missing negative-light occurrence is not absent from the actual CCM carrier.  It appears
coefficient-faithfully as one coordinate of a complex two-channel incidence law.  Scalar/even
compression hides it, and attempting to isolate negative light before retaining the positive
partner changes the exact source identity.

Remaining task is narrower: transport this finite-packet incidence through the actual
Robin--Gamma--holonomy rectangular trace and prove the resulting Schur residual is uniformly
lower-semi-bounded.  Completion must source both center reserve and oriented sine coordinate;
failure to preserve either is now a formal no-go criterion.

## Lean audit

- direct leaf check: passed;
- exact module build: passed;
- umbrella import: wired, not built;
- capstone axiom audit: only `propext`, `Classical.choice`, and `Quot.sound`.
