# The complete conductor Green operator

For $c>0$, define on $\ell^2(\mathbb N_{\ge1})$
\[
G_c e_m=E_m(c)^{-1}e_m.
\]
The completed pole energy is positive and minimal, so
$\|G_c\|=E_1(c)^{-1}$, attained by the pole coordinate.
The logarithmic conductor lower bound makes $E_m(c)^{-1}\to0$;
finite-coordinate truncations therefore approximate $G_c$ in operator norm.
The operator is compact and injective.

The critical heat divergence gives
\[
\sum_{m\ge1}E_m(c)^{-k}=\infty\qquad(k\in\mathbb N).
\]
Indeed $e^{-E}\le k!E^{-k}$ for $E>0$. Compactness therefore coexists with
nonsummability of every positive integer power of the coordinate eigenvalues.

The actual complete-Weil inverse converges to this diagonal form on each fixed
finite Ramanujan packet. This finite-packet identification does not assert
operator-norm convergence between the changing horizon spaces.

Lean: `CompletedArithmeticForms/ConductorGreenCompletion.lean`,
`norm_tiltedConductorGreen`, `isCompactOperator_tiltedConductorGreen`,
`tiltedConductorGreen_injective`,
`not_summable_tiltedConductorGreen_coordinate_power`.
