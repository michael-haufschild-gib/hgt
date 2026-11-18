# Effective sections at separated conductors

For an effective divisor $a$, put $M=\sum_d a_d$ and $P=(\sum_d a_d/\sqrt d)(\sum_d a_d\sqrt d)$. There are absolute $c,C>0$ and $R$ such that $M\ge R$ gives $\operatorname{radius}(a)-\log d(a)\ge cP-CM^4$. In particular the prescribed divisor $m(e_1+e_p)$ admits a nonzero section at its original radius whenever $m$ is sufficiently large and $p\ge C' m^4$.

## Proof

On a mesh of denominator $r$, translating the unit atom by $\log d$ gives its samples on the mesh of denominator $rd$. Its exponential weight acquires the factor $d^t$. The original integration window contains the whole translated support. The tilted unit atom is compactly supported and Lipschitz. The harmonic quadrature estimate gives an error at most $C_t/(rd)$ from its strictly positive integral $I_t$. Thus the signed sampled moment differs from $I_t\sum_d a_d d^t$ by at most $(C_t/r)\sum_d |a_d|d^{t-1}$. At the original resolution $r=\sum_d|a_d|$, both pole readings have bounded additive error for every signed divisor. When the positive pole degree vanishes, the entire sampled pole correction is $O(r)$. For effective divisors the product of the two sampled pole moments is at least a positive constant times $P$.

The discrete Lévy identity bounds the regularized jet pairing from above by the supremum of its finite diagonal parts times the sampled square mass. The diagonal parts converge, and twice the square mass is precisely the contact multiplicity at lag one. The contact-size theorem bounds it by $CM^2$ uniformly. The rounded ordinary-prime product costs at most $CM^4$, and the remaining prime powers cost at most $CM^2$. Subtraction gives the claimed bound. For the prime pair, $M=2m$ and $P=m^2(1+p^{-1/2})(1+p^{1/2})$.

## Lean

[ConductorUniformPoleQuadrature.lean](../../../../formal/GaloisForLFunctions/CountingHolography/Sections/ConductorUniformPoleQuadrature.lean) proves `conductor_moment_quadrature_error`. [EffectiveSectionsAtSeparatedConductors.lean](../../../../formal/GaloisForLFunctions/CountingHolography/Sections/EffectiveSectionsAtSeparatedConductors.lean) proves `bounded_actual_pole_reading_error`, `pole_balanced_linear_error`, `uniform_finite_jet_debit`, `effective_divisor_degree_lower` and `all_separated_primePair_moduli_fit`.
