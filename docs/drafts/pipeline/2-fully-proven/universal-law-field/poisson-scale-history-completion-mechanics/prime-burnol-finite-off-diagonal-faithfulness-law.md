# Prime Burnol finite off-diagonal faithfulness law

- **ID:** ULF-PBFOF-001
- **Stage:** 2-fully-proven
- **Type:** unconditional pre-divisor source-kernel theorem
- **Parents:** ULF-PBFMS-001
- **Status:** [PAPER-PROVED] [LEAN-PROVED] [NOT RH]
- **Lean:** formal/GaloisForLFunctions/RHTower/PrimeBurnolFiniteOffDiagonalFaithfulness.lean

## 1. Big-picture meaning

ULF-PBFMS-001 proved finite Burnol packets invertible but did not exclude a vanishing individual
cross-prime edge. The source--theta holonomy needs those edges: diagonal or same-prime data cannot
compare different archimedean rapidities. The literal half-line integral gives every Gram entry
explicitly and proves none vanish.

This is source formation, not positivity selection. It says multiplicative Euler formation is a
complete weighted graph before completion acts.

## 2. Exact theorem

For primitive cells `u,v`, clocks `kappa,nu`, put

~~~text
lambda_u=log(p_u^(e_u+1)),
A_u=sqrt(log(p_u)/p_u^(e_u+1)),
c_(u,v)=lambda_u+lambda_v+i(nu-kappa).
~~~

The literal Burnol columns are

~~~text
f_(u,kappa)(L)=A_u L exp(-(lambda_u+i kappa)L),  L>0.
~~~

Since `Re c_(u,v)>0`, the complex monomial Laplace identity gives

~~~text
<f_(u,kappa),f_(v,nu)>
  =A_u A_v integral_0^infinity L^2 exp(-c_(u,v)L)dL
  =A_u A_v 2/c_(u,v)^3.                                (PBFOF.1)
~~~

Both amplitudes are nonzero and `c_(u,v)` has positive real part, hence

~~~text
(C_F)_(ij) != 0                                        (PBFOF.2)
~~~

for every pair of labels in every finite packet, including off-diagonal and cross-prime pairs.

## 3. Consequence and limit

Combining (PBFOF.2) with ULF-SFMH-001's fusion identity shows that any packet containing two
distinct primes has nontrivial source--theta holonomy for every nonneutral grade. This removes the
last finite nontriviality premise.

The theorem does not form a cofinal relative class, produce an integer, or compare its cubic value
with the global strict sub-unit Burnol budget. Those remain the completion boundary problem.
