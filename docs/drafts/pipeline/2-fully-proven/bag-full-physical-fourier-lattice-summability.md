# BAG full physical Fourier lattice summability

- ID: C28.56ag.5, continuation01aa.
- Parent: ../1-in-progress/bag-complete-lattice-fourier-transfer.md.
- Status: dependency-closed paper proof; production leaf and all12 public
  declaration axiom audits passed. See the matching P3 card.
- Scope: actual three-coordinate amplitude, all shifted Fourier lattice
  coefficients and absolute summability at each fixed scale. No Poisson
  identity, uniform growing-scale saving or signed cancellation claimed.

## Statement

Use the actual cutoff eta supported in (N,2N), N>1, and

    f(p)=eta(p)*V(p/N)/log(p),
    A(p,q,r)=2*pi*f(p)*f(q)*conj(f(r))/r *
      W(p*q/(r*N))*e(p*q/r).

Regard A as a function on Euclidean three-space with its standard volume
and Fourier transform. A is Schwartz. For EVERY a in that space,

    sum_(k in Z^3) |hat(A)(k+a)| < infinity.

At every natural triple the coefficient is exactly

    eta(p)*eta(q)*eta(r) * primeGaussianCubicMainEntry(N,p,q,r)
      / (log(p)*log(q)*log(r)).

No physical factor or r-coordinate is dropped. The unconditional family
selects the already-proved sharp/smooth cutoffs and retains their original
o(N/log(N)^2) comparison. That comparison is inherited, not a new saving.

## Dependency-closed proof

1. The previous leaf proves all f_tau smooth, including f=f_0. For r>1,
   divide only by nonzero r; W is the literal ContDiffBump, so A is smooth.
   For r<=1 the r-slice vanishes on the open neighborhood r<N. A is
   identically zero there. Thus no singular reciprocal is differentiated
   at zero. Complex conjugation is real-linear and smooth.

2. If A is nonzero, each f-coordinate is nonzero, hence all three
   coordinates belong to (N,2N). Its support is contained in the compact
   closed cube [N,2N]^3. Smooth compact support gives an actual Schwartz
   element, with no assumed regularity or Fourier decay.

3. For any Schwartz function h on Euclidean three-space the source
   seminorm theorem bounds (1+norm(x))^6*norm(h(x)) by a finite C_h.
   Each coordinate absolute value is at most norm(x), so

       (1+k_1^2)(1+k_2^2)(1+k_3^2)*norm(h(k)) <= C_h.

   Each inverse-square lattice factor is summable: bound its nonzero
   terms by 1/k^2 and include the one zero term separately. The full
   three-coordinate product is summable by the nonnegative product-sum
   theorem. Domination proves absolute sampling of h on ALL Z^3.

4. Translation preserves Schwartz space. Apply step3 to h(x+a), then to
   the Fourier transform of A, which is itself Schwartz. This proves
   the asserted all-shift absolute convergence. It does not exchange a
   Mellin integral with a lattice sum: A is transformed as a whole first.

5. Expand f at natural coordinates. Conjugation fixes the real cutoff
   and real logarithm; multiplication and total field division give the
   literal original coefficient. Select the actual eta_N from the earlier
   sharp/smooth theorem and use A_N above at its eventual good scales,
   zero on irrelevant bad scales. This supplies an unconditional family.

## Remaining mathematical gap

The convergence constant depends on the scale and its full derivative
seminorms. This proof supplies no asymptotic estimate at the BAG target
scale. Multidimensional Poisson matching and literal projected critical
atom assembly remain to be formalized, followed by the hard complete
signed near-cone/transverse-tail bound. Growing moments, moving cofactors,
common-height self-return and RH remain open. BAG is not retired.
