# Route K completed-endpoint RVM relocation

- **Stage:** 3-formalized
- **Status:** dependency-closed unconditional Lean
- **Scope:** operator existence, trace ideals, cofinal holonomy, first reflection-even signal,
  exact degree-two source incidence with unchanged RVM tail
- **Not claimed:** centered-Xi determinant identity or RH

## New theorem package

Let `t_n` be smooth Riemann--von Mangoldt quantiles, `q_n=t_n⁻¹`, and let `Q` be the
marked-prime diagonal with entries `q_n`. Let

```text
K_phys(t)=S(1+it)-2S(2+it)+Delta_val(t),
B(p,q)=(log p/p)(log q/q)
  Re((K_phys(log p-log q)+K_phys(log q-log p))/2).
```

Then:

1. `Q` is positive, injective, self-adjoint, and Hilbert--Schmidt.
2. `B` is a source-defined self-adjoint Hilbert--Schmidt operator.
3. `K_RVM=[Q,[Q,B]]` is self-adjoint and Schatten-1, with exact matrix
   `(q_p-q_q)^2 B(p,q)`.
4. Beyond every prime index, `K_RVM` has a nonzero triangle holonomy.
5. Those cofinal triangles give nonzero centered-reflection quartic edge-flip signal.
6. `K_RVM` has zero diagonal and is Hilbert--Schmidt-orthogonal to `Q`, so
   `||Q+K_RVM||_HS²=||Q||_HS²+||K_RVM||_HS²>||Q||_HS²`.
7. If `M_0^src` is the zeroth normalized completed prime--Gamma moment, a finite prime set `F`
   and unique positive `c_F` exist such that

   ```text
   A_F=c_F(Q_F+K_RVM)+Q_(F^c),
   2||A_F||_HS²=M_0^src.
   ```

   The diagonal of `A_F` is exactly the original reciprocal smooth-RVM skeleton outside `F`.
8. Every off-diagonal edge is multiplied by `c_F`, so cofinal nonzero triangle holonomy and the
   reflection-even quartic edge-flip signal survive exact quadratic normalization.
9. If `M_1^src` is the next source moment, then

   ```text
   0 < M_1^src < (M_0^src)²/2.
   ```

   Thus the source pair lies strictly inside the necessary reflected self-adjoint two-moment
   purity cone; quartic matching has no scalar sign/size obstruction.

The cofinal result needs no PNT. If every late two-gap block contained a fixed positive log gap,
even block endpoints would grow geometrically; both parity subsequences of reciprocal primes
would be summable, contradicting Euler divergence. Local source stiffness and continuity then
turn the resulting three-prime log clusters into positive completed-endpoint triangles.

## Lean certificate

```text
formal/GaloisForLFunctions/RHTower/PrimeLogTripleCluster.lean
formal/GaloisForLFunctions/RHTower/XiPrimeMarkedPhysicalEndpointCofinalHolonomy.lean
formal/GaloisForLFunctions/RHTower/XiPrimeMarkedPhysicalEndpointRVMRelocation.lean
formal/GaloisForLFunctions/RHTower/XiPrimeMarkedPhysicalEndpointRVMQuadraticIncidence.lean
formal/GaloisForLFunctions/RHTower/SchattenDoubleCommutatorRelocation.lean
```

## Superseded frontier

Exact quartic source incidence is now solved by a finite-head/cofinite-reserve construction that
preserves the exact reciprocal RVM tail and cofinal source holonomy.  The all-order Hilbert--Schmidt
Gram factorization proves that every complete reflected incidence carrier canonically lands in
Route P's compact positive Markov endpoint before determinant formation.  Route K is therefore
retired as an independent RH route; its exact quartic construction remains the positive survivor.

Closure certificate:
`route-k-exact-quartic-incidence-all-order-factorization.md`.
