# Dyadic relative-reflection integral-frame rigidity

- **ID:** `ULF-DRRIF-1`
- **Stage:** 3-formalized
- **Type:** unconditional integral-monodromy rigidity law
- **Status:** dependency-closed paper proof; Lean-certified in
  `GaloisForLFunctions.RHTower.DyadicRelativeReflectionIntegralFrameRigidity`

## Statement

Let

`R=[[0,1],[1,0]]`,

`R_u=[[0,exp(u)],[exp(-u),0]]`,

and `C_u=R_u-R`. For `|a|<1`, suppose there are `B in GL_2(C)` and `A in M_2(Z)` such that

`C_(a log 2) B = B A`.

Then `a=0`. Conversely, at `a=0` the identity basis and zero integer matrix give such a frame.
Hence the dyadic relative reflection admits a rank-two integral frame iff grade is zero.

For every Xi support point, existence of this frame is equivalent to critical-line placement;
existence at every support point is equivalent to RH.

## Proof

The intertwining identity makes `C_(a log 2)` conjugate to `A`, so

`det C_(a log 2)=det A in Z`.

The exact relative-reflection determinant law gives

`det C_u=2(cosh u-1)`.

If `|a|<1`, strict monotonicity of `cosh` in absolute value gives

`0<=det C_(a log 2)<2(cosh(log 2)-1)=1/2`.

The only integer in `[0,1/2)` is zero. Thus `cosh(a log 2)=1`, hence `a log 2=0`, and `a=0`.
At zero, `R_0=R`, so `C_0=0` and the converse is immediate.

For Xi, `a=2 Re(rho)-1` lies in `(-1,1)`, and `a=0` is exactly `Re(rho)=1/2`.

## Sharp boundary

1. A complex change of basis alone gives no integrality; integer coordinates are load-bearing.
2. Integral determinant alone is sufficient, but the frame statement identifies the source object
   that can produce it.
3. Prime two is aperture-optimal: its full strip determinant stays below one. Larger primes cross
   integer determinant values before the strip boundary.
4. No common lattice across primes or powers is needed.

## Dependency audit

- Exact corpus identity `C_u=R_u-R` and `det C_u=2(cosh u-1)`.
- Determinant invariance under conjugation and determinant of an integer matrix.
- Elementary `cosh(log 2)=5/4` and Xi open-strip theorem.
- No RH, positivity, numerical computation, added axiom, or assumed source realization.
