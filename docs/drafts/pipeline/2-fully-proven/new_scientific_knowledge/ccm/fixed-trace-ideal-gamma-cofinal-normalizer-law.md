# Fixed-trace-ideal Gamma cofinal normalizer law

- **Status:** `[PAPER PROOF COMPLETE] [LEAN FORMALIZED] [TARGET BUILD PASSED] [AXIOM AUDITED] [NEW SCIENTIFIC KNOWLEDGE] [NOT RH]`
- **Route:** R / rational-adelic Stokes to fixed physical Xi quotient
- **Target module:**
  `GaloisForLFunctions.RHTower.PrimeFirstTraceGammaCofinalNormalizerFrontier`

## Problem isolated

Let `P` be ordinary primes, `S=P -> C`, and let

```text
I = {a in S : sum_p |a_p| < infinity}.
```

For a real centered grade `t`, the raw Gamma character is

```text
C_t(a)_p = p^(-2t) a_p.
```

The activation-Fisher coefficient is

```text
F_t(p) = p^t p/(p+1)^2.
```

Existing work proves `C_t(F_t)=F_(-t)` and, for `u<1`,

```text
F_u in I  <->  u<0.                                      (1)
```

It also constructs the actual rational-adelic period-one Stokes class and its two physical
landings `c_rho[F_(-t_rho)]` and `c_rho[F_(t_rho)]`.  What was not classified is whether the
literal finite-place Gamma action itself can supply fixed-ideal descent.

## Theorem

Assume `|t|<1`.

1. `C_t(I) subset I` if and only if `0<=t`.
2. `C_(-t)(I) subset I` if and only if `t<=0`.
3. The raw Gamma reflection normalizes the fixed physical ideal in both directions if and only if
   `t=0`.
4. Every Gamma multiplier supported on only finitely many primes induces the identity on `S/I`,
   for every real grade.
5. Every finite-prime truncation of `F_t` represents zero in `S/I`.  The full class satisfies
   `[F_t]!=0` exactly when `0<=t`; hence its physical information is born only at the cofinal
   all-prime boundary.
6. The reflected pair `([F_(-t)],[F_t])` is never the zero pair, but both entries are nonzero
   exactly when `t=0`.  Off center, exactly one orientation is erased.
7. For every actual Xi divisor and every ordinary prime, the retained period-one rational-adelic
   class survives unconditionally in at least one physical Gamma orientation.  Away from the
   critical line exactly one physical orientation erases it.  Two-sided fixed-ideal normalization
   at every Xi divisor is equivalent to RH.
8. The singular cofinal Gamma Bockstein

   ```text
   beta_t = [F_(-t)] - [F_t]
   ```

   is nonzero exactly when `t!=0`, although every finite-prime Gamma Bockstein is zero.
9. For the actual retained rational-adelic period-one class, the difference of its two physical
   Gamma landings is exactly the nonzero leading Xi jet multiplied by `beta_(t_rho)`.  Thus its
   physical orientation defect is nonzero exactly off the critical line.
10. Global annihilation of this explicit source-derived physical Gamma Bockstein is equivalent to
    RH.  This identifies the literal class an arithmetic producer must annihilate; it does not
    assume or prove that annihilation.

Consequently no finite adelic correspondence, finite-prime chain map, or finite-support Gamma
naturality square can prove source-derived global physical non-erasure.  The missing producer must
be an intrinsically cofinal, singular all-prime law which both:

- is invisible at every finite stage; and
- controls the fixed `ell1` ideal rather than a transported variable ideal.

## Proof

Suppose first that `0<=t`.  Every ordinary prime satisfies `p>=2`, so `1<=p`.  Since
`-2t<=0`, monotonicity of real powers gives

```text
0 < p^(-2t) <= 1.
```

For `a in I`, therefore

```text
|C_t(a)_p| = p^(-2t)|a_p| <= |a_p|.
```

Absolute summability is inherited under this pointwise majorant, proving `C_t(I) subset I`.

Conversely suppose `C_t(I) subset I` and `t<0`.  Because `|t|<1`, both `t<1` and `-t<1`.
By (1), `F_t in I`, while `F_(-t) notin I` because `0<-t`.  But

```text
C_t(F_t)=F_(-t),
```

contradicting preservation.  This proves clause 1.  Replacing `t` by `-t` proves clause 2, and
their conjunction is `0<=t` and `t<=0`, hence `t=0`.  At `t=0`, `C_0=id`, proving clause 3.

For clause 4, let `M` equal `C_t` on a finite prime set `K` and the identity elsewhere.  Then
`M(a)-a` is supported on `K`, hence absolutely summable.  Thus `M(a)` and `a` have the same class
in `S/I`; the induced quotient map is the identity.  This uses no bound on `t`.

A finite-prime truncation of `F_t` is finitely supported, so clause 5 follows from the same
argument and (1).  For clause 6, total order gives `0<=t` or `t<=0`; (1) therefore makes at least
one of `[F_t]` and `[F_(-t)]` nonzero.  Both are nonzero exactly when `0<=t` and `t<=0`, namely
`t=0`.

For clauses 8--10, define `beta_t=[F_(-t)]-[F_t]`.  At `t=0` it vanishes.  If `t>0`, then
`[F_(-t)]=0` and `[F_t]!=0`, so `beta_t=-[F_t]!=0`; if `t<0`, the roles reverse and
`beta_t=[F_(-t)]!=0`.  At every finite prime set `K`, clause 4 gives

```text
[C_(t,K)F_t]-[F_t]=0,
```

so `beta_t` is a genuinely cofinal class rather than a compatible finite-stage invariant.  The
two source Stokes landing formulas have the same nonzero leading Xi jet `j_rho` and coefficients
`[F_(-t_rho)]` and `[F_(t_rho)]`; subtracting them gives exactly `j_rho beta_(t_rho)`.  Nonvanishing
of `j_rho` therefore makes this defect zero precisely when `t_rho=0`.  Quantifying over actual Xi
divisors gives the stated RH equivalence.

## Hostile audit

- **Not a proof of RH.** At an actual Xi divisor, clause 3 is equivalent to critical-line
  placement; it cannot be asserted as source functoriality.
- **Finite-place Fourier naturality is nonselective.** Clause 4 proves it is literally the
  identity in the physical quotient for every grade.
- **Resolved Stokes retention is insufficient.** It lives before the singular cofinal quotient
  in clause 5.
- **Unitary `L2` Fourier theory is insufficient.** It preserves the Hilbert carrier, not the fixed
  first-trace `ell1` ideal.  Turning it into a two-sided ideal action would assume clause 3.
- **Generalized-prime falsifier survives.** The raw multiplier and every finite-stage identity
  exist off center; only a genuinely arithmetic all-prime cofinal law can exclude that model.

## External boundary

Hien's rapid-decay/de Rham pairing gives perfectness of an irregular period pairing, and
Mochizuki's wild harmonic theory supplies polarized wild twistor structures.  Neither identifies
an adelic Fourier mate with the same fixed trace ideal.  Connes--Consani--Marcolli construct the
idele-class cyclic action and trace formula, but RH remains the positivity condition on the trace
pairing.  These parent theories therefore support source periods, Fourier symmetry, and cyclic
descent without supplying the cofinal fixed-ideal theorem isolated above.

Primary sources:

- M. Hien, *Periods for irregular singular connections on surfaces*,
  <https://arxiv.org/abs/math/0609439>.
- T. Mochizuki, *Wild Harmonic Bundles and Wild Pure Twistor D-modules*,
  <https://arxiv.org/abs/0803.1344>.
- A. Connes, C. Consani, M. Marcolli, *The Weil proof and the geometry of the adeles class space*,
  <https://arxiv.org/abs/math/0703392>.
