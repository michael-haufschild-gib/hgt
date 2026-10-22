# Retracted Suzuki scalar jump-Herglotz phase no-go

- **ID:** `suzuki-scalar-jump-herglotz-phase-no-go`
- **Stage:** 5-failed
- **Type:** RETRACTED SOURCE-CONVENTION CLAIM / MIXED-COORDINATE NO-GO
- **Scientific status:** `[RETRACTED 2026-07-22] [MIXED ALGEBRA FORMALIZED] [NOT RH]`
- **Failed claim:** source quadrature makes the scalar Euler--Gamma jump colligation impossible
- **Positive survivor:**
  `../3-formalized/new_scientific_knowledge/suzuki-one-sided-coordinate-phase-normalization.md`
- **RH used:** no
- **Computation used:** no
- **Primary sources:** M. Suzuki,
  [*Weil's quadratic form via the screw function*](https://arxiv.org/abs/2606.09096),
  Theorem 1.5 and Sections 6, 8.3; M. Suzuki,
  [*Aspects of the screw function corresponding to the Riemann zeta function*](https://arxiv.org/abs/2206.03682),
  Theorem 1.1(1).

## Retraction and exact error

This card's conclusion is false for Suzuki's physical sheet.  It combined the centered Xi
multiplier `G_0=XiC'/(z^2 XiC)` with an unrephased physical triangle `T_phys`.  Suzuki's 2023
one-sided identity and the centered Xi chain rule instead give the physical multiplier `iG_0`.
For real form shift `lambda`, the exact physical and canonically normalized sheets are

```text
E_phys=iG_eta W-T_phys,
(-i)E_phys=G_eta W-(-iT_phys),
eta=-i lambda/2.                                       (R1)
```

Factor `1/2` is forced by the positive-half-line transform of `r_0(t)=-|t|/2`:

```text
int_0^infinity (-t/2)e^(izt)dt=1/(2z^2).               (R2)
```

Thus interval input in existing `G_eta W-I` pole algebra is `I=-iT_phys`, not `T_phys`.  Actual
source quadrature still gives `W_lambda'(0) in R` and `T_phys,lambda(0) in iR`, but `(R1)` makes
the normalized triangle value real.  If `Phi_phys` is physical affine flux, then

```text
Phi_norm=-i Phi_phys,
Re Phi_norm=Im Phi_phys,                                (R3)
```

which is not forced to vanish.  No contradiction with the Herglotz residue threshold follows.
Scalar jump-Pick conjecture is reopened.  Centered Euler observable below remains a valid
alternative RH detector, but it is not forced by a scalar phase no-go.

## Retired argument (kept as failure ledger)

For two real admissible form shifts `lambda_alpha != lambda_beta`, the corpus constructs the
phase-one characteristics `W_alpha,W_beta`, physical right triangles `R_alpha,R_beta`, centered
parameters

```text
eta_lambda=-i lambda,
```

and the scalar sheet-jump quotient `m_ext=-C_odd/P`.  Its central residue is already known:

```text
Res_0 m_ext
 =-XiC''(0)/XiC(0)+Phi_(alpha,beta),                    (1)

Phi_(alpha,beta)
 =[eta_beta W_beta'(0)R_alpha(0)
   -eta_alpha W_alpha'(0)R_beta(0)]
  /[(eta_beta-eta_alpha)W_alpha'(0)W_beta'(0)].         (2)
```

Since `XiC''(0)/XiC(0)<0`, any Herglotz realization needs

```text
Re Phi_(alpha,beta)<0.                                  (3)
```

The proposed source programme was to prove `(3)` and then the full positive jump Gram law from
the Euler--Gamma source.  Source reality makes `(3)` impossible.

## Theorem A: actual source phases are in exact quadrature

Fix a real shift `lambda<lambda_a`.  The restricted Weil operator and its resolvent commute with
complex conjugation.  The uniquely normalized deficiency solutions of

```text
(A_a-lambda I)v_+=e^x,
(A_a-lambda I)v_-=e^(-x)
```

may therefore be taken real, with `v_-(x)=v_+(-x)`.  Suzuki's phase-one characteristic is

```text
W_lambda(z)
 =(z-i) F_+(z)+(z+i)F_-(z),
F_-(z)=F_+(-z).                                         (4)
```

For real `x`, reality of `v_+` gives `F_+(-x)=conj(F_+(x))`; the two terms in `(4)` are complex
conjugates.  Hence `W_lambda(x)` is real.  Source reflection makes it odd, so

```text
W_lambda'(0) in R.                                      (5)
```

With zero extensions understood distributionally, the compact source whose Fourier transform is
`W_lambda` is

```text
u_lambda
 =i(v_+'-v_+ + v_-'+v_-).                              (6)
```

The bracket in `(6)` is a real odd distribution.  The shifted convolution kernel
`g-lambda r_0` is real.  Its physical right Volterra triangle at spectral value zero is therefore
purely imaginary:

```text
R_lambda(0) in iR.                                      (7)
```

Endpoint atoms caused by zero extension remain real before the common factor `i`, so they do not
alter `(7)`.  The statement also follows by smooth-core approximation in the source Hilbert
space.

## Theorem B: sewn central flux has zero real part

Write

```text
W_alpha'(0)=a,       W_beta'(0)=b,        a,b in R,
R_alpha(0)=i r_alpha, R_beta(0)=i r_beta, r_alpha,r_beta in R,
eta_alpha=-i lambda_alpha,
eta_beta =-i lambda_beta.                               (8)
```

In `(2)`, numerator is real: each term contains two purely imaginary factors.  Denominator is
purely imaginary: it contains exactly one purely imaginary factor.  Division therefore gives

```text
Phi_(alpha,beta) in iR,
Re Phi_(alpha,beta)=0.                                  (9)
```

This is invariant under a common nonzero normalization of each source channel, because both
`R_lambda(0)` and `W_lambda'(0)` acquire the same factor.

There is an independent structural check.  The corpus proves that `(2)` is the value at target
shift zero of the affine interpolant of the normalized one-source jets
`R_lambda(0)/W_lambda'(0)`.  The direct inverse-Neumann contribution is linear in the shift and
therefore cancels from this intercept.  It cannot supply the missing negative real part.

## Invalid corollary for the actual sheet

Combining `(1)`, `(9)`, and the unconditional theta-cusp curvature law gives

```text
Re Res_0 m_ext
 =-XiC''(0)/XiC(0)
 >0.                                                     (10)
```

A Herglotz function has nonpositive real residue at every real pole.  Thus `(10)` proves only:

> The mixed expression `G_eta W-T_phys` cannot produce a Herglotz quotient.

This does not address the physical sheet `iG_eta W-T_phys` or its normalized form `(R1)`.
Consequently it does not falsify scalar jump Gram conjecture `(S31.12)`.

## Additional positive survivor: centered Euler seam observable

Independently of whether Herglotz route succeeds, mandatory boundary pole at fixed point `z=0`
is irrelevant to nonreal Xi detection.  Define

```text
E[f](z)=z f'(z)-f(z),
J[f](z)=z E[f](z).                                      (11)
```

`J` has exactly the three properties required by the source weld:

1. **Endpoint escape invariance.** `J[f+c z]=J[f]`.
2. **Central desingularization.** If `ord_0(f)=n<0`, then
   `ord_0(E[f])=n` and `ord_0(J[f])=n+1`.  In particular the mandatory simple central pole of
   `m_ext` becomes analytic under `J`.
3. **Nonzero Xi amplification.** At `z_0!=0`, multiplication by `z` is an analytic unit.  Hence
   `ord_(z_0)(J[f])=ord_(z_0)(E[f])=ord_(z_0)(f)-1`.  A hypothetical nonreal Xi zero still gives
   an exact double pole.

An alternative corrected source target is:

> Construct from the prime-power/Gamma half-line source a function `D_src`, analytic on the upper
> half-plane, whose germ at one unconditional high point equals `J[m_ext]`.

Because `z` never vanishes in the upper half-plane, `D_src/z` is analytic there and has germ
`E[m_ext]`.  The existing meromorphic germ-weld theorem then proves RH.  Center multiplication
removes exactly the newly discovered false boundary obstruction without weakening detection of a
single nonreal Xi zero.

## Postmortem

1. **Missed multiplier phase.** Independent source gauges cannot repair relative `i` between
   centered and physical multipliers; whole exterior equation must be rephased.
2. **Wrong physical identification.** Reality and reflection prove physical quadrature, but
   equations `(2)` and `(9)` used interval input incompatible with physical convolution.
3. **No RH input.** Curvature sign in `(10)` is unconditional; no statement about Xi-zero
   location is used.
4. **No endpoint regularity shortcut.** Distributional endpoint atoms respect the same real/
   imaginary phase split.
5. **No loss of RH information.** The only extra zero introduced by `J=zE` is at the boundary
   center.  Every nonreal Xi zero is nonzero and retains the exact double-pole obstruction.
6. **Orbit-insertion falsifier retained.** Valid jump positivity or `D_src` must still fail for a
   functional-equation--Schwarz orbit-inserted countermodel; abstract finite characteristic data
   cannot produce the analytic seam.

## Novelty audit

Internal search found the central residue split, affine-intercept law, and Neumann linear-channel
cancellation, but no source-quadrature theorem `(9)`, no contradiction `(10)`, and no centered
Euler survivor `(11)`.  Suzuki's 2023 and 2026 papers supply the real source and one-sided
transform formulas but do not formulate this two-shift exterior quotient or its central phase
obstruction.  Generic Herglotz residue signs and Euler homogeneity are classical.  Candidate
novelty is the Suzuki-specific phase incompatibility and exact replacement observable.  External
priority remains unverified.

## Gates

- [x] mixed-coordinate phase-quadrature algebra isolated
- [x] missed source multiplier phase and half-Neumann factor identified
- [x] scalar Herglotz/jump-Gram falsification retracted
- [x] strongest positive survivor extracted with dependency-closed paper proof
- [x] formalize mixed-coordinate falsifier and centered Euler survivor in Lean
- [ ] formalize canonical physical-to-Weyl phase connector
- [ ] construct analytic prime--Gamma germ for `J[m_ext]`
- [ ] RH

Lean module:
`formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiCarlemanJumpPhaseObstruction.lean`.
It proves the mixed-coordinate real/pure-imaginary implication and non-Herglotz theorem, plus
centered meromorphic order laws, linear-escape invariance, and one-germ centered-Euler RH
discharge.  Mixed theorem must not be instantiated as the actual physical sheet.  Prime--Gamma
analytic germ remains open.
