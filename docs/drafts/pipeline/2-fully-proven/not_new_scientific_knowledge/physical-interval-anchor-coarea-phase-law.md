# Physical interval anchor coarea and aperture phase law

- **ID:** `physical-interval-anchor-coarea-phase-law`
- **Stage:** `2-fully-proven`
- **Type:** `[PAPER-PROVED] [FALSIFIED SIGN CONJECTURE] [POSITIVE SALVAGE] [SOURCE-SPECIFIC BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Source:** `rh-proof-shape-1707.md`, `(35m20a)`--`(35m20c)`;
  `common-profile-boolean-anchor-curvature.md`, `(CG5)`--`(CG7)`;
  `critical-multiplicative-compensated-cancellation-rh.md`, `(AC24)`--`(AC25)`
- **Statement:** For the centered clipped-interval packet, every Boolean anchor curvature is
  exactly a nonnegative Boolean-cover coarea mass minus one nonnegative rank-one centering mass;
  nevertheless the complete physical packet with `M=3`, `K=4` has a one-anchor curvature whose
  sign changes at one explicit aperture.

## Goal and bold conjecture attacked

The source-specific conjecture suggested by the generic Gram no-go was:

```text
[CONJECTURE PI-SIGN]
For every physical packet
  g_m=(log(m)/m) P_0 1_((-u_m,c-u_m] intersect (0,A)),
  u_m=log(m/M),
every nonempty squarefree Boolean anchor curvature satisfies
  kappa_C Energy(N)>=0.
```

Such a theorem would have supplied an anchorwise orientation unavailable for arbitrary Gram
packets and might have allowed the response term in `(AC25)` to be compared monotonically with
its Euler vacuum.  The conjecture is false for the complete physical packet, not merely for an
arbitrary Gram realization or independently chosen response profiles.

The strongest surviving statement is an exact source-specific signed coarea decomposition and
the complete aperture phase diagram of the smallest nonzero physical packet.

## The physical interval lift

Fix `0<c<A`.  For each positive integer `m`, put

```text
u_m=log(m/M),
I_m=(-u_m,c-u_m] intersect (0,A),
ell_m=|I_m|,
w_m=log(m)/m,
chi_m=1_(I_m),
k_m=chi_m-ell_m/A,
g_m=w_m k_m.
```

Only finitely many `g_m` are nonzero.  For a finite prime set `S`, write

```text
P_S(m)=product_(p in S)1_(p does not divide m),
F_S(t)=sum_m P_S(m)w_m chi_m(t),
L_S=integral_0^A F_S(t)dt=sum_m P_S(m)w_m ell_m,
Energy(S)=||sum_m P_S(m)g_m||_2^2.
```

Since `sum_m P_S(m)g_m=F_S-L_S/A`, orthogonal centering gives

```text
Energy(S)=integral_0^A F_S(t)^2dt-L_S^2/A.             (PI1)
```

## Boolean-cover coarea theorem

Let `C` be a nonempty finite anchor set, let `c_C=product_(p in C)p`, and assume `C` is disjoint
from `N`.  Define

```text
U_(C,N)
 =sum_(D subset C)(-1)^|D| integral_0^A F_(N union D)(t)^2dt,

B_(C,N)
 =sum_(D subset C)(-1)^|D| L_(N union D)^2.            (PI2)
```

Then both alternating expressions are nonnegative.  More precisely,

```text
U_(C,N)
 =integral_0^A sum_(m,n)
    P_N(m)P_N(n)1_(c_C|mn)w_mw_n chi_m(t)chi_n(t)dt
 >=0,

B_(C,N)
 =sum_(m,n)
    P_N(m)P_N(n)1_(c_C|mn)w_mw_n ell_m ell_n
 >=0.                                                  (PI3)
```

Consequently the physical Boolean anchor curvature has the exact signed coarea law

```text
kappa_C Energy(N)
 :=sum_(D subset C)(-1)^|D|Energy(N union D)
 =U_(C,N)-B_(C,N)/A.                                  (PI4)
```

If `B_(C,N)>0`, the dimensionless anchored overlap concentration

```text
eta_(C,N)=A U_(C,N)/B_(C,N)                            (PI5)
```

gives the complete sign classification

```text
kappa_C Energy(N)=(B_(C,N)/A)(eta_(C,N)-1).            (PI6)
```

Thus the uncentered interval lift has positive Boolean-cover curvature.  Every negative physical
anchor curvature comes from the single rank-one mean-removal channel, and its sign says exactly
whether selected interval pairs overlap less or more than the uniform baseline `1/A`.

### Proof

Insert `(PI1)` into the Boolean alternating sum.  For every pair `(m,n)`, finite
inclusion--exclusion gives

```text
sum_(D subset C)(-1)^|D|P_D(m)P_D(n)
 =product_(p in C)(1-1_(p does not divide m)1_(p does not divide n))
 =1_(c_C|mn).                                         (PI7)
```

Interchanging the finite sums proves both identities in `(PI3)`.  Every summand in their final
forms is nonnegative because `w_m`, `chi_m`, and `ell_m` are nonnegative.  Equation `(PI4)` now
follows from `(PI1)`, and `(PI6)` is immediate.  No spectral, asymptotic, or RH input occurs.

## Exact join with the full AC25 response

Let the `(AC25)` pairs `(p,a)` satisfy

```text
a|P_<p,       D/p<a<=D,
c_(p,a)=pa,   C_(p,a)=primeFactors(pa),   N_p=P_>p,

Vac_(p,a)=sum_h theta_h(pa)V_(N_p)(h)J_h.
```

The future divisor average over `r` is already collapsed by `(CG1)`--`(CG4)`.  Summing also over
`h,p,a`, equations `(CG6)` and `(PI4)` give the exact source-specific normal form

```text
R_M
 :=sum_(h,p,a)mu(a)theta_h(pa)
       E_(r~w_(N_p,h))[mu(r)B_(pa,r,h)]

 =sum_(p,a)mu(a)
    [U_(C_(p,a),N_p)-B_(C_(p,a),N_p)/A-Vac_(p,a)].    (PI8)
```

Hence the complete checkpoint `(AC25)` is identically

```text
FCRJ_M
 =sum_h J_h S_z(h)
  -sum_(p,a)mu(a)U_(C_(p,a),N_p)
  +A^(-1)sum_(p,a)mu(a)B_(C_(p,a),N_p)
  +sum_(p,a)mu(a)Vac_(p,a).                            (PI9)
```

This is genuinely after the `h,p,a,r` joining.  It is not a positivity theorem: the outer
`mu(a)` signs remain, and even one fixed physical anchor can have either curvature sign, as the
next theorem shows.

## Complete physical two-prime aperture phase law

Take

```text
M=3,       K=4,       c=log(4/3),
a=log(3)/3,            b=log(2)/2,
d=log(3/2).
```

For every `A>=log 2`, all nonzero physical atoms are exactly `m=2,3`: indices `m>=4` have empty
cells, while the only possible lower index is `m=1`, whose weight is `log(1)=0`.  Their cells are

```text
I_3=(0,c],             I_2=(d,d+c]=(log(3/2),log 2].  (PI10)
```

They have length `c` and are disjoint because `4/3<3/2`.  Therefore

```text
||k_2||^2=||k_3||^2=c-c^2/A,
<k_2,k_3>=-c^2/A.                                     (PI11)
```

For the anchor `C={2}` and `N=empty`, the sieve kills the `m=2` atom and retains the `m=3` atom.
Thus the complete physical curvature is

```text
kappa_{2} Energy(empty)
 =Energy(empty)-Energy({2})
 =||b k_2+a k_3||^2-||a k_3||^2
 =b^2(c-c^2/A)-2ab c^2/A
 =(bc/A)[b(A-c)-2ac].                                 (PI12)
```

There is exactly one transition aperture

```text
A_*=c(1+2a/b)
   =c(1+4log(3)/(3log(2))),                            (PI13)
```

and, throughout the full-cell range `A>=log 2`,

```text
kappa_{2}Energy(empty)<0  iff A<A_*,
kappa_{2}Energy(empty)=0  iff A=A_*,
kappa_{2}Energy(empty)>0  iff A>A_*.                  (PI14)
```

The transition lies strictly between `3c` and `4c`.  Indeed,

```text
3c<A_*  iff 8<9,
A_*<4c  follows from 3^4<2^9.                         (PI15)
```

Both integer apertures are inside the full-cell range because
`log 2<3log(4/3)` is `2<64/27`.  Directly,

```text
A=3c:
  kappa_{2}Energy(empty)=(2bc/3)(b-a)<0,
  because 3log(2)<2log(3), equivalently 8<9;

A=4c:
  kappa_{2}Energy(empty)=(bc/4)(3b-2a)>0,
  because 9log(2)>4log(3), equivalently 2^9>3^4.       (PI16)
```

This is an exact configuration of the whole physical packet for those parameters.  It does not
zero unwanted translated-interval vectors by hand, and it uses the actual weights `log(m)/m`.
Since `2` and `3` are prime, it is also the complete nonzero von Mangoldt packet in
`q_4-q_3`.

## Hostile audit and significance

- **The bold sign conjecture is false.**  Centered translated intervals do not impose a fixed
  anchor orientation, even on a complete physical prime packet.
- **The no-go is stronger than generic Gram sign-surjectivity.**  The witness uses the clipped
  interval source, physical logarithmic weights, the actual support rule, and one arithmetic
  anchor.
- **Negative type does not repair the route.**  On the unclipped interior,
  `||k_u-k_v||^2=2min(|u-v|,c)` is a standard negative-type metric, but `(PI12)` shows that this
  distance structure does not orient Boolean deletion curvature.
- **Total positivity or variation diminution of the uncentered overlap cannot by itself repair
  the route.**  Equation `(PI3)` already extracts the strongest positivity visible before
  centering; the rank-one subtraction crosses zero in `(PI14)`.
- **No AC25 power has been gained.**  Equations `(PI8)`--`(PI9)` are exact joins, but `U`, `B/A`,
  and the Euler vacuum are individually at the natural macroscopic scale, while `mu(a)` restores
  signed causal interference.  Separating them by absolute values would lose the required
  `M^(-1)` factor.
- **What the result changes.**  Any surviving source theorem must control the correlation of the
  overlap defect `eta_(C,N)-1` with the causal outer signs and the Euler vacuum after the whole
  `(p,a)` sum.  There is no anchorwise positivity or monotonicity to exploit.
- **Novelty verdict.**  The exact phase witness and coarea normal form are new to the internal
  corpus, but their proof is finite Boolean inclusion--exclusion plus orthogonal mean removal.
  They are a source-specific bridge and route classification, not externally new scientific
  knowledge and not an RH advance.

## No-go closure

- **Exact killing theorem/mechanism:** `(PI12)`--`(PI16)` give a complete physical packet whose
  one-anchor curvature is negative at `A=3c` and positive at `A=4c`; centering subtracts the
  uniform overlap baseline and destroys any fixed source sign.
- **Strongest positive survivor:** `(PI3)`--`(PI6)` classify physical anchor curvature as the
  difference of two nonnegative Boolean-cover masses, with sign exactly measured by the anchored
  overlap concentration `eta`; `(PI12)`--`(PI14)` give the exact aperture phase boundary in the
  smallest nonzero packet.
- **New insight:** all negative mass is confined to the rank-one centering channel before the
  causal outer sum, but that localization does not survive as a positive estimate after the
  `mu(a)` joining.  A response theorem must correlate occupancy, centering, and Euler vacuum in
  one signed law.
- **Status:** dependency-closed paper proof; corpus search found no prior statement of this exact
  physical phase law.  Lean formalization is pending and was deliberately not run in this
  paper-only task.

## Gates

- [x] Audited against the live physical kernel `(35m20a)`--`(35m20c)`.
- [x] Audited against the common-profile curvature normalization `(CG5)`--`(CG7)`.
- [x] Joined exactly to the `h,p,a,r` response in `(AC24)`--`(AC25)`.
- [x] Supplied an exact complete physical-packet falsification with no numerical evidence.
- [x] Extracted the strongest positive coarea and phase-classification survivor.
- [x] Classified the result as an internal source-specific bridge, not external novelty.
- [ ] Formalize `(PI3)`--`(PI4)` and `(PI12)`--`(PI16)` in Lean and run the axiom/lint gates.

## Log

- 2026-07-18 — paper proof completed; `PI-SIGN` falsified; positive survivor and AC25 join
  recorded.
