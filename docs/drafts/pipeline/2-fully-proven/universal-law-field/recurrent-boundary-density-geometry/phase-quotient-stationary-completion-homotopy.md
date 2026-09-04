# Phase-quotient stationary completion homotopy

- **ID:** ULF-PQSCH-001
- **Stage:** 2-fully-proven
- **Type:** unconditional pre-divisor completion-field theorem
- **Parents:** ULF-PCOB-001, ULF-CRSHC-001, ULF-RPBDT-001, ULF-PHSTH-001
- **Status:** `[PAPER-PROVED] [BRIDGE] [ONE DEFECT / OPEN HISTORY] [NOT A THETA SELECTOR]`
- **Lean:** not formalized; current task is a read-only Lean audit

## 1. Exact bridge, not higher producer

There is one local object:

```text
T_d = X - U* X U.                                         (PQSCH.1)
```

It is the pre-divisor, prime-mixed, integral--nuclear defect already constructed in Lean. The
many possible completions are not competing defects. They are positive stationary histories over
the same `T_d`.

The complete Euler covariance and prime--Hodge reachability admit a phase-resolved composition.
Every phase carries a contractive radial source channel. Its operator-valued covariance is lifted
as a Toeplitz history. The open history retains every Fourier mode; phase closure erases the
off-diagonal modes and sees only one trace-class prime covariance. Both readings have the same
local displacement `T_d`.

This proves that one conserved integral defect admits a noncompact positive homotopy fibre whose
closed phase quotient has source mass strictly below one. Operator-valued Toeplitz lifting and
phase averaging are generic. They do not explain why theta/Xi completion occupies this fibre and
therefore do not constitute the missing higher producer.

## 2. Corpus audit before construction

Required corpus searches included:

```text
operator-valued phase field Toeplitz Herglotz recurrent boundary density contraction
Toeplitz symbol Fourier coefficient positive shift fixed operator valued
functional equation phase quotient contraction field radial covariance Burnol theta
integral nuclear homotopy defect prime mixed pre-divisor history phase
```

The audit found:

- `PrimeHodgeHistoryIntegralNuclearHomotopyDefect`: one Lean term `T(t)` is Schatten-one,
  reflection-odd, has trace `sign(t)` and trace norm one off the wall, and has every same-history
  cross-prime entry nonzero. Its diagonal is the literal theta Mellin-six flux times the unsquared
  prime density. No divisor enters.
- `ULF-PCOB-001`: `T_d` is the unique bounded solution of the cubic prime-clock boundary equation;
  its prime factor is `A_d=W_dW_d*` on the literal radial half-line.
- `ULF-PHSTH-001`: every positive bounded same-`T_d` completion is `G_d+R`, where
  `R>=0` and `U*RU=R`.
- `ULF-RPBDT-001`: the finite recurrent trace density of `R` equals its grade-zero cubic boundary
  excess.
- `ULF-CRSHC-001`: the constant radial channel gives
  `C_d=W_dS_baseW_d*` and `G_d+I tensor C_d`, with trace strictly below `B_base<1`.
- `ConstitutiveToeplitzDefectIndex`: one-sided shift already supplies recurrent boundary, open
  defect history, linear index growth, and nonliftability. Therefore abstract Toeplitz recurrence
  is not new source content.
- `XiWardCubicApertureIntertwiningRateNoGo`: no linear map commuting with every radial aperture
  translation can take a primitive Burnol cubic mode to a strict-right completed-Xi mode, even if
  the map is unbounded. Any actual landing must break aperture covariance through a polar--Gamma
  boundary defect.

No corpus theorem constructs the operator-valued source phase field below. The standard part is
operator-valued Toeplitz/Herglotz lifting. New corpus-specific content is its composition with the
literal `W_d`, `S_base`, same-`T_d` completion fibre, and strict sub-unit recurrent law.

## 3. Source phase field

Fix `d>0` and put

```text
H_rad = L2((0,infinity),dL),
K     = ell2(Primes),
H     = ell2(N_0;K).
```

Let `S_base>=0` be the complete primitive Euler covariance on `H_rad`, with

```text
S_base in S_1,        Tr(S_base)=B_base<1.                (PQSCH.2)
```

Let `W_d:H_rad->K` be prime--Hodge reachability. Then

```text
W_dW_d*=A_d,          ||W_d||^2<1.                        (PQSCH.3)
```

Write `T` for the unit circle with normalized Haar measure `m`. Let

```text
V:T->B(H_rad)
```

be operator-norm measurable with `||V(z)||<=1` almost everywhere. Define the positive nuclear
source density

```text
c_(d,V)(z)=W_d V(z) S_base V(z)* W_d* in S_1(K).          (PQSCH.4)
```

Because multiplication by fixed bounded operators is continuous in trace norm, `c_(d,V)` is
Bochner measurable in `S_1(K)`. Moreover

```text
0<=c_(d,V)(z),
Tr(c_(d,V)(z))<=||W_d||^2 B_base<B_base<1                (PQSCH.5)
```

almost everywhere. Its Fourier coefficients are the trace-class operators

```text
C_j=integral_T z^j c_(d,V)(z) dm(z),       j in Z.        (PQSCH.6)
```

In particular

```text
C_0=integral_T c_(d,V)(z)dm(z)>=0,
Tr(C_0)<=||W_d||^2B_base<B_base<1.                       (PQSCH.7)
```

## 4. Positive stationary lift

For a finitely supported history vector `x=(x_n)` define

```text
F_x(z)=sum_(n>=0) z^n x_n
q_V(x,y)=integral_T <F_x(z),c_(d,V)(z)F_y(z)>dm(z).       (PQSCH.8)
```

**Theorem PQSCH-A (phase-field Toeplitz lift).** The form `q_V` extends uniquely to a positive
bounded operator `R_(d,V)` on `H`. With `E_n:K->H` the inclusion at history grade `n`, its blocks
are

```text
E_n* R_(d,V) E_m=C_(m-n).                                (PQSCH.9)
```

For the unilateral history shift `U`,

```text
U* R_(d,V) U=R_(d,V).                                    (PQSCH.10)
```

**Proof.** Positivity is pointwise positivity of `c_(d,V)`. Parseval gives

```text
|q_V(x,y)|<=esssup_z ||c_(d,V)(z)|| ||x|| ||y||,
```

so Riesz representation produces a unique positive bounded operator. Substituting
`F_(E_nu)(z)=z^n u` proves `(PQSCH.9)` with the convention that the inner product is
conjugate-linear in its first variable. Since `F_(Ux)(z)=zF_x(z)` and `|z|=1`,
`q_V(Ux,Uy)=q_V(x,y)`, proving `(PQSCH.10)`. QED.

## 5. One conserved integral defect

Let `G_d` be the minimal prime--Hodge history completion and define

```text
X_(d,V)=G_d+R_(d,V).                                     (PQSCH.11)
```

**Theorem PQSCH-B (one-defect conservation law).** `X_(d,V)` is positive and bounded, and

```text
X_(d,V)-U*X_(d,V)U=T_d.                                  (PQSCH.12)
```

Its recurrent trace density and cumulative cubic boundary excess are

```text
tau_hist(R_(d,V))=Ex(X_(d,V))=Tr(C_0)<B_base<1.           (PQSCH.13)
```

For every finite prime projection `Q_F` and history cutoff `P_(N,F)`, one has the exact finite
identity

```text
Tr(P_(N,F)R_(d,V)P_(N,F))
  =N Tr(Q_F C_0 Q_F).                                    (PQSCH.14)
```

**Proof.** Equation `(PQSCH.10)` makes `R_(d,V)` cancel from the displacement. The remaining
identity is `G_d-U*G_dU=T_d`. The grade-zero compression is `C_0` by `(PQSCH.9)`, so
`ULF-RPBDT-001` gives `(PQSCH.13)--(PQSCH.14)`. The strict estimate is `(PQSCH.7)`. QED.

The local charge does not vary with `V`: for positive wall parameter its nuclear trace remains
the integral `Tr(T_d)=1`, its trace norm remains one, and every same-history prime pair remains
coupled. Only the stationary completion history varies.

## 6. Closed observer versus open lifted history

For `a in T`, define the history gauge

```text
(Gamma_a x)_n=a^n x_n.
```

The weak phase average of the open history is

```text
E_phase(R)=integral_T Gamma_a* R Gamma_a dm(a).
```

**Theorem PQSCH-C (information-neutral phase quotient).** One has

```text
E_phase(R_(d,V))=I tensor C_0.                            (PQSCH.15)
```

Thus closure deletes exactly the nonzero Fourier blocks and preserves the full grade-zero
nuclear covariance and its trace:

```text
E_n*E_phase(R)E_m = 1_(n=m) C_0,
tau_hist(E_phase(R))=tau_hist(R)=Tr(C_0).                 (PQSCH.16)
```

**Proof.** The `(n,m)` block of `Gamma_a*R Gamma_a` is `a^(m-n)C_(m-n)`. Haar orthogonality kills
it unless `m=n`, when it equals `C_0`. The resulting diagonal block operator is bounded, so block
equality on finitely supported vectors extends to all of `H`. Equation `(PQSCH.16)` follows. QED.

This is the exact meaning of “closed observer projection with open lifted history”: closure is
information-neutral for recurrent mass but not information-complete. All phase-resolved temporal
correlations live in `C_j`, `j!=0`, and are invisible to the quotient.

## 7. Genuine homotopy, not a static compatibility card

Let `s->V_s` be a norm-continuous path in `L-infinity(T;B(H_rad))` through contraction fields.

**Theorem PQSCH-D (same-defect homotopy).** The path `s->X_(d,V_s)` is operator-norm continuous,
all its members obey `(PQSCH.12)`, and all have recurrent density below `B_base`.

**Proof.** For two contraction fields `V,Z`,

```text
V S_base V* - Z S_base Z*
 =(V-Z)S_base V*+Z S_base(V*-Z*).
```

Hence

```text
esssup_z ||c_(d,V)(z)-c_(d,Z)(z)||
 <=2||W_d||^2||S_base|| ||V-Z||_infinity.                (PQSCH.17)
```

The form estimate in PQSCH-A turns `(PQSCH.17)` into the same operator-norm bound for the Toeplitz
lifts. Conservation and the sub-unit estimate were proved in PQSCH-B. QED.

The constant field `V(z)=V_0` recovers exactly the harmonic completion of ULF-CRSHC-001:

```text
R_(d,V)=I tensor W_dV_0S_baseV_0*W_d*.                   (PQSCH.18)
```

Nonconstant fields are the new sector: they preserve one local integral--nuclear `T_d` while
carrying open phase history that no static harmonic symbol records.

## 8. Fourth-organ prediction and exact RH gate

`XiWardCubicApertureIntertwiningRateNoGo` proves that an actual primitive-to-completed landing
cannot commute with every radial aperture translation. Therefore any functional-equation phase
field capable of such landing must satisfy, on a set of positive phase measure,

```text
[V_theta(z), radial translation] != 0,                   (PQSCH.19)
```

or must contain an additional polar--Gamma boundary-defect channel before the positive covariance
is formed. Making `V_theta` phase-dependent is not by itself sufficient; `(PQSCH.19)` is the
corpus-forced covariance-breaking requirement.

The narrowed source theorem needed for RH is now:

1. derive from integer/Poisson formation a canonical contraction field `V_theta(z)`;
2. derive the anomaly-subtracted theta remainder as `R_(d,V_theta)`;
3. prove its covariance-breaking part is exactly the polar--Gamma functional-equation defect;
4. identify strict-right relation incidence as a nonzero projection in the same `C_0`.

Then PQSCH-B and ULF-RPBDT-001 give simultaneously

```text
1<=Tr(C_0)<B_base<1,
```

excluding every strict-right copy; reflection excludes the left half.

## 9. Hostile audit

- `[PROVED]` Positivity, bounded Toeplitz lift, stationarity, same-`T_d` displacement, finite trace
  density, strict sub-unit bound, phase quotient, and same-defect homotopy are closed on paper.
- `[NOT NEW ABSTRACT TOEPLITZ THEORY]` Operator-valued Toeplitz lifting and Haar diagonal
  expectation are standard. Claimed progress is their exact source-native placement over
  `W_dS_baseW_d*` in the prime--Hodge same-defect fibre.
- `[ONE T]` No defect is fitted to a phase or zero. Every completion has the same pre-existing
  prime-mixed integral nuclear `T_d`.
- `[NO FALSE PRIME-MIXING CLAIM]` Arbitrary contractions may erase prime entries of `C_0`; prime
  mixing is unconditional for `T_d` and for the identity-channel member, not for every phase
  field.
- `[NOT A SELECTOR]` Nothing here proves actual theta completion is `X_(d,V_theta)` or supplies
  `V_theta`.
- `[NOT AN ESCAPE FROM THE RATE NO-GO BY WORDPLAY]` Phase dependence alone does not change radial
  exponential type. Actual field must violate aperture covariance as in `(PQSCH.19)` or add the
  polar--Gamma boundary-defect channel.
- `[FALSIFIER]` If anomaly-subtracted theta remainder is not positive stationary Toeplitz, or its
  grade-zero covariance has no contractive factorization through `S_base`, this completion field
  does not govern Xi.
