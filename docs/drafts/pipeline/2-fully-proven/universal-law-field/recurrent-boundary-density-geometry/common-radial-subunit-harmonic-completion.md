# Common-radial sub-unit harmonic completion

- **ID:** ULF-CRSHC-001
- **Stage:** 2-fully-proven
- **Type:** unconditional pre-divisor source-construction theorem
- **Parents:** ULF-PCOB-001, ULF-LBCNS-001, ULF-PHSTH-001, ULF-RPBDT-001
- **Status:** `[PAPER-PROVED] [SOURCE HALF CLOSED] [NOT ACTUAL XI COMPLETION]`
- **Lean:** not formalized; this pass audits Lean read-only and performs no Lean build

## 1. Higher law

The prime--Hodge defect and the complete primitive Euler budget do not merely have comparable
numbers. They are two covariances over the same literal radial space `L2(0,infinity)`.

The prime--Hodge reachability map reads radial cubic modes into the ordinary-prime carrier. The
Burnol covariance contains every resolved prime-depth Euler column on that radial space. Sandwich
the latter by the former:

```text
radial Euler covariance S_base
        |
        | prime--Hodge reachability W_d
        v
C_d=W_d S_base W_d* on ell2(Primes).                    (CRSHC.1)
```

This creates a canonical positive prime-mixed horizon symbol whose trace is strictly below the
complete Euler budget. Repeating that symbol through open history and adding the minimal
prime--Hodge completion gives a positive bounded completion with exactly the original local defect
`T_d` and sub-unit recurrent density.

The source half of the direct sub-unit mechanism therefore exists on one carrier. What remains is
not construction of a budgeted completion; it is proving that anomaly-subtracted theta/Xi
completion selects this source-built completion, or is dominated by it, before divisor data.

## 2. Corpus collision audit

Required searches included:

```text
prime Hodge reachability Burnol nuclear source sandwich common radial
R_d S_base R_d adjoint prime compressed covariance
common radial half line prime Hodge Burnol completion
harmonic lift Burnol covariance same defect prime Hodge
source budget recurrent horizon prime compressed covariance
```

They found the ingredients but no sandwich `(CRSHC.1)` or its same-defect harmonic completion:

- `ULF-PCOB-001` constructs `W_d:L2(0,infinity)->ell2(Primes)`, proves
  `W_dW_d*=A_d`, `||W_d||_HS^2=1`, and proves `W_d` and `W_d*` injective.
- `RoutePPrimitiveBurnolBaseNuclearSynthesis` / `ULF-LBCNS-001` constructs on the same Lebesgue
  half-line the positive covariance `S_base`, with `Tr(S_base)=B_base<1`.
- `RoutePPrimitiveBurnolWardResolvedGeneratorGraph` identifies every Burnol column as a
  coefficient-weighted `L exp(-lambda L)` radial generator mode. These are the same cubic radial
  species used by `W_d`; the composition is not an abstract Hilbert-space identification.
- `FrankensteinCCMRoutePBaseCubicGreenSourceBridge` already proves coefficient-faithful natural-
  number/primitive-cell carrier identification for `B_base`.
- `ULF-PHSTH-001` classifies harmonic same-defect additions but does not supply a source-forced
  sub-unit symbol.
- `ULF-RPBDT-001` reads any such symbol as recurrent cubic boundary density.

Generic covariance sandwiches and their trace bounds are standard. New corpus content is the
literal common-radial composition and its exact placement in the same-`T` completion fibre.

## 3. Two source maps on one radial space

Fix `d>0`. Let

```text
H_rad=L2((0,infinity),dL),        K=ell2(Primes).
```

The prime--Hodge reachability map is

```text
(W_d h)_p=2b_d(p) integral_0^infinity L exp(-lambda_p L)h(L)dL,
lambda_p=log p.                                             (CRSHC.2)
```

ULF-PCOB-001 proves

```text
W_dW_d*=A_d,           ||W_d||_HS^2=Tr(A_d)=1,             (CRSHC.3)
ker W_d=ker W_d*=0.                                         (CRSHC.4)
```

Let `I=Primes x N_0`. At zero source clock the Burnol synthesis is

```text
B:ell2(I)->H_rad,       B c=sum_alpha c_alpha f_alpha,
f_(p,e)(L)=a_(p,e) L exp(-((e+1)log p)L),                  (CRSHC.5)
```

with positive literal von-Mangoldt amplitude `a_(p,e)`. Its range covariance is

```text
S_base=BB*>=0,          S_base in S_1,
Tr(S_base)=||B||_HS^2=B_base<1.                            (CRSHC.6)
```

No zero, divisor, ordinate, or adjustable carrier equivalence occurs.

## 4. Prime compression of the complete Euler covariance

Define

```text
C_d=W_d S_base W_d*:K->K.                                  (CRSHC.7)
```

**Theorem CRSHC-A (canonical prime-mixed sub-unit symbol).** `C_d` is positive and trace class,
and

```text
0<Tr(C_d)<=||W_d||^2 B_base<B_base<1.                      (CRSHC.8)
```

Every prime matrix entry of `C_d` is strictly positive.

**Proof.** Positivity follows from

```text
C_d=(W_d S_base^(1/2))(W_d S_base^(1/2))*.
```

Since `S_base` is trace class and `W_d` is bounded, the ideal property makes `C_d` trace class.
Cyclicity and `0<=W_d*W_d<=||W_d||^2 I` give

```text
Tr(C_d)
 =Tr(S_base^(1/2)W_d*W_dS_base^(1/2))
 <=||W_d||^2 Tr(S_base).
```

Now `||W_d||^2=||W_dW_d*||=||A_d||`. The positive compact operator `A_d` has trace one and is
injective on the infinite-dimensional prime carrier. Its top eigenvalue cannot equal one: that
would consume the whole trace while injectivity forces further positive eigenvalues. Hence
`||W_d||^2<1`. Equation `(CRSHC.6)` proves the upper chain in `(CRSHC.8)`.

The covariance `S_base` is nonzero. Since `W_d` is injective,
`W_dS_base^(1/2)` is nonzero, so `Tr(C_d)>0`.

For matrix entries, put `g_p=W_d*e_p`. Equations `(CRSHC.2)` and `(CRSHC.5)` make every `g_p` and
every nonzero `f_alpha` strictly positive almost everywhere. Therefore

```text
<e_p,C_de_q>
 =<g_p,S_base g_q>
 =sum_alpha <g_p,f_alpha><f_alpha,g_q>>0.                 (CRSHC.9)
```

The sum converges because it is the Gram expansion of the Hilbert--Schmidt synthesis. QED.

Thus `C_d` preserves full prime mixing and all prime-depth source provenance while paying less
than one recurrent unit.

## 5. The source-built same-defect completion

Let `H_h=ell2(N_0)`, `mathcal U=S tensor I_K`, and let

```text
G_d=diag(m_n) tensor A_d,       T_d=diag(w_n) tensor A_d
```

be the prime--Hodge completion and defect. Define

```text
X_d^src=G_d+I_(H_h) tensor C_d.                             (CRSHC.10)
```

**Theorem CRSHC-B (sub-unit harmonic completion).** `X_d^src` is bounded and positive, and

```text
X_d^src-mathcal U*X_d^src mathcal U=T_d.                   (CRSHC.11)
```

Its harmonic remainder is `R_d^src=I tensor C_d`, and its recurrent density and cumulative cubic
boundary excess are

```text
tau_hist(R_d^src)=Ex(X_d^src)=Tr(C_d)<B_base<1.             (CRSHC.12)
```

Although `R_d^src` has infinite total trace, every finite history/prime compression obeys the
exact ULF-RPBDT-001 law.

**Proof.** Positivity and boundedness are immediate. Since `S*S=I`,

```text
mathcal U*(I tensor C_d)mathcal U=I tensor C_d.
```

It cancels from the displacement, leaving
`G_d-mathcal U*G_dmathcal U=T_d`. Grade-zero compression of the remainder is `C_d`, so
ULF-RPBDT-001 and `(CRSHC.8)` give `(CRSHC.12)`. Since `C_d` is nonzero, identical positive
diagonal blocks repeat at every history grade, making total trace infinite. QED.

## 6. Joint reconstruction law

The single object `X_d^src` has four exact recoveries:

```text
history displacement        -> T_d;
minimal history tail        -> G_d;
grade-zero harmonic symbol  -> W_dS_baseW_d*;
recurrent cubic excess      -> Tr(W_dS_baseW_d*)<B_base.   (CRSHC.13)
```

The source object asked for by the direct sub-unit programme therefore exists without choosing a
zero or mapping between unrelated carriers. The `T_d` defect remains the integral unit; the new
harmonic symbol is the sub-unit Euler financing of its completion ambiguity.

## 7. Contractive radial completion class

The canonical sandwich is the identity-channel member of a larger source-controlled class. For
any contraction `V:H_rad->H_rad`, define

```text
C_(d,V)=W_d V S_base V* W_d*,
X_(d,V)=G_d+I tensor C_(d,V).                              (CRSHC.14)
```

**Theorem CRSHC-C (contractive common-radial admissibility).** Every `X_(d,V)` is positive,
bounded, and has the same local defect `T_d`. Moreover

```text
Ex(X_(d,V))=Tr(C_(d,V))
 <=||W_d||^2 ||V||^2 B_base<B_base<1.                     (CRSHC.15)
```

**Proof.** Positivity and the displacement identity are the proof of CRSHC-B with `C_d` replaced
by `C_(d,V)`. Cyclicity gives

```text
Tr(C_(d,V))
 =Tr(S_base^(1/2)V*W_d*W_dVS_base^(1/2))
 <=||W_dV||^2 Tr(S_base)
 <=||W_d||^2||V||^2B_base.
```

Use `||V||<=1`, `||W_d||^2<1`, and ULF-RPBDT-001. QED.

This is the exact admissibility class suggested by the working theory: after anomaly subtraction,
completion may move the radial Euler polarization, but any contractive movement remains strictly
below one recurrent unit. The functional equation must still supply its particular `V`; the
theorem does not assume every completion is contractive.

## 8. Exact limit of the theorem

`X_d^src` is a canonical pre-divisor reference completion. It is **not proved** to be the relative
completion selected by the actual theta functional equation. Nor is an off-line relation horizon
proved to sit in its grade-zero symbol.

Indeed `(CRSHC.15)` means no member of this contractive radial class can contain a rank-one
projection in its grade-zero covariance. Therefore the following selection statement would close
RH:

> anomaly-subtracted theta/Xi completion has a harmonic grade-zero covariance of the form
> `W_d V S_base V* W_d*` for a source-forced contraction `V`, while strict-right incidence forces
> a nonzero projection in that covariance.

This statement is now a **common-radial factorization theorem**, not an unspecified map from a
finite covariance to a horizon on another carrier. `ULF-TRDS-001` is updated to this exact edge.

## 9. Hostile audit

- `[PAPER-PROVED]` Common carrier, positivity, trace-class membership, trace bound, strict prime
  mixing, same displacement, and recurrent-density formula are dependency-closed.
- `[NO FITTED MAP]` `W_d` and `S_base` pre-exist independently and are both literal radial
  source constructions. No abstract unitary or rank-matching identification is inserted.
- `[NOT NUMERICAL]` Only existing symbolic theorem `B_base<1` is used.
- `[NOT A SELECTOR]` Many positive harmonic symbols can be added to `G_d`; the theorem constructs
  the source-canonical Burnol sandwich and its contractive class but does not prove theta
  completion belongs to that class.
- `[NOT RH]` Actual completion factorization and relation-incidence grade-zero
  identification remain open.
- `[FALSIFIER]` If the functional-equation completion does not factor through the common radial
  covariance by a contraction, or its relative harmonic symbol is not positive, this source
  completion class is not physical.

## 10. Note (2026-09-05): the selection statement of §8 is refuted on this carrier

The anomaly-subtracted theta/Xi divisor side on `H_rad` is the Hankel form `pole − S_base`
(rate measure `du − ν_E`), which is indefinite: Lean
`RHTower.poleHankelEnergy_radialSpike_lt_re_inner_baseNuclearSource`
(`RadialCarrierPoleHankelEulerSourceIndefinite`). No source-forced contraction `V` realizes it as
`W_d V S_base V* W_d*`. Theorems CRSHC-A/B/C stand as bridge structures. See ULF-TRDS-001 §9
(`5-failed`).
