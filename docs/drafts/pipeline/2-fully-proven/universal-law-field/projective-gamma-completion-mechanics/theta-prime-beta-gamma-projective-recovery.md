# Theta--prime beta--gamma projective recovery

- **ID:** ULF-BGPR-001
- **Stage:** 2-fully-proven
- **Labels:** `[PAPER-PROVED] [BRIDGE] [CORPUS FUSION]`
- **Parents:** ULF-TM6H-001, ULF-CTRFM-001, ULF-TSRC-001, ULF-PHIN-001
- **Purpose:** replace the impossible fixed theta-contrast transport by an explicit source-defined
  additive-completion/projective-formation coupling with exact recovery.

## 1. What is wrong first

Hausdorff or de Finetti representation of the survival moments is not completion transport. It
only reconstructs a compact source law. Corpus countermodels prove that moment-cone membership
does not identify a source point with a target, and the existing de Finetti consumer reaches RH
only after assuming the missing prime--archimedean moment comparison.

A fixed theta contrast is also impossible. ULF-CTRFM-001 proves that prime survival has cubic
endpoint mass while every fixed `tanh(a x)` theta chart is flat to all orders. No fixed-scale
state-preserving intertwiner exists.

The surviving representation is not a pointwise theta contrast. It is the projective coordinate
of the exact six-unit Mellin completion.

## 2. Gamma completion coordinates

For `alpha>0`, let `Gamma(alpha,pi)` denote the probability density

```text
g_alpha(x)=pi^alpha x^(alpha-1) exp(-pi x)/Gamma(alpha),  x>0.   (BGPR.1)
```

Take independent variables

```text
X ~ Gamma(3/2,pi),
Y ~ Gamma(3,pi),
V=X+Y,
U=X/V.                                                        (BGPR.2)
```

**Theorem BGPR-A (projective gamma factorization).** `U` and `V` are independent, with

```text
U ~ Beta(3/2,3),
V ~ Gamma(9/2,pi).                                           (BGPR.3)
```

**Proof.** Change variables `x=uv`, `y=(1-u)v` on `(0,infinity)^2`. The Jacobian is `v`. The joint
density becomes

```text
[Gamma(9/2)/(Gamma(3/2)Gamma(3))
   u^(1/2)(1-u)^2]
 *[pi^(9/2)/Gamma(9/2) v^(7/2) exp(-pi v)].                  (BGPR.4)
```

The two brackets are probability densities in `u` and `v`, proving both laws and independence.
QED.

## 3. Literal theta Mellin-six identity

The pole-stripped first theta atom of ULF-TM6H-001 is

```text
G_theta(s)=Gamma_R(s)=pi^(-s/2) Gamma(s/2).                  (BGPR.5)
```

For every `n>=0`, Gamma moments give

```text
G_theta(2n+3)/G_theta(3)=E[X^n],
G_theta(2n+9)/G_theta(9)=E[V^n].                             (BGPR.6)
```

Since `X=UV` and `U` is independent of `V`,

```text
H_n=[G_theta(2n+3)/G_theta(2n+9)]
      /[G_theta(3)/G_theta(9)]
   =E[X^n]/E[V^n]
   =E[U^n]
   =105/[(2n+3)(2n+5)(2n+7)]
   =m_n.                                                     (BGPR.7)
```

Thus six Mellin units are not merely a Gamma recurrence. They are an independent positive
completion leg of shape `3`; theta history is the scale-free ratio of the shape-`3/2` input and
its shape-`3` completion.

## 4. Exact signed prime recovery

Let `epsilon` be an independent symmetric sign and set

```text
D=epsilon sqrt(U),
E=sqrt(1-U).                                                (BGPR.8)
```

**Theorem BGPR-B.** `D` has density

```text
(105/16) d^2(1-d^2)^2 1_(-1,1)(d),                         (BGPR.9)
```

which is exactly the signed prime-pair Cayley spectral law of ULF-CTRFM-001. Moreover

```text
D^2+E^2=1,
E[D^(2n)]=m_n,
E[D^(2n)E^2]=m_n-m_(n+1)=w_n.                              (BGPR.10)
```

**Proof.** Under `u=d^2`, the two signs and Jacobian transform the beta density in `(BGPR.4)` into
`(BGPR.9)`. The remaining identities follow from `D^2=U`, `E^2=1-U`, and `(BGPR.7)`. QED.

This retains orientation: theta completion adds the positive variable `Y`; it does not average
away `epsilon`.

## 5. Information-neutral recovery kernel

Use the product coordinates of `(BGPR.3)` and define

```text
H_source=L2({-1,+1} x (0,1), Rademacher x Beta(3/2,3)),
H_complete=H_source tensor L2((0,infinity),Gamma(9/2,pi)).   (BGPR.11)
```

Let

```text
(Jf)(epsilon,u,v)=f(epsilon,u),
(Pg)(epsilon,u)=integral g(epsilon,u,v) dGamma_(9/2,pi)(v). (BGPR.12)
```

**Theorem BGPR-C (projective recovery).** `J` is an isometry, `P=J*`, and

```text
P J=I,
M_phi J=J M_phi,
P M_phi=M_phi P                                             (BGPR.13)
```

for every bounded `phi(epsilon,u)`. Hence the signed survival multiplier `D`, exit multiplier
`E`, every finite record `E D^n`, and their complete observability history lift and recover
without loss.

**Proof.** Fubini and total Gamma mass one prove isometry and the adjoint formula. Functions of
`(epsilon,u)` are independent of `v`, so multiplication commutes with insertion and integration.
QED.

This is stronger than equality of scalar moments: the entire source algebra is a recovered
subalgebra of the additive Gamma completion. It evades ULF-CTRFM-001 because it does not identify
`D` with any fixed `tanh(a x)` multiplier.

## 6. Relative curvature is posterior information gain

Let `mu_n` be the survival-tilted law

```text
dmu_n(u)=u^n dBeta_(3/2,3)(u)/m_n
        =dBeta_(n+3/2,3)(u).                               (BGPR.14)
```

Then

```text
r_n=m_(n+1)/m_n=E_mu_n[U],
h_n=1-r_n=E_mu_n[1-U],
w_n=m_n h_n.                                               (BGPR.15)
```

For `n>=1`, the relative-curvature weight of ULF-TSRC-001 is

```text
kappa_n=r_n-r_(n-1)
       =Var_mu_(n-1)(U)/E_mu_(n-1)[U]
       =12/[(2n+7)(2n+9)].                                 (BGPR.16)
```

**Proof.** Power tilting shifts the first beta shape by `n`, proving `(BGPR.14)` and `(BGPR.15)`.
For any probability law with positive mean, tilting once by `u` changes the mean from `E[U]` to
`E[U^2]/E[U]`; their difference is `Var(U)/E[U]`. The beta variance formula yields the last term.
QED.

Therefore the self-commutator curvature is the normalized information gained by one further
survival event. Exit flux and metric curvature are not merely reconstructible sequences; they are
the loss and learning faces of one projective Gamma completion.

## 7. Prime-mixed integral--nuclear lift

Tensor `(J,P)` with the identity on the full prime formation carrier. Equivalently, append the
independent `V` coordinate to the history--prime object and recover by conditional expectation.
Every cross-prime matrix entry, unsquared prime diagonal, history tail `m_n`, exit weight `w_n`,
relative curvature `kappa_n`, trace, and orientation of `mathsf T` are unchanged. The total Gamma
coordinate supplies noncompact completion scale without altering compact projective formation.

The persistent survival projection in this normal source model is

```text
strong-lim_N M_(U^N)=M_(1_{U=1})=0,                         (BGPR.17)
```

because the beta law has no atom at `1`, equivalently `Y>0` almost surely. This is source-side
zero-horizon exactness, not RH.

## 8. Hostile audit and exact limitation

- `[LITERATURE]` Beta--gamma factorization and its Lukacs converse are classical. General
  beta--gamma algebra is much broader than this construction. No novelty is claimed for
  `(BGPR.2)--(BGPR.4)` alone.
- `[REDISCOVERED]` Conditional expectation onto an independent coordinate is standard.
- `[CORPUS FUSION]` New leverage is the exact identification of the corpus's literal theta
  Mellin-six holonomy, signed prime Cayley colligation, Hodge exit law, relative metric curvature,
  and prime-mixed integral--nuclear history inside that single projective completion.
- This does not identify completed Xi relative energy or relation horizon with `(BGPR.17)`.
  Assuming that identification after choosing a zero would be circular.
- A generic Gamma spectator is nonselective. Shapes `3/2` and `3`, rate `pi`, orientation line,
  prime algebra, and conditional recovery are all forced here by source formulas.

The theorem changes the open problem: no unknown theta transport is needed for the history
algebra. The remaining question is whether literal Euler--Poisson completion of the full
prime-marked carrier obeys the same projective sum/ratio independence before divisor
specialization, and whether its normal persistent projection exhausts the relation horizon.

## 9. Literature

- Ger--Misiewicz--Wesolowski, *The Lukacs theorem and the Olkin--Baker equation*:
  <https://arxiv.org/abs/1112.1226>.
- Chhaibi, *Beta-gamma algebra identities and Lie-theoretic exponential functionals of Brownian
  motion*: <https://arxiv.org/abs/1404.7029>.

## 10. Formal status

`[PAPER-PROVED]`. Existing Lean certifies the theta Mellin-six identity, beta moments, signed
contrast formulas, exit telescope, relative curvature inputs, and `mathsf T`. The joint
beta--gamma change of variables, conditional-expectation recovery, and posterior-variance law are
not yet Lean-certified and must not be cited as `[LEAN-PROVED]`.
