# Cayley--theta record flatness mismatch

- **ID:** ULF-CTRFM-001
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parents:** `ULF-CCRHD-001`; corpus modules
  `ThetaCarrierPolarizationFisher`, `ThetaCuspTiltFluxSourceWeld`,
  `HausdorffCDDMeasureSource`, `MobiusThetaCompletePhysicalCofaceAnnihilatorNoGo`
- **Purpose:** determine whether the prime-collision record can enter one fixed additive
  Fourier-self-dual theta polarization by a state-preserving observability intertwiner.

## 1. Big-picture interpretation

Prime formation and theta completion carry the same local conservative mechanism:

```text
signed contrast S + complementary visibility E
                  |
                  v
full exit history (E S^n)_(n>=0)
```

At the prime wall, `S` is signed Cayley contrast `(x-y)/(x+y)` and `E` is geometric mean
`2sqrt(xy)/(x+y)`.  In the literal reflected theta experiment, `S_a=tanh(ax)` and
`E_a=sech(ax)`.  Both satisfy `S* S+E* E=I`, and both full-history observability maps are
isometries.

This common law does not imply that completion identifies the two gauges.  Their endpoint
regularity is different.  The prime Hodge spectral law reaches unit contrast with cubic mass;
every fixed theta tilt reaches unit contrast with a distribution flat to all orders.  This
forbids every fixed-scale, state-preserving isometric completion transport.  The surviving
completion law must change clock with history depth or be singular at the contrast boundary.

## 2. Prime-pair colligation

Let

```text
d mu_H(v)=(105/16)v^2(1-v^2)^2 1_(-1,1)(v)dv,
H_H=L2((-1,1),mu_H),
S_H f(v)=v f(v),
E_H f(v)=sqrt(1-v^2)f(v),
Omega_H(v)=1.
```

This is the cyclic spectral representation of the oriented state and signed survival operator
of `ULF-CCRHD-001`.  Its even survival moments are

```text
m_n=||S_H^n Omega_H||^2
   =105/((2n+3)(2n+5)(2n+7)).                       (CTRFM.1)
```

The full record map is

```text
O_H f=(E_H S_H^n f)_(n>=0).                          (CTRFM.2)
```

## 3. Theta colligation

Let `k(x)=thetaCuspFullSource(x)`.  The corpus proves that `k` is positive, even, and for every
real `M` has an explicit constant `C_M>0` such that

```text
k(x)<=C_M exp(-M|x|).                                (CTRFM.3)
```

For `a in R`, put

```text
Z_a=integral_R cosh(ax)k(x)dx,
d nu_a(x)=Z_a^(-1)cosh(ax)k(x)dx,
H_a=L2(R,nu_a),
S_a f(x)=tanh(ax)f(x),
E_a f(x)=sech(ax)f(x),
Omega_a(x)=1,
O_a f=(E_a S_a^n f)_(n>=0).                          (CTRFM.4)
```

Equation `(CTRFM.3)` makes `0<Z_a<infinity` for every real `a`.  For `|a|<=1`, `nu_a` is exactly
the balanced law of the two literal theta tilts in `ThetaCarrierPolarizationFisher`.

## 4. Common conservation law

**Theorem CTRFM-A (signed complementary observability).**  Both `(S_H,E_H)` and `(S_a,E_a)`
obey, for every `N>=1`,

```text
sum_(n<N) ||E S^n f||^2+||S^N f||^2=||f||^2.         (CTRFM.5)
```

Moreover `S^N f->0`, so `O_H` and every `O_a` are isometries.

**Proof.**  In the source gauge, `v^2+(1-v^2)=1`; in the theta gauge,
`tanh(ax)^2+sech(ax)^2=1`.  Multiplication operators commute, so the finite geometric identity

```text
sum_(n<N) S*^n E*E S^n+S*^N S^N=I
```

gives `(CTRFM.5)`.  Pointwise `|v|<1` and `|tanh(ax)|<1` when `a!=0`; dominated convergence gives
strong stability.  When `a=0`, `S_a=0`, so stability is immediate. QED.

Reflection acts identically in the two gauges.  Prime-pair swap sends `v` to `-v`; theta
reflection sends `x` to `-x`.  Hence `S` is odd and `E` is even, so every application of survival
reverses parity.  The source marked input is odd, giving grade parity `(-1)^(n+1)`; the canonical
theta probability vector is even, giving grade parity `(-1)^n`.  Thus a completion transport must
also carry an orientation-line twist.  This is the route-independent mechanism behind the parity
law in `ULF-CCRHD-001` and the corpus theta-polarization law.

## 5. Spectral endpoint invariant

Let `sigma_H` be the spectral law of `S_H` in `Omega_H`; thus `sigma_H=mu_H`.  Let

```text
sigma_a=(x |-> tanh(ax))_* nu_a.                     (CTRFM.6)
```

**Theorem CTRFM-B (finite-order versus flat boundary).**  The prime law has the exact cubic
endpoint asymptotic

```text
sigma_H({|v|>1-epsilon}) / epsilon^3 -> 35/2          (CTRFM.7)
```

as `epsilon->0+`.  For every fixed `a` and every `N>0`,

```text
sigma_a({|v|>1-epsilon})=O_(a,N)(epsilon^N).           (CTRFM.8)
```

If `a=0`, the left side of `(CTRFM.8)` is zero for `epsilon<1`.

**Proof.**  Symmetry gives

```text
sigma_H({|v|>1-epsilon})
 =2(105/16) integral_(1-epsilon)^1 v^2(1-v^2)^2 dv.
```

The integrand divided by `(1-v)^2` tends to `4`, so division by `epsilon^3` gives
`2(105/16)(4/3)=35/2`.

Fix `a!=0`.  From `(CTRFM.3)`, using `cosh(ax)<=exp(|a||x|)`, for every `R>0` there is
`D_(a,R)` with

```text
nu_a({|x|>L})<=D_(a,R)exp(-R L).                     (CTRFM.9)
```

Now `|tanh(ax)|>1-epsilon` implies

```text
|x|>artanh(1-epsilon)/|a|
    =(1/(2|a|))log((2-epsilon)/epsilon).
```

Apply `(CTRFM.9)` with `R=2|a|N`.  Since `(2-epsilon)/epsilon>=1/epsilon`, the resulting bound is
at most `D_(a,R)epsilon^N`. QED.

Thus the prime completion boundary has finite order three, while every stationary theta chart is
infinitely flat.  This order/flat dichotomy is invariant under any state-preserving spectral
intertwiner; it is not visible from the shared Pythagorean identity alone.

## 6. Moment form and fixed-scale impossibility

Define theta survival moments

```text
q_n(a)=||S_a^n Omega_a||^2
      =integral_R |tanh(ax)|^(2n)d nu_a(x).           (CTRFM.10)
```

**Theorem CTRFM-C (superpolynomial theta record).**  For fixed `a` and every `K>0`,

```text
n^K q_n(a)->0.                                       (CTRFM.11)
```

By contrast,

```text
n^3 m_n->105/8.                                      (CTRFM.12)
```

**Proof.**  The claim is immediate for `a=0`.  Suppose `a!=0`.  For `t>=0`,

```text
tanh(t)^(2n)<=(1-sech(t)^2)^n
              <=exp(-n sech(t)^2)
              <=exp(-n exp(-2t)).                   (CTRFM.13)
```

The last inequality uses `cosh(t)<=exp(t)`.  Split at
`L_n=log(n)/(4|a|)`.  On `|x|<=L_n`, `(CTRFM.13)` is at most `exp(-sqrt(n))`.  On the complement,
`(CTRFM.9)` with an arbitrarily large `R` gives `O(n^(-R/(4|a|)))`.  Choose
`R>4|a|K`.  This proves `(CTRFM.11)`.  Equation `(CTRFM.12)` follows directly from `(CTRFM.1)`.
QED.

**Corollary CTRFM-D (no fixed theta completion intertwiner).**  For no real `a` is there a linear
isometry

```text
U:H_H->H_a,
U Omega_H=Omega_a,
U S_H=S_a U.                                         (CTRFM.14)
```

The same is true after restricting both spaces to the cyclic subspaces generated by their marked
states.

**Proof.**  Such a `U` would give

```text
m_n=||S_H^n Omega_H||^2
   =||S_a^n Omega_a||^2=q_n(a)
```

for every `n`, contradicting `(CTRFM.11)` and `(CTRFM.12)`. QED.

Compact Hausdorff moment determinacy gives the equivalent spectral statement: the full survival
record determines the contrast law, and the two laws are unequal.

## 7. Exact consequence for the RH mechanism

The common complementary-observability law is genuine but insufficient.  It unifies three
structurally different organs:

1. literal mixed-prime Cayley formation;
2. additive theta likelihood polarization;
3. closed dephased history versus open coherent record.

It predicts, and CTRFM-D proves, a restriction in the fourth organ: theta/Poisson completion cannot
be a fixed-scale state-preserving map on the completed `L2` carrier.  This independently agrees
with `MobiusThetaCompletePhysicalCofaceAnnihilatorNoGo`, where every continuous same-`L2` coface
annihilator kills the theta source itself.

Therefore the remaining completion transport must alter endpoint order.  Equivalently, it must
contain at least one of:

```text
history-dependent theta scale a_n,
singular boundary clock blow-up at |contrast|=1,
non-isometric anomaly counterterm changing the marked spectral law.
```

A fixed `a`, bounded gauge conjugacy, or stationary Markov recovery is now closed.  This does not
prove RH: it narrows the source model class required by `MUST-157` from arbitrary singular
relative functors to functors that explicitly convert a cubic endpoint into an infinitely flat
theta endpoint while preserving the integral source record.

## 8. Hostile novelty audit

- `[REDISCOVERED]` The observability telescope is standard stable-contraction theory.
- `[REDISCOVERED]` A cyclic self-adjoint operator is determined by its marked spectral measure;
  compact moment determinacy is classical and already Lean-certified in the corpus.
- `[CORPUS FUSION]` The signed Cayley and theta contrast gauges, their alternating parity, and the
  cubic-versus-flat endpoint obstruction are obtained only after combining the corpus's literal
  prime collision law with its literal theta superexponential envelope.
- `[NEW RESTRICTION]` Any RH-relevant completion preserving the full marked record must be a
  running/singular clock conversion, not a fixed theta polarization.  No divisor or zero enters
  this theorem.

## 9. Lean status

Paper proof dependency-closed.  No Lean file was written during the current read-only research
phase.  Corpus Lean already proves the two exact contrast formulas, theta superexponential
envelope, compact moment determinacy, and same-`L2` coface no-go.  Future Stage 3 should formalize
the abstract observability theorem, endpoint-flatness estimate, moment mismatch, and intertwiner
impossibility without re-formalizing theta source construction.

## Lean certificate

- [x] 2 → 3: Lean `GaloisForLFunctions.HTGeometry.CayleyThetaRecordFlatness`; `lake env lean` + module build pass; axiom audit `[propext, Classical.choice, Quot.sound]` only

Module `GaloisForLFunctions.HTGeometry.CayleyThetaRecordFlatness` (98 constants, axiom-audit clean), on top of the CCRHD modules and the corpus theta source (`thetaCuspFullSource`, its exponential envelope `thetaCuspFullSource_derivative_exp_bound`, `HedenmalmThetaSource.integrable_exp_mul_thetaCuspFullSource`, `thetaTiltProb`). Prime gauge: `hodgeSpectralLaw = μ_H`, `hodgeSpectralSurvival = S_H`, `hodgeSpectralExit = E_H`, `hodgeSpectralState = Ω_H`; theta gauge: `thetaBalanceLaw a = ν_a`, `thetaSurvival a = S_a`, `thetaExit a = E_a`, `thetaState a = Ω_a`.

| Claim | Lean declaration |
|-|-|
| §2 prime colligation; `μ_H` is the spectral law of the CCRHD state | `hodgeSpectralLaw`, `isProbabilityMeasure_hodgeSpectralLaw`, `integral_hodgeCollision_sq_mul_contrast` |
| (CTRFM.1) `m_n = ‖S_Hⁿ Ω_H‖² = 105/((2n+3)(2n+5)(2n+7))` | `norm_hodgeSpectralSurvival_pow_sq` |
| (CTRFM.2) `O_H f = (E_H S_Hⁿ f)_n` | `observability`, `hodgeSpectral_colligation`, `hodgeSpectral_stable` |
| (CTRFM.3) theta envelope, `0 < Z_a < ∞` | corpus `thetaCuspFullSource_derivative_exp_bound`; `integrable_exp_abs_cosh_theta`, `thetaBalanceMass_pos`, `thetaBalanceMass_eq` |
| (CTRFM.4) `ν_a`, `S_a = tanh(ax)`, `E_a = sech(ax)`, `Ω_a = 1`; balanced law of the literal tilts for `|a| ≤ 1` | `thetaBalanceLaw`, `thetaSurvival`, `thetaExit`, `thetaState`, `thetaBalanceLaw_eq_balancedLaw` |
| Theorem A, (CTRFM.5): `S*S + E*E = I`, telescope, `Sᴺ → 0`, `O` isometric, in both gauges | `multiplier_colligation`, `theta_colligation`, `theta_stable`, `colligation_telescope`, `sum_norm_exit_sq_add`, `norm_observability_apply` |
| Theorem A, parity: `S_a` odd, `E_a` even, `JΩ_a = Ω_a`, `Je_n = (-1)ⁿ e_n` (prime side `(-1)ⁿ⁺¹`: CCRHD `pairSwap_collisionExitVector`) | `thetaReflection_conj_survival`, `thetaReflection_conj_exit`, `thetaReflection_state_and_exit`, `measurePreserving_neg_thetaBalanceLaw` |
| (CTRFM.6) `σ_a = tanh(a·)_* ν_a` | `thetaContrastLaw` |
| Theorem B, (CTRFM.7): `σ_H(|v| > 1-ε)/ε³ → 35/2` (exact polynomial form) | `hodgeSpectralLaw_endpoint`, `tendsto_hodgeSpectralLaw_endpoint` |
| Theorem B, (CTRFM.8)–(CTRFM.9): `σ_a(|v| > 1-ε) = O(εᴺ)`; zero at `a = 0` | `thetaContrastLaw_endpoint_le`, `thetaBalanceLaw_real_endpoint_le`, `exp_neg_two_abs_lt_of_tanh`, `thetaContrastLaw_zero_endpoint` |
| (CTRFM.10) `q_n(a) = ‖S_aⁿ Ω_a‖²` | `thetaSurvivalMoment`, `norm_thetaSurvival_pow_sq` |
| Theorem C, (CTRFM.11)–(CTRFM.13): `nᴷ q_n(a) → 0`; `n³ m_n → 105/8` | `tendsto_pow_mul_thetaSurvivalMoment`, `thetaSurvivalMoment_le`, `tendsto_pow_three_mul_m` |
| Corollary D, (CTRFM.14): no isometric `U`, `UΩ_H = Ω_a`, `US_H = S_aU`; same on cyclic orbits; spectral laws unequal | `no_theta_completion_intertwiner`, `not_forall_norm_survival_eq`, `exists_survivalMoment_ne`, `hodgeSpectralLaw_ne_thetaContrastLaw` |
| Summary | `cayley_theta_record_flatness_mismatch` |

§1, §7 and §8 are interpretation and audit.

## Log

- 2026-09-29 — Lean certificate audited; every numbered claim mapped to a declaration; moved to 3-formalized.
