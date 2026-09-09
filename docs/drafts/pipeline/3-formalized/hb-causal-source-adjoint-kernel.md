# HB: radial evaluation of the causal source and Einstein-current factor

Status: five public theorems formalized. The complete physical tensor pairing and RH remain unproved.

Module: `GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCausalSourceAdjoint`.

This evaluates the radial/angular factors in the [explicit horizon pairing](../1-in-progress/hb-causal-horizon-circle-kernel.md), using the [actual Riemann kernel](hb-causal-riemann-kernel.md). Its two integral identities include proofs of continuity, integrability, actual derivatives, and every radial endpoint value. The full angular circle-mean realization and physical response admission remain separate obligations.

## First transfer: original source to an explicit cubic

For positive delay, `E=exp(q)>1`. The direct branch has `c=E-1`, `d=E+1`, upper endpoint one. The image branch has `c=E+1`, `d=E-1`, upper endpoint `(E-1)/(E+1)`. In both branches put

```
D=d/c, Z=E-cu, p_D(u)=(1-u)(D-u),
lambda=nu(nu+1), P=P_nu(Z),
A=(5s²+15s+4)/4, k=s(s-1)/4, B=(s+2)(2s+3).
```

The actual Legendre derivatives satisfy `(p_D P')'=lambda P`, where primes now denote radial `u` derivatives. The original source density is

```
u(1+u)^(2s)[A+k u²(B-lambda/2)]P.
```

`originalDensity_sourceRemainder` identifies its coefficient with the corpus's literal `sourceRemainder`, retaining the gradient-source coefficient `lambda/2-(s+1)(s+2)`. No new source polynomial is presumed to match the old source.

For `h=u³(1+u)^(2s)`, integration by parts transfers `lambda` from `P` to `(p_D h')'`. The flux `h p_D P'-h' p_D P` vanishes at both endpoints: `h(0)=h'(0)=0`, and `p_D` vanishes at the upper characteristic. Lean proves the resulting complete integral equality.

The transferred density equals `g_(s,D)(u)P`, with

```
g_(s,D)(u)=u(1+u)^(2s-2) C_(s,D)(u),
C_(s,D)(u)=c0+c1 u+c2 u²+c3 u³,
c0=A-3kD,
c1=2A+9k/2-3kD(4s+1)/2,
c2=A+k[2s²+14s+9-D(2s²-2s-6)],
c3=k(2s+3)[6s+3+D(2s+3)]/2.
```

The literal coefficient `B` cancels the fourth radial power. `original_source_integral_eq_cubic` proves the complete source integral is this explicit cubic-weight integral for arbitrary complex `s,nu` and both causal branches.

## Second transfer: the current factor and its forced circle term

The Einstein horizon current contains `D_covector-2`. On `coexact` scalar fields this is `coexact(Delta-2)`. In the actual Legendre kernel, its scalar factor is `lambda-2`.

The second integration by parts has a nonzero lower endpoint: `g(0)=0`, `g'(0)=c0`, so its flux contributes `D c0 P_nu(E)`. Define `L_D f=(p_D f')'`. The exact direct/image source kernel `K_s,nu,a(E)` therefore satisfies

```
(lambda-2)K_s,nu,a(E)
 = -a² integral_0^1 [(L_(D_d)-2)g_(s,D_d)] P_nu(E-(E-1)u)du
   +a² integral_0^b [(L_(D_i)-2)g_(s,D_i)] P_nu(E-(E+1)u)du
   +Gamma_s,a(E) P_nu(E),

b=(E-1)/(E+1), D_d=(E+1)/(E-1), D_i=(E-1)/(E+1),
Gamma_s,a(E)=-4a²E/(E²-1)[A-6k(E²+1)/(E²-1)].
```

`sourceKernel_action` proves this identity for the original source kernel. The density `actionDensity` contains explicitly differentiated power and cubic jets; it is not an unspecified derivative or a supplied endpoint functional.

The corresponding full-angular paper identity uses the actual circle mean `M_Z Q` in place of `P_nu(Z)`, retaining the entire theta-square source. The circle term comes from moving the angular operator inside the horizon formula. It has not been identified with the complete four-dimensional AdS action flux. The displayed terms must remain assembled near zero delay, where their separate rational expressions have singular factors. No zero-delay or infinite-time interchange is claimed by the strict-positive-delay theorem.

The next cancellation test substitutes this evaluated current factor and the literal source contacts into equation (8) of the horizon card. The remaining radial integrals, circle terms, angular boundary terms and other tensor sectors still require an assembled evaluation.

## Verification

The completed scratch file passed `lake env lean` without warnings. The exact leaf passed `lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCausalSourceAdjoint` in 8.7 seconds, three Lake jobs, with 3,972 existing own dependency caches frozen and external dependency caches reused. No dependency or umbrella build ran.

Only the five new public theorems received axiom checks. Each depends solely on `propext`, `Classical.choice`, and `Quot.sound`. Installed source and artifacts match the audited copies byte for byte. The module is imported by `RHTower.lean`.

The generated catalogs were refreshed and `python3 scripts/formal_tools.py lint` passed. Scoped `git diff --check` passed. The frontier map was not edited by this work.
