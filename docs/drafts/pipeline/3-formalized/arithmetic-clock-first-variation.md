# Exact first variation of arithmetic remainder prefixes

- **Stage:** 3-formalized
- **Type:** closed theorem F [BRIDGE]; no RH implication established
- **Modules:** `ArithmeticClockResonanceMoments`, `ArithmeticClockFirstVariation`
- **Namespace:** `RHTower.DeletionMixedRefinement`

The frozen first-variation identity and its strict sign are proved. This closes the integer-endpoint cases left undecided by the source-scaling limit. Every fixed positive complete prefix is now eventually negative as height and cutoff grow proportionally. The cutoff may depend on the prefix; the all-prefix finite-cutoff inequalities B2, C, D1, and R remain open. The independent sign constraint at the unit remainder of every zeta zero remains missing.

## Exact statement and coefficient

Let `b(v)=(fract(v)^2-fract(v))/2`, `q_h(v)=(exp(h*v)-1)/h` for `h>0`, `q_0(v)=v`, and

`J_h(sigma,lambda,A)=integral_(0..A)b(q_h(v))*exp(-(sigma+1)*h*v)*sin(lambda*v) dv`.

For fixed `sigma>=-1`, positive integer m, natural K, `0<lambda<2*pi`, and `lambda*m=2*pi*K`, Lean proves

`lim_(h->0+) J_h(sigma,lambda,m)/h = Q(sigma,lambda,m) < 0`,

where

`Q=m*[(1-sigma)/lambda^3 + sigma*cos(lambda/2)/(2*lambda^2*sin(lambda/2)) - 1/(4*lambda*sin(lambda/2)^2)]`.

This is precisely frozen F. With `c(lambda)=cos(lambda/2)/lambda^2-2*sin(lambda/2)/lambda^3`, the original frozen expression is the same coefficient:

`Q=m/[2*sin(lambda/2)]*[(sigma+2)*c+lambda*c'-(lambda/2)*c*cot(lambda/2)]`.

The exact moment representation, also proved, is

`Q=-(sigma+2)*integral_(0..m)v*b(v)*sin(lambda*v) dv - lambda/2*integral_(0..m)v^2*b(v)*cos(lambda*v) dv`.

The module defines Q by this literal integral combination; its closed formula, strict sign, and identification with the clock limit are separate theorems. No claimed remainder estimate is a premise.

## Closed proof and retained boundary information

1. **Exact finite moments.** Cell integration, including the slope jump at every integer, gives `integral_(0..m)b(v)*cos(lambda*v) dv=sin(m*lambda)*d(lambda)`, where `d=cos(lambda/2)/(2*lambda^2*sin(lambda/2))-1/lambda^3`. Differentiate this identity before imposing `lambda*m=2*pi*K`. Differentiation under the finite integral gives the first sine moment `-m*d` and second cosine moment `-2*m*d'`. Substitution yields the displayed Q.
2. **Strict sign.** Set `x=lambda/2` and `f(x)=x^2+x*sin(x)*cos(x)-2*sin(x)^2`. Direct differentiation gives `f(0)=f'(0)=0` and `f''(x)=4*sin(x)*(sin(x)-x*cos(x))>0` on `(0,pi)`. Thus `f>0`, while `d<0`, and `Q=m*[-f(x)/(8*x^3*sin(x)^2)+(sigma+1)*d]<0`. This includes the undamped boundary `sigma=-1`.
3. **Actual clock derivative.** The periodic quadratic has the global bound `|b(x)-b(y)|<=|x-y|/2` and right derivative `fract(v)-1/2` at every v, including integers. The extended clock has derivative `v^2/2` at zero and satisfies `q_h(v)>=v` for every `h>0`. The right derivative of the literal integrand is therefore `D(v)=[v^2*(fract(v)-1/2)/2-(sigma+1)*v*b(v)]*sin(lambda*v)`. This handles the slope jumps directly; no differentiability across an integer is assumed.
4. **Interchange justified.** For `v>=0`, `h>0`, and `h*v<=1`, the difference quotient is bounded in absolute value by `v^2/2+(sigma+1)*v`. On every fixed interval `[0,A]`, this is an integrable bound independent of sufficiently small h. Dominated convergence gives `(J_h-J_0)/h -> integral_(0..A)D(v) dv` for every fixed `A>=0`.
5. **Boundary term evaluated.** Integrate the right derivative of `v^2*b(v)*sin(lambda*v)/2`. Both endpoint values vanish when A=m is an integer. The resulting exact identity is `integral D=Q`, with all slope jumps retained. The proved constant-speed law gives `J_0=0` at the complete-turn endpoint, closing F.

The moving-endpoint substitution proposed on the research card is unnecessary for this proof. No numerical experiment or numerical certificate enters any declaration.

## Transfer to the literal arithmetic source and exhaustive endpoint coverage

Write `S(sigma,lambda,N;0,A)` for the scaled logarithmic integral defined in [the source-scaling certificate](arithmetic-logarithmic-phase-scaling.md). Integer periodicity and the exact change of variables give

`J_(1/N)(sigma,lambda,A)=S(sigma,lambda,N;0,A)`

for every positive integer N. Consequently at an integer endpoint coincidence,

`N*S(sigma,lambda,N;0,m) -> Q < 0`.

Since `S=N^(2*sigma+2)*Im[N^(-s)*integral_(N..N*exp(m/N))b(x)*x^(-conjugate(s)-2) dx]`, with `s=sigma+i*lambda*N`, this is the first-order coefficient of the actual anchored source, with its positive normalization retained.

For any fixed complete endpoint `A=2*pi*K/lambda`, `K>0`, split A into its integer part and fractional part. A positive fractional part has a strictly negative leading limit by the earlier theorem. A zero fractional part has the strictly negative first-order coefficient proved here. Thus all endpoints are covered:

`for every fixed sigma>=-1, 0<lambda<2*pi, and K>0, there exists N0 such that every integer N>=N0 has S(sigma,lambda,N;0,2*pi*K/lambda)<0`.

The theorem does not exchange `for every K there exists N0` with `there exists N0 for every K`. Neither an unbounded number of turns at one cutoff nor the unit cutoff at an arbitrary zero height is covered. This is why F does not prove B2, C, D1, R, or RH.

## Corpus provenance and novelty boundary

The question came from the corpus's exact equality classification in `ArithmeticLinearPhasePrefix` and literal change of variables in `ArithmeticLogarithmicPhaseScaling`. The missing information was the first signed term at their zero-margin endpoints. The proof develops that term using current-source cell primitives, parameter differentiation, right derivatives, and dominated convergence. It is not a renamed completed proof architecture.

The trigonometric inequality `(x/sin(x))^2+x/tan(x)>2` already appears as equation (5), on `0<|x|<pi/2`, in [Chen and Cheung, “Sharpness of Wilker and Huygens type inequalities” (2012)](https://hub.hku.hk/bitstream/10722/149088/1/content.pdf). Our sign argument proves its equivalent numerator inequality on `(0,pi)`, but no novelty claim is made for the ingredient, its domain, or the full arithmetic application. The paper was checked after the corpus-derived proof, and is not a Lean dependency. Global absence from literature has not been established.

## Formal declarations and audit

`ArithmeticClockResonanceMoments` has seven public definitions and nine public theorems. `ArithmeticClockFirstVariation` has four public definitions and nineteen public theorems. Principal declarations:

- `resonantClockMomentCoefficient_eq` and `resonantClockMomentCoefficient_neg`;
- `tendsto_clockVariationPrefix_quotient` and `integral_clockVariationDensity`;
- `tendsto_clockVariationPrefix_div_at_resonance`;
- `clockVariationPrefix_reciprocal_integer`;
- `tendsto_scaledLogarithmic_integer_prefix_first_order`;
- `eventually_scaledLogarithmic_complete_prefix_neg` and `eventually_scaledLogarithmic_turn_prefix_neg`.

Scratch and source checks passed with `LEAN_NUM_THREADS=1 lake env lean`. Serialized final leaf audits passed with `LEAN_NUM_THREADS=1 lake build --old GaloisForLFunctions.RHTower.ArithmeticClockResonanceMoments` and the corresponding command for `ArithmeticClockFirstVariation`, rebuilding only those leaves. Both modules are wired into `RHTower.lean`; no full or umbrella build ran. All 39 public declarations were audited from `/tmp/rh_clock_first_variation_axioms.lean`; each reports only `propext`, `Classical.choice`, and `Quot.sound`, with no added axiom or computational certificate. The corpus index was refreshed and the new limit and coefficient declarations were retrieved with the research tool. `python3 scripts/formal_tools.py lint --check-generated` passed with existing large-file warnings; its success output is in `/tmp/rh_clock_first_variation_lint.txt`. Local certificate links and the relevant tracked-file whitespace diff check passed. Every owned Lean process completed; no new Runpod computation was needed.
