# Continuous countermodel with an exact logarithmic counting remainder

- **ID:** CONTINUOUS-BEURLING-LOG-ERROR-AUDIT
- **Stage:** 3-formalized / not_new_scientific_knowledge
- **Type:** source-class audit and explicit auxiliary construction; not an RH architecture
- **Source:** `BeurlingRationalRealizability`, `BeurlingRegularIntegersOffLineZeros`,
  `FrullaniIntegral`, `MonomialLaplaceComplex`; current statements inspected.
- **Novelty:** not established; treat as an application of classical continuous Beurling constructions.

## Why this is needed

`regular_integers_do_not_constrain_zeros` chooses its model after the error exponent. Its Lean
statement proves positivity of a continuous logarithmic density and a rational transform identity,
not a counting asymptotic. Several descriptions reverse that quantifier order and infer universal
requirements on RH proof methods. Correct those descriptions independently of whether this repair
works. Continuous countermodels cannot eliminate a method whose additional discrete hypotheses
they do not satisfy.

## Concrete repair and paper proof

For real `g`, define

```
c = 4/27 + g^2/3,       r = 4/27 + 4g^2/3,
w_g(t) = (exp(t)+2-2 exp(2t/3) cos(g t)-exp(-t/3))/t,       t>0,
Z_g(s) = ((s-2/3)^2+g^2)(s+1/3)/((s-1)s^2),
J_g(t) = r exp(t) + (1-r) - r t - c t^2/2,                 t>=0,
j_g(t) = r(exp(t)-1)-c t.
```

The existing exponential factorization at `t/3` gives
`exp(t)+2-2 exp(2t/3)-exp(-t/3)>=0`. Adding
`2 exp(2t/3)(1-cos(g t))` proves `w_g>=0`. Its numerator vanishes at zero and is differentiable,
so the density is locally integrable at zero. Three Frullani terms, with pole parameters `1,0,0`
and zero parameters `2/3+i g,2/3-i g,-1/3`, give

```
exp(integral_(t>0) exp(-s t) w_g(t) dt) = Z_g(s),           Re(s)>1.
```

`J_g(0)=1`, `J_g'=j_g`, and `j_g(t)>=0` on `t>=0`: use `exp(t)-1>=t` and `r-c=g^2`.
Thus `J_g` counts a positive continuous measure with a unit atom at zero in logarithmic
coordinates. The elementary transforms of `1,t,exp(t)` yield

```
1 + integral_(t>0) exp(-s t) j_g(t) dt
  = 1 + r/(s-1) - r/s - c/s^2 = Z_g(s),                   Re(s)>1.
```

These identities explicitly pair the positive counting density with the positive logarithmic-prime
density at the level of their transforms. Lean proves the two integrability statements and transform
identities; it does not invoke a formal measure-uniqueness or convolution-exponential theorem. The exact counting formula is `N_g(x)=J_g(log x)` for `x>=1`, hence
`N_g(x)-r x = 1-r-r log x-c(log x)^2/2`. It has `O((log x)^2)` remainder and therefore, for this
**one fixed model**, `O(x^e)` for every `e>0`. When `g!=0`, `2/3+i g` is a genuine nonreal zero:
the denominator is nonzero there. The family is continuous; it is not a sequence of primes or of
unit-weight integers, and no functional equation is claimed.

## Exact formal result

`formal/GaloisForLFunctions/RHTower/BeurlingLogarithmicCounting.lean` contains 19 public theorems.
The premise-free `explicit_continuous_countermodel` instantiates `g=1` and packages:

- nonnegativity of both densities on their stated domains;
- the counting primitive as `1 + integral_0^t j(u) du`;
- integrability and both transform identities for every `Re(s)>1`;
- the exact remainder `-13/27-(40/27)log x-(13/54)(log x)^2` for `x>=1`;
- `o(x^e)` remainder for every `e>0`, with the same counting function;
- the zero at `2/3+i`, its nonzero denominator, and its real and imaginary parts.

Domain quantifiers are part of the closed statement. There is no RH premise, added axiom, numerical
certificate, discrete realization, or claimed functional equation. Local finiteness and the
interpretation through a convolution exponential are paper consequences; the formal interface is
specified by the integral identities above.

## Verification

- Scratch and production `lake env lean` checks passed.
- The comment-corrected older module also passed its direct check.
- `LEAN_NUM_THREADS=1 lake build --old GaloisForLFunctions.RHTower.BeurlingLogarithmicCounting`
  passed, rebuilding only the changed older dependency and the new leaf; other dependency jobs
  were cached. No full or umbrella build ran.
- All 19 public theorems passed an imported scratch axiom audit: only `propext`, `Classical.choice`,
  and `Quot.sound`. The private helpers are included transitively in these dependency audits.
- `RHTower.lean` imports the leaf; generated indexes refreshed; repository formal lint passed with
  existing large-file warnings. No mathematical computation was used and no Runpod job was started.

## Consequence for further research

The original arbitrary-zero theorem retains `for every exponent, there exists a model`; this new
fixed-model theorem proves a stronger error statement for zeros at the specified horizontal position
`2/3`. It does not prove arbitrary horizontal placement in a single subpower-error family.

The strongest positive survivor is the exact counting formula and the explicit pair of positive
densities with matching transforms. This is auxiliary countermodel work, not a novel RH architecture.
**NO POSITIVE SALVAGE FOUND as a new RH proof mechanism.** The intended chain remains literal zeta
coefficients → a new zero-forced relation → an off-line contradiction → RH; neither missing link
was established here.

The useful correction is to the admissible search space. Countermodels can eliminate only criteria
whose entire hypotheses they satisfy. They do not prove universal requirements that every RH proof
use exact occurrence, addition–multiplication coupling, or a prescribed order of completion. The
source comments, four directly affected cards, and the corresponding `STATUS.md` rules now retain
that distinction. Future rejection of a candidate must identify its complete assumptions and the
single countermodel satisfying them.
