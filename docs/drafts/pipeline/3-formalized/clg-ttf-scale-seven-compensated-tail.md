# CLG/TTF compensated odd positivity from scale seven

- **Stage:** 3-formalized
- **Scope:** Literal compensated odd determinant positivity for `q=π exp(2x)≥7`, hence `x≥7/16`, uniformly for `0≤C≤3·10⁹`.
- **Full chain:** Literal theta source → all signed center-mixed Hankel sections nonnegative → global Fourier-current sign → Xi Bezoutian orientation → RH.
- **Remaining:** The fixed center interval `(8/95,7/16)`, then the all-order hierarchy. Global mixed rank-six positivity and RH remain unproved.

## Sharp finite cooling against the complete measure

Let `φ` be the first theta atom, `Φ` the complete theta source, `R=Φ/φ−1`, and

`q=π exp(2x)`, `ε=exp(−3(q−π))/399`.

The literal positive higher-likelihood measure `μ` is supported on `[3,∞)`. Its tilted moments are

`M_m(B)=∫ t^m exp(−Bt) dμ(t)`.

The exact scaled-moment derivative recurrence is `J_(n+1,m)=2m J_(n,m)−2J_(n,m+1)`, with `J_(0,m)=q^mM_m(B(x))`. Define scalar polynomials by

`L_(0,m)(z)=z^m`, `L_(n+1,m)(z)=2m L_(n,m)(z)−2L_(n,m+1)(z)`.

Induction using integrable tilted moments gives the exact complete-measure identity

`J_(n,m)(x)=∫ L_(n,m)(qt) exp(−B(x)t) dμ(t)`.

For `P_n=L_(n,0)`, this is also `P₀=1`, `P_(n+1)=2z(P_n′−P_n)`. For every `n≤10`, both `(−1)^nP_n(z)` and `(2z)^n−(−1)^nP_n(z)` have explicit nonnegative coefficient expansions in powers of `z−18`. Each expansion is proved by a real polynomial identity. Therefore

`0≤(−1)^nP_n(z)≤(2z)^n` for `z≥18`.

On `q≥6`, the support condition gives `qt≥18`. Integrating the signed inequalities yields

`0≤(−1)^nR⁽ⁿ⁾(x)≤(2q)^nM_n(B(x))`.

The calibrated support comparison gives `M_n(B(x))≤3^nε` when `n/3≤q−π`. Since `n≤10` and `π<3.15`, this condition holds throughout `q≥7`. Thus

`0≤(−1)^nR⁽ⁿ⁾(x)≤(6q)^nε`, `|R⁽ⁿ⁾(x)|≤(6q)^nε`.

This is a proved finite-order uniform bound, not a quantifier exchange giving every order on one fixed ray.

## Factor reflection before estimating derivatives

Set `B_x(t)=φ(x+t)φ(x−t)` and

`L_x(t)=R(x+t)+R(x−t)+R(x+t)R(x−t)`.

On a neighborhood of `t=0` for every `x>0`,

`Φ(x+t)Φ(x−t)−B_x(t)=B_x(t)L_x(t)`.

Let `b_n=B_x⁽ⁿ⁾(0)` and `ℓ_n=L_x⁽ⁿ⁾(0)`. Exact local differentiation gives, at every order,

`j_n−b_n=Σ_i binom(n,i)b_iℓ_(n−i)`.

The correction derivative has the exact formula

`ℓ_n=(1+(−1)^n)R⁽ⁿ⁾ + Σ_i binom(n,i)R⁽ⁱ⁾(−1)^(n−i)R⁽ⁿ⁻ⁱ⁾`.

The finite cooling bounds and the binomial theorem imply

`|ℓ_n|≤2(6q)^nε+(12q)^nε²` for `n≤10`, `q≥7`.

All odd `b_n` vanish by reflection symmetry, and `b₀=φ²`. Taking absolute values after this factorization retains the smaller even reflected first-atom jets.

## Explicit normalized entry errors

Use the signed normalization

`A_k=(−1)^k j_(2k)/(φ²q^k)`, `B_k=(−1)^k b_(2k)/(φ²q^k)`.

The exact first-atom rational profiles from [the effective-tail proof](clg-ttf-effective-compensated-odd-tail.md) have common denominator `(4−6u)²`, where `u=1/q`. Positive Bernstein expansions on `0≤u≤1/7` prove:

| k | First-atom interval for B_k | Complete-source error ceiling |
|---|---|---|
| 1 | `[8,9]` | `|A₁−B₁|≤1/75000` |
| 2 | `[180,210]` | `|A₂−B₂|≤1/250` |
| 3 | `[7000,8500]` | `|A₃−B₃|≤5/4` |
| 4 | `[300000,500000]` | `|A₄−B₄|≤450` |
| 5 | `[20000000,40000000]` | `|A₅−B₅|≤175000` |

For the errors, `exp(21)≥1300000000` follows from `exp(1)>2718/1000`. Together with `exp(3π)<12704`, this gives the endpoint constant `E₀=32/1300000000`. Polynomial-exponential monotonicity gives, for every `m≤5`,

`q^mε≤7^mE₀`, `q^mε²≤7^mE₀²`.

With `U=(1,9,210,8500,500000,40000000)`, the reflected convolution gives

`|A_k−B_k|≤Σ_(j=0)^k binom(2k,2j)U_j q^(k−j)[2·6^(2k−2j)ε+12^(2k−2j)ε²]`.

Substituting the proved polynomially weighted ceilings establishes every rational error in the table. The proofs retain the infinite source; numerical source samples are not premises.

## Retain the leading cofactor in the determinant comparison

Write `T(a,b,c,d,e)=ace−ad²−b²e+2bcd−c³`. Exact positive Bernstein expansions on `u∈[0,1/7]` give

`T(B₁,…,B₅)≥8·10¹⁰`, `0≤B₁B₃−B₂²≤27000`.

The first expansion is for the known degree-nine numerator minus `8·10¹⁰(4−6u)^6`; the second uses the exact leading-minor numerator. Both identities and all coefficient signs are kernel checked.

Let lowercase letters denote the complete tuple and uppercase letters the first-atom tuple. Updating coordinates in the order `e,a,b,c,d` gives the exact identity

`T(a,b,c,d,e)−T(A,B,C,D,E)`

`=(e−E)(AC−B²)`

` +(a−A)(Ce−D²)`

` +(b−B)(−(b+B)e+2CD)`

` +(c−C)(ae+2bD−c²−cC−C²)`

` +(d−D)(−a(d+D)+2bc)`.

The table bounds and entry errors keep both tuples nonnegative. For a difference of two nonnegative terms, its absolute value is at most their larger upper bound. This retains cancellation in every displayed coefficient:

| Updated entry | Absolute coefficient ceiling |
|---|---|
| e | `27000` |
| a | `350000000000` |
| b | `17000000000` |
| c | `600000000` |
| d | `9010000` |

Multiplying these ceilings by their corresponding errors and adding gives a total below `10¹⁰`. Hence the literal full-source determinant satisfies

`H/(φ⁶q⁹)=T(A₁,…,A₅)≥7·10¹⁰`.

The same entry errors give `Δ/(φ⁴q⁴)≤28000`. Strict positivity of `Δ` is already a proved global source theorem.

## Absorb the adverse compensation

The exact first-atom slope polynomial gives `|φ′|≤2qφ` on `q≥7`. The complete-source derivative errors of orders zero and one, together with `ε≤E₀`, give

`Φ≤(101/100)φ`, `|Φ′|≤(201/100)qφ`.

For `x≥0`, the inequalities `exp(2x−1)≥2x`, `π>3`, and `exp(1)>27/10` imply `16x≤q`. Therefore

`Φ|Φ′|≤(52/25)qφ²`,

`G=3Φ²+2xΦΦ′≥−(13/50)q²φ²`.

Consequently `G/(φ²q⁵)≥−13/(50·7³)` on `q≥7`. For every `0≤C≤3·10⁹`,

`[H+CΔG]/(φ⁶q⁹)≥7·10¹⁰−(3·10⁹)(28000)13/(50·7³)>5·10⁹`.

Lean exports the weak margin `5·10⁹` and strict positivity. Since `x≥7/16` implies `q≥16x≥7`, this is an explicit physical center ray.

## Current source conclusion

The canonical coefficient satisfies `10⁹<K_*<3·10⁹`. Combining the tail with [the global-energy compact reserve](clg-ttf-global-modular-energy-compensation.md) proves its positivity on

`[0,8/95] ∪ [7/16,∞)`.

The corrected weighted odd determinant is positive for every `a>0` on `r≥7/8`, as well as the [global-energy compact interval](clg-ttf-global-modular-energy-compensation.md) `0<r≤16/95`. The correction still has zero integral. The gap `(8/95,7/16)` must be controlled before the global mixed odd rank-three receiver applies. The all-order hierarchy remains a further unproved source comparison.

## Lean modules

- `LogarithmicLaplaceScoreBounds`, `ThetaCuspSharpFiniteCooling`: signed scalar and complete-measure bounds.
- `ThetaCuspFactoredReflectionError`, `ThetaCuspFactoredReflectionBound`: exact all-order factorization and finite sharp error.
- `FirstAtomOddScaleSevenBounds`, `FirstAtomOddScaleSevenLower`, `ThetaCuspFirstAtomScaleSevenProfiles`: exact positive profile, determinant, and leading-minor bounds.
- `ThetaCuspScaleSevenLikelihood`, `ThetaCuspScaleSevenEntryErrors`: explicit endpoint error ceilings for every required entry.
- `ScaleSevenHankelPerturbation`, `ThetaCuspScaleSevenOddDeterminant`: cofactor-preserving perturbation and actual determinant reserve.
- `ThetaCuspScaleSevenCompensationSource`, `ThetaCuspScaleSevenCompensatedTail`: adverse-source control and literal compensated positivity.

All 13 modules passed targeted foreground `lake env lean` checks, one process at a time. Identical checked scratch sources were copied to their module paths and wired exactly once into their area umbrellas. Only needed oleans were produced; no full or umbrella build was run.

Only five new capstones were audited with `#print axioms`: signed finite cooling, all-order factorization, the normalized compensated lower bound, canonical positivity outside the fixed gap, and corrected weighted tail positivity. Each reports only `propext`, `Classical.choice`, and `Quot.sound`. No axiom or numerical source premise was added.

Formal lint passes. All 85 new public declarations have no outside conflicts; the 13 modules total 1928 lines, with a largest file of 302 lines. Owned scratch, exploration, generator, audit, and bytecode files were removed. No owned Lean or Lake process remains.
