# CLG/TTF effective compensated odd tail

- **Stage:** 3-formalized
- **Scope:** Explicit positivity of the literal compensated odd determinant for `q=π exp(2x)≥30`, hence `x≥6/5`, uniformly for `0≤C≤3·10⁹`.
- **Full chain:** Literal theta source → every signed center-mixed Hankel section nonnegative → global Fourier-current sign → Xi Bezoutian orientation → RH.
- **Remaining:** The fixed interval `(137/2000,7/16)` after the stronger [scale-seven proof](clg-ttf-scale-seven-compensated-tail.md), then the all-order center-mixed positivity hierarchy. Global rank-six positivity and RH remain unproved.

## All-order quantitative source comparison

Write `φ=thetaCuspSourceTerm x 1`, `Φ=thetaCuspFullSource`, `q=π exp(2x)`, and

`ε=exp(−3(q−π))/399`.

The positive higher-likelihood spectral measure is supported at least three units above the first atom. Its calibrated zeroth moment at the seam is less than `1/399`. The existing support comparison therefore gives

`M_m(B(x))≤3^m ε` when `m/3≤q−π`.

For the scaled moment `q^m M_m`, the exact derivative recurrence is

`J_(n+1,m)=2m J_(n,m)−2 J_(n,m+1)`.

Induction gives `|J_(n,m)|≤(8q)^n(3q)^m ε` whenever `q≥m+n+6`: each step costs at most `2m+6q≤8q`. In particular,

`|D^n(Φ/φ−1)|≤(8q)^n ε`.

The first-atom Gaussian monomials `E_m=exp(x/2−q)q^m` have recurrence

`E'ₘ=(2m+1/2)E_m−2E_(m+1)`.

Since `φ=4E₂−6E₁`, the parallel induction gives `|φ⁽ⁿ⁾|≤3(4q)^n φ` when `q≥n+3`. The exact Leibniz formula then yields

`|Φ⁽ⁿ⁾−φ⁽ⁿ⁾|≤3(12q)^n ε φ` when `q≥n+6`.

For the reflected jets `j_n=D_t^n[Φ(x+t)Φ(x−t)]|_(t=0)` and their first-atom counterparts `b_n`, the two linear errors and quadratic error give

`|j_n−b_n|/φ²≤18(16q)^n ε+9(24q)^n ε²≤27(24q)^n ε`.

These are all-order inequalities with explicit order-dependent thresholds; no exchange of order and center quantifiers is used.

## Uniform accuracy of the five normalized entries

The proved exponential inequalities `exp(3π)<12704` and `exp(30)>10¹³` give

`exp(3π)exp(−90)/399≤32/10³⁹`.

Polynomial-exponential monotonicity on `q≥30` yields `q⁵ε≤10⁻³⁰`. Set

`A_k=(−1)^k j_(2k)/(φ²q^k)`, `B_k=(−1)^k b_(2k)/(φ²q^k)`.

The all-order estimate gives `|A_k−B_k|≤27·24^(2k)q^k ε`. Thus `|A_k−B_k|≤10⁻¹⁰` for every `k≤5` on this ray. All exponential and arithmetic bounds are symbolic Lean proofs; sampled source values supply no premise.

## Exact first-atom reserve and perturbation

Put `u=1/q∈[0,1/30]` and `D=(4−6u)²≥9`. The five first-atom entries are `B_k=N_k(u)/D`, with coefficients in ascending powers of `u`:

| k | Coefficients of N_k |
|---|---|
| 1 | `128, −384, 480` |
| 2 | `3072, −9728, 17664, −1920` |
| 3 | `122880, −430080, 1015808, −328704, 7680` |
| 4 | `6881280, −27525120, 78446592, −49553408, 5443584, −30720` |
| 5 | `495452160, −2312110080, 7596933120, −7696220160, 2001010688, −87834624, 122880` |

Let `T(a,b,c,d,e)=ace−ad²−b²e+2bcd−c³`. The exact numerator of `T(B₁,…,B₅)` over `D³` is the degree-nine polynomial `P` with coefficients

`395824185999360, −4848846278492160, 31393805752074240, −128024385159168000, 348949943722967040, −645131575649894400, 783383995927756800, −587172709977292800, 246568703754240000, −49313740750848000`.

Expanding `P−5·10¹⁰D³`, bounding each negative-power term using `u^j≤30^(−j)`, and retaining nonnegative terms proves `T(B₁,…,B₅)≥5·10¹⁰`. The same interval bounds give `|B_k|≤10⁸`, `B₁≤9`, and `B₃≤9000`. These finite identities are proved directly from the actual reflected first-atom jets.

For two tuples bounded by `M` with entrywise error at most `δ`, telescoping each triple product gives error at most `3M²δ`. Accounting for the six signed cubic monomials proves

`|T(A)−T(B)|≤18M²δ`.

Taking `M=2·10⁸`, `δ=10⁻¹⁰` gives error at most `72,000,000`. Therefore the literal determinant `H` obeys

`H/(φ⁶q⁹)=T(A₁,…,A₅)≥49,000,000,000`.

Its leading minor `Δ` satisfies

`0<Δ/(φ⁴q⁴)=A₁A₃−A₂²≤100000`.

For the upper bound, `A₁>0`, `A₁≤10`, and `A₃≤10000`; the square is nonnegative.

## Compensation and explicit center endpoint

The exact first-atom slope polynomial is `exp(x/2−q)(−8q³+30q²−15q)`. On `q≥30`, it gives `|φ′|≤2qφ`. The derivative error and calibrated small `ε` imply

`Φ≤2φ`, `|Φ′|≤3qφ`.

The exponential lower bound also gives `6x≤q`. Consequently, for `G=3Φ²+2xΦΦ′`,

`G≥−12xqφ²≥−2q²φ²`, hence `G/(φ²q⁵)≥−2/30³`.

For `0≤C≤3·10⁹`, the normalized product of `C` and the positive leading minor is at most `3·10¹⁴`. Combining all bounds yields

`[H+CΔG]/(φ⁶q⁹)≥49·10⁹−(3·10¹⁴)(2/30³)>20·10⁹`.

Lean exports the weak lower margin `20·10⁹`, and therefore strict positivity. Finally, `exp(1)>27/10`, `exp(2/5)≥7/5`, and `π>3` give `π exp(12/5)>30`; monotonicity proves the physical ray `x≥6/5`.

The canonical coefficient satisfies `10⁹<K_*<3·10⁹`. Combining this tail with [the explicit compact proof](clg-ttf-explicit-compact-odd-compensation.md) establishes its positivity on

`[0,137/2000] ∪ [6/5,∞)`.

The corrected weighted determinant is positive for every aperture `a>0` on `r≥12/5`, as well as the previously proved `0<r≤137/1000`. The exact zero-integral correction is unchanged. The stronger [scale-seven proof](clg-ttf-scale-seven-compensated-tail.md) gives positivity for `x≥7/16`; the remaining gap is `(137/2000,7/16)`, followed by the all-order signs.

## Lean landing and audit

The 11 modules are `ThetaCuspEffectiveLikelihoodCooling`, `ThetaCuspEffectiveFirstAtomJets`, `ThetaCuspEffectiveSourceApproximation`, `ThetaCuspEffectiveReflectionApproximation`, `ThetaCuspEffectiveTailScale`, `FirstAtomOddTailAlgebra`, `HankelThreePerturbation`, `ThetaCuspEffectiveFirstAtomProfiles`, `ThetaCuspEffectiveOddDeterminant`, `ThetaCuspEffectiveCompensationSource`, and `ThetaCuspEffectiveCompensatedTail`.

All passed targeted foreground `lake env lean` checks, one process at a time. Verified scratch sources were copied identically to their module paths, retaining only needed oleans. Every module is wired into its area umbrella; no umbrella or full build was run.

Only four new capstones were checked with `#print axioms`: the all-order reflected error, effective normalized compensated lower bound, canonical positivity outside the fixed gap, and weighted effective-tail positivity. Each reports only `propext`, `Classical.choice`, and `Quot.sound`; no added axiom or numerical source premise occurs.

Formal lint passes. All 60 new public declarations have no outside conflicts; the 11 modules total 1291 lines. Owned scratch sources, probes, generators, and audit files were removed after verification. No owned Lean or Lake process remains.
