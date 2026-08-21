# The completed local Euler valuation tower is a Lorentz logarithm

- **ID:** `local-euler-valuation-lorentz-log-colligation`
- **Stage:** 2-fully-proven/not_new_scientific_knowledge
- **Type:** THEOREM (paper) / POSITIVE COMPLETION MODEL / RH BRIDGE
- **Scientific status:** `[PROVED HERE] [NOT FORMALIZED]
  [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parents:** `rational-hurwitz-lorentz-boost-colligation.md` and
  `../../1-in-progress/prime-valuation-veronese-master-law.md`
- **Statement:** The entire prime-power valuation tower of a reflected rational-Hurwitz fibre
  sums exactly to the matrix logarithm of its normalized Lorentz block.  This completion exists
  at every point of the open critical strip, so no local valuation tower proves RH.  Its
  anti-reflection coordinate is nevertheless a faithful critical-line detector, and its
  Gamma--Meixner prime sum has the exact horizontal-displacement convergence threshold.

## Normalized prime transfer

Let

```text
rho=1/2+a+i*t,       |a|<1/2,
L=log p,             p prime.                            (1)
```

The reflected rational-Hurwitz response at valuation degree `m` has common phase
`exp(i*m*t*L)`, critical normalization `p^(-m/2)`, and Lorentz rapidity `m*a*L`.  Therefore all
valuation degrees are powers of the single transfer

```text
T_(p,rho)=p^(-1/2) exp(i*t*L) B_a(p),                    (2)

B_a(p)=
  [ cosh(aL)  sinh(aL)
    sinh(aL)  cosh(aL) ].                                (3)
```

In light-cone coordinates the eigenvalues of `(2)` are

```text
z_+=p^(-1/2+a+i*t)=p^(-(1-rho)),
z_-=p^(-1/2-a+i*t)=p^(-conj(rho)).                       (4)
```

Both have modulus strictly less than one exactly because `rho` lies in the open critical strip.

## Exact Euler-log completion

The connected-cycle weight `1/m` gives the absolutely convergent matrix series

```text
C_p(rho)=sum_(m>=1) T_(p,rho)^m/m
        =-Log(I-T_(p,rho)).                              (5)
```

Let the power-series branch `f(z)=-log(1-z)` be used on the unit disk.  In light-cone
coordinates, `(5)` is

```text
diag(f(z_+),f(z_-)).                                     (6)
```

In even/odd coordinates it is

```text
C_p(rho)=
  [ u_p(rho)  v_p(rho)
    v_p(rho)  u_p(rho) ],                                (7)

u_p=(f(z_+)+f(z_-))/2,
v_p=(f(z_+)-f(z_-))/2.                                  (8)
```

Equivalently,

```text
v_p(rho)
 =sum_(m>=1) exp(i*m*t*L) p^(-m/2) sinh(m*a*L)/m.        (9)
```

Thus `(5)` is exactly the Euler completion of every prime-power Veronese/valuation layer, not a
new carrier fitted after seeing the divisor.

## Reflection and the exact zero set

Horizontal reflection sends `a` to `-a`, swaps `z_+` and `z_-`, fixes `u_p`, and negates `v_p`.
Moreover,

```text
v_p(rho)=0  iff a=0.                                    (10)
```

Indeed, `v_p=0` gives `f(z_+)=f(z_-)`.  Exponentiating the unit-disk logarithms gives
`1-z_+=1-z_-`, hence `z_+=z_-`.  Since their common nonzero phase cancels, `p^a=p^(-a)`, so
`a=0`.  The converse is immediate.

Consequently the completed local Euler logarithm is a faithful critical-line detector even
though its defining series converges throughout the open strip.

## Gamma--Meixner threshold

For fixed `rho` with `a != 0`, the first valuation degree dominates asymptotically.  From `(9)`,

```text
v_p(rho)
 =exp(i*t*L)p^(-1/2)sinh(aL)
   *(1+o(1))                       as p -> infinity.     (11)
```

To verify `(11)`, put `x=p^(-1/2+|a|)`.  The absolute value of the tail `m>=2` is at most

```text
sum_(m>=2) x^m/m <= x^2/(1-x),                           (12)
```

whereas the first term has order `p^(-1/2+|a|)`.  Since `|a|<1/2`, their ratio tends to zero.
Hence

```text
|v_p(rho)|^2 asymp p^(-1+2|a|).                         (13)
```

For the Gamma--Meixner weight

```text
w_theta(p)=cosh(2log p)^(-theta/2) asymp p^(-theta),     (14)
```

the positive prime series

```text
E_rho(theta)
 =sum_p 4(log p)^2 |v_p(rho)|^2 w_theta(p)              (15)
```

therefore satisfies the exact criterion

```text
E_rho(theta)<infinity  iff theta>2|a|,                  (16)
```

while `E_rho` is identically zero when `a=0`.  At equality, `(13)` reduces `(15)` to a positive
constant multiple of `sum_p (log p)^2/p`, which diverges; on either side the standard prime
Dirichlet comparison gives `(16)`.

Thus any positive multiplicity-weighted sum of `(15)` which contains every Xi divisor orbit is
finite for every `theta>0` only if every orbit has `a=0`.  Conversely, RH makes the entire
anti-reflection energy zero.  This is an exact RH consumer built from the completed Euler
valuation module.

## No-go and nontrivial positive successor

The tempting claim that infinitely many valuation degrees force the Lorentz rapidity to vanish is
false.  Equation `(4)` shows

```text
spectralRadius(T_(p,rho))=p^(-1/2+|a|)<1                (17)
```

at every open-strip point, so the complete local Euler logarithm `(5)` exists off the critical
line as well as on it.

The positive successor has three parts:

1. `(5)` is a canonical closed-form completion of the valuation-resolved HT source.
2. Its odd coordinate `(8)` detects the critical line exactly, rather than merely seeing the
   off-line direction.
3. Its all-prime Gamma--Meixner energy has the sharp threshold `(16)`.

Accordingly the missing RH mechanism cannot be local prime-power completion.  It must be the
cofinal all-prime source metric or singular Mertens-corona boundary which turns the faithful odd
coordinate into a uniformly finite positive trace for every shape.

## Parent-theory boundary

The matrix logarithm, Euler logarithm, Lorentz diagonalization, and elementary convergence tests
are classical.  Their exact alignment with the project's reflected Hurwitz fibre and
valuation-resolved HT module is a useful bridge, not a claim of new scientific knowledge.

## Gates

- [x] identify every valuation degree with a power of one normalized Lorentz transfer
- [x] prove absolute local completion throughout the open strip
- [x] compute the matrix logarithm in light-cone and even/odd coordinates
- [x] prove that the odd completed coordinate vanishes exactly on the critical line
- [x] prove its exact Gamma--Meixner convergence threshold
- [x] replace the local-completion no-go by a nontrivial positive RH consumer
- [ ] formalize only if the completed all-prime source metric uses this logarithmic colligation

## Lean formalization — COMPLETE (2026-08-21)

Module: `formal/GaloisForLFunctions/RHTower/EulerValuationLorentzLog.lean`
(wired into `GaloisForLFunctions.RHTower`; every capstone has axiom footprint
`propext, Classical.choice, Quot.sound`).  It sits on
`RHTower/RationalHurwitzLorentzBoost.lean` (the parent card's colligation, formalized first).

| Card equation | Lean declaration |
|---|---|
| `(1)`–`(3)` the normalized prime transfer `T = p^{-1/2+it}·B(a log p)` | `eulerPhase`, `eulerRapidity`, `eulerTransfer` |
| `(4)` the light-cone eigenvalues `z_± = p^{-(1-ρ)}, p^{-conj ρ}` | `eulerLightConePlus/Minus`, `eulerLightConePlus_eq_phase_mul`, `eulerLightConeMinus_eq_phase_mul` |
| `|z_±| < 1` inside the open strip | `norm_eulerLightConePlus_lt_one`, `norm_eulerLightConeMinus_lt_one` |
| every valuation degree is a power of one transfer | **`eulerTransfer_pow`**, `eulerTransfer_pow_entry_diagonal/offDiagonal` |
| `(5)`–`(8)` the matrix logarithm in even/odd coordinates | `eulerLogEven`, `eulerLogOdd`, **`hasSum_eulerLogEven`**, **`hasSum_eulerLogOdd`** |
| `(9)` the explicit connected-cycle series | `eulerTransfer_offDiagonal_div_eq` together with `hasSum_eulerLogOdd` |
| `(10)` `v_p = 0 ⟺ a = 0` | `eulerLightCone_eq_iff`, **`eulerLogOdd_eq_zero_iff`** |
| `(11)`–`(13)` `|v_p| ≍ p^{|a|-1/2}` | `eulerConeScale`, `eulerConeCoScale`, **`norm_eulerLogOdd_le`**, **`le_norm_eulerLogOdd`** |
| `(14)` `w_θ(p) ≍ p^{-θ}` | `gammaMeixnerWeight`, `cosh_two_log_bounds`, `gammaMeixnerWeight_le`, `le_gammaMeixnerWeight` |
| `(15)`–`(16)` the exact threshold | `eulerAntiReflectionTerm`, **`summable_eulerAntiReflectionTerm_iff`** |
| the energy vanishes identically on the critical line | `eulerAntiReflectionTerm_eq_zero` |
| `(17)` the spectral radius `p^{|a|-1/2} < 1` | `max_norm_eulerLightCone`, `max_norm_eulerLightCone_lt_one` |

Proof mechanisms:

1. **Degreewise transfer.**  `eulerTransfer = p^{-1/2+it} • B(a log p)` with the *real* boost of the
   parent card mapped into `ℂ`; `eulerTransfer_pow` is an induction using `lorentzBoost_mul`
   (rapidity additivity) and `Matrix.map_mul`.  The `(0,0)` and `(0,1)` entries of `T^m` are then
   `w^m cosh(m u)` and `w^m sinh(m u)`.
2. **The series.**  `Complex.hasSum_taylorSeries_neg_log` at `z_+` and `z_-`, added and subtracted;
   the entrywise identity `w^m sinh(mu) = (z_+^m − z_-^m)/2` comes from `z_± = w·e^{±u}`.
3. **`(10)` exactly.**  `v_p = 0` gives `log(1−z_+) = log(1−z_-)`; exponentiating (both arguments
   are nonzero because `‖z_±‖ < 1`) gives `z_+ = z_-`, and comparing moduli gives
   `p^{Re ρ − 1} = p^{−Re ρ}`, i.e. `Re ρ = 1/2`.
4. **Two-sided size of `v_p`.**  Both bounds come from the corpus's uniform Taylor estimate
   `HTGeometry.ComplexLogTaylorUniform.norm_log_one_add_sub_taylor_le'` at order two:
   `‖−log(1−z) − z‖ ≤ ‖z‖²`.  Upper: `‖v_p‖ ≤ 2X` once `X ≤ 1/2`.  Lower: writing
   `2v_p = (z_+ − z_-) + E` with `‖E‖ ≤ 2X²` and `‖z_+ − z_-‖ = X − Y` (`norm_eulerLightCone_sub`)
   gives `‖v_p‖ ≥ X/8` once `X ≤ 1/8` and `Y ≤ X/2`; both conditions hold for all but finitely
   many primes (`eventually_eulerConeScale_le`, `eventually_eulerConeCoScale_le`).
5. **The threshold.**  Comparison in both directions through `Summable.of_norm_bounded_eventually`:
   above the threshold against the corpus's log-weighted Dirichlet series
   `summable_abs_log_natCast_pow_mul_rpow_neg` restricted to primes; at or below it against
   `not_summable_one_div_primes`, using `(log p)² ≥ 16` for all but finitely many primes.

The card's final gate ("formalize only if the completed all-prime source metric uses this
logarithmic colligation") was a deferral *policy*; the theorem itself is unconditional and is now
machine-checked.  The open successor it names — the cofinal all-prime source metric or singular
Mertens-corona boundary turning the faithful odd coordinate into a uniformly finite positive trace
— is a separate statement and is untouched.
