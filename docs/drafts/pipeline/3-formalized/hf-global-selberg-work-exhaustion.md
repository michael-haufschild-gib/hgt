# HF: global Selberg work and transverse energy

- **ID:** hf-global-selberg-work-exhaustion
- **Stage:** 3-formalized
- **Type:** THEOREM; unconditional paper proof and Lean formalization
- **Parent goal:** unconditional Lean closure of HF, unchanged.
- **Frontier input:** the source field is now identified at every Xi zero; full source
  sign and an upper bound on transverse energy remain open.

## Exact target

Use actual multiplicity copies. Write `p = 1/2 + a_p + i t_p`,
`K(p,q) = (a_p-a_q)/|p-q|²`, and `F(p) = xiSourceField p`.
For `R ≥ 4`, use rational height damping

    w_R(t) = R⁴/(R²+t²)²,
    c_N(t) = max(0, 1-|t|/(N+1)).

Prove that the finite arithmetic source works

    W(R,N) = Σ_{|t_p|≤N+1} a_p w_R(t_p)c_N(t_p) F(p)

have finite nonnegative limits `W_R`. Then prove

    lim_{R→∞} ofReal(W_R)
      = (1/2) Σ_{p,q} ofReal((a_p-a_q)²/|p-q|²) ∈ [0,∞].

This is the multiplicity-weighted transverse energy, not the unit-charge energy
already defined in AES. Do not silently identify those two energies. No finite
off-line-support or simplicity premise is allowed. No RH criterion is needed.

## Proposed mechanism

Pair critical-line reflections before taking the infinite sum. For two zero
copies put `x=a-b`, `y=a+b`, `d=t-u`, and

    E = x²/(x²+d²) + y²/(y²+d²),
    C = xy(1/(x²+d²) + 1/(y²+d²)).

For height weights `v(t),v(u)`, the reflection-paired work kernel is

    J_v = ((v(t)+v(u)) E + (v(t)-v(u)) C)/2.

The source work equals `(1/4) Σ_{p,q} J_v`. At `v=1`, this equals
`(1/2) Σ_{p,q} (a_p-a_q)²/|p-q|²` by reflection invariance.

## Paper proof

1. Strip geometry gives `x²+y²≤1`. If `|d|≤1`, then `|d C|≤2E`.
   If `|d|≥1`, then `|C|≤E`. At `d=0`, every height weight agrees at
   the two points, so the term involving `C` vanishes, including coincident fibres.
2. Rational damping satisfies
   `|w_R(t)-w_R(u)|≤|t-u|(w_R(t)+w_R(u))/R`.
   Set `A=R²+t²`, `B=R²+u²`; use
   `R|t+u|(A+B)≤A²+B²`. Consequently `0≤J_(w_R)≤(w_R(t)+w_R(u))E`.
3. The tapers lie in `[0,1]`, tend pointwise to one and have Lipschitz
   constant at most one. Thus
   `|J_(w_R c_N)|≤2(w_R(t)+w_R(u))E`, uniformly in `N`.
4. Let `S=Σ_q 1/t_q²<∞`, already proved for actual Xi copies. The angular
   row is bounded by `((2|t_p|+1)²+4)S`: split at `|t_q|=2|t_p|+1`.
   On the near part use the unit bound and `1≤(2|t_p|+1)²/t_q²`;
   on the far part use `|t_p-t_q|≥|t_q|/2` and `|a_p-a_q|≤1`.
   Moreover
   `w_R(t)((2|t|+1)²+4)≤13R⁴/t²` for `R≥1`, `t≠0`.
   These bounds give an absolutely summable product majorant for the paired kernels.
5. Every tapered source work is a finite sum of absolutely convergent field rows.
   Symmetrize and reflect these rows, then use the product majorant and dominated
   convergence. This proves the inner limit without any zero-separation estimate.
6. As `R→∞`, `J_(w_R)→E` pointwise, `J_(w_R)≥0`, and `J_(w_R)≤2E`.
   Fatou proves divergence to `∞` when the total energy is infinite; dominated
   convergence proves the finite case. This supplies the full extended-real limit.

The algebra in step 1 is justified as follows. Put `h=1/(x²+d²)` and
`k=1/(y²+d²)`, and `B=y²h+x²k`. Then

    EB-C² = hk(x²-y²)² ≥ 0,
    (d²+x²+y²)E-d²B = 2hk x²y²(2d²+x²+y²) ≥ 0.

For `d≠0` these follow by clearing the positive denominators; for `d=0`
the desired near estimate is immediate. They give
`d²C²≤(d²+x²+y²)E²≤2E²`, hence `|dC|≤2E`.
On the far part use

    E-C = (x-y)²(d²-xy)/((x²+d²)(y²+d²)),
    E+C = (x+y)²(d²+xy)/((x²+d²)(y²+d²)).

Both are nonnegative since `|xy|≤(x²+y²)/2≤1/2≤d²`.

For step 2, `2R|t+u|≤2R(|t|+|u|)≤A+B`, by the two
squares `(R-|t|)²,(R-|u|)²`. Also `(A+B)²≤2(A²+B²)`.
Factoring `A²-B²=(t-u)(t+u)(A+B)` proves the weight estimate.
The near estimate gives
`|(w_R(t)-w_R(u))C|≤(2/R)(w_R(t)+w_R(u))E`; the far estimate
uses `|w_R(t)-w_R(u)|≤w_R(t)+w_R(u)`. These prove step 2.

For step 3, the elementary product difference and the taper's Lipschitz law give
`|w_R(t)c_N(t)-w_R(u)c_N(u)|≤(1+1/R)|d|(w_R(t)+w_R(u))`.
Since `R≥4`, the near bound on the absolute paired work is at most
`(7/4)(w_R(t)+w_R(u))E`, below the stated majorant. The far bound is
at most `(w_R(t)+w_R(u))E`.

The majorant in step 4 can also be taken pointwise on the product of zero copies:
`w_R(t_p) angular(p,q)≤13R⁴/(t_p² t_q²)`. Apply the same estimate
after swapping and reflecting the two indices. Thus the full paired majorant
is bounded by a fixed multiple of the product of the two known summable
inverse-square ordinate sequences. This validates every sum interchange and
the dominated-convergence argument in step 5. At finite cutoff, the original
source rows are absolutely summable because there are finitely many nonzero
rows, each already absolutely summable. No pointwise bound on the regular part
or on zero separation is assumed.

An algebraically simpler version of step 4, used in Lean, is

    angular(x,t-u) ≤ 2(1+t²)/(1+u²),  x²≤1.

For nonzero angular denominator, clear the two positive denominators and use
`u²≤2t²+2(t-u)²` and `x²≤1`; the difference is bounded below by
`x²+2(t-u)²(1+t²-x²)≥0`. At zero denominator the angular term is zero.
For `R≥1`, `w_R(t)≤R⁴/(1+t²)²`, hence

    w_R(t) angular(x,t-u) ≤ 2R⁴/((1+t²)(1+u²)).

The sequence `1/(1+t_p²)` is summable by comparison with the known inverse
square ordinate sequence. Reflection and swapping now give a product majorant
`8R⁴/((1+t_p²)(1+t_q²))` for `(w_p+w_q)E`, uniformly also at small heights.
This proves the same global target without the near/far height split in step 4.

In step 6 take `R=n+4`. When total energy is finite, use the majorant `2E`.
When it is infinite, any finite set of pairs has arbitrarily large total
energy; pointwise convergence on that finite set and nonnegativity of all
paired kernels force `W_R` eventually above every finite real bound. This is
the extended-real limit and does not require interchange of divergent signed sums.

## Lean theorem and audit

Files under `formal/GaloisForLFunctions/ArithmeticElectrostatics/`:

- `ReflectedTransverseWork.lean`: near/far mixed-term estimates, rational relative
  variation, nonnegative damped work, uniform compact-taper bound, and the
  inverse-quadratic product majorant, including all coincidence cases.
- `TheSelbergWorkExhaustsTheTransverseEnergy.lean`: actual copied divisor and
  arithmetic Laurent-residue source; absolute summability before reindexing;
  complete finite-source identity; both limits, including infinite energy.

Exact declarations in `GaloisForLFunctions.ArithmeticElectrostatics`:

- `xiTaperedSourceWork_eq_paired_tsum`: every compact arithmetic source work
  equals one quarter of the reflected pair sum, with exterior rows retained.
- `xiDampedSourceWork_nonneg`: damped work is nonnegative for every `R≥4`.
- `xiTaperedSourceWork_tendsto`: the inner compact-cutoff limit equals this
  finite damped work.
- `xiCopyTransverseEnergy_eq_half_tsum`: the energy is exactly half the ordered
  geometric pair sum over analytic multiplicity copies.
- `xiDampedSourceWork_tendsto_energy`: `ofReal(W_(n+4))` converges to this full
  extended energy without finite off-line support, simple-zero, separation,
  ordinary undamped-work summability, or source-sign assumptions.

The full application file passed the exact foreground check
`lake --old env lean GaloisForLFunctions/ArithmeticElectrostatics/TheSelbergWorkExhaustsTheTransverseEnergy.lean`.
The three source identity/limit audits report only `propext`, `Classical.choice`,
and `Quot.sound`. No placeholders, new axioms, trusted-computation shortcuts, or
limit increases were used. Both leaves are imported by the AES umbrella; the
umbrella is not compiled. Only the two genuinely missing import dependencies
(`ReflectedTransverseWork`, `EveryXiZeroHasASourceField`) had oleans written.

## Relation to the closing obstacle

This theorem supplies a global exhaustion from arithmetic Laurent residues to
energy. It supplies a source formula, not the required arithmetic upper bound.
The closing task remains controlling
the actual `W_R` above by a sub-unit bound or proving the full Weil sign.
No external search, novelty audit, numerical experiment or new RH criterion.

## Significance and next conjecture loop

Verdict: **BRIDGE**, not closure of HF. The new corpus result is the complete
multiplicity-exact two-stage source-work/energy identity, valid even with
infinite energy. It does not assert convergence of the ordinary undamped signed
source series. No external novelty claim is made: the user explicitly excluded
external search and novelty audits.

The mathematical gain is removal of the global source-exhaustion gap. The hard
gap is unchanged in type: prove an actual arithmetic upper estimate on these
source works that beats the off-line reserve, or prove full Weil positivity.
The next cycle must attack that upper estimate directly. More characterizations,
zero-side lower bounds, and finite-dimensional virial identities do not close it.

Anti-theatre/anti-laziness audit: a substantive source theorem is now proved and
formalized, but no HF sign premise was discharged. The corpus was searched for
existing source, reflection, and convergence machinery; no difficulty-based
downscoping was used. The parent goal remains active and unresolved.

## Log

- 2026-10-27 — revalidated the preceding all-zero source-field theorem; researched
  current source work, reflection, renormalization and height-exhaustion machinery.
- 2026-10-27 — exponential damping led to a good-height boundary argument;
  replaced it by rational damping and compact Lipschitz tapers, which permit
  absolute pairwise domination and avoid zero-separation assumptions.
- 2026-10-27 — completed both limits and the actual arithmetic-source identity;
  full application check and dependency audits passed.
