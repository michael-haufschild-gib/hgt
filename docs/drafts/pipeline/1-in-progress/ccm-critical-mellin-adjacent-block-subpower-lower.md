# Subpower lower control of one critical-Mellin adjacent-block imbalance closes RH

- **ID:** `ccm-critical-mellin-adjacent-block-subpower-lower`
- **Stage:** 1-in-progress
- **Type:** `[CONJECTURE]` / SOURCE PRODUCER FOR A FORMAL RH GATE
- **Scientific status:** `[CONJECTURE] [RH-EQUIVALENT] [TOP-DOWN TARGET]`
- **Statement:** For one fixed `L>0`, prove that the completed prime--polar adjacent-block imbalance
  is bounded below by `-C_epsilon n^epsilon` for every `epsilon>0`.

## Goal

Let

```text
R(h)=4sinh(h/2)-sum_(q<=exp(h)) Lambda(q)q^(-1/2)
```

and define the fixed-scale Haar coefficient

```text
I_L(n)
 = integral_[log n-L,log n] R(h)dh
   - integral_[log n-2L,log n-L] R(h)dh.
```

The target is

```text
for every epsilon>0,
  exists C_epsilon>=0 and N_epsilon such that
  I_L(n) >= -C_epsilon n^epsilon for all n>=N_epsilon.    (1)
```

The formalized completed-error reduction in
`../3-formalized/not_new_scientific_knowledge/ccm-completed-critical-mellin-chebyshev-potential-law.md`
rewrites the integrand exactly as

```text
R(h)
 =1-2/sqrt(exp(h))-E(exp(h))/sqrt(exp(h))
  -(1/2) integral_[1,exp(h)] E(t)t^(-3/2)dt,

E(X)=psi(X)-X.                                            (2)
```

Thus `(1)` is now literally a one-sided subpower lower problem for one fixed Haar coefficient of
the normalized Chebyshev potential `(2)`.  The polar and von Mangoldt square-root main terms have
already cancelled in Lean; they are not separate remaining estimates.

Writing

```text
e(h)=E(exp(h))/sqrt(exp(h)),
```

the same formal theorem gives the local causal form

```text
R(h)=1-2exp(-h/2)-e(h)-(1/2)integral_[0,h]e(u)du.          (3)
```

The open inequality is therefore exactly a fixed Volterra--Haar value constraint on `e`; no
Gamma value, polar main term, or unsmoothed prime sum remains in the unresolved scalar.

The formalized mode law in
`../3-formalized/not_new_scientific_knowledge/ccm-critical-mellin-volterra-haar-mode-faithfulness.md`
computes the transfer multiplier

```text
M_L(w)=-(2w+1)(1-exp(-Lw))^2/(2w^2)                       (4)
```

and proves `M_L(w)!=0` whenever `L>0` and `Re(w)>0`.  Hence the fixed Volterra--Haar filter
faithfully retains every positive-growth exponential mode.  The remaining theorem must constrain
the normalized Chebyshev input itself; filter censorship is excluded.

The paper-proved rectangular critical-Mellin law identifies the actual fixed-width Weil value with
`2 I_L(n)` plus a fixed term and an `n`-uniformly bounded Gamma term. The Lean theorem
`riemannHypothesis_of_xiRectangularWeilTailSubpowerLower` therefore turns `(1)` into RH.

## Why this is weaker than the previous open core

The previous source obligation asked for one finite constant floor

```text
I_L(n) >= -C.
```

Condition `(1)` permits `I_L(n)` to tend to minus infinity. It excludes only negative excursions
of a fixed positive power size. No positivity, monotonicity, norm bound, or limiting positive
measure is required.

Under false RH, the formal power-corrected Landau theorem selects the hidden transverse exponent
`delta_*>0`, sets `alpha=delta_*/4`, and proves that a lower bound of order `n^alpha` is already
impossible. Since `(1)` supplies that bound for every positive exponent, it closes RH without
placing `delta_*` in the source statement.

## Required research

Prove a one-sided cancellation theorem for the completed prime--polar Haar coefficient. Viable
forms include:

1. a positive covariance or conditional-negative-type representation whose boundary loss is
   `O_epsilon(n^epsilon)`;
2. a coupled renewal or Möbius projection retaining the prime and polar channels before
   scalarization, with subpower control of the escaping boundary shell;
3. a Perron/Mellin contour representation in which every residue to the right of the critical
   boundary contributes with the opposite sign to `(1)`, so a source-side zero-free deformation
   gives the lower estimate;
4. an all-prime Gamma-completed norm-square identity with a one-sided subpower boundary term.

The proof must be formulated directly from the von Mangoldt and Gamma data. It may not assume Xi
zero locations, real-rootedness, anti-Herglotz positivity, the rectangular Weil lower bound, or an
RH-equivalent limiting measure.

The pointwise target is no longer the weakest available source obligation.  The formalized sharp
positive-excess gate shows that it is enough to prove, for

```text
E(n)=(W(n)-2(1-1/sqrt(2))*sqrt(n))_+,
```

either `sum E(n)/n^(1+epsilon)<infinity` or
`sum E(n)^2/n^(1+epsilon)<infinity` for every `epsilon>0`.  These conditions retain only the
unfavorable overshoots and permit sparse pointwise failures.  Any covariance or norm-square attack
should therefore target this weighted energy before attempting the stronger uniform estimate.

## Attacks and exclusions

1. `[REJECTED]` Applying absolute values separately to the polar and prime terms loses their
   square-root-scale cancellation. Classical coarse PNT bounds leave an error much larger than
   `n^epsilon` for small `epsilon`.
2. `[REJECTED]` Finite-prime or finite-jet control cannot provide `(1)`: the corpus proves finite
   divisor and finite Cauchy-jet blindness.
3. `[REJECTED]` Hypertranscendence, Gamma shift elimination, and finite Cholesky positivity do not
   orient this coefficient. The constraint and orientation axes vary independently.
4. `[LIVE]` Use the zero-mean Haar structure to localize the source loss to the moving boundary
   shell, then prove that shell is one-sided subpower after completed prime--Gamma coupling.
5. `[LIVE]` Replace a constant-boundary norm-square law by a subpower boundary law; the new Lean
   gate shows that no uniform remainder is necessary.
6. `[REJECTED]` Cofinal-order scalar extrapolation from positive shifts does not cross the half-unit
   seam at subpower cost.  The theorem
   `../2-fully-proven/not_new_scientific_knowledge/ccm-half-unit-linear-extrapolation-cost-law.md`
   proves that any linear combination reproducing the half-unit atom at aperture `n` has
   coefficient `l1` mass at least `n^(1/2)`, regardless of the number or placement of shifts.
7. `[LIVE, POSITIVE DUAL]` Allow cofinal order only inside a non-diagonal source covariance,
   determinant, relative trace, or compressed graph which retains the prime--polar coupling and
   cancels the half-unit atom before scalar absolute values are taken.  The permitted residual
   boundary loss remains `n^o(1)`.
8. `[PROVED, POSITIVE FILTER LAW]` The exact Volterra--Haar multiplier `(4)` is nonzero throughout
   the open right half-plane.  Every positive-growth mode is visible, so fixed-window linear
   filtering loses none of the RH-bearing exponent.
9. `[LIVE, WEAKER ENERGY TARGET]` Prove weighted `l1` or `l2` Dirichlet energy of only the positive
   sharp-window excess.  The exact negative-part correction makes the coefficients nonnegative,
   and the formal Landau gate turns either energy estimate directly into RH.
10. `[LIVE, SPARSE-EXCEPTION TARGET]` Split apertures into a regular set with pointwise subpower
    control and an exceptional set carrying finite positive-excess Dirichlet energy.  The two
    estimates may be combined without controlling either channel globally.
11. `[PROVED, HALF-POWER EXCEPTION ENVELOPE]` Chebyshev's unconditional bound controls the positive
    excess by `sqrt(2)*(log 4+4)*sqrt(n)`.  Thus an exceptional set may be specified before seeing
    any prime values: it is enough that `sum_(n in E)n^(-1/2-epsilon)` converge for every positive
    `epsilon`, while the pointwise target is proved only on `E^c`.
12. `[PROVED, APERTURE-RESOLVENT PHASE COLLAPSE]` Exponentially average the exact CCM aperture
    multiplier.  At unit rate,
    `integral_0^infinity exp(-L)M_L(w)dL=-1/(w+1)`, with strictly negative real part throughout
    `Re(w)>0`.  In time domain the aperture kernel cancels the completed-error Volterra memory and
    leaves the positive causal kernel `exp(-t)`.  The surviving source scalar is exactly
    `X^(-1) integral_0^X (psi(y)-y)y^(-1/2)dy`.  Admissible truncation `L<=log(X)/2` changes every
    possible off-critical mode only by an exponentially decaying tail.  Filter phase and aperture
    censorship are therefore closed; source-sector sign is not.
13. `[LIVE, EXACT CONNES SOURCE FRONTIER]` Prove the one-sided all-epsilon subpower upper bound for
    the aperture-resolvent Riesz mean and prove its one-sided Landau connector to RH.  This is
    `ccm-aperture-resolvent-riesz-sector.md`; it replaces further fixed-window filter work.

## Formal endpoint

The complete formal chain is in
`GaloisForLFunctions.RHTower.CCMRectangularSubpowerLowerGate`:

```text
source inequality (1)
  -> XiRectangularWeilTailSubpowerLower L N
  -> riemannHypothesis_of_xiRectangularWeilTailSubpowerLower
  -> RiemannHypothesis.
```

The only paper-to-Lean bridge still missing in this displayed chain is the already paper-proved
Stieltjes/autocorrelation identity from `I_L(n)` to the actual rectangular Weil value.  The source
quantity `I_L(n)` itself and its exact Chebyshev-potential form are now formalized without a `Prop`
interface.

## Gates

- [x] exact source scalar isolated
- [x] weaker one-sided subpower endpoint proved sufficient in Lean
- [x] bounded Gamma term shown harmless on paper
- [x] square-root polar/prime cancellation reduced in Lean to the normalized Chebyshev potential
- [x] causal Volterra--Haar transfer multiplier computed and proved right-half-plane faithful
- [x] exponential aperture average computed; unit rate collapses to an oriented resolvent
- [x] causal Volterra memory and legal-aperture tail shown not to censor positive-growth modes
- [x] pointwise target weakened to positive-excess Dirichlet energy and square energy in Lean
- [ ] prove `(1)` unconditionally from the completed source
- [ ] prove aperture-resolvent Riesz-sector source bound and one-sided Landau connector
- [ ] formalize the critical-Mellin Stieltjes/autocorrelation identity
- [ ] compose to RH

## Log

- 2026-07-12 — Replaced the constant adjacent-block floor by the weaker all-epsilon subpower lower
  target after formalizing the power-corrected Landau gate.
