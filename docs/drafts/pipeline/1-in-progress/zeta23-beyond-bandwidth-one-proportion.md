# Euler--Gamma horizontal-charge density at the 75% threshold

- **ID:** `euler-gamma-horizontal-charge-density-75`
- **Stage:** 1-in-progress
- **Type:** CONJECTURAL SOURCE ESTIMATE / EXACT PROVED REDUCTION
- **Source:** `claude-zeta23-rank-trace-audit.md`;
  `../2-fully-proven/not_new_scientific_knowledge/horizontal-entry-charge-transfer.md`;
  `../2-fully-proven/not_new_scientific_knowledge/euler-shift-pair-incidence-resultant.md`;
  `../3-formalized/not_new_scientific_knowledge/finite-offline-cauchy-energy-threshold-core.md`;
  `../2-fully-proven/not_new_scientific_knowledge/critical-logderivative-euler-safe-depoissonized-weil-stationarity.md`;
  external Zeta-23 paper and Lean artifact
- **Statement:** Prove unconditionally that at least `75%` of Riemann-zeta zero copies lie on the
  critical line, using a quantitative Euler--Gamma estimate that separates positive real shifts
  from diagonal multiplicity even at submicroscopic displacement.  This would improve the
  optimized Zeta-23 constant `q_A = 0.672500703679...` without finite Gabor compression.

## Goal

Let `N(T)` count nontrivial zero copies through height `T`, `N_0(T)` count critical-line copies,
and, at each positive ordinate `gamma`, let `H_gamma` be total horizontal multiplicity.  Define

```text
O(T) = sum_(0<gamma<=T) H_gamma^2
       - sum_(0<Im rho<=T) m_rho^2.
```

The first exact horizontal-incidence target is the source-side density estimate

```text
limsup_(T->infinity) O(T)/N(T) <= 1/4.                    (HC75)
```

This proves the `75%` target because every off-line zero copy belongs to a reflected pair at
the same ordinate, and that pair contributes at least its total multiplicity to `O(T)`.  Hence

```text
N(T)-N_0(T) <= O(T),
liminf N_0(T)/N(T) >= 1-limsup O(T)/N(T) >= 3/4.
```

This reduction is insensitive to how close an off-line pair is to the critical line.  It therefore
avoids the `1/log T` displacement-resolution wall that kills resolvent, slab-variance, Turan, and
smooth detector bounds.

## Gates

- [x] 0 → 1 in-progress: exact target and external comparator identified; internal and external
  frontier audit complete; corpus-native carrier and exact numerical gate identified.
- [ ] 1 → 2 fully-proven: complete unconditional paper proof, `[PAPER-PROVED]`, no open dependency.
- [ ] 2 → 3 formalized: exact theorem in Lean; targeted build, lint, and axiom gates pass.
- [ ] 3 → 4 publication-ready: standalone paper, independent proof and priority audit.

## Exact corpus carrier

For centered completed zeta `Xi`, the corpus constructs the positive intersection current

```text
J_Xi = dd^c log|Xi(c-u)| wedge dd^c log|Xi(c+u)|.
```

Twice its thin-slice mass on `Re u>0`, `Im u=0`, pushed to `Im c`, is exactly the measure `O`.
This construction uses completed-function values and Poincare--Lelong, not an enumerated zero
factorization.  The exact identity is paper-proved in
`euler-shift-pair-incidence-resultant.md`; it supplies no estimate by itself.

## Quantized anti-causal Cauchy reduction

The corpus contains a second separator stronger than every smooth displacement detector.  For a
finite positive-height window `W` of strict-right centered zeros

```text
lambda_j=a_j+i gamma_j,    0<a_j<1/2,
ell_W(t)=2 sum_j m_j exp(-(a_j+i gamma_j)t),  t>0,
E_W=integral_0^infinity |ell_W(t)|^2 dt,
```

termwise integration gives

```text
E_W=4 sum_(j,k) m_j m_k
  (a_j+a_k)/((a_j+a_k)^2+(gamma_j-gamma_k)^2).           (CE)
```

Every entry of `(CE)` is positive.  Its diagonal therefore gives

```text
E_W >= 2 sum_j m_j^2/a_j > 4 sum_j m_j^2 >= 4 R_W,
```

where `R_W=sum_j m_j` is strict-right multiplicity.  Functional-equation reflection preserves
height and multiplicity, so complete off-line multiplicity in `W` is `2R_W`.  Consequently

```text
N_off(W) < E_W/2.                                        (CR)
```

This is the requested submicroscopic separation: as `a_j->0+`, cost is not lost but diverges like
`1/a_j`; a critical-line zero has no strict-right anti-causal mode at all, regardless of its
diagonal multiplicity.  Unweighted energy is also uniquely phase-noncancelling among natural
power-weighted Hankel energies, by
`anti-causal-cauchy-trace-unique-phase-noncancellation.md`.

For dyadic `W_T=(T,2T]`, a source-defined localization satisfying

```text
E_(W_T) <= (1/2+o(1)) N(T,2T)                            (EG75)
```

would combine with `(CR)` to prove `(HC75)` and hence `N_0/N>=3/4`.  This is weaker than the
corpus's global four-unit contraction, which is RH-equivalent: `(EG75)` asks only for an average
energy budget proportional to the local zero census.

Main definition gate is source-faithful height localization.  A post-divisor cutoff merely
relabels zeros.  Required packet must arise before divisor expansion from completed Euler--Gamma
current, retain nonnegative weights on strict-right residues, exclude critical boundary divisor,
and preserve `(CE)`'s positive cross terms.

## Hostile source audit

Three tempting source transports are already closed by exact corpus theorems.

1. **Safe-offset tuning gives no slack.**  On every absolute-Euler line, the positive
   Caratheodory density and its Cauchy loss de-Poissonize to one offset-independent completed Weil
   form.  Prime weights return exactly to `-Lambda(n)/(2 sqrt(n))`.  Moving farther right only
   hides and then restores the same critical constraint.
2. **A bounded fixed-line continuation cannot carry `(CE)`.**  One pole at depth `a` has bounded
   Euler-line Hardy norm while its anti-causal residue energy grows like `1/a`.  The full
   FE--Schwarz quartet retains this blow-up.  Any valid transfer must use a source-selected
   unbounded graph or an equivalent residue coordinate.
3. **The global four-unit graph estimate is too strong.**  Corpus Ward and CCM theorems prove it
   equivalent to RH.  Reasserting that contraction does not establish the weaker density estimate
   `(EG75)`.  A legitimate advance must average the singular graph over height before taking the
   critical limit and prove only the relative `N(T,2T)/2` budget.

Thus missing knowledge is not Cauchy positivity, residue bookkeeping, or Euler-safe evaluation;
all are formalized.  It is a quantitative, height-local, source-defined incidence theorem that
survives unbounded de-Poissonization while discarding critical-line boundary multiplicity.

## Source-faithful Ward window inequality

The corpus already contains a better submicroscopic normalisation than multiplying each Cauchy
mode by a zero-dependent factor.  Write a strict-right centered zero as

```text
lambda_q = a_q + i gamma_q,     0<a_q<1/2.
```

At the Euler--Gamma probe `w=h+ic`, `h>1/2`, its Schwarz-pair Ward response is the sum of two
positive Lorentzians.  If `|gamma_q-c|<=delta`, the Lorentzian centered at `gamma_q` gives

```text
2h / ((h+1/2)^2+delta^2) <= Re r_q(h+ic).                (WQ)
```

The lower bound is uniform as `a_q->0+`: numerator `h+a_q` is bounded below by `h`, and its
denominator is bounded above by `(h+1/2)^2+delta^2`.  A critical-line zero supplies no
strict-right Ward mode at all, independent of multiplicity.  Thus `(WQ)` separates every positive
horizontal shift from the diagonal boundary at arbitrarily small displacement without an
inverse-`a_q` blow-up.

Let `S` be any finite set of multiplicity copies of strict-right upper zeros in that height
window.  Positivity of every Schwarz-pair response and absolute convergence of their sum give

```text
card(S) * 2h / ((h+1/2)^2+delta^2)
  <= sum_(q in S) Re r_q(h+ic)
  <= Re r(h+ic).
```

Functional-equation reflection absorbs both the complementary divisor term and the complete
Ward boundary self-symbol.  The existing source identity therefore proves the unconditional
Euler--Gamma estimate

```text
card(S) * 2h / ((h+1/2)^2+delta^2) <= B_EG(h,c),          (EGW)

B_EG(h,c)
 = 2 Re[ 1/s + 1/(s-1) + (Gamma_R'/Gamma_R)(s)
         - sum_(n>=2) Lambda(n)n^(-s) ],
s=h+1/2+ic,   Re s>1.
```

Every term on the right is in the absolute Euler region.  No zero location, line multiplicity,
RH premise, or post-divisor scalar normalisation occurs in `B_EG`.  Paper proof is exactly the
three displayed inequalities: the already-proved per-pair Lorentzian bound, finite-sum
monotonicity inside the nonnegative absolutely convergent Ward series, and the already-proved
source-only Ward majorant.

Lean formalization is complete in
`formal/GaloisForLFunctions/RHTower/XiWardSourceWindowMultiplicity.lean`; targeted build and axiom
audit pass.  Formal card:
`../3-formalized/not_new_scientific_knowledge/euler-gamma-ward-window-multiplicity-bound.md`.

This closes the requested *local separator* but not `(HC75)`.  Stirling gives
`B_EG(h,c)~log(|c|/(2pi))`; summing first-moment windows through a dyadic interval therefore has
the same `T log T` order and leading scale as the full zero census.  The raw Ward first moment
cannot supply the missing factor `1/8` for strict-right multiplicity.  A 75% proof still needs a
centered quadratic/correlation estimate, or an index estimate, which removes the universal Gamma
baseline before summation.

### Exact localized quadratic gate

The edge Gram corpus fixes the constant required from that correlation estimate.  Put
`x_q=a_q+1/2 in (1/2,1)`.  On the Euler edge the real part of one Schwarz-pair response is

```text
f_q(t) = 2x_q/(x_q^2+(t+gamma_q)^2)
       + 2x_q/(x_q^2+(t-gamma_q)^2) >= 0.
```

For `1<L<T/2`, let

```text
U_(T,L)=[-2T-L,-T+L] union [T-L,2T+L].
```

If `F_T` is any finite set of strict-right multiplicity copies with `T<gamma_q<=2T`, positivity
before squaring and the two length-`2L` neighborhoods of `+-gamma_q` give

```text
(4pi-16/(3L^3)) card(F_T)
  <= integral_(U_(T,L)) (Re r(1/2+it))^2 dt.             (WQL)
```

Indeed, each centered Lorentzian square has full mass `2pi/x_q`; its two tails beyond `L` have
mass at most `8/(3L^3)`.  There are two centers, and `(sum f_q)^2>=sum f_q^2`.  This is uniform as
`a_q->0+`, uses multiplicity copies, and never charges a critical-line zero.

Let `L=L(T)->infinity` with `L(T)=o(T)`.  If the completed Euler--Gamma source supplied

```text
integral_(U_(T,L(T))) (Re r(1/2+it))^2 dt
  <= (pi/2+o(1)) N(T,2T),                               (EGQ75)
```

then `(WQL)` would give `R(T,2T)<=N(T,2T)/8+o(N)`.  Since positive-height off-line multiplicity is
`2R(T,2T)`, this is exactly `N_off(T,2T)<=N(T,2T)/4+o(N)`, hence the `75%` target.  The reliable
localized deposit is `4pi` per right-upper copy, so the source threshold is `pi/2`; `pi/4` would
be unnecessarily twice as strong.

Corpus audit finds no proof of `(EGQ75)`.  `XiWardEdgeImChannelGram.lean` evaluates the quadratic
energy as a positive zero-pair Gram sum, not as Euler--Gamma data.  The source absorption in
`XiWardInteriorReflectionAbsorption.lean` is linear; squaring its uncentered `O(log T)` majorant
only gives `O(T log^2 T)`.  A valid proof must expose cancellation of the Gamma census baseline
through a centered prime--Gamma two-point identity.  The existing moire/Ward audit locates the
same obstruction as the subtraction defect between the full prime trace and the critical-line
spectral trace; bypassing it would amount to assuming the missing correlation.

### Two rejected false shortcuts

1. The exact co-Poisson critical flux `integral_0^X t|P(t)|^2 dt~(1/4)log X` is a dilation-tail
   law, not a height census.  Its multiplier ideal is proved dense and erases divisor classes;
   the matching constant `1/4` has no proved map to the `T log T` zero scale.
2. Normalising a Cauchy mode by `sqrt(2a_q)` makes its self-Gram exactly one and preserves positive
   cross terms, but it is zero-dependent.  It is not produced by the holomorphic Euler--Gamma
   source: a nonvanishing holomorphic scalar `H` with `|H(z)|^2=2 Re z` would make
   `log|H(z)|=(1/2)log(2 Re z)` harmonic, whereas its Laplacian is
   `-1/(2(Re z)^2)`.  The Ward Lorentzian normalisation avoids this defect.

## Horizontal-current alternative

Replace the discontinuous thin slice by a positive microscopic majorant.  For a nonnegative
dyadic height window `w_T` and a nonnegative smooth `kappa` with `kappa(0)=1`, define

```text
O_(T,eta) = 2 integral w_T(Im c) 1_(Re u>0)
              kappa(Im u log(T)/eta) dJ_Xi(c,u).
```

Every same-ordinate reflection atom occurs with full weight, so `O(T,2T) <= O_(T,eta)` up to the
chosen endpoint convention.  The missing theorem is to prove, directly from the completed
Euler--Gamma source, for one explicit `(w,kappa,eta)`,

```text
limsup O_(T,eta)/N(T,2T) <= 1/4.                         (HC)
```

Poincare--Lelong and two integrations by parts turn `(HC)` into a smoothed two-point correlation
of `log|Xi(c-u)|` and `log|Xi(c+u)|`.  Candidate infrastructure is the corpus's full rectangular
Guinand--Weil formula, Selberg prime-square pairing, and completed prime--Gamma cross-kernel.
What must be added is the quantitative nonlinear correlation estimate and all boundary control;
none is presently proved.

The cutoff in `Re u` cannot be harmlessly smoothed.  A continuous cutoff vanishing at `u=0`
misses off-line pairs with arbitrarily small displacement, while one nonzero at `u=0` also charges
the diagonal multiplicity current.  Thus `(HC)` must retain the open-stratum boundary term or
subtract its diagonal contribution by a separately proved source identity.  This discontinuous
separation is the main hostile gate, not a technicality.

This is mathematically different from Zeta-23: it charges the off-line reflection incidence
directly and uses no finite critical-density Gabor system, Gram trace/Frobenius comparison, or
rank--trace multiplicity inequality.  A proof may still encounter an equivalent pair-correlation
barrier; different packaging is not counted as progress.

## Active labels

- `[LITERATURE]` Zeta-23 proves the optimized unconditional constant
  `q_A = 0.672500703679...` and formalizes it without nonstandard axioms.
- `[PAPER-PROVED REDUCTION]` `N-N_0 <= O`; `(HC)` with constant `1/4` proves `75%`.
- `[PAPER-PROVED REDUCTION]` Anti-causal packet satisfies `N_off(W)<E_W/2`; `(EG75)` proves
  `75%` and strengthens as horizontal displacement tends to zero.
- `[PAPER-PROVED SOURCE ESTIMATE]` `(EGW)` bounds any finite multiplicity-exact strict-right
  height-window packet by an explicit absolutely convergent Euler--Gamma quantity, uniformly for
  arbitrarily small positive horizontal displacement and with critical-line multiplicity absent.
- `[PAPER-PROVED QUADRATIC REDUCTION]` `(WQL)` gives a uniform localized `4pi` real-channel
  deposit per right-upper copy; `(EGQ75)` with source constant `pi/2` proves `75%`.
- `[PAPER-PROVED CARRIER]` The positive-real thin slice of `J_Xi` equals `O` exactly.
- `[OPEN CORE]` Construct source-faithful dyadic anti-causal localization and prove `(EG75)`, or
  prove centered prime--Gamma correlation `(EGQ75)`; equivalently prove `(HC)` with constant
  `1/4` by a source-defined current estimate.

## No-go closure (mandatory when falsified)

- **Resolved dead alternatives:**
  1. resolvent mass and Turan bounds weight high zeros too weakly;
  2. slab variance and bounded displacement energies lose uniform force as a pair approaches the
     line; unweighted anti-causal Cauchy energy has correct inverse-displacement force but no
     proved height-averaged source upper bound;
  3. de Bruijn--Newman flow is monotone toward the line and gives upper extinction-time bounds;
  4. the `0.86864` Zeta-23 result for zeros of `Xi'` does not transfer back to zeros of `Xi`:
     Rolle and Gauss--Lucas point in the wrong direction, while the corpus's Hedenmalm census
     collision premise is RH-bearing;
  5. a lower bound for distinct zero locations does not bound distinct ordinates: simple off-line
     reflected pairs may make every zero location distinct;
  6. smoothing the positive-real-shift indicator either loses submicroscopic off-line pairs or
     imports the collision-conserved diagonal multiplicity charge.
- **Strongest positive survivor:** anti-causal Euler--Gamma density estimate `(EG75)`, with `(HC)`
  as current-theoretic alternative.
- **New insight:** the corpus's absolute `<2` horizontal-charge target is unnecessarily strong for
  this problem.  Relative constant `1/4` suffices, and anti-causal energy supplies a singular
  submicroscopic separator unavailable to bounded smooth detectors.
- **Status:** exact `75%` reductions paper-proved; missing source estimate remains open; no Lean
  headline theorem or density improvement claimed.

## Log

- 2026-08-12 — created in Stage 1 for exact Zeta-23 constant-improvement target.
- 2026-08-12 — scope corrected after user requested a genuinely corpus-native mechanism rather
  than a higher-bandwidth refinement of Zeta-23.  Horizontal charge selected as sole survivor;
  exact threshold and source-current target recorded.
- 2026-08-12 — target raised to `75%`.  Added anti-causal Cauchy reduction `(CE)`--`(EG75)`, which
  separates strict positive shifts from arbitrary critical-line multiplicity at submicroscopic
  displacement.  Global four-unit transport rejected as an RH-equivalent restatement; only a
  height-averaged source incidence can count as progress.
- 2026-08-13 — proved `(EGW)` on paper: finite strict-right window multiplicity is bounded by the
  explicit absolute-Euler Ward source at one interior probe, uniformly down to submicroscopic
  horizontal displacement and with line multiplicity absent.  Constant audit shows its raw first
  moment is census-scale but does not by itself yield `75%`; co-Poisson `1/4` and zero-normalised
  Cauchy shortcuts rejected.
- 2026-08-13 — audited the complete edge Gram stack and corrected the localized quadratic
  constant: `(WQL)` deposits `4pi-o(1)` per right-upper copy, so the exact `75%` source gate is
  `(EGQ75)` with `pi/2+o(1)`.  Existing quadratic formulas are zero-side; no centered prime--Gamma
  source upper bound is present.
