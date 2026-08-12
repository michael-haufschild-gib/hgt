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
- `[PAPER-PROVED CARRIER]` The positive-real thin slice of `J_Xi` equals `O` exactly.
- `[OPEN CORE]` Construct source-faithful dyadic anti-causal localization and prove `(EG75)`, or
  prove `(HC)` directly from completed Euler--Gamma source with constant `1/4`.

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
