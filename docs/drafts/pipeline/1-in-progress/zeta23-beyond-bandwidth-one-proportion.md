# Horizontal-charge density beyond Zeta-23

- **ID:** `horizontal-charge-density-beyond-zeta23`
- **Stage:** 1-in-progress
- **Type:** CONJECTURAL SOURCE ESTIMATE / EXACT PROVED REDUCTION
- **Source:** `claude-zeta23-rank-trace-audit.md`;
  `../2-fully-proven/not_new_scientific_knowledge/horizontal-entry-charge-transfer.md`;
  `../2-fully-proven/not_new_scientific_knowledge/euler-shift-pair-incidence-resultant.md`;
  external Zeta-23 paper and Lean artifact
- **Statement:** Prove unconditionally that the lower density of Riemann-zeta zeros on the
  critical line is strictly greater than the optimized Zeta-23 constant
  `q_A = 0.672500703679...`, using the positive-real-shift horizontal-incidence current rather
  than finite Gabor compression and rank--trace.

## Goal

Let `N(T)` count nontrivial zero copies through height `T`, `N_0(T)` count critical-line copies,
and, at each positive ordinate `gamma`, let `H_gamma` be total horizontal multiplicity.  Define

```text
O(T) = sum_(0<gamma<=T) H_gamma^2
       - sum_(0<Im rho<=T) m_rho^2.
```

The first exact target is a source-side density estimate

```text
limsup_(T->infinity) O(T)/N(T) < theta_A,
theta_A = 1-q_A = 0.327499296320588354...
```

This is enough to beat Zeta-23 because every off-line zero copy belongs to a reflected pair at
the same ordinate, and that pair contributes at least its total multiplicity to `O(T)`.  Hence

```text
N(T)-N_0(T) <= O(T),
liminf N_0(T)/N(T) >= 1-limsup O(T)/N(T) > q_A.
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

## Proposed analytic addition

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
limsup O_(T,eta)/N(T,2T) < theta_A.                       (HC)
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
- `[PAPER-PROVED REDUCTION]` `N-N_0 <= O`; `(HC)` with constant below `theta_A` beats Zeta-23.
- `[PAPER-PROVED CARRIER]` The positive-real thin slice of `J_Xi` equals `O` exactly.
- `[OPEN CORE]` Prove `(HC)` from the completed Euler--Gamma source with an explicit certified
  constant below `0.327499296320588354...`.

## No-go closure (mandatory when falsified)

- **Resolved dead alternatives:**
  1. resolvent mass and Turan bounds weight high zeros too weakly;
  2. slab variance and Cauchy displacement energies have no source upper bound and lose uniform
     force as a pair approaches the line;
  3. de Bruijn--Newman flow is monotone toward the line and gives upper extinction-time bounds;
  4. the `0.86864` Zeta-23 result for zeros of `Xi'` does not transfer back to zeros of `Xi`:
     Rolle and Gauss--Lucas point in the wrong direction, while the corpus's Hedenmalm census
     collision premise is RH-bearing;
  5. a lower bound for distinct zero locations does not bound distinct ordinates: simple off-line
     reflected pairs may make every zero location distinct;
  6. smoothing the positive-real-shift indicator either loses submicroscopic off-line pairs or
     imports the collision-conserved diagonal multiplicity charge.
- **Strongest positive survivor:** horizontal-incidence density estimate `(HC)`.
- **New insight:** the corpus's absolute `<2` horizontal-charge target is unnecessarily strong for
  this problem.  A relative estimate below `theta_A N(T)` suffices and is compatible with smoothing
  at microscopic ordinate scale.
- **Status:** no unconditional improvement proved; no Lean headline theorem claimed.

## Log

- 2026-08-12 — created in Stage 1 for exact Zeta-23 constant-improvement target.
- 2026-08-12 — scope corrected after user requested a genuinely corpus-native mechanism rather
  than a higher-bandwidth refinement of Zeta-23.  Horizontal charge selected as sole survivor;
  exact threshold and source-current target recorded.
