# SC rigged-prime determinant collapse and regularization-order obstruction

- **ID:** SC-RP-DET-COLLAPSE
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `rh-current-frontier-map.md` · SC remaining coefficient-faithful Xi landing/determinant
- **Statement:** Ordinary SC rigged-prime Gram determinants collapse cofinally to zero, their wall-vanishing order grows exactly with packet cardinality, every fixed finite pole-order renormalization still collapses for all sufficiently large packets, and no horizontal-only scalar normalization can equal normalized Xi.

## Goal
Decide the missing SC determinant arrow at structural level. Either construct a source-derived
coefficient-faithful Xi determinant, or prove the exact regularization class that cannot carry one
and isolate the minimal surviving singular renormalization datum. No numerical constant or bound
optimization is in scope.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean module and exact leaf `lake build` green; approved-axiom report PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Door passport
- **Route:** SC, source-horizontal rigged Krein prime form.
- **Exact open arrow:** source-derived infinite prime assembly → coefficient-faithful Xi determinant.
- **Permitted inputs:** `sourceSharedReservoirMatrix`, `preDivisorRiggedPrimeWittGram`, cofinal
  Gamma-Bockstein coefficients, source-derived prime enumeration, elementary determinant theory.
- **Forbidden circularity:** no Xi-zero enumeration, no RH-equivalent spectral hypothesis, no
  coefficient interpolant whose input already contains Xi zeros.
- **Success criterion:** exact Xi determinant or a sharp unconditional obstruction which specifies
  the regularization data still required.

## Conjecture loop

### C1 — polarized SC kernel itself is an Xi determinant
**Failed.** The SC coefficient system depends only on the horizontal real coordinate and vanishes
identically on the critical wall, whereas normalized Xi has nonzero central curvature. A raw
identification loses the vertical Xi variable before determinant formation.

### C2 — cofinal finite Gram determinants retain a nonzero Xi carrier
**Paper proof complete.** For `m` weights `wᵢ ≥ 0`, the shared-reservoir matrix is
`diag(√w) (I - 11ᵀ) diag(√w)`, hence
`det = (1-m) ∏ᵢ wᵢ`. The oriented determinant is
`o^m (1-m) ∏ᵢ wᵢ`. In the open critical strip every SC prime weight is bounded by one fixed
`q(s) < 1`, so the packet with `m+2` primes has absolute determinant at most
`(m+1) q(s)^(m+2)` and therefore tends to zero. On the critical wall every packet determinant is
exactly zero.

### C3 — a fixed-order meromorphic wall renormalization can recover a nonzero limit
**Failed, with exact positive survivor.** Source orientation times each absolute weight is exactly
the signed Gamma-Bockstein. Therefore the `m+2` packet determinant divided by `t^(m+2)` converges
to
`(1-(m+2)) ∏ᵢ[-2 Fisher(pᵢ) log pᵢ]`, and this leading coefficient is nonzero. For every fixed
`k`, any renormalizer `g` for which `t^k g(t)` has a finite punctured limit still gives
`g(t) det(packet_m(t)) → 0` whenever `k < m+2`. Thus fixed-order meromorphic wall
renormalization cannot recover normalized Xi value `1` from sufficiently large packets.

### C4 — arbitrary horizontal-only scalar normalization can recover Xi
**Failed.** Any complex-differentiable function factoring through `z.re` has arbitrarily small
nonzero imaginary periods and is therefore constant. Normalized centered Xi cannot be constant:
its central logarithmic second derivative has strictly negative real part. Hence no scalar profile
`g(z.re)`—regardless of singular packet-size normalization away from the wall—can equal
`XiC(z)/XiC(0)` on the complex plane. This is formalized as `no_realProfile_normalizedXiC`.

## Proof
1. Factor every finite packet determinant by Sylvester's determinant identity:
   `diag(√w) (I-11ᵀ) diag(√w)` has determinant `(1-m)∏wᵢ`.
2. Bound every packet weight by the corpus-native common contraction `q(s)<1`; squeeze
   `(m+1)q(s)^(m+2)` to zero. Wall packets vanish exactly because source orientation is zero.
3. On transverse coordinate `s(t)=(t+1)/2`, resolve orientation against absolute weights to obtain
   the signed Gamma-Bockstein product exactly.
4. Apply each corpus-native Bockstein derivative at neutral grade and finite-product limit laws.
   The resulting leading coefficient is nonzero because Fisher density and `log p` are positive.
5. Factor a general fixed-pole renormalized packet as
   `(t^k g(t)) · (det_m(t)/t^(m+2)) · t^(m+2-k)`; last factor forces zero when `k<m+2`.
6. For arbitrary horizontal-only scalar normalization, use imaginary dyadic translations as
   arbitrarily small periods. Holomorphic period rigidity forces constancy, contradicted by the
   corpus-native strict central Xi curvature theorem.

`[PROVED HERE]`

## No-go closure
- **Exact killing theorem/mechanism:** `tendsto_preDivisorRiggedPrimePacketDeterminant_zero` kills
  raw ordinary determinants. `tendsto_fixedPole_mul_preDivisorRiggedPrimeNeutralPacketDeterminant_zero`
  kills every fixed finite wall pole order once packet cardinality exceeds that order.
  `no_realProfile_normalizedXiC` kills every horizontal-only scalar Xi landing, independently of
  normalization order.
- **Strongest positive survivor:** exact rank-one determinant law and exact packet-growing neutral
  asymptotic with explicit nonzero prime-log leading coefficient,
  `tendsto_preDivisorRiggedPrimeNeutralPacketDeterminant_div_pow`.
- **New insight:** SC failure is not insufficient numerical decay. The raw finite Gram determinant
  destroys the carrier cofinally, and the wall introduces one simple zero per prime coordinate.
  Any survivor must use singular, packet-size-dependent regularization before specialization and
  must restore a genuinely complex vertical parameter or operator-valued datum; scalar
  normalization of horizontal data is categorically insufficient.
- **Status:** paper proof dependency-closed and formalized in
  `GaloisForLFunctions.RHTower.SourceHorizontalRiggedKreinDeterminantCollapse`. Exact leaf build
  PASS. Main capstones depend only on `propext`, `Classical.choice`, and `Quot.sound`.
  `[NOVELTY UNVERIFIED]`.

## Literature audit
- Britz–Carey–Gesztesy–Nichols–Sukochev–Zanin, *The product formula for regularized Fredholm
  determinants* (2020), <https://arxiv.org/abs/2007.12834>: trace-class determinant versus
  Hilbert–Schmidt `det₂` and its trace correction; no SC prime-Gamma packet theorem.
- Álvarez López–Kim–Morishita, *Regularized determinant formulas for foliated dynamical systems*
  (2024), <https://arxiv.org/abs/2410.20758>: dynamical regularized determinant precedent; no
  source-horizontal SC coefficient landing.
- Deninger, *A dynamical systems analogue of Lichtenbaum's conjectures on special values of Hasse–Weil
  zeta functions* (2006), <https://arxiv.org/abs/math/0605724>: dynamical determinant program;
  no finite rigged-prime Gram regularization result.

## Log
- 2026-08-28 — created directly in 1-in-progress after corpus and literature audit isolated the
  determinant landing as the exact SC open arrow.
- 2026-08-28 — C1 falsified by horizontal-variable loss and wall degeneracy.
- 2026-08-28 — C2 proved on paper and in `/tmp/sc_det_checks.lean`; C3 initiated.
- 2026-08-28 — C3 falsified: exact neutral order equals packet cardinality, excluding every fixed
  finite pole-order renormalization on sufficiently large packets.
- 2026-08-28 — C4 falsified: arbitrary horizontal-only scalar landing contradicts holomorphic
  small-period rigidity and strict central Xi curvature.
- 2026-08-28 — formalized in
  `SourceHorizontalRiggedKreinDeterminantCollapse.lean`; exact leaf build PASS; axiom audit
  `[propext, Classical.choice, Quot.sound]`; wired into `RHTower.lean`.
