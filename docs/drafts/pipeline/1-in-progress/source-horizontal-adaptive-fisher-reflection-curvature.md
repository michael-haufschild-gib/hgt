# Source-horizontal adaptive Fisher reflection curvature

- **ID:** `source-horizontal-adaptive-fisher-reflection-curvature`
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) / FRANKENSTEIN SEAM / EXACT PRODUCER CLASSIFICATION / NOT RH
- **Source:** `rh-current-frontier-map.md`; constitutive formation-information properness;
  source-horizontal Gamma-six framing; Fisher-deconvolved same-carrier orientation;
  Gauss-Hodge mass current; Wold prime-clock profile.
- **Formal module:**
  `formal/GaloisForLFunctions/RHTower/SourceHorizontalAdaptiveFisherReflectionCurvature.lean`
- **Statement:** Frozen coefficient-faithful Gamma-Bockstein transport is exactly adaptive
  Bernoulli reflection information times a positive Gamma-six frame distortion. Equality of the
  two readings holds exactly at neutral grade; on every Xi divisor copy, global equality is RH.

## Goal

Find one non-equivariant source carrier on which two reflection transports are both defined with
literal prime labels and divisor multiplicities, then identify exact obstruction to their equality.
Required result must connect previously separate abelian-formation, Gamma-six, Gauss-Hodge, and
Wold/prime-clock structures without assuming a zero-placement law.

## Exact theorem

For prime `p` and grade `t`, define adaptive occupation

```text
q_p(t) = p^t/(p+p^t),                 q_p(t)/(1-q_p(t)) = p^(t-1),
F_p    = p/(p+1)^2,
D_p(t) = ((p+p^t)(p+p^(-t)))/(p+1)^2.
```

Lean proves unconditionally

```text
q_p(t)-q_p(-t)
  = p(p^t-p^(-t))/((p+p^t)(p+p^(-t))),

F_p(p^t-p^(-t)) = D_p(t)(q_p(t)-q_p(-t)),

D_p(t)
  = 1 + F_p * sourceHorizontalGammaSixUnitOppositeBoundaryCurvature(t log p),

D_p(t)=1 <-> t=0.
```

The actual symmetric Bernoulli KL divergence of the two adaptive occupations is

```text
J_ad(p,t) = 2t log(p) (q_p(t)-q_p(-t)).
```

Frozen Gauss-Hodge work is

```text
J_fr(p,t) = 2 log(p) F_p hodgeMassShape(p,t),
J_fr(p,t) = D_p(t) J_ad(p,t),
J_fr(p,t)-J_ad(p,t)
  = F_p GammaSix(t log p) J_ad(p,t).
```

Both works are reflection-even and strictly positive exactly off center. Therefore

```text
J_ad(p,t) <= J_fr(p,t),
J_fr(p,t)=J_ad(p,t) <-> t=0.
```

The assembled Gauss-Hodge current retains its residue and prime label through exact identity

```text
4 log(p) H_m(q,p)
  = log(2) residue_m(p) D_p(t_q) J_ad(p,t_q).
```

## Heavy conjecture loop

### C0 -- strict-right Hardy selector kills trace current

**Verdict: FAILED.** Strict-right Hardy object is canonical factor selection, not Hilbert
idempotent. Covariant scalar energy remains positive off line; no trace commutator annihilator.

### C1 -- Gibbs/Abel recession vanishes after source normalization

**Verdict: FAILED EXACTLY.** Existing exact limit is twice transverse defect. Abel recession
repackages off-line mass and cannot kill it.

### C2 -- functional equation forces right Hardy phase equal reciprocal phase

**Verdict: FAILED EXACTLY.** True Wiener-Hopf factorization gives right factor times complement.
At center complement is reciprocal; off center one is contractive and other expansive. Functional
equation conserves their rapidity instead of annihilating it.

### C3 -- finite-order Xi growth bounds universal Wold dilation orbit

**Verdict: FAILED BY TYPE MISMATCH.** Wold dilation is artificial source-grade orbit, not actual Xi
translation. Entire-function order cannot bound it without a nonlinear Xi landing theorem.

### C4 -- Wold polar work is constitutive Jeffreys work

**Verdict: FAILED AS EQUALITY; POSITIVE SURVIVOR PROVED.** Wold/Gauss-Hodge uses frozen neutral
Fisher frame, while constitutive formation adapts occupation with grade. Exact mismatch is `D_p(t)`.

### C5 -- frozen/adaptive mismatch is arbitrary gauge

**Verdict: FALSIFIED.** Distortion is canonical and equals one plus literal Gamma-six paired
curvature. It is reflection-even, prime-faithful, positive, and has exact neutral radical.

### C6 -- source reflection alone identifies adaptive and frozen transports

**Verdict: FAILED.** Reflection preserves each symmetric work separately for every grade. It does
not compare frames. Equality is stronger and pointwise equivalent to neutrality.

### C7 -- Hasse packet plus functional-equation lift supplies sufficient observer

**Verdict: FAILED.** Packet lift is KL isometry exchanging sheets. It preserves distinguishability;
no Xi-typed sufficient observer or zero landing forces frozen/adaptive equality.

## Higher universal principle

Retained horizontal class is not an unexplained defect inside any one route. It is curvature of
changing connection between two natural source readings:

> adaptive statistical transport changes Fisher metric with horizontal character; frozen
> coefficient-faithful transport moves character inside neutral source frame. Gamma-six curvature
> is exact Radon--Nikodym defect between these connections.

This explains why functional-equation isometries, stable index, polar normalization, trace
cyclicity, and symmetric KL all retain rather than orient off-line class: each is internal to one
connection. Producer must compare connections on actual arithmetic carrier.

## Exact open producer — sharpened by C8/C9

Direct equality of frozen and adaptive symmetric work remains sufficient but is no longer shortest
producer. `source-horizontal-adaptive-fisher-chirality-selection.md` proves a weaker signed route:
source reversal plus equality of forward/reverse conditional observer-fibre KL costs forces adaptive
directed chirality to vanish, hence `t=0`. Hidden conditional costs may be nonzero. Canonical Boolean
complement is formally excluded because it transports `t` to `2-t`, not `-t`.

Live source target is therefore a literal arithmetic fibre-balanced reversal certificate on each
Xi copy. Cross-fibre reflection, KL isometry, bounded unframed work, and transported metric equality
still do not supply that conditional current equality.

## Formal capstones

- `sourceHorizontalPrimeAdaptiveOccupation_odds`
- `sourceHorizontalFrozenBockstein_eq_distortion_mul_adaptive`
- `sourceHorizontalPrimeFisherFrameDistortion_eq_one_add_curvature`
- `bernoulliJeffreysReal_sourceHorizontalPrimeAdaptive_eq`
- `sourceHorizontalPrimeFrozenHodgeWork_eq_distortion_mul_adaptiveJeffreysWork`
- `sourceHorizontalPrimeFrozen_sub_adaptive_eq_gammaSixCurvatureReserve`
- `gaussHodgeMassCurrent_eq_adaptiveJeffreysCurvature_crossmultiplied`
- `sourceHorizontalXiAdaptiveJeffreysWork_reflection`
- `sourceHorizontalXiWork_multiplicity_copy_independent`
- `riemannHypothesis_iff_sourceHorizontalXi_frozenHodge_eq_adaptiveJeffreys`

## Gates and status

- [x] source-pure exact carrier and heavy fail/pivot loop recorded;
- [x] dependency-closed paper algebra;
- [x] unconditional Lean module direct check green;
- [x] targeted module build green; capstone axiom audit reports only `propext`,
  `Classical.choice`, and `Quot.sound`;
- [x] wired into `GaloisForLFunctions.RHTower` umbrella;
- [ ] external novelty audit;
- [ ] arithmetic frozen/adaptive equality producer;
- [ ] weaker arithmetic fibre-balanced reversal producer;
- [ ] RH.

No RH proof is claimed. Terminal theorem is exact producer equivalence, not proof of producer law.
