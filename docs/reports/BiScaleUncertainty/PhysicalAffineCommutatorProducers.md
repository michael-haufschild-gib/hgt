# Actual affine action, sharp commutators and finite producers

Status: dependency-closed paper proof completed before Lean; now formally
verified as connected contribution18/100. Topic: continuum coprime shear
and physical additive/multiplicative Dirichlet regularity.

## Constructed translations and the primitive anchor

Work in the actual real Hilbert space V=L²(ℝ,dt), with F_q(t)=∫₀ᵗq.
Translation t↦t+b preserves Lebesgue measure. Therefore pullback defines
an actual linear isometry τ_bq(t)=q(t+b), independent of representatives.
Composition and inverses are

    τ_bτ_c=τ_(b+c), τ_0=id, τ_(-b)τ_b=id, ‖τ_bq‖=‖q‖.

Interval substitution, with the already proved local integrability of every
q∈V, yields

    F_(τ_bq)(t)=F_q(t+b)−F_q(b).                    (1)

The primitive is injective: if F_q=F_r, their almost-everywhere derivatives
are equal, and the certified derivative theorem identifies those derivatives
with q and r. Primitive linearity follows by integrating actual a.e. linear
representatives; in particular F_(-q)=−F_q and F_0=0.

For logarithmic states f_q(x)=F_q(exp x) and b≥0, (1) becomes

    f_(τ_bq)(x)=f_q(log(exp x+b))−F_q(b).

Thus the nonlinear additive shear is realized on actual physical velocities.
The constant term is essential: an anchored state (c,q), representing
c+F_q(t), translates to (c+F_q(b),τ_bq). Its evaluation at t equals the
original evaluation at t+b; anchor and velocity compose exactly. Dilation
acts by (c,q)↦(c,A_aq), representing evaluation at at. These maps satisfy

    anchoredTranslation_b anchoredDilation_a
      =anchoredDilation_a anchoredTranslation_(ab).

No positive-half-line invertibility is inferred from the full-space action.

## Exact affine covariance and positive commutator defect

The certified actual dilation is A_aq(t)=a q(at), including A_0=0,
with ‖A_aq‖²=|a|‖q‖². Substitute the primitive formulas (1) and
F_(A_aq)(t)=F_q(at), then use primitive injectivity: for all real a,b,

    τ_b A_a=A_a τ_(ab).                            (2)

At a=0 both sides vanish; no nonzero-scale admission condition is needed.
Define the bounded commutator C_(a,b)=A_aτ_b−τ_bA_a and the real affine
gap c=b(a−1)=ab−b. Equation (2) and translation isometry give

    C_(a,b)q=A_a(τ_bq−τ_(ab)q),
    ‖C_(a,b)q‖²=|a|‖τ_cq−q‖².                   (3)

For example τ_b(q−τ_cq)=τ_bq−τ_(ab)q; its norm is unchanged.
The real Hilbert parallelogram identity gives the exact positive defect

    4|a|‖q‖²−‖C_(a,b)q‖²=|a|‖τ_cq+q‖².        (4)

Consequently ‖C_(a,b)q‖≤2√|a|‖q‖ unconditionally. Its primitive is
also explicit:

    F_(Cq)(t)=F_q(at+b)−F_q(b)−F_q(at+ab)+F_q(ab).

This separates the physical affine gap from the anchoring correction.

## Antiperiodic rigidity from actual cell analysis

First, an ℓ² sequence w with w_(k+1)=−w_k must vanish. Induction gives
w_k²=w_0². Its square series is summable, so w_k² tends to0; uniqueness
of the limit forces w_0²=0 and then every coefficient is zero.

Let B be certified unit-cell analysis. Formula (1) gives

    B(τ_1q)_k=(Bq)_(k+1).                         (5)

If τ_1q=−q, (5) and the preceding sequence argument imply Bq=0.
Translations commute, so every τ_bq is also antiperiodic and B(τ_bq)=0.
Its first coefficient is F_q(b+1)−F_q(b), hence this increment vanishes
for every b. At b=0, F_q(1)=0. On the other hand, applying primitives to
τ_1q=−q and using (1) gives F_q(b+1)−F_q(1)=−F_q(b). Together these
identities force F_q(b)=0 for every b. Primitive injectivity gives q=0.

For c≠0, if τ_cq=−q, put r=A_cq. Covariance gives τ_1r=−r, so r=0.
The exact dilation energy |c|‖q‖²=0 then forces q=0. At c=0,
q=−q forces q=0 by real linearity. Thus, for every c,q,

    τ_cq=−q  iff q=0,
    ‖τ_cq−q‖²=4‖q‖²  iff q=0.                  (6)

The second statement follows from the parallelogram identity: equality
means τ_cq+q=0. Combining (4) and (6) classifies equality in the universal
commutator bound: ‖C_(a,b)q‖²=4|a|‖q‖² iff a=0 or q=0.
This proof constructs all cell coefficients in ℓ²; it assumes no periodic
integrability theorem or trace-summability premise.

## Explicit finite producers and their exact errors

Let e_j be the certified orthonormal unit cells 1_(j,j+1], and for N≥1 put

    p_N=Σ_(j<N)(−1)^j e_j.

Orthonormality gives ‖p_N‖²=N. Translation by−1 sends e_j to e_(j+1).
In the pairing of τ_(-1)p_N with p_N, the N−1 adjacent overlaps each
contribute−1 and all other pairings are zero. Thus

    ⟨τ_(-1)p_N,p_N⟩=−(N−1),
    ‖τ_(-1)p_N−p_N‖²=4N−2.

Translation isometry makes the same difference norm hold at shift+1.
These are exact finite identities, requiring no numerical experiment.

For any real c define r_(c,N)=A_(1/c)p_N, with inverse0=0, so r_(0,N)=0.
If c≠0, covariance gives τ_c r_(c,N)=A_(1/c)τ_1p_N; if c=0 all terms
vanish. In every case,

    ‖r_(c,N)‖²=|1/c|N,
    ‖τ_c r_(c,N)−r_(c,N)‖²=|1/c|(4N−2).

Define the actual normalized producer

    P_(c,N)=(√(|1/c|N))⁻¹ r_(c,N).

At c=0 it is0. At c≠0 its norm is1 and its translation-difference
energy is4−2/N. Set c=b(a−1). Equation (3) now yields

    ‖C_(a,b)P_(c,N)‖² =
      if c=0 then0 else |a|(4−2/N).                (7)

Thus the normalized deficit is exactly2|a|/N at every nonzero affine gap.
This gives explicit near-attainers with unconditional error formulas, rather
than an existential or uninstantiated weight bound.

## Sharp operator norm and the geometric implication

At c=0, (2) gives C_(a,b)=0. At c≠0, the unit producers in (7) imply
‖C_(a,b)‖²≥|a|(4−2/N) for every positive integer N. Taking N→∞
using 1/N→0 gives the lower bound4|a|; (4) gives the matching upper bound.
Therefore, for all real a,b,

    ‖C_(a,b)‖ = if b(a−1)=0 then0 else2√|a|.      (8)

In particular C_(a,b)=0 iff a=0 or a=1 or b=0. When the commutator is
nonzero, (6) proves that no nonzero state attains its operator norm.
Every individual state has strict loss, but the explicit finite producers
approach the bound with error2|a|/N.

A nonzero affine gap can be arbitrarily small while the full energy-space
commutator norm stays maximal. Thus a small geometric shear gap alone
cannot give a small operator bound on physical velocities. State-dependent
regularity, trace constraints or the exact antiperiodic defect are needed.
This is compatible with the existing pointwise primitive resistance bounds;
they control a different quantity. No assertion about norm continuity,
SourceGraph admission, or preservation of completed divisor domains is
smuggled into this conclusion.

## Provenance and scope

Classical measure-preserving pullback and affine representation theory are
parents, not external novelty claims. Primary sources inspected:
[mathlib Lp pullback isometries](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Function/LpSpace/Basic.html),
[Tao, Fourier representation and Haar measure](https://www.math.ucla.edu/~tao/247b.1.07w/notes9.pdf).
Local source is authoritative for Lean API names. The field contribution is
the actual anchored shear/energy-space coupling, cell-based rigidity,
positive commutator defect, and quantitative finite physical producers.

Current corpus query returned20 candidate statements, all inspected; no
source arguments, proof ideas or ingredient sets returned. partial=true,
text/source interrupted; generation1447234 pending, refresh incomplete,
returned compiler status source_only. Existing dilation/cell results and
continuous affine bounds are parents; no absence or external novelty claim.
Evidence /tmp/physical-affine-search.json. Earlier candidate queries and
caveats remain on the pipeline card. README read fully and read-only.
No RH work, hgtl7 workflow, computations, full build or new axioms.


## Lean certification

Six leaves,674lines,76 public declarations:66 theorems,9 definitions and1
abbreviation. All six serial direct `lake --old env lean` checks have
empty logs and current normal `.olean` outputs. Scratch final audit
`/tmp/physical_affine_axioms.lean` checks all76 public dependencies using
only `propext`, `Classical.choice`, `Quot.sound`;29 principal signatures
and73 mathlib API probes also pass. Six umbrella imports and76 exact
catalog source locations are verified. README hash is unchanged.

Principal endpoints: `physicalAffineCommutator_defect`,
`physicalTranslation_antiperiodic_iff`, `physicalAffineProducer_energy`,
`physicalAffineProducer_defect`, `norm_physicalAffineCommutator`,
`physicalAffineCommutator_zero_iff`,
`physicalAffineCommutator_norm_attainment_iff`, and
`physicalAffineProducer_defect_tendsto`.

Global `scripts/formal_tools.py lint --check-generated` exits1 for22
unrelated unreachable modules and concurrent LEAN_API drift, with381
large-file warnings. Exact foreign names are on the stage3 card and in
`/tmp/physical-affine-lint-errors.json`; no own/proof-debt error.
Index refreshed after lint and scoped catalog rechecked. Global green is
not claimed. Logs: `/tmp/physical-affine-{axioms,lint-final,index-post-lint}.log`.
Card: `docs/drafts/pipeline/3-formalized/physical-affine-commutator-producers.md`.
