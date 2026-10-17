# Actual physical box averages and quantitative affine regularity

Status: dependency-closed paper proof completed before Lean, now formally
certified as one connected contribution (19/100). Topic: continuum coprime
shear, actual additive regularity and multiplicative graph control.

## Construct the operator in the physical Hilbert space

Let V=L²(ℝ,dt), τ_uq(t)=q(t+u), and F_q(t)=∫₀ᵗq. These are the
actual physical space, translations and primitives already certified.
The map u↦τ_uq is norm-continuous: continuous measure-preserving pullback
acts continuously on L². Equivalently, compact continuous functions are
dense, translations are isometries, and uniform continuity proves the
claim on the dense subspace. Thus this orbit is Bochner integrable on
every finite interval. No orbit-integrability premise is needed.

For real s, set h=exp(s)>0 and define

    M_s q = h⁻¹ ∫₀ʰ τ_uq du,                       (1)
    D_s q = h⁻¹(τ_hq−q).

Both are actual vectors of V. Integral linearity gives linearity of M_s;
the norm-integral inequality and translation isometry give

    ‖M_s q‖≤h⁻¹∫₀ʰ‖q‖du=‖q‖.                    (2)

Hence M_s is a bounded linear contraction, for every s. Likewise D_s is
bounded linear and ‖D_s q‖≤2h⁻¹‖q‖. This constructs regular velocities
from arbitrary physical states instead of assuming regularity of q.
Translations commute with M_s because each τ_c is a bounded linear map
and τ_cτ_u=τ_(c+u)=τ_uτ_c.

Write G_q(t)=∫₀ᵗτ_uq du. Banach-valued FTC gives G_q'(t)=τ_tq at
every real t. Oriented interval additivity and translation substitution
then give the exact moving-window formula

    τ_cM_s q = h⁻¹(G_q(c+h)−G_q(c)).               (3)

All interval identities hold for arbitrary signs of c.

## Actual representative and its derivative

For every t, define the actual L² interval vector

    v_t=1_(0,t]−1_(t,0].

Both indicators have finite measure. The L² inner product with v_t is
exactly F_q(t), by the definition of the oriented integral. Thus evaluation
q↦F_q(t) is a continuous linear functional and commutes with the Bochner
integral in (1). Let H_q(t)=∫₀ᵗF_q(v)dv. The primitive F_q is continuous,
so H_q'(t)=F_q(t) for every t. The translation anchor formula gives

    F_(M_s q)(t)
      =h⁻¹∫₀ʰ(F_q(t+u)−F_q(u))du
      =h⁻¹(H_q(t+h)−H_q(t)−H_q(h)).              (4)

Here H_q(0)=0. Differentiating (4) at every t proves that its derivative is

    m_(s,q)(t)=h⁻¹(F_q(t+h)−F_q(t)).             (5)

The certified a.e. derivative of the primitive of M_s q is its L²
representative. Uniqueness of derivatives therefore proves

    M_s q(t)=m_(s,q)(t) almost everywhere.

Formula (5) is continuous and gives the actual moving box average
h⁻¹∫_t^(t+h)q, not merely an abstract vector called an average.
The anchor formula and primitive linearity also give

    m_(s,q)(t)=F_(D_s q)(t)+h⁻¹F_q(h).          (6)

Consequently m_(s,q) is locally absolutely continuous and has derivative
D_s q almost everywhere. In particular both m_(s,q) and its actual a.e.
derivative are in L². The output's Sobolev regularity is proved from its
construction. No differentiability, compact support or integral estimate
for the input is assumed.

Differentiating (3) in the Hilbert space gives the stronger orbit statement

    d/dc [τ_cM_s q] = h⁻¹(τ_(c+h)q−τ_cq)
                    = τ_cD_s q,                (7)

at every real c. Thus these explicit producers lie in the domain of the
strong translation derivative, with its value constructed exactly.
This does not identify the domain of an unrelated completed graph operator.

## Exact positive averaging loss

All following scalar integrands are continuous on compact intervals,
so all integrals are finite. Put I=∫₀ʰτ_uq du=hM_s q and R=‖q‖².
Continuous inner-product functionals commute with integration. Hence

    ∫₀ʰ∫₀ʰ ⟨τ_uq,τ_vq⟩ dv du = ⟨I,I⟩ = ‖I‖².

Expand each squared difference and use translation isometry. Integrating
2R−2⟨τ_uq,τ_vq⟩ proves

    ∫₀ʰ∫₀ʰ ‖τ_uq−τ_vq‖² dv du
       = 2h²(R−‖M_s q‖²),                     (8)

or, equivalently, the contraction loss is the double variance divided by
2h². Similarly, expanding ‖τ_uq−M_s q‖² and using I=hM_s q gives

    ∫₀ʰ ‖τ_uq−M_s q‖² du = h(R−‖M_s q‖²).     (9)

These are exact positive identities, retaining all cross-shift pairings.
They connect the actual continuous producer to the earlier finite-block
variance calculus without replacing its Gram terms by independent bounds.

## Quantitative affine gap control by interval cancellation

Subtract (3) at c=0. Oriented interval additivity yields

    τ_cM_s q−M_s q
      =h⁻¹(∫_h^(h+c)τ_uq du−∫₀ᶜτ_uq du)
      =h⁻¹∫₀ᶜ(τ_(u+h)q−τ_uq)du.              (10)

The norm-integral inequality works for either orientation of 0..c, giving

    ‖τ_cM_s q−M_s q‖ ≤ (2|c|/h)‖q‖.

The triangle inequality and (2) also give the bound2‖q‖. Combining,

    ‖τ_cM_s q−M_s q‖
      ≤2 min(1,|c|/h)‖q‖.                     (11)

For A_aq(t)=a q(at), C_(a,b)=A_aτ_b−τ_bA_a and c=b(a−1), the exact
certified commutator energy is |a|‖τ_cq−q‖². Thus for all real a,b,s
and every actual q∈V,

    ‖C_(a,b)M_s q‖
      ≤2√|a| min(1,|b(a−1)|/exp(s))‖q‖,       (12)
    ‖C_(a,b)M_s q‖²
      ≤4|a| min(1,|b(a−1)|/exp(s))²‖q‖².      (13)

All zero and negative scale/shift cases are included. For fixed smoothing
width this tends to zero with the affine gap, unlike the unrestricted
operator norm. This is an operator estimate on the explicitly constructed
range M_s applied to bounded input, not a claim that every velocity has a
uniform small-gap estimate. No optimality of the coefficient in (11) is
claimed.

## Strong approximation and graph coupling

Since G_q'(0)=q and G_q(0)=0, the definition of the derivative implies
h⁻¹G_q(h)→q in V as h→0 through positive values. Compose with h=exp(s)
as s→−∞ to obtain

    M_s q → q in physical L².                  (14)

Thus the constructed regular velocities approximate every physical input.
This is strong convergence for each input, not operator-norm convergence.
The exact loss (8) also tends to zero by norm continuity.

For any compact continuous source ψ and nonnegative sequence of line
weights, write R_ψ for the already constructed finite resistance mass and
E_ψ(q) for compact-mixture jump energy. Existing congestion gives

    E_ψ(q)≤congestionEnergy(q)
          ≤R_ψ sourceDirichletMass(ψ,q).

Logarithmic substitution turns sourceDirichletMass into the physical square
integral over [exp(−radius ψ),exp(radius ψ)]. This is at most the full
physical square integral ‖q‖², since the integrand is nonnegative. The
same inequality holds in the extended nonnegative reals, with ofReal on
real energies. Hence

    E_ψ(q)≤R_ψ ofReal(‖q‖²).                   (15)

Apply this to the actual commutator of the average and then use (13):

    E_ψ(C_(a,b)M_s q)
      ≤R_ψ ofReal(4|a| min(1,|b(a−1)|/h)²‖q‖²). (16)

All coefficients are finite by construction, and no full-family graph
admission premise is introduced. This transfers the explicit physical
affine producer bound to multiplicative diffuse and nodal jump energies of
the established compact-source graph. It does not establish full uncut
SourceGraph closure or completed divisor-domain invariance.

There is also actual approximation in compact graph jump energy. Apply (15)
to M_s q−q. Its norm tends to zero by (14). Since R_ψ is finite, the upper
bound is ofReal(R_ψ.toReal·‖M_s q−q‖²), which tends to zero. Nonnegativity
and the squeeze theorem therefore prove

    E_ψ(M_s q−q) → 0 as s→−∞.                 (17)

Thus the explicit regular velocities approximate every physical input in
both physical energy norm and each constructed compact-source jump energy.
This statement includes arbitrary nonnegative line weights; their finite
resistance coefficient is already constructed by the compact-mixture theory.

## Parent theories, corpus evidence and boundaries

Classical translation continuity, Steklov averaging, Hilbert variance and
FTC are parent theories. Primary references inspected:
[mathlib continuous Lp pullback](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Function/LpSpace/ContinuousCompMeasurePreserving.html)
and [Demkowicz, Energy Spaces, §§2.1–2.3](https://users.ices.utexas.edu/~leszek/classes/CSE393/book.pdf).
The latter gives translation continuity, convolution bounds and smoothing;
it is not cited as proving this exact affine/graph package. Local mathlib
source is authoritative for the formal APIs. No external novelty claim.

Current corpus query: all20 candidate statements inspected; no source
arguments, proof ideas or ingredient sets returned. partial=true; text/source
interrupted, deadline/vector-proof stage unfinished, generation1447551
pending, refresh incomplete/background indexer. Relevant parents include
actual primitive derivatives, compact-source variance/congestion and
compact continuous annular averages. Earlier candidate audit inspected20
candidates and20 source arguments. No absence inference.
Evidence: /tmp/physical-box-average-search.json and previous candidate card.

Trap10 is addressed by actual unconditional producers and exact loss.
No RH work, numerical experiment, derivative-moment truncation of a Lévy
functional, pre-floor subtraction or added analytic hypothesis. This
physical Sobolev construction does not claim an unweighted logarithmic H1
identification. Field README fully read and read-only. All theorems above
are proved on paper and formally certified below.

## Formal certificate

| Module | Lines | Public declarations |
|---|---:|---:|
| PhysicalTranslationContinuity | 78 | 12 |
| PhysicalBoxAverage | 116 | 13 |
| PhysicalBoxProfile | 117 | 16 |
| PhysicalBoxVariance | 88 | 6 |
| PhysicalBoxAffineRegularity | 115 | 9 |
| PhysicalBoxGraphControl | 85 | 5 |

Six serial direct leaf checks pass without diagnostics; all normal outputs
are current. All61 public axiom checks use only propext,Classical.choice,
Quot.sound.28 principal signatures and73 mathlib API probes pass. Six unique
umbrella imports and61 exact catalog locations verified.599lines total,
53theorems+8definitions. Paper proof preceded field Lean. README remains
unchanged, SHA256 dda7a67adbca527a21596c6fb672c28afb5feda594fe3b552a781325df7c3933.
No full/umbrella build, heartbeat increase or numerical experiment.

Global lint --check-generated exits1 for seven unrelated unreachable modules:
ConfinedCoherentPlasticGap, ForcedFirstCollar, SignedLcmFractionalDefectAndCompleteFibreCollapse, SignedPrimePolarClampedPrimeSum, SignedPrimePolarRealFactorialStencil, StrictPairedCollarLimit, UniformPairedCollarGain.
There are381 existing large-file warnings; no own, proof-debt or generated
index errors. Repository-wide green is not claimed. Concurrent files preserved.

Evidence: /tmp/physical-box-axioms.log, /tmp/physical_box_axioms.lean,
/tmp/physical-box-{audit-names,manifest-report,leaf-checks,lint-errors}.json,
/tmp/physical-box-api-entries.txt, /tmp/physical-box-index.log and
/tmp/physical-box-lint-final.log. Paper:
docs/reports/BiScaleUncertainty/PhysicalBoxAverageAffineRegularity.md.
Card: docs/drafts/pipeline/3-formalized/physical-box-average-affine-regularity.md.
One connected contribution, certified19/100; overall goal remains active.
