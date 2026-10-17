# Actual dilation, integer block aggregation and infinite variance

Status: paper proof preceded Lean; all five leaves and all72 public declarations
now verified. Certified contribution17/100, counted once as a connected package.

Trap 10 alignment: the producer here is the explicit block replication
T_m z, its right inverse T_m z/m, and the physical packet S(T_m δ_0).
Their bounds and exact error decomposition are unconditional on actual
L²/ℓ² inputs. They belong to the continuum coprime-shear topic; no Weil
positivity receiver or unproved Chebyshev estimate enters. Arithmetic
stencils, if later coupled to these operators, must act on the unmodified
factorial floor sum T(N), with smooth counterterms handled after summation.
The present integer block index is not a pre-floor arithmetic counterterm.

## Physical dilation on the actual energy space

Let V=L²(ℝ,dt), with F_q(t)=∫₀ᵗq and f_q(x)=F_q(eˣ). For every real a,
define A_aq by the representative a q(at); A_0=0. For a≠0, dilation
preserves null sets, and change of variables gives

    ∫ℝ |a q(at)|²dt=|a|∫ℝ|q(t)|²dt.

This proves representative independence and actual L² membership. At a=0,
the representative is identically zero. Almost-everywhere linearity and the
norm identity construct a bounded real-linear operator with

    ‖A_aq‖²=|a|‖q‖²,   ‖A_aq‖=√|a|‖q‖,
    A_a A_b=A_(ab),      A_1=id, A_0=0.

For the composition identity, pull the almost-everywhere formula for A_bq
back through t↦at when a≠0; a=0 is immediate. Oriented integral substitution
gives F_(A_aq)(t)=F_q(at) for all real t,a, including zero and negative a.
For n∈ℕ, f_(A_(n+1)q)(x)=f_q(x+log(n+1)). Thus this is an actual bounded
operator on the physical Dirichlet space underlying logarithmic states.

## Constructed integer block aggregation

Use the certified isometric unit-cell synthesis S:ℓ²(ℕ)→V, its actual
adjoint B, and Q=SB. For m∈ℕ define the bounded operator

    H_m = B A_m S.

Write p_n(w)=Σ_(k<n)w_k. Primitive substitution and the certified synthesis
traces give p_n(H_mw)=p_(mn)(w), hence

    (H_mw)_j = Σ_(mj≤k<m(j+1))w_k
              = Σ_(r<m)w_(mj+r).

This constructs the infinite block-sum operator without assuming its output
is square-summable. For arbitrary physical q, the same finite telescoping
gives the exact intertwining B A_mq=H_m Bq. No cellular-input assumption.
Moreover H_0=0,H_1=id, and H_m H_n=H_(mn), since their prefixes equal
p_(nmk)(w). Equality of all prefixes determines each coordinate.

Let R be the certified unilateral right shift. Shifting a sequence m places
inserts m zeros, so grouping it into blocks of length m inserts exactly one
zero block. Therefore

    H_m R^m = R H_m

as actual bounded operators, also for m=0. This is the precise additive/
multiplicative covariance at integer scale, not a unitary-group assertion.

## Adjoint replication, exact coisometry and sharpness

Let T_m=H_m*. For m>0, a coordinate single δ_k is sent by H_m to δ_(k/m).
Pairing with δ_k gives the explicit adjoint

    (T_mz)_k=z_(k/m).

For m=0, T_0=0. Every length-m block of T_mz is constant z_j, so

    H_m T_m=m id,   ‖T_mz‖²=m‖z‖².

The second identity follows by pairing T_mz with itself and applying the
adjoint identity and the first. Thus H_m is surjective for m>0, with the
explicit right inverse z↦T_mz/m. Its sharp norm is √m: the upper bound
follows from B's contraction, A_m's norm, and S's isometry; T_mδ_0 has norm
√m and maps to mδ_0. The zero-scale norm is zero.

For m>0, K_m=(1/m)T_m H_m is an orthogonal projection onto the block-constant
sequences: coisometry gives idempotence and H_m(w−K_mw)=0, while adjoint
pairing makes the latter residual orthogonal to range(T_m). In particular,

    m‖w‖²−‖H_mw‖²=m‖w−K_mw‖².

Equality in the sharp energy bound holds exactly when w is block-constant.
This can also be read directly from the variance identity below. For m=0
the bound is equality for every w and the block condition is vacuous.

## Infinite variance, with convergence proved

For any finite vector u_0,…,u_(m−1), expanding the squares gives

    Σ_(r<m) Σ_(s<r)(u_r−u_s)²
      =m Σ_(r<m)u_r²−(Σ_(r<m)u_r)².                 (1)

A dependency-closed induction proof: append u_m. The new pair terms sum to
m u_m²−2u_mΣ_(r<m)u_r+Σ_(r<m)u_r²; substituting the induction hypothesis
and expanding (Σu+u_m)² gives (1) for m+1. The empty case is zero.

Define the explicit nonnegative block variance

    V_j(m,w)=Σ_(r<m)Σ_(s<r)(w_(mj+r)−w_(mj+s))².

For m>0, quotient fibres {k:k/m=j} are exactly [mj,m(j+1)). Regrouping the
actual summable square series of w gives

    Σ_j Σ_(r<m)w_(mj+r)²=‖w‖².

The square series of H_mw is also summable because H_m is already a bounded
operator. Subtract the two convergent series and use (1). Consequently

    HasSum (j↦V_j(m,w)) (m‖w‖²−‖H_mw‖²).          (2)

At m=0 both summands and the claimed sum are zero. Thus (2) holds for every
m and actual w, without an admission premise. The series can vanish only
when every pair square vanishes: every term is nonnegative, so each finite
block variance, then each square, is zero. This proves the block-constant
equality classification directly, including the vacuous zero case.

## Full physical defect and its equality states

Put b=Bq. The certified orthogonal cell decomposition gives
‖q‖²=‖b‖²+‖q−Qq‖². Combine this with (2) and B A_mq=H_m b:

    m‖q‖²−‖B A_mq‖²
      =m‖q−Qq‖²+Σ_j V_j(m,Bq).                    (3)

Every term is now an actual constructed quantity, and convergence is proved.
This lifts the finite multiplicative-to-additive trace inequality to actual
infinite operators, with an exact nonnegative defect. For m>0, equality in
the sharp bound holds exactly when q=Qq and b is constant within every block.
An explicit attainer is q=S(T_mδ_0): constant one on the first m unit cells,
zero on the other cells and on the negative half-line. Its energy is m and
its dilated cell-analysis energy is m². The case m=0 is identically zero.

The noncellular term in (3) retains the negative physical half-line through
the certified split ‖q−Qq‖²=∫_(-∞,0]q²+‖q−q⁻−Qq‖². No part of physical
energy is silently discarded.

## Domain boundary and provenance

Do not infer invariance of a completed divisor space under A_m. Its first
primitive trace becomes F_q(m), whereas completed divisor states require the
trace at1 to vanish. For example the certified full-family escape unitCell1
has F(1)=0 but F(2)=1. Dilation by2 therefore leaves that completed domain.
The positive result is the exact unrestricted operator and defect calculus;
domain covariance requires additional arithmetic structure.

Classical change of variables, Hilbert adjoints and finite variance are
parent tools, not external novelty claims. Primary sources inspected:
[mathlib Haar-space substitution](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Measure/Haar/NormedSpace.html),
[mathlib oriented interval substitution](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.html).
The field contribution is the constructed infinite physical/discrete coupling,
sharp block producer, exact convergent defect and successor covariance.
No RH, full SourceGraph, full affine-unitary or unweighted logarithmic H1 claim.
README remains read-only; no numerical experiments or new axioms.

Corpus query `physical L2 dilation block aggregation adjoint infinite variance
shift covariance`: all20 candidates and20 source arguments inspected.
partial=true, text/source interrupted; inventory complete73727files,
snapshot1446744/current1446745; compiler predominantly pending/source-only,
refresh incomplete/background_indexer_running. Existing shear, cell analysis,
prefix and successor results are parents; no matching infinite operator
package appeared. Focused lexical `dilation` returned9 declarations, including
the finite discrete shift estimate and continuum shear law; no semantic or
compiler coverage supplied. No absence or external novelty conclusion.


## Formal certificate

Namespace: GaloisForLFunctions.BiScaleUncertainty.SobolevShear.
Five leaves: PhysicalDilation (156lines/17public), IntegerBlockAggregation
(101/14), IntegerBlockCoisometry (125/12), IntegerBlockVariance (133/13),
IntegerDilationTraceDefect (152/16). Total667lines,72public declarations:
62theorems and10definitions. All five serial direct leaf checks have empty
logs and current normal compiled outputs. No full or umbrella build.

All72 public declarations pass #print axioms in /tmp/integer_dilation_axioms.lean;
only propext,Classical.choice,Quot.sound occur. All23 principal signatures
inspected: no admitted integrability, summability or analytic estimate.
All53 mathlib API probes pass. Five unique imports and72 exact catalog
locations verified. Key certificates: hasSum_integerBlockVariance,
integerBlockSum_shift, physicalDilation_trace_defect,
physicalDilation_trace_energy_eq_iff, blockPhysicalPacket_trace_energy,
dilation_two_outside_divisor_completion.

Global lint --check-generated exits1 for nine unrelated unreachable modules:
CenteredRamanujanVarianceAndAbelCofactorCancellation, CoherentKernelSplitting,
DivisorAverageChebyshevAndDyadicBlockVarianceProducer,
MultiOctaveStepBrickPartitionAndWitnessDyadicPositivity,
NyquistWeightCellAsymptotic, NyquistWeightKernel, NyquistWideSourceEnergy,
RightNodeCollarPartition, RoutePMVarianceToWitnessSynthesisAndCriticalStripBridge;
also concurrent LEAN_API/LEAN_OVERVIEW drift. No own or proof-debt error.
Indexes refreshed after lint; global lint is not claimed green.
Evidence: /tmp/integer-dilation-{axioms,lint-final,index-post-lint}.log,
/tmp/integer-dilation-{audit-names,leaf-checks,lint-errors}.json,
/tmp/integer-dilation-api-entries.txt. README hash unchanged.
