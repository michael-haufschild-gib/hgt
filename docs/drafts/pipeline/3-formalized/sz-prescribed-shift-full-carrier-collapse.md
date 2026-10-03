# Actual prescribed-shift carrier collapse

- **ID:** sz-prescribed-shift-full-carrier-collapse
- **Stage:** 3-formalized
- **Route:** SZ
- **Type:** THEOREM (Lean)
- **Date:** 2026-10-02
- **Statement:** The actual prescribed-shift V2 Livsic family tends locally uniformly to zero on the entire upper half-plane, along the full positive-aperture filter.
- **Lean status:** Four final leaf audits and thirteen public axiom checks passed.

## Exact theorem

`RHTower.tendstoLocallyUniformlyOn_suzukiTaV2Livsic_prescribed_zero`:

    TendstoLocallyUniformlyOn suzukiTaV2Livsic (fun _ => 0)
      (comap (fun a : SuzukiPositiveAperture => a.1) atTop)
      {z : Complex | 0 < z.im}

No hypothesis binders. This is the existing actual family, not a selected
negative shift, free-aperture surrogate, or newly normalized characteristic.
It classifies the limit of these coordinates; it neither proves nor falsifies
RH and does not retire SZ.

## Dependency-closed paper proof [PROVED HERE]

Write p_s(x)=exp(sx) cut off to [-a,a], c_a for the actual prescribed shift,
f_a for the physical raw deficiency at1 and delta_a=norm(f_a-p_1/c_a).
The previously audited actual V2 profile gives delta_a->0, and the actual
shift obeys c_a<=C exp(a), C=norm(kappa)+47.

Exact L2 integration gives, for s+t nonzero,

    <p_s,p_t> = (exp((s+t)a)-exp(-(s+t)a))/(s+t).

The zero-sum case is retained as an exact integral. For s>=1/2, pointwise
comparison with p_(1/2) and its audited norm yields norm(p_s)<=exp(sa).
Reflection gives the same bound for p_-s. This avoids an aperture-length
factor and does not use numerical approximation.

Fix1/2<s<1 and set r_a=c_a exp(-(1+s)a)>0. Complex Cauchy--Schwarz gives

    norm(r_a <p_±s,f_a-p_1/c_a>) <= C delta_a -> 0.

No reality premise on f_a is needed. Exact normalized Gram main terms are

    exp(-(1+s)a)<p_s,p_1> = (1-exp(-2(1+s)a))/(1+s),
    exp(-(1+s)a)<p_-s,p_1> = (exp(-2sa)-exp(-2a))/(1-s).

Consequently r_a<p_s,f_a>->1/(1+s) and r_a<p_-s,f_a>->0 in Complex.
The denominator limit is nonzero.

The actual interval spectral exponential at i s equals the literal real
exponential at slope s. The existing physical Fourier/Riesz bridge and
interval/aperture unitary therefore give exactly

    Fourier_a(w)(i s) = <p_-s,Jw>.

Existing actual raw-deficiency reflection replaces the minus channel by
reflection of the plus channel. The common deficiency norm cancels by the
existing raw-carrier identity, giving

    Livsic_a(i s) = ((i s-i)/(i s+i))
      * <p_-s,f_a>/<p_s,f_a>.

The common scale r_a cancels. Hence Livsic_a(i s)->0 on the interior segment.
No Ioo free-aperture integral is silently identified with the actual Icc
interval subtype.

For an arbitrary cofinal aperture sequence, actual finite carriers are
holomorphic on the upper half-plane and satisfy norm<1. Thus they are locally
bounded. The segment has an interior accumulation point at3i/4, proved using
continuous injective imaginary-axis embedding on a punctured real
neighborhood. The corpus Vitali target-identification theorem applies with
the holomorphic target0, giving locally uniform convergence of every cofinal
sequence to0 on the whole connected upper half-plane.

The positive-aperture comap filter is countably generated. On every compact
subset, Mathlib's sequential uniform-convergence criterion promotes these
sequence limits to uniform convergence along that filter. The compact-set
characterization then gives the displayed full-filter theorem.

## Corpus evidence and audit ledger

Deep search1189848: partial/source_only, pending coverage; broad results
included the previous cofinal-Xi no-go and an imaginary-segment determinacy
argument. Narrowed lexical polar search identified exact current norm/Gram
interfaces, with no freshness metadata. Deep analytic search1189974:
partial/source_only, pending; located the existing Vitali theorem. No global
absence or novelty claim follows from search coverage.

- API86202 passed: integral-ofReal, change of variables, actual reflection,
  norm comparison and physical Fourier/Riesz interfaces.
- SuzukiTaV2MixedSourceGram: scratch76030, final88852 passed. Four exports.
- SuzukiTaV2MixedSourceLimit: final74510 passed. Three theorem exports plus
  actual scale/pairing definitions; retains full complex errors.
- API14517 passed: Vitali target identification, compact-set convergence,
  sequential criterion, and actual filter countable-generation instance.
- SuzukiTaV2ImaginaryCarrierCollapse: final5798 passed. Four exports.
  Existing raw reflection from SuzukiTaMovableCompletedCovarianceSchur:254
  was reused; an initial duplicate draft was removed.
- SuzukiTaV2PrescribedCarrierCollapse: final20678 passed. Cofinal-sequence
  and full-filter roots. No whole-carrier limit premise remains.
- Axiom22765 passed for all thirteen public theorems: only propext,
  Classical.choice and Quot.sound. Exact full-filter root signature checked.

Every final command used `lake --old env lean <leaf> -o <leaf.olean>`;
all four imports are wired once. No full/umbrella build, computation experiment,
heartbeat increase, subagent, new axiom, commit or push.

Global lint68235 exits1 on thirteen unrelated unreachable modules:
CCMApertureChainProfile, CCMApertureTranslationChains,
CCMExponentialRampPrimeMoment, CCMExponentialRampSourceDissipation,
CCMExponentialRampTerminalEntropy, CCMRetainedChainKernelLower,
DirichletLLogStrip, MoebiusMollifiedCriticalMoment, MoebiusMollifiedErrorThreeLines,
ThetaMovingShellFirstOrderPhase, ThetaTailGaussianCoarea,
ThetaTailGaussianSubmodular, ZetaZeroDensityPowerSaving. No prohibited proof
declaration is reported. No current leaf is among failures; global gate is
not green and unrelated modules were preserved.

## New insight and remaining hard problem

This is the strongest positive survivor of the prescribed-shift direct-Xi
no-go, beyond the already proved first-defect and anchor-Wronskian limits.
These shifted coordinates discard the whole upper-half-plane target, not
merely one jet. A successful SZ proof needs a lawful recovery of unshifted
arithmetic information. Full signed shell/metric cancellation, shift removal,
canonical target identification and RH remain unresolved.

The existing actual-head completed-error producer is a concrete shared
Suzuki/CCM source interface for that work. Its sign on canonical ground heads
remains open; its equivalence to ground positivity is not a proof of that sign.
The live research log records exact next source targets and failed mechanisms.
