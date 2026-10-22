# SQB reflected pair with common theta forcing

Status: source construction, full native graph equation, true constant-mode
centering, and analytic graph limits are closed and audited in Lean. Local
full-support of the arithmetic packet density has a paper proof; its Lean
formalization and normalized full-Xi occurrence remain open.
RH and normalized full-Xi occurrence remain unproved. Frontier map is read-only;
all work is analytical.

Chain: actual theta source -> normalized native approximate vectors at the unchanged
full Xi target -> occurrence -> real-preimage classification -> critical line -> RH.
The hardest obstacle is the normalized full residual. This construction seeks an
exact common forcing instead of a cutoff-dependent error.

## Conjecture and direct source calculation

Let z=xiSpectralPoint(q), q*=xiZeroCopyReflectEquiv(q), so z(q*)=-z.
The actual causal modes u=u_q and v=u_q* satisfy

    u'=-iz u-i Phi,       v'=iz v-i Phi,

with the original complete theta source Phi. Define

    p_q=-(u-v)/(2z).

The divisor has nonzero real spectral frequency, hence z!=0. Direct differentiation gives

    p_q' = (i/2)(u+v),
    p_q''+z^2 p_q=Phi.                                    (1)

This is an exact second-order source equation with the same forcing for every Xi copy.
All modes have the already proved all-rate theta decay. Their linear combination
therefore retains both-end decay, with no critical-line assumption.

In height coordinates put f_q(y)=sqrt(y)p_q(log(y)/2), and let W_q be its full modular
periodization. The source is exactly

    W_q=-(modeSource(q)-modeSource(q*))/(2z),

so the existing native admission proves W_q belongs to L2. With A=1+Delta and

    e_q=5/4+z^2/4=5/4-kappa^2,

(1) gives on paper

    (A-e_q)W_q=-(1/4) positiveSource.                      (2)

Equation (2) is proved for the actual native closed operator. Complete row regrouping
and two native norm limits establish graph admission without a derivative-interchange
or domain premise.

Centering in the original native measure leaves the common forcing

    F_0=-(1/4)(positiveSource-mean(positiveSource)),
    (A-e_q)(W_q-mean(W_q))=F_0.                           (3)

The exact native mean follows from the already proved first-order means:

    integral W_q = sourceMass/(1+z^2).

## Required positive test

A common forcing does not by itself yield occurrence. Its norm and the norm of the
constructed vector must be compared in the actual native space. The completed
pointwise Gram theorem supplies a full norm kernel for dilation packets; it does not
assert that the ratio in (2) or (3) tends to zero. A successful continuation must
construct a nonzero family with vanishing normalized full residual, or exact cancellation
of F_0 that preserves a nonzero vector.

## Analytical pivot

A group difference made directly from a solution telescopes away both the solution
and its forcing after complete periodization. That particular construction was discarded
without a new exclusion module. The reflected pair above instead cancels only the
source derivative and retains a common, literal forcing. Its remaining error is explicit.

## Native graph construction

Use H_n=n+3 and the existing smooth height weight w_a, equal to one below a and
zero above 2a. The two-ended seed cutoff is

    chi_n(y)=w_(H_n)(y)-w_(1/H_n)(y).

It is zero below 1/H_n and above 2H_n, bounded in absolute value by one, and
locally equal to one at each fixed positive height for all sufficiently large n.
For every derivative order j, y^j chi_n^(j)(y) has one bound independent of n.
The two positive source bounds are

    |f_q(y)| <= C_q positiveProfile(y),
    |y f_q'(y)| <= D_q positiveProfile(y).

The compact planar seed is cuspWindow(x) chi_n(y) f_q(y). Its full periodization
belongs to the actual native operator domain. In each primitive row the complete
integer sum of cuspWindow'' vanishes; the ordinary window sums to one. Thus its
operator image keeps every height row and has the exact residual

    -chi_n positiveProfile/4
    -2 (y chi_n') (y f_q') - (y^2 chi_n'') f_q.

The source majorants dominate both error sums by a fixed multiple of the admitted
positiveSource. Row dominated convergence and then native L2 dominated convergence
are proved. They identify the original source and its full image in the closed native
graph. True constant-mode centering gives (3), also without a domain premise.

Lean leaves:
- formal/GaloisForLFunctions/RHTower/SelbergThetaCommonForcing.lean
- formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMPositiveHeightOperator.lean
- formal/GaloisForLFunctions/RHTower/SelbergThetaCommonForcingGraph.lean

All three source checks and named leaf builds passed. All 73 public declarations
passed the axiom audit using only propext, Classical.choice, and Quot.sound.
The refreshed corpus passes formal lint. Full details are in
[the native graph audit](../../../3-formalized/sqb-common-theta-forcing.md).

The common-forcing constructions found in
FrankensteinThetaPrimeTranslationCommonForcing and ThetaCuspHawkingBMCommonRadialSource
retain their own source operators. They do not yet provide a cancellation law for
this unchanged native equation. The remaining target is a concrete nonzero native
family with vanishing normalized full residual; no such estimate is asserted.

The [native Gram composition search](../../sqb-native-gram-composition-search.md) records
existing small-image and one-sided norm-transfer constructions found across the
corpus. The open join is an exact source/native augmented Gram identification,
including mixed vector/operator-image entries, together with the source-specific
small-image input. Target-space density is not required by the existing one-sided
Gram isometry.

The [common-forcing Gram reduction](../../../3-formalized/sqb-common-theta-forcing-gram.md)
now computes the native augmented Gram and both finite-packet energies from the
response Gram G and the scalar pairing m(q)=<F_0,U_q>. The exact identity
`(e_r-conj(e_q)) G(q,r)=m(r)-conj(m(q))` determines G away from reflected energy
collisions. The remaining source comparison can therefore target m and the fixed
forcing mass, while retaining collision values and the native normalization.

The [literal scalar pairing formula](../../../3-formalized/sqb-common-theta-forcing-pairing.md)
identifies m(q) with an absolutely convergent height integral against the fixed,
strictly positive horizontal mean of the complete theta field. Its exact
finite-volume constant-mode subtraction is retained. The formula and all eight
public declarations are audited; the source estimate needed for normalized
small residuals remains open.

## Full local mass of the literal arithmetic packets (paper proof)

The existing `SelbergThetaNativeMeanCancellation.sourcePairing_eq_cauchy`
eliminates the constant-mode residue exactly. The native Gram theorem
`SelbergThetaCommonForcingPacketMass.packet_norm_sq_eq_integral` uses the
nonnegative density `d(t)=Xi(t)^2 B(t)`, where
`B(t)=boundaryWeight(t)=|1+boundaryPhase(t)|^2/2`. This density has **full
support on the real frequency line**, a stronger property than the already
formalized assertion that it is not almost everywhere zero.

Here is a direct proof retaining the complete arithmetic factor. Put
`z=-1+it` and `N(z)=z xi(z+2)+(z+2) xi(z+1)`. Algebra in the literal
scattering phase gives

    B(t)=|N(-1+it)|^2 / (2 |(-1+it) xi(1+it)|^2).             (A)

The denominator never vanishes: `-1+it` is nonzero and the corpus proves
`xi(s) != 0` for `Re(s)>=1`. The entire function `N` is not identically
zero, since `N(0)=2 xi(1)!=0`. The complex identity theorem therefore makes
its zero set discrete; its intersection with `{-1+it:t in R}` is countable.
Likewise `XiC(w)` is entire and not identically zero, since
`XiC(-i)=xi(3/2)!=0`, so the real zero set of `Xi(t)` is countable. Thus
`d(t)>0` outside a countable set, and every nonempty real open interval has
strictly positive integral of `d`.

For a finite packet with distinct squared spectral parameters and nonzero
coefficient vector, `SelbergThetaCommonForcingPacketMass.numeratorPoly_ne_zero`
shows its rational response is not identically zero. Its real zeros are finite
when all denominators lie in the strict spectral half-plane. Consequently
the packet density `d(t)*|rationalPacket(t)|^2` is positive almost everywhere
on every nonempty interval, so every such interval contributes strictly
positive native packet mass to the exact Gram formula. This is a
source-specific local mass theorem, not merely abstract Hilbert positivity.

The next occurrence test must turn this local mass into a sequence whose
*normalized residual* tends to zero at the unchanged full-Xi target.
Full support alone does not identify a possibly nonreal target with a real
spectral point or prove density of the available rational packet family.
The paper proof of (A) and the local-mass corollary have not been Lean-checked.
For formalization, the corpus already supplies `boundaryWeight_eq_half_sq`,
`xi_ne_zero_of_one_le_re`, and the finite-packet polynomial argument. Mathlib's
`AnalyticOnNhd.preimage_zero_mem_codiscrete` and
`IsLindelof.countable_of_isDiscrete` supply the isolated-zero-to-countable
step for `N` and `XiC`.

The common forcing also yields an **exact residual integral for every
force-cancelled finite packet** in the strict upper spectral chamber. Let
`e_i=5/4+z_i^2/4`, `D_i(t)=t^2-z_i^2`, `lambda(t)=5/4+t^2/4`, and
`R(t)=sum_i c_i/D_i(t)`. If `sum_i c_i=0`, then the existing native graph
identity gives

    (A-e) sum_i c_i S_i = sum_i c_i(e_i-e) S_i,
    sum_i c_i(e_i-e)/D_i(t) = (lambda(t)-e) R(t).           (B)

The second equality follows termwise from
`(e_i-e)/D_i=(lambda(t)-e)/D_i-1/4`; the last constant
vanishes by force cancellation. Applying the already formalized packet
Gram formula twice gives the exact source-specific quotient

    ||(A-e)sum_i c_i S_i||^2 / ||sum_i c_i S_i||^2
      = integral d(t)|lambda(t)-e|^2|R(t)|^2 dt
          / integral d(t)|R(t)|^2 dt,                       (C)

whenever the packet is nonzero. The denominator is strictly positive by
the existing `packet_ne_zero` theorem; the new full-local-mass observation
also locates positive contributions in every real interval. This reduces
the hard normalized-occurrence problem to concentration of the **actual
arithmetic rational packet** at the unchanged target energy. The graph
identity and the pointwise algebra in (B) are the next small Lean targets;
(C) is presently a paper deduction. A full-support density alone does not
construct the concentrating packet.
