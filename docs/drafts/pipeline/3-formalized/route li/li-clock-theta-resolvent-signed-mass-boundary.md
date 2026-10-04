# Exact signed-mass boundary of the actual theta resolvent

- **ID:** LI-CLOCK-THETA-RESOLVENT-SIGNED-MASS-BOUNDARY
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [completed-clock sign attempt](../1-in-progress/li-clock-completed-forcing-direct-sign.md)
- **Statement:** For the actual resolvent r and beta=max_q abs(Im((xiSpectralPoint q)^(-1))), each signed part exp(-pt)r_+ and exp(-pt)r_- is integrable exactly when p>beta. Both ordinary signed masses are infinite and both signs occur cofinally.

## Gates

- [x] Complete source proof and all159-line independent audit, including critical endpoint.
- [x] Exact signed-mass and contour survivor formalization.
- [x] Named/direct builds, all-public axioms, complete source review and integration.

## No-go closure

- **Exact killing mechanism:** Finite one-sided ordinary mass forces both sides integrable; the undivided Laplace identity then contradicts an actual reciprocal-Xi zero on the closed boundary. The same argument excludes the exact weighted critical endpoint.
- **Strongest positive survivor:** A sharp common integrability domain for both signs, with genuine above-threshold Laplace identity and complete finite-contour growth admission. Under RH, the signed Laplace mass tends to one while both ordinary signed masses remain infinite.
- **New insight:** Integrable positive-part control of r cannot orient the actual response. The remaining r*g comparison must preserve cancellation.
- **Status:** PAPER PASS; Lean CLOSED (see Lean certificate). beta=0 iff RH is a characterization; beta=0 has not been proved. No route retirement or actual S sign conclusion.

## Audited paper proof [PROVED HERE]

Root159 below is preserved verbatim: `/tmp/li_root_theta_resolvent_signed_mass_boundary.md`, SHA256 `689928e95f673d1f81de9cff92db7238a70b3732ebf068e4fccd81aecdd8ad17`. Its pending-audit header is historical. Independent all159-line audit `/tmp/li_producer_theta_resolvent_signed_mass_audit.md` (71 lines), SHA256 `83d73da9e1602e864d8316162d1034f691802b61a4b21a28d469fc928893892f`, passed; root read every audit line. Full inverse/source admission is preserved in [theta forcing and inverse boundary](li-clock-theta-forcing-inverse-boundary.md).

- 2026-10-01 — Complete paper and primary-source audits pass. Critical threshold and both signed parts retained; Lean formalization and RH-bearing comparison remain open.

# Exact signed-mass boundary of the actual theta resolvent

2026-10-01. Root paper proof; independent audit pending. This classifies
the actual resolvent r, not the desired massive response -S. It supplies
no proof of r*g<=g, S<=0 or RH.

## 1. Fixed source and the actual growth threshold

Use exactly the entire Phi, B, K=B' and r=-u'' of final291
/tmp/li_producer_massive_theta_forcing_attack.md,
SHA f7f219376559c6411960d839726a9c6ade09bbab81b1cb83426065f077f05cc2.
In particular all normalizations and every zero multiplicity are retained:

    Phi(z)=XiC(-Iz)/XiC0=sum_j nu_j z^(2j)/(2j)!,
    B(t)=sum_j nu_j t^(2j)/((2j)!)^2,
    r+r*K=K, r(0)=0, r'(0)=nu_1/2>0.

Phi and B are even entire and nu_j>0. B and each fixed derivative have
every positive exponential type by Cauchy applied to the ordinary Phi.
K>=0 for nonnegative clocks. The r construction is entire and real on
real clocks; no positive-inverse premise is supplied.

Put w_q=(xiSpectralPoint q)^(-1) and

    beta=sup_q |Im w_q|.

The source is nonempty. XiHeatShellMinimum:24-30 constructs a genuine
XiZeroCopy from xiDivisorSupport_infinite. XiCanonicalProduct:48-99 gives
the actual spectral coordinate, its nonvanishing, complete reciprocal
square summability and real coordinates under RH. TopFrequency:95-152
defines the exact rates, proves their square summability, finite upper
levels and a nonempty finite maximal packet if RH fails. Its proof also
shows that vanishing of every rate implies RH.

Consequently 0<=beta<gamma=1/300. If beta>0, choose any positive rate a.
The finite nonempty set of rates >=a has a maximum b; all remaining rates
are <a<=b, so b=beta and beta is attained. If beta=0, every actual rate
equals zero. In both cases some nonzero actual reciprocal zero lies on
the line Re p=beta: all zeros of Phi(1/p), p!=0, are p=-I*w_q; evenness
supplies the sign of p with nonnegative real part. No simple-zero
assumption is needed. Denote one such zero by p_0.

This proves beta=0 iff RH as a characterization; it does not prove beta=0.

## 2. Genuine upper admission at every rate above beta

For ANY delta>beta, the same finite rectangle used in final291 can be
chosen with vertical edges Re p=+-delta and horizontal edges Im p=+-H,
where H>1/sqrt(150). It encloses zero and every reciprocal zero strictly.
The contour for 1/[p^2 Phi(1/p)] deforms from a sufficiently large circle
without crossing any singularity. All multiplicities and the singular
point zero stay inside; no infinite sum of residues is invoked.

Hence for every fixed m and real t,

    |r^(m)(t)|<=C_(delta,m) exp(delta*|t|).

The constants depend on delta and m. For every p>beta, choose delta
strictly between beta and p. This proves the genuine absolute admission

    integral_0^infinity exp(-pt)|r(t)| dt < infinity.       (1)

Since p>beta>=0, K also has a genuine absolute Laplace transform there.
The equation r+r*K=K and absolute convolution Fubini yield, for real p>beta,

    H(p)=integral_0^infinity exp(-pt)r(t)dt
        =1-1/Phi(1/p).                                  (2)

Here 1+Khat(p)=Phi(1/p)>1; this is division at positive real p only.

## 3. The critical weighted absolute integral diverges

Suppose integral exp(-beta*t)|r(t)| is finite. Its complex Laplace
transform H(z) is holomorphic on Re z>beta and uniformly bounded on the
closed half-plane Re z>=beta by that finite integral. Holomorphy follows
from dominated differentiation on each smaller half-plane: every fixed
t power is bounded after multiplication by an additional decaying
exponential, against the assumed exp(-beta*t)|r(t)| majorant.

On Re z>beta, Phi(1/z) is holomorphic because z!=0. The undivided product

    (1-H(z))*Phi(1/z)=1                                  (3)

holds on the real interval z>beta by (2), then on the whole connected
open half-plane by the identity theorem. This step does not divide by
Phi or remove a zero set from the domain.

Approach the nonzero boundary zero p_0 from section1 along z=p_0+epsilon,
epsilon>0. Phi(1/z)->Phi(1/p_0)=0, while |1-H(z)| stays bounded by
1+integral exp(-beta*t)|r(t)|. The left side of (3) tends to zero,
contradicting its exact value one. Thus the critical integral diverges.

For any real p<=beta, exp(-beta*t)<=exp(-pt) on t>=0. Therefore its
weighted absolute integral diverges as well. Together with (1),

    integral exp(-pt)|r(t)|<infinity iff p>beta,
    for EVERY real p.                                   (4)

This includes beta=0: the boundary zero p_0 is still nonzero, so the same
bounded boundary argument proves r is not ordinarily integrable even
under RH.

## 4. Both signs have exactly the same critical boundary

Let r_+=max(r,0), r_-=max(-r,0). These are continuous nonnegative functions
and r=r_+-r_-. Rearranging the exact causal equation on each compact
interval gives

    r_-+r_-*K = r_++r_+*K-K <= r_++r_+*K,
    r_++r_+*K = K+r_-+r_-*K.                            (5)

Fix p>0. Khat(p) is finite. If either signed part has finite exp(-pt)
integral, Tonelli makes its convolution with K finite with exact product
mass. Formula (5) then bounds the other part by a function of finite
weighted mass. Thus for every p>0,

    exp(-pt)r_+ integrable iff exp(-pt)r_- integrable
      iff exp(-pt)|r| integrable.                        (6)

It remains to handle p=0 without assuming K is integrable. Suppose one
ordinary signed mass is finite. Then for every p>0 that part is weighted
integrable, so (6) admits both parts and proves (2) for EVERY p>0.
The genuine positive source series gives

    Phi(1/p)>=1+nu_1/(2p^2),
    H(p)=1-1/Phi(1/p)->1 as p decreases to zero.

If integral r_+=M<infinity, monotone convergence in
H_-(p)=H_+(p)-H(p) shows integral r_-=M-1<infinity
(if M<1 this is already impossible by nonnegativity). If integral
r_-=M<infinity, use H_+(p)=H(p)+H_-(p) to obtain integral r_+=M+1.
Either supposition makes r ordinarily integrable, contradicting (4).
Hence BOTH ordinary signed masses are infinite. For p<0, the weights
are >=1, so both signed weighted masses remain infinite.

Combining this with (4)-(6), the exact unconditional classification is

    integral exp(-pt)r_+<infinity iff p>beta,
    integral exp(-pt)r_-<infinity iff p>beta,              (7)

for every real p. In particular each unweighted tail has infinite positive
and negative mass; finite compact contributions cannot account for it.
Both signs occur cofinally. No fixed-amplitude, pointwise exponential
asymptotic, or simplicity of actual zeros is claimed.

## 5. Positive survivor and limit of the conclusion

The sharp boundary (7), the same threshold for both signs, genuine
above-threshold identity (2), and undivided complex identity (3) are the
positive survivor. Under RH, beta=0, so the genuine signed Laplace mass
exists for every p>0 and tends to one as p decreases to zero, while BOTH
ordinary signed masses are infinite. Without RH, beta>0 and both signed
weighted integrals already diverge at the strictly positive threshold.

This rules out integrable positive-part or negative-part control of r
as a route to the actual history comparison. It does not exclude a signed
correlation estimate with the particular g, nor prove that g-r*g is
negative somewhere. The desired massive and finite-window inequalities
remain open. No new Lean theorem, compiler result or RH conclusion.

## Lean certificate

- [x] 2 → 3: Lean `GaloisForLFunctions.RHTower.LiClockThetaResolventSignedMass`, `GaloisForLFunctions.RHTower.LiClockThetaInverseContourGrowth`, `GaloisForLFunctions.RHTower.LiClockThetaResolventSignChange`, `GaloisForLFunctions.RHTower.LiClockThetaMassiveForcing`, `GaloisForLFunctions.HTGeometry.RectangleBorelLaplaceInversion`, `GaloisForLFunctions.RHTower.XiHeatShellMinimum`, `GaloisForLFunctions.RHTower.XiReciprocalTranslationSeamNormLaw`, `GaloisForLFunctions.RHTower.ProfileRenewalLogKernel`, `GaloisForLFunctions.HTGeometry.QuasiPolynomialLaplaceCalculus`; `lake env lean` + module build pass; axiom audit `[propext, Classical.choice, Quot.sound]` only

Modules (all `lake env lean` clean, `lake build --old` clean, every public constant audited to `[propext, Classical.choice, Quot.sound]`, wired into the umbrellas):
`GaloisForLFunctions.RHTower.LiClockThetaResolventSignedMass` (new), building on `GaloisForLFunctions.RHTower.LiClockThetaInverseContourGrowth`, `GaloisForLFunctions.RHTower.LiClockThetaResolventSignChange`, `GaloisForLFunctions.RHTower.LiClockThetaMassiveForcing`, `GaloisForLFunctions.HTGeometry.RectangleBorelLaplaceInversion`; installed inputs `GaloisForLFunctions.RHTower.XiHeatShellMinimum` (nonempty divisor), `GaloisForLFunctions.RHTower.XiReciprocalTranslationSeamNormLaw` (RH ⇔ all `Im α_q = 0`), `GaloisForLFunctions.RHTower.ProfileRenewalLogKernel` (integrable nonnegative convolutions), `GaloisForLFunctions.HTGeometry.QuasiPolynomialLaplaceCalculus` (complex monomial Laplace transforms).

| Claim | Declaration |
|-|-|
| §1 `β=sup_q|Im α_q⁻¹|` is a maximum, `0≤β<1/300` | `liClockThetaResolventThreshold`, `liClockThetaResolventThreshold_spec`, `exists_isMax_abs_im_inv_xiSpectralPoint`, `liClockThetaResolventThreshold_nonneg`, `liClockThetaResolventThreshold_lt` |
| `β=0 ⇔ RH`; `¬RH ⇒ β>0` | `liClockThetaResolventThreshold_eq_zero_iff`, `liClockThetaResolventThreshold_pos_of_not_rh` |
| A nonzero reciprocal zero `p₀` of `Φ(1/p)` with `Re p₀=β` (evenness of `Φ`) | `exists_liClockThetaGenerator_inv_eq_zero_re_eq_threshold`, `liClockThetaGenerator_neg` |
| §2 rectangle growth `|r^{(m)}(t)|≤C_{δ,m}e^{δ|t|}` for every `δ>β` | `exists_abs_iteratedDeriv_liClockThetaResolvent_le`, `exists_abs_iteratedDeriv_liClockThetaCausalInverse_le` |
| (1) `∫e^{-pt}|r|<∞` for `p>β` | `integrableOn_exp_mul_abs_liClockThetaResolvent` |
| (2) `H(p)=1−1/Φ(1/p)`, `Φ(1/p)=1+K̂(p)`, `0≤H(p)≤1` for real `p>β` | `integral_exp_mul_liClockThetaResolvent`, `integral_exp_mul_liClockThetaResolvent_mem_Icc`, `integral_Ioi_liClockThetaKernel_mul_exp_neg_eq` |
| (3) undivided `(1−H(z))Φ(1/z)=1` on the whole half-plane `Re z>β` (complex convolution theorem; complex `K̂(z)=Φ(1/z)−1`) | `one_sub_liClockThetaResolventLaplace_mul`, `integral_Ioi_cexp_mul_liClockThetaKernel` |
| §3 critical divergence `∫e^{-βt}|r|=∞`; (4) `e^{-pt}|r|` integrable iff `p>β`, every real `p` | `not_integrableOn_exp_threshold_mul_abs_liClockThetaResolvent`, `integrableOn_exp_mul_abs_liClockThetaResolvent_iff` |
| §4 (5) `r₊+r₊⋆K=K+r₋+r₋⋆K` | `liClockThetaResolvent_signed_balance`, `liClockThetaResolventPos_sub_neg`, `liClockThetaResolventPos_add_neg` |
| (6) for `p>0`, `e^{-pt}r₊` integrable iff `e^{-pt}r₋` integrable | `integrableOn_exp_mul_liClockThetaResolventPos_iff_neg` |
| (7) `e^{-pt}r₊`, `e^{-pt}r₋` integrable iff `p>β`, every real `p` | `integrableOn_exp_mul_liClockThetaResolventPos_iff`, `integrableOn_exp_mul_liClockThetaResolventNeg_iff` |
| Both ordinary signed masses infinite; both signs occur cofinally | `not_integrableOn_liClockThetaResolventPos`, `not_integrableOn_liClockThetaResolventNeg`, `liClockThetaResolvent_frequently_pos_and_neg` |
| §5 under `β=0` (⇔ RH) the signed Laplace mass tends to `1` as `p↓0` | `tendsto_integral_exp_mul_liClockThetaResolvent_of_threshold_eq_zero` |

Proof-route notes: the undivided identity (3) is proved directly at every complex `z` with `Re z>β` from the complex convolution theorem (no identity-theorem continuation needed); the `p≤0` signed-mass cases use a truncation bound (`∫_0^T f ≤ e^{pT}∫e^{-pt}f`, `p↓0`) in place of monotone convergence. Conclusions are the card's.

## Log

- 2026-10-04 — Lean certificate audited; every numbered claim mapped to a declaration; moved to 3-formalized.
