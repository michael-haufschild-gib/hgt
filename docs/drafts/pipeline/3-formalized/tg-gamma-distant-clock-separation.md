# TG C9.16: local Gamma boundary invariant against all distant clocks

- **ID:** TG-C9.16
- **Stage:** 3-formalized
- **Type:** THEOREM (paper and Lean)
- **Route:** TG, joint-source Gamma endpoint/domain repair
- **Statement:** The literal clock-divided Gamma ground singularity cannot be canceled by arbitrary finite prime-polar ground additions supported away from clock zero.

## Exact physical probe and dependency-closed paper proof [PROVED HERE]

Use the actual corpus entries B_a(u), ground f_a, and covariance
<B_a(u),B_a(v)>=2a exp(-max(u,v)). For a>0 and eps>0 write
S_eps=B_a(0)-B_a(eps), M_eps=2a(1-exp(-eps)), and define
Q_eps=M_(2eps) S_eps-M_eps S_(2eps).

Direct use of the covariance proves
||Q_eps||^2=M_eps M_(2eps)(M_(2eps)-M_eps).
It also proves <Q_eps,B_a(u)>=0 whenever u<=0 or u>=2eps.
The actual dilation formula D_exp(u)f_a=exp(u/2)B_a(u) therefore gives
annihilation of each literal dilation at such a clock, including the
identity at zero. No assumption on coefficients, number of terms or
cancellation among distant clocks is involved.

For the actual symmetric difference F_a(u), for u>=eps,
<Q_eps,F_a(u)>=-2a M_eps exp(u/2)(exp(-u)-exp(-max(2eps,u))).
This has one sign and is zero for u>=2eps. Consequently for any R>=2eps,
<Q_eps,K_(eps,R)f_a>=-integral_[eps,R] J_eps(u)du, where
J_eps(u)=2a M_eps exp(u/2)(exp(-u)-exp(-max(2eps,u))) gamma(u)/u>=0.
Compact-interval continuity justifies the literal Bochner pairing.

Assume 0<eps<=1/2. On [eps,3eps/2], M_eps>=a eps and
exp(u/2)(exp(-u)-exp(-2eps))
=exp(-u/2)(1-exp(-(2eps-u)))>=eps/8.
Indeed exp(-u/2)>=1/2 and, for 0<t<=1, 1-exp(-t)>=t/2;
here eps/2<=2eps-u<=eps. Also gamma(u)/u>=1/(4u^2)>=1/(9eps^2).
Thus J_eps(u)>=a^2/36 on that short interval, and its full integral
is at least a^2 eps/72. Since M_eps<=2a eps and M_(2eps)<=4a eps,
the exact norm identity gives ||Q_eps||^2<=32a^3 eps^3.

For EVERY vector W_eps annihilated by Q_eps, Cauchy-Schwarz now gives
 eps ||K_(eps,R)f_a+W_eps||^2 >= a/(32*72^2).
The only role of this explicit constant is to certify inverse-cutoff
energy growth. In particular the norms diverge as eps->0+, even when
the distant-clock coefficients depend arbitrarily on eps and have no
uniform bound.

The native finite prime-polar sources are annihilated once
2eps<=min(log 2,b): every prime clock is at least log 2; every continuum
clock is at least its fixed positive lower endpoint b. Negative dilation
directions and arbitrary identity counterterms are also annihilated.
Linearity moves the pairing through each finite prime sum and each
finite Bochner continuum integral. Thus these are actual source additions,
not modeled coefficients. All mixed contributions remain in the original
vector norm; none is deleted by a triangle upper bound.

## Positive survivor and scope

The exact annulus law is a new local source invariant: it extracts the
Gamma boundary signal independently of all arbitrary distant prime and
polar coefficients. The source-faithful replacement retains the forced
homogeneous Gamma reference and the admitted exact relative remainder
proved in C9.14. C9.15 identifies its scalar Gamma factor and normalization.
This is a no-go for raw bounded-ground joint assembly, not an RH
falsification or a retirement of TG. The unbounded reference domain,
actual full remainder response, arithmetic energy finiteness, Hardy
compatibility and strict sub-unit control remain open.

## Lean status

`formal/GaloisForLFunctions/RHTower/SoninGammaDistantClockSeparation.lean`
passes the required targeted command `lake --old env lean GaloisForLFunctions/RHTower/SoninGammaDistantClockSeparation.lean -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/SoninGammaDistantClockSeparation.olean`, exit 0 with empty diagnostics.
The joint energy theorem is `gammaPrimePolar_joint_energy_lower`; the full
arbitrary-cutoff norm divergence is `gammaPrimePolar_joint_norm_tendsto_atTop`.
All eleven public foundation queries pass with only propext, Classical.choice
and Quot.sound. Umbrella wired; index exits 0, all eleven declarations present.
Global lint exits 1 on thirteen unrelated unreachable leaves, with no finding
in this module; exact diagnostics: `/tmp/tg-c916-lint.log`. Final leaf diagnostics
are empty. Audit closed 2026-10-04.
