# HB: literal retarded pulse and fixed-clock history

Status: five source theorems formalized; exact cached leaf audit passed. Complete radiative extinction remains open.

Proof chain: literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → original common Hawking-clock extinction → RH.

## Exact source law

Let P be `fullSourceOnsetPulse`, R the original `retardedNullAction`, and P_h(t,x,z)=P(t+h,x,z). For nonnegative p,w,h, the original source null coordinates give

    R[P](p+h,w)=R[P_h](p,w)+H_h[P](p,w),
    H_h[P](p,w)=integral_a=0..h integral_b=a..p+h+w K^d_{p+h,w}[P](a,b)
               -integral_a=0..h integral_b=a..p+h K^i_{p+h,w}[P](a,b).

K includes the original circular mean and factor 1/4. Source time and radius are (a+b)/2 and (a-b)/2 in both terms. The image changes the radial argument inside the kernel invariant only. Translating p,a,b by the same h preserves that invariant and translates the original source time by h. Source continuity justifies splitting each outer interval at h and translating both integration variables.

The actual pulse is supported in source ingoing time a in [0,1]. This proves

    R[P_{1+h}](p,w)=0,
    H_{1+h}[P](p,w)=H_1[P](p+h,w),
    R[P](p+1+h,w)=H_1[P](p+h,w).

The first identity discards the zero translated drive on the interior of the causal domain; endpoints have zero measure. The second splits the original history interval at 1 and removes the piece on which the literal source vanishes. The remaining radial bounds and kernels depend on target time. Neither the horizon contribution nor either direct/image history integral is declared zero.

All translations use the original physical coordinate and fixed onset. No source-dependent clock or frequency correction is introduced.

## What this resolves

A stationary kernel alone does not prove covariance of a fixed-origin causal action. The exact additional term is now proved for the literal pulse. Its entire late response has an exact integral over the original ingoing onset strip. This strengthens the earlier contact result: a zero source-contact translation moment does not by itself annihilate the propagated contribution.

## Open physical obligation

The theorem supplies a scalar source-response term. Its actual left-QNM projection, pulse/incoming cross currents, independent SS/SV/VV channels and retained spin-two terms still need a completed action calculation. The solved complete ++ and +- tensor equations are needed to remove changing metric weights. Horizon, cusp, exterior, temporal, characteristic and source-contact contributions must share the same prescription and orientation.

The sufficient final interface remains C_phys=-Sigma |D|² together with a source-derived Re C_phys>=0, or a strict bound -Re C_phys<=epsilon Sigma |D|² with epsilon<1. No such sign or strict bound is proved here. The proof of extinction from that interface is elementary positivity; assuming the interface's missing sign would not solve the source problem.

## Lean

Source: `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMRetardedPulseClock.lean`.
Namespace: `RHTower.D4BMRetardedPulseClock`.

- `pulseKernel_translation`: original kernel/source argument identity.
- `retardedPulse_translation`: finite causal action identity with both history terms.
- `shiftedPulse_retarded_action_zero`: actual late translated drive contributes zero on the original domain.
- `pulseHistory_fixed_onset`: history restriction to the original interval [0,1].
- `retardedPulse_late_history`: exact late response as fixed-onset history.

All public theorems use actual Xi occurrences and original source functions, without added source-equation, covariance, integrability or extinction premises. Private analytic helpers derive the needed continuity and finite integral substitutions.

See C13–C15 in [the active investigation](../1-in-progress/hb-fixed-clock-source-translation.md) for the paper proof, full interface and unsuccessful source-sign transfers.

Validation: scratch checked with `lake env lean`; final `lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingBMRetardedPulseClock` passed in 155 seconds without warnings. Twelve existing cache roots were reused; only the new leaf compiled. The finished leaf is wired into the umbrella without an umbrella or full build. Source SHA-256: `ba006ed0b56e7b91d1101c535ad7eb464bd29fbe0437c044048fdb7dc0fc581d`.

Static API index refreshed; formal lint passed with existing large-file warnings. The audited canonical `.olean` and `.ilean` are retained.
