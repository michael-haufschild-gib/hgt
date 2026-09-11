# PW-B full original-source paired adjoint

- **ID:** PW-B-GAMMA-FULL-PAIRED-ADJOINT-2026-09-11
- **Stage:** 3-formalized
- **Status:** All four public theorems passed the final foreground scratch without diagnostics. Exact checked source promoted and wired once; targeted leaf build passed in124s. All public names indexed; final repository formal lint passed.
- **Scope:** Complete source pairing identity, before physical operator-domain closure or Xi occurrence. RH remains unproved.

Write g_z=M_z/Q, w=exp(-x-1/x)/x, P_z,v=w*conj(g_z)*g_v.
The original normalized forward generator is
A g_v(x)=integral_(h>0) exp(-h)*(g_v(x+h)-g_v(x))/h dh,
and the backward generator uses x/(1+h*x) in place of x+h.
The proved identity is

`integral_(x>0) w*conj(g_z)*A g_v`

`= integral_(x>0) w*g_v*conj(B g_z) + integral_(x>0) P_z,v*2log(x)`.

A g_v is already the actual complete coefficient current M'_v/Q, where the
prime here denotes parameter derivative, not coordinate derivative.
The new coordinate identity is instead (g_z)'=g_z-g_(z-1); its complete
bound admits the forward paired response and its cutoff limit.

## Proved original cutoff identity

Let F_delta be the forward paired response with h>delta, x>0. Let R_delta
be the backward paired response with h>delta, x>delta. Let E_delta be the
paired oriented response integral from a_delta(x) to delta on x>delta,
where a_delta(x)=delta/[x*(x-delta)]. Let C_delta be the paired constant
contact and L_delta the previously retained empty incoming constant loss.
For0<delta<=1 the exact identity is

`F_delta=R_delta+E_delta+(C_delta-L_delta)`.

Proof assembly:

1. Forward response equals full gain minus
   E1(delta)*integral_(x>0)P_z,v.
2. The measure-preserving shear (x,y)->(x,y-x) and admitted Fubini retain
   the original triangle0<x<y-delta. The injective reciprocal Jacobian
   maps it to h>a_delta(y), retaining the complete source.
3. The transported gain is the backward response at cutoff a_delta plus
   P_z,v*E1(a_delta). This is the exact complete-source difference identity.
4. Difference of admitted response tails gives R_delta+E_delta.
   Difference of admitted exponential tails gives the constant contact,
   so the remaining gain is C_delta+E1(delta)*integral_(x>delta)P_z,v.
5. Split the original source integral at delta. Its removed interval is
   exactly L_delta, with its original sign.

All inner and outer integrals are individually admitted. In particular,
no Bochner integral identity is used to conceal failed admission. Existing
paired-contact and paired-response leaves admit the right side; the
[original gain proof](pw-b-gamma-adjoint-gain-transposition.md) admits both triangular and reciprocal inner sections
and both outer integrals.

Then F_delta converges to the admitted actual forward current pairing;
R_delta converges to the admitted backward pairing; E_delta tends to zero;
and C_delta-L_delta tends to the retained2log pairing. Uniqueness of limits
gives the displayed full source identity. Its backward term is exactly
the original arithmetic current at the reciprocal coordinate:

`B g_z(x)=SameSourceCurrent_z(1/x)/Q(1/x)`.

The final theorem displays both original arithmetic currents and proves
absolute admission of both pairings and the logarithmic contact separately.

## Lean verification

Leaf: `ThetaCuspHawkingParikhWilczekGammaFullPairedAdjoint.lean`.
Scratch: `/tmp/pwb-gamma-full-paired-adjoint.lean`.
Public theorems:

- `pwGammaMobiusPaired_original_cutoff_identity`;
- `pwGammaMobiusPaired_original_adjoint`;
- `pwGammaMobiusPaired_original_current_adjoint`;
- `pwGammaMobiusPaired_original_current_admission`.

The final adjoint and admission statements hold for every complex z,v with
no balance, zero-location or cutoff premise. Scratch and targeted leaf build
passed; no full/umbrella build or numerical experiment was used.

## Remaining RH scope

This is a paired integral identity on the complete arithmetic source
family. A full physical operator adjoint still requires its common domain
and closure/density analysis. The physical necessity of this pairing, a
different justified Xi occurrence and independently forced fixed-grade Ward
balance remain open. The previously excluded corrected Gamma scalar ansatz
is not restored by an adjoint pairing identity.
