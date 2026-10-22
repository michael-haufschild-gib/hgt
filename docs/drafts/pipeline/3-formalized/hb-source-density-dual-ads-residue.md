# HB: source density dual and physical AdS residue

Proof chain: literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal/left-QNM action → fixed Hawking-clock extinction → RH.

The new result is an exact radial source intertwiner with its surviving boundary density. It does not prove extinction. The repaired auxiliary dual fails the naive identification with the original fundamental radial mode whenever its explicit source residue is nonzero.

## Exact source identity

Let u=-tanh x, x<0, s=physicalRate(q,branch), t=physicalRate(q,!branch)=-s-3, and lambda=rho(rho-1). Keep the literal half-square Q and its actual Laplacian LQ, including the complete gradient energy. At fixed original ingoing time v set

    F_s[J]=a² chi(v) exp(2sv) (1+u)^(2s) J,
    w(u)=(1+u)^5/u^4,
    G_t[J]=w(u) F_t[J].

The original source generator is D=partial_x/(u-1)+3. Put

    A0=(5lambda-6)/4,
    C=((4lambda+1)(lambda+2)-(lambda+4)Delta)/8,
    K=(7lambda-2-2Delta)/8.

Its common source operator is P=A0+u²C-u²KD. The original complex-bilinear formal transpose in measure u²du dXdy/y² is

    Pdagger=A0+u²C+(4u-u²)K+u²KD.

The radial profile is defined explicitly in the new leaf. Differentiation of the actual source gives

    D F_s=(2s+3)F_s,
    D G_t=(2t+4-4/u)G_t,
    dw/dx=(u-1)(1-4/u)w.

Substitute t=-s-3: the extra term (4u-u²)K cancels the weight correction, leaving the same angular coefficient as P F_s. The proved original-forcing dictionary is cross-multiplied:

    -2(1-u²)u F_s[1] Pdagger G_t[Q]
       =G_t[1] timeOriginalForcing_s(v-x,x,z).

No source amplitude, onset, tilt or angular value is divided out. The angular input is not replaced by a guessed spectral eigenvalue. This is an exact identity for the separated radial transpose profile. Identification with the full three-coordinate `transposeProducer` and its angular current is not asserted as a new Lean theorem here.

## Retained spin-two flux and boundary residue

Let R=-Delta(Delta-2), acting on the full Q. The original radial Green-density expression evaluated on this auxiliary test is

    J_u=-u^4(1+u) F_s[KQ] G_t[RQ]/y²
       =-a²b² chi(v)² exp(-6v) (KQ)(RQ)/y².

Proof: u^4(1+u)w=(1+u)^6 and the two complex radial powers multiply to (1+u)^(-6), since 2s+2t=-6. Both bases are positive real; complex power addition is justified. The two original time exponentials similarly combine to exp(-6v). Every angular factor remains unchanged. Thus this radial density is independent of radius, with equal endpoint values; no endpoint is set to zero. For v>=1 its fixed-clock translation is the exact decay factor exp(-6h), so compensating by that common factor preserves its coefficient rather than extinguishing it.

At the AdS face the proved limit is

    lim_(x→0-) u^4 G_t[Q]=b² chi(v)exp(2tv)Q.

Indeed the expression equals (1+u)^5 F_t[Q] in the exterior, and the latter is continuous at x=0. The full source residue is retained, including possible zeros at particular source points.

## Comparison with the actual physical radial modes

For every target Xi occurrence r and either original fundamental frequency w0, both original radial normalizations agree on x<0 with

    psi_left(x)=z^(w0/2)(1-z)^(1/2), z=1-u².

The existing connection and fundamental-mode identities supply this formula without a new spectral or boundary assumption. Since z→1 and 1-z→0, the new theorem proves psi_left→0 at the AdS face. Consequently, for any constant complex normalization c,

    lim_(x→0-) u^4 [G_t[Q]-c psi_left(x)]
       =b² chi(v)exp(2tv)Q.

Source and target occurrences are independent. This compares original radial modes, not an arbitrarily declared left state. It proves the exact surviving discrepancy; it does not assume the discrepancy vanishes or claim it is nonzero at every point. The physical radius lift introduces another known radial factor and does not justify replacing the singular auxiliary seed by a homogeneous left stream.

## Scope of the remaining extinction theorem

The completed physical left-QNM action must retain the solved ++ and +- quadratic corrections, all nine SS/SV/VV pairings, changing metric weights and the temporal, horizon, exterior, cusp, characteristic and source-contact faces. None of those unevaluated terms is canceled by this radial identity.

After independently identifying the completed action C_phys with the established reduced receiver -Sigma |D|², Sigma>0, a sufficient source theorem is Re C_phys>=0, or the strict estimate -Re C_phys<=epsilon Sigma |D|² with epsilon<1. Either gives (1-epsilon)Sigma |D|²<=0 and hence D=0. The literal source has not yet supplied that sign or estimate. Adding it as a hypothesis would leave the central problem unsolved.

The active C19 calculation records why the common producer cannot be passed through the physical wave inverse merely by formal transposition: its nonconstant radial derivative coefficient creates a second-derivative commutator. A corrected intertwiner must derive the temporal/onset terms and the original physical boundary transport before it can act on the complete nonlinear assembly.

## Lean validation

Module: `GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMSourceDensityDual`.
Namespace: `RHTower.D4BMSourceDensityDual`.

Seven public theorems cover the integrating-factor derivative, source-forcing identity, radial density, source AdS residue, spin-two radial flux, actual fundamental-mode endpoint and their exact difference residue. Six public definitions name the explicit source expressions. Source theorems quantify over actual Xi occurrences and geometric domain subtypes; no additional source law or vanishing assumption is introduced.

Scratch `lake env lean /tmp/hb-source-density-dual.lean` passed without warnings. Exact cached leaf audit passed in 134 seconds without warnings, compiling only this leaf against twelve existing cache roots. The module is wired once into `RHTower.lean`; no umbrella or full build was run.

Source SHA-256: `7aaa8794178e8c78a2fd7730ff30aa4f89340a4997cd7ef44a029d81158be629`. Static API index refreshed; all thirteen public declarations are indexed. Formal lint passed with existing large-file warnings. Canonical `.olean` and `.ilean` retained.
