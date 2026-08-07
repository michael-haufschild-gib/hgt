# Cofinal essential-phase Sonin coupling nonannihilation — formalized

- **ID:** `cofinal-essential-phase-sonin-coupling-nonannihilation`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Scientific status:** `[LEAN-PROVED] [CORPUS-NEW] [EXTERNAL NOVELTY PROVISIONAL] [NOT RH]`
- **Paper proof:**
  `../../2-fully-proven/new_scientific_knowledge/sonin/cofinal-essential-phase-sonin-coupling-nonannihilation.md`
- **Status:** unconditional; no `sorry`, `admit`, `axiom`, `opaque`, or `unsafe`

## Lean modules

The construction runs across the packet stack, from the bump to the boundary corona:

- `formal/GaloisForLFunctions/RHTower/SoninAnnulusBump.lean`
- `formal/GaloisForLFunctions/RHTower/SoninAnnulusPacket.lean`
- `formal/GaloisForLFunctions/RHTower/SoninCosineRiemannLebesgue.lean`
- `formal/GaloisForLFunctions/RHTower/SoninAnnulusPacketAsymptotics.lean`
- `formal/GaloisForLFunctions/RHTower/SoninPacketL2.lean`
- `formal/GaloisForLFunctions/RHTower/SoninPacketCompactVanishing.lean`
- `formal/GaloisForLFunctions/RHTower/SoninPacketFourierEscape.lean`
- `formal/GaloisForLFunctions/RHTower/SoninPacketFourierConcentration.lean`
- `formal/GaloisForLFunctions/RHTower/SoninCouplingPacketLimit.lean`
- `formal/GaloisForLFunctions/RHTower/SoninCouplingNonannihilation.lean`
- `formal/GaloisForLFunctions/RHTower/SoninStrictApertureCurvature.lean`
- `formal/GaloisForLFunctions/RHTower/SoninCouplingAdjointLimit.lean`
- `formal/GaloisForLFunctions/RHTower/SoninCouplingPartialUnitary.lean`
- `formal/GaloisForLFunctions/RHTower/SoninMellinBlindness.lean`
- `formal/GaloisForLFunctions/RHTower/SoninCouplingOperatorNormFloor.lean`
- `formal/GaloisForLFunctions/RHTower/SoninNormalizedPacket.lean`
- `formal/GaloisForLFunctions/RHTower/SoninBoundaryCorona.lean`
- `formal/GaloisForLFunctions/RHTower/SoninBoundaryTransition.lean`
- `formal/GaloisForLFunctions/RHTower/SoninCoronaBanach.lean`

The paper card carries the complete module list and the full statement-to-declaration table.

## Formal theorem chain

1. `soninAnnulusBump` is an even smooth nonnegative bump strictly inside `b < |x| < c` with
   positive mass, so the profile of `(1)` exists.
2. `soninPacket` is its cosine modulation corrected to zero mean; `soninPacket_zero` and
   `integral_soninPacket` are the two Meyer conditions `(2)`, so the family is an exact
   Poisson source test rather than an `L²` witness.
3. `tendsto_norm_evenFourierCutoff_soninPacketEven` and
   `tendsto_norm_sub_evenFourierCutoff_soninPacketEven_scaled` are the two spectral horns `(13)`:
   the packet leaves every band below the carrier and keeps everything above it.
4. `tendsto_norm_soninApertureCoupling_soninPacketEven_sub` is `(3)`: past the crossing threshold
   the coupling carries the packet to its inverse dilate.
5. `tendsto_norm_soninApertureCoupling_apply_soninPacketEven` and
   `eventually_one_sub_le_norm_soninApertureCoupling` give `(4)`, and
   `eventually_soninApertureCoupling_ne_zero` gives nonannihilation for every large clock.
6. `tendsto_norm_adjoint_soninApertureCoupling_soninDilatedPacket_sub`,
   `tendsto_norm_adjoint_mul_soninApertureCoupling_soninPacketEven_sub`, and
   `tendsto_norm_soninApertureCoupling_adjoint_soninDilatedPacket_sub` are `(4a)`, `(4b)`: the
   coupling is a partial unitary on the two packet classes.
7. `tendsto_pow_mul_norm_soninPacketMellin` is `(4c)`: every fixed Mellin exponent is blind to the
   family to all polynomial orders in the carrier.
8. `eventually_re_opTrace_evenSoninApertureRestrictionCurvature_neg` and
   `exists_scale_re_opTrace_evenSoninApertureRestrictionCurvature_neg` are `(5)`: strict negativity
   of the successive-aperture curvature at an actual dilation scale.
9. `soninNormalizedPacket` is the card's own `w = u/‖u‖`, with `norm_soninNormalizedPacket` and
   `eventually_soninPacketEven_ne_zero` making it a genuine unit vector,
   `soninNormalizedPacketFun_zero` and `integral_soninNormalizedPacketFun` carrying both Meyer
   conditions across the normalization, and
   `tendsto_norm_soninApertureCoupling_apply_soninNormalizedPacket` giving `‖Z_r w_r‖ → 1`
   verbatim.  `(3)`, `(4a)`, `(4b)`, `(4c)` are restated for the same unit family.
10. `SoninCorona`, `SoninCoronaSpace` and `soninBoundaryClass_soninCouplingFamily` realize `(19)`
    to `(21)`: the boundary classes of the two packet families are nonzero and the coupling acts on
    them as stated, inside a Hausdorff Banach corona.

## Meaning

The open nonannihilation horn left by Theorem Q of `sonin-principal-shell-cyclic-trace` is closed
by an explicit object, not by an abstract existence argument: a frequency-locked annular Meyer
wavepacket whose carrier runs with the clock while its support stays fixed.  On that family the
successive-layer coupling and its adjoint are mutually inverse isometries in the limit, so the
coupling cannot vanish at large scale and the aperture curvature is strictly negative there.

## Scope

This constructs a source-test mode at the cofinal phase-space boundary.  It does not land a Xi
conormal — indeed `(4c)` shows every fixed Mellin exponent is blind to this sector — and it is not
the missing RH theorem.

## Verification

- `lake env lean` passes on every module listed above;
- `#print axioms` on all 165 declarations named by the paper card, and on all 21 declarations of
  `SoninNormalizedPacket.lean`, returns only `propext`, `Classical.choice`, and `Quot.sound`;
- `SoninNormalizedPacket` is imported by `GaloisForLFunctions.RHTower`.

## Remaining frontier

Publication: standalone paper, external novelty audit against the Burnol and Israel–Mayeli
literature, and a citable Lean certificate.
