# Arbitrary-complex-translation (coset) elliptic-gamma chain — BUILT 2026-08-20

Card: `2-fully-proven/new_scientific_knowledge/other/all-depth-compatible-pair-face-differential-matroid`
(its new content over the structural theorem is *arbitrary complex translations*, not just the
`ℤ`-span of the hierarchy parameters).

## What is now Lean-certified (all axiom-clean, umbrella-wired)

New notion: `CosetSeparated τ A` — labels in `A ⊆ ℂ` are pairwise inequivalent modulo
`fullPeriodLattice τ = ℤ + ∑_i ℤ τ_i`.  Packet: `cosetFacePacket τ hτ A J` = translates of the
face coordinate by `cosetFaceShiftSet τ A J = A + faceShiftLattice τ J`.

Module chain (each mirrors the unlabelled one, label inert):

| new module | mirrors |
|---|---|
| `EllipticGammaTranslateOrbitSeparated` | *new*: base-point-free order-one orbit theorem |
| `MultipleEllipticGammaCosetFacePacket` | `MultipleEllipticGammaFacePacket` |
| `MultipleEllipticGammaCosetBottomFace` | `FaceShiftLatticeNonresonance` |
| `MultipleEllipticGammaCosetBottomStar` | `BottomFaceCrossSeparation` + `BottomFaceStarIndependence` |
| `MultipleEllipticGammaCosetFaceDisjointness` | `FaceDepthRigidity` + `MultipleEllipticGammaFacePacketDisjointness` |
| `MultipleEllipticGammaCosetFaceField` | `FacePacketFieldStability` + `FacePacketFieldTranslation` + `MultipleEllipticGammaFacePalette` |
| `MultipleEllipticGammaCosetDifferenceSystem` | `FacePacketDifferenceSystem` |
| `MultipleEllipticGammaCosetFreeTelescoping` | `FacePacketFreeTelescoping` |
| `MultipleEllipticGammaCosetLayerGluing` | `FacePacketLayerGluing` + `FaceLayerOffStarDisplacement` + `FaceLayerDescendingUnion` |
| `MultipleEllipticGammaCosetTranslateInjective` | `FaceTranslateInjective` |
| `MultipleEllipticGammaCosetAllFaceIndependence` | `MultipleEllipticGammaAllFaceIndependence` |
| `MultipleEllipticGammaCosetCompleteDifferentialMatroid` | `MultipleEllipticGammaCompleteDifferentialMatroid` |

Capstones:
```
cosetProperFacePackets_diffIndepOn        all labelled packets of faces with ≥2 survivors are
                                          jointly differentially independent over ℂ
cosetSelectedFaces_differentialIndependent(_rationalBase)
cosetFacePacket_differentialAlgebraic_iff exact two-survivor phase boundary
cosetCompleteDifferentialMatroid(_rationalBase)
cosetCompleteDifferentialRank(_rationalBase)
```

## The one trick that made the bottom layer work

The corpus's order-one packet theorem needs each shift *individually* nonresonant, because it is
base-pointed at the untranslated `Ψ`.  With arbitrary labels one label class is the half-period
class, so that fails.  Fix: `ellipticGammaTranslateOrbit_diffIndepOn_of_pairwiseSeparated` —
rebase at a chosen `s₀ ∈ S` using `addTranslationMeroDifferentialAlgEquiv s₀` and
`HTGeometry.DifferentialAlgEquiv.diffIndepOn_image`; only *differences* of distinct shifts need to
be nonresonant.  Use this base-point-free form for any future translate-family work.

## Remaining for the card

The Stanley–Reisner orbit decomposition `(8)`–`(11)` (`B = ⊕_c R_c`,
`R_c/I_d = ⊕_{|J| ≤ d−2} x_J S[t_J^{±1}]`), i.e. the "universal cyclic carrier reduction": the
labelled analogue of `MultipleEllipticGammaStructuralSpanDecomposition`
(`multipleEllipticGammaStructuralTranslate_mem_span`).  The card calls (8)–(11) a
Stanley–Reisner `[BRIDGE]`; the corpus owns the unlabelled Laurent layer in
`StanleyReisnerLaurentRows` / `LocalizedStanleyReisnerMatroidRank`.
