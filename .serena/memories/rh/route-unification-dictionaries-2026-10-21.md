# Route unification dictionaries (2026-10-21)

Report: docs/reports/review-2110/route-unification-ledger.md (companion of walls-ledger.md, linked from its header). Card: docs/drafts/pipeline/3-formalized/route-unification-dictionaries-2026-10-21.md.

Principle: a route is fixed by the unit its receiver measures. Units: zero width (cluster A: WL, MC energy, PBM, SZ, TT, TH, HCF, PA, BAG, FU, HF window, SRT minimal, DR; endpoint-only LA, WD, XN, LI, RB, CTF, PM, FEL), aperture of window positivity (cluster B: RW, ACT, OWU, EWU, AIP, APT, SRT window/lag, TT odd, JAS level one, SZ core, CHMD odd eigenstates, HF prime-blind), per-zero side (cluster C: HJ, SEC, CDC, BSH, IRK, W1C, PCS, PTR + zero-indexed constructions), damped receiver (cluster D: MC, PM, CTF, BVI, MSC; FU, RP, LI by history), quantifier gap (cluster E: BAG, JAS, LA pairs, SRT grids).

Lean (formal/GaloisForLFunctions/SquareRootThreshold/, wired in the umbrella import block, axioms standard, oleans built):
- TheRoutesMeasureOneAperture: ZetaWindowPositive A; 0 ≤ μ(A) ⟺ ∀ A' < A window(A') (mollification into strict interior via CHMDDoobGraph.smooth with radius 1/(4(k+1)), re_weilFullFunctional_smooth_tendsto, Rayleigh GLB, continuity of μ); parity split; odd window ⟺ OWU sinh capacity at cutoff ⌈e^{2A}⌉; odd window ⟹ ACT single-shift (pole −2|F̂(i/2)|²); μ ≥ 0 ⟹ EWU blind min ≥ 0; SRT complex window transfer; Rayleigh lag bridge; RH ⟺ ∀A window ⟺ ∀A μ ≥ 0.
- TheRoutesMeasureOneZeroWidth: zetaZeroWidth ≤ σ ⟺ receivers of PBM, WL, MC/FU, TT, HCF, SZ, TH, PA, RW/HF (CCM tomography), BAG (recurrent disc right of ½+σ), projective reflection radius (= width); one-directional Lagarias at width σ and cos(hD)Ξ ∈ LP for h > width.
- TheZeroIndexedRoutesMeasureOneSide: per-zero indicators (HJ residual, seam charge, orientation defect, SEC jet boundedness, CDC confluence, BSH mate gain, IRK non-unit, W1C reality) ⟺ Re ρ = ½; global forms ⟺ RH.

Corpus repair: RHTower.norm_mobiusMertensPartialSum_eq duplicated in LiouvilleSummatoryRH and CausalMobiusThetaTail (both in RHTower umbrella, different statements); Liouville copy renamed norm_mobiusMertensPartialSum_eq_abs_sourcePartialSum_moebiusR, consumer SignedArithmeticAbscissaRH updated, oleans rebuilt.

Lint (scripts/formal_tools.py lint): my modules reachable; four in-flight modules of other lanes reported unreachable (PrimeSpanIsThePolynomialClosure, ZetaOrbitApproachesEveryAnalyticTargetWithTheHurwitzThreshold, ShortWindowMoebiusSavingIsTheQuasiRiemannHypothesis, PositionAndDepthShareOneNyquistAperture).

Open arrows: EWU and ACT converses at fixed aperture; PCS/PTR per-zero iff; Lagarias and cosine-shift converses; width ⟹ μ-floor (the only one that would be RH progress). User rules reaffirmed: README is foundational, not a ledger; frontier map read-only; no git.
