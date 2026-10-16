# CHMD continuous literal orbit projections — 2026-10-16

Status: structural contribution FORMALIZED. Unconditional RH goal remains ACTIVE and unproved. Read user attachment on each new turn. No web, external novelty audit, old research Markdown, numerical experiments, subagents, full/umbrella builds, heartbeat increases, commits or pushes. Follow-up to `mem:rh/chmd-admitted-cardinal-packets-2026-10-16`.

Card: docs/drafts/pipeline/3-formalized/chmd-continuous-orbit-projections-2026-10-16.md.

## Closed obstacle
The prior actual cardinal frames had internal signed signatures, but no literal spectral readout representation against arbitrary completed graph vectors. This is now proved on the full original arithmetic SourceGraph, with no source regularity premise on the arbitrary vector.

For p with L2(mu) source v, mu=Phi*cosh(x/2) dx, define C_p(z)=integral Phi(x)*v(x)*cos(z*x) dx. The kernel cos(z*x)/cosh(x/2) is L2(mu) for every complex z by actual theta exponential moments. C is a continuous real-linear functional, its literal integral is absolutely integrable, and C is even/Schwarz symmetric.

For an actual Xi zero a with Re(a)>0 and its admitted CardinalGraphFrame F, let A(z)=1_{z=+/-a}, B(z)=A(conj z), M_a=sum mult*(A+B)/2. M_a>0; M=Kplus at real a and 2*Kplus at nonreal a. Exact universal identities:
  sourcePair p F.reVector = M_a*(C_p(a)).re
  sourcePair p F.imVector = M_a*(C_p(a)).im.
Proof first polarizes compact/cardinal sources with explicit diagonal summability plus finite cross support; both polar cancellations retained. Continuity and dense_compactTests extend to all p. This is not an assumed representation/completeness premise.

Projection P_a p = Re(C_p(a))*F.reVector for real a; otherwise 2*Re(C_p(a))*F.reVector - 2*Im(C_p(a))*F.imVector. It is a continuous real-linear map, preserves C_p(a), is idempotent, fixes its frame directions, has exact rank-one/rank-two range descriptions, is primitive and signed symmetric, and gives E(p)=E(Pp)+E(p-Pp). Nonreal projected energy is 4*Kplus*(Re(C)^2-Im(C)^2); real energy Kplus*Re(C)^2. Distinct four-point orbits mutually annihilate. Actual signed-radical vectors have C_p(a)=0 at EVERY Xi zero. Real-orbit imaginary frame vector lies in full radical (no nonzero claim).

Canonical actual family: PositiveXiZero={a:Complex // 0<a.re and XiC a=0}; literalOrbitFrame chooses the already proved actual frame; literalOrbitProjection needs no user-supplied frame. literalOrbitProjection_splitting packages sample preservation, idempotence, primitive status, energy split. exists_nonzero_literalOrbitProjection is premise-free, via an actual positive real Xi zero.

## Seven wired leaves, 955 lines, 94 explicit declarations
- CHMDGraphCosineReadout: cosineKernel_memLp; graphCosineReadout; continuous_graphCosineReadout; integrable_graphCosineReadout_source; graphCosineReadout_eq_integral / of_source / neg / conj / real.
- CHMDCompactSourceClass: compact_expMomentSource, compact_expDecayTest, compact_source_lipschitz, compact_source_thetaBound.
- CHMDCosineSourceFourier: ExpMomentSource.ofReal_re / integrable_paperFT_source; paperFT_add_sources; cosine_integral_eq_half_paperFT; graphCosineReadout_of_source_eq_half / of_even_source.
- CHMDCardinalIncidencePairing: cardinalOrbitWeight / Mass, finite summability and positivity, cardinalOrbit_mem_reverse, exact incidence extraction against even Schwarz C.
- CHMDCompactCardinalPairing: paperCosineReadout; cardinalCrossSummand; Wsummand_add_cardinal; cardinalCrossSum_re; signedZeroPair_cardinal (summability hypothesis discharged in compact wrapper); CardinalGraphFrame.compact_pair.
- CHMDUniversalCardinalPairing: CardinalGraphFrame.pair_re / pair_im, readout_re / readout_im, real_samples / nonreal_samples, readouts_outside_orbit, real_im_mem_signedRadical; radical_graphCosineReadout_zero.
- CHMDContinuousOrbitProjection: graphCosineReadoutCLM, CardinalGraphFrame.orbitProjection and its full splitting/range/energy/symmetry/annihilation identities; canonical actual family and nonzero instance.

## Verification / cleanup
All seven `lake --old build <leaf>` passed without own warnings. Every final plain `lake env lean <leaf>` passed sequentially, seven empty logs. 88 explicit `have := @Name` API probes passed. #print axioms on all 94 new declarations: only propext, Classical.choice, Quot.sound. All seven umbrella imports present exactly once; package root reaches theorem-area umbrella via MainTheorems. Guarded formal_tools.py index exited 0 and generated API records for the new declarations.

GLOBAL LINT LIMITATION: two runs of scripts/formal_tools.py lint exited 1 due unrelated concurrent modules initially not wired. EvenSectorPolarCompletion was subsequently wired by its owner. Latest run has exactly one error: owned module unreachable from RHTower umbrella: GaloisForLFunctions.RHTower.PaperThetaSpatialSolvability. Observed its separate owner's active Lean build; do not overwrite that work. No new CHMD leaf has a lint error. Existing large-file warnings remain. No full or umbrella build was run.

All owned handles terminal; all 25 owned /tmp search, probe, build and audit artifacts deleted. Verified build artifacts retained. Card moved to 3-formalized. Overall goal NOT completed or blocked.

SHA256:
CHMDGraphCosineReadout e3c9b4d5bdee75e0e24638c8a1f4bd4e85da47acf0975f1678034e9e98b689eb
CHMDCompactSourceClass 09116ae973c038d982872d4e32b70379e4867950b98f8de3d0825d125bb7c5aa
CHMDCosineSourceFourier 237c47899770cafd3a6ac1664738c8cb63982d5c86b99b43009c553587744974
CHMDCardinalIncidencePairing 0687549a0600e89fa2b23de47739d5219b796ebdc836c1cc965c2bed76f76c50
CHMDCompactCardinalPairing 0f896b9cf681d1eba2027dfb99a483d4317aeca3da6dd459ab241279ecfd3be8
CHMDUniversalCardinalPairing 2e8b7bab6ca2280576c00fcd5cc63ffac06f1b7779156acb7fb7ab443127db44
CHMDContinuousOrbitProjection 9fd6300725a46e1dd3d038a380b81db00784f87aa867a6d5f6d759c12e2d38bb

## Research audit / next conjecture
This closes the completed-graph domain obstruction within the checked corpus. External novelty unassessed by explicit user instruction. No primitive positivity, global completeness, full radical classification, exclusion of nonreal zeros, or RH proved. The auxiliary bounds serve the exact projection theorem; no standalone improved bound is the claimed contribution.
Next structural conjecture: an even graph source with zero cosine samples at every Xi zero and zero polar cosine moment lies in the full signed radical. Need justified mixed zero-sum limit for arbitrary graph sources (or an independently proved completeness theorem); do not assume completeness. The all-plane kernel argument suggests uniformly continuous samples in the critical strip, but the mixed tail passage must be proved with actual compact-test decay/summability. Odd-sector detection remains separate. Treat this as an unproved next conjecture, search corpus before pursuing it.

## Lean lessons
Explicitly type complex Integrable proofs before integral_add; otherwise scalar/type metavariables can make identical-looking rewrites fail. Pi.add_apply is needed before rewriting a pointwise sum obtained from Integrable.add. Keep .method on same line as closing parenthesis; newline-separated dot parsed incorrectly. Complex.div_ofNat_re avoids norm_num expanding product real parts before incidence substitutions. For residual_pair_projection, rewrite F.orbitProjection_real/nonreal with explicit q, or rewriting first hits the inner projection of p and causes unification blowup. Normalize RingHom.id_apply in CLM map_smul'. Avoid add_comm in global simp over energy splits: it reorders graph sums before sub_add_cancel. Prove energy(0)=0 through sourcePair_self and sourcePair, since sourceEnergy unfolds to the closed-jump energy wrapper. Use generic zero_apply, not deprecated ContinuousLinearMap.zero_apply.