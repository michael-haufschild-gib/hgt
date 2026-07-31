2026-07-30 recurrence master-law extension.

Exact new Lean module: formal/GaloisForLFunctions/HTGeometry/LBitTemporalDimensionLaw.lean, imported by HTGeometry.lean.

Core law for finite l-bit energy E_J(x)=sum_S J_S chi_S(x):
tau(J)=dim_Q span{J_S:S nonempty}. Load-bearing declarations:
- lbitGapSubspace_eq_coefficientSubspace
- lbitTemporalRank_eq
- lbitTemporalRank_le_order
- exists_lbitEnergy_maximal_uniformly_close
- lbitChargeMatrix_commutes
- exists_localizedTemporalDimensionExplosion
- card_mixedLBitSupports
- universalLBitFiniteRestriction_fullRank

Consequences:
- k-body truncation tau <= sum_{j=0}^k choose(n,j)-1.
- Arbitrarily small coefficient-L1 perturbation can reach tau=2^n-1 with uniform energy closeness, same diagonal eigenbasis, all l-bit charges conserved.
- Mixed two-block supports count (2^a-1)(2^b-1), exactly matching rectangle relation gain.
- One countable coefficient assignment (prime-log indexed) has full rank on every finite restriction simultaneously. This is not infinite-volume C*-dynamics.

Physical interpretation: exact localization and completed temporal dimension are independent; matter can be frozen in space while recurrence future becomes exponentially dimensional.

Boundary: call this exact l-bit/LIOM localization, not Anderson localization. No proof for ordinary finite-range random Anderson/MBL Hamiltonians or stability under microscopic local couplings. Strict finite interaction order cannot reach full exponential rank. Microscopic open core is nonidentity of every balanced integer eigenvalue relation over disorder/contact parameters.

Closest SOTA:
- Huse–Nandkishore–Oganesyan arXiv:1408.4297, all-order l-bit phenomenology and dephasing without flips.
- Prakash–Pixley–Kulkarni arXiv:2008.07547, Poisson SFF matches numerical MBL and l-bit models.
- Riddell–Bertini arXiv:2404.12100, rationally independent free fermions still fail Poisson higher SFF moments.
- Aizenman–Warzel arXiv:0809.3436, finite-range interacting multiparticle localization, but not rational relation erasure.

Verification:
target compiled with lake env lean and cached olean; #print axioms reports only propext, Classical.choice, Quot.sound. scripts/formal_tools.py lint failed only on unrelated pre-existing umbrella-reachability errors; new HTGeometry module was reachable. No stale Lean process left.

Research cards:
- docs/drafts/pipeline/3-formalized/lbit-temporal-dimension-law.md
- docs/drafts/pipeline/3-formalized/separable-interaction-temporal-dimension-law.md
- master card updated: docs/drafts/pipeline/1-in-progress/recurrence-relation-lattice-universal-law.md