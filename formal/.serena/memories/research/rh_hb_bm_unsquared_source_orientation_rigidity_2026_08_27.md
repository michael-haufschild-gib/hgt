# HB unsquared-source orientation rigidity (2026-08-27)

Formalized:
- `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMSecondHarmonicUnsquaredSourceOrientationRigidity.lean`
- `docs/drafts/pipeline/3-formalized/bm-second-harmonic-unsquared-source-orientation-rigidity.md`
- umbrella wired; frontier map untouched/read-only.

New exact identities:
- BM complementary exponent: `λ_n(q)=4n+2+q`.
- normalized Mellin carrier at seed one: `C(q)=q²(q+2)/8` (from existing corpus identity).
- reflection is `q↦1-q`.
- after cancelling nonzero off-wall angular factor and clearing reflected exponent, literal unsquared source orientation compatibility reduces to
  `P_n(q)=u²+(56n+46)u+(40n+25)=0`, `u=(2q-1)²`.

New rigidity:
- Every Xi zero satisfying `P_n(q)=0` lies on `Re(q)=1/2`.
- Proof: off wall and nonzero Xi height imply `Im u≠0`; imaginary equation forces `2Re u + 56n+46=0`; real equation contradicts coefficient gap `(56n+46)²>4(40n+25)`.

New source classification:
- Literal unsquared source amplitude `A(Jq)=A(q)r_n(q)` iff critical wall.
- Literal unsquared-source reflected current vanishes iff wall.
- Universal vanishing iff RH.

Meaning:
Both Hermitian square and literal unsquared angular–Einstein source phase fail to provide needed off-wall Peierls orientation. Remaining producer phase must come from global retarded-minus-advanced response, augmented boundary pairing, or left-QNM functional.

Verification:
- direct Lean passed
- targeted build passed 11885/11885
- five exported theorems use only propext, Classical.choice, Quot.sound
- scratch removed
- novelty primary-source search found no analogue; priority provisional.