# Exponential-wall/Xi tau projective-jet no-go (2026-08-25)

Formalized a source-specific irregular-RH obstruction.

For the unit-exponential cubic Stokes-wall Fredholm determinant D:
- D(0)=1, D'(0)=1, D''(0)=19/35.
- (log D)'(0)=1 and (log D)''(0)=-16/35.
- Projective log two-jet J(L)=-L''(0)/(2 L'(0)^2) equals 8/35 after every nonzero scalar irregular-time rescaling z ↦ cz.

For canonicalXiSeamLog:
- L'(0)=m₀/2, L''(0)=-m₁/2.
- J(L)=m₁/m₀².
- Existing corpus bounds m₀>1/25 and m₁/m₀<9/2000 give J(L)<9/80<8/35.

Therefore no c : ℂ makes canonicalXiSeamLog and log(D(c·)) equal as germs at 0. This kills scalar irregular-time rescaling as Xi bridge. Positive survivor/open core: construct a genuinely non-scalar deformation of even Stokes/monodromy data matching Xi's projective jet, then higher jets/divisor.

Lean:
- formal/GaloisForLFunctions/RHTower/RoutePPrimitiveGammaJuliaStokesExpWallXiTauProjectiveJetNoGo.lean
- imported by formal/GaloisForLFunctions/RHTower.lean
- card: docs/drafts/pipeline/3-formalized/route-p-exp-wall-xi-tau-projective-jet-no-go.md
- targeted lake env lean passed.
- #print axioms for all new theorems: only propext, Classical.choice, Quot.sound.
- global lint had only unrelated pre-existing HTGeometry umbrella reachability errors.
- no umbrella build run; scratch and temporary olean files removed.
- frontier map remained read-only.

Novelty audit: Bertola arXiv:0902.4716, Its–Lisovyy–Prokhorov arXiv:1604.03082, Yafaev arXiv:1511.04683; exact kernel/invariant comparison not found. Keep [CANDIDATE NEW SCIENTIFIC KNOWLEDGE] pending independent expert audit.