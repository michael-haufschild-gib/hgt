# Critical FZZ neutral-screening / Parikh–Wilczek recoil endpoint (2026-08-24)

User correction: Hawking route must use irreducible black-hole/string structures, not relabel classic RH criteria. Static FZZ puncture-dilation completeness, generic KMS/passivity/Krein/Cayley, and polylog/Lee–Yang relabelings were rejected.

New cross-source representation (algebra exact; identifying FZZ neutral depth with 4D PW recoil depth remains conjectural):
- FZZ cigar scattering charge m gives delay exp(-m t).
- Torus monodromy forces neutral W+W− depth k with coefficient μ^(2k)/(k!)².
- Parikh–Wilczek finite-mass recoil gives m^k t^(2k), Mellin jet Γ(s+2k)ζ(s+k).
- Hence fixed-charge paper series is exp(-m t) I₀(2 μ t sqrt(m)).
- Exponential rate: -m + 2 μ sqrt(m). Charge m=n+1 wall μ=sqrt(m)/2; its square equals exact PW endpoint action m/4.
- Global stability iff μ≤1/2; strict stability iff μ<1/2. At μ=1/2 only m=1 is marginal, with t^-1/2 tail.
- Forward critical Mellin tail power is Re(s)-3/2; reverse is -Re(s)-1/2. Both are logarithmic (-1) iff Re(s)=1/2.

Lean file created:
`formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingFZZNeutralScreeningRecoilEndpoint.lean`
and imported by `formal/GaloisForLFunctions/RHTower.lean`.

Open physical producer, explicitly conjectural:
actual critical neutral torus one-point insertion has one shared local logarithmic sewing counterterm for forward/reverse Mellin charts. If independent counterterms are allowed, route fails. Halder–Jafferis leave torus one-point open. Global sewing predicate is proved iff RH, but physical sewing is not proved.

Lean verification:
- direct module compile passed;
- targeted module build passed;
- all newly created public theorems use only propext, Classical.choice, Quot.sound;
- lint found only unrelated pre-existing HTGeometry umbrella reachability errors (HardyHorizontalLayerLeakage, HorizontalLayerBlaschke, HorizontalLayerLeakageLimit, HorizontalLayerProjective, ProjectiveBoundaryMultiplier).
- scratch files removed.
No git commands used.