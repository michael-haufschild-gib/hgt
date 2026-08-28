# FZZ-P argument-dilation dark-orbit no-go (HC39, 2026-08-28)

Formalized
`GaloisForLFunctions.RHTower.FZZCigarParityArgumentDilationDarkOrbitNoGo` and retired pure positive
argument dilation as a Ward-charge producer.

For actual dilated source response `M_r(s)=Mellin[t ↦ fzzParityDelay(r*t)](s)`, proved
`M_r(s)=r^(-s)M(s)` and the character is nonzero for every `r>0`. Therefore darkness at one scale,
at any scale, and at all positive scales are equivalent. Every Xi divisor copy has an unconditional
all-scale literal FZZ dark orbit, irrespective of horizontal position. Adding HC38 shared Ward
cancellation on those already-dark orbits is exactly equivalent to RH.

Formalized positive survivor: complete positive-dilation dark-orbit classification. Viable FZZ/GFZZ
producer must break pure Mellin argument covariance through a nonmultiplicative boundary,
interaction, recoil, or cross-response channel.

Verification: direct Lean check passed; targeted module build passed (8824 jobs); all seven public
theorems use only `propext`, `Classical.choice`, `Quot.sound`; lint had no HC39 finding; module wired
into RHTower umbrella without full umbrella build. Frontier map remained read-only.
