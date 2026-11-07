# Rank fourteen from a source-paid power core

- **Stage:** 3-formalized.
- **Statement:** For every `0<a≤1/2`, the complete signed theta Hankel section of rank fourteen is positive definite.
- **Payment:** For `deg P<14`, put `E=∫₋₁₂¹²(1−b²/144)^8 P(b)²`. Then `∫P² current ≥ aE/250`; `E>0` for `P≠0`.

The fourth reciprocal trace excludes zero ordinates through twelve. The complete reciprocal-square mass is below `1/18`, giving
`|(log Ξ)'(b)|≤b/[18(1−b²/144)]` and hence
`Ξ(b)≥Ξ(0)(1−b²/144)^4` on `|b|≤12`.
The on-line and off-line pair estimates retain `current≥(a/185)(1−b²/144)^8`.

The general power-weighted Legendre envelope gives
`P(b)²≤(220000000000/12^26)|b|^26 E` for `|b|≥66`.
The coupled exponential current bound pays the entire exterior by `aE/1000`.
Verified height 67 keeps the middle region nonnegative. Thus the complete signed integral retains the stated strict reserve.

Lean: `ThetaCuspSections/TheFourteenthSectionFromHeightSixtySeven.lean`,
`form14_lower`, `thetaCuspCenterMixedSignedHankel_fourteen_posDef`.
Final ordinary audit passed; both capstones use only `propext`, `Classical.choice`, `Quot.sound`. All supporting modules are wired into the umbrella.

The polynomial exterior theorem is valid for every degree and integer core power. Its scalar payment is established here through rank fourteen; higher ranks still require a sharper estimate or larger paid core.
