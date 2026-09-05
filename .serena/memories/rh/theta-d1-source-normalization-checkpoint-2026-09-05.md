# Literal theta D1 — verification debt

Card: `docs/drafts/pipeline/1-in-progress/theta-d1-refined-parabolic-box.md`. No literal source sign or RH architecture has been proved by this work yet.

Verified scratch caches:
- `HgtTCDCleanJetForms`: exact integer-normalized source jets 0–4.
- `HgtTCDCleanHigherJetForms`: jets 5–8.
- `HgtTCDDeterminantForm`: unchanged full determinant `intD1Form.property`.
- `HgtTCDSourceRealForm`: exact source determinant evaluation in independent real U,B,Q.
- `HgtTCDExplicitRealForm`: exact candidate coefficient evaluation in independent real a,t,u.
All source files and oleans are in `/tmp`. Jet-8 and determinant axiom audit reports only propext, Classical.choice, Quot.sound.

Important compiler diagnosis: earlier `intJetFormN` equalities were valid but NOT reduced polynomial forms. Partial derivatives of numeral constants survived simp, multiplying at each jet. Explicit `OfNat.ofNat` unfolding before `Derivation.map_natCast` makes numeral simplification match. Merely adding a generic numeral derivative lemma did not match.

Unverified: `/tmp/HgtTCDLiteralIdentity.lean` identifies source evaluation at the exact physical box with `8^12 * evalNestedRat a (10*r^2/19) u explicitEvenChartD1`. Its latest proof uses the two cached real evaluations and one final ring equality. `/tmp/HgtTCDLiteralPositivity.lean` is also still an unchecked draft. Do not promote or claim global D1 until both pass.

Earlier 25-channel Bernstein positivity and actual-orbit admission caches are verified; reuse them. No full/umbrella builds. Finite D1 is not theta-specific cofinal Xi incidence: complete reflected-Hankel real-rootedness is formally false.
