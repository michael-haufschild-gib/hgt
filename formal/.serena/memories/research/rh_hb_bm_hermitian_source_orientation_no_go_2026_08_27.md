# HB literal Hermitian-source orientation no-go (2026-08-27)

Formalized module:
- `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMSecondHarmonicHermitianSourceOrientationNoGo.lean`
- Card: `docs/drafts/pipeline/3-formalized/bm-second-harmonic-hermitian-source-orientation-no-go.md`
- Umbrella wired.
- Frontier map remained read only.

Let literal source amplitude be `A(q)=angularMix(q)*EinsteinCarrier(1, xiSpectralPoint q)`, and real Hermitian weight `w(q)=normSq A(q)`. Let forced cancellation ratio from prior classification be `r_n(q)=-λ_n(q)/λ_n(Jq)`.

Proved:
- `w(Jq)=w(q)r_n(q) ↔ Re(q)=1/2`.
- Off wall, angular mixing and carrier are nonzero, so `w(q)≠0`; imaginary parts contradict `Im r_n(q)≠0`.
- On wall, angular mixing is zero on q and Jq, so both weights vanish.
- Literal Hermitian reflected current `w(q)J_n(q)+w(Jq)J_n(Jq)` vanishes iff critical wall.
- Universal vanishing over Xi support iff RH.

Meaning:
Actual norm-square angular–Einstein source coefficient cannot realize missing off-wall complex Peierls orientation. Remaining producer must retain unsquared complex phase and transform reflection-covariantly.

Verification:
- direct lean passed
- targeted build passed 11884/11884
- all 3 theorems depend only on propext, Classical.choice, Quot.sound
- axiom scratch deleted
- no exact literature analogue found; priority provisional.