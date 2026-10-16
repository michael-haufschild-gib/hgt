# EWU: the even pole-free cone now completes automatically

Supersedes the remaining pole-free lower-floor/double-pole gap after `mem:rh/ewu-detuned-evenization-source-uniqueness-2026-10-15`.

New modules:
- `GaloisForLFunctions.HTGeometry.HolomorphicQuadraticBoundary`
- `GaloisForLFunctions.RHTower.EvenSectorTwistedAbel`
- `GaloisForLFunctions.RHTower.EvenSectorPolarCompletion`

Unconditional capstone, with no premises: `RHTower.EvenSector.evenPolar_sourceCone_eq_full_sourceCone` proves `{lam | WeilPositiveEvenPolar lam} = {lam | WeilPositiveFull lam}`.

Main constructive implications (only intrinsic cone membership):
- `weilPositiveEvenAt_one_of_weilPositiveEvenPolar`: restores the missing pole direction at canonical weight.
- `weilPositiveFull_of_weilPositiveEvenPolar`: restores every compact complex test.
- `source_unique_of_weilPositiveEvenPolar`: lam(n)=vonMangoldt(n) for n>=2.
No coefficient sign, growth, convergence, lower-floor, Laurent, or Abel premise is added. Cone nonemptiness and RH are NOT proved.

Mechanism: detuned signed real Toeplitz forms split arbitrary complex coefficients into real and imaginary parts. Apply logarithmic unitary characters to get a harmonic density ceiling uniform in every real frequency. Signed Abel integration and the residue-one harmonic factor give s Re F(s+it)<=M on one common small neighborhood, where F(z)=sum lam(n)n^(-1-z) is holomorphic for Re z>0. `tendsto_sq_mul_re_zero_of_uniform_ceiling` uses a freely chosen fixed anchor d: Harnack on the disc centered at d with radius d-s/2 for G=2M/s-F yields -s^2 Re F(s)<=8Md+4ds|Re F(d)|+s^2|Re F(d)|. Choose d small first, then s. Thus the quadratic defect vanishes even without meromorphic continuation. Existing sharp untwisted ceiling and Abel correction complete the pole direction; existing even-to-full theorem finishes.

Rejected approaches: abstract codimension-one PSD extension is invalid; real-axis cosh doubling alone admits x*sinh(x/2), already formalized in ExposingRayCoshDoubling. Do not repeat those approaches or try to improve their constants. Uniformity in all frequency twists is decisive.

Reused `ExposingRayTransfer.positive_twisted_harmonic_bound` was made public in WeilWorkExposingRayCriticalTwists (proof unchanged).

Validation: all three new .oleans built using targeted foreground lake --old builds; final lake env lean audits of all three leaves and the changed reused-lemma leaf passed without warnings. Eight key #print axioms audits show only propext, Classical.choice, Quot.sound. No added axioms, sorry, numerical experiments, native computations, or heartbeat changes. Both area umbrellas wired; index refreshed. Global lint at audit time had only an unrelated concurrently added unwired PaperThetaSpatialSolvability module.

Paper proof, rejected conjectures, and final audit record: `docs/drafts/pipeline/3-formalized/ewu-pole-free-harnack-completion-2026-10-16.md`. No old research markdown or external novelty search was used.