# Formalization record: ULF-GCP-1

- **Lean module:** `GaloisForLFunctions.HTGeometry.ConstitutiveGammaResponseLifetime`
- **Source:**
  `formal/GaloisForLFunctions/HTGeometry/ConstitutiveGammaResponseLifetime.lean`
- **Certified general theorem:** response-kernel transport for a composite linear response is
  surjective whenever its first response is surjective, and its zero fibre is exactly that first
  response kernel.
- **Certified Gamma theorem:** fixed-corona Gamma responses are surjective and additive; kernels
  equal the weighted ideals modulo the fixed ideal and form a monotone persistence filtration;
  total-to-earlier kernel transport is surjective with later kernel; damped Bockstein death occurs
  exactly for `|t| / 2 < s`; critical time survives;
  death-time infimum is exactly `|t| / 2`; centered lifetime equals distance from `1/2`.
- **Uncertified/open:** chain-level source-normal coframe conservation, scalar Xi landing, and RH.
- **Proof policy:** no `sorry`, `admit`, project postulate, unsafe declaration, or computation proof.
