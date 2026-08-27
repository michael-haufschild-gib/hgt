# PW-B countable matrix three-moment no-go (2026-08-27)

Formalized module: `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingParikhWilczekCountableMatrixThreeMomentNoGo.lean`
Card: `docs/drafts/pipeline/3-formalized/parikh-wilczek-countable-matrix-three-moment-no-go.md`
Umbrella: imported by `formal/GaloisForLFunctions/RHTower.lean`.
Frontier map was treated read-only.

New classification:
- For `M : ℕ → ℕ → ℝ`, define three unconditional product-index moments over `ℕ × ℕ`: M, M*(d_i+d_j), M*d_i*d_j with PW shift d_k=4k(k+1).
- Under summability of exactly these three coefficient families, every countable residual energy is summable and equals m0*x^2+m1*x+m2.
- Full recoil energy is wall^2 times this quadratic.
- Identical darkness iff all three moments vanish.
- The existing exact four-chamber quadratic half-line cone remains the complete countable receiver cone; universal vanishing in it is RH-equivalent.
Thus absolutely summable countable/cofinal linear completion retains no invariant beyond the finite three moments.

Sharp genuine infinite-support dark witness:
w_n = 2^(-n) + 2*1_{n=0} - 4*1_{n=1}.
Lean proves sum w_n=0 and sum 4n(n+1)w_n=0 using corpus geometric second-moment theorem. M_ij=w_i*w_j is admissible, symmetric, nonzero on every diagonal n>=2, PSD on every finite principal section, has all three moments zero, and has identically zero full PW energy.

Verification:
- direct `lake env lean`: pass
- targeted module build: pass
- axiom audit: only propext, Classical.choice, Quot.sound
- no project axioms/sorry/admit/opaque/unsafe in module
- novelty audit provisional; corpus and primary literature searches found no countable PW grade-matrix classification or infinite-support PSD dark kernel.

Survivor: PW-B must use conditional/source-canonical renormalization, nonlinear/nonpolynomial grade interaction, an independent physical orbit/channel, or a literal pre-divisor source annihilation law.