# Rigidity of the prime kinks under positive-definiteness of the lag function

**Object.** As in `../lag-function-pd-horizon/`: `Φ = Φ_arch + Σ_n 2Λ(n)n^{−1/2}sinh((|L|−log n)/2)_+`, RH ⟺ Φ positive-definite.
Perturb ONE prime power `n₀` (position `log n₀ → log n₀ ± ε`, or weight `× (1 ± ε)`), all other prime powers exact, and
find the largest `ε` for which the `500×500` Toeplitz matrix of the perturbed function on `[0, 6]` stays positive
semidefinite (`pd_rigidity.py`, runpod, 16 cores, ~30 s per prime power).

**Result** (`pd_rigidity.log`). Baseline: the unperturbed prime-side `Φ` is numerically positive semidefinite on every
window `[0,L]`, `L ≤ 8`, with smallest eigenvalue `1·10⁻³ … 2.7·10⁻³` (a prime-only confirmation of Weil positivity for
this family). Tolerances: `ε ≈ 1·10⁻⁵ … 4·10⁻⁴` for all 18 prime powers `≤ 32`, in both directions and for both
position and weight; larger only for the smallest kink weights (`n₀ = 16, 27, 32`).

**Interpretation (theorem under RH, elementary).** The tolerance is a grid-limited shadow of an exact continuum
rigidity: on any window `[0,L]` the Toeplitz operator of `Φ` is `Σ_ρ |ρ|^{−2}|e_γ⟩⟨e_γ|`, trace class, with no spectral
gap (its spectral measure is atomic with density `~ log ξ/(2πξ²)` at frequency `ξ`), while a single-kink perturbation
has a signed absolutely continuous transform `~ ε·w·sin(ξ log n₀)/ξ`, which dominates `log ξ/ξ²` at high frequency and is
negative on half of every period. Hence for every `ε ≠ 0` there are test functions on the window on which the perturbed
form is negative: positive-definiteness pins the position and the weight of every prime power exactly, given the others.
A finer grid (Nyquist frequency `~ (1/ε)log(1/ε)`) makes the measured tolerance arbitrarily small. Recorded as MUST-234.
The baseline smallest eigenvalue is likewise a discretisation artefact of the same gapless operator; the continuum
positivity is marginal (infimum of the spectrum `0` on every window), which any producer must reproduce.
