# The top spectrum of the prime form is exhausted by the integers

- **ID:** rapt-exhaustion-of-the-top-spectrum
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** RAPT §9 topic 2 ("Open: exhaustion of the bounded renormalized spectrum");
  `0-backlog/rapt-top-spectrum-of-prime-form-is-log-integers.md`; RP37.
- **Statement:** For every `T > 0` and `ε > 0`, eventually in `N`, there are a finite set `S` of
  integers with `log m + d(m) < T` (`d` = `tameDifferent`) and vectors `v_m`, `m ∈ S` (`modeVec`),
  such that every `x` orthogonal to all `v_m` satisfies `P_N(x) ≤ (log N − γ − T + ε)|x|²`
  (`eventually_atomicWeilForm_le_of_modes`). So at most `#{m : log m + d(m) < T}` eigenvalues of
  `P_N` lie above `log N − γ − T + ε`. With `eventually_fullPrimeMatrix_eigenvalue_near` (an
  eigenvalue near each level), the spectrum within bounded distance of `log N − γ` is
  `log N − γ − {log m + d(m)} + o(1)`.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven
- [x] 2 → 3  formalized: axioms `[propext, Classical.choice, Quot.sound]`

## Proof

Work in the pole gauge `y = √n x` with the harmonic measure `1/n`. Write
`D = Σ Λ(t)/(mt)(y_{mt} − y_m)²`.

1. **Truncated ladder** (`TheTruncatedValuationLadderIsExactlySolvable`). On `{0..J}` with
   `w_j = p^{−j}`, take the modes `ψ_k = 1_{j≥k} − c_k 1_{j=k−1}` with
   `c_k = (1 − p^{−(J−k+1)})/(p − 1)`. They are orthogonal: `⟨1, ψ_k⟩ = 0` by the tail sum, and
   `ψ_k = 1` on the support of `ψ_l` for `k < l`. They are eigenvectors: `B(s_k, g)` and
   `B(e_{k−1}, g)` are computed in closed form (`ladForm_step`, `ladForm_single`), giving
   `B(ψ_k, g) = log p (k + c_k)⟨ψ_k, g⟩` (`ladForm_ladMode`). They are complete by induction on the
   tail sums (`eq_zero_of_ladInner_ladMode`). This gives the expansion, Parseval and the energy
   expansion.
2. **Finite box** (`TheFinitePrimeChainHasTheSpectrumOfTheIntegers`). Use the product modes
   `Ψ_m(a) = Π_{p<Q} ψ_{p,v_p(m)}(v_p(a))`. Induction over the primes: `boxEnergy_succ` splits off
   the top ladder; `sum_ladWeight_boxEnergy` uses coefficient Parseval. The result is
   `E(f) ≥ T‖f‖² − Σ_{λ(m)<T}(T − λ(m))⟨f, Ψ_m⟩²/‖Ψ_m‖²` (`boxSpectral`).
3. **Assembly** (`TheTopSpectrumOfThePrimeFormIsExhaustedByTheIntegers`).
   - The vectors `v_m` read `Σ_{a≤X}(1/a)Ψ_m(a)h_a`, where `h` is the fibre mean over the
     `Q`-smooth parts (`sum_mul_modeVec`).
   - Orthogonality kills the penalty and the mean (`smoothVar_mul_le_of_orthogonal`, via
     `smoothVar_mul_le_of_box`).
   - The two scales give the walk bound (`two_scale_le`, `le_of_two_scale`).
   - Box levels below `T − ε/8` are integers with `log m + d(m) < T` once `X` is large
     (`log_add_tameDifferent_le_boxEig`).

## Insight

Below its sharp counterterm, Weil's prime form realizes the multiplicative monoid spectrally. Its
bounded renormalized spectrum is that of the infinite product of valuation ladders,
`λ(m) = Σ_p λ_{p, v_p(m)}`, with no contribution from the horizon or from the infinitely many
large primes. Those cost at least `log Q/K`.

## Log
- 2026-10-28 — created; plan.
- 2026-10-28 — formalized; RP39.
