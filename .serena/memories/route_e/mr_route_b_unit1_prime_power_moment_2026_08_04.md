# MR route-B unit 1 built: variable-ℓ prime-power adapted moment (2026-08-04)

Card: `docs/drafts/pipeline/1-in-progress/mr-splice-wide-range-mean-square.md`.

Built `RHTower/Sieve/PrimePowerSupport.lean` (wired, build 8802 jobs pass, axioms only
propext/Classical.choice/Quot.sound, zero warnings):
- `powIdx {N ℓ} : (Fin ℓ → Fin N) → Fin (N^ℓ)` product index + `powIdx_val_add_one`;
- `dirPoly_convPow : dirPoly (N^ℓ) (convPow N ℓ a) t = (dirPoly N a t)^ℓ` — pi-type expansion via
  `Finset.prod_univ_sum` + `Fintype.piFinset_univ`, phases via `Real.log_prod` (signature: takes
  ONLY the nonvanishing hypothesis, s and f implicit) and `Complex.exp_sum`;
- support-filtered mass bound and `powFibreOn_primeSupport_card_le` (≤ ℓ^ℓ via anchor image +
  `Prime.dvd_finsetProd_iff` — non-deprecated name, NOT dvd_finset_prod_iff);
- `volume_largeValues_pow_symm_le_of_prime_support`:
  V^{2ℓ}·meas{t ∈ [-T,T] : V ≤ |F|} ≤ 2(T + 4N^ℓ(1+log N^ℓ))·ℓ^ℓ·(∑‖b_p‖²)^ℓ, any ℓ ≠ 0.
  The fibre-9 sixth moment (PrimeCubeSupport) is the ℓ=3 special case.

Consumer (route B, MR note appendix): the well-spaced count |𝒯| ≪ exp((logX)^{1/48+o(1)}) for
short prime polynomials with N = e^{(j+1)/H}, ℓ ≈ logT/(j/H) so N^ℓ ≍ T; the ℓ^ℓ cost is the
tolerable exp(ℓ log ℓ).

Lean traps: `Finset.sum_filter_of_ne` with a ∀-shaped predicate needs `refine (….symm)` + intros
(a fused lambda mis-unifies the predicate); `rw [hg]` on a `set`-abbreviation leaves an un-beta'd
application — use `simp only [hg]`; empty-case `simp; omega` can close early — use
`rw [he, Finset.card_empty]; exact Nat.zero_le _`.

Next: unit 2 = spaced-count corollary (measure → well-spaced points, `DirichletLargeValuesCount`
pattern at variable ℓ); audit AlmostOrthogonality/CharacterSeparation for the [4,L11] duality;
then numeric re-certification of full route-B bookkeeping before assembly.
