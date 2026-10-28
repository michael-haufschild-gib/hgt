# The matched prime place has a Hodge index on the p-adic classes

- **ID:** rapt-matched-prime-place-hodge-index-on-classes
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Walls ledger §4 ("local Lorentzian structure at a prime: absent"), ALG local factors,
  RAPT tower forms; continues `rapt-archimedean-place-pays-the-tower-deficit`.
- **Statement:** For every prime `p`, depth `J` and `0 < η ≤ min(1/2, log p/4)`, eventually in `M` the
  form `P_M − (log M − γ − η)|·|²` on the span of the class pole vectors `w_0, …, w_J` has at most one
  positive square (hyperbolic); on the polar hyperplane `ℓ = 0`,
  `P_M(x) ≤ (log M − γ − g_J log p + 2η)|x|²`, `g_J = Σ_{j ≤ J} p^{−j}`.

## Proof

Keep the Laplacian in the Metzler stability identity of the valuation Gram (weight `1`):
`qf G a = Σ rowSum·a² − ½ Σ m_{max}(a_j − a_k)²`, rows `≤ 0`. Since masses descend,
`m_{max(j,k)} ≥ m_j m_k/m_0`; the complete-graph identity gives
`½ Σ m_j m_k (a_j − a_k)² = S Σ m a² − (Σ m a)²`. Insert into the class finite part (RAPT) with
`ℓ(x) = Σ a_j m_j` and `S/m_0 → g_J` (`m_j − p^{−j} m_0 → −δ_j j log p`, `m_0 → ∞`).
Hyperbolicity: nonpositivity on `ker ℓ` (ALG `isHyperbolic_of_nonpos_on_ker`).

## Significance

The raw prime kernel has two positive squares on a ladder; matched against the archimedean
counterterm `log M − γ` it has exactly the Hodge-index signature on the torsion-orbit (class)
space, with the pole as positive direction and gap `g_J log p → p log p/(p − 1)` (`≥ 2 log 2`).
Positive survivor of the "no local Lorentzian structure" verdict. Numerically the whole top of
the spectrum of `P_M` matches: `λ₁ − log M → −γ`, `λ₂ − log M → −(γ + 2 log 2)`,
`λ₃ − log M → −(γ + (3/2) log 3)` (M up to 32000), i.e. `log M − spec(H_Q)` with
`spec(H_p) = {γ} ∪ {γ_p + k log p : k ≥ 1}`.

## Status

Lean: `formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/TheMatchedPrimePlaceHasAHodgeIndexOnTheClasses.lean`
(`sum_cross_add_gap_le_valuation`, `polarFunctional_classCombination`,
`eventually_sum_classMass_ge`, `eventually_atomicWeilForm_classCombination_gap_le`,
`qf_classHodgeGram`, `eventually_isHyperbolic_classHodgeGram`). Exact-file check clean, axioms
`propext, Classical.choice, Quot.sound`, wired into the RAPT umbrella.

Open: multi-prime classes (Kronecker sum), all vectors (not only class combinations).
