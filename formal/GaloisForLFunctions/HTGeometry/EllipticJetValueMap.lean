import GaloisForLFunctions.HTGeometry.EllipticCountingTools

/-!
# The coefficient-to-data map of the elliptic counting argument

The counting argument compares the monomials `fⁱ (f')ʲ` against their principal parts.  The linear
algebra is done in coordinates: a coefficient vector indexed by the monomials is sent to the list of
principal-part coefficients at each pole representative, together with the value of the combination
at one chosen regular point.

Defining that map as the *combination of the jets* rather than the *jet of the combination* makes it
linear with no analytic hypotheses whatsoever; `principalJet_finset_sum` identifies the two when the
pole orders are cleared, which is where the analytic input enters — later, and only once.

* `diffMonomial` — the monomial `fⁱ (f')ʲ`;
* **`jetValueMap`** — the coefficient-to-data linear map;
* `card_jetValueTarget` and `card_jetValueSource` — its target and source dimensions;
* **`exists_degree_gt`** — a degree at which the source outgrows the target, which is the whole
  content of "quadratically many monomials beat linearly many principal parts".
-/

namespace GaloisForLFunctions.HTGeometry

/-- The differential monomial `fⁱ · (f')ʲ`. -/
noncomputable def diffMonomial (f : ℂ → ℂ) (i j : ℕ) : ℂ → ℂ :=
  fun z => f z ^ i * deriv f z ^ j

/-- **The coefficient-to-data map.**  A coefficient vector indexed by pairs of exponents is sent to
the principal-part coefficients of the corresponding combination at each pole representative,
together with its value at a chosen point.  Linear by construction. -/
noncomputable def jetValueMap (f : ℂ → ℂ) (S : Finset ℂ) (d N : ℕ) (z₀ : ℂ) :
    ((Fin (N + 1) × Fin (N + 1)) → ℂ) →ₗ[ℂ] (((↥S × Fin d) ⊕ Unit) → ℂ) where
  toFun c := Sum.elim
    (fun pk : ↥S × Fin d => ∑ q : Fin (N + 1) × Fin (N + 1),
      c q * principalJet (diffMonomial f (q.1 : ℕ) (q.2 : ℕ)) (pk.1 : ℂ) d (pk.2 : ℕ))
    (fun _ : Unit => ∑ q : Fin (N + 1) × Fin (N + 1),
      c q * diffMonomial f (q.1 : ℕ) (q.2 : ℕ) z₀)
  map_add' c₁ c₂ := by
    funext x
    cases x with
    | inl pk =>
        simp only [Sum.elim_inl, Pi.add_apply]
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun q _ => by ring)
    | inr u =>
        simp only [Sum.elim_inr, Pi.add_apply]
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun q _ => by ring)
  map_smul' a c := by
    funext x
    cases x with
    | inl pk =>
        simp only [Sum.elim_inl, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun q _ => by ring)
    | inr u =>
        simp only [Sum.elim_inr, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun q _ => by ring)

@[simp]
theorem jetValueMap_inl (f : ℂ → ℂ) (S : Finset ℂ) (d N : ℕ) (z₀ : ℂ)
    (c : (Fin (N + 1) × Fin (N + 1)) → ℂ) (pk : ↥S × Fin d) :
    jetValueMap f S d N z₀ c (Sum.inl pk)
      = ∑ q : Fin (N + 1) × Fin (N + 1),
        c q * principalJet (diffMonomial f (q.1 : ℕ) (q.2 : ℕ)) (pk.1 : ℂ) d (pk.2 : ℕ) := rfl

@[simp]
theorem jetValueMap_inr (f : ℂ → ℂ) (S : Finset ℂ) (d N : ℕ) (z₀ : ℂ)
    (c : (Fin (N + 1) × Fin (N + 1)) → ℂ) (u : Unit) :
    jetValueMap f S d N z₀ c (Sum.inr u)
      = ∑ q : Fin (N + 1) × Fin (N + 1), c q * diffMonomial f (q.1 : ℕ) (q.2 : ℕ) z₀ := rfl

/-! ### The dimension count -/

theorem card_jetValueSource (N : ℕ) :
    Fintype.card (Fin (N + 1) × Fin (N + 1)) = (N + 1) ^ (2 : ℕ) := by
  simp [Fintype.card_prod, sq]

theorem card_jetValueTarget (S : Finset ℂ) (d : ℕ) :
    Fintype.card ((↥S × Fin d) ⊕ Unit) = S.card * d + 1 := by
  simp [Fintype.card_sum, Fintype.card_prod]

/-- **The count.**  At degree `N = 2·A·m + 1` the monomials outnumber the principal-part
coefficients: quadratic growth beats linear growth. -/
theorem exists_degree_gt (A m : ℕ) :
    ∃ N : ℕ, 1 ≤ N ∧ A * (2 * m * N) + 1 < (N + 1) ^ (2 : ℕ) := by
  refine ⟨2 * A * m + 1, by omega, ?_⟩
  have hexp : A * (2 * m * (2 * A * m + 1)) = 2 * A * m * (2 * A * m + 1) := by ring
  rw [hexp]
  nlinarith [Nat.zero_le (A * m)]


/-- **A nonzero coefficient vector with vanishing data.**  At the degree supplied by
`exists_degree_gt` the coefficient space outgrows the data space, so some nonzero combination of the
monomials has all its principal-part coefficients and its value at `z₀` equal to zero. -/
theorem exists_ne_zero_jetValueMap_eq_zero (f : ℂ → ℂ) (S : Finset ℂ) (m : ℕ) (z₀ : ℂ) :
    ∃ (N : ℕ) (c : (Fin (N + 1) × Fin (N + 1)) → ℂ), 1 ≤ N ∧ c ≠ 0 ∧
      jetValueMap f S (2 * m * N) N z₀ c = 0 := by
  obtain ⟨N, hN1, hcount⟩ := exists_degree_gt S.card m
  have hlt : Fintype.card ((↥S × Fin (2 * m * N)) ⊕ Unit)
      < Fintype.card (Fin (N + 1) × Fin (N + 1)) := by
    rw [card_jetValueTarget, card_jetValueSource]
    exact hcount
  obtain ⟨c, hcne, hc0⟩ := exists_ne_zero_ker_of_card_lt (jetValueMap f S (2 * m * N) N z₀) hlt
  exact ⟨N, c, hN1, hcne, hc0⟩

end GaloisForLFunctions.HTGeometry
