import GaloisForLFunctions.HTGeometry.DifferentialSeparantIterate

/-!
# Pseudo-division against a polynomial linear in the top jet

A proper derivative of a differential polynomial is linear in its top jet: `D = S·y_m + B` with `S`
and `B` of order below `m`.  Pseudo-dividing an arbitrary polynomial of order at most `m` by such a
`D` costs only powers of `S`, and the remainder has order strictly below `m`.  This is the
order-lowering half of Ritt's reduction.

The induction runs over the jets of order at most `m`, where the only variable that has to be
eliminated is `y_m` itself.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial GaloisForLFunctions

noncomputable section

variable {K : Type*} [CommRing K]

/-- Pseudo-division by a polynomial linear in the top jet, on polynomials presented through the
jets of order at most `m`. -/
theorem exists_pseudo_division_aux (m : ℕ) {S B : DifferentialPolynomial Unit K}
    (hS : ∀ p ∈ S.vars, p.2 < m) (hB : ∀ p ∈ B.vars, p.2 < m)
    (F' : MvPolynomial {q : Unit × ℕ // q.2 ≤ m} K) :
    ∃ (e : ℕ) (G Rem : DifferentialPolynomial Unit K),
      (∀ p ∈ Rem.vars, p.2 < m) ∧
      S ^ e * (MvPolynomial.rename Subtype.val F')
        = G * (S * MvPolynomial.X ((), m) + B) + Rem := by
  classical
  induction F' using MvPolynomial.induction_on with
  | C a =>
      refine ⟨0, 0, MvPolynomial.C a, ?_, ?_⟩
      · intro p hp
        rw [MvPolynomial.vars_C] at hp
        exact absurd hp (Finset.notMem_empty p)
      · rw [MvPolynomial.rename_C]
        ring
  | add p q hp hq =>
      obtain ⟨e₁, G₁, R₁, hR₁, hE₁⟩ := hp
      obtain ⟨e₂, G₂, R₂, hR₂, hE₂⟩ := hq
      refine ⟨max e₁ e₂,
        S ^ (max e₁ e₂ - e₁) * G₁ + S ^ (max e₁ e₂ - e₂) * G₂,
        S ^ (max e₁ e₂ - e₁) * R₁ + S ^ (max e₁ e₂ - e₂) * R₂, ?_, ?_⟩
      · intro x hx
        rcases Finset.mem_union.mp (MvPolynomial.vars_add_subset _ _ hx) with h | h
        · rcases Finset.mem_union.mp (MvPolynomial.vars_mul _ _ h) with h' | h'
          · exact hS x (MvPolynomial.vars_pow _ _ h')
          · exact hR₁ x h'
        · rcases Finset.mem_union.mp (MvPolynomial.vars_mul _ _ h) with h' | h'
          · exact hS x (MvPolynomial.vars_pow _ _ h')
          · exact hR₂ x h'
      · have ha : max e₁ e₂ - e₁ + e₁ = max e₁ e₂ := by omega
        have hb : max e₁ e₂ - e₂ + e₂ = max e₁ e₂ := by omega
        rw [map_add]
        calc S ^ max e₁ e₂ * (MvPolynomial.rename Subtype.val p
              + MvPolynomial.rename Subtype.val q)
            = S ^ (max e₁ e₂ - e₁) * (S ^ e₁ * MvPolynomial.rename Subtype.val p)
              + S ^ (max e₁ e₂ - e₂) * (S ^ e₂ * MvPolynomial.rename Subtype.val q) := by
              rw [← mul_assoc, ← mul_assoc, ← pow_add, ← pow_add, ha, hb]
              ring
          _ = _ := by rw [hE₁, hE₂]; ring
  | mul_X q i hq =>
      obtain ⟨e, G, R, hR, hE⟩ := hq
      obtain ⟨⟨u, j⟩, hj⟩ := i
      have hu : u = () := Subsingleton.elim u ()
      subst hu
      have hren : MvPolynomial.rename Subtype.val (q * MvPolynomial.X ⟨((), j), hj⟩)
          = MvPolynomial.rename Subtype.val q * MvPolynomial.X ((), j) := by
        rw [map_mul, MvPolynomial.rename_X]
      by_cases hjm : j = m
      · subst hjm
        refine ⟨e + 1, S * G * MvPolynomial.X ((), j) + R, -(R * B), ?_, ?_⟩
        · intro x hx
          rw [MvPolynomial.vars_neg] at hx
          rcases Finset.mem_union.mp (MvPolynomial.vars_mul _ _ hx) with h | h
          · exact hR x h
          · exact hB x h
        · rw [hren]
          calc S ^ (e + 1) * (MvPolynomial.rename Subtype.val q * MvPolynomial.X ((), j))
              = (S ^ e * MvPolynomial.rename Subtype.val q)
                * (S * MvPolynomial.X ((), j)) := by ring
            _ = (G * (S * MvPolynomial.X ((), j) + B) + R)
                * (S * MvPolynomial.X ((), j)) := by rw [hE]
            _ = _ := by ring
      · have hjlt : j < m := by omega
        refine ⟨e, G * MvPolynomial.X ((), j), R * MvPolynomial.X ((), j), ?_, ?_⟩
        · intro x hx
          rcases Finset.mem_union.mp (MvPolynomial.vars_mul _ _ hx) with h | h
          · exact hR x h
          · have hx' := mvPolynomial_vars_X_subset (R := K) ((), j) h
            simp only [Finset.mem_singleton] at hx'
            subst hx'
            exact hjlt
        · rw [hren]
          calc S ^ e * (MvPolynomial.rename Subtype.val q * MvPolynomial.X ((), j))
              = (S ^ e * MvPolynomial.rename Subtype.val q) * MvPolynomial.X ((), j) := by ring
            _ = (G * (S * MvPolynomial.X ((), m) + B) + R) * MvPolynomial.X ((), j) := by rw [hE]
            _ = _ := by ring

/-- **Pseudo-division against a polynomial linear in the top jet.** -/
theorem exists_pseudo_division (m : ℕ) {S B F : DifferentialPolynomial Unit K}
    (hS : ∀ p ∈ S.vars, p.2 < m) (hB : ∀ p ∈ B.vars, p.2 < m)
    (hF : ∀ p ∈ F.vars, p.2 ≤ m) :
    ∃ (e : ℕ) (G Rem : DifferentialPolynomial Unit K),
      (∀ p ∈ Rem.vars, p.2 < m) ∧
      S ^ e * F = G * (S * MvPolynomial.X ((), m) + B) + Rem := by
  have hsub : ↑F.vars ⊆ {p : Unit × ℕ | p.2 ≤ m} := fun p hp => hF p hp
  have hmem : F ∈ MvPolynomial.supported K {p : Unit × ℕ | p.2 ≤ m} :=
    MvPolynomial.mem_supported.mpr hsub
  rw [MvPolynomial.supported_eq_range_rename] at hmem
  obtain ⟨F', hF'⟩ := hmem
  have hF'' : MvPolynomial.rename (Subtype.val) F' = F := hF'
  obtain ⟨e, G, Rem, hRem, hEq⟩ := exists_pseudo_division_aux m hS hB F'
  refine ⟨e, G, Rem, hRem, ?_⟩
  rw [← hF'']
  exact hEq

section Reduction

variable [Differential K]

/-- **The order-lowering reduction step of Ritt's algorithm.**  Against a fixed `A` of order `n`,
any polynomial of order at most `m > n` reduces, at the cost of a power of the separant, to one of
order strictly below `m`. -/
theorem exists_order_reduction {A F : DifferentialPolynomial Unit K} {m : ℕ}
    (hm : scalarDifferentialPolynomialOrder A < m)
    (hF : ∀ p ∈ F.vars, p.2 ≤ m) :
    ∃ (e : ℕ) (G Rem : DifferentialPolynomial Unit K),
      (∀ p ∈ Rem.vars, p.2 < m) ∧
      scalarSeparant A ^ e * F
        = G * ((⇑(differentialPolynomialOverDerivation Unit K))^[m -
            scalarDifferentialPolynomialOrder A] A) + Rem := by
  obtain ⟨k, hk⟩ : ∃ k, m = scalarDifferentialPolynomialOrder A + k + 1 :=
    ⟨m - scalarDifferentialPolynomialOrder A - 1, by omega⟩
  subst hk
  obtain ⟨B, hB, hEq⟩ := exists_iterated_separant_decomposition A k
  have hiter : scalarDifferentialPolynomialOrder A + k + 1
      - scalarDifferentialPolynomialOrder A = k + 1 := by omega
  rw [hiter]
  have hSv : ∀ p ∈ (scalarSeparant A).vars,
      p.2 < scalarDifferentialPolynomialOrder A + k + 1 := by
    intro p hp
    have h1 := vars_le_scalarOrder _ p hp
    have h2 := scalarOrder_separant_le A
    omega
  have hBv : ∀ p ∈ B.vars, p.2 < scalarDifferentialPolynomialOrder A + k + 1 := by
    intro p hp
    have := hB p hp
    omega
  obtain ⟨e, G, Rem, hRem, hPD⟩ :=
    exists_pseudo_division (scalarDifferentialPolynomialOrder A + k + 1) hSv hBv hF
  exact ⟨e, G, Rem, hRem, by rw [hEq]; exact hPD⟩

end Reduction

end

end GaloisForLFunctions.HTGeometry
