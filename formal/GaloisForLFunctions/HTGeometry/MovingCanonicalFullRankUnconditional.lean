import GaloisForLFunctions.HTGeometry.ExponentSeparationCriterion

/-!
# An unconditional full-rank node packet for the moving canonical jets

Every hypothesis of the configuration theorem is discharged here: the shift is real and alone, so
there are no companions to bound, the sampled set is the zero sequence itself, the exponent box is
`{1, L^{(m)}}`, and the row family is the column family.

What remains to the left of the turnstile is data only — the sequence `θ`, the differentiation order
`m`, the degree budget `q` — so the statement carries no mathematical assumption.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- The two-term exponent box: the constant monomial and the jet itself. -/
noncomputable def singleJetBox : Fin 2 → (Fin 1 →₀ ℕ) := ![0, Finsupp.single 0 1]

/-- **Unconditional.**  For every parameter sequence, differentiation order and degree budget there
is a node packet in the open upper half-plane, with pairwise distinct nodes, on which the expanded
evaluation map of the moving canonical jet is injective. -/
theorem exists_row_packet_movingCanonicalSingleJet
    (θ : BoundedRealSequence) (m q : ℕ) :
    ∃ z : (Fin 2 × Fin (q + 1)) → ℂ, (∀ b, 0 < (z b).im) ∧ Function.Injective z ∧
      Function.Injective (expandedDifferentialEvaluationMatrix q 1 z singleJetBox
        (fun p => iteratedDeriv ((![m] : Fin 1 → ℕ) p.2) (movingCanonicalLogDerivative θ)
          (z p.1 + (![0] : Fin 1 → ℂ) p.2))).mulVec := by
  classical
  have hZinj : Function.Injective
      (fun p : ℕ => ((movingCanonicalZero θ p : ℂ) - (![0] : Fin 1 → ℂ) 0)) := by
    intro p₁ p₂ hp
    simp only [Matrix.cons_val_zero, sub_zero] at hp
    exact movingCanonicalZero_injective θ (Complex.ofReal_injective hp)
  refine exists_row_packet_upperHalfPlane_movingCanonicalJets
    (κ := Fin 2) (row := Fin 2 × Fin (q + 1)) (q := q)
    (Z := Set.range fun p : ℕ => ((movingCanonicalZero θ p : ℂ) - (![0] : Fin 1 → ℂ) 0))
    (exponent := singleJetBox)
    θ (![m]) (![0]) 0 (![0]) 1 ?_ ?_ (Set.infinite_range_of_injective hZinj) ?_ ?_ ?_ ?_ ?_ id
    Function.injective_id
  · intro k hk
    exact absurd (Subsingleton.elim k 0) hk
  · simp
  · rintro ζ ⟨p, rfl⟩
    exact ⟨p, rfl⟩
  · intro ζ _ k hk
    exact absurd (Subsingleton.elim k 0) hk
  · intro a k
    fin_cases a <;> fin_cases k <;> simp [singleJetBox]
  · have hempty : (Finset.univ : Finset (Fin 1)).erase 0 = ∅ := by
      ext k
      simp [Subsingleton.elim k 0]
    rw [hempty, Finset.sum_empty]
    simp
  · intro a b hab
    fin_cases a <;> fin_cases b <;>
      simp_all [singleJetBox]


/-! ## Two jets -/

/-- The two-jet exponent box: the shifted jet and the differentiated one. -/
noncomputable def twoJetBox : Fin 2 → (Fin 2 →₀ ℕ) :=
  ![Finsupp.single 1 1, Finsupp.single 0 1]

/-- **Unconditional, two jets.**  For every parameter sequence, differentiation order and degree
budget there is a node packet in the open upper half-plane, with pairwise distinct nodes, on which
the expanded evaluation map of the pair `(L^{(m)}, L(· + i))` is injective.

The companion's analytic order at every sampled point is zero, because the sampled points sit on the
line `Im = 1` where the log-derivative has strictly positive imaginary part and so cannot vanish. -/
theorem exists_row_packet_movingCanonicalTwoJets
    (θ : BoundedRealSequence) (m q : ℕ) :
    ∃ z : (Fin 2 × Fin (q + 1)) → ℂ, (∀ b, 0 < (z b).im) ∧ Function.Injective z ∧
      Function.Injective (expandedDifferentialEvaluationMatrix q 2 z twoJetBox
        (fun p => iteratedDeriv ((![m, 0] : Fin 2 → ℕ) p.2) (movingCanonicalLogDerivative θ)
          (z p.1 + (![0, Complex.I] : Fin 2 → ℂ) p.2))).mulVec := by
  classical
  have hZinj : Function.Injective
      (fun p : ℕ => ((movingCanonicalZero θ p : ℂ) - (![0, Complex.I] : Fin 2 → ℂ) 0)) := by
    intro p₁ p₂ hp
    simp only [Matrix.cons_val_zero, sub_zero] at hp
    exact movingCanonicalZero_injective θ (Complex.ofReal_injective hp)
  have hupper : ∀ ζ ∈ (Set.range fun p : ℕ =>
      ((movingCanonicalZero θ p : ℂ) - (![0, Complex.I] : Fin 2 → ℂ) 0)),
      0 < (ζ + (![0, Complex.I] : Fin 2 → ℂ) 1).im := by
    rintro ζ ⟨p, rfl⟩
    simp
  refine exists_row_packet_upperHalfPlane_movingCanonicalJets
    (κ := Fin 2) (row := Fin 2 × Fin (q + 1)) (q := q)
    (Z := Set.range fun p : ℕ => ((movingCanonicalZero θ p : ℂ) - (![0, Complex.I] : Fin 2 → ℂ) 0))
    (exponent := twoJetBox)
    θ (![m, 0]) (![0, Complex.I]) 0 (![0, 0]) 1 ?_ ?_
    (Set.infinite_range_of_injective hZinj) ?_ ?_ ?_ ?_ ?_ id Function.injective_id
  · intro k hk
    fin_cases k
    · exact absurd rfl hk
    · norm_num
  · norm_num
  · rintro ζ ⟨p, rfl⟩
    exact ⟨p, rfl⟩
  · intro ζ hζ k hk
    have hk1 : k = 1 := by
      fin_cases k
      · exact absurd rfl hk
      · rfl
    subst hk1
    have hpos := hupper ζ hζ
    have hana : AnalyticAt ℂ
        (fun w => iteratedDeriv ((![m, 0] : Fin 2 → ℕ) 1) (movingCanonicalLogDerivative θ)
          (w + (![0, Complex.I] : Fin 2 → ℂ) 1)) ζ :=
      analyticAt_translate_jet _ _ hpos
    have hV0 : (((![0, 0] : Fin 2 → ℕ) 1 : ℕ) : ℕ∞) = 0 := by norm_num
    rw [hV0, hana.analyticOrderAt_eq_zero]
    simp only [Matrix.cons_val_one]
    exact movingCanonicalLogDerivative_ne_zero_of_im_pos θ hpos
  · intro a k
    fin_cases a <;> fin_cases k <;> simp [twoJetBox]
  · have hone : (Finset.univ : Finset (Fin 2)).erase 0 = {1} := by decide
    rw [hone]
    simp
  · intro a b hab
    fin_cases a <;> fin_cases b <;>
      simp_all [twoJetBox]


/-! ## A box of arbitrary size -/

/-- The full binomial box in the two jets: `(L^{(m)})^a · L(· + i)^{N-a}`. -/
noncomputable def binomialJetBox (N : ℕ) : Fin (N + 1) → (Fin 2 →₀ ℕ) :=
  fun a => Finsupp.single 0 (a : ℕ) + Finsupp.single 1 (N - (a : ℕ))

theorem binomialJetBox_apply_zero (N : ℕ) (a : Fin (N + 1)) :
    binomialJetBox N a 0 = (a : ℕ) := by
  simp [binomialJetBox]

theorem binomialJetBox_apply_one (N : ℕ) (a : Fin (N + 1)) :
    binomialJetBox N a 1 = N - (a : ℕ) := by
  simp [binomialJetBox]

/-- **Unconditional, box of arbitrary size.**  For every parameter sequence, differentiation order,
degree budget and box size there is a node packet in the open upper half-plane, with pairwise
distinct nodes, on which the expanded evaluation map of the binomial box in the two jets
`(L^{(m)}, L(· + i))` is injective. -/
theorem exists_row_packet_movingCanonicalBinomialBox
    (θ : BoundedRealSequence) (m q N : ℕ) :
    ∃ z : (Fin (N + 1) × Fin (q + 1)) → ℂ, (∀ b, 0 < (z b).im) ∧ Function.Injective z ∧
      Function.Injective (expandedDifferentialEvaluationMatrix q 2 z (binomialJetBox N)
        (fun p => iteratedDeriv ((![m, 0] : Fin 2 → ℕ) p.2) (movingCanonicalLogDerivative θ)
          (z p.1 + (![0, Complex.I] : Fin 2 → ℂ) p.2))).mulVec := by
  classical
  have hZinj : Function.Injective
      (fun p : ℕ => ((movingCanonicalZero θ p : ℂ) - (![0, Complex.I] : Fin 2 → ℂ) 0)) := by
    intro p₁ p₂ hp
    simp only [Matrix.cons_val_zero, sub_zero] at hp
    exact movingCanonicalZero_injective θ (Complex.ofReal_injective hp)
  have hupper : ∀ ζ ∈ (Set.range fun p : ℕ =>
      ((movingCanonicalZero θ p : ℂ) - (![0, Complex.I] : Fin 2 → ℂ) 0)),
      0 < (ζ + (![0, Complex.I] : Fin 2 → ℂ) 1).im := by
    rintro ζ ⟨p, rfl⟩
    simp
  refine exists_row_packet_upperHalfPlane_movingCanonicalJets
    (κ := Fin (N + 1)) (row := Fin (N + 1) × Fin (q + 1)) (q := q)
    (Z := Set.range fun p : ℕ => ((movingCanonicalZero θ p : ℂ) - (![0, Complex.I] : Fin 2 → ℂ) 0))
    (exponent := binomialJetBox N)
    θ (![m, 0]) (![0, Complex.I]) 0 (![0, 0]) N ?_ ?_
    (Set.infinite_range_of_injective hZinj) ?_ ?_ ?_ ?_ ?_ id Function.injective_id
  · intro k hk
    fin_cases k
    · exact absurd rfl hk
    · norm_num
  · norm_num
  · rintro ζ ⟨p, rfl⟩
    exact ⟨p, rfl⟩
  · intro ζ hζ k hk
    have hk1 : k = 1 := by
      fin_cases k
      · exact absurd rfl hk
      · rfl
    subst hk1
    have hpos := hupper ζ hζ
    have hana : AnalyticAt ℂ
        (fun w => iteratedDeriv ((![m, 0] : Fin 2 → ℕ) 1) (movingCanonicalLogDerivative θ)
          (w + (![0, Complex.I] : Fin 2 → ℂ) 1)) ζ :=
      analyticAt_translate_jet _ _ hpos
    have hV0 : (((![0, 0] : Fin 2 → ℕ) 1 : ℕ) : ℕ∞) = 0 := by norm_num
    rw [hV0, hana.analyticOrderAt_eq_zero]
    simp only [Matrix.cons_val_one]
    exact movingCanonicalLogDerivative_ne_zero_of_im_pos θ hpos
  · intro a k
    fin_cases k
    · show binomialJetBox N a 0 ≤ N
      rw [binomialJetBox_apply_zero]
      exact Nat.lt_succ_iff.mp a.isLt
    · show binomialJetBox N a 1 ≤ N
      rw [binomialJetBox_apply_one]
      exact Nat.sub_le _ _
  · have hone : (Finset.univ : Finset (Fin 2)).erase 0 = {1} := by decide
    rw [hone]
    simp
  · intro a b hab
    simp only [binomialJetBox_apply_zero] at hab
    exact Fin.val_injective hab

end GaloisForLFunctions.HTGeometry
