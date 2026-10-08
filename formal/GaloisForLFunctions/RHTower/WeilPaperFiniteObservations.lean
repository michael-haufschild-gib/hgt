import GaloisForLFunctions.RHTower.WeilPaperNullPositiveParts

/-!
# Rational information invisible to finitely many Weil observations

The prime-mask sampling sections leave a nonzero sampled direction in the
kernel of every finite family of real linear observations. Positive repair
realizes this direction as a pair of nonnegative integer-null mixtures with
equal mass. In particular, their full energies can agree while a primitive
rational correlation differs.
-/

noncomputable section
namespace RHTower.WeilWorkPBAP

open WeilOneSided

/-- Any `k` real linear observations miss a direction detected by `k+1` consecutive ratios. -/
theorem exists_paperNullMassSpace_finite_observation_kernel (k : ℕ)
    (T : (WeilTestFn →₀ ℝ) →ₗ[ℝ] (Fin k → ℝ)) :
    ∃ d : paperNullMassSpace, T d.1 = 0 ∧ paperConsecutiveSampler (k + 1) d ≠ 0 := by
  obtain ⟨S, hS⟩ := exists_paperConsecutiveSampler_rightInverse (k + 1)
  let U := T.comp (paperNullMassSpace.subtype.comp S)
  have hni : ¬ Function.Injective U := by
    intro hinj
    have h := LinearMap.finrank_le_finrank_of_injective hinj
    simp only [Module.finrank_fin_fun] at h
    omega
  obtain ⟨v, hv, hv0⟩ : ∃ v, U v = 0 ∧ v ≠ 0 := by
    by_contra! h
    exact hni (LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr h))
  refine ⟨S v, hv, ?_⟩
  have hs : paperConsecutiveSampler (k + 1) (S v) = v :=
    congrArg (fun A : (Fin (k + 1) → ℝ) →ₗ[ℝ] (Fin (k + 1) → ℝ) => A v) hS
  simpa only [hs] using hv0

/-- Finite observation equality is realized by actual nonnegative mixtures, while a reduced
ratio with labels at most `k+3` still separates them. -/
theorem exists_positive_null_pair_same_finite_observations (k : ℕ)
    (T : (WeilTestFn →₀ ℝ) →ₗ[ℝ] (Fin k → ℝ)) :
    ∃ a b : WeilTestFn →₀ ℝ,
      (∀ f, 0 ≤ a f) ∧ (∀ f, 0 ≤ b f) ∧ defect a = 0 ∧ defect b = 0 ∧
      mixtureSample a 0 = mixtureSample b 0 ∧ T a = T b ∧
      ∃ r : PaperPacketPrimitiveEdge (k + 3),
        mixtureSample a (Real.log (r.1.1 : ℕ) - Real.log (r.1.2 : ℕ)) ≠
          mixtureSample b (Real.log (r.1.1 : ℕ) - Real.log (r.1.2 : ℕ)) := by
  obtain ⟨d, hd, hs⟩ := exists_paperNullMassSpace_finite_observation_kernel k T
  obtain ⟨i, hi⟩ : ∃ i, paperConsecutiveSampler (k + 1) d i ≠ 0 := by
    by_contra! h
    exact hs (funext h)
  refine ⟨paperNullPositivePart d, paperNullNegativePart d,
    paperNullPositivePart_nonneg d, paperNullNegativePart_nonneg d,
    defect_paperNullPositivePart d, defect_paperNullNegativePart d,
    paperNullPositivePart_mass_eq d, ?_, paperConsecutiveEdge (k + 1) i, ?_⟩
  · apply sub_eq_zero.mp
    rw [← map_sub, paperNullPositivePart_sub_negativePart]
    exact hd
  · intro heq
    apply hi
    rw [paperConsecutiveSampler_apply, ← mixtureSample_paperNullParts_sub, heq,
      sub_self, Complex.zero_re]

/-- Integer defects, mass and any finite linear observation vector cannot determine all
primitive rational correlations, even on the nonnegative cone. -/
theorem no_primitive_samples_factor_through_finite_observations (k : ℕ)
    (T : (WeilTestFn →₀ ℝ) →ₗ[ℝ] (Fin k → ℝ)) :
    ¬ ∃ F : (LogIndex →₀ ℝ) → ℂ → (Fin k → ℝ) → (PaperPacketPrimitiveEdge (k + 3) → ℂ),
      ∀ c : WeilTestFn →₀ ℝ, (∀ f, 0 ≤ c f) → ∀ r : PaperPacketPrimitiveEdge (k + 3),
        mixtureSample c (Real.log (r.1.1 : ℕ) - Real.log (r.1.2 : ℕ)) =
          F (defect c) (mixtureSample c 0) (T c) r := by
  rintro ⟨F, hF⟩
  obtain ⟨a, b, ha, hb, ha0, hb0, hm, hT, r, hr⟩ :=
    exists_positive_null_pair_same_finite_observations k T
  apply hr
  rw [hF a ha r, hF b hb r, ha0, hb0, hm, hT]

/-- Equal full energy and every integer constraint still leave rational correlation freedom. -/
theorem exists_positive_null_equal_mass_energy_pair_distinct_sample :
    ∃ a b : WeilTestFn →₀ ℝ,
      (∀ f, 0 ≤ a f) ∧ (∀ f, 0 ≤ b f) ∧ defect a = 0 ∧ defect b = 0 ∧
      mixtureSample a 0 = mixtureSample b 0 ∧ energy a = energy b ∧
      ∃ r : PaperPacketPrimitiveEdge 4,
        mixtureSample a (Real.log (r.1.1 : ℕ) - Real.log (r.1.2 : ℕ)) ≠
          mixtureSample b (Real.log (r.1.1 : ℕ) - Real.log (r.1.2 : ℕ)) := by
  obtain ⟨a, b, ha, hb, ha0, hb0, hm, hT, hr⟩ :=
    exists_positive_null_pair_same_finite_observations 1 (LinearMap.pi fun _ : Fin 1 => energy)
  exact ⟨a, b, ha, hb, ha0, hb0, hm, congrFun hT 0, hr⟩

end RHTower.WeilWorkPBAP
