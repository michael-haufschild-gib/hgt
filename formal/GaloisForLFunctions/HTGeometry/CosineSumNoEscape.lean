import GaloisForLFunctions.HTGeometry.ConicLaurentNoEscape
import GaloisForLFunctions.HTGeometry.LabeledCosineDescent
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Analysis.Convex.Contractible

/-!
# No finite asymptotic value for the reflected cosine source

An escaping path eventually avoids the two square-root branch points. Lift that
tail continuously to the conic and apply its compactification obstruction.
-/

namespace GaloisForLFunctions.HTGeometry.CosineSumNoEscape

open Filter Topology Set Complex LabeledCosineDescent

theorem continuous_square_lift {f : ℝ → ℂ} (hf : Continuous f) (hne : ∀ t, f t ≠ 0) :
    ∃ u : ℝ → ℂ, Continuous u ∧ ∀ t, u t ^ 2 = f t := by
  have cov := isCoveringMapOn_npow 2 (by norm_num : (2 : ℂ) ≠ 0)
  obtain ⟨u, ⟨_, hu⟩, _⟩ := cov.existsUnique_continuousMap_lifts (⟨f, hf⟩ : C(ℝ, ℂ)) (a₀ := 0)
      (sqrt_square (f 0)) hne
  exact ⟨u, u.continuous, fun t ↦ congrFun hu t⟩

theorem descended_sum_no_escape {f : ℝ → ℂ} (hf : Continuous f) {c d : ℂ}
    (he : Tendsto f atTop (cocompact ℂ))
    (hd : Tendsto (fun t ↦ descendedCos (f t) + descendedCos (c - f t)) atTop (𝓝 d)) :
    False := by
  have hn₀ : ∀ᶠ t in atTop, f t ≠ 0 := he isCompact_singleton.compl_mem_cocompact
  have hnc : ∀ᶠ t in atTop, f t ≠ c := he isCompact_singleton.compl_mem_cocompact
  obtain ⟨T, hT⟩ := eventually_atTop.mp (hn₀.and hnc)
  let g : ℝ → ℂ := fun t ↦ f (max T t)
  have hg : Continuous g := hf.comp (continuous_const.max continuous_id)
  have hgf : g =ᶠ[atTop] f := by
    filter_upwards [eventually_ge_atTop T] with t ht
    simp [g, max_eq_right ht]
  have hg₀ (t) : g t ≠ 0 := (hT (max T t) (le_max_left _ _)).1
  have hgc (t) : c - g t ≠ 0 :=
    sub_ne_zero.mpr ((hT (max T t) (le_max_left _ _)).2.symm)
  obtain ⟨u, hu, hu₂⟩ := continuous_square_lift hg hg₀
  obtain ⟨v, hv, hv₂⟩ := continuous_square_lift (f := fun t ↦ c - g t) (continuous_const.sub hg) hgc
  have hconic (t) : (I * u t) ^ 2 + (I * v t) ^ 2 = -c := by
    simp only [mul_pow, I_sq, hu₂, hv₂]
    ring
  have hge : Tendsto g atTop (cocompact ℂ) := he.congr' hgf.symm
  have hp : Tendsto (fun t ↦ (I * u t, I * v t)) atTop (cocompact (ℂ × ℂ)) := by
    have hproject : Tendsto ((fun p : ℂ × ℂ ↦ -p.1 ^ 2) ∘ fun t ↦ (I * u t, I * v t))
        atTop (cocompact ℂ) := by
      simpa only [Function.comp_def, mul_pow, I_sq, hu₂, neg_mul, one_mul, neg_neg] using hge
    exact (tendsto_comap_iff.mpr hproject).mono_right
      (comap_cocompact_le (show Continuous (fun p : ℂ × ℂ ↦ -p.1 ^ 2) by fun_prop))
  have hdg : Tendsto (fun t ↦ descendedCos (g t) + descendedCos (c - g t)) atTop (𝓝 d) := by
    apply hd.congr'
    filter_upwards [hgf] with t ht
    rw [ht]
  have hsum : Tendsto (fun t ↦ cos (u t) + cos (v t)) atTop (𝓝 d) := by
    apply hdg.congr'
    exact Eventually.of_forall fun t ↦ by
      change descendedCos (g t) + descendedCos (c - g t) = cos (u t) + cos (v t)
      rw [descendedCos_of_square (hu₂ t), descendedCos_of_square (hv₂ t)]
  have hLaurent : Tendsto (fun t ↦ ToricConicCorner.laurent (exp (I * u t)) (exp (I * v t)))
      atTop (𝓝 (2 * d)) := by
    apply (hsum.const_mul 2).congr'
    exact Eventually.of_forall fun t ↦ by
      simp only [ToricConicCorner.laurent, cos, neg_mul, exp_neg, mul_comm (u t) I,
        mul_comm (v t) I]
      ring
  exact ConicLaurentNoEscape.no_finite_asymptotic_value
    (hu.const_mul I) (hv.const_mul I) hconic hp hLaurent

theorem source_sum_no_finite_asymptotic_value {f : ℝ → ℂ} (hf : Continuous f) {d : ℂ}
    (he : Tendsto f atTop (cocompact ℂ))
    (hd : Tendsto (fun t ↦ source (f t) + source (-f t)) atTop (𝓝 d)) : False := by
  let α : ℂ := (2 * (Real.pi : ℂ)) ^ 2 / 27
  have hα : α ≠ 0 := by
    dsimp [α]
    exact div_ne_zero (pow_ne_zero _ (mul_ne_zero (by norm_num)
      (by exact_mod_cast Real.pi_ne_zero))) (by norm_num)
  let e : ℂ ≃ₜ ℂ :=
    { toFun := fun w ↦ α * (w + 1 / 12)
      invFun := fun z ↦ z / α - 1 / 12
      left_inv := fun z ↦ by field_simp; ring
      right_inv := fun z ↦ by field_simp; ring
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  have hge : Tendsto (fun t ↦ e (f t)) atTop (cocompact ℂ) :=
    e.isClosedEmbedding.tendsto_cocompact.comp he
  have hgd : Tendsto (fun t ↦ descendedCos (e (f t)) + descendedCos (α / 6 - e (f t)))
      atTop (𝓝 d) := by
    apply hd.congr'
    exact Eventually.of_forall fun t ↦ by
      dsimp [source, e, α]
      congr 2 <;> ring
  exact descended_sum_no_escape (e.continuous.comp hf) hge hgd

end GaloisForLFunctions.HTGeometry.CosineSumNoEscape
