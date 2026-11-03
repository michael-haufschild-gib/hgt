import GaloisForLFunctions.SquareRootThreshold.ClusterDistanceProducts
import GaloisForLFunctions.RHTower.ClusterRobustHodgeExclusion

/-!
# Reflected cluster products

An empty-annulus selection controls both reflected products of killing distances,
while keeping the centre near the original zero and preserving its depth.
-/

open Complex MeasureTheory Real Set Filter Topology
open scoped ComplexConjugate BigOperators
noncomputable section
namespace SquareRootThreshold
open RHTower Zeta23

/-- Omitting clipped factors can only increase the product. -/
theorem cluster_product_le_mapped (P K : Finset ℂ) (f : ℂ → ℂ)
    (hf : Function.Injective f) (c : ℂ) (t : ℝ)
    (hmem : ∀ ρ ∈ K, f ρ ∈ P) (hfar : ∀ ρ ∈ K, t / 2 ≤ ‖f ρ - c‖) :
    (∏ q ∈ P, clusterDistanceFactor c t q) ≤ ∏ ρ ∈ K, ‖f ρ - c‖ := by
  classical
  have hsub : K.image f ⊆ P := by
    intro q hq
    obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp hq
    exact hmem ρ hρ
  calc (∏ q ∈ P, clusterDistanceFactor c t q)
      ≤ ∏ q ∈ K.image f, clusterDistanceFactor c t q :=
        Finset.prod_le_prod_of_subset_of_le_one hsub
          (fun q _ => clusterDistanceFactor_nonneg c q t)
          (fun q _ _ => clusterDistanceFactor_le_one c q t)
    _ = ∏ ρ ∈ K, clusterDistanceFactor c t (f ρ) :=
      Finset.prod_image (fun _ _ _ _ he => hf he)
    _ ≤ ∏ ρ ∈ K, ‖f ρ - c‖ := by
      apply Finset.prod_le_prod (fun ρ _ => clusterDistanceFactor_nonneg c (f ρ) t)
      intro ρ hρ
      rw [clusterDistanceFactor, if_pos (hfar ρ hρ)]
      exact min_le_right _ _

/-- Recentring preserves depth and controls the two reflected root products separately. -/
theorem cluster_selection_with_products (Z : ZeroConfig) {ρ₀ : ℂ} (hρ₀ : ρ₀ ∈ Z.carrier) {δ : ℝ}
    (hδ : 0 < δ) (hre : ρ₀.re = 1 / 2 + δ) {H : ℝ} (hH : 0 ≤ H) {N₀ n : ℕ}
    (hn : (Z.finite_window (ρ₀.im - (H + 1)) (ρ₀.im + (H + 1))).toFinset.card ≤ n) {r₀ : ℝ}
    (hr₀ : 0 < r₀) (hr₀s : r₀ ≤ lowHeightEps0 δ N₀) :
    ∃ ρ₁ ∈ Z.carrier, ∃ δ₁ : ℝ, ρ₁.re = 1 / 2 + δ₁ ∧ δ / 2 ≤ δ₁ ∧ |δ - δ₁| < r₀ ∧
      |ρ₁.im - ρ₀.im| ≤ r₀ ∧
      ∃ Kset ⊆ (Z.finite_window (ρ₁.im - H) (ρ₁.im + H)).toFinset, Kset.card ≤ n ∧
        ∃ ε η : ℝ, 0 < ε ∧ ε ≤ lowHeightEps0 δ₁ N₀ ∧ ε ≤ r₀ ∧ η ≤ 1 ∧
          0 < η ∧
          ε / η = 1 / lowHeightScale n ∧
          (∀ ρ ∈ (Z.finite_window (ρ₁.im - H) (ρ₁.im + H)).toFinset, ρ ∉ Kset →
            ‖(gammaOf ρ - ρ₁.im) - -(I * δ₁)‖ < ε ∨ ‖(gammaOf ρ - ρ₁.im) - I * δ₁‖ < ε) ∧
          (∀ ρ ∈ Kset,
            η ≤ ‖(gammaOf ρ - ρ₁.im) - -(I * δ₁)‖ ∧ η ≤ ‖(gammaOf ρ - ρ₁.im) - I * δ₁‖) ∧
          (r₀ * (1 / (16 * lowHeightScale n)) ^ 2) ^ (2 * n) ≤
            ∏ ρ ∈ Kset, ‖(gammaOf ρ - ρ₁.im) - -(I * δ₁)‖ ∧
          (r₀ * (1 / (16 * lowHeightScale n)) ^ 2) ^ (2 * n) ≤
            ∏ ρ ∈ Kset, ‖(gammaOf ρ - ρ₁.im) - I * δ₁‖ := by
  classical
  set γ₀ := ρ₀.im with hγ₀
  set W₁ := (Z.finite_window (γ₀ - (H + 1)) (γ₀ + (H + 1))).toFinset with hW₁def
  have hW₁ : ∀ ρ, ρ ∈ W₁ ↔ ρ ∈ Z.carrier ∧ γ₀ - (H + 1) < ρ.im ∧ ρ.im ≤ γ₀ + (H + 1) := by
    intro ρ; rw [hW₁def, Set.Finite.mem_toFinset]; rfl
  set xf : ℂ → ℂ := fun ρ => gammaOf ρ - γ₀ with hxf
  set P := W₁.image xf with hP
  have hPcard : P.card ≤ n := Finset.card_image_le.trans hn
  set s := r₀ with hs
  have hs0 : 0 < s := hr₀
  have hsδ : s ≤ δ / 300 := hr₀s.trans (lowHeightEps0_le hδ N₀).1
  have hs1 : s ≤ 1 / 300 := hr₀s.trans (lowHeightEps0_le hδ N₀).2
  set lam := lowHeightScale n with hlamdef
  have hlam : 1 ≤ lam := by
    rw [hlamdef]; unfold lowHeightScale; nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hx₀ : xf ρ₀ = -(I * δ) := (gammaOf_sub_of_re_im (γ₀ := γ₀) rfl hre).1
  have hx₀P : -(I * (δ : ℂ)) ∈ P := by
    rw [← hx₀]
    exact Finset.mem_image_of_mem xf ((hW₁ ρ₀).mpr ⟨hρ₀, by linarith, by linarith⟩)
  obtain ⟨c, hcP, t, ht0, ht2, ht3, ht4, htprod⟩ :=
    exists_empty_annulus_with_product hlam n P (-(I * δ)) s hPcard hx₀P hs0 (by linarith)
  obtain ⟨ρ₁, hρ₁W, hρ₁c⟩ := Finset.mem_image.mp hcP
  have hρ₁Z := ((hW₁ ρ₁).mp hρ₁W).1
  set δ₁ := ρ₁.re - 1 / 2 with hδ₁def
  have hcre : c.re = ρ₁.im - γ₀ := by rw [← hρ₁c]; simp [hxf, WeilEF.gammaOf_re]
  have hcim : c.im = -δ₁ := by rw [← hρ₁c]; simp [hxf, WeilEF.gammaOf_im, hδ₁def]
  have hcnear : ‖c - -(I * (δ : ℂ))‖ < s := by linarith
  have hre_near : |ρ₁.im - γ₀| < s := by
    have := Complex.abs_re_le_norm (c - -(I * (δ : ℂ)))
    rw [Complex.sub_re, Complex.neg_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, hcre] at this
    simp only [zero_mul, mul_zero, sub_zero, neg_zero] at this
    linarith
  have him_near : |δ - δ₁| < s := by
    have := Complex.abs_im_le_norm (c - -(I * (δ : ℂ)))
    rw [Complex.sub_im, Complex.neg_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, hcim] at this
    simp only [zero_mul, one_mul, zero_add] at this
    rw [abs_sub_comm]
    have e : -δ₁ - -δ = δ - δ₁ := by ring
    rw [e] at this
    rw [abs_sub_comm]; linarith
  have hδ₁ : δ / 2 ≤ δ₁ := by
    have := (abs_lt.mp him_near).2
    linarith
  -- the new window
  set W := (Z.finite_window (ρ₁.im - H) (ρ₁.im + H)).toFinset with hWdef
  have hW : ∀ ρ, ρ ∈ W ↔ ρ ∈ Z.carrier ∧ ρ₁.im - H < ρ.im ∧ ρ.im ≤ ρ₁.im + H := by
    intro ρ; rw [hWdef, Set.Finite.mem_toFinset]; rfl
  have hWW₁ : W ⊆ W₁ := by
    intro ρ hρ
    obtain ⟨hρZ, h1, h2⟩ := (hW ρ).mp hρ
    have := abs_lt.mp hre_near
    exact (hW₁ ρ).mpr ⟨hρZ, by linarith, by linarith⟩
  have hrefl : ∀ ρ ∈ W₁, reflect ρ ∈ W₁ := by
    intro ρ hρ
    obtain ⟨hρZ, h1, h2⟩ := (hW₁ ρ).mp hρ
    exact (hW₁ _).mpr ⟨Z.reflect_mem ρ hρZ, by rw [Tail.reflect_im]; exact h1,
      by rw [Tail.reflect_im]; exact h2⟩
  -- coordinates centred at `γ₁`
  have hid1 : ∀ ρ : ℂ, (gammaOf ρ - ρ₁.im) - -(I * δ₁) = xf ρ - c := by
    intro ρ
    apply Complex.ext
    · simp [hxf, hcre]
    · simp [hxf, hcim]
  have hid2 : ∀ ρ : ℂ, ‖(gammaOf ρ - ρ₁.im) - I * δ₁‖ = ‖xf (reflect ρ) - c‖ := by
    intro ρ
    have : (gammaOf ρ - ρ₁.im) - I * δ₁ = conj (xf (reflect ρ) - c) := by
      rw [hxf]
      simp only [Tail.gammaOf_reflect, map_sub, Complex.conj_conj, Complex.conj_ofReal]
      apply Complex.ext
      · simp [hcre]
      · simp [hcim]
    rw [this, Complex.norm_conj]
  set ε := t / (2 * lam) with hεdef
  set η := t / 2 with hηdef
  set Kset := W.filter (fun ρ => η ≤ ‖(gammaOf ρ - ρ₁.im) - -(I * δ₁)‖ ∧
    η ≤ ‖(gammaOf ρ - ρ₁.im) - I * δ₁‖) with hKdef
  have hlam0 : 0 < lam := by linarith
  have hεs : ε ≤ s / 2 := by
    rw [hεdef, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  refine ⟨ρ₁, hρ₁Z, δ₁, by rw [hδ₁def]; ring, hδ₁, him_near, hre_near.le, Kset,
    Finset.filter_subset _ _,
    ((Finset.card_filter_le _ _).trans (Finset.card_le_card hWW₁)).trans hn, ε, η,
    by positivity, ?_, by linarith, ?_, by positivity, ?_, ?_, ?_, ?_, ?_⟩
  · have : s / 2 ≤ lowHeightEps0 δ N₀ / 2 := by linarith
    exact hεs.trans (this.trans (lowHeightEps0_half_le hδ₁ N₀))
  · rw [hηdef]; linarith
  · rw [hεdef, hηdef]; field_simp
  · intro ρ hρ hK
    have hnot : ¬ (η ≤ ‖(gammaOf ρ - ρ₁.im) - -(I * δ₁)‖ ∧
        η ≤ ‖(gammaOf ρ - ρ₁.im) - I * δ₁‖) := fun h => hK (Finset.mem_filter.mpr ⟨hρ, h⟩)
    rw [not_and_or, not_le, not_le] at hnot
    rcases hnot with h | h
    · left
      rw [hid1] at h ⊢
      exact ht4 _ (Finset.mem_image_of_mem xf (hWW₁ hρ)) h
    · right
      rw [hid2] at h ⊢
      exact ht4 _ (Finset.mem_image_of_mem xf (hrefl _ (hWW₁ hρ))) h
  · intro ρ hρ
    exact (Finset.mem_filter.mp hρ).2

  · refine htprod.trans ?_
    have hxf_inj : Function.Injective xf := by
      intro ρ σ he
      have hre := congrArg Complex.re he
      have him := congrArg Complex.im he
      simp only [hxf, Complex.sub_re, WeilEF.gammaOf_re, Complex.ofReal_re] at hre
      simp only [hxf, Complex.sub_im, WeilEF.gammaOf_im, Complex.ofReal_im] at him
      apply Complex.ext <;> linarith
    have hh := cluster_product_le_mapped P Kset xf hxf_inj c t
      (fun ρ hρ => Finset.mem_image_of_mem xf (hWW₁ (Finset.mem_filter.mp hρ).1))
      (fun ρ hρ => by rw [← hid1]; exact (Finset.mem_filter.mp hρ).2.1)
    simpa only [hid1] using hh
  · refine htprod.trans ?_
    have hxf_inj : Function.Injective (fun ρ => xf (reflect ρ)) := by
      intro ρ σ he
      have hre := congrArg Complex.re he
      have him := congrArg Complex.im he
      simp only [hxf, Complex.sub_re, WeilEF.gammaOf_re, Complex.ofReal_re,
        Tail.reflect_im] at hre
      simp only [hxf, Complex.sub_im, WeilEF.gammaOf_im, Complex.ofReal_im,
        reflect, Complex.sub_re, Complex.one_re, Complex.conj_re] at him
      apply Complex.ext <;> linarith
    have hh := cluster_product_le_mapped P Kset (fun ρ => xf (reflect ρ)) hxf_inj c t
      (fun ρ hρ => Finset.mem_image_of_mem xf (hrefl _ (hWW₁ (Finset.mem_filter.mp hρ).1)))
      (fun ρ hρ => by rw [← hid2]; exact (Finset.mem_filter.mp hρ).2.2)
    simpa only [hid2] using hh

end SquareRootThreshold
