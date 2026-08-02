import GaloisForLFunctions.HTGeometry.BoxDimension

/-!
# Box dimension is a bi-Lipschitz invariant

A Lipschitz map cannot increase covering numbers beyond the rescaling of the resolution, and an
antilipschitz map cannot decrease them: a cover of the image pulls back to a cover of the source at
the inversely rescaled resolution.  Consequently a bi-Lipschitz image of a set with two-sided
covering bounds has the same box dimension.
-/

open Filter MeasureTheory Metric Set Topology
open scoped ENNReal NNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]

/-- **Covers pull back along an antilipschitz map.** -/
theorem externalCoveringNumber_le_of_antilipschitz {f : X → Y} {K : ℝ≥0}
    (hf : AntilipschitzWith K f) (A : Set X) (ε : ℝ≥0) :
    Metric.externalCoveringNumber (K * (2 * ε)) A
      ≤ Metric.externalCoveringNumber ε (f '' A) := by
  classical
  refine le_iInf₂ fun C hC => ?_
  by_cases hA : A = ∅
  · subst hA
    simp
  · obtain ⟨a₀, ha₀⟩ := Set.nonempty_iff_ne_empty.mpr hA
    set g : Y → X := fun c => if h : ∃ a ∈ A, edist (f a) c ≤ (ε : ℝ≥0∞) then h.choose else a₀
      with hg
    have hcover : Metric.IsCover (K * (2 * ε)) A (g '' C) := by
      intro x hx
      obtain ⟨c, hc, hxc⟩ := hC ⟨x, hx, rfl⟩
      have hex : ∃ a ∈ A, edist (f a) c ≤ (ε : ℝ≥0∞) := ⟨x, hx, hxc⟩
      have hgc : g c = hex.choose := by
        rw [hg]
        exact dif_pos hex
      refine ⟨g c, ⟨c, hc, rfl⟩, ?_⟩
      have hspec := hex.choose_spec
      have hfy : edist (f (g c)) c ≤ (ε : ℝ≥0∞) := by
        rw [hgc]
        exact hspec.2
      have htri : edist (f x) (f (g c)) ≤ (ε : ℝ≥0∞) + (ε : ℝ≥0∞) := by
        refine le_trans (edist_triangle (f x) c (f (g c))) ?_
        exact add_le_add hxc (by rw [edist_comm]; exact hfy)
      have hpull : edist x (g c) ≤ (K : ℝ≥0∞) * edist (f x) (f (g c)) := hf x (g c)
      refine le_trans hpull ?_
      rw [ENNReal.coe_mul, ENNReal.coe_mul]
      refine mul_le_mul' le_rfl (le_trans htri ?_)
      rw [show ((2 : ℝ≥0) : ℝ≥0∞) * (ε : ℝ≥0∞) = (ε : ℝ≥0∞) + (ε : ℝ≥0∞) by
        rw [show ((2 : ℝ≥0) : ℝ≥0∞) = 1 + 1 by norm_num, add_mul, one_mul]]
    exact le_trans (iInf₂_le_of_le (g '' C) hcover le_rfl) (Set.encard_image_le g C)

theorem coveringCard_mono_of_le {ε₁ ε₂ : ℝ≥0} {A : Set X} {B : Set Y} {n : ℕ}
    (h : Metric.externalCoveringNumber ε₁ A ≤ Metric.externalCoveringNumber ε₂ B)
    (hfin : Metric.externalCoveringNumber ε₂ B ≤ (n : ℕ∞)) :
    coveringCard ε₁ A ≤ coveringCard ε₂ B := by
  have hmono : (Metric.externalCoveringNumber ε₂ B).toENNReal ≤ (n : ℝ≥0∞) := by
    simpa using (ENat.toENNReal_le).2 hfin
  have hne : (Metric.externalCoveringNumber ε₂ B).toENNReal ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp) hmono
  refine ENNReal.toReal_mono hne ?_
  simpa using (ENat.toENNReal_le).2 h

/-- **Box dimension transfers along a bi-Lipschitz map.**  Two-sided covering bounds on the source
give the image the same box dimension. -/
theorem hasBoxDim_image_of_covering_bounds {f : X → Y} {L K : ℝ≥0} (hL : 0 < (L : ℝ))
    (hK : 0 < (K : ℝ)) (hlip : LipschitzWith L f) (hanti : AntilipschitzWith K f) {A : Set X}
    {k : ℕ} {c₁ c₂ ε₀ : ℝ} (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hε₀ : 0 < ε₀)
    (hfin : ∀ δ : ℝ, 0 < δ → ∃ n : ℕ,
      Metric.externalCoveringNumber δ.toNNReal A ≤ (n : ℕ∞))
    (hlow : ∀ δ : ℝ, 0 < δ → δ < ε₀ → c₁ * (1 / δ) ^ k ≤ coveringCard δ.toNNReal A)
    (hupp : ∀ δ : ℝ, 0 < δ → δ < ε₀ → coveringCard δ.toNNReal A ≤ c₂ * (1 / δ) ^ k) :
    HasBoxDim (f '' A) (k : ℝ) := by
  have hKL : 0 < 2 * (K : ℝ) := by linarith
  -- the image covering number is controlled by the source at the rescaled radius
  have hrad : ∀ ε : ℝ, 0 < ε → L * (ε / (L : ℝ)).toNNReal = ε.toNNReal := by
    intro ε hε
    refine NNReal.coe_injective ?_
    push_cast
    rw [Real.coe_toNNReal _ (by positivity : (0:ℝ) ≤ ε / (L : ℝ)), Real.coe_toNNReal _ hε.le]
    field_simp
  have himgle : ∀ ε : ℝ, 0 < ε →
      Metric.externalCoveringNumber ε.toNNReal (f '' A)
        ≤ Metric.externalCoveringNumber ((ε / (L : ℝ)).toNNReal) A := by
    intro ε hε
    have himg := externalCoveringNumber_image_le hlip A ((ε / (L : ℝ)).toNNReal)
    rwa [hrad ε hε] at himg
  have himgfin : ∀ ε : ℝ, 0 < ε → ∃ n : ℕ,
      Metric.externalCoveringNumber ε.toNNReal (f '' A) ≤ (n : ℕ∞) := by
    intro ε hε
    obtain ⟨m, hm⟩ := hfin (ε / (L : ℝ)) (by positivity)
    exact ⟨m, le_trans (himgle ε hε) hm⟩
  refine hasBoxDim_of_covering_bounds (c₁ := c₁ * (1 / (2 * (K : ℝ))) ^ k)
    (c₂ := c₂ * (L : ℝ) ^ k) (ε₀ := min (ε₀ * (L : ℝ)) (ε₀ / (2 * (K : ℝ))))
    (by positivity) (by positivity) (lt_min (by positivity) (by positivity)) ?_ ?_
  · intro ε hε hεmin
    have hεK : 2 * (K : ℝ) * ε < ε₀ := by
      have hlt := lt_of_lt_of_le hεmin (min_le_right _ _)
      rw [lt_div_iff₀ hKL] at hlt
      linarith
    have hsrc := hlow (2 * (K : ℝ) * ε) (by positivity) hεK
    have hradius : ((2 * (K : ℝ) * ε).toNNReal) = K * (2 * ε.toNNReal) := by
      refine NNReal.coe_injective ?_
      rw [Real.coe_toNNReal _ (by positivity : (0:ℝ) ≤ 2 * (K : ℝ) * ε)]
      push_cast
      rw [Real.coe_toNNReal _ hε.le]
      ring
    have hle : Metric.externalCoveringNumber ((2 * (K : ℝ) * ε).toNNReal) A
        ≤ Metric.externalCoveringNumber ε.toNNReal (f '' A) := by
      rw [hradius]
      exact externalCoveringNumber_le_of_antilipschitz hanti A ε.toNNReal
    obtain ⟨n, hn⟩ := himgfin ε hε
    have hcc : coveringCard ((2 * (K : ℝ) * ε).toNNReal) A
        ≤ coveringCard ε.toNNReal (f '' A) := coveringCard_mono_of_le hle hn
    refine le_trans (le_of_eq ?_) (le_trans hsrc hcc)
    rw [mul_assoc, ← mul_pow]
    congr 2
    field_simp
  · intro ε hε hεmin
    have hεL : ε / (L : ℝ) < ε₀ := by
      have hlt := lt_of_lt_of_le hεmin (min_le_left _ _)
      rw [div_lt_iff₀ hL]
      linarith
    have hsrc := hupp (ε / (L : ℝ)) (by positivity) hεL
    obtain ⟨m, hm⟩ := hfin (ε / (L : ℝ)) (by positivity)
    have hcc : coveringCard ε.toNNReal (f '' A) ≤ coveringCard ((ε / (L : ℝ)).toNNReal) A :=
      coveringCard_mono_of_le (himgle ε hε) hm
    refine le_trans hcc (le_trans hsrc (le_of_eq ?_))
    rw [mul_assoc, ← mul_pow]
    congr 2
    field_simp

end

end GaloisForLFunctions.HTGeometry
