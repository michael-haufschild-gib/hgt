import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Slicing.LineStrips

/-! # From a large mixed derivative to consecutive coordinate strips -/

open MeasureTheory Set
open scoped ENNReal
namespace GaloisForLFunctions.HTGeometry.SpectralJets
noncomputable section

/-- Removing outer derivatives one at a time reduces the measure bound to
one strip per letter. The mass bound need only hold on suffixes of the word. -/
theorem sublevel_le_word_length {ι X : Type*} [MeasurableSpace X] (μ : Measure X)
    (F : List ι → X → ℝ) (b : ℕ → ℝ) (w : List ι) (M : ℝ≥0∞)
    (hstrip : ∀ i v, (∃ u, w = u ++ i::v) →
      μ {x | F v x < b v.length ∧ b (v.length+1) ≤ F (i::v) x} ≤ M) :
    μ {x | F [] x < b 0 ∧ b w.length ≤ F w x} ≤ (w.length:ℝ≥0∞)*M := by
  induction w with
  | nil =>
    have he : {x | F [] x < b 0 ∧ b (([] : List ι).length) ≤ F [] x} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact hx.1.not_ge hx.2
    rw [he,measure_empty]
    exact bot_le
  | cons i w ih =>
    let A := {x | F [] x < b 0 ∧ b w.length ≤ F w x}
    let S := {x | F w x < b w.length ∧ b (w.length+1) ≤ F (i::w) x}
    have hA : μ A ≤ (w.length:ℝ≥0∞)*M := ih fun j v h => by
      obtain ⟨u,hu⟩ := h
      exact hstrip j v ⟨i::u,congrArg (List.cons i) hu⟩
    have hS : μ S ≤ M := hstrip i w ⟨[],rfl⟩
    have hsub : {x | F [] x < b 0 ∧ b (i::w).length ≤ F (i::w) x} ⊆ A ∪ S := by
      intro x hx
      rcases le_or_gt (b w.length) (F w x) with h | h
      · exact Or.inl ⟨hx.1,h⟩
      · exact Or.inr ⟨h,hx.2⟩
    exact (measure_mono hsub).trans ((measure_union_le A S).trans ((add_le_add hA hS).trans_eq
      (by simp [List.length_cons,add_mul])))

/-- Geometric thresholds turn each consecutive strip into the same cost,
independently of the derivative order. -/
theorem geometric_coordinate_strip (f : ℝ → ℝ) (C : Finset ℝ) {A q : ℝ}
    (hA : 0 < A) (hq : 0 < q) {p L : ℕ} (hp : p < L)
    (hreg : ∀ x ∉ C, DifferentiableAt ℝ f x ∧ ContinuousAt (deriv f) x)
    (hcut : ∀ x ∉ C, |deriv f x| ≠ A*q^(L-(p+1))/2) :
    volume {x | |f x| < A*q^(L-p) ∧ A*q^(L-(p+1)) ≤ |deriv f x|} ≤
      ((C.card+1 : ℕ):ℝ≥0∞)*ENNReal.ofReal (8*q) := by
  let t := A*q^(L-(p+1))
  have ht : 0 < t := mul_pos hA (pow_pos hq _)
  have h := regular_strip_volume_le f C (a := t/2) (b := A*q^(L-p)) (by positivity) (by positivity)
    hreg hcut
  have hb : A*q^(L-p) = t*q := by
    have he : L-p = (L-(p+1))+1 := by omega
    rw [he,pow_succ]
    dsimp [t]
    ring
  have h₁ : 2*(t/2) = t := by ring
  have h₂ : 4*(A*q^(L-p))/(t/2) = 8*q := by rw [hb]; field_simp [ht.ne']; ring
  rwa [h₁,h₂] at h

/-- A cut level may be chosen anywhere between one quarter and one half
of the response threshold, allowing avoidance of constant algebraic branches. -/
theorem strip_of_variable_cut (f : ℝ → ℝ) (C : Finset ℝ) {t q a : ℝ}
    (ht : 0 < t) (hq : 0 ≤ q) (ha : t/4 ≤ a) (ha' : 2*a ≤ t)
    (hreg : ∀ x ∉ C, DifferentiableAt ℝ f x ∧ ContinuousAt (deriv f) x)
    (hcut : ∀ x ∉ C, |deriv f x| ≠ a) :
    volume {x | |f x| < t*q ∧ t ≤ |deriv f x|} ≤
      ((C.card+1 : ℕ):ℝ≥0∞)*ENNReal.ofReal (16*q) := by
  have hap : 0 < a := by linarith only [ht,ha]
  have h := regular_strip_volume_le f C hap (mul_nonneg ht.le hq) hreg hcut
  apply (measure_mono (fun x hx => And.intro hx.1 (ha'.trans hx.2))).trans (h.trans ?_)
  apply mul_le_mul_right (ENNReal.ofReal_le_ofReal ?_)
  apply (div_le_iff₀ hap).mpr
  nlinarith only [mul_le_mul_of_nonneg_right ha hq]

#print axioms strip_of_variable_cut
#print axioms sublevel_le_word_length
#print axioms geometric_coordinate_strip
end
end GaloisForLFunctions.HTGeometry.SpectralJets
