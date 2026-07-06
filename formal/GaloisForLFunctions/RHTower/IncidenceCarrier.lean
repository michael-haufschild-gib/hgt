/-
The incidence carrier of an anchored pencil: reality, mirror action, and forced events.

The zero dynamics of the whole pencil `c·Λ₁ + d·Λ₂` is the level-set geometry of the one
meromorphic function `incidence = −Λ₂/Λ₁`: a member vanishes at a point iff its parameter
ratio equals the incidence value there.  Members traversed by a real deformation path have
real ratio, so the entire boundary-crossing event set of the family lives on the real
locus `Im(incidence) = 0`, and its edge geometry is read from the imaginary part:

* the functional equation acts on incidence values as the Möbius involution
  `r ↦ (ε'/ε)/r` — the parameter-space form of the mirror identity;
* on the critical line a pencil of real-FE carriers has real incidence: the seam is
  contained in the real locus, so seam points are degenerate for the transversal event
  structure and carry their own ledger;
* where `Im(incidence)` does not vanish, no real-ratio member vanishes at all — the
  quiet-edge certificate; where its endpoint signs bracket, a real-ratio member is
  forced to vanish on the edge — a forced transversal event from two point evaluations;
* the incidence value vanishes only at zeros of `Λ₂`, so a pencil anchored at a
  nonvanishing `Λ₁` has incidence omitting `∞` and hitting `0` only on the target's
  zero set.
-/
import GaloisForLFunctions.RHTower.MirrorPencil
import GaloisForLFunctions.RHTower.SeamParity

namespace RHTower

open Complex Metric

/-- **The Möbius mirror action.**  Under the functional-equation pair
`Λ₁(1−s) = ε·Λ₂(s)`, `Λ₂(1−s) = ε'·Λ₁(s)`, the incidence carrier transforms by the
parameter-space involution `r ↦ (ε'/ε)/r`. -/
theorem incidence_mirror {Λ₁ Λ₂ : ℂ → ℂ} {ε ε' : ℂ}
    (hFE₁ : ∀ s, Λ₁ (1 - s) = ε * Λ₂ s) (hFE₂ : ∀ s, Λ₂ (1 - s) = ε' * Λ₁ s)
    {s : ℂ} (hε : ε ≠ 0) (hΛ₂ : Λ₂ s ≠ 0) :
    incidence Λ₁ Λ₂ (1 - s) = (ε' / ε) / incidence Λ₁ Λ₂ s := by
  by_cases hΛ₁ : Λ₁ s = 0
  · simp only [incidence]
    rw [hFE₁, hFE₂, hΛ₁]
    simp
  · simp only [incidence]
    rw [hFE₁, hFE₂]
    field_simp

/-- The incidence value vanishes exactly on the zero set of `Λ₂`, away from zeros of
the anchor `Λ₁`. -/
theorem incidence_eq_zero_iff {Λ₁ Λ₂ : ℂ → ℂ} {s : ℂ} (hΛ₁ : Λ₁ s ≠ 0) :
    incidence Λ₁ Λ₂ s = 0 ↔ Λ₂ s = 0 := by
  simp [incidence, div_eq_zero_iff, hΛ₁]

/-- **The seam lies in the real locus.**  A pencil of carriers that are real on the
critical line has real incidence there: every seam point is degenerate for the
transversal event structure. -/
theorem incidence_im_eq_zero_on_line {Λ₁ Λ₂ : ℂ → ℂ} {τ : ℝ}
    (h₁ : (Λ₁ (linePt τ)).im = 0) (h₂ : (Λ₂ (linePt τ)).im = 0) :
    (incidence Λ₁ Λ₂ (linePt τ)).im = 0 := by
  have e₁ : Λ₁ (linePt τ) = (((Λ₁ (linePt τ)).re : ℝ) : ℂ) :=
    Complex.ext rfl (by simp [h₁])
  have e₂ : Λ₂ (linePt τ) = (((Λ₂ (linePt τ)).re : ℝ) : ℂ) :=
    Complex.ext rfl (by simp [h₂])
  rw [incidence, e₁, e₂, ← Complex.ofReal_neg, ← Complex.ofReal_div]
  exact Complex.ofReal_im _

/-- **The quiet-edge certificate.**  Where the incidence carrier is not real, no member
of the pencil with real parameter ratio vanishes: a nonvanishing imaginary part excludes
every crossing event of every real deformation path at once. -/
theorem real_pencil_ne_zero_of_im_incidence_ne {Λ₁ Λ₂ : ℂ → ℂ} {s₀ : ℂ}
    (hΛ₁ : Λ₁ s₀ ≠ 0) (him : (incidence Λ₁ Λ₂ s₀).im ≠ 0)
    (c d : ℝ) (hcd : ¬(c = 0 ∧ d = 0)) :
    pencil Λ₁ Λ₂ (c : ℂ) (d : ℂ) s₀ ≠ 0 := by
  intro h0
  by_cases hd : d = 0
  · have hc : c ≠ 0 := fun hc => hcd ⟨hc, hd⟩
    rw [hd] at h0
    simp only [pencil, Complex.ofReal_zero, zero_mul, add_zero] at h0
    exact hΛ₁ ((mul_eq_zero.mp h0).resolve_left
      (fun h => hc (by exact_mod_cast h)))
  · have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd
    have hratio := (pencil_eq_zero_iff_incidence hdC hΛ₁).mp h0
    apply him
    rw [← hratio, ← Complex.ofReal_div]
    exact Complex.ofReal_im _

/-- **The band sign of an edge**: the endpoint product of the imaginary part of the
incidence carrier along a parameterized edge. -/
noncomputable def bandSign (Λ₁ Λ₂ : ℂ → ℂ) (γ : ℝ → ℂ) (a b : ℝ) : ℝ :=
  (incidence Λ₁ Λ₂ (γ a)).im * (incidence Λ₁ Λ₂ (γ b)).im

/-- An edge on which the incidence carrier is nowhere real has positive band sign. -/
theorem bandSign_pos_of_im_ne_zero {Λ₁ Λ₂ : ℂ → ℂ} {γ : ℝ → ℂ} {a b : ℝ}
    (hab : a ≤ b)
    (hcont : ContinuousOn (fun t => (incidence Λ₁ Λ₂ (γ t)).im) (Set.Icc a b))
    (hne : ∀ t ∈ Set.Icc a b, (incidence Λ₁ Λ₂ (γ t)).im ≠ 0) :
    0 < bandSign Λ₁ Λ₂ γ a b :=
  endpoint_sign_product_pos hab hcont hne

/-- **The forced-event bracket.**  A negative band sign forces a real-ratio member of
the pencil to vanish somewhere on the edge: two point evaluations of the incidence
carrier certify a transversal crossing event of the real family sweep. -/
theorem exists_real_member_zero_of_bandSign_neg {Λ₁ Λ₂ : ℂ → ℂ} {γ : ℝ → ℂ} {a b : ℝ}
    (hab : a ≤ b)
    (hcont : ContinuousOn (fun t => (incidence Λ₁ Λ₂ (γ t)).im) (Set.Icc a b))
    (hΛ₁ : ∀ t ∈ Set.Icc a b, Λ₁ (γ t) ≠ 0)
    (hbr : bandSign Λ₁ Λ₂ γ a b < 0) :
    ∃ t ∈ Set.Icc a b, ∃ r : ℝ, pencil Λ₁ Λ₂ (r : ℂ) 1 (γ t) = 0 := by
  have hivt : ∃ t ∈ Set.Icc a b, (incidence Λ₁ Λ₂ (γ t)).im = 0 := by
    rcases mul_neg_iff.mp hbr with ⟨hpa, hnb⟩ | ⟨hna, hpb⟩
    · obtain ⟨t, ht, hFt⟩ := intermediate_value_Icc' hab hcont
        (Set.mem_Icc.mpr ⟨hnb.le, hpa.le⟩)
      exact ⟨t, ht, hFt⟩
    · obtain ⟨t, ht, hFt⟩ := intermediate_value_Icc hab hcont
        (Set.mem_Icc.mpr ⟨hna.le, hpb.le⟩)
      exact ⟨t, ht, hFt⟩
  obtain ⟨t₀, ht₀, him0⟩ := hivt
  refine ⟨t₀, ht₀, (incidence Λ₁ Λ₂ (γ t₀)).re, ?_⟩
  have hre : incidence Λ₁ Λ₂ (γ t₀) =
      (((incidence Λ₁ Λ₂ (γ t₀)).re : ℝ) : ℂ) :=
    Complex.ext rfl (by simp [him0])
  have hdiv : -Λ₂ (γ t₀) / Λ₁ (γ t₀) =
      (((incidence Λ₁ Λ₂ (γ t₀)).re : ℝ) : ℂ) := hre
  rw [div_eq_iff (hΛ₁ t₀ ht₀)] at hdiv
  show (((incidence Λ₁ Λ₂ (γ t₀)).re : ℝ) : ℂ) * Λ₁ (γ t₀) + 1 * Λ₂ (γ t₀) = 0
  linear_combination -hdiv

end RHTower
