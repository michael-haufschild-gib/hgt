/-
The seam sign bit: a second deformation invariant on the critical line.

The critical line of an FE + Schwarz-symmetric member is real: on `s = ½+iτ` the reflection
`s ↦ 1 − s` and the Schwarz conjugation `s ↦ conj s` coincide (`conj s = 1 − s`), so
`f(s) = f(1−s) = f(conj s) = conj f(s)`, forcing `f(s)` real. Where the restriction is nonvanishing
it therefore carries a sign, and that sign is a deformation invariant alongside the deck charge:
a continuous nonvanishing real family cannot change sign, so the sign bit at a line anchor is
conserved by any boundary-nonvanishing deformation. Off-line zeros are exactly the defects that
carry deck charge yet are invisible to this seam sign data; an odd on-line defect flips the sign
between anchors bracketing it, and a sign bracket on the seam is undeformable — an on-line zero is
pinned between anchors whose product of real restrictions is negative.
-/
import GaloisForLFunctions.RHTower.GoldilocksTrichotomy
import GaloisForLFunctions.RHTower.HardyCarrier
import GaloisForLFunctions.RHTower.ConnectedSymmetryBarrier

open Complex

namespace RHTower

/-- **Reality on the seam.**  An FE + Schwarz-symmetric member is real-valued on the critical line:
on `s = ½+iτ` the functional-equation reflection and the Schwarz conjugation coincide
(`conj s = 1 − s`), so `f s = f (1 − s) = f (conj s) = conj (f s)`, hence `f s` equals its own
conjugate and is real. Only the FE and Schwarz clauses are used. -/
theorem fESchwarz_real_on_line {f : ℂ → ℂ} (hf : FESchwarz f) (τ : ℝ) :
    (f (linePt τ)).im = 0 := by
  obtain ⟨_, hfe, hconj⟩ := hf
  have key : (starRingEnd ℂ) (f (linePt τ)) = f (linePt τ) := by
    have h1 := hconj (linePt τ)
    rw [conj_linePt] at h1
    rw [hfe (linePt τ)] at h1
    exact h1.symm
  exact Complex.conj_eq_iff_im.mp key

/-- **Seam sign conservation.**  Along a family whose restriction to a fixed line point `linePt τ` is
continuous, real, and nonvanishing in the deformation parameter, the sign of the real part is
conserved: a continuous never-zero real function cannot change sign between the endpoints, since the
intermediate value theorem would otherwise produce a zero. -/
theorem line_sign_conserved {F : ℝ → ℂ → ℂ} {τ : ℝ}
    (hc : Continuous fun t : ℝ => F t (linePt τ))
    (hreal : ∀ t : ℝ, (F t (linePt τ)).im = 0)
    (hnv : ∀ t : ℝ, F t (linePt τ) ≠ 0) :
    (0 < (F 0 (linePt τ)).re ↔ 0 < (F 1 (linePt τ)).re) := by
  have hgc : Continuous (fun t : ℝ => (F t (linePt τ)).re) := Complex.continuous_re.comp hc
  have hgne : ∀ t : ℝ, (F t (linePt τ)).re ≠ 0 := by
    intro t hgt
    exact hnv t (Complex.ext hgt (hreal t))
  have hcon : ContinuousOn (fun t : ℝ => (F t (linePt τ)).re) (Set.Icc 0 1) := hgc.continuousOn
  constructor
  · intro h0
    by_contra h1
    have h1' : (F 1 (linePt τ)).re < 0 := lt_of_le_of_ne (not_lt.mp h1) (hgne 1)
    have hmem : (0:ℝ) ∈ Set.Icc ((F 1 (linePt τ)).re) ((F 0 (linePt τ)).re) := ⟨h1'.le, h0.le⟩
    obtain ⟨c, _, hc0⟩ := intermediate_value_Icc' (by norm_num : (0:ℝ) ≤ 1) hcon hmem
    exact hgne c hc0
  · intro h1
    by_contra h0
    have h0' : (F 0 (linePt τ)).re < 0 := lt_of_le_of_ne (not_lt.mp h0) (hgne 0)
    have hmem : (0:ℝ) ∈ Set.Icc ((F 0 (linePt τ)).re) ((F 1 (linePt τ)).re) := ⟨h0'.le, h1.le⟩
    obtain ⟨c, _, hc0⟩ := intermediate_value_Icc (by norm_num : (0:ℝ) ≤ 1) hcon hmem
    exact hgne c hc0

/-- **Two conserved seam invariants.**  A deformation of window pairs conserves a *pair* of
quantities: the deck charge at every level (`boxCharge_conserved_moving`) and the seam sign bit at
each of two line anchors (`line_sign_conserved`). An odd on-line defect flips the sign between
anchors bracketing it, while any off-line mirror pair is invisible to both anchors — carrying deck
charge without touching the seam sign data. -/
theorem seam_two_invariants_conserved (k : ℕ) {F : ℝ → ℂ → ℂ} {c : ℝ → ℂ} {r : ℝ → ℝ}
    {τ₁ τ₂ : ℝ}
    (hc : Continuous fun p : ℝ × ℝ => F p.1 (c p.1 + ↑(r p.1) * exp (I * ↑p.2)))
    (hnv : ∀ σ θ : ℝ, F σ (c σ + ↑(r σ) * exp (I * ↑θ)) ≠ 0)
    (hc₁ : Continuous fun t : ℝ => F t (linePt τ₁))
    (hreal₁ : ∀ t : ℝ, (F t (linePt τ₁)).im = 0)
    (hnv₁ : ∀ t : ℝ, F t (linePt τ₁) ≠ 0)
    (hc₂ : Continuous fun t : ℝ => F t (linePt τ₂))
    (hreal₂ : ∀ t : ℝ, (F t (linePt τ₂)).im = 0)
    (hnv₂ : ∀ t : ℝ, F t (linePt τ₂) ≠ 0) :
    boxCharge k (F 0) (c 0) (r 0) = boxCharge k (F 1) (c 1) (r 1) ∧
      (0 < (F 0 (linePt τ₁)).re ↔ 0 < (F 1 (linePt τ₁)).re) ∧
      (0 < (F 0 (linePt τ₂)).re ↔ 0 < (F 1 (linePt τ₂)).re) :=
  ⟨boxCharge_conserved_moving k hc hnv,
    line_sign_conserved hc₁ hreal₁ hnv₁,
    line_sign_conserved hc₂ hreal₂ hnv₂⟩

/-- **Bracket pinning.**  A sign bracket on the seam is undeformable: if at the initial time the real
restrictions at two line anchors have opposite signs (negative product), then at the final time —
after any deformation keeping both anchors nonvanishing — an on-line zero survives between them.
The two anchor signs are transported by `line_sign_conserved`, so the bracket persists to the final
time; the real-valued continuous restriction along the line then changes sign on `[τ₁, τ₂]`, and the
intermediate value theorem plus reality on the segment forces `F 1 (linePt τ) = 0`. Odd on-line
defects are pinned to the critical line; off-line zeros are exactly the defects carrying deck charge
that no such bracket ever forces back. -/
theorem online_zero_pinned_of_sign_bracket {F : ℝ → ℂ → ℂ} {τ₁ τ₂ : ℝ} (hτ : τ₁ ≤ τ₂)
    (hc₁ : Continuous fun t : ℝ => F t (linePt τ₁))
    (hc₂ : Continuous fun t : ℝ => F t (linePt τ₂))
    (hreal₁ : ∀ t : ℝ, (F t (linePt τ₁)).im = 0)
    (hreal₂ : ∀ t : ℝ, (F t (linePt τ₂)).im = 0)
    (hnv₁ : ∀ t : ℝ, F t (linePt τ₁) ≠ 0)
    (hnv₂ : ∀ t : ℝ, F t (linePt τ₂) ≠ 0)
    (hline : Continuous fun τ : ℝ => F 1 (linePt τ))
    (hreal_seg : ∀ τ ∈ Set.Icc τ₁ τ₂, (F 1 (linePt τ)).im = 0)
    (hbracket : (F 0 (linePt τ₁)).re * (F 0 (linePt τ₂)).re < 0) :
    ∃ τ ∈ Set.Icc τ₁ τ₂, F 1 (linePt τ) = 0 := by
  have iff₁ := line_sign_conserved hc₁ hreal₁ hnv₁
  have iff₂ := line_sign_conserved hc₂ hreal₂ hnv₂
  have ha₁ : (F 1 (linePt τ₁)).re ≠ 0 := fun h => hnv₁ 1 (Complex.ext h (hreal₁ 1))
  have hb₁ : (F 1 (linePt τ₂)).re ≠ 0 := fun h => hnv₂ 1 (Complex.ext h (hreal₂ 1))
  have neg_of : ∀ {x y : ℝ}, (0 < x ↔ 0 < y) → y ≠ 0 → x < 0 → y < 0 := by
    intro x y hiff hy hx
    exact lt_of_le_of_ne (not_lt.mp (mt hiff.mpr (not_lt.mpr hx.le))) hy
  have hcon : ContinuousOn (fun τ : ℝ => (F 1 (linePt τ)).re) (Set.Icc τ₁ τ₂) :=
    (Complex.continuous_re.comp hline).continuousOn
  have hbr1 : (F 1 (linePt τ₁)).re * (F 1 (linePt τ₂)).re < 0 := by
    rcases mul_neg_iff.mp hbracket with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exact mul_neg_of_pos_of_neg (iff₁.mp ha) (neg_of iff₂ hb₁ hb)
    · exact mul_neg_of_neg_of_pos (neg_of iff₁ ha₁ ha) (iff₂.mp hb)
  rcases mul_neg_iff.mp hbr1 with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · have hmem : (0:ℝ) ∈ Set.Icc ((F 1 (linePt τ₂)).re) ((F 1 (linePt τ₁)).re) := ⟨hb.le, ha.le⟩
    obtain ⟨τ, hτmem, hτ0⟩ := intermediate_value_Icc' hτ hcon hmem
    exact ⟨τ, hτmem, Complex.ext hτ0 (hreal_seg τ hτmem)⟩
  · have hmem : (0:ℝ) ∈ Set.Icc ((F 1 (linePt τ₁)).re) ((F 1 (linePt τ₂)).re) := ⟨ha.le, hb.le⟩
    obtain ⟨τ, hτmem, hτ0⟩ := intermediate_value_Icc hτ hcon hmem
    exact ⟨τ, hτmem, Complex.ext hτ0 (hreal_seg τ hτmem)⟩

end RHTower
