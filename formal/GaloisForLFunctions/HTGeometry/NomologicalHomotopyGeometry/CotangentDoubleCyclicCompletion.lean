import GaloisForLFunctions.HTGeometry.NomologicalHomotopyGeometry.GradedLieLaw

/-!
# The shifted cotangent double of the three-storey law

For the three-storey graded Lie algebra `L = ⟨x, y, w⟩` (`x, y, w` in degrees `−1, −2, −3`,
`[x, y] = w`) and an integer `d`, the shifted cotangent double `T*[d]L = L ⋉ L*[d]` carries the
coadjoint semidirect bracket
`[x, w*] = (−1)^d y*`, `[y, w*] = x*`, `[x, y] = w`.

* `cotangentLaw d` is a graded Lie algebra on the six-dimensional space `L ⊕ L*[d]`; every double
  bracket vanishes.
* `cotangentPairing d` is the canonical evaluation pairing: nondegenerate, invariant
  (`⟨[A, B], C⟩ = ⟨A, [B, C]⟩`), graded symmetric and of degree `d`, with signs
  `s_x = s_w = 1`, `s_y = (−1)^{d+1}`.
* The inclusion `L → T*[d]L` is an injective strict graded-Lie morphism, hence filtered for the
  lower central series, and `T*[d]L` is nilpotent (`F³ = 0`).
-/

namespace GaloisForLFunctions.HTGeometry.NomologicalHomotopyGeometry

noncomputable section

/-- Coordinates of `T*[d]L = L ⊕ L*[d]`: `(u, ξ)` with `u = u₁x + u₂y + u₃w` and
`ξ = ξ₁x* + ξ₂y* + ξ₃w*`. -/
abbrev CotangentDouble := ThreeStorey × ThreeStorey

/-- The sign `ε = (−1)^d`. -/
def shiftSign (d : ℤ) : ℝ := (-1 : ℝ) ^ d

theorem shiftSign_sq (d : ℤ) : shiftSign d * shiftSign d = 1 := by
  rw [shiftSign, ← mul_zpow]; norm_num

/-- The coadjoint semidirect bracket on `T*[d]L`:
`[x, w*] = (−1)^d y*`, `[y, w*] = x*`, `[w*, x] = y*`, `[w*, y] = −x*`, `[x, y] = w`. -/
def cotangentBracket (d : ℤ) : CotangentDouble →ₗ[ℝ] CotangentDouble →ₗ[ℝ] CotangentDouble :=
  LinearMap.mk₂ ℝ (fun A B =>
    ((0, 0, A.1.1 * B.1.2.1 - A.1.2.1 * B.1.1),
      (A.1.2.1 * B.2.2.2 - B.1.2.1 * A.2.2.2,
        shiftSign d * A.1.1 * B.2.2.2 + B.1.1 * A.2.2.2, 0)))
    (fun A A' B => by ext <;> simp <;> ring)
    (fun c A B => by ext <;> simp <;> ring)
    (fun A B B' => by ext <;> simp <;> ring)
    (fun c A B => by ext <;> simp <;> ring)

@[simp] theorem cotangentBracket_apply (d : ℤ) (A B : CotangentDouble) :
    cotangentBracket d A B =
      ((0, 0, A.1.1 * B.1.2.1 - A.1.2.1 * B.1.1),
        (A.1.2.1 * B.2.2.2 - B.1.2.1 * A.2.2.2,
          shiftSign d * A.1.1 * B.2.2.2 + B.1.1 * A.2.2.2, 0)) := rfl

/-- The degree-`i` component of `T*[d]L`: `x, y, w` sit in degrees `−1, −2, −3` and the shifted
duals `x*, y*, w*` in degrees `1 − d, 2 − d, 3 − d`. -/
def cotangentComp (d i : ℤ) : Submodule ℝ CotangentDouble where
  carrier := {A | (i ≠ -1 → A.1.1 = 0) ∧ (i ≠ -2 → A.1.2.1 = 0) ∧ (i ≠ -3 → A.1.2.2 = 0) ∧
    (i ≠ 1 - d → A.2.1 = 0) ∧ (i ≠ 2 - d → A.2.2.1 = 0) ∧ (i ≠ 3 - d → A.2.2.2 = 0)}
  add_mem' := by
    rintro A B ⟨a1, a2, a3, a4, a5, a6⟩ ⟨b1, b2, b3, b4, b5, b6⟩
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩ <;>
      simp [*]
  zero_mem' := by simp
  smul_mem' := by
    rintro c A ⟨a1, a2, a3, a4, a5, a6⟩
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩ <;>
      simp [*]

variable {d : ℤ}

theorem deg_of_u1 {i : ℤ} {A : CotangentDouble} (hA : A ∈ cotangentComp d i) (h : A.1.1 ≠ 0) :
    i = -1 := by by_contra hi; exact h (hA.1 hi)
theorem deg_of_u2 {i : ℤ} {A : CotangentDouble} (hA : A ∈ cotangentComp d i) (h : A.1.2.1 ≠ 0) :
    i = -2 := by by_contra hi; exact h (hA.2.1 hi)
theorem deg_of_u3 {i : ℤ} {A : CotangentDouble} (hA : A ∈ cotangentComp d i) (h : A.1.2.2 ≠ 0) :
    i = -3 := by by_contra hi; exact h (hA.2.2.1 hi)
theorem deg_of_x1 {i : ℤ} {A : CotangentDouble} (hA : A ∈ cotangentComp d i) (h : A.2.1 ≠ 0) :
    i = 1 - d := by by_contra hi; exact h (hA.2.2.2.1 hi)
theorem deg_of_x2 {i : ℤ} {A : CotangentDouble} (hA : A ∈ cotangentComp d i) (h : A.2.2.1 ≠ 0) :
    i = 2 - d := by by_contra hi; exact h (hA.2.2.2.2.1 hi)
theorem deg_of_x3 {i : ℤ} {A : CotangentDouble} (hA : A ∈ cotangentComp d i) (h : A.2.2.2 ≠ 0) :
    i = 3 - d := by by_contra hi; exact h (hA.2.2.2.2.2 hi)

private theorem mul_eq_zero_of_degrees {a b : ℝ} {P Q : Prop} (ha : a ≠ 0 → P) (hb : b ≠ 0 → Q)
    (hPQ : P → Q → False) : a * b = 0 := by
  by_contra h
  obtain ⟨h1, h2⟩ := mul_ne_zero_iff.mp h
  exact hPQ (ha h1) (hb h2)

theorem cotangent_iSup_eq_top : iSup (cotangentComp d) = ⊤ := by
  rw [eq_top_iff]
  intro A _
  have hA : A = ((A.1.1, 0, 0), (0, 0, 0)) + ((0, A.1.2.1, 0), (0, 0, 0)) +
      ((0, 0, A.1.2.2), (0, 0, 0)) + ((0, 0, 0), (A.2.1, 0, 0)) + ((0, 0, 0), (0, A.2.2.1, 0)) +
        ((0, 0, 0), (0, 0, A.2.2.2)) := by
    ext <;> simp
  rw [hA]
  refine add_mem (add_mem (add_mem (add_mem (add_mem ?_ ?_) ?_) ?_) ?_) ?_
  · exact Submodule.mem_iSup_of_mem (-1) ⟨fun h => absurd rfl h, by simp, by simp, by simp,
      by simp, by simp⟩
  · exact Submodule.mem_iSup_of_mem (-2) ⟨by simp, fun h => absurd rfl h, by simp, by simp,
      by simp, by simp⟩
  · exact Submodule.mem_iSup_of_mem (-3) ⟨by simp, by simp, fun h => absurd rfl h, by simp,
      by simp, by simp⟩
  · exact Submodule.mem_iSup_of_mem (1 - d) ⟨by simp, by simp, by simp,
      fun h => absurd rfl h, by simp, by simp⟩
  · exact Submodule.mem_iSup_of_mem (2 - d) ⟨by simp, by simp, by simp, by simp,
      fun h => absurd rfl h, by simp⟩
  · exact Submodule.mem_iSup_of_mem (3 - d) ⟨by simp, by simp, by simp, by simp, by simp,
      fun h => absurd rfl h⟩

/-- The coordinates of degree `i` vanish. -/
def cotangentAvoid (d i : ℤ) : Submodule ℝ CotangentDouble where
  carrier := {A | (i = -1 → A.1.1 = 0) ∧ (i = -2 → A.1.2.1 = 0) ∧ (i = -3 → A.1.2.2 = 0) ∧
    (i = 1 - d → A.2.1 = 0) ∧ (i = 2 - d → A.2.2.1 = 0) ∧ (i = 3 - d → A.2.2.2 = 0)}
  add_mem' := by
    rintro A B ⟨a1, a2, a3, a4, a5, a6⟩ ⟨b1, b2, b3, b4, b5, b6⟩
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩ <;>
      simp [*]
  zero_mem' := by simp
  smul_mem' := by
    rintro c A ⟨a1, a2, a3, a4, a5, a6⟩
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩ <;>
      simp [*]

theorem cotangent_iSupIndep : iSupIndep (cotangentComp d) := by
  rw [iSupIndep_def]
  intro i
  rw [Submodule.disjoint_def]
  intro A hA hsup
  have hle : (⨆ j, ⨆ (_ : j ≠ i), cotangentComp d j) ≤ cotangentAvoid d i := by
    refine iSup₂_le fun j hj B hB => ?_
    refine ⟨fun h => hB.1 ?_, fun h => hB.2.1 ?_, fun h => hB.2.2.1 ?_, fun h => hB.2.2.2.1 ?_,
      fun h => hB.2.2.2.2.1 ?_, fun h => hB.2.2.2.2.2 ?_⟩ <;> rw [← h] <;> exact hj
  have hav := hle hsup
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hA
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := hav
  ext
  · by_cases h : i = -1
    · exact b1 h
    · exact a1 h
  · by_cases h : i = -2
    · exact b2 h
    · exact a2 h
  · by_cases h : i = -3
    · exact b3 h
    · exact a3 h
  · by_cases h : i = 1 - d
    · exact b4 h
    · exact a4 h
  · by_cases h : i = 2 - d
    · exact b5 h
    · exact a5 h
  · by_cases h : i = 3 - d
    · exact b6 h
    · exact a6 h

theorem cotangentBracket_mem {i j : ℤ} {A B : CotangentDouble} (hA : A ∈ cotangentComp d i)
    (hB : B ∈ cotangentComp d j) : cotangentBracket d A B ∈ cotangentComp d (i + j) := by
  rw [cotangentBracket_apply]
  refine ⟨fun _ => rfl, fun _ => rfl, fun hij => ?_, fun hij => ?_, fun hij => ?_, fun _ => rfl⟩
  · have t1 : A.1.1 * B.1.2.1 = 0 := mul_eq_zero_of_degrees (deg_of_u1 hA) (deg_of_u2 hB)
      (fun h1 h2 => hij (by rw [h1, h2]; norm_num))
    have t2 : A.1.2.1 * B.1.1 = 0 := mul_eq_zero_of_degrees (deg_of_u2 hA) (deg_of_u1 hB)
      (fun h1 h2 => hij (by rw [h1, h2]; norm_num))
    simp [t1, t2]
  · have t1 : A.1.2.1 * B.2.2.2 = 0 := mul_eq_zero_of_degrees (deg_of_u2 hA) (deg_of_x3 hB)
      (fun h1 h2 => hij (by rw [h1, h2]; ring))
    have t2 : B.1.2.1 * A.2.2.2 = 0 := mul_eq_zero_of_degrees (deg_of_u2 hB) (deg_of_x3 hA)
      (fun h1 h2 => hij (by rw [h1, h2]; ring))
    simp [t1, t2]
  · have t1 : A.1.1 * B.2.2.2 = 0 := mul_eq_zero_of_degrees (deg_of_u1 hA) (deg_of_x3 hB)
      (fun h1 h2 => hij (by rw [h1, h2]; ring))
    have t2 : B.1.1 * A.2.2.2 = 0 := mul_eq_zero_of_degrees (deg_of_u1 hB) (deg_of_x3 hA)
      (fun h1 h2 => hij (by rw [h1, h2]; ring))
    simp [mul_assoc, t1, t2]

theorem koszulSign_neg_one_three_sub (d : ℤ) :
    shiftSign d + koszulSign (-1) (3 - d) = 0 := by
  rw [shiftSign, koszulSign, show (-1 : ℤ) * (3 - d) = d + (-3) by ring,
    zpow_add₀ (by norm_num : (-1 : ℝ) ≠ 0)]
  norm_num

theorem koszulSign_three_sub_neg_one (d : ℤ) :
    1 + koszulSign (3 - d) (-1) * shiftSign d = 0 := by
  rw [shiftSign, koszulSign, ← zpow_add₀ (by norm_num : (-1 : ℝ) ≠ 0),
    show (3 - d) * (-1) + d = 2 * d + (-3) by ring, zpow_add₀ (by norm_num : (-1 : ℝ) ≠ 0),
    zpow_mul]
  norm_num

theorem cotangentBracket_antisymm {i j : ℤ} {A B : CotangentDouble}
    (hA : A ∈ cotangentComp d i) (hB : B ∈ cotangentComp d j) :
    cotangentBracket d A B = -(koszulSign i j • cotangentBracket d B A) := by
  rw [cotangentBracket_apply, cotangentBracket_apply]
  -- the `w`-coordinate
  have hw : (1 - koszulSign i j) * (A.1.1 * B.1.2.1 - A.1.2.1 * B.1.1) = 0 := by
    have t1 : (1 - koszulSign i j) * (A.1.1 * B.1.2.1) = 0 := by
      by_cases h : A.1.1 * B.1.2.1 = 0
      · rw [h, mul_zero]
      · obtain ⟨h1, h2⟩ := mul_ne_zero_iff.mp h
        rw [deg_of_u1 hA h1, deg_of_u2 hB h2]; norm_num [koszulSign]
    have t2 : (1 - koszulSign i j) * (A.1.2.1 * B.1.1) = 0 := by
      by_cases h : A.1.2.1 * B.1.1 = 0
      · rw [h, mul_zero]
      · obtain ⟨h1, h2⟩ := mul_ne_zero_iff.mp h
        rw [deg_of_u2 hA h1, deg_of_u1 hB h2]; norm_num [koszulSign]
    linear_combination t1 - t2
  -- the `x*`-coordinate
  have hx : (1 - koszulSign i j) * (A.1.2.1 * B.2.2.2 - B.1.2.1 * A.2.2.2) = 0 := by
    have t1 : (1 - koszulSign i j) * (A.1.2.1 * B.2.2.2) = 0 := by
      by_cases h : A.1.2.1 * B.2.2.2 = 0
      · rw [h, mul_zero]
      · obtain ⟨h1, h2⟩ := mul_ne_zero_iff.mp h
        rw [deg_of_u2 hA h1, deg_of_x3 hB h2, koszulSign,
          show (-2 : ℤ) * (3 - d) = 2 * (d - 3) by ring, zpow_mul]
        norm_num
    have t2 : (1 - koszulSign i j) * (B.1.2.1 * A.2.2.2) = 0 := by
      by_cases h : B.1.2.1 * A.2.2.2 = 0
      · rw [h, mul_zero]
      · obtain ⟨h1, h2⟩ := mul_ne_zero_iff.mp h
        rw [deg_of_u2 hB h1, deg_of_x3 hA h2, koszulSign,
          show (3 - d) * (-2 : ℤ) = 2 * (d - 3) by ring, zpow_mul]
        norm_num
    linear_combination t1 - t2
  -- the `y*`-coordinate
  have hy : A.1.1 * B.2.2.2 * (shiftSign d + koszulSign i j) +
      B.1.1 * A.2.2.2 * (1 + koszulSign i j * shiftSign d) = 0 := by
    have t1 : A.1.1 * B.2.2.2 * (shiftSign d + koszulSign i j) = 0 := by
      by_cases h : A.1.1 * B.2.2.2 = 0
      · rw [h, zero_mul]
      · obtain ⟨h1, h2⟩ := mul_ne_zero_iff.mp h
        rw [deg_of_u1 hA h1, deg_of_x3 hB h2, koszulSign_neg_one_three_sub, mul_zero]
    have t2 : B.1.1 * A.2.2.2 * (1 + koszulSign i j * shiftSign d) = 0 := by
      by_cases h : B.1.1 * A.2.2.2 = 0
      · rw [h, zero_mul]
      · obtain ⟨h1, h2⟩ := mul_ne_zero_iff.mp h
        rw [deg_of_u1 hB h1, deg_of_x3 hA h2, koszulSign_three_sub_neg_one, mul_zero]
    linear_combination t1 + t2
  ext <;> simp
  · linear_combination hw
  · linear_combination hx
  · linear_combination hy

theorem cotangentBracket_bracket_eq_zero (A B C : CotangentDouble) :
    cotangentBracket d A (cotangentBracket d B C) = 0 := by
  simp

variable (d) in
/-- **The shifted cotangent double** `T*[d]L = L ⋉ L*[d]` with its coadjoint semidirect bracket. -/
def cotangentLaw : GradedLieAlgebra CotangentDouble where
  comp := cotangentComp d
  isInternal := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top cotangent_iSupIndep
    cotangent_iSup_eq_top
  bracket := cotangentBracket d
  bracket_mem := cotangentBracket_mem
  antisymm := cotangentBracket_antisymm
  jacobi := by
    intro i j k u v w _ _ _
    simp only [cotangentBracket_bracket_eq_zero, smul_zero, add_zero]

variable (d) in
/-- The canonical pairing of `T*[d]L`:
`⟨(u, ξ), (v, ζ)⟩ = ζ_x u_x − ε ζ_y u_y + ζ_w u_w − ε (ξ_x v_x + ξ_y v_y + ξ_w v_w)`,
with `ε = (−1)^d`. -/
def cotangentPairing : CotangentDouble →ₗ[ℝ] CotangentDouble →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun A B =>
    A.1.1 * B.2.1 - shiftSign d * (A.1.2.1 * B.2.2.1) + A.1.2.2 * B.2.2.2 -
      shiftSign d * (A.2.1 * B.1.1 + A.2.2.1 * B.1.2.1 + A.2.2.2 * B.1.2.2))
    (fun A A' B => by simp; ring) (fun c A B => by simp; ring)
    (fun A B B' => by simp; ring) (fun c A B => by simp; ring)

@[simp] theorem cotangentPairing_apply (A B : CotangentDouble) :
    cotangentPairing d A B = A.1.1 * B.2.1 - shiftSign d * (A.1.2.1 * B.2.2.1) +
      A.1.2.2 * B.2.2.2 - shiftSign d * (A.2.1 * B.1.1 + A.2.2.1 * B.1.2.1 + A.2.2.2 * B.1.2.2) :=
  rfl

/-- **Invariance**: `⟨[A, B], C⟩ = ⟨A, [B, C]⟩`. -/
theorem cotangentPairing_invariant (A B C : CotangentDouble) :
    cotangentPairing d (cotangentBracket d A B) C =
      cotangentPairing d A (cotangentBracket d B C) := by
  have hε := shiftSign_sq d
  simp only [cotangentPairing_apply, cotangentBracket_apply]
  linear_combination (A.1.2.1 * B.1.1 * C.2.2.2 - A.1.1 * B.2.2.2 * C.1.2.1) * hε

/-- **Nondegeneracy** of the pairing. -/
theorem cotangentPairing_nondegenerate (A : CotangentDouble) (h : ∀ B, cotangentPairing d A B = 0) :
    A = 0 := by
  have hε : shiftSign d ≠ 0 := fun h0 => by simpa [h0] using shiftSign_sq d
  have h1 := h ((0, 0, 0), (1, 0, 0))
  have h2 := h ((0, 0, 0), (0, 1, 0))
  have h3 := h ((0, 0, 0), (0, 0, 1))
  have h4 := h ((1, 0, 0), (0, 0, 0))
  have h5 := h ((0, 1, 0), (0, 0, 0))
  have h6 := h ((0, 0, 1), (0, 0, 0))
  simp only [cotangentPairing_apply] at h1 h2 h3 h4 h5 h6
  ext <;> simp_all

/-- The pairing has degree `d`: it pairs only components of total degree `−d`. -/
theorem cotangentPairing_degree {i j : ℤ} {A B : CotangentDouble} (hA : A ∈ cotangentComp d i)
    (hB : B ∈ cotangentComp d j) (hij : i + j ≠ -d) : cotangentPairing d A B = 0 := by
  have z1 : A.1.1 * B.2.1 = 0 := mul_eq_zero_of_degrees (deg_of_u1 hA) (deg_of_x1 hB)
    (fun h1 h2 => hij (by rw [h1, h2]; ring))
  have z2 : A.1.2.1 * B.2.2.1 = 0 := mul_eq_zero_of_degrees (deg_of_u2 hA) (deg_of_x2 hB)
    (fun h1 h2 => hij (by rw [h1, h2]; ring))
  have z3 : A.1.2.2 * B.2.2.2 = 0 := mul_eq_zero_of_degrees (deg_of_u3 hA) (deg_of_x3 hB)
    (fun h1 h2 => hij (by rw [h1, h2]; ring))
  have z4 : A.2.1 * B.1.1 = 0 := mul_eq_zero_of_degrees (deg_of_x1 hA) (deg_of_u1 hB)
    (fun h1 h2 => hij (by rw [h1, h2]; ring))
  have z5 : A.2.2.1 * B.1.2.1 = 0 := mul_eq_zero_of_degrees (deg_of_x2 hA) (deg_of_u2 hB)
    (fun h1 h2 => hij (by rw [h1, h2]; ring))
  have z6 : A.2.2.2 * B.1.2.2 = 0 := mul_eq_zero_of_degrees (deg_of_x3 hA) (deg_of_u3 hB)
    (fun h1 h2 => hij (by rw [h1, h2]; ring))
  rw [cotangentPairing_apply, z1, z2, z3, z4, z5, z6]
  ring

theorem koszulSign_dual_pair (d : ℤ) : koszulSign (-1) (1 - d) = -shiftSign d := by
  rw [koszulSign, shiftSign, show (-1 : ℤ) * (1 - d) = d + (-1) by ring,
    zpow_add₀ (by norm_num : (-1 : ℝ) ≠ 0)]
  norm_num

/-- **Graded symmetry** of the pairing: `⟨B, A⟩ = (−1)^{|A||B|} ⟨A, B⟩`. -/
theorem cotangentPairing_graded_symm {i j : ℤ} {A B : CotangentDouble}
    (hA : A ∈ cotangentComp d i) (hB : B ∈ cotangentComp d j) :
    cotangentPairing d B A = koszulSign i j * cotangentPairing d A B := by
  have hε := shiftSign_sq d
  -- each product pins the degrees, hence the Koszul sign
  have c1 : A.1.1 * B.2.1 * (koszulSign i j + shiftSign d) = 0 := by
    by_cases h : A.1.1 * B.2.1 = 0
    · rw [h, zero_mul]
    · obtain ⟨h1, h2⟩ := mul_ne_zero_iff.mp h
      rw [deg_of_u1 hA h1, deg_of_x1 hB h2, koszulSign_dual_pair]; ring
  have c4 : A.2.1 * B.1.1 * (koszulSign i j * shiftSign d + 1) = 0 := by
    by_cases h : A.2.1 * B.1.1 = 0
    · rw [h, zero_mul]
    · obtain ⟨h1, h2⟩ := mul_ne_zero_iff.mp h
      rw [deg_of_x1 hA h1, deg_of_u1 hB h2, koszulSign_comm, koszulSign_dual_pair]
      linear_combination (-(A.2.1 * B.1.1)) * hε
  have c2 : A.1.2.1 * B.2.2.1 * (koszulSign i j - 1) = 0 := by
    by_cases h : A.1.2.1 * B.2.2.1 = 0
    · rw [h, zero_mul]
    · obtain ⟨h1, h2⟩ := mul_ne_zero_iff.mp h
      rw [deg_of_u2 hA h1, deg_of_x2 hB h2, koszulSign,
        show (-2 : ℤ) * (2 - d) = 2 * (d - 2) by ring, zpow_mul]
      norm_num
  have c5 : A.2.2.1 * B.1.2.1 * (koszulSign i j - 1) = 0 := by
    by_cases h : A.2.2.1 * B.1.2.1 = 0
    · rw [h, zero_mul]
    · obtain ⟨h1, h2⟩ := mul_ne_zero_iff.mp h
      rw [deg_of_x2 hA h1, deg_of_u2 hB h2, koszulSign,
        show (2 - d) * (-2 : ℤ) = 2 * (d - 2) by ring, zpow_mul]
      norm_num
  have c3 : A.1.2.2 * B.2.2.2 * (koszulSign i j + shiftSign d) = 0 := by
    by_cases h : A.1.2.2 * B.2.2.2 = 0
    · rw [h, zero_mul]
    · obtain ⟨h1, h2⟩ := mul_ne_zero_iff.mp h
      rw [deg_of_u3 hA h1, deg_of_x3 hB h2, koszulSign, shiftSign,
        show (-3 : ℤ) * (3 - d) = (d + (-1)) + 2 * (d - 4) by ring,
        zpow_add₀ (by norm_num : (-1 : ℝ) ≠ 0), zpow_add₀ (by norm_num : (-1 : ℝ) ≠ 0), zpow_mul]
      norm_num
  have c6 : A.2.2.2 * B.1.2.2 * (koszulSign i j * shiftSign d + 1) = 0 := by
    by_cases h : A.2.2.2 * B.1.2.2 = 0
    · rw [h, zero_mul]
    · obtain ⟨h1, h2⟩ := mul_ne_zero_iff.mp h
      rw [deg_of_x3 hA h1, deg_of_u3 hB h2, koszulSign, shiftSign,
        ← zpow_add₀ (by norm_num : (-1 : ℝ) ≠ 0),
        show (3 - d) * (-3 : ℤ) + d = (-1) + 2 * (2 * d - 4) by ring,
        zpow_add₀ (by norm_num : (-1 : ℝ) ≠ 0), zpow_mul]
      norm_num
  simp only [cotangentPairing_apply]
  linear_combination -c1 + c4 + shiftSign d * c2 + shiftSign d * c5 - c3 + c6

/-- The inclusion `L → T*[d]L`. -/
def cotangentInclusion : GradedLieHom threeStoreyLaw (cotangentLaw d) where
  toLinearMap := LinearMap.inl ℝ ThreeStorey ThreeStorey
  map_comp := by
    intro i u hu
    rcases mem_threeStoreyComp.mp hu with ⟨rfl, h2, h3⟩ | ⟨rfl, h1, h3⟩ | ⟨rfl, h1, h2⟩ | rfl
    · exact ⟨fun h => absurd rfl h, fun _ => h2, fun _ => h3, fun _ => rfl, fun _ => rfl,
        fun _ => rfl⟩
    · exact ⟨fun _ => h1, fun h => absurd rfl h, fun _ => h3, fun _ => rfl, fun _ => rfl,
        fun _ => rfl⟩
    · exact ⟨fun _ => h1, fun _ => h2, fun h => absurd rfl h, fun _ => rfl, fun _ => rfl,
        fun _ => rfl⟩
    · exact Submodule.zero_mem _
  map_bracket := by
    intro u v
    ext <;> simp [threeStoreyLaw_bracket, cotangentLaw]

theorem cotangentInclusion_injective :
    Function.Injective (cotangentInclusion (d := d)).toLinearMap :=
  LinearMap.inl_injective

/-- Strict morphisms are filtered: they map the lower central series into the lower central
series. -/
theorem GradedLieHom.map_lowerCentral_le {V V' : Type*} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup V'] [Module ℝ V'] {G : GradedLieAlgebra V} {G' : GradedLieAlgebra V'}
    (q : GradedLieHom G G') (k : ℕ) :
    (G.lowerCentral k).map q.toLinearMap ≤ G'.lowerCentral k := by
  induction k with
  | zero => exact le_top
  | succ k ih =>
    rw [GradedLieAlgebra.lowerCentral, GradedLieAlgebra.lowerCentral, Submodule.map_span,
      Submodule.span_le]
    rintro _ ⟨_, ⟨u, v, hv, rfl⟩, rfl⟩
    exact Submodule.subset_span ⟨q.toLinearMap u, q.toLinearMap v,
      ih (Submodule.mem_map_of_mem hv), q.map_bracket u v⟩

/-- The cotangent double is nilpotent: `F³ = 0`. -/
theorem cotangentLaw_lowerCentral_two : (cotangentLaw d).lowerCentral 2 = ⊥ := by
  have hker : (cotangentLaw d).lowerCentral 1 ≤ LinearMap.ker (cotangentBracket d).flip := by
    rw [GradedLieAlgebra.lowerCentral, Submodule.span_le]
    rintro _ ⟨u, v, -, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker]
    exact LinearMap.ext fun A => cotangentBracket_bracket_eq_zero A u v
  rw [GradedLieAlgebra.lowerCentral, Submodule.span_eq_bot]
  rintro _ ⟨u, v, hv, rfl⟩
  exact LinearMap.congr_fun (LinearMap.mem_ker.mp (hker hv)) u

theorem cotangentLaw_isNilpotent : (cotangentLaw d).IsNilpotent :=
  ⟨2, cotangentLaw_lowerCentral_two⟩

theorem finrank_cotangentDouble : Module.finrank ℝ CotangentDouble = 6 := by
  simp [Module.finrank_prod]

/-- The coadjoint values: `[x, w*] = (−1)^d y*`, `[y, w*] = x*`, `[x, y] = w`. -/
theorem cotangentBracket_generators :
    cotangentBracket d (gx, 0) (0, gw) = (0, (0, shiftSign d, 0)) ∧
      cotangentBracket d (gy, 0) (0, gw) = (0, (1, 0, 0)) ∧
        cotangentBracket d (gx, 0) (gy, 0) = (gw, 0) := by
  refine ⟨?_, ?_, ?_⟩ <;> ext <;> simp [gx, gy, gw]

/-- The pairing signs `s_x = s_w = 1`, `s_y = (−1)^{d+1}`. -/
theorem cotangentPairing_generators :
    cotangentPairing d (gx, 0) (0, gx) = 1 ∧
      cotangentPairing d (gy, 0) (0, gy) = (-1 : ℝ) ^ (d + 1) ∧
        cotangentPairing d (gw, 0) (0, gw) = 1 := by
  refine ⟨by simp [gx], ?_, by simp [gw]⟩
  simp only [cotangentPairing_apply, gy, shiftSign, zpow_add_one₀ (by norm_num : (-1 : ℝ) ≠ 0)]
  simp

end

end GaloisForLFunctions.HTGeometry.NomologicalHomotopyGeometry
