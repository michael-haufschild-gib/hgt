import GaloisForLFunctions.HTGeometry.ToeplitzTotalPositivityQuadratic

/-!
# Two-term sequences, scalar multiples, and the quadratic cone law

* `PFSeq.twoTerm`: the sequence `(c₀, c₁, 0, 0, …)` with `c₀, c₁ ≥ 0` is `PF_k` for every `k`.
  Expand a Toeplitz minor along its first row or column; the offset `d = j₀ − i₀` decides.  For
  `d < 0` the first column vanishes, and for `d > 1` the first row vanishes.  For `d = 0` the first
  column is `c₀ e₀`, and for `d = 1` the first row is `c₁ e₀`.  Every minor is therefore `0` or a
  monomial `c₀^p c₁^q`.
* `PFSeq.const_mul`: nonnegative multiples of `PF_k` sequences are `PF_k`.
* `PFSeq.quadratic_of_cone`: for `A, C ≥ 0` with `A + C > 0`, the quadratic
  `(A + C)² + 2(A − C) y + y²` has a `PF_k` coefficient sequence as soon as
  `cos (π/(k+1)) (A + C) ≤ A − C`.  It is `(A + C)² rⁿ (1, 2cos ψ, 1)` with `r = 1/(A + C)` and
  `cos ψ = (A − C)/(A + C)`, and the condition says `(k + 1) ψ ≤ π` (`PFSeq.cosQuadratic_geom`).
  For roots `y = −w²`, `−w̄²` with `w = √A + i√C`, this is the cone `√C ≤ tan (π/(2k+2)) √A`.
-/

open Finset Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The two-term sequence `(c₀, c₁, 0, 0, …)`. -/
def twoTermSeq (c0 c1 : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then c0 else if n = 1 then c1 else 0

theorem zext_twoTermSeq (c0 c1 : ℝ) (z : ℤ) :
    zext (twoTermSeq c0 c1) z = if z = 0 then c0 else if z = 1 then c1 else 0 := by
  rcases lt_or_ge z 0 with hz | hz
  · rw [zext_of_neg _ hz, if_neg (by omega), if_neg (by omega)]
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hz
    rw [zext_natCast]
    simp [twoTermSeq]

/-- Every Toeplitz minor of a nonnegative two-term sequence with increasing indices is
nonnegative. -/
theorem seqMinor_twoTermSeq_nonneg {c0 c1 : ℝ} (h0 : 0 ≤ c0) (h1 : 0 ≤ c1) :
    ∀ (m : ℕ) (i j : ℕ → ℕ), StrictMono i → StrictMono j →
      0 ≤ seqMinor (twoTermSeq c0 c1) m i j := by
  intro m
  induction m with
  | zero =>
    intro i j _ _
    rw [seqMinor_zero]
    exact zero_le_one
  | succ m ih =>
    intro i j hi hj
    have htail := ih (fun l => i (l + 1)) (fun l => j (l + 1)) (fun a b h => hi (by omega))
      (fun a b h => hj (by omega))
    have hcol : ∀ r : ℕ, 1 ≤ r → r ≤ m → (j 0 : ℤ) ≤ i 0 →
        zext (twoTermSeq c0 c1) ((j 0 : ℤ) - i r) = 0 := by
      intro r hr _ hji
      have : i 0 < i r := hi (by omega)
      exact zext_of_neg _ (by omega)
    have hrow : ∀ c : ℕ, 1 ≤ c → c ≤ m → (i 0 : ℤ) + 1 ≤ j 0 →
        zext (twoTermSeq c0 c1) ((j c : ℤ) - i 0) = 0 := by
      intro c hc _ hij
      have : j 0 < j c := hj (by omega)
      rw [zext_twoTermSeq, if_neg (by omega), if_neg (by omega)]
    rcases lt_or_ge (j 0 : ℤ) (i 0 + 1) with hlt | hge
    · rw [seqMinor_succ_of_col _ m i j fun r hr hrm => hcol r hr hrm (by omega)]
      rw [zext_twoTermSeq]
      split_ifs <;> first | exact mul_nonneg h0 htail | exact mul_nonneg h1 htail |
        simp
    · rw [seqMinor_succ_of_row _ m i j fun c hc hcm => hrow c hc hcm hge]
      rw [zext_twoTermSeq]
      split_ifs <;> first | exact mul_nonneg h0 htail | exact mul_nonneg h1 htail |
        simp

namespace PFSeq

/-- **Nonnegative two-term sequences are `PF_k` for every `k`.** -/
theorem twoTerm {c0 c1 : ℝ} (h0 : 0 ≤ c0) (h1 : 0 ≤ c1) (k : ℕ) :
    PFSeq k (twoTermSeq c0 c1) := by
  intro m _ i j hi hj
  rw [toeplitzMinor_eq_seqMinor]
  exact seqMinor_twoTermSeq_nonneg h0 h1 m _ _ (strictMono_finExtend hi) (strictMono_finExtend hj)

/-- Nonnegative multiples of `PF_k` sequences are `PF_k`. -/
theorem const_mul {k : ℕ} {a : ℕ → ℝ} (ha : PFSeq k a) {c : ℝ} (hc : 0 ≤ c) :
    PFSeq k (fun n => c * a n) := by
  intro m hm i j hi hj
  have hz : ∀ z : ℤ, zext (fun n => c * a n) z = c * zext a z := by
    intro z
    unfold zext
    split_ifs
    · rfl
    · rw [mul_zero]
  have hM : toeplitzMinor (fun n => c * a n) m i j = c ^ m * toeplitzMinor a m i j := by
    unfold toeplitzMinor
    simp_rw [hz]
    rw [show (Matrix.of fun r c' : Fin m => c * zext a ((j c' : ℤ) - i r)) =
        c • Matrix.of fun r c' : Fin m => zext a ((j c' : ℤ) - i r) by
      ext r c'
      simp, Matrix.det_smul, Fintype.card_fin]
  rw [hM]
  exact mul_nonneg (pow_nonneg hc m) (ha m hm i j hi hj)

/-- **The quadratic cone law.**  For `A, C ≥ 0`, `A + C > 0` and
`cos (π/(k+1)) (A + C) ≤ A − C`, the coefficients `((A + C)², 2(A − C), 1)` form a `PF_k`
sequence. -/
theorem quadratic_of_cone {k : ℕ} {A C : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C) (hAC : 0 < A + C)
    (hcone : Real.cos (Real.pi / ((k : ℝ) + 1)) * (A + C) ≤ A - C) :
    PFSeq k (fun n => if n = 0 then (A + C) ^ 2 else if n = 1 then 2 * (A - C)
      else if n = 2 then 1 else 0) := by
  set x : ℝ := (A - C) / (A + C) with hx
  have hx1 : x ≤ 1 := by
    rw [hx, div_le_one hAC]
    linarith
  have hx0 : -1 ≤ x := by
    rw [hx, le_div_iff₀ hAC]
    linarith
  set ψ : ℝ := Real.arccos x with hψ
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hθ0 : 0 ≤ Real.pi / ((k : ℝ) + 1) := div_nonneg Real.pi_pos.le hk1.le
  have hθπ : Real.pi / ((k : ℝ) + 1) ≤ Real.pi :=
    div_le_self Real.pi_pos.le (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])
  have hcosx : Real.cos (Real.pi / ((k : ℝ) + 1)) ≤ x := by
    rw [hx, le_div_iff₀ hAC]
    exact hcone
  have hψle : ψ ≤ Real.pi / ((k : ℝ) + 1) := by
    calc ψ ≤ Real.arccos (Real.cos (Real.pi / ((k : ℝ) + 1))) := Real.arccos_le_arccos hcosx
      _ = Real.pi / ((k : ℝ) + 1) := Real.arccos_cos hθ0 hθπ
  have hkψ : ((k : ℝ) + 1) * ψ ≤ Real.pi := by
    calc ((k : ℝ) + 1) * ψ ≤ ((k : ℝ) + 1) * (Real.pi / ((k : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left hψle hk1.le
      _ = Real.pi := by field_simp
  have hcosψ : Real.cos ψ = x := Real.cos_arccos hx0 hx1
  have hr : 0 < 1 / (A + C) := by positivity
  have h := const_mul (PFSeq.cosQuadratic_geom (Real.arccos_nonneg x) hkψ hr)
    (sq_nonneg (A + C))
  convert h using 1
  funext n
  rw [hcosψ, hx]
  have hne : A + C ≠ 0 := hAC.ne'
  rcases n with _ | _ | _ | n
  · simp
  · norm_num
    field_simp
  · norm_num
    field_simp
  · have h3 : n + 3 ≠ 2 := by omega
    simp [h3]

end PFSeq

end

end GaloisForLFunctions.HTGeometry
