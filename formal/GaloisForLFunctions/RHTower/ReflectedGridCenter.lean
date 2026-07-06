/-
The canonical center geometry of reflected saddle/grid collisions.

For a divisor-antidiagonal collision `(n,m)`, the ratio center

  `n / (n+m)`

lies in the open critical strip, factor-swap reflection sends it to `1-center`,
and diagonal collisions land at the FE fixed point `1/2`.  This is the geometric
center assignment consumed by `ReflectedGridCompletedCharge`: once local orders of
`completedGN N` are finite at these centers, the completed reflected-grid charge is even.
-/
import GaloisForLFunctions.RHTower.ReflectedGridCompletedCharge

open Complex Real Filter Topology
open scoped BigOperators

namespace RHTower

/-- The real ratio center of a reflected grid collision `(n,m)`: `n/(n+m)`. -/
noncomputable def reflectedGridRatioCenterR (x : ℕ × ℕ) : ℝ :=
  (x.1 : ℝ) / ((x.1 + x.2 : ℕ) : ℝ)

/-- The ratio center as a point of the complex plane, on the real axis. -/
noncomputable def reflectedGridRatioCenter (x : ℕ × ℕ) : ℂ :=
  (reflectedGridRatioCenterR x : ℂ)

/-- The first factor of a reflected grid collision is positive. -/
theorem reflectedGridCollision_fst_pos {C : ℕ} {x : ℕ × ℕ}
    (hx : x ∈ reflectedGridCollisions C) : 0 < x.1 := by
  rw [reflectedGridCollision_mem_iff] at hx
  exact Nat.pos_of_ne_zero fun h => hx.2 (by rw [← hx.1, h, zero_mul])

/-- The second factor of a reflected grid collision is positive. -/
theorem reflectedGridCollision_snd_pos {C : ℕ} {x : ℕ × ℕ}
    (hx : x ∈ reflectedGridCollisions C) : 0 < x.2 := by
  rw [reflectedGridCollision_mem_iff] at hx
  exact Nat.pos_of_ne_zero fun h => hx.2 (by rw [← hx.1, h, mul_zero])

/-- Factor swap sends the real ratio center to `1-center`. -/
theorem reflectedGridRatioCenterR_swap {C : ℕ} {x : ℕ × ℕ}
    (hx : x ∈ reflectedGridCollisions C) :
    reflectedGridRatioCenterR (reflectedGridSwap x) = 1 - reflectedGridRatioCenterR x := by
  have hx1 : 0 < (x.1 : ℝ) := by exact_mod_cast reflectedGridCollision_fst_pos hx
  have hx2 : 0 < (x.2 : ℝ) := by exact_mod_cast reflectedGridCollision_snd_pos hx
  have hden : (x.1 : ℝ) + (x.2 : ℝ) ≠ 0 := by positivity
  rw [reflectedGridRatioCenterR, reflectedGridRatioCenterR, reflectedGridSwap]
  simp only [Nat.cast_add]
  rw [add_comm (x.2 : ℝ) (x.1 : ℝ)]
  field_simp [hden]
  ring

/-- Factor swap sends the complex ratio center to `1-center`. -/
theorem reflectedGridRatioCenter_swap {C : ℕ} {x : ℕ × ℕ}
    (hx : x ∈ reflectedGridCollisions C) :
    reflectedGridRatioCenter (reflectedGridSwap x) = 1 - reflectedGridRatioCenter x := by
  rw [reflectedGridRatioCenter, reflectedGridRatioCenter,
    reflectedGridRatioCenterR_swap hx]
  norm_num

/-- Every reflected grid ratio center lies in the open critical strip. -/
theorem reflectedGridRatioCenter_strip {C : ℕ} {x : ℕ × ℕ}
    (hx : x ∈ reflectedGridCollisions C) :
    0 < (reflectedGridRatioCenter x).re ∧ (reflectedGridRatioCenter x).re < 1 := by
  have hx1 : 0 < (x.1 : ℝ) := by exact_mod_cast reflectedGridCollision_fst_pos hx
  have hx2 : 0 < (x.2 : ℝ) := by exact_mod_cast reflectedGridCollision_snd_pos hx
  have hdenpos : 0 < (x.1 : ℝ) + (x.2 : ℝ) := by positivity
  rw [reflectedGridRatioCenter, reflectedGridRatioCenterR]
  simp only [Nat.cast_add, Complex.ofReal_re]
  constructor
  · exact div_pos hx1 hdenpos
  · rw [div_lt_iff₀ hdenpos]
    linarith

/-- Diagonal reflected grid collisions have real ratio center `1/2`. -/
theorem reflectedGridRatioCenterR_diag {C : ℕ} {x : ℕ × ℕ}
    (hx : x ∈ reflectedGridCollisions C) (hdiag : x.1 = x.2) :
    reflectedGridRatioCenterR x = 1 / 2 := by
  have hx1 : 0 < (x.1 : ℝ) := by exact_mod_cast reflectedGridCollision_fst_pos hx
  have hx2ne : (x.2 : ℝ) ≠ 0 := by
    rw [← hdiag]
    exact ne_of_gt hx1
  rw [reflectedGridRatioCenterR, hdiag]
  simp only [Nat.cast_add]
  field_simp [hx2ne]
  ring

/-- Diagonal reflected grid collisions land at the FE fixed point `1/2`. -/
theorem reflectedGridRatioCenter_diag {C : ℕ} {x : ℕ × ℕ}
    (hx : x ∈ reflectedGridCollisions C) (hdiag : x.1 = x.2) :
    reflectedGridRatioCenter x = (1 / 2 : ℂ) := by
  rw [reflectedGridRatioCenter, reflectedGridRatioCenterR_diag hx hdiag]
  norm_num

/-- On the real axis, the finite Dirichlet polynomial is the corresponding real
sum of positive powers. -/
theorem dirichletPoly_ofReal_eq (N : ℕ) (σ : ℝ) :
    dirichletPoly N (σ : ℂ) = ((∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-σ)) : ℝ) := by
  unfold dirichletPoly
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl ?_
  intro n _hn
  rw [show -((σ : ℝ) : ℂ) = ((-σ : ℝ) : ℂ) by norm_num]
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_cpow (Nat.cast_nonneg n)]

/-- For `N ≥ 1`, the real-axis Dirichlet polynomial has positive real part. -/
theorem dirichletPoly_ofReal_re_pos {N : ℕ} (hN : 1 ≤ N) (σ : ℝ) :
    0 < (dirichletPoly N (σ : ℂ)).re := by
  rw [dirichletPoly_ofReal_eq]
  simp only [Complex.ofReal_re]
  refine Finset.sum_pos (s := Finset.Icc 1 N) ?_ ?_
  · intro n hn
    exact Real.rpow_pos_of_pos (by
      have hnpos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hn).1
      exact_mod_cast hnpos) (-σ)
  · exact ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hN⟩⟩

/-- For `N ≥ 1`, the real-axis Dirichlet polynomial is nonzero. -/
theorem dirichletPoly_ofReal_ne_zero {N : ℕ} (hN : 1 ≤ N) (σ : ℝ) :
    dirichletPoly N (σ : ℂ) ≠ 0 := by
  intro h
  have hp := dirichletPoly_ofReal_re_pos (N := N) hN σ
  rw [h] at hp
  exact lt_irrefl _ hp

/-- Deligne's real gamma factor restricted to the real axis. -/
theorem GammaR_ofReal_eq (σ : ℝ) :
    Gammaℝ (σ : ℂ) = (((Real.pi : ℝ) ^ (-σ / 2) * Real.Gamma (σ / 2) : ℝ) : ℂ) := by
  rw [Gammaℝ_def]
  rw [show -((σ : ℂ)) / 2 = (((-σ / 2 : ℝ)) : ℂ) by norm_num]
  rw [← Complex.ofReal_cpow (le_of_lt Real.pi_pos)]
  rw [show (σ : ℂ) / 2 = ((σ / 2 : ℝ) : ℂ) by norm_num]
  rw [Complex.Gamma_ofReal]
  norm_num

/-- The concrete `χ` factor restricted to the real axis. -/
theorem zetaChi_ofReal_eq (σ : ℝ) :
    zetaChi (σ : ℂ) =
      ((((Real.pi : ℝ) ^ (-(1 - σ) / 2) * Real.Gamma ((1 - σ) / 2)) /
        ((Real.pi : ℝ) ^ (-σ / 2) * Real.Gamma (σ / 2)) : ℝ) : ℂ) := by
  unfold zetaChi
  rw [GammaR_ofReal_eq σ]
  have h1 : (1 : ℂ) - (σ : ℂ) = ((1 - σ : ℝ) : ℂ) := by norm_num
  rw [h1, GammaR_ofReal_eq (1 - σ)]
  norm_num

/-- On the real interval `0<σ<1`, `χ(σ)` has positive real part. -/
theorem zetaChi_ofReal_re_pos {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) :
    0 < (zetaChi (σ : ℂ)).re := by
  rw [zetaChi_ofReal_eq]
  simp only [Complex.ofReal_re]
  apply div_pos
  · apply mul_pos
    · exact Real.rpow_pos_of_pos Real.pi_pos (-(1 - σ) / 2)
    · exact Real.Gamma_pos_of_pos (by linarith)
  · apply mul_pos
    · exact Real.rpow_pos_of_pos Real.pi_pos (-σ / 2)
    · exact Real.Gamma_pos_of_pos (by linarith)

/-- For `N ≥ 1`, the concrete raw carrier has positive real part at every real
point of the open strip. -/
theorem gN_ofReal_re_pos {N : ℕ} (hN : 1 ≤ N) {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) :
    0 < (gN N (σ : ℂ)).re := by
  unfold gN chiSymmetrize
  rw [dirichletPoly_ofReal_eq N σ]
  have h1sub : (1 : ℂ) - (σ : ℂ) = ((1 - σ : ℝ) : ℂ) := by norm_num
  rw [h1sub, dirichletPoly_ofReal_eq N (1 - σ), zetaChi_ofReal_eq σ]
  rw [← Complex.ofReal_mul, ← Complex.ofReal_add, Complex.ofReal_re]
  apply add_pos
  · exact Finset.sum_pos (s := Finset.Icc 1 N)
      (fun n hn => Real.rpow_pos_of_pos (by
        have hnpos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hn).1
        exact_mod_cast hnpos) (-σ))
      ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hN⟩⟩
  · apply mul_pos
    · apply div_pos
      · apply mul_pos
        · exact Real.rpow_pos_of_pos Real.pi_pos (-(1 - σ) / 2)
        · exact Real.Gamma_pos_of_pos (by linarith)
      · apply mul_pos
        · exact Real.rpow_pos_of_pos Real.pi_pos (-σ / 2)
        · exact Real.Gamma_pos_of_pos (by linarith)
    · exact Finset.sum_pos (s := Finset.Icc 1 N)
        (fun n hn => Real.rpow_pos_of_pos (by
          have hnpos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hn).1
          exact_mod_cast hnpos) (-(1 - σ)))
        ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hN⟩⟩

/-- For `N ≥ 1`, the concrete raw carrier is nonzero at every real point of the
open strip. -/
theorem gN_ofReal_ne_zero {N : ℕ} (hN : 1 ≤ N) {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) :
    gN N (σ : ℂ) ≠ 0 := by
  intro h
  have hp := gN_ofReal_re_pos (N := N) hN h0 h1
  rw [h] at hp
  exact lt_irrefl _ hp

/-- For `N ≥ 1`, the completed carrier is nonzero at every real point of the
open strip. -/
theorem completedGN_ofReal_ne_zero {N : ℕ} (hN : 1 ≤ N) {σ : ℝ}
    (h0 : 0 < σ) (h1 : σ < 1) :
    completedGN N (σ : ℂ) ≠ 0 := by
  exact completedGN_ne_zero_of_gN_ne_zero (N := N) (z := (σ : ℂ)) (by simpa using h0)
    (by
      intro h
      have hre := congrArg Complex.re h
      simp at hre
      linarith)
    (gN_ofReal_ne_zero (N := N) hN h0 h1)

/-- For `N ≥ 1`, the completed carrier has finite local order at every real point
of the open strip. In fact the order is zero there. -/
theorem completedGN_orderAt_ofReal_ne_top {N : ℕ} (hN : 1 ≤ N) {σ : ℝ}
    (h0 : 0 < σ) (h1 : σ < 1) :
    analyticOrderAt (completedGN N) (σ : ℂ) ≠ ⊤ := by
  have hne := completedGN_ofReal_ne_zero (N := N) hN h0 h1
  have hzero : analyticOrderAt (completedGN N) (σ : ℂ) = 0 := by
    rw [analyticOrderAt_eq_zero]
    exact Or.inr hne
  rw [hzero]
  norm_num

/-- For `N ≥ 1`, the finite-order hypothesis for ratio centers is automatic. -/
theorem reflectedGridCompletedCharge_finite_of_ratio_center {C N : ℕ} (hN : 1 ≤ N) :
    ∀ x ∈ reflectedGridCollisions C,
      analyticOrderAt (completedGN N) (reflectedGridRatioCenter x) ≠ ⊤ := by
  intro x hx
  have hstrip := reflectedGridRatioCenter_strip hx
  have h0 : 0 < reflectedGridRatioCenterR x := by
    simpa [reflectedGridRatioCenter] using hstrip.1
  have h1 : reflectedGridRatioCenterR x < 1 := by
    simpa [reflectedGridRatioCenter] using hstrip.2
  simpa [reflectedGridRatioCenter] using
    completedGN_orderAt_ofReal_ne_top (N := N) hN h0 h1

/-- Completed-carrier charge parity for the canonical ratio center. Once the local orders
of `completedGN N` are finite at the ratio centers, the reflected completed charge is even. -/
theorem reflectedGridCompletedCharge_even_of_ratio_center {C N : ℕ}
    (hfinite : ∀ x ∈ reflectedGridCollisions C,
      analyticOrderAt (completedGN N) (reflectedGridRatioCenter x) ≠ ⊤) :
    Even (reflectedGridCompletedCharge C N reflectedGridRatioCenter) := by
  exact reflectedGridCompletedCharge_even_of_center_swap
    (fun x hx => reflectedGridRatioCenter_swap hx)
    (fun x hx => reflectedGridRatioCenter_strip hx)
    (fun x hx hdiag => reflectedGridRatioCenter_diag hx hdiag)
    hfinite

/-- Deck form for the canonical ratio center. -/
theorem reflectedGridCompletedCharge_deckRed_two_eq_one_of_ratio_center {C N : ℕ}
    (hfinite : ∀ x ∈ reflectedGridCollisions C,
      analyticOrderAt (completedGN N) (reflectedGridRatioCenter x) ≠ ⊤) :
    deckRed 2 (↑(reflectedGridCompletedCharge C N reflectedGridRatioCenter)) = 1 := by
  exact reflectedGridCompletedCharge_deckRed_two_eq_one_of_center_swap
    (fun x hx => reflectedGridRatioCenter_swap hx)
    (fun x hx => reflectedGridRatioCenter_strip hx)
    (fun x hx hdiag => reflectedGridRatioCenter_diag hx hdiag)
    hfinite

/-- Completed-carrier charge parity for the canonical ratio center, with the
finite-order side condition discharged by `N ≥ 1`. -/
theorem reflectedGridCompletedCharge_even_of_ratio_center_of_one_le {C N : ℕ} (hN : 1 ≤ N) :
    Even (reflectedGridCompletedCharge C N reflectedGridRatioCenter) := by
  exact reflectedGridCompletedCharge_even_of_ratio_center
    (reflectedGridCompletedCharge_finite_of_ratio_center (C := C) hN)

/-- Deck form for the canonical ratio center, with the finite-order side condition
discharged by `N ≥ 1`. -/
theorem reflectedGridCompletedCharge_deckRed_two_eq_one_of_ratio_center_of_one_le {C N : ℕ}
    (hN : 1 ≤ N) :
    deckRed 2 (↑(reflectedGridCompletedCharge C N reflectedGridRatioCenter)) = 1 := by
  exact reflectedGridCompletedCharge_deckRed_two_eq_one_of_ratio_center
    (reflectedGridCompletedCharge_finite_of_ratio_center (C := C) hN)

end RHTower
