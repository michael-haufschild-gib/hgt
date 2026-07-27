import GaloisForLFunctions.RHTower.DirichletLGammaRatio

/-!
# The left edge of the Phragmén–Lindelöf strip

On the line `Re w = -2` the functional equation expresses `L(w,χ)` through `L(1-w, χ⁻¹)`, which sits
on `Re s = 3` and is bounded there, times the ratio of the two Archimedean factors.  That ratio is
polynomial, so the L-function grows at most polynomially on the left edge.

The exponential factors of the two `Γ`'s cancel because both arguments have imaginary part of
modulus `|t|/2`; the remaining `π`-powers and the constant `N^{5/2} |ε(χ)|` are absorbed into the
constant.
-/

open Complex
open GaloisForLFunctions.HTGeometry

namespace RHTower

variable {N : ℕ} [NeZero N]

/-- **Left edge of the strip.**  For a nontrivial primitive character, `‖L(w,χ)‖` is `O(|t|³)` on
the line `Re w = -2`. -/
theorem exists_bound_LFunction_left_edge {χ : DirichletCharacter ℂ N}
    (hprim : χ.IsPrimitive) :
    ∃ A : ℝ, 0 < A ∧ ∀ t : ℝ, 2 ≤ |t| →
      ‖DirichletCharacter.LFunction χ ((-2 : ℂ) + (t : ℂ) * Complex.I)‖ ≤ A * |t| ^ 3 := by
  obtain ⟨d, hd, hgf⟩ := gammaFactor_eq_Gammaℝ χ
  obtain ⟨C, hC, hCbound⟩ := exists_bound_LFunction_of_two_le_re χ⁻¹
  obtain ⟨A₀, hA₀, hratio⟩ : ∃ A₀ : ℝ, 0 < A₀ ∧ ∀ t : ℝ, 2 ≤ |t| →
      ‖Complex.Gamma (((3 : ℂ) - (t : ℂ) * Complex.I + ((d : ℝ) : ℂ)) / 2)‖
        ≤ A₀ * |t / 2| ^ 3 *
          ‖Complex.Gamma ((((-2 : ℂ) + (t : ℂ) * Complex.I) + ((d : ℝ) : ℂ)) / 2)‖ := by
    rcases hd with rfl | rfl
    · exact ⟨40, by norm_num, fun t ht => norm_Gamma_ratio_even ht⟩
    · exact exists_norm_Gamma_ratio_odd
  have hNpos : (0 : ℕ) < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
  set Npow : ℝ := (N : ℝ) ^ ((5 : ℝ) / 2) with hNpow
  have hNpowpos : 0 < Npow := Real.rpow_pos_of_pos hNr _
  set eps : ℝ := ‖χ.rootNumber‖ + 1 with heps
  have hepspos : 0 < eps := by
    have := norm_nonneg χ.rootNumber
    rw [heps]; linarith
  set π₁ : ℝ := Real.pi ^ (-(3 + d) / 2) with hπ₁
  set π₂ : ℝ := Real.pi ^ (-(-2 + d) / 2) with hπ₂
  have hπ₁pos : 0 < π₁ := Real.rpow_pos_of_pos Real.pi_pos _
  have hπ₂pos : 0 < π₂ := Real.rpow_pos_of_pos Real.pi_pos _
  refine ⟨Npow * eps * C * π₁ * A₀ / (8 * π₂), by positivity, fun t ht => ?_⟩
  set w : ℂ := (-2 : ℂ) + (t : ℂ) * Complex.I with hw
  set s : ℂ := (3 : ℂ) - (t : ℂ) * Complex.I with hs
  have htne : t ≠ 0 := by intro h; rw [h] at ht; norm_num at ht
  have hwre : w.re = -2 := by rw [hw]; simp
  have hwim : w.im = t := by rw [hw]; simp
  have hsre : s.re = 3 := by rw [hs]; simp
  have hsim : s.im = -t := by rw [hs]; simp
  -- the two Archimedean factors
  have hnum_re : (s + ((d : ℝ) : ℂ)).re = 3 + d := by rw [Complex.add_re, hsre]; simp
  have hden_re : (w + ((d : ℝ) : ℂ)).re = -2 + d := by rw [Complex.add_re, hwre]; simp
  have hden_im : ((w + ((d : ℝ) : ℂ)) / 2).im = t / 2 := by
    simp [Complex.add_im, hwim]
  have hGden_ne : Complex.Gamma ((w + ((d : ℝ) : ℂ)) / 2) ≠ 0 := by
    refine Complex.Gamma_ne_zero fun m hcon => ?_
    have him := hden_im
    rw [hcon] at him
    simp at him
    exact htne (by linarith)
  have hGden_pos : 0 < ‖Complex.Gamma ((w + ((d : ℝ) : ℂ)) / 2)‖ := norm_pos_iff.mpr hGden_ne
  have hgfden_ne : DirichletCharacter.gammaFactor χ w ≠ 0 := by
    rw [hgf w]
    intro hcon
    rw [Complex.Gammaℝ_eq_zero_iff] at hcon
    obtain ⟨n, hn⟩ := hcon
    have him : (w + ((d : ℝ) : ℂ)).im = t := by rw [Complex.add_im, hwim]; simp
    rw [hn] at him
    simp at him
    exact htne him.symm
  have hgfnum_ne : DirichletCharacter.gammaFactor χ⁻¹ s ≠ 0 := by
    rw [gammaFactor_inv, hgf s]
    refine Complex.Gammaℝ_ne_zero_of_re_pos ?_
    rw [hnum_re]
    rcases hd with rfl | rfl <;> norm_num
  -- the functional equation, cleared of denominators
  have hws : (1 : ℂ) - s = w := by rw [hs, hw]; ring
  have hFE := hprim.completedLFunction_one_sub s
  rw [hws] at hFE
  have hwne : w ≠ 0 := by intro h; rw [h] at hwre; simp at hwre
  have hsne : s ≠ 0 := by intro h; rw [h] at hsre; simp at hsre
  have hLw := DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ w (Or.inl hwne)
  have hLs := DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ⁻¹ s (Or.inl hsne)
  have hΛw : DirichletCharacter.completedLFunction χ w
      = DirichletCharacter.LFunction χ w * DirichletCharacter.gammaFactor χ w := by
    rw [hLw, div_mul_cancel₀ _ hgfden_ne]
  have hΛs : DirichletCharacter.completedLFunction χ⁻¹ s
      = DirichletCharacter.LFunction χ⁻¹ s * DirichletCharacter.gammaFactor χ⁻¹ s := by
    rw [hLs, div_mul_cancel₀ _ hgfnum_ne]
  rw [hΛw, hΛs] at hFE
  -- pass to norms
  have hnorm := congrArg (fun z : ℂ => ‖z‖) hFE
  simp only [norm_mul] at hnorm
  have hNcpow : ‖(N : ℂ) ^ (s - 1 / 2)‖ = Npow := by
    rw [Complex.norm_natCast_cpow_of_pos hNpos, hNpow]
    congr 1
    rw [Complex.sub_re, hsre]
    norm_num
  have hgfden : ‖DirichletCharacter.gammaFactor χ w‖
      = π₂ * ‖Complex.Gamma ((w + ((d : ℝ) : ℂ)) / 2)‖ := by
    rw [hgf w, norm_Gammaℝ, hden_re, hπ₂]
  have hgfnum : ‖DirichletCharacter.gammaFactor χ⁻¹ s‖
      = π₁ * ‖Complex.Gamma ((s + ((d : ℝ) : ℂ)) / 2)‖ := by
    rw [gammaFactor_inv, hgf s, norm_Gammaℝ, hnum_re, hπ₁]
  rw [hNcpow, hgfden, hgfnum] at hnorm
  -- estimate the right-hand side
  have hLsb : ‖DirichletCharacter.LFunction χ⁻¹ s‖ ≤ C := hCbound s (by rw [hsre]; norm_num)
  have hrat : ‖Complex.Gamma ((s + ((d : ℝ) : ℂ)) / 2)‖
      ≤ A₀ * |t / 2| ^ 3 * ‖Complex.Gamma ((w + ((d : ℝ) : ℂ)) / 2)‖ := by
    have h := hratio t ht
    rw [← hs, ← hw] at h
    exact h
  have heps' : ‖χ.rootNumber‖ ≤ eps := by rw [heps]; linarith
  have hLnn : 0 ≤ ‖DirichletCharacter.LFunction χ w‖ := norm_nonneg _
  have hGnum_nn : 0 ≤ ‖Complex.Gamma ((s + ((d : ℝ) : ℂ)) / 2)‖ := norm_nonneg _
  have hLsnn : 0 ≤ ‖DirichletCharacter.LFunction χ⁻¹ s‖ := norm_nonneg _
  have habs : |t / 2| ^ 3 = |t| ^ 3 / 8 := by
    rw [abs_div, show |(2 : ℝ)| = 2 by norm_num, div_pow]
    norm_num
  -- combine
  have hkey : ‖DirichletCharacter.LFunction χ w‖ *
      (π₂ * ‖Complex.Gamma ((w + ((d : ℝ) : ℂ)) / 2)‖)
      ≤ (Npow * eps * C * π₁ * A₀ / 8) * |t| ^ 3 *
        ‖Complex.Gamma ((w + ((d : ℝ) : ℂ)) / 2)‖ := by
    rw [hnorm]
    have hstep : Npow * ‖χ.rootNumber‖ *
        (‖DirichletCharacter.LFunction χ⁻¹ s‖ *
          (π₁ * ‖Complex.Gamma ((s + ((d : ℝ) : ℂ)) / 2)‖))
        ≤ Npow * eps * (C * (π₁ *
            (A₀ * |t / 2| ^ 3 * ‖Complex.Gamma ((w + ((d : ℝ) : ℂ)) / 2)‖))) := by
      have h1 : Npow * ‖χ.rootNumber‖ ≤ Npow * eps :=
        mul_le_mul_of_nonneg_left heps' hNpowpos.le
      have h2 : ‖DirichletCharacter.LFunction χ⁻¹ s‖ *
          (π₁ * ‖Complex.Gamma ((s + ((d : ℝ) : ℂ)) / 2)‖)
          ≤ C * (π₁ * (A₀ * |t / 2| ^ 3 *
            ‖Complex.Gamma ((w + ((d : ℝ) : ℂ)) / 2)‖)) := by
        refine mul_le_mul hLsb (mul_le_mul_of_nonneg_left hrat hπ₁pos.le)
          (by positivity) hC.le
      refine mul_le_mul h1 h2 (by positivity) (by positivity)
    refine hstep.trans (le_of_eq ?_)
    rw [habs]
    ring
  have hfinal := le_of_mul_le_mul_right (by
    calc ‖DirichletCharacter.LFunction χ w‖ * π₂ *
        ‖Complex.Gamma ((w + ((d : ℝ) : ℂ)) / 2)‖
        = ‖DirichletCharacter.LFunction χ w‖ *
            (π₂ * ‖Complex.Gamma ((w + ((d : ℝ) : ℂ)) / 2)‖) := by ring
      _ ≤ (Npow * eps * C * π₁ * A₀ / 8) * |t| ^ 3 *
            ‖Complex.Gamma ((w + ((d : ℝ) : ℂ)) / 2)‖ := hkey) hGden_pos
  have hdiv : ‖DirichletCharacter.LFunction χ w‖
      ≤ Npow * eps * C * π₁ * A₀ / (8 * π₂) * |t| ^ 3 := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity : (0 : ℝ) < 8 * π₂)]
    linarith [hfinal]
  exact hdiv

end RHTower
