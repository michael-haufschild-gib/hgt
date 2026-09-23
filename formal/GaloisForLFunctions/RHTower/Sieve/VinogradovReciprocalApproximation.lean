import Mathlib.NumberTheory.DiophantineApproximation.Basic

namespace RHTower.Sieve

noncomputable section

/-- Source-shaped Dirichlet approximation at the reciprocal scale.  Every
positive real `ξ` has a reduced approximation `a/q` with quadratic error
and denominator trapped, up to endpoint rounding, around `1/ξ`. -/
theorem exists_reciprocal_rational_approximation
    {ξ : ℝ} (hξ : 0 < ξ) :
    ∃ a q : ℕ,
      0 < q ∧ Nat.Coprime a q ∧
      |ξ - (a : ℝ) / (q : ℝ)| ≤ 1 / (q : ℝ) ^ (2 : ℕ) ∧
      1 / ξ - 1 / 2 ≤ (q : ℝ) ∧
      (q : ℝ) < 2 / ξ + 1 := by
  let H : ℕ := ⌈2 / ξ⌉₊
  have hscale : 0 < 2 / ξ := by positivity
  have hH : 0 < H := (Nat.ceil_pos.mpr hscale)
  obtain ⟨r, hr, hrH⟩ :=
    Real.exists_rat_abs_sub_le_and_den_le ξ hH
  let q : ℕ := r.den
  let a : ℕ := r.num.natAbs
  have hq : 0 < q := by exact r.den_pos
  have hHreal : 2 / ξ ≤ (H : ℝ) := Nat.le_ceil _
  have hsmall : 1 / ((H : ℝ) + 1) ≤ ξ / 2 := by
    have hden : 0 < (H : ℝ) + 1 := by positivity
    rw [div_eq_mul_inv, div_eq_mul_inv]
    have hinv : (((H : ℝ) + 1) : ℝ)⁻¹ ≤ (2 / ξ)⁻¹ := by
      apply inv_anti₀ hscale
      linarith
    have hrewrite : (2 / ξ)⁻¹ = ξ * (2 : ℝ)⁻¹ := by
      field_simp
    rw [hrewrite] at hinv
    simpa [mul_comm] using hinv
  have hrsmall : |ξ - (r : ℝ)| ≤ ξ / 2 := by
    calc
      _ ≤ 1 / (((H : ℝ) + 1) * (r.den : ℝ)) := hr
      _ ≤ 1 / ((H : ℝ) + 1) := by
        have hden : (1 : ℝ) ≤ r.den := by exact_mod_cast r.den_pos
        have hHpos : 0 < (H : ℝ) + 1 := by positivity
        have hmul : (H : ℝ) + 1 ≤ ((H : ℝ) + 1) * (r.den : ℝ) := by
          nlinarith
        simpa [one_div] using inv_anti₀ hHpos hmul
      _ ≤ ξ / 2 := hsmall
  have hrpos : 0 < (r : ℝ) := by
    have habs := (abs_le.mp hrsmall).2
    linarith
  have hnumpos : 0 < r.num := by
    rw [Rat.cast_def] at hrpos
    have hdenR : 0 < (r.den : ℝ) := by positivity
    rcases div_pos_iff.mp hrpos with hpos | hneg
    · exact_mod_cast hpos.1
    · exact False.elim (not_lt_of_ge hdenR.le hneg.2)
  have hnumcast : ((a : ℕ) : ℤ) = r.num := by
    exact Int.natAbs_of_nonneg hnumpos.le
  have hrat : (r : ℝ) = (a : ℝ) / (q : ℝ) := by
    rw [Rat.cast_def]
    change (r.num : ℝ) / (r.den : ℝ) = (a : ℝ) / (q : ℝ)
    rw [show (r.num : ℝ) = (a : ℝ) by exact_mod_cast hnumcast.symm]
  have hcop : Nat.Coprime a q := by
    exact r.reduced
  have hqH : q ≤ H := hrH
  have hquadratic :
      |ξ - (a : ℝ) / (q : ℝ)| ≤ 1 / (q : ℝ) ^ (2 : ℕ) := by
    rw [← hrat]
    calc
      _ ≤ 1 / (((H : ℝ) + 1) * (q : ℝ)) := hr
      _ ≤ 1 / (q : ℝ) ^ (2 : ℕ) := by
        have hqR : 0 < (q : ℝ) := by positivity
        have hle : (q : ℝ) ^ (2 : ℕ) ≤ ((H : ℝ) + 1) * (q : ℝ) := by
          have : (q : ℝ) ≤ (H : ℝ) + 1 := by exact_mod_cast (show q ≤ H + 1 by omega)
          nlinarith
        exact one_div_le_one_div_of_le (sq_pos_of_pos hqR) hle
  have hcross : |(q : ℝ) * ξ - (a : ℝ)| ≤ 1 / ((H : ℝ) + 1) := by
    have hqR : 0 < (q : ℝ) := by positivity
    have heq : (q : ℝ) * |ξ - (r : ℝ)| =
        |(q : ℝ) * ξ - (a : ℝ)| := by
      rw [hrat]
      have habsQ : |(q : ℝ)| = q := abs_of_pos hqR
      calc
        (q : ℝ) * |ξ - (a : ℝ) / (q : ℝ)| =
            |(q : ℝ)| * |ξ - (a : ℝ) / (q : ℝ)| := by rw [habsQ]
        _ = |(q : ℝ) * (ξ - (a : ℝ) / (q : ℝ))| := (abs_mul _ _).symm
        _ = |(q : ℝ) * ξ - (a : ℝ)| := by
          congr 1
          field_simp
    calc
      _ = (q : ℝ) * |ξ - (r : ℝ)| := heq.symm
      _ ≤ (q : ℝ) * (1 / (((H : ℝ) + 1) * (q : ℝ))) := by
        gcongr
      _ = 1 / ((H : ℝ) + 1) := by field_simp
  have ha : 1 ≤ a := by
    have haR : 0 < (a : ℝ) := by
      have haInt : (0 : ℤ) < (a : ℤ) := by simpa [hnumcast] using hnumpos
      exact_mod_cast haInt
    exact_mod_cast haR
  have haUpper : (a : ℝ) ≤ ((q : ℝ) + 1 / 2) * ξ := by
    have hlower := (abs_le.mp hcross).1
    have hsmall' := hsmall
    nlinarith
  have hlowerQ : 1 / ξ - 1 / 2 ≤ (q : ℝ) := by
    have haOne : (1 : ℝ) ≤ a := by exact_mod_cast ha
    have hone : 1 / ξ ≤ (q : ℝ) + 1 / 2 := by
      rw [div_le_iff₀ hξ]
      exact haOne.trans haUpper
    linarith
  have hupperQ : (q : ℝ) < 2 / ξ + 1 := by
    have hqHR : (q : ℝ) ≤ H := by exact_mod_cast hqH
    exact hqHR.trans_lt (Nat.ceil_lt_add_one hscale.le)
  exact ⟨a, q, hq, hcop, hquadratic, hlowerQ, hupperQ⟩

end

end RHTower.Sieve
