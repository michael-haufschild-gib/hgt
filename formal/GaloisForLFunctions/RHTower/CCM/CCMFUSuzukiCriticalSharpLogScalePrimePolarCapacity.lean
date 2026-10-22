import GaloisForLFunctions.RHTower.CCM.CCMFUSuzukiCriticalLogScalePrimePolarCapacity

/-!
# Sharp forward log-scale polar capacity for the critical CCM--FU source

The previous local construction spent `ceil (2 log p)` polar cells to pay one
prime atom.  This module removes that factor two: the literal forward polar
span through `ceil (log p)` cells already pays the atom.  Together with the
existing sharp forward memory lower law, this closes the local scale gap.  The
remaining problem is exclusively the simultaneous signed allocation of
overlapping prime windows.
-/

open Filter Topology Set

namespace RHTower

noncomputable section

private theorem log_sq_le_natCast (p : ℕ) (hp : 1 ≤ p) :
    Real.log (p : ℝ) ^ (2 : ℕ) ≤ (p : ℝ) := by
  let x : ℝ := p
  let s : ℝ := Real.sqrt x
  let r : ℝ := Real.sqrt s
  have hx0 : 0 < x := by
    dsimp only [x]
    exact_mod_cast (Nat.zero_lt_of_lt (lt_of_lt_of_le (by omega : 0 < 1) hp))
  have hx1 : 1 ≤ x := by
    dsimp only [x]
    exact_mod_cast hp
  have hs0 : 0 < s := by
    dsimp only [s]
    exact Real.sqrt_pos.mpr hx0
  have hr0 : 0 < r := by
    dsimp only [r]
    exact Real.sqrt_pos.mpr hs0
  have hlogs : Real.log s = Real.log x / 2 := by
    dsimp only [s]
    rw [Real.log_sqrt hx0.le]
  have hlogr : Real.log r = Real.log s / 2 := by
    dsimp only [r]
    rw [Real.log_sqrt hs0.le]
  have hlogrepr : Real.log x = 4 * Real.log r := by
    rw [hlogr, hlogs]
    ring
  have hlogrle : Real.log r ≤ r - 1 := Real.log_le_sub_one_of_pos hr0
  have hquad : 4 * (r - 1) ≤ r ^ (2 : ℕ) := by
    nlinarith [sq_nonneg (r - 2)]
  have hsqrs : r ^ (2 : ℕ) = s := by
    dsimp only [r]
    exact Real.sq_sqrt hs0.le
  have hlogle : Real.log x ≤ s := by
    calc
      Real.log x = 4 * Real.log r := hlogrepr
      _ ≤ 4 * (r - 1) := by gcongr
      _ ≤ r ^ (2 : ℕ) := hquad
      _ = s := hsqrs
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hsq : Real.log x ^ (2 : ℕ) ≤ s ^ (2 : ℕ) :=
    (sq_le_sq₀ hlog0 hs0.le).2 hlogle
  have hsqs : s ^ (2 : ℕ) = x := by
    dsimp only [s]
    exact Real.sq_sqrt hx0.le
  simpa only [x] using hsq.trans_eq hsqs

/-- One literal prime atom is paid by any forward polar span of at least `log p` cells.
No positivity is imposed on other prime--polar cells in that span. -/
theorem ccmFUCritical_primePolar_capacity_of_oneLogScale
    {p L : ℕ} (hp : 1 < p)
    (hscale : Real.log (p : ℝ) ≤ (L : ℝ)) :
    Real.log (p : ℝ) / (p : ℝ) ≤
      Real.log ((p + L : ℕ) : ℝ) - Real.log ((p - 1 : ℕ) : ℝ) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Nat.zero_lt_of_lt hp)
  have hp1 : 1 ≤ p := by omega
  have hpL0 : (0 : ℝ) < ((p + L : ℕ) : ℝ) := by positivity
  have hlog0 : 0 ≤ Real.log (p : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hp1)
  have hlogle : Real.log (p : ℝ) ≤ (p : ℝ) := by
    have h := Real.log_le_sub_one_of_pos hp0
    linarith
  have hlogSq : Real.log (p : ℝ) ^ (2 : ℕ) ≤ (p : ℝ) := log_sq_le_natCast p hp1
  have hprod : 0 ≤ ((p : ℝ) - Real.log (p : ℝ)) *
      ((L : ℝ) - Real.log (p : ℝ)) :=
    mul_nonneg (sub_nonneg.mpr hlogle) (sub_nonneg.mpr hscale)
  have hgap : 0 ≤ (p : ℝ) - Real.log (p : ℝ) ^ (2 : ℕ) := sub_nonneg.mpr hlogSq
  have hkey : Real.log (p : ℝ) * ((p + L : ℕ) : ℝ) ≤
      (p : ℝ) * ((L : ℝ) + 1) := by
    push_cast
    nlinarith [hprod, hgap]
  have hfrac : Real.log (p : ℝ) / (p : ℝ) ≤
      ((L : ℝ) + 1) / ((p + L : ℕ) : ℝ) := by
    rw [div_le_div_iff₀ hp0 hpL0]
    simpa [mul_comm] using hkey
  exact hfrac.trans (ccmFUCritical_polarLogSpan_lower hp)

/-- Any literal forward polar span which pays one marked prime atom has the corresponding
harmonic memory cost.  This is a capacity statement, independent of any sign assumption on the
full source block. -/
theorem ccmFUCritical_primePolar_capacity_forces_harmonic_radius
    {p L : ℕ} (hp : 1 < p)
    (hcapacity : Real.log (p : ℝ) / (p : ℝ) ≤
      Real.log ((p + L : ℕ) : ℝ) - Real.log ((p - 1 : ℕ) : ℝ)) :
    ((p - 1 : ℕ) : ℝ) * (Real.log (p : ℝ) / (p : ℝ)) ≤ (L + 1 : ℕ) := by
  have hpL : (0 : ℝ) < ((p + L : ℕ) : ℝ) := by positivity
  have hpm1 : (0 : ℝ) < ((p - 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < p - 1 by omega)
  have hsub : (p : ℝ) - 1 ≠ 0 := by
    have hsubpos : 0 < (p : ℝ) - 1 := by
      convert hpm1 using 1
      rw [Nat.cast_sub (by omega : 1 ≤ p)]
      norm_num
    exact hsubpos.ne'
  have hratio : 0 < ((p + L : ℕ) : ℝ) / ((p - 1 : ℕ) : ℝ) :=
    div_pos hpL hpm1
  have hspan :
      Real.log ((p + L : ℕ) : ℝ) - Real.log ((p - 1 : ℕ) : ℝ) ≤
        ((L + 1 : ℕ) : ℝ) / ((p - 1 : ℕ) : ℝ) := by
    rw [← Real.log_div hpL.ne' hpm1.ne']
    calc
      Real.log (((p + L : ℕ) : ℝ) / ((p - 1 : ℕ) : ℝ)) ≤
          ((p + L : ℕ) : ℝ) / ((p - 1 : ℕ) : ℝ) - 1 :=
        Real.log_le_sub_one_of_pos hratio
      _ = ((L + 1 : ℕ) : ℝ) / ((p - 1 : ℕ) : ℝ) := by
        rw [Nat.cast_sub (by omega : 1 ≤ p)]
        push_cast
        field_simp [hsub]
        ring
  have hmain : Real.log (p : ℝ) / (p : ℝ) ≤
      ((L + 1 : ℕ) : ℝ) / ((p - 1 : ℕ) : ℝ) := hcapacity.trans hspan
  calc
    ((p - 1 : ℕ) : ℝ) * (Real.log (p : ℝ) / (p : ℝ)) ≤
        ((p - 1 : ℕ) : ℝ) * (((L + 1 : ℕ) : ℝ) / ((p - 1 : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left hmain hpm1.le
    _ = (L + 1 : ℕ) := by field_simp [hpm1.ne']

/-- Minimal source-scale integer radius supplied by the sharp local capacity law. -/
def ccmFUCriticalPrimeSharpLogTransportRadius (p : ℕ) : ℕ :=
  Nat.ceil (Real.log (p : ℝ))

theorem ccmFUCriticalPrimeSharpLogTransportRadius_lower (p : ℕ) :
    Real.log (p : ℝ) ≤ (ccmFUCriticalPrimeSharpLogTransportRadius p : ℝ) := by
  exact Nat.le_ceil _

/-- The literal polar span at `ceil (log p)` pays a marked prime atom. -/
theorem ccmFUCritical_primePolar_capacity_at_sharpLogTransportRadius
    {p : ℕ} (hp : 1 < p) :
    Real.log (p : ℝ) / (p : ℝ) ≤
      Real.log ((p + ccmFUCriticalPrimeSharpLogTransportRadius p : ℕ) : ℝ) -
        Real.log ((p - 1 : ℕ) : ℝ) := by
  apply ccmFUCritical_primePolar_capacity_of_oneLogScale hp
  exact ccmFUCriticalPrimeSharpLogTransportRadius_lower p

end

end RHTower
