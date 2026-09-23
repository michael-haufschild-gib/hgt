import GaloisForLFunctions.HTGeometry.RealTreeBPFirstCrossing
import GaloisForLFunctions.HTGeometry.SpecialMapFixedPointMultiplier

/-!
# The complex belief-propagation map and its interior multiplier

The homogeneous belief-propagation map of a binary channel is a rational map of the complex plane;
on the real interval it is the map of the first-crossing theorem.  Its interior fixed point
therefore supplies a complex fixed point whose multiplier is nonzero of modulus at most one, which
is exactly the datum excluding every family on the Ritt list.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex

noncomputable section

/-- The belief-propagation map as a rational map of the complex plane. -/
def treeBPC (p : ℕ) (u v z : ℂ) : ℂ :=
  ((1 + u * z) ^ p - (1 + v * z) ^ p) / ((1 + u * z) ^ p + (1 + v * z) ^ p)

theorem treeBPC_ofReal (p : ℕ) (u v y : ℝ) :
    treeBPC p (u : ℂ) (v : ℂ) (y : ℂ) = ((treeBP p u v y : ℝ) : ℂ) := by
  rw [treeBPC, treeBP]
  push_cast
  ring

/-- The exact derivative of the complex belief-propagation map. -/
theorem hasDerivAt_treeBPC {p : ℕ} (hp : 0 < p) {u v z : ℂ}
    (hden : (1 + u * z) ^ p + (1 + v * z) ^ p ≠ 0) :
    HasDerivAt (treeBPC p u v)
      (2 * (p : ℂ) * (u - v) * (1 + u * z) ^ (p - 1) * (1 + v * z) ^ (p - 1) /
        ((1 + u * z) ^ p + (1 + v * z) ^ p) ^ (2 : ℕ)) z := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  have hAaff : HasDerivAt (fun t : ℂ => 1 + u * t) u z := by
    simpa using ((hasDerivAt_id z).const_mul u).const_add (1 : ℂ)
  have hBaff : HasDerivAt (fun t : ℂ => 1 + v * t) v z := by
    simpa using ((hasDerivAt_id z).const_mul v).const_add (1 : ℂ)
  have hAp : HasDerivAt (fun t : ℂ => (1 + u * t) ^ (q + 1))
      (((q : ℂ) + 1) * (1 + u * z) ^ q * u) z := by
    have h := (hasDerivAt_pow (q + 1) (1 + u * z)).comp z hAaff
    simpa [Function.comp_def] using h
  have hBp : HasDerivAt (fun t : ℂ => (1 + v * t) ^ (q + 1))
      (((q : ℂ) + 1) * (1 + v * z) ^ q * v) z := by
    have h := (hasDerivAt_pow (q + 1) (1 + v * z)).comp z hBaff
    simpa [Function.comp_def] using h
  have hquot := (hAp.sub hBp).div (hAp.add hBp) hden
  refine hquot.congr_deriv ?_
  simp only [Pi.add_apply, Pi.sub_apply, Nat.add_sub_cancel]
  congr 1
  push_cast
  ring

/-- **The interior fixed point of the complex map.**  In the expansive regime the belief-propagation
map has a complex fixed point whose multiplier is nonzero of modulus at most one. -/
theorem exists_treeBPC_nonsuper_nonrepelling_fixedPoint {p : ℕ} (hp : 2 ≤ p) {u v : ℝ}
    (hv : -1 < v) (huv : v < u) (hu : u < 1)
    (hlam : 1 < (p : ℝ) * (u - v) / 2) :
    ∃ (c : ℂ) (dR : ℂ), treeBPC p (u : ℂ) (v : ℂ) c = c ∧
      HasDerivAt (treeBPC p (u : ℂ) (v : ℂ)) dR c ∧ dR ≠ 0 ∧ ‖dR‖ ≤ 1 := by
  obtain ⟨c, hc0, hc1, hfix, hpos, hle⟩ := exists_treeBP_interior_fixedPoint hp hv huv hu hlam
  obtain ⟨hu', hv'⟩ := abs_lt_one_of_between hv huv hu
  have hcabs : |c| ≤ 1 := by
    rw [abs_le]
    exact ⟨by linarith, hc1.le⟩
  have hAr : (0 : ℝ) < 1 + u * c := branch_pos hu' hcabs
  have hBr : (0 : ℝ) < 1 + v * c := branch_pos hv' hcabs
  have hp0 : 0 < p := by omega
  have hA : ((1 : ℂ) + (u : ℂ) * (c : ℂ)) ≠ 0 := by
    have : ((1 : ℂ) + (u : ℂ) * (c : ℂ)) = ((1 + u * c : ℝ) : ℂ) := by push_cast; ring
    rw [this]
    exact_mod_cast ne_of_gt hAr
  have hB : ((1 : ℂ) + (v : ℂ) * (c : ℂ)) ≠ 0 := by
    have : ((1 : ℂ) + (v : ℂ) * (c : ℂ)) = ((1 + v * c : ℝ) : ℂ) := by push_cast; ring
    rw [this]
    exact_mod_cast ne_of_gt hBr
  have hdenr : (0 : ℝ) < (1 + u * c) ^ p + (1 + v * c) ^ p := by
    have := pow_pos hAr p
    have := pow_pos hBr p
    linarith
  have hden : ((1 : ℂ) + (u : ℂ) * (c : ℂ)) ^ p + ((1 : ℂ) + (v : ℂ) * (c : ℂ)) ^ p ≠ 0 := by
    have hcast : ((1 : ℂ) + (u : ℂ) * (c : ℂ)) ^ p + ((1 : ℂ) + (v : ℂ) * (c : ℂ)) ^ p =
        (((1 + u * c) ^ p + (1 + v * c) ^ p : ℝ) : ℂ) := by push_cast; ring
    rw [hcast]
    exact_mod_cast ne_of_gt hdenr
  refine ⟨(c : ℂ), _, ?_, hasDerivAt_treeBPC hp0 hden, ?_, ?_⟩
  · rw [treeBPC_ofReal, hfix]
  · have hposr := treeBP_deriv_pos hp0 huv hAr hBr
    have hcast : (2 * (p : ℂ) * ((u : ℂ) - (v : ℂ)) * ((1 : ℂ) + (u : ℂ) * (c : ℂ)) ^ (p - 1) *
        ((1 : ℂ) + (v : ℂ) * (c : ℂ)) ^ (p - 1) /
        (((1 : ℂ) + (u : ℂ) * (c : ℂ)) ^ p + ((1 : ℂ) + (v : ℂ) * (c : ℂ)) ^ p) ^ (2 : ℕ)) =
        ((2 * (p : ℝ) * (u - v) * (1 + u * c) ^ (p - 1) * (1 + v * c) ^ (p - 1) /
          ((1 + u * c) ^ p + (1 + v * c) ^ p) ^ (2 : ℕ) : ℝ) : ℂ) := by push_cast; ring
    rw [hcast]
    exact_mod_cast ne_of_gt hposr
  · have hderivEq : deriv (treeBP p u v) c =
        2 * (p : ℝ) * (u - v) * (1 + u * c) ^ (p - 1) * (1 + v * c) ^ (p - 1) /
          ((1 + u * c) ^ p + (1 + v * c) ^ p) ^ (2 : ℕ) :=
      (hasDerivAt_treeBP hp0 hAr hBr).deriv
    have hcast : (2 * (p : ℂ) * ((u : ℂ) - (v : ℂ)) * ((1 : ℂ) + (u : ℂ) * (c : ℂ)) ^ (p - 1) *
        ((1 : ℂ) + (v : ℂ) * (c : ℂ)) ^ (p - 1) /
        (((1 : ℂ) + (u : ℂ) * (c : ℂ)) ^ p + ((1 : ℂ) + (v : ℂ) * (c : ℂ)) ^ p) ^ (2 : ℕ)) =
        ((2 * (p : ℝ) * (u - v) * (1 + u * c) ^ (p - 1) * (1 + v * c) ^ (p - 1) /
          ((1 + u * c) ^ p + (1 + v * c) ^ p) ^ (2 : ℕ) : ℝ) : ℂ) := by push_cast; ring
    rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
    · rw [← hderivEq]; exact hle
    · have := treeBP_deriv_pos hp0 huv hAr hBr
      linarith

/-- **The belief-propagation map is conjugate to no special map.**  In the expansive regime its
interior fixed point has nonzero multiplier of modulus at most one, which none of the power, inverse
power, Chebyshev or Lattès families admits. -/
theorem treeBPC_not_conj_special {p : ℕ} (hp : 2 ≤ p) {u v : ℝ}
    (hv : -1 < v) (huv : v < u) (hu : u < 1)
    (hlam : 1 < (p : ℝ) * (u - v) / 2) :
    ∃ (c dR : ℂ), treeBPC p (u : ℂ) (v : ℂ) c = c ∧
      HasDerivAt (treeBPC p (u : ℂ) (v : ℂ)) dR c ∧ dR ≠ 0 ∧ ‖dR‖ ≤ 1 ∧
      (∀ (n : ℕ) (φ : ℂ → ℂ) (dφ : ℂ), 2 ≤ n →
        (∀ z, φ (treeBPC p (u : ℂ) (v : ℂ) z) = powerMap n (φ z)) →
        HasDerivAt φ dφ c → dφ ≠ 0 → False) ∧
      (∀ (n : ℕ) (φ : ℂ → ℂ) (dφ : ℂ), 2 ≤ n →
        (∀ z, φ (treeBPC p (u : ℂ) (v : ℂ) z) = invPowerMap n (φ z)) →
        HasDerivAt φ dφ c → dφ ≠ 0 → φ c ≠ 0 → False) ∧
      (∀ (n : ℕ) (φ : ℂ → ℂ) (dφ : ℂ), 2 ≤ n →
        (∀ z, φ (treeBPC p (u : ℂ) (v : ℂ) z) = dicksonMap n (φ z)) →
        HasDerivAt φ dφ c → dφ ≠ 0 → False) ∧
      (∀ (L : PeriodPair) (a z₀ : ℂ), 1 < ‖a‖ →
        (∀ z, treeBPC p (u : ℂ) (v : ℂ) (L.weierstrassP z) = L.weierstrassP (a * z)) →
        z₀ ∉ (L.lattice : Set ℂ) → a * z₀ ∉ (L.lattice : Set ℂ) →
        L.derivWeierstrassP z₀ ≠ 0 → L.weierstrassP z₀ = c → False) := by
  obtain ⟨c, dR, hfix, hR, hdR, hle⟩ :=
    exists_treeBPC_nonsuper_nonrepelling_fixedPoint hp hv huv hu hlam
  refine ⟨c, dR, hfix, hR, hdR, hle, ?_, ?_, ?_, ?_⟩
  · intro n φ dφ hn hconj hφ hφne
    exact not_conj_powerMap_of_nonsuper_nonrepelling hn hconj hR hfix hφ hφne hdR hle
  · intro n φ dφ hn hconj hφ hφne hφc
    exact not_conj_invPowerMap_of_nonrepelling hn hconj hR hfix hφ hφne hφc hle
  · intro n φ dφ hn hconj hφ hφne
    exact not_conj_dicksonMap_of_nonrepelling hn hconj hR hfix hφ hφne hle
  · intro L a z₀ ha hsemi hz₀ haz₀ hne hval
    refine not_lattes_of_nonrepelling ha hsemi hz₀ haz₀ hne ?_ ?_ hle
    · rw [hval]; exact hR
    · rw [hval]; exact hfix

end

end GaloisForLFunctions.HTGeometry
