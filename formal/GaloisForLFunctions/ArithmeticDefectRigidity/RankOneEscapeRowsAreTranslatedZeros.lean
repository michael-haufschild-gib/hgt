import GaloisForLFunctions.ArithmeticDefectRigidity.MellinResiduesPinPowerLikeSolutionsToZeros
import GaloisForLFunctions.ArithmeticDefectRigidity.TwoDilationEigenrowsArePowerRows

/-!
# Rank-one escape rows are exactly the translated zeros

For `0 < ε < 1/2` and `1/2 < Re s < 1 − ε`, call a complex row a *rank-one escape row at `s`* if it
has infinite pronic energy, is an approximate eigenrow of `D₂` and `D₃` with exponent `s`
(`w − 2^s D₂ w`, `w − 3^s D₃ w` of finite energy), and satisfies the renormalized inversion law
(`S_ε w − c' n^{1−ε}` of finite energy for some `c'`).

* `riemannZeta_add_eq_zero_iff_exists_rankOneEscapeRow`: such a row exists iff `ζ(s + ε) = 0`.

The two dilation laws make the row `c n^s` plus finite energy with `c ≠ 0`
(`exists_cPronicEnergy_sub_cpow_ne_top_same`); the Mellin residue at `s` then forces
`ζ(s + ε) = 0` (`riemannZeta_add_eq_zero_of_powerLike_solution`). Conversely, at a translated zero
the power row `n^s` itself satisfies all three laws, by the symbol estimate
`norm_powerRowCofactorSum_sub_le`.
-/

open Finset Filter Topology Complex
open GaloisForLFunctions.BezoutValuationIncidence (pronicNorm pronicNorm_nonneg pronicNorm_sq)

noncomputable section
set_option autoImplicit false

namespace GaloisForLFunctions.ArithmeticDefectRigidity

theorem energyBounded_of_cPronicEnergy_ne_top {r : ℕ → ℂ} (h : cPronicEnergy r ≠ ⊤) :
    EnergyBounded r := by
  obtain ⟨B, hB⟩ := (pronicEnergy_ne_top_iff fun n => ‖r n‖).mp h
  refine ⟨B ^ 2, fun T => ?_⟩
  rw [← pronicNorm_sq]
  exact pow_le_pow_left₀ (pronicNorm_nonneg T _) (hB T) 2

theorem cPronicEnergy_ne_top_of_energyBounded {r : ℕ → ℂ} (h : EnergyBounded r) :
    cPronicEnergy r ≠ ⊤ := by
  obtain ⟨E, hE⟩ := h
  rw [cPronicEnergy, pronicEnergy_ne_top_iff]
  refine ⟨Real.sqrt E, fun T => ?_⟩
  rw [← Real.sqrt_sq (pronicNorm_nonneg T _), pronicNorm_sq]
  exact Real.sqrt_le_sqrt (hE T)

/-- A power row above the critical line has infinite pronic energy. -/
theorem cPronicEnergy_cpow_eq_top {s : ℂ} (hs : 1 / 2 < s.re) :
    cPronicEnergy (fun n => (n : ℂ) ^ s) = ⊤ := by
  by_contra hfin
  have hs0 : s ≠ 0 := fun h => by rw [h, Complex.zero_re] at hs; linarith
  have hrow : (fun n : ℕ => ‖(n : ℂ) ^ s‖) =
      fun n : ℕ => (0 : ℝ) - (-1) * (n : ℝ) ^ (1 - (1 - s.re)) := by
    funext n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [Complex.zero_cpow hs0]
      exact (Real.zero_rpow (by linarith)).symm
    · rw [show (1 : ℝ) - (1 - s.re) = s.re by ring, ← Complex.ofReal_natCast,
        Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast hn)]
      ring
  have h1 : pronicEnergy (fun n : ℕ => (0 : ℝ) - (-1) * (n : ℝ) ^ (1 - (1 - s.re))) ≠ ⊤ := by
    rw [← hrow]; exact hfin
  have h2 : pronicEnergy (fun n : ℕ => (0 : ℝ) - 0 * (n : ℝ) ^ (1 - (1 - s.re))) ≠ ⊤ := by
    simp [pronicEnergy]
  have := eq_of_pronicEnergy_sub_pole_ne_top (ε := 1 - s.re) (by linarith) (w := fun _ => 0) h1 h2
  norm_num at this

/-- **Rank-one escape rows are exactly the translated zeros.** -/
theorem riemannZeta_add_eq_zero_iff_exists_rankOneEscapeRow {ε : ℝ} (hε0 : 0 < ε)
    (hε : ε < 1 / 2) {s : ℂ} (hs : 1 / 2 < s.re) (hs1 : s.re < 1 - ε) :
    riemannZeta (s + ε) = 0 ↔
      ∃ w : ℕ → ℂ, w 0 = 0 ∧ cPronicEnergy w = ⊤ ∧
        cPronicEnergy (cEulerLaw 2 s w) ≠ ⊤ ∧ cPronicEnergy (cEulerLaw 3 s w) ≠ ⊤ ∧
        ∃ c' : ℂ, cPronicEnergy (fun n => cTotalCofactorSum ε w n -
          c' * ((n : ℝ) : ℂ) ^ ((1 - ε : ℝ) : ℂ)) ≠ ⊤ := by
  have hs0 : s ≠ 0 := fun h => by rw [h, Complex.zero_re] at hs; linarith
  have hsα : s ≠ ((1 - ε : ℝ) : ℂ) := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  constructor
  · intro hz
    obtain ⟨K, hK⟩ := norm_powerRowCofactorSum_sub_le hε0 (by linarith) (by linarith : 0 < s.re) hs1
    have hw0 : (fun n : ℕ => (n : ℂ) ^ s) 0 = 0 := by simp [Complex.zero_cpow hs0]
    have hzero : cPronicEnergy (fun n : ℕ => (n : ℂ) ^ s - 1 * (n : ℂ) ^ s) ≠ ⊤ := by
      simp [cPronicEnergy, pronicEnergy]
    refine ⟨fun n => (n : ℂ) ^ s, hw0, cPronicEnergy_cpow_eq_top hs,
      cPronicEnergy_cEulerLaw_ne_top (by linarith) (by linarith) hw0 hzero (by norm_num),
      cPronicEnergy_cEulerLaw_ne_top (by linarith) (by linarith) hw0 hzero (by norm_num),
      powerPoleTrace ε s, ?_⟩
    have hconv : ∀ n, cTotalCofactorSum ε (fun m : ℕ => (m : ℂ) ^ s) n =
        powerRowCofactorSum ε s n := by
      intro n
      unfold cTotalCofactorSum powerRowCofactorSum
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Complex.ofReal_cpow (Nat.cast_nonneg j), Complex.ofReal_natCast]
      push_cast
      rfl
    rw [cPronicEnergy, pronicEnergy_ne_top_iff]
    have hδ : 0 < 1 - (s.re - ε) := by linarith
    refine ⟨Real.sqrt (K ^ 2 * (1 + 1 / (1 - (s.re - ε)))), fun T => ?_⟩
    rw [← Real.sqrt_sq (pronicNorm_nonneg T _), pronicNorm_sq]
    refine Real.sqrt_le_sqrt (TransHorizonIncidenceMechanics.sum_sq_le_of_abs_le_sqrt_rpow hδ
      (fun n hn => ?_) T)
    rw [show 1 - (1 - (s.re - ε)) = s.re - ε by ring, abs_of_nonneg (norm_nonneg _), hconv n]
    have h := hK n hn
    rw [hz, zero_mul, sub_zero] at h
    exact h
  · rintro ⟨w, hw0, hwinf, h2, h3, c', hlaw⟩
    obtain ⟨c, hc⟩ := exists_cPronicEnergy_sub_cpow_ne_top_same hs (by linarith) hw0 h2 h3
    have hc0 : c ≠ 0 := by
      rintro rfl
      have hw : cPronicEnergy w ≠ ⊤ := by simpa using hc
      exact hw hwinf
    set r : ℕ → ℂ := fun n => w n - c * (n : ℂ) ^ s with hrdef
    set r' : ℕ → ℂ := fun n => cTotalCofactorSum ε w n - c' * ((n : ℝ) : ℂ) ^ ((1 - ε : ℝ) : ℂ)
      with hr'def
    have hr0 : r 0 = 0 := by simp [hrdef, hw0, Complex.zero_cpow hs0]
    have hr'0 : r' 0 = 0 := by
      simp [hr'def, cTotalCofactorSum]
      right
      intro h
      have := congrArg Complex.re h
      simp at this
      linarith
    refine riemannZeta_add_eq_zero_of_powerLike_solution hε0 hε {s}
      (fun t ht => by
        rw [Finset.mem_singleton] at ht; subst ht
        exact ⟨hs, by linarith, hsα⟩)
      (fun _ => c) hr0 (energyBounded_of_cPronicEnergy_ne_top hc) hr'0
      (energyBounded_of_cPronicEnergy_ne_top hlaw) c' ?_ s (Finset.mem_singleton_self s) hc0
    intro n
    have hfun : (fun m : ℕ => ∑ t ∈ ({s} : Finset ℂ), (fun _ => c) t * ((m : ℝ) : ℂ) ^ t + r m) =
        w := by
      funext m
      simp only [Finset.sum_singleton, hrdef, Complex.ofReal_natCast]
      ring
    rw [hfun]
    simp only [hr'def]
    ring

end GaloisForLFunctions.ArithmeticDefectRigidity
