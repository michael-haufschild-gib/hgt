import GaloisForLFunctions.goldbach.LiLiu.TestWeight
import GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.SourceCuspMellinReflection

/-!
# The Goldbach Mellin weight on the moving strip

Multiplication by √u absorbs the factor n⁻¹ᐟ² in the character polynomial.
On the left boundary α = 1/log N, the factor Nˢ has constant modulus e.
Rapid Mellin decay therefore bounds the boundary test uniformly in N.
-/

namespace GaloisForLFunctions.Goldbach.LiLiu
open _root_.Complex Set MetaplecticMobiusDescent.CubicEisenstein
open scoped ContDiff
noncomputable section

/-- The companion Φ(u) = √u φ(u). -/
def companion (φ : TestWeight) : ℝ → ℂ := Vstar (fun u => (φ u : ℂ))

private theorem castWeight_support (φ : TestWeight) :
    Function.support (fun u => (φ u : ℂ)) ⊆ Icc (1 / 3 : ℝ) (2 / 3) := by
  intro u hu
  exact φ.supported (fun he => hu (by simp [he]))

theorem companion_support (φ : TestWeight) :
    Function.support (companion φ) ⊆ Icc (1 / 3 : ℝ) (2 / 3) :=
  Vstar_support _ _ _ (castWeight_support φ)

theorem companion_smooth (φ : TestWeight) : ContDiff ℝ ∞ (companion φ) :=
  Vstar_contDiff _ _ _ (by norm_num) (castWeight_support φ) (Complex.ofRealCLM.contDiff.comp φ.smooth)

theorem mellin_companion_differentiable (φ : TestWeight) :
    Differentiable ℂ (mellin (companion φ)) :=
  compact_source_mellin_differentiable _ _ _ (by norm_num) (companion_support φ) (companion_smooth φ)

/-- Inversion on every vertical line, including the moving left boundary. -/
theorem companion_inversion (φ : TestWeight) (σ x : ℝ) (hx : 0 < x) :
    companion φ x = (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ,
      (x : ℂ) ^ (-((σ : ℂ) + t * I)) * mellin (companion φ) ((σ : ℂ) + t * I) :=
  compactMellin_inversion _ _ _ (by norm_num) (companion_support φ) (companion_smooth φ) σ x hx

def leftEdge (N : ℕ) : ℝ := 1 / Real.log N

/-- The Mellin functional density before the universal factor 1/(2π). -/
def boundaryTest (φ : TestWeight) (N : ℕ) (t : ℝ) : ℂ :=
  let s := (leftEdge N : ℂ) + t * I
  (N : ℂ) ^ s * mellin (companion φ) s * (1 + s)

theorem boundaryTest_decay (φ : TestWeight) (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ Real.log N → ∀ t : ℝ,
      (1 + |t|) ^ j * ‖boundaryTest φ N t‖ ≤ C := by
  obtain ⟨D, hD, hbound⟩ := compact_source_mellin_strip_decay _ _ _ (by norm_num)
    (companion_support φ) (companion_smooth φ) 0 1 (j + 1)
  refine ⟨2 * Real.exp 1 * D, by positivity, ?_⟩
  intro N hN t
  have hl : 0 < Real.log N := lt_of_lt_of_le zero_lt_one hN
  have hp : (0 : ℝ) < N := lt_of_lt_of_le zero_lt_one ((Real.log_pos_iff (Nat.cast_nonneg N)).mp hl).le
  have hα : leftEdge N ∈ Icc (0 : ℝ) 1 :=
    ⟨(one_div_pos.mpr hl).le, (div_le_one hl).mpr hN⟩
  let s := (leftEdge N : ℂ) + t * I
  have hpow : ‖(N : ℂ) ^ s‖ = Real.exp 1 := by
    rw [Complex.norm_natCast_cpow_of_pos (by exact_mod_cast hp),
      show s.re = leftEdge N by simp [s], Real.rpow_def_of_pos hp, leftEdge]
    rw [mul_one_div_cancel hl.ne']
  have hs : ‖1 + s‖ ≤ 2 * (1 + |t|) := by
    have h1 := norm_add_le (1 : ℂ) s
    have h2 := norm_add_le (leftEdge N : ℂ) ((t : ℂ) * I)
    simp only [norm_one, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hα.1] at h1 h2
    change ‖1 + s‖ ≤ 2 * (1 + |t|)
    dsimp [s] at h1 ⊢
    linarith only [h1, h2, hα.2, abs_nonneg t]
  change (1 + |t|) ^ j * ‖(N : ℂ) ^ s * mellin (companion φ) s * (1 + s)‖ ≤ _
  rw [norm_mul, norm_mul, hpow]
  have he := hbound (leftEdge N) hα t
  calc
    _ ≤ (1 + |t|) ^ j * (Real.exp 1 * ‖mellin (companion φ) s‖ * (2 * (1 + |t|))) := by
      gcongr
    _ = (2 * Real.exp 1) * ((1 + |t|) ^ (j + 1) * ‖mellin (companion φ) s‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left he (by positivity)

#print axioms companion_inversion
#print axioms boundaryTest_decay
end
end GaloisForLFunctions.Goldbach.LiLiu
