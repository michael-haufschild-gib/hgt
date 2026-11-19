import GaloisForLFunctions.CompactHyperbolicSurfaces.BergmanKernel

/-!
# Logarithmic distortion of the hyperbolic point-pair and Bergman factors

The logarithmic distortion estimate of Koskela et al., Lemma 2.3, has
an exact point-pair analogue. Moving the endpoints costs the sum of their
hyperbolic distances, with coefficient one for the point-pair factor and
one half for the normalized Bergman factor. Positivity preserves the
same multiplicative comparison on periodization.
-/

open UpperHalfPlane
open scoped MatrixGroups
noncomputable section
namespace GaloisForLFunctions.CompactHyperbolicSurfaces
open GaloisForLFunctions.HTGeometry

private theorem distance_pair {z w Z W : ℍ} :
    dist z w ≤ dist Z W + (dist z Z + dist w W) := by
  have h := dist_triangle4 z Z W w
  rw [dist_comm W w] at h
  linarith only [h]

/-- The multiplicative distortion has no prefactor, including at zero
displacement. The two endpoints may move different distances. -/
theorem one_add_pairU_transport (z w Z W : ℍ) :
    1+pairU z w ≤ Real.exp (dist z Z + dist w W)*(1+pairU Z W) := by
  let D := dist z Z + dist w W
  have hd : 0 ≤ D := add_nonneg dist_nonneg dist_nonneg
  have ha : dist z w ≤ D+dist Z W := by linarith only [distance_pair (z:=z) (w:=w) (Z:=Z) (W:=W)]
  have hb : -dist z w ≤ D-dist Z W := by
    have h := distance_pair (z:=Z) (w:=W) (Z:=z) (W:=w)
    rw [dist_comm Z z,dist_comm W w] at h
    linarith only [h]
  have he := Real.exp_le_exp.mpr ha
  have hf := Real.exp_le_exp.mpr hb
  rw [Real.exp_add] at he
  rw [sub_eq_add_neg,Real.exp_add] at hf
  have h1 := Real.one_le_exp hd
  change 1+pairU z w ≤ Real.exp D*(1+pairU Z W)
  rw [pairU_eq_cosh,pairU_eq_cosh,Real.cosh_eq,Real.cosh_eq]
  linarith only [he,hf,h1]

private theorem log_pair_one_sided (z w Z W : ℍ) :
    Real.log (1+pairU z w)-Real.log (1+pairU Z W) ≤ dist z Z+dist w W := by
  have h₀ : 0 < 1+pairU z w := by linarith only [pairU_nonneg z w]
  have h₁ : 0 < 1+pairU Z W := by linarith only [pairU_nonneg Z W]
  have hh := Real.log_le_log h₀ (one_add_pairU_transport z w Z W)
  rw [Real.log_mul (Real.exp_ne_zero _) h₁.ne',Real.log_exp] at hh
  linarith only [hh]

/-- The logarithm of the exact positive point-pair weight is Lipschitz
in the sum of the hyperbolic endpoint distances. -/
theorem log_pairU_distortion (z w Z W : ℍ) :
    |Real.log (1+pairU z w)-Real.log (1+pairU Z W)| ≤ dist z Z+dist w W := by
  have h := log_pair_one_sided Z W z w
  rw [dist_comm Z z,dist_comm W w] at h
  exact abs_le.mpr ⟨by linarith only [h],log_pair_one_sided z w Z W⟩

/-- Normalization of the Bergman factor divides its logarithmic
displacement cost by two. -/
theorem log_bergK_distortion (z w Z W : ℍ) :
    |Real.log ‖bergK z w‖ - Real.log ‖bergK Z W‖| ≤ (dist z Z+dist w W)/2 := by
  have lognorm (a b : ℍ) : 2*Real.log ‖bergK a b‖ = -Real.log (1+pairU a b) := by
    have hh := congrArg Real.log (norm_bergK_sq a b)
    simpa only [Real.log_pow,Real.log_inv,Nat.cast_ofNat] using hh
  have h := abs_le.mp (log_pairU_distortion z w Z W)
  apply abs_le.mpr
  constructor <;> linarith only [h.1,h.2,lognorm z w,lognorm Z W]

/-- Every positive inverse-power automorphic kernel satisfies the same
global distortion law as its individual orbit terms. -/
theorem automorphic_power_transport {Γ : Subgroup SL(2, ℝ)} (hΓ : IsCocompactFree Γ)
    {σ : ℝ} (hσ : 1 < σ) (z w Z W : ℍ) :
    autR Γ (fun u => (1+u)^(-σ)) z w ≤
      Real.exp (σ*(dist z Z+dist w W))*autR Γ (fun u => (1+u)^(-σ)) Z W := by
  let D := dist z Z+dist w W
  unfold autR
  rw [← tsum_mul_left]
  apply Summable.tsum_le_tsum _ (hΓ.summable_rpow hσ z w) ((hΓ.summable_rpow hσ Z W).mul_left _)
  intro g
  let a := 1+pairU z ((g:SL(2, ℝ)) • w)
  let b := 1+pairU Z ((g:SL(2, ℝ)) • W)
  have ha : 0 < a := by dsimp only [a]; linarith only [pairU_nonneg z ((g:SL(2, ℝ)) • w)]
  have hb : 0 < b := by dsimp only [b]; linarith only [pairU_nonneg Z ((g:SL(2, ℝ)) • W)]
  have h := log_pair_one_sided Z ((g:SL(2, ℝ)) • W) z ((g:SL(2, ℝ)) • w)
  rw [dist_smul,dist_comm Z z,dist_comm W w] at h
  change Real.log b - Real.log a ≤ D at h
  change a^(-σ) ≤ Real.exp (σ*D)*b^(-σ)
  rw [Real.rpow_def_of_pos ha,Real.rpow_def_of_pos hb,← Real.exp_add,Real.exp_le_exp]
  linarith only [mul_le_mul_of_nonneg_left h (by linarith only [hσ] : 0 ≤ σ)]

#print axioms one_add_pairU_transport
#print axioms log_pairU_distortion
#print axioms log_bergK_distortion
#print axioms automorphic_power_transport
end GaloisForLFunctions.CompactHyperbolicSurfaces
