import GaloisForLFunctions.goldbach.LiLiu.Mellin.CharacterInversion
import GaloisForLFunctions.goldbach.LiLiu.Mellin.VerticalLine
import GaloisForLFunctions.goldbach.LiLiu.Boundary.KernelRegularity

/-! # The odd-character moment on two Mellin lines

Each odd character gives a rank-one kernel. Integrating its two factors
recovers the squared norm of the normalized finite character polynomial.
-/

namespace GaloisForLFunctions.Goldbach.LiLiu
open _root_.Complex MeasureTheory Filter Finset
open scoped ComplexConjugate Classical
noncomputable section

private theorem characterIntegrand_integrable {n : ℕ} (φ : TestWeight) (h : modulusGRH (n+1))
    {χ : DirichletCharacter ℂ (n+1)} (hχ : χ ≠ 1) {a : ℝ} (ha : 0 < a) (ht : a ≤ 1) :
    Integrable (fun t => characterIntegrand φ χ (mellinLine a t)) := by
  obtain ⟨A,hA,hb⟩ := characterFeature_strip_bound h ha
  have hl : Continuous (mellinLine a) := by unfold mellinLine; fun_prop
  have hc : Continuous (fun t => characterFeature χ (mellinLine a t)) :=
    continuous_iff_continuousAt.mpr fun t =>
      (characterFeature_analyticAt h hχ (by simpa [mellinLine] using ha)).continuousAt.comp hl.continuousAt
  have hV := (mellinMultiplier_continuous (n+1) (Nat.succ_pos n) φ).comp hl
  apply ((mellinMultiplier_quarter_integrable (n+1) (Nat.succ_pos n) φ a).const_mul A).mono'
    (hV.mul hc).aestronglyMeasurable
  filter_upwards with t
  have H := hb χ hχ (mellinLine a t) (by simp [mellinLine]) (by simpa [mellinLine] using ht)
  change ‖mellinMultiplier _ φ _ * characterFeature χ _‖ ≤ _
  rw [norm_mul]
  calc
    _ ≤ ‖mellinMultiplier (n+1) φ (mellinLine a t)‖ * (A*(1+|t|)^(1/4:ℝ)) :=
      mul_le_mul_of_nonneg_left (by simpa [mellinLine] using H) (norm_nonneg _)
    _ = _ := by ring

def characterTestKernel (N : ℕ) [NeZero N] (φ : TestWeight) (a : ℝ) (p : ℝ × ℝ) : ℂ :=
  let s := mellinLine a p.1
  let z := mellinLine a p.2
  (mellinMultiplier N φ s * conj (mellinMultiplier N φ z)) * characterKernel N s z

/-- Absolute integrability and the exact value of the finite Gram sum. -/
theorem characterMoment_integral {n : ℕ} (φ : TestWeight) (h : modulusGRH (n+1))
    {a : ℝ} (ha : 0 < a) (ht : a ≤ 1) :
    Integrable (characterTestKernel (n+1) φ a) ∧
    (1/(2*Real.pi):ℂ)^2 * (∫ p, characterTestKernel (n+1) φ a p) = (oddMoment φ n : ℂ) := by
  let N := n+1
  let c := (1/(2*Real.pi):ℂ)
  let V := fun t => mellinMultiplier N φ (mellinLine a t)
  let F := fun (χ : DirichletCharacter ℂ N) t => characterIntegrand φ χ (mellinLine a t)
  let U (χ : DirichletCharacter ℂ N) := unitCharacterSum n
    (fun u => (coefficient φ N (u : ZMod N).val : ℂ)) χ
  let X := univ.filter (fun χ : DirichletCharacter ℂ N => χ.Odd)
  let G (χ : DirichletCharacter ℂ N) (p : ℝ × ℝ) := F χ p.1 * conj (F χ p.2)
  have hn {χ : DirichletCharacter ℂ N} (hχ : χ ∈ X) : χ ≠ 1 :=
    odd_ne_principal (mem_filter.mp hχ).2
  have hi (χ) (hχ : χ ∈ X) : Integrable (G χ) := by
    have hF := characterIntegrand_integrable φ h (hn hχ) ha ht
    have hconj : Integrable (fun t => conj (F χ t)) := by
      apply hF.norm.mono' (continuous_conj.comp_aestronglyMeasurable hF.1)
      exact Eventually.of_forall fun _ => (RCLike.norm_conj _).le
    exact hF.mul_prod hconj
  have hK (p : ℝ × ℝ) : characterTestKernel N φ a p = (2/(N.totient : ℂ)) * ∑ χ ∈ X, G χ p := by
    let P := fun (χ : DirichletCharacter ℂ N) =>
      characterFeature χ (mellinLine a p.1) * conj (characterFeature χ (mellinLine a p.2))
    change (V p.1 * conj (V p.2)) * ((2/(N.totient:ℂ)) * ∑ χ ∈ X, P χ) = _
    rw [mul_left_comm,Finset.mul_sum]
    congr 1
    apply sum_congr rfl
    intro χ hχ
    simp only [G,F,V,P,characterIntegrand,mellinMultiplier,map_mul]
    ring
  change Integrable (characterTestKernel N φ a) ∧ c^2 * (∫ p, characterTestKernel N φ a p) = _
  rw [show characterTestKernel N φ a = fun p => (2/(N.totient:ℂ))*∑ χ ∈ X, G χ p from funext hK]
  refine ⟨(integrable_finsetSum X hi).const_mul _,?_⟩
  rw [integral_const_mul,integral_finsetSum X hi]
  have hN : 0 < (N:ℝ) := Nat.cast_pos.mpr (Nat.succ_pos n)
  have hs : (Real.sqrt N : ℂ)^2 = (N : ℂ) := by
    rw [← Complex.ofReal_pow,Real.sq_sqrt hN.le,Complex.ofReal_natCast]
  have hn0 : (Real.sqrt N : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hN).ne'
  have hval (χ) (hχ : χ ∈ X) : c^2 * (∫ p, G χ p) = (‖U χ‖^2 : ℝ) / (N : ℂ) := by
    have e : U χ/(Real.sqrt N : ℂ) = -c*(∫ t : ℝ, F χ t) :=
      character_polynomial_integral φ h (hn hχ) ha ht
    rw [show (∫ p, G χ p) = (∫ t : ℝ, F χ t)*conj (∫ t : ℝ, F χ t) by
      simp only [G,integral_prod_mul,integral_conj]]
    calc
      _ = (-c*(∫ t : ℝ, F χ t)) * (-c*conj (∫ t : ℝ, F χ t)) := by ring
      _ = (U χ/(Real.sqrt N : ℂ))*conj (U χ/(Real.sqrt N : ℂ)) := by rw [e]; simp [c]
      _ = _ := by rw [map_div,conj_ofReal,div_mul_div_comm,← sq,hs,Complex.mul_conj,Complex.normSq_eq_norm_sq]
  change c^2 * ((2/(N.totient:ℂ)) * _) = _
  rw [mul_left_comm,Finset.mul_sum]
  simp_rw [Finset.sum_congr rfl hval]
  simp only [oddMoment,Complex.ofReal_div,Complex.ofReal_mul,Complex.ofReal_sum,Complex.ofReal_natCast,
    Complex.ofReal_ofNat,← Finset.sum_div,X,U,N]
  ring

#print axioms characterMoment_integral
end
end GaloisForLFunctions.Goldbach.LiLiu
