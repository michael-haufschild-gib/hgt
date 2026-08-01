import GaloisForLFunctions.HTGeometry.BohrProductSpectrum
import GaloisForLFunctions.HTGeometry.BohrMeanInvariance
import GaloisForLFunctions.HTGeometry.BohrTrigPolynomial

/-!
# The product rule for frequency modules, from uniform approximation

Multiplying by a trigonometric polynomial enlarges the frequency module by the polynomial's own
frequencies.  Since Bohr coefficients are `1`-Lipschitz for the uniform distance, that bound passes
to uniform limits: if the second factor is uniformly approximable by trigonometric polynomials whose
frequencies stay in a set `S`, the frequency module of the product lies in the module of the first
factor joined with the span of `S`.

This reduces the general product rule to the approximation statement alone.
-/

open Filter Topology Complex

namespace GaloisForLFunctions

/-- **The product rule from uniform approximation.**  If `g` is uniformly approximable by
trigonometric polynomials with frequencies in `S`, the frequency module of `f · g` lies in the
frequency module of `f` joined with the span of `S`. -/
theorem bohrFrequencyModule_mul_le_of_uniform_approx {f g : ℝ → ℂ} {C : ℝ}
    (hfc : Continuous f) (hfa : HTGeometry.IsBohrAlmostPeriodic f) (hfb : ∀ t, ‖f t‖ ≤ C)
    (hgc : Continuous g) (hga : HTGeometry.IsBohrAlmostPeriodic g) (S : Set ℝ)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ (s : Finset ℝ) (cg : ℝ → ℂ), (↑s ⊆ S) ∧
      ∀ t : ℝ, ‖g t - ∑ μ ∈ s, cg μ * expChar μ t‖ ≤ ε) :
    bohrFrequencyModule (fun t => f t * g t)
      ≤ bohrFrequencyModule f ⊔ Submodule.span ℚ S := by
  classical
  have hC : 0 ≤ C := le_trans (norm_nonneg (f 0)) (hfb 0)
  rw [bohrFrequencyModule]
  refine Submodule.span_le.mpr ?_
  intro lam hlam
  by_contra hnot
  refine hlam ?_
  -- every approximation bounds the coefficient by `C·ε`
  have key : ∀ ε : ℝ, 0 < ε → ‖bohrCoefficient (fun t => f t * g t) lam‖ ≤ C * ε := by
    intro ε hε
    obtain ⟨s, cg, hsS, hbound⟩ := happrox ε hε
    set G : ℝ → ℂ := fun t => ∑ μ ∈ s, cg μ * expChar μ t with hG
    have hGc : Continuous G := by
      rw [hG]
      exact continuous_finsetSum _ (fun μ _ => continuous_const.mul (continuous_expChar μ))
    have hGa : HTGeometry.IsBohrAlmostPeriodic G := by
      rw [hG]
      refine isBohrAlmostPeriodic_sum s (fun μ _ => continuous_const.mul (continuous_expChar μ))
        (fun μ _ => isBohrAlmostPeriodic_const_mul (cg μ) (isBohrAlmostPeriodic_expChar μ))
    have hle : bohrFrequencyModule (fun t => f t * G t)
        ≤ bohrFrequencyModule f ⊔ Submodule.span ℚ S := by
      refine le_trans (bohrFrequencyModule_mul_trigPoly_le s cg (fun μ => μ) hfc hfa) ?_
      refine sup_le_sup_left (Submodule.span_le.mpr ?_) _
      intro x hx
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hx
      obtain ⟨μ, hμ, rfl⟩ := hx
      exact Submodule.subset_span (hsS hμ)
    have hzero : bohrCoefficient (fun t => f t * G t) lam = 0 := by
      by_contra hne
      exact hnot (hle (Submodule.subset_span (by exact hne)))
    have hdiff : ∀ t : ℝ, ‖f t * g t - f t * G t‖ ≤ C * ε := by
      intro t
      have : f t * g t - f t * G t = f t * (g t - G t) := by ring
      rw [this, norm_mul]
      exact mul_le_mul (hfb t) (hbound t) (norm_nonneg _) hC
    have hlip := norm_bohrCoefficient_sub_le (hfc.mul hgc)
      (isBohrAlmostPeriodic_mul hfc hfa hgc hga) (hfc.mul hGc)
      (isBohrAlmostPeriodic_mul hfc hfa hGc hGa) hdiff lam
    have hlip' : ‖bohrCoefficient (fun t => f t * g t) lam
        - bohrCoefficient (fun t => f t * G t) lam‖ ≤ C * ε := hlip
    rw [hzero, sub_zero] at hlip'
    exact hlip'
  by_contra hne
  have hpos : 0 < ‖bohrCoefficient (fun t => f t * g t) lam‖ := norm_pos_iff.mpr hne
  have hεpos : 0 < ‖bohrCoefficient (fun t => f t * g t) lam‖ / (2 * (C + 1)) := by
    have : (0 : ℝ) < 2 * (C + 1) := by linarith
    positivity
  have hbound := key _ hεpos
  have hCle : C * (‖bohrCoefficient (fun t => f t * g t) lam‖ / (2 * (C + 1)))
      < ‖bohrCoefficient (fun t => f t * g t) lam‖ := by
    have h2 : (0 : ℝ) < 2 * (C + 1) := by linarith
    rw [mul_div_assoc']
    rw [div_lt_iff₀ h2]
    nlinarith
  linarith

/-- A character written multiplicatively is the corpus's Bohr exponential. -/
theorem expChar_eq_bohrExp (mu t : ℝ) : expChar mu t = bohrExp mu t := by
  rw [expChar_eq_bohrChar, bohrExp]

/-- The Bohr coefficients of a trigonometric polynomial indexed by its own frequencies. -/
theorem bohrCoefficient_trigPoly_expChar (s : Finset ℝ) (cg : ℝ → ℂ) (lam : ℝ) :
    bohrCoefficient (fun t => ∑ μ ∈ s, cg μ * expChar μ t) lam
      = ∑ μ ∈ s, if μ = lam then cg μ else 0 := by
  have hfun : (fun t : ℝ => ∑ μ ∈ s, cg μ * expChar μ t)
      = fun t : ℝ => ∑ μ ∈ s, cg μ * bohrExp μ t := by
    funext t
    exact Finset.sum_congr rfl fun μ _ => by rw [expChar_eq_bohrExp]
  rw [hfun]
  exact bohrCoefficient_trigPoly s cg id lam

/-- **The frequency module of a uniform limit.**  If `g` is uniformly approximable by trigonometric
polynomials with frequencies in `S`, its frequency module lies in the `ℚ`-span of `S`. -/
theorem bohrFrequencyModule_le_of_uniform_approx {g : ℝ → ℂ}
    (hgc : Continuous g) (hga : HTGeometry.IsBohrAlmostPeriodic g) (S : Set ℝ)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ (s : Finset ℝ) (cg : ℝ → ℂ), (↑s ⊆ S) ∧
      ∀ t : ℝ, ‖g t - ∑ μ ∈ s, cg μ * expChar μ t‖ ≤ ε) :
    bohrFrequencyModule g ≤ Submodule.span ℚ S := by
  classical
  rw [bohrFrequencyModule]
  refine Submodule.span_le.mpr ?_
  intro lam hlam
  by_contra hnot
  refine hlam ?_
  have key : ∀ ε : ℝ, 0 < ε → ‖bohrCoefficient g lam‖ ≤ ε := by
    intro ε hε
    obtain ⟨s, cg, hsS, hbound⟩ := happrox ε hε
    have hGc : Continuous (fun t : ℝ => ∑ μ ∈ s, cg μ * expChar μ t) :=
      continuous_finsetSum _ (fun μ _ => continuous_const.mul (continuous_expChar μ))
    have hGa : HTGeometry.IsBohrAlmostPeriodic (fun t : ℝ => ∑ μ ∈ s, cg μ * expChar μ t) :=
      isBohrAlmostPeriodic_sum s (fun μ _ => continuous_const.mul (continuous_expChar μ))
        (fun μ _ => isBohrAlmostPeriodic_const_mul (cg μ) (isBohrAlmostPeriodic_expChar μ))
    have hzero : bohrCoefficient (fun t : ℝ => ∑ μ ∈ s, cg μ * expChar μ t) lam = 0 := by
      rw [bohrCoefficient_trigPoly_expChar]
      refine Finset.sum_eq_zero fun μ hμ => ?_
      have hne : μ ≠ lam := by
        intro h
        exact hnot (h ▸ Submodule.subset_span (hsS hμ))
      simp [hne]
    have hlip := norm_bohrCoefficient_sub_le hgc hga hGc hGa hbound lam
    rw [hzero, sub_zero] at hlip
    exact hlip
  have hle : ‖bohrCoefficient g lam‖ ≤ 0 :=
    le_of_forall_pos_le_add fun ε hε => by simpa using key ε hε
  exact norm_le_zero_iff.mp hle

/-- **The frequency module of a uniform limit, along a fixed frequency sequence.**  If `g` is
uniformly approximated by the partial sums of an exponential series whose frequencies lie in `S`,
its frequency module lies in the `ℚ`-span of `S`. -/
theorem bohrFrequencyModule_le_of_uniform_approx_nat {g : ℝ → ℂ}
    (hgc : Continuous g) (hga : HTGeometry.IsBohrAlmostPeriodic g) (S : Set ℝ) (mu : ℕ → ℝ)
    (hmu : ∀ n, mu n ∈ S)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ (N : ℕ) (cg : ℕ → ℂ),
      ∀ t : ℝ, ‖g t - ∑ n ∈ Finset.range N, cg n * expChar (mu n) t‖ ≤ ε) :
    bohrFrequencyModule g ≤ Submodule.span ℚ S := by
  classical
  rw [bohrFrequencyModule]
  refine Submodule.span_le.mpr ?_
  intro lam hlam
  by_contra hnot
  refine hlam ?_
  have key : ∀ ε : ℝ, 0 < ε → ‖bohrCoefficient g lam‖ ≤ ε := by
    intro ε hε
    obtain ⟨N, cg, hbound⟩ := happrox ε hε
    have hGc : Continuous (fun t : ℝ => ∑ n ∈ Finset.range N, cg n * expChar (mu n) t) :=
      continuous_finsetSum _ (fun n _ => continuous_const.mul (continuous_expChar (mu n)))
    have hGa : HTGeometry.IsBohrAlmostPeriodic
        (fun t : ℝ => ∑ n ∈ Finset.range N, cg n * expChar (mu n) t) :=
      isBohrAlmostPeriodic_sum (Finset.range N)
        (fun n _ => continuous_const.mul (continuous_expChar (mu n)))
        (fun n _ => isBohrAlmostPeriodic_const_mul (cg n) (isBohrAlmostPeriodic_expChar (mu n)))
    have hzero : bohrCoefficient
        (fun t : ℝ => ∑ n ∈ Finset.range N, cg n * expChar (mu n) t) lam = 0 := by
      have hfun : (fun t : ℝ => ∑ n ∈ Finset.range N, cg n * expChar (mu n) t)
          = fun t : ℝ => ∑ n ∈ Finset.range N, cg n * bohrExp (mu n) t := by
        funext t
        exact Finset.sum_congr rfl fun n _ => by rw [expChar_eq_bohrExp]
      rw [hfun, bohrCoefficient_trigPoly]
      refine Finset.sum_eq_zero fun n _ => ?_
      have hne : mu n ≠ lam := by
        intro h
        exact hnot (h ▸ Submodule.subset_span (hmu n))
      simp [hne]
    have hlip := norm_bohrCoefficient_sub_le hgc hga hGc hGa hbound lam
    rw [hzero, sub_zero] at hlip
    exact hlip
  have hle : ‖bohrCoefficient g lam‖ ≤ 0 :=
    le_of_forall_pos_le_add fun ε hε => by simpa using key ε hε
  exact norm_le_zero_iff.mp hle

/-- **The frequency module of a uniform limit, along a fixed indexed frequency family.**  If `g` is
uniformly approximated by finite exponential sums drawn from a fixed frequency family lying in `S`,
its frequency module lies in the `ℚ`-span of `S`. -/
theorem bohrFrequencyModule_le_of_uniform_approx_index {g : ℝ → ℂ} {ι : Type*}
    (hgc : Continuous g) (hga : HTGeometry.IsBohrAlmostPeriodic g) (S : Set ℝ) (mu : ι → ℝ)
    (hmu : ∀ i, mu i ∈ S)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ (u : Finset ι) (c : ι → ℂ),
      ∀ t : ℝ, ‖g t - ∑ i ∈ u, c i * expChar (mu i) t‖ ≤ ε) :
    bohrFrequencyModule g ≤ Submodule.span ℚ S := by
  classical
  rw [bohrFrequencyModule]
  refine Submodule.span_le.mpr ?_
  intro lam hlam
  by_contra hnot
  refine hlam ?_
  have key : ∀ ε : ℝ, 0 < ε → ‖bohrCoefficient g lam‖ ≤ ε := by
    intro ε hε
    obtain ⟨u, c, hbound⟩ := happrox ε hε
    have hGc : Continuous (fun t : ℝ => ∑ i ∈ u, c i * expChar (mu i) t) :=
      continuous_finsetSum _ (fun i _ => continuous_const.mul (continuous_expChar (mu i)))
    have hGa : HTGeometry.IsBohrAlmostPeriodic (fun t : ℝ => ∑ i ∈ u, c i * expChar (mu i) t) :=
      isBohrAlmostPeriodic_sum u
        (fun i _ => continuous_const.mul (continuous_expChar (mu i)))
        (fun i _ => isBohrAlmostPeriodic_const_mul (c i) (isBohrAlmostPeriodic_expChar (mu i)))
    have hzero : bohrCoefficient (fun t : ℝ => ∑ i ∈ u, c i * expChar (mu i) t) lam = 0 := by
      have hfun : (fun t : ℝ => ∑ i ∈ u, c i * expChar (mu i) t)
          = fun t : ℝ => ∑ i ∈ u, c i * bohrExp (mu i) t := by
        funext t
        exact Finset.sum_congr rfl fun i _ => by rw [expChar_eq_bohrExp]
      rw [hfun, bohrCoefficient_trigPoly]
      refine Finset.sum_eq_zero fun i _ => ?_
      have hne : mu i ≠ lam := by
        intro h
        exact hnot (h ▸ Submodule.subset_span (hmu i))
      simp [hne]
    have hlip := norm_bohrCoefficient_sub_le hgc hga hGc hGa hbound lam
    rw [hzero, sub_zero] at hlip
    exact hlip
  have hle : ‖bohrCoefficient g lam‖ ≤ 0 :=
    le_of_forall_pos_le_add fun ε hε => by simpa using key ε hε
  exact norm_le_zero_iff.mp hle

end GaloisForLFunctions
