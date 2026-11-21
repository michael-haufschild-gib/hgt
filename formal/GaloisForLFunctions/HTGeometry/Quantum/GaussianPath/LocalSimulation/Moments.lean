import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.LocalSimulation.CoordinateLaw
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPathCoefficientMass

/-! # Arbitrary fixed moments of Gaussian interactions on growing open prefixes -/
open Filter MeasureTheory ProbabilityTheory Finset
open scoped Topology ENNReal
namespace GaloisForLFunctions.HTGeometry.LocalPatches
noncomputable section

private theorem prefix_cap (F : ℝ → ℝ) (hF : ∀ x, 0 ≤ x → 0 ≤ F x)
    (hMeas : Measurable (fun x : ℝ => F |x|))
    (hi : Integrable (fun x : ℝ => F |x|) (gaussianReal 0 1)) :
    ∃ B : ℝ, 0 < B ∧ ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      ∃ R : ℝ, 1 ≤ R ∧ (∀ l, |pathPauliDisorderShell ω n l| ≤ R) ∧
        F R ≤ B*((n+2:ℕ):ℝ) := by
  classical
  let f (x : ℝ) := F |x|
  let m := ∫ x, f x ∂gaussianReal 0 1
  have hm : 0 ≤ m := integral_nonneg fun x => hF _ (abs_nonneg x)
  have hw (d : PathPauliDirections) := coordinate_strong_law (gaussianReal 0 1) d f hMeas hi
  refine ⟨m+F 1+1,by linarith only [hm,hF 1 zero_le_one],?_⟩
  filter_upwards [ae_all_iff.mpr hw] with ω hω
  have hd (d : PathPauliDirections) := (hω d).eventually_lt_const
    (show (∫ x, f x ∂gaussianReal 0 1) < m+F 1+1 by linarith only [hF 1 zero_le_one])
  have hN := (tendsto_add_atTop_nat 2).eventually (Filter.eventually_all.mpr hd)
  filter_upwards [hN] with n hn
  let N := n+2
  let u := pathPauliDisorderShell ω n
  let S := insert (1:ℝ) (univ.image fun l : PathLabel n => |u l|)
  have hne : S.Nonempty := ⟨1,mem_insert_self ..⟩
  let R := S.max' hne
  have h1 : 1 ≤ R := le_max' _ _ (mem_insert_self ..)
  have hmem (l : PathLabel n) : |u l| ∈ S := mem_insert_of_mem
    (mem_image_of_mem (fun q : PathLabel n => |u q|) (mem_univ l))
  have hcap : ∀ l, |u l| ≤ R := fun l => le_max' S |u l| (hmem l)
  refine ⟨R,h1,hcap,?_⟩
  have hpos : 0 < (N:ℝ) := by dsimp [N]; positivity
  have oneN : 1 ≤ (N:ℝ) := by exact_mod_cast (show 1 ≤ N by dsimp [N]; omega)
  have hpoint (i : ℕ) (d : PathPauliDirections) (hi : i<N) : f (ω (i,d)) ≤ (m+F 1+1)*(N:ℝ) :=
    (single_le_sum (f := fun q => f (ω (q,d))) (fun _ _ => hF _ (abs_nonneg _))
      (mem_range.mpr hi)).trans ((div_lt_iff₀ hpos).mp (hn d)).le
  have hRmem : R ∈ S := max'_mem _ _
  rcases mem_insert.mp hRmem with he|he
  · rw [he]
    exact (by linarith only [hm] : F 1 ≤ m+F 1+1).trans
      (le_mul_of_one_le_right (by linarith only [hm,hF 1 zero_le_one]) oneN)
  · obtain ⟨l,_,hl⟩ := mem_image.mp he
    rw [←hl]
    rcases l with ⟨s,a⟩|⟨e,ab⟩
    · exact hpoint s.val (.inl a) s.isLt
    · exact hpoint e.val (.inr ab) (e.isLt.trans (by dsimp [N]; omega))

/-- The p-th power of a cap on every coefficient of the prefix is at
most linear in its size, for each fixed moment order. -/
theorem gaussian_prefix_local_moment (p : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      ∃ R : ℝ, 1 ≤ R ∧ (∀ l, |pathPauliDisorderShell ω n l| ≤ R) ∧
        R^p ≤ B*((n+2:ℕ):ℝ) := by
  apply prefix_cap (fun y => y^p) (fun _ hy => pow_nonneg hy _) (by fun_prop)
  simpa only [id,Real.norm_eq_abs] using
    (memLp_id_gaussianReal' (μ := 0) (v := 1) (p:ℝ≥0∞) (by simp)).integrable_norm_pow'

/-- One logarithmic cap holds eventually on the fixed draw, independently
of the simulation order and physical time. -/
theorem gaussian_prefix_local_exponential :
    ∃ B : ℝ, 0 < B ∧ ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      ∃ R : ℝ, 1 ≤ R ∧ (∀ l, |pathPauliDisorderShell ω n l| ≤ R) ∧
        Real.exp R ≤ B*((n+2:ℕ):ℝ) := by
  apply prefix_cap Real.exp (fun x _ => (Real.exp_pos x).le) (by fun_prop)
  have h₁ := integrable_exp_mul_gaussianReal (μ := 0) (v := 1) 1
  have h₂ := integrable_exp_mul_gaussianReal (μ := 0) (v := 1) (-1)
  apply (h₁.add h₂).mono' (by fun_prop)
  filter_upwards with x
  simp only [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),Pi.add_apply,one_mul,neg_one_mul]
  rcases le_total 0 x with hx|hx
  · rw [abs_of_nonneg hx]
    exact le_add_of_nonneg_right (Real.exp_pos _).le
  · rw [abs_of_nonpos hx]
    exact le_add_of_nonneg_left (Real.exp_pos _).le

#print axioms gaussian_prefix_local_exponential

#print axioms gaussian_prefix_local_moment
end
end GaloisForLFunctions.HTGeometry.LocalPatches
