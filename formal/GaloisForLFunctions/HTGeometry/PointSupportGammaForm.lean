import GaloisForLFunctions.HTGeometry.PointSupportTriangular

/-!
# The Gamma frequency equation has no point-supported solution

The frequency equation `2η f' + f = iη(r(η)I - T)f` pairs against a test function as

`f(φ) + 2f(ηφ') + i f(ηrφ) - i T(f(ηφ)) = 0`.

On a distribution supported at the origin the first two terms are the diagonal `(2j+1)`, while both
`η`-carrying terms move each jet coefficient strictly upward.  The resulting triangular system has
only the zero solution.
-/

open Set SchwartzMap Complex

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- Multiplication by a smooth function of temperate growth on Schwartz space. -/
def mulTemperateCLM {g : ℝ → ℂ} (hg : Function.HasTemperateGrowth g) :
    SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ :=
  SchwartzMap.bilinLeftCLM (ContinuousLinearMap.mul ℂ ℂ) hg

@[simp] theorem mulTemperateCLM_apply {g : ℝ → ℂ} (hg : Function.HasTemperateGrowth g)
    (φ : SchwartzMap ℝ ℂ) (x : ℝ) : (mulTemperateCLM hg φ : ℝ → ℂ) x = φ x * g x := rfl

/-- The jet coefficients of a multiplier acting on a jet test function. -/
theorem iteratedDeriv_mulTemperate_jetTest {g : ℝ → ℂ} (hgt : Function.HasTemperateGrowth g)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (i j : ℕ) :
    iteratedDeriv j ((mulTemperateCLM hgt (jetTest i) : SchwartzMap ℝ ℂ) : ℝ → ℂ) 0
      = if i ≤ j then (j.choose (j - i) : ℂ) * iteratedDeriv (j - i) g 0 else 0 := by
  have hfun : ((mulTemperateCLM hgt (jetTest i) : SchwartzMap ℝ ℂ) : ℝ → ℂ)
      = fun x : ℝ => g x * (jetTest i : ℝ → ℂ) x := by
    funext x
    rw [mulTemperateCLM_apply]
    ring
  rw [hfun, iteratedDeriv_mul_jetTest_zero hg]

/-- **The Gamma frequency equation excludes point-supported solutions.** -/
theorem eq_zero_of_pointSupport_gammaForm {u : SchwartzMap ℝ ℂ →L[ℂ] X} {g : ℝ → ℂ}
    (hgt : Function.HasTemperateGrowth g) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hg0 : g 0 = 0)
    (T : X →L[ℂ] X)
    (hu : ∀ ψ : SchwartzMap ℝ ℂ, (∃ δ > 0, ∀ x : ℝ, |x| ≤ δ → (ψ : ℝ → ℂ) x = 0) → u ψ = 0)
    (hEq : ∀ φ : SchwartzMap ℝ ℂ,
      u φ + (2 : ℂ) • u (coordMulCLM (SchwartzMap.derivCLM ℂ ℂ φ))
        + I • u (mulTemperateCLM hgt φ) - I • T (u (coordMulCLM φ)) = 0) :
    ∀ φ : SchwartzMap ℝ ℂ, u φ = 0 := by
  obtain ⟨N, c, hrep⟩ := exists_delta_representation u hu
  -- the coordinate is itself a multiplier vanishing at the origin
  have hidgt : Function.HasTemperateGrowth (fun x : ℝ => (x : ℂ)) :=
    Complex.ofRealCLM.hasTemperateGrowth
  have hidc : ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ => (x : ℂ)) := Complex.ofRealCLM.contDiff
  have hcoordFun : ∀ (φ : SchwartzMap ℝ ℂ),
      ((coordMulCLM φ : SchwartzMap ℝ ℂ) : ℝ → ℂ)
        = ((mulTemperateCLM hidgt φ : SchwartzMap ℝ ℂ) : ℝ → ℂ) := fun φ => rfl
  have hcoordJet : ∀ i j : ℕ,
      iteratedDeriv j ((coordMulCLM (jetTest i) : SchwartzMap ℝ ℂ) : ℝ → ℂ) 0
        = if i ≤ j then (j.choose (j - i) : ℂ)
            * iteratedDeriv (j - i) (fun x : ℝ => (x : ℂ)) 0 else 0 := by
    intro i j
    rw [hcoordFun, iteratedDeriv_mulTemperate_jetTest hidgt hidc]
  -- the coefficients of the two upper-triangular terms
  set α : ℕ → ℕ → ℂ := fun i j =>
    if i ≤ j then (j.choose (j - i) : ℂ) * iteratedDeriv (j - i) g 0 else 0 with hα
  set β : ℕ → ℕ → ℂ := fun i j =>
    if i ≤ j then (j.choose (j - i) : ℂ)
      * iteratedDeriv (j - i) (fun x : ℝ => (x : ℂ)) 0 else 0 with hβ
  have hαdiag : ∀ i, α i i = 0 := by
    intro i
    rw [hα]
    simp [hg0, iteratedDeriv_zero]
  have hβdiag : ∀ i, β i i = 0 := by
    intro i
    rw [hβ]
    simp [iteratedDeriv_zero]
  -- the triangular system
  have hsystem : ∀ i, i ≤ N → ((2 * i + 1 : ℂ)) • c i
      = ∑ j ∈ Finset.range (N+1),
        if i < j then (-(I * α i j)) • c j + (I * β i j) • T (c j) else 0 := by
    intro i hi
    have hmem : i ∈ Finset.range (N+1) := Finset.mem_range.mpr (by omega)
    have hu1 : u (jetTest i) = c i := by
      rw [hrep]
      have hcongr : ∀ j ∈ Finset.range (N+1),
          (iteratedDeriv j (jetTest i : ℝ → ℂ) 0) • c j = if j = i then c j else 0 := by
        intro j _
        rw [iteratedDeriv_jetTest_zero]
        by_cases h : j = i
        · rw [if_pos h, if_pos h, one_smul]
        · rw [if_neg h, if_neg h, zero_smul]
      rw [Finset.sum_congr rfl hcongr, Finset.sum_ite_eq' (Finset.range (N+1)) i c, if_pos hmem]
    have hu2 : u (coordMulCLM (SchwartzMap.derivCLM ℂ ℂ (jetTest i))) = (i : ℂ) • c i := by
      rw [hrep]
      have hcongr : ∀ j ∈ Finset.range (N+1),
          (iteratedDeriv j ((coordMulCLM (SchwartzMap.derivCLM ℂ ℂ (jetTest i)) :
              SchwartzMap ℝ ℂ) : ℝ → ℂ) 0) • c j = if j = i then (i : ℂ) • c i else 0 := by
        intro j _
        rw [iteratedDeriv_coordMul_deriv_zero, iteratedDeriv_jetTest_zero]
        by_cases h : j = i
        · rw [if_pos h, if_pos h, h, mul_one]
        · rw [if_neg h, if_neg h, mul_zero, zero_smul]
      rw [Finset.sum_congr rfl hcongr,
        Finset.sum_ite_eq' (Finset.range (N+1)) i (fun _ => (i : ℂ) • c i), if_pos hmem]
    have hu3 : u (mulTemperateCLM hgt (jetTest i)) = ∑ j ∈ Finset.range (N+1), (α i j) • c j := by
      rw [hrep]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [iteratedDeriv_mulTemperate_jetTest hgt hg, hα]
    have hu4 : u (coordMulCLM (jetTest i)) = ∑ j ∈ Finset.range (N+1), (β i j) • c j := by
      rw [hrep]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hcoordJet, hβ]
    have h := hEq (jetTest i)
    rw [hu1, hu2, hu3, hu4] at h
    -- rearrange into the triangular form
    have hTsum : T (∑ j ∈ Finset.range (N+1), (β i j) • c j)
        = ∑ j ∈ Finset.range (N+1), (β i j) • T (c j) := by
      rw [map_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [map_smul]
    rw [hTsum] at h
    have hsmul1 : I • (∑ j ∈ Finset.range (N+1), (α i j) • c j)
        = ∑ j ∈ Finset.range (N+1), (I * α i j) • c j := by
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [smul_smul]
    have hsmul2 : I • (∑ j ∈ Finset.range (N+1), (β i j) • T (c j))
        = ∑ j ∈ Finset.range (N+1), (I * β i j) • T (c j) := by
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [smul_smul]
    rw [hsmul1, hsmul2] at h
    have hsplit : ∑ j ∈ Finset.range (N+1),
        (if i < j then (-(I * α i j)) • c j + (I * β i j) • T (c j) else 0)
        = ∑ j ∈ Finset.range (N+1), ((-(I * α i j)) • c j + (I * β i j) • T (c j)) := by
      refine Finset.sum_congr rfl fun j hj => ?_
      have hjN : j ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      by_cases hlt : i < j
      · rw [if_pos hlt]
      · rw [if_neg hlt]
        have hji : j ≤ i := by omega
        by_cases hji' : j = i
        · subst hji'
          rw [hαdiag j, hβdiag j]
          simp
        · have hnle : ¬ (i ≤ j) := by omega
          simp [hα, hβ, hnle]
    rw [hsplit, Finset.sum_add_distrib]
    have hneg : ∑ j ∈ Finset.range (N+1), (-(I * α i j)) • c j
        = -∑ j ∈ Finset.range (N+1), (I * α i j) • c j := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun j _ => by rw [neg_smul]
    rw [hneg]
    have hci : ((2 * i + 1 : ℂ)) • c i = c i + (2 : ℂ) • ((i : ℂ) • c i) := by
      module
    rw [hci]
    linear_combination (norm := module) h
  have hzero := coeff_eq_zero_of_triangular_map
    (A := fun i j x => (-(I * α i j)) • x + (I * β i j) • T x)
    (fun i j => by simp) hsystem
  intro φ
  rw [hrep]
  refine Finset.sum_eq_zero fun j hj => ?_
  rw [hzero j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)), smul_zero]

end

end GaloisForLFunctions.HTGeometry
