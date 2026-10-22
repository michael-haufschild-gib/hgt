import GaloisForLFunctions.RHTower.Deninger.DeningerRadialEulerData
import GaloisForLFunctions.RHTower.Deninger.DeningerFourierWeight

/-!
# The Poisson operator is a strict morphism

Every Schwartz seminorm of a member of Meyer's space is bounded by finitely many seminorms of the
radial datum of its Poisson sum.  The two regions are covered by different mechanisms:

* near the origin by the Fourier side — the derivative supremum `p_{0,n}(f)` is controlled by the
  weighted suprema of `𝓕f`, whose radial datum is the reflected radial datum of `f`;
* away from the origin by the dilation side — the weighted derivative `x^n f^{(n)}` is a
  combination of Euler iterates `θ^j f`, whose radial data are derivatives of the radial datum
  of `f`.

Together with the continuity of the Poisson operator this says that `Z : ℋ_∩ → ℋ_−` is a strict
morphism: it is a homeomorphism onto its image.

* `deningerRadialData` : the finite radial data of a Poisson sum.
* `exists_bound_seminorm_radial` : **every Schwartz seminorm of `f` is bounded by radial data.**
* `deningerPoissonLM_strict` : **the Poisson operator is a strict morphism.**
-/

open scoped Real SchwartzMap FourierTransform ContDiff NNReal
open Complex MeasureTheory GaloisForLFunctions

noncomputable section

namespace RHTower

/-! ## Finite radial data -/

/-- The finite radial datum of a Poisson sum: a finite sup of Schwartz seminorms, summed over
finitely many weight indices. -/
def deningerRadialData (S : Finset ℤ) (K : Finset (ℕ × ℕ)) (f : 𝓢(ℝ, ℂ))
    (hf : f ∈ DeningerMeyerCap) : ℝ :=
  ∑ s ∈ S, (K.sup (schwartzSeminormFamily ℂ ℝ ℂ)) (deningerPoissonSchwartz s f hf)

theorem deningerRadialData_nonneg (S : Finset ℤ) (K : Finset (ℕ × ℕ)) (f : 𝓢(ℝ, ℂ))
    (hf : f ∈ DeningerMeyerCap) : 0 ≤ deningerRadialData S K f hf :=
  Finset.sum_nonneg fun _ _ => apply_nonneg _ _

theorem deningerRadialData_mono {S S' : Finset ℤ} {K K' : Finset (ℕ × ℕ)} (hS : S ⊆ S')
    (hK : K ⊆ K') (f : 𝓢(ℝ, ℂ)) (hf : f ∈ DeningerMeyerCap) :
    deningerRadialData S K f hf ≤ deningerRadialData S' K' f hf := by
  have hsup : K.sup (schwartzSeminormFamily ℂ ℝ ℂ) ≤ K'.sup (schwartzSeminormFamily ℂ ℝ ℂ) :=
    Finset.sup_mono hK
  refine le_trans (Finset.sum_le_sum fun s _ => hsup (deningerPoissonSchwartz s f hf)) ?_
  exact Finset.sum_le_sum_of_subset_of_nonneg hS fun _ _ _ => apply_nonneg _ _

theorem le_deningerRadialData {S : Finset ℤ} {K : Finset (ℕ × ℕ)} {s : ℤ} (hs : s ∈ S)
    (f : 𝓢(ℝ, ℂ)) (hf : f ∈ DeningerMeyerCap) :
    (K.sup (schwartzSeminormFamily ℂ ℝ ℂ)) (deningerPoissonSchwartz s f hf)
      ≤ deningerRadialData S K f hf :=
  Finset.single_le_sum (f := fun s => (K.sup (schwartzSeminormFamily ℂ ℝ ℂ))
    (deningerPoissonSchwartz s f hf)) (fun _ _ => apply_nonneg _ _) hs

/-! ## The derivative seminorms -/

/-- **The derivative suprema are bounded by radial data**, through the Fourier side. -/
theorem exists_bound_seminorm_zero_deriv_radial (n : ℕ) :
    ∃ (S : Finset ℤ) (K : Finset (ℕ × ℕ)) (C : ℝ), 0 ≤ C ∧
      ∀ (f : 𝓢(ℝ, ℂ)) (hf : f ∈ DeningerMeyerCap),
        SchwartzMap.seminorm ℂ 0 n f ≤ C * deningerRadialData S K f hf := by
  classical
  have hpi : (0 : ℝ) < π := Real.pi_pos
  obtain ⟨K₁, C₁, hC₁, hb₁⟩ := exists_bound_seminorm_zero_fourier n
  obtain ⟨K₂, C₂, hC₂, hb₂⟩ := exists_bound_seminorm_zero_fourier (n + 2)
  refine ⟨{1 - ((n : ℤ) + 2), 1 - (((n + 2 : ℕ) : ℤ) + 2), 2}, K₁ ∪ K₂,
    (2 * π) ^ n * π * (2 * C₁ + 2 * C₂), by positivity, fun f hf => ?_⟩
  set S : Finset ℤ := {1 - ((n : ℤ) + 2), 1 - (((n + 2 : ℕ) : ℤ) + 2), 2} with hS
  set K : Finset (ℕ × ℕ) := K₁ ∪ K₂ with hK
  set R : ℝ := deningerRadialData S K f hf with hR
  have hRnn : 0 ≤ R := deningerRadialData_nonneg _ _ _ _
  have hmem₁ : (1 - ((n : ℤ) + 2)) ∈ S := by
    rw [hS]
    exact Finset.mem_insert_self _ _
  have hmem₂ : (1 - (((n + 2 : ℕ) : ℤ) + 2)) ∈ S := by
    rw [hS]
    simp
  have hmem₃ : (2 : ℤ) ∈ S := by
    rw [hS]
    simp
  have hsup₁ : K₁.sup (schwartzSeminormFamily ℂ ℝ ℂ) ≤ K.sup (schwartzSeminormFamily ℂ ℝ ℂ) :=
    Finset.sup_mono Finset.subset_union_left
  have hsup₂ : K₂.sup (schwartzSeminormFamily ℂ ℝ ℂ) ≤ K.sup (schwartzSeminormFamily ℂ ℝ ℂ) :=
    Finset.sup_mono Finset.subset_union_right
  have hterm₁ : SchwartzMap.seminorm ℂ n 0 (fourierSCLM f) ≤ C₁ * (2 * R) := by
    refine le_trans (hb₁ f hf) ?_
    refine mul_le_mul_of_nonneg_left ?_ hC₁
    have ha := le_trans (hsup₁ (deningerPoissonSchwartz (1 - ((n : ℤ) + 2)) f hf))
      (le_deningerRadialData hmem₁ f hf)
    have hb := le_trans (hsup₁ (deningerPoissonSchwartz 2 f hf))
      (le_deningerRadialData hmem₃ f hf)
    linarith
  have hterm₂ : SchwartzMap.seminorm ℂ (n + 2) 0 (fourierSCLM f) ≤ C₂ * (2 * R) := by
    refine le_trans (hb₂ f hf) ?_
    refine mul_le_mul_of_nonneg_left ?_ hC₂
    have ha := le_trans (hsup₂ (deningerPoissonSchwartz (1 - (((n + 2 : ℕ) : ℤ) + 2)) f hf))
      (le_deningerRadialData hmem₂ f hf)
    have hb := le_trans (hsup₂ (deningerPoissonSchwartz 2 f hf))
      (le_deningerRadialData hmem₃ f hf)
    linarith
  calc SchwartzMap.seminorm ℂ 0 n f
      ≤ (2 * π) ^ n * π * (SchwartzMap.seminorm ℂ n 0 (fourierSCLM f)
          + SchwartzMap.seminorm ℂ (n + 2) 0 (fourierSCLM f)) :=
        seminorm_zero_deriv_le_fourier n f
    _ ≤ (2 * π) ^ n * π * (C₁ * (2 * R) + C₂ * (2 * R)) := by
        refine mul_le_mul_of_nonneg_left (add_le_add hterm₁ hterm₂) (by positivity)
    _ = (2 * π) ^ n * π * (2 * C₁ + 2 * C₂) * R := by ring

/-! ## The Euler iterates -/

/-- **The supremum seminorms of the Euler iterates are bounded by radial data.** -/
theorem exists_bound_seminorm_zero_euler_radial (k j : ℕ) :
    ∃ (S : Finset ℤ) (K : Finset (ℕ × ℕ)) (C : ℝ), 0 ≤ C ∧
      ∀ (f : 𝓢(ℝ, ℂ)) (hf : f ∈ DeningerMeyerCap),
        SchwartzMap.seminorm ℂ k 0 ((eulerSCLM^[j]) f) ≤ C * deningerRadialData S K f hf := by
  classical
  obtain ⟨K₀, C₀, hC₀, hb₀⟩ := exists_bound_seminorm_zero k
  obtain ⟨K₁, C₁, hC₁, hb₁⟩ := exists_bound_schwartzSup_euler ((k : ℤ) + 2) j K₀
  obtain ⟨K₂, C₂, hC₂, hb₂⟩ := exists_bound_schwartzSup_euler (-1) j K₀
  refine ⟨{(k : ℤ) + 2, -1}, K₁ ∪ K₂, C₀ * (C₁ + C₂), by positivity, fun f hf => ?_⟩
  set S : Finset ℤ := {(k : ℤ) + 2, -1} with hS
  set K : Finset (ℕ × ℕ) := K₁ ∪ K₂ with hK
  set R : ℝ := deningerRadialData S K f hf with hR
  have hRnn : 0 ≤ R := deningerRadialData_nonneg _ _ _ _
  have hmem₁ : ((k : ℤ) + 2) ∈ S := by
    rw [hS]
    exact Finset.mem_insert_self _ _
  have hmem₂ : (-1 : ℤ) ∈ S := by
    rw [hS]
    simp
  have hsup₁ : K₁.sup (schwartzSeminormFamily ℂ ℝ ℂ) ≤ K.sup (schwartzSeminormFamily ℂ ℝ ℂ) :=
    Finset.sup_mono Finset.subset_union_left
  have hsup₂ : K₂.sup (schwartzSeminormFamily ℂ ℝ ℂ) ≤ K.sup (schwartzSeminormFamily ℂ ℝ ℂ) :=
    Finset.sup_mono Finset.subset_union_right
  have hEmem : ((eulerSCLM^[j]) f) ∈ DeningerMeyerCap := deningerMeyerCap_eulerSCLM_iterate hf j
  have hstep := hb₀ ((eulerSCLM^[j]) f) hEmem
  have hleft : (K₀.sup (schwartzSeminormFamily ℂ ℝ ℂ))
      (deningerPoissonSchwartz ((k : ℤ) + 2) ((eulerSCLM^[j]) f) hEmem) ≤ C₁ * R := by
    refine le_trans (hb₁ f hf) ?_
    refine mul_le_mul_of_nonneg_left ?_ hC₁
    exact le_trans (hsup₁ (deningerPoissonSchwartz ((k : ℤ) + 2) f hf))
      (le_deningerRadialData hmem₁ f hf)
  have hright : (K₀.sup (schwartzSeminormFamily ℂ ℝ ℂ))
      (deningerPoissonSchwartz (-1) ((eulerSCLM^[j]) f) hEmem) ≤ C₂ * R := by
    refine le_trans (hb₂ f hf) ?_
    refine mul_le_mul_of_nonneg_left ?_ hC₂
    exact le_trans (hsup₂ (deningerPoissonSchwartz (-1) f hf))
      (le_deningerRadialData hmem₂ f hf)
  calc SchwartzMap.seminorm ℂ k 0 ((eulerSCLM^[j]) f)
      ≤ C₀ * ((K₀.sup (schwartzSeminormFamily ℂ ℝ ℂ))
            (deningerPoissonSchwartz ((k : ℤ) + 2) ((eulerSCLM^[j]) f) hEmem)
          + (K₀.sup (schwartzSeminormFamily ℂ ℝ ℂ))
            (deningerPoissonSchwartz (-1) ((eulerSCLM^[j]) f) hEmem)) := hstep
    _ ≤ C₀ * (C₁ * R + C₂ * R) := mul_le_mul_of_nonneg_left (add_le_add hleft hright) hC₀
    _ = C₀ * (C₁ + C₂) * R := by ring

/-- A finite nonnegative combination of the Euler-iterate seminorms is bounded by radial data. -/
theorem exists_bound_sum_euler_radial (k : ℕ) (a : ℕ → ℝ) (m : ℕ) :
    ∃ (S : Finset ℤ) (K : Finset (ℕ × ℕ)) (C : ℝ), 0 ≤ C ∧
      ∀ (f : 𝓢(ℝ, ℂ)) (hf : f ∈ DeningerMeyerCap),
        (∑ j ∈ Finset.range m, ‖a j‖ * SchwartzMap.seminorm ℂ k 0 ((eulerSCLM^[j]) f))
          ≤ C * deningerRadialData S K f hf := by
  classical
  induction m with
  | zero =>
    refine ⟨∅, ∅, 0, le_refl 0, fun f hf => ?_⟩
    simp [deningerRadialData]
  | succ m ih =>
    obtain ⟨S, K, C, hC, hb⟩ := ih
    obtain ⟨S', K', C', hC', hb'⟩ := exists_bound_seminorm_zero_euler_radial k m
    refine ⟨S ∪ S', K ∪ K', C + ‖a m‖ * C', by positivity, fun f hf => ?_⟩
    set R : ℝ := deningerRadialData (S ∪ S') (K ∪ K') f hf with hR
    have hRnn : 0 ≤ R := deningerRadialData_nonneg _ _ _ _
    have hmono : deningerRadialData S K f hf ≤ R :=
      deningerRadialData_mono Finset.subset_union_left Finset.subset_union_left f hf
    have hmono' : deningerRadialData S' K' f hf ≤ R :=
      deningerRadialData_mono Finset.subset_union_right Finset.subset_union_right f hf
    have h1 : (∑ j ∈ Finset.range m, ‖a j‖ * SchwartzMap.seminorm ℂ k 0 ((eulerSCLM^[j]) f))
        ≤ C * R := le_trans (hb f hf) (mul_le_mul_of_nonneg_left hmono hC)
    have h2 : ‖a m‖ * SchwartzMap.seminorm ℂ k 0 ((eulerSCLM^[m]) f) ≤ ‖a m‖ * (C' * R) := by
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      exact le_trans (hb' f hf) (mul_le_mul_of_nonneg_left hmono' hC')
    rw [Finset.sum_range_succ]
    calc (∑ j ∈ Finset.range m, ‖a j‖ * SchwartzMap.seminorm ℂ k 0 ((eulerSCLM^[j]) f))
          + ‖a m‖ * SchwartzMap.seminorm ℂ k 0 ((eulerSCLM^[m]) f)
        ≤ C * R + ‖a m‖ * (C' * R) := add_le_add h1 h2
      _ = (C + ‖a m‖ * C') * R := by ring

/-! ## Every Schwartz seminorm is radial data -/

/-- **Every Schwartz seminorm of a member of Meyer's space is bounded by finitely many seminorms of
the radial datum of its Poisson sum.** -/
theorem exists_bound_seminorm_radial (k n : ℕ) :
    ∃ (S : Finset ℤ) (K : Finset (ℕ × ℕ)) (C : ℝ), 0 ≤ C ∧
      ∀ (f : 𝓢(ℝ, ℂ)) (hf : f ∈ DeningerMeyerCap),
        SchwartzMap.seminorm ℂ k n f ≤ C * deningerRadialData S K f hf := by
  classical
  obtain ⟨S₁, K₁, C₁, hC₁, hb₁⟩ := exists_bound_seminorm_zero_deriv_radial n
  obtain ⟨S₂, K₂, C₂, hC₂, hb₂⟩ :=
    exists_bound_sum_euler_radial k (fun j => ‖deningerStirling n j‖) (n + 1)
  refine ⟨S₁ ∪ S₂, K₁ ∪ K₂, C₁ + C₂, by positivity, fun f hf => ?_⟩
  set R : ℝ := deningerRadialData (S₁ ∪ S₂) (K₁ ∪ K₂) f hf with hR
  have hRnn : 0 ≤ R := deningerRadialData_nonneg _ _ _ _
  have hmono₁ : deningerRadialData S₁ K₁ f hf ≤ R :=
    deningerRadialData_mono Finset.subset_union_left Finset.subset_union_left f hf
  have hmono₂ : deningerRadialData S₂ K₂ f hf ≤ R :=
    deningerRadialData_mono Finset.subset_union_right Finset.subset_union_right f hf
  have hderiv : SchwartzMap.seminorm ℂ 0 n f ≤ C₁ * R :=
    le_trans (hb₁ f hf) (mul_le_mul_of_nonneg_left hmono₁ hC₁)
  have hsumcoe : (∑ j ∈ Finset.range (n + 1),
        ‖(fun j => ‖deningerStirling n j‖) j‖ * SchwartzMap.seminorm ℂ k 0 ((eulerSCLM^[j]) f))
      = ∑ j ∈ Finset.range (n + 1),
        ‖deningerStirling n j‖ * SchwartzMap.seminorm ℂ k 0 ((eulerSCLM^[j]) f) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  have hfar : SchwartzMap.seminorm ℂ k 0 (deningerWeightedDerivCLM n f) ≤ C₂ * R := by
    refine le_trans (seminorm_weightedDeriv_le_euler n k f) ?_
    have h := hb₂ f hf
    rw [hsumcoe] at h
    exact le_trans h (mul_le_mul_of_nonneg_left hmono₂ hC₂)
  calc SchwartzMap.seminorm ℂ k n f
      ≤ SchwartzMap.seminorm ℂ 0 n f
        + SchwartzMap.seminorm ℂ k 0 (deningerWeightedDerivCLM n f) :=
        seminorm_le_weightedDeriv k n f
    _ ≤ C₁ * R + C₂ * R := add_le_add hderiv hfar
    _ = (C₁ + C₂) * R := by ring

/-- Finite suprema of Schwartz seminorms are bounded by radial data. -/
theorem exists_bound_schwartzSup_radial (K₀ : Finset (ℕ × ℕ)) :
    ∃ (S : Finset ℤ) (K : Finset (ℕ × ℕ)) (C : ℝ), 0 ≤ C ∧
      ∀ (f : 𝓢(ℝ, ℂ)) (hf : f ∈ DeningerMeyerCap),
        (K₀.sup (schwartzSeminormFamily ℂ ℝ ℂ)) f ≤ C * deningerRadialData S K f hf := by
  classical
  induction K₀ using Finset.induction with
  | empty =>
    refine ⟨∅, ∅, 0, le_refl 0, fun f hf => ?_⟩
    simp [deningerRadialData]
  | insert a K₀ ha ih =>
    obtain ⟨S, K, C, hC, hb⟩ := ih
    obtain ⟨S', K', C', hC', hb'⟩ := exists_bound_seminorm_radial a.1 a.2
    refine ⟨S ∪ S', K ∪ K', C + C', by positivity, fun f hf => ?_⟩
    set R : ℝ := deningerRadialData (S ∪ S') (K ∪ K') f hf with hR
    have hRnn : 0 ≤ R := deningerRadialData_nonneg _ _ _ _
    have hmono : deningerRadialData S K f hf ≤ R :=
      deningerRadialData_mono Finset.subset_union_left Finset.subset_union_left f hf
    have hmono' : deningerRadialData S' K' f hf ≤ R :=
      deningerRadialData_mono Finset.subset_union_right Finset.subset_union_right f hf
    have h1 : (K₀.sup (schwartzSeminormFamily ℂ ℝ ℂ)) f ≤ C * R :=
      le_trans (hb f hf) (mul_le_mul_of_nonneg_left hmono hC)
    have h2 : (schwartzSeminormFamily ℂ ℝ ℂ a) f ≤ C' * R := by
      have hfam : (schwartzSeminormFamily ℂ ℝ ℂ a) f = SchwartzMap.seminorm ℂ a.1 a.2 f := rfl
      rw [hfam]
      exact le_trans (hb' f hf) (mul_le_mul_of_nonneg_left hmono' hC')
    rw [Finset.sup_insert, Seminorm.sup_apply]
    refine max_le ?_ ?_
    · calc (schwartzSeminormFamily ℂ ℝ ℂ a) f ≤ C' * R := h2
        _ ≤ (C + C') * R := by nlinarith
    · calc (K₀.sup (schwartzSeminormFamily ℂ ℝ ℂ)) f ≤ C * R := h1
        _ ≤ (C + C') * R := by nlinarith

/-! ## The strict morphism -/

/-- **The Poisson operator is a strict morphism**: every seminorm of Meyer's space is bounded by a
seminorm of the radial space evaluated at the image.  With the continuity of the operator this
says that `Z` is a homeomorphism onto its image. -/
theorem deningerPoissonLM_strict (K₀ : Finset (ℕ × ℕ)) :
    ∃ (i : Finset ℤ × (ℤ → ℕ)) (C : ℝ), 0 ≤ C ∧ ∀ f : DeningerMeyerCap,
      deningerRestrictSeminorm DeningerMeyerCap (K₀.sup (schwartzSeminormFamily ℂ ℝ ℂ)) f
        ≤ C * deningerRestrictSeminorm deningerRadialCompat
            (deningerPiFamily (fun _ : ℤ => (shiftedSeminorm : SeminormFamily ℂ 𝓢(ℝ, ℂ) ℕ)) i)
            (deningerPoissonLM f) := by
  classical
  obtain ⟨S, K, C, hC, hb⟩ := exists_bound_schwartzSup_radial K₀
  obtain ⟨m, C', hC', hb'⟩ := schwartzSup_le_shiftedSeminorm K
  refine ⟨(S, fun _ => m), C * C', by positivity, fun f => ?_⟩
  have hval : deningerRestrictSeminorm deningerRadialCompat
      (deningerPiFamily (fun _ : ℤ => (shiftedSeminorm : SeminormFamily ℂ 𝓢(ℝ, ℂ) ℕ))
        (S, fun _ => m)) (deningerPoissonLM f)
      = ∑ s ∈ S, shiftedSeminorm m (deningerPoissonSchwartz s (f : 𝓢(ℝ, ℂ)) f.2) := by
    rw [deningerRestrictSeminorm_apply, deningerPiFamily, deningerPiSeminorm_apply]
    rfl
  have hleft : deningerRestrictSeminorm DeningerMeyerCap
      (K₀.sup (schwartzSeminormFamily ℂ ℝ ℂ)) f
      = (K₀.sup (schwartzSeminormFamily ℂ ℝ ℂ)) (f : 𝓢(ℝ, ℂ)) := by
    rw [deningerRestrictSeminorm_apply]
  have hdata : deningerRadialData S K (f : 𝓢(ℝ, ℂ)) f.2
      ≤ C' * ∑ s ∈ S, shiftedSeminorm m (deningerPoissonSchwartz s (f : 𝓢(ℝ, ℂ)) f.2) := by
    rw [deningerRadialData, Finset.mul_sum]
    exact Finset.sum_le_sum fun s _ => hb' (deningerPoissonSchwartz s (f : 𝓢(ℝ, ℂ)) f.2)
  rw [hval, hleft]
  calc (K₀.sup (schwartzSeminormFamily ℂ ℝ ℂ)) (f : 𝓢(ℝ, ℂ))
      ≤ C * deningerRadialData S K (f : 𝓢(ℝ, ℂ)) f.2 := hb (f : 𝓢(ℝ, ℂ)) f.2
    _ ≤ C * (C' * ∑ s ∈ S, shiftedSeminorm m
          (deningerPoissonSchwartz s (f : 𝓢(ℝ, ℂ)) f.2)) :=
        mul_le_mul_of_nonneg_left hdata hC
    _ = C * C' * ∑ s ∈ S, shiftedSeminorm m
          (deningerPoissonSchwartz s (f : 𝓢(ℝ, ℂ)) f.2) := by ring

end RHTower

end
