import GaloisForLFunctions.HTGeometry.NevanlinnaEntire
import GaloisForLFunctions.HTGeometry.MinimalTypeNoArithmeticProgression

/-!
# Minimal exponential type of the Nevanlinna entries, reduced to the kernel roots

Each entry is `±1` plus `h₀·z` times a weighted bilinear series, and Cauchy–Schwarz bounds that
series by a product of two kernel roots.  So a growth hypothesis on the kernel roots alone —

`∀ A > 0, ∃ C ≥ 1, ∀ z n, kernelRoot s (monicOrthoC s · z) n ≤ C·exp (A‖z‖)`, and the same for
`secondKindC` —

upgrades to minimal exponential type for all four entries: the extra factor `‖z‖` is absorbed by
`x ≤ exp x` applied at half the exponent.

This isolates M. Riesz's theorem as the single remaining analytic input: the entries of a
Nevanlinna matrix have minimal exponential type exactly because their kernel roots do.
-/

open scoped BigOperators

namespace HTGeometry

variable {s : ℕ → ℝ}

/-! ## Size bounds for the two entries carrying an additive constant -/

/-- **Size bound for the `B` entry.** -/
theorem norm_nevBinf_le (h : PositiveMomentForm s) (z : ℂ) {S0 P0 : ℝ}
    (hSz : ∀ n, kernelRoot s (fun j => monicOrthoC s j z) n ≤ S0)
    (hP0 : ∀ n, kernelRoot s (fun j => secondKindC s j 0) n ≤ P0) :
    ‖nevBinf s z‖
      ≤ 1 + momentInner s (monicOrtho s 0) (monicOrtho s 0) * ‖z‖ * (S0 * P0) := by
  have h0pos : 0 < momentInner s (monicOrtho s 0) (monicOrtho s 0) :=
    monicOrtho_inner_self_pos h 0
  have hnormAux : ‖((momentInner s (monicOrtho s 0) (monicOrtho s 0) : ℝ) : ℂ)‖
      = momentInner s (monicOrtho s 0) (monicOrtho s 0) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos h0pos]
  rw [nevBinf]
  refine le_trans (norm_add_le _ _) ?_
  have hone : ‖(-1 : ℂ)‖ = 1 := by simp
  rw [hone, norm_mul, norm_mul, hnormAux]
  gcongr
  exact norm_tsum_weighted_le h _ _ hSz hP0

/-- **Size bound for the `C` entry.** -/
theorem norm_nevCinf_le (h : PositiveMomentForm s) (z : ℂ) {S0 Pz : ℝ}
    (hS0 : ∀ n, kernelRoot s (fun j => monicOrthoC s j 0) n ≤ S0)
    (hPz : ∀ n, kernelRoot s (fun j => secondKindC s j z) n ≤ Pz) :
    ‖nevCinf s z‖
      ≤ 1 + momentInner s (monicOrtho s 0) (monicOrtho s 0) * ‖z‖ * (S0 * Pz) := by
  have h0pos : 0 < momentInner s (monicOrtho s 0) (monicOrtho s 0) :=
    monicOrtho_inner_self_pos h 0
  have hnormAux : ‖((momentInner s (monicOrtho s 0) (monicOrtho s 0) : ℝ) : ℂ)‖
      = momentInner s (monicOrtho s 0) (monicOrtho s 0) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos h0pos]
  rw [nevCinf]
  refine le_trans (norm_add_le _ _) ?_
  have hone : ‖(1 : ℂ)‖ = 1 := by simp
  rw [hone, norm_mul, norm_mul, hnormAux]
  gcongr
  exact norm_tsum_weighted_le h _ _ hS0 hPz

/-! ## The kernel-root growth hypothesis -/

/-- Both kernel roots grow slower than every exponential, uniformly in the truncation. -/
def KernelMinimalExponentialType (s : ℕ → ℝ) : Prop :=
  ∀ A : ℝ, 0 < A → ∃ C : ℝ, 1 ≤ C ∧ ∀ (z : ℂ) (n : ℕ),
    kernelRoot s (fun j => monicOrthoC s j z) n ≤ C * Real.exp (A * ‖z‖) ∧
      kernelRoot s (fun j => secondKindC s j z) n ≤ C * Real.exp (A * ‖z‖)

/-- The elementary absorption of one linear factor into half an exponential. -/
theorem norm_mul_exp_half_le {A r : ℝ} (hA : 0 < A) (_hr : 0 ≤ r) :
    r * Real.exp (A / 2 * r) ≤ 2 / A * Real.exp (A * r) := by
  have hx : A / 2 * r ≤ Real.exp (A / 2 * r) := by
    have := Real.add_one_le_exp (A / 2 * r)
    linarith
  have h2A : (0 : ℝ) < 2 / A := by positivity
  have hmul := mul_le_mul_of_nonneg_left hx h2A.le
  have heq : 2 / A * (A / 2 * r) = r := by field_simp
  rw [heq] at hmul
  have hpos : 0 < Real.exp (A / 2 * r) := Real.exp_pos _
  calc
    r * Real.exp (A / 2 * r) ≤ (2 / A * Real.exp (A / 2 * r)) * Real.exp (A / 2 * r) :=
      mul_le_mul_of_nonneg_right hmul hpos.le
    _ = 2 / A * Real.exp (A / 2 * r + A / 2 * r) := by rw [Real.exp_add]; ring
    _ = 2 / A * Real.exp (A * r) := by congr 2; ring

/-- The shape of every entry bound: `1 + K·r·exp(A r/2)` is dominated by `C·exp(A r)`. -/
theorem entry_bound_absorb {A K r : ℝ} (hA : 0 < A) (hK : 0 ≤ K) (hr : 0 ≤ r) :
    1 + K * r * Real.exp (A / 2 * r) ≤ (1 + 2 / A * K) * Real.exp (A * r) := by
  have hone : (1 : ℝ) ≤ Real.exp (A * r) := by
    refine Real.one_le_exp ?_
    positivity
  have hmain : K * (r * Real.exp (A / 2 * r)) ≤ K * (2 / A * Real.exp (A * r)) :=
    mul_le_mul_of_nonneg_left (norm_mul_exp_half_le hA hr) hK
  nlinarith [Real.exp_pos (A * r)]

/-! ## The reduction -/

/-- **Minimal exponential type of `B`, from the kernel roots.** -/
theorem hasMinimalExponentialType_nevBinf (h : PositiveMomentForm s) (h0b : BoundedKernel s 0)
    (hker : KernelMinimalExponentialType s) :
    GaloisForLFunctions.HTGeometry.HasMinimalExponentialType (nevBinf s) := by
  refine ⟨(nevanlinna_entire_unimodular h h0b).2.1, fun A hA => ?_⟩
  obtain ⟨C, hC1, hCbound⟩ := hker (A / 2) (by linarith)
  have h0pos : 0 < momentInner s (monicOrtho s 0) (monicOrtho s 0) :=
    monicOrtho_inner_self_pos h 0
  have hC0 : 0 ≤ C := by linarith
  set K : ℝ := momentInner s (monicOrtho s 0) (monicOrtho s 0) * (C * C) with hK
  have hKnn : 0 ≤ K := by positivity
  have hCle : (1 : ℝ) ≤ 1 + 2 / A * K := by
    have : 0 ≤ 2 / A * K := by positivity
    linarith
  refine ⟨1 + 2 / A * K, hCle, fun z => ?_⟩
  have hP0 : ∀ n, kernelRoot s (fun j => secondKindC s j 0) n ≤ C := by
    intro n
    simpa using (hCbound 0 n).2
  have hSz : ∀ n, kernelRoot s (fun j => monicOrthoC s j z) n
      ≤ C * Real.exp (A / 2 * ‖z‖) := fun n => (hCbound z n).1
  have hbound := norm_nevBinf_le h z hSz hP0
  have hbound2 : ‖nevBinf s z‖ ≤ 1 + K * ‖z‖ * Real.exp (A / 2 * ‖z‖) := by
    refine le_trans hbound (le_of_eq ?_)
    rw [hK]; ring
  exact le_trans hbound2 (entry_bound_absorb hA hKnn (norm_nonneg z))

/-- **Minimal exponential type of `C`, from the kernel roots.** -/
theorem hasMinimalExponentialType_nevCinf (h : PositiveMomentForm s) (h0b : BoundedKernel s 0)
    (hker : KernelMinimalExponentialType s) :
    GaloisForLFunctions.HTGeometry.HasMinimalExponentialType (nevCinf s) := by
  refine ⟨(nevanlinna_entire_unimodular h h0b).2.2.1, fun A hA => ?_⟩
  obtain ⟨C, hC1, hCbound⟩ := hker (A / 2) (by linarith)
  have h0pos : 0 < momentInner s (monicOrtho s 0) (monicOrtho s 0) :=
    monicOrtho_inner_self_pos h 0
  have hC0 : 0 ≤ C := by linarith
  set K : ℝ := momentInner s (monicOrtho s 0) (monicOrtho s 0) * (C * C) with hK
  have hKnn : 0 ≤ K := by positivity
  have hCle : (1 : ℝ) ≤ 1 + 2 / A * K := by
    have : 0 ≤ 2 / A * K := by positivity
    linarith
  refine ⟨1 + 2 / A * K, hCle, fun z => ?_⟩
  have hS0 : ∀ n, kernelRoot s (fun j => monicOrthoC s j 0) n ≤ C := by
    intro n
    simpa using (hCbound 0 n).1
  have hPz : ∀ n, kernelRoot s (fun j => secondKindC s j z) n
      ≤ C * Real.exp (A / 2 * ‖z‖) := fun n => (hCbound z n).2
  have hbound := norm_nevCinf_le h z hS0 hPz
  have hbound2 : ‖nevCinf s z‖ ≤ 1 + K * ‖z‖ * Real.exp (A / 2 * ‖z‖) := by
    refine le_trans hbound (le_of_eq ?_)
    rw [hK]; ring
  exact le_trans hbound2 (entry_bound_absorb hA hKnn (norm_nonneg z))

/-- **Minimal exponential type of `A`, from the kernel roots.** -/
theorem hasMinimalExponentialType_nevAinf (h : PositiveMomentForm s) (h0b : BoundedKernel s 0)
    (hker : KernelMinimalExponentialType s) :
    GaloisForLFunctions.HTGeometry.HasMinimalExponentialType (nevAinf s) := by
  refine ⟨(nevanlinna_entire_unimodular h h0b).1, fun A hA => ?_⟩
  obtain ⟨C, hC1, hCbound⟩ := hker (A / 2) (by linarith)
  have h0pos : 0 < momentInner s (monicOrtho s 0) (monicOrtho s 0) :=
    monicOrtho_inner_self_pos h 0
  have hC0 : 0 ≤ C := by linarith
  set K : ℝ := momentInner s (monicOrtho s 0) (monicOrtho s 0) * (C * C) with hK
  have hKnn : 0 ≤ K := by positivity
  have hCle : (1 : ℝ) ≤ 1 + 2 / A * K := by
    have : 0 ≤ 2 / A * K := by positivity
    linarith
  refine ⟨1 + 2 / A * K, hCle, fun z => ?_⟩
  have hP0 : ∀ n, kernelRoot s (fun j => secondKindC s j 0) n ≤ C := by
    intro n
    simpa using (hCbound 0 n).2
  have hPz : ∀ n, kernelRoot s (fun j => secondKindC s j z) n
      ≤ C * Real.exp (A / 2 * ‖z‖) := fun n => (hCbound z n).2
  have hbound := norm_nevAinf_le h z hP0 hPz
  have hbound2 : ‖nevAinf s z‖ ≤ K * ‖z‖ * Real.exp (A / 2 * ‖z‖) := by
    refine le_trans hbound (le_of_eq ?_)
    rw [hK]; ring
  have habs := entry_bound_absorb (A := A) (K := K) (r := ‖z‖) hA hKnn (norm_nonneg z)
  linarith

/-- **Minimal exponential type of `D`, from the kernel roots.** -/
theorem hasMinimalExponentialType_nevDinf (h : PositiveMomentForm s) (h0b : BoundedKernel s 0)
    (hker : KernelMinimalExponentialType s) :
    GaloisForLFunctions.HTGeometry.HasMinimalExponentialType (nevDinf s) := by
  refine ⟨(nevanlinna_entire_unimodular h h0b).2.2.2.1, fun A hA => ?_⟩
  obtain ⟨C, hC1, hCbound⟩ := hker (A / 2) (by linarith)
  have h0pos : 0 < momentInner s (monicOrtho s 0) (monicOrtho s 0) :=
    monicOrtho_inner_self_pos h 0
  have hC0 : 0 ≤ C := by linarith
  set K : ℝ := momentInner s (monicOrtho s 0) (monicOrtho s 0) * (C * C) with hK
  have hKnn : 0 ≤ K := by positivity
  have hCle : (1 : ℝ) ≤ 1 + 2 / A * K := by
    have : 0 ≤ 2 / A * K := by positivity
    linarith
  refine ⟨1 + 2 / A * K, hCle, fun z => ?_⟩
  have hS0 : ∀ n, kernelRoot s (fun j => monicOrthoC s j 0) n ≤ C := by
    intro n
    simpa using (hCbound 0 n).1
  have hSz : ∀ n, kernelRoot s (fun j => monicOrthoC s j z) n
      ≤ C * Real.exp (A / 2 * ‖z‖) := fun n => (hCbound z n).1
  have hbound := norm_nevDinf_le h z hS0 hSz
  have hbound2 : ‖nevDinf s z‖ ≤ K * ‖z‖ * Real.exp (A / 2 * ‖z‖) := by
    refine le_trans hbound (le_of_eq ?_)
    rw [hK]; ring
  have habs := entry_bound_absorb (A := A) (K := K) (r := ‖z‖) hA hKnn (norm_nonneg z)
  linarith

end HTGeometry
