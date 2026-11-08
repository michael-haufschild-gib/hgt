import GaloisForLFunctions.HeightHomotopyArithmeticCounts.KernelHilbertCompletion

/-!
# Arithmetic conductor atoms in the weighted Hilbert carrier

Normalized Hilbert basis vectors carry inverse square-root conductor weights.
Rescaling them gives unit arithmetic coefficients at a single conductor.
Their exact Gram entries recover the original kernel, without a limiting argument.
-/

noncomputable section
namespace GaloisForLFunctions.HeightHomotopyArithmeticCounts

/-- The normalized conductor basis of the weighted Hilbert carrier. -/
def weightedProbeBasis (δ : ℝ) : HilbertBasis ℕ ℝ (WeightedProbe δ) :=
  HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℝ _)

theorem weightedProbeBasis_apply (δ : ℝ) (n : ℕ) :
    weightedProbeBasis δ n = lp.single 2 n (1:ℝ) := by
  have h := (weightedProbeBasis δ).repr_self n
  simpa [weightedProbeBasis] using h

/-- A normalized basis vector has the inverse square-root conductor weight as its coefficient. -/
theorem probeCoefficients_normalizedAtom (δ : ℝ) (n m : ℕ) :
    probeCoefficients δ (lp.single 2 n (1:ℝ)) m =
      if m=n+1 then ((n+1:ℕ):ℝ)^(-δ/2) else 0 := by
  cases m with
  | zero => rw [probeCoefficients_zero,if_neg ((by omega : 0≠n+1))]
  | succ m =>
    rw [probeCoefficients_succ]
    simp only [lp.single_apply,Pi.single_apply]
    by_cases h : m=n
    · subst m
      simp only [ite_true,one_mul]
    · have hh : m+1≠n+1 := by omega
      simp only [if_neg h,if_neg hh,zero_mul]

/-- Normalized conductor atoms read the kernel with its two square-root weights. -/
theorem weightedKernelPairing_normalizedAtoms (δ : ℝ) (K : ℕ → ℕ → ℝ) (m n : ℕ) :
    weightedKernelPairing δ K (lp.single 2 m (1:ℝ)) (lp.single 2 n (1:ℝ)) =
      ((m+1:ℕ):ℝ)^(-δ/2)*((n+1:ℕ):ℝ)^(-δ/2)*K (m+1) (n+1) := by
  unfold weightedKernelPairing
  simp_rw [probeCoefficients_normalizedAtom]
  rw [tsum_eq_single (m+1,n+1)]
  · simp only [ite_true]
  · rintro ⟨a,b⟩ hab
    by_cases ha : a=m+1
    · have hb : b≠n+1 := fun hb => hab (Prod.ext ha hb)
      simp only [if_neg hb,mul_zero,zero_mul]
    · simp only [if_neg ha,zero_mul]

/-- A unit arithmetic coefficient at one positive conductor, in normalized Hilbert coordinates. -/
def weightedConductorAtom (δ : ℝ) (n : ℕ+) : WeightedProbe δ :=
  (n.val : ℝ)^(δ/2) • lp.single 2 (n.val-1) (1:ℝ)

/-- A conductor atom has exactly one original arithmetic coefficient. -/
theorem probeCoefficients_conductorAtom (δ : ℝ) (n : ℕ+) (m : ℕ) :
    probeCoefficients δ (weightedConductorAtom δ n) m = if m=n.val then 1 else 0 := by
  cases m with
  | zero =>
    rw [probeCoefficients_zero,if_neg (Nat.ne_of_lt n.pos)]
  | succ m =>
    rw [probeCoefficients_succ]
    simp only [weightedConductorAtom,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,
      lp.single_apply,Pi.single_apply]
    by_cases h : m+1=n.val
    · have hm : m=n.val-1 := by omega
      rw [if_pos hm,if_pos h,mul_one,h]
      rw [← Real.rpow_add (show (0:ℝ)<n.val by exact_mod_cast n.pos),
        show δ/2 + -δ/2=0 by ring,Real.rpow_zero]
    · have hm : m≠n.val-1 := by have hn := n.pos; omega
      rw [if_neg hm,if_neg h,mul_zero,zero_mul]

/-- The original arithmetic kernel is the exact Gram matrix on conductor atoms. -/
theorem weightedKernelPairing_conductorAtoms (δ : ℝ) (K : ℕ → ℕ → ℝ) (m n : ℕ+) :
    weightedKernelPairing δ K (weightedConductorAtom δ m) (weightedConductorAtom δ n) =
      K m.val n.val := by
  unfold weightedKernelPairing
  simp_rw [probeCoefficients_conductorAtom]
  rw [tsum_eq_single (m.val,n.val)]
  · simp only [ite_true,one_mul]
  · rintro ⟨a,b⟩ hab
    by_cases ha : a=m.val
    · have hb : b≠n.val := fun hb => hab (Prod.ext ha hb)
      simp only [if_neg hb,mul_zero,zero_mul]
    · simp only [if_neg ha,zero_mul]

#print axioms weightedProbeBasis_apply
#print axioms weightedKernelPairing_normalizedAtoms
#print axioms probeCoefficients_conductorAtom
#print axioms weightedKernelPairing_conductorAtoms
end GaloisForLFunctions.HeightHomotopyArithmeticCounts
