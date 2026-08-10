import GaloisForLFunctions.HTGeometry.AbelianZetaGas.Normalization

/-!
# The depth ladder telescopes

Shifting the socle parameter by one temperature, `τ ↦ τ + σ`, moves depth `j` to depth `j + 1`.
The complete zeta ladder therefore telescopes: the partition function of the shifted parameters is
the original one divided by the single factor `ζ(σ + τ)`.  This is (GAS.7), the depth-fan origin of
the translation-divisor law of `ULF-EQG-1`.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

namespace AbelianZetaConvergentParameters

/-- The socle tilt `τ ↦ τ + σ` inside the convergence chamber. -/
def depthShift (θ : AbelianZetaConvergentParameters) : AbelianZetaConvergentParameters where
  sigma := θ.sigma
  tau := θ.tau + θ.sigma
  sigma_pos := θ.sigma_pos
  tau_nonneg := by
    have := θ.tau_nonneg
    have := θ.sigma_pos
    linarith
  firstDepth := by
    have := θ.firstDepth
    have := θ.sigma_pos
    linarith

@[simp] theorem depthShift_sigma (θ : AbelianZetaConvergentParameters) :
    θ.depthShift.sigma = θ.sigma := rfl

@[simp] theorem depthShift_tau (θ : AbelianZetaConvergentParameters) :
    θ.depthShift.tau = θ.tau + θ.sigma := rfl

end AbelianZetaConvergentParameters

/-- `ℕ` enumerates the nonzero naturals. -/
def natComplZeroEquiv : ℕ ≃ (({0} : Set ℕ)ᶜ : Set ℕ) where
  toFun n := ⟨n + 1, by simp⟩
  invFun x := x.1 - 1
  left_inv n := by simp
  right_inv x := by
    refine Subtype.ext ?_
    have hx : (x : ℕ) ≠ 0 := x.2
    show (x : ℕ) - 1 + 1 = (x : ℕ)
    omega

/-- **(GAS.7).**  The depth ladder telescopes: the socle tilt `τ ↦ τ + σ` divides the partition
function by exactly one zeta factor. -/
theorem zetaPartition_depthShift (θ : AbelianZetaConvergentParameters) :
    θ.zetaPartition
      = riemannZeta (((θ.sigma + θ.tau : ℝ) : ℂ)) * θ.depthShift.zetaPartition := by
  classical
  set f : ℕ → ℂ := fun n =>
    riemannZeta ((((n + 1 : ℕ) : ℝ) * θ.sigma + θ.tau : ℝ) : ℂ) with hf
  have hP : HasProd f θ.zetaPartition := θ.hasProd_zetaLadder_zetaPartition
  have hP' : HasProd (fun n : ℕ =>
      riemannZeta ((((n + 1 : ℕ) : ℝ) * θ.depthShift.sigma + θ.depthShift.tau : ℝ) : ℂ))
      θ.depthShift.zetaPartition := θ.depthShift.hasProd_zetaLadder_zetaPartition
  -- the shifted ladder is the tail of the original one
  have hshift : (fun n : ℕ =>
      riemannZeta ((((n + 1 : ℕ) : ℝ) * θ.depthShift.sigma + θ.depthShift.tau : ℝ) : ℂ))
      = fun n : ℕ => f (n + 1) := by
    funext n
    rw [hf]
    congr 2
    simp only [AbelianZetaConvergentParameters.depthShift_sigma,
      AbelianZetaConvergentParameters.depthShift_tau]
    push_cast
    ring
  rw [hshift] at hP'
  -- the head factor
  have hhead : HasProd (f ∘ (Subtype.val : ({0} : Set ℕ) → ℕ)) (f 0) := by
    have h := hasProd_fintype (f ∘ (Subtype.val : ({0} : Set ℕ) → ℕ))
    have hval : (∏ i : ({0} : Set ℕ), (f ∘ (Subtype.val : ({0} : Set ℕ) → ℕ)) i) = f 0 := by
      simp
    rwa [hval] at h
  -- the tail factor
  have htail : HasProd (f ∘ (Subtype.val : (({0} : Set ℕ)ᶜ : Set ℕ) → ℕ))
      θ.depthShift.zetaPartition := by
    refine (natComplZeroEquiv.hasProd_iff).mp ?_
    exact hP'
  have hcomb := hhead.mul_compl htail
  have huniq := hP.unique hcomb
  have hf0 : f 0 = riemannZeta (((θ.sigma + θ.tau : ℝ) : ℂ)) := by
    rw [hf]
    norm_num
  rw [huniq, hf0]

end

end GaloisForLFunctions.HTGeometry
