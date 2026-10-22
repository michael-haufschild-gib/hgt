import GaloisForLFunctions.HTGeometry.FrequencyPropagator
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Classification of homogeneous Gamma solutions on a frequency half-line

On a positive frequency half-line the Gamma equation in logarithmic normal form reads

`f' = [-1/(2η) + (i/2)(r(η) I - T)] f`,

whose coefficient is the logarithmic derivative of `η^{-1/2}Q(η)` for the Gamma transport
`Q(η) = exp((i/2)∫₀^η r) exp(-iηT/2)`.  Consequently every solution is `η^{-1/2}Q(η)c` for a single
channel vector `c`, and the channel vector is unique.  The proof is the exact integrating factor:
`η^{1/2}Q(η)^{-1}f(η)` has vanishing derivative, so it is constant on the connected half-line.
-/

open Complex Set

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- The Gamma transport `Q(η) = exp((i/2)∫₀^η r) exp(-iηT/2)`, the zero-frequency propagator. -/
def gammaTransport (Rint : ℝ → ℝ) (T : X →L[ℂ] X) (η : ℝ) : X →L[ℂ] X :=
  freqPropagator 0 Rint T η

/-- The inverse Gamma transport. -/
def gammaTransportInv (Rint : ℝ → ℝ) (T : X →L[ℂ] X) (η : ℝ) : X →L[ℂ] X :=
  freqPropagator 0 (fun x => -Rint x) (-T) η

variable {Rint : ℝ → ℝ} {T : X →L[ℂ] X}

theorem gammaTransport_mul_inv (η : ℝ) :
    gammaTransport Rint T η * gammaTransportInv Rint T η = 1 := by
  letI : NormedAlgebra ℚ (X →L[ℂ] X) := .restrictScalars ℚ ℂ _
  rw [gammaTransport, gammaTransportInv, freqPropagator, freqPropagator, smul_mul_smul_comm]
  have hscal : gammaPhase 0 Rint η * gammaPhase 0 (fun x => -Rint x) η = 1 := by
    rw [gammaPhase, gammaPhase, ← Complex.exp_add]
    have h : ((η * 0 + Rint η / 2 : ℝ) : ℂ) * I + ((η * 0 + -Rint η / 2 : ℝ) : ℂ) * I = 0 := by
      push_cast; ring
    rw [h, Complex.exp_zero]
  have hop : opPhase T η * opPhase (-T) η = 1 := by
    have hneg : opPhase (-T) η = NormedSpace.exp (-(η • ((-I / 2 : ℂ) • T))) := by
      rw [opPhase, smul_neg, smul_neg]
    rw [opPhase, hneg, ← NormedSpace.exp_add_of_commute ((Commute.refl _).neg_right),
      add_neg_cancel, NormedSpace.exp_zero]
  rw [hscal, hop, one_smul]

theorem gammaTransportInv_mul (η : ℝ) :
    gammaTransportInv Rint T η * gammaTransport Rint T η = 1 := by
  letI : NormedAlgebra ℚ (X →L[ℂ] X) := .restrictScalars ℚ ℂ _
  rw [gammaTransport, gammaTransportInv, freqPropagator, freqPropagator, smul_mul_smul_comm]
  have hscal : gammaPhase 0 (fun x => -Rint x) η * gammaPhase 0 Rint η = 1 := by
    rw [gammaPhase, gammaPhase, ← Complex.exp_add]
    have h : ((η * 0 + -Rint η / 2 : ℝ) : ℂ) * I + ((η * 0 + Rint η / 2 : ℝ) : ℂ) * I = 0 := by
      push_cast; ring
    rw [h, Complex.exp_zero]
  have hop : opPhase (-T) η * opPhase T η = 1 := by
    have hneg : opPhase (-T) η = NormedSpace.exp (-(η • ((-I / 2 : ℂ) • T))) := by
      rw [opPhase, smul_neg, smul_neg]
    have hcomm : Commute (-(η • ((-I / 2 : ℂ) • T))) (η • ((-I / 2 : ℂ) • T)) :=
      (Commute.refl _).neg_left
    rw [hneg, opPhase, ← NormedSpace.exp_add_of_commute hcomm, neg_add_cancel,
      NormedSpace.exp_zero]
  rw [hscal, hop, one_smul]

@[simp] theorem gammaTransport_apply_inv_apply (η : ℝ) (v : X) :
    gammaTransport Rint T η (gammaTransportInv Rint T η v) = v := by
  have h := gammaTransport_mul_inv (Rint := Rint) (T := T) η
  have := congrArg (fun S : X →L[ℂ] X => S v) h
  simpa using this

omit [CompleteSpace X] in
/-- The transported symbol commutes with the inverse transport. -/
theorem commute_shiftedSymbolOp_gammaTransportInv (c : ℝ) (η : ℝ) :
    shiftedSymbolOp c T * gammaTransportInv Rint T η
      = gammaTransportInv Rint T η * shiftedSymbolOp c T := by
  have hT : Commute T (opPhase (-T) η) := by
    have h := (commute_opPhase (-T) η).neg_left
    rwa [neg_neg] at h
  have hB : Commute (shiftedSymbolOp c T) (opPhase (-T) η) := by
    rw [shiftedSymbolOp]
    exact ((Commute.one_left _).smul_left _).sub_left (hT.smul_left _)
  have hfull : Commute (shiftedSymbolOp c T) (gammaTransportInv Rint T η) := by
    rw [gammaTransportInv, freqPropagator]
    exact hB.smul_right _
  exact hfull

/-- The inverse transport solves the adjoint transport equation. -/
theorem hasDerivAt_gammaTransportInv {r : ℝ → ℝ} {η : ℝ} (hRint : HasDerivAt Rint (r η) η) :
    HasDerivAt (gammaTransportInv Rint T)
      (-(I • (shiftedSymbolOp (r η / 2) T * gammaTransportInv Rint T η))) η := by
  have h := hasDerivAt_freqPropagator (L := 0) (Rint := fun x => -Rint x) (r := fun x => -r x)
    (η := η) (-T) hRint.neg
  have hop : shiftedSymbolOp (0 + -r η / 2) (-T) = -shiftedSymbolOp (r η / 2) T := by
    rw [shiftedSymbolOp, shiftedSymbolOp, zero_add, smul_neg, sub_neg_eq_add, neg_sub]
    have hc : (((-r η / 2 : ℝ)) : ℂ) = -(((r η / 2 : ℝ)) : ℂ) := by push_cast; ring
    rw [hc, neg_smul]
    abel
  rw [hop] at h
  have hval : I • (-shiftedSymbolOp (r η / 2) T * freqPropagator 0 (fun x => -Rint x) (-T) η)
      = -(I • (shiftedSymbolOp (r η / 2) T
          * freqPropagator 0 (fun x => -Rint x) (-T) η)) := by
    rw [neg_mul, smul_neg]
  rw [hval] at h
  exact h

omit [CompleteSpace X] in
/-- The product rule for an operator-valued factor acting on a vector-valued factor, with the
operator complex linear and the parameter real. -/
theorem hasDerivAt_clm_apply {Q : ℝ → (X →L[ℂ] X)} {Q' : X →L[ℂ] X} {u : ℝ → X} {u' : X} {η : ℝ}
    (hQ : HasDerivAt Q Q' η) (hu : HasDerivAt u u' η) :
    HasDerivAt (fun y => Q y (u y)) (Q' (u η) + Q η u') η := by
  have hΨ := (ContinuousLinearMap.restrictScalarsL ℂ X X ℝ ℝ).hasFDerivAt.comp_hasDerivAt η hQ
  exact hΨ.clm_apply hu

omit [CompleteSpace X] in
theorem ofReal_smul_eq (c : ℝ) (x : X) : ((c : ℂ)) • x = c • x := by
  rw [← Complex.coe_algebraMap, algebraMap_smul]

omit [CompleteSpace X] in
theorem map_real_smul (S : X →L[ℂ] X) (c : ℝ) (x : X) : S (c • x) = c • S x := by
  rw [← ofReal_smul_eq, map_smul, ofReal_smul_eq]

/-- **The half-line classification.**  A solution of the Gamma equation in logarithmic normal form
on the positive frequency half-line is `η^{-1/2}Q(η)c` for a channel vector `c`; the vector is the
constant value of the exact integrating factor `η^{1/2}Q(η)^{-1}f(η)`. -/
theorem exists_channel_vector {r : ℝ → ℝ} {f f' : ℝ → X}
    (hRint : ∀ η : ℝ, 0 < η → HasDerivAt Rint (r η) η)
    (hf : ∀ η : ℝ, 0 < η → HasDerivAt f (f' η) η)
    (hode : ∀ η : ℝ, 0 < η → f' η
      = ((((-(1 / (2 * η)) : ℝ)) : ℂ)) • f η + I • (shiftedSymbolOp (r η / 2) T (f η))) :
    ∃ c : X, ∀ η : ℝ, 0 < η → f η = (η ^ (-(1:ℝ)/2)) • gammaTransport Rint T η c := by
  set g : ℝ → X := fun η => (η ^ ((1:ℝ)/2)) • (gammaTransportInv Rint T η (f η)) with hgdef
  have hgderiv : ∀ η : ℝ, 0 < η → HasDerivAt g 0 η := by
    intro η hη
    have hQ := hasDerivAt_gammaTransportInv (T := T) (r := r) (hRint η hη)
    have happ := hasDerivAt_clm_apply hQ (hf η hη)
    have hpow : HasDerivAt (fun y : ℝ => y ^ ((1:ℝ)/2)) ((1:ℝ)/2 * η ^ ((1:ℝ)/2 - 1)) η :=
      Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hη))
    have hg := hpow.smul happ
    have hcomm := commute_shiftedSymbolOp_gammaTransportInv (T := T) (Rint := Rint)
      (r η / 2) η
    have hcommv : shiftedSymbolOp (r η / 2) T (gammaTransportInv Rint T η (f η))
        = gammaTransportInv Rint T η (shiftedSymbolOp (r η / 2) T (f η)) := by
      have := congrArg (fun S : X →L[ℂ] X => S (f η)) hcomm
      simpa using this
    have hterm1 : (-(I • (shiftedSymbolOp (r η / 2) T * gammaTransportInv Rint T η))) (f η)
        = -(I • (gammaTransportInv Rint T η (shiftedSymbolOp (r η / 2) T (f η)))) := by
      rw [hcomm]
      rfl
    have hterm2 : gammaTransportInv Rint T η (f' η)
        = ((((-(1 / (2 * η)) : ℝ)) : ℂ)) • (gammaTransportInv Rint T η (f η))
          + I • (gammaTransportInv Rint T η (shiftedSymbolOp (r η / 2) T (f η))) := by
      rw [hode η hη, map_add, map_smul, map_smul]
    have hsum : (-(I • (shiftedSymbolOp (r η / 2) T * gammaTransportInv Rint T η))) (f η)
        + gammaTransportInv Rint T η (f' η)
        = ((-(1 / (2 * η)) : ℝ)) • (gammaTransportInv Rint T η (f η)) := by
      rw [hterm1, hterm2, ofReal_smul_eq]
      abel
    have hscal : (η ^ ((1:ℝ)/2)) * (-(1 / (2 * η)) : ℝ) + (1:ℝ)/2 * η ^ ((1:ℝ)/2 - 1) = 0 := by
      have hsub : η ^ ((1:ℝ)/2 - 1) = η ^ ((1:ℝ)/2) / η ^ (1:ℝ) :=
        Real.rpow_sub hη _ _
      rw [hsub, Real.rpow_one]
      field_simp
      ring
    have hzero : (η ^ ((1:ℝ)/2)) •
          ((-(I • (shiftedSymbolOp (r η / 2) T * gammaTransportInv Rint T η))) (f η)
            + gammaTransportInv Rint T η (f' η))
        + ((1:ℝ)/2 * η ^ ((1:ℝ)/2 - 1)) • (gammaTransportInv Rint T η (f η)) = 0 := by
      rw [hsum, smul_smul, ← add_smul, hscal, zero_smul]
    rw [← hzero]
    exact hg
  have hconst : ∀ x : ℝ, 0 < x → g x = g 1 := by
    intro x hx
    have ha : 0 < min x 1 := lt_min hx one_pos
    have hsub : ∀ y ∈ Icc (min x 1) (max x 1), 0 < y := fun y hy => lt_of_lt_of_le ha hy.1
    have hcont : ContinuousOn g (Icc (min x 1) (max x 1)) := fun y hy =>
      ((hgderiv y (hsub y hy)).continuousAt).continuousWithinAt
    have hd : ∀ y ∈ Ico (min x 1) (max x 1), HasDerivWithinAt g 0 (Ici y) y := fun y hy =>
      (hgderiv y (hsub y (Ico_subset_Icc_self hy))).hasDerivWithinAt
    have h1 := constant_of_has_deriv_right_zero hcont hd x ⟨min_le_left _ _, le_max_left _ _⟩
    have h2 := constant_of_has_deriv_right_zero hcont hd 1 ⟨min_le_right _ _, le_max_right _ _⟩
    rw [h1, h2]
  refine ⟨g 1, fun η hη => ?_⟩
  have hpowmul : (η ^ (-(1:ℝ)/2)) * (η ^ ((1:ℝ)/2)) = 1 := by
    rw [← Real.rpow_add hη]
    norm_num
  have h1 : gammaTransportInv Rint T η (f η) = (η ^ (-(1:ℝ)/2)) • g 1 := by
    rw [← hconst η hη, hgdef]
    show _ = (η ^ (-(1:ℝ)/2)) • ((η ^ ((1:ℝ)/2)) • (gammaTransportInv Rint T η (f η)))
    rw [smul_smul, hpowmul, one_smul]
  have h2 := congrArg (gammaTransport Rint T η) h1
  rw [gammaTransport_apply_inv_apply, map_real_smul] at h2
  exact h2

@[simp] theorem gammaTransportInv_apply_apply (η : ℝ) (v : X) :
    gammaTransportInv Rint T η (gammaTransport Rint T η v) = v := by
  have h := gammaTransportInv_mul (Rint := Rint) (T := T) η
  have := congrArg (fun S : X →L[ℂ] X => S v) h
  simpa using this

/-- **Uniqueness of the channel vector.**  Two channel vectors producing the same solution on the
half-line coincide. -/
theorem channel_vector_unique {c d : X}
    (h : ∀ η : ℝ, 0 < η → (η ^ (-(1:ℝ)/2)) • gammaTransport Rint T η c
      = (η ^ (-(1:ℝ)/2)) • gammaTransport Rint T η d) : c = d := by
  have h1 := h 1 one_pos
  rw [Real.one_rpow, one_smul, one_smul] at h1
  have h2 := congrArg (gammaTransportInv Rint T 1) h1
  rwa [gammaTransportInv_apply_apply, gammaTransportInv_apply_apply] at h2

end

end GaloisForLFunctions.RHTower
