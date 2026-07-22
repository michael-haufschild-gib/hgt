import GaloisForLFunctions.HTGeometry.PolynomialPowerExplicitConfinement

open Filter Finset PowerSeries MvPolynomial Topology Asymptotics Set

namespace GaloisForLFunctions

noncomputable section

def atomValuation (b : ℕ → ℝ) (ν : ℕ →₀ ℕ) : ℝ :=
  ν.sum fun i k => (k : ℝ) * b i

/-- The intrinsic unit phase of one grouped ADE atom. -/
def normalizedAtomPhase (F : PowerSeries ℂ) (b : ℕ → ℝ)
    (ν : ℕ →₀ ℕ) : ℂ :=
  (Real.exp (atomValuation b ν) : ℂ) *
    ν.prod (fun i k => (PowerSeries.coeff i F) ^ k)

theorem norm_normalizedAtomPhase
    (F : PowerSeries ℂ) (b : ℕ → ℝ)
    (hb : ∀ i, ‖PowerSeries.coeff i F‖ = Real.exp (-b i))
    (ν : ℕ →₀ ℕ) :
    ‖normalizedAtomPhase F b ν‖ = 1 := by
  rw [normalizedAtomPhase, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), norm_aval hb]
  dsimp [atomValuation]
  rw [← Real.exp_add]
  ring_nf
  simp

theorem atomProduct_eq_exp_neg_mul_normalizedAtomPhase
    (F : PowerSeries ℂ) (b : ℕ → ℝ) (ν : ℕ →₀ ℕ) :
    ν.prod (fun i k => (PowerSeries.coeff i F) ^ k) =
      (Real.exp (-atomValuation b ν) : ℂ) * normalizedAtomPhase F b ν := by
  rw [normalizedAtomPhase]
  push_cast
  rw [← mul_assoc, ← Complex.exp_add]
  simp

theorem normalized_aeval_coefficient_identity
    (n N : ℕ) (F : PowerSeries ℂ)
    (Q : MvPolynomial (Fin (n + 2)) ℂ) (b : ℕ → ℝ)
    (hrel : aeval (formalJets n F) Q = 0) (m : ℝ) :
    ∑ ν ∈ (sigmaIdx n N Q).image (atomKeyOf n),
        aevalWeight n N Q ν *
          (Real.exp (-(atomValuation b ν - m)) : ℂ) *
            normalizedAtomPhase F b ν = 0 := by
  have hcoeff : PowerSeries.coeff N (aeval (formalJets n F) Q) = 0 := by
    rw [hrel, map_zero]
  rw [coeff_aeval_regrouped_weight] at hcoeff
  calc
    ∑ ν ∈ (sigmaIdx n N Q).image (atomKeyOf n),
        aevalWeight n N Q ν *
          (Real.exp (-(atomValuation b ν - m)) : ℂ) *
            normalizedAtomPhase F b ν =
        (Real.exp m : ℂ) *
          ∑ ν ∈ (sigmaIdx n N Q).image (atomKeyOf n),
            (ν.prod (fun i k => (PowerSeries.coeff i F) ^ k)) *
              aevalWeight n N Q ν := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ν hν
      rw [normalizedAtomPhase]
      push_cast
      rw [show -((atomValuation b ν : ℂ) - (m : ℂ)) =
        -(atomValuation b ν : ℂ) + (m : ℂ) by ring]
      have hexp :
          Complex.exp (-(atomValuation b ν : ℂ) + (m : ℂ)) *
              Complex.exp (atomValuation b ν : ℂ) = Complex.exp (m : ℂ) := by
        rw [← Complex.exp_add]
        congr 1
        ring
      calc
        aevalWeight n N Q ν *
              Complex.exp (-(atomValuation b ν : ℂ) + (m : ℂ)) *
                (Complex.exp (atomValuation b ν : ℂ) *
                  ν.prod (fun i k => (PowerSeries.coeff i F) ^ k)) =
            (Complex.exp (-(atomValuation b ν : ℂ) + (m : ℂ)) *
              Complex.exp (atomValuation b ν : ℂ)) *
                ((ν.prod (fun i k => (PowerSeries.coeff i F) ^ k)) *
                  aevalWeight n N Q ν) := by ring
        _ = Complex.exp (m : ℂ) *
              ((ν.prod (fun i k => (PowerSeries.coeff i F) ^ k)) *
                aevalWeight n N Q ν) := by rw [hexp]
    _ = 0 := by rw [hcoeff, mul_zero]

/-- Abstract finite-cluster phase cancellation: an exact normalized balance,
a uniform outside valuation gap, and a weight-mass bound imply an
exponentially small cluster sum. -/
theorem norm_cluster_sum_le_mass_mul_exp_neg_gap
    {α : Type*} [DecidableEq α]
    (T C : Finset α)
    (w phase : α → ℂ) (V : α → ℝ) (m G P : ℝ)
    (hbalance :
      ∑ a ∈ C, w a * (Real.exp (-(V a - m)) : ℂ) * phase a =
        -∑ a ∈ T \ C, w a * (Real.exp (-(V a - m)) : ℂ) * phase a)
    (hphase : ∀ a ∈ T, ‖phase a‖ ≤ 1)
    (hgap : ∀ a ∈ T \ C, m + G ≤ V a)
    (hmass : ∑ a ∈ T, ‖w a‖ ≤ P) :
    ‖∑ a ∈ C, w a * (Real.exp (-(V a - m)) : ℂ) * phase a‖ ≤
      P * Real.exp (-G) := by
  rw [hbalance, norm_neg]
  calc
    ‖∑ a ∈ T \ C,
        w a * (Real.exp (-(V a - m)) : ℂ) * phase a‖
        ≤ ∑ a ∈ T \ C,
          ‖w a * (Real.exp (-(V a - m)) : ℂ) * phase a‖ :=
      norm_sum_le _ _
    _ ≤ ∑ a ∈ T \ C, ‖w a‖ * Real.exp (-G) := by
      apply Finset.sum_le_sum
      intro a ha
      have haT : a ∈ T := (Finset.mem_sdiff.mp ha).1
      have hexp : Real.exp (-(V a - m)) ≤ Real.exp (-G) := by
        apply Real.exp_le_exp.mpr
        linarith [hgap a ha]
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _)]
      have hnonneg : 0 ≤ ‖w a‖ := norm_nonneg _
      calc
        ‖w a‖ * Real.exp (-(V a - m)) * ‖phase a‖
            ≤ ‖w a‖ * Real.exp (-(V a - m)) * 1 :=
          mul_le_mul_of_nonneg_left (hphase a haT)
            (mul_nonneg hnonneg (Real.exp_nonneg _))
        _ ≤ ‖w a‖ * Real.exp (-G) := by
          simpa using mul_le_mul_of_nonneg_left hexp hnonneg
    _ = (∑ a ∈ T \ C, ‖w a‖) * Real.exp (-G) := by rw [Finset.sum_mul]
    _ ≤ (∑ a ∈ T, ‖w a‖) * Real.exp (-G) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
      exact Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
        (fun a haT haDiff => norm_nonneg (w a))
    _ ≤ P * Real.exp (-G) :=
      mul_le_mul_of_nonneg_right hmass (Real.exp_nonneg _)

theorem normalized_cluster_balance_of_identity
    {α : Type*} [DecidableEq α]
    (T C : Finset α) (hCT : C ⊆ T) (f : α → ℂ)
    (hzero : ∑ a ∈ T, f a = 0) :
    ∑ a ∈ C, f a = -∑ a ∈ T \ C, f a := by
  have hsplit : (∑ a ∈ T \ C, f a) + ∑ a ∈ C, f a = 0 := by
    rw [Finset.sum_sdiff hCT, hzero]
  calc
    ∑ a ∈ C, f a =
        ((∑ a ∈ T \ C, f a) + ∑ a ∈ C, f a) -
          ∑ a ∈ T \ C, f a := by ring
    _ = -∑ a ∈ T \ C, f a := by rw [hsplit]; simp

end

end GaloisForLFunctions
