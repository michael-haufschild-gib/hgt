import GaloisForLFunctions.HTGeometry.ExponentialSeriesFiberwise

/-!
# Finite sums of exponential series

A finite sum of exponential series is the exponential series indexed by the disjoint union of their
index sets, and the amplitude it carries at a frequency is the sum of the amplitudes the summands
carry there.

This is how the finitely many monomials of a differential relation are combined into one series
before its coefficients are read off.
-/

open Filter Topology

namespace GaloisForLFunctions

noncomputable section

variable {κ : Type*} {J : κ → Type*}

/-- The fibre of a disjoint union splits into the fibres of the pieces. -/
def sigmaFiberSplit (J : κ → Type*) (om : ∀ c, J c → ℝ) (nu : ℝ) :
    {p : Σ c, J c // om p.1 p.2 = nu} ≃ Σ c, {j : J c // om c j = nu} where
  toFun p := ⟨p.1.1, ⟨p.1.2, p.2⟩⟩
  invFun q := ⟨⟨q.1, q.2.1⟩, q.2.2⟩
  left_inv := by rintro ⟨⟨c, j⟩, hp⟩; rfl
  right_inv := by rintro ⟨c, ⟨j, hj⟩⟩; rfl

theorem summable_norm_sigma [Fintype κ] {b : ∀ c, J c → ℂ}
    (hb : ∀ c, Summable fun j => ‖b c j‖) :
    Summable fun p : Σ c, J c => ‖b p.1 p.2‖ :=
  (summable_sigma_of_nonneg (fun _ => norm_nonneg _)).2 ⟨fun c => hb c, Summable.of_finite⟩

theorem summable_sigma_of_fibrewise [Fintype κ] {b : ∀ c, J c → ℂ}
    (hb : ∀ c, Summable fun j => ‖b c j‖) : Summable fun p : Σ c, J c => b p.1 p.2 :=
  Summable.of_norm (summable_norm_sigma hb)

/-- **A finite sum of exponential series is one exponential series.** -/
theorem sum_expSeriesCarrier [Fintype κ] (b : ∀ c, J c → ℂ) (om : ∀ c, J c → ℝ)
    (hb : ∀ c, Summable fun j => ‖b c j‖) (t : ℝ) :
    ∑ c, expSeriesCarrier (b c) (om c) t
      = expSeriesCarrier (fun p : Σ c, J c => b p.1 p.2) (fun p : Σ c, J c => om p.1 p.2) t := by
  have hsum : Summable fun p : Σ c, J c => b p.1 p.2 * expChar (om p.1 p.2) t := by
    refine Summable.of_norm ?_
    have hnorm : ∀ p : Σ c, J c, ‖b p.1 p.2 * expChar (om p.1 p.2) t‖ = ‖b p.1 p.2‖ := by
      intro p
      simp
    simpa only [hnorm] using summable_norm_sigma hb
  rw [expSeriesCarrier, hsum.tsum_sigma, tsum_fintype]
  rfl

/-- **The amplitude of a disjoint union is the sum of the amplitudes.** -/
theorem fiberAmplitude_sigma [Fintype κ] (b : ∀ c, J c → ℂ) (om : ∀ c, J c → ℝ)
    (hb : ∀ c, Summable fun j => ‖b c j‖) (nu : ℝ) :
    fiberAmplitude (fun p : Σ c, J c => b p.1 p.2) (fun p : Σ c, J c => om p.1 p.2) nu
      = ∑ c, fiberAmplitude (b c) (om c) nu := by
  have hsub : ∀ c, Summable fun j : {j : J c // om c j = nu} => ‖b c (j : J c)‖ :=
    fun c => (hb c).subtype _
  have hsig : Summable fun q : Σ c, {j : J c // om c j = nu} => b q.1 (q.2 : J q.1) :=
    summable_sigma_of_fibrewise hsub
  rw [fiberAmplitude, ← (sigmaFiberSplit J om nu).symm.tsum_eq
    (fun p : {p : Σ c, J c // om p.1 p.2 = nu} => b (p : Σ c, J c).1 (p : Σ c, J c).2)]
  rw [show (fun q : Σ c, {j : J c // om c j = nu} =>
      b ((sigmaFiberSplit J om nu).symm q : Σ c, J c).1
        ((sigmaFiberSplit J om nu).symm q : Σ c, J c).2)
      = fun q : Σ c, {j : J c // om c j = nu} => b q.1 (q.2 : J q.1) from rfl]
  rw [hsig.tsum_sigma, tsum_fintype]
  rfl

/-! ## Scaling -/

theorem const_mul_expSeriesCarrier {I' : Type*} (c : ℂ) (B : I' → ℂ) (Omega : I' → ℝ) (t : ℝ) :
    c * expSeriesCarrier B Omega t
      = expSeriesCarrier (fun n => c * B n) Omega t := by
  rw [expSeriesCarrier, expSeriesCarrier, ← tsum_mul_left]
  exact tsum_congr fun n => by ring

theorem fiberAmplitude_const_mul {I' : Type*} (c : ℂ) (B : I' → ℂ) (Omega : I' → ℝ) (nu : ℝ) :
    fiberAmplitude (fun n => c * B n) Omega nu = c * fiberAmplitude B Omega nu := by
  rw [fiberAmplitude, fiberAmplitude, ← tsum_mul_left]

end

end GaloisForLFunctions
