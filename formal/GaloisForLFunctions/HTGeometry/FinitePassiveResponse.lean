import GaloisForLFunctions.HTGeometry.FiniteKMSWightman

/-!
# Finite passive-response value relations

The Lehmann representation of a retarded response is a positive spectral sum of resolvents.  In
the convention

`R(z) = Σ_a I_a / (z - ω_a)`,

its absorptive part has the exact value

`Im R(z) = -Σ_a I_a Im(z) / |z - ω_a|²`.

Thus nonnegative intensities make `R` anti-Herglotz in the upper half-plane.  The transition-space
specialization uses the Liouvillian frequencies `E_a - E_b`; canonical KMS/Wightman data discharge
the nonnegative-intensity hypothesis automatically.
-/

open scoped BigOperators

namespace HTGeometry

noncomputable section

/-- Finite passive resolvent in the convention with negative imaginary part in the upper
half-plane. -/
def finitePassiveResponse {α : Type*} [Fintype α]
    (intensity frequency : α → ℝ) (z : ℂ) : ℂ :=
  ∑ a, (intensity a : ℂ) / (z - (frequency a : ℂ))

/-- The absorptive value of one real-frequency resolvent atom. -/
theorem im_ofReal_div_sub_ofReal (w t : ℝ) (z : ℂ) :
    (((w : ℂ) / (z - (t : ℂ))).im) =
      -(w * z.im) / Complex.normSq (z - (t : ℂ)) := by
  rw [Complex.div_im]
  simp [Complex.normSq_apply]
  ring

/-- An upper-half-plane point cannot coincide with a real response frequency. -/
theorem normSq_sub_ofReal_pos {t : ℝ} {z : ℂ} (hz : 0 < z.im) :
    0 < Complex.normSq (z - (t : ℂ)) := by
  rw [Complex.normSq_pos]
  intro h
  have him := congrArg Complex.im h
  simp at him
  linarith

/-- Exact absorptive value of a finite passive response. -/
theorem finitePassiveResponse_im {α : Type*} [Fintype α]
    (intensity frequency : α → ℝ) (z : ℂ) :
    (finitePassiveResponse intensity frequency z).im =
      ∑ a, -(intensity a * z.im) /
        Complex.normSq (z - (frequency a : ℂ)) := by
  rw [finitePassiveResponse]
  change Complex.imCLM
    (∑ a, (intensity a : ℂ) / (z - (frequency a : ℂ))) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro a _
  exact im_ofReal_div_sub_ofReal _ _ _

/-- Nonnegative spectral weights make the response anti-Herglotz in the upper half-plane. -/
theorem finitePassiveResponse_im_nonpos {α : Type*} [Fintype α]
    (intensity frequency : α → ℝ) (hintensity : ∀ a, 0 ≤ intensity a)
    {z : ℂ} (hz : 0 < z.im) :
    (finitePassiveResponse intensity frequency z).im ≤ 0 := by
  rw [finitePassiveResponse_im]
  apply Finset.sum_nonpos
  intro a _
  exact div_nonpos_of_nonpos_of_nonneg
    (neg_nonpos.mpr (mul_nonneg (hintensity a) hz.le))
    (Complex.normSq_nonneg _)

/-- The passive response on the finite transition spectrum of a Hamiltonian. -/
def finiteTransitionPassiveResponse {α : Type*} [Fintype α]
    (intensity : α → α → ℝ) (energy : α → ℝ) (z : ℂ) : ℂ :=
  ∑ a, ∑ b, (intensity a b : ℂ) /
    (z - ((energy a - energy b : ℝ) : ℂ))

/-- Exact absorptive value of the transition-space response. -/
theorem finiteTransitionPassiveResponse_im {α : Type*} [Fintype α]
    (intensity : α → α → ℝ) (energy : α → ℝ) (z : ℂ) :
    (finiteTransitionPassiveResponse intensity energy z).im =
      ∑ a, ∑ b, -(intensity a b * z.im) /
        Complex.normSq (z - ((energy a - energy b : ℝ) : ℂ)) := by
  rw [finiteTransitionPassiveResponse]
  change Complex.imCLM (∑ a, ∑ b, (intensity a b : ℂ) /
    (z - ((energy a - energy b : ℝ) : ℂ))) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro a _
  change Complex.imCLM (∑ b, (intensity a b : ℂ) /
    (z - ((energy a - energy b : ℝ) : ℂ))) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro b _
  exact im_ofReal_div_sub_ofReal _ _ _

/-- Nonnegative transition intensities give the finite Kubo/Lehmann response its passive sign. -/
theorem finiteTransitionPassiveResponse_im_nonpos {α : Type*} [Fintype α]
    (intensity : α → α → ℝ) (energy : α → ℝ)
    (hintensity : ∀ a b, 0 ≤ intensity a b)
    {z : ℂ} (hz : 0 < z.im) :
    (finiteTransitionPassiveResponse intensity energy z).im ≤ 0 := by
  rw [finiteTransitionPassiveResponse_im]
  apply Finset.sum_nonpos
  intro a _
  apply Finset.sum_nonpos
  intro b _
  exact div_nonpos_of_nonpos_of_nonneg
    (neg_nonpos.mpr (mul_nonneg (hintensity a b) hz.le))
    (Complex.normSq_nonneg _)

/-- Canonical KMS/Wightman data need no separate passivity hypothesis. -/
theorem finiteKMSWightmanTransitionPassiveResponse_im_nonpos
    {α : Type*} [Fintype α] [Nonempty α]
    (β : ℝ) (energy : α → ℝ) (amplitude : α → α → ℂ)
    {z : ℂ} (hz : 0 < z.im) :
    (finiteTransitionPassiveResponse
      (finiteKMSWightmanTransitionIntensity β energy amplitude) energy z).im ≤ 0 := by
  exact finiteTransitionPassiveResponse_im_nonpos _ energy
    (finiteKMSWightmanTransitionIntensity_nonneg β energy amplitude) hz

end

end HTGeometry
