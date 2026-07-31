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

/-- Real transition frequencies and intensities make the response compatible with complex
conjugation. -/
theorem finiteTransitionPassiveResponse_conj {α : Type*} [Fintype α]
    (intensity : α → α → ℝ) (energy : α → ℝ) (z : ℂ) :
    (starRingEnd ℂ) (finiteTransitionPassiveResponse intensity energy z) =
      finiteTransitionPassiveResponse intensity energy ((starRingEnd ℂ) z) := by
  simp only [finiteTransitionPassiveResponse, map_sum, map_div₀, map_sub,
    Complex.conj_ofReal]

/-- A finite real-frequency passive response respects complex conjugation. -/
theorem finitePassiveResponse_conj {α : Type*} [Fintype α]
    (intensity frequency : α → ℝ) (z : ℂ) :
    (starRingEnd ℂ) (finitePassiveResponse intensity frequency z) =
      finitePassiveResponse intensity frequency ((starRingEnd ℂ) z) := by
  simp only [finitePassiveResponse, map_sum, map_div₀, map_sub,
    Complex.conj_ofReal]

/-- Exact diagonal Kramers--Kronig/Pick value of a finite positive spectral resolvent. -/
theorem finitePassiveResponse_cauchyDiagonal_re {α : Type*} [Fintype α]
    (intensity frequency : α → ℝ) {z : ℂ} (hz : 0 < z.im) :
    (((finitePassiveResponse intensity frequency ((starRingEnd ℂ) z) -
      finitePassiveResponse intensity frequency z) /
        (z - (starRingEnd ℂ) z)).re) =
      ∑ a, intensity a / Complex.normSq (z - (frequency a : ℂ)) := by
  rw [← finitePassiveResponse_conj]
  have hzine : z.im ≠ 0 := ne_of_gt hz
  have hcalc :
      ((((starRingEnd ℂ) (finitePassiveResponse intensity frequency z) -
        finitePassiveResponse intensity frequency z) /
          (z - (starRingEnd ℂ) z)).re) =
        -(finitePassiveResponse intensity frequency z).im / z.im := by
    rw [Complex.div_re]
    simp [Complex.normSq_apply]
    field_simp
    ring
  rw [hcalc, finitePassiveResponse_im]
  rw [← Finset.sum_neg_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a _
  field_simp

/-- Exact diagonal Pick value of the finite Hamiltonian transition response. -/
theorem finiteTransitionPassiveResponse_cauchyDiagonal_re
    {α : Type*} [Fintype α]
    (intensity : α → α → ℝ) (energy : α → ℝ) {z : ℂ} (hz : 0 < z.im) :
    (((finiteTransitionPassiveResponse intensity energy ((starRingEnd ℂ) z) -
      finiteTransitionPassiveResponse intensity energy z) /
        (z - (starRingEnd ℂ) z)).re) =
      ∑ a, ∑ b, intensity a b /
        Complex.normSq (z - ((energy a - energy b : ℝ) : ℂ)) := by
  rw [← finiteTransitionPassiveResponse_conj]
  have hzine : z.im ≠ 0 := ne_of_gt hz
  have hcalc :
      ((((starRingEnd ℂ) (finiteTransitionPassiveResponse intensity energy z) -
        finiteTransitionPassiveResponse intensity energy z) /
          (z - (starRingEnd ℂ) z)).re) =
        -(finiteTransitionPassiveResponse intensity energy z).im / z.im := by
    rw [Complex.div_re]
    simp [Complex.normSq_apply]
    field_simp
    ring
  rw [hcalc, finiteTransitionPassiveResponse_im]
  rw [← Finset.sum_neg_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a _
  rw [← Finset.sum_neg_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro b _
  field_simp

/-- Nonnegative transition intensities make every diagonal response divided difference
nonnegative. -/
theorem finiteTransitionPassiveResponse_cauchyDiagonal_nonneg
    {α : Type*} [Fintype α]
    (intensity : α → α → ℝ) (energy : α → ℝ)
    (hintensity : ∀ a b, 0 ≤ intensity a b)
    {z : ℂ} (hz : 0 < z.im) :
    0 ≤ (((finiteTransitionPassiveResponse intensity energy ((starRingEnd ℂ) z) -
      finiteTransitionPassiveResponse intensity energy z) /
        (z - (starRingEnd ℂ) z)).re) := by
  rw [finiteTransitionPassiveResponse_cauchyDiagonal_re intensity energy hz]
  apply Finset.sum_nonneg
  intro a _
  apply Finset.sum_nonneg
  intro b _
  exact div_nonneg (hintensity a b) (Complex.normSq_nonneg _)

/-- Pairing every transition with its reverse makes the finite passive response exactly odd in
the centered spectral coordinate. -/
theorem finiteTransitionPassiveResponse_neg {α : Type*} [Fintype α]
    (intensity : α → α → ℝ) (energy : α → ℝ)
    (hsymm : ∀ a b, intensity a b = intensity b a) (z : ℂ) :
    finiteTransitionPassiveResponse intensity energy (-z) =
      -finiteTransitionPassiveResponse intensity energy z := by
  rw [finiteTransitionPassiveResponse, finiteTransitionPassiveResponse]
  calc
    (∑ a, ∑ b, (intensity a b : ℂ) /
        (-z - ((energy a - energy b : ℝ) : ℂ))) =
      ∑ a, ∑ b, (intensity b a : ℂ) /
        (-z - ((energy b - energy a : ℝ) : ℂ)) := Finset.sum_comm
    _ = ∑ a, ∑ b, -((intensity a b : ℂ) /
        (z - ((energy a - energy b : ℝ) : ℂ))) := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      rw [← hsymm a b]
      have hden : -z - ((energy b - energy a : ℝ) : ℂ) =
          -(z - ((energy a - energy b : ℝ) : ℂ)) := by
        push_cast
        ring
      rw [div_eq_mul_inv, hden, inv_neg]
      ring
    _ = -(∑ a, ∑ b, (intensity a b : ℂ) /
        (z - ((energy a - energy b : ℝ) : ℂ))) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_neg_distrib]

/-- Hermiticity makes canonical KMS/Wightman response approximants exactly odd without a free
transition-symmetry hypothesis. -/
theorem finiteKMSWightmanTransitionPassiveResponse_neg
    {α : Type*} [Fintype α]
    (β : ℝ) (energy : α → ℝ) (amplitude : α → α → ℂ)
    (hHermitian : ∀ a b, amplitude b a = star (amplitude a b)) (z : ℂ) :
    finiteTransitionPassiveResponse
      (finiteKMSWightmanTransitionIntensity β energy amplitude) energy (-z) =
      -finiteTransitionPassiveResponse
        (finiteKMSWightmanTransitionIntensity β energy amplitude) energy z := by
  exact finiteTransitionPassiveResponse_neg _ energy
    (finiteKMSWightmanTransitionIntensity_symm β energy amplitude hHermitian) z

/-- Canonical KMS/Wightman weights automatically make the response Cauchy diagonal
nonnegative. -/
theorem finiteKMSWightmanTransitionPassiveResponse_cauchyDiagonal_nonneg
    {α : Type*} [Fintype α] [Nonempty α]
    (β : ℝ) (energy : α → ℝ) (amplitude : α → α → ℂ)
    {z : ℂ} (hz : 0 < z.im) :
    0 ≤ (((finiteTransitionPassiveResponse
      (finiteKMSWightmanTransitionIntensity β energy amplitude) energy
        ((starRingEnd ℂ) z) -
      finiteTransitionPassiveResponse
        (finiteKMSWightmanTransitionIntensity β energy amplitude) energy z) /
          (z - (starRingEnd ℂ) z)).re) := by
  exact finiteTransitionPassiveResponse_cauchyDiagonal_nonneg _ energy
    (finiteKMSWightmanTransitionIntensity_nonneg β energy amplitude) hz

end

end HTGeometry
