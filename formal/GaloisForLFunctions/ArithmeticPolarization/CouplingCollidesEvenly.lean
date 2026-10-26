import GaloisForLFunctions.ArithmeticCorrespondencePositivity.ExteriorAndHeightCoupledQuartetContractions

/-!
# Coupling collides evenly

Two ways to collide a conjugate pair of Frobenius eigenvalues into the real axis: the **coupling**
`D ⊗ (e^{iθ} ⊕ e^{−iθ})`, the finite-field shadow of the height-coupled lift
`F(s)² F(s + iγ) F(s − iγ)`, and the **exterior square** `Λ²D`. They differ by the parity of the
collision.

* **The coupled datum** (`CurveDatum.couple`): for every curve datum and phase `θ`, the eigenvalues
  `e^{±iθ} β_i` form a curve datum of twice the genus; the phase `θ = −arg β` turns the impure
  eigenvalue `β` into the real eigenvalue `|β|` (`complexFake_couple_collides`).
* **Couplings are blind to kernel counts** (`couple_detDeg_eq_normSq`, `couple_detDeg_nonneg`):
  every kernel count of a coupled datum is a modulus square `|Π_i P(√q e^{iθ} β_i)|²`, for every
  datum: fake, golden or genuine. The collided eigenvalue appears twice, once from `β` with
  `e^{iθ}` and once from `β̄` with `e^{−iθ}`.
* **Exterior squares are not** (ACP `complexFake_exteriorDetDeg_two_seventeen`,
  `unitary_of_exteriorDetDeg_nonneg`): in `Λ²` the pair `{β, β̄}` is one subset, the collided
  eigenvalue `|β|²` appears once, and kernel counts force unitarity.
* **Over `ℤ` the coupling collides evenly** (`heightCoupled_order_even`): the height-coupled
  completion of every completed positive system vanishes to even order at every real point,
  `2 ord_x(Λ) + 2 ord_{x+iγ}(Λ)`. This is the parity behind the `2 : 1` real-anchor law and the
  Fejér barrier: a coupling can anchor a contraction but never count the collided charge, and the
  odd collision that counts is the global exterior square, which has no meromorphic carrier.
-/

open Complex Polynomial Finset
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.ArithmeticPolarization

open ArithmeticCastelnuovoSeveri ArithmeticCorrespondencePositivity

/-- The two phases `e^{±iθ}` of a coupling, indexed by `Bool`. -/
def phase (θ : ℝ) (b : Bool) : ℂ := if b then Complex.exp (θ * I) else Complex.exp (-(θ * I))

theorem conj_phase (θ : ℝ) (b : Bool) : conj (phase θ b) = phase θ (!b) := by
  cases b <;> simp [phase, ← Complex.exp_conj]

theorem phase_not_mul (θ : ℝ) (b : Bool) : phase θ (!b) * phase θ b = 1 := by
  cases b <;> simp [phase, ← Complex.exp_add]

theorem swap_bool (b : Bool) : Equiv.swap true false b = !b := by
  cases b <;> simp [Equiv.swap_apply_left, Equiv.swap_apply_right]

/-- **The coupled datum** `D ⊗ (e^{iθ} ⊕ e^{−iθ})`. -/
def CurveDatum.couple {ι : Type*} [Fintype ι] (D : CurveDatum ι) (θ : ℝ) :
    CurveDatum (ι × Bool) where
  q := D.q
  one_lt_q := D.one_lt_q
  β p := phase θ p.2 * D.β p.1
  conjPerm := Equiv.prodCongr D.conjPerm (Equiv.swap true false)
  β_conjPerm p := by
    simp only [Equiv.prodCongr_apply, Prod.map, swap_bool, D.β_conjPerm, map_mul, conj_phase]
  fePerm := Equiv.prodCongr D.fePerm (Equiv.swap true false)
  β_fePerm p := by
    simp only [Equiv.prodCongr_apply, Prod.map, swap_bool]
    rw [show phase θ (!p.2) * D.β (D.fePerm p.1) * (phase θ p.2 * D.β p.1) =
      (phase θ (!p.2) * phase θ p.2) * (D.β (D.fePerm p.1) * D.β p.1) by ring,
      phase_not_mul, D.β_fePerm, one_mul]

variable {ι : Type*} [Fintype ι] (D : CurveDatum ι)

/-- **Every kernel count of a coupled datum is a modulus square.** -/
theorem couple_detDeg_eq_normSq (θ : ℝ) (P : ℝ[X]) :
    detDeg (D.couple θ) P =
      (Complex.normSq (∏ i, aeval ((D.sqrtq : ℂ) * (phase θ true * D.β i)) P) : ℂ) := by
  have hsq : (D.couple θ).sqrtq = D.sqrtq := rfl
  rw [detDeg, Fintype.prod_prod_type]
  simp only [eigenvalue, hsq, Fintype.prod_bool]
  rw [Finset.prod_mul_distrib, ← Complex.mul_conj]
  congr 1
  -- the `false` phases are the conjugates of the `true` phases at the conjugate index
  rw [map_prod, ← Equiv.prod_comp D.conjPerm]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← aeval_conj, map_mul, Complex.conj_ofReal, map_mul, conj_phase, D.β_conjPerm,
    Complex.conj_conj]
  rfl

/-- Kernel counts of a coupled datum are nonnegative reals, for every datum. -/
theorem couple_detDeg_nonneg (θ : ℝ) (P : ℝ[X]) :
    ∃ r : ℝ, 0 ≤ r ∧ detDeg (D.couple θ) P = r :=
  ⟨_, Complex.normSq_nonneg _, couple_detDeg_eq_normSq D θ P⟩

/-- **The coupling collides the complex fake.** At `θ = −π/2` the impure eigenvalue `2i` of the
complex fake becomes the real eigenvalue `2`, off the unit circle; yet every kernel count of the
coupled datum is nonnegative. -/
theorem complexFake_couple_collides :
    (complexFake.couple (-(Real.pi / 2))).β (0, true) = 2 ∧
      (∀ P : ℝ[X], ∃ r : ℝ, 0 ≤ r ∧ detDeg (complexFake.couple (-(Real.pi / 2))) P = r) := by
  refine ⟨?_, couple_detDeg_nonneg complexFake _⟩
  show phase (-(Real.pi / 2)) true * complexFake.β 0 = 2
  have hβ : complexFake.β 0 = 2 * I := rfl
  have he : Complex.exp ((-(Real.pi / 2) : ℝ) * I) = -I := by
    rw [show ((-(Real.pi / 2) : ℝ) : ℂ) * I = -(Real.pi / 2 * I) by push_cast; ring,
      Complex.exp_neg, show (Real.pi : ℂ) / 2 * I = Real.pi / 2 * I from rfl]
    rw [show (↑Real.pi / 2 * I : ℂ) = ↑(Real.pi / 2) * I by push_cast; ring, Complex.exp_mul_I]
    rw [← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_two, Real.sin_pi_div_two]
    simp
  simp only [phase, if_true, he, hβ]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- **Over `ℤ` the coupling collides evenly.** The height-coupled completion of a completed
positive system vanishes to even order at every real point. -/
theorem heightCoupled_order_even {κ d : ℕ} {F Λ : ℂ → ℂ}
    (hS : StripBochnerWeilForcing.CompletedPositiveSystem κ d F Λ) (γ x : ℝ) :
    Even (analyticOrderAt (heightCoupledΛ Λ γ) (x : ℂ)).toNat := by
  rw [ArithmeticCorrespondencePositivity.CompletedPositiveSystem.orderAt_heightCoupledΛ_real hS γ x]
  exact ⟨(analyticOrderAt Λ (x : ℂ)).toNat + (analyticOrderAt Λ ((x : ℂ) + (γ : ℂ) * I)).toNat,
    by ring⟩

end GaloisForLFunctions.ArithmeticPolarization
