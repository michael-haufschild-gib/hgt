import GaloisForLFunctions.ArithmeticScatteringHolography.TheFluxLaw

/-!
# The scattering matrix

An incoming amplitude on the cusps is a function `A : G → ℂ`. Split it into its mean and a zero-mean part.

* The **zero-mean part** never reaches the core: the core and the dead ends stay at zero, each neck
  transmits the wave from `P` to `-P`, and the outgoing amplitude is `(Y/X) A(-P)`
  (`zeroMeanField_eigen`). This part of the scattering matrix has no pole.
* The **mean** is the radial sector. It carries the core, the dead ends and every resonance, with
  `S = -Y j(Y, X)/(X j(X, Y))`.

So the scattering matrix is `(Y/X) σ` plus a rank-one coupling to the core. In the causal variable `w = X⁻²`,

  `S(w) = q w + q(q-1) h w²(1 + q w) / ((1 - q² w)(1 - t w + q w²))`

(`scattering_eq_causal`), and the coefficients of this series are the echoes of the time-domain solution.
On the unitary circle `|X|² = q` both pieces have modulus one (`norm_radialScattering_eq_one`), for every real
`t`.
-/

open Finset ComplexConjugate

noncomputable section

set_option linter.unusedSectionVars false

namespace GaloisForLFunctions.ArithmeticScatteringHolography

variable {G D : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G] [Fintype D]

theorem eq_neg_of_two_nsmul {P : G} (h : 2 • P = 0) : -P = P := by
  have : P + P = 0 := by rw [← two_nsmul]; exact h
  exact neg_eq_of_add_eq_zero_left this

/-- The value of the zero-mean solution at the neck of `P`. -/
def zeroMeanNeck (X : ℂ) (A : G → ℂ) (P : G) : ℂ :=
  if 2 • P = 0 then A P / X else (A P + A (-P)) / X

theorem zeroMeanNeck_neg (X : ℂ) (A : G → ℂ) (P : G) :
    zeroMeanNeck X A (-P) = zeroMeanNeck X A P := by
  unfold zeroMeanNeck
  by_cases h : 2 • P = 0
  · rw [if_pos (by rwa [two_nsmul_neg_eq_zero_iff]), if_pos h, eq_neg_of_two_nsmul h]
  · rw [if_neg h, if_neg (by rwa [two_nsmul_neg_eq_zero_iff]), neg_neg]
    ring

/-- The eigenfunction with incoming amplitude `A` of mean zero. -/
def zeroMeanField (q : ℕ) (X Y : ℂ) (A : G → ℂ) : Vertex G D → ℂ
  | .core => 0
  | .dead _ => 0
  | .neck x => Quotient.liftOn x (zeroMeanNeck X A) (fun P R h => by
      rcases h with rfl | rfl
      · rfl
      · exact (zeroMeanNeck_neg X A P).symm)
  | .cap L => ((q : ℂ) + 1) * A L.1 / X
  | .ray P k => A P * X ^ k + (Y / X) * A (-P) * Y ^ k

@[simp] theorem zeroMeanField_core (q : ℕ) (X Y : ℂ) (A : G → ℂ) :
    zeroMeanField q X Y A (.core : Vertex G D) = 0 := rfl
@[simp] theorem zeroMeanField_dead (q : ℕ) (X Y : ℂ) (A : G → ℂ) (d : D) :
    zeroMeanField q X Y A (.dead d : Vertex G D) = 0 := rfl
@[simp] theorem zeroMeanField_neck (q : ℕ) (X Y : ℂ) (A : G → ℂ) (P : G) :
    zeroMeanField q X Y A (.neck (Branch.mk P) : Vertex G D) = zeroMeanNeck X A P := rfl
@[simp] theorem zeroMeanField_cap (q : ℕ) (X Y : ℂ) (A : G → ℂ) (L : TwoTorsion G) :
    zeroMeanField q X Y A (.cap L : Vertex G D) = ((q : ℂ) + 1) * A L.1 / X := rfl
@[simp] theorem zeroMeanField_ray (q : ℕ) (X Y : ℂ) (A : G → ℂ) (P : G) (k : ℕ) :
    zeroMeanField q X Y A (.ray P k : Vertex G D) = A P * X ^ k + (Y / X) * A (-P) * Y ^ k := rfl

/-- The neck sum of a zero-mean solution vanishes: the core does not see it. -/
theorem sum_zeroMeanNeck (X : ℂ) {A : G → ℂ} (hA : ∑ P, A P = 0) :
    ∑ P : G, branchWeight P * zeroMeanNeck X A P = 0 := by
  have hterm (P : G) : branchWeight P * zeroMeanNeck X A P =
      (A P + A (-P)) / (2 * X) := by
    unfold branchWeight zeroMeanNeck
    by_cases h : 2 • P = 0
    · have e := eq_neg_of_two_nsmul h
      simp only [if_pos h, e]
      by_cases hX : X = 0
      · simp [hX]
      · field_simp
        ring
    · simp only [if_neg h]
      by_cases hX : X = 0
      · simp [hX]
      · field_simp
  simp only [hterm, ← Finset.sum_div, Finset.sum_add_distrib]
  have e2 : ∑ P : G, A (-P) = ∑ P : G, A P := Equiv.sum_comp (Equiv.neg G) A
  rw [e2, hA]
  simp

/-- The gap term of a zero-mean solution, in one closed form for both kinds of point. -/
theorem gapOp_zeroMeanField {q : ℕ} {X Y : ℂ} (hXY : X * Y = q) (hX : X ≠ 0) (A : G → ℂ) (R : G) :
    gapOp q (zeroMeanField q X Y A : Vertex G D → ℂ) R = Y * (A R + A (-R)) := by
  unfold gapOp
  by_cases h : 2 • R = 0
  · have e := eq_neg_of_two_nsmul h
    rw [dif_pos h, zeroMeanField_neck, zeroMeanField_cap, e]
    unfold zeroMeanNeck
    rw [if_pos h, ← hXY]
    field_simp
    ring
  · rw [dif_neg h, zeroMeanField_neck]
    unfold zeroMeanNeck
    rw [if_neg h, ← hXY]
    field_simp

/-- **The zero-mean sectors.** For every `X ≠ 0`, the amplitude `A` of mean zero extends to an eigenfunction
with outgoing amplitude `(Y/X) A(-P)`. There is no condition on `X`: this part of the scattering has no
resonance. -/
theorem zeroMeanField_eigen {q : ℕ} {X Y : ℂ} (hXY : X * Y = q) (hX : X ≠ 0) {A : G → ℂ}
    (hA : ∑ P, A P = 0) (v : Vertex G D) :
    waveOp q (zeroMeanField q X Y A) v = (X + Y) * zeroMeanField q X Y A v := by
  rcases v with _ | d | x | L | ⟨P, _ | k⟩
  · rw [waveOp_core]
    simp only [zeroMeanField_dead, zeroMeanField_neck, zeroMeanField_core, Finset.sum_const_zero]
    rw [sum_zeroMeanNeck X hA]
    simp
  · simp
  · induction x using Quotient.inductionOn with
    | h P =>
      change waveOp q _ (.neck (Branch.mk P)) = _ * zeroMeanField q X Y A (.neck (Branch.mk P))
      rw [waveOp_neck, zeroMeanField_neck]
      unfold neckOp zeroMeanNeck
      by_cases h : 2 • P = 0
      · have e := eq_neg_of_two_nsmul h
        simp only [if_pos h, zeroMeanField_core, zeroMeanField_ray, e, pow_zero, mul_one, mul_zero,
          zero_add]
        field_simp
      · simp only [if_neg h, zeroMeanField_core, zeroMeanField_ray, neg_neg, pow_zero, mul_one,
          mul_zero, zero_add]
        field_simp
        ring
  · have e := eq_neg_of_two_nsmul L.2
    simp only [waveOp_cap, zeroMeanField_cap, zeroMeanField_ray, e, pow_zero, mul_one]
    field_simp
  · rw [waveOp_ray_zero, gapOp_zeroMeanField hXY hX]
    simp only [zeroMeanField_ray, pow_zero, mul_one, pow_one]
    field_simp
    ring
  · rw [waveOp_ray_succ]
    simp only [zeroMeanField_ray]
    rw [← hXY]
    field_simp
    ring

/-! ### The radial scattering coefficient -/

/-- The radial scattering coefficient `S = -Y j(Y, X)/(X j(X, Y))`: outgoing over incoming amplitude. -/
def radialScattering (t X Y : ℂ) : ℂ := -(Y * jost t Y X) / (X * jost t X Y)

/-- **The scattering coefficient as a rational function of `a = X²`.** The prompt bounce `q/a`, plus the core
response. -/
theorem scattering_eq_prompt_add_core {q t X : ℂ} (hX : X ≠ 0) (h1 : X ^ 2 - q ^ 2 ≠ 0)
    (h2 : X ^ 4 - t * X ^ 2 + q ≠ 0) :
    radialScattering t X (q / X) =
      q / X ^ 2 + q * (q - 1) * (q + 1 - t) * (X ^ 2 + q) / ((X ^ 2 - q ^ 2) * (X ^ 4 - t * X ^ 2 + q)) := by
  obtain ⟨Δ, hΔ⟩ : ∃ Δ, Δ = X ^ 2 - q ^ 2 := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P, P = X ^ 4 - t * X ^ 2 + q := ⟨_, rfl⟩
  obtain ⟨E, hE⟩ : ∃ E, E = (X ^ 2 - 1) * (q ^ 4 - t * q ^ 2 * X ^ 2 + q * X ^ 4) := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K, K = q * (q - 1) * (q + 1 - t) * (X ^ 2 + q) := ⟨_, rfl⟩
  rw [← hΔ] at h1 ⊢
  rw [← hP] at h2 ⊢
  rw [← hK]
  have e1 : X * jost t X (q / X) = -(Δ * P) / X ^ 2 := by
    rw [hΔ, hP]
    unfold jost
    field_simp
    ring
  have e2 : (q / X) * jost t (q / X) X = E / X ^ 4 := by
    rw [hE]
    unfold jost
    field_simp
  have key : E = q * Δ * P + X ^ 2 * K := by
    rw [hE, hΔ, hP, hK]
    ring
  unfold radialScattering
  rw [e1, neg_div, e2, key]
  field_simp

/-- **Causal form.** With `w = X⁻²` and `h = q + 1 - t`, the scattering coefficient is the prompt bounce plus
the core response, as a function of `w`. The coefficients of its expansion are the echoes. -/
theorem scattering_eq_causal {q t X : ℂ} (hX : X ≠ 0) (h1 : X ^ 2 - q ^ 2 ≠ 0)
    (h2 : X ^ 4 - t * X ^ 2 + q ≠ 0) :
    radialScattering t X (q / X) =
      q * (1 / X ^ 2) + q * (q - 1) * (q + 1 - t) * (1 / X ^ 2) ^ 2 * (1 + q * (1 / X ^ 2)) /
        ((1 - q ^ 2 * (1 / X ^ 2)) * (1 - t * (1 / X ^ 2) + q * (1 / X ^ 2) ^ 2)) := by
  rw [scattering_eq_prompt_add_core hX h1 h2]
  have e3 : 1 - q ^ 2 * (1 / X ^ 2) = (X ^ 2 - q ^ 2) / X ^ 2 := by
    field_simp
  have e4 : 1 - t * (1 / X ^ 2) + q * (1 / X ^ 2) ^ 2 = (X ^ 4 - t * X ^ 2 + q) / X ^ 4 := by
    field_simp
  rw [e3, e4]
  field_simp

/-- **Unitarity.** On the circle `|X|² = q`, where `Y = X̄`, the radial scattering coefficient has modulus one
for every real `t`. -/
theorem norm_radialScattering_eq_one {t : ℝ} {X Y : ℂ} (hY : Y = conj X) (hX : X ≠ 0)
    (hj : jost (t : ℂ) X Y ≠ 0) : ‖radialScattering (t : ℂ) X Y‖ = 1 := by
  have hconj : jost (t : ℂ) Y X = conj (jost (t : ℂ) X Y) := by
    unfold jost
    rw [hY]
    simp [Complex.conj_ofReal]
  have hYn : ‖Y‖ = ‖X‖ := by rw [hY, Complex.norm_conj]
  have hXn : ‖X‖ ≠ 0 := norm_ne_zero_iff.mpr hX
  have hjn : ‖jost (t : ℂ) X Y‖ ≠ 0 := norm_ne_zero_iff.mpr hj
  unfold radialScattering
  rw [norm_div, norm_neg, norm_mul, norm_mul, hconj, Complex.norm_conj, hYn]
  field_simp

/-- **The prompt part on the zero-mean sectors is also unitary.** -/
theorem norm_div_conj {X : ℂ} (hX : X ≠ 0) : ‖conj X / X‖ = 1 := by
  rw [norm_div, Complex.norm_conj]
  exact div_self (norm_ne_zero_iff.mpr hX)

end GaloisForLFunctions.ArithmeticScatteringHolography

end
