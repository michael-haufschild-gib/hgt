import GaloisForLFunctions.RHTower.RoutePPrimitiveBurnolWardHerglotzTangent

open Complex Matrix
open scoped ComplexOrder

namespace RHTower

noncomputable section

/-- Natural entrywise polarization of the one-mode Ward--Herglotz tangent
that is linear in its left response and conjugate-linear in its right
response, restricted to a common positive real external node. -/
def xiWardCrossModeHerglotzPolarization {n : ℕ}
    (x : ℝ) (a : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j =>
    (((1 / x) * (1 / (x + a i) + 1 / (x + a j)) : ℝ) : ℂ)

theorem xiWardCrossModeHerglotzPolarization_apply
    {n : ℕ} (x : ℝ) (a : Fin n → ℝ)
    (i j : Fin n) :
    xiWardCrossModeHerglotzPolarization x a i j =
      (((1 / x) * (1 / (x + a i) + 1 / (x + a j)) : ℝ) : ℂ) := by
  rfl

/-- On real data this is exactly the natural entrywise polarization of the
one-mode Ward response. -/
theorem xiWardCrossModeHerglotzPolarization_eq_response
    {n : ℕ} {x : ℝ} (hx : x ≠ 0) (a : Fin n → ℝ)
    (i j : Fin n) :
    xiWardCrossModeHerglotzPolarization x a i j =
      (2 * ((((x + a i : ℝ) : ℂ))⁻¹) +
        star (2 * ((((x + a j : ℝ) : ℂ))⁻¹))) /
          (((x : ℝ) : ℂ) + star (((x : ℝ) : ℂ))) := by
  simp [xiWardCrossModeHerglotzPolarization]
  field_simp [hx]
  ring

/-- Every diagonal entry is exactly the corresponding P-G197 one-mode
Herglotz tangent at the common external node. -/
theorem xiWardCrossModeHerglotzPolarization_diag_eq_mode
    {n : ℕ} {x : ℝ} (hx : 0 < x) (a : Fin n → ℝ)
    (i : Fin n) :
    xiWardCrossModeHerglotzPolarization x a i i =
      xiWardModeHerglotzPickMatrix
        (fun _ : Fin n => (x : ℂ)) (a i : ℂ) i i := by
  simp [xiWardCrossModeHerglotzPolarization,
    xiWardModeHerglotzPickMatrix]
  field_simp [hx.ne']
  ring

/-- The two-mode determinant is the negative square of the difference of
the two resolvent values. -/
theorem det_xiWardCrossModeHerglotzPolarization_two
    (x a b : ℝ) :
    (xiWardCrossModeHerglotzPolarization x ![a, b]).det =
      ((-((1 / (x + a) - 1 / (x + b)) / x) ^ 2 : ℝ) : ℂ) := by
  rw [Matrix.det_fin_two]
  simp only [xiWardCrossModeHerglotzPolarization]
  push_cast
  ring

/-- Distinct modes make the natural cross-mode polarization indefinite
already on a two-point packet. -/
theorem not_posSemidef_xiWardCrossModeHerglotzPolarization_two
    {x a b : ℝ} (hx : 0 < x) (hab : a ≠ b) :
    ¬ (xiWardCrossModeHerglotzPolarization x ![a, b]).PosSemidef := by
  intro hpsd
  have hdet := hpsd.det_nonneg
  rw [det_xiWardCrossModeHerglotzPolarization_two x a b] at hdet
  have hdiff : 1 / (x + a) - 1 / (x + b) ≠ 0 := by
    rw [sub_ne_zero, one_div, one_div]
    intro h
    apply hab
    exact add_left_cancel (_root_.inv_inj.mp h)
  have hquot : (1 / (x + a) - 1 / (x + b)) / x ≠ 0 :=
    div_ne_zero hdiff hx.ne'
  have hsqpos : (0 : ℝ) <
      ((1 / (x + a) - 1 / (x + b)) / x) ^ 2 :=
    sq_pos_of_ne_zero hquot
  have hdetReal := (RCLike.nonneg_iff.mp hdet).1
  change 0 ≤
    (((-((1 / (x + a) - 1 / (x + b)) / x) ^ 2 : ℝ) : ℂ).re) at hdetReal
  rw [Complex.ofReal_re] at hdetReal
  linarith

/-- Exact two-mode classification: in the positive chamber, the natural
cross-mode polarization is PSD only on the diagonal where the two modes
coincide. -/
theorem xiWardCrossModeHerglotzPolarization_two_posSemidef_iff
    {x a b : ℝ} (hx : 0 < x) (ha : 0 < a) (hb : 0 < b) :
    (xiWardCrossModeHerglotzPolarization x ![a, b]).PosSemidef ↔
      a = b := by
  constructor
  · intro hpsd
    by_contra hab
    exact not_posSemidef_xiWardCrossModeHerglotzPolarization_two hx hab hpsd
  · intro hab
    subst b
    let c : ℝ := 2 / (x * (x + a))
    have hc : 0 ≤ c := by
      dsimp [c]
      positivity
    have heq :
        xiWardCrossModeHerglotzPolarization x ![a, a] =
          c • Matrix.gram ℂ (fun _ : Fin 2 => (1 : ℂ)) := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [xiWardCrossModeHerglotzPolarization, Matrix.gram_apply, c]
      all_goals field_simp [hx.ne', (add_pos hx ha).ne']; ring
    rw [heq]
    exact (Matrix.posSemidef_gram ℂ _).smul hc

end

end RHTower
