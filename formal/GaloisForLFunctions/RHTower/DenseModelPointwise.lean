import GaloisForLFunctions.RHTower.DenseModelBohr

/-!
# Fourier inversion and the pointwise bound for the dense model

`unitFourier_inversion` is Fourier inversion on `(ZMod q)ˣ` for the family of Dirichlet characters
modulo `q`, and `sum_normSq_bohrAvg` evaluates `∑_χ ‖E_{b ∈ B} χ(b)‖²` as `φ(q)/#B`.

Together with the Fourier identity for the dense model, these give the pointwise bound
`norm_denseModel_sub_mass_le`: if every nonprincipal Fourier coefficient of `F` is at most `M`,
then the model stays within `M·φ(q)/#B` of the total mass of `F`.  This is item (i) of the
multiplicative dense model theorem of Matomäki--Teräväinen — the statement that the model is
bounded, once `F` is taken to be a pseudorandom majorant and `B` is large.
-/

open Finset

noncomputable section

namespace RHTower

/-- **Fourier inversion on the unit group.** -/
theorem unitFourier_inversion (n : ℕ) (G : (ZMod (n + 1))ˣ → ℂ) (a : (ZMod (n + 1))ˣ) :
    (((n + 1).totient : ℂ)) * G a
      = ∑ χ : DirichletCharacter ℂ (n + 1),
          (∑ u : (ZMod (n + 1))ˣ, G u * (starRingEnd ℂ) (χ (u : ZMod (n + 1))))
            * χ (a : ZMod (n + 1)) := by
  classical
  have hswap : ∑ χ : DirichletCharacter ℂ (n + 1),
      (∑ u : (ZMod (n + 1))ˣ, G u * (starRingEnd ℂ) (χ (u : ZMod (n + 1))))
        * χ (a : ZMod (n + 1))
      = ∑ u : (ZMod (n + 1))ˣ, G u
          * ∑ χ : DirichletCharacter ℂ (n + 1),
              χ (a : ZMod (n + 1)) * χ ((u : ZMod (n + 1))⁻¹) := by
    have hL : ∀ χ : DirichletCharacter ℂ (n + 1),
        (∑ u : (ZMod (n + 1))ˣ, G u * (starRingEnd ℂ) (χ (u : ZMod (n + 1))))
          * χ (a : ZMod (n + 1))
        = ∑ u : (ZMod (n + 1))ˣ,
            G u * (χ (a : ZMod (n + 1)) * χ ((u : ZMod (n + 1))⁻¹)) := by
      intro χ
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun u _ => ?_)
      rw [conj_char n χ u]
      ring
    rw [Finset.sum_congr rfl (fun χ _ => hL χ), Finset.sum_comm]
    refine Finset.sum_congr rfl (fun u _ => ?_)
    rw [Finset.mul_sum]
  rw [hswap]
  have hker : ∀ u : (ZMod (n + 1))ˣ,
      (∑ χ : DirichletCharacter ℂ (n + 1),
        χ (a : ZMod (n + 1)) * χ ((u : ZMod (n + 1))⁻¹))
        = if a = u then (((n + 1).totient : ℂ)) else 0 :=
    fun u => dirichletCharacterFamily_kernel n a u
  rw [Finset.sum_congr rfl (fun u _ => by rw [hker u])]
  have hfin : ∑ u : (ZMod (n + 1))ˣ,
      G u * (if a = u then (((n + 1).totient : ℂ)) else 0)
      = G a * (((n + 1).totient : ℂ)) := by
    rw [Finset.sum_congr rfl (fun u _ => by rw [mul_ite, mul_zero])]
    rw [Finset.sum_ite_eq Finset.univ a (fun u => G u * (((n + 1).totient : ℂ)))]
    simp
  rw [hfin]
  ring


/-- Parseval for the normalised Bohr averages. -/
theorem sum_normSq_bohrAvg (n : ℕ) (B : Finset (ZMod (n + 1))ˣ) (hB : B.Nonempty) :
    ∑ χ : DirichletCharacter ℂ (n + 1), ‖bohrAvg n B χ‖ ^ 2
      = ((n + 1).totient : ℝ) / (B.card : ℝ) := by
  have hcardR : (0 : ℝ) < (B.card : ℝ) := by exact_mod_cast Finset.card_pos.2 hB
  have hexp : ∀ χ : DirichletCharacter ℂ (n + 1),
      ‖bohrAvg n B χ‖ ^ 2
        = ((B.card : ℝ))⁻¹ * ((B.card : ℝ))⁻¹ * ‖∑ b ∈ B, χ (b : ZMod (n + 1))‖ ^ 2 := by
    intro χ
    rw [bohrAvg, norm_mul, norm_inv, Complex.norm_natCast, mul_pow]
    ring
  rw [Finset.sum_congr rfl (fun χ _ => hexp χ), ← Finset.mul_sum, sum_normSq_setCharSum]
  field_simp

/-- **Item (i) of the dense model theorem.**  If every nonprincipal Fourier coefficient of `F` is
at most `M`, then the model differs from the total mass of `F` by at most `M·φ(q)/#B`. -/
theorem norm_denseModel_sub_mass_le (n : ℕ) (F : (ZMod (n + 1))ˣ → ℝ)
    (B : Finset (ZMod (n + 1))ˣ) (hB : B.Nonempty) {M : ℝ} (hM : 0 ≤ M)
    (hsmall : ∀ χ : DirichletCharacter ℂ (n + 1), χ ≠ 1 → ‖unitFourier n F χ‖ ≤ M)
    (a : (ZMod (n + 1))ˣ) :
    |denseModel n F B a - ∑ u : (ZMod (n + 1))ˣ, F u|
      ≤ M * (((n + 1).totient : ℝ) / (B.card : ℝ)) := by
  classical
  have hphi : ((((n + 1).totient : ℂ))) ≠ 0 := by
    have hpos : 0 < (n + 1).totient := Nat.totient_pos.2 (by omega)
    exact_mod_cast Nat.cast_ne_zero.2 hpos.ne'
  have hcoeff : ∀ χ : DirichletCharacter ℂ (n + 1),
      (∑ u : (ZMod (n + 1))ˣ, ((denseModel n F B u : ℝ) : ℂ)
        * (starRingEnd ℂ) (χ (u : ZMod (n + 1))))
        = (((n + 1).totient : ℂ)) * (((‖bohrAvg n B χ‖ ^ 2 : ℝ) : ℂ) * unitFourier n F χ) := by
    intro χ
    have h := denseModel_fourier_real n F B hB χ
    rw [← h]
    field_simp
  have hinv := unitFourier_inversion n (fun u => ((denseModel n F B u : ℝ) : ℂ)) a
  have hval : (((n + 1).totient : ℂ)) * (denseModel n F B a : ℂ)
      = (((n + 1).totient : ℂ)) * ∑ χ : DirichletCharacter ℂ (n + 1),
          (((‖bohrAvg n B χ‖ ^ 2 : ℝ) : ℂ) * unitFourier n F χ) * χ (a : ZMod (n + 1)) := by
    rw [hinv, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun χ _ => by rw [hcoeff χ]; ring)
  have hmodel : (denseModel n F B a : ℂ)
      = ∑ χ : DirichletCharacter ℂ (n + 1),
          (((‖bohrAvg n B χ‖ ^ 2 : ℝ) : ℂ) * unitFourier n F χ) * χ (a : ZMod (n + 1)) :=
    mul_left_cancel₀ hphi hval
  have hone : ((‖bohrAvg n B (1 : DirichletCharacter ℂ (n + 1))‖ ^ 2 : ℝ) : ℂ)
      * unitFourier n F (1 : DirichletCharacter ℂ (n + 1))
      * (1 : DirichletCharacter ℂ (n + 1)) (a : ZMod (n + 1))
      = ((∑ u : (ZMod (n + 1))ˣ, F u : ℝ) : ℂ) := by
    rw [bohrAvg_one n B hB, unitFourier]
    push_cast
    simp [MulChar.one_apply_coe]
  have hsplit := Finset.add_sum_erase (Finset.univ : Finset (DirichletCharacter ℂ (n + 1)))
    (fun χ => (((‖bohrAvg n B χ‖ ^ 2 : ℝ) : ℂ) * unitFourier n F χ) * χ (a : ZMod (n + 1)))
    (Finset.mem_univ (1 : DirichletCharacter ℂ (n + 1)))
  have hdiff : ((denseModel n F B a : ℝ) : ℂ) - ((∑ u : (ZMod (n + 1))ˣ, F u : ℝ) : ℂ)
      = ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ (n + 1))).erase 1,
          (((‖bohrAvg n B χ‖ ^ 2 : ℝ) : ℂ) * unitFourier n F χ) * χ (a : ZMod (n + 1)) := by
    rw [hmodel, ← hsplit, hone]
    ring
  have hnorm : |denseModel n F B a - ∑ u : (ZMod (n + 1))ˣ, F u|
      = ‖((denseModel n F B a : ℝ) : ℂ) - ((∑ u : (ZMod (n + 1))ˣ, F u : ℝ) : ℂ)‖ := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  rw [hnorm, hdiff]
  have hterm : ∀ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ (n + 1))).erase 1,
      ‖(((‖bohrAvg n B χ‖ ^ 2 : ℝ) : ℂ) * unitFourier n F χ) * χ (a : ZMod (n + 1))‖
        ≤ ‖bohrAvg n B χ‖ ^ 2 * M := by
    intro χ hχ
    have hne : χ ≠ 1 := (Finset.mem_erase.1 hχ).1
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity), norm_unitChar n χ a, mul_one]
    exact mul_le_mul_of_nonneg_left (hsmall χ hne) (by positivity)
  refine le_trans (norm_sum_le _ _) (le_trans (Finset.sum_le_sum hterm) ?_)
  have hsub : ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ (n + 1))).erase 1,
      ‖bohrAvg n B χ‖ ^ 2 * M
      ≤ ∑ χ : DirichletCharacter ℂ (n + 1), ‖bohrAvg n B χ‖ ^ 2 * M := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) ?_
    intro χ _ _
    positivity
  refine le_trans hsub ?_
  rw [← Finset.sum_mul, sum_normSq_bohrAvg n B hB]
  linarith [le_of_eq (mul_comm (((n + 1).totient : ℝ) / (B.card : ℝ)) M)]

end RHTower
