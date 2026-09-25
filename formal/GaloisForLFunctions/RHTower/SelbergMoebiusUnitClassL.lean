import GaloisForLFunctions.RHTower.SelbergEisensteinCuspScattering

open Complex LSeries
open scoped LSeries.notation ArithmeticFunction.Moebius

/-!
# The Möbius series in a unit class and its continuation to `Re w ≥ 1`

For a unit `u` of `ℤ/N`, orthogonality of Dirichlet characters gives
`μ(n)[(n,N)=1][n ≡ u] = φ(N)^{-1} Σ_χ χ(u)^{-1} χ(n) μ(n)` (`muChiU_eq`), and `L(χμ, w) = 1/L(w, χ)` for `Re w > 1`, so
`L(μχ_N δ_u, w) = L_u(w) := φ(N)^{-1} Σ_χ χ(u)^{-1}/L(w, χ)` (`LSeries_muChiU_eq`). Since `L(w, χ)` does not vanish on
`Re w ≥ 1` (except at the pole `w = 1` of the principal character), `L_u` is holomorphic at every `w ≠ 1` with
`Re w ≥ 1` (`differentiableAt_LU`).
-/

namespace GaloisForLFunctions.RHTower.SelbergMoebiusUnitClassL
open GaloisForLFunctions.RHTower.SelbergEisensteinCuspScattering GaloisForLFunctions.RHTower.TotientMulLSeries
  GaloisForLFunctions.RHTower.TotientMulMoebius

variable (N : ℕ) [NeZero N]

/-- `L_u(w) = φ(N)^{-1} Σ_χ χ(u)^{-1} / L(w, χ)`: the continued Möbius series in the unit class `u`. -/
noncomputable def LU (u : (ZMod N)ˣ) (w : ℂ) : ℂ :=
  (N.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ N, χ ((u : ZMod N)⁻¹) * (DirichletCharacter.LFunction χ w)⁻¹

theorem muChiU_eq (u : (ZMod N)ˣ) {n : ℕ} (hn : n ≠ 0) :
    muChiU N u n = (N.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ N, χ ((u : ZMod N)⁻¹) * (χ n * (μ n : ℂ)) := by
  have hφ : (N.totient : ℂ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N))).ne'
  have horth := DirichletCharacter.sum_char_inv_mul_char_eq ℂ (u.isUnit) (n : ZMod N)
  have e : ∑ χ : DirichletCharacter ℂ N, χ ((u : ZMod N)⁻¹) * (χ n * (μ n : ℂ)) =
      (∑ χ : DirichletCharacter ℂ N, χ ((u : ZMod N)⁻¹) * χ n) * (μ n : ℂ) := by
    rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro χ _; ring
  rw [e, horth]
  unfold muChiU muChi
  simp only [ArithmeticFunction.pmul_apply, chi, ArithmeticFunction.coe_mk]
  have hcu : (n : ZMod N) = u → n.Coprime N := fun h =>
    (ZMod.isUnit_iff_coprime n N).mp (h ▸ u.isUnit)
  split_ifs with h1 h2 h3 h4 h5 h6
  · push_cast; field_simp
  · exact absurd h2.symm h3
  · exact absurd h4.symm h2
  · simp
  · exact absurd ⟨hn, hcu h5⟩ h1
  · exact absurd h5.symm h6
  · rename_i h7; exact absurd h7.symm h5
  · simp

/-- `L(w, μχ_N δ_u) = L_u(w)` for `Re w > 1`. -/
theorem LSeries_muChiU_eq {u : (ZMod N)ˣ} {w : ℂ} (hw : 1 < w.re) : LSeries (muChiU N u) w = LU N u w := by
  rw [LSeries_congr (fun hn => muChiU_eq N u hn)]
  have hs : ∀ χ : DirichletCharacter ℂ N, LSeriesSummable (fun n : ℕ => χ ((u : ZMod N)⁻¹) * (χ n * (μ n : ℂ))) w := by
    intro χ
    have h := DirichletCharacter.LSeriesSummable_mul χ (ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hw)
    exact (h.smul (χ ((u : ZMod N)⁻¹))).congr' _ (Filter.Eventually.of_forall (fun n => by simp [Pi.mul_apply]))
  have e1 : (fun n : ℕ => (N.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ N, χ ((u : ZMod N)⁻¹) * (χ n * (μ n : ℂ))) =
      (N.totient : ℂ)⁻¹ • ∑ χ : DirichletCharacter ℂ N, fun n : ℕ => χ ((u : ZMod N)⁻¹) * (χ n * (μ n : ℂ)) := by
    funext n; simp [Finset.sum_apply]
  rw [e1, LSeries_smul, LSeries_sum (fun χ _ => hs χ), LU]
  congr 1
  apply Finset.sum_congr rfl
  intro χ _
  have e2 : (fun n : ℕ => χ ((u : ZMod N)⁻¹) * (χ n * (μ n : ℂ))) =
      χ ((u : ZMod N)⁻¹) • (↗χ * ↗μ) := by funext n; simp [Pi.mul_apply]
  rw [e2, LSeries_smul]
  have h1 := DirichletCharacter.LSeries.mul_mu_eq_one χ hw
  rw [DirichletCharacter.LFunction_eq_LSeries χ hw]
  congr 1
  exact (eq_inv_of_mul_eq_one_right h1)

/-- **Holomorphy of `L_u`** at every `w ≠ 1` with `Re w ≥ 1`. -/
theorem differentiableAt_LU (u : (ZMod N)ˣ) {w : ℂ} (hw : 1 ≤ w.re) (hw1 : w ≠ 1) :
    DifferentiableAt ℂ (LU N u) w := by
  unfold LU
  refine DifferentiableAt.const_mul ?_ _
  have : (fun w => ∑ χ : DirichletCharacter ℂ N, χ ((u : ZMod N)⁻¹) * (DirichletCharacter.LFunction χ w)⁻¹) =
      ∑ χ : DirichletCharacter ℂ N, fun w => χ ((u : ZMod N)⁻¹) * (DirichletCharacter.LFunction χ w)⁻¹ := by
    funext w; simp [Finset.sum_apply]
  rw [this]
  refine DifferentiableAt.sum (fun χ _ => ?_)
  exact ((DirichletCharacter.differentiableAt_LFunction χ w (Or.inl hw1)).inv
    (DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inr hw1) hw)).const_mul _

end GaloisForLFunctions.RHTower.SelbergMoebiusUnitClassL
