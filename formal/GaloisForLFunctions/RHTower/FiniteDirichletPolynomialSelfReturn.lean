import GaloisForLFunctions.RHTower.EntireDirichletPolynomial
import GaloisForLFunctions.HTGeometry.BohrFiniteRecurrence
import GaloisForLFunctions.HTGeometry.AlmostPeriodicReturnDensity

/-!
# Positive-density self-return of finite Dirichlet polynomials

A finite family of logarithmic phases is almost periodic. Its returns near the
identity have positive lower Lebesgue density. On a compact set, the finitely
many coefficient functions have a uniform bound, so these phase returns give
uniform self-return of the actual entire Dirichlet polynomial.
-/

open Complex Filter Topology MeasureTheory Set
open GaloisForLFunctions GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

/-- Times when a finite Dirichlet polynomial returns uniformly on `K`. -/
def edPolyReturnSet (a : ℕ → ℂ) (s : Finset ℕ) (K : Set ℂ) (ε : ℝ) : Set ℝ :=
  {τ | ∀ z ∈ K, ‖edPoly a s (z + (τ : ℂ) * I) - edPoly a s z‖ < ε}

theorem nat_cpow_neg_vertical_translate {n : ℕ} (hn : 0 < n) (z : ℂ) (τ : ℝ) :
    ((n : ℝ) : ℂ) ^ (-(z + (τ : ℂ) * I)) =
      ((n : ℝ) : ℂ) ^ (-z) * bohrChar (Real.log n) τ := by
  have hpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hne : ((n : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [Complex.cpow_def_of_ne_zero hne, Complex.cpow_def_of_ne_zero hne,
    bohrChar, ← Complex.exp_add, ← Complex.ofReal_log hpos.le]
  congr 1
  push_cast
  ring

/-- Unconditional finite-head recurrence, uniformly on every compact set, with
a strictly positive lower density of return times. -/
theorem exists_pos_density_edPolyReturnSet (a : ℕ → ℂ) {s : Finset ℕ}
    (hs : ∀ n ∈ s, 1 ≤ n) {K : Set ℂ} (hK : IsCompact K)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ᶠ T : ℝ in atTop,
      ENNReal.ofReal (κ * T) ≤ volume (edPolyReturnSet a s K ε ∩ Icc 0 T) := by
  classical
  let G : ℂ → ℝ := fun z => ∑ n ∈ s, ‖a n * ((n : ℝ) : ℂ) ^ (-z)‖
  have hG : Continuous G := by
    apply continuous_finsetSum
    intro n hn
    have hpos : (0 : ℝ) < n := by exact_mod_cast hs n hn
    have hne : ((n : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hpos.ne'
    have hd : Differentiable ℂ (fun z : ℂ => a n * ((n : ℝ) : ℂ) ^ (-z)) :=
      fun z => (DifferentiableAt.const_cpow (differentiable_id.neg z)
        (Or.inl hne)).const_mul (a n)
    exact hd.continuous.norm
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hG.continuousOn
  let M : ℝ := max C 0
  have hM : 0 ≤ M := le_max_right _ _
  have hGM {z : ℂ} (hz : z ∈ K) : G z ≤ M :=
    (le_abs_self _).trans ((hC z hz).trans (le_max_left _ _))
  let δ : ℝ := ε / (M + 1)
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hMδ : M * δ < ε := by
    dsimp [δ]
    rw [← mul_div_assoc, div_lt_iff₀ (by positivity : 0 < M + 1)]
    nlinarith
  let e := Fintype.equivFin s
  let u : Fin (Fintype.card s) → ℝ := fun j => Real.log ((e.symm j).val : ℝ)
  obtain ⟨κ, hκ, hdensity⟩ := exists_pos_return_density_of_isBohrAlmostPeriodic
    (continuous_bohrCharVector u)
    (isBohrAlmostPeriodic_bohrCharVector _ u) hδ
  refine ⟨κ, hκ, hdensity.mono fun T hT => hT.trans (measure_mono ?_)⟩
  rintro τ ⟨hτ, hτT⟩
  refine ⟨?_, hτT⟩
  intro z hz
  have hphase (n : ℕ) (hn : n ∈ s) : ‖bohrChar (Real.log n) τ - 1‖ ≤ δ := by
    have hc := (norm_le_pi_norm (bohrCharVector u τ - bohrCharVector u 0)
      (e ⟨n, hn⟩)).trans hτ.le
    simp only [Pi.sub_apply, bohrCharVector_zero] at hc
    simpa only [bohrCharVector, u, Equiv.symm_apply_apply] using hc
  have hdiff : edPoly a s (z + (τ : ℂ) * I) - edPoly a s z =
      ∑ n ∈ s, (a n * ((n : ℝ) : ℂ) ^ (-z)) * (bohrChar (Real.log n) τ - 1) := by
    rw [edPoly, edPoly, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    rw [nat_cpow_neg_vertical_translate (hs n hn) z τ]
    ring
  calc
    ‖edPoly a s (z + (τ : ℂ) * I) - edPoly a s z‖
      ≤ ∑ n ∈ s, ‖a n * ((n : ℝ) : ℂ) ^ (-z)‖ * δ := by
        rw [hdiff]
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun n hn => by
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (hphase n hn) (norm_nonneg _))
    _ = G z * δ := (Finset.sum_mul ..).symm
    _ ≤ M * δ := mul_le_mul_of_nonneg_right (hGM hz) hδ.le
    _ < ε := hMδ

end RHTower
