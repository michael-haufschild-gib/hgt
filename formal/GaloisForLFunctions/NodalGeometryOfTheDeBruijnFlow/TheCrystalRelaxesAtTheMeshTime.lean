import Mathlib.NumberTheory.ZetaValues
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# The crystal relaxes at the mesh time

The linearization of the Dyson flow `ẋ_j = 2 Σ_{k ≠ j} 1/(x_j − x_k)` at a lattice `x_j = g j` of spacing `g` is the operator

`(L u)_j = −(2/g²) Σ_{m ≥ 1} (2u_j − u_{j+m} − u_{j−m})/m²`.

It is diagonal on plane waves: `L e^{ijξ} = −λ(ξ) e^{ijξ}`, with the exact symbol (`lattice_eigen`)

`λ(ξ) = ξ(2π − ξ)/g²`,  `0 ≤ ξ ≤ 2π`.

So the time scale of the flow on a crystal is the mesh time `t ≍ g²`: for a crystal of density `≍ log X` this is the variable `τ = t log²X`. The fastest mode `ξ = π` decays at rate `π²/g²`, the pair mode at the mesh scale. At long
wavelength `λ(ξ) ≈ 2π|k|/g`, `k = ξ/g`, so the flow is the Poisson semigroup `e^{−h|k|}` at height `h = 2πt/g`: for `g = 2π/log X`, the height `h = t log X`. Near the crystal the time scale `t ≍ 1/log X` of the
collision-free horizon is the time in which modes at unit wavelength relax.
-/

open Real Filter Topology

namespace GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow

noncomputable section

/-- **The symbol as a Fourier series.** `Σ_{m ≥ 1} (1 − cos mξ)/m² = ξ(2π − ξ)/4` on `[0, 2π]`. -/
theorem hasSum_one_sub_cos_div_sq {ξ : ℝ} (h0 : 0 ≤ ξ) (h1 : ξ ≤ 2 * π) :
    HasSum (fun m : ℕ => (1 - cos ((m : ℝ) * ξ)) / (m : ℝ) ^ 2) (ξ * (2 * π - ξ) / 4) := by
  have hx : ξ / (2 * π) ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · positivity
    · rw [div_le_one (by positivity)]
      exact h1
  have hc := hasSum_one_div_nat_pow_mul_cos (k := 1) one_ne_zero hx
  have hz := hasSum_zeta_two
  have hb : (Polynomial.map (algebraMap ℚ ℝ) (Polynomial.bernoulli (2 * 1))).eval (ξ / (2 * π)) =
      (ξ / (2 * π)) ^ 2 - ξ / (2 * π) + 1 / 6 := by
    simp [Polynomial.bernoulli, Finset.sum_range_succ, Nat.choose]
    ring
  rw [hb] at hc
  have hsub := hz.sub hc
  have hpi : π ≠ 0 := pi_ne_zero
  have hfun : (fun m : ℕ => (1 - cos ((m : ℝ) * ξ)) / (m : ℝ) ^ 2) =
      fun b : ℕ => 1 / (b : ℝ) ^ 2 - 1 / (b : ℝ) ^ (2 * 1) * cos (2 * π * (b : ℝ) * (ξ / (2 * π))) := by
    funext m
    have harg : 2 * π * (m : ℝ) * (ξ / (2 * π)) = (m : ℝ) * ξ := by
      field_simp
    rw [harg]
    ring
  have hval : ξ * (2 * π - ξ) / 4 = π ^ 2 / 6 -
      (-1) ^ (1 + 1) * (2 * π) ^ (2 * 1) / 2 / ((2 * 1).factorial : ℝ) *
        ((ξ / (2 * π)) ^ 2 - ξ / (2 * π) + 1 / 6) := by
    have hfac : ((2 * 1).factorial : ℝ) = 2 := by norm_num [Nat.factorial]
    rw [hfac]
    field_simp
    ring
  rw [hfun, hval]
  exact hsub

/-- The linearized Dyson operator at a lattice of spacing `g`. -/
def latticeDyson (g : ℝ) (u : ℤ → ℂ) (j : ℤ) : ℂ :=
  -((2 / g ^ 2 : ℝ) : ℂ) * ∑' m : ℕ, (2 * u j - u (j + m) - u (j - m)) / ((m : ℝ) : ℂ) ^ 2

/-- A plane wave on the lattice. -/
def planeWave (ξ : ℝ) (j : ℤ) : ℂ := Complex.exp (Complex.I * ((j : ℝ) * ξ : ℝ))

/-- **The symbol of the crystal.** Plane waves are eigenfunctions of the linearized Dyson operator, with eigenvalue `−ξ(2π − ξ)/g²`. -/
theorem lattice_eigen {g ξ : ℝ} (hg : g ≠ 0) (h0 : 0 ≤ ξ) (h1 : ξ ≤ 2 * π) (j : ℤ) :
    latticeDyson g (planeWave ξ) j = -((ξ * (2 * π - ξ) / g ^ 2 : ℝ) : ℂ) * planeWave ξ j := by
  have hterm (m : ℕ) : (2 * planeWave ξ j - planeWave ξ (j + m) - planeWave ξ (j - m)) / ((m : ℝ) : ℂ) ^ 2 =
      (2 * planeWave ξ j) * (((1 - cos ((m : ℝ) * ξ)) / (m : ℝ) ^ 2 : ℝ) : ℂ) := by
    have h2 : planeWave ξ (j + m) = planeWave ξ j * Complex.exp (Complex.I * ((m : ℝ) * ξ : ℝ)) := by
      unfold planeWave
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    have h3 : planeWave ξ (j - m) = planeWave ξ j * Complex.exp (-(Complex.I * ((m : ℝ) * ξ : ℝ))) := by
      unfold planeWave
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    have h4 : (Complex.cos (((m : ℝ) * ξ : ℝ) : ℂ)) * 2 =
        Complex.exp (Complex.I * ((m : ℝ) * ξ : ℝ)) + Complex.exp (-(Complex.I * ((m : ℝ) * ξ : ℝ))) := by
      rw [Complex.cos]
      rw [show ((((m : ℝ) * ξ : ℝ) : ℂ)) * Complex.I = Complex.I * (((m : ℝ) * ξ : ℝ) : ℂ) by ring,
        show -(((m : ℝ) * ξ : ℝ) : ℂ) * Complex.I = -(Complex.I * (((m : ℝ) * ξ : ℝ) : ℂ)) by ring]
      ring
    rw [h2, h3]
    push_cast at h4 ⊢
    rw [show (2 * planeWave ξ j - planeWave ξ j * Complex.exp (Complex.I * ((m : ℂ) * (ξ : ℂ))) -
        planeWave ξ j * Complex.exp (-(Complex.I * ((m : ℂ) * (ξ : ℂ))))) =
        planeWave ξ j * (2 - (Complex.exp (Complex.I * ((m : ℂ) * (ξ : ℂ))) +
          Complex.exp (-(Complex.I * ((m : ℂ) * (ξ : ℂ)))))) by ring, ← h4]
    ring
  have hsum := ((hasSum_one_sub_cos_div_sq h0 h1).mapL Complex.ofRealCLM).mul_left (2 * planeWave ξ j)
  simp only [Complex.ofRealCLM_apply] at hsum
  unfold latticeDyson
  rw [tsum_congr hterm, hsum.tsum_eq]
  have hgc : (g : ℂ) ≠ 0 := by exact_mod_cast hg
  push_cast
  field_simp
  ring

/-- The symbol is nonnegative, vanishes only at `ξ ∈ {0, 2π}`, and it is largest at the pair mode `ξ = π`, with value `π²/g²`. -/
theorem symbol_le {g ξ : ℝ} (hg : g ≠ 0) : ξ * (2 * π - ξ) / g ^ 2 ≤ π ^ 2 / g ^ 2 := by
  have : ξ * (2 * π - ξ) ≤ π ^ 2 := by nlinarith only [sq_nonneg (ξ - π)]
  exact div_le_div_of_nonneg_right this (by positivity)

/-- The linearized Dyson semigroup on a plane wave is exponential at the rate of the symbol. -/
theorem hasDerivAt_latticeMode {g ξ : ℝ} (hg : g ≠ 0) (h0 : 0 ≤ ξ) (h1 : ξ ≤ 2 * π) (j : ℤ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => Complex.exp (-((ξ * (2 * π - ξ) / g ^ 2 * s : ℝ) : ℂ)) * planeWave ξ j)
      (Complex.exp (-((ξ * (2 * π - ξ) / g ^ 2 * t : ℝ) : ℂ)) * latticeDyson g (planeWave ξ) j) t := by
  rw [lattice_eigen hg h0 h1]
  have h2 : HasDerivAt (fun s : ℝ => -((ξ * (2 * π - ξ) / g ^ 2 * s : ℝ) : ℂ))
      (-((ξ * (2 * π - ξ) / g ^ 2 : ℝ) : ℂ)) t := by
    have h3 : HasDerivAt (fun s : ℝ => ξ * (2 * π - ξ) / g ^ 2 * s) (ξ * (2 * π - ξ) / g ^ 2) t := by
      simpa only [mul_one, id] using (hasDerivAt_id t).const_mul (ξ * (2 * π - ξ) / g ^ 2)
    exact h3.ofReal_comp.fun_neg
  have h4 := (h2.cexp).mul_const (planeWave ξ j)
  refine h4.congr_deriv ?_
  ring

end

end GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow
