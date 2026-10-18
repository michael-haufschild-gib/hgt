import GaloisForLFunctions.RHTower.WeilMarkovPoleCapacity

/-! Hyperbolic pole parity decoupling, odd-mode sinh-capacity thresholds, and
creation-potential aperture drift in the Weil–Markov–pole decomposition.

In the exact finite-aperture Weil decomposition (`weil_eq_markovForm_add_pole`),
`W(g) = M_N(g) + coshPairing(g)^2 / 2 - sinhPairing(g)^2 / 2`,
where `M_N(g) = V_N ‖g‖_2^2 + levyJump(g) + primeJump_N(g)` is Markovian and the
hyperbolic pole plane `coshPairing(g)^2 / 2 - sinhPairing(g)^2 / 2` is the sole
anti-Markovian component.

We prove:
1. Exact parity vanishing: `coshPairing g = 0` for every odd function `g`, and
   `sinhPairing g = 0` for every even function `g`.
2. Orthogonal parity diagonalization of the hyperbolic pole form: on any linear
   combination `c g_even + d g_odd`, the cosh functional reads only the even
   component, the sinh functional reads only the odd component, and the pole
   quadratic form splits without cross-terms into
   `c^2 coshPairing(g_even)^2 / 2 - d^2 sinhPairing(g_odd)^2 / 2`.
3. Even-mode stabilization and odd-mode sinh-capacity classification (`iff`):
   for even `g ∈ C²_c(ℝ)`, `W(g) = M_N(g) + coshPairing(g)^2 / 2 ≥ M_N(g)`;
   for odd `g ∈ C²_c(ℝ)`, `W(g) = M_N(g) - sinhPairing(g)^2 / 2`, so
   `0 ≤ W(g) ↔ sinhPairing(g)^2 ≤ 2 M_N(g)` and
   `W(g) < 0 ↔ M_N(g) < sinhPairing(g)^2 / 2`.
4. Exact creation-potential drift across prime apertures `2 ≤ N₁ ≤ N₂`:
   `V_{N₁} - V_{N₂} = 2 ∑_{n ∈ (N₁, N₂]} Λ(n) / √n ≥ 0`. -/

open Complex MeasureTheory Set Filter
open scoped BigOperators Topology
open _root_.Zeta23 _root_.RHTower _root_.RHTower.WeilMarkovPole

namespace GaloisForLFunctions.ArithmeticPositivityTheory

noncomputable section
set_option autoImplicit false

/-- The rank-two hyperbolic pole quadratic form
`P_pole(g) = coshPairing(g)^2 / 2 - sinhPairing(g)^2 / 2`. -/
def hyperbolicPoleForm (g : ℝ → ℝ) : ℝ :=
  coshPairing g ^ 2 / 2 - sinhPairing g ^ 2 / 2

/-- For any odd function `g` (`∀ u, g (-u) = -g u`), the stabilizing `cosh` pole pairing vanishes. -/
theorem coshPairing_eq_zero_of_odd {g : ℝ → ℝ} (hodd : ∀ u : ℝ, g (-u) = -g u) :
    coshPairing g = 0 := by
  unfold coshPairing
  have hneg : (∫ u : ℝ, g (-u) * (2 * Real.cosh (-u / 2))) =
      ∫ u : ℝ, g u * (2 * Real.cosh (u / 2)) :=
    integral_neg_eq_self (fun u : ℝ => g u * (2 * Real.cosh (u / 2))) volume
  have hpt : (fun u : ℝ => g (-u) * (2 * Real.cosh (-u / 2))) =
      fun u : ℝ => -(g u * (2 * Real.cosh (u / 2))) := by
    funext u
    rw [hodd u, show -u / 2 = -(u / 2) by ring, Real.cosh_neg]
    ring
  rw [hpt, integral_neg] at hneg
  linarith

/-- For any even function `g` (`∀ u, g (-u) = g u`), the destabilizing `sinh` pole pairing vanishes. -/
theorem sinhPairing_eq_zero_of_even {g : ℝ → ℝ} (heven : ∀ u : ℝ, g (-u) = g u) :
    sinhPairing g = 0 := by
  unfold sinhPairing
  have hneg : (∫ u : ℝ, g (-u) * (2 * Real.sinh (-u / 2))) =
      ∫ u : ℝ, g u * (2 * Real.sinh (u / 2)) :=
    integral_neg_eq_self (fun u : ℝ => g u * (2 * Real.sinh (u / 2))) volume
  have hpt : (fun u : ℝ => g (-u) * (2 * Real.sinh (-u / 2))) =
      fun u : ℝ => -(g u * (2 * Real.sinh (u / 2))) := by
    funext u
    rw [heven u, show -u / 2 = -(u / 2) by ring, Real.sinh_neg]
    ring
  rw [hpt, integral_neg] at hneg
  linarith

/-- On any even function, the hyperbolic pole form is nonnegative and equals `coshPairing(g)^2 / 2`. -/
theorem hyperbolicPoleForm_of_even {g : ℝ → ℝ} (heven : ∀ u : ℝ, g (-u) = g u) :
    hyperbolicPoleForm g = coshPairing g ^ 2 / 2 ∧ 0 ≤ hyperbolicPoleForm g := by
  have heq : hyperbolicPoleForm g = coshPairing g ^ 2 / 2 := by
    unfold hyperbolicPoleForm
    rw [sinhPairing_eq_zero_of_even heven]
    ring
  exact ⟨heq, heq.symm ▸ div_nonneg (sq_nonneg _) (by norm_num)⟩

/-- On any odd function, the hyperbolic pole form is nonpositive and equals `-sinhPairing(g)^2 / 2`. -/
theorem hyperbolicPoleForm_of_odd {g : ℝ → ℝ} (hodd : ∀ u : ℝ, g (-u) = -g u) :
    hyperbolicPoleForm g = -(sinhPairing g ^ 2 / 2) ∧ hyperbolicPoleForm g ≤ 0 := by
  have heq : hyperbolicPoleForm g = -(sinhPairing g ^ 2 / 2) := by
    unfold hyperbolicPoleForm
    rw [coshPairing_eq_zero_of_odd hodd]
    ring
  exact ⟨heq, heq.symm ▸ neg_nonpos.mpr (div_nonneg (sq_nonneg _) (by norm_num))⟩

private theorem integrable_cosh_weight {g : ℝ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g) :
    Integrable (fun u : ℝ => g u * (2 * Real.cosh (u / 2))) :=
  (hg.mul (by fun_prop)).integrable_of_hasCompactSupport hgc.mul_right

private theorem integrable_sinh_weight {g : ℝ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g) :
    Integrable (fun u : ℝ => g u * (2 * Real.sinh (u / 2))) :=
  (hg.mul (by fun_prop)).integrable_of_hasCompactSupport hgc.mul_right

/-- Exact parity filtering of `coshPairing` on a linear combination `c g_e + d g_o`. -/
theorem coshPairing_even_add_odd {g_e g_o : ℝ → ℝ}
    (hge : Continuous g_e) (hgec : HasCompactSupport g_e)
    (hgo : Continuous g_o) (hgoc : HasCompactSupport g_o)
    (hodd : ∀ u : ℝ, g_o (-u) = -g_o u) (c d : ℝ) :
    coshPairing (fun u => c * g_e u + d * g_o u) = c * coshPairing g_e := by
  have hie := (integrable_cosh_weight hge hgec).const_mul c
  have hio := (integrable_cosh_weight hgo hgoc).const_mul d
  have hlin : coshPairing (fun u => c * g_e u + d * g_o u) =
      c * coshPairing g_e + d * coshPairing g_o := by
    unfold coshPairing
    have hpt : (fun u => (c * g_e u + d * g_o u) * (2 * Real.cosh (u / 2))) =
        fun u => c * (g_e u * (2 * Real.cosh (u / 2))) +
          d * (g_o u * (2 * Real.cosh (u / 2))) := by
      funext u; ring
    rw [hpt, integral_add hie hio, integral_const_mul, integral_const_mul]
  rw [hlin, coshPairing_eq_zero_of_odd hodd, mul_zero, add_zero]

/-- Exact parity filtering of `sinhPairing` on a linear combination `c g_e + d g_o`. -/
theorem sinhPairing_even_add_odd {g_e g_o : ℝ → ℝ}
    (hge : Continuous g_e) (hgec : HasCompactSupport g_e)
    (hgo : Continuous g_o) (hgoc : HasCompactSupport g_o)
    (heven : ∀ u : ℝ, g_e (-u) = g_e u) (c d : ℝ) :
    sinhPairing (fun u => c * g_e u + d * g_o u) = d * sinhPairing g_o := by
  have hie := (integrable_sinh_weight hge hgec).const_mul c
  have hio := (integrable_sinh_weight hgo hgoc).const_mul d
  have hlin : sinhPairing (fun u => c * g_e u + d * g_o u) =
      c * sinhPairing g_e + d * sinhPairing g_o := by
    unfold sinhPairing
    have hpt : (fun u => (c * g_e u + d * g_o u) * (2 * Real.sinh (u / 2))) =
        fun u => c * (g_e u * (2 * Real.sinh (u / 2))) +
          d * (g_o u * (2 * Real.sinh (u / 2))) := by
      funext u; ring
    rw [hpt, integral_add hie hio, integral_const_mul, integral_const_mul]
  rw [hlin, sinhPairing_eq_zero_of_even heven, mul_zero, zero_add]

/-- **Orthogonal Parity Diagonalization of the Hyperbolic Pole Form.**
For any compactly supported continuous even function `g_e` and odd function `g_o`,
the hyperbolic pole quadratic form on `c g_e + d g_o` decouples without cross-term into
`c^2 coshPairing(g_e)^2 / 2 - d^2 sinhPairing(g_o)^2 / 2`. -/
theorem hyperbolicPoleForm_even_odd_decoupling {g_e g_o : ℝ → ℝ}
    (hge : Continuous g_e) (hgec : HasCompactSupport g_e)
    (hgo : Continuous g_o) (hgoc : HasCompactSupport g_o)
    (heven : ∀ u : ℝ, g_e (-u) = g_e u)
    (hodd : ∀ u : ℝ, g_o (-u) = -g_o u) (c d : ℝ) :
    hyperbolicPoleForm (fun u => c * g_e u + d * g_o u) =
      c ^ 2 * (coshPairing g_e ^ 2 / 2) - d ^ 2 * (sinhPairing g_o ^ 2 / 2) := by
  unfold hyperbolicPoleForm
  rw [coshPairing_even_add_odd hge hgec hgo hgoc hodd c d,
    sinhPairing_even_add_odd hge hgec hgo hgoc heven c d]
  ring

/-- **Even-Mode Weil–Markov–Pole Splitting.** For an even test `g ∈ C²_c(ℝ)` at prime
aperture `N`, the destabilizing sinh pole moment vanishes identically and
`W(g) = markovForm N g + coshPairing g ^ 2 / 2 ≥ markovForm N g`. -/
theorem weil_even_eq_markovForm_add_cosh_sq {g : ℝ → ℝ}
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (heven : ∀ u : ℝ, g (-u) = g u)
    {N : ℕ} (hN : ∀ n : ℕ, N < n → ∀ u, g u * g (u + Real.log n) = 0) :
    (weilFullFunctional (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (EF.weilTest (fun u => (g u : ℂ)) (fun u => (g u : ℂ)))).re =
      markovForm N g + coshPairing g ^ 2 / 2 := by
  rw [weil_eq_markovForm_add_pole hg hgc hN, sinhPairing_eq_zero_of_even heven]
  ring

/-- **Odd-Mode Weil–Markov–Pole Splitting.** For an odd test `g ∈ C²_c(ℝ)` at prime
aperture `N`, the stabilizing cosh pole moment vanishes identically and
`W(g) = markovForm N g - sinhPairing g ^ 2 / 2`. -/
theorem weil_odd_eq_markovForm_sub_sinh_sq {g : ℝ → ℝ}
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hodd : ∀ u : ℝ, g (-u) = -g u)
    {N : ℕ} (hN : ∀ n : ℕ, N < n → ∀ u, g u * g (u + Real.log n) = 0) :
    (weilFullFunctional (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (EF.weilTest (fun u => (g u : ℂ)) (fun u => (g u : ℂ)))).re =
      markovForm N g - sinhPairing g ^ 2 / 2 := by
  rw [weil_eq_markovForm_add_pole hg hgc hN, coshPairing_eq_zero_of_odd hodd]
  ring

/-- **Odd-Mode Sinh-Capacity Positivity Classification (`iff`).** For an odd test `g ∈ C²_c(ℝ)`
at prime aperture `N`, the Weil energy is nonnegative if and only if
`sinhPairing g ^ 2 ≤ 2 * markovForm N g`. -/
theorem weil_odd_nonneg_iff_sinh_sq_le_two_markovForm {g : ℝ → ℝ}
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hodd : ∀ u : ℝ, g (-u) = -g u)
    {N : ℕ} (hN : ∀ n : ℕ, N < n → ∀ u, g u * g (u + Real.log n) = 0) :
    0 ≤ (weilFullFunctional (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (EF.weilTest (fun u => (g u : ℂ)) (fun u => (g u : ℂ)))).re ↔
      sinhPairing g ^ 2 ≤ 2 * markovForm N g := by
  rw [weil_odd_eq_markovForm_sub_sinh_sq hg hgc hodd hN]
  constructor <;> intro h <;> linarith

/-- **Sharp Odd-Mode Instability Classification (`iff`).** For an odd test `g ∈ C²_c(ℝ)`
at prime aperture `N`, the Weil energy is strictly negative if and only if
`markovForm N g < sinhPairing g ^ 2 / 2`. -/
theorem weil_odd_neg_iff_markovForm_lt_half_sinh_sq {g : ℝ → ℝ}
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hodd : ∀ u : ℝ, g (-u) = -g u)
    {N : ℕ} (hN : ∀ n : ℕ, N < n → ∀ u, g u * g (u + Real.log n) = 0) :
    (weilFullFunctional (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (EF.weilTest (fun u => (g u : ℂ)) (fun u => (g u : ℂ)))).re < 0 ↔
      markovForm N g < sinhPairing g ^ 2 / 2 := by
  rw [weil_odd_eq_markovForm_sub_sinh_sq hg hgc hodd hN]
  constructor <;> intro h <;> linarith

/-- Exact creation-potential drift between two prime apertures `2 ≤ N₁ ≤ N₂`:
`creationPotential N₁ - creationPotential N₂ = 2 * ∑_{n ∈ (N₁, N₂]} primeJumpWeight n`. -/
theorem creationPotential_sub_eq_sum_Ioc {N₁ N₂ : ℕ} (h1 : 1 ≤ N₁) (h12 : N₁ ≤ N₂) :
    creationPotential N₁ - creationPotential N₂ =
      2 * ∑ n ∈ Finset.Ioc N₁ N₂, primeJumpWeight n := by
  unfold creationPotential
  have hsplit : Finset.Icc 2 N₂ = Finset.Icc 2 N₁ ∪ Finset.Ioc N₁ N₂ := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc]
    omega
  have hdisj : Disjoint (Finset.Icc 2 N₁) (Finset.Ioc N₁ N₂) := by
    rw [Finset.disjoint_left]
    intro n hn1 hn2
    simp only [Finset.mem_Icc, Finset.mem_Ioc] at hn1 hn2
    omega
  rw [hsplit, Finset.sum_union hdisj]
  ring

/-- The creation potential `V_N = Ω(0) - 2 ∑_{2 ≤ n ≤ N} Λ(n) / √n` is antitone in the
prime aperture `N` for `N ≥ 1`. -/
theorem creationPotential_antitone {N₁ N₂ : ℕ} (h1 : 1 ≤ N₁) (h12 : N₁ ≤ N₂) :
    creationPotential N₂ ≤ creationPotential N₁ := by
  have hsub := creationPotential_sub_eq_sum_Ioc h1 h12
  have hnonneg : 0 ≤ 2 * ∑ n ∈ Finset.Ioc N₁ N₂, primeJumpWeight n :=
    mul_nonneg (by norm_num) (Finset.sum_nonneg fun n _ => primeJumpWeight_nonneg n)
  linarith

end

end GaloisForLFunctions.ArithmeticPositivityTheory
