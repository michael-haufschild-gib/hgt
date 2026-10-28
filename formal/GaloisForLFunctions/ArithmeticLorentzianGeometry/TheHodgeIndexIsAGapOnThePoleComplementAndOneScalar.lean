import GaloisForLFunctions.ArithmeticLorentzianGeometry.ThePoleDefectPaysThePole
import GaloisForLFunctions.ArithmeticLorentzianGeometry.TheStabilityRegimeEndsAtTheRobinEulerThreshold
import GaloisForLFunctions.ArithmeticCriticalityTheory.ShiftedGroundStateOddProfileCoordinates

/-!
# The Hodge index is a gap on the pole complement and one scalar

Weil's form on an atomic test `f_x = Σ_{n ≤ N} x_n g(· − log n)` is the Markov form plus the pole
term, `W(f_x) = M(f_x) + 2A(f_x)B(f_x)`, with `A = ∫ f e^{−u/2}` and `B = ∫ f e^{u/2}`. The `H`-row
is exactly the pole functional. For every profile and every width — overlapping atoms included —
`A(f_x) = (∫ g e^{−v/2}) · p(x)` with `p(x) = Σ_{n ≤ N} x_n/√n`
(`integral_atomicTest_mul_exp_neg_half`). It is the functional whose kernel is the pole complement
of RenormalizedArithmeticPotentialTheory.

* **The reduction for a quadratic plus a rank-two term** (`forall_add_two_mul_nonneg_iff`): for a
  quadratic `Q` and linear `A, B`, `Q + 2AB ≥ 0` iff `Q ≥ 0` on `ker A` and `Q + 2B ≥ 0` on
  `{A = 1}`. On `ker A` the pole term vanishes; off it, scaling to `A = 1` turns the rank-two term
  into the linear term `2B`.
* **The atomic Hodge index is a gap and one scalar** (`forall_weilQuad_atomicTest_nonneg_iff`): at
  every width, Weil's form is nonnegative on the atomic tests iff the Markov form is nonnegative on
  the pole complement `p = 0`, and `M(f_x) + 2a₀ B(f_x) ≥ 0` on the affine hyperplane `p = 1`,
  `a₀ = ∫ g e^{−v/2}`. The second condition is a single number: the infimum of a quadratic over an
  affine hyperplane.
* **Beyond the Robin–Euler threshold** (`eventually_markovEnergy_pole_neg_and_gap`): there the
  Markov form is negative at the pole vector, which has `p = H_N > 0`. If Weil's form is
  nonnegative on the atomic family, then the Markov form is nonnegative on the hyperplane `p = 0`
  and negative at a vector transversal to it. So it has exactly one negative direction, which the
  pole term must pay through the scalar condition. Below the threshold the gap condition is
  supplied by the stability regime. Beyond it, it is the explicit spectral gap of the prime form
  below its pole, sharpened by the Lévy self-energy, and it is the open content of the window.
-/

noncomputable section

open MeasureTheory Finset RHTower

namespace GaloisForLFunctions.ArithmeticLorentzianGeometry

open GaloisForLFunctions.SpacingScaleHarmonicAnalysis GaloisForLFunctions.ArithmeticElectrostatics
  GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

/-! ### A quadratic plus a rank-two term -/

/-- **The reduction.** For a quadratic function `Q` and linear functionals `A, B` on a real vector
space, `Q + 2AB ≥ 0` everywhere iff `Q ≥ 0` on `ker A` and `Q + 2B ≥ 0` on `{A = 1}`. -/
theorem forall_add_two_mul_nonneg_iff {V : Type*} [AddCommGroup V] [Module ℝ V] (Q : V → ℝ)
    (hQ : ∀ (t : ℝ) (x : V), Q (t • x) = t ^ 2 * Q x) (A B : V →ₗ[ℝ] ℝ) :
    (∀ x, 0 ≤ Q x + 2 * (A x * B x)) ↔
      (∀ y, A y = 0 → 0 ≤ Q y) ∧ (∀ x, A x = 1 → 0 ≤ Q x + 2 * B x) := by
  constructor
  · intro h
    refine ⟨fun y hy => by simpa [hy] using h y, fun x hx => by simpa [hx] using h x⟩
  · rintro ⟨h0, h1⟩ x
    by_cases hx : A x = 0
    · rw [hx, zero_mul, mul_zero, add_zero]; exact h0 x hx
    · set t := A x
      have hA : A (t⁻¹ • x) = 1 := by rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hx]
      have h := h1 _ hA
      have hQx : Q x = t ^ 2 * Q (t⁻¹ • x) := by
        rw [hQ t⁻¹ x, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hx, one_pow, one_mul]
      have hBx : B x = t * B (t⁻¹ • x) := by
        rw [map_smul, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hx, one_mul]
      rw [hQx, hBx]
      have e : t ^ 2 * Q (t⁻¹ • x) + 2 * (t * (t * B (t⁻¹ • x))) =
          t ^ 2 * (Q (t⁻¹ • x) + 2 * B (t⁻¹ • x)) := by ring
      rw [e]
      exact mul_nonneg (sq_nonneg t) h

/-! ### The pole rows of an atomic test -/

/-- The pole functional `p(x) = Σ_{n ≤ N} x_n/√n`. -/
def poleFunctional (N : ℕ) : (ℕ → ℝ) →ₗ[ℝ] ℝ where
  toFun x := ∑ n ∈ Icc 1 N, x n / Real.sqrt n
  map_add' x y := by simp only [Pi.add_apply, add_div, sum_add_distrib]
  map_smul' c x := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_sum, mul_div_assoc]

/-- The `V`-row of the atomic tests of `g`, `x ↦ Σ_n x_n ∫ g(u − log n) e^{u/2} du`. -/
def vRowFunctional (N : ℕ) (g : ℝ → ℝ) : (ℕ → ℝ) →ₗ[ℝ] ℝ where
  toFun x := ∑ n ∈ Icc 1 N, x n * ∫ u, g (u - Real.log n) * Real.exp (u / 2)
  map_add' x y := by simp only [Pi.add_apply, add_mul, sum_add_distrib]
  map_smul' c x := by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_sum, mul_assoc]

variable {g : ℝ → ℝ} {w : ℝ}

/-- An atom `g(· − log n)` against `e^{−u/2}` is `n^{−1/2} ∫ g e^{−v/2}`. -/
theorem integral_atom_mul_exp_neg_half (g : ℝ → ℝ) {n : ℕ} (hn : 1 ≤ n) :
    ∫ u, g (u - Real.log n) * Real.exp (-(u / 2)) =
      (∫ v, g v * Real.exp (-(v / 2))) / Real.sqrt n := by
  have hsq : Real.exp (Real.log n / 2) = Real.sqrt n := by
    rw [← Real.sqrt_sq (Real.exp_pos _).le, exp_half_log_sq hn]
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  have e : ∀ u, g (u - Real.log n) * Real.exp (-(u / 2)) =
      (g (u - Real.log n) * Real.exp (-((u - Real.log n) / 2))) / Real.sqrt n := fun u => by
    rw [← hsq, eq_div_iff (Real.exp_pos _).ne', mul_assoc, ← Real.exp_add]
    congr 2; ring
  simp_rw [e]
  rw [integral_div, integral_sub_right_eq_self (fun v => g v * Real.exp (-(v / 2))) (Real.log n)]

/-- **The `H`-row is the pole functional**: `∫ f_x e^{−u/2} = (∫ g e^{−v/2}) p(x)` at every width. -/
theorem integral_atomicTest_mul_exp_neg_half (hg : Continuous g)
    (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) (N : ℕ) (x : ℕ → ℝ) :
    ∫ u, atomicTest N x g u * Real.exp (-(u / 2)) =
      (∫ v, g v * Real.exp (-(v / 2))) * poleFunctional N x := by
  rw [integral_atomicTest_mul (by fun_prop) hg hgsupp, poleFunctional, LinearMap.coe_mk,
    AddHom.coe_mk, mul_sum]
  refine sum_congr rfl fun n hn => ?_
  rw [integral_atom_mul_exp_neg_half g (Finset.mem_Icc.mp hn).1]
  ring

theorem integral_atomicTest_mul_exp_half (hg : Continuous g)
    (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) (N : ℕ) (x : ℕ → ℝ) :
    ∫ u, atomicTest N x g u * Real.exp (u / 2) = vRowFunctional N g x := by
  rw [integral_atomicTest_mul (by fun_prop) hg hgsupp]; rfl

/-- The Markov form is quadratic along atomic tests. -/
theorem markovEnergy_atomicTest_smul (g : ℝ → ℝ) (N : ℕ) (t : ℝ) (x : ℕ → ℝ) :
    markovEnergy (fun u => (atomicTest N (t • x) g u : ℂ)) =
      t ^ 2 * markovEnergy (fun u => (atomicTest N x g u : ℂ)) := by
  have e : (fun u => (atomicTest N (t • x) g u : ℂ)) =
      (t : ℂ) • fun u => (atomicTest N x g u : ℂ) := by
    funext u
    simp only [atomicTest, Pi.smul_apply, smul_eq_mul, Complex.real_smul, mul_sum, mul_assoc]
    push_cast
    rfl
  rw [e, ArithmeticCriticalityTheory.markovEnergy_real_smul]

/-! ### The atomic Hodge index -/

/-- **The atomic Hodge index is a gap on the pole complement and one scalar.** For a `C²` profile
supported in `[0, w]` — at every width, overlapping atoms included — Weil's form is nonnegative on
every atomic test iff the Markov form is nonnegative on the pole complement `p = 0` and
`M(f_x) + 2a₀ B(f_x) ≥ 0` on `p = 1`, `a₀ = ∫ g e^{−v/2}`. -/
theorem forall_weilQuad_atomicTest_nonneg_iff (hg : ContDiff ℝ 2 g)
    (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) (N : ℕ) :
    (∀ x : ℕ → ℝ, 0 ≤ weilQuad (atomicTest N x g)) ↔
      (∀ x, poleFunctional N x = 0 → 0 ≤ markovEnergy (fun u => (atomicTest N x g u : ℂ))) ∧
      (∀ x, poleFunctional N x = 1 → 0 ≤ markovEnergy (fun u => (atomicTest N x g u : ℂ)) +
        2 * ((∫ v, g v * Real.exp (-(v / 2))) * vRowFunctional N g x)) := by
  have hgc : HasCompactSupport g := HasCompactSupport.intro isCompact_Icc hgsupp
  have hW : ∀ x, weilQuad (atomicTest N x g) =
      markovEnergy (fun u => (atomicTest N x g u : ℂ)) +
        2 * (poleFunctional N x * ((∫ v, g v * Real.exp (-(v / 2))) • vRowFunctional N g) x) := by
    intro x
    have hf := contDiff_atomicTest hg N x
    have hfc := hasCompactSupport_atomicTest hgsupp N x
    rw [weilQuad_eq hf hfc, add_sub_assoc, two_mul_cosh_sq_sub_sinh_sq_eq hf.continuous hfc,
      markovEnergy_ofReal_eq_archForm_sub_primeSum hf hfc, archForm_eq_levyEnergy hf hfc,
      integral_atomicTest_mul_exp_neg_half hg.continuous hgsupp,
      integral_atomicTest_mul_exp_half hg.continuous hgsupp, LinearMap.smul_apply, smul_eq_mul]
    ring
  simp_rw [hW]
  rw [forall_add_two_mul_nonneg_iff (fun x => markovEnergy (fun u => (atomicTest N x g u : ℂ)))
    (markovEnergy_atomicTest_smul g N)]
  simp only [LinearMap.smul_apply, smul_eq_mul]

/-! ### Beyond the Robin–Euler threshold -/

theorem poleFunctional_truncPole {N : ℕ} :
    poleFunctional N (truncPole N) = ∑ n ∈ Icc 1 N, (1 : ℝ) / n := by
  simp only [poleFunctional, LinearMap.coe_mk, AddHom.coe_mk]
  refine sum_congr rfl fun n hn => ?_
  have hn1 := (Finset.mem_Icc.mp hn).1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  simp only [truncPole, if_pos (Finset.mem_Icc.mp hn).2, poleVector]
  rw [div_div, ← Real.sqrt_mul hn0.le, Real.sqrt_mul_self hn0.le]

/-- **Beyond the Robin–Euler threshold the Hodge index forces one negative direction.** Eventually
in `N`, at widths beyond the threshold: the Markov form is negative at the pole vector, which lies
off the pole complement (`p = H_N > 0`). If Weil's form is nonnegative on the atomic family, the
Markov form is nonnegative on the pole complement, so it has exactly one negative direction. -/
theorem eventually_markovEnergy_pole_neg_and_gap {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hφ0 : 0 < ∫ u, φ u ^ 2) {K : ℝ}
    (hK : ∀ u v, |φ u - φ v| ≤ K * |u - v|) (hφnn : ∀ u, 0 ≤ φ u) {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ w : ℝ, 0 < w → w ≤ atomSpacing N / 2 →
      2 * gammaHardyPhaseRate 0 + Real.log (1 / (w * N)) + profileRobin φ +
          Real.eulerMascheroniConstant + ε + Real.exp (1 / 2) / 2 * w < 0 →
        markovEnergy (fun u => (atomicTest N (truncPole N) (atomDilate φ w) u : ℂ)) < 0 ∧
          0 < poleFunctional N (truncPole N) ∧
          ((∀ x : ℕ → ℝ, 0 ≤ weilQuad (atomicTest N x (atomDilate φ w))) →
            ∀ x, poleFunctional N x = 0 →
              0 ≤ markovEnergy (fun u => (atomicTest N x (atomDilate φ w) u : ℂ))) := by
  obtain ⟨N₀, hN₀⟩ := eventually_markovEnergy_poleTest_neg hφ hφsupp hφ0 hK hφnn hε
  refine ⟨max N₀ 1, fun N hN w hw0 hw hneg => ⟨hN₀ N (le_trans (le_max_left _ _) hN) w hw0 hw hneg,
    ?_, fun hW => ?_⟩⟩
  · have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
    rw [poleFunctional_truncPole]
    have hmem : 1 ∈ Icc 1 N := Finset.mem_Icc.mpr ⟨le_rfl, hN1⟩
    have := Finset.single_le_sum (f := fun n : ℕ => (1 : ℝ) / n) (fun n _ => by positivity) hmem
    simp only [Nat.cast_one, div_one] at this
    linarith
  · obtain ⟨hg, hgsupp, -⟩ := atomDilate_facts hφ hφsupp hw0
    exact ((forall_weilQuad_atomicTest_nonneg_iff hg hgsupp N).mp hW).1

end GaloisForLFunctions.ArithmeticLorentzianGeometry
