import GaloisForLFunctions.SignedWindowCriticality.TheSectorsAreTheMomentConditionsOfTheJets

/-!
# Capacities and constrained ground states are singular at the edge

No window eigenfunction is smooth (`eq_zero_of_isWindowEigen`). The same holds for every window
equation whose source solves a linear ODE with constant coefficients — the equations of all the
constrained problems and capacities of the field.

* **Window equations with exponential-polynomial sources** (`eq_zero_of_isWindowSolution`): if
  `P^{(m+1)} = Σ_{i ≤ m} cᵢP^{(i)}` and a smooth test `F` of `[−a, a]` satisfies
  `W(F, G) = μ⟨F, G⟩ + κ⟨P, G⟩` for every smooth test `G` of the window, then `F = 0`. The operator
  `L(D)` killing `P` maps the equation to `(W − μ)L(D)F = 0` (`d/dx` is skew for `W` and for
  `⟨·,·⟩`); `L(D)F` is a smooth window eigenfunction, hence `0`, and a bump solving a
  constant-coefficient ODE vanishes.
* **Parity** (`isWindowSolution_of_sector`): in a parity sector the equation need only be tested on
  the sector.
* **Capacities are not attained** (`not_isCapacityMax`): if a smooth test of a sector maximized
  `ℓ_P²/(W + bℓ_P²)`, `ℓ_P = ⟨P, ·⟩`, its first variation would be `W(F, ·) = (W(F)/ℓ_P(F))ℓ_P`.
* **Hyperplane-constrained ground states are not smooth** (`eq_zero_of_isMin_on_hyperplane`): the
  Lagrange equation of `inf W/‖·‖²` on `{ℓ_P = 0}` is `(W − μ)F = κP`.

Instances: the odd moment capacity `(∫xF)²/(W + b(∫xF)²)` of the odd unit window
(`not_isMax_oddMomentCapacity`), the pole's sinh capacity (`not_isMax_sinhCapacity`), the even
ground state on the cosh hyperplane (`eq_zero_of_isMin_on_coshHyperplane`) and on the mean-zero
hyperplane (`eq_zero_of_isMin_on_meanZero`). The extremals that decide these bounded inequalities
live in the energy completion and are singular at the window edge; a smooth test never attains
them.
-/

open MeasureTheory Set Filter Topology
open scoped ContDiff

noncomputable section

namespace GaloisForLFunctions.SignedWindowCriticality

open ArithmeticCastelnuovoSeveri SpacingScaleHarmonicAnalysis DimensionZeroGeometryOfSpecZ
open GrowingWindowsOfSpecZ

variable {a μ κ : ℝ}

/-- `H` solves the **window equation with source** `(W − μ)H = κP` on `[−a, a]`: against every
smooth test of the window. -/
def IsWindowSolution (a μ κ : ℝ) (P H : ℝ → ℝ) : Prop :=
  ∀ G : ℝ → ℝ, ContDiff ℝ ∞ G → SupportedIn a G →
    weilPair H G = μ * (∫ u, H u * G u) + κ * ∫ u, P u * G u

theorem integral_mul_deriv_eq_neg {P G : ℝ → ℝ} (hP : ContDiff ℝ ∞ P) (hG : ContDiff ℝ ∞ G)
    (hGc : HasCompactSupport G) : ∫ u, P u * deriv G u = -∫ u, deriv P u * G u := by
  have h := integral_deriv_mul_eq_neg (f := G) (g := P) (by exact_mod_cast contDiff_infty.mp hG 1)
    hGc (by exact_mod_cast contDiff_infty.mp hP 1)
  have e1 : (fun u => P u * deriv G u) = fun u => deriv G u * P u := funext fun u => mul_comm _ _
  have e2 : (fun u => deriv P u * G u) = fun u => G u * deriv P u := funext fun u => mul_comm _ _
  rw [e1, e2, h]

/-- The equation passes to derivatives: `(W − μ)H' = κP'`. -/
theorem isWindowSolution_deriv {P H : ℝ → ℝ} (hH : ContDiff ℝ ∞ H) (hHa : SupportedIn a H)
    (hP : ContDiff ℝ ∞ P) (h : IsWindowSolution a μ κ P H) :
    IsWindowSolution a μ κ (deriv P) (deriv H) := by
  intro G hG hGa
  have hHc := hasCompactSupport_of_supportedIn' hHa
  have hGc := hasCompactSupport_of_supportedIn' hGa
  rw [weilPair_deriv_left hH hHc hG hGc, h (deriv G) (contDiff_deriv_of_smooth hG)
    (supportedIn_deriv hGa)]
  have hibp := integral_deriv_mul_eq_neg (f := H) (g := G)
    (by exact_mod_cast contDiff_infty.mp hH 1) hHc (by exact_mod_cast contDiff_infty.mp hG 1)
  rw [hibp, integral_mul_deriv_eq_neg hP hG hGc]
  ring

theorem isWindowSolution_iteratedDeriv {P H : ℝ → ℝ} (hH : ContDiff ℝ ∞ H)
    (hHa : SupportedIn a H) (hP : ContDiff ℝ ∞ P) (h : IsWindowSolution a μ κ P H) (k : ℕ) :
    IsWindowSolution a μ κ (iteratedDeriv k P) (iteratedDeriv k H) := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    rw [iteratedDeriv_succ, iteratedDeriv_succ]
    exact isWindowSolution_deriv (contDiff_iteratedDeriv_of_smooth hH k)
      (iteratedDeriv_supportedIn hHa k) (contDiff_iteratedDeriv_of_smooth hP k) ih

theorem integrable_mul_of_continuous {f G : ℝ → ℝ} (hf : Continuous f) (hG : Continuous G)
    (hGc : HasCompactSupport G) : Integrable fun u => f u * G u :=
  (hf.mul hG).integrable_of_hasCompactSupport hGc.mul_left

/-- **A window equation whose source solves a linear ODE with constant coefficients has no smooth
solution.** If `P^{(m+1)} = Σ_{i ≤ m} cᵢP^{(i)}` (polynomials, exponentials, `cosh`, `sinh`, …) and a
smooth test `F` of `[−a, a]` satisfies `(W − μ)F = κP` against every smooth test of the window, then
`F = 0`. The operator `L(D) = D^{m+1} − Σ cᵢDⁱ` kills the source and, `d/dx` being `W`-skew, maps
the equation to `(W − μ)L(D)F = 0`; so `L(D)F` is a smooth window eigenfunction, hence `0`, and a
bump solving a constant-coefficient ODE vanishes. -/
theorem eq_zero_of_isWindowSolution {P F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F) (hFa : SupportedIn a F)
    (hP : ContDiff ℝ ∞ P) {m : ℕ} (c : Fin (m + 1) → ℝ)
    (hode : iteratedDeriv (m + 1) P = ∑ i, c i • iteratedDeriv i P)
    (h : IsWindowSolution a μ κ P F) : F = 0 := by
  have hFc := hasCompactSupport_of_supportedIn' hFa
  set S := ∑ i : Fin (m + 1), c i • iteratedDeriv (i : ℕ) F with hSdef
  set H := iteratedDeriv (m + 1) F - S with hHdef
  have hSs : ContDiff ℝ ∞ S := contDiff_jetComb hF c fun i => (i : ℕ)
  have hSa : SupportedIn a S := supportedIn_jetComb hFa c fun i => (i : ℕ)
  have hHs : ContDiff ℝ ∞ H := (contDiff_iteratedDeriv_of_smooth hF _).sub hSs
  have hHa : SupportedIn a H := fun u hu => by
    simp only [hHdef, Pi.sub_apply, iteratedDeriv_supportedIn hFa _ u hu, hSa u hu, sub_zero]
  have heig : IsWindowEigen a μ H := by
    intro G hG hGa
    have hGr := smooth_mem_realTests hG hGa
    have hGc := hasCompactSupport_of_supportedIn' hGa
    have hr : ∀ k, iteratedDeriv k F ∈ realTests := iteratedDeriv_mem_realTests hF hFc
    have hk := fun k => isWindowSolution_iteratedDeriv hF hFa hP h k G hG hGa
    have IF : ∀ k, Integrable fun u => iteratedDeriv k F u * G u := fun k =>
      integrable_mul_of_continuous (contDiff_iteratedDeriv_of_smooth hF k).continuous
        hG.continuous hGc
    have IP : ∀ k, Integrable fun u => iteratedDeriv k P u * G u := fun k =>
      integrable_mul_of_continuous (contDiff_iteratedDeriv_of_smooth hP k).continuous
        hG.continuous hGc
    have hW : weilPair H G = weilPair (iteratedDeriv (m + 1) F) G -
        ∑ i : Fin (m + 1), c i * weilPair (iteratedDeriv i F) G := by
      rw [hHdef, hSdef, weilPair_sub_left (hr _)
        (Submodule.sum_mem _ fun i _ => realTests.smul_mem _ (hr _)) hGr,
        weilPair_sum_left _ (fun i => realTests.smul_mem _ (hr _)) hGr]
      simp only [weilPair_smul_left]
    have hI : ∫ u, H u * G u = (∫ u, iteratedDeriv (m + 1) F u * G u) -
        ∑ i : Fin (m + 1), c i * ∫ u, iteratedDeriv i F u * G u := by
      have e : (fun u => H u * G u) = fun u => iteratedDeriv (m + 1) F u * G u -
          ∑ i : Fin (m + 1), c i * (iteratedDeriv i F u * G u) := by
        funext u
        simp only [hHdef, hSdef, Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
          sub_mul, Finset.sum_mul, mul_assoc]
      rw [e, integral_sub (IF _) (integrable_finsetSum (Finset.univ : Finset (Fin (m + 1)))
        fun i _ => (IF (i : ℕ)).const_mul (c i)),
        integral_finsetSum (Finset.univ : Finset (Fin (m + 1))) fun i _ => (IF (i : ℕ)).const_mul (c i)]
      simp only [integral_const_mul]
    have hJ : ∫ u, iteratedDeriv (m + 1) P u * G u =
        ∑ i : Fin (m + 1), c i * ∫ u, iteratedDeriv i P u * G u := by
      have e : (fun u => iteratedDeriv (m + 1) P u * G u) = fun u =>
          ∑ i : Fin (m + 1), c i * (iteratedDeriv i P u * G u) := by
        funext u
        rw [hode]
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, mul_assoc]
      rw [e, integral_finsetSum (Finset.univ : Finset (Fin (m + 1))) fun i _ => (IP (i : ℕ)).const_mul (c i)]
      simp only [integral_const_mul]
    have hsum : ∑ i : Fin (m + 1), c i * (μ * (∫ u, iteratedDeriv i F u * G u) +
        κ * ∫ u, iteratedDeriv i P u * G u) =
        μ * (∑ i : Fin (m + 1), c i * ∫ u, iteratedDeriv i F u * G u) +
          κ * ∑ i : Fin (m + 1), c i * ∫ u, iteratedDeriv i P u * G u := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hW, hk (m + 1)]
    simp only [hk]
    rw [hsum, hJ, hI]
    ring
  have hH0 := eq_zero_of_isWindowEigen hHs hHa heig
  exact eq_zero_of_iteratedDeriv_eq_sum hF hFc c (sub_eq_zero.mp hH0)

/-! ### Parity -/

/-- In a parity sector the window equation need only be tested on the sector: if `F` and `P` have
parity `ε`, the equation against the tests of parity `ε` gives it against all tests. -/
theorem isWindowSolution_of_sector {P F : ℝ → ℝ} (ε : ℝ) (hε : ε = 1 ∨ ε = -1)
    (hF : ContDiff ℝ ∞ F) (hFa : SupportedIn a F) (hFp : ∀ x, F (-x) = ε * F x)
    (hP : Continuous P) (hPp : ∀ x, P (-x) = ε * P x)
    (h : ∀ G : ℝ → ℝ, ContDiff ℝ ∞ G → SupportedIn a G → (∀ x, G (-x) = ε * G x) →
      weilPair F G = μ * (∫ u, F u * G u) + κ * ∫ u, P u * G u) :
    IsWindowSolution a μ κ P F := by
  intro G hG hGa
  have hFr := smooth_mem_realTests hF hFa
  set Ge := fun x => (G x + G (-x)) / 2
  set Go := fun x => (G x - G (-x)) / 2
  have hGeq : G = Ge + Go := by funext x; simp only [Ge, Go, Pi.add_apply]; ring
  have hGes := evenPart_smooth hG
  have hGos := oddPart_smooth hG
  have hGer := smooth_mem_realTests hGes (supportedIn_evenPart hGa)
  have hGor := smooth_mem_realTests hGos (supportedIn_oddPart hGa)
  have hGe : ∀ x, Ge (-x) = Ge x := fun x => by simp only [Ge, neg_neg]; ring
  have hGo : ∀ x, Go (-x) = -Go x := fun x => by simp only [Go, neg_neg]; ring
  have hGec := hasCompactSupport_of_supportedIn' (supportedIn_evenPart hGa)
  have hGoc := hasCompactSupport_of_supportedIn' (supportedIn_oddPart hGa)
  have hFc := hFr.1.continuous
  have i1 := integrable_mul_of_continuous hFc hGes.continuous hGec
  have i2 := integrable_mul_of_continuous hFc hGos.continuous hGoc
  have i3 := integrable_mul_of_continuous hP hGes.continuous hGec
  have i4 := integrable_mul_of_continuous hP hGos.continuous hGoc
  have hsplitF : ∫ u, F u * G u = (∫ u, F u * Ge u) + ∫ u, F u * Go u := by
    rw [← integral_add i1 i2]; congr 1; funext u; rw [hGeq]; simp only [Pi.add_apply]; ring
  have hsplitP : ∫ u, P u * G u = (∫ u, P u * Ge u) + ∫ u, P u * Go u := by
    rw [← integral_add i3 i4]; congr 1; funext u; rw [hGeq]; simp only [Pi.add_apply]; ring
  have hWG : weilPair F G = weilPair F Ge + weilPair F Go := by
    rw [← weilPair_add_right hFr hGer hGor, ← hGeq]
  rw [hWG, hsplitF, hsplitP]
  rcases hε with rfl | rfl
  · have hFe : ∀ x, F (-x) = F x := fun x => by rw [hFp, one_mul]
    have hPe : ∀ x, P (-x) = P x := fun x => by rw [hPp, one_mul]
    rw [h Ge hGes (supportedIn_evenPart hGa) (fun x => by rw [hGe, one_mul]),
      weilPair_comm, weilPair_odd_even hGor hFr hGo hFe, integral_even_mul_odd hFe hGo,
      integral_even_mul_odd hPe hGo]
    ring
  · have hFo : ∀ x, F (-x) = -F x := fun x => by rw [hFp, neg_one_mul]
    have hPo : ∀ x, P (-x) = -P x := fun x => by rw [hPp, neg_one_mul]
    have e1 : ∫ u, F u * Ge u = 0 := by
      rw [show (fun u => F u * Ge u) = fun u => Ge u * F u from funext fun u => mul_comm _ _]
      exact integral_even_mul_odd hGe hFo
    have e2 : ∫ u, P u * Ge u = 0 := by
      rw [show (fun u => P u * Ge u) = fun u => Ge u * P u from funext fun u => mul_comm _ _]
      exact integral_even_mul_odd hGe hPo
    rw [h Go hGos (supportedIn_oddPart hGa) (fun x => by rw [hGo, neg_one_mul]),
      weilPair_odd_even hFr hGer hFo hGe, e1, e2]
    ring

/-! ### Capacities are not attained on smooth tests -/

/-- **No smooth test attains a capacity.** Let `ℓ(G) = ∫PG` with `P` solving a linear ODE with
constant coefficients and `R = W + bℓ²`. If a smooth test `F` of the parity sector `ε` of `[−a, a]`
(with `P` of parity `ε`) maximized `ℓ²/R` over the smooth tests of that sector, its first
variation would give `(W)F = (W(F)/ℓ(F))P`, which has no smooth solution. -/
theorem not_isCapacityMax {P F : ℝ → ℝ} (ε : ℝ) (hε : ε = 1 ∨ ε = -1) (hF : ContDiff ℝ ∞ F)
    (hFa : SupportedIn a F) (hFp : ∀ x, F (-x) = ε * F x) (hP : ContDiff ℝ ∞ P)
    (hPp : ∀ x, P (-x) = ε * P x) {m : ℕ} (c : Fin (m + 1) → ℝ)
    (hode : iteratedDeriv (m + 1) P = ∑ i, c i • iteratedDeriv i P) (b : ℝ)
    (hℓ : ∫ u, P u * F u ≠ 0)
    (hmax : ∀ G : ℝ → ℝ, ContDiff ℝ ∞ G → SupportedIn a G → (∀ x, G (-x) = ε * G x) →
      (∫ u, P u * G u) ^ 2 * (weilQuad F + b * (∫ u, P u * F u) ^ 2) ≤
        (∫ u, P u * F u) ^ 2 * (weilQuad G + b * (∫ u, P u * G u) ^ 2)) : False := by
  have hFr := smooth_mem_realTests hF hFa
  have hFc := hasCompactSupport_of_supportedIn' hFa
  set A := ∫ u, P u * F u
  have hvar : ∀ G : ℝ → ℝ, ContDiff ℝ ∞ G → SupportedIn a G → (∀ x, G (-x) = ε * G x) →
      weilPair F G = 0 * (∫ u, F u * G u) + (weilQuad F / A) * ∫ u, P u * G u := by
    intro G hG hGa hGp
    have hGr := smooth_mem_realTests hG hGa
    have hGc := hasCompactSupport_of_supportedIn' hGa
    set B := ∫ u, P u * G u
    have iF := integrable_mul_of_continuous hP.continuous hF.continuous hFc
    have iG := integrable_mul_of_continuous hP.continuous hG.continuous hGc
    have hX : A ^ 2 * weilPair F G - A * B * weilQuad F = 0 := by
      refine eq_zero_of_forall_quadratic_nonneg (Y := A ^ 2 * weilQuad G - B ^ 2 * weilQuad F)
        fun t => ?_
      have h1 := hmax (F + t • G) (smooth_add_smul hF hG t) (supportedIn_add_smul hFa hGa t)
        (fun x => by simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hFp, hGp]; ring)
      have hl : ∫ u, P u * (F + t • G) u = A + t * B := by
        have : (fun u => P u * (F + t • G) u) = fun u => P u * F u + t * (P u * G u) := by
          funext u; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
        rw [this, integral_add iF (iG.const_mul t), integral_const_mul]
      have hq : weilQuad (F + t • G) = weilQuad F + 2 * t * weilPair F G + t ^ 2 * weilQuad G := by
        rw [weilQuad_add hFr (realTests.smul_mem t hGr), weilPair_smul_right]
        have : weilQuad (t • G) = t ^ 2 * weilQuad G := by
          show weilPair (t • G) (t • G) = _
          rw [weilPair_smul_left, weilPair_smul_right, show weilQuad G = weilPair G G from rfl]
          ring
        rw [this]; ring
      rw [hl, hq] at h1
      nlinarith [h1]
    have hA : A ≠ 0 := hℓ
    have h2 : A * weilPair F G - B * weilQuad F = 0 :=
      (mul_eq_zero.mp (show A * (A * weilPair F G - B * weilQuad F) = 0 by
        linear_combination hX)).resolve_left hA
    rw [zero_mul, zero_add, div_mul_eq_mul_div, eq_div_iff hA]
    linear_combination h2
  have hsol := isWindowSolution_of_sector ε hε hF hFa hFp hP.continuous hPp hvar
  have hF0 := eq_zero_of_isWindowSolution hF hFa hP c hode hsol
  apply hℓ
  rw [show A = ∫ u, P u * F u from rfl, hF0]
  simp

/-! ### Hyperplane-constrained ground states are not smooth -/

/-- **No smooth test attains a ground energy under a moment constraint.** With `P` as above and of
parity `ε`, a smooth test `F` of the sector with `∫PF = 0`, `W ≥ μ‖·‖²` on the sector's smooth tests
with `∫PG = 0`, and `W(F) = μ‖F‖²`, vanishes: the Lagrange equation is `(W − μ)F = κP`. -/
theorem eq_zero_of_isMin_on_hyperplane {P F : ℝ → ℝ} (ε : ℝ) (hε : ε = 1 ∨ ε = -1)
    (hF : ContDiff ℝ ∞ F) (hFa : SupportedIn a F) (hFp : ∀ x, F (-x) = ε * F x)
    (hP : ContDiff ℝ ∞ P) (hPp : ∀ x, P (-x) = ε * P x) {m : ℕ} (c : Fin (m + 1) → ℝ)
    (hode : iteratedDeriv (m + 1) P = ∑ i, c i • iteratedDeriv i P)
    (hFℓ : ∫ u, P u * F u = 0)
    (hfloor : ∀ G : ℝ → ℝ, ContDiff ℝ ∞ G → SupportedIn a G → (∀ x, G (-x) = ε * G x) →
      ∫ u, P u * G u = 0 → μ * ∫ u, G u ^ 2 ≤ weilQuad G)
    (heq : weilQuad F = μ * ∫ u, F u ^ 2) : F = 0 := by
  have hFr := smooth_mem_realTests hF hFa
  have hFc := hasCompactSupport_of_supportedIn' hFa
  -- the variational equation on the hyperplane
  have hvar : ∀ G : ℝ → ℝ, ContDiff ℝ ∞ G → SupportedIn a G → (∀ x, G (-x) = ε * G x) →
      ∫ u, P u * G u = 0 → weilPair F G = μ * ∫ u, F u * G u := by
    intro G hG hGa hGp hGℓ
    have hGr := smooth_mem_realTests hG hGa
    have hGc := hasCompactSupport_of_supportedIn' hGa
    refine sub_eq_zero.mp (eq_zero_of_forall_quadratic_nonneg
      (Y := weilQuad G - μ * ∫ u, G u ^ 2) fun t => ?_)
    have iF := integrable_mul_of_continuous hP.continuous hF.continuous hFc
    have iG := integrable_mul_of_continuous hP.continuous hG.continuous hGc
    have hl : ∫ u, P u * (F + t • G) u = 0 := by
      have : (fun u => P u * (F + t • G) u) = fun u => P u * F u + t * (P u * G u) := by
        funext u; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
      rw [this, integral_add iF (iG.const_mul t), integral_const_mul, hFℓ, hGℓ]; ring
    have hf := hfloor (F + t • G) (smooth_add_smul hF hG t) (supportedIn_add_smul hFa hGa t)
      (fun x => by simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hFp, hGp]; ring) hl
    have htG : t • G ∈ realTests := realTests.smul_mem t hGr
    rw [weilQuad_add hFr htG, weilPair_smul_right] at hf
    have e2 : weilQuad (t • G) = t ^ 2 * weilQuad G := by
      show weilPair (t • G) (t • G) = _
      rw [weilPair_smul_left, weilPair_smul_right, show weilQuad G = weilPair G G from rfl]; ring
    have hi1 := integrable_sq_of_continuous hFr.1.continuous hFr.2
    have hi2 := integrable_sq_of_continuous hGr.1.continuous hGr.2
    have hi3 : Integrable fun u => F u * G u :=
      integrable_mul_of_continuous hF.continuous hG.continuous hGc
    have e3 : ∫ u, (F + t • G) u ^ 2 =
        (∫ u, F u ^ 2) + 2 * t * (∫ u, F u * G u) + t ^ 2 * ∫ u, G u ^ 2 := by
      have : (fun u => (F + t • G) u ^ 2) =
          fun u => (F u ^ 2 + (2 * t) * (F u * G u)) + t ^ 2 * G u ^ 2 := by
        funext u; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
      have j0 : Integrable fun u => 2 * t * (F u * G u) := hi3.const_mul _
      have j1 : Integrable fun u => F u ^ 2 + 2 * t * (F u * G u) := hi1.add j0
      have j2 : Integrable fun u => t ^ 2 * G u ^ 2 := hi2.const_mul _
      rw [this, integral_add j1 j2, integral_add hi1 j0, integral_const_mul, integral_const_mul]
    rw [e2, heq, e3] at hf
    nlinarith
  -- the Lagrange multiplier
  by_cases hex : ∃ G₀ : ℝ → ℝ, ContDiff ℝ ∞ G₀ ∧ SupportedIn a G₀ ∧ (∀ x, G₀ (-x) = ε * G₀ x) ∧
      ∫ u, P u * G₀ u ≠ 0
  · obtain ⟨G₀, hG₀, hG₀a, hG₀p, hG₀ℓ⟩ := hex
    have hG₀r := smooth_mem_realTests hG₀ hG₀a
    have hG₀c := hasCompactSupport_of_supportedIn' hG₀a
    set κ' := (weilPair F G₀ - μ * ∫ u, F u * G₀ u) / ∫ u, P u * G₀ u
    refine eq_zero_of_isWindowSolution (μ := μ) (κ := κ') hF hFa hP c hode
      (isWindowSolution_of_sector (μ := μ) ε hε hF hFa hFp hP.continuous hPp
        fun G hG hGa hGp => ?_)
    have hGr := smooth_mem_realTests hG hGa
    have hGc := hasCompactSupport_of_supportedIn' hGa
    set s := (∫ u, P u * G u) / ∫ u, P u * G₀ u
    have iG := integrable_mul_of_continuous hP.continuous hG.continuous hGc
    have iG₀ := integrable_mul_of_continuous hP.continuous hG₀.continuous hG₀c
    have jG := integrable_mul_of_continuous hF.continuous hG.continuous hGc
    have jG₀ := integrable_mul_of_continuous hF.continuous hG₀.continuous hG₀c
    have hG' := hvar (G - s • G₀) (hG.sub (hG₀.const_smul s))
      (fun u hu => by simp [hGa u hu, hG₀a u hu])
      (fun x => by simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hGp, hG₀p]; ring)
      (by
        have : (fun u => P u * (G - s • G₀) u) = fun u => P u * G u - s * (P u * G₀ u) := by
          funext u; simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
        rw [this, integral_sub iG (iG₀.const_mul s), integral_const_mul]
        simp only [s]; field_simp; ring)
    rw [weilPair_sub_right hFr hGr (realTests.smul_mem s hG₀r), weilPair_smul_right] at hG'
    have hint : ∫ u, F u * (G - s • G₀) u = (∫ u, F u * G u) - s * ∫ u, F u * G₀ u := by
      have : (fun u => F u * (G - s • G₀) u) = fun u => F u * G u - s * (F u * G₀ u) := by
        funext u; simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
      rw [this, integral_sub jG (jG₀.const_mul s), integral_const_mul]
    rw [hint] at hG'
    simp only [κ', s] at hG' ⊢
    field_simp
    field_simp at hG'
    linear_combination hG'
  · push Not at hex
    refine eq_zero_of_isWindowEigen (μ := μ) hF hFa fun G hG hGa => ?_
    have h0 := isWindowSolution_of_sector (μ := μ) (κ := 0) ε hε hF hFa hFp hP.continuous hPp
      (fun G hG hGa hGp => by rw [hvar G hG hGa hGp (hex G hG hGa hGp), zero_mul, add_zero])
      G hG hGa
    rw [h0, zero_mul, add_zero]

/-! ### The capacities and constrained ground states of the field -/

theorem hasDerivAt_sinh_half (x : ℝ) :
    HasDerivAt (fun x : ℝ => Real.sinh (x / 2)) (Real.cosh (x / 2) / 2) x := by
  have := ((hasDerivAt_id x).div_const 2).sinh
  simp only [id] at this
  convert this using 1; ring

theorem hasDerivAt_cosh_half (x : ℝ) :
    HasDerivAt (fun x : ℝ => Real.cosh (x / 2)) (Real.sinh (x / 2) / 2) x := by
  have := ((hasDerivAt_id x).div_const 2).cosh
  simp only [id] at this
  convert this using 1; ring

/-- `sinh(x/2)'' = sinh(x/2)/4`. -/
theorem iteratedDeriv_two_sinh_half :
    iteratedDeriv (1 + 1) (fun x : ℝ => Real.sinh (x / 2)) =
      ∑ i : Fin 2, (![1 / 4, 0] : Fin 2 → ℝ) i • iteratedDeriv i (fun x : ℝ => Real.sinh (x / 2)) := by
  rw [iteratedDeriv_succ, iteratedDeriv_one, Fin.sum_univ_two]
  have h1 : deriv (fun x : ℝ => Real.sinh (x / 2)) = fun x => Real.cosh (x / 2) / 2 :=
    funext fun x => (hasDerivAt_sinh_half x).deriv
  have h2 : deriv (fun x : ℝ => Real.cosh (x / 2) / 2) = fun x => Real.sinh (x / 2) / 2 / 2 :=
    funext fun x => ((hasDerivAt_cosh_half x).div_const 2).deriv
  rw [h1, h2]
  funext x
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue, Fin.val_zero, Fin.val_one,
    iteratedDeriv_zero, iteratedDeriv_one, Pi.add_apply, Pi.smul_apply, smul_eq_mul, zero_mul,
    add_zero]
  ring

/-- `cosh(x/2)'' = cosh(x/2)/4`. -/
theorem iteratedDeriv_two_cosh_half :
    iteratedDeriv (1 + 1) (fun x : ℝ => Real.cosh (x / 2)) =
      ∑ i : Fin 2, (![1 / 4, 0] : Fin 2 → ℝ) i • iteratedDeriv i (fun x : ℝ => Real.cosh (x / 2)) := by
  rw [iteratedDeriv_succ, iteratedDeriv_one, Fin.sum_univ_two]
  have h1 : deriv (fun x : ℝ => Real.cosh (x / 2)) = fun x => Real.sinh (x / 2) / 2 :=
    funext fun x => (hasDerivAt_cosh_half x).deriv
  have h2 : deriv (fun x : ℝ => Real.sinh (x / 2) / 2) = fun x => Real.cosh (x / 2) / 2 / 2 :=
    funext fun x => ((hasDerivAt_sinh_half x).div_const 2).deriv
  rw [h1, h2]
  funext x
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue, Fin.val_zero, Fin.val_one,
    iteratedDeriv_zero, iteratedDeriv_one, Pi.add_apply, Pi.smul_apply, smul_eq_mul, zero_mul,
    add_zero]
  ring

/-- `x'' = 0`. -/
theorem iteratedDeriv_two_id :
    iteratedDeriv (1 + 1) (fun x : ℝ => x) =
      ∑ i : Fin 2, (0 : Fin 2 → ℝ) i • iteratedDeriv i (fun x : ℝ => x) := by
  rw [iteratedDeriv_succ, iteratedDeriv_one]
  simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero]
  rw [deriv_id'']
  funext x
  exact deriv_const x 1

/-- `1' = 0`. -/
theorem iteratedDeriv_one_const :
    iteratedDeriv (0 + 1) (fun _ : ℝ => (1 : ℝ)) =
      ∑ i : Fin 1, (0 : Fin 1 → ℝ) i • iteratedDeriv i (fun _ : ℝ => (1 : ℝ)) := by
  simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero, zero_add, iteratedDeriv_one]
  funext x
  exact deriv_const x 1

/-- **The moment capacity of the odd sector is not attained on smooth tests.** For every `b` and
every window, no smooth odd test `F` with `∫xF ≠ 0` maximizes `(∫xG)²/(W(G) + b(∫xG)²)` over the
smooth odd tests: the extremal of the capacity form of the odd unit window is singular at the
edge. -/
theorem not_isMax_oddMomentCapacity {F : ℝ → ℝ} (b : ℝ) (hF : ContDiff ℝ ∞ F)
    (hFa : SupportedIn a F) (hFo : ∀ x, F (-x) = -F x) (hℓ : ∫ u, u * F u ≠ 0)
    (hmax : ∀ G : ℝ → ℝ, ContDiff ℝ ∞ G → SupportedIn a G → (∀ x, G (-x) = -G x) →
      (∫ u, u * G u) ^ 2 * (weilQuad F + b * (∫ u, u * F u) ^ 2) ≤
        (∫ u, u * F u) ^ 2 * (weilQuad G + b * (∫ u, u * G u) ^ 2)) : False :=
  not_isCapacityMax (P := fun u => u) (-1) (Or.inr rfl) hF hFa
    (fun x => by rw [hFo, neg_one_mul]) contDiff_id (fun x => by ring) (m := 1) 0
    iteratedDeriv_two_id b hℓ fun G hG hGa hGp => hmax G hG hGa fun x => by rw [hGp, neg_one_mul]

/-- **The sinh capacity is not attained on smooth tests**: no smooth odd test with
`∫ sinh(x/2)F ≠ 0` maximizes `(∫ sinh(x/2)G)²/(W(G) + b(∫ sinh(x/2)G)²)` over the smooth odd tests
of a window (for `b = 2` this is the pole's sinh capacity `⟨s, F⟩²/(2M(F))`). -/
theorem not_isMax_sinhCapacity {F : ℝ → ℝ} (b : ℝ) (hF : ContDiff ℝ ∞ F)
    (hFa : SupportedIn a F) (hFo : ∀ x, F (-x) = -F x) (hℓ : ∫ u, Real.sinh (u / 2) * F u ≠ 0)
    (hmax : ∀ G : ℝ → ℝ, ContDiff ℝ ∞ G → SupportedIn a G → (∀ x, G (-x) = -G x) →
      (∫ u, Real.sinh (u / 2) * G u) ^ 2 *
          (weilQuad F + b * (∫ u, Real.sinh (u / 2) * F u) ^ 2) ≤
        (∫ u, Real.sinh (u / 2) * F u) ^ 2 *
          (weilQuad G + b * (∫ u, Real.sinh (u / 2) * G u) ^ 2)) : False :=
  not_isCapacityMax (P := fun u => Real.sinh (u / 2)) (-1) (Or.inr rfl) hF hFa
    (fun x => by rw [hFo, neg_one_mul]) (Real.contDiff_sinh.comp (contDiff_id.div_const 2))
    (fun x => by rw [neg_div, Real.sinh_neg, neg_one_mul]) (m := 1) ![1 / 4, 0]
    iteratedDeriv_two_sinh_half b hℓ fun G hG hGa hGp => hmax G hG hGa fun x => by
      rw [hGp, neg_one_mul]

/-- **The even ground state on the cosh hyperplane is not smooth**: a smooth even test `F` with
`∫ cosh(x/2)F = 0` that attains `μ = inf W/‖·‖²` over the smooth even tests of the window on that
hyperplane vanishes. This is the constrained problem of the cosh capacity. -/
theorem eq_zero_of_isMin_on_coshHyperplane {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F)
    (hFa : SupportedIn a F) (hFe : ∀ x, F (-x) = F x) (hFℓ : ∫ u, Real.cosh (u / 2) * F u = 0)
    (hfloor : ∀ G : ℝ → ℝ, ContDiff ℝ ∞ G → SupportedIn a G → (∀ x, G (-x) = G x) →
      ∫ u, Real.cosh (u / 2) * G u = 0 → μ * ∫ u, G u ^ 2 ≤ weilQuad G)
    (heq : weilQuad F = μ * ∫ u, F u ^ 2) : F = 0 :=
  eq_zero_of_isMin_on_hyperplane (P := fun u => Real.cosh (u / 2)) 1 (Or.inl rfl) hF hFa
    (fun x => by rw [hFe, one_mul]) (Real.contDiff_cosh.comp (contDiff_id.div_const 2))
    (fun x => by rw [neg_div, Real.cosh_neg, one_mul]) (m := 1) ![1 / 4, 0]
    iteratedDeriv_two_cosh_half hFℓ (fun G hG hGa hGp => hfloor G hG hGa fun x => by
      rw [hGp, one_mul]) heq

/-- **The mean-zero even ground state is not smooth**: a smooth even test `F` with `∫F = 0`
attaining `inf W/‖·‖²` over the smooth even mean-zero tests of the window vanishes. -/
theorem eq_zero_of_isMin_on_meanZero {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F)
    (hFa : SupportedIn a F) (hFe : ∀ x, F (-x) = F x) (hFℓ : ∫ u, F u = 0)
    (hfloor : ∀ G : ℝ → ℝ, ContDiff ℝ ∞ G → SupportedIn a G → (∀ x, G (-x) = G x) →
      ∫ u, G u = 0 → μ * ∫ u, G u ^ 2 ≤ weilQuad G)
    (heq : weilQuad F = μ * ∫ u, F u ^ 2) : F = 0 :=
  eq_zero_of_isMin_on_hyperplane (P := fun _ => (1 : ℝ)) 1 (Or.inl rfl) hF hFa
    (fun x => by rw [hFe, one_mul]) contDiff_const (fun x => by ring) (m := 0) 0
    iteratedDeriv_one_const (by simpa using hFℓ)
    (fun G hG hGa hGp hGℓ => hfloor G hG hGa (fun x => by rw [hGp, one_mul])
      (by simpa using hGℓ)) heq

end GaloisForLFunctions.SignedWindowCriticality

end

