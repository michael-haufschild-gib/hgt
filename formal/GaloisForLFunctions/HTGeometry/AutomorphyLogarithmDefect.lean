import GaloisForLFunctions.HTGeometry.AutomorphyFactorCocycle

/-!
# Logarithms of a factor of automorphy

A continuous nowhere-vanishing factor of automorphy on a complex normed space always admits a
continuous logarithm, because the space is contractible and hence simply connected.  The logarithm
is then automatically quasi-additive with a **constant integral** defect: the pointwise defect is an
integer at every base point, it is continuous, and a continuous integer-valued function on a
connected space is constant.

This supplies the analytic input of the integrality half of the generalized Riemann relations.
Together with `automorphyFactor_commutator_int` and `exists_hermitian_of_alternating` the chain runs
from a factor of automorphy to a Hermitian form with integral imaginary part.
-/

open Complex Set Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- **A continuous integer-valued function on a preconnected space is constant.** -/
theorem eq_of_continuous_int_valued {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    {u : X → ℂ} (hu : Continuous u) (hint : ∀ x, ∃ n : ℤ, u x = (n : ℂ)) (x y : X) :
    u x = u y := by
  have hloc : IsLocallyConstant u := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro z
    have hnhds : ∀ᶠ w in nhds z, ‖u w - u z‖ < 1 := by
      have hcont := hu.continuousAt (x := z)
      have h := Metric.tendsto_nhds.mp hcont 1 one_pos
      filter_upwards [h] with w hw
      rwa [Complex.dist_eq] at hw
    filter_upwards [hnhds] with w hw
    obtain ⟨n, hn⟩ := hint w
    obtain ⟨m, hm⟩ := hint z
    rw [hn, hm] at hw ⊢
    have hcast : ((n : ℂ)) - ((m : ℂ)) = (((n - m : ℤ) : ℂ)) := by push_cast; ring
    rw [hcast] at hw
    have hzero : n - m = 0 := by
      by_contra hne
      have habs : (1 : ℤ) ≤ |n - m| := Int.one_le_abs hne
      have h1 : (1 : ℝ) ≤ ‖((n - m : ℤ) : ℂ)‖ := by
        simp only [Complex.norm_intCast]
        exact_mod_cast habs
      linarith
    have hnm : n = m := by omega
    rw [hnm]
  exact hloc.apply_eq_of_preconnectedSpace x y

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]

theorem isSimplyConnected_univ : IsSimplyConnected (Set.univ : Set W) := by
  rw [IsSimplyConnected]
  exact (Homeomorph.Set.univ W).toHomotopyEquiv.simplyConnectedSpace

/-- **Continuous logarithm of a nowhere-vanishing continuous function on a normed space.** -/
theorem exists_continuous_exp_eq {g : W → ℂ} (hg : Continuous g) (hg0 : ∀ z, g z ≠ 0) :
    ∃ L : W → ℂ, Continuous L ∧ ∀ z, Complex.exp (L z) = g z := by
  obtain ⟨f, hfc, hfe⟩ := Complex.exists_continuousOn_eqOn_exp_comp isSimplyConnected_univ
    isOpen_univ hg.continuousOn (by rintro ⟨z, -, hz⟩; exact hg0 z hz)
  refine ⟨f, continuousOn_univ.mp hfc, fun z => hfe (mem_univ z)⟩

theorem two_pi_I_ne_zero : (2 : ℂ) * (Real.pi : ℂ) * Complex.I ≠ 0 := by
  have h1 : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  simp [h1, Complex.I_ne_zero]

/-- **Every continuous nowhere-vanishing factor of automorphy has a quasi-additive logarithm whose
defect is a constant integer.** -/
theorem exists_isQuasiAdditive_log_of_isMulTwoCocycle {e : W → W → ℂ} (he : ∀ γ z, e γ z ≠ 0)
    (hcont : ∀ γ, Continuous (e γ)) (hcoc : IsMulTwoCocycle e) :
    ∃ F c : W → W → ℂ,
      (∀ γ z, Complex.exp (2 * (Real.pi : ℂ) * Complex.I * F γ z) = e γ z) ∧
      IsQuasiAdditive F c ∧
      (∀ γ γ', ∃ n : ℤ, c γ γ' = (n : ℂ)) := by
  have hlog : ∀ γ : W, ∃ L : W → ℂ, Continuous L ∧ ∀ z, Complex.exp (L z) = e γ z :=
    fun γ => exists_continuous_exp_eq (hcont γ) (he γ)
  choose L hLc hLe using hlog
  refine ⟨fun γ z => L γ z / (2 * (Real.pi : ℂ) * Complex.I),
    fun γ γ' => L (γ + γ') 0 / (2 * (Real.pi : ℂ) * Complex.I)
      - L γ (0 + γ') / (2 * (Real.pi : ℂ) * Complex.I)
      - L γ' 0 / (2 * (Real.pi : ℂ) * Complex.I), ?_, ?_, ?_⟩
  · intro γ z
    rw [mul_div_cancel₀ _ two_pi_I_ne_zero]
    exact hLe γ z
  · -- quasi-additivity: the defect does not depend on the base point
    intro γ γ' z
    have hexp : ∀ a b : W, Complex.exp (2 * (Real.pi : ℂ) * Complex.I
        * (L a b / (2 * (Real.pi : ℂ) * Complex.I))) = e a b := by
      intro a b
      rw [mul_div_cancel₀ _ two_pi_I_ne_zero]
      exact hLe a b
    have hdcont : Continuous fun w : W =>
        L (γ + γ') w / (2 * (Real.pi : ℂ) * Complex.I)
          - L γ (w + γ') / (2 * (Real.pi : ℂ) * Complex.I)
          - L γ' w / (2 * (Real.pi : ℂ) * Complex.I) := by
      have h1 : Continuous fun w : W => L (γ + γ') w / (2 * (Real.pi : ℂ) * Complex.I) :=
        (hLc (γ + γ')).div_const _
      have h2 : Continuous fun w : W => L γ (w + γ') / (2 * (Real.pi : ℂ) * Complex.I) :=
        ((hLc γ).comp (continuous_id.add continuous_const)).div_const _
      have h3 : Continuous fun w : W => L γ' w / (2 * (Real.pi : ℂ) * Complex.I) :=
        (hLc γ').div_const _
      exact (h1.sub h2).sub h3
    have hdint : ∀ w : W, ∃ n : ℤ,
        L (γ + γ') w / (2 * (Real.pi : ℂ) * Complex.I)
          - L γ (w + γ') / (2 * (Real.pi : ℂ) * Complex.I)
          - L γ' w / (2 * (Real.pi : ℂ) * Complex.I) = (n : ℂ) :=
      fun w => exists_int_logDefect he hcoc hexp γ γ' w
    have hconst := eq_of_continuous_int_valued hdcont hdint z 0
    linear_combination hconst
  · intro γ γ'
    have hexp : ∀ a b : W, Complex.exp (2 * (Real.pi : ℂ) * Complex.I
        * (L a b / (2 * (Real.pi : ℂ) * Complex.I))) = e a b := by
      intro a b
      rw [mul_div_cancel₀ _ two_pi_I_ne_zero]
      exact hLe a b
    exact exists_int_logDefect he hcoc hexp γ γ' 0

end GaloisForLFunctions.HTGeometry
