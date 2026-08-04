import GaloisForLFunctions.HTGeometry.AnalyticRootFactor
import GaloisForLFunctions.HTGeometry.PolynomialAntiderivative
import GaloisForLFunctions.HTGeometry.PolynomialGrowthBound
import GaloisForLFunctions.HTGeometry.TranscendentalEntireOrderOne

/-!
# A transcendental entire function comes near every value arbitrarily far out

Outside every disc a transcendental entire function takes values arbitrarily close to every complex
number.  This is the Casorati–Weierstrass theorem at the essential singularity at infinity, in the
form that only entire functions require.

The proof needs no singularity theory.  If some value were avoided by a definite margin outside a
disc, the zeros of the shifted function would all lie in that disc; extracting them as a polynomial
factor leaves a zero-free entire cofactor whose reciprocal is bounded by a polynomial, hence is a
polynomial, hence — having no zeros — a constant.  The shifted function is then a polynomial.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

/-- **Casorati–Weierstrass at infinity.**  A transcendental entire function comes arbitrarily close
to every value at points of arbitrarily large modulus. -/
theorem exists_norm_gt_and_dist_lt_of_transcendental {f : ℂ → ℂ}
    (hf : TranscendentalEntire f) (R : ℝ) (w₀ : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ z : ℂ, R < ‖z‖ ∧ ‖f z - w₀‖ < δ := by
  by_contra hexists
  have hcon : ∀ z : ℂ, R < ‖z‖ → δ ≤ ‖f z - w₀‖ := by
    intro z hz
    by_contra hlt
    exact hexists ⟨z, hz, not_le.mp hlt⟩
  set R' : ℝ := max R 0 with hR'
  have hR'0 : 0 ≤ R' := le_max_right _ _
  have hRR' : R ≤ R' := le_max_left _ _
  set F : ℂ → ℂ := fun z => f z - w₀ with hFdef
  have hfan : AnalyticOnNhd ℂ f (Set.univ : Set ℂ) :=
    DifferentiableOn.analyticOnNhd (fun z _ => (hf.1 z).differentiableWithinAt) isOpen_univ
  have hFan : AnalyticOnNhd ℂ F (Set.univ : Set ℂ) := hfan.sub analyticOnNhd_const
  have hfar : ∀ z : ℂ, R' < ‖z‖ → δ ≤ ‖F z‖ := fun z hz => hcon z (lt_of_le_of_lt hRR' hz)
  -- a point where the shifted function is nonzero
  set z₁ : ℂ := ((R' + 1 : ℝ) : ℂ) with hz₁def
  have hz₁n : ‖z₁‖ = R' + 1 := by
    rw [hz₁def, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  have hFz₁ : F z₁ ≠ 0 := by
    have hge : δ ≤ ‖F z₁‖ := hfar z₁ (by rw [hz₁n]; linarith)
    intro h0
    rw [h0, norm_zero] at hge
    linarith
  have hnz : ∀ a ∈ (Set.univ : Set ℂ), ¬ ∀ᶠ z in nhds a, F z = 0 := by
    intro a _ hloc
    have hev : F =ᶠ[nhds a] 0 := by
      filter_upwards [hloc] with z hz
      exact hz
    have heq := hFan.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (Set.mem_univ a) hev
    exact hFz₁ (heq (Set.mem_univ z₁))
  -- extract the zeros, which all lie in the disc
  obtain ⟨P, g, _, hgan, hgfree, hfac⟩ :=
    exists_polynomial_factor_closedBall (c := 0) (R := R') isOpen_univ (Set.subset_univ _)
      hFan hnz
  have hgall : ∀ z : ℂ, g z ≠ 0 := by
    intro z
    by_cases hz : ‖z‖ ≤ R'
    · exact hgfree z (by simpa [Metric.mem_closedBall] using hz)
    · have hge : δ ≤ ‖F z‖ := hfar z (not_le.mp hz)
      intro hg0
      have hFz : F z = 0 := by rw [hfac z (Set.mem_univ z), hg0, mul_zero]
      rw [hFz, norm_zero] at hge
      linarith
  set u : ℂ → ℂ := fun z => (g z)⁻¹ with hudef
  have hud : Differentiable ℂ u :=
    fun z => ((hgan z (Set.mem_univ z)).differentiableAt.inv (hgall z))
  set d : ℕ := P.natDegree with hd
  obtain ⟨M₁, hM₁⟩ := (isCompact_closedBall (0 : ℂ) R').exists_bound_of_continuousOn
    (fun z _ => (hud z).continuousAt.continuousWithinAt)
  set C₀ : ℝ := max M₁ (coeffNormSum P / δ) with hC₀
  have hCδ : coeffNormSum P ≤ C₀ * δ := by
    have h1 : coeffNormSum P / δ ≤ C₀ := le_max_right _ _
    rw [div_le_iff₀ hδ] at h1
    exact h1
  have hbound : ∀ z : ℂ, ‖u z‖ ≤ C₀ * (1 + ‖z‖) ^ d := by
    intro z
    have hpow1 : (1 : ℝ) ≤ (1 + ‖z‖) ^ d := one_le_pow₀ (by linarith [norm_nonneg z])
    by_cases hz : ‖z‖ ≤ R'
    · have h1 : ‖u z‖ ≤ M₁ := hM₁ z (by simpa [Metric.mem_closedBall] using hz)
      have h2 : M₁ ≤ C₀ := le_max_left _ _
      nlinarith [norm_nonneg (u z)]
    · have hge : δ ≤ ‖F z‖ := hfar z (not_le.mp hz)
      have hug : ‖u z‖ * ‖g z‖ = 1 := by
        rw [← norm_mul, hudef]
        simp [inv_mul_cancel₀ (hgall z)]
      have hnorm : ‖F z‖ = ‖P.eval z‖ * ‖g z‖ := by
        rw [hfac z (Set.mem_univ z), norm_mul]
      have hkey : ‖u z‖ * ‖F z‖ = ‖P.eval z‖ := by
        rw [hnorm]
        calc ‖u z‖ * (‖P.eval z‖ * ‖g z‖) = (‖u z‖ * ‖g z‖) * ‖P.eval z‖ := by ring
          _ = ‖P.eval z‖ := by rw [hug, one_mul]
      have hPle : ‖P.eval z‖ ≤ coeffNormSum P * (1 + ‖z‖) ^ d :=
        norm_eval_le_coeffNormSum P z
      have hu0 : 0 ≤ ‖u z‖ := norm_nonneg _
      have hstep : ‖u z‖ * δ ≤ ‖u z‖ * ‖F z‖ := mul_le_mul_of_nonneg_left hge hu0
      have hfin : ‖u z‖ * δ ≤ C₀ * δ * (1 + ‖z‖) ^ d := by
        have h1 : coeffNormSum P * (1 + ‖z‖) ^ d ≤ C₀ * δ * (1 + ‖z‖) ^ d :=
          mul_le_mul_of_nonneg_right hCδ (by positivity)
        linarith [hstep, hkey, hPle]
      refine le_of_mul_le_mul_right ?_ hδ
      linarith [hfin]
  -- the reciprocal cofactor is a polynomial without zeros, hence a constant
  have hpoly : ∃ p : Polynomial ℂ, ∀ z : ℂ, u z = p.eval z := by
    by_contra hnp
    obtain ⟨z, hz⟩ := exists_norm_gt_of_not_polynomial hud hnp C₀ d
    exact absurd (hbound z) (not_le.mpr hz)
  obtain ⟨p, hp⟩ := hpoly
  have hpg : ∀ z : ℂ, p.eval z * g z = 1 := by
    intro z
    rw [← hp z, hudef]
    exact inv_mul_cancel₀ (hgall z)
  have hpne : ∀ z : ℂ, p.eval z ≠ 0 := by
    intro z h0
    have h1 := hpg z
    rw [h0, zero_mul] at h1
    exact zero_ne_one h1
  have hdeg : p.natDegree = 0 := by
    by_contra hdz
    have hdpos : 0 < p.degree :=
      Polynomial.natDegree_pos_iff_degree_pos.mp (Nat.pos_of_ne_zero hdz)
    obtain ⟨r, hr⟩ := Complex.exists_root hdpos
    exact hpne r hr
  have hpc : p = Polynomial.C (p.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hdeg
  have ha : p.coeff 0 ≠ 0 := by
    have h1 := hpne 0
    rw [hpc] at h1
    simpa using h1
  have hgc : ∀ z : ℂ, g z = (p.coeff 0)⁻¹ := by
    intro z
    have h1 := hpg z
    rw [hpc, Polynomial.eval_C] at h1
    field_simp
    linear_combination h1
  -- the shifted function is a polynomial multiple of the extracted factor
  refine hf.2 ⟨Polynomial.C w₀ + Polynomial.C (p.coeff 0)⁻¹ * P, ?_⟩
  intro z
  have h1 : f z - w₀ = P.eval z * g z := hfac z (Set.mem_univ z)
  rw [hgc z] at h1
  rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_C]
  linear_combination h1

end GaloisForLFunctions.HTGeometry
