import GaloisForLFunctions.HTGeometry.PolynomialProjectiveBoundaryWitness
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
# The neutral Gamma-ratio class realizes the projective-boundary interface

The coefficient class of the neutral Gamma ratio `G_θ(s) = Γ(s + iθ)/Γ(s)` times an arbitrary
rational function satisfies `HasPolynomialFunctionalProjectiveBoundary` unconditionally.  For a
finite tuple `G_θ · p_j/q_j` translated along an arbitrary upper-height sequence, one common
meromorphic normalization — the reciprocal translated Gamma ratio times the cleared common
denominator and the recession weight `(iT)^{-d}` — turns every member into the scaled vertical
translate of its cleared numerator `p_j · ∏_{l ≠ j} q_l`.  Above a height determined by each
compact set the Gamma ratio has no zeros (`Γ` vanishes only at the encoded nonpositive-integer
poles, which lie on the real axis and on one horizontal line below it) and the finitely many
denominator roots are left behind, so the identification holds eventually on every compact set and
the locally uniform polynomial one-point recession supplies the nonzero polynomial limit tuple.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The neutral Gamma ratio `G_θ(s) = Γ(s + iθ)/Γ(s)`. -/
def neutralGammaRatio (θ : ℝ) (s : ℂ) : ℂ :=
  Complex.Gamma (s + Complex.I * (θ : ℂ)) / Complex.Gamma s

/-- The neutral Gamma-ratio coefficient class: `G_θ` times an arbitrary rational function. -/
def neutralGammaRatioRationalClass (θ : ℝ) : Set (ℂ → ℂ) :=
  {u | ∃ p q : Polynomial ℂ, q ≠ 0 ∧
    u = fun z => neutralGammaRatio θ z * (p.eval z / q.eval z)}

/-- In the open upper half-plane and for `0 ≤ θ` the Gamma ratio does not vanish: neither Gamma
factor has a zero there. -/
theorem neutralGammaRatio_ne_zero {θ : ℝ} (hθ : 0 ≤ θ) {s : ℂ} (hs : 0 < s.im) :
    neutralGammaRatio θ s ≠ 0 := by
  have hnum : Complex.Gamma (s + Complex.I * (θ : ℂ)) ≠ 0 := by
    refine Complex.Gamma_ne_zero fun m h => ?_
    have him : (s + Complex.I * (θ : ℂ)).im = s.im + θ := by simp
    have h0 : (s + Complex.I * (θ : ℂ)).im = 0 := by rw [h]; simp
    rw [him] at h0
    linarith
  have hden : Complex.Gamma s ≠ 0 := by
    refine Complex.Gamma_ne_zero fun m h => ?_
    have h0 : s.im = 0 := by rw [h]; simp
    linarith
  exact div_ne_zero hnum hden

/-- A nonzero polynomial has an escape radius beyond which it cannot vanish. -/
theorem exists_norm_gt_eval_ne_zero {q : Polynomial ℂ} (hq : q ≠ 0) :
    ∃ M : ℝ, ∀ z : ℂ, M < ‖z‖ → q.eval z ≠ 0 := by
  have hfin : ({x : ℂ | q.IsRoot x}).Finite := Polynomial.finite_setOf_isRoot hq
  have himg : ((fun z : ℂ => ‖z‖) '' {x : ℂ | q.IsRoot x}).Finite := hfin.image _
  obtain ⟨M, hM⟩ := himg.bddAbove
  refine ⟨M, fun z hz hroot => ?_⟩
  exact absurd (hM ⟨z, hroot, rfl⟩) (not_le.mpr hz)

/-- Locally uniform convergence transfers to a sequence agreeing eventually near every point. -/
theorem tendstoLocallyUniformly_congr_eventually_local {α β ι : Type*} [TopologicalSpace α]
    [UniformSpace β] {F G : ι → α → β} {f : α → β} {p : Filter ι}
    (h : TendstoLocallyUniformly F f p)
    (heq : ∀ x : α, ∃ t ∈ 𝓝 x, ∀ᶠ n in p, ∀ y ∈ t, F n y = G n y) :
    TendstoLocallyUniformly G f p := by
  intro v hv x
  obtain ⟨t, ht, hev⟩ := h v hv x
  obtain ⟨t', ht', hev'⟩ := heq x
  refine ⟨t ∩ t', Filter.inter_mem ht ht', ?_⟩
  filter_upwards [hev, hev'] with n hn hn' y hy
  rw [← hn' y hy.2]
  exact hn y hy.1

/-- The clearing identity in atoms: dividing out the nonvanishing Gamma value and the member's own
denominator turns the normalized member into its cleared numerator. -/
theorem gamma_clearing_identity (N Gv Pj Qj Pe : ℂ) (hG : Gv ≠ 0) (hQ : Qj ≠ 0) :
    Pj * Pe / N = N⁻¹ * Gv⁻¹ * (Qj * Pe) * (Gv * (Pj / Qj)) := by
  field_simp

/-- **The neutral Gamma-ratio rational class satisfies the projective-boundary interface.**  The
common normalization is the reciprocal translated Gamma ratio times the cleared common denominator
and the recession weight `(iT)^{-d}`; the limits are the leading coefficients of the cleared
numerators `p_j · ∏_{l ≠ j} q_l` at the common degree bound. -/
theorem hasPolynomialFunctionalProjectiveBoundary_neutralGammaRatioRationalClass
    {θ : ℝ} (hθ : 0 ≤ θ) :
    HasPolynomialFunctionalProjectiveBoundary (neutralGammaRatioRationalClass θ) := by
  classical
  intro r a haK ha S hS
  choose p q hq hfa using fun j => haK j
  have hbne : ∃ j, p j * ∏ l ∈ Finset.univ.erase j, q l ≠ 0 := by
    obtain ⟨j0, hj0⟩ := ha
    refine ⟨j0, ?_⟩
    have hp0 : p j0 ≠ 0 := by
      intro hzero
      apply hj0
      rw [hfa j0, hzero]
      funext z
      simp
    exact mul_ne_zero hp0 (Finset.prod_ne_zero_iff.mpr fun l _ => hq l)
  set b : Fin r → Polynomial ℂ := fun j => p j * ∏ l ∈ Finset.univ.erase j, q l with hbdef
  set d := Finset.univ.sup (fun j => (b j).natDegree) with hd
  obtain ⟨j1, hj1⟩ := exists_coeff_sup_natDegree_ne_zero b hbne
  choose M hM using fun l => exists_norm_gt_eval_ne_zero (hq l)
  refine ⟨id, strictMono_id,
    fun k z => ((Complex.I * (S k : ℂ)) ^ d)⁻¹ *
      (neutralGammaRatio θ (z + Complex.I * (S k : ℂ)))⁻¹ *
      ∏ l, (q l).eval (z + Complex.I * (S k : ℂ)),
    fun j => Polynomial.C ((b j).coeff d),
    ⟨j1, fun h => hj1 (Polynomial.C_eq_zero.mp h)⟩, ?_⟩
  intro j
  have hdeg : (b j).natDegree ≤ d :=
    Finset.le_sup (f := fun j => (b j).natDegree) (Finset.mem_univ j)
  have hbase := TendstoLocallyUniformly.comp_tendsto
    (poly_scaled_translate_tendstoLocallyUniformly (b j) hdeg) hS
  have hlim : (fun z : ℂ => (Polynomial.C ((b j).coeff d)).eval z)
      = fun _ : ℂ => (b j).coeff d := by
    funext z
    simp
  show TendstoLocallyUniformly
    (fun (k : ℕ) (z : ℂ) =>
      ((Complex.I * (S (id k) : ℂ)) ^ d)⁻¹ *
        (neutralGammaRatio θ (z + Complex.I * (S (id k) : ℂ)))⁻¹ *
        (∏ l, (q l).eval (z + Complex.I * (S (id k) : ℂ))) *
        a j (z + Complex.I * (S (id k) : ℂ)))
    (fun z : ℂ => (Polynomial.C ((b j).coeff d)).eval z) atTop
  rw [hlim]
  simp only [id_eq]
  refine tendstoLocallyUniformly_congr_eventually_local hbase ?_
  intro x
  refine ⟨Metric.ball x 1, Metric.ball_mem_nhds x one_pos, ?_⟩
  have hev1 : ∀ᶠ k in atTop, ‖x‖ + 1 < S k :=
    hS.eventually (eventually_gt_atTop _)
  have hev2 : ∀ᶠ k in atTop, ∀ l, M l + (‖x‖ + 1) < S k :=
    Filter.eventually_all.mpr fun l => hS.eventually (eventually_gt_atTop _)
  filter_upwards [hev1, hev2] with k hk1 hk2 y hy
  have hyx : ‖y‖ < ‖x‖ + 1 := by
    have hdist : dist y x < 1 := Metric.mem_ball.mp hy
    have h2 : ‖y‖ - ‖x‖ ≤ ‖y - x‖ := norm_sub_norm_le y x
    rw [dist_eq_norm] at hdist
    linarith
  have hSpos : (0 : ℝ) < S k := by
    have := norm_nonneg x
    linarith
  have hnormIS : ‖Complex.I * (S k : ℂ)‖ = S k := by
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hSpos]
  have hwnorm : S k - ‖y‖ ≤ ‖y + Complex.I * (S k : ℂ)‖ := by
    have h4 : ‖Complex.I * (S k : ℂ)‖ ≤ ‖y + Complex.I * (S k : ℂ)‖ + ‖y‖ := by
      calc ‖Complex.I * (S k : ℂ)‖ = ‖(y + Complex.I * (S k : ℂ)) - y‖ := by
            congr 1
            ring
        _ ≤ ‖y + Complex.I * (S k : ℂ)‖ + ‖y‖ := norm_sub_le _ _
    rw [hnormIS] at h4
    linarith
  have him : 0 < (y + Complex.I * (S k : ℂ)).im := by
    have h6 : (y + Complex.I * (S k : ℂ)).im = y.im + S k := by simp
    have h7 : |y.im| ≤ ‖y‖ := Complex.abs_im_le_norm y
    have h8 : -‖y‖ ≤ y.im := (abs_le.mp h7).1
    rw [h6]
    linarith
  have hΓ : neutralGammaRatio θ (y + Complex.I * (S k : ℂ)) ≠ 0 :=
    neutralGammaRatio_ne_zero hθ him
  have hql : ∀ l, (q l).eval (y + Complex.I * (S k : ℂ)) ≠ 0 := by
    intro l
    refine hM l _ ?_
    have := hk2 l
    linarith
  have hprod : (∏ l, (q l).eval (y + Complex.I * (S k : ℂ)))
      = (q j).eval (y + Complex.I * (S k : ℂ)) *
        ∏ l ∈ Finset.univ.erase j, (q l).eval (y + Complex.I * (S k : ℂ)) :=
    (Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)).symm
  rw [hfa j]
  simp only [hbdef, Polynomial.eval_mul, Polynomial.eval_prod, hprod]
  exact gamma_clearing_identity ((Complex.I * (S k : ℂ)) ^ d)
    (neutralGammaRatio θ (y + Complex.I * (S k : ℂ)))
    ((p j).eval (y + Complex.I * (S k : ℂ)))
    ((q j).eval (y + Complex.I * (S k : ℂ)))
    (∏ l ∈ Finset.univ.erase j, (q l).eval (y + Complex.I * (S k : ℂ)))
    hΓ (hql j)

/-- **The two-stage boundary of the neutral Gamma-ratio class, unconditionally.**  The projective
boundary of the Gamma-ratio rational class is polynomial, and every nonzero polynomial tuple
recedes to its nonzero leading-coefficient vector. -/
theorem neutralGammaRatio_twoStageBoundary_rationalClass {θ : ℝ} (hθ : 0 ≤ θ) :
    HasPolynomialFunctionalProjectiveBoundary (neutralGammaRatioRationalClass θ) ∧
      ∀ {r : ℕ} (p : Fin r → Polynomial ℂ), (∃ j, p j ≠ 0) →
        ∃ d : ℕ, (∃ j, (p j).coeff d ≠ 0) ∧
          ∀ (z : ℂ) (j : Fin r),
            Filter.Tendsto
              (fun T : ℝ =>
                (p j).eval (z + Complex.I * (T : ℂ)) /
                  (Complex.I * (T : ℂ)) ^ d)
              atTop (𝓝 ((p j).coeff d)) :=
  neutralGammaRatio_twoStageBoundary _
    (hasPolynomialFunctionalProjectiveBoundary_neutralGammaRatioRationalClass hθ)

end

end GaloisForLFunctions.HTGeometry
