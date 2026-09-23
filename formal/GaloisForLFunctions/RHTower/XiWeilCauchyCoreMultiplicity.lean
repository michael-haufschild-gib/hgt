import GaloisForLFunctions.RHTower.XiWeilHilbertCore
import GaloisForLFunctions.RHTower.DeningerArithmeticGeometricJetExhaustion
import GaloisForLFunctions.RHTower.XiHadamardFactorization

/-!
# The multiplicity annihilator of the Cauchy resolvent core

The Cauchy evaluation vectors `q => (rho_q - z)^{-1}` are constant along each multiplicity fibre of
the Xi divisor, so they can never separate two copies of a multiple zero.  This file proves that
this is the *only* obstruction: a divisor vector is orthogonal to the algebraic span of the regular
Cauchy vectors exactly when its sum over the multiplicity copies above every Xi zero vanishes.

The nontrivial direction extracts the fibre sum as a residue.  The resolvent transform of an
orthogonal vector vanishes at every regular point; multiplying by `a - z` turns the fibre part into
the constant fibre sum, while the remaining terms are bounded uniformly by Cauchy--Schwarz because
the divisor is separated from `a`.  Letting `z` approach `a` inside the punctured neighbourhood of
regular points kills the fibre sum.

Consequently the closed Cauchy core is the whole divisor `ell^(2 : ℕ)` space if and only if every Xi zero
is simple, and otherwise its orthogonal complement is exactly the space of fibrewise mean-zero
vectors.
-/

open Complex Metric Set Filter Topology

namespace RHTower

noncomputable section

/-- The finite set of divisor-multiplicity copies above a single Xi zero. -/
def xiZeroCopyFiber (ρ : XiDivisorSupport) : Finset XiZeroCopy :=
  Finset.univ.map ⟨Sigma.mk ρ, sigma_mk_injective⟩

@[simp] theorem mem_xiZeroCopyFiber {ρ : XiDivisorSupport} {q : XiZeroCopy} :
    q ∈ xiZeroCopyFiber ρ ↔ q.1 = ρ := by
  constructor
  · intro hq
    simp only [xiZeroCopyFiber, Finset.mem_map, Finset.mem_univ, Function.Embedding.coeFn_mk,
      true_and] at hq
    obtain ⟨j, hj⟩ := hq
    exact hj ▸ rfl
  · intro hq
    subst hq
    simp only [xiZeroCopyFiber, Finset.mem_map, Finset.mem_univ, Function.Embedding.coeFn_mk,
      true_and]
    exact ⟨q.2, rfl⟩

/-- The sum of a divisor vector over the multiplicity copies above one Xi zero. -/
def xiWeilFiberSum (u : XiZeroCopy → ℂ) (ρ : XiDivisorSupport) : ℂ :=
  ∑ q ∈ xiZeroCopyFiber ρ, u q

/-- Square-summability of the coordinates of an `ell^(2 : ℕ)` vector. -/
theorem summable_sq_lp {ι : Type*} (u : lp (fun _ : ι => ℂ) 2) :
    Summable (fun q => ‖u q‖ ^ 2) := by
  have h := (memℓp_gen_iff (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)).mp (lp.memℓp u)
  refine h.congr ?_
  intro k
  rw [show ((2 : ENNReal).toReal) = (2 : ℕ) by norm_num, Real.rpow_natCast]

/-- Cauchy--Schwarz summability: the product of two square-summable families is absolutely
summable. -/
theorem summable_norm_mul_of_sq {ι : Type*} {a b : ι → ℂ}
    (ha : Summable (fun q => ‖a q‖ ^ 2)) (hb : Summable (fun q => ‖b q‖ ^ 2)) :
    Summable (fun q => ‖a q * b q‖) := by
  refine Summable.of_nonneg_of_le (fun q => norm_nonneg _) (fun q => ?_)
    (((ha.add hb).mul_left (1 / 2)))
  rw [norm_mul]
  nlinarith [sq_nonneg (‖a q‖ - ‖b q‖), norm_nonneg (a q), norm_nonneg (b q)]

/-- Conjugation preserves square-summability of the coordinates. -/
theorem summable_sq_conj_lp (u : lp (fun _ : XiZeroCopy => ℂ) 2) :
    Summable (fun q => ‖(starRingEnd ℂ) (u q)‖ ^ 2) := by
  simpa only [RCLike.norm_conj] using summable_sq_lp u

/-- Absolute summability of the resolvent pairing of an `ell^(2 : ℕ)` divisor vector with a Cauchy
kernel. -/
theorem summable_norm_conj_mul_cauchy (u : lp (fun _ : XiZeroCopy => ℂ) 2) (z : ℂ) :
    Summable (fun q : XiZeroCopy => ‖(starRingEnd ℂ) (u q) * (xiSpectralPoint q - z)⁻¹‖) :=
  summable_norm_mul_of_sq (summable_sq_conj_lp u) (XiWeilSquareSummable_cauchy z)

/-- The conjugated resolvent transform of a divisor vector orthogonal to every regular Cauchy
vector vanishes at every regular point. -/
theorem tsum_conj_mul_cauchy_eq_zero (u : lp (fun _ : XiZeroCopy => ℂ) 2)
    {N : Set ℂ} (h : ∀ z : XiCRegularPoint, (z : ℂ) ∈ N → inner ℂ (xiWeilCauchyLp z) u = 0)
    {z : ℂ} (hz : XiC z ≠ 0) (hzN : z ∈ N) :
    ∑' q : XiZeroCopy, (starRingEnd ℂ) (u q) * (xiSpectralPoint q - z)⁻¹ = 0 := by
  have hcalc : ∀ q : XiZeroCopy,
      (starRingEnd ℂ) (u q) * (xiSpectralPoint q - z)⁻¹ =
        star (inner ℂ (xiWeilCauchyLp ⟨z, hz⟩ q) (u q)) := by
    intro q
    simp only [xiWeilCauchyLp_apply, xiWeilCauchyTest, RCLike.inner_apply, star_mul',
      starRingEnd_apply, star_star]
  calc ∑' q : XiZeroCopy, (starRingEnd ℂ) (u q) * (xiSpectralPoint q - z)⁻¹
      = ∑' q : XiZeroCopy, star (inner ℂ (xiWeilCauchyLp ⟨z, hz⟩ q) (u q)) := tsum_congr hcalc
    _ = star (∑' q : XiZeroCopy, inner ℂ (xiWeilCauchyLp ⟨z, hz⟩ q) (u q)) := tsum_star.symm
    _ = star (inner ℂ (xiWeilCauchyLp ⟨z, hz⟩) u) := by rw [lp.inner_eq_tsum]
    _ = 0 := by rw [h ⟨z, hz⟩ hzN]; simp



/-- The Xi divisor is uniformly separated from any one of its points: the centered spectral
coordinates of all *other* divisor points stay a positive distance away.  Finitely many divisor
points meet any disc, so the minimum over those is positive and the rest are far by the triangle
inequality. -/
theorem exists_pos_le_norm_xiSpectralPoint_sub_support (ρ₀ : XiDivisorSupport) :
    ∃ d : ℝ, 0 < d ∧ ∀ q : XiZeroCopy, q.1 ≠ ρ₀ →
      d ≤ ‖xiSpectralPoint q - xiSpectralPointSupport ρ₀‖ := by
  classical
  set a : ℂ := xiSpectralPointSupport ρ₀ with ha
  set R : ℝ := ‖a‖ + 1 with hR
  have hfin : {τ : XiDivisorSupport | xiSpectralPointSupport τ ∈ Metric.closedBall 0 R}.Finite :=
    deningerXiSupport_closedBall_finite R
  set T : Finset XiDivisorSupport := hfin.toFinset.erase ρ₀ with hT
  have hfar : ∀ τ : XiDivisorSupport, τ ∉ hfin.toFinset → 1 ≤ ‖xiSpectralPointSupport τ - a‖ := by
    intro τ hτ
    have hnot : xiSpectralPointSupport τ ∉ Metric.closedBall (0 : ℂ) R := by
      intro hmem
      exact hτ (hfin.mem_toFinset.mpr hmem)
    rw [Metric.mem_closedBall, dist_zero_right, not_le] at hnot
    have := norm_sub_norm_le (xiSpectralPointSupport τ) a
    rw [hR] at hnot
    linarith
  have hpos : ∀ τ ∈ T, 0 < ‖xiSpectralPointSupport τ - a‖ := by
    intro τ hτ
    rw [norm_pos_iff, sub_ne_zero]
    intro h
    exact (Finset.mem_erase.mp hτ).1 (xiSpectralPointSupport_injective h)
  by_cases hne : T.Nonempty
  · refine ⟨min 1 (T.inf' hne (fun τ => ‖xiSpectralPointSupport τ - a‖)), ?_, ?_⟩
    · refine lt_min one_pos ?_
      rw [Finset.lt_inf'_iff]
      exact hpos
    · intro q hq
      rw [xiSpectralPoint_eq_support]
      by_cases hmem : q.1 ∈ hfin.toFinset
      · exact le_trans (min_le_right _ _)
          (Finset.inf'_le _ (Finset.mem_erase.mpr ⟨hq, hmem⟩))
      · exact le_trans (min_le_left _ _) (hfar q.1 hmem)
  · refine ⟨1, one_pos, ?_⟩
    intro q hq
    rw [xiSpectralPoint_eq_support]
    refine hfar q.1 (fun hmem => hne ⟨q.1, Finset.mem_erase.mpr ⟨hq, hmem⟩⟩)

/-- Every Xi zero has a punctured neighbourhood on which `XiC` does not vanish. -/
theorem eventually_XiC_ne_zero_punctured (a : ℂ) : ∀ᶠ w in nhdsWithin a {a}ᶜ, XiC w ≠ 0 := by
  have hnot : ¬ (∀ᶠ w in nhds a, XiC w = 0) := by
    intro hev
    have hall := XiC_analytic.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (Set.mem_univ a) hev (Set.mem_univ 0)
    exact XiC_zero_ne hall
  exact (XiC_analytic a (Set.mem_univ a)).eventually_eq_zero_or_eventually_ne_zero.resolve_left hnot

/-- **Multiplicity annihilation.**  A divisor vector orthogonal to every regular Cauchy evaluation
vector has vanishing sum over the multiplicity copies above each Xi zero.  The resolvent transform
of the vector vanishes at every regular point; multiplying by `a - z` isolates the fibre sum as the
residue at the zero `a`, while the remaining terms are bounded uniformly by Cauchy--Schwarz because
the divisor is separated from `a`. -/
theorem xiWeilFiberSum_eq_zero_of_inner_xiWeilCauchyLp_eq_zero_on_nodes
    (u : lp (fun _ : XiZeroCopy => ℂ) 2) {N : Set ℂ}
    (hN : ∀ ρ : XiDivisorSupport, ∀ᶠ z in nhdsWithin (xiSpectralPointSupport ρ) {xiSpectralPointSupport ρ}ᶜ, z ∈ N)
    (h : ∀ z : XiCRegularPoint, (z : ℂ) ∈ N → inner ℂ (xiWeilCauchyLp z) u = 0)
    (ρ₀ : XiDivisorSupport) : xiWeilFiberSum (fun q => u q) ρ₀ = 0 := by
  classical
  obtain ⟨d, hd, hsep⟩ := exists_pos_le_norm_xiSpectralPoint_sub_support ρ₀
  set a : ℂ := xiSpectralPointSupport ρ₀ with ha
  set S : ℂ := xiWeilFiberSum (fun q => u q) ρ₀ with hS
  set C : ℝ := 2 * ∑' q : XiZeroCopy, ‖(starRingEnd ℂ) (u q) * (xiSpectralPoint q - a)⁻¹‖ with hC
  have hCnn : 0 ≤ C := by
    have h0 : 0 ≤ ∑' q : XiZeroCopy, ‖(starRingEnd ℂ) (u q) * (xiSpectralPoint q - a)⁻¹‖ :=
      tsum_nonneg (fun q => norm_nonneg _)
    rw [hC]; linarith
  have hev : ∀ᶠ z in nhdsWithin a {a}ᶜ, ‖S‖ ≤ C * ‖a - z‖ := by
    have h1 : ∀ᶠ z in nhdsWithin a {a}ᶜ, XiC z ≠ 0 := eventually_XiC_ne_zero_punctured a
    have h2 : ∀ᶠ z in nhdsWithin a {a}ᶜ, ‖z - a‖ ≤ d / 2 := by
      refine Filter.Eventually.filter_mono nhdsWithin_le_nhds ?_
      filter_upwards [Metric.ball_mem_nhds a (half_pos hd)] with z hz
      rw [Metric.mem_ball, dist_eq_norm] at hz
      linarith
    have h3 : ∀ᶠ z in nhdsWithin a {a}ᶜ, z ≠ a := by
      filter_upwards [self_mem_nhdsWithin] with z hz using hz
    filter_upwards [h1, h2, h3, hN ρ₀] with z hz1 hz2 hz3 hz4
    set f : XiZeroCopy → ℂ :=
      fun q => (starRingEnd ℂ) (u q) * (xiSpectralPoint q - z)⁻¹ with hf
    have hsumz : Summable f := (summable_norm_conj_mul_cauchy u z).of_norm
    have hsplit := hsumz.sum_add_tsum_compl (s := xiZeroCopyFiber ρ₀)
    have htotal : ∑' q : XiZeroCopy, f q = 0 := tsum_conj_mul_cauchy_eq_zero u h hz1 hz4
    have hfiber : ∑ q ∈ xiZeroCopyFiber ρ₀, f q = (starRingEnd ℂ) S * (a - z)⁻¹ := by
      rw [hS, xiWeilFiberSum, map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun q hq => ?_)
      rw [hf]
      simp only [xiSpectralPoint_eq_support, mem_xiZeroCopyFiber.mp hq]
      rw [← ha]
    have hbound : ∀ q : XiZeroCopy, q.1 ≠ ρ₀ →
        ‖f q‖ ≤ 2 * ‖(starRingEnd ℂ) (u q) * (xiSpectralPoint q - a)⁻¹‖ := by
      intro q hq
      have hqa : d ≤ ‖xiSpectralPoint q - a‖ := hsep q hq
      have hza : ‖a - z‖ ≤ d / 2 := by rw [norm_sub_rev]; exact hz2
      have htri : ‖xiSpectralPoint q - a‖ - ‖a - z‖ ≤ ‖xiSpectralPoint q - z‖ := by
        have := norm_sub_norm_le (xiSpectralPoint q - a) (z - a)
        have hrw : xiSpectralPoint q - a - (z - a) = xiSpectralPoint q - z := by ring
        rw [hrw] at this
        have hzz : ‖z - a‖ = ‖a - z‖ := norm_sub_rev _ _
        linarith
      have hhalf : ‖xiSpectralPoint q - a‖ / 2 ≤ ‖xiSpectralPoint q - z‖ := by linarith
      have hpos : 0 < ‖xiSpectralPoint q - a‖ := lt_of_lt_of_le hd hqa
      have hinv : ‖xiSpectralPoint q - z‖⁻¹ ≤ 2 * ‖xiSpectralPoint q - a‖⁻¹ := by
        rw [show (2 : ℝ) * ‖xiSpectralPoint q - a‖⁻¹ = (‖xiSpectralPoint q - a‖ / 2)⁻¹ by
          field_simp]
        exact inv_anti₀ (by linarith) hhalf
      rw [hf]
      simp only [norm_mul, norm_inv]
      calc ‖(starRingEnd ℂ) (u q)‖ * ‖xiSpectralPoint q - z‖⁻¹
          ≤ ‖(starRingEnd ℂ) (u q)‖ * (2 * ‖xiSpectralPoint q - a‖⁻¹) :=
            mul_le_mul_of_nonneg_left hinv (norm_nonneg _)
        _ = 2 * (‖(starRingEnd ℂ) (u q)‖ * ‖xiSpectralPoint q - a‖⁻¹) := by ring
    have hsub : Summable
        (fun q : ↥((xiZeroCopyFiber ρ₀ : Set XiZeroCopy))ᶜ => ‖f q‖) :=
      (summable_norm_conj_mul_cauchy u z).subtype _
    have hsub2 : Summable
        (fun q : ↥((xiZeroCopyFiber ρ₀ : Set XiZeroCopy))ᶜ =>
          2 * ‖(starRingEnd ℂ) (u q) * (xiSpectralPoint q - a)⁻¹‖) :=
      ((summable_norm_conj_mul_cauchy u a).subtype _).mul_left 2
    have htail : ‖∑' q : ↥((xiZeroCopyFiber ρ₀ : Set XiZeroCopy))ᶜ, f q‖ ≤ C := by
      calc ‖∑' q : ↥((xiZeroCopyFiber ρ₀ : Set XiZeroCopy))ᶜ, f q‖
          ≤ ∑' q : ↥((xiZeroCopyFiber ρ₀ : Set XiZeroCopy))ᶜ, ‖f q‖ :=
            norm_tsum_le_tsum_norm hsub
        _ ≤ ∑' q : ↥((xiZeroCopyFiber ρ₀ : Set XiZeroCopy))ᶜ,
              2 * ‖(starRingEnd ℂ) (u q) * (xiSpectralPoint q - a)⁻¹‖ := by
            refine hsub.tsum_le_tsum (fun q => ?_) hsub2
            refine hbound q ?_
            intro hcon
            exact q.2 (by simpa only [Finset.mem_coe] using mem_xiZeroCopyFiber.mpr hcon)
        _ = 2 * ∑' q : ↥((xiZeroCopyFiber ρ₀ : Set XiZeroCopy))ᶜ,
              ‖(starRingEnd ℂ) (u q) * (xiSpectralPoint q - a)⁻¹‖ := tsum_mul_left
        _ ≤ C := by
            rw [hC]
            refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
            exact Summable.tsum_subtype_le _ _ (fun q => norm_nonneg _)
              (summable_norm_conj_mul_cauchy u a)
    have hkey : (starRingEnd ℂ) S * (a - z)⁻¹ =
        -(∑' q : ↥((xiZeroCopyFiber ρ₀ : Set XiZeroCopy))ᶜ, f q) := by
      have hzz := hsplit.trans htotal
      rw [hfiber] at hzz
      exact eq_neg_of_add_eq_zero_left hzz
    have hnorm : ‖S‖ * ‖a - z‖⁻¹ ≤ C := by
      have hb : ‖(starRingEnd ℂ) S * (a - z)⁻¹‖ ≤ C := by
        rw [hkey, norm_neg]; exact htail
      simpa only [norm_mul, RCLike.norm_conj, norm_inv] using hb
    have haz : 0 < ‖a - z‖ := by
      rw [norm_pos_iff, sub_ne_zero]
      exact fun hh => hz3 hh.symm
    rw [← div_eq_mul_inv, div_le_iff₀ haz] at hnorm
    linarith
  have hlim : Filter.Tendsto (fun z : ℂ => C * ‖a - z‖) (nhdsWithin a {a}ᶜ) (nhds 0) := by
    have hcont : Filter.Tendsto (fun z : ℂ => C * ‖a - z‖) (nhds a) (nhds (C * ‖a - a‖)) := by
      refine Filter.Tendsto.const_mul _ ?_
      exact (continuous_norm.comp (continuous_const.sub continuous_id)).tendsto a
    simpa using hcont.mono_left nhdsWithin_le_nhds
  have hle : ‖S‖ ≤ 0 := ge_of_tendsto hlim hev
  exact norm_le_zero_iff.mp hle


/-- The fibre sum written over the multiplicity index of the Xi divisor. -/
theorem xiWeilFiberSum_eq_sum_fin (u : XiZeroCopy → ℂ) (ρ : XiDivisorSupport) :
    xiWeilFiberSum u ρ =
      ∑ j : Fin (Int.toNat ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ))), u ⟨ρ, j⟩ := by
  simp [xiWeilFiberSum, xiZeroCopyFiber, Finset.sum_map]

/-- The fibre above a Xi zero has exactly as many elements as the divisor multiplicity. -/
theorem card_xiZeroCopyFiber (ρ : XiDivisorSupport) :
    (xiZeroCopyFiber ρ).card = Int.toNat ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ)) := by
  simp [xiZeroCopyFiber]

/-- The multiplicity annihilation law for the full family of regular Cauchy vectors. -/
theorem xiWeilFiberSum_eq_zero_of_inner_xiWeilCauchyLp_eq_zero
    (u : lp (fun _ : XiZeroCopy => ℂ) 2)
    (h : ∀ z : XiCRegularPoint, inner ℂ (xiWeilCauchyLp z) u = 0)
    (ρ₀ : XiDivisorSupport) : xiWeilFiberSum (fun q => u q) ρ₀ = 0 :=
  xiWeilFiberSum_eq_zero_of_inner_xiWeilCauchyLp_eq_zero_on_nodes u
    (N := Set.univ) (fun _ => Filter.Eventually.of_forall (fun _ => Set.mem_univ _))
    (fun z _ => h z) ρ₀

/-- Conversely, a divisor vector whose multiplicity fibre sums all vanish is orthogonal to every
regular Cauchy evaluation vector: the Cauchy kernel is constant along each fibre, so the sigma
decomposition of the pairing is a sum of vanishing fibre terms. -/
theorem inner_xiWeilEvaluationLp_eq_zero_of_xiWeilFiberSum_eq_zero
    (F : ℂ → ℂ) (hF : XiWeilSquareSummable F) (u : lp (fun _ : XiZeroCopy => ℂ) 2)
    (h : ∀ ρ : XiDivisorSupport, xiWeilFiberSum (fun q => u q) ρ = 0) :
    inner ℂ (xiWeilEvaluationLp F hF) u = 0 := by
  classical
  set g : XiZeroCopy → ℂ := fun q => inner ℂ (xiWeilEvaluationLp F hF q) (u q) with hg
  have hg' : ∀ q, g q = (starRingEnd ℂ) (F (xiSpectralPoint q)) * u q := by
    intro q
    simp [hg, RCLike.inner_apply, mul_comm]
  have hs1 : Summable (fun q : XiZeroCopy => ‖(starRingEnd ℂ) (F (xiSpectralPoint q))‖ ^ 2) := by
    simpa only [XiWeilSquareSummable, RCLike.norm_conj] using hF
  have hnorm : Summable
      (fun q : XiZeroCopy => ‖(starRingEnd ℂ) (F (xiSpectralPoint q)) * u q‖) :=
    summable_norm_mul_of_sq hs1 (summable_sq_lp u)
  have hsummable : Summable g := hnorm.of_norm.congr (fun q => (hg' q).symm)
  have hfib : ∀ ρ : XiDivisorSupport, HasSum (fun j => g ⟨ρ, j⟩) 0 := by
    intro ρ
    have hfin := hasSum_fintype (fun j => g ⟨ρ, j⟩)
    have hsum : ∑ j, g ⟨ρ, j⟩ =
        (starRingEnd ℂ) (F (xiSpectralPointSupport ρ)) *
          xiWeilFiberSum (fun q => u q) ρ := by
      rw [xiWeilFiberSum_eq_sum_fin, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [hg' ⟨ρ, j⟩]
      simp [xiSpectralPoint_eq_support]
    rw [hsum, h ρ, mul_zero] at hfin
    exact hfin
  have hzero := hsummable.hasSum.sigma hfib
  rw [lp.inner_eq_tsum]
  exact hzero.unique hasSum_zero

/-- The Cauchy case of the fibrewise orthogonality law. -/
theorem inner_xiWeilCauchyLp_eq_zero_of_xiWeilFiberSum_eq_zero
    (u : lp (fun _ : XiZeroCopy => ℂ) 2)
    (h : ∀ ρ : XiDivisorSupport, xiWeilFiberSum (fun q => u q) ρ = 0)
    (z : XiCRegularPoint) : inner ℂ (xiWeilCauchyLp z) u = 0 :=
  inner_xiWeilEvaluationLp_eq_zero_of_xiWeilFiberSum_eq_zero _
    (XiWeilSquareSummable_cauchy (z : ℂ)) u h

/-- **The Cauchy core annihilator.**  A divisor vector is orthogonal to the algebraic span of the
regular Cauchy evaluation vectors exactly when its sum over the multiplicity copies above every Xi
zero vanishes. -/
theorem inner_eq_zero_on_xiWeilCauchyAlgebraicSubspace_iff
    (u : lp (fun _ : XiZeroCopy => ℂ) 2) :
    (∀ x ∈ xiWeilCauchyAlgebraicSubspace, inner ℂ x u = 0) ↔
      ∀ ρ : XiDivisorSupport, xiWeilFiberSum (fun q => u q) ρ = 0 := by
  constructor
  · intro hx
    refine xiWeilFiberSum_eq_zero_of_inner_xiWeilCauchyLp_eq_zero u (fun z => ?_)
    exact hx _ (Submodule.subset_span ⟨z, rfl⟩)
  · intro hfib x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
        obtain ⟨z, hz⟩ := hy
        rw [← hz]
        exact inner_xiWeilCauchyLp_eq_zero_of_xiWeilFiberSum_eq_zero u hfib z
    | zero => simp
    | add y w hy hw ihy ihw => rw [inner_add_left, ihy, ihw, add_zero]
    | smul c y hy ih => rw [inner_smul_left, ih, mul_zero]

/-- The orthogonal complement of the algebraic Cauchy core is the space of fibrewise mean-zero
divisor vectors. -/
theorem mem_orthogonal_xiWeilCauchyAlgebraicSubspace_iff
    (u : lp (fun _ : XiZeroCopy => ℂ) 2) :
    u ∈ (xiWeilCauchyAlgebraicSubspace)ᗮ ↔
      ∀ ρ : XiDivisorSupport, xiWeilFiberSum (fun q => u q) ρ = 0 := by
  rw [Submodule.mem_orthogonal]
  exact inner_eq_zero_on_xiWeilCauchyAlgebraicSubspace_iff u

/-- **Exact density criterion for the Cauchy resolvent core.**  The closed span of the regular
Cauchy evaluation vectors is the whole divisor `ell^(2 : ℕ)` space exactly when every Xi zero is simple:
a zero of multiplicity two or more carries a difference of two copies which is annihilated by every
Cauchy kernel, and conversely a simple divisor makes the fibre sums the coordinates themselves. -/
theorem xiWeilCauchyHilbertSubspace_eq_top_iff :
    xiWeilCauchyHilbertSubspace = ⊤ ↔
      ∀ ρ : XiDivisorSupport, Int.toNat ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ)) = 1 := by
  classical
  have hclosure : xiWeilCauchyHilbertSubspace =
      (xiWeilCauchyAlgebraicSubspace).topologicalClosure := rfl
  rw [hclosure, Submodule.topologicalClosure_eq_top_iff]
  constructor
  · intro hbot ρ
    by_contra hne
    have hpos : 0 < (MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) := xi_divisor_pos_on_support ρ
    have h1 : 1 ≤ Int.toNat ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ)) := by omega
    have h2 : 2 ≤ Int.toNat ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ)) := by omega
    set i0 : XiZeroCopy := ⟨ρ, ⟨0, by omega⟩⟩ with hi0
    set i1 : XiZeroCopy := ⟨ρ, ⟨1, by omega⟩⟩ with hi1
    have hne01 : i0 ≠ i1 := by
      intro hcon
      have := congrArg (fun q : XiZeroCopy => (q.2 : ℕ)) hcon
      simp at this
    set u : lp (fun _ : XiZeroCopy => ℂ) 2 :=
      lp.single 2 i0 (1 : ℂ) - lp.single 2 i1 (1 : ℂ) with hu
    have hcoe : ∀ q : XiZeroCopy,
        (u : XiZeroCopy → ℂ) q =
          (Pi.single i0 (1 : ℂ) : XiZeroCopy → ℂ) q -
            (Pi.single i1 (1 : ℂ) : XiZeroCopy → ℂ) q := by
      intro q
      simp [hu]
    have hu0 : u ≠ 0 := by
      intro hcon
      have h0 : (u : XiZeroCopy → ℂ) i0 = 0 := by rw [hcon]; rfl
      rw [hcoe i0, Pi.single_eq_same] at h0
      rw [Pi.single_eq_of_ne hne01] at h0
      norm_num at h0
    have hmem : u ∈ (xiWeilCauchyAlgebraicSubspace)ᗮ := by
      rw [mem_orthogonal_xiWeilCauchyAlgebraicSubspace_iff]
      intro τ
      simp only [xiWeilFiberSum, hcoe, Finset.sum_sub_distrib, Pi.single_apply,
        Finset.sum_ite_eq' (xiZeroCopyFiber τ)]
      by_cases hτ : ρ = τ
      · simp [mem_xiZeroCopyFiber, hi0, hi1, hτ]
      · have h0 : i0 ∉ xiZeroCopyFiber τ := by simp [mem_xiZeroCopyFiber, hi0, hτ]
        have h1' : i1 ∉ xiZeroCopyFiber τ := by simp [mem_xiZeroCopyFiber, hi1, hτ]
        simp [h0, h1']
    rw [hbot, Submodule.mem_bot] at hmem
    exact hu0 hmem
  · intro hsimple
    rw [Submodule.eq_bot_iff]
    intro u hu
    have hfib := (mem_orthogonal_xiWeilCauchyAlgebraicSubspace_iff u).mp hu
    apply Subtype.ext
    funext q
    have hcard : (xiZeroCopyFiber q.1).card = 1 := by
      rw [card_xiZeroCopyFiber, hsimple]
    obtain ⟨b, hb⟩ := Finset.card_eq_one.mp hcard
    have hqmem : q ∈ xiZeroCopyFiber q.1 := mem_xiZeroCopyFiber.mpr rfl
    rw [hb, Finset.mem_singleton] at hqmem
    have hz := hfib q.1
    rw [xiWeilFiberSum, hb, Finset.sum_singleton, ← hqmem] at hz
    exact hz


/-- **Every evaluation vector lies in the closed Cauchy core.**  The evaluation of a test function
at the divisor is constant along each multiplicity fibre, and the closed Cauchy core is exactly the
orthogonal complement of the fibrewise mean-zero vectors.  So the resolvent core, although it is a
proper subspace whenever some Xi zero is multiple, always contains the entire range of the
evaluation map --- no square-summable test function is ever lost. -/
theorem xiWeilEvaluationLp_mem_xiWeilCauchyHilbertSubspace
    (F : ℂ → ℂ) (hF : XiWeilSquareSummable F) :
    xiWeilEvaluationLp F hF ∈ xiWeilCauchyHilbertSubspace := by
  have hclosure : xiWeilCauchyHilbertSubspace = (xiWeilCauchyAlgebraicSubspace)ᗮᗮ :=
    (Submodule.orthogonal_orthogonal_eq_closure _).symm
  rw [hclosure, Submodule.mem_orthogonal]
  intro u hu
  have hfib := (mem_orthogonal_xiWeilCauchyAlgebraicSubspace_iff u).mp hu
  have h0 := inner_xiWeilEvaluationLp_eq_zero_of_xiWeilFiberSum_eq_zero F hF u hfib
  rw [← inner_conj_symm, h0, map_zero]

/-- The closed Cauchy core and its algebraic span have the same annihilator, so the fibrewise
mean-zero description of the annihilator is unaffected by closing up. -/
theorem mem_orthogonal_xiWeilCauchyHilbertSubspace_iff
    (u : lp (fun _ : XiZeroCopy => ℂ) 2) :
    u ∈ (xiWeilCauchyHilbertSubspace)ᗮ ↔
      ∀ ρ : XiDivisorSupport, xiWeilFiberSum (fun q => u q) ρ = 0 := by
  rw [← mem_orthogonal_xiWeilCauchyAlgebraicSubspace_iff]
  constructor
  · intro hu
    exact fun x hx => hu x ((xiWeilCauchyAlgebraicSubspace).le_topologicalClosure hx)
  · intro hu x hx
    have hxc : x ∈ (xiWeilCauchyAlgebraicSubspace)ᗮᗮ := by
      rw [Submodule.orthogonal_orthogonal_eq_closure]
      exact hx
    have h0 := (Submodule.mem_orthogonal _ _).mp hxc u hu
    rw [← inner_conj_symm, h0, map_zero]

end

end RHTower
