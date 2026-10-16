import GaloisForLFunctions.RHTower.EvenSectorTwistedAbel
import GaloisForLFunctions.RHTower.EvenSectorPoleFreeTwoSidedGrowth
import GaloisForLFunctions.RHTower.EvenSectorPolarStripCeiling
import GaloisForLFunctions.HTGeometry.HolomorphicQuadraticBoundary

/-!
# Automatic completion of the even pole-free Weil cone

The arithmetic structure removes the missing pole direction. Detuned packets
give a ceiling uniform in every frequency twist. Holomorphy and a freely chosen
Harnack anchor eliminate the negative quadratic boundary defect. The existing
Abel correction then restores the pole term at its canonical weight, and the
even-to-full theorem restores every compact complex test.

The completion uses only membership in the original even pole-free cone. It adds
no coefficient sign, growth, convergence, lower-floor, Laurent, or Abel premise.
It does not assert that this cone is inhabited.
-/

open Complex Filter Topology Set
open scoped ComplexConjugate

noncomputable section
namespace RHTower.EvenSector
open OddSector WeilHerglotz GaloisForLFunctions.HTGeometry

/-- The actual arithmetic Dirichlet series, shifted so its convergence boundary is zero. -/
def polarDirichlet (lam : ℕ → ℝ) (z : ℂ) : ℂ := LSeries (lamC lam) (1 + z)

private theorem summable_lamC_of_polar {lam : ℕ → ℝ} (h : WeilPositiveEvenPolar lam)
    {z : ℂ} (hz : 1 < z.re) : LSeriesSummable (lamC lam) z := by
  apply summable_norm_iff.mp
  refine (summable_abs_div_rpow_of_weilPositiveEvenPolar h hz).of_nonneg_of_le
    (fun n => norm_nonneg _) fun n => ?_
  rw [LSeries.norm_term_eq]
  by_cases hn0 : n = 0
  · simp only [if_pos hn0]
    positivity
  rw [if_neg hn0, lamC, Complex.norm_real, Real.norm_eq_abs]
  split_ifs
  · exact le_rfl
  · simp only [abs_zero, zero_div]
    positivity

theorem differentiableOn_polarDirichlet {lam : ℕ → ℝ} (h : WeilPositiveEvenPolar lam) :
    DifferentiableOn ℂ (polarDirichlet lam) {z | 0 < z.re} := by
  have ha : LSeries.abscissaOfAbsConv (lamC lam) ≤ (1 : ℝ) :=
    LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy =>
      summable_lamC_of_polar h (by simpa using hy)
  intro z hz
  change 0 < z.re at hz
  have hr : (1 : ℝ) < (1 + z).re := by simp only [Complex.add_re, Complex.one_re]; linarith
  have ha' : LSeries.abscissaOfAbsConv (lamC lam) < (1 + z).re :=
    lt_of_le_of_lt ha (by exact_mod_cast hr)
  exact ((LSeries_hasDerivAt ha').differentiableAt.comp z
    (by fun_prop : DifferentiableAt ℂ (fun w : ℂ => 1 + w) z)).differentiableWithinAt

private theorem re_cpow_neg_one_add {x : ℝ} (hx : 0 < x) (z : ℂ) :
    ((x : ℂ) ^ (-(1 + z))).re =
      Real.cos (z.im * Real.log x) / x ^ (1 + z.re) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'),
    ← Complex.ofReal_log hx.le, Complex.exp_re]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.neg_re, Complex.neg_im, Complex.add_re, Complex.add_im,
    Complex.one_re, Complex.one_im, zero_mul, zero_add, sub_zero, add_zero,
    mul_neg, Real.cos_neg]
  rw [Real.exp_neg, Real.rpow_def_of_pos hx, mul_comm (Real.log x) z.im]
  ring

/-- The frequency-twisted real series is the real part of one holomorphic function. -/
theorem re_polarDirichlet {lam : ℕ → ℝ} (h : WeilPositiveEvenPolar lam)
    {z : ℂ} (hz : 0 < z.re) :
    (polarDirichlet lam z).re = oddDirichlet (evenTwist lam z.im) z.re := by
  unfold polarDirichlet LSeries oddDirichlet
  have hz1 : 1 < (1 + z).re := by
    simp only [Complex.add_re, Complex.one_re]
    linarith
  rw [Complex.re_tsum (summable_lamC_of_polar h hz1)]
  apply tsum_congr
  intro n
  by_cases hn : 2 ≤ n
  · have hn0 : n ≠ 0 := by omega
    have hnr : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    rw [LSeries.term_of_ne_zero hn0, lamC, if_pos hn, if_pos hn,
      div_eq_mul_inv, ← Complex.cpow_neg, Complex.re_ofReal_mul,
      ← Complex.ofReal_natCast n, re_cpow_neg_one_add hnr]
    dsimp [evenTwist]
    ring
  · simp [LSeries.term_def, lamC, hn]

theorem polarDirichlet_ofReal (lam : ℕ → ℝ) (s : ℝ) :
    polarDirichlet lam s = (oddDirichlet lam s : ℂ) :=
  LSeries_lamC_eq_oddDirichlet lam s

/-- The quadratic boundary defect vanishes on the original pole-free cone.
Absolute convergence and the all-frequency ceiling are produced internally. -/
theorem tendsto_sq_mul_oddDirichlet_zero_of_weilPositiveEvenPolar {lam : ℕ → ℝ}
    (h : WeilPositiveEvenPolar lam) :
    Tendsto (fun s : ℝ => s * (s * oddDirichlet lam s)) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M, hM, hceil⟩ := uniform_twisted_abel_ceiling h
  obtain ⟨r, hr, hinterval⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hceil
  have hF := tendsto_sq_mul_re_zero_of_uniform_ceiling
    ((differentiableOn_polarDirichlet h).mono fun _ hz => hz.1) hM hr
    (fun z hz hzr => by
      rw [re_polarDirichlet h hz]
      exact hinterval ⟨hz, hzr⟩ z.im)
  simpa only [polarDirichlet_ofReal, Complex.ofReal_re, pow_two, mul_assoc] using hF

/-- **Automatic pole completion.** The same arithmetic source is positive on
every even test at the actual pole weight. No extra analytic premise is needed. -/
theorem weilPositiveEvenAt_one_of_weilPositiveEvenPolar {lam : ℕ → ℝ}
    (h : WeilPositiveEvenPolar lam) : WeilPositiveEvenAt 1 lam := by
  have hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ :=
    fun _ hσ => summable_abs_div_rpow_of_weilPositiveEvenPolar h hσ
  obtain ⟨C, _, hg⟩ := exists_abs_le_of_weilPositiveEvenPolar h
  have hup := eventually_le_one_add_of_log_density_le hsl fun _ hε =>
    even_log_density_le_of_polar h hg hε
  have hdp : ∀ ε > 0, ∀ᶠ s : ℝ in 𝓝[>] 0, -ε ≤ s * (s * oddDirichlet lam s) := by
    intro ε hε
    exact (tendsto_sq_mul_oddDirichlet_zero_of_weilPositiveEvenPolar h).eventually
      (le_mem_nhds (by linarith : -ε < 0))
  exact weilPositiveEvenAt_one_of_real fun g hg hgc hge =>
    realWeil_nonneg_of_polar h hsl hup hdp hg hgc hge

/-- **Full test-cone completion.** An even pole-free source automatically acts
nonnegatively on every compact complex autocorrelation. -/
theorem weilPositiveFull_of_weilPositiveEvenPolar {lam : ℕ → ℝ}
    (h : WeilPositiveEvenPolar lam) : WeilPositiveFull lam :=
  weilPositiveFull_of_weilPositiveEvenAt (weilPositiveEvenAt_one_of_weilPositiveEvenPolar h)

/-- The pole-free cone has no noncanonical arithmetic source. -/
theorem source_unique_of_weilPositiveEvenPolar {lam : ℕ → ℝ}
    (h : WeilPositiveEvenPolar lam) :
    ∀ n, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n :=
  source_unique_of_weilPositiveEvenAt (weilPositiveEvenAt_one_of_weilPositiveEvenPolar h)

/-- Exact equality of the arithmetic source cones: restricting to even pole-free
tests creates no extra source. This does not assert nonemptiness. -/
theorem evenPolar_sourceCone_eq_full_sourceCone :
    {lam : ℕ → ℝ | WeilPositiveEvenPolar lam} = {lam : ℕ → ℝ | WeilPositiveFull lam} := by
  ext lam
  exact ⟨weilPositiveFull_of_weilPositiveEvenPolar, fun h =>
    weilPositiveEvenPolar_of_weilPositiveEvenAt (weilPositiveEvenAt_of_weilPositiveFull h)⟩

end RHTower.EvenSector
end
