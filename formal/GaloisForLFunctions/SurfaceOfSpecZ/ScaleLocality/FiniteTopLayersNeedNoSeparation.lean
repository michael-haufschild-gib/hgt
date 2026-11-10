import GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality.FiniteModeWindowLength
import GaloisForLFunctions.SurfaceOfSpecZ.BohrDenseSetsSampleEveryAttainedTop
import GaloisForLFunctions.VerifiedHeightRungs.TheZeroSideOfTheWindowRung
import GaloisForLFunctions.VerifiedHeightRungs.HadamardBudget.TheVerifiedHeightSixtySeven

/-!
# A finite top layer has a uniform window length

Conjugate pairing expresses the top trace using only its positive
ordinates. Half-period deletion then gives a window length depending
on their number and lowest ordinate. For zeta, the proved height 67
makes this length depend only on the number of top quartets.
-/

open Complex Filter Topology Set
open scoped ComplexConjugate
noncomputable section
namespace GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality
open SquareRootThreshold Zeta23 VerifiedHeightRungs

/-- The positive-ordinate half of the active top spectrum. -/
def positiveTopSupport (Z : ZeroConfig) (b : ℝ) : Set ℂ :=
  {z | z.re = b ∧ 0 < z.im ∧ evenCoeff Z (boxSpline 1 3) z ≠ 0}

/-- Conjugate pairing reduces a finite top layer to its positive frequencies. -/
theorem topTrace_eq_positive_sum {Z : ZeroConfig} {b : ℝ} (S : Finset ℂ)
    (hS : ∀ z, z ∈ S ↔ z ∈ positiveTopSupport Z b)
    (hreal : ∀ z, evenCoeff Z (boxSpline 1 3) z ≠ 0 → z.re = b → z.im ≠ 0)
    (u : ℝ) :
    topTrace Z b u =
      (∑ z ∈ S, (2 * evenCoeff Z (boxSpline 1 3) z) *
        Complex.exp (((z.im * u : ℝ) : ℂ) * I)).re := by
  classical
  have hc (z : ℂ) : topTerm Z b (conj z) u = conj (topTerm Z b z u) := by
    simp only [topTerm, Complex.conj_re]
    split_ifs
    · simp only [evenCoeff_conj, Complex.conj_im, map_mul, conj_bohrExp]
    · simp only [map_zero]
  have hd : Disjoint S (S.image conj) := by
    apply Finset.disjoint_left.mpr
    intro z hz hz'
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz'
    have hp := ((hS y).mp hy).2.1
    have hn := ((hS (conj y)).mp hz).2.1
    simp only [Complex.conj_im] at hn
    linarith only [hp, hn]
  have hsum : topTraceC Z b u = ∑ z ∈ S ∪ S.image conj, topTerm Z b z u := by
    apply tsum_eq_sum
    intro z hz
    by_cases hb : z.re = b
    · by_cases he : evenCoeff Z (boxSpline 1 3) z = 0
      · simp only [topTerm, if_pos hb, he, zero_mul]
      · exfalso
        rcases lt_or_gt_of_ne (hreal z he hb) with hn | hp
        · apply hz
          apply Finset.mem_union_right
          apply Finset.mem_image.mpr
          refine ⟨conj z, (hS _).mpr ?_, Complex.conj_conj z⟩
          refine ⟨by simpa only [Complex.conj_re] using hb,
            by simpa only [Complex.conj_im] using neg_pos.mpr hn, ?_⟩
          rw [evenCoeff_conj]
          intro hz
          apply he
          simpa only [Complex.conj_conj, map_zero] using congrArg conj hz
        · exact hz (Finset.mem_union_left _ ((hS z).mpr ⟨hb, hp, he⟩))
    · simp only [topTerm, if_neg hb]
  rw [topTrace_eq_re, hsum, Finset.sum_union hd,
    Finset.sum_image (fun _ _ _ _ h => star_injective h)]
  have he : (∑ z ∈ S, topTerm Z b (conj z) u) = conj (∑ z ∈ S, topTerm Z b z u) := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun z _ => hc z
  rw [he, Complex.add_re, Complex.conj_re]
  have hterm : (∑ z ∈ S, (2 * evenCoeff Z (boxSpline 1 3) z) *
      Complex.exp (((z.im * u : ℝ) : ℂ) * I)) = 2 * ∑ z ∈ S, topTerm Z b z u := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z hz
    rw [topTerm, if_pos (((hS z).mp hz).1), bohrExp_apply]
    ring
  rw [hterm]
  norm_num [Complex.mul_re] <;> ring

/-- Finite active top spectra have negative normalized traces in every sufficiently late window. -/
theorem finite_top_negative_in_every_window {Z : ZeroConfig} (hZ : TemperedConfig Z)
    {b Γ L : ℝ} (htop : TopDepth Z b) (hΓ : 0 < Γ) (S : Finset ℂ)
    (hS : ∀ z, z ∈ S ↔ z ∈ positiveTopSupport Z b) (hne : S.Nonempty)
    (hreal : ∀ z, evenCoeff Z (boxSpline 1 3) z ≠ 0 → z.re = b → z.im ≠ 0)
    (hγ : ∀ z ∈ S, Γ ≤ z.im) (hL : S.card * Real.pi < Γ * L) :
    ∃ ε U : ℝ, 0 < ε ∧ ∀ T : ℝ, U ≤ T → ∃ u ∈ Icc T (T + L),
      normTrace Z b u < -ε := by
  classical
  let e : Fin S.card ≃ S := S.equivFin.symm
  let a : Fin S.card → ℂ := fun j => 2 * evenCoeff Z (boxSpline 1 3) (e j)
  let γ : Fin S.card → ℝ := fun j => (e j : ℂ).im
  have hi : Function.Injective γ := by
    intro i j hij
    apply e.injective
    apply Subtype.ext
    apply Complex.ext
    · exact (((hS _).mp (e i).property).1).trans (((hS _).mp (e j).property).1).symm
    · exact hij
  have ha : ∃ j, a j ≠ 0 := by
    obtain ⟨z, hz⟩ := hne
    obtain ⟨j, hj⟩ := e.surjective ⟨z, hz⟩
    refine ⟨j, ?_⟩
    dsimp [a]
    rw [hj]
    exact mul_ne_zero (by norm_num) (((hS z).mp hz).2.2)
  have he (u : ℝ) :
      (∑ j, a j * Complex.exp (((γ j * u : ℝ) : ℂ) * I)).re = topTrace Z b u := by
    rw [topTrace_eq_positive_sum S hS hreal u]
    congr 1
    exact (e.sum_comp (fun z : S => (2 * evenCoeff Z (boxSpline 1 3) z) *
      Complex.exp ((((z : ℂ).im * u : ℝ) : ℂ) * I))).trans (Finset.sum_coe_sort S _)
  apply finite_spectrum_negative_windows_of_remainder a γ hΓ
    (fun j => hγ _ (e j).property) hi ha hL
  simpa only [he] using tendsto_normTrace_sub_topTrace hZ htop

/-- Every active positive-depth zeta frequency lies above the proved height 67. -/
theorem sixtySeven_lt_im_of_positive_zeta_mode {z : ℂ}
    (hz : evenCoeff zetaZeroConfig (boxSpline 1 3) z ≠ 0)
    (hre : 0 < z.re) (him : 0 < z.im) : 67 < z.im := by
  have hρ : (1 / 2 : ℂ) + z ∈ zetaZeroConfig.carrier := by
    rcases mem_of_evenCoeff_ne_zero hz with h | h
    · exact h
    · have hhalf : conj (1 / 2 : ℂ) = 1 / 2 := by norm_num
      simpa only [map_add, hhalf, Complex.conj_conj] using conj_mem_zetaZeroConfig h
  by_contra hn
  have him' : ((1 / 2 : ℂ) + z).im = z.im := by norm_num
  have he := re_eq_half_of_mem_carrier HadamardBudget.rhVerifiedThrough_sixtySeven hρ
    (by rw [him', abs_of_pos him]; exact le_of_not_gt hn)
  have hre' : ((1 / 2 : ℂ) + z).re = 1 / 2 + z.re := by norm_num
  rw [hre'] at he
  linarith only [hre, he]

/-- At most `k` top quartets are detected in length `(k+1)π/67`, independently of their spacing. -/
theorem zeta_finite_top_negative_windows {b : ℝ} (hb : 0 < b)
    (htop : TopDepth zetaZeroConfig b) (S : Finset ℂ)
    (hS : ∀ z, z ∈ S ↔ z ∈ positiveTopSupport zetaZeroConfig b)
    (hne : S.Nonempty) {k : ℕ} (hk : S.card ≤ k) :
    ∃ ε U : ℝ, 0 < ε ∧ ∀ T : ℝ, U ≤ T →
      ∃ u ∈ Icc T (T + ((k : ℝ) + 1) * Real.pi / 67),
        normTrace zetaZeroConfig b u < -ε := by
  apply finite_top_negative_in_every_window temperedConfig_zetaZeroConfig htop (Γ := 67)
    (by norm_num) S hS hne (fun z hz _ => evenCoeff_spline_real hz)
  · intro z hz
    obtain ⟨hre, him, he⟩ := (hS z).mp hz
    exact (sixtySeven_lt_im_of_positive_zeta_mode he (by rwa [hre]) him).le
  · have hcard : (S.card : ℝ) ≤ k := by exact_mod_cast hk
    have hπ := Real.pi_pos
    nlinarith only [mul_le_mul_of_nonneg_right hcard hπ.le, hπ]

/-- Every fixed floor fails on every sufficiently late window of this same length. -/
theorem zeta_finite_top_breaks_every_floor {b : ℝ} (hb : 0 < b)
    (htop : TopDepth zetaZeroConfig b) (S : Finset ℂ)
    (hS : ∀ z, z ∈ S ↔ z ∈ positiveTopSupport zetaZeroConfig b)
    (hne : S.Nonempty) {k : ℕ} (hk : S.card ≤ k) (K : ℝ) :
    ∃ U : ℝ, ∀ T : ℝ, U ≤ T →
      ∃ u ∈ Icc T (T + ((k : ℝ) + 1) * Real.pi / 67),
        2 * (lagStructure zetaZeroConfig (boxSpline 1 3) u).re < -K := by
  obtain ⟨ε, V, hε, hwin⟩ := zeta_finite_top_negative_windows hb htop S hS hne hk
  let M : ℝ := (|K| + 1) / ε
  have hM : 0 < M := div_pos (by positivity) hε
  refine ⟨max V (Real.log M / b), fun T hT => ?_⟩
  obtain ⟨u, hu, hneg⟩ := hwin T ((le_max_left _ _).trans hT)
  have hum : Real.log M / b ≤ u := ((le_max_right _ _).trans hT).trans hu.1
  have hexp : M ≤ Real.exp (b * u) := by
    rw [← Real.exp_log hM]
    apply Real.exp_le_exp.mpr
    have hh := (div_le_iff₀ hb).mp hum
    linarith only [hh]
  have hcost : |K| + 1 ≤ ε * Real.exp (b * u) := by
    have hh := mul_le_mul_of_nonneg_left hexp hε.le
    dsimp [M] at hh
    rw [← mul_div_assoc, mul_div_cancel_left₀ _ hε.ne'] at hh
    exact hh
  have hraw := mul_lt_mul_of_pos_right hneg (Real.exp_pos (b * u))
  rw [normTrace, mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one] at hraw
  refine ⟨u, hu, ?_⟩
  have hK := le_abs_self K
  nlinarith only [hraw, hcost, hK]

#print axioms zeta_finite_top_negative_windows
#print axioms zeta_finite_top_breaks_every_floor

end GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality
