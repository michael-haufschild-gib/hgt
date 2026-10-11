import GaloisForLFunctions.RHTower.XiSliceHeatLargeHeightPositivity
import GaloisForLFunctions.RHTower.XiSliceHeatNegativeFailure

/-!
# The WD heat threshold against the de Bruijn–Newman constant

**Propagation** (`exists_lt_mem_wdHeatAdmissible`).  If at some heat `μ > 0` every even heated slice
coefficient is strictly positive at every height, then some smaller heat is still admissible.
Large heights are handled by `exists_xiSliceHeatTransfer_nonneg_large_height` (at `μ/2`, then
monotonicity in `λ`), large orders at bounded heights by large-order positivity of `c_{2k}(t)`,
and the finitely many remaining orders on a compact height interval by joint continuity in
`(λ, t)` and the tube lemma.

**Consequences.**
* `wdHeatThreshold_lt_of_realRooted`: if `H_μ` has only real zeros (`μ > 0`), then `λ_WD < μ`.
  The heated slices at `μ` are Gaussian height averages of the slice moments of `H_μ`.  These are
  nonnegative by the cone criterion and not identically zero, so the averages are strictly positive.
* `wdHeatThreshold_lt_newmanConstant`: `λ_WD < Λ` whenever `Λ > 0`.
* `riemannHypothesis_iff_wdHeatThreshold_eq_newmanConstant`: **RH ⟺ λ_WD = Λ.**  Under RH both
  vanish; otherwise `0 < λ_WD < Λ`.
* `exists_xiSliceHeatTransfer_eq_zero_of_pos` (touching): if `λ_WD > 0`, then `λ_WD` is admissible
  and some even heated coefficient vanishes at some height at heat exactly `λ_WD`.

**Phase diagram.**  The admissible heats are exactly `[λ_WD, ∞)`.  For `λ > λ_WD` every even heated
coefficient is strictly positive at every height (`xiSliceHeatTransfer_pos_of_gt`).  At `λ = λ_WD`
some even coefficient vanishes, unconditionally (`exists_xiSliceHeatTransfer_eq_zero_at_threshold`).
The order of the touching decides RH: **RH ⟺ the heated value `T_0(λ_WD, 0, t)` vanishes at some
height** (`riemannHypothesis_iff_exists_xiSliceHeatTransfer_zero_order_eq_zero`).  At positive heat
`T_0` is a Gaussian average of `H_λ²` and is strictly positive.
-/

open Complex MeasureTheory Filter Topology Set
open scoped ComplexOrder

namespace RHTower.DeBruijn

noncomputable section

/-! ## Joint continuity in heat and height -/

theorem continuousOn_xiSliceHeatTransfer_Iic (x₀ : ℝ) (n : ℕ) {L : ℝ} (hL : 0 ≤ L) :
    ContinuousOn (fun p : ℝ × ℝ => xiSliceHeatTransfer p.1 x₀ p.2 n) (Set.Iic L ×ˢ Set.univ) := by
  set Φ := riemannKernelReal with hΦ
  have hΦ0 : ∀ u, 0 ≤ Φ u := riemannKernel_superExp.nonneg
  set F : ℝ × ℝ → ℝ × ℝ → ℂ := fun q p =>
    ((Φ p.1 * Φ p.2 * Real.exp (q.1 * (p.1 - p.2) ^ 2 / 2) * Real.exp (x₀ * (p.1 - p.2)) *
      ((p.1 - p.2) ^ n / n.factorial) : ℝ) : ℂ) * cexp (I * q.2 * (p.1 + p.2)) with hF
  set D : ℝ × ℝ → ℝ := fun p =>
    Φ p.1 * Real.exp (L * p.1 ^ 2) * Real.exp ((|x₀| + 1) * |p.1|) *
      (Φ p.2 * Real.exp (L * p.2 ^ 2) * Real.exp ((|x₀| + 1) * |p.2|)) with hD
  have hDi : Integrable D :=
    integrable_prod_majorant (riemannKernel_superExp.mul_exp_sq hL) (|x₀| + 1)
  have hbound : ∀ q ∈ Set.Iic L ×ˢ (Set.univ : Set ℝ), ∀ p : ℝ × ℝ, ‖F q p‖ ≤ D p := by
    intro q hq p
    have hqL : q.1 ≤ L := (Set.mem_prod.mp hq).1
    have hexp : Real.exp (q.1 * (p.1 - p.2) ^ 2 / 2) ≤
        Real.exp (L * p.1 ^ 2) * Real.exp (L * p.2 ^ 2) := by
      rw [← Real.exp_add]
      refine Real.exp_le_exp.mpr ?_
      have h1 : q.1 * (p.1 - p.2) ^ 2 ≤ L * (p.1 - p.2) ^ 2 :=
        mul_le_mul_of_nonneg_right hqL (sq_nonneg _)
      nlinarith [sq_nonneg (p.1 + p.2)]
    have h2 := abs_sub_pow_div_mul_exp_le x₀ p.1 p.2 n
    simp only [hF, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_cexp_I_mul_ofReal_add,
      mul_one, abs_div, abs_pow, Nat.abs_cast, abs_of_nonneg (hΦ0 _), abs_of_pos (Real.exp_pos _)]
    calc Φ p.1 * Φ p.2 * Real.exp (q.1 * (p.1 - p.2) ^ 2 / 2) * Real.exp (x₀ * (p.1 - p.2)) *
          (|p.1 - p.2| ^ n / n.factorial)
        = Φ p.1 * Φ p.2 * Real.exp (q.1 * (p.1 - p.2) ^ 2 / 2) *
          (|p.1 - p.2| ^ n / n.factorial * Real.exp (x₀ * (p.1 - p.2))) := by ring
      _ ≤ Φ p.1 * Φ p.2 * (Real.exp (L * p.1 ^ 2) * Real.exp (L * p.2 ^ 2)) *
            (Real.exp ((|x₀| + 1) * |p.1|) * Real.exp ((|x₀| + 1) * |p.2|)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hexp (mul_nonneg (hΦ0 _) (hΦ0 _))) h2
            (by positivity) (by have := hΦ0 p.1; have := hΦ0 p.2; positivity)
      _ = D p := by simp only [hD]; ring
  have hcont := continuous_riemannKernelReal
  unfold xiSliceHeatTransfer
  refine continuousOn_of_dominated (F := F) (bound := D)
    (fun q _ => (by simp only [hF, hΦ]; fun_prop : Continuous (F q)).aestronglyMeasurable)
    (fun q hq => Eventually.of_forall (hbound q hq)) hDi
    (Eventually.of_forall fun p => (by simp only [hF]; fun_prop : Continuous fun q => F q p).continuousOn)

/-- `(λ, t) ↦ T_n(λ, x₀, t)` is jointly continuous. -/
theorem continuous_xiSliceHeatTransfer_joint (x₀ : ℝ) (n : ℕ) :
    Continuous fun p : ℝ × ℝ => xiSliceHeatTransfer p.1 x₀ p.2 n := by
  refine continuous_iff_continuousAt.mpr fun q => ?_
  have h := continuousOn_xiSliceHeatTransfer_Iic x₀ n (L := |q.1| + 1) (by positivity)
  refine h.continuousAt (prod_mem_nhds (Iic_mem_nhds ?_) univ_mem)
  linarith [le_abs_self q.1]

/-- The heated slice is symmetric in the height. -/
theorem xiSliceHeatTransfer_neg_height {lam : ℝ} (hlam : 0 < lam) (t : ℝ) (l : ℕ) :
    xiSliceHeatTransfer lam 0 (-t) (2 * l) = xiSliceHeatTransfer lam 0 t (2 * l) :=
  Complex.ext (re_xiSliceHeatTransfer_neg hlam t l)
    (by rw [xiSliceHeatTransfer_im_eq_zero hlam.le, xiSliceHeatTransfer_im_eq_zero hlam.le])

/-- A real number in `ℂ` with positive real part is positive. -/
theorem xiSliceHeatTransfer_nonneg_of_re_pos {lam t : ℝ} (hlam : 0 ≤ lam) {n : ℕ}
    (h : 0 < (xiSliceHeatTransfer lam 0 t n).re) : 0 ≤ xiSliceHeatTransfer lam 0 t n :=
  Complex.nonneg_iff.mpr ⟨h.le, (xiSliceHeatTransfer_im_eq_zero hlam t n).symm⟩

/-! ## Propagation below a strictly positive heat -/

/-- `t log t ≤ T log T` for `0 ≤ t ≤ T`, `1 ≤ T`. -/
theorem mul_log_le_mul_log {t T : ℝ} (ht : 0 ≤ t) (hT : 1 ≤ T) (htT : t ≤ T) :
    t * Real.log t ≤ T * Real.log T := by
  have hTl : 0 ≤ T * Real.log T := mul_nonneg (by linarith) (Real.log_nonneg hT)
  rcases le_total t 1 with h | h
  · have : t * Real.log t ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos ht (Real.log_nonpos ht h)
    linarith
  · exact mul_le_mul htT (Real.log_le_log (by linarith) htT) (Real.log_nonneg h) (by linarith)

/-- Large orders are positive at bounded heights for every heat `λ ≥ 0`. -/
theorem exists_xiSliceHeatTransfer_nonneg_large_order (T : ℝ) :
    ∃ k₀ : ℕ, ∀ t : ℝ, 0 ≤ t → t ≤ T → ∀ lam : ℝ, 0 ≤ lam → ∀ l : ℕ, k₀ ≤ l →
      0 ≤ xiSliceHeatTransfer lam 0 t (2 * l) := by
  obtain ⟨K₀, hK₀⟩ := exists_xiSliceCoeff_pos_large_order
  set T' := max T 1 with hT'
  refine ⟨⌈max K₀ (T' * Real.log T' / 8)⌉₊, fun t ht0 htT lam hlam l hl => ?_⟩
  have hT1 : 1 ≤ T' := le_max_right _ _
  have hcoef : ∀ k : ℕ, l ≤ k → 0 < xiSliceCoeff t (2 * k) := by
    intro k hk
    have hk' : max K₀ (T' * Real.log T' / 8) ≤ k :=
      (Nat.le_ceil _).trans (by exact_mod_cast hl.trans hk)
    refine hK₀ t ht0 k ((le_max_left _ _).trans hk') ?_
    have := mul_log_le_mul_log ht0 hT1 (htT.trans (le_max_left _ _))
    linarith [le_max_right K₀ (T' * Real.log T' / 8)]
  have hT := hasSum_xiSliceHeatTransfer_kernelSliceMoment hlam 0 t (2 * l)
  simp only [kernelSliceMoment_riemannKernel_eq_xiSliceCoeff] at hT
  refine hT.nonneg fun k => mul_nonneg (Complex.zero_le_real.mpr (by positivity)) ?_
  rw [show 2 * l + 2 * k = 2 * (l + k) by ring]
  exact (hcoef (l + k) (by omega)).le

/-- **Propagation.**  If at heat `μ > 0` all even heated coefficients are strictly positive at every
height `t ≥ 0`, some heat `λ < μ` is admissible. -/
theorem exists_lt_mem_wdHeatAdmissible {μ : ℝ} (hμ : 0 < μ)
    (hpos : ∀ t : ℝ, 0 ≤ t → ∀ l : ℕ, 0 < (xiSliceHeatTransfer μ 0 t (2 * l)).re) :
    ∃ lam < μ, lam ∈ wdHeatAdmissible := by
  obtain ⟨T, hT⟩ := exists_xiSliceHeatTransfer_nonneg_large_height (lam := μ / 2) (by positivity)
  set T' := max T 0 with hT'
  obtain ⟨k₀, hk₀⟩ := exists_xiSliceHeatTransfer_nonneg_large_order T'
  -- the tube lemma on `[0, T']` for the orders below `k₀`
  have hcpt : IsCompact (Set.Icc (0 : ℝ) T') := isCompact_Icc
  have htube : ∀ l ∈ Finset.range k₀, ∀ᶠ lam in 𝓝 μ, ∀ t ∈ Set.Icc (0 : ℝ) T',
      0 < (xiSliceHeatTransfer lam 0 t (2 * l)).re := by
    intro l _
    refine hcpt.eventually_forall_of_forall_eventually fun t ht => ?_
    have hc : ContinuousAt (fun z : ℝ × ℝ => (xiSliceHeatTransfer z.1 0 z.2 (2 * l)).re) (μ, t) :=
      (Complex.continuous_re.comp (continuous_xiSliceHeatTransfer_joint 0 (2 * l))).continuousAt
    exact hc.eventually (lt_mem_nhds (hpos t ht.1 l))
  have hall := (Filter.eventually_all_finset _).mpr htube
  have hhalf : ∀ᶠ lam in 𝓝 μ, μ / 2 < lam := lt_mem_nhds (by linarith)
  obtain ⟨lam, ⟨hlow, hlam2⟩, hlamμ⟩ :=
    (((hall.and hhalf).filter_mono nhdsWithin_le_nhds).and
      (self_mem_nhdsWithin : Set.Iio μ ∈ 𝓝[<] μ)).exists
  have hlam0 : 0 < lam := by linarith
  refine ⟨lam, hlamμ, fun t n => ?_⟩
  obtain ⟨l, rfl | rfl⟩ := Nat.even_or_odd' n
  swap
  · rw [xiSliceHeatTransfer_odd_eq_zero hlam0.le]
  -- reduce to `t ≥ 0`
  suffices key : ∀ s : ℝ, 0 ≤ s → 0 ≤ xiSliceHeatTransfer lam 0 s (2 * l) by
    rcases le_total 0 t with h | h
    · exact key t h
    · rw [← neg_neg t, xiSliceHeatTransfer_neg_height hlam0]; exact key (-t) (by linarith)
  intro s hs
  by_cases hsT : T ≤ s
  · exact xiSliceHeatTransfer_nonneg_of_le_of_forall hlam2.le
      (hT s (by rwa [abs_of_nonneg hs])) _
  · have hsT' : s ≤ T' := le_trans (le_of_lt (not_le.mp hsT)) (le_max_left _ _)
    by_cases hl : k₀ ≤ l
    · exact hk₀ s hs hsT' lam hlam0.le l hl
    · exact xiSliceHeatTransfer_nonneg_of_re_pos hlam0.le
        (hlow l (Finset.mem_range.mpr (not_le.mp hl)) s ⟨hs, hsT'⟩)

/-! ## Strict positivity at real-rooted heats -/

/-- `∫ G f > 0` for `G > 0` integrable and `f ≥ 0` continuous, bounded and positive somewhere. -/
theorem integral_mul_pos_of_pos {G f : ℝ → ℝ} (hG : Integrable G) (hG0 : ∀ x, 0 < G x) (hf : Continuous f) {B : ℝ} (hfB : ∀ x, |f x| ≤ B) (hf0 : ∀ x, 0 ≤ f x)
    {t₀ : ℝ} (ht₀ : 0 < f t₀) : 0 < ∫ x, G x * f x := by
  have hint : Integrable (fun x => G x * f x) :=
    hG.mul_bdd hf.aestronglyMeasurable (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact hfB x)
  refine (integral_pos_iff_support_of_nonneg (fun x => mul_nonneg (hG0 x).le (hf0 x)) hint).mpr ?_
  have hopen : IsOpen (f ⁻¹' Set.Ioi 0) := isOpen_Ioi.preimage hf
  have hsub : f ⁻¹' Set.Ioi 0 ⊆ Function.support (fun x => G x * f x) := fun x hx =>
    mul_ne_zero (hG0 x).ne' (ne_of_gt hx)
  exact lt_of_lt_of_le (hopen.measure_pos volume ⟨t₀, ht₀⟩) (measure_mono hsub)

/-- If the `2l`-th slice moments of `H_μ` (`μ > 0`) are nonnegative at every height, the heated
coefficient `T_{2l}(μ, 0, t)` has strictly positive real part at every height: it is a Gaussian
height average of a nonnegative function that is not identically zero. -/
theorem re_xiSliceHeatTransfer_pos_of_moments_nonneg {μ : ℝ} (hμ : 0 < μ) (l : ℕ)
    (hM : ∀ t' : ℝ, 0 ≤ kernelSliceMoment (heatKernel μ) 0 t' (2 * l)) (t : ℝ) :
    0 < (xiSliceHeatTransfer μ 0 t (2 * l)).re := by
  have hσ : 0 < Real.sqrt (1 / (2 * μ)) := Real.sqrt_pos.mpr (by positivity)
  obtain ⟨t₀, -, hne⟩ := exists_mem_Ioo_kernelSliceMoment_ne_zero hμ.le l
    (show (0 : ℝ) < 1 by norm_num)
  have hre : 0 < (kernelSliceMoment (heatKernel μ) 0 t₀ (2 * l)).re := by
    obtain ⟨hre0, him⟩ := Complex.nonneg_iff.mp (hM t₀)
    refine lt_of_le_of_ne hre0 fun h => hne ?_
    exact Complex.ext (by simpa using h.symm) (by simpa using him.symm)
  rw [re_xiSliceHeatTransfer_eq hμ]
  exact integral_mul_pos_of_pos (integrable_heightGaussian hσ t)
    (fun x => by unfold heightGaussian; positivity)
    (Complex.continuous_re.comp (continuous_kernelSliceMoment_heatKernel hμ.le l))
    (fun x => (Complex.abs_re_le_norm _).trans (norm_kernelSliceMoment_heatKernel_le x l))
    (fun x => (Complex.nonneg_iff.mp (hM x)).1) hre

/-- **Strict positivity at real-rooted heats.**  If `H_μ` (`μ > 0`) has only real zeros, every even
heated slice coefficient at heat `μ` is strictly positive at every height. -/
theorem re_xiSliceHeatTransfer_pos_of_realRooted {μ : ℝ} (hμ : 0 < μ)
    (hreal : ∀ z, riemannHeat μ z = 0 → z.im = 0) (t : ℝ) (l : ℕ) :
    0 < (xiSliceHeatTransfer μ 0 t (2 * l)).re := by
  refine re_xiSliceHeatTransfer_pos_of_moments_nonneg hμ l (fun t' => ?_) t
  have hNT := nonnegTaylorAtZero_riemannHeat_slice_of_cone (t := t') hμ.le fun ζ hζ => by
    rw [hreal ζ hζ]; nlinarith [sq_nonneg (ζ.re - t')]
  have e := kernelSliceMoment_heat_eq hμ.le 0 t' (2 * l)
  have hk : (fun u => riemannKernelReal u * Real.exp (μ * u ^ 2)) = heatKernel μ := rfl
  rw [hk] at e
  rw [e, Complex.ofReal_zero, div_eq_mul_inv,
    show (((2 * l).factorial : ℂ))⁻¹ = ((((2 * l).factorial : ℝ))⁻¹ : ℝ) by push_cast; rfl]
  exact mul_nonneg (hNT.2 _) (Complex.zero_le_real.mpr (by positivity))

/-- **`λ_WD < μ` at every real-rooted heat `μ > 0`.** -/
theorem wdHeatThreshold_lt_of_realRooted {μ : ℝ} (hμ : 0 < μ)
    (hreal : ∀ z, riemannHeat μ z = 0 → z.im = 0) : wdHeatThreshold < μ := by
  obtain ⟨lam, hlam, hmem⟩ := exists_lt_mem_wdHeatAdmissible hμ
    fun t _ l => re_xiSliceHeatTransfer_pos_of_realRooted hμ hreal t l
  exact lt_of_le_of_lt (csInf_le wdHeatAdmissible_bddBelow hmem) hlam

/-- **`λ_WD < Λ` whenever `Λ > 0`.** -/
theorem wdHeatThreshold_lt_newmanConstant (hΛ : 0 < newmanConstant) :
    wdHeatThreshold < newmanConstant := by
  have hmem := (mem_realRootedTimes_iff newmanConstant_nonneg).mpr le_rfl
  exact wdHeatThreshold_lt_of_realRooted hΛ hmem.2

/-- **RH ⟺ λ_WD = Λ.**  Under RH both thresholds vanish; otherwise `0 < λ_WD < Λ`. -/
theorem riemannHypothesis_iff_wdHeatThreshold_eq_newmanConstant :
    RiemannHypothesis ↔ wdHeatThreshold = newmanConstant := by
  constructor
  · intro hRH
    rw [riemannHypothesis_iff_wdHeatThreshold_eq_zero.mp hRH,
      riemannHypothesis_iff_newmanConstant_eq_zero.mp hRH]
  · intro h
    by_contra hRH
    have hΛ : 0 < newmanConstant := lt_of_le_of_ne newmanConstant_nonneg
      (fun h0 => hRH (riemannHypothesis_iff_newmanConstant_eq_zero.mpr h0.symm))
    exact (wdHeatThreshold_lt_newmanConstant hΛ).ne h

/-! ## Touching at the threshold -/

/-- The threshold itself is admissible. -/
theorem wdHeatThreshold_mem_wdHeatAdmissible : wdHeatThreshold ∈ wdHeatAdmissible := by
  intro t n
  have hc : Tendsto (fun lam => xiSliceHeatTransfer lam 0 t n) (𝓝[>] wdHeatThreshold)
      (𝓝 (xiSliceHeatTransfer wdHeatThreshold 0 t n)) := by
    have h := (continuous_xiSliceHeatTransfer_joint 0 n).comp
      (Continuous.prodMk continuous_id continuous_const : Continuous fun lam : ℝ => (lam, t))
    exact (h.tendsto wdHeatThreshold).mono_left nhdsWithin_le_nhds
  exact ge_of_tendsto hc (eventually_nhdsWithin_of_forall fun lam hlam =>
    mem_wdHeatAdmissible_of_lt hlam t n)

/-- **Touching.**  If `λ_WD > 0`, then at heat exactly `λ_WD` some even heated slice coefficient
vanishes at some height. -/
theorem exists_xiSliceHeatTransfer_eq_zero_of_pos (h : 0 < wdHeatThreshold) :
    ∃ t : ℝ, 0 ≤ t ∧ ∃ l : ℕ, xiSliceHeatTransfer wdHeatThreshold 0 t (2 * l) = 0 := by
  by_contra hcon
  push Not at hcon
  have hpos : ∀ t : ℝ, 0 ≤ t → ∀ l : ℕ, 0 < (xiSliceHeatTransfer wdHeatThreshold 0 t (2 * l)).re := by
    intro t ht l
    obtain ⟨hre, him⟩ := Complex.nonneg_iff.mp (wdHeatThreshold_mem_wdHeatAdmissible t (2 * l))
    refine lt_of_le_of_ne hre fun h0 => hcon t ht l ?_
    exact Complex.ext (by simpa using h0.symm) (by simpa using him.symm)
  obtain ⟨lam, hlam, hmem⟩ := exists_lt_mem_wdHeatAdmissible h hpos
  exact absurd (csInf_le wdHeatAdmissible_bddBelow hmem) (not_le.mpr hlam)

/-! ## The phase diagram of the heat threshold -/

/-- At every height, the even heated coefficients of high order are strictly positive for every heat
`λ ≥ 0`. -/
theorem exists_xiSliceHeatTransfer_pos_high_order (t : ℝ) (ht : 0 ≤ t) :
    ∃ m₀ : ℕ, ∀ lam : ℝ, 0 ≤ lam → ∀ m : ℕ, m₀ ≤ m → 0 < xiSliceHeatTransfer lam 0 t (2 * m) := by
  obtain ⟨K₀, hK₀⟩ := exists_xiSliceCoeff_pos_large_order
  refine ⟨⌈max K₀ (t * Real.log t / 8)⌉₊, fun lam hlam m hm => ?_⟩
  have hcoef : ∀ k : ℕ, m ≤ k → 0 < xiSliceCoeff t (2 * k) := by
    intro k hk
    have hk' : max K₀ (t * Real.log t / 8) ≤ k :=
      (Nat.le_ceil _).trans (by exact_mod_cast hm.trans hk)
    exact hK₀ t ht k ((le_max_left _ _).trans hk') ((le_max_right _ _).trans hk')
  have hT := hasSum_xiSliceHeatTransfer_kernelSliceMoment hlam 0 t (2 * m)
  simp only [kernelSliceMoment_riemannKernel_eq_xiSliceCoeff] at hT
  have hterm : ∀ k : ℕ, 0 ≤ ((((lam / 2) ^ k / k.factorial *
      ((2 * m + 2 * k).factorial / (2 * m).factorial) : ℝ) : ℂ) * xiSliceCoeff t (2 * m + 2 * k)) := by
    intro k
    refine mul_nonneg (Complex.zero_le_real.mpr (by positivity)) ?_
    rw [show 2 * m + 2 * k = 2 * (m + k) by ring]
    exact (hcoef (m + k) (by omega)).le
  have h0 := le_hasSum hT 0 fun j _ => hterm j
  have hfac : ((2 * m).factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, mul_zero, add_zero, div_self hfac,
    one_mul, Complex.ofReal_one] at h0
  exact lt_of_lt_of_le (hcoef m le_rfl) h0

/-- **Strict positivity above the threshold.**  For `λ > λ_WD` every even heated slice coefficient is
strictly positive at every height. -/
theorem xiSliceHeatTransfer_pos_of_gt {lam : ℝ} (hlam : wdHeatThreshold < lam) (t : ℝ) (l : ℕ) :
    0 < xiSliceHeatTransfer lam 0 t (2 * l) := by
  have hW0 := wdHeatThreshold_nonneg
  have hlam0 : 0 < lam := lt_of_le_of_lt hW0 hlam
  suffices key : ∀ s : ℝ, 0 ≤ s → 0 < xiSliceHeatTransfer lam 0 s (2 * l) by
    rcases le_total 0 t with h | h
    · exact key t h
    · rw [← neg_neg t, xiSliceHeatTransfer_neg_height hlam0]; exact key (-t) (by linarith)
  intro s hs
  obtain ⟨m₀, hm₀⟩ := exists_xiSliceHeatTransfer_pos_high_order s hs
  have hshift := hasSum_xiSliceHeatTransfer_shift hlam.le 0 s (2 * l)
  have hadm := wdHeatThreshold_mem_wdHeatAdmissible
  have hd : 0 < (lam - wdHeatThreshold) / 2 := by linarith
  have hterm : ∀ k : ℕ, 0 ≤ (((((lam - wdHeatThreshold) / 2) ^ k / k.factorial *
      ((2 * l + 2 * k).factorial / (2 * l).factorial) : ℝ) : ℂ) *
        xiSliceHeatTransfer wdHeatThreshold 0 s (2 * l + 2 * k)) := fun k =>
    mul_nonneg (Complex.zero_le_real.mpr (by positivity)) (hadm s _)
  have hk := le_hasSum hshift m₀ fun j _ => hterm j
  have hpos : 0 < (((((lam - wdHeatThreshold) / 2) ^ m₀ / m₀.factorial *
      ((2 * l + 2 * m₀).factorial / (2 * l).factorial) : ℝ) : ℂ) *
        xiSliceHeatTransfer wdHeatThreshold 0 s (2 * l + 2 * m₀)) := by
    refine mul_pos (Complex.zero_lt_real.mpr (by positivity)) ?_
    rw [show 2 * l + 2 * m₀ = 2 * (l + m₀) by ring]
    exact hm₀ _ hW0 _ (by omega)
  exact lt_of_lt_of_le hpos hk

/-- **Touching at the threshold, unconditionally.**  At heat exactly `λ_WD` some even heated slice
coefficient vanishes at some height: at a real zero of `Ξ` (order `0`) when `λ_WD = 0`, by
`exists_xiSliceHeatTransfer_eq_zero_of_pos` otherwise. -/
theorem exists_xiSliceHeatTransfer_eq_zero_at_threshold :
    ∃ t : ℝ, 0 ≤ t ∧ ∃ l : ℕ, xiSliceHeatTransfer wdHeatThreshold 0 t (2 * l) = 0 := by
  rcases eq_or_lt_of_le wdHeatThreshold_nonneg with h | h
  · obtain ⟨a, -, ha0, -, -, ha, -⟩ := exists_two_distinct_positive_real_XiC_zeros
    refine ⟨a, ha0.le, 0, ?_⟩
    rw [← h, xiSliceHeatTransfer_zero_eq]
    unfold xiSliceCoeff
    simp only [mul_zero, iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one, inv_one, one_mul]
    rw [xiSliceProduct_eq_XiC, mul_zero, sub_zero, add_zero, ha, zero_mul]
  · exact exists_xiSliceHeatTransfer_eq_zero_of_pos h

/-- At positive heat the heated value `T_0(λ, 0, t)` (a Gaussian height average of `H_λ²`) is
strictly positive. -/
theorem xiSliceHeatTransfer_zero_order_pos {lam : ℝ} (hlam : 0 < lam) (t : ℝ) :
    0 < xiSliceHeatTransfer lam 0 t 0 := by
  have hM : ∀ t' : ℝ, 0 ≤ kernelSliceMoment (heatKernel lam) 0 t' (2 * 0) := by
    intro t'
    have e := kernelSliceMoment_heat_eq hlam.le 0 t' 0
    have hk : (fun u => riemannKernelReal u * Real.exp (lam * u ^ 2)) = heatKernel lam := rfl
    rw [hk] at e
    rw [show 2 * 0 = 0 by rfl, e]
    simp only [iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one, div_one, Complex.ofReal_zero,
      mul_zero, sub_zero, add_zero]
    have hreal : riemannHeat lam (t' : ℂ) = ((riemannHeat lam (t' : ℂ)).re : ℂ) := by
      have h := riemannHeat_conj hlam.le (t' : ℂ)
      rw [Complex.conj_ofReal] at h
      refine Complex.ext rfl ?_
      have := congrArg Complex.im h
      simp only [Complex.conj_im] at this
      simp only [Complex.ofReal_im]
      linarith
    rw [hreal, ← Complex.ofReal_mul]
    exact Complex.zero_le_real.mpr (mul_self_nonneg _)
  have hre := re_xiSliceHeatTransfer_pos_of_moments_nonneg hlam 0 hM t
  have him := xiSliceHeatTransfer_im_eq_zero hlam.le t (2 * 0)
  simp only [mul_zero] at hre him
  have e : xiSliceHeatTransfer lam 0 t 0 = ((xiSliceHeatTransfer lam 0 t 0).re : ℂ) :=
    Complex.ext rfl (by simp [him])
  rw [e]
  exact Complex.zero_lt_real.mpr hre

/-- **RH ⟺ the threshold touches in the value.**  The Riemann hypothesis holds if and only if, at
heat `λ_WD`, the heated value `T_0(λ_WD, 0, t)` vanishes at some height.  Under RH this happens at
every real zero of `Ξ`; otherwise `λ_WD > 0`, `T_0(λ_WD, 0, ·) > 0`, and the touching of
`exists_xiSliceHeatTransfer_eq_zero_of_pos` happens at an order `≥ 2`. -/
theorem riemannHypothesis_iff_exists_xiSliceHeatTransfer_zero_order_eq_zero :
    RiemannHypothesis ↔ ∃ t : ℝ, xiSliceHeatTransfer wdHeatThreshold 0 t 0 = 0 := by
  constructor
  · intro hRH
    obtain ⟨a, -, -, -, -, ha, -⟩ := exists_two_distinct_positive_real_XiC_zeros
    refine ⟨a, ?_⟩
    rw [riemannHypothesis_iff_wdHeatThreshold_eq_zero.mp hRH, xiSliceHeatTransfer_zero_eq]
    unfold xiSliceCoeff
    simp only [iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one, inv_one, one_mul]
    rw [xiSliceProduct_eq_XiC, mul_zero, sub_zero, add_zero, ha, zero_mul]
  · rintro ⟨t, ht⟩
    by_contra hRH
    have hpos : 0 < wdHeatThreshold := lt_of_le_of_ne wdHeatThreshold_nonneg
      (fun h0 => hRH (riemannHypothesis_iff_wdHeatThreshold_eq_zero.mpr h0.symm))
    exact (xiSliceHeatTransfer_zero_order_pos hpos t).ne' ht

end

end RHTower.DeBruijn
