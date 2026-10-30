import GaloisForLFunctions.ArithmeticIndexDescent.TheSharpEulerHeadCouplesDetailsToFarWindows
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.DisjointStepsHaveLogarithmicGammaCost
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheArchimedeanPairingOfTwoAtoms

/-!
# The index of a growing Euler head is unbounded

For a fixed finite prime set, Gamma minus the complete mixed Euler source has a negative index
bounded uniformly in the horizon (`exists_uniform_finiteEulerGamma_negative_dimension`). This bound
cannot be made uniform over the heads `p ≤ Y`:

* (`eventually_eulerHead_negative_family`) for every `K`, once `Y` is large, every horizon
  `X ≥ (K + 1)Y` carries a `K`-dimensional space on which Gamma minus the head `p ≤ Y` is negative
  definite;
* (`not_exists_uniform_eulerHead_index`) no bound on the negative index holds for all heads;
* (`eventually_logPowerHead_negative_family`) for every `A > 0` the heads `p ≤ (log N)^A` at horizon
  `N` have negative index tending to infinity.

**Mechanism.** The test pairs the details `a = 1, …, K` with coarse windows `b = 1, …, K` placed at
`log Y + [log 2b, log(2b + 2))`, with coarse coefficients `(s/√Y) Lᵀx`. The sharp edge of the head
at `m = Y` couples them with strength `√Y L[a, b]` (`tendsto_headCoupling`), and `L` is lower
triangular with negative diagonal, hence `Σ_b (Lᵀx)_b² ≥ σ‖x‖²`. The Gamma energy of the windows is
translation invariant, so it costs `O(s²/Y)`, while the coupling gains `s σ ‖x‖²`: for
`s σ > 4 Γ(details) + 1` the form is negative for large `Y`.
-/

noncomputable section

open MeasureTheory Finset Filter Topology
open RHTower

namespace GaloisForLFunctions.ArithmeticIndexDescent

open ArithmeticCastelnuovoSeveri.LogCells BiarithmeticGaugeGeometry HTGeometry

local notation "L²₊" => Lp ℂ 2 halfLineMeasure

/-! ### Bilinearity of the mixed source -/

theorem haarSection_sum {ι : Type*} (s : Finset ι) (x : ι → ℝ) (d : ι → ℕ → ℝ) (Y : ℕ) :
    haarSection (fun n => ∑ i ∈ s, x i * d i n) Y = ∑ i ∈ s, (x i : ℂ) • haarSection (d i) Y := by
  unfold haarSection
  simp_rw [smul_sum, smul_smul, Complex.ofReal_sum, Complex.ofReal_mul, sum_smul]
  exact sum_comm

theorem coarseSection_sum {ι : Type*} (s : Finset ι) (z : ι → ℝ) (q : ι → ℕ → ℝ) (X : ℕ) :
    coarseSection (fun n => ∑ j ∈ s, z j * q j n) X = ∑ j ∈ s, (z j : ℂ) • coarseSection (q j) X := by
  unfold coarseSection
  simp_rw [smul_sum, smul_smul, Complex.ofReal_sum, Complex.ofReal_mul, sum_smul]
  exact sum_comm

private theorem re_inner_sum_sum {ι κ : Type*} (s : Finset ι) (t : Finset κ) (x : ι → ℝ)
    (z : κ → ℝ) (u : ι → L²₊) (v : κ → L²₊) :
    (inner ℂ (∑ i ∈ s, (x i : ℂ) • u i) (∑ j ∈ t, (z j : ℂ) • v j)).re =
      ∑ i ∈ s, ∑ j ∈ t, x i * z j * (inner ℂ (u i) (v j)).re := by
  rw [sum_inner, Complex.re_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [inner_sum, Complex.re_sum]
  refine sum_congr rfl fun j _ => ?_
  rw [inner_smul_left, inner_smul_right, Complex.conj_ofReal, ← mul_assoc, ← Complex.ofReal_mul,
    Complex.re_ofReal_mul]

theorem integerMixedSource_sum {ι κ : Type*} (s : Finset ι) (t : Finset κ) (x : ι → ℝ)
    (d : ι → ℕ → ℝ) (z : κ → ℝ) (q : κ → ℕ → ℝ) (m Y X : ℕ) :
    integerMixedSource m (fun n => ∑ i ∈ s, x i * d i n) (fun n => ∑ j ∈ t, z j * q j n) Y X =
      ∑ i ∈ s, ∑ j ∈ t, x i * z j * integerMixedSource m (d i) (q j) Y X := by
  unfold integerMixedSource
  rw [haarSection_sum, coarseSection_sum, map_sum, map_sum]
  simp only [map_smul]
  rw [re_inner_sum_sum, re_inner_sum_sum, sum_comm (s := t), mul_add, mul_sum, mul_sum,
    ← sum_add_distrib]
  refine sum_congr rfl fun i _ => ?_
  rw [mul_sum, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun j _ => ?_
  ring

theorem finiteEulerMixedSource_sum {ι κ : Type*} (s : Finset ι) (t : Finset κ) (x : ι → ℝ)
    (d : ι → ℕ → ℝ) (z : κ → ℝ) (q : κ → ℕ → ℝ) (P : Finset Nat.Primes) (X : ℕ) :
    finiteEulerMixedSource P (fun n => ∑ i ∈ s, x i * d i n) (fun n => ∑ j ∈ t, z j * q j n) X =
      ∑ i ∈ s, ∑ j ∈ t, x i * z j * finiteEulerMixedSource P (d i) (q j) X := by
  unfold finiteEulerMixedSource primeEulerMixedSource
  simp_rw [integerMixedSource_sum]
  have hs : ∀ p : Nat.Primes, ∀ i ∈ s, Summable fun k : ℕ =>
      ∑ j ∈ t, x i * z j * integerMixedSource ((p : ℕ) ^ (k + 1)) (d i) (q j) X X := fun p i _ =>
    summable_sum fun j _ => (summable_primeEulerMixed p (d i) (q j) X).mul_left _
  simp_rw [Summable.tsum_finsetSum (hs _), Summable.tsum_finsetSum fun j _ =>
    (summable_primeEulerMixed _ _ _ X).mul_left _, tsum_mul_left, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun i _ => ?_
  rw [sum_comm]

/-! ### Gamma energy -/

theorem levyEnergy_const_mul (c : ℝ) (f : ℝ → ℝ) :
    levyEnergy (fun u => c * f u) = c ^ 2 * levyEnergy f := by
  unfold levyEnergy
  have h : ∀ x : ℝ, ∫ u, (c * f u - c * f (u + x)) ^ 2 = c ^ 2 * ∫ u, (f u - f (u + x)) ^ 2 :=
    fun x => by rw [← integral_const_mul]; congr 1; funext u; ring
  simp_rw [h]
  rw [← integral_const_mul]
  congr 1
  funext x
  ring

theorem levyEnergy_add_le_two_bv {f g : ℝ → ℝ} (hf : BoundedVariationOn f Set.univ)
    (hg : BoundedVariationOn g Set.univ) (hfc : HasCompactSupport f) (hgc : HasCompactSupport g) :
    levyEnergy (fun u => f u + g u) ≤ 2 * levyEnergy f + 2 * levyEnergy g := by
  have hg' : BoundedVariationOn (fun u => (-1) * g u) Set.univ := bv_const_mul (-1) hg
  have hgc' : HasCompactSupport (fun u => (-1) * g u) := hgc.mul_left
  have h := levyEnergy_sub_le_two_bv hf hg' hfc hgc'
  have he : (fun x => f x - (-1) * g x) = fun u => f u + g u := funext fun u => by ring
  rw [he, levyEnergy_const_mul, neg_one_sq, one_mul] at h
  exact h

theorem averageSectionProfile_bv (q : ℕ → ℝ) (X : ℕ) :
    BoundedVariationOn (averageSectionProfile q X) Set.univ := by
  have h := completePairProfile_bv q (fun _ => 0) X
  have he : completePairProfile q (fun _ => 0) X = averageSectionProfile q X := by
    funext x; simp [completePairProfile, haarSectionProfile]
  rwa [he] at h

theorem averageSectionProfile_hasCompactSupport (q : ℕ → ℝ) (X : ℕ) :
    HasCompactSupport (averageSectionProfile q X) := by
  have h := completePairProfile_compact q (fun _ => 0) X
  have he : completePairProfile q (fun _ => 0) X = averageSectionProfile q X := by
    funext x; simp [completePairProfile, haarSectionProfile]
  rwa [he] at h

/-! ### Triangular couplings are bounded below -/

/-- A lower-triangular matrix with nonzero diagonal: `Σ_j (Σ_i x_i L_ij)² ≥ σ ‖x‖²`. -/
theorem exists_sq_vecMul_ge {K : ℕ} (L : Fin K → Fin K → ℝ) (htri : ∀ i j, i < j → L i j = 0)
    (hdiag : ∀ i, L i i ≠ 0) :
    ∃ σ > 0, ∀ x : Fin K → ℝ, σ * ‖x‖ ^ 2 ≤ ∑ j, (∑ i, x i * L i j) ^ 2 := by
  let ℓ : (Fin K → ℝ) →ₗ[ℝ] (Fin K → ℝ) :=
    { toFun := fun x j => ∑ i, x i * L i j
      map_add' := fun x y => by funext j; simp only [Pi.add_apply, add_mul, sum_add_distrib]
      map_smul' := fun c x => by
        funext j; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_sum, mul_assoc] }
  have hℓ : ∀ x j, ℓ x j = ∑ i, x i * L i j := fun _ _ => rfl
  have hinj : Function.Injective ℓ := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro x hx
    by_contra hne
    have hS : (univ.filter fun i => x i ≠ 0).Nonempty := by
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
      exact ⟨i, mem_filter.mpr ⟨mem_univ _, hi⟩⟩
    have hi₀ : x ((univ.filter fun i => x i ≠ 0).max' hS) ≠ 0 :=
      (mem_filter.mp (max'_mem _ hS)).2
    have hzero : ∀ i, (univ.filter fun i => x i ≠ 0).max' hS < i → x i = 0 := fun i hi => by
      by_contra h
      exact absurd (le_max' _ i (mem_filter.mpr ⟨mem_univ _, h⟩)) (not_le.mpr hi)
    have h := congrFun (LinearMap.mem_ker.mp hx) ((univ.filter fun i => x i ≠ 0).max' hS)
    rw [hℓ, sum_eq_single ((univ.filter fun i => x i ≠ 0).max' hS) (fun i _ hne => ?_)
      (fun h => absurd (mem_univ _) h)] at h
    · exact mul_ne_zero hi₀ (hdiag _) h
    · rcases lt_or_gt_of_ne hne with hlt | hgt
      · rw [htri i _ hlt, mul_zero]
      · rw [hzero i hgt, zero_mul]
  obtain ⟨C, hC, hanti⟩ := (LinearMap.injective_iff_antilipschitz ℓ).mp hinj
  have hC0 : (0 : ℝ) < C := hC
  refine ⟨1 / (C : ℝ) ^ 2, by positivity, fun x => ?_⟩
  have h1 : ‖x‖ ≤ C * ‖ℓ x‖ := by
    have := hanti.le_mul_dist x 0
    simpa only [dist_zero_right, map_zero] using this
  have h2 : ‖ℓ x‖ ^ 2 ≤ ∑ j, (∑ i, x i * L i j) ^ 2 := by
    have hn : ‖ℓ x‖ ≤ Real.sqrt (∑ j, (∑ i, x i * L i j) ^ 2) := by
      refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun j => ?_
      rw [Real.norm_eq_abs, hℓ, ← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt (single_le_sum (f := fun j => (∑ i, x i * L i j) ^ 2)
        (fun j _ => sq_nonneg _) (mem_univ j))
    calc ‖ℓ x‖ ^ 2 ≤ (Real.sqrt (∑ j, (∑ i, x i * L i j) ^ 2)) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hn 2
      _ = _ := Real.sq_sqrt (sum_nonneg fun j _ => sq_nonneg _)
  calc 1 / (C : ℝ) ^ 2 * ‖x‖ ^ 2 ≤ 1 / (C : ℝ) ^ 2 * (C * ‖ℓ x‖) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) h1 2) (by positivity)
    _ = ‖ℓ x‖ ^ 2 := by field_simp
    _ ≤ _ := h2

/-! ### The test family -/

/-- The detail combination `Σ_i x_i e_{i+1}`. -/
def detailComb {K : ℕ} (x : Fin K → ℝ) (n : ℕ) : ℝ := ∑ i, x i * detailUnit (i + 1) n

theorem abs_detailComb_le {K : ℕ} (x : Fin K → ℝ) (n : ℕ) : |detailComb x n| ≤ ‖x‖ := by
  by_cases h : ∃ i : Fin K, n = i + 1
  · obtain ⟨i, rfl⟩ := h
    rw [detailComb, sum_eq_single i (fun j _ hj => by
      simp only [detailUnit]; rw [if_neg (fun h => hj (Fin.ext (by omega))), mul_zero])
      (fun h => absurd (mem_univ _) h)]
    simp only [detailUnit, ↓reduceIte, mul_one]
    rw [← Real.norm_eq_abs]
    exact norm_le_pi_norm x i
  · push Not at h
    rw [detailComb, sum_eq_zero fun i _ => by simp [detailUnit, h i], abs_zero]
    exact norm_nonneg _

theorem detailComb_eq_zero {K : ℕ} (x : Fin K → ℝ) {n : ℕ} (hn : K < n) : detailComb x n = 0 :=
  sum_eq_zero fun i _ => by
    simp only [detailUnit, if_neg (show n ≠ (i : ℕ) + 1 by have := i.2; omega), mul_zero]

/-- Gamma energy of the detail combination: `Γ(Σ x_a h_a) ≤ 2‖x‖² Σ_{a ≤ K} Γ(h_a)`. -/
theorem levyEnergy_haarSectionProfile_detailComb_le {K X : ℕ} (hKX : K ≤ X) (x : Fin K → ℝ) :
    levyEnergy (haarSectionProfile (detailComb x) X) ≤
      2 * ‖x‖ ^ 2 * ∑ a ∈ Icc 1 K, levyEnergy (haarProfile a) := by
  have hdisj : ∀ a ∈ Icc 1 X, ∀ a' ∈ Icc 1 X, a ≠ a' → ∀ u,
      detailComb x a * haarProfile a u = 0 ∨ detailComb x a' * haarProfile a' u = 0 := by
    intro a _ a' _ hne u
    by_contra hcon
    push Not at hcon
    have hsupp : ∀ b : ℕ, haarProfile b u ≠ 0 →
        Real.log ((2 * b : ℕ) : ℝ) ≤ u ∧ u < Real.log ((2 * b + 2 : ℕ) : ℝ) := fun b hb =>
      ⟨not_lt.mp fun h => hb (haarProfile_eq_zero_of_lt h),
        not_le.mp fun h => hb (haarProfile_eq_zero_of_ge h)⟩
    have h1 := hsupp a (right_ne_zero_of_mul hcon.1)
    have h2 := hsupp a' (right_ne_zero_of_mul hcon.2)
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have : Real.log ((2 * a + 2 : ℕ) : ℝ) ≤ Real.log ((2 * a' : ℕ) : ℝ) :=
        Real.log_le_log (by positivity) (by push_cast; norm_cast; omega)
      linarith [h1.2, h2.1]
    · have : Real.log ((2 * a' + 2 : ℕ) : ℝ) ≤ Real.log ((2 * a : ℕ) : ℝ) :=
        Real.log_le_log (by positivity) (by push_cast; norm_cast; omega)
      linarith [h1.1, h2.2]
  have h := levyEnergy_disjoint_sum_le (Icc 1 X) (fun a u => detailComb x a * haarProfile a u)
    (fun a _ => bv_const_mul _ (haarProfile_bv a)) (fun a _ => (haarProfile_compact a).mul_left)
    (haarSectionProfile_bv _ X) (haarSectionProfile_compact _ X) hdisj
  refine h.trans ?_
  simp_rw [levyEnergy_const_mul]
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  have hsplit : ∑ a ∈ Icc 1 X, detailComb x a ^ 2 * levyEnergy (haarProfile a) =
      ∑ a ∈ Icc 1 K, detailComb x a ^ 2 * levyEnergy (haarProfile a) := by
    refine (sum_subset (Icc_subset_Icc_right hKX) fun a ha ha' => ?_).symm
    rw [detailComb_eq_zero x (by simp only [mem_Icc] at ha ha'; omega), sq, zero_mul, zero_mul]
  rw [hsplit, mul_sum]
  refine sum_le_sum fun a _ => mul_le_mul_of_nonneg_right ?_ (levyEnergy_nonneg _)
  rw [← sq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) (abs_detailComb_le x a) 2

/-- The coarse combination `Σ_b z_b 1_{window b}`. -/
def windowComb {K : ℕ} (Y : ℕ) (z : Fin K → ℝ) (n : ℕ) : ℝ := ∑ j, z j * coarseWindow Y (j + 1) n

theorem averageSectionProfile_windowComb {K Y X : ℕ} (z : Fin K → ℝ) (u : ℝ) :
    averageSectionProfile (windowComb Y z) X u =
      ∑ j, z j * averageSectionProfile (coarseWindow Y (j + 1)) X u := by
  simp only [averageSectionProfile, windowComb, sum_mul, mul_sum]
  rw [sum_comm]
  exact sum_congr rfl fun j _ => sum_congr rfl fun n _ => by ring

/-- Gamma energy of the coarse combination: `Γ ≤ 2 Σ_b z_b² Γ(1_{[log 2b, log(2b+2))})`. -/
theorem levyEnergy_averageSectionProfile_windowComb_le {K Y X : ℕ} (hY : 1 ≤ Y)
    (hX : Y * (K + 1) ≤ X + 1) (z : Fin K → ℝ) :
    levyEnergy (averageSectionProfile (windowComb Y z) X) ≤
      2 * ∑ j : Fin K, z j ^ 2 * levyEnergy (coarseProfile (j + 1)) := by
  have hwin : ∀ j : Fin K, ∀ u, averageSectionProfile (coarseWindow Y (j + 1)) X u =
      coarseProfile (j + 1) (u - Real.log Y) := fun j u =>
    averageSectionProfile_coarseWindow hY (by omega) (le_trans (by
      have := j.2; nlinarith) hX) u
  have hdisj : ∀ j ∈ (univ : Finset (Fin K)), ∀ j' ∈ (univ : Finset (Fin K)), j ≠ j' → ∀ u,
      z j * averageSectionProfile (coarseWindow Y (j + 1)) X u = 0 ∨
        z j' * averageSectionProfile (coarseWindow Y (j' + 1)) X u = 0 := by
    intro j _ j' _ hne u
    by_contra hcon
    push Not at hcon
    have hsupp : ∀ b : Fin K, averageSectionProfile (coarseWindow Y (b + 1)) X u ≠ 0 →
        Real.log ((2 * ((b : ℕ) + 1) : ℕ) : ℝ) ≤ u - Real.log Y ∧
          u - Real.log Y < Real.log ((2 * ((b : ℕ) + 1) + 2 : ℕ) : ℝ) := fun b hb => by
      rw [hwin, coarseProfile_eq_indicator (by omega)] at hb
      by_contra h
      rw [Set.indicator_of_notMem (fun hm => h ⟨hm.1, hm.2⟩)] at hb
      exact hb rfl
    have h1 := hsupp j (right_ne_zero_of_mul hcon.1)
    have h2 := hsupp j' (right_ne_zero_of_mul hcon.2)
    have hne' : (j : ℕ) ≠ j' := fun h => hne (Fin.ext h)
    rcases lt_or_gt_of_ne hne' with hlt | hgt
    · have : Real.log ((2 * ((j : ℕ) + 1) + 2 : ℕ) : ℝ) ≤ Real.log ((2 * ((j' : ℕ) + 1) : ℕ) : ℝ) :=
        Real.log_le_log (by positivity) (by norm_cast; omega)
      linarith [h1.2, h2.1]
    · have : Real.log ((2 * ((j' : ℕ) + 1) + 2 : ℕ) : ℝ) ≤ Real.log ((2 * ((j : ℕ) + 1) : ℕ) : ℝ) :=
        Real.log_le_log (by positivity) (by norm_cast; omega)
      linarith [h1.1, h2.2]
  have hfun : averageSectionProfile (windowComb Y z) X =
      fun u => ∑ j, z j * averageSectionProfile (coarseWindow Y (j + 1)) X u :=
    funext fun u => averageSectionProfile_windowComb z u
  have h := levyEnergy_disjoint_sum_le univ
    (fun j u => z j * averageSectionProfile (coarseWindow Y (j + 1)) X u)
    (fun j _ => bv_const_mul _ (averageSectionProfile_bv _ X))
    (fun j _ => (averageSectionProfile_hasCompactSupport _ X).mul_left)
    (hfun ▸ averageSectionProfile_bv _ X) (hfun ▸ averageSectionProfile_hasCompactSupport _ X)
    hdisj
  rw [hfun]
  refine h.trans (le_of_eq ?_)
  simp_rw [levyEnergy_const_mul]
  congr 1
  refine sum_congr rfl fun j _ => ?_
  congr 1
  rw [show averageSectionProfile (coarseWindow Y (j + 1)) X =
    fun u => coarseProfile (j + 1) (u - Real.log Y) from funext (hwin j)]
  exact SpacingScaleHarmonicAnalysis.levyEnergy_translate (g := coarseProfile (j + 1)) _

/-! ### Assembly -/

theorem abs_sum_mul_le_norm {K : ℕ} (x c : Fin K → ℝ) : |∑ i, x i * c i| ≤ ‖x‖ * ∑ i, |c i| := by
  refine (abs_sum_le_sum_abs _ _).trans ?_
  rw [mul_sum]
  refine sum_le_sum fun i _ => ?_
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_right ((Real.norm_eq_abs _).symm.trans_le (norm_le_pi_norm x i))
    (abs_nonneg _)

/-- `|Σ_j (Σ_k x_k L_kj)(Σ_i x_i e_ij)| ≤ ‖x‖² (Σ|L|)(Σ|e|)`. -/
theorem abs_sum_bilinear_le {K : ℕ} (x : Fin K → ℝ) (L e : Fin K → Fin K → ℝ) :
    |∑ j, (∑ k, x k * L k j) * ∑ i, x i * e i j| ≤
      ‖x‖ ^ 2 * (∑ i, ∑ j, |L i j|) * ∑ i, ∑ j, |e i j| := by
  have hL : ∀ j, |∑ k, x k * L k j| ≤ ‖x‖ * ∑ i, ∑ j, |L i j| := fun j =>
    (abs_sum_mul_le_norm x _).trans (mul_le_mul_of_nonneg_left
      (sum_le_sum fun k _ => single_le_sum (f := fun j => |L k j|) (fun _ _ => abs_nonneg _)
        (mem_univ j)) (norm_nonneg _))
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ j, |(∑ k, x k * L k j) * ∑ i, x i * e i j|
      ≤ ∑ j, (‖x‖ * ∑ i, ∑ j, |L i j|) * (‖x‖ * ∑ i, |e i j|) := by
        refine sum_le_sum fun j _ => ?_
        rw [abs_mul]
        exact mul_le_mul (hL j) (abs_sum_mul_le_norm x _) (abs_nonneg _)
          (mul_nonneg (norm_nonneg _) (sum_nonneg fun _ _ => sum_nonneg fun _ _ => abs_nonneg _))
    _ = ∑ j, ‖x‖ ^ 2 * (∑ i, ∑ j, |L i j|) * ∑ i, |e i j| := sum_congr rfl fun j _ => by ring
    _ = ‖x‖ ^ 2 * (∑ i, ∑ j, |L i j|) * ∑ j, ∑ i, |e i j| := by rw [← mul_sum]
    _ = _ := by congr 1; exact sum_comm

/-- The limit coupling matrix of the details and windows `1, …, K`. -/
def headLimitMatrix (K : ℕ) (i j : Fin K) : ℝ := headCouplingLimit ((i : ℕ) + 1) ((j : ℕ) + 1)

/-- **Gamma minus a large Euler head is negative definite on `K` dimensions.** For every `K`, once
`Y` is large, at every horizon `X ≥ max(K, (K + 1)Y − 1)` the family of the details `1, …, K` with
the coarse windows weighted by `(s/√Y) Lᵀ` makes Gamma minus the head `p ≤ Y` negative definite. -/
theorem eventually_eulerHead_negative_family (K : ℕ) :
    ∀ᶠ Y : ℕ in atTop, ∀ X : ℕ, K ≤ X → Y * (K + 1) ≤ X + 1 →
      ∃ q d : Fin K → ℕ → ℝ, ∀ x : Fin K → ℝ, x ≠ 0 →
        finiteEulerGammaProfileForm (eulerHead Y) q d X x < 0 := by
  set L := headLimitMatrix K
  obtain ⟨σ, hσ, hσx⟩ := exists_sq_vecMul_ge L
    (fun i j h => headCouplingLimit_eq_zero_of_lt (by have : (i : ℕ) < j := h; omega))
    (fun i => (headCouplingLimit_self_neg (by omega)).ne)
  set GH := ∑ a ∈ Icc 1 K, levyEnergy (haarProfile a)
  set GC := ∑ j : Fin K, levyEnergy (coarseProfile (j + 1))
  set AL := ∑ i, ∑ j, |L i j|
  have hGH : 0 ≤ GH := sum_nonneg fun _ _ => levyEnergy_nonneg _
  have hGC : 0 ≤ GC := sum_nonneg fun _ _ => levyEnergy_nonneg _
  have hAL : 0 ≤ AL := sum_nonneg fun _ _ => sum_nonneg fun _ _ => abs_nonneg _
  set s := (4 * GH + 1) / σ
  have hs : 0 < s := by positivity
  have hsσ : s * σ = 4 * GH + 1 := by rw [div_mul_cancel₀ _ hσ.ne']
  -- the normalized couplings converge to `L`
  set E : ℕ → ℝ := fun Y => ∑ i : Fin K, ∑ j : Fin K,
    |headCoupling Y ((i : ℕ) + 1) ((j : ℕ) + 1) / Real.sqrt Y - L i j|
  have hE : Tendsto E atTop (𝓝 0) := by
    have h : Tendsto E atTop (𝓝 (∑ i : Fin K, ∑ j : Fin K, |L i j - L i j|)) :=
      tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ =>
        ((tendsto_headCoupling (by omega) (by omega)).sub_const _).abs
    simpa using h
  have hsmall : Tendsto (fun Y : ℕ => 4 * (s ^ 2 / (Y : ℝ)) * (AL ^ 2 * GC) + s * AL * E Y) atTop
      (𝓝 0) := by
    have h1 : Tendsto (fun Y : ℕ => s ^ 2 / (Y : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    simpa using ((h1.const_mul 4).mul_const (AL ^ 2 * GC)).add (hE.const_mul (s * AL))
  filter_upwards [hsmall.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num)),
    eventually_ge_atTop 1] with Y hY hY1 X hKX hX
  have hY0 : (0 : ℝ) < Y := by exact_mod_cast hY1
  have hsY := Real.sqrt_pos.mpr hY0
  set t := s / Real.sqrt Y
  have ht : 0 ≤ t := by positivity
  have ht2 : t ^ 2 = s ^ 2 / Y := by rw [div_pow, Real.sq_sqrt hY0.le]
  refine ⟨fun i n => ∑ j, t * L i j * coarseWindow Y (j + 1) n, fun i => detailUnit (i + 1),
    fun x hx => ?_⟩
  set ℓ : Fin K → ℝ := fun j => ∑ i, x i * L i j
  set z : Fin K → ℝ := fun j => t * ℓ j
  have hq : (fun n => ∑ i, x i * ∑ j, t * L i j * coarseWindow Y (j + 1) n) = windowComb Y z := by
    funext n
    simp only [windowComb, z, ℓ, mul_sum, sum_mul]
    rw [sum_comm]
    exact sum_congr rfl fun j _ => sum_congr rfl fun i _ => by ring
  have hd : (fun n => ∑ i, x i * detailUnit (i + 1) n) = detailComb x := rfl
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  -- the Gamma energy
  have hz : ∀ j, z j ^ 2 ≤ (t * AL * ‖x‖) ^ 2 := fun j => by
    rw [← sq_abs]
    refine pow_le_pow_left₀ (abs_nonneg _) ?_ 2
    rw [abs_mul, abs_of_nonneg ht, mul_assoc]
    refine mul_le_mul_of_nonneg_left ((abs_sum_mul_le_norm x _).trans ?_) ht
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (sum_le_sum fun k _ => single_le_sum
      (f := fun j => |L k j|) (fun _ _ => abs_nonneg _) (mem_univ j)) (norm_nonneg _)
  have hcoarse : levyEnergy (averageSectionProfile (windowComb Y z) X) ≤
      2 * (t * AL * ‖x‖) ^ 2 * GC := by
    have hsum : ∑ j : Fin K, z j ^ 2 * levyEnergy (coarseProfile ((j : ℕ) + 1)) ≤
        (t * AL * ‖x‖) ^ 2 * GC := by
      simp only [GC]
      rw [mul_sum]
      exact sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hz j) (levyEnergy_nonneg _)
    have h := levyEnergy_averageSectionProfile_windowComb_le hY1 hX z
    linarith
  have hdetail := levyEnergy_haarSectionProfile_detailComb_le hKX x
  have henergy : levyEnergy (completePairProfile (windowComb Y z) (detailComb x) X) ≤
      4 * (t * AL * ‖x‖) ^ 2 * GC + 4 * ‖x‖ ^ 2 * GH := by
    have h := levyEnergy_add_le_two_bv (averageSectionProfile_bv (windowComb Y z) X)
      (haarSectionProfile_bv (detailComb x) X) (averageSectionProfile_hasCompactSupport _ X)
      (haarSectionProfile_compact _ X)
    have he : completePairProfile (windowComb Y z) (detailComb x) X =
        fun u => averageSectionProfile (windowComb Y z) X u + haarSectionProfile (detailComb x) X u :=
      rfl
    rw [he]
    linarith
  -- the source
  have hsource : finiteEulerMixedSource (eulerHead Y) (detailComb x) (windowComb Y z) X =
      s * ∑ j, ℓ j * ∑ i, x i * (headCoupling Y ((i : ℕ) + 1) ((j : ℕ) + 1) / Real.sqrt Y) := by
    have h := finiteEulerMixedSource_sum univ univ x (fun i => detailUnit (i + 1)) z
      (fun j => coarseWindow Y (j + 1)) (eulerHead Y) X
    have hdc : detailComb x = fun n => ∑ i, x i * detailUnit (i + 1) n := rfl
    have hwc : windowComb Y z = fun n => ∑ j, z j * coarseWindow Y (j + 1) n := rfl
    rw [hdc, hwc, h]
    have hB : ∀ i j : Fin K, finiteEulerMixedSource (eulerHead Y) (detailUnit ((i : ℕ) + 1))
        (coarseWindow Y ((j : ℕ) + 1)) X = headCoupling Y ((i : ℕ) + 1) ((j : ℕ) + 1) := fun i j =>
      finiteEulerMixedSource_detailUnit_coarseWindow (by omega) (by have := i.2; omega) hY1
        (by omega) (le_trans (Nat.mul_le_mul_left Y (by have := j.2; omega)) hX)
    simp_rw [hB]
    rw [sum_comm, mul_sum]
    refine sum_congr rfl fun j _ => ?_
    rw [mul_sum, mul_sum]
    refine sum_congr rfl fun i _ => ?_
    simp only [z, t]
    field_simp
  have hsplit : ∑ j, ℓ j * ∑ i, x i * (headCoupling Y ((i : ℕ) + 1) ((j : ℕ) + 1) / Real.sqrt Y) =
      ∑ j, ℓ j ^ 2 + ∑ j, ℓ j * ∑ i, x i *
        (headCoupling Y ((i : ℕ) + 1) ((j : ℕ) + 1) / Real.sqrt Y - L i j) := by
    rw [← sum_add_distrib]
    refine sum_congr rfl fun j _ => ?_
    simp only [ℓ, mul_sub, sum_sub_distrib]
    ring
  have hcross := abs_sum_bilinear_le x L
    (fun i j => headCoupling Y ((i : ℕ) + 1) ((j : ℕ) + 1) / Real.sqrt Y - L i j)
  have hlow : σ * ‖x‖ ^ 2 - ‖x‖ ^ 2 * AL * E Y ≤
      ∑ j, ℓ j * ∑ i, x i * (headCoupling Y ((i : ℕ) + 1) ((j : ℕ) + 1) / Real.sqrt Y) := by
    rw [hsplit]
    have h1 := hσx x
    have h2 := neg_abs_le (∑ j, ℓ j * ∑ i, x i *
      (headCoupling Y ((i : ℕ) + 1) ((j : ℕ) + 1) / Real.sqrt Y - L i j))
    linarith
  -- the form
  have hform : finiteEulerGammaProfileForm (eulerHead Y)
      (fun i n => ∑ j, t * L i j * coarseWindow Y (j + 1) n) (fun i => detailUnit (i + 1)) X x =
      levyEnergy (completePairProfile (windowComb Y z) (detailComb x) X) -
        finiteEulerMixedSource (eulerHead Y) (detailComb x) (windowComb Y z) X := by
    rw [finiteEulerGammaProfileForm, hq, hd]
  rw [hform, hsource]
  have hxx : 0 < ‖x‖ ^ 2 := by positivity
  have hkey : 4 * (s ^ 2 / (Y : ℝ)) * (AL ^ 2 * GC) + s * AL * E Y < 1 := hY
  have hexp : 4 * (t * AL * ‖x‖) ^ 2 * GC = ‖x‖ ^ 2 * (4 * (s ^ 2 / (Y : ℝ)) * (AL ^ 2 * GC)) := by
    rw [← ht2]; ring
  nlinarith [mul_le_mul_of_nonneg_left hlow hs.le, mul_lt_mul_of_pos_left hkey hxx]

/-- **No uniform index for the Euler heads.** No bound on the negative index of Gamma minus the
complete mixed Euler source holds for all heads `p ≤ Y` and all horizons. -/
theorem not_exists_uniform_eulerHead_index :
    ¬ ∃ C : ℕ, ∀ (Y X n : ℕ) (q d : Fin n → ℕ → ℝ) (W : Submodule ℝ (Fin n → ℝ)),
      (∀ x ∈ W, x ≠ 0 → finiteEulerGammaProfileForm (eulerHead Y) q d X x < 0) →
        Module.finrank ℝ W ≤ C := by
  rintro ⟨C, hC⟩
  obtain ⟨Y, hY, hY1⟩ := ((eventually_eulerHead_negative_family (C + 1)).and
    (eventually_ge_atTop 1)).exists
  obtain ⟨q, d, hneg⟩ := hY (Y * (C + 1 + 1)) (le_trans (Nat.le_succ _)
    (Nat.le_mul_of_pos_left _ hY1)) (Nat.le_succ _)
  have h := hC Y _ (C + 1) q d ⊤ fun x _ hx => hneg x hx
  rw [finrank_top, Module.finrank_fin_fun] at h
  omega

/-- **The heads `p ≤ (log N)^A` have unbounded index.** For every `A > 0` and every `K`, eventually
in `N` Gamma minus the head `p ≤ ⌊(log N)^A⌋` at horizon `N` is negative definite on `K`
dimensions. -/
theorem eventually_logPowerHead_negative_family {A : ℝ} (hA : 0 < A) (K : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∃ q d : Fin K → ℕ → ℝ, ∀ x : Fin K → ℝ, x ≠ 0 →
      finiteEulerGammaProfileForm (eulerHead ⌊Real.log N ^ A⌋₊) q d N x < 0 := by
  have hlog : Tendsto (fun N : ℕ => Real.log N ^ A) atTop atTop :=
    (tendsto_rpow_atTop hA).comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hYN : Tendsto (fun N : ℕ => ⌊Real.log N ^ A⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp hlog
  have hsmall : ∀ᶠ N : ℕ in atTop, Real.log N ^ A ≤ (N : ℝ) / (K + 1) := by
    have h := (isLittleO_log_rpow_rpow_atTop A (show (0 : ℝ) < 1 by norm_num)).bound
      (show (0 : ℝ) < 1 / (K + 1) by positivity)
    filter_upwards [tendsto_natCast_atTop_atTop.eventually h,
      tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (1 : ℝ))] with N hN hN1
    have hl : 0 ≤ Real.log N := Real.log_nonneg hN1
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hl _), Real.rpow_one,
      Real.norm_of_nonneg (by linarith)] at hN
    calc Real.log N ^ A ≤ 1 / (K + 1) * N := hN
      _ = (N : ℝ) / (K + 1) := by ring
  filter_upwards [hYN.eventually (eventually_eulerHead_negative_family K), hsmall,
    eventually_ge_atTop K] with N hN hsm hKN
  refine hN N hKN ?_
  have hfl : (⌊Real.log N ^ A⌋₊ : ℝ) ≤ Real.log N ^ A :=
    Nat.floor_le (Real.rpow_nonneg (Real.log_natCast_nonneg N) _)
  have : ((⌊Real.log N ^ A⌋₊ * (K + 1) : ℕ) : ℝ) ≤ N := by
    push_cast
    calc (⌊Real.log N ^ A⌋₊ : ℝ) * (K + 1) ≤ (N : ℝ) / (K + 1) * (K + 1) :=
          mul_le_mul_of_nonneg_right (hfl.trans hsm) (by positivity)
      _ = N := by field_simp
  have : ⌊Real.log N ^ A⌋₊ * (K + 1) ≤ N := by exact_mod_cast this
  omega

end GaloisForLFunctions.ArithmeticIndexDescent

#print axioms GaloisForLFunctions.ArithmeticIndexDescent.eventually_eulerHead_negative_family
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.eventually_logPowerHead_negative_family
