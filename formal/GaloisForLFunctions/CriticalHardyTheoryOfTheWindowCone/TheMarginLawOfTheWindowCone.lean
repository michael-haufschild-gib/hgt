import GaloisForLFunctions.CriticalHardyTheoryOfTheWindowCone.TheTwistedArcFamilyIsNearNull
import GaloisForLFunctions.RHTower.PrimeBlindLevelFloor
import GaloisForLFunctions.RHTower.PrimeBlindPoleCurvatureFloor
import GaloisForLFunctions.ArithmeticIncidencePositivity.MultiPrimeDilationModulusAndIteratedWeilFloors

/-!
# The margin law of the window cone

The **best margin** `λ*(c) = sup_λ inf_f W_λ(f)/‖f‖²` of the window `[−c, c]` is the level value of the
blind functional at pole weight one (`bestMargin`, `exists_hasMargin_iff_le_bestMargin`), by the
finite-level duality. Its behaviour:

* **Ceiling** (`exists_bestMargin_le`): `λ*(c) ≤ K exp(3c − (π/6) e^{2(c−13/12)})` for `c ≥ 3`, over all
  weights, unconditionally. This is the law known for `Λ` alone, carried to the supremum over the cone.
* **RH is the limit** (`riemannHypothesis_iff_tendsto_bestMargin`): `λ*(c) → 0` iff RH. Under RH the
  best margin is nonnegative and below the ceiling; otherwise it is eventually negative and antitone.
* **Floors** (`weilFloorTowerConst_le_bestMargin`): the known tower of positive floors at apertures
  `a_k` is a lower bound for `λ*(a_k)`.

**The margin is an inradius** (`hasMargin_add`, `Icc_subset_bandSet`). A finitely supported perturbation
`v` of the weights costs at most `Σ_n 2|v(n)|/√n` of margin, so a weight with margin `m` carries a ball
of that radius inside the cone. In particular the band of `λ(n)` has width at least `m√n`: a margin
forces bands, and the ceiling is what bands must respect from below at each finite level.
-/

open MeasureTheory Filter Topology Set
open scoped Nat Real

noncomputable section

namespace GaloisForLFunctions.CriticalHardyTheoryOfTheWindowCone

open _root_.RHTower _root_.RHTower.WeilSpectral _root_.RHTower.WeilOneSided _root_.Zeta23

/-! ### Margins -/

/-- `m` is a margin of the weights `lam` on the window `[−c, c]`. -/
def HasMargin (lam : ℕ → ℝ) (c m : ℝ) : Prop :=
  ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-c) c →
    m * ∫ u, ‖f u‖ ^ 2 ≤ (weilFullFunctional lam (EF.weilTest f f)).re

theorem HasMargin.weilPositiveFullUpTo {lam : ℕ → ℝ} {c m : ℝ} (h : HasMargin lam c m)
    (hm : 0 ≤ m) : WeilPositiveFullUpTo lam c := fun f hf hfs =>
  (mul_nonneg hm (integral_nonneg fun _ => by positivity)).trans (h f hf hfs)

theorem HasMargin.mono {lam : ℕ → ℝ} {c m m' : ℝ} (h : HasMargin lam c m) (hm : m' ≤ m) :
    HasMargin lam c m' := fun f hf hfs =>
  (mul_le_mul_of_nonneg_right hm (integral_nonneg fun _ => by positivity)).trans (h f hf hfs)

theorem HasMargin.anti {lam : ℕ → ℝ} {c c' m : ℝ} (h : HasMargin lam c m) (hc : c' ≤ c) :
    HasMargin lam c' m := fun f hf hfs =>
  h f hf (hfs.trans (Icc_subset_Icc (by linarith) hc))

theorem hasCompactSupport_of_tsupport_subset {f : ℝ → ℂ} {c : ℝ}
    (hfs : tsupport f ⊆ Icc (-c) c) : HasCompactSupport f :=
  IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport f) hfs

/-- The level test attached to a window test. -/
theorem levelTest_of_tsupport {f : ℝ → ℂ} {c : ℝ} (hf : ContDiff ℝ 2 f)
    (hfs : tsupport f ⊆ Icc (-c) c) :
    LevelTest c (⟨f, hf, hasCompactSupport_of_tsupport_subset hfs⟩ : WeilTestFn) :=
  fun _ hu => abs_le.mpr (hfs (subset_tsupport _ hu))

theorem poleWeightFunctional_one (f : WeilTestFn) :
    poleWeightFunctional 1 f = weilArchRe (EF.weilTest f.1 f.1) := by
  simp [poleWeightFunctional]

/-- **Margins are the level margins of the blind functional.** -/
theorem exists_hasMargin_iff_mem_levelMargins {c m : ℝ} :
    (∃ lam : ℕ → ℝ, HasMargin lam c m) ↔ m ∈ levelMargins c 1 := by
  constructor
  · rintro ⟨lam, h⟩
    refine ⟨fun j => lam j, fun g hg => ?_⟩
    have h1 := h g.1 g.2.1 (tsupport_subset_of_levelTest hg)
    rw [re_weilFullFunctional_eq lam g] at h1
    rw [poleWeightFunctional_one]
    unfold testMass
    linarith
  · rintro ⟨lam', h⟩
    set lam : ℕ → ℝ := fun n => if hn : 2 ≤ n then lam' ⟨n, hn⟩ else 0 with hlam
    have heq : (fun j : LogIndex => lam j) = lam' := by
      funext j
      simp [hlam, j.2]
    refine ⟨lam, fun f hf hfs => ?_⟩
    set g : WeilTestFn := ⟨f, hf, hasCompactSupport_of_tsupport_subset hfs⟩ with hg
    have h1 := h g (levelTest_of_tsupport hf hfs)
    have h2 := re_weilFullFunctional_eq lam g
    rw [heq] at h2
    rw [poleWeightFunctional_one] at h1
    unfold testMass at h1
    change _ ≤ (weilFullFunctional lam (EF.weilTest g.1 g.1)).re
    change _ * ∫ u, ‖g.1 u‖ ^ 2 ≤ _
    linarith

/-- The best margin `λ*(c)` of the window `[−c, c]`. -/
def bestMargin (c : ℝ) : ℝ := levelValueAt c 1

/-- `m` is a margin of some weights iff `m ≤ λ*(c)`. -/
theorem exists_hasMargin_iff_le_bestMargin {c m : ℝ} (hc : 3 / 10 ≤ c) :
    (∃ lam : ℕ → ℝ, HasMargin lam c m) ↔ m ≤ bestMargin c := by
  rw [exists_hasMargin_iff_mem_levelMargins, ← levelFloors_eq_levelMargins,
    levelFloors_eq_Iic hc 1, mem_Iic]
  rfl

/-- The best margin is attained. -/
theorem exists_hasMargin_bestMargin {c : ℝ} (hc : 3 / 10 ≤ c) :
    ∃ lam : ℕ → ℝ, HasMargin lam c (bestMargin c) :=
  (exists_hasMargin_iff_le_bestMargin hc).mpr le_rfl

theorem bestMargin_antitone {c c' : ℝ} (hc : 3 / 10 ≤ c) (hcc : c ≤ c') :
    bestMargin c' ≤ bestMargin c :=
  levelValueAt_antitone hc hcc 1

/-- `𝒜(c)` is nonempty iff the best margin is nonnegative. -/
theorem exists_weilPositiveFullUpTo_iff_nonneg_bestMargin {c : ℝ} (hc : 3 / 10 ≤ c) :
    (∃ lam : ℕ → ℝ, WeilPositiveFullUpTo lam c) ↔ 0 ≤ bestMargin c := by
  rw [← exists_hasMargin_iff_le_bestMargin hc]
  refine exists_congr fun lam => ⟨fun h f hf hfs => ?_, fun h => h.weilPositiveFullUpTo le_rfl⟩
  rw [zero_mul]
  exact h f hf hfs

/-! ### The ceiling -/

/-- **The margin law.** `λ*(c) ≤ K exp(3c − (π/6) e^{2(c−13/12)})` for `c ≥ 3`, over all weights. -/
theorem exists_bestMargin_le :
    ∃ K : ℝ, 0 < K ∧ ∀ c : ℝ, 3 ≤ c → bestMargin c ≤ K * marginCeiling c := by
  obtain ⟨K, hK, h⟩ := exists_margin_ceiling
  refine ⟨K, hK, fun c hc => ?_⟩
  by_cases hm : 0 ≤ bestMargin c
  · obtain ⟨lam, hlam⟩ := exists_hasMargin_bestMargin (c := c) (by linarith)
    exact h c _ lam hc hm hlam
  · exact (not_le.mp hm).le.trans (mul_pos hK (marginCeiling_pos c)).le

theorem tendsto_marginCeiling : Tendsto marginCeiling atTop (𝓝 0) := by
  have hexp : Tendsto (fun c : ℝ => 3 * c - Real.pi / 6 * Real.exp (2 * (c - 13 / 12))) atTop atBot := by
    refine tendsto_atBot.mpr fun b => ?_
    filter_upwards [eventually_ge_atTop (|b| + 40)] with c hc
    have hb := neg_abs_le b
    have hab := abs_nonneg b
    obtain ⟨y, hy⟩ : ∃ y, y = 2 * (c - 13 / 12) := ⟨_, rfl⟩
    rw [← hy]
    have hy0 : 76 + 2 * |b| ≤ y := by rw [hy]; linarith
    have hq := Real.quadratic_le_exp_of_nonneg (by linarith : 0 ≤ y)
    have hπ := Real.pi_gt_three
    have h1 : (1 : ℝ) / 2 * Real.exp y ≤ Real.pi / 6 * Real.exp y :=
      mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
    have hc' : c = y / 2 + 13 / 12 := by rw [hy]; ring
    have hyy : (76 + 2 * |b|) * y ≤ y ^ 2 := by nlinarith
    rw [hc']
    nlinarith
  exact Real.tendsto_exp_atBot.comp hexp

/-- `e^{11/6} ≥ 6`: the window loses only `13/12` of aperture, against the `2` of the Gaussian ceiling. -/
theorem six_le_exp_eleven_sixths : (6 : ℝ) ≤ Real.exp (11 / 6) := by
  have h1 : (27 / 10 : ℝ) ≤ Real.exp 1 := by
    have := Real.exp_one_gt_d9
    linarith
  have h2 : (27 / 10 : ℝ) ^ 11 ≤ Real.exp 1 ^ 11 := pow_le_pow_left₀ (by norm_num) h1 11
  have h3 : Real.exp 1 ^ 11 = Real.exp (11 / 6) ^ 6 := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
    norm_num
  by_contra hcon
  rw [not_le] at hcon
  have h4 := pow_lt_pow_left₀ hcon (Real.exp_pos _).le (by norm_num : (6 : ℕ) ≠ 0)
  rw [← h3] at h4
  norm_num at h2 h4
  linarith

/-- The ceiling is below the Gaussian ceiling of the Weil form. -/
theorem marginCeiling_le_gaussian {c : ℝ} (hc : 0 ≤ c) :
    marginCeiling c ≤ Real.exp (11 / 2 * c - Real.pi * Real.exp (2 * (c - 2))) := by
  unfold marginCeiling
  refine Real.exp_le_exp.mpr ?_
  have e : Real.exp (2 * (c - 13 / 12)) = Real.exp (11 / 6) * Real.exp (2 * (c - 2)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h6 := six_le_exp_eleven_sixths
  have hE := Real.exp_pos (2 * (c - 2))
  have hπ := Real.pi_pos
  rw [e]
  have h : Real.pi * Real.exp (2 * (c - 2)) ≤
      Real.pi / 6 * (Real.exp (11 / 6) * Real.exp (2 * (c - 2))) := by
    have := mul_le_mul_of_nonneg_right h6 (mul_pos hπ hE).le
    nlinarith
  linarith

/-- **The Gaussian ceiling holds for every weight.** `λ*(c) ≤ K exp((11/2)c − π e^{2(c−2)})` for `c ≥ 3`:
the bound known for `Λ` holds for the best margin over all weights. -/
theorem exists_bestMargin_le_gaussian :
    ∃ K : ℝ, 0 < K ∧ ∀ c : ℝ, 3 ≤ c →
      bestMargin c ≤ K * Real.exp (11 / 2 * c - Real.pi * Real.exp (2 * (c - 2))) := by
  obtain ⟨K, hK, h⟩ := exists_bestMargin_le
  exact ⟨K, hK, fun c hc => (h c hc).trans
    (mul_le_mul_of_nonneg_left (marginCeiling_le_gaussian (by linarith)) hK.le)⟩

/-- **RH is the limit of the best margin.** `λ*(c) → 0` iff RH. -/
theorem riemannHypothesis_iff_tendsto_bestMargin :
    RiemannHypothesis ↔ Tendsto bestMargin atTop (𝓝 0) := by
  constructor
  · intro hRH
    obtain ⟨K, -, hK⟩ := exists_bestMargin_le
    have hup : Tendsto (fun c => K * marginCeiling c) atTop (𝓝 0) := by
      simpa using tendsto_marginCeiling.const_mul K
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
    · filter_upwards [eventually_ge_atTop (3 / 10 : ℝ)] with c hc
      exact riemannHypothesis_iff_forall_nonneg_levelValueAt.mp hRH c hc
    · filter_upwards [eventually_ge_atTop (3 : ℝ)] with c hc
      exact hK c hc
  · intro hlim
    rw [riemannHypothesis_iff_forall_nonneg_levelValueAt]
    intro L hL
    refine le_of_tendsto hlim ?_
    filter_upwards [eventually_ge_atTop L] with c hc
    exact bestMargin_antitone hL hc

/-- The tower of unconditional floors bounds the best margin from below. -/
theorem weilFloorTowerConst_le_bestMargin (k : ℕ) :
    ArithmeticIncidencePositivity.weilFloorTowerConst k ≤
      bestMargin (ArithmeticIncidencePositivity.weilFloorApertureTower k) := by
  have ha : (3 / 10 : ℝ) ≤ ArithmeticIncidencePositivity.weilFloorApertureTower k := by
    have h1 := ArithmeticIncidencePositivity.enlargedWeilFloorAperture_bounds.1
    have h2 := ArithmeticIncidencePositivity.enlargedWeilFloorAperture_lt_weilFloorApertureTower k
    linarith
  refine (exists_hasMargin_iff_le_bestMargin ha).mp
    ⟨fun n => (ArithmeticFunction.vonMangoldt n : ℝ), fun f hf hfs => ?_⟩
  have h := ArithmeticIncidencePositivity.zetaZeroConfig_re_W_ge_of_aperture_le_weilFloorApertureTower
    k hf hfs
  rwa [zeta_W_eq_weilFullFunctional hf (hasCompactSupport_of_tsupport_subset hfs)] at h

/-! ### The margin is an inradius -/

/-- The operator size of a finitely supported perturbation of the weights. -/
def perturbationSize (s : Finset ℕ) (v : ℕ → ℝ) : ℝ :=
  ∑ n ∈ s, if 2 ≤ n then 2 * |v n| / Real.sqrt n else 0

theorem perturbationSize_nonneg (s : Finset ℕ) (v : ℕ → ℝ) : 0 ≤ perturbationSize s v :=
  Finset.sum_nonneg fun n _ => by split_ifs <;> positivity

theorem abs_re_log_atom_le (g : WeilTestFn) (n : ℕ) :
    |(EF.weilTest g.1 g.1 (Real.log n) + EF.weilTest g.1 g.1 (-Real.log n)).re| ≤
      2 * ∫ u, ‖g.1 u‖ ^ 2 := by
  have h1 := norm_weilTest_self_le_testMass g (Real.log n)
  have h2 := norm_weilTest_self_le_testMass g (-Real.log n)
  unfold testMass at h1 h2
  calc _ ≤ ‖EF.weilTest g.1 g.1 (Real.log n) + EF.weilTest g.1 g.1 (-Real.log n)‖ :=
        Complex.abs_re_le_norm _
    _ ≤ _ := (norm_add_le _ _).trans (by linarith)

/-- A finitely supported perturbation moves Weil's functional by at most its operator size. -/
theorem re_weilFullFunctional_add_ge {lam v : ℕ → ℝ} {s : Finset ℕ} (hv : ∀ n, n ∉ s → v n = 0)
    {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    (weilFullFunctional lam (EF.weilTest f f)).re - perturbationSize s v * ∫ u, ‖f u‖ ^ 2 ≤
      (weilFullFunctional (fun n => lam n + v n) (EF.weilTest f f)).re := by
  set g : WeilTestFn := ⟨f, hf, hfc⟩ with hg
  obtain ⟨N₀, hN₀⟩ := exists_forall_log_eq_zero (EF.weilTest_hasCompactSupport hfc hfc)
  obtain ⟨N, hN⟩ : ∃ N, N = max N₀ (s.sup id + 1) := ⟨_, rfl⟩
  have hNk : ∀ n : ℕ, N ≤ n → EF.weilTest f f (Real.log n) = 0 ∧
      EF.weilTest f f (-Real.log n) = 0 :=
    fun n hn => hN₀ n ((le_max_left _ _).trans (hN ▸ hn))
  have e₁ := re_weilFullFunctional_eq_affine (fun n => lam n + v n) hNk
  have e₂ := re_weilFullFunctional_eq_affine lam hNk
  obtain ⟨R, hR⟩ : ∃ R : ℕ → ℝ, R = fun n : ℕ =>
    (EF.weilTest f f (Real.log n) + EF.weilTest f f (-Real.log n)).re := ⟨_, rfl⟩
  have hdiff : (weilFullFunctional (fun n => lam n + v n) (EF.weilTest f f)).re =
      (weilFullFunctional lam (EF.weilTest f f)).re -
        ∑ n ∈ Finset.range N, (if 2 ≤ n then v n / Real.sqrt n else 0) * R n := by
    rw [e₁, e₂, sub_sub, ← Finset.sum_add_distrib, hR]
    congr 1
    refine Finset.sum_congr rfl fun n _ => ?_
    split_ifs <;> ring
  have hs : s ⊆ Finset.range N := by
    intro n hn
    have hle : n ≤ s.sup id := Finset.le_sup (f := id) hn
    have : s.sup id + 1 ≤ N := by rw [hN]; exact le_max_right _ _
    exact Finset.mem_range.mpr (by omega)
  have hsub : ∑ n ∈ Finset.range N, (if 2 ≤ n then v n / Real.sqrt n else 0) * R n =
      ∑ n ∈ s, (if 2 ≤ n then v n / Real.sqrt n else 0) * R n :=
    (Finset.sum_subset hs fun n _ hn => by simp [hv n hn]).symm
  have hM : ∀ n, |R n| ≤ 2 * ∫ u, ‖f u‖ ^ 2 := fun n => by
    rw [hR]
    exact abs_re_log_atom_le g n
  have hle : ∑ n ∈ s, (if 2 ≤ n then v n / Real.sqrt n else 0) * R n ≤
      perturbationSize s v * ∫ u, ‖f u‖ ^ 2 := by
    unfold perturbationSize
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun n _ => ?_
    split_ifs with h2
    · have hq := Real.sqrt_nonneg (n : ℝ)
      calc v n / Real.sqrt n * R n ≤ |v n / Real.sqrt n * R n| := le_abs_self _
        _ = |v n| / Real.sqrt n * |R n| := by rw [abs_mul, abs_div, abs_of_nonneg hq]
        _ ≤ |v n| / Real.sqrt n * (2 * ∫ u, ‖f u‖ ^ 2) :=
            mul_le_mul_of_nonneg_left (hM n) (by positivity)
        _ = _ := by ring
    · simp
  rw [hdiff, hsub]
  linarith

/-- **A perturbation of the weights costs its operator size in margin.** -/
theorem hasMargin_add {lam v : ℕ → ℝ} {s : Finset ℕ} {c m : ℝ} (hv : ∀ n, n ∉ s → v n = 0)
    (h : HasMargin lam c m) :
    HasMargin (fun n => lam n + v n) c (m - perturbationSize s v) := by
  intro f hf hfs
  have h1 := re_weilFullFunctional_add_ge (lam := lam) hv hf (hasCompactSupport_of_tsupport_subset hfs)
  have h2 := h f hf hfs
  rw [sub_mul]
  linarith

/-- The values of the weight at `n` over the cone `𝒜(c)`. -/
def bandSet (c : ℝ) (n : ℕ) : Set ℝ := {t | ∃ lam : ℕ → ℝ, WeilPositiveFullUpTo lam c ∧ lam n = t}

/-- **A margin forces a band.** If `lam` has margin `m` on the window, the band of `λ(n)` contains the
interval of radius `m√n/2` around `lam n`. -/
theorem Icc_subset_bandSet {lam : ℕ → ℝ} {c m : ℝ} (h : HasMargin lam c m) {n : ℕ} (hn : 2 ≤ n) :
    Icc (lam n - m * Real.sqrt n / 2) (lam n + m * Real.sqrt n / 2) ⊆ bandSet c n := by
  intro t ht
  set v : ℕ → ℝ := fun k => if k = n then t - lam n else 0 with hv
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hq : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
  have hadd := hasMargin_add (s := {n}) (v := v) (fun k hk => by simp at hk; simp [hv, hk]) h
  have hsize : perturbationSize {n} v ≤ m := by
    unfold perturbationSize
    rw [Finset.sum_singleton, if_pos hn]
    simp only [hv, if_true]
    rw [div_le_iff₀ hq]
    have : |t - lam n| ≤ m * Real.sqrt n / 2 := by
      rw [abs_le]
      constructor <;> linarith [ht.1, ht.2]
    linarith
  refine ⟨fun k => lam k + v k, (hadd.weilPositiveFullUpTo (by linarith)), ?_⟩
  simp [hv]

/-- **Band widths dominate margins**: two points of the band of `λ(n)` lie `m√n` apart. -/
theorem exists_band_width_ge {lam : ℕ → ℝ} {c m : ℝ} (h : HasMargin lam c m) (hm : 0 ≤ m) {n : ℕ}
    (hn : 2 ≤ n) : ∃ t₁ ∈ bandSet c n, ∃ t₂ ∈ bandSet c n, t₂ - t₁ = m * Real.sqrt n := by
  have hq := Real.sqrt_nonneg (n : ℝ)
  have hr : 0 ≤ m * Real.sqrt n / 2 := by positivity
  refine ⟨lam n - m * Real.sqrt n / 2, Icc_subset_bandSet h hn ⟨le_rfl, by linarith⟩,
    lam n + m * Real.sqrt n / 2, Icc_subset_bandSet h hn ⟨by linarith, le_rfl⟩, by ring⟩

end GaloisForLFunctions.CriticalHardyTheoryOfTheWindowCone
