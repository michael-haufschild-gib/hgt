import GaloisForLFunctions.FiniteFreeProbability.HurwitzDeflation
import GaloisForLFunctions.InfiniteRankPurityTheory.ADefectOfIndexOneIsPureOffTheRealAxis
import GaloisForLFunctions.RHTower.XiGlobalKummerSquareClasses
import GaloisForLFunctions.RHTower.VonMangoldtMinusOneAbscissa

/-!
# The index is semicontinuous

In a family of Frobenius modules the weights of a special member do not exceed the generic weights.
The infinite-rank form: along a locally uniform limit of entire functions the number of zeros in an
open set cannot jump up. Zeros may leave to infinity, they cannot appear.

* `zeros_subsingleton_of_tendstoLocallyUniformly`: if eventually every member of the sequence has at
  most one zero in an open set `U`, so has the limit (Hurwitz).
* `im_eq_zero_of_limit_of_indexOne`: a locally uniform limit of real entire functions each with at
  most one zero right of the line has at most one zero right of the line, and that zero is real:
  purity by parity passes to limits.
* `riemannHypothesis_iff_limit_of_indexOne`: RH holds iff `ξ` is a locally uniform limit of real
  entire functions each with at most one zero right of the line. The cleared constant terms of the
  Eisenstein series are such functions; `ξ` has no real zero, so a limit of them that equals `ξ` has
  no zero right of the line.
* `encard_zeros_le_of_tendstoLocallyUniformly`, `encard_xi_zeros_le_of_limit`: the same at any
  index: a bound `κ` on the number of zeros in an open set passes to the limit, so a limit of
  functions of index `≤ κ` that equals `ξ` leaves at most `κ` zeros right of the line.
-/

open Complex Filter Topology Set Metric

namespace GaloisForLFunctions.InfiniteRankPurityTheory

open _root_.RHTower

/-- **The index cannot jump up in a limit.** If eventually every `P n` has at most one zero in the
open set `U`, the locally uniform limit `g ≢ 0` has at most one zero in `U`. -/
theorem zeros_subsingleton_of_tendstoLocallyUniformly {P : ℕ → ℂ → ℂ} {g : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hP : TendstoLocallyUniformly P g atTop) (hPd : ∀ n, Differentiable ℂ (P n))
    (hg : Differentiable ℂ g) {a : ℂ} (ha : g a ≠ 0)
    (hsub : ∀ᶠ n in atTop, {u | u ∈ U ∧ P n u = 0}.Subsingleton) :
    {u | u ∈ U ∧ g u = 0}.Subsingleton := by
  rintro z₁ ⟨h₁U, h₁⟩ z₂ ⟨h₂U, h₂⟩
  by_contra hne
  have hd : 0 < dist z₁ z₂ := dist_pos.mpr hne
  obtain ⟨r₁, hr₁, hb₁⟩ := Metric.isOpen_iff.mp hU z₁ h₁U
  obtain ⟨r₂, hr₂, hb₂⟩ := Metric.isOpen_iff.mp hU z₂ h₂U
  set r : ℝ := min (min r₁ r₂) (dist z₁ z₂ / 2) with hr
  have hrpos : 0 < r := lt_min (lt_min hr₁ hr₂) (by positivity)
  have hrr₁ : r ≤ r₁ := (min_le_left _ _).trans (min_le_left _ _)
  have hrr₂ : r ≤ r₂ := (min_le_left _ _).trans (min_le_right _ _)
  have hrd : r ≤ dist z₁ z₂ / 2 := min_le_right _ _
  have e₁ := FiniteFreeProbability.eventually_exists_zero_of_tendstoLocallyUniformly hP hPd hg ha
    h₁ hrpos
  have e₂ := FiniteFreeProbability.eventually_exists_zero_of_tendstoLocallyUniformly hP hPd hg ha
    h₂ hrpos
  obtain ⟨n, ⟨u₁, hu₁, hz₁⟩, ⟨u₂, hu₂, hz₂⟩, hs⟩ := (e₁.and (e₂.and hsub)).exists
  have hu₁U : u₁ ∈ U := hb₁ (Metric.ball_subset_ball hrr₁ hu₁)
  have hu₂U : u₂ ∈ U := hb₂ (Metric.ball_subset_ball hrr₂ hu₂)
  have heq : u₁ = u₂ := hs ⟨hu₁U, hz₁⟩ ⟨hu₂U, hz₂⟩
  have h1 : dist u₁ z₁ < r := Metric.mem_ball.mp hu₁
  have h2 : dist u₂ z₂ < r := Metric.mem_ball.mp hu₂
  rw [← heq] at h2
  have htri : dist z₁ z₂ ≤ dist z₁ u₁ + dist u₁ z₂ := dist_triangle _ _ _
  rw [dist_comm z₁ u₁] at htri
  linarith

/-- A pointwise limit of real functions is real. -/
theorem conj_limit {P : ℕ → ℂ → ℂ} {g : ℂ → ℂ} (hP : TendstoLocallyUniformly P g atTop)
    (hreal : ∀ n s, P n ((starRingEnd ℂ) s) = (starRingEnd ℂ) (P n s)) (s : ℂ) :
    g ((starRingEnd ℂ) s) = (starRingEnd ℂ) (g s) := by
  have hPu := tendstoLocallyUniformlyOn_univ.mpr hP
  have h1 : Tendsto (fun n => P n ((starRingEnd ℂ) s)) atTop (𝓝 (g ((starRingEnd ℂ) s))) :=
    hPu.tendsto_at (Set.mem_univ _)
  have h2 : Tendsto (fun n => (starRingEnd ℂ) (P n s)) atTop (𝓝 ((starRingEnd ℂ) (g s))) :=
    (Complex.continuous_conj.tendsto _).comp (hPu.tendsto_at (Set.mem_univ s))
  simp_rw [hreal] at h1
  exact tendsto_nhds_unique h1 h2

/-- **Purity by parity passes to limits.** A locally uniform limit `g ≢ 0` of real entire functions,
each with at most one zero right of the line, has at most one zero right of the line, and it is
real. -/
theorem im_eq_zero_of_limit_of_indexOne {P : ℕ → ℂ → ℂ} {g : ℂ → ℂ}
    (hP : TendstoLocallyUniformly P g atTop) (hPd : ∀ n, Differentiable ℂ (P n))
    (hg : Differentiable ℂ g) {a : ℂ} (ha : g a ≠ 0)
    (hreal : ∀ n s, P n ((starRingEnd ℂ) s) = (starRingEnd ℂ) (P n s))
    (hsub : ∀ᶠ n in atTop, {u | u ∈ rightHalf ∧ P n u = 0}.Subsingleton) :
    {u | u ∈ rightHalf ∧ g u = 0}.Subsingleton ∧
      ∀ s ∈ rightHalf, g s = 0 → s.im = 0 := by
  have hs := zeros_subsingleton_of_tendstoLocallyUniformly isOpen_rightHalf hP hPd hg ha hsub
  refine ⟨hs, fun s hsr hz => ?_⟩
  have hconj : g ((starRingEnd ℂ) s) = 0 := by rw [conj_limit hP hreal, hz, map_zero]
  have heq : s = (starRingEnd ℂ) s := hs ⟨hsr, hz⟩ ⟨conj_mem_rightHalf hsr, hconj⟩
  exact Complex.conj_eq_iff_im.mp heq.symm

/-- **RH is membership of `ξ` in the closure of the index-one class.** The Riemann hypothesis holds
iff `ξ` is a locally uniform limit of real entire functions each with at most one zero right of the
line. -/
theorem riemannHypothesis_iff_limit_of_indexOne :
    RiemannHypothesis ↔ ∃ P : ℕ → ℂ → ℂ, (∀ n, Differentiable ℂ (P n)) ∧
      TendstoLocallyUniformly P xi atTop ∧
      (∀ n s, P n ((starRingEnd ℂ) s) = (starRingEnd ℂ) (P n s)) ∧
      ∀ n, {u | u ∈ rightHalf ∧ P n u = 0}.Subsingleton := by
  constructor
  · intro hRH
    have hhalf := riemannHypothesis_iff_xi_zero_re_eq_half.mp hRH
    have hconst : TendstoLocallyUniformly (fun _ : ℕ => xi) xi atTop := fun u hu x =>
      ⟨Set.univ, Filter.univ_mem, Eventually.of_forall fun _ y _ => refl_mem_uniformity hu⟩
    refine ⟨fun _ => xi, fun _ => xi_differentiable, hconst, fun _ s => xi_conj s, fun _ => ?_⟩
    rintro u ⟨hu, hz⟩ v -
    have h1 : (1 : ℝ) / 2 < u.re := hu
    rw [hhalf u hz] at h1
    exact absurd h1 (lt_irrefl _)
  · rintro ⟨P, hPd, hP, hreal, hsub⟩
    have hx0 : xi 0 ≠ 0 := by
      rw [xi_zero]
      norm_num
    obtain ⟨-, hreal'⟩ := im_eq_zero_of_limit_of_indexOne hP hPd xi_differentiable hx0 hreal
      (Eventually.of_forall hsub)
    rw [riemannHypothesis_iff_xiZeroHalfPlaneBound_zero]
    intro ρ hρ
    by_contra hgt
    have hmem : ρ ∈ rightHalf := by
      show (1 : ℝ) / 2 < ρ.re
      linarith [not_le.mp hgt]
    have him := hreal' ρ hmem hρ
    -- a real zero contradicts `ξ > 0` on the real axis
    have hρreal : ρ = (ρ.re : ℂ) := Complex.ext (by simp) (by simp [him])
    have hpos := XiGlobalKummer.xi_real_pos ρ.re
    rw [← hρreal, hρ] at hpos
    simp at hpos

/-! ### Any index -/

/-- **The index cannot jump up in a limit, at any index.** If eventually every `P n` has at most
`κ` zeros in the open set `U`, the locally uniform limit `g ≢ 0` has at most `κ` zeros in `U`:
`κ + 1` zeros of `g` have disjoint balls inside `U`, and each ball eventually contains a zero of
`P n`. -/
theorem encard_zeros_le_of_tendstoLocallyUniformly {P : ℕ → ℂ → ℂ} {g : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hP : TendstoLocallyUniformly P g atTop) (hPd : ∀ n, Differentiable ℂ (P n))
    (hg : Differentiable ℂ g) {a : ℂ} (ha : g a ≠ 0) {κ : ℕ}
    (hκ : ∀ᶠ n in atTop, {u | u ∈ U ∧ P n u = 0}.encard ≤ κ) :
    {u | u ∈ U ∧ g u = 0}.encard ≤ κ := by
  classical
  by_contra hcon
  obtain ⟨T, hTsub, hTcard⟩ :=
    Set.exists_subset_encard_eq (Order.add_one_le_of_lt (not_le.mp hcon))
  have hTcard' : T.encard = ((κ + 1 : ℕ) : ℕ∞) := by
    rw [hTcard]
    push_cast
    rfl
  have hTfin : T.Finite := Set.finite_of_encard_eq_coe hTcard'
  have hTne : hTfin.toFinset.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    have hc := hTfin.encard_eq_coe_toFinset_card
    rw [hTcard', h, Finset.card_empty] at hc
    have : κ + 1 = 0 := by exact_mod_cast hc
    omega
  have hrad : ∀ z ∈ T, ∃ r > 0, ball z r ⊆ U := fun z hz =>
    Metric.isOpen_iff.mp hU z (hTsub hz).1
  choose! rU hrU0 hrU using hrad
  -- one radius inside `U` at every point and separating the points
  obtain ⟨R, hR⟩ : ∃ R : Finset ℝ, R = hTfin.toFinset.image rU ∪
      ((hTfin.toFinset ×ˢ hTfin.toFinset).filter fun p => p.1 ≠ p.2).image
        (fun p => dist p.1 p.2 / 2) := ⟨_, rfl⟩
  have hRne : R.Nonempty := by
    rw [hR]
    exact (hTne.image rU).mono Finset.subset_union_left
  have hr0 : 0 < R.min' hRne := by
    rw [Finset.lt_min'_iff]
    intro x hx
    rw [hR] at hx
    rcases Finset.mem_union.mp hx with h | h
    · obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp h
      exact hrU0 z (hTfin.mem_toFinset.mp hz)
    · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp h
      exact div_pos (dist_pos.mpr (Finset.mem_filter.mp hp).2) two_pos
  have hrle : ∀ z ∈ T, R.min' hRne ≤ rU z := by
    intro z hz
    refine Finset.min'_le _ _ ?_
    rw [hR]
    exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (hTfin.mem_toFinset.mpr hz))
  have hrsep : ∀ z ∈ T, ∀ z' ∈ T, z ≠ z' → 2 * R.min' hRne ≤ dist z z' := by
    intro z hz z' hz' hne
    have hmem : dist z z' / 2 ∈ R := by
      rw [hR]
      exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(z, z'), Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨hTfin.mem_toFinset.mpr hz, hTfin.mem_toFinset.mpr hz'⟩, hne⟩,
        rfl⟩)
    have := Finset.min'_le _ _ hmem
    linarith
  -- eventually every ball contains a zero of `P n`
  have hev : ∀ᶠ n in atTop, ∀ z ∈ hTfin.toFinset, ∃ u ∈ ball z (R.min' hRne), P n u = 0 := by
    rw [Filter.eventually_all_finset]
    intro z hz
    exact FiniteFreeProbability.eventually_exists_zero_of_tendstoLocallyUniformly hP hPd hg ha
      (hTsub (hTfin.mem_toFinset.mp hz)).2 hr0
  obtain ⟨n, hn, hcount⟩ := (hev.and hκ).exists
  choose! u hu hzero using hn
  have hinj : Set.InjOn u T := by
    intro z hz z' hz' huz
    by_contra hne
    have h1 : dist (u z) z < R.min' hRne := mem_ball.mp (hu z (hTfin.mem_toFinset.mpr hz))
    have h2 : dist (u z') z' < R.min' hRne := mem_ball.mp (hu z' (hTfin.mem_toFinset.mpr hz'))
    rw [← huz] at h2
    have htri : dist z z' ≤ dist z (u z) + dist (u z) z' := dist_triangle _ _ _
    rw [dist_comm z (u z)] at htri
    have := hrsep z hz z' hz' hne
    linarith
  have hsub : u '' T ⊆ {v | v ∈ U ∧ P n v = 0} := by
    rintro _ ⟨z, hz, rfl⟩
    have hzT := hTfin.mem_toFinset.mpr hz
    exact ⟨hrU z hz (Metric.ball_subset_ball (hrle z hz) (hu z hzT)), hzero z hzT⟩
  have h2 := Set.encard_le_encard hsub
  rw [hinj.encard_image, hTcard'] at h2
  have h3 : ((κ + 1 : ℕ) : ℕ∞) ≤ (κ : ℕ∞) := h2.trans hcount
  have h4 : κ + 1 ≤ κ := by exact_mod_cast h3
  omega

/-- **A finite index is closed in the limit.** If `ξ` is a locally uniform limit of entire functions
each with at most `κ` zeros right of the line, then `ξ` has at most `κ` zeros right of the line. -/
theorem encard_xi_zeros_le_of_limit {P : ℕ → ℂ → ℂ} (hPd : ∀ n, Differentiable ℂ (P n))
    (hP : TendstoLocallyUniformly P xi atTop) {κ : ℕ}
    (hκ : ∀ᶠ n in atTop, {u | u ∈ rightHalf ∧ P n u = 0}.encard ≤ κ) :
    {u | u ∈ rightHalf ∧ xi u = 0}.encard ≤ κ := by
  have hx0 : xi 0 ≠ 0 := by
    rw [xi_zero]
    norm_num
  exact encard_zeros_le_of_tendstoLocallyUniformly isOpen_rightHalf hP hPd xi_differentiable hx0 hκ

end GaloisForLFunctions.InfiniteRankPurityTheory
