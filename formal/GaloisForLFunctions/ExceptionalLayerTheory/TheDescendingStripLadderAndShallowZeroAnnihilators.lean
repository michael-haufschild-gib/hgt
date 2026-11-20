import GaloisForLFunctions.ExceptionalLayerTheory.TheHeightErrorOfTheHadamardThreshold

/-!
# The descending strip-gap ladder, shallow-preserving zero annihilators, and quartet moment obstructions

When a zero configuration approaches the critical line (`ApproachesLine Z`) yet fails to land
(`¬ LandingLaw Z`), its off-line geometry discretizes into an explicit countable ladder of vertical
zero-free strips, while finite Dirichlet polynomials isolate shallow off-line layers cleanly:

* **Strict descending strip-gap ladder (`exists_max_depth_below_and_zero_free_strip`,
  `exists_descending_strip_ladder_of_not_landing`, `zeta_descending_strip_ladder_of_not_landing`,
  `topRightOrdinate_eq_on_zero_free_strip`).** Under `¬ LandingLaw Z`, there exist `δ : ℕ → ℝ` and
  `ρ : ℕ → ℂ` with `StrictAnti δ`, `0 < δ n`, `Tendsto δ atTop (𝓝 0)`, `ρ n ∈ rightOf Z 0`,
  `Re (ρ n) = 1 / 2 + δ n`, `Re z ≤ 1 / 2 + δ 0` for all `z ∈ Z`, and **no** zeros of `Z` at any
  height in `(1 / 2 + δ (n + 1), 1 / 2 + δ n)` — exhausting all off-line real parts right of `1 / 2`.
  For `ζ`, `topRightOrdinate` is constant across each strip `[1 / 2 + δ (n + 1), 1 / 2 + δ n)`.
* **Shallow-preserving Dirichlet-polynomial zero annihilators (`dirichletZeroAnnihilator`,
  `exists_deep_zero_annihilator_of_zerosApproachLine`).** Under `ZerosApproachLine`, for every
  `ε > 0` a finite product `∏_{ρ ∈ L} (1 - 2^{ρ - s})` is entire, vanishes at every zero of `ζ` in
  `Re s ≥ 1 / 2 + ε / 2`, is uniformly bounded on every right half-plane `Re s ≥ σ₀`, and satisfies
  `‖M_L(s)‖ ≥ (2^{ε/4} - 1)^{|L|} > 0` uniformly on `Re s ≤ 1 / 2 + ε / 4`.
* **Ki–Kim–Lee Gaussian saddle confinement (`kiKimLee_saddle_in_strip_of_healing_time`).** At
  healing time `0 < t ≤ C δ²` and prime cutoff `2π < X` with `δ² log(X / (2π)) < 1 / (2C)`, the
  Gaussian saddle `1 / 2 + t log(X / (2π))` lies strictly in `(1 / 2, 1)`.
* **Lehmer-pair to off-line quartet Newton obstruction (`lehmer_quartet_moment_obstruction`).** Any
  off-line quartet `(±γ ± iδ)` (`δ ≠ 0`) matching the second moment of a real Lehmer pair
  `(±(γ̄ ± η))` has root-product residual `+4 (γ̄² + δ²)(η² + δ²) > 0` and fourth-moment residual
  `-16 (γ̄² + δ²)(η² + δ²) < 0`.
-/

open Complex Set Filter Topology Zeta23
open RHTower RHTower.BacklundConverse RHTower.LindelofSparse
open GaloisForLFunctions.ZeroConfigurationGeometry.ConfigAbscissa
open GaloisForLFunctions.ZeroConfigurationGeometry.ZetaAbscissa

noncomputable section

namespace GaloisForLFunctions.ExceptionalLayerTheory

/-! ### Part 1: Strict descending strip-gap ladder under `¬ LandingLaw` -/

/-- Below any positive depth `δ > 0`, a configuration that approaches the critical line without
landing attains a maximum off-line depth `δ' ∈ (0, δ)` and is completely zero-free in the open
vertical strip `1 / 2 + δ' < Re s < 1 / 2 + δ` across all heights. -/
theorem exists_max_depth_below_and_zero_free_strip {Z : ZeroConfig}
    (hA : ApproachesLine Z) (hInf : ¬ (rightOf Z 0).Finite) {δ : ℝ} (hδ : 0 < δ) :
    ∃ δ' : ℝ, ∃ ρ₁ : ℂ, 0 < δ' ∧ δ' < δ ∧ ρ₁ ∈ rightOf Z 0 ∧ ρ₁.re = 1 / 2 + δ' ∧
      ∀ z ∈ Z.carrier, ¬ (1 / 2 + δ' < z.re ∧ z.re < 1 / 2 + δ) := by
  set S : Set ℂ := {z | z ∈ rightOf Z 0 ∧ z.re < 1 / 2 + δ}
  have hS_ne : S.Nonempty := by
    by_contra hS
    rw [not_nonempty_iff_eq_empty] at hS
    apply hInf ((hA (δ / 2) (half_pos hδ)).subset fun z hz => ?_)
    have hnot : z ∉ S := by rw [hS]; exact not_mem_empty z
    refine ⟨hz.1, ?_⟩
    by_contra hle
    exact hnot ⟨hz, by linarith⟩
  obtain ⟨ρ₀, hρ₀_right, hρ₀_lt⟩ := hS_ne
  have hρ₀_gt : 1 / 2 < ρ₀.re := by linarith [hρ₀_right.2]
  set η : ℝ := (ρ₀.re - 1 / 2) / 2
  have hη : 0 < η := by dsimp [η]; linarith
  set F : Set ℂ := {z | z ∈ S ∧ 1 / 2 + η < z.re}
  have hF_fin : F.Finite :=
    (hA η hη).subset fun z hz => ⟨hz.1.1.1, hz.2⟩
  have hρ₀F : ρ₀ ∈ F := ⟨⟨hρ₀_right, hρ₀_lt⟩, by dsimp [η]; linarith⟩
  obtain ⟨ρ₁, hρ₁F, hmax⟩ := hF_fin.exists_maximalFor Complex.re F ⟨ρ₀, hρ₀F⟩
  have hρ₁_gt : 1 / 2 + η < ρ₁.re := hρ₁F.2
  have hρ₁_lt : ρ₁.re < 1 / 2 + δ := hρ₁F.1.2
  refine ⟨ρ₁.re - 1 / 2, ρ₁, by linarith, by linarith, hρ₁F.1.1, by ring, ?_⟩
  intro z hz ⟨hlo, hhi⟩
  have hzS : z ∈ S := ⟨⟨hz, by linarith⟩, hhi⟩
  have hzF : z ∈ F := ⟨hzS, by linarith⟩
  have hle : z.re ≤ ρ₁.re := hmax hzF (by linarith)
  linarith

private noncomputable def stripLadderStep (Z : ZeroConfig) (hA : ApproachesLine Z)
    (hInf : ¬ (rightOf Z 0).Finite) (δ : ℝ) : ℝ × ℂ :=
  if h : 0 < δ then
    let hEx := exists_max_depth_below_and_zero_free_strip hA hInf h
    (Classical.choose hEx, Classical.choose (Classical.choose_spec hEx))
  else (0, 0)

private lemma stripLadderStep_spec {Z : ZeroConfig} (hA : ApproachesLine Z)
    (hInf : ¬ (rightOf Z 0).Finite) {δ : ℝ} (hδ : 0 < δ) :
    let p := stripLadderStep Z hA hInf δ
    0 < p.1 ∧ p.1 < δ ∧ p.2 ∈ rightOf Z 0 ∧ p.2.re = 1 / 2 + p.1 ∧
      ∀ z ∈ Z.carrier, ¬ (1 / 2 + p.1 < z.re ∧ z.re < 1 / 2 + δ) := by
  dsimp only [stripLadderStep]
  rw [dif_pos hδ]
  exact Classical.choose_spec (Classical.choose_spec
    (exists_max_depth_below_and_zero_free_strip hA hInf hδ))

/-- **The descending strip-gap ladder.** Whenever `LandingLaw Z` fails, the off-line real parts of
`Z` right of `1 / 2` form a strictly decreasing sequence `1 / 2 + δ n → 1 / 2` separated by open
all-height zero-free vertical strips `(1 / 2 + δ (n + 1), 1 / 2 + δ n)`. -/
theorem exists_descending_strip_ladder_of_not_landing {Z : ZeroConfig} (hNL : ¬ LandingLaw Z) :
    ∃ (δ : ℕ → ℝ) (ρ : ℕ → ℂ),
      StrictAnti δ ∧
      (∀ n, 0 < δ n) ∧
      Tendsto δ atTop (𝓝 0) ∧
      (∀ n, ρ n ∈ rightOf Z 0 ∧ (ρ n).re = 1 / 2 + δ n) ∧
      (∀ z ∈ Z.carrier, z.re ≤ 1 / 2 + δ 0) ∧
      (∀ n, ∀ z ∈ Z.carrier, ¬ (1 / 2 + δ (n + 1) < z.re ∧ z.re < 1 / 2 + δ n)) ∧
      (∀ z ∈ rightOf Z 0, ∃ n, z.re = 1 / 2 + δ n) := by
  classical
  rw [LandingLaw, not_imp] at hNL
  obtain ⟨hA, hInf⟩ := hNL
  let seq : ℕ → ℝ × ℂ := fun n => Nat.rec (stripLadderStep Z hA hInf 1)
    (fun _ prev => stripLadderStep Z hA hInf prev.1) n
  have hpos : ∀ n, 0 < (seq n).1 := by
    intro n
    induction n with
    | zero => exact (stripLadderStep_spec hA hInf one_pos).1
    | succ n ih => exact (stripLadderStep_spec hA hInf ih).1
  let δ : ℕ → ℝ := fun n => (seq n).1
  let ρ : ℕ → ℂ := fun n => (seq n).2
  have hanti : StrictAnti δ := strictAnti_nat_of_succ_lt fun n =>
    (stripLadderStep_spec hA hInf (hpos n)).2.1
  have hρ : ∀ n, ρ n ∈ rightOf Z 0 ∧ (ρ n).re = 1 / 2 + δ n := by
    intro n
    cases n with
    | zero =>
      have hs := stripLadderStep_spec hA hInf one_pos
      exact ⟨hs.2.2.1, hs.2.2.2.1⟩
    | succ n =>
      have hs := stripLadderStep_spec hA hInf (hpos n)
      exact ⟨hs.2.2.1, hs.2.2.2.1⟩
  have htop : ∀ z ∈ Z.carrier, z.re ≤ 1 / 2 + δ 0 := by
    intro z hz
    have hs := (stripLadderStep_spec hA hInf one_pos).2.2.2.2 z hz
    have hz1 : z.re ≤ 1 := (Z.strip z hz).2
    by_contra hgt
    exact hs ⟨by linarith, by linarith⟩
  have hgap : ∀ n, ∀ z ∈ Z.carrier, ¬ (1 / 2 + δ (n + 1) < z.re ∧ z.re < 1 / 2 + δ n) :=
    fun n => (stripLadderStep_spec hA hInf (hpos n)).2.2.2.2
  have htend : Tendsto δ atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    have hex : ∃ N, δ N < ε := by
      by_contra hall
      push Not at hall
      have hinj : Function.Injective ρ := by
        intro i j hij
        have hre : (ρ i).re = (ρ j).re := congrArg Complex.re hij
        rw [(hρ i).2, (hρ j).2] at hre
        exact hanti.injective (by linarith)
      have hsub : Set.range ρ ⊆ rightOf Z (ε / 2) := by
        rintro _ ⟨n, rfl⟩
        refine ⟨(hρ n).1.1, ?_⟩
        rw [(hρ n).2]
        linarith [hall n]
      exact (Set.infinite_range_of_injective hinj) ((hA (ε / 2) (half_pos hε)).subset hsub)
    obtain ⟨N, hN⟩ := hex
    refine ⟨N, fun n hn => ?_⟩
    have hle : δ n ≤ δ N := hanti.antitone hn
    rw [Real.dist_eq, sub_zero, abs_of_pos (hpos n)]
    exact lt_of_le_of_lt hle hN
  have hexhaust : ∀ z ∈ rightOf Z 0, ∃ n, z.re = 1 / 2 + δ n := by
    intro z hz
    have hd : 0 < z.re - 1 / 2 := by linarith [hz.2]
    have hex : ∃ m, δ m < z.re - 1 / 2 :=
      (htend.eventually (gt_mem_nhds hd)).exists
    let k := Nat.find hex
    have hk_lt : δ k < z.re - 1 / 2 := Nat.find_spec hex
    rcases Nat.eq_zero_or_pos k with hkz | hkpos
    · exfalso
      have h0 : δ 0 < z.re - 1 / 2 := hkz ▸ hk_lt
      linarith [htop z hz.1]
    · refine ⟨k - 1, ?_⟩
      have hmin : ¬ δ (k - 1) < z.re - 1 / 2 := Nat.find_min hex (by omega)
      have hle : z.re ≤ 1 / 2 + δ (k - 1) := by linarith
      have hgt : 1 / 2 + δ (k - 1 + 1) < z.re := by
        rw [Nat.sub_add_cancel hkpos]
        linarith
      rcases lt_or_eq_of_le hle with hlt | heq
      · exact False.elim (hgap (k - 1) z hz.1 ⟨hgt, hlt⟩)
      · exact heq
  exact ⟨δ, ρ, hanti, hpos, htend, hρ, htop, hgap, hexhaust⟩

/-- Specialization of the descending strip-gap ladder to `ζ` under `¬ ZetaLandingLaw`. -/
theorem zeta_descending_strip_ladder_of_not_landing (hNL : ¬ ZetaLandingLaw) :
    ∃ (δ : ℕ → ℝ) (ρ : ℕ → ℂ),
      StrictAnti δ ∧
      (∀ n, 0 < δ n) ∧
      Tendsto δ atTop (𝓝 0) ∧
      (∀ n, ρ n ∈ rightOf zetaZeroConfig 0 ∧ (ρ n).re = 1 / 2 + δ n) ∧
      (∀ z ∈ zetaZeroConfig.carrier, z.re ≤ 1 / 2 + δ 0) ∧
      (∀ n, ∀ z ∈ zetaZeroConfig.carrier, ¬ (1 / 2 + δ (n + 1) < z.re ∧ z.re < 1 / 2 + δ n)) ∧
      (∀ z ∈ rightOf zetaZeroConfig 0, ∃ n, z.re = 1 / 2 + δ n) :=
  exists_descending_strip_ladder_of_not_landing (mt zetaLandingLaw_iff_landingLaw.mpr hNL)

/-- On any all-height zero-free open vertical strip `(a, b)` of `ζ`, `topRightOrdinate` is
identically constant across the half-open interval `[a, b)`. -/
theorem topRightOrdinate_eq_on_zero_free_strip {a b σ₁ σ₂ : ℝ}
    (hstrip : ∀ z ∈ zetaZeroConfig.carrier, ¬ (a < z.re ∧ z.re < b))
    (ha₁ : a ≤ σ₁) (hb₁ : σ₁ < b) (ha₂ : a ≤ σ₂) (hb₂ : σ₂ < b) :
    topRightOrdinate σ₁ = topRightOrdinate σ₂ := by
  unfold topRightOrdinate
  congr 2
  ext q
  simp only [mem_setOf_eq]
  have hq : (q.1 : ℂ) ∈ zetaZeroConfig.carrier :=
    CrossRouteReceiverBridges.xiZeroCopy_mem_zetaZeroConfig_carrier q
  constructor <;> intro h
  · have hnot : ¬ (q.1 : ℂ).re < b := fun hlt => hstrip (q.1 : ℂ) hq ⟨lt_of_le_of_lt ha₁ h, hlt⟩
    linarith
  · have hnot : ¬ (q.1 : ℂ).re < b := fun hlt => hstrip (q.1 : ℂ) hq ⟨lt_of_le_of_lt ha₂ h, hlt⟩
    linarith

/-! ### Part 2: Shallow-preserving Dirichlet-polynomial zero annihilators -/

/-- Finite Dirichlet polynomial `∏_{ρ ∈ L} (1 - 2^{ρ - s}) = ∏_{ρ ∈ L} (1 - exp((log 2)(ρ - s)))`. -/
def dirichletZeroAnnihilator (L : List ℂ) (s : ℂ) : ℂ :=
  (L.map fun ρ => 1 - Complex.exp ((Real.log 2 : ℂ) * (ρ - s))).prod

theorem dirichletZeroAnnihilator_eq_prod_cpow (L : List ℂ) (s : ℂ) :
    dirichletZeroAnnihilator L s = (L.map fun ρ => 1 - (2 : ℂ) ^ (ρ - s)).prod := by
  unfold dirichletZeroAnnihilator
  congr 1
  refine List.map_congr_left fun ρ _ => ?_
  rw [Complex.cpow_def_of_ne_zero two_ne_zero]
  have hlog : Complex.log 2 = (Real.log 2 : ℂ) := by
    rw [← Complex.ofReal_ofNat, Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2)]
  rw [hlog]

/-- `dirichletZeroAnnihilator L` is entire on `ℂ`. -/
theorem differentiable_dirichletZeroAnnihilator (L : List ℂ) :
    Differentiable ℂ (dirichletZeroAnnihilator L) := by
  induction L with
  | nil =>
    unfold dirichletZeroAnnihilator
    simpa using differentiable_const (1 : ℂ)
  | cons ρ tail ih =>
    have hcons : dirichletZeroAnnihilator (ρ :: tail) =
        fun s => (1 - Complex.exp ((Real.log 2 : ℂ) * (ρ - s))) * dirichletZeroAnnihilator tail s := by
      funext s
      simp [dirichletZeroAnnihilator]
    rw [hcons]
    have hsub : Differentiable ℂ (fun s : ℂ => (Real.log 2 : ℂ) * (ρ - s)) :=
      (differentiable_const ρ |>.sub differentiable_id).const_mul _
    exact (differentiable_const (1 : ℂ) |>.sub hsub.cexp).mul ih

/-- `dirichletZeroAnnihilator L` vanishes at every point `ρ ∈ L`. -/
theorem dirichletZeroAnnihilator_eq_zero_of_mem {L : List ℂ} {ρ : ℂ} (hρ : ρ ∈ L) :
    dirichletZeroAnnihilator L ρ = 0 := by
  unfold dirichletZeroAnnihilator
  refine List.prod_eq_zero (List.mem_map.mpr ⟨ρ, hρ, ?_⟩)
  simp

private lemma norm_exp_log_two_mul_sub (ρ s : ℂ) :
    ‖Complex.exp ((Real.log 2 : ℂ) * (ρ - s))‖ = (2 : ℝ) ^ (ρ.re - s.re) := by
  rw [Complex.norm_exp]
  have hre : ((Real.log 2 : ℂ) * (ρ - s)).re = Real.log 2 * (ρ.re - s.re) := by
    simp [Complex.mul_re]
  rw [hre, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]

/-- Uniform upper bound for `dirichletZeroAnnihilator L` on any closed right half-plane `Re s ≥ σ₀`. -/
theorem norm_dirichletZeroAnnihilator_le_of_re_ge (L : List ℂ) {σ₀ : ℝ} {s : ℂ}
    (hs : σ₀ ≤ s.re) :
    ‖dirichletZeroAnnihilator L s‖ ≤ (L.map fun ρ => 1 + (2 : ℝ) ^ (ρ.re - σ₀)).prod := by
  induction L with
  | nil => simp [dirichletZeroAnnihilator]
  | cons ρ tail ih =>
    simp only [dirichletZeroAnnihilator, List.map_cons, List.prod_cons, norm_mul]
    have hfac : ‖1 - Complex.exp ((Real.log 2 : ℂ) * (ρ - s))‖ ≤ 1 + (2 : ℝ) ^ (ρ.re - σ₀) := by
      calc ‖(1 : ℂ) - Complex.exp ((Real.log 2 : ℂ) * (ρ - s))‖
          ≤ ‖(1 : ℂ)‖ + ‖Complex.exp ((Real.log 2 : ℂ) * (ρ - s))‖ := norm_sub_le _ _
        _ = 1 + (2 : ℝ) ^ (ρ.re - s.re) := by rw [norm_one, norm_exp_log_two_mul_sub]
        _ ≤ 1 + (2 : ℝ) ^ (ρ.re - σ₀) :=
          add_le_add_right
            (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)) 1
    have hprod_nonneg : 0 ≤ (tail.map fun z : ℂ => 1 + (2 : ℝ) ^ (z.re - σ₀)).prod :=
      List.prod_nonneg fun x hx => by
        obtain ⟨z, _, rfl⟩ := List.mem_map.mp hx
        positivity
    exact mul_le_mul hfac ih (norm_nonneg _) (by positivity)

/-- Uniform positive lower bound for `dirichletZeroAnnihilator L` on any closed left half-plane
`Re s ≤ σ₁` strictly left of `L` (`σ₁ < σ₂ ≤ Re ρ` for all `ρ ∈ L`). -/
theorem norm_dirichletZeroAnnihilator_ge_of_re_le {L : List ℂ} {σ₁ σ₂ : ℝ} (hσ : σ₁ < σ₂)
    (hL : ∀ ρ ∈ L, σ₂ ≤ ρ.re) {s : ℂ} (hs : s.re ≤ σ₁) :
    ((2 : ℝ) ^ (σ₂ - σ₁) - 1) ^ L.length ≤ ‖dirichletZeroAnnihilator L s‖ := by
  have hbase_pos : 0 < (2 : ℝ) ^ (σ₂ - σ₁) - 1 := by
    have hgt : (1 : ℝ) < (2 : ℝ) ^ (σ₂ - σ₁) :=
      Real.one_lt_rpow (by norm_num) (by linarith)
    linarith
  induction L with
  | nil => simp [dirichletZeroAnnihilator]
  | cons ρ tail ih =>
    simp only [dirichletZeroAnnihilator, List.map_cons, List.prod_cons, List.length_cons,
      pow_succ', norm_mul]
    have hρ : σ₂ ≤ ρ.re := hL ρ (List.mem_cons_self ..)
    have htail := ih (fun z hz => hL z (List.mem_cons_of_mem _ hz))
    have hrev : ‖Complex.exp ((Real.log 2 : ℂ) * (ρ - s))‖ - 1 ≤
        ‖(1 : ℂ) - Complex.exp ((Real.log 2 : ℂ) * (ρ - s))‖ := by
      have h := norm_sub_norm_le (Complex.exp ((Real.log 2 : ℂ) * (ρ - s))) 1
      rwa [norm_sub_rev, norm_one] at h
    have hfac : (2 : ℝ) ^ (σ₂ - σ₁) - 1 ≤
        ‖(1 : ℂ) - Complex.exp ((Real.log 2 : ℂ) * (ρ - s))‖ := by
      refine le_trans ?_ hrev
      rw [norm_exp_log_two_mul_sub]
      have hexp : (2 : ℝ) ^ (σ₂ - σ₁) ≤ (2 : ℝ) ^ (ρ.re - s.re) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      linarith
    exact mul_le_mul hfac htail (pow_nonneg hbase_pos.le _)
      (norm_nonneg _)

/-- **Deep-zero clearing without shallow-zero loss under `ZerosApproachLine`.** For every `ε > 0`,
there exists a finite list `L` of zeros of `ζ` in `Re s ≥ 1 / 2 + ε / 2` whose Dirichlet polynomial
`dirichletZeroAnnihilator L` vanishes on all zeros of `ζ` with `Re ρ ≥ 1 / 2 + ε / 2` while
remaining bounded below by `(2^{ε / 4} - 1)^{|L|} > 0` across `Re s ≤ 1 / 2 + ε / 4`. -/
theorem exists_deep_zero_annihilator_of_zerosApproachLine (hZ : ZerosApproachLine)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ L : List ℂ,
      (∀ ρ ∈ zetaZeroConfig.carrier, 1 / 2 + ε / 2 ≤ ρ.re → dirichletZeroAnnihilator L ρ = 0) ∧
      0 < ((2 : ℝ) ^ (ε / 4) - 1) ^ L.length ∧
      (∀ s : ℂ, s.re ≤ 1 / 2 + ε / 4 →
        ((2 : ℝ) ^ (ε / 4) - 1) ^ L.length ≤ ‖dirichletZeroAnnihilator L s‖) := by
  classical
  have hA : ApproachesLine zetaZeroConfig := zetaZeroConfig_approachesLine_iff.mpr hZ
  set D : Set ℂ := {ρ | ρ ∈ zetaZeroConfig.carrier ∧ 1 / 2 + ε / 2 ≤ ρ.re}
  have hD_fin : D.Finite :=
    (hA (ε / 4) (by positivity)).subset fun ρ hρ => ⟨hρ.1, by linarith [hρ.2]⟩
  let L : List ℂ := hD_fin.toFinset.toList
  have hmem : ∀ ρ : ℂ, ρ ∈ L ↔ ρ ∈ D := fun ρ => by
    simp [L, Set.Finite.mem_toFinset]
  have hgt : 0 < (2 : ℝ) ^ (ε / 4) - 1 := by
    have h1 : (1 : ℝ) < (2 : ℝ) ^ (ε / 4) := Real.one_lt_rpow (by norm_num) (by positivity)
    linarith
  refine ⟨L, fun ρ hρ hre => dirichletZeroAnnihilator_eq_zero_of_mem ((hmem ρ).mpr ⟨hρ, hre⟩),
    pow_pos hgt _, fun s hs => ?_⟩
  have hdiff : (1 / 2 + ε / 2) - (1 / 2 + ε / 4) = ε / 4 := by ring
  rw [← hdiff]
  exact norm_dirichletZeroAnnihilator_ge_of_re_le (by linarith)
    (fun ρ hρ => ((hmem ρ).mp hρ).2) hs

/-! ### Part 3: Ki–Kim–Lee Gaussian saddle confinement in the critical strip -/

/-- When the healing time satisfies `0 < t ≤ C δ²` (`C > 0`) and the prime cutoff `2π < X` obeys
`δ² log(X / (2π)) < 1 / (2C)`, the Gaussian saddle abscissa `1 / 2 + t log(X / (2π))` lies strictly
inside `(1 / 2, 1)`. -/
theorem kiKimLee_saddle_in_strip_of_healing_time {C t δ X : ℝ} (hC : 0 < C) (ht0 : 0 < t)
    (ht : t ≤ C * δ ^ 2) (hX : 2 * Real.pi < X)
    (hcut : δ ^ 2 * Real.log (X / (2 * Real.pi)) < 1 / (2 * C)) :
    1 / 2 < 1 / 2 + t * Real.log (X / (2 * Real.pi)) ∧
      1 / 2 + t * Real.log (X / (2 * Real.pi)) < 1 := by
  have hpi : 0 < 2 * Real.pi := by positivity
  have hquot : 1 < X / (2 * Real.pi) := (one_lt_div hpi).mpr hX
  have hlog : 0 < Real.log (X / (2 * Real.pi)) := Real.log_pos hquot
  refine ⟨by nlinarith [mul_pos ht0 hlog], ?_⟩
  have hle : t * Real.log (X / (2 * Real.pi)) ≤ C * (δ ^ 2 * Real.log (X / (2 * Real.pi))) := by
    nlinarith [mul_le_mul_of_nonneg_right ht hlog.le]
  have hlt : C * (δ ^ 2 * Real.log (X / (2 * Real.pi))) < C * (1 / (2 * C)) :=
    mul_lt_mul_of_pos_left hcut hC
  have hcanc : C * (1 / (2 * C)) = 1 / 2 := by field_simp
  linarith

/-! ### Part 4: Lehmer-pair to off-line quartet Newton moment obstruction -/

/-- **Exact 4-root Newton moment obstruction.** Whenever a real Lehmer pair `(±(γ̄ + η), ±(γ̄ - η))`
and an off-line quartet `(±γ ± iδ)` share the same second moment
`(γ̄ + η)² + (γ̄ - η)² = 2 (γ² - δ²)`:
1. the root-product residual `(γ² + δ²)² - (γ̄ + η)² (γ̄ - η)²` equals `4 (γ̄² + δ²)(η² + δ²)`;
2. the fourth-moment residual `4 (γ⁴ - 6 γ² δ² + δ⁴) - 2 ((γ̄ + η)⁴ + (γ̄ - η)⁴)` equals
   `-16 (γ̄² + δ²)(η² + δ²)`;
3. for every nonzero off-line depth `δ ≠ 0`, both residuals are strictly nonzero with opposite
   signs. -/
theorem lehmer_quartet_moment_obstruction {γ δ γbar η : ℝ}
    (hm2 : (γbar + η) ^ 2 + (γbar - η) ^ 2 = 2 * (γ ^ 2 - δ ^ 2)) :
    ((γ ^ 2 + δ ^ 2) ^ 2 - (γbar + η) ^ 2 * (γbar - η) ^ 2 =
        4 * (γbar ^ 2 + δ ^ 2) * (η ^ 2 + δ ^ 2)) ∧
      (4 * (γ ^ 4 - 6 * γ ^ 2 * δ ^ 2 + δ ^ 4) - 2 * ((γbar + η) ^ 4 + (γbar - η) ^ 4) =
        -16 * (γbar ^ 2 + δ ^ 2) * (η ^ 2 + δ ^ 2)) ∧
      (δ ≠ 0 → 0 < (γ ^ 2 + δ ^ 2) ^ 2 - (γbar + η) ^ 2 * (γbar - η) ^ 2 ∧
        4 * (γ ^ 4 - 6 * γ ^ 2 * δ ^ 2 + δ ^ 4) < 2 * ((γbar + η) ^ 4 + (γbar - η) ^ 4)) := by
  have hγ2 : γ ^ 2 = γbar ^ 2 + η ^ 2 + δ ^ 2 := by linarith
  have he4 : (γ ^ 2 + δ ^ 2) ^ 2 - (γbar + η) ^ 2 * (γbar - η) ^ 2 =
      4 * (γbar ^ 2 + δ ^ 2) * (η ^ 2 + δ ^ 2) := by
    linear_combination (2 * γ ^ 2 + 2 * γbar ^ 2 + 2 * η ^ 2 + 6 * δ ^ 2) * hγ2
  have hp4 : 4 * (γ ^ 4 - 6 * γ ^ 2 * δ ^ 2 + δ ^ 4) - 2 * ((γbar + η) ^ 4 + (γbar - η) ^ 4) =
      -16 * (γbar ^ 2 + δ ^ 2) * (η ^ 2 + δ ^ 2) := by
    linear_combination 4 * (γ ^ 2 + γbar ^ 2 + η ^ 2 - 5 * δ ^ 2) * hγ2
  refine ⟨he4, hp4, fun hδ => ?_⟩
  have hδ2 : 0 < δ ^ 2 := sq_pos_of_ne_zero hδ
  have hpos : 0 < (γbar ^ 2 + δ ^ 2) * (η ^ 2 + δ ^ 2) :=
    mul_pos (by positivity) (by positivity)
  exact ⟨by linarith, by linarith⟩

#print axioms exists_max_depth_below_and_zero_free_strip
#print axioms exists_descending_strip_ladder_of_not_landing
#print axioms zeta_descending_strip_ladder_of_not_landing
#print axioms topRightOrdinate_eq_on_zero_free_strip
#print axioms differentiable_dirichletZeroAnnihilator
#print axioms norm_dirichletZeroAnnihilator_le_of_re_ge
#print axioms norm_dirichletZeroAnnihilator_ge_of_re_le
#print axioms exists_deep_zero_annihilator_of_zerosApproachLine
#print axioms kiKimLee_saddle_in_strip_of_healing_time
#print axioms lehmer_quartet_moment_obstruction

end GaloisForLFunctions.ExceptionalLayerTheory
