import GaloisForLFunctions.RHTower.PhysicalOrdinateRiggedRecovery
import GaloisForLFunctions.RHTower.PhysicalOrdinateGraphCollapse
import GaloisForLFunctions.RHTower.Zeta23SimpleCriticalDensity
import GaloisForLFunctions.RHTower.XiSimpleCriticalSuperlinearConsumer

/-!
# Zero-density rigidity of bounded readings of the rigged source

A bounded `L : H_{-a} → ℂ` read on the rigged critical source gives the Dirichlet readout
`F(γ) = L(z_{1,γ}) = Σ_n μ(n) n^{-(a+1/2)} L(δ_n) n^{iγ}`, weighted-summable for every `η < a`
**(13)**.  Unless all its coefficients vanish, its distinct real zeros in `[0, T]` are `O(1 + T)`,
whereas the simple critical Xi ordinates up to `T` are eventually at least `T log T / (72π)`
(Alpöge–Furman's two-thirds theorem, formalized in the Zeta23 dependency).  Hence:

* **(13)** if `L(z_{1,γ}) = 0` at every positive simple critical ordinate, `L` vanishes on
  `ℓ²(squarefree)`; the same holds for bounded maps into any Hilbert space, and separately at every
  safe Euler level `σ > 1` for bounded readings of the normalized source `y_{σ,γ}`;
* **(14)** if bounded `L_j` read `z_{σ_j,γ}` convergently, `σ_j ↓ 1`, to a nonzero `F` vanishing at all
  positive simple critical ordinates, then `‖L_j‖ → ∞`.
-/

noncomputable section
set_option autoImplicit false

open Complex Filter Topology Set

namespace RHTower

open GaloisForLFunctions.HTGeometry

local notation "ℓ²ℕ" => lp (fun _ : ℕ => ℂ) 2

/-- A readout vanishing at all positive simple critical Xi ordinates has zero coefficients. -/
theorem coeff_eq_zero_of_readout_vanishes_on_simpleCritical {c : ℕ → ℂ} {η : ℝ}
    (hc : WeightedAbsSummable c η) (hη : 0 < η)
    (hvanish : ∀ t : ℝ, 0 < t → xi (linePt t) = 0 → (analyticOrderAt xi (linePt t)).toNat = 1 →
      dirichletReadout c t = 0) :
    ∀ n, 0 < n → c n = 0 := by
  by_contra hne
  push Not at hne
  obtain ⟨K, -, hK⟩ := exists_zero_count_linear hc hη hne
  refine not_linear_bound_of_superlinear (c := 1 / (72 * Real.pi)) (K := K) (m := 0)
    (by positivity) eventually_superlinear_xiSimpleCriticalZeroCount fun T hT => ?_
  rw [add_zero, ← card_xiSimpleCriticalOrdinateFinset]
  refine hK T (by linarith) _ fun t ht => ?_
  obtain ⟨ht0, htT, hxi, hsimple⟩ := mem_xiSimpleCriticalOrdinateFinset.mp ht
  exact ⟨ht0.le, htT, hvanish t ht0 hxi hsimple⟩

/-! ### Bounded scalar readings -/

/-- The expansion `L f = Σ f(n) L(δ_n)` of a bounded functional. -/
theorem hasSum_functional (L : ℓ²ℕ →L[ℂ] ℂ) (f : ℓ²ℕ) :
    HasSum (fun n => (f : ℕ → ℂ) n * L (lp.single 2 n 1)) (L f) := by
  classical
  have h := (lp.hasSum_single (E := fun _ : ℕ => ℂ) (p := 2) (by norm_num) f).mapL L
  refine h.congr_fun fun n => ?_
  have hs : lp.single (E := fun _ : ℕ => ℂ) 2 n ((f : ℕ → ℂ) n) =
      (f : ℕ → ℂ) n • lp.single (E := fun _ : ℕ => ℂ) 2 n 1 := by
    rw [← lp.single_smul, smul_eq_mul, mul_one]
  change _ = L (lp.single 2 n ((f : ℕ → ℂ) n))
  rw [hs, map_smul, smul_eq_mul]

theorem summable_norm_sq_functional (L : ℓ²ℕ →L[ℂ] ℂ) :
    Summable fun n => ‖L (lp.single 2 n 1)‖ ^ 2 := by
  classical
  set h : ℓ²ℕ := (InnerProductSpace.toDual ℂ ℓ²ℕ).symm L
  refine (summable_norm_sq_lp h).congr fun n => ?_
  rw [← InnerProductSpace.toDual_symm_apply (x := lp.single 2 n (1 : ℂ)) (y := L),
    ← inner_conj_symm, lp.inner_single_left]
  simp
  rfl

/-- **The rigged reading is a Dirichlet readout (13).** -/
theorem functional_rigged_eq_readout {a : ℝ} (ha : 0 < a) (L : ℓ²ℕ →L[ℂ] ℂ) (γ : ℝ) :
    L (riggedSource a 1 γ) =
      dirichletReadout (fun n => riggedWeight a n * L (lp.single 2 n 1)) γ := by
  have hw := weightedAbsSummable_rigged_mul (a := a) (η := 0) ha (summable_norm_sq_functional L)
  rw [dirichletReadout_ofReal hw le_rfl, GaloisForLFunctions.expSeriesCarrier]
  have h := hasSum_functional L (riggedSource a 1 γ)
  rw [← h.tsum_eq, h.summable.tsum_eq_zero_add]
  have h1 : 1 < 2 * a + 1 := by linarith
  simp only [riggedSource_apply h1, riggedCoord_one]
  have hw0 : riggedWeight a 0 = 0 := by simp [riggedWeight]
  rw [hw0, zero_mul, zero_mul, zero_add]
  refine tsum_congr fun m => ?_
  ring

theorem riggedSource_mem_squarefreeSubspace (a σ γ : ℝ) :
    riggedSource a σ γ ∈ squarefreeSubspace := by
  intro n hn
  by_cases h : 1 < 2 * a + σ
  · rw [riggedSource_apply h, riggedCoord, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hn]
    simp
  · rw [riggedSource, dif_neg h]; rfl

/-- A bounded functional vanishing on every squarefree coordinate vanishes on `ℓ²(squarefree)`. -/
theorem functional_eq_zero_on_squarefree (L : ℓ²ℕ →L[ℂ] ℂ)
    (hL : ∀ n, Squarefree n → L (lp.single 2 n 1) = 0) (f : ℓ²ℕ) (hf : f ∈ squarefreeSubspace) :
    L f = 0 := by
  rw [← (hasSum_functional L f).tsum_eq]
  refine (tsum_congr fun n => ?_).trans tsum_zero
  by_cases hn : Squarefree n
  · rw [hL n hn, mul_zero]
  · rw [hf n hn, zero_mul]

/-- **Zero-density rigidity (13).**  A bounded reading of the rigged critical source vanishing at
every positive simple critical Xi ordinate annihilates `ℓ²(squarefree)`. -/
theorem rigged_reader_vanishes {a : ℝ} (ha : 0 < a) (L : ℓ²ℕ →L[ℂ] ℂ)
    (hvanish : ∀ t : ℝ, 0 < t → xi (linePt t) = 0 → (analyticOrderAt xi (linePt t)).toNat = 1 →
      L (riggedSource a 1 t) = 0) (f : ℓ²ℕ) (hf : f ∈ squarefreeSubspace) : L f = 0 := by
  have hw := weightedAbsSummable_rigged_mul (a := a) (η := a / 2) (by linarith)
    (summable_norm_sq_functional L)
  have hcoef := coeff_eq_zero_of_readout_vanishes_on_simpleCritical hw (by positivity)
    fun t ht0 hxi hsimple => by
      rw [← functional_rigged_eq_readout ha L t]; exact hvanish t ht0 hxi hsimple
  refine functional_eq_zero_on_squarefree L (fun n hn => ?_) f hf
  have hn0 : 0 < n := Nat.pos_of_ne_zero fun h => by subst h; exact not_squarefree_zero hn
  have := hcoef n hn0
  have hwn : riggedWeight a n ≠ 0 := by
    have hn0' : (0 : ℝ) < n := by exact_mod_cast hn0
    refine mul_ne_zero ?_ (Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hn0' _).ne')
    rw [ArithmeticFunction.moebius_apply_of_squarefree hn]; simp
  exact (mul_eq_zero.mp this).resolve_left hwn

/-- **The readout dichotomy.**  A bounded rigged reading either vanishes at every real height or has
at most `K (1 + T)` distinct real zeros in `[0, T]`. -/
theorem rigged_reader_dichotomy {a : ℝ} (ha : 0 < a) (L : ℓ²ℕ →L[ℂ] ℂ) :
    (∀ γ : ℝ, L (riggedSource a 1 γ) = 0) ∨
      ∃ K : ℝ, ∀ T : ℝ, 0 ≤ T → ∀ S : Finset ℝ,
        (∀ t ∈ S, 0 ≤ t ∧ t ≤ T ∧ L (riggedSource a 1 t) = 0) → (S.card : ℝ) ≤ K * (1 + T) := by
  have hw := weightedAbsSummable_rigged_mul (a := a) (η := a / 2) (by linarith)
    (summable_norm_sq_functional L)
  by_cases hne : ∃ n, 0 < n ∧ riggedWeight a n * L (lp.single 2 n 1) ≠ 0
  · right
    obtain ⟨K, -, hK⟩ := exists_zero_count_linear hw (by positivity) hne
    refine ⟨K, fun T hT S hS => hK T hT S fun t ht => ?_⟩
    obtain ⟨h0, h1, h2⟩ := hS t ht
    exact ⟨h0, h1, by rw [← functional_rigged_eq_readout ha L t]; exact h2⟩
  · left
    push Not at hne
    intro γ
    refine functional_eq_zero_on_squarefree L (fun n hn => ?_) _
      (riggedSource_mem_squarefreeSubspace a 1 γ)
    have hn0 : 0 < n := Nat.pos_of_ne_zero fun h => by subst h; exact not_squarefree_zero hn
    have hwn : riggedWeight a n ≠ 0 := by
      have hn0' : (0 : ℝ) < n := by exact_mod_cast hn0
      refine mul_ne_zero ?_ (Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hn0' _).ne')
      rw [ArithmeticFunction.moebius_apply_of_squarefree hn]; simp
    exact (mul_eq_zero.mp (hne n hn0)).resolve_left hwn

/-- **Hilbert-valued rigidity (13).** -/
theorem rigged_map_vanishes {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] {a : ℝ}
    (ha : 0 < a) (T : ℓ²ℕ →L[ℂ] Y)
    (hvanish : ∀ t : ℝ, 0 < t → xi (linePt t) = 0 → (analyticOrderAt xi (linePt t)).toNat = 1 →
      T (riggedSource a 1 t) = 0) (f : ℓ²ℕ) (hf : f ∈ squarefreeSubspace) : T f = 0 := by
  have h := rigged_reader_vanishes ha ((innerSL ℂ (T f)).comp T) (fun t ht0 hxi hs => by
    rw [ContinuousLinearMap.comp_apply, hvanish t ht0 hxi hs, map_zero]) f hf
  rw [ContinuousLinearMap.comp_apply, innerSL_apply_apply] at h
  exact inner_self_eq_zero.mp h

/-- **Rigidity at every safe Euler level.**  For `σ > 1`, a bounded reading of the normalized source
`y_{σ,γ}` vanishing at every positive simple critical ordinate annihilates `ℓ²(squarefree)`. -/
theorem source_reader_vanishes {σ : ℝ} (hσ : 1 < σ) (L : ℓ²ℕ →L[ℂ] ℂ)
    (hvanish : ∀ t : ℝ, 0 < t → xi (linePt t) = 0 → (analyticOrderAt xi (linePt t)).toNat = 1 →
      L (ordinateSource σ (-t)) = 0) (f : ℓ²ℕ) (hf : f ∈ squarefreeSubspace) : L f = 0 := by
  set η : ℝ := (σ - 1) / 4 with hηdef
  have hη : 0 < η := by rw [hηdef]; linarith
  have hw := weightedAbsSummable_source_mul (t := fun n => L (lp.single 2 n 1)) (η := η) hσ
    (by rw [hηdef]; linarith) (summable_norm_sq_functional L)
  have hread : ∀ t : ℝ, L (ordinateSource σ (-t)) =
      dirichletReadout (fun n => sourceWeight σ n * L (lp.single 2 n 1)) t := by
    intro t
    have hw0 := weightedAbsSummable_source_mul (t := fun n => L (lp.single 2 n 1)) (η := 0) hσ
      (by linarith) (summable_norm_sq_functional L)
    rw [dirichletReadout_ofReal hw0 le_rfl, GaloisForLFunctions.expSeriesCarrier]
    have h := hasSum_functional L (ordinateSource σ (-t))
    rw [← h.tsum_eq, h.summable.tsum_eq_zero_add]
    simp only [ordinateSource_neg_apply hσ, sourceWeight_zero, mul_zero, zero_mul, zero_add]
    refine tsum_congr fun m => ?_
    ring
  have hcoef := coeff_eq_zero_of_readout_vanishes_on_simpleCritical hw hη
    fun t ht0 hxi hs => by rw [← hread t]; exact hvanish t ht0 hxi hs
  refine functional_eq_zero_on_squarefree L (fun n hn => ?_) f hf
  have hn0 : 0 < n := Nat.pos_of_ne_zero fun h => by subst h; exact not_squarefree_zero hn
  have hwn : sourceWeight σ n ≠ 0 := by
    intro h0
    have := norm_infiniteMobiusSignedWeight_sq hσ n
    rw [show infiniteMobiusSignedWeight σ n = sourceWeight σ n from rfl, h0, norm_zero] at this
    have hprob : 0 < squarefreeMobiusProbability σ n := by
      rw [squarefreeMobiusProbability, squarefreeMobiusMass, if_pos hn]
      exact div_pos (by positivity) (squarefreeMobiusTotal_pos hσ)
    nlinarith
  exact (mul_eq_zero.mp (hcoef n hn0)).resolve_left hwn

/-! ### The cofinal singular divisor reader (14) -/

/-- **(14)**  If bounded functionals `L_j` read `z_{σ_j,γ}`, `σ_j ↓ 1`, convergently at every height
to a nonzero `F` vanishing at every positive simple critical Xi ordinate, then `‖L_j‖ → ∞`. -/
theorem tendsto_norm_atTop_of_divisor_reader {a : ℝ} (ha : 0 < a) (σs : ℕ → ℝ)
    (hσs : Tendsto σs atTop (𝓝[>] 1)) (L : ℕ → ℓ²ℕ →L[ℂ] ℂ) (F : ℝ → ℂ)
    (hconv : ∀ γ, Tendsto (fun j => L j (riggedSource a (σs j) γ)) atTop (𝓝 (F γ)))
    (hF : ∃ γ, F γ ≠ 0)
    (hzero : ∀ t : ℝ, 0 < t → xi (linePt t) = 0 → (analyticOrderAt xi (linePt t)).toNat = 1 →
      F t = 0) :
    Tendsto (fun j => ‖L j‖) atTop atTop := by
  by_contra hnt
  obtain ⟨B, hB⟩ : ∃ B : ℝ, ∃ᶠ j in atTop, ‖L j‖ ≤ B := by
    rw [tendsto_atTop] at hnt
    push Not at hnt
    obtain ⟨B, hB⟩ := hnt
    exact ⟨B, hB.mono fun j h => le_of_lt h⟩
  obtain ⟨φ, hφ, hφB⟩ := Filter.extraction_of_frequently_atTop hB
  set h : ℕ → ℓ²ℕ := fun k => (InnerProductSpace.toDual ℂ ℓ²ℕ).symm (L (φ k)) with hhdef
  have hL : ∀ k f, L (φ k) f = inner ℂ (h k) f := fun k f =>
    (InnerProductSpace.toDual_symm_apply).symm
  have hnorm : ∀ k, ‖h k‖ ≤ B := fun k => by
    rw [hhdef, LinearIsometryEquiv.norm_map]; exact hφB k
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hnorm 0)
  have hcpt : IsCompact (Set.univ.pi fun _ : ℕ => Metric.closedBall (0 : ℂ) B) :=
    isCompact_univ_pi fun _ => isCompact_closedBall 0 B
  obtain ⟨g, -, ψ, hψ, hlim⟩ := hcpt.tendsto_subseq (x := fun k => ((h k : ℓ²ℕ) : ℕ → ℂ))
    (fun k n _ => by
      simpa using (lp.norm_apply_le_norm (E := fun _ : ℕ => ℂ) (p := 2) two_ne_zero (h k) n).trans
        (hnorm k))
  have hcoord : ∀ n, Tendsto (fun k => (h (ψ k) : ℕ → ℂ) n) atTop (𝓝 (g n)) := fun n =>
    ((continuous_apply n).tendsto g).comp hlim
  have hgsum : ∀ N, ∑ n ∈ Finset.range N, ‖g n‖ ^ 2 ≤ B ^ 2 := by
    intro N
    have hlim' : Tendsto (fun k => ∑ n ∈ Finset.range N, ‖(h (ψ k) : ℕ → ℂ) n‖ ^ 2) atTop
        (𝓝 (∑ n ∈ Finset.range N, ‖g n‖ ^ 2)) :=
      tendsto_finsetSum _ fun n _ => (hcoord n).norm.pow 2
    refine le_of_tendsto hlim' (Eventually.of_forall fun k => ?_)
    calc ∑ n ∈ Finset.range N, ‖(h (ψ k) : ℕ → ℂ) n‖ ^ 2
        ≤ ∑' n, ‖(h (ψ k) : ℕ → ℂ) n‖ ^ 2 :=
          Summable.sum_le_tsum _ (fun _ _ => by positivity) (summable_norm_sq_lp _)
      _ = ‖h (ψ k)‖ ^ 2 := (HilbertSchmidt.lp_norm_sq_eq _).symm
      _ ≤ B ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hnorm _) 2
  have hgmem : Memℓp g 2 :=
    HilbertSchmidt.memℓp_of_sq (summable_of_sum_range_le (fun _ => by positivity) hgsum)
  set G : ℓ²ℕ := ⟨g, hgmem⟩ with hG
  have hGn : ‖G‖ ≤ B := by
    have h2 : ‖G‖ ^ 2 ≤ B ^ 2 := by
      rw [HilbertSchmidt.lp_norm_sq_eq]
      exact Real.tsum_le_of_sum_range_le (fun _ => by positivity) hgsum
    exact (sq_le_sq₀ (norm_nonneg _) hB0).mp h2
  have hweak : ∀ f : ℓ²ℕ, Tendsto (fun k => inner ℂ (h (ψ k)) f) atTop (𝓝 (inner ℂ G f)) := by
    intro f
    have h1 := tendsto_inner_lp_of_coord (fun k => h (ψ k) - G) (C := 2 * B) (by positivity)
      (fun k => (norm_sub_le _ _).trans (by linarith [hnorm (ψ k)]))
      (fun n => by
        have := (hcoord n).sub_const (g n)
        simp only [sub_self] at this
        refine this.congr fun k => ?_
        rw [lp.coeFn_sub, Pi.sub_apply]) f
    have h2 := h1.star
    simp only [star_zero] at h2
    have h3 : Tendsto (fun k => inner ℂ (h (ψ k)) f - inner ℂ G f) atTop (𝓝 0) :=
      h2.congr fun k => by
        rw [← inner_sub_left]
        exact inner_conj_symm _ _
    simpa using h3.add_const (inner ℂ G f)
  have hsub : Tendsto (fun k => φ (ψ k)) atTop atTop := (hφ.comp hψ).tendsto_atTop
  have hFG : ∀ γ, F γ = inner ℂ G (riggedSource a 1 γ) := by
    intro γ
    have h1 : Tendsto (fun k => L (φ (ψ k)) (riggedSource a (σs (φ (ψ k))) γ)) atTop (𝓝 (F γ)) :=
      (hconv γ).comp hsub
    have hz : Tendsto (fun k => riggedSource a (σs (φ (ψ k))) γ) atTop (𝓝 (riggedSource a 1 γ)) :=
      (tendsto_riggedSource ha γ).comp (hσs.comp hsub)
    have hdiff : Tendsto (fun k => inner ℂ (h (ψ k))
        (riggedSource a (σs (φ (ψ k))) γ - riggedSource a 1 γ)) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have hz' := (tendsto_iff_norm_sub_tendsto_zero.mp hz).const_mul B
      rw [mul_zero] at hz'
      refine squeeze_zero (fun _ => norm_nonneg _) (fun k => ?_) hz'
      exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hnorm _) (norm_nonneg _))
    have h2 : Tendsto (fun k => L (φ (ψ k)) (riggedSource a (σs (φ (ψ k))) γ)) atTop
        (𝓝 (inner ℂ G (riggedSource a 1 γ))) := by
      have := (hweak (riggedSource a 1 γ)).add hdiff
      rw [add_zero] at this
      refine this.congr fun k => ?_
      rw [hL, inner_sub_right]; ring
    exact tendsto_nhds_unique h1 h2
  have hvan := rigged_reader_vanishes ha (innerSL ℂ G) (fun t ht0 hxi hs => by
    rw [innerSL_apply_apply, ← hFG]; exact hzero t ht0 hxi hs)
  obtain ⟨γ, hγ⟩ := hF
  exact hγ (by
    rw [hFG, ← innerSL_apply_apply]
    exact hvan _ (riggedSource_mem_squarefreeSubspace a 1 γ))

end RHTower
