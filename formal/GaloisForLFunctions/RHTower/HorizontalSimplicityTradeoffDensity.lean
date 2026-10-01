import GaloisForLFunctions.RHTower.HorizontalSimplicityWindowSums
import GaloisForLFunctions.RHTower.ZetaOffLineMomentSelbergWeights
import GaloisForLFunctions.RHTower.Zeta23SimpleCriticalDensity
import GaloisForLFunctions.RHTower.XiCensusVonMangoldtBridge
import GaloisForLFunctions.RHTower.RiemannVonMangoldt

/-!
# Horizontal singleton fibres: density at least `HD(1) − 17π/1200`

**Theorem** (`horizontalSingleton_density_selberg`).  In lower density, at least
`HD(1) − 17π/1200 = 0.628…` of the positive-ordinate zeros of `ξ` (counted with multiplicity) lie on
a horizontal line carrying no other zero.  Here `HD(1) = 2 − 1/c₁* = 0.6725…` is the
Montgomery–Taylor constant.  In general an off-line moment bound `Σ (β − ½)⁺ ≤ μ T` gives
`HD(1) − πμ/12` (`horizontalSingleton_density_of_moment`); `μ = 21/100` gives `HD(1) − 7π/400`
(`horizontalSingleton_density_tradeoff`) and `μ = 17/100` the theorem.

Proof.
* For fixed `λ < 1`, Theorem D with overlap deficits (`thmD_horizontal_deficit_lam_abstract`) gives
  `(HD(λ) − ε) N(T,2T) ≤ N_iso + (L/24) Σ_{I′, β > ½} (β − ½) + (2/L) N(I′)`, `L = λ log(T/2π)`.
  The edges of `I′` and the last term are `o(N(T,2T))`, and `log(T/2π)(β − ½) ≤ (β − ½) log(γ/2π)`
  on `(T, 2T]`.  So `(HD(λ) − ε) N(T,2T) ≤ N_iso(T,2T) + (λ/24) M_log(T,2T)` with the additive
  logarithmic moment `M_log` (`zeta_block_deficit_lam`).
* Dyadic summation (`Assembly.dyadic`) and `λ → 1` (`eps_form_HD`) give
  `(HD(1) − ε) N(T) ≤ N_iso(0,T) + M_log(0,T)/24` (`zeta_cumulative_deficit`).
* `M_log(0,T) ≤ log T · Σ (β − ½)⁺ ≤ μ T log T` by an off-line moment bound; unconditionally
  `μ = 17/100` (`ZetaGateProductAFE.eventually_offLineMoment_le_selberg`).  Riemann–von Mangoldt
  gives `T log T ≤ (2π + o(1)) N(T)`, and `(μ/24)·2π = πμ/12`.
* A simple critical zero with no off-line zero on its horizontal line is alone on that line
  (`NisoH_half_le_xiSingletonFiberCount`).
-/

open Filter Asymptotics Topology Zeta23 Zeta23.ThmD Zeta23.Assembly

namespace RHTower

noncomputable section

/-- `√T · l(T)² = o(T l(T))`. -/
theorem isLittleO_sqrt_mul_l_sq_Tl :
    (fun T => Real.sqrt T * l T ^ 2) =o[atTop] fun T => T * l T := by
  have hlog := isLittleO_log_rpow_atTop (by norm_num : (0:ℝ) < 1 / 2)
  refine (isLittleO_iff).2 fun c hc => ?_
  filter_upwards [hlog.bound hc, eventually_l_pos, eventually_gt_atTop (0:ℝ)] with T hT hl hT0
  have hsq : T ^ (1 / 2 : ℝ) = Real.sqrt T := (Real.sqrt_eq_rpow T).symm
  have hlT : l T ≤ Real.log T := by
    unfold l
    rw [Real.log_div hT0.ne' (by positivity)]
    have : 0 < Real.log (2 * Real.pi) := Real.log_pos (by linarith [Real.pi_gt_three])
    linarith
  have hlog0 : 0 ≤ Real.log T := le_trans hl.le hlT
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hlog0,
    abs_of_nonneg (by positivity), hsq] at hT
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
    abs_of_nonneg (by positivity)]
  have h1 : l T ≤ c * Real.sqrt T := hlT.trans hT
  have hs : Real.sqrt T * Real.sqrt T = T := Real.mul_self_sqrt hT0.le
  have h2 : Real.sqrt T * l T * l T ≤ Real.sqrt T * l T * (c * Real.sqrt T) :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  calc Real.sqrt T * l T ^ 2 = Real.sqrt T * l T * l T := by ring
    _ ≤ Real.sqrt T * l T * (c * Real.sqrt T) := h2
    _ = c * ((Real.sqrt T * Real.sqrt T) * l T) := by ring
    _ = c * (T * l T) := by rw [hs]

/-- `N(0, T) → ∞` under Riemann–von Mangoldt. -/
theorem tendsto_N_zero_atTop (Z : ZeroConfig) (hR : RiemannVonMangoldt Z) :
    Tendsto (fun T => (Z.N 0 T : ℝ)) atTop atTop := by
  have h1 : Tendsto (fun T : ℝ => (Z.N (T / 2) (2 * (T / 2)) : ℝ)) atTop atTop :=
    (tendsto_N_atTop Z hR).comp (tendsto_id.atTop_div_const two_pos)
  refine tendsto_atTop_mono' _ ?_ h1
  filter_upwards [eventually_ge_atTop 0] with T hT
  have hsplit := N_add Z (a := 0) (b := T / 2) (c := T) (by linarith) (by linarith)
  rw [show 2 * (T / 2) = T by ring, hsplit]
  push_cast
  linarith [(Nat.cast_nonneg (Z.N 0 (T / 2)) : (0:ℝ) ≤ _)]

/-- **The dyadic block bound** at fixed `λ ∈ (0,1)`. -/
theorem zeta_block_deficit_lam {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (HD lam - ε) * (zetaZeroConfig.N T (2 * T) : ℝ)
        ≤ NisoH zetaZeroConfig (1 / 2) T (2 * T)
          + lam / 24 * logMoment zetaZeroConfig T (2 * T) := by
  set Z := zetaZeroConfig with hZ
  have hP := paramsOf_valid taperProfile_stdProfile h0 h1.le
  have hmain := thmD_horizontal_deficit_lam_abstract Z paperInputs_zeta (paramsOf stdProfile lam)
    hP h1 (1 / 2)
  have hR := paperInputs_zeta.RvM
  obtain ⟨A₀, hA₀, hloc⟩ := hR.local_count
  obtain ⟨CII, hII⟩ := Tail.eventually_NII_le Z hA₀ hloc
  set N : ℝ → ℝ := fun T => (Z.N T (2 * T) : ℝ) with hN
  set NII' : ℝ → ℝ := fun T => (NII Z T : ℝ) with hNII'
  set E : ℝ → ℝ := fun T => lam / 48 * l T * NII' T + 2 / (lam * l T) * (N T + NII' T) with hE
  -- the error is `o(N)`
  have hIIO : NII' =O[atTop] fun T => Real.sqrt T * l T := by
    refine IsBigO.of_bound |CII| ?_
    filter_upwards [hII, eventually_l_pos, eventually_ge_atTop 0] with T h hl hT
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _),
      abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) hl.le)]
    calc (NII Z T : ℝ) ≤ CII * Real.sqrt T * l T := h
      _ ≤ |CII| * (Real.sqrt T * l T) := by
        rw [← mul_assoc]; gcongr; exact le_abs_self _
  have o1 : (fun T => lam / 48 * l T * NII' T) =o[atTop] N := by
    apply isLittleO_N_of_isLittleO_Tl Z hR
    refine IsBigO.trans_isLittleO ?_ isLittleO_sqrt_mul_l_sq_Tl
    refine IsBigO.of_bound (lam / 48 * |CII|) ?_
    filter_upwards [hII, eventually_l_pos, eventually_ge_atTop 0] with T h hl hT
    have hNII0 : (0:ℝ) ≤ NII' T := Nat.cast_nonneg _
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (mul_nonneg (by positivity) hl.le) hNII0),
      abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (sq_nonneg _))]
    have h' : (NII Z T : ℝ) ≤ |CII| * Real.sqrt T * l T := by
      refine h.trans ?_
      have := le_abs_self CII
      have h2 : 0 ≤ Real.sqrt T * l T := mul_nonneg (Real.sqrt_nonneg _) hl.le
      nlinarith
    have := mul_le_mul_of_nonneg_left h' (mul_nonneg (by positivity) hl.le : (0:ℝ) ≤ lam / 48 * l T)
    calc lam / 48 * l T * NII' T ≤ lam / 48 * l T * (|CII| * Real.sqrt T * l T) := this
      _ = lam / 48 * |CII| * (Real.sqrt T * l T ^ 2) := by ring
  have o2 : NII' =o[atTop] N := isLittleO_N_of_isLittleO_Tl Z hR
    (hIIO.trans_isLittleO isLittleO_sqrt_mul_l_Tl)
  have hinv : Tendsto (fun T => 2 / (lam * l T)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_l_atTop.const_mul_atTop h0)
  have o3 : (fun T => 2 / (lam * l T) * (N T + NII' T)) =o[atTop] N :=
    (isLittleO_of_tendsto_zero_mul hinv).trans_isBigO ((isBigO_refl N atTop).add o2.isBigO)
  have hEo : E =o[atTop] N := o1.add o3
  intro ε hε
  have hEb := hEo.bound (by linarith : (0:ℝ) < ε / 2)
  obtain ⟨T₁, hT₁⟩ := hmain (ε / 2) (by linarith)
  obtain ⟨T₂, hT₂⟩ := eventually_atTop.mp (hEb.and (eventually_l_pos.and (eventually_ge_atTop 1)))
  refine ⟨max T₁ T₂, fun T hT => ?_⟩
  have hTT₁ : T₁ ≤ T := le_trans (le_max_left _ _) hT
  obtain ⟨hEbT, hl, hT1⟩ := hT₂ T (le_trans (le_max_right _ _) hT)
  have hT0 : 0 < T := by linarith
  have h := hT₁ T hTT₁
  -- the window `I′` and its edges
  have hD0 : D0 T = Real.sqrt T := rfl
  have hs0 : 0 ≤ Real.sqrt T := Real.sqrt_nonneg T
  have hLdef : (paramsOf stdProfile lam).L T = lam * l T := rfl
  have hw : (paramsOf stdProfile lam).w = 1 := rfl
  rw [hLdef, hw, hD0] at h
  have hsplit : offMoment Z (T - Real.sqrt T) (2 * T + Real.sqrt T)
      = offMoment Z (T - Real.sqrt T) T + offMoment Z T (2 * T)
        + offMoment Z (2 * T) (2 * T + Real.sqrt T) := by
    rw [offMoment_add Z (by linarith : T - Real.sqrt T ≤ T) (by linarith : T ≤ 2 * T + Real.sqrt T),
      offMoment_add Z (by linarith : T ≤ 2 * T) (by linarith : 2 * T ≤ 2 * T + Real.sqrt T)]
    ring
  have hmid := mul_offMoment_le_logMoment Z (T₂ := 2 * T) hT0
  have hedge1 := offMoment_le_half_N Z (T - Real.sqrt T) T
  have hedge2 := offMoment_le_half_N Z (2 * T) (2 * T + Real.sqrt T)
  have hNII : (NII Z T : ℝ) = (Z.N (T - Real.sqrt T) T : ℝ) + (Z.N (2 * T) (2 * T + Real.sqrt T) : ℝ) := by
    simp only [NII, hD0]; push_cast; ring
  have hNI : (Z.NIprime T : ℝ) = N T + NII' T := by
    simp only [hN, hNII']; exact_mod_cast NIprime_eq Z hT0.le
  rw [hNI] at h
  have hlam24 : 0 ≤ 1 / 24 * (lam * l T) := by positivity
  have hcnt : 1 / 24 * (lam * l T) * offMoment Z (T - Real.sqrt T) (2 * T + Real.sqrt T)
      ≤ lam / 24 * logMoment Z T (2 * T) + lam / 48 * l T * NII' T := by
    rw [hsplit]
    have e1 : 1 / 24 * (lam * l T) * offMoment Z T (2 * T) ≤ lam / 24 * logMoment Z T (2 * T) := by
      have := mul_le_mul_of_nonneg_left hmid (by positivity : (0:ℝ) ≤ lam / 24)
      linarith
    have e2 := mul_le_mul_of_nonneg_left hedge1 hlam24
    have e3 := mul_le_mul_of_nonneg_left hedge2 hlam24
    simp only [hNII', hNII]
    nlinarith
  have hENb : E T ≤ ε / 2 * N T := by
    have hN0 : 0 ≤ N T := Nat.cast_nonneg _
    have := le_trans (le_abs_self _) hEbT
    rwa [Real.norm_eq_abs, abs_of_nonneg hN0] at this
  have hEeq : E T = lam / 48 * l T * NII' T + 2 * 1 / (lam * l T) * (N T + NII' T) := by
    simp only [hE]; ring
  have hN0 : 0 ≤ N T := Nat.cast_nonneg _
  change (HD lam - ε) * N T ≤ _
  change (HD lam - ε / 2) * N T ≤ _ + 1 / 24 * (lam * l T) * _ + 2 * 1 / (lam * l T) * (N T + NII' T)
    at h
  nlinarith

/-- **Cumulative bound** at fixed `λ ∈ (0,1)`. -/
theorem zeta_cumulative_deficit_lam {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (HD lam - ε) * (zetaZeroConfig.N 0 T : ℝ)
        ≤ NisoH zetaZeroConfig (1 / 2) 0 T + lam / 24 * logMoment zetaZeroConfig 0 T :=
  dyadic (f := fun a b => (NisoH zetaZeroConfig (1 / 2) a b : ℝ)
      + lam / 24 * logMoment zetaZeroConfig a b)
    (g := fun a b => (zetaZeroConfig.N a b : ℝ))
    (fun a b c hab hbc => by
      rw [NisoH_add _ _ hab hbc, logMoment_add _ hab hbc]
      push_cast; ring)
    (fun a b c hab hbc => by
      rw [N_add _ hab hbc]
      push_cast; ring)
    (fun a b => by
      have := logMoment_nonneg zetaZeroConfig a b
      positivity)
    (fun a b => Nat.cast_nonneg _)
    (tendsto_N_zero_atTop _ paperInputs_zeta.RvM)
    (zeta_block_deficit_lam h0 h1)

/-- **Cumulative bound**, `λ → 1`. -/
theorem zeta_cumulative_deficit :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (HD 1 - ε) * (zetaZeroConfig.N 0 T : ℝ)
        ≤ NisoH zetaZeroConfig (1 / 2) 0 T + logMoment zetaZeroConfig 0 T / 24 :=
  eps_form_HD (fun _ => Nat.cast_nonneg _) fun lam hl1 hl2 ε hε => by
    obtain ⟨T₀, hT₀⟩ := zeta_cumulative_deficit_lam (by linarith) hl2 ε hε
    refine ⟨T₀, fun T hT => (hT₀ T hT).trans ?_⟩
    have h := logMoment_nonneg zetaZeroConfig 0 T
    have : lam / 24 * logMoment zetaZeroConfig 0 T ≤ logMoment zetaZeroConfig 0 T / 24 := by
      nlinarith
    linarith

/-! ## Bridges to the `ξ` census -/

theorem zetaZeroConfig_N_zero_eq (T : ℝ) : zetaZeroConfig.N 0 T = xiPosZeroCount T := by
  rw [← zeta23_Ncount_zero_eq_xiPosZeroCount]
  exact zetaZeros_N zetaSeam 0 T

/-- The distinct-zero off-line moment is at most the census moment. -/
theorem offMoment_zero_le_offLineMoment (T : ℝ) :
    offMoment zetaZeroConfig 0 T ≤ offLineMoment T := by
  classical
  unfold offMoment offLineMoment
  set S := (zetaZeroConfig.window_finite 0 T).toFinset.filter (fun ρ => 1 / 2 < ρ.re)
  have hmem : ∀ ρ ∈ S, ρ ∈ boxFinsetLe T ∧ 1 ≤ ((analyticOrderAt xi ρ).toNat : ℝ) := by
    intro ρ hρ
    obtain ⟨hρw, hre⟩ := Finset.mem_filter.mp hρ
    rw [Set.Finite.mem_toFinset] at hρw
    obtain ⟨hnt, him0, himT⟩ := hρw
    have hnt' : IsNontrivialZero ρ := hnt
    obtain ⟨hz, hre0, hre1⟩ := hnt'
    refine ⟨mem_boxFinsetLe.mpr ⟨hre, hre1, him0.le, himT,
      (xi_zero_iff_zeta_zero_of_mem_strip hre0 hre1).2 hz⟩, ?_⟩
    have hm := zetaZeroConfig.one_le_mult ρ hnt
    have : zetaZeroConfig.mult ρ = (analyticOrderAt xi ρ).toNat := by
      show zeroMult ρ = _
      unfold zeroMult
      rw [xi_analyticOrderAt_eq_riemannZeta_of_mem_strip ⟨hre0, hre1⟩]
    rw [this] at hm
    exact_mod_cast hm
  calc ∑ ρ ∈ S, (ρ.re - 1 / 2)
      ≤ ∑ ρ ∈ S, ((analyticOrderAt xi ρ).toNat : ℝ) * (ρ.re - 1 / 2) := by
        refine Finset.sum_le_sum fun ρ hρ => ?_
        have h1 := (hmem ρ hρ).2
        have h2 : 0 ≤ ρ.re - 1 / 2 := by linarith [(Finset.mem_filter.mp hρ).2]
        nlinarith
    _ ≤ ∑ z ∈ boxFinsetLe T, ((analyticOrderAt xi z).toNat : ℝ) * (z.re - 1 / 2) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (fun ρ hρ => (hmem ρ hρ).1)
        intro z hz _
        exact offLineMoment_term_nonneg hz

/-- A simple critical zero with no off-line zero on its horizontal line is alone there. -/
theorem NisoH_half_le_xiSingletonFiberCount (T : ℝ) :
    NisoH zetaZeroConfig (1 / 2) 0 T ≤ xiSingletonFiberCount T := by
  classical
  unfold NisoH xiSingletonFiberCount
  rw [← Set.ncard_coe_finset]
  apply Set.ncard_le_ncard _ (Finset.finite_toSet _)
  rintro ρ ⟨⟨⟨⟨hnt, him0, himT⟩, hline⟩, hsimple⟩, hiso⟩
  have hnt' : IsNontrivialZero ρ := hnt
  obtain ⟨hz, hre0, hre1⟩ := hnt'
  have hxi : xi ρ = 0 := (xi_zero_iff_zeta_zero_of_mem_strip hre0 hre1).2 hz
  have hline' : ρ.re = 1 / 2 := hline
  have hmult : zeroMult ρ = 1 := hsimple
  rw [Finset.mem_coe, Finset.mem_filter]
  refine ⟨mem_stripFinsetPos.mpr ⟨hre0, hre1, him0, himT, hxi⟩, ?_⟩
  -- the horizontal fibre of `ρ` is `{ρ}`
  have hfib : stripHeightFinset ρ.im = {ρ} := by
    ext z
    rw [Finset.mem_singleton, mem_stripHeightFinset]
    constructor
    · rintro ⟨hz0, hz1, hzim, hzxi⟩
      have hzζ : riemannZeta z = 0 := (xi_zero_iff_zeta_zero_of_mem_strip hz0 hz1).1 hzxi
      have hzre : z.re = 1 / 2 := by
        by_contra hne
        have h := hiso z ⟨hzζ, hz0, hz1⟩ hzim hne
        have : |z.re - 1 / 2| < 1 / 2 := abs_lt.mpr ⟨by linarith, by linarith⟩
        linarith
      exact Complex.ext (by rw [hzre, hline']) hzim
    · rintro rfl
      exact ⟨hre0, hre1, rfl, hxi⟩
  unfold xiHorizontalMultiplicity
  rw [hfib, Finset.sum_singleton, xi_analyticOrderAt_eq_riemannZeta_of_mem_strip ⟨hre0, hre1⟩]
  exact hmult

/-! ## The density theorem -/

/-- **Horizontal singleton fibres from an off-line moment bound.**  If
`Σ_{0 < Im ρ ≤ V} m(ρ)(Re ρ − ½) ≤ μ V` for all large `V`, `0 ≤ μ ≤ 1`, then in lower density at
least `HD(1) − πμ/12` of the positive-ordinate zero copies of `ξ` lie on a horizontal line carrying
no other zero. -/
theorem horizontalSingleton_density_of_moment {μ : ℝ} (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1)
    (hmom : ∀ᶠ V in atTop, offLineMoment V ≤ μ * V) :
    HD 1 - Real.pi * μ / 12 ≤ liminf xiSingletonFiberRatio atTop := by
  have hcob : IsCoboundedUnder (fun x y : ℝ => x ≥ y) atTop xiSingletonFiberRatio :=
    (isBoundedUnder_of ⟨1, fun T => xiSingletonFiberRatio_le_one T⟩).isCoboundedUnder_ge
  have hπ := Real.pi_pos
  refine le_of_forall_sub_le fun η hη => ?_
  set ε' := η / (4 * Real.pi * (1 + η)) with hε'
  have hε'0 : 0 < ε' := by positivity
  obtain ⟨T₁, hT₁⟩ := zeta_cumulative_deficit (η / 2) (by linarith)
  obtain ⟨T₂, hT₂4, hT₂⟩ := exists_xiZeroCount_close ε' hε'0
  obtain ⟨T₃, hT₃⟩ := eventually_atTop.mp hmom
  refine le_liminf_of_le hcob ?_
  filter_upwards [eventually_ge_atTop T₁, eventually_ge_atTop T₂, eventually_ge_atTop T₃,
    eventually_pos_xiPosZeroCount_of_zeta23, eventually_l_pos] with T h1 h2 h3 hNpos hl
  have hT4 : 4 ≤ T := le_trans hT₂4 h2
  have hT0 : 0 ≤ T := by linarith
  set N := (xiPosZeroCount T : ℝ) with hN
  have hNZ : (zetaZeroConfig.N 0 T : ℝ) = N := by rw [zetaZeroConfig_N_zero_eq]
  have hmain := hT₁ T h1
  rw [hNZ] at hmain
  -- the logarithmic moment
  have hlT : l T ≤ Real.log T := by
    unfold l
    rw [Real.log_div (by linarith) (by positivity)]
    have : 0 < Real.log (2 * Real.pi) := Real.log_pos (by linarith [Real.pi_gt_three])
    linarith
  have hlog0 : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have hM0 := offMoment_nonneg zetaZeroConfig 0 T
  have hM1 := offMoment_zero_le_offLineMoment T
  have hM2 := hT₃ T h3
  have hlogM : logMoment zetaZeroConfig 0 T ≤ Real.log T * (μ * T) := by
    have e1 := logMoment_le_mul_offMoment zetaZeroConfig (T₁ := 0) (T := T) le_rfl
    have e2 : max (l T) 0 ≤ Real.log T := max_le hlT hlog0
    calc logMoment zetaZeroConfig 0 T ≤ max (l T) 0 * offMoment zetaZeroConfig 0 T := e1
      _ ≤ Real.log T * offMoment zetaZeroConfig 0 T := mul_le_mul_of_nonneg_right e2 hM0
      _ ≤ Real.log T * (μ * T) :=
          mul_le_mul_of_nonneg_left (hM1.trans hM2) hlog0
  -- Riemann–von Mangoldt
  have hRvM : (1 / (2 * Real.pi) - ε') * (T * Real.log T) ≤ N := by
    have hc := abs_le.mp (hT₂ T h2)
    have hcast : ((xiPosZeroCount T : ℤ) : ℝ) = ((xiZeroCount T : ℤ) : ℝ) :=
      congrArg (fun n : ℤ => (n : ℝ)) (xiPosZeroCount_eq_xiZeroCount hT0)
    have : (N : ℝ) = (xiZeroCount T : ℝ) := by
      rw [hN, ← hcast]; push_cast; rfl
    rw [this]
    linarith [hc.1]
  have hTl0 : 0 ≤ T * Real.log T := mul_nonneg hT0 hlog0
  have hkey : logMoment zetaZeroConfig 0 T / 24 ≤ (Real.pi * μ / 12 + η / 2) * N := by
    have e1 : logMoment zetaZeroConfig 0 T / 24 ≤ μ / 24 * (T * Real.log T) := by
      linarith [hlogM]
    have e2 : μ / 24 * (T * Real.log T)
        ≤ (Real.pi * μ / 12 + η / 2) * ((1 / (2 * Real.pi) - ε') * (T * Real.log T)) := by
      have hcoef : μ / 24 ≤ (Real.pi * μ / 12 + η / 2) * (1 / (2 * Real.pi) - ε') := by
        have hpi1 : Real.pi * μ / 12 ≤ 1 := by nlinarith [Real.pi_lt_d2]
        have hε'b : ε' * (1 + η) = η / (4 * Real.pi) := by
          rw [hε']; field_simp
        have hb : ε' * (Real.pi * μ / 12 + η / 2) ≤ η / (4 * Real.pi) := by
          rw [← hε'b]
          exact mul_le_mul_of_nonneg_left (by linarith) hε'0.le
        have e : (Real.pi * μ / 12 + η / 2) * (1 / (2 * Real.pi))
            = μ / 24 + η / (4 * Real.pi) := by
          field_simp; ring
        nlinarith
      have := mul_le_mul_of_nonneg_right hcoef hTl0
      linarith
    have e3 : (Real.pi * μ / 12 + η / 2) * ((1 / (2 * Real.pi) - ε') * (T * Real.log T))
        ≤ (Real.pi * μ / 12 + η / 2) * N :=
      mul_le_mul_of_nonneg_left hRvM (by positivity)
    linarith
  have hNpos' : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hsing := NisoH_half_le_xiSingletonFiberCount T
  have hsing' : (NisoH zetaZeroConfig (1 / 2) 0 T : ℝ) ≤ (xiSingletonFiberCount T : ℝ) := by
    exact_mod_cast hsing
  rw [xiSingletonFiberRatio, le_div_iff₀ hNpos']
  nlinarith

/-- **Horizontal singleton fibres.**  In lower density at least `HD(1) − 7π/400 = 0.6175…` of the
positive-ordinate zero copies of `ξ` lie on a horizontal line carrying no other zero. -/
theorem horizontalSingleton_density_tradeoff :
    HD 1 - 7 * Real.pi / 400 ≤ liminf xiSingletonFiberRatio atTop := by
  have h := horizontalSingleton_density_of_moment (μ := 21 / 100) (by norm_num) (by norm_num)
    ZetaGateProductAFE.eventually_offLineMoment_le
  rwa [show Real.pi * (21 / 100) / 12 = 7 * Real.pi / 400 by ring] at h

/-- **Horizontal singleton fibres, Selberg moment.**  In lower density at least
`HD(1) − 17π/1200 = 0.628…` of the positive-ordinate zero copies of `ξ` lie on a horizontal line
carrying no other zero. -/
theorem horizontalSingleton_density_selberg :
    HD 1 - 17 * Real.pi / 1200 ≤ liminf xiSingletonFiberRatio atTop := by
  have h := horizontalSingleton_density_of_moment (μ := 17 / 100) (by norm_num) (by norm_num)
    ZetaGateProductAFE.eventually_offLineMoment_le_selberg
  rwa [show Real.pi * (17 / 100) / 12 = 17 * Real.pi / 1200 by ring] at h

end

end RHTower
