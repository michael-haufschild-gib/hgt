import Zeta23.FinalMult

/-!
# Off-line multiple zeros are charged twice by the two-thirds certificate

Alpöge–Furman's `c = 2` rank–trace certificate (`Zeta23.thmB₀_mult`) bounds the simple
critical-line zeros of `ζ` below by `(2/3 − ε)N(T,2T)`.  Its zero-side step discards the
multiplicity excess `N − (s₁ + 2s₂ + 2p)`.  Every off-line zero of multiplicity `m ≥ 2` contributes
`m − 1 ≥ m/2` to that excess, so keeping it gives the refinement

`(2/3 − ε)·N(T,2T) + M_off(T,2T) ≤ N₀ˢ(T,2T)`,

where `M_off` counts, with multiplicity, the off-line zeros of multiplicity at least two.
Unconditional consequences for Mathlib's `riemannZeta`:

* `M_off ≤ (1/6 + ε)N`: at least `(5/6 − ε)N` zero copies are simple or on the critical line;
* `S_off + 2·M_off ≤ (1/3 + ε)N`, where `S_off` counts the simple off-line zeros;
* in every large dyadic window, either at least three quarters of the zero copies lie on the
  critical line, or at least `(1/6 − ε)N` of them are simple off-line zeros.

The last item isolates the three-quarters problem: it is a bound on simple off-line zeros alone.
-/

open Filter Asymptotics Topology Real RHLinalg Finset
open scoped BigOperators ComplexOrder

noncomputable section

namespace RHTower

open Zeta23 Zeta23.ZeroSide Zeta23.ZeroSide.RankTraceMult Zeta23.Assembly

/-! ## Block level: the excess pays for off-line multiple zeros twice -/

section Block

variable {ι d : Type*} [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d]

/-- Off-line zeros of multiplicity at least two in a zero block, counted with multiplicity. -/
def blockOffLineMultipleMass (D : ZeroBlockData ι d) : ℕ :=
  ∑ z ∈ univ.filter (fun z => ¬ D.σ z = z ∧ 2 ≤ D.m z), D.m z

/-- The raw `c = 2` rank–trace inequality `4 tr Â − ‖Â‖_F² ≤ 3s₁ + 4s₂ + 4p`. -/
theorem four_rtrace_sub_frobSq_le_block (D : ZeroBlockData ι d) (Pr : D.PairReps)
    {c : ℝ} (hc : 0 < c) (hPois : ∀ z ∈ D.onLine, ∑ k, ‖D.v z k‖ ^ (2 : ℕ) ≤ c) :
    4 * rtrace (D.blockP c + D.blockQ c) - frobSq (D.blockP c + D.blockQ c) ≤
      3 * (D.s₁ : ℝ) + 4 * (D.s₂ : ℝ) + 4 * (Pr.p : ℝ) := by
  classical
  have hR := rank_trace_mult_k_le (𝕜 := ℂ) (fun z => D.mhat_nonneg z) (D.vhat c)
    (D.xsq_vhat_le hc hPois) (D.blockQ_isHermitian c) (D.posIndex_blockQ_le Pr hc)
    (c := 2) (by norm_num)
  rw [← D.blockP_eq_Pmat hc] at hR
  have hk : ∑ z : D.onLine, kc 2 (D.mhat z) = 3 * (D.s₁ : ℝ) + 4 * (D.s₂ : ℝ) := by
    have := sum_kc_two_nat (fun z : D.onLine => D.m z) (fun z => D.one_le_m z)
    simp only [ZeroBlockData.mhat] at this ⊢
    rw [this, D.card_sub_filter (fun n => n = 1), D.card_sub_filter (fun n => 2 ≤ n),
      D.card_onLine_m_eq_one]
    have h2 : (D.onLine.filter (fun z => 2 ≤ D.m z)).card = D.s₂ := by
      unfold ZeroBlockData.s₂ ZeroBlockData.S₂ ZeroBlockData.onLine
      rw [Finset.filter_filter]
    rw [h2]
  rw [hk] at hR
  norm_num at hR
  linarith

/-- Each off-line zero of multiplicity `m ≥ 2` carries excess `m − 1 ≥ m/2`, so the off-line
multiple mass is at most twice the multiplicity excess `N − (s₁ + 2s₂ + 2p)`. -/
theorem blockOffLineMultipleMass_add_le (D : ZeroBlockData ι d) (Pr : D.PairReps) :
    blockOffLineMultipleMass D + 2 * (D.s₁ + 2 * D.s₂ + 2 * Pr.p) ≤ 2 * D.Ncount := by
  classical
  set off := univ.filter (fun z => ¬ D.σ z = z) with hoff
  have hsplit : D.Ncount = D.Non + ∑ z ∈ off, D.m z := by
    unfold ZeroBlockData.Ncount ZeroBlockData.Non ZeroBlockData.onLine
    rw [hoff, Finset.sum_filter_add_sum_filter_not]
  have hcard : off.card = 2 * Pr.p := by
    have h1 := D.card_eq_onLine_add Pr
    have h2 := Finset.card_filter_add_card_filter_not (s := (univ : Finset ι))
      (p := fun z => D.σ z = z)
    have h3 : (univ.filter fun z => D.σ z = z) = D.onLine := rfl
    rw [h3, Finset.card_univ] at h2
    rw [hoff]
    omega
  have hNon := D.s₁_add_two_s₂_le_Non
  have hpt : ∀ z ∈ off, 2 + (if 2 ≤ D.m z then D.m z else 0) ≤ 2 * D.m z := by
    intro z _
    have := D.one_le_m z
    split_ifs with h <;> omega
  have hsum := Finset.sum_le_sum hpt
  rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, ← Finset.sum_filter,
    ← Finset.mul_sum, Finset.filter_filter] at hsum
  unfold blockOffLineMultipleMass
  rw [hcard] at hsum
  omega

end Block

/-! ## Window counts for an abstract zero configuration -/

section Window

variable (Z : ZeroConfig)

/-- The window `{ρ : T₁ < Im ρ ≤ T₂}` of distinct zeros, as a finset. -/
def zeroWindowFinset (T₁ T₂ : ℝ) : Finset ℂ := (Z.finite_window T₁ T₂).toFinset

lemma mem_zeroWindowFinset {T₁ T₂ : ℝ} {ρ : ℂ} : ρ ∈ zeroWindowFinset Z T₁ T₂ ↔ ρ ∈ Z.window T₁ T₂ :=
  Set.Finite.mem_toFinset _

/-- Off-line zeros of multiplicity at least two in the window, counted with multiplicity. -/
def offLineMultipleMass (T₁ T₂ : ℝ) : ℕ :=
  ∑ ρ ∈ (zeroWindowFinset Z T₁ T₂).filter (fun ρ => ρ.re ≠ 1 / 2 ∧ 2 ≤ Z.mult ρ), Z.mult ρ

/-- Simple off-line zeros in the window. -/
def offLineSimpleCount (T₁ T₂ : ℝ) : ℕ :=
  ((zeroWindowFinset Z T₁ T₂).filter (fun ρ => ρ.re ≠ 1 / 2 ∧ Z.mult ρ = 1)).card

lemma N_eq_sum_zeroWindowFinset (T₁ T₂ : ℝ) : Z.N T₁ T₂ = ∑ ρ ∈ zeroWindowFinset Z T₁ T₂, Z.mult ρ := by
  rw [ZeroConfig.N]
  exact finsum_mem_eq_finite_toFinset_sum _ (show (Z.window T₁ T₂).Finite from Z.finite_window T₁ T₂)

lemma N0_eq_sum_zeroWindowFinset (T₁ T₂ : ℝ) :
    Z.N0 T₁ T₂ = ∑ ρ ∈ (zeroWindowFinset Z T₁ T₂).filter (fun ρ => ρ.re = 1 / 2), Z.mult ρ := by
  have hset : Z.window T₁ T₂ ∩ ZeroConfig.onLine
      = ↑((zeroWindowFinset Z T₁ T₂).filter (fun ρ => ρ.re = 1 / 2)) := by
    ext ρ
    simp [ZeroConfig.onLine, mem_zeroWindowFinset]
  rw [ZeroConfig.N0, hset, finsum_mem_coe_finset]

lemma N0s_eq_card_zeroWindowFinset (T₁ T₂ : ℝ) :
    Z.N0s T₁ T₂ = ((zeroWindowFinset Z T₁ T₂).filter (fun ρ => ρ.re = 1 / 2 ∧ Z.mult ρ = 1)).card := by
  have hset : Z.window T₁ T₂ ∩ ZeroConfig.onLine ∩ Z.simple
      = ↑((zeroWindowFinset Z T₁ T₂).filter (fun ρ => ρ.re = 1 / 2 ∧ Z.mult ρ = 1)) := by
    ext ρ
    simp only [ZeroConfig.onLine, ZeroConfig.simple, Set.mem_inter_iff, Set.mem_setOf_eq,
      Finset.coe_filter, mem_zeroWindowFinset]
    tauto
  rw [ZeroConfig.N0s, hset, Set.ncard_coe_finset]

/-- `N = N₀ + S_off + M_off`: every zero copy is on the line, simple off-line, or off-line of
multiplicity at least two. -/
theorem N_eq_N0_add_offLineSimple_add_offLineMultiple (T₁ T₂ : ℝ) :
    Z.N T₁ T₂ = Z.N0 T₁ T₂ + offLineSimpleCount Z T₁ T₂ + offLineMultipleMass Z T₁ T₂ := by
  classical
  set W := zeroWindowFinset Z T₁ T₂
  rw [N_eq_sum_zeroWindowFinset, N0_eq_sum_zeroWindowFinset, offLineSimpleCount, offLineMultipleMass,
    ← Finset.sum_filter_add_sum_filter_not W (fun ρ => ρ.re = 1 / 2)]
  have hoff : ∑ ρ ∈ W.filter (fun ρ => ¬ ρ.re = 1 / 2), Z.mult ρ
      = (W.filter (fun ρ => ρ.re ≠ 1 / 2 ∧ Z.mult ρ = 1)).card
        + ∑ ρ ∈ W.filter (fun ρ => ρ.re ≠ 1 / 2 ∧ 2 ≤ Z.mult ρ), Z.mult ρ := by
    rw [← Finset.sum_filter_add_sum_filter_not (W.filter fun ρ => ¬ ρ.re = 1 / 2)
      (fun ρ => Z.mult ρ = 1), Finset.filter_filter, Finset.filter_filter]
    congr 1
    · rw [Finset.card_eq_sum_ones]
      refine Finset.sum_congr rfl fun ρ hρ => ?_
      exact (Finset.mem_filter.mp hρ).2.2
    · refine Finset.sum_congr ?_ fun _ _ => rfl
      ext ρ
      simp only [Finset.mem_filter, ne_eq]
      constructor
      · rintro ⟨hW, hre, h1⟩
        have := Z.one_le_mult ρ ((mem_zeroWindowFinset Z).mp hW).1
        exact ⟨hW, hre, by omega⟩
      · rintro ⟨hW, hre, h2⟩
        exact ⟨hW, hre, by omega⟩
  rw [hoff]
  ring

/-- Simple critical zeros are critical zero copies. -/
theorem N0s_le_N0 (T₁ T₂ : ℝ) : Z.N0s T₁ T₂ ≤ Z.N0 T₁ T₂ := by
  classical
  rw [N0s_eq_card_zeroWindowFinset, N0_eq_sum_zeroWindowFinset, Finset.card_eq_sum_ones]
  calc ∑ ρ ∈ (zeroWindowFinset Z T₁ T₂).filter (fun ρ => ρ.re = 1 / 2 ∧ Z.mult ρ = 1), 1
      = ∑ ρ ∈ (zeroWindowFinset Z T₁ T₂).filter (fun ρ => ρ.re = 1 / 2 ∧ Z.mult ρ = 1),
          Z.mult ρ :=
        Finset.sum_congr rfl fun ρ hρ => ((Finset.mem_filter.mp hρ).2.2).symm
    _ ≤ ∑ ρ ∈ (zeroWindowFinset Z T₁ T₂).filter (fun ρ => ρ.re = 1 / 2), Z.mult ρ := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => Nat.zero_le _
        intro ρ hρ
        simp only [Finset.mem_filter] at hρ ⊢
        exact ⟨hρ.1, hρ.2.1⟩

/-- Every window multiplicity is at least one. -/
lemma one_le_mult_of_mem_window {T₁ T₂ : ℝ} {ρ : ℂ} (hρ : ρ ∈ Z.window T₁ T₂) : 1 ≤ Z.mult ρ :=
  Z.one_le_mult ρ hρ.1

/-- Off-line multiple mass is monotone in the window. -/
theorem offLineMultipleMass_mono {T₁ T₂ T₁' T₂' : ℝ} (h₁ : T₁' ≤ T₁) (h₂ : T₂ ≤ T₂') :
    offLineMultipleMass Z T₁ T₂ ≤ offLineMultipleMass Z T₁' T₂' := by
  classical
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => Nat.zero_le _
  intro ρ hρ
  simp only [Finset.mem_filter, mem_zeroWindowFinset, ZeroConfig.window, Set.mem_inter_iff,
    Set.mem_setOf_eq] at hρ ⊢
  exact ⟨⟨hρ.1.1, by linarith [hρ.1.2.1], by linarith [hρ.1.2.2]⟩, hρ.2⟩

end Window

/-! ## The concrete Gram: keeping the excess in the `c = 2` seam -/

section Seam

variable {Z : ZeroConfig} {P : Params} {T : ℝ}

/-- The block data of `𝒵(I′)` sees exactly the off-line multiple mass of the window `I′`. -/
lemma blockOffLineMultipleMass_mkData (Z : ZeroConfig) (hconj : PhiHatConj T P) :
    blockOffLineMultipleMass (mkData Z T (evalVec Z T P) (evalVec_reflect hconj)) =
      offLineMultipleMass Z (T - D0 T) (2 * T + D0 T) := by
  classical
  unfold blockOffLineMultipleMass offLineMultipleMass
  have h := sum_filter_coe (ZI Z T) (fun ρ => ρ.re ≠ 1 / 2 ∧ 2 ≤ Z.mult ρ)
    (fun z => ¬ (mkData Z T (evalVec Z T P) (evalVec_reflect hconj)).σ z = z ∧
      2 ≤ (mkData Z T (evalVec Z T P) (evalVec_reflect hconj)).m z)
    (fun z => by rw [mkData_σ_eq_iff, mkData_m]) (fun ρ => Z.mult ρ)
  convert h using 2 <;> first
    | rfl
    | (ext; simp [mem_zeroWindowFinset, mem_ZI, ZeroConfig.ZIprime])

/-- **The `c = 2` certificate with the excess retained**:
`4 tr Â − ‖Â‖_F² − 2N(I′) + M_off(I′) ≤ s₁(I′)`. -/
theorem hatAz_mult2_offLineMultiple (Z : ZeroConfig) (hconj : PhiHatConj T P)
    (hreal : PhiHatReal T P)
    (hPois : PoissonSq T P) (hc : 0 < P.a T * P.L T ^ 2) :
    4 * rtrace (P.hat T (Z.Az P T)) - frobSq (P.hat T (Z.Az P T)) - 2 * (Z.NIprime T : ℝ)
      + (offLineMultipleMass Z (T - D0 T) (2 * T + D0 T) : ℝ) ≤ (Z.s1 T : ℝ) := by
  rw [hat_Az_eq_hatP_add_hatQ Z T P hconj, NIprime_eq_mk Z T _ (evalVec_reflect hconj),
    s1_eq_mk Z T _ (evalVec_reflect hconj), ← blockOffLineMultipleMass_mkData Z hconj]
  unfold hatP hatQ blockData
  have hraw := four_rtrace_sub_frobSq_le_block _ (mkPairReps Z T _ (evalVec_reflect hconj)) hc
    (sum_normSq_v_le Z T P hconj hreal hPois)
  have hmass := blockOffLineMultipleMass_add_le
    (mkData Z T (evalVec Z T P) (evalVec_reflect hconj)) (mkPairReps Z T _ (evalVec_reflect hconj))
  have hmass' : (blockOffLineMultipleMass (mkData Z T (evalVec Z T P) (evalVec_reflect hconj)) : ℝ)
      + 2 * ((mkData Z T (evalVec Z T P) (evalVec_reflect hconj)).s₁ +
        2 * (mkData Z T (evalVec Z T P) (evalVec_reflect hconj)).s₂ +
        2 * (mkPairReps Z T _ (evalVec_reflect hconj)).p : ℝ) ≤
      2 * ((mkData Z T (evalVec Z T P) (evalVec_reflect hconj)).Ncount : ℝ) := by
    exact_mod_cast hmass
  linarith

/-- **Seam A with the off-line multiple mass**: on the dyadic window,
`4 tr Ĝ − ‖Ĝ‖² − 2N − 3N_II − B(4 + 2√‖Ĝ‖² + B) ≤ N₀ˢ(T,2T) − M_off(T,2T)`. -/
theorem seamA_mult2_offLineMultiple (hT : 0 ≤ T) (hconj : PhiHatConj T P)
    (hreal : PhiHatReal T P) (hPois : PoissonSq T P)
    {θ₀ : ℝ} (hTl : TailInputs Z P T θ₀) (ha : 0 < P.a T) (hL : 0 < P.L T) :
    4 * rtrace (P.hat T (Z.Gz P T)) - frobSq (P.hat T (Z.Gz P T)) - 2 * (Z.N T (2 * T) : ℝ)
      - 3 * (NII Z T : ℝ)
      - θ₀ / (P.a T * P.L T)
          * (4 + 2 * Real.sqrt (frobSq (P.hat T (Z.Gz P T))) + θ₀ / (P.a T * P.L T))
      ≤ (Z.N0s T (2 * T) : ℝ) - (offLineMultipleMass Z T (2 * T) : ℝ) := by
  obtain ⟨Bc, hB0, htrE, hfrE, hBle⟩ := hTl.hat
  have hGAE : P.hat T (Z.Gz P T) = P.hat T (Z.Az P T) + P.hat T (Z.Ez P T) := by
    rw [← hat_add]; congr 1; simp [ZeroConfig.Ez]
  have hB₀ : 0 ≤ θ₀ / (P.a T * P.L T) := div_nonneg hTl.theta_nonneg (mul_pos ha hL).le
  have hcore := hatAz_mult2_offLineMultiple Z hconj hreal hPois (mul_pos ha (pow_pos hL 2))
  have hpert := ctr_sub_frobSq_perturb 4 (by norm_num) hGAE hB₀ (htrE.trans hBle)
    (hfrE.trans (pow_le_pow_left₀ hB0 hBle 2))
  have hs1 : (Z.s1 T : ℝ) ≤ (Z.N0s T (2 * T) : ℝ) + (NII Z T : ℝ) := by
    exact_mod_cast s1_le Z hT
  have hNI : (Z.NIprime T : ℝ) = (Z.N T (2 * T) : ℝ) + (NII Z T : ℝ) := by
    exact_mod_cast NIprime_eq Z hT
  have hmono : (offLineMultipleMass Z T (2 * T) : ℝ) ≤
      (offLineMultipleMass Z (T - D0 T) (2 * T + D0 T) : ℝ) := by
    exact_mod_cast offLineMultipleMass_mono Z (by linarith [D0_nonneg T])
      (by linarith [D0_nonneg T])
  rw [hNI] at hcore
  linarith [hcore, hpert, hs1]

end Seam

/-! ## The asymptotic certificate -/

section Abstract

variable (Z : ZeroConfig) (H : PaperInputs Z) (P : Params) (hP : P.Valid) (hlam : P.lam < 1)
  (hTr : ThmTracesHyp P Z)

include H hP hlam hTr in
/-- **Multiplicity-refined Theorem B at fixed `λ ∈ (0,1)`**:
`(H(λ) − ε)·N(T,2T) ≤ N₀ˢ(T,2T) − M_off(T,2T)`.  Same moments as `Zeta23.thmBmult_abstract`;
only the zero-side lower count changes. -/
theorem thmBmult_offLineMultiple_abstract :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (Hfun P.lam - ε) * (Z.N T (2 * T) : ℝ)
      ≤ (Z.N0s T (2 * T) : ℝ) - (offLineMultipleMass Z T (2 * T) : ℝ) := by
  have hlam0 := hP.lam_pos
  have hlam1 : P.lam ≤ 1 := hlam.le
  obtain ⟨hGzGp, ha, hNII, -⟩ := Zeta23.eventually_side_conditions Z H P hP
  obtain ⟨θ₀, hTail, Cθ, hθ⟩ := Zeta23.Tail.eventually_tailPackage Z H P hP
  obtain ⟨htrace, hfrob⟩ := Zeta23.moments_of_traces Z H P hP hlam hTr hGzGp ha
  have hLtop := Zeta23.Assembly.tendsto_L_atTop P hlam0
  have hapos : ∀ᶠ T in atTop, 1 / 2 ≤ P.a T := by
    filter_upwards [ha, hLtop.eventually_ge_atTop (4 * P.w)] with T h hL4
    have hw := hP.one_le_w
    have hLpos : 0 < P.L T := by linarith
    have : 2 * P.w / P.L T ≤ 1 / 2 := by rw [div_le_iff₀ hLpos]; linarith
    linarith [h.1]
  have hwL : ∀ᶠ T in atTop, 8 * P.w ≤ P.L T := hLtop.eventually_ge_atTop _
  have h0 : ∀ᶠ T in atTop, 4 * rtrace (P.hat T (Z.Gz P T)) - frobSq (P.hat T (Z.Gz P T))
      - 2 * (Z.N T (2 * T) : ℝ) - 3 * (NII Z T : ℝ)
      - θ₀ T / (P.a T * P.L T)
          * (4 + 2 * Real.sqrt (frobSq (P.hat T (Z.Gz P T))) + θ₀ T / (P.a T * P.L T))
      ≤ (Z.N0s T (2 * T) : ℝ) - (offLineMultipleMass Z T (2 * T) : ℝ) := by
    filter_upwards [hTail, hwL, hapos, eventually_ge_atTop (0:ℝ),
      Zeta23.Assembly.eventually_l_pos] with T hTl h8 ha2 hT0 hl
    have hLpos : 0 < P.L T := by simp only [Params.L]; positivity
    exact seamA_mult2_offLineMultiple hT0 Zeta23.ZeroSide.phiHatConj Zeta23.ZeroSide.phiHatReal
      (Zeta23.ZeroSide.poissonSq hP h8) hTl (by linarith) hLpos
  have hB0 : ∀ᶠ T in atTop, 0 ≤ θ₀ T / (P.a T * P.L T) := by
    filter_upwards [hTail, hapos, Zeta23.Assembly.eventually_l_pos] with T hTl ha2 hl
    have hLpos : 0 < P.L T := by simp only [Params.L]; positivity
    exact div_nonneg hTl.theta_nonneg (by positivity)
  have hBto : Tendsto (fun T => θ₀ T / (P.a T * P.L T)) atTop (𝓝 0) := by
    have hup : Tendsto (fun T => 2 * |Cθ| * (l T * T ^ (P.lam / 2 - 1) / P.L T)) atTop (𝓝 0) := by
      simpa using (Zeta23.Assembly.tendsto_theta_over_L P hlam0 hlam1).const_mul (2 * |Cθ|)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup hB0 ?_
    filter_upwards [hTail, hapos, Zeta23.Assembly.eventually_l_pos, hθ, eventually_gt_atTop (0:ℝ)]
      with T hTl ha2 hl hθT hT0
    have hLpos : 0 < P.L T := by simp only [Params.L]; positivity
    have hapos' : 0 < P.a T := by linarith
    have hq' : 0 ≤ l T * T ^ (P.lam / 2 - 1) / P.L T := by positivity
    rw [div_le_iff₀ (mul_pos hapos' hLpos)]
    calc θ₀ T ≤ Cθ * l T * T ^ (P.lam / 2 - 1) := hθT
      _ ≤ |Cθ| * l T * T ^ (P.lam / 2 - 1) := by gcongr; exact le_abs_self _
      _ = |Cθ| * (l T * T ^ (P.lam / 2 - 1) / P.L T) * P.L T := by field_simp
      _ ≤ (2 * |Cθ| * (l T * T ^ (P.lam / 2 - 1) / P.L T)) * (P.a T * P.L T) := by
          have e : |Cθ| * (l T * T ^ (P.lam / 2 - 1) / P.L T) * P.L T
              = (2 * |Cθ| * (l T * T ^ (P.lam / 2 - 1) / P.L T)) * (1 / 2 * P.L T) := by ring
          rw [e]; gcongr
  have hNII_o : (fun T => (NII Z T : ℝ)) =o[atTop] (fun T => (Z.N T (2 * T) : ℝ)) := by
    obtain ⟨CII, hII⟩ := hNII
    have hO : (fun T => (NII Z T : ℝ)) =O[atTop] (fun T => Real.sqrt T * l T) := by
      refine IsBigO.of_bound CII ?_
      filter_upwards [hII, Zeta23.Assembly.eventually_l_pos] with T h hl
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _),
        abs_of_nonneg (by positivity)]
      simpa [mul_assoc] using h
    exact hO.trans_isLittleO (Zeta23.Assembly.isLittleO_N_of_isLittleO_Tl Z H.RvM
      Zeta23.Assembly.isLittleO_sqrt_mul_l_Tl)
  have hNtop := Zeta23.Assembly.tendsto_N_atTop Z H.RvM
  have h := Zeta23.Assembly.count_certificate Z P (kfun P.lam)
    (fun T => (Z.N0s T (2 * T) : ℝ) - (offLineMultipleMass Z T (2 * T) : ℝ)) θ₀ h0 hB0 hBto
    hNII_o hNtop htrace hfrob
  simpa only [Hfun_eq_two_sub_kfun] using h

end Abstract

/-! ## ζ: off-line multiple zeros, and the simple off-line core of three quarters -/

section Zeta

/-- Multiplicity-refined Theorem B for `ζ` at fixed `λ ∈ (0,1)`, unconditional. -/
theorem thmB_mult_offLineMultiple_lam {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (Hfun lam - ε) * (Ncount T (2 * T) : ℝ) ≤
        (N0simple T (2 * T) : ℝ) - (offLineMultipleMass zetaZeroConfig T (2 * T) : ℝ) := by
  have hP := paramsOf_valid taperProfile_stdProfile h0 h1.le
  exact thmBmult_offLineMultiple_abstract zetaZeroConfig paperInputs_zeta
    (paramsOf stdProfile lam) hP h1 (PrimeSide.thm_traces hP paperInputs_zeta)

/-- **Off-line multiple zeros are charged twice by the two-thirds certificate**, unconditional:
`(2/3 − ε)·N(T,2T) + M_off(T,2T) ≤ N₀ˢ(T,2T)`. -/
theorem two_thirds_add_offLineMultipleMass_le_N0simple :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (2 / 3 - ε) * (Ncount T (2 * T) : ℝ) + (offLineMultipleMass zetaZeroConfig T (2 * T) : ℝ)
        ≤ N0simple T (2 * T) := by
  have h := eps_form_twoThirds (N := fun T => (Ncount T (2 * T) : ℝ))
    (lower := fun T =>
      (N0simple T (2 * T) : ℝ) - (offLineMultipleMass zetaZeroConfig T (2 * T) : ℝ))
    (fun _ => Nat.cast_nonneg _) fun lam hl1 hl2 =>
      thmB_mult_offLineMultiple_lam (by linarith) hl2
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := h ε hε
  exact ⟨T₀, fun T hT => by have := hT₀ T hT; linarith⟩

/-- The window census of `ζ`: `N = N₀ + S_off + M_off`. -/
lemma zeta_N_eq_N0_add_offLineSimple_add_offLineMultiple (T₁ T₂ : ℝ) :
    (Ncount T₁ T₂ : ℝ) = (N0 T₁ T₂ : ℝ) + (offLineSimpleCount zetaZeroConfig T₁ T₂ : ℝ)
      + (offLineMultipleMass zetaZeroConfig T₁ T₂ : ℝ) := by
  have h := N_eq_N0_add_offLineSimple_add_offLineMultiple zetaZeroConfig T₁ T₂
  rw [zetaZeroConfig_N] at h
  have h0 : zetaZeroConfig.N0 T₁ T₂ = N0 T₁ T₂ := zetaZeros_N0 zetaSeam T₁ T₂
  rw [h0] at h
  exact_mod_cast h

/-- `N₀ˢ ≤ N₀` for `ζ`. -/
lemma zeta_N0simple_le_N0 (T₁ T₂ : ℝ) : N0simple T₁ T₂ ≤ N0 T₁ T₂ :=
  (trivial_chain₀ T₁ T₂).1.trans (trivial_chain₀ T₁ T₂).2.1

/-- **At most `(1/6 + ε)N` zero copies are off-line and multiple**: at least `(5/6 − ε)N` of the
zero copies of `ζ` in `(T, 2T]` are simple or lie on the critical line. -/
theorem offLineMultipleMass_le_one_sixth :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (offLineMultipleMass zetaZeroConfig T (2 * T) : ℝ) ≤ (1 / 6 + ε) * (Ncount T (2 * T) : ℝ) := by
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := two_thirds_add_offLineMultipleMass_le_N0simple (2 * ε) (by linarith)
  refine ⟨T₀, fun T hT => ?_⟩
  have h := hT₀ T hT
  have hN := zeta_N_eq_N0_add_offLineSimple_add_offLineMultiple T (2 * T)
  have hs : (N0simple T (2 * T) : ℝ) ≤ N0 T (2 * T) := by exact_mod_cast zeta_N0simple_le_N0 _ _
  have hS : (0 : ℝ) ≤ offLineSimpleCount zetaZeroConfig T (2 * T) := Nat.cast_nonneg _
  linarith

/-- **Simple off-line zeros plus twice the off-line multiple mass are at most `(1/3 + ε)N`**. -/
theorem offLineSimple_add_two_offLineMultiple_le_one_third :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (offLineSimpleCount zetaZeroConfig T (2 * T) : ℝ)
          + 2 * (offLineMultipleMass zetaZeroConfig T (2 * T) : ℝ)
        ≤ (1 / 3 + ε) * (Ncount T (2 * T) : ℝ) := by
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := two_thirds_add_offLineMultipleMass_le_N0simple ε hε
  refine ⟨T₀, fun T hT => ?_⟩
  have h := hT₀ T hT
  have hN := zeta_N_eq_N0_add_offLineSimple_add_offLineMultiple T (2 * T)
  have hs : (N0simple T (2 * T) : ℝ) ≤ N0 T (2 * T) := by exact_mod_cast zeta_N0simple_le_N0 _ _
  linarith

/-- **The simple off-line core of the three-quarters problem**, unconditional: in every large
dyadic window either at least three quarters of the zero copies of `ζ` lie on the critical line,
or at least `(1/6 − ε)N` of them are simple off-line zeros. -/
theorem three_quarters_or_simple_offLine :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      3 / 4 * (Ncount T (2 * T) : ℝ) ≤ N0 T (2 * T) ∨
        (1 / 6 - ε) * (Ncount T (2 * T) : ℝ) ≤ offLineSimpleCount zetaZeroConfig T (2 * T) := by
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := offLineSimple_add_two_offLineMultiple_le_one_third ε hε
  refine ⟨T₀, fun T hT => ?_⟩
  have h := hT₀ T hT
  have hN := zeta_N_eq_N0_add_offLineSimple_add_offLineMultiple T (2 * T)
  by_cases h34 : 3 / 4 * (Ncount T (2 * T) : ℝ) ≤ N0 T (2 * T)
  · exact Or.inl h34
  · right
    push Not at h34
    linarith

end Zeta

end RHTower

end
