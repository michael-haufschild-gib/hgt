import GaloisForLFunctions.RHTower.Zeta23OffLineMultipleExclusionMontgomeryTaylor

/-!
# Simple or critical zeros: the `c = 3` census

The `c = 3` multiplicity-aware rank–trace inequality of Alpöge–Furman,
`6 tr Â − ‖Â‖_F² ≤ 5a₁ + 8a₂ + 9a₃ + 9p` (`a_k` on-line points of multiplicity `k`, resp. `≥ 3`;
`p` off-line pairs), prices an off-line pair of multiplicity `m` at `10m − 9 ≥ (11/2)m` units of the
budget `5N − (6 tr Â − ‖Â‖_F²)`.  Hence the off-line multiple mass `M_off` satisfies

`(GD(1) − ε)·N(T,2T) ≤ N(T,2T) − (11/8)·M_off(T,2T)`,   `GD(1) = (3 − 1/c₁*)/2 = 0.83625…`,

so at least `((3 + 8·GD(1))/11 − ε)N ≈ 0.881N` zero copies of `ζ` are simple or on the critical
line.  With the flat window the constant is `29/33`.  Unconditional.
-/

open Filter Asymptotics Topology Real RHLinalg Finset
open scoped BigOperators ComplexOrder

noncomputable section

namespace RHTower

open Zeta23 Zeta23.Assembly

/-! ## Block level -/

section Block

open Zeta23.ZeroSide Zeta23.ZeroSide.RankTraceMult

variable {ι d : Type*} [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d]

/-- The raw `c = 3` rank–trace inequality `6 tr Â − ‖Â‖_F² ≤ 5a₁ + 8a₂ + 9a₃ + 9p`. -/
theorem six_rtrace_sub_frobSq_le_block (D : ZeroBlockData ι d) (Pr : D.PairReps)
    {c : ℝ} (hc : 0 < c) (hPois : ∀ z ∈ D.onLine, ∑ k, ‖D.v z k‖ ^ (2 : ℕ) ≤ c) :
    6 * rtrace (D.blockP c + D.blockQ c) - frobSq (D.blockP c + D.blockQ c) ≤
      5 * ((D.onLine.filter (fun z => D.m z = 1)).card : ℝ)
        + 8 * ((D.onLine.filter (fun z => D.m z = 2)).card : ℝ)
        + 9 * ((D.onLine.filter (fun z => 3 ≤ D.m z)).card : ℝ) + 9 * (Pr.p : ℝ) := by
  classical
  have hR := rank_trace_mult_k_le (𝕜 := ℂ) (fun z => D.mhat_nonneg z) (D.vhat c)
    (D.xsq_vhat_le hc hPois) (D.blockQ_isHermitian c) (D.posIndex_blockQ_le Pr hc)
    (c := 3) (by norm_num)
  rw [← D.blockP_eq_Pmat hc] at hR
  have hk : ∑ z : D.onLine, kc 3 (D.mhat z) =
      5 * ((D.onLine.filter (fun z => D.m z = 1)).card : ℝ)
        + 8 * ((D.onLine.filter (fun z => D.m z = 2)).card : ℝ)
        + 9 * ((D.onLine.filter (fun z => 3 ≤ D.m z)).card : ℝ) := by
    have := sum_kc_three_nat (fun z : D.onLine => D.m z) (fun z => D.one_le_m z)
    simp only [ZeroBlockData.mhat] at this ⊢
    rw [this, D.card_sub_filter (fun n => n = 1), D.card_sub_filter (fun n => n = 2),
      D.card_sub_filter (fun n => 3 ≤ n)]
  rw [hk] at hR
  norm_num at hR
  linarith

/-- An off-line pair of multiplicity `m` uses `10m − 9 ≥ (11/2)m` of the `c = 3` budget:
`4(5a₁ + 8a₂ + 9a₃ + 9p) + 11·M_off ≤ 20N`. -/
theorem c3_budget_add_offLineMultipleMass_le (D : ZeroBlockData ι d) (Pr : D.PairReps) :
    4 * (5 * ((D.onLine.filter (fun z => D.m z = 1)).card : ℝ)
        + 8 * ((D.onLine.filter (fun z => D.m z = 2)).card : ℝ)
        + 9 * ((D.onLine.filter (fun z => 3 ≤ D.m z)).card : ℝ) + 9 * (Pr.p : ℝ))
      + 11 * (blockOffLineMultipleMass D : ℝ) ≤ 20 * (D.Ncount : ℝ) := by
  classical
  -- the census splits into on-line points and reflected pairs
  have hN : D.Ncount = D.Non + ∑ z ∈ Pr.R, 2 * D.m z := by
    unfold ZeroBlockData.Ncount ZeroBlockData.Non
    rw [D.sum_split Pr (fun z => D.m z)]
    congr 1
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [D.m_σ z]; ring
  set g : ι → ℕ := fun z => if ¬ D.σ z = z ∧ 2 ≤ D.m z then D.m z else 0 with hg
  have hM : blockOffLineMultipleMass D = ∑ z ∈ Pr.R, 2 * (if 2 ≤ D.m z then D.m z else 0) := by
    have h1 : blockOffLineMultipleMass D = ∑ z, g z := by
      unfold blockOffLineMultipleMass
      rw [Finset.sum_filter]
    rw [h1, D.sum_split Pr g]
    have hon : ∑ z ∈ D.onLine, g z = 0 := by
      refine Finset.sum_eq_zero fun z hz => ?_
      have : D.σ z = z := (D.mem_onLine).mp hz
      simp [hg, this]
    rw [hon, zero_add]
    refine Finset.sum_congr rfl fun z hz => ?_
    have hoff : ¬ D.σ z = z := Pr.off z hz
    have hoff' : ¬ D.σ (D.σ z) = D.σ z := by
      rw [D.σ_invol z]; exact fun h => hoff h.symm
    simp only [hg, hoff, hoff', not_false_eq_true, true_and, D.m_σ z]
    ring
  have hpair : ∀ z ∈ Pr.R, 36 + 22 * (if 2 ≤ D.m z then D.m z else 0) ≤ 40 * D.m z := by
    intro z _
    have := D.one_le_m z
    split_ifs with h <;> omega
  have hsum := Finset.sum_le_sum hpair
  rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, ← Finset.mul_sum,
    ← Finset.mul_sum] at hsum
  have hp : Pr.R.card = Pr.p := rfl
  have hNon := D.Non_ge_weighted
  have hsumR : (∑ z ∈ Pr.R, 2 * D.m z : ℕ) * 20 = 40 * ∑ z ∈ Pr.R, D.m z := by
    rw [← Finset.mul_sum]; ring
  have hMR : (blockOffLineMultipleMass D : ℕ) * 11 =
      22 * ∑ z ∈ Pr.R, (if 2 ≤ D.m z then D.m z else 0) := by
    rw [hM, ← Finset.mul_sum]; ring
  have hnat : 36 * Pr.p + 11 * blockOffLineMultipleMass D ≤ 20 * ∑ z ∈ Pr.R, 2 * D.m z := by
    rw [hp] at hsum
    omega
  have hreal : 36 * (Pr.p : ℝ) + 11 * (blockOffLineMultipleMass D : ℝ)
      ≤ 20 * ((∑ z ∈ Pr.R, 2 * D.m z : ℕ) : ℝ) := by exact_mod_cast hnat
  have hNr : (D.Ncount : ℝ) = (D.Non : ℝ) + ((∑ z ∈ Pr.R, 2 * D.m z : ℕ) : ℝ) := by
    exact_mod_cast hN
  have h2 : (0 : ℝ) ≤ ((D.onLine.filter (fun z => D.m z = 2)).card : ℝ) := Nat.cast_nonneg _
  have h3 : (0 : ℝ) ≤ ((D.onLine.filter (fun z => 3 ≤ D.m z)).card : ℝ) := Nat.cast_nonneg _
  linarith

end Block

/-! ## The concrete Gram: the `c = 3` seam with the off-line multiple mass -/

section Seam

open Zeta23.ZeroSide

variable {Z : ZeroConfig} {P : Params} {T : ℝ}

/-- **The `c = 3` certificate with the off-line multiple mass**:
`6 tr Â − ‖Â‖_F² − 5N(I′) + (11/4)M_off(I′) ≤ 0`. -/
theorem hatAz_mult3_offLineMultiple (Z : ZeroConfig) (hconj : PhiHatConj T P)
    (hreal : PhiHatReal T P) (hPois : PoissonSq T P) (hc : 0 < P.a T * P.L T ^ 2) :
    6 * rtrace (P.hat T (Z.Az P T)) - frobSq (P.hat T (Z.Az P T)) - 5 * (Z.NIprime T : ℝ)
      + 11 / 4 * (offLineMultipleMass Z (T - D0 T) (2 * T + D0 T) : ℝ) ≤ 0 := by
  rw [hat_Az_eq_hatP_add_hatQ Z T P hconj, NIprime_eq_mk Z T _ (evalVec_reflect hconj),
    ← blockOffLineMultipleMass_mkData Z hconj]
  unfold hatP hatQ blockData
  have hraw := six_rtrace_sub_frobSq_le_block _ (mkPairReps Z T _ (evalVec_reflect hconj)) hc
    (sum_normSq_v_le Z T P hconj hreal hPois)
  have hbud := c3_budget_add_offLineMultipleMass_le
    (mkData Z T (evalVec Z T P) (evalVec_reflect hconj)) (mkPairReps Z T _ (evalVec_reflect hconj))
  linarith

/-- **Seam A, `c = 3`, with the off-line multiple mass**: on the dyadic window,
`6 tr Ĝ − ‖Ĝ‖² − 3N − 5N_II − B(6 + 2√‖Ĝ‖² + B) ≤ 2(N − (11/8)M_off)`. -/
theorem seamA_mult3_offLineMultiple (hT : 0 ≤ T) (hconj : PhiHatConj T P)
    (hreal : PhiHatReal T P) (hPois : PoissonSq T P)
    {θ₀ : ℝ} (hTl : TailInputs Z P T θ₀) (ha : 0 < P.a T) (hL : 0 < P.L T) :
    6 * rtrace (P.hat T (Z.Gz P T)) - frobSq (P.hat T (Z.Gz P T)) - 3 * (Z.N T (2 * T) : ℝ)
      - 5 * (NII Z T : ℝ)
      - θ₀ / (P.a T * P.L T)
          * (6 + 2 * Real.sqrt (frobSq (P.hat T (Z.Gz P T))) + θ₀ / (P.a T * P.L T))
      ≤ 2 * ((Z.N T (2 * T) : ℝ) - 11 / 8 * (offLineMultipleMass Z T (2 * T) : ℝ)) := by
  obtain ⟨Bc, hB0, htrE, hfrE, hBle⟩ := hTl.hat
  have hGAE : P.hat T (Z.Gz P T) = P.hat T (Z.Az P T) + P.hat T (Z.Ez P T) := by
    rw [← hat_add]; congr 1; simp [ZeroConfig.Ez]
  have hB₀ : 0 ≤ θ₀ / (P.a T * P.L T) := div_nonneg hTl.theta_nonneg (mul_pos ha hL).le
  have hcore := hatAz_mult3_offLineMultiple Z hconj hreal hPois (mul_pos ha (pow_pos hL 2))
  have hpert := ctr_sub_frobSq_perturb 6 (by norm_num) hGAE hB₀ (htrE.trans hBle)
    (hfrE.trans (pow_le_pow_left₀ hB0 hBle 2))
  have hNI : (Z.NIprime T : ℝ) = (Z.N T (2 * T) : ℝ) + (NII Z T : ℝ) := by
    exact_mod_cast NIprime_eq Z hT
  have hmono : (offLineMultipleMass Z T (2 * T) : ℝ) ≤
      (offLineMultipleMass Z (T - D0 T) (2 * T + D0 T) : ℝ) := by
    exact_mod_cast offLineMultipleMass_mono Z (by linarith [D0_nonneg T])
      (by linarith [D0_nonneg T])
  rw [hNI] at hcore
  linarith [hcore, hpert]

end Seam

/-! ## The Theorem-D endgame for the `c = 3` census -/

section TheoremD

open Zeta23.ThmD

/-- **Simple-or-critical census, Theorem-D window, abstract**:
`(3/2 − c⁻¹/2 − ε)N ≤ N − (11/8)M_off`. -/
theorem thmD_mult3_offLineMultiple_abstract (Z : ZeroConfig) (H : PaperInputs Z) (P : Params)
    (hP : P.Valid) (hlam : P.lam < 1)
    (aT bT JT trG trG2 : ℝ → ℝ)
    (hTr : TracesBoundsD P aT bT JT trG trG2 (fun T => (Z.N T (2 * T) : ℝ)))
    {c : ℝ} (hc0 : 0 < c)
    (hc : Tendsto (fun T => cRatio (P.lam1 T) (aT T) (bT T) (JT T)) atTop (𝓝 c))
    (ha : ∀ᶠ T in atTop, 1 / 2 ≤ aT T ∧ aT T ≤ 1)
    (θ₀ : ℝ → ℝ) (hTail : ∀ᶠ T in atTop, TailInputs Z (P.atD T) T (θ₀ T))
    (hθ₀ : ∃ C : ℝ, ∀ᶠ T in atTop, θ₀ T ≤ C * l T * T ^ (P.lam / 2 - 1))
    (hNII : ∃ C : ℝ, ∀ᶠ T in atTop, (NII Z T : ℝ) ≤ C * Real.sqrt T * l T)
    (hGzGp : ∀ᶠ T in atTop, Z.Gz (P.atD T) T = (P.atD T).Gp T)
    (hId : ∀ᶠ T in atTop, (P.atD T).trGtilde T = trG T ∧ (P.atD T).trGtildeSq T = trG2 T ∧
      (P.atD T).a T = aT T)
    (hcalE : Tendsto P.calE atTop (𝓝 0)) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (3 / 2 - c⁻¹ / 2 - ε) * (Z.N T (2 * T) : ℝ)
        ≤ (Z.N T (2 * T) : ℝ) - 11 / 8 * (offLineMultipleMass Z T (2 * T) : ℝ) := by
  intro ε hε
  have hlam0 := hP.lam_pos
  have hlam1 : P.lam ≤ 1 := hlam.le
  obtain ⟨C₁, hC₁, T₁, htr1⟩ := hTr.tr1
  obtain ⟨C₂, hC₂, T₂, hfr2⟩ := hTr.frhat
  obtain ⟨Cθ, hθ⟩ := hθ₀
  obtain ⟨CII, hII⟩ := hNII
  set N : ℝ → ℝ := fun T => (Z.N T (2 * T) : ℝ) with hNdef
  set cinv : ℝ → ℝ := fun T => (cRatio (P.lam1 T) (aT T) (bT T) (JT T))⁻¹ with hcinv
  set R₁ : ℝ → ℝ := fun T => C₁ * Real.sqrt (P.X T) / aT T with hR₁
  set R₂ : ℝ → ℝ := fun T => C₂ * P.calE T * (cinv T * N T) with hR₂
  set B : ℝ → ℝ := fun T => θ₀ T / (aT T * P.L T) with hBdef
  set err : ℝ → ℝ := fun T => (6 * R₁ T + R₂ T + 5 * (NII Z T : ℝ)
      + B T * (6 + 2 * Real.sqrt (cinv T * N T + R₂ T) + B T)) + |cinv T - c⁻¹| * N T with herr
  have hcinv_to : Tendsto cinv atTop (𝓝 c⁻¹) := hc.inv₀ hc0.ne'
  -- (1) the seam with the off-line multiple mass, eventually in `T`
  have hmain : ∀ᶠ T in atTop, (3 - c⁻¹) * N T - err T
      ≤ 2 * ((Z.N T (2 * T) : ℝ) - 11 / 8 * (offLineMultipleMass Z T (2 * T) : ℝ)) := by
    filter_upwards [hTail, hGzGp, hId, ha, eventually_ge_atTop T₁,
      eventually_ge_atTop T₂, eventually_ge_atTop (0:ℝ), eventually_l_pos,
      eventually_calE_nonneg P hlam0 (zero_le_one.trans hP.one_le_w), eventually_w8 hP]
      with T hTl hGG hid ha2 hT₁ hT₂ hT0 hl hE0 h8
    obtain ⟨hidtr, hidfr, hida⟩ := hid
    have hapos' : 0 < aT T := by linarith [ha2.1]
    have haposD : 0 < (P.atD T).a T := by rw [hida]; exact hapos'
    have hLpos : 0 < P.L T := by simp only [Params.L]; positivity
    have hA := seamA_mult3_offLineMultiple hT0 (fun z => GzGp.phiHat_conj _ T z)
      (fun r => GzGp.phiHat_ofReal _ T r) (poissonSqD hP h8) hTl haposD hLpos
    have hrt : rtrace ((P.atD T).hat T (Z.Gz (P.atD T) T)) = (aT T * P.L T)⁻¹ * trG T := by
      rw [rtrace_hat, hGG, rtrace_tilde_Gp, hidtr, hida]; rfl
    have hfr : frobSq ((P.atD T).hat T (Z.Gz (P.atD T) T))
        = ((aT T * P.L T)⁻¹) ^ 2 * trG2 T := by
      rw [frobSq_hat, hGG, frobSq_tilde_Gp, hidfr, hida]; rfl
    have haL : (P.atD T).a T * (P.atD T).L T = aT T * P.L T := by rw [hida]; rfl
    rw [hrt, hfr, haL] at hA
    have htr : |(aT T * P.L T)⁻¹ * trG T - N T| ≤ R₁ T :=
      trGhat_sub_N_le hapos' hLpos (by simpa only using htr1 T hT₁)
    have hfrb : ((aT T * P.L T)⁻¹) ^ 2 * trG2 T ≤ cinv T * N T + R₂ T := by
      have h := hfr2 T hT₂
      simp only at h
      have h1 : trG2 T / (aT T * P.L T) ^ 2 - cinv T * N T ≤ C₂ * P.calE T * (cinv T * N T) := by
        rw [← mul_assoc] at h
        exact le_trans (le_trans (le_max_left _ 0) (le_abs_self _)) h
      have e : ((aT T * P.L T)⁻¹) ^ 2 * trG2 T = trG2 T / (aT T * P.L T) ^ 2 := by
        rw [inv_pow, div_eq_inv_mul]
      rw [e]; simp only [hR₂]; linarith
    have hB₀ : 0 ≤ B T := div_nonneg hTl.theta_nonneg (mul_pos hapos' hLpos).le
    have h := Nd_lower_c3 hB₀ hA htr hfrb
    have hN0 : 0 ≤ N T := Nat.cast_nonneg _
    have hcd : (3 - c⁻¹) * N T - |cinv T - c⁻¹| * N T ≤ (3 - cinv T) * N T := by
      have h1 := mul_le_mul_of_nonneg_right (le_abs_self (cinv T - c⁻¹)) hN0
      linarith [h1]
    simp only [herr, hR₁, hR₂, hBdef, hNdef] at h hcd ⊢
    linarith
  -- (2) `err = o(N)`, exactly as in the Theorem-D endgame
  have hNtop : Tendsto N atTop atTop := tendsto_N_atTop Z H.RvM
  have o1 : R₁ =o[atTop] N := by
    have hbd : (fun T => C₁ / aT T) =O[atTop] (fun _ => (1:ℝ)) := by
      refine isBigO_one_of_abs_le (C := 2 * C₁) ?_
      filter_upwards [ha] with T ha2
      rw [abs_of_nonneg (div_nonneg hC₁.le (by linarith [ha2.1]))]
      rw [div_le_iff₀ (by linarith [ha2.1])]; nlinarith [ha2.1]
    have := isLittleO_of_bdd_mul hbd
      (isLittleO_N_of_isLittleO_Tl Z H.RvM (isLittleO_sqrtX_Tl P hlam0 hlam1))
    exact this.congr_left fun T => by simp only [hR₁]; ring
  have hcinv_bd : ∀ᶠ T in atTop, 0 ≤ cinv T ∧ cinv T ≤ 2 * c⁻¹ := by
    have hcpos : (0:ℝ) < c⁻¹ := inv_pos.mpr hc0
    filter_upwards [hcinv_to.eventually (eventually_ge_nhds hcpos),
      hcinv_to.eventually (eventually_le_nhds (show c⁻¹ < 2 * c⁻¹ by linarith))] with T h1 h2
    exact ⟨h1, h2⟩
  have hcinvO : cinv =O[atTop] (fun _ => (1:ℝ)) := by
    refine isBigO_one_of_abs_le (C := 2 * c⁻¹) ?_
    filter_upwards [hcinv_bd] with T h
    rw [abs_of_nonneg h.1]; exact h.2
  have o2 : R₂ =o[atTop] N := by
    have hcE0 : Tendsto (fun T => C₂ * P.calE T) atTop (𝓝 0) := by
      simpa using hcalE.const_mul C₂
    have i1 : (fun T => cinv T * N T) =O[atTop] N := by
      have := hcinvO.mul (isBigO_refl N atTop)
      simpa using this
    have := ((isLittleO_one_iff ℝ).2 hcE0).mul_isBigO i1
    refine (this.congr_left fun T => ?_).congr_right fun T => by simp
    simp only [hR₂]
  have o3 : (fun T => (NII Z T : ℝ)) =o[atTop] N := by
    have hO : (fun T => (NII Z T : ℝ)) =O[atTop] (fun T => Real.sqrt T * l T) := by
      refine IsBigO.of_bound CII ?_
      filter_upwards [hII, eventually_l_pos] with T h hl
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _),
        abs_of_nonneg (by positivity)]
      simpa [mul_assoc] using h
    exact hO.trans_isLittleO (isLittleO_N_of_isLittleO_Tl Z H.RvM isLittleO_sqrt_mul_l_Tl)
  have o4 : Tendsto B atTop (𝓝 0) := by
    have hup : Tendsto (fun T => 2 * |Cθ| * (l T * T ^ (P.lam / 2 - 1) / P.L T)) atTop (𝓝 0) := by
      simpa using (tendsto_theta_over_L P hlam0 hlam1).const_mul (2 * |Cθ|)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
    · filter_upwards [hTail, ha, eventually_l_pos] with T hTl ha2 hl
      have hLpos : 0 < P.L T := by simp only [Params.L]; positivity
      exact div_nonneg hTl.theta_nonneg (by nlinarith [ha2.1])
    · filter_upwards [hTail, ha, eventually_l_pos, hθ, eventually_gt_atTop (0:ℝ)]
        with T hTl ha2 hl hθT hT0
      have hLpos : 0 < P.L T := by simp only [Params.L]; positivity
      have hapos' : 0 < aT T := by linarith [ha2.1]
      have hq : 0 ≤ l T * T ^ (P.lam / 2 - 1) / P.L T := by positivity
      simp only [hBdef]
      rw [div_le_iff₀ (mul_pos hapos' hLpos)]
      calc θ₀ T ≤ Cθ * l T * T ^ (P.lam / 2 - 1) := hθT
        _ ≤ |Cθ| * l T * T ^ (P.lam / 2 - 1) := by gcongr; exact le_abs_self _
        _ = |Cθ| * (l T * T ^ (P.lam / 2 - 1) / P.L T) * P.L T := by field_simp
        _ ≤ (2 * |Cθ| * (l T * T ^ (P.lam / 2 - 1) / P.L T)) * (aT T * P.L T) := by
          have : |Cθ| * (l T * T ^ (P.lam / 2 - 1) / P.L T) * P.L T
              = (2 * |Cθ| * (l T * T ^ (P.lam / 2 - 1) / P.L T)) * (1 / 2 * P.L T) := by ring
          rw [this]; gcongr; exact ha2.1
  have o5 := err_isLittleO (R₁ := R₁) (R₂ := R₂) (NII := fun T => (NII Z T : ℝ)) (B := B)
    (cl := cinv) hNtop o1 o2 o3 o4 hcinv_bd
  have o6 : (fun T => |cinv T - c⁻¹| * N T) =o[atTop] N := by
    refine isLittleO_of_tendsto_zero_mul ?_
    have : Tendsto (fun T => cinv T - c⁻¹) atTop (𝓝 0) := by
      simpa using hcinv_to.sub_const c⁻¹
    simpa using this.abs
  have oB : B =o[atTop] N := by
    refine ((isLittleO_one_iff ℝ).2 o4).trans_isBigO (IsBigO.of_bound 1 ?_)
    filter_upwards [hNtop.eventually_ge_atTop 1] with T h1
    rw [norm_one, Real.norm_eq_abs, abs_of_nonneg (by linarith), one_mul]; exact h1
  have o5' : (fun T => 6 * R₁ T + R₂ T + 5 * (NII Z T : ℝ)
      + B T * (6 + 2 * Real.sqrt (cinv T * N T + R₂ T) + B T)) =o[atTop] N := by
    have := o5.add (((o1.const_mul_left 2).add (o3.const_mul_left 2)).add (oB.const_mul_left 2))
    exact this.congr_left fun T => by ring
  have herr_o : err =o[atTop] N := o5'.add o6
  -- (3) conclude (halve)
  have hfin := eps_form_of_isLittleO hmain (Eventually.of_forall fun T => Nat.cast_nonneg _) herr_o
    (2 * ε) (by linarith)
  obtain ⟨T₀, hT₀⟩ := hfin
  exact ⟨T₀, fun T hT => by have := hT₀ T hT; linarith⟩

/-- Simple-or-critical census at fixed `λ ∈ (0,1)`, abstract zero configuration. -/
theorem thmD_simpleOrCritical_lam_abstract (Z : ZeroConfig) (H : PaperInputs Z) (P : Params)
    (hP : P.Valid) (hlam : P.lam < 1) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (GD P.lam - ε) * (Z.N T (2 * T) : ℝ)
      ≤ (Z.N T (2 * T) : ℝ) - 11 / 8 * (offLineMultipleMass Z T (2 * T) : ℝ) := by
  have hLoc : LocalHypsCoreDEventually P := localHypsCoreD_eventually hP
  have hTr := tracesBoundsD_concrete (Z := Z) hP H hLoc
  have hc := tendsto_cRatio_concrete hP Z
  have hc0 := cStar_pos hP.lam_pos hP.lam_le_one
  have ha : ∀ᶠ T in atTop, 1 / 2 ≤ (concreteDataD P Z).aT T ∧ (concreteDataD P Z).aT T ≤ 1 :=
    (concreteFactsD hP H hLoc).ab_range.mono fun T h => ⟨h.1.trans h.2.1, h.2.2.1⟩
  obtain ⟨θ₀, hTail, hθ₀⟩ := eventually_tailPackageD Z H hP
  obtain ⟨A₀, hA₀, hloc⟩ := H.RvM.local_count
  have hNII := Tail.eventually_NII_le Z hA₀ hloc
  have hGzGp := eventually_GzGpD Z H hP
  have hId : ∀ᶠ T in atTop,
      (P.atD T).trGtilde T = (concreteDataD P Z).trG T ∧
      (P.atD T).trGtildeSq T = (concreteDataD P Z).trG2 T ∧
      (P.atD T).a T = (concreteDataD P Z).aT T :=
    Eventually.of_forall fun T =>
      ⟨Params.atD_trGtilde T hP, Params.atD_trGtildeSq T hP, Params.atD_a T hP⟩
  have hcalE := calE_tendsto_zero P hP.lam_pos hP.lam_le_one (zero_le_one.trans hP.one_le_w)
  have h := thmD_mult3_offLineMultiple_abstract Z H P hP hlam _ _ _ _ _ hTr hc0 hc ha θ₀ hTail
    hθ₀ hNII hGzGp hId hcalE
  simpa only [GD] using h

/-- Simple-or-critical census for `ζ` at fixed `λ ∈ (0,1)`, unconditional. -/
theorem thmD_simpleOrCritical_lam {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (GD lam - ε) * (Ncount T (2 * T) : ℝ)
      ≤ (Ncount T (2 * T) : ℝ) - 11 / 8 * (offLineMultipleMass zetaZeroConfig T (2 * T) : ℝ) := by
  have hP := paramsOf_valid taperProfile_stdProfile h0 h1.le
  exact thmD_simpleOrCritical_lam_abstract zetaZeroConfig paperInputs_zeta
    (paramsOf stdProfile lam) hP h1

/-- `(GD(1) − ε)N ≤ N − (11/8)M_off` for `ζ`, unconditional. -/
theorem GD_one_le_N_sub_offLineMultipleMass :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (GD 1 - ε) * (Ncount T (2 * T) : ℝ)
      ≤ (Ncount T (2 * T) : ℝ) - 11 / 8 * (offLineMultipleMass zetaZeroConfig T (2 * T) : ℝ) := by
  -- `GD = (HD + 1)/2`: run `eps_form_HD` on `2(N − (11/8)M) − N`
  have h := eps_form_HD (N := fun T => (Ncount T (2 * T) : ℝ))
    (lower := fun T => 2 * ((Ncount T (2 * T) : ℝ)
      - 11 / 8 * (offLineMultipleMass zetaZeroConfig T (2 * T) : ℝ)) - (Ncount T (2 * T) : ℝ))
    (fun _ => Nat.cast_nonneg _) (fun lam hl1 hl2 ε hε => by
      obtain ⟨T₀, hT₀⟩ := thmD_simpleOrCritical_lam (by linarith) hl2 (ε / 2) (by linarith)
      refine ⟨T₀, fun T hT => ?_⟩
      have := hT₀ T hT
      rw [GD_eq] at this
      linarith)
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := h (2 * ε) (by linarith)
  refine ⟨T₀, fun T hT => ?_⟩
  have := hT₀ T hT
  rw [GD_eq]
  linarith

/-- **At least `((3 + 8·GD(1))/11 − ε)N ≈ 0.881N` zero copies of `ζ` in `(T, 2T]` are simple or
lie on the critical line**, unconditional. -/
theorem simple_or_critical_dyadic :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, ((3 + 8 * GD 1) / 11 - ε) * (Ncount T (2 * T) : ℝ)
      ≤ (Ncount T (2 * T) : ℝ) - (offLineMultipleMass zetaZeroConfig T (2 * T) : ℝ) := by
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := GD_one_le_N_sub_offLineMultipleMass (11 / 8 * ε) (by positivity)
  refine ⟨T₀, fun T hT => ?_⟩
  have h := hT₀ T hT
  have hN : (0 : ℝ) ≤ Ncount T (2 * T) := Nat.cast_nonneg _
  nlinarith

end TheoremD

end RHTower

end
