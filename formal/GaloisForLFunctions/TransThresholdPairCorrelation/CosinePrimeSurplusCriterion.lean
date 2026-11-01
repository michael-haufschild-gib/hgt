import GaloisForLFunctions.TransThresholdPairCorrelation.CosinePrimeGramCertificate

/-!
# The cosine surplus certificate through bandwidth two

The actual prime diagonal and trace retain the shape-one cosine coefficient.
A bounded normalized tail costs only `o(N)` whenever the counting lower bound
is positive, so the endpoint bandwidth two is included.
-/

noncomputable section
open Real Filter Topology MeasureTheory Asymptotics Zeta23 Zeta23.Assembly Zeta23.PrimeSide Zeta23.ThmE RHLinalg RHTower
open GaloisForLFunctions.IncommensurableGaborPinching

namespace GaloisForLFunctions.TransThresholdPairCorrelation

private theorem eventually_linear_le_count (C ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ T in atTop, C * T ≤ ε * (zetaZeroConfig.N T (2 * T) : ℝ) := by
  filter_upwards [eventually_N_ge zetaZeroConfig paperInputs_zeta.RvM,
    tendsto_l_atTop.eventually_ge_atTop (4 * π * C / ε),
    eventually_ge_atTop (0 : ℝ)] with T hN hl hT
  have hc : 4 * π * C ≤ ε * l T := by
    have hh := (div_le_iff₀ hε).mp hl
    linarith only [hh]
  have hh := mul_le_mul_of_nonneg_left hc hT
  have hh' := mul_le_mul_of_nonneg_left hN hε.le
  have he : ε * (T * l T / (4 * π)) * (4 * π) = T * (ε * l T) := by
    field_simp
  have hn := mul_le_mul_of_nonneg_right hh' (by positivity : 0 ≤ 4 * π)
  nlinarith only [hh, hn, he, Real.pi_pos]

private theorem cosine_main_normalization {a b J L e T : ℝ}
    (ha : a ≠ 0) (hL : L ≠ 0) (he : e ≠ 0) :
    (T * L / (2 * π) * (b * e ^ 2 + L ^ 2 * J)) / (a * L) ^ 2 =
      ((b + (L / e) ^ 2 * J) / ((L / e) * a ^ 2)) * (T * e / (2 * π)) := by
  field_simp [ha, hL, he]

private theorem params_frob_split (P : Params) (T : ℝ) {c : ℝ}
    (hF : LocalHypsCoreW c (P.toSetting T) (P.localFun T)) (hT : 0 ≤ T) :
    frobSq (P.hat T (P.Gp T)) =
      (Mform (P.PhiR T) T Zeta23.mu Zeta23.mu +
        (1 / (2 * π ^ 2)) * ppDiag (P.PhiR T) T (P.X T) +
        2 * Mform (P.PhiR T) T Zeta23.mu (Zeta23.PX (P.X T)) +
        2 * Mform (P.PhiR T) T Zeta23.mu (Zeta23.PiX (P.X T)) +
        Mform (P.PhiR T) T (Zeta23.PiX (P.X T)) (Zeta23.PiX (P.X T))) /
          (P.a T * P.L T) ^ 2 + frobSurplus (P.toSetting T) (P.localFun T) /
            (P.a T * P.L T) ^ 2 := by
  have hsplit := trGt2Nu_nuX_split paperInputs_zeta.Gamma hF hT
  have hPhi : (P.localFun T).Phi = P.PhiR T := rfl
  have htime : (P.toSetting T).T = T := rfl
  have hX : (P.toSetting T).X = P.X T := rfl
  rw [hPhi, htime, hX] at hsplit
  change trGt2Nu (nuX (P.X T)) (P.toSetting T) (P.localFun T) = _ at hsplit
  rw [frobSq_hat, frobSq_tilde_Gp]
  change (P.a T * P.L T)⁻¹ ^ 2 *
    trGt2Nu (nuX (P.X T)) (P.toSetting T) (P.localFun T) = _
  rw [hsplit]
  ring

private theorem cosine_frob_split (lam T : ℝ)
    (hF : LocalHypsCoreW (ThmD.cDT stdProfile 1)
      ((zetaCosineParams lam T).toSetting T) ((zetaCosineParams lam T).localFun T))
    (hT : 0 ≤ T) :
    let Q := zetaCosineParams lam T
    frobSq (Q.hat T (Q.Gp T)) =
      zetaCosineDiagonalPart lam T / (Q.a T * Q.L T) ^ 2 + zetaCosineFrobSurplus lam T :=
  params_frob_split (zetaCosineParams lam T) T hF hT

private theorem cosine_diagonal_normalized (lam : ℝ) (hlam : 0 < lam) (hlam2 : lam ≤ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T in atTop,
      let Q := zetaCosineParams lam T
      frobSq (Q.hat T (Q.Gp T)) ≤
        (2 - cosineWindowRate (paramsOf stdProfile lam) 1 T) * (T * ell1 T / (2 * π)) +
          C * T + zetaCosineFrobSurplus lam T := by
  let P := paramsOf stdProfile lam
  obtain ⟨C, hC, hdiag⟩ := zetaCosine_diagonal_part_le lam hlam hlam2
  refine ⟨4 * C / lam ^ 2, by positivity, ?_⟩
  have hlocal := cosineParams_eventually_localHypsCoreW (P := P)
    taperProfile_stdProfile hlam (κ := 1) (by norm_num) le_rfl (by norm_num [P, paramsOf])
  filter_upwards [hlocal, hdiag, eventually_l_bounds, eventually_ge_atTop (1 : ℝ)]
    with T hF hd hlbounds hTone
  let Q := zetaCosineParams lam T
  change LocalHypsCoreW (ThmD.cDT stdProfile 1) (Q.toSetting T) (Q.localFun T) at hF
  let L := Q.L T
  let a := Q.a T
  let M := T * ell1 T / (2 * π)
  change frobSq (Q.hat T (Q.Gp T)) ≤
    (2 - cosineWindowRate P 1 T) * M + (4 * C / lam ^ 2) * T + zetaCosineFrobSurplus lam T
  have hT : 0 < T := by linarith only [hTone]
  have hl : 0 < l T := by linarith only [hlbounds.2.1]
  have hL : 0 < L := hF.L_pos
  have ha : 0 < a := hF.a_pos
  have ha2 : 1 / 2 ≤ a := hF.b_ge_half.trans hF.b_le_a
  have he : 0 < ell1 T := ell1_pos hl
  have hnorm := div_le_div_of_nonneg_right hd (sq_nonneg (a * L))
  have hm : (T * L / (2 * π) * (Q.b T * ell1 T ^ 2 + L ^ 2 * cosineWindowJ P 1 T)) /
      (a * L) ^ 2 = (2 - cosineWindowRate P 1 T) * M := by
    rw [cosine_main_normalization ha.ne' hL.ne' he.ne']
    unfold cosineWindowRate Params.lam1
    change _ = (2 - (2 - ((Q.b T + (L / ell1 T) ^ 2 * cosineWindowJ P 1 T) /
      ((L / ell1 T) * a ^ 2)))) * M
    rw [sub_sub_cancel]
  have herr : C * (T * l T ^ 2) / (a * L) ^ 2 ≤ (4 * C / lam ^ 2) * T := by
    have hlo : (1 / 2 * (lam * l T)) ^ 2 ≤ (a * L) ^ 2 := by
      apply pow_le_pow_left₀ (by positivity)
      change 1 / 2 * L ≤ a * L
      exact mul_le_mul_of_nonneg_right ha2 hL.le
    calc C * (T * l T ^ 2) / (a * L) ^ 2
        ≤ C * (T * l T ^ 2) / (1 / 2 * (lam * l T)) ^ 2 :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hlo
      _ = (4 * C / lam ^ 2) * T := by field_simp [hlam.ne', hl.ne']; ring
  change zetaCosineDiagonalPart lam T / (a * L) ^ 2 ≤
    (T * L / (2 * π) * (Q.b T * ell1 T ^ 2 + L ^ 2 * cosineWindowJ P 1 T) + C * (T * l T ^ 2)) /
      (a * L) ^ 2 at hnorm
  rw [add_div, hm] at hnorm
  rw [cosine_frob_split lam T hF hT.le]
  linarith only [hnorm, herr]

/-- The normalized actual prime Gram has the matching cosine coefficient and signed surplus. -/
theorem zetaCosine_frobSq_le (lam : ℝ) (hlam : 0 < lam) (hlam2 : lam ≤ 2)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ T in atTop,
      let Q := zetaCosineParams lam T
      frobSq (Q.hat T (Q.Gp T)) ≤
        (2 - shapeOneCosineRate lam + ε) * (zetaZeroConfig.N T (2 * T) : ℝ) +
          zetaCosineFrobSurplus lam T := by
  let P := paramsOf stdProfile lam
  obtain ⟨C, hC, hdiag⟩ := cosine_diagonal_normalized lam hlam hlam2
  obtain ⟨CR, TR, hRvM⟩ := paperInputs_zeta.RvM.main
  let k := 2 - shapeOneCosineRate lam + ε / 2
  let E := C + |k| * |CR|
  have hrate := cosineWindowRate_tendsto (P := P) taperProfile_stdProfile hlam
    (κ := 1) (by norm_num) le_rfl (by norm_num [P, paramsOf])
  have hr : ∀ᶠ T in atTop, shapeOneCosineRate lam - ε / 2 ≤ cosineWindowRate P 1 T :=
    hrate.eventually (eventually_ge_nhds (by change shapeOneCosineRate lam - ε / 2 < shapeOneCosineRate lam; linarith only [hε]))
  filter_upwards [hdiag, hr, eventually_ge_atTop TR,
    eventually_l_bounds, eventually_ge_atTop (1 : ℝ),
    eventually_linear_le_count E (ε / 2) (by positivity)] with T hd hr hTR hlbounds hTone hE
  let Q := zetaCosineParams lam T
  let N : ℝ := zetaZeroConfig.N T (2 * T)
  let M := T * ell1 T / (2 * π)
  change frobSq (Q.hat T (Q.Gp T)) ≤
    (2 - shapeOneCosineRate lam + ε) * N + zetaCosineFrobSurplus lam T
  change frobSq (Q.hat T (Q.Gp T)) ≤
    (2 - cosineWindowRate P 1 T) * M + C * T + zetaCosineFrobSurplus lam T at hd
  change E * T ≤ (ε / 2) * N at hE
  have hT : 0 < T := by linarith only [hTone]
  have hl : 0 < l T := by linarith only [hlbounds.2.1]
  have he : 0 < ell1 T := ell1_pos hl
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hlog : 0 ≤ log T := log_nonneg hTone
  have hlogT : log T ≤ T := by linarith only [log_le_sub_one_of_pos hT]
  have hRv : |N - M| ≤ |CR| * log T := by
    have hh := hRvM T hTR
    change |N - T / (2 * π) * ell1 T| ≤ CR * log T at hh
    have heq : T / (2 * π) * ell1 T = M := by dsimp [M]; ring
    rw [heq] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right (le_abs_self CR) hlog)
  have hrateM := mul_le_mul_of_nonneg_right (show 2 - cosineWindowRate P 1 T ≤ k by dsimp [k]; linarith only [hr]) hM
  have hkerr : k * M ≤ k * N + |k| * |CR| * T := by
    have hh : k * (M - N) ≤ |k| * |N - M| := by
      have hh := le_abs_self (k * (M - N))
      simpa only [abs_mul, abs_sub_comm M N] using hh
    have hh' := mul_le_mul_of_nonneg_left hRv (abs_nonneg k)
    have hh'' := mul_le_mul_of_nonneg_left hlogT (by positivity : 0 ≤ |k| * |CR|)
    nlinarith only [hh, hh', hh'']
  dsimp only [k, E] at hrateM hkerr hE
  linarith only [hd, hrateM, hkerr, hE]


/-- The actual normalized cosine prime trace is asymptotic to the zero census
through bandwidth two. -/
theorem zetaCosine_trace_close (lam : ℝ) (hlam : 0 < lam) (hlam2 : lam ≤ 2)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ T in atTop,
      let Q := zetaCosineParams lam T
      |rtrace (Q.hat T (Q.Gp T)) - (zetaZeroConfig.N T (2 * T) : ℝ)| ≤
        ε * (zetaZeroConfig.N T (2 * T) : ℝ) := by
  let P := paramsOf stdProfile lam
  obtain ⟨CR, TR, hRvM⟩ := paperInputs_zeta.RvM.main
  obtain ⟨C, T₀, hC, htrace⟩ := prop_trace_zeta_wide
    (cϱ := ThmD.cDT stdProfile 1) hlam |CR|
  have hlocal := cosineParams_eventually_localHypsCoreW (P := P)
    taperProfile_stdProfile hlam (κ := 1) (by norm_num) le_rfl (by norm_num [P, paramsOf])
  filter_upwards [hlocal, eventually_ge_atTop TR, eventually_ge_atTop T₀,
    eventually_l_bounds, eventually_ge_atTop (1 : ℝ),
    eventually_linear_le_count (6 * C) ε hε] with T hF hTR hT₀ hlbounds hTone hsmall
  let Q := zetaCosineParams lam T
  change LocalHypsCoreW (ThmD.cDT stdProfile 1) (Q.toSetting T) (Q.localFun T) at hF
  let N : ℝ := zetaZeroConfig.N T (2 * T)
  change |rtrace (Q.hat T (Q.Gp T)) - N| ≤ ε * N
  change 6 * C * T ≤ ε * N at hsmall
  have hT : 0 < T := by linarith only [hTone]
  have hL : 0 < Q.L T := hF.L_pos
  have ha : 0 < Q.a T := hF.a_pos
  have ha2 : 1 / 2 ≤ Q.a T := hF.b_ge_half.trans hF.b_le_a
  have hlog : 0 ≤ log T := log_nonneg hTone
  have hlogT : log T ≤ T := by linarith only [log_le_sub_one_of_pos hT]
  have hsX : Real.sqrt (Q.X T) ≤ T := by
    have hh := sqrt_exp_lam_l_le (lam := lam) hlam.le hT hlbounds.2.2.2
    have hh' := Real.rpow_le_rpow_of_exponent_le hTone (by linarith only [hlam2] : lam / 2 ≤ 1)
    rw [Real.rpow_one] at hh'
    exact hh.trans hh'
  have hr := htrace (Q.toSetting T) (Q.localFun T) rfl hT₀ hF N (by
    change |N - T / (2 * π) * ell1q 1 T| ≤ |CR| * log T
    rw [← ell1_eq_ell1q]
    exact (hRvM T hTR).trans (mul_le_mul_of_nonneg_right (le_abs_self CR) hlog))
  change |Q.trGtilde T - Q.a T * Q.L T * N| ≤
    C * (Q.L T * (1 + log T + Real.sqrt (Q.X T))) at hr
  have hr' : |Q.trGtilde T - Q.a T * Q.L T * N| ≤
      (Q.a T * Q.L T) * (6 * C * T) := by
    have hh := mul_le_mul_of_nonneg_left (show 1 + log T + Real.sqrt (Q.X T) ≤ 3 * T by
      linarith only [hTone, hlogT, hsX]) (mul_nonneg hC hL.le)
    have hh' := mul_le_mul_of_nonneg_right ha2 (by positivity : 0 ≤ Q.L T * (6 * C * T))
    nlinarith only [hr, hh, hh']
  have heq : rtrace (Q.hat T (Q.Gp T)) - N =
      (Q.trGtilde T - Q.a T * Q.L T * N) / (Q.a T * Q.L T) := by
    rw [rtrace_hat, rtrace_tilde_Gp]
    field_simp [ha.ne', hL.ne']
  rw [heq, abs_div, abs_of_pos (mul_pos ha hL)]
  exact ((div_le_iff₀ (mul_pos ha hL)).mpr (by nlinarith only [hr'])).trans hsmall


private theorem cosine_tail_loss_littleO (B K : ℝ) (hK : 0 ≤ K) :
    (fun T => B * (4 + 2 * Real.sqrt (K * (zetaZeroConfig.N T (2 * T) : ℝ)) + B))
      =o[atTop] (fun T => (zetaZeroConfig.N T (2 * T) : ℝ)) := by
  let N : ℝ → ℝ := fun T => zetaZeroConfig.N T (2 * T)
  have hN0 (T : ℝ) : 0 ≤ N T := Nat.cast_nonneg _
  have hN := tendsto_N_atTop zetaZeroConfig paperInputs_zeta.RvM
  have h1 : (fun _ : ℝ => (1 : ℝ)) =o[atTop] N := by
    refine isLittleO_iff.mpr fun c hc => ?_
    filter_upwards [hN.eventually_ge_atTop (1 / c)] with T hT
    rw [norm_one, Real.norm_eq_abs, abs_of_nonneg (hN0 T)]
    have hh := (div_le_iff₀ hc).mp hT
    linarith only [hh]
  have hs := (h1.sqrt (Eventually.of_forall hN0)).mul_isBigO
    (isBigO_refl (fun T => Real.sqrt (N T)) atTop)
  have hs' : (fun T => Real.sqrt (N T)) =o[atTop] N := by
    simpa only [Real.sqrt_one, one_mul, ← pow_two, Real.sq_sqrt (hN0 _)] using hs
  have hh := (h1.const_mul_left (B * (4 + B))).add
    (hs'.const_mul_left (2 * B * Real.sqrt K))
  change (fun T => B * (4 + 2 * Real.sqrt (K * N T) + B)) =o[atTop] N
  have hid : (fun T => B * (4 + 2 * Real.sqrt (K * N T) + B)) =
      (fun T => B * (4 + B) * (1 : ℝ) + (2 * B * Real.sqrt K) * Real.sqrt (N T)) := by
    funext T
    rw [Real.sqrt_mul hK]
    ring
  rw [hid]
  exact hh

private theorem cosine_boundary_littleO :
    (fun T => (NII zetaZeroConfig T : ℝ)) =o[atTop]
      (fun T => (zetaZeroConfig.N T (2 * T) : ℝ)) := by
  obtain ⟨A, hA, hloc⟩ := paperInputs_zeta.RvM.local_count
  obtain ⟨C, hbound⟩ := Tail.eventually_NII_le zetaZeroConfig hA hloc
  have hO : (fun T => (NII zetaZeroConfig T : ℝ)) =O[atTop]
      (fun T => Real.sqrt T * l T) := by
    refine IsBigO.of_bound C ?_
    filter_upwards [hbound, eventually_l_pos] with T h hl
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _),
      abs_of_nonneg (by positivity)]
    simpa only [mul_assoc] using h
  exact hO.trans_isLittleO
    (isLittleO_N_of_isLittleO_Tl zetaZeroConfig paperInputs_zeta.RvM isLittleO_sqrt_mul_l_Tl)

/-- The actual cosine prime surplus and explicit pinching credit give a simple-critical
counting certificate at every fixed bandwidth through two. -/
theorem zetaCosine_surplus_certificate (lam : ℝ) (hlam : 0 < lam) (hlam2 : lam ≤ 2)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ T in atTop,
      (shapeOneCosineRate lam + cosinePairFloor lam ^ 2 / 200 - ε) *
        (zetaZeroConfig.N T (2 * T) : ℝ) - zetaCosineFrobSurplus lam T ≤
          zetaZeroConfig.N0s T (2 * T) := by
  let e := min ε 1
  have he : 0 < e := lt_min hε one_pos
  have he1 : e ≤ 1 := min_le_right _ _
  have heε : e ≤ ε := min_le_left _ _
  let δ := cosinePairFloor lam ^ 2 / 200
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  let K := 3 + δ
  have hK : 0 ≤ K := by dsimp [K]; positivity
  obtain ⟨B, hB, hseam⟩ := zetaCosine_prime_rankTrace lam hlam hlam2
  have herr := (cosine_boundary_littleO.const_mul_left 3).add
    (cosine_tail_loss_littleO B K hK)
  have hsmall := herr.def (show 0 < e / 2 by positivity)
  filter_upwards [hseam, hsmall,
    zetaCosine_frobSq_le lam hlam hlam2 (e / 10) (by positivity),
    zetaCosine_trace_close lam hlam hlam2 (e / 10) (by positivity)] with T hseam hsmall hf ht
  let Q := zetaCosineParams lam T
  let N : ℝ := zetaZeroConfig.N T (2 * T)
  let S := zetaCosineFrobSurplus lam T
  let f := frobSq (Q.hat T (Q.Gp T))
  let tr := rtrace (Q.hat T (Q.Gp T))
  change f ≤ (2 - shapeOneCosineRate lam + e / 10) * N + S at hf
  change |tr - N| ≤ e / 10 * N at ht
  change 4 * tr - f - 2 * N - 3 * (NII zetaZeroConfig T : ℝ) + δ * N -
    B * (4 + 2 * Real.sqrt f + B) ≤ zetaZeroConfig.N0s T (2 * T) at hseam
  have hN : 0 ≤ N := Nat.cast_nonneg _
  change (shapeOneCosineRate lam + δ - ε) * N - S ≤ zetaZeroConfig.N0s T (2 * T)
  -- A positive proposed lower bound itself controls the prime Frobenius square.
  have hcount : (shapeOneCosineRate lam + δ - e) * N - S ≤
      zetaZeroConfig.N0s T (2 * T) := by
    by_cases hneg : (shapeOneCosineRate lam + δ - e) * N - S ≤ 0
    · exact hneg.trans (Nat.cast_nonneg _)
    have hs : S < (shapeOneCosineRate lam + δ - e) * N := by linarith only [hneg]
    have hf' : f ≤ K * N := by
      have hh : e / 10 - e ≤ 1 := by linarith only [he, he1]
      have hh' := mul_le_mul_of_nonneg_right hh hN
      change f ≤ (2 - shapeOneCosineRate lam + e / 10) * N + S at hf
      dsimp only [K]
      nlinarith only [hf, hs, hh']
    have hpert : B * (4 + 2 * Real.sqrt f + B) ≤ B * (4 + 2 * Real.sqrt (K * N) + B) := by
      have hh := Real.sqrt_le_sqrt hf'
      nlinarith only [mul_le_mul_of_nonneg_left hh hB]
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hN] at hsmall
    have hsmall' := (le_abs_self _).trans hsmall
    have ht' := (abs_le.mp ht).1
    change 3 * (NII zetaZeroConfig T : ℝ) + B * (4 + 2 * Real.sqrt (K * N) + B) ≤
      e / 2 * N at hsmall'
    linarith only [hseam, hf, ht', hpert, hsmall']
  have hmono := mul_le_mul_of_nonneg_right heε hN
  linarith only [hcount, hmono]

/-- At bandwidth four thirds, the matched cosine certificate has explicit margin
`79/1250` above three quarters, in addition to its positive pinching credit. -/
theorem zetaCosine_fourThirds_surplus_certificate (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ T in atTop,
      (3 / 4 + 79 / 1250 + cosinePairFloor (4 / 3) ^ 2 / 200 - ε) *
        (zetaZeroConfig.N T (2 * T) : ℝ) - zetaCosineFrobSurplus (4 / 3) T ≤
          zetaZeroConfig.N0s T (2 * T) := by
  filter_upwards [zetaCosine_surplus_certificate (4 / 3) (by norm_num) (by norm_num) ε hε] with T hT
  have hh := mul_le_mul_of_nonneg_right shapeOneCosineRate_fourThirds
    (Nat.cast_nonneg (zetaZeroConfig.N T (2 * T)) : (0 : ℝ) ≤ _)
  linarith only [hT, hh]

/-- At bandwidth two, the cosine coefficient exceeds five sixths by `43/3750`,
while the signed surplus remains explicit. -/
theorem zetaCosine_two_surplus_certificate (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ T in atTop,
      (5 / 6 + 43 / 3750 + cosinePairFloor 2 ^ 2 / 200 - ε) *
        (zetaZeroConfig.N T (2 * T) : ℝ) - zetaCosineFrobSurplus 2 T ≤
          zetaZeroConfig.N0s T (2 * T) := by
  filter_upwards [zetaCosine_surplus_certificate 2 (by norm_num) le_rfl ε hε] with T hT
  have hc : 5 / 6 + 43 / 3750 ≤ shapeOneCosineRate 2 := by
    have h := shapeOneCosineRate_ge_box 2 (by norm_num)
    norm_num at h ⊢
    exact h
  have hh := mul_le_mul_of_nonneg_right hc
    (Nat.cast_nonneg (zetaZeroConfig.N T (2 * T)) : (0 : ℝ) ≤ _)
  linarith only [hT, hh]

end GaloisForLFunctions.TransThresholdPairCorrelation
