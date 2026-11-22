import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.ShortNorms.HostOfField
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.ShortNorms.RanksOnFrame
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.CharacterBoxes.FieldChi
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.CharacterBoxes.PairHyp
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.CharacterBoxes.BoundedTw
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.CharacterBoxes.WinPairs
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PairEx

/-! Host data for the trivial level and for a moving window attached to a character. -/

noncomputable section

open NumberField WindowedLandauTheory.BasicNotions WindowedLandauTheory.MainNotions
open WindowedLandauTheory.MainNotions.Inhab WindowedLandauTheory.HC WindowedLandauTheory.FrobeniusOrbits
open GlobalTheory.EX UpperTheory.Top HostParam.Seam

/-- At the trivial level the frame order is a pure power of two. -/
theorem UpperTheory.T3.hostExOf (hSN : UpperTheory.T3.ShortNorm) (hSO : UpperTheory.T3.SmallOne) :
    HostEx := by
  refine ⟨2, by norm_num, ?_⟩
  intro eps he he'
  obtain ⟨CT2, C8, c6, Cb, x₀, hC8, hc6, hCb, hHost⟩ :=
    UpperTheory.T3.hostOfFieldOf hSN hSO eps 4 he he' (by norm_num)
  obtain ⟨Y₁, hPair⟩ := QH.pairEx 1 one_pos eps 1 he he' le_rfl
  obtain ⟨x₁, hRank⟩ := GlobalTheory.EX.exists_ranks_rankVal_frame eps he he'
  obtain ⟨x₂, hSmall⟩ := Filter.eventually_atTop.mp
    ((tendsto_rpow_atTop (by positivity : 0 < eps / 5)).eventually_ge_atTop 8)
  obtain ⟨page, hPage⟩ := exists_pageN eps he
  let Ξ : Subgroup (DirichletCharacter ℂ 1) := ⊥
  have hcard : Nat.card Ξ = 1 := Subgroup.card_bot
  obtain ⟨c, e₀, hc, hc', hOrd⟩ := UpperTheory.Top.ordAny 1 Ξ
  rw [hcard] at hc'
  have hc1 : c = 1 := le_antisymm hc' hc
  subst c
  let eMin := max e₀ 2
  refine ⟨CT2, C8, 4, c6, Cb, max (max x₀ Y₁) (max (max x₁ x₂) ((2 : ℝ) ^ eMin)),
    by linarith, by norm_num, hc6, hCb, Scales.univ 2 1 le_rfl, ?_⟩
  intro s hs hx hS
  have hJ : s.J = 1 := Scales.mem_univ.mp hS
  simp only [max_le_iff] at hx
  obtain ⟨⟨hx₀, hY₁⟩, ⟨hx₁, hx₂⟩, hx₃⟩ := hx
  obtain ⟨q, d, hGood⟩ := hPair s.x hY₁
  rw [Real.rpow_one] at hGood
  obtain ⟨hHyp, hSplit, -⟩ := UpperTheory.Top.pairHyp eps s.x q d hGood.pair
  have h8 := hSmall s.x hx₂
  have hq3 : q ≠ 3 := by
    rintro rfl
    have hlo := hGood.pair.q_lo
    have hlog := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num)
    norm_num only [Nat.cast_ofNat] at hlo
    linarith
  have hp := hPage s.x s.one_lt_alt.le
  have hWide : s.x ≤ s.x ^ (2 + 8 * eps) := by
    conv_lhs => rw [← Real.rpow_one s.x]
    exact Real.rpow_le_rpow_of_exponent_le s.one_lt_alt.le (by linarith)
  have heMin : eMin ≤ page s.x :=
    (pow_le_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp (hx₃.trans (hWide.trans hp.1))
  have h₀ : e₀ ≤ page s.x := (le_max_left _ _).trans heMin
  have h₂ : 2 ≤ page s.x := (le_max_right _ _).trans heMin
  have h4 : 4 * 1 ≤ 2 ^ page s.x :=
    (show 4 * 1 ≤ 2 ^ (2 : ℕ) by norm_num).trans (Nat.pow_le_pow_right two_pos h₂)
  have hOrd' : (AnyGrp.frame Ξ (page s.x)).ord = 2 ^ page s.x := by
    rw [hOrd (page s.x) h₀, one_mul]
  have hOdd : ∀ l : ℕ, l.Prime → l ≠ 2 → l ∣ (1 : ℕ) → jacobiSym (-(d : ℤ)) l = 1 := by
    intro l hl _ hdv
    exact (hl.ne_one (Nat.dvd_one.mp hdv)).elim
  let H := AnyGrp.host Ξ (page s.x) hHyp hGood.coprime h₂ hOdd
  have hQSdvd : H.QS ∣ Nat.lcm (2 ^ (page s.x + 2)) 1 := AnyGrp.QS_dvd Ξ (page s.x)
  let b := ⌊s.x ^ (eps / 5)⌋₊
  have hb : 4 * 1 ≤ b := Nat.le_floor (by push_cast; linarith)
  obtain ⟨hbrows, hQS⟩ := conductor_divisor_bounds hQSdvd hb
  have hRows : FieldRows H b := by
    refine ⟨AnyGrp.psQ Ξ _ hHyp hGood.coprime h₂ hOdd, AnyGrp.exists_sqq Ξ _ hHyp hGood.coprime h₂ hOdd,
      AnyGrp.exact Ξ _ hHyp hGood.coprime h₂ hOdd, AnyGrp.QS_le Ξ _ h4, ?_, hq3, ?_, hbrows⟩
    · change (AnyGrp.frame Ξ (page s.x)).o ^ 64 ≤ 2 ^ page s.x
      rw [AnyGrp.o_eq, hcard, one_pow]
      exact Nat.one_le_two_pow
    · exact fun l hl hl2 hle => hSplit l hl hl2
        ((Nat.cast_le.2 hle).trans (Nat.floor_le (by positivity)))
  obtain ⟨R, hR, hRV⟩ := hRank s hs hx₁ (AnyGrp.frame Ξ (page s.x))
    (by rw [hs, hOrd']; exact_mod_cast hp.1)
    (by rw [hs, hOrd']; exact_mod_cast hp.2)
  have transport (φ : Frame) (hφ : φ = AnyGrp.frame Ξ (page s.x)) :
      ∃ H₀ : HostAx φ, H₀.q = q ∧ H₀.d = d ∧ H₀.QS ∣ Nat.lcm (2 ^ (φ.e + 2)) 1 ∧
        H₀.QS ≤ 4 * φ.ord ∧ FieldRows H₀.toHostRaw b := by
    subst φ
    refine ⟨HostAx.ofRaw H, rfl, rfl, hQSdvd, ?_, hRows⟩
    rw [hOrd']
    simpa using hQS
  obtain ⟨H₀, hq, hd, hQdvd, hQle, hField⟩ := transport R.toFrame hR
  have hRo : R.o = 1 := (congrArg Frame.o hR).trans ((AnyGrp.o_eq Ξ _).trans hcard)
  obtain ⟨H', q₀, -, hCT, hG, -⟩ := hHost s R H₀ 1 s.x hs hx₀ hRV
    (by rw [hJ]; norm_num)
    (by rw [hRo]; norm_num)
    (by exact_mod_cast hQle)
    one_pos (by norm_num)
    hQdvd
    ⟨by rw [hJ, div_one, Real.rpow_one], le_rfl⟩
    (by rw [hq, hd]; exact hGood)
    hField
  exact ⟨R, H', q₀, hRV, hCT, hG, trivial⟩

/-- The arithmetic hosts attached to the character satisfy the required Selmer bounds on a common window. -/
theorem UpperTheory.T3.supplyChiOf (hSN : UpperTheory.T3.ShortNorm) (hSO : UpperTheory.T3.SmallOne)
    (ψ : PChar) (hV : VWinAt ψ 401) :
    HostExW (3 / 2) (fun _ s R H _ => EAtH (Level.cyc ψ) H.toHostRaw H.TT s.x s.eps 4 ∧
      VVle H.E R.t (Real.sqrt s.b)) := by
  intro eps heps heps'
  have hSup := UpperTheory.T3.hostOfFieldOf hSN hSO
  have hAdm := GlobalTheory.EX.exists_ranks_rankVal_frame
  haveI := ψ.ne
  have hN0 : 0 < ψ.N := Nat.pos_of_ne_zero (NeZero.ne _)
  obtain ⟨c, e0, hc, hF⟩ := UpperTheory.Top.fieldChi ψ
  obtain ⟨J, hJ, hwin⟩ := UpperTheory.Top.winPairs ψ eps (c : ℝ) heps heps' (by exact_mod_cast hc) hV QH.pairEx
  obtain ⟨C0, hC1, hCJ, hCo, hCN⟩ : ∃ C0 : ℝ, 1 ≤ C0 ∧ J ≤ C0 ∧ ((Level.cyc ψ).o : ℝ) ≤ C0 ∧
      8 * (ψ.N : ℝ) ≤ C0 :=
    by
      have h1 : (0 : ℝ) ≤ ((Level.cyc ψ).o : ℝ) := Nat.cast_nonneg _
      have h2 : (0 : ℝ) ≤ (ψ.N : ℝ) := Nat.cast_nonneg _
      exact ⟨J + ((Level.cyc ψ).o : ℝ) + 8 * (ψ.N : ℝ), by linarith, by linarith, by linarith, by linarith⟩
  obtain ⟨CT2, C8, c6, Cb, x0A, hC8, hc6, hCb, hA⟩ := hSup eps C0 heps heps' hC1
  obtain ⟨x0B, hB⟩ := hAdm eps heps heps'
  obtain ⟨x0T, hT⟩ := UpperTheory.Top.eventually_rank_le_rpow_of_lt_one_div_fiftytwo eps heps heps'
  obtain ⟨K, hK5, hK4⟩ : ∃ K : ℝ, 5 ≤ K ∧ 4 * (ψ.N : ℝ) ≤ K :=
    by
      have h2 : (0 : ℝ) ≤ (ψ.N : ℝ) := Nat.cast_nonneg _
      exact ⟨5 + 4 * (ψ.N : ℝ), by linarith, by linarith⟩
  have hK0 : 0 ≤ K := by linarith
  obtain ⟨A, hA0, hAK⟩ : ∃ A : ℝ, 0 ≤ A ∧ A ^ (eps / 5) = K := by
    refine ⟨K ^ (5 / eps), Real.rpow_nonneg hK0 _, ?_⟩
    rw [← Real.rpow_mul hK0, show 5 / eps * (eps / 5) = (1 : ℝ) by field_simp, Real.rpow_one]
  have hc0 : (0 : ℝ) ≤ c := by positivity
  have hAJ0 : 0 ≤ A ^ J := Real.rpow_nonneg hA0 _
  obtain ⟨x1, h1A, h1B, h1T, h1J, h1c⟩ : ∃ x1 : ℝ, x0A ≤ x1 ∧ x0B ≤ x1 ∧ x0T ≤ x1 ∧ A ^ J ≤ x1 ∧
      (c : ℝ) * 2 ^ e0 < x1 := by
    have h2 : (0 : ℝ) ≤ (c : ℝ) * 2 ^ e0 := by positivity
    refine ⟨|x0A| + |x0B| + |x0T| + A ^ J + (c : ℝ) * 2 ^ e0 + 1, ?_, ?_, ?_, ?_, ?_⟩ <;>
      linarith [le_abs_self x0A, le_abs_self x0B, le_abs_self x0T, abs_nonneg x0A, abs_nonneg x0B,
        abs_nonneg x0T]
  refine ⟨CT2, C8, 4, c6, Cb, x1, le_trans hC1 hC8, by norm_num, hc6, hCb, ?_⟩
  refine ⟨⟨J, hJ, {x | ∃ Y q d e, UpperTheory.Top.WinDatum ψ eps J c x Y q d e}, hwin⟩, ?_⟩
  rintro s hs hx ⟨hsJ, Y, q, d, e, hW⟩
  have hx1 : 1 < s.x := s.one_lt_alt
  have hJ0 : 0 < J := by linarith
  have hYA : A ≤ Y := by
    calc A = (A ^ J) ^ (1 / J) := by rw [one_div, Real.rpow_rpow_inv hA0 hJ0.ne']
      _ ≤ s.x ^ (1 / J) := Real.rpow_le_rpow hAJ0 (h1J.trans hx) (div_nonneg zero_le_one hJ0.le)
      _ ≤ Y := hW.lo
  have hY0 : 0 ≤ Y := hA0.trans hYA
  have hYK : K ≤ Y ^ (eps / 5) := by
    rw [← hAK]
    exact Real.rpow_le_rpow hA0 hYA (by positivity)
  obtain ⟨hHyp, hjac, -⟩ := UpperTheory.Top.pairHyp eps Y q d hW.good.pair
  have hq3 : q ≠ 3 := by
    intro hq
    have h1 := hW.good.pair.q_lo
    rw [hq] at h1
    push_cast at h1
    have h2 : Real.log 3 ≤ 2 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
      linarith
    linarith
  have he : e ≥ e0 := by
    by_contra! hlt
    have h1 : (2 : ℝ) ^ e ≤ 2 ^ e0 := pow_le_pow_right₀ (by norm_num) hlt.le
    have h2 : s.x ≤ s.x ^ (2 + 8 * eps) := by
      calc s.x = s.x ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith)
    have h3 := hW.n_lo
    linarith [mul_le_mul_of_nonneg_left h1 hc0]
  have h4N : 4 * ψ.N ≤ ⌊Y ^ (eps / 5)⌋₊ := by
    apply Nat.le_floor
    push_cast
    linarith
  have hjacb : ∀ p : ℕ, Nat.Prime p → p ≠ 2 → p ≤ ⌊Y ^ (eps / 5)⌋₊ → jacobiSym (-(d : ℤ)) p = 1 :=
    fun p hp hp2 hpb => hjac p hp hp2 ((Nat.cast_le.2 hpb).trans (Nat.floor_le (Real.rpow_nonneg hY0 _)))
  obtain ⟨φ, H0, hφe, hφord, hHq, hHd, hφo, hFR, hQSdvd, hQSle, hkept, hps, hker, htw⟩ :=
    hF e he q d ⌊Y ^ (eps / 5)⌋₊ hHyp hq3 hW.good.coprime h4N hjacb
  obtain ⟨R, h, hRV⟩ := hB s hs (h1B.trans hx) φ
    (by rw [hs, hφord]; push_cast; exact hW.n_lo)
    (by rw [hs, hφord]; push_cast; exact hW.n_up)
  subst h
  have hnlo := hRV.n_lo
  have hQS : (H0.QS : ℝ) ≤ C0 * R.n := by
    have hq' : (H0.QS : ℝ) ≤ 4 * ψ.N * R.toFrame.ord := by exact_mod_cast hQSle
    have hord : (R.toFrame.ord : ℝ) = c * 2 ^ e := by rw [hφord]; push_cast; ring
    have hn : (0 : ℝ) ≤ R.n := Nat.cast_nonneg _
    have hN : (0 : ℝ) ≤ ψ.N := Nat.cast_nonneg _
    rw [hord] at hq'
    have h5 := hW.n_up
    nlinarith [mul_le_mul_of_nonneg_left h5 (by positivity : (0 : ℝ) ≤ 4 * ψ.N),
      mul_le_mul_of_nonneg_left (hs ▸ hnlo) (by positivity : (0 : ℝ) ≤ 8 * ψ.N),
      mul_le_mul_of_nonneg_right hCN hn]
  obtain ⟨H, q0, hH, hCT, hGood, hSh⟩ := hA s R H0 ψ.N Y hs (h1A.trans hx) hRV
    (by rw [hsJ]; exact hCJ) (by rw [hφo]; exact hCo) hQS hN0
    (by have : (0 : ℝ) ≤ ψ.N := Nat.cast_nonneg _; linarith)
    (by rw [hφe]; exact hQSdvd) ⟨by rw [hsJ]; exact hW.lo, hW.up⟩
    (by rw [hHq, hHd]; exact hW.good) hFR
  subst hH
  refine ⟨R, H, q0, hRV, hCT, hGood, ?_, ?_⟩
  · have hprime : ∀ l : ℕ, Nat.Prime l → l ∣ H.QS → l ∣ 2 * ψ.N := by
      intro l hl hlQ
      have h1 : l ∣ 2 ^ (e + 2) * ψ.N := hlQ.trans (hQSdvd.trans (Nat.lcm_dvd (dvd_mul_right _ _) (dvd_mul_left _ _)))
      rcases (Nat.Prime.dvd_mul hl).1 h1 with h2 | h2
      · have h3 := (Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).1 (hl.dvd_of_dvd_pow h2)
        subst h3
        exact dvd_mul_right 2 _
      · exact dvd_mul_of_dvd_right h2 2
    have hbd := UpperTheory.Top.boundedTw ψ R.toFrame H.toHostRaw eps Y s.x heps hx1.le hW.up htw hker.1 hprime
      (by rw [hHq, hHd]; exact hW.good)
    rw [hs] at hSh ⊢
    exact ⟨hφo, hkept, hps, hSh, hbd.1, hbd.2⟩
  · have hCF := UpperTheory.Top.isChiField ψ R.toFrame H.toHostRaw hker
    rw [hφe, hHq, hHd] at hCF
    have hv := hW.bound H.E hCF
    refine hv.mono ?_ (le_of_eq ?_)
    · apply Nat.le_floor
      exact hT s R hs (h1T.trans hx) hRV
    · rw [WindowedLandauTheory.BasicNotions.Scale.b, WindowedLandauTheory.BasicNotions.Scale.L, hs]
