import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.StageSelection

/-! The second prime lies in the progression selected by the first prime and the small primes. -/

open Finset WindowedLandauTheory.HC UpperTheory.Top

namespace QH

private theorem firstTwist (N₀ q : ℕ) [NeZero N₀] (hq : q.Prime) (h2 : q ≠ 2)
    (hlt : N₀ < q) (ξ : DirichletCharacter ℂ N₀) (a : ℕ) :
    ∃ χ : PChar, χ.N ≤ N₀ * q ∧
      (a ≤ 1 → ∀ n : ℕ, n.Coprime N₀ → χ.val n = ξ n * J q n ^ a) := by
  have hfN : ξ.conductor ≤ N₀ := Nat.le_of_dvd (NeZero.pos N₀) ξ.conductor_dvd_level
  by_cases ha : a ≤ 1
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp ha with rfl | rfl
    · refine ⟨PChar.of ξ, hfN.trans (Nat.le_mul_of_pos_right _ hq.pos), fun _ n hn => ?_⟩
      simpa only [PChar.val, pow_zero, mul_one] using (An.induces_of ξ).2 n hn
    · haveI : NeZero ξ.conductor := ⟨ξ.conductor_ne_zero⟩
      have hqf : ¬ q ∣ ξ.conductor := fun h =>
        ((Nat.le_of_dvd (NeZero.pos ξ.conductor) h).trans hfN).not_gt hlt
      obtain ⟨ψ, hψ, -, hψn⟩ :=
        twist_prim ξ.conductor q ξ.primitiveCharacter ξ.primitiveCharacter_isPrimitive hq h2 hqf
      haveI : NeZero (ξ.conductor * q) := ⟨mul_ne_zero ξ.conductor_ne_zero hq.ne_zero⟩
      refine ⟨⟨ξ.conductor * q, ψ, hψ⟩, Nat.mul_le_mul_right q hfN, fun _ n hn => ?_⟩
      change ψ n = _
      rw [pow_one, hψn n]
      exact congrArg (fun c : ℂ => c * J q n) ((An.induces_of ξ).2 n hn)
  · exact ⟨PChar.one, Nat.mul_pos (NeZero.pos N₀) hq.pos, fun h => (ha h).elim⟩

private theorem ev_log {ε K : ℝ} (hε : 0 < ε) (hK : 1 ≤ K) :
    ∀ᶠ Y : ℝ in Filter.atTop, 800 * K * Real.log Y ≤ Y ^ (ε / 5) := by
  have h := (isLittleO_log_rpow_atTop (show 0 < ε / 5 by positivity)).bound
    (show (0 : ℝ) < 1 / (800 * K) by positivity)
  filter_upwards [h, Filter.eventually_gt_atTop (0 : ℝ)] with Y hY hY0
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hY0.le _), Real.norm_eq_abs] at hY
  have h1 : Real.log Y ≤ 1 / (800 * K) * Y ^ (ε / 5) := (le_abs_self _).trans hY
  calc 800 * K * Real.log Y ≤ 800 * K * (1 / (800 * K) * Y ^ (ε / 5)) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = _ := by field_simp

theorem stage2 (hP : PrimeProgressions.PNTAPRelW) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ε τ K η : ℝ) (N₀ : ℕ), 0 < ε → ε < 1 / 52 → 0 < τ → 1 ≤ K → 0 < η → 0 < N₀ → ∃ Y₀ : ℝ, ∀ Y ≥ Y₀,
      ∀ z' : ℝ, Y ^ (ε / 5) * Real.log Y ^ 2 ≤ z' → z' ≤ K ^ 2 * (Y ^ (ε / 5) * Real.log Y ^ 2) → ∀ q ∈ primePairSetFirst (Y ^ (ε / 5)),
      (primeSetTwoBounds (Y ^ (ε / 5)) z' q).Nonempty ∧ ∀ B ⊆ primeSetTwoBounds (Y ^ (ε / 5)) z' q,
        (∀ d ∈ B, ¬ GoodD N₀ C τ Y (Y ^ K) (Y ^ (ε / 5)) z' q d) → (B.card : ℝ) ≤ η * (primeSetTwoBounds (Y ^ (ε / 5)) z' q).card := by
  obtain ⟨C, hC, hst⟩ := stage hP
  refine ⟨C, hC, fun ε τ K η N₀ hε hε52 hτ hK hη hN₀ => ?_⟩
  haveI : NeZero N₀ := ⟨by omega⟩
  classical
  letI : Fintype (DirichletCharacter ℂ N₀) := Fintype.ofFinite _
  obtain ⟨Y₀, hY₀⟩ := hst (6 * ε / 5) τ K η (Fintype.card (DirichletCharacter ℂ N₀) * 2)
    (by positivity) (by linarith) hτ hK hη
  have e1 := ev_log hε hK
  have e2 := (tendsto_rpow_atTop (by positivity : (0:ℝ) < ε / 5)).eventually_ge_atTop
    (2 * Real.log N₀ + 2)
  have e3 := (tendsto_rpow_atTop (by positivity : (0:ℝ) < ε / 25)).eventually_ge_atTop (K ^ 2)
  have e4 := Filter.eventually_ge_atTop (Real.exp 2)
  obtain ⟨Y₁, hY₁⟩ := Filter.eventually_atTop.mp (e1.and (e2.and (e3.and e4)))
  refine ⟨max Y₀ Y₁, fun Y hY z' hz1 hz2 q hq => ?_⟩
  obtain ⟨hlog, hzN, hK2, hYe⟩ := hY₁ Y (le_trans (le_max_right _ _) hY)
  have hY0 : Y ≥ Y₀ := le_trans (le_max_left _ _) hY
  set z := Y ^ (ε / 5) with hz
  have hYpos : 0 < Y := lt_of_lt_of_le (Real.exp_pos 2) hYe
  have hY1 : 1 ≤ Y := le_trans (Real.one_le_exp (by norm_num)) hYe
  have hlogY : 2 ≤ Real.log Y := by
    have h1 := Real.log_exp 2
    have h2 := Real.log_le_log (Real.exp_pos 2) hYe
    linarith
  have hlogN : 0 ≤ Real.log (N₀:ℝ) := Real.log_nonneg (Nat.one_le_cast.mpr hN₀)
  have hz2' : 2 ≤ z := by linarith
  have hzpos : 0 < z := by linarith
  have hlogY2 : 4 ≤ Real.log Y ^ 2 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hlogY 2
    norm_num at h
    exact h
  have hz'4 : 4 * z ≤ z' := by
    rw [mul_comm]
    exact (mul_le_mul_of_nonneg_left hlogY2 hzpos.le).trans hz1
  simp only [primePairSetFirst, PPset, Finset.mem_filter, Finset.mem_Icc] at hq
  obtain ⟨⟨-, hqle⟩, hqp, hq8, hqlo⟩ := hq
  have hqle' : (q:ℝ) ≤ Real.exp z :=
    le_trans (Nat.cast_le.mpr hqle) (Nat.floor_le (Real.exp_pos z).le)
  have hq2 : q ≠ 2 := by
    rintro rfl
    norm_num at hq8
  have hhalf : Real.exp z ^ (1/2:ℝ) = Real.exp (z/2) := by
    rw [← Real.exp_mul]
    congr 1
    ring
  have hqbig : Real.exp (z/2) < q := by rw [← hhalf]; exact hqlo
  have hNq : N₀ < q := by
    have h : (N₀:ℝ) < q := by
      calc (N₀:ℝ) = Real.exp (Real.log N₀) := (Real.exp_log (by exact_mod_cast hN₀)).symm
        _ ≤ Real.exp (z/2) := Real.exp_le_exp.mpr (by linarith)
        _ < q := hqbig
    exact_mod_cast h
  have hqK : (Y ^ K) ^ 400 < (q:ℝ) := by
    have h : (Y ^ K) ^ 400 = Real.exp (400 * (K * Real.log Y)) := by
      rw [Real.rpow_def_of_pos hYpos, ← Real.exp_nat_mul]
      push_cast
      ring_nf
    rw [h]
    refine lt_of_le_of_lt (Real.exp_le_exp.mpr ?_) hqbig
    linarith only [hlog, hz]
  obtain ⟨a₀, hcop, hPP⟩ := exists_coprime_primePairSetSecond_eq_PPset z z' hqp hq2
  rw [hPP]
  have hodd : 0 < oddM z q := by
    unfold oddM
    exact Nat.mul_pos hqp.pos (Finset.prod_pos fun p hp => (Finset.mem_filter.mp hp).2.pos)
  have hadm : AdmissiblePrimeScale (6 * ε / 5) Y (Real.exp z') (16 * oddM z q) a₀ := by
    refine ⟨by omega, Dvd.dvd.mul_right (by norm_num) _, hcop, ?_, ?_, ?_⟩
    · rw [Real.log_exp]
      have hlm := log_oddM z q hzpos.le hqp.pos
      have hlq : Real.log q ≤ z := by
        rw [Real.log_le_iff_le_exp (by exact_mod_cast hqp.pos)]
        exact hqle'
      have h16 : Real.log 16 = 4 * Real.log 2 := by
        rw [show (16:ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
        norm_num
      have h4 : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
        norm_num
      have hl2 := Real.log_two_lt_d9
      have hl2' : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have hm : Real.log ((16 * oddM z q : ℕ) : ℝ) ≤ 4 * z := by
        rw [h16, h4] at hlm
        have h := mul_le_mul_of_nonneg_right hz2' (by positivity : 0 ≤ 2 * Real.log 2)
        linarith only [hlm, hlq, h, mul_lt_mul_of_pos_right hl2 hzpos]
      linarith only [hz1, mul_le_mul_of_nonneg_left hm (sq_nonneg (Real.log Y))]
    · rw [Real.log_exp, show 6 * ε / 5 / 6 = ε / 5 by ring]
      rw [← hz]
      exact (le_mul_of_one_le_right hzpos.le (by linarith only [hlogY2])).trans hz1
    · rw [Real.log_exp, show 6 * ε / 5 / 5 = ε / 5 + ε / 25 by ring, Real.rpow_add hYpos]
      have h := mul_le_mul_of_nonneg_right hK2 (by positivity : (0:ℝ) ≤ z * Real.log Y ^ 2)
      rw [← hz]
      linarith only [hz2, h]
  have hzle : z ≤ Y ^ (6 * ε / 5 / 5) := by
    rw [hz]
    exact Real.rpow_le_rpow_of_exponent_le hY1 (by linarith)
  have hprime : ∀ p : ℕ, p.Prime → p ∣ 16 * oddM z q →
      (p:ℝ) ≤ Y ^ (6 * ε / 5 / 5) ∨ (Y ^ K) ^ 400 < (p:ℝ) := by
    intro p hp hpm
    rcases (Nat.Prime.dvd_mul hp).mp hpm with h | h
    · have hp2 : p = 2 :=
        (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow (show p ∣ 2 ^ 4 from h))
      subst hp2
      left
      push_cast
      linarith
    · unfold oddM at h
      rcases (Nat.Prime.dvd_mul hp).mp h with h | h
      · right
        rw [(Nat.prime_dvd_prime_iff_eq hp hqp).mp h]
        exact hqK
      · left
        obtain ⟨r, hr, hpr⟩ := (Prime.dvd_finset_prod_iff hp.prime _).mp h
        simp only [Finset.mem_filter, Finset.mem_Icc] at hr
        have hpr' := (Nat.prime_dvd_prime_iff_eq hp hr.2).mp hpr
        subst hpr'
        have h' : (p:ℝ) ≤ z := le_trans (Nat.cast_le.mpr hr.1.2) (Nat.floor_le hzpos.le)
        linarith
  set F := (N₀:ℝ) * Real.exp z with hF
  have hF1 : 1 ≤ F :=
    one_le_mul_of_one_le_of_one_le (Nat.one_le_cast.mpr hN₀) (Real.one_le_exp hzpos.le)
  have hFU : F ≤ Real.exp z' ^ (1/2:ℝ) := by
    rw [← Real.exp_mul]
    calc F = Real.exp (Real.log N₀ + z) := by
          rw [Real.exp_add, Real.exp_log (by exact_mod_cast hN₀)]
      _ ≤ Real.exp (z' * (1/2)) := Real.exp_le_exp.mpr (by linarith only [hz'4, hzN, hzpos, hz])
  choose g hg using fun p : DirichletCharacter ℂ N₀ × ℕ => firstTwist N₀ q hqp hq2 hNq p.1 p.2
  have hcard : ((Finset.univ ×ˢ Finset.range 2).image g).card ≤
      Fintype.card (DirichletCharacter ℂ N₀) * 2 := by
    calc ((Finset.univ ×ˢ Finset.range 2).image g).card ≤ (Finset.univ ×ˢ Finset.range 2).card :=
          Finset.card_image_le
      _ = _ := by simp [Finset.card_product]
  have hΞ : ∀ ξ ∈ (Finset.univ ×ˢ Finset.range 2).image g,
      (ξ.N : ℝ) ≤ F := by
    intro ξ hξ
    obtain ⟨p, -, rfl⟩ := Finset.mem_image.mp hξ
    refine (Nat.cast_le.mpr (hg p).1).trans ?_
    push_cast
    exact mul_le_mul_of_nonneg_left hqle' (Nat.cast_nonneg _)
  have hst' := hY₀ Y hY0 (Real.exp z') F (16 * oddM z q) a₀ _ hadm hprime hF1 hFU hcard hΞ
  refine ⟨hst'.1, fun B hB hbad => hst'.2 B hB ?_⟩
  intro d hd
  have hdB := hB hd
  simp only [PPset, Finset.mem_filter] at hdB
  obtain ⟨-, hdp, -⟩ := hdB
  have hnot := hbad d hd
  simp only [GoodD, not_forall] at hnot
  obtain ⟨ξ, a, ha, hnb⟩ := hnot
  refine ⟨g (ξ, a), Finset.mem_image.mpr ⟨(ξ, a),
    Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_range.mpr (by omega)⟩, rfl⟩,
    N₀ * q * d, Nat.pos_iff_ne_zero.mp (Nat.mul_pos (Nat.mul_pos hN₀ hqp.pos) hdp.pos), ?_⟩
  intro hall
  apply hnb
  intro N _ ψ hInd
  have h := hall N ψ ⟨hInd.1, fun n hn => ?_⟩
  · rwa [hF, mul_assoc, ← Real.exp_add] at h
  · have hn0 : n.Coprime N₀ := Nat.Coprime.coprime_dvd_right ((Nat.dvd_mul_right N₀ q).mul_right d) hn
    rw [hInd.2 n hn]
    dsimp only
    exact congrArg (fun c : ℂ => c * J d n) ((hg (ξ, a)).2 ha n hn0).symm

end QH
