import GaloisForLFunctions.RHTower.MobiusMomentMatchedFamily

/-!
# Moment-matched literal packets of the cubic Möbius source at one scale

Split `[2R, 4R)` into `J = ⌊2R/L⌋` blocks `[2R + jL, 2R + (j+1)L)` and run the moment-matched
cofactor block in each.  The selected atoms of sign `+1` and `-1` form disjoint sets `U₊`, `U₋` of
`J Σ_q m_q` atoms each, all of admissible shape, and the literal Möbius packet
`Σ_{n ∈ U₊ ∪ U₋} μ(n) f_n` obeys, uniformly in `0 ≤ δ ≤ 1`,

`‖·‖_δ ≤ J [Σ_{j=1}^{d} 2L^j/j! K_j R² R^{-(5+δ)/2}/R^j + 2(Σ_q m_q) L^{d+1}/(d+1)! K_{d+1} 4R² R^{-(5+δ)/2}/R^{d+1}]`.
-/

open Finset

noncomputable section

namespace RHTower.CubicGamma

open RHTower.MomentSelector
open scoped ArithmeticFunction.Moebius

/-- `X² X^{-e}/X^k ≤ R² R^{-e}/R^k` for `0 < R ≤ X`, `k ≥ 1`, `e ≥ 2`. -/
theorem sq_rpow_inv_div_pow_antitone {R X e : ℝ} (hR : 0 < R) (hRX : R ≤ X) (he : 2 ≤ e)
    (k : ℕ) (hk : 1 ≤ k) : X ^ 2 * (X ^ e)⁻¹ / X ^ k ≤ R ^ 2 * (R ^ e)⁻¹ / R ^ k := by
  have hX : 0 < X := hR.trans_le hRX
  have eX : X ^ 2 * (X ^ e)⁻¹ / X ^ k = X ^ ((2 : ℝ) - e - k) := by
    rw [Real.rpow_sub hX, Real.rpow_sub hX, Real.rpow_natCast, Real.rpow_two]
    field_simp
  have eR : R ^ 2 * (R ^ e)⁻¹ / R ^ k = R ^ ((2 : ℝ) - e - k) := by
    rw [Real.rpow_sub hR, Real.rpow_sub hR, Real.rpow_natCast, Real.rpow_two]
    field_simp
  rw [eX, eR]
  have : (1 : ℝ) ≤ k := by exact_mod_cast hk
  exact Real.rpow_le_rpow_of_nonpos hR hRX (by linarith)

/-- **Moment-matched packet at scale `R`.** -/
theorem exists_family_packet {d : ℕ} (hd : 1 ≤ d) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ z₀ : ℝ, 1 ≤ z₀ ∧ ∀ (R L : ℝ) (F : Finset ℕ), 5 ≤ R → 0 < L → L ≤ R →
      (∀ q ∈ F, AdmissibleCofactor R q ∧ 2 ≤ R / q ∧ z₀ ≤ R / q ∧
        (q : ℝ) * (4 * R / q) ^ supplyExp ≤ ε * L) →
      ∃ UP UN : Finset ℕ, Disjoint UP UN ∧
        (∀ n ∈ UP, μ n = 1) ∧ (∀ n ∈ UN, μ n = -1) ∧
        (∀ n ∈ UP ∪ UN, 2 * R < n ∧ (n : ℝ) < 4 * R ∧ ∃ q ∈ F, AtomShape R q n) ∧
        UP.card = ⌊2 * R / L⌋₊ * ∑ q ∈ F, cofactorSupply R q ∧
        UN.card = ⌊2 * R / L⌋₊ * ∑ q ∈ F, cofactorSupply R q ∧
        ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 →
          gammaNorm δ (fun t => ∑ n ∈ UP ∪ UN, ((μ n : ℤ) : ℝ) * atom n t) ≤
            (⌊2 * R / L⌋₊ : ℝ) * (∑ j ∈ range d, 2 * L ^ (j + 1) / ((j + 1).factorial : ℝ) *
                (jetConst (j + 1) * R ^ 2 * (R ^ ((5 + δ) / 2))⁻¹ / R ^ (j + 1)) +
              ((2 * ∑ q ∈ F, cofactorSupply R q : ℕ) : ℝ) *
                (L ^ (d + 1) / ((d + 1).factorial : ℝ) *
                  (jetConst (d + 1) * (4 * R ^ 2) * (R ^ ((5 + δ) / 2))⁻¹ / R ^ (d + 1)))) := by
  obtain ⟨ε, hε0, hεw, hε⟩ := exists_window_width d hd
  obtain ⟨z₀, hz₀, hsupply⟩ := exists_theta_window_supply
  refine ⟨ε, hε0, z₀, hz₀, fun R L F hR hL hLR hF => ?_⟩
  classical
  set J : ℕ := ⌊2 * R / L⌋₊ with hJdef
  set M : ℕ := ∑ q ∈ F, cofactorSupply R q with hMdef
  have hR0 : 0 < R := by linarith
  have hJL : (J : ℝ) * L ≤ 2 * R := by
    have h := Nat.floor_le (show 0 ≤ 2 * R / L by positivity)
    rw [← hJdef] at h
    calc (J : ℝ) * L ≤ 2 * R / L * L := by gcongr
      _ = 2 * R := by field_simp
  have hblock : ∀ j : ℕ, j < J → ∃ aP aN : (Σ _ : ℕ, Fin (d + 1) × ℕ) → ℕ,
      ∃ TP ⊆ familyLabels (d := d) F (cofactorSupply R),
      ∃ TN ⊆ familyLabels (d := d) F (cofactorSupply R),
      TP.card = M ∧ TN.card = M ∧
      Set.InjOn aP ↑(familyLabels (d := d) F (cofactorSupply R)) ∧
      Set.InjOn aN ↑(familyLabels (d := d) F (cofactorSupply R)) ∧
      (∀ x ∈ familyLabels (d := d) F (cofactorSupply R), 2 * R + j * L < aP x ∧
        (aP x : ℝ) < 2 * R + j * L + L ∧ μ (aP x) = 1 ∧ x.1 ∈ F ∧ AtomShape R x.1 (aP x)) ∧
      (∀ x ∈ familyLabels (d := d) F (cofactorSupply R), 2 * R + j * L < aN x ∧
        (aN x : ℝ) < 2 * R + j * L + L ∧ μ (aN x) = -1 ∧ x.1 ∈ F ∧ AtomShape R x.1 (aN x)) ∧
      ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 →
        gammaNorm δ (fun t => ∑ x ∈ TP, atom (aP x) t - ∑ x ∈ TN, atom (aN x) t) ≤
          ∑ i ∈ range d, 2 * L ^ (i + 1) / ((i + 1).factorial : ℝ) *
              (jetConst (i + 1) * R ^ 2 * (R ^ ((5 + δ) / 2))⁻¹ / R ^ (i + 1)) +
            ((2 * M : ℕ) : ℝ) * (L ^ (d + 1) / ((d + 1).factorial : ℝ) *
              (jetConst (d + 1) * (4 * R ^ 2) * (R ^ ((5 + δ) / 2))⁻¹ / R ^ (d + 1))) := by
    intro j hj
    have hj0 : (0 : ℝ) ≤ j * L := by positivity
    have hjJ : ((j : ℝ) + 1) * L ≤ J * L :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hj) hL.le
    obtain ⟨aP, aN, TP, hTP, TN, hTN, hcP, hcN, hiP, hiN, hP, hN, hb⟩ :=
      exists_family_block hd hε0 hεw hε hz₀ hsupply hR hL hLR (X := 2 * R + j * L)
        (by linarith) (by nlinarith) F hF
    refine ⟨aP, aN, TP, hTP, TN, hTN, hcP, hcN, hiP, hiN, hP, hN, fun δ hδ0 hδ1 => ?_⟩
    refine (hb δ hδ0 hδ1).trans ?_
    have hX : R ≤ 2 * R + j * L := by linarith
    have he : (2 : ℝ) ≤ (5 + δ) / 2 := by linarith
    have hterm : ∀ k : ℕ, 1 ≤ k → (2 * R + j * L) ^ 2 * ((2 * R + j * L) ^ ((5 + δ) / 2))⁻¹ /
        (2 * R + j * L) ^ k ≤ R ^ 2 * (R ^ ((5 + δ) / 2))⁻¹ / R ^ k :=
      fun k hk => sq_rpow_inv_div_pow_antitone hR0 hX he k hk
    apply add_le_add
    · apply sum_le_sum
      intro i _
      have h1 := hterm (i + 1) (by omega)
      have hc : 0 ≤ 2 * L ^ (i + 1) / ((i + 1).factorial : ℝ) := by positivity
      have hjc := jetConst_nonneg (i + 1)
      have e1 : jetConst (i + 1) * (2 * R + j * L) ^ 2 * ((2 * R + j * L) ^ ((5 + δ) / 2))⁻¹ /
          (2 * R + j * L) ^ (i + 1) = jetConst (i + 1) * ((2 * R + j * L) ^ 2 *
            ((2 * R + j * L) ^ ((5 + δ) / 2))⁻¹ / (2 * R + j * L) ^ (i + 1)) := by ring
      have e2 : jetConst (i + 1) * R ^ 2 * (R ^ ((5 + δ) / 2))⁻¹ / R ^ (i + 1) =
          jetConst (i + 1) * (R ^ 2 * (R ^ ((5 + δ) / 2))⁻¹ / R ^ (i + 1)) := by ring
      rw [e1, e2]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 hjc) hc
    · have h1 := hterm (d + 1) (by omega)
      have hc : 0 ≤ ((2 * M : ℕ) : ℝ) * (L ^ (d + 1) / ((d + 1).factorial : ℝ)) := by positivity
      have hjc := jetConst_nonneg (d + 1)
      have e1 : ((2 * M : ℕ) : ℝ) * (L ^ (d + 1) / ((d + 1).factorial : ℝ) *
          (jetConst (d + 1) * (4 * (2 * R + j * L) ^ 2) *
            ((2 * R + j * L) ^ ((5 + δ) / 2))⁻¹ / (2 * R + j * L) ^ (d + 1))) =
          ((2 * M : ℕ) : ℝ) * (L ^ (d + 1) / ((d + 1).factorial : ℝ)) *
            (4 * jetConst (d + 1) * ((2 * R + j * L) ^ 2 *
              ((2 * R + j * L) ^ ((5 + δ) / 2))⁻¹ / (2 * R + j * L) ^ (d + 1))) := by ring
      have e2 : ((2 * M : ℕ) : ℝ) * (L ^ (d + 1) / ((d + 1).factorial : ℝ) *
          (jetConst (d + 1) * (4 * R ^ 2) * (R ^ ((5 + δ) / 2))⁻¹ / R ^ (d + 1))) =
          ((2 * M : ℕ) : ℝ) * (L ^ (d + 1) / ((d + 1).factorial : ℝ)) *
            (4 * jetConst (d + 1) * (R ^ 2 * (R ^ ((5 + δ) / 2))⁻¹ / R ^ (d + 1))) := by ring
      rw [e1, e2]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 (by positivity)) hc
  choose! aP aN TP hTP TN hTN hcP hcN hiP hiN hP hN hb using hblock
  set lab := familyLabels (d := d) F (cofactorSupply R) with hlab
  -- the atom sets
  set UP : Finset ℕ := (range J).biUnion fun j => (TP j).image (aP j) with hUP
  set UN : Finset ℕ := (range J).biUnion fun j => (TN j).image (aN j) with hUN
  have hsep : ∀ j j' : ℕ, j < J → j' < J → ∀ n : ℕ, 2 * R + j * L < n →
      (n : ℝ) < 2 * R + j * L + L → 2 * R + j' * L < n → (n : ℝ) < 2 * R + j' * L + L →
      j = j' := by
    intro j j' _ _ n h1 h2 h3 h4
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have : ((j : ℝ) + 1) * L ≤ j' * L :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast h) hL.le
      linarith
    · have : ((j' : ℝ) + 1) * L ≤ j * L :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast h) hL.le
      linarith
  have hdisjP : (↑(range J) : Set ℕ).PairwiseDisjoint fun j => (TP j).image (aP j) := by
    intro j hj j' hj' hne
    rw [Function.onFun, Finset.disjoint_left]
    intro n hn hn'
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hn
    obtain ⟨x', hx', he⟩ := mem_image.mp hn'
    have hj1 := mem_range.mp hj
    have hj2 := mem_range.mp hj'
    have p1 := hP j hj1 x (hTP j hj1 hx)
    have p2 := hP j' hj2 x' (hTP j' hj2 hx')
    rw [he] at p2
    exact hne (hsep j j' hj1 hj2 _ p1.1 p1.2.1 p2.1 p2.2.1)
  have hdisjN : (↑(range J) : Set ℕ).PairwiseDisjoint fun j => (TN j).image (aN j) := by
    intro j hj j' hj' hne
    rw [Function.onFun, Finset.disjoint_left]
    intro n hn hn'
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hn
    obtain ⟨x', hx', he⟩ := mem_image.mp hn'
    have hj1 := mem_range.mp hj
    have hj2 := mem_range.mp hj'
    have p1 := hN j hj1 x (hTN j hj1 hx)
    have p2 := hN j' hj2 x' (hTN j' hj2 hx')
    rw [he] at p2
    exact hne (hsep j j' hj1 hj2 _ p1.1 p1.2.1 p2.1 p2.2.1)
  have hμP : ∀ n ∈ UP, μ n = 1 := by
    intro n hn
    obtain ⟨j, hj, hn⟩ := mem_biUnion.mp hn
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hn
    exact (hP j (mem_range.mp hj) x (hTP j (mem_range.mp hj) hx)).2.2.1
  have hμN : ∀ n ∈ UN, μ n = -1 := by
    intro n hn
    obtain ⟨j, hj, hn⟩ := mem_biUnion.mp hn
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hn
    exact (hN j (mem_range.mp hj) x (hTN j (mem_range.mp hj) hx)).2.2.1
  have hdisj : Disjoint UP UN := by
    rw [Finset.disjoint_left]
    intro n hn hn'
    have := (hμP n hn).symm.trans (hμN n hn')
    norm_num at this
  have hcardP : UP.card = J * M := by
    rw [hUP, card_biUnion hdisjP]
    rw [show J * M = ∑ _j ∈ range J, M by rw [sum_const, card_range, smul_eq_mul]]
    apply sum_congr rfl
    intro j hj
    rw [card_image_of_injOn ((hiP j (mem_range.mp hj)).mono (hTP j (mem_range.mp hj))),
      hcP j (mem_range.mp hj)]
  have hcardN : UN.card = J * M := by
    rw [hUN, card_biUnion hdisjN]
    rw [show J * M = ∑ _j ∈ range J, M by rw [sum_const, card_range, smul_eq_mul]]
    apply sum_congr rfl
    intro j hj
    rw [card_image_of_injOn ((hiN j (mem_range.mp hj)).mono (hTN j (mem_range.mp hj))),
      hcN j (mem_range.mp hj)]
  refine ⟨UP, UN, hdisj, hμP, hμN, fun n hn => ?_, hcardP, hcardN, fun δ hδ0 hδ1 => ?_⟩
  · -- positions and shapes
    have hpos : ∀ j < J, 2 * R ≤ 2 * R + j * L ∧ 2 * R + j * L + L ≤ 4 * R := by
      intro j hj
      have hj0 : (0 : ℝ) ≤ j * L := by positivity
      have hjJ : ((j : ℝ) + 1) * L ≤ J * L :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hj) hL.le
      constructor <;> nlinarith
    rcases mem_union.mp hn with hn | hn
    · obtain ⟨j, hj, hn⟩ := mem_biUnion.mp hn
      obtain ⟨x, hx, rfl⟩ := mem_image.mp hn
      have hj' := mem_range.mp hj
      obtain ⟨p1, p2, -, hxF, hsh⟩ := hP j hj' x (hTP j hj' hx)
      obtain ⟨b1, b2⟩ := hpos j hj'
      exact ⟨by linarith, by linarith, x.1, hxF, hsh⟩
    · obtain ⟨j, hj, hn⟩ := mem_biUnion.mp hn
      obtain ⟨x, hx, rfl⟩ := mem_image.mp hn
      have hj' := mem_range.mp hj
      obtain ⟨p1, p2, -, hxF, hsh⟩ := hN j hj' x (hTN j hj' hx)
      obtain ⟨b1, b2⟩ := hpos j hj'
      exact ⟨by linarith, by linarith, x.1, hxF, hsh⟩
  · -- the norm
    have hδ : 0 < 5 + δ := by linarith
    have hfun : (fun t => ∑ n ∈ UP ∪ UN, ((μ n : ℤ) : ℝ) * atom n t) =
        fun t => ∑ j ∈ range J, (∑ x ∈ TP j, atom (aP j x) t - ∑ x ∈ TN j, atom (aN j x) t) := by
      funext t
      rw [sum_union hdisj, sum_sub_distrib]
      have h1 : ∑ n ∈ UP, ((μ n : ℤ) : ℝ) * atom n t = ∑ j ∈ range J, ∑ x ∈ TP j, atom (aP j x) t := by
        rw [hUP, sum_biUnion hdisjP]
        apply sum_congr rfl
        intro j hj
        rw [sum_image ((hiP j (mem_range.mp hj)).mono (hTP j (mem_range.mp hj)))]
        apply sum_congr rfl
        intro x hx
        rw [(hP j (mem_range.mp hj) x (hTP j (mem_range.mp hj) hx)).2.2.1]
        simp
      have h2 : ∑ n ∈ UN, ((μ n : ℤ) : ℝ) * atom n t =
          -∑ j ∈ range J, ∑ x ∈ TN j, atom (aN j x) t := by
        rw [hUN, sum_biUnion hdisjN, ← sum_neg_distrib]
        apply sum_congr rfl
        intro j hj
        rw [sum_image ((hiN j (mem_range.mp hj)).mono (hTN j (mem_range.mp hj))),
          ← sum_neg_distrib]
        apply sum_congr rfl
        intro x hx
        rw [(hN j (mem_range.mp hj) x (hTN j (mem_range.mp hj) hx)).2.2.1]
        simp
      rw [h1, h2]
      ring
    rw [hfun]
    have hfin : ∀ j ∈ range J, GammaFinite δ (fun t => ∑ x ∈ TP j, atom (aP j x) t -
        ∑ x ∈ TN j, atom (aN j x) t) := by
      intro j hj
      have hj' := mem_range.mp hj
      refine (GammaFinite.sum _ fun x hx => gammaFinite_atom hδ ?_).sub
        (GammaFinite.sum _ fun x hx => gammaFinite_atom hδ ?_)
      · have := (hP j hj' x (hTP j hj' hx)).1
        have : (0 : ℝ) ≤ j * L := by positivity
        linarith
      · have := (hN j hj' x (hTN j hj' hx)).1
        have : (0 : ℝ) ≤ j * L := by positivity
        linarith
    refine (gammaNorm_sum_le hδ _ hfin).trans ?_
    refine (sum_le_sum fun j hj => hb j (mem_range.mp hj) δ hδ0 hδ1).trans (le_of_eq ?_)
    rw [sum_const, card_range, nsmul_eq_mul]

end RHTower.CubicGamma
