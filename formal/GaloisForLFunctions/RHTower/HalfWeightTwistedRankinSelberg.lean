import GaloisForLFunctions.RHTower.HalfWeightTwistedEisenstein
import GaloisForLFunctions.RHTower.HalfWeightRankinSelberg

/-!
# Rankin–Selberg unfolding against the weight-½ Eisenstein series with a character

* `eisHalf_eq_two_tsum_pos_psi`: for an even character and `Re w > 1`, `E(z,w;ψ) = 2 Σ_{p} F_z(p)` over
  positive bottom rows (the rows `±p` contribute `F(-p) = ψ̄(-1) F(p) = F(p)`).
* **`unfold_eisHalf_psi`**: if `G(γz) = ψ̄(d) \overline{j(γ,z)} G(z)` on `Γ₀(4M)` and `G y^w` is integrable
  on the strip, then `∫_𝒟 Σ_c G(out c · z) E(out c · z, w; ψ) dμ = 2 ∫_{strip} G y^w` for `Re w > 1`.
* `rsFoldTw`, **`differentiableAt_rsFoldTw`**: the folded integral against `E*_ψ` is holomorphic on
  `Re w > 1/4` for continuous `G` whose translates decay faster than every power of `y^{±1}` on `𝒟`.
* **`rsFoldTw_eq`**: for even `ψ₀` and `Re w > 1` it equals `2 L(4w-1, ψ̄₀²) ∫_{strip} G y^w`.
-/

open Real Complex Filter Topology MeasureTheory UpperHalfPlane Metric Set
open CongruenceSubgroup ModularGroup
open scoped MatrixGroups Pointwise

namespace GaloisForLFunctions.RHTower.HalfWeight

open GaloisForLFunctions.HTGeometry

noncomputable section

/-! ### Unfolding with an even character -/

section Unfold

variable (M : ℕ) (ψ : DirichletCharacter ℂ (4 * M))

/-- For an even character and `Re w > 1`: `E(z,w;ψ) = 2 Σ_{positive rows} F(p)`. -/
theorem eisHalf_eq_two_tsum_pos_psi (hev : ψ (-1) = 1) {w : ℂ} (hw : 1 < w.re) (z : UpperHalfPlane) :
    eisHalf M ψ w z = 2 * ∑' p : posRows M, Fp M ψ w z p := by
  set F := Fp M ψ w z
  have hS := summable_indicator M ψ hw z
  have hsum : ∀ s ⊆ adm4 M, Summable (s.indicator F) := by
    intro s hs
    refine Summable.of_norm_bounded hS fun p => ?_
    by_cases hp : p ∈ s
    · rw [Set.indicator_of_mem hp, Set.indicator_of_mem (hs hp)]
    · rw [Set.indicator_of_notMem hp, norm_zero]; exact norm_nonneg _
  set N := adm4 M \ posRows M
  have hsplit : (adm4 M).indicator F = (posRows M).indicator F + N.indicator F := by
    funext p
    rw [Pi.add_apply]
    by_cases h1 : p ∈ posRows M
    · rw [Set.indicator_of_mem h1, Set.indicator_of_mem (posRows_subset M h1),
        Set.indicator_of_notMem (fun h => h.2 h1), add_zero]
    · by_cases h2 : p ∈ adm4 M
      · rw [Set.indicator_of_mem h2, Set.indicator_of_notMem h1,
          Set.indicator_of_mem (show p ∈ N from ⟨h2, h1⟩), zero_add]
      · rw [Set.indicator_of_notMem h2, Set.indicator_of_notMem h1,
          Set.indicator_of_notMem (fun h => h2 h.1), add_zero]
  have hneg : ∑' p : ℤ × ℤ, N.indicator F p = ∑' p : ℤ × ℤ, (posRows M).indicator F p := by
    rw [← (Equiv.neg (ℤ × ℤ)).tsum_eq]
    refine tsum_congr fun p => ?_
    simp only [Equiv.neg_apply]
    by_cases hp : p ∈ posRows M
    · have h1 : -p ∈ N := by
        refine ⟨?_, ?_⟩
        · obtain ⟨c, d⟩ := p; exact (mem_adm4_neg_iff M c d).2 hp.1
        · intro h; exact (neg_mem_posRows_iff M hp.1).1 h hp
      rw [Set.indicator_of_mem h1, Set.indicator_of_mem hp]
      obtain ⟨c, d⟩ := p
      show F (-c, -d) = F (c, d)
      simp only [F]
      rw [Fp_neg, hev, map_one, one_mul]
    · have h1 : -p ∉ N := by
        rintro ⟨h1, h2⟩
        have hp' : p ∈ adm4 M := by
          obtain ⟨c, d⟩ := p; exact (mem_adm4_neg_iff M c d).1 h1
        exact hp (by have := (neg_mem_posRows_iff M h1).2 h2; simpa using this)
      rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem hp]
  rw [eisHalf_eq_tsum_indicator, hsplit, Pi.add_def, (hsum _ (posRows_subset M)).tsum_add
    (hsum _ Set.sdiff_subset), hneg, ← tsum_subtype (posRows M) F, two_mul]

/-- The summand with a character: `G(γ_p z) Im(γ_p z)^w = G(z) F_z(p)`. -/
theorem G_rowMat_eq_psi {G : UpperHalfPlane → ℂ}
    (hG : ∀ γ ∈ Gamma0 (4 * M), ∀ z, G (γ • z) =
      starRingEnd ℂ (ψ (ent γ 1 1 : ZMod (4 * M))) * starRingEnd ℂ (jU γ z) * G z)
    (w : ℂ) (z : UpperHalfPlane) (p : posRows M) :
    G (rowMat M p • z) * (((rowMat M p • z).im : ℝ) : ℂ) ^ w = G z * Fp M ψ w z p := by
  set γ : Gamma0 (4 * M) := ⟨rowMat M p, rowMat_mem M p⟩
  have he := eTerm_eq_Fp M ψ w z γ
  have h10 : ent γ 1 0 = p.1.1 := rowMat_10 M p
  have h11 : ent γ 1 1 = p.1.2 := rowMat_11 M p
  rw [h10, h11] at he
  rw [← he, eTerm, hG _ (rowMat_mem M p)]
  ring

/-- **Rankin–Selberg unfolding with an even character.** If `G(γz) = ψ̄(d) \overline{j(γ,z)} G(z)` on
`Γ₀(4M)` and `G(z) y^w` is integrable on the strip, then for `Re w > 1`
`∫_𝒟 Σ_c G(out c · z) E(out c · z, w; ψ) dμ = 2 ∫_{strip} G(z) y^w dμ`. -/
theorem unfold_eisHalf_psi [NeZero M] (hev : ψ (-1) = 1) {w : ℂ} (hw : 1 < w.re)
    {G : UpperHalfPlane → ℂ}
    (hG : ∀ γ ∈ Gamma0 (4 * M), ∀ z, G (γ • z) =
      starRingEnd ℂ (ψ (ent γ 1 1 : ZMod (4 * M))) * starRingEnd ℂ (jU γ z) * G z)
    (hint : IntegrableOn (fun z : UpperHalfPlane => G z * ((z.im : ℝ) : ℂ) ^ w) modularStrip) :
    ∫ z in fd, ∑ c : Cos0 M, G (Quotient.out c • z) * eisHalf M ψ w (Quotient.out c • z) =
      2 * ∫ z in modularStrip, G z * ((z.im : ℝ) : ℂ) ^ w := by
  set f : UpperHalfPlane → ℂ := fun z => G z * ((z.im : ℝ) : ℂ) ^ w with hf
  have hfinv : ∀ (h : translationSubgroup) (z : UpperHalfPlane), f (h • z) = f z := by
    intro h z
    obtain ⟨n, hn⟩ := translationSubgroup_smul_eq h z
    simp only [f]
    have hd : ent (T ^ n) 1 1 = 1 := by
      simp [ent, ModularGroup.coe_T_zpow]
    rw [hn, hG _ (zpow_mem (T_mem_Gamma0 M) n), jU_T_zpow, hd, Int.cast_one, map_one, map_one,
      one_mul, one_mul, UpperHalfPlane.modular_T_zpow_smul]
    simp
  have hU := isFundamentalDomain_repT M
  have hintU : IntegrableOn f (⋃ ic, repT M ic • fd) :=
    (hU.integrableOn_iff isFundamentalDomain_modularStrip hfinv).mpr hint
  rw [isFundamentalDomain_modularStrip.setIntegral_eq hU hfinv,
    SelbergPoincareUnfolding.integral_iUnion_eq_integral_tsum isFundamentalDomain_fd
      (repT_injective M) hintU, ← integral_const_mul]
  congr 1
  funext z
  set g : Cos0 M × posRows M → ℂ := fun cp => f (repT M (cp.2, cp.1) • z)
  have hg : ∀ cp : Cos0 M × posRows M, g cp =
      G (Quotient.out cp.1 • z) * Fp M ψ w (Quotient.out cp.1 • z) cp.2 := by
    intro cp
    simp only [g, f, repT_smul]
    exact G_rowMat_eq_psi M ψ hG w _ cp.2
  have hslice : ∀ c : Cos0 M, Summable fun p : posRows M => ‖g (c, p)‖ := by
    intro c
    have hS := summable_indicator M ψ hw (Quotient.out c • z)
    have h2 : Summable fun p : posRows M => ‖Fp M ψ w (Quotient.out c • z) p‖ :=
      (hS.subtype (posRows M)).congr fun p => by
        simp only [Function.comp, Set.indicator_of_mem (posRows_subset M p.2)]
    refine (h2.mul_left ‖G (Quotient.out c • z)‖).congr fun p => ?_
    rw [hg, norm_mul]
  have hgs : Summable g := by
    refine Summable.of_norm ?_
    exact (summable_prod_of_nonneg (fun _ => norm_nonneg _)).2 ⟨hslice, Summable.of_finite⟩
  have e1 : ∑' ic : posRows M × Cos0 M, f (repT M ic • z) = ∑' cp : Cos0 M × posRows M, g cp := by
    rw [← (Equiv.prodComm (Cos0 M) (posRows M)).tsum_eq]
    rfl
  rw [e1, hgs.tsum_prod, tsum_fintype, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [hg]
  rw [tsum_mul_left, eisHalf_eq_two_tsum_pos_psi M ψ hev hw]
  ring

end Unfold

/-! ### The twisted folded Rankin–Selberg integral -/

section Twisted

variable {q : ℕ} [hq : Fact q.Prime] (ψ₀ : DirichletCharacter ℂ q) (M' : ℕ) [NeZero M']

instance neZero_level : NeZero (M' * q ^ 2) :=
  ⟨mul_ne_zero (NeZero.ne M') (pow_ne_zero _ hq.out.ne_zero)⟩

omit [NeZero M'] in
theorem psiL_neg_one : psiL ψ₀ M' (-1) = ψ₀ (-1) := by
  have h := DirichletCharacter.changeLevel_eq_cast_of_dvd ψ₀ (q_dvd_level M') (-1)
  simp only [Units.val_neg, Units.val_one] at h
  rw [psiL, h, ZMod.cast_neg (q_dvd_level M'), ZMod.cast_one (q_dvd_level M')]

/-- `∫_𝒟 Σ_{c ∈ Γ₀(4M'q²)\SL₂(ℤ)} G(out c · z) E*_ψ(out c · z, w) dμ`. -/
def rsFoldTw (G : UpperHalfPlane → ℂ) (w : ℂ) : ℂ :=
  ∫ z in fd, ∑ c : Cos0 (M' * q ^ 2), G (Quotient.out c • z) * EstarTw ψ₀ M' (Quotient.out c • z) w

/-- **Holomorphy of the twisted folded Rankin–Selberg integral** on `Re w > 1/4`. -/
theorem differentiableAt_rsFoldTw (h2 : ψ₀ ^ 2 ≠ 1) {G : UpperHalfPlane → ℂ} (hGc : Continuous G)
    (hdec : ∀ (A : ℝ) (c : Cos0 (M' * q ^ 2)), IntegrableOn (fun z : UpperHalfPlane =>
      ‖G (Quotient.out c • z)‖ * ((Quotient.out c • z).im ^ A + (Quotient.out c • z).im ^ (-A))) fd)
    {w₀ : ℂ} (h1 : 1 / 4 < w₀.re) :
    DifferentiableAt ℂ (rsFoldTw ψ₀ M' G) w₀ := by
  obtain ⟨r, hr0, C, A, hC0, hgrow⟩ := EstarTw_growth ψ₀ M' h2 h1
  set R := min r ((w₀.re - 1 / 4) / 2) with hR
  have hR0 : 0 < R := lt_min hr0 (by linarith)
  have hRr : R ≤ r := min_le_left _ _
  have hR1 : R ≤ (w₀.re - 1 / 4) / 2 := min_le_right _ _
  have hstrip : ∀ w ∈ ball w₀ R, 1 / 4 < w.re := by
    intro w hw
    obtain ⟨h3, h4⟩ := re_ge_of_mem_closedBall (ball_subset_closedBall hw)
    linarith
  set F : ℂ → UpperHalfPlane → ℂ := fun w z =>
    ∑ c : Cos0 (M' * q ^ 2), G (Quotient.out c • z) * EstarTw ψ₀ M' (Quotient.out c • z) w
  set bound : UpperHalfPlane → ℝ := fun z => ∑ c : Cos0 (M' * q ^ 2),
    C * (‖G (Quotient.out c • z)‖ * ((Quotient.out c • z).im ^ A + (Quotient.out c • z).im ^ (-A)))
  have hmeas : ∀ w ∈ ball w₀ R, AEStronglyMeasurable (F w) (volume.restrict fd) := by
    intro w hw
    have h3 := hstrip w hw
    refine Continuous.aestronglyMeasurable ?_
    refine continuous_finsetSum _ fun c _ => ?_
    exact (hGc.comp (continuous_smul_sl _)).mul
      ((continuous_EstarTw ψ₀ M' h2 h3).comp (continuous_smul_sl _))
  have hdiff : ∀ z : UpperHalfPlane, DifferentiableOn ℂ (fun w => F w z) (ball w₀ R) := by
    intro z w hw
    have h3 := hstrip w hw
    refine DifferentiableAt.differentiableWithinAt ?_
    simp only [F]
    refine DifferentiableAt.fun_sum fun c _ => ?_
    exact (differentiableAt_EstarTw ψ₀ M' h2 _ h3).const_mul _
  have hbound : ∀ z : UpperHalfPlane, ∀ w ∈ ball w₀ R, ‖F w z‖ ≤ bound z := by
    intro z w hw
    have hwr : w ∈ closedBall w₀ r := closedBall_subset_closedBall hRr (ball_subset_closedBall hw)
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => ?_)
    rw [norm_mul]
    have := hgrow w hwr (Quotient.out c • z)
    calc ‖G (Quotient.out c • z)‖ * ‖EstarTw ψ₀ M' (Quotient.out c • z) w‖
        ≤ ‖G (Quotient.out c • z)‖ * (C * ((Quotient.out c • z).im ^ A + (Quotient.out c • z).im ^ (-A))) :=
          mul_le_mul_of_nonneg_left this (norm_nonneg _)
      _ = _ := by ring
  have hboundInt : Integrable bound (volume.restrict fd) :=
    integrable_finsetSum _ fun c _ => (hdec A c).const_mul C
  exact differentiableAt_integral_of_cauchy_dominated hR0 hmeas hdiff hbound hboundInt

/-- **The twisted Rankin–Selberg identity**: for even `ψ₀` and `Re w > 1`,
`∫_𝒟 Σ_c G(out c · z) E*_ψ(out c · z, w) dμ = 2 L(4w-1, ψ̄₀²) ∫_{strip} G(z) y^w dμ`. -/
theorem rsFoldTw_eq (h1 : ψ₀ ≠ 1) (h2 : ψ₀ ^ 2 ≠ 1) (hcop : q.Coprime (4 * M')) (hev : ψ₀ (-1) = 1)
    {G : UpperHalfPlane → ℂ}
    (hG : ∀ γ ∈ Gamma0 (4 * (M' * q ^ 2)), ∀ z, G (γ • z) =
      starRingEnd ℂ (psiL ψ₀ M' (ent γ 1 1 : ZMod (4 * (M' * q ^ 2)))) * starRingEnd ℂ (jU γ z) * G z)
    {w : ℂ} (hw : 1 < w.re)
    (hint : IntegrableOn (fun z : UpperHalfPlane => G z * ((z.im : ℝ) : ℂ) ^ w) modularStrip) :
    rsFoldTw ψ₀ M' G w = 2 * RTw ψ₀ w * ∫ z in modularStrip, G z * ((z.im : ℝ) : ℂ) ^ w := by
  unfold rsFoldTw
  simp_rw [EstarTw_eq ψ₀ M' h1 h2 hcop hw]
  have e : ∀ z : UpperHalfPlane, ∑ c : Cos0 (M' * q ^ 2), G (Quotient.out c • z) *
      (RTw ψ₀ w * eisHalf (M' * q ^ 2) (psiL ψ₀ M') w (Quotient.out c • z)) =
      RTw ψ₀ w * ∑ c : Cos0 (M' * q ^ 2), G (Quotient.out c • z) *
        eisHalf (M' * q ^ 2) (psiL ψ₀ M') w (Quotient.out c • z) := by
    intro z; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun c _ => by ring
  simp_rw [e]
  rw [integral_const_mul, unfold_eisHalf_psi (M' * q ^ 2) (psiL ψ₀ M')
    (by rw [psiL_neg_one, hev]) hw hG hint]
  ring

end Twisted

end

end GaloisForLFunctions.RHTower.HalfWeight
