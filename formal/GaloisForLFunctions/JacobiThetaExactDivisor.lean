import GaloisForLFunctions.JacobiThetaRectangleCharge
import GaloisForLFunctions.RHTower.Peeling

open Complex Set Metric Filter

namespace GaloisForLFunctions

noncomputable section

def thetaRectangleClosed (τ z₁ : ℂ) : Set ℂ :=
  uIcc z₁.re (z₁.re + 1) ×ℂ uIcc z₁.im (z₁.im + τ.im)

def thetaRectangleInterior (τ z₁ : ℂ) : Set ℂ :=
  Ioo z₁.re (z₁.re + 1) ×ℂ Ioo z₁.im (z₁.im + τ.im)

theorem thetaRectangle_zero_mem_interior {τ z₁ z : ℂ} (hτ : 0 < τ.im)
    (hreg : ThetaRectangleBoundaryRegular τ z₁)
    (hzK : z ∈ thetaRectangleClosed τ z₁) (hz0 : jacobiTheta₂ z τ = 0) :
    z ∈ thetaRectangleInterior τ z₁ := by
  rw [thetaRectangleClosed, Complex.mem_reProdIm,
    uIcc_of_le (by linarith : z₁.re ≤ z₁.re + 1),
    uIcc_of_le (by linarith : z₁.im ≤ z₁.im + τ.im), mem_Icc] at hzK
  rw [thetaRectangleInterior, Complex.mem_reProdIm, mem_Ioo]
  rcases hzK with ⟨⟨hxl, hxr⟩, ⟨hyl, hyr⟩⟩
  have hxl' : z₁.re < z.re := lt_of_le_of_ne hxl (fun he => by
    apply hreg.2 z.im
    · rw [uIcc_of_le (by linarith : z₁.im ≤ z₁.im + τ.im)]
      exact ⟨hyl, hyr⟩
    · rw [show (z₁.re : ℂ) + z.im * I = z by
        apply Complex.ext
        · simpa using he
        · simp]
      exact hz0)
  have hxr' : z.re < z₁.re + 1 := lt_of_le_of_ne hxr (fun he => by
    apply thetaRectangle_right_ne_zero hreg z.im
      (by rw [uIcc_of_le (by linarith : z₁.im ≤ z₁.im + τ.im)]; exact ⟨hyl, hyr⟩)
    rw [show ((z₁.re + 1 : ℝ) : ℂ) + z.im * I = z by
      apply Complex.ext
      · simpa using he.symm
      · simp]
    exact hz0)
  have hyl' : z₁.im < z.im := lt_of_le_of_ne hyl (fun he => by
    apply hreg.1 z.re
    · rw [uIcc_of_le (by linarith : z₁.re ≤ z₁.re + 1)]
      exact ⟨hxl, hxr⟩
    · rw [show (z.re : ℂ) + z₁.im * I = z by
        apply Complex.ext
        · simp
        · simpa using he]
      exact hz0)
  have hyr' : z.im < z₁.im + τ.im := lt_of_le_of_ne hyr (fun he => by
    apply thetaRectangle_top_ne_zero hreg z.re
    rw [show (z.re : ℂ) + (z₁.im + τ.im : ℝ) * I = z by
      apply Complex.ext
      · simp
      · simpa using he.symm]
    exact hz0)
  exact ⟨⟨hxl', hxr'⟩, ⟨hyl', hyr'⟩⟩

theorem jacobiTheta₂_order_ne_top {τ : ℂ} (hτ : 0 < τ.im) (z : ℂ) :
    analyticOrderAt (jacobiTheta₂ · τ) z ≠ ⊤ := by
  intro htop
  have hev0 : (jacobiTheta₂ · τ) =ᶠ[nhds z] (0 : ℂ → ℂ) := by
    filter_upwards [analyticOrderAt_eq_top.mp htop] with w hw
    simpa using hw
  have hall := (jacobiTheta₂_analyticOnNhd_fst τ hτ).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    isPreconnected_univ (mem_univ z) hev0
  have hzero : jacobiTheta₂ 0 τ = 0 := hall (mem_univ 0)
  have hnonzero : jacobiTheta₂ 0 τ ≠ 0 := by
    simpa [Bottcher.thetaThree] using Bottcher.thetaThree_ne_zero_of_im_pos hτ
  exact hnonzero hzero

end
end GaloisForLFunctions

namespace GaloisForLFunctions

noncomputable section

open Metric

/-- A regular theta rectangle contains total zero multiplicity one. -/
theorem thetaRectangle_zero_count_one {τ z₁ : ℂ} (hτ : 0 < τ.im)
    (hreg : ThetaRectangleBoundaryRegular τ z₁) :
    ∃ (t : Finset ℂ) (m : ℂ → ℕ) (h : ℂ → ℂ),
      (∀ w ∈ t, w ∈ thetaRectangleInterior τ z₁ ∧ jacobiTheta₂ w τ = 0) ∧
      (∀ z ∈ thetaRectangleInterior τ z₁, jacobiTheta₂ z τ = 0 → z ∈ t) ∧
      AnalyticOnNhd ℂ h
        (thetaRectangleInterior τ z₁ ∪ (jacobiTheta₂ · τ) ⁻¹' {0}ᶜ) ∧
      (∀ z ∈ thetaRectangleInterior τ z₁ ∪ (jacobiTheta₂ · τ) ⁻¹' {0}ᶜ, h z ≠ 0) ∧
      (∀ z ∈ thetaRectangleInterior τ z₁ ∪ (jacobiTheta₂ · τ) ⁻¹' {0}ᶜ,
        jacobiTheta₂ z τ = (∏ w ∈ t, (z - w) ^ m w) * h z) ∧
      ∑ w ∈ t, m w = 1 := by
  let K : Set ℂ := thetaRectangleClosed τ z₁
  let Z : Set ℂ := {z ∈ K | jacobiTheta₂ z τ = 0}
  have hKcompact : IsCompact K := by
    dsimp [K, thetaRectangleClosed]
    exact isCompact_uIcc.reProdIm isCompact_uIcc
  have hcod : ((jacobiTheta₂ · τ) ⁻¹' {0}ᶜ) ∈ codiscreteWithin (Set.univ : Set ℂ) :=
    (jacobiTheta₂_analyticOnNhd_fst τ hτ).preimage_zero_mem_codiscreteWithin
      (x := 0) (by
        simpa [Bottcher.thetaThree] using Bottcher.thetaThree_ne_zero_of_im_pos hτ)
      (Set.mem_univ 0) isConnected_univ
  have hcodK : ((jacobiTheta₂ · τ) ⁻¹' {0}ᶜ) ∈ codiscreteWithin K :=
    Filter.codiscreteWithin_mono (Set.subset_univ _) hcod
  have hZ : Z.Finite := by
    refine (hKcompact.finite_diff_of_mem_codiscreteWithin hcodK).subset ?_
    intro z hz
    rw [Set.mem_sep_iff] at hz
    exact ⟨hz.1, by simp [Set.mem_preimage, hz.2]⟩
  let t : Finset ℂ := hZ.toFinset
  let N : Set ℂ := (jacobiTheta₂ · τ) ⁻¹' {0}ᶜ
  let U : Set ℂ := thetaRectangleInterior τ z₁ ∪ N
  have hNopen : IsOpen N := by
    dsimp [N]
    exact isOpen_compl_singleton.preimage
      (jacobiTheta₂_analyticOnNhd_fst τ hτ).continuous
  have hOopen : IsOpen (thetaRectangleInterior τ z₁) := by
    dsimp [thetaRectangleInterior]
    exact isOpen_Ioo.reProdIm isOpen_Ioo
  have hUopen : IsOpen U := hOopen.union hNopen
  have hsub : K ⊆ U := by
    intro z hzK
    by_cases hz0 : jacobiTheta₂ z τ = 0
    · exact Or.inl (thetaRectangle_zero_mem_interior hτ hreg hzK hz0)
    · exact Or.inr (by simp [N, hz0])
  have htU : ∀ w ∈ t, w ∈ U := by
    intro w hw
    have hwZ : w ∈ Z := hZ.mem_toFinset.mp hw
    exact hsub hwZ.1
  have htdata : ∀ w ∈ t, w ∈ thetaRectangleInterior τ z₁ ∧ jacobiTheta₂ w τ = 0 := by
    intro w hw
    have hwZ : w ∈ Z := hZ.mem_toFinset.mp hw
    exact ⟨thetaRectangle_zero_mem_interior hτ hreg hwZ.1 hwZ.2, hwZ.2⟩
  have hzeros : ∀ z ∈ U, jacobiTheta₂ z τ = 0 → z ∈ t := by
    intro z hzU hz0
    have hzO : z ∈ thetaRectangleInterior τ z₁ := by
      rcases hzU with hzO | hzN
      · exact hzO
      · have hnz : jacobiTheta₂ z τ ≠ 0 := by simpa [N] using hzN
        exact (hnz hz0).elim
    have hzK : z ∈ K := by
      dsimp [thetaRectangleInterior] at hzO
      dsimp [K, thetaRectangleClosed]
      rcases hzO with ⟨hx, hy⟩
      exact ⟨mem_uIcc_of_le hx.1.le hx.2.le, mem_uIcc_of_le hy.1.le hy.2.le⟩
    exact hZ.mem_toFinset.mpr ⟨hzK, hz0⟩
  have hord : ∀ w ∈ t, analyticOrderAt (jacobiTheta₂ · τ) w ≠ ⊤ :=
    fun w _ => jacobiTheta₂_order_ne_top hτ w
  obtain ⟨m, h, hhan, hh0, hfact⟩ :=
    RHTower.exists_multi_peel hUopen
      ((jacobiTheta₂_analyticOnNhd_fst τ hτ).mono (subset_univ _))
      t htU hzeros hord
  have hin : ∀ w ∈ t,
      z₁.re < w.re ∧ w.re < (thetaRectangleUpperRight τ z₁).re ∧
        z₁.im < w.im ∧ w.im < (thetaRectangleUpperRight τ z₁).im := by
    intro w hw
    have hd := (htdata w hw).1
    rw [thetaRectangleInterior, Complex.mem_reProdIm, mem_Ioo, mem_Ioo] at hd
    rw [thetaRectangleUpperRight_re, thetaRectangleUpperRight_im]
    exact ⟨hd.1.1, hd.1.2, hd.2.1, hd.2.2⟩
  have hlogeq : logDeriv (jacobiTheta₂ · τ) = fun z => thetaLogDeriv z τ := by
    funext z
    rw [logDeriv_apply, thetaLogDeriv, (hasDerivAt_jacobiTheta₂_fst z hτ).deriv]
  have hcount := RHTower.rectIntegral_logDeriv_boxCount t (fun w => w) m
    hUopen hin (by
      rw [thetaRectangleUpperRight_re, thetaRectangleUpperRight_im]
      simpa [K, thetaRectangleClosed] using hsub) hhan hh0 hfact
  rw [hlogeq] at hcount
  have hcharge := thetaRectangleIntegral_eq_two_pi_I hτ hreg
  have heq : 2 * Real.pi * I =
      2 * Real.pi * I * (∑ w ∈ t, (m w : ℂ)) := hcharge.symm.trans hcount
  have hc : (2 * (Real.pi : ℂ) * I) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
  have hsumC : (∑ w ∈ t, (m w : ℂ)) = 1 := by
    apply mul_left_cancel₀ hc
    calc
      (2 * (Real.pi : ℂ) * I) * (∑ w ∈ t, (m w : ℂ)) = 2 * Real.pi * I := heq.symm
      _ = (2 * (Real.pi : ℂ) * I) * 1 := (mul_one _).symm
  have hsum : ∑ w ∈ t, m w = 1 := by exact_mod_cast hsumC
  refine ⟨t, m, h, htdata, ?_, hhan, hh0, hfact, hsum⟩
  intro z hzO hz0
  exact hzeros z (Or.inl hzO) hz0

end
end GaloisForLFunctions

namespace GaloisForLFunctions

noncomputable section

/-- Every complex point has a lattice translate in the closed axis-aligned fundamental rectangle. -/
theorem exists_lattice_translate_mem_thetaRectangleClosed {τ z₁ z : ℂ} (hτ : 0 < τ.im) :
    ∃ m n : ℤ, z + m + n * τ ∈ thetaRectangleClosed τ z₁ := by
  let n : ℤ := -⌊(z.im - z₁.im) / τ.im⌋
  let q : ℂ := z + n * τ
  have hqim : q.im = z.im + n * τ.im := by simp [q]
  have hqlo : z₁.im ≤ q.im := by
    rw [hqim]
    dsimp [n]
    push_cast
    have h := Int.sub_floor_div_mul_nonneg (z.im - z₁.im) hτ
    linarith
  have hqhi : q.im ≤ z₁.im + τ.im := by
    rw [hqim]
    dsimp [n]
    push_cast
    have h := Int.sub_floor_div_mul_lt (z.im - z₁.im) hτ
    linarith
  let m : ℤ := -⌊q.re - z₁.re⌋
  let p : ℂ := q + m
  have hpre : p.re = q.re + m := by simp [p]
  have hpim : p.im = q.im := by simp [p]
  have hplo : z₁.re ≤ p.re := by
    rw [hpre]
    dsimp [m]
    push_cast
    have h := Int.floor_le (q.re - z₁.re)
    linarith
  have hphi : p.re ≤ z₁.re + 1 := by
    rw [hpre]
    dsimp [m]
    push_cast
    have h := Int.lt_floor_add_one (q.re - z₁.re)
    linarith
  refine ⟨m, n, ?_⟩
  have hpK : p ∈ thetaRectangleClosed τ z₁ := by
    rw [thetaRectangleClosed, Complex.mem_reProdIm,
      uIcc_of_le (by linarith : z₁.re ≤ z₁.re + 1),
      uIcc_of_le (by linarith : z₁.im ≤ z₁.im + τ.im), mem_Icc]
    exact ⟨⟨hplo, hphi⟩, by rw [hpim]; exact ⟨hqlo, hqhi⟩⟩
  convert hpK using 1
  dsimp [p, q]
  ring

/-- Every theta zero has a lattice translate in the open regular rectangle. -/
theorem exists_lattice_translate_zero_mem_thetaRectangleInterior {τ z₁ z : ℂ} (hτ : 0 < τ.im)
    (hreg : ThetaRectangleBoundaryRegular τ z₁) (hz0 : jacobiTheta₂ z τ = 0) :
    ∃ m n : ℤ, z + m + n * τ ∈ thetaRectangleInterior τ z₁ ∧
      jacobiTheta₂ (z + m + n * τ) τ = 0 := by
  obtain ⟨m, n, hmem⟩ := exists_lattice_translate_mem_thetaRectangleClosed (z := z) hτ
  have hn0 := jacobiTheta₂_eq_zero_add_int_mul_tau hz0 n
  have hm0 := jacobiTheta₂_eq_zero_add_int hn0 m
  have hzero : jacobiTheta₂ (z + m + n * τ) τ = 0 := by
    convert hm0 using 1
    ring
  exact ⟨m, n, thetaRectangle_zero_mem_interior hτ hreg hmem hzero, hzero⟩

end
end GaloisForLFunctions

namespace GaloisForLFunctions

noncomputable section

/-- Every regular fundamental rectangle contains exactly one theta zero. -/
theorem thetaRectangle_unique_zero {τ z₁ : ℂ} (hτ : 0 < τ.im)
    (hreg : ThetaRectangleBoundaryRegular τ z₁) :
    ∃ p ∈ thetaRectangleInterior τ z₁, jacobiTheta₂ p τ = 0 ∧
      ∀ z ∈ thetaRectangleInterior τ z₁, jacobiTheta₂ z τ = 0 → z = p := by
  let z₀ : ℂ := (1 + τ) / 2
  have hz₀ : jacobiTheta₂ z₀ τ = 0 := jacobiTheta₂_thetaHalfPeriod_eq_zero τ
  obtain ⟨mp, np, hpO, hp0⟩ :=
    exists_lattice_translate_zero_mem_thetaRectangleInterior hτ hreg hz₀
  let p : ℂ := z₀ + mp + np * τ
  obtain ⟨t, m, h, htdata, hzeros, hhan, hh0, hfact, hsum⟩ :=
    thetaRectangle_zero_count_one hτ hreg
  have hpMem : p ∈ t := hzeros p hpO hp0
  have hmpos : ∀ w ∈ t, 0 < m w := by
    intro w hw
    by_contra hnot
    have hmw : m w = 0 := Nat.eq_zero_of_not_pos hnot
    have hprod : (∏ u ∈ t, (w - u) ^ m u) ≠ 0 := by
      rw [Finset.prod_ne_zero_iff]
      intro u hu
      by_cases huw : u = w
      · subst u
        simp [hmw]
      · exact pow_ne_zero _ (sub_ne_zero.mpr (Ne.symm huw))
    have hwU : w ∈ thetaRectangleInterior τ z₁ ∪ (jacobiTheta₂ · τ) ⁻¹' {0}ᶜ :=
      Or.inl (htdata w hw).1
    have hwnz : jacobiTheta₂ w τ ≠ 0 := by
      rw [hfact w hwU]
      exact mul_ne_zero hprod (hh0 w hwU)
    exact hwnz (htdata w hw).2
  have hcardle : t.card ≤ ∑ w ∈ t, m w := by
    rw [Finset.card_eq_sum_ones]
    exact Finset.sum_le_sum fun w hw => Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (hmpos w hw))
  have hcardpos : 0 < t.card := Finset.card_pos.mpr ⟨p, hpMem⟩
  have hcard : t.card = 1 := by omega
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hcard
  have hpa : p = a := by simpa [ha] using hpMem
  refine ⟨p, hpO, hp0, ?_⟩
  intro z hzO hz0
  have hzMem : z ∈ t := hzeros z hzO hz0
  have hza : z = a := by simpa [ha] using hzMem
  exact hza.trans hpa.symm

end
end GaloisForLFunctions

namespace GaloisForLFunctions

noncomputable section

/-- **Exact Jacobi-theta divisor.** The zeros are precisely the odd half-period lattice orbit. -/
theorem jacobiTheta₂_eq_zero_iff_thetaHalfPeriod_add_lattice {τ z : ℂ} (hτ : 0 < τ.im) :
    jacobiTheta₂ z τ = 0 ↔
      ∃ m n : ℤ, z = thetaHalfPeriod τ + m + n * τ := by
  constructor
  · intro hz0
    obtain ⟨z₁, hreg⟩ := exists_thetaRectangleBoundaryRegular hτ
    obtain ⟨p, hpO, hp0, hunique⟩ := thetaRectangle_unique_zero hτ hreg
    have hhalf0 : jacobiTheta₂ (thetaHalfPeriod τ) τ = 0 :=
      jacobiTheta₂_thetaHalfPeriod_eq_zero τ
    obtain ⟨mp, np, hp'O, hp'0⟩ :=
      exists_lattice_translate_zero_mem_thetaRectangleInterior hτ hreg hhalf0
    obtain ⟨mz, nz, hzO, hz'0⟩ :=
      exists_lattice_translate_zero_mem_thetaRectangleInterior hτ hreg hz0
    have hpEq : thetaHalfPeriod τ + mp + np * τ = p :=
      hunique _ hp'O hp'0
    have hzEq : z + mz + nz * τ = p :=
      hunique _ hzO hz'0
    refine ⟨mp - mz, np - nz, ?_⟩
    push_cast
    linear_combination hzEq - hpEq
  · rintro ⟨m, n, rfl⟩
    exact jacobiTheta₂_thetaHalfPeriod_add_lattice_eq_zero τ m n

end
end GaloisForLFunctions
