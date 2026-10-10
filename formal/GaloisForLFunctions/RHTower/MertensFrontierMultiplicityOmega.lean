import GaloisForLFunctions.RHTower.RayPolylogMultiplicity
import GaloisForLFunctions.RHTower.MobiusMertensAbscissaLittlewood
import GaloisForLFunctions.RHTower.FareyDiscrepancyOmega

/-!
# Graded Ω for the Mertens function at the zero frontier

Let `Θ = sup {Re ρ : ζ(ρ) = 0}` (`zetaZeroAbscissa`). Unconditionally `M(N) = O(N^{Θ+ε})`
(`mobiusMertens_subpower_zetaZeroAbscissa`). This module shows that the frontier line `Re s = Θ`
grades the Ω-behaviour of `M` by multiplicity.

* **Strict law at any exponent** (`natCast_order_lt_of_mertens_littleO_at`). For `½ ≤ θ < 1`, if
  `M(N) = O(N^{θ+ε})` for every `ε > 0` and `|M(x)| ≤ ε x^θ (1 + log x)^a` for `x ≥ T_ε`, then every
  point of `Re s = θ` has `ζ`-order `< a + 1`.
* **Graded Ω at the frontier** (`not_mertens_littleO_zetaZeroAbscissa_of_le_order`). If a zero `ρ`
  of order `m` lies on `Re s = Θ`, then `M(x) ≠ o(x^Θ (1 + log x)^a)` for every `a ≤ m - 1`, with
  no hypothesis. In particular `M(x) ≠ o(x^Θ)` whenever `Θ` is attained
  (`not_mertens_littleO_zetaZeroAbscissa`). Under RH (`Θ = ½`, attained by Hardy's zeros) this is
  `M ≠ o(√x)`.

**Proof.** On `Re s > θ` the transform `G(s) = ∫_1^∞ M(x) x^{-s-1} dx` is holomorphic and
`G(s)·s·(s - 1)ζ(s) = s - 1`. Along `s = ρ + r` the Mellin tail bound gives
`‖G(ρ + r)‖ ≤ η r^{-(a+1)} + C_η`, and the ray lemma caps the order.
-/

open Complex Filter Topology MeasureTheory Set Asymptotics

namespace RHTower

noncomputable section

/-- `M(x) = o(x^θ (1 + log x)^a)`, in explicit form. -/
def MertensLittleOAt (θ a : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, 1 ≤ T ∧ ∀ x : ℝ, T ≤ x →
    |mertensFunctionReal x| ≤ ε * x ^ θ * (1 + Real.log x) ^ a

theorem mertensFunctionReal_natFloor (x : ℝ) :
    mertensFunctionReal (⌊x⌋₊ : ℝ) = mertensFunctionReal x := by
  unfold mertensFunctionReal
  rw [Nat.floor_natCast]

theorem abs_mertensFunctionReal_le_of_subpower {θ ε C : ℝ} (hθε : 0 ≤ θ + ε) (hC : 0 ≤ C)
    (hM : ∀ N : ℕ, ‖mobiusMertensPartialSum N‖ ≤ C * ((N : ℝ) + 1) ^ (θ + ε)) {x : ℝ}
    (hx : 1 ≤ x) : |mertensFunctionReal x| ≤ C * 2 ^ (θ + ε) * x ^ (θ + ε) := by
  have hx0 : 0 < x := by linarith
  rw [← mertensFunctionReal_natFloor, ← norm_mobiusMertensPartialSum_eq_abs_mertensFunctionReal]
  have hfl : ((⌊x⌋₊ : ℕ) : ℝ) + 1 ≤ 2 * x := by
    have := Nat.floor_le hx0.le
    linarith
  calc ‖mobiusMertensPartialSum ⌊x⌋₊‖ ≤ C * (((⌊x⌋₊ : ℕ) : ℝ) + 1) ^ (θ + ε) := hM _
    _ ≤ C * (2 * x) ^ (θ + ε) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hfl hθε) hC
    _ = C * 2 ^ (θ + ε) * x ^ (θ + ε) := by rw [Real.mul_rpow (by norm_num) hx0.le]; ring

theorem differentiableOn_mertensMellin_of_subpower {θ : ℝ} (hθ : 0 ≤ θ)
    (hM : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
      ‖mobiusMertensPartialSum N‖ ≤ C * ((N : ℝ) + 1) ^ (θ + ε)) :
    DifferentiableOn ℂ mertensMellin {s : ℂ | θ < s.re} := by
  intro s hs
  have hs' : θ < s.re := hs
  set ε : ℝ := (s.re - θ) / 2 with hε
  obtain ⟨C, hC, hMC⟩ := hM ε (by rw [hε]; linarith)
  have htop : mertensC =O[atTop] fun x : ℝ => x ^ (-(-(θ + ε))) := by
    refine IsBigO.of_bound (C * 2 ^ (θ + ε)) ?_
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    have hx0 : 0 < x := by linarith
    rw [neg_neg, mertensC, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _)]
    exact abs_mertensFunctionReal_le_of_subpower (by rw [hε]; linarith) hC hMC hx
  have hbot : mertensC =O[𝓝[>] 0] fun x : ℝ => x ^ (-(-s.re - 1)) := by
    refine IsBigO.of_bound 0 ?_
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with x hx
    rw [mertensC, mertensFunctionReal_eq_zero_of_lt_one hx.2]
    simp
  have hd : DifferentiableAt ℂ (mellin mertensC) (-s) :=
    mellin_differentiableAt_of_isBigO_rpow (locallyIntegrable_mertensC.locallyIntegrableOn _)
      htop (by rw [Complex.neg_re, hε]; linarith) hbot (by rw [Complex.neg_re]; linarith)
  exact (hd.comp s differentiableAt_id.neg).differentiableWithinAt

theorem mertensMellin_mul_eq_of_subpower {θ : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (hM : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
      ‖mobiusMertensPartialSum N‖ ≤ C * ((N : ℝ) + 1) ^ (θ + ε))
    {s : ℂ} (hs : θ < s.re) :
    mertensMellin s * (s * zetaResidueUnit s) = s - 1 := by
  set U : Set ℂ := {s : ℂ | θ < s.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hFa : AnalyticOnNhd ℂ (fun s => mertensMellin s * (s * zetaResidueUnit s)) U :=
    ((differentiableOn_mertensMellin_of_subpower hθ hM).mul (differentiableOn_id.mul
      (fun z _ => (analyticAt_zetaResidueUnit z).differentiableAt.differentiableWithinAt))).analyticOnNhd
      hUo
  have hGa : AnalyticOnNhd ℂ (fun s : ℂ => s - 1) U := fun z _ => analyticAt_id.sub analyticAt_const
  have h2U : (2 : ℂ) ∈ U := by simp [hU]; linarith
  have hev : (fun s => mertensMellin s * (s * zetaResidueUnit s)) =ᶠ[𝓝 (2 : ℂ)]
      fun s : ℂ => s - 1 := by
    have hopen : IsOpen {w : ℂ | 1 < w.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds (show (1 : ℝ) < (2 : ℂ).re by norm_num)] with w hw
    have hw1 : 1 < w.re := hw
    have hw0 : w ≠ 0 := by intro h; rw [h, Complex.zero_re] at hw1; linarith
    have hwne : w ≠ 1 := by intro h; rw [h, Complex.one_re] at hw1; linarith
    have hz : riemannZeta w ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hw1
    rw [mertensMellin_eq_inv hw1, zetaResidueUnit, Function.update_of_ne hwne]
    field_simp
  exact hFa.eqOn_of_preconnected_of_eventuallyEq hGa (convex_halfSpace_re_gt _).isPreconnected
    h2U hev hs

/-- **Strict multiplicity law at any exponent.** -/
theorem natCast_order_lt_of_mertens_littleO_at {θ a : ℝ} (ha : 0 ≤ a) (hθ : 1 / 2 ≤ θ)
    (hθ1 : θ < 1)
    (hM : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
      ‖mobiusMertensPartialSum N‖ ≤ C * ((N : ℝ) + 1) ^ (θ + ε))
    (hlittle : MertensLittleOAt θ a) {ρ : ℂ} (hρ : ρ.re = θ) :
    ((analyticOrderAt riemannZeta ρ).toNat : ℝ) < a + 1 := by
  have hρpos : 0 < ρ.re := by rw [hρ]; linarith
  have hρlt : ρ.re < 1 := by rw [hρ]; exact hθ1
  have hρ1 : ρ ≠ 1 := by intro h; rw [h, Complex.one_re] at hρlt; exact lt_irrefl _ hρlt
  have horderFinite : analyticOrderAt riemannZeta ρ ≠ ⊤ := by
    rw [← xi_analyticOrderAt_eq_riemannZeta_of_mem_strip ⟨hρpos, hρlt⟩]
    exact xi_orderAt_ne_top ρ
  set n : ℕ := (analyticOrderAt riemannZeta ρ).toNat with hn
  have hncoe : (n : ℕ∞) = analyticOrderAt riemannZeta ρ := ENat.coe_toNat horderFinite
  obtain ⟨p, hp, _, hfactor⟩ :=
    ((analyticOn_riemannZeta ρ hρ1).analyticOrderAt_eq_natCast).mp hncoe.symm
  set P : ℂ → ℂ := fun z => z * ((z - 1) * p z) with hP
  have hPc : ContinuousAt P ρ :=
    continuousAt_id.mul ((continuousAt_id.sub continuousAt_const).mul hp.continuousAt)
  have hfac : ∀ᶠ z in 𝓝 ρ, z * zetaResidueUnit z = (z - ρ) ^ n * P z := by
    filter_upwards [hfactor, isOpen_compl_singleton.mem_nhds hρ1] with z hz hne
    rw [zetaResidueUnit, Function.update_of_ne hne, hz, smul_eq_mul, hP]
    ring
  have hHc : ContinuousAt (fun z : ℂ => z - 1) ρ := continuousAt_id.sub continuousAt_const
  have hHρ : ρ - 1 ≠ 0 := sub_ne_zero.mpr hρ1
  have hray_re : ∀ r : ℝ, (ρ + (r : ℂ) * 1).re = θ + r := fun r => by simp [hρ]
  have hFE : ∀ᶠ r : ℝ in 𝓝[>] 0,
      mertensMellin (ρ + r * 1) * ((ρ + r * 1) * zetaResidueUnit (ρ + r * 1)) =
        (ρ + r * 1) - 1 := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hr0 : (0 : ℝ) < r := hr
    exact mertensMellin_mul_eq_of_subpower (by linarith) hθ1 hM (by rw [hray_re]; linarith)
  -- the Mellin tail bound
  obtain ⟨C₁, hC₁, hM₁⟩ := hM 1 one_pos
  obtain ⟨T, hT1, hT⟩ := hlittle 1 one_pos
  set B : ℝ := max 1 T with hBdef
  have hB : ∀ t : ℝ, 1 < t → ‖mertensC t‖ ≤ B * t ^ θ * (1 + Real.log t) ^ a := by
    intro t ht
    rw [mertensC, Complex.norm_real, Real.norm_eq_abs]
    have ht0 : 0 < t := by linarith
    have hw1 : 1 ≤ t ^ θ * (1 + Real.log t) ^ a :=
      one_le_mul_of_one_le_of_one_le (Real.one_le_rpow ht.le (by linarith))
        (Real.one_le_rpow (by linarith [Real.log_nonneg ht.le]) ha)
    rcases le_or_gt T t with hTt | htT
    · calc |mertensFunctionReal t| ≤ 1 * t ^ θ * (1 + Real.log t) ^ a := hT t hTt
        _ ≤ B * t ^ θ * (1 + Real.log t) ^ a := by
            rw [mul_assoc, mul_assoc]
            exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    · calc |mertensFunctionReal t| ≤ |t| := abs_mertensFunctionReal_le_abs t
        _ = t := abs_of_pos ht0
        _ ≤ B := htT.le.trans (le_max_right _ _)
        _ = B * 1 := (mul_one B).symm
        _ ≤ B * (t ^ θ * (1 + Real.log t) ^ a) :=
            mul_le_mul_of_nonneg_left hw1 (le_max_of_le_left zero_le_one)
        _ = B * t ^ θ * (1 + Real.log t) ^ a := by ring
  have htail := norm_integral_Ioi_one_cpow_mul_le (f := mertensC) (c := θ) (a := a) (B := B) ha
    hB (fun ε hε => by
      obtain ⟨T', hT'1, hT'⟩ := hlittle ε hε
      exact ⟨T', hT'1, fun t ht => by
        rw [mertensC, Complex.norm_real, Real.norm_eq_abs]; exact hT' t ht⟩)
  have hF : ∀ η : ℝ, 0 < η → ∃ C : ℝ, ∀ᶠ r : ℝ in 𝓝[>] 0,
      ‖mertensMellin (ρ + r * 1)‖ ≤ η * r ^ (-(a + 1)) + C := by
    intro η hη
    obtain ⟨C, hC⟩ := htail η hη
    refine ⟨C, ?_⟩
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with r hr
    have h := hC (ρ + r * 1) (by rw [hray_re]; linarith [hr.1]) (by rw [hray_re]; linarith [hr.2])
    rw [hray_re, show (θ + r - θ : ℝ) = r by ring] at h
    rw [mertensMellin_eq_integral_Ici, integral_Ici_eq_integral_Ioi]
    exact h
  exact natCast_lt_of_ray_littleO (E := fun z => z * zetaResidueUnit z)
    (H := fun z => z - 1) ha hPc hfac hHc hHρ hFE hF

/-- **Graded Ω at the zero frontier.** If a zero `ρ` with `Re ρ = Θ` has order `m`, then
`M(x) ≠ o(x^Θ (1 + log x)^a)` for every `0 ≤ a` with `a + 1 ≤ m`. -/
theorem not_mertens_littleO_zetaZeroAbscissa_of_le_order {ρ : ℂ} (hz : riemannZeta ρ = 0)
    (hρ : ρ.re = zetaZeroAbscissa) {a : ℝ} (ha : 0 ≤ a)
    (hm : a + 1 ≤ ((analyticOrderAt riemannZeta ρ).toNat : ℝ)) :
    ¬ MertensLittleOAt zetaZeroAbscissa a := by
  intro hlittle
  have hρ1 : ρ.re < 1 := by
    by_contra h
    exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp h) hz
  have hlt := natCast_order_lt_of_mertens_littleO_at ha half_le_zetaZeroAbscissa
    (by rw [← hρ]; exact hρ1) (fun ε hε => mobiusMertens_subpower_zetaZeroAbscissa ε hε)
    hlittle hρ
  linarith

/-- **`M(x) ≠ o(x^Θ)` when the frontier is attained.** -/
theorem not_mertens_littleO_zetaZeroAbscissa {ρ : ℂ} (hz : riemannZeta ρ = 0)
    (hρ : ρ.re = zetaZeroAbscissa) : ¬ MertensLittleOAt zetaZeroAbscissa 0 := by
  have hρpos : 0 < ρ.re := by rw [hρ]; exact zetaZeroAbscissa_pos
  have hρ1 : ρ.re < 1 := by
    by_contra h
    exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp h) hz
  have hρne1 : ρ ≠ 1 := by intro h; rw [h, Complex.one_re] at hρ1; exact lt_irrefl _ hρ1
  have hfin : analyticOrderAt riemannZeta ρ ≠ ⊤ := by
    rw [← xi_analyticOrderAt_eq_riemannZeta_of_mem_strip ⟨hρpos, hρ1⟩]
    exact xi_orderAt_ne_top ρ
  have hne : analyticOrderAt riemannZeta ρ ≠ 0 := by
    rw [Ne, analyticOrderAt_eq_zero]
    rintro (h | h)
    exacts [h (analyticOn_riemannZeta ρ hρne1), h hz]
  have h1 : 1 ≤ (analyticOrderAt riemannZeta ρ).toNat := by
    rw [Nat.one_le_iff_ne_zero]
    intro h
    exact hne ((ENat.toNat_eq_zero.mp h).resolve_right hfin)
  exact not_mertens_littleO_zetaZeroAbscissa_of_le_order hz hρ le_rfl
    (by simpa using (show (1 : ℝ) ≤ ((analyticOrderAt riemannZeta ρ).toNat : ℝ) by
      exact_mod_cast h1))

end

end RHTower
