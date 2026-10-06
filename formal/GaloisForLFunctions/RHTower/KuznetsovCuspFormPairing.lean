import GaloisForLFunctions.RHTower.KuznetsovPoincarePairing
import GaloisForLFunctions.RHTower.DeckCuspidalFourierExpansion
import GaloisForLFunctions.RHTower.HalfWeightWhittaker

/-!
# Poincaré series against cuspidal eigenfunctions

For a cuspidal Laplace eigenfunction `U` (eigenvalue `λ = ¼ − ν²`) and a cusp vector `v` of frequency
`μ ≠ 0`, the frequency `μ` coefficient `∫_0^1 e(−μx)⟨v, U(x+iy)⟩ dx` is `c · √y K_ν(2π|μ|y)` for one
constant `c` (`deckCuspCoeff_eigen_eq_whittaker`): `ρ(T)^{N+1} = 1` forces `μ(N+1) = n ∈ ℤ`, the
coefficient is the combination `Σ_q conj(v_q) a_{q,n}(y)` of the Fourier modes of the coordinates over
the level period, and each mode is a Whittaker function.  Unfolding the Poincaré series and
`∫_0^∞ K_ν(t)e^{−t}t^{a−1}dt = 2^{a−1}Γ(a)Γ(a+ν)Γ(a−ν)/Γ(2a)` give

`∫_𝒟 ⟨U(·|s, μ, v), U⟩ = 2c (2πμ)^{½−s̄} 2^{s̄−3/2} Γ(s̄−½)Γ(s̄−½+ν)Γ(s̄−½−ν)/Γ(2s̄−1)`

for `Re s > 1`, `|Re ν| < Re s − ½` (`integral_inner_poincSeries_eigen`).
-/

open UpperHalfPlane ModularGroup MeasureTheory Set EisensteinSeries Complex
open scoped MatrixGroups InnerProductSpace ComplexConjugate

namespace GaloisForLFunctions.RHTower.DeckPointPair

open MaassFiniteDeckDirichlet MaassCongruenceL2 SelbergMaassCongruenceTrace
  GaloisForLFunctions.HTGeometry SelbergMaassFourier SelbergMaassMean MaassWhittaker

noncomputable section

variable {N : ℕ}

local instance gammaNormalKCF (N : ℕ) : (CongruenceSubgroup.Gamma (N + 1)).Normal :=
  CongruenceSubgroup.Gamma_normal (N + 1)

/-! ## The level period -/

theorem deckRho_T_level (u : DeckSpace N) :
    deckRho N (ModularGroup.T ^ ((N + 1 : ℕ) : ℤ)) u = u := by
  have hg : ModularGroup.T ^ ((N + 1 : ℕ) : ℤ) ∈ CongruenceSubgroup.Gamma (N + 1) := by
    simpa only [Int.natAbs_natCast] using
      CongruenceSubgroup.ModularGroup_T_pow_mem_Gamma (N + 1 : ℕ) (N + 1 : ℕ) (dvd_refl _)
  have hdeck : (QuotientGroup.mk (ModularGroup.T ^ ((N + 1 : ℕ) : ℤ)) : Deck N) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr hg
  rw [deckRho, hdeck]
  ext q
  simp [finiteRegularUnitary_apply]

/-- A nonzero cusp vector of frequency `μ` has `μ(N+1) ∈ ℤ`. -/
theorem IsCuspEigen.exists_int {μ : ℝ} {v : DeckSpace N} (hv : IsCuspEigen μ v) (hv0 : v ≠ 0) :
    ∃ n : ℤ, μ * ((N + 1 : ℕ) : ℝ) = n := by
  have h := deckRho_T_zpow_eigen hv ((N + 1 : ℕ) : ℤ)
  rw [deckRho_T_level] at h
  have h1 : cexp (2 * Real.pi * Complex.I * μ * ((N + 1 : ℕ) : ℤ)) = 1 := by
    by_contra hne
    have : (1 - cexp (2 * Real.pi * Complex.I * μ * ((N + 1 : ℕ) : ℤ))) • v = 0 := by
      rw [sub_smul, one_smul, ← h, sub_self]
    exact hv0 ((smul_eq_zero.1 this).resolve_left (sub_ne_zero.2 (Ne.symm hne)))
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 h1
  refine ⟨n, ?_⟩
  have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have : ((μ * ((N + 1 : ℕ) : ℝ) : ℝ) : ℂ) = (n : ℂ) := by
    apply mul_left_cancel₀ hpi
    push_cast at hn ⊢
    linear_combination hn
  exact_mod_cast this

/-! ## Coefficients as combinations of Fourier modes -/

/-- The weighted inner product `e(−μx)⟨v, U(x+iy)⟩` is `1`-periodic. -/
theorem periodic_cuspIntegrand {U : ℍ → DeckSpace N} (hUe : deckEquivariant N U) {μ : ℝ}
    {v : DeckSpace N} (hv : IsCuspEigen μ v) {y : ℝ} (hy : 0 < y) :
    Function.Periodic (fun x : ℝ => cuspChar μ x * ⟪v, U (ofComplex (⟨x, y⟩ : ℂ))⟫_ℂ) 1 := by
  intro x
  simp only [ofComplex_eq_hLine hy]
  have h := T_zpow_smul_hLine hy 1 x
  simp only [zpow_one, Int.cast_one] at h
  have hflip : ⟪v, deckRho N ModularGroup.T (U (hLine hy x))⟫_ℂ =
      ⟪(deckRho N ModularGroup.T).symm v, U (hLine hy x)⟫_ℂ := by
    rw [← (deckRho N ModularGroup.T).inner_map_map ((deckRho N ModularGroup.T).symm v),
      LinearIsometryEquiv.apply_symm_apply]
  rw [← h, show U (ModularGroup.T • hLine hy x) = deckRho N ModularGroup.T (U (hLine hy x)) from
    hUe _ _, hflip, show cuspChar μ (x + 1) =
    cuspChar μ x * cexp (-(2 * Real.pi * Complex.I * μ * ((1 : ℤ) : ℝ))) by
      rw [cuspChar, cuspChar, ← Complex.exp_add]; congr 1; push_cast; ring]
  have hinv : (deckRho N ModularGroup.T).symm v = cexp (-(2 * Real.pi * Complex.I * μ)) • v := by
    refine symm_eq_of_apply_eq ?_
    rw [map_smul, hv, smul_smul, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, one_smul]
  rw [hinv, inner_smul_left, ← Complex.exp_conj]
  simp only [map_neg, map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  rw [mul_assoc, ← mul_assoc (cexp _), ← Complex.exp_add]
  push_cast
  rw [show -(2 * (Real.pi : ℂ) * Complex.I * μ * 1) + -(2 * Real.pi * -Complex.I * μ) = 0 by ring,
    Complex.exp_zero, one_mul]

theorem inner_eq_sum_conj_mul (v u : DeckSpace N) : ⟪v, u⟫_ℂ = ∑ q, conj (v q) * u q := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [RCLike.inner_apply, mul_comm]

/-- **The coefficient at a cusp vector** is the combination `Σ_q conj(v_q) a_{q,n}(y)` of the Fourier
modes of the coordinates over the level period, `n = μ(N+1)`. -/
theorem deckCuspCoeff_eq_sum_deckMode {U : ℍ → DeckSpace N}
    (hUc : ContinuousOn (fun ζ => U (ofComplex ζ)) {ζ : ℂ | 0 < ζ.im}) (hUe : deckEquivariant N U)
    {μ : ℝ} {v : DeckSpace N} (hv : IsCuspEigen μ v) {n : ℤ} (hn : μ * ((N + 1 : ℕ) : ℝ) = n)
    {y : ℝ} (hy : 0 < y) :
    deckCuspCoeff μ v U y = ∑ q, conj (v q) * deckMode U q n y := by
  have hL : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
  have hslice : ∀ q : Deck N, Continuous fun x : ℝ => U (ofComplex (point x y)) q := fun q => by
    have hc : ContinuousOn (fun ζ => U (ofComplex ζ) q) {ζ : ℂ | 0 < ζ.im} :=
      ((EuclideanSpace.proj q : DeckSpace N →L[ℂ] ℂ).continuous.comp_continuousOn hUc)
    refine hc.comp_continuous (by unfold point; fun_prop : Continuous fun x : ℝ => point x y)
      fun x => ?_
    simpa [point] using hy
  have hgc : Continuous fun x : ℝ => cuspChar μ x * ⟪v, U (ofComplex (⟨x, y⟩ : ℂ))⟫_ℂ := by
    refine (continuous_cuspChar μ).mul ?_
    have : (fun x : ℝ => ⟪v, U (ofComplex (⟨x, y⟩ : ℂ))⟫_ℂ) =
        fun x => ∑ q, conj (v q) * U (ofComplex (point x y)) q := funext fun x => by
      rw [inner_eq_sum_conj_mul, point_eq_mk]
    rw [this]
    exact continuous_finsetSum _ fun q _ => continuous_const.mul (hslice q)
  have hper := periodic_cuspIntegrand hUe hv hy
  have hkernel : ∀ x : ℝ, _root_.RHTower.deningerFourierKernel ((N + 1 : ℕ) : ℝ) n x =
      cuspChar μ x := fun x => by
    have hn' : (n : ℂ) = (μ : ℂ) * (((N + 1 : ℕ) : ℝ) : ℂ) := by exact_mod_cast hn.symm
    have hL' : (((N + 1 : ℕ) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
    rw [_root_.RHTower.deningerFourierKernel, cuspChar, hn']
    congr 1
    field_simp
  -- the right side as one integral over the level period
  have hR : ∑ q, conj (v q) * deckMode U q n y = (1 / (((N + 1 : ℕ) : ℝ) : ℂ)) *
      ∫ x in (0 : ℝ)..((N + 1 : ℕ) : ℝ),
        cuspChar μ x * ⟪v, U (ofComplex (⟨x, y⟩ : ℂ))⟫_ℂ := by
    have hslice' : ∀ q : Deck N, Continuous fun x : ℝ => U (ofComplex (⟨x, y⟩ : ℂ)) q :=
      fun q => by simpa only [point_eq_mk] using hslice q
    unfold deckMode coefficient _root_.RHTower.deningerFourierCoeff
    simp only [Function.comp_apply, component, hkernel, inner_eq_sum_conj_mul, Finset.mul_sum,
      point_eq_mk]
    rw [intervalIntegral.integral_finsetSum (f := fun q x =>
      cuspChar μ x * (conj (v q) * U (ofComplex (⟨x, y⟩ : ℂ)) q)) fun q _ =>
      ((continuous_cuspChar μ).mul (continuous_const.mul (hslice' q))).intervalIntegrable _ _,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [mul_left_comm, ← intervalIntegral.integral_const_mul]
    congr 1
    refine intervalIntegral.integral_congr fun x _ => ?_
    simp only
    ring
  have h1 := hper.intervalIntegral_add_zsmul_eq ((N + 1 : ℕ) : ℤ) 0
    (fun a b => hgc.intervalIntegrable a b)
  simp only [zero_add, zsmul_eq_mul, mul_one, Int.cast_natCast] at h1
  rw [hR, deckCuspCoeff, h1, integral_Ico_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le zero_le_one]
  have hL' : (((N + 1 : ℕ) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  push_cast
  field_simp

theorem IsCuspLaplaceEigen.continuous' {lam : ℝ} {U : ℍ → DeckSpace N}
    (hU : IsCuspLaplaceEigen N lam U) : Continuous U := by
  have h := hU.contDiffOn.continuousOn.comp_continuous UpperHalfPlane.continuous_coe
    (fun z => z.im_pos)
  simpa only [Function.comp_def, ofComplex_apply] using h

/-- **Whittaker form of the coefficient at a cusp vector.** -/
theorem deckCuspCoeff_eigen_eq_whittaker {lam : ℝ} {U : ℍ → DeckSpace N}
    (hU : IsCuspLaplaceEigen N lam U) {μ : ℝ} (hμ : μ ≠ 0) {v : DeckSpace N} (hv : IsCuspEigen μ v)
    {ν : ℂ} (hν : ν ^ 2 = 1 / 4 - lam) :
    ∃ c : ℂ, ∀ y, 0 < y → deckCuspCoeff μ v U y = c * whittakerW (2 * Real.pi * |μ|) ν y := by
  by_cases hv0 : v = 0
  · refine ⟨0, fun y _ => ?_⟩
    simp [deckCuspCoeff, hv0]
  obtain ⟨n, hn⟩ := hv.exists_int hv0
  have hL : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp only [Int.cast_zero, mul_eq_zero] at hn
    exact hn.elim hμ (fun h => hL.ne' h)
  have hW := fun q : Deck N => hU.deckMode_eq_whittaker q hn0 hν
  choose ρ hρ using hW
  have hfreq : |signedFrequency ((N + 1 : ℕ) : ℝ) n| = 2 * Real.pi * |μ| := by
    unfold signedFrequency
    rw [← hn, show 2 * Real.pi * (μ * ((N + 1 : ℕ) : ℝ)) / ((N + 1 : ℕ) : ℝ) = 2 * Real.pi * μ by
      field_simp, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
  refine ⟨∑ q, conj (v q) * ρ q, fun y hy => ?_⟩
  rw [deckCuspCoeff_eq_sum_deckMode hU.contDiffOn.continuousOn hU.equivariant hv hn hy,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [hρ q y hy, hfreq]
  ring

/-- **The Mellin transform of a Whittaker coefficient**:
`∫_0^∞ y^{b−2} e^{−ky} c √y K_ν(ky) dy = c k^{−(b−½)} 2^{b−3/2}Γ(b−½)Γ(b−½+ν)Γ(b−½−ν)/Γ(2b−1)`. -/
theorem integral_whittaker_mellin {b ν : ℂ} (hνb : |ν.re| < b.re - 1 / 2) {k : ℝ} (hk : 0 < k)
    (c : ℂ) :
    ∫ y in Ioi (0 : ℝ), (y ^ 2)⁻¹ • ((y : ℂ) ^ b * (Real.exp (-(k * y)) : ℂ) *
      (c * whittakerW k ν y)) =
      c * (k : ℂ) ^ (-(b - 1 / 2)) *
        ((2 : ℂ) ^ (b - 1 / 2 - 1) * Complex.Gamma (b - 1 / 2) *
          Complex.Gamma (b - 1 / 2 + ν) * Complex.Gamma (b - 1 / 2 - ν) /
            Complex.Gamma (2 * (b - 1 / 2))) := by
  set a : ℂ := b - 1 / 2 with ha
  have hare : |ν.re| < a.re := by
    rw [ha, Complex.sub_re]; norm_num; linarith
  set G : ℝ → ℂ := fun t => HalfWeight.Kb ν t * ((Real.exp (-t) : ℝ) : ℂ) * (t : ℂ) ^ (a - 1)
    with hG
  have hpt : ∀ y ∈ Ioi (0 : ℝ), (y ^ 2)⁻¹ • ((y : ℂ) ^ b * (Real.exp (-(k * y)) : ℂ) *
      (c * whittakerW k ν y)) = c * (k : ℂ) ^ (-(a - 1)) * G (k * y) := by
    intro y (hy : 0 < y)
    rw [whittakerW, hG]
    simp only [besK, HalfWeight.Kb]
    have hy' : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
    have hsqrt : ((Real.sqrt y : ℝ) : ℂ) = (y : ℂ) ^ (1 / 2 : ℂ) := by
      rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow hy.le]; push_cast; ring_nf
    have hsplit : (((k * y : ℝ)) : ℂ) ^ (a - 1) = (k : ℂ) ^ (a - 1) * (y : ℂ) ^ (a - 1) := by
      rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hk.le hy.le]
    have hya : (y : ℂ) ^ b * (y : ℂ) ^ (1 / 2 : ℂ) * (((y ^ 2)⁻¹ : ℝ) : ℂ) =
        (y : ℂ) ^ (a - 1) := by
      rw [ha, show b - 1 / 2 - 1 = b + 1 / 2 + (-2 : ℂ) by ring,
        Complex.cpow_add _ _ hy', Complex.cpow_add _ _ hy', Complex.cpow_neg,
        show (2 : ℂ) = ((2 : ℕ) : ℂ) by norm_num, Complex.cpow_natCast]
      push_cast
      ring
    rw [hsplit, Complex.real_smul, hsqrt, Complex.cpow_neg]
    have hk' : (k : ℂ) ^ (a - 1) ≠ 0 := by
      rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hk.ne')]
      exact Complex.exp_ne_zero _
    rw [← hya]
    field_simp
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul,
    integral_comp_mul_left_Ioi G 0 hk, mul_zero, HalfWeight.integral_Kb_exp_cpow hare,
    Complex.real_smul]
  have hk' : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  rw [show -(a - 1) = -a + 1 by ring, Complex.cpow_add _ _ hk', Complex.cpow_one]
  push_cast
  field_simp

/-- **The pairing of a Poincaré series with a cuspidal eigenfunction.** -/
theorem integral_inner_poincSeries_eigen {s : ℂ} (hs : 1 < s.re) {μ : ℝ} (hμ : 0 < μ)
    {v : DeckSpace N} (hv : IsCuspEigen μ v) {lam : ℝ} {U : ℍ → DeckSpace N}
    (hU : IsCuspLaplaceEigen N lam U) {ν : ℂ} (hνs : |ν.re| < s.re - 1 / 2) {c : ℂ}
    (hc : ∀ y, 0 < y → deckCuspCoeff μ v U y = c * whittakerW (2 * Real.pi * |μ|) ν y) :
    ∫ z in fd, ⟪poincSeries (poincProfile s μ) v z, U z⟫_ℂ =
      2 * (c * ((2 * Real.pi * μ : ℝ) : ℂ) ^ (-(conj s - 1 / 2)) *
        ((2 : ℂ) ^ (conj s - 1 / 2 - 1) * Complex.Gamma (conj s - 1 / 2) *
          Complex.Gamma (conj s - 1 / 2 + ν) * Complex.Gamma (conj s - 1 / 2 - ν) /
            Complex.Gamma (2 * (conj s - 1 / 2)))) := by
  rw [integral_inner_poincSeries_eq_deckCuspCoeff hs hμ hv hU.continuous' hU.equivariant hU.memLp]
  congr 1
  have hk : (0 : ℝ) < 2 * Real.pi * μ := by positivity
  rw [← integral_whittaker_mellin (b := conj s) (by rw [Complex.conj_re]; exact hνs) hk c]
  refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
  rw [hc y hy, abs_of_pos hμ]

/-! ## The conjugate series -/

theorem poincProfile_hLine (s : ℂ) (ν : ℝ) {y : ℝ} (hy : 0 < y) (x : ℝ) :
    poincProfile s ν (hLine hy x) =
      (y : ℂ) ^ s * (Real.exp (-(2 * Real.pi * ν * y)) : ℂ) * cuspChar (-ν) x := by
  rw [poincProfile, hLine_im, coe_hLine, cuspChar, Complex.ofReal_exp, mul_assoc ((y : ℂ) ^ s),
    ← Complex.exp_add]
  congr 2
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

/-- **Unfolding the conjugate series in coordinates**:
`∫_𝒟 ⟨P(·| h̄_{s,ν}, w), G⟩ = 2 ∫_0^∞ y^{−2} y^s e^{−2πνy} deckCuspCoeff (−ν) w G y dy`. -/
theorem integral_inner_poincSeries_conjProfile_eq_deckCuspCoeff {s : ℂ} (hs : 1 < s.re) {ν : ℝ}
    (hν : 0 < ν) {w : DeckSpace N} (hw : IsCuspEigen (-ν) w) {G : ℍ → DeckSpace N}
    (hGc : Continuous G) (hGe : deckEquivariant N G) (hGL : MemLp G 2 cellMeasure) :
    ∫ z in fd, ⟪poincSeries (conjProfile s ν) w z, G z⟫_ℂ =
      2 * ∫ y in Ioi (0 : ℝ), (y ^ 2)⁻¹ •
        ((y : ℂ) ^ s * (Real.exp (-(2 * Real.pi * ν * y)) : ℂ) * deckCuspCoeff (-ν) w G y) := by
  have hH : MemLp (fun z => ∑' p : gammaSet 1 1 0, ‖conjProfile s ν (gammaSetMatrix p • z)‖) 2
      cellMeasure := by
    simp_rw [norm_conjProfile]
    exact memLp_tsum_norm_poincProfile hs hν
  have hc := cuspCompatible_conjProfile s hw
  have hint := integrableOn_poincIntegrand_strip hc (continuous_conjProfile s ν) hGc hGe hGL
    (summable_norm_conjProfile hs hν.le) hH
  rw [integral_inner_poincSeries hc (continuous_conjProfile s ν) hGc hGe hGL
    (summable_norm_conjProfile hs hν.le) hH, setIntegral_modularStrip_eq_iterated _ hint]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
  congr 1
  rw [deckCuspCoeff, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ico fun x _ => ?_
  rw [ofComplex_eq_hLine hy, poincIntegrand, conjProfile, Complex.conj_conj, poincProfile_hLine]
  ring

/-- **The pairing of the conjugate series with a cuspidal eigenfunction.** -/
theorem integral_inner_poincSeries_conjProfile_eigen {s : ℂ} (hs : 1 < s.re) {ν : ℝ} (hν : 0 < ν)
    {w : DeckSpace N} (hw : IsCuspEigen (-ν) w) {lam : ℝ} {U : ℍ → DeckSpace N}
    (hU : IsCuspLaplaceEigen N lam U) {β : ℂ} (hβs : |β.re| < s.re - 1 / 2) {c : ℂ}
    (hc : ∀ y, 0 < y → deckCuspCoeff (-ν) w U y = c * whittakerW (2 * Real.pi * |-ν|) β y) :
    ∫ z in fd, ⟪poincSeries (conjProfile s ν) w z, U z⟫_ℂ =
      2 * (c * ((2 * Real.pi * ν : ℝ) : ℂ) ^ (-(s - 1 / 2)) *
        ((2 : ℂ) ^ (s - 1 / 2 - 1) * Complex.Gamma (s - 1 / 2) *
          Complex.Gamma (s - 1 / 2 + β) * Complex.Gamma (s - 1 / 2 - β) /
            Complex.Gamma (2 * (s - 1 / 2)))) := by
  rw [integral_inner_poincSeries_conjProfile_eq_deckCuspCoeff hs hν hw hU.continuous'
    hU.equivariant hU.memLp]
  congr 1
  have hk : (0 : ℝ) < 2 * Real.pi * ν := by positivity
  rw [← integral_whittaker_mellin (b := s) hβs hk c]
  refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
  rw [hc y hy, abs_neg, abs_of_pos hν]

end

end GaloisForLFunctions.RHTower.DeckPointPair
