import GaloisForLFunctions.RHTower.SuzukiCauchyIsometry
import GaloisForLFunctions.RHTower.SuzukiWeilFrakSZeroSeries
import GaloisForLFunctions.RHTower.SuzukiScrewKernelExponentialSeries

/-!
# Suzuki's screw line

Theorem 4.2 of Suzuki, *On the Hilbert space derived from the Weil distribution*: under the
Riemann hypothesis `t ↦ π^{-1/2} 𝔖_t` is a screw line for the screw function `g_ξ`, i.e.

```text
(1/π) ⟪𝔖_t, 𝔖_u⟫_{L²(ℝ)} = G_g(t, u).
```

On the real axis `E^♯ = conj E`, so `𝔖_t = i · conj(A/E) · P_t` and the inner product of two
`𝔖`'s is the inner product of the energy-weighted series `(A/E) · P_t`.  Regrouping `P_t` over
the divisor *support* turns it into a Cauchy series with coefficients `m_ρ c_ρ(t)`, whose `L²`
inner products are computed by the Cauchy-kernel isometry.  The resulting weighted `ℓ²` sum is
exactly Su22's exponential zero series for `G_g`.

Corollary 4.3's forward direction, `‖𝔖_t‖² = 2π Ψ(t)`, follows by putting `u = t`.
-/

open Complex Filter Topology MeasureTheory

namespace RHTower
noncomputable section

/-- The support-level coefficient of Suzuki's series `P_t`. -/
def suzukiPtSupportCoef (t : ℝ) (ρ : XiDivisorSupport) : ℂ :=
  (xiSupportMult ρ : ℂ) *
    ((Complex.exp (-(I * ((xiRealSpectralPointSupport ρ : ℝ) : ℂ) * (t : ℂ))) - 1)
      / ((xiRealSpectralPointSupport ρ : ℝ) : ℂ))

/-- The energy-weighted form of `P_t` on the real axis. -/
def suzukiEnergyPt (t : ℝ) (x : ℝ) : ℂ :=
  suzukiHalfInner ((x : ℝ) : ℂ) * suzukiPtZeroSum t ((x : ℝ) : ℂ)

theorem xiSpectralPoint_copy_eq (hRH : RiemannHypothesis) (ρ : XiDivisorSupport)
    (i : Fin (xiSupportMult ρ)) :
    xiSpectralPoint (⟨ρ, i⟩ : XiZeroCopy) = ((xiRealSpectralPointSupport ρ : ℝ) : ℂ) := by
  rw [xiSpectralPoint_eq_support, ofReal_xiRealSpectralPointSupport hRH]

theorem suzukiPtZeroTerm_ofReal_support (hRH : RiemannHypothesis) (t x : ℝ)
    (ρ : XiDivisorSupport) (i : Fin (xiSupportMult ρ)) :
    suzukiPtZeroTerm t ((x : ℝ) : ℂ) (⟨ρ, i⟩ : XiZeroCopy)
      = ((Complex.exp (-(I * ((xiRealSpectralPointSupport ρ : ℝ) : ℂ) * (t : ℂ))) - 1)
          / ((xiRealSpectralPointSupport ρ : ℝ) : ℂ)) * suzukiCauchyKernel ρ x := by
  rw [suzukiPtZeroTerm, xiSpectralPoint_copy_eq hRH, suzukiCauchyKernel]
  rw [div_mul_eq_div_div, div_eq_mul_inv]

theorem hasSum_suzukiPtSupportCoef (hRH : RiemannHypothesis) (t x : ℝ) :
    HasSum (fun ρ : XiDivisorSupport => suzukiPtSupportCoef t ρ * suzukiCauchyKernel ρ x)
      (suzukiPtZeroSum t ((x : ℝ) : ℂ)) := by
  have hs := (summable_suzukiPtZeroTerm t ((x : ℝ) : ℂ)).hasSum
  have h := hs.sigma (g := fun ρ : XiDivisorSupport =>
      ∑ i : Fin (xiSupportMult ρ), suzukiPtZeroTerm t ((x : ℝ) : ℂ) (⟨ρ, i⟩ : XiZeroCopy))
    (fun ρ => hasSum_fintype _)
  have hfun : (fun ρ : XiDivisorSupport =>
      ∑ i : Fin (xiSupportMult ρ), suzukiPtZeroTerm t ((x : ℝ) : ℂ) (⟨ρ, i⟩ : XiZeroCopy))
      = fun ρ : XiDivisorSupport => suzukiPtSupportCoef t ρ * suzukiCauchyKernel ρ x := by
    funext ρ
    rw [Finset.sum_congr rfl (fun i _ => suzukiPtZeroTerm_ofReal_support hRH t x ρ i),
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      suzukiPtSupportCoef]
    ring
  rw [hfun] at h
  exact h

theorem hasSum_suzukiEnergyPt (hRH : RiemannHypothesis) (t x : ℝ) :
    HasSum (fun ρ : XiDivisorSupport => suzukiPtSupportCoef t ρ * suzukiEnergyKernelFun ρ x)
      (suzukiEnergyPt t x) := by
  have h := (hasSum_suzukiPtSupportCoef hRH t x).mul_left (suzukiHalfInner ((x : ℝ) : ℂ))
  refine h.congr_fun fun ρ => ?_
  rw [suzukiEnergyKernelFun]
  ring

/-! ## Square-summability of the coefficients -/

/-- The copy-level coefficient of `P_t`. -/
def suzukiPtCopyCoef (t : ℝ) (q : XiZeroCopy) : ℂ :=
  (Complex.exp (-(I * xiSpectralPoint q * (t : ℂ))) - 1) / xiSpectralPoint q

theorem norm_suzukiPtCopyCoef_le (t : ℝ) (q : XiZeroCopy) :
    ‖suzukiPtCopyCoef t q‖ ≤ (Real.exp (|t| / 2) + 1) * (1 / ‖xiSpectralPoint q‖) := by
  have hneg : -(I * xiSpectralPoint q * (t : ℂ)) = I * xiSpectralPoint q * ((-t : ℝ) : ℂ) := by
    push_cast; ring
  have h1 : ‖Complex.exp (-(I * xiSpectralPoint q * (t : ℂ))) - 1‖ ≤ Real.exp (|t| / 2) + 1 := by
    rw [hneg]
    refine le_trans (norm_sub_le _ _) ?_
    rw [norm_one]
    have h := norm_exp_I_xiSpectralPoint_mul_le (-t) q
    rw [abs_neg] at h
    linarith
  rw [suzukiPtCopyCoef, norm_div, mul_one_div]
  gcongr

theorem summable_norm_sq_suzukiPtCopyCoef (t : ℝ) :
    Summable fun q : XiZeroCopy => ‖suzukiPtCopyCoef t q‖ ^ 2 := by
  refine Summable.of_nonneg_of_le (fun q => sq_nonneg _) (fun q => ?_)
    (xiSpectralPoint_inv_sq_summable.mul_left ((Real.exp (|t| / 2) + 1) ^ 2))
  have h := norm_suzukiPtCopyCoef_le t q
  have h0 : (0 : ℝ) ≤ ‖suzukiPtCopyCoef t q‖ := norm_nonneg _
  have hpos : (0 : ℝ) < ‖xiSpectralPoint q‖ := norm_pos_iff.mpr (xiSpectralPoint_ne_zero q)
  have hexp : (0 : ℝ) ≤ Real.exp (|t| / 2) + 1 := by positivity
  calc ‖suzukiPtCopyCoef t q‖ ^ 2
      ≤ ((Real.exp (|t| / 2) + 1) * (1 / ‖xiSpectralPoint q‖)) ^ 2 := by nlinarith
    _ = (Real.exp (|t| / 2) + 1) ^ 2 * (1 / ‖xiSpectralPoint q‖ ^ 2) := by
        rw [mul_pow, div_pow]
        ring

theorem suzukiPtSupportCoef_eq (hRH : RiemannHypothesis) (t : ℝ) (ρ : XiDivisorSupport)
    (i : Fin (xiSupportMult ρ)) :
    suzukiPtSupportCoef t ρ = (xiSupportMult ρ : ℂ) * suzukiPtCopyCoef t (⟨ρ, i⟩ : XiZeroCopy) := by
  rw [suzukiPtSupportCoef, suzukiPtCopyCoef, xiSpectralPoint_copy_eq hRH]

theorem summable_weighted_suzukiPtSupportCoef (hRH : RiemannHypothesis) (t : ℝ) :
    Summable fun ρ : XiDivisorSupport =>
      ‖suzukiPtSupportCoef t ρ‖ ^ 2 * suzukiCauchyWeight ρ := by
  have hbase := summable_norm_sq_suzukiPtCopyCoef t
  have hsig := (summable_sigma_of_nonneg (f := fun q : XiZeroCopy => ‖suzukiPtCopyCoef t q‖ ^ 2)
    (fun q => sq_nonneg _)).mp hbase
  refine ((hsig.2).mul_left Real.pi).congr fun ρ => ?_
  have hpos := xiSupportMult_pos ρ
  have hi : Fin (xiSupportMult ρ) := ⟨0, hpos⟩
  show Real.pi * (∑' j : Fin (xiSupportMult ρ), ‖suzukiPtCopyCoef t (⟨ρ, j⟩ : XiZeroCopy)‖ ^ 2)
      = ‖suzukiPtSupportCoef t ρ‖ ^ 2 * suzukiCauchyWeight ρ
  · have hconst : ∀ j : Fin (xiSupportMult ρ),
        ‖suzukiPtCopyCoef t (⟨ρ, j⟩ : XiZeroCopy)‖ ^ 2
          = ‖suzukiPtCopyCoef t (⟨ρ, hi⟩ : XiZeroCopy)‖ ^ 2 := by
      intro j
      rw [suzukiPtCopyCoef, suzukiPtCopyCoef, xiSpectralPoint_copy_eq hRH,
        xiSpectralPoint_copy_eq hRH]
    have htsum : (∑' j : Fin (xiSupportMult ρ),
        ‖suzukiPtCopyCoef t (⟨ρ, j⟩ : XiZeroCopy)‖ ^ 2)
        = (xiSupportMult ρ : ℝ) * ‖suzukiPtCopyCoef t (⟨ρ, hi⟩ : XiZeroCopy)‖ ^ 2 := by
      rw [tsum_fintype, Finset.sum_congr rfl (fun j _ => hconst j), Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [htsum, suzukiPtSupportCoef_eq hRH t ρ hi, suzukiCauchyWeight, norm_mul,
      Complex.norm_natCast, mul_pow]
    have hmR : (0 : ℝ) < (xiSupportMult ρ : ℝ) := by exact_mod_cast hpos
    field_simp


/-! ## The screw line -/

theorem exists_lp_suzukiEnergyPt (hRH : RiemannHypothesis) (t : ℝ) :
    ∃ S : Lp ℂ 2 (volume : Measure ℝ),
      Tendsto (suzukiCauchyPartial hRH (suzukiPtSupportCoef t)) atTop (𝓝 S)
        ∧ (S : ℝ → ℂ) =ᵐ[volume] suzukiEnergyPt t :=
  exists_lp_of_hasSum hRH (suzukiPtSupportCoef t) (summable_weighted_suzukiPtSupportCoef hRH t)
    (suzukiEnergyPt t) (Filter.Eventually.of_forall fun x => hasSum_suzukiEnergyPt hRH t x)

theorem conj_mul_suzukiPtCopyCoef (hRH : RiemannHypothesis) (t u : ℝ) (q : XiZeroCopy) :
    (starRingEnd ℂ) (suzukiPtCopyCoef t q) * suzukiPtCopyCoef u q
      = suzukiScrewExpTerm t u q := by
  have hreal : (starRingEnd ℂ) (xiSpectralPoint q) = xiSpectralPoint q := by
    rw [xiSpectralPoint_eq_ofReal_of_rh hRH, Complex.conj_ofReal]
  have hexp : (starRingEnd ℂ) (Complex.exp (-(I * xiSpectralPoint q * (t : ℂ))))
      = Complex.exp (I * xiSpectralPoint q * (t : ℂ)) := by
    rw [← Complex.exp_conj]
    congr 1
    rw [map_neg, map_mul, map_mul, hreal, Complex.conj_I, Complex.conj_ofReal]
    ring
  rw [suzukiPtCopyCoef, suzukiPtCopyCoef, map_div₀, map_sub, hexp, map_one, hreal,
    suzukiScrewExpTerm, div_mul_div_comm, sq]

theorem tsum_weighted_suzukiPtSupportCoef (hRH : RiemannHypothesis) (t u : ℝ) :
    (∑' ρ : XiDivisorSupport, (starRingEnd ℂ) (suzukiPtSupportCoef t ρ)
        * suzukiPtSupportCoef u ρ * ((suzukiCauchyWeight ρ : ℝ) : ℂ))
      = ((Real.pi : ℝ) : ℂ) * suzukiScrewKernel t u := by
  have hsum := summable_suzukiScrewExpTerm t u
  have hsigma := hsum.tsum_sigma (f := fun q : XiZeroCopy => suzukiScrewExpTerm t u q)
  rw [suzukiScrewKernel_eq_tsum t u, hsigma, ← tsum_mul_left]
  refine tsum_congr fun ρ => ?_
  have hpos := xiSupportMult_pos ρ
  have hi : Fin (xiSupportMult ρ) := ⟨0, hpos⟩
  have hconst : ∀ j : Fin (xiSupportMult ρ),
      suzukiScrewExpTerm t u (⟨ρ, j⟩ : XiZeroCopy)
        = suzukiScrewExpTerm t u (⟨ρ, hi⟩ : XiZeroCopy) := by
    intro j
    rw [suzukiScrewExpTerm, suzukiScrewExpTerm, xiSpectralPoint_copy_eq hRH,
      xiSpectralPoint_copy_eq hRH]
  show _ = ((Real.pi : ℝ) : ℂ) *
    ∑' j : Fin (xiSupportMult ρ), suzukiScrewExpTerm t u (⟨ρ, j⟩ : XiZeroCopy)
  rw [tsum_fintype, Finset.sum_congr rfl (fun j _ => hconst j), Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [suzukiPtSupportCoef_eq hRH t ρ hi, suzukiPtSupportCoef_eq hRH u ρ hi,
    ← conj_mul_suzukiPtCopyCoef hRH t u (⟨ρ, hi⟩ : XiZeroCopy), suzukiCauchyWeight]
  have hmR : ((xiSupportMult ρ : ℝ)) ≠ 0 := by
    have : (0 : ℝ) < (xiSupportMult ρ : ℝ) := by exact_mod_cast hpos
    exact ne_of_gt this
  have hmC : ((xiSupportMult ρ : ℂ)) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]
    omega
  rw [map_mul, Complex.conj_natCast]
  push_cast
  field_simp

theorem integral_conj_suzukiEnergyPt (hRH : RiemannHypothesis) (t u : ℝ) :
    (∫ x : ℝ, (starRingEnd ℂ) (suzukiEnergyPt t x) * suzukiEnergyPt u x)
      = ((Real.pi : ℝ) : ℂ) * suzukiScrewKernel t u := by
  obtain ⟨St, hSt, haet⟩ := exists_lp_suzukiEnergyPt hRH t
  obtain ⟨Su, hSu, haeu⟩ := exists_lp_suzukiEnergyPt hRH u
  have hinner := inner_of_tendsto hRH (suzukiPtSupportCoef t) (suzukiPtSupportCoef u)
    (summable_weighted_suzukiPtSupportCoef hRH t) (summable_weighted_suzukiPtSupportCoef hRH u)
    hSt hSu
  rw [tsum_weighted_suzukiPtSupportCoef hRH t u] at hinner
  rw [← hinner, MeasureTheory.L2.inner_def]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [haet, haeu] with x h1 h2
  rw [RCLike.inner_apply, h1, h2]
  ring

/-- **Suzuki Theorem 4.2 (the screw line).**  Under the Riemann hypothesis the `L²(ℝ)` inner
products of the family `𝔖_t` reproduce Suzuki's kernel `G_g`. -/
theorem inner_suzukiFrakSFull_eq_pi_mul_screwKernel (hRH : RiemannHypothesis) (t u : ℝ) :
    inner ℂ ((memLp_suzukiFrakSFull t).toLp _) ((memLp_suzukiFrakSFull u).toLp _)
      = ((Real.pi : ℝ) : ℂ) * suzukiScrewKernel t u := by
  rw [MeasureTheory.L2.inner_def, ← integral_conj_suzukiEnergyPt hRH t u]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [(memLp_suzukiFrakSFull t).coeFn_toLp, (memLp_suzukiFrakSFull u).coeFn_toLp,
    ae_ne_zero_and_XiC_ne_zero] with x h1 h2 hx
  have hXi : XiC ((x : ℝ) : ℂ) ≠ 0 := hx.2
  have hsharp : XiC ((x : ℝ) : ℂ) / xiHedenmalmDeBrangesESharp ((x : ℝ) : ℂ)
      = (starRingEnd ℂ) (suzukiHalfInner ((x : ℝ) : ℂ)) := by
    rw [suzukiHalfInner, map_div₀, xiHedenmalmDeBrangesESharp_ofReal_eq_conj]
    congr 1
    exact (Complex.conj_eq_iff_im.mpr (XiC_ofReal_im x)).symm
  rw [RCLike.inner_apply, h1, h2, suzukiFrakSFull_ofReal_eq t hXi,
    suzukiFrakSFull_ofReal_eq u hXi, hsharp, suzukiEnergyPt, suzukiEnergyPt]
  simp only [map_mul, Complex.conj_I, Complex.conj_conj]
  linear_combination (-((starRingEnd ℂ) (suzukiHalfInner ((x : ℝ) : ℂ))
    * suzukiPtZeroSum u ((x : ℝ) : ℂ) * suzukiHalfInner ((x : ℝ) : ℂ)
    * (starRingEnd ℂ) (suzukiPtZeroSum t ((x : ℝ) : ℂ)))) * Complex.I_sq

/-- **Suzuki Corollary 4.3, forward direction.**  Under the Riemann hypothesis the squared `L²`
norm of `𝔖_t` is `2π` times the screw source. -/
theorem norm_sq_suzukiFrakSFull_eq (hRH : RiemannHypothesis) (t : ℝ) :
    ‖(memLp_suzukiFrakSFull t).toLp (fun x : ℝ => suzukiFrakSFull t ((x : ℝ) : ℂ))‖ ^ 2
      = 2 * Real.pi * suzukiPsi t := by
  have hinner := inner_suzukiFrakSFull_eq_pi_mul_screwKernel hRH t t
  rw [suzukiScrewKernel_self] at hinner
  have h := @inner_self_eq_norm_sq ℂ _ _ _ _
    ((memLp_suzukiFrakSFull t).toLp (fun x : ℝ => suzukiFrakSFull t ((x : ℝ) : ℂ)))
  rw [hinner] at h
  have h2 : ((2 * Real.pi * suzukiPsi t : ℝ) : ℂ) = ((Real.pi : ℝ) : ℂ) *
      ((2 * suzukiPsi t : ℝ) : ℂ) := by push_cast; ring
  rw [← h2] at h
  exact_mod_cast h.symm


/-- **Suzuki Corollary 4.3**, in the form the corpus's Su22 Theorem 1.7 supports: RH holds if and
only if the squared `L²` norm of `𝔖_t` equals `2π Ψ(t)` on the whole source half-line.  (Suzuki
states the converse assuming the identity only on `[t₀, ∞)`; that refinement needs Su22 Theorem
11.1, which is not yet formalized here.) -/
theorem riemannHypothesis_iff_norm_sq_suzukiFrakSFull :
    RiemannHypothesis ↔ ∀ t : ℝ, 0 ≤ t →
      ‖(memLp_suzukiFrakSFull t).toLp (fun x : ℝ => suzukiFrakSFull t ((x : ℝ) : ℂ))‖ ^ 2
        = 2 * Real.pi * suzukiPsi t := by
  refine ⟨fun hRH t _ => norm_sq_suzukiFrakSFull_eq hRH t, fun h => ?_⟩
  refine riemannHypothesis_of_suzukiPsiPointwiseNonnegative fun t ht => ?_
  have h2 : (0 : ℝ) ≤ ‖(memLp_suzukiFrakSFull t).toLp
      (fun x : ℝ => suzukiFrakSFull t ((x : ℝ) : ℂ))‖ ^ 2 := sq_nonneg _
  rw [h t ht] at h2
  nlinarith [Real.pi_pos]

/-- **Regrouping a copy-indexed Cauchy series over the divisor support.**  A coefficient family
that depends on the copy only through its spectral point collapses to the support with a
multiplicity factor. -/
theorem hasSum_supportCauchy (hRH : RiemannHypothesis) (c : ℂ → ℂ) (x : ℝ)
    (hs : Summable fun q : XiZeroCopy =>
      c (xiSpectralPoint q) * ((x : ℂ) - xiSpectralPoint q)⁻¹) :
    HasSum (fun ρ : XiDivisorSupport =>
        ((xiSupportMult ρ : ℂ) * c ((xiRealSpectralPointSupport ρ : ℝ) : ℂ))
          * suzukiCauchyKernel ρ x)
      (∑' q : XiZeroCopy, c (xiSpectralPoint q) * ((x : ℂ) - xiSpectralPoint q)⁻¹) := by
  have h := hs.hasSum.sigma
    (g := fun ρ : XiDivisorSupport => ∑ i : Fin (xiSupportMult ρ),
      c (xiSpectralPoint (⟨ρ, i⟩ : XiZeroCopy))
        * ((x : ℂ) - xiSpectralPoint (⟨ρ, i⟩ : XiZeroCopy))⁻¹)
    (fun ρ => hasSum_fintype _)
  have hfun : (fun ρ : XiDivisorSupport => ∑ i : Fin (xiSupportMult ρ),
      c (xiSpectralPoint (⟨ρ, i⟩ : XiZeroCopy))
        * ((x : ℂ) - xiSpectralPoint (⟨ρ, i⟩ : XiZeroCopy))⁻¹)
      = fun ρ : XiDivisorSupport =>
        ((xiSupportMult ρ : ℂ) * c ((xiRealSpectralPointSupport ρ : ℝ) : ℂ))
          * suzukiCauchyKernel ρ x := by
    funext ρ
    rw [Finset.sum_congr rfl (fun i _ => by rw [xiSpectralPoint_copy_eq hRH]),
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, suzukiCauchyKernel]
    ring
  rw [hfun] at h
  exact h

end
end RHTower
