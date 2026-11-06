import GaloisForLFunctions.RHTower.Representation.EndpointExteriorProduct
import GaloisForLFunctions.RHTower.XiHorizontalSlicePolyaFrequencyCone
import GaloisForLFunctions.HTGeometry.GeneralPrimaryFactor
import GaloisForLFunctions.VerifiedHeightRungs.HadamardBudget.TheVerifiedHeightSixtySeven

/-!
# Finite-order positivity of the endpoint exterior coefficients

Positive translation preserves the divisor visibility cone. Conjugate endpoint factors
therefore satisfy the same quadratic Pólya frequency bound. Conjugation-stable finite
products and their locally uniform limit transfer this bound to the exact exterior series.
-/

noncomputable section
open Complex Filter Topology
open scoped BigOperators ComplexOrder Classical
namespace RHTower
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.VerifiedHeightRungs

/-- Adding a nonnegative real number preserves every closed sector in the right half-plane. -/
private lemma sector_add_real {c a : ℝ} {z : ℂ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (ha : 0 ≤ a) (hz : c * ‖z‖ ≤ z.re) :
    c * ‖(a : ℂ) + z‖ ≤ ((a : ℂ) + z).re := by
  calc
    c * ‖(a : ℂ) + z‖ ≤ c * (‖(a : ℂ)‖ + ‖z‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) hc0
    _ = c * a + c * ‖z‖ := by rw [Complex.norm_real, Real.norm_of_nonneg ha]; ring
    _ ≤ a + z.re := by nlinarith only [hz, mul_le_mul_of_nonneg_right hc1 ha]
    _ = _ := by simp

/-- A conjugate pair has precisely the quadratic coefficient sequence of its denominator. -/
private lemma endpoint_pair_factor (D : ℂ) (hD : D ≠ 0) :
    (fun x : ℂ => (1 + x ^ 2 / D) * (1 + x ^ 2 / (starRingEnd ℂ) D)) =
      fun x => ((1 / ‖D‖ ^ 2 : ℝ) : ℂ) *
        (x ^ 4 + ((2 * D.re : ℝ) : ℂ) * x ^ 2 + ((‖D‖ ^ 2 : ℝ) : ℂ)) := by
  have hc : (starRingEnd ℂ) D ≠ 0 := (map_ne_zero _).mpr hD
  have hs : D + (starRingEnd ℂ) D = ((2 * D.re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [two_mul]
  have hp : D * (starRingEnd ℂ) D = ((‖D‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.sq_norm]
  funext x
  calc
    _ = (x ^ 4 + (D + (starRingEnd ℂ) D) * x ^ 2 + D * (starRingEnd ℂ) D) / (D * (starRingEnd ℂ) D) := by
      field_simp [hD, hc]
      ring
    _ = _ := by rw [hs, hp]; push_cast; ring

private lemma pfTaylorAtZero_endpoint_pair {k : ℕ} (hk : 1 ≤ k) {D : ℂ} (hD : D ≠ 0)
    (hcone : Real.cos (Real.pi / ((k : ℝ) + 1)) * ‖D‖ ≤ D.re) :
    PFTaylorAtZero k (fun x : ℂ => (1 + x ^ 2 / D) * (1 + x ^ 2 / (starRingEnd ℂ) D)) := by
  let A := (‖D‖ + D.re) / 2
  let C := (‖D‖ - D.re) / 2
  have hbounds := abs_le.mp (Complex.abs_re_le_norm D)
  have hA : 0 ≤ A := by dsimp [A]; linarith only [hbounds.1]
  have hC : 0 ≤ C := by dsimp [C]; linarith only [hbounds.2]
  have hsum : A + C = ‖D‖ := by dsimp [A, C]; ring
  have hdiff : A - C = D.re := by dsimp [A, C]; ring
  have hAC : 0 < A + C := by rw [hsum]; exact norm_pos_iff.mpr hD
  have hh : Real.cos (Real.pi / ((k : ℝ) + 1)) * (A + C) ≤ A - C := by
    rw [hsum, hdiff]
    exact hcone
  rw [endpoint_pair_factor D hD]
  simpa only [hsum, hdiff] using
    pfTaylorAtZero_quartic_of_cone hk (C₀ := 1 / ‖D‖ ^ 2) (by positivity) hA hC hAC hh

/-- Denominator of a normalized endpoint color. -/
private def endpointFactorDenominator (q : XiZeroCopy) : ℂ :=
  (xiEndpointColorMass : ℂ) * (1 / 4 + xiSpectralPoint q ^ 2)

private lemma endpointFactorDenominator_ne_zero (q : XiZeroCopy) :
    endpointFactorDenominator q ≠ 0 := by
  apply mul_ne_zero (Complex.ofReal_ne_zero.mpr xiEndpointColorMass_pos.ne')
  intro h
  have hp := xiStripEdgeWeight_re_pos q
  rw [xiStripEdgeWeight_eq_spectral, h, inv_zero, Complex.zero_re] at hp
  exact lt_irrefl _ hp

private lemma endpointFactorDenominator_inv (q : XiZeroCopy) :
    (endpointFactorDenominator q)⁻¹ = xiStripEdgeWeight q / (xiEndpointColorMass : ℂ) := by
  simp only [endpointFactorDenominator, mul_inv_rev, xiStripEdgeWeight_eq_spectral,
    div_eq_mul_inv]

private lemma endpointFactorDenominator_conj (q : XiZeroCopy) :
    endpointFactorDenominator (xiZeroCopyConjEquiv q) = (starRingEnd ℂ) (endpointFactorDenominator q) := by
  have h4 : (starRingEnd ℂ) (4 : ℂ) = 4 := map_natCast (starRingEnd ℂ) 4
  simp [endpointFactorDenominator, xiSpectralPoint_conjEquiv, h4]

private lemma coneCos_nonneg {k : ℕ} (hk : 1 ≤ k) :
    0 ≤ Real.cos (Real.pi / ((k : ℝ) + 1)) := by
  apply Real.cos_nonneg_of_mem_Icc
  have hkR : (2 : ℝ) ≤ (k : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ hk
  constructor
  · have hp : 0 ≤ Real.pi / ((k : ℝ) + 1) := by positivity
    linarith only [hp, Real.pi_pos]
  · rw [div_le_div_iff₀ (by linarith only [hkR]) (by norm_num)]
    exact mul_le_mul_of_nonneg_left hkR Real.pi_pos.le

private lemma endpointFactorDenominator_cone {k : ℕ} (hk : 1 ≤ k)
    (hcone : ∀ q : XiZeroCopy, Real.cos (Real.pi / ((k : ℝ) + 1)) *
      (((q.1 : ℂ).im) ^ 2 + ((q.1 : ℂ).re - 1 / 2) ^ 2) ≤
        ((q.1 : ℂ).im) ^ 2 - ((q.1 : ℂ).re - 1 / 2) ^ 2) (q : XiZeroCopy) :
    Real.cos (Real.pi / ((k : ℝ) + 1)) * ‖endpointFactorDenominator q‖ ≤
      (endpointFactorDenominator q).re := by
  let c := Real.cos (Real.pi / ((k : ℝ) + 1))
  have hc1 : c ≤ 1 := Real.cos_le_one _
  have hc0 : 0 ≤ c := coneCos_nonneg hk
  have hs : ‖xiSpectralPoint q ^ 2‖ =
      ((q.1 : ℂ).im) ^ 2 + ((q.1 : ℂ).re - 1 / 2) ^ 2 := by
    rw [norm_pow, Complex.sq_norm, Complex.normSq_apply,
      re_xiSpectralPoint, im_xiSpectralPoint]
    ring
  have hr : (xiSpectralPoint q ^ 2).re =
      ((q.1 : ℂ).im) ^ 2 - ((q.1 : ℂ).re - 1 / 2) ^ 2 := by
    rw [pow_two, Complex.mul_re, re_xiSpectralPoint, im_xiSpectralPoint]
    ring
  have hb : c * ‖xiSpectralPoint q ^ 2‖ ≤ (xiSpectralPoint q ^ 2).re := by
    rw [hs, hr]
    exact hcone q
  have hshift := sector_add_real (a := 1 / 4) hc0 hc1 (by positivity) hb
  simp only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] at hshift
  change c * ‖endpointFactorDenominator q‖ ≤ (endpointFactorDenominator q).re
  simp only [endpointFactorDenominator, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg xiEndpointColorMass_pos.le, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  calc
    c * (xiEndpointColorMass * ‖(1 / 4 : ℂ) + xiSpectralPoint q ^ 2‖) =
      xiEndpointColorMass * (c * ‖(1 / 4 : ℂ) + xiSpectralPoint q ^ 2‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hshift xiEndpointColorMass_pos.le

private lemma endpointExteriorProduct_locallyUniform :
    TendstoLocallyUniformlyOn
      (fun S : Finset XiZeroCopy => fun z : ℂ => ∏ q ∈ S,
        (1 + z / endpointFactorDenominator q)) xiEndpointExteriorSeries atTop Set.univ := by
  let w : XiZeroCopy → ℂ := fun q => -(endpointFactorDenominator q)⁻¹
  have hw : ∀ q, w q ≠ 0 := fun q => neg_ne_zero.mpr (inv_ne_zero (endpointFactorDenominator_ne_zero q))
  have hs : Summable (fun q => ‖w q‖ ^ (0 + 1)) := by
    simp only [w, zero_add, pow_one, norm_neg, endpointFactorDenominator_inv]
    exact (summable_xiStripEdgeWeight.div_const (xiEndpointColorMass : ℂ)).norm
  have h := _root_.HTGeometry.canonicalWeightProduct_hasProdLocallyUniformlyOn 0 w hw hs
  have he (q : XiZeroCopy) (z : ℂ) : _root_.HTGeometry.primaryFactor 0 (z * w q) =
      1 + z / endpointFactorDenominator q := by
    simp [_root_.HTGeometry.primaryFactor, _root_.HTGeometry.primaryExponent, w, div_eq_mul_inv]
  have hv (z : ℂ) : _root_.HTGeometry.canonicalWeightProduct 0 w z = xiEndpointExteriorSeries z := by
    apply (h.hasProd (Set.mem_univ z)).unique
    have hh := hasProd_xiEndpointExteriorSeries z
    simpa only [he, div_eq_mul_inv, endpointFactorDenominator_inv, mul_assoc] using hh
  change TendstoLocallyUniformlyOn
    (fun S : Finset XiZeroCopy => fun z => ∏ q ∈ S, _root_.HTGeometry.primaryFactor 0 (z * w q))
    (_root_.HTGeometry.canonicalWeightProduct 0 w) atTop Set.univ at h
  have hvfun : _root_.HTGeometry.canonicalWeightProduct 0 w = xiEndpointExteriorSeries := funext hv
  rw [hvfun] at h
  simpa only [he] using h

/-- A divisor visibility cone transfers to the exact endpoint exterior coefficients. -/
private theorem pfTaylorAtZero_endpoint_of_cone {k : ℕ} (hk : 1 ≤ k)
    (hcone : ∀ q : XiZeroCopy, Real.cos (Real.pi / ((k : ℝ) + 1)) *
      (((q.1 : ℂ).im) ^ 2 + ((q.1 : ℂ).re - 1 / 2) ^ 2) ≤
        ((q.1 : ℂ).im) ^ 2 - ((q.1 : ℂ).re - 1 / 2) ^ 2) :
    PFTaylorAtZero k (fun x : ℂ => xiEndpointExteriorSeries (x ^ 2)) := by
  let τ := xiZeroCopyConjEquiv
  let c : Finset XiZeroCopy → Finset XiZeroCopy := fun S => S ∪ S.image τ
  have hc : Tendsto c atTop atTop :=
    tendsto_atTop_mono (fun S => Finset.subset_union_left) tendsto_id
  have hcl (S : Finset XiZeroCopy) : ∀ q ∈ c S, τ q ∈ c S := by
    intro q hq
    simp only [c, Finset.mem_union, Finset.mem_image] at hq ⊢
    rcases hq with hq | ⟨a, ha, rfl⟩
    · exact Or.inr ⟨q, hq, rfl⟩
    · exact Or.inl (by simpa only [τ, xiZeroCopyConjEquiv_apply_apply] using ha)
  let f : XiZeroCopy → ℂ → ℂ := fun q x => 1 + x ^ 2 / endpointFactorDenominator q
  have hfix (q : XiZeroCopy) (hq : τ q = q) : PFTaylorAtZero k (f q) := by
    have hre : (endpointFactorDenominator q).im = 0 := by
      have hh := endpointFactorDenominator_conj q
      rw [show xiZeroCopyConjEquiv q = q from hq] at hh
      have hi := congrArg Complex.im hh
      simp only [Complex.conj_im] at hi
      linarith only [hi]
    have hreal : endpointFactorDenominator q = ((endpointFactorDenominator q).re : ℂ) := by
      apply Complex.ext <;> simp [hre]
    have hnonneg : 0 ≤ (endpointFactorDenominator q).re :=
      (mul_nonneg (coneCos_nonneg hk) (norm_nonneg _)).trans
        (endpointFactorDenominator_cone hk hcone q)
    have he : f q = fun x : ℂ => ((1 : ℝ) : ℂ) +
        (((endpointFactorDenominator q).re)⁻¹ : ℝ) * x ^ 2 + ((0 : ℝ) : ℂ) * x ^ 4 := by
      funext x
      simp only [f]
      rw [hreal]
      simp only [Complex.ofReal_re, Complex.ofReal_zero, Complex.ofReal_one,
        div_eq_mul_inv, ← Complex.ofReal_inv, zero_mul, add_zero]
      ring
    rw [he]
    exact pfTaylorAtZero_linear k zero_le_one (inv_nonneg.mpr hnonneg)
  have hpair (q : XiZeroCopy) (_ : τ q ≠ q) : PFTaylorAtZero k (f q * f (τ q)) := by
    have he : f q * f (τ q) = fun x : ℂ =>
        (1 + x ^ 2 / endpointFactorDenominator q) *
          (1 + x ^ 2 / (starRingEnd ℂ) (endpointFactorDenominator q)) := by
      funext x
      simp only [Pi.mul_apply, f, τ, endpointFactorDenominator_conj]
    rw [he]
    exact pfTaylorAtZero_endpoint_pair hk (endpointFactorDenominator_ne_zero q)
      (endpointFactorDenominator_cone hk hcone q)
  have hfin (S : Finset XiZeroCopy) : PFTaylorAtZero k (fun x => ∏ q ∈ c S, f q x) :=
    prod_of_involution_of_mul (by simpa using pfTaylorAtZero_const k zero_le_one)
      (fun _ _ hf hg => hf.mul hg) τ xiZeroCopyConjEquiv_apply_apply f hfix hpair (c S) (hcl S)
  have hcont : Continuous (fun x : ℂ => x ^ 2) := by fun_prop
  have hl := TendstoLocallyUniformlyOn.comp endpointExteriorProduct_locallyUniform
    (fun x : ℂ => x ^ 2) (Set.mapsTo_univ _ Set.univ) hcont.continuousOn
  have hlc := tendstoLocallyUniformlyOn_comp_index hl hc
  exact PFTaylorAtZero.of_tendstoLocallyUniformlyOn (l := (atTop : Filter (Finset XiZeroCopy))) hfin
    (nonnegTaylorAtZero_xiEndpointExteriorSeries.1.comp (by fun_prop)) hlc

private theorem evenTaylorRe_endpoint_square (n : ℕ) :
    evenTaylorRe (fun x : ℂ => xiEndpointExteriorSeries (x ^ 2)) n =
      (xiEndpointExteriorCoefficient n).re := by
  let f : ℂ → ℂ := fun x => xiEndpointExteriorSeries (x ^ 2)
  have hf : Differentiable ℂ f := nonnegTaylorAtZero_xiEndpointExteriorSeries.1.comp (by fun_prop)
  have heven : ∀ x, f (-x) = f x := fun x => by simp only [f, neg_sq]
  have hlift : evenSquareLift f = xiEndpointExteriorSeries := by
    funext y
    let z := Complex.sqrt y
    have hz : z ^ 2 = y := Complex.cpow_nat_inv_pow _ (by norm_num)
    rw [← hz, evenSquareLift_sq hf heven]
  have hd : iteratedDeriv n (evenSquareLift f) 0 = (n.factorial : ℂ) * evenSquareCoeff f n := by
    have h := (hasFPowerSeriesOnBall_evenSquareLift hf).factorial_smul (1 : ℂ) n
    rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, Finset.prod_const_one, one_smul,
      FormalMultilinearSeries.ofScalars_apply_eq, one_pow, smul_eq_mul, mul_one, nsmul_eq_mul] at h
    exact h.symm
  rw [hlift] at hd
  have hc := xiEndpointExteriorCoefficient_eq_deriv n
  rw [hd] at hc
  have hn : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have hcoef : xiEndpointExteriorCoefficient n = evenSquareCoeff f n := by
    rw [hc]
    field_simp [hn]
  rw [hcoef]
  simp only [evenTaylorRe, evenSquareCoeff, div_eq_mul_inv, mul_comm, f]

/-- Every endpoint exterior Toeplitz minor of order at most 200 is nonnegative. -/
theorem xiEndpointExteriorCoefficient_pfSeq_twoHundred :
    PFSeq 200 (fun n => (xiEndpointExteriorCoefficient n).re) := by
  have hcone (q : XiZeroCopy) : Real.cos (Real.pi / (((200 : ℕ) : ℝ) + 1)) *
      (((q.1 : ℂ).im) ^ 2 + ((q.1 : ℂ).re - 1 / 2) ^ 2) ≤
        ((q.1 : ℂ).im) ^ 2 - ((q.1 : ℂ).re - 1 / 2) ^ 2 := by
    by_cases hq : |(q.1 : ℂ).im| ≤ 67
    · rw [re_eq_half_of_rhVerifiedThrough HadamardBudget.rhVerifiedThrough_sixtySeven q hq]
      have hc := Real.cos_le_one (Real.pi / (((200 : ℕ) : ℝ) + 1))
      nlinarith only [hc, sq_nonneg ((q.1 : ℂ).im)]
    · exact cone_of_distance (Real.cos_le_one _)
        (xi_divisor_support_centered_re_sq_lt_quarter q.1) (by norm_num : (0 : ℝ) ≤ 67)
        (not_le.mp hq).le (half_le_sq_mul_one_sub_cos (by norm_num : (5 : ℝ) ≤ 67) (by norm_num))
  have h := (pfTaylorAtZero_endpoint_of_cone (by norm_num : 1 ≤ 200) hcone).2.2
  have he : evenTaylorRe (fun x : ℂ => xiEndpointExteriorSeries (x ^ 2)) =
      fun n => (xiEndpointExteriorCoefficient n).re := funext evenTaylorRe_endpoint_square
  rwa [he] at h

end RHTower
