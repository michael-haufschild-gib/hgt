import GaloisForLFunctions.ExceptionalLayerTheory.TheRestrictedPrimeConvolutionsDetectEveryRightZero
import GaloisForLFunctions.HeckeLFunctions.HeckeLFunctionsContinuePastTheLineReOne
import GaloisForLFunctions.RHTower.ChebyshevErrorExponentLaw
import GaloisForLFunctions.RHTower.DirichletSummatorySwap
import GaloisForLFunctions.RHTower.BurnolIntegrand
import GaloisForLFunctions.RHTower.Sieve.VaughanTypeIRestricted

/-!
# Paired cofactor bounds for ordinary prime counts

Subtract the count of all integers from the von Mangoldt count before
convolving with the finite Vaughan cofactor. The resulting summatory
function is a finite combination of ordinary Chebyshev errors. A power
bound continues its Dirichlet series across every zero to the right of
the exponent. Two cofactor widths suffice even for a non-isolated zero layer.
-/

noncomputable section

open Complex Finset ArithmeticFunction Filter Topology
open scoped LSeries.notation
open RHTower.Sieve hiding dirPoly
open RHTower.WeilFiniteType

namespace GaloisForLFunctions.ExceptionalLayerTheory

/-- Signed cofactor counts with the ordinary integer density removed. -/
def cofactorCountCoeff (V W : ℕ) : ArithmeticFunction ℝ :=
  (vonMangoldt - (zeta : ArithmeticFunction ℝ)) * truncAF (typeIIShort V) W

/-- The count through the integer `N`. -/
def cofactorCountError (V W N : ℕ) : ℝ :=
  ∑ n ∈ Icc 1 N, cofactorCountCoeff V W n

/-- Summing the density-subtracted von Mangoldt weight gives the ordinary prime error. -/
theorem sum_vonMangoldt_sub_zeta (N : ℕ) :
    (∑ n ∈ Icc 1 N, (vonMangoldt - (zeta : ArithmeticFunction ℝ)) n) =
      Chebyshev.psi N - N := by
  have hterm (n : ℕ) (hn : n ∈ Icc 1 N) :
      (vonMangoldt - (zeta : ArithmeticFunction ℝ)) n = vonMangoldt n - 1 := by
    change vonMangoldt n - (zeta : ArithmeticFunction ℝ) n = _
    rw [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply,
      if_neg (Nat.ne_of_gt (mem_Icc.mp hn).1)]
    simp
  rw [sum_congr rfl hterm, sum_sub_distrib]
  simp only [sum_const, nsmul_eq_mul, mul_one, Nat.card_Icc, Nat.add_sub_cancel]
  congr 1
  unfold Chebyshev.psi
  rw [Nat.floor_natCast]
  rfl

/-- Exact expression as signed counts of prime powers at the divided cutoffs. -/
theorem cofactorCountError_eq (V W N : ℕ) :
    cofactorCountError V W N = ∑ d ∈ Icc 1 (min N W), typeIIShort V d *
      (Chebyshev.psi (N / d : ℕ) - (N / d : ℕ)) := by
  rw [cofactorCountError, cofactorCountCoeff, mul_comm, RHTower.sum_Icc_mul_apply]
  simp_rw [sum_vonMangoldt_sub_zeta, truncAF_apply, ite_mul, zero_mul, ← sum_filter]
  congr 1
  ext d
  simp only [mem_filter, mem_Icc, le_min_iff]
  tauto

/-- Every exponent above the true zero abscissa bounds each fixed cofactor count. -/
theorem cofactorCountError_power_above_abscissa {b : ℝ} (hb : RHTower.zeroReSup < b) (V W : ℕ) :
    ∃ K : ℝ, ∀ N : ℕ, 1 ≤ N → |cofactorCountError V W N| ≤ K * (N : ℝ) ^ b := by
  obtain ⟨C, hC, hψ⟩ := RHTower.exists_abs_chebyshevPsi_sub_le_rpow hb
  have hb0 : 0 ≤ b := by linarith only [RHTower.half_le_zeroReSup, hb]
  refine ⟨(∑ d ∈ Icc 1 W, |typeIIShort V d|) * C, fun N _ => ?_⟩
  rw [cofactorCountError_eq, mul_assoc]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc
    _ ≤ ∑ d ∈ Icc 1 (min N W), |typeIIShort V d| * (C * (N : ℝ) ^ b) := by
      apply sum_le_sum
      intro d hd
      obtain ⟨hd1, hdmax⟩ := mem_Icc.mp hd
      have hq1 := (Nat.one_le_div_iff hd1).mpr (hdmax.trans (min_le_left _ _))
      have hp := hψ (N / d : ℕ) (by exact_mod_cast hq1)
      rw [abs_mul]
      refine mul_le_mul_of_nonneg_left (hp.trans ?_) (abs_nonneg _)
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _)
        (by exact_mod_cast Nat.div_le_self N d) hb0) hC
    _ ≤ _ := by
      rw [← sum_mul]
      exact mul_le_mul_of_nonneg_right
        (sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc_right (min_le_right N W))
          (fun d _ _ => abs_nonneg (typeIIShort V d))) (by positivity)

private def countSeries (V W : ℕ) (s : ℂ) : ℂ :=
  (-deriv riemannZeta s / riemannZeta s - riemannZeta s) * dirPoly W (typeIIShort V) s

private theorem countSeries_on_euler {s : ℂ} (hs : 1 < s.re) (V W : ℕ) :
    LSeriesSummable (fun n => (cofactorCountCoeff V W n : ℂ)) s ∧
      LSeries (fun n => (cofactorCountCoeff V W n : ℂ)) s = countSeries V W s := by
  let f := (vonMangoldt - (zeta : ArithmeticFunction ℝ))
  let g := truncAF (typeIIShort V) W
  have hf : (fun n => (f n : ℂ)) =
      (fun n => (vonMangoldt n : ℂ)) - fun n => (((zeta : ArithmeticFunction ℝ) n : ℝ) : ℂ) := by
    funext n
    exact Complex.ofReal_sub _ _
  have hg : SupportedIn W g := ⟨ArithmeticFunction.map_zero, fun _ h => truncAF_apply_of_gt h⟩
  have hconv : (fun n => (cofactorCountCoeff V W n : ℂ)) =
      ((fun n => (f n : ℂ)) ⍟ fun n => (g n : ℂ)) := by
    funext n
    rw [LSeries.convolution_def]
    exact coe_mul_apply _ _ _
  have hζeq : (fun n => (((zeta : ArithmeticFunction ℝ) n : ℝ) : ℂ)) =
      fun n => ((zeta n : ℕ) : ℂ) := by
    funext n
    by_cases hn : n = 0 <;> simp [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply, hn]
  have hζ := ArithmeticFunction.LSeriesSummable_zeta_iff.mpr hs
  have hΛ := ArithmeticFunction.LSeriesSummable_vonMangoldt hs
  have hgs := LSeriesSummable_of_supportedIn hg s
  rw [hconv, hf, hζeq]
  refine ⟨(hΛ.sub hζ).convolution hgs, ?_⟩
  rw [LSeries_convolution' (hΛ.sub hζ) hgs, LSeries_sub hΛ hζ,
    ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs, LSeries_eq_dirPoly hg]
  have hZ : LSeries (fun n => ((zeta n : ℕ) : ℂ)) s = riemannZeta s := by
    exact ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs
  rw [hZ, countSeries]
  congr 1
  unfold dirPoly
  exact sum_congr rfl fun n hn => by simp [g, truncAF_apply, (mem_Icc.mp hn).2]

/-- A bound on the finite arithmetic counts forces the short symbol to vanish
at every strip zero strictly to the right of the bound's exponent. -/
theorem shortCofactor_eq_zero_of_count_bound (V W : ℕ) {b K : ℝ} (hb : 0 ≤ b) (hb1 : b < 1)
    (hcount : ∀ N : ℕ, 1 ≤ N → |cofactorCountError V W N| ≤ K * (N : ℝ) ^ b)
    {ρ : ℂ} (hρ : b < ρ.re) (hz : riemannZeta ρ = 0) :
    dirPoly W (typeIIShort V) ρ = 0 := by
  let c := fun n => (cofactorCountCoeff V W n : ℂ)
  have hc0 : c 0 = 0 := by simp [c]
  have hK : 0 ≤ K := by simpa using (abs_nonneg _).trans (hcount 1 le_rfl)
  have hreal (x : ℝ) (hx : 1 ≤ x) : ‖∑ k ∈ Icc 1 ⌊x⌋₊, c k‖ ≤ K * x ^ b := by
    change ‖∑ k ∈ Icc 1 ⌊x⌋₊, (cofactorCountCoeff V W k : ℂ)‖ ≤ _
    rw [← Complex.ofReal_sum, Complex.norm_real, Real.norm_eq_abs]
    exact (hcount _ ((Nat.one_le_floor_iff x).mpr hx)).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _)
        (Nat.floor_le (zero_le_one.trans hx)) hb) hK)
  let D := {s : ℂ | b < s.re}
  let G := HeckeLFunctions.growthCont c b
  have hopen : IsOpen D := isOpen_lt continuous_const Complex.continuous_re
  have hG : DifferentiableOn ℂ G D := HeckeLFunctions.differentiableOn_growthCont hc0 hb hreal
  let F := countSeries V W - G
  have hmero : MeromorphicOn F D := by
    apply MeromorphicOn.sub _ (hG.analyticOnNhd hopen).meromorphicOn
    intro s _
    have hZ := RHTower.meromorphicAt_riemannZeta_everywhere s
    exact (((hZ.deriv.neg.div hZ).sub hZ).mul
      ((differentiable_dirPoly W (typeIIShort V)).analyticAt s).meromorphicAt)
  have h2 : meromorphicOrderAt F (2 : ℂ) = ⊤ := by
    apply meromorphicOrderAt_eq_top_iff.mpr
    have hnb : {s : ℂ | 1 < s.re} ∈ 𝓝 (2 : ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    filter_upwards [nhdsWithin_le_nhds hnb] with s hs
    obtain ⟨habs, he⟩ := countSeries_on_euler hs V W
    exact sub_eq_zero.mpr (he.symm.trans
      (HeckeLFunctions.growthCont_eq_LSeries hc0 hb hreal (hb1.trans hs) habs).symm)
  have htop : meromorphicOrderAt F ρ = ⊤ := by
    by_contra h
    exact (hmero.meromorphicOrderAt_ne_top_of_isPreconnected
      (convex_halfSpace_re_gt b).isPreconnected hρ
      (show b < (2 : ℂ).re by simpa using hb1.trans (by norm_num : (1 : ℝ) < 2)) h) h2
  have hagree : countSeries V W =ᶠ[𝓝[≠] ρ] G := by
    filter_upwards [meromorphicOrderAt_eq_top_iff.mp htop] with s hs
    exact sub_eq_zero.mp hs
  have hGlim := (hG.differentiableAt (hopen.mem_nhds hρ)).continuousAt.tendsto.mono_left
    (nhdsWithin_le_nhds (s := ({ρ}ᶜ : Set ℂ)))
  have hlin : Tendsto (fun s : ℂ => s - ρ) (𝓝[≠] ρ) (𝓝 0) :=
    ((continuous_id.sub continuous_const).tendsto' ρ 0 (sub_self ρ)).mono_left (nhdsWithin_le_nhds (s := ({ρ}ᶜ : Set ℂ)))
  have hzero : Tendsto (fun s => (s - ρ) * countSeries V W s) (𝓝[≠] ρ) (𝓝 0) := by
    have hprod : (fun s => (s - ρ) * countSeries V W s) =ᶠ[𝓝[≠] ρ] fun s => (s - ρ) * G s :=
      hagree.mono fun s hs => congrArg ((s - ρ) * ·) hs
    apply (tendsto_congr' hprod).mpr
    simpa only [zero_mul] using hlin.mul hGlim
  obtain ⟨m, hm, hmres⟩ := RHTower.neg_logDeriv_zeta_zero_residue hz
  have hρne := RHTower.riemannZeta_zero_ne_one hz
  have hZlim := (differentiableAt_riemannZeta hρne).continuousAt.tendsto.mono_left
    (nhdsWithin_le_nhds (s := ({ρ}ᶜ : Set ℂ)))
  have hDlim := (differentiable_dirPoly W (typeIIShort V) ρ).continuousAt.tendsto.mono_left
    (nhdsWithin_le_nhds (s := ({ρ}ᶜ : Set ℂ)))
  have hres : Tendsto (fun s => (s - ρ) * countSeries V W s) (𝓝[≠] ρ)
      (𝓝 (-(m : ℂ) * dirPoly W (typeIIShort V) ρ)) := by
    convert (hmres.sub (hlin.mul hZlim)).mul hDlim using 1
    · funext s
      unfold countSeries
      ring
    · rw [zero_mul, sub_zero]
  exact (mul_eq_zero.mp (tendsto_nhds_unique hres hzero)).resolve_left
    (neg_ne_zero.mpr (Nat.cast_ne_zero.mpr (by omega : m ≠ 0)))

/-- RH is equivalent to power bounds for pairs of signed ordinary prime counts.
The cutoffs can depend on the exponent and the bound on the cutoff. -/
theorem riemannHypothesis_iff_paired_cofactor_count_bounds :
    RiemannHypothesis ↔ ∀ b : ℝ, 1 / 2 < b → b < 1 →
      ∃ᶠ V : ℕ in atTop, ∀ W ∈ ({V ^ 2, 2 * V ^ 2} : Finset ℕ), ∃ K : ℝ,
        ∀ N : ℕ, 1 ≤ N → |cofactorCountError V W N| ≤ K * (N : ℝ) ^ b := by
  constructor
  · intro hRH b hb _
    have hΘ := RHTower.zeroReSup_le_of_forall_re_le fun q =>
      (RHTower.xiZeroCopy_re_eq_half_of_riemannHypothesis hRH q).le
    exact (Eventually.of_forall fun V W _ =>
      cofactorCountError_power_above_abscissa (hΘ.trans_lt hb) V W).frequently
  · intro hcounts
    apply RHTower.riemannHypothesis_iff_riemannZeta_ne_zero_of_mem_upper_strip.mpr
    intro ρ hlo hhi hz
    obtain ⟨b, hb, hbρ⟩ := exists_between hlo
    obtain ⟨V, hV, hdetect⟩ := ((hcounts b hb (hbρ.trans hhi)).and_eventually
      (eventually_dyadic_shortCofactor_detects_zero hlo hhi hz)).exists
    have hkill (W : ℕ) (hW : W ∈ ({V ^ 2, 2 * V ^ 2} : Finset ℕ)) :
        dirPoly W (typeIIShort V) ρ = 0 := by
      obtain ⟨K, hK⟩ := hV W hW
      exact shortCofactor_eq_zero_of_count_bound V W (by linarith only [hb])
        (hbρ.trans hhi) hK hbρ hz
    rcases hdetect _ le_rfl with h | h
    · exact h (hkill _ (by simp))
    · exact h (hkill _ (by simp))

/-- Centred counts of the ordinary long-prime convolution with its finite head deleted. -/
def restrictedCofactorCount (U V W N : ℕ) : ℝ :=
  ∑ n ∈ Icc 1 N, ((typeIILong U - (zeta : ArithmeticFunction ℝ)) *
    truncAF (typeIIShort V) W) n

/-- Deleting the prime head changes the count by the prefix of a convolution
supported through `U * W`. This formula includes horizons inside the head. -/
theorem cofactorCount_sub_restricted (U V W N : ℕ) :
    cofactorCountError V W N - restrictedCofactorCount U V W N =
      ∑ n ∈ Icc 1 (min N (U * W)), (truncAF vonMangoldt U * truncAF (typeIIShort V) W) n := by
  rw [cofactorCountError, restrictedCofactorCount, ← sum_sub_distrib]
  let h := truncAF (vonMangoldt : ArithmeticFunction ℝ) U
  let g := truncAF (typeIIShort V) W
  have hdiff : cofactorCountCoeff V W - (typeIILong U - (zeta : ArithmeticFunction ℝ)) * g =
      h * g := by
    unfold cofactorCountCoeff typeIILong
    change (vonMangoldt - (zeta : ArithmeticFunction ℝ)) * g - (vonMangoldt - h - zeta) * g = h*g
    rw [← sub_mul]
    congr 1
    abel
  have he (n : ℕ) := DFunLike.congr_fun hdiff n
  change (∑ n ∈ Icc 1 N, (cofactorCountCoeff V W n -
    ((typeIILong U - (zeta : ArithmeticFunction ℝ)) * g) n)) = _
  simp_rw [show ∀ n, cofactorCountCoeff V W n - ((typeIILong U - (zeta : ArithmeticFunction ℝ)) *
    g) n = (h * g) n from he]
  apply (sum_subset (Icc_subset_Icc_right (min_le_left N (U*W))) _).symm
  intro n hn hnot
  obtain ⟨hn1, hnN⟩ := mem_Icc.mp hn
  exact truncAF_conv_apply_of_gt (show U * W < n by
    by_contra! h
    exact hnot (mem_Icc.mpr ⟨hn1, le_min hnN h⟩))

private theorem transfer_count_bound {a f : ℕ → ℝ} {b M : ℝ} (hb : 0 ≤ b)
    (hd : ∀ N, |a N - f N| ≤ M)
    (hf : ∃ K : ℝ, ∀ N : ℕ, 1 ≤ N → |f N| ≤ K * (N : ℝ) ^ b) :
    ∃ K : ℝ, ∀ N : ℕ, 1 ≤ N → |a N| ≤ K * (N : ℝ) ^ b := by
  obtain ⟨K, hK⟩ := hf
  have hM : 0 ≤ M := (abs_nonneg _).trans (hd 1)
  refine ⟨M + K, fun N hN => ?_⟩
  have hone : 1 ≤ (N : ℝ) ^ b := Real.one_le_rpow (by exact_mod_cast hN) hb
  calc
    |a N| = |(a N - f N) + f N| := by rw [sub_add_cancel]
    _ ≤ |a N - f N| + |f N| := abs_add_le _ _
    _ ≤ M + K * (N : ℝ) ^ b := add_le_add (hd N) (hK N hN)
    _ ≤ (M + K) * (N : ℝ) ^ b := by
      rw [add_mul]
      exact add_le_add (le_mul_of_one_le_right hM hone) le_rfl

/-- Each fixed power bound survives deletion of any finite prime head. -/
theorem restrictedCofactorCount_power_iff (U V W : ℕ) {b : ℝ} (hb : 0 ≤ b) :
    (∃ K : ℝ, ∀ N : ℕ, 1 ≤ N → |restrictedCofactorCount U V W N| ≤ K * (N : ℝ) ^ b) ↔
      ∃ K : ℝ, ∀ N : ℕ, 1 ≤ N → |cofactorCountError V W N| ≤ K * (N : ℝ) ^ b := by
  let h := truncAF (vonMangoldt : ArithmeticFunction ℝ) U * truncAF (typeIIShort V) W
  have hd (N : ℕ) : |cofactorCountError V W N - restrictedCofactorCount U V W N| ≤
      ∑ n ∈ Icc 1 (U * W), |h n| := by
    rw [cofactorCount_sub_restricted]
    exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum_of_subset_of_nonneg
      (Icc_subset_Icc_right (min_le_right N (U * W))) (fun n _ _ => abs_nonneg (h n)))
  exact ⟨transfer_count_bound hb hd, transfer_count_bound hb (fun N => (abs_sub_comm _ _).le.trans (hd N))⟩

/-- The paired-count criterion uses the actual long-prime Vaughan coefficients,
with an arbitrary finite choice of deleted prime head at each Möbius cutoff. -/
theorem riemannHypothesis_iff_paired_restricted_count_bounds (U : ℕ → ℕ) :
    RiemannHypothesis ↔ ∀ b : ℝ, 1 / 2 < b → b < 1 →
      ∃ᶠ V : ℕ in atTop, ∀ W ∈ ({V ^ 2, 2 * V ^ 2} : Finset ℕ), ∃ K : ℝ,
        ∀ N : ℕ, 1 ≤ N → |restrictedCofactorCount (U V) V W N| ≤ K * (N : ℝ) ^ b := by
  rw [riemannHypothesis_iff_paired_cofactor_count_bounds]
  constructor <;> intro h b hb hb1
  · exact (h b hb hb1).mono fun V hV W hW =>
      (restrictedCofactorCount_power_iff (U V) V W (by linarith only [hb])).mpr (hV W hW)
  · exact (h b hb hb1).mono fun V hV W hW =>
      (restrictedCofactorCount_power_iff (U V) V W (by linarith only [hb])).mp (hV W hW)

#print axioms norm_dirPoly_zeta_convolution_sub_le
#print axioms norm_dyadic_shortCofactor_sub_le
#print axioms lseries_restrictedPrimeConvolution
#print axioms restrictedPrimeSeries_residue_at_zero
#print axioms riemannHypothesis_iff_cofinal_restrictedPrimeResidues
#print axioms cofactorCountError_eq
#print axioms riemannHypothesis_iff_paired_cofactor_count_bounds
#print axioms riemannHypothesis_iff_paired_restricted_count_bounds

end GaloisForLFunctions.ExceptionalLayerTheory
