import GaloisForLFunctions.RHTower.FiniteOfflineCauchyL2
import GaloisForLFunctions.HTGeometry.BarnesMellinRepresentation

/-!
# The unweighted anti-causal Cauchy trace is the unique phase-noncancelling Hankel energy

For a finite right-half divisor packet the anti-causal boundary profile is

`ℓ(t) = 2 ∑ⱼ mⱼ exp(-zⱼ t)`,   `zⱼ = aⱼ + i γⱼ`,  `aⱼ > 0`,

and its power-weighted boundary energies are

`E_α(ℓ) = ∫_0^∞ t^α ‖ℓ(t)‖² dt = 4 Γ(α+1) ∑_{j,k} mⱼ m_k Re[(conj zⱼ + z_k)^{-(α+1)}]`.

The cross entry has the sign of `cos((α+1)θ)`, where `θ = arg(conj zⱼ + z_k) ∈ (-π/2, π/2)`.  At
`α = 0` this is positive for every pair — the strictly entrywise-positive Cauchy kernel of the
four-unit Ward threshold — and for every `α > 0` there is a divisor packet whose cross entry is
negative.  So the unweighted `L²` trace is the unique power weight that never cancels phase.

The Hilbert–Schmidt norm of the Hankel operator with kernel `ℓ(x+y)` is the *first-moment* energy
`E₁` (`lintegral_hankelSquare_eq_firstMoment`), so it sits at the wrong weight.

Everything reuses the corpus off-line Cauchy stack
(`RHTower.finiteOfflineProfile`, `RHTower.finiteOfflinePairIntegrand`) and the corpus complex-rate
Euler integral `GaloisForLFunctions.HTGeometry.integral_cpow_mul_exp_neg_mul_Ioi`.
-/

namespace RHTower

noncomputable section

open MeasureTheory Set Complex
open scoped BigOperators ENNReal NNReal

/-! ## The weighted Gram expansion -/

/-- The Cauchy rate `conj zⱼ + z_k = (aⱼ + a_k) - i(γⱼ - γ_k)` of a cross mode. -/
def offlineCrossRate {n : ℕ} (a gamma : Fin n → ℝ) (j k : Fin n) : ℂ :=
  ((a j + a k : ℝ) : ℂ) - Complex.I * ((gamma j - gamma k : ℝ) : ℂ)

@[simp]
theorem offlineCrossRate_re {n : ℕ} (a gamma : Fin n → ℝ) (j k : Fin n) :
    (offlineCrossRate a gamma j k).re = a j + a k := by
  simp [offlineCrossRate]

/-- The `t^α`-weighted cross-mode integrand. -/
def weightedOfflinePairIntegrand (alpha : ℝ) {n : ℕ} (a gamma : Fin n → ℝ) (m : Fin n → ℕ)
    (j k : Fin n) (t : ℝ) : ℂ :=
  ((t : ℂ) ^ (alpha : ℂ)) * finiteOfflinePairIntegrand a gamma m j k t

theorem weightedOfflinePairIntegrand_eq (alpha : ℝ) {n : ℕ} (a gamma : Fin n → ℝ) (m : Fin n → ℕ)
    (j k : Fin n) (t : ℝ) :
    weightedOfflinePairIntegrand alpha a gamma m j k t =
      (4 * (m j : ℂ) * (m k : ℂ)) *
        ((t : ℂ) ^ (((alpha : ℂ) + 1) - 1) *
          Complex.exp (-(offlineCrossRate a gamma j k * (t : ℂ)))) := by
  unfold weightedOfflinePairIntegrand finiteOfflinePairIntegrand offlineCrossRate
  have h1 : ((alpha : ℂ) + 1 - 1) = (alpha : ℂ) := by ring
  have h2 : -((((a j + a k : ℝ) : ℂ) - Complex.I * ((gamma j - gamma k : ℝ) : ℂ)) * (t : ℂ))
      = (-((a j + a k : ℝ) : ℂ) + Complex.I * ((gamma j - gamma k : ℝ) : ℂ)) * (t : ℂ) := by
    ring
  rw [h1, h2]
  ring

theorem weightedOfflinePairIntegrand_integrableOn {alpha : ℝ} (halpha : -1 < alpha) {n : ℕ}
    {a gamma : Fin n → ℝ} (m : Fin n → ℕ) (ha : ∀ j, 0 < a j) (j k : Fin n) :
    IntegrableOn (weightedOfflinePairIntegrand alpha a gamma m j k) (Ioi 0) := by
  have hs : 0 < ((alpha : ℂ) + 1).re := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.one_re]
    linarith
  have hw : 0 < (offlineCrossRate a gamma j k).re := by
    rw [offlineCrossRate_re]
    linarith [ha j, ha k]
  have hbase := GaloisForLFunctions.HTGeometry.integrableOn_cpow_mul_exp_neg_mul_Ioi hs hw
  have : IntegrableOn (fun t : ℝ => (4 * (m j : ℂ) * (m k : ℂ)) *
      ((t : ℂ) ^ (((alpha : ℂ) + 1) - 1) *
        Complex.exp (-(offlineCrossRate a gamma j k * (t : ℂ))))) (Ioi 0) :=
    hbase.const_mul _
  refine this.congr_fun ?_ measurableSet_Ioi
  intro t _
  exact (weightedOfflinePairIntegrand_eq alpha a gamma m j k t).symm

theorem integral_weightedOfflinePairIntegrand {alpha : ℝ} (halpha : -1 < alpha) {n : ℕ}
    {a gamma : Fin n → ℝ} (m : Fin n → ℕ) (ha : ∀ j, 0 < a j) (j k : Fin n) :
    ∫ t in Ioi (0 : ℝ), weightedOfflinePairIntegrand alpha a gamma m j k t =
      (4 * (m j : ℂ) * (m k : ℂ)) *
        (Complex.Gamma ((alpha : ℂ) + 1) *
          (offlineCrossRate a gamma j k) ^ (-((alpha : ℂ) + 1))) := by
  have hs : 0 < ((alpha : ℂ) + 1).re := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.one_re]
    linarith
  have hw : 0 < (offlineCrossRate a gamma j k).re := by
    rw [offlineCrossRate_re]
    linarith [ha j, ha k]
  have hfun : (fun t : ℝ => weightedOfflinePairIntegrand alpha a gamma m j k t) =
      fun t : ℝ => (4 * (m j : ℂ) * (m k : ℂ)) *
        ((t : ℂ) ^ (((alpha : ℂ) + 1) - 1) *
          Complex.exp (-(offlineCrossRate a gamma j k * (t : ℂ)))) := by
    funext t
    exact weightedOfflinePairIntegrand_eq alpha a gamma m j k t
  rw [hfun, integral_const_mul,
    GaloisForLFunctions.HTGeometry.integral_cpow_mul_exp_neg_mul_Ioi hs hw]

/-- The `t^α`-weighted anti-causal boundary energy of a finite right-half divisor packet. -/
def weightedOfflineEnergy (alpha : ℝ) {n : ℕ} (a gamma : Fin n → ℝ) (m : Fin n → ℕ) : ℝ :=
  ∫ t in Ioi (0 : ℝ), t ^ alpha * ‖finiteOfflineProfile a gamma m t‖ ^ 2

theorem weightedOfflineEnergy_pointwise (alpha : ℝ) {n : ℕ} (a gamma : Fin n → ℝ) (m : Fin n → ℕ)
    {t : ℝ} (ht : 0 < t) :
    t ^ alpha * ‖finiteOfflineProfile a gamma m t‖ ^ 2 =
      (∑ j, ∑ k, weightedOfflinePairIntegrand alpha a gamma m j k t).re := by
  have hnorm : ‖finiteOfflineProfile a gamma m t‖ ^ 2 =
      ((starRingEnd ℂ) (finiteOfflineProfile a gamma m t) *
        finiteOfflineProfile a gamma m t).re := by
    rw [← Complex.normSq_eq_norm_sq]
    exact_mod_cast congrArg Complex.re
      (Complex.normSq_eq_conj_mul_self (z := finiteOfflineProfile a gamma m t))
  have hcast : (((t ^ alpha : ℝ)) : ℂ) = (t : ℂ) ^ (alpha : ℂ) :=
    Complex.ofReal_cpow ht.le alpha
  have hsum : ∑ j, ∑ k, weightedOfflinePairIntegrand alpha a gamma m j k t =
      ((t : ℂ) ^ (alpha : ℂ)) *
        ((starRingEnd ℂ) (finiteOfflineProfile a gamma m t) *
          finiteOfflineProfile a gamma m t) := by
    rw [finiteOfflineProfile_gramExpansion, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => rfl
  rw [hsum, hnorm, ← hcast]
  simp [Complex.mul_re]

theorem weightedOfflineEnergy_integrableOn {alpha : ℝ} (halpha : -1 < alpha) {n : ℕ}
    {a gamma : Fin n → ℝ} (m : Fin n → ℕ) (ha : ∀ j, 0 < a j) :
    IntegrableOn
      (fun t => ∑ j, ∑ k, weightedOfflinePairIntegrand alpha a gamma m j k t) (Ioi 0) := by
  apply integrable_finsetSum
  intro j _
  apply integrable_finsetSum
  intro k _
  exact weightedOfflinePairIntegrand_integrableOn halpha m ha j k

/-- **The weighted Gram expansion.**  Every power-weighted boundary energy of the anti-causal
profile is `4Γ(α+1)` times the Gram sum of the real parts of the inverse `(α+1)`-powers of the
Cauchy rates. -/
theorem weightedOfflineEnergy_eq {alpha : ℝ} (halpha : -1 < alpha) {n : ℕ}
    {a gamma : Fin n → ℝ} (m : Fin n → ℕ) (ha : ∀ j, 0 < a j) :
    weightedOfflineEnergy alpha a gamma m =
      4 * Real.Gamma (alpha + 1) *
        ∑ j, ∑ k, (m j : ℝ) * (m k : ℝ) *
          ((offlineCrossRate a gamma j k) ^ (-((alpha : ℂ) + 1))).re := by
  have hcongr : ∀ t ∈ Ioi (0 : ℝ),
      t ^ alpha * ‖finiteOfflineProfile a gamma m t‖ ^ 2 =
        (∑ j, ∑ k, weightedOfflinePairIntegrand alpha a gamma m j k t).re := by
    intro t ht
    exact weightedOfflineEnergy_pointwise alpha a gamma m ht
  unfold weightedOfflineEnergy
  rw [setIntegral_congr_fun measurableSet_Ioi hcongr]
  have hre : (∫ t in Ioi (0 : ℝ),
        (∑ j, ∑ k, weightedOfflinePairIntegrand alpha a gamma m j k t).re) =
      (∫ t in Ioi (0 : ℝ), ∑ j, ∑ k, weightedOfflinePairIntegrand alpha a gamma m j k t).re :=
    integral_re (μ := volume.restrict (Ioi 0)) (weightedOfflineEnergy_integrableOn halpha m ha)
  rw [hre]
  rw [integral_finsetSum Finset.univ
    (fun j _ => integrable_finsetSum _
      (fun k _ => weightedOfflinePairIntegrand_integrableOn halpha m ha j k))]
  rw [Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_finsetSum Finset.univ
    (fun k _ => weightedOfflinePairIntegrand_integrableOn halpha m ha j k)]
  rw [Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_weightedOfflinePairIntegrand halpha m ha j k]
  have hgamma : Complex.Gamma ((alpha : ℂ) + 1) = ((Real.Gamma (alpha + 1) : ℝ) : ℂ) := by
    rw [show ((alpha : ℂ) + 1) = (((alpha + 1 : ℝ)) : ℂ) by push_cast; ring, Complex.Gamma_ofReal]
  rw [hgamma]
  have hcoef : (4 * (m j : ℂ) * (m k : ℂ)) * (((Real.Gamma (alpha + 1) : ℝ) : ℂ) *
      (offlineCrossRate a gamma j k) ^ (-((alpha : ℂ) + 1)))
      = (((4 * Real.Gamma (alpha + 1) * ((m j : ℝ) * (m k : ℝ)) : ℝ)) : ℂ) *
        (offlineCrossRate a gamma j k) ^ (-((alpha : ℂ) + 1)) := by
    push_cast
    ring
  rw [hcoef, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-! ## The sign of a cross entry -/

/-- The real part of an inverse complex power in polar terms. -/
theorem re_cpow_neg_ofReal {w : ℂ} (hw : w ≠ 0) (c : ℝ) :
    (w ^ (-(c : ℂ))).re = ‖w‖ ^ (-c) * Real.cos (c * Complex.arg w) := by
  have hnorm : (0 : ℝ) < ‖w‖ := norm_pos_iff.2 hw
  rw [Complex.cpow_def_of_ne_zero hw, Complex.exp_re]
  have hre : (Complex.log w * (-(c : ℂ))).re = Real.log ‖w‖ * (-c) := by
    rw [Complex.mul_re]
    simp [Complex.log_re]
  have him : (Complex.log w * (-(c : ℂ))).im = Complex.arg w * (-c) := by
    rw [Complex.mul_im]
    simp [Complex.log_im]
  rw [hre, him, Real.rpow_def_of_pos hnorm,
    show Complex.arg w * (-c) = -(c * Complex.arg w) by ring, Real.cos_neg]

/-- **Entrywise positivity at the unweighted trace.**  Every cross entry of the `α = 0` Gram sum is
strictly positive. -/
theorem re_offlineCrossRate_cpow_neg_one_pos {n : ℕ} {a gamma : Fin n → ℝ}
    (ha : ∀ i, 0 < a i) (j k : Fin n) :
    0 < ((offlineCrossRate a gamma j k) ^ (-(((0 : ℝ) : ℂ) + 1))).re := by
  have hre : 0 < (offlineCrossRate a gamma j k).re := by
    rw [offlineCrossRate_re]
    linarith [ha j, ha k]
  have hne : offlineCrossRate a gamma j k ≠ 0 := by
    intro h
    rw [h] at hre
    simp at hre
  have hexp : (-(((0 : ℝ) : ℂ) + 1)) = (-1 : ℂ) := by push_cast; ring
  rw [hexp, Complex.cpow_neg_one, Complex.inv_re]
  have hns : 0 < Complex.normSq (offlineCrossRate a gamma j k) :=
    Complex.normSq_pos.2 hne
  positivity

/-- **Every positive power weight cancels phase.**  For every `α > 0` there is a two-mode
right-half divisor packet whose `α`-weighted Gram matrix has a strictly negative cross entry. -/
theorem exists_offlinePacket_re_cpow_neg_lt_zero {alpha : ℝ} (halpha : 0 < alpha) :
    ∃ (a gamma : Fin 2 → ℝ) (j k : Fin 2), (∀ i, 0 < a i) ∧
      ((offlineCrossRate a gamma j k) ^ (-((alpha : ℂ) + 1))).re < 0 := by
  set c : ℝ := alpha + 1 with hc
  have hc1 : 1 < c := by rw [hc]; linarith
  have hcpos : 0 < c := by linarith
  have hpi : 0 < Real.pi := Real.pi_pos
  set L : ℝ := Real.pi / (2 * c) with hL
  set R : ℝ := min (Real.pi / 2) (3 * Real.pi / (2 * c)) with hR
  have hcL : c * L = Real.pi / 2 := by
    rw [hL, mul_div_assoc', div_eq_div_iff (by positivity) (by positivity)]
    ring
  have hcR3 : c * (3 * Real.pi / (2 * c)) = 3 * Real.pi / 2 := by
    rw [mul_div_assoc', div_eq_div_iff (by positivity) (by positivity)]
    ring
  have hLpos : 0 < L := by rw [hL]; positivity
  have hLhalf : L < Real.pi / 2 := by
    have : c * L = Real.pi / 2 := hcL
    nlinarith
  have hL3 : L < 3 * Real.pi / (2 * c) := by
    rw [hL, div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hLR : L < R := by
    rw [hR]
    exact lt_min hLhalf hL3
  set theta : ℝ := (L + R) / 2 with hth
  have hLt : L < theta := by rw [hth]; linarith
  have htR : theta < R := by rw [hth]; linarith
  have hthpos : 0 < theta := lt_trans hLpos hLt
  have hthlt : theta < Real.pi / 2 := lt_of_lt_of_le htR (by rw [hR]; exact min_le_left _ _)
  have hcth1 : Real.pi / 2 < c * theta := by
    have := mul_lt_mul_of_pos_left hLt hcpos
    rw [hcL] at this
    exact this
  have hcth2 : c * theta < Real.pi + Real.pi / 2 := by
    have hle : R ≤ 3 * Real.pi / (2 * c) := by rw [hR]; exact min_le_right _ _
    have h1 : c * theta < c * R := mul_lt_mul_of_pos_left htR hcpos
    have h2 : c * R ≤ c * (3 * Real.pi / (2 * c)) := mul_le_mul_of_nonneg_left hle hcpos.le
    rw [hcR3] at h2
    linarith
  have hcosneg : Real.cos (c * theta) < 0 :=
    Real.cos_neg_of_pi_div_two_lt_of_lt hcth1 hcth2
  have hcospos : 0 < Real.cos theta :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, hthlt⟩
  refine ⟨fun _ => Real.cos theta / 2, ![0, Real.sin theta], 0, 1,
    fun _ => div_pos hcospos (by norm_num), ?_⟩
  have hrate : offlineCrossRate (fun _ : Fin 2 => Real.cos theta / 2) ![0, Real.sin theta] 0 1
      = Complex.cos (theta : ℂ) + Complex.sin (theta : ℂ) * Complex.I := by
    unfold offlineCrossRate
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [← Complex.ofReal_cos, ← Complex.ofReal_sin,
      show (Real.cos theta / 2 + Real.cos theta / 2 : ℝ) = Real.cos theta by ring,
      show ((0 : ℝ) - Real.sin theta) = -(Real.sin theta) by ring, Complex.ofReal_neg]
    ring
  have hnorm : ‖Complex.cos (theta : ℂ) + Complex.sin (theta : ℂ) * Complex.I‖ = 1 :=
    Complex.norm_cos_add_sin_mul_I theta
  have hnew : Complex.cos (theta : ℂ) + Complex.sin (theta : ℂ) * Complex.I ≠ 0 := by
    intro h
    rw [h, norm_zero] at hnorm
    exact zero_ne_one hnorm
  have harg : Complex.arg (Complex.cos (theta : ℂ) + Complex.sin (theta : ℂ) * Complex.I)
      = theta :=
    Complex.arg_cos_add_sin_mul_I ⟨by linarith, by linarith⟩
  rw [hrate, show (-((alpha : ℂ) + 1)) = (-((c : ℝ) : ℂ)) by rw [hc]; push_cast; ring,
    re_cpow_neg_ofReal hnew c, harg, hnorm, Real.one_rpow, one_mul]
  exact hcosneg

/-! ## The single-mode floor and the Hilbert–Schmidt weight -/

/-- **The unweighted energy of one mode of multiplicity `m` is `2m²/a`.** -/
theorem finiteOfflineCauchyEnergy_single {a gamma : ℝ} (ha : 0 < a) (m : ℕ) :
    finiteOfflineCauchyEnergy (fun _ : Fin 1 => a) (fun _ => gamma) (fun _ => m)
      = 2 * (m : ℝ) ^ 2 / a := by
  have hk : transverseCauchyKernel a a (gamma - gamma) = (2 * a)⁻¹ :=
    transverseCauchyKernel_self ha gamma
  unfold finiteOfflineCauchyEnergy
  rw [Fin.sum_univ_one, Fin.sum_univ_one]
  show (4 : ℝ) * ((m : ℝ) * (m : ℝ) * transverseCauchyKernel a a (gamma - gamma)) = _
  rw [hk, inv_eq_one_div, mul_one_div, ← mul_div_assoc,
    div_eq_div_iff (by positivity) (by positivity)]
  ring

/-- **The four-unit per-zero floor.**  A single strip zero of multiplicity at least one has
unweighted boundary energy strictly greater than four. -/
theorem finiteOfflineCauchyEnergy_single_gt_four {a gamma : ℝ} (ha : 0 < a) (ha' : a < 1 / 2)
    {m : ℕ} (hm : 1 ≤ m) :
    4 < finiteOfflineCauchyEnergy (fun _ : Fin 1 => a) (fun _ => gamma) (fun _ => m) := by
  rw [finiteOfflineCauchyEnergy_single ha m]
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  rw [lt_div_iff₀ ha]
  nlinarith


/-! ## The Hilbert-Schmidt weight is the first moment -/

/-- Shifting the half-line: `∫_{y>0} g(x+y) dy = ∫_{t>x} g(t) dt`. -/
theorem lintegral_Ioi_add_left (g : ℝ → ℝ≥0∞) (x : ℝ) :
    ∫⁻ y in Ioi (0 : ℝ), g (x + y) = ∫⁻ t in Ioi x, g t := by
  have h1 : (fun y : ℝ => (Ioi (0 : ℝ)).indicator (fun y => g (x + y)) y)
      = fun y : ℝ => (Ioi x).indicator g (y + x) := by
    funext y
    by_cases hy : y ∈ Ioi (0 : ℝ)
    · have hy' : y + x ∈ Ioi x := by
        simp only [mem_Ioi] at hy ⊢
        linarith
      rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy', add_comm]
    · have hy' : y + x ∉ Ioi x := by
        simp only [mem_Ioi] at hy ⊢
        intro h
        exact hy (by linarith)
      rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy']
  rw [← lintegral_indicator measurableSet_Ioi, ← lintegral_indicator measurableSet_Ioi, h1]
  exact lintegral_add_right_eq_self ((Ioi x).indicator g) x

/-- **The Hilbert-Schmidt weight is `α = 1`.**  The Hilbert-Schmidt square of the Hankel operator
with kernel `ℓ(x+y)` is the double half-line integral of `‖ℓ(x+y)‖²`, and that double integral is
the *first-moment* energy `∫_0^∞ t ‖ℓ(t)‖² dt`, not the unweighted one. -/
theorem lintegral_hankelSquare_eq_firstMoment {g : ℝ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ x in Ioi (0 : ℝ), ∫⁻ y in Ioi (0 : ℝ), g (x + y)
      = ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal t * g t := by
  have hstep : ∀ x ∈ Ioi (0 : ℝ), (∫⁻ y in Ioi (0 : ℝ), g (x + y))
      = ∫⁻ t in Ioi (0 : ℝ), (Ioi x).indicator g t := by
    intro x hx
    rw [lintegral_Ioi_add_left g x, setLIntegral_indicator measurableSet_Ioi]
    congr 1
    rw [Set.inter_eq_self_of_subset_left (Ioi_subset_Ioi (le_of_lt hx))]
  rw [setLIntegral_congr_fun measurableSet_Ioi hstep]
  have hmeas : AEMeasurable
      (Function.uncurry fun x t : ℝ => (Ioi x).indicator g t)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
    have : (Function.uncurry fun x t : ℝ => (Ioi x).indicator g t)
        = fun p : ℝ × ℝ => if p.1 < p.2 then g p.2 else 0 := by
      funext p
      simp [Function.uncurry, Set.indicator_apply]
    rw [this]
    refine Measurable.aemeasurable ?_
    exact Measurable.ite (measurableSet_lt measurable_fst measurable_snd)
      (hg.comp measurable_snd) measurable_const
  rw [lintegral_lintegral_swap hmeas]
  refine setLIntegral_congr_fun measurableSet_Ioi ?_
  intro t ht
  show (∫⁻ x in Ioi (0 : ℝ), (Ioi x).indicator g t) = ENNReal.ofReal t * g t
  have hind : (fun x : ℝ => (Ioi x).indicator g t) = (Iio t).indicator (fun _ => g t) := by
    funext x
    simp [Set.indicator_apply]
  rw [hind, setLIntegral_indicator measurableSet_Iio, setLIntegral_const]
  have hset : Iio t ∩ Ioi (0 : ℝ) = Ioo (0 : ℝ) t := by
    ext x
    simp [and_comm]
  rw [hset, Real.volume_Ioo, sub_zero, mul_comm]

end

end RHTower
