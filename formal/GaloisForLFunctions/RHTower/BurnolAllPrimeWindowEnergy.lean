import GaloisForLFunctions.RHTower.BurnolReciprocalStokesSewing
import GaloisForLFunctions.RHTower.BurnolCoPoissonSubWindowSource
import GaloisForLFunctions.RHTower.EvenL2LogUnitary

/-!
# The literal all-prime Burnol window energies

The co-Poisson value of the prime window `[p⁻¹, 1]` is `G_p(t) = ({t} - {p t})/t`.  Below the lower
window end it is the constant `1 - p`, and globally it obeys the two pointwise estimates
`|G_p| ≤ 2p` and `|G_p(t)| ≤ |t|⁻¹`.  Splitting the even integral at `(2p)⁻¹` gives the exact
two-sided window energy

`2 (p-1)² / p ≤ ‖G_p‖₂² ≤ 8 p`,

so the weighted family `(A_p G_p)_p` with `A_p = 1/(p log p)` lies in the Hilbert direct sum: the
upper bound turns its energy into `8 ∑ 1/(p (log p)²)`, which converges.
-/

open Real Filter Topology MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace RHTower

/-! ## Even splitting -/

/-- An even nonnegative integrand has twice its positive-ray Lebesgue integral. -/
theorem lintegral_even_eq_two_mul_Ioi {g : ℝ → ℝ≥0∞} (hg : ∀ x : ℝ, g (-x) = g x) :
    ∫⁻ x : ℝ, g x = 2 * ∫⁻ x in Ioi (0 : ℝ), g x := by
  calc ∫⁻ x : ℝ, g x
      = (∫⁻ x in Ioi (0 : ℝ), g x) + ∫⁻ x in Iic (0 : ℝ), g x := by
        simpa only [Set.compl_Ioi] using
          (MeasureTheory.lintegral_add_compl (μ := volume) (A := Ioi (0 : ℝ)) g
            measurableSet_Ioi).symm
    _ = (∫⁻ x in Ioi (0 : ℝ), g x) + ∫⁻ x in Iio (0 : ℝ), g x := by
        rw [MeasureTheory.restrict_Iio_eq_restrict_Iic (μ := volume)]
    _ = (∫⁻ x in Ioi (0 : ℝ), g x) + ∫⁻ x in Ioi (0 : ℝ), g (-x) := by
        rw [lintegral_Iio_eq_lintegral_Ioi_neg]
    _ = 2 * ∫⁻ x in Ioi (0 : ℝ), g x := by
        rw [lintegral_congr (fun x => hg x)]
        ring

/-! ## The prime window and its energy -/

/-- The co-Poisson value of the prime window `[p⁻¹, 1]`. -/
def burnolPrimeWindow (p : ℕ) : ℝ → ℂ :=
  burnolCoPoissonRightSum (coPoissonSubWindowSeed ((p : ℝ)⁻¹) 1)

/-- The Lebesgue energy of the prime window on the whole line. -/
def burnolPrimeWindowEnergy (p : ℕ) : ℝ≥0∞ :=
  ∫⁻ x : ℝ, ENNReal.ofReal (‖burnolPrimeWindow p x‖ ^ 2)

theorem burnolPrimeWindow_inv_pos {p : ℕ} (hp : 2 ≤ p) : (0 : ℝ) < ((p : ℝ)⁻¹) := by
  have hppos : (0 : ℝ) < (p : ℝ) := by
    have h : (0 : ℕ) < p := lt_of_lt_of_le two_pos hp
    exact_mod_cast h
  positivity

theorem burnolPrimeWindow_inv_le_one {p : ℕ} (hp : 2 ≤ p) : ((p : ℝ)⁻¹) ≤ 1 := by
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast Nat.one_le_of_lt hp
  rw [inv_le_one_iff₀]
  exact Or.inr hp1

theorem burnolPrimeWindowEnergy_eq_two_mul (p : ℕ) :
    burnolPrimeWindowEnergy p =
      2 * ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (‖burnolPrimeWindow p x‖ ^ 2) := by
  refine lintegral_even_eq_two_mul_Ioi (fun x => ?_)
  rw [burnolPrimeWindow, burnolCoPoissonRightSum_even]

/-- **Lower window energy.** -/
theorem burnolPrimeWindowEnergy_lower {p : ℕ} (hp : 2 ≤ p) :
    ENNReal.ofReal (2 * ((p : ℝ) - 1) ^ 2 / (p : ℝ)) ≤ burnolPrimeWindowEnergy p := by
  have hppos : (0 : ℝ) < (p : ℝ) := by
    have : (0 : ℕ) < p := by omega
    exact_mod_cast this
  have hcpos := burnolPrimeWindow_inv_pos hp
  have hcd := burnolPrimeWindow_inv_le_one hp
  have hconst : ∀ x ∈ Ioo (0 : ℝ) ((p : ℝ)⁻¹),
      ENNReal.ofReal (‖burnolPrimeWindow p x‖ ^ 2) =
        ENNReal.ofReal (((p : ℝ) - 1) ^ 2) := by
    intro x hx
    rw [burnolPrimeWindow,
      burnolCoPoissonRightSum_coPoissonSubWindowSeed_eq_const hcpos hcd hx.1 hx.2,
      Complex.norm_real, Real.norm_eq_abs]
    congr 1
    rw [sq_abs]
    field_simp
  have hmono : ∫⁻ x in Ioo (0 : ℝ) ((p : ℝ)⁻¹),
      ENNReal.ofReal (‖burnolPrimeWindow p x‖ ^ 2) ≤
      ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (‖burnolPrimeWindow p x‖ ^ 2) :=
    lintegral_mono_set (fun x hx => hx.1)
  have hval : ∫⁻ x in Ioo (0 : ℝ) ((p : ℝ)⁻¹),
      ENNReal.ofReal (‖burnolPrimeWindow p x‖ ^ 2) =
        ENNReal.ofReal (((p : ℝ) - 1) ^ 2 / (p : ℝ)) := by
    rw [setLIntegral_congr_fun measurableSet_Ioo hconst, setLIntegral_const,
      Real.volume_Ioo, sub_zero, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
  rw [burnolPrimeWindowEnergy_eq_two_mul p]
  calc ENNReal.ofReal (2 * ((p : ℝ) - 1) ^ 2 / (p : ℝ))
      = 2 * ENNReal.ofReal (((p : ℝ) - 1) ^ 2 / (p : ℝ)) := by
        rw [show (2 : ℝ) * ((p : ℝ) - 1) ^ 2 / (p : ℝ) = 2 * (((p : ℝ) - 1) ^ 2 / (p : ℝ)) by ring,
          ENNReal.ofReal_mul (by norm_num)]
        norm_num
    _ ≤ 2 * ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (‖burnolPrimeWindow p x‖ ^ 2) := by
        rw [← hval]
        gcongr

/-- **Upper window energy.** -/
theorem burnolPrimeWindowEnergy_upper {p : ℕ} (hp : 2 ≤ p) :
    burnolPrimeWindowEnergy p ≤ ENNReal.ofReal (8 * (p : ℝ)) := by
  have hppos : (0 : ℝ) < (p : ℝ) := by
    have : (0 : ℕ) < p := by omega
    exact_mod_cast this
  have hcpos := burnolPrimeWindow_inv_pos hp
  have hcd := burnolPrimeWindow_inv_le_one hp
  set a : ℝ := (2 * (p : ℝ))⁻¹ with ha
  have hapos : (0 : ℝ) < a := by rw [ha]; positivity
  have hdisj : Disjoint (Ioc (0 : ℝ) a) (Ioi a) :=
    Set.disjoint_left.mpr fun x hx hx' => absurd hx' (not_lt.mpr hx.2)
  -- near piece
  have hnear : ∫⁻ x in Ioc (0 : ℝ) a,
      ENNReal.ofReal (‖burnolPrimeWindow p x‖ ^ 2) ≤ ENNReal.ofReal (2 * (p : ℝ)) := by
    have hb : ∀ᵐ x ∂(volume.restrict (Ioc (0 : ℝ) a)),
        ENNReal.ofReal (‖burnolPrimeWindow p x‖ ^ 2) ≤
          ENNReal.ofReal (4 * (p : ℝ) ^ 2) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with x _
      refine ENNReal.ofReal_le_ofReal ?_
      have hg := norm_burnolCoPoissonRightSum_coPoissonSubWindowSeed_le_global hcpos hcd x
      have h2 : (2 : ℝ) / ((p : ℝ)⁻¹) = 2 * (p : ℝ) := by field_simp
      rw [h2] at hg
      have hnn : 0 ≤ ‖burnolPrimeWindow p x‖ := norm_nonneg _
      have hgg : ‖burnolPrimeWindow p x‖ ≤ 2 * (p : ℝ) := by
        rw [burnolPrimeWindow]
        exact hg
      nlinarith [hgg, hnn, hppos]
    refine (lintegral_mono_ae hb).trans ?_
    rw [setLIntegral_const, Real.volume_Ioc, sub_zero,
      ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [ha]
    field_simp
    norm_num
  -- far piece
  have hfar : ∫⁻ x in Ioi a,
      ENNReal.ofReal (‖burnolPrimeWindow p x‖ ^ 2) ≤ ENNReal.ofReal (2 * (p : ℝ)) := by
    have hint : IntegrableOn (fun t : ℝ => t ^ (-2 : ℝ)) (Ioi a) volume :=
      integrableOn_Ioi_rpow_of_lt (by norm_num) hapos
    have hvalint : ∫ t in Ioi a, t ^ (-2 : ℝ) = a⁻¹ := by
      rw [integral_Ioi_rpow_of_lt (by norm_num) hapos,
        show (-2 : ℝ) + 1 = -((1 : ℕ) : ℝ) by norm_num, Real.rpow_neg hapos.le,
        Real.rpow_natCast, pow_one]
      norm_num
    have hnn : 0 ≤ᵐ[volume.restrict (Ioi a)] fun t : ℝ => t ^ (-2 : ℝ) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact Real.rpow_nonneg (le_of_lt (lt_trans hapos ht)) _
    have hlint : ∫⁻ t in Ioi a, ENNReal.ofReal (t ^ (-2 : ℝ)) = ENNReal.ofReal a⁻¹ := by
      rw [← hvalint, ofReal_integral_eq_lintegral_ofReal hint hnn]
    have hb : ∀ᵐ x ∂(volume.restrict (Ioi a)),
        ENNReal.ofReal (‖burnolPrimeWindow p x‖ ^ 2) ≤ ENNReal.ofReal (x ^ (-2 : ℝ)) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hxpos : (0 : ℝ) < x := lt_trans hapos hx
      refine ENNReal.ofReal_le_ofReal ?_
      have hg := norm_burnolCoPoissonRightSum_coPoissonSubWindowSeed_le hcpos hcd hxpos
      have hgg : ‖burnolPrimeWindow p x‖ ≤ 1 / x := by
        rw [burnolPrimeWindow]
        exact hg
      have hnn' : 0 ≤ ‖burnolPrimeWindow p x‖ := norm_nonneg _
      have hrp : x ^ (-2 : ℝ) = (x ^ 2)⁻¹ := by
        rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg hxpos.le,
          Real.rpow_natCast]
      rw [hrp]
      have hsq : ‖burnolPrimeWindow p x‖ ^ 2 ≤ (1 / x) ^ 2 := pow_le_pow_left₀ hnn' hgg 2
      refine hsq.trans_eq ?_
      rw [div_pow, one_pow, one_div]
    refine (lintegral_mono_ae hb).trans ?_
    rw [hlint]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [ha, inv_inv]
  have hsplit : Ioi (0 : ℝ) = Ioc (0 : ℝ) a ∪ Ioi a := (Set.Ioc_union_Ioi_eq_Ioi hapos.le).symm
  rw [burnolPrimeWindowEnergy_eq_two_mul p, hsplit,
    lintegral_union measurableSet_Ioi hdisj]
  calc 2 * ((∫⁻ x in Ioc (0 : ℝ) a, ENNReal.ofReal (‖burnolPrimeWindow p x‖ ^ 2)) +
        ∫⁻ x in Ioi a, ENNReal.ofReal (‖burnolPrimeWindow p x‖ ^ 2))
      ≤ 2 * (ENNReal.ofReal (2 * (p : ℝ)) + ENNReal.ofReal (2 * (p : ℝ))) :=
        by gcongr
    _ = ENNReal.ofReal (8 * (p : ℝ)) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          show (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) by simp,
          ← ENNReal.ofReal_mul (by norm_num)]
        congr 1
        ring

/-- The window energy is finite. -/
theorem burnolPrimeWindowEnergy_ne_top {p : ℕ} (hp : 2 ≤ p) :
    burnolPrimeWindowEnergy p ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (burnolPrimeWindowEnergy_upper hp)

/-- **The weighted all-prime window family lies in the Hilbert direct sum.** -/
theorem burnolSummable_primeWindowSourceEnergy :
    Summable (fun p : Nat.Primes =>
      burnolSourceBoundary (p : ℕ) ^ 2 * (burnolPrimeWindowEnergy (p : ℕ)).toReal) := by
  have hle : ∀ p : Nat.Primes,
      burnolSourceBoundary (p : ℕ) ^ 2 * (burnolPrimeWindowEnergy (p : ℕ)).toReal ≤
        8 * (1 / (((p : ℕ) : ℝ) * Real.log ((p : ℕ) : ℝ) ^ 2)) := by
    intro p
    have hp : 2 ≤ (p : ℕ) := p.2.two_le
    have hppos : (0 : ℝ) < ((p : ℕ) : ℝ) := by
      have : (0 : ℕ) < (p : ℕ) := by omega
      exact_mod_cast this
    have hp1 : (1 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast hp.trans_lt' one_lt_two
    have hLpos : 0 < Real.log ((p : ℕ) : ℝ) := Real.log_pos hp1
    have hupper : (burnolPrimeWindowEnergy (p : ℕ)).toReal ≤ 8 * ((p : ℕ) : ℝ) := by
      have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (burnolPrimeWindowEnergy_upper hp)
      rwa [ENNReal.toReal_ofReal (by positivity)] at h
    have hnn : 0 ≤ burnolSourceBoundary (p : ℕ) ^ 2 := sq_nonneg _
    have hbound := mul_le_mul_of_nonneg_left hupper hnn
    refine hbound.trans_eq ?_
    rw [burnolSourceBoundary]
    field_simp
  exact Summable.of_nonneg_of_le
    (fun p => mul_nonneg (sq_nonneg _) ENNReal.toReal_nonneg) hle
    (burnolSummable_prime_one_div_mul_log_sq.mul_left 8)

/-! ## The four-way jet equivalence -/

theorem burnolBddAbove_finsetSums_iff_summable {ι : Type*} {f : ι → ℝ} (hf : ∀ i, 0 ≤ f i) :
    BddAbove (Set.range fun s : Finset ι => ∑ i ∈ s, f i) ↔ Summable f := by
  constructor
  · rintro ⟨c, hc⟩
    exact summable_of_sum_le hf (fun u => hc (Set.mem_range_self u))
  · intro hs
    refine ⟨∑' i, f i, ?_⟩
    rintro x ⟨u, rfl⟩
    exact hs.sum_le_tsum u (fun i _ => hf i)

/-- The completed Xi conormal weighted by the strict source boundary. -/
def burnolCompletedConormal (c : ℂ) (p : ℕ) : ℂ :=
  c / ((p : ℂ) * ((Real.log (p : ℝ) : ℝ) : ℂ))

theorem burnolAllPrimeCompletion_mul_inverseCoefficient {c ρ : ℂ} {p : ℕ} (hp : 2 ≤ p)
    (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1) :
    burnolAllPrimeCompletionMultiplier p ρ *
        burnolAllPrimeInverseCompletionCoefficient c ρ p = burnolCompletedConormal c p := by
  have hCne : burnolAllPrimeCompletionMultiplier p ρ ≠ 0 :=
    burnolAllPrimeCompletionMultiplier_ne_zero hp hρ0 hρ1
  rw [burnolAllPrimeInverseCompletionCoefficient, burnolCompletedConormal]
  field_simp

/-- **The diagonal range condition is the square summability of the inverse-completed jet.** -/
theorem burnolCompletedConormal_mem_range_iff {c ρ : ℂ}
    (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1) :
    (∃ z : Nat.Primes → ℂ, Summable (fun p : Nat.Primes => ‖z p‖ ^ 2) ∧
        ∀ p : Nat.Primes, burnolAllPrimeCompletionMultiplier (p : ℕ) ρ * z p =
          burnolCompletedConormal c (p : ℕ)) ↔
      Summable (fun p : Nat.Primes =>
        ‖burnolAllPrimeInverseCompletionCoefficient c ρ (p : ℕ)‖ ^ 2) := by
  constructor
  · rintro ⟨z, hzsum, hz⟩
    refine hzsum.congr (fun p => ?_)
    have hp : 2 ≤ (p : ℕ) := p.2.two_le
    have hCne : burnolAllPrimeCompletionMultiplier (p : ℕ) ρ ≠ 0 :=
      burnolAllPrimeCompletionMultiplier_ne_zero hp hρ0 hρ1
    have hkey := (burnolAllPrimeCompletion_mul_inverseCoefficient (c := c) hp hρ0 hρ1).trans
      (hz p).symm
    have := mul_left_cancel₀ hCne hkey
    rw [this]
  · intro hsum
    refine ⟨fun p => burnolAllPrimeInverseCompletionCoefficient c ρ (p : ℕ), hsum, fun p => ?_⟩
    exact burnolAllPrimeCompletion_mul_inverseCoefficient p.2.two_le hρ0 hρ1

/-- **The all-prime Cartier jet equivalence.**  Uniform boundedness of the finite multiplicity-jet
energies, square summability of the jet, admission of the completed conormal into the diagonal
range, and the closed left half of the critical strip are one and the same condition. -/
theorem burnolAllPrimeCartierJet_tfae {c ρ : ℂ} (hc : c ≠ 0)
    (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1) :
    (BddAbove (Set.range fun P : Finset Nat.Primes =>
        ∑ p ∈ P, ‖burnolAllPrimeInverseCompletionCoefficient c ρ (p : ℕ)‖ ^ 2) ↔
      Summable (fun p : Nat.Primes =>
        ‖burnolAllPrimeInverseCompletionCoefficient c ρ (p : ℕ)‖ ^ 2)) ∧
    ((∃ z : Nat.Primes → ℂ, Summable (fun p : Nat.Primes => ‖z p‖ ^ 2) ∧
        ∀ p : Nat.Primes, burnolAllPrimeCompletionMultiplier (p : ℕ) ρ * z p =
          burnolCompletedConormal c (p : ℕ)) ↔
      Summable (fun p : Nat.Primes =>
        ‖burnolAllPrimeInverseCompletionCoefficient c ρ (p : ℕ)‖ ^ 2)) ∧
    (Summable (fun p : Nat.Primes =>
        ‖burnolAllPrimeInverseCompletionCoefficient c ρ (p : ℕ)‖ ^ 2) ↔ ρ.re ≤ 1 / 2) :=
  ⟨burnolBddAbove_finsetSums_iff_summable (fun _ => sq_nonneg _),
    burnolCompletedConormal_mem_range_iff hρ0 hρ1,
    summable_burnolAllPrimeInverseCompletionCoefficient_sq_iff hc hρ0 hρ1⟩

end RHTower
