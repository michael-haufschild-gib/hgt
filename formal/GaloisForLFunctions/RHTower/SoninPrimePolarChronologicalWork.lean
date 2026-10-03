import GaloisForLFunctions.RHTower.SoninPrimePolarCumulativeEnergy
import GaloisForLFunctions.RHTower.SoninPrimePolarGroundTransfer

/-!
# Chronological work of the original prime–polar ground source

The actual entering ground interval has an ordered exponential covariance.
The original prime coefficients and the original polar density yield a
literal counting discrepancy on the earlier side and a literal harmonic
discrepancy on the later side. Their product is the complete cross work.

Prime insertion and continuous polar motion have exact signed energy laws.
No sign, decorrelation, cofinal convergence or uniform arithmetic bound is
assumed or concluded.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace RHTower


/-- The literal entering ground interval, with its dilation normalization removed. -/
def soninGroundEntry (a u : ℝ) : SoninL2 :=
  (Real.exp (-u/2):ℂ) • rayDilate (Real.exp u) (soninCutoffMonomial a 0)

private def countDensity (u : ℝ) : ℝ := (Real.exp u+1)/u

private theorem entry_continuous (a : ℝ) : Continuous (soninGroundEntry a) := by
  exact (by fun_prop : Continuous (fun u : ℝ => (Real.exp (-u/2):ℂ))).smul
    (continuous_dilationOrbit (soninCutoffMonomial a 0))

private theorem density_continuousOn (b R : ℝ) (hb : 0 < b) :
    ContinuousOn countDensity (Icc b R) := by
  intro u hu
  apply ContinuousAt.continuousWithinAt
  have hu0 : u ≠ 0 := ne_of_gt (lt_of_lt_of_le hb hu.1)
  unfold countDensity
  fun_prop

private theorem density_entry_integrable (a b R : ℝ) (hb : 0 < b) :
    IntegrableOn (fun u => (countDensity u:ℂ) • soninGroundEntry a u) (Icc b R) :=
  ((Complex.continuous_ofReal.comp_continuousOn (density_continuousOn b R hb)).smul
    (entry_continuous a).continuousOn).integrableOn_Icc

private theorem inner_integral_left {μ : Measure ℝ} {f : ℝ → SoninL2}
    (hf : Integrable f μ) (y : SoninL2) :
    inner ℂ (∫ u, f u ∂μ) y = ∫ u, inner ℂ (f u) y ∂μ := by
  rw [← inner_conj_symm, ← integral_inner hf, ← integral_conj]
  apply integral_congr_ae
  filter_upwards [] with u
  exact inner_conj_symm _ _

/-- Exact ordered covariance of the actual entering ground intervals. -/
theorem inner_soninGroundEntry_of_le (a : ℝ) (ha : 0 ≤ a) (u v : ℝ) (huv : u ≤ v) :
    inner ℂ (soninGroundEntry a u) (soninGroundEntry a v) =
      ((2*a*Real.exp (-v):ℝ):ℂ) := by
  rw [soninGroundEntry, soninGroundEntry, inner_smul_left, inner_smul_right,
    inner_logDilation_soninCutoffMonomial, norm_sq_soninCutoffMonomial a ha 0,
    abs_of_nonpos (sub_nonpos.mpr huv)]
  simp only [Nat.cast_zero, mul_zero, zero_add, pow_one, div_one,
    Complex.conj_ofReal, ← Complex.ofReal_mul]
  congr 1
  have he : Real.exp (-u/2)*Real.exp (-v/2)*Real.exp (-(1/2)*(-(u-v))) =
      Real.exp (-v) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  calc
    _ = 2*a*(Real.exp (-u/2)*Real.exp (-v/2)*Real.exp (-(1/2)*(-(u-v)))) := by ring
    _ = _ := by rw [he]

private theorem prime_entry (a : ℝ) (p : Nat.Primes) :
    ((Real.sqrt (p:ℝ))⁻¹ : ℂ) • rayDilate (Real.exp (Real.log (p:ℝ)))
      (soninCutoffMonomial a 0) = soninGroundEntry a (Real.log (p:ℝ)) := by
  unfold soninGroundEntry
  congr 2
  have hp : 0 < (p:ℝ) := by exact_mod_cast p.prop.pos
  have hs : Real.sqrt (p:ℝ) = Real.exp (Real.log (p:ℝ)/2) := by
    apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (Real.exp_pos _).le).mp
    rw [Real.sq_sqrt hp.le, ← Real.exp_nat_mul]
    calc
      _ = Real.exp (Real.log (p:ℝ)) := (Real.exp_log hp).symm
      _ = _ := by
        congr 1
        ring
  rw [hs, ← Complex.ofReal_inv, ← Real.exp_neg]
  rw [neg_div]

private theorem density_entry (a u : ℝ) :
    soninLogPolarDensity u • rayDilate (Real.exp u) (soninCutoffMonomial a 0) =
      (countDensity u:ℂ) • soninGroundEntry a u := by
  unfold soninGroundEntry
  rw [smul_smul]
  congr 1
  rw [soninLogPolarDensity, ← Complex.ofReal_mul]
  congr 1
  unfold countDensity
  rw [Real.cosh_eq]
  have he : Real.exp u*Real.exp (-u/2) = Real.exp (u/2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [neg_div]
  rw [neg_div] at he
  calc
    _ = (Real.exp (u/2)+Real.exp (-(u/2)))/u := by ring
    _ = _ := by rw [← he]; ring

private theorem source_entries (a : ℝ) (P : Finset Nat.Primes) (b R : ℝ) (hb : 0 < b) :
    soninPrimePolarSourceOperator P b R 1 hb (soninCutoffMonomial a 0) =
      (∑ p ∈ P, soninGroundEntry a (Real.log (p:ℝ))) -
        ∫ u in Icc b R, (countDensity u:ℂ) • soninGroundEntry a u := by
  rw [soninPrimePolarSourceOperator_apply]
  simp only [one_mul, prime_entry, density_entry]

private theorem cumulative_terminal_eq (P : Finset Nat.Primes) (b R : ℝ)
    (hP : ∀ p ∈ P, Real.log (p:ℝ) ≤ R) :
    soninPrimePolarGroundCumulative P b R R =
      (∑ _p ∈ P, (1:ℝ)) - ∫ u in Icc b R, countDensity u := by
  unfold soninPrimePolarGroundCumulative
  congr 1
  · exact Finset.sum_congr rfl fun p hp => if_pos (hP p hp)
  · apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
    exact if_pos hu.2

/-- A later entering interval tests exactly the earlier terminal counting discrepancy. -/
theorem inner_soninPrimePolar_ground_entry (a : ℝ) (ha : 0 ≤ a)
    (P : Finset Nat.Primes) (b R v : ℝ) (hb : 0 < b)
    (hP : ∀ p ∈ P, Real.log (p:ℝ) ≤ R) (hv : R ≤ v) :
    inner ℂ (soninPrimePolarSourceOperator P b R 1 hb (soninCutoffMonomial a 0))
      (soninGroundEntry a v) =
      ((2*a*soninPrimePolarGroundCumulative P b R R*Real.exp (-v):ℝ):ℂ) := by
  rw [source_entries, inner_sub_left, sum_inner,
    inner_integral_left (density_entry_integrable a b R hb)]
  have hs : (∑ p ∈ P, inner ℂ (soninGroundEntry a (Real.log (p:ℝ))) (soninGroundEntry a v)) =
      ∑ _p ∈ P, ((2*a*Real.exp (-v):ℝ):ℂ) :=
    Finset.sum_congr rfl fun p hp => inner_soninGroundEntry_of_le a ha _ v ((hP p hp).trans hv)
  rw [hs]
  have hi : (∫ u in Icc b R, inner ℂ ((countDensity u:ℂ) • soninGroundEntry a u)
      (soninGroundEntry a v)) =
        (((∫ u in Icc b R, countDensity u)*(2*a*Real.exp (-v)):ℝ):ℂ) := by
    rw [Complex.ofReal_mul, ← integral_complex_ofReal, ← integral_mul_const]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
    rw [inner_smul_left, inner_soninGroundEntry_of_le a ha u v (hu.2.trans hv), Complex.conj_ofReal]
  rw [hi, cumulative_terminal_eq P b R hP]
  push_cast
  rw [Finset.sum_const, nsmul_eq_mul, Finset.sum_const, nsmul_eq_mul]
  ring


/-- The later harmonic discrepancy retains the original prime and polar terms. -/
def soninPrimePolarHarmonicDiscrepancy (P : Finset Nat.Primes) (b R : ℝ) : ℝ :=
  (∑ p ∈ P, (p:ℝ)⁻¹) - ∫ u in Icc b R, (1+Real.exp (-u))/u

private theorem exp_neg_log_prime (p : Nat.Primes) : Real.exp (-Real.log (p:ℝ)) = (p:ℝ)⁻¹ := by
  rw [Real.exp_neg, Real.exp_log (show 0 < (p:ℝ) by exact_mod_cast p.prop.pos)]

private theorem density_exp_neg (u : ℝ) :
    countDensity u*Real.exp (-u) = (1+Real.exp (-u))/u := by
  have he : Real.exp u*Real.exp (-u) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  unfold countDensity
  calc
    _ = (Real.exp u*Real.exp (-u)+Real.exp (-u))/u := by ring
    _ = _ := by rw [he]

/-- Exact arithmetic cross work of two chronologically ordered native blocks. -/
theorem inner_soninPrimePolar_ground_ordered (a : ℝ) (ha : 0 ≤ a)
    (P Q : Finset Nat.Primes) (b R c S : ℝ) (hb : 0 < b) (hc : 0 < c)
    (hP : ∀ p ∈ P, Real.log (p:ℝ) ≤ R)
    (hQ : ∀ q ∈ Q, R ≤ Real.log (q:ℝ)) (hRc : R ≤ c) :
    inner ℂ (soninPrimePolarSourceOperator P b R 1 hb (soninCutoffMonomial a 0))
      (soninPrimePolarSourceOperator Q c S 1 hc (soninCutoffMonomial a 0)) =
      ((2*a*soninPrimePolarGroundCumulative P b R R*
        soninPrimePolarHarmonicDiscrepancy Q c S:ℝ):ℂ) := by
  rw [source_entries a Q c S hc, inner_sub_right, inner_sum,
    ← integral_inner (density_entry_integrable a c S hc)]
  have hs : (∑ q ∈ Q, inner ℂ
      (soninPrimePolarSourceOperator P b R 1 hb (soninCutoffMonomial a 0))
      (soninGroundEntry a (Real.log (q:ℝ)))) =
      ∑ q ∈ Q, ((2*a*soninPrimePolarGroundCumulative P b R R*(q:ℝ)⁻¹:ℝ):ℂ) := by
    apply Finset.sum_congr rfl
    intro q hq
    rw [inner_soninPrimePolar_ground_entry a ha P b R _ hb hP (hQ q hq), exp_neg_log_prime]
  rw [hs]
  have hi : (∫ u in Icc c S, inner ℂ
      (soninPrimePolarSourceOperator P b R 1 hb (soninCutoffMonomial a 0))
      ((countDensity u:ℂ) • soninGroundEntry a u)) =
      ((2*a*soninPrimePolarGroundCumulative P b R R*
        (∫ u in Icc c S, (1+Real.exp (-u))/u):ℝ):ℂ) := by
    rw [Complex.ofReal_mul, ← integral_complex_ofReal, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
    rw [inner_smul_right, inner_soninPrimePolar_ground_entry a ha P b R u hb hP (hRc.trans hu.1)]
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
    congr 1
    rw [← density_exp_neg]
    ring
  rw [hi, soninPrimePolarHarmonicDiscrepancy]
  push_cast
  rw [mul_sub, Finset.mul_sum]

/-- An actual prime entry contributes its harmonic diagonal plus the
signed interaction with the entire preceding prime–polar discrepancy. -/
theorem soninPrimePolar_ground_energy_prime_jump (a : ℝ) (ha : 0 ≤ a)
    (P : Finset Nat.Primes) (p : Nat.Primes) (hp : p ∉ P) (b : ℝ) (hb : 0 < b)
    (hP : ∀ q ∈ P, Real.log (q:ℝ) ≤ Real.log (p:ℝ)) :
    ‖soninPrimePolarSourceOperator (insert p P) b (Real.log (p:ℝ)) 1 hb
        (soninCutoffMonomial a 0)‖^2 -
      ‖soninPrimePolarSourceOperator P b (Real.log (p:ℝ)) 1 hb
        (soninCutoffMonomial a 0)‖^2 =
      2*a*(2*soninPrimePolarGroundCumulative P b (Real.log (p:ℝ)) (Real.log (p:ℝ))+1)/(p:ℝ) := by
  classical
  have he : soninPrimePolarSourceOperator (insert p P) b (Real.log (p:ℝ)) 1 hb
      (soninCutoffMonomial a 0) =
      soninPrimePolarSourceOperator P b (Real.log (p:ℝ)) 1 hb (soninCutoffMonomial a 0) +
        soninGroundEntry a (Real.log (p:ℝ)) := by
    rw [source_entries, source_entries, Finset.sum_insert hp]
    abel
  have hn : ‖soninGroundEntry a (Real.log (p:ℝ))‖^2 = 2*a*(p:ℝ)⁻¹ := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), inner_soninGroundEntry_of_le a ha _ _ le_rfl,
      exp_neg_log_prime]
    rfl
  rw [he, norm_add_sq (𝕜 := ℂ),
    inner_soninPrimePolar_ground_entry a ha P b _ _ hb hP le_rfl,
    exp_neg_log_prime, hn]
  change ‖soninPrimePolarSourceOperator P b (Real.log (p:ℝ)) 1 hb (soninCutoffMonomial a 0)‖^2 +
    2*(2*a*soninPrimePolarGroundCumulative P b (Real.log (p:ℝ)) (Real.log (p:ℝ))*(p:ℝ)⁻¹) +
    2*a*(p:ℝ)⁻¹ - ‖soninPrimePolarSourceOperator P b (Real.log (p:ℝ)) 1 hb (soninCutoffMonomial a 0)‖^2 = _
  ring


/-- Actual polar motion of the original finite source, before taking its energy. -/
theorem hasDerivAt_soninPrimePolar_ground_polar (a : ℝ) (P : Finset Nat.Primes)
    (b R : ℝ) (hb : 0 < b) (hbR : b < R) :
    HasDerivAt (fun t => soninPrimePolarSourceOperator P b t 1 hb (soninCutoffMonomial a 0))
      (-(((Real.exp R+1)/R:ℝ):ℂ) • soninGroundEntry a R) R := by
  let f : ℝ → SoninL2 := fun u => (countDensity u:ℂ) • soninGroundEntry a u
  have hc : ContinuousAt f R := by
    have hR0 : R ≠ 0 := ne_of_gt (hb.trans hbR)
    have hd : ContinuousAt (fun u => (countDensity u:ℂ)) R := by
      unfold countDensity
      fun_prop
    exact hd.smul (entry_continuous a).continuousAt
  have hm : StronglyMeasurable f := by
    have hd : Measurable (fun u => (countDensity u:ℂ)) := by
      unfold countDensity
      fun_prop
    exact hd.stronglyMeasurable.smul (entry_continuous a).stronglyMeasurable
  have hi : IntervalIntegrable f volume b R :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hbR.le).mpr
      (density_entry_integrable a b R hb)
  have hd := (intervalIntegral.integral_hasDerivAt_right hi hm.stronglyMeasurableAtFilter hc).const_sub
    (∑ p ∈ P, soninGroundEntry a (Real.log (p:ℝ)))
  have heq : (fun t => soninPrimePolarSourceOperator P b t 1 hb (soninCutoffMonomial a 0)) =ᶠ[𝓝 R]
      (fun t => (∑ p ∈ P, soninGroundEntry a (Real.log (p:ℝ))) - ∫ u in b..t, f u) := by
    filter_upwards [eventually_gt_nhds hbR] with t ht
    rw [source_entries, intervalIntegral.integral_of_le ht.le, integral_Icc_eq_integral_Ioc]
  simpa only [f, countDensity, neg_smul] using hd.congr_of_eventuallyEq heq

private theorem real_inner_ground (f g : SoninL2) :
    inner ℝ f g = (inner ℂ f g).re := by
  exact integral_re (L2.integrable_inner (𝕜 := ℂ) f g)

/-- Exact continuous polar work on ground energy; its sign remains the
sign of the actual cumulative discrepancy, with no dissipativity premise. -/
theorem hasDerivAt_soninPrimePolar_ground_energy_polar (a : ℝ) (ha : 0 ≤ a)
    (P : Finset Nat.Primes) (b R : ℝ) (hb : 0 < b) (hbR : b < R)
    (hP : ∀ p ∈ P, Real.log (p:ℝ) ≤ R) :
    HasDerivAt (fun t => ‖soninPrimePolarSourceOperator P b t 1 hb (soninCutoffMonomial a 0)‖^2)
      (-4*a*((1+Real.exp (-R))/R)*soninPrimePolarGroundCumulative P b R R) R := by
  have hd := (hasDerivAt_soninPrimePolar_ground_polar a P b R hb hbR).norm_sq
  apply hd.congr_deriv
  rw [real_inner_ground, inner_smul_right,
    inner_soninPrimePolar_ground_entry a ha P b R R hb hP le_rfl]
  change 2*((-(((Real.exp R+1)/R:ℝ):ℂ)) *
    ((2*a*soninPrimePolarGroundCumulative P b R R*Real.exp (-R):ℝ):ℂ)).re = _
  rw [← Complex.ofReal_neg, ← Complex.ofReal_mul, Complex.ofReal_re]
  have he := density_exp_neg R
  unfold countDensity at he
  calc
    _ = -4*a*(((Real.exp R+1)/R)*Real.exp (-R))*soninPrimePolarGroundCumulative P b R R := by ring
    _ = _ := by rw [he]

/-- Strong continuity of the original entering ground vector. -/
theorem continuous_soninGroundEntry (a : ℝ) : Continuous (soninGroundEntry a) :=
  entry_continuous a

/-- The original polar integrand in exact ground-counting coordinates. -/
theorem soninGroundEntry_polar_density (a u : ℝ) :
    soninLogPolarDensity u • rayDilate (Real.exp u) (soninCutoffMonomial a 0) =
      (((Real.exp u + 1) / u : ℝ) : ℂ) • soninGroundEntry a u :=
  density_entry a u

end RHTower
