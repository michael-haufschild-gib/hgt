import GaloisForLFunctions.ExceptionalLayerTheory.TheBoundaryTraceOfTheTwoIntervalPrimeRadius
import GaloisForLFunctions.ZeroConfigurationGeometry.TheBoundaryTraceDeterminesTheTopZeros
import GaloisForLFunctions.HTGeometry.LinearOdeBohrSpectrum

/-!
# A quartet radius forces commensurable extremal ordinates

A real almost-periodic function with periodic absolute value can be approximated
uniformly by periodic functions whose periods are integer multiples of that
period. Applied to the extremal prime increment, this puts every top ordinate
in the rational span of the trial frequency, even for an infinite top layer.
-/

noncomputable section
open Filter Topology Complex RHTower
open GaloisForLFunctions.ZeroConfigurationGeometry
open _root_.HTGeometry

namespace GaloisForLFunctions.ExceptionalLayerTheory

/-- Two lattice translates fall in the same ball of a finite cover of the orbit. -/
private theorem lattice_almost_period {f : ℝ → ℝ} (hf : HasTotallyBoundedOrbit f)
    (p : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, 0 < n ∧ ∀ t : ℝ, |f (t + n*p) - f t| ≤ ε := by
  classical
  obtain ⟨S, _, hS⟩ := hf (ε/2) (half_pos hε)
  have hs (i : ℕ) : ∃ s : S, ∀ x, ‖f (x + i*p) - f (x+s)‖ ≤ ε/2 := by
    obtain ⟨s, hs, h⟩ := hS (i*p)
    exact ⟨⟨s,hs⟩,h⟩
  choose a ha using hs
  obtain ⟨i, j, hij, heq⟩ := Finite.exists_ne_map_eq_of_infinite a
  obtain ⟨i,j,hlt,heq⟩ : ∃ i j : ℕ, i < j ∧ a i = a j := by
    rcases lt_or_gt_of_ne hij with h | h
    · exact ⟨i,j,h,heq⟩
    · exact ⟨j,i,h,heq.symm⟩
  refine ⟨j-i, Nat.sub_pos_of_lt hlt, fun t => ?_⟩
  let x := t - i*p
  have hi := ha i x
  have hj := ha j x
  rw [heq] at hi
  have hab := abs_sub_le (f (x+j*p)) (f (x+a j)) (f (x+i*p))
  rw [abs_sub_comm (f (x+a j))] at hab
  rw [Nat.cast_sub hlt.le, show t+((j:ℝ)-i)*p = x+j*p by dsimp [x]; ring,
    show t = x+i*p by dsimp [x]; ring] 
  change |f (x+j*p) - f (x+i*p)| ≤ ε
  exact hab.trans ((add_le_add hj hi).trans_eq (add_halves ε))

private def trim (δ y : ℝ) := max (y-δ) 0 - max (-y-δ) 0

private theorem periodic_approximant {f : ℝ → ℝ} (hc : Continuous f)
    (ha : IsBohrAlmostPeriodic f) {p : ℝ} (hp : Function.Periodic (fun t => |f t|) p)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ (n : ℕ) (g : ℝ → ℝ), 0 < n ∧ Continuous g ∧ Function.Periodic g (n*p) ∧
      ∀ t, |f t - g t| ≤ δ := by
  obtain ⟨n,hn,hshift⟩ := lattice_almost_period
    (hasTotallyBoundedOrbit_of_isBohrAlmostPeriodic hc ha) p hδ
  refine ⟨n,fun t => trim δ (f t), hn, ?_, ?_, ?_⟩
  · unfold trim
    fun_prop
  · intro t
    have he : |f (t+n*p)| = |f t| := hp.nat_mul n t
    rcases abs_eq_abs.mp he with he | he
    · rw [he]
    · have hd := hshift t
      rw [he] at hd
      have hle := abs_le.mp hd
      change trim δ (f (t+n*p)) = trim δ (f t)
      rw [he]
      simp only [trim, neg_neg, max_eq_right (show f t-δ ≤ 0 by linarith only [hle.1, hδ]),
        max_eq_right (show -f t-δ ≤ 0 by linarith only [hle.2, hδ])]
  · intro t
    dsimp only [trim]
    rw [abs_le]
    simp only [max_def]
    split_ifs <;> constructor <;> linarith

/-- Every nonzero frequency of a real almost-periodic function with periodic
absolute value makes an integral number of turns on some multiple of the period. -/
private theorem frequency_of_periodic_abs {f : ℝ → ℝ} (hc : Continuous f)
    (ha : IsBohrAlmostPeriodic f) {p : ℝ} (hp : 0 < p)
    (hper : Function.Periodic (fun t => |f t|) p) {ω : ℝ}
    (hω : bohrCoefficient (fun t => (f t : ℂ)) ω ≠ 0) :
    ∃ n : ℕ, 0 < n ∧ expChar ω (n*p) = 1 := by
  let c := bohrCoefficient (fun t => (f t : ℂ)) ω
  have hc0 : 0 < ‖c‖ := norm_pos_iff.mpr hω
  obtain ⟨n,g,hn,hg,hgper,hclose⟩ := periodic_approximant hc ha hper (half_pos hc0)
  have hperC : Function.Periodic (fun t => (g t : ℂ)) (n*p) :=
    fun t => congrArg Complex.ofReal (hgper t)
  have hgC := Complex.continuous_ofReal.comp hg
  have hga := isBohrAlmostPeriodic_of_periodic (mul_pos (Nat.cast_pos.mpr hn) hp) hperC
  have hfa : IsBohrAlmostPeriodic (fun t => (f t : ℂ)) := by
    simpa only [IsBohrAlmostPeriodic, ← Complex.ofReal_sub, Complex.norm_real] using ha
  have hb := norm_bohrCoefficient_sub_le (Complex.continuous_ofReal.comp hc) hfa hgC hga
    (fun t => by simpa only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
                 using hclose t) ω
  let b := bohrCoefficient (fun t => (g t : ℂ)) ω
  have hb0 : b ≠ 0 := by
    change ‖c-b‖ ≤ ‖c‖/2 at hb
    intro hz
    rw [hz, sub_zero] at hb
    linarith only [hb,hc0]
  have he := bohrCoefficient_comp_add_const hgC hga ((n:ℝ)*p) ω
  have htrans : (fun t => (g (t+n*p) : ℂ)) = fun t => (g t : ℂ) := funext hperC
  rw [htrans] at he
  refine ⟨n,hn, mul_right_cancel₀ hb0 ?_⟩
  exact he.symm.trans (one_mul b).symm

/-- The multiplier for a normalized increment never vanishes at a real frequency
when the forward scale is greater than one. -/
private theorem boundaryStep_coefficient {β h : ℝ} (hβ : 1/2 < β) (hh : 0 < h) :
    let D := boundaryStep β h (primeErrorBoundaryTrace β)
    Continuous D ∧ IsBohrAlmostPeriodic D ∧
      ∀ q : XiZeroCopy, (q.1 : ℂ).re = β →
        bohrCoefficient (fun t => (D t : ℂ)) (xiCopyOrdinate q) ≠ 0 := by
  intro D
  let F := fun t => (primeErrorBoundaryTrace β t : ℂ)
  let A := Real.exp (β*h)
  have hF : F = expSeriesCarrier (primeErrorBoundaryAmplitude β) xiCopyOrdinate :=
    funext (ofReal_primeErrorBoundaryTrace β)
  have hc : Continuous F := hF ▸ continuous_expSeriesCarrier (summable_primeErrorBoundaryAmplitude hβ) _
  have ha : IsBohrAlmostPeriodic F := hF ▸ isBohrAlmostPeriodic_expSeriesCarrier
    (summable_primeErrorBoundaryAmplitude hβ) _
  let G := fun t => (A:ℂ)*F (t+h)
  have hsc := hc.comp (continuous_id.add continuous_const : Continuous (fun t : ℝ => t+h))
  have hsa := isBohrAlmostPeriodic_comp_add_const ha h
  have hgc : Continuous G := continuous_const.mul hsc
  have hga : IsBohrAlmostPeriodic G := isBohrAlmostPeriodic_const_mul _ hsa
  have he : (fun t => (D t : ℂ)) = fun t => G t - F t := by
    funext t; simp only [D, boundaryStep, G, A, F, Complex.ofReal_sub, Complex.ofReal_mul]
  have hdc : Continuous (fun t => (D t : ℂ)) := he ▸ hgc.sub hc
  have hda : IsBohrAlmostPeriodic (fun t => (D t : ℂ)) :=
    he ▸ isBohrAlmostPeriodic_sub hgc hga hc ha
  refine ⟨Complex.continuous_re.comp hdc, ?_, fun q hq => ?_⟩
  · simpa only [IsBohrAlmostPeriodic, ← Complex.ofReal_sub, Complex.norm_real] using hda
  let ω := xiCopyOrdinate q
  have hcoef : bohrCoefficient (fun t => (D t : ℂ)) ω =
      ((A:ℂ)*expChar ω h - 1)*bohrCoefficient F ω := by
    rw [he]
    have hsub : bohrCoefficient (fun t => G t - F t) ω = bohrCoefficient G ω - bohrCoefficient F ω := by
      simp only [bohrCoefficient, sub_mul]
      exact bohrMean_sub (hgc.mul (continuous_bohrChar ω)) (isBohrAlmostPeriodic_mul_bohrChar hgc hga ω)
        (hc.mul (continuous_bohrChar ω)) (isBohrAlmostPeriodic_mul_bohrChar hc ha ω)
    rw [hsub, show bohrCoefficient G ω = (A:ℂ)*bohrCoefficient (fun t => F (t+h)) ω from
      bohrCoefficient_const_mul _ hsc hsa ω, bohrCoefficient_comp_add_const hc ha]
    ring
  rw [hcoef]
  refine mul_ne_zero (sub_ne_zero.mpr fun hz => ?_) (bohrCoefficient_boundary_ne_zero hβ q hq)
  have heq := congrArg norm hz
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    norm_expChar, mul_one, norm_one, A] at heq
  exact (Real.one_lt_exp_iff.mpr (mul_pos (by linarith only [hβ]) hh)).ne' heq

/-- If the actual radius has square-root discrepancy, each attained extremal
ordinate is a rational multiple of the trial frequency. No separation of the
extremal line or finiteness of its zeros is needed. -/
theorem top_ordinates_commensurable_of_bounded_thetaRadial {γ : ℝ} {m : ℕ}
    (hΘ : 1/2 < zetaZeroAbscissa) (hγ : γ ≠ 0)
    (hb : ¬ IsLogSqrtSqUnbounded (thetaRadialDiscrepancy zetaZeroAbscissa γ m)) :
    ∀ q : XiZeroCopy, (q.1 : ℂ).re = zetaZeroAbscissa →
      ∃ r : ℚ, (q.1 : ℂ).im = (r:ℝ)*|γ| := by
  let h := quarterPeriodStep γ
  let D := boundaryStep zetaZeroAbscissa h (primeErrorBoundaryTrace zetaZeroAbscissa)
  have hh : 0 < h := quarterPeriodStep_pos hγ
  obtain ⟨hc,ha,hfreq⟩ := boundaryStep_coefficient hΘ hh
  have hcircle := boundaryStep_circle_of_bounded_thetaRadial hΘ hb
  have hp : Function.Periodic (fun t => |D t|) (2*h) := by
    intro t
    have h1 := hcircle t
    have h2 := hcircle (t+h)
    change D t ^ 2 + D (t+h)^2 = _ at h1
    change D (t+h)^2 + D (t+h+h)^2 = _ at h2
    change |D (t+2*h)| = |D t|
    rw [show t+2*h = t+h+h by ring, ← sq_eq_sq₀ (abs_nonneg _) (abs_nonneg _), sq_abs, sq_abs]
    linarith only [h1,h2]
  intro q hq
  obtain ⟨n, hn, he⟩ := frequency_of_periodic_abs hc ha (by linarith only [hh]) hp (hfreq q hq)
  obtain ⟨k,hk⟩ := Complex.exp_eq_one_iff.mp he
  have him : xiCopyOrdinate q * ((n:ℝ)*(2*h)) = (k:ℝ)*(2*Real.pi) := by
    simpa [Complex.mul_im, Complex.mul_re] using congrArg Complex.im hk
  have hscale : (2*h)*|γ| = Real.pi := by
    dsimp only [h, quarterPeriodStep]
    field_simp [abs_ne_zero.mpr hγ]
  have hprod : xiCopyOrdinate q * (n:ℝ) = (2*(k:ℝ))*|γ| := by
    apply mul_right_cancel₀ Real.pi_ne_zero
    calc (xiCopyOrdinate q*n)*Real.pi = (xiCopyOrdinate q*((n:ℝ)*(2*h)))*|γ| := by
           linear_combination -(xiCopyOrdinate q*n) * hscale
      _ = ((2*(k:ℝ))*|γ|)*Real.pi := by rw [him]; ring
  refine ⟨(2*(k:ℚ))/n, ?_⟩
  push_cast
  rw [div_mul_eq_mul_div, eq_div_iff (Nat.cast_pos.mpr hn : 0 < (n:ℝ)).ne']
  exact hprod

/-- For every nonzero trial frequency, either its actual ordinary-prime
discrepancy is unbounded or the extremal line is inhabited and lies in the
rational span of the trial frequency. -/
theorem extremal_radial_exclusion_or_commensurable_top {γ : ℝ} {m : ℕ}
    (hΘ : 1/2 < zetaZeroAbscissa) (hγ : γ ≠ 0) (hm : 1 ≤ m) :
    IsLogSqrtSqUnbounded (thetaRadialDiscrepancy zetaZeroAbscissa γ m) ∨
      ((∃ q : XiZeroCopy, (q.1 : ℂ).re = zetaZeroAbscissa) ∧
       ∀ q : XiZeroCopy, (q.1 : ℂ).re = zetaZeroAbscissa →
         ∃ r : ℚ, (q.1 : ℂ).im = (r:ℝ)*|γ|) := by
  by_cases hb : IsLogSqrtSqUnbounded (thetaRadialDiscrepancy zetaZeroAbscissa γ m)
  · exact Or.inl hb
  refine Or.inr ⟨?_, top_ordinates_commensurable_of_bounded_thetaRadial hΘ hγ hb⟩
  by_contra! he
  exact hb (thetaRadial_unbounded_of_unattained hΘ he hγ hm)

/-- Two rationally independent ordinates on the extremal line exclude every
trial radius at the extremal abscissa, regardless of the zeros below it. -/
theorem thetaRadial_unbounded_of_incommensurable_top_pair
    (hΘ : 1/2 < zetaZeroAbscissa) (p q : XiZeroCopy)
    (hp : (p.1 : ℂ).re = zetaZeroAbscissa) (hq : (q.1 : ℂ).re = zetaZeroAbscissa)
    (hind : ∀ r : ℚ, xiCopyOrdinate p ≠ (r:ℝ)*xiCopyOrdinate q)
    {γ : ℝ} (hγ : γ ≠ 0) (m : ℕ) :
    IsLogSqrtSqUnbounded (thetaRadialDiscrepancy zetaZeroAbscissa γ m) := by
  by_contra hb
  have hf := top_ordinates_commensurable_of_bounded_thetaRadial hΘ hγ hb
  obtain ⟨a,ha⟩ := hf p hp
  obtain ⟨b,hb⟩ := hf q hq
  change xiCopyOrdinate p = _ at ha
  change xiCopyOrdinate q = _ at hb
  have hq0 : xiCopyOrdinate q ≠ 0 := by
    intro hz
    have hgt := four_lt_abs_xiCopyOrdinate q
    rw [hz, abs_zero] at hgt
    linarith only [hgt]
  have hb0 : (b:ℝ) ≠ 0 := fun hz => hq0 (by rw [hb,hz,zero_mul])
  apply hind (a/b)
  rw [Rat.cast_div, ha, hb]
  field_simp

#print axioms thetaRadial_unbounded_of_incommensurable_top_pair
#print axioms extremal_radial_exclusion_or_commensurable_top

end GaloisForLFunctions.ExceptionalLayerTheory
