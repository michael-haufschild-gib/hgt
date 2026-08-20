import GaloisForLFunctions.HTGeometry.SummableSpectrumScrewAlmostPeriodic
import GaloisForLFunctions.HTGeometry.BohrDerivativeSpectrum
import GaloisForLFunctions.HTGeometry.BohrMeanInvariance

/-!
# Exact Bohr coefficients of a summable screw spectrum

Uniform summability permits termwise extraction of every Bohr coefficient of a screw series,
without any frequency-separation assumption.  Equal and opposite frequencies collide by addition,
so the result retains their exact total mass.  We also isolate the rigidity fact that two
continuous Bohr almost-periodic asymptotes of the same source are identical.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

open _root_.HTGeometry
open GaloisForLFunctions

noncomputable section

variable {I : Type*} {a omega : I → ℝ}

/-- Contribution of one screw atom `a(1-cos(ωt))` to the Bohr coefficient at `λ`. -/
def screwAtomBohrCoefficient (a omega lam : ℝ) : ℂ :=
  (if (0 : ℝ) = lam then (a : ℂ) else 0) -
    (if omega = lam then ((a / 2 : ℝ) : ℂ) else 0) -
    (if -omega = lam then ((a / 2 : ℝ) : ℂ) else 0)

theorem complex_screw_atom_eq_expChar (a omega t : ℝ) :
    ((a * (1 - Real.cos (omega * t)) : ℝ) : ℂ) =
      (a : ℂ) * expChar 0 t -
        ((a / 2 : ℝ) : ℂ) * expChar omega t -
        ((a / 2 : ℝ) : ℂ) * expChar (-omega) t := by
  simp only [expChar, zero_mul, Complex.ofReal_zero, Complex.exp_zero, mul_one]
  rw [Complex.exp_mul_I, Complex.exp_mul_I]
  push_cast
  simp only [neg_mul]
  apply Complex.ext <;> simp <;> ring

/-- Exact coefficient of one screw atom, including the zero-frequency degeneracy. -/
theorem bohrCoefficient_complex_screw_atom (a omega lam : ℝ) :
    bohrCoefficient
        (fun t : ℝ => ((a * (1 - Real.cos (omega * t)) : ℝ) : ℂ)) lam =
      screwAtomBohrCoefficient a omega lam := by
  let cf : Fin 3 → ℂ := fun i =>
    if i = 0 then (a : ℂ) else if i = 1 then -((a / 2 : ℝ) : ℂ)
      else -((a / 2 : ℝ) : ℂ)
  let mu : Fin 3 → ℝ := fun i =>
    if i = 0 then 0 else if i = 1 then omega else -omega
  have hfun :
      (fun t : ℝ => ((a * (1 - Real.cos (omega * t)) : ℝ) : ℂ)) =
        fun t : ℝ => ∑ i ∈ Finset.univ, cf i * expChar (mu i) t := by
    funext t
    rw [complex_screw_atom_eq_expChar]
    simp [Fin.sum_univ_three, cf, mu]
    ring
  rw [hfun, bohrCoefficient_sum_expChar]
  simp [Fin.sum_univ_three, cf, mu, screwAtomBohrCoefficient]
  split_ifs <;> ring

/-- Real-to-complex scalar inclusion preserves Bohr almost periodicity. -/
theorem isBohrAlmostPeriodic_ofReal {f : ℝ → ℝ}
    (hf : IsBohrAlmostPeriodic f) :
    IsBohrAlmostPeriodic (fun t => (f t : ℂ)) := by
  intro ε hε
  obtain ⟨L, hL, hdense⟩ := hf ε hε
  refine ⟨L, hL, fun b => ?_⟩
  obtain ⟨τ, hτmem, hτ⟩ := hdense b
  refine ⟨τ, hτmem, fun x => ?_⟩
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  simpa [Real.norm_eq_abs] using hτ x

theorem complex_screw_atom_isBohrAlmostPeriodic (a omega : ℝ) :
    IsBohrAlmostPeriodic
      (fun t : ℝ => ((a * (1 - Real.cos (omega * t)) : ℝ) : ℂ)) := by
  let cf : Fin 3 → ℂ := fun i =>
    if i = 0 then (a : ℂ) else if i = 1 then -((a / 2 : ℝ) : ℂ)
      else -((a / 2 : ℝ) : ℂ)
  let mu : Fin 3 → ℝ := fun i =>
    if i = 0 then 0 else if i = 1 then omega else -omega
  have hfun :
      (fun t : ℝ => ((a * (1 - Real.cos (omega * t)) : ℝ) : ℂ)) =
        fun t : ℝ => ∑ i ∈ Finset.univ, cf i * expChar (mu i) t := by
    funext t
    rw [complex_screw_atom_eq_expChar]
    simp [Fin.sum_univ_three, cf, mu]
    ring
  rw [hfun]
  exact isBohrAlmostPeriodic_sum Finset.univ
    (fun i _ => continuous_const.mul (continuous_expChar (mu i)))
    (fun i _ => isBohrAlmostPeriodic_const_mul _
      (isBohrAlmostPeriodic_expChar (mu i)))

theorem summable_screwAtomBohrCoefficient
    (hpos : ∀ i, 0 ≤ a i) (hsum : Summable a) (lam : ℝ) :
    Summable (fun i => screwAtomBohrCoefficient (a i) (omega i) lam) := by
  apply Summable.of_norm_bounded (hsum.mul_left 2)
  intro i
  let x : ℂ := if (0 : ℝ) = lam then (a i : ℂ) else 0
  let y : ℂ := if omega i = lam then ((a i / 2 : ℝ) : ℂ) else 0
  let z : ℂ := if -omega i = lam then ((a i / 2 : ℝ) : ℂ) else 0
  have hx : ‖x‖ ≤ a i := by
    dsimp only [x]
    split_ifs
    · simp [Complex.norm_real, abs_of_nonneg (hpos i)]
    · simpa using hpos i
  have hy : ‖y‖ ≤ a i / 2 := by
    dsimp only [y]
    have hhalf : 0 ≤ a i / 2 := div_nonneg (hpos i) (by norm_num)
    split_ifs
    · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hhalf]
    · simpa using hhalf
  have hz : ‖z‖ ≤ a i / 2 := by
    dsimp only [z]
    have hhalf : 0 ≤ a i / 2 := div_nonneg (hpos i) (by norm_num)
    split_ifs
    · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hhalf]
    · simpa using hhalf
  change ‖x - y - z‖ ≤ 2 * a i
  rw [show x - y - z = (x + -y) + -z by ring]
  calc
    ‖(x + -y) + -z‖ ≤ ‖x + -y‖ + ‖-z‖ := norm_add_le _ _
    _ ≤ (‖x‖ + ‖-y‖) + ‖-z‖ := by
      gcongr
      exact norm_add_le _ _
    _ = (‖x‖ + ‖y‖) + ‖z‖ := by rw [norm_neg, norm_neg]
    _ ≤ (a i + a i / 2) + a i / 2 := by gcongr
    _ = 2 * a i := by ring

/-- Exact termwise Bohr coefficient formula for a nonnegative summable screw spectrum. -/
theorem bohrCoefficient_complex_screwSeries
    (hpos : ∀ i, 0 ≤ a i) (hsum : Summable a) (lam : ℝ) :
    bohrCoefficient (fun t => (screwSeries a omega t : ℂ)) lam =
      ∑' i, screwAtomBohrCoefficient (a i) (omega i) lam := by
  classical
  let term : I → ℝ → ℝ := fun i t => a i * (1 - Real.cos (omega i * t))
  let F : Finset I → ℝ → ℂ := fun S t => ∑ i ∈ S, (term i t : ℂ)
  let f : ℝ → ℂ := fun t => (screwSeries a omega t : ℂ)
  have hterm : ∀ i t, ‖term i t‖ ≤ 2 * a i := by
    intro i t
    have hnonneg : 0 ≤ term i t :=
      mul_nonneg (hpos i) (sub_nonneg.mpr (Real.cos_le_one _))
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
    dsimp only [term]
    calc
      a i * (1 - Real.cos (omega i * t)) ≤ a i * 2 :=
        mul_le_mul_of_nonneg_left
          (by linarith [Real.neg_one_le_cos (omega i * t)]) (hpos i)
      _ = 2 * a i := by ring
  have huniformR : TendstoUniformly
      (fun S : Finset I => fun t : ℝ => ∑ i ∈ S, term i t)
      (screwSeries a omega) atTop := by
    change TendstoUniformly
      (fun S : Finset I => fun t : ℝ => ∑ i ∈ S, term i t)
      (fun t : ℝ => ∑' i, term i t) atTop
    exact tendstoUniformly_tsum (hsum.mul_left 2) hterm
  have huniform : TendstoUniformly F f atTop := by
    rw [Metric.tendstoUniformly_iff] at huniformR ⊢
    intro ε hε
    filter_upwards [huniformR ε hε] with S hS
    intro t
    change dist (screwSeries a omega t : ℂ) (∑ i ∈ S, (term i t : ℂ)) < ε
    rw [← Complex.ofReal_sum, dist_eq_norm, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs]
    simpa [Real.dist_eq] using hS t
  have hfc : Continuous f := by
    dsimp only [f]
    exact Complex.continuous_ofReal.comp (screwSeries_continuous hpos hsum)
  have hfa : IsBohrAlmostPeriodic f := by
    dsimp only [f]
    exact isBohrAlmostPeriodic_ofReal
      (isBohrAlmostPeriodic_screwSeries hpos hsum)
  have hFc : ∀ S, Continuous (F S) := by
    intro S
    exact continuous_finsetSum S (fun i _ => by
      dsimp only [F, term]
      fun_prop)
  have hFa : ∀ S, IsBohrAlmostPeriodic (F S) := by
    intro S
    exact isBohrAlmostPeriodic_sum S
      (fun i _ => by dsimp only [F, term]; fun_prop)
      (fun i _ => by
        dsimp only [F, term]
        exact complex_screw_atom_isBohrAlmostPeriodic (a i) (omega i))
  have hcoef : Tendsto (fun S : Finset I => bohrCoefficient (F S) lam)
      atTop (nhds (bohrCoefficient f lam)) := by
    refine Metric.tendsto_atTop.mpr fun ε hε => ?_
    have hhalf : 0 < ε / 2 := by linarith
    have hevent := (Metric.tendstoUniformly_iff.mp huniform) (ε / 2) hhalf
    rw [eventually_atTop] at hevent
    obtain ⟨S₀, hS₀⟩ := hevent
    refine ⟨S₀, fun S hSS => ?_⟩
    have hbound : ∀ t, ‖F S t - f t‖ ≤ ε / 2 := by
      intro t
      have ht := hS₀ S hSS t
      rw [norm_sub_rev]
      simpa [dist_eq_norm] using ht.le
    rw [dist_eq_norm]
    calc
      ‖bohrCoefficient (F S) lam - bohrCoefficient f lam‖ ≤ ε / 2 :=
        norm_bohrCoefficient_sub_le (hFc S) (hFa S) hfc hfa hbound lam
      _ < ε := by linarith
  have hfinite : ∀ S : Finset I,
      bohrCoefficient (F S) lam =
        ∑ i ∈ S, screwAtomBohrCoefficient (a i) (omega i) lam := by
    intro S
    rw [bohrCoefficient_finsetSum S
      (fun i => fun t : ℝ => (term i t : ℂ))
      (fun i _ => by dsimp only [term]; fun_prop)
      (fun i _ => by
        dsimp only [term]
        exact complex_screw_atom_isBohrAlmostPeriodic (a i) (omega i))]
    apply Finset.sum_congr rfl
    intro i _
    exact bohrCoefficient_complex_screw_atom (a i) (omega i) lam
  have hseries := (summable_screwAtomBohrCoefficient
    (a := a) (omega := omega) hpos hsum lam).hasSum
  exact tendsto_nhds_unique hcoef
    (hseries.congr' (Filter.Eventually.of_forall fun S => (hfinite S).symm))

/-- A Bohr almost-periodic function cannot decay at positive infinity unless it vanishes. -/
private theorem eq_zero_of_isBohrAlmostPeriodic_of_tendsto_zero
    {E : Type*} [NormedAddCommGroup E] {g : ℝ → E}
    (hap : IsBohrAlmostPeriodic g)
    (hzero : Tendsto g atTop (nhds 0)) :
    ∀ t, g t = 0 := by
  intro t
  by_contra hne
  have hnpos : 0 < ‖g t‖ := norm_pos_iff.mpr hne
  let ε : ℝ := ‖g t‖ / 3
  have hε : 0 < ε := by dsimp only [ε]; positivity
  obtain ⟨L, hL, hdense⟩ := hap ε hε
  obtain ⟨A, hA⟩ := Metric.tendsto_atTop.mp hzero ε hε
  obtain ⟨τ, hτmem, hτ⟩ := hdense (A - t)
  have htA : A ≤ t + τ := by linarith [hτmem.1]
  have htail := hA (t + τ) htA
  rw [dist_zero_right] at htail
  have hreturn : ‖g t - g (t + τ)‖ ≤ ε := by
    rw [norm_sub_rev]
    exact hτ t
  have hbound : ‖g t‖ < 2 * ε := calc
    ‖g t‖ = ‖(g t - g (t + τ)) + g (t + τ)‖ := by congr 1; abel
    _ ≤ ‖g t - g (t + τ)‖ + ‖g (t + τ)‖ := norm_add_le _ _
    _ < ε + ε := add_lt_add_of_le_of_lt hreturn htail
    _ = 2 * ε := by ring
  dsimp only [ε] at hbound
  linarith

/-- Two continuous Bohr almost-periodic asymptotes of one source are identical. -/
theorem asymptoticBohrModel_unique
    {source P Q : ℝ → ℝ}
    (hPc : Continuous P) (hPa : IsBohrAlmostPeriodic P)
    (hQc : Continuous Q) (hQa : IsBohrAlmostPeriodic Q)
    (hP : Tendsto (fun t => source t - P t) atTop (nhds 0))
    (hQ : Tendsto (fun t => source t - Q t) atTop (nhds 0)) :
    P = Q := by
  have hap : IsBohrAlmostPeriodic (fun t => P t - Q t) :=
    isBohrAlmostPeriodic_sub hPc hPa hQc hQa
  have hzero : Tendsto (fun t => P t - Q t) atTop (nhds 0) := by
    have h := hQ.sub hP
    simpa only [sub_zero] using h.congr' (Filter.Eventually.of_forall fun t => by ring)
  funext t
  exact sub_eq_zero.mp
    (eq_zero_of_isBohrAlmostPeriodic_of_tendsto_zero hap hzero t)

end

end GaloisForLFunctions.HTGeometry
