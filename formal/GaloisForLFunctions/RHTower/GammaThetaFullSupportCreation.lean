import GaloisForLFunctions.RHTower.GammaThetaFullSupportSource

/-!
# Forward creation on the completed Gamma--theta source

Every prime creator acts on the simultaneously completed source. Its exact occupied-support
equation retains the chosen complex prime amplitude. The source is independent of Xi zeros;
the equation does not supply inverse-preimage covariance or a prime-Poisson intertwiner.
-/

open Complex Real MeasureTheory Set Filter
open scoped BigOperators ENNReal LinearPMap Topology

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

theorem exp_mul_jasGammaThetaFullSourceFun
    (x : ℝ) (z : ℂ) (tau : Nat.Primes → ℝ) (r : ℕ)
    (v : JASGammaThetaSupport × ℝ) :
    (Real.exp v.2 : ℂ) * jasGammaThetaFullSourceFun x z tau r v =
      jasGammaThetaFullSourceFun x z tau (r + 1) v := by
  have he : Real.exp v.2 * Real.exp (((v.1.card : ℝ) + (r : ℝ)) * v.2) =
      Real.exp (((v.1.card : ℝ) + ((r + 1 : ℕ) : ℝ)) * v.2) := by
    rw [← Real.exp_add]
    congr 1
    push_cast
    ring
  unfold jasGammaThetaFullSourceFun
  rw [← he]
  push_cast
  ring

theorem jasGammaThetaEnergy_mul_fullSourceFun
    (x : ℝ) (z : ℂ) (tau : Nat.Primes → ℝ) (r : ℕ) (p : Nat.Primes)
    (v : JASGammaThetaSupport × ℝ) :
    (jasGammaThetaCreationEnergy x p v : ℂ) * jasGammaThetaFullSourceFun x z tau r v =
      (jasGammaBooleanCreationEnergy x p v.1 : ℂ) *
        jasGammaThetaFullSourceFun x z tau (r + 1) v := by
  classical
  by_cases hp : p ∈ v.1
  · simp [jasGammaThetaCreationEnergy, jasGammaBooleanCreationEnergy, hp]
  · simp only [jasGammaThetaCreationEnergy, jasGammaBooleanCreationEnergy, if_neg hp,
      Complex.ofReal_mul]
    rw [mul_assoc, exp_mul_jasGammaThetaFullSourceFun]

/-- Every unbounded native creator admits the completed source: the next actual theta grade
pays for multiplication by `exp(y)`, while the support gain has a uniform arithmetic ceiling. -/
theorem jasGammaThetaFullSource_mem_creationDomain
    {x : ℝ} (hx : 0 < x) (z : ℂ) (tau : Nat.Primes → ℝ) (r : ℕ) (p : Nat.Primes) :
    jasGammaThetaFullSource hx z tau r ∈ (jasGammaThetaCreation x p).domain := by
  change MemLp (fun v => (jasGammaThetaCreationEnergy x p v : ℂ) *
    (jasGammaThetaFullSource hx z tau r : JASGammaThetaSupport × ℝ → ℂ) v) 2
      ((Measure.count : Measure JASGammaThetaSupport).prod (volume : Measure ℝ))
  have hraw : MemLp (fun v => (jasGammaThetaCreationEnergy x p v : ℂ) *
      jasGammaThetaFullSourceFun x z tau r v) 2
      ((Measure.count : Measure JASGammaThetaSupport).prod (volume : Measure ℝ)) := by
    have hm : Measurable (fun v => (jasGammaThetaCreationEnergy x p v : ℂ) *
        jasGammaThetaFullSourceFun x z tau r v) :=
      ((measurable_jasGammaThetaCreationEnergy x p).complex_ofReal).mul
        (measurable_jasGammaThetaFullSourceFun x z tau r)
    apply (memLp_jasGammaThetaFullSourceFun hx z tau (r + 1)).of_le_mul
      (c := ((p : ℝ) + 1)⁻¹) hm.aestronglyMeasurable
    refine Eventually.of_forall fun v => ?_
    rw [jasGammaThetaEnergy_mul_fullSourceFun, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (jasGammaBooleanCreationEnergy_bounds hx p v.1).1]
    exact mul_le_mul_of_nonneg_right (jasGammaBooleanCreationEnergy_bounds hx p v.1).2
      (norm_nonneg _)
  apply (memLp_congr_ae ?_).mpr hraw
  filter_upwards [jasGammaThetaFullSource_coeFn hx z tau r] with v hv
  rw [hv]

def jasGammaThetaFullSourceDomain
    {x : ℝ} (hx : 0 < x) (z : ℂ) (tau : Nat.Primes → ℝ) (r : ℕ) (p : Nat.Primes) :
    (jasGammaThetaCreation x p).domain :=
  ⟨jasGammaThetaFullSource hx z tau r,
    jasGammaThetaFullSource_mem_creationDomain hx z tau r p⟩

/-- Exact insertion identity on every unoccupied support, with the original complex prime phase. -/
theorem jasGammaThetaFullSourceFun_insert
    {x : ℝ} (hx : 0 < x) (z : ℂ) (tau : Nat.Primes → ℝ) (r : ℕ)
    (p : Nat.Primes) (P : JASGammaThetaSupport) (hp : p ∉ P) (y : ℝ) :
    jasGammaThetaPrimeAmplitude z tau p *
        ((jasGammaThetaCreationEnergy x p (P, y) : ℂ) *
          jasGammaThetaFullSourceFun x z tau r (P, y)) =
      jasGammaThetaFullSourceFun x z tau r (insert p P, y) := by
  classical
  have he : Real.exp y * Real.exp (((P.card : ℝ) + (r : ℝ)) * y) =
      Real.exp (((P.card : ℝ) + 1 + (r : ℝ)) * y) := by
    rw [← Real.exp_add]
    congr 1
    ring
  simp only [jasGammaThetaFullSourceFun, jasGammaThetaCreationEnergy, if_neg hp,
    Finset.prod_insert hp, Finset.card_insert_of_notMem hp, Nat.cast_add, Nat.cast_one,
    jasGammaSynchronizedLcmWeight_insert_boolean hx]
  rw [← he]
  push_cast
  ring

/-- Coordinate formula for the native closed creator on its entire domain. -/
theorem jasGammaThetaCreation_coeFn (x : ℝ) (p : Nat.Primes)
    (f : (jasGammaThetaCreation x p).domain) :
    (jasGammaThetaCreation x p f : JASGammaThetaSupport × ℝ → ℂ) =ᵐ[
      (Measure.count : Measure JASGammaThetaSupport).prod (volume : Measure ℝ)]
      fun v => (jasGammaThetaCreationEnergy x p (jasGammaSupportToggle p v.1, v.2) : ℂ) *
        (f : JASGammaThetaL2) (jasGammaSupportToggle p v.1, v.2) := by
  let g : (maximalRealL2Mul
      ((Measure.count : Measure JASGammaThetaSupport).prod (volume : Measure ℝ))
      (jasGammaThetaCreationEnergy x p)).domain := f
  change (Lp.compMeasurePreserving (jasGammaThetaToggleMeasurableEquiv p)
      (jasGammaThetaToggle_measurePreserving p)
      (maximalRealL2Mul _ (jasGammaThetaCreationEnergy x p) g) :
        JASGammaThetaSupport × ℝ → ℂ) =ᵐ[_] _
  filter_upwards [Lp.coeFn_compMeasurePreserving
      (maximalRealL2Mul _ (jasGammaThetaCreationEnergy x p) g)
      (jasGammaThetaToggle_measurePreserving p),
    (maximalRealL2Mul_apply_ae _ (jasGammaThetaCreationEnergy x p) g).comp_tendsto
      (jasGammaThetaToggle_measurePreserving p).quasiMeasurePreserving.tendsto_ae]
    with v hv hm
  exact hv.trans hm

/-- Forward source covariance, simultaneously at every prime, in the literal completed carrier.
The identity uses multiplication by the prime amplitude, so it also holds at formation zero. -/
theorem jasGammaThetaFullSource_creation_covariance
    {x : ℝ} (hx : 0 < x) (z : ℂ) (tau : Nat.Primes → ℝ) (r : ℕ) (p : Nat.Primes) :
    (fun v => jasGammaThetaPrimeAmplitude z tau p *
      (jasGammaThetaCreation x p (jasGammaThetaFullSourceDomain hx z tau r p) :
        JASGammaThetaSupport × ℝ → ℂ) v) =ᵐ[
      (Measure.count : Measure JASGammaThetaSupport).prod (volume : Measure ℝ)]
      fun v => if p ∈ v.1 then jasGammaThetaFullSourceFun x z tau r v else 0 := by
  classical
  filter_upwards [jasGammaThetaCreation_coeFn x p (jasGammaThetaFullSourceDomain hx z tau r p),
    (jasGammaThetaFullSource_coeFn hx z tau r).comp_tendsto
      (jasGammaThetaToggle_measurePreserving p).quasiMeasurePreserving.tendsto_ae] with v hv hs
  rw [hv]
  change jasGammaThetaPrimeAmplitude z tau p *
      ((jasGammaThetaCreationEnergy x p (jasGammaSupportToggle p v.1, v.2) : ℂ) *
        (jasGammaThetaFullSource hx z tau r : JASGammaThetaSupport × ℝ → ℂ)
          (jasGammaSupportToggle p v.1, v.2)) = _
  change (jasGammaThetaFullSource hx z tau r : JASGammaThetaSupport × ℝ → ℂ)
      (jasGammaSupportToggle p v.1, v.2) =
      jasGammaThetaFullSourceFun x z tau r (jasGammaSupportToggle p v.1, v.2) at hs
  rw [hs]
  by_cases hp : p ∈ v.1
  · rw [if_pos hp, jasGammaSupportToggle_apply, if_pos hp]
    simpa only [Finset.insert_erase hp] using
      jasGammaThetaFullSourceFun_insert hx z tau r p (v.1.erase p)
        (by simp) v.2
  · rw [if_neg hp, jasGammaSupportToggle_apply, if_neg hp]
    simp only [jasGammaThetaCreationEnergy, Finset.mem_insert_self, if_true, Complex.ofReal_zero,
      zero_mul, mul_zero]

/-- Literal finite-prime alphabet cutoff, retaining every compound over that alphabet. -/
def jasGammaThetaSupportCutoffSymbol (N : ℕ) (v : JASGammaThetaSupport × ℝ) : ℂ :=
  if ∀ p ∈ v.1, (p : ℕ) ≤ N then 1 else 0

theorem measurable_jasGammaThetaSupportCutoffSymbol (N : ℕ) :
    Measurable (jasGammaThetaSupportCutoffSymbol N) := by
  have hm := measurable_of_countable
    (fun P : JASGammaThetaSupport => if ∀ p ∈ P, (p : ℕ) ≤ N then (1 : ℂ) else 0)
  exact hm.comp measurable_fst

theorem norm_jasGammaThetaSupportCutoffSymbol_le (N : ℕ) (v : JASGammaThetaSupport × ℝ) :
    ‖jasGammaThetaSupportCutoffSymbol N v‖ ≤ 1 := by
  unfold jasGammaThetaSupportCutoffSymbol
  split_ifs <;> norm_num

def jasGammaThetaSupportCutoff (N : ℕ) : JASGammaThetaL2 →L[ℂ] JASGammaThetaL2 :=
  lpBoundedMulCLM (measurable_jasGammaThetaSupportCutoffSymbol N) zero_le_one
    (norm_jasGammaThetaSupportCutoffSymbol_le N)

/-- Finite prime alphabets exhaust the actual Hilbert carrier in norm, preserving all
unbounded theta grades already admitted in the vector. -/
theorem tendsto_jasGammaThetaSupportCutoff (f : JASGammaThetaL2) :
    Tendsto (fun N : ℕ => jasGammaThetaSupportCutoff N f) atTop (𝓝 f) := by
  have hpt (v : JASGammaThetaSupport × ℝ) :
      Tendsto (fun N : ℕ => jasGammaThetaSupportCutoffSymbol N v) atTop (𝓝 (1 : ℂ)) := by
    apply Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [eventually_ge_atTop (v.1.sup fun p => (p : ℕ))] with N hN
    have hbound : ∀ p ∈ v.1, (p : ℕ) ≤ N := fun p hp =>
      (Finset.le_sup (f := fun q : Nat.Primes => (q : ℕ)) hp).trans hN
    simp only [jasGammaThetaSupportCutoffSymbol, if_pos hbound]
  have h := tendsto_lpBoundedMulCLM_apply
    (φ := fun N v => jasGammaThetaSupportCutoffSymbol N v)
    (ψ := fun _ : JASGammaThetaSupport × ℝ => (1 : ℂ))
    measurable_jasGammaThetaSupportCutoffSymbol measurable_const zero_le_one
    norm_jasGammaThetaSupportCutoffSymbol_le (fun _ => by simp) hpt f
  have hid : lpBoundedMulCLM (p := 2)
      (μ := (Measure.count : Measure JASGammaThetaSupport).prod (volume : Measure ℝ))
      (φ := fun _ : JASGammaThetaSupport × ℝ => (1 : ℂ)) measurable_const zero_le_one
      (fun _ => by simp) f = f := by
    apply Lp.ext
    filter_upwards [lpBoundedMulCLM_coeFn (p := 2)
      (μ := (Measure.count : Measure JASGammaThetaSupport).prod (volume : Measure ℝ))
      (φ := fun _ : JASGammaThetaSupport × ℝ => (1 : ℂ)) measurable_const zero_le_one
      (fun _ => by simp) f] with v hv
    simpa only [one_mul] using hv
  simpa only [jasGammaThetaSupportCutoff, hid] using h

theorem jasGammaThetaFullSource_cutoff_coeFn
    {x : ℝ} (hx : 0 < x) (z : ℂ) (tau : Nat.Primes → ℝ) (r N : ℕ) :
    (jasGammaThetaSupportCutoff N (jasGammaThetaFullSource hx z tau r) :
      JASGammaThetaSupport × ℝ → ℂ) =ᵐ[
      (Measure.count : Measure JASGammaThetaSupport).prod (volume : Measure ℝ)]
      fun v => if ∀ p ∈ v.1, (p : ℕ) ≤ N then jasGammaThetaFullSourceFun x z tau r v else 0 := by
  filter_upwards [lpBoundedMulCLM_coeFn (p := 2)
      (measurable_jasGammaThetaSupportCutoffSymbol N) zero_le_one
      (norm_jasGammaThetaSupportCutoffSymbol_le N) (jasGammaThetaFullSource hx z tau r),
    jasGammaThetaFullSource_coeFn hx z tau r] with v hv hs
  calc
    (jasGammaThetaSupportCutoff N (jasGammaThetaFullSource hx z tau r) :
        JASGammaThetaSupport × ℝ → ℂ) v =
        jasGammaThetaSupportCutoffSymbol N v *
          (jasGammaThetaFullSource hx z tau r : JASGammaThetaSupport × ℝ → ℂ) v := hv
    _ = jasGammaThetaSupportCutoffSymbol N v * jasGammaThetaFullSourceFun x z tau r v :=
      congrArg (fun a => jasGammaThetaSupportCutoffSymbol N v * a) hs
    _ = _ := by
      unfold jasGammaThetaSupportCutoffSymbol
      split_ifs <;> simp

/-- Source-derived norm exhaustion, without a cutoff-admission premise. -/
theorem tendsto_jasGammaThetaFullSource_primeCutoffs
    {x : ℝ} (hx : 0 < x) (z : ℂ) (tau : Nat.Primes → ℝ) (r : ℕ) :
    Tendsto (fun N : ℕ => jasGammaThetaSupportCutoff N (jasGammaThetaFullSource hx z tau r))
      atTop (𝓝 (jasGammaThetaFullSource hx z tau r)) :=
  tendsto_jasGammaThetaSupportCutoff _

end

end RHTower
