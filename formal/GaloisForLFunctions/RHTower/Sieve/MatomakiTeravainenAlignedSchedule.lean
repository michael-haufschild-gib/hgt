import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenGridFreePaperScale
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenAdjacentSchedule
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenFiniteIterationTermination

/-!
# Aligned natural schedule for repaired Matomäki--Teräväinen iteration

Using natural endpoints themselves as all recursive sieve cutoffs removes both rounding-spill
families.  Narrow shifted endpoint ratios retain the exact paper-width C3 geometry.
-/

namespace RHTower.Sieve

open Filter Topology Finset

noncomputable section

/-- Cutoff attached to an aligned natural endpoint. -/
def mtAlignedCutoff {t : ℕ} (endpoint : ℕ → ℕ) (j : Fin (t + 1)) : ℕ :=
  endpoint j.1

/-- Maximal shifted-natural step allowed by one multiplicative paper-width block, clipped at the
target endpoint. -/
def mtPaperAlignedEndpoint (z₀ z₁ : ℕ) (δ : ℝ) : ℕ → ℕ
  | 0 => z₀
  | j + 1 => min z₁
      (Nat.floor ((1 + δ) * ((mtPaperAlignedEndpoint z₀ z₁ δ j - 1 : ℕ) : ℝ)) + 1)

@[simp] theorem mtPaperAlignedEndpoint_zero (z₀ z₁ : ℕ) (δ : ℝ) :
    mtPaperAlignedEndpoint z₀ z₁ δ 0 = z₀ := rfl

@[simp] theorem mtPaperAlignedEndpoint_succ (z₀ z₁ : ℕ) (δ : ℝ) (j : ℕ) :
    mtPaperAlignedEndpoint z₀ z₁ δ (j + 1) = min z₁
      (Nat.floor ((1 + δ) *
        ((mtPaperAlignedEndpoint z₀ z₁ δ j - 1 : ℕ) : ℝ)) + 1) := rfl

/-- Once the lower shifted endpoint contains one reciprocal width, every later aligned step can
advance by at least one integer. -/
theorem le_floor_paperAlignedStep {z₀ a : ℕ} {δ : ℝ}
    (hz₀ : 1 ≤ z₀) (hza : z₀ ≤ a) (hδ : 0 ≤ δ)
    (hprogress : 1 ≤ δ * ((z₀ - 1 : ℕ) : ℝ)) :
    a ≤ Nat.floor ((1 + δ) * ((a - 1 : ℕ) : ℝ)) := by
  have ha : 1 ≤ a := hz₀.trans hza
  have hsub : ((z₀ - 1 : ℕ) : ℝ) ≤ ((a - 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.sub_le_sub_right hza 1
  have hprogressA : 1 ≤ δ * ((a - 1 : ℕ) : ℝ) :=
    hprogress.trans (mul_le_mul_of_nonneg_left hsub hδ)
  apply Nat.le_floor
  calc
    (a : ℝ) = ((a - 1 : ℕ) : ℝ) + 1 := by
      rw [Nat.cast_sub ha]
      push_cast
      ring
    _ ≤ ((a - 1 : ℕ) : ℝ) + δ * ((a - 1 : ℕ) : ℝ) :=
      by simpa [add_comm] using
        add_le_add_left hprogressA ((a - 1 : ℕ) : ℝ)
    _ = (1 + δ) * ((a - 1 : ℕ) : ℝ) := by ring

/-- Every aligned endpoint stays between its initial and target endpoints. -/
theorem mtPaperAlignedEndpoint_mem_Icc {z₀ z₁ : ℕ} {δ : ℝ}
    (hz₀ : 1 ≤ z₀) (hz : z₀ ≤ z₁) (hδ : 0 ≤ δ)
    (hprogress : 1 ≤ δ * ((z₀ - 1 : ℕ) : ℝ)) (j : ℕ) :
    z₀ ≤ mtPaperAlignedEndpoint z₀ z₁ δ j ∧
      mtPaperAlignedEndpoint z₀ z₁ δ j ≤ z₁ := by
  induction j with
  | zero => simp [hz]
  | succ j ih =>
      rw [mtPaperAlignedEndpoint_succ]
      have hfloor := le_floor_paperAlignedStep hz₀ ih.1 hδ hprogress
      constructor
      · exact le_min hz (ih.1.trans (hfloor.trans (Nat.le_add_right _ _)))
      · exact min_le_left _ _

/-- Aligned endpoints are monotone. -/
theorem mtPaperAlignedEndpoint_monotone {z₀ z₁ : ℕ} {δ : ℝ}
    (hz₀ : 1 ≤ z₀) (hz : z₀ ≤ z₁) (hδ : 0 ≤ δ)
    (hprogress : 1 ≤ δ * ((z₀ - 1 : ℕ) : ℝ)) :
    Monotone (mtPaperAlignedEndpoint z₀ z₁ δ) := by
  apply monotone_nat_of_le_succ
  intro j
  rw [mtPaperAlignedEndpoint_succ]
  have hj := mtPaperAlignedEndpoint_mem_Icc hz₀ hz hδ hprogress j
  have hfloor := le_floor_paperAlignedStep hz₀ hj.1 hδ hprogress
  exact le_min hj.2 (hfloor.trans (Nat.le_add_right _ _))

/-- Before reaching the target, each aligned step advances by at least one. -/
theorem mtPaperAlignedEndpoint_add_le {z₀ z₁ : ℕ} {δ : ℝ}
    (hz₀ : 1 ≤ z₀) (hz : z₀ ≤ z₁) (hδ : 0 ≤ δ)
    (hprogress : 1 ≤ δ * ((z₀ - 1 : ℕ) : ℝ))
    (j : ℕ) (hj : z₀ + j ≤ z₁) :
    z₀ + j ≤ mtPaperAlignedEndpoint z₀ z₁ δ j := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [mtPaperAlignedEndpoint_succ]
      have hjPrev : z₀ + j ≤ z₁ := by omega
      have hcurrent := ih hjPrev
      have hbase := (mtPaperAlignedEndpoint_mem_Icc hz₀ hz hδ hprogress j).1
      have hfloor := le_floor_paperAlignedStep hz₀ hbase hδ hprogress
      apply le_min
      · simpa [Nat.add_assoc] using hj
      · omega

/-- Padding by `z₁-z₀` steps always reaches the target exactly. -/
theorem mtPaperAlignedEndpoint_sub_eq {z₀ z₁ : ℕ} {δ : ℝ}
    (hz₀ : 1 ≤ z₀) (hz : z₀ ≤ z₁) (hδ : 0 ≤ δ)
    (hprogress : 1 ≤ δ * ((z₀ - 1 : ℕ) : ℝ)) :
    mtPaperAlignedEndpoint z₀ z₁ δ (z₁ - z₀) = z₁ := by
  apply Nat.le_antisymm
  · exact (mtPaperAlignedEndpoint_mem_Icc hz₀ hz hδ hprogress _).2
  · have hreach := mtPaperAlignedEndpoint_add_le hz₀ hz hδ hprogress
      (z₁ - z₀) (by omega : z₀ + (z₁ - z₀) ≤ z₁)
    simpa [Nat.add_sub_of_le hz] using hreach

/-- Every recursive aligned block satisfies the exact shifted paper-width inequality. -/
theorem mtPaperAlignedEndpoint_band {z₀ z₁ : ℕ} {δ : ℝ}
    (hδ : 0 ≤ δ) (j : ℕ) :
    ((mtPaperAlignedEndpoint z₀ z₁ δ (j + 1) - 1 : ℕ) : ℝ) ≤
      (1 + δ) * ((mtPaperAlignedEndpoint z₀ z₁ δ j - 1 : ℕ) : ℝ) := by
  rw [mtPaperAlignedEndpoint_succ]
  let R : ℝ := (1 + δ) *
    ((mtPaperAlignedEndpoint z₀ z₁ δ j - 1 : ℕ) : ℝ)
  have hR : 0 ≤ R := by
    dsimp [R]
    positivity
  have hnat : min z₁ (Nat.floor R + 1) - 1 ≤ Nat.floor R := by omega
  have hcast : ((min z₁ (Nat.floor R + 1) - 1 : ℕ) : ℝ) ≤
      (Nat.floor R : ℝ) := by exact_mod_cast hnat
  exact hcast.trans (Nat.floor_le hR)

/-- Adjacent source data whose recursive cutoffs equal their natural block endpoints. -/
def MTFiniteIterationSourceData.ofAlignedSchedule {t : ℕ}
    (z₀ D : ℕ) (endpoint : ℕ → ℕ)
    (hmono : Monotone endpoint) (hendpoint₀ : endpoint 0 = z₀) :
    MTFiniteIterationSourceData t := by
  apply MTFiniteIterationSourceData.ofAdjacentSchedule z₀ D endpoint
    (mtAlignedCutoff endpoint) hmono
  · exact hendpoint₀.ge
  · intro j
    rw [← hendpoint₀]
    exact hmono (Nat.zero_le j.1)
  · intro j
    exact le_rfl
  · intro i
    exact hmono (Nat.zero_le i.succ.1)

@[simp] theorem mtAdjacentLowerSpill_aligned {t : ℕ}
    (z₀ : ℕ) (endpoint : ℕ → ℕ) (hendpoint₀ : endpoint 0 = z₀)
    (j : Fin (t + 1)) :
    mtAdjacentLowerSpill z₀ endpoint (mtAlignedCutoff endpoint) j = ∅ := by
  induction j using Fin.cases with
  | zero =>
      ext q
      simp [mtAdjacentLowerSpill, mtAlignedCutoff, hendpoint₀, primesIco]
  | succ i =>
      ext q
      simp [mtAdjacentLowerSpill, hendpoint₀, primesIco]

@[simp] theorem mtAdjacentUpperSpill_aligned {t : ℕ}
    (endpoint : ℕ → ℕ) (j : Fin (t + 1)) :
    mtAdjacentUpperSpill endpoint (mtAlignedCutoff endpoint) j = ∅ := by
  induction j using Fin.cases with
  | zero => simp [mtAdjacentUpperSpill]
  | succ i =>
      ext q
      simp [mtAdjacentUpperSpill, mtAlignedCutoff, primesIco]

/-- Aligned narrow endpoints give the complete grid-free support certificate. -/
def MTFiniteIterationSourceData.alignedPaperScaleCertificate {t : ℕ}
    (A : ℕ) (X : ℝ) (z₀ D : ℕ) (endpoint : ℕ → ℕ)
    (hmono : Monotone endpoint) (hendpoint₀ : endpoint 0 = z₀)
    (hz₀ : z₀ = mtLowerCutoffNat X) (hD : D = mtTruncationNat X)
    (hNOne : 1 ≤ endpoint t) (hNX : (endpoint t : ℝ) ≤ X)
    (hlowerCut : ∀ i : Fin t,
      mtLowerCutoff X / (1 + mtPaperWidth A X) ≤
        ((endpoint i.1 - 1 : ℕ) : ℝ))
    (hband : ∀ i : Fin t,
      ((endpoint (i.1 + 1) - 1 : ℕ) : ℝ) ≤
        (1 + mtPaperWidth A X) * ((endpoint i.1 - 1 : ℕ) : ℝ)) :
    MTGridFreePaperScaleCertificate
      (MTFiniteIterationSourceData.ofAlignedSchedule
        (t := t) z₀ D endpoint hmono hendpoint₀) A X where
  lower := mtBlockLower (mtAdjacentPrimeBlock endpoint) (mtAlignedCutoff endpoint)
  PLower := ∅
  PUpper := ∅
  P := primesIco z₀ (endpoint t)
  N := endpoint t
  z₀_eq := hz₀
  D_eq := hD
  lower_eq := by
    intro k
    rfl
  lower_subset := by
    intro k
    change mtAdjacentLowerSpill z₀ endpoint (mtAlignedCutoff endpoint) k ⊆ ∅
    rw [mtAdjacentLowerSpill_aligned z₀ endpoint hendpoint₀ k]
  upper_subset := by
    intro k
    change mtAdjacentUpperSpill endpoint (mtAlignedCutoff endpoint) k ⊆ ∅
    rw [mtAdjacentUpperSpill_aligned endpoint k]
  prefix_subset := by
    intro k q hq
    obtain ⟨hqz, hqUpper, hqPrime⟩ := mem_primesIco.mp hq
    exact mem_primesIco.mpr ⟨hqz,
      hqUpper.trans_le (hmono (by omega : k.1 ≤ t)), hqPrime⟩
  lower_prime := by simp
  upper_prime := by simp
  prime := by
    intro q hq
    exact (mem_primesIco.mp hq).2.2
  N_one := hNOne
  N_le := hNX
  prime_le := by
    intro q hq
    exact (mem_primesIco.mp hq).2.1.le
  lower_mass := by
    simp only [Finset.sum_empty]
    have hNOneR : (1 : ℝ) ≤ (endpoint t : ℝ) := by exact_mod_cast hNOne
    have hXOne : (1 : ℝ) ≤ X := hNOneR.trans hNX
    exact mul_nonneg (by norm_num)
      (by rw [mtPaperWidth]; exact Real.rpow_nonneg (Real.log_nonneg hXOne) _)
  upper_mass := by
    simp only [Finset.sum_empty]
    have hNOneR : (1 : ℝ) ≤ (endpoint t : ℝ) := by exact_mod_cast hNOne
    have hXOne : (1 : ℝ) ≤ X := hNOneR.trans hNX
    exact mul_nonneg (by norm_num)
      (by rw [mtPaperWidth]; exact Real.rpow_nonneg (Real.log_nonneg hXOne) _)
  lower_cut := by
    intro q hq
    have hqUnion : q ∈
        (mtBlockPrefix (Fin.last t)).biUnion (mtAdjacentPrimeBlock endpoint) := by
      rw [mtAdjacentPrimeBlock_prefix_biUnion endpoint hmono]
      simpa [hendpoint₀] using hq
    obtain ⟨i, hi, hqi⟩ := Finset.mem_biUnion.mp hqUnion
    rw [mtBlockLower_eq_of_mem (mtAdjacentPrimeBlock endpoint)
      (mtAlignedCutoff endpoint)
      (mtAdjacentPrimeBlock_disjoint endpoint hmono) i hqi]
    exact hlowerCut i
  lower_le := by
    intro q hq
    have hqUnion : q ∈
        (mtBlockPrefix (Fin.last t)).biUnion (mtAdjacentPrimeBlock endpoint) := by
      rw [mtAdjacentPrimeBlock_prefix_biUnion endpoint hmono]
      simpa [hendpoint₀] using hq
    obtain ⟨i, hi, hqi⟩ := Finset.mem_biUnion.mp hqUnion
    rw [mtBlockLower_eq_of_mem (mtAdjacentPrimeBlock endpoint)
      (mtAlignedCutoff endpoint)
      (mtAdjacentPrimeBlock_disjoint endpoint hmono) i hqi]
    exact (mem_primesIco.mp hqi).1
  band := by
    intro q hq
    have hqUnion : q ∈
        (mtBlockPrefix (Fin.last t)).biUnion (mtAdjacentPrimeBlock endpoint) := by
      rw [mtAdjacentPrimeBlock_prefix_biUnion endpoint hmono]
      simpa [hendpoint₀] using hq
    obtain ⟨i, hi, hqi⟩ := Finset.mem_biUnion.mp hqUnion
    rw [mtBlockLower_eq_of_mem (mtAdjacentPrimeBlock endpoint)
      (mtAlignedCutoff endpoint)
      (mtAdjacentPrimeBlock_disjoint endpoint hmono) i hqi]
    have hqBound : q - 1 ≤ endpoint (i.1 + 1) - 1 := by
      have := (mem_primesIco.mp hqi).2.1
      omega
    have hqBoundR : ((q - 1 : ℕ) : ℝ) ≤
        ((endpoint (i.1 + 1) - 1 : ℕ) : ℝ) := by
      exact_mod_cast hqBound
    exact hqBoundR.trans (hband i)

/-- Concrete aligned source data joining `z₀` to `z₁`; padding ends after `z₁-z₀` steps. -/
def MTFiniteIterationSourceData.ofPaperAlignedSchedule
    (z₀ z₁ D : ℕ) (δ : ℝ) (hz₀ : 1 ≤ z₀) (hz : z₀ ≤ z₁)
    (hδ : 0 ≤ δ) (hprogress : 1 ≤ δ * ((z₀ - 1 : ℕ) : ℝ)) :
    MTFiniteIterationSourceData (z₁ - z₀) :=
  MTFiniteIterationSourceData.ofAlignedSchedule z₀ D
    (mtPaperAlignedEndpoint z₀ z₁ δ)
    (mtPaperAlignedEndpoint_monotone hz₀ hz hδ hprogress) rfl

/-- Paper parameters instantiate the complete grid-free certificate for the aligned recurrence. -/
def MTFiniteIterationSourceData.paperAlignedPaperScaleCertificate
    (A : ℕ) (X : ℝ) (z₀ z₁ D : ℕ)
    (hz₀One : 1 ≤ z₀) (hz : z₀ ≤ z₁)
    (hz₀ : z₀ = mtLowerCutoffNat X) (hD : D = mtTruncationNat X)
    (hz₁X : (z₁ : ℝ) ≤ X)
    (hprogress : 1 ≤ mtPaperWidth A X * ((z₀ - 1 : ℕ) : ℝ)) :
    MTGridFreePaperScaleCertificate
      (MTFiniteIterationSourceData.ofPaperAlignedSchedule
        z₀ z₁ D (mtPaperWidth A X) hz₀One hz
        (by
          rw [mtPaperWidth]
          have hz₁OneR : (1 : ℝ) ≤ (z₁ : ℝ) := by
            exact_mod_cast hz₀One.trans hz
          exact Real.rpow_nonneg (Real.log_nonneg (hz₁OneR.trans hz₁X)) _)
        hprogress) A X := by
  have hz₁One : 1 ≤ z₁ := hz₀One.trans hz
  have hz₁Eq : mtPaperAlignedEndpoint z₀ z₁ (mtPaperWidth A X) (z₁ - z₀) = z₁ :=
    mtPaperAlignedEndpoint_sub_eq hz₀One hz
      (by
        rw [mtPaperWidth]
        have hz₁OneR : (1 : ℝ) ≤ (z₁ : ℝ) := by exact_mod_cast hz₁One
        exact Real.rpow_nonneg (Real.log_nonneg (hz₁OneR.trans hz₁X)) _)
      hprogress
  have hδ : 0 ≤ mtPaperWidth A X := by
    rw [mtPaperWidth]
    have hz₁OneR : (1 : ℝ) ≤ (z₁ : ℝ) := by exact_mod_cast hz₁One
    exact Real.rpow_nonneg (Real.log_nonneg (hz₁OneR.trans hz₁X)) _
  apply MTFiniteIterationSourceData.alignedPaperScaleCertificate
    A X z₀ D (mtPaperAlignedEndpoint z₀ z₁ (mtPaperWidth A X))
    (mtPaperAlignedEndpoint_monotone hz₀One hz hδ hprogress) rfl
    hz₀ hD
  · simpa [hz₁Eq] using hz₁One
  · simpa [hz₁Eq] using hz₁X
  · intro i
    have hendpointLower :=
      (mtPaperAlignedEndpoint_mem_Icc hz₀One hz hδ hprogress i.1).1
    have hsubLower : z₀ - 1 ≤
        mtPaperAlignedEndpoint z₀ z₁ (mtPaperWidth A X) i.1 - 1 :=
      Nat.sub_le_sub_right hendpointLower 1
    have hcutCeil : mtLowerCutoff X ≤ (z₀ : ℝ) := by
      rw [hz₀, mtLowerCutoffNat]
      exact Nat.le_ceil _
    have hden : 0 < 1 + mtPaperWidth A X := by linarith
    have hz₀Cast : (z₀ : ℝ) = ((z₀ - 1 : ℕ) : ℝ) + 1 := by
      rw [Nat.cast_sub hz₀One]
      push_cast
      ring
    have hbase : mtLowerCutoff X / (1 + mtPaperWidth A X) ≤
        ((z₀ - 1 : ℕ) : ℝ) := by
      apply (div_le_iff₀ hden).2
      calc
        mtLowerCutoff X ≤ (z₀ : ℝ) := hcutCeil
        _ = ((z₀ - 1 : ℕ) : ℝ) + 1 := hz₀Cast
        _ ≤ ((z₀ - 1 : ℕ) : ℝ) +
            mtPaperWidth A X * ((z₀ - 1 : ℕ) : ℝ) :=
          by simpa [add_comm] using
            add_le_add_left hprogress ((z₀ - 1 : ℕ) : ℝ)
        _ = ((z₀ - 1 : ℕ) : ℝ) * (1 + mtPaperWidth A X) := by ring
    exact hbase.trans (by exact_mod_cast hsubLower)
  · intro i
    exact mtPaperAlignedEndpoint_band hδ i.1

/-- Paper width eventually advances the shifted natural lower endpoint by at least one. -/
theorem eventually_one_le_mtPaperWidth_mul_mtLowerCutoffNat_sub_one (A : ℕ) :
    ∀ᶠ X : ℝ in atTop,
      1 ≤ mtPaperWidth A X * ((mtLowerCutoffNat X - 1 : ℕ) : ℝ) := by
  have hdecay := eventually_two_mul_exp_neg_sqrt_log_le_log_rpow_neg
    (B := (1 : ℝ)) (c := (1 : ℝ)) (K := ((10 * A : ℕ) : ℝ))
    (by norm_num) (by norm_num)
  have hcutLarge := tendsto_mtLowerLogCutoff_atTop.eventually_ge_atTop (Real.log 2)
  filter_upwards [eventually_sqrt_log_le_mtLowerLogCutoff, hdecay, hcutLarge,
    Filter.eventually_ge_atTop (1 : ℝ)] with X hsqrt hdecayX hcutLargeX hX
  have hcutPos : 0 < mtLowerCutoff X := by
    rw [mtLowerCutoff]
    exact Real.exp_pos _
  have hcutTwo : (2 : ℝ) ≤ mtLowerCutoff X := by
    rw [mtLowerCutoff]
    calc
      (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
      _ ≤ Real.exp (mtLowerLogCutoff X) := Real.exp_le_exp.mpr hcutLargeX
  have hceil : mtLowerCutoff X ≤ (mtLowerCutoffNat X : ℝ) := by
    exact Nat.le_ceil _
  have hzTwo : 2 ≤ mtLowerCutoffNat X := by exact_mod_cast hcutTwo.trans hceil
  have hhalf : mtLowerCutoff X / 2 ≤
      ((mtLowerCutoffNat X - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ mtLowerCutoffNat X)]
    push_cast
    linarith
  have hexp : Real.exp (-mtLowerLogCutoff X) ≤
      Real.exp (-Real.sqrt (Real.log X)) := by
    rw [Real.exp_le_exp]
    linarith
  have hinv : 2 * (mtLowerCutoff X)⁻¹ ≤ mtPaperWidth A X := by
    calc
      2 * (mtLowerCutoff X)⁻¹ = 2 * Real.exp (-mtLowerLogCutoff X) := by
        rw [mtLowerCutoff, Real.exp_neg]
      _ ≤ 2 * Real.exp (-Real.sqrt (Real.log X)) :=
        mul_le_mul_of_nonneg_left hexp (by norm_num)
      _ ≤ mtPaperWidth A X := by
        simpa [mtPaperWidth] using hdecayX
  have hwidth : 0 ≤ mtPaperWidth A X := by
    rw [mtPaperWidth]
    exact Real.rpow_nonneg (Real.log_nonneg hX) _
  have hone : (1 : ℝ) ≤ mtPaperWidth A X * (mtLowerCutoff X / 2) := by
    have hmul := mul_le_mul_of_nonneg_right hinv
      (show 0 ≤ mtLowerCutoff X / 2 by positivity)
    have hcancel : 2 * (mtLowerCutoff X)⁻¹ * (mtLowerCutoff X / 2) = 1 := by
      field_simp
    rw [hcancel] at hmul
    nlinarith
  exact hone.trans (mul_le_mul_of_nonneg_left hhalf hwidth)

/-- Unconditional paper-scale schedule and repaired terminal-depth error bound. -/
theorem eventually_exists_paperAlignedSourceData_errorBound
    (A : ℕ) (hA : 5 ≤ A) :
    ∀ᶠ X : ℝ in atTop,
      ∀ (z₁ Y : ℕ) (a : ArithmeticFunction ℂ) (B : ℝ),
      mtLowerCutoffNat X ≤ z₁ → (z₁ : ℝ) ≤ X →
      1 ≤ Y → (Y : ℝ) ≤ 4 * X → 0 ≤ B →
      (∀ {m : ℕ}, 0 < m → ‖a m‖ ≤ B) →
      ∃ (data : MTFiniteIterationSourceData (z₁ - mtLowerCutoffNat X)),
        ∃ _cert : MTGridFreePaperScaleCertificate data A X,
          data.cutoff (Fin.last (z₁ - mtLowerCutoffNat X)) = z₁ ∧
          let J := Nat.floor (Real.log (Y : ℝ) / Real.log (data.z₀ : ℝ))
          ∑ n ∈ Finset.Icc 1 Y,
              ‖mtAccumulatedSourceErrorAF data a J
                (Fin.last (z₁ - mtLowerCutoffNat X)) n‖ ^ 2 ≤
            15 * B ^ 2 * (Y : ℝ) *
              (Real.log X) ^ (-((2 * A : ℕ) : ℝ)) := by
  filter_upwards [eventually_one_le_mtPaperWidth_mul_mtLowerCutoffNat_sub_one A,
    eventually_mtC1_integer_schedule,
    eventually_sum_norm_sq_mtAccumulatedSourceErrorAF_at_logDepth_gridFree A hA]
    with X hprogress hschedule hboundX
  intro z₁ Y a B hz hz₁X hY hYX hB ha
  have hz₀One : 1 ≤ mtLowerCutoffNat X := by omega
  have hz₁One : 1 ≤ z₁ := hz₀One.trans hz
  have hz₁OneR : (1 : ℝ) ≤ (z₁ : ℝ) := by exact_mod_cast hz₁One
  have hδ : 0 ≤ mtPaperWidth A X := by
    rw [mtPaperWidth]
    exact Real.rpow_nonneg (Real.log_nonneg (hz₁OneR.trans hz₁X)) _
  let data : MTFiniteIterationSourceData (z₁ - mtLowerCutoffNat X) :=
    MTFiniteIterationSourceData.ofPaperAlignedSchedule
      (mtLowerCutoffNat X) z₁ (mtTruncationNat X) (mtPaperWidth A X)
      hz₀One hz hδ hprogress
  let cert : MTGridFreePaperScaleCertificate data A X :=
    MTFiniteIterationSourceData.paperAlignedPaperScaleCertificate
      A X (mtLowerCutoffNat X) z₁ (mtTruncationNat X)
      hz₀One hz rfl rfl hz₁X hprogress
  refine ⟨data, cert, ?_, ?_⟩
  · dsimp [data, MTFiniteIterationSourceData.ofPaperAlignedSchedule,
      MTFiniteIterationSourceData.ofAlignedSchedule,
      MTFiniteIterationSourceData.ofAdjacentSchedule,
      MTFiniteIterationSourceData.ofPrefixUnion, mtAlignedCutoff]
    exact mtPaperAlignedEndpoint_sub_eq hz₀One hz hδ hprogress
  · exact hboundX (z₁ - mtLowerCutoffNat X) data cert a
      (Fin.last (z₁ - mtLowerCutoffNat X)) Y B hY hYX hB ha

/-- Repaired source-scale Lemma 2.3(ii): exact terminal expansion and mean-square error estimate,
with an unconditional aligned block schedule. -/
theorem eventually_exists_matomakiTeravainen_lemma23ii_repaired
    (A : ℕ) (hA : 5 ≤ A) :
    ∀ᶠ X : ℝ in atTop,
      ∀ (z₁ Y : ℕ) (α : ℕ → ℂ) (B : ℝ),
      mtLowerCutoffNat X ≤ z₁ → (z₁ : ℝ) ≤ X →
      1 ≤ Y → (Y : ℝ) ≤ 4 * X → 0 ≤ B →
      (∀ {m : ℕ}, 0 < m → ‖α m‖ ≤ B) →
      ∃ (data : MTFiniteIterationSourceData (z₁ - mtLowerCutoffNat X)),
        ∃ _cert : MTGridFreePaperScaleCertificate data A X,
          data.cutoff (Fin.last (z₁ - mtLowerCutoffNat X)) = z₁ ∧
          (let J := Nat.floor (Real.log (Y : ℝ) / Real.log (data.z₀ : ℝ))
           ∀ n ∈ Finset.Icc 1 Y,
            mtDivisorSiftSum α z₁ n =
              ((mtCoefficientAF α *
                  mtFiniteIterationMain data.truncation data.block data.cutoff J
                    (Fin.last (z₁ - mtLowerCutoffNat X))) +
                mtAccumulatedSourceErrorAF data (mtCoefficientAF α) J
                  (Fin.last (z₁ - mtLowerCutoffNat X))) n) ∧
          (let J := Nat.floor (Real.log (Y : ℝ) / Real.log (data.z₀ : ℝ))
           ∑ n ∈ Finset.Icc 1 Y,
              ‖mtAccumulatedSourceErrorAF data (mtCoefficientAF α) J
                (Fin.last (z₁ - mtLowerCutoffNat X)) n‖ ^ 2 ≤
            15 * B ^ 2 * (Y : ℝ) *
              (Real.log X) ^ (-((2 * A : ℕ) : ℝ))) := by
  filter_upwards [eventually_exists_paperAlignedSourceData_errorBound A hA,
    eventually_mtC1_integer_schedule] with X hexistsX hschedule
  intro z₁ Y α B hz hz₁X hY hYX hB hα
  have hcoeff : ∀ {m : ℕ}, 0 < m → ‖mtCoefficientAF α m‖ ≤ B := by
    intro m hm
    rw [mtCoefficientAF_apply_of_pos α hm]
    exact hα hm
  obtain ⟨data, cert, hroot, herror⟩ :=
    hexistsX z₁ Y (mtCoefficientAF α) B hz hz₁X hY hYX hB hcoeff
  refine ⟨data, cert, hroot, ?_, herror⟩
  dsimp only
  intro n hnIcc
  have hn : 0 < n := by
    rw [Finset.mem_Icc] at hnIcc
    omega
  have hnY : n ≤ Y := (Finset.mem_Icc.mp hnIcc).2
  have hzData : 1 < data.z₀ := by
    rw [cert.z₀_eq]
    omega
  have hexact := matomakiTeravainen_lemma23ii_terminal_exact
    data α (Fin.last (z₁ - mtLowerCutoffNat X)) hn hzData hnY
  dsimp only at hexact
  rw [hroot] at hexact
  exact hexact

end

end RHTower.Sieve
