import GaloisForLFunctions.RHTower.SectorPrimeZeroUniqueness

/-!
# Sectorial uniqueness for abstract frequency spectra

The prime logarithms are one instance of a more general analytic law.  A
frequency family is sector-Blaschke complete when, after every real
translation, its Cayley image violates the Blaschke summability condition.
Every bounded analytic function on the corresponding translated sector that
vanishes on the frequency family is then identically zero on the positive
ray.

This file removes all arithmetic from that uniqueness argument.  The
prime-logarithm specialization is recovered separately from Euler's
divergence of the reciprocal-prime sum.
-/

noncomputable section

namespace RHTower

open Complex Filter Function Metric Set

/-- Frequencies lying at least one unit beyond a translated sector vertex. -/
abbrev FrequencyBeyond {ι : Type*} (lambda : ι → ℝ) (R : ℝ) :=
  {i : ι // R + 1 < lambda i}

/-- The exact translated Blaschke-divergence hypothesis for a frequency
family and a fixed sector-root order. -/
def SectorBlaschkeComplete {ι : Type*}
    (lambda : ι → ℝ) (n : ℕ) (R₀ : ℝ) : Prop :=
  Function.Injective lambda ∧
    ∀ R ≥ R₀,
      ¬ Summable (fun i : FrequencyBeyond lambda R ↦
        (1 / ((lambda (i : ι) - R) ^ n + 1) : ℝ))

/-- Carrier-independent form: translated Blaschke divergence holds at every
positive integral sector-root order. -/
def StrongSectorBlaschkeComplete {ι : Type*}
    (lambda : ι → ℝ) (R₀ : ℝ) : Prop :=
  ∀ n : ℕ, n ≠ 0 → SectorBlaschkeComplete lambda n R₀

/-- Cayley image of the positive translated power
`(lambda i - R)^n`. -/
def frequencyCayley {ι : Type*}
    (lambda : ι → ℝ) (n : ℕ) (R : ℝ)
    (i : FrequencyBeyond lambda R) : ℂ :=
  ((((lambda (i : ι) - R) ^ n - 1) /
    ((lambda (i : ι) - R) ^ n + 1) : ℝ) : ℂ)

private theorem frequencyBeyond_base_gt_one
    {ι : Type*} (lambda : ι → ℝ) (R : ℝ)
    (i : FrequencyBeyond lambda R) :
    1 < lambda (i : ι) - R := by
  linarith [i.prop]

private theorem frequencyCayley_real_pos_lt_one
    {ι : Type*} {lambda : ι → ℝ} {n : ℕ} (hn : n ≠ 0)
    (R : ℝ) (i : FrequencyBeyond lambda R) :
    0 < ((lambda (i : ι) - R) ^ n - 1) /
      ((lambda (i : ι) - R) ^ n + 1) ∧
    ((lambda (i : ι) - R) ^ n - 1) /
      ((lambda (i : ι) - R) ^ n + 1) < 1 := by
  let y : ℝ := lambda (i : ι) - R
  have hy : 1 < y := frequencyBeyond_base_gt_one lambda R i
  have hyn : 1 < y ^ n := by
    simpa using pow_lt_pow_left₀ hy zero_le_one hn
  change 0 < (y ^ n - 1) / (y ^ n + 1) ∧
    (y ^ n - 1) / (y ^ n + 1) < 1
  constructor
  · exact div_pos (sub_pos.mpr hyn) (by linarith)
  · rw [div_lt_one (by linarith)]
    linarith

@[simp]
theorem norm_frequencyCayley
    {ι : Type*} {lambda : ι → ℝ} {n : ℕ} (hn : n ≠ 0)
    (R : ℝ) (i : FrequencyBeyond lambda R) :
    ‖frequencyCayley lambda n R i‖ =
      ((lambda (i : ι) - R) ^ n - 1) /
        ((lambda (i : ι) - R) ^ n + 1) := by
  rw [frequencyCayley, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (frequencyCayley_real_pos_lt_one hn R i).1]

@[simp]
theorem one_sub_norm_frequencyCayley
    {ι : Type*} {lambda : ι → ℝ} {n : ℕ} (hn : n ≠ 0)
    (R : ℝ) (i : FrequencyBeyond lambda R) :
    1 - ‖frequencyCayley lambda n R i‖ =
      2 / ((lambda (i : ι) - R) ^ n + 1) := by
  rw [norm_frequencyCayley hn]
  have hbase : 0 < lambda (i : ι) - R :=
    (frequencyBeyond_base_gt_one lambda R i).trans' zero_lt_one
  have hden : 0 < (lambda (i : ι) - R) ^ n + 1 := by
    positivity
  field_simp
  ring

/-- Injectivity of the frequency labels passes through translated positive
powers and the Cayley map. -/
theorem frequencyCayley_injective
    {ι : Type*} {lambda : ι → ℝ}
    (hlambda : Function.Injective lambda)
    {n : ℕ} (hn : n ≠ 0) (R : ℝ) :
    Function.Injective (frequencyCayley lambda n R) := by
  intro i j hij
  have hijR :
      ((lambda (i : ι) - R) ^ n - 1) /
          ((lambda (i : ι) - R) ^ n + 1) =
      ((lambda (j : ι) - R) ^ n - 1) /
          ((lambda (j : ι) - R) ^ n + 1) := by
    rw [frequencyCayley] at hij
    exact Complex.ofReal_injective hij
  let a : ℝ := lambda (i : ι) - R
  let b : ℝ := lambda (j : ι) - R
  have ha : 0 ≤ a :=
    (frequencyBeyond_base_gt_one lambda R i).le.trans' zero_le_one
  have hb : 0 ≤ b :=
    (frequencyBeyond_base_gt_one lambda R j).le.trans' zero_le_one
  have hda : a ^ n + 1 ≠ 0 := by positivity
  have hdb : b ^ n + 1 ≠ 0 := by positivity
  have hpow : a ^ n = b ^ n := by
    change (a ^ n - 1) / (a ^ n + 1) =
      (b ^ n - 1) / (b ^ n + 1) at hijR
    field_simp [hda, hdb] at hijR
    nlinarith
  have hab : a = b := (pow_left_inj₀ ha hb hn).mp hpow
  have hlabel : (i : ι) = (j : ι) := by
    apply hlambda
    dsimp [a, b] at hab
    linarith
  exact Subtype.ext hlabel

/-- The abstract translated Blaschke defect is nonsummable precisely under
the defining spectral condition. -/
theorem frequencyCayley_defect_not_summable
    {ι : Type*} {lambda : ι → ℝ} {n : ℕ} (hn : n ≠ 0)
    (R : ℝ)
    (hdiv : ¬ Summable (fun i : FrequencyBeyond lambda R ↦
      (1 / ((lambda (i : ι) - R) ^ n + 1) : ℝ))) :
    ¬ Summable (fun i : FrequencyBeyond lambda R ↦
      1 - ‖frequencyCayley lambda n R i‖) := by
  intro h
  have htwo : Summable (fun i : FrequencyBeyond lambda R ↦
      2 * (1 / ((lambda (i : ι) - R) ^ n + 1) : ℝ)) := by
    apply h.congr
    intro i
    simpa [div_eq_mul_inv] using one_sub_norm_frequencyCayley hn R i
  have hone : Summable (fun i : FrequencyBeyond lambda R ↦
      (1 / ((lambda (i : ι) - R) ^ n + 1) : ℝ)) := by
    have hs := htwo.mul_left (1 / 2 : ℝ)
    exact hs.congr fun i ↦ by
      ring
  exact hdiv hone

/-- A bounded nonzero analytic function on the unit disc cannot vanish on an
abstract frequency Cayley family with nonsummable Blaschke defect. -/
theorem not_bounded_analytic_zero_on_all_frequencyCayley
    {ι : Type*} {lambda : ι → ℝ}
    (hlambda : Function.Injective lambda)
    {n : ℕ} (hn : n ≠ 0) (R : ℝ)
    (hdiv : ¬ Summable (fun i : FrequencyBeyond lambda R ↦
      (1 / ((lambda (i : ι) - R) ^ n + 1) : ℝ)))
    {f : ℂ → ℂ} {M : ℝ} (hM : 1 ≤ M)
    (hf : AnalyticOnNhd ℂ f (ball 0 1))
    (hf0 : f 0 ≠ 0)
    (f_bound : ∀ z ∈ ball (0 : ℂ) 1, ‖f z‖ ≤ M)
    (hzero : ∀ i : FrequencyBeyond lambda R,
      f (frequencyCayley lambda n R i) = 0) : False := by
  apply frequencyCayley_defect_not_summable hn R hdiv
  apply summable_one_sub_norm_of_bounded_analytic_zeros_openDisk
    hM hf hf0 f_bound
    (frequencyCayley lambda n R)
    (frequencyCayley_injective hlambda hn R)
  · intro i
    rw [norm_frequencyCayley hn]
    exact (frequencyCayley_real_pos_lt_one hn R i).2
  · exact hzero

lemma diskToRight_frequencyCayley
    {ι : Type*} (lambda : ι → ℝ)
    (n : ℕ) (R : ℝ) (i : FrequencyBeyond lambda R) :
    diskToRight (frequencyCayley lambda n R i) =
      (((lambda (i : ι) - R) ^ n : ℝ) : ℂ) := by
  let y : ℝ := lambda (i : ι) - R
  have hy : 0 < y :=
    (frequencyBeyond_base_gt_one lambda R i).trans' zero_lt_one
  have hden : y ^ n + 1 ≠ 0 := by positivity
  unfold diskToRight frequencyCayley
  norm_cast
  change (1 + ((y ^ n - 1) / (y ^ n + 1))) /
    (1 - ((y ^ n - 1) / (y ^ n + 1))) = y ^ n
  field_simp [hden]
  ring

lemma sectorRootMap_frequencyCayley
    {ι : Type*} {lambda : ι → ℝ}
    {n : ℕ} (hn : n ≠ 0) (R : ℝ)
    (i : FrequencyBeyond lambda R) :
    sectorRootMap n R (frequencyCayley lambda n R i) =
      lambda (i : ι) := by
  let y : ℝ := lambda (i : ι) - R
  have hy : 0 < y :=
    (frequencyBeyond_base_gt_one lambda R i).trans' zero_lt_one
  rw [sectorRootMap, diskToRight_frequencyCayley lambda n]
  have hcast :
      (((lambda (i : ι) - R) ^ n : ℝ) : ℂ) = (y : ℂ) ^ n := by
    simp [y]
  rw [hcast]
  have hroot : (((y : ℂ) ^ n) ^ ((n : ℂ)⁻¹)) = (y : ℂ) := by
    apply Complex.pow_cpow_nat_inv hn
    · rw [Complex.arg_ofReal_of_nonneg hy.le]
      have hnpos : (0 : ℝ) < n := by
        exact_mod_cast Nat.pos_of_ne_zero hn
      have hdivpos : 0 < Real.pi / (n : ℝ) :=
        div_pos Real.pi_pos hnpos
      linarith
    · rw [Complex.arg_ofReal_of_nonneg hy.le]
      have hnpos : (0 : ℝ) < n := by
        exact_mod_cast Nat.pos_of_ne_zero hn
      exact (div_pos Real.pi_pos hnpos).le
  rw [hroot]
  exact_mod_cast (show R + y = lambda (i : ι) by
    dsimp [y]
    ring)

/-- Frequency zeros force vanishing at the translated sector vertex plus
one. -/
theorem frequency_zero_forces_sectorRootMap_zero
    {ι : Type*} {lambda : ι → ℝ}
    (hlambda : Function.Injective lambda)
    {n : ℕ} (hn : n ≠ 0) (R : ℝ)
    (hdiv : ¬ Summable (fun i : FrequencyBeyond lambda R ↦
      (1 / ((lambda (i : ι) - R) ^ n + 1) : ℝ)))
    {H : ℂ → ℂ} {M : ℝ} (hM : 1 ≤ M)
    (hcomp : AnalyticOnNhd ℂ
      (fun z ↦ H (sectorRootMap n R z)) (ball 0 1))
    (hbound : ∀ z ∈ ball (0 : ℂ) 1,
      ‖H (sectorRootMap n R z)‖ ≤ M)
    (hzero : ∀ i : FrequencyBeyond lambda R,
      H (lambda (i : ι)) = 0) :
    H (R + 1) = 0 := by
  by_contra hne
  apply not_bounded_analytic_zero_on_all_frequencyCayley
    hlambda hn R hdiv hM hcomp
  · simpa using hne
  · exact hbound
  · intro i
    rw [sectorRootMap_frequencyCayley hn]
    exact hzero i

/-- Universal ray uniqueness theorem.  The arithmetic nature of the
frequencies is irrelevant; only injectivity and translated Blaschke
divergence enter. -/
theorem frequency_zero_uniqueness_on_ray
    {ι : Type*} {lambda : ι → ℝ}
    {n : ℕ} (hn : n ≠ 0) (R₀ : ℝ)
    (hcomplete : SectorBlaschkeComplete lambda n R₀)
    {H : ℂ → ℂ}
    (hcomp : ∀ R ≥ R₀,
      AnalyticOnNhd ℂ
        (fun z ↦ H (sectorRootMap n R z)) (ball 0 1))
    (hbound : ∀ R ≥ R₀, ∃ M : ℝ, 1 ≤ M ∧
      ∀ z ∈ ball (0 : ℂ) 1,
        ‖H (sectorRootMap n R z)‖ ≤ M)
    (hzero : ∀ i : ι, R₀ + 1 < lambda i →
      H (lambda i) = 0) :
    ∀ x : ℝ, R₀ + 1 ≤ x → H x = 0 := by
  intro x hx
  let R : ℝ := x - 1
  have hRR₀ : R₀ ≤ R := by
    dsimp [R]
    linarith
  obtain ⟨M, hM, hMb⟩ := hbound R hRR₀
  have htail : ∀ i : FrequencyBeyond lambda R,
      H (lambda (i : ι)) = 0 := by
    intro i
    apply hzero (i : ι)
    have hi := i.prop
    dsimp [R] at hi
    linarith
  have hv := frequency_zero_forces_sectorRootMap_zero
    hcomplete.1 hn R (hcomplete.2 R hRR₀) hM
    (hcomp R hRR₀) hMb htail
  simpa [R] using hv

/-! ## Cofinite stability -/

/-- Strong sector-Blaschke completeness is unchanged by deleting an arbitrary
finite set of frequencies. -/
theorem strongSectorBlaschkeComplete_compl_finset
    {ι : Type*} [DecidableEq ι] (lambda : ι → ℝ) (R₀ : ℝ)
    (hcomplete : StrongSectorBlaschkeComplete lambda R₀)
    (S : Finset ι) :
    StrongSectorBlaschkeComplete
      (fun i : {i : ι // i ∉ S} ↦ lambda i) R₀ := by
  intro n hn
  let lambdaS : {i : ι // i ∉ S} → ℝ := fun i ↦ lambda i
  have hlambdaS : Function.Injective lambdaS := by
    intro i j hij
    apply Subtype.ext
    exact (hcomplete n hn).1 hij
  refine ⟨hlambdaS, fun R hRR₀ ↦ ?_⟩
  intro hsum
  let emb : FrequencyBeyond lambda R ↪ ι :=
    ⟨fun i ↦ (i : ι), Subtype.val_injective⟩
  let T : Set (FrequencyBeyond lambda R) :=
    emb ⁻¹' (S : Set ι)
  let Tcomp : Set (FrequencyBeyond lambda R) := Tᶜ
  have hT : T.Finite := by
    simpa only [T] using S.finite_toSet.preimage_embedding emb
  let e : FrequencyBeyond lambdaS R ≃ Tcomp :=
    { toFun := fun i ↦
        ⟨⟨((i : FrequencyBeyond lambdaS R).1 : ι), by
            exact i.prop⟩, by
          have hiS := (i : FrequencyBeyond lambdaS R).1.prop
          simpa [Tcomp, T, emb] using hiS⟩
      invFun := fun i ↦
        ⟨⟨((i : Tcomp).1 : ι), by
            have hiT : (i : Tcomp).1 ∉ T := (i : Tcomp).prop
            intro hiS
            apply hiT
            change emb (i : Tcomp).1 ∈ (S : Set ι)
            simpa only [emb] using! hiS⟩, by
          exact (i : Tcomp).1.prop⟩
      left_inv := by
        intro i
        rfl
      right_inv := by
        intro i
        rfl }
  let f : FrequencyBeyond lambda R → ℝ :=
    fun i ↦ 1 / ((lambda i - R) ^ n + 1)
  have hsumT : Summable (fun i : Tcomp ↦
      f (i : FrequencyBeyond lambda R)) := by
    apply (Equiv.summable_iff e).mp
    simpa [lambdaS, f, e] using! hsum
  have hsumAll : Summable f := by
    exact hT.summable_compl_iff.mp
      (by simpa only [Tcomp, Function.comp_apply] using! hsumT)
  exact (hcomplete n hn).2 R hRR₀ hsumAll

/-! ## Arithmetic instance: cofinite prime logarithms -/

/-- Logarithms are injective on the prime subtype. -/
theorem primeLog_injective :
    Function.Injective
      (fun p : Nat.Primes ↦ Real.log ((p : Nat.Primes) : ℝ)) := by
  intro p q hpq
  change Real.log ((p : Nat.Primes) : ℝ) =
    Real.log ((q : Nat.Primes) : ℝ) at hpq
  have hp0 : 0 < ((p : Nat.Primes) : ℝ) := by
    exact_mod_cast p.prop.pos
  have hq0 : 0 < ((q : Nat.Primes) : ℝ) := by
    exact_mod_cast q.prop.pos
  have hcast : (((p : Nat.Primes) : ℝ)) =
      (((q : Nat.Primes) : ℝ)) := by
    have h := congrArg Real.exp hpq
    simpa [Real.exp_log hp0, Real.exp_log hq0] using h
  apply Subtype.ext
  exact_mod_cast hcast

/-- Deleting any finite prime set preserves strong translated
sector-Blaschke completeness of the logarithmic frequency spectrum. -/
theorem cofinitePrimeLog_strongSectorBlaschkeComplete
    (S : Finset Nat.Primes) (R₀ : ℝ) (hR₀ : 0 ≤ R₀) :
    StrongSectorBlaschkeComplete
      (fun p : {p : Nat.Primes // p ∉ S} ↦
        Real.log (((p : {p : Nat.Primes // p ∉ S}) : Nat.Primes) : ℝ))
      R₀ := by
  intro n hn
  let lambda : {p : Nat.Primes // p ∉ S} → ℝ :=
    fun p ↦ Real.log (((p : {p : Nat.Primes // p ∉ S}) : Nat.Primes) : ℝ)
  have hlambda : Function.Injective lambda := by
    intro p q hpq
    apply Subtype.ext
    exact primeLog_injective hpq
  refine ⟨hlambda, fun R hRR₀ ↦ ?_⟩
  intro hsum
  let emb : PrimeLogBeyond R ↪ Nat.Primes :=
    ⟨fun p ↦ (p : Nat.Primes), Subtype.val_injective⟩
  let T : Set (PrimeLogBeyond R) :=
    emb ⁻¹' (S : Set Nat.Primes)
  let Tcomp : Set (PrimeLogBeyond R) := Tᶜ
  have hT : T.Finite := by
    simpa only [T] using S.finite_toSet.preimage_embedding emb
  let e : FrequencyBeyond lambda R ≃ Tcomp :=
    { toFun := fun i ↦
      ⟨⟨((i : FrequencyBeyond lambda R).1 : Nat.Primes), by
          have hi := i.prop
          simpa [lambda, smallPrimeLogs] using hi⟩, by
        have hiS := (i : FrequencyBeyond lambda R).1.prop
        simpa [Tcomp, T, emb] using hiS⟩
      invFun := fun p ↦
      ⟨⟨((p : Tcomp).1 : PrimeLogBeyond R), by
          have hpT : (p : Tcomp).1 ∉ T := (p : Tcomp).prop
          intro hpS
          apply hpT
          change emb (p : Tcomp).1 ∈ (S : Set Nat.Primes)
          simpa only [emb] using! hpS⟩, by
        have hp :
            (((p : Tcomp).1 : Nat.Primes) : Nat.Primes) ∈
              (smallPrimeLogs R)ᶜ :=
          (p : Tcomp).1.prop
        simp only [Set.mem_compl_iff, smallPrimeLogs, Set.mem_setOf_eq,
          Classical.not_not] at hp
        simpa [lambda] using hp⟩
      left_inv := by
        intro i
        rfl
      right_inv := by
        intro p
        rfl }
  let f : PrimeLogBeyond R → ℝ :=
    fun p ↦
      1 / ((Real.log (((p : PrimeLogBeyond R) : Nat.Primes) : ℝ) - R) ^ n + 1)
  have hsumT : Summable (fun p : Tcomp ↦ f (p : PrimeLogBeyond R)) := by
    apply (Equiv.summable_iff e).mp
    simpa [lambda, f, e] using! hsum
  have hsumAll : Summable f := by
    exact hT.summable_compl_iff.mp
      (by simpa only [Tcomp, Function.comp_apply] using! hsumT)
  exact prime_shifted_log_power_recip_beyond_not_summable
    n R (hR₀.trans hRR₀) hsumAll

/-- Prime-logarithm spectrum after deleting a prescribed finite prime set. -/
def cofinitePrimeLog (S : Finset Nat.Primes) :
    {p : Nat.Primes // p ∉ S} → ℝ :=
  fun p ↦ Real.log (((p : {p : Nat.Primes // p ∉ S}) : Nat.Primes) : ℝ)

theorem cofinitePrimeLog_positive
    (S : Finset Nat.Primes) (p : {p : Nat.Primes // p ∉ S}) :
    0 < cofinitePrimeLog S p := by
  unfold cofinitePrimeLog
  exact Real.log_pos (by exact_mod_cast ((p : Nat.Primes).prop.one_lt))

theorem cofinitePrimeLog_strongSectorBlaschkeComplete'
    (S : Finset Nat.Primes) (R₀ : ℝ) (hR₀ : 0 ≤ R₀) :
    StrongSectorBlaschkeComplete (cofinitePrimeLog S) R₀ := by
  change StrongSectorBlaschkeComplete
    (fun p : {p : Nat.Primes // p ∉ S} ↦
      Real.log (((p : {p : Nat.Primes // p ∉ S}) : Nat.Primes) : ℝ)) R₀
  exact cofinitePrimeLog_strongSectorBlaschkeComplete S R₀ hR₀

end RHTower
