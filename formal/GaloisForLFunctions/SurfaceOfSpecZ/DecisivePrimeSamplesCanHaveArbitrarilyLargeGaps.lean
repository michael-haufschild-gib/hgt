import GaloisForLFunctions.SurfaceOfSpecZ.TheGapMethodIterates
import GaloisForLFunctions.ZeroConfigurationGeometry.TheSplineTracesOnCompactConfigurationFamilies
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Decisive prime samples with arbitrarily large gaps

Every tail of the primes detects each impure tempered configuration without real zeros.
Compact configuration charts turn these pointwise detections into finite prime blocks.
Placing the blocks beyond successively larger multiplicative gaps gives one universal decisive
sample with no power-saving gap bound. No bound for the traces of the zeta configuration is asserted.
-/

open Set Finset Filter Topology Complex
noncomputable section
namespace GaloisForLFunctions.SurfaceOfSpecZ
open ArithmeticOrientationGeometry ArithmeticCastelnuovoSeveri SquareRootThreshold Zeta23
open ZeroConfigurationGeometry.CompactCoordinates

/-- Every tail of the primes sees arbitrarily negative traces of an impure configuration. -/
theorem exists_prime_trace_lt (Z : ZeroConfig) (hZ : TemperedConfig Z)
    (hnoreal : ∀ z ∈ Z.carrier, z.im ≠ 0)
    (himpure : ∃ z ∈ Z.carrier, z.re ≠ 1 / 2) (A : ℕ) (T : ℝ) :
    ∃ p : ℕ, p.Prime ∧ A ≤ p ∧
      2 * (lagStructure Z (boxSpline 1 3) (Real.log p)).re < -T := by
  classical
  by_contra h
  push_neg at h
  let f : ℕ → ℝ := fun p => 2 * (lagStructure Z (boxSpline 1 3) (Real.log p)).re
  let B := max T (∑ p ∈ Finset.range A, |f p|)
  have hb : ∀ p : ℕ, p.Prime → -B ≤ f p := by
    intro p hp
    by_cases hpa : p < A
    · have habs : |f p| ≤ ∑ q ∈ Finset.range A, |f q| :=
        Finset.single_le_sum (fun q _ => abs_nonneg (f q)) (Finset.mem_range.mpr hpa)
      have hB : (∑ q ∈ Finset.range A, |f q|) ≤ B := le_max_right _ _
      linarith [neg_abs_le (f p)]
    · have ht := h p hp (Nat.le_of_not_gt hpa)
      have hB : T ≤ B := le_max_left _ _
      change -T ≤ f p at ht
      linarith
  have hpure := onLine_of_bddBelow_primes Z hZ hnoreal hb
  obtain ⟨z, hz, hzne⟩ := himpure
  exact hzne (hpure z hz)

private theorem cubic_contDiff : ContDiff ℝ 2 (boxSpline 1 3) :=
  contDiff_boxSpline one_pos 2

private theorem cubic_compact : HasCompactSupport (boxSpline 1 3) :=
  hasCompactSupport_of_support_subset_abs (boxSpline_support one_pos 3)

/-- One finite block of arbitrarily late primes detects every member of a compact chart. -/
theorem exists_finite_prime_block (K A : ℕ) (T : ℝ) :
    ∃ F : Finset ℕ, (∀ p ∈ F, p.Prime ∧ A ≤ p) ∧
      ∀ q ∈ family K, ∃ p ∈ F, 2 * (traceSum (boxSpline 1 3) (Real.log p) q).re < -T := by
  classical
  letI : CompactSpace (family K) := (isCompact_iff_compactSpace.mp (isCompact_family K))
  let P := {p : ℕ // p.Prime ∧ A ≤ p}
  let U : P → Set (family K) := fun p =>
    {q | 2 * (traceSum (boxSpline 1 3) (Real.log p.val) q).re < -T}
  have hU : ∀ p : P, IsOpen (U p) := by
    intro p
    exact isOpen_lt ((Complex.continuous_re.comp
      (continuous_traceSum_family cubic_contDiff cubic_compact (Real.log p.val) K)).const_mul 2)
      continuous_const
  have hcover : (Set.univ : Set (family K)) ⊆ ⋃ p : P, U p := by
    intro q _
    have hq := family_config_impure K q.property
    obtain ⟨p, hp, hAp, hneg⟩ := exists_prime_trace_lt
      (config q.val q.property.1) hq.1 (config_has_no_real_zeros q.val q.property.1) hq.2 A T
    apply Set.mem_iUnion.mpr
    refine ⟨⟨p, hp, hAp⟩, ?_⟩
    change 2 * (traceSum (boxSpline 1 3) (Real.log p) q.val).re < -T
    rwa [traceSum_eq_lagStructure cubic_contDiff cubic_compact (Real.log p) q.property.1]
  obtain ⟨F, hF⟩ := (isCompact_univ : IsCompact (Set.univ : Set (family K))).elim_finite_subcover U hU hcover
  refine ⟨F.image Subtype.val, ?_, ?_⟩
  · intro p hp
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hp
    exact q.property
  · intro q hq
    obtain ⟨p, hp⟩ := Set.mem_iUnion.mp (hF (Set.mem_univ ⟨q, hq⟩))
    obtain ⟨hpF, hneg⟩ := Set.mem_iUnion.mp hp
    exact ⟨p, Finset.mem_image.mpr ⟨p, hpF, rfl⟩, hneg⟩

private def detectingBlock (K A : ℕ) : Finset ℕ :=
  Classical.choose (exists_finite_prime_block K A K)

private theorem detectingBlock_spec (K A : ℕ) :
    (∀ p ∈ detectingBlock K A, p.Prime ∧ A ≤ p) ∧
      ∀ q ∈ family K, ∃ p ∈ detectingBlock K A,
        2 * (traceSum (boxSpline 1 3) (Real.log p) q).re < -(K : ℝ) :=
  Classical.choose_spec (exists_finite_prime_block K A K)

/-- The gap endpoint is chosen after the preceding finite detecting block. -/
private def cut : ℕ → ℕ
  | 0 => 1
  | k + 1 => (k + 2) * cut k + (∑ p ∈ detectingBlock k ((k + 2) * cut k), p) + 1

private def sampleBlock (k : ℕ) : Finset ℕ := detectingBlock k ((k + 2) * cut k)

/-- A prime sample obtained from finite detectors separated by multiplicative gaps. -/
def decisiveSample : Set ℕ := {p | ∃ k : ℕ, p ∈ sampleBlock k}

private theorem cut_lt_succ (k : ℕ) : cut k < cut (k + 1) := by
  rw [cut, Nat.add_mul]
  omega

private theorem cut_mono : Monotone cut := (strictMono_nat_of_lt_succ cut_lt_succ).monotone

private theorem cut_ge (k : ℕ) : k + 1 ≤ cut k := by
  induction k with
  | zero => exact le_rfl
  | succ k ih => exact (Nat.succ_le_succ ih).trans (cut_lt_succ k)

private theorem block_lt_next {k p : ℕ} (hp : p ∈ sampleBlock k) : p < cut (k + 1) := by
  have hsum : p ≤ ∑ q ∈ detectingBlock k ((k + 2) * cut k), q :=
    Finset.single_le_sum (fun q _ => Nat.zero_le q) hp
  rw [cut]
  omega

theorem decisiveSample_prime {p : ℕ} (hp : p ∈ decisiveSample) : p.Prime := by
  obtain ⟨k, hk⟩ := hp
  exact ((detectingBlock_spec k ((k + 2) * cut k)).1 p hk).1

/-- Each protected multiplicative interval contains no sample degree. -/
theorem decisiveSample_gap (k : ℕ) {p : ℕ} (hp : p ∈ decisiveSample) :
    p < cut k ∨ (k + 2) * cut k ≤ p := by
  obtain ⟨j, hj⟩ := hp
  rcases lt_or_ge j k with hjk | hkj
  · exact Or.inl ((block_lt_next hj).trans_le (cut_mono (Nat.succ_le_of_lt hjk)))
  · exact Or.inr ((Nat.mul_le_mul (Nat.add_le_add_right hkj 2) (cut_mono hkj)).trans
      ((detectingBlock_spec j ((j + 2) * cut j)).1 p hj).2)

/-- The prime sample decides purity for all tempered configurations without real zeros,
including those whose top abscissa is unattained. -/
theorem onLine_of_bddBelow_decisiveSample (Z : ZeroConfig) (hZ : TemperedConfig Z)
    (hnoreal : ∀ z ∈ Z.carrier, z.im ≠ 0) {T : ℝ}
    (hT : ∀ p ∈ decisiveSample,
      -T ≤ 2 * (lagStructure Z (boxSpline 1 3) (Real.log p)).re) :
    ∀ z ∈ Z.carrier, z.re = 1 / 2 := by
  by_contra h
  push_neg at h
  obtain ⟨K, hK⟩ := exists_family_encoding Z hZ hnoreal h
  obtain ⟨k, hk⟩ := exists_nat_gt (max (K : ℝ) (2 * T))
  have hKk : K ≤ k := by exact_mod_cast (le_max_left (K : ℝ) (2 * T)).trans hk.le
  have hq := family_mono hKk hK
  obtain ⟨p, hp, hneg⟩ := (detectingBlock_spec k ((k + 2) * cut k)).2 (encoding Z) hq
  have hbound := hT p ⟨k, hp⟩
  rw [traceSum_encoding cubic_contDiff cubic_compact (Real.log p) Z hZ hnoreal] at hneg
  have hkT : 2 * T < (k : ℝ) := (le_max_right (K : ℝ) (2 * T)).trans_lt hk
  simp only [Complex.mul_re, Complex.ofNat_re, Complex.ofNat_im, zero_mul, sub_zero] at hneg
  linarith
/-- The multiplicative ratios of omitted intervals are unbounded. -/
theorem decisiveSample_has_large_gaps (R N : ℕ) :
    ∃ r : ℕ, 0 < r ∧ N ≤ r ∧ ∀ p ∈ decisiveSample, p < r ∨ R * r ≤ p := by
  let k := max R N
  refine ⟨cut k, by have := cut_ge k; omega, ?_, ?_⟩
  · exact (le_max_right R N).trans (by have := cut_ge k; omega)
  · intro p hp
    rcases decisiveSample_gap k hp with h | h
    · exact Or.inl h
    · exact Or.inr ((Nat.mul_le_mul_right (cut k)
        (show R ≤ k + 2 by have := le_max_left R N; omega)).trans h)

/-- No sublinear power controls the gaps of the decisive sample. -/
theorem not_powGaps_decisiveSample {θ : ℝ} (hθ : θ < 1) :
    ¬ PowGaps θ decisiveSample := by
  rintro ⟨_, M, X, _, hgap⟩
  have hlim : Tendsto (fun x : ℝ => M * (x ^ (1 - θ))⁻¹) atTop (𝓝 0) := by
    have h := (tendsto_inv_atTop_zero.comp (tendsto_rpow_atTop (by linarith : 0 < 1 - θ))).const_mul M
    simpa only [mul_zero] using h
  obtain ⟨Y, hY⟩ := eventually_atTop.mp (hlim.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 4))
  obtain ⟨k, hk⟩ := exists_nat_gt (max X Y)
  have hcut : (k : ℝ) + 1 ≤ cut k := by exact_mod_cast cut_ge k
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  let x : ℝ := 3 * cut k / 2
  have hx : 0 < x := by dsimp [x]; linarith
  have hxX : X ≤ x := by dsimp [x]; linarith [le_max_left X Y]
  have hxY : Y ≤ x := by dsimp [x]; linarith [le_max_right X Y]
  have he : (x ^ (1 - θ))⁻¹ * x = x ^ θ := by
    calc
      _ = x ^ (-(1 - θ)) * x ^ (1 : ℝ) := by rw [Real.rpow_neg hx.le, Real.rpow_one]
      _ = x ^ (-(1 - θ) + 1) := (Real.rpow_add hx _ _).symm
      _ = _ := by congr 1; ring
  have hsmall := mul_lt_mul_of_pos_right (hY x hxY) hx
  rw [mul_assoc, he] at hsmall
  obtain ⟨p, hp, hpx, hdist⟩ := hgap x hxX
  have hpcut : (p : ℝ) < cut k := by
    rcases decisiveSample_gap k hp with h | h
    · exact_mod_cast h
    · have hh : 2 * cut k ≤ p := (Nat.mul_le_mul_right (cut k) (by omega : 2 ≤ k + 2)).trans h
      have hh' : 2 * (cut k : ℝ) ≤ p := by exact_mod_cast hh
      dsimp [x] at hpx
      linarith
  dsimp [x] at hsmall hdist
  linarith

/-- Power-saving gaps are sufficient but not necessary for a one-sided prime sample to decide
purity. A single universal sample can have arbitrarily large multiplicative gaps. -/
theorem exists_decisive_prime_sample_without_power_saving_gaps :
    ∃ D : Set ℕ, (∀ p ∈ D, p.Prime) ∧
      (∀ R N : ℕ, ∃ r : ℕ, 0 < r ∧ N ≤ r ∧ ∀ p ∈ D, p < r ∨ R * r ≤ p) ∧
      (∀ θ : ℝ, θ < 1 → ¬ PowGaps θ D) ∧
      ∀ (Z : ZeroConfig), TemperedConfig Z → (∀ z ∈ Z.carrier, z.im ≠ 0) →
        (∃ T : ℝ, ∀ p ∈ D, -T ≤ 2 * (lagStructure Z (boxSpline 1 3) (Real.log p)).re) →
        ∀ z ∈ Z.carrier, z.re = 1 / 2 := by
  refine ⟨decisiveSample, (fun _ hp => decisiveSample_prime hp), decisiveSample_has_large_gaps,
    (fun _ hθ => not_powGaps_decisiveSample hθ), ?_⟩
  rintro Z hZ hnoreal ⟨T, hT⟩
  exact onLine_of_bddBelow_decisiveSample Z hZ hnoreal hT

#print axioms exists_finite_prime_block
#print axioms onLine_of_bddBelow_decisiveSample
#print axioms decisiveSample_has_large_gaps
#print axioms not_powGaps_decisiveSample
#print axioms exists_decisive_prime_sample_without_power_saving_gaps

end GaloisForLFunctions.SurfaceOfSpecZ
