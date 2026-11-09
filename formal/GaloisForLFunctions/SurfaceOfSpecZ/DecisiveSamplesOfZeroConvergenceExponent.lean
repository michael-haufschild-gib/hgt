import GaloisForLFunctions.SurfaceOfSpecZ.TheGapMethodIterates
import GaloisForLFunctions.ZeroConfigurationGeometry.TheSplineTracesOnCompactConfigurationFamilies
import Mathlib.Analysis.PSeries

/-!
# Decisive samples of zero convergence exponent

Finite detectors on successive prime-power meshes give one sample that decides purity
for every tempered configuration without real zeros. Its Dirichlet series converges
at every positive real argument: counting growth alone does not decide sampling power.
-/

open Set Finset Filter Topology Complex
noncomputable section
namespace GaloisForLFunctions.SurfaceOfSpecZ
open ArithmeticOrientationGeometry ArithmeticCastelnuovoSeveri SquareRootThreshold Zeta23
open ZeroConfigurationGeometry.CompactCoordinates

namespace ZeroExponentSample

private theorem cubic_contDiff : ContDiff ℝ 2 (boxSpline 1 3) :=
  contDiff_boxSpline one_pos 2

private theorem cubic_compact : HasCompactSupport (boxSpline 1 3) :=
  hasCompactSupport_of_support_subset_abs (boxSpline_support one_pos 3)

/-- Each compact impure chart has a finite detector on every positive prime-power mesh. -/
theorem exists_finite_power_block (K m : ℕ) (hm : 1 ≤ m) (T : ℝ) :
    ∃ F : Finset ℕ, (∀ p ∈ F, p.Prime) ∧
      ∀ q ∈ family K, ∃ p ∈ F,
        2 * (traceSum (boxSpline 1 3) (m * Real.log p) q).re < -T := by
  classical
  letI : CompactSpace (family K) := isCompact_iff_compactSpace.mp (isCompact_family K)
  let P := {p : ℕ // p.Prime}
  let U : P → Set (family K) := fun p =>
    {q | 2 * (traceSum (boxSpline 1 3) (m * Real.log p.val) q).re < -T}
  have hU : ∀ p : P, IsOpen (U p) := by
    intro p
    exact isOpen_lt ((Complex.continuous_re.comp
      (continuous_traceSum_family cubic_contDiff cubic_compact (m * Real.log p.val) K)).const_mul 2)
      continuous_const
  have hcover : (Set.univ : Set (family K)) ⊆ ⋃ p : P, U p := by
    intro q _
    have hq := family_config_impure K q.property
    by_contra hnot
    have hb : ∀ p : ℕ, p.Prime →
        -T ≤ 2 * (lagStructure (config q.val q.property.1)
          (boxSpline 1 3) (m * Real.log p)).re := by
      intro p hp
      apply le_of_not_gt
      intro hn
      apply hnot
      apply Set.mem_iUnion.mpr
      refine ⟨⟨p, hp⟩, ?_⟩
      change 2 * (traceSum (boxSpline 1 3) (m * Real.log p) q.val).re < -T
      rwa [traceSum_eq_lagStructure cubic_contDiff cubic_compact
        (m * Real.log p) q.property.1]
    have hpure := onLine_of_bddBelow_kthPrimePowers (config q.val q.property.1)
      hq.1 (config_has_no_real_zeros q.val q.property.1) hm hb
    obtain ⟨z, hz, hzne⟩ := hq.2
    exact hzne (hpure z hz)
  obtain ⟨F, hF⟩ := (isCompact_univ : IsCompact (Set.univ : Set (family K))).elim_finite_subcover U hU hcover
  refine ⟨F.image Subtype.val, ?_, ?_⟩
  · intro p hp
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hp
    exact q.property
  · intro q hq
    obtain ⟨p, hp⟩ := Set.mem_iUnion.mp (hF (Set.mem_univ ⟨q, hq⟩))
    obtain ⟨hpF, hneg⟩ := Set.mem_iUnion.mp hp
    exact ⟨p, Finset.mem_image.mpr ⟨p, hpF, rfl⟩, hneg⟩

private def block (k : ℕ) : Finset ℕ :=
  Classical.choose (exists_finite_power_block k (k + 1) (by omega) k)

private theorem block_spec (k : ℕ) :
    (∀ p ∈ block k, p.Prime) ∧
      ∀ q ∈ family k, ∃ p ∈ block k,
        2 * (traceSum (boxSpline 1 3) ((k + 1) * Real.log p) q).re < -(k : ℝ) := by
  simpa only [Nat.cast_add, Nat.cast_one] using
    Classical.choose_spec (exists_finite_power_block k (k + 1) (by omega) k)

private abbrev Occurrence := Σ k : ℕ, {p : ℕ // p ∈ block k}

private def degree (a : Occurrence) : ℕ := a.2.val ^ (a.1 + 1)

/-- The universal sample consists of a finite block on each successive prime-power mesh. -/
def sample : Set ℕ := Set.range degree

theorem sample_prime_power {d : ℕ} (hd : d ∈ sample) :
    ∃ p k : ℕ, p.Prime ∧ 0 < k ∧ d = p ^ k := by
  obtain ⟨a, rfl⟩ := hd
  exact ⟨a.2.val, a.1 + 1, (block_spec a.1).1 _ a.2.property, Nat.succ_pos _, rfl⟩

/-- The sample decides purity without any assumption on attainment of the top abscissa. -/
theorem onLine_of_bddBelow (Z : ZeroConfig) (hZ : TemperedConfig Z)
    (hnoreal : ∀ z ∈ Z.carrier, z.im ≠ 0) {T : ℝ}
    (hT : ∀ d ∈ sample,
      -T ≤ 2 * (lagStructure Z (boxSpline 1 3) (Real.log d)).re) :
    ∀ z ∈ Z.carrier, z.re = 1 / 2 := by
  by_contra h
  push Not at h
  obtain ⟨K, hK⟩ := exists_family_encoding Z hZ hnoreal h
  obtain ⟨k, hk⟩ := exists_nat_gt (max (K : ℝ) (2 * T))
  have hKk : K ≤ k := by exact_mod_cast (le_max_left (K : ℝ) (2 * T)).trans hk.le
  obtain ⟨p, hp, hneg⟩ := (block_spec k).2 (encoding Z) (family_mono hKk hK)
  have hbound := hT (p ^ (k + 1)) ⟨⟨k, p, hp⟩, rfl⟩
  rw [Nat.cast_pow, Real.log_pow] at hbound
  rw [traceSum_encoding cubic_contDiff cubic_compact _ Z hZ hnoreal] at hneg
  have hkT : 2 * T < (k : ℝ) := (le_max_right (K : ℝ) (2 * T)).trans_lt hk
  simp only [Nat.cast_add, Nat.cast_one, two_mul, Complex.add_re] at hbound hneg
  linarith

private theorem summable_occurrence {s : ℝ} (hs : 0 < s) :
    Summable (fun a : Occurrence => (degree a : ℝ) ^ (-s)) := by
  classical
  obtain ⟨N, hN⟩ := exists_nat_gt (2 / s)
  have hNs : 1 < ((N : ℝ) + 1) * s := by
    have hh := (div_lt_iff₀ hs).mp hN
    nlinarith only [hh, hs]
  let t : ℝ := ((N : ℝ) + 1) * s
  have ht : 1 < t := hNs
  have hseries : Summable (fun p : ℕ => (p : ℝ) ^ (-t)) :=
    Real.summable_nat_rpow.mpr (by linarith only [ht])
  let C : ℝ := ∑' p : ℕ, (p : ℝ) ^ (-t)
  let r : ℝ := (2 : ℝ) ^ (-s)
  have hr0 : 0 ≤ r := Real.rpow_nonneg (by norm_num) _
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_of_pos hs)
  let row : ℕ → ℝ := fun k => ∑ p ∈ block k, ((p ^ (k + 1) : ℕ) : ℝ) ^ (-s)
  have htail : Summable (fun k : ℕ => row (k + N)) := by
    apply Summable.of_nonneg_of_le
      (fun k => Finset.sum_nonneg fun p _ => Real.rpow_nonneg (Nat.cast_nonneg _) _) _
      ((summable_geometric_of_lt_one hr0 hr1).mul_right C)
    intro k
    have hterm : ∀ p ∈ block (k + N),
        ((p ^ (k + N + 1) : ℕ) : ℝ) ^ (-s) ≤ r ^ k * (p : ℝ) ^ (-t) := by
      intro p hp
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast ((block_spec (k + N)).1 p hp).two_le
      have hp0 : (0 : ℝ) < p := lt_of_lt_of_le (by norm_num) hp2
      rw [Nat.cast_pow, ← Real.rpow_natCast_mul hp0.le]
      have he : ((k + N + 1 : ℕ) : ℝ) * (-s) = (-s) * k + (-t) := by
        dsimp only [t]
        push_cast
        ring
      rw [he, Real.rpow_add hp0, Real.rpow_mul_natCast hp0.le]
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hp0.le _)
      exact pow_le_pow_left₀ (Real.rpow_nonneg hp0.le _)
        (Real.rpow_le_rpow_of_nonpos (by norm_num) hp2 (neg_nonpos.mpr hs.le)) k
    calc
      row (k + N) ≤ ∑ p ∈ block (k + N), r ^ k * (p : ℝ) ^ (-t) :=
        Finset.sum_le_sum hterm
      _ = r ^ k * ∑ p ∈ block (k + N), (p : ℝ) ^ (-t) := by rw [Finset.mul_sum]
      _ ≤ r ^ k * C := mul_le_mul_of_nonneg_left
        (hseries.sum_le_tsum _ (fun p _ => Real.rpow_nonneg (Nat.cast_nonneg _) _))
        (pow_nonneg hr0 _)
  have hrow : Summable row := (summable_nat_add_iff N).mp htail
  apply (summable_sigma_of_nonneg
    (fun a : Occurrence => Real.rpow_nonneg (Nat.cast_nonneg (degree a)) (-s))).mpr
  refine ⟨fun k => (hasSum_fintype _).summable, ?_⟩
  simpa only [degree, tsum_fintype, Finset.sum_coe_sort] using hrow

/-- Every positive Dirichlet exponent is summable on this universal decisive sample. -/
theorem summable_sample {s : ℝ} (hs : 0 < s) :
    Summable (fun d : sample => (d.val : ℝ) ^ (-s)) := by
  classical
  let select : sample → Occurrence := fun d => Classical.choose d.property
  have hselect : ∀ d : sample, degree (select d) = d.val :=
    fun d => Classical.choose_spec d.property
  have hinj : Function.Injective select := by
    intro a b hab
    apply Subtype.ext
    rw [← hselect a, ← hselect b, hab]
  exact ((summable_occurrence hs).comp_injective hinj).congr
    (fun d => by rw [hselect d])

/-- Every finite portion of the sample obeys each positive power counting bound. -/
theorem finite_count_le_rpow {s : ℝ} (hs : 0 < s) (F : Finset ℕ)
    (hF : ∀ d ∈ F, d ∈ sample) {X : ℝ} (hX : 0 ≤ X)
    (hFX : ∀ d ∈ F, (d : ℝ) ≤ X) :
    (F.card : ℝ) ≤ (∑' d : sample, (d.val : ℝ) ^ (-s)) * X ^ s := by
  classical
  let i : {d : ℕ // d ∈ F} → sample := fun d => ⟨d.val, hF d.val d.property⟩
  have hi : Function.Injective i := by
    intro a b hab
    exact Subtype.ext (congrArg Subtype.val hab)
  have hpartial : (∑ d ∈ F, (d : ℝ) ^ (-s)) ≤
      ∑' d : sample, (d.val : ℝ) ^ (-s) := by
    have h := tsum_comp_le_tsum_of_inj (summable_sample hs)
      (fun d => Real.rpow_nonneg (Nat.cast_nonneg d.val) (-s)) hi
    simpa only [Function.comp_apply, i, tsum_fintype, Finset.sum_coe_sort] using h
  have hunit : ∀ d ∈ F, (1 : ℝ) ≤ X ^ s * (d : ℝ) ^ (-s) := by
    intro d hd
    obtain ⟨p, k, hp, _, heq⟩ := sample_prime_power (hF d hd)
    have hd0 : (0 : ℝ) < d := by
      rw [heq]
      exact_mod_cast (pow_pos hp.pos k)
    have hpw := Real.rpow_le_rpow hd0.le (hFX d hd) hs.le
    have hh := mul_le_mul_of_nonneg_right hpw
      (inv_nonneg.mpr (Real.rpow_nonneg hd0.le s))
    rw [mul_inv_cancel₀ (Real.rpow_pos_of_pos hd0 s).ne'] at hh
    rwa [Real.rpow_neg hd0.le]
  calc
    (F.card : ℝ) = ∑ _d ∈ F, (1 : ℝ) := by simp
    _ ≤ ∑ d ∈ F, X ^ s * (d : ℝ) ^ (-s) := Finset.sum_le_sum hunit
    _ = X ^ s * ∑ d ∈ F, (d : ℝ) ^ (-s) := by rw [Finset.mul_sum]
    _ ≤ X ^ s * ∑' d : sample, (d.val : ℝ) ^ (-s) :=
      mul_le_mul_of_nonneg_left hpartial (Real.rpow_nonneg hX s)
    _ = _ := mul_comm _ _

/-- The counting function of the decisive sample is bounded by every positive power. -/
theorem count_le_rpow {s : ℝ} (hs : 0 < s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
      (((Finset.range (N + 1)).filter (fun d => d ∈ sample)).card : ℝ) ≤ C * (N : ℝ) ^ s := by
  classical
  refine ⟨∑' d : sample, (d.val : ℝ) ^ (-s),
    tsum_nonneg (fun d => Real.rpow_nonneg (Nat.cast_nonneg d.val) (-s)), ?_⟩
  intro N
  apply finite_count_le_rpow hs _
    (fun d hd => (Finset.mem_filter.mp hd).2) (Nat.cast_nonneg N)
  intro d hd
  have h := Finset.mem_range.mp (Finset.mem_filter.mp hd).1
  exact_mod_cast (show d ≤ N by omega)

/-- Counting sparsity can be arbitrarily strong while a one-sided sample still decides purity. -/
theorem exists_decisive_sample_of_zero_convergence_exponent :
    ∃ D : Set ℕ,
      (∀ d ∈ D, ∃ p k : ℕ, p.Prime ∧ 0 < k ∧ d = p ^ k) ∧
      (∀ s : ℝ, 0 < s → Summable (fun d : D => (d.val : ℝ) ^ (-s))) ∧
      ∀ (Z : ZeroConfig), TemperedConfig Z → (∀ z ∈ Z.carrier, z.im ≠ 0) →
        (∃ T : ℝ, ∀ d ∈ D, -T ≤ 2 * (lagStructure Z (boxSpline 1 3) (Real.log d)).re) →
        ∀ z ∈ Z.carrier, z.re = 1 / 2 := by
  refine ⟨sample, (fun _ hd => sample_prime_power hd), (fun _ hs => summable_sample hs), ?_⟩
  rintro Z hZ hnoreal ⟨T, hT⟩
  exact onLine_of_bddBelow Z hZ hnoreal hT

#print axioms exists_finite_power_block
#print axioms summable_sample
#print axioms count_le_rpow
#print axioms onLine_of_bddBelow
#print axioms exists_decisive_sample_of_zero_convergence_exponent

end ZeroExponentSample
end GaloisForLFunctions.SurfaceOfSpecZ
