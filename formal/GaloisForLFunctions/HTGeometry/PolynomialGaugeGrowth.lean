import GaloisForLFunctions.HTGeometry.NevanlinnaEntireCharacteristic
import GaloisForLFunctions.HTGeometry.SmallGrowthMeromorphicField
import GaloisForLFunctions.HTGeometry.PolynomialGrowthBound
import GaloisForLFunctions.HTGeometry.JensenCountingLowerBound
import GaloisForLFunctions.HTGeometry.TripticMultiplicativeSourceClass
import GaloisForLFunctions.Bottcher.ConnectedRepellingRootDefect

/-!
# Growth and zero-count cost of a polynomial gauge

Multiplication by a nonzero polynomial changes an entire function's Nevanlinna characteristic by
only `O(log r)` and adds at most the polynomial degree to every unintegrated zero count.  These are
the quantitative coarse-data invariants used by finite rational-gauge blindness constructions.
-/

open Complex Polynomial Set Filter

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open GaloisForLFunctions.Nevanlinna

/-- Concrete `O(log r)` bound, with `1 + log r` as a nonnegative comparison scale on `r ≥ 1`. -/
def CharacteristicLogBound (f : ℂ → ℂ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 1 ≤ r →
    ValueDistribution.characteristic f ⊤ r ≤ C * (1 + Real.log r)

/-- Every complex polynomial has logarithmic Nevanlinna characteristic. -/
theorem characteristicLogBound_polynomial (P : Polynomial ℂ) :
    CharacteristicLogBound (fun z => P.eval z) := by
  let C0 := coeffNormSum P
  let n : ℝ := P.natDegree
  let C := Real.posLog C0 + n * (Real.log 2 + 1)
  refine ⟨C, ?_, ?_⟩
  · have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    exact add_nonneg Real.posLog_nonneg
      (mul_nonneg (Nat.cast_nonneg _) (by linarith))
  intro r hr
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hlogr : 0 ≤ Real.log r := Real.log_nonneg hr
  have han : AnalyticOnNhd ℂ (fun z => P.eval z) Set.univ :=
    P.differentiable.differentiableOn.analyticOnNhd isOpen_univ
  have hchar := characteristic_top_le_posLog_of_bound han (r := r)
    (M := C0 * (1 + r) ^ P.natDegree) (by
      intro z hz
      have hz' : ‖z‖ = r := by
        simpa [Metric.mem_sphere, abs_of_pos hr0, dist_zero_right] using hz
      simpa [C0, hz'] using norm_eval_le_coeffNormSum P z)
  have hpos : Real.posLog (C0 * (1 + r) ^ P.natDegree) ≤
      Real.posLog C0 + n * Real.posLog (1 + r) := by
    calc
      Real.posLog (C0 * (1 + r) ^ P.natDegree) ≤
          Real.posLog C0 + Real.posLog ((1 + r) ^ P.natDegree) := Real.posLog_mul
      _ = Real.posLog C0 + n * Real.posLog (1 + r) := by
        rw [Real.posLog_pow]
  have hlog1 : Real.posLog (1 + r) = Real.log (1 + r) := by
    rw [Real.posLog_eq_log (by rw [abs_of_nonneg (by linarith)]; linarith)]
  have hlogle : Real.log (1 + r) ≤ Real.log 2 + Real.log r := by
    rw [← Real.log_mul (by norm_num) hr0.ne']
    exact Real.log_le_log (by positivity) (by linarith)
  dsimp [C, n]
  apply hchar.trans
  apply hpos.trans
  rw [hlog1]
  have hn : (0 : ℝ) ≤ P.natDegree := Nat.cast_nonneg _
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  calc
    Real.posLog C0 + (↑P.natDegree : ℝ) * Real.log (1 + r) ≤
        Real.posLog C0 + (↑P.natDegree : ℝ) * (Real.log 2 + Real.log r) := by
      simpa [add_comm] using
        add_le_add_left (mul_le_mul_of_nonneg_left hlogle hn) (Real.posLog C0)
    _ ≤ (Real.posLog C0 + (↑P.natDegree : ℝ) * (Real.log 2 + 1)) *
        (1 + Real.log r) := by
      have hA : 0 ≤ Real.posLog C0 := Real.posLog_nonneg
      nlinarith [hA, mul_nonneg hA hlogr, mul_nonneg hn hlog2,
        mul_nonneg (mul_nonneg hn hlog2) hlogr]

/-- Two meromorphic characteristics differ by `O(log r)`. -/
def CharacteristicLogEquivalent (f g : ℂ → ℂ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 1 ≤ r →
    |ValueDistribution.characteristic f ⊤ r -
      ValueDistribution.characteristic g ⊤ r| ≤ C * (1 + Real.log r)

/-- Multiplication by a nonzero polynomial changes characteristic by only `O(log r)`. -/
theorem characteristicLogEquivalent_mul_polynomial
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Set.univ)
    (hfne : ∃ z, f z ≠ 0) (P : Polynomial ℂ) (hPne : ∃ z, P.eval z ≠ 0) :
    CharacteristicLogEquivalent (fun z => P.eval z * f z) f := by
  let p : ℂ → ℂ := fun z => P.eval z
  have hpAn : AnalyticOnNhd ℂ p Set.univ :=
    P.differentiable.differentiableOn.analyticOnNhd isOpen_univ
  have hpMero : Meromorphic p := fun z => (hpAn z (Set.mem_univ z)).meromorphicAt
  have hfMero : Meromorphic f := fun z => (hf z (Set.mem_univ z)).meromorphicAt
  have hpMeroOn : MeromorphicOn p Set.univ := fun z _ => hpMero z
  have hfMeroOn : MeromorphicOn f Set.univ := fun z _ => hfMero z
  have hpDiff : Differentiable ℂ p := P.differentiable
  obtain ⟨zp, hzp⟩ := hPne
  obtain ⟨zf, hzf⟩ := hfne
  have hpOrder : ∀ z, meromorphicOrderAt p z ≠ ⊤ := by
    intro z
    rw [(hpAn z (Set.mem_univ z)).meromorphicOrderAt_eq]
    have hz := GaloisForLFunctions.analyticOrderAt_ne_top_of_entire hpDiff hzp z
    simp [hz]
  have hfDiff : Differentiable ℂ f :=
    Complex.analyticOnNhd_univ_iff_differentiable.mp hf
  have hfOrder : ∀ z, meromorphicOrderAt f z ≠ ⊤ := by
    intro z
    rw [(hf z (Set.mem_univ z)).meromorphicOrderAt_eq]
    have hz := GaloisForLFunctions.analyticOrderAt_ne_top_of_entire hfDiff hzf z
    simp [hz]
  let F : ℂ → ℂ := fun z => p z * f z
  have hFMero : Meromorphic F := fun z =>
    (hpAn z (Set.mem_univ z)).meromorphicAt.mul (hf z (Set.mem_univ z)).meromorphicAt
  have hFMeroOn : MeromorphicOn F Set.univ := fun z _ => hFMero z
  have hFOrder : ∀ z, meromorphicOrderAt F z ≠ ⊤ :=
    meromorphicOrderAt_mul_ne_top hpMeroOn hfMeroOn hpOrder hfOrder
  have hpInvMero : Meromorphic p⁻¹ := hpMero.inv
  have hpInvOrder : ∀ z, meromorphicOrderAt p⁻¹ z ≠ ⊤ := by
    intro z
    rw [meromorphicOrderAt_inv]
    simp [hpOrder z]
  have hnonzero : ∀ᶠ z in Filter.codiscrete ℂ, p z ≠ 0 := by
    change {z | p z ≠ 0} ∈ Filter.codiscreteWithin (Set.univ : Set ℂ)
    rw [mem_codiscreteWithin_iff_forall_mem_nhdsNE]
    intro z _
    simp only [Set.compl_univ, Set.union_empty]
    change ∀ᶠ x in nhdsWithin z {z}ᶜ, p x ≠ 0
    exact (meromorphicOrderAt_ne_top_iff_eventually_ne_zero
      (hpMero z)).mp (hpOrder z)
  have hrecover : f =ᶠ[Filter.codiscrete ℂ] F * p⁻¹ := by
    filter_upwards [hnonzero] with z hz
    simp only [F, Pi.mul_apply, Pi.inv_apply]
    field_simp
  obtain ⟨Cp, hCp0, hCp⟩ := characteristicLogBound_polynomial P
  let Cinv : ℝ := max |Real.log ‖p 0‖|
    |Real.log ‖meromorphicTrailingCoeffAt p 0‖|
  have hCinv0 : 0 ≤ Cinv := le_max_of_le_left (abs_nonneg _)
  refine ⟨Cp + Cinv, add_nonneg hCp0 hCinv0, ?_⟩
  intro r hr
  have hr0 : r ≠ 0 := (lt_of_lt_of_le zero_lt_one hr).ne'
  have hlogr : 0 ≤ Real.log r := Real.log_nonneg hr
  have hscale : 1 ≤ 1 + Real.log r := by linarith
  have hpChar := hCp r hr
  have hforward : ValueDistribution.characteristic F ⊤ r -
      ValueDistribution.characteristic f ⊤ r ≤ Cp * (1 + Real.log r) := by
    have hmul := GaloisForLFunctions.Nevanlinna.characteristic_mul_le hpAn hf r
    change ValueDistribution.characteristic F ⊤ r ≤
      ValueDistribution.characteristic p ⊤ r +
        ValueDistribution.characteristic f ⊤ r at hmul
    have hpChar' : ValueDistribution.characteristic p ⊤ r ≤
        Cp * (1 + Real.log r) := by simpa [p] using hpChar
    linarith
  have hinvDiff : ValueDistribution.characteristic p⁻¹ ⊤ r ≤
      ValueDistribution.characteristic p ⊤ r + Cinv := by
    have h := ValueDistribution.characteristic_sub_characteristic_inv_le
      (f := p) (R := r) hpMero
    change |ValueDistribution.characteristic p ⊤ r -
      ValueDistribution.characteristic p⁻¹ ⊤ r| ≤ Cinv at h
    linarith [(abs_le.mp h).1]
  have hreChar : ValueDistribution.characteristic f ⊤ r =
      ValueDistribution.characteristic (F * p⁻¹) ⊤ r :=
    characteristic_congr_codiscrete hfMero (hFMero.mul hpInvMero) hrecover hr0
  have hbackward : ValueDistribution.characteristic f ⊤ r -
      ValueDistribution.characteristic F ⊤ r ≤
        (Cp + Cinv) * (1 + Real.log r) := by
    have hmul := ValueDistribution.characteristic_mul_top_le hr
      hFMero hFOrder hpInvMero hpInvOrder
    rw [hreChar]
    change ValueDistribution.characteristic (F * p⁻¹) ⊤ r -
      ValueDistribution.characteristic F ⊤ r ≤ _
    have hsum : ValueDistribution.characteristic (F * p⁻¹) ⊤ r ≤
        ValueDistribution.characteristic F ⊤ r +
          ValueDistribution.characteristic p⁻¹ ⊤ r := by
      simpa using hmul
    nlinarith [mul_nonneg hCp0 hlogr, mul_nonneg hCinv0 hlogr]
  rw [abs_le]
  constructor
  · linarith
  · exact hforward.trans (mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_right hCinv0) (by linarith))

/-- Divisors of nonzero entire products add pointwise. -/
theorem divisor_mul_eq_add_of_finiteOrder
    {f g : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Set.univ)
    (hg : AnalyticOnNhd ℂ g Set.univ)
    (hfOrder : ∀ z, meromorphicOrderAt f z ≠ ⊤)
    (hgOrder : ∀ z, meromorphicOrderAt g z ≠ ⊤)
    (U : Set ℂ) (z : ℂ) :
    MeromorphicOn.divisor (f * g) U z =
      MeromorphicOn.divisor f U z + MeromorphicOn.divisor g U z := by
  by_cases hz : z ∈ U
  · have hfM : MeromorphicOn f U := fun w _ =>
      (hf w (Set.mem_univ w)).meromorphicAt
    have hgM : MeromorphicOn g U := fun w _ =>
      (hg w (Set.mem_univ w)).meromorphicAt
    have hfgM : MeromorphicOn (f * g) U := hfM.mul hgM
    rw [hfgM.divisor_apply hz, hfM.divisor_apply hz, hgM.divisor_apply hz,
      meromorphicOrderAt_mul
        (hf z (Set.mem_univ z)).meromorphicAt
        (hg z (Set.mem_univ z)).meromorphicAt]
    exact WithTop.untopD_add (hfOrder z) (hgOrder z)
  · simp [hz]

/-- Unintegrated zero counts of nonzero entire products add exactly. -/
theorem zeroCount_mul_eq_add
    {f g : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Set.univ)
    (hg : AnalyticOnNhd ℂ g Set.univ)
    (hfOrder : ∀ z, meromorphicOrderAt f z ≠ ⊤)
    (hgOrder : ∀ z, meromorphicOrderAt g z ≠ ⊤)
    (c : ℂ) (R : ℝ) :
    zeroCount (f * g) c R = zeroCount f c R + zeroCount g c R := by
  have hfs : (Function.support fun u =>
      (MeromorphicOn.divisor f (Metric.closedBall c R) u : ℝ)).Finite := by
    refine ((MeromorphicOn.divisor f (Metric.closedBall c R)).finiteSupport
      (isCompact_closedBall ..)).subset ?_
    intro u hu
    simp only [Function.mem_support, ne_eq] at hu
    exact_mod_cast fun h => hu (by rw [h]; simp)
  have hgs : (Function.support fun u =>
      (MeromorphicOn.divisor g (Metric.closedBall c R) u : ℝ)).Finite := by
    refine ((MeromorphicOn.divisor g (Metric.closedBall c R)).finiteSupport
      (isCompact_closedBall ..)).subset ?_
    intro u hu
    simp only [Function.mem_support, ne_eq] at hu
    exact_mod_cast fun h => hu (by rw [h]; simp)
  rw [zeroCount, zeroCount, zeroCount]
  have heq : (fun u =>
      (MeromorphicOn.divisor (f * g) (Metric.closedBall c R) u : ℝ)) =
      fun u => (MeromorphicOn.divisor f (Metric.closedBall c R) u : ℝ) +
        (MeromorphicOn.divisor g (Metric.closedBall c R) u : ℝ) := by
    funext u
    rw [divisor_mul_eq_add_of_finiteOrder hf hg hfOrder hgOrder]
    push_cast
    rfl
  rw [heq, finsum_add_distrib hfs hgs]

/-- A degree-`d` polynomial contributes at most `d` zeros in every closed ball. -/
theorem zeroCount_polynomial_le_natDegree
    (P : Polynomial ℂ) (hP : P ≠ 0) (c : ℂ) (R : ℝ) :
    zeroCount (fun z => P.eval z) c R ≤ P.natDegree := by
  classical
  let p : ℂ → ℂ := fun z => P.eval z
  let B := Metric.closedBall c R
  have hpAn : AnalyticOnNhd ℂ p Set.univ :=
    P.differentiable.differentiableOn.analyticOnNhd isOpen_univ
  have hpM : MeromorphicOn p B := fun z _ =>
    (hpAn z (Set.mem_univ z)).meromorphicAt
  have hsupp : Function.support (fun u =>
      (MeromorphicOn.divisor p B u : ℝ)) ⊆ (P.roots.toFinset : Set ℂ) := by
    intro u hu
    simp only [Function.mem_support, ne_eq] at hu
    by_contra hroot
    have hroot' : u ∉ P.roots := by simpa using hroot
    have hval : P.eval u ≠ 0 := by
      simpa [Polynomial.IsRoot] using
        (not_congr (Polynomial.mem_roots hP)).mp hroot'
    by_cases huB : u ∈ B
    · rw [hpM.divisor_apply huB,
        (hpAn u (Set.mem_univ u)).meromorphicOrderAt_eq,
        (hpAn u (Set.mem_univ u)).analyticOrderAt_eq_zero.mpr hval] at hu
      simp at hu
    · simp [huB] at hu
  rw [zeroCount]
  change (∑ᶠ u, (MeromorphicOn.divisor p B u : ℝ)) ≤ _
  rw [finsum_eq_sum_of_support_subset _ hsupp]
  calc
    ∑ u ∈ P.roots.toFinset, (MeromorphicOn.divisor p B u : ℝ) ≤
        ∑ u ∈ P.roots.toFinset, (P.roots.count u : ℝ) := by
      apply Finset.sum_le_sum
      intro u hu
      by_cases huB : u ∈ B
      · rw [hpM.divisor_apply huB,
          (hpAn u (Set.mem_univ u)).meromorphicOrderAt_eq,
          Bottcher.analyticOrderAt_polynomial_eval_eq_rootMultiplicity hP,
          ← Polynomial.count_roots]
        simp
      · simp [huB]
    _ = (P.roots.card : ℝ) := by
      exact_mod_cast Multiset.sum_count_eq_card
        (fun a ha => Multiset.mem_toFinset.mpr ha)
    _ ≤ P.natDegree := by
      exact_mod_cast (by
        have hc := Polynomial.card_roots hP
        simpa [Polynomial.degree_eq_natDegree hP] using hc)

end

end GaloisForLFunctions.HTGeometry
