import GaloisForLFunctions.RHTower.SteinhausFiniteCharacterCells

/-!
# Exact second moments with a finite prime prefix frozen

Freezing finitely many prime phases retains off-diagonal terms: two characters have nonzero
correlation exactly when their factorisations agree outside the frozen prefix. The surviving
correlation is their prescribed-prefix phase. Finite complex-weighted carriers therefore have
an exact second moment equal to a sum of squared coefficient sums, grouped by exterior
factorisation.

This supplies the literal background source formula needed alongside the covariance event.
It retains all prefix-dependent cancellation and makes no uniform background bound, local-target
probability, or recurrence assertion.
-/

noncomputable section
open MeasureTheory Filter Topology Finset Complex
namespace RHTower
open SteinhausModel

/-- Freeze a finite prime-coordinate prefix and retain all remaining independent coordinates. -/
def freezeSteinhausPrefix (S : Finset ℕ) (omega eta : Omega) : Omega := fun p =>
  if p ∈ S then omega p else eta p

theorem continuous_freezeSteinhausPrefix (S : Finset ℕ) (omega : Omega) :
    Continuous (freezeSteinhausPrefix S omega) := by
  apply continuous_pi
  intro p
  by_cases hp : p ∈ S
  · simpa only [freezeSteinhausPrefix, if_pos hp] using continuous_const (y := omega p)
  · simpa only [freezeSteinhausPrefix, if_neg hp] using continuous_apply p

theorem integrable_frozenPrefix_character_pair (S : Finset ℕ) (omega : Omega) (n m : ℕ) :
    Integrable (fun eta => X n (freezeSteinhausPrefix S omega eta) *
      (starRingEnd ℂ) (X m (freezeSteinhausPrefix S omega eta))) steinhausMeasure := by
  apply Integrable.mono' (integrable_const (1 : ℝ))
  · exact (((continuous_steinhausCharacter n).comp (continuous_freezeSteinhausPrefix S omega)).mul
      (((continuous_steinhausCharacter m).comp (continuous_freezeSteinhausPrefix S omega)).star)).aestronglyMeasurable
  · filter_upwards with eta
    rw [norm_mul, norm_X, RCLike.norm_conj, norm_X, one_mul]

/-- The exact frozen-prefix character kernel, before collecting equal exterior frequencies. -/
theorem integral_frozenPrefix_character_pair_product (S : Finset ℕ) (omega : Omega) (n m : ℕ) :
    (∫ eta, X n (freezeSteinhausPrefix S omega eta) *
        (starRingEnd ℂ) (X m (freezeSteinhausPrefix S omega eta)) ∂steinhausMeasure) =
      ∏ p ∈ n.primeFactors ∪ m.primeFactors,
        if p ∈ S then charFactor (freq n m p) (omega p)
        else if freq n m p = 0 then 1 else 0 := by
  classical
  let T := n.primeFactors ∪ m.primeFactors
  let g : ℕ → ℝ → ℂ := fun p t =>
    if p ∈ S then charFactor (freq n m p) (omega p) else charFactor (freq n m p) t
  have hpoint : ∀ eta : Omega,
      X n (freezeSteinhausPrefix S omega eta) *
        (starRingEnd ℂ) (X m (freezeSteinhausPrefix S omega eta)) =
      ∏ p ∈ T, g p (eta p) := by
    intro eta
    rw [X_mul_conj_eq_prod]
    apply Finset.prod_congr rfl
    intro p _
    by_cases hp : p ∈ S <;> simp only [freezeSteinhausPrefix, g, hp, if_true, if_false]
  have hcont : Continuous fun y : (i : ↥T) → ℝ => ∏ i : ↥T, g i (y i) := by
    apply continuous_finsetProd
    intro i _
    by_cases hi : i.val ∈ S
    · simpa only [g, hi, if_true] using continuous_const (y := charFactor (freq n m i.val) (omega i.val))
    · dsimp only [g]
      simp only [if_neg hi]
      unfold charFactor
      fun_prop
  have hmap : Measure.map T.restrict steinhausMeasure =
      Measure.pi (fun _ : ↥T => volume.restrict (Set.Icc (0 : ℝ) 1)) := by
    unfold steinhausMeasure
    exact Measure.infinitePi_map_restrict _
  have hfinite : (∫ eta, ∏ p ∈ T, g p (eta p) ∂steinhausMeasure) =
      ∫ y : (i : ↥T) → ℝ, ∏ i : ↥T, g i (y i)
        ∂Measure.pi (fun _ : ↥T => volume.restrict (Set.Icc (0 : ℝ) 1)) := by
    rw [← hmap, integral_map (Finset.measurable_restrict T).aemeasurable hcont.aestronglyMeasurable]
    apply integral_congr_ae
    filter_upwards with eta
    rw [← Finset.prod_coe_sort T (fun p => g p (eta p))]
    rfl
  rw [integral_congr_ae (Filter.Eventually.of_forall hpoint), hfinite,
    integral_fintype_prod_eq_prod]
  rw [Finset.prod_coe_sort T (fun p => ∫ t, g p t ∂(volume.restrict (Set.Icc (0 : ℝ) 1)))]
  apply Finset.prod_congr rfl
  intro p _
  by_cases hp : p ∈ S
  · simp [g, hp]
  · simp only [g, if_neg hp, charInt]


/-- The factorisation visible to random coordinates outside a fixed finite prefix. -/
def steinhausExteriorFactorization (S : Finset ℕ) (n : ℕ) : ℕ →₀ ℕ :=
  n.factorization.filter (fun p => p ∉ S)

theorem steinhausExteriorFactorization_eq_iff (S : Finset ℕ) (n m : ℕ) :
    steinhausExteriorFactorization S n = steinhausExteriorFactorization S m ↔
      ∀ p, p ∉ S → n.factorization p = m.factorization p := by
  constructor
  · intro h p hp
    have heq := congrArg (fun f : ℕ →₀ ℕ => f p) h
    simpa only [steinhausExteriorFactorization, Finsupp.filter_apply, if_pos hp] using heq
  · intro h
    ext p
    by_cases hp : p ∉ S
    · simp only [steinhausExteriorFactorization, Finsupp.filter_apply, if_pos hp, h p hp]
    · simp only [steinhausExteriorFactorization, Finsupp.filter_apply, if_neg hp]

/-- Free coordinates kill exactly the pairs with distinct exterior factorisations. -/
theorem integral_frozenPrefix_character_pair (S : Finset ℕ) (omega : Omega) (n m : ℕ) :
    (∫ eta, X n (freezeSteinhausPrefix S omega eta) *
        (starRingEnd ℂ) (X m (freezeSteinhausPrefix S omega eta)) ∂steinhausMeasure) =
      if steinhausExteriorFactorization S n = steinhausExteriorFactorization S m then
        X n (freezeSteinhausPrefix S omega 0) * (starRingEnd ℂ) (X m (freezeSteinhausPrefix S omega 0))
      else 0 := by
  classical
  rw [integral_frozenPrefix_character_pair_product]
  by_cases heq : steinhausExteriorFactorization S n = steinhausExteriorFactorization S m
  · rw [if_pos heq, X_mul_conj_eq_prod]
    apply Finset.prod_congr rfl
    intro p _
    by_cases hp : p ∈ S
    · simp only [if_pos hp, freezeSteinhausPrefix]
    · have hfac := (steinhausExteriorFactorization_eq_iff S n m).mp heq p hp
      have hfreq : freq n m p = 0 := by simp only [freq, hfac, sub_self]
      simp only [if_neg hp, hfreq, charFactor_zero, if_true]
  · rw [if_neg heq]
    have hdiff : ∃ p, p ∉ S ∧ n.factorization p ≠ m.factorization p := by
      by_contra h
      push Not at h
      exact heq ((steinhausExteriorFactorization_eq_iff S n m).mpr h)
    obtain ⟨p, hpS, hfac⟩ := hdiff
    have hpT : p ∈ n.primeFactors ∪ m.primeFactors := by
      by_contra hp
      have hn : n.factorization p = 0 := by
        by_contra hn
        apply hp
        apply Finset.mem_union_left
        rw [← Nat.support_factorization]
        exact Finsupp.mem_support_iff.mpr hn
      have hm : m.factorization p = 0 := by
        by_contra hm
        apply hp
        apply Finset.mem_union_right
        rw [← Nat.support_factorization]
        exact Finsupp.mem_support_iff.mpr hm
      exact hfac (hn.trans hm.symm)
    have hfreq : freq n m p ≠ 0 := by
      unfold freq
      apply sub_ne_zero.mpr
      exact_mod_cast hfac
    apply Finset.prod_eq_zero hpT
    rw [if_neg hpS, if_neg hfreq]


/-- Finite frozen-prefix covariance retains precisely the exterior-frequency blocks. -/
theorem integral_frozenPrefix_dpoly_mul_conj (S : Finset ℕ) (omega : Omega)
    (a : ℕ → ℂ) (s : Finset ℕ) :
    (∫ eta, (∑ n ∈ s, a n * X n (freezeSteinhausPrefix S omega eta)) *
      (starRingEnd ℂ) (∑ n ∈ s, a n * X n (freezeSteinhausPrefix S omega eta)) ∂steinhausMeasure) =
      ∑ n ∈ s, ∑ m ∈ s,
        if steinhausExteriorFactorization S n = steinhausExteriorFactorization S m then
          (a n * X n (freezeSteinhausPrefix S omega 0)) *
            (starRingEnd ℂ) (a m * X m (freezeSteinhausPrefix S omega 0)) else 0 := by
  classical
  have hexp : ∀ eta : Omega,
      (∑ n ∈ s, a n * X n (freezeSteinhausPrefix S omega eta)) *
        (starRingEnd ℂ) (∑ n ∈ s, a n * X n (freezeSteinhausPrefix S omega eta)) =
      ∑ n ∈ s, ∑ m ∈ s, (a n * (starRingEnd ℂ) (a m)) *
        (X n (freezeSteinhausPrefix S omega eta) *
          (starRingEnd ℂ) (X m (freezeSteinhausPrefix S omega eta))) := by
    intro eta
    rw [map_sum, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    apply Finset.sum_congr rfl
    intro m _
    rw [map_mul]
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hexp)]
  rw [integral_finsetSum _ (fun n _ => integrable_finsetSum _
    (fun m _ => (integrable_frozenPrefix_character_pair S omega n m).const_mul _))]
  apply Finset.sum_congr rfl
  intro n _
  rw [integral_finsetSum _ (fun m _ => (integrable_frozenPrefix_character_pair S omega n m).const_mul _)]
  apply Finset.sum_congr rfl
  intro m _
  rw [integral_const_mul, integral_frozenPrefix_character_pair]
  split_ifs
  · rw [map_mul]
    ring
  · rw [mul_zero]

private theorem sum_equal_fibres {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (s : Finset ι) (g : ι → κ) (b : ι → ℂ) :
    (∑ n ∈ s, ∑ m ∈ s, if g n = g m then b n * (starRingEnd ℂ) (b m) else 0) =
      ∑ q ∈ s.image g, (∑ n ∈ s.filter (fun n => g n = q), b n) *
        (starRingEnd ℂ) (∑ n ∈ s.filter (fun n => g n = q), b n) := by
  classical
  have hgroup := Finset.sum_fiberwise_of_maps_to (s := s) (t := s.image g) (g := g)
    (fun n hn => Finset.mem_image_of_mem g hn)
    (fun n => ∑ m ∈ s.filter (fun m => g m = g n), b n * (starRingEnd ℂ) (b m))
  calc
    _ = ∑ n ∈ s, ∑ m ∈ s.filter (fun m => g m = g n), b n * (starRingEnd ℂ) (b m) := by
      apply Finset.sum_congr rfl
      intro n _
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro m _
      simp only [eq_comm]
    _ = ∑ q ∈ s.image g, ∑ n ∈ s.filter (fun n => g n = q),
        ∑ m ∈ s.filter (fun m => g m = g n), b n * (starRingEnd ℂ) (b m) := hgroup.symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro q _
      rw [map_sum, Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      rw [(Finset.mem_filter.mp hn).2]

/-- Exact positive-block formula for the second moment with a finite prime prefix frozen. -/
theorem integral_normSq_frozenPrefix_dpoly (S : Finset ℕ) (omega : Omega)
    (a : ℕ → ℂ) (s : Finset ℕ) :
    (∫ eta, ‖∑ n ∈ s, a n * X n (freezeSteinhausPrefix S omega eta)‖ ^ 2 ∂steinhausMeasure) =
      ∑ q ∈ s.image (steinhausExteriorFactorization S),
        ‖∑ n ∈ s.filter (fun n => steinhausExteriorFactorization S n = q),
          a n * X n (freezeSteinhausPrefix S omega 0)‖ ^ 2 := by
  have h := integral_frozenPrefix_dpoly_mul_conj S omega a s
  rw [sum_equal_fibres] at h
  have hpoint : ∀ eta : Omega,
      (∑ n ∈ s, a n * X n (freezeSteinhausPrefix S omega eta)) *
        (starRingEnd ℂ) (∑ n ∈ s, a n * X n (freezeSteinhausPrefix S omega eta)) =
      ((‖∑ n ∈ s, a n * X n (freezeSteinhausPrefix S omega eta)‖ ^ 2 : ℝ) : ℂ) := by
    intro eta
    rw [Complex.mul_conj']
    push_cast
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpoint), integral_complex_ofReal] at h
  have hsum : (∑ q ∈ s.image (steinhausExteriorFactorization S),
      (∑ n ∈ s.filter (fun n => steinhausExteriorFactorization S n = q),
        a n * X n (freezeSteinhausPrefix S omega 0)) *
      (starRingEnd ℂ) (∑ n ∈ s.filter (fun n => steinhausExteriorFactorization S n = q),
        a n * X n (freezeSteinhausPrefix S omega 0))) =
      ((∑ q ∈ s.image (steinhausExteriorFactorization S),
        ‖∑ n ∈ s.filter (fun n => steinhausExteriorFactorization S n = q),
          a n * X n (freezeSteinhausPrefix S omega 0)‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    apply Finset.sum_congr rfl
    intro q _
    rw [Complex.mul_conj']
  rw [hsum] at h
  exact_mod_cast h

end RHTower
