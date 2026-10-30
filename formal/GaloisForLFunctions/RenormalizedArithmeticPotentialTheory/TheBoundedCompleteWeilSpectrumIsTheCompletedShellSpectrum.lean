import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheBoundedCompleteWeilSpectrumIsTheAdjunctionSpectrum
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheNonRatioPrimeRowsSplitIntoDownwardAndUpward
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.MacroscopicOverlapSpectralAssembly
import GaloisForLFunctions.BiScaleUncertainty.SieveCoordinateSupNorm

/-!
# The bounded complete-Weil spectrum is the completed shell spectrum

At a fixed overlap ratio the low spectrum of the complete Weil matrix is counted, with
multiplicity, by the conductors whose completed energy lies below the threshold.

* **Lower count from quasimodes** (`card_le_lowerSpectralWindow_of_quasimodes`): `k` almost
  orthonormal vectors with small residuals against energies `≤ T − δ` force `k` eigenvalues
  below `T`. On their span the form is `< T‖x‖²`, while a nonzero vector of the span orthogonal to
  the low eigenvectors would have form `≥ T‖x‖²`; rank then bounds `k`. Coincident energies are
  allowed.
* **Finite completed sublevels** (`finite_completedConductorEnergy_sublevel`): the shell correction
  is bounded uniformly in the conductor since `|c_m(h)| ≤ φ(m)`, so every sublevel of `E_m(c)` lies in
  a sublevel of the reference energy.
* **Exact counts** (`eventually_completeWeil_spectral_count_eq_of_reserve_quasimodes`): a
  prime-defect reserve and norm quasimodes give, for every threshold `T` off the energy set,
  `#{eigenvalues < T} = #{m ≥ 1 : E_m < T}` eventually.
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped RealInnerProductSpace Classical

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open CompletedShell BezoutValuationIncidence

section MinMax

variable {I K : Type*} [Fintype I] [DecidableEq I] [Fintype K] {A : Matrix I I ℝ}

/-- The form of an almost orthonormal quasimode combination lies below `T` by a definite
fraction of its coefficient mass. -/
theorem inner_quasimode_combination_sub_le (T : ℝ) (v : K → EuclideanSpace ℝ I) (E : K → ℝ)
    {δ η ρ B : ℝ} (hη0 : 0 ≤ η) (hρ0 : 0 ≤ ρ) (hE : ∀ k, E k ≤ T - δ) (hB : ∀ k, |E k - T| ≤ B)
    (hgram : ∀ k l, |⟪v k, v l⟫ - if k = l then 1 else 0| ≤ η)
    (hres : ∀ k, ‖Matrix.toEuclideanLin A (v k) - E k • v k‖ ≤ ρ)
    (hη : (Fintype.card K : ℝ) * η ≤ 1) (a : K → ℝ) :
    ⟪Matrix.toEuclideanLin A (∑ k, a k • v k), ∑ k, a k • v k⟫ -
        T * ‖∑ k, a k • v k‖ ^ 2 ≤
      (-δ + (Fintype.card K : ℝ) * B * η + ρ * ((Fintype.card K : ℝ) + 1)) *
        ∑ k, a k ^ 2 := by
  set x := ∑ k, a k • v k with hx
  set S := ∑ k, a k ^ 2 with hS
  set P := ∑ k, |a k| with hP
  set g : K → K → ℝ := fun k l => ⟪v k, v l⟫ - if k = l then 1 else 0 with hg
  set r : K → EuclideanSpace ℝ I := fun k => Matrix.toEuclideanLin A (v k) - E k • v k with hr
  have hS0 : 0 ≤ S := sum_nonneg fun k _ => sq_nonneg _
  have hP0 : 0 ≤ P := sum_nonneg fun k _ => abs_nonneg _
  have hPS : P ^ 2 ≤ (Fintype.card K : ℝ) * S := by
    have h := sq_sum_le_card_mul_sum_sq (s := (univ : Finset K)) (f := fun k => |a k|)
    simpa only [sq_abs, card_univ] using h
  -- coordinates of `x` against the trial vectors
  have hvx : ∀ k, ⟪v k, x⟫ = a k + ∑ l, a l * g k l := by
    intro k
    have h1 : ⟪v k, x⟫ = ∑ l, a l * ⟪v k, v l⟫ := by
      simp only [hx, inner_sum, real_inner_smul_right]
    have h2 : ∑ l, a l * ⟪v k, v l⟫ =
        ∑ l, a l * (if k = l then 1 else 0) + ∑ l, a l * g k l := by
      rw [← sum_add_distrib]
      exact Finset.sum_congr rfl fun l _ => by simp only [hg]; ring
    rw [h1, h2]
    simp only [mul_ite, mul_one, mul_zero, sum_ite_eq, mem_univ, if_true]
  -- double sums against `g` are controlled by `η P²`
  have hdouble : ∀ (w : K → ℝ) (C : ℝ), (∀ k, |w k| ≤ C) →
      ∑ k, a k * w k * ∑ l, a l * g k l ≤ C * η * P ^ 2 := by
    intro w C hw
    have hrow : ∀ k, |∑ l, a l * g k l| ≤ η * P := by
      intro k
      refine (abs_sum_le_sum_abs _ _).trans ?_
      rw [hP, mul_sum]
      exact Finset.sum_le_sum fun l _ => by
        rw [abs_mul, mul_comm η]
        exact mul_le_mul_of_nonneg_left (hgram k l) (abs_nonneg _)
    calc ∑ k, a k * w k * ∑ l, a l * g k l
        ≤ ∑ k, |a k * w k * ∑ l, a l * g k l| :=
          (le_abs_self _).trans (abs_sum_le_sum_abs _ _)
      _ ≤ ∑ k, |a k| * (C * (η * P)) := Finset.sum_le_sum fun k _ => by
          rw [abs_mul, abs_mul, mul_assoc]
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul (hw k) (hrow k) (abs_nonneg _) ((abs_nonneg _).trans (hw k)))
            (abs_nonneg _)
      _ = C * η * P ^ 2 := by rw [← sum_mul, ← hP]; ring
  -- the norm of `x`
  have hnorm : ‖x‖ ^ 2 = S + ∑ k, a k * 1 * ∑ l, a l * g k l := by
    rw [← real_inner_self_eq_norm_sq]
    have h1 : ⟪x, x⟫ = ∑ k, a k * ⟪v k, x⟫ := by
      show ⟪∑ k, a k • v k, x⟫ = _
      simp only [sum_inner, real_inner_smul_left]
    rw [h1, hS, ← sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by rw [hvx]; ring
  have hnorm_le : ‖x‖ ^ 2 ≤ S + η * P ^ 2 := by
    have := hdouble (fun _ => 1) 1 (fun _ => by simp)
    rw [hnorm]
    linarith
  -- the form of `x`
  have hform : ⟪Matrix.toEuclideanLin A x, x⟫ - T * ‖x‖ ^ 2 =
      ∑ k, a k * (E k - T) * a k + ∑ k, a k * (E k - T) * ∑ l, a l * g k l +
        ∑ k, a k * ⟪r k, x⟫ := by
    have hAx : ⟪Matrix.toEuclideanLin A x, x⟫ = ∑ k, a k * (E k * ⟪v k, x⟫ + ⟪r k, x⟫) := by
      have : Matrix.toEuclideanLin A x = ∑ k, a k • (E k • v k + r k) := by
        rw [hx, map_sum]
        exact Finset.sum_congr rfl fun k _ => by
          rw [map_smul]
          simp only [hr, add_sub_cancel]
      rw [this]
      simp only [sum_inner, real_inner_smul_left, inner_add_left]
    have hxx : T * ‖x‖ ^ 2 = ∑ k, a k * (T * ⟪v k, x⟫) := by
      rw [← real_inner_self_eq_norm_sq]
      show T * ⟪∑ k, a k • v k, x⟫ = _
      simp only [sum_inner, real_inner_smul_left, mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [hAx, hxx, ← sum_sub_distrib, ← sum_add_distrib, ← sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by rw [hvx]; ring
  -- the three pieces
  have h1 : ∑ k, a k * (E k - T) * a k ≤ -δ * S := by
    rw [hS, mul_sum]
    exact Finset.sum_le_sum fun k _ => by nlinarith [hE k, sq_nonneg (a k)]
  have h2 := hdouble (fun k => E k - T) B hB
  have h3 : ∑ k, a k * ⟪r k, x⟫ ≤ ρ * ((P ^ 2 + ‖x‖ ^ 2) / 2) := by
    calc ∑ k, a k * ⟪r k, x⟫ ≤ ∑ k, |a k| * (ρ * ‖x‖) := Finset.sum_le_sum fun k _ => by
          refine (le_abs_self _).trans ?_
          rw [abs_mul]
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          exact (abs_real_inner_le_norm _ _).trans
            (mul_le_mul_of_nonneg_right (hres k) (norm_nonneg _))
      _ = ρ * (P * ‖x‖) := by rw [← sum_mul, ← hP]; ring
      _ ≤ ρ * ((P ^ 2 + ‖x‖ ^ 2) / 2) := by
          refine mul_le_mul_of_nonneg_left ?_ hρ0
          nlinarith [sq_nonneg (P - ‖x‖)]
  have hηP : η * P ^ 2 ≤ S := by
    calc η * P ^ 2 ≤ η * ((Fintype.card K : ℝ) * S) := mul_le_mul_of_nonneg_left hPS hη0
      _ = ((Fintype.card K : ℝ) * η) * S := by ring
      _ ≤ 1 * S := mul_le_mul_of_nonneg_right hη hS0
      _ = S := one_mul S
  have hBη : B * η * P ^ 2 ≤ (Fintype.card K : ℝ) * B * η * S := by
    have hB' : 0 ≤ B * η ∨ B * η < 0 := le_or_gt 0 (B * η)
    rcases hB' with hBη0 | hBη0
    · calc B * η * P ^ 2 ≤ B * η * ((Fintype.card K : ℝ) * S) :=
            mul_le_mul_of_nonneg_left hPS hBη0
        _ = _ := by ring
    · have : B * η * P ^ 2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hBη0.le (sq_nonneg _)
      -- `B < 0` forces `K` to be empty
      have hB_nonneg : ∀ k : K, 0 ≤ B := fun k => (abs_nonneg _).trans (hB k)
      by_cases hK : IsEmpty K
      · have hS' : S = 0 := by rw [hS]; simp
        rw [hS', mul_zero]
        exact this
      · obtain ⟨k⟩ := not_isEmpty_iff.mp hK
        exact absurd hBη0 (not_lt.mpr (mul_nonneg (hB_nonneg k) hη0))
  rw [hform]
  have hcard : (0 : ℝ) ≤ Fintype.card K := Nat.cast_nonneg _
  nlinarith [hnorm_le, hηP, hBη, hPS, h1, h2, h3, mul_nonneg hρ0 hS0, mul_nonneg hρ0 hcard]

/-- **Lower spectral count from quasimodes.** -/
theorem card_le_lowerSpectralWindow_of_quasimodes (hA : A.IsHermitian) (T : ℝ)
    (v : K → EuclideanSpace ℝ I) (E : K → ℝ) {δ η ρ B : ℝ} (hη0 : 0 ≤ η) (hρ0 : 0 ≤ ρ)
    (hE : ∀ k, E k ≤ T - δ) (hB : ∀ k, |E k - T| ≤ B)
    (hgram : ∀ k l, |⟪v k, v l⟫ - if k = l then 1 else 0| ≤ η)
    (hres : ∀ k, ‖Matrix.toEuclideanLin A (v k) - E k • v k‖ ≤ ρ)
    (hη : (Fintype.card K : ℝ) * η ≤ 1)
    (hsmall : (Fintype.card K : ℝ) * B * η + ρ * ((Fintype.card K : ℝ) + 1) < δ) :
    Fintype.card K ≤ (univ.filter (fun i => hA.eigenvalues i < T)).card := by
  let J := univ.filter (fun i => hA.eigenvalues i < T)
  let b := hA.eigenvectorBasis
  let syn : (K → ℝ) →ₗ[ℝ] EuclideanSpace ℝ I :=
    { toFun := fun a => ∑ k, a k • v k
      map_add' := by
        intro a d
        simp only [Pi.add_apply, add_smul, sum_add_distrib]
      map_smul' := by
        intro r a
        simp only [Pi.smul_apply, smul_eq_mul, mul_smul, smul_sum, RingHom.id_apply] }
  let L : (K → ℝ) →ₗ[ℝ] (J → ℝ) :=
    { toFun := fun a j => ⟪syn a, b j⟫
      map_add' := by
        intro a d
        funext j
        simp only [map_add, inner_add_left, Pi.add_apply]
      map_smul' := by
        intro r a
        funext j
        simp only [map_smul, real_inner_smul_left, Pi.smul_apply, smul_eq_mul,
          RingHom.id_apply] }
  have hker (a : K → ℝ) (ha : L a = 0) : a = 0 := by
    by_contra ha0
    set x := syn a with hxdef
    have hlow : ∀ i, hA.eigenvalues i < T → ⟪x, b i⟫ = 0 := fun i hi =>
      congrFun ha ⟨i, mem_filter.mpr ⟨mem_univ _, hi⟩⟩
    have hge : T * ‖x‖ ^ 2 ≤ ⟪Matrix.toEuclideanLin A x, x⟫ := by
      rw [HTGeometry.hermitianEnergy_eq_sum, ← hA.eigenvectorBasis.sum_sq_inner_left x, mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      by_cases hi : hA.eigenvalues i < T
      · rw [hlow i hi, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero, mul_zero]
      · exact mul_le_mul_of_nonneg_right (le_of_not_gt hi) (sq_nonneg _)
    have hS : 0 < ∑ k, a k ^ 2 := by
      obtain ⟨k, hk⟩ := Function.ne_iff.mp ha0
      exact lt_of_lt_of_le (pow_pos (abs_pos.mpr hk) 2 |>.trans_eq (sq_abs _))
        (single_le_sum (fun l _ => sq_nonneg (a l)) (mem_univ k))
    have hle := inner_quasimode_combination_sub_le T v E hη0 hρ0 hE hB hgram hres hη a
    have hneg : (-δ + (Fintype.card K : ℝ) * B * η + ρ * ((Fintype.card K : ℝ) + 1)) *
        ∑ k, a k ^ 2 < 0 := mul_neg_of_neg_of_pos (by linarith) hS
    change ⟪Matrix.toEuclideanLin A x, x⟫ - T * ‖x‖ ^ 2 ≤ _ at hle
    linarith
  have hinj : Function.Injective L := by
    intro a d had
    have hzero : L (a - d) = 0 := by rw [map_sub, had, sub_self]
    exact sub_eq_zero.mp (hker (a - d) hzero)
  have hdim := L.finrank_le_finrank_of_injective hinj
  simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] using hdim

end MinMax

/-- A finite set below a threshold stays below it by a fixed margin. -/
theorem exists_pos_gap_of_finset {E : ℕ → ℝ} {T : ℝ} (S : Finset ℕ) (hS : ∀ m ∈ S, E m < T) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ m ∈ S, E m ≤ T - δ := by
  induction S using Finset.induction_on with
  | empty => exact ⟨1, one_pos, fun m hm => by simp at hm⟩
  | @insert m S _ ih =>
    obtain ⟨δ, hδ, hgap⟩ := ih fun n hn => hS n (mem_insert_of_mem hn)
    have hmT := hS m (mem_insert_self m S)
    refine ⟨min δ (T - E m), lt_min hδ (by linarith), fun n hn => ?_⟩
    rcases mem_insert.mp hn with rfl | hn
    · have := min_le_right δ (T - E n); linarith
    · have := min_le_left δ (T - E m); linarith [hgap n hn]

/-- **Lower count at a fixed overlap.** Norm quasimodes for a finite packet of conductors whose
energies lie below `T` give as many eigenvalues below `T`. -/
theorem eventually_card_le_completeWeilSpectralSublevel_of_quasimodes {φ : ℝ → ℝ} {c : ℝ}
    {E : ℕ → ℝ} (S : Finset ℕ) (hS : ∀ m ∈ S, 0 < m) {T : ℝ} (hST : ∀ m ∈ S, E m < T)
    (hquasi : ∀ m ∈ S, Tendsto (fun N : ℕ =>
      ‖Matrix.toEuclideanLin (completeWeilMatrix φ c N) (normalizedRamanujanHorizonVector m N) -
        E m • normalizedRamanujanHorizonVector m N‖) atTop (𝓝 0)) :
    ∀ᶠ N : ℕ in atTop, S.card ≤ (completeWeilSpectralSublevel φ c N T).card := by
  obtain ⟨δ, hδ, hgap⟩ := exists_pos_gap_of_finset S hST
  set k : ℝ := (Fintype.card S : ℝ) with hk
  have hk0 : 0 ≤ k := Nat.cast_nonneg _
  set B : ℝ := ∑ m ∈ S, |E m - T| with hBdef
  have hB0 : 0 ≤ B := sum_nonneg fun _ _ => abs_nonneg _
  have hB : ∀ m : S, |E m - T| ≤ B := fun m =>
    single_le_sum (f := fun m => |E m - T|) (fun _ _ => abs_nonneg _) m.property
  set η : ℝ := min (1 / (k + 1)) (δ / (2 * (k * B + 1))) with hηdef
  have hη0 : 0 < η := lt_min (by positivity) (by positivity)
  set ρ : ℝ := δ / (4 * (k + 1)) with hρdef
  have hρ0 : 0 < ρ := by positivity
  have hkη : k * η ≤ 1 := by
    calc k * η ≤ k * (1 / (k + 1)) := mul_le_mul_of_nonneg_left (min_le_left _ _) hk0
      _ ≤ 1 := by rw [mul_one_div, div_le_one (by positivity)]; linarith
  have hsmall : k * B * η + ρ * (k + 1) < δ := by
    have h1 : k * B * η ≤ k * B * (δ / (2 * (k * B + 1))) :=
      mul_le_mul_of_nonneg_left (min_le_right _ _) (mul_nonneg hk0 hB0)
    have h2 : k * B * (δ / (2 * (k * B + 1))) < δ / 2 := by
      rw [mul_div_assoc', div_lt_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [mul_nonneg hk0 hB0]
    have h3 : ρ * (k + 1) = δ / 4 := by rw [hρdef]; field_simp
    linarith
  have hgram : ∀ᶠ N : ℕ in atTop, ∀ m l : S,
      |⟪normalizedRamanujanHorizonVector m N, normalizedRamanujanHorizonVector l N⟫ -
        if (m : ℕ) = l then 1 else 0| ≤ η := by
    rw [Filter.eventually_all]
    intro m
    rw [Filter.eventually_all]
    intro l
    have h := tendsto_normalizedRamanujanHorizonVector_gram (hS m m.property) (hS l l.property)
    have h' := (h.sub_const (if (m : ℕ) = l then (1 : ℝ) else 0)).abs
    simp only [sub_self, abs_zero] at h'
    exact h'.eventually (ge_mem_nhds hη0) |>.mono fun N hN => hN
  have hres : ∀ᶠ N : ℕ in atTop, ∀ m : S,
      ‖Matrix.toEuclideanLin (completeWeilMatrix φ c N) (normalizedRamanujanHorizonVector m N) -
        E m • normalizedRamanujanHorizonVector m N‖ ≤ ρ := by
    rw [Filter.eventually_all]
    intro m
    exact (hquasi m m.property).eventually (ge_mem_nhds hρ0)
  filter_upwards [hgram, hres] with N hgN hrN
  have h := card_le_lowerSpectralWindow_of_quasimodes (completeWeilMatrix_isHermitian φ c N) T
    (fun m : S => normalizedRamanujanHorizonVector m N) (fun m : S => E m) hη0.le hρ0.le
    (fun m => hgap m m.property) hB
    (fun m l => by simpa only [Subtype.ext_iff] using hgN m l) hrN hkη hsmall
  simpa only [Fintype.card_coe, completeWeilSpectralSublevel, completeWeilEigenvalue] using h

/-- The shell correction is bounded uniformly in the conductor. -/
theorem abs_shellCorrection_le (φ : ℝ → ℝ) (c : ℝ) {m : ℕ} (hm : 0 < m) :
    |shellCorrection φ c m| ≤ 2 / |∫ u, φ u ^ 2| *
      ∑ h ∈ Finset.Ico 1 ⌈c⌉₊, |∫ u in ((h : ℝ) / c)..1, shellAutocorr φ u / u| := by
  have ht : (0 : ℝ) < m.totient := by exact_mod_cast Nat.totient_pos.mpr hm
  rw [shellCorrection, abs_mul, abs_div, abs_mul, abs_of_pos ht, abs_two]
  calc 2 / (|∫ u, φ u ^ 2| * m.totient) *
        |∑ h ∈ Finset.Ico 1 ⌈c⌉₊, ramanujanLagCoefficient m h *
          ∫ u in ((h : ℝ) / c)..1, shellAutocorr φ u / u|
      ≤ 2 / (|∫ u, φ u ^ 2| * m.totient) *
        ∑ h ∈ Finset.Ico 1 ⌈c⌉₊, m.totient *
          |∫ u in ((h : ℝ) / c)..1, shellAutocorr φ u / u| := by
        refine mul_le_mul_of_nonneg_left ((abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun h _ => ?_)) (by positivity)
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right
          (BiScaleUncertainty.SieveMoments.abs_ramanujanLagCoefficient_le_totient m h)
          (abs_nonneg _)
    _ = _ := by
        rw [← mul_sum]
        rcases eq_or_ne |∫ u, φ u ^ 2| 0 with h0 | h0
        · rw [h0]; simp
        · field_simp

/-- Every sublevel of the completed conductor energies is finite. -/
theorem finite_completedConductorEnergy_sublevel (φ : ℝ → ℝ) {c : ℝ} (hc : 0 < c) (T : ℝ) :
    {m : ℕ | 0 < m ∧ completedConductorEnergy φ c m < T}.Finite := by
  set K := 2 / |∫ u, φ u ^ 2| *
    ∑ h ∈ Finset.Ico 1 ⌈c⌉₊, |∫ u in ((h : ℝ) / c)..1, shellAutocorr φ u / u|
  refine (finite_completeWeilAdjunctionEnergy_sublevel φ c (T + K)).subset fun m hm => ?_
  obtain ⟨hm0, hmT⟩ := hm
  refine ⟨hm0, ?_⟩
  rw [completedConductorEnergy_eq_sub_shellCorrection hc hm0] at hmT
  have := (abs_le.mp (abs_shellCorrection_le φ c hm0)).2
  linarith

/-- The completed conductors with energy below a threshold. -/
def completedEnergySublevel (φ : ℝ → ℝ) {c : ℝ} (hc : 0 < c) (T : ℝ) : Finset ℕ :=
  (finite_completedConductorEnergy_sublevel φ hc T).toFinset

@[simp] theorem mem_completedEnergySublevel (φ : ℝ → ℝ) {c : ℝ} (hc : 0 < c) (T : ℝ) (m : ℕ) :
    m ∈ completedEnergySublevel φ hc T ↔ 0 < m ∧ completedConductorEnergy φ c m < T := by
  simp only [completedEnergySublevel, Set.Finite.mem_toFinset, Set.mem_setOf_eq]

/-- **Upper count from a reserve.** No low spectral multiplicity survives beyond the conductors
below the threshold. -/
theorem eventually_completeWeilSpectralSublevel_card_le_of_reserve_quasimodes {φ : ℝ → ℝ}
    {c : ℝ} (hc : 0 < c) {a β : ℝ} (hβ : 0 < β)
    (hres : ∀ᶠ N : ℕ in atTop, ∀ x : EuclideanSpace ℝ (PrimeHorizonIndex N),
      a * ‖x‖ ^ 2 + β * poleDefect N (primeHorizonExtension x) ≤ completeWeilEnergy φ c N x)
    (hquasi : ∀ m : ℕ, 0 < m → Tendsto (fun N : ℕ =>
      ‖Matrix.toEuclideanLin (completeWeilMatrix φ c N) (normalizedRamanujanHorizonVector m N) -
        completedConductorEnergy φ c m • normalizedRamanujanHorizonVector m N‖) atTop (𝓝 0))
    (T : ℝ) (hT : ∀ m : ℕ, 0 < m → completedConductorEnergy φ c m ≠ T) :
    ∀ᶠ N : ℕ in atTop,
      (completeWeilSpectralSublevel φ c N T).card ≤ (completedEnergySublevel φ hc T).card := by
  set S := completedEnergySublevel φ hc T
  obtain ⟨C, hC, hcert⟩ :=
    CriticalArithmeticCorrelationTheory.exists_finite_ramanujan_coordinate_certificate_of_reserve
      hβ hres T
  let R : ℕ → ℕ → ℝ := fun m N =>
    ‖Matrix.toEuclideanLin (completeWeilMatrix φ c N) (normalizedRamanujanHorizonVector m N) -
      completedConductorEnergy φ c m • normalizedRamanujanHorizonVector m N‖
  let F : ℕ → ℝ := fun N => ∑ m ∈ C,
    if m ∈ S then 0 else R m N ^ 2 / (completedConductorEnergy φ c m - T) ^ 2
  have hlim : Tendsto F atTop (𝓝 0) := by
    have hi : ∀ m ∈ C, Tendsto (fun N : ℕ =>
        if m ∈ S then (0 : ℝ) else R m N ^ 2 / (completedConductorEnergy φ c m - T) ^ 2)
        atTop (𝓝 0) := by
      intro m hm
      by_cases hs : m ∈ S
      · simp only [if_pos hs]
        exact tendsto_const_nhds
      · simp only [if_neg hs]
        have hr := (hquasi m (hC m hm)).pow 2
        simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0), zero_div, R] using
          hr.div_const ((completedConductorEnergy φ c m - T) ^ 2)
    simpa only [F, sum_const_zero] using tendsto_finsetSum C hi
  have hsmall : ∀ᶠ N : ℕ in atTop, F N < 1 / 18 :=
    hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 18))
  filter_upwards [hcert, hsmall] with N hcN hsmallN
  have hcount : (univ.filter (fun i : PrimeHorizonIndex N =>
      (completeWeilMatrix_isHermitian φ c N).eigenvalues i < T)).card ≤ Fintype.card S := by
    apply HTGeometry.lowerSpectralWindow_card_le_of_coordinates
      (completeWeilMatrix_isHermitian φ c N) T
      (fun m : S => normalizedRamanujanHorizonVector m N)
    intro x hx hlo
    by_contra hn
    push Not at hn
    have henergy : completeWeilEnergy φ c N x ≤ T := by
      have h := HTGeometry.hermitianEnergy_le_of_support
        (completeWeilMatrix_isHermitian φ c N) T x hlo
      simpa only [completeWeilEnergy, hx, one_pow, mul_one] using h
    have hmass := hcN x hx henergy
    have hsum : (∑ m ∈ C, ⟪x, normalizedRamanujanHorizonVector m N⟫ ^ 2) ≤ F N := by
      refine Finset.sum_le_sum fun m hm => ?_
      by_cases hs : m ∈ S
      · rw [if_pos hs, hn ⟨m, hs⟩, zero_pow (by decide : (2 : ℕ) ≠ 0)]
      · rw [if_neg hs]
        have hnot : ¬ completedConductorEnergy φ c m < T := fun h =>
          hs ((mem_completedEnergySublevel φ hc T m).mpr ⟨hC m hm, h⟩)
        have hgt : T < completedConductorEnergy φ c m :=
          lt_of_le_of_ne (le_of_not_gt hnot) (Ne.symm (hT m (hC m hm)))
        exact HTGeometry.inner_sq_le_residual_sq_div_upper_gap_sq
          (completeWeilMatrix_isHermitian φ c N) T (completedConductorEnergy φ c m)
          hgt x (normalizedRamanujanHorizonVector m N) hx hlo
    linarith only [hmass, hsum, hsmallN]
  simpa only [completeWeilSpectralSublevel, completeWeilEigenvalue, Fintype.card_coe] using hcount

/-- **Exact bounded spectral counts at a fixed overlap.** A prime-defect reserve and norm
quasimodes against the completed conductor energies count every low window of the complete Weil
matrix, with multiplicity, by the conductors below the threshold. -/
theorem eventually_completeWeil_spectral_count_eq_of_reserve_quasimodes {φ : ℝ → ℝ}
    {c : ℝ} (hc : 0 < c) {a β : ℝ} (hβ : 0 < β)
    (hres : ∀ᶠ N : ℕ in atTop, ∀ x : EuclideanSpace ℝ (PrimeHorizonIndex N),
      a * ‖x‖ ^ 2 + β * poleDefect N (primeHorizonExtension x) ≤ completeWeilEnergy φ c N x)
    (hquasi : ∀ m : ℕ, 0 < m → Tendsto (fun N : ℕ =>
      ‖Matrix.toEuclideanLin (completeWeilMatrix φ c N) (normalizedRamanujanHorizonVector m N) -
        completedConductorEnergy φ c m • normalizedRamanujanHorizonVector m N‖) atTop (𝓝 0))
    (T : ℝ) (hT : ∀ m : ℕ, 0 < m → completedConductorEnergy φ c m ≠ T) :
    ∀ᶠ N : ℕ in atTop,
      (completeWeilSpectralSublevel φ c N T).card = (completedEnergySublevel φ hc T).card := by
  have hS : ∀ m ∈ completedEnergySublevel φ hc T, 0 < m := fun m hm =>
    ((mem_completedEnergySublevel φ hc T m).mp hm).1
  have hST : ∀ m ∈ completedEnergySublevel φ hc T, completedConductorEnergy φ c m < T :=
    fun m hm => ((mem_completedEnergySublevel φ hc T m).mp hm).2
  filter_upwards [eventually_completeWeilSpectralSublevel_card_le_of_reserve_quasimodes hc hβ hres
      hquasi T hT,
    eventually_card_le_completeWeilSpectralSublevel_of_quasimodes
      (completedEnergySublevel φ hc T) hS hST fun m hm => hquasi m (hS m hm)] with N hu hl
  exact Nat.le_antisymm hu hl

/-! ### The bottom of the spectrum and its vanishing margin -/

/-- The bottom of the completed conductor spectrum, `inf_{m ≥ 1} E_m(c)`. -/
def completedEnergyFloor (φ : ℝ → ℝ) (c : ℝ) : ℝ :=
  ⨅ m : {m : ℕ // 0 < m}, completedConductorEnergy φ c m

section Floor

variable {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
  (hM : 0 < ∫ u, φ u ^ 2)
include hφ hsupp hM

theorem bddBelow_completedConductorEnergy {c : ℝ} (hc : 0 < c) :
    BddBelow (Set.range fun m : {m : ℕ // 0 < m} => completedConductorEnergy φ c m) :=
  ⟨0, by
    rintro _ ⟨m, rfl⟩
    exact completedConductorEnergy_nonneg hφ hsupp hM hc m.property⟩

theorem completedEnergyFloor_le {c : ℝ} (hc : 0 < c) {m : ℕ} (hm : 0 < m) :
    completedEnergyFloor φ c ≤ completedConductorEnergy φ c m :=
  ciInf_le (bddBelow_completedConductorEnergy hφ hsupp hM hc) ⟨m, hm⟩

theorem completedEnergyFloor_nonneg {c : ℝ} (hc : 0 < c) : 0 ≤ completedEnergyFloor φ c :=
  le_ciInf fun m => completedConductorEnergy_nonneg hφ hsupp hM hc m.property

/-- The bottom is attained: below `E_1(c) + 1` only finitely many conductors compete. -/
theorem exists_completedConductorEnergy_eq_floor {c : ℝ} (hc : 0 < c) :
    ∃ m : ℕ, 0 < m ∧ completedConductorEnergy φ c m = completedEnergyFloor φ c := by
  set S := completedEnergySublevel φ hc (completedConductorEnergy φ c 1 + 1)
  have h1 : 1 ∈ S := (mem_completedEnergySublevel φ hc _ 1).mpr ⟨one_pos, lt_add_one _⟩
  obtain ⟨m, hmS, hmin⟩ := S.exists_min_image (completedConductorEnergy φ c) ⟨1, h1⟩
  have hm0 := ((mem_completedEnergySublevel φ hc _ m).mp hmS).1
  refine ⟨m, hm0, le_antisymm (le_ciInf fun l => ?_) (completedEnergyFloor_le hφ hsupp hM hc hm0)⟩
  by_cases hl : (l : ℕ) ∈ S
  · exact hmin l hl
  · have hge : completedConductorEnergy φ c 1 + 1 ≤ completedConductorEnergy φ c l := by
      by_contra hlt
      exact hl ((mem_completedEnergySublevel φ hc _ l).mpr ⟨l.property, lt_of_not_ge hlt⟩)
    have := hmin 1 h1
    linarith

/-- **The margin vanishes at infinite overlap**: `inf_m E_m(c) → 0` as `c → ∞`. -/
theorem tendsto_completedEnergyFloor_atTop :
    Tendsto (completedEnergyFloor φ) atTop (𝓝 0) := by
  refine squeeze_zero' ?_ ?_ (tendsto_completedConductorEnergy_atTop hφ hsupp hM 1)
  · filter_upwards [eventually_gt_atTop 0] with c hc
    exact completedEnergyFloor_nonneg hφ hsupp hM hc
  · filter_upwards [eventually_gt_atTop 0] with c hc
    exact completedEnergyFloor_le hφ hsupp hM hc one_pos

/-- **The bottom of the complete Weil spectrum at a fixed overlap.** Under a reserve and norm
quasimodes every eigenvalue eventually exceeds `inf_m E_m(c) − ε`, and one lies within `ε` of it. -/
theorem eventually_completeWeil_spectrum_bottom_of_reserve_quasimodes {c : ℝ} (hc : 0 < c)
    {a β : ℝ} (hβ : 0 < β)
    (hres : ∀ᶠ N : ℕ in atTop, ∀ x : EuclideanSpace ℝ (PrimeHorizonIndex N),
      a * ‖x‖ ^ 2 + β * poleDefect N (primeHorizonExtension x) ≤ completeWeilEnergy φ c N x)
    (hquasi : ∀ m : ℕ, 0 < m → Tendsto (fun N : ℕ =>
      ‖Matrix.toEuclideanLin (completeWeilMatrix φ c N) (normalizedRamanujanHorizonVector m N) -
        completedConductorEnergy φ c m • normalizedRamanujanHorizonVector m N‖) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, (∀ i, completedEnergyFloor φ c - ε < completeWeilEigenvalue φ c N i) ∧
      ∃ i, |completeWeilEigenvalue φ c N i - completedEnergyFloor φ c| < ε := by
  set T := completedEnergyFloor φ c - ε / 2 with hTdef
  have hT : ∀ m : ℕ, 0 < m → completedConductorEnergy φ c m ≠ T := fun m hm h => by
    have := completedEnergyFloor_le hφ hsupp hM hc hm
    linarith [hTdef]
  have hempty : completedEnergySublevel φ hc T = ∅ := by
    refine Finset.eq_empty_of_forall_notMem fun m hm => ?_
    obtain ⟨hm0, hmT⟩ := (mem_completedEnergySublevel φ hc T m).mp hm
    have := completedEnergyFloor_le hφ hsupp hM hc hm0
    linarith [hTdef]
  obtain ⟨m, hm0, hme⟩ := exists_completedConductorEnergy_eq_floor hφ hsupp hM hc
  have hnear : ∀ᶠ N : ℕ in atTop, ∃ i : PrimeHorizonIndex N,
      |(completeWeilMatrix_isHermitian φ c N).eigenvalues i - completedConductorEnergy φ c m| < ε := by
    have hr := (hquasi m hm0).pow 2
    have hnorm := (tendsto_normalizedRamanujanHorizonVector_norm_sq hm0).const_mul (ε ^ 2)
    have hlt := hr.eventually_lt hnorm
      (by simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0), mul_one] using pow_pos hε 2)
    filter_upwards [hlt] with N hN
    exact HTGeometry.exists_eigenvalue_abs_sub_lt_of_residual_sq_lt
      (completeWeilMatrix_isHermitian φ c N) (normalizedRamanujanHorizonVector m N)
      (completedConductorEnergy φ c m) hε.le hN
  filter_upwards [eventually_completeWeilSpectralSublevel_card_le_of_reserve_quasimodes hc hβ hres
      hquasi T hT, hnear] with N hcount hN
  refine ⟨fun i => ?_, ?_⟩
  · rw [hempty, Finset.card_empty, Nat.le_zero, Finset.card_eq_zero] at hcount
    have hi : i ∉ completeWeilSpectralSublevel φ c N T := by rw [hcount]; exact Finset.notMem_empty i
    rw [completeWeilSpectralSublevel, Finset.mem_filter] at hi
    push Not at hi
    have := hi (Finset.mem_univ i)
    linarith [hTdef]
  · obtain ⟨i, hi⟩ := hN
    exact ⟨i, by rw [completeWeilEigenvalue, ← hme]; exact hi⟩

end Floor

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
