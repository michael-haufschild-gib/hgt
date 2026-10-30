import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheBottomOfTheCompleteWeilSpectrumIsTheCompletedShellEnergy
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.BoundedPrimeEnergyHasFiniteRamanujanCoordinates
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.MacroscopicOverlapTiltedSplineReserve
import GaloisForLFunctions.HTGeometry.HermitianSpectralWindowBounds

/-!
# The low complete-Weil spectrum lives on the low conductors

At a fixed overlap `c` the complete Weil matrix has exact low spectral counts: below a threshold `T`
off the energy set there are as many eigenvalues as conductors `m` with completed energy
`E_m(c) < T`. This file upgrades counts to **eigenvectors**. Let `U_N(T)` be the span of the actual
eigenvectors with eigenvalue `< T` (`completeWeilLowSpace`). Then, eventually in `N`:

* every normalized Ramanujan vector `v_m`, `E_m(c) < T`, is within `ε` of `U_N(T)` (Davis–Kahan:
  the residual `‖(A − E_m) v_m‖ → 0` is divided by the gap `T − E_m`);
* every vector of `U_N(T)` is within `ε` (relatively) of the span of these `v_m`
  (`eventually_completeWeil_lowSpace_near_ramanujan`).

The second half uses the exact count: the projections of the `v_m` are a near-orthonormal family of
`dim U_N(T)` vectors inside `U_N(T)`, hence a basis with controlled coefficients
(`exists_combination_of_near_orthonormal`).

So the low spectrum is localized on the finitely many conductors below the threshold. For the
tilted unit spline this holds at every overlap `c > 0` (`tiltedUnitSpline_lowSpace_near_ramanujan`).
Since every completed energy tends to `0` as `c → ∞`, the conductor set below a fixed threshold grows
with the overlap, and a diagonal schedule `c_N → ∞` keeps the localization
(`exists_overlap_schedule_lowSpace_near_ramanujan`).
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open GaloisForLFunctions.HTGeometry (hermitianEigenProjection
  gap_sq_mul_eigenProjection_error_le_residual_sq)
open SpacingScaleHarmonicAnalysis CompletedShell CriticalArithmeticCorrelationTheory

/-! ### Near-orthonormal families span -/

section Span

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {K : Type*} [Fintype K]
  [DecidableEq K]

/-- The coefficients of a combination of a near-orthonormal family are controlled by its norm. -/
theorem sum_sq_le_two_mul_norm_sq {w : K → E} {η : ℝ} (hη : (Fintype.card K : ℝ) * η ≤ 1 / 2)
    (hgram : ∀ k l, |⟪w k, w l⟫ - if k = l then 1 else 0| ≤ η) (a : K → ℝ) :
    ∑ k, a k ^ 2 ≤ 2 * ‖∑ k, a k • w k‖ ^ 2 := by
  have hexp : ‖∑ k, a k • w k‖ ^ 2 = ∑ k, ∑ l, a k * a l * ⟪w k, w l⟫ := by
    rw [← real_inner_self_eq_norm_sq, sum_inner]
    refine sum_congr rfl fun k _ => ?_
    rw [inner_sum]
    refine sum_congr rfl fun l _ => ?_
    rw [real_inner_smul_left, real_inner_smul_right]; ring
  have hsplit : ∑ k, ∑ l, a k * a l * ⟪w k, w l⟫ = ∑ k, a k ^ 2 +
      ∑ k, ∑ l, a k * a l * (⟪w k, w l⟫ - if k = l then 1 else 0) := by
    simp only [mul_sub, sum_sub_distrib, mul_ite, mul_one, mul_zero, sum_ite_eq, mem_univ, if_true]
    ring_nf
  have herr : |∑ k, ∑ l, a k * a l * (⟪w k, w l⟫ - if k = l then 1 else 0)| ≤
      η * (∑ k, |a k|) ^ 2 := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    rw [sq, sum_mul_sum, mul_sum]
    refine sum_le_sum fun k _ => (abs_sum_le_sum_abs _ _).trans ?_
    rw [mul_sum]
    refine sum_le_sum fun l _ => ?_
    rw [abs_mul, abs_mul]
    nlinarith [hgram k l, abs_nonneg (a k), abs_nonneg (a l), mul_nonneg (abs_nonneg (a k))
      (abs_nonneg (a l))]
  have hcs : (∑ k, |a k|) ^ 2 ≤ Fintype.card K * ∑ k, a k ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := (univ : Finset K)) (f := fun k => |a k|)
    simpa [sq_abs] using this
  have hS : 0 ≤ ∑ k, a k ^ 2 := sum_nonneg fun k _ => sq_nonneg _
  have h1 := (abs_le.mp herr).1
  have h2 : η * (∑ k, |a k|) ^ 2 ≤ (1 / 2) * ∑ k, a k ^ 2 := by
    by_cases hη0 : 0 ≤ η
    · calc η * (∑ k, |a k|) ^ 2 ≤ η * (Fintype.card K * ∑ k, a k ^ 2) :=
            mul_le_mul_of_nonneg_left hcs hη0
        _ = (Fintype.card K * η) * ∑ k, a k ^ 2 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hη hS
    · push Not at hη0
      have : η * (∑ k, |a k|) ^ 2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hη0.le (sq_nonneg _)
      linarith
  rw [hexp, hsplit]
  linarith

/-- **A near-orthonormal family of `dim U` vectors in `U` is a basis with controlled coefficients.** -/
theorem exists_combination_of_near_orthonormal (U : Submodule ℝ E) [FiniteDimensional ℝ U]
    (hU : Module.finrank ℝ U = Fintype.card K) {w : K → E} (hw : ∀ k, w k ∈ U) {η : ℝ}
    (hη : (Fintype.card K : ℝ) * η ≤ 1 / 2)
    (hgram : ∀ k l, |⟪w k, w l⟫ - if k = l then 1 else 0| ≤ η) :
    ∀ x ∈ U, ∃ a : K → ℝ, x = ∑ k, a k • w k ∧ ∑ k, a k ^ 2 ≤ 2 * ‖x‖ ^ 2 := by
  let Lw : (K → ℝ) →ₗ[ℝ] U :=
    { toFun := fun a => ⟨∑ k, a k • w k, U.sum_mem fun k _ => U.smul_mem _ (hw k)⟩
      map_add' := fun a b => by ext; simp [add_smul, sum_add_distrib]
      map_smul' := fun t a => by ext; simp [smul_sum, smul_smul] }
  have hinj : Function.Injective Lw := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro a ha
    have h0 : ∑ k, a k • w k = 0 := congrArg Subtype.val (LinearMap.mem_ker.mp ha)
    have h := sum_sq_le_two_mul_norm_sq hη hgram a
    rw [h0, norm_zero] at h
    funext k
    have hk : a k ^ 2 ≤ ∑ k, a k ^ 2 := single_le_sum (fun k _ => sq_nonneg (a k)) (mem_univ k)
    have : a k ^ 2 = 0 := le_antisymm (by linarith) (sq_nonneg _)
    simpa using this
  have hsurj : Function.Surjective Lw :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by
      rw [Module.finrank_fintype_fun_eq_card, hU])).mp hinj
  intro x hx
  obtain ⟨a, ha⟩ := hsurj ⟨x, hx⟩
  have hxa : x = ∑ k, a k • w k := (congrArg Subtype.val ha).symm
  exact ⟨a, hxa, hxa ▸ sum_sq_le_two_mul_norm_sq hη hgram a⟩

end Span

/-! ### The low spectral subspace -/

/-- The span of the actual eigenvectors of the complete Weil matrix with eigenvalue below `T`. -/
def completeWeilLowSpace (φ : ℝ → ℝ) (c : ℝ) (N : ℕ) (T : ℝ) :
    Submodule ℝ (EuclideanSpace ℝ (PrimeHorizonIndex N)) :=
  Submodule.span ℝ ((completeWeilMatrix_isHermitian φ c N).eigenvectorBasis ''
    (completeWeilSpectralSublevel φ c N T : Set (PrimeHorizonIndex N)))

theorem finrank_completeWeilLowSpace (φ : ℝ → ℝ) (c : ℝ) (N : ℕ) (T : ℝ) :
    Module.finrank ℝ (completeWeilLowSpace φ c N T) = (completeWeilSpectralSublevel φ c N T).card := by
  set hA := completeWeilMatrix_isHermitian φ c N
  set S := completeWeilSpectralSublevel φ c N T
  have hli : LinearIndependent ℝ (fun i : S => hA.eigenvectorBasis (i : PrimeHorizonIndex N)) :=
    hA.eigenvectorBasis.orthonormal.linearIndependent.comp _ Subtype.val_injective
  have hrange : Set.range (fun i : S => hA.eigenvectorBasis (i : PrimeHorizonIndex N)) =
      hA.eigenvectorBasis '' (S : Set (PrimeHorizonIndex N)) := by
    ext v; simp
  rw [completeWeilLowSpace, ← hrange, finrank_span_eq_card hli, Fintype.card_coe]

theorem eigenProjection_mem_lowSpace (φ : ℝ → ℝ) (c : ℝ) (N : ℕ) (T : ℝ)
    (v : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    hermitianEigenProjection (completeWeilMatrix_isHermitian φ c N)
      (completeWeilSpectralSublevel φ c N T) v ∈ completeWeilLowSpace φ c N T :=
  Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)

/-- **Davis–Kahan.** A quasimode at energy `E < T` lies within `residual/(T − E)` of the low space:
outside the sublevel every eigenvalue is at least `T`. -/
theorem norm_sub_eigenProjection_le (φ : ℝ → ℝ) (c : ℝ) (N : ℕ) {T E : ℝ} (hE : E < T)
    (v : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    ‖v - hermitianEigenProjection (completeWeilMatrix_isHermitian φ c N)
      (completeWeilSpectralSublevel φ c N T) v‖ ≤
      ‖Matrix.toEuclideanLin (completeWeilMatrix φ c N) v - E • v‖ / (T - E) := by
  set hA := completeWeilMatrix_isHermitian φ c N
  have hgap : ∀ i ∉ completeWeilSpectralSublevel φ c N T, T - E ≤ |hA.eigenvalues i - E| := by
    intro i hi
    have : ¬ completeWeilEigenvalue φ c N i < T := fun h =>
      hi (mem_filter.mpr ⟨mem_univ _, h⟩)
    rw [completeWeilEigenvalue] at this
    push Not at this
    rw [abs_of_nonneg (by linarith)]
    linarith
  have h := gap_sq_mul_eigenProjection_error_le_residual_sq hA _ v E (T - E) (by linarith) hgap
  rw [le_div_iff₀ (by linarith)]
  by_contra hcon
  push Not at hcon
  have h0 := norm_nonneg (Matrix.toEuclideanLin (completeWeilMatrix φ c N) v - E • v)
  nlinarith

/-! ### Localization at a fixed overlap -/

/-- **The low spectrum lives on the low conductors.** Under a prime-defect reserve and norm
quasimodes, for every threshold `T` off the energy set and every `ε > 0`, eventually in `N`: every
Ramanujan vector of a conductor below `T` is within `ε` of the low space, and every vector of the low
space is within `ε` (relatively) of the span of these Ramanujan vectors. -/
theorem eventually_completeWeil_lowSpace_near_ramanujan {φ : ℝ → ℝ} {c : ℝ} (hc : 0 < c)
    {a β : ℝ} (hβ : 0 < β)
    (hres : ∀ᶠ N : ℕ in atTop, ∀ x : EuclideanSpace ℝ (PrimeHorizonIndex N),
      a * ‖x‖ ^ 2 + β * poleDefect N (primeHorizonExtension x) ≤ completeWeilEnergy φ c N x)
    (hquasi : ∀ m : ℕ, 0 < m → Tendsto (fun N : ℕ =>
      ‖Matrix.toEuclideanLin (completeWeilMatrix φ c N) (normalizedRamanujanHorizonVector m N) -
        completedConductorEnergy φ c m • normalizedRamanujanHorizonVector m N‖) atTop (𝓝 0))
    (T : ℝ) (hT : ∀ m : ℕ, 0 < m → completedConductorEnergy φ c m ≠ T) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      (∀ m ∈ completedEnergySublevel φ hc T,
        ‖normalizedRamanujanHorizonVector m N - hermitianEigenProjection
          (completeWeilMatrix_isHermitian φ c N) (completeWeilSpectralSublevel φ c N T)
            (normalizedRamanujanHorizonVector m N)‖ ≤ ε) ∧
      ∀ x ∈ completeWeilLowSpace φ c N T, ∃ y ∈ Submodule.span ℝ
        ((fun m => normalizedRamanujanHorizonVector m N) '' (completedEnergySublevel φ hc T : Set ℕ)),
          ‖x - y‖ ≤ ε * ‖x‖ := by
  classical
  set S := completedEnergySublevel φ hc T
  set k := S.card
  have hS : ∀ m ∈ S, 0 < m ∧ completedConductorEnergy φ c m < T := fun m hm =>
    (mem_completedEnergySublevel φ hc T m).mp hm
  set η : ℝ := 1 / (2 * (k + 1))
  have hη : 0 < η := by positivity
  set τ : ℝ := min (η / 10) (ε / (2 * (k + 1)))
  have hτ : 0 < τ := lt_min (by positivity) (by positivity)
  have hτη : τ ≤ η / 10 := min_le_left _ _
  have hτε : τ ≤ ε / (2 * (k + 1)) := min_le_right _ _
  have hη1 : η ≤ 1 / 2 := by
    simp only [η]; rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith [k.cast_nonneg (α := ℝ)]
  have hτ1 : τ ≤ 1 := by linarith
  -- the eventual inputs
  have E2 : ∀ᶠ N : ℕ in atTop, ∀ m ∈ S,
      ‖Matrix.toEuclideanLin (completeWeilMatrix φ c N) (normalizedRamanujanHorizonVector m N) -
        completedConductorEnergy φ c m • normalizedRamanujanHorizonVector m N‖ ≤
          τ * (T - completedConductorEnergy φ c m) :=
    (eventually_all_finset S).mpr fun m hm => (hquasi m (hS m hm).1).eventually
      (ge_mem_nhds (mul_pos hτ (by linarith [(hS m hm).2])))
  have E3 : ∀ᶠ N : ℕ in atTop, ∀ m ∈ S, ∀ l ∈ S,
      |⟪normalizedRamanujanHorizonVector m N, normalizedRamanujanHorizonVector l N⟫ -
        if m = l then 1 else 0| ≤ η / 2 :=
    (eventually_all_finset S).mpr fun m hm => (eventually_all_finset S).mpr fun l hl => by
      have h := (tendsto_normalizedRamanujanHorizonVector_gram (hS m hm).1 (hS l hl).1).sub_const
        (if m = l then (1 : ℝ) else 0)
      rw [sub_self] at h
      have h' : Tendsto (fun N : ℕ => |⟪normalizedRamanujanHorizonVector m N,
          normalizedRamanujanHorizonVector l N⟫ - if m = l then (1 : ℝ) else 0|) atTop (𝓝 0) := by
        simpa using h.abs
      exact h'.eventually (ge_mem_nhds (half_pos hη))
  have E4 : ∀ᶠ N : ℕ in atTop, ∀ m ∈ S, ‖normalizedRamanujanHorizonVector m N‖ ≤ 2 :=
    (eventually_all_finset S).mpr fun m hm =>
      ((tendsto_normalizedRamanujanHorizonVector_norm_sq (hS m hm).1).eventually
        (ge_mem_nhds (by norm_num : (1 : ℝ) < 4))).mono fun N hN => by
          nlinarith [norm_nonneg (normalizedRamanujanHorizonVector m N)]
  filter_upwards [eventually_completeWeil_spectral_count_eq_of_reserve_quasimodes hc hβ hres hquasi
    T hT, E2, E3, E4] with N hcount h2 h3 h4
  set hA := completeWeilMatrix_isHermitian φ c N
  set Sub := completeWeilSpectralSublevel φ c N T
  set v : ℕ → EuclideanSpace ℝ (PrimeHorizonIndex N) := fun m => normalizedRamanujanHorizonVector m N
  set w : ℕ → EuclideanSpace ℝ (PrimeHorizonIndex N) := fun m => hermitianEigenProjection hA Sub (v m)
  have hvw : ∀ m ∈ S, ‖v m - w m‖ ≤ τ := by
    intro m hm
    have h := norm_sub_eigenProjection_le φ c N (hS m hm).2 (v m)
    refine h.trans ?_
    rw [div_le_iff₀ (by linarith [(hS m hm).2])]
    exact h2 m hm
  refine ⟨fun m hm => (hvw m hm).trans (hτε.trans ?_), ?_⟩
  · rw [div_le_iff₀ (by positivity)]; nlinarith [k.cast_nonneg (α := ℝ)]
  intro x hx
  -- the projected quasimodes form a near-orthonormal basis of the low space
  have hgram : ∀ m l : S, |⟪w m, w l⟫ - if m = l then 1 else 0| ≤ η := by
    intro m l
    have hm := m.2; have hl := l.2
    have hv := h3 m hm l hl
    have hwl : ‖w l‖ ≤ 3 := by
      have := norm_le_insert' (w l) (v l)
      linarith [hvw l hl, h4 l hl, norm_sub_rev (w l) (v l)]
    have hdiff : ⟪w m, w l⟫ - ⟪v m, v l⟫ = ⟪w m - v m, w l⟫ + ⟪v m, w l - v l⟫ := by
      simp only [inner_sub_left, inner_sub_right]; ring
    have hb : |⟪w m, w l⟫ - ⟪v m, v l⟫| ≤ 5 * τ := by
      rw [hdiff]
      refine (abs_add_le _ _).trans ?_
      have e1 := abs_real_inner_le_norm (w m - v m) (w l)
      have e2 := abs_real_inner_le_norm (v m) (w l - v l)
      have n1 : ‖w m - v m‖ ≤ τ := by rw [norm_sub_rev]; exact hvw m hm
      have n2 : ‖w l - v l‖ ≤ τ := by rw [norm_sub_rev]; exact hvw l hl
      have hvm := h4 m hm
      nlinarith [norm_nonneg (w m - v m), norm_nonneg (w l - v l), norm_nonneg (v m),
        norm_nonneg (w l)]
    have hml : (if (m : ℕ) = (l : ℕ) then (1 : ℝ) else 0) = if m = l then 1 else 0 := by
      simp only [Subtype.ext_iff]
    rw [← hml]
    calc |⟪w m, w l⟫ - if (m : ℕ) = l then 1 else 0|
        ≤ |⟪w m, w l⟫ - ⟪v m, v l⟫| + |⟪v m, v l⟫ - if (m : ℕ) = l then 1 else 0| := by
          rw [show ⟪w m, w l⟫ - (if (m : ℕ) = l then 1 else 0) = (⟪w m, w l⟫ - ⟪v m, v l⟫) +
            (⟪v m, v l⟫ - if (m : ℕ) = l then 1 else 0) by ring]
          exact abs_add_le _ _
      _ ≤ 5 * τ + η / 2 := add_le_add hb hv
      _ ≤ η := by linarith
  have hU : Module.finrank ℝ (completeWeilLowSpace φ c N T) = Fintype.card S := by
    rw [finrank_completeWeilLowSpace, Fintype.card_coe]; exact hcount
  have hηk : (Fintype.card S : ℝ) * η ≤ 1 / 2 := by
    rw [Fintype.card_coe]
    simp only [η]
    rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  obtain ⟨cf, hxc, hcf⟩ := exists_combination_of_near_orthonormal (completeWeilLowSpace φ c N T) hU
    (w := fun m : S => w m) (fun m => eigenProjection_mem_lowSpace φ c N T _) hηk hgram x hx
  refine ⟨∑ m : S, cf m • v m, Submodule.sum_mem _ fun m _ => Submodule.smul_mem _ _
    (Submodule.subset_span ⟨m, m.2, rfl⟩), ?_⟩
  have habs : ∑ m : S, |cf m| ≤ (k + 1) * ‖x‖ := by
    have hcs : (∑ m : S, |cf m|) ^ 2 ≤ k * ∑ m : S, cf m ^ 2 := by
      have := sq_sum_le_card_mul_sum_sq (s := (univ : Finset S)) (f := fun m => |cf m|)
      simpa [sq_abs, Fintype.card_coe] using this
    have h0 : 0 ≤ ∑ m : S, |cf m| := sum_nonneg fun m _ => abs_nonneg _
    have hk : (0 : ℝ) ≤ k := k.cast_nonneg
    have h2 : (∑ m : S, |cf m|) ^ 2 ≤ ((k + 1) * ‖x‖) ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hcf hk, sq_nonneg ((k : ℝ) - 1), sq_nonneg ‖x‖]
    exact (pow_le_pow_iff_left₀ h0 (by positivity) two_ne_zero).mp h2
  rw [hxc, ← sum_sub_distrib]
  calc ‖∑ m : S, (cf m • w m - cf m • v m)‖ ≤ ∑ m : S, |cf m| * τ := by
        refine (norm_sum_le _ _).trans (sum_le_sum fun m _ => ?_)
        rw [← smul_sub, norm_smul, Real.norm_eq_abs, norm_sub_rev]
        exact mul_le_mul_of_nonneg_left (hvw m m.2) (abs_nonneg _)
    _ = τ * ∑ m : S, |cf m| := by rw [mul_sum]; exact sum_congr rfl fun m _ => mul_comm _ _
    _ ≤ (ε / (2 * (k + 1))) * ((k + 1) * ‖x‖) :=
        mul_le_mul hτε habs (sum_nonneg fun m _ => abs_nonneg _) (by positivity)
    _ ≤ ε * ‖∑ m : S, cf m • w m‖ := by
        rw [← hxc]
        have : (ε / (2 * (k + 1))) * ((k + 1) * ‖x‖) = ε * ‖x‖ / 2 := by field_simp
        rw [this]; nlinarith [norm_nonneg x]

/-- **Low-mode localization for the tilted unit spline at every overlap.** -/
theorem tiltedUnitSpline_lowSpace_near_ramanujan {c : ℝ} (hc : 0 < c) (T : ℝ)
    (hT : ∀ m : ℕ, 0 < m → completedConductorEnergy tiltedUnitSpline c m ≠ T) {ε : ℝ}
    (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      (∀ m ∈ completedEnergySublevel tiltedUnitSpline hc T,
        ‖normalizedRamanujanHorizonVector m N - hermitianEigenProjection
          (completeWeilMatrix_isHermitian tiltedUnitSpline c N)
            (completeWeilSpectralSublevel tiltedUnitSpline c N T)
            (normalizedRamanujanHorizonVector m N)‖ ≤ ε) ∧
      ∀ x ∈ completeWeilLowSpace tiltedUnitSpline c N T, ∃ y ∈ Submodule.span ℝ
        ((fun m => normalizedRamanujanHorizonVector m N) ''
          (completedEnergySublevel tiltedUnitSpline hc T : Set ℕ)), ‖x - y‖ ≤ ε * ‖x‖ := by
  obtain ⟨a, β, hβ, hres⟩ :=
    CriticalArithmeticCorrelationTheory.exists_tiltedUnitSpline_completeWeilEnergy_reserve hc
  exact eventually_completeWeil_lowSpace_near_ramanujan hc hβ hres
    (fun _ hm => CriticalArithmeticCorrelationTheory.tendsto_completeWeilMatrix_ramanujan_quasimode_norm
      contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos hc hm) T hT hε

/-! ### Growing overlap -/

/-- **Diagonal schedule.** A family of eventual statements, one per index `k`, holds along some
unbounded schedule `k = s(N)`. -/
theorem exists_schedule_of_forall_eventually (P : ℕ → ℕ → Prop) (h : ∀ k, ∀ᶠ N : ℕ in atTop, P k N) :
    ∃ s : ℕ → ℕ, Tendsto s atTop atTop ∧ ∀ᶠ N : ℕ in atTop, P (s N) N := by
  have h' : ∀ k : ℕ, ∃ M : ℕ, ∀ N, M ≤ N → P k N := fun k => eventually_atTop.mp (h k)
  choose M hM using h'
  set M' : ℕ → ℕ := fun k => (∑ j ∈ range (k + 1), M j) + k with hM'
  have hle : ∀ k, M k ≤ M' k := fun k => by
    have : M k ≤ ∑ j ∈ range (k + 1), M j :=
      single_le_sum (f := M) (fun _ _ => Nat.zero_le _) (mem_range.mpr (Nat.lt_succ_self k))
    simp only [hM']; omega
  refine ⟨fun N => Nat.findGreatest (fun k => M' k ≤ N) N, ?_, ?_⟩
  · refine tendsto_atTop_atTop.mpr fun K => ⟨M' K, fun N hN => ?_⟩
    have hKN : K ≤ N := (show K ≤ M' K by simp only [hM']; omega).trans hN
    exact Nat.le_findGreatest hKN hN
  · filter_upwards [eventually_ge_atTop (M' 0)] with N hN
    have hspec : M' (Nat.findGreatest (fun k => M' k ≤ N) N) ≤ N :=
      Nat.findGreatest_spec (P := fun k => M' k ≤ N) (Nat.zero_le N) hN
    exact hM _ N ((hle _).trans hspec)

/-- Above any `T` there is a threshold in `(T, T + 1]` off the completed energy set. -/
theorem exists_threshold_off_energies (φ : ℝ → ℝ) {c : ℝ} (hc : 0 < c) (T : ℝ) :
    ∃ T' : ℝ, T < T' ∧ T' ≤ T + 1 ∧ ∀ m : ℕ, 0 < m → completedConductorEnergy φ c m ≠ T' := by
  classical
  set F := completedEnergySublevel φ hc (T + 2)
  set g : ℕ → ℝ := fun j => T + 1 / ((j : ℝ) + 2)
  have hg : Function.Injective g := by
    intro i j hij
    simp only [g, add_right_inj, one_div, inv_inj] at hij
    exact_mod_cast (add_left_inj (2 : ℝ)).mp hij
  obtain ⟨j, hj⟩ := ((F.image (completedConductorEnergy φ c)).finite_toSet.preimage
    hg.injOn).infinite_compl.nonempty
  have hpos : (0 : ℝ) < 1 / ((j : ℝ) + 2) := by positivity
  have hle : 1 / ((j : ℝ) + 2) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith [j.cast_nonneg (α := ℝ)]
  refine ⟨g j, by simp only [g]; linarith, by simp only [g]; linarith, fun m hm hE => hj ?_⟩
  have hmF : m ∈ F := (mem_completedEnergySublevel φ hc (T + 2) m).mpr ⟨hm, by
    rw [hE]; simp only [g]; linarith⟩
  exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨m, hmF, hE⟩)

/-- **Localization along a growing overlap.** For every `T` there are thresholds `T_k ∈ (T, T + 1]`
and an unbounded schedule `k = s(N)` such that, at overlap `c = s(N) + 1`, every vector of the
spectral subspace below `T_{s(N)}` is within `1/(s(N) + 1)` (relatively) of the span of the
Ramanujan vectors of the conductors with completed energy below `T_{s(N)}`. -/
theorem exists_overlap_schedule_lowSpace_near_ramanujan (T : ℝ) :
    ∃ Tk : ℕ → ℝ, (∀ k, T < Tk k ∧ Tk k ≤ T + 1) ∧ ∃ s : ℕ → ℕ, Tendsto s atTop atTop ∧
      ∀ᶠ N : ℕ in atTop, ∀ x ∈ completeWeilLowSpace tiltedUnitSpline ((s N : ℝ) + 1) N (Tk (s N)),
        ∃ y ∈ Submodule.span ℝ ((fun m => normalizedRamanujanHorizonVector m N) ''
          (completedEnergySublevel tiltedUnitSpline (Nat.cast_add_one_pos (s N)) (Tk (s N)) : Set ℕ)),
            ‖x - y‖ ≤ 1 / ((s N : ℝ) + 1) * ‖x‖ := by
  have hT : ∀ k : ℕ, ∃ T' : ℝ, T < T' ∧ T' ≤ T + 1 ∧ ∀ m : ℕ, 0 < m →
      completedConductorEnergy tiltedUnitSpline ((k : ℝ) + 1) m ≠ T' := fun k =>
    exists_threshold_off_energies tiltedUnitSpline (Nat.cast_add_one_pos k) T
  choose Tk hTk using hT
  refine ⟨Tk, fun k => ⟨(hTk k).1, (hTk k).2.1⟩, ?_⟩
  obtain ⟨s, hs, hev⟩ := exists_schedule_of_forall_eventually
    (fun k N => ∀ x ∈ completeWeilLowSpace tiltedUnitSpline ((k : ℝ) + 1) N (Tk k),
      ∃ y ∈ Submodule.span ℝ ((fun m => normalizedRamanujanHorizonVector m N) ''
        (completedEnergySublevel tiltedUnitSpline (Nat.cast_add_one_pos k) (Tk k) : Set ℕ)),
          ‖x - y‖ ≤ 1 / ((k : ℝ) + 1) * ‖x‖)
    fun k => (tiltedUnitSpline_lowSpace_near_ramanujan (Nat.cast_add_one_pos k) (Tk k)
      (hTk k).2.2 (by positivity)).mono fun N hN => hN.2
  exact ⟨s, hs, hev⟩

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
