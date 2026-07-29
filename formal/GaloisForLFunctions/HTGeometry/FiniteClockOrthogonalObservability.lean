import GaloisForLFunctions.HTGeometry.FiniteConstraintGroupAverage

/-!
# Orthogonal observability for arbitrary finite quantum clocks

For a nonempty finite-period isometry `U`, the finite cyclic gauge average is the orthogonal
projection onto the stationary sector.  If `X` is self-adjoint and `ψ` is stationary, the
conditional-variance defect of the observable twirl is exactly the squared norm of the component
of `X ψ` erased by that projection.  Hence

`‖Φ_U(X) ψ‖² + Re ⟪ψ, (Φ_U(X²) - Φ_U(X)²) ψ⟫ = ‖X ψ‖²`.

This is a static information partition: it concerns what the clock-observer algebra retains, not
how a state evolves in a time parameter.  The physics interpretation is the finite cyclic form of
group-asymmetry as reference-frame information; see de la Hamette--Ludescher--Mueller,
*Entanglement-asymmetry correspondence for internal quantum reference frames*, arXiv:2112.00046,
and Helsen et al., *Real Randomized Benchmarking*, arXiv:1801.06121, for the finite-group twirl as
the orthogonal projection onto the commutant.
-/

open scoped BigOperators

namespace HTGeometry

section AlgebraicOrbitIdentities

variable {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- A cyclic shift does not change a finite power sum when the final power closes the period. -/
theorem sum_pow_period_sub_eq
    (U : E →L[𝕜] E) (N : ℕ) (hperiod : U ^ N = 1) :
    (∑ k ∈ Finset.range N, U ^ (N - k)) =
      ∑ k ∈ Finset.range N, U ^ k := by
  have hcycle :
      (∑ k ∈ Finset.range N, U ^ (k + 1)) =
        ∑ k ∈ Finset.range N, U ^ k := by
    have hsame :
        (∑ k ∈ Finset.range N, U ^ k) + U ^ N =
          (∑ k ∈ Finset.range N, U ^ (k + 1)) + U ^ 0 := by
      rw [← Finset.sum_range_succ, ← Finset.sum_range_succ']
    rw [hperiod, pow_zero] at hsame
    exact (add_right_cancel hsame).symm
  calc
    (∑ k ∈ Finset.range N, U ^ (N - k)) =
        ∑ k ∈ Finset.range N, U ^ (N - 1 - k + 1) := by
      apply Finset.sum_congr rfl
      intro k hk
      congr 1
      have hkN : k < N := Finset.mem_range.mp hk
      omega
    _ = ∑ k ∈ Finset.range N, U ^ (k + 1) :=
      Finset.sum_range_reflect (fun k => U ^ (k + 1)) N
    _ = ∑ k ∈ Finset.range N, U ^ k := hcycle

/-- The recursive observable-twirl numerator is the finite sum of symmetric cyclic conjugates. -/
theorem finiteCyclicObservableTwirlNumerator_eq_sum
    (U X : E →L[𝕜] E) : ∀ N : ℕ,
    finiteCyclicObservableTwirlNumerator U X N =
      ∑ k ∈ Finset.range N, U ^ k * X * U ^ (N - k)
  | 0 => by simp [finiteCyclicObservableTwirlNumerator]
  | n + 1 => by
      simp only [finiteCyclicObservableTwirlNumerator, Finset.sum_range_succ']
      rw [finiteCyclicObservableTwirlNumerator_eq_sum U X n, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro k hk
      have hkN : k < n := Finset.mem_range.mp hk
      rw [show n + 1 - (k + 1) = n - k by omega, pow_succ']
      simp only [mul_assoc]

/-- On a stationary vector, the observable-twirl numerator is the gauge orbit sum of the observed
vector. -/
theorem finiteCyclicObservableTwirlNumerator_apply_of_fixed
    (U X : E →L[𝕜] E) (N : ℕ) {ψ : E} (hψ : U ψ = ψ) :
    finiteCyclicObservableTwirlNumerator U X N ψ =
      finiteCyclicGaugeSum U N (X ψ) := by
  have hpow : ∀ k : ℕ, (U ^ k) ψ = ψ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [pow_succ, mul_apply_eq_comp, hψ, ih]
  rw [finiteCyclicObservableTwirlNumerator_eq_sum, finiteCyclicGaugeSum]
  simp only [_root_.sum_apply]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [mul_apply_eq_comp, hpow]

/-- On a stationary vector, twirling an observable is exactly projecting the observed vector onto
the stationary sector. -/
theorem finiteCyclicObservableTwirl_apply_of_fixed
    (U X : E →L[𝕜] E) (N : ℕ) {ψ : E} (hψ : U ψ = ψ) :
    finiteCyclicObservableTwirl U X N ψ =
      finiteCyclicGaugeAverage U N (X ψ) := by
  rw [finiteCyclicObservableTwirl, finiteCyclicGaugeAverage,
    _root_.smul_apply, _root_.smul_apply,
    finiteCyclicObservableTwirlNumerator_apply_of_fixed U X N hψ]

end AlgebraicOrbitIdentities

section OrthogonalFiniteClock

variable {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- For a nonempty periodic isometry, the adjoint is the final inverse power in the cycle. -/
theorem adjoint_eq_pow_pred_of_periodic_isometry
    (U : E →L[𝕜] E) (N : ℕ) (hN : N ≠ 0)
    (hadjoint_mul : U.adjoint * U = 1) (hperiod : U ^ N = 1) :
    U.adjoint = U ^ (N - 1) := by
  have hpos : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hN
  have hright : U * U ^ (N - 1) = 1 := by
    calc
      U * U ^ (N - 1) = U ^ ((N - 1) + 1) := (pow_succ' U (N - 1)).symm
      _ = U ^ N := by rw [Nat.sub_add_cancel hpos]
      _ = 1 := hperiod
  calc
    U.adjoint = U.adjoint * 1 := by simp
    _ = U.adjoint * (U * U ^ (N - 1)) := by rw [hright]
    _ = (U.adjoint * U) * U ^ (N - 1) := by rw [mul_assoc]
    _ = U ^ (N - 1) := by rw [hadjoint_mul, one_mul]

/-- The adjoint of every power in a periodic isometric cycle is its complementary power. -/
theorem adjoint_pow_eq_period_sub_of_periodic_isometry
    (U : E →L[𝕜] E) (N k : ℕ) (hN : N ≠ 0) (hk : k ≤ N)
    (hadjoint_mul : U.adjoint * U = 1) (hperiod : U ^ N = 1) :
    (U ^ k).adjoint = U ^ (N - k) := by
  have hUadj :=
    adjoint_eq_pow_pred_of_periodic_isometry U N hN hadjoint_mul hperiod
  have hcomm : U.adjoint * U = U * U.adjoint := by
    rw [hUadj]
    exact (Commute.self_pow U (N - 1)).eq.symm
  have hleft : (U ^ k).adjoint * U ^ k = 1 := by
    rw [show (U ^ k).adjoint = U.adjoint ^ k by
      simp only [← ContinuousLinearMap.star_eq_adjoint, star_pow]]
    have hcomm' : Commute U.adjoint U := hcomm
    rw [← hcomm'.mul_pow, hadjoint_mul, one_pow]
  have hright : U ^ k * U ^ (N - k) = 1 := by
    rw [← pow_add, Nat.add_sub_of_le hk, hperiod]
  calc
    (U ^ k).adjoint = (U ^ k).adjoint * 1 := by simp
    _ = (U ^ k).adjoint * (U ^ k * U ^ (N - k)) := by rw [hright]
    _ = ((U ^ k).adjoint * U ^ k) * U ^ (N - k) := by rw [mul_assoc]
    _ = U ^ (N - k) := by rw [hleft, one_mul]

/-- The orbit sum of an arbitrary finite-period isometry is self-adjoint.  The clock step itself
need not be self-adjoint. -/
theorem finiteCyclicGaugeSum_isSelfAdjoint_of_periodic_isometry
    (U : E →L[𝕜] E) (N : ℕ) (hN : N ≠ 0)
    (hadjoint_mul : U.adjoint * U = 1) (hperiod : U ^ N = 1) :
    IsSelfAdjoint (finiteCyclicGaugeSum U N) := by
  rw [isSelfAdjoint_iff]
  change (finiteCyclicGaugeSum U N).adjoint = finiteCyclicGaugeSum U N
  simp only [finiteCyclicGaugeSum]
  let adj : (E →L[𝕜] E) ≃ₗᵢ⋆[𝕜] (E →L[𝕜] E) :=
    ContinuousLinearMap.adjoint
  change adj (∑ k ∈ Finset.range N, U ^ k) = _
  rw [map_sum]
  have hterm : ∀ k ∈ Finset.range N, (U ^ k).adjoint = U ^ (N - k) := by
    intro k hk
    exact adjoint_pow_eq_period_sub_of_periodic_isometry U N k hN
      (Nat.le_of_lt (Finset.mem_range.mp hk)) hadjoint_mul hperiod
  rw [Finset.sum_congr rfl hterm]
  exact sum_pow_period_sub_eq U N hperiod

/-- The normalized gauge average of a nonempty finite-period isometry is self-adjoint. -/
theorem finiteCyclicGaugeAverage_isSelfAdjoint_of_periodic_isometry
    (U : E →L[𝕜] E) (N : ℕ) (hN : N ≠ 0)
    (hadjoint_mul : U.adjoint * U = 1) (hperiod : U ^ N = 1) :
    IsSelfAdjoint (finiteCyclicGaugeAverage U N) := by
  have hscalar : IsSelfAdjoint (((N : 𝕜)⁻¹) : 𝕜) := by
    rw [isSelfAdjoint_iff]
    simp
  exact hscalar.smul
    (finiteCyclicGaugeSum_isSelfAdjoint_of_periodic_isometry
      U N hN hadjoint_mul hperiod)

/-- **Arbitrary-period invariant/asymmetric energy partition.**  The finite clock average splits
every vector orthogonally into its stationary component and the component erased by the clock. -/
theorem norm_finiteCyclicGaugeAverage_sq_add_complement_sq_of_periodic_isometry
    (U : E →L[𝕜] E) (N : ℕ) (hN : N ≠ 0)
    (hadjoint_mul : U.adjoint * U = 1) (hperiod : U ^ N = 1) (ψ : E) :
    ‖finiteCyclicGaugeAverage U N ψ‖ ^ 2 +
        ‖(1 - finiteCyclicGaugeAverage U N) ψ‖ ^ 2 = ‖ψ‖ ^ 2 := by
  let P : E →L[𝕜] E := finiteCyclicGaugeAverage U N
  have hPAdj : P.adjoint = P := by
    simpa only [P, ContinuousLinearMap.star_eq_adjoint] using
      (finiteCyclicGaugeAverage_isSelfAdjoint_of_periodic_isometry
        U N hN hadjoint_mul hperiod).star_eq
  have hPP : P * P = P :=
    finiteCyclicGaugeAverage_idempotent U N hN hperiod
  have horth : inner 𝕜 (P ψ) ((1 - P) ψ) = 0 := by
    have hfix : P (P ψ) = P ψ := by
      rw [← mul_apply_eq_comp, hPP]
    calc
      inner 𝕜 (P ψ) ((1 - P) ψ) = inner 𝕜 (P ψ) (ψ - P ψ) := by simp
      _ = inner 𝕜 ψ (P.adjoint (ψ - P ψ)) :=
        (P.adjoint_inner_right ψ (ψ - P ψ)).symm
      _ = inner 𝕜 ψ (P (ψ - P ψ)) := by rw [hPAdj]
      _ = inner 𝕜 ψ (P ψ - P (P ψ)) := by rw [map_sub]
      _ = 0 := by rw [hfix, sub_self, inner_zero_right]
  have hsum : P ψ + (1 - P) ψ = ψ := by simp
  have hpyth :=
    norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (P ψ) ((1 - P) ψ) horth
  change ‖P ψ‖ ^ 2 + ‖(1 - P) ψ‖ ^ 2 = ‖ψ‖ ^ 2
  simp only [pow_two]
  calc
    ‖P ψ‖ * ‖P ψ‖ + ‖(1 - P) ψ‖ * ‖(1 - P) ψ‖ =
        ‖P ψ + (1 - P) ψ‖ * ‖P ψ + (1 - P) ψ‖ := hpyth.symm
    _ = ‖ψ‖ * ‖ψ‖ := by rw [hsum]

/-- A symmetric cyclic conjugate of a self-adjoint observable is self-adjoint. -/
theorem cyclicConjugate_isSelfAdjoint
    (U X : E →L[𝕜] E) (N k : ℕ) (hN : N ≠ 0) (hk : k ≤ N)
    (hadjoint_mul : U.adjoint * U = 1) (hperiod : U ^ N = 1)
    (hX : IsSelfAdjoint X) :
    IsSelfAdjoint (U ^ k * X * U ^ (N - k)) := by
  have hXadj : X.adjoint = X := by
    simpa only [ContinuousLinearMap.star_eq_adjoint] using hX.star_eq
  have hleft := adjoint_pow_eq_period_sub_of_periodic_isometry
    U N k hN hk hadjoint_mul hperiod
  have hright := adjoint_pow_eq_period_sub_of_periodic_isometry
    U N (N - k) hN (Nat.sub_le N k) hadjoint_mul hperiod
  rw [Nat.sub_sub_self hk] at hright
  rw [isSelfAdjoint_iff]
  change ContinuousLinearMap.adjoint
      (((U ^ k) ∘L X) ∘L (U ^ (N - k))) = _
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
    hleft, hright, hXadj]
  ext y
  rfl

/-- The full finite cyclic twirl numerator preserves self-adjointness for a periodic isometry. -/
theorem finiteCyclicObservableTwirlNumerator_isSelfAdjoint
    (U X : E →L[𝕜] E) (N : ℕ) (hN : N ≠ 0)
    (hadjoint_mul : U.adjoint * U = 1) (hperiod : U ^ N = 1)
    (hX : IsSelfAdjoint X) :
    IsSelfAdjoint (finiteCyclicObservableTwirlNumerator U X N) := by
  rw [finiteCyclicObservableTwirlNumerator_eq_sum]
  exact isSelfAdjoint_sum (Finset.range N) fun k hk =>
    cyclicConjugate_isSelfAdjoint U X N k hN
      (Nat.le_of_lt (Finset.mem_range.mp hk)) hadjoint_mul hperiod hX

/-- A finite-period isometric clock twirl preserves self-adjoint observables. -/
theorem finiteCyclicObservableTwirl_isSelfAdjoint
    (U X : E →L[𝕜] E) (N : ℕ) (hN : N ≠ 0)
    (hadjoint_mul : U.adjoint * U = 1) (hperiod : U ^ N = 1)
    (hX : IsSelfAdjoint X) :
    IsSelfAdjoint (finiteCyclicObservableTwirl U X N) := by
  have hscalar : IsSelfAdjoint (((N : 𝕜)⁻¹) : 𝕜) := by
    rw [isSelfAdjoint_iff]
    simp
  exact hscalar.smul
    (finiteCyclicObservableTwirlNumerator_isSelfAdjoint
      U X N hN hadjoint_mul hperiod hX)

/-- **Finite-clock erased-information law.**  On a stationary state, the twirl's complete
conditional-variance defect is exactly the squared norm of the observed vector rejected by the
stationary projection. -/
theorem re_inner_finiteCyclicObservableTwirlKadisonDefect_eq_erasedNormSq
    (U X : E →L[𝕜] E) (N : ℕ) (hN : N ≠ 0)
    (hadjoint_mul : U.adjoint * U = 1) (hperiod : U ^ N = 1)
    (hX : IsSelfAdjoint X) {ψ : E} (hψ : U ψ = ψ) :
    RCLike.re
        (inner 𝕜 ψ (finiteCyclicObservableTwirlKadisonDefect U X N ψ)) =
      ‖(1 - finiteCyclicGaugeAverage U N) (X ψ)‖ ^ 2 := by
  let Φ : E →L[𝕜] E := finiteCyclicObservableTwirl U X N
  let B : E →L[𝕜] E := X - Φ
  have hUadj := adjoint_eq_pow_pred_of_periodic_isometry
    U N hN hadjoint_mul hperiod
  have hpowfix : ∀ k : ℕ, (U ^ k) ψ = ψ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [pow_succ, mul_apply_eq_comp, hψ, ih]
  have hψleft : U.adjoint ψ = ψ := by
    rw [hUadj, hpowfix]
  have hΦadj : Φ.adjoint = Φ := by
    simpa only [Φ, ContinuousLinearMap.star_eq_adjoint] using
      (finiteCyclicObservableTwirl_isSelfAdjoint
        U X N hN hadjoint_mul hperiod hX).star_eq
  have hXadj : X.adjoint = X := by
    simpa only [ContinuousLinearMap.star_eq_adjoint] using hX.star_eq
  have hBadj : B.adjoint = B := by
    simp only [B, Φ]
    rw [ContinuousLinearMap.adjoint.map_sub, hXadj, hΦadj]
  have hvalue := inner_finiteCyclicObservableTwirlKadisonDefect_of_fixed
    U X N hN hperiod hψleft hψ
  have hBapply :
      B ψ = (1 - finiteCyclicGaugeAverage U N) (X ψ) := by
    simp only [B, Φ, _root_.sub_apply, one_apply_eq_self]
    rw [finiteCyclicObservableTwirl_apply_of_fixed U X N hψ]
  calc
    RCLike.re
        (inner 𝕜 ψ (finiteCyclicObservableTwirlKadisonDefect U X N ψ)) =
        RCLike.re (inner 𝕜 ψ ((B * B) ψ)) := by
          exact congrArg RCLike.re hvalue
    _ = RCLike.re (inner 𝕜 ψ (B.adjoint (B ψ))) := by
      rw [mul_apply_eq_comp, hBadj]
    _ = ‖B ψ‖ ^ 2 := (B.apply_norm_sq_eq_inner_adjoint_right ψ).symm
    _ = ‖(1 - finiteCyclicGaugeAverage U N) (X ψ)‖ ^ 2 := by rw [hBapply]

/-- **Clock-observable value partition.**  The observed vector energy is the sum of its retained
stationary value and the complete conditional-variance defect. -/
theorem finiteClock_observableValue_energy_partition
    (U X : E →L[𝕜] E) (N : ℕ) (hN : N ≠ 0)
    (hadjoint_mul : U.adjoint * U = 1) (hperiod : U ^ N = 1)
    (hX : IsSelfAdjoint X) {ψ : E} (hψ : U ψ = ψ) :
    ‖finiteCyclicObservableTwirl U X N ψ‖ ^ 2 +
        RCLike.re
          (inner 𝕜 ψ (finiteCyclicObservableTwirlKadisonDefect U X N ψ)) =
      ‖X ψ‖ ^ 2 := by
  have hsplit :=
    norm_finiteCyclicGaugeAverage_sq_add_complement_sq_of_periodic_isometry
      U N hN hadjoint_mul hperiod (X ψ)
  rw [← finiteCyclicObservableTwirl_apply_of_fixed U X N hψ,
    ← re_inner_finiteCyclicObservableTwirlKadisonDefect_eq_erasedNormSq
      U X N hN hadjoint_mul hperiod hX hψ] at hsplit
  exact hsplit

/-- The finite-clock conditional-variance value is nonnegative on every stationary state. -/
theorem re_inner_finiteCyclicObservableTwirlKadisonDefect_nonneg
    (U X : E →L[𝕜] E) (N : ℕ) (hN : N ≠ 0)
    (hadjoint_mul : U.adjoint * U = 1) (hperiod : U ^ N = 1)
    (hX : IsSelfAdjoint X) {ψ : E} (hψ : U ψ = ψ) :
    0 ≤ RCLike.re
      (inner 𝕜 ψ (finiteCyclicObservableTwirlKadisonDefect U X N ψ)) := by
  rw [re_inner_finiteCyclicObservableTwirlKadisonDefect_eq_erasedNormSq
    U X N hN hadjoint_mul hperiod hX hψ]
  positivity

/-- Zero finite-clock defect means that twirling loses none of the observable action on the
stationary state. -/
theorem re_inner_finiteCyclicObservableTwirlKadisonDefect_eq_zero_iff_twirl_fixed
    (U X : E →L[𝕜] E) (N : ℕ) (hN : N ≠ 0)
    (hadjoint_mul : U.adjoint * U = 1) (hperiod : U ^ N = 1)
    (hX : IsSelfAdjoint X) {ψ : E} (hψ : U ψ = ψ) :
    RCLike.re
        (inner 𝕜 ψ (finiteCyclicObservableTwirlKadisonDefect U X N ψ)) = 0 ↔
      finiteCyclicObservableTwirl U X N ψ = X ψ := by
  rw [re_inner_finiteCyclicObservableTwirlKadisonDefect_eq_erasedNormSq
    U X N hN hadjoint_mul hperiod hX hψ]
  constructor
  · intro hz
    have hresidual : (1 - finiteCyclicGaugeAverage U N) (X ψ) = 0 := by
      exact norm_eq_zero.mp (sq_eq_zero_iff.mp hz)
    rw [finiteCyclicObservableTwirl_apply_of_fixed U X N hψ]
    have hxP : X ψ = finiteCyclicGaugeAverage U N (X ψ) := by
      apply sub_eq_zero.mp
      simpa only [_root_.sub_apply, one_apply_eq_self] using hresidual
    exact hxP.symm
  · intro hfixed
    rw [finiteCyclicObservableTwirl_apply_of_fixed U X N hψ] at hfixed
    simp [hfixed]

/-- Zero finite-clock defect discharges the physicality hypothesis for the observed vector, and
conversely. -/
theorem re_inner_finiteCyclicObservableTwirlKadisonDefect_eq_zero_iff_physical
    (U X : E →L[𝕜] E) (N : ℕ) (hN : N ≠ 0)
    (hadjoint_mul : U.adjoint * U = 1) (hperiod : U ^ N = 1)
    (hX : IsSelfAdjoint X) {ψ : E} (hψ : U ψ = ψ) :
    RCLike.re
        (inner 𝕜 ψ (finiteCyclicObservableTwirlKadisonDefect U X N ψ)) = 0 ↔
      GaloisForLFunctions.PhysicalState (U - 1).toLinearMap (X ψ) := by
  rw [re_inner_finiteCyclicObservableTwirlKadisonDefect_eq_zero_iff_twirl_fixed
      U X N hN hadjoint_mul hperiod hX hψ,
    finiteCyclicObservableTwirl_apply_of_fixed U X N hψ]
  exact (physicalState_iff_finiteCyclicGaugeAverage_fixed
    U N hN hperiod (X ψ)).symm

/-- **Arbitrary-period commutator criterion.**  On a stationary state, zero observability defect
is equivalent to the clock-observable commutator annihilating that state. -/
theorem re_inner_finiteCyclicObservableTwirlKadisonDefect_eq_zero_iff_commutator
    (U X : E →L[𝕜] E) (N : ℕ) (hN : N ≠ 0)
    (hadjoint_mul : U.adjoint * U = 1) (hperiod : U ^ N = 1)
    (hX : IsSelfAdjoint X) {ψ : E} (hψ : U ψ = ψ) :
    RCLike.re
        (inner 𝕜 ψ (finiteCyclicObservableTwirlKadisonDefect U X N ψ)) = 0 ↔
      (U * X - X * U) ψ = 0 := by
  rw [re_inner_finiteCyclicObservableTwirlKadisonDefect_eq_zero_iff_physical
    U X N hN hadjoint_mul hperiod hX hψ]
  rw [GaloisForLFunctions.PhysicalState]
  change (U - 1) (X ψ) = 0 ↔ (U * X - X * U) ψ = 0
  simp only [_root_.sub_apply, mul_apply_eq_comp,
    one_apply_eq_self, hψ]

end OrthogonalFiniteClock

end HTGeometry
