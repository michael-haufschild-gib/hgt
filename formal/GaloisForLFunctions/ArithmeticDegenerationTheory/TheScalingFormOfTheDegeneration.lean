import GaloisForLFunctions.ArithmeticDegenerationTheory.TheSubthresholdBlockIsUniformlyJordan

/-!
# The scaling form of the degeneration

The conductor energies of the tilted spline have an exact **scaling form**:

`E_m(c) = J(m) · c^{-7} · R_m(c/m)`   (`rpow_seven_mul_completedConductorEnergy_eq_scaling`),

with the Jordan coefficient `J(m)` and the scaling function

`R_m(x) = Σ_{(n,m)=1} n^{-8} g(nx) / (A_φ Σ_{(n,m)=1} n^{-8})`,   `g(y) = y⁷ T(y)`.

The conductor enters only through the ratio `x = c/m` and through which `n` are prime to `m`:
the degeneration is one profile function `g`, averaged over the coprime shells with weights
`n^{-8}`, times an arithmetic normalization.

* **Degenerating end** (`abs_scalingFunction_sub_one_le`): `R_m(x) → 1` as `x → ∞`, uniformly in
  `m`. This is the Jordan regime.
* **Pure end** (`scalingFunction_le`): `0 ≤ R_m(x) ≤ C x`, uniformly in `m`. For `m ≫ c` the energy is
  far below the Jordan extrapolation `J(m)c^{-7}`; the energies of the pure block do not degenerate.
* **Inherited polarization with arbitrarily small loss** (`eventually_inherited_polarization`): on
  every fixed finite conductor packet, along every schedule below the exponent `1/8`, eventually
  `c⁷ ⟨W x, x⟩ ≥ (1 − ε) Σ J(e) b_e²` uniformly in the coefficients — the form inherits the
  polarization of its rescaled limit up to a loss of `ε`.
-/

noncomputable section

open Filter Topology Finset MeasureTheory
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.ArithmeticDegenerationTheory

open RenormalizedArithmeticPotentialTheory RenormalizedArithmeticPotentialTheory.CompletedShell
  SpacingScaleHarmonicAnalysis

/-- The profile function `g(y) = y⁷ T(y)` of the tilted spline. -/
def tailProfile (y : ℝ) : ℝ := y ^ (7 : ℝ) * spectralTail tiltedUnitSpline y

/-- The coprime shell average `Σ_{(n,m)=1} n^{-8} g(nx)`. -/
def shellAverage (m : ℕ) (x : ℝ) : ℝ :=
  ∑' n : ℕ, if Nat.Coprime m (n + 1) then ((n : ℝ) + 1) ^ (-(8 : ℝ)) * tailProfile (((n : ℝ) + 1) * x)
    else 0

/-- The scaling function `R_m(x)`. -/
def scalingFunction (m : ℕ) (x : ℝ) : ℝ := shellAverage m x / (tiltedTailConstant * coprimeZetaSum 8 m)

theorem tailProfile_nonneg {y : ℝ} (hy : 0 ≤ y) : 0 ≤ tailProfile y :=
  mul_nonneg (Real.rpow_nonneg hy _) (spectralTail_nonneg y)

/-- `g(y) ≤ C y` for all `y ≥ 0`. -/
theorem exists_tailProfile_le_linear : ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, 0 ≤ y → tailProfile y ≤ C * y := by
  have hφ := contDiff_tiltedUnitSpline
  have hsupp : ∀ u : ℝ, u ∉ Set.Icc (0 : ℝ) 1 → tiltedUnitSpline u = 0 :=
    fun u hu => tiltedUnitSpline_eq_zero u hu
  obtain ⟨B, hB0, hB⟩ := exists_rpow_mul_spectralTail_le hφ hsupp (by norm_num : (0 : ℝ) < 7)
    tendsto_rpow_seven_mul_spectralTail_tiltedUnitSpline
  set I := ∫ t, shellSpectrum tiltedUnitSpline t
  have hI : 0 ≤ I := integral_nonneg fun t => shellSpectrum_nonneg t
  refine ⟨max B I, le_max_of_le_left hB0, fun y hy => ?_⟩
  rcases le_total 1 y with h1 | h1
  · calc tailProfile y ≤ B := hB y h1
      _ ≤ max B I := le_max_left _ _
      _ ≤ max B I * y := le_mul_of_one_le_right (le_max_of_le_left hB0) h1
  · have h7 : y ^ (7 : ℝ) ≤ y := by
      rcases hy.eq_or_lt with rfl | hy'
      · simp
      calc y ^ (7 : ℝ) ≤ y ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_ge hy' h1 (by norm_num)
        _ = y := Real.rpow_one y
    calc tailProfile y ≤ y * I :=
          mul_le_mul h7 (spectralTail_le_integral hφ hsupp y) (spectralTail_nonneg y) hy
      _ ≤ max B I * y := by rw [mul_comm]; exact mul_le_mul_of_nonneg_right (le_max_right _ _) hy

/-- The summand of the shell average is dominated by `B n^{-8}`. -/
theorem summable_shellAverage (m : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    Summable fun n : ℕ => if Nat.Coprime m (n + 1) then
      ((n : ℝ) + 1) ^ (-(8 : ℝ)) * tailProfile (((n : ℝ) + 1) * x) else 0 := by
  obtain ⟨C, hC0, hC⟩ := exists_tailProfile_le_linear
  have hs := (summable_shift_rpow_neg (k := 7) (by norm_num)).mul_left (C * x)
  refine hs.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
  · split_ifs
    · exact mul_nonneg (by positivity) (tailProfile_nonneg (by positivity))
    · exact le_rfl
  · have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    split_ifs
    · calc ((n : ℝ) + 1) ^ (-(8 : ℝ)) * tailProfile (((n : ℝ) + 1) * x)
          ≤ ((n : ℝ) + 1) ^ (-(8 : ℝ)) * (C * (((n : ℝ) + 1) * x)) :=
            mul_le_mul_of_nonneg_left (hC _ (by positivity)) (by positivity)
        _ = C * x * ((n : ℝ) + 1) ^ (-(7 : ℝ)) := by
            rw [show (-(7 : ℝ)) = -(8 : ℝ) + 1 by norm_num, Real.rpow_add hn, Real.rpow_one]
            ring
    · positivity

/-- **The scaling form of the degeneration.** `c⁷ E_m(c) = J(m) R_m(c/m)`. -/
theorem rpow_seven_mul_completedConductorEnergy_eq_scaling {c : ℝ} (hc : 0 < c) {m : ℕ}
    (hm : 0 < m) :
    c ^ (7 : ℝ) * completedConductorEnergy tiltedUnitSpline c m =
      jordanCoefficient m * scalingFunction m (c / m) := by
  have hφ := contDiff_tiltedUnitSpline
  have hsupp : ∀ u : ℝ, u ∉ Set.Icc (0 : ℝ) 1 → tiltedUnitSpline u = 0 :=
    fun u hu => tiltedUnitSpline_eq_zero u hu
  have hM := integral_tiltedUnitSpline_sq_pos
  set K := 2 / ((∫ u, tiltedUnitSpline u ^ 2) * m.totient) * (m : ℝ) ^ ((7 : ℝ) + 1)
  have hS := hasSum_rpow_mul_completedConductorEnergy hφ hsupp hM (β := 7) hc hm
  have hval : c ^ (7 : ℝ) * completedConductorEnergy tiltedUnitSpline c m = K * shellAverage m (c / m) := by
    rw [← hS.tsum_eq, shellAverage, ← tsum_mul_left]
    refine tsum_congr fun n => ?_
    split_ifs
    · simp only [K, tailProfile]
      rw [mul_div_assoc, show (7 : ℝ) + 1 = 8 by norm_num]
    · simp
  have hA := tiltedTailConstant_pos
  have hZ : 0 < coprimeZetaSum 8 m := lt_of_lt_of_le one_pos (one_le_coprimeZetaSum (by norm_num) m)
  rw [hval, jordanCoefficient_eq_coprime hm, scalingFunction]
  simp only [K]
  norm_num
  field_simp

theorem scalingFunction_nonneg (m : ℕ) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ scalingFunction m x := by
  have hA := tiltedTailConstant_pos
  have hZ : 0 < coprimeZetaSum 8 m := lt_of_lt_of_le one_pos (one_le_coprimeZetaSum (by norm_num) m)
  refine div_nonneg (tsum_nonneg fun n => ?_) (by positivity)
  split_ifs
  · exact mul_nonneg (by positivity) (tailProfile_nonneg (by positivity))
  · exact le_rfl

/-- **The pure end.** `R_m(x) ≤ C x` uniformly in the conductor. -/
theorem scalingFunction_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ, ∀ x : ℝ, 0 ≤ x → scalingFunction m x ≤ C * x := by
  obtain ⟨C, hC0, hC⟩ := exists_tailProfile_le_linear
  have hA := tiltedTailConstant_pos
  set Z7 := ∑' n : ℕ, ((n : ℝ) + 1) ^ (-(7 : ℝ))
  have hZ7 : 0 ≤ Z7 := tsum_nonneg fun n => by positivity
  refine ⟨C * Z7 / tiltedTailConstant, by positivity, fun m x hx => ?_⟩
  have hZ : 1 ≤ coprimeZetaSum 8 m := one_le_coprimeZetaSum (by norm_num) m
  have hsum := summable_shellAverage m hx
  have hs7 := (summable_shift_rpow_neg (k := 7) (by norm_num)).mul_left (C * x)
  have hle : shellAverage m x ≤ C * x * Z7 := by
    rw [shellAverage, ← tsum_mul_left]
    refine hsum.tsum_le_tsum (fun n => ?_) hs7
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    split_ifs
    · calc ((n : ℝ) + 1) ^ (-(8 : ℝ)) * tailProfile (((n : ℝ) + 1) * x)
          ≤ ((n : ℝ) + 1) ^ (-(8 : ℝ)) * (C * (((n : ℝ) + 1) * x)) :=
            mul_le_mul_of_nonneg_left (hC _ (by positivity)) (by positivity)
        _ = C * x * ((n : ℝ) + 1) ^ (-(7 : ℝ)) := by
            rw [show (-(7 : ℝ)) = -(8 : ℝ) + 1 by norm_num, Real.rpow_add hn, Real.rpow_one]
            ring
    · positivity
  have hnum : 0 ≤ shellAverage m x := tsum_nonneg fun n => by
    split_ifs
    · exact mul_nonneg (by positivity) (tailProfile_nonneg (by positivity))
    · exact le_rfl
  rw [scalingFunction, div_le_iff₀ (by positivity)]
  calc shellAverage m x ≤ C * x * Z7 := hle
    _ ≤ C * x * Z7 * coprimeZetaSum 8 m := le_mul_of_one_le_right (by positivity) hZ
    _ = C * Z7 / tiltedTailConstant * x * (tiltedTailConstant * coprimeZetaSum 8 m) := by
        field_simp

/-- **The degenerating end.** `R_m(x) → 1` as `x → ∞`, uniformly in the conductor. -/
theorem abs_scalingFunction_sub_one_le {ε : ℝ} (hε : 0 < ε) :
    ∃ X : ℝ, 1 ≤ X ∧ ∀ m : ℕ, 0 < m → ∀ x : ℝ, X ≤ x → |scalingFunction m x - 1| ≤ ε := by
  obtain ⟨X, hX1, hX⟩ := uniform_jordan_law hε
  refine ⟨X, hX1, fun m hm x hx => ?_⟩
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hx0 : 0 < x := lt_of_lt_of_le one_pos (hX1.trans hx)
  have hc : 0 < x * m := mul_pos hx0 hm0
  have h := hX (x * m) hc m hm (mul_le_mul_of_nonneg_right hx hm0.le)
  rw [rpow_seven_mul_completedConductorEnergy_eq_scaling hc hm, mul_div_cancel_right₀ _ hm0.ne'] at h
  have hJ := jordanCoefficient_pos hm
  rw [show jordanCoefficient m * scalingFunction m x - jordanCoefficient m =
      jordanCoefficient m * (scalingFunction m x - 1) by ring, abs_mul, abs_of_pos hJ] at h
  nlinarith [abs_nonneg (scalingFunction m x - 1)]

/-- **Inherited polarization with arbitrarily small loss.** On a fixed finite conductor packet, along
every schedule `c_N → ∞`, `c_N ≤ (log N)^α`, `α < 1/8`, eventually and uniformly in the coefficients,
`c_N⁷ ⟨W x, x⟩ ≥ (1 − ε) Σ J(e) b_e²`. -/
theorem eventually_inherited_polarization {α : ℝ} (hα : α < 1 / 8) {c : ℕ → ℝ}
    (hc : Tendsto c atTop atTop) (hcα : ∀ᶠ N : ℕ in atTop, c N ≤ Real.log N ^ α) {S : Finset ℕ}
    (hS : ∀ e ∈ S, 0 < e) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ b : ℕ → ℝ,
      (1 - ε) * ∑ e ∈ S, jordanCoefficient e * b e ^ 2 ≤
        ∑ e ∈ S, ∑ e' ∈ S, b e * b e' * rescaledConductorGram (c N) N e e' := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · exact Eventually.of_forall fun b => by simp
  -- the smallest Jordan coefficient on the packet
  obtain ⟨e₀, he₀, hmin⟩ := S.exists_min_image jordanCoefficient hne
  set Jmin := jordanCoefficient e₀
  have hJmin : 0 < Jmin := jordanCoefficient_pos (hS e₀ he₀)
  set η := ε * Jmin / S.card
  have hcard : (0 : ℝ) < S.card := by exact_mod_cast hne.card_pos
  have hη : 0 < η := by positivity
  have hent : ∀ᶠ N : ℕ in atTop, ∀ e ∈ S, ∀ e' ∈ S,
      |rescaledConductorGram (c N) N e e' - (if e = e' then jordanCoefficient e else 0)| ≤ η := by
    rw [eventually_all_finset]
    intro e he
    rw [eventually_all_finset]
    intro e' he'
    have h := (tendsto_rescaledConductorGram hα hc hcα (hS e he) (hS e' he')).eventually
      (Metric.closedBall_mem_nhds _ hη)
    filter_upwards [h] with N hN
    simpa [Real.dist_eq] using hN
  filter_upwards [hent] with N hN b
  -- split the rescaled form into its limit and the error
  have hdiag : ∑ e ∈ S, ∑ e' ∈ S, b e * b e' * (if e = e' then jordanCoefficient e else 0) =
      ∑ e ∈ S, jordanCoefficient e * b e ^ 2 := by
    refine sum_congr rfl fun e he => ?_
    rw [sum_eq_single_of_mem e he (fun e' _ hne' => by simp [Ne.symm hne'])]
    simp only [if_true]
    ring
  have herr : |∑ e ∈ S, ∑ e' ∈ S, b e * b e' * (rescaledConductorGram (c N) N e e' -
      (if e = e' then jordanCoefficient e else 0))| ≤ η * (∑ e ∈ S, |b e|) ^ 2 := by
    calc |∑ e ∈ S, ∑ e' ∈ S, b e * b e' * (rescaledConductorGram (c N) N e e' -
          (if e = e' then jordanCoefficient e else 0))|
        ≤ ∑ e ∈ S, ∑ e' ∈ S, |b e| * |b e'| * η := by
          refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun e he => ?_)
          refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun e' he' => ?_)
          rw [abs_mul, abs_mul]
          exact mul_le_mul_of_nonneg_left (hN e he e' he') (by positivity)
      _ = η * (∑ e ∈ S, |b e|) ^ 2 := by
          rw [sq, sum_mul_sum, mul_sum]
          refine sum_congr rfl fun e _ => ?_
          rw [mul_sum]
          exact sum_congr rfl fun e' _ => by ring
  have hcs : (∑ e ∈ S, |b e|) ^ 2 ≤ S.card * ∑ e ∈ S, b e ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := S) (f := fun e => |b e|)
    simpa [sq_abs] using this
  have hJb : Jmin * ∑ e ∈ S, b e ^ 2 ≤ ∑ e ∈ S, jordanCoefficient e * b e ^ 2 := by
    rw [mul_sum]
    exact sum_le_sum fun e he => mul_le_mul_of_nonneg_right (hmin e he) (sq_nonneg _)
  have hsplit : ∑ e ∈ S, ∑ e' ∈ S, b e * b e' * rescaledConductorGram (c N) N e e' =
      ∑ e ∈ S, jordanCoefficient e * b e ^ 2 + ∑ e ∈ S, ∑ e' ∈ S, b e * b e' *
        (rescaledConductorGram (c N) N e e' - (if e = e' then jordanCoefficient e else 0)) := by
    rw [← hdiag, ← sum_add_distrib]
    exact sum_congr rfl fun e _ => by rw [← sum_add_distrib]; exact sum_congr rfl fun e' _ => by ring
  have hηcard : η * S.card = ε * Jmin := by
    simp only [η]
    field_simp
  rw [hsplit]
  have hlow := neg_abs_le (∑ e ∈ S, ∑ e' ∈ S, b e * b e' *
    (rescaledConductorGram (c N) N e e' - (if e = e' then jordanCoefficient e else 0)))
  have h1 : η * (∑ e ∈ S, |b e|) ^ 2 ≤ ε * Jmin * ∑ e ∈ S, b e ^ 2 := by
    rw [← hηcard, mul_assoc]
    exact mul_le_mul_of_nonneg_left hcs hη.le
  have h2 : ε * Jmin * ∑ e ∈ S, b e ^ 2 ≤ ε * ∑ e ∈ S, jordanCoefficient e * b e ^ 2 := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hJb hε.le
  linarith

end GaloisForLFunctions.ArithmeticDegenerationTheory
