import GaloisForLFunctions.ExclusionOfTheCriticalState.Pick.TheRealProbeKernelIsAKreinForm
import GaloisForLFunctions.HTGeometry.ConvexDiffCountableConnected
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.OnePrimeSeesTheDefectOfEveryConfiguration
import GaloisForLFunctions.ArithmeticOrientationGeometry.TheIndexExit
import GaloisForLFunctions.ExclusionOfTheCriticalState.Index.TheSecondCriticalState
import GaloisForLFunctions.ExclusionOfTheCriticalState.Index.TheBoundedIndexStratumIsLindelofDeep

/-!
# The real probe kernel counts the zeros right of the line

The real Pick matrices `(K(p_i, p_j))`, `K(p, q) = (D(p) + D(q))/(p + q)`, `D = (log ξ)'(½ + ·)`, are
Weil's bare form on the half-line probes `e_{p_i}`. On every uniqueness set `S ⊆ [1, ∞)` of nodes
for bounded holomorphic functions on `Re w > 1` (`IsRightProbeUniquenessSet`; e.g. the integers
`n ≥ 2`) their negative squares count the zeros of `ζ` right of the critical line:

* **The probe index law** (`probeIndex_law`). Some real Pick matrix with nodes in `S` has `n`
  negative squares iff `ζ` has at least `n` zeros right of the line, in `ℕ∞`.
* **Integer form** (`integerProbeIndex_law`). The same for the explicit matrices
  `((D(m_i) + D(m_j))/(m_i + m_j))` with integer nodes `m_i ≥ 2`.
* **Corollaries.** RH iff every such matrix is positive semidefinite
  (`riemannHypothesis_iff_probeIndex_eq_zero`); off RH some has two negative squares; an odd number
  of negative squares forces one more (`probeIndex_even_step`); the index is bounded over all node
  families iff only finitely many zeros lie off the line (`probeIndex_bounded_iff_finiteOffLine`),
  which forces the Lindelöf hypothesis (`lindelof_of_probeIndex_bounded`).

Mechanism. `K(p, q) = ⟨R v_q, v_p⟩` with `v_p(ρ) = √m_ρ/(p − z_ρ)` (`bareMixedEnergy_probe_eq_inner`),
a Krein form whose negative directions are `e_ρ − e_{1−ρ̄}` for the zeros right of the line; the
upper bound is `hermNegIndex_probeGram_le`. For attainment the probe vectors are dense
(`orthogonal_probeSpan_eq_bot`): a vector `a` orthogonal to them makes the Cauchy transform
`F(w) = Σ_ρ √m_ρ a_ρ/(w − z̄_ρ)` vanish on the nodes; `F(w)/(w + 1)²` is bounded on `Re w > 1`
(`|F(w)| ≲ 1 + |w|²` by a Peetre-type bound and the temperedness of the zeros), so `F` vanishes
there, hence on the connected complement of the zero points, and its coefficient at each zero is read
off at `z̄_ρ + ε`. Combinations of probe vectors close to the negative directions then carry a
Gram matrix close to `−2 I` (`card_le_hermNegIndex_probeGram_of_near`).
-/

noncomputable section
open MeasureTheory Set Filter Topology Complex Metric
open scoped ComplexConjugate lp Matrix

namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri HTGeometry Zeta23
  _root_.RHTower

/-! ### Uniqueness sets right of `Re w = 1` -/

/-- Real nodes on which bounded holomorphic functions of `Re w > 1` are determined. -/
def IsRightProbeUniquenessSet (S : Set ℝ) : Prop :=
  ∀ G : ℂ → ℂ, DifferentiableOn ℂ G {w : ℂ | 1 < w.re} →
    (∃ C : ℝ, ∀ w : ℂ, 1 < w.re → ‖G w‖ ≤ C) →
    (∀ p ∈ S, G (p : ℂ) = 0) → ∀ w : ℂ, 1 < w.re → G w = 0

/-- The integers `n ≥ N`, `N ≥ 2`, are a uniqueness set right of `Re w = 1`. -/
theorem isRightProbeUniquenessSet_natFrom {N : ℕ} (hN : 2 ≤ N) :
    IsRightProbeUniquenessSet {p : ℝ | ∃ n : ℕ, N ≤ n ∧ p = n} := by
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  rintro G hG ⟨C, hC⟩ hz
  refine eqOn_zero_of_bounded_of_blaschke_divergent (δ := 1) zero_le_one hG hC
    (Λ := fun n : ℕ => ((n + N : ℕ) : ℝ)) ?_ ?_ ?_ ?_ ?_
  · intro a b h
    have := Nat.cast_injective (R := ℝ) h
    omega
  · rw [Nat.cofinite_eq_atTop]
    exact tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat N)
  · intro n
    push_cast
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  · intro n
    exact hz _ ⟨n + N, by omega, rfl⟩
  · intro hs
    have hle : ∀ n : ℕ, (1 : ℝ) / ((n + N : ℕ) : ℝ) ≤
        2 * (((n + N : ℕ) : ℝ) / (1 + ((n + N : ℕ) : ℝ) ^ 2)) := by
      intro n
      have hx : (1 : ℝ) ≤ ((n + N : ℕ) : ℝ) := by
        push_cast
        have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        linarith
      rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    have hsum : Summable fun n : ℕ => (1 : ℝ) / ((n + N : ℕ) : ℝ) :=
      Summable.of_nonneg_of_le (fun n => by positivity) hle (hs.mul_left 2)
    exact Real.not_summable_one_div_natCast ((summable_nat_add_iff N).mp hsum)

/-! ### The zero points and a Peetre bound -/

/-- The conjugated centred zero `z̄_ρ`, the pole of the Cauchy transform. -/
def zeroPoint (τ : zetaZeroConfig.carrier) : ℂ := conj ((τ : ℂ) - 1 / 2)

theorem zeroPoint_injective : Function.Injective zeroPoint := fun a b h => by
  have h' := congrArg conj h
  simp only [zeroPoint, Complex.conj_conj, sub_left_inj] at h'
  exact Subtype.ext h'

theorem re_zeroPoint_le (τ : zetaZeroConfig.carrier) : (zeroPoint τ).re ≤ 1 / 2 := by
  rw [zeroPoint, Complex.conj_re]
  exact (le_abs_self _).trans (abs_re_carrier_sub_half τ)

theorem norm_zeroPoint_sq (τ : zetaZeroConfig.carrier) :
    ‖zeroPoint τ‖ ^ 2 = Complex.normSq ((τ : ℂ) - 1 / 2) := by
  rw [zeroPoint, Complex.norm_conj, Complex.sq_norm]

/-- **Local separation of the zero points.** Around every point the other zero points keep a positive
distance: only finitely many zeros lie in a window of height two. -/
theorem exists_pos_le_norm_sub_zeroPoint (w₀ : ℂ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ τ : zetaZeroConfig.carrier, zeroPoint τ ≠ w₀ →
      δ ≤ ‖w₀ - zeroPoint τ‖ := by
  classical
  set S : Set ℂ := zetaZeroConfig.carrier ∩ {ρ | -w₀.im - 1 < ρ.im ∧ ρ.im ≤ -w₀.im + 1} with hSdef
  have hS : S.Finite := zetaZeroConfig.finite_window _ _
  have hfar : ∀ τ : zetaZeroConfig.carrier, (τ : ℂ) ∉ S → 1 ≤ ‖w₀ - zeroPoint τ‖ := by
    intro τ hτ
    have hnot : ¬ (-w₀.im - 1 < (τ : ℂ).im ∧ (τ : ℂ).im ≤ -w₀.im + 1) := fun h => hτ ⟨τ.2, h⟩
    have him : (w₀ - zeroPoint τ).im = w₀.im + (τ : ℂ).im := by
      simp [zeroPoint]
    have h1 := Complex.abs_im_le_norm (w₀ - zeroPoint τ)
    rw [him] at h1
    refine le_trans ?_ h1
    rcases not_and_or.mp hnot with h | h
    · rw [abs_of_nonpos (by linarith)]
      linarith
    · rw [abs_of_pos (by linarith)]
      linarith
  set F : Finset ℂ := hS.toFinset.filter fun ρ => conj (ρ - 1 / 2) ≠ w₀ with hF
  by_cases hFn : F.Nonempty
  · obtain ⟨ρ₁, hρ₁, hmin⟩ := F.exists_min_image (fun ρ => ‖w₀ - conj (ρ - 1 / 2)‖) hFn
    have hpos : 0 < ‖w₀ - conj (ρ₁ - 1 / 2)‖ :=
      norm_pos_iff.mpr (sub_ne_zero.mpr (Finset.mem_filter.mp hρ₁).2.symm)
    refine ⟨min 1 ‖w₀ - conj (ρ₁ - 1 / 2)‖, lt_min one_pos hpos, fun τ hτ => ?_⟩
    by_cases hτS : (τ : ℂ) ∈ S
    · exact (min_le_right _ _).trans
        (hmin τ (Finset.mem_filter.mpr ⟨hS.mem_toFinset.mpr hτS, hτ⟩))
    · exact (min_le_left _ _).trans (hfar τ hτS)
  · refine ⟨1, one_pos, fun τ hτ => ?_⟩
    have hτS : (τ : ℂ) ∉ S := fun hm =>
      hFn ⟨τ, Finset.mem_filter.mpr ⟨hS.mem_toFinset.mpr hm, hτ⟩⟩
    exact hfar τ hτS

/-- **Peetre-type bound**: at distance `≥ δ` from `ζ`, `|w − ζ|⁻² ≤ K/(1 + |ζ|²)`. -/
theorem inv_sq_norm_sub_le {w ζ : ℂ} {δ R : ℝ} (hδ : 0 < δ) (hR : ‖w‖ ≤ R)
    (h : δ ≤ ‖w - ζ‖) :
    1 / ‖w - ζ‖ ^ 2 ≤ ((1 + 2 * R ^ 2) / δ ^ 2 + 2) / (1 + ‖ζ‖ ^ 2) := by
  set d := ‖w - ζ‖
  have hd : 0 < d := hδ.trans_le h
  have hζ : ‖ζ‖ ≤ ‖w‖ + d := by
    have := norm_sub_le w (w - ζ)
    rwa [sub_sub_cancel] at this
  have hw0 : 0 ≤ ‖w‖ := norm_nonneg _
  have hζ2 : ‖ζ‖ ^ 2 ≤ 2 * R ^ 2 + 2 * d ^ 2 := by
    have : ‖ζ‖ ≤ R + d := by linarith
    nlinarith [norm_nonneg ζ, sq_nonneg (R - d)]
  have hδd : δ ^ 2 ≤ d ^ 2 := pow_le_pow_left₀ hδ.le h 2
  have hK : (1 + 2 * R ^ 2) ≤ (1 + 2 * R ^ 2) / δ ^ 2 * d ^ 2 := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg R]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-! ### The Cauchy transform of a vector of `ℓ²` -/

/-- The term `√m_ρ a_ρ/(w − z̄_ρ)`. -/
def pairTerm (a : ℓ²(zetaZeroConfig.carrier, ℂ)) (w : ℂ) (τ : zetaZeroConfig.carrier) : ℂ :=
  ((Real.sqrt (zetaZeroConfig.mult τ) : ℝ) : ℂ) * a τ / (w - zeroPoint τ)

/-- The Peetre majorant `(|a_ρ|² + K m_ρ/(1 + |z_ρ|²))/2`. -/
def pairBound (a : ℓ²(zetaZeroConfig.carrier, ℂ)) (K : ℝ) (τ : zetaZeroConfig.carrier) : ℝ :=
  (‖a τ‖ ^ 2 + K * ((zetaZeroConfig.mult τ : ℝ) / (1 + Complex.normSq ((τ : ℂ) - 1 / 2)))) / 2

theorem summable_pairBound (a : ℓ²(zetaZeroConfig.carrier, ℂ)) (K : ℝ) :
    Summable (pairBound a K) := by
  have h2 := (lp.memℓp a).summable (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at h2
  exact (h2.add (summable_mult_div_normSq.mul_left K)).div_const 2

theorem norm_pairTerm_le (a : ℓ²(zetaZeroConfig.carrier, ℂ)) {w : ℂ} {δ R : ℝ} (hδ : 0 < δ)
    (hR : ‖w‖ ≤ R) {τ : zetaZeroConfig.carrier} (h : δ ≤ ‖w - zeroPoint τ‖) :
    ‖pairTerm a w τ‖ ≤ pairBound a ((1 + 2 * R ^ 2) / δ ^ 2 + 2) τ := by
  set d := ‖w - zeroPoint τ‖
  have hd : 0 < d := hδ.trans_le h
  set m : ℝ := (zetaZeroConfig.mult τ : ℝ)
  have hm : 0 ≤ m := Nat.cast_nonneg _
  set N := Complex.normSq ((τ : ℂ) - 1 / 2)
  have hN : 0 < 1 + N := by have := Complex.normSq_nonneg ((τ : ℂ) - 1 / 2); linarith
  have hP := inv_sq_norm_sub_le hδ hR h
  rw [norm_zeroPoint_sq] at hP
  have hs : Real.sqrt m ^ 2 = m := Real.sq_sqrt hm
  have hnorm : ‖pairTerm a w τ‖ = ‖a τ‖ * (Real.sqrt m / d) := by
    rw [pairTerm, norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    ring
  rw [hnorm, pairBound]
  have hAM : ‖a τ‖ * (Real.sqrt m / d) ≤ (‖a τ‖ ^ 2 + (Real.sqrt m / d) ^ 2) / 2 := by
    nlinarith [sq_nonneg (‖a τ‖ - Real.sqrt m / d)]
  have hsq : (Real.sqrt m / d) ^ 2 = m * (1 / d ^ 2) := by
    rw [div_pow, hs]
    ring
  have hK : m * (1 / d ^ 2) ≤ ((1 + 2 * R ^ 2) / δ ^ 2 + 2) * (m / (1 + N)) := by
    calc m * (1 / d ^ 2) ≤ m * (((1 + 2 * R ^ 2) / δ ^ 2 + 2) / (1 + N)) :=
          mul_le_mul_of_nonneg_left hP hm
      _ = ((1 + 2 * R ^ 2) / δ ^ 2 + 2) * (m / (1 + N)) := by ring
  linarith

/-- The Cauchy transform `F_a(w) = Σ_ρ √m_ρ a_ρ/(w − z̄_ρ)`. -/
def cauchyTransform (a : ℓ²(zetaZeroConfig.carrier, ℂ)) (w : ℂ) : ℂ := ∑' τ, pairTerm a w τ

/-- The Cauchy transform at a real node is the inner product with the probe vector. -/
theorem inner_probeVec_eq_cauchyTransform {p : ℝ} (hp : 1 ≤ p) (a : ℓ²(zetaZeroConfig.carrier, ℂ)) :
    inner ℂ (probeVec hp) a = cauchyTransform a p := by
  rw [lp.inner_eq_tsum, cauchyTransform]
  refine tsum_congr fun τ => ?_
  rw [RCLike.inner_apply', probeVec_apply, probeCoord, pairTerm, zeroPoint, map_div₀,
    Complex.conj_ofReal, map_sub, Complex.conj_ofReal]
  ring

/-- **Holomorphy off the zero points.** -/
theorem analyticAt_cauchyTransform (a : ℓ²(zetaZeroConfig.carrier, ℂ)) {w₀ : ℂ}
    (hw₀ : w₀ ∉ Set.range zeroPoint) : AnalyticAt ℂ (cauchyTransform a) w₀ := by
  obtain ⟨δ, hδ, hsep⟩ := exists_pos_le_norm_sub_zeroPoint w₀
  have hsep' : ∀ τ, δ ≤ ‖w₀ - zeroPoint τ‖ := fun τ => hsep τ fun h => hw₀ ⟨τ, h⟩
  have hball : ∀ w ∈ ball w₀ (δ / 2), ∀ τ, δ / 2 ≤ ‖w - zeroPoint τ‖ := by
    intro w hw τ
    have h1 := hsep' τ
    have h2 : ‖w₀ - w‖ < δ / 2 := by rwa [mem_ball, dist_eq_norm, norm_sub_rev] at hw
    have h3 := norm_sub_le_norm_sub_add_norm_sub w₀ w (zeroPoint τ)
    linarith
  have hR : ∀ w ∈ ball w₀ (δ / 2), ‖w‖ ≤ ‖w₀‖ + δ / 2 := by
    intro w hw
    have h2 : ‖w - w₀‖ < δ / 2 := by rwa [mem_ball, dist_eq_norm] at hw
    have := norm_le_insert' w w₀
    linarith [norm_sub_norm_le w w₀]
  have hd : DifferentiableOn ℂ (fun w => ∑' τ, pairTerm a w τ) (ball w₀ (δ / 2)) := by
    refine differentiableOn_tsum_of_summable_norm (F := fun τ w => pairTerm a w τ)
      (summable_pairBound a ((1 + 2 * (‖w₀‖ + δ / 2) ^ 2) / (δ / 2) ^ 2 + 2)) (fun τ => ?_)
      isOpen_ball (fun τ w hw => norm_pairTerm_le a (by positivity) (hR w hw) (hball w hw τ))
    intro w hw
    have hne : w - zeroPoint τ ≠ 0 :=
      norm_pos_iff.mp (lt_of_lt_of_le (by positivity) (hball w hw τ))
    show DifferentiableWithinAt ℂ
      (fun w => ((Real.sqrt (zetaZeroConfig.mult τ) : ℝ) : ℂ) * a τ / (w - zeroPoint τ)) _ w
    have h1 : DifferentiableAt ℂ (fun w : ℂ => w - zeroPoint τ) w := differentiableAt_id.sub_const _
    exact ((differentiableAt_const _).div h1 hne).differentiableWithinAt
  exact hd.analyticAt (isOpen_ball.mem_nhds (mem_ball_self (by positivity)))

/-- **Growth right of `Re w = 1`**: `|F_a(w)| ≤ A + B|w|²`. -/
theorem norm_cauchyTransform_le (a : ℓ²(zetaZeroConfig.carrier, ℂ)) {w : ℂ} (hw : 1 < w.re) :
    ‖cauchyTransform a w‖ ≤ ∑' τ, pairBound a ((1 + 2 * ‖w‖ ^ 2) / (1 / 2) ^ 2 + 2) τ := by
  have hsep : ∀ τ, (1 / 2 : ℝ) ≤ ‖w - zeroPoint τ‖ := fun τ => by
    have := Complex.re_le_norm (w - zeroPoint τ)
    rw [Complex.sub_re] at this
    linarith [re_zeroPoint_le τ]
  have hb := fun τ => norm_pairTerm_le a (by norm_num : (0 : ℝ) < 1 / 2) le_rfl (hsep τ)
  exact (norm_tsum_le_tsum_norm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb
    (summable_pairBound a _))).trans
    ((Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb (summable_pairBound a _)).tsum_le_tsum
      hb (summable_pairBound a _))

theorem tsum_pairBound_eq (a : ℓ²(zetaZeroConfig.carrier, ℂ)) (K : ℝ) :
    ∑' τ, pairBound a K τ = ((∑' τ, ‖a τ‖ ^ 2) + K *
      ∑' τ : zetaZeroConfig.carrier,
        (zetaZeroConfig.mult τ : ℝ) / (1 + Complex.normSq ((τ : ℂ) - 1 / 2))) / 2 := by
  have h2 := (lp.memℓp a).summable (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at h2
  unfold pairBound
  rw [tsum_div_const, h2.tsum_add (summable_mult_div_normSq.mul_left K), tsum_mul_left]

/-! ### Density of the probe vectors -/

/-- **Density.** Only `0` is orthogonal to the probe vectors of a uniqueness set of nodes. -/
theorem orthogonal_probeSpan_eq_bot {S : Set ℝ} (hS1 : ∀ p ∈ S, 1 ≤ p)
    (hU : IsRightProbeUniquenessSet S) :
    (Submodule.span ℂ (Set.range fun p : S => probeVec (hS1 p p.2)))ᗮ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro a ha
  have hzero : ∀ p ∈ S, cauchyTransform a p = 0 := fun p hp => by
    have h := (Submodule.mem_orthogonal _ a).mp ha (probeVec (hS1 p hp))
      (Submodule.subset_span ⟨⟨p, hp⟩, rfl⟩)
    rwa [inner_probeVec_eq_cauchyTransform] at h
  -- right of `Re w = 1` the transform divided by `(w + 1)²` is bounded
  set A : ℝ := ∑' τ, ‖a τ‖ ^ 2
  set M : ℝ := ∑' τ : zetaZeroConfig.carrier,
    (zetaZeroConfig.mult τ : ℝ) / (1 + Complex.normSq ((τ : ℂ) - 1 / 2))
  have hA : 0 ≤ A := tsum_nonneg fun _ => by positivity
  have hM : 0 ≤ M := tsum_nonneg fun τ => by
    have := Complex.normSq_nonneg ((τ : ℂ) - 1 / 2)
    positivity
  have hrange : ∀ w : ℂ, 1 < w.re → w ∉ Set.range zeroPoint := by
    rintro w hw ⟨τ, rfl⟩
    linarith [re_zeroPoint_le τ]
  have hG : ∀ w : ℂ, 1 < w.re → cauchyTransform a w / (w + 1) ^ 2 = 0 := by
    refine hU (fun w => cauchyTransform a w / (w + 1) ^ 2) ?_ ⟨(A + 14 * M) / 2, fun w hw => ?_⟩
      (fun p hp => by simp [hzero p hp])
    · intro w hw
      have hw1 : (w + 1) ^ 2 ≠ 0 := pow_ne_zero 2 fun h => by
        have := congrArg Complex.re h
        simp at this
        linarith [show (1 : ℝ) < w.re from hw]
      exact ((analyticAt_cauchyTransform a (hrange w hw)).differentiableAt.div
        ((differentiableAt_id.add_const 1).pow 2) hw1).differentiableWithinAt
    · have h1 := norm_cauchyTransform_le a hw
      rw [tsum_pairBound_eq] at h1
      have hw2 : 1 + ‖w‖ ^ 2 ≤ ‖w + 1‖ ^ 2 := by
        rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
        simp only [Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im, add_zero]
        nlinarith
      have hpos : 0 < ‖w + 1‖ ^ 2 := lt_of_lt_of_le (by positivity) hw2
      rw [norm_div, norm_pow, div_le_iff₀ hpos]
      have hk : ((1 + 2 * ‖w‖ ^ 2) / (1 / 2) ^ 2 + 2) = 6 + 8 * ‖w‖ ^ 2 := by ring
      rw [hk] at h1
      have hw0 : 0 ≤ ‖w‖ ^ 2 := by positivity
      nlinarith
  have hright : ∀ w : ℂ, 1 < w.re → cauchyTransform a w = 0 := fun w hw => by
    have h := hG w hw
    have hw1 : (w + 1) ^ 2 ≠ 0 := pow_ne_zero 2 fun h => by
      have := congrArg Complex.re h
      simp at this
      linarith
    exact (div_eq_zero_iff.mp h).resolve_right hw1
  -- the transform vanishes off the zero points
  have hcount : (Set.range zeroPoint).Countable := by
    haveI : Countable zetaZeroConfig.carrier :=
      (GaloisForLFunctions.SquareRootThreshold.carrier_countable zetaZeroConfig).to_subtype
    exact Set.countable_range _
  have h2 : (2 : ℂ) ∈ Set.univ \ Set.range zeroPoint :=
    ⟨trivial, hrange 2 (by norm_num)⟩
  have hU' : IsPreconnected (Set.univ \ Set.range zeroPoint) :=
    (isPathConnected_diff_of_countable_of_convex (by rw [Complex.rank_real_complex]; norm_num)
      convex_univ isOpen_univ hcount h2).isConnected.isPreconnected
  have hAn : AnalyticOnNhd ℂ (cauchyTransform a) (Set.univ \ Set.range zeroPoint) :=
    fun w hw => analyticAt_cauchyTransform a hw.2
  have hEq : EqOn (cauchyTransform a) (fun _ => 0) (Set.univ \ Set.range zeroPoint) :=
    hAn.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const hU' h2 (Filter.eventually_of_mem ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds
        (show (2 : ℂ) ∈ {w : ℂ | 1 < w.re} by norm_num)) fun w hw => hright w hw)
  -- the coefficient at each zero
  ext τ₀
  rw [lp.coeFn_zero, Pi.zero_apply]
  obtain ⟨δ, hδ, hsep⟩ := exists_pos_le_norm_sub_zeroPoint (zeroPoint τ₀)
  have hsep' : ∀ τ, τ ≠ τ₀ → δ ≤ ‖zeroPoint τ₀ - zeroPoint τ‖ := fun τ hτ =>
    hsep τ fun h => hτ (zeroPoint_injective h)
  set R : ℝ := ‖zeroPoint τ₀‖ + δ / 2
  set K : ℝ := (1 + 2 * R ^ 2) / (δ / 2) ^ 2 + 2
  set B : ℝ := ∑' τ, pairBound a K τ
  have hB : 0 ≤ B := tsum_nonneg fun τ => by
    unfold pairBound
    have := Complex.normSq_nonneg ((τ : ℂ) - 1 / 2)
    have hK : 0 ≤ K := by positivity
    positivity
  set c : ℂ := ((Real.sqrt (zetaZeroConfig.mult τ₀) : ℝ) : ℂ) * a τ₀
  have hle : ∀ ε : ℝ, 0 < ε → ε < δ / 2 → ‖c‖ ≤ ε * B := by
    intro ε hε hεδ
    set w : ℂ := zeroPoint τ₀ + ε
    have hwτ : ∀ τ, τ ≠ τ₀ → δ / 2 ≤ ‖w - zeroPoint τ‖ := by
      intro τ hτ
      have h1 := hsep' τ hτ
      have h3 := norm_sub_le_norm_sub_add_norm_sub (zeroPoint τ₀) w (zeroPoint τ)
      have h4 : ‖zeroPoint τ₀ - w‖ = ε := by
        rw [show zeroPoint τ₀ - w = -(ε : ℂ) by simp [w], norm_neg, Complex.norm_real,
          Real.norm_of_nonneg hε.le]
      linarith
    have hwR : ‖w‖ ≤ R := by
      have := norm_add_le (zeroPoint τ₀) (ε : ℂ)
      rw [Complex.norm_real, Real.norm_of_nonneg hε.le] at this
      simp only [R]
      linarith
    have hwU : w ∈ Set.univ \ Set.range zeroPoint := by
      refine ⟨trivial, ?_⟩
      rintro ⟨τ, hτ⟩
      by_cases h : τ = τ₀
      · subst h
        have : (ε : ℂ) = 0 := by simpa [w] using hτ.symm
        exact hε.ne' (Complex.ofReal_eq_zero.mp this)
      · have := hwτ τ h
        rw [hτ, sub_self, norm_zero] at this
        linarith
    have h0 : cauchyTransform a w = 0 := hEq hwU
    set g : zetaZeroConfig.carrier → ℂ := fun τ => if τ = τ₀ then 0 else pairTerm a w τ
    have hgb : ∀ τ, ‖g τ‖ ≤ pairBound a K τ := by
      intro τ
      by_cases h : τ = τ₀
      · simp only [g, if_pos h, norm_zero]
        unfold pairBound
        have := Complex.normSq_nonneg ((τ : ℂ) - 1 / 2)
        have hK : 0 ≤ K := by positivity
        positivity
      · simp only [g, if_neg h]
        exact norm_pairTerm_le a (by positivity) hwR (hwτ τ h)
    have hgs : Summable g := Summable.of_norm_bounded (summable_pairBound a K) hgb
    have hfs : Summable (pairTerm a w) := by
      have hs : Summable fun τ => if τ = τ₀ then pairTerm a w τ₀ else 0 :=
        summable_of_ne_finset_zero (s := {τ₀}) fun τ hτ => by
          rw [Finset.mem_singleton] at hτ
          exact if_neg hτ
      refine (hgs.add hs).congr fun τ => ?_
      by_cases h : τ = τ₀
      · rw [h]; simp [g]
      · simp only [g, if_neg h, add_zero]
    have hsplit : cauchyTransform a w = pairTerm a w τ₀ + ∑' τ, g τ :=
      hfs.tsum_eq_add_tsum_ite τ₀
    have hterm : pairTerm a w τ₀ = c / ε := by
      simp only [pairTerm, c, w, add_sub_cancel_left]
    have hgB : ‖∑' τ, g τ‖ ≤ B :=
      (norm_tsum_le_tsum_norm hgs.norm).trans (hgs.norm.tsum_le_tsum hgb (summable_pairBound a K))
    rw [h0, hterm] at hsplit
    have hc : c = -(ε : ℂ) * ∑' τ, g τ := by
      have hε0 : (ε : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hε.ne'
      have h1 : c / ε = -∑' τ, g τ := by linear_combination -hsplit
      calc c = c / ε * ε := (div_mul_cancel₀ c hε0).symm
        _ = -(ε : ℂ) * ∑' τ, g τ := by rw [h1]; ring
    rw [hc, norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg hε.le]
    exact mul_le_mul_of_nonneg_left hgB hε.le
  have hc0 : c = 0 := by
    by_contra hne
    have hpos : 0 < ‖c‖ := norm_pos_iff.mpr hne
    set ε : ℝ := min (δ / 4) (‖c‖ / (2 * (B + 1)))
    have hε : 0 < ε := lt_min (by positivity) (by positivity)
    have hεδ : ε < δ / 2 := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have h1 := hle ε hε hεδ
    have h2 : ε * B ≤ ‖c‖ / (2 * (B + 1)) * B := mul_le_mul_of_nonneg_right (min_le_right _ _) hB
    have h3 : ‖c‖ / (2 * (B + 1)) * B < ‖c‖ := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith
    linarith
  have hm : ((Real.sqrt (zetaZeroConfig.mult τ₀) : ℝ) : ℂ) ≠ 0 := by
    have : (1 : ℝ) ≤ zetaZeroConfig.mult τ₀ := by exact_mod_cast zetaZeroConfig.one_le_mult _ τ₀.2
    exact Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by linarith)).ne'
  exact (mul_eq_zero.mp hc0).resolve_left hm

/-! ### Attainment -/

/-- The reflection commutes with finite combinations. -/
theorem reflectVec_sum_smul {κ : Type*} (s : Finset κ) (c : κ → ℂ)
    (v : κ → ℓ²(zetaZeroConfig.carrier, ℂ)) :
    reflectVec zetaZeroConfig (∑ k ∈ s, c k • v k) =
      ∑ k ∈ s, c k • reflectVec zetaZeroConfig (v k) := by
  ext τ
  simp only [reflectVec_apply, lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply]

/-- The Krein Gram of the combinations `f_i = Σ_k C_{ik} v_{p_k}` is the congruence `C K Cᴴ` of the
probe Gram. -/
theorem inner_reflect_probeComb_eq {κ ι : Type*} [Fintype κ] {p : κ → ℝ} (hp : ∀ k, 1 ≤ p k)
    (C : Matrix ι κ ℂ) (i j : ι) :
    inner ℂ (reflectVec zetaZeroConfig (∑ k, C j k • probeVec (hp k)))
        (∑ k, C i k • probeVec (hp k)) = (C * probeGram p * Cᴴ) i j := by
  rw [reflectVec_sum_smul, sum_inner]
  simp only [inner_smul_left, inner_sum, inner_smul_right, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Finset.sum_mul, probeGram]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
  have hs : star (C j l) = conj (C j l) := rfl
  rw [← bareMixedEnergy_probe_eq_inner (hp k) (hp l)]
  try rw [hs]
  ring

/-- **Attainment from approximate targets.** If `n` vectors `t_i` with Krein Gram `−2 I` and norms
`≤ M` are each within `1/((2M + 1)(n + 1))` of a combination of probe vectors, the probe Gram has at
least `n` negative squares. -/
theorem card_le_hermNegIndex_probeGram_of_near {κ ι : Type*} [Fintype κ] [Fintype ι]
    [DecidableEq ι] {p : κ → ℝ} (hp : ∀ k, 1 ≤ p k) (t : ι → ℓ²(zetaZeroConfig.carrier, ℂ))
    (hRt : ∀ i j, inner ℂ (reflectVec zetaZeroConfig (t j)) (t i) = if i = j then -2 else 0)
    {M : ℝ} (hM : 1 ≤ M) (htM : ∀ i, ‖t i‖ ≤ M) (C : Matrix ι κ ℂ)
    (hx : ∀ i, ‖∑ k, C i k • probeVec (hp k) - t i‖ <
      1 / ((2 * M + 1) * ((Fintype.card ι : ℝ) + 1))) :
    Fintype.card ι ≤ hermNegIndex (probeGram p) := by
  set ε : ℝ := 1 / ((2 * M + 1) * ((Fintype.card ι : ℝ) + 1)) with hε
  have hk : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
  have hM' : 0 < 2 * M + 1 := by linarith
  have hε0 : 0 < ε := by positivity
  have hε1 : ε ≤ 1 := by
    rw [hε, div_le_one (by positivity)]
    nlinarith
  set f : ι → ℓ²(zetaZeroConfig.carrier, ℂ) := fun i => ∑ k, C i k • probeVec (hp k) with hf
  set G : Matrix ι ι ℂ := C * probeGram p * Cᴴ with hG
  have hentry : ∀ i j, ‖G i j - (if i = j then -2 else 0)‖ ≤ (2 * M + 1) * ε := by
    intro i j
    have hGij : G i j = inner ℂ (reflectVec zetaZeroConfig (f j)) (f i) :=
      (inner_reflect_probeComb_eq hp C i j).symm
    have hdi : f i = t i + (f i - t i) := by abel
    have hdj : f j = t j + (f j - t j) := by abel
    set ei := f i - t i
    set ej := f j - t j
    have hei : ‖ei‖ < ε := hx i
    have hej : ‖ej‖ < ε := hx j
    rw [hGij, hdi, hdj, reflectVec_add, inner_add_left, inner_add_right, inner_add_right, hRt i j]
    have h1 := (norm_inner_le_norm (𝕜 := ℂ) (reflectVec zetaZeroConfig (t j)) ei).trans_eq
      (by rw [norm_reflectVec])
    have h2 := (norm_inner_le_norm (𝕜 := ℂ) (reflectVec zetaZeroConfig ej) (t i)).trans_eq
      (by rw [norm_reflectVec])
    have h3 := (norm_inner_le_norm (𝕜 := ℂ) (reflectVec zetaZeroConfig ej) ei).trans_eq
      (by rw [norm_reflectVec])
    calc ‖(if i = j then -2 else 0) + inner ℂ (reflectVec zetaZeroConfig (t j)) ei +
          (inner ℂ (reflectVec zetaZeroConfig ej) (t i) +
            inner ℂ (reflectVec zetaZeroConfig ej) ei) - (if i = j then -2 else 0)‖
        = ‖inner ℂ (reflectVec zetaZeroConfig (t j)) ei +
            inner ℂ (reflectVec zetaZeroConfig ej) (t i) +
            inner ℂ (reflectVec zetaZeroConfig ej) ei‖ := by congr 1; ring
      _ ≤ ‖t j‖ * ‖ei‖ + ‖ej‖ * ‖t i‖ + ‖ej‖ * ‖ei‖ :=
        norm_add₃_le.trans (add_le_add (add_le_add h1 h2) h3)
      _ ≤ M * ε + ε * M + ε * ε := by
        have := htM i; have := htM j
        gcongr
      _ ≤ (2 * M + 1) * ε := by nlinarith [mul_le_mul_of_nonneg_left hε1 hε0.le]
  have hη : (2 * M + 1) * ε * (Fintype.card ι : ℝ) ≤ 1 := by
    rw [hε, show (2 * M + 1) * (1 / ((2 * M + 1) * ((Fintype.card ι : ℝ) + 1))) *
        (Fintype.card ι : ℝ) = Fintype.card ι / (Fintype.card ι + 1) by field_simp,
      div_le_one (by positivity)]
    linarith
  have hpd : IsPosDefOn (-G) ⊤ := fun y _ hy0 => by
    rw [hermQuad_neg]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hy0
    have hpos : 0 < ∑ i, ‖y i‖ ^ 2 :=
      lt_of_lt_of_le (pow_pos (norm_pos_iff.mpr hi) 2) (Finset.single_le_sum
        (f := fun i => ‖y i‖ ^ 2) (fun i _ => by positivity) (Finset.mem_univ i))
    linarith [hermQuad_le_of_near _ hη hentry y]
  have h1 := finrank_le_posIndex hpd
  rw [finrank_top, Module.finrank_fintype_fun_eq_card] at h1
  calc Fintype.card ι ≤ hermNegIndex G := h1
    _ ≤ hermNegIndex (probeGram p) := hermNegIndex_mul_mul_conjTranspose_le C _

/-- **Approximation by probes.** Every vector of `ℓ²` is within `ε` of a finite combination of probe
vectors with nodes in a uniqueness set. -/
theorem exists_finsupp_probe_near {S : Set ℝ} (hS1 : ∀ p ∈ S, 1 ≤ p)
    (hU : IsRightProbeUniquenessSet S) (t : ℓ²(zetaZeroConfig.carrier, ℂ)) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ c : S →₀ ℂ, ‖(c.sum fun p a => a • probeVec (hS1 p p.2)) - t‖ < ε := by
  have hd := Submodule.topologicalClosure_eq_top_iff.mpr (orthogonal_probeSpan_eq_bot hS1 hU)
  have ht : t ∈ closure (Submodule.span ℂ (Set.range fun p : S => probeVec (hS1 p p.2)) :
      Set (ℓ²(zetaZeroConfig.carrier, ℂ))) := by
    rw [← Submodule.topologicalClosure_coe, hd, Submodule.top_coe]
    exact Set.mem_univ t
  obtain ⟨v, hv, hvt⟩ := Metric.mem_closure_iff.mp ht ε hε
  obtain ⟨c, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hv
  exact ⟨c, by rwa [dist_comm, dist_eq_norm] at hvt⟩

/-! ### The probe index law -/

/-- **The probe index law.** On a uniqueness set of nodes `≥ 1`, some real Pick matrix of the probe
kernel has `n` negative squares iff `ζ` has at least `n` zeros right of the critical line. -/
theorem probeIndex_law {S : Set ℝ} (hS1 : ∀ p ∈ S, 1 ≤ p) (hU : IsRightProbeUniquenessSet S)
    (n : ℕ) :
    (∃ (N : ℕ) (p : Fin N → ℝ), (∀ i, p i ∈ S) ∧ n ≤ hermNegIndex (probeGram p)) ↔
      (n : ℕ∞) ≤ (rightZeros zetaZeroConfig).encard := by
  classical
  constructor
  · rintro ⟨N, p, hpS, hn⟩
    exact (ENat.coe_le_coe.mpr hn).trans (hermNegIndex_probeGram_le fun i => hS1 _ (hpS i))
  · intro hn
    obtain ⟨T, hTR, hTn⟩ := Set.exists_subset_encard_eq hn
    have hTf : T.Finite := Set.finite_of_encard_eq_coe hTn
    set F : Finset ℂ := hTf.toFinset with hF
    have hFn : F.card = n := by
      have h := hTf.encard_eq_coe_toFinset_card
      rw [hTn] at h
      exact_mod_cast h.symm
    have hmem : ∀ i : F, (i : ℂ) ∈ rightZeros zetaZeroConfig := fun i =>
      hTR (hTf.mem_toFinset.mp i.2)
    obtain ⟨r, hr⟩ : ∃ r : F → zetaZeroConfig.carrier, ∀ i, (r i : ℂ) = i :=
      ⟨fun i => ⟨i, (hmem i).1⟩, fun i => rfl⟩
    have hre : ∀ i, 1 / 2 < ((r i : zetaZeroConfig.carrier) : ℂ).re := fun i => by
      rw [hr i]; exact (hmem i).2
    have hRt : ∀ i j, inner ℂ (reflectVec zetaZeroConfig (kreinNegVec zetaZeroConfig (r j)))
        (kreinNegVec zetaZeroConfig (r i)) = if i = j then -2 else 0 := by
      intro i j
      rw [inner_reflect_kreinNegVec zetaZeroConfig (hre i) (hre j)]
      by_cases h : i = j
      · rw [if_pos h, if_pos (congrArg r h)]
      · refine (if_neg fun h' => h (Subtype.ext ?_)).trans (if_neg h).symm
        rw [← hr i, ← hr j, h']
    have hε0 : (0 : ℝ) < 1 / ((2 * 2 + 1) * ((Fintype.card F : ℝ) + 1)) := by positivity
    choose c hc using fun i : F =>
      exists_finsupp_probe_near hS1 hU (kreinNegVec zetaZeroConfig (r i)) hε0
    set P : Finset S := Finset.univ.biUnion fun i => (c i).support with hP
    set e : Fin P.card ≃ P := P.equivFin.symm with he
    set p : Fin P.card → ℝ := fun k => ((e k : S) : ℝ) with hp
    have hp1 : ∀ k, 1 ≤ p k := fun k => hS1 _ (e k : S).2
    set C : Matrix F (Fin P.card) ℂ := fun i k => c i (e k) with hC
    have hsum : ∀ i, ∑ k, C i k • probeVec (hp1 k) =
        (c i).sum fun q a => a • probeVec (hS1 q q.2) := by
      intro i
      have h1 := Finsupp.sum_of_support_subset (c i) (s := P)
        (fun q hq => Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hq⟩)
        (fun q a => a • probeVec (hS1 q q.2)) (fun q _ => zero_smul ℂ _)
      show ∑ k, c i (e k) • probeVec (hp1 k) = _
      rw [h1, ← Finset.sum_coe_sort P]
      exact Fintype.sum_equiv e _ _ fun k => rfl
    have hx : ∀ i, ‖∑ k, C i k • probeVec (hp1 k) - kreinNegVec zetaZeroConfig (r i)‖ <
        1 / ((2 * 2 + 1) * ((Fintype.card F : ℝ) + 1)) := fun i => by
      rw [hsum i]; exact hc i
    have h := card_le_hermNegIndex_probeGram_of_near hp1
      (fun i => kreinNegVec zetaZeroConfig (r i)) hRt (by norm_num : (1 : ℝ) ≤ 2)
      (fun i => norm_kreinNegVec_le zetaZeroConfig (r i)) C hx
    rw [Fintype.card_coe, hFn] at h
    exact ⟨P.card, p, fun k => (e k : S).2, h⟩

/-! ### Corollaries -/

/-- **RH is the vanishing of the probe index** on any uniqueness set of nodes `≥ 1`. -/
theorem riemannHypothesis_iff_probeIndex_eq_zero {S : Set ℝ} (hS1 : ∀ p ∈ S, 1 ≤ p)
    (hU : IsRightProbeUniquenessSet S) :
    RiemannHypothesis ↔
      ∀ (N : ℕ) (p : Fin N → ℝ), (∀ i, p i ∈ S) → hermNegIndex (probeGram p) = 0 := by
  rw [← rightZeros_zeta_eq_empty_iff, ← Set.encard_eq_zero]
  constructor
  · intro h N p hpS
    have h1 := hermNegIndex_probeGram_le fun i => hS1 _ (hpS i)
    rw [h] at h1
    have h2 : hermNegIndex (probeGram p) ≤ 0 := by exact_mod_cast h1
    omega
  · intro h
    by_contra hne
    have h1 : ((1 : ℕ) : ℕ∞) ≤ (rightZeros zetaZeroConfig).encard := by
      rw [Nat.cast_one]; exact Order.one_le_iff_ne_zero.mpr hne
    obtain ⟨N, p, hpS, hp⟩ := (probeIndex_law hS1 hU 1).mpr h1
    rw [h N p hpS] at hp
    omega

/-- **Off RH some real Pick matrix has two negative squares**: the zeros right of the line come in
conjugate pairs. -/
theorem exists_two_le_hermNegIndex_probeGram_of_not_RH {S : Set ℝ} (hS1 : ∀ p ∈ S, 1 ≤ p)
    (hU : IsRightProbeUniquenessSet S) (h : ¬ RiemannHypothesis) :
    ∃ (N : ℕ) (p : Fin N → ℝ), (∀ i, p i ∈ S) ∧ 2 ≤ hermNegIndex (probeGram p) := by
  refine (probeIndex_law hS1 hU 2).mpr ?_
  have h2 := two_le_rightZeros_encard_of_not_RH h
  exact_mod_cast h2

/-- **Negative squares come in pairs.** If a real Pick matrix on `S` has `2k + 1` negative squares,
another has `2k + 2`: the zeros right of the line are closed under conjugation and none is real. -/
theorem probeIndex_even_step {S : Set ℝ} (hS1 : ∀ p ∈ S, 1 ≤ p)
    (hU : IsRightProbeUniquenessSet S) {k : ℕ}
    (h : ∃ (N : ℕ) (p : Fin N → ℝ), (∀ i, p i ∈ S) ∧ 2 * k + 1 ≤ hermNegIndex (probeGram p)) :
    ∃ (N : ℕ) (p : Fin N → ℝ), (∀ i, p i ∈ S) ∧ 2 * k + 2 ≤ hermNegIndex (probeGram p) := by
  have h1 := (probeIndex_law hS1 hU (2 * k + 1)).mp h
  refine (probeIndex_law hS1 hU (2 * k + 2)).mpr ?_
  rcases (rightZeros zetaZeroConfig).finite_or_infinite with hfin | hinf
  · rw [hfin.encard_eq_coe_toFinset_card] at h1 ⊢
    have h1' : 2 * k + 1 ≤ hfin.toFinset.card := by exact_mod_cast h1
    obtain ⟨m, hm⟩ := ArithmeticOrientationGeometry.even_ncard_rightZeros hfin
    have h2 : 2 * k + 2 ≤ hfin.toFinset.card := by omega
    exact_mod_cast h2
  · rw [Set.encard_eq_top_iff.mpr hinf]
    exact le_top

section FiniteLayer
open _root_.RHTower.BacklundConverse _root_.RHTower.LindelofSparse

/-- **Bounded probe index is the finite layer.** The negative index of the real Pick matrices on `S`
is bounded iff only finitely many zeros of `ζ` lie off the critical line. -/
theorem probeIndex_bounded_iff_finiteOffLine {S : Set ℝ} (hS1 : ∀ p ∈ S, 1 ≤ p)
    (hU : IsRightProbeUniquenessSet S) :
    (∃ B : ℕ, ∀ (N : ℕ) (p : Fin N → ℝ), (∀ i, p i ∈ S) → hermNegIndex (probeGram p) ≤ B) ↔
      FiniteOffLine := by
  rw [← ArithmeticOrientationGeometry.rightZeros_zeta_finite_iff_finiteOffLine]
  constructor
  · rintro ⟨B, hB⟩
    by_contra hinf
    have htop : (rightZeros zetaZeroConfig).encard = ⊤ := Set.encard_eq_top_iff.mpr hinf
    obtain ⟨N, p, hpS, hp⟩ := (probeIndex_law hS1 hU (B + 1)).mpr (by rw [htop]; exact le_top)
    have := hB N p hpS
    omega
  · intro hfin
    refine ⟨hfin.toFinset.card, fun N p hpS => ?_⟩
    have h := hermNegIndex_probeGram_le fun i => hS1 _ (hpS i)
    rw [hfin.encard_eq_coe_toFinset_card] at h
    exact_mod_cast h

/-- **The Lindelöf wall on real nodes.** A bounded probe index forces the Lindelöf hypothesis and a
zero-free half-plane `Re s > ½ + α` with `α < ½`. -/
theorem lindelof_of_probeIndex_bounded {S : Set ℝ} (hS1 : ∀ p ∈ S, 1 ≤ p)
    (hU : IsRightProbeUniquenessSet S)
    (h : ∃ B : ℕ, ∀ (N : ℕ) (p : Fin N → ℝ), (∀ i, p i ∈ S) → hermNegIndex (probeGram p) ≤ B) :
    LindelofCriticalLine ∧ ∃ α : ℝ, α < 1 / 2 ∧ XiZeroHalfPlaneBound α :=
  lindelof_of_confinedIndexBounded
    ((confinedIndexBounded_tfae.out 2 0).mp ((probeIndex_bounded_iff_finiteOffLine hS1 hU).mp h))

end FiniteLayer

/-! ### Integer nodes -/

/-- The integer Pick matrix `((D(m_i) + D(m_j))/(m_i + m_j))` of the probe kernel. -/
def integerPickMatrix {N : ℕ} (m : Fin N → ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  fun i j => (((probeSymbol (m i) + probeSymbol (m j)) / ((m i : ℝ) + (m j : ℝ)) : ℝ) : ℂ)

theorem integerPickMatrix_eq_probeGram {N : ℕ} (m : Fin N → ℕ) (hm : ∀ i, 1 ≤ m i) :
    integerPickMatrix m = probeGram fun i => (m i : ℝ) := by
  have hh : ∀ i, (1 : ℝ) / 2 < m i := fun i => by
    have : (1 : ℝ) ≤ m i := by exact_mod_cast hm i
    linarith
  ext i j
  simp only [integerPickMatrix, probeGram]
  rw [bareMixedEnergy_probe (hh i) (hh j)]

/-- **The integer probe index law.** Some integer Pick matrix `((D(m_i) + D(m_j))/(m_i + m_j))` with
nodes `m_i ≥ 2` has `n` negative squares iff `ζ` has at least `n` zeros right of the line. -/
theorem integerProbeIndex_law (n : ℕ) :
    (∃ (N : ℕ) (m : Fin N → ℕ), (∀ i, 2 ≤ m i) ∧ n ≤ hermNegIndex (integerPickMatrix m)) ↔
      (n : ℕ∞) ≤ (rightZeros zetaZeroConfig).encard := by
  have hS1 : ∀ p ∈ {p : ℝ | ∃ m : ℕ, 2 ≤ m ∧ p = m}, 1 ≤ p := by
    rintro p ⟨m, hm, rfl⟩
    have : (2 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  rw [← probeIndex_law hS1 (isRightProbeUniquenessSet_natFrom le_rfl) n]
  constructor
  · rintro ⟨N, m, hm, hn⟩
    refine ⟨N, fun i => (m i : ℝ), fun i => ⟨m i, hm i, rfl⟩, ?_⟩
    rwa [← integerPickMatrix_eq_probeGram m fun i => le_trans (by norm_num) (hm i)]
  · rintro ⟨N, p, hpS, hn⟩
    have hpS' : ∀ i, ∃ m : ℕ, 2 ≤ m ∧ p i = m := hpS
    choose m hm hpm using hpS'
    refine ⟨N, m, hm, ?_⟩
    rw [integerPickMatrix_eq_probeGram m fun i => le_trans (by norm_num) (hm i)]
    have : (fun i => (m i : ℝ)) = p := funext fun i => (hpm i).symm
    rwa [this]

#print axioms orthogonal_probeSpan_eq_bot
#print axioms probeIndex_law
#print axioms riemannHypothesis_iff_probeIndex_eq_zero
#print axioms probeIndex_even_step
#print axioms lindelof_of_probeIndex_bounded
#print axioms integerProbeIndex_law

end GaloisForLFunctions.ExclusionOfTheCriticalState
