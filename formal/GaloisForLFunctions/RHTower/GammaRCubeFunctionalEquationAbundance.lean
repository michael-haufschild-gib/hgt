import GaloisForLFunctions.RHTower.GammaRCubeChartNodes
import GaloisForLFunctions.HTGeometry.HalfLineSamplingRelations

/-!
# Infinitely many Dirichlet series with the functional equation of `ζ(s)³`

`gammaRCube_functional_equation_abundance`: there are infinitely many linearly independent
coefficient sequences `e_r` of polynomial growth such that `Λ_r(s) = Γ_ℝ(s)³ Σ_n e_r(n)(n+1)^{-s}`
extends to an entire function with `Λ_r(1-s) = Λ_r(s)`. So the functional equation of `ζ(s)³`
(degree 3, conductor 1), unlike those of `ζ(s)` (Hamburger) and degree-2 level-1 data, does not
determine the Dirichlet series up to a finite-dimensional choice.

Proof in the cube-root chart `x = X³/(3√3)`:
1. on the antisymmetric chart space, `‖F'‖ ≤ K‖XF‖`, so a supercritical node sequence
   (equally spaced points near `0`, then every other integer node `X_{N₀+2k}`) is a sampling set;
2. hence each value `F(X_d)` at a skipped integer node `X_{N₀+2k+1}` is a fixed `ℓ²`-type
   combination of node values (Hahn–Banach and Riesz in `ℓ²`);
3. `m+1` such relations combine to one that avoids the `m` non-integer nodes;
4. applied to the charts of `K₂(yx) - y⁻¹K₂(x/y)`, the relation is the theta relation
   `θ(1/y) = yθ(y)` for `θ(y) = Σ e_n K₂((n+1)y)`, and Hecke's argument gives the completion;
5. disjoint blocks of skipped nodes give linear independence.
-/

open Complex MeasureTheory Filter Set Topology

noncomputable section

namespace RHTower.DegreeThreeHankel

/-- Parameters: a multiplier bound `K`, a gap parameter `a`, and a node sequence with the
supercritical gap condition and positive frame constant (with `ε = 1`). -/
theorem exists_chart_sampling_parameters (N : ℕ) :
    ∃ K a : ℝ, ∃ N₀ m : ℕ, 1 ≤ N₀ ∧ N ≤ N₀ ∧ 0 < a ∧
      (∀ t : ℝ, ‖((-1 / 2 : ℂ) + t * I) * chartMultiplier ((-1 / 2 : ℂ) + t * I)‖ ≤ K) ∧
      (∀ j, max |nodeSeq N₀ m j| |nodeSeq N₀ m (j + 1)| *
        (nodeSeq N₀ m (j + 1) - nodeSeq N₀ m j) ≤ a / 2) ∧
      0 < 1 - ((1 + 1) ^ 2 * (a / (2 * Real.pi)) ^ 2 + 2 * nodeSeq N₀ m 0 ^ 4) * K ^ 2 := by
  obtain ⟨K, hK⟩ := exists_bound_mul_chartMultiplier_neg_half
  have hK0 : 0 ≤ K := le_trans (norm_nonneg _) (hK 0)
  set K₁ := K + 1 with hK₁
  have hK₁0 : 0 < K₁ := by linarith
  set a := Real.pi / (2 * K₁) with ha
  have ha0 : 0 < a := by positivity
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.mp
    (tendsto_nodeX.eventually_ge_atTop (8 * Real.sqrt 3 / a))
  set N₀ := max n₀ N + 1 with hN₀
  set L := nodeX N₀ with hL
  have hL0 : 0 < L := nodeX_pos (by omega)
  set m := ⌈2 * L ^ 2 / a + 2 * K₁ * L⌉₊ with hm
  have hmc : 2 * L ^ 2 / a + 2 * K₁ * L ≤ (m : ℝ) + 1 := by
    have := Nat.le_ceil (2 * L ^ 2 / a + 2 * K₁ * L); linarith
  have hm1 : 2 * L ^ 2 / a ≤ (m : ℝ) + 1 := by
    have : 0 ≤ 2 * K₁ * L := by positivity
    linarith
  have hm2 : 2 * K₁ * L ≤ (m : ℝ) + 1 := by
    have : 0 ≤ 2 * L ^ 2 / a := by positivity
    linarith
  refine ⟨K, a, N₀, m, by omega, by omega, ha0, hK,
    nodeSeq_gap (by omega) ha0 (hn₀ N₀ (by omega)) hm1, ?_⟩
  rw [nodeSeq_zero]
  have hm0 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  set p₀ := L / ((m : ℝ) + 1) with hp₀
  have hp₀0 : 0 ≤ p₀ := by positivity
  have hp₀le : p₀ * (2 * K₁) ≤ 1 := by
    rw [hp₀, div_mul_eq_mul_div, div_le_one hm0]; linarith
  have haq : a / (2 * Real.pi) = 1 / (4 * K₁) := by
    rw [ha]; field_simp; ring
  rw [haq]
  have hKK : K ^ 2 ≤ K₁ ^ 2 := pow_le_pow_left₀ hK0 (by linarith) 2
  have h1 : (1 + 1) ^ 2 * (1 / (4 * K₁)) ^ 2 * K ^ 2 ≤ 1 / 4 := by
    rw [div_pow, one_pow, mul_pow]
    have : (1 + 1 : ℝ) ^ 2 * (1 / (4 ^ 2 * K₁ ^ 2)) * K ^ 2 = K ^ 2 / (4 * K₁ ^ 2) := by
      field_simp; ring
    rw [this, div_le_iff₀ (by positivity)]
    linarith
  have hq : (p₀ * (2 * K₁)) ^ 4 ≤ 1 := pow_le_one₀ (by positivity) hp₀le
  have h2 : 2 * p₀ ^ 4 * K ^ 2 ≤ 1 / 8 := by
    have e : (p₀ * (2 * K₁)) ^ 4 = 16 * p₀ ^ 4 * K₁ ^ 4 := by ring
    rw [e] at hq
    have hK₁1 : 1 ≤ K₁ := by linarith
    have hK₁4 : K₁ ^ 2 ≤ K₁ ^ 4 := pow_le_pow_right₀ hK₁1 (by norm_num)
    have hp4 : 0 ≤ p₀ ^ 4 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hKK hp4, mul_le_mul_of_nonneg_left hK₁4 hp4]
  nlinarith

/-- Rapidly decaying functions are square summable along the node sequence with weights
`max(p_j, p_{j+1})`. -/
theorem summable_nodeSeq_of_rapidDecay {F : ℝ → ℂ} (hF : RapidDecay F) {N₀ : ℕ} (hN₀ : 1 ≤ N₀)
    (m : ℕ) : Summable fun j => max |nodeSeq N₀ m j| |nodeSeq N₀ m (j + 1)| *
      (‖F (nodeSeq N₀ m j)‖ ^ 2 + ‖F (nodeSeq N₀ m (j + 1))‖ ^ 2) := by
  obtain ⟨C, hC⟩ := hF 6
  rw [← summable_nat_add_iff m]
  have hbase : Summable fun k : ℕ => 4 * C ^ 2 * (((k : ℝ) + 1) ^ 2)⁻¹ := by
    have h := (Real.summable_nat_pow_inv (p := 2)).mpr (by norm_num)
    have h' := (summable_nat_add_iff 1).mpr h
    exact (h'.mul_left (4 * C ^ 2)).congr (fun k => by push_cast; ring)
  refine hbase.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
  rw [show k + m + 1 = (k + 1) + m by ring, nodeSeq_add, nodeSeq_add,
    show N₀ + 2 * (k + 1) = N₀ + 2 * k + 2 by ring]
  set v := nodeX (N₀ + 2 * k)
  set u := nodeX (N₀ + 2 * k + 2)
  have hn : 1 ≤ N₀ + 2 * k := by omega
  have hv1 : 1 ≤ v := one_le_nodeX hn
  have hv0 : 0 < v := by linarith
  obtain ⟨hu2, -⟩ := nodeX_two_step hn
  have hvu : v ≤ u := (nodeX_strictMono (by omega : N₀ + 2 * k < N₀ + 2 * k + 2)).le
  have hu0 : 0 < u := by linarith
  rw [abs_of_pos hv0, abs_of_pos hu0, max_eq_right hvu]
  have hdec : ∀ X : ℝ, 1 ≤ X → ‖F X‖ ^ 2 ≤ C ^ 2 * ((X ^ 6) ^ 2)⁻¹ := by
    intro X hX
    have hX0 : 0 < X := by linarith
    have h := hC X hX
    rw [Real.rpow_neg hX0.le, Real.rpow_natCast] at h
    have h0 : 0 ≤ C * (X ^ 6)⁻¹ := le_trans (norm_nonneg _) h
    calc ‖F X‖ ^ 2 ≤ (C * (X ^ 6)⁻¹) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
      _ = C ^ 2 * ((X ^ 6) ^ 2)⁻¹ := by rw [mul_pow, inv_pow]
  have h1 := hdec v hv1
  have h2 := hdec u (le_trans hv1 hvu)
  have hu6 : ((u ^ 6) ^ 2)⁻¹ ≤ ((v ^ 6) ^ 2)⁻¹ :=
    inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) (pow_le_pow_left₀ hv0.le hvu 6) 2)
  have hv3 : (k : ℝ) + 1 ≤ v ^ 3 := by
    rw [nodeX_cube]; push_cast
    have hs : (1 : ℝ) ≤ 3 * Real.sqrt 3 := by
      have : (1 : ℝ) ≤ Real.sqrt 3 := by
        rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by norm_num)
      linarith
    have : (k : ℝ) + 1 ≤ (N₀ : ℝ) + 2 * k := by
      have : (1 : ℝ) ≤ N₀ := by exact_mod_cast hN₀
      linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    nlinarith [(Nat.cast_nonneg N₀ : (0 : ℝ) ≤ N₀), (Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  -- `2u ≤ 4v` and `v · v^{-12} ≤ v^{-6} ≤ (k+1)^{-2}`
  have hkey : u * ((v ^ 6) ^ 2)⁻¹ ≤ 2 * (((k : ℝ) + 1) ^ 2)⁻¹ := by
    have hv6 : ((v ^ 6) ^ 2)⁻¹ * v ≤ ((v ^ 3) ^ 2)⁻¹ := by
      rw [inv_mul_le_iff₀ (by positivity)]
      have : (v ^ 6) ^ 2 * ((v ^ 3) ^ 2)⁻¹ = v ^ 6 := by field_simp
      rw [this]
      calc v = v ^ 1 := (pow_one v).symm
        _ ≤ v ^ 6 := pow_le_pow_right₀ hv1 (by norm_num)
    have hk : ((v ^ 3) ^ 2)⁻¹ ≤ (((k : ℝ) + 1) ^ 2)⁻¹ :=
      inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) hv3 2)
    have hpos : 0 ≤ ((v ^ 6) ^ 2)⁻¹ := by positivity
    calc u * ((v ^ 6) ^ 2)⁻¹ ≤ 2 * v * ((v ^ 6) ^ 2)⁻¹ := mul_le_mul_of_nonneg_right hu2 hpos
      _ = 2 * (((v ^ 6) ^ 2)⁻¹ * v) := by ring
      _ ≤ 2 * (((k : ℝ) + 1) ^ 2)⁻¹ := by linarith
  have hC2 : 0 ≤ C ^ 2 := sq_nonneg C
  calc u * (‖F v‖ ^ 2 + ‖F u‖ ^ 2) ≤ u * (C ^ 2 * ((v ^ 6) ^ 2)⁻¹ + C ^ 2 * ((v ^ 6) ^ 2)⁻¹) := by
        refine mul_le_mul_of_nonneg_left ?_ hu0.le
        have : C ^ 2 * ((u ^ 6) ^ 2)⁻¹ ≤ C ^ 2 * ((v ^ 6) ^ 2)⁻¹ := mul_le_mul_of_nonneg_left hu6 hC2
        linarith
    _ = 2 * C ^ 2 * (u * ((v ^ 6) ^ 2)⁻¹) := by ring
    _ ≤ 2 * C ^ 2 * (2 * (((k : ℝ) + 1) ^ 2)⁻¹) := mul_le_mul_of_nonneg_left hkey (by positivity)
    _ = 4 * C ^ 2 * (((k : ℝ) + 1) ^ 2)⁻¹ := by ring

/-- Among `m+1` coefficient sequences, a nontrivial combination kills the first `m` entries. -/
theorem exists_eliminating_combination {m : ℕ} (γ : Fin (m + 1) → ℕ → ℂ) :
    ∃ t : Fin (m + 1) → ℂ, (∃ i, t i ≠ 0) ∧ ∀ j < m, ∑ i, t i * γ i j = 0 := by
  have hnot : ¬ LinearIndependent ℂ (fun i : Fin (m + 1) => fun j : Fin m => γ i j) := by
    intro h
    have := h.fintype_card_le_finrank
    simp at this
  rw [Fintype.not_linearIndependent_iff] at hnot
  obtain ⟨g, hg, i, hi⟩ := hnot
  refine ⟨g, ⟨i, hi⟩, fun j hj => ?_⟩
  have := congrFun hg ⟨j, hj⟩
  simpa [Finset.sum_apply] using this

/-- **Block relation.** For `m+1` chart points `X_{d_i}` (`d_i ≥ 1`) there is a nontrivial
combination `Σ t_i F(X_{d_i})` that equals a combination of the values at the integer nodes
`X_{N₀+2k}` alone, for every `F` in the antisymmetric chart space; the coefficients `Γ` grow at
most linearly in the node position. -/
theorem exists_block_relation {K a : ℝ} {N₀ m : ℕ} (hN₀ : 1 ≤ N₀)
    (hK : ∀ t : ℝ, ‖((-1 / 2 : ℂ) + t * I) * chartMultiplier ((-1 / 2 : ℂ) + t * I)‖ ≤ K)
    (hgap : ∀ j, max |nodeSeq N₀ m j| |nodeSeq N₀ m (j + 1)| *
      (nodeSeq N₀ m (j + 1) - nodeSeq N₀ m j) ≤ a / 2)
    (hbr : 0 < 1 - ((1 + 1) ^ 2 * (a / (2 * Real.pi)) ^ 2 + 2 * nodeSeq N₀ m 0 ^ 4) * K ^ 2)
    (d : Fin (m + 1) → ℕ) (hd : ∀ i, 1 ≤ d i) :
    ∃ t : Fin (m + 1) → ℂ, ∃ Γ : ℕ → ℂ, ∃ A : ℝ, (∃ i, t i ≠ 0) ∧
      (∀ j, ‖Γ j‖ ≤ A * (nodeSeq N₀ m (j + 1) + 1)) ∧
      ∀ F ∈ antiChartSpace, Summable (fun k => Γ (k + m) * F (nodeX (N₀ + 2 * k))) ∧
        ∑ i, t i * F (nodeX (d i)) = ∑' k, Γ (k + m) * F (nodeX (N₀ + 2 * k)) := by
  set p := nodeSeq N₀ m with hpdef
  have hE : ∀ F ∈ antiChartSpace, ∃ F' : ℝ → ℂ, (∀ x, 0 < x → HasDerivAt F (F' x) x) ∧
      ContinuousOn F' (Ioi 0) ∧ IntegrableOn (fun x => x ^ 2 * ‖F x‖ ^ 2) (Ioi 0) ∧
      IntegrableOn (fun x => ‖F' x‖ ^ 2) (Ioi 0) ∧
      ∫ x in Ioi 0, ‖F' x‖ ^ 2 ≤ K ^ 2 * ∫ x in Ioi 0, x ^ 2 * ‖F x‖ ^ 2 :=
    fun F hF => hF.1.analytic hK
  have hsum : ∀ F ∈ antiChartSpace, Summable fun j => max |p j| |p (j + 1)| *
      (‖F (p j)‖ ^ 2 + ‖F (p (j + 1))‖ ^ 2) :=
    fun F hF => summable_nodeSeq_of_rapidDecay hF.2 hN₀ m
  have hrel : ∀ i : Fin (m + 1), ∃ γ : ℕ → ℂ, ∃ M : ℝ, (∀ j, ‖γ j‖ ^ 2 ≤ M * (p (j + 1) + 1)) ∧
      ∀ F ∈ antiChartSpace, Summable (fun j => γ j * F (p j)) ∧
        F (nodeX (d i)) = ∑' j, γ j * F (p j) :=
    fun i => GaloisForLFunctions.HTGeometry.exists_sampling_relation antiChartSpace hE
      (nodeSeq_strictMono hN₀ m) (nodeSeq_pos hN₀ m 0) (tendsto_nodeSeq N₀ m) one_pos hgap hbr
      hsum (nodeX_pos (hd i))
  choose γ M hγ hγrel using hrel
  obtain ⟨t, ht, hkill⟩ := exists_eliminating_combination γ
  set Γ : ℕ → ℂ := fun j => ∑ i, t i * γ i j with hΓ
  refine ⟨t, Γ, ∑ i, ‖t i‖ * (|M i| + 2), ht, fun j => ?_, fun F hF => ?_⟩
  · have hp1 : 0 ≤ p (j + 1) := (nodeSeq_pos hN₀ m _).le
    calc ‖Γ j‖ ≤ ∑ i, ‖t i * γ i j‖ := norm_sum_le _ _
      _ = ∑ i, ‖t i‖ * ‖γ i j‖ := by simp_rw [norm_mul]
      _ ≤ ∑ i, ‖t i‖ * ((|M i| + 2) * (p (j + 1) + 1)) := by
          refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          have h1 := hγ i j
          have h2 : ‖γ i j‖ ≤ ‖γ i j‖ ^ 2 + 1 := by nlinarith [sq_nonneg (‖γ i j‖ - 1)]
          have h3 : M i * (p (j + 1) + 1) ≤ |M i| * (p (j + 1) + 1) :=
            mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith)
          nlinarith [abs_nonneg (M i)]
      _ = (∑ i, ‖t i‖ * (|M i| + 2)) * (p (j + 1) + 1) := by
          rw [Finset.sum_mul]; congr 1; funext i; ring
  · have hsumi : ∀ i, Summable fun j => t i * (γ i j * F (p j)) :=
      fun i => ((hγrel i F hF).1).mul_left (t i)
    have hsumΓ : Summable fun j => Γ j * F (p j) := by
      have := summable_sum (s := Finset.univ) (fun i _ => hsumi i)
      refine this.congr fun j => ?_
      simp only [hΓ, Finset.sum_mul]; congr 1; funext i; ring
    have hmain : ∑ i, t i * F (nodeX (d i)) = ∑' j, Γ j * F (p j) := by
      calc ∑ i, t i * F (nodeX (d i)) = ∑ i, ∑' j, t i * (γ i j * F (p j)) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [(hγrel i F hF).2, ((hγrel i F hF).1).tsum_mul_left]
        _ = ∑' j, ∑ i, t i * (γ i j * F (p j)) :=
            (Summable.tsum_finsetSum (fun i _ => hsumi i)).symm
        _ = ∑' j, Γ j * F (p j) := by
            congr 1; funext j; simp only [hΓ, Finset.sum_mul]; congr 1; funext i; ring
    have hzero : ∑ j ∈ Finset.range m, Γ j * F (p j) = 0 := by
      refine Finset.sum_eq_zero fun j hj => ?_
      rw [Finset.mem_range] at hj
      simp only [hΓ, hkill j hj, zero_mul]
    have hsplit := hsumΓ.sum_add_tsum_nat_add m
    rw [hzero, zero_add] at hsplit
    have hshift : (fun k => Γ (k + m) * F (p (k + m)))
        = fun k => Γ (k + m) * F (nodeX (N₀ + 2 * k)) := by
      funext k; rw [hpdef, nodeSeq_add]
    refine ⟨?_, ?_⟩
    · rw [← hshift]; exact (summable_nat_add_iff m).mpr hsumΓ
    · rw [hmain, ← hsplit, hshift]

/-- The integer coefficients of a block relation: `t_i X_n` at `n = d_i`, minus `Γ_{k+m} X_n` at
the node integers `n = N₀ + 2k`. -/
def blockCoeff (N₀ m : ℕ) (d : Fin (m + 1) → ℕ) (t : Fin (m + 1) → ℂ) (Γ : ℕ → ℂ) (n : ℕ) : ℂ :=
  (∑ i, if n = d i then t i * (nodeX n : ℂ) else 0) -
    (if N₀ ≤ n ∧ (n - N₀) % 2 = 0 then Γ ((n - N₀) / 2 + m) * (nodeX n : ℂ) else 0)

theorem nodeX_le_two_mul (n : ℕ) : nodeX n ≤ 2 * ((n : ℝ) + 1) := by
  unfold nodeX
  have hs : Real.sqrt 3 ≤ 2 := by
    rw [show (2 : ℝ) = Real.sqrt 4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hr : (n : ℝ) ^ (1 / 3 : ℝ) ≤ (n : ℝ) + 1 := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp
    · have h1 : (1 : ℝ) ≤ n := by exact_mod_cast h
      calc (n : ℝ) ^ (1 / 3 : ℝ) ≤ (n : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le h1 (by norm_num)
        _ = n := Real.rpow_one _
        _ ≤ n + 1 := by linarith
  have h0 : 0 ≤ (n : ℝ) ^ (1 / 3 : ℝ) := by positivity
  nlinarith [Real.sqrt_nonneg 3]

/-- Growth of the block coefficients: `|a_n| ≤ C (n+1)²`. -/
theorem norm_blockCoeff_le {N₀ m : ℕ} (hN₀ : 1 ≤ N₀) (d : Fin (m + 1) → ℕ) (t : Fin (m + 1) → ℂ)
    {Γ : ℕ → ℂ} {A : ℝ} (hΓ : ∀ j, ‖Γ j‖ ≤ A * (nodeSeq N₀ m (j + 1) + 1)) (n : ℕ) :
    ‖blockCoeff N₀ m d t Γ n‖ ≤ (2 * ∑ i, ‖t i‖ + 10 * |A|) * ((n : ℝ) + 1) ^ 2 := by
  have hX := nodeX_le_two_mul n
  have hX0 := nodeX_nonneg n
  have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  set T := ∑ i, ‖t i‖ with hT
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun i _ => norm_nonneg _
  have h1 : ‖∑ i, (if n = d i then t i * (nodeX n : ℂ) else 0)‖ ≤ T * nodeX n := by
    refine (norm_sum_le _ _).trans ?_
    rw [hT, Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => ?_
    split_ifs
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hX0]
    · simp only [norm_zero]; positivity
  have h2 : ‖(if N₀ ≤ n ∧ (n - N₀) % 2 = 0 then Γ ((n - N₀) / 2 + m) * (nodeX n : ℂ) else 0)‖
      ≤ |A| * (4 * ((n : ℝ) + 1) + 1) * nodeX n := by
    split_ifs with hc
    · obtain ⟨hle, hev⟩ := hc
      obtain ⟨k, hk⟩ : ∃ k, n = N₀ + 2 * k := ⟨(n - N₀) / 2, by omega⟩
      subst hk
      have hkk : (N₀ + 2 * k - N₀) / 2 = k := by omega
      rw [hkk, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hX0]
      have hb := hΓ (k + m)
      rw [show k + m + 1 = (k + 1) + m by ring, nodeSeq_add,
        show N₀ + 2 * (k + 1) = N₀ + 2 * k + 2 by ring] at hb
      obtain ⟨hu2, -⟩ := nodeX_two_step (by omega : 1 ≤ N₀ + 2 * k)
      have hu0 : 0 ≤ nodeX (N₀ + 2 * k + 2) := nodeX_nonneg _
      have hΓb : ‖Γ (k + m)‖ ≤ |A| * (4 * (((N₀ + 2 * k : ℕ) : ℝ) + 1) + 1) := by
        refine hb.trans ?_
        calc A * (nodeX (N₀ + 2 * k + 2) + 1) ≤ |A| * (nodeX (N₀ + 2 * k + 2) + 1) :=
              mul_le_mul_of_nonneg_right (le_abs_self A) (by linarith)
          _ ≤ |A| * (4 * (((N₀ + 2 * k : ℕ) : ℝ) + 1) + 1) :=
              mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg A)
      exact mul_le_mul_of_nonneg_right hΓb hX0
    · simp only [norm_zero]; have := abs_nonneg A; positivity
  unfold blockCoeff
  refine (norm_sub_le _ _).trans ?_
  have hA0 := abs_nonneg A
  have e1 : T * nodeX n ≤ 2 * T * ((n : ℝ) + 1) ^ 2 := by
    have : nodeX n ≤ 2 * ((n : ℝ) + 1) ^ 2 := by nlinarith
    exact (mul_le_mul_of_nonneg_left this hT0).trans (le_of_eq (by ring))
  have e2 : |A| * (4 * ((n : ℝ) + 1) + 1) * nodeX n ≤ 10 * |A| * ((n : ℝ) + 1) ^ 2 := by
    have hq : (4 * ((n : ℝ) + 1) + 1) * nodeX n ≤ 10 * ((n : ℝ) + 1) ^ 2 := by nlinarith
    nlinarith
  nlinarith

/-- Sum against the block coefficients: `Σ a_n h(n) = Σ t_i X_{d_i} h(d_i) - Σ_k Γ_{k+m} X h`. -/
theorem tsum_blockCoeff_mul {N₀ m : ℕ} (d : Fin (m + 1) → ℕ) (t : Fin (m + 1) → ℂ) (Γ : ℕ → ℂ)
    (h : ℕ → ℂ) (hs : Summable fun k => Γ (k + m) * ((nodeX (N₀ + 2 * k) : ℂ) * h (N₀ + 2 * k))) :
    Summable (fun n => blockCoeff N₀ m d t Γ n * h n) ∧
      ∑' n, blockCoeff N₀ m d t Γ n * h n =
        ∑ i, t i * ((nodeX (d i) : ℂ) * h (d i)) -
          ∑' k, Γ (k + m) * ((nodeX (N₀ + 2 * k) : ℂ) * h (N₀ + 2 * k)) := by
  set Aterm : Fin (m + 1) → ℕ → ℂ := fun i n =>
    if n = d i then t i * ((nodeX (d i) : ℂ) * h (d i)) else 0 with hA
  set B : ℕ → ℂ := fun n =>
    if N₀ ≤ n ∧ (n - N₀) % 2 = 0 then Γ ((n - N₀) / 2 + m) * ((nodeX n : ℂ) * h n) else 0 with hB
  have hsplit : (fun n => blockCoeff N₀ m d t Γ n * h n) = fun n => (∑ i, Aterm i n) - B n := by
    funext n
    simp only [blockCoeff, hA, hB, sub_mul, Finset.sum_mul]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs with hn
      · subst hn; ring
      · simp
    · split_ifs <;> ring
  have hAsum : ∀ i, Summable (Aterm i) := fun i => by
    simp only [hA]; exact (hasSum_ite_eq (d i) _).summable
  have hAtsum : ∀ i, ∑' n, Aterm i n = t i * ((nodeX (d i) : ℂ) * h (d i)) := fun i => by
    simp only [hA]; exact tsum_ite_eq (d i) _
  set g : ℕ → ℕ := fun k => N₀ + 2 * k with hg
  have hginj : Function.Injective g := fun a b hab => by simp only [hg] at hab; omega
  have hBg : B ∘ g = fun k => Γ (k + m) * ((nodeX (N₀ + 2 * k) : ℂ) * h (N₀ + 2 * k)) := by
    funext k
    simp only [Function.comp, hB, hg]
    rw [if_pos ⟨by omega, by omega⟩, show (N₀ + 2 * k - N₀) / 2 = k by omega]
  have hBout : ∀ n ∉ Set.range g, B n = 0 := by
    intro n hn
    simp only [hB]
    rw [if_neg]
    rintro ⟨hle, hev⟩
    exact hn ⟨(n - N₀) / 2, by simp only [hg]; omega⟩
  have hBsum : Summable B := (hginj.summable_iff hBout).mp (by rw [hBg]; exact hs)
  have hBtsum : ∑' n, B n = ∑' k, Γ (k + m) * ((nodeX (N₀ + 2 * k) : ℂ) * h (N₀ + 2 * k)) := by
    rw [← hBg]
    exact (hginj.tsum_eq (Function.support_subset_iff'.mpr hBout)).symm
  have hAall : Summable fun n => ∑ i, Aterm i n := summable_sum fun i _ => hAsum i
  rw [hsplit]
  refine ⟨hAall.sub hBsum, ?_⟩
  rw [hAall.tsum_sub hBsum, Summable.tsum_finsetSum (fun i _ => hAsum i), hBtsum]
  simp_rw [hAtsum]

theorem chartFun_nodeX (f : ℝ → ℂ) (n : ℕ) :
    chartFun f (nodeX n) = (3 : ℂ) ^ (-(1 / 4 : ℂ)) * ((nodeX n : ℂ) * f n) := by
  unfold chartFun; rw [chartPoint_nodeX]; ring

/-- Theta series with coefficients `O((n+1)²)` converge. -/
theorem summable_mul_gammaRPowKernel_two {e : ℕ → ℂ} {C : ℝ}
    (he : ∀ n, ‖e n‖ ≤ C * ((n : ℝ) + 1) ^ 2) {y : ℝ} (hy : 0 < y) :
    Summable fun n => e n * gammaRPowKernel 2 (((n : ℝ) + 1) * y) := by
  obtain ⟨C', hC'⟩ := exists_norm_gammaRPowKernel_le 2 (c := 4) (by norm_num)
  have hC0 : 0 ≤ C := by have := (norm_nonneg _).trans (he 0); simpa using this
  have hbase : Summable fun n : ℕ => C * C' * (y ^ 4)⁻¹ * (((n : ℝ) + 1) ^ 2)⁻¹ := by
    have h := (Real.summable_nat_pow_inv (p := 2)).mpr (by norm_num)
    have h' := (summable_nat_add_iff 1).mpr h
    exact (h'.mul_left (C * C' * (y ^ 4)⁻¹)).congr (fun n => by push_cast; ring)
  refine Summable.of_norm_bounded hbase (fun n => ?_)
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hx : 0 < ((n : ℝ) + 1) * y := mul_pos hn hy
  have h1 := hC' _ hx
  rw [Real.rpow_neg hx.le, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at h1
  rw [norm_mul]
  calc ‖e n‖ * ‖gammaRPowKernel 2 (((n : ℝ) + 1) * y)‖
      ≤ (C * ((n : ℝ) + 1) ^ 2) * (C' * ((((n : ℝ) + 1) * y) ^ 4)⁻¹) :=
        mul_le_mul (he n) h1 (norm_nonneg _) (by positivity)
    _ = C * C' * (y ^ 4)⁻¹ * (((n : ℝ) + 1) ^ 2)⁻¹ := by
        field_simp

/-- The block coefficients annihilate every theta test function: `Σ_n a_n f_y(n) = 0`. -/
theorem blockCoeff_theta_relation {N₀ m : ℕ} (d : Fin (m + 1) → ℕ) (t : Fin (m + 1) → ℂ)
    (Γ : ℕ → ℂ) (hrel : ∀ F ∈ antiChartSpace, Summable (fun k => Γ (k + m) * F (nodeX (N₀ + 2 * k))) ∧
        ∑ i, t i * F (nodeX (d i)) = ∑' k, Γ (k + m) * F (nodeX (N₀ + 2 * k)))
    {y : ℝ} (hy : 0 < y) :
    Summable (fun n => blockCoeff N₀ m d t Γ n * thetaTestFunction y n) ∧
      ∑' n, blockCoeff N₀ m d t Γ n * thetaTestFunction y n = 0 := by
  set c₃ : ℂ := (3 : ℂ) ^ (-(1 / 4 : ℂ)) with hc₃
  have hc₃0 : c₃ ≠ 0 := by
    rw [hc₃]; exact (Complex.cpow_ne_zero_iff_of_exponent_ne_zero (by norm_num)).mpr (by norm_num)
  obtain ⟨hs, heq⟩ := hrel _ (chartFun_thetaTestFunction_mem hy)
  simp_rw [chartFun_nodeX] at hs heq
  set h : ℕ → ℂ := fun n => thetaTestFunction y n with hh
  have hs' : Summable fun k => Γ (k + m) * ((nodeX (N₀ + 2 * k) : ℂ) * h (N₀ + 2 * k)) := by
    have := hs.mul_left c₃⁻¹
    refine this.congr fun k => ?_
    simp only [hh]; rw [← hc₃]; field_simp
  obtain ⟨hsum, htsum⟩ := tsum_blockCoeff_mul (N₀ := N₀) d t Γ h hs'
  refine ⟨hsum, ?_⟩
  rw [htsum, sub_eq_zero]
  have e1 : ∑ i, t i * (c₃ * ((nodeX (d i) : ℂ) * thetaTestFunction y (d i)))
      = c₃ * ∑ i, t i * ((nodeX (d i) : ℂ) * h (d i)) := by
    rw [Finset.mul_sum]; congr 1; funext i; simp only [hh]; ring
  have e2 : ∑' k, Γ (k + m) * (c₃ * ((nodeX (N₀ + 2 * k) : ℂ) * thetaTestFunction y ↑(N₀ + 2 * k)))
      = c₃ * ∑' k, Γ (k + m) * ((nodeX (N₀ + 2 * k) : ℂ) * h (N₀ + 2 * k)) := by
    rw [← hs'.tsum_mul_left]; congr 1; funext k; simp only [hh]; ring
  rw [e1, e2] at heq
  exact mul_left_cancel₀ hc₃0 heq

theorem block_index_inj {m r r' : ℕ} {i i' : Fin (m + 1)}
    (h : (m + 1) * r + i = (m + 1) * r' + i') : r = r' ∧ i = i' := by
  have hm : 0 < m + 1 := Nat.succ_pos m
  have h1 := congrArg (· / (m + 1)) h
  have h2 := congrArg (· % (m + 1)) h
  simp only [Nat.mul_add_div hm, Nat.div_eq_of_lt i.isLt, Nat.div_eq_of_lt i'.isLt,
    Nat.mul_add_mod, Nat.mod_eq_of_lt i.isLt, Nat.mod_eq_of_lt i'.isLt] at h1 h2
  exact ⟨by simpa using h1, Fin.ext h2⟩

theorem skipped_index_inj {N₀ m r r' : ℕ} {i i' : Fin (m + 1)}
    (h : N₀ + 2 * ((m + 1) * r + i) + 1 = N₀ + 2 * ((m + 1) * r' + i') + 1) : r = r' ∧ i = i' := by
  apply block_index_inj
  have h1 := Nat.add_right_cancel h
  have h2 := Nat.add_left_cancel h1
  exact Nat.eq_of_mul_eq_mul_left (by norm_num) h2

/-- **Infinitely many theta relations for `Γ_ℝ(s)³`.** There are linearly independent coefficient
sequences `e_r`, `r ∈ ℕ`, each of growth `O((n+1)²)`, with
`Σ_n e_r(n) K₂((n+1)/y) = y Σ_n e_r(n) K₂((n+1)y)` for all `y > 0`, where `K₂` is the inverse
Mellin transform of `Γ_ℝ(s)³`.

Each `e_r` comes from `m+1` skipped integer nodes `X_d` in the cube-root chart: every point value
`F(X_d)` on the antisymmetric chart space is a fixed combination of node values (sampling lower
bound and Hahn–Banach/Riesz), a nontrivial combination of the `m+1` relations removes the
non-integer nodes, and applying the result to the charts of `K₂(yx) - y⁻¹K₂(x/y)` gives the theta
relation. Distinct blocks of skipped nodes give independence. -/
theorem gammaRCube_theta_relations_vanishing_below (N : ℕ) :
    ∃ e : ℕ → ℕ → ℂ, LinearIndependent ℂ e ∧ ∀ r, (∀ n, n + 1 < N → e r n = 0) ∧ ∃ C : ℝ,
      (∀ n, ‖e r n‖ ≤ C * ((n : ℝ) + 1) ^ 2) ∧
      ∀ y : ℝ, 0 < y → (∑' n, e r n * gammaRPowKernel 2 (((n : ℝ) + 1) * (1 / y)))
        = (y : ℂ) * ∑' n, e r n * gammaRPowKernel 2 (((n : ℝ) + 1) * y) := by
  obtain ⟨K, a, N₀, m, hN₀, hNN₀, -, hK, hgap, hbr⟩ := exists_chart_sampling_parameters N
  set d : ℕ → Fin (m + 1) → ℕ := fun r i => N₀ + 2 * ((m + 1) * r + i) + 1 with hd
  have hblock : ∀ r, ∃ t : Fin (m + 1) → ℂ, ∃ Γ : ℕ → ℂ, ∃ A : ℝ, (∃ i, t i ≠ 0) ∧
      (∀ j, ‖Γ j‖ ≤ A * (nodeSeq N₀ m (j + 1) + 1)) ∧
      ∀ F ∈ antiChartSpace, Summable (fun k => Γ (k + m) * F (nodeX (N₀ + 2 * k))) ∧
        ∑ i, t i * F (nodeX (d r i)) = ∑' k, Γ (k + m) * F (nodeX (N₀ + 2 * k)) :=
    fun r => exists_block_relation hN₀ hK hgap hbr (d r) (fun i => by simp only [hd]; omega)
  choose t Γ A ht hΓ hrel using hblock
  set a' : ℕ → ℕ → ℂ := fun r n => blockCoeff N₀ m (d r) (t r) (Γ r) n with ha'
  have ha0 : ∀ r, a' r 0 = 0 := by
    intro r
    simp only [ha', blockCoeff]
    rw [if_neg (by omega)]
    simp only [sub_zero]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [if_neg (by simp only [hd]; omega)]
  refine ⟨fun r n => a' r (n + 1), ?_, fun r => ?_⟩
  · -- independence
    rw [linearIndependent_iff']
    intro sfin g hg r hr
    obtain ⟨i, hi⟩ := ht r
    have hval : ∀ r', a' r' (d r i) = if r' = r then t r i * (nodeX (d r i) : ℂ) else 0 := by
      intro r'
      simp only [ha', blockCoeff]
      rw [if_neg (by simp only [hd]; omega), sub_zero]
      split_ifs with hrr
      · subst hrr
        rw [Finset.sum_eq_single i]
        · rw [if_pos rfl]
        · intro i' _ hne
          rw [if_neg]
          intro heq
          simp only [hd] at heq
          exact hne (skipped_index_inj heq).2.symm
        · simp
      · refine Finset.sum_eq_zero fun i' _ => ?_
        rw [if_neg]
        intro heq
        simp only [hd] at heq
        exact hrr (skipped_index_inj heq).1.symm
    have hn : d r i = (d r i - 1) + 1 := by simp only [hd]; omega
    have hev := congrFun hg (d r i - 1)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hev
    rw [← hn] at hev
    simp_rw [hval] at hev
    rw [Finset.sum_eq_single r (fun r' _ hne => by rw [if_neg hne, mul_zero])
      (fun h => absurd hr h), if_pos rfl] at hev
    have hX : (nodeX (d r i) : ℂ) ≠ 0 := by
      exact_mod_cast (nodeX_pos (by simp only [hd]; omega)).ne'
    rcases mul_eq_zero.mp hev with h | h
    · exact h
    · exact absurd h (mul_ne_zero hi hX)
  · -- vanishing below `N`, growth and theta symmetry
    have hlow : ∀ n, n + 1 < N → a' r (n + 1) = 0 := by
      intro n hn
      simp only [ha', blockCoeff]
      rw [if_neg (by omega), sub_zero]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [if_neg (by simp only [hd]; omega)]
    refine ⟨hlow, ?_⟩
    set C₀ := 2 * ∑ i, ‖t r i‖ + 10 * |A r| with hC₀
    have hC₀0 : 0 ≤ C₀ := by
      have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => norm_nonneg (t r i))
      have := abs_nonneg (A r); positivity
    have hgrowth : ∀ n, ‖a' r (n + 1)‖ ≤ 4 * C₀ * ((n : ℝ) + 1) ^ 2 := by
      intro n
      have h := norm_blockCoeff_le hN₀ (d r) (t r) (hΓ r) (n + 1)
      refine h.trans ?_
      push_cast
      have : ((n : ℝ) + 1 + 1) ^ 2 ≤ 4 * ((n : ℝ) + 1) ^ 2 := by
        nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      nlinarith
    refine ⟨4 * C₀, hgrowth, fun y hy => ?_⟩
    obtain ⟨hsum, hzero⟩ := blockCoeff_theta_relation (d r) (t r) (Γ r) (hrel r) hy
    have hshift := hsum.tsum_eq_zero_add
    rw [hzero] at hshift
    have h0 : a' r 0 * thetaTestFunction y ((0 : ℕ) : ℝ) = 0 := by rw [ha0 r, zero_mul]
    simp only [ha'] at h0
    rw [h0, zero_add] at hshift
    -- `Σ e_n (K₂(y(n+1)) - y⁻¹ K₂(y⁻¹(n+1))) = 0`
    have hy' : 0 < y⁻¹ := inv_pos.mpr hy
    have hs1 := summable_mul_gammaRPowKernel_two hgrowth hy
    have hs2 := summable_mul_gammaRPowKernel_two hgrowth hy'
    have hexp : (fun n : ℕ => blockCoeff N₀ m (d r) (t r) (Γ r) (n + 1) *
        thetaTestFunction y ((n + 1 : ℕ) : ℝ)) = fun n =>
        a' r (n + 1) * gammaRPowKernel 2 (((n : ℝ) + 1) * y) -
          ((y⁻¹ : ℝ) : ℂ) * (a' r (n + 1) * gammaRPowKernel 2 (((n : ℝ) + 1) * y⁻¹)) := by
      funext n
      simp only [ha', thetaTestFunction]
      push_cast
      ring_nf
    rw [hexp, hs1.tsum_sub (hs2.mul_left _), hs2.tsum_mul_left] at hshift
    have hyC : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
    have hfin := sub_eq_zero.mp hshift.symm
    rw [show (fun n : ℕ => a' r (n + 1) * gammaRPowKernel 2 (((n : ℝ) + 1) * (1 / y)))
        = fun n => a' r (n + 1) * gammaRPowKernel 2 (((n : ℝ) + 1) * y⁻¹) by
      funext n; rw [one_div]]
    rw [hfin]
    push_cast
    field_simp

theorem gammaRCube_theta_relations_infinite :
    ∃ e : ℕ → ℕ → ℂ, LinearIndependent ℂ e ∧ ∀ r, ∃ C : ℝ,
      (∀ n, ‖e r n‖ ≤ C * ((n : ℝ) + 1) ^ 2) ∧
      ∀ y : ℝ, 0 < y → (∑' n, e r n * gammaRPowKernel 2 (((n : ℝ) + 1) * (1 / y)))
        = (y : ℂ) * ∑' n, e r n * gammaRPowKernel 2 (((n : ℝ) + 1) * y) := by
  obtain ⟨e, hind, he⟩ := gammaRCube_theta_relations_vanishing_below 0
  exact ⟨e, hind, fun r => (he r).2⟩

/-- **`ζ(s)³`'s functional equation has infinitely many independent solutions.** There are
linearly independent coefficient sequences `e_r` (growth `O((n+1)²)`) such that each completed
Dirichlet series `Λ_r(s) = Γ_ℝ(s)³ Σ_n e_r(n)(n+1)^{-s}` (for `Re s > 3`) is the restriction of an
entire function with `Λ_r(1-s) = Λ_r(s)`. -/
theorem gammaRCube_functional_equation_abundance :
    ∃ e : ℕ → ℕ → ℂ, LinearIndependent ℂ e ∧ ∀ r,
      Differentiable ℂ (mellin fun y : ℝ => ∑' n : ℕ, e r n * gammaRPowKernel 2 (((n : ℝ) + 1) * y)) ∧
      (∀ s : ℂ, mellin (fun y : ℝ => ∑' n : ℕ, e r n * gammaRPowKernel 2 (((n : ℝ) + 1) * y)) (1 - s)
        = mellin (fun y : ℝ => ∑' n : ℕ, e r n * gammaRPowKernel 2 (((n : ℝ) + 1) * y)) s) ∧
      (∀ s : ℂ, 3 < s.re →
        mellin (fun y : ℝ => ∑' n : ℕ, e r n * gammaRPowKernel 2 (((n : ℝ) + 1) * y)) s
          = (∑' n : ℕ, e r n * (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s)) * Gammaℝ s ^ 3) := by
  obtain ⟨e, hind, he⟩ := gammaRCube_theta_relations_infinite
  refine ⟨e, hind, fun r => ?_⟩
  obtain ⟨C, hC, hsym⟩ := he r
  have hC' : ∀ n : ℕ, ‖e r n‖ ≤ C * ((n : ℝ) + 1) ^ (2 : ℝ) := fun n => by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; exact hC n
  obtain ⟨h1, h2, h3⟩ := gammaRPow_theta_converse 2 (by norm_num : (0 : ℝ) ≤ 2) hC' hsym
  exact ⟨h1, h2, fun s hs => h3 s (by linarith)⟩

end RHTower.DegreeThreeHankel

namespace RHTower.DegreeThreeHankel

/-- **No finite set of coefficients and the functional equation determines `ζ(s)³`.** For every
`N` there are linearly independent coefficient sequences `e_r`, vanishing at all integers `< N`,
whose completed Dirichlet series `Γ_ℝ(s)³ Σ_n e_r(n)(n+1)^{-s}` are entire and invariant under
`s ↦ 1-s`. Adding any of them to `ζ(s)³` keeps the functional equation, the poles and the first
`N - 1` Dirichlet coefficients. -/
theorem gammaRCube_functional_equation_abundance_vanishing_below (N : ℕ) :
    ∃ e : ℕ → ℕ → ℂ, LinearIndependent ℂ e ∧ ∀ r, (∀ n, n + 1 < N → e r n = 0) ∧
      Differentiable ℂ (mellin fun y : ℝ => ∑' n : ℕ, e r n * gammaRPowKernel 2 (((n : ℝ) + 1) * y)) ∧
      (∀ s : ℂ, mellin (fun y : ℝ => ∑' n : ℕ, e r n * gammaRPowKernel 2 (((n : ℝ) + 1) * y)) (1 - s)
        = mellin (fun y : ℝ => ∑' n : ℕ, e r n * gammaRPowKernel 2 (((n : ℝ) + 1) * y)) s) ∧
      (∀ s : ℂ, 3 < s.re →
        mellin (fun y : ℝ => ∑' n : ℕ, e r n * gammaRPowKernel 2 (((n : ℝ) + 1) * y)) s
          = (∑' n : ℕ, e r n * (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s)) * Gammaℝ s ^ 3) := by
  obtain ⟨e, hind, he⟩ := gammaRCube_theta_relations_vanishing_below N
  refine ⟨e, hind, fun r => ?_⟩
  obtain ⟨hlow, C, hC, hsym⟩ := he r
  have hC' : ∀ n : ℕ, ‖e r n‖ ≤ C * ((n : ℝ) + 1) ^ (2 : ℝ) := fun n => by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; exact hC n
  obtain ⟨h1, h2, h3⟩ := gammaRPow_theta_converse 2 (by norm_num : (0 : ℝ) ≤ 2) hC' hsym
  exact ⟨hlow, h1, h2, fun s hs => h3 s (by linarith)⟩

end RHTower.DegreeThreeHankel
