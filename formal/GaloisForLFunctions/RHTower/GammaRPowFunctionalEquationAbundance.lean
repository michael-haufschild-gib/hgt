import GaloisForLFunctions.RHTower.GammaRPowChartNodes
import GaloisForLFunctions.HTGeometry.HalfLineSamplingRelations

/-!
# The functional equation of `ζ(s)^d` has infinitely many solutions for every `d ≥ 3`

`gammaRPow_functional_equation_abundance`: for `d = k+1 ≥ 3` and every `N` there are infinitely
many linearly independent coefficient sequences `e_r` of polynomial growth, vanishing below `N`,
such that `Γ_ℝ(s)^d Σ_n e_r(n)(n+1)^{-s}` extends to an entire function invariant under `s ↦ 1-s`.

Contrast: in degree 1 the functional equation determines `ζ` (Hamburger), and in degree 2 at level 1
it determines `ζ²`. From degree 3 on, neither the functional equation nor any finite set of
coefficients pins down `ζ(s)^d`.

Proof in the chart `x = X^d`:
* the antisymmetric chart space has `‖F'‖ ≤ K‖XF‖`;
* the integer nodes `n^{1/d}` are supercritical;
* sampling relations at skipped nodes, with blocks of `m+1` of them, remove the non-integer
  nodes near `0`;
* the relations applied to the theta test functions are the theta relations, and Hecke's
  argument gives the completions.
-/

open Complex MeasureTheory Filter Set Topology

noncomputable section

namespace RHTower.GammaRPowTwins

/-- Parameters for degree `d ≥ 3`: a multiplier bound `K`, a gap parameter `a`, and a node
sequence starting at `N₀ ≥ N` with the gap condition and positive frame constant (`ε = 1`). -/
theorem exists_chart_sampling_parameters {d : ℕ} (hd : 3 ≤ d) (N : ℕ) :
    ∃ K a : ℝ, ∃ N₀ m : ℕ, 1 ≤ N₀ ∧ N ≤ N₀ ∧ 0 < a ∧
      (∀ t : ℝ, ‖((-1 / 2 : ℂ) + t * I) * chartMultiplier d ((-1 / 2 : ℂ) + t * I)‖ ≤ K) ∧
      (∀ j, max |nodeSeq d N₀ m j| |nodeSeq d N₀ m (j + 1)| *
        (nodeSeq d N₀ m (j + 1) - nodeSeq d N₀ m j) ≤ a / 2) ∧
      0 < 1 - ((1 + 1) ^ 2 * (a / (2 * Real.pi)) ^ 2 + 2 * nodeSeq d N₀ m 0 ^ 4) * K ^ 2 := by
  obtain ⟨K, hK⟩ := exists_bound_mul_chartMultiplier_neg_half d hd
  have hK0 : 0 ≤ K := le_trans (norm_nonneg _) (hK 0)
  set K₁ := K + 1 with hK₁
  have hK₁0 : 0 < K₁ := by linarith
  set a := Real.pi / (2 * K₁) with ha
  have ha0 : 0 < a := by positivity
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.mp
    ((tendsto_nodeX (d := d) (by omega)).eventually_ge_atTop (8 / a))
  set N₀ := max n₀ N + 1 with hN₀
  set L := nodeX d N₀ with hL
  have hL0 : 0 < L := nodeX_pos (by omega) (by omega)
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
    nodeSeq_gap hd (by omega) ha0 (hn₀ N₀ (by omega)) hm1, ?_⟩
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
theorem summable_nodeSeq_of_rapidDecay {d : ℕ} (hd : 3 ≤ d) {F : ℝ → ℂ} (hF : RapidDecay F)
    {N₀ : ℕ} (hN₀ : 1 ≤ N₀) (m : ℕ) : Summable fun j => max |nodeSeq d N₀ m j| |nodeSeq d N₀ m (j + 1)| *
      (‖F (nodeSeq d N₀ m j)‖ ^ 2 + ‖F (nodeSeq d N₀ m (j + 1))‖ ^ 2) := by
  obtain ⟨C, hC⟩ := hF (2 * d)
  rw [← summable_nat_add_iff m]
  have hbase : Summable fun k : ℕ => 4 * C ^ 2 * (((k : ℝ) + 1) ^ 2)⁻¹ := by
    have h := (Real.summable_nat_pow_inv (p := 2)).mpr (by norm_num)
    have h' := (summable_nat_add_iff 1).mpr h
    exact (h'.mul_left (4 * C ^ 2)).congr (fun k => by push_cast; ring)
  refine hbase.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
  rw [show k + m + 1 = (k + 1) + m by ring, nodeSeq_add, nodeSeq_add,
    show N₀ + 2 * (k + 1) = N₀ + 2 * k + 2 by ring]
  set v := nodeX d (N₀ + 2 * k)
  set u := nodeX d (N₀ + 2 * k + 2)
  have hn : 1 ≤ N₀ + 2 * k := by omega
  have hv1 : 1 ≤ v := one_le_nodeX (by omega) hn
  have hv0 : 0 < v := by linarith
  obtain ⟨hu2, -⟩ := nodeX_two_step hd hn
  have hvu : v ≤ u := (nodeX_strictMono (d := d) (by omega)
    (by omega : N₀ + 2 * k < N₀ + 2 * k + 2)).le
  have hu0 : 0 < u := by linarith
  rw [abs_of_pos hv0, abs_of_pos hu0, max_eq_right hvu]
  have hdec : ∀ X : ℝ, 1 ≤ X → ‖F X‖ ^ 2 ≤ C ^ 2 * ((X ^ (2 * d)) ^ 2)⁻¹ := by
    intro X hX
    have hX0 : 0 < X := by linarith
    have h := hC X hX
    rw [Real.rpow_neg hX0.le, show ((2 * d : ℕ) : ℝ) = ((2 * d : ℕ) : ℝ) from rfl,
      Real.rpow_natCast] at h
    have h0 : 0 ≤ C * (X ^ (2 * d))⁻¹ := le_trans (norm_nonneg _) h
    calc ‖F X‖ ^ 2 ≤ (C * (X ^ (2 * d))⁻¹) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
      _ = C ^ 2 * ((X ^ (2 * d)) ^ 2)⁻¹ := by rw [mul_pow, inv_pow]
  have h1 := hdec v hv1
  have h2 := hdec u (le_trans hv1 hvu)
  have hu6 : ((u ^ (2 * d)) ^ 2)⁻¹ ≤ ((v ^ (2 * d)) ^ 2)⁻¹ :=
    inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) (pow_le_pow_left₀ hv0.le hvu _) 2)
  have hvd : (k : ℝ) + 1 ≤ v ^ d := by
    rw [nodeX_pow (by omega)]; push_cast
    have : (1 : ℝ) ≤ N₀ := by exact_mod_cast hN₀
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hkey : u * ((v ^ (2 * d)) ^ 2)⁻¹ ≤ 2 * (((k : ℝ) + 1) ^ 2)⁻¹ := by
    have hv6 : ((v ^ (2 * d)) ^ 2)⁻¹ * v ≤ ((v ^ d) ^ 2)⁻¹ := by
      rw [inv_mul_le_iff₀ (by positivity)]
      have : (v ^ (2 * d)) ^ 2 * ((v ^ d) ^ 2)⁻¹ = v ^ (2 * d) := by
        rw [← pow_mul, ← pow_mul]; field_simp; ring_nf
      rw [this]
      calc v = v ^ 1 := (pow_one v).symm
        _ ≤ v ^ (2 * d) := pow_le_pow_right₀ hv1 (by omega)
    have hk : ((v ^ d) ^ 2)⁻¹ ≤ (((k : ℝ) + 1) ^ 2)⁻¹ :=
      inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) hvd 2)
    have hpos : 0 ≤ ((v ^ (2 * d)) ^ 2)⁻¹ := by positivity
    calc u * ((v ^ (2 * d)) ^ 2)⁻¹ ≤ 2 * v * ((v ^ (2 * d)) ^ 2)⁻¹ := mul_le_mul_of_nonneg_right hu2 hpos
      _ = 2 * (((v ^ (2 * d)) ^ 2)⁻¹ * v) := by ring
      _ ≤ 2 * (((k : ℝ) + 1) ^ 2)⁻¹ := by linarith
  have hC2 : 0 ≤ C ^ 2 := sq_nonneg C
  calc u * (‖F v‖ ^ 2 + ‖F u‖ ^ 2) ≤ u * (C ^ 2 * ((v ^ (2 * d)) ^ 2)⁻¹ + C ^ 2 * ((v ^ (2 * d)) ^ 2)⁻¹) := by
        refine mul_le_mul_of_nonneg_left ?_ hu0.le
        have : C ^ 2 * ((u ^ (2 * d)) ^ 2)⁻¹ ≤ C ^ 2 * ((v ^ (2 * d)) ^ 2)⁻¹ :=
          mul_le_mul_of_nonneg_left hu6 hC2
        linarith
    _ = 2 * C ^ 2 * (u * ((v ^ (2 * d)) ^ 2)⁻¹) := by ring
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

/-- **Block relation in degree `d ≥ 3`.** For `m+1` chart points `X_{d_i}` (`d_i ≥ 1`) a nontrivial
combination `Σ t_i F(X_{d_i})` equals a combination of the values at the integer nodes `X_{N₀+2k}`
alone, for every `F` in the antisymmetric chart space. -/
theorem exists_block_relation {d : ℕ} (hd : 3 ≤ d) {K a : ℝ} {N₀ m : ℕ} (hN₀ : 1 ≤ N₀)
    (hK : ∀ t : ℝ, ‖((-1 / 2 : ℂ) + t * I) * chartMultiplier d ((-1 / 2 : ℂ) + t * I)‖ ≤ K)
    (hgap : ∀ j, max |nodeSeq d N₀ m j| |nodeSeq d N₀ m (j + 1)| *
      (nodeSeq d N₀ m (j + 1) - nodeSeq d N₀ m j) ≤ a / 2)
    (hbr : 0 < 1 - ((1 + 1) ^ 2 * (a / (2 * Real.pi)) ^ 2 + 2 * nodeSeq d N₀ m 0 ^ 4) * K ^ 2)
    (δ : Fin (m + 1) → ℕ) (hδ : ∀ i, 1 ≤ δ i) :
    ∃ t : Fin (m + 1) → ℂ, ∃ Γ : ℕ → ℂ, ∃ A : ℝ, (∃ i, t i ≠ 0) ∧
      (∀ j, ‖Γ j‖ ≤ A * (nodeSeq d N₀ m (j + 1) + 1)) ∧
      ∀ F ∈ antiChartSpace d, Summable (fun k => Γ (k + m) * F (nodeX d (N₀ + 2 * k))) ∧
        ∑ i, t i * F (nodeX d (δ i)) = ∑' k, Γ (k + m) * F (nodeX d (N₀ + 2 * k)) := by
  set p := nodeSeq d N₀ m with hpdef
  have hE : ∀ F ∈ antiChartSpace d, ∃ F' : ℝ → ℂ, (∀ x, 0 < x → HasDerivAt F (F' x) x) ∧
      ContinuousOn F' (Ioi 0) ∧ IntegrableOn (fun x => x ^ 2 * ‖F x‖ ^ 2) (Ioi 0) ∧
      IntegrableOn (fun x => ‖F' x‖ ^ 2) (Ioi 0) ∧
      ∫ x in Ioi 0, ‖F' x‖ ^ 2 ≤ K ^ 2 * ∫ x in Ioi 0, x ^ 2 * ‖F x‖ ^ 2 :=
    fun F hF => hF.1.analytic hK
  have hsum : ∀ F ∈ antiChartSpace d, Summable fun j => max |p j| |p (j + 1)| *
      (‖F (p j)‖ ^ 2 + ‖F (p (j + 1))‖ ^ 2) :=
    fun F hF => summable_nodeSeq_of_rapidDecay hd hF.2 hN₀ m
  have hrel : ∀ i : Fin (m + 1), ∃ γ : ℕ → ℂ, ∃ M : ℝ, (∀ j, ‖γ j‖ ^ 2 ≤ M * (p (j + 1) + 1)) ∧
      ∀ F ∈ antiChartSpace d, Summable (fun j => γ j * F (p j)) ∧
        F (nodeX d (δ i)) = ∑' j, γ j * F (p j) :=
    fun i => GaloisForLFunctions.HTGeometry.exists_sampling_relation (antiChartSpace d) hE
      (nodeSeq_strictMono (by omega) hN₀ m) (nodeSeq_pos (by omega) hN₀ m 0)
      (tendsto_nodeSeq (by omega) N₀ m) one_pos hgap hbr hsum (nodeX_pos (by omega) (hδ i))
  choose γ M hγ hγrel using hrel
  obtain ⟨t, ht, hkill⟩ := exists_eliminating_combination γ
  set Γ : ℕ → ℂ := fun j => ∑ i, t i * γ i j with hΓ
  refine ⟨t, Γ, ∑ i, ‖t i‖ * (|M i| + 2), ht, fun j => ?_, fun F hF => ?_⟩
  · have hp1 : 0 ≤ p (j + 1) := (nodeSeq_pos (by omega) hN₀ m _).le
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
    have hmain : ∑ i, t i * F (nodeX d (δ i)) = ∑' j, Γ j * F (p j) := by
      calc ∑ i, t i * F (nodeX d (δ i)) = ∑ i, ∑' j, t i * (γ i j * F (p j)) := by
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
        = fun k => Γ (k + m) * F (nodeX d (N₀ + 2 * k)) := by
      funext k; rw [hpdef, nodeSeq_add]
    refine ⟨?_, ?_⟩
    · rw [← hshift]; exact (summable_nat_add_iff m).mpr hsumΓ
    · rw [hmain, ← hsplit, hshift]

/-- The chart weight at the integer node `X_n`: `√d X_n^{(d-1)/2}`. -/
def nodeWeight (d n : ℕ) : ℝ := Real.sqrt d * nodeX d n ^ (((d : ℝ) - 1) / 2)

theorem chartFun_nodeX {d : ℕ} (hd : 1 ≤ d) (f : ℝ → ℂ) (n : ℕ) :
    chartFun d f (nodeX d n) = (nodeWeight d n : ℂ) * f n := by
  unfold chartFun nodeWeight; rw [nodeX_pow hd]

theorem nodeWeight_nonneg (d n : ℕ) : 0 ≤ nodeWeight d n := by
  unfold nodeWeight; have := nodeX_nonneg d n; positivity

theorem nodeWeight_le {d : ℕ} (hd : 1 ≤ d) (n : ℕ) :
    nodeWeight d n ≤ Real.sqrt d * 2 ^ d * ((n : ℝ) + 1) ^ d := by
  unfold nodeWeight
  have hX := nodeX_le_two_mul d n hd
  have h0 := nodeX_nonneg d n
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hb : (1 : ℝ) ≤ 2 * ((n : ℝ) + 1) := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have h1 : nodeX d n ^ (((d : ℝ) - 1) / 2) ≤ (2 * ((n : ℝ) + 1)) ^ (((d : ℝ) - 1) / 2) :=
    Real.rpow_le_rpow h0 hX (by linarith)
  have h2 : (2 * ((n : ℝ) + 1)) ^ (((d : ℝ) - 1) / 2) ≤ (2 * ((n : ℝ) + 1)) ^ (d : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hb (by linarith)
  rw [Real.rpow_natCast, mul_pow] at h2
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (h1.trans h2) (Real.sqrt_nonneg _)

/-- The integer coefficients of a block relation: `t_i w_n` at `n = δ_i`, minus `Γ_{k+m} w_n` at the
node integers `n = N₀ + 2k`, with `w_n` the chart weight. -/
def blockCoeff (d N₀ m : ℕ) (δ : Fin (m + 1) → ℕ) (t : Fin (m + 1) → ℂ) (Γ : ℕ → ℂ) (n : ℕ) : ℂ :=
  (∑ i, if n = δ i then t i * (nodeWeight d n : ℂ) else 0) -
    (if N₀ ≤ n ∧ (n - N₀) % 2 = 0 then Γ ((n - N₀) / 2 + m) * (nodeWeight d n : ℂ) else 0)

/-- Growth of the block coefficients: `|a_n| ≤ C (n+1)^{d+1}`. -/
theorem norm_blockCoeff_le {d : ℕ} (hd : 3 ≤ d) {N₀ m : ℕ} (hN₀ : 1 ≤ N₀) (δ : Fin (m + 1) → ℕ)
    (t : Fin (m + 1) → ℂ) {Γ : ℕ → ℂ} {A : ℝ} (hΓ : ∀ j, ‖Γ j‖ ≤ A * (nodeSeq d N₀ m (j + 1) + 1))
    (n : ℕ) :
    ‖blockCoeff d N₀ m δ t Γ n‖ ≤
      ((∑ i, ‖t i‖ + 5 * |A|) * (Real.sqrt d * 2 ^ d)) * ((n : ℝ) + 1) ^ (d + 1) := by
  have hW := nodeWeight_le (by omega : 1 ≤ d) n
  have hW0 := nodeWeight_nonneg d n
  have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  set T := ∑ i, ‖t i‖ with hT
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun i _ => norm_nonneg _
  have hA0 := abs_nonneg A
  have h1 : ‖∑ i, (if n = δ i then t i * (nodeWeight d n : ℂ) else 0)‖ ≤ T * nodeWeight d n := by
    refine (norm_sum_le _ _).trans ?_
    rw [hT, Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => ?_
    split_ifs
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hW0]
    · simp only [norm_zero]; positivity
  have h2 : ‖(if N₀ ≤ n ∧ (n - N₀) % 2 = 0 then Γ ((n - N₀) / 2 + m) * (nodeWeight d n : ℂ) else 0)‖
      ≤ |A| * (5 * ((n : ℝ) + 1)) * nodeWeight d n := by
    split_ifs with hc
    · obtain ⟨hle, hev⟩ := hc
      obtain ⟨k, hk⟩ : ∃ k, n = N₀ + 2 * k := ⟨(n - N₀) / 2, by omega⟩
      subst hk
      have hkk : (N₀ + 2 * k - N₀) / 2 = k := by omega
      rw [hkk, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hW0]
      have hb := hΓ (k + m)
      rw [show k + m + 1 = (k + 1) + m by ring, nodeSeq_add,
        show N₀ + 2 * (k + 1) = N₀ + 2 * k + 2 by ring] at hb
      obtain ⟨hu2, -⟩ := nodeX_two_step hd (by omega : 1 ≤ N₀ + 2 * k)
      have hX := nodeX_le_two_mul d (N₀ + 2 * k) (by omega)
      have hu0 : 0 ≤ nodeX d (N₀ + 2 * k + 2) := nodeX_nonneg _ _
      have hΓb : ‖Γ (k + m)‖ ≤ |A| * (5 * (((N₀ + 2 * k : ℕ) : ℝ) + 1)) := by
        refine hb.trans ?_
        calc A * (nodeX d (N₀ + 2 * k + 2) + 1) ≤ |A| * (nodeX d (N₀ + 2 * k + 2) + 1) :=
              mul_le_mul_of_nonneg_right (le_abs_self A) (by linarith)
          _ ≤ |A| * (5 * (((N₀ + 2 * k : ℕ) : ℝ) + 1)) := by
              apply mul_le_mul_of_nonneg_left _ hA0
              have : (0 : ℝ) ≤ ((N₀ + 2 * k : ℕ) : ℝ) := Nat.cast_nonneg _
              linarith
      exact mul_le_mul_of_nonneg_right hΓb hW0
    · simp only [norm_zero]; positivity
  unfold blockCoeff
  refine (norm_sub_le _ _).trans ?_
  have hWn : nodeWeight d n * ((n : ℝ) + 1) ≤ Real.sqrt d * 2 ^ d * ((n : ℝ) + 1) ^ (d + 1) := by
    rw [pow_succ]
    have := mul_le_mul_of_nonneg_right hW (by linarith : (0 : ℝ) ≤ (n : ℝ) + 1)
    linarith
  have hW1 : nodeWeight d n ≤ Real.sqrt d * 2 ^ d * ((n : ℝ) + 1) ^ (d + 1) := by
    have : nodeWeight d n ≤ nodeWeight d n * ((n : ℝ) + 1) := le_mul_of_one_le_right hW0 hn1
    linarith
  have e1 : T * nodeWeight d n ≤ T * (Real.sqrt d * 2 ^ d * ((n : ℝ) + 1) ^ (d + 1)) :=
    mul_le_mul_of_nonneg_left hW1 hT0
  have e2 : |A| * (5 * ((n : ℝ) + 1)) * nodeWeight d n
      ≤ 5 * |A| * (Real.sqrt d * 2 ^ d * ((n : ℝ) + 1) ^ (d + 1)) := by
    have := mul_le_mul_of_nonneg_left hWn (by positivity : (0 : ℝ) ≤ 5 * |A|)
    nlinarith
  nlinarith

/-- Sum against the block coefficients. -/
theorem tsum_blockCoeff_mul {d N₀ m : ℕ} (δ : Fin (m + 1) → ℕ) (t : Fin (m + 1) → ℂ) (Γ : ℕ → ℂ)
    (h : ℕ → ℂ) (hs : Summable fun k => Γ (k + m) * ((nodeWeight d (N₀ + 2 * k) : ℂ) * h (N₀ + 2 * k))) :
    Summable (fun n => blockCoeff d N₀ m δ t Γ n * h n) ∧
      ∑' n, blockCoeff d N₀ m δ t Γ n * h n =
        ∑ i, t i * ((nodeWeight d (δ i) : ℂ) * h (δ i)) -
          ∑' k, Γ (k + m) * ((nodeWeight d (N₀ + 2 * k) : ℂ) * h (N₀ + 2 * k)) := by
  set Aterm : Fin (m + 1) → ℕ → ℂ := fun i n =>
    if n = δ i then t i * ((nodeWeight d (δ i) : ℂ) * h (δ i)) else 0 with hA
  set B : ℕ → ℂ := fun n =>
    if N₀ ≤ n ∧ (n - N₀) % 2 = 0 then Γ ((n - N₀) / 2 + m) * ((nodeWeight d n : ℂ) * h n) else 0
    with hB
  have hsplit : (fun n => blockCoeff d N₀ m δ t Γ n * h n) = fun n => (∑ i, Aterm i n) - B n := by
    funext n
    simp only [blockCoeff, hA, hB, sub_mul, Finset.sum_mul]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs with hn
      · subst hn; ring
      · simp
    · split_ifs <;> ring
  have hAsum : ∀ i, Summable (Aterm i) := fun i => by
    simp only [hA]; exact (hasSum_ite_eq (δ i) _).summable
  have hAtsum : ∀ i, ∑' n, Aterm i n = t i * ((nodeWeight d (δ i) : ℂ) * h (δ i)) := fun i => by
    simp only [hA]; exact tsum_ite_eq (δ i) _
  set g : ℕ → ℕ := fun k => N₀ + 2 * k with hg
  have hginj : Function.Injective g := fun a b hab => by simp only [hg] at hab; omega
  have hBg : B ∘ g = fun k => Γ (k + m) * ((nodeWeight d (N₀ + 2 * k) : ℂ) * h (N₀ + 2 * k)) := by
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
  have hBtsum : ∑' n, B n = ∑' k, Γ (k + m) * ((nodeWeight d (N₀ + 2 * k) : ℂ) * h (N₀ + 2 * k)) := by
    rw [← hBg]
    exact (hginj.tsum_eq (Function.support_subset_iff'.mpr hBout)).symm
  have hAall : Summable fun n => ∑ i, Aterm i n := summable_sum fun i _ => hAsum i
  rw [hsplit]
  refine ⟨hAall.sub hBsum, ?_⟩
  rw [hAall.tsum_sub hBsum, Summable.tsum_finsetSum (fun i _ => hAsum i), hBtsum]
  simp_rw [hAtsum]

/-- Theta series with coefficients `O((n+1)^B)` converge. -/
theorem summable_mul_gammaRPowKernel (k B : ℕ) {e : ℕ → ℂ} {C : ℝ}
    (he : ∀ n, ‖e n‖ ≤ C * ((n : ℝ) + 1) ^ B) {y : ℝ} (hy : 0 < y) :
    Summable fun n => e n * gammaRPowKernel k (((n : ℝ) + 1) * y) := by
  obtain ⟨C', hC'⟩ := exists_norm_gammaRPowKernel_le k (c := ((B + 2 : ℕ) : ℝ)) (by positivity)
  have hbase : Summable fun n : ℕ => C * C' * (y ^ (B + 2))⁻¹ * (((n : ℝ) + 1) ^ 2)⁻¹ := by
    have h := (Real.summable_nat_pow_inv (p := 2)).mpr (by norm_num)
    have h' := (summable_nat_add_iff 1).mpr h
    exact (h'.mul_left (C * C' * (y ^ (B + 2))⁻¹)).congr (fun n => by push_cast; ring)
  refine Summable.of_norm_bounded hbase (fun n => ?_)
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hx : 0 < ((n : ℝ) + 1) * y := mul_pos hn hy
  have h1 := hC' _ hx
  rw [Real.rpow_neg hx.le, Real.rpow_natCast] at h1
  rw [norm_mul]
  calc ‖e n‖ * ‖gammaRPowKernel k (((n : ℝ) + 1) * y)‖
      ≤ (C * ((n : ℝ) + 1) ^ B) * (C' * ((((n : ℝ) + 1) * y) ^ (B + 2))⁻¹) :=
        mul_le_mul (he n) h1 (norm_nonneg _) (le_trans (norm_nonneg _) (he n))
    _ = C * C' * (y ^ (B + 2))⁻¹ * (((n : ℝ) + 1) ^ 2)⁻¹ := by
        rw [mul_pow, pow_add ((n : ℝ) + 1) B 2]; field_simp

/-- The block coefficients annihilate every theta test function. -/
theorem blockCoeff_theta_relation {k : ℕ} (hk : 2 ≤ k) {N₀ m : ℕ} (δ : Fin (m + 1) → ℕ)
    (t : Fin (m + 1) → ℂ) (Γ : ℕ → ℂ)
    (hrel : ∀ F ∈ antiChartSpace (k + 1),
      Summable (fun j => Γ (j + m) * F (nodeX (k + 1) (N₀ + 2 * j))) ∧
        ∑ i, t i * F (nodeX (k + 1) (δ i)) = ∑' j, Γ (j + m) * F (nodeX (k + 1) (N₀ + 2 * j)))
    {y : ℝ} (hy : 0 < y) :
    Summable (fun n => blockCoeff (k + 1) N₀ m δ t Γ n * thetaFunction k y n) ∧
      ∑' n, blockCoeff (k + 1) N₀ m δ t Γ n * thetaFunction k y n = 0 := by
  obtain ⟨hs, heq⟩ := hrel _ (chartFun_thetaFunction_mem hk hy)
  simp_rw [chartFun_nodeX (by omega : 1 ≤ k + 1)] at hs heq
  set h : ℕ → ℂ := fun n => thetaFunction k y n with hh
  obtain ⟨hsum, htsum⟩ := tsum_blockCoeff_mul (d := k + 1) (N₀ := N₀) δ t Γ h hs
  exact ⟨hsum, by rw [htsum, sub_eq_zero]; exact heq⟩

theorem skipped_index_inj {N₀ m r r' : ℕ} {i i' : Fin (m + 1)}
    (h : N₀ + 2 * ((m + 1) * r + i) + 1 = N₀ + 2 * ((m + 1) * r' + i') + 1) : r = r' ∧ i = i' := by
  have h1 := Nat.add_right_cancel h
  have h2 := Nat.add_left_cancel h1
  have h3 := Nat.eq_of_mul_eq_mul_left (by norm_num) h2
  have hm : 0 < m + 1 := Nat.succ_pos m
  have e1 := congrArg (· / (m + 1)) h3
  have e2 := congrArg (· % (m + 1)) h3
  simp only [Nat.mul_add_div hm, Nat.div_eq_of_lt i.isLt, Nat.div_eq_of_lt i'.isLt,
    Nat.mul_add_mod, Nat.mod_eq_of_lt i.isLt, Nat.mod_eq_of_lt i'.isLt] at e1 e2
  exact ⟨by simpa using e1, Fin.ext e2⟩

/-- **Infinitely many theta relations for `Γ_ℝ(s)^{k+1}`, `k ≥ 2`, vanishing below `N`.** -/
theorem gammaRPow_theta_relations_vanishing_below {k : ℕ} (hk : 2 ≤ k) (N : ℕ) :
    ∃ e : ℕ → ℕ → ℂ, LinearIndependent ℂ e ∧ ∀ r, (∀ n, n + 1 < N → e r n = 0) ∧ ∃ C : ℝ,
      (∀ n, ‖e r n‖ ≤ C * ((n : ℝ) + 1) ^ (k + 2)) ∧
      ∀ y : ℝ, 0 < y → (∑' n, e r n * gammaRPowKernel k (((n : ℝ) + 1) * (1 / y)))
        = (y : ℂ) * ∑' n, e r n * gammaRPowKernel k (((n : ℝ) + 1) * y) := by
  have hd : 3 ≤ k + 1 := by omega
  obtain ⟨K, a, N₀, m, hN₀, hNN₀, -, hK, hgap, hbr⟩ := exists_chart_sampling_parameters hd N
  set δ : ℕ → Fin (m + 1) → ℕ := fun r i => N₀ + 2 * ((m + 1) * r + i) + 1 with hδ
  have hblock : ∀ r, ∃ t : Fin (m + 1) → ℂ, ∃ Γ : ℕ → ℂ, ∃ A : ℝ, (∃ i, t i ≠ 0) ∧
      (∀ j, ‖Γ j‖ ≤ A * (nodeSeq (k + 1) N₀ m (j + 1) + 1)) ∧
      ∀ F ∈ antiChartSpace (k + 1), Summable (fun j => Γ (j + m) * F (nodeX (k + 1) (N₀ + 2 * j))) ∧
        ∑ i, t i * F (nodeX (k + 1) (δ r i)) = ∑' j, Γ (j + m) * F (nodeX (k + 1) (N₀ + 2 * j)) :=
    fun r => exists_block_relation hd hN₀ hK hgap hbr (δ r) (fun i => by simp only [hδ]; omega)
  choose t Γ A ht hΓ hrel using hblock
  set a' : ℕ → ℕ → ℂ := fun r n => blockCoeff (k + 1) N₀ m (δ r) (t r) (Γ r) n with ha'
  have ha0 : ∀ r, a' r 0 = 0 := by
    intro r
    simp only [ha', blockCoeff]
    rw [if_neg (by omega)]
    simp only [sub_zero]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [if_neg (by simp only [hδ]; omega)]
  refine ⟨fun r n => a' r (n + 1), ?_, fun r => ?_⟩
  · rw [linearIndependent_iff']
    intro sfin g hg r hr
    obtain ⟨i, hi⟩ := ht r
    have hval : ∀ r', a' r' (δ r i) = if r' = r then t r i * (nodeWeight (k + 1) (δ r i) : ℂ) else 0 := by
      intro r'
      simp only [ha', blockCoeff]
      rw [if_neg (by simp only [hδ]; omega), sub_zero]
      split_ifs with hrr
      · subst hrr
        rw [Finset.sum_eq_single i]
        · rw [if_pos rfl]
        · intro i' _ hne
          rw [if_neg]
          intro heq
          simp only [hδ] at heq
          exact hne (skipped_index_inj heq).2.symm
        · simp
      · refine Finset.sum_eq_zero fun i' _ => ?_
        rw [if_neg]
        intro heq
        simp only [hδ] at heq
        exact hrr (skipped_index_inj heq).1.symm
    have hn : δ r i = (δ r i - 1) + 1 := by simp only [hδ]; omega
    have hev := congrFun hg (δ r i - 1)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hev
    rw [← hn] at hev
    simp_rw [hval] at hev
    rw [Finset.sum_eq_single r (fun r' _ hne => by rw [if_neg hne, mul_zero])
      (fun h => absurd hr h), if_pos rfl] at hev
    have hW : (nodeWeight (k + 1) (δ r i) : ℂ) ≠ 0 := by
      have h1 : 0 < nodeX (k + 1) (δ r i) := nodeX_pos (by omega) (by simp only [hδ]; omega)
      have : 0 < nodeWeight (k + 1) (δ r i) := by unfold nodeWeight; positivity
      exact_mod_cast this.ne'
    rcases mul_eq_zero.mp hev with h | h
    · exact h
    · exact absurd h (mul_ne_zero hi hW)
  · have hlow : ∀ n, n + 1 < N → a' r (n + 1) = 0 := by
      intro n hn
      simp only [ha', blockCoeff]
      rw [if_neg (by omega), sub_zero]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [if_neg (by simp only [hδ]; omega)]
    refine ⟨hlow, ?_⟩
    set C₀ := (∑ i, ‖t r i‖ + 5 * |A r|) * (Real.sqrt ((k + 1 : ℕ) : ℝ) * 2 ^ (k + 1)) with hC₀
    have hC₀0 : 0 ≤ C₀ := by
      have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => norm_nonneg (t r i))
      have := abs_nonneg (A r); positivity
    have hgrowth : ∀ n, ‖a' r (n + 1)‖ ≤ 2 ^ (k + 2) * C₀ * ((n : ℝ) + 1) ^ (k + 2) := by
      intro n
      have h := norm_blockCoeff_le hd hN₀ (δ r) (t r) (hΓ r) (n + 1)
      refine h.trans ?_
      have hb : (((n + 1 : ℕ) : ℝ) + 1) ^ (k + 1 + 1) ≤ 2 ^ (k + 2) * ((n : ℝ) + 1) ^ (k + 2) := by
        rw [← mul_pow]
        apply pow_le_pow_left₀ (by positivity)
        push_cast; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      have := mul_le_mul_of_nonneg_left hb hC₀0
      calc C₀ * (((n + 1 : ℕ) : ℝ) + 1) ^ (k + 1 + 1) ≤ C₀ * (2 ^ (k + 2) * ((n : ℝ) + 1) ^ (k + 2)) :=
            this
        _ = 2 ^ (k + 2) * C₀ * ((n : ℝ) + 1) ^ (k + 2) := by ring
    refine ⟨2 ^ (k + 2) * C₀, hgrowth, fun y hy => ?_⟩
    obtain ⟨hsum, hzero⟩ := blockCoeff_theta_relation hk (δ r) (t r) (Γ r) (hrel r) hy
    have hshift := hsum.tsum_eq_zero_add
    rw [hzero] at hshift
    have h0 : a' r 0 * thetaFunction k y ((0 : ℕ) : ℝ) = 0 := by rw [ha0 r, zero_mul]
    simp only [ha'] at h0
    rw [h0, zero_add] at hshift
    have hy' : 0 < y⁻¹ := inv_pos.mpr hy
    have hs1 := summable_mul_gammaRPowKernel k (k + 2) hgrowth hy
    have hs2 := summable_mul_gammaRPowKernel k (k + 2) hgrowth hy'
    have hexp : (fun n : ℕ => blockCoeff (k + 1) N₀ m (δ r) (t r) (Γ r) (n + 1) *
        thetaFunction k y ((n + 1 : ℕ) : ℝ)) = fun n =>
        a' r (n + 1) * gammaRPowKernel k (((n : ℝ) + 1) * y) -
          ((y⁻¹ : ℝ) : ℂ) * (a' r (n + 1) * gammaRPowKernel k (((n : ℝ) + 1) * y⁻¹)) := by
      funext n
      simp only [ha', thetaFunction]
      push_cast
      ring_nf
    rw [hexp, hs1.tsum_sub (hs2.mul_left _), hs2.tsum_mul_left] at hshift
    have hyC : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
    have hfin := sub_eq_zero.mp hshift.symm
    rw [show (fun n : ℕ => a' r (n + 1) * gammaRPowKernel k (((n : ℝ) + 1) * (1 / y)))
        = fun n => a' r (n + 1) * gammaRPowKernel k (((n : ℝ) + 1) * y⁻¹) by
      funext n; rw [one_div]]
    rw [hfin]
    push_cast
    field_simp

/-- **The functional equation of `ζ(s)^d` does not determine it, for every `d ≥ 3`, even together
with any finite set of coefficients.** For `d = k+1 ≥ 3` and every `N` there are linearly
independent coefficient sequences `e_r`, vanishing at all integers `< N`, such that each
`Γ_ℝ(s)^d Σ_n e_r(n)(n+1)^{-s}` (for `Re s > k+3`) is the restriction of an entire function `Λ_r`
with `Λ_r(1-s) = Λ_r(s)`. -/
theorem gammaRPow_functional_equation_abundance {k : ℕ} (hk : 2 ≤ k) (N : ℕ) :
    ∃ e : ℕ → ℕ → ℂ, LinearIndependent ℂ e ∧ ∀ r, (∀ n, n + 1 < N → e r n = 0) ∧
      Differentiable ℂ (mellin fun y : ℝ => ∑' n : ℕ, e r n * gammaRPowKernel k (((n : ℝ) + 1) * y)) ∧
      (∀ s : ℂ, mellin (fun y : ℝ => ∑' n : ℕ, e r n * gammaRPowKernel k (((n : ℝ) + 1) * y)) (1 - s)
        = mellin (fun y : ℝ => ∑' n : ℕ, e r n * gammaRPowKernel k (((n : ℝ) + 1) * y)) s) ∧
      (∀ s : ℂ, (k : ℝ) + 3 < s.re →
        mellin (fun y : ℝ => ∑' n : ℕ, e r n * gammaRPowKernel k (((n : ℝ) + 1) * y)) s
          = (∑' n : ℕ, e r n * (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s)) * Gammaℝ s ^ (k + 1)) := by
  obtain ⟨e, hind, he⟩ := gammaRPow_theta_relations_vanishing_below hk N
  refine ⟨e, hind, fun r => ?_⟩
  obtain ⟨hlow, C, hC, hsym⟩ := he r
  have hC' : ∀ n : ℕ, ‖e r n‖ ≤ C * ((n : ℝ) + 1) ^ ((k + 2 : ℕ) : ℝ) := fun n => by
    rw [Real.rpow_natCast]; exact hC n
  obtain ⟨h1, h2, h3⟩ := gammaRPow_theta_converse k (by positivity) hC' hsym
  refine ⟨hlow, h1, h2, fun s hs => h3 s (by push_cast; linarith)⟩

end RHTower.GammaRPowTwins
