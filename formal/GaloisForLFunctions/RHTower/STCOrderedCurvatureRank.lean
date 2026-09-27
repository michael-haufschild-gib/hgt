import GaloisForLFunctions.RHTower.STCCofinalTriangleHolonomy
import GaloisForLFunctions.RHTower.STCPrimeWindowPackets

/-!
# Ordered cross-prime Stokes curvature has unbounded exterior rank

The analytic reflection-odd pair scalar `c_pq(g)` is symmetric in `p, q` and, away from the
neutral grade, is a sum of four separable one-prime channels; every finite symmetric packet
matrix `(c_{p_i p_j}(g))` therefore has rank at most four.  Placing `+c_pq` above and `-c_pq`
below the prime-order diagonal changes this completely: for every fixed `g ≠ 0` and every even
`n`, suitable packets of `n` large primes in a shrinking multiplicative window give an ordered
matrix of full rank `n`.  The normalized ordered matrix tends to the sign matrix `S_n`, whose
determinant is odd (it is `1 + n ≡ 1` modulo two by the matrix determinant lemma).

Consequently the ordered curvature is not the matrix of any fixed finite-dimensional
alternating form evaluated on one-prime sections.
-/

open Filter Topology Matrix

namespace RHTower

noncomputable section

/-! ### Symmetry and four-channel rank bound -/

theorem routeRCrossPrimeStokesRatio_swap (p q : ℕ) (g : ℝ) :
    routeRCrossPrimeStokesRatio q p g = (routeRCrossPrimeStokesRatio p q g)⁻¹ := by
  unfold routeRCrossPrimeStokesRatio
  simp only [div_eq_mul_inv, mul_inv, inv_inv]
  ring

/-- The reflection-odd pair scalar is symmetric in the two primes. -/
theorem routeRCrossPrimeStokesOddCurvature_comm (p q : ℕ) (g : ℝ) :
    routeRCrossPrimeStokesOddCurvature q p g = routeRCrossPrimeStokesOddCurvature p q g := by
  rw [routeRCrossPrimeStokesOddCurvature_eq, routeRCrossPrimeStokesOddCurvature_eq,
    routeRCrossPrimeStokesGauge, routeRCrossPrimeStokesGauge, routeRCrossPrimeStokesRatio_swap,
    inv_inv, routeRCrossPrimeStokesPhase, routeRCrossPrimeStokesPhase]
  ring_nf

/-- The symmetric pair matrix of a finite packet. -/
def symmetricStokesMatrix {n : ℕ} (p : Fin n → ℕ) (g : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => routeRCrossPrimeStokesOddCurvature (p i) (p j) g

/-- **Four-channel rank bound.** Every finite symmetric packet matrix has rank at most four. -/
theorem rank_symmetricStokesMatrix_le {n : ℕ} (p : Fin n → ℕ) (hp : ∀ i, 1 < p i) (g : ℝ) :
    (symmetricStokesMatrix p g).rank ≤ 4 := by
  by_cases hg : g = 0
  · have : symmetricStokesMatrix p g = 0 := by
      ext i j
      simp [symmetricStokesMatrix, hg, (routeRCrossPrimeStokesOddCurvature_eq_zero_iff
        (hp i) (hp j) 0).mpr rfl]
    rw [this, Matrix.rank_zero]
    norm_num
  let U : Matrix (Fin n) (Fin 4) ℝ := Matrix.of fun i t =>
    ![stokesChannelU (p i) g, 1, stokesChannelV (p i) g, stokesChannelW (p i) g] t
  let V : Matrix (Fin 4) (Fin n) ℝ := Matrix.of fun t j =>
    ![-2, -2 * stokesChannelU (p j) g, -2 * stokesChannelW (p j) g,
      -2 * stokesChannelV (p j) g] t
  have hfac : symmetricStokesMatrix p g = U * V := by
    ext i j
    simp only [symmetricStokesMatrix, Matrix.of_apply, Matrix.mul_apply, Fin.sum_univ_four,
      U, V, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three]
    rw [stokes_odd_four_channel (hp i) (hp j) hg]
    simp
    ring
  rw [hfac]
  calc (U * V).rank ≤ U.rank := Matrix.rank_mul_le_left U V
    _ ≤ Fintype.card (Fin 4) := Matrix.rank_le_card_width U
    _ = 4 := Fintype.card_fin 4

/-! ### The sign matrix has odd determinant in even dimension -/

/-- The sign matrix `S_n`: `+1` above the diagonal, `-1` below it, `0` on it. -/
def orderSignMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of fun i j => if i < j then 1 else if j < i then -1 else 0

/-- Modulo two, `S_n = 1 + 1 1ᵀ`, so `det S_n ≡ 1 + n`. For even `n` the determinant is odd. -/
theorem det_orderSignMatrix_ne_zero {n : ℕ} (hn : Even n) :
    (orderSignMatrix n).det ≠ 0 := by
  intro h
  have hmap : (orderSignMatrix n).map (Int.cast : ℤ → ZMod 2) =
      1 + replicateCol Unit (fun _ : Fin n => (1 : ZMod 2)) *
        replicateRow Unit (fun _ : Fin n => (1 : ZMod 2)) := by
    ext i j
    rcases lt_trichotomy i j with hij | hij | hij
    · simp [orderSignMatrix, Matrix.mul_apply, hij, hij.ne]
    · subst hij
      simp [orderSignMatrix, Matrix.mul_apply]
      rfl
    · simp [orderSignMatrix, Matrix.mul_apply, hij.ne', not_lt.mpr hij.le, hij]
  have hdet : ((orderSignMatrix n).det : ZMod 2) =
      ((orderSignMatrix n).map (Int.cast : ℤ → ZMod 2)).det := Int.cast_det _
  rw [h, Int.cast_zero, hmap, det_one_add_replicateCol_mul_replicateRow] at hdet
  have hsum : (fun _ : Fin n => (1 : ZMod 2)) ⬝ᵥ (fun _ : Fin n => (1 : ZMod 2)) = 0 := by
    simp only [dotProduct, mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    obtain ⟨m, rfl⟩ := hn
    rw [Nat.cast_add, ← two_mul]
    simp [show (2 : ZMod 2) = 0 from rfl]
  rw [hsum, add_zero] at hdet
  exact one_ne_zero hdet.symm

/-- The real sign matrix is invertible in even dimension. -/
theorem det_orderSignMatrix_real_ne_zero {n : ℕ} (hn : Even n) :
    ((orderSignMatrix n).map (Int.cast : ℤ → ℝ)).det ≠ 0 := by
  rw [← Int.cast_det]
  exact_mod_cast det_orderSignMatrix_ne_zero hn

/-! ### Ordered packet matrix -/

/-- The ordered curvature matrix of a packet: `+c` above and `-c` below the diagonal. -/
def orderedStokesMatrix {n : ℕ} (p : Fin n → ℕ) (g : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j =>
    if i < j then routeRCrossPrimeStokesOddCurvature (p i) (p j) g
    else if j < i then -routeRCrossPrimeStokesOddCurvature (p j) (p i) g else 0

/-! ### Asymptotics in a shrinking window -/

private theorem abs_coth_le_four {A : ℝ} (hA : 1 ≤ |A|) :
    |Real.cosh A / Real.sinh A| ≤ 4 := by
  have hs : 0 < |Real.sinh A| := by
    rw [abs_pos, Real.sinh_ne_zero]
    intro h
    rw [h, abs_zero] at hA
    linarith
  rw [abs_div, abs_of_pos (Real.cosh_pos A), div_le_iff₀ hs]
  have hsabs : |Real.sinh A| = Real.sinh |A| := by
    rcases le_or_gt 0 A with h | h
    · rw [abs_of_nonneg h, abs_of_nonneg (Real.sinh_nonneg_iff.mpr h)]
    · rw [abs_of_neg h, abs_of_neg (Real.sinh_neg_iff.mpr h), Real.sinh_neg]
  have hcabs : Real.cosh A = Real.cosh |A| := (Real.cosh_abs A).symm
  rw [hsabs, hcabs, Real.cosh_eq, Real.sinh_eq]
  have h1 : 2 ≤ Real.exp |A| := by
    have := Real.add_one_le_exp |A|
    linarith
  have h2 : Real.exp (-|A|) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [abs_nonneg A])
  have h3 : 0 < Real.exp (-|A|) := Real.exp_pos _
  nlinarith

/-- `sinh(A+δ)/sinh A → 1` when `|A| → ∞` and `δ → 0`. -/
theorem tendsto_sinh_add_div_sinh {α : Type*} {l : Filter α} {A δ : α → ℝ}
    (hA : Tendsto (fun k => |A k|) l atTop) (hδ : Tendsto δ l (𝓝 0)) :
    Tendsto (fun k => Real.sinh (A k + δ k) / Real.sinh (A k)) l (𝓝 1) := by
  have hcosh : Tendsto (fun k => Real.cosh (δ k)) l (𝓝 1) := by
    have h := (Real.continuous_cosh.tendsto 0).comp hδ
    simp only [Function.comp_def, Real.cosh_zero] at h
    exact h
  have hsinh : Tendsto (fun k => Real.sinh (δ k)) l (𝓝 0) := by
    have h := (Real.continuous_sinh.tendsto 0).comp hδ
    simp only [Function.comp_def, Real.sinh_zero] at h
    exact h
  have hbdd : Tendsto (fun k => Real.sinh (δ k) * (Real.cosh (A k) / Real.sinh (A k))) l
      (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (by simpa using hsinh.norm.mul_const 4)
    filter_upwards [hA.eventually_ge_atTop 1] with k hk
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (abs_coth_le_four hk) (abs_nonneg _)
  have hsum := hcosh.add hbdd
  rw [add_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards [hA.eventually_ge_atTop 1] with k hk
  have hs : Real.sinh (A k) ≠ 0 := by
    rw [Real.sinh_ne_zero]
    intro h
    rw [h, abs_zero] at hk
    linarith
  rw [Real.sinh_add]
  field_simp

/-- Normalized pair scalar near a large common logarithm `L`: if `x - L → 0`, `y - L → 0` and
`L → ∞`, then `c/(−4 sinh(gL)) → 1`, written in logarithmic coordinates. -/
theorem tendsto_stokesOdd_log_normalized {α : Type*} {l : Filter α} {g : ℝ} (hg : g ≠ 0)
    {L x y : α → ℝ} (hL : Tendsto L l atTop) (hx : Tendsto (fun k => x k - L k) l (𝓝 0))
    (hy : Tendsto (fun k => y k - L k) l (𝓝 0)) :
    Tendsto (fun k => (-4 * Real.sinh (g * L k))⁻¹ *
      (-2 * Real.sinh (g * (x k + y k) / 2) *
        (Real.sinh (g * y k / 2) / Real.sinh (g * x k / 2) +
          (Real.sinh (g * y k / 2) / Real.sinh (g * x k / 2))⁻¹))) l (𝓝 1) := by
  have hgabs : 0 < |g| := abs_pos.mpr hg
  have hA1 : Tendsto (fun k => |g * L k|) l atTop := by
    refine (hL.const_mul_atTop hgabs).congr' ?_
    filter_upwards [hL.eventually_ge_atTop 0] with k hk
    rw [abs_mul, abs_of_nonneg hk]
  have hA2 : Tendsto (fun k => |g * L k / 2|) l atTop := by
    refine (hA1.atTop_div_const two_pos).congr' (Eventually.of_forall fun k => ?_)
    show |g * L k| / 2 = |g * L k / 2|
    rw [abs_div, abs_two]
  have hs1 : ∀ᶠ k in l, Real.sinh (g * L k) ≠ 0 := by
    filter_upwards [hA1.eventually_ge_atTop 1] with k hk
    rw [Real.sinh_ne_zero]; intro h; rw [h, abs_zero] at hk; linarith
  have hs2 : ∀ᶠ k in l, Real.sinh (g * L k / 2) ≠ 0 := by
    filter_upwards [hA2.eventually_ge_atTop 1] with k hk
    rw [Real.sinh_ne_zero]; intro h; rw [h, abs_zero] at hk; linarith
  have hphase : Tendsto (fun k => Real.sinh (g * (x k + y k) / 2) / Real.sinh (g * L k)) l
      (𝓝 1) := by
    refine (tendsto_sinh_add_div_sinh (A := fun k => g * L k)
      (δ := fun k => g * ((x k - L k) + (y k - L k)) / 2) hA1 ?_).congr (fun k => ?_)
    · simpa using ((hx.add hy).const_mul g).div_const 2
    · show Real.sinh (g * L k + g * ((x k - L k) + (y k - L k)) / 2) / Real.sinh (g * L k) = _
      rw [show g * L k + g * ((x k - L k) + (y k - L k)) / 2 = g * (x k + y k) / 2 by ring]
  have hone : ∀ z : α → ℝ, Tendsto (fun k => z k - L k) l (𝓝 0) →
      Tendsto (fun k => Real.sinh (g * z k / 2) / Real.sinh (g * L k / 2)) l (𝓝 1) := by
    intro z hz
    refine (tendsto_sinh_add_div_sinh (A := fun k => g * L k / 2)
      (δ := fun k => g * (z k - L k) / 2) hA2 ?_).congr (fun k => ?_)
    · simpa using (hz.const_mul g).div_const 2
    · show Real.sinh (g * L k / 2 + g * (z k - L k) / 2) / Real.sinh (g * L k / 2) = _
      rw [show g * L k / 2 + g * (z k - L k) / 2 = g * z k / 2 by ring]
  have hR : Tendsto (fun k => Real.sinh (g * y k / 2) / Real.sinh (g * x k / 2)) l (𝓝 1) := by
    have h := (hone y hy).div (hone x hx) one_ne_zero
    rw [div_one] at h
    refine h.congr' ?_
    filter_upwards [hs2] with k hk
    simp only [Pi.div_apply]
    rw [div_div_div_cancel_right₀ hk]
  have hmain := hphase.mul ((hR.add (hR.inv₀ one_ne_zero)).div_const 2)
  rw [show (1 : ℝ) * ((1 + 1⁻¹) / 2) = 1 by norm_num] at hmain
  refine hmain.congr' ?_
  filter_upwards [hs1] with k hk
  field_simp
  ring

/-- The analytic pair scalar in logarithmic coordinates. -/
theorem routeRCrossPrimeStokesOddCurvature_log_form {p q : ℕ} (hp : 1 < p) (hq : 1 < q)
    {g : ℝ} (hg : g ≠ 0) :
    routeRCrossPrimeStokesOddCurvature p q g =
      -2 * Real.sinh (g * (Real.log p + Real.log q) / 2) *
        (Real.sinh (g * Real.log q / 2) / Real.sinh (g * Real.log p / 2) +
          (Real.sinh (g * Real.log q / 2) / Real.sinh (g * Real.log p / 2))⁻¹) := by
  rw [routeRCrossPrimeStokesOddCurvature_eq, routeRCrossPrimeStokesGauge,
    routeRCrossPrimeStokesRatio_eq_sinh_div hp hq hg, routeRCrossPrimeStokesPhase]

/-! ### Full rank of ordered packets -/

private theorem tendsto_log_ratio_zero {P Q : ℕ → ℕ} (hP : ∀ k, 0 < P k)
    (hlo : ∀ k, P k ≤ Q k) (hhi : ∀ k, (Q k : ℝ) < (1 + 1 / ((k : ℝ) + 1)) * P k) :
    Tendsto (fun k => Real.log (Q k) - Real.log (P k)) atTop (𝓝 0) := by
  have hshrink : Tendsto (fun k : ℕ => Real.log (1 + 1 / ((k : ℝ) + 1))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun k : ℕ => 1 + 1 / ((k : ℝ) + 1)) atTop (𝓝 (1 + 0)) :=
      tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat
    have h2 := (Real.continuousAt_log (by norm_num : (1 + 0 : ℝ) ≠ 0)).tendsto.comp h1
    simp only [Function.comp_def, add_zero, Real.log_one] at h2
    exact h2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hshrink (fun k => ?_)
    (fun k => ?_)
  · have hPk : (0 : ℝ) < P k := by exact_mod_cast hP k
    have := Real.log_le_log hPk (show ((P k : ℕ) : ℝ) ≤ Q k by exact_mod_cast hlo k)
    linarith
  · have hPk : (0 : ℝ) < P k := by exact_mod_cast hP k
    have hQk : (0 : ℝ) < Q k := hPk.trans_le (show ((P k : ℕ) : ℝ) ≤ Q k by exact_mod_cast hlo k)
    have := Real.log_le_log hQk (hhi k).le
    rw [Real.log_mul (by positivity) hPk.ne'] at this
    linarith

/-- **Unbounded ordered rank.** For every `g ≠ 0`, every even `n` and every threshold `N`,
there are `n` increasing primes above `N` whose ordered curvature matrix has full rank `n`. -/
theorem exists_prime_packet_orderedStokesMatrix_rank {g : ℝ} (hg : g ≠ 0) {n : ℕ}
    (hn : Even n) (N : ℕ) :
    ∃ p : Fin n → ℕ, StrictMono p ∧ (∀ i, (p i).Prime) ∧ (∀ i, N < p i) ∧
      (orderedStokesMatrix p g).rank = n := by
  have hpk : ∀ k : ℕ, ∃ P : ℕ → ℕ, StrictMono P ∧ (∀ i, (P i).Prime) ∧
      ((max N k : ℕ) : ℝ) < P 0 ∧ ∀ i ≤ n, (P i : ℝ) < (1 + 1 / ((k : ℝ) + 1)) * P 0 :=
    fun k => exists_prime_packet (by positivity) n _
  choose P hmono hprime hbig hwin using hpk
  -- the base logarithm tends to infinity
  have hL : Tendsto (fun k => Real.log (P k 0)) atTop atTop := by
    refine Real.tendsto_log_atTop.comp (tendsto_atTop_mono (fun k => ?_)
      tendsto_natCast_atTop_atTop)
    have := hbig k
    have hk : (k : ℝ) ≤ ((max N k : ℕ) : ℝ) := by exact_mod_cast le_max_right N k
    linarith
  have hgap : ∀ i : Fin n, Tendsto (fun k => Real.log (P k i) - Real.log (P k 0)) atTop
      (𝓝 0) := by
    intro i
    exact tendsto_log_ratio_zero (fun k => (hprime k 0).pos)
      (fun k => (hmono k).monotone (Nat.zero_le _))
      (fun k => hwin k i (le_of_lt i.isLt))
  -- entrywise convergence of the normalized ordered matrix
  set S : Matrix (Fin n) (Fin n) ℝ := (orderSignMatrix n).map (Int.cast : ℤ → ℝ) with hS
  let M : ℕ → Matrix (Fin n) (Fin n) ℝ := fun k =>
    (-4 * Real.sinh (g * Real.log (P k 0)))⁻¹ • orderedStokesMatrix (fun i => P k i) g
  have hone : ∀ i j : Fin n, Tendsto (fun k => (-4 * Real.sinh (g * Real.log (P k 0)))⁻¹ *
      routeRCrossPrimeStokesOddCurvature (P k i) (P k j) g) atTop (𝓝 1) := by
    intro i j
    have h := tendsto_stokesOdd_log_normalized hg hL (hgap i) (hgap j)
    refine h.congr' (Eventually.of_forall fun k => ?_)
    dsimp only
    rw [routeRCrossPrimeStokesOddCurvature_log_form (hprime k i).one_lt (hprime k j).one_lt hg]
  have hlim : Tendsto M atTop (𝓝 S) := by
    refine tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j => ?_
    simp only [M, S, Matrix.smul_apply, orderedStokesMatrix, Matrix.of_apply, Matrix.map_apply,
      orderSignMatrix, smul_eq_mul]
    rcases lt_trichotomy i j with hij | hij | hij
    · simp only [if_pos hij]
      simpa using hone i j
    · subst hij
      simp
    · simp only [if_neg (not_lt.mpr hij.le), if_pos hij]
      simpa [mul_neg] using (hone j i).neg
  have hdetlim : Tendsto (fun k => (M k).det) atTop (𝓝 S.det) :=
    ((continuous_id.matrix_det).tendsto S).comp hlim
  have hdet0 : S.det ≠ 0 := det_orderSignMatrix_real_ne_zero hn
  obtain ⟨K, hK⟩ := eventually_atTop.mp
    ((hdetlim.eventually (isOpen_ne.mem_nhds hdet0)).and
      (hL.eventually_gt_atTop 0))
  obtain ⟨hdetK, hLK⟩ := hK K le_rfl
  refine ⟨fun i => P K i, fun a b hab => hmono K hab, fun i => hprime K i, fun i => ?_, ?_⟩
  · have h0 : (N : ℝ) < P K 0 := lt_of_le_of_lt (by exact_mod_cast le_max_left N K) (hbig K)
    have : P K 0 ≤ P K i := (hmono K).monotone (Nat.zero_le _)
    exact lt_of_lt_of_le (by exact_mod_cast h0) this
  · have hc : (-4 * Real.sinh (g * Real.log (P K 0)))⁻¹ ≠ 0 := by
      apply inv_ne_zero
      apply mul_ne_zero (by norm_num)
      rw [Real.sinh_ne_zero]
      exact mul_ne_zero hg hLK.ne'
    have hunit : IsUnit (orderedStokesMatrix (fun i : Fin n => P K i) g).det := by
      rw [isUnit_iff_ne_zero]
      intro h0
      apply hdetK
      simp only [M, Matrix.det_smul, h0, mul_zero]
    have := Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).mpr hunit)
    simpa using this

/-- **No fixed finite alternating channel representation.** At a nonzero grade the ordered
curvature is not the matrix of an alternating bilinear form on a fixed `k`-dimensional channel
space evaluated on one-prime sections. -/
theorem no_finite_alternating_stokes_channels {g : ℝ} (hg : g ≠ 0) (k : ℕ) :
    ¬∃ (φ : ℕ → Fin k → ℝ) (B : Matrix (Fin k) (Fin k) ℝ), Bᵀ = -B ∧
      ∀ p q : ℕ, p.Prime → q.Prime → p < q →
        routeRCrossPrimeStokesOddCurvature p q g = φ p ⬝ᵥ B.mulVec (φ q) := by
  rintro ⟨φ, B, halt, hrep⟩
  obtain ⟨p, hmono, hprime, -, hrank⟩ :=
    exists_prime_packet_orderedStokesMatrix_rank hg (n := 2 * (k + 1)) (even_two_mul _) 0
  let Φ : Matrix (Fin (2 * (k + 1))) (Fin k) ℝ := Matrix.of fun i t => φ (p i) t
  have hskew : ∀ x : Fin k → ℝ, x ⬝ᵥ B.mulVec x = 0 := by
    intro x
    have h1 : x ⬝ᵥ B.mulVec x = x ⬝ᵥ Bᵀ.mulVec x := by
      rw [Matrix.dotProduct_mulVec, Matrix.mulVec_transpose, dotProduct_comm]
    rw [halt, Matrix.neg_mulVec, dotProduct_neg] at h1
    linarith
  have hswap : ∀ x y : Fin k → ℝ, y ⬝ᵥ B.mulVec x = -(x ⬝ᵥ B.mulVec y) := by
    intro x y
    have := hskew (x + y)
    simp only [Matrix.mulVec_add, dotProduct_add, add_dotProduct, hskew x, hskew y] at this
    linarith
  have hfac : orderedStokesMatrix p g = Φ * B * Φᵀ := by
    ext i j
    simp only [orderedStokesMatrix, Matrix.of_apply, Matrix.mul_apply, Φ, Matrix.transpose_apply]
    have hform : ∀ a b : Fin (2 * (k + 1)),
        ∑ x, (∑ t, φ (p a) t * B t x) * φ (p b) x = φ (p a) ⬝ᵥ B.mulVec (φ (p b)) := by
      intro a b
      simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun t _ => ?_
      ring
    rw [hform]
    rcases lt_trichotomy i j with hij | hij | hij
    · rw [if_pos hij, hrep _ _ (hprime i) (hprime j) (hmono hij)]
    · subst hij
      simp [hskew]
    · rw [if_neg (not_lt.mpr hij.le), if_pos hij, hrep _ _ (hprime j) (hprime i) (hmono hij),
        hswap, neg_neg]
  have hle : (orderedStokesMatrix p g).rank ≤ k := by
    rw [hfac]
    calc (Φ * B * Φᵀ).rank ≤ (Φ * B).rank := Matrix.rank_mul_le_left _ _
      _ ≤ Φ.rank := Matrix.rank_mul_le_left _ _
      _ ≤ Fintype.card (Fin k) := Matrix.rank_le_card_width Φ
      _ = k := Fintype.card_fin k
  rw [hrank] at hle
  omega

end

end RHTower
