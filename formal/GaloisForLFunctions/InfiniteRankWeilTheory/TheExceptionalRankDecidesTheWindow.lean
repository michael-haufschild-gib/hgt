import GaloisForLFunctions.InfiniteRankWeilTheory.TheLevelSumsOfAWeilTower

/-!
# The exceptional rank decides the window

Turán's second main theorem bounds a power sum of `N` terms from below on every window of `N`
consecutive exponents, with constants decaying like `(NM)^{−N}`. At infinite rank such a statement is
void. What survives is a statement in which only the **exceptional rank** enters: the number of
distinct visible points of maximal modulus. The remainder below the top, of any rank, enters only
through its trace norm.

* `exists_pos_forall_window_le_norm_expSum`: distinct unimodular points `p_j` with coefficients
  `c ≠ 0` give `|Σ c_j p_jᵛ| ≥ ε` at some level of every window of `k` consecutive levels, `ε > 0`
  independent of the window (inverse Vandermonde matrix).
* `exists_pos_forall_window_le_norm_levelSum`: a tower with a finite top set `F` whose visible points
  have modulus `R`, and a remainder of modulus `≤ r` and any rank, satisfies
  `|S(ν)| ≥ εRᵛ − (Σ|b|) rᵛ` at some level of every window of `#F` levels.
* `eventually_forall_window_exists_lt_norm_levelSum`: if `r < R`, every rate `ρ < R` is exceeded at
  some level of every window of `#F` levels beyond some point: the excursion set is syndetic with gap
  the exceptional rank.
* `not_forall_mem_thick_norm_levelSum_le`: hence no **thick** set of levels (one containing
  arbitrarily long runs arbitrarily far out) carries a bound `Cρᵛ` with `ρ < R`. A crude bound on a
  thick set of levels self-improves past every isolated visible top.
* `le_tsum_norm_of_levelSum_eq_zero_on_window`: a remainder of modulus `≤ 1` that cancels the level
  sums on a window at position `M` has trace norm `≥ εR^{M+1}`: the price of hiding a top grows
  exponentially with the position of the window.
-/

open Complex Finset Filter Topology

noncomputable section

namespace GaloisForLFunctions.InfiniteRankWeilTheory

/-! ### Window visibility of a finite exponential polynomial -/

/-- **Vandermonde window bound.** For distinct unimodular points and coefficients `c ≠ 0`, every
window of `k` consecutive levels has a level with `|Σ_j c_j p_jᵛ| ≥ ε`, `ε` independent of the
window. -/
theorem exists_pos_forall_window_le_norm_expSum {k : ℕ} (p : Fin k → ℂ)
    (hp : Function.Injective p) (hunit : ∀ j, ‖p j‖ = 1) (c : Fin k → ℂ) (hc : c ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ M : ℕ, ∃ m : Fin k, ε ≤ ‖∑ j, c j * p j ^ (M + 1 + (m : ℕ))‖ := by
  classical
  obtain ⟨j₀, hj₀⟩ : ∃ j₀, c j₀ ≠ 0 := by
    by_contra h
    push Not at h
    exact hc (funext h)
  set V : Matrix (Fin k) (Fin k) ℂ := Matrix.transpose (Matrix.vandermonde p) with hV
  have hdet : IsUnit V.det := by
    rw [hV, Matrix.det_transpose]
    exact isUnit_iff_ne_zero.mpr (Matrix.det_vandermonde_ne_zero_iff.mpr hp)
  set K : ℝ := ∑ m, ‖V⁻¹ j₀ m‖ with hK
  have hK0 : 0 ≤ K := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hcpos : 0 < ‖c j₀‖ := norm_pos_iff.mpr hj₀
  refine ⟨‖c j₀‖ / (K + 1), by positivity, fun M => ?_⟩
  by_contra hcon
  push Not at hcon
  set x : Fin k → ℂ := fun j => c j * p j ^ (M + 1) with hx
  have hy : ∀ m : Fin k, V.mulVec x m = ∑ j, c j * p j ^ (M + 1 + (m : ℕ)) := by
    intro m
    simp only [Matrix.mulVec, dotProduct, hV, Matrix.transpose_apply, Matrix.vandermonde_apply,
      hx]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [pow_add]
    ring
  have hxW : x j₀ = (V⁻¹.mulVec (V.mulVec x)) j₀ := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul V hdet, Matrix.one_mulVec]
  have hxj : ‖x j₀‖ = ‖c j₀‖ := by
    simp [hx, norm_pow, hunit]
  have hle : ‖x j₀‖ ≤ K * (‖c j₀‖ / (K + 1)) := by
    rw [hxW]
    simp only [Matrix.mulVec, dotProduct]
    calc ‖∑ m, V⁻¹ j₀ m * V.mulVec x m‖ ≤ ∑ m, ‖V⁻¹ j₀ m * V.mulVec x m‖ := norm_sum_le _ _
      _ ≤ ∑ m, ‖V⁻¹ j₀ m‖ * (‖c j₀‖ / (K + 1)) := by
          refine Finset.sum_le_sum fun m _ => ?_
          rw [norm_mul, hy m]
          exact mul_le_mul_of_nonneg_left (hcon m).le (norm_nonneg _)
      _ = K * (‖c j₀‖ / (K + 1)) := by rw [← Finset.sum_mul]
  have hlt : K * (‖c j₀‖ / (K + 1)) < ‖c j₀‖ := by
    rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith
  linarith

/-- **Window bound for a finite point measure.** If every point `q ∈ P` with `c q ≠ 0` has modulus
`R`, and some point has `c q ≠ 0`, then `|Σ_{q∈P} c q qᵛ| ≥ εRᵛ` at some level of every window
`[M+1, M+#P]`. -/
theorem exists_pos_forall_window_le_norm_pointSum (P : Finset ℂ) (c : ℂ → ℂ) {R : ℝ}
    (hR : 0 < R) (htop : ∀ q ∈ P, c q ≠ 0 → ‖q‖ = R) (hvis : ∃ q ∈ P, c q ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ M : ℕ, ∃ ν : ℕ, M + 1 ≤ ν ∧ ν ≤ M + P.card ∧
      ε * R ^ ν ≤ ‖∑ q ∈ P, c q * q ^ ν‖ := by
  classical
  set P' := P.filter (fun q => c q ≠ 0) with hP'
  set e : Fin P'.card ≃ P' := P'.equivFin.symm with he
  have hRc : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  set p : Fin P'.card → ℂ := fun j => (e j : ℂ) / R with hpdef
  have hmem : ∀ j, (e j : ℂ) ∈ P ∧ c (e j) ≠ 0 := fun j => mem_filter.1 (e j).2
  have hp : Function.Injective p := by
    intro a b h
    have h' : (e a : ℂ) = (e b : ℂ) := by
      have := congrArg (· * (R : ℂ)) h
      simpa [hpdef, div_mul_cancel₀ _ hRc] using this
    exact e.injective (Subtype.ext h')
  have hunit : ∀ j, ‖p j‖ = 1 := by
    intro j
    rw [hpdef, norm_div, Complex.norm_real, Real.norm_of_nonneg hR.le,
      htop _ (hmem j).1 (hmem j).2, div_self hR.ne']
  have hcc : (fun j => c (e j)) ≠ 0 := by
    obtain ⟨q, hq, hcq⟩ := hvis
    intro h0
    have := congrFun h0 (e.symm ⟨q, mem_filter.2 ⟨hq, hcq⟩⟩)
    simp only [Equiv.apply_symm_apply, Pi.zero_apply] at this
    exact hcq this
  obtain ⟨ε, hε, hwin⟩ := exists_pos_forall_window_le_norm_expSum p hp hunit _ hcc
  refine ⟨ε, hε, fun M => ?_⟩
  obtain ⟨m, hm⟩ := hwin M
  have hmk : (m : ℕ) < P'.card := m.2
  have hP'P : P'.card ≤ P.card := card_filter_le _ _
  refine ⟨M + 1 + m, by omega, by omega, ?_⟩
  have hsum : ∑ q ∈ P, c q * q ^ (M + 1 + (m : ℕ)) =
      (R : ℂ) ^ (M + 1 + (m : ℕ)) * ∑ j, c (e j) * p j ^ (M + 1 + (m : ℕ)) := by
    rw [← Finset.sum_filter_of_ne (p := fun q => c q ≠ 0)
      (fun q _ hq => left_ne_zero_of_mul hq), ← hP', ← Finset.sum_coe_sort P',
      ← Equiv.sum_comp e, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hej : (e j : ℂ) = R * p j := by rw [hpdef, mul_div_cancel₀ _ hRc]
    rw [hej, mul_pow]
    ring
  rw [hsum, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hR.le, mul_comm]
  exact mul_le_mul_of_nonneg_left hm (pow_nonneg hR.le _)

/-! ### Towers with an isolated top -/

/-- Fibre decomposition of the top part of a level sum over the points of `F`. -/
theorem sum_mul_pow_eq_sum_image {ι : Type*} (z b : ι → ℂ) (F : Finset ι) (ν : ℕ) :
    ∑ i ∈ F, b i * z i ^ ν = ∑ w ∈ F.image z, (∑ j ∈ F with z j = w, b j) * w ^ ν := by
  rw [← Finset.sum_fiberwise_of_maps_to (s := F) (t := F.image z) (g := z)
    (fun i hi => mem_image_of_mem z hi)]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [(mem_filter.1 hj).2]

/-- **Isolated-top window bound at infinite rank.** A finite top set `F` whose visible points (nonzero
merged weight) all have modulus `R`, over a remainder of modulus `≤ r` and arbitrary rank:
`|S(ν)| ≥ εRᵛ − (Σ|b|) rᵛ` at some level of every window of `#F` consecutive levels. -/
theorem exists_pos_forall_window_le_norm_levelSum {ι : Type*} (z b : ι → ℂ)
    (hb : Summable fun i => ‖b i‖) (F : Finset ι) {R r : ℝ} (hR : 0 < R) (hr : 0 ≤ r)
    (hrest : ∀ i ∉ F, ‖z i‖ ≤ r)
    (htop : ∀ i ∈ F, (∑ j ∈ F with z j = z i, b j) ≠ 0 → ‖z i‖ = R)
    (hvis : ∃ i ∈ F, (∑ j ∈ F with z j = z i, b j) ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ M : ℕ, ∃ ν : ℕ, M + 1 ≤ ν ∧ ν ≤ M + F.card ∧
      ε * R ^ ν - (∑' i, ‖b i‖) * r ^ ν ≤ ‖levelSum z b ν‖ := by
  classical
  set c : ℂ → ℂ := fun w => ∑ j ∈ F with z j = w, b j with hc
  have htop' : ∀ w ∈ F.image z, c w ≠ 0 → ‖w‖ = R := by
    intro w hw hcw
    obtain ⟨i, hi, rfl⟩ := mem_image.1 hw
    exact htop i hi hcw
  have hvis' : ∃ w ∈ F.image z, c w ≠ 0 := by
    obtain ⟨i, hi, hci⟩ := hvis
    exact ⟨z i, mem_image_of_mem z hi, hci⟩
  obtain ⟨ε, hε, hwin⟩ := exists_pos_forall_window_le_norm_pointSum _ c hR htop' hvis'
  refine ⟨ε, hε, fun M => ?_⟩
  obtain ⟨ν, h1, h2, h3⟩ := hwin M
  refine ⟨ν, h1, h2.trans (by have := card_image_le (s := F) (f := z); omega), ?_⟩
  -- the modes are bounded, so the level sum splits into top and remainder
  set B : ℝ := r + ∑ i ∈ F, ‖z i‖ with hB
  have hzB : ∀ i, ‖z i‖ ≤ B := by
    intro i
    by_cases hi : i ∈ F
    · exact le_add_of_nonneg_of_le hr (single_le_sum (fun j _ => norm_nonneg (z j)) hi)
    · exact (hrest i hi).trans (le_add_of_nonneg_right (sum_nonneg fun j _ => norm_nonneg _))
  have hbound : ∀ i, ‖b i * z i ^ (ν : ℤ)‖ ≤ ‖b i‖ * B ^ ν := fun i => by
    rw [norm_mul, zpow_natCast, norm_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hzB i) ν) (norm_nonneg _)
  have hsn : Summable fun i => ‖b i * z i ^ (ν : ℤ)‖ :=
    (hb.mul_right (B ^ ν)).of_nonneg_of_le (fun _ => norm_nonneg _) hbound
  have hsplit := (hsn.of_norm.sum_add_tsum_compl (s := F)).symm
  set top := ∑ i ∈ F, b i * z i ^ (ν : ℤ) with htopdef
  set rest := ∑' i : ↑((F : Set ι)ᶜ), b i * z i ^ (ν : ℤ) with hrestdef
  have htopeq : top = ∑ q ∈ F.image z, c q * q ^ ν := by
    rw [htopdef, ← sum_mul_pow_eq_sum_image]
    exact Finset.sum_congr rfl fun i _ => by rw [zpow_natCast]
  have hrestle : ‖rest‖ ≤ (∑' i, ‖b i‖) * r ^ ν := by
    have hrb : ∀ i : ↑((F : Set ι)ᶜ), ‖b i * z i ^ (ν : ℤ)‖ ≤ ‖b i‖ * r ^ ν := fun i => by
      have hi : (i : ι) ∉ F := fun h => i.2 (Finset.mem_coe.2 h)
      rw [norm_mul, zpow_natCast, norm_pow]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hrest _ hi) ν)
        (norm_nonneg _)
    have hbs : Summable fun i : ↑((F : Set ι)ᶜ) => ‖b i‖ * r ^ ν :=
      (hb.subtype _).mul_right _
    calc ‖rest‖ ≤ ∑' i : ↑((F : Set ι)ᶜ), ‖b i * z i ^ (ν : ℤ)‖ :=
          norm_tsum_le_tsum_norm (hsn.subtype _)
      _ ≤ ∑' i : ↑((F : Set ι)ᶜ), ‖b i‖ * r ^ ν := (hsn.subtype _).tsum_le_tsum hrb hbs
      _ = (∑' i : ↑((F : Set ι)ᶜ), ‖b i‖) * r ^ ν := tsum_mul_right
      _ ≤ (∑' i, ‖b i‖) * r ^ ν :=
          mul_le_mul_of_nonneg_right
            (Summable.tsum_subtype_le (fun i => ‖b i‖) _ (fun _ => norm_nonneg _) hb)
            (pow_nonneg hr _)
  have hS : levelSum z b ν = top + rest := hsplit
  have htri := norm_sub_le (top + rest) rest
  rw [add_sub_cancel_right] at htri
  have h3' : ε * R ^ ν ≤ ‖top‖ := by rw [htopeq]; exact h3
  rw [hS]
  linarith

/-! ### Self-improvement on windows and thick sets -/

/-- **The excursion set is syndetic with gap the exceptional rank.** Under an isolated visible top
(`r < R`), every rate `ρ < R` and constant `C` are exceeded at some level of every window of `#F`
consecutive levels beyond some point. -/
theorem eventually_forall_window_exists_lt_norm_levelSum {ι : Type*} (z b : ι → ℂ)
    (hb : Summable fun i => ‖b i‖) (F : Finset ι) {R r : ℝ} (hR : 0 < R) (hr : 0 ≤ r)
    (hrR : r < R) (hrest : ∀ i ∉ F, ‖z i‖ ≤ r)
    (htop : ∀ i ∈ F, (∑ j ∈ F with z j = z i, b j) ≠ 0 → ‖z i‖ = R)
    (hvis : ∃ i ∈ F, (∑ j ∈ F with z j = z i, b j) ≠ 0) {ρ C : ℝ} (hρ : 0 ≤ ρ) (hρR : ρ < R) :
    ∃ M₀ : ℕ, ∀ M, M₀ ≤ M → ∃ ν : ℕ, M + 1 ≤ ν ∧ ν ≤ M + F.card ∧
      C * ρ ^ ν < ‖levelSum z b ν‖ := by
  obtain ⟨ε, hε, hwin⟩ := exists_pos_forall_window_le_norm_levelSum z b hb F hR hr hrest htop hvis
  set W : ℝ := ∑' i, ‖b i‖ with hW
  have hW0 : 0 ≤ W := tsum_nonneg fun _ => norm_nonneg _
  set C' : ℝ := max C 0 with hC'
  set q : ℝ := max r ρ / R with hq
  have hq0 : 0 ≤ q := div_nonneg (le_max_of_le_left hr) hR.le
  have hq1 : q < 1 := by rw [hq, div_lt_one hR]; exact max_lt hrR hρR
  have hlim : Tendsto (fun n : ℕ => (W + C') * q ^ n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).const_mul (W + C')
  obtain ⟨M₀, hM₀⟩ := (hlim.eventually (gt_mem_nhds hε)).exists_forall_of_atTop
  refine ⟨M₀, fun M hM => ?_⟩
  obtain ⟨ν, h1, h2, h3⟩ := hwin M
  refine ⟨ν, h1, h2, ?_⟩
  have hqR : max r ρ = q * R := by rw [hq, div_mul_cancel₀ _ hR.ne']
  have hsmall : (W + C') * q ^ ν < ε := hM₀ ν (by omega)
  have hRν : 0 < R ^ ν := pow_pos hR ν
  have hr' : r ^ ν ≤ q ^ ν * R ^ ν := by
    rw [← mul_pow, ← hqR]; exact pow_le_pow_left₀ hr (le_max_left _ _) ν
  have hρ' : ρ ^ ν ≤ q ^ ν * R ^ ν := by
    rw [← mul_pow, ← hqR]; exact pow_le_pow_left₀ hρ (le_max_right _ _) ν
  have hC1 : C * ρ ^ ν ≤ C' * ρ ^ ν :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hρ _)
  have hC2 : C' * ρ ^ ν ≤ C' * (q ^ ν * R ^ ν) :=
    mul_le_mul_of_nonneg_left hρ' (le_max_right _ _)
  have hW2 : W * r ^ ν ≤ W * (q ^ ν * R ^ ν) := mul_le_mul_of_nonneg_left hr' hW0
  have hfin : (W + C') * q ^ ν * R ^ ν < ε * R ^ ν := mul_lt_mul_of_pos_right hsmall hRν
  nlinarith

/-- A set of levels is **thick** if it contains arbitrarily long runs arbitrarily far out. -/
def Thick (G : Set ℕ) : Prop :=
  ∀ L N : ℕ, ∃ M, N ≤ M ∧ ∀ ν, M + 1 ≤ ν → ν ≤ M + L → ν ∈ G

theorem thick_univ : Thick Set.univ := fun _ N => ⟨N, le_rfl, fun _ _ _ => Set.mem_univ _⟩

/-- Every cofinite set of levels is thick. -/
theorem thick_Ici (n₀ : ℕ) : Thick (Set.Ici n₀) :=
  fun _ N => ⟨max N n₀, le_max_left _ _, fun ν h _ => by
    simp only [Set.mem_Ici]; have := le_max_right N n₀; omega⟩

/-- **Thick sets self-improve.** No thick set of levels carries a bound `|S(ν)| ≤ Cρᵛ` with `ρ < R`
above an isolated visible top of modulus `R`. -/
theorem not_forall_mem_thick_norm_levelSum_le {ι : Type*} (z b : ι → ℂ)
    (hb : Summable fun i => ‖b i‖) (F : Finset ι) {R r : ℝ} (hR : 0 < R) (hr : 0 ≤ r)
    (hrR : r < R) (hrest : ∀ i ∉ F, ‖z i‖ ≤ r)
    (htop : ∀ i ∈ F, (∑ j ∈ F with z j = z i, b j) ≠ 0 → ‖z i‖ = R)
    (hvis : ∃ i ∈ F, (∑ j ∈ F with z j = z i, b j) ≠ 0) {ρ C : ℝ} (hρ : 0 ≤ ρ) (hρR : ρ < R)
    {G : Set ℕ} (hG : Thick G) : ¬ ∀ ν ∈ G, ‖levelSum z b ν‖ ≤ C * ρ ^ ν := by
  intro hbd
  obtain ⟨M₀, hM₀⟩ := eventually_forall_window_exists_lt_norm_levelSum z b hb F hR hr hrR hrest
    htop hvis (C := C) hρ hρR
  obtain ⟨M, hM, hwin⟩ := hG F.card M₀
  obtain ⟨ν, h1, h2, h3⟩ := hM₀ M hM
  exact absurd (hbd ν (hwin ν h1 h2)) (not_le.mpr h3)

/-- **The price of hiding a top.** A remainder of modulus `≤ 1` that makes the level sums vanish on
the window `[M+1, M+#F]` has trace norm at least `εR^{M+1}`, with `ε > 0` depending only on the top
layer. -/
theorem exists_pos_forall_window_vanish_le_tsum_norm {ι : Type*} (z b : ι → ℂ)
    (hb : Summable fun i => ‖b i‖) (F : Finset ι) {R : ℝ} (hR : 1 ≤ R)
    (hrest : ∀ i ∉ F, ‖z i‖ ≤ 1)
    (htop : ∀ i ∈ F, (∑ j ∈ F with z j = z i, b j) ≠ 0 → ‖z i‖ = R)
    (hvis : ∃ i ∈ F, (∑ j ∈ F with z j = z i, b j) ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ M : ℕ, (∀ ν, M + 1 ≤ ν → ν ≤ M + F.card → levelSum z b ν = 0) →
      ε * R ^ (M + 1) ≤ ∑' i, ‖b i‖ := by
  obtain ⟨ε, hε, hwin⟩ := exists_pos_forall_window_le_norm_levelSum z b hb F
    (by linarith) zero_le_one hrest htop hvis
  refine ⟨ε, hε, fun M hvan => ?_⟩
  obtain ⟨ν, h1, h2, h3⟩ := hwin M
  rw [hvan ν h1 h2, norm_zero, one_pow, mul_one] at h3
  calc ε * R ^ (M + 1) ≤ ε * R ^ ν :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hR h1) hε.le
    _ ≤ ∑' i, ‖b i‖ := by linarith

end GaloisForLFunctions.InfiniteRankWeilTheory
