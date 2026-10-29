import GaloisForLFunctions.HeckeKreinToeplitz.HyperbolicPairsAndTheIndexFormula

/-!
# Growth reads the depth of the deepest pair

Along a separating element `u`, a Krein–Langer kernel `k = p + Σ_j h_{χ_j,ω_j}` is the bounded
positive-definite part plus the exponential sum `Σ_j (ω_j w_j^n + ω̄_j w_j^{†n})` over the `2κ` nodes
`w_j = χ_j(u)`, `w_j^† = 1/w̄_j`. Its growth is the modulus of the deepest node.

**Non-cancellation at the top modulus** (`coeff_eq_zero_of_tendsto_zero`). A sum `Σ_i c_i ζ_i^n` of
distinct unimodular frequencies that tends to `0` has all coefficients zero: the vector of `m`
consecutive values is the transposed Vandermonde matrix applied to `(c_i ζ_i^n)_i`, whose entries
have constant modulus.

**Growth bound** (`coeff_eq_zero_of_norm_le`). If `|Σ_i c_i ν_i^n| ≤ M r^n` for distinct `ν_i`, then
`c_i = 0` whenever `|ν_i| > r`: divide by the largest modulus carrying a nonzero coefficient.

**Self-upgrade** (`card_eq_zero_of_bounded`, `isPosDefKernel_of_bounded`). A Krein–Langer kernel
separated at `u` and bounded along `u^n` has no pair: it is positive definite. A pair is never
hidden by boundedness; it always shows as exponential growth.

**Growth reads depth** (`not_norm_le_of_lt_depth`). If `R` is the largest node modulus, then
`|k(u^n)| ≤ C R^n`, and for every `r < R` no bound `M r^n` holds.
-/

open Complex Matrix Finset Filter Topology
open scoped ComplexConjugate
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace GaloisForLFunctions.HeckeKreinToeplitz

/-! ### Exponential sums -/

/-- **Non-cancellation of unimodular exponential sums.** -/
theorem coeff_eq_zero_of_tendsto_zero {m : ℕ} {ζ : Fin m → ℂ} (hζ : ∀ i, ‖ζ i‖ = 1)
    (hinj : Function.Injective ζ) (c : Fin m → ℂ)
    (h : Tendsto (fun n : ℕ => ∑ i, c i * ζ i ^ n) atTop (𝓝 0)) : c = 0 := by
  set V : Matrix (Fin m) (Fin m) ℂ := (vandermonde ζ)ᵀ
  have hdet : V.det ≠ 0 := by
    rw [det_transpose]; exact det_vandermonde_ne_zero_iff.mpr hinj
  set y : ℕ → Fin m → ℂ := fun n i => c i * ζ i ^ n
  have hA : ∀ n, V *ᵥ y n = fun j : Fin m => ∑ i, c i * ζ i ^ (n + (j : ℕ)) := fun n => by
    funext j
    simp only [V, y, mulVec, dotProduct, transpose_apply, vandermonde_apply, pow_add]
    exact sum_congr rfl fun i _ => by ring
  have hAt : Tendsto (fun n => V *ᵥ y n) atTop (𝓝 0) := by
    refine tendsto_pi_nhds.mpr fun j => ?_
    simp only [hA, Pi.zero_apply]
    exact h.comp (tendsto_add_atTop_nat j)
  have hy : ∀ n, y n = V⁻¹ *ᵥ (V *ᵥ y n) := fun n => by
    rw [mulVec_mulVec, nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet), one_mulVec]
  have hyt : Tendsto y atTop (𝓝 0) := by
    have := ((continuous_const (y := V⁻¹).matrix_mulVec continuous_id).tendsto
      (0 : Fin m → ℂ)).comp hAt
    simp only [Function.comp_def, id, mulVec_zero] at this
    exact this.congr fun n => (hy n).symm
  funext i
  have hi := (tendsto_pi_nhds.mp hyt i).norm
  have hconst : (fun n => ‖y n i‖) = fun _ => ‖c i‖ := by
    funext n; simp only [y, norm_mul, norm_pow, hζ, one_pow, mul_one]
  rw [hconst, Pi.zero_apply, norm_zero] at hi
  exact norm_eq_zero.mp (tendsto_nhds_unique tendsto_const_nhds hi)

/-- The non-cancellation lemma over any finite index type. -/
theorem coeff_eq_zero_of_tendsto_zero' {ι : Type*} [Fintype ι] {ζ : ι → ℂ}
    (hζ : ∀ i, ‖ζ i‖ = 1) (hinj : Function.Injective ζ) (c : ι → ℂ)
    (h : Tendsto (fun n : ℕ => ∑ i, c i * ζ i ^ n) atTop (𝓝 0)) : c = 0 := by
  set e := Fintype.equivFin ι
  have h' : Tendsto (fun n : ℕ => ∑ j, (c ∘ e.symm) j * (ζ ∘ e.symm) j ^ n) atTop (𝓝 0) := by
    refine h.congr fun n => ?_
    exact (e.symm.sum_comp (fun i => c i * ζ i ^ n)).symm
  have := coeff_eq_zero_of_tendsto_zero (fun j => hζ _) (hinj.comp e.symm.injective) _ h'
  funext i
  simpa using congrFun this (e i)

/-- **Growth bound.** If `|Σ_i c_i ν_i^n| ≤ M r^n` for distinct `ν_i`, every coefficient at a
node of modulus `> r` vanishes. -/
theorem coeff_eq_zero_of_norm_le {ι : Type*} [Fintype ι] {ν : ι → ℂ}
    (hinj : Function.Injective ν) (c : ι → ℂ) {r M : ℝ} (hr : 0 < r)
    (h : ∀ n : ℕ, ‖∑ i, c i * ν i ^ n‖ ≤ M * r ^ n) {i : ι} (hi : r < ‖ν i‖) : c i = 0 := by
  classical
  by_contra hci
  set T := univ.filter fun j => c j ≠ 0 ∧ r < ‖ν j‖
  obtain ⟨i₀, hi₀T, hmax⟩ := T.exists_max_image (fun j => ‖ν j‖)
    ⟨i, mem_filter.mpr ⟨mem_univ _, hci, hi⟩⟩
  set R := ‖ν i₀‖
  have hrR : r < R := (mem_filter.mp hi₀T).2.2
  have hR : 0 < R := hr.trans hrR
  have hle : ∀ j, c j ≠ 0 → ‖ν j‖ ≤ R := fun j hj => by
    by_cases hjr : r < ‖ν j‖
    · exact hmax j (mem_filter.mpr ⟨mem_univ _, hj, hjr⟩)
    · exact (not_lt.mp hjr).trans hrR.le
  set top := univ.filter fun j => ‖ν j‖ = R
  -- the normalized top part tends to zero
  have hsplit : ∀ n : ℕ, (∑ j, c j * ν j ^ n) / (R : ℂ) ^ n =
      ∑ j ∈ top, c j * (ν j / R) ^ n + ∑ j ∈ univ.filter (fun j => ¬ ‖ν j‖ = R),
        c j * (ν j / R) ^ n := fun n => by
    rw [sum_filter_add_sum_filter_not, sum_div]
    exact sum_congr rfl fun j _ => by rw [div_pow]; ring
  have hlow : Tendsto (fun n : ℕ => ∑ j ∈ univ.filter (fun j => ¬ ‖ν j‖ = R),
      c j * (ν j / R) ^ n) atTop (𝓝 0) := by
    have := tendsto_finsetSum (univ.filter fun j => ¬ ‖ν j‖ = R)
      (f := fun j (n : ℕ) => c j * (ν j / R) ^ n) (x := atTop) (a := fun _ => 0) fun j hj => by
        by_cases hcj : c j = 0
        · simp only [hcj, zero_mul]; exact tendsto_const_nhds
        · have hlt : ‖ν j / R‖ < 1 := by
            rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hR.le, div_lt_one hR]
            exact lt_of_le_of_ne (hle j hcj) (mem_filter.mp hj).2
          simpa using (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hlt).const_mul (c j)
    simpa using this
  have hfull : Tendsto (fun n : ℕ => (∑ j, c j * ν j ^ n) / (R : ℂ) ^ n) atTop (𝓝 0) := by
    refine squeeze_zero_norm (a := fun n : ℕ => M * (r / R) ^ n) (fun n => ?_) (by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity)
        ((div_lt_one hR).mpr hrR)).const_mul M)
    rw [norm_div, norm_pow, Complex.norm_real, Real.norm_of_nonneg hR.le, div_pow,
      div_le_iff₀ (by positivity)]
    calc ‖∑ j, c j * ν j ^ n‖ ≤ M * r ^ n := h n
      _ = M * (r ^ n / R ^ n) * R ^ n := by field_simp
  have htop : Tendsto (fun n : ℕ => ∑ j ∈ top, c j * (ν j / R) ^ n) atTop (𝓝 0) := by
    have := hfull.sub hlow
    simp only [sub_zero] at this
    exact this.congr fun n => by rw [hsplit]; ring
  -- non-cancellation on the top modulus
  have hz := coeff_eq_zero_of_tendsto_zero' (ι := top) (ζ := fun j => ν j / R)
    (fun j => by rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hR.le,
      (mem_filter.mp j.2).2, div_self hR.ne'])
    (fun j k hjk => Subtype.ext (hinj (by
      have := congrArg (· * (R : ℂ)) hjk
      simpa [div_mul_cancel₀, Complex.ofReal_ne_zero.mpr hR.ne'] using this)))
    (fun j => c j) (htop.congr fun n => (top.sum_coe_sort (fun j => c j * (ν j / R) ^ n)).symm)
  exact (mem_filter.mp hi₀T).2.1 (congrFun hz ⟨i₀, mem_filter.mpr ⟨mem_univ _, rfl⟩⟩)

/-! ### Krein–Langer kernels along a separating element -/

variable {G : Type*} [Group G] {κ : ℕ}

/-- The coefficient of a node: `ω_j` at `w_j`, `ω̄_j` at `w_j^†`. -/
def nodeCoeff (ω : Fin κ → ℂ) : Fin κ ⊕ Fin κ → ℂ := Sum.elim ω fun j => conj (ω j)

/-- Along `u^n` the pairs are an exponential sum over the nodes. -/
theorem sum_pairKernel_pow (χ : Fin κ → G →* ℂ) (ω : Fin κ → ℂ) (u : G) (n : ℕ) :
    ∑ j, pairKernel (χ j) (ω j) (u ^ n) = ∑ m, nodeCoeff ω m * nodes χ u m ^ n := by
  rw [Fintype.sum_sum_type, ← sum_add_distrib]
  refine sum_congr rfl fun j _ => ?_
  simp only [pairKernel, map_pow, nodeCoeff, nodes, Sum.elim_inl, Sum.elim_inr]

/-- Every pair has a node of modulus `> 1` with nonzero coefficient. -/
theorem exists_outer_node {χ : Fin κ → G →* ℂ} {ω : Fin κ → ℂ} (hω : ∀ j, ω j ≠ 0) {u : G}
    (hne : ∀ j, ‖χ j u‖ ≠ 1) (j : Fin κ) :
    ∃ m, 1 < ‖nodes χ u m‖ ∧ nodeCoeff ω m ≠ 0 := by
  rcases lt_or_gt_of_ne (hne j) with h | h
  · refine ⟨Sum.inr j, ?_, (star_ne_zero).mpr (hω j)⟩
    simp only [nodes, Sum.elim_inr, norm_reflectChar]
    exact one_lt_inv₀ (norm_pos_iff.mpr (map_ne_zero _ _)) |>.mpr h
  · exact ⟨Sum.inl j, h, hω j⟩

/-- **Self-upgrade.** A Krein–Langer kernel separated at `u` and bounded along `u^n` has no pair. -/
theorem card_eq_zero_of_bounded {p : G → ℂ} (hp : IsPosDefKernel p) (χ : Fin κ → G →* ℂ)
    (ω : Fin κ → ℂ) (hω : ∀ j, ω j ≠ 0) (u : G) (hne : ∀ j, ‖χ j u‖ ≠ 1)
    (hsep : Function.Injective (nodes χ u))
    (hb : ∃ M, ∀ n : ℕ, ‖p (u ^ n) + ∑ j, pairKernel (χ j) (ω j) (u ^ n)‖ ≤ M) : κ = 0 := by
  obtain ⟨M, hM⟩ := hb
  by_contra hκ
  obtain ⟨m, hm1, hm0⟩ := exists_outer_node hω hne ⟨0, Nat.pos_of_ne_zero hκ⟩
  refine hm0 (coeff_eq_zero_of_norm_le hsep (nodeCoeff ω) one_pos (M := M + (p 1).re)
    (fun n => ?_) hm1)
  rw [← sum_pairKernel_pow, one_pow, mul_one]
  have h1 := hM n
  have h2 := hp.norm_le (u ^ n)
  calc ‖∑ j, pairKernel (χ j) (ω j) (u ^ n)‖
      = ‖(p (u ^ n) + ∑ j, pairKernel (χ j) (ω j) (u ^ n)) - p (u ^ n)‖ := by ring_nf
    _ ≤ ‖p (u ^ n) + ∑ j, pairKernel (χ j) (ω j) (u ^ n)‖ + ‖p (u ^ n)‖ := norm_sub_le _ _
    _ ≤ M + (p 1).re := add_le_add h1 h2

/-- A bounded separated Krein–Langer kernel is positive definite: it is its positive part. -/
theorem isPosDefKernel_of_bounded {p : G → ℂ} (hp : IsPosDefKernel p) (χ : Fin κ → G →* ℂ)
    (ω : Fin κ → ℂ) (hω : ∀ j, ω j ≠ 0) (u : G) (hne : ∀ j, ‖χ j u‖ ≠ 1)
    (hsep : Function.Injective (nodes χ u))
    (hb : ∃ M, ∀ n : ℕ, ‖p (u ^ n) + ∑ j, pairKernel (χ j) (ω j) (u ^ n)‖ ≤ M) :
    IsPosDefKernel fun g => p g + ∑ j, pairKernel (χ j) (ω j) g := by
  obtain rfl := card_eq_zero_of_bounded hp χ ω hω u hne hsep hb
  simpa using hp

/-- **Growth reads depth.** Below the largest node modulus no geometric bound holds. -/
theorem not_norm_le_of_lt_depth {p : G → ℂ} (hp : IsPosDefKernel p) (χ : Fin κ → G →* ℂ)
    (ω : Fin κ → ℂ) (hω : ∀ j, ω j ≠ 0) (u : G) (hsep : Function.Injective (nodes χ u))
    {r : ℝ} (hr : 1 ≤ r) {m : Fin κ ⊕ Fin κ} (hm : r < ‖nodes χ u m‖) :
    ¬ ∃ M, ∀ n : ℕ, ‖p (u ^ n) + ∑ j, pairKernel (χ j) (ω j) (u ^ n)‖ ≤ M * r ^ n := by
  rintro ⟨M, hM⟩
  have hc : nodeCoeff ω m ≠ 0 := by
    rcases m with j | j
    · exact hω j
    · exact (star_ne_zero).mpr (hω j)
  refine hc (coeff_eq_zero_of_norm_le hsep (nodeCoeff ω) (zero_lt_one.trans_le hr)
    (M := M + (p 1).re) (fun n => ?_) hm)
  rw [← sum_pairKernel_pow]
  have h1 := hM n
  have h2 := hp.norm_le (u ^ n)
  have hrn : 1 ≤ r ^ n := one_le_pow₀ hr
  have hp0 : 0 ≤ (p 1).re := (norm_nonneg _).trans (hp.norm_le 1)
  calc ‖∑ j, pairKernel (χ j) (ω j) (u ^ n)‖
      ≤ ‖p (u ^ n) + ∑ j, pairKernel (χ j) (ω j) (u ^ n)‖ + ‖p (u ^ n)‖ := by
        have := norm_sub_le (p (u ^ n) + ∑ j, pairKernel (χ j) (ω j) (u ^ n)) (p (u ^ n))
        simpa using this
    _ ≤ M * r ^ n + (p 1).re * r ^ n := add_le_add h1 (h2.trans (le_mul_of_one_le_right hp0 hrn))
    _ = (M + (p 1).re) * r ^ n := by ring

end GaloisForLFunctions.HeckeKreinToeplitz
