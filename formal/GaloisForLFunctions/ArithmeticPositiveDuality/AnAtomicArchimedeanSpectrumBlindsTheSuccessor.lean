import GaloisForLFunctions.ArithmeticPositiveDuality.AFiniteArchimedeanSpectrumBlindsTheSuccessor

/-!
# An atomic archimedean spectrum blinds the successor

Let `φ` be positive definite on `Aff(ℚ)` with dilation part a convergent positive combination of
archimedean characters, `φ(x ↦ ux) = Σ_m c_m u^{iγ_m}`, `c_m ≥ 0`, `Σ c_m < ∞`, `γ_m` distinct:
the shape of Weil's correlation of a test function under RH (a sum over the critical zeros).

**Theorem** (`successor_blind_of_atomic_archimedean`). The successor is blind:
`φ(x ↦ x + b) = α` for every `b ≠ 0`, with `0 ≤ α ≤ φ(1)`.

Mechanism. Two-prime box averages `W_N = N⁻²Σ_{a,b<N} Σ_{k<K} conj(χ_k(2^a3^b)) δ_{x ↦ 2^a3^b x}`
have spectral weights `F_N(m) = Σ_{k<K} N⁻²Σ_{a,b<N}(2^a3^b)^{i(γ_m−γ_k)} → 1[m < K]`
(`log 2/log 3 ∉ ℚ`), so `g ↦ lim ⟪W_N, π(g)W_N⟫` is a positive-definite function whose dilation
part is the finite sum `Σ_{k<K} c_k u^{iγ_k}`. Its successor is blind by the finite theorem
(`successor_blind_of_finite_archimedean`), and it differs from the successor of `φ` by at most
`2(φ(1)Σ_{m≥K}c_m)^{1/2}`.
-/

open Complex Finset Filter Topology

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality

/-! ### Box averages of characters -/

/-- The unit `2^a 3^b`. -/
def boxUnit (a b : ℕ) : ℚˣ := Units.mk0 ((2 : ℚ) ^ a * 3 ^ b) (by positivity)

theorem boxUnit_pos (a b : ℕ) : 0 < ((boxUnit a b : ℚˣ) : ℚ) := by
  simp only [boxUnit, Units.val_mk0]; positivity

theorem archChar_boxUnit (δ : ℝ) (a b : ℕ) :
    archChar δ (boxUnit a b) = archChar δ 2 ^ a * archChar δ 3 ^ b := by
  simp only [boxUnit, Units.val_mk0]
  rw [archChar_mul _ (by positivity) (by positivity), archChar_pow _ (by norm_num),
    archChar_pow _ (by norm_num)]

/-- The Cesàro mean `N⁻¹Σ_{a<N} zᵃ`. -/
def cesaro (z : ℂ) (N : ℕ) : ℂ := (1 / (N : ℂ)) * ∑ a ∈ range N, z ^ a

theorem norm_cesaro_le {z : ℂ} (hz : ‖z‖ = 1) (N : ℕ) : ‖cesaro z N‖ ≤ 1 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [cesaro]
  rw [cesaro, norm_mul]
  have h1 : ‖∑ a ∈ range N, z ^ a‖ ≤ N := by
    calc ‖∑ a ∈ range N, z ^ a‖ ≤ ∑ a ∈ range N, ‖z ^ a‖ := norm_sum_le _ _
      _ = N := by simp [norm_pow, hz]
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  calc ‖1 / (N : ℂ)‖ * ‖∑ a ∈ range N, z ^ a‖ ≤ (1 / N) * N := by
        rw [norm_div, norm_one, Complex.norm_natCast]
        exact mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = 1 := by field_simp

theorem tendsto_cesaro {z : ℂ} (hz : ‖z‖ = 1) (hz1 : z ≠ 1) :
    Tendsto (cesaro z) atTop (𝓝 0) := by
  have hsub : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
  have hbound : ∀ N : ℕ, 0 < N → ‖cesaro z N‖ ≤ (2 / ‖z - 1‖) * (1 / N) := by
    intro N hN
    rw [cesaro, geom_sum_eq hz1, norm_mul, norm_div, norm_div, norm_one, Complex.norm_natCast]
    have : ‖z ^ N - 1‖ ≤ 2 := by
      calc ‖z ^ N - 1‖ ≤ ‖z ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = 2 := by rw [norm_pow, hz, one_pow, norm_one]; norm_num
    have hn : (0 : ℝ) < ‖z - 1‖ := norm_pos_iff.mpr hsub
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
    calc 1 / (N : ℝ) * (‖z ^ N - 1‖ / ‖z - 1‖) ≤ 1 / N * (2 / ‖z - 1‖) := by
          gcongr
      _ = 2 / ‖z - 1‖ * (1 / N) := by ring
  have hlim : Tendsto (fun N : ℕ => (2 / ‖z - 1‖) * (1 / (N : ℝ))) atTop (𝓝 0) := by
    simpa using (tendsto_one_div_atTop_nhds_zero_nat).const_mul (2 / ‖z - 1‖)
  refine tendsto_zero_iff_norm_tendsto_zero.mpr (squeeze_zero' (Eventually.of_forall fun _ =>
    norm_nonneg _) ?_ hlim)
  filter_upwards [eventually_gt_atTop 0] with N hN
  exact hbound N hN

/-- The box average `N⁻²Σ_{a,b<N} (2^a3^b)^{iδ}`. -/
def boxAvg (δ : ℝ) (N : ℕ) : ℂ := cesaro (archChar δ 2) N * cesaro (archChar δ 3) N

theorem norm_boxAvg_le (δ : ℝ) (N : ℕ) : ‖boxAvg δ N‖ ≤ 1 := by
  rw [boxAvg, norm_mul]
  exact mul_le_one₀ (norm_cesaro_le (norm_archChar _ _) N) (norm_nonneg _)
    (norm_cesaro_le (norm_archChar _ _) N)

theorem boxAvg_zero {N : ℕ} (hN : 0 < N) : boxAvg 0 N = 1 := by
  have hNC : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  simp [boxAvg, cesaro, archChar_zero, hNC]

theorem tendsto_boxAvg {δ : ℝ} (hδ : δ ≠ 0) : Tendsto (boxAvg δ) atTop (𝓝 0) := by
  by_cases h2 : archChar δ 2 = 1
  · have h3 : archChar δ 3 ≠ 1 := fun h3 =>
      hδ (eq_zero_of_archChar_eq_one Nat.prime_two Nat.prime_three (by norm_num)
        (by exact_mod_cast h2) (by exact_mod_cast h3))
    have := (tendsto_cesaro (norm_archChar δ 3) h3)
    refine tendsto_zero_iff_norm_tendsto_zero.mpr (squeeze_zero (fun _ => norm_nonneg _)
      (fun N => ?_) (tendsto_zero_iff_norm_tendsto_zero.mp this))
    rw [boxAvg, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (norm_cesaro_le (norm_archChar _ _) N)
  · have := tendsto_cesaro (norm_archChar δ 2) h2
    refine tendsto_zero_iff_norm_tendsto_zero.mpr (squeeze_zero (fun _ => norm_nonneg _)
      (fun N => ?_) (tendsto_zero_iff_norm_tendsto_zero.mp this))
    rw [boxAvg, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (norm_cesaro_le (norm_archChar _ _) N)

/-- The box average is the average of the character over the box. -/
theorem boxAvg_eq (δ : ℝ) (N : ℕ) :
    boxAvg δ N = ∑ a ∈ range N, ∑ b ∈ range N,
      (1 / (N : ℂ) ^ 2) * archChar δ (boxUnit a b) := by
  rw [boxAvg, cesaro, cesaro, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [archChar_boxUnit]
  ring

/-! ### Dilation combinations and their spectral weights -/

section Atomic

variable {φ : AffineGroupQ → ℂ} (hφ : IsPosDefOnGroup φ) (γ : ℕ → ℝ) (c : ℕ → ℝ)
  (hc : ∀ m, 0 ≤ c m) (hcs : Summable c)
  (hf : ∀ u : ℚˣ, 0 < (u : ℚ) → φ (dilation u) = ∑' m, (c m : ℂ) * archChar (γ m) u)

/-- A finite combination `Σ_i α_i δ_{x ↦ v_i x}` of dilations. -/
def dilComb {ι : Type*} (s : Finset ι) (v : ι → ℚˣ) (α : ι → ℂ) : PreGNS ⟨φ, hφ⟩ :=
  ∑ i ∈ s, α i • gnsVec ⟨φ, hφ⟩ (dilation (v i))

/-- Its spectral weight at the atom `γ_m`: `Σ_i α_i v_i^{iγ_m}`. -/
def dilHat {ι : Type*} (s : Finset ι) (v : ι → ℚˣ) (α : ι → ℂ) (m : ℕ) : ℂ :=
  ∑ i ∈ s, α i * archChar (γ m) (v i)

include hc hcs in
theorem summable_weighted {X : ℕ → ℂ} {B : ℝ} (hX : ∀ m, ‖X m‖ ≤ B) :
    Summable fun m => (c m : ℂ) * X m :=
  Summable.of_norm_bounded (hcs.mul_right B) fun m => by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hc m)]
    exact mul_le_mul_of_nonneg_left (hX m) (hc m)

theorem norm_dilHat_le {ι : Type*} (s : Finset ι) (v : ι → ℚˣ) (α : ι → ℂ) (m : ℕ) :
    ‖dilHat γ s v α m‖ ≤ ∑ i ∈ s, ‖α i‖ := by
  unfold dilHat
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_mul, norm_archChar, mul_one]

include hc hcs hf in
/-- **Spectral form of dilation combinations.**
`⟪Σ α_i δ_{v_i}, π(x ↦ ux)Σ β_j δ_{w_j}⟫ = Σ_m c_m u^{iγ_m} conj(α̂_m) β̂_m`. -/
theorem inner_dilComb {ι κ : Type*} (s : Finset ι) (v : ι → ℚˣ) (α : ι → ℂ)
    (hv : ∀ i, 0 < (v i : ℚ)) (t : Finset κ) (w : κ → ℚˣ) (β : κ → ℂ)
    (hw : ∀ j, 0 < (w j : ℚ)) (u : ℚˣ) (hu : 0 < (u : ℚ)) :
    inner ℂ (dilComb hφ s v α) (gnsTranslate ⟨φ, hφ⟩ (dilation u) (dilComb hφ t w β)) =
      ∑' m, (c m : ℂ) * archChar (γ m) u * star (dilHat γ s v α m) * dilHat γ t w β m := by
  set Φ : PosDefFn AffineGroupQ := ⟨φ, hφ⟩
  have hentry : ∀ i j, inner ℂ (gnsVec Φ (dilation (v i)))
      (gnsTranslate Φ (dilation u) (gnsVec Φ (dilation (w j)))) =
        ∑' m, (c m : ℂ) * (star (archChar (γ m) (v i)) * archChar (γ m) u *
          archChar (γ m) (w j)) := by
    intro i j
    rw [gnsTranslate_gnsVec, inner_gnsVec]
    show φ ((dilation (v i))⁻¹ * (dilation u * dilation (w j))) = _
    rw [← map_mul, ← map_inv, ← map_mul]
    have hpos : 0 < (((v i)⁻¹ * (u * w j) : ℚˣ) : ℚ) := by
      push_cast
      have := hv i; have := hw j
      positivity
    rw [hf _ hpos]
    refine tsum_congr fun m => ?_
    push_cast
    rw [archChar_mul _ (inv_pos.mpr (hv i)) (mul_pos hu (hw j)), archChar_inv _ (hv i),
      archChar_mul _ hu (hw j)]
    ring
  have hsum : ∀ i j, Summable fun m => (c m : ℂ) * (star (archChar (γ m) (v i)) *
      archChar (γ m) u * archChar (γ m) (w j)) := fun i j =>
    summable_weighted c hc hcs (B := 1) fun m => by
      rw [norm_mul, norm_mul, norm_star, norm_archChar, norm_archChar, norm_archChar]; norm_num
  have hbil : inner ℂ (dilComb hφ s v α) (gnsTranslate Φ (dilation u) (dilComb hφ t w β)) =
      ∑ i ∈ s, ∑ j ∈ t, star (α i) * β j * inner ℂ (gnsVec Φ (dilation (v i)))
        (gnsTranslate Φ (dilation u) (gnsVec Φ (dilation (w j)))) := by
    unfold dilComb
    rw [map_sum, sum_inner]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_smul_left, inner_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, inner_smul_right, Complex.star_def]
    ring
  rw [hbil]
  simp_rw [hentry]
  have hmove : ∑ i ∈ s, ∑ j ∈ t, star (α i) * β j * ∑' m, (c m : ℂ) *
      (star (archChar (γ m) (v i)) * archChar (γ m) u * archChar (γ m) (w j)) =
      ∑' m, ∑ i ∈ s, ∑ j ∈ t, star (α i) * β j * ((c m : ℂ) *
        (star (archChar (γ m) (v i)) * archChar (γ m) u * archChar (γ m) (w j))) := by
    rw [Summable.tsum_finsetSum fun i _ => summable_sum fun j _ => (hsum i j).mul_left _]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Summable.tsum_finsetSum fun j _ => (hsum i j).mul_left _]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [tsum_mul_left]
  rw [hmove]
  refine tsum_congr fun m => ?_
  unfold dilHat
  rw [star_sum, mul_assoc ((c m : ℂ) * archChar (γ m) u), Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [star_mul]
  ring

end Atomic

/-! ### Norms of differences -/

section Norms

variable {φ : AffineGroupQ → ℂ} (hφ : IsPosDefOnGroup φ) (γ : ℕ → ℝ) (c : ℕ → ℝ)
  (hc : ∀ m, 0 ≤ c m) (hcs : Summable c)
  (hf : ∀ u : ℚˣ, 0 < (u : ℚ) → φ (dilation u) = ∑' m, (c m : ℂ) * archChar (γ m) u)
include hc hcs hf

theorem inner_dilComb_one {ι κ : Type*} (s : Finset ι) (v : ι → ℚˣ) (α : ι → ℂ)
    (hv : ∀ i, 0 < (v i : ℚ)) (t : Finset κ) (w : κ → ℚˣ) (β : κ → ℂ)
    (hw : ∀ j, 0 < (w j : ℚ)) :
    inner ℂ (dilComb hφ s v α) (dilComb hφ t w β) =
      ∑' m, (c m : ℂ) * star (dilHat γ s v α m) * dilHat γ t w β m := by
  have h := inner_dilComb hφ γ c hc hcs hf s v α hv t w β hw 1 (by norm_num)
  rw [map_one, gnsTranslate_one] at h
  rw [h]
  refine tsum_congr fun m => ?_
  rw [show ((1 : ℚˣ) : ℚ) = 1 from rfl, archChar_one, mul_one]

/-- `‖X − Y‖² = Σ_m c_m |X̂_m − Ŷ_m|²` for dilation combinations. -/
theorem norm_sq_sub_dilComb {ι κ : Type*} (s : Finset ι) (v : ι → ℚˣ) (α : ι → ℂ)
    (hv : ∀ i, 0 < (v i : ℚ)) (t : Finset κ) (w : κ → ℚˣ) (β : κ → ℂ)
    (hw : ∀ j, 0 < (w j : ℚ)) :
    ‖dilComb hφ s v α - dilComb hφ t w β‖ ^ 2 =
      ∑' m, c m * ‖dilHat γ s v α m - dilHat γ t w β m‖ ^ 2 := by
  set X := dilComb hφ s v α
  set Y := dilComb hφ t w β
  set x := dilHat γ s v α
  set y := dilHat γ t w β
  have bx : ∀ m, ‖x m‖ ≤ ∑ i ∈ s, ‖α i‖ := fun m => norm_dilHat_le γ s v α m
  have by' : ∀ m, ‖y m‖ ≤ ∑ j ∈ t, ‖β j‖ := fun m => norm_dilHat_le γ t w β m
  have hS : ∀ (a b : ℕ → ℂ) (A B : ℝ), (∀ m, ‖a m‖ ≤ A) → (∀ m, ‖b m‖ ≤ B) →
      Summable fun m => (c m : ℂ) * star (a m) * b m := by
    intro a b A B ha hb
    have := summable_weighted c hc hcs (X := fun m => star (a m) * b m) (B := A * B) fun m => by
      rw [norm_mul, norm_star]
      exact mul_le_mul (ha m) (hb m) (norm_nonneg _) ((norm_nonneg _).trans (ha 0))
    simpa [mul_assoc] using this
  have e : inner ℂ (X - Y) (X - Y) =
      ((∑' m, c m * ‖x m - y m‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_sub_sub_self, inner_dilComb_one hφ γ c hc hcs hf s v α hv s v α hv,
      inner_dilComb_one hφ γ c hc hcs hf s v α hv t w β hw,
      inner_dilComb_one hφ γ c hc hcs hf t w β hw s v α hv,
      inner_dilComb_one hφ γ c hc hcs hf t w β hw t w β hw,
      ← (hS x x _ _ bx bx).tsum_sub (hS x y _ _ bx by'),
      ← ((hS x x _ _ bx bx).sub (hS x y _ _ bx by')).tsum_sub (hS y x _ _ by' bx),
      ← (((hS x x _ _ bx bx).sub (hS x y _ _ bx by')).sub (hS y x _ _ by' bx)).tsum_add
        (hS y y _ _ by' by'), Complex.ofReal_tsum]
    refine tsum_congr fun m => ?_
    push_cast
    rw [← Complex.ofReal_pow, ← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self,
      map_sub]
    simp only [Complex.star_def]
    ring
  rw [@norm_sq_eq_re_inner ℂ, e]
  exact Complex.ofReal_re _

end Norms

/-! ### Limit states with finitely many atoms -/

section Limit

variable {φ : AffineGroupQ → ℂ} (hφ : IsPosDefOnGroup φ) (γ : ℕ → ℝ) (c : ℕ → ℝ)

/-- The box `[0, N)²`. -/
def boxIdx (N : ℕ) : Finset (ℕ × ℕ) := range N ×ˢ range N

/-- The averaged vector `W_N = Σ_{(a,b) ∈ [0,N)²} N⁻² Σ_{k<K} conj(χ_k(2^a3^b)) δ_{2^a3^b}`. -/
def boxVec (K N : ℕ) : PreGNS ⟨φ, hφ⟩ :=
  dilComb hφ (boxIdx N) (fun ab => boxUnit ab.1 ab.2)
    (fun ab => (1 / (N : ℂ) ^ 2) * ∑ k ∈ range K, star (archChar (γ k) (boxUnit ab.1 ab.2)))

/-- The cyclic vector `δ_1` as a dilation combination. -/
def oneVec : PreGNS ⟨φ, hφ⟩ :=
  dilComb hφ (Finset.univ : Finset Unit) (fun _ => 1) (fun _ => 1)

theorem oneVec_eq : oneVec hφ = gnsVec ⟨φ, hφ⟩ 1 := by
  simp [oneVec, dilComb]

theorem dilHat_boxVec (K N m : ℕ) :
    dilHat γ (boxIdx N) (fun ab => boxUnit ab.1 ab.2)
      (fun ab => (1 / (N : ℂ) ^ 2) * ∑ k ∈ range K, star (archChar (γ k) (boxUnit ab.1 ab.2))) m =
      ∑ k ∈ range K, boxAvg (γ m - γ k) N := by
  unfold dilHat boxIdx
  rw [Finset.sum_product]
  simp_rw [boxAvg_eq]
  calc ∑ a ∈ range N, ∑ b ∈ range N, (1 / (N : ℂ) ^ 2) *
        (∑ k ∈ range K, star (archChar (γ k) (boxUnit a b))) * archChar (γ m) (boxUnit a b)
      = ∑ a ∈ range N, ∑ b ∈ range N, ∑ k ∈ range K,
          (1 / (N : ℂ) ^ 2) * archChar (γ m - γ k) (boxUnit a b) := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [archChar_sub]
        ring
    _ = ∑ a ∈ range N, ∑ k ∈ range K, ∑ b ∈ range N,
          (1 / (N : ℂ) ^ 2) * archChar (γ m - γ k) (boxUnit a b) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = _ := Finset.sum_comm

end Limit

/-! ### Spectral weights of the averaged vectors -/

/-- The spectral weights `F_N(m) = Σ_{k<K} N⁻²Σ_{a,b<N}(2^a3^b)^{i(γ_m − γ_k)}` of `W_N`. -/
def boxWeight (γ : ℕ → ℝ) (K N m : ℕ) : ℂ := ∑ k ∈ range K, boxAvg (γ m - γ k) N

/-- The limiting weight `1[m < K]`. -/
def cutWeight (K m : ℕ) : ℂ := if m < K then 1 else 0

theorem norm_boxWeight_le (γ : ℕ → ℝ) (K N m : ℕ) : ‖boxWeight γ K N m‖ ≤ K := by
  unfold boxWeight
  refine (norm_sum_le _ _).trans ?_
  calc ∑ k ∈ range K, ‖boxAvg (γ m - γ k) N‖ ≤ ∑ _k ∈ range K, (1 : ℝ) :=
        Finset.sum_le_sum fun k _ => norm_boxAvg_le _ _
    _ = K := by simp

theorem norm_cutWeight_le (K m : ℕ) : ‖cutWeight K m‖ ≤ 1 := by
  unfold cutWeight; split_ifs <;> simp

theorem tendsto_boxWeight {γ : ℕ → ℝ} (hγ : Function.Injective γ) (K m : ℕ) :
    Tendsto (fun N => boxWeight γ K N m) atTop (𝓝 (cutWeight K m)) := by
  have hterm : ∀ k ∈ range K, Tendsto (fun N => boxAvg (γ m - γ k) N) atTop
      (𝓝 (if k = m then 1 else 0)) := by
    intro k _
    split_ifs with hkm
    · subst hkm
      simp only [sub_self]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with N hN
      exact (boxAvg_zero hN).symm
    · exact tendsto_boxAvg (sub_ne_zero.mpr fun h => hkm (hγ h).symm)
  have h := tendsto_finsetSum (range K) hterm
  rw [Finset.sum_ite_eq'] at h
  simp only [Finset.mem_range] at h
  exact h

section Main

variable {φ : AffineGroupQ → ℂ} (hφ : IsPosDefOnGroup φ) {γ : ℕ → ℝ}
  (hγ : Function.Injective γ) {c : ℕ → ℝ} (hc : ∀ m, 0 ≤ c m) (hcs : Summable c)
  (hf : ∀ u : ℚˣ, 0 < (u : ℚ) → φ (dilation u) = ∑' m, (c m : ℂ) * archChar (γ m) u)
include hc hcs hf

omit hc hcs hf in
theorem dilHat_oneVec (m : ℕ) :
    dilHat γ (Finset.univ : Finset Unit) (fun _ => 1) (fun _ => 1) m = 1 := by
  simp [dilHat, archChar_one]

/-- `‖W_N − W_M‖² = Σ_m c_m |F_N(m) − F_M(m)|²`. -/
theorem norm_sq_boxVec_sub (K N M : ℕ) :
    ‖boxVec hφ γ K N - boxVec hφ γ K M‖ ^ 2 =
      ∑' m, c m * ‖boxWeight γ K N m - boxWeight γ K M m‖ ^ 2 := by
  unfold boxVec
  rw [norm_sq_sub_dilComb hφ γ c hc hcs hf _ _ _ (fun _ => boxUnit_pos _ _) _ _ _
    (fun _ => boxUnit_pos _ _)]
  simp_rw [dilHat_boxVec]
  rfl

theorem norm_sq_boxVec_sub_one (K N : ℕ) :
    ‖boxVec hφ γ K N - oneVec hφ‖ ^ 2 = ∑' m, c m * ‖boxWeight γ K N m - 1‖ ^ 2 := by
  unfold boxVec oneVec
  rw [norm_sq_sub_dilComb hφ γ c hc hcs hf _ _ _ (fun _ => boxUnit_pos _ _) _ _ _
    (fun _ => by norm_num)]
  simp_rw [dilHat_boxVec, dilHat_oneVec]
  rfl

theorem norm_sq_boxVec (K N : ℕ) :
    ‖boxVec hφ γ K N‖ ^ 2 = ∑' m, c m * ‖boxWeight γ K N m‖ ^ 2 := by
  have h := norm_sq_sub_dilComb hφ γ c hc hcs hf (boxIdx N) (fun ab => boxUnit ab.1 ab.2)
    (fun ab => (1 / (N : ℂ) ^ 2) * ∑ k ∈ range K, star (archChar (γ k) (boxUnit ab.1 ab.2)))
    (fun _ => boxUnit_pos _ _) (∅ : Finset Unit) (fun _ => 1) (fun _ => 0) (fun _ => by norm_num)
  simp only [dilComb, Finset.sum_empty, sub_zero, dilHat] at h
  rw [show boxVec hφ γ K N = dilComb hφ (boxIdx N) (fun ab => boxUnit ab.1 ab.2)
    (fun ab => (1 / (N : ℂ) ^ 2) * ∑ k ∈ range K, star (archChar (γ k) (boxUnit ab.1 ab.2))) from
      rfl]
  unfold dilComb
  rw [h]
  refine tsum_congr fun m => ?_
  rw [← dilHat, dilHat_boxVec]
  rfl

theorem norm_sq_oneVec : ‖oneVec hφ‖ ^ 2 = ∑' m, c m := by
  have h := norm_sq_sub_dilComb hφ γ c hc hcs hf (Finset.univ : Finset Unit) (fun _ => 1)
    (fun _ => 1) (fun _ => by norm_num) (∅ : Finset Unit) (fun _ => 1) (fun _ => 0)
    (fun _ => by norm_num)
  simp only [dilComb, Finset.sum_empty, sub_zero] at h
  rw [show oneVec hφ = ∑ i ∈ (Finset.univ : Finset Unit), (fun _ => (1 : ℂ)) i •
    gnsVec ⟨φ, hφ⟩ (dilation ((fun _ => (1 : ℚˣ)) i)) from rfl, h]
  refine tsum_congr fun m => ?_
  simp [dilHat, archChar_one]

end Main

/-! ### Limits -/

theorem norm_inner_translate_sub_le {Φ : PosDefFn AffineGroupQ} (g : AffineGroupQ)
    (A B : PreGNS Φ) :
    ‖inner ℂ A (gnsTranslate Φ g A) - inner ℂ B (gnsTranslate Φ g B)‖ ≤
      ‖A - B‖ * (‖A‖ + ‖B‖) := by
  have e : inner ℂ A (gnsTranslate Φ g A) - inner ℂ B (gnsTranslate Φ g B) =
      inner ℂ (A - B) (gnsTranslate Φ g A) + inner ℂ B (gnsTranslate Φ g (A - B)) := by
    rw [inner_sub_left, map_sub, inner_sub_right]; ring
  rw [e]
  calc _ ≤ ‖inner ℂ (A - B) (gnsTranslate Φ g A)‖ + ‖inner ℂ B (gnsTranslate Φ g (A - B))‖ :=
        norm_add_le _ _
    _ ≤ ‖A - B‖ * ‖gnsTranslate Φ g A‖ + ‖B‖ * ‖gnsTranslate Φ g (A - B)‖ :=
        add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _)
    _ = ‖A - B‖ * (‖A‖ + ‖B‖) := by rw [norm_gnsTranslate, norm_gnsTranslate]; ring

section Blind

variable {φ : AffineGroupQ → ℂ} (hφ : IsPosDefOnGroup φ) {γ : ℕ → ℝ}
  (hγ : Function.Injective γ) {c : ℕ → ℝ} (hc : ∀ m, 0 ≤ c m) (hcs : Summable c)
  (hf : ∀ u : ℚˣ, 0 < (u : ℚ) → φ (dilation u) = ∑' m, (c m : ℂ) * archChar (γ m) u)

/-- The tail mass `Σ_{m ≥ K} c_m`. -/
def tailMass (c : ℕ → ℝ) (K : ℕ) : ℝ := ∑' m, c m * ‖cutWeight K m - 1‖ ^ 2

include hc hcs in
theorem tendsto_tailMass : Tendsto (tailMass c) atTop (𝓝 0) := by
  have hpt : ∀ m, Tendsto (fun K => c m * ‖cutWeight K m - 1‖ ^ 2) atTop (𝓝 0) := by
    intro m
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [eventually_gt_atTop m] with K hK
    simp [cutWeight, hK]
  have hbd : ∀ᶠ K in atTop, ∀ m, ‖c m * ‖cutWeight K m - 1‖ ^ 2‖ ≤ c m :=
    Eventually.of_forall fun K m => by
      rw [Real.norm_of_nonneg (mul_nonneg (hc m) (sq_nonneg _))]
      have : ‖cutWeight K m - 1‖ ≤ 1 := by unfold cutWeight; split_ifs <;> simp
      exact mul_le_of_le_one_right (hc m) (pow_le_one₀ (norm_nonneg _) this)
  have h := tendsto_tsum_of_dominated_convergence (𝓕 := atTop)
    (f := fun K m => c m * ‖cutWeight K m - 1‖ ^ 2) (g := fun _ => (0 : ℝ)) hcs hpt hbd
  simp only [tsum_zero] at h
  exact h

include hγ hc hcs in
theorem tendsto_weightDefect (K : ℕ) :
    Tendsto (fun N => ∑' m, c m * ‖boxWeight γ K N m - cutWeight K m‖ ^ 2) atTop (𝓝 0) := by
  have h := tendsto_tsum_of_dominated_convergence (𝓕 := atTop)
    (f := fun N m => c m * ‖boxWeight γ K N m - cutWeight K m‖ ^ 2) (g := fun _ => (0 : ℝ))
    (bound := fun m => c m * ((K : ℝ) + 1) ^ 2) (hcs.mul_right _) (fun m => by
      have := ((continuous_norm.pow 2).tendsto _).comp
        ((tendsto_boxWeight hγ K m).sub_const (cutWeight K m))
      simpa using this.const_mul (c m)) (Eventually.of_forall fun N m => by
      rw [Real.norm_of_nonneg (mul_nonneg (hc m) (sq_nonneg _))]
      have h1 : ‖boxWeight γ K N m - cutWeight K m‖ ≤ K + 1 :=
        (norm_sub_le _ _).trans (add_le_add (norm_boxWeight_le γ K N m) (norm_cutWeight_le K m))
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) h1 2) (hc m))
  simpa using h


include hc hcs hf in
theorem norm_sq_boxVec_sub_le (K N M : ℕ) :
    ‖boxVec hφ γ K N - boxVec hφ γ K M‖ ^ 2 ≤
      2 * ∑' m, c m * ‖boxWeight γ K N m - cutWeight K m‖ ^ 2 +
        2 * ∑' m, c m * ‖boxWeight γ K M m - cutWeight K m‖ ^ 2 := by
  have hb : ∀ n m, ‖boxWeight γ K n m - cutWeight K m‖ ≤ K + 1 := fun n m =>
    (norm_sub_le _ _).trans (add_le_add (norm_boxWeight_le γ K n m) (norm_cutWeight_le K m))
  have hS : ∀ n, Summable fun m => c m * ‖boxWeight γ K n m - cutWeight K m‖ ^ 2 := fun n =>
    Summable.of_nonneg_of_le (fun m => mul_nonneg (hc m) (sq_nonneg _))
      (fun m => mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hb n m) 2) (hc m))
      (hcs.mul_right (((K : ℝ) + 1) ^ 2))
  rw [norm_sq_boxVec_sub hφ hc hcs hf, ← tsum_mul_left, ← tsum_mul_left,
    ← ((hS N).mul_left 2).tsum_add ((hS M).mul_left 2)]
  refine Summable.tsum_le_tsum (fun m => ?_) ?_ (((hS N).mul_left 2).add ((hS M).mul_left 2))
  · have h1 : ‖boxWeight γ K N m - boxWeight γ K M m‖ ≤
        ‖boxWeight γ K N m - cutWeight K m‖ + ‖boxWeight γ K M m - cutWeight K m‖ := by
      rw [show boxWeight γ K N m - boxWeight γ K M m = (boxWeight γ K N m - cutWeight K m) -
        (boxWeight γ K M m - cutWeight K m) by ring]
      exact norm_sub_le _ _
    have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    nlinarith [hc m, sq_nonneg (‖boxWeight γ K N m - cutWeight K m‖ -
      ‖boxWeight γ K M m - cutWeight K m‖)]
  · refine Summable.of_nonneg_of_le (fun m => mul_nonneg (hc m) (sq_nonneg _)) (fun m => ?_)
      (hcs.mul_right ((2 * (K : ℝ)) ^ 2))
    have h1 : ‖boxWeight γ K N m - boxWeight γ K M m‖ ≤ 2 * K :=
      (norm_sub_le _ _).trans (by linarith [norm_boxWeight_le γ K N m, norm_boxWeight_le γ K M m])
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) h1 2) (hc m)

include hc hcs hf in
theorem norm_boxVec_le (K N : ℕ) : ‖boxVec hφ γ K N‖ ≤ K * Real.sqrt (∑' m, c m) := by
  have hsq : ‖boxVec hφ γ K N‖ ^ 2 ≤ (K : ℝ) ^ 2 * ∑' m, c m := by
    rw [norm_sq_boxVec hφ hc hcs hf, ← tsum_mul_left]
    refine Summable.tsum_le_tsum (fun m => ?_) ?_ (hcs.mul_left _)
    · rw [mul_comm ((K : ℝ) ^ 2)]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _)
        (norm_boxWeight_le γ K N m) 2) (hc m)
    · exact Summable.of_nonneg_of_le (fun m => mul_nonneg (hc m) (sq_nonneg _))
        (fun m => mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _)
          (norm_boxWeight_le γ K N m) 2) (hc m)) (hcs.mul_right _)
  have hC : 0 ≤ ∑' m, c m := tsum_nonneg hc
  rw [← Real.sqrt_sq (norm_nonneg _), ← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ K),
    ← Real.sqrt_mul (sq_nonneg _)]
  exact Real.sqrt_le_sqrt hsq

/-- `z_N(g) = ⟪W_N, π(g)W_N⟫`. -/
def boxState (hφ : IsPosDefOnGroup φ) (γ : ℕ → ℝ) (K N : ℕ) (g : AffineGroupQ) : ℂ :=
  inner ℂ (boxVec hφ γ K N) (gnsTranslate ⟨φ, hφ⟩ g (boxVec hφ γ K N))

include hγ hc hcs hf in
theorem cauchySeq_boxState (K : ℕ) (g : AffineGroupQ) :
    CauchySeq fun N => boxState hφ γ K N g := by
  rw [Metric.cauchySeq_iff']
  intro ε hε
  set B : ℝ := 2 * K * Real.sqrt (∑' m, c m) + 1 with hB
  have hBpos : 0 < B := by positivity
  set δ : ℝ := (ε / B) ^ 2 / 8 with hδ
  have hδpos : 0 < δ := by positivity
  obtain ⟨N0, hN0⟩ := (tendsto_order.mp (tendsto_weightDefect hγ hc hcs K)).2 δ hδpos
    |>.exists_forall_of_atTop
  refine ⟨N0, fun n hn => ?_⟩
  have h1 := norm_sq_boxVec_sub_le hφ hc hcs hf K n N0
  have hd1 := hN0 n hn
  have hd0 := hN0 N0 le_rfl
  have hsq : ‖boxVec hφ γ K n - boxVec hφ γ K N0‖ ^ 2 < (ε / B) ^ 2 / 2 := by
    rw [hδ] at hd1 hd0; linarith
  have hnorm : ‖boxVec hφ γ K n - boxVec hφ γ K N0‖ < ε / B := by
    have : ‖boxVec hφ γ K n - boxVec hφ γ K N0‖ ^ 2 < (ε / B) ^ 2 := by
      have : 0 < (ε / B) ^ 2 := by positivity
      linarith
    exact lt_of_pow_lt_pow_left₀ 2 (by positivity) this
  rw [dist_eq_norm]
  calc ‖boxState hφ γ K n g - boxState hφ γ K N0 g‖
      ≤ ‖boxVec hφ γ K n - boxVec hφ γ K N0‖ * (‖boxVec hφ γ K n‖ + ‖boxVec hφ γ K N0‖) :=
        norm_inner_translate_sub_le g _ _
    _ ≤ ‖boxVec hφ γ K n - boxVec hφ γ K N0‖ * B := by
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        have := norm_boxVec_le hφ hc hcs hf K n
        have := norm_boxVec_le hφ hc hcs hf K N0
        rw [hB]; linarith
    _ < ε / B * B := mul_lt_mul_of_pos_right hnorm hBpos
    _ = ε := by field_simp

/-- The limit state `L_K(g) = lim_N ⟪W_N, π(g)W_N⟫`. -/
def limitState (hφ : IsPosDefOnGroup φ) (γ : ℕ → ℝ) (K : ℕ) (g : AffineGroupQ) : ℂ :=
  limUnder atTop fun N => boxState hφ γ K N g

include hγ hc hcs hf in
theorem tendsto_limitState (K : ℕ) (g : AffineGroupQ) :
    Tendsto (fun N => boxState hφ γ K N g) atTop (𝓝 (limitState hφ γ K g)) :=
  (cauchySeq_boxState hφ hγ hc hcs hf K g).tendsto_limUnder

include hγ hc hcs hf in
/-- The limit state is positive definite: its Gram forms are limits of squared norms. -/
theorem isPosDefOnGroup_limitState (K : ℕ) : IsPosDefOnGroup (limitState hφ γ K) := by
  intro n x a
  set Φ : PosDefFn AffineGroupQ := ⟨φ, hφ⟩
  set S : Set ℂ := {z | 0 ≤ z.re ∧ z.im = 0}
  have hclosed : IsClosed S :=
    (isClosed_le continuous_const Complex.continuous_re).inter
      (isClosed_eq Complex.continuous_im continuous_const)
  have hlim : Tendsto (fun N => ∑ i, ∑ j, star (a i) * boxState hφ γ K N ((x i)⁻¹ * x j) * a j)
      atTop (𝓝 (∑ i, ∑ j, star (a i) * limitState hφ γ K ((x i)⁻¹ * x j) * a j)) :=
    tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ =>
      (tendsto_const_nhds.mul (tendsto_limitState hφ hγ hc hcs hf K _)).mul tendsto_const_nhds
  have hmem : ∀ N, (∑ i, ∑ j, star (a i) * boxState hφ γ K N ((x i)⁻¹ * x j) * a j) ∈ S := by
    intro N
    set W := boxVec hφ γ K N
    have e : (∑ i, ∑ j, star (a i) * boxState hφ γ K N ((x i)⁻¹ * x j) * a j) =
        inner ℂ (∑ i, a i • gnsTranslate Φ (x i) W) (∑ j, a j • gnsTranslate Φ (x j) W) := by
      rw [sum_inner]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [inner_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [inner_smul_left, inner_smul_right, boxState, gnsTranslate_mul, ← inner_gnsTranslate_left,
        Complex.star_def]
      ring
    rw [e]
    have h1 := inner_self_nonneg (𝕜 := ℂ) (x := ∑ i, a i • gnsTranslate Φ (x i) W)
    have h2 := inner_self_im (𝕜 := ℂ) (∑ i, a i • gnsTranslate Φ (x i) W)
    exact ⟨by simpa using h1, by simpa using h2⟩
  have := hclosed.mem_of_tendsto hlim (Eventually.of_forall hmem)
  exact ⟨_, this.1, Complex.ext (by simp) (by rw [Complex.ofReal_im]; exact this.2)⟩

include hγ hc hcs hf in
/-- The dilation part of the limit state is the finite sum `Σ_{k<K} c_k u^{iγ_k}`. -/
theorem limitState_dilation (K : ℕ) (u : ℚˣ) (hu : 0 < (u : ℚ)) :
    limitState hφ γ K (dilation u) = ∑ k : Fin K, (c k : ℂ) * archChar (γ k) u := by
  have hN : ∀ N, boxState hφ γ K N (dilation u) =
      ∑' m, (c m : ℂ) * archChar (γ m) u * star (boxWeight γ K N m) * boxWeight γ K N m := by
    intro N
    unfold boxState boxVec
    rw [inner_dilComb hφ γ c hc hcs hf _ _ _ (fun _ => boxUnit_pos _ _) _ _ _
      (fun _ => boxUnit_pos _ _) u hu]
    simp_rw [dilHat_boxVec]
    rfl
  have hlim : Tendsto (fun N => boxState hφ γ K N (dilation u)) atTop
      (𝓝 (∑' m, (c m : ℂ) * archChar (γ m) u * star (cutWeight K m) * cutWeight K m)) := by
    simp_rw [hN]
    refine tendsto_tsum_of_dominated_convergence (bound := fun m => c m * (K : ℝ) ^ 2)
      (hcs.mul_right _) (fun m => ?_) (Eventually.of_forall fun N m => ?_)
    · exact ((tendsto_const_nhds.mul ((continuous_star.tendsto _).comp
        (tendsto_boxWeight hγ K m))).mul (tendsto_boxWeight hγ K m))
    · rw [norm_mul, norm_mul, norm_mul, norm_star, Complex.norm_real,
        Real.norm_of_nonneg (hc m), norm_archChar, mul_one, mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (hc m)
      rw [← sq]
      exact pow_le_pow_left₀ (norm_nonneg _) (norm_boxWeight_le γ K N m) 2
  rw [tendsto_nhds_unique (tendsto_limitState hφ hγ hc hcs hf K _) hlim]
  rw [tsum_eq_sum (s := range K) fun m hm => by
    simp [cutWeight, Finset.mem_range.not.mp hm]]
  rw [← Fin.sum_univ_eq_sum_range (fun m => (c m : ℂ) * archChar (γ m) u * star (cutWeight K m) *
    cutWeight K m)]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [cutWeight, k.2]


include hγ hc hcs hf in
/-- The successor of `φ` is within `2(Σc · Σ_{m≥K}c)^{1/2}` of that of the limit state. -/
theorem norm_successor_sub_limitState_le (K : ℕ) (b : ℚ) :
    ‖φ (translation b) - limitState hφ γ K (translation b)‖ ≤
      2 * Real.sqrt (∑' m, c m) * Real.sqrt (tailMass c K) := by
  set Φ : PosDefFn AffineGroupQ := ⟨φ, hφ⟩
  set C := ∑' m, c m with hC
  have hC0 : 0 ≤ C := tsum_nonneg hc
  have hψ : φ (translation b) =
      inner ℂ (oneVec hφ) (gnsTranslate Φ (translation b) (oneVec hφ)) := by
    rw [oneVec_eq, gnsTranslate_gnsVec, inner_gnsVec, inv_one, one_mul, mul_one]
  have hbound : ∀ N, ‖φ (translation b) - boxState hφ γ K N (translation b)‖ ≤
      ‖oneVec hφ - boxVec hφ γ K N‖ * (‖oneVec hφ‖ + ‖boxVec hφ γ K N‖) := by
    intro N; rw [hψ]; exact norm_inner_translate_sub_le _ _ _
  have hsq_lim : ∀ (w : ℕ → ℕ → ℂ) (e : ℕ → ℂ) (B : ℝ), (∀ m, Tendsto (fun N => w N m) atTop
      (𝓝 (e m))) → (∀ N m, ‖w N m‖ ≤ B) →
      Tendsto (fun N => ∑' m, c m * ‖w N m‖ ^ 2) atTop (𝓝 (∑' m, c m * ‖e m‖ ^ 2)) := by
    intro w e B hw hB
    refine tendsto_tsum_of_dominated_convergence (bound := fun m => c m * B ^ 2) (hcs.mul_right _)
      (fun m => ?_) (Eventually.of_forall fun N m => ?_)
    · exact (((continuous_norm.pow 2).tendsto _).comp (hw m)).const_mul (c m)
    · rw [Real.norm_of_nonneg (mul_nonneg (hc m) (sq_nonneg _))]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hB N m) 2) (hc m)
  have h1 : Tendsto (fun N => ‖oneVec hφ - boxVec hφ γ K N‖) atTop
      (𝓝 (Real.sqrt (tailMass c K))) := by
    have hsq := hsq_lim (fun N m => boxWeight γ K N m - 1) (fun m => cutWeight K m - 1) (K + 1)
      (fun m => (tendsto_boxWeight hγ K m).sub_const 1) (fun N m =>
        (norm_sub_le _ _).trans (by simpa using add_le_add_right (norm_boxWeight_le γ K N m) 1))
    have e : ∀ N, ‖oneVec hφ - boxVec hφ γ K N‖ =
        Real.sqrt (∑' m, c m * ‖boxWeight γ K N m - 1‖ ^ 2) := fun N => by
      rw [norm_sub_rev, ← norm_sq_boxVec_sub_one hφ hc hcs hf, Real.sqrt_sq (norm_nonneg _)]
    simp_rw [e]
    exact (Real.continuous_sqrt.tendsto _).comp hsq
  have h2 : Tendsto (fun N => ‖boxVec hφ γ K N‖) atTop
      (𝓝 (Real.sqrt (∑' m, c m * ‖cutWeight K m‖ ^ 2))) := by
    have hsq := hsq_lim (fun N m => boxWeight γ K N m) (fun m => cutWeight K m) K
      (fun m => tendsto_boxWeight hγ K m) (fun N m => norm_boxWeight_le γ K N m)
    have e : ∀ N, ‖boxVec hφ γ K N‖ = Real.sqrt (∑' m, c m * ‖boxWeight γ K N m‖ ^ 2) :=
      fun N => by rw [← norm_sq_boxVec hφ hc hcs hf, Real.sqrt_sq (norm_nonneg _)]
    simp_rw [e]
    exact (Real.continuous_sqrt.tendsto _).comp hsq
  have h0 : ‖oneVec hφ‖ = Real.sqrt C := by
    rw [hC, ← norm_sq_oneVec hφ hc hcs hf, Real.sqrt_sq (norm_nonneg _)]
  have hlimL : Tendsto (fun N => ‖φ (translation b) - boxState hφ γ K N (translation b)‖) atTop
      (𝓝 ‖φ (translation b) - limitState hφ γ K (translation b)‖) :=
    ((continuous_norm.tendsto _).comp
      (tendsto_const_nhds.sub (tendsto_limitState hφ hγ hc hcs hf K _)))
  have hlimR := h1.mul ((tendsto_const_nhds (x := ‖oneVec hφ‖)).add h2)
  have hle := le_of_tendsto_of_tendsto' hlimL hlimR hbound
  rw [h0] at hle
  have hcut : ∑' m, c m * ‖cutWeight K m‖ ^ 2 ≤ C :=
    Summable.tsum_le_tsum (fun m => mul_le_of_le_one_right (hc m)
      (pow_le_one₀ (norm_nonneg _) (norm_cutWeight_le K m)))
      (Summable.of_nonneg_of_le (fun m => mul_nonneg (hc m) (sq_nonneg _))
        (fun m => mul_le_of_le_one_right (hc m) (pow_le_one₀ (norm_nonneg _)
          (norm_cutWeight_le K m))) hcs) hcs
  calc ‖φ (translation b) - limitState hφ γ K (translation b)‖
      ≤ Real.sqrt (tailMass c K) * (Real.sqrt C + Real.sqrt (∑' m, c m * ‖cutWeight K m‖ ^ 2)) :=
        hle
    _ ≤ Real.sqrt (tailMass c K) * (Real.sqrt C + Real.sqrt C) :=
        mul_le_mul_of_nonneg_left (add_le_add le_rfl (Real.sqrt_le_sqrt hcut))
          (Real.sqrt_nonneg _)
    _ = 2 * Real.sqrt C * Real.sqrt (tailMass c K) := by ring

end Blind

/-! ### Blindness -/

/-- **An atomic archimedean spectrum blinds the successor.** If `φ` is positive definite on
`Aff(ℚ)` and `φ(x ↦ ux) = Σ_m c_m u^{iγ_m}` for `u > 0`, with `c_m ≥ 0` summable and distinct
`γ_m`, then `φ(x ↦ x + b) = α` for every `b ≠ 0`, with `0 ≤ α ≤ φ(1)`. -/
theorem successor_blind_of_atomic_archimedean {φ : AffineGroupQ → ℂ} (hφ : IsPosDefOnGroup φ)
    {γ : ℕ → ℝ} (hγ : Function.Injective γ) {c : ℕ → ℝ} (hc : ∀ m, 0 ≤ c m) (hcs : Summable c)
    (hf : ∀ u : ℚˣ, 0 < (u : ℚ) → φ (dilation u) = ∑' m, (c m : ℂ) * archChar (γ m) u) :
    ∃ α : ℝ, 0 ≤ α ∧ α ≤ (φ 1).re ∧ ∀ b : ℚ, b ≠ 0 → φ (translation b) = α := by
  set C := ∑' m, c m
  have hblind : ∀ K, ∃ α : ℝ, ∀ b : ℚ, b ≠ 0 → limitState hφ γ K (translation b) = α := by
    intro K
    obtain ⟨α, -, -, hα⟩ := successor_blind_of_finite_archimedean
      (isPosDefOnGroup_limitState hφ hγ hc hcs hf K) (fun k : Fin K => γ k)
      (fun k l h => Fin.ext (hγ h)) (fun k => c k) (fun k => hc k)
      (fun u hu => limitState_dilation hφ hγ hc hcs hf K u hu)
    exact ⟨α, hα⟩
  have hconst : ∀ b b' : ℚ, b ≠ 0 → b' ≠ 0 → φ (translation b) = φ (translation b') := by
    intro b b' hb hb'
    have hle : ∀ K, ‖φ (translation b) - φ (translation b')‖ ≤
        4 * Real.sqrt C * Real.sqrt (tailMass c K) := by
      intro K
      obtain ⟨α, hα⟩ := hblind K
      have e1 := norm_successor_sub_limitState_le hφ hγ hc hcs hf K b
      have e2 := norm_successor_sub_limitState_le hφ hγ hc hcs hf K b'
      rw [hα b hb] at e1
      rw [hα b' hb'] at e2
      calc ‖φ (translation b) - φ (translation b')‖
          = ‖(φ (translation b) - α) - (φ (translation b') - α)‖ := by ring_nf
        _ ≤ ‖φ (translation b) - α‖ + ‖φ (translation b') - α‖ := norm_sub_le _ _
        _ ≤ 4 * Real.sqrt C * Real.sqrt (tailMass c K) := by linarith
    have hlim : Tendsto (fun K => 4 * Real.sqrt C * Real.sqrt (tailMass c K)) atTop (𝓝 0) := by
      have := ((Real.continuous_sqrt.tendsto 0).comp (tendsto_tailMass hc hcs)).const_mul
        (4 * Real.sqrt C)
      simpa using this
    exact sub_eq_zero.mp (norm_le_zero_iff.mp (ge_of_tendsto' hlim hle))
  set α := φ (translation 1) with hα_def
  obtain ⟨him, hre⟩ := const_successor_real ⟨φ, hφ⟩ (gnsVec ⟨φ, hφ⟩ 1) α (fun b hb => by
    rw [gnsTranslate_gnsVec, inner_gnsVec, inv_one, one_mul, mul_one]
    exact hconst b 1 hb.ne' one_ne_zero)
  have hα : α = (α.re : ℂ) := Complex.ext (by simp) (by simp [him])
  obtain ⟨r0, hr0, h0⟩ := hφ.map_one_eq
  refine ⟨α.re, hre, ?_, fun b hb => by rw [hconst b 1 hb one_ne_zero, ← hα]⟩
  have h : Complex.normSq α ≤ (φ 1).re ^ 2 := hφ.normSq_le (translation 1)
  rw [hα, Complex.normSq_ofReal, h0, Complex.ofReal_re] at h
  rw [h0, Complex.ofReal_re]
  nlinarith

end GaloisForLFunctions.ArithmeticPositiveDuality
