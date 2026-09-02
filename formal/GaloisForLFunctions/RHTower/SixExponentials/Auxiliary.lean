import GaloisForLFunctions.RHTower.SixExponentials.Field
import GaloisForLFunctions.RHTower.GelfondSchneiderSiegel
import GaloisForLFunctions.HTGeometry.ComplexExponentialPolynomial

/-!
# Six exponentials: Siegel coefficients and the auxiliary exponential polynomial

Siegel's lemma applied to the scaled sample matrix at level `(L, M₀)` with `2 M₀³ ≤ L²` gives a
nonzero integral coefficient vector `ξ` with house at most `B ≤ 2 c₁² L² H^{6LM₀}`.  The
auxiliary function `F(z) = Σ σ(ξ_{ab}) exp(λ_{ab} z)` vanishes at every sample point of level
`M₀`, is not identically zero (distinct frequencies), grows at most like `L² B exp(LX‖z‖)`, and
its scaled values `Σ ξ_{ab} · entry(m, ab)` at level `M` are algebraic integers with
`σ(value) = c^{6LM} F(s_m)` and house at most `L² B H^{6LM}`.
-/

open Complex Finset NumberField

namespace GaloisForLFunctions.RHTower.SixExponentials

/-- The explicit Siegel constant is at least one. -/
theorem one_le_siegel_c₁ (K : Type*) [Field K] [NumberField K] [DecidableEq (K →+* ℂ)] :
    1 ≤ GelfondSchneiderSiegel.c₁ K := by
  unfold GelfondSchneiderSiegel.c₁ GelfondSchneiderSiegel.c₂
  have h1 : (1 : ℝ) ≤ Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  have h2 : (1 : ℝ) ≤ max 1 (GelfondSchneiderSiegel.c K) := le_max_left _ _
  have h3 := GelfondSchneiderSiegel.one_le_supOfBasis K
  calc (1 : ℝ) = 1 * (1 * 1) := by ring
    _ ≤ Module.finrank ℚ K
        * (max 1 (GelfondSchneiderSiegel.c K) * GelfondSchneiderSiegel.supOfBasis K) :=
        mul_le_mul h1 (mul_le_mul h2 h3 zero_le_one (by linarith)) (by norm_num) (by positivity)

/-- The Siegel house bound with exponent at most one is at most `2 c² q A`. -/
theorem siegel_bound_le {c q p A : ℝ} (hc : 1 ≤ c) (hq : 1 ≤ q) (hp : 0 < p) (hqp : 2 * p ≤ q)
    (hA : 1 ≤ A) : c * (c * q * A) ^ (p / (q - p)) ≤ 2 * c ^ 2 * q * A := by
  have hb1 : 1 ≤ c * q * A := by
    calc (1 : ℝ) = 1 * 1 * 1 := by ring
      _ ≤ c * q * A := mul_le_mul (mul_le_mul hc hq zero_le_one (by linarith)) hA zero_le_one
          (by nlinarith)
  have ht1 : p / (q - p) ≤ 1 := by
    rw [div_le_one (by linarith)]
    linarith
  have hbt : (c * q * A) ^ (p / (q - p)) ≤ c * q * A := by
    calc (c * q * A) ^ (p / (q - p)) ≤ (c * q * A) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hb1 ht1
      _ = c * q * A := Real.rpow_one _
  calc c * (c * q * A) ^ (p / (q - p)) ≤ c * (c * q * A) :=
        mul_le_mul_of_nonneg_left hbt (by linarith)
    _ = c ^ 2 * q * A := by ring
    _ ≤ 2 * c ^ 2 * q * A := by nlinarith [sq_nonneg c]

namespace AlgData

variable (A : AlgData)

/-- The scaled sample matrix at level `(L, M)`. -/
noncomputable def mat (L M : ℕ) : Matrix (Fin 3 → Fin M) (Fin L × Fin L) (𝓞 A.K) :=
  Matrix.of fun m ab => A.entry L M m ab

theorem mat_apply (L M : ℕ) (m : Fin 3 → Fin M) (ab : Fin L × Fin L) :
    A.mat L M m ab = A.entry L M m ab := rfl

theorem mat_ne_zero {L M : ℕ} (hL : 0 < L) (hM : 0 < M) : A.mat L M ≠ 0 := by
  intro h
  have h1 : A.mat L M (fun _ => ⟨0, hM⟩) (⟨0, hL⟩, ⟨0, hL⟩) = 0 := by
    rw [h]
    rfl
  exact A.entry_ne_zero _ _ _ _ h1

/-- **Siegel coefficients.**  For `2 M₀³ ≤ L²` there is a nonzero integral vector killing the
level-`M₀` sample matrix, with house at most `B ≤ 2 c₁² L² H^{6LM₀}`, `B ≥ 1`. -/
theorem exists_coefficients {L M₀ : ℕ} (hL : 0 < L) (hM : 0 < M₀) (h2 : 2 * M₀ ^ 3 ≤ L * L)
    [DecidableEq (A.K →+* ℂ)] :
    ∃ (ξ : Fin L × Fin L → 𝓞 A.K) (B : ℝ), ξ ≠ 0 ∧ (A.mat L M₀).mulVec ξ = 0 ∧ 1 ≤ B ∧
      (∀ l, house (algebraMap (𝓞 A.K) A.K (ξ l)) ≤ B) ∧
      B ≤ 2 * GelfondSchneiderSiegel.c₁ A.K ^ 2 * (L * L) * A.Hb ^ (6 * L * M₀) := by
  have hcardβ : Fintype.card (Fin L × Fin L) = L * L := by simp
  have hcardα : Fintype.card (Fin 3 → Fin M₀) = M₀ ^ 3 := by simp
  have hp0 : 0 < M₀ ^ 3 := pow_pos hM 3
  have hlt : M₀ ^ 3 < L * L := by omega
  obtain ⟨ξ, hξ, hker, hh⟩ := GelfondSchneiderSiegel.exists_ne_zero_int_vec_house_le (K := A.K)
    (A.mat L M₀) (A.mat_ne_zero hL hM) hp0 hlt hcardβ
    (A := A.Hb ^ (6 * L * M₀)) (fun k l => A.house_entry_le L M₀ k l) hcardα
  have hc₁ : 1 ≤ GelfondSchneiderSiegel.c₁ A.K := one_le_siegel_c₁ A.K
  have hAb : 1 ≤ A.Hb ^ (6 * L * M₀) := one_le_pow₀ A.one_le_Hb
  have hq1 : (1 : ℝ) ≤ ((L * L : ℕ) : ℝ) := by
    have : 1 ≤ L * L := Nat.one_le_iff_ne_zero.mpr (by positivity)
    exact_mod_cast this
  have hp0' : (0 : ℝ) < ((M₀ ^ 3 : ℕ) : ℝ) := by exact_mod_cast hp0
  have hqp : 2 * ((M₀ ^ 3 : ℕ) : ℝ) ≤ ((L * L : ℕ) : ℝ) := by exact_mod_cast h2
  have hbound := siegel_bound_le hc₁ hq1 hp0' hqp hAb
  refine ⟨ξ, max 1 (GelfondSchneiderSiegel.c₁ A.K *
      (GelfondSchneiderSiegel.c₁ A.K * ((L * L : ℕ) : ℝ) * A.Hb ^ (6 * L * M₀))
        ^ (((M₀ ^ 3 : ℕ) : ℝ) / (((L * L : ℕ) : ℝ) - ((M₀ ^ 3 : ℕ) : ℝ)))),
    hξ, hker, le_max_left _ _, ?_, ?_⟩
  · intro l
    exact le_trans (hh l) (le_max_right _ _)
  · apply max_le
    · calc (1 : ℝ) ≤ 2 * 1 ^ 2 * 1 * 1 := by norm_num
        _ ≤ 2 * GelfondSchneiderSiegel.c₁ A.K ^ 2 * (L * L) * A.Hb ^ (6 * L * M₀) := by
            have hL1 : (1 : ℝ) ≤ (L : ℝ) * L := by
              have := hq1
              push_cast at this
              exact this
            gcongr
    · calc GelfondSchneiderSiegel.c₁ A.K *
          (GelfondSchneiderSiegel.c₁ A.K * ((L * L : ℕ) : ℝ) * A.Hb ^ (6 * L * M₀))
            ^ (((M₀ ^ 3 : ℕ) : ℝ) / (((L * L : ℕ) : ℝ) - ((M₀ ^ 3 : ℕ) : ℝ)))
          ≤ 2 * GelfondSchneiderSiegel.c₁ A.K ^ 2 * ((L * L : ℕ) : ℝ) * A.Hb ^ (6 * L * M₀) :=
            hbound
        _ = 2 * GelfondSchneiderSiegel.c₁ A.K ^ 2 * (L * L) * A.Hb ^ (6 * L * M₀) := by
            push_cast
            ring

/-! ### The auxiliary function -/

/-- The auxiliary exponential polynomial `F(z) = Σ σ(ξ_{ab}) exp(λ_{ab} z)`. -/
noncomputable def F {L : ℕ} (ξ : Fin L × Fin L → 𝓞 A.K) (z : ℂ) : ℂ :=
  ∑ ab, A.σ (algebraMap (𝓞 A.K) A.K (ξ ab)) * Complex.exp (A.toData.freq ab * z)

theorem differentiable_F {L : ℕ} (ξ : Fin L × Fin L → 𝓞 A.K) : Differentiable ℂ (A.F ξ) := by
  unfold F
  refine Differentiable.fun_sum (𝕜 := ℂ) fun ab _ => ?_
  exact (differentiable_const _).mul ((differentiable_const _).mul differentiable_id).cexp

theorem analyticAt_F {L : ℕ} (ξ : Fin L × Fin L → 𝓞 A.K) (z : ℂ) : AnalyticAt ℂ (A.F ξ) z :=
  (A.differentiable_F ξ).analyticAt z

/-- The scaled value of `F` at the sample point `s_m` of level `M`. -/
noncomputable def sval (L M : ℕ) (ξ : Fin L × Fin L → 𝓞 A.K) (m : Fin 3 → Fin M) : 𝓞 A.K :=
  (A.mat L M).mulVec ξ m

theorem sval_eq_sum (L M : ℕ) (ξ : Fin L × Fin L → 𝓞 A.K) (m : Fin 3 → Fin M) :
    A.sval L M ξ m = ∑ ab, A.entry L M m ab * ξ ab := by
  unfold sval Matrix.mulVec dotProduct
  rfl

/-- **Embedded scaled value.**  `σ(value) = c^{6LM} · F(s_m)`. -/
theorem σ_sval (L M : ℕ) (ξ : Fin L × Fin L → 𝓞 A.K) (m : Fin 3 → Fin M) :
    A.σ (algebraMap (𝓞 A.K) A.K (A.sval L M ξ m))
      = (A.scale : ℂ) ^ (6 * L * M) * A.F ξ (A.toData.pt m) := by
  rw [sval_eq_sum, map_sum, map_sum]
  unfold F
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun ab _ => ?_
  rw [map_mul, map_mul, σ_entry]
  ring

/-- Vanishing at the Siegel level. -/
theorem F_pt_eq_zero_of_ker {L M₀ : ℕ} (ξ : Fin L × Fin L → 𝓞 A.K)
    (hker : (A.mat L M₀).mulVec ξ = 0) (m : Fin 3 → Fin M₀) : A.F ξ (A.toData.pt m) = 0 := by
  have h := A.σ_sval L M₀ ξ m
  have h0 : A.sval L M₀ ξ m = 0 := by
    unfold sval
    rw [hker]
    rfl
  rw [h0, map_zero, map_zero] at h
  have hc : (A.scale : ℂ) ^ (6 * L * M₀) ≠ 0 :=
    pow_ne_zero _ (by exact_mod_cast A.scale_ne_zero)
  rcases mul_eq_zero.mp h.symm with h1 | h1
  · exact absurd h1 hc
  · exact h1

/-- House bound for the scaled value: at most `L² · H^{6LM} · B`. -/
theorem house_sval_le (L M : ℕ) (ξ : Fin L × Fin L → 𝓞 A.K) {B : ℝ}
    (hB : ∀ l, house (algebraMap (𝓞 A.K) A.K (ξ l)) ≤ B) (m : Fin 3 → Fin M) :
    house (algebraMap (𝓞 A.K) A.K (A.sval L M ξ m)) ≤ (L * L) * (A.Hb ^ (6 * L * M) * B) := by
  rw [sval_eq_sum, map_sum]
  have hH0 : 0 ≤ A.Hb ^ (6 * L * M) := pow_nonneg (le_trans zero_le_one A.one_le_Hb) _
  calc house (∑ ab, algebraMap (𝓞 A.K) A.K (A.entry L M m ab * ξ ab))
      ≤ ∑ ab, house (algebraMap (𝓞 A.K) A.K (A.entry L M m ab * ξ ab)) :=
        house_sum_le_sum_house _ _
    _ ≤ ∑ _ab : Fin L × Fin L, A.Hb ^ (6 * L * M) * B := by
        apply Finset.sum_le_sum
        intro ab _
        rw [map_mul]
        exact le_trans (house_mul_le _ _)
          (mul_le_mul (A.house_entry_le L M m ab) (hB ab) (house_nonneg _) hH0)
    _ = (L * L) * (A.Hb ^ (6 * L * M) * B) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring

/-- **Growth bound.**  `‖F(z)‖ ≤ L² · B · exp(L X ‖z‖)`. -/
theorem norm_F_le {L : ℕ} (ξ : Fin L × Fin L → 𝓞 A.K) {B : ℝ}
    (hB : ∀ l, house (algebraMap (𝓞 A.K) A.K (ξ l)) ≤ B) (z : ℂ) :
    ‖A.F ξ z‖ ≤ (L * L) * (B * Real.exp (L * A.toData.X * ‖z‖)) := by
  unfold F
  calc ‖∑ ab, A.σ (algebraMap (𝓞 A.K) A.K (ξ ab)) * Complex.exp (A.toData.freq ab * z)‖
      ≤ ∑ ab, ‖A.σ (algebraMap (𝓞 A.K) A.K (ξ ab)) * Complex.exp (A.toData.freq ab * z)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _ab : Fin L × Fin L, B * Real.exp (L * A.toData.X * ‖z‖) := by
        apply Finset.sum_le_sum
        intro ab _
        rw [norm_mul, Complex.norm_exp]
        apply mul_le_mul
        · exact le_trans (norm_embedding_le_house _ _) (hB ab)
        · apply Real.exp_le_exp.mpr
          calc (A.toData.freq ab * z).re ≤ ‖A.toData.freq ab * z‖ := Complex.re_le_norm _
            _ = ‖A.toData.freq ab‖ * ‖z‖ := norm_mul _ _
            _ ≤ (L * A.toData.X) * ‖z‖ :=
                mul_le_mul_of_nonneg_right (A.toData.norm_freq_le ab) (norm_nonneg _)
        · positivity
        · exact le_trans (house_nonneg _) (hB ab)
    _ = (L * L) * (B * Real.exp (L * A.toData.X * ‖z‖)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring

/-- **Nonvanishing.**  A nonzero coefficient vector gives a nonzero function, because the
frequencies are pairwise distinct. -/
theorem exists_F_ne_zero {L : ℕ} (hL : 0 < L) (ξ : Fin L × Fin L → 𝓞 A.K) (hξ : ξ ≠ 0) :
    ∃ z, A.F ξ z ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hLL : L * L - 1 + 1 = L * L :=
    Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (by positivity))
  let e : Fin (L * L - 1 + 1) ≃ Fin L × Fin L := (finCongr hLL).trans finProdFinEquiv.symm
  let c : Fin (L * L - 1 + 1) → ℂ := fun k => A.toData.freq (e k)
  let P : Fin (L * L - 1 + 1) → Polynomial ℂ :=
    fun k => Polynomial.C (A.σ (algebraMap (𝓞 A.K) A.K (ξ (e k))))
  have hc : Function.Injective c := (A.toData.freq_injective L).comp e.injective
  have hzero : ∀ z, HTGeometry.CExpPoly.cexpFn c P z = 0 := by
    intro z
    rw [← hcon z]
    unfold HTGeometry.CExpPoly.cexpFn F
    exact Fintype.sum_equiv e _ _ (fun k => by simp [P, c])
  have hP := HTGeometry.CExpPoly.eq_zero_of_cexpFn_eq_zero (L * L - 1) c P hc hzero
  apply hξ
  funext ab
  have h1 := hP (e.symm ab)
  simp only [P, Equiv.apply_symm_apply, Polynomial.C_eq_zero] at h1
  have h2 : algebraMap (𝓞 A.K) A.K (ξ ab) = 0 := A.σ_injective (by rw [h1, map_zero])
  show ξ ab = 0
  exact IsFractionRing.injective (𝓞 A.K) A.K (by rw [h2, map_zero])

end AlgData

end GaloisForLFunctions.RHTower.SixExponentials
