import GaloisForLFunctions.RHTower.CharacterProductZeroPlantingTwoLevel
import GaloisForLFunctions.RHTower.MultiplicativeLargeSieve

/-!
# A limit-periodic Dirichlet exponential carries a single character

**Theorem** (`limitPeriodic_exp_single_character`). Let `ℓ(0) = ℓ(1) = 0` with
`Σ |ℓ(n)| n^{−σ} < ∞` for every `σ > 1`, and let `a = exp⋆ℓ` be its Dirichlet exponential.
Suppose `a` is limit-periodic with square-root weighted `ℓ¹` periodic parts: `a(n) = Σ_q Ψ_q(n)`
for `n ≥ 1`, where `Ψ_q` has period `q + 1`, `|Ψ_q| ≤ B_q` and `Σ_q √(q+1) B_q < ∞`. For a
character `ξ` mod `N` let

`Γ_ξ(s) = Σ_q Σ_{χ mod q+1, χ ∼ ξ} L(s, c_χ) L(s, χ)`   (`limitCharCoeff`),

where `χ ∼ ξ` means that `χ` and `ξ` agree at the level `(q + 1)N`, and
`c_χ(m) = φ(q+1)^{−1} Σ_b χ(b⁻¹) Ψ_q(m b)` on the `(q+1)`-smooth `m`. Then for every real `s₀ > 1`
and every level `N`, at most one character `ξ` mod `N` has `Γ_ξ(s₀) ≠ 0`.

For a single period this is `periodic_exp_single_character` (Saias–Weingartner rigidity in
Bohr-lift form). Here infinitely many periods are allowed, with the weight `√(q+1)`. This is the
size of a Gauss sum, so the frequencies `x = b/q` of an absolutely convergent expansion
`a(n) = Σ_x β(x) e(nx)` with `Σ_x |β(x)| √den(x) < ∞` qualify.

**Proof.** Suppose `Γ_{ξ₁}(s₀), Γ_{ξ₂}(s₀) ≠ 0`.
* *Parseval* (`sum_norm_charSection_le`): `Σ_χ |c_χ(m)| ≤ √(q+1) B_q`, so the level-`q` part has
  character mass `W_q ≤ √(q+1) B_q Z(s₀)²` with `Z(s₀) = Σ n^{−s₀}` (`sum_norm_near_le`).
* *Levels.* Pick `q₀` with `Σ_{q ≥ q₀} W_q ≤ |Γ_{ξ₁}|/96` and put `N₁ = N·q₀!`. The coefficients do
  not depend on the level (`limitCharCoeff_changeLevel`). The two-level planting
  (`exists_twoLevel_zero_of_far`) at level `N₁` gives `η`. Pick `D ≥ q₀` such that the level-`N₁`
  coefficients of the levels `q < D` are within `η/2` of `Γ` (`tendsto_nearCoeff`, from the Euler
  product of `L(s₀, χ)`), and such that the tail `Σ_{q ≥ D} B_q` is small. Put `N' = N₁·D!`.
* *Twist.* Let `f` be completely multiplicative with `f(p) = p^{−s₀}` for `p ≤ D` and `f(p) = z_p`
  on a finite set `S` of primes above `D` (`lowValues`). Then `Σ_n a(n) f(n) = Σ_q Σ_n Ψ_q(n) f(n)`
  (`LSeries_limitPeriodic_twist`). For `q < D` the character decomposition gives
  `Σ_χ L(s₀, c_χ) Π_{p≤D}(1 − χ(p)p^{−s₀})^{−1} Π_S(1 − χ(p)z_p)^{−1}`
  (`LSeries_periodic_twist_lowValues`). Regrouped at level `N'`, this is the level-`N₁` part plus
  band characters with mass `≤ Σ_{q ≥ q₀} W_q` (`sum_near_regroup`, `sum_norm_bandCoeff_le`).
* *Far part.* The levels `q ≥ D` and the error of the level-`N₁` coefficients form a far part of
  size `≤ η e^{2Σ_S|z_p|}`, holomorphic in `z` (Euler bound `lowValues_support`).
* The planting gives `z` with `Σ_n a(n) f(n) = 0`. But `Σ_n a(n) f(n) = exp(Σ_n ℓ(n) f(n)) ≠ 0`
  (`tsum_dirichletExp_twist_ne_zero`).
-/

open Complex Filter Topology

namespace RHTower

namespace CharacterZeroPlanting

open GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## Character Parseval for the sections -/

/-- The section `c_χ(m)` as a character sum over all of `ℤ/M`. -/
theorem charSection_eq_sum {M : ℕ} [NeZero M] (Ψ : ZMod M → ℂ) (χ : DirichletCharacter ℂ M)
    (m : ℕ) : charSection Ψ χ m =
      ((M.totient : ℂ))⁻¹ *
        ∑ c : ZMod M, χ c * (if IsUnit c then Ψ ((m : ZMod M) * c⁻¹) else 0) := by
  classical
  unfold charSection
  congr 1
  have h1 : ∑ c : ZMod M, χ c * (if IsUnit c then Ψ ((m : ZMod M) * c⁻¹) else 0) =
      ∑ c : ZMod M, (if IsUnit c then χ c * Ψ ((m : ZMod M) * c⁻¹) else 0) :=
    Finset.sum_congr rfl fun c _ => by split_ifs <;> simp
  rw [h1, sum_ite_isUnit (fun c => χ c * Ψ ((m : ZMod M) * c⁻¹))]
  refine Fintype.sum_equiv (Equiv.inv _) _ _ fun b => ?_
  simp only [Equiv.inv_apply, ZMod.inv_coe_unit, inv_inv]

/-- **Character Parseval for the sections.** If `|Ψ| ≤ B`, then `Σ_χ |c_χ(m)| ≤ √M · B`. -/
theorem sum_norm_charSection_le {M : ℕ} [NeZero M] (Ψ : ZMod M → ℂ) {B : ℝ}
    (hB : ∀ a, ‖Ψ a‖ ≤ B) (m : ℕ) :
    ∑ χ : DirichletCharacter ℂ M, ‖charSection Ψ χ m‖ ≤ Real.sqrt M * B := by
  classical
  set g : ZMod M → ℂ := fun c => if IsUnit c then Ψ ((m : ZMod M) * c⁻¹) else 0 with hg
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have htot : (0 : ℝ) < M.totient := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne M))
  have hpars := sum_dirichletChar_normSq (r := M) g
  have hgB : ∑ b ∈ (Finset.univ : Finset (ZMod M)).filter IsUnit, ‖g b‖ ^ 2 ≤ M * B ^ 2 := by
    calc ∑ b ∈ (Finset.univ : Finset (ZMod M)).filter IsUnit, ‖g b‖ ^ 2
        ≤ ∑ _b ∈ (Finset.univ : Finset (ZMod M)).filter IsUnit, B ^ 2 :=
          Finset.sum_le_sum fun b hb => by
            have hbu : IsUnit b := (Finset.mem_filter.mp hb).2
            simp only [hg, if_pos hbu]
            exact pow_le_pow_left₀ (norm_nonneg _) (hB _) 2
      _ = ((Finset.univ : Finset (ZMod M)).filter IsUnit).card * B ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ M * B ^ 2 := by
          refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
          have h := Finset.card_filter_le (Finset.univ : Finset (ZMod M)) IsUnit
          rw [Finset.card_univ, ZMod.card] at h
          exact_mod_cast h
  have hcs : ∀ χ : DirichletCharacter ℂ M, ‖charSection Ψ χ m‖ ^ 2 =
      ((M.totient : ℝ))⁻¹ ^ 2 * ‖∑ c : ZMod M, χ c * g c‖ ^ 2 := fun χ => by
    rw [charSection_eq_sum, norm_mul, mul_pow, norm_inv, Complex.norm_natCast]
  have hsq : ∑ χ : DirichletCharacter ℂ M, ‖charSection Ψ χ m‖ ^ 2 ≤
      ((M.totient : ℝ))⁻¹ * (M * B ^ 2) := by
    rw [Finset.sum_congr rfl fun χ _ => hcs χ, ← Finset.mul_sum, hpars]
    calc ((M.totient : ℝ))⁻¹ ^ 2 * (M.totient *
          ∑ b ∈ (Finset.univ : Finset (ZMod M)).filter IsUnit, ‖g b‖ ^ 2)
        = ((M.totient : ℝ))⁻¹ * ∑ b ∈ (Finset.univ : Finset (ZMod M)).filter IsUnit, ‖g b‖ ^ 2 := by
          field_simp
      _ ≤ ((M.totient : ℝ))⁻¹ * (M * B ^ 2) := mul_le_mul_of_nonneg_left hgB (by positivity)
  have hcard : ((Finset.univ : Finset (DirichletCharacter ℂ M)).card : ℝ) = M.totient := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card,
      DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity]
  have hCS := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (DirichletCharacter ℂ M)))
    (f := fun χ => ‖charSection Ψ χ m‖)
  rw [hcard] at hCS
  have hfin : (∑ χ : DirichletCharacter ℂ M, ‖charSection Ψ χ m‖) ^ 2 ≤ M * B ^ 2 := by
    refine hCS.trans ?_
    calc (M.totient : ℝ) * ∑ χ : DirichletCharacter ℂ M, ‖charSection Ψ χ m‖ ^ 2
        ≤ M.totient * (((M.totient : ℝ))⁻¹ * (M * B ^ 2)) :=
          mul_le_mul_of_nonneg_left hsq htot.le
      _ = M * B ^ 2 := by field_simp
  have hs0 : 0 ≤ ∑ χ : DirichletCharacter ℂ M, ‖charSection Ψ χ m‖ :=
    Finset.sum_nonneg fun _ _ => norm_nonneg _
  calc ∑ χ : DirichletCharacter ℂ M, ‖charSection Ψ χ m‖
      = Real.sqrt ((∑ χ : DirichletCharacter ℂ M, ‖charSection Ψ χ m‖) ^ 2) :=
        (Real.sqrt_sq hs0).symm
    _ ≤ Real.sqrt (M * B ^ 2) := Real.sqrt_le_sqrt hfin
    _ = Real.sqrt M * B := by
        rw [Real.sqrt_mul (Nat.cast_nonneg M), Real.sqrt_sq hB0]

/-! ## Dirichlet series bounds -/

/-- `Z(s₀) = Σ_n n^{−s₀}`. -/
def zetaBound (s₀ : ℝ) : ℝ := ∑' n : ℕ, (n : ℝ) ^ (-s₀)

theorem summable_rpow_neg {s₀ : ℝ} (hs : 1 < s₀) : Summable fun n : ℕ => (n : ℝ) ^ (-s₀) :=
  Real.summable_nat_rpow.mpr (by linarith)

theorem zetaBound_nonneg (s₀ : ℝ) : 0 ≤ zetaBound s₀ :=
  tsum_nonneg fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _

/-- `‖term f s₀ n‖ = ‖f n‖ n^{−s₀}` for real `s₀ > 0`. -/
theorem norm_term_ofReal (f : ℕ → ℂ) {s₀ : ℝ} (hs : 0 < s₀) (n : ℕ) :
    ‖LSeries.term f s₀ n‖ = ‖f n‖ * (n : ℝ) ^ (-s₀) := by
  rw [LSeries.norm_term_eq]
  split_ifs with hn
  · rw [hn, Nat.cast_zero, Real.zero_rpow (by linarith), mul_zero]
  · rw [ofReal_re, div_eq_mul_inv, ← Real.rpow_neg (Nat.cast_nonneg n)]

/-- A Dirichlet series with bounded coefficients at a real point `s₀ > 1`. -/
theorem norm_LSeries_le_tsum {f : ℕ → ℂ} {s₀ : ℝ} (hs : 1 < s₀) {K : ℝ}
    (hf : ∀ n, ‖f n‖ ≤ K) :
    Summable (fun n => ‖f n‖ * (n : ℝ) ^ (-s₀)) ∧
      ‖LSeries f s₀‖ ≤ ∑' n, ‖f n‖ * (n : ℝ) ^ (-s₀) := by
  have hs0 : (0 : ℝ) < s₀ := by linarith
  have hs' : Summable (fun n => ‖f n‖ * (n : ℝ) ^ (-s₀)) :=
    Summable.of_nonneg_of_le (fun n => by positivity)
      (fun n => mul_le_mul_of_nonneg_right (hf n) (by positivity))
      ((summable_rpow_neg hs).mul_left K)
  refine ⟨hs', ?_⟩
  have ht : Summable fun n => ‖LSeries.term f s₀ n‖ := by
    simpa only [norm_term_ofReal f hs0] using hs'
  calc ‖LSeries f s₀‖ = ‖∑' n, LSeries.term f s₀ n‖ := rfl
    _ ≤ ∑' n, ‖LSeries.term f s₀ n‖ := norm_tsum_le_tsum_norm ht
    _ = ∑' n, ‖f n‖ * (n : ℝ) ^ (-s₀) := by simp only [norm_term_ofReal f hs0]

theorem norm_LSeries_le_of_norm_le {f : ℕ → ℂ} {s₀ : ℝ} (hs : 1 < s₀) {K : ℝ}
    (hf : ∀ n, ‖f n‖ ≤ K) : ‖LSeries f s₀‖ ≤ K * zetaBound s₀ := by
  obtain ⟨hs', hle⟩ := norm_LSeries_le_tsum hs hf
  refine hle.trans ?_
  rw [zetaBound, ← tsum_mul_left]
  exact hs'.tsum_le_tsum (fun n => mul_le_mul_of_nonneg_right (hf n) (by positivity))
    ((summable_rpow_neg hs).mul_left K)

/-- **Mass of the smooth sections.** `Σ_χ |L(s₀, c_χ)| ≤ √M · B · Z(s₀)`. -/
theorem sum_norm_LSeries_charSmoothCoeff_le {M : ℕ} [NeZero M] (Ψ : ZMod M → ℂ) {B : ℝ}
    (hB : ∀ a, ‖Ψ a‖ ≤ B) {s₀ : ℝ} (hs : 1 < s₀) :
    ∑ χ : DirichletCharacter ℂ M, ‖LSeries (charSmoothCoeff Ψ χ) s₀‖ ≤
      Real.sqrt M * B * zetaBound s₀ := by
  have hK : ∀ χ : DirichletCharacter ℂ M, ∀ n,
      ‖charSmoothCoeff Ψ χ n‖ ≤ ‖charSection Ψ χ n‖ := by
    intro χ n; unfold charSmoothCoeff; split_ifs
    · exact le_rfl
    · rw [norm_zero]; exact norm_nonneg _
  have h1 := fun χ => norm_LSeries_le_tsum hs fun n => (hK χ n).trans (norm_charSection_le Ψ χ n)
  calc ∑ χ, ‖LSeries (charSmoothCoeff Ψ χ) s₀‖
      ≤ ∑ χ, ∑' n, ‖charSmoothCoeff Ψ χ n‖ * (n : ℝ) ^ (-s₀) :=
        Finset.sum_le_sum fun χ _ => (h1 χ).2
    _ = ∑' n, ∑ χ, ‖charSmoothCoeff Ψ χ n‖ * (n : ℝ) ^ (-s₀) :=
        (Summable.tsum_finsetSum fun χ _ => (h1 χ).1).symm
    _ ≤ ∑' n : ℕ, Real.sqrt M * B * (n : ℝ) ^ (-s₀) := by
        refine Summable.tsum_le_tsum (fun n => ?_) (summable_sum fun χ _ => (h1 χ).1)
          ((summable_rpow_neg hs).mul_left _)
        rw [← Finset.sum_mul]
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        exact (Finset.sum_le_sum fun χ _ => hK χ n).trans (sum_norm_charSection_le Ψ hB n)
    _ = Real.sqrt M * B * zetaBound s₀ := by rw [zetaBound, tsum_mul_left]

/-- At `s = 0` a Dirichlet series with `f(0) = 0` is the plain sum. -/
theorem LSeries_zero_eq_tsum {g : ℕ → ℂ} (hg : g 0 = 0) : LSeries g 0 = ∑' n, g n := by
  refine tsum_congr fun n => ?_
  rw [LSeries.term_def]
  split_ifs with hn
  · rw [hn, hg]
  · rw [Complex.cpow_zero, div_one]

/-! ## Low prime values -/

/-- Prime values `p^{−s₀}` at the primes `p ≤ D`, and `v_p` elsewhere. -/
def lowValues (D : ℕ) (s₀ : ℝ) (v : ℕ → ℂ) (p : ℕ) : ℂ :=
  if p ∈ (D + 1).primesBelow then (p : ℂ) ^ (-(s₀ : ℂ)) else v p

theorem norm_natCast_cpow_neg {p : ℕ} (hp : 0 < p) (s₀ : ℝ) :
    ‖(p : ℂ) ^ (-(s₀ : ℂ))‖ = (p : ℝ) ^ (-s₀) := by
  rw [Complex.norm_natCast_cpow_of_pos hp]; simp only [neg_re, ofReal_re]

theorem rpow_neg_le_half {p : ℕ} (hp : p.Prime) {s₀ : ℝ} (hs : 1 < s₀) :
    (p : ℝ) ^ (-s₀) ≤ 1 / 2 := by
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  calc (p : ℝ) ^ (-s₀) ≤ (p : ℝ) ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    _ = (p : ℝ)⁻¹ := Real.rpow_neg_one _
    _ ≤ 1 / 2 := by rw [one_div]; exact inv_anti₀ (by norm_num) h2

theorem sum_primesBelow_rpow_le (D : ℕ) {s₀ : ℝ} (hs : 1 < s₀) :
    ∑ p ∈ (D + 1).primesBelow, (p : ℝ) ^ (-s₀) ≤ zetaBound s₀ :=
  (summable_rpow_neg hs).sum_le_tsum _ fun n _ => by positivity

/-- The low values of a vector supported on `S` with entries at most `½` are supported on
`{p ≤ D} ∪ S`, at most `½` there, and have total size at most `Z(s₀) + Σ_S|v_p|`. -/
theorem lowValues_support {D : ℕ} {s₀ : ℝ} (hs : 1 < s₀) {S : Finset ℕ} {v : ℕ → ℂ}
    (hv0 : ∀ p, p ∉ S → v p = 0) (hv : ∀ p ∈ S, ‖v p‖ ≤ 1 / 2) :
    (∀ p, p ∉ (D + 1).primesBelow ∪ S → lowValues D s₀ v p = 0) ∧
      (∀ p ∈ (D + 1).primesBelow ∪ S, ‖lowValues D s₀ v p‖ ≤ 1 / 2) ∧
      ∑ p ∈ (D + 1).primesBelow ∪ S, ‖lowValues D s₀ v p‖ ≤ zetaBound s₀ + ∑ p ∈ S, ‖v p‖ := by
  classical
  refine ⟨fun p hp => ?_, fun p hp => ?_, ?_⟩
  · rw [Finset.mem_union, not_or] at hp
    simp only [lowValues, if_neg hp.1]; exact hv0 p hp.2
  · unfold lowValues
    split_ifs with h
    · have hp := (Nat.mem_primesBelow.mp h).2
      rw [norm_natCast_cpow_neg hp.pos]; exact rpow_neg_le_half hp hs
    · rcases Finset.mem_union.mp hp with h' | h'
      · exact absurd h' h
      · exact hv p h'
  · set P := (D + 1).primesBelow with hP
    have hpt : ∀ p, ‖lowValues D s₀ v p‖ ≤
        (if p ∈ P then (p : ℝ) ^ (-s₀) else 0) + ‖v p‖ := by
      intro p; unfold lowValues; split_ifs with h
      · rw [norm_natCast_cpow_neg (Nat.mem_primesBelow.mp h).2.pos]
        linarith [norm_nonneg (v p)]
      · linarith
    have hfil : (P ∪ S).filter (· ∈ P) = P := by
      ext p; simp only [Finset.mem_filter, Finset.mem_union]; tauto
    calc ∑ p ∈ P ∪ S, ‖lowValues D s₀ v p‖
        ≤ ∑ p ∈ P ∪ S, ((if p ∈ P then (p : ℝ) ^ (-s₀) else 0) + ‖v p‖) :=
          Finset.sum_le_sum fun p _ => hpt p
      _ = ∑ p ∈ P, (p : ℝ) ^ (-s₀) + ∑ p ∈ P ∪ S, ‖v p‖ := by
          rw [Finset.sum_add_distrib, ← Finset.sum_filter, hfil]
      _ ≤ zetaBound s₀ + ∑ p ∈ S, ‖v p‖ := by
          rw [← Finset.sum_subset Finset.subset_union_right
            (fun p _ hp => by rw [hv0 p hp, norm_zero])]
          linarith [sum_primesBelow_rpow_le D hs]

/-- Low values of a vector with `|z_p| ≤ p^{−σ}` are at most `p^{−min(σ, s₀)}` at the primes. -/
theorem norm_lowValues_le_rpow {D : ℕ} {s₀ σ : ℝ} {S : Finset ℕ} {z : ℕ → ℂ}
    (hz0 : ∀ p, p ∉ S → z p = 0) (hz : ∀ p ∈ S, ‖z p‖ ≤ (p : ℝ) ^ (-σ)) {p : ℕ} (hp : p.Prime) :
    ‖lowValues D s₀ z p‖ ≤ (p : ℝ) ^ (-min σ s₀) := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  unfold lowValues
  split_ifs with h
  · rw [norm_natCast_cpow_neg hp.pos]
    exact Real.rpow_le_rpow_of_exponent_le hp1 (by simp)
  · by_cases hS : p ∈ S
    · exact (hz p hS).trans (Real.rpow_le_rpow_of_exponent_le hp1 (by simp))
    · rw [hz0 p hS, norm_zero]; positivity

/-- The truncated Euler product `Π_{p ≤ D}(1 − χ(p)p^{−s₀})^{−1}`. -/
def lowEuler {M : ℕ} (χ : DirichletCharacter ℂ M) (D : ℕ) (s₀ : ℝ) : ℂ :=
  ∏ p ∈ (D + 1).primesBelow, (1 - χ p * (p : ℂ) ^ (-(s₀ : ℂ)))⁻¹

theorem tendsto_lowEuler {M : ℕ} (χ : DirichletCharacter ℂ M) {s₀ : ℝ} (hs : 1 < s₀) :
    Tendsto (fun D => lowEuler χ D s₀) atTop (𝓝 (LSeries (fun n => χ n) s₀)) :=
  (DirichletCharacter.LSeries_eulerProduct χ (s := s₀) (by simpa using hs)).comp
    (tendsto_add_atTop_nat 1)

/-- **The twisted Euler product.** For `z` supported on a set `S` of primes above `D` with
`|z_p| ≤ p^{−σ}`, `σ > 1`, the completely multiplicative `f` with prime values
`lowValues D s₀ z` satisfies
`Σ_n χ(n) f(n) = Π_{p≤D}(1 − χ(p)p^{−s₀})^{−1} Π_S(1 − χ(p) z_p)^{−1}`. -/
theorem LSeries_charTwist_lowValues {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M) {D : ℕ}
    {s₀ σ : ℝ} (hs : 1 < s₀) (hσ : 1 < σ) {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime ∧ D < p)
    {z : ℕ → ℂ} (hz0 : ∀ p, p ∉ S → z p = 0) (hz : ∀ p ∈ S, ‖z p‖ ≤ (p : ℝ) ^ (-σ)) :
    LSeries (fun n => χ n * primeValueTwist (lowValues D s₀ z) n) 0 =
      lowEuler χ D s₀ * ∏ p ∈ S, (1 - χ p * z p)⁻¹ := by
  classical
  set P := (D + 1).primesBelow with hP
  have hσ' : 1 < min σ s₀ := lt_min hσ hs
  have hsum : Summable fun n : ℕ => χ n * primeValueTwist (lowValues D s₀ z) n := by
    refine Summable.of_norm_bounded (Real.summable_nat_rpow.mpr (by linarith :
      -min σ s₀ < -1)) fun n => ?_
    rcases eq_or_ne n 0 with rfl | hn
    · simp only [Nat.cast_zero, map_zero, mul_zero, norm_zero]
      exact Real.rpow_nonneg le_rfl _
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (DirichletCharacter.norm_le_one χ _)).trans
      (norm_primeValueTwist_le (fun p hp => norm_lowValues_le_rpow hz0 hz hp) hn)
  have hdisj : Disjoint P S := by
    rw [Finset.disjoint_left]
    intro p hpP hpS
    have := (Nat.mem_primesBelow.mp hpP).1
    have := (hS p hpS).2
    omega
  have hT : ∀ p ∈ P ∪ S, p.Prime := by
    intro p hp
    rcases Finset.mem_union.mp hp with h | h
    · exact (Nat.mem_primesBelow.mp h).2
    · exact (hS p h).1
  have hv : ∀ p, p.Prime → p ∉ P ∪ S → χ p * lowValues D s₀ z p = 0 := by
    intro p _ hp
    rw [Finset.mem_union, not_or] at hp
    rw [hP] at hp
    simp only [lowValues, if_neg hp.1, hz0 p hp.2, mul_zero]
  rw [LSeries_charTwist_eq_prod χ _ (P ∪ S) hT hv hsum, Finset.prod_union hdisj]
  congr 1
  · exact Finset.prod_congr rfl fun p hp => by simp only [lowValues, if_pos hp]
  · refine Finset.prod_congr rfl fun p hp => ?_
    have hpP : p ∉ (D + 1).primesBelow := Finset.disjoint_right.mp hdisj hp
    simp only [lowValues, if_neg hpP]

/-- **Near part.** For `M ≤ D`, twisting an `M`-periodic `Ψ` by the completely multiplicative `f`
with prime values `lowValues D s₀ z` gives
`Σ_χ L(s₀, c_χ) Π_{p≤D}(1 − χ(p)p^{−s₀})^{−1} Π_S(1 − χ(p)z_p)^{−1}`. -/
theorem LSeries_periodic_twist_lowValues {M : ℕ} [NeZero M] (Ψ : ZMod M → ℂ) {D : ℕ}
    (hMD : M ≤ D) {s₀ σ : ℝ} (hs : 1 < s₀) (hσ : 1 < σ) {S : Finset ℕ}
    (hS : ∀ p ∈ S, p.Prime ∧ D < p) {z : ℕ → ℂ} (hz0 : ∀ p, p ∉ S → z p = 0)
    (hz : ∀ p ∈ S, ‖z p‖ ≤ (p : ℝ) ^ (-σ)) :
    LSeries (fun n => Ψ n * primeValueTwist (lowValues D s₀ z) n) 0 =
      ∑ χ : DirichletCharacter ℂ M, LSeries (charSmoothCoeff Ψ χ) s₀ *
        (lowEuler χ D s₀ * ∏ p ∈ S, (1 - χ p * z p)⁻¹) := by
  classical
  set f : ℕ →*₀ ℂ := primeValueTwist (lowValues D s₀ z) with hf
  set σ' : ℝ := min σ s₀ with hσ'def
  have hσ' : 1 < σ' := lt_min hσ hs
  have hf_norm : ∀ n, n ≠ 0 → ‖f n‖ ≤ (n : ℝ) ^ (-σ') := fun n hn =>
    norm_primeValueTwist_le (fun p hp => norm_lowValues_le_rpow hz0 hz hp) hn
  have hB : ∀ χ : DirichletCharacter ℂ M, ∀ n, n ≠ 0 →
      ‖smoothSection Ψ χ f n‖ ≤ (∑ a, ‖Ψ a‖) * (n : ℝ) ^ (-σ') := by
    intro χ n hn
    unfold smoothSection
    split_ifs
    · rw [norm_mul]
      exact mul_le_mul (norm_charSection_le Ψ χ n) (hf_norm n hn) (norm_nonneg _)
        (Finset.sum_nonneg fun _ _ => norm_nonneg _)
    · rw [norm_zero]; positivity
  have hβS : ∀ χ : DirichletCharacter ℂ M, LSeriesSummable (smoothSection Ψ χ f) 0 := fun χ =>
    LSeriesSummable_of_le_const_mul_rpow (x := 1 - σ') (by simp; linarith)
      ⟨∑ a, ‖Ψ a‖, fun n hn => by rw [show 1 - σ' - 1 = -σ' by ring]; exact hB χ n hn⟩
  have hγnorm : ∀ χ : DirichletCharacter ℂ M, ∀ n : ℕ, n ≠ 0 →
      ‖χ n * f n‖ ≤ (n : ℝ) ^ (-σ') := by
    intro χ n hn
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (DirichletCharacter.norm_le_one χ _)).trans
      (hf_norm n hn)
  have hγS : ∀ χ : DirichletCharacter ℂ M, LSeriesSummable (fun n : ℕ => χ n * f n) 0 :=
    fun χ => summable_of_norm_le_rpow hσ' (hγnorm χ)
  have hdecomp : LSeries (fun n => Ψ n * f n) 0 =
      ∑ χ : DirichletCharacter ℂ M,
        LSeries (smoothSection Ψ χ f) 0 * LSeries (fun n : ℕ => χ n * f n) 0 := by
    have h1 : LSeries (fun n => Ψ n * f n) 0 = LSeries (∑ χ : DirichletCharacter ℂ M,
        LSeries.convolution (smoothSection Ψ χ f) (fun r => χ r * f r)) 0 := by
      refine LSeries_congr (fun {n} hn => ?_) 0
      rw [Finset.sum_apply]
      exact periodic_twist_eq_sum_convolution Ψ f hn
    rw [h1, LSeries_sum fun χ _ => (hβS χ).convolution (hγS χ)]
    exact Finset.sum_congr rfl fun χ _ => LSeries_convolution' (hβS χ) (hγS χ)
  have hβ : ∀ χ : DirichletCharacter ℂ M, LSeries (smoothSection Ψ χ f) 0 =
      LSeries (charSmoothCoeff Ψ χ) s₀ := by
    intro χ
    simp only [LSeries]
    refine tsum_congr fun n => ?_
    rw [LSeries.term_def, LSeries.term_def]
    split_ifs with hn
    · rfl
    · rw [Complex.cpow_zero, div_one]
      unfold smoothSection charSmoothCoeff
      split_ifs with hm
      · have hlow : ∀ p, p.Prime → p ∈ M.primeFactors →
            lowValues D s₀ z p = (p : ℂ) ^ (-(s₀ : ℂ)) := by
          intro p hp hpM
          have hpM' := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne M))
            (Nat.dvd_of_mem_primeFactors hpM)
          have hpD : p ∈ (D + 1).primesBelow := Nat.mem_primesBelow.mpr ⟨by omega, hp⟩
          simp only [lowValues, if_pos hpD]
        rw [hf, primeValueTwist_eq_cpow (P := M.primeFactors) (s := (s₀ : ℂ)) hlow hm,
          Complex.cpow_neg, div_eq_mul_inv]
      · rw [zero_div]
  rw [hdecomp]
  refine Finset.sum_congr rfl fun χ _ => ?_
  rw [hβ, LSeries_charTwist_lowValues χ hs hσ hS hz0 hz]

/-! ## Limit-periodic coefficients -/

/-- Two characters agree at a common level iff they agree at every larger level. -/
theorem changeLevel_eq_changeLevel_iff {a b L L' : ℕ} [NeZero L'] (ha : a ∣ L) (hb : b ∣ L)
    (hL : L ∣ L') (χ : DirichletCharacter ℂ a) (ξ : DirichletCharacter ℂ b) :
    DirichletCharacter.changeLevel (ha.trans hL) χ =
        DirichletCharacter.changeLevel (hb.trans hL) ξ ↔
      DirichletCharacter.changeLevel ha χ = DirichletCharacter.changeLevel hb ξ := by
  rw [DirichletCharacter.changeLevel_trans χ ha hL, DirichletCharacter.changeLevel_trans ξ hb hL]
  exact (DirichletCharacter.changeLevel_injective hL).eq_iff

open Classical in
/-- The coefficient of the character `ξ` mod `N` in `Σ_q Ψ_q`, where `Ψ_q` has period `q + 1`:
the sum, over all `q` and all characters `χ` mod `q + 1` that agree with `ξ` at the level
`(q + 1)N`, of `L(s, c_χ) L(s, χ)`. -/
def limitCharCoeff (Ψ : (q : ℕ) → ZMod (q + 1) → ℂ) {N : ℕ} (ξ : DirichletCharacter ℂ N)
    (s : ℂ) : ℂ :=
  ∑' q : ℕ, ∑ χ : DirichletCharacter ℂ (q + 1),
    if DirichletCharacter.changeLevel (dvd_mul_right (q + 1) N) χ =
        DirichletCharacter.changeLevel (dvd_mul_left N (q + 1)) ξ then
      LSeries (charSmoothCoeff (Ψ q) χ) s * LSeries (fun n => χ n) s else 0

/-- The coefficient does not depend on the level at which `ξ` is presented. -/
theorem limitCharCoeff_changeLevel (Ψ : (q : ℕ) → ZMod (q + 1) → ℂ) {N N₁ : ℕ} [NeZero N₁]
    (hN : N ∣ N₁) (ξ : DirichletCharacter ℂ N) (s : ℂ) :
    limitCharCoeff Ψ (DirichletCharacter.changeLevel hN ξ) s = limitCharCoeff Ψ ξ s := by
  classical
  unfold limitCharCoeff
  refine tsum_congr fun q => Finset.sum_congr rfl fun χ _ => ?_
  have hL : (q + 1) * N ∣ (q + 1) * N₁ := Nat.mul_dvd_mul_left _ hN
  have hiff := changeLevel_eq_changeLevel_iff (dvd_mul_right (q + 1) N)
    (dvd_mul_left N (q + 1)) hL χ ξ
  rw [← DirichletCharacter.changeLevel_trans ξ hN (dvd_mul_left N₁ (q + 1))]
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd (hiff.mp h1) h2
  · exact absurd (hiff.mpr h2) h1
  · rfl

/-! ## Regrouping the near part by characters of a common level -/

open Classical in
/-- Coefficients at level `N₁`: the characters `χ` mod `q + 1`, `q < D`, that agree with `ξ` at
the level `(q + 1)N₁`. -/
def nearCoeff (N₁ D : ℕ) (a : (q : ℕ) → DirichletCharacter ℂ (q + 1) → ℂ)
    (ξ : DirichletCharacter ℂ N₁) : ℂ :=
  ∑ q ∈ Finset.range D, ∑ χ : DirichletCharacter ℂ (q + 1),
    if DirichletCharacter.changeLevel (dvd_mul_right (q + 1) N₁) χ =
        DirichletCharacter.changeLevel (dvd_mul_left N₁ (q + 1)) ξ then a q χ else 0

open Classical in
/-- Lifted coefficients at level `N'`: the characters `χ` mod `q + 1`, `q < D`, whose lift to `N'`
is `ψ`. -/
def liftCoeff (N' D : ℕ) (a : (q : ℕ) → DirichletCharacter ℂ (q + 1) → ℂ)
    (ψ : DirichletCharacter ℂ N') : ℂ :=
  ∑ q ∈ Finset.range D, if h : (q + 1) ∣ N' then
    ∑ χ : DirichletCharacter ℂ (q + 1),
      if DirichletCharacter.changeLevel h χ = ψ then a q χ else 0 else 0

open Classical in
/-- Band coefficients: the lifted coefficients of the characters mod `N'` that do not factor
through `N₁`. -/
def bandCoeff (N₁ N' D : ℕ) (a : (q : ℕ) → DirichletCharacter ℂ (q + 1) → ℂ)
    (ψ : DirichletCharacter ℂ N') : ℂ :=
  if ψ.FactorsThrough N₁ then 0 else liftCoeff N' D a ψ

/-- On primes that are units mod `N'`, a character and its lift to `N'` agree. -/
theorem prod_changeLevel_eq {M N' : ℕ} (h : M ∣ N') (χ : DirichletCharacter ℂ M) {S : Finset ℕ}
    (hSu : ∀ p ∈ S, IsUnit (p : ZMod N')) (z : ℕ → ℂ) :
    ∏ p ∈ S, (1 - DirichletCharacter.changeLevel h χ p * z p)⁻¹ =
      ∏ p ∈ S, (1 - χ p * z p)⁻¹ :=
  Finset.prod_congr rfl fun p hp => by rw [changeLevel_natCast_of_isUnit h χ (hSu p hp)]

/-- **Regrouping.** The near part `Σ_{q<D} Σ_χ a(q, χ) Π_S(1 − χ(p)z_p)^{−1}` splits into the
characters mod `N₁` with coefficients `nearCoeff` and the band characters mod `N'` with
coefficients `bandCoeff`. -/
theorem sum_near_regroup {N₁ N' D : ℕ} [NeZero N'] (hN : N₁ ∣ N')
    (hq : ∀ q < D, (q + 1) * N₁ ∣ N') (a : (q : ℕ) → DirichletCharacter ℂ (q + 1) → ℂ)
    {S : Finset ℕ} (hSu : ∀ p ∈ S, IsUnit (p : ZMod N')) (z : ℕ → ℂ) :
    ∑ q ∈ Finset.range D, ∑ χ : DirichletCharacter ℂ (q + 1),
        a q χ * ∏ p ∈ S, (1 - χ p * z p)⁻¹ =
      ∑ ξ : DirichletCharacter ℂ N₁, nearCoeff N₁ D a ξ * ∏ p ∈ S, (1 - ξ p * z p)⁻¹ +
        ∑ ψ : DirichletCharacter ℂ N', bandCoeff N₁ N' D a ψ * ∏ p ∈ S, (1 - ψ p * z p)⁻¹ := by
  classical
  set P : DirichletCharacter ℂ N' → ℂ := fun ψ => ∏ p ∈ S, (1 - ψ p * z p)⁻¹ with hP
  set K : DirichletCharacter ℂ N' → ℂ := liftCoeff N' D a with hK
  have hq' : ∀ q < D, (q + 1) ∣ N' := fun q hqD => (dvd_mul_right (q + 1) N₁).trans (hq q hqD)
  -- the near part is `Σ_ψ K(ψ) P(ψ)`
  have h1 : ∑ q ∈ Finset.range D, ∑ χ : DirichletCharacter ℂ (q + 1),
      a q χ * ∏ p ∈ S, (1 - χ p * z p)⁻¹ = ∑ ψ, K ψ * P ψ := by
    simp only [hK, liftCoeff, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun q hqD => ?_
    have hqd := hq' q (Finset.mem_range.mp hqD)
    simp only [dif_pos hqd, Finset.sum_mul, ite_mul, zero_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun χ _ => ?_
    rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _), hP]
    exact (prod_changeLevel_eq hqd χ hSu z).symm ▸ rfl
  -- split off the factoring characters
  have h2 : ∑ ψ, K ψ * P ψ = ∑ ψ, (if ψ.FactorsThrough N₁ then K ψ * P ψ else 0) +
      ∑ ψ, bandCoeff N₁ N' D a ψ * P ψ := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ψ _ => ?_
    unfold bandCoeff
    by_cases hψ : ψ.FactorsThrough N₁
    · rw [if_pos hψ, if_pos hψ, zero_mul, add_zero]
    · rw [if_neg hψ, if_neg hψ, zero_add]
  -- the factoring characters are the lifts of the characters mod `N₁`
  have himage : (Finset.univ : Finset (DirichletCharacter ℂ N')).filter
      (fun ψ => ψ.FactorsThrough N₁) =
      (Finset.univ : Finset (DirichletCharacter ℂ N₁)).image
        (DirichletCharacter.changeLevel hN) := by
    ext ψ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · rintro ⟨h, χ₀, rfl⟩; exact ⟨χ₀, rfl⟩
    · rintro ⟨χ₀, rfl⟩; exact ⟨hN, χ₀, rfl⟩
  have h3 : ∑ ψ, (if ψ.FactorsThrough N₁ then K ψ * P ψ else 0) =
      ∑ ξ : DirichletCharacter ℂ N₁, K (DirichletCharacter.changeLevel hN ξ) *
        P (DirichletCharacter.changeLevel hN ξ) := by
    rw [← Finset.sum_filter, himage, Finset.sum_image fun x _ y _ hxy =>
      DirichletCharacter.changeLevel_injective hN hxy]
  have h4 : ∀ ξ : DirichletCharacter ℂ N₁, K (DirichletCharacter.changeLevel hN ξ) =
      nearCoeff N₁ D a ξ := by
    intro ξ
    simp only [hK, liftCoeff, nearCoeff]
    refine Finset.sum_congr rfl fun q hqD => ?_
    have hqL := hq q (Finset.mem_range.mp hqD)
    rw [dif_pos (hq' q (Finset.mem_range.mp hqD))]
    refine Finset.sum_congr rfl fun χ _ => ?_
    have hiff := changeLevel_eq_changeLevel_iff (dvd_mul_right (q + 1) N₁)
      (dvd_mul_left N₁ (q + 1)) hqL χ ξ
    split_ifs with c1 c2 c2
    · rfl
    · exact absurd (hiff.mp c1) c2
    · exact absurd (hiff.mpr c2) c1
    · rfl
  rw [h1, h2, h3]
  congr 1
  refine Finset.sum_congr rfl fun ξ _ => ?_
  rw [h4, hP]
  simp only [prod_changeLevel_eq hN ξ hSu z]

/-- **Band mass.** Only the levels `q + 1` that do not divide `N₁` contribute to the band. -/
theorem sum_norm_bandCoeff_le {N₁ N' D : ℕ} [NeZero N'] (hN : N₁ ∣ N')
    (a : (q : ℕ) → DirichletCharacter ℂ (q + 1) → ℂ) :
    ∑ ψ : DirichletCharacter ℂ N', ‖bandCoeff N₁ N' D a ψ‖ ≤
      ∑ q ∈ Finset.range D, if (q + 1) ∣ N₁ then 0 else
        ∑ χ : DirichletCharacter ℂ (q + 1), ‖a q χ‖ := by
  classical
  set b : DirichletCharacter ℂ N' → ℝ := fun ψ => ∑ q ∈ Finset.range D,
    if h : (q + 1) ∣ N' then ∑ χ : DirichletCharacter ℂ (q + 1),
      (if DirichletCharacter.changeLevel h χ = ψ ∧ ¬ ψ.FactorsThrough N₁ then ‖a q χ‖ else 0)
    else 0 with hb
  have hle : ∀ ψ, ‖bandCoeff N₁ N' D a ψ‖ ≤ b ψ := by
    intro ψ
    unfold bandCoeff liftCoeff
    split_ifs with hψ
    · rw [norm_zero]
      refine Finset.sum_nonneg fun q _ => ?_
      split_ifs
      · exact Finset.sum_nonneg fun χ _ => by split_ifs <;> simp
      · exact le_rfl
    · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun q _ => ?_)
      split_ifs with h
      · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun χ _ => ?_)
        by_cases hc : DirichletCharacter.changeLevel h χ = ψ
        · rw [if_pos hc, if_pos ⟨hc, hψ⟩]
        · rw [if_neg hc, if_neg fun h' => hc h'.1, norm_zero]
      · rw [norm_zero]
  have hsum : ∑ ψ, b ψ = ∑ q ∈ Finset.range D, if h : (q + 1) ∣ N' then
      ∑ χ : DirichletCharacter ℂ (q + 1),
        (if ¬ (DirichletCharacter.changeLevel h χ).FactorsThrough N₁ then ‖a q χ‖ else 0)
      else 0 := by
    simp only [hb]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun q _ => ?_
    split_ifs with h
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun χ _ => ?_
      have e : ∀ ψ : DirichletCharacter ℂ N',
          (if DirichletCharacter.changeLevel h χ = ψ ∧ ¬ ψ.FactorsThrough N₁ then ‖a q χ‖
            else 0) = if DirichletCharacter.changeLevel h χ = ψ then
              (if ¬ ψ.FactorsThrough N₁ then ‖a q χ‖ else 0) else 0 := fun ψ => by
        by_cases h1 : DirichletCharacter.changeLevel h χ = ψ <;>
          by_cases h2 : ψ.FactorsThrough N₁ <;> simp [h1, h2]
      simp only [e]
      rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]
    · simp
  refine (Finset.sum_le_sum fun ψ _ => hle ψ).trans ?_
  rw [hsum]
  refine Finset.sum_le_sum fun q _ => ?_
  split_ifs with h hN1
  · refine (Finset.sum_eq_zero fun χ _ => ?_).le
    have hft : (DirichletCharacter.changeLevel h χ).FactorsThrough N₁ := by
      refine ⟨hN, DirichletCharacter.changeLevel hN1 χ, ?_⟩
      exact DirichletCharacter.changeLevel_trans χ hN1 hN
    rw [if_neg (not_not.mpr hft)]
  · exact Finset.sum_le_sum fun χ _ => by split_ifs <;> simp
  · exact le_rfl
  · exact Finset.sum_nonneg fun χ _ => norm_nonneg _

/-! ## Convergence of the near coefficients -/

/-- Tails of a summable nonnegative sequence tend to `0`. -/
theorem tendsto_tsum_tail {u : ℕ → ℝ} (hu : Summable u) (hu0 : ∀ q, 0 ≤ u q) :
    Tendsto (fun D => ∑' q, if D ≤ q then u q else 0) atTop (𝓝 0) := by
  have h : ∀ D, ∑' q, (if D ≤ q then u q else 0) = ∑' k, u (k + D) := by
    intro D
    have hs : Summable fun q => if D ≤ q then u q else 0 :=
      Summable.of_nonneg_of_le (fun q => by split_ifs <;> simp [hu0])
        (fun q => by split_ifs <;> simp [hu0]) hu
    rw [← hs.sum_add_tsum_nat_add D, Finset.sum_eq_zero fun i hi =>
      if_neg (by rw [Finset.mem_range] at hi; omega), zero_add]
    exact tsum_congr fun k => if_pos (Nat.le_add_left D k)
  simp only [h]
  exact tendsto_sum_nat_add u

/-- `|Π_{p≤D}(1 − χ(p)p^{−s₀})^{−1}| ≤ Z(s₀)`. -/
theorem norm_lowEuler_le {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M) (D : ℕ) {s₀ : ℝ}
    (hs : 1 < s₀) : ‖lowEuler χ D s₀‖ ≤ zetaBound s₀ := by
  have hS : ∀ p ∈ (∅ : Finset ℕ), p.Prime ∧ D < p := fun p hp => absurd hp (Finset.notMem_empty p)
  have hz : ∀ p ∈ (∅ : Finset ℕ), ‖(0 : ℕ → ℂ) p‖ ≤ (p : ℝ) ^ (-s₀) :=
    fun p hp => absurd hp (Finset.notMem_empty p)
  have h := LSeries_charTwist_lowValues χ (D := D) hs hs hS (fun p _ => rfl) hz
  rw [Finset.prod_empty, mul_one] at h
  rw [← h, LSeries_zero_eq_tsum (by simp)]
  have hb : ∀ n : ℕ, ‖χ n * primeValueTwist (lowValues D s₀ 0) n‖ ≤ (n : ℝ) ^ (-s₀) := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp only [Nat.cast_zero, map_zero, mul_zero, norm_zero]; exact Real.rpow_nonneg le_rfl _
    rw [norm_mul]
    refine (mul_le_of_le_one_left (norm_nonneg _) (DirichletCharacter.norm_le_one χ _)).trans ?_
    have := norm_primeValueTwist_le (v := lowValues D s₀ 0) (σ := min s₀ s₀)
      (fun p hp => norm_lowValues_le_rpow (S := ∅) (fun p _ => rfl) hz hp) hn
    rwa [min_self] at this
  have hsb : Summable fun n : ℕ => ‖χ n * primeValueTwist (lowValues D s₀ 0) n‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb (summable_rpow_neg hs)
  exact (norm_tsum_le_tsum_norm hsb).trans (hsb.tsum_le_tsum hb (summable_rpow_neg hs))

/-- `Σ_χ |L(s₀, c_χ) Π_{p≤D}(1 − χ(p)p^{−s₀})^{−1}| ≤ √M · B · Z(s₀)²`. -/
theorem sum_norm_near_le {M : ℕ} [NeZero M] (Ψ : ZMod M → ℂ) {B : ℝ} (hB : ∀ a, ‖Ψ a‖ ≤ B)
    (D : ℕ) {s₀ : ℝ} (hs : 1 < s₀) :
    ∑ χ : DirichletCharacter ℂ M, ‖LSeries (charSmoothCoeff Ψ χ) s₀ * lowEuler χ D s₀‖ ≤
      Real.sqrt M * B * zetaBound s₀ * zetaBound s₀ := by
  calc ∑ χ : DirichletCharacter ℂ M, ‖LSeries (charSmoothCoeff Ψ χ) s₀ * lowEuler χ D s₀‖
      ≤ ∑ χ : DirichletCharacter ℂ M, ‖LSeries (charSmoothCoeff Ψ χ) s₀‖ * zetaBound s₀ :=
        Finset.sum_le_sum fun χ _ => by
          rw [norm_mul]; exact mul_le_mul_of_nonneg_left (norm_lowEuler_le χ D hs) (norm_nonneg _)
    _ = (∑ χ : DirichletCharacter ℂ M, ‖LSeries (charSmoothCoeff Ψ χ) s₀‖) * zetaBound s₀ := by
        rw [Finset.sum_mul]
    _ ≤ Real.sqrt M * B * zetaBound s₀ * zetaBound s₀ :=
        mul_le_mul_of_nonneg_right (sum_norm_LSeries_charSmoothCoeff_le Ψ hB hs)
          (zetaBound_nonneg _)

/-- **Convergence of the near coefficients.** As `D → ∞`, the level-`N₁` coefficients of the
near part tend to `limitCharCoeff`. -/
theorem tendsto_nearCoeff (Ψ : (q : ℕ) → ZMod (q + 1) → ℂ) {B : ℕ → ℝ}
    (hB : ∀ q a, ‖Ψ q a‖ ≤ B q) (hBs : Summable fun q : ℕ => Real.sqrt ((q : ℝ) + 1) * B q)
    {N₁ : ℕ} (ξ : DirichletCharacter ℂ N₁) {s₀ : ℝ} (hs : 1 < s₀) :
    Tendsto (fun D => nearCoeff N₁ D
      (fun q χ => LSeries (charSmoothCoeff (Ψ q) χ) s₀ * lowEuler χ D s₀) ξ) atTop
      (𝓝 (limitCharCoeff Ψ ξ s₀)) := by
  classical
  set Z := zetaBound s₀ with hZ
  have hnear : ∀ D, nearCoeff N₁ D
      (fun q χ => LSeries (charSmoothCoeff (Ψ q) χ) s₀ * lowEuler χ D s₀) ξ =
      ∑' q, if q < D then (∑ χ : DirichletCharacter ℂ (q + 1),
        if DirichletCharacter.changeLevel (dvd_mul_right (q + 1) N₁) χ =
            DirichletCharacter.changeLevel (dvd_mul_left N₁ (q + 1)) ξ then
          LSeries (charSmoothCoeff (Ψ q) χ) s₀ * lowEuler χ D s₀ else 0) else 0 := by
    intro D
    rw [tsum_eq_sum (s := Finset.range D) fun q hq => if_neg (by simpa using hq)]
    unfold nearCoeff
    exact Finset.sum_congr rfl fun q hq => (if_pos (Finset.mem_range.mp hq)).symm
  simp only [hnear]
  unfold limitCharCoeff
  refine tendsto_tsum_of_dominated_convergence
    (bound := fun q => Real.sqrt ((q : ℝ) + 1) * B q * Z * Z) ((hBs.mul_right Z).mul_right Z)
    (fun q => ?_) (Eventually.of_forall fun D q => ?_)
  · have hev : ∀ᶠ D in atTop, (if q < D then (∑ χ : DirichletCharacter ℂ (q + 1),
        if DirichletCharacter.changeLevel (dvd_mul_right (q + 1) N₁) χ =
            DirichletCharacter.changeLevel (dvd_mul_left N₁ (q + 1)) ξ then
          LSeries (charSmoothCoeff (Ψ q) χ) s₀ * lowEuler χ D s₀ else 0) else 0) =
        ∑ χ : DirichletCharacter ℂ (q + 1),
        if DirichletCharacter.changeLevel (dvd_mul_right (q + 1) N₁) χ =
            DirichletCharacter.changeLevel (dvd_mul_left N₁ (q + 1)) ξ then
          LSeries (charSmoothCoeff (Ψ q) χ) s₀ * lowEuler χ D s₀ else 0 :=
      (eventually_gt_atTop q).mono fun D hD => if_pos hD
    refine Tendsto.congr' (Filter.EventuallyEq.symm hev) (tendsto_finsetSum _ fun χ _ => ?_)
    split_ifs
    · exact (tendsto_lowEuler χ hs).const_mul _
    · exact tendsto_const_nhds
  · split_ifs
    · refine (norm_sum_le _ _).trans ((Finset.sum_le_sum (g := fun χ =>
        ‖LSeries (charSmoothCoeff (Ψ q) χ) s₀ * lowEuler χ D s₀‖) fun χ _ => ?_).trans ?_)
      · split_ifs
        · exact le_rfl
        · rw [norm_zero]; exact norm_nonneg _
      · have := sum_norm_near_le (Ψ q) (hB q) D hs
        push_cast at this
        exact this
    · rw [norm_zero]
      have := (hB q 0)
      have h0 : 0 ≤ B q := (norm_nonneg _).trans this
      exact mul_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) h0) (zetaBound_nonneg _))
        (zetaBound_nonneg _)

/-! ## Interchanging the levels and the integers -/

/-- If `exp⋆ℓ(n) = Σ_q Ψ_q(n)` with `|Ψ_q| ≤ B_q` summable, then for an absolutely summable
completely multiplicative `f`, `Σ_n exp⋆ℓ(n) f(n) = Σ_q Σ_n Ψ_q(n) f(n)`. -/
theorem LSeries_limitPeriodic_twist {ℓ : ℕ → ℂ} {Ψ : (q : ℕ) → ZMod (q + 1) → ℂ} {B : ℕ → ℝ}
    (hB : ∀ q a, ‖Ψ q a‖ ≤ B q) (hBsum : Summable B)
    (hΨ : ∀ n : ℕ, n ≠ 0 → dirichletExp ℓ n = ∑' q, Ψ q n) (f : ℕ →*₀ ℂ)
    (hf : Summable fun n => ‖f n‖) :
    LSeries (fun n => dirichletExp ℓ n * f n) 0 = ∑' q, ∑' n : ℕ, Ψ q n * f n := by
  have hB0 : ∀ q, 0 ≤ B q := fun q => (norm_nonneg _).trans (hB q 0)
  rw [LSeries_zero_eq_tsum (by simp)]
  have h1 : ∀ n : ℕ, dirichletExp ℓ n * f n = ∑' q, Ψ q n * f n := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · rw [hΨ n hn, tsum_mul_right]
  simp only [h1]
  have hsum : Summable (Function.uncurry fun (n q : ℕ) => Ψ q n * f n) := by
    refine Summable.of_norm_bounded (Summable.mul_of_nonneg hf hBsum
      (fun n => norm_nonneg _) hB0) fun x => ?_
    simp only [Function.uncurry, norm_mul]
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left (hB x.2 _) (norm_nonneg _)
  exact hsum.tsum_comm.symm

/-! ## The theorem -/

/-- **A limit-periodic Dirichlet exponential carries a single character.** Let `ℓ(0) = ℓ(1) = 0`
with `Σ|ℓ(n)| n^{−σ} < ∞` for every `σ > 1`. Suppose `exp⋆ℓ(n) = Σ_q Ψ_q(n)` for `n ≥ 1`, where
`Ψ_q` has period `q + 1`, `|Ψ_q| ≤ B_q` and `Σ_q √(q+1) B_q < ∞`. Then at every real `s₀ > 1`,
for every level `N`, at most one character mod `N` has a nonzero coefficient
`limitCharCoeff Ψ ξ s₀`. -/
theorem limitPeriodic_exp_single_character {ℓ : ℕ → ℂ} (hℓ0 : ℓ 0 = 0) (hℓ1 : ℓ 1 = 0)
    (hℓ : ∀ σ : ℝ, 1 < σ → LSeriesSummable ℓ σ) {Ψ : (q : ℕ) → ZMod (q + 1) → ℂ}
    {B : ℕ → ℝ} (hB : ∀ q a, ‖Ψ q a‖ ≤ B q)
    (hBs : Summable fun q : ℕ => Real.sqrt ((q : ℝ) + 1) * B q)
    (hΨ : ∀ n : ℕ, n ≠ 0 → dirichletExp ℓ n = ∑' q, Ψ q n)
    {N : ℕ} [NeZero N] {s₀ : ℝ} (hs : 1 < s₀) {ξ₁ ξ₂ : DirichletCharacter ℂ N}
    (h12 : ξ₁ ≠ ξ₂) :
    limitCharCoeff Ψ ξ₁ s₀ = 0 ∨ limitCharCoeff Ψ ξ₂ s₀ = 0 := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨hC1, hC2⟩ := hcon
  set Z := zetaBound s₀ with hZ
  have hZ0 : 0 ≤ Z := zetaBound_nonneg s₀
  have hB0 : ∀ q, 0 ≤ B q := fun q => (norm_nonneg _).trans (hB q 0)
  have hBsum : Summable B := Summable.of_nonneg_of_le hB0
    (fun q => le_mul_of_one_le_left (hB0 q) (Real.one_le_sqrt.mpr
      (le_add_of_nonneg_left (Nat.cast_nonneg q)))) hBs
  set W : ℕ → ℝ := fun q => Real.sqrt ((q : ℝ) + 1) * B q * Z * Z with hW
  have hW0 : ∀ q, 0 ≤ W q := fun q =>
    mul_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (hB0 q)) hZ0) hZ0
  have hWs : Summable W := (hBs.mul_right Z).mul_right Z
  set a : ℕ → (q : ℕ) → DirichletCharacter ℂ (q + 1) → ℂ := fun D q χ =>
    LSeries (charSmoothCoeff (Ψ q) χ) s₀ * lowEuler χ D s₀ with ha
  have hmass : ∀ D q, ∑ χ : DirichletCharacter ℂ (q + 1), ‖a D q χ‖ ≤ W q := by
    intro D q
    have := sum_norm_near_le (Ψ q) (hB q) D hs
    push_cast at this
    exact this
  /- The level `N₁`: all levels `q + 1 ≤ q₀` divide `N₁`, and the rest has mass `≤ |C(ξ₁)|/96`. -/
  set c₁ : ℝ := ‖limitCharCoeff Ψ ξ₁ s₀‖ with hc₁
  have hc₁pos : 0 < c₁ := norm_pos_iff.mpr hC1
  obtain ⟨q₀, hq₀⟩ : ∃ q₀, ∑' q, (if q₀ ≤ q then W q else 0) ≤ c₁ / 96 :=
    ((tendsto_tsum_tail hWs hW0).eventually (ge_mem_nhds (by positivity))).exists
  set N₁ : ℕ := N * q₀.factorial with hN₁
  haveI : NeZero N₁ := ⟨mul_ne_zero (NeZero.ne N) (Nat.factorial_ne_zero q₀)⟩
  have hNN₁ : N ∣ N₁ := dvd_mul_right N _
  have h12' : DirichletCharacter.changeLevel hNN₁ ξ₁ ≠ DirichletCharacter.changeLevel hNN₁ ξ₂ :=
    fun h => h12 (DirichletCharacter.changeLevel_injective hNN₁ h)
  set C : DirichletCharacter ℂ N₁ → ℂ := fun ξ => limitCharCoeff Ψ ξ s₀ with hC
  have hC1' : C (DirichletCharacter.changeLevel hNN₁ ξ₁) ≠ 0 := by
    simp only [hC, limitCharCoeff_changeLevel]; exact hC1
  have hC2' : C (DirichletCharacter.changeLevel hNN₁ ξ₂) ≠ 0 := by
    simp only [hC, limitCharCoeff_changeLevel]; exact hC2
  have hCξ₁ : ‖C (DirichletCharacter.changeLevel hNN₁ ξ₁)‖ = c₁ := by
    simp only [hC, limitCharCoeff_changeLevel, hc₁]
  obtain ⟨η, hη, H⟩ := exists_twoLevel_zero_of_far h12' hC1' hC2'
  /- The cutoff `D`. -/
  have hΔ : Tendsto (fun D => ∑ ξ : DirichletCharacter ℂ N₁, ‖nearCoeff N₁ D (a D) ξ - C ξ‖)
      atTop (𝓝 0) := by
    have h := tendsto_finsetSum (Finset.univ : Finset (DirichletCharacter ℂ N₁)) fun ξ _ =>
      ((tendsto_nearCoeff Ψ hB hBs ξ hs).sub_const (C ξ)).norm
    simp only [hC, sub_self, norm_zero, Finset.sum_const_zero] at h
    exact h
  have htail := (tendsto_tsum_tail hBsum hB0).const_mul (Real.exp (2 * Z))
  rw [mul_zero] at htail
  obtain ⟨D, hDq₀, hDΔ, hDtail⟩ : ∃ D, q₀ ≤ D ∧
      ∑ ξ : DirichletCharacter ℂ N₁, ‖nearCoeff N₁ D (a D) ξ - C ξ‖ ≤ η / 2 ∧
      Real.exp (2 * Z) * ∑' q, (if D ≤ q then B q else 0) ≤ η / 2 :=
    ((eventually_ge_atTop q₀).and ((hΔ.eventually (ge_mem_nhds (half_pos hη))).and
      (htail.eventually (ge_mem_nhds (half_pos hη))))).exists
  /- The level `N'` and the band. -/
  set N' : ℕ := N₁ * D.factorial with hN'
  haveI : NeZero N' := ⟨mul_ne_zero (NeZero.ne N₁) (Nat.factorial_ne_zero D)⟩
  have hN₁N' : N₁ ∣ N' := dvd_mul_right N₁ _
  have hqN' : ∀ q < D, (q + 1) * N₁ ∣ N' := fun q hq => by
    rw [hN', mul_comm N₁]
    exact Nat.mul_dvd_mul_right (Nat.dvd_factorial (Nat.succ_pos q) hq) N₁
  have hDc : ∀ ψ, bandCoeff N₁ N' D (a D) ψ ≠ 0 → ¬ ψ.FactorsThrough N₁ := fun ψ h hft =>
    h (by simp only [bandCoeff, if_pos hft])
  have hDsum : ∑ ψ, ‖bandCoeff N₁ N' D (a D) ψ‖ ≤
      ‖C (DirichletCharacter.changeLevel hNN₁ ξ₁)‖ / 96 := by
    rw [hCξ₁]
    refine (sum_norm_bandCoeff_le hN₁N' (a D)).trans (le_trans ?_ hq₀)
    have hsW : Summable fun q => if q₀ ≤ q then W q else 0 :=
      Summable.of_nonneg_of_le (fun q => by split_ifs <;> simp [hW0])
        (fun q => by split_ifs <;> simp [hW0]) hWs
    refine le_trans (Finset.sum_le_sum fun q _ => ?_)
      (hsW.sum_le_tsum (Finset.range D) fun q _ => by split_ifs <;> simp [hW0])
    split_ifs with h1 h2 h2
    · exact hW0 q
    · exact le_rfl
    · exact hmass D q
    · exfalso
      apply h1
      exact (Nat.dvd_factorial (Nat.succ_pos q) (by omega)).trans (dvd_mul_left _ N)
  /- The far part. -/
  have hX : ∀ (S : Finset ℕ) (v : ℕ → ℂ), (∀ p, p ∉ S → v p = 0) → (∀ p ∈ S, ‖v p‖ ≤ 1 / 2) →
      ∀ q, ‖∑' k : ℕ, Ψ q k * primeValueTwist (lowValues D s₀ v) k‖ ≤
        B q * (Real.exp (2 * Z) * Real.exp (2 * ∑ p ∈ S, ‖v p‖)) := by
    intro S v hv0 hv q
    obtain ⟨h1, h2, h3⟩ := lowValues_support (D := D) hs hv0 hv
    obtain ⟨-, hle⟩ := norm_tsum_mul_primeValueTwist_le (τ := fun k : ℕ => Ψ q k)
      (fun k => hB q k) h1 h2
    refine hle.trans ?_
    rw [← Real.exp_add]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (hB0 q)
  set Φ : Finset ℕ → (ℕ → ℂ) → ℂ := fun S v =>
    ∑ ξ : DirichletCharacter ℂ N₁, (nearCoeff N₁ D (a D) ξ - C ξ) * ∏ p ∈ S, (1 - ξ p * v p)⁻¹ +
      ∑' q, (if D ≤ q then ∑' k : ℕ, Ψ q k * primeValueTwist (lowValues D s₀ v) k else 0)
    with hΦ
  have hΦb : ∀ (S : Finset ℕ) (v : ℕ → ℂ), (∀ p, p ∉ S → v p = 0) →
      (∀ p ∈ S, ‖v p‖ ≤ 1 / 2) → ‖Φ S v‖ ≤ η * Real.exp (2 * ∑ p ∈ S, ‖v p‖) := by
    intro S v hv0 hv
    set E := Real.exp (2 * ∑ p ∈ S, ‖v p‖) with hE
    have hE0 : 0 ≤ E := (Real.exp_pos _).le
    have hfirst : ‖∑ ξ : DirichletCharacter ℂ N₁,
        (nearCoeff N₁ D (a D) ξ - C ξ) * ∏ p ∈ S, (1 - ξ p * v p)⁻¹‖ ≤ η / 2 * E := by
      refine (norm_sum_le _ _).trans ?_
      calc ∑ ξ : DirichletCharacter ℂ N₁,
            ‖(nearCoeff N₁ D (a D) ξ - C ξ) * ∏ p ∈ S, (1 - ξ p * v p)⁻¹‖
          ≤ ∑ ξ : DirichletCharacter ℂ N₁, ‖nearCoeff N₁ D (a D) ξ - C ξ‖ * E :=
            Finset.sum_le_sum fun ξ _ => by
              rw [norm_mul]
              exact mul_le_mul_of_nonneg_left (norm_prod_inv_one_sub_le
                (fun p => DirichletCharacter.norm_le_one ξ _) hv).1 (norm_nonneg _)
        _ = (∑ ξ : DirichletCharacter ℂ N₁, ‖nearCoeff N₁ D (a D) ξ - C ξ‖) * E := by
            rw [Finset.sum_mul]
        _ ≤ η / 2 * E := mul_le_mul_of_nonneg_right hDΔ hE0
    have hsec : ‖∑' q, (if D ≤ q then
        ∑' k : ℕ, Ψ q k * primeValueTwist (lowValues D s₀ v) k else 0)‖ ≤ η / 2 * E := by
      have hbq : ∀ q, ‖(if D ≤ q then
          ∑' k : ℕ, Ψ q k * primeValueTwist (lowValues D s₀ v) k else 0)‖ ≤
          (if D ≤ q then B q else 0) * (Real.exp (2 * Z) * E) := by
        intro q; split_ifs
        · exact hX S v hv0 hv q
        · rw [norm_zero, zero_mul]
      have hsB : Summable fun q => (if D ≤ q then B q else 0) * (Real.exp (2 * Z) * E) :=
        (Summable.of_nonneg_of_le (fun q => by split_ifs <;> simp [hB0])
          (fun q => by split_ifs <;> simp [hB0]) hBsum).mul_right _
      have hsn := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hbq hsB
      refine (norm_tsum_le_tsum_norm hsn).trans ((hsn.tsum_le_tsum hbq hsB).trans ?_)
      rw [tsum_mul_right]
      calc (∑' q, if D ≤ q then B q else 0) * (Real.exp (2 * Z) * E) =
            Real.exp (2 * Z) * (∑' q, if D ≤ q then B q else 0) * E := by ring
        _ ≤ η / 2 * E := mul_le_mul_of_nonneg_right hDtail hE0
    calc ‖Φ S v‖ ≤ η / 2 * E + η / 2 * E := (norm_add_le _ _).trans (add_le_add hfirst hsec)
      _ = η * E := by ring
  have hΦd : ∀ (S : Finset ℕ) (zt : ℂ → ℕ → ℂ) (U : Set ℂ), IsOpen U →
      (∀ p, Differentiable ℂ (fun t => zt t p)) → (∀ t ∈ U, ∀ p, p ∉ S → zt t p = 0) →
      (∀ t ∈ U, ∀ p ∈ S, ‖zt t p‖ ≤ 1 / 2) → DifferentiableOn ℂ (fun t => Φ S (zt t)) U := by
    intro S zt U hU hd hz0 hz
    have hd1 : DifferentiableOn ℂ (fun t => ∑ ξ : DirichletCharacter ℂ N₁,
        (nearCoeff N₁ D (a D) ξ - C ξ) * ∏ p ∈ S, (1 - ξ p * zt t p)⁻¹) U := by
      intro t ht
      refine (DifferentiableAt.fun_sum fun ξ _ => (differentiableAt_const _).mul
        (differentiableAt_prod_inv hd fun p hp => ?_)).differentiableWithinAt
      rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) (DirichletCharacter.norm_le_one ξ _)).trans
        (hz t ht p hp)
    have hlowd : ∀ p, Differentiable ℂ fun t => lowValues D s₀ (zt t) p := fun p => by
      unfold lowValues; split_ifs
      · exact differentiable_const _
      · exact hd p
    have hd2 : DifferentiableOn ℂ (fun t => ∑' q, (if D ≤ q then
        ∑' k : ℕ, Ψ q k * primeValueTwist (lowValues D s₀ (zt t)) k else 0)) U := by
      refine Complex.differentiableOn_tsum_of_summable_norm
        (u := fun q => B q * (Real.exp (2 * Z) * Real.exp (S.card : ℝ))) (hBsum.mul_right _)
        (fun q => ?_) hU (fun q t ht => ?_)
      · split_ifs
        · exact differentiableOn_tsum_mul_primeValueTwist (τ := fun k : ℕ => Ψ q k)
            (fun k => hB q k) hU hlowd
            (fun t ht => (lowValues_support (D := D) hs (hz0 t ht) (hz t ht)).1)
            (fun t ht => (lowValues_support (D := D) hs (hz0 t ht) (hz t ht)).2.1)
        · exact differentiableOn_const _
      · split_ifs
        · refine (hX S (zt t) (hz0 t ht) (hz t ht) q).trans
            (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
              (Real.exp_le_exp.mpr ?_) (Real.exp_pos _).le) (hB0 q))
          have hle : ∑ p ∈ S, ‖zt t p‖ ≤ ∑ _p ∈ S, (1 / 2 : ℝ) :=
            Finset.sum_le_sum fun p hp => hz t ht p hp
          rw [Finset.sum_const, nsmul_eq_mul] at hle
          linarith
        · rw [norm_zero]
          exact mul_nonneg (hB0 q) (by positivity)
    exact hd1.add hd2
  /- Planting. -/
  obtain ⟨σ, hσ, S, hSmem, z, hz, hz0, hzero⟩ :=
    H N' hN₁N' D (bandCoeff N₁ N' D (a D)) hDc hDsum Φ hΦb hΦd
  have hSD : ∀ p ∈ S, p.Prime ∧ D < p := fun p hp => ⟨(hSmem p hp).1, (hSmem p hp).2.2⟩
  have hSu : ∀ p ∈ S, IsUnit (p : ZMod N') := fun p hp => (hSmem p hp).2.1
  have hσ' : 1 < min σ s₀ := lt_min hσ hs
  have hf_norm : ∀ n, n ≠ 0 →
      ‖primeValueTwist (lowValues D s₀ z) n‖ ≤ (n : ℝ) ^ (-min σ s₀) := fun n hn =>
    norm_primeValueTwist_le (fun p hp => norm_lowValues_le_rpow hz0 hz hp) hn
  have hfsum : Summable fun n => ‖primeValueTwist (lowValues D s₀ z) n‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => by
      rcases eq_or_ne n 0 with rfl | hn
      · simp only [map_zero, norm_zero, Nat.cast_zero]; exact Real.rpow_nonneg le_rfl _
      · exact hf_norm n hn) (summable_rpow_neg hσ')
  have hsumℓ : LSeriesSummable (fun n => ℓ n * primeValueTwist (lowValues D s₀ z) n) 0 := by
    refine Summable.of_norm_bounded (summable_norm_iff.mpr (hℓ (min σ s₀) hσ')) fun n => ?_
    rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
    split_ifs with hn
    · rfl
    · rw [norm_mul, Complex.zero_re, Real.rpow_zero, div_one, ofReal_re, div_eq_mul_inv,
        ← Real.rpow_neg (Nat.cast_nonneg n)]
      exact mul_le_mul_of_nonneg_left (hf_norm n hn) (norm_nonneg _)
  apply tsum_dirichletExp_twist_ne_zero hℓ0 hℓ1 _ hsumℓ
  rw [LSeries_limitPeriodic_twist hB hBsum hΨ _ hfsum]
  /- Split the levels at `D`. -/
  have hXs : Summable fun q => ∑' n : ℕ, Ψ q n * primeValueTwist (lowValues D s₀ z) n := by
    refine Summable.of_norm_bounded (hBsum.mul_right (∑' n, ‖primeValueTwist (lowValues D s₀ z) n‖))
      fun q => ?_
    have hs1 : Summable fun n : ℕ => ‖Ψ q n * primeValueTwist (lowValues D s₀ z) n‖ :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => by
        rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hB q n) (norm_nonneg _))
        (hfsum.mul_left (B q))
    refine (norm_tsum_le_tsum_norm hs1).trans ?_
    rw [← tsum_mul_left]
    exact hs1.tsum_le_tsum (fun n => by
      rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hB q n) (norm_nonneg _))
      (hfsum.mul_left (B q))
  have hsplit : ∑' q, ∑' n : ℕ, Ψ q n * primeValueTwist (lowValues D s₀ z) n =
      ∑ q ∈ Finset.range D, ∑' n : ℕ, Ψ q n * primeValueTwist (lowValues D s₀ z) n +
        ∑' q, (if D ≤ q then
          ∑' n : ℕ, Ψ q n * primeValueTwist (lowValues D s₀ z) n else 0) := by
    have e : ∀ q, ∑' n : ℕ, Ψ q n * primeValueTwist (lowValues D s₀ z) n =
        (if q < D then ∑' n : ℕ, Ψ q n * primeValueTwist (lowValues D s₀ z) n else 0) +
          (if D ≤ q then ∑' n : ℕ, Ψ q n * primeValueTwist (lowValues D s₀ z) n else 0) :=
      fun q => by
        by_cases h : q < D
        · rw [if_pos h, if_neg (by omega), add_zero]
        · rw [if_neg h, if_pos (by omega), zero_add]
    have hs1 : Summable fun q => if q < D then
        ∑' n : ℕ, Ψ q n * primeValueTwist (lowValues D s₀ z) n else 0 :=
      Summable.of_norm_bounded hXs.norm fun q => by split_ifs <;> simp
    have hs2 : Summable fun q => if D ≤ q then
        ∑' n : ℕ, Ψ q n * primeValueTwist (lowValues D s₀ z) n else 0 :=
      Summable.of_norm_bounded hXs.norm fun q => by split_ifs <;> simp
    rw [tsum_congr e, hs1.tsum_add hs2,
      tsum_eq_sum (s := Finset.range D) fun q hq => if_neg (by simpa using hq)]
    congr 1
    exact Finset.sum_congr rfl fun q hq => if_pos (Finset.mem_range.mp hq)
  /- The near part. -/
  have hnear : ∑ q ∈ Finset.range D, ∑' n : ℕ, Ψ q n * primeValueTwist (lowValues D s₀ z) n =
      ∑ q ∈ Finset.range D, ∑ χ : DirichletCharacter ℂ (q + 1),
        a D q χ * ∏ p ∈ S, (1 - χ p * z p)⁻¹ := by
    refine Finset.sum_congr rfl fun q hq => ?_
    have h := LSeries_periodic_twist_lowValues (Ψ q) (Finset.mem_range.mp hq) hs hσ hSD hz0 hz
    rw [LSeries_zero_eq_tsum (by simp)] at h
    rw [h]
    exact Finset.sum_congr rfl fun χ _ => by simp only [ha]; ring
  have hCsplit : ∑ ξ : DirichletCharacter ℂ N₁,
      nearCoeff N₁ D (a D) ξ * ∏ p ∈ S, (1 - ξ p * z p)⁻¹ =
      ∑ ξ : DirichletCharacter ℂ N₁, C ξ * ∏ p ∈ S, (1 - ξ p * z p)⁻¹ +
        ∑ ξ : DirichletCharacter ℂ N₁, (nearCoeff N₁ D (a D) ξ - C ξ) *
          ∏ p ∈ S, (1 - ξ p * z p)⁻¹ := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun ξ _ => by ring
  rw [hsplit, hnear, sum_near_regroup hN₁N' hqN' (a D) hSu z, hCsplit]
  simp only [hΦ] at hzero
  linear_combination hzero

end

end CharacterZeroPlanting

end RHTower
