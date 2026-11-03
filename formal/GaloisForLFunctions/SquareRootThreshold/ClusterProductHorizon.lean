import GaloisForLFunctions.SquareRootThreshold.ClusterProductWeilDetector
import GaloisForLFunctions.SquareRootThreshold.SmoothWeilDetectorPolynomialAperture

/-!
# The cluster horizon with one logarithm

Retaining root-distance products changes the required aperture from
`O(n log² R + log |γ|)` to `O(n log R + log |γ|)`.
-/

open Complex MeasureTheory Real Set Filter Topology
open scoped ComplexConjugate BigOperators
noncomputable section
namespace SquareRootThreshold
open RHTower Zeta23

/-- The product scale is at least the inverse eighth power of the aperture. -/
theorem clusterProductScale_ge {δ a : ℝ} {N₀ n : ℕ} (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2)
    (ha6 : Real.exp 6 ≤ a) (haδ : 1 / δ ≤ a) (hN : (N₀ : ℝ) ≤ a)
    (hn : (n : ℝ) + 1 ≤ a) : Real.exp (-(8 * Real.log a)) ≤ clusterProductScale δ N₀ n := by
  obtain ⟨-, -, he6, -, -, -⟩ := exp_numeric_bounds
  have ha400 : (400 : ℝ) ≤ a := he6.trans ha6
  have ha0 : 0 < a := by linarith
  set D := 100 * (3 * (N₀ : ℝ) + 3) * (16 * (100 * ((n : ℝ) + 1))) ^ 2 with hD
  have hD0 : 0 < D := by rw [hD]; positivity
  have hDa : D ≤ a ^ 7 := by
    have hN' : 100 * (3 * (N₀ : ℝ) + 3) ≤ 600 * a := by linarith
    have hn' : 16 * (100 * ((n : ℝ) + 1)) ≤ 1600 * a := by linarith
    have hconst : (1536000000 : ℝ) ≤ a ^ 4 := by
      have hpow := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 400) ha400 4
      norm_num at hpow
      linarith
    calc D ≤ 600 * a * (1600 * a) ^ 2 := by
            rw [hD]
            exact mul_le_mul hN' (pow_le_pow_left₀ (by positivity) hn' 2)
              (by positivity) (by positivity)
      _ = 1536000000 * a ^ 3 := by ring
      _ ≤ a ^ 4 * a ^ 3 := mul_le_mul_of_nonneg_right hconst (by positivity)
      _ = a ^ 7 := by ring
  have hδa : 1 ≤ δ * a := by
    have := (div_le_iff₀ hδ).mp haδ
    nlinarith
  have hexp : Real.exp (-(8 * Real.log a)) = 1 / a ^ 8 := by
    rw [Real.exp_neg, show (8 : ℝ) * Real.log a = ((8 : ℕ) : ℝ) * Real.log a by norm_num,
      Real.exp_nat_mul, Real.exp_log ha0, one_div]
  have hscale : clusterProductScale δ N₀ n = δ / D := by
    unfold clusterProductScale lowHeightEps0 lowHeightScale
    rw [min_eq_left (by linarith : δ ≤ 1), hD]
    field_simp
  rw [hexp, hscale, div_le_div_iff₀ (by positivity) hD0, one_mul]
  calc D ≤ a ^ 7 := hDa
    _ ≤ (δ * a) * a ^ 7 := le_mul_of_one_le_left (by positivity) hδa
    _ = δ * a ^ 8 := by ring

/-- The size condition pays the product loss and the split tail. -/
theorem cluster_product_horizon_linear {a ℓ Λ : ℝ} {n N₀ : ℕ} (hℓ6 : 6 ≤ ℓ) (hΛ0 : 0 ≤ Λ)
    (hsize : 100 * (((n : ℝ) + 1) * ℓ + Λ) ≤ a) (hN : a - 1 < N₀) :
    (n : ℝ) + 1 ≤ a ∧ 2 * n + 7 ≤ N₀ ∧
      ((8 * n + 15 : ℕ) : ℝ) * 5 + (4 + 5 * Λ) <
        ((2 * N₀ : ℕ) : ℝ) * 2 + ((8 * n : ℕ) : ℝ) * (-(8 * ℓ)) +
          ((4 : ℕ) : ℝ) * (-ℓ - 1) := by
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hnl : 6 * ((n : ℝ) + 1) ≤ ((n : ℝ) + 1) * ℓ := by nlinarith
  refine ⟨by nlinarith, ?_, ?_⟩
  · have : ((2 * n + 7 : ℕ) : ℝ) < N₀ := by push_cast; nlinarith
    exact_mod_cast this.le
  · push_cast
    nlinarith

/-- The three multiplicative lower bounds combine without a smallest-distance loss. -/
theorem cluster_product_horizon_lower {B U κ δ ℓ : ℝ} {n N₀ : ℕ} (hκ0 : 0 ≤ κ)
    (hBQ : B ^ (2 * N₀) * Real.exp (((2 * N₀ : ℕ) : ℝ) * 2) ≤ (101 : ℝ) ^ (4 * N₀) * U ^ (2 * N₀))
    (hκ8 : Real.exp (((8 * n : ℕ) : ℝ) * (-(8 * ℓ))) ≤ κ ^ (8 * n))
    (hδ4 : Real.exp (((4 : ℕ) : ℝ) * (-ℓ - 1)) ≤ (δ / 2) ^ 4) (hU : 0 ≤ U) :
    B ^ (2 * N₀) * Real.exp (((2 * N₀ : ℕ) : ℝ) * 2 + ((8 * n : ℕ) : ℝ) * (-(8 * ℓ)) +
        ((4 : ℕ) : ℝ) * (-ℓ - 1)) ≤
      (101 : ℝ) ^ (4 * N₀) * U ^ (2 * N₀) * κ ^ (8 * n) * (δ / 2) ^ 4 := by
  rw [Real.exp_add, Real.exp_add, ← mul_assoc, ← mul_assoc]
  have h2 : 0 ≤ Real.exp (((8 * n : ℕ) : ℝ) * (-(8 * ℓ))) := (Real.exp_pos _).le
  have h3 : 0 ≤ Real.exp (((4 : ℕ) : ℝ) * (-ℓ - 1)) := (Real.exp_pos _).le
  have h4 : 0 ≤ (101 : ℝ) ^ (4 * N₀) * U ^ (2 * N₀) := by positivity
  have h5 : 0 ≤ κ ^ (8 * n) := pow_nonneg hκ0 _
  exact mul_le_mul (mul_le_mul hBQ hκ8 h2 h4) hδ4 h3 (mul_nonneg h4 h5)

/-- The one-logarithm size condition dominates the full tail at `H=100`. -/
theorem cluster_product_horizon_condition {A₀ G δ a : ℝ} (hA₀ : 1 ≤ A₀) (hG : 0 ≤ G) (hδ : 0 < δ)
    (hδ2 : δ ≤ 1 / 2) (ha6 : Real.exp 6 ≤ a) (haδ : 1 / δ ≤ a) {n : ℕ}
    (hsize : 100 * (((n : ℝ) + 1) * Real.log a + Real.log (A₀ * (G + 4))) ≤ a) :
    2 * n + 7 ≤ ⌊a⌋₊ ∧
      clusterTailConstant 100 (G + 1) ⌊a⌋₊ n * (24 * A₀ * Real.log (G + 4)) <
        79 / 50 * (1 + 100) ^ (4 * ⌊a⌋₊ - 4 * n - 11) * clusterProductFloor δ ⌊a⌋₊ n := by
  obtain ⟨e5, -, e6, -, e2, e1⟩ := exp_numeric_bounds
  set N₀ := ⌊a⌋₊ with hN₀def
  set ℓ := Real.log a with hℓ
  set Λ := Real.log (A₀ * (G + 4)) with hΛ
  have ha0 : 0 < a := lt_of_lt_of_le (Real.exp_pos 6) ha6
  have hℓ6 : 6 ≤ ℓ := by
    have := Real.log_le_log (Real.exp_pos 6) ha6; rwa [Real.log_exp] at this
  have hΛ0 : 0 ≤ Λ := Real.log_nonneg (by nlinarith)
  have hN₀a : (N₀ : ℝ) ≤ a := Nat.floor_le ha0.le
  have hN₀a' : a - 1 < N₀ := Nat.sub_one_lt_floor a
  obtain ⟨hn1, h2n7, hlin⟩ := cluster_product_horizon_linear (N₀ := N₀) hℓ6 hΛ0 hsize hN₀a'
  refine ⟨h2n7, ?_⟩
  have hκ := clusterProductScale_ge hδ hδ2 ha6 haδ hN₀a hn1
  set κ := clusterProductScale δ N₀ n with hκdef
  have hκ0 : 0 ≤ κ := (Real.exp_pos _).le.trans hκ
  set U := unitWeightFloor with hUdef
  have hU := unitWeightFloor_ge
  set B := Real.exp (1 / 2) * 168 with hBdef
  have hB0 : 0 < B := by positivity
  have hB : B ≤ 336 := by rw [hBdef]; nlinarith [exp_one_half_lt_two]
  -- the five estimates
  have hX := tail_prefactor_le_exp hA₀ hG
  have h101 : (101 : ℝ) ^ (4 * n + 4) * (101 : ℝ) ^ (4 * n + 11) ≤
      Real.exp (((8 * n + 15 : ℕ) : ℝ) * 5) := by
    have e : (101 : ℝ) ^ (4 * n + 4) * (101 : ℝ) ^ (4 * n + 11) = (101 : ℝ) ^ (8 * n + 15) := by
      rw [← pow_add]; congr 1; ring
    rw [e, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by norm_num) e5 _
  have hδ4 : Real.exp (((4 : ℕ) : ℝ) * (-ℓ - 1)) ≤ (δ / 2) ^ 4 := by
    rw [Real.exp_nat_mul]
    apply pow_le_pow_left₀ (Real.exp_pos _).le
    have hδe : Real.exp (-ℓ) ≤ δ := by
      rw [Real.exp_neg, Real.exp_log ha0]
      rw [div_le_iff₀ hδ] at haδ
      rw [inv_le_iff_one_le_mul₀ ha0]; linarith
    rw [sub_eq_add_neg, Real.exp_add, Real.exp_neg 1]
    have : (Real.exp 1)⁻¹ ≤ 1 / 2 := by
      rw [inv_le_iff_one_le_mul₀ (Real.exp_pos 1)]; linarith
    nlinarith [Real.exp_pos (-ℓ)]
  have hκ8 : Real.exp (((8 * n : ℕ) : ℝ) * (-(8 * ℓ))) ≤ κ ^ (8 * n) := by
    rw [Real.exp_nat_mul]; exact pow_le_pow_left₀ (Real.exp_pos _).le hκ _
  have hBQ : B ^ (2 * N₀) * Real.exp (((2 * N₀ : ℕ) : ℝ) * 2) ≤
      (101 : ℝ) ^ (4 * N₀) * U ^ (2 * N₀) := by
    have e : (101 : ℝ) ^ (4 * N₀) * U ^ (2 * N₀) = ((101 : ℝ) ^ 2 * U) ^ (2 * N₀) := by
      rw [mul_pow, ← pow_mul]; ring_nf
    rw [Real.exp_nat_mul, ← mul_pow, e]
    apply pow_le_pow_left₀ (by positivity)
    nlinarith [Real.exp_pos 2]
  have hsplit : (1 + 100 : ℝ) ^ (4 * N₀ - 4 * n - 11) * (101 : ℝ) ^ (4 * n + 11) =
      (101 : ℝ) ^ (4 * N₀) := by
    rw [show (1 + 100 : ℝ) = 101 by norm_num, ← pow_add]; congr 1; omega
  -- assembly
  unfold clusterTailConstant clusterProductFloor
  rw [← hBdef, ← hκdef, ← hUdef, show (100 : ℝ) + 1 = 101 by norm_num,
    show G + 1 + 1 = G + 1 + 1 from rfl]
  have hpos : (0 : ℝ) < 101 ^ (4 * n + 11) := by positivity
  refine lt_of_mul_lt_mul_right ?_ hpos.le
  calc B ^ (2 * N₀) * 101 ^ (4 * n + 4) * (G + 1 + 1) ^ 4 * (24 * A₀ * Real.log (G + 4)) *
        101 ^ (4 * n + 11)
      = B ^ (2 * N₀) * (101 ^ (4 * n + 4) * 101 ^ (4 * n + 11)) *
          ((G + 1 + 1) ^ 4 * (24 * A₀ * Real.log (G + 4))) := by ring
    _ ≤ B ^ (2 * N₀) * Real.exp (((8 * n + 15 : ℕ) : ℝ) * 5) * Real.exp (4 + 5 * Λ) := by
        have : 0 ≤ (G + 1 + 1) ^ 4 * (24 * A₀ * Real.log (G + 4)) := by
          have := Real.log_nonneg (show (1 : ℝ) ≤ G + 4 by linarith)
          have : (0 : ℝ) ≤ A₀ := by linarith
          positivity
        gcongr
    _ = B ^ (2 * N₀) * Real.exp (((8 * n + 15 : ℕ) : ℝ) * 5 + (4 + 5 * Λ)) := by
        rw [mul_assoc, ← Real.exp_add]
    _ < B ^ (2 * N₀) * Real.exp (((2 * N₀ : ℕ) : ℝ) * 2 + ((8 * n : ℕ) : ℝ) * (-(8 * ℓ)) +
          ((4 : ℕ) : ℝ) * (-ℓ - 1)) := by
        gcongr
    _ ≤ (101 : ℝ) ^ (4 * N₀) * U ^ (2 * N₀) * κ ^ (8 * n) * (δ / 2) ^ 4 :=
        cluster_product_horizon_lower hκ0 hBQ hκ8 hδ4 unitWeightFloor_pos.le
    _ ≤ 79 / 50 * ((1 + 100) ^ (4 * N₀ - 4 * n - 11) * 101 ^ (4 * n + 11)) *
          (U ^ (2 * N₀) * κ ^ (8 * n) * (δ / 2) ^ 4) := by
        rw [hsplit]
        have hX0 : 0 ≤ (101 : ℝ) ^ (4 * N₀) * (U ^ (2 * N₀) * κ ^ (8 * n) * (δ / 2) ^ 4) :=
          mul_nonneg (pow_nonneg (by norm_num) _) (mul_nonneg (mul_nonneg
            (pow_nonneg unitWeightFloor_pos.le _) (pow_nonneg hκ0 _)) (pow_nonneg (by linarith) _))
        calc (101 : ℝ) ^ (4 * N₀) * U ^ (2 * N₀) * κ ^ (8 * n) * (δ / 2) ^ 4
            = 1 * ((101 : ℝ) ^ (4 * N₀) * (U ^ (2 * N₀) * κ ^ (8 * n) * (δ / 2) ^ 4)) := by ring
          _ ≤ 79 / 50 * ((101 : ℝ) ^ (4 * N₀) * (U ^ (2 * N₀) * κ ^ (8 * n) * (δ / 2) ^ 4)) :=
              mul_le_mul_of_nonneg_right (by norm_num) hX0
          _ = _ := by ring
    _ = 79 / 50 * (1 + 100) ^ (4 * N₀ - 4 * n - 11) *
          (U ^ (2 * N₀) * κ ^ (8 * n) * (δ / 2) ^ 4) * 101 ^ (4 * n + 11) := by ring

/-- An off-line zero defeats the Hodge index once the aperture pays `n log a`. -/
theorem not_hodgeIndex_below_cluster_product_horizon (Z : ZeroConfig) {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3))
    {ρ₀ : ℂ} (hρ₀ : ρ₀ ∈ Z.carrier) {δ : ℝ} (hδ : 0 < δ) (hre : δ ≤ |ρ₀.re - 1 / 2|)
    (hγ : 2 ≤ |ρ₀.im|) {a : ℝ} (ha6 : Real.exp 6 ≤ a) (haδ : 1 / δ ≤ a) {n : ℕ}
    (hn : Z.Nd (ρ₀.im - 101) (ρ₀.im + 101) ≤ n)
    (hsize : 100 * (((n : ℝ) + 1) * Real.log a + Real.log (A₀ * (|ρ₀.im| + 4))) ≤ a) :
    ¬ HodgeIndexAtLevel Z a := by
  intro hodge
  -- the zero of the pair to the right of the critical line
  obtain ⟨σ, hσ, hσre, hσim⟩ : ∃ σ ∈ Z.carrier, σ.re = 1 / 2 + |ρ₀.re - 1 / 2| ∧
      σ.im = ρ₀.im := by
    rcases le_or_gt (1 / 2) ρ₀.re with h | h
    · exact ⟨ρ₀, hρ₀, by rw [abs_of_nonneg (by linarith)]; ring, rfl⟩
    · refine ⟨reflect ρ₀, Z.reflect_mem ρ₀ hρ₀, ?_, Tail.reflect_im ρ₀⟩
      rw [abs_of_neg (by linarith)]
      simp only [reflect, Complex.sub_re, Complex.one_re, Complex.conj_re]; ring
  set δ' := |ρ₀.re - 1 / 2| with hδ'
  have hδ'0 : 0 < δ' := lt_of_lt_of_le hδ hre
  have hst := Z.strip σ hσ
  have hδ'2 : δ' ≤ 1 / 2 := by linarith [hst.2]
  have haδ' : 1 / δ' ≤ a := le_trans (one_div_le_one_div_of_le hδ hre) haδ
  have ha0 : 0 < a := lt_of_lt_of_le (Real.exp_pos 6) ha6
  obtain ⟨h2n7, hbig⟩ := cluster_product_horizon_condition hA₀ (abs_nonneg σ.im) hδ'0 hδ'2 ha6 haδ'
    (n := n) (by rw [hσim]; exact hsize)
  have hn' : (Z.finite_window (σ.im - (100 + 1)) (σ.im + (100 + 1))).toFinset.card ≤ n := by
    have e : (Z.finite_window (σ.im - (100 + 1)) (σ.im + (100 + 1))).toFinset.card =
        Z.Nd (σ.im - (100 + 1)) (σ.im + (100 + 1)) :=
      (Set.ncard_eq_toFinset_card (Z.window _ _) (Z.finite_window _ _)).symm
    rw [e, hσim, show (100 : ℝ) + 1 = 101 by norm_num]
    exact hn
  obtain ⟨f, hf, hfs, hp, hm, hneg⟩ := exists_hodge_violation_cluster_product Z hA₀ hloc hσ hδ'0
    hσre (by rw [hσim]; exact hγ) (H := 100) (by norm_num) (Nat.floor_le ha0.le) hn' h2n7
    (by rw [hσim] at hbig ⊢; exact hbig)
  exact absurd (hodge f hf hfs hp hm) (not_le.mpr hneg)

/-- For ζ, aperture `a` detects depth `1/a` up to height `exp(a/(10⁵ A₀ log a))−306`. -/
theorem zeta_hodge_index_cluster_product_horizon :
    ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ δ : ℝ, 0 < δ → ∀ ρ ∈ zetaZeroConfig.carrier, δ ≤ |ρ.re - 1 / 2| →
      2 ≤ |ρ.im| → ∀ a : ℝ, Real.exp 6 ≤ a → 1 / δ ≤ a →
        10 ^ 5 * A₀ * Real.log (|ρ.im| + 306) * Real.log a ≤ a →
        ¬ HodgeIndexAtLevel zetaZeroConfig a := by
  obtain ⟨A₀, hA₀, hloc⟩ := Zeta23.RvM.zetaZeroConfig_local_count
  refine ⟨A₀, hA₀, fun δ hδ ρ hρ hre hγ a ha6 haδ hsize => ?_⟩
  set L := Real.log (|ρ.im| + 306) with hL
  set ℓ := Real.log a with hℓ
  have ha0 : 0 < a := lt_of_lt_of_le (Real.exp_pos 6) ha6
  have hℓ0 : 1 ≤ ℓ := by
    have := Real.log_le_log (Real.exp_pos 6) ha6
    rw [Real.log_exp] at this; linarith
  have hL1 : 1 ≤ L := by
    rw [hL, ← Real.log_exp 1]
    apply Real.log_le_log (Real.exp_pos 1)
    obtain ⟨-, -, -, -, -, -⟩ := exp_numeric_bounds
    have := Real.exp_one_lt_d9
    linarith [abs_nonneg ρ.im]
  have hcount := Nd_le_of_local_count zetaZeroConfig hA₀ hloc (ρ.im - 101) 202
  have hwin : ρ.im - 101 + ((202 : ℕ) : ℝ) = ρ.im + 101 := by push_cast; ring
  rw [hwin] at hcount
  have hcountL : (zetaZeroConfig.Nd (ρ.im - 101) (ρ.im + 101) : ℝ) ≤ 202 * (A₀ * L) := by
    refine hcount.trans ?_
    have hlog : Real.log (|ρ.im - 101| + ((202 : ℕ) : ℝ) + 3) ≤ L := by
      rw [hL]
      apply Real.log_le_log (by positivity)
      have := abs_sub (ρ.im) 101
      push_cast; norm_num at this ⊢; linarith
    have hA0 : 0 ≤ A₀ := by linarith
    push_cast at hlog ⊢
    gcongr
  refine not_hodgeIndex_below_cluster_product_horizon zetaZeroConfig hA₀ hloc hρ hδ hre hγ ha6 haδ
    (n := zetaZeroConfig.Nd (ρ.im - 101) (ρ.im + 101)) le_rfl ?_
  -- the size condition
  have hA0 : 0 < A₀ := by linarith
  have hlogA : Real.log (A₀ * (|ρ.im| + 4)) ≤ 2 * (A₀ * L) := by
    rw [Real.log_mul hA0.ne' (by positivity)]
    have h1 : Real.log A₀ ≤ A₀ := (Real.log_le_sub_one_of_pos hA0).trans (by linarith)
    have h2 : Real.log (|ρ.im| + 4) ≤ L := Real.log_le_log (by positivity) (by linarith)
    nlinarith
  have hAL : 1 ≤ A₀ * L := by nlinarith
  set nn := (zetaZeroConfig.Nd (ρ.im - 101) (ρ.im + 101) : ℝ) with hnn
  have hnn0 : 0 ≤ nn := Nat.cast_nonneg _
  have hs1 : (nn + 1) * ℓ ≤ (202 * (A₀ * L) + A₀ * L) * ℓ :=
    mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have hs2 : Real.log (A₀ * (|ρ.im| + 4)) ≤ 2 * (A₀ * L) * ℓ := by nlinarith
  calc 100 * ((nn + 1) * ℓ + Real.log (A₀ * (|ρ.im| + 4)))
      ≤ 100 * ((202 * (A₀ * L) + A₀ * L) * ℓ + 2 * (A₀ * L) * ℓ) := by linarith
    _ = 20500 * (A₀ * L) * ℓ := by ring
    _ ≤ 10 ^ 5 * A₀ * L * ℓ := by nlinarith
    _ ≤ a := hsize

/-- The improved cluster horizon has a smooth negative witness, with aperture enlarged by one. -/
theorem zeta_exists_smooth_cluster_product_detector :
    ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ δ : ℝ, 0 < δ → ∀ ρ ∈ zetaZeroConfig.carrier,
      δ ≤ |ρ.re - 1 / 2| → 2 ≤ |ρ.im| → ∀ a : ℝ, Real.exp 6 ≤ a → 1 / δ ≤ a →
        10 ^ 5 * A₀ * Real.log (|ρ.im| + 306) * Real.log a ≤ a →
        ∃ f : ℝ → ℂ, ContDiff ℝ (⊤ : ℕ∞) f ∧ HasCompactSupport f ∧
          tsupport f ⊆ Icc (-(a + 1)) (a + 1) ∧ (zetaZeroConfig.W f f).re < 0 := by
  obtain ⟨A₀, hA₀, h⟩ := zeta_hodge_index_cluster_product_horizon
  exact ⟨A₀, hA₀, fun δ hδ ρ hρ hre hγ a ha6 haδ hsize =>
    RHTower.exists_smooth_weil_negative_of_not_hodgeIndex (h δ hδ ρ hρ hre hγ a ha6 haδ hsize)⟩

/-- At depth `1/a`, every zero below the exponential one-logarithm horizon has a smooth detector. -/
theorem zeta_smooth_detector_below_product_horizon :
    ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ a : ℝ, Real.exp 6 ≤ a → ∀ ρ ∈ zetaZeroConfig.carrier,
      1 / a ≤ |ρ.re - 1 / 2| → 2 ≤ |ρ.im| →
      |ρ.im| ≤ Real.exp (a / (10 ^ 5 * A₀ * Real.log a)) - 306 →
      ∃ f : ℝ → ℂ, ContDiff ℝ (⊤ : ℕ∞) f ∧ HasCompactSupport f ∧
        tsupport f ⊆ Icc (-(a + 1)) (a + 1) ∧ (zetaZeroConfig.W f f).re < 0 := by
  obtain ⟨A₀, hA₀, h⟩ := zeta_exists_smooth_cluster_product_detector
  refine ⟨A₀, hA₀, fun a ha6 ρ hρ hre hγ hheight => ?_⟩
  have ha0 : 0 < a := (Real.exp_pos 6).trans_le ha6
  have hlog : 0 < Real.log a := by
    have hh := Real.log_le_log (Real.exp_pos 6) ha6
    rw [Real.log_exp] at hh
    linarith
  have hA0 : 0 < A₀ := by linarith
  have hden : 0 < 10 ^ 5 * A₀ * Real.log a := by positivity
  have hL := Real.log_le_log (show 0 < |ρ.im| + 306 by positivity)
    (show |ρ.im| + 306 ≤ Real.exp (a / (10 ^ 5 * A₀ * Real.log a)) by linarith)
  rw [Real.log_exp, le_div_iff₀ hden] at hL
  apply h (1 / a) (by positivity) ρ hρ hre hγ a ha6
  · simpa only [one_div_one_div] using (le_refl a)
  · nlinarith only [hL]

end SquareRootThreshold

#print axioms SquareRootThreshold.exists_empty_annulus_with_product
#print axioms SquareRootThreshold.cluster_selection_with_products
#print axioms SquareRootThreshold.norm_sq_lowHeightProfile_product_ge
#print axioms SquareRootThreshold.exists_hodge_violation_cluster_product
#print axioms SquareRootThreshold.not_hodgeIndex_below_cluster_product_horizon
#print axioms SquareRootThreshold.zeta_hodge_index_cluster_product_horizon
#print axioms SquareRootThreshold.zeta_smooth_detector_below_product_horizon
