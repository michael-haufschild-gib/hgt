import GaloisForLFunctions.RHTower.LowHeightWeilTests

/-!
# The level-`a` Hodge index excludes low off-line zeros

Let `Z` be a zero configuration with local count `N(t, t+1] ≤ A₀ log(|t| + 3)`, and let
`ρ₀ = ½ + δ + iγ₀` be a zero with `δ > 0` and `|γ₀| ≥ 1`.  The test of `LowHeightWeilTests`, with
weight `(1 - u²)₊^{5/2}`, is built so that its transform `F(z - γ₀)`:

* vanishes at every zero of the window `|γ - γ₀| ≤ H` outside a cluster around `ρ₀`, `1 - ρ̄₀`;
* vanishes at both polar points `±i/2`, so the test is polar-constrained;
* has a root at a real phase point `c ∈ [-δ, δ]`, chosen by the intermediate value theorem so
  that `F(-iδ)` is purely imaginary.

Then:

* the killed zeros contribute nothing;
* the deep pair contributes `-2m_{ρ₀}|F(-iδ)|²`;
* the other cluster zeros contribute negatively, by a product-perturbation estimate at the
  radius chosen by pigeonhole over `n + 1` scales;
* the zeros outside the window are bounded by the decay of `ŵ^{N₀}` against the unit-window
  count.

The outcome (`exists_hodge_violation_low_height`) is an explicit elementary inequality in
`(a, δ, γ₀, H, n, A₀)` under which the level-`a` Hodge index fails; `n` is the number of zeros in
the window.  Contrapositively, the Hodge index at level `a` excludes every such zero
(`not_hodge_index_of_low_offLine_zero`), and for `ζ` the local count is unconditional
(`zeta_hodge_index_excludes_low_offLine_zeros`).

For fixed data the size condition holds at every large level, since exponential decay beats the
polynomial loss (`eventually_lowHeight_condition`).  Hence every off-line zero with `|γ| ≥ 1`
violates the Hodge index at all large levels (`eventually_not_hodgeIndex`), and the Hodge index at
every level puts every zero of `ζ` with `|γ| ≥ 1` on the critical line
(`zeta_re_eq_half_of_hodgeIndex`).
-/

open Complex MeasureTheory Real Set Filter Topology
open scoped ComplexConjugate

noncomputable section
namespace RHTower

open Zeta23

/-! ### The unit weight `w₁ = (1 - u²)₊^{5/2}` -/

/-- `∫ (a² - u²)₊^{5/2} cosh(δu) ≥ a (3a²/4)^{5/2}` for every `δ`. -/
theorem sinhTestWeight_cosh_energy_ge' {a : ℝ} (ha : 0 < a) (δ : ℝ) :
    a * (3 * a ^ 2 / 4) ^ (5 / 2 : ℝ) ≤ ∫ u, sinhTestWeight a u * Real.cosh (δ * u) := by
  set c := (3 * a ^ 2 / 4) ^ (5 / 2 : ℝ) with hc
  have hg0 : ∀ u, 0 ≤ sinhTestWeight a u * Real.cosh (δ * u) := fun u =>
    mul_nonneg (sinhTestWeight_nonneg a u) (Real.cosh_pos _).le
  have hcont : Continuous (fun u => sinhTestWeight a u * Real.cosh (δ * u)) :=
    (sinhTestWeight_contDiff a).continuous.mul
      (Real.continuous_cosh.comp (continuous_const.mul continuous_id))
  have hint : Integrable (fun u => sinhTestWeight a u * Real.cosh (δ * u)) := by
    refine hcont.integrable_of_hasCompactSupport ?_
    exact (hasCompactSupport_of_support_subset_abs (sinhTestWeight_supp ha.le)).mul_right
  have hsub : ∫ u in Icc (-(a / 2)) (a / 2), c ≤
      ∫ u in Icc (-(a / 2)) (a / 2), sinhTestWeight a u * Real.cosh (δ * u) := by
    refine setIntegral_mono_on (integrableOn_const measure_Icc_lt_top.ne (by simp))
      hcont.integrableOn_Icc measurableSet_Icc fun u hu => ?_
    obtain ⟨hu1, hu2⟩ := hu
    have hp : 3 * a ^ 2 / 4 ≤ a ^ 2 - u ^ 2 := by nlinarith
    have hψ : c ≤ sinhTestWeight a u := Real.rpow_le_rpow (by positivity) hp (by norm_num)
    calc c = c * 1 := (mul_one c).symm
      _ ≤ sinhTestWeight a u * Real.cosh (δ * u) :=
          mul_le_mul hψ (Real.one_le_cosh _) zero_le_one (sinhTestWeight_nonneg a u)
  have hle := setIntegral_le_integral (s := Icc (-(a / 2)) (a / 2)) hint
    (Eventually.of_forall hg0)
  rw [setIntegral_const, Real.volume_real_Icc, smul_eq_mul, max_eq_left (by linarith)] at hsub
  have : a / 2 - -(a / 2) = a := by ring
  rw [this] at hsub
  exact hsub.trans hle

/-- `(3/4)^{5/2}`, the energy floor of the unit weight. -/
def unitWeightFloor : ℝ := (3 / 4 : ℝ) ^ (5 / 2 : ℝ)

theorem unitWeightFloor_pos : 0 < unitWeightFloor := by unfold unitWeightFloor; positivity

theorem paperFT_unitWeight_neg_I_mul (δ : ℝ) :
    paperFT (fun u => (sinhTestWeight 1 u : ℂ)) (-(I * δ)) =
      ((∫ u, sinhTestWeight 1 u * Real.cosh (δ * u) : ℝ) : ℂ) :=
  paperFT_even_neg_I_mul (sinhTestWeight_contDiff 1).continuous (sinhTestWeight_supp zero_le_one)
    (sinhTestWeight_even 1) δ

theorem unitWeightFloor_le (δ : ℝ) :
    unitWeightFloor ≤ ∫ u, sinhTestWeight 1 u * Real.cosh (δ * u) := by
  have := sinhTestWeight_cosh_energy_ge' (a := 1) one_pos δ
  unfold unitWeightFloor
  simpa using this

theorem integral_abs_unitWeight_le (δ : ℝ) :
    ∫ u, |sinhTestWeight 1 u| ≤ ∫ u, sinhTestWeight 1 u * Real.cosh (δ * u) := by
  have hcont : Continuous (fun u => sinhTestWeight 1 u * Real.cosh (δ * u)) :=
    (sinhTestWeight_contDiff 1).continuous.mul
      (Real.continuous_cosh.comp (continuous_const.mul continuous_id))
  have hint : Integrable (fun u => sinhTestWeight 1 u * Real.cosh (δ * u)) := by
    refine hcont.integrable_of_hasCompactSupport ?_
    exact (hasCompactSupport_of_support_subset_abs (sinhTestWeight_supp zero_le_one)).mul_right
  refine integral_mono_of_nonneg (Eventually.of_forall fun u => abs_nonneg _) hint
    (Eventually.of_forall fun u => ?_)
  show |sinhTestWeight 1 u| ≤ sinhTestWeight 1 u * Real.cosh (δ * u)
  rw [abs_of_nonneg (sinhTestWeight_nonneg 1 u)]
  exact le_mul_of_one_le_right (sinhTestWeight_nonneg 1 u) (Real.one_le_cosh _)

theorem testNorm_unitWeight_le : testNorm (sinhTestWeight 1) ≤ 42 := by
  have := testNorm_sinhTestWeight_le (a := 1) zero_le_one
  norm_num at this
  linarith

theorem exp_one_half_lt_two : Real.exp (1 / 2) < 2 := by
  have h := Real.exp_one_lt_d9
  have h2 : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by rw [← Real.exp_nat_mul]; norm_num
  nlinarith [Real.exp_pos (1 / 2)]

theorem exp_sub_one_le_two_mul_of_le_half {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ 1 / 2) :
    Real.exp s - 1 ≤ 2 * s := by
  have h1 : 1 - s ≤ Real.exp (-s) := by linarith [Real.add_one_le_exp (-s)]
  have h2 : Real.exp s * Real.exp (-s) = 1 := by rw [← Real.exp_add]; simp
  have h3 : Real.exp s ≤ 2 :=
    (Real.exp_le_exp.mpr hs).trans exp_one_half_lt_two.le
  have h4 : Real.exp s * (1 - s) ≤ 1 := by
    calc Real.exp s * (1 - s) ≤ Real.exp s * Real.exp (-s) :=
          mul_le_mul_of_nonneg_left h1 (Real.exp_pos s).le
      _ = 1 := h2
  nlinarith

/-- **Cluster estimate.**  If the profile's factors are far from `x₀ = -iδ` relative to `ε`, and
`F(x₀)` is purely imaginary, then `Re F(z)² ≤ -(79/100)|F(x₀)|²` whenever `|z - x₀| < ε`. -/
theorem re_sq_lowHeightProfile_cluster {k : ℕ} {L : List ℂ} {δ ε : ℝ} (hδ : 0 < δ)
    (hδ2 : δ ≤ 1 / 2) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hr : ∀ r ∈ pairRoots L, -(I * δ) - r ≠ 0)
    (hS : ((k + 2 * L.length + 1 : ℕ) : ℝ) * (4 * ε) +
        ((pairRoots L).map fun r => ε / ‖-(I * δ) - r‖).sum ≤ 1 / 20)
    (hF0 : lowHeightProfile (sinhTestWeight 1) k L (-(I * δ)) ^ 2 =
      -((‖lowHeightProfile (sinhTestWeight 1) k L (-(I * δ))‖ ^ 2 : ℝ) : ℂ))
    {z : ℂ} (hz : ‖z - -(I * δ)‖ < ε) :
    (lowHeightProfile (sinhTestWeight 1) k L z ^ 2).re ≤
      -(79 / 100) * ‖lowHeightProfile (sinhTestWeight 1) k L (-(I * δ))‖ ^ 2 := by
  set x₀ := -(I * (δ : ℂ)) with hx₀
  set W := paperFT (fun u => (sinhTestWeight 1 u : ℂ)) with hW
  have hWx₀ : W x₀ = ((∫ u, sinhTestWeight 1 u * Real.cosh (δ * u) : ℝ) : ℂ) :=
    paperFT_unitWeight_neg_I_mul δ
  have hfloor := unitWeightFloor_le δ
  have hWn : ‖W x₀‖ = ∫ u, sinhTestWeight 1 u * Real.cosh (δ * u) := by
    rw [hWx₀, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg
      (unitWeightFloor_pos.le.trans hfloor)]
  have hW0 : W x₀ ≠ 0 := by
    intro h
    rw [h, norm_zero] at hWn
    linarith [unitWeightFloor_pos]
  have hzε : ‖z - x₀‖ ≤ ε := hz.le
  -- the Lipschitz ratio of `ŵ`
  have hlip := norm_paperFT_sub_le (sinhTestWeight_contDiff 1).continuous
    (sinhTestWeight_supp zero_le_one) (z₁ := z) (z₂ := x₀) (by linarith)
  have hx₀im : |x₀.im| = δ := by simp [hx₀, abs_of_pos hδ]
  rw [hx₀im] at hlip
  have hexp : Real.exp (δ * 1) ≤ 2 :=
    (Real.exp_le_exp.mpr (by linarith)).trans exp_one_half_lt_two.le
  have habs := integral_abs_unitWeight_le δ
  have hratio : ‖W z - W x₀‖ / ‖W x₀‖ ≤ 4 * ε := by
    rw [div_le_iff₀ (norm_pos_iff.mpr hW0), hWn]
    have hI0 : 0 ≤ ∫ u, |sinhTestWeight 1 u| := integral_nonneg fun _ => abs_nonneg _
    calc ‖W z - W x₀‖ ≤ 2 * 1 * ‖z - x₀‖ * Real.exp (δ * 1) * ∫ u, |sinhTestWeight 1 u| := hlip
      _ ≤ 2 * 1 * ε * 2 * ∫ u, sinhTestWeight 1 u * Real.cosh (δ * u) := by
          gcongr
      _ = 4 * ε * ∫ u, sinhTestWeight 1 u * Real.cosh (δ * u) := by ring
  -- the perturbation sum
  have hpert := norm_lowHeightProfile_sub_le (sinhTestWeight 1) k L (z := z) hW0 hr
  set S := ((k + 2 * L.length + 1 : ℕ) : ℝ) * (‖W z - W x₀‖ / ‖W x₀‖) +
    ((pairRoots L).map fun r => ‖z - x₀‖ / ‖x₀ - r‖).sum with hSdef
  have hS0 : 0 ≤ S := by
    have : 0 ≤ ((pairRoots L).map fun r => ‖z - x₀‖ / ‖x₀ - r‖).sum :=
      List.sum_nonneg fun y hy => by obtain ⟨r, -, rfl⟩ := List.mem_map.mp hy; positivity
    positivity
  have hSle : S ≤ 1 / 20 := by
    refine le_trans ?_ hS
    have h1 : ((pairRoots L).map fun r => ‖z - x₀‖ / ‖x₀ - r‖).sum ≤
        ((pairRoots L).map fun r => ε / ‖x₀ - r‖).sum :=
      List.sum_le_sum fun r _ => by gcongr
    have h2 := mul_le_mul_of_nonneg_left hratio
      (Nat.cast_nonneg (k + 2 * L.length + 1) : (0 : ℝ) ≤ ((k + 2 * L.length + 1 : ℕ) : ℝ))
    linarith
  have hθ : Real.exp S - 1 ≤ 1 / 10 := by
    have := exp_sub_one_le_two_mul_of_le_half hS0 (by linarith)
    linarith
  have hnear : ‖lowHeightProfile (sinhTestWeight 1) k L z -
      lowHeightProfile (sinhTestWeight 1) k L x₀‖ ≤
      1 / 10 * ‖lowHeightProfile (sinhTestWeight 1) k L x₀‖ :=
    hpert.trans (mul_le_mul_of_nonneg_right hθ (norm_nonneg _))
  have := re_sq_le_of_near (by norm_num : (0 : ℝ) ≤ 1 / 10) hF0 hnear
  linarith

/-! ### Size of the profile at the deep zero and in the tail -/

theorem pairRoots_append (K M : List ℂ) : pairRoots (K ++ M) = pairRoots K ++ pairRoots M := by
  simp [pairRoots, List.flatMap_append]

theorem pairRoots_pc (p c : ℂ) : pairRoots [p, c] = [p, conj p, c, conj c] := by
  simp [pairRoots]

/-- Lower bound for the profile at `x₀`. -/
theorem norm_lowHeightProfile_x₀_ge {k : ℕ} {K : List ℂ} {p c x₀ : ℂ} {W₀ η δ : ℝ} {n : ℕ}
    (hW₀ : 0 ≤ W₀) (hW : W₀ ≤ ‖paperFT (fun u => (sinhTestWeight 1 u : ℂ)) x₀‖)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hKn : K.length ≤ n)
    (hK : ∀ r ∈ pairRoots K, η ≤ ‖x₀ - r‖) (hp : 1 ≤ ‖x₀ - p‖) (hp' : 1 ≤ ‖x₀ - conj p‖)
    (hδ0 : 0 ≤ δ) (hc : δ ≤ ‖x₀ - c‖) (hc' : δ ≤ ‖x₀ - conj c‖) :
    W₀ ^ (k + 2 * (K ++ [p, c]).length + 1) * η ^ (2 * n) * δ ^ 2 ≤
      ‖lowHeightProfile (sinhTestWeight 1) k (K ++ [p, c]) x₀‖ := by
  rw [lowHeightProfile_eq_pairRoots, norm_mul, norm_pow, pairRoots_append, pairRoots_pc,
    List.map_append, List.prod_append, norm_mul]
  have hKprod := le_norm_list_prod_pow hη0 (fun r => x₀ - r) hK
  have hlen : (pairRoots K).length = 2 * K.length := pairRoots_length K
  rw [hlen] at hKprod
  have hKprod' : η ^ (2 * n) ≤ ‖((pairRoots K).map fun r => x₀ - r).prod‖ :=
    (pow_le_pow_of_le_one hη0 hη1 (by omega)).trans hKprod
  have hlast : δ ^ 2 ≤ ‖([p, conj p, c, conj c].map fun r => x₀ - r).prod‖ := by
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, norm_mul]
    have h1 : 1 ≤ ‖x₀ - p‖ * ‖x₀ - conj p‖ := by nlinarith [norm_nonneg (x₀ - p)]
    have h2 : δ ^ 2 ≤ ‖x₀ - c‖ * ‖x₀ - conj c‖ := by
      rw [sq]; exact mul_le_mul hc hc' hδ0 (norm_nonneg _)
    nlinarith [norm_nonneg (x₀ - c), norm_nonneg (x₀ - conj c), mul_nonneg (norm_nonneg (x₀ - c))
      (norm_nonneg (x₀ - conj c))]
  have hWpow := pow_le_pow_left₀ hW₀ hW (k + 2 * (K ++ [p, c]).length + 1)
  calc W₀ ^ (k + 2 * (K ++ [p, c]).length + 1) * η ^ (2 * n) * δ ^ 2
      ≤ ‖paperFT (fun u => (sinhTestWeight 1 u : ℂ)) x₀‖ ^ (k + 2 * (K ++ [p, c]).length + 1) *
          ‖((pairRoots K).map fun r => x₀ - r).prod‖ *
          ‖([p, conj p, c, conj c].map fun r => x₀ - r).prod‖ := by
        gcongr
    _ = _ := by ring

/-- Distance bound for the tail: every root of the profile is within `M(1 + |Re x|)` of `x`. -/
theorem norm_sub_root_le {x r : ℂ} {H B : ℝ} (hx : |x.im| ≤ 1 / 2) (hrre : |r.re| ≤ B)
    (hrim : |r.im| ≤ 1 / 2) (hB : 0 ≤ B) (hH : B ≤ H) :
    ‖x - r‖ ≤ (H + 1) * (1 + |x.re|) := by
  calc ‖x - r‖ ≤ |(x - r).re| + |(x - r).im| := Complex.norm_le_abs_re_add_abs_im _
    _ ≤ (|x.re| + |r.re|) + (|x.im| + |r.im|) := by
        simp only [Complex.sub_re, Complex.sub_im]
        exact add_le_add (abs_sub _ _) (abs_sub _ _)
    _ ≤ (|x.re| + H) + 1 := by linarith
    _ ≤ (H + 1) * (1 + |x.re|) := by nlinarith [abs_nonneg x.re]

/-! ### Summation -/

theorem re_W_le_of_pointwise (Z : ZeroConfig) (f : ℝ → ℂ)
    (hsum : Summable (fun ρ : Z.carrier => Z.Wsummand f f ρ)) (ρ₀ₛ ρ₁ₛ : Z.carrier) (Q : ℝ) {T : Z.carrier → ℝ} (hT : Summable T)
    (hpt : ∀ ρ : Z.carrier, (Z.Wsummand f f ρ).re ≤
      (if ρ = ρ₀ₛ then -Q else 0) + (if ρ = ρ₁ₛ then -Q else 0) + T ρ) :
    (Z.W f f).re ≤ -2 * Q + ∑' ρ, T ρ := by
  classical
  have hre : Summable (fun ρ : Z.carrier => (Z.Wsummand f f ρ).re) :=
    (Complex.hasSum_re hsum.hasSum).summable
  have hi0 := hasSum_ite_eq ρ₀ₛ (-Q)
  have hi1 := hasSum_ite_eq ρ₁ₛ (-Q)
  have hb : Summable (fun ρ => (if ρ = ρ₀ₛ then -Q else 0) + (if ρ = ρ₁ₛ then -Q else 0) + T ρ) :=
    (hi0.summable.add hi1.summable).add hT
  have hle := Summable.tsum_le_tsum hpt hre hb
  rw [Summable.tsum_add (hi0.summable.add hi1.summable) hT,
    Summable.tsum_add hi0.summable hi1.summable, hi0.tsum_eq, hi1.tsum_eq] at hle
  rw [ZeroConfig.W, Complex.re_tsum hsum]
  linarith

/-- `(e^{1/2}·168)^{2N₀} M^{4n+8}`, the tail constant of the low-height test. -/
def lowHeightTailConstant (M : ℝ) (N₀ n : ℕ) : ℝ :=
  (Real.exp (1 / 2) * 168) ^ (2 * N₀) * M ^ (4 * n + 8)

theorem lowHeightTailConstant_nonneg {M : ℝ} (hM : 0 ≤ M) (N₀ n : ℕ) :
    0 ≤ lowHeightTailConstant M N₀ n := by
  unfold lowHeightTailConstant; positivity

/-- Tail estimate for the low-height profile. -/
theorem norm_sq_lowHeightProfile_tail {k : ℕ} {L : List ℂ} {M : ℝ} (hM : 1 ≤ M) {x : ℂ}
    (hx : |x.im| ≤ 1 / 2) (hr : ∀ r ∈ pairRoots L, ‖x - r‖ ≤ M * (1 + |x.re|)) {N₀ n E : ℕ}
    (hN : k + 2 * L.length + 1 = N₀) (hL : L.length ≤ n + 2) (hE : E + 3 + 4 * (n + 2) ≤ 4 * N₀) :
    ‖lowHeightProfile (sinhTestWeight 1) k L x‖ ^ 2 * (1 + |x.re|) ^ (3 + E) ≤
      lowHeightTailConstant M N₀ n := by
  have hmain := norm_lowHeightProfile_sq_le (sinhTestWeight_contDiff 1)
    (sinhTestWeight_supp zero_le_one) k L hx (by linarith) hr
  rw [hN, pairRoots_length] at hmain
  set D := 1 + |x.re| with hD
  have hD1 : 1 ≤ D := by linarith [abs_nonneg x.re]
  have hD0 : 0 < D := by linarith
  set p := 2 * L.length with hp
  have hp4 : 2 * p ≤ 4 * n + 8 := by omega
  have hsplit : (D ^ 2) ^ (2 * N₀) = D ^ (2 * p) * D ^ (3 + E) * D ^ (4 * N₀ - 2 * p - (3 + E)) := by
    rw [← pow_mul, ← pow_add, ← pow_add]
    congr 1
    omega
  have hA : Real.exp (1 / 2) * (4 * testNorm (sinhTestWeight 1)) ≤ Real.exp (1 / 2) * 168 := by
    have := testNorm_unitWeight_le
    gcongr
    linarith
  have hA0 : 0 ≤ Real.exp (1 / 2) * (4 * testNorm (sinhTestWeight 1)) := by
    have := testNorm_nonneg (sinhTestWeight 1); positivity
  have hF0 := sq_nonneg ‖lowHeightProfile (sinhTestWeight 1) k L x‖
  have hextra : 1 ≤ D ^ (4 * N₀ - 2 * p - (3 + E)) := one_le_pow₀ hD1
  have hMp : M ^ (2 * p) ≤ M ^ (4 * n + 8) := pow_le_pow_right₀ hM hp4
  have hDp : 0 < D ^ (2 * p) := by positivity
  have key : ‖lowHeightProfile (sinhTestWeight 1) k L x‖ ^ 2 * D ^ (3 + E) * D ^ (2 * p) ≤
      (Real.exp (1 / 2) * (4 * testNorm (sinhTestWeight 1))) ^ (2 * N₀) * M ^ (2 * p) *
        D ^ (2 * p) := by
    have h1 : ‖lowHeightProfile (sinhTestWeight 1) k L x‖ ^ 2 * D ^ (3 + E) * D ^ (2 * p) ≤
        ‖lowHeightProfile (sinhTestWeight 1) k L x‖ ^ 2 * (D ^ 2) ^ (2 * N₀) := by
      rw [hsplit]
      have : 0 ≤ ‖lowHeightProfile (sinhTestWeight 1) k L x‖ ^ 2 * D ^ (3 + E) * D ^ (2 * p) := by
        positivity
      nlinarith
    calc _ ≤ ‖lowHeightProfile (sinhTestWeight 1) k L x‖ ^ 2 * (D ^ 2) ^ (2 * N₀) := h1
      _ ≤ _ := hmain.trans (le_of_eq (by rw [mul_pow]; ring_nf))
  have key' : ‖lowHeightProfile (sinhTestWeight 1) k L x‖ ^ 2 * D ^ (3 + E) ≤
      (Real.exp (1 / 2) * (4 * testNorm (sinhTestWeight 1))) ^ (2 * N₀) * M ^ (2 * p) :=
    le_of_mul_le_mul_right (by linarith) hDp
  calc _ ≤ (Real.exp (1 / 2) * (4 * testNorm (sinhTestWeight 1))) ^ (2 * N₀) * M ^ (2 * p) := key'
    _ ≤ (Real.exp (1 / 2) * 168) ^ (2 * N₀) * M ^ (4 * n + 8) := by
        gcongr
    _ = lowHeightTailConstant M N₀ n := rfl

/-! ### Root bookkeeping -/

theorem mem_pairRoots {L : List ℂ} {r : ℂ} : r ∈ pairRoots L ↔ ∃ s ∈ L, r = s ∨ r = conj s := by
  unfold pairRoots
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨s, hs, hr⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    exact ⟨s, hs, hr⟩
  · rintro ⟨s, hs, hr⟩
    exact ⟨s, hs, by simp only [List.mem_cons, List.not_mem_nil, or_false]; exact hr⟩

theorem lowHeightProfile_eq_zero_of_mem {w : ℝ → ℝ} {k : ℕ} {L : List ℂ} {r : ℂ} (hr : r ∈ L) :
    lowHeightProfile w k L r = 0 := by
  unfold lowHeightProfile
  rw [List.prod_eq_zero (List.mem_map.mpr ⟨r, hr, by simp⟩), mul_zero]

theorem lowHeightProfile_eq_zero_of_conj_mem {w : ℝ → ℝ} {k : ℕ} {L : List ℂ} {r : ℂ}
    (hr : r ∈ L) : lowHeightProfile w k L (conj r) = 0 := by
  unfold lowHeightProfile
  rw [List.prod_eq_zero (List.mem_map.mpr ⟨r, hr, by simp⟩), mul_zero]

/-- The roots of the low-height test: the killed ordinates, the polar root and the phase root. -/
def lowHeightRoots (γ₀ c : ℝ) (Kset : Finset ℂ) : List ℂ :=
  Kset.toList.map (fun ρ => gammaOf ρ - γ₀) ++ [(⟨-γ₀, 1 / 2⟩ : ℂ), (c : ℂ)]

theorem lowHeightRoots_length (γ₀ c : ℝ) (Kset : Finset ℂ) :
    (lowHeightRoots γ₀ c Kset).length = Kset.card + 2 := by
  simp [lowHeightRoots]

/-- The perturbation sum over the roots, at scale `ε`. -/
theorem sum_pairRoots_lowHeightRoots_le {γ₀ c δ ε η : ℝ} {Kset : Finset ℂ} (hδ : 0 < δ)
    (hε : 0 ≤ ε) (hη : 0 < η) (hγ : 1 ≤ |γ₀|)
    (hkil : ∀ ρ ∈ Kset, η ≤ ‖(gammaOf ρ - γ₀) - -(I * δ)‖ ∧ η ≤ ‖(gammaOf ρ - γ₀) - I * δ‖) :
    ((pairRoots (lowHeightRoots γ₀ c Kset)).map fun r => ε / ‖-(I * δ) - r‖).sum ≤
      (2 * (Kset.card : ℝ)) * (ε / η) + 2 * ε + 2 * ε / δ := by
  unfold lowHeightRoots
  rw [pairRoots_append, pairRoots_pc, List.map_append, List.sum_append]
  have hK : ((pairRoots (Kset.toList.map fun ρ => gammaOf ρ - γ₀)).map
      fun r => ε / ‖-(I * δ) - r‖).sum ≤ (2 * (Kset.card : ℝ)) * (ε / η) := by
    refine (List.sum_le_card_nsmul _ (ε / η) ?_).trans (le_of_eq ?_)
    · intro y hy
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hy
      obtain ⟨s, hs, hrs⟩ := mem_pairRoots.mp hr
      obtain ⟨ρ, hρ, rfl⟩ := List.mem_map.mp hs
      have hρK : ρ ∈ Kset := Finset.mem_toList.mp hρ
      obtain ⟨h1, h2⟩ := hkil ρ hρK
      have hd : η ≤ ‖-(I * δ) - r‖ := by
        rcases hrs with rfl | rfl
        · rw [norm_sub_rev]; exact h1
        · have : -(I * (δ : ℂ)) - conj (gammaOf ρ - γ₀) = conj (I * δ - (gammaOf ρ - γ₀)) := by
            simp [map_sub, Complex.conj_ofReal]
          rw [this, Complex.norm_conj, norm_sub_rev]; exact h2
      exact div_le_div_of_nonneg_left hε hη hd
    · rw [List.length_map, pairRoots_length, List.length_map, Finset.length_toList, nsmul_eq_mul]
      push_cast; ring
  have hp : 1 ≤ ‖-(I * (δ : ℂ)) - (⟨-γ₀, 1 / 2⟩ : ℂ)‖ := by
    refine hγ.trans ?_
    have := Complex.abs_re_le_norm (-(I * (δ : ℂ)) - (⟨-γ₀, 1 / 2⟩ : ℂ))
    simpa using this
  have hp' : 1 ≤ ‖-(I * (δ : ℂ)) - conj (⟨-γ₀, 1 / 2⟩ : ℂ)‖ := by
    refine hγ.trans ?_
    have := Complex.abs_re_le_norm (-(I * (δ : ℂ)) - conj (⟨-γ₀, 1 / 2⟩ : ℂ))
    simpa using this
  have hcd : δ ≤ ‖-(I * (δ : ℂ)) - (c : ℂ)‖ := by
    have := Complex.abs_im_le_norm (-(I * (δ : ℂ)) - (c : ℂ))
    simpa [abs_of_pos hδ] using this
  have hcd' : δ ≤ ‖-(I * (δ : ℂ)) - conj (c : ℂ)‖ := by
    rw [Complex.conj_ofReal]; exact hcd
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  have e1 : ε / ‖-(I * (δ : ℂ)) - (⟨-γ₀, 1 / 2⟩ : ℂ)‖ ≤ ε := div_le_self hε hp
  have e2 : ε / ‖-(I * (δ : ℂ)) - conj (⟨-γ₀, 1 / 2⟩ : ℂ)‖ ≤ ε := div_le_self hε hp'
  have e3 : ε / ‖-(I * (δ : ℂ)) - (c : ℂ)‖ ≤ ε / δ := div_le_div_of_nonneg_left hε hδ hcd
  have e4 : ε / ‖-(I * (δ : ℂ)) - conj (c : ℂ)‖ ≤ ε / δ := div_le_div_of_nonneg_left hε hδ hcd'
  calc _ ≤ (2 * (Kset.card : ℝ)) * (ε / η) + (ε + (ε + (ε / δ + ε / δ))) :=
        add_le_add hK (add_le_add e1 (add_le_add e2 (add_le_add e3 e4)))
    _ = _ := by ring

theorem ne_of_pairRoots_lowHeightRoots {γ₀ c δ η : ℝ} {Kset : Finset ℂ} (hδ : 0 < δ)
    (hη : 0 < η) (hγ : 1 ≤ |γ₀|)
    (hkil : ∀ ρ ∈ Kset, η ≤ ‖(gammaOf ρ - γ₀) - -(I * δ)‖ ∧ η ≤ ‖(gammaOf ρ - γ₀) - I * δ‖) :
    ∀ r ∈ pairRoots (lowHeightRoots γ₀ c Kset), -(I * δ) - r ≠ 0 := by
  intro r hr h
  have hr0 : r = -(I * (δ : ℂ)) := (sub_eq_zero.mp h).symm
  obtain ⟨s, hs, hrs⟩ := mem_pairRoots.mp hr
  unfold lowHeightRoots at hs
  rcases List.mem_append.mp hs with hs | hs
  · obtain ⟨ρ, hρ, rfl⟩ := List.mem_map.mp hs
    obtain ⟨h1, h2⟩ := hkil ρ (Finset.mem_toList.mp hρ)
    rcases hrs with hrs | hrs
    · rw [← hrs, hr0, sub_self, norm_zero] at h1; linarith
    · have : gammaOf ρ - γ₀ = I * δ := by
        have := congrArg conj hrs
        rw [Complex.conj_conj] at this
        rw [← this, hr0]; simp [Complex.conj_ofReal]
      rw [this, sub_self, norm_zero] at h2; linarith
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl <;> rcases hrs with hrs | hrs
    · have := congrArg Complex.re (hrs.symm.trans hr0); simp at this
      rw [this, abs_zero] at hγ; linarith
    · have := congrArg Complex.re (hrs.symm.trans hr0); simp at this
      rw [this, abs_zero] at hγ; linarith
    · have := congrArg Complex.im (hrs.symm.trans hr0); simp at this; linarith
    · have := congrArg Complex.im (hrs.symm.trans hr0); simp at this; linarith

/-! ### Assembly lemmas -/

/-- Every root of the low-height test is within `(H + |γ₀| + 1)(1 + |Re x|)` of any `x` in the
strip. -/
theorem lowHeightRoots_dist_le {γ₀ c δ H : ℝ} {Kset : Finset ℂ} (Z : ZeroConfig) (hH : 1 / 2 ≤ H)
    (hcδ : c ∈ Icc (-δ) δ) (hδ2 : δ ≤ 1 / 2)
    (hK : ∀ ρ ∈ Kset, ρ ∈ Z.carrier ∧ |ρ.im - γ₀| ≤ H) {x : ℂ} (hx : |x.im| ≤ 1 / 2) :
    ∀ r ∈ pairRoots (lowHeightRoots γ₀ c Kset), ‖x - r‖ ≤ (H + |γ₀| + 1) * (1 + |x.re|) := by
  intro r hr
  obtain ⟨s, hs, hrs⟩ := mem_pairRoots.mp hr
  have hB0 : 0 ≤ H + |γ₀| := by have := abs_nonneg γ₀; linarith
  have key : |s.re| ≤ H + |γ₀| ∧ |s.im| ≤ 1 / 2 := by
    unfold lowHeightRoots at hs
    rcases List.mem_append.mp hs with hs | hs
    · obtain ⟨ρ, hρ, rfl⟩ := List.mem_map.mp hs
      obtain ⟨hρZ, hρH⟩ := hK ρ (Finset.mem_toList.mp hρ)
      have hst := Z.strip ρ hρZ
      constructor
      · rw [Complex.sub_re, WeilEF.gammaOf_re, Complex.ofReal_re]
        linarith [abs_nonneg γ₀]
      · rw [Complex.sub_im, WeilEF.gammaOf_im, Complex.ofReal_im, sub_zero, abs_le]
        constructor <;> linarith [hst.1, hst.2]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl
      · simp only [abs_neg]
        constructor
        · linarith
        · norm_num [abs_of_pos]
      · simp only [Complex.ofReal_re, Complex.ofReal_im, abs_zero]
        constructor
        · have : |c| ≤ δ := abs_le.mpr hcδ
          linarith [abs_nonneg γ₀]
        · norm_num
  have key' : |r.re| ≤ H + |γ₀| ∧ |r.im| ≤ 1 / 2 := by
    rcases hrs with rfl | rfl
    · exact key
    · rw [Complex.conj_re, Complex.conj_im, abs_neg]; exact key
  have := norm_sub_root_le hx key'.1 key'.2 hB0 le_rfl
  linarith

/-- The value of the profile at `x₀ = -iδ` factors as `G·(c + iδ)²`. -/
theorem lowHeightProfile_x₀_eq (k : ℕ) (γ₀ c δ : ℝ) (Kset : Finset ℂ) :
    lowHeightProfile (sinhTestWeight 1) k (lowHeightRoots γ₀ c Kset) (-(I * δ)) =
      (paperFT (fun u => (sinhTestWeight 1 u : ℂ)) (-(I * δ)) ^
          (k + 2 * (lowHeightRoots γ₀ c Kset).length + 1) *
        ((Kset.toList.map (fun ρ => gammaOf ρ - γ₀) ++ [(⟨-γ₀, 1 / 2⟩ : ℂ)]).map
          (fun r => (-(I * δ) - r) * (-(I * δ) - conj r))).prod) * ((c : ℂ) + I * δ) ^ 2 := by
  unfold lowHeightProfile lowHeightRoots
  rw [show Kset.toList.map (fun ρ => gammaOf ρ - γ₀) ++ [(⟨-γ₀, 1 / 2⟩ : ℂ), (c : ℂ)] =
      (Kset.toList.map (fun ρ => gammaOf ρ - γ₀) ++ [(⟨-γ₀, 1 / 2⟩ : ℂ)]) ++ [(c : ℂ)] by simp]
  rw [List.map_append, List.prod_append]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    Complex.conj_ofReal]
  ring

/-! ### The pointwise estimate -/

/-- Tail weight outside the window. -/
def lowHeightTail (Z : ZeroConfig) (Wn : Finset ℂ) (γ₀ H C : ℝ) (E : ℕ) : Z.carrier → ℝ :=
  fun ρ => if (ρ : ℂ) ∈ Wn then 0 else
    (Z.mult ρ : ℝ) * C / ((1 + H) ^ E * (1 + |(ρ : ℂ).im - γ₀|) ^ 3)

theorem gammaOf_sub_reflect {ρ₀ : ℂ} {δ : ℝ} (hre : ρ₀.re = 1 / 2 + δ) :
    gammaOf (reflect ρ₀) - ρ₀.im = I * δ := by
  have hre1 : (reflect ρ₀).re = 1 / 2 + -δ := by
    simp only [reflect, Complex.sub_re, Complex.one_re, Complex.conj_re, hre]; ring
  have him1 : (reflect ρ₀).im = ρ₀.im := by
    simp only [reflect, Complex.sub_im, Complex.one_im, Complex.conj_im]; ring
  have := (gammaOf_sub_of_re_im him1 hre1).1
  rw [this, Complex.ofReal_neg, mul_neg, neg_neg]

theorem lowHeight_pointwise (Z : ZeroConfig) {ρ₀ : ℂ} (hρ₀ : ρ₀ ∈ Z.carrier) {δ : ℝ}
    (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2) (hre : ρ₀.re = 1 / 2 + δ) (hγ : 1 ≤ |ρ₀.im|) {H : ℝ}
    (hH : 1 ≤ H) {Wn Kset : Finset ℂ}
    (hWn : ∀ ρ, ρ ∈ Wn ↔ ρ ∈ Z.carrier ∧ ρ₀.im - H < ρ.im ∧ ρ.im ≤ ρ₀.im + H)
    (hKW : Kset ⊆ Wn) {n : ℕ} (hKn : Kset.card ≤ n) {ε η : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hη0 : 0 < η)
    (hclu : ∀ ρ ∈ Wn, ρ ∉ Kset →
      ‖(gammaOf ρ - ρ₀.im) - -(I * δ)‖ < ε ∨ ‖(gammaOf ρ - ρ₀.im) - I * δ‖ < ε)
    (hkil : ∀ ρ ∈ Kset,
      η ≤ ‖(gammaOf ρ - ρ₀.im) - -(I * δ)‖ ∧ η ≤ ‖(gammaOf ρ - ρ₀.im) - I * δ‖)
    {N₀ : ℕ} (hS : (N₀ : ℝ) * (4 * ε) + (2 * (n : ℝ)) * (ε / η) + 2 * ε + 2 * ε / δ ≤ 1 / 20)
    {c : ℝ} (hc : c ∈ Icc (-δ) δ) {k : ℕ}
    (hk : k + 2 * (lowHeightRoots ρ₀.im c Kset).length + 1 = N₀)
    (hF0re : (lowHeightProfile (sinhTestWeight 1) k (lowHeightRoots ρ₀.im c Kset)
      (-(I * δ))).re = 0)
    {E : ℕ} (hE : E + 3 + 4 * (n + 2) ≤ 4 * N₀) (ρ : Z.carrier) :
    (Z.Wsummand (lowHeightTest ρ₀.im (sinhTestWeight 1) k (lowHeightRoots ρ₀.im c Kset))
        (lowHeightTest ρ₀.im (sinhTestWeight 1) k (lowHeightRoots ρ₀.im c Kset)) ρ).re ≤
      (if ρ = ⟨ρ₀, hρ₀⟩ then -(79 / 100 * (Z.mult ρ₀ : ℝ) *
          ‖lowHeightProfile (sinhTestWeight 1) k (lowHeightRoots ρ₀.im c Kset) (-(I * δ))‖ ^ 2)
        else 0) +
      (if ρ = ⟨reflect ρ₀, Z.reflect_mem ρ₀ hρ₀⟩ then -(79 / 100 * (Z.mult ρ₀ : ℝ) *
          ‖lowHeightProfile (sinhTestWeight 1) k (lowHeightRoots ρ₀.im c Kset) (-(I * δ))‖ ^ 2)
        else 0) +
      lowHeightTail Z Wn ρ₀.im H (lowHeightTailConstant (H + |ρ₀.im| + 1) N₀ n) E ρ := by
  classical
  set γ₀ := ρ₀.im with hγ₀
  set L := lowHeightRoots γ₀ c Kset with hL
  set F := lowHeightProfile (sinhTestWeight 1) k L with hF
  set x₀ : ℂ := -(I * δ) with hx₀
  set F₀ := F x₀ with hF₀
  have hWs : Z.Wsummand (lowHeightTest γ₀ (sinhTestWeight 1) k L)
      (lowHeightTest γ₀ (sinhTestWeight 1) k L) ρ = (Z.mult (ρ : ℂ) : ℂ) * F (gammaOf ρ - γ₀) ^ 2 :=
    Wsummand_lowHeightTest (sinhTestWeight_contDiff 1) (sinhTestWeight_even 1)
      (sinhTestWeight_supp zero_le_one) Z γ₀ k L (ρ : ℂ)
  have hsq : F₀ ^ 2 = -((‖F₀‖ ^ 2 : ℝ) : ℂ) := sq_eq_neg_normSq_of_re_eq_zero hF0re
  have hconj : ∀ z, F (conj z) = conj (F z) := lowHeightProfile_conj (sinhTestWeight_even 1) k L
  have hLlen : L.length = Kset.card + 2 := lowHeightRoots_length γ₀ c Kset
  -- the cluster estimate
  have hr := ne_of_pairRoots_lowHeightRoots (c := c) hδ hη0 hγ hkil
  have hsum := sum_pairRoots_lowHeightRoots_le (c := c) hδ hε0.le hη0 hγ hkil
  have hS' : ((k + 2 * L.length + 1 : ℕ) : ℝ) * (4 * ε) +
      ((pairRoots L).map fun r => ε / ‖-(I * δ) - r‖).sum ≤ 1 / 20 := by
    rw [hk]
    have hcard : (2 * (Kset.card : ℝ)) * (ε / η) ≤ (2 * (n : ℝ)) * (ε / η) := by
      have : (Kset.card : ℝ) ≤ n := by exact_mod_cast hKn
      have : 0 ≤ ε / η := by positivity
      nlinarith
    linarith
  have hclus : ∀ z, ‖z - x₀‖ < ε → (F z ^ 2).re ≤ -(79 / 100) * ‖F₀‖ ^ 2 := fun z hz =>
    re_sq_lowHeightProfile_cluster hδ hδ2 hε0 hε1 hr hS' hsq hz
  have hclus' : ∀ z, ‖z - I * δ‖ < ε → (F z ^ 2).re ≤ -(79 / 100) * ‖F₀‖ ^ 2 := by
    intro z hz
    have h1 : F z = conj (F (conj z)) := by rw [hconj, Complex.conj_conj]
    have h2 : ‖conj z - x₀‖ < ε := by
      have : conj z - x₀ = conj (z - I * δ) := by simp [hx₀, map_sub, Complex.conj_ofReal]
      rw [this, Complex.norm_conj]; exact hz
    have h3 := hclus _ h2
    rw [h1, ← map_pow, Complex.conj_re]
    exact h3
  have hm0 : (0 : ℝ) ≤ Z.mult ρ₀ := Nat.cast_nonneg _
  have hF0n : 0 ≤ ‖F₀‖ ^ 2 := sq_nonneg _
  -- window membership of the pair
  have hρ₀W : ρ₀ ∈ Wn := (hWn ρ₀).mpr ⟨hρ₀, by linarith, by linarith⟩
  have hρ₁W : reflect ρ₀ ∈ Wn := by
    have him1 : (reflect ρ₀).im = ρ₀.im := by
      simp only [reflect, Complex.sub_im, Complex.one_im, Complex.conj_im]; ring
    exact (hWn _).mpr ⟨Z.reflect_mem ρ₀ hρ₀, by rw [him1]; linarith, by rw [him1]; linarith⟩
  have hne : (⟨reflect ρ₀, Z.reflect_mem ρ₀ hρ₀⟩ : Z.carrier) ≠ ⟨ρ₀, hρ₀⟩ := by
    intro h
    have := congrArg (fun x : Z.carrier => (x : ℂ).re) h
    simp only [reflect, Complex.sub_re, Complex.one_re, Complex.conj_re, hre] at this
    linarith
  have hT0 : ∀ σ : Z.carrier, (σ : ℂ) ∈ Wn →
      lowHeightTail Z Wn γ₀ H (lowHeightTailConstant (H + |γ₀| + 1) N₀ n) E σ = 0 := by
    intro σ hσ; simp [lowHeightTail, hσ]
  rw [hWs]
  by_cases h0 : ρ = ⟨ρ₀, hρ₀⟩
  · subst h0
    rw [if_pos rfl, if_neg hne.symm, hT0 _ hρ₀W, add_zero, add_zero]
    have hx : gammaOf ρ₀ - γ₀ = x₀ := (gammaOf_sub_of_re_im (ρ := ρ₀) (γ₀ := γ₀) rfl hre).1
    rw [show ((⟨ρ₀, hρ₀⟩ : Z.carrier) : ℂ) = ρ₀ from rfl, hx, ← hF₀, hsq]
    simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im, Complex.neg_re,
      Complex.ofReal_re, Complex.neg_im, Complex.ofReal_im, zero_mul, sub_zero, neg_zero]
    nlinarith
  by_cases h1 : ρ = ⟨reflect ρ₀, Z.reflect_mem ρ₀ hρ₀⟩
  · subst h1
    rw [if_neg hne, if_pos rfl, hT0 _ hρ₁W, zero_add, add_zero]
    have hx : gammaOf (reflect ρ₀) - γ₀ = conj x₀ := by
      rw [gammaOf_sub_reflect hre, hx₀]; simp [Complex.conj_ofReal]
    rw [show ((⟨reflect ρ₀, Z.reflect_mem ρ₀ hρ₀⟩ : Z.carrier) : ℂ) = reflect ρ₀ from rfl, hx,
      hconj, ← map_pow, ← hF₀, hsq, Z.mult_reflect ρ₀ hρ₀]
    simp only [map_neg, Complex.conj_ofReal, Complex.mul_re, Complex.natCast_re,
      Complex.natCast_im, Complex.neg_re, Complex.ofReal_re, Complex.neg_im, Complex.ofReal_im,
      zero_mul, sub_zero, neg_zero]
    nlinarith
  rw [if_neg h0, if_neg h1, zero_add, zero_add]
  have hmρ : (0 : ℝ) ≤ Z.mult (ρ : ℂ) := Nat.cast_nonneg _
  have hre_eq : ((Z.mult (ρ : ℂ) : ℂ) * F (gammaOf ρ - γ₀) ^ 2).re =
      (Z.mult (ρ : ℂ) : ℝ) * (F (gammaOf ρ - γ₀) ^ 2).re := by
    simp [Complex.mul_re]
  by_cases hW : (ρ : ℂ) ∈ Wn
  · rw [hT0 _ hW, hre_eq]
    by_cases hK : (ρ : ℂ) ∈ Kset
    · have hmem : gammaOf ρ - γ₀ ∈ L := by
        rw [hL]; unfold lowHeightRoots
        exact List.mem_append_left _ (List.mem_map.mpr ⟨ρ, Finset.mem_toList.mpr hK, rfl⟩)
      rw [hF, lowHeightProfile_eq_zero_of_mem hmem]
      simp
    · rcases hclu ρ hW hK with hc1 | hc1
      · have := hclus _ hc1
        nlinarith
      · have := hclus' _ hc1
        nlinarith
  · -- the tail
    have hρZ := ρ.2
    have hfar : H ≤ |(ρ : ℂ).im - γ₀| := by
      have hnot : ¬ (γ₀ - H < (ρ : ℂ).im ∧ (ρ : ℂ).im ≤ γ₀ + H) := fun h => hW ((hWn _).mpr ⟨hρZ, h⟩)
      rw [not_and_or, not_lt, not_le] at hnot
      rcases hnot with h | h
      · rw [abs_of_nonpos (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
    have hst := Z.strip _ hρZ
    set x := gammaOf (ρ : ℂ) - γ₀ with hxdef
    have hxre : x.re = (ρ : ℂ).im - γ₀ := by simp [hxdef, WeilEF.gammaOf_re]
    have hxim : |x.im| ≤ 1 / 2 := by
      rw [hxdef, Complex.sub_im, WeilEF.gammaOf_im, Complex.ofReal_im, sub_zero, abs_le]
      constructor <;> linarith [hst.1, hst.2]
    have hKH : ∀ σ ∈ Kset, σ ∈ Z.carrier ∧ |σ.im - γ₀| ≤ H := by
      intro σ hσ
      obtain ⟨hσZ, h1, h2⟩ := (hWn σ).mp (hKW hσ)
      exact ⟨hσZ, abs_le.mpr ⟨by linarith, by linarith⟩⟩
    have hroots := lowHeightRoots_dist_le (c := c) Z (by linarith : (1 : ℝ) / 2 ≤ H) hc hδ2 hKH hxim
    have hM : (1 : ℝ) ≤ H + |γ₀| + 1 := by have := abs_nonneg γ₀; linarith
    have htail := norm_sq_lowHeightProfile_tail hM hxim hroots hk (by rw [hLlen]; omega) hE
    rw [hxre] at htail
    set D := 1 + |(ρ : ℂ).im - γ₀| with hD
    have hD1 : 1 + H ≤ D := by rw [hD]; linarith
    have hDpos : 0 < D := by linarith
    have hHpos : 0 < 1 + H := by linarith
    have hDE : (1 + H) ^ E * D ^ 3 ≤ D ^ (3 + E) := by
      rw [pow_add, mul_comm]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hHpos.le hD1 E) (by positivity)
    have hFbound : ‖F x‖ ^ 2 ≤ lowHeightTailConstant (H + |γ₀| + 1) N₀ n / ((1 + H) ^ E * D ^ 3) := by
      rw [le_div_iff₀ (by positivity)]
      calc ‖F x‖ ^ 2 * ((1 + H) ^ E * D ^ 3) ≤ ‖F x‖ ^ 2 * D ^ (3 + E) :=
            mul_le_mul_of_nonneg_left hDE (sq_nonneg _)
        _ ≤ _ := htail
    simp only [lowHeightTail, if_neg hW]
    calc ((Z.mult (ρ : ℂ) : ℂ) * F x ^ 2).re ≤ ‖(Z.mult (ρ : ℂ) : ℂ) * F x ^ 2‖ := Complex.re_le_norm _
      _ = (Z.mult (ρ : ℂ) : ℝ) * ‖F x‖ ^ 2 := by rw [norm_mul, norm_pow, Complex.norm_natCast]
      _ ≤ (Z.mult (ρ : ℂ) : ℝ) *
          (lowHeightTailConstant (H + |γ₀| + 1) N₀ n / ((1 + H) ^ E * D ^ 3)) :=
          mul_le_mul_of_nonneg_left hFbound hmρ
      _ = _ := by ring

/-! ### The low-height theorem -/

/-- `100(n + 1)`, the scale ratio of the gap selection. -/
def lowHeightScale (n : ℕ) : ℝ := 100 * (n + 1)

/-- `min(δ, 1)/(100(3N₀ + 3))`, the initial scale of the gap selection. -/
def lowHeightEps0 (δ : ℝ) (N₀ : ℕ) : ℝ := min δ 1 / (100 * (3 * N₀ + 3))

/-- The floor for `|F(x₀)|²`. -/
def lowHeightFloor (δ : ℝ) (N₀ n : ℕ) : ℝ :=
  unitWeightFloor ^ (2 * N₀) * (lowHeightEps0 δ N₀ / lowHeightScale n ^ n) ^ (4 * n) * δ ^ 4

theorem killed_dist_ge {γ₀ δ η : ℝ} {Kset : Finset ℂ}
    (hkil : ∀ ρ ∈ Kset, η ≤ ‖(gammaOf ρ - γ₀) - -(I * δ)‖ ∧ η ≤ ‖(gammaOf ρ - γ₀) - I * δ‖) :
    ∀ r ∈ pairRoots (Kset.toList.map fun ρ => gammaOf ρ - γ₀), η ≤ ‖-(I * δ) - r‖ := by
  intro r hr
  obtain ⟨s, hs, hrs⟩ := mem_pairRoots.mp hr
  obtain ⟨ρ, hρ, rfl⟩ := List.mem_map.mp hs
  obtain ⟨h1, h2⟩ := hkil ρ (Finset.mem_toList.mp hρ)
  rcases hrs with rfl | rfl
  · rw [norm_sub_rev]; exact h1
  · have : -(I * (δ : ℂ)) - conj (gammaOf ρ - γ₀) = conj (I * δ - (gammaOf ρ - γ₀)) := by
      simp [map_sub, Complex.conj_ofReal]
    rw [this, Complex.norm_conj, norm_sub_rev]; exact h2

/-- Scale arithmetic for the cluster estimate. -/
theorem lowHeight_scale_bound {N₀ n : ℕ} {δ ε : ℝ} (hδ : 0 < δ) (hε0 : 0 ≤ ε)
    (hε : ε ≤ lowHeightEps0 δ N₀) :
    (N₀ : ℝ) * (4 * ε) + (2 * (n : ℝ)) * (1 / lowHeightScale n) + 2 * ε + 2 * ε / δ ≤ 1 / 20 := by
  have hN0 : (0 : ℝ) ≤ N₀ := Nat.cast_nonneg N₀
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hden : 0 < 100 * (3 * (N₀ : ℝ) + 3) := by positivity
  have hmin1 : min δ 1 ≤ 1 := min_le_right _ _
  have hminδ : min δ 1 ≤ δ := min_le_left _ _
  have hεN : ε * (100 * (3 * (N₀ : ℝ) + 3)) ≤ min δ 1 := by
    rw [← le_div_iff₀ hden]; exact hε
  have h1 : (N₀ : ℝ) * (4 * ε) ≤ 4 / 300 := by nlinarith
  have h2 : (2 * (n : ℝ)) * (1 / lowHeightScale n) ≤ 2 / 100 := by
    unfold lowHeightScale
    rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have h3 : 2 * ε ≤ 2 / 300 := by nlinarith
  have h4 : 2 * ε / δ ≤ 2 / 300 := by
    rw [div_le_div_iff₀ hδ (by norm_num)]
    nlinarith
  linarith

/-- Gap selection: a killed set, a cluster radius `ε` and a killing distance `η = λε`. -/
theorem lowHeight_selection (Wn : Finset ℂ) {γ₀ δ : ℝ} (hδ : 0 < δ) {N₀ n : ℕ}
    (hn : Wn.card ≤ n) :
    ∃ Kset ⊆ Wn, ∃ ε η : ℝ, 0 < ε ∧ ε ≤ lowHeightEps0 δ N₀ ∧ 0 < η ∧ η ≤ 1 ∧
      lowHeightEps0 δ N₀ / lowHeightScale n ^ n ≤ η ∧ ε / η = 1 / lowHeightScale n ∧
      (∀ ρ ∈ Wn, ρ ∉ Kset →
        ‖(gammaOf ρ - γ₀) - -(I * δ)‖ < ε ∨ ‖(gammaOf ρ - γ₀) - I * δ‖ < ε) ∧
      (∀ ρ ∈ Kset, η ≤ ‖(gammaOf ρ - γ₀) - -(I * δ)‖ ∧ η ≤ ‖(gammaOf ρ - γ₀) - I * δ‖) := by
  classical
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hlam : 1 < lowHeightScale n := by unfold lowHeightScale; linarith
  have hε₀ : 0 < lowHeightEps0 δ N₀ := by
    unfold lowHeightEps0; have := lt_min hδ one_pos; positivity
  have hε₀1 : lowHeightEps0 δ N₀ ≤ 1 := by
    unfold lowHeightEps0
    rw [div_le_one (by positivity)]
    have := min_le_right δ 1
    nlinarith [Nat.cast_nonneg (α := ℝ) N₀]
  obtain ⟨k₀, hk₀, hgap⟩ := exists_gap_scale Wn
    (fun ρ => min ‖(gammaOf ρ - γ₀) - -(I * δ)‖ ‖(gammaOf ρ - γ₀) - I * δ‖) hε₀ hlam
  refine ⟨Wn.filter (fun ρ => lowHeightEps0 δ N₀ / lowHeightScale n ^ k₀ ≤
      min ‖(gammaOf ρ - γ₀) - -(I * δ)‖ ‖(gammaOf ρ - γ₀) - I * δ‖),
    Finset.filter_subset _ _, lowHeightEps0 δ N₀ / lowHeightScale n ^ (k₀ + 1),
    lowHeightEps0 δ N₀ / lowHeightScale n ^ k₀, by positivity, ?_, by positivity, ?_, ?_, ?_, ?_,
    ?_⟩
  · exact div_le_self hε₀.le (one_le_pow₀ hlam.le)
  · exact (div_le_self hε₀.le (one_le_pow₀ hlam.le)).trans hε₀1
  · exact div_le_div_of_nonneg_left hε₀.le (by positivity)
      (pow_le_pow_right₀ hlam.le (hk₀.trans hn))
  · rw [pow_succ]
    have : 0 < lowHeightScale n ^ k₀ := by positivity
    field_simp
  · intro ρ hρ hK
    rcases hgap ρ hρ with h | h
    · exact min_lt_iff.mp h
    · exact absurd (Finset.mem_filter.mpr ⟨hρ, h⟩) hK
  · intro ρ hρ
    exact le_min_iff.mp (Finset.mem_filter.mp hρ).2

/-- The Weil form of the low-height test. -/
theorem re_W_lowHeightTest_le (Z : ZeroConfig) {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3))
    {ρ₀ : ℂ} (hρ₀ : ρ₀ ∈ Z.carrier) {δ : ℝ}
    (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2) (hre : ρ₀.re = 1 / 2 + δ) (hγ : 1 ≤ |ρ₀.im|) {H : ℝ}
    (hH : 1 ≤ H) {Wn Kset : Finset ℂ}
    (hWn : ∀ ρ, ρ ∈ Wn ↔ ρ ∈ Z.carrier ∧ ρ₀.im - H < ρ.im ∧ ρ.im ≤ ρ₀.im + H)
    (hKW : Kset ⊆ Wn) {n : ℕ} (hKn : Kset.card ≤ n) {ε η : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hη0 : 0 < η)
    (hclu : ∀ ρ ∈ Wn, ρ ∉ Kset →
      ‖(gammaOf ρ - ρ₀.im) - -(I * δ)‖ < ε ∨ ‖(gammaOf ρ - ρ₀.im) - I * δ‖ < ε)
    (hkil : ∀ ρ ∈ Kset,
      η ≤ ‖(gammaOf ρ - ρ₀.im) - -(I * δ)‖ ∧ η ≤ ‖(gammaOf ρ - ρ₀.im) - I * δ‖)
    {N₀ : ℕ} (hS : (N₀ : ℝ) * (4 * ε) + (2 * (n : ℝ)) * (ε / η) + 2 * ε + 2 * ε / δ ≤ 1 / 20)
    {c : ℝ} (hc : c ∈ Icc (-δ) δ) {k : ℕ}
    (hk : k + 2 * (lowHeightRoots ρ₀.im c Kset).length + 1 = N₀)
    (hF0re : (lowHeightProfile (sinhTestWeight 1) k (lowHeightRoots ρ₀.im c Kset)
      (-(I * δ))).re = 0)
    {E : ℕ} (hE : E + 3 + 4 * (n + 2) ≤ 4 * N₀) :
    (Z.W (lowHeightTest ρ₀.im (sinhTestWeight 1) k (lowHeightRoots ρ₀.im c Kset))
        (lowHeightTest ρ₀.im (sinhTestWeight 1) k (lowHeightRoots ρ₀.im c Kset))).re ≤
      -(79 / 50) * ‖lowHeightProfile (sinhTestWeight 1) k (lowHeightRoots ρ₀.im c Kset)
        (-(I * δ))‖ ^ 2 +
      lowHeightTailConstant (H + |ρ₀.im| + 1) N₀ n / (1 + H) ^ E *
        (24 * A₀ * Real.log (|ρ₀.im| + 3)) := by
  classical
  set γ₀ := ρ₀.im with hγ₀
  set C₁ := lowHeightTailConstant (H + |γ₀| + 1) N₀ n with hC₁
  have hC₁0 : 0 ≤ C₁ := lowHeightTailConstant_nonneg (by positivity) N₀ n
  obtain ⟨hwsum, hwle⟩ := window_tsum_le Z hA₀ hloc γ₀
  have hLlen := lowHeightRoots_length γ₀ c Kset
  have hKH : ∀ σ ∈ Kset, σ ∈ Z.carrier ∧ |σ.im - γ₀| ≤ H := by
    intro σ hσ
    obtain ⟨hσZ, h1, h2⟩ := (hWn σ).mp (hKW hσ)
    exact ⟨hσZ, abs_le.mpr ⟨by linarith, by linarith⟩⟩
  have hM : (1 : ℝ) ≤ H + |γ₀| + 1 := by have := abs_nonneg γ₀; linarith
  -- summability
  have hbound : ∀ ρ : Z.carrier,
      ‖Z.Wsummand (lowHeightTest γ₀ (sinhTestWeight 1) k (lowHeightRoots γ₀ c Kset))
        (lowHeightTest γ₀ (sinhTestWeight 1) k (lowHeightRoots γ₀ c Kset)) ρ‖ ≤
        C₁ * ((Z.mult ρ : ℝ) / (1 + |(ρ : ℂ).im - γ₀|) ^ 3) := by
    intro ρ
    have hst := Z.strip _ ρ.2
    have hxim : |(gammaOf (ρ : ℂ) - γ₀).im| ≤ 1 / 2 := by
      rw [Complex.sub_im, WeilEF.gammaOf_im, Complex.ofReal_im, sub_zero, abs_le]
      constructor <;> linarith [hst.1, hst.2]
    have hxre : (gammaOf (ρ : ℂ) - γ₀).re = (ρ : ℂ).im - γ₀ := by simp [WeilEF.gammaOf_re]
    have hroots := lowHeightRoots_dist_le (c := c) Z (by linarith : (1 : ℝ) / 2 ≤ H) hc hδ2 hKH
      hxim
    have htail := norm_sq_lowHeightProfile_tail (E := 0) (n := n) hM hxim hroots hk
      (by rw [hLlen]; omega) (by omega)
    rw [hxre] at htail
    rw [Wsummand_lowHeightTest (sinhTestWeight_contDiff 1) (sinhTestWeight_even 1)
      (sinhTestWeight_supp zero_le_one), norm_mul, norm_pow, Complex.norm_natCast]
    have hD : 0 < (1 + |(ρ : ℂ).im - γ₀|) ^ 3 := by positivity
    have hm : (0 : ℝ) ≤ Z.mult (ρ : ℂ) := Nat.cast_nonneg _
    have hF : ‖lowHeightProfile (sinhTestWeight 1) k (lowHeightRoots γ₀ c Kset)
        (gammaOf ρ - γ₀)‖ ^ 2 ≤ C₁ / (1 + |(ρ : ℂ).im - γ₀|) ^ 3 := by
      rw [le_div_iff₀ hD]; exact htail
    calc (Z.mult (ρ : ℂ) : ℝ) * ‖lowHeightProfile (sinhTestWeight 1) k (lowHeightRoots γ₀ c Kset)
          (gammaOf ρ - γ₀)‖ ^ 2 ≤ (Z.mult (ρ : ℂ) : ℝ) * (C₁ / (1 + |(ρ : ℂ).im - γ₀|) ^ 3) :=
          mul_le_mul_of_nonneg_left hF hm
      _ = C₁ * ((Z.mult ρ : ℝ) / (1 + |(ρ : ℂ).im - γ₀|) ^ 3) := by ring
  have hsum := Summable.of_norm_bounded (hwsum.mul_left C₁) hbound
  -- pointwise and summation
  have hpt := lowHeight_pointwise Z hρ₀ hδ hδ2 hre hγ hH hWn hKW hKn hε0 hε1 hη0 hclu hkil hS hc
    hk hF0re hE
  have hW := re_W_le_of_pointwise Z _ hsum _ _ _ (T := lowHeightTail Z Wn γ₀ H C₁ E)
    (by
      refine Summable.of_nonneg_of_le (fun ρ => ?_) (fun ρ => ?_) (hwsum.mul_left (C₁ / (1 + H) ^ E))
      · unfold lowHeightTail; split_ifs
        · exact le_rfl
        · have : (0 : ℝ) ≤ Z.mult (ρ : ℂ) := Nat.cast_nonneg _
          positivity
      · unfold lowHeightTail; split_ifs
        · have : (0 : ℝ) ≤ Z.mult (ρ : ℂ) := Nat.cast_nonneg _
          positivity
        · apply le_of_eq; field_simp)
    hpt
  have hTle : ∑' ρ, lowHeightTail Z Wn γ₀ H C₁ E ρ ≤ C₁ / (1 + H) ^ E *
      (24 * A₀ * Real.log (|γ₀| + 3)) := by
    have hcomp : ∀ ρ, lowHeightTail Z Wn γ₀ H C₁ E ρ ≤
        C₁ / (1 + H) ^ E * ((Z.mult ρ : ℝ) / (1 + |(ρ : ℂ).im - γ₀|) ^ 3) := by
      intro ρ
      unfold lowHeightTail; split_ifs
      · have : (0 : ℝ) ≤ Z.mult (ρ : ℂ) := Nat.cast_nonneg _
        positivity
      · apply le_of_eq; field_simp
    have hT0 : ∀ ρ, 0 ≤ lowHeightTail Z Wn γ₀ H C₁ E ρ := by
      intro ρ; unfold lowHeightTail; split_ifs
      · exact le_rfl
      · have : (0 : ℝ) ≤ Z.mult (ρ : ℂ) := Nat.cast_nonneg _
        positivity
    calc ∑' ρ, lowHeightTail Z Wn γ₀ H C₁ E ρ
        ≤ ∑' ρ : Z.carrier, C₁ / (1 + H) ^ E * ((Z.mult (ρ : ℂ) : ℝ) /
            (1 + |(ρ : ℂ).im - γ₀|) ^ 3) :=
          Summable.tsum_le_tsum hcomp (Summable.of_nonneg_of_le hT0 hcomp
            (hwsum.mul_left _)) (hwsum.mul_left _)
      _ = C₁ / (1 + H) ^ E * ∑' ρ : Z.carrier, (Z.mult ρ : ℝ) / (1 + |(ρ : ℂ).im - γ₀|) ^ 3 :=
          tsum_mul_left
      _ ≤ C₁ / (1 + H) ^ E * (24 * A₀ * Real.log (|γ₀| + 3)) :=
          mul_le_mul_of_nonneg_left hwle (by positivity)
  have hm : (1 : ℝ) ≤ Z.mult ρ₀ := by exact_mod_cast Z.one_le_mult ρ₀ hρ₀
  have hFn := sq_nonneg ‖lowHeightProfile (sinhTestWeight 1) k (lowHeightRoots γ₀ c Kset)
    (-(I * δ))‖
  nlinarith

/-- The floor for the deep-zero value of the low-height profile. -/
theorem lowHeightFloor_le {γ₀ c δ η : ℝ} {Kset : Finset ℂ} {k N₀ n : ℕ} (hδ : 0 < δ)
    (hγ : 1 ≤ |γ₀|) (hη0 : 0 < η) (hη1 : η ≤ 1)
    (hηlow : lowHeightEps0 δ N₀ / lowHeightScale n ^ n ≤ η) (hKn : Kset.card ≤ n)
    (hkil : ∀ ρ ∈ Kset, η ≤ ‖(gammaOf ρ - γ₀) - -(I * δ)‖ ∧ η ≤ ‖(gammaOf ρ - γ₀) - I * δ‖)
    (hk : k + 2 * (lowHeightRoots γ₀ c Kset).length + 1 = N₀) :
    lowHeightFloor δ N₀ n ≤
      ‖lowHeightProfile (sinhTestWeight 1) k (lowHeightRoots γ₀ c Kset) (-(I * δ))‖ ^ 2 := by
  have hW : unitWeightFloor ≤ ‖paperFT (fun u => (sinhTestWeight 1 u : ℂ)) (-(I * δ))‖ := by
    rw [paperFT_unitWeight_neg_I_mul, Complex.norm_real, Real.norm_eq_abs]
    exact (unitWeightFloor_le δ).trans (le_abs_self _)
  have hp : 1 ≤ ‖-(I * (δ : ℂ)) - (⟨-γ₀, 1 / 2⟩ : ℂ)‖ := by
    refine hγ.trans ?_
    have := Complex.abs_re_le_norm (-(I * (δ : ℂ)) - (⟨-γ₀, 1 / 2⟩ : ℂ))
    simpa using this
  have hp' : 1 ≤ ‖-(I * (δ : ℂ)) - conj (⟨-γ₀, 1 / 2⟩ : ℂ)‖ := by
    refine hγ.trans ?_
    have := Complex.abs_re_le_norm (-(I * (δ : ℂ)) - conj (⟨-γ₀, 1 / 2⟩ : ℂ))
    simpa using this
  have hcd : δ ≤ ‖-(I * (δ : ℂ)) - (c : ℂ)‖ := by
    have := Complex.abs_im_le_norm (-(I * (δ : ℂ)) - (c : ℂ))
    simpa [abs_of_pos hδ] using this
  have hcd' : δ ≤ ‖-(I * (δ : ℂ)) - conj (c : ℂ)‖ := by rw [Complex.conj_ofReal]; exact hcd
  have hKlen : (Kset.toList.map fun ρ => gammaOf ρ - γ₀).length ≤ n := by
    rw [List.length_map, Finset.length_toList]; exact hKn
  have hlow := norm_lowHeightProfile_x₀_ge (k := k) unitWeightFloor_pos.le hW hη0.le hη1 hKlen
    (killed_dist_ge hkil) hp hp' hδ.le hcd hcd'
  rw [show Kset.toList.map (fun ρ => gammaOf ρ - γ₀) ++ [(⟨-γ₀, 1 / 2⟩ : ℂ), (c : ℂ)] =
    lowHeightRoots γ₀ c Kset from rfl, hk] at hlow
  have hpos : 0 ≤ unitWeightFloor ^ N₀ * η ^ (2 * n) * δ ^ 2 := by
    have := unitWeightFloor_pos; positivity
  have hsq := pow_le_pow_left₀ hpos hlow 2
  have hε₀0 : 0 ≤ lowHeightEps0 δ N₀ / lowHeightScale n ^ n := by
    unfold lowHeightEps0 lowHeightScale
    have := lt_min hδ one_pos
    positivity
  have hηpow := pow_le_pow_left₀ hε₀0 hηlow (4 * n)
  unfold lowHeightFloor
  calc unitWeightFloor ^ (2 * N₀) * (lowHeightEps0 δ N₀ / lowHeightScale n ^ n) ^ (4 * n) * δ ^ 4
      ≤ unitWeightFloor ^ (2 * N₀) * η ^ (4 * n) * δ ^ 4 := by
        have := unitWeightFloor_pos
        gcongr
    _ = (unitWeightFloor ^ N₀ * η ^ (2 * n) * δ ^ 2) ^ 2 := by ring
    _ ≤ _ := hsq

/-- **Quantitative Weil criterion at low height.**  Let `Z` be a zero configuration with local
count `N(t, t+1] ≤ A₀ log(|t| + 3)`, and let `ρ₀ = ½ + δ + iγ₀` be a zero with `δ > 0` and
`|γ₀| ≥ 1`.  If the window `γ₀ - H < Im ρ ≤ γ₀ + H` contains at most `n` distinct zeros,
`2n + 7 ≤ N₀ ≤ a`, and
`C_tail·24A₀ log(|γ₀| + 3) < (79/50)(1 + H)^{4N₀ - 4n - 11}·lowHeightFloor δ N₀ n`,
then the level-`a` Hodge index fails: a `C²` test supported in `[-a, a]` with
`h_f(±i/2) = 0` has negative Weil form.

The test is `e^{-iγ₀u}` times an iterated convolution of `(1 - u²)₊^{5/2}` whose transform
vanishes at every zero of the window outside a cluster around `ρ₀, 1 - ρ̄₀`, at the two polar
points, and at a phase root that makes the deep contribution `-|F(x₀)|²`.  The cluster radius
comes from pigeonhole over `n + 1` scales. -/
theorem exists_hodge_violation_low_height (Z : ZeroConfig) {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3))
    {ρ₀ : ℂ} (hρ₀ : ρ₀ ∈ Z.carrier) {δ : ℝ} (hδ : 0 < δ) (hre : ρ₀.re = 1 / 2 + δ)
    (hγ : 1 ≤ |ρ₀.im|) {H a : ℝ} (hH : 1 ≤ H) {N₀ n : ℕ} (hN₀a : (N₀ : ℝ) ≤ a)
    (hn : (Z.finite_window (ρ₀.im - H) (ρ₀.im + H)).toFinset.card ≤ n) (hNn : 2 * n + 7 ≤ N₀)
    (hbig : lowHeightTailConstant (H + |ρ₀.im| + 1) N₀ n * (24 * A₀ * Real.log (|ρ₀.im| + 3)) <
      79 / 50 * (1 + H) ^ (4 * N₀ - 4 * n - 11) * lowHeightFloor δ N₀ n) :
    ∃ f : ℝ → ℂ, ContDiff ℝ 2 f ∧ tsupport f ⊆ Icc (-a) a ∧ paperFT f (I / 2) = 0 ∧
      paperFT f (-(I / 2)) = 0 ∧ (Z.W f f).re < 0 := by
  classical
  have hst := Z.strip ρ₀ hρ₀
  have hδ2 : δ ≤ 1 / 2 := by linarith [hst.2]
  have hWn : ∀ ρ, ρ ∈ (Z.finite_window (ρ₀.im - H) (ρ₀.im + H)).toFinset ↔
      ρ ∈ Z.carrier ∧ ρ₀.im - H < ρ.im ∧ ρ.im ≤ ρ₀.im + H := by
    intro ρ; rw [Set.Finite.mem_toFinset]; rfl
  obtain ⟨Kset, hKW, ε, η, hε0, hεε₀, hη0, hη1, hηlow, hεη, hclu, hkil⟩ :=
    lowHeight_selection (γ₀ := ρ₀.im) (N₀ := N₀) _ hδ hn
  have hKn : Kset.card ≤ n := (Finset.card_le_card hKW).trans hn
  have hε1 : ε ≤ 1 := by
    refine hεε₀.trans ?_
    unfold lowHeightEps0
    rw [div_le_one (by positivity)]
    have := min_le_right δ 1
    nlinarith [Nat.cast_nonneg (α := ℝ) N₀]
  have hS : (N₀ : ℝ) * (4 * ε) + (2 * (n : ℝ)) * (ε / η) + 2 * ε + 2 * ε / δ ≤ 1 / 20 := by
    rw [hεη]; exact lowHeight_scale_bound hδ hε0.le hεε₀
  -- the phase
  obtain ⟨c, hc, hcre⟩ := exists_phase_rotation hδ
    (paperFT (fun u => (sinhTestWeight 1 u : ℂ)) (-(I * δ)) ^
        (N₀ - (2 * (Kset.card + 2) + 1) + 2 * (Kset.card + 2) + 1) *
      ((Kset.toList.map (fun ρ => gammaOf ρ - ρ₀.im) ++ [(⟨-ρ₀.im, 1 / 2⟩ : ℂ)]).map
        (fun r => (-(I * δ) - r) * (-(I * δ) - conj r))).prod)
  have hLlen := lowHeightRoots_length ρ₀.im c Kset
  have hk : N₀ - (2 * (Kset.card + 2) + 1) + 2 * (lowHeightRoots ρ₀.im c Kset).length + 1 = N₀ := by
    rw [hLlen]; omega
  have hF0re : (lowHeightProfile (sinhTestWeight 1) (N₀ - (2 * (Kset.card + 2) + 1))
      (lowHeightRoots ρ₀.im c Kset) (-(I * δ))).re = 0 := by
    rw [lowHeightProfile_x₀_eq, hLlen, mul_comm]
    exact hcre
  -- the test
  obtain ⟨hfc, hfs, hff⟩ := lowHeightTest_props (sinhTestWeight_contDiff 1)
    (sinhTestWeight_even 1) (sinhTestWeight_supp zero_le_one) ρ₀.im
    (N₀ - (2 * (Kset.card + 2) + 1)) (lowHeightRoots ρ₀.im c Kset)
  refine ⟨lowHeightTest ρ₀.im (sinhTestWeight 1) (N₀ - (2 * (Kset.card + 2) + 1))
    (lowHeightRoots ρ₀.im c Kset), hfc, ?_, ?_, ?_, ?_⟩
  · refine tsupport_subset_of_support_subset_abs fun u hu => ?_
    have h := hfs u hu
    have e : (((N₀ - (2 * (Kset.card + 2) + 1) : ℕ) : ℝ) +
        2 * ((lowHeightRoots ρ₀.im c Kset).length : ℝ) + 1) * 1 = (N₀ : ℝ) := by
      rw [mul_one]; exact_mod_cast hk
    rw [e] at h
    linarith
  · rw [hff]
    have : I / 2 - (ρ₀.im : ℂ) = (⟨-ρ₀.im, 1 / 2⟩ : ℂ) := by apply Complex.ext <;> simp
    rw [this]
    exact lowHeightProfile_eq_zero_of_mem (by unfold lowHeightRoots; simp)
  · rw [hff]
    have : -(I / 2) - (ρ₀.im : ℂ) = conj (⟨-ρ₀.im, 1 / 2⟩ : ℂ) := by apply Complex.ext <;> simp
    rw [this]
    exact lowHeightProfile_eq_zero_of_conj_mem (by unfold lowHeightRoots; simp)
  · have hW := re_W_lowHeightTest_le Z hA₀ hloc hρ₀ hδ hδ2 hre hγ hH hWn hKW hKn hε0 hε1 hη0
      hclu hkil hS hc hk hF0re (E := 4 * N₀ - 4 * n - 11) (by omega)
    have hfloor := lowHeightFloor_le hδ hγ hη0 hη1 hηlow hKn hkil hk
    have hHE : 0 < (1 + H) ^ (4 * N₀ - 4 * n - 11) := by positivity
    have hkey : lowHeightTailConstant (H + |ρ₀.im| + 1) N₀ n / (1 + H) ^ (4 * N₀ - 4 * n - 11) *
        (24 * A₀ * Real.log (|ρ₀.im| + 3)) < 79 / 50 * lowHeightFloor δ N₀ n := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ hHE]
      linarith
    linarith

/-- **The level-`a` Hodge index excludes low off-line zeros.**  Under `HodgeIndexAtLevel Z a`, no
zero `ρ₀ = ½ + δ + iγ₀` with `|γ₀| ≥ 1` satisfies the size condition of
`exists_hodge_violation_low_height`. -/
theorem not_hodge_index_of_low_offLine_zero (Z : ZeroConfig) {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3)) {a : ℝ}
    (hodge : HodgeIndexAtLevel Z a)
    {ρ₀ : ℂ} (hρ₀ : ρ₀ ∈ Z.carrier) {δ : ℝ} (hδ : 0 < δ) (hre : ρ₀.re = 1 / 2 + δ)
    (hγ : 1 ≤ |ρ₀.im|) {H : ℝ} (hH : 1 ≤ H) {N₀ n : ℕ} (hN₀a : (N₀ : ℝ) ≤ a)
    (hn : (Z.finite_window (ρ₀.im - H) (ρ₀.im + H)).toFinset.card ≤ n) (hNn : 2 * n + 7 ≤ N₀) :
    79 / 50 * (1 + H) ^ (4 * N₀ - 4 * n - 11) * lowHeightFloor δ N₀ n ≤
      lowHeightTailConstant (H + |ρ₀.im| + 1) N₀ n * (24 * A₀ * Real.log (|ρ₀.im| + 3)) := by
  by_contra h
  obtain ⟨f, hf, hfs, hp, hm, hneg⟩ := exists_hodge_violation_low_height Z hA₀ hloc hρ₀ hδ hre
    hγ hH hN₀a hn hNn (lt_of_not_ge h)
  exact absurd (hodge f hf hfs hp hm) (not_le.mpr hneg)

/-- The low-height exclusion for the nontrivial zeros of `ζ`, with the unconditional local count. -/
theorem zeta_hodge_index_excludes_low_offLine_zeros :
    ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ a : ℝ, HodgeIndexAtLevel zetaZeroConfig a →
      ∀ ρ₀ ∈ zetaZeroConfig.carrier, ∀ δ : ℝ, 0 < δ → ρ₀.re = 1 / 2 + δ → 1 ≤ |ρ₀.im| →
      ∀ H : ℝ, 1 ≤ H → ∀ N₀ n : ℕ, (N₀ : ℝ) ≤ a →
        (zetaZeroConfig.finite_window (ρ₀.im - H) (ρ₀.im + H)).toFinset.card ≤ n →
        2 * n + 7 ≤ N₀ →
        79 / 50 * (1 + H) ^ (4 * N₀ - 4 * n - 11) * lowHeightFloor δ N₀ n ≤
          lowHeightTailConstant (H + |ρ₀.im| + 1) N₀ n * (24 * A₀ * Real.log (|ρ₀.im| + 3)) := by
  obtain ⟨A₀, hA₀, hloc⟩ := Zeta23.RvM.zetaZeroConfig_local_count
  exact ⟨A₀, hA₀, fun a hodge ρ₀ hρ₀ δ hδ hre hγ H hH N₀ n hN₀a hn hNn =>
    not_hodge_index_of_low_offLine_zero zetaZeroConfig hA₀ hloc hodge hρ₀ hδ hre hγ hH hN₀a hn hNn⟩

/-! ### Every off-line zero is excluded at all large levels -/

theorem unitWeightFloor_ge : (48 / 100 : ℝ) ≤ unitWeightFloor := by
  unfold unitWeightFloor
  rw [show (5 / 2 : ℝ) = 2 + 1 / 2 by norm_num, Real.rpow_add (by norm_num),
    ← Real.sqrt_eq_rpow, show ((3 / 4 : ℝ) ^ (2 : ℝ)) = 9 / 16 by norm_num]
  have hs : (86 / 100 : ℝ) ≤ Real.sqrt (3 / 4) := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  nlinarith

/-- Exponential growth beats a polynomial. -/
theorem eventually_mul_pow_lt_mul_pow {r : ℝ} (hr : 1 < r) (C K : ℝ) (hK : 0 < K) (k : ℕ) :
    ∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N → C * (N : ℝ) ^ k < K * r ^ N := by
  rcases le_or_gt C 0 with hC | hC
  · refine ⟨0, fun N _ => ?_⟩
    have : 0 ≤ (N : ℝ) ^ k := by positivity
    have : 0 < K * r ^ N := by positivity
    nlinarith
  have ht := tendsto_pow_const_div_const_pow_of_one_lt k hr
  have hev := ht.eventually (gt_mem_nhds (show (0 : ℝ) < K / C by positivity))
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp hev
  refine ⟨N₁, fun N hN => ?_⟩
  have h := hN₁ N hN
  have hrN : 0 < r ^ N := by positivity
  rw [div_lt_div_iff₀ hrN hC] at h
  linarith

/-- For fixed data, the size condition of `exists_hodge_violation_low_height` holds at every
large level (with window half-width `H = 100`). -/
theorem eventually_lowHeight_condition {δ : ℝ} (hδ : 0 < δ) (γ₀ A₀ : ℝ) (n : ℕ) :
    ∃ N₁ : ℕ, ∀ N₀ : ℕ, N₁ ≤ N₀ →
      lowHeightTailConstant (100 + |γ₀| + 1) N₀ n * (24 * A₀ * Real.log (|γ₀| + 3)) <
        79 / 50 * (1 + 100) ^ (4 * N₀ - 4 * n - 11) * lowHeightFloor δ N₀ n := by
  have hB0 : 0 < Real.exp (1 / 2) * 168 := by positivity
  have hW₀0 : 0 < unitWeightFloor := unitWeightFloor_pos
  have hm0 : 0 < min δ 1 := lt_min hδ one_pos
  have hlam0 : 0 < lowHeightScale n := by unfold lowHeightScale; positivity
  set B := Real.exp (1 / 2) * 168 with hB
  set Q := (101 : ℝ) ^ 2 * unitWeightFloor with hQ
  have hr : 1 < (Q / B) ^ 2 := by
    have hB2 : B ≤ 2 * 168 := by rw [hB]; nlinarith [exp_one_half_lt_two]
    have : 1 < Q / B := by
      rw [lt_div_iff₀ hB0, hQ]
      nlinarith [unitWeightFloor_ge]
    nlinarith
  set K := 79 / 50 * (min δ 1 / lowHeightScale n ^ n) ^ (4 * n) * δ ^ 4 with hK
  have hK0 : 0 < K := by rw [hK]; positivity
  set C := (100 + |γ₀| + 1) ^ (4 * n + 8) * (24 * A₀ * Real.log (|γ₀| + 3)) *
    (600 : ℝ) ^ (4 * n) * (101 : ℝ) ^ (4 * n + 11) with hC
  obtain ⟨N₂, hN₂⟩ := eventually_mul_pow_lt_mul_pow hr C K hK0 (4 * n)
  refine ⟨max N₂ (n + 3), fun N₀ hN₀ => ?_⟩
  have hN₂' : N₂ ≤ N₀ := le_of_max_le_left hN₀
  have hn3 : n + 3 ≤ N₀ := le_of_max_le_right hN₀
  have hgrow := hN₂ N₀ hN₂'
  have hN0 : (1 : ℝ) ≤ N₀ := by exact_mod_cast (by omega : 1 ≤ N₀)
  set E := 4 * N₀ - 4 * n - 11 with hE
  have hsplit : (101 : ℝ) ^ E * (101 : ℝ) ^ (4 * n + 11) = (101 : ℝ) ^ (4 * N₀) := by
    rw [← pow_add]; congr 1; omega
  have hQpow : Q ^ (2 * N₀) = (101 : ℝ) ^ (4 * N₀) * unitWeightFloor ^ (2 * N₀) := by
    rw [hQ, mul_pow, ← pow_mul]; ring_nf
  -- lower bound for the right side
  set Rlow := 79 / 50 * (101 : ℝ) ^ E * unitWeightFloor ^ (2 * N₀) *
    (min δ 1 / lowHeightScale n ^ n) ^ (4 * n) * δ ^ 4 / (600 * (N₀ : ℝ)) ^ (4 * n) with hRlowDef
  have hRlow : Rlow ≤ 79 / 50 * (1 + 100) ^ E * lowHeightFloor δ N₀ n := by
    unfold lowHeightFloor lowHeightEps0
    have hden : 0 < 100 * (3 * (N₀ : ℝ) + 3) := by positivity
    have hle : 100 * (3 * (N₀ : ℝ) + 3) ≤ 600 * N₀ := by nlinarith
    have hpowle : (100 * (3 * (N₀ : ℝ) + 3)) ^ (4 * n) ≤ (600 * (N₀ : ℝ)) ^ (4 * n) :=
      pow_le_pow_left₀ hden.le hle _
    have e : (min δ 1 / (100 * (3 * (N₀ : ℝ) + 3)) / lowHeightScale n ^ n) ^ (4 * n) =
        (min δ 1 / lowHeightScale n ^ n) ^ (4 * n) / (100 * (3 * (N₀ : ℝ) + 3)) ^ (4 * n) := by
      rw [div_div, mul_comm (100 * (3 * (N₀ : ℝ) + 3)), ← div_div, div_pow]
    rw [e, hRlowDef, show (1 + 100 : ℝ) = 101 by norm_num]
    have hA : 0 ≤ 79 / 50 * (101 : ℝ) ^ E * unitWeightFloor ^ (2 * N₀) *
        (min δ 1 / lowHeightScale n ^ n) ^ (4 * n) * δ ^ 4 := by positivity
    calc 79 / 50 * (101 : ℝ) ^ E * unitWeightFloor ^ (2 * N₀) *
          (min δ 1 / lowHeightScale n ^ n) ^ (4 * n) * δ ^ 4 / (600 * (N₀ : ℝ)) ^ (4 * n)
        ≤ 79 / 50 * (101 : ℝ) ^ E * unitWeightFloor ^ (2 * N₀) *
          (min δ 1 / lowHeightScale n ^ n) ^ (4 * n) * δ ^ 4 /
            (100 * (3 * (N₀ : ℝ) + 3)) ^ (4 * n) :=
          div_le_div_of_nonneg_left hA (by positivity) hpowle
      _ = _ := by ring
  refine lt_of_lt_of_le ?_ hRlow
  -- the growth comparison
  have hBpos : 0 < B ^ (2 * N₀) := by positivity
  have hkey : B ^ (2 * N₀) * (C * (N₀ : ℝ) ^ (4 * n)) < B ^ (2 * N₀) * (K * ((Q / B) ^ 2) ^ N₀) :=
    mul_lt_mul_of_pos_left hgrow hBpos
  have hrpow : B ^ (2 * N₀) * ((Q / B) ^ 2) ^ N₀ = Q ^ (2 * N₀) := by
    rw [← pow_mul, div_pow, mul_div_cancel₀ _ (by positivity)]
  have h101 : 0 < (101 : ℝ) ^ (4 * n + 11) := by positivity
  have hden6 : 0 < (600 * (N₀ : ℝ)) ^ (4 * n) := by positivity
  rw [hRlowDef, lt_div_iff₀ hden6]
  unfold lowHeightTailConstant
  rw [← hB]
  have hlhs : B ^ (2 * N₀) * (100 + |γ₀| + 1) ^ (4 * n + 8) * (24 * A₀ * Real.log (|γ₀| + 3)) *
      (600 * (N₀ : ℝ)) ^ (4 * n) * (101 : ℝ) ^ (4 * n + 11) =
      B ^ (2 * N₀) * (C * (N₀ : ℝ) ^ (4 * n)) := by
    rw [hC, mul_pow]; ring
  have hrhs : 79 / 50 * (101 : ℝ) ^ E * unitWeightFloor ^ (2 * N₀) *
      (min δ 1 / lowHeightScale n ^ n) ^ (4 * n) * δ ^ 4 * (101 : ℝ) ^ (4 * n + 11) =
      B ^ (2 * N₀) * (K * ((Q / B) ^ 2) ^ N₀) := by
    rw [mul_comm K, ← mul_assoc, hrpow, hQpow, ← hsplit, hK]; ring
  nlinarith [hlhs, hrhs, hkey]

/-- **Every off-line zero violates the Hodge index at all large levels.**  For a configuration
with local count `A₀` and a zero `ρ₀ = ½ + δ + iγ₀` with `δ > 0` and `|γ₀| ≥ 1`, there is `a₀`
such that the level-`a` Hodge index fails for every `a ≥ a₀`. -/
theorem eventually_not_hodgeIndex (Z : ZeroConfig) {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3))
    {ρ₀ : ℂ} (hρ₀ : ρ₀ ∈ Z.carrier) {δ : ℝ} (hδ : 0 < δ) (hre : ρ₀.re = 1 / 2 + δ)
    (hγ : 1 ≤ |ρ₀.im|) :
    ∃ a₀ : ℝ, ∀ a : ℝ, a₀ ≤ a → ¬ HodgeIndexAtLevel Z a := by
  set n := (Z.finite_window (ρ₀.im - 100) (ρ₀.im + 100)).toFinset.card with hn
  obtain ⟨N₁, hN₁⟩ := eventually_lowHeight_condition hδ ρ₀.im A₀ n
  refine ⟨((max N₁ (2 * n + 7) : ℕ) : ℝ), fun a ha hodge => ?_⟩
  have ha0 : 0 ≤ a := le_trans (Nat.cast_nonneg _) ha
  set N₀ := ⌊a⌋₊ with hN₀
  have hN₀a : (N₀ : ℝ) ≤ a := Nat.floor_le ha0
  have h1 : (N₁ : ℝ) ≤ a := le_trans (by exact_mod_cast le_max_left N₁ (2 * n + 7)) ha
  have h2 : ((2 * n + 7 : ℕ) : ℝ) ≤ a := le_trans (by exact_mod_cast le_max_right N₁ (2 * n + 7)) ha
  have hN₁N₀ : N₁ ≤ N₀ := Nat.le_floor h1
  have hnN₀ : 2 * n + 7 ≤ N₀ := Nat.le_floor h2
  have hbig := hN₁ N₀ hN₁N₀
  have := not_hodge_index_of_low_offLine_zero Z hA₀ hloc hodge hρ₀ hδ hre hγ (H := 100)
    (by norm_num) hN₀a le_rfl hnN₀
  linarith

/-- **The Hodge index at every level places every zero of `ζ` with `|γ| ≥ 1` on the critical
line.** -/
theorem zeta_re_eq_half_of_hodgeIndex (hodge : ∀ a : ℝ, HodgeIndexAtLevel zetaZeroConfig a)
    {ρ : ℂ} (hρ : ρ ∈ zetaZeroConfig.carrier) (hγ : 1 ≤ |ρ.im|) : ρ.re = 1 / 2 := by
  obtain ⟨A₀, hA₀, hloc⟩ := Zeta23.RvM.zetaZeroConfig_local_count
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · -- the reflected zero lies to the right
    have hρ' := zetaZeroConfig.reflect_mem ρ hρ
    have hre' : (reflect ρ).re = 1 / 2 + (1 / 2 - ρ.re) := by
      simp only [reflect, Complex.sub_re, Complex.one_re, Complex.conj_re]; ring
    have him' : (reflect ρ).im = ρ.im := by
      simp only [reflect, Complex.sub_im, Complex.one_im, Complex.conj_im]; ring
    obtain ⟨a₀, ha₀⟩ := eventually_not_hodgeIndex zetaZeroConfig hA₀ hloc hρ'
      (by linarith : (0 : ℝ) < 1 / 2 - ρ.re) hre' (by rw [him']; exact hγ)
    exact ha₀ a₀ le_rfl (hodge a₀)
  · obtain ⟨a₀, ha₀⟩ := eventually_not_hodgeIndex zetaZeroConfig hA₀ hloc hρ
      (by linarith : (0 : ℝ) < ρ.re - 1 / 2) (by ring) hγ
    exact ha₀ a₀ le_rfl (hodge a₀)

end RHTower
