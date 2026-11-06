import GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow.TheGapLawOfAdjacentZeros

/-!
# The cluster spreads at the exact rate

The localization of the averaged repulsion law. For `n` real points `y_i` the **spread** is `P = n Σ_i y_i² − (Σ_i y_i)² = Σ_{i<j} (y_j − y_i)²`. Under the pure Dyson flow of `n` points it grows at the exact rate `2n²(n − 1)`, whatever
the configuration: the singular forces cancel in pairs (`sum_mul_sum_inv_eq`).

For a cluster of `n` simple real zeros of the flow, isolated by a distance `ρ` from all other zeros of its packet, the exterior field acts only through its Lipschitz constant, and

`|dP/dt − 2n²(n − 1)| ≤ λ P`,  `λ ≪ log X/ρ²`    (`cluster_rate_le`, `exists_cluster_spread_law`).

So `P(b)` is `2n²(n − 1)(b − a) + P(a)` up to the factor `e^{±λ(b − a)}`, at every height. The law needs no separation inside the cluster, and it is valid across all configurations of the cluster, as long as its zeros stay real and simple. This is what the mesh law cannot
say: a cluster as a whole opens at the rate of the Hermite model, with no factor `1/n`; its mean square gap grows like `4n(t − t₀)`.
-/

open Complex Filter Topology Set Metric MeasureTheory
open GaloisForLFunctions.HTGeometry RHTower RHTower.DeBruijn

namespace GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow

noncomputable section

/-! ## The algebra of the spread -/

/-- The spread of `n` real points. -/
def clusterSpread {n : ℕ} (y : Fin n → ℝ) : ℝ := (n : ℝ) * ∑ i, y i ^ 2 - (∑ i, y i) ^ 2

/-- The mean of `n` real points. -/
def clusterMean {n : ℕ} (y : Fin n → ℝ) : ℝ := (∑ i, y i) / n

/-- The spread is half the double sum of the squared differences. -/
theorem clusterSpread_eq {n : ℕ} (y : Fin n → ℝ) :
    clusterSpread y = (∑ i, ∑ j, (y i - y j) ^ 2) / 2 := by
  have h : ∑ i, ∑ j, (y i - y j) ^ 2 = 2 * ((n : ℝ) * ∑ i, y i ^ 2 - (∑ i, y i) ^ 2) := by
    simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum, ← Finset.sum_mul]
    rw [sq (∑ i, y i)]
    ring
  rw [h, clusterSpread]
  ring

theorem clusterSpread_nonneg {n : ℕ} (y : Fin n → ℝ) : 0 ≤ clusterSpread y := by
  rw [clusterSpread_eq]
  positivity

/-- The deviations from the mean sum to zero. -/
theorem sum_sub_clusterMean {n : ℕ} (hn : 0 < n) (y : Fin n → ℝ) : ∑ i, (y i - clusterMean y) = 0 := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    clusterMean]
  field_simp
  ring

/-- `P = n Σ_i (y_i − ȳ)²`. -/
theorem clusterSpread_eq_mul_sum_sq {n : ℕ} (hn : 0 < n) (y : Fin n → ℝ) :
    clusterSpread y = (n : ℝ) * ∑ i, (y i - clusterMean y) ^ 2 := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum, ← Finset.sum_mul, clusterSpread, clusterMean]
  field_simp
  ring

/-- **The singular forces cancel in pairs.** `Σ_i (y_i − c) Σ_{j ≠ i} 1/(y_i − y_j) = n(n − 1)/2`, for every `c`. -/
theorem sum_mul_sum_inv_eq {n : ℕ} {y : Fin n → ℝ} (hy : Function.Injective y) (c : ℝ) :
    ∑ i, (y i - c) * ∑ j ∈ Finset.univ.erase i, 1 / (y i - y j) = (n : ℝ) * ((n : ℝ) - 1) / 2 := by
  classical
  set f : Fin n → Fin n → ℝ := fun i j => if i = j then 0 else (y i - c) / (y i - y j) with hf
  have h1 : ∑ i, (y i - c) * ∑ j ∈ Finset.univ.erase i, 1 / (y i - y j) = ∑ i, ∑ j, f i j := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, ← Finset.add_sum_erase Finset.univ (f i) (Finset.mem_univ i)]
    simp only [hf, if_true, zero_add]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hij : i ≠ j := (Finset.mem_erase.mp hj).1.symm
    rw [if_neg hij]
    ring
  have h2 : ∑ i, ∑ j, f i j = ∑ i, ∑ j, f j i := Finset.sum_comm
  have h3 : ∑ i, ∑ j, (f i j + f j i) = (n : ℝ) * ((n : ℝ) - 1) := by
    have h4 (i : Fin n) : ∑ j, (f i j + f j i) = (n : ℝ) - 1 := by
      rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)]
      simp only [hf, if_true, add_zero, zero_add]
      have h5 : ∀ j ∈ Finset.univ.erase i,
          (if i = j then (0 : ℝ) else (y i - c) / (y i - y j)) +
            (if j = i then (0 : ℝ) else (y j - c) / (y j - y i)) = 1 := by
        intro j hj
        have hij : i ≠ j := (Finset.mem_erase.mp hj).1.symm
        rw [if_neg hij, if_neg hij.symm]
        have h6 : y i - y j ≠ 0 := sub_ne_zero.mpr fun h => hij (hy h)
        have h7 : y j - y i ≠ 0 := sub_ne_zero.mpr fun h => hij (hy h).symm
        rw [show y j - y i = -(y i - y j) by ring, div_neg]
        field_simp
        ring
      rw [Finset.sum_congr rfl h5, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i),
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, Nat.cast_sub (by
          have := i.isLt
          omega)]
      simp
    rw [Finset.sum_congr rfl fun i _ => h4 i, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
  have h5 : ∑ i, ∑ j, (f i j + f j i) = ∑ i, ∑ j, f i j + ∑ i, ∑ j, f j i := by
    simp only [Finset.sum_add_distrib]
  rw [h1]
  linarith only [h2, h3, h5]

/-! ## The rate of the spread -/

/-- **The rate of the spread of a cluster at one time.** For `n` real simple zeros of `H_t` in the inner window, at distance at least `ρ` from all other zeros of the packet, `2n Σ_i (y_i − ȳ) Re V_i` differs from `2n²(n − 1)` by at most `4(M/ρ² + K) P`. -/
theorem cluster_rate_le {t X K M ρ : ℝ} {S : Finset ℂ} {Q : ℂ → ℂ} {n : ℕ} (hn : 0 < n) {y : Fin n → ℝ} (ht : 0 < t)
    (hpacket : ∀ a, a ∈ S ↔ riemannHeat t a = 0 ∧ |a.re - X| ≤ 2)
    (hcount : ((∑ a ∈ S, zeroMult (riemannHeat t) a : ℕ) : ℝ) ≤ M)
    (hQ : ∀ z, |z.re - X| ≤ 1 → |z.im| ≤ 1 / 2 →
      AnalyticAt ℂ Q z ∧ ‖deriv Q z‖ ≤ K ∧ (riemannHeat t z ≠ 0 →
        logDeriv (riemannHeat t) z = (∑ b ∈ S, (zeroMult (riemannHeat t) b : ℂ) / (z - b)) + Q z))
    (hρ : 0 < ρ) (hy : Function.Injective y) (h0 : ∀ i, riemannHeat t (y i : ℂ) = 0)
    (hd : ∀ i, deriv (riemannHeat t) (y i : ℂ) ≠ 0) (hX : ∀ i, |y i - X| < 1)
    (hiso : ∀ b ∈ S, (∀ i, b ≠ (y i : ℂ)) → (∀ i, ρ ≤ ‖(y i : ℂ) - b‖) ∧ ρ ≤ ‖(clusterMean y : ℂ) - b‖) :
    |2 * (n : ℝ) * ∑ i, (y i - clusterMean y) * (zeroVelocity t (y i : ℂ)).re -
        2 * (n : ℝ) ^ 2 * ((n : ℝ) - 1)| ≤ 4 * (M / ρ ^ 2 + K) * clusterSpread y := by
  classical
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  set c := clusterMean y with hc
  have hK0 : 0 ≤ K := by
    have hin : |((y ⟨0, hn⟩ : ℝ) : ℂ).re - X| ≤ 1 ∧ |((y ⟨0, hn⟩ : ℝ) : ℂ).im| ≤ 1 / 2 := by
      constructor
      · rw [Complex.ofReal_re]; exact (hX _).le
      · rw [Complex.ofReal_im, abs_zero]; norm_num
    exact (norm_nonneg _).trans (hQ _ hin.1 hin.2).2.1
  -- the mean lies in the window
  have hcX : |c - X| < 1 := by
    have hne : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0, hn⟩, Finset.mem_univ _⟩
    have h1 : ∑ i : Fin n, (X - 1) < ∑ i, y i :=
      Finset.sum_lt_sum_of_nonempty hne fun i _ => by
        have := (abs_lt.mp (hX i)).1
        linarith only [this]
    have h2 : ∑ i, y i < ∑ i : Fin n, (X + 1) :=
      Finset.sum_lt_sum_of_nonempty hne fun i _ => by
        have := (abs_lt.mp (hX i)).2
        linarith only [this]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h1 h2
    have h3 : c * n = ∑ i, y i := by
      rw [hc, clusterMean]
      field_simp
    rw [abs_lt]
    constructor
    · have : (X - 1) * n < c * n := by rw [h3]; rwa [mul_comm]
      have := lt_of_mul_lt_mul_right this hn0.le
      linarith only [this]
    · have : c * n < (X + 1) * n := by rw [h3]; rwa [mul_comm]
      have := lt_of_mul_lt_mul_right this hn0.le
      linarith only [this]
  -- the cluster inside the packet and the exterior
  set Y : Fin n → ℂ := fun i => (y i : ℂ) with hYdef
  have hYinj : Function.Injective Y := fun i j h => hy (Complex.ofReal_injective h)
  set T := (Finset.univ : Finset (Fin n)).image Y with hT
  have hTS : T ⊆ S := by
    intro a ha
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp ha
    refine (hpacket _).mpr ⟨h0 i, ?_⟩
    simp only [hYdef, Complex.ofReal_re]
    linarith only [(hX i).le]
  set E := S \ T with hE
  set W : ℂ → ℂ := fun z => (∑ b ∈ E, (zeroMult (riemannHeat t) b : ℂ) / (z - b)) + Q z with hW
  have hmone (i : Fin n) : zeroMult (riemannHeat t) (Y i) = 1 :=
    zeroMult_riemannHeat_eq_one ht.le (h0 i) (hd i)
  -- the velocity in terms of the cluster and the exterior
  have hvel (i : Fin n) : zeroVelocity t (Y i) =
      2 * (((∑ j ∈ Finset.univ.erase i, 1 / (y i - y j) : ℝ) : ℂ) + W (Y i)) := by
    have hv := simple_heat_zero_velocity_eq_exterior ht hpacket
      (fun z h1 h2 => ⟨(hQ z h1 h2).1, (hQ z h1 h2).2.2⟩) (h0 i) (hd i)
      (by simp only [Complex.ofReal_re]; exact hX i)
    have hsplit : S.erase (Y i) = E ∪ (T.erase (Y i)) := by
      ext b
      simp only [hE, Finset.mem_erase, Finset.mem_union, Finset.mem_sdiff]
      constructor
      · rintro ⟨h1, h2⟩
        by_cases hb : b ∈ T
        · exact Or.inr ⟨h1, hb⟩
        · exact Or.inl ⟨h2, hb⟩
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · refine ⟨?_, h1⟩
          rintro rfl
          exact h2 (Finset.mem_image_of_mem _ (Finset.mem_univ i))
        · exact ⟨h1, hTS h2⟩
    have hdisj : Disjoint E (T.erase (Y i)) := Finset.disjoint_left.mpr fun b h1 h2 =>
      (Finset.mem_sdiff.mp h1).2 (Finset.mem_erase.mp h2).2
    have himg : T.erase (Y i) = (Finset.univ.erase i).image Y := by
      ext b
      constructor
      · intro hb
        obtain ⟨h1, h2⟩ := Finset.mem_erase.mp hb
        obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp h2
        exact Finset.mem_image.mpr ⟨j, Finset.mem_erase.mpr ⟨fun h => h1 (by rw [h]), Finset.mem_univ _⟩, rfl⟩
      · intro hb
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hb
        exact Finset.mem_erase.mpr ⟨fun h => (Finset.mem_erase.mp hj).1 (hYinj h),
          Finset.mem_image_of_mem _ (Finset.mem_univ j)⟩
    have hsum : ∑ b ∈ T.erase (Y i), (zeroMult (riemannHeat t) b : ℂ) / (Y i - b) =
        ((∑ j ∈ Finset.univ.erase i, 1 / (y i - y j) : ℝ) : ℂ) := by
      rw [himg, Finset.sum_image fun a _ b _ h => hYinj h]
      push_cast
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hmone j, Nat.cast_one]
    change deriv (deriv (riemannHeat t)) (Y i) / deriv (riemannHeat t) (Y i) = _
    rw [hv, hsplit, Finset.sum_union hdisj, hsum]
    simp only [hW]
    ring
  -- the Lipschitz bound of the exterior
  have hQlip (x : ℝ) (hx : |x - X| < 1) : ‖Q (x : ℂ) - Q (c : ℂ)‖ ≤ K * |x - c| := by
    set D : Set ℂ := {z | |z.re - X| ≤ 1 ∧ |z.im| ≤ 1 / 2} with hDdef
    have hDc : Convex ℝ D := by
      have h1 : Convex ℝ {z : ℂ | |z.re - X| ≤ 1} := by
        have : {z : ℂ | |z.re - X| ≤ 1} = Complex.re ⁻¹' (Set.Icc (X - 1) (X + 1)) := by
          ext z
          simp only [mem_setOf_eq, mem_preimage, mem_Icc, abs_le]
          constructor
          · rintro ⟨h1, h2⟩; constructor <;> linarith only [h1, h2]
          · rintro ⟨h1, h2⟩; constructor <;> linarith only [h1, h2]
        rw [this]
        exact (convex_Icc _ _).is_linear_preimage Complex.reLm.isLinear
      have h2 : Convex ℝ {z : ℂ | |z.im| ≤ 1 / 2} := by
        have : {z : ℂ | |z.im| ≤ 1 / 2} = Complex.im ⁻¹' (Set.Icc (-(1 / 2)) (1 / 2)) := by
          ext z
          simp only [mem_setOf_eq, mem_preimage, mem_Icc, abs_le]
        rw [this]
        exact (convex_Icc _ _).is_linear_preimage Complex.imLm.isLinear
      exact h1.inter h2
    have hinD (w : ℝ) (hw : |w - X| < 1) : (w : ℂ) ∈ D := by
      constructor
      · rw [Complex.ofReal_re]; exact hw.le
      · rw [Complex.ofReal_im, abs_zero]; norm_num
    have h := hDc.norm_image_sub_le_of_norm_deriv_le (f := Q) (C := K)
      (fun z hz => (hQ z hz.1 hz.2).1.differentiableAt) (fun z hz => (hQ z hz.1 hz.2).2.1)
      (hinD c hcX) (hinD x hx)
    have hnorm : ‖(x : ℂ) - c‖ = |x - c| := by
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    rwa [hnorm] at h
  have hEmass : ∑ b ∈ E, (zeroMult (riemannHeat t) b : ℝ) ≤ M := by
    refine le_trans ?_ hcount
    rw [Nat.cast_sum]
    exact Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset fun _ _ _ => Nat.cast_nonneg _
  have hρ2 : 0 < ρ ^ 2 := by positivity
  have hMpos : 0 ≤ M := le_trans (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _) hEmass
  have hlip (i : Fin n) : ‖W (Y i) - W (c : ℂ)‖ ≤ (M / ρ ^ 2 + K) * |y i - c| := by
    have hpole : ‖(∑ b ∈ E, (zeroMult (riemannHeat t) b : ℂ) / (Y i - b)) -
        ∑ b ∈ E, (zeroMult (riemannHeat t) b : ℂ) / ((c : ℂ) - b)‖ ≤ M / ρ ^ 2 * |y i - c| := by
      rw [← Finset.sum_sub_distrib]
      refine (norm_sum_le _ _).trans ?_
      have hterm : ∀ b ∈ E, ‖(zeroMult (riemannHeat t) b : ℂ) / (Y i - b) -
          (zeroMult (riemannHeat t) b : ℂ) / ((c : ℂ) - b)‖ ≤
          (zeroMult (riemannHeat t) b : ℝ) * (|y i - c| / ρ ^ 2) := by
        intro b hb
        obtain ⟨hbS, hbT⟩ := Finset.mem_sdiff.mp hb
        have hnot : ∀ j, b ≠ (y j : ℂ) := fun j h => hbT (by
          rw [h]
          exact Finset.mem_image_of_mem Y (Finset.mem_univ j))
        obtain ⟨h1, h2⟩ := hiso b hbS hnot
        have h3 := h1 i
        have hne1 : (Y i - b) ≠ 0 := by
          intro h
          rw [show (y i : ℂ) - b = Y i - b from rfl, h, norm_zero] at h3
          linarith only [h3, hρ]
        have hne2 : ((c : ℂ) - b) ≠ 0 := by
          intro h
          rw [h, norm_zero] at h2
          linarith only [h2, hρ]
        have hid : (zeroMult (riemannHeat t) b : ℂ) / (Y i - b) -
            (zeroMult (riemannHeat t) b : ℂ) / ((c : ℂ) - b) =
            (zeroMult (riemannHeat t) b : ℂ) * (((c : ℂ) - Y i) / ((Y i - b) * ((c : ℂ) - b))) := by
          field_simp
          ring
        rw [hid, norm_mul, Complex.norm_natCast, norm_div, norm_mul]
        refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
        have hnum : ‖(c : ℂ) - Y i‖ = |y i - c| := by
          simp only [hYdef]
          rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
        rw [hnum]
        refine div_le_div_of_nonneg_left (abs_nonneg _) hρ2 ?_
        rw [sq]
        exact mul_le_mul h3 h2 hρ.le (norm_nonneg _)
      refine (Finset.sum_le_sum hterm).trans ?_
      rw [← Finset.sum_mul]
      have h4 := mul_le_mul_of_nonneg_right hEmass (by positivity : 0 ≤ |y i - c| / ρ ^ 2)
      refine h4.trans (le_of_eq ?_)
      ring
    have hsplit : W (Y i) - W (c : ℂ) = ((∑ b ∈ E, (zeroMult (riemannHeat t) b : ℂ) / (Y i - b)) -
        ∑ b ∈ E, (zeroMult (riemannHeat t) b : ℂ) / ((c : ℂ) - b)) + (Q (Y i) - Q (c : ℂ)) := by
      simp only [hW]
      ring
    rw [hsplit]
    refine (norm_add_le _ _).trans ?_
    have := hQlip (y i) (hX i)
    rw [add_mul]
    exact add_le_add hpole this
  -- the sum over the cluster
  have hzero : ∑ i, ((y i - c : ℝ) : ℂ) = 0 := by
    rw [← Complex.ofReal_sum, sum_sub_clusterMean hn y, Complex.ofReal_zero]
  have hsumV : ∑ i, ((y i - c : ℝ) : ℂ) * zeroVelocity t (Y i) =
      (((n : ℝ) * ((n : ℝ) - 1) : ℝ) : ℂ) + 2 * ∑ i, ((y i - c : ℝ) : ℂ) * (W (Y i) - W (c : ℂ)) := by
    have hint := sum_mul_sum_inv_eq hy c
    have h1 : ∑ i, ((y i - c : ℝ) : ℂ) * (W (Y i) - W (c : ℂ)) = ∑ i, ((y i - c : ℝ) : ℂ) * W (Y i) := by
      simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hzero, zero_mul, sub_zero]
    rw [h1]
    simp only [hvel]
    have h2 : ∀ i, ((y i - c : ℝ) : ℂ) * (2 * (((∑ j ∈ Finset.univ.erase i, 1 / (y i - y j) : ℝ) : ℂ) + W (Y i))) =
        2 * (((y i - c) * ∑ j ∈ Finset.univ.erase i, 1 / (y i - y j) : ℝ) : ℂ) +
          2 * (((y i - c : ℝ) : ℂ) * W (Y i)) := by
      intro i
      push_cast
      ring
    simp only [h2, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [← Complex.ofReal_sum, hint]
    push_cast
    ring
  -- taking real parts
  have hre : ∑ i, (y i - c) * (zeroVelocity t (y i : ℂ)).re =
      (n : ℝ) * ((n : ℝ) - 1) + 2 * (∑ i, ((y i - c : ℝ) : ℂ) * (W (Y i) - W (c : ℂ))).re := by
    have h1 := congrArg Complex.re hsumV
    have h2re (Z : ℂ) : ((2 : ℂ) * Z).re = 2 * Z.re := by simp
    rw [Complex.re_sum, Complex.add_re, Complex.ofReal_re, h2re] at h1
    rw [← h1]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.re_ofReal_mul]
  have hbound : ‖∑ i, ((y i - c : ℝ) : ℂ) * (W (Y i) - W (c : ℂ))‖ ≤ (M / ρ ^ 2 + K) * ∑ i, (y i - c) ^ 2 := by
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have h1 := mul_le_mul_of_nonneg_left (hlip i) (abs_nonneg (y i - c))
    refine h1.trans (le_of_eq ?_)
    rw [← sq_abs (y i - c)]
    ring
  have hP := clusterSpread_eq_mul_sum_sq hn y
  rw [← hc] at hP
  set Rr := (∑ i, ((y i - c : ℝ) : ℂ) * (W (Y i) - W (c : ℂ))) with hRr
  have hRe : |Rr.re| ≤ (M / ρ ^ 2 + K) * ∑ i, (y i - c) ^ 2 := (Complex.abs_re_le_norm _).trans hbound
  have hrw : 2 * (n : ℝ) * ∑ i, (y i - c) * (zeroVelocity t (y i : ℂ)).re - 2 * (n : ℝ) ^ 2 * ((n : ℝ) - 1) =
      4 * (n : ℝ) * Rr.re := by
    rw [hre]
    ring
  rw [hrw, abs_mul, abs_of_pos (by positivity : 0 < 4 * (n : ℝ)), hP]
  have h2 := mul_le_mul_of_nonneg_left hRe (by positivity : 0 ≤ 4 * (n : ℝ))
  refine h2.trans (le_of_eq ?_)
  ring

/-! ## The integrated law -/

/-- The derivative of the spread along paths. -/
theorem hasDerivAt_clusterSpread {n : ℕ} (hn : 0 < n) {x : Fin n → ℝ → ℝ} {v : Fin n → ℝ} {s : ℝ}
    (hx : ∀ i, HasDerivAt (x i) (v i) s) :
    HasDerivAt (fun u => clusterSpread fun i => x i u)
      (2 * (n : ℝ) * ∑ i, (x i s - clusterMean (fun i => x i s)) * v i) s := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have h1 : HasDerivAt (fun u => ∑ i, x i u ^ 2) (∑ i, 2 * x i s * v i) s := by
    have := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => (hx i).pow 2)
    refine this.congr_deriv (Finset.sum_congr rfl fun i _ => ?_)
    norm_num
  have h2 : HasDerivAt (fun u => ∑ i, x i u) (∑ i, v i) s :=
    HasDerivAt.fun_sum (u := Finset.univ) fun i _ => hx i
  have h3 := (h1.const_mul (n : ℝ)).sub (h2.pow 2)
  refine h3.congr_deriv ?_
  have h5 : ∑ i, (x i s - clusterMean (fun i => x i s)) * v i =
      ∑ i, x i s * v i - clusterMean (fun i => x i s) * ∑ i, v i := by
    simp only [sub_mul, Finset.sum_sub_distrib, Finset.mul_sum]
  have h6 : (n : ℝ) * clusterMean (fun i => x i s) = ∑ i, x i s := by
    rw [clusterMean]
    field_simp
  have h7 : ∑ i, 2 * x i s * v i = 2 * ∑ i, x i s * v i := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [h5, h7, ← h6]
  norm_num
  ring

/-- **The cluster spread law.** Let `x_1 < … ` be `n` continuous paths of simple real zeros in the inner window at height `X`, at distance at least `ρ ≤ 1` from all other zeros of the packet, also from the mean of the cluster. Then the spread `P` satisfies
`e^{−λ(b−a)} (P(a) + 2n²(n−1)(b − a)) ≤ P(b) ≤ e^{λ(b−a)} (P(a) + 2n²(n−1)(b − a))`, with `λ = C log X/ρ²`. -/
theorem exists_cluster_spread_law :
    ∃ C > 0, ∃ X₀ : ℝ, 4096 ≤ X₀ ∧ ∀ X : ℝ, X₀ ≤ X → ∀ a b : ℝ, 0 < a → a ≤ b → b ≤ 1 / 8 →
      b * Real.log X ≤ 1 → ∀ (n : ℕ) (x : Fin n → ℝ → ℝ) (ρ : ℝ), 0 < n → 0 < ρ → ρ ≤ 1 →
      (∀ i, ContinuousOn (x i) (Icc a b)) →
      (∀ s ∈ Icc a b, Function.Injective (fun i => x i s) ∧
        (∀ i, riemannHeat s (x i s : ℂ) = 0 ∧ deriv (riemannHeat s) (x i s : ℂ) ≠ 0 ∧ |x i s - X| < 1) ∧
        ∀ w : ℂ, riemannHeat s w = 0 → |w.re - X| ≤ 2 → (∀ i, w ≠ (x i s : ℂ)) →
          (∀ i, ρ ≤ ‖(x i s : ℂ) - w‖) ∧ ρ ≤ ‖(clusterMean (fun i => x i s) : ℂ) - w‖) →
      Real.exp (-(C * Real.log X / ρ ^ 2 * (b - a))) *
          (clusterSpread (fun i => x i a) + 2 * (n : ℝ) ^ 2 * ((n : ℝ) - 1) * (b - a)) ≤
        clusterSpread (fun i => x i b) ∧
      clusterSpread (fun i => x i b) ≤ Real.exp (C * Real.log X / ρ ^ 2 * (b - a)) *
          (clusterSpread (fun i => x i a) + 2 * (n : ℝ) ^ 2 * ((n : ℝ) - 1) * (b - a)) := by
  obtain ⟨C₀, hC₀, X₀, hX₀, hforce⟩ := exists_uniform_riemannHeat_exterior_force
  refine ⟨8 * C₀, by positivity, X₀, hX₀, ?_⟩
  intro X hX a b ha hab hb hbX n x ρ hn hρ hρ1 hxc hprop
  have hL : 0 < Real.log X := Real.log_pos (by linarith only [hX, hX₀])
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  set l := 8 * C₀ * Real.log X / ρ ^ 2 with hl
  have hl0 : 0 ≤ l := by positivity
  set Dd := 2 * (n : ℝ) ^ 2 * ((n : ℝ) - 1) with hDd
  have hDd0 : 0 ≤ Dd := by
    have : 0 ≤ (n : ℝ) - 1 := by linarith only [hn1]
    positivity
  set P : ℝ → ℝ := fun u => clusterSpread fun i => x i u with hP
  have hPc : ContinuousOn P (Icc a b) := by
    simp only [hP, clusterSpread]
    exact (continuousOn_const.mul (continuousOn_finsetSum _ fun i _ => (hxc i).pow 2)).sub
      ((continuousOn_finsetSum _ fun i _ => hxc i).pow 2)
  -- the rate
  have hrate (s : ℝ) (hs : s ∈ Ioo a b) : ∃ D, HasDerivAt P D s ∧ |D - Dd| ≤ l * P s := by
    have hsI : s ∈ Icc a b := Ioo_subset_Icc_self hs
    obtain ⟨hinj, hzero, hiso⟩ := hprop s hsI
    have hIcc : Icc a b ∈ 𝓝 s := Icc_mem_nhds hs.1 hs.2
    have hs0 : 0 < s := ha.trans hs.1
    have hsX : s * Real.log X ≤ 1 := (mul_le_mul_of_nonneg_right hs.2.le hL.le).trans hbX
    have hdx (i : Fin n) := hasDerivAt_real_zero_path hs0 ((hxc i).continuousAt hIcc)
      (Filter.eventually_of_mem hIcc fun u hu => ((hprop u hu).2.1 i).1) (hzero i).2.1
    obtain ⟨S, Q, hpacket, hcount, -, hQ⟩ := hforce X hX s hs0.le (hs.2.le.trans hb) hsX
    have hr := cluster_rate_le (K := C₀ * Real.log X) (M := C₀ * Real.log X) (ρ := ρ) (y := fun i => x i s) hn hs0
      hpacket hcount (fun z h1 h2 => ⟨(hQ z h1 h2).1, (hQ z h1 h2).2.2.1, (hQ z h1 h2).2.2.2.2⟩) hρ hinj
      (fun i => (hzero i).1) (fun i => (hzero i).2.1) (fun i => (hzero i).2.2)
      (fun w hw hne => hiso w ((hpacket w).mp hw).1 ((hpacket w).mp hw).2 hne)
    refine ⟨_, hasDerivAt_clusterSpread hn hdx, hr.trans ?_⟩
    have hP0 := clusterSpread_nonneg fun i => x i s
    refine mul_le_mul_of_nonneg_right ?_ hP0
    have hρ2 : ρ ^ 2 ≤ 1 := by nlinarith only [hρ, hρ1]
    have hρ3 : 0 < ρ ^ 2 := by positivity
    rw [hl, mul_add, le_div_iff₀ hρ3]
    have h1 : 4 * (C₀ * Real.log X / ρ ^ 2) * ρ ^ 2 = 4 * (C₀ * Real.log X) := by
      field_simp
    have hCL : 0 < C₀ * Real.log X := by positivity
    have h2 := mul_le_mul_of_nonneg_left hρ2 hCL.le
    nlinarith only [h1, h2, hCL]
  have hP0 (s : ℝ) : 0 ≤ P s := clusterSpread_nonneg _
  -- the upper bound
  set f : ℝ → ℝ := fun s => P s * Real.exp (-l * (s - a)) with hf
  have hfc : ContinuousOn f (Icc a b) :=
    hPc.mul (by fun_prop : Continuous fun s : ℝ => Real.exp (-l * (s - a))).continuousOn
  have hE (c s : ℝ) : HasDerivAt (fun u : ℝ => Real.exp (c * (u - a))) (Real.exp (c * (s - a)) * c) s := by
    have h1 : HasDerivAt (fun u : ℝ => c * (u - a)) c s := by
      simpa using ((hasDerivAt_id s).sub_const a).const_mul c
    exact h1.exp
  have hfd (s : ℝ) (hs : s ∈ Ioo a b) : ∃ D, HasDerivAt f D s ∧ D ≤ Dd := by
    obtain ⟨D, hD, hle⟩ := hrate s hs
    refine ⟨_, hD.mul (hE (-l) s), ?_⟩
    have hsa : 0 ≤ s - a := by linarith only [hs.1]
    have hexp1 : Real.exp (-l * (s - a)) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      nlinarith only [mul_nonneg hl0 hsa]
    have hexp0 : 0 < Real.exp (-l * (s - a)) := Real.exp_pos _
    have h2 := (abs_le.mp hle).2
    calc D * Real.exp (-l * (s - a)) + P s * (Real.exp (-l * (s - a)) * -l)
        = (D - l * P s) * Real.exp (-l * (s - a)) := by ring
      _ ≤ Dd * Real.exp (-l * (s - a)) := mul_le_mul_of_nonneg_right (by linarith only [h2]) hexp0.le
      _ ≤ Dd * 1 := mul_le_mul_of_nonneg_left hexp1 hDd0
      _ = Dd := mul_one _
  have hup : f b - f a ≤ Dd * (b - a) := by
    refine Convex.image_sub_le_mul_sub_of_deriv_le (D := Icc a b) (convex_Icc a b) hfc
      (by
        rw [interior_Icc]
        intro s hs
        obtain ⟨D, hD, -⟩ := hfd s hs
        exact hD.differentiableAt.differentiableWithinAt)
      (by
        rw [interior_Icc]
        intro s hs
        obtain ⟨D, hD, hle⟩ := hfd s hs
        rw [hD.deriv]
        exact hle) a (left_mem_Icc.mpr hab) b (right_mem_Icc.mpr hab) hab
  -- the lower bound
  set g : ℝ → ℝ := fun s => P s * Real.exp (l * (s - a)) with hg
  have hgc : ContinuousOn g (Icc a b) :=
    hPc.mul (by fun_prop : Continuous fun s : ℝ => Real.exp (l * (s - a))).continuousOn
  have hgd (s : ℝ) (hs : s ∈ Ioo a b) : ∃ D, HasDerivAt g D s ∧ Dd ≤ D := by
    obtain ⟨D, hD, hle⟩ := hrate s hs
    refine ⟨_, hD.mul (hE l s), ?_⟩
    have hsa : 0 ≤ s - a := by linarith only [hs.1]
    have hexp1 : 1 ≤ Real.exp (l * (s - a)) := Real.one_le_exp (mul_nonneg hl0 hsa)
    have h2 := (abs_le.mp hle).1
    calc Dd = Dd * 1 := (mul_one _).symm
      _ ≤ Dd * Real.exp (l * (s - a)) := mul_le_mul_of_nonneg_left hexp1 hDd0
      _ ≤ (D + l * P s) * Real.exp (l * (s - a)) :=
        mul_le_mul_of_nonneg_right (by linarith only [h2]) (Real.exp_pos _).le
      _ = D * Real.exp (l * (s - a)) + P s * (Real.exp (l * (s - a)) * l) := by ring
  have hdown : Dd * (b - a) ≤ g b - g a := by
    refine Convex.mul_sub_le_image_sub_of_le_deriv (D := Icc a b) (convex_Icc a b) hgc
      (by
        rw [interior_Icc]
        intro s hs
        obtain ⟨D, hD, -⟩ := hgd s hs
        exact hD.differentiableAt.differentiableWithinAt)
      (by
        rw [interior_Icc]
        intro s hs
        obtain ⟨D, hD, hle⟩ := hgd s hs
        rw [hD.deriv]
        exact hle) a (left_mem_Icc.mpr hab) b (right_mem_Icc.mpr hab) hab
  have hfa : f a = P a := by simp [hf]
  have hga : g a = P a := by simp [hg]
  have hfb : f b = P b * Real.exp (-l * (b - a)) := rfl
  have hgb : g b = P b * Real.exp (l * (b - a)) := rfl
  rw [hfa, hfb] at hup
  rw [hga, hgb] at hdown
  have hexpn : Real.exp (-(l * (b - a))) = Real.exp (-l * (b - a)) := by
    congr 1
    ring
  have hprod : Real.exp (l * (b - a)) * Real.exp (-l * (b - a)) = 1 := by
    rw [← Real.exp_add]
    simp
  have hPa : clusterSpread (fun i => x i a) = P a := rfl
  have hPb : clusterSpread (fun i => x i b) = P b := rfl
  rw [hPa, hPb]
  constructor
  · rw [hexpn]
    have h1 := mul_le_mul_of_nonneg_left (show P a + Dd * (b - a) ≤ P b * Real.exp (l * (b - a)) by
      linarith only [hdown]) (Real.exp_pos (-l * (b - a))).le
    refine h1.trans (le_of_eq ?_)
    calc Real.exp (-l * (b - a)) * (P b * Real.exp (l * (b - a)))
        = P b * (Real.exp (l * (b - a)) * Real.exp (-l * (b - a))) := by ring
      _ = P b := by rw [hprod, mul_one]
  · have h1 := mul_le_mul_of_nonneg_left (show P b * Real.exp (-l * (b - a)) ≤ P a + Dd * (b - a) by
      linarith only [hup]) (Real.exp_pos (l * (b - a))).le
    refine le_trans (le_of_eq ?_) h1
    calc P b = P b * (Real.exp (l * (b - a)) * Real.exp (-l * (b - a))) := by rw [hprod, mul_one]
      _ = _ := by ring

/-- **A cluster born at a zero of order `n`.** If the spread of `n` paths of simple real zeros tends to `0` at time `a`, then `P(b)` equals `2n²(n − 1)(b − a)`, up to the factor `e^{±λ(b−a)}`. This is the law of the Hermite profile for the actual flow, and it does not lose a factor of `n`. -/
theorem exists_cluster_spread_of_collision :
    ∃ C > 0, ∃ X₀ : ℝ, 4096 ≤ X₀ ∧ ∀ X : ℝ, X₀ ≤ X → ∀ a b : ℝ, 0 ≤ a → a < b → b ≤ 1 / 8 →
      b * Real.log X ≤ 1 → ∀ (n : ℕ) (x : Fin n → ℝ → ℝ) (ρ : ℝ), 0 < n → 0 < ρ → ρ ≤ 1 →
      (∀ i, ContinuousOn (x i) (Ioc a b)) →
      (∀ s ∈ Ioc a b, Function.Injective (fun i => x i s) ∧
        (∀ i, riemannHeat s (x i s : ℂ) = 0 ∧ deriv (riemannHeat s) (x i s : ℂ) ≠ 0 ∧ |x i s - X| < 1) ∧
        ∀ w : ℂ, riemannHeat s w = 0 → |w.re - X| ≤ 2 → (∀ i, w ≠ (x i s : ℂ)) →
          (∀ i, ρ ≤ ‖(x i s : ℂ) - w‖) ∧ ρ ≤ ‖(clusterMean (fun i => x i s) : ℂ) - w‖) →
      Tendsto (fun s => clusterSpread fun i => x i s) (𝓝[>] a) (𝓝 0) →
      Real.exp (-(C * Real.log X / ρ ^ 2 * (b - a))) * (2 * (n : ℝ) ^ 2 * ((n : ℝ) - 1) * (b - a)) ≤
        clusterSpread (fun i => x i b) ∧
      clusterSpread (fun i => x i b) ≤ Real.exp (C * Real.log X / ρ ^ 2 * (b - a)) *
          (2 * (n : ℝ) ^ 2 * ((n : ℝ) - 1) * (b - a)) := by
  obtain ⟨C, hC, X₀, hX₀, hlaw⟩ := exists_cluster_spread_law
  refine ⟨C, hC, X₀, hX₀, ?_⟩
  intro X hX a b ha hab hb hbX n x ρ hn hρ hρ1 hxc hprop hlim
  set l := C * Real.log X / ρ ^ 2 with hl
  set Dd := 2 * (n : ℝ) ^ 2 * ((n : ℝ) - 1) with hDd
  have hev : ∀ᶠ a' in 𝓝[>] a,
      Real.exp (-(l * (b - a'))) * ((clusterSpread fun i => x i a') + Dd * (b - a')) ≤
          clusterSpread (fun i => x i b) ∧
        clusterSpread (fun i => x i b) ≤
          Real.exp (l * (b - a')) * ((clusterSpread fun i => x i a') + Dd * (b - a')) := by
    filter_upwards [Ioo_mem_nhdsGT hab] with a' ha'
    have hsub : Icc a' b ⊆ Ioc a b := fun s hs => ⟨ha'.1.trans_le hs.1, hs.2⟩
    exact hlaw X hX a' b (ha.trans_lt ha'.1) ha'.2.le hb hbX n x ρ hn hρ hρ1
      (fun i => (hxc i).mono hsub) (fun s hs => hprop s (hsub hs))
  have hcont1 : Tendsto (fun a' : ℝ => Real.exp (-(l * (b - a')))) (𝓝[>] a) (𝓝 (Real.exp (-(l * (b - a))))) := by
    have hc : Continuous fun a' : ℝ => Real.exp (-(l * (b - a'))) := by fun_prop
    exact (hc.tendsto a).mono_left nhdsWithin_le_nhds
  have hcont2 : Tendsto (fun a' : ℝ => Real.exp (l * (b - a'))) (𝓝[>] a) (𝓝 (Real.exp (l * (b - a)))) := by
    have hc : Continuous fun a' : ℝ => Real.exp (l * (b - a')) := by fun_prop
    exact (hc.tendsto a).mono_left nhdsWithin_le_nhds
  have hcont3 : Tendsto (fun a' : ℝ => (clusterSpread fun i => x i a') + Dd * (b - a')) (𝓝[>] a)
      (𝓝 (0 + Dd * (b - a))) := by
    have hc : Continuous fun a' : ℝ => Dd * (b - a') := by fun_prop
    exact hlim.add ((hc.tendsto a).mono_left nhdsWithin_le_nhds)
  rw [zero_add] at hcont3
  exact ⟨le_of_tendsto (hcont1.mul hcont3) (hev.mono fun _ h => h.1),
    ge_of_tendsto (hcont2.mul hcont3) (hev.mono fun _ h => h.2)⟩

end

end GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow
