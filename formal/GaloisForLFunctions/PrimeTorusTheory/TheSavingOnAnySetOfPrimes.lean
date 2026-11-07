import GaloisForLFunctions.PrimeTorusTheory.TheSavingAgainstSize

/-!
# The saving on any set of primes

The size of a column sits at the top, on the primes near `y`. A saving carried by small primes moves nothing there. Words use every integer in a short interval, hence every small prime, so their saving may sit on a bounded set of primes. The pigeonhole only uses unique factorization, so it holds on any set of primes that is larger than the Kronecker scale.

**Theorem** (`saving_on_any_set_of_primes`). Let `1 < A' ≤ A` and `δ > 0`. For all large `T`, every set `G` of at least `(log T)^{A'}` primes up to `(log T)^A`, and every `t ∈ [T, 2T]`,

`Σ_{p ∈ G} p^{−½} (1 − cos(t log p)) ≥ T^{−2(A − A' + 1)/(A' − 1) − δ}`.

**Corollary** (`saving_at_the_top_of_the_column`). For `1 < A' < A`, deleting every prime up to `(log T)^{A'}` keeps this saving: the top of the column never reaches its size.

The exponent is `2/(A − 1)` at `A' = A`. The threshold `A' = 1` is the limit of the method: `C(|G|, k) > T` needs `|G| ≫ log T`.
-/

open Finset Filter Topology

namespace GaloisForLFunctions.PrimeTorusTheory

noncomputable section

/-- The parameters of the pigeonhole on a set of `L^{A'}` primes up to `L^A`, all eventually satisfied. -/
structure SparseConditions (A A' B δ L : ℝ) : Prop where
  log_one : 1 ≤ Real.log L
  ratio_one : 1 ≤ B * L / Real.log L
  pow_large : 4 ≤ L ^ A
  base : Real.log (4 * B) ≤ (A' - 1) * Real.log L
  pigeon : Real.log 2 + L + Real.log (4 * A * B * L) <
    B * L / Real.log L * ((A' - 1) * Real.log L - Real.log (4 * B))
  gap : L + Real.log 2 ≤ B * L / Real.log L * (A * Real.log L - Real.log 2)
  product : 1 ≤ 4 * A * B * L
  decay : Real.exp (-(δ / 2 * L)) ≤
    1 / (32 * Real.pi ^ 2 * B ^ 2) * L ^ (-(A / 2 + 2 + 2 * A))

theorem eventually_sparseConditions {A A' B δ : ℝ} (hA' : 1 < A') (hAA' : A' ≤ A) (hB : 0 < B)
    (hδ : 0 < δ) (hmain : 1 < B * (A' - 1)) :
    ∀ᶠ L : ℝ in atTop, SparseConditions A A' B δ L := by
  have hA0 : 0 < A := by linarith
  have hA1 : 0 < A' - 1 := by linarith
  have hAB : 1 < A * B := by nlinarith
  have hlog := Real.tendsto_log_atTop
  have h1 : ∀ᶠ L : ℝ in atTop, 1 ≤ Real.log L := hlog.eventually_ge_atTop 1
  have h2 := eventually_small hB 0 1 0
  have hpow := tendsto_rpow_atTop hA0
  have h3 : ∀ᶠ L : ℝ in atTop, 4 ≤ L ^ A := hpow.eventually_ge_atTop 4
  have h4 : ∀ᶠ L : ℝ in atTop, Real.log (4 * B) ≤ (A' - 1) * Real.log L :=
    (hlog.const_mul_atTop hA1).eventually_ge_atTop _
  have h5 := eventually_small (a := B * (A' - 1) - 1) (by linarith) (Real.log (4 * B) * B) 1
    (Real.log 2 + Real.log (4 * A * B))
  have h6 := eventually_small (a := A * B - 1) (by linarith) (B * Real.log 2) 0 (Real.log 2)
  have h7 : ∀ᶠ L : ℝ in atTop, 1 ≤ 4 * A * B * L :=
    (tendsto_id.const_mul_atTop (by positivity : 0 < 4 * A * B)).eventually_ge_atTop 1
  have h8 : ∀ᶠ L : ℝ in atTop, Real.exp (-(δ / 2 * L)) ≤
      1 / (32 * Real.pi ^ 2 * B ^ 2) * L ^ (-(A / 2 + 2 + 2 * A)) := by
    have hlim := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (A / 2 + 2 + 2 * A) (δ / 2)
      (by positivity)
    have hc : 0 < 1 / (32 * Real.pi ^ 2 * B ^ 2) := by positivity
    filter_upwards [hlim.eventually (gt_mem_nhds hc), eventually_gt_atTop (0 : ℝ)] with L hL hL0
    have hp : 0 < L ^ (A / 2 + 2 + 2 * A) := Real.rpow_pos_of_pos hL0 _
    rw [Real.rpow_neg hL0.le, mul_comm _ ((L ^ (A / 2 + 2 + 2 * A))⁻¹), ← div_eq_inv_mul,
      le_div_iff₀ hp, mul_comm]
    rw [neg_mul] at hL
    exact hL.le
  filter_upwards [h1, h2, h3, h4, h5, h6, h7, h8, eventually_gt_atTop (1 : ℝ)]
    with L h1 h2 h3 h4 h5 h6 h7 h8 hL1
  have hL0 : 0 < L := by linarith
  have hlogL : 0 < Real.log L := by linarith
  refine ⟨h1, ?_, h3, h4, ?_, ?_, h7, h8⟩
  · rw [le_div_iff₀ hlogL]
    simp only [zero_mul, zero_add, add_zero, one_mul] at h2
    linarith
  · have e : B * L / Real.log L * ((A' - 1) * Real.log L - Real.log (4 * B)) =
        B * (A' - 1) * L - Real.log (4 * B) * B * (L / Real.log L) := by
      field_simp
    have hl : Real.log (4 * A * B * L) = Real.log (4 * A * B) + Real.log L :=
      Real.log_mul (by positivity) hL0.ne'
    rw [e, hl]
    nlinarith
  · have e : B * L / Real.log L * (A * Real.log L - Real.log 2) =
        A * B * L - B * Real.log 2 * (L / Real.log L) := by
      field_simp
    rw [e]
    nlinarith

/-- The pigeonhole condition on a set of at least `L^{A'}` elements. -/
theorem pigeon_of_sparse {A A' B δ T L t : ℝ} {y k d : ℕ} (hA : 0 < A) (hB : 0 < B)
    (hcond : SparseConditions A A' B δ L) (hL1 : 1 < L) (hTL : T = Real.exp L)
    (ht : t ≤ 2 * T) (ht0 : 0 < t) (hy2 : 2 ≤ y) (hlogu : Real.log y ≤ A * Real.log L)
    (hkl : B * L / Real.log L ≤ (k : ℝ)) (hk2 : (k : ℝ) ≤ 2 * (B * L / Real.log L)) (hk1 : 1 ≤ k)
    (hd : L ^ A' ≤ (d : ℝ)) :
    ⌊t * k * Real.log y / Real.pi⌋₊ + 1 < d.choose k := by
  have hL0 : 0 < L := by linarith
  have hlogL : 1 ≤ Real.log L := hcond.log_one
  have hlogpos : 0 < Real.log L := by linarith
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
  have hlogy : 0 < Real.log y := Real.log_pos (by exact_mod_cast (by omega : 1 < y))
  have hLA : L ^ A' = L ^ (A' - 1) * L := by
    rw [← Real.rpow_add_one hL0.ne']
    congr 1
    ring
  have hZpos : 0 < L ^ (A' - 1) / (4 * B) := by positivity
  -- The base of the count.
  have hbase : L ^ (A' - 1) / (4 * B) ≤ (d : ℝ) / (2 * k) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hkL : 2 * (k : ℝ) ≤ 4 * (B * L) := by
      have : B * L / Real.log L ≤ B * L := div_le_self (by positivity) hlogL
      linarith
    calc
      L ^ (A' - 1) * (2 * (k : ℝ)) ≤ L ^ (A' - 1) * (4 * (B * L)) :=
        mul_le_mul_of_nonneg_left hkL (by positivity)
      _ = L ^ A' * (4 * B) := by
        rw [hLA]
        ring
      _ ≤ (d : ℝ) * (4 * B) := mul_le_mul_of_nonneg_right hd (by positivity)
  have hlogZ : Real.log (L ^ (A' - 1) / (4 * B)) = (A' - 1) * Real.log L - Real.log (4 * B) := by
    rw [Real.log_div (by positivity) (by positivity), Real.log_rpow hL0]
  have hZ1 : 1 ≤ L ^ (A' - 1) / (4 * B) := by
    rw [← Real.log_nonneg_iff hZpos, hlogZ]
    linarith [hcond.base]
  have h2kd : 2 * k ≤ d := by
    have h1 : (1 : ℝ) ≤ (d : ℝ) / (2 * k) := hZ1.trans hbase
    rw [le_div_iff₀ (by positivity)] at h1
    have : ((2 * k : ℕ) : ℝ) ≤ (d : ℝ) := by
      push_cast
      linarith
    exact_mod_cast this
  have hchoose := div_pow_le_choose hk1 h2kd
  have hpowZ : (L ^ (A' - 1) / (4 * B)) ^ k ≤ (d.choose k : ℝ) :=
    (pow_le_pow_left₀ hZpos.le hbase k).trans hchoose
  -- The lower bound of the count in exponential form.
  have hexpZ : Real.exp (B * L / Real.log L * ((A' - 1) * Real.log L - Real.log (4 * B))) ≤
      (L ^ (A' - 1) / (4 * B)) ^ k := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos hZpos, hlogZ]
    refine Real.exp_le_exp.mpr ?_
    have hnn : 0 ≤ (A' - 1) * Real.log L - Real.log (4 * B) := by linarith [hcond.base]
    rw [mul_comm ((A' - 1) * Real.log L - Real.log (4 * B))]
    exact mul_le_mul_of_nonneg_right hkl hnn
  -- The number of boxes.
  have hT1 : 1 ≤ T := by
    rw [hTL]
    exact Real.one_le_exp hL0.le
  have hboxes : (⌊t * k * Real.log y / Real.pi⌋₊ : ℝ) + 1 ≤ 2 * T * (4 * A * B * L) := by
    have hx0 : 0 ≤ t * k * Real.log y / Real.pi := by positivity
    have h1 := Nat.floor_le hx0
    have hpi := Real.pi_gt_three
    have h2 : (k : ℝ) * Real.log y ≤ 2 * (A * B * L) := by
      have e : 2 * (B * L / Real.log L) * (A * Real.log L) = 2 * (A * B * L) := by
        field_simp
      calc
        (k : ℝ) * Real.log y ≤ 2 * (B * L / Real.log L) * (A * Real.log L) :=
          mul_le_mul hk2 hlogu hlogy.le (by positivity)
        _ = 2 * (A * B * L) := e
    have h3 : t * k * Real.log y / Real.pi ≤ t * k * Real.log y :=
      div_le_self (by positivity) (by linarith)
    have h4 : t * k * Real.log y ≤ 2 * T * (2 * (A * B * L)) := by
      rw [mul_assoc t]
      exact mul_le_mul ht h2 (by positivity) (by positivity)
    have h5 := hcond.product
    have h6 : (1 : ℝ) ≤ T * (4 * A * B * L) := by nlinarith
    nlinarith
  have hexpB : 2 * T * (4 * A * B * L) = Real.exp (Real.log 2 + L + Real.log (4 * A * B * L)) := by
    rw [Real.exp_add, Real.exp_add, Real.exp_log (by norm_num), ← hTL,
      Real.exp_log (by positivity)]
  have hlt : (⌊t * k * Real.log y / Real.pi⌋₊ : ℝ) + 1 < (d.choose k : ℝ) := by
    calc
      (⌊t * k * Real.log y / Real.pi⌋₊ : ℝ) + 1 ≤ 2 * T * (4 * A * B * L) := hboxes
      _ = Real.exp (Real.log 2 + L + Real.log (4 * A * B * L)) := hexpB
      _ < Real.exp (B * L / Real.log L * ((A' - 1) * Real.log L - Real.log (4 * B))) :=
        Real.exp_lt_exp.mpr hcond.pigeon
      _ ≤ _ := hexpZ.trans hpowZ
  exact_mod_cast hlt

/-- The saving on a set of primes at fixed parameters. -/
theorem saving_on_set_at_parameters {A A' B δ T L t : ℝ} {y k : ℕ} (hA : 1 < A) (hB : 0 < B) (hcond : SparseConditions A A' B δ L) (hL1 : 1 < L) (hTL : T = Real.exp L)
    (ht : t ∈ Set.Icc T (2 * T)) (hy2 : 2 ≤ y) (hlogu : Real.log y ≤ A * Real.log L)
    (hlogl : A * Real.log L - Real.log 2 ≤ Real.log y)
    (hkl : B * L / Real.log L ≤ (k : ℝ)) (hku : (k : ℝ) ≤ B * L / Real.log L + 1) (hk1 : 1 ≤ k)
    {G : Finset ℕ} (hG : ∀ p ∈ G, p.Prime) (hGy : ∀ p ∈ G, p ≤ y) (hcard : L ^ A' ≤ (G.card : ℝ)) :
    Real.exp (-((2 * (A * B) - 2 + δ / 2) * L)) ≤
      ∑ p ∈ G, (p : ℝ) ^ (-(1 / 2 : ℝ)) * (1 - Real.cos (t * Real.log p)) := by
  have hA0 : 0 < A := by linarith
  have hL0 : 0 < L := by linarith
  have hT0 : 0 < T := by rw [hTL]; exact Real.exp_pos _
  have hlogL : 1 ≤ Real.log L := hcond.log_one
  have hlogpos : 0 < Real.log L := by linarith
  have hy1 : 1 ≤ y := by omega
  have hyr0 : (0 : ℝ) < (y : ℝ) := by exact_mod_cast hy1
  have hlogy : 0 < Real.log y := Real.log_pos (by exact_mod_cast (by omega : 1 < y))
  have hratio := hcond.ratio_one
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
  have hk2 : (k : ℝ) ≤ 2 * (B * L / Real.log L) := by linarith
  have ht0 : 0 < t := lt_of_lt_of_le hT0 ht.1
  have hpig := pigeon_of_sparse hA0 hB hcond hL1 hTL ht.2 ht0 hy2 hlogu hkl hk2 hk1 hcard
  have hykexp : (y : ℝ) ^ k = Real.exp (k * Real.log y) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos hyr0, mul_comm]
  have hyk0 : 0 < (y : ℝ) ^ k := by positivity
  have hgap : 2 * T ≤ (y : ℝ) ^ k := by
    have h1 : L + Real.log 2 ≤ k * Real.log y := by
      refine hcond.gap.trans ?_
      calc
        B * L / Real.log L * (A * Real.log L - Real.log 2) ≤ B * L / Real.log L * Real.log y :=
          mul_le_mul_of_nonneg_left hlogl (by positivity)
        _ ≤ k * Real.log y := mul_le_mul_of_nonneg_right hkl hlogy.le
    have h2 : Real.exp (L + Real.log 2) ≤ (y : ℝ) ^ k := by
      rw [hykexp]
      exact Real.exp_le_exp.mpr h1
    rw [Real.exp_add, ← hTL, Real.exp_log (show (0 : ℝ) < 2 by norm_num)] at h2
    linarith
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = Real.exp (A * B * L + A * Real.log L) := ⟨_, rfl⟩
  have hE0 : 0 < E := by rw [hE]; exact Real.exp_pos _
  have hykE : (y : ℝ) ^ k ≤ E := by
    rw [hykexp, hE]
    refine Real.exp_le_exp.mpr ?_
    have h1 : (k : ℝ) * Real.log y ≤ (B * L / Real.log L + 1) * (A * Real.log L) :=
      mul_le_mul hku hlogu hlogy.le (by positivity)
    have e : (B * L / Real.log L + 1) * (A * Real.log L) = A * B * L + A * Real.log L := by
      field_simp
    linarith
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = t / (4 * k * (y : ℝ) ^ k) := ⟨_, rfl⟩
  have hε0 : 0 ≤ ε := by rw [hε]; positivity
  have hεeq : 2 * (k : ℝ) * ε = t / (2 * (y : ℝ) ^ k) := by
    rw [hε]
    field_simp
    ring
  have hεpi : 2 * (k : ℝ) * ε < Real.pi := by
    rw [hεeq]
    have h1 : t / (2 * (y : ℝ) ^ k) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [ht.2]
    linarith [Real.pi_gt_three]
  have hεlt : 2 * (k : ℝ) * ε * (y : ℝ) ^ k < t := by
    rw [hεeq]
    have e : t / (2 * (y : ℝ) ^ k) * (y : ℝ) ^ k = t / 2 := by
      field_simp
    rw [e]
    linarith
  have hha : ∀ r ∈ G, 0 ≤ (r : ℝ) ^ (-(1 / 2 : ℝ)) := fun r _ =>
    Real.rpow_nonneg (Nat.cast_nonneg r) _
  have hw : ∀ p ∈ G, (y : ℝ) ^ (-(1 / 2 : ℝ)) ≤ (p : ℝ) ^ (-(1 / 2 : ℝ)) := by
    intro p hp
    refine Real.rpow_le_rpow_of_nonpos ?_ ?_ (by norm_num)
    · exact_mod_cast (hG p hp).pos
    · exact_mod_cast hGy p hp
  have hD := defect_ge_of_pigeonhole (Q := G) (a := fun p : ℕ => (p : ℝ) ^ (-(1 / 2 : ℝ)))
    hha (y := y) (k := k) (t := t) (ε := ε) (w := (y : ℝ) ^ (-(1 / 2 : ℝ))) ht0 hy1 hε0
    hG hGy hw hεpi hεlt hpig
  rw [primeSystem_defect] at hD
  refine le_trans ?_ hD
  have hwlow : Real.exp (-(A / 2 * Real.log L)) ≤ (y : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [Real.rpow_def_of_pos hyr0]
    refine Real.exp_le_exp.mpr ?_
    nlinarith
  have hεlow : T / (8 * B * L * E) ≤ ε := by
    rw [hε]
    have hkL : (k : ℝ) ≤ 2 * (B * L) := by
      refine hk2.trans ?_
      have : B * L / Real.log L ≤ B * L := div_le_self (by positivity) hlogL
      linarith
    have hden : 4 * (k : ℝ) * (y : ℝ) ^ k ≤ 8 * B * L * E := by
      have := mul_le_mul hkL hykE hyk0.le (by positivity)
      nlinarith
    calc
      T / (8 * B * L * E) ≤ t / (8 * B * L * E) :=
        div_le_div_of_nonneg_right ht.1 (by positivity)
      _ ≤ t / (4 * k * (y : ℝ) ^ k) :=
        div_le_div_of_nonneg_left ht0.le (by positivity) hden
  rw [hE] at hεlow
  exact final_lower_bound hA hB hcond.decay hL0 hTL hwlow hεlow

/-- **The saving on any set of primes.** See the module docstring. -/
theorem saving_on_any_set_of_primes {A A' δ : ℝ} (hA' : 1 < A') (hAA' : A' ≤ A) (hδ : 0 < δ) :
    ∃ T₀ : ℝ, ∀ T, T₀ ≤ T → ∀ G : Finset ℕ, (∀ p ∈ G, p.Prime) →
      (∀ p ∈ G, (p : ℝ) ≤ Real.log T ^ A) → Real.log T ^ A' ≤ (G.card : ℝ) →
      ∀ t ∈ Set.Icc T (2 * T),
        T ^ (-(2 * (A - A' + 1) / (A' - 1) + δ)) ≤
          ∑ p ∈ G, (p : ℝ) ^ (-(1 / 2 : ℝ)) * (1 - Real.cos (t * Real.log p)) := by
  have hA : 1 < A := by linarith
  have hA0 : 0 < A := by linarith
  have hA1 : 0 < A' - 1 := by linarith
  obtain ⟨δ₁, hδ₁⟩ : ∃ δ₁ : ℝ, δ₁ = δ * (A' - 1) / (4 * A) := ⟨_, rfl⟩
  have hδ₁0 : 0 < δ₁ := by rw [hδ₁]; positivity
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = (1 + δ₁) / (A' - 1) := ⟨_, rfl⟩
  have hB0 : 0 < B := by rw [hB]; positivity
  have hBA : B * (A' - 1) = 1 + δ₁ := by
    rw [hB]
    field_simp
  have hexp2 : 2 * (A * B) - 2 + δ / 2 = 2 * (A - A' + 1) / (A' - 1) + δ := by
    rw [hB, hδ₁]
    field_simp
    ring
  have hev := Real.tendsto_log_atTop.eventually
    (eventually_sparseConditions (A := A) (A' := A') (B := B) (δ := δ) hA' hAA' hB0 hδ
      (by rw [hBA]; linarith))
  obtain ⟨T₁, hT₁⟩ := eventually_atTop.mp (hev.and (eventually_gt_atTop (1 : ℝ)))
  refine ⟨T₁, fun T hT G hG hGy hcard t ht => ?_⟩
  obtain ⟨hcond, hT1⟩ := hT₁ T hT
  have hT0 : 0 < T := by linarith
  have hL0 : 0 < Real.log T := Real.log_pos hT1
  have hL1 : 1 < Real.log T := by
    have h1 := (Real.le_log_iff_exp_le hL0).mp hcond.log_one
    have h2 := Real.exp_one_gt_d9
    linarith
  obtain ⟨-, -, hy2, hlogu, hlogl⟩ := floor_bounds hL1 hA0 hcond.pow_large
  have hlogpos : 0 < Real.log (Real.log T) := by linarith [hcond.log_one]
  have hkl := Nat.le_ceil (B * Real.log T / Real.log (Real.log T))
  have hku : ((⌈B * Real.log T / Real.log (Real.log T)⌉₊ : ℕ) : ℝ) ≤
      B * Real.log T / Real.log (Real.log T) + 1 :=
    (Nat.ceil_lt_add_one (by positivity)).le
  have hk1 : 1 ≤ ⌈B * Real.log T / Real.log (Real.log T)⌉₊ := by
    have : (1 : ℝ) ≤ ((⌈B * Real.log T / Real.log (Real.log T)⌉₊ : ℕ) : ℝ) :=
      hcond.ratio_one.trans hkl
    exact_mod_cast this
  have hGy' : ∀ p ∈ G, p ≤ ⌊Real.log T ^ A⌋₊ := fun p hp => Nat.le_floor (hGy p hp)
  have h := saving_on_set_at_parameters hA hB0 hcond hL1 (Real.exp_log hT0).symm ht hy2 hlogu
    hlogl hkl hku hk1 hG hGy' hcard
  rw [hexp2] at h
  refine le_trans (le_of_eq ?_) h
  rw [Real.rpow_def_of_pos hT0]
  congr 1
  ring

/-- The primes in `(x, y]`. -/
def topPrimes (x : ℝ) (y : ℕ) : Finset ℕ := (primesUpTo y).filter fun p => x < (p : ℝ)

theorem card_topPrimes_ge {x : ℝ} {y : ℕ} (hx : 0 ≤ x) :
    ((primesUpTo y).card : ℝ) - x ≤ ((topPrimes x y).card : ℝ) := by
  classical
  have hsplit := Finset.card_filter_add_card_filter_not (s := primesUpTo y) (fun p : ℕ => x < (p : ℝ))
  have hlow : (((primesUpTo y).filter fun p : ℕ => ¬ x < (p : ℝ)).card : ℝ) ≤ x := by
    have hsub : ((primesUpTo y).filter fun p : ℕ => ¬ x < (p : ℝ)) ⊆ (Finset.range (⌊x⌋₊ + 1)).erase 0 := by
      intro p hp
      rw [Finset.mem_filter, not_lt] at hp
      have hp0 := (prime_of_mem_primesUpTo hp.1).pos
      refine Finset.mem_erase.mpr ⟨hp0.ne', Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.le_floor hp.2))⟩
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem (Finset.mem_range.mpr (Nat.succ_pos _)), Finset.card_range,
      Nat.succ_sub_one] at hcard
    exact (Nat.cast_le.mpr hcard).trans (Nat.floor_le hx)
  have hcast : ((topPrimes x y).card : ℝ) + (((primesUpTo y).filter fun p : ℕ => ¬ x < (p : ℝ)).card : ℝ) =
      ((primesUpTo y).card : ℝ) := by
    unfold topPrimes
    exact_mod_cast hsplit
  linarith

/-- **The top of the column.** Deleting every prime up to `(log T)^{A'}` keeps a saving against size. -/
theorem saving_at_the_top_of_the_column {A A' δ : ℝ} (hA' : 1 < A') (hAA' : A' < A) (hδ : 0 < δ) :
    ∃ T₀ : ℝ, ∀ T, T₀ ≤ T → ∀ t ∈ Set.Icc T (2 * T),
      T ^ (-(2 * (A - A' + 1) / (A' - 1) + δ)) ≤
        ∑ p ∈ topPrimes (Real.log T ^ A') ⌊Real.log T ^ A⌋₊,
          (p : ℝ) ^ (-(1 / 2 : ℝ)) * (1 - Real.cos (t * Real.log p)) := by
  have hA0 : 0 < A := by linarith
  have hgap : 0 < A - A' := by linarith
  obtain ⟨T₁, h⟩ := saving_on_any_set_of_primes hA' hAA'.le hδ
  obtain ⟨x₀, -, hx₀⟩ := exists_chebyshev_threshold
  -- `L^{A−A'}` beats `8A log L`.
  have hbeat : ∀ᶠ L : ℝ in atTop, 8 * A * Real.log L ≤ L ^ (A - A') := by
    have h1 := (isLittleO_log_rpow_atTop hgap).bound (show (0 : ℝ) < 1 / (8 * A) by positivity)
    filter_upwards [h1, Real.tendsto_log_atTop.eventually_ge_atTop 0, eventually_gt_atTop (0 : ℝ)]
      with L h1 h2 h3
    rw [Real.norm_of_nonneg h2, Real.norm_of_nonneg (Real.rpow_nonneg h3.le _)] at h1
    have : 8 * A * Real.log L ≤ 8 * A * (1 / (8 * A) * L ^ (A - A')) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have e : 8 * A * (1 / (8 * A) * L ^ (A - A')) = L ^ (A - A') := by
      field_simp
    linarith
  have hpow := tendsto_rpow_atTop hA0
  have hev : ∀ᶠ L : ℝ in atTop, 8 * A * Real.log L ≤ L ^ (A - A') ∧ 4 ≤ L ^ A ∧ x₀ ≤ L ^ A / 2 ∧
      1 < L ∧ 0 < Real.log L := by
    filter_upwards [hbeat, hpow.eventually_ge_atTop 4, hpow.eventually_ge_atTop (2 * x₀),
      eventually_gt_atTop (1 : ℝ)] with L h1 h2 h3 h4
    exact ⟨h1, h2, by linarith, h4, Real.log_pos h4⟩
  obtain ⟨T₂, hT₂⟩ := eventually_atTop.mp (Real.tendsto_log_atTop.eventually hev)
  refine ⟨max T₁ (max T₂ 1), fun T hT t ht => ?_⟩
  have hTT₁ : T₁ ≤ T := (le_max_left _ _).trans hT
  have hTT₂ : T₂ ≤ T := ((le_max_left _ _).trans (le_max_right _ _)).trans hT
  obtain ⟨hb, h4, hcheb, hL1, hlogpos⟩ := hT₂ T hTT₂
  have hL0 : 0 < Real.log T := by linarith
  obtain ⟨hyu, hyl, hy2, hlogu, -⟩ := floor_bounds hL1 hA0 h4
  obtain ⟨y, hy⟩ : ∃ y, y = ⌊Real.log T ^ A⌋₊ := ⟨_, rfl⟩
  rw [← hy] at hyu hyl hy2 hlogu ⊢
  have hcardπ := card_primesUpTo_ge hy2 (hx₀ y (hcheb.trans hyl))
  have hlogy : 0 < Real.log y := Real.log_pos (by exact_mod_cast (by omega : 1 < y))
  have hLA : Real.log T ^ A = Real.log T ^ (A - A') * Real.log T ^ A' := by
    rw [← Real.rpow_add hL0]
    congr 1
    ring
  have hp0 : 0 < Real.log T ^ A' := Real.rpow_pos_of_pos hL0 _
  -- There are at least `2L^{A'}` primes up to `y`.
  have hπ : 2 * Real.log T ^ A' ≤ ((primesUpTo y).card : ℝ) := by
    refine le_trans ?_ hcardπ
    rw [le_div_iff₀ (by positivity)]
    have h1 : Real.log (y : ℝ) * (Real.log T ^ A' * 4) ≤ A * Real.log (Real.log T) * (Real.log T ^ A' * 4) :=
      mul_le_mul_of_nonneg_right hlogu (by positivity)
    have h2 : 8 * A * Real.log (Real.log T) * Real.log T ^ A' ≤ Real.log T ^ (A - A') * Real.log T ^ A' :=
      mul_le_mul_of_nonneg_right hb hp0.le
    rw [← hLA] at h2
    nlinarith
  have htop : Real.log T ^ A' ≤ ((topPrimes (Real.log T ^ A') y).card : ℝ) := by
    have := card_topPrimes_ge (x := Real.log T ^ A') (y := y) hp0.le
    linarith
  refine h T hTT₁ (topPrimes (Real.log T ^ A') y) ?_ ?_ htop t ht
  · intro p hp
    exact prime_of_mem_primesUpTo (Finset.mem_filter.mp hp).1
  · intro p hp
    have hle : (p : ℝ) ≤ (y : ℝ) := by
      exact_mod_cast le_of_mem_primesUpTo (Finset.mem_filter.mp hp).1
    exact hle.trans hyu

end

end GaloisForLFunctions.PrimeTorusTheory
