import GaloisForLFunctions.RHTower.SelbergExponentialNearLineDensity
import GaloisForLFunctions.RHTower.ZetaLineLogMeanLittlewoodBudget
import GaloisForLFunctions.RHTower.SpeiserEventualEquivalence

/-!
# Exponential density of the Speiser shadow set at the critical scale

For `κ > 0` and `L = log U`, the `κ`-shadow set collects the heights `t` lying in the shadow
`[Im ρ − |Re ρ − 1/2|, Im ρ + |Re ρ − 1/2|]` of a zero `ρ` of `ξ` with `|Re ρ − 1/2| ≥ κ/L`.
Every local RH sign fails at horizontal distance `≥ κ/L` from the critical line only at such
heights (the Speiser-disk laws of `SpeiserLocalDisk` and `XiLogDerivReLocality`).

**Theorem** (`exists_speiserShadow_exponential_density`). There are `A', K' ≥ 0` such that for all
large `U` there are admissible heights `T₁ ∈ (U/4, U/4 + 1)`, `T₂ ∈ (U/2 − 1, U/2)` with, for every
`2 ≤ κ ≤ L/2 − 2`,
`|κ-shadow ∩ [T₁ + 1/2, T₂ − 1/2]| ≤ A'(T₂ − T₁)e^{−κ/2400} + K'L²`.

**Proof.**
- The measure is at most twice the tail moment `Σ_{β − 1/2 ≥ κ/L} m_ρ (β − 1/2)`.
- A layer decomposition in steps `2/L` (`sum_mul_sub_half_le_of_layer_bound`) bounds the tail
  moment by the exponential near-line zero density `2π(a/L) N(1/2 + 2a/L) ≤ ΔT·A e^{−a/1200} + KL`
  (`exists_selberg_exponential_nearLine_zeroDensity`).
-/

open Complex Set MeasureTheory Filter

namespace RHTower

noncomputable section

/-- `Σ_{k<M} e^{−k/1200} ≤ 1201`. -/
theorem sum_exp_neg_div_le (M : ℕ) :
    ∑ k ∈ Finset.range M, Real.exp (-((k : ℝ) / 1200)) ≤ 1201 := by
  set q : ℝ := Real.exp (-(1 / 1200)) with hq
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := by rw [hq]; exact Real.exp_lt_one_iff.mpr (by norm_num)
  have hterm : ∀ k : ℕ, Real.exp (-((k : ℝ) / 1200)) = q ^ k := by
    intro k
    rw [hq, ← Real.exp_nat_mul]; congr 1; ring
  simp only [hterm]
  have hgeo : ∑ k ∈ Finset.range M, q ^ k ≤ 1 / (1 - q) := by
    rw [geom_sum_eq hq1.ne, div_eq_mul_inv, one_div]
    have h1 : 0 < 1 - q := by linarith
    rw [show (q ^ M - 1) * (q - 1)⁻¹ = (1 - q ^ M) * (1 - q)⁻¹ by
      rw [show q - 1 = -(1 - q) by ring, inv_neg]; ring]
    apply mul_le_of_le_one_left (inv_pos.mpr h1).le
    have := pow_nonneg hq0 M
    linarith
  have hbound : 1 / (1 - q) ≤ 1201 := by
    have hexp : 1 + 1 / 1200 ≤ Real.exp (1 / 1200) := by
      have := Real.add_one_le_exp (1 / 1200 : ℝ); linarith
    have hq' : q * Real.exp (1 / 1200) = 1 := by
      rw [hq, ← Real.exp_add]; simp
    have hqle : q ≤ 1200 / 1201 := by
      have hpos : 0 < Real.exp (1 / 1200) := Real.exp_pos _
      have : q = 1 / Real.exp (1 / 1200) := by field_simp; linarith [hq']
      rw [this, div_le_div_iff₀ hpos (by norm_num)]
      linarith
    rw [div_le_iff₀ (by linarith)]
    linarith
  linarith

/-- **Tail moment from the layer bound.** If for every `1 ≤ a` with `2a + 2 ≤ L` the weighted
number of points of `Z` with `Re ≥ 1/2 + 2a/L` satisfies `2π(a/L)N ≤ D e^{−a/1200} + E`, then for
`2 ≤ κ ≤ L/2 − 2`,
`Σ_{Re w ≥ 1/2 + κ/L} m_w (Re w − 1/2) ≤ (2/π)(1201 D e^{−κ/2400} + (L/4 + 1) E)`. -/
theorem sum_mul_sub_half_le_of_layer_bound {Z : Finset ℂ} {m : ℂ → ℝ} (hm : ∀ w, 0 ≤ m w)
    {L κ D E : ℝ} (hL : 4 ≤ L) (hκ : 2 ≤ κ) (hκL : κ ≤ L / 2 - 2)
    (hre : ∀ w ∈ Z, w.re < 1) (hD : 0 ≤ D) (hE : 0 ≤ E)
    (hlayer : ∀ a : ℝ, 1 ≤ a → 2 * a + 2 ≤ L →
      2 * Real.pi * ((a / L) * ∑ w ∈ Z.filter (fun w => 1 / 2 + 2 * a / L ≤ w.re), m w) ≤
        D * Real.exp (-(a / 1200)) + E) :
    ∑ w ∈ Z.filter (fun w => 1 / 2 + κ / L ≤ w.re), m w * (w.re - 1 / 2) ≤
      2 / Real.pi * (1201 * D * Real.exp (-(κ / 2400)) + (L / 4 + 1) * E) := by
  classical
  have hL0 : 0 < L := by linarith
  have hπ : 0 < Real.pi := Real.pi_pos
  set M : ℕ := ⌊L / 4⌋₊ + 1 with hM
  set F := Z.filter (fun w => 1 / 2 + κ / L ≤ w.re) with hF
  -- the layer index of a point
  set kf : ℂ → ℕ := fun w => ⌊(L * (w.re - 1 / 2) - κ) / 2⌋₊ with hkf
  have hkmem : ∀ w ∈ F, kf w ∈ Finset.range M := by
    intro w hw
    obtain ⟨hwZ, hwre⟩ := Finset.mem_filter.mp hw
    have h1 := hre w hwZ
    rw [Finset.mem_range, hM, Nat.lt_succ_iff]
    apply Nat.floor_le_floor
    have : L * (w.re - 1 / 2) ≤ L / 2 := by nlinarith
    linarith
  have hlow : ∀ w ∈ F, 1 / 2 + 2 * (κ / 2 + kf w) / L ≤ w.re := by
    intro w hw
    have hwre : 1 / 2 + κ / L ≤ w.re := (Finset.mem_filter.mp hw).2
    have hκx : κ ≤ (w.re - 1 / 2) * L := (div_le_iff₀ hL0).mp (by linarith)
    have hnn : 0 ≤ (L * (w.re - 1 / 2) - κ) / 2 := by nlinarith
    have hfl : ((kf w : ℕ) : ℝ) ≤ (L * (w.re - 1 / 2) - κ) / 2 := Nat.floor_le hnn
    have h2 : 2 * (κ / 2 + (kf w : ℝ)) / L ≤ w.re - 1 / 2 := by
      rw [div_le_iff₀ hL0]; nlinarith
    linarith
  have hup : ∀ w ∈ F, w.re - 1 / 2 ≤ (2 * (κ / 2 + kf w) + 2) / L := by
    intro w _
    have hfl : (L * (w.re - 1 / 2) - κ) / 2 < ((kf w : ℕ) : ℝ) + 1 :=
      Nat.lt_floor_add_one _
    rw [le_div_iff₀ hL0]
    nlinarith
  -- regroup by layers
  have hstep1 : ∑ w ∈ F, m w * (w.re - 1 / 2) ≤
      ∑ w ∈ F, m w * ((2 * (κ / 2 + kf w) + 2) / L) :=
    Finset.sum_le_sum fun w hw => mul_le_mul_of_nonneg_left (hup w hw) (hm w)
  have hstep2 : ∑ w ∈ F, m w * ((2 * (κ / 2 + kf w) + 2) / L) =
      ∑ k ∈ Finset.range M, ∑ w ∈ F.filter (fun w => kf w = k),
        m w * ((2 * (κ / 2 + k) + 2) / L) := by
    rw [← Finset.sum_fiberwise_of_maps_to hkmem]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun w hw => ?_
    rw [(Finset.mem_filter.mp hw).2]
  have hstep3 : ∀ k ∈ Finset.range M, ∑ w ∈ F.filter (fun w => kf w = k),
      m w * ((2 * (κ / 2 + k) + 2) / L) ≤
        2 / Real.pi * (D * Real.exp (-((κ / 2 + k) / 1200)) + E) := by
    intro k hk
    set a : ℝ := κ / 2 + k with ha
    have ha1 : 1 ≤ a := by rw [ha]; have := Nat.cast_nonneg (α := ℝ) k; linarith
    have ha2 : 2 * a + 2 ≤ L := by
      have hkM : (k : ℝ) ≤ L / 4 := by
        have := Finset.mem_range.mp hk
        rw [hM, Nat.lt_succ_iff] at this
        exact (Nat.cast_le.mpr this).trans (Nat.floor_le (by linarith))
      rw [ha]; linarith
    have hsub : F.filter (fun w => kf w = k) ⊆ Z.filter (fun w => 1 / 2 + 2 * a / L ≤ w.re) := by
      intro w hw
      obtain ⟨hwF, hwk⟩ := Finset.mem_filter.mp hw
      refine Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hwF).1, ?_⟩
      have := hlow w hwF
      rw [hwk] at this
      exact this
    have hN := hlayer a ha1 ha2
    set N := ∑ w ∈ Z.filter (fun w => 1 / 2 + 2 * a / L ≤ w.re), m w with hNdef
    have hsubsum : ∑ w ∈ F.filter (fun w => kf w = k), m w ≤ N :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub fun w _ _ => hm w
    have hN' : N ≤ L / (2 * Real.pi * a) * (D * Real.exp (-(a / 1200)) + E) := by
      have ha0 : 0 < a := by linarith
      have e : N = 2 * Real.pi * (a / L * N) * (L / (2 * Real.pi * a)) := by
        field_simp
      rw [e, mul_comm (L / (2 * Real.pi * a))]
      exact mul_le_mul_of_nonneg_right hN (by positivity)
    rw [← Finset.sum_mul]
    have hfac : 0 ≤ (2 * a + 2) / L := by positivity
    calc (∑ w ∈ F.filter (fun w => kf w = k), m w) * ((2 * a + 2) / L)
        ≤ (L / (2 * Real.pi * a) * (D * Real.exp (-(a / 1200)) + E)) * ((2 * a + 2) / L) :=
          mul_le_mul_of_nonneg_right (hsubsum.trans hN') hfac
      _ = (a + 1) / (Real.pi * a) * (D * Real.exp (-(a / 1200)) + E) := by
          field_simp
      _ ≤ 2 / Real.pi * (D * Real.exp (-(a / 1200)) + E) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          rw [div_le_div_iff₀ (by positivity) hπ]
          nlinarith
  have hstep4 : ∑ k ∈ Finset.range M, 2 / Real.pi * (D * Real.exp (-((κ / 2 + k) / 1200)) + E) ≤
      2 / Real.pi * (1201 * D * Real.exp (-(κ / 2400)) + (L / 4 + 1) * E) := by
    rw [← Finset.mul_sum]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hsplit : ∀ k : ℕ, D * Real.exp (-((κ / 2 + k) / 1200)) =
        D * Real.exp (-(κ / 2400)) * Real.exp (-((k : ℝ) / 1200)) := by
      intro k; rw [mul_assoc, ← Real.exp_add]; congr 2; ring
    simp only [hsplit]
    rw [← Finset.mul_sum]
    have hgeo := sum_exp_neg_div_le M
    have hMle : (M : ℝ) ≤ L / 4 + 1 := by
      rw [hM]; push_cast; linarith [Nat.floor_le (show 0 ≤ L / 4 by linarith)]
    have hDe : 0 ≤ D * Real.exp (-(κ / 2400)) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hgeo hDe, mul_le_mul_of_nonneg_right hMle hE]
  calc ∑ w ∈ F, m w * (w.re - 1 / 2)
      ≤ ∑ w ∈ F, m w * ((2 * (κ / 2 + kf w) + 2) / L) := hstep1
    _ = _ := hstep2
    _ ≤ ∑ k ∈ Finset.range M, 2 / Real.pi * (D * Real.exp (-((κ / 2 + k) / 1200)) + E) :=
        Finset.sum_le_sum hstep3
    _ ≤ _ := hstep4

/-- **The shadow set against the tail moment.** Heights in `[T₁ + 1/2, T₂ − 1/2]` shadowed by a
zero with `|Re ρ − 1/2| ≥ κ/L` have measure at most twice the tail moment of the zeros between
`T₁` and `T₂`. -/
theorem volume_speiserShadow_le {T₁ T₂ κ L : ℝ} (hL : 0 < L) (hκ : 0 < κ) {Z : Finset ℂ}
    (hZ : ∀ z : ℂ, z ∈ Z ↔ z ∈ (uIcc (1 / 2 : ℝ) (15 / 2) ×ℂ uIcc T₁ T₂) ∧ riemannZeta z = 0)
    (hT : T₁ < T₂) :
    volume {t : ℝ | t ∈ Icc (T₁ + 1 / 2) (T₂ - 1 / 2) ∧ ∃ ρ : ℂ, xi ρ = 0 ∧
        κ / L ≤ |ρ.re - 1 / 2| ∧ |t - ρ.im| ≤ |ρ.re - 1 / 2|} ≤
      ENNReal.ofReal (2 * ∑ w ∈ Z.filter (fun w => 1 / 2 + κ / L ≤ w.re),
        ((analyticOrderAt riemannZeta w).toNat : ℝ) * (w.re - 1 / 2)) := by
  classical
  set F := Z.filter (fun w => 1 / 2 + κ / L ≤ w.re) with hF
  have hsub : {t : ℝ | t ∈ Icc (T₁ + 1 / 2) (T₂ - 1 / 2) ∧ ∃ ρ : ℂ, xi ρ = 0 ∧
      κ / L ≤ |ρ.re - 1 / 2| ∧ |t - ρ.im| ≤ |ρ.re - 1 / 2|} ⊆
      ⋃ w ∈ F, Icc (w.im - (w.re - 1 / 2)) (w.im + (w.re - 1 / 2)) := by
    rintro t ⟨ht, ρ, hρ, hr, hdist⟩
    have hκL : 0 < κ / L := div_pos hκ hL
    have hlt1 : ρ.re < 1 := by
      by_contra h; push Not at h; exact xi_ne_zero_of_one_le_re h hρ
    have hgt0 : 0 < ρ.re := by
      by_contra h
      push Not at h
      apply xi_ne_zero_of_one_le_re (ρ := 1 - ρ) (by simp; linarith)
      rw [xi_one_sub]; exact hρ
    -- the right member of the pair
    obtain ⟨w, hw, hwre, hwim⟩ : ∃ w : ℂ, xi w = 0 ∧ w.re = 1 / 2 + |ρ.re - 1 / 2| ∧
        w.im = ρ.im := by
      rcases le_or_gt (1 / 2) ρ.re with h | h
      · exact ⟨ρ, hρ, by rw [abs_of_nonneg (by linarith)]; ring, rfl⟩
      · refine ⟨1 - (starRingEnd ℂ) ρ, by rw [xi_one_sub, xi_conj, hρ, map_zero], ?_, by simp⟩
        rw [abs_of_neg (by linarith)]; simp; ring
    have hrhalf : |ρ.re - 1 / 2| < 1 / 2 := by rw [abs_lt]; constructor <;> linarith
    have hw1 : w ≠ 1 := fun h => by rw [h, Complex.one_re] at hwre; linarith
    have hζw : riemannZeta w = 0 :=
      (xi_eq_zero_iff (by rw [hwre]; positivity) hw1).mp hw
    have htw : |t - w.im| ≤ w.re - 1 / 2 := by rw [hwim, hwre]; linarith
    have hwmem : w ∈ F := by
      refine Finset.mem_filter.mpr ⟨(hZ w).mpr ⟨?_, hζw⟩, by rw [hwre]; linarith⟩
      rw [Complex.mem_reProdIm, uIcc_of_le (by norm_num), uIcc_of_le hT.le]
      have := abs_le.mp htw
      refine ⟨⟨by rw [hwre]; linarith [abs_nonneg (ρ.re - 1 / 2)], by rw [hwre]; linarith⟩,
        ⟨by linarith [ht.1], by linarith [ht.2]⟩⟩
    refine Set.mem_iUnion₂.mpr ⟨w, hwmem, ?_⟩
    have := abs_le.mp htw
    exact ⟨by linarith, by linarith⟩
  refine (measure_mono hsub).trans ((measure_biUnion_finset_le _ _).trans ?_)
  have hterm : ∀ w ∈ F, volume (Icc (w.im - (w.re - 1 / 2)) (w.im + (w.re - 1 / 2))) ≤
      ENNReal.ofReal (2 * (((analyticOrderAt riemannZeta w).toNat : ℝ) * (w.re - 1 / 2))) := by
    intro w hw
    obtain ⟨hwZ, hwre⟩ := Finset.mem_filter.mp hw
    obtain ⟨-, hζw⟩ := (hZ w).mp hwZ
    have hr0 : 0 ≤ w.re - 1 / 2 := by have := div_pos hκ hL; linarith
    have hw1 : w ≠ 1 := fun h => by
      have := (hZ w).mp hwZ
      rw [h] at hζw; exact riemannZeta_one_ne_zero hζw
    have hm := one_le_toNat_analyticOrderAt_riemannZeta hw1 hζw
    rw [Real.volume_Icc]
    apply ENNReal.ofReal_le_ofReal
    have : (1 : ℝ) ≤ ((analyticOrderAt riemannZeta w).toNat : ℝ) := by exact_mod_cast hm
    nlinarith
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← ENNReal.ofReal_sum_of_nonneg (fun w hw => by
    have hwre := (Finset.mem_filter.mp hw).2
    have hr0 : 0 ≤ w.re - 1 / 2 := by have := div_pos hκ hL; linarith
    positivity), Finset.mul_sum]

/-- **Signs at distance `≥ κ/L` off the `κ`-shadow set.** If no zero `ρ` with
`|Re ρ − 1/2| ≥ κ/L` shadows the height `t ≥ 100`, then the Hadamard sign holds at every
`Re s ≥ 1/2 + κ/L` and `ζ' ≠ 0` at every `0 < Re s ≤ 1/2 − κ/L` on the line `Im s = t`. -/
theorem signs_of_not_mem_kappaShadow {t κ L : ℝ} (hL : 0 < L) (hκ : 0 < κ) (ht : 100 ≤ t)
    (hno : ¬ ∃ ρ : ℂ, xi ρ = 0 ∧ κ / L ≤ |ρ.re - 1 / 2| ∧ |t - ρ.im| ≤ |ρ.re - 1 / 2|) :
    (∀ σ : ℝ, 1 / 2 + κ / L ≤ σ → xi ((σ : ℂ) + t * I) ≠ 0 ∧
      0 ≤ (logDeriv xi ((σ : ℂ) + t * I)).re) ∧
    (∀ σ : ℝ, 0 < σ → σ ≤ 1 / 2 - κ / L → deriv riemannZeta ((σ : ℂ) + t * I) ≠ 0) := by
  have hκL : 0 < κ / L := div_pos hκ hL
  have key : ∀ (σ : ℝ) (ρ : ℂ), xi ρ = 0 → κ / L ≤ |σ - 1 / 2| →
      (σ - 1 / 2) ^ 2 + (t - ρ.im) ^ 2 ≤ (ρ.re - 1 / 2) ^ 2 → False := by
    intro σ ρ hρ hσ hdisk
    apply hno
    have h1 : |σ - 1 / 2| ≤ |ρ.re - 1 / 2| := by
      rw [← sq_le_sq]; nlinarith [sq_nonneg (t - ρ.im)]
    have h2 : |t - ρ.im| ≤ |ρ.re - 1 / 2| := by
      rw [← sq_le_sq]; nlinarith [sq_nonneg (σ - 1 / 2), sq_abs (t - ρ.im), sq_abs (ρ.re - 1 / 2)]
    exact ⟨ρ, hρ, hσ.trans h1, h2⟩
  refine ⟨fun σ hσ => ?_, fun σ h0 hσ hd => ?_⟩
  · have hre : ((σ : ℂ) + t * I).re = σ := by simp
    have him : ((σ : ℂ) + t * I).im = t := by simp
    have habs : κ / L ≤ |σ - 1 / 2| := by rw [abs_of_nonneg (by linarith)]; linarith
    have hxi : xi ((σ : ℂ) + t * I) ≠ 0 := fun h0 =>
      key σ _ h0 habs (by rw [hre, him]; simp)
    refine ⟨hxi, re_logDeriv_xi_nonneg_of_disk_bound (by rw [hre]; linarith) hxi fun q => ?_⟩
    by_contra hge
    push Not at hge
    rw [hre, him] at hge
    exact key σ _ (xi_eq_zero_of_mem_divisor_support q.1) habs hge
  · have hre : ((σ : ℂ) + t * I).re = σ := by simp
    have him : ((σ : ℂ) + t * I).im = t := by simp
    obtain ⟨ρ, hρ, -, -, hdisk⟩ := exists_xi_zero_disk_of_deriv_riemannZeta_eq_zero
      (s := (σ : ℂ) + t * I) (by rw [hre]; exact h0) (by rw [hre]; linarith)
      (by rw [him]; exact ht) hd
    rw [hre, him] at hdisk
    exact key σ ρ hρ (by rw [abs_of_neg (by linarith)]; linarith) hdisk

/-- **Exponential density of the Speiser shadow set.** There are `A', K' ≥ 0` such that for all
large `U`, with `L = log U`, admissible heights `T₁ ∈ (U/4, U/4 + 1)`, `T₂ ∈ (U/2 − 1, U/2)`
exist with, for every `2 ≤ κ ≤ L/2 − 2`, the heights of `[T₁ + 1/2, T₂ − 1/2]` shadowed by a zero
with `|Re ρ − 1/2| ≥ κ/L` of measure at most `A'(T₂ − T₁)e^{−κ/2400} + K'L²`. -/
theorem exists_speiserShadow_exponential_density :
    ∃ A' K' : ℝ, 0 ≤ A' ∧ 0 ≤ K' ∧ ∀ᶠ U in atTop,
      ∃ T₁ ∈ Ioo (U / 4) (U / 4 + 1), ∃ T₂ ∈ Ioo (U / 2 - 1) (U / 2),
        ∀ κ : ℝ, 2 ≤ κ → κ ≤ Real.log U / 2 - 2 →
          volume {t : ℝ | t ∈ Icc (T₁ + 1 / 2) (T₂ - 1 / 2) ∧ ∃ ρ : ℂ, xi ρ = 0 ∧
              κ / Real.log U ≤ |ρ.re - 1 / 2| ∧ |t - ρ.im| ≤ |ρ.re - 1 / 2|} ≤
            ENNReal.ofReal (A' * (T₂ - T₁) * Real.exp (-(κ / 2400)) +
              K' * Real.log U ^ 2) := by
  obtain ⟨A, K, hA, hK, hev⟩ := exists_selberg_exponential_nearLine_zeroDensity
  refine ⟨4 / Real.pi * 1201 * A, 2 / Real.pi * K, by positivity, by positivity, ?_⟩
  have hLev := Real.tendsto_log_atTop.eventually_ge_atTop (4 : ℝ)
  filter_upwards [hev, hLev, eventually_ge_atTop (200 : ℝ)] with U hU hL4 hU200
  obtain ⟨T₁, hT₁, T₂, hT₂, hbound⟩ := hU
  refine ⟨T₁, hT₁, T₂, hT₂, fun κ hκ hκL => ?_⟩
  set L := Real.log U with hLdef
  have hL0 : 0 < L := by linarith
  have hT : T₁ < T₂ := by linarith [hT₁.2, hT₂.1]
  obtain ⟨Z, hZ⟩ := exists_zetaRectangleZeros_finset (T₁ := T₁) (T₂ := T₂)
    (by linarith [hT₁.1]) hT
  have hre : ∀ w ∈ Z, w.re < 1 := by
    intro w hw
    obtain ⟨-, hζ⟩ := (hZ w).mp hw
    by_contra h
    push Not at h
    exact riemannZeta_ne_zero_of_one_le_re h hζ
  have hD : 0 ≤ (T₂ - T₁) * A := by nlinarith
  have htail := sum_mul_sub_half_le_of_layer_bound (Z := Z)
    (m := fun w => ((analyticOrderAt riemannZeta w).toNat : ℝ)) (fun w => Nat.cast_nonneg _)
    (L := L) (κ := κ) (D := (T₂ - T₁) * A) (E := K * L) hL4 hκ hκL hre hD (by positivity)
    (fun a ha1 ha2 => by
      have := hbound a ha1 ha2 Z hZ
      calc 2 * Real.pi * (a / L * ∑ w ∈ Z.filter (fun w => 1 / 2 + 2 * a / L ≤ w.re),
            ((analyticOrderAt riemannZeta w).toNat : ℝ))
          ≤ (T₂ - T₁) * (A * Real.exp (-(a / 1200))) + K * L := this
        _ = (T₂ - T₁) * A * Real.exp (-(a / 1200)) + K * L := by ring)
  refine (volume_speiserShadow_le hL0 (by linarith) hZ hT).trans (ENNReal.ofReal_le_ofReal ?_)
  have hLL : (L / 4 + 1) * (K * L) ≤ K * L ^ 2 / 2 := by
    nlinarith [mul_nonneg (mul_nonneg hK hL0.le) (by linarith : (0 : ℝ) ≤ L / 4 - 1)]
  have hπ : 0 < Real.pi := Real.pi_pos
  have h2 : 2 * (2 / Real.pi * (1201 * ((T₂ - T₁) * A) * Real.exp (-(κ / 2400)) +
      (L / 4 + 1) * (K * L))) ≤
      4 / Real.pi * 1201 * A * (T₂ - T₁) * Real.exp (-(κ / 2400)) + 2 / Real.pi * K * L ^ 2 := by
    have e1 : 2 * (2 / Real.pi * (1201 * ((T₂ - T₁) * A) * Real.exp (-(κ / 2400)) +
        (L / 4 + 1) * (K * L))) = 4 / Real.pi * 1201 * A * (T₂ - T₁) * Real.exp (-(κ / 2400)) +
          4 / Real.pi * ((L / 4 + 1) * (K * L)) := by ring
    rw [e1]
    have : 4 / Real.pi * ((L / 4 + 1) * (K * L)) ≤ 4 / Real.pi * (K * L ^ 2 / 2) :=
      mul_le_mul_of_nonneg_left hLL (by positivity)
    have e2 : 4 / Real.pi * (K * L ^ 2 / 2) = 2 / Real.pi * K * L ^ 2 := by ring
    linarith
  linarith

/-- **Dyadic form.** There are `A', K' ≥ 0` such that for all large `T` and every
`2 ≤ κ ≤ log(4T)/2 − 2`, the heights of `[T + 2, 2T − 2]` shadowed by a zero with
`|Re ρ − 1/2| ≥ κ/log(4T)` have measure at most `A' T e^{−κ/2400} + K' log²(4T)`. -/
theorem eventually_speiserShadow_dyadic_le :
    ∃ A' K' : ℝ, 0 ≤ A' ∧ 0 ≤ K' ∧ ∀ᶠ T in atTop, ∀ κ : ℝ, 2 ≤ κ →
      κ ≤ Real.log (4 * T) / 2 - 2 →
        volume {t : ℝ | t ∈ Icc (T + 2) (2 * T - 2) ∧ ∃ ρ : ℂ, xi ρ = 0 ∧
            κ / Real.log (4 * T) ≤ |ρ.re - 1 / 2| ∧ |t - ρ.im| ≤ |ρ.re - 1 / 2|} ≤
          ENNReal.ofReal (A' * T * Real.exp (-(κ / 2400)) + K' * Real.log (4 * T) ^ 2) := by
  obtain ⟨A', K', hA', hK', hev⟩ := exists_speiserShadow_exponential_density
  refine ⟨A', K', hA', hK', ?_⟩
  have h4 : Tendsto (fun T : ℝ => 4 * T) atTop atTop :=
    tendsto_id.const_mul_atTop (by norm_num)
  filter_upwards [h4.eventually hev, eventually_ge_atTop (1 : ℝ)] with T hT hT1
  obtain ⟨T₁, hT₁, T₂, hT₂, hbound⟩ := hT
  intro κ hκ hκL
  have hsub : {t : ℝ | t ∈ Icc (T + 2) (2 * T - 2) ∧ ∃ ρ : ℂ, xi ρ = 0 ∧
      κ / Real.log (4 * T) ≤ |ρ.re - 1 / 2| ∧ |t - ρ.im| ≤ |ρ.re - 1 / 2|} ⊆
      {t : ℝ | t ∈ Icc (T₁ + 1 / 2) (T₂ - 1 / 2) ∧ ∃ ρ : ℂ, xi ρ = 0 ∧
        κ / Real.log (4 * T) ≤ |ρ.re - 1 / 2| ∧ |t - ρ.im| ≤ |ρ.re - 1 / 2|} := by
    rintro t ⟨ht, h⟩
    refine ⟨⟨?_, ?_⟩, h⟩
    · have := hT₁.2; linarith [ht.1]
    · have := hT₂.1; linarith [ht.2]
  refine (measure_mono hsub).trans ((hbound κ hκ hκL).trans (ENNReal.ofReal_le_ofReal ?_))
  have hΔ : T₂ - T₁ ≤ T := by linarith [hT₁.1, hT₂.2]
  have he : 0 ≤ Real.exp (-(κ / 2400)) := (Real.exp_pos _).le
  nlinarith [mul_le_mul_of_nonneg_left hΔ (mul_nonneg hA' he)]

end

end RHTower
