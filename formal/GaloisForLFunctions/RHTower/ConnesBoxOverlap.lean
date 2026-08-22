import GaloisForLFunctions.RHTower.ConnesOrbitGeometricConvergence
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# §VII (10): the box-overlap estimate

§VII (10) of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068:

  `|⟨k_n , U(q^{-1}) k_n⟩| ≤ c n^m (Sup_S |q_v|)^{-1}`,   `m = Card(S)`,

where `k_n` is the characteristic function of the box `K_n = {x : |x_v| ≤ n ∀ v ∈ S}`.

The inner product is `|q|^{1/2}` times the volume of `K_n ∩ q^{-1}K_n`, which factorises over the
places into `∏_v vol_v{|x_v| ≤ min(n, n/|q_v|)}`.  Since `q` is an `S`-unit its module `|q| = ∏|q_v|`
is `1`, and the arithmetic content of (10) is then the elementary inequality proved here:

  `∏_v min(1, a_v⁻¹) ≤ (Sup_v a_v)^{-1}`   whenever `a_v > 0` and `∏_v a_v = 1`.

The product being `1` forces the largest `a_v` to be at least `1`, so the factor at the maximising
place is exactly `(Sup a)^{-1}` and every other factor is at most `1`.

The archimedean overlap volume is computed exactly, so the abstract bound is grounded in a real
measure rather than left as a hypothesis.
-/

open MeasureTheory Set Finset

namespace GaloisForLFunctions.RHTower

noncomputable section

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- A finite family of positive reals with product one has a member at least `1`. -/
theorem connes_one_le_sup_of_prod_eq_one {a : ι → ℝ} (hpos : ∀ i, 0 < a i)
    (hprod : ∏ i, a i = 1) :
    1 ≤ Finset.univ.sup' Finset.univ_nonempty a := by
  by_contra hcon
  rw [not_le] at hcon
  have hle : ∀ i : ι, a i ≤ Finset.univ.sup' Finset.univ_nonempty a := fun i =>
    Finset.le_sup' a (Finset.mem_univ i)
  have hstep : (∏ i : ι, a i)
      ≤ ∏ _i : ι, Finset.univ.sup' Finset.univ_nonempty a :=
    Finset.prod_le_prod (fun i _ => (hpos i).le) (fun i _ => hle i)
  rw [hprod, Finset.prod_const] at hstep
  have hcard : 0 < Fintype.card ι := Fintype.card_pos
  have hs0 : 0 < Finset.univ.sup' Finset.univ_nonempty a := by
    obtain ⟨i⟩ := ‹Nonempty ι›
    exact lt_of_lt_of_le (hpos i) (hle i)
  have hlt : (Finset.univ.sup' Finset.univ_nonempty a) ^ (Fintype.card ι) < 1 :=
    pow_lt_one₀ hs0.le hcon hcard.ne'
  rw [Finset.card_univ] at hstep
  linarith

/-- **§VII (10), the arithmetic core.** -/
theorem connes_prod_min_le_sup_inv {a : ι → ℝ} (hpos : ∀ i, 0 < a i)
    (hprod : ∏ i, a i = 1) :
    (∏ i, min 1 (a i)⁻¹) ≤ (Finset.univ.sup' Finset.univ_nonempty a)⁻¹ := by
  classical
  obtain ⟨w, _, hw⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty a
  have hone : 1 ≤ Finset.univ.sup' Finset.univ_nonempty a :=
    connes_one_le_sup_of_prod_eq_one hpos hprod
  have hw1 : 1 ≤ a w := by rw [hw] at hone; exact hone
  have hminw : min 1 (a w)⁻¹ = (a w)⁻¹ := by
    refine min_eq_right ?_
    have h := hpos w
    have hcancel : (a w)⁻¹ * a w = 1 := inv_mul_cancel₀ (ne_of_gt h)
    nlinarith [inv_nonneg.mpr h.le]
  have hnn : ∀ i : ι, 0 ≤ min 1 (a i)⁻¹ := fun i =>
    le_min zero_le_one (inv_nonneg.mpr (hpos i).le)
  have hle1 : ∀ i : ι, min 1 (a i)⁻¹ ≤ 1 := fun _ => min_le_left _ _
  have hsplit : (∏ i, min 1 (a i)⁻¹)
      = min 1 (a w)⁻¹ * ∏ i ∈ Finset.univ.erase w, min 1 (a i)⁻¹ :=
    (Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ w)).symm
  have hrest : (∏ i ∈ Finset.univ.erase w, min 1 (a i)⁻¹) ≤ 1 :=
    Finset.prod_le_one (fun i _ => hnn i) (fun i _ => hle1 i)
  calc (∏ i, min 1 (a i)⁻¹)
      = min 1 (a w)⁻¹ * ∏ i ∈ Finset.univ.erase w, min 1 (a i)⁻¹ := hsplit
    _ ≤ min 1 (a w)⁻¹ * 1 := mul_le_mul_of_nonneg_left hrest (hnn w)
    _ = (a w)⁻¹ := by rw [hminw, mul_one]
    _ = (Finset.univ.sup' Finset.univ_nonempty a)⁻¹ := by rw [hw]

/-- The overlap radius factorises out one power of the box size. -/
theorem connes_boxOverlap_radius {n : ℝ} (hn : 0 ≤ n) (a : ℝ) :
    min n (n / a) = n * min 1 a⁻¹ := by
  rw [mul_min_of_nonneg _ _ hn, mul_one, ← div_eq_mul_inv]

/-- **§VII (10).**  The overlap of the box `K_n` with its dilate is at most
`(∏ c_v) n^{Card S} (Sup_v a_v)^{-1}`. -/
theorem connes_boxOverlap_prod_le {n : ℝ} (hn : 0 ≤ n) {a c : ι → ℝ}
    (hpos : ∀ i, 0 < a i) (hprod : ∏ i, a i = 1) (hc : ∀ i, 0 ≤ c i) :
    (∏ i, c i * min n (n / a i))
      ≤ (∏ i, c i) * (n ^ (Fintype.card ι) *
          (Finset.univ.sup' Finset.univ_nonempty a)⁻¹) := by
  have hrw : ∀ i : ι, c i * min n (n / a i) = c i * (n * min 1 (a i)⁻¹) := by
    intro i
    rw [connes_boxOverlap_radius hn (a i)]
  have hsplit : (∏ i, c i * min n (n / a i))
      = (∏ i, c i) * (n ^ (Fintype.card ι) * ∏ i, min 1 (a i)⁻¹) := by
    calc (∏ i, c i * min n (n / a i))
        = ∏ i, (c i * n) * min 1 (a i)⁻¹ := by
          refine Finset.prod_congr rfl fun i _ => ?_
          rw [hrw i]
          ring
      _ = (∏ i, c i * n) * ∏ i, min 1 (a i)⁻¹ := Finset.prod_mul_distrib
      _ = ((∏ i, c i) * n ^ (Fintype.card ι)) * ∏ i, min 1 (a i)⁻¹ := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
      _ = (∏ i, c i) * (n ^ (Fintype.card ι) * ∏ i, min 1 (a i)⁻¹) := by ring
  rw [hsplit]
  have hcnn : (0 : ℝ) ≤ ∏ i, c i := Finset.prod_nonneg fun i _ => hc i
  have hnpow : (0 : ℝ) ≤ n ^ (Fintype.card ι) := by positivity
  refine mul_le_mul_of_nonneg_left ?_ hcnn
  exact mul_le_mul_of_nonneg_left (connes_prod_min_le_sup_inv hpos hprod) hnpow

/-- The archimedean overlap volume, computed exactly. -/
theorem connes_archBoxOverlap_volume {n : ℝ} (hn : 0 ≤ n) {a : ℝ} (ha : 0 < a) :
    (volume {x : ℝ | |x| ≤ n ∧ |a * x| ≤ n}).toReal = 2 * min n (n / a) := by
  have hset : {x : ℝ | |x| ≤ n ∧ |a * x| ≤ n} = Icc (-(min n (n / a))) (min n (n / a)) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_Icc, abs_mul, abs_of_pos ha]
    constructor
    · rintro ⟨h1, h2⟩
      have h2' : |x| ≤ n / a := by
        rw [le_div_iff₀ ha]
        linarith [h2]
      have : |x| ≤ min n (n / a) := le_min h1 h2'
      exact abs_le.mp this
    · intro h
      have hx : |x| ≤ min n (n / a) := abs_le.mpr h
      refine ⟨le_trans hx (min_le_left _ _), ?_⟩
      have h2 : |x| ≤ n / a := le_trans hx (min_le_right _ _)
      rw [mul_comm]
      exact (le_div_iff₀ ha).mp h2
  rw [hset, Real.volume_Icc]
  have hmnn : (0 : ℝ) ≤ min n (n / a) := le_min hn (by positivity)
  rw [ENNReal.toReal_ofReal (by linarith)]
  ring

end

end GaloisForLFunctions.RHTower
