import GaloisForLFunctions.HTGeometry.KleinbockMargulis.Good
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Topology.Algebra.Polynomial

/-!
# Polynomials are good functions (Kleinbock–Margulis, Proposition 3.2)

A real polynomial of degree at most `k` is `(2k(k+1)^{1/k}, 1/k)`-good on the real line.

The proof follows the paper.  If the sublevel set `{|f| < ε}` inside an interval `B` has measure
`m`, then for every `δ < m/(2k)` it contains `k+1` points that are pairwise `δ`-separated: a
`δ`-separated subset of cardinality `n ≤ k` cannot cover `{|f| < ε}` by the `n` balls of radius
`δ` around its points, since those have total measure at most `2kδ < m`, so one can always add a
further point.  Lagrange's interpolation formula at these `k+1` points then bounds `‖f‖_B` by
`(k+1) ε (|B|/δ)^k`, and letting `δ ↑ m/(2k)` gives the claim.

## Main results

* `exists_finset_separated` — a set of measure `> 2kδ` contains `k+1` points pairwise
  `δ`-separated.
* `abs_eval_le_of_lagrange` — the interpolation bound.
* `isGood_polynomial` — Proposition 3.2.
-/

open MeasureTheory Metric Set Filter Topology Polynomial
open scoped ENNReal NNReal

namespace GaloisForLFunctions.HTGeometry.KleinbockMargulis

/-! ### Separated points inside a set of large measure -/

/-- If a set of real numbers has measure larger than `2kδ`, it contains `k + 1` points that are
pairwise at distance at least `δ`.  Indeed a `δ`-separated subset of cardinality `n ≤ k` leaves
some point of the set outside the union of the `n` balls of radius `δ` around it, since those
balls have total measure at most `2kδ`. -/
theorem exists_finset_separated {S : Set ℝ} {δ : ℝ} (hδ : 0 < δ) (k : ℕ)
    (hm : 2 * (k : ℝ) * δ < (volume S).toReal) :
    ∃ T : Finset ℝ, ↑T ⊆ S ∧ T.card = k + 1 ∧ ∀ a ∈ T, ∀ b ∈ T, a ≠ b → δ ≤ |a - b| := by
  have hSfin : volume S ≠ ∞ := by
    intro h
    rw [h] at hm
    simp at hm
    linarith [mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (Nat.cast_nonneg k)) hδ.le]
  suffices H : ∀ n : ℕ, n ≤ k + 1 → ∃ T : Finset ℝ, ↑T ⊆ S ∧ T.card = n ∧
      ∀ a ∈ T, ∀ b ∈ T, a ≠ b → δ ≤ |a - b| from H (k + 1) le_rfl
  intro n
  induction n with
  | zero => intro _; exact ⟨∅, by simp, by simp, by simp⟩
  | succ n ih =>
    intro hn
    obtain ⟨T, hTS, hTcard, hTsep⟩ := ih (Nat.le_of_succ_le hn)
    have hnk : n ≤ k := Nat.succ_le_succ_iff.mp hn
    -- some point of `S` is `δ`-far from every point of `T`
    have hexists : ∃ y ∈ S, ∀ t ∈ T, δ ≤ |y - t| := by
      by_contra hcon
      push Not at hcon
      have hcover : S ⊆ ⋃ t ∈ T, ball t δ := by
        intro y hy
        obtain ⟨t, ht, hlt⟩ := hcon y hy
        exact mem_biUnion ht (by simpa [Real.dist_eq] using hlt)
      have h1 : volume S ≤ ∑ t ∈ T, volume (ball t δ) :=
        le_trans (measure_mono hcover) (measure_biUnion_finset_le T _)
      have h2 : ∑ t ∈ T, volume (ball t δ) = (n : ℝ≥0∞) * ENNReal.ofReal (2 * δ) := by
        simp [Real.volume_ball, hTcard, mul_comm]
      rw [h2] at h1
      have h3 : (volume S).toReal ≤ (n : ℝ) * (2 * δ) := by
        have := ENNReal.toReal_mono (by simp [ENNReal.mul_eq_top]) h1
        simpa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hδ.le,
          ENNReal.toReal_ofReal (by positivity : (0:ℝ) ≤ 2 * δ)] using this
      have h4 : (n : ℝ) ≤ (k : ℝ) := Nat.cast_le.mpr hnk
      nlinarith [hδ.le]
    obtain ⟨y, hyS, hy⟩ := hexists
    have hyT : y ∉ T := by
      intro hmem
      have := hy y hmem
      simp at this
      linarith
    refine ⟨insert y T, ?_, ?_, ?_⟩
    · intro a ha
      rcases Finset.mem_insert.mp (by exact_mod_cast ha) with rfl | ha'
      · exact hyS
      · exact hTS ha'
    · rw [Finset.card_insert_of_notMem hyT, hTcard]
    · intro a ha bb hb hab
      rcases Finset.mem_insert.mp ha with rfl | ha'
      · rcases Finset.mem_insert.mp hb with rfl | hb'
        · exact absurd rfl hab
        · exact hy bb hb'
      · rcases Finset.mem_insert.mp hb with rfl | hb'
        · rw [abs_sub_comm]; exact hy a ha'
        · exact hTsep a ha' bb hb' hab

/-! ### The interpolation bound -/

/-- **Lagrange's bound.**  A polynomial of degree at most `k` which is at most `ε` in absolute
value at `k + 1` points that are pairwise `δ`-separated is at most `(k+1) ε (b/δ)^k` at any point
at distance at most `b` from all of them. -/
theorem abs_eval_le_of_lagrange {k : ℕ} (P : Polynomial ℝ) (hdeg : P.natDegree ≤ k)
    (v : Fin (k + 1) → ℝ) (hinj : Function.Injective v) {ε δ b : ℝ} (hδ : 0 < δ) (_hb : 0 ≤ b)
    (hbound : ∀ i, |P.eval (v i)| ≤ ε) (hsep : ∀ i j, i ≠ j → δ ≤ |v i - v j|)
    {x : ℝ} (hx : ∀ i, |x - v i| ≤ b) :
    |P.eval x| ≤ ((k : ℝ) + 1) * ε * (b / δ) ^ k := by
  classical
  have hεnn : 0 ≤ ε := le_trans (abs_nonneg _) (hbound 0)
  have hcard : (Finset.univ : Finset (Fin (k + 1))).card = k + 1 := by simp
  have hdlt : P.degree < ((Finset.univ : Finset (Fin (k + 1))).card : ℕ) := by
    rw [hcard]
    rcases eq_or_ne P 0 with rfl | hP
    · simp
    · exact lt_of_le_of_lt (degree_le_natDegree) (by exact_mod_cast Nat.lt_succ_of_le hdeg)
  have hinjOn : Set.InjOn v (Finset.univ : Finset (Fin (k + 1))) := hinj.injOn
  have hP := Lagrange.eq_interpolate hinjOn hdlt
  have heval : P.eval x
      = ∑ i : Fin (k + 1), P.eval (v i) * (Lagrange.basis Finset.univ v i).eval x := by
    conv_lhs => rw [hP]
    simp [Lagrange.interpolate_apply, eval_finsetSum]
  -- each Lagrange basis polynomial is bounded by `(b/δ)^k` at `x`
  have hbasis : ∀ i : Fin (k + 1), |(Lagrange.basis Finset.univ v i).eval x| ≤ (b / δ) ^ k := by
    intro i
    have hprod : (Lagrange.basis Finset.univ v i).eval x
        = ∏ j ∈ Finset.univ.erase i, (v i - v j)⁻¹ * (x - v j) := by
      simp [Lagrange.basis, eval_prod, Lagrange.basisDivisor]
    rw [hprod, Finset.abs_prod]
    have hle : ∀ j ∈ Finset.univ.erase i, |(v i - v j)⁻¹ * (x - v j)| ≤ b / δ := by
      intro j hj
      have hne : i ≠ j := (Finset.ne_of_mem_erase hj).symm
      have h1 : δ ≤ |v i - v j| := hsep i j hne
      have h2 : |x - v j| ≤ b := hx j
      rw [abs_mul, abs_inv]
      have h3 : |v i - v j|⁻¹ ≤ δ⁻¹ := by gcongr
      calc |v i - v j|⁻¹ * |x - v j| ≤ δ⁻¹ * b :=
            mul_le_mul h3 h2 (abs_nonneg _) (by positivity)
        _ = b / δ := by ring
    calc ∏ j ∈ Finset.univ.erase i, |(v i - v j)⁻¹ * (x - v j)|
        ≤ ∏ _j ∈ Finset.univ.erase i, (b / δ) :=
          Finset.prod_le_prod (fun j _ => abs_nonneg _) hle
      _ = (b / δ) ^ k := by
          rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ i), hcard]
          simp
  calc |P.eval x| = |∑ i : Fin (k + 1), P.eval (v i) * (Lagrange.basis Finset.univ v i).eval x| := by
        rw [heval]
    _ ≤ ∑ i : Fin (k + 1), |P.eval (v i) * (Lagrange.basis Finset.univ v i).eval x| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin (k + 1), ε * (b / δ) ^ k := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [abs_mul]
        exact mul_le_mul (hbound i) (hbasis i) (abs_nonneg _) hεnn
    _ = ((k : ℝ) + 1) * ε * (b / δ) ^ k := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring

/-! ### Proposition 3.2 -/

/-- A bound `X ≤ K/δ` valid for all `δ` below `D` passes to the limit `δ = D`. -/
theorem le_div_of_forall_lt {X K D : ℝ} (hD : 0 < D) (h : ∀ δ, 0 < δ → δ < D → X ≤ K / δ) :
    X ≤ K / D := by
  have hcont : Filter.Tendsto (fun δ : ℝ => K / δ) (𝓝[<] D) (𝓝 (K / D)) :=
    ((continuousAt_const.div continuousAt_id hD.ne')).continuousWithinAt
  have hev : ∀ᶠ δ in 𝓝[<] D, X ≤ K / δ := by
    filter_upwards [self_mem_nhdsWithin,
      eventually_nhdsWithin_of_eventually_nhds (eventually_gt_nhds hD)] with δ h1 h2
    exact h δ h2 h1
  exact ge_of_tendsto hcont hev

/-- The one-dimensional core of Proposition 3.2: on an interval, the sublevel measure of a
polynomial of degree at most `k` obeys `m · |f(z)|^{1/k} ≤ 2k(k+1)^{1/k} ε^{1/k} |B|`. -/
theorem polynomial_measure_mul_rpow_le {k : ℕ} (hk : 1 ≤ k) (P : Polynomial ℝ)
    (hdeg : P.natDegree ≤ k) {a c : ℝ} (hac : a < c) {ε : ℝ} (hε : 0 < ε)
    {z : ℝ} (hz : z ∈ Ioo a c) :
    (volume {x ∈ Ioo a c | |P.eval x| < ε}).toReal * |P.eval z| ^ ((k : ℝ)⁻¹)
      ≤ 2 * (k : ℝ) * (((k : ℝ) + 1) ^ ((k : ℝ)⁻¹) * ε ^ ((k : ℝ)⁻¹)) * (c - a) := by
  classical
  have hkR : (0:ℝ) < k := by exact_mod_cast hk
  have hkinv : (0:ℝ) < (k : ℝ)⁻¹ := by positivity
  set S : Set ℝ := {x ∈ Ioo a c | |P.eval x| < ε} with hS
  set m : ℝ := (volume S).toReal with hmdef
  set L : ℝ := c - a with hLdef
  have hL : 0 < L := by simp [hLdef]; linarith
  have hmnn : 0 ≤ m := ENNReal.toReal_nonneg
  have hRHSnn : 0 ≤ 2 * (k : ℝ) * (((k : ℝ) + 1) ^ ((k : ℝ)⁻¹) * ε ^ ((k : ℝ)⁻¹)) * L := by
    have h1 : (0:ℝ) ≤ ((k : ℝ) + 1) ^ ((k : ℝ)⁻¹) := Real.rpow_nonneg (by positivity) _
    have h2 : (0:ℝ) ≤ ε ^ ((k : ℝ)⁻¹) := Real.rpow_nonneg hε.le _
    positivity
  rcases eq_or_lt_of_le hmnn with hm0 | hmpos
  · rw [← hm0]; simpa using hRHSnn
  -- the main case: the sublevel set has positive measure
  set D : ℝ := m / (2 * (k : ℝ)) with hDdef
  have hD : 0 < D := by rw [hDdef]; positivity
  set K : ℝ := m * (((k : ℝ) + 1) * ε) ^ ((k : ℝ)⁻¹) * L with hKdef
  have hmain : ∀ δ : ℝ, 0 < δ → δ < D → m * |P.eval z| ^ ((k : ℝ)⁻¹) ≤ K / δ := by
    intro δ hδ hδD
    have hsep : 2 * (k : ℝ) * δ < (volume S).toReal := by
      rw [← hmdef]
      rw [hDdef, lt_div_iff₀ (by positivity)] at hδD
      linarith [hδD]
    obtain ⟨T, hTS, hTcard, hTsep⟩ := exists_finset_separated hδ k hsep
    set v : Fin (k + 1) → ℝ := fun i => ((T.orderIsoOfFin hTcard i : {x // x ∈ T}) : ℝ) with hv
    have hvmem : ∀ i, v i ∈ T := fun i => (T.orderIsoOfFin hTcard i).2
    have hvinj : Function.Injective v := by
      intro i j hij
      exact (T.orderIsoOfFin hTcard).injective (Subtype.ext hij)
    have hvS : ∀ i, v i ∈ S := fun i => hTS (by exact_mod_cast hvmem i)
    have hbound : ∀ i, |P.eval (v i)| ≤ ε := fun i => (hvS i).2.le
    have hsepv : ∀ i j, i ≠ j → δ ≤ |v i - v j| := by
      intro i j hij
      exact hTsep _ (hvmem i) _ (hvmem j) (fun h => hij (hvinj h))
    have hx : ∀ i, |z - v i| ≤ L := by
      intro i
      have h1 := (hvS i).1
      rw [abs_le]
      constructor <;> [skip; skip] <;>
        simp only [hLdef] <;> [linarith [hz.1, hz.2, h1.1, h1.2]; linarith [hz.1, hz.2, h1.1, h1.2]]
    have hlag := abs_eval_le_of_lagrange P hdeg v hvinj hδ hL.le hbound hsepv hx
    -- take `k`-th roots
    have hpow : |P.eval z| ^ ((k : ℝ)⁻¹) ≤ (((k : ℝ) + 1) * ε) ^ ((k : ℝ)⁻¹) * (L / δ) := by
      have h1 : |P.eval z| ^ ((k : ℝ)⁻¹)
          ≤ (((k : ℝ) + 1) * ε * (L / δ) ^ k) ^ ((k : ℝ)⁻¹) :=
        Real.rpow_le_rpow (abs_nonneg _) hlag hkinv.le
      refine h1.trans_eq ?_
      have hLδ : (0:ℝ) ≤ L / δ := by positivity
      rw [Real.mul_rpow (by positivity) (by positivity)]
      congr 1
      rw [← Real.rpow_natCast (L / δ) k, ← Real.rpow_mul hLδ,
        mul_inv_cancel₀ (by positivity : (k:ℝ) ≠ 0), Real.rpow_one]
    have hfin : m * |P.eval z| ^ ((k : ℝ)⁻¹)
        ≤ m * ((((k : ℝ) + 1) * ε) ^ ((k : ℝ)⁻¹) * (L / δ)) := by
      exact mul_le_mul_of_nonneg_left hpow hmnn
    refine hfin.trans_eq ?_
    rw [hKdef]
    field_simp
  have hlim := le_div_of_forall_lt hD hmain
  refine hlim.trans_eq ?_
  rw [hKdef, hDdef]
  have hsplit : (((k : ℝ) + 1) * ε) ^ ((k : ℝ)⁻¹)
      = ((k : ℝ) + 1) ^ ((k : ℝ)⁻¹) * ε ^ ((k : ℝ)⁻¹) :=
    Real.mul_rpow (by positivity) hε.le
  rw [hsplit]
  field_simp

/-- **Proposition 3.2.**  Every real polynomial of degree at most `k ≥ 1` is
`(2k(k+1)^{1/k}, 1/k)`-good on the whole line. -/
theorem isGood_polynomial {k : ℕ} (hk : 1 ≤ k) (P : Polynomial ℝ) (hdeg : P.natDegree ≤ k) :
    IsGood (2 * (k : ℝ) * ((k : ℝ) + 1) ^ ((k : ℝ)⁻¹)) ((k : ℝ)⁻¹)
      (fun x : Fin 1 → ℝ => P.eval (x 0)) univ := by
  classical
  refine isGood_of_toReal ?_
  intro x₀ r hr _ ε hε z hz
  have hmp : MeasurePreserving (MeasurableEquiv.funUnique (Fin 1) ℝ) volume volume :=
    volume_preserving_funUnique (Fin 1) ℝ
  have hmem : ∀ x : Fin 1 → ℝ, x ∈ ball x₀ r ↔ x 0 ∈ Ioo (x₀ 0 - r) (x₀ 0 + r) := by
    intro x
    rw [mem_ball, dist_pi_lt_iff hr, mem_Ioo]
    constructor
    · intro h
      have h0 := h 0
      rw [Real.dist_eq, abs_lt] at h0
      constructor <;> linarith [h0.1, h0.2]
    · intro h i
      have hi : i = 0 := Subsingleton.elim i 0
      subst hi
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith [h.1, h.2]
  have hset : {x ∈ ball x₀ r | |P.eval (x 0)| < ε}
      = (MeasurableEquiv.funUnique (Fin 1) ℝ) ⁻¹'
        {t ∈ Ioo (x₀ 0 - r) (x₀ 0 + r) | |P.eval t| < ε} := by
    ext x
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨(hmem x).mp h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨(hmem x).mpr h1, h2⟩
  have hmeas : MeasurableSet {t ∈ Ioo (x₀ 0 - r) (x₀ 0 + r) | |P.eval t| < ε} :=
    measurableSet_Ioo.inter (measurableSet_lt (P.continuous.abs.measurable) measurable_const)
  have hvol1 : volume {x ∈ ball x₀ r | |P.eval (x 0)| < ε}
      = volume {t ∈ Ioo (x₀ 0 - r) (x₀ 0 + r) | |P.eval t| < ε} := by
    rw [hset, hmp.measure_preimage hmeas.nullMeasurableSet]
  have hvol2 : (volume (ball x₀ r : Set (Fin 1 → ℝ))).toReal = (x₀ 0 + r) - (x₀ 0 - r) := by
    rw [Real.volume_pi_ball _ hr]
    simp only [Fintype.card_fin, pow_one,
      ENNReal.toReal_ofReal (by linarith : (0:ℝ) ≤ 2 * r)]
    ring
  have hzI : z 0 ∈ Ioo (x₀ 0 - r) (x₀ 0 + r) := (hmem z).mp hz
  have hcore := polynomial_measure_mul_rpow_le hk P hdeg
    (show x₀ 0 - r < x₀ 0 + r by linarith) hε hzI
  rw [hvol1, hvol2]
  refine hcore.trans_eq ?_
  ring

end GaloisForLFunctions.HTGeometry.KleinbockMargulis
