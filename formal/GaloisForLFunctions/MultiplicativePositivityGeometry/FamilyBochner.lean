import GaloisForLFunctions.MultiplicativePositivityGeometry.SummableBochner
import GaloisForLFunctions.MultiplicativePositivityGeometry.FamilyCapacity

/-!
# Bochner's theorem for families

For a family over a finite abelian group `G`, an absolutely summable configuration `𝒟` on `G × ℝ` is
a joint boundary divisor iff it is even and positive definite (`family_summable_bochner`). This is
the family form of the finite and summable Bochner theorems: poles and zeros may sit at any points
`(g, u)`, with any orders, as long as positive definiteness on `G × ℝ` holds.

* **Positivity** (`familyBohr_nonneg`). For a character `ψ` of `G` and `t ∈ ℝ`,
  `(g, u) ↦ Re(ψ(g) e^{itu})` is a unitary character of `G × ℝ`, so
  `B(ψ, t) = Σ_p 𝒟(p) Re(ψ(−p₁) e^{−itp₂}) ≥ 0` by Bochner positivity in `ℓ¹`
  (`tsum_nonneg_of_gram`): the Gram forms split into the Gram forms of the real and imaginary parts.
* **Realization** (`familyWeight_isJointBoundaryDivisor`). The weights
  `Λ(n) n^{−1−x} B(ψ, log n)/|G|` on the frequencies `(ψ, log n)` have joint trace
  `Σ_p (𝒟(p)/2)([g = p₁] tr_ζ(u − p₂) + [g = −p₁] tr_ζ(u + p₂))` by character orthogonality
  (`sum_jointMode_mul`), and Tannery's theorem passes to the boundary.
-/

open Finset Filter Topology Complex

namespace GaloisForLFunctions.MultiplicativePositivityGeometry

universe u

variable {G : Type u} [AddCommGroup G] [Fintype G] [DecidableEq G]

omit [DecidableEq G] in
/-- A joint mode at a difference is the real Gram kernel of the phases. -/
theorem jointMode_sub (ψ : AddChar G ℂ) (t : ℝ) (p q : G × ℝ) :
    jointMode ψ t (p - q) = (jointPhase ψ t p).re * (jointPhase ψ t q).re +
      (jointPhase ψ t p).im * (jointPhase ψ t q).im := by
  rw [jointMode, jointPhase_sub, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

omit [DecidableEq G] in
/-- Gram forms of `𝒟 · Re(ψ e^{it·})` are nonnegative. -/
theorem IsEvenPosDef.sum_sum_jointMode_nonneg {𝒟 : G × ℝ → ℝ} (h𝒟 : IsEvenPosDef 𝒟)
    (ψ : AddChar G ℂ) (t : ℝ) (F : Finset (G × ℝ)) :
    0 ≤ ∑ x ∈ F, ∑ y ∈ F, 𝒟 (x - y) * jointMode ψ t (x - y) := by
  have h1 := h𝒟.sum_finset_mul_nonneg F fun x => (jointPhase ψ t x).re
  have h2 := h𝒟.sum_finset_mul_nonneg F fun x => (jointPhase ψ t x).im
  have e : ∑ x ∈ F, ∑ y ∈ F, 𝒟 (x - y) * jointMode ψ t (x - y) =
      ∑ x ∈ F, ∑ y ∈ F, (jointPhase ψ t x).re * (jointPhase ψ t y).re * 𝒟 (x - y) +
        ∑ x ∈ F, ∑ y ∈ F, (jointPhase ψ t x).im * (jointPhase ψ t y).im * 𝒟 (x - y) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [jointMode_sub]
    ring
  rw [e]
  exact add_nonneg h1 h2

/-- The family Bohr series `B(ψ, t) = Σ_p 𝒟(p) Re(ψ(−p₁) e^{−itp₂})`. -/
noncomputable def familyBohr (𝒟 : G × ℝ → ℝ) (ψ : AddChar G ℂ) (t : ℝ) : ℝ :=
  ∑' p, 𝒟 p * jointMode ψ t (-p)

omit [DecidableEq G] in
theorem summable_mul_jointMode {𝒟 : G × ℝ → ℝ} (hs : Summable 𝒟) (ψ : AddChar G ℂ) (t : ℝ)
    (f : G × ℝ → G × ℝ) : Summable fun p => 𝒟 p * jointMode ψ t (f p) :=
  Summable.of_norm_bounded hs.abs fun p => by
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (abs_jointMode_le _ _ _)

omit [DecidableEq G] in
theorem familyBohr_nonneg {𝒟 : G × ℝ → ℝ} (h𝒟 : IsEvenPosDef 𝒟) (hs : Summable 𝒟)
    (ψ : AddChar G ℂ) (t : ℝ) : 0 ≤ familyBohr 𝒟 ψ t := by
  have h := tsum_nonneg_of_gram hs (ψ := fun p => 𝒟 p * jointMode ψ t p)
    (fun p => by rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (abs_jointMode_le _ _ _))
    (h𝒟.sum_sum_jointMode_nonneg ψ t)
  unfold familyBohr
  rw [← (Equiv.neg (G × ℝ)).tsum_eq]
  simpa [h𝒟.even] using h

omit [DecidableEq G] in
theorem abs_familyBohr_le {𝒟 : G × ℝ → ℝ} (hs : Summable 𝒟) (ψ : AddChar G ℂ) (t : ℝ) :
    |familyBohr 𝒟 ψ t| ≤ ∑' p, |𝒟 p| := by
  have hb := summable_mul_jointMode hs ψ t Neg.neg
  unfold familyBohr
  rw [← Real.norm_eq_abs]
  refine (norm_tsum_le_tsum_norm hb.norm).trans (Summable.tsum_le_tsum (fun p => ?_) hb.norm hs.abs)
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (abs_jointMode_le _ _ _)

/-- The family weights `Λ(n) n^{−1−x} B(ψ, log n)/|G|`. -/
noncomputable def familyWeight (𝒟 : G × ℝ → ℝ) (x : ℝ) (r : ℕ × AddChar G ℂ) : ℝ :=
  zetaBoundaryWeight x r.1 * (familyBohr 𝒟 r.2 (logFrequency r.1) / Fintype.card G)

/-- The joint trace of the family weights through shifted ζ-traces. -/
theorem jointTrace_familyWeight {𝒟 : G × ℝ → ℝ} (h𝒟 : IsEvenPosDef 𝒟) (hs : Summable 𝒟)
    {x : ℝ} (hx : 0 < x) (q : G × ℝ) :
    jointTrace (familyWeight 𝒟 x) Prod.snd (fun r => logFrequency r.1) q =
      ∑' p, 𝒟 p / 2 * ((if q.1 = p.1 then 1 else 0) *
          cosineTrace (zetaBoundaryWeight x) logFrequency (q.2 - p.2) +
        (if q.1 = -p.1 then 1 else 0) *
          cosineTrace (zetaBoundaryWeight x) logFrequency (q.2 + p.2)) := by
  have hz := summable_zetaBoundaryWeight hx
  have hz0 := zetaBoundaryWeight_nonneg x
  have hG : (Fintype.card G : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hG0 : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  set A := ∑' p, |𝒟 p|
  -- Absolute summability of the weights.
  have hwb : ∀ r : ℕ × AddChar G ℂ, |familyWeight 𝒟 x r| ≤ zetaBoundaryWeight x r.1 * A := by
    intro r
    unfold familyWeight
    rw [abs_mul, abs_of_nonneg (hz0 _), abs_div, abs_of_pos hG0]
    refine mul_le_mul_of_nonneg_left ?_ (hz0 _)
    rw [div_le_iff₀ hG0]
    exact (abs_familyBohr_le hs _ _).trans (le_mul_of_one_le_right
      (tsum_nonneg fun p => abs_nonneg _) (by exact_mod_cast Fintype.card_pos))
  have hsw : Summable fun r : ℕ × AddChar G ℂ =>
      familyWeight 𝒟 x r * jointMode r.2 (logFrequency r.1) q := by
    refine Summable.of_norm_bounded (g := fun r : ℕ × AddChar G ℂ => zetaBoundaryWeight x r.1 * A)
      ?_ fun r => ?_
    · exact (summable_prod_of_nonneg fun r => mul_nonneg (hz0 _)
        (tsum_nonneg fun p => abs_nonneg _)).mpr ⟨fun _ => Summable.of_finite, by
          simpa [tsum_fintype] using (hz.mul_right A).mul_left (Fintype.card (AddChar G ℂ) : ℝ)⟩
    · rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (abs_jointMode_le _ _ _) |>.trans (hwb r)
  -- Character orthogonality inside each integer.
  have hinner : ∀ n : ℕ, ∑' ψ : AddChar G ℂ, familyWeight 𝒟 x (n, ψ) *
      jointMode ψ (logFrequency n) q =
      ∑' p, 𝒟 p / 2 * ((if q.1 = p.1 then 1 else 0) *
          (zetaBoundaryWeight x n * Real.cos (logFrequency n * (q.2 - p.2))) +
        (if q.1 = -p.1 then 1 else 0) *
          (zetaBoundaryWeight x n * Real.cos (logFrequency n * (q.2 + p.2)))) := by
    intro n
    rw [tsum_fintype]
    simp only [familyWeight, familyBohr]
    have hstep : ∀ ψ : AddChar G ℂ, zetaBoundaryWeight x n *
        ((∑' p, 𝒟 p * jointMode ψ (logFrequency n) (-p)) / Fintype.card G) *
          jointMode ψ (logFrequency n) q =
        ∑' p, zetaBoundaryWeight x n / Fintype.card G *
          (𝒟 p * (jointMode ψ (logFrequency n) (-p) * jointMode ψ (logFrequency n) q)) := by
      intro ψ
      have e : ∀ S : ℝ, zetaBoundaryWeight x n * (S / Fintype.card G) *
          jointMode ψ (logFrequency n) q =
          zetaBoundaryWeight x n / Fintype.card G * (S * jointMode ψ (logFrequency n) q) :=
        fun S => by ring
      rw [e, ← tsum_mul_right, ← tsum_mul_left]
      exact tsum_congr fun p => by ring
    rw [Finset.sum_congr rfl fun ψ _ => hstep ψ, ← Summable.tsum_finsetSum fun ψ _ =>
      ((summable_mul_jointMode hs ψ (logFrequency n) Neg.neg).mul_right
        (jointMode ψ (logFrequency n) q)).mul_left (zetaBoundaryWeight x n / Fintype.card G)
          |>.congr fun p => by ring]
    refine tsum_congr fun p => ?_
    rw [← Finset.mul_sum, ← Finset.mul_sum, sum_jointMode_mul]
    field_simp
  -- Swap the integers and the points.
  set f : ℕ → G × ℝ → ℝ := fun n p => 𝒟 p / 2 * ((if q.1 = p.1 then 1 else 0) *
      (zetaBoundaryWeight x n * Real.cos (logFrequency n * (q.2 - p.2))) +
    (if q.1 = -p.1 then 1 else 0) *
      (zetaBoundaryWeight x n * Real.cos (logFrequency n * (q.2 + p.2))))
  have hf : Summable (Function.uncurry f) := by
    refine Summable.of_norm_bounded (Summable.mul_of_nonneg hz hs.abs hz0 fun p => abs_nonneg _)
      fun r => ?_
    obtain ⟨n, p⟩ := r
    simp only [Function.uncurry_apply_pair, f, Real.norm_eq_abs]
    have h1 := Real.abs_cos_le_one (logFrequency n * (q.2 - p.2))
    have h2 := Real.abs_cos_le_one (logFrequency n * (q.2 + p.2))
    have hi1 : |(if q.1 = p.1 then (1 : ℝ) else 0)| ≤ 1 := by split_ifs <;> simp
    have hi2 : |(if q.1 = -p.1 then (1 : ℝ) else 0)| ≤ 1 := by split_ifs <;> simp
    have hz1 : |zetaBoundaryWeight x n * Real.cos (logFrequency n * (q.2 - p.2))| ≤
        zetaBoundaryWeight x n := by
      rw [abs_mul, abs_of_nonneg (hz0 n)]; exact mul_le_of_le_one_right (hz0 n) h1
    have hz2 : |zetaBoundaryWeight x n * Real.cos (logFrequency n * (q.2 + p.2))| ≤
        zetaBoundaryWeight x n := by
      rw [abs_mul, abs_of_nonneg (hz0 n)]; exact mul_le_of_le_one_right (hz0 n) h2
    calc |𝒟 p / 2 * ((if q.1 = p.1 then 1 else 0) *
            (zetaBoundaryWeight x n * Real.cos (logFrequency n * (q.2 - p.2))) +
          (if q.1 = -p.1 then 1 else 0) *
            (zetaBoundaryWeight x n * Real.cos (logFrequency n * (q.2 + p.2))))|
        ≤ |𝒟 p| / 2 * (zetaBoundaryWeight x n + zetaBoundaryWeight x n) := by
          rw [abs_mul, abs_div, abs_two]
          refine mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans (add_le_add ?_ ?_))
            (by positivity)
          · rw [abs_mul]
            exact (mul_le_mul hi1 hz1 (abs_nonneg _) zero_le_one).trans (by rw [one_mul])
          · rw [abs_mul]
            exact (mul_le_mul hi2 hz2 (abs_nonneg _) zero_le_one).trans (by rw [one_mul])
      _ = zetaBoundaryWeight x n * |𝒟 p| := by ring
  have hcol : ∀ p, ∑' n, f n p = 𝒟 p / 2 * ((if q.1 = p.1 then 1 else 0) *
        cosineTrace (zetaBoundaryWeight x) logFrequency (q.2 - p.2) +
      (if q.1 = -p.1 then 1 else 0) *
        cosineTrace (zetaBoundaryWeight x) logFrequency (q.2 + p.2)) := fun p => by
    have hA := summable_cosineTrace_terms hz0 hz logFrequency (q.2 - p.2)
    have hB := summable_cosineTrace_terms hz0 hz logFrequency (q.2 + p.2)
    unfold cosineTrace
    rw [← tsum_mul_left, ← tsum_mul_left, ← Summable.tsum_add (hA.mul_left _) (hB.mul_left _),
      ← tsum_mul_left]
  unfold jointTrace
  rw [hsw.tsum_prod]
  calc ∑' n, ∑' ψ : AddChar G ℂ, familyWeight 𝒟 x (n, ψ) * jointMode ψ (logFrequency n) q
      = ∑' n, ∑' p, f n p := tsum_congr hinner
    _ = ∑' p, ∑' n, f n p := hf.tsum_comm.symm
    _ = _ := tsum_congr hcol

/-- **Realization.** -/
theorem familyWeight_isJointBoundaryDivisor {𝒟 : G × ℝ → ℝ} (h𝒟 : IsEvenPosDef 𝒟)
    (hs : Summable 𝒟) :
    IsJointBoundaryDivisor Prod.snd (fun r : ℕ × AddChar G ℂ => logFrequency r.1)
      (familyWeight 𝒟) 𝒟 where
  nonneg x _ r := mul_nonneg (zetaBoundaryWeight_nonneg x r.1)
    (div_nonneg (familyBohr_nonneg h𝒟 hs _ _) (Nat.cast_nonneg _))
  summable x hx := by
    have hG0 : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
    refine Summable.of_nonneg_of_le (fun r => mul_nonneg (zetaBoundaryWeight_nonneg x r.1)
      (div_nonneg (familyBohr_nonneg h𝒟 hs _ _) (Nat.cast_nonneg _))) (fun r => ?_)
      (f := fun r : ℕ × AddChar G ℂ => zetaBoundaryWeight x r.1 * ∑' p, |𝒟 p|) ?_
    · unfold familyWeight
      refine mul_le_mul_of_nonneg_left ?_ (zetaBoundaryWeight_nonneg x r.1)
      rw [div_le_iff₀ hG0]
      exact (le_abs_self _).trans ((abs_familyBohr_le hs _ _).trans (le_mul_of_one_le_right
        (tsum_nonneg fun p => abs_nonneg _) (by exact_mod_cast Fintype.card_pos)))
    · exact (summable_prod_of_nonneg fun r => mul_nonneg (zetaBoundaryWeight_nonneg x r.1)
        (tsum_nonneg fun p => abs_nonneg _)).mpr ⟨fun _ => Summable.of_finite, by
          simpa [tsum_fintype] using ((summable_zetaBoundaryWeight hx).mul_right
            (∑' p, |𝒟 p|)).mul_left (Fintype.card (AddChar G ℂ) : ℝ)⟩
  tendsto q := by
    have hz : ∀ v, Tendsto (fun x => x * cosineTrace (zetaBoundaryWeight x) logFrequency v)
        (𝓝[>] 0) (𝓝 (diracAt v)) := fun v => by
      have := zeta_isBoundaryDivisor.tendsto v
      rwa [zetaBoundaryDivisor_eq] at this
    have hev : ∀ᶠ x in 𝓝[>] (0 : ℝ),
        0 < x ∧ x * cosineTrace (zetaBoundaryWeight x) logFrequency 0 ≤ 2 :=
      (eventually_mem_nhdsWithin.mono fun x (hx : x ∈ Set.Ioi (0 : ℝ)) => (hx : 0 < x)).and
        ((hz 0).eventually (ge_mem_nhds (by simp [diracAt])))
    have hbd : ∀ x, 0 < x → x * cosineTrace (zetaBoundaryWeight x) logFrequency 0 ≤ 2 →
        ∀ v, |x * cosineTrace (zetaBoundaryWeight x) logFrequency v| ≤ 2 := by
      intro x hx h2 v
      have hz0 := zetaBoundaryWeight_nonneg x
      have hzs := summable_zetaBoundaryWeight hx
      have hle : |cosineTrace (zetaBoundaryWeight x) logFrequency v| ≤
          cosineTrace (zetaBoundaryWeight x) logFrequency 0 := by
        unfold cosineTrace
        simp only [mul_zero, Real.cos_zero, mul_one]
        have ht := summable_cosineTrace_terms hz0 hzs logFrequency v
        rw [← Real.norm_eq_abs]
        refine (norm_tsum_le_tsum_norm ht.norm).trans (Summable.tsum_le_tsum (fun n => ?_)
          ht.norm hzs)
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hz0 n)]
        exact mul_le_of_le_one_right (hz0 n) (Real.abs_cos_le_one _)
      rw [abs_mul, abs_of_pos hx]
      exact (mul_le_mul_of_nonneg_left hle hx.le).trans h2
    have hT := tendsto_tsum_of_dominated_convergence (𝓕 := 𝓝[>] (0 : ℝ))
      (f := fun x p => 𝒟 p / 2 * ((if q.1 = p.1 then 1 else 0) *
          (x * cosineTrace (zetaBoundaryWeight x) logFrequency (q.2 - p.2)) +
        (if q.1 = -p.1 then 1 else 0) *
          (x * cosineTrace (zetaBoundaryWeight x) logFrequency (q.2 + p.2))))
      (g := fun p => 𝒟 p / 2 * ((if q.1 = p.1 then 1 else 0) * diracAt (q.2 - p.2) +
        (if q.1 = -p.1 then 1 else 0) * diracAt (q.2 + p.2)))
      (bound := fun p => 2 * |𝒟 p|) (hs.abs.mul_left 2)
      (fun p => (((hz _).const_mul _).add ((hz _).const_mul _)).const_mul _)
      (hev.mono fun x hx p => by
        rw [Real.norm_eq_abs, abs_mul, abs_div, abs_two]
        have hi1 : |(if q.1 = p.1 then (1 : ℝ) else 0)| ≤ 1 := by split_ifs <;> simp
        have hi2 : |(if q.1 = -p.1 then (1 : ℝ) else 0)| ≤ 1 := by split_ifs <;> simp
        have h1 := hbd x hx.1 hx.2 (q.2 - p.2)
        have h2 := hbd x hx.1 hx.2 (q.2 + p.2)
        have : |(if q.1 = p.1 then 1 else 0) *
              (x * cosineTrace (zetaBoundaryWeight x) logFrequency (q.2 - p.2)) +
            (if q.1 = -p.1 then 1 else 0) *
              (x * cosineTrace (zetaBoundaryWeight x) logFrequency (q.2 + p.2))| ≤ 4 := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul (if q.1 = p.1 then (1 : ℝ) else 0), abs_mul (if q.1 = -p.1 then (1 : ℝ) else 0)]
          have := mul_le_mul hi1 h1 (abs_nonneg _) zero_le_one
          have := mul_le_mul hi2 h2 (abs_nonneg _) zero_le_one
          linarith
        calc |𝒟 p| / 2 * |(if q.1 = p.1 then 1 else 0) *
              (x * cosineTrace (zetaBoundaryWeight x) logFrequency (q.2 - p.2)) +
            (if q.1 = -p.1 then 1 else 0) *
              (x * cosineTrace (zetaBoundaryWeight x) logFrequency (q.2 + p.2))|
            ≤ |𝒟 p| / 2 * 4 := mul_le_mul_of_nonneg_left this (by positivity)
          _ = 2 * |𝒟 p| := by ring)
    -- The limit is `𝒟(q)`: the two halves are `𝒟(q)` and `𝒟(−q)`.
    have hpt : ∀ p : G × ℝ, (if q.1 = p.1 then (1 : ℝ) else 0) * diracAt (q.2 - p.2) =
        if p = q then 1 else 0 := fun p => by
      unfold diracAt
      by_cases h : p = q
      · subst h; simp
      · rw [if_neg h]
        by_cases h1 : q.1 = p.1
        · rw [if_pos h1, if_neg (fun h2 => h (Prod.ext h1.symm (by linarith [sub_eq_zero.mp h2]))),
            mul_zero]
        · rw [if_neg h1, zero_mul]
    have hmt : ∀ p : G × ℝ, (if q.1 = -p.1 then (1 : ℝ) else 0) * diracAt (q.2 + p.2) =
        if p = -q then 1 else 0 := fun p => by
      unfold diracAt
      by_cases h : p = -q
      · subst h; simp
      · rw [if_neg h]
        by_cases h1 : q.1 = -p.1
        · rw [if_pos h1, if_neg (fun h2 => h (Prod.ext (by rw [Prod.fst_neg, h1, neg_neg])
            (by simp only [Prod.snd_neg]; linarith [add_eq_zero_iff_eq_neg.mp h2]))), mul_zero]
        · rw [if_neg h1, zero_mul]
    have hlimval : ∑' p, 𝒟 p / 2 * ((if q.1 = p.1 then 1 else 0) * diracAt (q.2 - p.2) +
        (if q.1 = -p.1 then 1 else 0) * diracAt (q.2 + p.2)) = 𝒟 q := by
      simp only [hpt, hmt]
      rw [show (fun p => 𝒟 p / 2 * ((if p = q then (1 : ℝ) else 0) + if p = -q then 1 else 0)) =
          fun p => (if p = q then 𝒟 p / 2 else 0) + (if p = -q then 𝒟 p / 2 else 0) from
        funext fun p => by split_ifs <;> ring,
        Summable.tsum_add (summable_of_ne_finset_zero (s := {q}) fun p hp => by
          rw [Finset.mem_singleton] at hp; rw [if_neg hp])
          (summable_of_ne_finset_zero (s := {-q}) fun p hp => by
          rw [Finset.mem_singleton] at hp; rw [if_neg hp]),
        tsum_ite_eq, tsum_ite_eq, h𝒟.even]
      ring
    rw [hlimval] at hT
    refine hT.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    rw [jointTrace_familyWeight h𝒟 hs hx q, ← tsum_mul_left]
    exact tsum_congr fun p => by ring

/-- **Bochner's theorem for families.** An absolutely summable configuration on `G × ℝ` is a joint
boundary divisor iff it is even and positive definite. -/
theorem family_summable_bochner {𝒟 : G × ℝ → ℝ} (hs : Summable 𝒟) :
    (∃ (ι : Type u) (ψ : ι → AddChar G ℂ) (lam : ι → ℝ) (w : ℝ → ι → ℝ),
        IsJointBoundaryDivisor ψ lam w 𝒟) ↔ IsEvenPosDef 𝒟 :=
  ⟨fun ⟨_, _, _, _, hw⟩ => hw.isEvenPosDef, fun h𝒟 =>
    ⟨_, _, _, _, familyWeight_isJointBoundaryDivisor h𝒟 hs⟩⟩

end GaloisForLFunctions.MultiplicativePositivityGeometry
