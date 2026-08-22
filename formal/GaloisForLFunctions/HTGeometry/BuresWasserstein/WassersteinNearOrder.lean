import GaloisForLFunctions.HTGeometry.BuresWasserstein.KantorovichConverse
import GaloisForLFunctions.HTGeometry.BuresWasserstein.WassersteinDual

/-!
# Two-sided near-order comparison of the Wasserstein mean and its dual

Kim–Mer–Pálfia (arXiv:2607.29142), Theorem 6.17: if every `Aᵢ` lies in the Loewner interval
`[m, M]` with `0 < m ≤ M`, then the Wasserstein barycentre `P` and the dual barycentre `D` satisfy

`κ⁻⁴ P ⪯ D ⪯ (2κ - 1)² P`,   `κ = max {(1+M²)/(2M), (1+m²)/(2m)}`.

The mechanism is joint operator concavity of the geometric mean combined with the Kantorovich
converse `a ∇ b ≤ κ (a # b)` of Lemma 6.16, applied both to the pair `(D, P⁻¹)` and to the
self-inverse pairs `(Aᵢ⁻¹, Aᵢ)` whose geometric mean is the identity.
-/

open scoped NNReal Ring

namespace GaloisForLFunctions.HTGeometry.BuresWasserstein

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {ι : Type*} {s : Finset ι} {w : ι → ℝ} {Av : ι → A} {P D : A}

/-- The Kantorovich constant of the interval `[m, M]` used in Theorem 6.17. -/
noncomputable def wassKappa (m M : ℝ) : ℝ := max (kantorovich (M * M)) (kantorovich (m * m))

lemma one_le_kantorovich {h : ℝ} (hh : 0 < h) : 1 ≤ kantorovich h := by
  have hs : 0 < Real.sqrt h := Real.sqrt_pos.mpr hh
  have hsq : Real.sqrt h * Real.sqrt h = h := Real.mul_self_sqrt hh.le
  unfold kantorovich
  rw [le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg (Real.sqrt h - 1)]

lemma one_le_wassKappa {m M : ℝ} (hm : 0 < m) : 1 ≤ wassKappa m M :=
  le_trans (one_le_kantorovich (mul_pos hm hm)) (le_max_right _ _)

lemma wassKappa_pos {m M : ℝ} (hm : 0 < m) : 0 < wassKappa m M :=
  lt_of_lt_of_le zero_lt_one (one_le_wassKappa hm)

/-- The Kantorovich constant of `[m, M]` bounds the constant produced by Lemma 6.16 for a pair
confined to `[m, M]` and `[M⁻¹, m⁻¹]`. -/
lemma kappa_eq_max {m M : ℝ} (hm : 0 < m) :
    max (kantorovich (M / M⁻¹)) (kantorovich (m⁻¹ / m)) = wassKappa m M := by
  unfold wassKappa
  rw [show M / M⁻¹ = M * M by rw [div_eq_mul_inv, inv_inv],
    show m⁻¹ / m = (m * m)⁻¹ by rw [div_eq_mul_inv, ← mul_inv],
    kantorovich_inv (mul_pos hm hm)]

/-- Order bounds transfer to inverses. -/
lemma mem_Icc_ringInverse {a : A} (ha : IsStrictlyPositive a) {m M : ℝ} (hm : 0 < m) (hM : 0 < M)
    (h1 : m • (1 : A) ≤ a) (h2 : a ≤ M • (1 : A)) :
    M⁻¹ • (1 : A) ≤ a⁻¹ʳ ∧ a⁻¹ʳ ≤ m⁻¹ • (1 : A) :=
  ⟨smul_one_le_ringInverse_of_le_smul_one ha hM h2, ringInverse_le_of_smul_one_le hm h1⟩

/-- Order bounds on the inverse transfer back. -/
lemma mem_Icc_of_ringInverse {a : A} (ha : IsStrictlyPositive a) {m M : ℝ} (hm : 0 < m)
    (hM : 0 < M) (h1 : M⁻¹ • (1 : A) ≤ a⁻¹ʳ) (h2 : a⁻¹ʳ ≤ m⁻¹ • (1 : A)) :
    m • (1 : A) ≤ a ∧ a ≤ M • (1 : A) := by
  constructor
  · have hc := CStarAlgebra.ringInverse_le_ringInverse h2 ha.ringInverse
    rwa [Ring.inverse_inverse ha.isUnit,
      ringInverse_smul (inv_pos.mpr hm) (isStrictlyPositive_one (A := A)),
      Ring.inverse_one, inv_inv] at hc
  · have hc := CStarAlgebra.ringInverse_le_ringInverse h1
      (IsStrictlyPositive.smul (inv_pos.mpr hM) isStrictlyPositive_one)
    rwa [Ring.inverse_inverse ha.isUnit,
      ringInverse_smul (inv_pos.mpr hM) (isStrictlyPositive_one (A := A)),
      Ring.inverse_one, inv_inv] at hc

/-! ### The core two-sided estimate on `D # P⁻¹` -/

variable {m M : ℝ}

/-- The geometric mean of the dual barycentre and the inverse primal barycentre is squeezed
between `κ⁻²` and `2κ - 1`. -/
theorem gm_dual_primalInv_bounds (hm : 0 < m) (hM : 0 < M)
    (hw : ∀ i ∈ s, 0 < w i) (hsum : ∑ i ∈ s, w i = 1)
    (hA : ∀ i ∈ s, IsStrictlyPositive (Av i))
    (hlo : ∀ i ∈ s, m • (1 : A) ≤ Av i) (hhi : ∀ i ∈ s, Av i ≤ M • (1 : A))
    (hP : IsWassersteinPoint s w Av P) (hD : IsDualWassersteinPoint s w Av D) :
    ((wassKappa m M)⁻¹ * (wassKappa m M)⁻¹) • (1 : A) ≤ gm D P⁻¹ʳ ∧
      gm D P⁻¹ʳ ≤ (2 * wassKappa m M - 1) • (1 : A) := by
  classical
  set κ := wassKappa m M with hκdef
  have hκ1 : (1 : ℝ) ≤ κ := one_le_wassKappa hm
  have hκ0 : (0 : ℝ) < κ := lt_of_lt_of_le zero_lt_one hκ1
  have hPpos : IsStrictlyPositive P := hP.1
  have hDpos : IsStrictlyPositive D := hD.1
  have hsne : s.Nonempty := by
    rcases Finset.eq_empty_or_nonempty s with rfl | h
    · simp at hsum
    · exact h
  obtain ⟨hPlo, hPhi⟩ := hP.mem_Icc hm hM hsum hw hA hlo hhi
  obtain ⟨hPinvlo, hPinvhi⟩ := mem_Icc_ringInverse hPpos hm hM hPlo hPhi
  have hAinv : ∀ i ∈ s, IsStrictlyPositive ((Av i)⁻¹ʳ) := fun i hi => (hA i hi).ringInverse
  have hAinvlo : ∀ i ∈ s, M⁻¹ • (1 : A) ≤ (Av i)⁻¹ʳ := fun i hi =>
    (mem_Icc_ringInverse (hA i hi) hm hM (hlo i hi) (hhi i hi)).1
  have hAinvhi : ∀ i ∈ s, (Av i)⁻¹ʳ ≤ m⁻¹ • (1 : A) := fun i hi =>
    (mem_Icc_ringInverse (hA i hi) hm hM (hlo i hi) (hhi i hi)).2
  have hD' : IsWassersteinPoint s w (fun i => (Av i)⁻¹ʳ) D⁻¹ʳ :=
    (isDualWassersteinPoint_iff hDpos hA).mp hD
  obtain ⟨hDinvlo, hDinvhi⟩ :=
    hD'.mem_Icc (inv_pos.mpr hM) (inv_pos.mpr hm) hsum hw hAinv hAinvlo hAinvhi
  obtain ⟨hDlo, hDhi⟩ := mem_Icc_of_ringInverse hDpos hm hM hDinvlo hDinvhi
  -- the two defining equations
  have hEq1 : ∑ i ∈ s, w i • gm D ((Av i)⁻¹ʳ) = 1 := hD.2
  have hEq2 : ∑ i ∈ s, w i • gm P⁻¹ʳ (Av i) = 1 := by
    rw [← hP.2]
    exact Finset.sum_congr rfl fun i hi => by rw [gm_comm hPpos.ringInverse (hA i hi)]
  -- Kantorovich for the pair `(D, P⁻¹)` and for the self-inverse pairs
  have hkantDP : (2 : ℝ)⁻¹ • (D + P⁻¹ʳ) ≤ κ • gm D P⁻¹ʳ := by
    have hk := arith_le_smul_gm hDpos hPpos.ringInverse hm hM (inv_pos.mpr hM) (inv_pos.mpr hm)
      hDlo hDhi hPinvlo hPinvhi
    rwa [kappa_eq_max hm] at hk
  have hgmself : ∀ i ∈ s, gm ((Av i)⁻¹ʳ) (Av i) = 1 := fun i hi => by
    rw [gm_comm (hA i hi).ringInverse (hA i hi)]
    exact gm_ringInverse_self (hA i hi)
  have hkantAi : ∀ i ∈ s, (2 : ℝ)⁻¹ • ((Av i)⁻¹ʳ + Av i) ≤ κ • (1 : A) := by
    intro i hi
    have hk := arith_le_smul_gm (hA i hi).ringInverse (hA i hi) (inv_pos.mpr hM) (inv_pos.mpr hm)
      hm hM (hAinvlo i hi) (hAinvhi i hi) (hlo i hi) (hhi i hi)
    rwa [max_comm, kappa_eq_max hm, hgmself i hi] at hk
  refine ⟨?_, ?_⟩
  · -- lower bound
    have hstep : ∀ i ∈ s, (2 : ℝ)⁻¹ • gm D ((Av i)⁻¹ʳ) + (2 : ℝ)⁻¹ • gm P⁻¹ʳ (Av i)
        ≤ κ • CFC.sqrt (gm D P⁻¹ʳ) := by
      intro i hi
      have hmid := gm_midpoint_concave hDpos hPpos.ringInverse (hA i hi).ringInverse (hA i hi)
      refine hmid.trans ?_
      have hmono := gm_mono
        (a := (2 : ℝ)⁻¹ • D + (2 : ℝ)⁻¹ • P⁻¹ʳ)
        (c := κ • gm D P⁻¹ʳ)
        (b := (2 : ℝ)⁻¹ • (Av i)⁻¹ʳ + (2 : ℝ)⁻¹ • Av i)
        (d := κ • (1 : A))
        (by
          rw [← smul_add]
          exact IsStrictlyPositive.smul (by norm_num)
            (hDpos.add_nonneg hPpos.ringInverse.nonneg))
        ((gm_strictlyPositive hDpos hPpos.ringInverse).smul hκ0)
        (by
          rw [← smul_add]
          exact IsStrictlyPositive.smul (by norm_num)
            ((hA i hi).ringInverse.add_nonneg (hA i hi).nonneg))
        (by rw [← smul_add]; exact hkantDP)
        (by rw [← smul_add]; exact hkantAi i hi)
      refine hmono.trans (le_of_eq ?_)
      rw [gm_smul_self hκ0 (gm_strictlyPositive hDpos hPpos.ringInverse) isStrictlyPositive_one,
        gm_one_right (gm_strictlyPositive hDpos hPpos.ringInverse)]
    have hone : (1 : A) ≤ κ • CFC.sqrt (gm D P⁻¹ʳ) := by
      have hlhs : ∑ i ∈ s, w i • ((2 : ℝ)⁻¹ • gm D ((Av i)⁻¹ʳ)
          + (2 : ℝ)⁻¹ • gm P⁻¹ʳ (Av i)) = 1 := by
        have hsplit : ∀ i ∈ s, w i • ((2 : ℝ)⁻¹ • gm D ((Av i)⁻¹ʳ)
            + (2 : ℝ)⁻¹ • gm P⁻¹ʳ (Av i))
            = (2 : ℝ)⁻¹ • (w i • gm D ((Av i)⁻¹ʳ)) + (2 : ℝ)⁻¹ • (w i • gm P⁻¹ʳ (Av i)) :=
          fun i _ => by rw [smul_add, smul_comm, smul_comm (w i) ((2 : ℝ)⁻¹)]
        rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, ← Finset.smul_sum,
          ← Finset.smul_sum, hEq1, hEq2, ← add_smul]
        norm_num
      have hrhs : ∑ i ∈ s, w i • (κ • CFC.sqrt (gm D P⁻¹ʳ)) = κ • CFC.sqrt (gm D P⁻¹ʳ) := by
        rw [← Finset.sum_smul, hsum, one_smul]
      rw [← hlhs, ← hrhs]
      exact Finset.sum_le_sum fun i hi =>
        smul_le_smul_of_nonneg_left (hstep i hi) (hw i hi).le
    have h1 : κ⁻¹ • (1 : A) ≤ CFC.sqrt (gm D P⁻¹ʳ) := by
      have h2 := smul_le_smul_of_nonneg_left hone (inv_pos.mpr hκ0).le
      rwa [smul_smul, inv_mul_cancel₀ hκ0.ne', one_smul] at h2
    have h3 := smul_one_le_mul_self_of_le (CFC.sqrt_nonneg (gm D P⁻¹ʳ))
      (inv_pos.mpr hκ0).le h1
    rwa [CFC.sqrt_mul_sqrt_self _ (gm_nonneg _ _)] at h3
  · -- upper bound
    have hrev : ∀ {x y : A}, (2 : ℝ)⁻¹ • (x + y) ≤ κ • gm x y →
        κ⁻¹ • ((2 : ℝ)⁻¹ • x + (2 : ℝ)⁻¹ • y) ≤ gm x y := by
      intro x y h
      rw [← smul_add]
      have h2 := smul_le_smul_of_nonneg_left h (inv_pos.mpr hκ0).le
      rwa [show κ⁻¹ • κ • gm x y = gm x y by
        rw [smul_smul, inv_mul_cancel₀ hκ0.ne', one_smul]] at h2
    have hstep : ∀ i ∈ s, κ⁻¹ • ((2 : ℝ)⁻¹ • gm D P⁻¹ʳ + (2 : ℝ)⁻¹ • (1 : A))
        ≤ gm (gm D ((Av i)⁻¹ʳ)) (gm P⁻¹ʳ (Av i)) := by
      intro i hi
      have hpos1 : IsStrictlyPositive ((2 : ℝ)⁻¹ • D + (2 : ℝ)⁻¹ • (Av i)⁻¹ʳ) := by
        rw [← smul_add]
        exact IsStrictlyPositive.smul (by norm_num)
          (hDpos.add_nonneg (hA i hi).ringInverse.nonneg)
      have hpos2 : IsStrictlyPositive ((2 : ℝ)⁻¹ • P⁻¹ʳ + (2 : ℝ)⁻¹ • Av i) := by
        rw [← smul_add]
        exact IsStrictlyPositive.smul (by norm_num)
          (hPpos.ringInverse.add_nonneg (hA i hi).nonneg)
      have hmid := gm_midpoint_concave hDpos (hA i hi).ringInverse hPpos.ringInverse (hA i hi)
      have hmid' : (2 : ℝ)⁻¹ • gm D P⁻¹ʳ + (2 : ℝ)⁻¹ • (1 : A)
          ≤ gm ((2 : ℝ)⁻¹ • D + (2 : ℝ)⁻¹ • (Av i)⁻¹ʳ)
            ((2 : ℝ)⁻¹ • P⁻¹ʳ + (2 : ℝ)⁻¹ • Av i) := by
        rw [← hgmself i hi]; exact hmid
      have hsc := smul_le_smul_of_nonneg_left hmid' (inv_pos.mpr hκ0).le
      refine hsc.trans (le_of_eq (gm_smul_self (inv_pos.mpr hκ0) hpos1 hpos2).symm) |>.trans ?_
      refine gm_mono (hpos1.smul (inv_pos.mpr hκ0))
        (gm_strictlyPositive hDpos (hA i hi).ringInverse) (hpos2.smul (inv_pos.mpr hκ0))
        (hrev ?_) (hrev ?_)
      · have hk := arith_le_smul_gm hDpos (hA i hi).ringInverse hm hM (inv_pos.mpr hM)
          (inv_pos.mpr hm) hDlo hDhi (hAinvlo i hi) (hAinvhi i hi)
        rwa [kappa_eq_max hm] at hk
      · have hk := arith_le_smul_gm hPpos.ringInverse (hA i hi) (inv_pos.mpr hM) (inv_pos.mpr hm)
          hm hM hPinvlo hPinvhi (hlo i hi) (hhi i hi)
        rwa [max_comm, kappa_eq_max hm] at hk
    have hupper : κ⁻¹ • ((2 : ℝ)⁻¹ • gm D P⁻¹ʳ + (2 : ℝ)⁻¹ • (1 : A)) ≤ 1 := by
      have hlhs : ∑ i ∈ s, w i • (κ⁻¹ • ((2 : ℝ)⁻¹ • gm D P⁻¹ʳ + (2 : ℝ)⁻¹ • (1 : A)))
          = κ⁻¹ • ((2 : ℝ)⁻¹ • gm D P⁻¹ʳ + (2 : ℝ)⁻¹ • (1 : A)) := by
        rw [← Finset.sum_smul, hsum, one_smul]
      have hconc := gm_concave (s := s) (w := w) (f := fun i => gm D ((Av i)⁻¹ʳ))
        (g := fun i => gm P⁻¹ʳ (Av i)) hsne hw
        (fun i hi => gm_strictlyPositive hDpos (hA i hi).ringInverse)
        (fun i hi => gm_strictlyPositive hPpos.ringInverse (hA i hi))
      rw [hEq1, hEq2, gm_one_left, CFC.sqrt_one] at hconc
      rw [← hlhs]
      exact le_trans (Finset.sum_le_sum fun i hi =>
        smul_le_smul_of_nonneg_left (hstep i hi) (hw i hi).le) hconc
    have hfin := smul_le_smul_of_nonneg_left hupper (by positivity : (0:ℝ) ≤ 2 * κ)
    rw [show (2 * κ) • (κ⁻¹ • ((2 : ℝ)⁻¹ • gm D P⁻¹ʳ + (2 : ℝ)⁻¹ • (1 : A)))
        = gm D P⁻¹ʳ + 1 by
      rw [smul_smul, smul_add, smul_smul, smul_smul,
        show 2 * κ * κ⁻¹ * (2 : ℝ)⁻¹ = 1 by field_simp, one_smul, one_smul]] at hfin
    refine le_trans (le_sub_iff_add_le.mpr hfin) (le_of_eq ?_)
    rw [sub_smul, one_smul]

/-! ### Theorem 6.17 -/

/-- **Theorem 6.17, lower half**: `κ⁻⁴ P ⪯ D`. -/
theorem nearLE_smul_primal_dual (hm : 0 < m) (hM : 0 < M)
    (hw : ∀ i ∈ s, 0 < w i) (hsum : ∑ i ∈ s, w i = 1)
    (hA : ∀ i ∈ s, IsStrictlyPositive (Av i))
    (hlo : ∀ i ∈ s, m • (1 : A) ≤ Av i) (hhi : ∀ i ∈ s, Av i ≤ M • (1 : A))
    (hP : IsWassersteinPoint s w Av P) (hD : IsDualWassersteinPoint s w Av D) :
    NearLE ((wassKappa m M * wassKappa m M * (wassKappa m M * wassKappa m M))⁻¹ • P) D := by
  set κ := wassKappa m M with hκdef
  have hκ0 : (0 : ℝ) < κ := wassKappa_pos hm
  have hPpos : IsStrictlyPositive P := hP.1
  have hDpos : IsStrictlyPositive D := hD.1
  obtain ⟨hlow, -⟩ := gm_dual_primalInv_bounds hm hM hw hsum hA hlo hhi hP hD
  unfold NearLE
  rw [ringInverse_smul (by positivity) hPpos, inv_inv,
    gm_smul_left (by positivity) hPpos.ringInverse hDpos,
    Real.sqrt_mul_self (by positivity), gm_comm hPpos.ringInverse hDpos]
  have hscale := smul_le_smul_of_nonneg_left hlow (by positivity : (0:ℝ) ≤ κ * κ)
  rwa [smul_smul, show κ * κ * (κ⁻¹ * κ⁻¹) = 1 by field_simp, one_smul] at hscale

/-- **Theorem 6.17, upper half**: `D ⪯ (2κ - 1)² P`. -/
theorem nearLE_dual_smul_primal (hm : 0 < m) (hM : 0 < M)
    (hw : ∀ i ∈ s, 0 < w i) (hsum : ∑ i ∈ s, w i = 1)
    (hA : ∀ i ∈ s, IsStrictlyPositive (Av i))
    (hlo : ∀ i ∈ s, m • (1 : A) ≤ Av i) (hhi : ∀ i ∈ s, Av i ≤ M • (1 : A))
    (hP : IsWassersteinPoint s w Av P) (hD : IsDualWassersteinPoint s w Av D) :
    NearLE D (((2 * wassKappa m M - 1) * (2 * wassKappa m M - 1)) • P) := by
  set κ := wassKappa m M with hκdef
  have hκ1 : (1 : ℝ) ≤ κ := one_le_wassKappa hm
  have hν : (0 : ℝ) < 2 * κ - 1 := by linarith
  have hPpos : IsStrictlyPositive P := hP.1
  have hDpos : IsStrictlyPositive D := hD.1
  obtain ⟨-, hup⟩ := gm_dual_primalInv_bounds hm hM hw hsum hA hlo hhi hP hD
  have hbpos : IsStrictlyPositive (((2 * κ - 1) * (2 * κ - 1))⁻¹ • P⁻¹ʳ) :=
    hPpos.ringInverse.smul (by positivity)
  have hdual := gm_ringInverse hDpos hbpos
  rw [ringInverse_smul (by positivity) hPpos.ringInverse, inv_inv,
    Ring.inverse_inverse hPpos.isUnit] at hdual
  have hval : gm D (((2 * κ - 1) * (2 * κ - 1))⁻¹ • P⁻¹ʳ)
      = (2 * κ - 1)⁻¹ • gm D P⁻¹ʳ := by
    rw [gm_smul_right (by positivity) hDpos hPpos.ringInverse, Real.sqrt_inv,
      Real.sqrt_mul_self hν.le]
  rw [hval] at hdual
  have hle : (2 * κ - 1)⁻¹ • gm D P⁻¹ʳ ≤ 1 := by
    have h2 := smul_le_smul_of_nonneg_left hup (inv_pos.mpr hν).le
    rwa [smul_smul, inv_mul_cancel₀ hν.ne', one_smul] at h2
  have hpos : IsStrictlyPositive ((2 * κ - 1)⁻¹ • gm D P⁻¹ʳ) :=
    (gm_strictlyPositive hDpos hPpos.ringInverse).smul (inv_pos.mpr hν)
  unfold NearLE
  rw [← hdual]
  have hcmp := CStarAlgebra.ringInverse_le_ringInverse hle hpos
  rwa [Ring.inverse_one] at hcmp

end

end GaloisForLFunctions.HTGeometry.BuresWasserstein
