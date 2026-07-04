/-
# Böttcher tower — Brolin: arbitrary-target finite measures and shifted limits

This module is part of the split Brolin/Riesz-measure interface. Import
`GaloisForLFunctions.Bottcher.Brolin` for the full public surface.
-/
import GaloisForLFunctions.Bottcher.Brolin.FiniteLimits

open Filter Topology MeasureTheory CompactlySupported Laplacian
open scoped Laplacian

namespace Bottcher

local instance : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

/-- The finite normalized pullback of an arbitrary target point `a` under `f_c^[n]`. -/
noncomputable def preBrolinMeasureAt (c a : ℂ) (n : ℕ) : Measure ℂ :=
  ((2 ^ n : ENNReal)⁻¹) •
    rootCountingMeasure ((quadraticPolyIterate c n - Polynomial.C a).roots)

/-- Integrating against a finite normalized arbitrary-target pre-Brolin measure
is the normalized average over the level-`n` pullback multiset. -/
theorem integral_preBrolinMeasureAt_eq_root_average
    (c a : ℂ) (n : ℕ) (f : ℂ → ℝ) :
    ∫ z, f z ∂preBrolinMeasureAt c a n =
      (2 ^ n : ℝ)⁻¹ *
        (((quadraticPolyIterate c n - Polynomial.C a).roots.map f).sum) := by
  rw [preBrolinMeasureAt, integral_smul_measure, integral_rootCountingMeasure]
  simp [ENNReal.toReal_inv, ENNReal.toReal_pow]

/-- The arbitrary-target finite pre-Brolin potential is the normalized root
log-kernel sum. -/
theorem logPotential_preBrolinMeasureAt_eq_scaled_rootLogKernelSum
    (c a z : ℂ) (n : ℕ) :
    logPotential (preBrolinMeasureAt c a n) z =
      (2 ^ n : ℝ)⁻¹ *
        (((quadraticPolyIterate c n - Polynomial.C a).roots.map
          (fun r => logKernel z r)).sum) := by
  rw [preBrolinMeasureAt, logPotential_smul, logPotential_rootCountingMeasure]
  simp [ENNReal.toReal_inv, ENNReal.toReal_pow]

/-- `f_c^[n](X) - a` is monic. -/
theorem quadraticPolyIterate_sub_C_monic (c a : ℂ) (n : ℕ) :
    (quadraticPolyIterate c n - Polynomial.C a).Monic := by
  refine (quadraticPolyIterate_monic c n).sub_of_left ?_
  have hpos : 0 < (quadraticPolyIterate c n).degree := by
    rw [← Polynomial.natDegree_pos_iff_degree_pos, quadraticPolyIterate_natDegree]
    positivity
  exact lt_of_le_of_lt Polynomial.degree_C_le hpos

/-- The arbitrary-target finite pre-Brolin potential is the normalized negative
root-log sum. -/
theorem logPotential_preBrolinMeasureAt_eq_neg_rootLogSum (c a z : ℂ) (n : ℕ) :
    logPotential (preBrolinMeasureAt c a n) z =
      - (2 ^ n : ℝ)⁻¹ *
        ((quadraticPolyIterate c n - Polynomial.C a).roots.map
          (fun r => Real.log ‖z - r‖)).sum := by
  rw [preBrolinMeasureAt, logPotential_smul, logPotential_rootCountingMeasure]
  have hscale : (((2 ^ n : ENNReal)⁻¹).toReal) = (2 ^ n : ℝ)⁻¹ := by
    simp [ENNReal.toReal_inv, ENNReal.toReal_pow]
  have hkernel :
      (((quadraticPolyIterate c n - Polynomial.C a).roots.map
          (fun ζ => logKernel z ζ)).sum) =
        - (((quadraticPolyIterate c n - Polynomial.C a).roots.map
          (fun ζ => Real.log ‖z - ζ‖)).sum) := by
    simp [logKernel]
  rw [hscale, hkernel]
  ring

/-- Finite arbitrary-target Brolin potential identity away from the atoms:
`-U^{μ_{c,a,n}}(z) = 2⁻ⁿ log ‖f_c^[n](z) - a‖`. -/
theorem neg_logPotential_preBrolinMeasureAt_eq_log_norm {c a z : ℂ} {n : ℕ}
    (hz : (quadratic c)^[n] z - a ≠ 0) :
    - logPotential (preBrolinMeasureAt c a n) z =
      (2 ^ n : ℝ)⁻¹ * Real.log ‖(quadratic c)^[n] z - a‖ := by
  have hzeval : (quadraticPolyIterate c n - Polynomial.C a).eval z ≠ 0 := by
    simpa [Polynomial.eval_sub, quadraticPolyIterate_eval] using hz
  have hroots := rootLogSum_eq_log_eval_of_monic
    (quadraticPolyIterate_sub_C_monic c a n) (z := z) hzeval
  calc
    - logPotential (preBrolinMeasureAt c a n) z
        = (2 ^ n : ℝ)⁻¹ *
            ((quadraticPolyIterate c n - Polynomial.C a).roots.map
              (fun r => Real.log ‖z - r‖)).sum := by
          rw [logPotential_preBrolinMeasureAt_eq_neg_rootLogSum]
          ring
    _ = (2 ^ n : ℝ)⁻¹ *
          Real.log ‖(quadraticPolyIterate c n - Polynomial.C a).eval z‖ := by
          rw [hroots]
    _ = (2 ^ n : ℝ)⁻¹ * Real.log ‖(quadratic c)^[n] z - a‖ := by
          rw [Polynomial.eval_sub, Polynomial.eval_C, quadraticPolyIterate_eval]

/-- Finite arbitrary-target potentials scale exactly under `f_c`: the signed
potential at `f_c z` on level `n` is twice the signed potential at `z` on
level `n+1`, away from the finite atoms. -/
theorem neg_logPotential_preBrolinMeasureAt_quadratic_eq_two_succ
    {c a z : ℂ} {n : ℕ} (hz : (quadratic c)^[n + 1] z - a ≠ 0) :
    - logPotential (preBrolinMeasureAt c a n) (quadratic c z) =
      2 * (- logPotential (preBrolinMeasureAt c a (n + 1)) z) := by
  have hzq : (quadratic c)^[n] (quadratic c z) - a ≠ 0 := by
    rwa [← Function.iterate_succ_apply (quadratic c) n z]
  calc
    - logPotential (preBrolinMeasureAt c a n) (quadratic c z)
        = (2 ^ n : ℝ)⁻¹ *
            Real.log ‖(quadratic c)^[n] (quadratic c z) - a‖ :=
          neg_logPotential_preBrolinMeasureAt_eq_log_norm hzq
    _ = (2 ^ n : ℝ)⁻¹ *
          Real.log ‖(quadratic c)^[n + 1] z - a‖ := by
          rw [← Function.iterate_succ_apply (quadratic c) n z]
    _ = 2 * ((2 ^ (n + 1) : ℝ)⁻¹ *
          Real.log ‖(quadratic c)^[n + 1] z - a‖) := by
          rw [pow_succ]
          ring
    _ = 2 * (- logPotential (preBrolinMeasureAt c a (n + 1)) z) := by
          rw [neg_logPotential_preBrolinMeasureAt_eq_log_norm hz]

/-- Unsigned form of finite arbitrary-target quadratic scaling. -/
theorem logPotential_preBrolinMeasureAt_quadratic_eq_two_succ
    {c a z : ℂ} {n : ℕ} (hz : (quadratic c)^[n + 1] z - a ≠ 0) :
    logPotential (preBrolinMeasureAt c a n) (quadratic c z) =
      2 * logPotential (preBrolinMeasureAt c a (n + 1)) z := by
  have h :=
    neg_logPotential_preBrolinMeasureAt_quadratic_eq_two_succ
      (c := c) (a := a) (z := z) (n := n) hz
  linarith

/-- Finite arbitrary-target truncated-kernel integrals are bounded above by
the true finite potential whenever the evaluation point is not a level-`n`
atom over the target. -/
theorem integral_truncatedLogKernel_preBrolinMeasureAt_le_logPotential_of_iterate_ne_target
    {c a z : ℂ} {δ : ℝ} {n : ℕ} (hδ : 0 < δ)
    (hz : (quadratic c)^[n] z - a ≠ 0) :
    ∫ w, truncatedLogKernel z δ w ∂preBrolinMeasureAt c a n ≤
      logPotential (preBrolinMeasureAt c a n) z := by
  rw [integral_preBrolinMeasureAt_eq_root_average,
    logPotential_preBrolinMeasureAt_eq_scaled_rootLogKernelSum]
  have hsum :
      (((quadraticPolyIterate c n - Polynomial.C a).roots.map
          (fun w => truncatedLogKernel z δ w)).sum) ≤
        (((quadraticPolyIterate c n - Polynomial.C a).roots.map
          (fun w => logKernel z w)).sum) := by
    suffices hsum' : ∀ s : Multiset ℂ,
        (∀ w ∈ s, truncatedLogKernel z δ w ≤ logKernel z w) →
          (s.map (fun w => truncatedLogKernel z δ w)).sum ≤
            (s.map (fun w => logKernel z w)).sum by
      apply hsum'
      intro w hw
      have hzw : z ≠ w := by
        intro h
        have hwroot : (quadraticPolyIterate c n - Polynomial.C a).IsRoot w :=
          (Polynomial.mem_roots (quadraticPolyIterate_sub_C_monic c a n).ne_zero).mp hw
        have hiter : (quadratic c)^[n] w - a = 0 := by
          simpa [Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_C,
            quadraticPolyIterate_eval] using hwroot
        exact hz (by rwa [h])
      exact truncatedLogKernel_le_logKernel_of_ne hδ hzw
    intro s
    induction s using Multiset.induction_on with
    | empty =>
        intro _h
        simp
    | cons x s ih =>
        intro h
        have hx : truncatedLogKernel z δ x ≤ logKernel z x := h x (by simp)
        have hs : ∀ w ∈ s, truncatedLogKernel z δ w ≤ logKernel z w := by
          intro w hw
          exact h w (by simp [hw])
        simpa using add_le_add hx (ih hs)
  exact mul_le_mul_of_nonneg_left hsum (by positivity)

/-- Pulling back any point by `f_c^[n]` gives exactly `2^n` roots over `ℂ`,
counted with multiplicity. -/
theorem roots_card_quadraticPolyIterate_sub_C (c a : ℂ) (n : ℕ) :
    (quadraticPolyIterate c n - Polynomial.C a).roots.card = 2 ^ n := by
  rw [IsAlgClosed.card_roots_eq_natDegree, Polynomial.natDegree_sub_C,
    quadraticPolyIterate_natDegree]

/-- A level-`n` pullback atom of an arbitrary target `a` has Green height
`2⁻ⁿG_c(a)`. -/
theorem greenFunctionDyn_eq_scaled_target_of_mem_roots_quadraticPolyIterate_sub_C
    {c a z : ℂ} {n : ℕ}
    (hz : z ∈ (quadraticPolyIterate c n - Polynomial.C a).roots) :
    greenFunctionDyn c z =
      (2 ^ n : ℝ)⁻¹ * greenFunctionDyn c a := by
  have hzroot : (quadratic c)^[n] z = a := by
    have hp : quadraticPolyIterate c n - Polynomial.C a ≠ 0 :=
      (quadraticPolyIterate_sub_C_monic c a n).ne_zero
    have hisroot : (quadraticPolyIterate c n - Polynomial.C a).IsRoot z :=
      (Polynomial.mem_roots hp).mp hz
    rwa [Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_C,
      quadraticPolyIterate_eval, sub_eq_zero] at hisroot
  have hscale := greenFunctionDyn_iterate c z n
  rw [hzroot] at hscale
  have hpow : (2 ^ n : ℝ) ≠ 0 := by positivity
  calc
    greenFunctionDyn c z = (2 ^ n : ℝ)⁻¹ * ((2 ^ n : ℝ) * greenFunctionDyn c z) := by
      field_simp [hpow]
    _ = (2 ^ n : ℝ)⁻¹ * greenFunctionDyn c a := by
      rw [← hscale]

/-- Every level-`n` pullback atom of `a` lies in the corresponding Green
sublevel. -/
theorem mem_greenSublevel_scaled_target_of_mem_roots_quadraticPolyIterate_sub_C
    {c a z : ℂ} {n : ℕ}
    (hz : z ∈ (quadraticPolyIterate c n - Polynomial.C a).roots) :
    z ∈ greenSublevel c ((2 ^ n : ℝ)⁻¹ * greenFunctionDyn c a) := by
  rw [greenSublevel]
  exact le_of_eq
    (greenFunctionDyn_eq_scaled_target_of_mem_roots_quadraticPolyIterate_sub_C hz)

/-- The unnormalized arbitrary-target pullback measure gives no mass above the
exact Green height `2⁻ⁿG_c(a)`. -/
theorem rootCountingMeasure_roots_sub_C_greenSublevel_scaled_target_compl
    (c a : ℂ) (n : ℕ) :
    rootCountingMeasure (quadraticPolyIterate c n - Polynomial.C a).roots
        (greenSublevel c ((2 ^ n : ℝ)⁻¹ * greenFunctionDyn c a))ᶜ = 0 :=
  rootCountingMeasure_compl_eq_zero_of_forall_mem _ _ fun _ hz =>
    mem_greenSublevel_scaled_target_of_mem_roots_quadraticPolyIterate_sub_C hz

/-- One-step finite balancedness at the root-multiset level: the two roots of
`f_c(X) = a`, counted with multiplicity, both push forward to `a`. -/
theorem roots_map_quadraticPoly_sub_C (c a : ℂ) :
    ((quadraticPoly c - Polynomial.C a).roots.map (quadratic c)) =
      Multiset.replicate 2 a := by
  rw [Multiset.eq_replicate]
  constructor
  · rw [Multiset.card_map, IsAlgClosed.card_roots_eq_natDegree, Polynomial.natDegree_sub_C,
      quadraticPoly_natDegree]
  · intro b hb
    rw [Multiset.mem_map] at hb
    rcases hb with ⟨x, hx, rfl⟩
    have hdeg : 0 < (quadraticPoly c).degree := by
      rw [← Polynomial.natDegree_pos_iff_degree_pos, quadraticPoly_natDegree]
      norm_num
    have hxroot : (quadraticPoly c).eval x = a :=
      (Polynomial.mem_roots_sub_C hdeg).mp hx
    simpa [quadraticPoly, quadratic_apply] using hxroot

/-- The two one-step roots of `z² + c = a`, counted with multiplicity, are
invariant under the antipodal map. -/
theorem roots_quadraticPoly_sub_C_map_neg (c a : ℂ) :
    ((quadraticPoly c - Polynomial.C a).roots.map Neg.neg) =
      (quadraticPoly c - Polynomial.C a).roots := by
  have hpoly :
      quadraticPoly c - Polynomial.C a =
        (Polynomial.X ^ 2 - Polynomial.C (a - c) : Polynomial ℂ) := by
    rw [quadraticPoly, map_sub]
    ring
  have hroots :
      (quadraticPoly c - Polynomial.C a).roots =
        Polynomial.nthRoots 2 (a - c) := by
    rw [hpoly, Polynomial.nthRoots]
  rw [hroots]
  by_cases hac : a - c = 0
  · rw [hac, Polynomial.nthRoots_zero_right]
    norm_num
  · have hsep :
        (Polynomial.X ^ 2 - Polynomial.C (a - c) : Polynomial ℂ).Separable :=
      Polynomial.separable_X_pow_sub_C (a - c)
        (by norm_num : (2 : ℂ) ≠ 0) hac
    have hnodup : (Polynomial.nthRoots 2 (a - c)).Nodup := by
      unfold Polynomial.nthRoots
      exact Polynomial.nodup_roots hsep
    apply Multiset.ext.mpr
    intro x
    have hcount :
        ((Polynomial.nthRoots 2 (a - c)).map Neg.neg).count x =
          (Polynomial.nthRoots 2 (a - c)).count (-x) := by
      simpa using
        (Multiset.count_map_eq_count' (fun y : ℂ => -y)
          (Polynomial.nthRoots 2 (a - c))
          (fun u v h => neg_inj.mp h) (-x))
    rw [hcount]
    by_cases hx : x ^ 2 = a - c
    · have hxmem : x ∈ Polynomial.nthRoots 2 (a - c) := by
        rw [Polynomial.mem_nthRoots (by norm_num : 0 < 2)]
        exact hx
      have hnegmem : -x ∈ Polynomial.nthRoots 2 (a - c) := by
        rw [Polynomial.mem_nthRoots (by norm_num : 0 < 2)]
        rw [show (-x) ^ 2 = x ^ 2 by ring, hx]
      rw [Multiset.count_eq_one_of_mem hnodup hxmem,
        Multiset.count_eq_one_of_mem hnodup hnegmem]
    · have hxnot : x ∉ Polynomial.nthRoots 2 (a - c) := by
        rw [Polynomial.mem_nthRoots (by norm_num : 0 < 2)]
        exact hx
      have hnegnot : -x ∉ Polynomial.nthRoots 2 (a - c) := by
        rw [Polynomial.mem_nthRoots (by norm_num : 0 < 2)]
        intro h
        exact hx (by rwa [show (-x) ^ 2 = x ^ 2 by ring] at h)
      rw [Multiset.count_eq_zero_of_notMem hxnot,
        Multiset.count_eq_zero_of_notMem hnegnot]

/-- Roots of the level-`n+1` target polynomial decompose as the multiset union,
over roots of the level-`n` target polynomial, of the two one-step preimages. -/
theorem roots_quadraticPolyIterate_succ_sub_C (c a : ℂ) (n : ℕ) :
    (quadraticPolyIterate c (n + 1) - Polynomial.C a).roots =
      ((quadraticPolyIterate c n - Polynomial.C a).roots.bind fun r =>
        (quadraticPoly c - Polynomial.C r).roots) := by
  let p : Polynomial ℂ := quadraticPolyIterate c n - Polynomial.C a
  have hpmonic : p.Monic := by
    dsimp [p]
    exact quadraticPolyIterate_sub_C_monic c a n
  have hproots : p.roots.card = p.natDegree := by
    dsimp [p]
    rw [roots_card_quadraticPolyIterate_sub_C, Polynomial.natDegree_sub_C,
      quadraticPolyIterate_natDegree]
  have hfactor : (p.roots.map fun r => Polynomial.X - Polynomial.C r).prod = p :=
    Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hpmonic hproots
  have hne : (0 : Polynomial ℂ) ∉ p.roots.map (fun r => quadraticPoly c - Polynomial.C r) := by
    intro h
    rcases Multiset.mem_map.mp h with ⟨r, _hr, hzero⟩
    have hnd : (quadraticPoly c - Polynomial.C r).natDegree = 2 := by
      rw [Polynomial.natDegree_sub_C, quadraticPoly_natDegree]
    rw [hzero, Polynomial.natDegree_zero] at hnd
    norm_num at hnd
  calc
    (quadraticPolyIterate c (n + 1) - Polynomial.C a).roots
        = ((quadraticPolyIterate c n - Polynomial.C a).comp (quadraticPoly c)).roots := by
          rw [quadraticPolyIterate_succ_sub_C_eq_comp]
    _ = (p.comp (quadraticPoly c)).roots := by rfl
    _ = (((p.roots.map fun r => Polynomial.X - Polynomial.C r).prod).comp
          (quadraticPoly c)).roots := by rw [hfactor]
    _ = ((p.roots.map fun r => quadraticPoly c - Polynomial.C r).prod).roots := by
          congr 1
          rw [Polynomial.multiset_prod_comp, Multiset.map_map]
          apply congrArg Multiset.prod
          apply Multiset.map_congr rfl
          intro r _hr
          simp [Polynomial.sub_comp]
    _ = (p.roots.map fun r => quadraticPoly c - Polynomial.C r).bind Polynomial.roots := by
          rw [Polynomial.roots_multiset_prod _ hne]
    _ = ((quadraticPolyIterate c n - Polynomial.C a).roots.bind fun r =>
          (quadraticPoly c - Polynomial.C r).roots) := by
          rw [Multiset.bind_map]

/-- Arbitrary-target pullback roots are antipodally symmetric at every positive
level, with multiplicity. -/
theorem roots_quadraticPolyIterate_succ_sub_C_map_neg (c a : ℂ) (n : ℕ) :
    ((quadraticPolyIterate c (n + 1) - Polynomial.C a).roots.map Neg.neg) =
      (quadraticPolyIterate c (n + 1) - Polynomial.C a).roots := by
  have hdecomp := roots_quadraticPolyIterate_succ_sub_C c a n
  rw [hdecomp, Multiset.map_bind]
  apply Multiset.bind_congr
  intro r _hr
  exact roots_quadraticPoly_sub_C_map_neg c r

/-- Finite arbitrary-target pre-Brolin measures are antipodally invariant at
every positive level, in test-integral form. -/
theorem integral_preBrolinMeasureAt_succ_neg_eq
    (c a : ℂ) (n : ℕ) (g : ℂ → ℝ) :
    ∫ z, g (-z) ∂preBrolinMeasureAt c a (n + 1) =
      ∫ z, g z ∂preBrolinMeasureAt c a (n + 1) := by
  rw [integral_preBrolinMeasureAt_eq_root_average,
    integral_preBrolinMeasureAt_eq_root_average]
  congr 1
  calc
    (((quadraticPolyIterate c (n + 1) - Polynomial.C a).roots.map
        fun z => g (-z)).sum)
        = ((((quadraticPolyIterate c (n + 1) - Polynomial.C a).roots.map
          Neg.neg).map g).sum) := by
          rw [Multiset.map_map]
          rfl
    _ = (((quadraticPolyIterate c (n + 1) - Polynomial.C a).roots.map
          g).sum) := by
          rw [roots_quadraticPolyIterate_succ_sub_C_map_neg]

/-- Measure-level antipodal invariance of finite arbitrary-target pre-Brolin
measures at every positive level. -/
theorem map_preBrolinMeasureAt_succ_neg (c a : ℂ) (n : ℕ) :
    Measure.map Neg.neg (preBrolinMeasureAt c a (n + 1)) =
      preBrolinMeasureAt c a (n + 1) := by
  rw [preBrolinMeasureAt, Measure.map_smul,
    map_rootCountingMeasure _ _ continuous_neg.measurable]
  rw [roots_quadraticPolyIterate_succ_sub_C_map_neg]

/-- Zero-target pullback roots are antipodally symmetric at every finite
level, with multiplicity. -/
theorem roots_quadraticPolyIterate_map_neg (c : ℂ) (n : ℕ) :
    ((quadraticPolyIterate c n).roots.map Neg.neg) =
      (quadraticPolyIterate c n).roots := by
  cases n with
  | zero =>
      simp [quadraticPolyIterate]
  | succ n =>
      have hdecomp :
          (quadraticPolyIterate c (n + 1)).roots =
            ((quadraticPolyIterate c n).roots.bind fun r =>
              (quadraticPoly c - Polynomial.C r).roots) := by
        simpa using roots_quadraticPolyIterate_succ_sub_C c 0 n
      rw [hdecomp, Multiset.map_bind]
      apply Multiset.bind_congr
      intro r _hr
      exact roots_quadraticPoly_sub_C_map_neg c r

/-- Finite zero-target pre-Brolin measures are antipodally invariant in
test-integral form. -/
theorem integral_preBrolinMeasure_neg_eq (c : ℂ) (n : ℕ) (g : ℂ → ℝ) :
    ∫ z, g (-z) ∂preBrolinMeasure c n =
      ∫ z, g z ∂preBrolinMeasure c n := by
  rw [integral_preBrolinMeasure_eq_root_average,
    integral_preBrolinMeasure_eq_root_average]
  congr 1
  calc
    (((quadraticPolyIterate c n).roots.map fun z => g (-z)).sum)
        = ((((quadraticPolyIterate c n).roots.map Neg.neg).map g).sum) := by
          rw [Multiset.map_map]
          rfl
    _ = (((quadraticPolyIterate c n).roots.map g).sum) := by
          rw [roots_quadraticPolyIterate_map_neg]

/-- Measure-level antipodal invariance of the finite zero-target pre-Brolin
measures. -/
theorem map_preBrolinMeasure_neg (c : ℂ) (n : ℕ) :
    Measure.map Neg.neg (preBrolinMeasure c n) = preBrolinMeasure c n := by
  rw [preBrolinMeasure, Measure.map_smul,
    map_rootCountingMeasure _ _ continuous_neg.measurable]
  rw [roots_quadraticPolyIterate_map_neg]

/-- Restrict a negated compactly supported plane test function to the compact
escape disk as a bounded continuous test function. -/
noncomputable def compactNegRestrictionOnEscapeDisk
    (c : ℂ) (φ : C_c(ℂ, ℝ)) :
    BoundedContinuousFunction (escapeDisk c) ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun z : escapeDisk c => φ (-(z : ℂ)),
      φ.continuous.comp (continuous_neg.comp continuous_subtype_val)⟩

theorem preBrolinProbabilityOnEscapeDisk_subseq_neg_integral_tendsto
    (c : ℂ) (φ : C_c(ℂ, ℝ)) :
    Tendsto
      (fun k =>
        ∫ z : escapeDisk c, φ (-(z : ℂ))
          ∂(preBrolinProbabilityOnEscapeDisk c (brolinLimitSubsequence c k) :
            Measure (escapeDisk c)))
      atTop
      (𝓝 (∫ z : escapeDisk c, φ (-(z : ℂ))
          ∂(brolinLimitOnEscapeDisk c : Measure (escapeDisk c)))) := by
  have h :=
    (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp
      (preBrolinProbabilityOnEscapeDisk_subseq_tendsto c))
      (compactNegRestrictionOnEscapeDisk c φ)
  simpa [compactNegRestrictionOnEscapeDisk] using h

theorem integral_preBrolinMeasure_neg_eq_integral_escapeDisk
    (c : ℂ) (n : ℕ) (φ : C_c(ℂ, ℝ)) :
    ∫ z, φ (-z) ∂preBrolinMeasure c n =
      ∫ z : escapeDisk c, φ (-(z : ℂ))
        ∂(preBrolinProbabilityOnEscapeDisk c n : Measure (escapeDisk c)) := by
  rw [preBrolinMeasure_eq_map_preBrolinMeasureOnEscapeDisk, integral_map]
  · rfl
  · exact measurable_subtype_coe.aemeasurable
  · exact (φ.continuous.comp continuous_neg).aestronglyMeasurable

theorem integral_limitingBrolinMeasure_neg_eq_integral_escapeDisk
    (c : ℂ) (φ : C_c(ℂ, ℝ)) :
    ∫ z, φ (-z) ∂limitingBrolinMeasure c =
      ∫ z : escapeDisk c, φ (-(z : ℂ))
        ∂(brolinLimitOnEscapeDisk c : Measure (escapeDisk c)) := by
  rw [limitingBrolinMeasure, integral_map]
  · exact measurable_subtype_coe.aemeasurable
  · exact (φ.continuous.comp continuous_neg).aestronglyMeasurable

/-- The selected zero-target limiting Brolin measure inherits the finite
antipodal symmetry. -/
theorem integral_limitingBrolinMeasure_neg_eq
    (c : ℂ) (φ : C_c(ℂ, ℝ)) :
    ∫ z, φ (-z) ∂limitingBrolinMeasure c =
      ∫ z, φ z ∂limitingBrolinMeasure c := by
  have hneg :=
    preBrolinProbabilityOnEscapeDisk_subseq_neg_integral_tendsto c φ
  have hpos :=
    preBrolinProbabilityOnEscapeDisk_subseq_integral_tendsto c φ
  have hsame :
      Tendsto
        (fun k =>
          ∫ z : escapeDisk c, φ (-(z : ℂ))
            ∂(preBrolinProbabilityOnEscapeDisk c
                (brolinLimitSubsequence c k) :
              Measure (escapeDisk c)))
        atTop
        (𝓝 (∫ z : escapeDisk c, φ (z : ℂ)
          ∂(brolinLimitOnEscapeDisk c : Measure (escapeDisk c)))) := by
    exact hpos.congr' (by
      filter_upwards [eventually_ge_atTop 0] with k _hk
      have hplane :=
        integral_preBrolinMeasure_neg_eq c (brolinLimitSubsequence c k)
          (fun z : ℂ => φ z)
      rw [integral_preBrolinMeasure_neg_eq_integral_escapeDisk,
        integral_preBrolinMeasure_eq_integral_escapeDisk] at hplane
      exact hplane.symm)
  have hlim :
      (∫ z : escapeDisk c, φ (-(z : ℂ))
          ∂(brolinLimitOnEscapeDisk c : Measure (escapeDisk c))) =
        ∫ z : escapeDisk c, φ (z : ℂ)
          ∂(brolinLimitOnEscapeDisk c : Measure (escapeDisk c)) :=
    tendsto_nhds_unique hneg hsame
  rw [integral_limitingBrolinMeasure_neg_eq_integral_escapeDisk,
    integral_limitingBrolinMeasure_eq_integral_escapeDisk]
  exact hlim

/-- Measure-level antipodal invariance of the selected zero-target limiting
Brolin measure. -/
theorem map_limitingBrolinMeasure_neg (c : ℂ) :
    Measure.map Neg.neg (limitingBrolinMeasure c) = limitingBrolinMeasure c := by
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro φ
  rw [integral_map]
  · exact integral_limitingBrolinMeasure_neg_eq c φ
  · exact continuous_neg.measurable.aemeasurable
  · exact φ.continuous.aestronglyMeasurable

/-- Finite balancedness at the root-multiset level: pushing level `n+1` roots
forward by `f_c` gives each level-`n` root with multiplicity `2`. -/
theorem roots_map_quadraticPolyIterate_succ_sub_C (c a : ℂ) (n : ℕ) :
    ((quadraticPolyIterate c (n + 1) - Polynomial.C a).roots.map (quadratic c)) =
      ((quadraticPolyIterate c n - Polynomial.C a).roots.bind fun r =>
        Multiset.replicate 2 r) := by
  rw [roots_quadraticPolyIterate_succ_sub_C]
  rw [Multiset.map_bind]
  apply Multiset.bind_congr
  intro r _hr
  exact roots_map_quadraticPoly_sub_C c r

/-- Binding each point to two copies is the same multiset as adding the
multiset to itself. -/
theorem bind_replicate_two_eq_add (s : Multiset ℂ) :
    (s.bind fun r => Multiset.replicate 2 r) = s + s := by
  calc
    (s.bind fun r => Multiset.replicate 2 r)
        = (s.bind fun r => Multiset.replicate 1 r + Multiset.replicate 1 r) := by
          apply Multiset.bind_congr
          intro r _hr
          rw [← Multiset.replicate_add]
    _ = (s.bind fun r => Multiset.replicate 1 r) +
          (s.bind fun r => Multiset.replicate 1 r) := by
          rw [Multiset.bind_add]
    _ = s + s := by
          have hsingle : (s.bind fun r => ({r} : Multiset ℂ)) = s := by
            simpa using (Multiset.bind_singleton s id)
          simp [hsingle]

/-- Counting measure form of doubling every atom. -/
theorem rootCountingMeasure_bind_replicate_two (s : Multiset ℂ) :
    rootCountingMeasure (s.bind fun r => Multiset.replicate 2 r) =
      (2 : ENNReal) • rootCountingMeasure s := by
  rw [bind_replicate_two_eq_add, rootCountingMeasure_add]
  ext A hA
  simp [Measure.smul_apply, two_mul]

/-- Finite balancedness for normalized arbitrary-target pre-Brolin measures:
the pushforward of the level `n+1` pullback measure by `f_c` is the level `n`
pullback measure. -/
theorem map_preBrolinMeasureAt_succ (c a : ℂ) (n : ℕ) :
    Measure.map (quadratic c) (preBrolinMeasureAt c a (n + 1)) =
      preBrolinMeasureAt c a n := by
  have hquad : Measurable (quadratic c) := (continuous_quadratic c).measurable
  rw [preBrolinMeasureAt, preBrolinMeasureAt, Measure.map_smul,
    map_rootCountingMeasure _ _ hquad, roots_map_quadraticPolyIterate_succ_sub_C,
    rootCountingMeasure_bind_replicate_two]
  rw [smul_smul]
  congr 1
  rw [pow_succ]
  rw [ENNReal.mul_inv (Or.inl (by simp)) (Or.inl (by simp))]
  rw [mul_assoc]
  have h2 : (2 : ENNReal)⁻¹ * 2 = 1 := ENNReal.inv_mul_cancel (by simp) (by simp)
  rw [h2, mul_one]

/-- Summing over a multiset where every point is doubled multiplies the sum by `2`. -/
theorem sum_bind_replicate_two (s : Multiset ℂ) (g : ℂ → ℝ) :
    (((s.bind fun r => Multiset.replicate 2 r).map g).sum) =
      2 * (s.map g).sum := by
  rw [Multiset.map_bind, Multiset.sum_bind]
  simp [two_mul, Multiset.sum_map_add]

/-- Finite balancedness in test-function form: summing a test function after
pushing level `n+1` roots through `f_c` gives twice the level-`n` root sum. -/
theorem sum_quadratic_roots_quadraticPolyIterate_succ_sub_C (c a : ℂ) (n : ℕ)
    (g : ℂ → ℝ) :
    (((quadraticPolyIterate c (n + 1) - Polynomial.C a).roots.map
      (fun z => g (quadratic c z))).sum) =
      2 * (((quadraticPolyIterate c n - Polynomial.C a).roots.map g).sum) := by
  change (((quadraticPolyIterate c (n + 1) - Polynomial.C a).roots.map
    (g ∘ quadratic c)).sum) =
      2 * (((quadraticPolyIterate c n - Polynomial.C a).roots.map g).sum)
  rw [← Multiset.map_map]
  rw [roots_map_quadraticPolyIterate_succ_sub_C, sum_bind_replicate_two]

/-- Finite balancedness in normalized integral form.  Integrating `g ∘ f_c`
against the level-`n+1` arbitrary-target pullback measure equals integrating
`g` against the level-`n` measure. -/
theorem integral_preBrolinMeasureAt_succ_comp_quadratic
    (c a : ℂ) (n : ℕ) (g : ℂ → ℝ) :
    ∫ z, g (quadratic c z) ∂preBrolinMeasureAt c a (n + 1) =
      ∫ z, g z ∂preBrolinMeasureAt c a n := by
  rw [integral_preBrolinMeasureAt_eq_root_average,
    integral_preBrolinMeasureAt_eq_root_average,
    sum_quadratic_roots_quadraticPolyIterate_succ_sub_C]
  have h2 : (2 : ℝ) ≠ 0 := by norm_num
  have hpow : (2 ^ n : ℝ) ≠ 0 := by positivity
  rw [pow_succ]
  field_simp [h2, hpow]

/-- Each arbitrary-target finite pre-Brolin pullback measure is normalized to
total mass `1`. -/
theorem preBrolinMeasureAt_apply_univ (c a : ℂ) (n : ℕ) :
    preBrolinMeasureAt c a n Set.univ = 1 := by
  rw [preBrolinMeasureAt, Measure.smul_apply, rootCountingMeasure_apply_univ,
    roots_card_quadraticPolyIterate_sub_C]
  rw [smul_eq_mul]
  have hne : (2 ^ n : ENNReal) ≠ 0 := by simp
  have htop : (2 ^ n : ENNReal) ≠ ⊤ := by simp
  simpa using ENNReal.inv_mul_cancel hne htop

instance instIsProbabilityMeasure_preBrolinMeasureAt (c a : ℂ) (n : ℕ) :
    IsProbabilityMeasure (preBrolinMeasureAt c a n) where
  measure_univ := preBrolinMeasureAt_apply_univ c a n

/-- The finite positive functional represented by the normalized level-`n`
pullback measure of an arbitrary target. -/
noncomputable def preBrolinRieszFunctionalAt (c a : ℂ) (n : ℕ) :
    C_c(ℂ, ℝ) →ₚ[ℝ] ℝ :=
  { toFun := fun φ => ∫ z, φ z ∂preBrolinMeasureAt c a n
    map_add' := by
      intro φ ψ
      change ∫ z, φ z + ψ z ∂preBrolinMeasureAt c a n =
        ∫ z, φ z ∂preBrolinMeasureAt c a n +
          ∫ z, ψ z ∂preBrolinMeasureAt c a n
      rw [integral_add]
      · exact φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
      · exact ψ.continuous.integrable_of_hasCompactSupport ψ.hasCompactSupport
    map_smul' := by
      intro r φ
      change ∫ z, r • φ z ∂preBrolinMeasureAt c a n =
        r • ∫ z, φ z ∂preBrolinMeasureAt c a n
      rw [integral_smul]
    monotone' := by
      intro φ ψ hφψ
      apply integral_mono _ _ hφψ
      · exact φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
      · exact ψ.continuous.integrable_of_hasCompactSupport ψ.hasCompactSupport }

theorem preBrolinRieszFunctionalAt_apply (c a : ℂ) (n : ℕ)
    (φ : C_c(ℂ, ℝ)) :
    preBrolinRieszFunctionalAt c a n φ =
      ∫ z, φ z ∂preBrolinMeasureAt c a n := by
  rfl

/-- Arbitrary-target finite Riesz functionals are normalized root averages. -/
theorem preBrolinRieszFunctionalAt_apply_root_average
    (c a : ℂ) (n : ℕ) (φ : C_c(ℂ, ℝ)) :
    preBrolinRieszFunctionalAt c a n φ =
      (2 ^ n : ℝ)⁻¹ *
        (((quadraticPolyIterate c n - Polynomial.C a).roots.map fun z => φ z).sum) := by
  rw [preBrolinRieszFunctionalAt_apply, integral_preBrolinMeasureAt_eq_root_average]

/-- The finite normalized arbitrary-target pullback measure gives no mass above
the exact Green height `2⁻ⁿG_c(a)`. -/
theorem preBrolinMeasureAt_greenSublevel_scaled_target_compl
    (c a : ℂ) (n : ℕ) :
    preBrolinMeasureAt c a n
        (greenSublevel c ((2 ^ n : ℝ)⁻¹ * greenFunctionDyn c a))ᶜ = 0 := by
  rw [preBrolinMeasureAt, Measure.smul_apply,
    rootCountingMeasure_roots_sub_C_greenSublevel_scaled_target_compl]
  simp

/-- If a Green threshold lies above `2⁻ⁿG_c(a)`, then the level-`n`
arbitrary-target pullback measure is carried by that larger sublevel. -/
theorem preBrolinMeasureAt_greenSublevel_compl_of_scaled_target_le
    (c a : ℂ) (n : ℕ) {ε : ℝ}
    (hε : (2 ^ n : ℝ)⁻¹ * greenFunctionDyn c a ≤ ε) :
    preBrolinMeasureAt c a n (greenSublevel c ε)ᶜ = 0 := by
  rw [preBrolinMeasureAt, Measure.smul_apply]
  have hroot :
      rootCountingMeasure (quadraticPolyIterate c n - Polynomial.C a).roots
          (greenSublevel c ε)ᶜ = 0 :=
    rootCountingMeasure_compl_eq_zero_of_forall_mem _ _ fun z hz => by
      have hzsub :=
        mem_greenSublevel_scaled_target_of_mem_roots_quadraticPolyIterate_sub_C
          (c := c) (a := a) (n := n) hz
      rw [mem_greenSublevel_iff] at hzsub ⊢
      exact le_trans hzsub hε
  rw [hroot]
  simp

/-- If a test function vanishes on a Green sublevel that contains the
level-`n` pullback atoms of `a`, then the corresponding finite arbitrary-target
Brolin functional vanishes on it. -/
theorem preBrolinRieszFunctionalAt_eq_zero_of_scaled_target_le_of_eq_zero_on_greenSublevel
    (c a : ℂ) (n : ℕ) {ε : ℝ} (φ : C_c(ℂ, ℝ))
    (hε : (2 ^ n : ℝ)⁻¹ * greenFunctionDyn c a ≤ ε)
    (hφ : ∀ z, z ∈ greenSublevel c ε → φ z = 0) :
    preBrolinRieszFunctionalAt c a n φ = 0 := by
  rw [preBrolinRieszFunctionalAt_apply_root_average]
  have hsum :
      (((quadraticPolyIterate c n - Polynomial.C a).roots.map fun z => φ z).sum) = 0 := by
    have hmap :
        ((quadraticPolyIterate c n - Polynomial.C a).roots.map fun z => φ z) =
          ((quadraticPolyIterate c n - Polynomial.C a).roots.map fun _ => 0) := by
      apply Multiset.map_congr rfl
      intro z hz
      exact hφ z (by
        have hzsub :=
          mem_greenSublevel_scaled_target_of_mem_roots_quadraticPolyIterate_sub_C
            (c := c) (a := a) (n := n) hz
        rw [mem_greenSublevel_iff] at hzsub ⊢
        exact le_trans hzsub hε)
    rw [hmap]
    simp
  rw [hsum, mul_zero]

/-- The target Green height scaled by `2⁻ⁿ` eventually lies below any
positive threshold. -/
theorem exists_forall_scaled_target_le_of_pos (c a : ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n, N ≤ n →
      (2 ^ n : ℝ)⁻¹ * greenFunctionDyn c a ≤ ε := by
  have hGnonneg : 0 ≤ greenFunctionDyn c a := greenFunctionDyn_nonneg c a
  by_cases hGzero : greenFunctionDyn c a = 0
  · refine ⟨0, fun n _ => ?_⟩
    rw [hGzero, mul_zero]
    exact hε.le
  · have hGpos : 0 < greenFunctionDyn c a :=
      lt_of_le_of_ne hGnonneg (Ne.symm hGzero)
    obtain ⟨N, hN⟩ :=
      pow_unbounded_of_one_lt (greenFunctionDyn c a / ε)
        (show (1 : ℝ) < 2 by norm_num)
    refine ⟨N, fun n hn => ?_⟩
    have hpowmono : (2 ^ N : ℝ) ≤ 2 ^ n :=
      pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hn
    have hlt : greenFunctionDyn c a / ε < (2 ^ n : ℝ) := lt_of_lt_of_le hN hpowmono
    have hpowpos : 0 < (2 ^ n : ℝ) := by positivity
    have hGlt : greenFunctionDyn c a < ε * (2 ^ n : ℝ) := by
      rw [mul_comm]
      exact (div_lt_iff₀ hε).mp hlt
    have hscaled_lt : (2 ^ n : ℝ)⁻¹ * greenFunctionDyn c a < ε := by
      rw [inv_mul_eq_div]
      exact (div_lt_iff₀ hpowpos).mpr (by nlinarith)
    exact hscaled_lt.le

/-- For every positive Green threshold, all sufficiently deep arbitrary-target
finite pullback measures are carried by `{G_c ≤ ε}`. -/
theorem eventually_preBrolinMeasureAt_greenSublevel_compl_of_pos
    (c a : ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, preBrolinMeasureAt c a n (greenSublevel c ε)ᶜ = 0 := by
  obtain ⟨N, hN⟩ := exists_forall_scaled_target_le_of_pos c a hε
  filter_upwards [eventually_ge_atTop N] with n hn
  exact preBrolinMeasureAt_greenSublevel_compl_of_scaled_target_le c a n (hN n hn)

/-- Arbitrary-target finite Riesz functionals vanish eventually on every test
function that vanishes on a positive Green sublevel. -/
theorem eventually_preBrolinRieszFunctionalAt_eq_zero_of_eq_zero_on_greenSublevel
    (c a : ℂ) {ε : ℝ} (hε : 0 < ε) (φ : C_c(ℂ, ℝ))
    (hφ : ∀ z, z ∈ greenSublevel c ε → φ z = 0) :
    ∀ᶠ n in atTop, preBrolinRieszFunctionalAt c a n φ = 0 := by
  obtain ⟨N, hN⟩ := exists_forall_scaled_target_le_of_pos c a hε
  filter_upwards [eventually_ge_atTop N] with n hn
  exact preBrolinRieszFunctionalAt_eq_zero_of_scaled_target_le_of_eq_zero_on_greenSublevel
    c a n φ (hN n hn) hφ

/-- Arbitrary-target finite GAP-A Cauchy-transform identity: the normalized
pullback measure has Cauchy transform equal to the normalized logarithmic
derivative of `f_c^[n] - a`, away from the finite preimage atoms. -/
theorem integral_cauchy_preBrolinMeasureAt_eq_derivative_div {c a z : ℂ} {n : ℕ}
    (hz : (quadratic c)^[n] z - a ≠ 0) :
    ∫ ζ, (z - ζ)⁻¹ ∂preBrolinMeasureAt c a n =
      ((2 ^ n : ℝ)⁻¹ : ℂ) *
        ((quadraticPolyIterate c n).derivative.eval z / ((quadratic c)^[n] z - a)) := by
  have hzeval : (quadraticPolyIterate c n - Polynomial.C a).eval z ≠ 0 := by
    simpa [Polynomial.eval_sub, quadraticPolyIterate_eval] using hz
  rw [preBrolinMeasureAt, integral_smul_measure,
    integral_cauchy_rootCountingMeasure_eq_derivative_div hzeval]
  have hscale : (((2 ^ n : ENNReal)⁻¹).toReal : ℂ) = ((2 ^ n : ℝ)⁻¹ : ℂ) := by
    simp [ENNReal.toReal_inv, ENNReal.toReal_pow]
  rw [Polynomial.derivative_sub, Polynomial.derivative_C, sub_zero, Polynomial.eval_sub,
    Polynomial.eval_C, quadraticPolyIterate_eval]
  change (((2 ^ n : ENNReal)⁻¹).toReal : ℂ) *
      ((quadraticPolyIterate c n).derivative.eval z / ((quadratic c)^[n] z - a)) =
    ((2 ^ n : ℝ)⁻¹ : ℂ) *
      ((quadraticPolyIterate c n).derivative.eval z / ((quadratic c)^[n] z - a))
  rw [hscale]

/-- The finite normalized logarithmic derivative of `f_c^[n] - a` at `z`.
For basin points this is the algebraic side of the Cauchy-transform limit. -/
noncomputable def finiteBrolinNormalizedLogDerivativeAt
    (c a z : ℂ) (n : ℕ) : ℂ :=
  ((2 ^ n : ℝ)⁻¹ : ℂ) *
    ((quadraticPolyIterate c n).derivative.eval z / ((quadratic c)^[n] z - a))

/-- The polynomial derivative of the `n`th quadratic iterate agrees with the
explicit dynamical derivative cocycle. -/
theorem quadraticPolyIterate_derivative_eval_eq_prod
    (c : ℂ) (n : ℕ) (z : ℂ) :
    (quadraticPolyIterate c n).derivative.eval z =
      ∏ k ∈ Finset.range n, 2 * (quadratic c)^[k] z := by
  have hpoly : HasStrictDerivAt
      (fun z => (quadraticPolyIterate c n).eval z)
      ((quadraticPolyIterate c n).derivative.eval z) z :=
    Polynomial.hasStrictDerivAt _ _
  have heq : (fun z => (quadraticPolyIterate c n).eval z) =
      (quadratic c)^[n] := by
    funext w
    exact quadraticPolyIterate_eval c n w
  rw [heq] at hpoly
  exact hpoly.hasDerivAt.unique
    (hasStrictDerivAt_quadratic_iterate c n z).hasDerivAt

/-- One finite step of the zero-target normalized logarithmic derivative.  On
the basin, the last factor tends to `1`; this is the algebraic reason shifted
and unshifted exterior Cauchy transforms have the same subsequential limit. -/
theorem finiteBrolinNormalizedLogDerivativeAt_zero_succ_eq_mul
    {c z : ℂ} {n : ℕ}
    (h0 : (quadratic c)^[n] z ≠ 0)
    (h1 : (quadratic c)^[n + 1] z ≠ 0) :
    finiteBrolinNormalizedLogDerivativeAt c 0 z (n + 1) =
      finiteBrolinNormalizedLogDerivativeAt c 0 z n *
        (((quadratic c)^[n] z) ^ 2 / (quadratic c)^[n + 1] z) := by
  let x : ℂ := (quadratic c)^[n] z
  let D : ℂ := ∏ k ∈ Finset.range n, 2 * (quadratic c)^[k] z
  have hx : x ≠ 0 := by
    simpa [x] using h0
  have hqx : quadratic c x ≠ 0 := by
    simpa [x, Function.iterate_succ_apply'] using h1
  have hprod :
      (∏ k ∈ Finset.range (n + 1), 2 * (quadratic c)^[k] z) =
        D * (2 * x) := by
    simp [D, x, Finset.prod_range_succ]
  simp only [finiteBrolinNormalizedLogDerivativeAt, sub_zero]
  rw [
    quadraticPolyIterate_derivative_eval_eq_prod c (n + 1) z,
    quadraticPolyIterate_derivative_eval_eq_prod c n z,
    hprod]
  have hpow : ((2 ^ (n + 1) : ℝ)⁻¹ : ℂ) =
      ((2 ^ n : ℝ)⁻¹ : ℂ) / 2 := by
    rw [pow_succ]
    norm_num [inv_mul_eq_div]
    ring
  rw [hpow]
  have hiter : (quadratic c)^[n + 1] z = quadratic c x := by
    rw [Function.iterate_succ_apply']
  rw [hiter]
  field_simp [hx, hqx]
  rfl

/-- Outside the filled Julia set, the orbit escapes to infinity in norm. -/
theorem norm_iterate_tendsto_atTop_of_not_mem_filledJulia
    {c z : ℂ} (hz : z ∉ filledJulia c) :
    Tendsto (fun n : ℕ => ‖(quadratic c)^[n] z‖) atTop atTop := by
  refine tendsto_atTop.2 ?_
  intro B
  obtain ⟨N, hN⟩ := exists_orbit_gt hz (max (max 2 ‖c‖) B)
  have hNc : ‖c‖ ≤ ‖(quadratic c)^[N] z‖ :=
    le_of_lt (lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_left _ _)) hN)
  have hN2 : 2 < ‖(quadratic c)^[N] z‖ :=
    lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hNB : B ≤ ‖(quadratic c)^[N] z‖ :=
    le_of_lt (lt_of_le_of_lt (le_max_right _ _) hN)
  filter_upwards [eventually_ge_atTop N] with n hn
  have htail := norm_le_orbit hNc hN2 (n - N)
  rw [← Function.iterate_add_apply, Nat.sub_add_cancel hn] at htail
  exact le_trans hNB htail

/-- The finite one-step Cauchy multiplier tends to `1` on the basin. -/
theorem finiteBrolinCauchyShiftFactor_tendsto_one
    {c z : ℂ} (hz : z ∉ filledJulia c) {φ : ℕ → ℕ}
    (hφ : Tendsto φ atTop atTop) :
    Tendsto
      (fun k : ℕ =>
        ((quadratic c)^[φ k] z) ^ 2 /
          (quadratic c)^[φ k + 1] z)
      atTop (𝓝 (1 : ℂ)) := by
  have horbit_succ :
      Tendsto (fun k : ℕ => ‖(quadratic c)^[φ k + 1] z‖) atTop atTop :=
    (norm_iterate_tendsto_atTop_of_not_mem_filledJulia hz).comp
      ((tendsto_add_atTop_nat 1).comp hφ)
  have hbound :
      Tendsto
        (fun k : ℕ => ‖c‖ / ‖(quadratic c)^[φ k + 1] z‖)
        atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop horbit_succ
  have hnonzero :
      ∀ᶠ k in atTop, (quadratic c)^[φ k + 1] z ≠ 0 :=
    (horbit_succ.eventually_gt_atTop 0).mono fun _ hk =>
      norm_pos_iff.mp hk
  have hdiff0 :
      Tendsto
        (fun k : ℕ =>
          ((quadratic c)^[φ k] z) ^ 2 /
              (quadratic c)^[φ k + 1] z - 1)
        atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hbound
    filter_upwards [hnonzero] with k hk
    let x : ℂ := (quadratic c)^[φ k] z
    have hiter : (quadratic c)^[φ k + 1] z = quadratic c x := by
      rw [Function.iterate_succ_apply']
    have hq : quadratic c x ≠ 0 := by
      simpa [hiter] using hk
    have hq' : x ^ 2 + c ≠ 0 := by
      simpa [quadratic] using hq
    have hdiff :
        x ^ 2 / (quadratic c x) - 1 = -c / (quadratic c x) := by
      unfold quadratic
      field_simp [hq']
      ring
    calc
      ‖((quadratic c)^[φ k] z) ^ 2 /
            (quadratic c)^[φ k + 1] z - 1‖
          = ‖x ^ 2 / quadratic c x - 1‖ := by rw [hiter]
      _ = ‖-c / quadratic c x‖ := by rw [hdiff]
      _ = ‖c‖ / ‖quadratic c x‖ := by rw [norm_div, norm_neg]
      _ = ‖c‖ / ‖(quadratic c)^[φ k + 1] z‖ := by rw [hiter]
      _ ≤ ‖c‖ / ‖(quadratic c)^[φ k + 1] z‖ := le_rfl
  have hadd :
      Tendsto
        (fun k : ℕ =>
          (((quadratic c)^[φ k] z) ^ 2 /
              (quadratic c)^[φ k + 1] z - 1) + 1)
        atTop (𝓝 (0 + (1 : ℂ))) :=
    hdiff0.add (tendsto_const_nhds (x := (1 : ℂ)))
  simpa [sub_eq_add_neg, add_assoc] using hadd

/-- Real part of the finite arbitrary-target GAP-A Cauchy identity. -/
theorem integral_cauchy_re_preBrolinMeasureAt_eq_derivative_div
    {c a z : ℂ} {n : ℕ} (hz : (quadratic c)^[n] z - a ≠ 0) :
    ∫ ζ, ((z - ζ)⁻¹).re ∂preBrolinMeasureAt c a n =
      (finiteBrolinNormalizedLogDerivativeAt c a z n).re := by
  have hzeval : (quadraticPolyIterate c n - Polynomial.C a).eval z ≠ 0 := by
    simpa [Polynomial.eval_sub, quadraticPolyIterate_eval] using hz
  rw [preBrolinMeasureAt, integral_smul_measure,
    integral_cauchy_re_rootCountingMeasure_eq_derivative_div hzeval]
  have hscale : (((2 ^ n : ENNReal)⁻¹).toReal) = (2 ^ n : ℝ)⁻¹ := by
    simp [ENNReal.toReal_inv, ENNReal.toReal_pow]
  rw [Polynomial.derivative_sub, Polynomial.derivative_C, sub_zero, Polynomial.eval_sub,
    Polynomial.eval_C, quadraticPolyIterate_eval, hscale]
  rw [finiteBrolinNormalizedLogDerivativeAt, ← Complex.ofReal_inv, Complex.re_ofReal_mul]
  simp

/-- Imaginary part of the finite arbitrary-target GAP-A Cauchy identity. -/
theorem integral_cauchy_im_preBrolinMeasureAt_eq_derivative_div
    {c a z : ℂ} {n : ℕ} (hz : (quadratic c)^[n] z - a ≠ 0) :
    ∫ ζ, ((z - ζ)⁻¹).im ∂preBrolinMeasureAt c a n =
      (finiteBrolinNormalizedLogDerivativeAt c a z n).im := by
  have hzeval : (quadraticPolyIterate c n - Polynomial.C a).eval z ≠ 0 := by
    simpa [Polynomial.eval_sub, quadraticPolyIterate_eval] using hz
  rw [preBrolinMeasureAt, integral_smul_measure,
    integral_cauchy_im_rootCountingMeasure_eq_derivative_div hzeval]
  have hscale : (((2 ^ n : ENNReal)⁻¹).toReal) = (2 ^ n : ℝ)⁻¹ := by
    simp [ENNReal.toReal_inv, ENNReal.toReal_pow]
  rw [Polynomial.derivative_sub, Polynomial.derivative_C, sub_zero, Polynomial.eval_sub,
    Polynomial.eval_C, quadraticPolyIterate_eval, hscale]
  rw [finiteBrolinNormalizedLogDerivativeAt, ← Complex.ofReal_inv, Complex.im_ofReal_mul]
  simp

/-- The original finite pre-Brolin measure is the arbitrary-target construction
at target `0`. -/
theorem preBrolinMeasureAt_zero (c : ℂ) (n : ℕ) :
    preBrolinMeasureAt c 0 n = preBrolinMeasure c n := by
  simp [preBrolinMeasureAt, preBrolinMeasure]

/-- The arbitrary-target finite Riesz functional specializes to the original
zero-target finite Riesz functional. -/
theorem preBrolinRieszFunctionalAt_zero_apply (c : ℂ) (n : ℕ)
    (φ : C_c(ℂ, ℝ)) :
    preBrolinRieszFunctionalAt c 0 n φ = preBrolinRieszFunctional c n φ := by
  rw [preBrolinRieszFunctionalAt_apply, preBrolinRieszFunctional_apply,
    preBrolinMeasureAt_zero]

/-- Zero-target finite balancedness in normalized integral form. -/
theorem integral_preBrolinMeasure_succ_comp_quadratic
    (c : ℂ) (n : ℕ) (g : ℂ → ℝ) :
    ∫ z, g (quadratic c z) ∂preBrolinMeasure c (n + 1) =
      ∫ z, g z ∂preBrolinMeasure c n := by
  rw [← preBrolinMeasureAt_zero c (n + 1), ← preBrolinMeasureAt_zero c n]
  exact integral_preBrolinMeasureAt_succ_comp_quadratic c 0 n g

/-- Zero-target finite balancedness: the pushforward of the level `n+1`
finite Brolin pullback measure by `f_c` is the level `n` measure. -/
theorem map_preBrolinMeasure_succ (c : ℂ) (n : ℕ) :
    Measure.map (quadratic c) (preBrolinMeasure c (n + 1)) =
      preBrolinMeasure c n := by
  rw [← preBrolinMeasureAt_zero c (n + 1), ← preBrolinMeasureAt_zero c n]
  exact map_preBrolinMeasureAt_succ c 0 n

theorem integral_preBrolinProbabilityOnEscapeDisk_succ_comp_quadratic
    (c : ℂ) (n : ℕ) (φ : C_c(ℂ, ℝ)) :
    ∫ z : escapeDisk c, φ (quadratic c (z : ℂ))
        ∂(preBrolinProbabilityOnEscapeDisk c (n + 1) : Measure (escapeDisk c)) =
      ∫ z : escapeDisk c, φ (z : ℂ)
        ∂(preBrolinProbabilityOnEscapeDisk c n : Measure (escapeDisk c)) := by
  have hplane :=
    integral_preBrolinMeasure_succ_comp_quadratic c n
      (fun z : ℂ => φ z)
  have hleft :
      ∫ z, φ (quadratic c z) ∂preBrolinMeasure c (n + 1) =
        ∫ z : escapeDisk c, φ (quadratic c (z : ℂ))
          ∂(preBrolinProbabilityOnEscapeDisk c (n + 1) :
            Measure (escapeDisk c)) := by
    rw [preBrolinMeasure_eq_map_preBrolinMeasureOnEscapeDisk, integral_map]
    · rfl
    · exact measurable_subtype_coe.aemeasurable
    · exact (φ.continuous.comp (continuous_quadratic c)).aestronglyMeasurable
  have hright :
      ∫ z, φ z ∂preBrolinMeasure c n =
        ∫ z : escapeDisk c, φ (z : ℂ)
          ∂(preBrolinProbabilityOnEscapeDisk c n :
            Measure (escapeDisk c)) := by
    simpa [preBrolinProbabilityOnEscapeDisk] using
      integral_preBrolinMeasure_eq_integral_escapeDisk c n φ
  rw [hleft, hright] at hplane
  exact hplane

/-- Restrict a compactly supported plane test after one quadratic step to the
compact escape disk. -/
noncomputable def compactQuadraticRestrictionOnEscapeDisk
    (c : ℂ) (φ : C_c(ℂ, ℝ)) :
    BoundedContinuousFunction (escapeDisk c) ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun z : escapeDisk c => φ (quadratic c (z : ℂ)),
      φ.continuous.comp ((continuous_quadratic c).comp continuous_subtype_val)⟩

/-- A compactness-selected weak limit of the shifted finite measures
`μ_{ψ k + 1}`.  It is not asserted to equal `μ_c`; the next theorem records
the unconditional pushforward relation supplied by finite balancedness. -/
noncomputable def shiftedBrolinLimitOnEscapeDiskData (c : ℂ) :
    { ν : ProbabilityMeasure (escapeDisk c) //
      ∃ η : ℕ → ℕ, StrictMono η ∧
        Tendsto
          (fun k =>
            preBrolinProbabilityOnEscapeDisk c
              (brolinLimitSubsequence c (η k) + 1))
          atTop (𝓝 ν) } := by
  classical
  let shifted : ℕ → ProbabilityMeasure (escapeDisk c) :=
    fun k => preBrolinProbabilityOnEscapeDisk c
      (brolinLimitSubsequence c k + 1)
  let h := CompactSpace.tendsto_subseq shifted
  let ν := Classical.choose h
  have hν :
      ∃ η : ℕ → ℕ, StrictMono η ∧
        Tendsto (shifted ∘ η) atTop (𝓝 ν) :=
    Classical.choose_spec h
  let η := Classical.choose hν
  have hη :
      StrictMono η ∧ Tendsto (shifted ∘ η) atTop (𝓝 ν) :=
    Classical.choose_spec hν
  exact ⟨ν, η, hη.1, by simpa [shifted, Function.comp_def] using hη.2⟩

noncomputable def shiftedBrolinLimitOnEscapeDisk (c : ℂ) :
    ProbabilityMeasure (escapeDisk c) :=
  (shiftedBrolinLimitOnEscapeDiskData c).1

theorem shiftedBrolinLimitOnEscapeDisk_spec (c : ℂ) :
    ∃ η : ℕ → ℕ, StrictMono η ∧
      Tendsto
        (fun k =>
          preBrolinProbabilityOnEscapeDisk c
            (brolinLimitSubsequence c (η k) + 1))
        atTop (𝓝 (shiftedBrolinLimitOnEscapeDisk c)) :=
  (shiftedBrolinLimitOnEscapeDiskData c).2

noncomputable def shiftedBrolinLimitSubsequence (c : ℂ) : ℕ → ℕ :=
  Classical.choose (shiftedBrolinLimitOnEscapeDisk_spec c)

theorem shiftedBrolinLimitSubsequence_strictMono (c : ℂ) :
    StrictMono (shiftedBrolinLimitSubsequence c) :=
  (Classical.choose_spec (shiftedBrolinLimitOnEscapeDisk_spec c)).1

theorem shiftedBrolinLimitSubsequence_tendsto_atTop (c : ℂ) :
    Tendsto (shiftedBrolinLimitSubsequence c) atTop atTop :=
  (shiftedBrolinLimitSubsequence_strictMono c).tendsto_atTop

/-- The actual finite level used by the shifted cluster extraction. -/
noncomputable def shiftedBrolinIndex (c : ℂ) (k : ℕ) : ℕ :=
  brolinLimitSubsequence c (shiftedBrolinLimitSubsequence c k) + 1

theorem shiftedBrolinIndex_tendsto_atTop (c : ℂ) :
    Tendsto (shiftedBrolinIndex c) atTop atTop := by
  unfold shiftedBrolinIndex
  exact (tendsto_add_atTop_nat 1).comp
    ((brolinLimitSubsequence_tendsto_atTop c).comp
      (shiftedBrolinLimitSubsequence_tendsto_atTop c))

theorem shiftedBrolinProbabilityOnEscapeDisk_subseq_tendsto (c : ℂ) :
    Tendsto
      (fun k =>
        preBrolinProbabilityOnEscapeDisk c
          (shiftedBrolinIndex c k))
      atTop (𝓝 (shiftedBrolinLimitOnEscapeDisk c)) := by
  simpa [shiftedBrolinIndex] using (Classical.choose_spec
    (shiftedBrolinLimitOnEscapeDisk_spec c)).2

/-- Plane measure induced by the shifted compactness limit. -/
noncomputable def shiftedLimitingBrolinMeasure (c : ℂ) : Measure ℂ :=
  Measure.map (fun z : escapeDisk c => (z : ℂ))
    (shiftedBrolinLimitOnEscapeDisk c : Measure (escapeDisk c))

instance instIsProbabilityMeasure_shiftedLimitingBrolinMeasure (c : ℂ) :
    IsProbabilityMeasure (shiftedLimitingBrolinMeasure c) := by
  rw [shiftedLimitingBrolinMeasure]
  exact Measure.isProbabilityMeasure_map measurable_subtype_coe.aemeasurable

theorem shiftedLimitingBrolinMeasure_integral_eq_integral_escapeDisk
    (c : ℂ) (φ : C_c(ℂ, ℝ)) :
    ∫ z, φ z ∂shiftedLimitingBrolinMeasure c =
      ∫ z : escapeDisk c, φ (z : ℂ)
        ∂(shiftedBrolinLimitOnEscapeDisk c : Measure (escapeDisk c)) := by
  rw [shiftedLimitingBrolinMeasure, integral_map]
  · exact measurable_subtype_coe.aemeasurable
  · exact φ.continuous.aestronglyMeasurable

theorem preBrolinMeasure_shiftedSubseq_integral_tendsto_shiftedLimiting
    (c : ℂ) (φ : C_c(ℂ, ℝ)) :
    Tendsto
      (fun k => ∫ z, φ z ∂preBrolinMeasure c (shiftedBrolinIndex c k))
      atTop
      (𝓝 (∫ z, φ z ∂shiftedLimitingBrolinMeasure c)) := by
  have h :=
    (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp
      (shiftedBrolinProbabilityOnEscapeDisk_subseq_tendsto c))
      (compactRestrictionOnEscapeDisk c φ)
  rw [shiftedLimitingBrolinMeasure_integral_eq_integral_escapeDisk]
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 0] with k _hk
  rw [integral_preBrolinMeasure_eq_integral_escapeDisk]
  rfl

theorem shiftedBrolinProbabilityOnEscapeDisk_subseq_neg_integral_tendsto
    (c : ℂ) (φ : C_c(ℂ, ℝ)) :
    Tendsto
      (fun k =>
        ∫ z : escapeDisk c, φ (-(z : ℂ))
          ∂(preBrolinProbabilityOnEscapeDisk c (shiftedBrolinIndex c k) :
            Measure (escapeDisk c)))
      atTop
      (𝓝 (∫ z : escapeDisk c, φ (-(z : ℂ))
          ∂(shiftedBrolinLimitOnEscapeDisk c : Measure (escapeDisk c)))) := by
  have h :=
    (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp
      (shiftedBrolinProbabilityOnEscapeDisk_subseq_tendsto c))
      (compactNegRestrictionOnEscapeDisk c φ)
  simpa [compactNegRestrictionOnEscapeDisk] using h

theorem shiftedBrolinProbabilityOnEscapeDisk_subseq_integral_tendsto
    (c : ℂ) (φ : C_c(ℂ, ℝ)) :
    Tendsto
      (fun k =>
        ∫ z : escapeDisk c, φ (z : ℂ)
          ∂(preBrolinProbabilityOnEscapeDisk c (shiftedBrolinIndex c k) :
            Measure (escapeDisk c)))
      atTop
      (𝓝 (∫ z : escapeDisk c, φ (z : ℂ)
          ∂(shiftedBrolinLimitOnEscapeDisk c : Measure (escapeDisk c)))) := by
  have h :=
    (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp
      (shiftedBrolinProbabilityOnEscapeDisk_subseq_tendsto c))
      (compactRestrictionOnEscapeDisk c φ)
  simpa [compactRestrictionOnEscapeDisk] using h

theorem integral_shiftedLimitingBrolinMeasure_neg_eq_integral_escapeDisk
    (c : ℂ) (φ : C_c(ℂ, ℝ)) :
    ∫ z, φ (-z) ∂shiftedLimitingBrolinMeasure c =
      ∫ z : escapeDisk c, φ (-(z : ℂ))
        ∂(shiftedBrolinLimitOnEscapeDisk c : Measure (escapeDisk c)) := by
  rw [shiftedLimitingBrolinMeasure, integral_map]
  · exact measurable_subtype_coe.aemeasurable
  · exact (φ.continuous.comp continuous_neg).aestronglyMeasurable

/-- The shifted limiting Brolin cluster inherits the finite antipodal symmetry. -/
theorem integral_shiftedLimitingBrolinMeasure_neg_eq
    (c : ℂ) (φ : C_c(ℂ, ℝ)) :
    ∫ z, φ (-z) ∂shiftedLimitingBrolinMeasure c =
      ∫ z, φ z ∂shiftedLimitingBrolinMeasure c := by
  have hneg :=
    shiftedBrolinProbabilityOnEscapeDisk_subseq_neg_integral_tendsto c φ
  have hpos :=
    shiftedBrolinProbabilityOnEscapeDisk_subseq_integral_tendsto c φ
  have hsame :
      Tendsto
        (fun k =>
          ∫ z : escapeDisk c, φ (-(z : ℂ))
            ∂(preBrolinProbabilityOnEscapeDisk c
                (shiftedBrolinIndex c k) :
              Measure (escapeDisk c)))
        atTop
        (𝓝 (∫ z : escapeDisk c, φ (z : ℂ)
          ∂(shiftedBrolinLimitOnEscapeDisk c : Measure (escapeDisk c)))) := by
    exact hpos.congr' (by
      filter_upwards [eventually_ge_atTop 0] with k _hk
      have hplane :=
        integral_preBrolinMeasure_neg_eq c (shiftedBrolinIndex c k)
          (fun z : ℂ => φ z)
      rw [integral_preBrolinMeasure_neg_eq_integral_escapeDisk,
        integral_preBrolinMeasure_eq_integral_escapeDisk] at hplane
      exact hplane.symm)
  have hlim :
      (∫ z : escapeDisk c, φ (-(z : ℂ))
          ∂(shiftedBrolinLimitOnEscapeDisk c : Measure (escapeDisk c))) =
        ∫ z : escapeDisk c, φ (z : ℂ)
          ∂(shiftedBrolinLimitOnEscapeDisk c : Measure (escapeDisk c)) :=
    tendsto_nhds_unique hneg hsame
  rw [integral_shiftedLimitingBrolinMeasure_neg_eq_integral_escapeDisk,
    shiftedLimitingBrolinMeasure_integral_eq_integral_escapeDisk]
  exact hlim

/-- Measure-level antipodal invariance of the shifted limiting cluster. -/
theorem map_shiftedLimitingBrolinMeasure_neg (c : ℂ) :
    Measure.map Neg.neg (shiftedLimitingBrolinMeasure c) =
      shiftedLimitingBrolinMeasure c := by
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro φ
  rw [integral_map]
  · exact integral_shiftedLimitingBrolinMeasure_neg_eq c φ
  · exact continuous_neg.measurable.aemeasurable
  · exact φ.continuous.aestronglyMeasurable

theorem integral_shiftedLimitingBrolinMeasure_comp_quadratic_eq_integral_escapeDisk
    (c : ℂ) (φ : C_c(ℂ, ℝ)) :
    ∫ z, φ (quadratic c z) ∂shiftedLimitingBrolinMeasure c =
      ∫ z : escapeDisk c, φ (quadratic c (z : ℂ))
        ∂(shiftedBrolinLimitOnEscapeDisk c : Measure (escapeDisk c)) := by
  rw [shiftedLimitingBrolinMeasure, integral_map]
  · exact measurable_subtype_coe.aemeasurable
  · exact (φ.continuous.comp (continuous_quadratic c)).aestronglyMeasurable

noncomputable def truncatedLogKernelCompQuadraticOnEscapeDisk
    (c z : ℂ) (δ : ℝ) (hδ : 0 < δ) :
    BoundedContinuousFunction (escapeDisk c) ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun w : escapeDisk c => truncatedLogKernel z δ (quadratic c (w : ℂ)),
      (continuous_truncatedLogKernel (z := z) hδ).comp
        ((continuous_quadratic c).comp continuous_subtype_val)⟩

theorem integral_truncatedLogKernel_comp_quadratic_preBrolinMeasure_eq_integral_escapeDisk
    (c z : ℂ) {δ : ℝ} (hδ : 0 < δ) (n : ℕ) :
    ∫ w, truncatedLogKernel z δ (quadratic c w) ∂preBrolinMeasure c n =
      ∫ w : escapeDisk c, truncatedLogKernel z δ (quadratic c (w : ℂ))
        ∂preBrolinMeasureOnEscapeDisk c n := by
  rw [preBrolinMeasure_eq_map_preBrolinMeasureOnEscapeDisk, integral_map]
  · exact measurable_subtype_coe.aemeasurable
  · exact ((continuous_truncatedLogKernel (z := z) hδ).comp
      (continuous_quadratic c)).aestronglyMeasurable

theorem integral_truncatedLogKernel_shiftedLimitingBrolinMeasure_comp_quadratic_eq_integral_escapeDisk
    (c z : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    ∫ w, truncatedLogKernel z δ (quadratic c w)
        ∂shiftedLimitingBrolinMeasure c =
      ∫ w : escapeDisk c, truncatedLogKernel z δ (quadratic c (w : ℂ))
        ∂(shiftedBrolinLimitOnEscapeDisk c : Measure (escapeDisk c)) := by
  rw [shiftedLimitingBrolinMeasure, integral_map]
  · exact measurable_subtype_coe.aemeasurable
  · exact ((continuous_truncatedLogKernel (z := z) hδ).comp
      (continuous_quadratic c)).aestronglyMeasurable

theorem integral_truncatedLogKernel_preBrolinProbabilityOnEscapeDisk_succ_comp_quadratic
    (c z : ℂ) {δ : ℝ} (hδ : 0 < δ) (n : ℕ) :
    ∫ w : escapeDisk c, truncatedLogKernel z δ (quadratic c (w : ℂ))
        ∂(preBrolinProbabilityOnEscapeDisk c (n + 1) :
          Measure (escapeDisk c)) =
      ∫ w : escapeDisk c, truncatedLogKernel z δ (w : ℂ)
        ∂(preBrolinProbabilityOnEscapeDisk c n :
          Measure (escapeDisk c)) := by
  have hplane :=
    integral_preBrolinMeasure_succ_comp_quadratic c n
      (fun y : ℂ => truncatedLogKernel z δ y)
  have hleft :
      ∫ w, truncatedLogKernel z δ (quadratic c w)
          ∂preBrolinMeasure c (n + 1) =
        ∫ w : escapeDisk c, truncatedLogKernel z δ (quadratic c (w : ℂ))
          ∂(preBrolinProbabilityOnEscapeDisk c (n + 1) :
            Measure (escapeDisk c)) := by
    rw [integral_truncatedLogKernel_comp_quadratic_preBrolinMeasure_eq_integral_escapeDisk
      c z hδ]
    rfl
  have hright :
      ∫ w, truncatedLogKernel z δ w ∂preBrolinMeasure c n =
        ∫ w : escapeDisk c, truncatedLogKernel z δ (w : ℂ)
          ∂(preBrolinProbabilityOnEscapeDisk c n :
            Measure (escapeDisk c)) := by
    rw [integral_truncatedLogKernel_preBrolinMeasure_eq_integral_escapeDisk c z hδ]
    rfl
  rw [hleft, hright] at hplane
  exact hplane

theorem shiftedBrolinProbabilityOnEscapeDisk_subseq_integral_tendsto_quadratic
    (c : ℂ) (φ : C_c(ℂ, ℝ)) :
    Tendsto
      (fun k =>
        ∫ z : escapeDisk c, φ (quadratic c (z : ℂ))
          ∂(preBrolinProbabilityOnEscapeDisk c
              (shiftedBrolinIndex c k) :
            Measure (escapeDisk c)))
      atTop
      (𝓝 (∫ z : escapeDisk c, φ (quadratic c (z : ℂ))
          ∂(shiftedBrolinLimitOnEscapeDisk c : Measure (escapeDisk c)))) := by
  have h :=
    (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp
      (shiftedBrolinProbabilityOnEscapeDisk_subseq_tendsto c))
      (compactQuadraticRestrictionOnEscapeDisk c φ)
  simpa [compactQuadraticRestrictionOnEscapeDisk] using h

theorem truncatedLogKernel_shiftedBrolinProbabilityOnEscapeDisk_subseq_integral_tendsto_quadratic
    (c z : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto
      (fun k =>
        ∫ w : escapeDisk c, truncatedLogKernel z δ (quadratic c (w : ℂ))
          ∂(preBrolinProbabilityOnEscapeDisk c
              (shiftedBrolinIndex c k) :
            Measure (escapeDisk c)))
      atTop
      (𝓝 (∫ w : escapeDisk c, truncatedLogKernel z δ (quadratic c (w : ℂ))
          ∂(shiftedBrolinLimitOnEscapeDisk c : Measure (escapeDisk c)))) := by
  have h :=
    (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp
      (shiftedBrolinProbabilityOnEscapeDisk_subseq_tendsto c))
      (truncatedLogKernelCompQuadraticOnEscapeDisk c z δ hδ)
  simpa [truncatedLogKernelCompQuadraticOnEscapeDisk] using h

/-- Test-integral form of the unconditional balancedness bridge: the quadratic
pushforward of the shifted cluster limit is the original selected limit. -/
theorem shiftedLimitingBrolinMeasure_quadratic_test_integral_eq_limitingBrolinMeasure
    (c : ℂ) (φ : C_c(ℂ, ℝ)) :
    ∫ z, φ (quadratic c z) ∂shiftedLimitingBrolinMeasure c =
      ∫ z, φ z ∂limitingBrolinMeasure c := by
  have hshift :=
    shiftedBrolinProbabilityOnEscapeDisk_subseq_integral_tendsto_quadratic
      c φ
  have hbase :
      Tendsto
        (fun k =>
          ∫ z : escapeDisk c, φ (z : ℂ)
            ∂(preBrolinProbabilityOnEscapeDisk c
                (brolinLimitSubsequence c
                  (shiftedBrolinLimitSubsequence c k)) :
              Measure (escapeDisk c)))
        atTop
        (𝓝 (∫ z : escapeDisk c, φ (z : ℂ)
          ∂(brolinLimitOnEscapeDisk c : Measure (escapeDisk c)))) :=
    (preBrolinProbabilityOnEscapeDisk_subseq_integral_tendsto c φ).comp
      (shiftedBrolinLimitSubsequence_tendsto_atTop c)
  have hsame :
      Tendsto
        (fun k =>
          ∫ z : escapeDisk c, φ (quadratic c (z : ℂ))
            ∂(preBrolinProbabilityOnEscapeDisk c
                (shiftedBrolinIndex c k) :
              Measure (escapeDisk c)))
        atTop
        (𝓝 (∫ z : escapeDisk c, φ (z : ℂ)
          ∂(brolinLimitOnEscapeDisk c : Measure (escapeDisk c)))) := by
    exact hbase.congr' (by
      filter_upwards [eventually_ge_atTop 0] with k _hk
      simpa [shiftedBrolinIndex] using
        (integral_preBrolinProbabilityOnEscapeDisk_succ_comp_quadratic
          c (brolinLimitSubsequence c (shiftedBrolinLimitSubsequence c k)) φ).symm)
  have hlim :
      (∫ z : escapeDisk c, φ (quadratic c (z : ℂ))
          ∂(shiftedBrolinLimitOnEscapeDisk c : Measure (escapeDisk c))) =
        ∫ z : escapeDisk c, φ (z : ℂ)
          ∂(brolinLimitOnEscapeDisk c : Measure (escapeDisk c)) :=
    tendsto_nhds_unique hshift hsame
  rw [integral_shiftedLimitingBrolinMeasure_comp_quadratic_eq_integral_escapeDisk,
    integral_limitingBrolinMeasure_eq_integral_escapeDisk]
  exact hlim

/-- Truncated-potential form of shifted balancedness.  The compactness-selected
shifted limit pushes forward to the original limiting measure not only on
compactly supported tests, but also on the logarithmic kernels after positive
truncation. -/
theorem shiftedLimitingBrolinMeasure_truncatedLogKernel_comp_quadratic_integral_eq_limitingBrolinMeasure
    (c z : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    ∫ w, truncatedLogKernel z δ (quadratic c w)
        ∂shiftedLimitingBrolinMeasure c =
      ∫ w, truncatedLogKernel z δ w ∂limitingBrolinMeasure c := by
  have hshift :=
    truncatedLogKernel_shiftedBrolinProbabilityOnEscapeDisk_subseq_integral_tendsto_quadratic
      c z hδ
  have hbase :
      Tendsto
        (fun k =>
          ∫ w : escapeDisk c, truncatedLogKernel z δ (w : ℂ)
            ∂(preBrolinProbabilityOnEscapeDisk c
                (brolinLimitSubsequence c
                  (shiftedBrolinLimitSubsequence c k)) :
              Measure (escapeDisk c)))
        atTop
        (𝓝 (∫ w : escapeDisk c, truncatedLogKernel z δ (w : ℂ)
          ∂(brolinLimitOnEscapeDisk c : Measure (escapeDisk c)))) :=
    (truncatedLogKernel_preBrolinProbabilityOnEscapeDisk_subseq_integral_tendsto
      c z hδ).comp (shiftedBrolinLimitSubsequence_tendsto_atTop c)
  have hsame :
      Tendsto
        (fun k =>
          ∫ w : escapeDisk c, truncatedLogKernel z δ (quadratic c (w : ℂ))
            ∂(preBrolinProbabilityOnEscapeDisk c
                (shiftedBrolinIndex c k) :
              Measure (escapeDisk c)))
        atTop
        (𝓝 (∫ w : escapeDisk c, truncatedLogKernel z δ (w : ℂ)
          ∂(brolinLimitOnEscapeDisk c : Measure (escapeDisk c)))) := by
    exact hbase.congr' (by
      filter_upwards [eventually_ge_atTop 0] with k _hk
      simpa [shiftedBrolinIndex] using
        (integral_truncatedLogKernel_preBrolinProbabilityOnEscapeDisk_succ_comp_quadratic
          c z hδ
          (brolinLimitSubsequence c (shiftedBrolinLimitSubsequence c k))).symm)
  have hlim :
      (∫ w : escapeDisk c, truncatedLogKernel z δ (quadratic c (w : ℂ))
          ∂(shiftedBrolinLimitOnEscapeDisk c : Measure (escapeDisk c))) =
        ∫ w : escapeDisk c, truncatedLogKernel z δ (w : ℂ)
          ∂(brolinLimitOnEscapeDisk c : Measure (escapeDisk c)) :=
    tendsto_nhds_unique hshift hsame
  rw [integral_truncatedLogKernel_shiftedLimitingBrolinMeasure_comp_quadratic_eq_integral_escapeDisk
      c z hδ,
    integral_truncatedLogKernel_limitingBrolinMeasure_eq_integral_escapeDisk c z hδ]
  exact hlim

theorem shiftedBrolinLimitOnEscapeDisk_greenSublevel_preimage_compl_of_pos
    (c : ℂ) {ε : ℝ} (hε : 0 < ε) :
    (shiftedBrolinLimitOnEscapeDisk c : Measure (escapeDisk c))
      (((fun z : escapeDisk c => (z : ℂ)) ⁻¹' (greenSublevel c ε)ᶜ)) = 0 := by
  let G : Set (escapeDisk c) :=
    ((fun z : escapeDisk c => (z : ℂ)) ⁻¹' (greenSublevel c ε)ᶜ)
  have hGopen : IsOpen G := by
    dsimp [G]
    exact ((isClosed_greenSublevel c ε).isOpen_compl).preimage continuous_subtype_val
  have hle :=
    ProbabilityMeasure.le_liminf_measure_open_of_tendsto
      (shiftedBrolinProbabilityOnEscapeDisk_subseq_tendsto c) hGopen
  have hevent :
      ∀ᶠ k in atTop,
        (preBrolinProbabilityOnEscapeDisk c (shiftedBrolinIndex c k) :
          Measure (escapeDisk c)) G = 0 := by
    have hfull :=
      (shiftedBrolinIndex_tendsto_atTop c).eventually
        (eventually_preBrolinMeasureOnEscapeDisk_greenSublevel_preimage_compl_of_pos
          c hε)
    filter_upwards [hfull] with k hk
    simpa [G, preBrolinProbabilityOnEscapeDisk] using hk
  have htend :
      Tendsto
        (fun k =>
          (preBrolinProbabilityOnEscapeDisk c (shiftedBrolinIndex c k) :
            Measure (escapeDisk c)) G)
        atTop (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hevent] with k hk
    exact hk.symm
  have hliminf :
      atTop.liminf
        (fun k =>
          (preBrolinProbabilityOnEscapeDisk c (shiftedBrolinIndex c k) :
            Measure (escapeDisk c)) G) = 0 :=
    htend.liminf_eq
  have hle_zero :
      (shiftedBrolinLimitOnEscapeDisk c : Measure (escapeDisk c)) G ≤ 0 := by
    rw [← hliminf]
    exact hle
  have hGzero :
      (shiftedBrolinLimitOnEscapeDisk c : Measure (escapeDisk c)) G = 0 :=
    le_antisymm hle_zero bot_le
  simpa [G] using hGzero

theorem shiftedLimitingBrolinMeasure_greenSublevel_compl_of_pos
    (c : ℂ) {ε : ℝ} (hε : 0 < ε) :
    shiftedLimitingBrolinMeasure c (greenSublevel c ε)ᶜ = 0 := by
  have hmeas : MeasurableSet (greenSublevel c ε)ᶜ :=
    (measurableSet_greenSublevel c ε).compl
  rw [shiftedLimitingBrolinMeasure, Measure.map_apply measurable_subtype_coe hmeas]
  exact shiftedBrolinLimitOnEscapeDisk_greenSublevel_preimage_compl_of_pos c hε

/-- The shifted compactness limit is carried by the filled Julia set. -/
theorem shiftedLimitingBrolinMeasure_filledJulia_compl (c : ℂ) :
    shiftedLimitingBrolinMeasure c (filledJulia c)ᶜ = 0 := by
  rw [filledJulia_compl_eq_iUnion_greenSublevel_inv_nat_succ_compl c]
  apply measure_iUnion_null
  intro n
  exact shiftedLimitingBrolinMeasure_greenSublevel_compl_of_pos c (by positivity)

/-- The shifted compactness limit is another probability measure on `K_c`. -/
theorem shiftedLimitingBrolinMeasure_isProbOn_filledJulia (c : ℂ) :
    IsProbOn (shiftedLimitingBrolinMeasure c) (filledJulia c) :=
  ⟨instIsProbabilityMeasure_shiftedLimitingBrolinMeasure c,
    shiftedLimitingBrolinMeasure_filledJulia_compl c⟩

/-- Carrier-only lower bound for the shifted limiting potential at every point
of the fixed escape disk. -/
theorem logPotential_shiftedLimitingBrolinMeasure_lower_bound_of_mem_escapeDisk
    {c z : ℂ} (hz : z ∈ escapeDisk c) :
    - Real.log (2 * max 2 ‖c‖) ≤
      logPotential (shiftedLimitingBrolinMeasure c) z :=
  logPotential_lower_bound_of_isProbOn_filledJulia_of_mem_escapeDisk
    (shiftedLimitingBrolinMeasure_isProbOn_filledJulia c) hz

/-- Filled-Julia specialization of the carrier-only shifted potential lower
bound. -/
theorem logPotential_shiftedLimitingBrolinMeasure_lower_bound_of_mem_filledJulia
    {c z : ℂ} (hz : z ∈ filledJulia c) :
    - Real.log (2 * max 2 ‖c‖) ≤
      logPotential (shiftedLimitingBrolinMeasure c) z :=
  logPotential_shiftedLimitingBrolinMeasure_lower_bound_of_mem_escapeDisk
    (mem_escapeDisk_of_mem_filledJulia hz)

/-- Carrier-only upper bound for the negative shifted potential on `K_c`. -/
theorem neg_logPotential_shiftedLimitingBrolinMeasure_upper_bound_of_mem_filledJulia
    {c z : ℂ} (hz : z ∈ filledJulia c) :
    - logPotential (shiftedLimitingBrolinMeasure c) z ≤
      Real.log (2 * max 2 ‖c‖) := by
  have h :=
    logPotential_shiftedLimitingBrolinMeasure_lower_bound_of_mem_filledJulia
      (c := c) (z := z) hz
  linarith

theorem integral_truncatedLogKernel_shiftedLimitingBrolinMeasure_eq_integral_escapeDisk
    (c z : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    ∫ w, truncatedLogKernel z δ w ∂shiftedLimitingBrolinMeasure c =
      ∫ w : escapeDisk c, truncatedLogKernel z δ (w : ℂ)
        ∂(shiftedBrolinLimitOnEscapeDisk c : Measure (escapeDisk c)) := by
  rw [shiftedLimitingBrolinMeasure, integral_map]
  · exact measurable_subtype_coe.aemeasurable
  · exact (continuous_truncatedLogKernel (z := z) hδ).aestronglyMeasurable

theorem truncatedLogKernel_preBrolinMeasure_shiftedSubseq_integral_tendsto_shiftedLimiting
    (c z : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto
      (fun k =>
        ∫ w, truncatedLogKernel z δ w
          ∂preBrolinMeasure c (shiftedBrolinIndex c k))
      atTop
      (𝓝 (∫ w, truncatedLogKernel z δ w ∂shiftedLimitingBrolinMeasure c)) := by
  have h :=
    (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp
      (shiftedBrolinProbabilityOnEscapeDisk_subseq_tendsto c))
      (truncatedLogKernelOnEscapeDisk c z δ hδ)
  rw [integral_truncatedLogKernel_shiftedLimitingBrolinMeasure_eq_integral_escapeDisk
    c z hδ]
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 0] with k _hk
  rw [integral_truncatedLogKernel_preBrolinMeasure_eq_integral_escapeDisk c z hδ]
  rfl

theorem eventually_logPotential_preBrolinMeasure_shiftedSubseq_eq_integral_truncatedLogKernel
    (c z : ℂ) {ε δ : ℝ} (hε : 0 < ε)
    (hsep : ∀ w : ℂ, w ∈ greenSublevel c ε → δ ≤ ‖z - w‖) :
    ∀ᶠ k in atTop,
      logPotential (preBrolinMeasure c (shiftedBrolinIndex c k)) z =
        ∫ w, truncatedLogKernel z δ w
          ∂preBrolinMeasure c (shiftedBrolinIndex c k) := by
  have hfull :=
    (shiftedBrolinIndex_tendsto_atTop c).eventually
      (eventually_preBrolinMeasure_greenSublevel_compl_of_pos c hε)
  filter_upwards [hfull] with k hk
  exact logPotential_eq_integral_truncatedLogKernel_of_greenSublevel_support hk hsep

theorem logPotential_shiftedLimitingBrolinMeasure_eq_integral_truncatedLogKernel
    (c z : ℂ) {ε δ : ℝ} (hε : 0 < ε)
    (hsep : ∀ w : ℂ, w ∈ greenSublevel c ε → δ ≤ ‖z - w‖) :
    logPotential (shiftedLimitingBrolinMeasure c) z =
      ∫ w, truncatedLogKernel z δ w ∂shiftedLimitingBrolinMeasure c :=
  logPotential_eq_integral_truncatedLogKernel_of_greenSublevel_support
    (shiftedLimitingBrolinMeasure_greenSublevel_compl_of_pos c hε) hsep

/-- The shifted cluster limit has the same exterior logarithmic-potential
limit as the original Brolin cluster.  This is the core uniqueness substrate
for proving that the compactness-selected limit is independent of shifting. -/
theorem shiftedLimitingBrolinMeasure_hasSubseqLogPotentialLimit (c : ℂ) :
    ∀ ⦃z : ℂ⦄, z ∉ filledJulia c →
      Tendsto
        (fun k => - logPotential (preBrolinMeasure c (shiftedBrolinIndex c k)) z)
        atTop (𝓝 (- logPotential (shiftedLimitingBrolinMeasure c) z)) := by
  intro z hz
  have hGne : greenFunctionDyn c z ≠ 0 := by
    intro hzero
    exact hz ((greenFunctionDyn_eq_zero_iff c z).mp hzero)
  have hGpos : 0 < greenFunctionDyn c z :=
    lt_of_le_of_ne (greenFunctionDyn_nonneg c z) (by simpa [eq_comm] using hGne)
  let ε : ℝ := greenFunctionDyn c z / 2
  have hεpos : 0 < ε := by
    dsimp [ε]
    linarith
  have hεlt : ε < greenFunctionDyn c z := by
    dsimp [ε]
    linarith
  obtain ⟨δ, hδpos, hsep⟩ :=
    exists_pos_le_norm_of_greenSublevel_of_lt_green
      (c := c) (z := z) (ε := ε) hεlt
  have htrunc :=
    truncatedLogKernel_preBrolinMeasure_shiftedSubseq_integral_tendsto_shiftedLimiting
      c z hδpos
  have hlim :=
    logPotential_shiftedLimitingBrolinMeasure_eq_integral_truncatedLogKernel
      c z hεpos hsep
  have hevent :=
    eventually_logPotential_preBrolinMeasure_shiftedSubseq_eq_integral_truncatedLogKernel
      c z hεpos hsep
  have hlog :
      Tendsto
        (fun k => logPotential
          (preBrolinMeasure c (shiftedBrolinIndex c k)) z)
        atTop (𝓝 (logPotential (shiftedLimitingBrolinMeasure c) z)) := by
    rw [hlim]
    exact htrunc.congr' (by
      filter_upwards [hevent] with k hk
      exact hk.symm)
  simpa using hlog.neg

end Bottcher
