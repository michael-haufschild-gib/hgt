import Mathlib

/-!
# Extracting a root of an analytic function

At a zero of an analytic function that is not identically zero nearby, one linear factor can be
divided out and the quotient stays analytic.  Mathlib supplies the local normal form
`f z = (z - a)^n • g z` with `g a ≠ 0`; the content here is that the exponent is at least one at a
zero, so the normal form can be rewritten with a single explicit linear factor.

This is the first step of writing an analytic function on a disc as its zero polynomial times a
zero-free factor, which is what a minimum-modulus estimate consumes.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- **One linear factor comes out at a zero.**  If `f` is analytic at `a`, vanishes there, and is
not identically zero near `a`, then near `a` it is `(z - a)` times an analytic function. -/
theorem exists_factor_of_root {f : ℂ → ℂ} {a : ℂ} (hf : AnalyticAt ℂ f a)
    (hne : ¬ ∀ᶠ z in 𝓝 a, f z = 0) (hfa : f a = 0) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g a ∧ ∀ᶠ z in 𝓝 a, f z = (z - a) * g z := by
  obtain ⟨n, g₀, hg₀, hg₀0, hloc⟩ := hf.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hne
  have hn : 1 ≤ n := by
    by_contra hcon
    have hn0 : n = 0 := by omega
    have hself := hloc.self_of_nhds
    rw [hn0] at hself
    simp only [sub_self, pow_zero, one_smul] at hself
    rw [hfa] at hself
    exact hg₀0 hself.symm
  refine ⟨fun z => (z - a) ^ (n - 1) * g₀ z, ?_, ?_⟩
  · exact (((analyticAt_id).sub analyticAt_const).pow _).mul hg₀
  · filter_upwards [hloc] with z hz
    rw [hz, smul_eq_mul, ← mul_assoc, ← pow_succ']
    congr 2
    omega

/-- **The quotient is analytic away from the zero as well.**  Combining the local factor with the
elementary quotient off the zero: on any punctured neighbourhood the same `g` is `f z / (z - a)`. -/
theorem eq_div_of_factor {f g : ℂ → ℂ} {a : ℂ}
    (hfac : ∀ᶠ z in 𝓝 a, f z = (z - a) * g z) :
    ∀ᶠ z in 𝓝[≠] a, g z = f z / (z - a) := by
  have hmem : ∀ᶠ z in 𝓝[≠] a, f z = (z - a) * g z := nhdsWithin_le_nhds hfac
  filter_upwards [hmem, self_mem_nhdsWithin] with z hz hzne
  have hsub : z - a ≠ 0 := sub_ne_zero.mpr hzne
  rw [hz, mul_comm, mul_div_assoc, div_self hsub, mul_one]

/-- **The factor is global.**  On any open set where `f` is analytic, one linear factor at a zero
divides out with an analytic quotient on the whole set. -/
theorem exists_global_factor_of_root {f : ℂ → ℂ} {U : Set ℂ}
    (hf : AnalyticOnNhd ℂ f U) {a : ℂ} (ha : a ∈ U) (hfa : f a = 0)
    (hne : ¬ ∀ᶠ z in 𝓝 a, f z = 0) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g U ∧ ∀ z ∈ U, f z = (z - a) * g z := by
  classical
  obtain ⟨g₁, hg₁, hloc⟩ := exists_factor_of_root (hf a ha) hne hfa
  refine ⟨fun z => if z = a then g₁ a else f z / (z - a), ?_, ?_⟩
  · intro z hz
    by_cases hza : z = a
    · rw [hza]
      refine hg₁.congr ?_
      filter_upwards [hloc] with w hw
      by_cases hwa : w = a
      · simp [hwa]
      · have hwne : w - a ≠ 0 := sub_ne_zero.mpr hwa
        simp only [if_neg hwa]
        rw [hw]
        field_simp
    · have hzne : z - a ≠ 0 := sub_ne_zero.mpr hza
      have hbase : AnalyticAt ℂ (fun w => f w / (w - a)) z :=
        (hf z hz).div (analyticAt_id.sub analyticAt_const) hzne
      refine hbase.congr ?_
      filter_upwards [eventually_ne_nhds hza] with w hw
      simp only [if_neg hw]
  · intro z hz
    by_cases hza : z = a
    · rw [hza]
      simp [hfa]
    · have hzne : z - a ≠ 0 := sub_ne_zero.mpr hza
      simp only [if_neg hza]
      field_simp

/-- **Full multiplicity comes out.**  At a zero where `f` is not identically zero, the whole power
`(z - a)^n` matching the order divides out globally, and the quotient does not vanish at `a`. -/
theorem exists_pow_factor_of_root {f : ℂ → ℂ} {U : Set ℂ}
    (hf : AnalyticOnNhd ℂ f U) {a : ℂ} (ha : a ∈ U)
    (hne : ¬ ∀ᶠ z in 𝓝 a, f z = 0) :
    ∃ (n : ℕ) (g : ℂ → ℂ), AnalyticOnNhd ℂ g U ∧ g a ≠ 0 ∧
      ∀ z ∈ U, f z = (z - a) ^ n * g z := by
  classical
  obtain ⟨n, g₀, hg₀, hg₀0, hloc⟩ :=
    (hf a ha).exists_eventuallyEq_pow_smul_nonzero_iff.mpr hne
  refine ⟨n, fun z => if z = a then g₀ a else f z / (z - a) ^ n, ?_, by simp [hg₀0], ?_⟩
  · intro z hz
    by_cases hza : z = a
    · rw [hza]
      refine hg₀.congr ?_
      filter_upwards [hloc] with w hw
      by_cases hwa : w = a
      · simp [hwa]
      · have hwne : (w - a) ^ n ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hwa)
        simp only [if_neg hwa]
        rw [hw, smul_eq_mul]
        field_simp
    · have hzne : (z - a) ^ n ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hza)
      have hbase : AnalyticAt ℂ (fun w => f w / (w - a) ^ n) z :=
        (hf z hz).div ((analyticAt_id.sub analyticAt_const).pow _) hzne
      refine hbase.congr ?_
      filter_upwards [eventually_ne_nhds hza] with w hw
      simp only [if_neg hw]
  · intro z hz
    by_cases hza : z = a
    · rw [hza]
      have hself := hloc.self_of_nhds
      simpa using hself
    · have hzne : (z - a) ^ n ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hza)
      simp only [if_neg hza]
      field_simp

/-- **A root of a nonzero entire function has positive finite order.**  The local nonvanishing
hypothesis required by `exists_pow_factor_of_root` is automatic on the connected complex plane
once one value of the entire function is nonzero.  Consequently the exact full power at any root
divides globally, with an entire quotient nonzero at that root. -/
theorem exists_positive_pow_factor_of_entire_root {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f Set.univ) {a : ℂ} (hfa : f a = 0)
    (hne : ∃ z : ℂ, f z ≠ 0) :
    ∃ (n : ℕ) (g : ℂ → ℂ), 0 < n ∧ AnalyticOnNhd ℂ g Set.univ ∧ g a ≠ 0 ∧
      ∀ z : ℂ, f z = (z - a) ^ n * g z := by
  obtain ⟨z, hz⟩ := hne
  have hlocal : ¬ ∀ᶠ w in 𝓝 a, f w = 0 := by
    intro hzero
    have heq : Set.EqOn f 0 Set.univ :=
      hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero
        isPreconnected_univ (Set.mem_univ a) hzero
    exact hz (heq (Set.mem_univ z))
  obtain ⟨n, g, hg, hga, hfactor⟩ :=
    exists_pow_factor_of_root hf (Set.mem_univ a) hlocal
  have hn : 0 < n := by
    by_contra hn
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    have ha := hfactor a (Set.mem_univ a)
    rw [hfa, hn0] at ha
    simp only [pow_zero, one_mul] at ha
    exact hga ha.symm
  exact ⟨n, g, hn, hg, hga, fun z => hfactor z (Set.mem_univ z)⟩

/-- **The quotient inherits non-degeneracy.**  If a factorisation holds on an open set and the
original function is not identically zero near a point, neither is the quotient.  This is what lets
the extraction be iterated: the hypothesis of `exists_pow_factor_of_root` survives each step. -/
theorem not_eventually_zero_of_global_factor {f g : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    {a : ℂ} {n : ℕ} (hfac : ∀ z ∈ U, f z = (z - a) ^ n * g z)
    {b : ℂ} (hb : b ∈ U) (hf : ¬ ∀ᶠ z in 𝓝 b, f z = 0) :
    ¬ ∀ᶠ z in 𝓝 b, g z = 0 := by
  intro hg
  apply hf
  filter_upwards [hg, hU.mem_nhds hb] with z hz hzU
  rw [hfac z hzU, hz, mul_zero]

/-- **A zero of the quotient at a different point was a zero of the original.** -/
theorem eval_eq_zero_of_global_factor {f g : ℂ → ℂ} {U : Set ℂ}
    {a : ℂ} {n : ℕ} (hfac : ∀ z ∈ U, f z = (z - a) ^ n * g z)
    {b : ℂ} (hb : b ∈ U) (hgb : g b = 0) : f b = 0 := by
  rw [hfac b hb, hgb, mul_zero]

/-- **Away from the extracted point, the zeros are exactly the quotient's.** -/
theorem eval_eq_zero_iff_of_global_factor {f g : ℂ → ℂ} {U : Set ℂ}
    {a : ℂ} {n : ℕ} (hfac : ∀ z ∈ U, f z = (z - a) ^ n * g z)
    {b : ℂ} (hb : b ∈ U) (hba : b ≠ a) : f b = 0 ↔ g b = 0 := by
  constructor
  · intro hfb
    have hne : (b - a) ^ n ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hba)
    rw [hfac b hb] at hfb
    exact (mul_eq_zero.mp hfb).resolve_left hne
  · intro hgb
    exact eval_eq_zero_of_global_factor hfac hb hgb

/-! ## Finiteness of the zero set on a compact ball -/

/-- **Zeros are finite on a closed ball.**  An analytic function that is nowhere locally zero has
only finitely many zeros in a closed ball: the zero set is compact and discrete. -/
theorem finite_zeros_closedBall {f : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall c R))
    (hne : ∀ z ∈ Metric.closedBall c R, ¬ ∀ᶠ w in 𝓝 z, f w = 0) :
    {z ∈ Metric.closedBall c R | f z = 0}.Finite := by
  classical
  have hKcomp : IsCompact (Metric.closedBall c R) := isCompact_closedBall c R
  have hKclosed : IsClosed (Metric.closedBall c R) := Metric.isClosed_closedBall
  have hcont : ContinuousOn f (Metric.closedBall c R) := hf.continuousOn
  have hset : {z ∈ Metric.closedBall c R | f z = 0}
      = Metric.closedBall c R ∩ f ⁻¹' {0} := by
    ext z
    simp [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage]
  have hclosed : IsClosed {z ∈ Metric.closedBall c R | f z = 0} := by
    rw [hset]
    exact hcont.preimage_isClosed_of_isClosed hKclosed isClosed_singleton
  have hsub : {z ∈ Metric.closedBall c R | f z = 0} ⊆ Metric.closedBall c R :=
    fun z hz => hz.1
  have hcomp : IsCompact {z ∈ Metric.closedBall c R | f z = 0} :=
    hKcomp.of_isClosed_subset hclosed hsub
  refine hcomp.finite ?_
  rw [isDiscrete_iff_nhdsNE]
  intro x hx
  have hxK : x ∈ Metric.closedBall c R := hx.1
  have hdich := (hf x hxK).eventually_eq_zero_or_eventually_ne_zero
  have hev : ∀ᶠ z in 𝓝[≠] x, f z ≠ 0 := by
    rcases hdich with h | h
    · exact absurd h (hne x hxK)
    · exact h
  rw [Filter.inf_principal_eq_bot]
  filter_upwards [hev] with z hz
  intro hzS
  exact hz hzS.2

/-! ## Extracting a whole finite set of zeros -/

/-- **All the listed zeros come out at once.**  Over any finite set of points of an open set, an
analytic function that is nowhere locally zero factors as a product of powers of linear factors times
an analytic function that does not vanish at any of those points. -/
theorem exists_prod_factor_of_finset {U : Set ℂ} (hU : IsOpen U) :
    ∀ (T : Finset ℂ), (∀ a ∈ T, a ∈ U) → ∀ f : ℂ → ℂ, AnalyticOnNhd ℂ f U →
      (∀ a ∈ U, ¬ ∀ᶠ z in 𝓝 a, f z = 0) →
      ∃ (m : ℂ → ℕ) (g : ℂ → ℂ), AnalyticOnNhd ℂ g U ∧ (∀ a ∈ T, g a ≠ 0) ∧
        ∀ z ∈ U, f z = (∏ a ∈ T, (z - a) ^ (m a)) * g z := by
  classical
  intro T
  induction T using Finset.induction with
  | empty =>
      intro _ f hf _
      exact ⟨fun _ => 0, f, hf, by simp, by simp⟩
  | insert a T ha ih =>
      intro hmem f hf hnz
      have haU : a ∈ U := hmem a (Finset.mem_insert_self a T)
      obtain ⟨n, g₁, hg₁, hg₁a, hfac⟩ := exists_pow_factor_of_root hf haU (hnz a haU)
      have hnz₁ : ∀ b ∈ U, ¬ ∀ᶠ z in 𝓝 b, g₁ z = 0 := fun b hb =>
        not_eventually_zero_of_global_factor hU hfac hb (hnz b hb)
      obtain ⟨m, g, hg, hgT, hfac₂⟩ :=
        ih (fun b hb => hmem b (Finset.mem_insert_of_mem hb)) g₁ hg₁ hnz₁
      refine ⟨fun b => if b = a then n else m b, g, hg, ?_, ?_⟩
      · intro b hb
        rcases Finset.mem_insert.mp hb with rfl | hbT
        · intro hgb
          apply hg₁a
          rw [hfac₂ b haU, hgb, mul_zero]
        · exact hgT b hbT
      · intro z hz
        rw [hfac z hz, hfac₂ z hz, Finset.prod_insert ha]
        have hcongr : ∏ b ∈ T, (z - b) ^ (if b = a then n else m b)
            = ∏ b ∈ T, (z - b) ^ (m b) := by
          refine Finset.prod_congr rfl ?_
          intro b hb
          have hbne : b ≠ a := fun h => ha (h ▸ hb)
          rw [if_neg hbne]
        rw [hcongr]
        simp only [if_true]
        ring

/-- **The zero-free factorisation on a ball.**  An analytic function that is nowhere locally zero
factors on any open set as a finite product of powers of linear factors, indexed by its zeros in a
closed ball, times an analytic function with no zeros in that ball. -/
theorem exists_zero_free_factor_closedBall {f : ℂ → ℂ} {c : ℂ} {R : ℝ} {U : Set ℂ}
    (hU : IsOpen U) (hball : Metric.closedBall c R ⊆ U)
    (hf : AnalyticOnNhd ℂ f U) (hnz : ∀ a ∈ U, ¬ ∀ᶠ z in 𝓝 a, f z = 0) :
    ∃ (T : Finset ℂ) (m : ℂ → ℕ) (g : ℂ → ℂ),
      AnalyticOnNhd ℂ g U ∧ (∀ z ∈ Metric.closedBall c R, g z ≠ 0) ∧
      (∀ a ∈ T, a ∈ Metric.closedBall c R) ∧
      ∀ z ∈ U, f z = (∏ a ∈ T, (z - a) ^ (m a)) * g z := by
  classical
  have hfin : {z ∈ Metric.closedBall c R | f z = 0}.Finite :=
    finite_zeros_closedBall (hf.mono hball) (fun z hz => hnz z (hball hz))
  set T : Finset ℂ := hfin.toFinset with hTdef
  have hTmem : ∀ a ∈ T, a ∈ Metric.closedBall c R := by
    intro a ha
    have := hfin.mem_toFinset.mp ha
    exact this.1
  obtain ⟨m, g, hg, hgT, hfac⟩ :=
    exists_prod_factor_of_finset hU T (fun a ha => hball (hTmem a ha)) f hf hnz
  refine ⟨T, m, g, hg, ?_, hTmem, hfac⟩
  intro z hz hgz
  have hfz : f z = 0 := by
    rw [hfac z (hball hz), hgz, mul_zero]
  have hzT : z ∈ T := hfin.mem_toFinset.mpr ⟨hz, hfz⟩
  exact hgT z hzT hgz

/-! ## The factorisation as a polynomial times a zero-free function -/

/-- **`f = P · g` with `P` monic and `g` zero-free on the ball.**  This is the form a
minimum-modulus estimate consumes: the polynomial carries all the zeros in the ball and the other
factor is bounded below there by any zero-free lower bound. -/
theorem exists_polynomial_factor_closedBall {f : ℂ → ℂ} {c : ℂ} {R : ℝ} {U : Set ℂ}
    (hU : IsOpen U) (hball : Metric.closedBall c R ⊆ U)
    (hf : AnalyticOnNhd ℂ f U) (hnz : ∀ a ∈ U, ¬ ∀ᶠ z in 𝓝 a, f z = 0) :
    ∃ (P : Polynomial ℂ) (g : ℂ → ℂ), P.Monic ∧ AnalyticOnNhd ℂ g U ∧
      (∀ z ∈ Metric.closedBall c R, g z ≠ 0) ∧ ∀ z ∈ U, f z = P.eval z * g z := by
  classical
  obtain ⟨T, m, g, hg, hgfree, hTmem, hfac⟩ :=
    exists_zero_free_factor_closedBall hU hball hf hnz
  refine ⟨∏ a ∈ T, (Polynomial.X - Polynomial.C a) ^ (m a), g, ?_, hg, hgfree, ?_⟩
  · refine Polynomial.monic_prod_of_monic _ _ ?_
    intro a _
    exact (Polynomial.monic_X_sub_C a).pow _
  · intro z hz
    rw [hfac z hz]
    congr 1
    rw [Polynomial.eval_prod]
    refine Finset.prod_congr rfl ?_
    intro a _
    rw [Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]

/-- The degree of the extracted polynomial is the total multiplicity. -/
theorem natDegree_prod_X_sub_C_pow (T : Finset ℂ) (m : ℂ → ℕ) :
    (∏ a ∈ T, (Polynomial.X - Polynomial.C a) ^ (m a)).natDegree = ∑ a ∈ T, m a := by
  classical
  rw [Polynomial.natDegree_prod]
  · refine Finset.sum_congr rfl ?_
    intro a _
    rw [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one]
  · intro a _
    exact ((Polynomial.monic_X_sub_C a).pow (m a)).ne_zero

/-- **The factorisation with its degree exposed.**  The same statement as
`exists_polynomial_factor_closedBall`, additionally reporting that the degree of the polynomial is
the total multiplicity of the zeros in the ball — the quantity a counting estimate bounds. -/
theorem exists_polynomial_factor_closedBall_degree {f : ℂ → ℂ} {c : ℂ} {R : ℝ} {U : Set ℂ}
    (hU : IsOpen U) (hball : Metric.closedBall c R ⊆ U)
    (hf : AnalyticOnNhd ℂ f U) (hnz : ∀ a ∈ U, ¬ ∀ᶠ z in 𝓝 a, f z = 0) :
    ∃ (T : Finset ℂ) (m : ℂ → ℕ) (P : Polynomial ℂ) (g : ℂ → ℂ),
      P.Monic ∧ P.natDegree = ∑ a ∈ T, m a ∧
      (∀ a ∈ T, a ∈ Metric.closedBall c R) ∧
      AnalyticOnNhd ℂ g U ∧ (∀ z ∈ Metric.closedBall c R, g z ≠ 0) ∧
      ∀ z ∈ U, f z = P.eval z * g z := by
  classical
  obtain ⟨T, m, g, hg, hgfree, hTmem, hfac⟩ :=
    exists_zero_free_factor_closedBall hU hball hf hnz
  refine ⟨T, m, ∏ a ∈ T, (Polynomial.X - Polynomial.C a) ^ (m a), g, ?_,
    natDegree_prod_X_sub_C_pow T m, hTmem, hg, hgfree, ?_⟩
  · refine Polynomial.monic_prod_of_monic _ _ ?_
    intro a _
    exact (Polynomial.monic_X_sub_C a).pow _
  · intro z hz
    rw [hfac z hz]
    congr 1
    rw [Polynomial.eval_prod]
    refine Finset.prod_congr rfl ?_
    intro a _
    rw [Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]

/-- **The extracted polynomial has no roots outside the extraction set.**  This is what lets a
statement phrased on `Polynomial.roots` be applied to the polynomial built from the extraction. -/
theorem mem_of_mem_roots_prod_X_sub_C_pow {T : Finset ℂ} {m : ℂ → ℕ} {x : ℂ}
    (hx : x ∈ (∏ a ∈ T, (Polynomial.X - Polynomial.C a) ^ (m a)).roots) : x ∈ T := by
  classical
  by_contra hxT
  have hmonic : (∏ a ∈ T, (Polynomial.X - Polynomial.C a) ^ (m a)).Monic := by
    refine Polynomial.monic_prod_of_monic _ _ ?_
    intro a _
    exact (Polynomial.monic_X_sub_C a).pow _
  have hroot : (∏ a ∈ T, (Polynomial.X - Polynomial.C a) ^ (m a)).IsRoot x :=
    (Polynomial.mem_roots hmonic.ne_zero).mp hx
  have heval : (∏ a ∈ T, (Polynomial.X - Polynomial.C a) ^ (m a)).eval x
      = ∏ a ∈ T, (x - a) ^ (m a) := by
    rw [Polynomial.eval_prod]
    refine Finset.prod_congr rfl ?_
    intro a _
    rw [Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  have hne : ∏ a ∈ T, (x - a) ^ (m a) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr ?_
    intro a ha
    refine pow_ne_zero _ (sub_ne_zero.mpr ?_)
    intro hxa
    exact hxT (hxa ▸ ha)
  rw [Polynomial.IsRoot, heval] at hroot
  exact hne hroot

/-- **The displacement factors through a power of the variable.**  For an analytic `g` that is not
locally constant at the origin, `g z − g 0 = z^n · G z` with `G` analytic on the whole set and
`G 0 ≠ 0`.

This is the normalisation that lets a minimum-modulus estimate be applied to the displacement: the
displacement itself vanishes at the origin, but `G` does not, so the counting bound — which needs a
nonzero central value — applies to `G`. -/
theorem exists_pow_factor_sub_const {g : ℂ → ℂ} {U : Set ℂ}
    (h0 : (0 : ℂ) ∈ U) (hg : AnalyticOnNhd ℂ g U)
    (hnc : ¬ ∀ᶠ z in 𝓝 (0 : ℂ), g z = g 0) :
    ∃ (n : ℕ) (G : ℂ → ℂ), AnalyticOnNhd ℂ G U ∧ G 0 ≠ 0 ∧
      ∀ z ∈ U, g z - g 0 = z ^ n * G z := by
  have hsub : AnalyticOnNhd ℂ (fun z => g z - g 0) U := hg.sub analyticOnNhd_const
  have hne : ¬ ∀ᶠ z in 𝓝 (0 : ℂ), (fun z => g z - g 0) z = 0 := by
    intro hcon
    refine hnc ?_
    filter_upwards [hcon] with z hz
    exact sub_eq_zero.mp hz
  obtain ⟨n, G, hG, hG0, hfac⟩ := exists_pow_factor_of_root hsub h0 hne
  refine ⟨n, G, hG, hG0, ?_⟩
  intro z hz
  have := hfac z hz
  simpa using this

end GaloisForLFunctions.HTGeometry
