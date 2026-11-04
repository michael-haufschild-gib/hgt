import GaloisForLFunctions.ZeroConfigurationGeometry.RealityLeavesOnlyThroughCollision

/-!
# Purity leaves only through collision

The function-field model of the field. For a curve of genus `g` over `𝔽_q` the configuration is the
set of `2g` normalized Frobenius eigenvalues `α_j/√q`, closed under `z ↦ z⁻¹` and under
conjugation; Weil's theorem (purity) puts it on the unit circle. Pairing `z` with `z⁻¹` gives the
**trace points** `z + z⁻¹`, the roots of a real **trace polynomial** `Q` of degree `g`, and the
eigenvalues are the roots of the **circle polynomial** `z^g Q(z + z⁻¹)` (`circlePoly`).

* **Dictionary** (`isPure_iff_circle`). The roots of the circle polynomial lie on the unit circle
  iff `Q` is **pure** (`IsPure`): real-rooted with every root in `[−2, 2]`. The bridge is the
  trace of a unit: for `z ≠ 0`, `z + z⁻¹` is a real number in `[−2, 2]` iff `|z| = 1`
  (`norm_eq_one_of_add_inv`, `add_inv_of_norm_eq_one`).
* **Simple pure configurations are stable** (`eventually_pure_of_simple`). A pure trace
  polynomial of full degree with simple roots, none at `±2`, stays pure under small deformation:
  each root changes sign inside `(−2, 2)`, the sign changes persist, and the roots they produce
  exhaust the degree.
* **Purity is closed** (`isClosed_pure`). A pure `Q` obeys `|Q(y)| ≥ |lc Q| (|y| − 2)^{deg Q}` for
  `|y| ≥ 2` (`abs_leadingCoeff_mul_le_abs_eval`); the bound passes to coefficient limits and keeps
  every limit root in `[−2, 2]`.
* **The exit theorem** (`exists_first_frobenius_collision`, `exists_first_circle_collision`).
  Along a continuous family of trace polynomials of fixed degree, purity is lost only at a **Frobenius
  collision** (`IsFrobeniusCollision`): a double trace root — two eigenvalue pairs meeting on the
  circle — or a trace root at `±2` — an eigenvalue meeting its inverse at `±1`. A deformation
  that meets no Frobenius collision while pure ends pure
  (`isPure_of_forall_not_frobeniusCollision`).

In this model the deformation question of the field has a complete answer without spectral input:
purity is closed, and along every family it can only end on the collision locus.
-/

open Polynomial Filter Topology Set Complex
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.ZeroConfigurationGeometry

/-- A real trace polynomial is **pure** when it is real-rooted with every root in `[−2, 2]`. -/
def IsPure (Q : ℝ[X]) : Prop := Q.Splits ∧ ∀ x ∈ Q.roots, |x| ≤ 2

/-- A **Frobenius collision**: a real double root, or a root at `±2`. -/
def IsFrobeniusCollision (Q : ℝ[X]) : Prop := IsCollision Q ∨ Q.IsRoot 2 ∨ Q.IsRoot (-2)

theorem aeval_ofReal_eq (Q : ℝ[X]) (x : ℝ) : (aeval (x : ℂ) Q : ℂ) = ((Q.eval x : ℝ) : ℂ) := by
  simpa using aeval_algebraMap_apply_eq_algebraMap_eval (A := ℂ) x Q

/-- **Purity through complex roots**: every complex root lies in `[−2, 2]`. -/
theorem isPure_iff_complex {Q : ℝ[X]} (hQ : Q ≠ 0) :
    IsPure Q ↔ ∀ z : ℂ, (aeval z Q : ℂ) = 0 → z.im = 0 ∧ |z.re| ≤ 2 := by
  constructor
  · rintro ⟨hs, hr⟩ z hz
    have him := HTGeometry.im_eq_zero_of_splits hs hQ hz
    refine ⟨him, hr _ ((mem_roots hQ).mpr ?_)⟩
    have hzre : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [him])
    rw [hzre, aeval_ofReal_eq] at hz
    exact_mod_cast hz
  · intro h
    refine ⟨HTGeometry.splits_of_forall_complex_root_real _ Q le_rfl fun z hz => (h z hz).1,
      fun x hx => ?_⟩
    have hx' : (aeval (x : ℂ) Q : ℂ) = 0 := by
      rw [aeval_ofReal_eq, ((mem_roots hQ).mp hx).eq_zero, ofReal_zero]
    simpa using (h _ hx').2

/-! ### The circle dictionary -/

/-- The **circle polynomial** `z^g Q(z + z⁻¹)` of a trace polynomial of degree at most `g`. -/
def circlePoly (g : ℕ) (Q : ℝ[X]) : ℝ[X] :=
  ∑ k ∈ Finset.range (g + 1), C (Q.coeff k) * X ^ (g - k) * (X ^ 2 + 1) ^ k

theorem aeval_circlePoly {g : ℕ} {Q : ℝ[X]} (hQ : Q.natDegree ≤ g) {z : ℂ} (hz : z ≠ 0) :
    (aeval z (circlePoly g Q) : ℂ) = z ^ g * aeval (z + z⁻¹) Q := by
  rw [circlePoly, map_sum, aeval_eq_sum_range' (Nat.lt_succ_of_le hQ), Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ g := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hzk : z ^ k * (z + z⁻¹) ^ k = (z ^ 2 + 1) ^ k := by
    rw [← mul_pow, mul_add, mul_inv_cancel₀ hz]; ring
  have hg : z ^ g = z ^ (g - k) * z ^ k := by rw [← pow_add, Nat.sub_add_cancel hk']
  simp only [map_mul, map_pow, aeval_C, aeval_X, map_add, map_one, Complex.real_smul,
    Complex.coe_algebraMap, hg]
  linear_combination (-((Q.coeff k : ℂ)) * z ^ (g - k)) * hzk

theorem aeval_zero_circlePoly (g : ℕ) (Q : ℝ[X]) :
    (aeval (0 : ℂ) (circlePoly g Q) : ℂ) = (Q.coeff g : ℂ) := by
  rw [circlePoly, map_sum, Finset.sum_eq_single g]
  · simp
  · intro k hk hkg
    have : 0 < g - k :=
      Nat.sub_pos_of_lt (lt_of_le_of_ne (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)) hkg)
    simp [zero_pow this.ne']
  · intro h; exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self g)) h

/-- A trace in `[−2, 2]` comes from a unit. -/
theorem norm_eq_one_of_add_inv {z : ℂ} (hz : z ≠ 0) {t : ℝ} (ht : z + z⁻¹ = t) (h2 : |t| ≤ 2) :
    ‖z‖ = 1 := by
  have hq : z * z + 1 = (t : ℂ) * z := by
    rw [← ht, add_mul, inv_mul_cancel₀ hz]
  have h1 := congrArg Complex.re hq
  have hi := congrArg Complex.im hq
  simp only [add_re, mul_re, one_re, ofReal_re, ofReal_im, zero_mul, sub_zero, add_im, mul_im,
    one_im, add_zero] at h1 hi
  have ht2 : t ^ 2 ≤ 4 := by
    have := abs_le.mp h2; nlinarith
  have key : z.re * z.re + z.im * z.im = 1 := by
    have hfac : z.im * (2 * z.re - t) = 0 := by linear_combination hi
    rcases mul_eq_zero.mp hfac with hb | ha
    · rw [hb] at h1
      have hsq : (2 * z.re - t) ^ 2 ≤ 0 := by nlinarith
      have h0 : 2 * z.re - t = 0 := by nlinarith [sq_nonneg (2 * z.re - t)]
      rw [hb]
      nlinarith
    · have : t = 2 * z.re := by linarith
      rw [this] at h1
      linarith
  have hN := normSq_eq_norm_sq z
  rw [normSq_apply, key] at hN
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg z) two_ne_zero).mp hN.symm

/-- A unit has its trace in `[−2, 2]`. -/
theorem add_inv_of_norm_eq_one {z : ℂ} (h : ‖z‖ = 1) :
    z + z⁻¹ = ((2 * z.re : ℝ) : ℂ) ∧ |2 * z.re| ≤ 2 := by
  have hN : normSq z = 1 := by rw [normSq_eq_norm_sq, h, one_pow]
  have hinv : z⁻¹ = conj z := by rw [inv_def, hN, inv_one, ofReal_one, mul_one]
  refine ⟨by rw [hinv, add_conj], ?_⟩
  rw [abs_mul, abs_two]
  have := abs_re_le_norm z
  rw [h] at this
  linarith

/-- Every complex trace is the trace of some `z ≠ 0`. -/
theorem exists_add_inv_eq (t : ℂ) : ∃ z : ℂ, z ≠ 0 ∧ z + z⁻¹ = t := by
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (t ^ 2 - 4) two_pos
  set z := (t + s) / 2 with hzdef
  have hq : z * z - t * z + 1 = 0 := by rw [hzdef]; linear_combination (1 / 4 : ℂ) * hs
  have hz : z ≠ 0 := fun h => by rw [h] at hq; simp at hq
  refine ⟨z, hz, ?_⟩
  have : z + z⁻¹ - t = (z * z - t * z + 1) / z := by field_simp; ring
  rw [hq, zero_div, sub_eq_zero] at this
  exact this

/-- **The circle dictionary.** For a trace polynomial of degree `g`, the roots of the circle
polynomial lie on the unit circle iff the trace polynomial is pure. -/
theorem isPure_iff_circle {g : ℕ} {Q : ℝ[X]} (hdeg : Q.natDegree ≤ g) (hg : Q.coeff g ≠ 0) :
    IsPure Q ↔ ∀ z : ℂ, (aeval z (circlePoly g Q) : ℂ) = 0 → ‖z‖ = 1 := by
  have hQ : Q ≠ 0 := fun h => hg (by rw [h, coeff_zero])
  rw [isPure_iff_complex hQ]
  constructor
  · intro h z hz
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [aeval_zero_circlePoly] at hz
      exact hg (by exact_mod_cast hz)
    rw [aeval_circlePoly hdeg hz0] at hz
    obtain ⟨him, hre⟩ := h _ ((mul_eq_zero.mp hz).resolve_left (pow_ne_zero _ hz0))
    exact norm_eq_one_of_add_inv hz0 (Complex.ext (by simp) (by simp [him])) hre
  · intro h t ht
    obtain ⟨z, hz0, hzt⟩ := exists_add_inv_eq t
    have hzP : (aeval z (circlePoly g Q) : ℂ) = 0 := by
      rw [aeval_circlePoly hdeg hz0, hzt, ht, mul_zero]
    obtain ⟨h1, h2⟩ := add_inv_of_norm_eq_one (h z hzP)
    rw [← hzt, h1]
    simpa using h2

/-! ### Stability, closedness and the exit theorem -/

/-- **Simple pure configurations are stable.** If `P t₀` is pure of degree `n` with no Frobenius
collision, then `P t` is pure for all `t` near `t₀`. -/
theorem eventually_pure_of_simple {P : ℝ → ℝ[X]} {n : ℕ} (hdeg : ∀ t, (P t).natDegree ≤ n)
    (hcont : ∀ j, Continuous fun t => (P t).coeff j) {t₀ : ℝ} (hpure : IsPure (P t₀))
    (hn : (P t₀).natDegree = n) (hsimple : ¬ IsFrobeniusCollision (P t₀)) :
    ∀ᶠ t in 𝓝 t₀, IsPure (P t) := by
  classical
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · refine Eventually.of_forall fun t => ?_
    have hr : (P t).roots = 0 := Multiset.card_eq_zero.mp (by
      have := card_roots' (P t); have := hdeg t; omega)
    exact ⟨splits_iff_card_roots.mpr (by rw [hr, Multiset.card_zero]; have := hdeg t; omega),
      fun x hx => by simp [hr] at hx⟩
  set p := P t₀ with hp
  have hp0 : p ≠ 0 := fun h => by rw [h, natDegree_zero] at hn; omega
  set R := p.roots.toFinset with hR
  have hroot : ∀ r ∈ R, p.IsRoot r := fun r hr =>
    (mem_roots hp0).mp (Multiset.mem_toFinset.mp hr)
  have hderiv : ∀ r ∈ R, p.derivative.eval r ≠ 0 := fun r hr h =>
    hsimple (Or.inl ⟨r, hroot r hr, h⟩)
  -- the roots lie in the open interval `(−2, 2)`
  have hin : ∀ r ∈ R, |r| < 2 := by
    intro r hr
    refine lt_of_le_of_ne (hpure.2 r (Multiset.mem_toFinset.mp hr)) fun h => ?_
    rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 2)).mp h with h' | h'
    · exact hsimple (Or.inr (Or.inl (by rw [← h']; exact hroot r hr)))
    · exact hsimple (Or.inr (Or.inr (by rw [← h']; exact hroot r hr)))
  have hnodup : p.roots.Nodup := by
    refine Multiset.nodup_iff_count_le_one.mpr fun r => ?_
    rw [count_roots]
    by_contra h
    exact hsimple (Or.inl ⟨r, ((one_lt_rootMultiplicity_iff_isRoot hp0).mp (not_le.mp h)).1,
      ((one_lt_rootMultiplicity_iff_isRoot hp0).mp (not_le.mp h)).2⟩)
  have hcard : R.card = n := by
    rw [hR, Multiset.toFinset_card_of_nodup hnodup, splits_iff_card_roots.mp hpure.1, hn]
  -- one radius `ε`: sign changes, disjoint intervals, all inside `(−2, 2)`
  have hsign : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ r ∈ R, p.eval (r - ε) * p.eval (r + ε) < 0 :=
    (Finset.eventually_all R).mpr fun r hr => exists_sign_change (hroot r hr) (hderiv r hr)
  have hsep : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ r ∈ R, ∀ r' ∈ R, r ≠ r' → 2 * ε < |r - r'| := by
    refine (Finset.eventually_all R).mpr fun r _ => (Finset.eventually_all R).mpr fun r' _ => ?_
    by_cases hrr : r = r'
    · exact Eventually.of_forall fun _ h => absurd hrr h
    · filter_upwards [Ioo_mem_nhdsGT (half_pos (abs_pos.mpr (sub_ne_zero.mpr hrr)))] with ε hε _
      linarith [hε.2]
  have hbd : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ r ∈ R, ε < 2 - |r| :=
    (Finset.eventually_all R).mpr fun r hr => by
      filter_upwards [Ioo_mem_nhdsGT (sub_pos.mpr (hin r hr))] with ε hε using hε.2
  have hpos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := eventually_mem_nhdsWithin
  obtain ⟨ε, hε0, hεs, hεg, hεb⟩ := (hpos.and (hsign.and (hsep.and hbd))).exists
  have hev := continuous_eval_family hdeg hcont
  have hT : ∀ᶠ t in 𝓝 t₀, ∀ r ∈ R, (P t).eval (r - ε) * (P t).eval (r + ε) < 0 :=
    (Finset.eventually_all R).mpr fun r hr =>
      ((hev _).mul (hev _)).continuousAt.eventually_lt continuousAt_const (hεs r hr)
  filter_upwards [hT] with t ht
  have hroots : ∀ r ∈ R, ∃ x ∈ Ioo (r - ε) (r + ε), (P t).IsRoot x := fun r hr =>
    exists_root_Ioo_of_mul_neg (P t) (by linarith) (ht r hr)
  choose! x hx using hroots
  obtain ⟨r₀, hr₀⟩ : R.Nonempty := Finset.card_pos.mp (by omega)
  have hPt0 : P t ≠ 0 := fun h => by
    have := ht r₀ hr₀; rw [h] at this; simp at this
  have hinj : Set.InjOn x R := by
    intro r hr r' hr' hxx
    by_contra hne
    have h1 := (hx r hr).1
    have h2 := (hx r' hr').1
    rw [hxx] at h1
    rcases lt_abs.mp (hεg r hr r' hr' hne) with h | h <;>
      linarith [h1.1, h1.2, h2.1, h2.2]
  have hsub : R.image x ⊆ (P t).roots.toFinset := by
    intro y hy
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hy
    exact Multiset.mem_toFinset.mpr ((mem_roots hPt0).mpr (hx r hr).2)
  have h1 : (R.image x).card = n := by rw [Finset.card_image_of_injOn hinj, hcard]
  have h2 := Multiset.toFinset_card_le (P t).roots
  have h3 := card_roots' (P t)
  have h4 := hdeg t
  have h5 := Finset.card_le_card hsub
  -- the produced roots exhaust the roots of `P t`
  have heq : R.image x = (P t).roots.toFinset := Finset.eq_of_subset_of_card_le hsub (by omega)
  refine ⟨splits_iff_card_roots.mpr (by omega), fun y hy => ?_⟩
  obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp (heq ▸ Multiset.mem_toFinset.mpr hy)
  have hxr := (hx r hr).1
  have hb := hεb r hr
  exact abs_le.mpr ⟨by linarith [neg_abs_le r, hxr.1], by linarith [le_abs_self r, hxr.2]⟩

/-- **Pure polynomials are large outside `[−2, 2]`.** -/
theorem abs_leadingCoeff_mul_le_abs_eval {Q : ℝ[X]} (hQ : IsPure Q) {y : ℝ} (hy : 2 ≤ |y|) :
    |Q.leadingCoeff| * (|y| - 2) ^ Q.natDegree ≤ |Q.eval y| := by
  have hval : Q.eval y = Q.leadingCoeff * (Q.roots.map fun a => y - a).prod := by
    conv_lhs => rw [hQ.1.eq_prod_roots]
    rw [eval_mul, eval_C, eval_multiset_prod, Multiset.map_map]
    simp
  rw [hval, abs_mul, ← splits_iff_card_roots.mp hQ.1]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  have key : ∀ s : Multiset ℝ, (∀ a ∈ s, |a| ≤ 2) →
      (|y| - 2) ^ Multiset.card s ≤ |(s.map fun a => y - a).prod| := by
    intro s
    induction s using Multiset.induction_on with
    | empty => intro _; simp
    | cons a s ih =>
      intro hs
      rw [Multiset.card_cons, Multiset.map_cons, Multiset.prod_cons, abs_mul, pow_succ, mul_comm]
      have ha : |y| - 2 ≤ |y - a| := by
        have := abs_sub_abs_le_abs_sub y a
        linarith [hs a (Multiset.mem_cons_self a s)]
      exact mul_le_mul ha (ih fun b hb => hs b (Multiset.mem_cons_of_mem hb))
        (pow_nonneg (by linarith) _) (abs_nonneg _)
  exact key _ hQ.2

/-- **Purity is closed** along a family whose degree is bounded and whose leading coefficient does
not vanish on `[0, 1]`. -/
theorem isClosed_pure {P : ℝ → ℝ[X]} {n : ℕ} (hdeg : ∀ t, (P t).natDegree ≤ n)
    (hcont : ∀ j, Continuous fun t => (P t).coeff j)
    (hlead : ∀ t ∈ Icc (0 : ℝ) 1, (P t).coeff n ≠ 0) :
    IsClosed (Icc (0 : ℝ) 1 ∩ {t | IsPure (P t)}) := by
  refine isClosed_of_closure_subset fun t ht => ?_
  obtain ⟨s, hs, hst⟩ := mem_closure_iff_seq_limit.mp ht
  have htI : t ∈ Icc (0 : ℝ) 1 :=
    isClosed_Icc.mem_of_tendsto hst (Eventually.of_forall fun m => (hs m).1)
  refine ⟨htI, ?_⟩
  have hne : P t ≠ 0 := fun h => hlead t htI (by rw [h, coeff_zero])
  refine ⟨HTGeometry.splits_of_tendsto_coeff (qs := fun m => P (s m)) (fun m => hdeg _) (hdeg t)
    (fun m => (hs m).2.1) (fun j => ((hcont j).tendsto t).comp hst) hne, fun x hx => ?_⟩
  by_contra hx2
  have hx2' : 2 < |x| := not_le.mp hx2
  have hdegm : ∀ m, (P (s m)).natDegree = n := fun m =>
    natDegree_eq_of_le_of_coeff_ne_zero (hdeg _) (hlead _ (hs m).1)
  have hbd : ∀ m, |(P (s m)).coeff n| * (|x| - 2) ^ n ≤ |(P (s m)).eval x| := fun m => by
    have := abs_leadingCoeff_mul_le_abs_eval (hs m).2 hx2'.le
    rwa [leadingCoeff, hdegm m] at this
  have hlim1 : Tendsto (fun m => |(P (s m)).coeff n| * (|x| - 2) ^ n) atTop
      (𝓝 (|(P t).coeff n| * (|x| - 2) ^ n)) :=
    ((((hcont n).tendsto t).comp hst).abs).mul_const _
  have hlim2 : Tendsto (fun m => |(P (s m)).eval x|) atTop (𝓝 |(P t).eval x|) :=
    (((continuous_eval_family hdeg hcont x).tendsto t).comp hst).abs
  have hle := le_of_tendsto_of_tendsto' hlim1 hlim2 hbd
  rw [((mem_roots hne).mp hx).eq_zero, abs_zero] at hle
  have : 0 < |(P t).coeff n| * (|x| - 2) ^ n :=
    mul_pos (abs_pos.mpr (hlead t htI)) (pow_pos (by linarith) n)
  linarith

/-- **The exit theorem: purity leaves only through a Frobenius collision.** If `P 0` is pure and
`P 1` is not, there is a first exit time `τ ∈ [0, 1)`: all `P s` with `0 ≤ s ≤ τ` are pure, and
`P τ` has a double root or a root at `±2`. -/
theorem exists_first_frobenius_collision {P : ℝ → ℝ[X]} {n : ℕ}
    (hdeg : ∀ t, (P t).natDegree ≤ n) (hcont : ∀ j, Continuous fun t => (P t).coeff j)
    (hlead : ∀ t ∈ Icc (0 : ℝ) 1, (P t).coeff n ≠ 0) (h0 : IsPure (P 0)) (h1 : ¬ IsPure (P 1)) :
    ∃ τ ∈ Ico (0 : ℝ) 1, (∀ s ∈ Icc 0 τ, IsPure (P s)) ∧ IsFrobeniusCollision (P τ) := by
  set N := {t ∈ Icc (0 : ℝ) 1 | ¬ IsPure (P t)} with hN
  have hN1 : (1 : ℝ) ∈ N := ⟨⟨zero_le_one, le_rfl⟩, h1⟩
  have hNb : BddBelow N := ⟨0, fun t ht => ht.1.1⟩
  set τ := sInf N with hτ
  have hτ0 : 0 ≤ τ := le_csInf ⟨1, hN1⟩ fun t ht => ht.1.1
  have hτ1 : τ ≤ 1 := csInf_le hNb hN1
  have hbelow : ∀ s ∈ Ico 0 τ, IsPure (P s) := fun s hs => by
    by_contra h
    exact absurd (csInf_le hNb ⟨⟨hs.1, by linarith [hs.2]⟩, h⟩) (not_le.mpr hs.2)
  have hτs : IsPure (P τ) := by
    rcases hτ0.lt_or_eq with hpos | h
    · have hcl := isClosed_pure hdeg hcont hlead
      have hsub : Ico 0 τ ⊆ Icc (0 : ℝ) 1 ∩ {t | IsPure (P t)} := fun s hs =>
        ⟨⟨hs.1, by linarith [hs.2]⟩, hbelow s hs⟩
      have hmem : τ ∈ closure (Ico 0 τ) := by
        rw [closure_Ico hpos.ne]; exact ⟨hτ0, le_rfl⟩
      exact (hcl.closure_subset_iff.mpr hsub hmem).2
    · rw [← h]; exact h0
  have hτlt : τ < 1 := lt_of_le_of_ne hτ1 fun h => h1 (h ▸ hτs)
  refine ⟨τ, ⟨hτ0, hτlt⟩, fun s hs => ?_, ?_⟩
  · rcases hs.2.lt_or_eq with h | h
    · exact hbelow s ⟨hs.1, h⟩
    · rw [h]; exact hτs
  · by_contra hc
    have hdegτ : (P τ).natDegree = n :=
      natDegree_eq_of_le_of_coeff_ne_zero (hdeg τ) (hlead τ ⟨hτ0, hτ1⟩)
    obtain ⟨η, hη, hball⟩ := Metric.eventually_nhds_iff.mp
      (eventually_pure_of_simple hdeg hcont hτs hdegτ hc)
    have : τ + η ≤ τ := le_csInf ⟨1, hN1⟩ fun t ht => by
      by_contra hlt
      have htτ : τ ≤ t := csInf_le hNb ht
      exact ht.2 (hball (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith [not_le.mp hlt]))
    linarith

/-- **A deformation without Frobenius collision preserves purity.** -/
theorem isPure_of_forall_not_frobeniusCollision {P : ℝ → ℝ[X]} {n : ℕ}
    (hdeg : ∀ t, (P t).natDegree ≤ n) (hcont : ∀ j, Continuous fun t => (P t).coeff j)
    (hlead : ∀ t ∈ Icc (0 : ℝ) 1, (P t).coeff n ≠ 0) (h0 : IsPure (P 0))
    (hno : ∀ s ∈ Icc (0 : ℝ) 1, IsPure (P s) → ¬ IsFrobeniusCollision (P s)) : IsPure (P 1) := by
  by_contra h1
  obtain ⟨τ, hτ, hpure, hcol⟩ := exists_first_frobenius_collision hdeg hcont hlead h0 h1
  exact hno τ ⟨hτ.1, hτ.2.le⟩ (hpure τ ⟨hτ.1, le_rfl⟩) hcol

/-- **Eigenvalues leave the unit circle only through a Frobenius collision.** If the circle
polynomial of `P 0` has all roots on the unit circle and that of `P 1` does not, there is a first
exit time `τ ∈ [0, 1)` up to which all eigenvalues stay on the circle, and `P τ` has a Frobenius
collision. -/
theorem exists_first_circle_collision {P : ℝ → ℝ[X]} {g : ℕ}
    (hdeg : ∀ t, (P t).natDegree ≤ g) (hcont : ∀ j, Continuous fun t => (P t).coeff j)
    (hlead : ∀ t ∈ Icc (0 : ℝ) 1, (P t).coeff g ≠ 0)
    (h0 : ∀ z : ℂ, (aeval z (circlePoly g (P 0)) : ℂ) = 0 → ‖z‖ = 1)
    (h1 : ¬ ∀ z : ℂ, (aeval z (circlePoly g (P 1)) : ℂ) = 0 → ‖z‖ = 1) :
    ∃ τ ∈ Ico (0 : ℝ) 1,
      (∀ s ∈ Icc 0 τ, ∀ z : ℂ, (aeval z (circlePoly g (P s)) : ℂ) = 0 → ‖z‖ = 1) ∧
        IsFrobeniusCollision (P τ) := by
  have hI0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hI1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  rw [← isPure_iff_circle (hdeg 0) (hlead 0 hI0)] at h0
  rw [← isPure_iff_circle (hdeg 1) (hlead 1 hI1)] at h1
  obtain ⟨τ, hτ, hpure, hcol⟩ := exists_first_frobenius_collision hdeg hcont hlead h0 h1
  refine ⟨τ, hτ, fun s hs => ?_, hcol⟩
  have hsI : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1, hs.2.trans hτ.2.le⟩
  exact (isPure_iff_circle (hdeg s) (hlead s hsI)).mp (hpure s hs)

end GaloisForLFunctions.ZeroConfigurationGeometry
